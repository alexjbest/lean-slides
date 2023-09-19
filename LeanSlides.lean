import ProofWidgets.Component.HtmlDisplay
import Std.CodeAction.Misc
import Std.Tactic.OpenPrivate
import LeanSlides.Init
import Lean

open Lean ProofWidgets Elab Parser Command Server System

section Utils

def markdownDir : System.FilePath := "." / "md"
def slidesDir : System.FilePath := "." / "slides"

def getServerPort : IO String := do
  match ← IO.getEnv "LEANSLIDES_PORT" with
  | some port => return port
  | none => return "3000"

def getServerUrl : IO String := do
  let url := s!"http://localhost:{← getServerPort}"
  let out ← IO.Process.output { cmd := "curl", args := #[url] }
  if out.exitCode != 0 then
    IO.eprintln "The server for `Lean Slides` is not running."
    IO.eprintln "It can be started using the command `lake run lean-slides/serve-slides`."
  return url

def System.FilePath.getRelativePath (filePath : FilePath) : String :=
  if filePath.isRelative then
    filePath.normalize.toString.dropWhile (· ≠ FilePath.pathSeparator)
  else 
    panic! s!"The file path {filePath} is not a relative path."


namespace Lean.Elab.Term
open Meta

open Lean

private def mkEvalInstCore (evalClassName : Name) (e : Expr) : MetaM Expr := do
  let α    ← inferType e
  let u    ← getDecLevel α
  let inst := mkApp (Lean.mkConst evalClassName [u]) α
  try
    synthInstance inst
  catch _ =>
    -- Put `α` in WHNF and try again
    try
      let α ← whnf α
      synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
    catch _ =>
      -- Fully reduce `α` and try again
      try
        let α ← reduce (skipTypes := false) α
        synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
      catch _ =>
        throwError "expression{indentExpr e}\nhas type{indentExpr α}\nbut instance{indentExpr inst}\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `{evalClassName}` class"

private def mkRunMetaEval (e : Expr) : MetaM Expr :=
  withLocalDeclD `env (Lean.mkConst ``Lean.Environment) fun env =>
  withLocalDeclD `opts (Lean.mkConst ``Lean.Options) fun opts => do
    let α ← inferType e
    let u ← getDecLevel α
    let instVal ← mkEvalInstCore ``Lean.MetaEval e
    let e := mkAppN (Lean.mkConst ``Lean.runMetaEval [u]) #[α, instVal, env, opts, e]
    instantiateMVars (← mkLambdaFVars #[env, opts] e)

private def mkRunEval (e : Expr) : MetaM Expr := do
  let α ← inferType e
  let u ← getDecLevel α
  let instVal ← mkEvalInstCore ``Lean.Eval e
  instantiateMVars (mkAppN (Lean.mkConst ``Lean.runEval [u]) #[α, instVal, mkSimpleThunk e])
-- open private Lean.Elab.Command.mkRunMetaEval from Lean.Elab.Command
open Expr in
-- TODO an α version would be cool in presence of Quote α 
unsafe def metaEvalTerm /-(type : Expr)-/ (term : Syntax) /-(safety := DefinitionSafety.safe)-/ : CommandElabM String := do
  let declName := `_eval
  let addAndCompile (value : Expr) : TermElabM Unit := do
    let value ← Term.levelMVarToParam (← instantiateMVars value)
    let type ← inferType value
    let us := collectLevelParams {} value |>.params
    let value ← instantiateMVars value
    let decl := Declaration.defnDecl {
      name        := declName
      levelParams := us.toList
      type        := type
      value       := value
      hints       := ReducibilityHints.opaque
      safety      := DefinitionSafety.unsafe
    }
    Term.ensureNoUnassignedMVars decl
    addAndCompile decl
  -- Elaborate `term`
  let elabEvalTerm : TermElabM Expr := do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    if (← Term.logUnassignedUsingErrorInfos (← getMVars e)) then throwAbortTerm
    if (← isProp e) then
      mkDecide e
    else
      return e
  -- Evaluate using term using `MetaEval` class.
  let elabMetaEval : CommandElabM String := do
    -- act? is `some act` if elaborated `term` has type `CommandElabM α`
    let act? ← runTermElabM fun _ => Term.withDeclName declName do
      let e ← elabEvalTerm
      let eType ← instantiateMVars (← inferType e)
      if eType.isAppOfArity ``CommandElabM 1 then
        let mut stx ← Term.exprToSyntax e
        unless (← isDefEq eType.appArg! (Lean.mkConst ``Unit)) do
          stx ← `($stx >>= fun v => IO.println (repr v))
        let act ← Lean.Elab.Term.evalTerm (CommandElabM String) (mkApp (Lean.mkConst ``CommandElabM) (Lean.mkConst ``String)) stx
        pure <| some act
      else
        let e ← mkRunMetaEval e
        let env ← getEnv
        let opts ← getOptions
        let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) declName finally setEnv env
        let (out, res) ← act env opts -- we execute `act` using the environment
        return out
        -- match res with
        -- | Except.error e => throwError e.toString
        -- | Except.ok env  => do setEnv env; pure none
    let some act := act? | throwError "couldn't interpret as meta string"
    act
  -- Evaluate using term using `Eval` class.
  let elabEval : CommandElabM String := runTermElabM fun _ => Term.withDeclName declName do
    -- fall back to non-meta eval if MetaEval hasn't been defined yet
    -- modify e to `runEval e`
    let e ← mkRunEval (← elabEvalTerm)
    let env ← getEnv
    let act ← try addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) declName finally setEnv env
    let (out, res) ← liftM (m := IO) act
    return out
    -- logInfoAt term out -- was tk
    -- match res with
    -- | Except.error e => throwError e.toString
    -- | Except.ok _    => pure ()
  if (← getEnv).contains ``Lean.MetaEval then do
    elabMetaEval
  else
    elabEval
  -- let v ← elabTermEnsuringType value type
  -- synthesizeSyntheticMVarsNoPostponing
  -- let v ← instantiateMVars v
  -- if (← logUnassignedUsingErrorInfos (← getMVars v)) then throwAbortTerm
  -- if eType.isAppOfArity ``CommandElabM 1 then
  --   let mut stx ← Term.exprToSyntax e
  --   unless (← isDefEq eType.appArg! (mkConst ``Unit)) do
  --     stx ← `($stx >>= fun v => IO.println (repr v))
  --   let act ← Lean.Elab.Term.evalTerm (CommandElabM Unit) (mkApp (mkConst ``CommandElabM) (mkConst ``Unit)) stx
  --   pure <| some act
  -- evalExpr α type v safety

end Lean.Elab.Term
open Lean.Elab.Term

unsafe
def extractModuleDocContent : TSyntax ``moduleDoc → CommandElabM String
  | ⟨.node _ _ #[_, .atom _ doc]⟩ => do
      let e ←getEnv 
      logInfo doc
      -- TODO need escaping here for "" but unclear how
      -- let doc := doc.replace "\"" "\\\""
      -- let categories := (parserExtension.getState e).categories.toList.map (·.fst)
      -- logInfo (toString categories)
      let a ← match Parser.runParserCategory e `term <| "s!\"" ++ doc.dropRight 2 ++ "\"" with
      | Except.ok a => do pure a
      | Except.error s => throwError s
      
      let a : TSyntax interpolatedStrKind := ⟨a[1]⟩
      let b ← liftMacroM <| Lean.TSyntax.expandInterpolatedStr a (← `(String)) (← `(toString))
      logInfo b
      -- logInfo (← liftCoreM (Meta.liftMetaM (Meta.whnf (← liftTermElabM <| Term.elabTerm b none))))
      logInfo (← liftTermElabM <| Term.evalTerm String (mkConst ``String) b)
      -- liftTermElabM <| Term.evalTerm String (mkConst ``String) b
      metaEvalTerm b
      -- liftTermElabM
      --   (Lean.Meta.evalExpr String (← liftTermElabM <| Term.elabTerm b (mkConst ``String)) (mkConst ``String))--.run' {env := e}
      
      -- match (← liftTermElabM <| Term.elabTerm b none) with
      -- | .lit (.strVal b) => return
      -- (Lean.Meta.reduceEval b)
      -- | _ => throwError "boo"
      -- return (toString  b)
  | _ => panic!"Ill-formed module docstring."

def createMarkdownFile (title text : String) : IO FilePath := do
  let mdFile := markdownDir / (title ++ ".md")
  unless ← markdownDir.pathExists do
    IO.FS.createDir markdownDir
  IO.FS.writeFile mdFile text
  return mdFile

def runPandoc (mdFile : FilePath) : IO FilePath := do
  unless (← mdFile.pathExists) && mdFile.extension = some "md" do
    IO.throwServerError s!"The file {mdFile} is not a valid Markdown file."
  unless mdFile.parent = some markdownDir do
    IO.throwServerError s!"The file {mdFile} is not in the directory {markdownDir}."
  
  let htmlFile : FilePath := slidesDir / (mdFile.fileStem.get! ++ ".html")
  unless ← slidesDir.pathExists do
    IO.FS.createDir slidesDir 
  let out ← IO.Process.run {
    cmd := "pandoc",
    args := #["-s", "--katex", 
              "-t", "revealjs"] ++ 
            (← LeanSlides.pandocOptions.get) ++ 
            #[ mdFile.toString, 
              "-o", htmlFile.toString],
    cwd := some "."
  }
  IO.println out
  return htmlFile

open scoped ProofWidgets.Jsx in
def iframeComponent (url : String) :=
  <iframe src={url} width="100%" height="500px" frameBorder="0" />

end Utils

section Caching

initialize slidesCache : IO.Ref (HashMap (String × String) FilePath) ← IO.mkRef ∅

def getSlidesFor (title : String) (content : String) : IO FilePath := do
  let ref ← slidesCache.get
  match ref.find? (title, content) with
    | some filePath => return filePath
    | none => 
      let mdFile ← createMarkdownFile title content
      let htmlFile ← runPandoc mdFile
      slidesCache.set <| ref.insert (title, content) htmlFile
      return htmlFile

end Caching

/-!"

  # ad a 
"-/
section Doc

open Lean Parser
def slideContent := leading_parser ppDedent <|
  "/-!" >> commentBody >> ppLine

end Doc

section Widget

syntax (name := slidesCmd) "#slides" ("+draft")? ident moduleDoc : command

@[command_elab slidesCmd] unsafe def revealSlides : CommandElab
  | stx@`(command| #slides $title $doc) => do
    let name := title.getId.toString
    let content ← extractModuleDocContent doc
    let slidesPath ← getSlidesFor name content
    let slidesUrl := (← getServerUrl) ++ slidesPath.getRelativePath
    IO.println s!"Rendering results for {name} hosted at {slidesUrl} ..."
    -- TODO: Check whether the server is up programmatically
    IO.println "Ensure that the server is running ..."
    let slides := Html.ofTHtml <| iframeComponent slidesUrl
    runTermElabM fun _ ↦ do 
      savePanelWidgetInfo stx ``HtmlDisplayPanel <| do
        return .mkObj [("html", ← rpcEncode slides)]
  | `(command| #slides +draft%$tk $_ $_) => 
    logInfoAt tk m!"Slides are not rendered in draft mode."
  | _ => throwUnsupportedSyntax

open Std CodeAction in
@[command_code_action slidesCmd]
def draftSlidesCodeAction : CommandCodeAction := fun _ _ _ node ↦ do
  let .node info _ := node | return #[]
  let doc ← RequestM.readDoc
  match info.stx with
    | `(command| #slides%$tk $_:ident $_:moduleDoc) => 
      let eager : Lsp.CodeAction := {
        title := "Convert to draft slides.",
        kind? := "quickfix",
        isPreferred? := true
      }
      return #[{
        eager
        lazy? := some do
          let some pos := tk.getTailPos? | return eager
          return { eager with 
            edit? := some <| .ofTextEdit doc.meta.uri {
              range := doc.meta.text.utf8RangeToLspRange ⟨pos, pos⟩,
              newText := " +draft" } }
      }]
    | `(command| #slides +draft%$tk $_:ident $_:moduleDoc) => 
      let eager : Lsp.CodeAction := {
        title := "Convert to live slides.",
        kind? := "quickfix",
        isPreferred? := true
      }
      return #[{
        eager
        lazy? := some do
          let some startPos := tk.getPos? | return eager
          let some endPos := tk.getTailPos? | return eager
          return { eager with 
            edit? := some <| .ofTextEdit doc.meta.uri {
              range := doc.meta.text.utf8RangeToLspRange ⟨startPos, ⟨endPos.byteIdx + 1⟩⟩,
              newText := "" } }
      }]
    | _ => return #[]

end Widget