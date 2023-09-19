import LeanSlides
import Lean

open Lean
#eval 1 + 1


def aaa := 2

def typeOf {α : Sort _} (a : α) := α 
-- set_option pp.rawOnError true
#slides Introduction /-!
% Lean Slides
% https://github.com/0art0/lean-slides/
% Today

# About

`Lean Slides` is a tool to 
automatically generate `reveal.js` slides
from Markdown comments in the Lean editor.

# Use cases

`Lean Slides` can be used in 
tutorials or demonstrations
to avoid switching between 
the slides and the Lean editor.

-/

-- Some intervening Lean code
example : 1 = 1 := by
  rfl

def rainbow (s : String) : String := 
Id.run
  do
    let mut out := ""
    let mut i := 0
    let mut len : Float := 0
    for _ in s.data do
      len := len + 1 -- ew
    for char in s.data do
      let r : Float := (256 : Float) * i / len
      out := out.append s!"<text style='color: rgb({r},{r},{r})'>{char}</text>"
      i := i + 1
    return out

#slides Tool /-!
# Dependencies


`Lean Slides` works by combining together several tools:

- [`reveal.js`](https://revealjs.com/)

- [`pandoc`](https://pandoc.org/)

- [`node.js`](https://nodejs.org/en)

- [`http-server`](https://www.npmjs.com/package/http-server)

# Usage

To use `Lean Slides`, first install all the dependencies
and start the HTTP server with the command
```lean
lake run lean-slides/serve-slides
```

---

In any file that imports `Lean Slides`, type

```lean
#slides +draft Test /-!
  <Markdown text>
-/
```

# Features

`Lean Slides` turns comments written in the above format
into `reveal.js` slides which are rendered in the infoview
as a [`Widget`](https://github.com/EdAyers/ProofWidgets4).

The tool also features a code action to 
go in and out of draft mode.

<text style='color: red'>color</text>

We can also evaluate {" ".intercalate ["arbitrary", "Lean", "code"]}
We can also evaluate {rainbow "and make cool effects using Lean itself"}
-/


-- Some more intervening Lean code

namespace LeanSlides

#slides Math /-!
# Rendering math

The generated `reveal.js` slides
render mathematics by default
using $KaTeX$.{1}

-/

#set_pandoc_options "-V" "theme=white"

#slides Options /-!
# A test for pandoc options. 

This should use the white theme.
-/