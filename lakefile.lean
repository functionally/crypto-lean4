import Lake
open Lake DSL

package «Crypto» where

lean_lib «Crypto» where
  srcDir := "src"

/-
require std from git
  "https://github.com/leanprover/std4"
  @ "v4.7.0"
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.7.0"

@[default_target]
lean_exe «crypto» where
  root := `Main
  srcDir := "src"
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
