import Lake
open Lake DSL

package «MathProofGame» where
  -- add package configuration options here

-- for modules need to import
lean_lib «Definition» where
  -- add package configuration options here
lean_lib «Collection» where
  -- add package configuration options here

@[default_target]
lean_exe «mathproofgame» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.2.0"
