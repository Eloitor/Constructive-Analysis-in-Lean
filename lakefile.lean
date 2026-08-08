import Lake
open Lake DSL

package «ConstructiveAnalysis» where
  -- srcDir relative module layout, see `lean_lib` below

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

@[default_target]
lean_lib ConstructiveAnalysis where
  srcDir := "src"
