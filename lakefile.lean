import Lake
open Lake DSL

package "toyprover" where
  version := v!"0.1.0"
require batteries from git "https://github.com/leanprover-community/batteries" @ "e8dc5fc16c625fc4fe08f42d625523275ddbbb4b"

lean_lib «Toyprover» where
  -- add library configuration options here

@[default_target]
lean_exe "toyprover" where
  root := `Main
