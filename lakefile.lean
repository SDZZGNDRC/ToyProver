import Lake
open Lake DSL

package "toyprover" where
  version := v!"0.1.0"
require batteries from git "https://github.com/leanprover-community/batteries" @ "01006c9e86bf9e397c026fef4190478dd1fd897e"

lean_lib «Toyprover» where
  -- add library configuration options here

@[default_target]
lean_exe "toyprover" where
  root := `Main
