import Lake
open Lake DSL

package "toyprover" where
  version := v!"0.1.0"

lean_lib «Toyprover» where
  -- add library configuration options here

@[default_target]
lean_exe "toyprover" where
  root := `Main
