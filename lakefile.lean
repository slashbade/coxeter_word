import Lake
open Lake DSL

package «coxeter_word» where
  -- add package configuration options here

lean_lib «CoxeterWord» where
  -- add library configuration options here

@[default_target]
lean_exe «coxeter_word» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"
