import Lake
open Lake DSL

package «verusLeanStd» {
  -- add package configuration options here
}

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.5.0-rc1"

lean_lib «VerusLeanStd» {
  -- add library configuration options here
}

@[default_target]
lean_exe «verusLeanStd» {
  root := `Main
}
