import Lake
open Lake DSL

package «Formal2024» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Formal2024» {
  -- add any library configuration options here
}

lean_lib «MIL» {
  srcDir:= "References"
}

lean_lib «Tutorials» {
  srcDir:= "References"
}
