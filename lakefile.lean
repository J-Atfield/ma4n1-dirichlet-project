import Lake
open Lake DSL

package «mA4N1_Project» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MA4N1Project» {
  -- add any library configuration options here
}
