import Lake
open Lake DSL

package «tablet» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Tablet» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "a090f46da78e9af11fee348cd7ee47bf8dd219d2"
