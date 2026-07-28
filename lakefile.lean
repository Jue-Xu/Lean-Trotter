import Lake
open Lake DSL

package «lie-trotter» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-bch» from git
  "https://github.com/Jue-Xu/Lean-BCH.git" @ "05e8c52"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "06a46dae"

@[default_target]
lean_lib «LieTrotter» where
  srcDir := "."
