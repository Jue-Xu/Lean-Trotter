import Lake
open Lake DSL

package «lie-trotter» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «lean-bch» from git
  "https://github.com/Jue-Xu/Lean-BCH.git" @ "c71d8f2"

@[default_target]
lean_lib «LieTrotter» where
  srcDir := "."
