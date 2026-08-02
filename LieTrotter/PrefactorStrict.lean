/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict Prefactor Comparison: γᵢ < αᵢ, Termwise and With an 8× Gap

The existing comparison between this project's CAS-certified S₄ prefactors
`bchTightPrefactors` (the γᵢ) and the coefficients in Childs et al. (2021)'s
rigorous arXiv Proposition J.1 bound, `childsPrefactors` (the αᵢ), is the
*non-strict* summed
inequality `bchTightPrefactors_le_childs : Σγᵢ‖Cᵢ‖ ≤ Σαᵢ‖Cᵢ‖`
(`Suzuki4ViaBCH.lean`). This file formalizes a strict termwise improvement of
that published coefficient vector; it does not claim that either vector is
globally optimal in the over-complete commutator basis:

* `bchTightPrefactors_lt_childs_termwise` — **strict** inequality `γᵢ < αᵢ`
  at every index `i = 1, …, 8` (including `γ₃ = 0 < 0.0046 = α₃` and
  `γ₇ = 0 < 0.0173 = α₇`).
* `bchTightPrefactors_le_childs_div_eight_termwise` — the quantified gap
  `γᵢ ≤ αᵢ/8`: every certified prefactor is at least **8× smaller** than
  Childs's.  The binding index is `i = 2` (and `6`): `α₂/γ₂ = 0.0057/0.000663
  ≈ 8.60`, so `8` is the largest integer gap that holds termwise; the other
  nonzero ratios range up to ≈ 64× (`i = 8`).
* `bchTightPrefactors_boundSum_le_childs_div_eight` — the summed form
  `Σγᵢ‖Cᵢ‖ ≤ (Σαᵢ‖Cᵢ‖)/8` for arbitrary `A, B` in any normed ring.
* `bchTightPrefactors_boundSum_lt_childs` — strict dominance of the summed
  bound whenever it is nondegenerate (`Σαᵢ‖Cᵢ‖ > 0`; for commuting `A, B`
  both sums are `0` — see `Suzuki4Commute.lean` — so a hypothesis is
  genuinely needed).

All coefficient facts are pure rational arithmetic (`norm_num`); the summed
forms only add `norm_nonneg`.
-/

import LieTrotter.Suzuki4ViaBCH

noncomputable section

/-!
## Termwise coefficient comparisons (pure rational arithmetic)
-/

/-- **Strict termwise dominance**: every CAS-certified prefactor `γᵢ` of
`bchTightPrefactors` is *strictly* smaller than the corresponding Childs
coefficient `αᵢ` — including the two indices where `γᵢ = 0` exactly. -/
theorem bchTightPrefactors_lt_childs_termwise :
    bchTightPrefactors.γ₁ < childsPrefactors.γ₁ ∧
    bchTightPrefactors.γ₂ < childsPrefactors.γ₂ ∧
    bchTightPrefactors.γ₃ < childsPrefactors.γ₃ ∧
    bchTightPrefactors.γ₄ < childsPrefactors.γ₄ ∧
    bchTightPrefactors.γ₅ < childsPrefactors.γ₅ ∧
    bchTightPrefactors.γ₆ < childsPrefactors.γ₆ ∧
    bchTightPrefactors.γ₇ < childsPrefactors.γ₇ ∧
    bchTightPrefactors.γ₈ < childsPrefactors.γ₈ := by
  unfold bchTightPrefactors childsPrefactors
  norm_num

/-- **Quantified termwise gap**: `γᵢ ≤ αᵢ/8` at every index — the certified
prefactors are at least 8× tighter than Childs's, termwise.  The constant `8`
is the largest integer for which this holds: the binding ratio is
`α₂/γ₂ = 0.0057/0.000663 ≈ 8.60` (similarly `α₆/γ₆ ≈ 8.60`). -/
theorem bchTightPrefactors_le_childs_div_eight_termwise :
    bchTightPrefactors.γ₁ ≤ childsPrefactors.γ₁ / 8 ∧
    bchTightPrefactors.γ₂ ≤ childsPrefactors.γ₂ / 8 ∧
    bchTightPrefactors.γ₃ ≤ childsPrefactors.γ₃ / 8 ∧
    bchTightPrefactors.γ₄ ≤ childsPrefactors.γ₄ / 8 ∧
    bchTightPrefactors.γ₅ ≤ childsPrefactors.γ₅ / 8 ∧
    bchTightPrefactors.γ₆ ≤ childsPrefactors.γ₆ / 8 ∧
    bchTightPrefactors.γ₇ ≤ childsPrefactors.γ₇ / 8 ∧
    bchTightPrefactors.γ₈ ≤ childsPrefactors.γ₈ / 8 := by
  unfold bchTightPrefactors childsPrefactors
  norm_num

/-!
## Summed comparisons (any normed ring)
-/

section BoundSum

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- **Summed 8× gap**: `Σᵢ γᵢ‖Cᵢ‖ ≤ (Σᵢ αᵢ‖Cᵢ‖)/8` for arbitrary `A, B` —
the project's commutator-scaled `1/n⁴` coefficient is at most one eighth of
Childs's, uniformly in the operators.  Strengthens
`bchTightPrefactors_le_childs`. -/
theorem bchTightPrefactors_boundSum_le_childs_div_eight (A B : 𝔸) :
    bchTightPrefactors.boundSum A B ≤ childsBoundSum A B / 8 := by
  unfold BCHPrefactors.boundSum bchTightPrefactors childsBoundSum
  have h₁ := norm_nonneg (childsComm₁ A B)
  have h₂ := norm_nonneg (childsComm₂ A B)
  have h₃ := norm_nonneg (childsComm₃ A B)
  have h₄ := norm_nonneg (childsComm₄ A B)
  have h₅ := norm_nonneg (childsComm₅ A B)
  have h₆ := norm_nonneg (childsComm₆ A B)
  have h₇ := norm_nonneg (childsComm₇ A B)
  have h₈ := norm_nonneg (childsComm₈ A B)
  nlinarith

/-- **Strict summed dominance** whenever the comparison is nondegenerate:
if Childs's bound `Σᵢ αᵢ‖Cᵢ‖` is nonzero, the certified bound is *strictly*
smaller.  (The hypothesis is necessary: for commuting `A, B` both sums vanish
— `Suzuki4Commute.lean`.) -/
theorem bchTightPrefactors_boundSum_lt_childs (A B : 𝔸)
    (h : 0 < childsBoundSum A B) :
    bchTightPrefactors.boundSum A B < childsBoundSum A B :=
  lt_of_le_of_lt (bchTightPrefactors_boundSum_le_childs_div_eight A B)
    (by linarith)

end BoundSum

end
