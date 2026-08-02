/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commuting degeneration of the Suzuki S₄ integrator

When `A` and `B` commute, splitting is unnecessary and every product formula
is *exact*.  This file makes that degeneration a set of theorems for the
S₄ integrator, closing a docstring-vs-statement drift: the docstring of
`suzuki4_total_error_commutator_scaling` (`Suzuki4TightConvergence.lean`)
claims the commutator-scaled `1/n⁴` coefficient "vanishes as `A` and `B`
commute", but until now no theorem stated it.

## Main results

- `strangBlock_eq_exp_of_commute`: each Strang block is exactly
  `exp(s•(A+B))` when `Commute A B`.
- `suzuki4Exp_eq_exp_of_commute`: `S₄(t) = exp(t•(A+B))` for **every**
  parameter `p` — no `IsSuzukiCubic` needed, since the five block fractions
  `p, p, 1-4p, p, p` sum to `1` identically.
- `BCHPrefactors.boundSum_eq_zero_of_commute` (and the specializations
  `bchTightPrefactors_boundSum_eq_zero_of_commute`,
  `childsBoundSum_eq_zero_of_commute`): the commutator-scaled coefficient
  `Σᵢ γᵢ‖Cᵢ‖` is exactly `0`, because each Childs commutator `Cᵢ` is a
  4-fold nested bracket whose innermost factor is `[B, A] = 0`.
- `suzuki4_pow_eq_exp_of_commute` / `suzuki4_total_error_eq_zero_of_commute`:
  the compounded product `(S₄(t/n))ⁿ` equals `exp(t•(A+B))` on the nose, so
  the total error is literally `0`.
- `suzuki4_commutator_leading_term_eq_zero_of_commute`: the exact leading
  term of `suzuki4_total_error_commutator_scaling` evaluates to `0`.

## Hypotheses

Any complete normed ℝ-algebra with `NormOneClass` — no star structure, no
`IsSuzukiCubic`, matching the hypothesis discipline of
`Suzuki4Convergence.lean` / `Suzuki4TightConvergence.lean`.  The pure
commutator-vanishing lemmas need only `NormedRing`.
-/

import LieTrotter.Suzuki4Convergence
import LieTrotter.Suzuki4ViaBCH

noncomputable section

open NormedSpace

/-!
## Vanishing of the commutator-scaled coefficient

Each of the 8 Childs commutators `Cᵢ = [X₁,[X₂,[X₃,[B,A]]]]` (with
`Xⱼ ∈ {A, B}`) contains `[B, A]` innermost, so it vanishes identically when
`A` and `B` commute.  Consequently every weighted sum `Σᵢ γᵢ‖Cᵢ‖` — in
particular the CAS-certified `bchTightPrefactors.boundSum` consumed by
`suzuki4_total_error_commutator_scaling`, and Childs's own
`childsBoundSum` — is exactly `0`.  Only `NormedRing 𝔸` is needed here.
-/

section CommutatorVanishing

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The innermost bracket `[B, A]` vanishes for commuting `A, B`. -/
lemma commBr_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) : ⟦B, A⟧ = 0 := by
  unfold commBr
  rw [hAB.eq, sub_self]

/-- `[X, 0] = 0`. -/
lemma commBr_zero_right (X : 𝔸) : ⟦X, (0 : 𝔸)⟧ = 0 := by
  unfold commBr
  rw [mul_zero, zero_mul, sub_zero]

/-- Any 4-fold nested commutator built on the innermost bracket `[B, A]`
vanishes when `A` and `B` commute.  All 8 Childs commutators have this shape. -/
lemma nested_commBr_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) (X₁ X₂ X₃ : 𝔸) :
    ⟦X₁, ⟦X₂, ⟦X₃, ⟦B, A⟧⟧⟧⟧ = 0 := by
  rw [commBr_eq_zero_of_commute hAB, commBr_zero_right, commBr_zero_right,
    commBr_zero_right]

/-- `C₁ = [A,[A,[A,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₁_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₁ A B = 0 := by
  unfold childsComm₁; exact nested_commBr_eq_zero_of_commute hAB A A A

/-- `C₂ = [A,[A,[B,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₂_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₂ A B = 0 := by
  unfold childsComm₂; exact nested_commBr_eq_zero_of_commute hAB A A B

/-- `C₃ = [A,[B,[A,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₃_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₃ A B = 0 := by
  unfold childsComm₃; exact nested_commBr_eq_zero_of_commute hAB A B A

/-- `C₄ = [A,[B,[B,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₄_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₄ A B = 0 := by
  unfold childsComm₄; exact nested_commBr_eq_zero_of_commute hAB A B B

/-- `C₅ = [B,[A,[A,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₅_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₅ A B = 0 := by
  unfold childsComm₅; exact nested_commBr_eq_zero_of_commute hAB B A A

/-- `C₆ = [B,[A,[B,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₆_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₆ A B = 0 := by
  unfold childsComm₆; exact nested_commBr_eq_zero_of_commute hAB B A B

/-- `C₇ = [B,[B,[A,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₇_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₇ A B = 0 := by
  unfold childsComm₇; exact nested_commBr_eq_zero_of_commute hAB B B A

/-- `C₈ = [B,[B,[B,[B,A]]]] = 0` for commuting `A, B`. -/
lemma childsComm₈_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsComm₈ A B = 0 := by
  unfold childsComm₈; exact nested_commBr_eq_zero_of_commute hAB B B B

/-- **The commutator-scaled coefficient vanishes for commuting `A, B`** — for
ANY choice of prefactors `γ`: every term of `Σᵢ γᵢ‖Cᵢ‖` has `‖Cᵢ‖ = 0`. -/
lemma BCHPrefactors.boundSum_eq_zero_of_commute (γ : BCHPrefactors) {A B : 𝔸}
    (hAB : Commute A B) : γ.boundSum A B = 0 := by
  unfold BCHPrefactors.boundSum
  rw [childsComm₁_eq_zero_of_commute hAB, childsComm₂_eq_zero_of_commute hAB,
    childsComm₃_eq_zero_of_commute hAB, childsComm₄_eq_zero_of_commute hAB,
    childsComm₅_eq_zero_of_commute hAB, childsComm₆_eq_zero_of_commute hAB,
    childsComm₇_eq_zero_of_commute hAB, childsComm₈_eq_zero_of_commute hAB]
  simp

/-- The CAS-certified γ-sum `bchTightPrefactors.boundSum` — the `1/n⁴`
coefficient of `suzuki4_total_error_commutator_scaling` — is exactly `0`
for commuting `A, B`.  This is the theorem behind that docstring's claim
"it vanishes as `A` and `B` commute". -/
lemma bchTightPrefactors_boundSum_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    bchTightPrefactors.boundSum A B = 0 :=
  bchTightPrefactors.boundSum_eq_zero_of_commute hAB

/-- Childs's own α-sum (the `1/n⁴` coefficient of
`suzuki4_total_error_childs_scaling`) is exactly `0` for commuting `A, B`. -/
lemma childsBoundSum_eq_zero_of_commute {A B : 𝔸} (hAB : Commute A B) :
    childsBoundSum A B = 0 := by
  unfold childsBoundSum
  rw [childsComm₁_eq_zero_of_commute hAB, childsComm₂_eq_zero_of_commute hAB,
    childsComm₃_eq_zero_of_commute hAB, childsComm₄_eq_zero_of_commute hAB,
    childsComm₅_eq_zero_of_commute hAB, childsComm₆_eq_zero_of_commute hAB,
    childsComm₇_eq_zero_of_commute hAB, childsComm₈_eq_zero_of_commute hAB]
  simp

end CommutatorVanishing

/-!
## S₄ is exact for commuting `A, B`

The five Strang blocks of `suzuki4Exp_eq_strangProduct` each collapse to an
exact exponential, and the block time-fractions `p + p + (1-4p) + p + p = 1`
for **every** `p` — the Suzuki cubic condition is irrelevant here.
-/

section ExactExponential

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
  [CompleteSpace 𝔸]

omit [NormOneClass 𝔸] in
/-- Each Strang block degenerates to the exact exponential when `A` and `B`
commute: `S₂(s) = exp((s/2)•A)·exp(s•B)·exp((s/2)•A) = exp(s•(A+B))`. -/
theorem strangBlock_eq_exp_of_commute (A B : 𝔸) (hAB : Commute A B) (s : ℝ) :
    strangBlock A B s = exp (s • (A + B)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold strangBlock
  have h₁ : Commute ((s / 2) • A) (s • B) := (hAB.smul_left _).smul_right _
  have h₂ : Commute ((s / 2) • A + s • B) ((s / 2) • A) :=
    Commute.add_left (((Commute.refl A).smul_left _).smul_right _)
      ((hAB.symm.smul_left _).smul_right _)
  rw [← exp_add_of_commute h₁, ← exp_add_of_commute h₂]
  congr 1
  module

/-- **Commuting degeneration: S₄ is exact.**  When `A` and `B` commute, the
Suzuki S₄ product equals `exp(t•(A+B))` for **every** parameter `p` — no
`IsSuzukiCubic` hypothesis, since the block fractions `p, p, 1-4p, p, p`
sum to `1` identically in `p`. -/
theorem suzuki4Exp_eq_exp_of_commute (A B : 𝔸) (hAB : Commute A B) (p t : ℝ) :
    suzuki4Exp A B p t = exp (t • (A + B)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Merge two exponentials of scalar multiples of the same element `A + B`.
  have hmerge : ∀ c₁ c₂ : ℝ,
      exp (c₁ • (A + B)) * exp (c₂ • (A + B)) = exp ((c₁ + c₂) • (A + B)) := by
    intro c₁ c₂
    rw [← exp_add_of_commute (((Commute.refl (A + B)).smul_left c₁).smul_right c₂),
      ← add_smul]
  rw [suzuki4Exp_eq_strangProduct]
  simp only [strangBlock_eq_exp_of_commute A B hAB]
  rw [hmerge, hmerge, hmerge, hmerge]
  congr 1
  module

/-- **The compounded S₄ product is exact for commuting `A, B`**:
`(S₄(t/n))ⁿ = exp(t•(A+B))` for every `p`, every `t`, and every `n > 0`. -/
theorem suzuki4_pow_eq_exp_of_commute (A B : 𝔸) (hAB : Commute A B) (p t : ℝ)
    (n : ℕ) (hn : 0 < n) :
    suzuki4Exp A B p (t / (n : ℝ)) ^ n = exp (t • (A + B)) := by
  rw [suzuki4Exp_eq_exp_of_commute A B hAB]
  exact exp_smul_div_pow (A + B) t n hn

/-- **The S₄ total error is literally zero for commuting `A, B`** — the
degenerate endpoint of `suzuki4_total_error_quartic` and
`suzuki4_total_error_commutator_scaling`. -/
theorem suzuki4_total_error_eq_zero_of_commute (A B : 𝔸) (hAB : Commute A B)
    (p t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖suzuki4Exp A B p (t / (n : ℝ)) ^ n - exp (t • (A + B))‖ = 0 := by
  rw [suzuki4_pow_eq_exp_of_commute A B hAB p t n hn, sub_self, norm_zero]

omit [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- The exact leading term of `suzuki4_total_error_commutator_scaling`
evaluates to `0` for commuting `A, B`: the `e^{tK}·(Σᵢ γᵢ‖Cᵢ‖)·t⁵/n⁴` bound
collapses because its commutator-scaled coefficient does.  (The total error
itself is of course also `0`: `suzuki4_total_error_eq_zero_of_commute`.) -/
lemma suzuki4_commutator_leading_term_eq_zero_of_commute {A B : 𝔸}
    (hAB : Commute A B) (p t : ℝ) (n : ℕ) :
    Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) *
      (bchTightPrefactors.boundSum A B * t ^ 5) / (n : ℝ) ^ 4 = 0 := by
  rw [bchTightPrefactors_boundSum_eq_zero_of_commute hAB, zero_mul, mul_zero,
    zero_div]

end ExactExponential

end
