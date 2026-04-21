/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ as a product of 5 Strang blocks (Yoshida / Suzuki factorization)

This module provides the structural decomposition of the Suzuki S₄ product
into five symmetric Strang blocks with coefficients `[p, p, 1-4p, p, p]`:

  S₄(t)  =  S₂(pt) · S₂(pt) · S₂((1-4p)t) · S₂(pt) · S₂(pt)

where `S₂(s) := exp((s/2)·A)·exp(s·B)·exp((s/2)·A)` is the symmetric Strang
block. This is the natural algebraic form for importing BCH-based results
(see the companion Lean-BCH project): each Strang block has a symmetric BCH
expansion whose cubic terms sum to `Σᵢ cᵢ³·E₃(A,B) = (4p³+q³)·E₃(A,B)`,
vanishing under the Suzuki condition.

## Status

- `strangBlock`: definition.
- `suzuki4Exp_eq_strangProduct`: decomposition (proved).

Preparation for Path B integration with Lean-BCH (see the project handoff).
-/

import LieTrotter.Suzuki4CommutatorScaling
import LieTrotter.Suzuki4DerivExplicit

noncomputable section

open NormedSpace

section Scalars

/-!
## Suzuki coefficient arithmetic

The 5 Strang blocks in the S₄ factorization have coefficients
`(c₁, c₂, c₃, c₄, c₅) = (p, p, 1-4p, p, p)`. We record the two key sums:
- `Σᵢ cᵢ = 4p + (1-4p) = 1` (consistency)
- `Σᵢ cᵢ³ = 4p³ + (1-4p)³ = 0` (Suzuki cubic — the defining order-4 condition)
-/

/-- **Consistency sum**: `4p + (1-4p) = 1`. -/
lemma suzuki4_coeff_sum_one (p : ℝ) : p + p + (1 - 4 * p) + p + p = 1 := by ring

/-- **Suzuki cubic sum**: `4p³ + (1-4p)³ = 0` under `IsSuzukiCubic p`. This is
the operator-independent scalar identity enabling order-4 BCH cancellation —
summing cubic BCH terms over the 5 Strang blocks gives `Σᵢ cᵢ³ · E₃(A,B) = 0`. -/
lemma suzuki4_coeff_cube_sum_zero (p : ℝ) (h : IsSuzukiCubic p) :
    p ^ 3 + p ^ 3 + (1 - 4 * p) ^ 3 + p ^ 3 + p ^ 3 = 0 := by
  unfold IsSuzukiCubic at h
  linarith

/-- Block-structured restatement: `Σᵢ cᵢ³ = 0` in the form `Σ c_block_i³ = 0`
where the list of coefficients is `[p, p, 1-4p, p, p]`. -/
lemma suzuki4_block_cubes_sum_zero (p : ℝ) (h : IsSuzukiCubic p) :
    p ^ 3 + p ^ 3 + (1 - 4 * p) ^ 3 + p ^ 3 + p ^ 3 = 0 :=
  suzuki4_coeff_cube_sum_zero p h

end Scalars

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- Symmetric Strang block: `S₂(s)[A, B] = exp((s/2)·A) · exp(s·B) · exp((s/2)·A)`.

For `s = c·t`, this is the elementary palindromic order-2 integrator with
step size `c·t` applied to the pair `(A, B)`. -/
def strangBlock (A B : 𝔸) (s : ℝ) : 𝔸 :=
  exp ((s / 2) • A) * exp (s • B) * exp ((s / 2) • A)

/-- **S₄ = 5 Strang blocks** (Yoshida/Suzuki factorization):
  `suzuki4Exp A B p t = S₂(pt)·S₂(pt)·S₂((1-4p)t)·S₂(pt)·S₂(pt)`.

The 4 junctions between adjacent blocks produce the merged A-exponents
`exp(pt·A)` (between identical blocks) and `exp(((1-3p)/2)·t·A)` (between
`p` and `(1-4p)` blocks), matching the 11-factor `suzuki4Exp` definition. -/
theorem suzuki4Exp_eq_strangProduct (A B : 𝔸) (p t : ℝ) :
    suzuki4Exp A B p t =
      strangBlock A B (p * t) * strangBlock A B (p * t) *
      strangBlock A B ((1 - 4 * p) * t) *
      strangBlock A B (p * t) * strangBlock A B (p * t) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  simp only [suzuki4Exp, strangBlock]
  -- Normalize the `((c*t)/2) • A` form on the RHS to match LHS's `(c/2 * t) • A`.
  have hnorm : ∀ (c : ℝ) (X : 𝔸), (c * t / 2 : ℝ) • X = (c / 2 * t : ℝ) • X := by
    intros c X; congr 1; ring
  simp only [hnorm]
  -- Commutativity of scaled A with scaled A.
  have hcomm : ∀ (s₁ s₂ : ℝ), Commute ((s₁ * t) • A) ((s₂ * t) • A) :=
    fun s₁ s₂ => (Commute.refl A).smul_left _ |>.smul_right _
  -- Merge two adjacent A-factors with argument `(s_i * t) • A`.
  have hmerge_in : ∀ (s₁ s₂ : ℝ) (rest : 𝔸),
      exp ((s₁ * t) • A) * (exp ((s₂ * t) • A) * rest) =
      exp (((s₁ + s₂) * t) • A) * rest := fun s₁ s₂ rest => by
    rw [← mul_assoc, ← exp_add_of_commute (hcomm s₁ s₂), ← add_smul, add_mul]
  -- Reassociate and merge at each of 4 junctions.
  simp only [mul_assoc]
  -- Junction 1 (between blocks 1 and 2): exp(p/2·t·A) · exp(p/2·t·A) = exp(p·t·A)
  rw [show ∀ (rest : 𝔸),
      exp ((p / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
      exp ((p * t) • A) * rest from fun rest => by
    rw [hmerge_in]; congr 2; ring]
  -- Junction 2 (between blocks 2 and 3): p/2·t·A · (1-4p)/2·t·A = (1-3p)/2·t·A
  rw [show ∀ (rest : 𝔸),
      exp ((p / 2 * t) • A) * (exp (((1 - 4 * p) / 2 * t) • A) * rest) =
      exp (((1 - 3 * p) / 2 * t) • A) * rest from fun rest => by
    rw [hmerge_in]; congr 2; ring]
  -- Junction 3 (between blocks 3 and 4): (1-4p)/2·t·A · p/2·t·A = (1-3p)/2·t·A
  rw [show ∀ (rest : 𝔸),
      exp (((1 - 4 * p) / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
      exp (((1 - 3 * p) / 2 * t) • A) * rest from fun rest => by
    rw [hmerge_in]; congr 2; ring]
  -- Junction 4 (between blocks 4 and 5): p/2·t·A · p/2·t·A = p·t·A
  rw [show ∀ (rest : 𝔸),
      exp ((p / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
      exp ((p * t) • A) * rest from fun rest => by
    rw [hmerge_in]; congr 2; ring]

end
