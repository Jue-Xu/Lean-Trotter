/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commutator-Scaling for Second-Order Strang Splitting

The commutator-scaling bound for the second-order Suzuki (Strang) formula,
following the Proposition in Childs et al. (2021), §VII.A.

The symmetric product exp(tA/2)·exp(tB)·exp(tA/2) cancels the first-order
commutator [B,A] (order condition), leaving only **double commutators**
[B,[B,A]] and [A,[A,B]] at cubic order.

## Key identities

The double commutators [B,[B,A/2]] = (1/2)[B,[B,A]] and [A/2,[A/2,B]] = (1/4)[A,[A,B]]
give the prefactors t³/12 and t³/24 in the paper's tight bound.
-/

import LieTrotter.CommutatorScaling

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Phase 1: Double conjugation FTC

The key building block: applying `exp_conj_sub_eq_integral` twice to extract
a double commutator from `exp(τB)·A·exp(-τB) - A`.

The first FTC gives: `exp(τB)·A·exp(-τB) - A = ∫₀ᵗ exp(sB)·[B,A]·exp(-sB) ds`

The integrand `f(s) = exp(sB)·[B,A]·exp(-sB)` itself satisfies:
  `f(s) - f(0) = ∫₀ˢ exp(uB)·[B,[B,A]]·exp(-uB) du`

Combining: the conjugation difference equals [B,A]·τ + double integral of [B,[B,A]].
-/

/-- Double conjugation FTC: expand the conjugation integral to extract the
  double commutator. The difference `exp(τB)·A·exp(-τB) - A - [B,A]·τ`
  equals a double integral of `[B,[B,A]]` terms. -/
theorem exp_conj_sub_comm_eq_double_integral (A B : 𝔸) (τ : ℝ) :
    exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • (B * A - A * B) =
    ∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s,
      exp (u • B) * (B * (B * A - A * B) - (B * A - A * B) * B) *
        exp ((-u) • B) := by
  -- From exp_conj_sub_eq_integral: exp(τB)·A·exp(-τB) - A = ∫₀ᵗ exp(sB)·[B,A]·exp(-sB) ds
  rw [exp_conj_sub_eq_integral A B τ]
  -- ∫₀ᵗ f(s) ds - τ·f(0) = ∫₀ᵗ (f(s) - f(0)) ds  (since ∫₀ᵗ f(0) ds = τ·f(0))
  -- where f(s) = exp(sB)·[B,A]·exp(-sB) and f(0) = [B,A]
  have hf0 : exp ((0:ℝ) • B) * (B * A - A * B) * exp ((-(0:ℝ)) • B) = B * A - A * B := by
    simp [zero_smul, exp_zero]
  -- f(s) - f(0) = exp(sB)·[B,A]·exp(-sB) - [B,A] = ∫₀ˢ exp(uB)·[B,[B,A]]·exp(-uB) du
  -- by applying exp_conj_sub_eq_integral to [B,A] conjugated by B
  sorry

/-!
## Phase 2: Strang residual and first-order cancellation

The Strang product exp(τA/2)·exp(τB)·exp(τA/2) has residual 𝒯₂(τ) consisting
of two conjugation terms whose O(τ) parts cancel.
-/

/-- The Strang integral error representation via Duhamel/FTC-2.
  `exp(t/2·A)·exp(t·B)·exp(t/2·A) - exp(t·(A+B)) = ∫₀ᵗ ...` -/
theorem strang_integral_error (A B : 𝔸) (t : ℝ) :
    exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B)) =
      ∫ τ in (0:ℝ)..t, exp ((t - τ) • (A + B)) *
        ((exp ((τ / 2) • A) * B * exp ((- τ / 2) • A) - B) +
         exp ((τ / 2) • A) * (exp (τ • B) * ((1/2 : ℝ) • A) * exp ((-τ) • B) -
           (1/2 : ℝ) • A) * exp ((-τ / 2) • A)) *
        (exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A)) := by
  sorry

/-!
## Phase 3: Double commutator norm bounds

Bound ‖exp(τB)·A·exp(-τB) - A - [B,A]·τ‖ ≤ ‖[B,[B,A]]‖·τ²/2·exp(2τ‖B‖)
using the double integral representation and `norm_integral_le_of_norm_le_const`.
-/

/-- The double conjugation remainder is bounded by the double commutator norm.
  `‖exp(τB)·A·exp(-τB) - A - [B,A]·τ‖ ≤ ‖[B,[B,A]]‖·τ²/2·exp(2|τ|‖B‖)` -/
theorem norm_exp_conj_sub_comm_le (A B : 𝔸) (τ : ℝ) :
    ‖exp (τ • B) * A * exp ((-τ) • B) - A - τ • (B * A - A * B)‖ ≤
      ‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 2 *
        τ ^ 2 * Real.exp (2 * |τ| * ‖B‖) := by
  sorry

/-!
## Phase 4: Main commutator-scaling theorem for Strang

The bound scales with double commutators ‖[B,[B,A]]‖ and ‖[A,[A,B]]‖ at O(t³).
-/

/-- **Commutator-scaling bound for the second-order Strang formula:**
  The error scales with double commutators at O(t³).

  This improves the cubic bound `7‖A‖²‖B‖ + 3‖A‖‖B‖² + 3‖A‖³` from
  `norm_exp_mul_exp_mul_exp_sub_exp_add_cubic` to double commutator norms.

  In the anti-Hermitian case, the exponential factor is 1, matching the paper's
  tight bound (Proposition in §VII.A). -/
theorem norm_strang_comm_scaling (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤
      (‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
       ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24) *
      t ^ 3 * Real.exp (t * (3 * ‖A‖ + 5 * ‖B‖)) := by
  sorry

end
