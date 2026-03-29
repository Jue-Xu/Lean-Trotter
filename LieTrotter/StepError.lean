/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track C: Quadratic Step Error

The key estimate: ‖exp(a)exp(b) - exp(a+b)‖ ≤ 2‖a‖‖b‖ exp(‖a‖+‖b‖)
and its specialization to the Lie-Trotter step with a = A/n, b = B/n.
-/

import LieTrotter.ExpBounds

open NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-!
## C1: Quadratic error bound (HARDEST LEMMA)

`‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`

Recommended approach: second-order expansion.
Write `exp(a) = 1 + a + Rₐ`, `exp(b) = 1 + b + R_b` with
`‖Rₐ‖ ≤ ‖a‖²/2 · exp(‖a‖)` (from B4).
Then expand the product and bound each cross term.
-/

-- Auxiliary: Real.exp x - 1 ≤ x * Real.exp x for x ≥ 0
private lemma exp_sub_one_le_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have hexp_pos := Real.exp_pos x
  have h2 : (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x := by
    exact mul_le_mul_of_nonneg_right h1 hexp_pos.le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  linarith

-- Auxiliary: bound on the cross term ‖exp(a+b) - exp(a) - exp(b) + 1‖
-- This requires a power series argument (bounding termwise:
-- ‖(a+b)^k - a^k - b^k‖ ≤ (‖a‖+‖b‖)^k - ‖a‖^k - ‖b‖^k for k ≥ 2,
-- then summing to get (e^‖a‖ - 1)(e^‖b‖ - 1)).
private lemma norm_exp_cross_term_le (a b : 𝔸) :
    ‖exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
  sorry

/-- **Key estimate**: `‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`.
    This is the hardest lemma in the formalization. -/
theorem norm_exp_mul_exp_sub_exp_add' (a b : 𝔸) :
    ‖exp 𝕂 a * exp 𝕂 b - exp 𝕂 (a + b)‖ ≤
      2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
  -- Step 1: Algebraic identity
  have algebraic_id : exp 𝕂 a * exp 𝕂 b - exp 𝕂 (a + b) =
      (exp 𝕂 a - 1) * (exp 𝕂 b - 1) -
      (exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1) := by ring
  rw [algebraic_id]
  -- Step 2: Triangle inequality + bound each part
  have h_part1 : ‖(exp 𝕂 a - 1) * (exp 𝕂 b - 1)‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
    calc ‖(exp 𝕂 a - 1) * (exp 𝕂 b - 1)‖
        ≤ ‖exp 𝕂 a - 1‖ * ‖exp 𝕂 b - 1‖ := norm_mul_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
          apply mul_le_mul
          · exact norm_exp_sub_one_le a
          · exact norm_exp_sub_one_le b
          · exact norm_nonneg _
          · linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
  have h_part2 : ‖exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) :=
    norm_exp_cross_term_le a b
  -- Step 3: Combine via triangle inequality
  have h_sum : ‖(exp 𝕂 a - 1) * (exp 𝕂 b - 1) -
      (exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1)‖ ≤
      2 * ((Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1)) := by
    calc ‖(exp 𝕂 a - 1) * (exp 𝕂 b - 1) -
          (exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1)‖
        ≤ ‖(exp 𝕂 a - 1) * (exp 𝕂 b - 1)‖ +
          ‖exp 𝕂 (a + b) - exp 𝕂 a - exp 𝕂 b + 1‖ := norm_sub_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
          (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := add_le_add h_part1 h_part2
      _ = 2 * ((Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1)) := by ring
  -- Step 4: Bound (e^s - 1)(e^t - 1) ≤ st * e^(s+t)
  have h_bound : 2 * ((Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1)) ≤
      2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
    have ha : Real.exp ‖a‖ - 1 ≤ ‖a‖ * Real.exp ‖a‖ :=
      exp_sub_one_le_mul_exp (norm_nonneg a)
    have hb : Real.exp ‖b‖ - 1 ≤ ‖b‖ * Real.exp ‖b‖ :=
      exp_sub_one_le_mul_exp (norm_nonneg b)
    have h_ea_nonneg : 0 ≤ Real.exp ‖a‖ - 1 := by
      linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
    have h_eb_nonneg : 0 ≤ Real.exp ‖b‖ - 1 := by
      linarith [Real.add_one_le_exp ‖b‖, norm_nonneg b]
    calc 2 * ((Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1))
        ≤ 2 * (‖a‖ * Real.exp ‖a‖ * (‖b‖ * Real.exp ‖b‖)) := by
          gcongr
          exact mul_le_mul ha hb h_eb_nonneg (by positivity)
      _ = 2 * ‖a‖ * ‖b‖ * (Real.exp ‖a‖ * Real.exp ‖b‖) := by ring
      _ = 2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
          rw [Real.exp_add]
  linarith

/-!
## C2: Lie-Trotter step error

Specialization of C1 to `a = A/n`, `b = B/n`:
`‖exp(A/n) exp(B/n) - exp((A+B)/n)‖ ≤ 2‖A‖‖B‖/n² · exp((‖A‖+‖B‖)/n)`
-/

/-- The quadratic step error for Lie-Trotter:
    `‖exp(A/n) exp(B/n) - exp((A+B)/n)‖ ≤ 2‖A‖‖B‖/n² · exp((‖A‖+‖B‖)/n)`. -/
theorem lie_trotter_step_error (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B) -
     exp 𝕂 ((n : 𝕂)⁻¹ • (A + B))‖ ≤
      2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / n) := by
  have smul_sum : (n : 𝕂)⁻¹ • A + (n : 𝕂)⁻¹ • B = (n : 𝕂)⁻¹ • (A + B) :=
    (smul_add _ A B).symm
  rw [← smul_sum]
  have h_C1 := norm_exp_mul_exp_sub_exp_add' (𝕂 := 𝕂)
    ((n : 𝕂)⁻¹ • A) ((n : 𝕂)⁻¹ • B)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have norm_a : ‖(n : 𝕂)⁻¹ • A‖ = ‖A‖ / n := by
    rw [norm_smul, norm_inv_n, div_eq_inv_mul]
  have norm_b : ‖(n : 𝕂)⁻¹ • B‖ = ‖B‖ / n := by
    rw [norm_smul, norm_inv_n, div_eq_inv_mul]
  rw [norm_a, norm_b] at h_C1
  calc ‖exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B) -
        exp 𝕂 ((n : 𝕂)⁻¹ • A + (n : 𝕂)⁻¹ • B)‖
      ≤ 2 * (‖A‖ / ↑n) * (‖B‖ / ↑n) * Real.exp (‖A‖ / ↑n + ‖B‖ / ↑n) := h_C1
    _ = 2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / ↑n) := by
        have hn_ne_zero : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        field_simp
        ring
