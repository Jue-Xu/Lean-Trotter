/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commutator-Scaled Total Error for Strang Splitting

The Strang integrator has had a commutator-scaled *single-step* bound since
Track 6 (`norm_strang_comm_scaling`: `‖S₂(t) − e^{tH}‖ ≤ (‖[B,[B,A]]‖/12 +
‖[A,[A,B]]‖/24)·t³`, anti-Hermitian) and a tighter norm-of-difference step
bound (`norm_strang_comm_scaling_tight`: `‖D‖/6·t³ + T/4·t⁴`).  But its
*total-error* theorem (`strang_error_rate_sq`) still used norm-product
constants `O(‖A‖²‖B‖ + …)` that do **not** vanish for commuting `A, B` —
an asymmetry with S₄, which has both step- and total-error commutator-scaled
bounds (`Suzuki4TightConvergence.lean`).

This file compounds both Strang step bounds over `n` steps in the
anti-Hermitian (unitary) regime, where every factor has norm `1` and the
telescoping damping factor collapses to `1`:

* `strang_total_error_comm_scaling`:

  `‖S₂(t/n)ⁿ − exp(t(A+B))‖ ≤ (‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24) · t³/n²`

  — the compounded form of the Childs et al. (2021) §VII.A Strang bound; the
  `1/n²` coefficient is a double-commutator sum, so it vanishes as
  `[A,B] → 0`.

* `strang_total_error_comm_scaling_tight`:

  `‖S₂(t/n)ⁿ − exp(t(A+B))‖ ≤ ‖D‖/6 · t³/n² + T/4 · t⁴/n³`

  with `D = [B,[B,A′]] − [A′,[A′,B]]` (`A′ = A/2`) — the total-error form of
  this project's tighter norm-of-difference bound; its leading coefficient
  never exceeds the standard one (`norm_D_le_sum_of_norms`).

The proofs mirror `Suzuki4TightConvergence.lean` /
`Suzuki4UnitaryTotalError.lean`: telescoping `norm_pow_sub_pow_le'` with
`max ‖X‖ ‖Y‖ ≤ 1` (three unitary factors per step), exact composition of the
target `exp((t/n)•H)ⁿ = exp(t•H)` (`exp_smul_div_pow`), and `n` copies of the
step bound at `τ = t/n`.

## Hypotheses

The C*-algebra typeclasses of `norm_exp_smul_of_skewAdjoint` plus
`star A = -A`, `star B = -B`, and `0 ≤ t` (inherited from the step bounds).
-/

import LieTrotter.Telescoping
import LieTrotter.StrangCommutatorScaling
import LieTrotter.StrangCommutatorScalingTight
import LieTrotter.Suzuki4Convergence

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- A Strang step `exp((τ/2)•A)·exp(τ•B)·exp((τ/2)•A)` of skew-adjoint
generators is a product of three unitaries, hence has norm `≤ 1`. -/
lemma norm_strang_step_le_one {A B : 𝔸} (hA : star A = -A) (hB : star B = -B)
    (τ : ℝ) : ‖exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A)‖ ≤ 1 := by
  calc ‖exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A)‖
      ≤ ‖exp ((τ / 2) • A)‖ * ‖exp (τ • B)‖ * ‖exp ((τ / 2) • A)‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = 1 := by
        simp [norm_exp_smul_of_skewAdjoint hA, norm_exp_smul_of_skewAdjoint hB]

/-- **Commutator-scaled total error for Strang splitting** (anti-Hermitian):

  `‖S₂(t/n)ⁿ − exp(t(A+B))‖ ≤ (‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24) · t³/n²`.

The `1/n²` coefficient is a double-commutator sum — it vanishes as
`[A,B] → 0`, unlike the norm-product constant of `strang_error_rate_sq`.
Compounds the single-step `norm_strang_comm_scaling` over `n` unitary steps
(damping factor `1`). -/
theorem strang_total_error_comm_scaling (A B : 𝔸) (hA : star A = -A)
    (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (hn : 0 < n) :
    ‖(exp ((t / (n : ℝ) / 2) • A) * exp ((t / (n : ℝ)) • B) *
        exp ((t / (n : ℝ) / 2) • A)) ^ n - exp (t • (A + B))‖ ≤
      (‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
       ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24) * t ^ 3 / (n : ℝ) ^ 2 := by
  have hn_ne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set Ccomm : ℝ := ‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
      ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24 with hC_def
  have hC_nn : 0 ≤ Ccomm := by rw [hC_def]; positivity
  set τ : ℝ := t / (n : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by rw [hτ_def]; exact div_nonneg ht (Nat.cast_nonneg n)
  set X : 𝔸 := exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A) with hX_def
  set Y : 𝔸 := exp (τ • (A + B)) with hY_def
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  -- The target composes exactly.
  have hYpow : Y ^ n = exp (t • (A + B)) := by
    rw [hY_def, hτ_def]; exact exp_smul_div_pow (A + B) t n hn
  rw [← hYpow]
  -- Single-step commutator-scaled error at step size τ = t/n.
  have hstep : ‖X - Y‖ ≤ Ccomm * τ ^ 3 :=
    norm_strang_comm_scaling A B hτ_nn hA hB
  have hstep_nn : (0 : ℝ) ≤ Ccomm * τ ^ 3 := mul_nonneg hC_nn (pow_nonneg hτ_nn 3)
  -- Both factors are contractions: the unitary regime.
  have hX_norm : ‖X‖ ≤ 1 := by rw [hX_def]; exact norm_strang_step_le_one hA hB τ
  have hY_norm : ‖Y‖ ≤ 1 := by
    rw [hY_def]; exact le_of_eq (norm_exp_smul_of_skewAdjoint hAB τ)
  have hmax : max ‖X‖ ‖Y‖ ≤ 1 := max_le hX_norm hY_norm
  -- Telescoping: n copies of the step error, damping factor 1.
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := norm_pow_sub_pow_le' X Y n
    _ ≤ (n : ℝ) * (Ccomm * τ ^ 3) * 1 ^ (n - 1) := by gcongr
    _ = (n : ℝ) * (Ccomm * τ ^ 3) := by rw [one_pow, mul_one]
    _ = Ccomm * t ^ 3 / (n : ℝ) ^ 2 := by
        rw [hτ_def]; field_simp

/-- **Tight (norm-of-difference) commutator-scaled total error for Strang
splitting** (anti-Hermitian):

  `‖S₂(t/n)ⁿ − exp(t(A+B))‖ ≤ ‖D‖/6 · t³/n² + T/4 · t⁴/n³`

where `D = [B,[B,A′]] − [A′,[A′,B]]` with `A′ = A/2` and `T` is the
triple-commutator correction of `norm_strang_comm_scaling_tight`.  This is the
total-error form of the project's tighter Strang bound: its `1/n²` leading
coefficient `‖D‖/6` never exceeds the standard `‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24`
(`norm_D_le_sum_of_norms`), and is strictly smaller whenever the two double
commutators partially cancel. -/
theorem strang_total_error_comm_scaling_tight (A B : 𝔸) (hA : star A = -A)
    (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (hn : 0 < n) :
    let A' := (1/2 : ℝ) • A
    let D := (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
             (A' * (A' * B - B * A') - (A' * B - B * A') * A')
    let T := ‖A' * (A' * (A' * B - B * A') - (A' * B - B * A') * A') -
               (A' * (A' * B - B * A') - (A' * B - B * A') * A') * A'‖ / 3 +
             ‖A' * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
               (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * A'‖ / 2 +
             ‖B * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
               (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * B‖ / 6
    ‖(exp ((t / (n : ℝ) / 2) • A) * exp ((t / (n : ℝ)) • B) *
        exp ((t / (n : ℝ) / 2) • A)) ^ n - exp (t • (A + B))‖ ≤
      ‖D‖ / 6 * t ^ 3 / (n : ℝ) ^ 2 + T / 4 * t ^ 4 / (n : ℝ) ^ 3 := by
  intro A' D T
  have hn_ne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set τ : ℝ := t / (n : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by rw [hτ_def]; exact div_nonneg ht (Nat.cast_nonneg n)
  set X : 𝔸 := exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A) with hX_def
  set Y : 𝔸 := exp (τ • (A + B)) with hY_def
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  -- The target composes exactly.
  have hYpow : Y ^ n = exp (t • (A + B)) := by
    rw [hY_def, hτ_def]; exact exp_smul_div_pow (A + B) t n hn
  rw [← hYpow]
  -- Single-step tight error at step size τ = t/n (the lets are definitional).
  have hstep : ‖X - Y‖ ≤ ‖D‖ / 6 * τ ^ 3 + T / 4 * τ ^ 4 :=
    norm_strang_comm_scaling_tight A B hτ_nn hA hB
  have hT_nn : 0 ≤ T := by
    show 0 ≤ ‖A' * (A' * (A' * B - B * A') - (A' * B - B * A') * A') -
        (A' * (A' * B - B * A') - (A' * B - B * A') * A') * A'‖ / 3 +
      ‖A' * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
        (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * A'‖ / 2 +
      ‖B * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
        (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * B‖ / 6
    positivity
  have hstep_nn : (0 : ℝ) ≤ ‖D‖ / 6 * τ ^ 3 + T / 4 * τ ^ 4 :=
    add_nonneg
      (mul_nonneg (div_nonneg (norm_nonneg D) (by norm_num)) (pow_nonneg hτ_nn 3))
      (mul_nonneg (div_nonneg hT_nn (by norm_num)) (pow_nonneg hτ_nn 4))
  -- Both factors are contractions: the unitary regime.
  have hX_norm : ‖X‖ ≤ 1 := by rw [hX_def]; exact norm_strang_step_le_one hA hB τ
  have hY_norm : ‖Y‖ ≤ 1 := by
    rw [hY_def]; exact le_of_eq (norm_exp_smul_of_skewAdjoint hAB τ)
  have hmax : max ‖X‖ ‖Y‖ ≤ 1 := max_le hX_norm hY_norm
  -- Telescoping: n copies of the tight step error, damping factor 1.
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := norm_pow_sub_pow_le' X Y n
    _ ≤ (n : ℝ) * (‖D‖ / 6 * τ ^ 3 + T / 4 * τ ^ 4) * 1 ^ (n - 1) := by gcongr
    _ = (n : ℝ) * (‖D‖ / 6 * τ ^ 3 + T / 4 * τ ^ 4) := by rw [one_pow, mul_one]
    _ = ‖D‖ / 6 * t ^ 3 / (n : ℝ) ^ 2 + T / 4 * t ^ 4 / (n : ℝ) ^ 3 := by
        rw [hτ_def]; field_simp

end AntiHermitian

end
