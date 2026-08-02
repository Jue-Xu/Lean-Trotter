/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Total Error with Commutator Scaling

`Suzuki4Convergence.lean` compounds the *crude* single-step bound
(`exists_norm_s4Func_sub_exp_le_t5`, whose constant is expressed through `‖A‖`
and `‖B‖`) into `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴`.  That establishes the
*order* but not the *constant*.

This file compounds the **sharp** single-step bound
(`norm_suzuki4_level3_explicit`, whose leading coefficient is the CAS-certified
nested-commutator sum `Σᵢ γᵢ‖Cᵢ‖`) through the same telescoping, giving the
commutator-scaled total error

```
  ‖S₄(t/n)ⁿ − exp(t(A+B))‖  ≤  e^{tK} · (Σᵢ γᵢ‖Cᵢ‖) · t⁵ / n⁴  +  K′ / n⁵
```

with `K = s4Rate A B p + ‖A‖ + ‖B‖` the growth rate of the two factors.  This is
the shape Childs et al. (2021) is cited for: the `1/n⁴` coefficient is a sum of
*nested-commutator norms*, so it collapses when `A` and `B` nearly commute — the
whole point of commutator scaling, and invisible in an `∃ C` statement.

Because `γᵢ ≤ αᵢ` termwise (`bchTightPrefactors_le_childs`), the same bound holds
with Childs's own coefficients `Σᵢ αᵢ‖Cᵢ‖` (`suzuki4_total_error_childs_scaling`).

## Hypotheses

`p` is the Suzuki parameter `1/(4 − 4^{1/3})` (where the γᵢ are certified), `t ≥ 0`,
and nothing else: no C*-algebra, no anti-Hermitian structure.  Any complete normed
algebra with `NormOneClass` will do.
-/

import LieTrotter.Suzuki4Convergence
import LieTrotter.Suzuki4ViaBCH

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **S₄ total error with commutator scaling.**

For `A, B` in a complete normed algebra, `t ≥ 0`, and the Suzuki parameter
`p = 1/(4 − 4^{1/3})`, the `n`-step S₄ product formula satisfies

```
  ‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ e^{tK} · (Σᵢ γᵢ‖Cᵢ‖) · t⁵ / n⁴ + K′/n⁵
```

for all `n ≥ N`, where `K = s4Rate A B p + ‖A‖ + ‖B‖` and the `Cᵢ` are the eight
Childs four-fold nested commutators.

Unlike `suzuki4_total_error_quartic`, the `1/n⁴` coefficient here is **explicit
and commutator-scaled**: it vanishes as `A` and `B` commute. -/
theorem suzuki4_total_error_commutator_scaling (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ K' ≥ (0 : ℝ), ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖suzuki4Exp A B p (t / (n : ℝ)) ^ n - exp (t • (A + B))‖ ≤
        Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) *
          (bchTightPrefactors.boundSum A B * t ^ 5) / (n : ℝ) ^ 4
        + K' / (n : ℝ) ^ 5 := by
  set p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3)) with hp_def
  -- The sharp single-step bound: leading coefficient = the certified γ-sum.
  obtain ⟨δ, hδ_pos, K₀, hK₀_nn, hstep⟩ := norm_suzuki4_level3_explicit A B
  set Sbs := bchTightPrefactors.boundSum A B with hSbs_def
  have hSbs_nn : 0 ≤ Sbs := bchTightPrefactors.boundSum_nonneg A B
  clear_value Sbs
  -- A single rate dominating both `‖S₄(τ)‖` and `‖exp(τ(A+B))‖`.
  set K : ℝ := s4Rate A B p + ‖A‖ + ‖B‖ with hK_def
  have hrate_nn : 0 ≤ s4Rate A B p := s4Rate_nonneg A B p
  have hK_nn : 0 ≤ K := by
    rw [hK_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hrate_le_K : s4Rate A B p ≤ K := by
    rw [hK_def]; linarith [norm_nonneg A, norm_nonneg B]
  have hAB_le_K : ‖A‖ + ‖B‖ ≤ K := by rw [hK_def]; linarith
  have hE_pos : (0 : ℝ) < Real.exp (t * K) := Real.exp_pos _
  refine ⟨Real.exp (t * K) * (K₀ * t ^ 6), by positivity, ?_⟩
  -- Threshold: `n > t/δ` puts the step size inside the BCH regime.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (t / δ)
  refine ⟨N₀ + 1, by omega, ?_⟩
  intro n hn
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  set τ : ℝ := t / (n : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by rw [hτ_def]; positivity
  have habs_τ : |τ| = τ := abs_of_nonneg hτ_nn
  -- The step size is inside the regime of the sharp bound.
  have hτ_lt : τ < δ := by
    rw [hτ_def, div_lt_iff₀ hn_posR]
    have hN₀n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N₀ ≤ n)
    have h1 : t / δ < (n : ℝ) := lt_of_lt_of_le hN₀ hN₀n
    calc t = t / δ * δ := by field_simp
      _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right h1 hδ_pos
      _ = δ * (n : ℝ) := by ring
  set X : 𝔸 := suzuki4Exp A B p τ with hX_def
  set Y : 𝔸 := exp (τ • (A + B)) with hY_def
  -- The target composes exactly.
  have hYpow : Y ^ n = exp (t • (A + B)) := by
    rw [hY_def, hτ_def]; exact exp_smul_div_pow (A + B) t n hn_pos
  rw [← hYpow]
  -- Sharp single-step error at step size τ = t/n.
  have hstep_n : ‖X - Y‖ ≤ τ ^ 5 * Sbs + K₀ * τ ^ 6 := hstep τ hτ_nn hτ_lt
  -- Both factors grow at most like `exp(τ·K)`.
  have hX_norm : ‖X‖ ≤ Real.exp (τ * K) := by
    rw [hX_def]
    refine le_trans (norm_suzuki4Exp_le A B p τ) (Real.exp_le_exp.mpr ?_)
    rw [habs_τ]
    exact mul_le_mul_of_nonneg_left hrate_le_K hτ_nn
  have hY_norm : ‖Y‖ ≤ Real.exp (τ * K) := by
    rw [hY_def]
    refine le_trans (norm_exp_le (𝕂 := ℝ) _) (Real.exp_le_exp.mpr ?_)
    calc ‖τ • (A + B)‖ = |τ| * ‖A + B‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ τ * K := by
          rw [habs_τ]
          exact mul_le_mul_of_nonneg_left ((norm_add_le A B).trans hAB_le_K) hτ_nn
  have hmax : max ‖X‖ ‖Y‖ ≤ Real.exp (τ * K) := max_le hX_norm hY_norm
  -- Telescoping (Task A2).
  have htel := norm_pow_sub_pow_le' X Y n
  have hstep_nn : (0 : ℝ) ≤ τ ^ 5 * Sbs + K₀ * τ ^ 6 := by positivity
  have hnstep_nn : (0 : ℝ) ≤ (n : ℝ) * (τ ^ 5 * Sbs + K₀ * τ ^ 6) :=
    mul_nonneg hn_posR.le hstep_nn
  have hbase_one : (1 : ℝ) ≤ Real.exp (τ * K) := by
    have h0 : (0 : ℝ) ≤ τ * K := mul_nonneg hτ_nn hK_nn
    linarith [Real.add_one_le_exp (τ * K)]
  -- The damping factor is a constant: `exp(τ·K)^(n-1) ≤ exp(t·K)`.
  have hexp_pow : (Real.exp (τ * K)) ^ (n - 1) ≤ Real.exp (t * K) := by
    calc (Real.exp (τ * K)) ^ (n - 1)
        ≤ (Real.exp (τ * K)) ^ n := pow_le_pow_right₀ hbase_one (by omega)
      _ = Real.exp ((n : ℝ) * (τ * K)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (t * K) := by
          congr 1; rw [hτ_def]; field_simp
  -- n copies of the sharp step error, damped by a constant.
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := htel
    _ ≤ (n : ℝ) * (τ ^ 5 * Sbs + K₀ * τ ^ 6) * (Real.exp (τ * K)) ^ (n - 1) := by gcongr
    _ ≤ (n : ℝ) * (τ ^ 5 * Sbs + K₀ * τ ^ 6) * Real.exp (t * K) :=
        mul_le_mul_of_nonneg_left hexp_pow hnstep_nn
    _ = Real.exp (t * K) * (Sbs * t ^ 5) / (n : ℝ) ^ 4
          + Real.exp (t * K) * (K₀ * t ^ 6) / (n : ℝ) ^ 5 := by
        rw [hτ_def]; field_simp

/-- **S₄ total error with Childs's coefficients.**  Same statement, with the
leading `1/n⁴` coefficient given by Childs's own `Σᵢ αᵢ‖Cᵢ‖` — obtained from
the sharp γ-form by the termwise inequality `γᵢ ≤ αᵢ`. -/
theorem suzuki4_total_error_childs_scaling (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ K' ≥ (0 : ℝ), ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖suzuki4Exp A B p (t / (n : ℝ)) ^ n - exp (t • (A + B))‖ ≤
        Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) *
          (childsBoundSum A B * t ^ 5) / (n : ℝ) ^ 4
        + K' / (n : ℝ) ^ 5 := by
  intro p
  obtain ⟨K', hK'_nn, N, hN_pos, h⟩ := suzuki4_total_error_commutator_scaling A B ht
  refine ⟨K', hK'_nn, N, hN_pos, fun n hn => le_trans (h n hn) ?_⟩
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hE : (0 : ℝ) ≤ Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) := (Real.exp_pos _).le
  have ht5 : (0 : ℝ) ≤ t ^ 5 := by positivity
  -- Only the leading coefficient changes: γ-sum ≤ α-sum termwise.
  have key : Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) *
        (bchTightPrefactors.boundSum A B * t ^ 5) ≤
      Real.exp (t * (s4Rate A B p + ‖A‖ + ‖B‖)) * (childsBoundSum A B * t ^ 5) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (bchTightPrefactors_le_childs A B) ht5) hE
  have hdiv := (div_le_div_iff_of_pos_right (pow_pos hn_posR 4)).mpr key
  linarith [hdiv]
