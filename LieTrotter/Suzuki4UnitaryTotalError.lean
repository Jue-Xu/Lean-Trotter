/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Total Error for Anti-Hermitian Generators: No Growth Factor

The general total-error bounds for the S₄ integrator
(`suzuki4_total_error_commutator_scaling` in `Suzuki4TightConvergence.lean`,
`suzuki4_total_error_quartic` in `Suzuki4Convergence.lean`) carry an
exponential damping factor `e^{tK}` with `K = s4Rate A B p + ‖A‖ + ‖B‖`,
because in a general normed algebra both `‖S₄(τ)‖` and `‖exp(τ(A+B))‖` can
grow like `exp(|τ|·K)` and the telescoping accumulates `n − 1` such factors.

For the physically central case — **anti-Hermitian** generators `star A = -A`,
`star B = -B` in a C*-algebra, i.e. Hamiltonian simulation with `A = -iH₁`,
`B = -iH₂` — every exponential in sight is *unitary*, so all eleven factors of
`S₄(τ)` and the target `exp(τ(A+B))` have norm exactly `1`
(`norm_exp_smul_of_skewAdjoint`).  The damping factor collapses to `1` and the
total error is exactly `n` copies of the single-step error:

```
  ‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ (Σᵢ γᵢ‖Cᵢ‖) · t⁵ / n⁴ + K′ / n⁵
```

(`suzuki4_total_error_commutator_scaling_of_skewAdjoint`), with the same
CAS-certified commutator-scaled leading coefficient as the general bound but
**no** `e^{tK}` prefactor.  The same specialization of the crude `∃ C` bound is
`suzuki4_total_error_quartic_of_skewAdjoint`, whose constant is
`C₀·|t|⁵ + 1` — again free of the exponential factor buried in the general
`suzuki4_total_error_quartic`.

## Building blocks

* `norm_suzuki4Exp_le_one` — `‖S₄(τ)‖ ≤ 1`: the five Strang blocks
  (`suzuki4Exp_eq_strangProduct`) each consist of three unitary exponentials.
* `norm_exp_smul_add_of_skewAdjoint` — `‖exp(τ•(A+B))‖ = 1`: sums of
  skew-adjoint elements are skew-adjoint.

## Hypotheses

The C*-algebra typeclasses of `norm_exp_smul_of_skewAdjoint`
(`[StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
[StarModule ℝ 𝔸]`) plus `star A = -A`, `star B = -B`.  The commutator-scaled
bounds are stated at the Suzuki parameter `p = 1/(4 − 4^{1/3})` (where the γᵢ
are certified) and, like their general counterparts, keep `ht : 0 ≤ t` because
the sharp step bound `norm_suzuki4_level3_explicit` is stated for `0 ≤ τ`.
The crude quartic bound needs neither `0 ≤ t` nor a specific `p`, only
`IsSuzukiCubic p`.
-/

import LieTrotter.Suzuki4TightConvergence
import LieTrotter.StrangCommutatorScaling

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-!
## Unit-norm facts

In a C*-algebra, `exp` of a real multiple of a skew-adjoint element is unitary
(`norm_exp_smul_of_skewAdjoint`).  We record the two consequences the
total-error bounds need: the target exponential has norm `1`, and the full
11-factor S₄ product has norm `≤ 1`.
-/

/-- The target exponential is unitary: `‖exp(τ•(A+B))‖ = 1` for skew-adjoint
`A, B` (the sum of skew-adjoint elements is skew-adjoint). -/
theorem norm_exp_smul_add_of_skewAdjoint {A B : 𝔸} (hA : star A = -A)
    (hB : star B = -B) (τ : ℝ) :
    ‖exp (τ • (A + B))‖ = 1 :=
  norm_exp_smul_of_skewAdjoint (by rw [star_add, hA, hB, neg_add]) τ

/-- A Strang block `S₂(s) = exp((s/2)•A)·exp(s•B)·exp((s/2)•A)` of skew-adjoint
generators is a product of three unitaries, hence has norm `≤ 1`. -/
lemma norm_strangBlock_le_one {A B : 𝔸} (hA : star A = -A) (hB : star B = -B)
    (s : ℝ) : ‖strangBlock A B s‖ ≤ 1 := by
  unfold strangBlock
  calc ‖exp ((s / 2) • A) * exp (s • B) * exp ((s / 2) • A)‖
      ≤ ‖exp ((s / 2) • A)‖ * ‖exp (s • B)‖ * ‖exp ((s / 2) • A)‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = 1 := by
        simp [norm_exp_smul_of_skewAdjoint hA, norm_exp_smul_of_skewAdjoint hB]

/-- **S₄ is a contraction for skew-adjoint generators**: `‖S₄(τ)‖ ≤ 1`.

Via `suzuki4Exp_eq_strangProduct`, S₄ is a product of five Strang blocks, each
of norm `≤ 1` by `norm_strangBlock_le_one`.  This replaces the growth bound
`norm_suzuki4Exp_le` (`‖S₄(τ)‖ ≤ exp(|τ|·s4Rate)`) of the general theory. -/
theorem norm_suzuki4Exp_le_one {A B : 𝔸} (hA : star A = -A) (hB : star B = -B)
    (p τ : ℝ) : ‖suzuki4Exp A B p τ‖ ≤ 1 := by
  rw [suzuki4Exp_eq_strangProduct]
  have h : ∀ s : ℝ, ‖strangBlock A B s‖ ≤ 1 := norm_strangBlock_le_one hA hB
  have hmul : ∀ x y : 𝔸, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := fun x y hx hy =>
    (norm_mul_le x y).trans (mul_le_one₀ hx (norm_nonneg y) hy)
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (h _) (h _)) (h _)) (h _)) (h _)

/-!
## Total-error bounds without the growth factor

The proofs mirror `suzuki4_total_error_commutator_scaling` and
`suzuki4_total_error_quartic` verbatim, replacing the growth-rate estimates
`‖X‖, ‖Y‖ ≤ exp(τK)` by the unit-norm facts above, so the telescoping damping
factor `max(‖X‖,‖Y‖)^{n−1}` is `≤ 1` instead of `≤ e^{tK}`.
-/

/-- **S₄ total error with commutator scaling, anti-Hermitian case.**

For skew-adjoint `A, B` in a C*-algebra, `t ≥ 0`, and the Suzuki parameter
`p = 1/(4 − 4^{1/3})`, the `n`-step S₄ product formula satisfies

```
  ‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ (Σᵢ γᵢ‖Cᵢ‖) · t⁵ / n⁴ + K′/n⁵
```

for all `n ≥ N`, where the `Cᵢ` are the eight Childs four-fold nested
commutators.  This is `suzuki4_total_error_commutator_scaling` with the
exponential damping factor `e^{t(s4Rate + ‖A‖ + ‖B‖)}` replaced by `1`:
in the unitary regime the total error is exactly `n` copies of the
single-step error — nothing accumulates. -/
theorem suzuki4_total_error_commutator_scaling_of_skewAdjoint {A B : 𝔸}
    (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ K' ≥ (0 : ℝ), ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖suzuki4Exp A B p (t / (n : ℝ)) ^ n - exp (t • (A + B))‖ ≤
        (bchTightPrefactors.boundSum A B * t ^ 5) / (n : ℝ) ^ 4
        + K' / (n : ℝ) ^ 5 := by
  set p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3)) with hp_def
  -- The sharp single-step bound: leading coefficient = the certified γ-sum.
  obtain ⟨δ, hδ_pos, K₀, hK₀_nn, hstep⟩ := norm_suzuki4_level3_explicit A B
  set Sbs := bchTightPrefactors.boundSum A B with hSbs_def
  have hSbs_nn : 0 ≤ Sbs := bchTightPrefactors.boundSum_nonneg A B
  clear_value Sbs
  refine ⟨K₀ * t ^ 6, by positivity, ?_⟩
  -- Threshold: `n > t/δ` puts the step size inside the BCH regime.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (t / δ)
  refine ⟨N₀ + 1, by omega, ?_⟩
  intro n hn
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  set τ : ℝ := t / (n : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by rw [hτ_def]; positivity
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
  -- Both factors are contractions: the unitary regime.
  have hX_norm : ‖X‖ ≤ 1 := by
    rw [hX_def]; exact norm_suzuki4Exp_le_one hA hB p τ
  have hY_norm : ‖Y‖ ≤ 1 := by
    rw [hY_def]; exact le_of_eq (norm_exp_smul_add_of_skewAdjoint hA hB τ)
  have hmax : max ‖X‖ ‖Y‖ ≤ 1 := max_le hX_norm hY_norm
  -- Telescoping (Task A2).
  have htel := norm_pow_sub_pow_le' X Y n
  have hstep_nn : (0 : ℝ) ≤ τ ^ 5 * Sbs + K₀ * τ ^ 6 := by positivity
  -- n copies of the sharp step error, with damping factor 1.
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := htel
    _ ≤ (n : ℝ) * (τ ^ 5 * Sbs + K₀ * τ ^ 6) * 1 ^ (n - 1) := by gcongr
    _ = (n : ℝ) * (τ ^ 5 * Sbs + K₀ * τ ^ 6) := by rw [one_pow, mul_one]
    _ = Sbs * t ^ 5 / (n : ℝ) ^ 4 + K₀ * t ^ 6 / (n : ℝ) ^ 5 := by
        rw [hτ_def]; field_simp

/-- **S₄ total error with Childs's coefficients, anti-Hermitian case.**  Same
statement, with the leading `1/n⁴` coefficient given by Childs's own
`Σᵢ αᵢ‖Cᵢ‖` — obtained from the sharp γ-form by the termwise inequality
`γᵢ ≤ αᵢ`. -/
theorem suzuki4_total_error_childs_scaling_of_skewAdjoint {A B : 𝔸}
    (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ∃ K' ≥ (0 : ℝ), ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖suzuki4Exp A B p (t / (n : ℝ)) ^ n - exp (t • (A + B))‖ ≤
        (childsBoundSum A B * t ^ 5) / (n : ℝ) ^ 4 + K' / (n : ℝ) ^ 5 := by
  intro p
  obtain ⟨K', hK'_nn, N, hN_pos, h⟩ :=
    suzuki4_total_error_commutator_scaling_of_skewAdjoint hA hB ht
  refine ⟨K', hK'_nn, N, hN_pos, fun n hn => le_trans (h n hn) ?_⟩
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht5 : (0 : ℝ) ≤ t ^ 5 := by positivity
  -- Only the leading coefficient changes: γ-sum ≤ α-sum termwise.
  have key : bchTightPrefactors.boundSum A B * t ^ 5 ≤ childsBoundSum A B * t ^ 5 :=
    mul_le_mul_of_nonneg_right (bchTightPrefactors_le_childs A B) ht5
  have hdiv := (div_le_div_iff_of_pos_right (pow_pos hn_posR 4)).mpr key
  linarith [hdiv]

/-- **S₄ quartic total-error rate, anti-Hermitian case.**

Under the Suzuki cubic condition, for skew-adjoint `A, B`:

  `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ (C₀·|t|⁵ + 1)/n⁴`   for all `n ≥ N`,

where `C₀` is the single-step BCH constant of
`exists_norm_s4Func_sub_exp_le_t5`.  Unlike the general
`suzuki4_total_error_quartic`, whose constant is `C₀·|t|⁵·e^{|t|K} + 1`, the
constant here contains **no exponential growth factor**: both `S₄(τ)` and the
target exponential are contractions, so the telescoping damping factor is `1`.
Needs neither `0 ≤ t` nor the specific Suzuki parameter. -/
theorem suzuki4_total_error_quartic_of_skewAdjoint {A B : 𝔸}
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) (hp : IsSuzukiCubic p)
    (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖ ≤
        C / (n : ℝ) ^ 4 := by
  -- SLICE 1: the axiom-free single-step O(|τ|⁵) BCH bound.
  obtain ⟨δ, hδ_pos, C₀, hC₀_nn, hstep⟩ := exists_norm_s4Func_sub_exp_le_t5 A B p hp
  -- The constant: no exponential factor.
  set Cbase : ℝ := C₀ * |t| ^ 5 with hCbase_def
  have hCbase_nn : 0 ≤ Cbase := by rw [hCbase_def]; positivity
  -- The threshold: `n > |t|/δ` forces the step size into the BCH regime.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (|t| / δ)
  refine ⟨Cbase + 1, by linarith, N₀ + 1, by omega, ?_⟩
  intro n hn
  have hn_pos : 0 < n := by omega
  have hn_posR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have habs_tn : |t / (n : ℝ)| = |t| / (n : ℝ) := by rw [abs_div, Nat.abs_cast]
  -- The step size is inside the BCH regime.
  have hτ_lt : |t / (n : ℝ)| < δ := by
    rw [habs_tn, div_lt_iff₀ hn_posR]
    have hN₀n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N₀ ≤ n)
    have h1 : |t| / δ < (n : ℝ) := lt_of_lt_of_le hN₀ hN₀n
    calc |t| = |t| / δ * δ := by field_simp
      _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right h1 hδ_pos
      _ = δ * (n : ℝ) := by ring
  set X : 𝔸 := suzuki4Exp A B p (t / (n : ℝ)) with hX_def
  set Y : 𝔸 := exp ((t / (n : ℝ)) • (A + B)) with hY_def
  -- The target composes exactly: no error from the exponential side.
  have hYpow : Y ^ n = exp (t • (A + B)) := by
    rw [hY_def]; exact exp_smul_div_pow (A + B) t n hn_pos
  rw [← hYpow]
  -- Single-step error at step size `t/n`.
  have hstep_n : ‖X - Y‖ ≤ C₀ * |t / (n : ℝ)| ^ 5 := by
    rw [hX_def, hY_def, ← s4Func_eq_suzuki4Exp]
    exact hstep (t / (n : ℝ)) hτ_lt
  -- Both factors are contractions: the unitary regime.
  have hX_norm : ‖X‖ ≤ 1 := by
    rw [hX_def]; exact norm_suzuki4Exp_le_one hA hB p _
  have hY_norm : ‖Y‖ ≤ 1 := by
    rw [hY_def]; exact le_of_eq (norm_exp_smul_add_of_skewAdjoint hA hB _)
  have hmax : max ‖X‖ ‖Y‖ ≤ 1 := max_le hX_norm hY_norm
  -- Telescoping (Task A2).
  have htel := norm_pow_sub_pow_le' X Y n
  -- n copies of an O(n⁻⁵) step error, with damping factor 1 ⟹ O(n⁻⁴).
  calc ‖X ^ n - Y ^ n‖
      ≤ (n : ℝ) * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := htel
    _ ≤ (n : ℝ) * (C₀ * |t / (n : ℝ)| ^ 5) * 1 ^ (n - 1) := by gcongr
    _ = (n : ℝ) * (C₀ * |t / (n : ℝ)| ^ 5) := by rw [one_pow, mul_one]
    _ = Cbase / (n : ℝ) ^ 4 := by
        rw [hCbase_def, habs_tn]; field_simp
    _ ≤ (Cbase + 1) / (n : ℝ) ^ 4 :=
        (div_le_div_iff_of_pos_right (pow_pos hn_posR 4)).mpr
          (le_add_of_nonneg_right zero_le_one)

end AntiHermitian

end
