/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commutator-Scaling Trotter Error

The integral representation of the Lie-Trotter error via the variation-of-parameters
(Duhamel) formula, and the commutator-scaling bound:

  ‖exp(tB) exp(tA) - exp(t(A+B))‖ ≤ ‖[B,A]‖/2 · t² · exp(t(‖A‖+3‖B‖))

This improves the quadratic bound ‖a‖‖b‖ from StepError.lean to the commutator ‖[b,a]‖,
following Childs et al., "Theory of Trotter Error with Commutator Scaling" (2021).

## Proof strategy

1. Define w(τ) = exp(-τ(A+B)) · exp(τB) · exp(τA)
2. Compute w'(τ) via product rule → exp(-τ(A+B)) · [exp(τB), A] · exp(τA)
3. FTC-2: w(t) - w(0) = ∫₀ᵗ w'(τ) dτ → integral error representation
4. Extract [B,A] from [exp(τB), A] via FTC on s ↦ exp(sB) · A · exp(-sB)
5. Bound everything to get the commutator-scaling result
-/

import LieTrotter.ExpBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

-- We work over ℝ directly. For 𝕂 = ℂ applications, use NormedAlgebra.restrictScalars.
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Layer 0: Exponential algebra helpers

Scalar multiples of the same element always commute, so exp(t•H) and exp(-t•H)
are mutual inverses.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma commute_smul_self (H : 𝔸) (s t : ℝ) :
    Commute (s • H) (t • H) :=
  (Commute.refl H).smul_left s |>.smul_right t

/-- `exp(t • H) * exp((-t) • H) = 1` via commutativity of scalar multiples. -/
lemma exp_smul_mul_exp_neg_smul (H : 𝔸) (t : ℝ) :
    exp (t • H) * exp ((-t) • H) = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (commute_smul_self H t (-t))]
  simp [← add_smul]

/-- `exp((-t) • H) * exp(t • H) = 1` via commutativity of scalar multiples. -/
lemma exp_neg_smul_mul_exp_smul (H : 𝔸) (t : ℝ) :
    exp ((-t) • H) * exp (t • H) = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (commute_smul_self H (-t) t)]
  simp [← add_smul]

/-!
## Layer 1: Derivative computations

We compute derivatives of:
- `s ↦ exp(sB) · A · exp(-sB)` (conjugation)
- `τ ↦ exp(-τ(A+B)) · exp(τB) · exp(τA)` (conjugated Trotter product)

Both use `hasDerivAt_exp_smul_const'` and the product rule `HasDerivAt.mul`.
-/

/-- The derivative of the conjugation `s ↦ exp(sB) * A * exp((-s) • B)` is
  `exp(sB) * (B * A - A * B) * exp((-s) • B)`. -/
lemma hasDerivAt_exp_conj (A B : 𝔸) (s : ℝ) :
    HasDerivAt (fun u => exp (u • B) * A * exp ((-u) • B))
      (exp (s • B) * (B * A - A * B) * exp ((-s) • B)) s := by
  -- Normalize (-u) • B to u • (-B) so hasDerivAt_exp_smul_const' applies directly
  simp_rw [show ∀ u : ℝ, (-u) • B = u • (-B) from fun u => by rw [neg_smul, smul_neg]]
  -- Derivatives of each factor
  have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B s
  have hNB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-B) s
  -- d/du[A * exp(u•(-B))] = A * ((-B) * exp(s•(-B)))
  have hANB : HasDerivAt (fun u => A * exp (u • (-B)))
      (A * ((-B) * exp (s • (-B)))) s := by
    simpa using (hasDerivAt_const s A).mul hNB
  -- Rewrite f(u) = exp(u•B) * (A * exp(u•(-B))) using associativity
  have hassoc : (fun u : ℝ => exp (u • B) * A * exp (u • (-B))) =
      (fun u : ℝ => exp (u • B) * (A * exp (u • (-B)))) := by
    ext u; exact mul_assoc _ _ _
  rw [hassoc]
  -- Apply product rule and simplify
  have hProd := hB.mul hANB
  convert hProd using 1
  have hcomm : B * exp (s • B) = exp (s • B) * B :=
    ((Commute.refl B).smul_right s).exp_right.eq
  rw [hcomm]; noncomm_ring

/-- The derivative of `τ ↦ exp((-τ) • (A+B)) * (exp(τ • B) * exp(τ • A))` is
  `exp((-τ)(A+B)) * (exp(τB)*A - A*exp(τB)) * exp(τA)`. -/
lemma hasDerivAt_conj_trotter (A B : 𝔸) (τ : ℝ) :
    HasDerivAt (fun u => exp ((-u) • (A + B)) * (exp (u • B) * exp (u • A)))
      (exp ((-τ) • (A + B)) * ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))) τ := by
  -- Normalize (-u) • (A+B) to u • (-(A+B))
  simp_rw [show ∀ u : ℝ, (-u) • (A + B) = u • (-(A + B)) from
    fun u => by rw [neg_smul, smul_neg]]
  -- Derivatives of each factor
  have hAB : HasDerivAt (fun u => exp (u • (-(A + B))))
      ((-(A + B)) * exp (τ • (-(A + B)))) τ :=
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-(A + B)) τ
  have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B τ
  have hA := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A τ
  -- d/du[exp(u•B) * exp(u•A)]
  have hBA := hB.mul hA
  -- d/du[exp(u•(-(A+B))) * (exp(u•B) * exp(u•A))]
  have hFull := hAB.mul hBA
  convert hFull using 1
  -- Use commutativity of (A+B) with its own exponential, then noncomm_ring
  set E := exp (τ • (-(A + B)))
  have hcomm : (A + B) * E = E * (A + B) :=
    ((Commute.refl (A + B)).neg_right.smul_right τ).exp_right.eq
  have h1 : -(A + B) * E = -(E * (A + B)) := by rw [neg_mul, hcomm]
  rw [h1]; simp only [Pi.mul_apply]; noncomm_ring

/-!
## Layer 2: Continuity

The integrands from Layer 1 are continuous (compositions of continuous functions).
-/

private lemma continuous_exp_smul (x : 𝔸) : Continuous (fun (t : ℝ) => exp (t • x)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact exp_continuous.comp (continuous_id.smul continuous_const)

private lemma continuous_exp_neg_smul (x : 𝔸) : Continuous (fun (t : ℝ) => exp ((-t) • x)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact exp_continuous.comp (continuous_neg.smul continuous_const)

lemma continuous_exp_conj_deriv (A B : 𝔸) :
    Continuous (fun (s : ℝ) => exp (s • B) * (B * A - A * B) * exp ((-s) • B)) :=
  ((continuous_exp_smul B).mul continuous_const).mul (continuous_exp_neg_smul B)

lemma continuous_conj_trotter_deriv (A B : 𝔸) :
    Continuous (fun (τ : ℝ) => exp ((-τ) • (A + B)) *
      ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))) :=
  (continuous_exp_neg_smul (A + B)).mul
    (((continuous_exp_smul B).mul continuous_const).sub
      (continuous_const.mul (continuous_exp_smul B)) |>.mul (continuous_exp_smul A))

/-!
## Layer 3: FTC-2 applications

Apply the fundamental theorem of calculus to obtain integral representations.
-/

/-- Conjugation FTC: `exp(τB) * A * exp(-τB) - A = ∫₀ᵗ exp(sB) * [B,A] * exp(-sB) ds`. -/
theorem exp_conj_sub_eq_integral (A B : 𝔸) (τ : ℝ) :
    exp (τ • B) * A * exp ((-τ) • B) - A =
      ∫ s in (0 : ℝ)..τ, exp (s • B) * (B * A - A * B) * exp ((-s) • B) := by
  have hderiv : ∀ u ∈ Set.uIcc 0 τ,
      HasDerivAt (fun u => exp (u • B) * A * exp ((-u) • B))
        (exp (u • B) * (B * A - A * B) * exp ((-u) • B)) u :=
    fun u _ => hasDerivAt_exp_conj A B u
  have hint : IntervalIntegrable
      (fun s => exp (s • B) * (B * A - A * B) * exp ((-s) • B)) volume 0 τ :=
    (continuous_exp_conj_deriv A B).intervalIntegrable 0 τ
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [zero_smul, exp_zero, one_mul, neg_zero, mul_one] at hftc
  exact hftc.symm

/-- Integral representation of the Lie-Trotter error:
  `exp(tB) * exp(tA) - exp(t(A+B)) = ∫₀ᵗ exp((t-τ)(A+B)) * [exp(τB), A] * exp(τA) dτ`. -/
theorem lie_trotter_integral_error (A B : 𝔸) (t : ℝ) :
    exp (t • B) * exp (t • A) - exp (t • (A + B)) =
      ∫ τ in (0 : ℝ)..t, exp ((t - τ) • (A + B)) *
        ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Apply FTC-2 to w(τ) = exp(-τ(A+B)) * exp(τB) * exp(τA)
  have hderiv : ∀ u ∈ Set.uIcc 0 t,
      HasDerivAt (fun u => exp ((-u) • (A + B)) * (exp (u • B) * exp (u • A)))
        (exp ((-u) • (A + B)) * ((exp (u • B) * A - A * exp (u • B)) * exp (u • A))) u :=
    fun u _ => hasDerivAt_conj_trotter A B u
  have hint : IntervalIntegrable
      (fun τ => exp ((-τ) • (A + B)) *
        ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))) volume 0 t :=
    (continuous_conj_trotter_deriv A B).intervalIntegrable 0 t
  have hftc := integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [zero_smul, neg_zero, exp_zero, one_mul] at hftc
  -- hftc: ∫ w'(τ) dτ = exp(-t(A+B))·exp(tB)·exp(tA) - 1
  -- Goal: exp(tB)·exp(tA) - exp(t(A+B)) = ∫ exp((t-τ)(A+B)) · (...) dτ
  -- Left-multiply hftc by exp(t(A+B)):
  have hmul : exp (t • (A + B)) *
      (∫ τ in (0 : ℝ)..t, exp ((-τ) • (A + B)) *
        ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))) =
      exp (t • (A + B)) * (exp ((-t) • (A + B)) * (exp (t • B) * exp (t • A)) - 1) := by
    rw [hftc]
  -- Simplify LHS: exp(t(A+B))·exp(-t(A+B))·... = ... and exp(t(A+B))·1 = exp(t(A+B))
  rw [mul_sub, mul_one] at hmul
  have hcancel : exp (t • (A + B)) * (exp ((-t) • (A + B)) * (exp (t • B) * exp (t • A))) =
      exp (t • B) * exp (t • A) := by
    rw [← mul_assoc, exp_smul_mul_exp_neg_smul (A + B) t, one_mul]
  rw [hcancel] at hmul
  -- Step 1: rewrite ∫ exp((t-τ)(A+B)) * f = ∫ exp(t(A+B)) * exp(-τ(A+B)) * f
  -- by showing integrands are pointwise equal
  have hfold : ∀ τ : ℝ,
      exp ((t - τ) • (A + B)) * ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A)) =
      exp (t • (A + B)) * (exp ((-τ) • (A + B)) *
        ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))) := by
    intro τ
    have hsplit : (t - τ) • (A + B) = t • (A + B) + (-τ) • (A + B) := by
      rw [sub_smul, sub_eq_add_neg, neg_smul]
    rw [hsplit, exp_add_of_commute (commute_smul_self (A + B) t (-τ)), mul_assoc]
  simp_rw [hfold]
  -- Step 2: pull exp(t(A+B)) out via ContinuousLinearMap
  set L := ContinuousLinearMap.mul ℝ 𝔸 (exp (t • (A + B))) with hL_def
  have hL : ∀ x : 𝔸, L x = exp (t • (A + B)) * x := fun x => by
    simp [hL_def, ContinuousLinearMap.mul_apply']
  simp_rw [← hL]
  rw [L.intervalIntegral_comp_comm hint]
  simp only [hL]
  exact hmul.symm

/-!
## Layer 4: Commutator-scaling norm bounds

Bound the commutator `[exp(τB), A]` in terms of `‖[B,A]‖ = ‖B*A - A*B‖`,
then substitute into the integral representation to get the main result.
-/

/-- `‖exp(τB) * A * exp(-τB) - A‖ ≤ ‖B*A - A*B‖ * |τ| * exp(2|τ|‖B‖)`.

Proof: from `exp_conj_sub_eq_integral`, the LHS = ‖∫₀ᵗ exp(sB)·[B,A]·exp(-sB) ds‖.
Bound the integrand norm by ‖[B,A]‖·exp(2|τ|·‖B‖) (constant in s), then
`norm_integral_le_of_norm_le_const` gives the result. -/
theorem norm_exp_conj_sub_le (A B : 𝔸) (τ : ℝ) :
    ‖exp (τ • B) * A * exp ((-τ) • B) - A‖ ≤
      ‖B * A - A * B‖ * |τ| * Real.exp (2 * |τ| * ‖B‖) := by
  rw [exp_conj_sub_eq_integral]
  -- Use norm_integral_le_of_norm_le_const: bound integrand by a constant
  have hconst : ∀ s ∈ Set.uIoc 0 τ,
      ‖exp (s • B) * (B * A - A * B) * exp ((-s) • B)‖ ≤
        ‖B * A - A * B‖ * Real.exp (2 * |τ| * ‖B‖) := by
    intro s hs
    -- |s| ≤ |τ| for s ∈ uIoc 0 τ
    have habs : |s| ≤ |τ| := by
      rw [Set.mem_uIoc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos h1, abs_of_pos (lt_of_lt_of_le h1 h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_neg (lt_of_lt_of_le h1 h2)]; linarith
    -- ‖exp(s•B)‖ ≤ exp(|τ|‖B‖)
    have hexp1 : ‖exp (s • B)‖ ≤ Real.exp (|τ| * ‖B‖) := by
      exact (norm_exp_le (𝕂 := ℝ) _).trans (Real.exp_le_exp_of_le (by
        calc ‖s • B‖ ≤ ‖s‖ * ‖B‖ := norm_smul_le s B
          _ = |s| * ‖B‖ := by rw [Real.norm_eq_abs]
          _ ≤ |τ| * ‖B‖ := by nlinarith [norm_nonneg B]))
    have hexp2 : ‖exp ((-s) • B)‖ ≤ Real.exp (|τ| * ‖B‖) := by
      exact (norm_exp_le (𝕂 := ℝ) _).trans (Real.exp_le_exp_of_le (by
        calc ‖(-s) • B‖ ≤ ‖(-s : ℝ)‖ * ‖B‖ := norm_smul_le (-s) B
          _ = |s| * ‖B‖ := by rw [Real.norm_eq_abs, abs_neg]
          _ ≤ |τ| * ‖B‖ := by nlinarith [norm_nonneg B]))
    calc ‖exp (s • B) * (B * A - A * B) * exp ((-s) • B)‖
        ≤ ‖exp (s • B)‖ * ‖B * A - A * B‖ * ‖exp ((-s) • B)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (|τ| * ‖B‖) * ‖B * A - A * B‖ * Real.exp (|τ| * ‖B‖) := by
          gcongr
      _ = ‖B * A - A * B‖ * Real.exp (2 * |τ| * ‖B‖) := by
          rw [show Real.exp (|τ| * ‖B‖) * ‖B * A - A * B‖ * Real.exp (|τ| * ‖B‖) =
            ‖B * A - A * B‖ * (Real.exp (|τ| * ‖B‖) * Real.exp (|τ| * ‖B‖)) from by ring,
            ← Real.exp_add]; ring_nf
  calc ‖∫ s in (0 : ℝ)..τ, exp (s • B) * (B * A - A * B) * exp ((-s) • B)‖
      ≤ (‖B * A - A * B‖ * Real.exp (2 * |τ| * ‖B‖)) * |τ - 0| :=
        norm_integral_le_of_norm_le_const hconst
    _ = ‖B * A - A * B‖ * |τ| * Real.exp (2 * |τ| * ‖B‖) := by ring_nf

/-- `‖exp(τB) * A - A * exp(τB)‖ ≤ ‖B*A - A*B‖ * |τ| * exp(3|τ|‖B‖)`.

Proof: factor as `(exp(τB)·A·exp(-τB) - A) · exp(τB)`, apply `norm_mul_le`,
then use `norm_exp_conj_sub_le` and `norm_exp_le`. -/
theorem norm_comm_exp_le (A B : 𝔸) (τ : ℝ) :
    ‖exp (τ • B) * A - A * exp (τ • B)‖ ≤
      ‖B * A - A * B‖ * |τ| * Real.exp (3 * |τ| * ‖B‖) := by
  -- Factor: [exp(τB), A] = (exp(τB)·A·exp(-τB) - A) · exp(τB)
  have hfactor : exp (τ • B) * A - A * exp (τ • B) =
      (exp (τ • B) * A * exp ((-τ) • B) - A) * exp (τ • B) := by
    rw [sub_mul, mul_assoc, mul_assoc, exp_neg_smul_mul_exp_smul B τ, mul_one]
  rw [hfactor]
  -- Bound ‖exp(τB)‖ ≤ exp(|τ|·‖B‖)
  have hexp : ‖exp (τ • B)‖ ≤ Real.exp (|τ| * ‖B‖) :=
    (norm_exp_le (𝕂 := ℝ) _).trans (Real.exp_le_exp_of_le (by
      calc ‖τ • B‖ ≤ ‖τ‖ * ‖B‖ := norm_smul_le τ B
        _ = |τ| * ‖B‖ := by rw [Real.norm_eq_abs]))
  calc ‖(exp (τ • B) * A * exp ((-τ) • B) - A) * exp (τ • B)‖
      ≤ ‖exp (τ • B) * A * exp ((-τ) • B) - A‖ * ‖exp (τ • B)‖ := norm_mul_le _ _
    _ ≤ (‖B * A - A * B‖ * |τ| * Real.exp (2 * |τ| * ‖B‖)) *
          Real.exp (|τ| * ‖B‖) := by gcongr; exact norm_exp_conj_sub_le A B τ
    _ = ‖B * A - A * B‖ * |τ| * Real.exp (3 * |τ| * ‖B‖) := by
        rw [show ‖B * A - A * B‖ * |τ| * Real.exp (2 * |τ| * ‖B‖) * Real.exp (|τ| * ‖B‖) =
          ‖B * A - A * B‖ * |τ| * (Real.exp (2 * |τ| * ‖B‖) * Real.exp (|τ| * ‖B‖)) from
            by ring, ← Real.exp_add]; ring_nf

/-- **Tight commutator-scaling Trotter error bound:**
  `‖exp(tB) * exp(tA) - exp(t(A+B))‖ ≤ ‖[B,A]‖/2 * t² * exp(t(‖A‖+3‖B‖))`.

  This improves the quadratic bound `2‖a‖‖b‖` from `norm_exp_mul_exp_sub_exp_add'`
  to the commutator norm `‖B*A - A*B‖`, which can be much smaller when A and B
  nearly commute.

  Matches the tight bound from Childs et al. (2021), Proposition in §VII.A. -/
theorem norm_lie_trotter_comm_scaling (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • B) * exp (t • A) - exp (t • (A + B))‖ ≤
      ‖B * A - A * B‖ / 2 * t ^ 2 * Real.exp (t * (‖A‖ + 3 * ‖B‖)) := by
  rw [lie_trotter_integral_error]
  -- Bound ‖integrand(τ)‖ ≤ C * τ (keeping τ-dependence for the tight 1/2 factor)
  set C := ‖B * A - A * B‖ * Real.exp (t * (‖A‖ + 3 * ‖B‖)) with hC_def
  have hτbound : ∀ τ ∈ Set.Ioc 0 t,
      ‖exp ((t - τ) • (A + B)) * ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))‖ ≤
        C * τ := by
    intro τ hτ
    have hτ_pos : 0 < τ := hτ.1
    have hτ_le : τ ≤ t := hτ.2
    -- Individual norm bounds
    have h1 : ‖exp ((t - τ) • (A + B))‖ ≤ Real.exp ((t - τ) * (‖A‖ + ‖B‖)) := by
      refine (norm_exp_le (𝕂 := ℝ) _).trans (Real.exp_le_exp_of_le ?_)
      have := norm_smul_le (t - τ) (A + B)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
      exact this.trans (mul_le_mul_of_nonneg_left (norm_add_le A B) (by linarith))
    have h2 : ‖(exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A)‖ ≤
        (‖B * A - A * B‖ * τ * Real.exp (3 * τ * ‖B‖)) * Real.exp (τ * ‖A‖) := by
      calc ‖(exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A)‖
          ≤ ‖exp (τ • B) * A - A * exp (τ • B)‖ * ‖exp (τ • A)‖ := norm_mul_le _ _
        _ ≤ (‖B * A - A * B‖ * |τ| * Real.exp (3 * |τ| * ‖B‖)) *
              Real.exp (|τ| * ‖A‖) := by
            gcongr
            · exact norm_comm_exp_le A B τ
            · exact (norm_exp_le (𝕂 := ℝ) _).trans (Real.exp_le_exp_of_le (by
                calc ‖τ • A‖ ≤ ‖τ‖ * ‖A‖ := norm_smul_le τ A
                  _ = |τ| * ‖A‖ := by rw [Real.norm_eq_abs]))
        _ = _ := by rw [abs_of_pos hτ_pos]
    -- Combine: ‖integrand‖ ≤ exp((t-τ)(‖A‖+‖B‖)) * ‖BA-AB‖ * τ * exp(3τ‖B‖) * exp(τ‖A‖)
    --                       ≤ ‖BA-AB‖ * τ * exp(t(‖A‖+3‖B‖))   [combine exponents, τ ≤ t]
    --                       = C * τ
    calc ‖exp ((t - τ) • (A + B)) * ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))‖
        ≤ ‖exp ((t - τ) • (A + B))‖ *
            ‖(exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A)‖ := norm_mul_le _ _
      _ ≤ Real.exp ((t - τ) * (‖A‖ + ‖B‖)) *
            ((‖B * A - A * B‖ * τ * Real.exp (3 * τ * ‖B‖)) * Real.exp (τ * ‖A‖)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)
      _ = ‖B * A - A * B‖ * τ *
            (Real.exp ((t - τ) * (‖A‖ + ‖B‖)) * Real.exp (3 * τ * ‖B‖) * Real.exp (τ * ‖A‖)) :=
          by ring
      _ ≤ ‖B * A - A * B‖ * τ * Real.exp (t * (‖A‖ + 3 * ‖B‖)) := by
          gcongr
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp_of_le (by nlinarith [norm_nonneg B])
      _ = C * τ := by rw [hC_def]; ring
  -- Apply non-constant norm bound: ‖∫ f‖ ≤ ∫ g when ‖f‖ ≤ g pointwise
  have hg_int : IntervalIntegrable (fun τ => C * τ) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  calc ‖∫ τ in (0 : ℝ)..t, exp ((t - τ) • (A + B)) *
        ((exp (τ • B) * A - A * exp (τ • B)) * exp (τ • A))‖
      ≤ ∫ τ in (0 : ℝ)..t, C * τ :=
        norm_integral_le_of_norm_le ht
          (Filter.Eventually.of_forall (fun _ h => hτbound _ h)) hg_int
    _ = C * (t ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        -- ∫₀ᵗ τ dτ = t²/2 via FTC-2 on f(x) = x²/2
        have hderiv : ∀ x ∈ Set.uIcc 0 t,
            HasDerivAt (fun x => x ^ 2 / 2) x x := by
          intro x _
          have h := (hasDerivAt_pow 2 x).div_const 2
          simp only [Nat.cast_ofNat] at h
          convert h using 1; ring
        rw [integral_eq_sub_of_hasDerivAt hderiv (continuous_id.intervalIntegrable 0 t)]
        simp
    _ = ‖B * A - A * B‖ / 2 * t ^ 2 * Real.exp (t * (‖A‖ + 3 * ‖B‖)) := by
        rw [hC_def]; ring

end
