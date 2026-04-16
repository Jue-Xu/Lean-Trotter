/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Higher-Order Commutator Extraction via Iterated FTC

Generalizes the double-FTC pattern from `StrangCommutatorScaling.lean` to extract
triple commutators from the conjugation `exp(τB) · A · exp(-τB)`.

## Key results

- `exp_conj_sub_comm2_eq_triple_integral`: triple FTC extracting [B,[B,[B,A]]]
- `norm_exp_conj_sub_comm2_le`: norm bound ≤ ‖[B,[B,[B,A]]]‖/6 · τ³ · exp(2τ‖B‖)
- `norm_exp_conj_sub_comm2_le_of_skewAdjoint`: anti-Hermitian version ≤ ‖[B,[B,[B,A]]]‖/6 · τ³
-/

import LieTrotter.StrangCommutatorScaling

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Triple conjugation FTC

Strategy: Start from the double FTC result, which gives the double integral.
Subtract the constant term `(τ²/2)·c₂` by rewriting through the integral,
then apply `exp_conj_sub_eq_integral` to each inner integrand.
-/

/-- Triple conjugation FTC: the remainder after subtracting two commutator terms
  equals a triple integral of `[B,[B,[B,A]]]`-conjugated terms. -/
theorem exp_conj_sub_comm2_eq_triple_integral (A B : 𝔸) (τ : ℝ) :
    exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • (B * A - A * B) - (τ ^ 2 / 2) • (B * (B * A - A * B) - (B * A - A * B) * B) =
    ∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
      exp (v • B) * (B * (B * (B * A - A * B) - (B * A - A * B) * B) -
        (B * (B * A - A * B) - (B * A - A * B) * B) * B) * exp ((-v) • B) := by
  set c₁ : 𝔸 := B * A - A * B
  set c₂ : 𝔸 := B * c₁ - c₁ * B
  -- From double FTC: LHS_2 = ∫∫ exp(uB)·c₂·exp(-uB) du ds
  have hdbl := exp_conj_sub_comm_eq_double_integral A B τ
  -- hdbl: exp(τB)Aexp(-τB) - A - τ·c₁ = ∫₀ᵗ∫₀ˢ exp(uB)·c₂·exp(-uB) du ds
  -- Goal: hdbl - (τ²/2)·c₂ = ∫₀ᵗ∫₀ˢ∫₀ᵘ exp(vB)·c₃·exp(-vB) dv du ds
  -- Strategy: show ∫₀ᵗ∫₀ˢ (exp(uB)·c₂·exp(-uB) - c₂) du ds = triple_integral
  -- and show ∫₀ᵗ∫₀ˢ c₂ du ds = (τ²/2)·c₂
  -- Step 1: ∫₀ˢ c₂ du = s • c₂
  have hinner_const : ∀ s : ℝ, ∫ _ in (0:ℝ)..s, c₂ = s • c₂ := by
    intro s; rw [intervalIntegral.integral_const]; simp
  -- Step 2: ∫₀ᵗ s • c₂ ds = (τ²/2) • c₂
  have houter_const : ∫ s in (0:ℝ)..τ, s • c₂ = (τ ^ 2 / 2) • c₂ := by
    rw [intervalIntegral.integral_smul_const]; congr 1
    have hd : ∀ x ∈ Set.uIcc 0 τ, HasDerivAt (fun x => x ^ 2 / 2) x x := by
      intro x _; have h := (hasDerivAt_pow 2 x).div_const 2
      simp only [Nat.cast_ofNat] at h; convert h using 1; ring
    rw [integral_eq_sub_of_hasDerivAt hd (continuous_id.intervalIntegrable 0 τ)]; simp
  -- Step 3: ∫₀ᵗ∫₀ˢ c₂ du ds = (τ²/2) • c₂
  have hdbl_const : ∫ s in (0:ℝ)..τ, ∫ _ in (0:ℝ)..s, c₂ = (τ ^ 2 / 2) • c₂ := by
    simp_rw [hinner_const]; exact houter_const
  -- Step 4: Integrability of f(u) = exp(uB)·c₂·exp(-uB)
  set f : ℝ → 𝔸 := fun u => exp (u • B) * c₂ * exp ((-u) • B)
  have hf_cont : Continuous f := by
    letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
    exact (exp_continuous.comp (continuous_id.smul continuous_const) |>.mul
      continuous_const).mul
      (exp_continuous.comp (continuous_neg.smul continuous_const))
  have hf_int : ∀ s : ℝ, IntervalIntegrable f volume 0 s :=
    fun s => hf_cont.intervalIntegrable 0 s
  have hc_int : ∀ s : ℝ, IntervalIntegrable (fun _ => c₂) volume 0 s :=
    fun s => continuous_const.intervalIntegrable 0 s
  -- Step 5: Compute the difference
  -- LHS = (∫∫ f) - (τ²/2)·c₂ = (∫∫ f) - (∫∫ c₂) = ∫∫ (f - c₂)
  have hgoal : exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • c₁ - (τ ^ 2 / 2) • c₂ =
    ∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, (f u - c₂) := by
    have hsub : ∀ s : ℝ, ∫ u in (0:ℝ)..s, (f u - c₂) =
        (∫ u in (0:ℝ)..s, f u) - ∫ u in (0:ℝ)..s, c₂ :=
      fun s => integral_sub (hf_int s) (hc_int s)
    -- ∫₀ᵗ ∫₀ˢ (f-c₂) du ds = ∫₀ᵗ (∫₀ˢ f du - ∫₀ˢ c₂ du) ds
    --                        = ∫₀ᵗ (∫₀ˢ f du - s•c₂) ds
    --                        = ∫₀ᵗ ∫₀ˢ f du ds - ∫₀ᵗ s•c₂ ds
    --                        = (∫∫ f) - (τ²/2)•c₂
    -- But easier: from hdbl we have LHS + (τ²/2)·c₂ = ∫∫ f
    -- So LHS = ∫∫ f - (τ²/2)·c₂ = ∫∫ f - ∫∫ c₂ = ∫∫(f-c₂)
    -- We need integral_sub for the outer integral
    have h_outer_f : IntervalIntegrable (fun s => ∫ u in (0:ℝ)..s, f u) volume 0 τ := by
      apply Continuous.intervalIntegrable
      exact continuous_primitive hf_cont.intervalIntegrable 0
    have h_outer_c : IntervalIntegrable (fun s => ∫ u in (0:ℝ)..s, c₂) volume 0 τ := by
      apply Continuous.intervalIntegrable
      exact continuous_primitive (continuous_const.intervalIntegrable) 0
    calc exp (τ • B) * A * exp ((-τ) • B) - A - τ • c₁ - (τ ^ 2 / 2) • c₂
        = (exp (τ • B) * A * exp ((-τ) • B) - A - τ • c₁) - (τ ^ 2 / 2) • c₂ := by
          abel
      _ = (∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, f u) - (τ ^ 2 / 2) • c₂ := by
          rw [hdbl]
      _ = (∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, f u) -
          (∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, c₂) := by
          rw [hdbl_const]
      _ = ∫ s in (0:ℝ)..τ, ((∫ u in (0:ℝ)..s, f u) - (∫ u in (0:ℝ)..s, c₂)) := by
          rw [integral_sub h_outer_f h_outer_c]
      _ = ∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, (f u - c₂) := by
          congr 1; ext s; rw [← integral_sub (hf_int s) (hc_int s)]
  rw [hgoal]
  -- Step 6: f(u) - c₂ = exp(uB)·c₂·exp(-uB) - c₂ = ∫₀ᵘ exp(vB)·c₃·exp(-vB) dv
  congr 1; ext s; congr 1; ext u
  exact exp_conj_sub_eq_integral c₂ B u

/-!
## Norm bounds for triple commutator remainder
-/

/-- Triple commutator norm bound (general algebras):
  `‖exp(τB)·A·exp(-τB) - A - τ[B,A] - τ²/2·[B,[B,A]]‖ ≤ ‖[B,[B,[B,A]]]‖/6 · τ³ · exp(2τ‖B‖)` -/
theorem norm_exp_conj_sub_comm2_le (A B : 𝔸) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • (B * A - A * B) - (τ ^ 2 / 2) • (B * (B * A - A * B) - (B * A - A * B) * B)‖ ≤
      ‖B * (B * (B * A - A * B) - (B * A - A * B) * B) -
        (B * (B * A - A * B) - (B * A - A * B) * B) * B‖ / 6 *
        τ ^ 3 * Real.exp (2 * τ * ‖B‖) := by
  rw [exp_conj_sub_comm2_eq_triple_integral]
  set C := B * (B * (B * A - A * B) - (B * A - A * B) * B) -
    (B * (B * A - A * B) - (B * A - A * B) * B) * B
  set K := ‖C‖ * Real.exp (2 * τ * ‖B‖)
  -- Inner integral: ‖∫₀ᵘ exp(vB)·C·exp(-vB) dv‖ ≤ K·u
  have hinner : ∀ u ∈ Set.Ioc 0 τ,
      ‖∫ v in (0:ℝ)..u, exp (v • B) * C * exp ((-v) • B)‖ ≤ K * u := by
    intro u hu
    have h := norm_exp_conj_sub_le (B * (B * A - A * B) - (B * A - A * B) * B) B u
    calc ‖∫ v in (0:ℝ)..u, exp (v • B) * C * exp ((-v) • B)‖
        = ‖exp (u • B) * (B * (B * A - A * B) - (B * A - A * B) * B) *
            exp ((-u) • B) - (B * (B * A - A * B) - (B * A - A * B) * B)‖ := by
          congr 1; exact (exp_conj_sub_eq_integral _ B u).symm
      _ ≤ ‖C‖ * |u| * Real.exp (2 * |u| * ‖B‖) := h
      _ = ‖C‖ * u * Real.exp (2 * u * ‖B‖) := by rw [abs_of_pos hu.1]
      _ ≤ ‖C‖ * u * Real.exp (2 * τ * ‖B‖) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (le_of_lt hu.1))
          exact Real.exp_le_exp_of_le (by nlinarith [hu.2, norm_nonneg B])
      _ = K * u := by ring
  -- Middle integral: ‖∫₀ˢ inner du‖ ≤ K·s²/2
  have hmid : ∀ s ∈ Set.Ioc 0 τ,
      ‖∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
        exp (v • B) * C * exp ((-v) • B)‖ ≤ K * (s ^ 2 / 2) := by
    intro s hs
    calc ‖∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
          exp (v • B) * C * exp ((-v) • B)‖
        ≤ ∫ u in (0:ℝ)..s, K * u := by
          apply norm_integral_le_of_norm_le (le_of_lt hs.1) _ _
          · exact Filter.Eventually.of_forall (fun u hu =>
              hinner u ⟨hu.1, le_trans hu.2 hs.2⟩)
          · exact (continuous_const.mul continuous_id).intervalIntegrable 0 s
      _ = K * (s ^ 2 / 2) := by
          rw [intervalIntegral.integral_const_mul]; congr 1
          have : ∀ x ∈ Set.uIcc 0 s, HasDerivAt (fun x => x ^ 2 / 2) x x := by
            intro x _; have h := (hasDerivAt_pow 2 x).div_const 2
            simp only [Nat.cast_ofNat] at h; convert h using 1; ring
          rw [integral_eq_sub_of_hasDerivAt this (continuous_id.intervalIntegrable 0 s)]
          simp
  -- Outer integral: ‖∫₀ᵗ mid ds‖ ≤ K·τ³/6
  calc ‖∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
        exp (v • B) * C * exp ((-v) • B)‖
      ≤ ∫ s in (0:ℝ)..τ, K * (s ^ 2 / 2) := by
        apply norm_integral_le_of_norm_le hτ _ _
        · exact Filter.Eventually.of_forall (fun s hs => hmid s hs)
        · exact (continuous_const.mul ((continuous_id.pow 2).div_const 2)).intervalIntegrable 0 τ
    _ = K * (τ ^ 3 / 6) := by
        rw [intervalIntegral.integral_const_mul]; congr 1
        have hd : ∀ x ∈ Set.uIcc 0 τ,
            HasDerivAt (fun x => x ^ 3 / 6) (x ^ 2 / 2) x := by
          intro x _; have h := (hasDerivAt_pow 3 x).div_const 6
          simp only [Nat.cast_ofNat] at h; convert h using 1; ring
        rw [integral_eq_sub_of_hasDerivAt hd
          ((continuous_id.pow 2 |>.div_const 2).intervalIntegrable 0 τ)]
        simp
    _ = ‖C‖ / 6 * τ ^ 3 * Real.exp (2 * τ * ‖B‖) := by simp only [K]; ring

/-- Triple commutator bound for anti-Hermitian operators (‖exp(sB)‖ = 1):
  `‖exp(τB)·A·exp(-τB) - A - τ[B,A] - τ²/2·[B,[B,A]]‖ ≤ ‖[B,[B,[B,A]]]‖/6 · τ³` -/
theorem norm_exp_conj_sub_comm2_le_of_skewAdjoint
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) (hB : star B = -B) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • (B * A - A * B) - (τ ^ 2 / 2) • (B * (B * A - A * B) - (B * A - A * B) * B)‖ ≤
      ‖B * (B * (B * A - A * B) - (B * A - A * B) * B) -
        (B * (B * A - A * B) - (B * A - A * B) * B) * B‖ / 6 * τ ^ 3 := by
  rw [exp_conj_sub_comm2_eq_triple_integral]
  set C := B * (B * (B * A - A * B) - (B * A - A * B) * B) -
    (B * (B * A - A * B) - (B * A - A * B) * B) * B
  -- Anti-Hermitian isometry
  have hiso : ∀ (X : 𝔸) (s : ℝ), ‖exp (s • B) * X * exp ((-s) • B)‖ ≤ ‖X‖ := by
    intro X s
    calc ‖exp (s • B) * X * exp ((-s) • B)‖
        ≤ ‖exp (s • B)‖ * ‖X‖ * ‖exp ((-s) • B)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖X‖ := by
          rw [norm_exp_smul_of_skewAdjoint hB s, norm_exp_smul_of_skewAdjoint hB (-s)]; ring
  -- Inner: ‖∫₀ᵘ g dv‖ ≤ ‖C‖·u
  have hinner : ∀ u ∈ Set.Ioc 0 τ,
      ‖∫ v in (0:ℝ)..u, exp (v • B) * C * exp ((-v) • B)‖ ≤ ‖C‖ * u := by
    intro u hu
    calc ‖∫ v in (0:ℝ)..u, exp (v • B) * C * exp ((-v) • B)‖
        ≤ ‖C‖ * |u - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun v _ => hiso C v)
      _ = ‖C‖ * u := by rw [sub_zero, abs_of_pos hu.1]
  -- Middle: ‖∫₀ˢ inner du‖ ≤ ‖C‖·s²/2
  have hmid : ∀ s ∈ Set.Ioc 0 τ,
      ‖∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
        exp (v • B) * C * exp ((-v) • B)‖ ≤ ‖C‖ * (s ^ 2 / 2) := by
    intro s hs
    calc ‖∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
          exp (v • B) * C * exp ((-v) • B)‖
        ≤ ∫ u in (0:ℝ)..s, ‖C‖ * u := by
          apply norm_integral_le_of_norm_le (le_of_lt hs.1) _ _
          · exact Filter.Eventually.of_forall (fun u hu =>
              hinner u ⟨hu.1, le_trans hu.2 hs.2⟩)
          · exact (continuous_const.mul continuous_id).intervalIntegrable 0 s
      _ = ‖C‖ * (s ^ 2 / 2) := by
          rw [intervalIntegral.integral_const_mul]; congr 1
          have : ∀ x ∈ Set.uIcc 0 s, HasDerivAt (fun x => x ^ 2 / 2) x x := by
            intro x _; have h := (hasDerivAt_pow 2 x).div_const 2
            simp only [Nat.cast_ofNat] at h; convert h using 1; ring
          rw [integral_eq_sub_of_hasDerivAt this (continuous_id.intervalIntegrable 0 s)]
          simp
  -- Outer: ‖∫₀ᵗ mid ds‖ ≤ ‖C‖·τ³/6
  calc ‖∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s, ∫ v in (0:ℝ)..u,
        exp (v • B) * C * exp ((-v) • B)‖
      ≤ ∫ s in (0:ℝ)..τ, ‖C‖ * (s ^ 2 / 2) := by
        apply norm_integral_le_of_norm_le hτ _ _
        · exact Filter.Eventually.of_forall (fun s hs => hmid s hs)
        · exact (continuous_const.mul ((continuous_id.pow 2).div_const 2)).intervalIntegrable 0 τ
    _ = ‖C‖ * (τ ^ 3 / 6) := by
        rw [intervalIntegral.integral_const_mul]; congr 1
        have hd : ∀ x ∈ Set.uIcc 0 τ,
            HasDerivAt (fun x => x ^ 3 / 6) (x ^ 2 / 2) x := by
          intro x _; have h := (hasDerivAt_pow 3 x).div_const 6
          simp only [Nat.cast_ofNat] at h; convert h using 1; ring
        rw [integral_eq_sub_of_hasDerivAt hd
          ((continuous_id.pow 2 |>.div_const 2).intervalIntegrable 0 τ)]
        simp
    _ = ‖C‖ / 6 * τ ^ 3 := by ring
