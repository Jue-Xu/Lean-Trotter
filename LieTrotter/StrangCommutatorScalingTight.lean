/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tighter Strang Commutator-Scaling via Norm-of-Difference

Proves a tighter Strang bound by extracting the leading-order effective
double commutator D = [B,[B,A']] - [A',[A',B]] before taking norms,
using the triple FTC (HigherCommutator.lean) for the remainder.

  Standard:  ‖S₂(t) - exp(tH)‖ ≤ (‖[B,[B,A']]‖ + ‖[A',[A',B]]‖)/6 · t³
  Tighter:   ‖S₂(t) - exp(tH)‖ ≤ ‖[B,[B,A']] - [A',[A',B]]‖/6 · t³ + T/4 · t⁴

The leading term is always ≤ the standard bound (triangle inequality), and
strictly tighter when the two double commutators partially cancel.
-/

import LieTrotter.HigherCommutator

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Refined pointwise bound on the Strang residual

We refine the decomposition 𝒯₂(τ) = PartA(τ) + PartB(τ):
  PartA(τ) = -τ²/2·[A',[A',B]] + R_A(τ)     (from subtract-constant + triple FTC)
  PartB(τ) = +τ²/2·[B,[B,A']] + R_B(τ)       (from double FTC + conjugation correction)
Combining: 𝒯₂(τ) = τ²/2·D + R(τ) where ‖R(τ)‖ ≤ T·τ³.
-/

/-- Refined bound on `Part_A(τ) + τ²/2·[A',[A',B]]`:
  this residual is bounded by a triple commutator norm.
  Part_A is the "subtract-constant-at-τ" integral from the Strang proof. -/
private lemma norm_partA_sub_leading
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (B : 𝔸) (A' : 𝔸) (hA' : star A' = -A') {τ : ℝ} (hτ : 0 ≤ τ) :
    let c := A' * B - B * A'
    let g₁ := fun s : ℝ => exp (s • A') * c * exp ((-s) • A')
    let dblA := A' * c - c * A'  -- [A',[A',B]]
    ‖(∫ s in (0:ℝ)..τ, (g₁ s - g₁ τ)) + (τ ^ 2 / 2) • dblA‖ ≤
      ‖A' * dblA - dblA * A'‖ / 3 * τ ^ 3 := by
  intro c g₁ dblA
  set triA := A' * dblA - dblA * A'
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hn : ∀ s : ℝ, ‖exp (s • A')‖ = 1 := norm_exp_smul_of_skewAdjoint hA'
  -- Strategy: LHS = ∫₀ᵗ (φ(s) - φ(τ)) ds where φ(s) = g₁(s) - c - s·dblA
  -- Then ‖φ(s) - φ(τ)‖ ≤ ‖triA‖·(τ²-s²)/2 and integrate to ‖triA‖/3·τ³
  set φ : ℝ → 𝔸 := fun s => g₁ s - c - s • dblA
  -- Step 1: LHS = ∫₀ᵗ (φ(s) - φ(τ)) ds
  have hLHS_eq : (∫ s in (0:ℝ)..τ, (g₁ s - g₁ τ)) + (τ ^ 2 / 2) • dblA =
      ∫ s in (0:ℝ)..τ, (φ s - φ τ) := by
    -- φ(s) - φ(τ) = g₁(s) - g₁(τ) + (τ-s)·dblA
    have hpw : ∀ s : ℝ, φ s - φ τ = (g₁ s - g₁ τ) + (τ - s) • dblA := by
      intro s; simp only [φ, sub_smul]; abel
    simp_rw [hpw]
    have hg_int : IntervalIntegrable (fun s => g₁ s - g₁ τ) volume 0 τ :=
      ((((exp_continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const).mul
        (exp_continuous.comp (continuous_neg.smul continuous_const))).sub
        continuous_const).intervalIntegrable 0 τ
    have hsmul_int : IntervalIntegrable (fun s => (τ - s) • dblA) volume 0 τ :=
      ((continuous_const.sub continuous_id).smul continuous_const).intervalIntegrable 0 τ
    rw [integral_add hg_int hsmul_int, intervalIntegral.integral_smul_const]
    congr 1
    -- ∫₀ᵗ (τ-s) ds = τ²/2
    have hd : ∀ x ∈ Set.uIcc 0 τ,
        HasDerivAt (fun x => τ * x - x ^ 2 / 2) (τ - x) x := by
      intro x _
      have h1 := hasDerivAt_const x τ |>.mul (hasDerivAt_id x)
      have h2 := (hasDerivAt_pow 2 x).div_const 2
      simp only [Nat.cast_ofNat] at h2
      convert h1.sub h2 using 1; ring
    rw [integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.sub continuous_id).intervalIntegrable 0 τ)]
    simp; ring
  rw [hLHS_eq]
  -- Step 2: Pointwise bound
  -- φ(τ) - φ(s) = ∫ₛᵗ (h(u) - dblA) du where h(u) = exp(uA')·dblA·exp(-uA')
  -- ‖h(u) - dblA‖ ≤ ‖triA‖·u (anti-Hermitian)
  -- ‖φ(s) - φ(τ)‖ ≤ ∫ₛᵗ ‖triA‖·u du = ‖triA‖·(τ²-s²)/2
  have hh_bound : ∀ u : ℝ, 0 ≤ u →
      ‖exp (u • A') * dblA * exp ((-u) • A') - dblA‖ ≤ ‖triA‖ * u := by
    intro u hu
    rw [exp_conj_sub_eq_integral dblA A' u]
    calc ‖∫ v in (0:ℝ)..u, exp (v • A') * triA * exp ((-v) • A')‖
        ≤ ‖triA‖ * |u - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun v _ => by
            calc ‖exp (v • A') * triA * exp ((-v) • A')‖
                ≤ ‖exp (v • A')‖ * ‖triA‖ * ‖exp ((-v) • A')‖ :=
                  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                    (norm_mul_le _ _) (norm_nonneg _))
              _ = ‖triA‖ := by rw [hn v, hn (-v)]; ring)
      _ = ‖triA‖ * u := by rw [sub_zero, abs_of_nonneg hu]
  have hpointwise : ∀ s ∈ Set.Ioc (0:ℝ) τ,
      ‖φ s - φ τ‖ ≤ ‖triA‖ * ((τ ^ 2 - s ^ 2) / 2) := by
    intro s hs
    have hs_nn : 0 ≤ s := le_of_lt hs.1
    -- g₁(τ) - g₁(s) = ∫ₛᵗ exp(uA')·(A'c-cA')·exp(-uA') du
    have hg_diff : g₁ τ - g₁ s =
        ∫ u in s..τ, exp (u • A') * dblA * exp ((-u) • A') := by
      have h1 := exp_conj_sub_eq_integral c A' τ
      have h2 := exp_conj_sub_eq_integral c A' s
      have : g₁ τ - g₁ s = (g₁ τ - c) - (g₁ s - c) := by abel
      rw [this, h1, h2,
          ← integral_add_adjacent_intervals
            ((continuous_exp_conj_deriv c A').intervalIntegrable 0 s)
            ((continuous_exp_conj_deriv c A').intervalIntegrable s τ)]
      abel
    -- φ(τ) - φ(s) = (g₁(τ) - g₁(s)) - (τ-s)·dblA = ∫ₛᵗ (h(u)-dblA) du
    set h := fun u : ℝ => exp (u • A') * dblA * exp ((-u) • A')
    have hh_int : IntervalIntegrable h volume s τ :=
      (((exp_continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const).mul
        (exp_continuous.comp (continuous_neg.smul continuous_const))).intervalIntegrable s τ
    have hdblA_int : IntervalIntegrable (fun _ => dblA) volume s τ :=
      continuous_const.intervalIntegrable s τ
    have hφ_diff : φ τ - φ s = ∫ u in s..τ, (h u - dblA) := by
      -- Both sides equal (g₁τ-g₁s) - (τ-s)·dblA
      have hLHS : φ τ - φ s = (g₁ τ - g₁ s) - (τ - s) • dblA := by
        simp only [φ, sub_smul]; abel
      rw [hLHS, integral_sub hh_int hdblA_int, hg_diff.symm,
          intervalIntegral.integral_const]
    rw [show φ s - φ τ = -(φ τ - φ s) from by abel, norm_neg, hφ_diff]
    calc ‖∫ u in s..τ, (h u - dblA)‖
        ≤ ∫ u in s..τ, ‖triA‖ * u := by
          apply norm_integral_le_of_norm_le hs.2 _ _
          · exact Filter.Eventually.of_forall (fun u hu =>
              hh_bound u (le_trans hs_nn (le_of_lt hu.1)))
          · exact (continuous_const.mul continuous_id).intervalIntegrable s τ
      _ = ‖triA‖ * ((τ ^ 2 - s ^ 2) / 2) := by
          rw [intervalIntegral.integral_const_mul]; congr 1
          have hd : ∀ x ∈ Set.uIcc s τ, HasDerivAt (fun x => x ^ 2 / 2) x x := by
            intro x _; convert (hasDerivAt_pow 2 x).div_const 2 using 1
            simp only [Nat.cast_ofNat]; ring
          rw [integral_eq_sub_of_hasDerivAt hd (continuous_id.intervalIntegrable s τ)]
          ring
  -- Step 3: Integrate
  calc ‖∫ s in (0:ℝ)..τ, (φ s - φ τ)‖
      ≤ ∫ s in (0:ℝ)..τ, ‖triA‖ * ((τ ^ 2 - s ^ 2) / 2) := by
        apply norm_integral_le_of_norm_le hτ _ _
        · exact Filter.Eventually.of_forall (fun s hs => hpointwise s hs)
        · exact (continuous_const.mul
            ((continuous_const.sub (continuous_id.pow 2)).div_const 2)).intervalIntegrable 0 τ
    _ = ‖triA‖ * (τ ^ 3 / 3) := by
        rw [intervalIntegral.integral_const_mul]; congr 1
        have hd : ∀ x ∈ Set.uIcc 0 τ,
            HasDerivAt (fun x => (τ ^ 2 * x - x ^ 3 / 3) / 2) ((τ ^ 2 - x ^ 2) / 2) x := by
          intro x _
          have h1 : HasDerivAt (fun x => τ ^ 2 * x) (τ ^ 2) x :=
            (hasDerivAt_const x (τ ^ 2)).mul (hasDerivAt_id x) |>.congr_deriv (by ring)
          have h2 : HasDerivAt (fun x => x ^ 3 / 3) (x ^ 2) x := by
            convert (hasDerivAt_pow 3 x).div_const 3 using 1
            simp only [Nat.cast_ofNat]; ring
          exact (h1.sub h2).div_const 2
        rw [integral_eq_sub_of_hasDerivAt hd
          ((continuous_const.sub (continuous_id.pow 2)).div_const 2
            |>.intervalIntegrable 0 τ)]
        simp; ring
    _ = ‖triA‖ / 3 * τ ^ 3 := by ring

/-- Refined bound on `Part_B(τ) - τ²/2·[B,[B,A']]`:
  this residual includes the conjugation correction and the triple FTC remainder. -/
private lemma norm_partB_sub_leading
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (B : 𝔸) (A' : 𝔸) (hA' : star A' = -A') (hB : star B = -B) {τ : ℝ} (hτ : 0 ≤ τ) :
    let dblB := B * (B * A' - A' * B) - (B * A' - A' * B) * B  -- [B,[B,A']]
    ‖exp (τ • A') * (exp (τ • B) * A' * exp ((-τ) • B) - A' -
        τ • (B * A' - A' * B)) * exp ((-τ) • A') -
      (τ ^ 2 / 2) • dblB‖ ≤
      (‖A' * dblB - dblB * A'‖ / 2 +
       ‖B * dblB - dblB * B‖ / 6) * τ ^ 3 := by
  intro dblB
  have hn : ∀ (X : 𝔸), star X = -X → ∀ s : ℝ, ‖exp (s • X)‖ = 1 :=
    fun X hX s => norm_exp_smul_of_skewAdjoint hX s
  set triB := B * dblB - dblB * B
  set triAB := A' * dblB - dblB * A'
  set R₂ : 𝔸 := exp (τ • B) * A' * exp ((-τ) • B) - A' - τ • (B * A' - A' * B)
  set R_triple : 𝔸 := R₂ - (τ ^ 2 / 2) • dblB
  have hR₂_decomp : R₂ = (τ ^ 2 / 2) • dblB + R_triple := by simp only [R_triple]; abel
  have hR_triple_bound : ‖R_triple‖ ≤ ‖triB‖ / 6 * τ ^ 3 :=
    norm_exp_conj_sub_comm2_le_of_skewAdjoint A' B hB hτ
  -- Decompose: conj(R₂) - (τ²/2)·dblB = (τ²/2)·(conj(dblB)-dblB) + conj(R_triple)
  -- LHS of the goal is: exp(τA')·R₂·exp(-τA') - (τ²/2)·dblB
  -- = exp(τA')·((τ²/2)·dblB + R_triple)·exp(-τA') - (τ²/2)·dblB  [by hR₂_decomp]
  -- = (τ²/2)·(exp(τA')·dblB·exp(-τA') - dblB) + exp(τA')·R_triple·exp(-τA')
  -- Triangle inequality then gives the result.

  -- Part 1: ‖conj(dblB) - dblB‖ ≤ ‖triAB‖·τ
  have hconj_corr : ‖exp (τ • A') * dblB * exp ((-τ) • A') - dblB‖ ≤ ‖triAB‖ * τ := by
    rw [exp_conj_sub_eq_integral dblB A' τ]
    calc ‖∫ s in (0:ℝ)..τ, exp (s • A') * triAB * exp ((-s) • A')‖
        ≤ ‖triAB‖ * |τ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => by
            calc ‖exp (s • A') * triAB * exp ((-s) • A')‖
                ≤ ‖exp (s • A')‖ * ‖triAB‖ * ‖exp ((-s) • A')‖ :=
                  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                    (norm_mul_le _ _) (norm_nonneg _))
              _ = ‖triAB‖ := by rw [hn A' hA' s, hn A' hA' (-s)]; ring)
      _ = ‖triAB‖ * τ := by rw [sub_zero, abs_of_nonneg hτ]
  -- Part 2: ‖conj(R_triple)‖ ≤ ‖triB‖/6·τ³
  have hpart2 : ‖exp (τ • A') * R_triple * exp ((-τ) • A')‖ ≤ ‖triB‖ / 6 * τ ^ 3 := by
    calc ‖exp (τ • A') * R_triple * exp ((-τ) • A')‖
        ≤ ‖exp (τ • A')‖ * ‖R_triple‖ * ‖exp ((-τ) • A')‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖R_triple‖ := by rw [hn A' hA' τ, hn A' hA' (-τ)]; ring
      _ ≤ ‖triB‖ / 6 * τ ^ 3 := hR_triple_bound
  -- Combine
  -- LHS = conj(R₂) - (τ²/2)·dblB
  -- = conj((τ²/2)·dblB) + conj(R_triple) - (τ²/2)·dblB   [expanding R₂]
  -- = (τ²/2)·conj(dblB) + conj(R_triple) - (τ²/2)·dblB   [scalar through conj]
  -- = (τ²/2)·(conj(dblB)-dblB) + conj(R_triple)
  -- We bound this via triangle inequality.
  -- Rather than using `set` + `rw`, we apply norm bounds directly.
  -- The goal is: ‖exp(τA')·R₂·exp(-τA') - (τ²/2)·dblB‖ ≤ ...
  -- Decompose R₂ = (τ²/2)·dblB + R_triple, so:
  -- conj(R₂) - (τ²/2)·dblB = (τ²/2)·(conj(dblB)-dblB) + conj(R_triple)
  -- Then triangle + isometry gives the result.
  -- Key algebraic step: avoid `mul_add`/`add_mul` which cause normalization issues
  have hdecomp : exp (τ • A') * R₂ * exp ((-τ) • A') - (τ ^ 2 / 2) • dblB =
      (τ ^ 2 / 2) • (exp (τ • A') * dblB * exp ((-τ) • A') - dblB) +
      exp (τ • A') * R_triple * exp ((-τ) • A') := by
    -- exp(τA')·((τ²/2)·dblB + R_triple)·exp(-τA') - (τ²/2)·dblB
    -- = (τ²/2)·exp(τA')·dblB·exp(-τA') + exp(τA')·R_triple·exp(-τA') - (τ²/2)·dblB
    -- = (τ²/2)·(conj(dblB) - dblB) + conj(R_triple)
    have h1 : exp (τ • A') * R₂ * exp ((-τ) • A') =
        exp (τ • A') * ((τ ^ 2 / 2) • dblB) * exp ((-τ) • A') +
        exp (τ • A') * R_triple * exp ((-τ) • A') := by
      conv_lhs => rw [hR₂_decomp]
      rw [mul_add, add_mul]
    have h2 : exp (τ • A') * ((τ ^ 2 / 2) • dblB) * exp ((-τ) • A') =
        (τ ^ 2 / 2) • (exp (τ • A') * dblB * exp ((-τ) • A')) := by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [h1, h2]; module
  rw [hdecomp]
  calc ‖(τ ^ 2 / 2) • (exp (τ • A') * dblB * exp ((-τ) • A') - dblB) +
        exp (τ • A') * R_triple * exp ((-τ) • A')‖
      ≤ ‖(τ ^ 2 / 2) • (exp (τ • A') * dblB * exp ((-τ) • A') - dblB)‖ +
        ‖exp (τ • A') * R_triple * exp ((-τ) • A')‖ := norm_add_le _ _
    _ ≤ ‖triAB‖ / 2 * τ ^ 3 + ‖triB‖ / 6 * τ ^ 3 := by
        apply add_le_add
        · rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ τ ^ 2 / 2)]
          calc τ ^ 2 / 2 * ‖exp (τ • A') * dblB * exp ((-τ) • A') - dblB‖
              ≤ τ ^ 2 / 2 * (‖triAB‖ * τ) := mul_le_mul_of_nonneg_left hconj_corr
                (by positivity)
            _ = ‖triAB‖ / 2 * τ ^ 3 := by ring
        · exact hpart2
    _ = (‖triAB‖ / 2 + ‖triB‖ / 6) * τ ^ 3 := by ring

/-- Derivative of the conjugated Strang product (duplicated from StrangCommutatorScaling
  because it is private there). -/
private lemma hasDerivAt_conj_strang' (A B : 𝔸) (τ : ℝ) :
    HasDerivAt
      (fun u => exp ((-u) • (A + B)) * (exp ((u / 2) • A) * exp (u • B) * exp ((u / 2) • A)))
      (exp ((-τ) • (A + B)) *
        ((exp ((τ / 2) • A) * B * exp ((-τ / 2) • A) - B) +
         exp ((τ / 2) • A) * (exp (τ • B) * ((1/2 : ℝ) • A) * exp ((-τ) • B) -
           (1/2 : ℝ) • A) * exp ((-τ / 2) • A)) *
        (exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A))) τ := by
  set A' := (1/2 : ℝ) • A with hA'_def
  set nH := -(A + B) with hnH_def
  have hsmul : ∀ u : ℝ, (u / 2) • A = u • A' := by
    intro u; rw [hA'_def, smul_smul]; ring_nf
  have hneg_smul : ∀ u : ℝ, (-u) • (A + B) = u • nH := by
    intro u; rw [neg_smul, ← smul_neg, ← hnH_def]
  have hfun : (fun u : ℝ => exp ((-u) • (A + B)) *
      (exp ((u / 2) • A) * exp (u • B) * exp ((u / 2) • A))) =
      (fun u => exp (u • nH) * (exp (u • A') * (exp (u • B) * exp (u • A')))) := by
    ext u; rw [hneg_smul, hsmul u, mul_assoc]
  rw [hfun, hneg_smul τ, hsmul τ,
      show (-τ / 2) • A = (-τ) • A' from by rw [hA'_def, smul_smul]; congr 1; ring]
  have hFull := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) nH τ).mul
    ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) A' τ).mul
      ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) B τ).mul
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A' τ)))
  set E := exp (τ • nH)
  set eA := exp (τ • A')
  set enA := exp ((-τ) • A')
  set eB := exp (τ • B)
  set enB := exp ((-τ) • B)
  have hcA : A' * eA = eA * A' := ((Commute.refl A').smul_right τ).exp_right.eq
  have henA_eA : enA * eA = 1 := exp_neg_smul_mul_exp_smul A' τ
  have henB_eB : enB * eB = 1 := exp_neg_smul_mul_exp_smul B τ
  have henA_S : enA * (eA * eB * eA) = eB * eA := by
    rw [← mul_assoc, ← mul_assoc, henA_eA, one_mul]
  have ht1 : eA * B * enA * (eA * eB * eA) = eA * B * eB * eA := by
    rw [show eA * B * enA * (eA * eB * eA) =
      eA * B * (enA * (eA * eB * eA)) from by noncomm_ring, henA_S]; noncomm_ring
  have ht2 : eA * (eB * A' * enB) * enA * (eA * eB * eA) = eA * eB * A' * eA := by
    rw [show eA * (eB * A' * enB) * enA * (eA * eB * eA) =
      eA * (eB * A' * enB) * (enA * (eA * eB * eA)) from by noncomm_ring, henA_S,
      show eA * (eB * A' * enB) * (eB * eA) =
        eA * eB * A' * (enB * eB) * eA from by noncomm_ring, henB_eB, mul_one]
  have ht3 : eA * A' * enA * (eA * eB * eA) = A' * (eA * eB * eA) := by
    rw [show eA * A' * enA * (eA * eB * eA) =
      eA * A' * (enA * (eA * eB * eA)) from by noncomm_ring, henA_S,
      ← mul_assoc, hcA.symm, mul_assoc, mul_assoc,
      show eA * (eB * eA) = eA * eB * eA from (mul_assoc _ _ _).symm]
  have hA_sum : A' + A' = A := by rw [hA'_def, ← add_smul]; norm_num
  have hzero : nH + A' + A' + B = 0 := by
    rw [show nH + A' + A' + B = nH + (A' + A') + B from by abel, hA_sum, hnH_def]; abel
  have halg : E * ((eA * B * enA - B + eA * (eB * A' * enB - A') * enA) *
      (eA * eB * eA)) =
    nH * E * (eA * (eB * eA)) +
    E * (A' * eA * (eB * eA) + eA * (B * eB * eA + eB * (A' * eA))) := by
    calc E * ((eA * B * enA - B + eA * (eB * A' * enB - A') * enA) * (eA * eB * eA))
        = E * (eA * B * enA * (eA * eB * eA) - B * (eA * eB * eA) +
            (eA * (eB * A' * enB) * enA * (eA * eB * eA) -
             eA * A' * enA * (eA * eB * eA))) := by noncomm_ring
      _ = E * (eA * B * eB * eA - B * (eA * eB * eA) +
            (eA * eB * A' * eA - A' * (eA * eB * eA))) := by rw [ht1, ht2, ht3]
      _ = _ := by
          rw [show A' * (eA * eB * eA) = (A' * eA) * eB * eA from by noncomm_ring,
              mul_assoc (eA * eB) A' eA,
              show eA * B * eB * eA = eA * (B * eB) * eA from by rw [mul_assoc eA B eB],
              show nH * E = E * nH from ((Commute.refl nH).smul_right τ).exp_right.eq,
              ← sub_eq_zero]
          calc _ = -(E * ((nH + A' + A' + B) * eA * (eB * eA))) := by noncomm_ring
            _ = -(E * (0 * eA * (eB * eA))) := by rw [hzero]
            _ = 0 := by noncomm_ring
  rw [mul_assoc E, halg]; simp only [Pi.mul_apply] at hFull ⊢; exact hFull

/-- **Tighter Strang commutator-scaling** (anti-Hermitian, norm-of-difference).

  `‖S₂(t) - exp(tH)‖ ≤ ‖D‖/6 · t³ + T/4 · t⁴`

  where `D = [B,[B,A']] - [A',[A',B]]` and T involves triple commutators (A' = A/2).
  Always ≤ the standard bound. Strictly tighter when the double commutators
  partially cancel. -/
theorem norm_strang_comm_scaling_tight [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    let A' := (1/2 : ℝ) • A
    let D := (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
             (A' * (A' * B - B * A') - (A' * B - B * A') * A')
    let T := ‖A' * (A' * (A' * B - B * A') - (A' * B - B * A') * A') -
               (A' * (A' * B - B * A') - (A' * B - B * A') * A') * A'‖ / 3 +
             ‖A' * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
               (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * A'‖ / 2 +
             ‖B * (B * (B * A' - A' * B) - (B * A' - A' * B) * B) -
               (B * (B * A' - A' * B) - (B * A' - A' * B) * B) * B‖ / 6
    ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤
      ‖D‖ / 6 * t ^ 3 + T / 4 * t ^ 4 := by
  intro A' D T
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  have hA' : star A' = -A' := by
    rw [show A' = (1/2 : ℝ) • A from rfl, StarModule.star_smul, hA, smul_neg, star_trivial]
  have hn : ∀ (X : 𝔸), star X = -X → ∀ s : ℝ, ‖exp (s • X)‖ = 1 :=
    fun X hX s => norm_exp_smul_of_skewAdjoint hX s
  set c := A' * B - B * A'
  set dblA := A' * c - c * A'
  set dblB := B * (B * A' - A' * B) - (B * A' - A' * B) * B
  -- FTC-2 setup (same as norm_strang_comm_scaling)
  have hcont : Continuous (fun τ : ℝ =>
      exp ((-τ) • (A + B)) *
        ((exp ((τ / 2) • A) * B * exp ((-τ / 2) • A) - B) +
         exp ((τ / 2) • A) * (exp (τ • B) * A' * exp ((-τ) • B) - A') *
           exp ((-τ / 2) • A)) *
        (exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A))) := by
    apply Continuous.mul (Continuous.mul ?_ ?_) ?_
    · exact exp_continuous.comp (continuous_neg.smul continuous_const)
    · apply Continuous.add
      · exact ((exp_continuous.comp ((continuous_id.div_const 2).smul continuous_const)).mul
            continuous_const).mul
          (exp_continuous.comp ((continuous_neg.div_const 2).smul continuous_const)) |>.sub
          continuous_const
      · exact ((exp_continuous.comp ((continuous_id.div_const 2).smul continuous_const)).mul
            (((exp_continuous.comp (continuous_id.smul continuous_const)).mul
              continuous_const).mul
            (exp_continuous.comp (continuous_neg.smul continuous_const)) |>.sub
            continuous_const)).mul
          (exp_continuous.comp ((continuous_neg.div_const 2).smul continuous_const))
    · exact ((exp_continuous.comp ((continuous_id.div_const 2).smul continuous_const)).mul
          (exp_continuous.comp (continuous_id.smul continuous_const))).mul
        (exp_continuous.comp ((continuous_id.div_const 2).smul continuous_const))
  have hftc := integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_conj_strang' A B u) (hcont.intervalIntegrable 0 t)
  simp only [zero_smul, exp_zero, neg_zero, mul_one, zero_div] at hftc
  have hS₂_eq : exp ((t/2)•A)*exp (t•B)*exp ((t/2)•A) - exp (t•(A+B)) =
      exp (t•(A+B)) * (exp ((-t)•(A+B))*(exp ((t/2)•A)*exp (t•B)*exp ((t/2)•A)) - 1) := by
    rw [mul_sub, mul_one, ← mul_assoc, exp_smul_mul_exp_neg_smul, one_mul]
  have hsmul_eq : ∀ τ0 : ℝ, (τ0 / 2) • A = τ0 • A' := by
    intro τ0; rw [show A' = (1/2 : ℝ) • A from rfl, smul_smul]; ring_nf
  have hneg_smul_eq : ∀ τ0 : ℝ, (-τ0 / 2) • A = (-τ0) • A' := by
    intro τ0; rw [show A' = (1/2 : ℝ) • A from rfl, smul_smul]; ring_nf
  -- Pointwise bound: ‖integrand(τ0)‖ ≤ ‖D‖/2·τ0² + T·τ0³
  have hpointwise : ∀ τ0 ∈ Set.Ioc (0:ℝ) t,
      ‖exp ((-τ0) • (A + B)) *
        ((exp ((τ0 / 2) • A) * B * exp ((-τ0 / 2) • A) - B) +
         exp ((τ0 / 2) • A) * (exp (τ0 • B) * A' * exp ((-τ0) • B) - A') *
           exp ((-τ0 / 2) • A)) *
        (exp ((τ0 / 2) • A) * exp (τ0 • B) * exp ((τ0 / 2) • A))‖ ≤
      ‖D‖ / 2 * τ0 ^ 2 + T * τ0 ^ 3 := by
    intro τ0 hτ0
    have hτ0_nn : 0 ≤ τ0 := le_of_lt hτ0.1
    rw [hsmul_eq τ0, hneg_smul_eq τ0]
    set 𝒯₂ := (exp (τ0 • A') * B * exp ((-τ0) • A') - B) +
      exp (τ0 • A') * (exp (τ0 • B) * A' * exp ((-τ0) • B) - A') * exp ((-τ0) • A')
    -- ‖exp(-H)·𝒯₂·S₂‖ ≤ ‖𝒯₂‖
    have hbound1 : ‖exp ((-τ0) • (A + B)) * 𝒯₂ *
        (exp (τ0 • A') * exp (τ0 • B) * exp (τ0 • A'))‖ ≤ ‖𝒯₂‖ := by
      calc ‖exp ((-τ0) • (A + B)) * 𝒯₂ *
            (exp (τ0 • A') * exp (τ0 • B) * exp (τ0 • A'))‖
          ≤ ‖exp ((-τ0) • (A + B))‖ * ‖𝒯₂‖ *
            ‖exp (τ0 • A') * exp (τ0 • B) * exp (τ0 • A')‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * ‖𝒯₂‖ * 1 := by
            gcongr
            · exact le_of_eq (hn (A + B) hAB (-τ0))
            · calc ‖exp (τ0 • A') * exp (τ0 • B) * exp (τ0 • A')‖
                  ≤ ‖exp (τ0 • A')‖ * ‖exp (τ0 • B)‖ * ‖exp (τ0 • A')‖ :=
                    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                      (norm_mul_le _ _) (norm_nonneg _))
                _ = 1 := by rw [hn A' hA' τ0, hn B hB τ0]; ring
        _ = ‖𝒯₂‖ := by ring
    -- Algebraic decomposition of 𝒯₂ (from norm_strang_comm_scaling)
    have hBA' : B * A' - A' * B = -c := (neg_sub (A' * B) (B * A')).symm
    set g₁ : ℝ → 𝔸 := fun s => exp (s • A') * c * exp ((-s) • A')
    have hf₁_int := exp_conj_sub_eq_integral B A' τ0
    have hg₁_cont : Continuous g₁ :=
      ((exp_continuous.comp (continuous_id.smul continuous_const)).mul
        continuous_const).mul
        (exp_continuous.comp (continuous_neg.smul continuous_const))
    have hg₁_int : IntervalIntegrable g₁ volume 0 τ0 := hg₁_cont.intervalIntegrable 0 τ0
    have hg₁τ_int : IntervalIntegrable (fun _ => g₁ τ0) volume 0 τ0 :=
      continuous_const.intervalIntegrable 0 τ0
    have hPartA_eq : exp (τ0 • A') * B * exp ((-τ0) • A') - B -
        τ0 • (exp (τ0 • A') * c * exp ((-τ0) • A')) =
        ∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0) := by
      rw [hf₁_int]
      rw [show exp (τ0 • A') * c * exp ((-τ0) • A') = g₁ τ0 from rfl]
      rw [show τ0 • g₁ τ0 = ∫ _ in (0:ℝ)..τ0, g₁ τ0 from by
        rw [intervalIntegral.integral_const]; ring]
      rw [← integral_sub hg₁_int hg₁τ_int]
    -- 𝒯₂ = PartA + PartB via commutator cancellation
    have h𝒯₂_decomp : 𝒯₂ =
        (exp (τ0 • A') * B * exp ((-τ0) • A') - B -
          τ0 • (exp (τ0 • A') * c * exp ((-τ0) • A'))) +
        (exp (τ0 • A') *
          (exp (τ0 • B) * A' * exp ((-τ0) • B) - A' - τ0 • (B * A' - A' * B)) *
          exp ((-τ0) • A')) := by
      set eA := exp (τ0 • A')
      set enA := exp ((-τ0) • A')
      set f₂ := exp (τ0 • B) * A' * exp ((-τ0) • B) - A'
      rw [eq_comm, ← sub_eq_zero]
      have hmul_sub : eA * (f₂ - τ0 • (B * A' - A' * B)) * enA =
          eA * f₂ * enA - eA * (τ0 • (B * A' - A' * B)) * enA := by
        rw [mul_sub, sub_mul]
      have hgoal_rw : (eA * B * enA - B - τ0 • (eA * c * enA)) +
          eA * (f₂ - τ0 • (B * A' - A' * B)) * enA =
        ((eA * B * enA - B) + eA * f₂ * enA) -
          (τ0 • (eA * c * enA) + eA * (τ0 • (B * A' - A' * B)) * enA) := by
        rw [hmul_sub]; abel
      rw [hgoal_rw]
      have hcancel : τ0 • (eA * c * enA) +
          eA * (τ0 • (B * A' - A' * B)) * enA = 0 := by
        have h1 : τ0 • (eA * c * enA) = eA * (τ0 • c) * enA := by
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [h1, hBA', smul_neg, mul_neg, neg_mul, add_neg_cancel]
      rw [hcancel, sub_zero, sub_self]
    -- Now bound 𝒯₂ using the two auxiliary lemmas
    -- PartA = ∫(g₁(s)-g₁(τ0))  (from hPartA_eq)
    -- norm_partA_sub_leading: ‖PartA + (τ0²/2)·dblA‖ ≤ ‖triA‖/3·τ0³
    -- norm_partB_sub_leading: ‖PartB - (τ0²/2)·dblB‖ ≤ (‖triAB‖/2+‖triB‖/6)·τ0³
    -- 𝒯₂ = (PartA + (τ0²/2)·dblA) + (PartB - (τ0²/2)·dblB) + (τ0²/2)·(dblB - dblA)
    have hPartA := norm_partA_sub_leading B A' hA' hτ0_nn
    have hPartB := norm_partB_sub_leading B A' hA' hB hτ0_nn
    -- Rewrite h𝒯₂_decomp using hPartA_eq
    set PartB := exp (τ0 • A') *
          (exp (τ0 • B) * A' * exp ((-τ0) • B) - A' - τ0 • (B * A' - A' * B)) *
          exp ((-τ0) • A')
    have h𝒯₂_refined : 𝒯₂ =
        ((∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0)) + (τ0 ^ 2 / 2) • dblA) +
        (PartB - (τ0 ^ 2 / 2) • dblB) +
        (τ0 ^ 2 / 2) • (dblB - dblA) := by
      rw [h𝒯₂_decomp, hPartA_eq]
      set PA := ∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0)
      module
    calc ‖exp ((-τ0) • (A + B)) * 𝒯₂ *
          (exp (τ0 • A') * exp (τ0 • B) * exp (τ0 • A'))‖
        ≤ ‖𝒯₂‖ := hbound1
      _ = ‖((∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0)) + (τ0 ^ 2 / 2) • dblA) +
            (PartB - (τ0 ^ 2 / 2) • dblB) +
            (τ0 ^ 2 / 2) • (dblB - dblA)‖ := by rw [h𝒯₂_refined]
      _ ≤ ‖(∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0)) + (τ0 ^ 2 / 2) • dblA‖ +
            ‖PartB - (τ0 ^ 2 / 2) • dblB‖ +
            ‖(τ0 ^ 2 / 2) • (dblB - dblA)‖ := by
          calc _ ≤ ‖((∫ s in (0:ℝ)..τ0, (g₁ s - g₁ τ0)) + (τ0 ^ 2 / 2) • dblA) +
                    (PartB - (τ0 ^ 2 / 2) • dblB)‖ +
                  ‖(τ0 ^ 2 / 2) • (dblB - dblA)‖ := norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A' * dblA - dblA * A'‖ / 3 * τ0 ^ 3 +
            (‖A' * dblB - dblB * A'‖ / 2 + ‖B * dblB - dblB * B‖ / 6) * τ0 ^ 3 +
            (τ0 ^ 2 / 2 * ‖dblB - dblA‖) := by
          have hsmul_bound : ‖(τ0 ^ 2 / 2) • (dblB - dblA)‖ = τ0 ^ 2 / 2 * ‖dblB - dblA‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ τ0 ^ 2 / 2)]
          rw [hsmul_bound]
          exact add_le_add (add_le_add hPartA hPartB) le_rfl
      _ = ‖D‖ / 2 * τ0 ^ 2 + T * τ0 ^ 3 := by
          -- D = dblB - dblA, T = triA_norm/3 + triAB_norm/2 + triB_norm/6
          show ‖A' * dblA - dblA * A'‖ / 3 * τ0 ^ 3 +
            (‖A' * dblB - dblB * A'‖ / 2 + ‖B * dblB - dblB * B‖ / 6) * τ0 ^ 3 +
            τ0 ^ 2 / 2 * ‖dblB - dblA‖ =
            ‖D‖ / 2 * τ0 ^ 2 + T * τ0 ^ 3
          have hD_eq : D = dblB - dblA := rfl
          rw [hD_eq]; ring
  -- Integrate: ∫₀ᵗ (‖D‖/2·τ0² + T·τ0³) dτ0 = ‖D‖/6·t³ + T/4·t⁴
  rw [hS₂_eq]
  have hstep1 : ‖exp (t • (A + B)) *
      (exp ((-t) • (A + B)) * (exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A)) - 1)‖ ≤
      ‖exp ((-t) • (A + B)) * (exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A)) - 1‖ := by
    calc _ ≤ ‖exp (t • (A + B))‖ *
          ‖exp ((-t) • (A + B)) * (exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A)) - 1‖ :=
          norm_mul_le _ _
      _ = _ := by rw [hn (A + B) hAB t, one_mul]
  have hstep2 : exp ((-t) • (A + B)) *
      (exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A)) - 1 =
      ∫ τ0 in (0:ℝ)..t, exp ((-τ0) • (A + B)) *
        ((exp ((τ0 / 2) • A) * B * exp ((-τ0 / 2) • A) - B) +
         exp ((τ0 / 2) • A) * (exp (τ0 • B) * A' * exp ((-τ0) • B) - A') *
           exp ((-τ0 / 2) • A)) *
        (exp ((τ0 / 2) • A) * exp (τ0 • B) * exp ((τ0 / 2) • A)) := hftc.symm
  have hg_int : IntervalIntegrable
      (fun τ0 => ‖D‖ / 2 * τ0 ^ 2 + T * τ0 ^ 3) volume 0 t :=
    ((continuous_const.mul (continuous_id.pow 2)).add
      (continuous_const.mul (continuous_id.pow 3))).intervalIntegrable 0 t
  calc _ ≤ ‖exp ((-t) • (A + B)) *
          (exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A)) - 1‖ := hstep1
    _ = ‖∫ τ0 in (0:ℝ)..t, exp ((-τ0) • (A + B)) *
          ((exp ((τ0 / 2) • A) * B * exp ((-τ0 / 2) • A) - B) +
           exp ((τ0 / 2) • A) * (exp (τ0 • B) * A' * exp ((-τ0) • B) - A') *
             exp ((-τ0 / 2) • A)) *
          (exp ((τ0 / 2) • A) * exp (τ0 • B) * exp ((τ0 / 2) • A))‖ := by rw [hstep2]
    _ ≤ ∫ τ0 in (0:ℝ)..t, (‖D‖ / 2 * τ0 ^ 2 + T * τ0 ^ 3) := by
        apply norm_integral_le_of_norm_le ht _ hg_int
        exact Filter.Eventually.of_forall (fun τ0 hτ0 => hpointwise τ0 hτ0)
    _ = ‖D‖ / 2 * (t ^ 3 / 3) + T * (t ^ 4 / 4) := by
        -- Compute via FTC on the primitive F(x) = ‖D‖/2·x³/3 + T·x⁴/4
        have hd : ∀ x ∈ Set.uIcc 0 t,
            HasDerivAt (fun x => ‖D‖ / 2 * (x ^ 3 / 3) + T * (x ^ 4 / 4))
              (‖D‖ / 2 * x ^ 2 + T * x ^ 3) x := by
          intro x _
          have h1 : HasDerivAt (fun x => x ^ 3 / 3) (x ^ 2) x := by
            convert (hasDerivAt_pow 3 x).div_const 3 using 1
            simp only [Nat.cast_ofNat]; ring
          have h2 : HasDerivAt (fun x => x ^ 4 / 4) (x ^ 3) x := by
            convert (hasDerivAt_pow 4 x).div_const 4 using 1
            simp only [Nat.cast_ofNat]; ring
          exact (h1.const_mul _).add (h2.const_mul _)
        rw [integral_eq_sub_of_hasDerivAt hd (hg_int)]
        simp
    _ = ‖D‖ / 6 * t ^ 3 + T / 4 * t ^ 4 := by ring
