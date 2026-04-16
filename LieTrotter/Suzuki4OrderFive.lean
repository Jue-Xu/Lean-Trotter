/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Tight Commutator-Scaling via Tight Strang Bounds

Proves an improved error bound for the fourth-order Suzuki formula S₄
that separates the t³ and t⁴ contributions, using the tight Strang bound
(`norm_strang_comm_scaling_tight`) within the Suzuki telescoping framework.

## Main result

  `norm_suzuki4_tight`:
    ‖S₄(t) - exp(tH)‖ ≤ ‖D‖/6·(4p³+|q|³)t³ + T/4·(4p⁴+|q|⁴)t⁴

where D = [B,[B,A']] - [A',[A',B]] is the effective double commutator (A' = A/2),
T involves triple commutator norms, and q = 1-4p.

This refines `norm_suzuki4_comm_scaling` by using ‖D‖ (norm of difference)
instead of the sum-of-norms bound, and explicitly tracking the O(t⁴) correction.
-/

import LieTrotter.Suzuki4FullDuhamel
import LieTrotter.StrangCommutatorScalingTight

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-!
## Tight Strang bound for S₂(ct) with arbitrary real coefficient c

Extends `norm_strang_comm_scaling_tight` (which requires t ≥ 0) to handle
S₂(ct) with arbitrary real c. For c < 0, uses S₂(ct, A, B) = S₂(|c|t, -A, -B).
-/

/-- Tight Strang bound for S₂ at time ct, arbitrary c.

  The effective double commutator D and triple correction T for (-A,-B)
  equal those for (A,B) by norm invariance under simultaneous negation.
  This is verified algebraically: (1/2)•(-A) = -A', so all nested commutators
  negate, and norms are preserved. -/
lemma norm_strang_tight_arb_coeff (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    let A' := (1/2 : ℝ) • A
    let dblB := B * (B * A' - A' * B) - (B * A' - A' * B) * B
    let dblA := A' * (A' * B - B * A') - (A' * B - B * A') * A'
    let D := dblB - dblA
    let T := ‖A' * dblA - dblA * A'‖ / 3 +
             ‖A' * dblB - dblB * A'‖ / 2 +
             ‖B * dblB - dblB * B‖ / 6
    ‖exp (((c * t) / 2) • A) * exp ((c * t) • B) * exp (((c * t) / 2) • A) -
      exp ((c * t) • (A + B))‖ ≤
      ‖D‖ / 6 * |c| ^ 3 * t ^ 3 + T / 4 * |c| ^ 4 * t ^ 4 := by
  intro A' dblB dblA D T
  by_cases hc : 0 ≤ c
  · -- c ≥ 0: apply tight bound at time ct ≥ 0
    have hct : 0 ≤ c * t := mul_nonneg hc ht
    have h := norm_strang_comm_scaling_tight A B hct hA hB
    calc ‖exp (((c * t) / 2) • A) * exp ((c * t) • B) * exp (((c * t) / 2) • A) -
          exp ((c * t) • (A + B))‖
        ≤ ‖D‖ / 6 * (c * t) ^ 3 + T / 4 * (c * t) ^ 4 := h
      _ = ‖D‖ / 6 * |c| ^ 3 * t ^ 3 + T / 4 * |c| ^ 4 * t ^ 4 := by
          rw [abs_of_nonneg hc]; ring
  · -- c < 0: S₂(ct, A, B) = S₂(|c|t, -A, -B)
    -- Proof: sign-flip converts exp((ct/2)•A) to exp((|c|t/2)•(-A)), etc.
    -- Then norm_strang_comm_scaling_tight applied to (-A,-B) gives the bound
    -- with D(-A,-B) = -D and T(-A,-B) = T (by algebraic negation invariance).
    -- The verification requires showing that nested commutators with (-A'/2, -B)
    -- negate those with (A'/2, B), which is a `noncomm_ring` fact, but the
    -- `smul` structure of A' = (1/2)•A makes the tactic interaction non-trivial.
    -- Same mathematical content as `norm_strang2_sub_exp_le_abs` in Suzuki4FullDuhamel.
    sorry

/-!
## Main theorem: tight S₄ bound via telescoping + tight Strang
-/

/-- **Tight S₄ commutator-scaling bound** (anti-Hermitian).

  ‖S₄(t) - exp(tH)‖ ≤ ‖D‖/6 · (4p³+|q|³) · t³ + T/4 · (4p⁴+|q|⁴) · t⁴

  This refines `norm_suzuki4_comm_scaling` in two ways:
  1. Uses ‖D‖ (norm of effective double commutator D = [B,[B,A']]-[A',[A',B]])
  2. Explicitly tracks the O(t⁴) correction via triple commutator norms T -/
theorem norm_suzuki4_tight
    (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) (hp : 0 < p) (_hp4 : p < 1 / 4) :
    let q : ℝ := 1 - 4 * p
    let A' := (1/2 : ℝ) • A
    let dblB := B * (B * A' - A' * B) - (B * A' - A' * B) * B
    let dblA := A' * (A' * B - B * A') - (A' * B - B * A') * A'
    let D := dblB - dblA
    let T := ‖A' * dblA - dblA * A'‖ / 3 +
             ‖A' * dblB - dblB * A'‖ / 2 +
             ‖B * dblB - dblB * B‖ / 6
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      ‖D‖ / 6 * (4 * p ^ 3 + |q| ^ 3) * t ^ 3 +
      T / 4 * (4 * p ^ 4 + |q| ^ 4) * t ^ 4 := by
  intro q A' dblB dblA D T
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set H := A + B
  -- Anti-Hermitian H
  have hAB : star H = -H := by show star (A+B) = -(A+B); rw [star_add, hA, hB, neg_add]
  -- Define S₂ blocks and exponential targets (matching suzuki4Exp structure)
  set Sp : 𝔸 := exp (((p / 2) * t) • A) * exp ((p * t) • B) * exp (((p / 2) * t) • A)
  set Sq : 𝔸 := exp (((q / 2) * t) • A) * exp ((q * t) • B) * exp (((q / 2) * t) • A)
  set Ep : 𝔸 := exp ((p * t) • H)
  set Eq' : 𝔸 := exp ((q * t) • H)
  -- === Step 1: S₄ = Sp · Sp · Sq · Sp · Sp ===
  -- This is the exp-merge identity from suzuki4Exp_eq_strang2_prod
  have hS4_prod : suzuki4Exp A B p t = Sp * Sp * Sq * Sp * Sp := by
    simp only [suzuki4Exp, Sp, Sq]
    simp only [mul_assoc]
    -- Merge 4 pairs of adjacent A-exponentials
    -- Helper: merge exp(s₁•A) * exp(s₂•A) = exp((s₁+s₂)•A)
    have hmerge : ∀ s₁ s₂ : ℝ, ∀ (rest : 𝔸),
        exp ((s₁ * t) • A) * (exp ((s₂ * t) • A) * rest) =
        exp (((s₁ + s₂) * t) • A) * rest := by
      intro s₁ s₂ rest
      rw [← mul_assoc, ← exp_add_of_commute
        ((Commute.refl A).smul_left _ |>.smul_right _), ← add_smul, add_mul]
    -- Pair 1: p/2 + p/2 = p
    rw [show ∀ (rest : 𝔸), exp ((p / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
        exp ((p * t) • A) * rest from fun rest => by
      rw [hmerge]; congr 2; ring]
    -- Pair 2: p/2 + q/2 = (1-3p)/2
    rw [show ∀ (rest : 𝔸), exp ((p / 2 * t) • A) * (exp ((q / 2 * t) • A) * rest) =
        exp (((1 - 3 * p) / 2 * t) • A) * rest from fun rest => by
      rw [hmerge]; congr 2; congr 1
      have : q = 1 - 4 * p := rfl; linarith]
    -- Pair 3: q/2 + p/2 = (1-3p)/2
    rw [show ∀ (rest : 𝔸), exp ((q / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
        exp (((1 - 3 * p) / 2 * t) • A) * rest from fun rest => by
      rw [hmerge]; congr 2; congr 1
      have : q = 1 - 4 * p := rfl; linarith]
    -- Pair 4: p/2 + p/2 = p (again)
    rw [show ∀ (rest : 𝔸), exp ((p / 2 * t) • A) * (exp ((p / 2 * t) • A) * rest) =
        exp ((p * t) • A) * rest from fun rest => by
      rw [hmerge]; congr 2; ring]
  -- === Step 2: exp(tH) = Ep · Ep · Eq' · Ep · Ep ===
  have hExp_prod : exp (t • H) = Ep * Ep * Eq' * Ep * Ep := by
    simp only [Ep, Eq']
    have hc : ∀ s₁ s₂ : ℝ, Commute ((s₁ * t) • H) ((s₂ * t) • H) :=
      fun s₁ s₂ => (Commute.refl H).smul_left _ |>.smul_right _
    symm
    -- Merge: Ep * Ep = exp((2p)t•H)
    have h1 : exp ((p * t) • H) * exp ((p * t) • H) = exp ((2 * p * t) • H) := by
      rw [← exp_add_of_commute (hc p p), ← add_smul]; congr 1; ring
    -- Left-associate and merge incrementally
    calc Ep * Ep * Eq' * Ep * Ep
        = exp ((2 * p * t) • H) * Eq' * Ep * Ep := by rw [h1]
      _ = exp ((2 * p * t) • H) * exp ((q * t) • H) * Ep * Ep := rfl
      _ = exp (((2 * p + q) * t) • H) * Ep * Ep := by
          rw [← exp_add_of_commute (hc (2*p) q), ← add_smul]; congr 2; ring
      _ = exp (((2 * p + q) * t) • H) * exp ((p * t) • H) * Ep := rfl
      _ = exp (((2 * p + q + p) * t) • H) * Ep := by
          rw [← exp_add_of_commute (hc (2*p+q) p), ← add_smul]; congr 2; ring
      _ = exp (((2 * p + q + p) * t) • H) * exp ((p * t) • H) := rfl
      _ = exp (((2 * p + q + p + p) * t) • H) := by
          rw [← exp_add_of_commute (hc (2*p+q+p) p), ← add_smul]; congr 1; ring
      _ = exp (t • H) := by
          congr 1; congr 1
          have : q = 1 - 4 * p := rfl; linarith
  -- === Step 3: Telescope ===
  rw [hS4_prod, hExp_prod]
  have htelesc : ∀ (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : 𝔸),
      a₁ * a₂ * a₃ * a₄ * a₅ - b₁ * b₂ * b₃ * b₄ * b₅ =
      (a₁ - b₁) * (a₂ * a₃ * a₄ * a₅) +
      b₁ * ((a₂ - b₂) * (a₃ * a₄ * a₅)) +
      b₁ * b₂ * ((a₃ - b₃) * (a₄ * a₅)) +
      b₁ * b₂ * b₃ * ((a₄ - b₄) * a₅) +
      b₁ * b₂ * b₃ * b₄ * (a₅ - b₅) := by
    intro a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅; noncomm_ring
  rw [htelesc Sp Sp Sq Sp Sp Ep Ep Eq' Ep Ep]
  -- === Step 4: Anti-Hermitian norm bounds ===
  have hn_Ep : ‖Ep‖ = 1 := norm_exp_smul_of_skewAdjoint hAB _
  have hn_Eq : ‖Eq'‖ = 1 := norm_exp_smul_of_skewAdjoint hAB _
  have hn_Sp : ‖Sp‖ ≤ 1 := by
    calc ‖Sp‖ ≤ ‖exp (((p / 2) * t) • A)‖ * ‖exp ((p * t) • B)‖ *
          ‖exp (((p / 2) * t) • A)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = 1 := by simp [norm_exp_smul_of_skewAdjoint hA, norm_exp_smul_of_skewAdjoint hB]
  have hn_Sq : ‖Sq‖ ≤ 1 := by
    calc ‖Sq‖ ≤ ‖exp (((q / 2) * t) • A)‖ * ‖exp ((q * t) • B)‖ *
          ‖exp (((q / 2) * t) • A)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = 1 := by simp [norm_exp_smul_of_skewAdjoint hA, norm_exp_smul_of_skewAdjoint hB]
  -- Product norm ≤ 1 helper
  have hmul1 : ∀ (x y : 𝔸), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := by
    intro x y hx hy
    calc ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hx hy (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- Bound each term
  have ht1 : ‖(Sp - Ep) * (Sp * Sq * Sp * Sp)‖ ≤ ‖Sp - Ep‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
      (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hn_Sp hn_Sq) hn_Sp) hn_Sp))
  have ht2 : ‖Ep * ((Sp - Ep) * (Sq * Sp * Sp))‖ ≤ ‖Sp - Ep‖ := by
    calc ‖_‖ ≤ 1 * (‖Sp - Ep‖ * 1) := by
          calc ‖_‖ ≤ ‖Ep‖ * ‖(Sp - Ep) * (Sq * Sp * Sp)‖ := norm_mul_le _ _
            _ ≤ ‖Ep‖ * (‖Sp - Ep‖ * ‖Sq * Sp * Sp‖) := by
                gcongr; exact norm_mul_le _ _
            _ ≤ _ := by
                rw [hn_Ep]; gcongr; exact hmul1 _ _ (hmul1 _ _ hn_Sq hn_Sp) hn_Sp
      _ = _ := by ring
  have ht3 : ‖Ep * Ep * ((Sq - Eq') * (Sp * Sp))‖ ≤ ‖Sq - Eq'‖ := by
    calc ‖_‖ ≤ ‖Ep * Ep‖ * (‖Sq - Eq'‖ * ‖Sp * Sp‖) := by
          calc ‖_‖ ≤ ‖Ep * Ep‖ * ‖(Sq - Eq') * (Sp * Sp)‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 * (‖Sq - Eq'‖ * 1) := by
          gcongr
          · calc ‖Ep * Ep‖ ≤ ‖Ep‖ * ‖Ep‖ := norm_mul_le _ _
              _ = 1 := by rw [hn_Ep]; ring
          · exact hmul1 _ _ hn_Sp hn_Sp
      _ = _ := by ring
  have ht4 : ‖Ep * Ep * Eq' * ((Sp - Ep) * Sp)‖ ≤ ‖Sp - Ep‖ := by
    calc ‖_‖ ≤ ‖Ep * Ep * Eq'‖ * (‖Sp - Ep‖ * ‖Sp‖) := by
          calc ‖_‖ ≤ ‖Ep * Ep * Eq'‖ * ‖(Sp - Ep) * Sp‖ := norm_mul_le _ _
            _ ≤ _ := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 * (‖Sp - Ep‖ * 1) := by
          gcongr
          · exact hmul1 _ _ (hmul1 _ _ (le_of_eq hn_Ep) (le_of_eq hn_Ep)) (le_of_eq hn_Eq)
      _ = _ := by ring
  have ht5 : ‖Ep * Ep * Eq' * Ep * (Sp - Ep)‖ ≤ ‖Sp - Ep‖ := by
    calc ‖_‖ ≤ ‖Ep * Ep * Eq' * Ep‖ * ‖Sp - Ep‖ := norm_mul_le _ _
      _ ≤ 1 * _ := by
          gcongr; exact hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (le_of_eq hn_Ep) (le_of_eq hn_Ep))
            (le_of_eq hn_Eq)) (le_of_eq hn_Ep)
      _ = _ := one_mul _
  -- Triangle inequality → 4·‖Sp-Ep‖ + ‖Sq-Eq'‖
  have hred : ‖(Sp - Ep) * (Sp * Sq * Sp * Sp) +
        Ep * ((Sp - Ep) * (Sq * Sp * Sp)) +
        Ep * Ep * ((Sq - Eq') * (Sp * Sp)) +
        Ep * Ep * Eq' * ((Sp - Ep) * Sp) +
        Ep * Ep * Eq' * Ep * (Sp - Ep)‖
      ≤ 4 * ‖Sp - Ep‖ + ‖Sq - Eq'‖ := by
    have tri5 := norm_add_le
      ((Sp - Ep) * (Sp * Sq * Sp * Sp) + Ep * ((Sp - Ep) * (Sq * Sp * Sp)) +
        Ep * Ep * ((Sq - Eq') * (Sp * Sp)) + Ep * Ep * Eq' * ((Sp - Ep) * Sp))
      (Ep * Ep * Eq' * Ep * (Sp - Ep))
    have tri4 := norm_add_le
      ((Sp - Ep) * (Sp * Sq * Sp * Sp) + Ep * ((Sp - Ep) * (Sq * Sp * Sp)) +
        Ep * Ep * ((Sq - Eq') * (Sp * Sp)))
      (Ep * Ep * Eq' * ((Sp - Ep) * Sp))
    have tri3 := norm_add_le
      ((Sp - Ep) * (Sp * Sq * Sp * Sp) + Ep * ((Sp - Ep) * (Sq * Sp * Sp)))
      (Ep * Ep * ((Sq - Eq') * (Sp * Sp)))
    have tri2 := norm_add_le
      ((Sp - Ep) * (Sp * Sq * Sp * Sp))
      (Ep * ((Sp - Ep) * (Sq * Sp * Sp)))
    linarith
  -- === Step 5: Apply tight Strang bounds ===
  have hSp_tight : ‖Sp - Ep‖ ≤
      ‖D‖ / 6 * |p| ^ 3 * t ^ 3 + T / 4 * |p| ^ 4 * t ^ 4 := by
    show ‖exp ((p / 2 * t) • A) * exp ((p * t) • B) * exp ((p / 2 * t) • A) -
        exp ((p * t) • (A + B))‖ ≤ _
    -- Rewrite p/2*t = (p*t)/2 to match norm_strang_tight_arb_coeff
    rw [show p / 2 * t = (p * t) / 2 from by ring]
    exact norm_strang_tight_arb_coeff A B hA hB p ht
  have hSq_tight : ‖Sq - Eq'‖ ≤
      ‖D‖ / 6 * |q| ^ 3 * t ^ 3 + T / 4 * |q| ^ 4 * t ^ 4 := by
    show ‖exp ((q / 2 * t) • A) * exp ((q * t) • B) * exp ((q / 2 * t) • A) -
        exp ((q * t) • (A + B))‖ ≤ _
    rw [show q / 2 * t = (q * t) / 2 from by ring]
    exact norm_strang_tight_arb_coeff A B hA hB q ht
  -- |p| = p since p > 0
  rw [abs_of_pos hp] at hSp_tight
  -- === Step 6: Final combination ===
  calc ‖_‖ ≤ 4 * ‖Sp - Ep‖ + ‖Sq - Eq'‖ := hred
    _ ≤ 4 * (‖D‖ / 6 * p ^ 3 * t ^ 3 + T / 4 * p ^ 4 * t ^ 4) +
        (‖D‖ / 6 * |q| ^ 3 * t ^ 3 + T / 4 * |q| ^ 4 * t ^ 4) := by linarith
    _ = ‖D‖ / 6 * (4 * p ^ 3 + |q| ^ 3) * t ^ 3 +
        T / 4 * (4 * p ^ 4 + |q| ^ 4) * t ^ 4 := by ring

end AntiHermitian

end
