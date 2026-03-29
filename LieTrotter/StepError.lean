/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track C: Quadratic Step Error

The key estimate: ‖exp(a)exp(b) - exp(a+b)‖ ≤ 2‖a‖‖b‖ exp(‖a‖+‖b‖)
and its specialization to the Lie-Trotter step with a = A/n, b = B/n.
-/

import LieTrotter.ExpBounds

open NormedSpace
open scoped BigOperators Nat

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## C1: Quadratic error bound (HARDEST LEMMA)

`‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`

Recommended approach: second-order expansion.
Write `exp(a) = 1 + a + Rₐ`, `exp(b) = 1 + b + R_b` with
`‖Rₐ‖ ≤ ‖a‖²/2 · exp(‖a‖)` (from B4).
Then expand the product and bound each cross term.
-/

-- Auxiliary: Real.exp x - 1 ≤ x * Real.exp x for x ≥ 0
private lemma exp_sub_one_le_mul_exp {x : ℝ} (_hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have hexp_pos := Real.exp_pos x
  have h2 : (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x := by
    have h1' : 1 - x ≤ Real.exp (-x) := by linarith
    exact mul_le_mul_of_nonneg_right h1' hexp_pos.le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  linarith

-- Auxiliary: ‖(a+b)^m - a^m - b^m‖ ≤ (‖a‖+‖b‖)^m - ‖a‖^m - ‖b‖^m for m ≥ 1
omit [CompleteSpace 𝔸] in
private lemma norm_pow_add_sub_pow_sub_pow (a b : 𝔸) :
    ∀ m : ℕ, 1 ≤ m →
      ‖(a + b) ^ m - a ^ m - b ^ m‖ ≤
        (‖a‖ + ‖b‖) ^ m - ‖a‖ ^ m - ‖b‖ ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- m = 1: (a+b)^1 - a^1 - b^1 = 0, both sides are 0
      simp only [Nat.zero_add, pow_one]
      have lhs_zero : (a + b) - a - b = (0 : 𝔸) := by abel
      have rhs_zero : (‖a‖ + ‖b‖) - ‖a‖ - ‖b‖ = (0 : ℝ) := by ring
      rw [lhs_zero, rhs_zero, norm_zero]
    | succ k =>
      -- m = k + 2, inductive step from k + 1 ≥ 1
      have hk1 : 1 ≤ k + 1 := by omega
      have ih' := ih hk1
      -- Algebraic identity:
      -- (a+b)^(k+2) - a^(k+2) - b^(k+2) =
      --   (a+b) * ((a+b)^(k+1) - a^(k+1) - b^(k+1)) + a * b^(k+1) + b * a^(k+1)
      have alg_id : (a + b) ^ (k + 2) - a ^ (k + 2) - b ^ (k + 2) =
          (a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)) +
          a * b ^ (k + 1) + b * a ^ (k + 1) := by
        have ha : a ^ (k + 2) = a * a ^ (k + 1) := pow_succ' a (k + 1)
        have hb : b ^ (k + 2) = b * b ^ (k + 1) := pow_succ' b (k + 1)
        have hab : (a + b) ^ (k + 2) = (a + b) * (a + b) ^ (k + 1) := pow_succ' (a + b) (k + 1)
        rw [ha, hb, hab]
        noncomm_ring
      rw [alg_id]
      -- Bound: ‖X + Y + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖
      have h_tri : ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)) +
          a * b ^ (k + 1) + b * a ^ (k + 1)‖ ≤
          ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1))‖ +
          ‖a * b ^ (k + 1)‖ + ‖b * a ^ (k + 1)‖ := by
        calc ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)) +
              a * b ^ (k + 1) + b * a ^ (k + 1)‖
            ≤ ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)) +
              a * b ^ (k + 1)‖ + ‖b * a ^ (k + 1)‖ := norm_add_le _ _
          _ ≤ (‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1))‖ +
              ‖a * b ^ (k + 1)‖) + ‖b * a ^ (k + 1)‖ := by
              gcongr; exact norm_add_le _ _
          _ = _ := by ring
      -- Bound each term
      have h1 : ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1))‖ ≤
          (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) ^ (k + 1) - ‖a‖ ^ (k + 1) - ‖b‖ ^ (k + 1)) := by
        calc ‖(a + b) * ((a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1))‖
            ≤ ‖a + b‖ * ‖(a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)‖ :=
              norm_mul_le _ _
          _ ≤ (‖a‖ + ‖b‖) * ‖(a + b) ^ (k + 1) - a ^ (k + 1) - b ^ (k + 1)‖ :=
              mul_le_mul_of_nonneg_right (norm_add_le a b) (norm_nonneg _)
          _ ≤ (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) ^ (k + 1) - ‖a‖ ^ (k + 1) - ‖b‖ ^ (k + 1)) := by
              exact mul_le_mul_of_nonneg_left ih' (by positivity)
      have h2 : ‖a * b ^ (k + 1)‖ ≤ ‖a‖ * ‖b‖ ^ (k + 1) := by
        calc ‖a * b ^ (k + 1)‖ ≤ ‖a‖ * ‖b ^ (k + 1)‖ := norm_mul_le _ _
          _ ≤ ‖a‖ * ‖b‖ ^ (k + 1) := by gcongr; exact norm_pow_le b (k + 1)
      have h3 : ‖b * a ^ (k + 1)‖ ≤ ‖b‖ * ‖a‖ ^ (k + 1) := by
        calc ‖b * a ^ (k + 1)‖ ≤ ‖b‖ * ‖a ^ (k + 1)‖ := norm_mul_le _ _
          _ ≤ ‖b‖ * ‖a‖ ^ (k + 1) := by gcongr; exact norm_pow_le a (k + 1)
      -- Combine and use ring
      have real_id : (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) ^ (k + 1) - ‖a‖ ^ (k + 1) - ‖b‖ ^ (k + 1)) +
          ‖a‖ * ‖b‖ ^ (k + 1) + ‖b‖ * ‖a‖ ^ (k + 1) =
          (‖a‖ + ‖b‖) ^ (k + 2) - ‖a‖ ^ (k + 2) - ‖b‖ ^ (k + 2) := by ring
      linarith

-- Auxiliary: bound on the cross term ‖exp(a+b) - exp(a) - exp(b) + 1‖
include 𝕂 in
private lemma norm_exp_cross_term_le (a b : 𝔸) :
    ‖exp (a + b) - exp a - exp b + 1‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
  -- Summability of the three exp series
  have hsumm_ab := exp_summable (𝕂 := 𝕂) (a + b)
  have hsumm_a := exp_summable (𝕂 := 𝕂) a
  have hsumm_b := exp_summable (𝕂 := 𝕂) b
  -- Shifted summability (n ↦ n+1)
  have hsumm1_ab : Summable fun n => (((↑(n + 1)! : 𝕂)⁻¹ • (a + b) ^ (n + 1)) : 𝔸) :=
    hsumm_ab.comp_injective (fun _ _ h => by omega)
  have hsumm1_a : Summable fun n => (((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1)) : 𝔸) :=
    hsumm_a.comp_injective (fun _ _ h => by omega)
  have hsumm1_b : Summable fun n => (((↑(n + 1)! : 𝕂)⁻¹ • b ^ (n + 1)) : 𝔸) :=
    hsumm_b.comp_injective (fun _ _ h => by omega)
  -- Summability of the cross term series (n ↦ n+1)
  have hsumm1_cross : Summable fun n =>
      ((↑(n + 1)! : 𝕂)⁻¹ • ((a + b) ^ (n + 1) - a ^ (n + 1) - b ^ (n + 1)) : 𝔸) := by
    have h1 := hsumm1_ab.sub hsumm1_a
    have h2 := h1.sub hsumm1_b
    refine h2.congr (fun n => ?_)
    simp only [smul_sub]
  -- Shifted summability (n ↦ n+2) for the cross term
  have hsumm2_cross : Summable fun n =>
      ((↑(n + 2)! : 𝕂)⁻¹ • ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸) :=
    hsumm1_cross.comp_injective (fun _ _ h => by omega)
  -- Step 1: Express the cross term as a tsum
  -- exp(a+b) - exp(a) - exp(b) + 1 = (exp(a+b)-1) - (exp(a)-1) - (exp(b)-1)
  --   = ∑'_{n≥0} (n+1)!⁻¹ • ((a+b)^(n+1) - a^(n+1) - b^(n+1))
  have cross_eq_shifted1 : exp (a + b) - exp a - exp b + 1 =
      ∑' n, ((↑(n + 1)! : 𝕂)⁻¹ • ((a + b) ^ (n + 1) - a ^ (n + 1) - b ^ (n + 1)) : 𝔸) := by
    have hab_eq : exp (a + b) - 1 =
        ∑' n, ((↑(n + 1)! : 𝕂)⁻¹ • (a + b) ^ (n + 1) : 𝔸) := by
      rw [exp_tsum_form (𝕂 := 𝕂), hsumm_ab.tsum_eq_zero_add]
      simp [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    have ha_eq : exp a - 1 =
        ∑' n, ((↑(n + 1)! : 𝕂)⁻¹ • a ^ (n + 1) : 𝔸) := by
      rw [exp_tsum_form (𝕂 := 𝕂), hsumm_a.tsum_eq_zero_add]
      simp [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    have hb_eq : exp b - 1 =
        ∑' n, ((↑(n + 1)! : 𝕂)⁻¹ • b ^ (n + 1) : 𝔸) := by
      rw [exp_tsum_form (𝕂 := 𝕂), hsumm_b.tsum_eq_zero_add]
      simp [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    have rearrange : exp (a + b) - exp a - exp b + 1 =
        (exp (a + b) - 1) - (exp a - 1) - (exp b - 1) := by abel
    rw [rearrange, hab_eq, ha_eq, hb_eq,
        ← hsumm1_ab.tsum_sub hsumm1_a, ← (hsumm1_ab.sub hsumm1_a).tsum_sub hsumm1_b]
    congr 1; ext n; simp only [smul_sub]
  -- The n=0 term of the +1-shifted series is 0: (a+b)^1 - a^1 - b^1 = 0
  -- So peel it off to get the +2-shifted series
  have cross_eq : exp (a + b) - exp a - exp b + 1 =
      ∑' n, ((↑(n + 2)! : 𝕂)⁻¹ • ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸) := by
    rw [cross_eq_shifted1, hsumm1_cross.tsum_eq_zero_add]
    simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    have h0 : (a + b) - a - b = (0 : 𝔸) := by abel
    rw [h0, zero_add]
  -- Step 2: Bound the norm using norm_tsum_le_tsum_norm and the inductive bound
  -- Real-side summability
  have hrsumm := real_exp_summable (‖a‖ + ‖b‖)
  have hrsumm_a := real_exp_summable ‖a‖
  have hrsumm_b := real_exp_summable ‖b‖
  have hrsumm2r : Summable fun n =>
      ((‖a‖ + ‖b‖) ^ (n + 2) - ‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) / ((n + 2)! : ℝ) := by
    have h1 : Summable fun n => (‖a‖ + ‖b‖) ^ (n + 2) / ((n + 2)! : ℝ) :=
      hrsumm.comp_injective (fun _ _ h => by omega)
    have h2 : Summable fun n => ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
      hrsumm_a.comp_injective (fun _ _ h => by omega)
    have h3 : Summable fun n => ‖b‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
      hrsumm_b.comp_injective (fun _ _ h => by omega)
    have h4 := (h1.sub h2).sub h3
    refine h4.congr (fun n => ?_); ring
  -- Norm bound on each term of the cross series
  have hterm_norm : ∀ n, ‖((↑(n + 2)! : 𝕂)⁻¹ •
      ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸)‖ ≤
      ((‖a‖ + ‖b‖) ^ (n + 2) - ‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) / ((n + 2)! : ℝ) := by
    intro n
    rw [norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left (norm_pow_add_sub_pow_sub_pow a b (n + 2) (by omega))
    positivity
  -- Summability of norms
  have hnsumm : Summable fun n =>
      ‖((↑(n + 2)! : 𝕂)⁻¹ • ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸)‖ :=
    hrsumm2r.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_norm
  -- Main estimate
  rw [cross_eq]
  calc ‖∑' n, ((↑(n + 2)! : 𝕂)⁻¹ •
        ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸)‖
      ≤ ∑' n, ‖((↑(n + 2)! : 𝕂)⁻¹ •
        ((a + b) ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2)) : 𝔸)‖ :=
        norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ((‖a‖ + ‖b‖) ^ (n + 2) - ‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) /
        ((n + 2)! : ℝ) :=
        hnsumm.tsum_le_tsum hterm_norm hrsumm2r
    _ = (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
        -- Step 3: Evaluate the real tsum
        -- ∑'_n ((s+t)^(n+2) - s^(n+2) - t^(n+2)) / (n+2)!
        -- = (exp(s+t) - 1 - (s+t)) - (exp(s) - 1 - s) - (exp(t) - 1 - t)
        -- = exp(s+t) - exp(s) - exp(t) + 1
        -- = (exp(s) - 1)(exp(t) - 1)   [by exp_add and ring]
        have hrsumm1_ab : Summable fun n => (‖a‖ + ‖b‖) ^ (n + 1) / ((n + 1)! : ℝ) :=
          hrsumm.comp_injective (fun _ _ h => by omega)
        have hrsumm2_ab : Summable fun n => (‖a‖ + ‖b‖) ^ (n + 2) / ((n + 2)! : ℝ) :=
          hrsumm.comp_injective (fun _ _ h => by omega)
        have hrsumm1_a : Summable fun n => ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) :=
          hrsumm_a.comp_injective (fun _ _ h => by omega)
        have hrsumm2_a : Summable fun n => ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
          hrsumm_a.comp_injective (fun _ _ h => by omega)
        have hrsumm1_b : Summable fun n => ‖b‖ ^ (n + 1) / ((n + 1)! : ℝ) :=
          hrsumm_b.comp_injective (fun _ _ h => by omega)
        have hrsumm2_b : Summable fun n => ‖b‖ ^ (n + 2) / ((n + 2)! : ℝ) :=
          hrsumm_b.comp_injective (fun _ _ h => by omega)
        -- Rewrite the tsum by splitting
        have split_tsum :
            (∑' n, ((‖a‖ + ‖b‖) ^ (n + 2) - ‖a‖ ^ (n + 2) - ‖b‖ ^ (n + 2)) /
              ((n + 2)! : ℝ)) =
            (∑' n, (‖a‖ + ‖b‖) ^ (n + 2) / ((n + 2)! : ℝ)) -
            (∑' n, ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ)) -
            (∑' n, ‖b‖ ^ (n + 2) / ((n + 2)! : ℝ)) := by
          rw [← hrsumm2_ab.tsum_sub hrsumm2_a,
              ← (hrsumm2_ab.sub hrsumm2_a).tsum_sub hrsumm2_b]
          congr 1; ext n; ring
        rw [split_tsum]
        -- Each ∑'_n x^(n+2)/(n+2)! = exp(x) - 1 - x
        have eval_ab : ∑' n, (‖a‖ + ‖b‖) ^ (n + 2) / ((n + 2)! : ℝ) =
            Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by
          rw [real_exp_eq_tsum, hrsumm.tsum_eq_zero_add]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
          rw [hrsumm1_ab.tsum_eq_zero_add]
          simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
          ring
        have eval_a : ∑' n, ‖a‖ ^ (n + 2) / ((n + 2)! : ℝ) =
            Real.exp ‖a‖ - 1 - ‖a‖ := by
          rw [real_exp_eq_tsum, hrsumm_a.tsum_eq_zero_add]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
          rw [hrsumm1_a.tsum_eq_zero_add]
          simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
          ring
        have eval_b : ∑' n, ‖b‖ ^ (n + 2) / ((n + 2)! : ℝ) =
            Real.exp ‖b‖ - 1 - ‖b‖ := by
          rw [real_exp_eq_tsum, hrsumm_b.tsum_eq_zero_add]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
          rw [hrsumm1_b.tsum_eq_zero_add]
          simp only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
          ring
        rw [eval_ab, eval_a, eval_b, Real.exp_add]
        ring

include 𝕂 in
/-- **Key estimate**: `‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`.
    This is the hardest lemma in the formalization. -/
theorem norm_exp_mul_exp_sub_exp_add' (a b : 𝔸) :
    ‖exp a * exp b - exp (a + b)‖ ≤
      2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
  -- Step 1: Algebraic identity
  have algebraic_id : exp a * exp b - exp (a + b) =
      (exp a - 1) * (exp b - 1) -
      (exp (a + b) - exp a - exp b + 1) := by noncomm_ring
  rw [algebraic_id]
  -- Step 2: Triangle inequality + bound each part
  have h_part1 : ‖(exp a - 1) * (exp b - 1)‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
    calc ‖(exp a - 1) * (exp b - 1)‖
        ≤ ‖exp a - 1‖ * ‖exp b - 1‖ := norm_mul_le _ _
      _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) := by
          apply mul_le_mul
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) a
          · exact norm_exp_sub_one_le (𝕂 := 𝕂) b
          · exact norm_nonneg _
          · linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
  have h_part2 : ‖exp (a + b) - exp a - exp b + 1‖ ≤
      (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) :=
    norm_exp_cross_term_le (𝕂 := 𝕂) a b
  -- Step 3: Combine via triangle inequality
  have h_sum : ‖(exp a - 1) * (exp b - 1) -
      (exp (a + b) - exp a - exp b + 1)‖ ≤
      2 * ((Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1)) := by
    calc ‖(exp a - 1) * (exp b - 1) -
          (exp (a + b) - exp a - exp b + 1)‖
        ≤ ‖(exp a - 1) * (exp b - 1)‖ +
          ‖exp (a + b) - exp a - exp b + 1‖ := norm_sub_le _ _
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
    ‖exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) -
     exp ((n : 𝕂)⁻¹ • (A + B))‖ ≤
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
  calc ‖exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) -
        exp ((n : 𝕂)⁻¹ • A + (n : 𝕂)⁻¹ • B)‖
      ≤ 2 * (‖A‖ / ↑n) * (‖B‖ / ↑n) * Real.exp (‖A‖ / ↑n + ‖B‖ / ↑n) := h_C1
    _ = 2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / ↑n) := by
        have hn_ne_zero : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        field_simp
