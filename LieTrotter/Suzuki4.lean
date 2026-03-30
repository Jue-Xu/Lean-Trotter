/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourth-Order Suzuki Formula

The fourth-order Suzuki formula S₄ composes five symmetric Strang steps
and converges at O(1/n²). The optimal parameter choice yields O(1/n⁴)
via Suzuki's parity cancellation, deferred to future work.
-/

import LieTrotter.StrangSplitting

open Filter Topology NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Definition

S₄(n) is defined as a product of five Strang-type steps with coefficients
`[p, p, 1-4p, p, p]` that sum to 1. Each step `S₂(c, n)` is
`exp(cA/(2n)) · exp(cB/n) · exp(cA/(2n))`.
-/

/-- The Strang step `S₂(c, n)`. Parameterized by coefficient `c : 𝕂` and step count `n`. -/
noncomputable def strangStep (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (c : 𝕂) (n : ℕ) : 𝔸 :=
  exp ((2 * (n : 𝕂))⁻¹ • (c • A)) * exp ((n : 𝕂)⁻¹ • (c • B)) *
  exp ((2 * (n : 𝕂))⁻¹ • (c • A))

/-- The Suzuki S₄ step: five Strang steps with coefficients `[p, p, 1-4p, p, p]`. -/
noncomputable def suzuki4Step (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (p : 𝕂) (n : ℕ) : 𝔸 :=
  strangStep 𝕂 A B p n * strangStep 𝕂 A B p n *
  strangStep 𝕂 A B (1 - 4 * p) n *
  strangStep 𝕂 A B p n * strangStep 𝕂 A B p n

/-!
## Cubic step error for a single Strang step with coefficient c

This is a direct application of `norm_exp_mul_exp_mul_exp_sub_exp_add_cubic`
to the scaled operators `cA` and `cB`.
-/

omit [NormOneClass 𝔸] in
include 𝕂 in
private lemma strangStep_target_eq (A B : 𝔸) (c : 𝕂) (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ • (c • A) + (n : 𝕂)⁻¹ • (c • B) + (2 * (n : 𝕂))⁻¹ • (c • A) =
      (n : 𝕂)⁻¹ • (c • A + c • B) := by
  have h : (2 * (n : 𝕂))⁻¹ • (c • A) + (2 * (n : 𝕂))⁻¹ • (c • A) = (n : 𝕂)⁻¹ • (c • A) := by
    rw [← add_smul]; congr 1
    have hn_ne : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp; norm_num
  rw [smul_add]
  have : (2 * (n : 𝕂))⁻¹ • (c • A) + (n : 𝕂)⁻¹ • (c • B) + (2 * (n : 𝕂))⁻¹ • (c • A) =
      ((2 * (n : 𝕂))⁻¹ • (c • A) + (2 * (n : 𝕂))⁻¹ • (c • A)) + (n : 𝕂)⁻¹ • (c • B) := by
    abel
  rw [this, h]

include 𝕂 in
private theorem strangStep_cubic_error (A B : 𝔸) (c : 𝕂) (n : ℕ) (hn : 0 < n) :
    ‖strangStep 𝕂 A B c n - exp ((n : 𝕂)⁻¹ • (c • A + c • B))‖ ≤
      (7 / 4 * ‖c • A‖ ^ 2 * ‖c • B‖ + 3 / 2 * ‖c • A‖ * ‖c • B‖ ^ 2 +
       3 / 8 * ‖c • A‖ ^ 3) /
        (n : ℝ) ^ 3 * Real.exp ((‖c • A‖ + ‖c • B‖) / n) := by
  have hsmul := strangStep_target_eq (𝕂 := 𝕂) A B c n hn
  show ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A)) * exp ((n : 𝕂)⁻¹ • (c • B)) *
      exp ((2 * (n : 𝕂))⁻¹ • (c • A)) - exp ((n : 𝕂)⁻¹ • (c • A + c • B))‖ ≤ _
  rw [← hsmul]
  set a := (2 * (n : 𝕂))⁻¹ • (c • A)
  set b := (n : 𝕂)⁻¹ • (c • B)
  have h_gen := norm_exp_mul_exp_mul_exp_sub_exp_add_cubic (𝕂 := 𝕂) a b
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have norm_a : ‖a‖ = ‖c • A‖ / (2 * n) := by
    show ‖(2 * (n : 𝕂))⁻¹ • (c • A)‖ = _; rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
  have norm_b : ‖b‖ = ‖c • B‖ / n := by
    show ‖(n : 𝕂)⁻¹ • (c • B)‖ = _; rw [norm_smul, norm_inv_n, div_eq_inv_mul]
  rw [norm_a, norm_b] at h_gen
  calc ‖exp a * exp b * exp a - exp (a + b + a)‖
      ≤ _ := h_gen
    _ = _ := by field_simp; ring

/-!
## Norm bounds
-/

include 𝕂 in
private lemma norm_strangStep_le (A B : 𝔸) (c : 𝕂) (n : ℕ) (hn : 0 < n) :
    ‖strangStep 𝕂 A B c n‖ ≤ Real.exp ((‖c • A‖ + ‖c • B‖) / n) := by
  show ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A)) * exp ((n : 𝕂)⁻¹ • (c • B)) *
      exp ((2 * (n : 𝕂))⁻¹ • (c • A))‖ ≤ _
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  calc ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A)) * exp ((n : 𝕂)⁻¹ • (c • B)) *
        exp ((2 * (n : 𝕂))⁻¹ • (c • A))‖
      ≤ (Real.exp ‖(2 * (n : 𝕂))⁻¹ • (c • A)‖ * Real.exp ‖(n : 𝕂)⁻¹ • (c • B)‖) *
        Real.exp ‖(2 * (n : 𝕂))⁻¹ • (c • A)‖ := by
        calc _ ≤ ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A)) * exp ((n : 𝕂)⁻¹ • (c • B))‖ *
              ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A))‖ := norm_mul_le _ _
          _ ≤ (‖exp ((2 * (n : 𝕂))⁻¹ • (c • A))‖ * ‖exp ((n : 𝕂)⁻¹ • (c • B))‖) *
              ‖exp ((2 * (n : 𝕂))⁻¹ • (c • A))‖ := by gcongr; exact norm_mul_le _ _
          _ ≤ _ := by
              gcongr <;> exact norm_exp_le (𝕂 := 𝕂) _
    _ = Real.exp (‖(2 * (n : 𝕂))⁻¹ • (c • A)‖ + ‖(n : 𝕂)⁻¹ • (c • B)‖ +
        ‖(2 * (n : 𝕂))⁻¹ • (c • A)‖) := by
        rw [Real.exp_add, Real.exp_add]
    _ = Real.exp (‖c • A‖ / (2 * ↑n) + ‖c • B‖ / ↑n + ‖c • A‖ / (2 * ↑n)) := by
        simp only [norm_smul, norm_inv_2n, norm_inv_n, div_eq_inv_mul]
    _ = Real.exp ((‖c • A‖ + ‖c • B‖) / ↑n) := by congr 1; field_simp; ring

include 𝕂 in
private lemma norm_strangStep_le' (A B : 𝔸) (c : 𝕂) (n : ℕ) (hn : 0 < n)
    (hc : ‖c‖ ≤ 1) :
    ‖strangStep 𝕂 A B c n‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
  calc ‖strangStep 𝕂 A B c n‖
      ≤ Real.exp ((‖c • A‖ + ‖c • B‖) / n) :=
        norm_strangStep_le (𝕂 := 𝕂) A B c n hn
    _ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
        gcongr
        · exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)
        · exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)

include 𝕂 in
private lemma norm_strangStep_sub_exp_le (A B : 𝔸) (c : 𝕂) (n : ℕ) (hn : 0 < n)
    (hc : ‖c‖ ≤ 1) :
    ‖strangStep 𝕂 A B c n - exp ((n : 𝕂)⁻¹ • (c • A + c • B))‖ ≤
      (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 +
       3 / 8 * ‖A‖ ^ 3) /
        (n : ℝ) ^ 3 * Real.exp ((‖A‖ + ‖B‖) / n) := by
  have hcA : ‖c • A‖ ≤ ‖A‖ :=
    (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)
  have hcB : ‖c • B‖ ≤ ‖B‖ :=
    (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)
  have hcA2 : ‖c • A‖ ^ 2 ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcA 2
  have hcA3 : ‖c • A‖ ^ 3 ≤ ‖A‖ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hcA 3
  have hcB2 : ‖c • B‖ ^ 2 ≤ ‖B‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcB 2
  calc _ ≤ (7 / 4 * ‖c • A‖ ^ 2 * ‖c • B‖ + 3 / 2 * ‖c • A‖ * ‖c • B‖ ^ 2 +
         3 / 8 * ‖c • A‖ ^ 3) /
          (n : ℝ) ^ 3 * Real.exp ((‖c • A‖ + ‖c • B‖) / n) :=
        strangStep_cubic_error (𝕂 := 𝕂) A B c n hn
    _ ≤ (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 +
         3 / 8 * ‖A‖ ^ 3) /
          (n : ℝ) ^ 3 * Real.exp ((‖A‖ + ‖B‖) / n) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [norm_nonneg A, norm_nonneg B]
      · gcongr

include 𝕂 in
private lemma norm_exp_smul_AB_le (A B : 𝔸) (c : 𝕂)
    (n : ℕ) (hc : ‖c‖ ≤ 1) :
    ‖exp ((n : 𝕂)⁻¹ • (c • A + c • B))‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
  calc ‖exp ((n : 𝕂)⁻¹ • (c • A + c • B))‖
      ≤ Real.exp ‖(n : 𝕂)⁻¹ • (c • A + c • B)‖ := norm_exp_le (𝕂 := 𝕂) _
    _ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
        gcongr
        calc ‖(n : 𝕂)⁻¹ • (c • A + c • B)‖ ≤ ‖(n : 𝕂)⁻¹‖ * ‖c • A + c • B‖ :=
              norm_smul_le _ _
          _ ≤ ‖(n : 𝕂)⁻¹‖ * (‖c • A‖ + ‖c • B‖) := by gcongr; exact norm_add_le _ _
          _ ≤ ‖(n : 𝕂)⁻¹‖ * (‖A‖ + ‖B‖) := by
              gcongr
              · exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)
              · exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hc)
          _ = (‖A‖ + ‖B‖) / n := by
              rw [norm_inv, RCLike.norm_natCast, inv_mul_eq_div]

/-!
## Commuting exponentials
-/

include 𝕂 in
private lemma exp_smul_mul_exp_smul (c₁ c₂ : 𝕂) (X : 𝔸) :
    exp (c₁ • X) * exp (c₂ • X) = exp ((c₁ + c₂) • X) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ 𝕂 𝔸
  have hcomm : Commute (c₁ • X) (c₂ • X) := by
    show c₁ • X * (c₂ • X) = c₂ • X * (c₁ • X)
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c₁ c₂]
  rw [← exp_add_of_commute hcomm, add_smul]

/-!
## S₄ step error: O(1/n³)

The five Strang sub-steps have cubic errors, and the exact exponential targets
commute (all scalar multiples of `A + B`), so their product = `exp((A+B)/n)`.
-/

set_option maxHeartbeats 800000 in
include 𝕂 in
theorem suzuki4_step_error (A B : 𝔸) (p : ℝ) (hp : 0 < p) (hp4 : p < 1 / 4)
    (n : ℕ) (hn : 0 < n) :
    ‖suzuki4Step 𝕂 A B (↑p) n - exp ((n : 𝕂)⁻¹ • (A + B))‖ ≤
      19 * (‖A‖ + ‖B‖) ^ 3 /
        (n : ℝ) ^ 3 * Real.exp (5 * (‖A‖ + ‖B‖) / n) := by
  set s := ‖A‖ + ‖B‖
  set AB := A + B
  set K₀ := 7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 + 3 / 8 * ‖A‖ ^ 3
  set ε₀ := K₀ / (n : ℝ) ^ 3 * Real.exp (s / n)
  set M := Real.exp (s / n)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hp14 : 0 < 1 - 4 * p := by linarith
  -- Norm of coefficients
  have norm_p : ‖(↑p : 𝕂)‖ ≤ 1 := by
    rw [show (↑p : 𝕂) = RCLike.ofReal p from rfl, RCLike.norm_ofReal,
      abs_of_nonneg hp.le]; linarith
  have norm_q : ‖(1 : 𝕂) - 4 * (↑p : 𝕂)‖ ≤ 1 := by
    rw [show (1 : 𝕂) - 4 * (↑p : 𝕂) = (↑(1 - 4 * p) : 𝕂) from by push_cast; ring,
      show (↑(1 - 4 * p) : 𝕂) = RCLike.ofReal (1 - 4 * p) from rfl,
      RCLike.norm_ofReal, abs_of_nonneg hp14.le]; linarith
  set cp : 𝕂 := ↑p
  set cq : 𝕂 := 1 - 4 * cp
  -- The five steps and their targets
  set P := strangStep 𝕂 A B cp n
  set P' := strangStep 𝕂 A B cq n
  -- Target exponentials: exp(n⁻¹ • (c • A + c • B)) for various c
  -- Using c • A + c • B = c • (A + B) would require smul_add, but we keep it expanded.
  set E := exp ((n : 𝕂)⁻¹ • (cp • A + cp • B))
  set E' := exp ((n : 𝕂)⁻¹ • (cq • A + cq • B))
  have hS4 : suzuki4Step 𝕂 A B cp n = P * P * P' * P * P := rfl
  -- Exact product: E*E*E'*E*E = exp(n⁻¹ • (A + B))
  have coeff_sum : cp + cp + cq + cp + cp = (1 : 𝕂) := by
    show ↑p + ↑p + ((1 : 𝕂) - 4 * ↑p) + ↑p + ↑p = 1; ring
  -- E = exp(n⁻¹ • (cp • A + cp • B)) = exp((n⁻¹ * cp) • (A + B)) by smul algebra
  have hE_rw : ∀ c : 𝕂, exp ((n : 𝕂)⁻¹ • (c • A + c • B)) =
      exp (((n : 𝕂)⁻¹ * c) • AB) := by
    intro c; congr 1; rw [← smul_add, smul_smul]
  have exact_prod : E * E * E' * E * E = exp ((n : 𝕂)⁻¹ • AB) := by
    simp only [E, E', hE_rw]
    rw [exp_smul_mul_exp_smul (𝕂 := 𝕂)]
    rw [exp_smul_mul_exp_smul (𝕂 := 𝕂)]
    rw [exp_smul_mul_exp_smul (𝕂 := 𝕂)]
    rw [exp_smul_mul_exp_smul (𝕂 := 𝕂)]
    -- After rewrites, goal: (n⁻¹*cp + n⁻¹*cp + n⁻¹*cq + n⁻¹*cp + n⁻¹*cp) • AB = n⁻¹ • AB
    -- Factor out n⁻¹ and use coeff_sum
    have hcoeff : (n : 𝕂)⁻¹ * cp + (n : 𝕂)⁻¹ * cp + (n : 𝕂)⁻¹ * cq + (n : 𝕂)⁻¹ * cp +
        (n : 𝕂)⁻¹ * cp = (n : 𝕂)⁻¹ := by
      calc _ = (n : 𝕂)⁻¹ * (cp + cp + cq + cp + cp) := by ring
        _ = (n : 𝕂)⁻¹ * 1 := by rw [coeff_sum]
        _ = (n : 𝕂)⁻¹ := mul_one _
    rw [hcoeff]
  -- Individual error and norm bounds
  have err_P : ‖P - E‖ ≤ ε₀ := norm_strangStep_sub_exp_le (𝕂 := 𝕂) A B cp n hn norm_p
  have err_P' : ‖P' - E'‖ ≤ ε₀ := norm_strangStep_sub_exp_le (𝕂 := 𝕂) A B cq n hn norm_q
  have hP : ‖P‖ ≤ M := norm_strangStep_le' (𝕂 := 𝕂) A B cp n hn norm_p
  have hP' : ‖P'‖ ≤ M := norm_strangStep_le' (𝕂 := 𝕂) A B cq n hn norm_q
  have hE : ‖E‖ ≤ M := norm_exp_smul_AB_le (𝕂 := 𝕂) A B cp n norm_p
  have hE' : ‖E'‖ ≤ M := norm_exp_smul_AB_le (𝕂 := 𝕂) A B cq n norm_q
  have hM_pos : 0 < M := Real.exp_pos _
  -- 5-step telescope: peel off one factor at a time
  rw [hS4, ← exact_prod]
  -- ‖PP - EE‖ ≤ 2εM
  have h2 : ‖P * P - E * E‖ ≤ 2 * ε₀ * M := by
    calc ‖P * P - E * E‖ = ‖P * (P - E) + (P - E) * E‖ := by congr 1; noncomm_ring
      _ ≤ ‖P‖ * ‖P - E‖ + ‖P - E‖ * ‖E‖ := by
          calc _ ≤ ‖P * (P - E)‖ + ‖(P - E) * E‖ := norm_add_le _ _
            _ ≤ _ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ M * ε₀ + ε₀ * M := by gcongr
      _ = 2 * ε₀ * M := by ring
  -- ‖PPP' - EEE'‖ ≤ 3εM²
  have h3 : ‖P * P * P' - E * E * E'‖ ≤ 3 * ε₀ * M ^ 2 := by
    calc ‖P * P * P' - E * E * E'‖
        = ‖(P * P) * (P' - E') + (P * P - E * E) * E'‖ := by congr 1; noncomm_ring
      _ ≤ ‖P * P‖ * ‖P' - E'‖ + ‖P * P - E * E‖ * ‖E'‖ := by
          calc _ ≤ ‖(P * P) * (P' - E')‖ + ‖(P * P - E * E) * E'‖ := norm_add_le _ _
            _ ≤ _ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ (‖P‖ * ‖P‖) * ε₀ + (2 * ε₀ * M) * M := by
          gcongr; exact norm_mul_le _ _
      _ ≤ (M * M) * ε₀ + (2 * ε₀ * M) * M := by gcongr
      _ = 3 * ε₀ * M ^ 2 := by ring
  -- ‖PPP'P - EEE'E‖ ≤ 4εM³
  have h4 : ‖P * P * P' * P - E * E * E' * E‖ ≤ 4 * ε₀ * M ^ 3 := by
    calc ‖P * P * P' * P - E * E * E' * E‖
        = ‖(P * P * P') * (P - E) + (P * P * P' - E * E * E') * E‖ := by
          congr 1; noncomm_ring
      _ ≤ ‖P * P * P'‖ * ‖P - E‖ + ‖P * P * P' - E * E * E'‖ * ‖E‖ := by
          calc _ ≤ ‖(P * P * P') * (P - E)‖ + ‖(P * P * P' - E * E * E') * E‖ :=
                norm_add_le _ _
            _ ≤ _ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ (‖P * P‖ * ‖P'‖) * ε₀ + (3 * ε₀ * M ^ 2) * M := by
          gcongr; exact norm_mul_le _ _
      _ ≤ ((‖P‖ * ‖P‖) * M) * ε₀ + (3 * ε₀ * M ^ 2) * M := by
          gcongr; exact norm_mul_le _ _
      _ ≤ ((M * M) * M) * ε₀ + (3 * ε₀ * M ^ 2) * M := by gcongr
      _ = 4 * ε₀ * M ^ 3 := by ring
  -- ‖PPP'PP - EEE'EE‖ ≤ 5εM⁴
  calc ‖P * P * P' * P * P - E * E * E' * E * E‖
      = ‖(P * P * P' * P) * (P - E) + (P * P * P' * P - E * E * E' * E) * E‖ := by
        congr 1; noncomm_ring
    _ ≤ ‖P * P * P' * P‖ * ‖P - E‖ + ‖P * P * P' * P - E * E * E' * E‖ * ‖E‖ := by
        calc _ ≤ ‖(P * P * P' * P) * (P - E)‖ +
              ‖(P * P * P' * P - E * E * E' * E) * E‖ := norm_add_le _ _
          _ ≤ _ := by gcongr <;> exact norm_mul_le _ _
    _ ≤ (‖P * P * P'‖ * ‖P‖) * ε₀ + (4 * ε₀ * M ^ 3) * M := by
        gcongr; exact norm_mul_le _ _
    _ ≤ ((‖P * P‖ * ‖P'‖) * M) * ε₀ + (4 * ε₀ * M ^ 3) * M := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (((‖P‖ * ‖P‖) * M) * M) * ε₀ + (4 * ε₀ * M ^ 3) * M := by
        gcongr; exact norm_mul_le _ _
    _ ≤ (((M * M) * M) * M) * ε₀ + (4 * ε₀ * M ^ 3) * M := by gcongr
    _ = 5 * ε₀ * M ^ 4 := by ring
    _ = 5 * K₀ / (n : ℝ) ^ 3 * M ^ 5 := by ring
    _ = 5 * K₀ / (n : ℝ) ^ 3 * Real.exp (5 * (s / n)) := by
        congr 1; rw [← Real.exp_nat_mul]; norm_num
    _ = 5 * K₀ / (n : ℝ) ^ 3 * Real.exp (5 * s / n) := by congr 1; ring
    _ ≤ 19 * s ^ 3 / (n : ℝ) ^ 3 * Real.exp (5 * s / n) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        -- 5K₀ ≤ 19s³: since K₀ ≤ (7/4+3/2+3/8)s³ = 29/8·s³ and 5·29/8 = 145/8 < 19
        have hA := norm_nonneg A; have hB := norm_nonneg B
        have hA_le : ‖A‖ ≤ s := le_add_of_nonneg_right hB
        have hB_le : ‖B‖ ≤ s := le_add_of_nonneg_left hA
        have h1 : ‖A‖ ^ 2 * ‖B‖ ≤ s ^ 3 := by
          calc ‖A‖ ^ 2 * ‖B‖ ≤ s ^ 2 * s :=
                mul_le_mul (pow_le_pow_left₀ hA hA_le 2) hB_le hB (by positivity)
            _ = s ^ 3 := by ring
        have h2 : ‖A‖ * ‖B‖ ^ 2 ≤ s ^ 3 := by
          calc ‖A‖ * ‖B‖ ^ 2 ≤ s * s ^ 2 :=
                mul_le_mul hA_le (pow_le_pow_left₀ hB hB_le 2) (by positivity) (by positivity)
            _ = s ^ 3 := by ring
        have h3 : ‖A‖ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hA hA_le 3
        calc 5 * K₀ = 35 / 4 * (‖A‖ ^ 2 * ‖B‖) + 15 / 2 * (‖A‖ * ‖B‖ ^ 2) +
            15 / 8 * ‖A‖ ^ 3 := by ring
          _ ≤ 35 / 4 * s ^ 3 + 15 / 2 * s ^ 3 + 15 / 8 * s ^ 3 := by nlinarith
          _ = 145 / 8 * s ^ 3 := by ring
          _ ≤ 19 * s ^ 3 := by nlinarith [sq_nonneg s]

/-!
## Norm bound for S₄
-/

include 𝕂 in
private lemma norm_suzuki4Step_le (A B : 𝔸) (p : ℝ) (hp : 0 < p) (hp4 : p < 1 / 4)
    (n : ℕ) (hn : 0 < n) :
    ‖suzuki4Step 𝕂 A B (↑p) n‖ ≤ Real.exp (5 * (‖A‖ + ‖B‖) / n) := by
  have hp14 : 0 < 1 - 4 * p := by linarith
  have norm_p : ‖(↑p : 𝕂)‖ ≤ 1 := by
    rw [show (↑p : 𝕂) = RCLike.ofReal p from rfl, RCLike.norm_ofReal,
      abs_of_nonneg hp.le]; linarith
  have norm_q : ‖(1 : 𝕂) - 4 * (↑p : 𝕂)‖ ≤ 1 := by
    rw [show (1 : 𝕂) - 4 * (↑p : 𝕂) = (↑(1 - 4 * p) : 𝕂) from by push_cast; ring,
      show (↑(1 - 4 * p) : 𝕂) = RCLike.ofReal (1 - 4 * p) from rfl,
      RCLike.norm_ofReal, abs_of_nonneg hp14.le]; linarith
  set cp : 𝕂 := ↑p; set cq : 𝕂 := 1 - 4 * cp
  set M := Real.exp ((‖A‖ + ‖B‖) / n)
  set S₁ := strangStep 𝕂 A B cp n; set S₃ := strangStep 𝕂 A B cq n
  show ‖S₁ * S₁ * S₃ * S₁ * S₁‖ ≤ _
  have h1 : ‖S₁‖ ≤ M := norm_strangStep_le' (𝕂 := 𝕂) A B cp n hn norm_p
  have h3 : ‖S₃‖ ≤ M := norm_strangStep_le' (𝕂 := 𝕂) A B cq n hn norm_q
  calc ‖S₁ * S₁ * S₃ * S₁ * S₁‖
      ≤ ‖S₁ * S₁ * S₃ * S₁‖ * ‖S₁‖ := norm_mul_le _ _
    _ ≤ ‖S₁ * S₁ * S₃ * S₁‖ * M := by gcongr
    _ ≤ (‖S₁ * S₁ * S₃‖ * ‖S₁‖) * M := by gcongr; exact norm_mul_le _ _
    _ ≤ (‖S₁ * S₁ * S₃‖ * M) * M := by gcongr
    _ ≤ ((‖S₁ * S₁‖ * ‖S₃‖) * M) * M := by gcongr; exact norm_mul_le _ _
    _ ≤ ((‖S₁ * S₁‖ * M) * M) * M := by gcongr
    _ ≤ (((‖S₁‖ * ‖S₁‖) * M) * M) * M := by gcongr; exact norm_mul_le _ _
    _ ≤ (((M * M) * M) * M) * M := by gcongr
    _ = M ^ 5 := by ring
    _ = Real.exp (5 * ((‖A‖ + ‖B‖) / n)) := by
        rw [← Real.exp_nat_mul]; norm_num
    _ = Real.exp (5 * (‖A‖ + ‖B‖) / n) := by congr 1; ring

/-!
## Convergence rate: O(1/n²)
-/

include 𝕂 in
theorem suzuki4_error_rate_sq (A B : 𝔸) (p : ℝ) (hp : 0 < p) (hp4 : p < 1 / 4) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖(suzuki4Step 𝕂 A B (↑p) n) ^ n - exp (A + B)‖ ≤ C / n ^ 2 := by
  set s := ‖A‖ + ‖B‖
  set K := 19 * s ^ 3
  refine ⟨K * Real.exp (6 * s) + 1, by positivity, ?_⟩
  intro n hn
  have hpow : exp (A + B) = (exp ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (𝕂 := 𝕂) (A + B) n hn).symm
  rw [hpow]
  set S := suzuki4Step 𝕂 A B (↑p) n
  set Q := exp ((n : 𝕂)⁻¹ • (A + B))
  have h_telesc := norm_pow_sub_pow_le' S Q n
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs_nonneg : 0 ≤ s := by positivity
  -- Step error
  have h_step : ‖S - Q‖ ≤ K / (n : ℝ) ^ 3 * Real.exp (5 * s / n) :=
    suzuki4_step_error (𝕂 := 𝕂) A B p hp hp4 n hn
  -- Max norm bound
  have h_S_norm : ‖S‖ ≤ Real.exp (5 * s / n) :=
    norm_suzuki4Step_le (𝕂 := 𝕂) A B p hp hp4 n hn
  have h_Q_norm : ‖Q‖ ≤ Real.exp (s / n) := by
    calc ‖Q‖ ≤ Real.exp ‖(n : 𝕂)⁻¹ • (A + B)‖ := norm_exp_le (𝕂 := 𝕂) _
      _ ≤ Real.exp (s / n) := by
        gcongr
        calc ‖(n : 𝕂)⁻¹ • (A + B)‖ ≤ ‖(n : 𝕂)⁻¹‖ * ‖A + B‖ := norm_smul_le _ _
          _ ≤ (↑n)⁻¹ * s := by
              rw [norm_inv, RCLike.norm_natCast]; gcongr; exact norm_add_le A B
          _ = s / n := inv_mul_eq_div _ _
  have h_Q_le : ‖Q‖ ≤ Real.exp (5 * s / n) :=
    h_Q_norm.trans (by gcongr; linarith [div_nonneg hs_nonneg hn_pos.le])
  have h_max : max ‖S‖ ‖Q‖ ≤ Real.exp (5 * s / n) := max_le h_S_norm h_Q_le
  -- exp(5s/n)^n = exp(5s), and exp(5s/n) * exp(5s) ≤ exp(6s)
  have h_exp_combine : Real.exp (5 * s / n) * Real.exp (5 * s / n) ^ (n - 1) ≤
      Real.exp (6 * s) := by
    calc Real.exp (5 * s / n) * Real.exp (5 * s / n) ^ (n - 1)
        = Real.exp (5 * s / n) ^ n := by
          cases n with | zero => omega | succ m => simp [pow_succ']
      _ = Real.exp (5 * s) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
      _ ≤ Real.exp (6 * s) := by gcongr; linarith
  calc ‖S ^ n - Q ^ n‖
      ≤ n * ‖S - Q‖ * (max ‖S‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (K / (n : ℝ) ^ 3 * Real.exp (5 * s / n)) *
        (Real.exp (5 * s / n)) ^ (n - 1) := by gcongr
    _ = K / (↑n) ^ 2 * (Real.exp (5 * s / n) * Real.exp (5 * s / n) ^ (n - 1)) := by
        field_simp
    _ ≤ K / (↑n) ^ 2 * Real.exp (6 * s) := by gcongr
    _ = K * Real.exp (6 * s) / (↑n) ^ 2 := by ring
    _ ≤ (K * Real.exp (6 * s) + 1) / (↑n) ^ 2 := by
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr (le_add_of_nonneg_right zero_le_one)

/-!
## Main theorem: Convergence
-/

include 𝕂 in
/-- **The Fourth-Order Suzuki Product Formula (Phase 1).**
    For any `A, B` in a complete normed algebra and `0 < p < 1/4`,
    `(S₄(1/n))^n → exp(A+B)` as `n → ∞` at rate O(1/n²).

    The choice `p = 1/(4 - 4^{1/3})` yields O(1/n⁴) via Suzuki's
    parity cancellation (deferred). -/
theorem suzuki4_convergence (A B : 𝔸) (p : ℝ) (hp : 0 < p) (hp4 : p < 1 / 4) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Step 𝕂 A B (↑p) n) ^ n)
      atTop (nhds (exp (A + B))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ := suzuki4_error_rate_sq (𝕂 := 𝕂) A B p hp hp4
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  calc ‖(suzuki4Step 𝕂 A B (↑p) n) ^ n - exp (A + B)‖
      ≤ C / n ^ 2 := hC_bound n hn_pos
    _ ≤ C / n := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity)
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ 2 := pow_le_pow_right₀ hn_cast (by omega)
    _ ≤ C / (N + 1) := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity : (0:ℝ) < N + 1)
        exact_mod_cast hn
    _ ≤ C / N.succ := by norm_cast
    _ < ε := by
        rw [div_lt_iff₀' (by positivity : (0 : ℝ) < ↑N.succ)]
        calc C = C / ε * ε := by field_simp
          _ < (N + 1) * ε := by
              exact mul_lt_mul_of_pos_right (hN.trans (by linarith)) hε
          _ = ↑N.succ * ε := by push_cast; ring
