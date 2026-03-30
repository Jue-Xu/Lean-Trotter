/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Operator Symmetric Lie-Trotter (Strang Splitting)

Generalization of the two-operator Strang splitting to a list of operators:
  `(symmetricProd n [A₁,...,Aₘ])^n → exp(∑ᵢ Aᵢ)` as `n → ∞`

with O(1/n²) convergence rate, compared to O(1/n) for the first-order formula.
-/

import LieTrotter.StrangSplitting
import LieTrotter.MultiOperator

open Filter Topology NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Definition: Symmetric (palindromic) product

`symmetricProd 𝕂 n [A₁, A₂, ..., Aₘ]`
  = `exp(A₁/(2n)) * exp(A₂/(2n)) * ⋯ * exp(Aₘ₋₁/(2n)) * exp(Aₘ/n) * exp(Aₘ₋₁/(2n)) * ⋯ * exp(A₁/(2n))`

Defined recursively:
- `[]` → `1`
- `[A]` → `exp(A/n)`
- `A :: rest` → `exp(A/(2n)) * symmetricProd n rest * exp(A/(2n))`
-/

noncomputable def symmetricProd (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] (n : ℕ) : List 𝔸 → 𝔸
  | [] => 1
  | [A] => exp ((n : 𝕂)⁻¹ • A)
  | A :: rest => exp ((2 * (n : 𝕂))⁻¹ • A) * symmetricProd 𝕂 n rest * exp ((2 * (n : 𝕂))⁻¹ • A)

/-!
## Auxiliary: Scalar identity for the symmetric splitting

`(2n)⁻¹ • A + (n)⁻¹ • B + (2n)⁻¹ • A = n⁻¹ • (A + B)`

This is proved in `StrangSplitting.lean` as a `private` lemma, so we reprove it here.
-/

omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma half_inv_add_half_inv' (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ + (2 * (n : 𝕂))⁻¹ = (n : 𝕂)⁻¹ := by
  have hn_ne : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2n_ne : (2 : 𝕂) * (n : 𝕂) ≠ 0 := mul_ne_zero two_ne_zero hn_ne
  field_simp; norm_num

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma symmetric_smul_eq' (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      (n : 𝕂)⁻¹ • (A + B) := by
  have h : (2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A = (n : 𝕂)⁻¹ • A := by
    rw [← add_smul, half_inv_add_half_inv' (𝕂 := 𝕂) n hn]
  rw [smul_add]
  have : (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      ((2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A) + (n : 𝕂)⁻¹ • B := by abel
  rw [this, h]

/-!
## Lemma: Uniform norm bound for symmetricProd
-/

include 𝕂 in
lemma norm_symmetricProd_le (As : List 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖symmetricProd 𝕂 n As‖ ≤ Real.exp ((As.map norm).sum / n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  induction As with
  | nil =>
    simp [symmetricProd, norm_one]
  | cons A rest ih =>
    match rest, ih with
    | [], _ =>
      simp only [symmetricProd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      calc ‖exp ((n : 𝕂)⁻¹ • A)‖
          ≤ Real.exp ‖(n : 𝕂)⁻¹ • A‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A‖) := by
            gcongr; exact norm_smul_le _ _
        _ = Real.exp (‖A‖ / n) := by rw [norm_inv_n, inv_mul_eq_div]
    | B :: rest', ih_inner =>
      have ih_rest : ‖symmetricProd 𝕂 n (B :: rest')‖ ≤
          Real.exp (((B :: rest').map norm).sum / n) :=
        ih_inner
      show ‖symmetricProd 𝕂 n (A :: B :: rest')‖ ≤ _
      change ‖exp ((2 * (n : 𝕂))⁻¹ • A) * symmetricProd 𝕂 n (B :: rest') *
          exp ((2 * (n : 𝕂))⁻¹ • A)‖ ≤ _
      set a := (2 * (n : 𝕂))⁻¹ • A
      set S := symmetricProd 𝕂 n (B :: rest')
      have norm_a : ‖a‖ = ‖A‖ / (2 * n) := by
        show ‖(2 * (n : 𝕂))⁻¹ • A‖ = _
        rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
      calc ‖exp a * S * exp a‖
          ≤ ‖exp a * S‖ * ‖exp a‖ := norm_mul_le _ _
        _ ≤ (‖exp a‖ * ‖S‖) * ‖exp a‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ (Real.exp ‖a‖ * ‖S‖) * Real.exp ‖a‖ := by
            gcongr <;> exact norm_exp_le (𝕂 := 𝕂) _
        _ ≤ (Real.exp ‖a‖ * Real.exp (((B :: rest').map norm).sum / n)) *
            Real.exp ‖a‖ := by
            gcongr
        _ = Real.exp (2 * ‖a‖ + ((B :: rest').map norm).sum / n) := by
            rw [show Real.exp ‖a‖ * Real.exp (((B :: rest').map norm).sum / ↑n) *
                Real.exp ‖a‖ = (Real.exp ‖a‖ * Real.exp ‖a‖) *
                Real.exp (((B :: rest').map norm).sum / ↑n) from by ring,
              ← Real.exp_add, show ‖a‖ + ‖a‖ = 2 * ‖a‖ from by ring,
              ← Real.exp_add]
        _ = Real.exp (((A :: B :: rest').map norm).sum / n) := by
            congr 1; simp only [norm_a, List.map_cons, List.sum_cons]; field_simp

/-!
## Step error: Cubic bound for symmetricProd

The main technical lemma: per-step error is O(1/n³).
-/

include 𝕂 in
theorem norm_symmetricProd_sub_exp_smul_sum (As : List 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖symmetricProd 𝕂 n As - exp ((n : 𝕂)⁻¹ • As.sum)‖ ≤
      13 * ((As.map norm).sum) ^ 3 / (n : ℝ) ^ 3 *
        Real.exp ((As.map norm).sum / n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  induction As with
  | nil =>
    simp [symmetricProd, exp_zero, smul_zero]
  | cons A rest ih =>
    match rest, ih with
    | [], _ =>
      -- symmetricProd n [A] = exp(A/n), target = exp(A/n), diff = 0
      simp only [symmetricProd, List.sum_cons, List.sum_nil, add_zero, sub_self, norm_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      positivity
    | B :: rest', ih_inner =>
      -- Inductive step: A :: (B :: rest') where (B :: rest') is nonempty
      have ih_rest : ‖symmetricProd 𝕂 n (B :: rest') -
          exp ((n : 𝕂)⁻¹ • (B :: rest').sum)‖ ≤
          13 * (((B :: rest').map norm).sum) ^ 3 / (n : ℝ) ^ 3 *
            Real.exp ((((B :: rest').map norm).sum) / n) :=
        ih_inner
      -- Unfold symmetricProd first, then set abbreviations
      show ‖symmetricProd 𝕂 n (A :: B :: rest') - exp ((n : 𝕂)⁻¹ • (A :: B :: rest').sum)‖ ≤ _
      change ‖exp ((2 * (n : 𝕂))⁻¹ • A) * symmetricProd 𝕂 n (B :: rest') *
          exp ((2 * (n : 𝕂))⁻¹ • A) - exp ((n : 𝕂)⁻¹ • (A :: B :: rest').sum)‖ ≤ _
      -- Setup
      set a := (2 * (n : 𝕂))⁻¹ • A
      set S := symmetricProd 𝕂 n (B :: rest')
      set B_exp := exp ((n : 𝕂)⁻¹ • (B :: rest').sum)
      set T := ((B :: rest').map norm).sum
      set R := ((A :: B :: rest').map norm).sum
      -- The target is exp((n:𝕂)⁻¹ • (A :: B :: rest').sum)
      have sum_eq : (A :: B :: rest').sum = A + (B :: rest').sum := List.sum_cons
      have hsmul : a + (n : 𝕂)⁻¹ • (B :: rest').sum + a =
          (n : 𝕂)⁻¹ • (A :: B :: rest').sum := by
        rw [sum_eq]
        exact symmetric_smul_eq' (𝕂 := 𝕂) A (B :: rest').sum n hn
      rw [← hsmul]
      -- Algebraic split
      have alg : exp a * S * exp a - exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a) =
          exp a * (S - B_exp) * exp a +
          (exp a * B_exp * exp a -
            exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)) := by noncomm_ring
      rw [alg]
      -- Triangle inequality
      have h_tri : ‖exp a * (S - B_exp) * exp a +
          (exp a * B_exp * exp a -
            exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a))‖ ≤
          ‖exp a * (S - B_exp) * exp a‖ +
          ‖exp a * B_exp * exp a -
            exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)‖ :=
        norm_add_le _ _
      -- Norm bounds for a
      have norm_a : ‖a‖ = ‖A‖ / (2 * n) := by
        show ‖(2 * (n : 𝕂))⁻¹ • A‖ = _
        rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
      have hA := norm_nonneg A
      have hT : 0 ≤ T := by
        apply List.sum_nonneg; intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨b, _, rfl⟩ := hx; exact norm_nonneg b
      have hR_eq : R = ‖A‖ + T := by
        simp only [R, T, List.map_cons, List.sum_cons]
      -- Term 1: ‖exp(a) * (S - B_exp) * exp(a)‖
      have h_term1 : ‖exp a * (S - B_exp) * exp a‖ ≤
          Real.exp (‖A‖ / n) * (13 * T ^ 3 / (n : ℝ) ^ 3 *
            Real.exp (T / n)) := by
        calc ‖exp a * (S - B_exp) * exp a‖
            ≤ ‖exp a * (S - B_exp)‖ * ‖exp a‖ := norm_mul_le _ _
          _ ≤ (‖exp a‖ * ‖S - B_exp‖) * ‖exp a‖ := by
              gcongr; exact norm_mul_le _ _
          _ ≤ (Real.exp ‖a‖ * ‖S - B_exp‖) * Real.exp ‖a‖ := by
              gcongr
              · exact norm_exp_le (𝕂 := 𝕂) _
              · exact norm_exp_le (𝕂 := 𝕂) _
          _ = Real.exp (2 * ‖a‖) * ‖S - B_exp‖ := by
              rw [show Real.exp ‖a‖ * ‖S - B_exp‖ * Real.exp ‖a‖ =
                  (Real.exp ‖a‖ * Real.exp ‖a‖) * ‖S - B_exp‖ from by ring,
                ← Real.exp_add, show ‖a‖ + ‖a‖ = 2 * ‖a‖ from by ring]
          _ ≤ Real.exp (‖A‖ / n) * ‖S - B_exp‖ := by
              gcongr; rw [norm_a]; field_simp; linarith
          _ ≤ Real.exp (‖A‖ / n) *
              (13 * T ^ 3 / (n : ℝ) ^ 3 * Real.exp (T / n)) := by
              gcongr
      -- Term 2: cubic Strang bound
      -- This is exactly norm_exp_mul_exp_mul_exp_sub_exp_add_cubic applied
      -- to a and (n:𝕂)⁻¹ • (B :: rest').sum
      set b_arg := (n : 𝕂)⁻¹ • (B :: rest').sum
      have norm_b_arg : ‖b_arg‖ ≤ T / n := by
        calc ‖b_arg‖ = ‖(n : 𝕂)⁻¹ • (B :: rest').sum‖ := rfl
          _ ≤ ‖(n : 𝕂)⁻¹‖ * ‖(B :: rest').sum‖ := norm_smul_le _ _
          _ = ((n : ℝ))⁻¹ * ‖(B :: rest').sum‖ := by rw [norm_inv_n]
          _ ≤ ((n : ℝ))⁻¹ * T := by
              gcongr; exact norm_list_sum_le _
          _ = T / n := by rw [inv_mul_eq_div]
      have h_term2 : ‖exp a * B_exp * exp a -
          exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)‖ ≤
          (7 * ‖a‖ ^ 2 * ‖b_arg‖ + 3 * ‖a‖ * ‖b_arg‖ ^ 2 +
           3 * ‖a‖ ^ 3) *
            Real.exp (2 * ‖a‖ + ‖b_arg‖) := by
        have hrw : exp a * B_exp * exp a -
            exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a) =
            exp a * exp b_arg * exp a - exp (a + b_arg + a) := rfl
        rw [hrw]
        exact norm_exp_mul_exp_mul_exp_sub_exp_add_cubic (𝕂 := 𝕂) a b_arg
      -- Now bound Term 2 numerically
      have h_term2' : ‖exp a * B_exp * exp a -
          exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)‖ ≤
          (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
           3 / 8 * ‖A‖ ^ 3) / (n : ℝ) ^ 3 *
            Real.exp (R / n) := by
        calc ‖exp a * B_exp * exp a -
              exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)‖
            ≤ (7 * ‖a‖ ^ 2 * ‖b_arg‖ + 3 * ‖a‖ * ‖b_arg‖ ^ 2 +
               3 * ‖a‖ ^ 3) *
                Real.exp (2 * ‖a‖ + ‖b_arg‖) := h_term2
          _ ≤ (7 * (‖A‖ / (2 * n)) ^ 2 * (T / n) +
               3 * (‖A‖ / (2 * n)) * (T / n) ^ 2 +
               3 * (‖A‖ / (2 * n)) ^ 3) *
                Real.exp (2 * (‖A‖ / (2 * n)) + T / n) := by
              rw [norm_a]; gcongr
          _ = (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
               3 / 8 * ‖A‖ ^ 3) / (↑n) ^ 3 *
                Real.exp ((‖A‖ + T) / ↑n) := by
              field_simp; ring
          _ = (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
               3 / 8 * ‖A‖ ^ 3) / (↑n) ^ 3 *
                Real.exp (R / ↑n) := by
              rw [hR_eq]
      -- Combine terms
      calc ‖exp a * (S - B_exp) * exp a +
            (exp a * B_exp * exp a -
              exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a))‖
          ≤ ‖exp a * (S - B_exp) * exp a‖ +
            ‖exp a * B_exp * exp a -
              exp (a + (n : 𝕂)⁻¹ • (B :: rest').sum + a)‖ := h_tri
        _ ≤ Real.exp (‖A‖ / n) * (13 * T ^ 3 / (↑n) ^ 3 * Real.exp (T / n)) +
            ((7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
              3 / 8 * ‖A‖ ^ 3) / (↑n) ^ 3 * Real.exp (R / ↑n)) :=
          add_le_add h_term1 h_term2'
        _ ≤ 13 * R ^ 3 / (↑n) ^ 3 * Real.exp (R / ↑n) := by
            -- We need: exp(‖A‖/n) * 13*T³/n³ * exp(T/n) + (coeff)/n³ * exp(R/n) ≤ 13*R³/n³ * exp(R/n)
            -- Note: exp(‖A‖/n) * exp(T/n) = exp((‖A‖+T)/n) = exp(R/n)
            have hexp_combine : Real.exp (‖A‖ / ↑n) * Real.exp (T / ↑n) =
                Real.exp (R / ↑n) := by
              rw [← Real.exp_add, hR_eq]; ring_nf
            -- Rearrange term 1
            have h1_rw : Real.exp (‖A‖ / ↑n) * (13 * T ^ 3 / (↑n) ^ 3 * Real.exp (T / ↑n)) =
                13 * T ^ 3 / (↑n) ^ 3 * Real.exp (R / ↑n) := by
              rw [show Real.exp (‖A‖ / ↑n) * (13 * T ^ 3 / (↑n) ^ 3 * Real.exp (T / ↑n)) =
                  13 * T ^ 3 / (↑n) ^ 3 * (Real.exp (‖A‖ / ↑n) * Real.exp (T / ↑n)) from by ring,
                hexp_combine]
            rw [h1_rw]
            -- Now: 13*T³/n³ * E + (7/4*‖A‖²*T + 3/2*‖A‖*T² + 3/8*‖A‖³)/n³ * E ≤ 13*R³/n³ * E
            -- Factor out E/n³
            have hE := Real.exp_pos (R / ↑n)
            have hn3 : (0 : ℝ) < (↑n) ^ 3 := by positivity
            -- Sufficient: 13*T³ + 7/4*‖A‖²*T + 3/2*‖A‖*T² + 3/8*‖A‖³ ≤ 13*R³
            -- i.e., 13*T³ + 7/4*‖A‖²*T + 3/2*‖A‖*T² + 3/8*‖A‖³ ≤ 13*(‖A‖+T)³
            -- 13*(‖A‖+T)³ = 13*(‖A‖³ + 3*‖A‖²*T + 3*‖A‖*T² + T³)
            --             = 13*T³ + 39*‖A‖²*T + 39*‖A‖*T² + 13*‖A‖³
            -- Need: 7/4*‖A‖²*T + 3/2*‖A‖*T² + 3/8*‖A‖³ ≤ 39*‖A‖²*T + 39*‖A‖*T² + 13*‖A‖³
            -- This is clear since 7/4 ≤ 39, 3/2 ≤ 39, 3/8 ≤ 13
            -- Sufficient: 13*T³ + 7/4*‖A‖²*T + 3/2*‖A‖*T² + 3/8*‖A‖³ ≤ 13*R³
            have h_coeff : 13 * T ^ 3 + (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
                3 / 8 * ‖A‖ ^ 3) ≤ 13 * R ^ 3 := by
              rw [hR_eq]
              nlinarith [sq_nonneg ‖A‖, sq_nonneg T, sq_nonneg (‖A‖ * T),
                sq_nonneg (‖A‖ - T), mul_self_nonneg ‖A‖, mul_self_nonneg T]
            have hE_pos := Real.exp_pos (R / ↑n)
            have : 13 * T ^ 3 / (↑n) ^ 3 * Real.exp (R / ↑n) +
                (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 + 3 / 8 * ‖A‖ ^ 3) /
                  (↑n) ^ 3 * Real.exp (R / ↑n)
                = (13 * T ^ 3 + (7 / 4 * ‖A‖ ^ 2 * T + 3 / 2 * ‖A‖ * T ^ 2 +
                    3 / 8 * ‖A‖ ^ 3)) / (↑n) ^ 3 * Real.exp (R / ↑n) := by ring
            rw [this]
            apply mul_le_mul_of_nonneg_right _ hE_pos.le
            apply div_le_div_of_nonneg_right h_coeff
            positivity

/-!
## Convergence rate: O(1/n²)
-/

include 𝕂 in
theorem symmetric_lie_trotter_list_error_rate (As : List 𝔸) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖(symmetricProd 𝕂 n As) ^ n - exp As.sum‖ ≤ C / n ^ 2 := by
  set S := (As.map norm).sum with hS_def
  have hS_nonneg : 0 ≤ S := by
    apply List.sum_nonneg; intro x hx
    simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; exact norm_nonneg b
  set c := 13 * S ^ 3
  refine ⟨c * Real.exp S + 1, by positivity, ?_⟩
  intro n hn
  -- Step 1: Rewrite exp(As.sum) = exp(As.sum/n)^n
  have hpow : exp As.sum = (exp ((n : 𝕂)⁻¹ • As.sum)) ^ n :=
    (exp_div_pow (𝕂 := 𝕂) As.sum n hn).symm
  rw [hpow]
  set P := symmetricProd 𝕂 n As with hP_def
  set Q := exp ((n : 𝕂)⁻¹ • As.sum) with hQ_def
  -- Step 2: Apply telescoping
  have h_telesc := norm_pow_sub_pow_le' P Q n
  -- Step 3: Bound ‖P - Q‖ by cubic step error
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_step : ‖P - Q‖ ≤ c / (n : ℝ) ^ 3 * Real.exp (S / n) := by
    rw [hP_def, hQ_def]
    exact norm_symmetricProd_sub_exp_smul_sum (𝕂 := 𝕂) As n hn
  -- Step 4: Bound max(‖P‖, ‖Q‖)
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have h_max : max ‖P‖ ‖Q‖ ≤ Real.exp (S / n) := by
    have h_P : ‖P‖ ≤ Real.exp (S / n) := by
      rw [hP_def]
      exact norm_symmetricProd_le (𝕂 := 𝕂) As n hn
    have h_Q : ‖Q‖ ≤ Real.exp (S / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • As.sum)‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • As.sum‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖As.sum‖) := by
            gcongr; exact norm_smul_le _ _
        _ ≤ Real.exp (S / n) := by
            gcongr
            rw [norm_inv_n, inv_mul_eq_div]
            exact div_le_div_of_nonneg_right (norm_list_sum_le As) hn_pos.le
    exact max_le h_P h_Q
  -- Step 5: Combine and simplify
  calc ‖P ^ n - Q ^ n‖
      ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (c / (n : ℝ) ^ 3 * Real.exp (S / n)) *
        (Real.exp (S / n)) ^ (n - 1) := by
        have hc_nonneg : 0 ≤ c := by positivity
        gcongr
    _ ≤ (c * Real.exp S + 1) / n ^ 2 := by
        have h_pow : Real.exp (S / ↑n) * Real.exp (S / ↑n) ^ (n - 1) =
            Real.exp (S / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (S / ↑n) ^ n = Real.exp S := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have h_lhs : ↑n * (c / (↑n) ^ 3 * Real.exp (S / ↑n)) *
            Real.exp (S / ↑n) ^ (n - 1) =
            c * Real.exp S / (↑n) ^ 2 := by
          have : ↑n * (c / (↑n) ^ 3 * Real.exp (S / ↑n)) *
              Real.exp (S / ↑n) ^ (n - 1) =
              ↑n / (↑n) ^ 3 * c *
              (Real.exp (S / ↑n) * Real.exp (S / ↑n) ^ (n - 1)) := by ring
          rw [this, h_pow, h_exp_pow]
          have : (↑n : ℝ) / (↑n) ^ 3 = 1 / (↑n) ^ 2 := by
            field_simp
          rw [this]; ring
        rw [h_lhs]
        have hn2_pos : (0 : ℝ) < (↑n) ^ 2 := by positivity
        exact (div_le_div_iff_of_pos_right hn2_pos).mpr (le_add_of_nonneg_right zero_le_one)

/-!
## Main theorem: Convergence of the multi-operator symmetric Lie-Trotter formula
-/

include 𝕂 in
/-- **The Multi-Operator Symmetric Lie-Trotter (Strang Splitting) Product Formula.**
    For any list of elements `As` in a complete normed algebra,
    `(symmetricProd n As)^n → exp(∑ᵢ Aᵢ)` as `n → ∞`,
    with O(1/n²) convergence rate. -/
theorem symmetric_lie_trotter_list (As : List 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (symmetricProd 𝕂 n As) ^ n)
      atTop (nhds (exp As.sum)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ := symmetric_lie_trotter_list_error_rate (𝕂 := 𝕂) As
  -- Need N such that C/N² < ε. Use N > C/ε (since C/N² ≤ C/N < ε for N > C/ε ≥ 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  calc ‖(symmetricProd 𝕂 n As) ^ n - exp As.sum‖
      ≤ C / n ^ 2 := hC_bound n hn_pos
    _ ≤ C / n := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity) _
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ 2 := by
              exact pow_le_pow_right₀ hn_cast (by omega)
    _ ≤ C / (N + 1) := by
        apply div_le_div_of_nonneg_left hC_pos.le (by positivity : (0:ℝ) < N + 1)
        exact_mod_cast hn
    _ ≤ C / N.succ := by norm_cast
    _ < ε := by
        rw [div_lt_iff₀' (by positivity : (0 : ℝ) < ↑N.succ)]
        calc C = C / ε * ε := by field_simp
          _ < (N + 1) * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              calc C / ε < N := hN
                _ < N + 1 := by linarith
          _ = ↑N.succ * ε := by push_cast; ring
