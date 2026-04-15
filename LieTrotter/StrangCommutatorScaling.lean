/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Commutator-Scaling for Second-Order Strang Splitting

The commutator-scaling bound for the second-order Suzuki (Strang) formula,
following the Proposition in Childs et al. (2021), §VII.A.

The symmetric product exp(tA/2)·exp(tB)·exp(tA/2) cancels the first-order
commutator [B,A] (order condition), leaving only **double commutators**
[B,[B,A]] and [A,[A,B]] at cubic order.

## Key identities

The double commutators [B,[B,A/2]] = (1/2)[B,[B,A]] and [A/2,[A/2,B]] = (1/4)[A,[A,B]]
give the prefactors t³/12 and t³/24 in the paper's tight bound.
-/

import LieTrotter.CommutatorScaling
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Phase 1: Double conjugation FTC

The key building block: applying `exp_conj_sub_eq_integral` twice to extract
a double commutator from `exp(τB)·A·exp(-τB) - A`.

The first FTC gives: `exp(τB)·A·exp(-τB) - A = ∫₀ᵗ exp(sB)·[B,A]·exp(-sB) ds`

The integrand `f(s) = exp(sB)·[B,A]·exp(-sB)` itself satisfies:
  `f(s) - f(0) = ∫₀ˢ exp(uB)·[B,[B,A]]·exp(-uB) du`

Combining: the conjugation difference equals [B,A]·τ + double integral of [B,[B,A]].
-/

/-- Double conjugation FTC: expand the conjugation integral to extract the
  double commutator. The difference `exp(τB)·A·exp(-τB) - A - [B,A]·τ`
  equals a double integral of `[B,[B,A]]` terms. -/
theorem exp_conj_sub_comm_eq_double_integral (A B : 𝔸) (τ : ℝ) :
    exp (τ • B) * A * exp ((-τ) • B) - A -
      τ • (B * A - A * B) =
    ∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s,
      exp (u • B) * (B * (B * A - A * B) - (B * A - A * B) * B) *
        exp ((-u) • B) := by
  -- Step 1: rewrite LHS using exp_conj_sub_eq_integral
  -- exp(τB)·A·exp(-τB) - A = ∫₀ᵗ f(s) ds where f(s) = exp(sB)·[B,A]·exp(-sB)
  rw [exp_conj_sub_eq_integral A B τ]
  -- Now goal: ∫₀ᵗ f(s) ds - τ • c = ∫₀ᵗ (∫₀ˢ g(u) du) ds
  -- where c = f(0) = [B,A]
  set f : ℝ → 𝔸 := fun s => exp (s • B) * (B * A - A * B) * exp ((-s) • B)
  set c : 𝔸 := B * A - A * B
  -- Step 2: ∫₀ᵗ c ds = τ • c
  have hint_c : ∫ _ in (0:ℝ)..τ, c = τ • c := by
    rw [intervalIntegral.integral_const]; simp
  -- Step 3: ∫ f - τ•c = ∫ f - ∫ c = ∫ (f - c)
  have hint_f : IntervalIntegrable f volume 0 τ := by
    apply Continuous.intervalIntegrable
    letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
    exact (exp_continuous.comp (continuous_id.smul continuous_const) |>.mul
      continuous_const).mul
      (exp_continuous.comp (continuous_neg.smul continuous_const))
  have hint_const : IntervalIntegrable (fun _ => c) volume 0 τ :=
    continuous_const.intervalIntegrable 0 τ
  rw [← hint_c, ← integral_sub hint_f hint_const]
  -- Step 4: f(s) - c = exp(sB)·[B,A]·exp(-sB) - [B,A] = ∫₀ˢ g(u) du
  -- by exp_conj_sub_eq_integral applied to [B,A] conjugated by B
  congr 1; ext s
  exact exp_conj_sub_eq_integral (B * A - A * B) B s

/-!
## Phase 2: Strang residual and first-order cancellation

The Strang product exp(τA/2)·exp(τB)·exp(τA/2) has residual 𝒯₂(τ) consisting
of two conjugation terms whose O(τ) parts cancel.
-/

/-- The Strang error decomposes into two first-order Trotter errors.
  Each bracket uses `lie_trotter_integral_error` with appropriate operator pairs. -/
theorem strang_two_bracket_decomp (A B : 𝔸) (t : ℝ) :
    exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B)) =
      exp ((t / 2) • A) * (exp (t • B) * exp (t • ((1/2 : ℝ) • A)) -
        exp (t • (B + (1/2 : ℝ) • A))) +
      (exp (t • ((1/2 : ℝ) • A)) * exp (t • (B + (1/2 : ℝ) • A)) -
        exp (t • (A + B))) := by
  have h1 : t • ((1/2 : ℝ) • A) = (t / 2) • A := by rw [smul_smul]; ring_nf
  have h2 : (1/2 : ℝ) • A + (B + (1/2 : ℝ) • A) = A + B := by
    rw [show (1/2 : ℝ) • A + (B + (1/2 : ℝ) • A) = B + ((1/2 : ℝ) • A + (1/2 : ℝ) • A)
      from by abel]
    rw [← add_smul]; norm_num; abel
  rw [h1]; noncomm_ring

/-!
## Phase 3: Double commutator norm bounds

Bound ‖exp(τB)·A·exp(-τB) - A - [B,A]·τ‖ ≤ ‖[B,[B,A]]‖·τ²/2·exp(2τ‖B‖)
using the double integral representation and `norm_integral_le_of_norm_le_const`.
-/

/-- The double conjugation remainder is bounded by the double commutator norm.
  `‖exp(τB)·A·exp(-τB) - A - [B,A]·τ‖ ≤ ‖[B,[B,A]]‖·τ²/2·exp(2|τ|‖B‖)` -/
theorem norm_exp_conj_sub_comm_le (A B : 𝔸) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖exp (τ • B) * A * exp ((-τ) • B) - A - τ • (B * A - A * B)‖ ≤
      ‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 2 *
        τ ^ 2 * Real.exp (2 * τ * ‖B‖) := by
  rw [exp_conj_sub_comm_eq_double_integral]
  set C := B * (B * A - A * B) - (B * A - A * B) * B
  set K := ‖C‖ * Real.exp (2 * τ * ‖B‖)
  -- Inner integral bound: ‖∫₀ˢ g(u) du‖ ≤ K·s for 0 ≤ s ≤ τ
  -- (from norm_exp_conj_sub_le applied to [B,A] conjugated by B, + exp monotonicity)
  have hinner_bound : ∀ s ∈ Set.Ioc 0 τ,
      ‖∫ u in (0:ℝ)..s, exp (u • B) * C * exp ((-u) • B)‖ ≤ K * s := by
    intro s hs
    -- ‖∫₀ˢ g du‖ = ‖exp(sB)·(BA-AB)·exp(-sB) - (BA-AB)‖ ≤ ‖C‖·|s|·exp(2|s|‖B‖)
    have h := norm_exp_conj_sub_le (B * A - A * B) B s
    calc ‖∫ u in (0:ℝ)..s, exp (u • B) * C * exp ((-u) • B)‖
        = ‖exp (s • B) * (B * A - A * B) * exp ((-s) • B) - (B * A - A * B)‖ := by
          congr 1; exact (exp_conj_sub_eq_integral (B * A - A * B) B s).symm
      _ ≤ ‖C‖ * |s| * Real.exp (2 * |s| * ‖B‖) := h
      _ = ‖C‖ * s * Real.exp (2 * s * ‖B‖) := by rw [abs_of_pos hs.1]
      _ ≤ ‖C‖ * s * Real.exp (2 * τ * ‖B‖) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (le_of_lt hs.1))
          exact Real.exp_le_exp_of_le (by nlinarith [hs.2, norm_nonneg B])
      _ = K * s := by ring
  -- Outer integral: ‖∫₀ᵗ (∫₀ˢ g du) ds‖ ≤ ∫₀ᵗ K·s ds = K·τ²/2
  have hg_int : IntervalIntegrable (fun s => K * s) volume 0 τ :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 τ
  calc ‖∫ s in (0:ℝ)..τ, ∫ u in (0:ℝ)..s,
          exp (u • B) * C * exp ((-u) • B)‖
      ≤ ∫ s in (0:ℝ)..τ, K * s := by
        apply norm_integral_le_of_norm_le hτ _ hg_int
        exact Filter.Eventually.of_forall (fun s hs => hinner_bound s hs)
    _ = K * (τ ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have : ∀ x ∈ Set.uIcc 0 τ, HasDerivAt (fun x => x ^ 2 / 2) x x := by
          intro x _; have h := (hasDerivAt_pow 2 x).div_const 2
          simp only [Nat.cast_ofNat] at h; convert h using 1; ring
        rw [integral_eq_sub_of_hasDerivAt this (continuous_id.intervalIntegrable 0 τ)]
        simp
    _ = ‖C‖ / 2 * τ ^ 2 * Real.exp (2 * τ * ‖B‖) := by
        simp only [K]; ring

/-!
## Phase 4: Main commutator-scaling theorem for Strang

The bound scales with double commutators ‖[B,[B,A]]‖ and ‖[A,[A,B]]‖ at O(t³).
-/

/-- **Commutator-scaling bound for the second-order Strang formula** (anti-Hermitian case):
  The error scales with double commutators ‖[B,[B,A]]‖ and ‖[A,[A,B]]‖ at O(t³).

  This matches the Proposition in Childs et al. (2021), §VII.A:
    `‖S₂(t) - exp(tH)‖ ≤ t³/12·‖[B,[B,A]]‖ + t³/24·‖[A,[A,B]]‖`

  **Note:** The paper's tight bound (without exponential factors beyond the overall
  `exp(...)`) holds for anti-Hermitian operators where ‖exp(tX)‖ = 1, ensuring
  the two first-order commutator terms cancel perfectly at the integral level.

  For general Banach algebras, the exponential weights in the two brackets of
  `strang_two_bracket_decomp` differ, leaving an O(t²·‖[B,A]‖) residual from
  the imperfect cancellation. The O(t³) scaling with NORMS (not commutators)
  is already proved in `norm_exp_mul_exp_mul_exp_sub_exp_add_cubic`.

  **Building blocks proved:**
  - `exp_conj_sub_comm_eq_double_integral`: nested FTC extracting [B,[B,A]]
  - `norm_exp_conj_sub_comm_le`: bound ‖...‖ ≤ ‖[B,[B,A]]‖/2·τ²·exp(2τ‖B‖)
  - `strang_two_bracket_decomp`: S₂(t) - exp(tH) = exp(a)·Bracket₁ + Bracket₂ -/
-- Key property: in a C*-algebra, anti-Hermitian exponentials are unitary with norm 1.
lemma norm_exp_smul_of_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) :
    ‖exp (t • a)‖ = 1 := by
  have hta : star (t • a) = -(t • a) := by
    rw [StarModule.star_smul, ha, smul_neg, star_trivial]
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact CStarRing.norm_of_mem_unitary
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hta))

theorem norm_strang_comm_scaling [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤
      (‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
       ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24) * t ^ 3 := by
  -- Anti-Hermitian implies A+B is also anti-Hermitian
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  -- All exponentials have norm 1 in C*-algebra with anti-Hermitian argument
  -- Step 1: Bound ‖S₂(t) - exp(tH)‖ ≤ ∫₀ᵗ ‖𝒯₂(τ)‖ dτ via Duhamel + unitary norms
  -- Step 2: Bound ‖𝒯₂(τ)‖ ≤ C·τ² using double FTC
  -- Step 3: Evaluate ∫₀ᵗ C·τ² dτ = C·t³/3
  -- This requires computing 𝒯₂' and 𝒯₂'' (derivatives of the Strang residual)
  -- using hasDerivAt_exp_conj and the Leibniz rule for conjugation.
  -- Deferred: the building blocks (exp_conj_sub_comm_eq_double_integral,
  -- norm_exp_conj_sub_comm_le, norm_exp_smul_of_skewAdjoint) are all proved.
  sorry

end
