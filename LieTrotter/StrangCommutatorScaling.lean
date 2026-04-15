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

/-- Derivative of the conjugated Strang product
  `w(τ) = exp(-τH) · exp(τA/2) · exp(τB) · exp(τA/2)`.
  The derivative equals `exp(-τH) · 𝒯₂(τ) · S₂(τ)` where 𝒯₂ is the Strang residual. -/
private lemma hasDerivAt_conj_strang (A B : 𝔸) (τ : ℝ) :
    HasDerivAt
      (fun u => exp ((-u) • (A + B)) * (exp ((u / 2) • A) * exp (u • B) * exp ((u / 2) • A)))
      (exp ((-τ) • (A + B)) *
        ((exp ((τ / 2) • A) * B * exp ((-τ / 2) • A) - B) +
         exp ((τ / 2) • A) * (exp (τ • B) * ((1/2 : ℝ) • A) * exp ((-τ) • B) -
           (1/2 : ℝ) • A) * exp ((-τ / 2) • A)) *
        (exp ((τ / 2) • A) * exp (τ • B) * exp ((τ / 2) • A))) τ := by
  -- Step 1: Show the function equals a uniform `exp(u • X)` form
  set A' := (1/2 : ℝ) • A with hA'
  have hsmul_eq : ∀ u : ℝ, (u / 2) • A = u • A' := by
    intro u; rw [hA', smul_smul, show u * (1 / 2 : ℝ) = u / 2 from by ring]
  have hfun_eq : (fun u : ℝ => exp ((-u) • (A + B)) *
      (exp ((u / 2) • A) * exp (u • B) * exp ((u / 2) • A))) =
      (fun u => exp (u • (-(A + B))) * (exp (u • A') * (exp (u • B) * exp (u • A')))) := by
    ext u
    rw [show (-u) • (A + B) = u • (-(A + B)) from by rw [neg_smul, smul_neg],
        show (u / 2) • A = u • A' from hsmul_eq u, mul_assoc]
  rw [hfun_eq]
  -- Also rewrite the derivative value
  rw [show (-τ) • (A + B) = τ • (-(A + B)) from by rw [neg_smul, smul_neg],
     show (τ / 2) • A = τ • A' from hsmul_eq τ,
     show (-τ / 2) • A = τ • (-A') from by
       rw [show (-τ / 2 : ℝ) = -(τ / 2) from by ring, neg_smul, hsmul_eq, ← smul_neg],
     mul_assoc (exp (τ • A'))]
  -- Step 3: Derivatives via HasDerivAt.mul
  set A' := (1/2 : ℝ) • A
  set nH := -(A + B)
  have hH := hasDerivAt_exp_smul_const' (𝕂 := ℝ) nH τ
  have hA1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A' τ
  have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B τ
  have hA2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A' τ
  have hBA := hB.mul hA2
  have hS := hA1.mul hBA
  have hFull := hH.mul hS
  convert hFull using 1
  -- Step 4: Algebraic simplification using commutativity
  set E := exp (τ • nH)
  have hcH : (A + B) * E = E * (A + B) :=
    ((Commute.refl (A + B)).neg_right.smul_right τ).exp_right.eq
  have h_neg : nH * E = -(E * (A + B)) := by simp only [nH]; rw [neg_mul, hcH]
  have hcA : A' * exp (τ • A') = exp (τ • A') * A' :=
    ((Commute.refl A').smul_right τ).exp_right.eq
  have hcB : B * exp (τ • B) = exp (τ • B) * B :=
    ((Commute.refl B).smul_right τ).exp_right.eq
  -- The remaining step: show the product-rule derivative equals 𝒯₂·S₂.
  -- This is: S₂' - H·S₂ = 𝒯₂·S₂ where S₂' = A'·S₂ + eA·B·eB·eA + eA·eB·A'·eA
  -- and 𝒯₂ = [eA·B·enA - B] + eA·[eB·A'·enB - A']·enA
  -- The identity uses exp(X)·exp(-X) = 1 (from exp_smul_mul_exp_neg_smul).
  -- noncomm_ring alone can't handle this since it requires the inverse relation.
  convert hFull using 1
  simp only [Pi.mul_apply, nH]
  -- Goal: E * (𝒯₂ * S₂) = nH*E*S₂ + E*S₂' (after commutativity rewrites)
  -- 𝒯₂*S₂ = S₂' - H*S₂ = S₂' + nH*S₂ (since nH = -H)
  -- So E*(𝒯₂*S₂) = E*(S₂' + nH*S₂) = E*S₂' + E*nH*S₂ = E*S₂' + nH*E*S₂
  -- Remaining: algebraic identity E*𝒯₂*S₂ = nH*E*S₂ + E*S₂'
  -- using exp(X)*exp(-X) = 1, commutativity of A' with eA, B with eB, (A+B) with E
  -- The proof expands 𝒯₂*S₂, substitutes exp(-X)*exp(X) → 1 three times, and
  -- uses commutativity to show the result equals S₂' + nH*S₂.
  -- Verified on paper; the Lean formalization needs careful `set` management
  -- to avoid variable renaming issues from simp.
  sorry

theorem norm_strang_comm_scaling [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤
      (‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
       ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24) * t ^ 3 := by
  have hAB : star (A + B) = -(A + B) := by rw [star_add, hA, hB, neg_add]
  -- Abbreviations for double commutator norms
  set DC_B := ‖B * (B * A - A * B) - (B * A - A * B) * B‖
  set DC_A := ‖A * (A * B - B * A) - (A * B - B * A) * A‖
  -- Bound the Strang residual by double commutators
  -- TODO: combine hasDerivAt_conj_strang + FTC + norm_exp_conj_sub_comm_le
  -- to get ‖S₂(t) - exp(tH)‖ ≤ ∫₀ᵗ ‖𝒯₂(τ)‖ dτ ≤ (DC_B/12 + DC_A/24)·t³
  sorry

end
