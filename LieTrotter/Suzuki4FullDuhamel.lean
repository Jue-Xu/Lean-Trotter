/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Commutator-Scaling via Telescoping S₂ Blocks

Proves the S₄ error decomposes as a sum of 5 Strang-vs-exponential errors
via telescoping, and bounds the total error using `norm_strang_comm_scaling`.
The bound is O(t³) with coefficient C·(4|p|³+|q|³).

## Structure

1. S₄(τ) = S₂(p)·S₂(p)·S₂(q)·S₂(p)·S₂(p) (algebraic identity via exp merging)
2. Telescoping: S₄ - exp(H) = Σᵢ (prefix_i)·(S₂ᵢ - Eᵢ)·(suffix_i)
3. Anti-Hermitian isometry: ‖prefix‖ = ‖suffix‖ = 1
4. Each ‖S₂(ct) - exp(ctH)‖ ≤ C·|c|³·t³ (Strang commutator scaling)
5. Total: ‖S₄(t) - exp(tH)‖ ≤ C·(4|p|³+|q|³)·t³

## What this file proves

- `suzuki4Exp_eq_strang2_prod`: S₄ = product of 5 S₂ blocks (key identity)
- `suzuki4_telescope`: telescoping decomposition of S₄ - exp(tH)
- `norm_suzuki4_comm_scaling`: O(t³) bound with exact coefficient
-/

import LieTrotter.Suzuki4Deriv
import LieTrotter.Suzuki4CommutatorScaling

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Layer 1: S₂ building blocks and the S₄ = 5×S₂ identity

S₂(c,τ) = exp((c/2)τA) · exp(cτB) · exp((c/2)τA)

S₄(τ) has 11 exponentials. The product of 5 S₂ steps has 15, but at each
internal boundary, adjacent A-exponentials merge via `exp_add_of_commute`:
  exp((c₁/2)τA) · exp((c₂/2)τA) = exp(((c₁+c₂)/2)τA)

The 4 merges reduce 15 to 11 exponentials, matching `suzuki4Exp`.
-/

/-- Strang step with coefficient c: S₂(c,τ) = exp((c/2)τA) · exp(cτB) · exp((c/2)τA) -/
private def strang2 (A B : 𝔸) (c τ : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exp (((c / 2) * τ) • A) * exp ((c * τ) • B) * exp (((c / 2) * τ) • A)

/-- Continuity of S₂(c,τ) in τ. -/
private lemma continuous_strang2 (A B : 𝔸) (c : ℝ) : Continuous (strang2 A B c) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  unfold strang2
  exact ((exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const)).mul
    (exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const))).mul
    (exp_continuous.comp ((continuous_const.mul continuous_id).smul continuous_const))

/-- Merging adjacent exponentials of the same element:
  exp((c₁·τ)•X) · exp((c₂·τ)•X) = exp(((c₁+c₂)·τ)•X) -/
private lemma exp_merge (X : 𝔸) (c₁ c₂ τ : ℝ) :
    (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
     exp ((c₁ * τ) • X) * exp ((c₂ * τ) • X)) =
    (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
     exp (((c₁ + c₂) * τ) • X)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute
    ((Commute.refl X).smul_left ((c₁ * τ)) |>.smul_right ((c₂ * τ)))]
  congr 1; rw [← add_smul]; congr 1; ring

/-- **Key identity: S₄ equals the product of 5 Strang steps.**

  The 4 internal A-exponential merges are:
  - S₂(p)|S₂(p): (p/2 + p/2)τA = pτA ✓
  - S₂(p)|S₂(q): (p/2 + q/2)τA = ((1-3p)/2)τA ✓
  - S₂(q)|S₂(p): (q/2 + p/2)τA = ((1-3p)/2)τA ✓
  - S₂(p)|S₂(p): (p/2 + p/2)τA = pτA ✓ -/
lemma suzuki4Exp_eq_strang2_prod (A B : 𝔸) (p τ : ℝ) :
    suzuki4Exp A B p τ =
      strang2 A B p τ * strang2 A B p τ * strang2 A B (1 - 4 * p) τ *
      strang2 A B p τ * strang2 A B p τ := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  simp only [suzuki4Exp, strang2]
  set q := 1 - 4 * p
  -- Both sides contain 11 exponentials (after merging 4 adjacent pairs on the RHS).
  -- Flatten to right-association, then apply merge rewrites.
  simp only [mul_assoc]
  -- RHS (right-assoc) has 15 factors; LHS has 11. We merge 4 pairs on RHS.
  -- Merge: exp((p/2*τ)•A) * exp((p/2*τ)•A) → exp((p*τ)•A)
  have hm1 : exp ((p / 2 * τ) • A) * exp ((p / 2 * τ) • A) =
      exp ((p * τ) • A) := by
    rw [exp_merge]; congr 1; congr 1; ring
  -- Merge: exp((p/2*τ)•A) * exp((q/2*τ)•A) → exp(((1-3p)/2*τ)•A)
  have hm2 : exp ((p / 2 * τ) • A) * exp (((1 - 4 * p) / 2 * τ) • A) =
      exp (((1 - 3 * p) / 2 * τ) • A) := by
    rw [exp_merge]; congr 1; congr 1; ring
  -- Merge: exp((q/2*τ)•A) * exp((p/2*τ)•A) → exp(((1-3p)/2*τ)•A)
  have hm3 : exp (((1 - 4 * p) / 2 * τ) • A) * exp ((p / 2 * τ) • A) =
      exp (((1 - 3 * p) / 2 * τ) • A) := by
    rw [exp_merge]; congr 1; congr 1; ring
  -- After simp only [mul_assoc], the RHS is fully right-associated with 15 factors.
  -- We apply 4 merge rewrites from right to left (innermost first):
  -- pair (12,13), pair (9,10), pair (6,7), pair (3,4)
  -- Each rewrite turns `exp(c₁•A) * (exp(c₂•A) * rest)` into
  -- `exp((c₁+c₂)•A) * rest` via `← mul_assoc, merge, mul_assoc`.
  -- Merge pair (12,13): the 4th occurrence from the right
  rw [show ∀ (rest : 𝔸), exp ((p / 2 * τ) • A) *
      (exp ((p / 2 * τ) • A) * rest) = exp ((p * τ) • A) * rest from
      fun rest => by rw [← mul_assoc, hm1]]
  -- Merge pair (9,10):
  rw [show ∀ (rest : 𝔸), exp (((1 - 4 * p) / 2 * τ) • A) *
      (exp ((p / 2 * τ) • A) * rest) = exp (((1 - 3 * p) / 2 * τ) • A) * rest from
      fun rest => by rw [← mul_assoc, hm3]]
  -- Merge pair (6,7):
  rw [show ∀ (rest : 𝔸), exp ((p / 2 * τ) • A) *
      (exp (((1 - 4 * p) / 2 * τ) • A) * rest) = exp (((1 - 3 * p) / 2 * τ) • A) * rest from
      fun rest => by rw [← mul_assoc, hm2]]
  -- Merge pair (3,4):
  rw [show ∀ (rest : 𝔸), exp ((p / 2 * τ) • A) *
      (exp ((p / 2 * τ) • A) * rest) = exp ((p * τ) • A) * rest from
      fun rest => by rw [← mul_assoc, hm1]]

/-!
## Layer 2: Telescoping identity

The 5-factor telescoping reduces S₄ - exp(tH) to a sum of 5 terms,
each containing one (S₂ᵢ - Eᵢ) factor sandwiched between prefix/suffix products.
-/

/-- Telescoping for 5 factors. -/
private lemma telescope5 (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : 𝔸) :
    a₁ * a₂ * a₃ * a₄ * a₅ - b₁ * b₂ * b₃ * b₄ * b₅ =
      (a₁ - b₁) * (a₂ * a₃ * a₄ * a₅) +
      b₁ * ((a₂ - b₂) * (a₃ * a₄ * a₅)) +
      b₁ * b₂ * ((a₃ - b₃) * (a₄ * a₅)) +
      b₁ * b₂ * b₃ * ((a₄ - b₄) * a₅) +
      b₁ * b₂ * b₃ * b₄ * (a₅ - b₅) := by noncomm_ring

/-- exp(tH) factorizes as 5 commuting exponentials when coefficients sum to 1.
  Uses: p+p+q+p+p = 4p+q = 4p+(1-4p) = 1. -/
private lemma exp_factorize5 (H : 𝔸) (p t : ℝ) :
    (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
     exp (t • H)) =
    (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
     exp ((p * t) • H) * exp ((p * t) • H) * exp (((1 - 4 * p) * t) • H) *
     exp ((p * t) • H) * exp ((p * t) • H)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hcomm : ∀ s₁ s₂ : ℝ, Commute (s₁ • H) (s₂ • H) :=
    fun s₁ s₂ => (Commute.refl H).smul_left s₁ |>.smul_right s₂
  -- Work from LHS to RHS: split exp(tH) into 5 factors one at a time
  -- Strategy: first split off the last factor, then continue
  -- exp(tH) = exp((t - pt)•H) * exp((pt)•H) since [sH, s'H] = 0
  -- But it's cleaner to just use congr + ring at the end.
  -- Alternative: merge all 5 on the RHS into one exp.
  symm
  calc exp ((p * t) • H) * exp ((p * t) • H) * exp (((1 - 4 * p) * t) • H) *
        exp ((p * t) • H) * exp ((p * t) • H)
      = exp ((p * t) • H + (p * t) • H) * exp (((1 - 4 * p) * t) • H) *
        exp ((p * t) • H) * exp ((p * t) • H) := by
          rw [exp_add_of_commute (hcomm _ _)]
      _ = exp ((p * t) • H + (p * t) • H + ((1 - 4 * p) * t) • H) *
          exp ((p * t) • H) * exp ((p * t) • H) := by
          rw [exp_add_of_commute ((hcomm _ _).add_left (hcomm _ _))]
      _ = exp ((p * t) • H + (p * t) • H + ((1 - 4 * p) * t) • H + (p * t) • H) *
          exp ((p * t) • H) := by
          rw [exp_add_of_commute (((hcomm _ _).add_left (hcomm _ _)).add_left (hcomm _ _))]
      _ = exp ((p * t) • H + (p * t) • H + ((1 - 4 * p) * t) • H + (p * t) • H + (p * t) • H) := by
          rw [exp_add_of_commute ((((hcomm _ _).add_left (hcomm _ _)).add_left (hcomm _ _)).add_left (hcomm _ _))]
      _ = exp (t • H) := by
          congr 1; rw [← add_smul, ← add_smul, ← add_smul, ← add_smul]; congr 1; ring

/-- The S₄ error decomposes via telescoping into 5 Strang-vs-exponential errors.
  Each term has the form (prefix)·(S₂(cᵢt) - exp(cᵢtH))·(suffix). -/
lemma suzuki4_telescope (A B : 𝔸) (p t : ℝ) :
    letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
    let H := A + B
    let q := 1 - 4 * p
    let S := fun c => strang2 A B c t
    let E := fun c => exp ((c * t) • H)
    suzuki4Exp A B p t - exp (t • H) =
      (S p - E p) * (S p * S q * S p * S p) +
      E p * ((S p - E p) * (S q * S p * S p)) +
      E p * E p * ((S q - E q) * (S p * S p)) +
      E p * E p * E q * ((S p - E p) * S p) +
      E p * E p * E q * E p * (S p - E p) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  intro H q S E
  rw [suzuki4Exp_eq_strang2_prod, exp_factorize5 H p t]
  exact telescope5 (S p) (S p) (S q) (S p) (S p) (E p) (E p) (E q) (E p) (E p)

/-!
## Layer 3: Anti-Hermitian norm bounds

For anti-Hermitian A, B:
- ‖exp(sX)‖ = 1 for any scalar s
- ‖S₂(c,τ)‖ ≤ 1
- ‖E(c)‖ = 1
- The prefix/suffix products in the telescoping have norm ≤ 1
-/

/-- Norm of S₂(c,τ) ≤ 1 for anti-Hermitian operators. -/
private lemma norm_strang2_le_one
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (c τ : ℝ) :
    ‖strang2 A B c τ‖ ≤ 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  simp only [strang2]
  calc ‖exp ((c / 2 * τ) • A) * exp ((c * τ) • B) * exp ((c / 2 * τ) • A)‖
      ≤ ‖exp ((c / 2 * τ) • A)‖ * ‖exp ((c * τ) • B)‖ * ‖exp ((c / 2 * τ) • A)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = 1 := by
        simp [norm_exp_smul_of_skewAdjoint hA, norm_exp_smul_of_skewAdjoint hB]

/-- Norm of exp((c*t)•H) = 1 for anti-Hermitian H. -/
private lemma norm_exp_ct_H
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (c t : ℝ) :
    ‖exp ((c * t) • (A + B))‖ = 1 :=
  norm_exp_smul_of_skewAdjoint (by rw [star_add, hA, hB, neg_add]) (c * t)

/-!
## Layer 4: Main norm bound

Apply the Strang commutator-scaling bound to each S₂ term.
Then use the telescoping and anti-Hermitian bounds.

Each S₂ step satisfies (from `norm_strang_comm_scaling`):
  ‖S₂(ct) - exp(ctH)‖ ≤ C · |c|³ · t³

where C = ‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24.

The telescoping bound (with ‖prefix‖, ‖suffix‖ ≤ 1):
  ‖S₄(t) - exp(tH)‖ ≤ Σᵢ ‖S₂(cᵢt) - exp(cᵢtH)‖
    ≤ C · (4|p|³ + |q|³) · t³
-/

/-- Helper: the S₂ step S₂(c,t) matches the form needed for `norm_strang_comm_scaling`.
  We need to rewrite `strang2 A B c t` as `exp((ct/2)•A) * exp(ct•B) * exp((ct/2)•A)`. -/
private lemma strang2_eq_strang_form (A B : 𝔸) (c t : ℝ) :
    strang2 A B c t =
      (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
       exp (((c * t) / 2) • A) * exp ((c * t) • B) * exp (((c * t) / 2) • A)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  simp only [strang2]
  congr 2 <;> congr 1 <;> ring

/-- The S₂ error bound for arbitrary real coefficient c and t ≥ 0.
  Uses the symmetry: S₂(ct,A,B) = S₂(|ct|,-A,-B) when ct < 0,
  and the bound holds for |c|³·t³. -/
private lemma norm_strang2_sub_exp_le_abs
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    let C := ‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
             ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24
    ‖strang2 A B c t - exp ((c * t) • (A + B))‖ ≤ C * |c| ^ 3 * t ^ 3 := by
  intro C
  by_cases hc : 0 ≤ c
  · -- c ≥ 0: direct application
    have hct : 0 ≤ c * t := mul_nonneg hc ht
    rw [strang2_eq_strang_form]
    calc ‖_‖ ≤ C * (c * t) ^ 3 := norm_strang_comm_scaling A B hct hA hB
      _ = C * |c| ^ 3 * t ^ 3 := by rw [abs_of_nonneg hc]; ring
  · -- c < 0: use S₂(ct,A,B) = S₂(|c|t,-A,-B) and apply bound to (-A,-B)
    push_neg at hc
    have hc_neg : c < 0 := hc
    -- Key: strang2 A B c t = strang2 (-A) (-B) (-c) t
    -- because exp((c/2)τ·A) = exp((-c/2)τ·(-A)) etc.
    have hflip : strang2 A B c t = strang2 (-A) (-B) (-c) t := by
      simp only [strang2]
      letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
      -- Each factor: exp(s•X) = exp((-s)•(-X)) since s•X = (-s)•(-X)
      -- Key: (-c / 2 * t) • (-A) = (c / 2 * t) • A  (negations cancel)
      have h1 : (c / 2 * t) • A = ((-c) / 2 * t) • (-A) := by module
      have h2 : (c * t) • B = ((-c) * t) • (-B) := by module
      rw [h1, h2]
    have hflip_exp : exp ((c * t) • (A + B)) =
        (letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
         exp (((-c) * t) • ((-A) + (-B)))) := by
      letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
      congr 1
      show (c * t) • (A + B) = ((-c) * t) • ((-A) + (-B))
      module
    rw [hflip, hflip_exp]
    have hnA : star (-A) = -(-A) := by rw [star_neg, hA, neg_neg]
    have hnB : star (-B) = -(-B) := by rw [star_neg, hB, neg_neg]
    have hct' : 0 ≤ (-c) * t := mul_nonneg (le_of_lt (neg_pos.mpr hc_neg)) ht
    rw [strang2_eq_strang_form]
    have hcomm_eq : ‖(-B) * ((-B) * (-A) - (-A) * (-B)) - ((-B) * (-A) - (-A) * (-B)) * (-B)‖ =
        ‖B * (B * A - A * B) - (B * A - A * B) * B‖ := by
      have : (-B) * ((-B) * (-A) - (-A) * (-B)) - ((-B) * (-A) - (-A) * (-B)) * (-B) =
          -(B * (B * A - A * B) - (B * A - A * B) * B) := by noncomm_ring
      rw [this, norm_neg]
    have hcomm_eq2 : ‖(-A) * ((-A) * (-B) - (-B) * (-A)) - ((-A) * (-B) - (-B) * (-A)) * (-A)‖ =
        ‖A * (A * B - B * A) - (A * B - B * A) * A‖ := by
      have : (-A) * ((-A) * (-B) - (-B) * (-A)) - ((-A) * (-B) - (-B) * (-A)) * (-A) =
          -(A * (A * B - B * A) - (A * B - B * A) * A) := by noncomm_ring
      rw [this, norm_neg]
    calc ‖_‖ ≤ (‖(-B) * ((-B) * (-A) - (-A) * (-B)) - ((-B) * (-A) - (-A) * (-B)) * (-B)‖ / 12 +
               ‖(-A) * ((-A) * (-B) - (-B) * (-A)) - ((-A) * (-B) - (-B) * (-A)) * (-A)‖ / 24) *
             ((-c) * t) ^ 3 := norm_strang_comm_scaling (-A) (-B) hct' hnA hnB
      _ = C * |c| ^ 3 * t ^ 3 := by
          rw [hcomm_eq, hcomm_eq2]
          have : |c| = -c := abs_of_neg hc_neg
          rw [this]; ring

/-- **S₄ commutator-scaling bound via telescoping** (anti-Hermitian).

  The S₄ error is bounded by applying the Strang commutator-scaling bound to
  each of the 5 S₂ blocks and summing via the telescoping identity. The
  anti-Hermitian property ensures prefix/suffix products have norm ≤ 1.

  The bound is: ‖S₄(t) - exp(tH)‖ ≤ C · (4|p|³ + |q|³) · t³

  where C = ‖[B,[B,A]]‖/12 + ‖[A,[A,B]]‖/24 and q = 1-4p.

  Note: With the Suzuki parameter p = 1/(4-4^{1/3}), the cubic cancellation
  4p³ + q³ = 0 would eliminate the t³ term, but that requires exact computation
  with irrational p. This theorem provides the general bound for any p. -/
theorem norm_suzuki4_comm_scaling
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    let q : ℝ := 1 - 4 * p
    let C := ‖B * (B * A - A * B) - (B * A - A * B) * B‖ / 12 +
             ‖A * (A * B - B * A) - (A * B - B * A) * A‖ / 24
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      C * (4 * |p| ^ 3 + |q| ^ 3) * t ^ 3 := by
  intro p q C
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  -- Step 1: Telescope
  rw [suzuki4_telescope A B p t]
  set H := A + B
  set S := fun c => strang2 A B c t
  set E := fun c => exp ((c * t) • H)
  -- Step 2: Triangle inequality on the 5 terms
  -- Use repeated norm_add_le + linarith instead of gcongr chains
  have htri : ‖(S p - E p) * (S p * S q * S p * S p) +
        E p * ((S p - E p) * (S q * S p * S p)) +
        E p * E p * ((S q - E q) * (S p * S p)) +
        E p * E p * E q * ((S p - E p) * S p) +
        E p * E p * E q * E p * (S p - E p)‖
      ≤ ‖(S p - E p) * (S p * S q * S p * S p)‖ +
        ‖E p * ((S p - E p) * (S q * S p * S p))‖ +
        ‖E p * E p * ((S q - E q) * (S p * S p))‖ +
        ‖E p * E p * E q * ((S p - E p) * S p)‖ +
        ‖E p * E p * E q * E p * (S p - E p)‖ := by
    have h12 := norm_add_le
      ((S p - E p) * (S p * S q * S p * S p))
      (E p * ((S p - E p) * (S q * S p * S p)))
    have h123 := norm_add_le
      ((S p - E p) * (S p * S q * S p * S p) +
       E p * ((S p - E p) * (S q * S p * S p)))
      (E p * E p * ((S q - E q) * (S p * S p)))
    have h1234 := norm_add_le
      ((S p - E p) * (S p * S q * S p * S p) +
       E p * ((S p - E p) * (S q * S p * S p)) +
       E p * E p * ((S q - E q) * (S p * S p)))
      (E p * E p * E q * ((S p - E p) * S p))
    have h12345 := norm_add_le
      ((S p - E p) * (S p * S q * S p * S p) +
       E p * ((S p - E p) * (S q * S p * S p)) +
       E p * E p * ((S q - E q) * (S p * S p)) +
       E p * E p * E q * ((S p - E p) * S p))
      (E p * E p * E q * E p * (S p - E p))
    linarith
  -- Step 3: Bound each term using anti-Hermitian isometry
  have hn_Ep : ‖E p‖ = 1 := norm_exp_ct_H A B hA hB p t
  have hn_Eq : ‖E q‖ = 1 := norm_exp_ct_H A B hA hB q t
  have hn_Sp : ‖S p‖ ≤ 1 := norm_strang2_le_one A B hA hB p t
  have hn_Sq : ‖S q‖ ≤ 1 := norm_strang2_le_one A B hA hB q t
  -- Helper: products of norm-≤-1 elements have norm ≤ 1
  have hmul1 : ∀ (x y : 𝔸), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := by
    intro x y hx hy
    calc ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hx hy (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- Term 1
  have h1 : ‖(S p - E p) * (S p * S q * S p * S p)‖ ≤ ‖S p - E p‖ := by
    have hsuff : ‖S p * S q * S p * S p‖ ≤ 1 :=
      hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hn_Sp hn_Sq) hn_Sp) hn_Sp
    calc ‖(S p - E p) * (S p * S q * S p * S p)‖
        ≤ ‖S p - E p‖ * ‖S p * S q * S p * S p‖ := norm_mul_le _ _
      _ ≤ ‖S p - E p‖ * 1 := by gcongr
      _ = ‖S p - E p‖ := mul_one _
  -- Term 2
  have h2 : ‖E p * ((S p - E p) * (S q * S p * S p))‖ ≤ ‖S p - E p‖ := by
    have hsuff : ‖S q * S p * S p‖ ≤ 1 :=
      hmul1 _ _ (hmul1 _ _ hn_Sq hn_Sp) hn_Sp
    calc ‖E p * ((S p - E p) * (S q * S p * S p))‖
        ≤ ‖E p‖ * ‖(S p - E p) * (S q * S p * S p)‖ := norm_mul_le _ _
      _ ≤ 1 * (‖S p - E p‖ * ‖S q * S p * S p‖) := by
          rw [hn_Ep]; gcongr; exact norm_mul_le _ _
      _ ≤ 1 * (‖S p - E p‖ * 1) := by gcongr
      _ = ‖S p - E p‖ := by ring
  -- Term 3
  have h3 : ‖E p * E p * ((S q - E q) * (S p * S p))‖ ≤ ‖S q - E q‖ := by
    have hsuff : ‖S p * S p‖ ≤ 1 := hmul1 _ _ hn_Sp hn_Sp
    have hpref : ‖E p * E p‖ ≤ 1 := by
      calc ‖E p * E p‖ ≤ ‖E p‖ * ‖E p‖ := norm_mul_le _ _
        _ = 1 := by rw [hn_Ep]; ring
    calc ‖E p * E p * ((S q - E q) * (S p * S p))‖
        ≤ ‖E p * E p‖ * ‖(S q - E q) * (S p * S p)‖ := norm_mul_le _ _
      _ ≤ 1 * (‖S q - E q‖ * ‖S p * S p‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 * (‖S q - E q‖ * 1) := by gcongr
      _ = ‖S q - E q‖ := by ring
  -- Term 4
  have h4 : ‖E p * E p * E q * ((S p - E p) * S p)‖ ≤ ‖S p - E p‖ := by
    have hpref : ‖E p * E p * E q‖ ≤ 1 :=
      hmul1 _ _ (hmul1 _ _ (le_of_eq hn_Ep) (le_of_eq hn_Ep)) (le_of_eq hn_Eq)
    calc ‖E p * E p * E q * ((S p - E p) * S p)‖
        ≤ ‖E p * E p * E q‖ * ‖(S p - E p) * S p‖ := norm_mul_le _ _
      _ ≤ 1 * (‖S p - E p‖ * ‖S p‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ 1 * (‖S p - E p‖ * 1) := by gcongr
      _ = ‖S p - E p‖ := by ring
  -- Term 5
  have h5 : ‖E p * E p * E q * E p * (S p - E p)‖ ≤ ‖S p - E p‖ := by
    have hpref : ‖E p * E p * E q * E p‖ ≤ 1 :=
      hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (le_of_eq hn_Ep) (le_of_eq hn_Ep))
        (le_of_eq hn_Eq)) (le_of_eq hn_Ep)
    calc ‖E p * E p * E q * E p * (S p - E p)‖
        ≤ ‖E p * E p * E q * E p‖ * ‖S p - E p‖ := norm_mul_le _ _
      _ ≤ 1 * ‖S p - E p‖ := by gcongr
      _ = ‖S p - E p‖ := one_mul _
  -- Step 4: Combine telescoping bound with per-term bounds
  have hred : ‖(S p - E p) * (S p * S q * S p * S p) +
        E p * ((S p - E p) * (S q * S p * S p)) +
        E p * E p * ((S q - E q) * (S p * S p)) +
        E p * E p * E q * ((S p - E p) * S p) +
        E p * E p * E q * E p * (S p - E p)‖
      ≤ ‖S p - E p‖ + ‖S p - E p‖ + ‖S q - E q‖ + ‖S p - E p‖ + ‖S p - E p‖ := by
    linarith
  -- Step 5: Apply norm_strang2_sub_exp_le_abs to each ‖S₂(c,t) - E(c)‖
  have hSp' := norm_strang2_sub_exp_le_abs A B hA hB p ht
  have hSq' := norm_strang2_sub_exp_le_abs A B hA hB q ht
  -- Unfold the let binding in hSp'/hSq' to match our C
  have hSp : ‖S p - E p‖ ≤ C * |p| ^ 3 * t ^ 3 := hSp'
  have hSq : ‖S q - E q‖ ≤ C * |q| ^ 3 * t ^ 3 := hSq'
  -- Step 6: Combine everything
  calc ‖_‖ ≤ ‖S p - E p‖ + ‖S p - E p‖ + ‖S q - E q‖ + ‖S p - E p‖ + ‖S p - E p‖ := hred
    _ ≤ C * |p| ^ 3 * t ^ 3 + C * |p| ^ 3 * t ^ 3 + C * |q| ^ 3 * t ^ 3 +
        C * |p| ^ 3 * t ^ 3 + C * |p| ^ 3 * t ^ 3 := by linarith
    _ = C * (4 * |p| ^ 3 + |q| ^ 3) * t ^ 3 := by ring
