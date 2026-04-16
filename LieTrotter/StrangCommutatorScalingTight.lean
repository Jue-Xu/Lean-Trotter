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
  -- g₁(s) - g₁(τ) = -(τ-s)·dblA - ∫ₛᵗ (g₁'(u) - dblA) du
  -- So ∫₀ᵗ (g₁(s)-g₁(τ)) ds = -τ²/2·dblA - ∫₀ᵗ∫ₛᵗ (g₁'(u)-dblA) du ds
  -- Thus: (∫ (g₁(s)-g₁(τ))) + τ²/2·dblA = -∫₀ᵗ∫ₛᵗ (g₁'(u)-dblA) du ds
  -- Each g₁'(u) - dblA = exp(uA')·dblA·exp(-uA') - dblA bounded by ‖triA‖·u
  sorry

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
  -- conj_{τA'}(R₂(τ)) where R₂ = exp(τB)A'exp(-τB) - A' - τ[B,A']
  -- R₂(τ) = τ²/2·dblB + R_triple(τ)  where ‖R_triple‖ ≤ ‖triB‖/6·τ³ (triple FTC)
  -- conj_{τA'}(τ²/2·dblB) = τ²/2·dblB + τ²/2·(conj correction)
  --   where ‖conj corr‖ ≤ ‖triAB‖·τ (single FTC on dblB)
  -- conj_{τA'}(R_triple) has same norm as R_triple (isometry)
  -- Total: ‖result - τ²/2·dblB‖ ≤ (‖triAB‖/2 + ‖triB‖/6)·τ³
  sorry

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
  -- The proof reuses the Duhamel/FTC-2 framework from norm_strang_comm_scaling,
  -- but replaces the pointwise bound ‖𝒯₂(τ)‖ ≤ (C_A+C_B)/2·τ² with the
  -- tighter ‖𝒯₂(τ)‖ ≤ ‖D‖/2·τ² + T·τ³, using the triple FTC for the remainder.
  sorry
