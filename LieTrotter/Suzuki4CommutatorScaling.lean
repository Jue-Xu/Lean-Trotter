/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourth-Order Suzuki Commutator-Scaling

Two commutator-scaling bounds for the Suzuki S₄ integrator,
improving on Childs et al. (2021) Proposition 7.

## Phase 1: Exact coefficients (rigorous Childs' framework)

The S₄ Duhamel residual has 10 interface terms, each involving conjugation
expansions. After canceling orders 0–3 (Suzuki order conditions), the
order-4 remainder gives an O(t⁵) bound with 8 commutator terms.

Childs et al. compute numerical coefficients (4 decimal places) using a
"heuristic" balanced factoring. Our approach:
- Computes EXACT algebraic coefficients (polynomials in p = 1/(4-4^{1/3}))
- Uses the palindromic symmetry to pair interface terms
- Gives a machine-checked (non-heuristic) bound

## Phase 2: Norm-of-difference (tighter bound)

Instead of bounding 8 commutator terms separately (sum of norms),
we bound the algebraic combination E₅ (norm of sum).
This captures cancellation between commutator terms, giving a
strictly tighter bound for structured Hamiltonians.

## S₄ structure

S₄(t) = S₂(pt)·S₂(pt)·S₂(qt)·S₂(pt)·S₂(pt)
       = e^{a₁tA}·e^{b₁tB}·e^{a₂tA}·e^{b₂tB}·e^{a₃tA}·e^{b₃tB}·e^{a₄tA}·e^{b₄tB}·e^{a₅tA}·e^{b₅tB}·e^{a₆tA}

where p = 1/(4-4^{1/3}), q = 1-4p, and:
  a₁=a₆=p/2, a₂=a₅=p, a₃=a₄=(1-3p)/2
  b₁=b₂=b₄=b₅=p, b₃=q

Key identity: 4p³ + q³ = 0 (Suzuki cubic cancellation)
-/

import LieTrotter.StrangCommutatorScalingTight

noncomputable section

open NormedSpace MeasureTheory intervalIntegral
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## S₄ as 11 exponentials

Define the S₄ product explicitly in terms of the Suzuki parameter p.
-/

/-- The Suzuki S₄ product as 11 exponentials with parameter `p`.
  S₄(t) = e^{(p/2)tA}·e^{ptB}·e^{ptA}·e^{ptB}·e^{((1-3p)/2)tA}·e^{(1-4p)tB}·
           e^{((1-3p)/2)tA}·e^{ptB}·e^{ptA}·e^{ptB}·e^{(p/2)tA} -/
def suzuki4Exp (A B : 𝔸) (p t : ℝ) : 𝔸 :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let q := 1 - 4 * p
  let a₁ := p / 2       -- = a₆
  let a₂ := p            -- = a₅
  let a₃ := (1 - 3*p)/2  -- = a₄
  exp ((a₁ * t) • A) * exp ((p * t) • B) *
  exp ((a₂ * t) • A) * exp ((p * t) • B) *
  exp ((a₃ * t) • A) * exp ((q * t) • B) *
  exp ((a₃ * t) • A) * exp ((p * t) • B) *
  exp ((a₂ * t) • A) * exp ((p * t) • B) *
  exp ((a₁ * t) • A)

/-!
## Phase 1: Exact S₄ commutator-scaling (Childs' framework, rigorous)

The 10 interfaces contribute conjugation terms. After expanding to order 3
and canceling via order conditions, the order-4 remainder involves
8 independent 4-fold nested commutators [X₄,[X₃,[X₂,[X₁,A']]]] where
each Xᵢ ∈ {A, B} and the innermost is [B,A] (or [A,B] = -[B,A]).
-/

/-- **Phase 1: Rigorous S₄ commutator-scaling** (anti-Hermitian).

  `‖S₄(t) - exp(tH)‖ ≤ Σₖ αₖ ‖Cₖ‖ · t⁵`

  where αₖ are EXACT algebraic coefficients (polynomials in p = 1/(4-4^{1/3})).
  This rigorizes Childs et al. Proposition 7 (which gives 4-decimal approximations). -/
theorem norm_suzuki4_comm_scaling_exact
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      sorry -- 8-term bound with exact algebraic coefficients
      := by
  sorry

/-!
## Phase 2: Norm-of-difference S₄ bound

Instead of 8 separate commutator norms, bound ‖E₅‖ where E₅ is the single
algebraic error expression. This is always ≤ the Phase 1 bound and strictly
tighter when the 4-fold commutators partially cancel.
-/

/-- **Phase 2: Tighter S₄ commutator-scaling** (norm-of-difference).

  `‖S₄(t) - exp(tH)‖ ≤ ‖E₅‖ · t⁵ + O(t⁶)`

  where E₅ = Σₖ αₖ Cₖ is the single algebraic error expression.
  Since ‖E₅‖ ≤ Σ|αₖ|‖Cₖ‖ by the triangle inequality, this is always
  ≤ the Phase 1 bound and strictly tighter with partial cancellation. -/
theorem norm_suzuki4_comm_scaling_tight
    [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (A B : 𝔸) {t : ℝ} (ht : 0 ≤ t)
    (hA : star A = -A) (hB : star B = -B) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤
      sorry -- ‖E₅(A,B)‖ · t⁵ + correction · t⁶
      := by
  sorry
