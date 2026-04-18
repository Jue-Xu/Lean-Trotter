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
## S₄ commutator-scaling theorems

The Phase 1/Phase 2 stub theorems originally placed here have been
SUPERSEDED by the explicit Module 1-3 architecture in:
- `LieTrotter.Suzuki4HasDerivAt` (Module 1: HasDerivAt)
- `LieTrotter.Suzuki4Module2` (Module 2: FTC-2 bridge)
- `LieTrotter.Suzuki4Module3` (Module 3: FTC-2 reduction)

The conditional O(t⁵) S₄ bound is provided by
`LieTrotter.Suzuki4Module3.norm_suzuki4_order5_via_module3`, which gives
a CLEAN reduction to a pointwise residual bound on `w4Deriv A B p τ`.

The full form with explicit residual-bound hypothesis is
`LieTrotter.Suzuki4OrderFive.norm_suzuki4_fifth_order` — closed using
`norm_suzuki4_order5_via_module3` after providing the pointwise bound
on `w4Deriv`. The remaining research content is proving this bound from
the Suzuki order conditions (see `Suzuki4Phase5.lean`).
-/
