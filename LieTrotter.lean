/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lie–Trotter Product Formula

We prove the Lie–Trotter product formula for elements in a complete normed algebra:

  `exp(A + B) = lim_{n → ∞} (exp(A/n) * exp(B/n))^n`

## Module Structure

- `LieTrotter.Telescoping` — algebraic telescoping identity and norm bound
- `LieTrotter.ExpBounds` — exponential series remainder estimates
- `LieTrotter.StepError` — quadratic error ‖exp(a)exp(b) − exp(a+b)‖
- `LieTrotter.ExpDivPow` — exp(a/n)^n = exp(a)
- `LieTrotter.Assembly` — convergence rate and main theorem
- `LieTrotter.StrangSplitting` — symmetric Lie-Trotter (Strang splitting)
- `LieTrotter.MultiOperator` — multi-operator generalization (A₁+⋯+Aₘ)
- `LieTrotter.MultiStrang` — multi-operator symmetric Strang with O(1/n²)
- `LieTrotter.Suzuki4` — fourth-order Suzuki integrator (five S₂ steps)
- `LieTrotter.CommutatorScaling` — commutator-scaling error via Duhamel formula
- `LieTrotter.Suzuki4UnitaryTotalError` — S₄ total error, anti-Hermitian (no growth factor)
- `LieTrotter.StrangTotalErrorCommScaling` — commutator-scaled Strang total error
- `LieTrotter.Suzuki4Commute` — commuting degeneration: S₄ exact, coefficient zero
- `LieTrotter.TrotterStepCount` — ε-form step counts (n = O((C/ε)^{1/k}))
- `LieTrotter.MatrixCorollaries` — Matrix (Fin d) (Fin d) ℂ specializations, state error
- `LieTrotter.Suzuki4GapClosers` — general-t suzuki4Step + imaginary-time corollaries
- `LieTrotter.PrefactorStrict` — strict γᵢ < αᵢ with 8× termwise gap

## References

* [Trotter, H.F., *On the product of semi-groups of operators*, 1959]
* [Childs, A.M. et al., *Theory of Trotter Error with Commutator Scaling*, Phys. Rev. X, 2021]
-/

import LieTrotter.Telescoping
import LieTrotter.ExpBounds
import LieTrotter.StepError
import LieTrotter.ExpDivPow
import LieTrotter.Assembly
import LieTrotter.StrangSplitting
import LieTrotter.MultiOperator
import LieTrotter.MultiStrang
import LieTrotter.Suzuki4
import LieTrotter.CommutatorScaling
import LieTrotter.MultiCommutatorScaling
import LieTrotter.StrangCommutatorScaling
import LieTrotter.MultiStrangCommutatorScaling
import LieTrotter.HigherCommutator
import LieTrotter.StrangCommutatorScalingTight
import LieTrotter.Suzuki4OrderFive
import LieTrotter.Suzuki4HasDerivAt
import LieTrotter.Suzuki4Module2
import LieTrotter.Suzuki4Module3
import LieTrotter.Suzuki4Module4
import LieTrotter.Suzuki4ChildsForm
import LieTrotter.Suzuki4DerivExplicit
import LieTrotter.Suzuki4Phase5
import LieTrotter.Suzuki4MultinomialExpand
import LieTrotter.Suzuki4StrangBlocks
import LieTrotter.TaylorMatch
import LieTrotter.Suzuki4BchBound
import LieTrotter.Suzuki4ViaBCH
import LieTrotter.Suzuki4Convergence
import LieTrotter.Suzuki4TightConvergence
import LieTrotter.Suzuki4UnitaryTotalError
import LieTrotter.StrangTotalErrorCommScaling
import LieTrotter.Suzuki4Commute
import LieTrotter.TrotterStepCount
import LieTrotter.MatrixCorollaries
import LieTrotter.Suzuki4GapClosers
import LieTrotter.PrefactorStrict
