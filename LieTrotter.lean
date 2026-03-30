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
