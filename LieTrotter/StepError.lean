/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track C: Quadratic Step Error

The key estimate: ‖exp(a)exp(b) - exp(a+b)‖ ≤ 2‖a‖‖b‖ exp(‖a‖+‖b‖)
and its specialization to the Lie-Trotter step with a = A/n, b = B/n.
-/

import LieTrotter.ExpBounds

open NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-!
## C1: Quadratic error bound (HARDEST LEMMA)

`‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`

Recommended approach: second-order expansion.
Write `exp(a) = 1 + a + Rₐ`, `exp(b) = 1 + b + R_b` with
`‖Rₐ‖ ≤ ‖a‖²/2 · exp(‖a‖)` (from B4).
Then expand the product and bound each cross term.
-/

/-- **Key estimate**: `‖exp(a) exp(b) - exp(a+b)‖ ≤ 2 ‖a‖ ‖b‖ exp(‖a‖+‖b‖)`.
    This is the hardest lemma in the formalization. -/
theorem norm_exp_mul_exp_sub_exp_add' (a b : 𝔸) :
    ‖exp 𝕂 a * exp 𝕂 b - exp 𝕂 (a + b)‖ ≤
      2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
  /- Proof sketch:
     Write exp(a) = 1 + a + R_a where R_a = exp(a) - 1 - a
     Write exp(b) = 1 + b + R_b

     exp(a) * exp(b) = (1 + a + R_a)(1 + b + R_b)
                     = 1 + a + b + ab + R_a + R_b + a*R_b + R_a*b + R_a*R_b

     exp(a+b) = 1 + (a+b) + R_{a+b}

     Difference = ab + R_a + R_b + a*R_b + R_a*b + R_a*R_b - R_{a+b}

     Bound each piece using B4 (norm_exp_sub_one_sub_le). -/
  sorry

/-!
## C2: Lie-Trotter step error

Specialization of C1 to `a = A/n`, `b = B/n`:
`‖exp(A/n) exp(B/n) - exp((A+B)/n)‖ ≤ 2‖A‖‖B‖/n² · exp((‖A‖+‖B‖)/n)`
-/

/-- The quadratic step error for Lie-Trotter:
    `‖exp(A/n) exp(B/n) - exp((A+B)/n)‖ ≤ 2‖A‖‖B‖/n² · exp((‖A‖+‖B‖)/n)`. -/
theorem lie_trotter_step_error (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B) -
     exp 𝕂 ((n : 𝕂)⁻¹ • (A + B))‖ ≤
      2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / n) := by
  -- Apply norm_exp_mul_exp_sub_exp_add' with a = A/n, b = B/n
  -- Use ‖(n:𝕂)⁻¹ • A‖ = ‖A‖/n via norm_smul and norm_inv
  sorry
