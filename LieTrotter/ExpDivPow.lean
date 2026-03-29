/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track D: Exponential Power Identity

  D1. exp(a/n)^n = exp(a)
  D2. ‖exp(c•a)‖ ≤ exp(‖c‖ ‖a‖)
-/

import LieTrotter.ExpBounds

open NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-!
## D1: exp(a/n)^n = exp(a)

Key identity: since `a/n` commutes with itself, we get
`exp(a/n)^n = exp(n • a/n) = exp(a)` by `exp_nsmul`.

The scalar algebra step `n • (n⁻¹ • a) = a` uses `smul_smul` + `mul_inv_cancel`.
-/

/-- `exp(a/n)^n = exp(a)` in a complete normed algebra. -/
lemma exp_div_pow (a : 𝔸) (n : ℕ) (hn : 0 < n) :
    (exp 𝕂 ((n : 𝕂)⁻¹ • a)) ^ n = exp 𝕂 a := by
  -- Mathlib has NormedSpace.exp_nsmul: exp(n • x) = exp(x) ^ n
  -- So exp(x)^n = exp(n • x)
  -- With x = (n:𝕂)⁻¹ • a: exp((n:𝕂)⁻¹ • a)^n = exp(n • ((n:𝕂)⁻¹ • a))
  -- n • ((n:𝕂)⁻¹ • a) = (n : 𝕂) • ((n:𝕂)⁻¹ • a) = (n * n⁻¹) • a = 1 • a = a
  sorry

/-!
## D2: Norm bound for scalar-smul exponential

`‖exp(c • a)‖ ≤ exp(‖c‖ · ‖a‖)` from B1 and `‖c • a‖ ≤ ‖c‖ · ‖a‖`.
-/

/-- `‖exp(c • a)‖ ≤ exp(‖c‖ · ‖a‖)`. -/
lemma norm_exp_smul_le (c : 𝕂) (a : 𝔸) :
    ‖exp 𝕂 (c • a)‖ ≤ Real.exp (‖c‖ * ‖a‖) := by
  calc ‖exp 𝕂 (c • a)‖
      ≤ Real.exp ‖c • a‖ := norm_exp_le (c • a)
    _ ≤ Real.exp (‖c‖ * ‖a‖) := by
        gcongr
        exact norm_smul_le c a
