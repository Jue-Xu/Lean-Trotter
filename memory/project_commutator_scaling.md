---
name: Commutator-scaling implementation status
description: CommutatorScaling.lean complete (0 sorry's), uses NormedAlgebra ℝ not general 𝕂, bound has t² not t²/2
type: project
---

## Current state (2026-04-14)

**CommutatorScaling.lean: 370 lines, 0 sorry's, full build passes.**

Proved commutator-scaling Trotter error bound from Childs et al. (2021):
- `lie_trotter_integral_error`: Duhamel integral representation of Trotter error
- `norm_lie_trotter_comm_scaling`: `‖exp(tB)exp(tA) - exp(t(A+B))‖ ≤ ‖[B,A]‖ · t² · exp(t(‖A‖+3‖B‖))`

**Key design choice:** Uses `NormedAlgebra ℝ 𝔸` (not general `𝕂`) because `HasDerivAt`/`intervalIntegral` need `SMul ℝ 𝔸`, which isn't auto-synthesized from `[RCLike 𝕂] [NormedAlgebra 𝕂 𝔸]`. For ℂ applications, use `NormedAlgebra.restrictScalars`.

**Why:** Replaces `‖A‖‖B‖` with `‖[B,A]‖` — tighter when operators nearly commute. This is the theoretical foundation of commutator-scaling quantum simulation complexity.

**How to apply:** Existing `norm_exp_mul_exp_sub_exp_add'` (StepError.lean) gives `2‖a‖‖b‖`. The new bound gives `‖[b,a]‖` (always ≤ 2‖a‖‖b‖, often much smaller). Use whichever is tighter for the application.

## Remaining improvements

1. **Tighten t² → t²/2**: Requires `norm_integral_le_of_norm_le` (non-constant) + `integral_pow` to evaluate `∫₀ᵗ τ dτ = t²/2`
2. **n-step assembly**: Apply with `t = 1/n`, assemble via telescoping (parallels Assembly.lean)
3. **Strang commutator scaling**: Same Duhamel approach for symmetric splitting → double commutator bound
