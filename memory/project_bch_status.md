---
name: BCH project status
description: Lean-BCH formalization progress — Phase 2 complete (0 sorry's), next steps toward truncated BCH
type: project
---

## Current state (2026-03-31)

**Phase 1-2 complete: 0 sorry's, full build passes.**

Proved theorems:
- `exp_logOnePlus`: `exp(logOnePlus(x)) = 1 + x` for `‖x‖ < 1`
- `logOnePlus_exp_sub_one`: `logOnePlus(exp(a)-1) = a` for `‖a‖ < ln 2`
- `exp_bch`: `exp(bch(a,b)) = exp(a)·exp(b)` for `‖a‖+‖b‖ < ln 2`
- `norm_bch_sub_add_le`: `‖bch(a,b)-(a+b)‖ ≤ 3s²/(2-exp(s))` (bound was corrected from incorrect `2s²·exp(s)`)

## Remaining goals (from README)

1. **Truncated BCH to order 3**: Extract commutator `[a,b]/2` from `bch(a,b)-(a+b)` and bound the cubic remainder `R₃`. This is the main goal.
2. **Symmetric BCH**: `exp(A/2)exp(B)exp(A/2) = exp(A+B+c₃[A,[A,B]]+O(‖A‖³‖B‖))` — needed for fourth-order Suzuki in Lean-Trotter.
3. **Lie bracket ↔ ring commutator bridge**: Connect Mathlib's `⁅·,·⁆` to `AB-BA`.

**Why:** The Lean-Trotter project needs the symmetric BCH for the Suzuki S₄ integrator's O(1/n⁴) convergence rate.

**How to apply:** When working on Lean-BCH, focus on extracting the commutator term next. The quadratic bound is proved; the cubic refinement requires showing `bch(a,b) - (a+b) - [a,b]/2` is O(‖a‖²‖b‖ + ‖a‖‖b‖²).
