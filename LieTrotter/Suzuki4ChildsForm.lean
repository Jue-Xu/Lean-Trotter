/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Error Bound in Childs's Explicit-Prefactor Form

This module re-states Childs et al. (2021) Proposition pf4_bound_2term in
Lean and provides a CONDITIONAL reduction to it via Module 3.

## Childs Proposition pf4_bound_2term

For a Hamiltonian H = A + B and the fourth-order Suzuki formula `S₄`:

  ‖S₄(t) - exp(-itH)‖ ≤ t⁵ · (
    0.0047 · ‖[A,[A,[A,[B,A]]]]‖ +
    0.0057 · ‖[A,[A,[B,[B,A]]]]‖ +
    0.0046 · ‖[A,[B,[A,[B,A]]]]‖ +
    0.0074 · ‖[A,[B,[B,[B,A]]]]‖ +
    0.0097 · ‖[B,[A,[A,[B,A]]]]‖ +
    0.0097 · ‖[B,[A,[B,[B,A]]]]‖ +
    0.0173 · ‖[B,[B,[A,[B,A]]]]‖ +
    0.0284 · ‖[B,[B,[B,[B,A]]]]‖
  )

The 8 4-fold nested commutators enumerate the choices `[X₁,[X₂,[X₃,[B,A]]]]`
with `X_i ∈ {A, B}` (innermost forced to `[B,A]` since `[A,A] = 0`).

Childs et al. note that "we do not have a rigorous proof of the tightness
of these bounds" — the coefficients come from a heuristic balanced
factoring in the 12-factor Duhamel.

## What this module provides

- `commBr` shorthand for `[X, Y] = X·Y - Y·X` and a list of the 8 Childs
  commutators (`childsComm₁` through `childsComm₈`)
- `childsBoundSum`: the Childs RHS as a single sum
- `norm_suzuki4_childs_via_residual` (PROVED): the CONDITIONAL theorem
  showing that a Childs-style residual hypothesis on `w4Deriv` gives the
  Childs-form integrated bound
- `norm_suzuki4_childs_form`: the headline Proposition pf4_bound_2term
  from Childs et al., closed with an explicit residual-bound hypothesis
  `hResidual : ∀ τ ∈ [0,t], ‖w4Deriv τ‖ ≤ 5·childsBoundSum·τ⁴` (discharged
  via `norm_suzuki4_childs_via_residual`). The remaining research content
  is proving this pointwise bound from the Suzuki order conditions; see
  `Suzuki4Phase5.lean` for the architectural reduction.

## Caveats

1. **Numerical coefficients.** Childs's 0.0047 etc. are 4-decimal
   approximations of rational expressions in the Suzuki parameter
   `p = 1/(4-r)` where `r³ = 4`. The Lean theorem uses these decimal
   values literally; deriving exact algebraic forms is part of Module 4b.
2. **Sign conventions.** Childs writes `e^{-itH}`; we use `e^{tH}` (with
   `tH` for anti-Hermitian H). The two conventions agree when the algebra
   embeds Pauli matrices with `H = iH'` for Hermitian `H'`.
-/

import LieTrotter.Suzuki4Module3
import LieTrotter.Suzuki4Module4

noncomputable section

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## The 8 Childs commutators

We enumerate `[X₁, [X₂, [X₃, [B, A]]]]` for `X₁, X₂, X₃ ∈ {A, B}`.
-/

/-- Plain commutator `[X, Y] = X·Y - Y·X`. -/
def commBr (X Y : 𝔸) : 𝔸 := X * Y - Y * X

@[inherit_doc] notation "⟦" X ", " Y "⟧" => commBr X Y

/-- Childs commutator 1: `[A,[A,[A,[B,A]]]]`. -/
def childsComm₁ (A B : 𝔸) : 𝔸 := commBr A (commBr A (commBr A (commBr B A)))

/-- Childs commutator 2: `[A,[A,[B,[B,A]]]]`. -/
def childsComm₂ (A B : 𝔸) : 𝔸 := commBr A (commBr A (commBr B (commBr B A)))

/-- Childs commutator 3: `[A,[B,[A,[B,A]]]]`. -/
def childsComm₃ (A B : 𝔸) : 𝔸 := commBr A (commBr B (commBr A (commBr B A)))

/-- Childs commutator 4: `[A,[B,[B,[B,A]]]]`. -/
def childsComm₄ (A B : 𝔸) : 𝔸 := commBr A (commBr B (commBr B (commBr B A)))

/-- Childs commutator 5: `[B,[A,[A,[B,A]]]]`. -/
def childsComm₅ (A B : 𝔸) : 𝔸 := commBr B (commBr A (commBr A (commBr B A)))

/-- Childs commutator 6: `[B,[A,[B,[B,A]]]]`. -/
def childsComm₆ (A B : 𝔸) : 𝔸 := commBr B (commBr A (commBr B (commBr B A)))

/-- Childs commutator 7: `[B,[B,[A,[B,A]]]]`. -/
def childsComm₇ (A B : 𝔸) : 𝔸 := commBr B (commBr B (commBr A (commBr B A)))

/-- Childs commutator 8: `[B,[B,[B,[B,A]]]]`. -/
def childsComm₈ (A B : 𝔸) : 𝔸 := commBr B (commBr B (commBr B (commBr B A)))

/-!
## Childs's bound RHS as a sum

The 8 commutator-norm terms with their Childs coefficients (4-decimal
approximations from the heuristic balanced factoring).
-/

/-- The Childs RHS sum: `Σⱼ αⱼ · ‖Cⱼ‖` for the 8 commutators. -/
def childsBoundSum (A B : 𝔸) : ℝ :=
  0.0047 * ‖childsComm₁ A B‖ +
  0.0057 * ‖childsComm₂ A B‖ +
  0.0046 * ‖childsComm₃ A B‖ +
  0.0074 * ‖childsComm₄ A B‖ +
  0.0097 * ‖childsComm₅ A B‖ +
  0.0097 * ‖childsComm₆ A B‖ +
  0.0173 * ‖childsComm₇ A B‖ +
  0.0284 * ‖childsComm₈ A B‖

lemma childsBoundSum_nonneg (A B : 𝔸) : 0 ≤ childsBoundSum A B := by
  unfold childsBoundSum
  positivity

/-!
## Conditional reduction: Childs-form residual → Childs-form integrated bound

Given a residual hypothesis `‖w4Deriv τ‖ ≤ 5 · childsBoundSum · τ⁴`
(matching Childs's leading-order structure with the integration factor
of 5 absorbed), the integrated bound matches Childs's exactly.
-/

section AntiHermitian

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **Childs-form S₄ bound** (CONDITIONAL on the Childs-form residual).

  If the Duhamel residual is bounded by `5 · childsBoundSum · τ⁴`
  on `[0, t]`, then the integrated S₄ error matches Childs et al.
  Proposition pf4_bound_2term exactly:

    ‖S₄(t) - exp(tH)‖ ≤ t⁵ · childsBoundSum

  The factor of 5 in the residual hypothesis comes from
  `∫₀ᵗ τ⁴ dτ = t⁵/5` (the FTC-2 reduction in Module 3 introduces /5). -/
theorem norm_suzuki4_childs_via_residual (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hBound : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖w4Deriv A B p τ‖ ≤ (5 * childsBoundSum A B) * τ ^ 4) :
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ t ^ 5 * childsBoundSum A B := by
  -- Apply Module 3's FTC-2 reduction with C = 5 · childsBoundSum
  have hCont : Continuous (w4Deriv A B p) := continuous_w4Deriv A B p
  have hC_nn : 0 ≤ 5 * childsBoundSum A B := by
    have := childsBoundSum_nonneg A B
    positivity
  have h := norm_suzuki4_order5_via_module3 A B hA hB p ht hCont hC_nn hBound
  -- h : ‖S₄ - exp(tH)‖ ≤ (5 · childsBoundSum) / 5 · t⁵
  -- which simplifies to childsBoundSum · t⁵
  calc ‖suzuki4Exp A B p t - exp (t • (A + B))‖
      ≤ (5 * childsBoundSum A B) / 5 * t ^ 5 := h
    _ = t ^ 5 * childsBoundSum A B := by ring

/-- **Childs Proposition pf4_bound_2term** (with explicit residual hypothesis).

  The unconditional Childs bound, closed by taking the Module 4b residual
  bound as an explicit hypothesis `hResidual`. The conditional reduction
  `norm_suzuki4_childs_via_residual` (above) handles the integration step.

  The hypothesis is exactly the remaining Module 4b research target:
  `‖w4Deriv τ‖ ≤ 5 · childsBoundSum · τ⁴` for the Suzuki parameter
  `p = 1/(4 - 4^{1/3})`. Providing it closes the theorem. See
  `Suzuki4Phase5.lean` for the architectural reduction of this hypothesis
  to three concrete `iteratedDeriv` identities on `s4Func` at τ=0. -/
theorem norm_suzuki4_childs_form (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) {t : ℝ} (ht : 0 ≤ t) :
    let p : ℝ := 1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))
    (∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖w4Deriv A B p τ‖ ≤ (5 * childsBoundSum A B) * τ ^ 4) →
    ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ t ^ 5 * childsBoundSum A B := by
  intro p hResidual
  exact norm_suzuki4_childs_via_residual A B hA hB p ht hResidual

end AntiHermitian

/-!
## Status

**Provided (PROVED):**
- Definitions of the 8 Childs commutators (`childsComm₁`–`childsComm₈`)
- `childsBoundSum`: the Childs RHS sum
- `childsBoundSum_nonneg`: positivity
- `norm_suzuki4_childs_via_residual`: CONDITIONAL Childs-form bound (uses Module 3 + Module 4a)
- `norm_suzuki4_childs_form`: Childs bound with explicit residual hypothesis

**Architecture:**

```
Module 1 ✅ → Module 2 ✅ → Module 3 ✅ + Module 4a ✅
                                  ↓
                Module 4b (residual bound as HYPOTHESIS)
                ── as Childs's 8-term form: childsBoundSum
                                  ↓
              norm_suzuki4_childs_via_residual ✅ (conditional)
                                  ↓
              norm_suzuki4_childs_form ✅ (takes residual bound as hypothesis)
```

This module makes Childs Proposition pf4_bound_2term explicit in the
project, providing concrete commutator definitions and showing the
clean reduction path via Module 3. The theorem statement requires the
pointwise residual bound as an input; proving this bound from the Suzuki
order conditions is the remaining Module 4b research (see Suzuki4Phase5.lean
for the architectural reduction to three concrete iteratedDeriv identities).
-/

end
