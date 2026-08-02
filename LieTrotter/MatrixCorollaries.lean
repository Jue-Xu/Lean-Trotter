/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix Specializations: Quantum-Simulation Form of the Headline Theorems

Task F1 (long-open "nice-to-have"): the headline product-formula theorems,
specialized to `Matrix (Fin d) (Fin d) ℂ` equipped with the **L2 operator
norm** (spectral norm) — the norm actually used in quantum-simulation error
analysis.  For a quantum Hamiltonian `H = H₁ + H₂` one takes `A = -i·t·H₁`,
`B = -i·t·H₂` (skew-Hermitian), and the results below are then literal
Hamiltonian-simulation error bounds:

* `matrix_lie_trotter`          — `(e^{A/n} e^{B/n})^n → e^{A+B}`, O(1/n);
* `matrix_symmetric_lie_trotter`— Strang splitting, O(1/n²);
* `matrix_suzuki4_total_error_quartic` / `matrix_suzuki4_convergence_quartic`
                                — Suzuki S₄, total error ≤ C/n⁴;
* `matrix_suzuki4_state_error`  — the *state* error: for every input state
  `ψ`, `‖S₄(t/n)ⁿ ψ − e^{t(A+B)} ψ‖ ≤ C/n⁴ · ‖ψ‖` in the Euclidean (ℓ²)
  norm, via the defining property of the spectral norm.

## Instances

Everything is a one-line application of the abstract theorems; the real
content is that Mathlib's scoped `Matrix.Norms.L2Operator` instances now
provide the full typeclass context the abstract theorems demand:

* `Matrix.instL2OpNormedRing` / `instL2OpNormedAlgebra`
  (`Mathlib.Analysis.CStarAlgebra.Matrix`) — spectral-norm ring/algebra;
* `Matrix.instCStarRing` + `Matrix.nonempty` (needs `[NeZero d]`) —
  `NormOneClass` via `CStarRing.norm_one`;
* `Matrix.instCompleteSpace` (`Mathlib.Topology.UniformSpace.Matrix`) —
  the L2Op metric is built by `replaceUniformity`, so completeness of the
  entrywise uniformity transfers;
* `NormedAlgebra.complexToReal` — the ℝ-algebra structure required by the
  S₄ results (which live over `NormedAlgebra ℝ 𝔸`).

`[NeZero d]` is genuinely needed: for `d = 0` the zero algebra has `‖1‖ = 0`,
so `NormOneClass` fails (and the theorems are vacuous anyway).
-/

import LieTrotter.Assembly
import LieTrotter.StrangSplitting
import LieTrotter.Suzuki4Convergence
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.UniformSpace.Matrix

noncomputable section

open Filter Topology NormedSpace
open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} [NeZero d]

/-!
## First- and second-order product formulas (over ℂ)
-/

/-- **Lie–Trotter product formula for complex matrices** (spectral norm).
For `A = -i·H₁`, `B = -i·H₂` skew-Hermitian this is the first-order
Hamiltonian-simulation error statement `(e^{A/n} e^{B/n})^n → e^{A+B}`,
with O(1/n) rate from `lie_trotter_error_rate`. -/
theorem matrix_lie_trotter (A B : Matrix (Fin d) (Fin d) ℂ) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : ℂ)⁻¹ • A) * exp ((n : ℂ)⁻¹ • B)) ^ n)
      atTop (nhds (exp (A + B))) :=
  lie_trotter (𝕂 := ℂ) A B

/-- **Strang (symmetric Trotter) product formula for complex matrices**
(spectral norm): `(e^{A/2n} e^{B/n} e^{A/2n})^n → e^{A+B}`, with O(1/n²)
rate from `strang_error_rate_sq`. -/
theorem matrix_symmetric_lie_trotter (A B : Matrix (Fin d) (Fin d) ℂ) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((2 * (n : ℂ))⁻¹ • A) * exp ((n : ℂ)⁻¹ • B) *
                      exp ((2 * (n : ℂ))⁻¹ • A)) ^ n)
      atTop (nhds (exp (A + B))) :=
  symmetric_lie_trotter (𝕂 := ℂ) A B

/-!
## Suzuki S₄: fourth-order convergence (over ℝ-scalars)

`suzuki4Exp` and the S₄ convergence theorems live over `NormedAlgebra ℝ 𝔸`;
the instance for complex matrices is found through
`NormedAlgebra.complexToReal`.
-/

/-- **S₄ total error for complex matrices** (spectral norm): under the Suzuki
cubic condition `4p³ + (1−4p)³ = 0`,
`‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴` for all `n ≥ N`.  This is the operator-norm
error bound quoted in fourth-order Hamiltonian-simulation gate counts. -/
theorem matrix_suzuki4_total_error_quartic (A B : Matrix (Fin d) (Fin d) ℂ)
    (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖ ≤ C / (n : ℝ) ^ 4 :=
  suzuki4_total_error_quartic A B p hp t

/-- **S₄ convergence for complex matrices** (spectral norm):
`S₄(t/n)ⁿ → exp(t(A+B))`, at rate O(1/n⁴) by
`matrix_suzuki4_total_error_quartic`. -/
theorem matrix_suzuki4_convergence_quartic (A B : Matrix (Fin d) (Fin d) ℂ)
    (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Exp A B p (t / (n : ℝ))) ^ n)
      atTop (nhds (exp (t • (A + B)))) :=
  suzuki4_convergence_quartic A B p hp t

/-- The standard Suzuki parameter `p = 1/(4 − 4^{1/3})` satisfies the cubic
condition, so the matrix S₄ total-error bound holds hypothesis-free. -/
theorem matrix_suzuki4_total_error_quartic_suzukiP (A B : Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) (t / (n : ℝ))) ^ n -
        exp (t • (A + B))‖ ≤ C / (n : ℝ) ^ 4 :=
  suzuki4_total_error_quartic_suzukiP A B t

/-- Hypothesis-free matrix S₄ convergence at the standard Suzuki parameter. -/
theorem matrix_suzuki4_convergence_quartic_suzukiP (A B : Matrix (Fin d) (Fin d) ℂ)
    (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (suzuki4Exp A B (1 / (4 - (4 : ℝ) ^ ((1 : ℝ) / 3))) (t / (n : ℝ))) ^ n)
      atTop (nhds (exp (t • (A + B)))) :=
  suzuki4_convergence_quartic_suzukiP A B t

/-!
## State error

Quantum simulation cares about the error on *states*: for an input state `ψ`
(a vector in `EuclideanSpace ℂ (Fin d)`, i.e. ℓ²-normed), the deviation of the
S₄-evolved state from the exactly-evolved state.  The spectral norm is
*defined* as the ℓ²→ℓ² operator norm, so this is one application of
`Matrix.l2_opNorm_mulVec` to the error operator. -/

/-- **S₄ state error** (fourth order): for every input state `ψ`,
`‖S₄(t/n)ⁿ ψ − exp(t(A+B)) ψ‖ ≤ C/n⁴ · ‖ψ‖` in the Euclidean norm, with a
single constant `C` uniform in `ψ`.  For normalized states (`‖ψ‖ = 1`) the
right-hand side is just `C/n⁴`. -/
theorem matrix_suzuki4_state_error (A B : Matrix (Fin d) (Fin d) ℂ)
    (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ ψ : EuclideanSpace ℂ (Fin d),
        ‖(EuclideanSpace.equiv (Fin d) ℂ).symm
            ((suzuki4Exp A B p (t / (n : ℝ))) ^ n *ᵥ ψ) -
          (EuclideanSpace.equiv (Fin d) ℂ).symm (exp (t • (A + B)) *ᵥ ψ)‖
          ≤ C / (n : ℝ) ^ 4 * ‖ψ‖ := by
  obtain ⟨C, hC_pos, N, hN_pos, hbound⟩ := suzuki4_total_error_quartic A B p hp t
  refine ⟨C, hC_pos, N, hN_pos, fun n hn ψ => ?_⟩
  rw [← map_sub, ← Matrix.sub_mulVec]
  calc ‖(EuclideanSpace.equiv (Fin d) ℂ).symm
          (((suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))) *ᵥ ψ)‖
      ≤ ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖ * ‖ψ‖ :=
        Matrix.l2_opNorm_mulVec _ ψ
    _ ≤ C / (n : ℝ) ^ 4 * ‖ψ‖ :=
        mul_le_mul_of_nonneg_right (hbound n hn) (norm_nonneg ψ)

end
