/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S₄ Gap Closers: General-`t` `suzuki4Step` Rescaling + Imaginary-Time Corollaries

Two small gaps between the formalization and the manuscript's prose are closed
here, with no new analysis — everything is a rescaling of already-proved
theorems.

## 1. General-`t` total error in the `suzuki4Step` spelling

`suzuki4Step 𝕂 A B p n` (from `Suzuki4.lean`) has the physical time `t = 1`
built in: every factor carries `1/n`.  `Suzuki4Convergence.lean` upgraded it to
O(1/n⁴) at `t = 1` (`suzuki4Step_total_error_quartic`), while the free-`t`
statement existed only in the `suzuki4Exp` spelling
(`suzuki4_total_error_quartic`).  The manuscript covers general `t` for
`suzuki4Step` by the prose remark "rescale `A → tA`, `B → tB`" — here that
remark becomes a theorem.  The key identity is pure smul bookkeeping:

  `suzuki4Exp (t•A) (t•B) p τ = suzuki4Exp A B p (t*τ)`  (`suzuki4Exp_smul_smul`)

whence `suzuki4Step ℝ (t•A) (t•B) p n = suzuki4Exp A B p (t/n)`
(`suzuki4Step_smul_eq_suzuki4Exp`), and the O(1/n⁴) total error transports to
the rescaled `suzuki4Step` (`suzuki4Step_total_error_quartic_general`,
`suzuki4Step_convergence_quartic_general`).

## 2. Imaginary-time / Gibbs corollaries

The Trotter theorems of this development are stated for arbitrary elements of a
complete normed algebra — **no self-adjointness, anti-Hermitian structure,
positivity, or unitarity is assumed anywhere in the hypotheses**.  In
particular they already cover the *imaginary-time* (Euclidean / Gibbs)
factorization

  `exp(-β(A+B)) = lim_n (exp(-βA/n) · exp(-βB/n))^n`,

where the one-step factors are **not** unitary and the generator `-β(A+B)` is
**not** anti-Hermitian: the generic Banach-algebra generality is the point.
The named corollaries below (`gibbs_lie_trotter`, `gibbs_symmetric_lie_trotter`,
`gibbs_suzuki4_convergence`, …) are thin instantiations of `lie_trotter`,
`symmetric_lie_trotter` and `suzuki4_convergence_quartic` at the rescaled
operators `(-β)•A`, `(-β)•B` (equivalently, at time `t = -β`).  Their value is
the citable statement: Gibbs-state Trotterization needs no new proof.

No hypothesis restricts the sign of `β`; "inverse temperature" is only the
intended reading.
-/

import LieTrotter.Suzuki4Convergence

noncomputable section

open NormedSpace Filter Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Rescaling `suzuki4Exp`: operators `t•A, t•B` at step `τ` = operators `A, B` at step `t·τ`

Every factor of the 11-exponential product is `exp((c·τ) • (t•A)) =
exp((c·(t·τ)) • A)`, by `smul_smul` and commutativity of `ℝ`.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- **S₄ rescaling identity**: running S₄ on the rescaled operators `t•A, t•B`
with step size `τ` is the same algebra element as running it on `A, B` with
step size `t·τ`.  Pure smul bookkeeping — no analysis. -/
lemma suzuki4Exp_smul_smul (A B : 𝔸) (p t τ : ℝ) :
    suzuki4Exp (t • A) (t • B) p τ = suzuki4Exp A B p (t * τ) := by
  have h : ∀ (c : ℝ) (X : 𝔸), (c * τ) • (t • X) = (c * (t * τ)) • X := fun c X => by
    rw [smul_smul, show c * τ * t = c * (t * τ) from by ring]
  unfold suzuki4Exp
  simp only [h]

/-- **Rescaled-step bridge**: the `1/n`-built-in `suzuki4Step` on the rescaled
operators `t•A, t•B` is `suzuki4Exp A B p` at step size `t/n`.  Composes the
rescaling identity `suzuki4Exp_smul_smul` with the spelling bridge
`suzuki4Step_eq_suzuki4Exp`. -/
lemma suzuki4Step_smul_eq_suzuki4Exp (A B : 𝔸) (p t : ℝ) (n : ℕ) :
    suzuki4Step ℝ (t • A) (t • B) p n = suzuki4Exp A B p (t / (n : ℝ)) := by
  rw [suzuki4Step_eq_suzuki4Exp, suzuki4Exp_smul_smul, ← div_eq_mul_inv]

/-!
## General-`t` total error and convergence for `suzuki4Step`

The `suzuki4Step` spelling of `suzuki4_total_error_quartic` /
`suzuki4_convergence_quartic`: simulate `exp(t(A+B))` by running the unit-time
integrator on the rescaled operators `tA, tB`.  This formalizes the
manuscript's "follows by rescaling `A → tA, B → tB`" remark.  (The target is
written `t • (A + B)`; `smul_add` converts it to `t•A + t•B`, the sum of the
rescaled operators.)
-/

/-- **General-`t` `suzuki4Step` total error, O(1/n⁴).**  Under the Suzuki cubic
condition, the unit-time five-`strangStep` integrator applied to the rescaled
operators `t•A, t•B` approximates `exp(t(A+B))` at fourth order:

  `‖suzuki4Step(tA, tB, n)ⁿ - exp(t(A+B))‖ ≤ C/n⁴`   for `n ≥ N`.

The `t = 1` case is `suzuki4Step_total_error_quartic`. -/
theorem suzuki4Step_total_error_quartic_general (A B : 𝔸) (p : ℝ)
    (hp : IsSuzukiCubic p) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Step ℝ (t • A) (t • B) p n) ^ n - exp (t • (A + B))‖ ≤
        C / (n : ℝ) ^ 4 := by
  obtain ⟨C, hC_pos, N, hN_pos, hbound⟩ := suzuki4_total_error_quartic A B p hp t
  refine ⟨C, hC_pos, N, hN_pos, fun n hn => ?_⟩
  rw [suzuki4Step_smul_eq_suzuki4Exp]
  exact hbound n hn

/-- **General-`t` `suzuki4Step` convergence**: `suzuki4Step(tA, tB, n)ⁿ →
exp(t(A+B))`, at rate O(1/n⁴) by `suzuki4Step_total_error_quartic_general`.
The `t = 1` case is `suzuki4Step_convergence_quartic`. -/
theorem suzuki4Step_convergence_quartic_general (A B : 𝔸) (p : ℝ)
    (hp : IsSuzukiCubic p) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Step ℝ (t • A) (t • B) p n) ^ n)
      atTop (nhds (exp (t • (A + B)))) := by
  simpa only [suzuki4Step_smul_eq_suzuki4Exp] using
    suzuki4_convergence_quartic A B p hp t

/-!
## Imaginary-time (Gibbs) corollaries

`exp(-β(A+B))` — the (unnormalized) Gibbs factorization at inverse temperature
`β` — is covered by the *same* Banach-algebra theorems: nothing in
`lie_trotter`, `symmetric_lie_trotter`, or `suzuki4_convergence_quartic`
requires the generator to be anti-Hermitian or the factors to be unitary, so
instantiating at `(-β)•A, (-β)•B` (equivalently `t = -β`) is all there is to
do.  The scalar bookkeeping is `c⁻¹ • ((-β) • X) = (-β/c) • X`.
-/

/-- **Imaginary-time (Gibbs) Lie–Trotter.**  For arbitrary `A, B` in a complete
normed algebra and any `β : ℝ`,

  `(exp(-βA/n) · exp(-βB/n))ⁿ → exp(-β(A+B))`   as `n → ∞`.

This is `lie_trotter` at the rescaled operators `(-β)•A, (-β)•B`: the
first-order Trotter theorem never assumed anti-Hermitian generators or unitary
factors, so imaginary-time evolution is covered by the same statement.  Rate:
O(1/n) by `lie_trotter_error_rate`. -/
theorem gibbs_lie_trotter (A B : 𝔸) (β : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((-β / (n : ℝ)) • A) * exp ((-β / (n : ℝ)) • B)) ^ n)
      atTop (nhds (exp ((-β) • (A + B)))) := by
  have hsmul : ∀ (c : ℝ) (X : 𝔸), c⁻¹ • ((-β) • X) = (-β / c) • X := fun c X => by
    rw [smul_smul, inv_mul_eq_div]
  have h := lie_trotter (𝕂 := ℝ) ((-β) • A) ((-β) • B)
  rw [← smul_add] at h
  simpa only [hsmul] using h

/-- **Imaginary-time (Gibbs) Strang splitting.**  For arbitrary `A, B` in a
complete normed algebra and any `β : ℝ`,

  `(exp(-βA/(2n)) · exp(-βB/n) · exp(-βA/(2n)))ⁿ → exp(-β(A+B))`,

at rate O(1/n²).  `symmetric_lie_trotter` at `(-β)•A, (-β)•B` — no
self-adjointness or unitarity is needed. -/
theorem gibbs_symmetric_lie_trotter (A B : 𝔸) (β : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((-β / (2 * (n : ℝ))) • A) * exp ((-β / (n : ℝ)) • B) *
                      exp ((-β / (2 * (n : ℝ))) • A)) ^ n)
      atTop (nhds (exp ((-β) • (A + B)))) := by
  have hsmul : ∀ (c : ℝ) (X : 𝔸), c⁻¹ • ((-β) • X) = (-β / c) • X := fun c X => by
    rw [smul_smul, inv_mul_eq_div]
  have h := symmetric_lie_trotter (𝕂 := ℝ) ((-β) • A) ((-β) • B)
  rw [← smul_add] at h
  simpa only [hsmul] using h

/-- **Imaginary-time (Gibbs) fourth-order Suzuki convergence.**  For arbitrary
`A, B` in a complete normed algebra, `p` satisfying the Suzuki cubic condition,
and any `β : ℝ`,

  `S₄(-β/n)ⁿ → exp(-β(A+B))`   as `n → ∞`,

at rate O(1/n⁴).  `suzuki4_convergence_quartic` at time `t = -β`: the O(1/n⁴)
theorem is uniform in the sign and size of `t`, so Gibbs-state factorization
needs no separate proof. -/
theorem gibbs_suzuki4_convergence (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) (β : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Exp A B p (-β / (n : ℝ))) ^ n)
      atTop (nhds (exp ((-β) • (A + B)))) :=
  suzuki4_convergence_quartic A B p hp (-β)

/-- **Imaginary-time (Gibbs) S₄ total error, O(1/n⁴)**: the quantitative rate
behind `gibbs_suzuki4_convergence`.  `suzuki4_total_error_quartic` at `t = -β`. -/
theorem gibbs_suzuki4_total_error_quartic (A B : 𝔸) (p : ℝ)
    (hp : IsSuzukiCubic p) (β : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ‖(suzuki4Exp A B p (-β / (n : ℝ))) ^ n - exp ((-β) • (A + B))‖ ≤
        C / (n : ℝ) ^ 4 :=
  suzuki4_total_error_quartic A B p hp (-β)

/-- **Imaginary-time (Gibbs) `suzuki4Step` convergence**: the `suzuki4Step`
spelling of `gibbs_suzuki4_convergence`, via the general-`t` rescaling theorem
at `t = -β`. -/
theorem gibbs_suzuki4Step_convergence (A B : 𝔸) (p : ℝ)
    (hp : IsSuzukiCubic p) (β : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (suzuki4Step ℝ ((-β) • A) ((-β) • B) p n) ^ n)
      atTop (nhds (exp ((-β) • (A + B)))) :=
  suzuki4Step_convergence_quartic_general A B p hp (-β)

end
