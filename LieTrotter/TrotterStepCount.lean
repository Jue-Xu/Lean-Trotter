/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ε-Form Step-Count Corollaries

The form quantum-algorithms papers actually consume (Childs et al., "Theory of
Trotter Error with Commutator Scaling", PRX 11, 011020 (2021)): given a target
accuracy `ε`, how many Trotter steps `n` suffice?

For a `k`-th order integrator with total error `≤ C/nᵏ`, the answer is
`n = O((C/ε)^{1/k})`.  To avoid `Real.rpow` in the statements, each threshold
is expressed as a *polynomial side condition* on `n`:

  * first order   (`lie_trotter_step_count`):     `C ≤ ε·n   →  err ≤ ε`,
  * second order  (`strang_step_count`):          `C ≤ ε·n²  →  err ≤ ε`,
  * fourth order  (`suzuki4_step_count_quartic`): `C ≤ ε·n⁴  →  err ≤ ε`.

Reading off the step counts: `n = O(C/ε)`, `n = O((C/ε)^{1/2})`, and
`n = O((C/ε)^{1/4})` respectively.  Rescaling `A → tA`, `B → tB` for a
simulation time `t` (so that `C = O(t²)`, `O(t³)`, `O(t⁵)` up to the
exponential factor, which is `e^{O(t)}` and absorbed into the constant for
fixed `t`), these are the familiar first-order `n = O(t²/ε)`, Strang
`n = O(t^{3/2}/ε^{1/2})`, and fourth-order `n = O(t^{5/4}/ε^{1/4})` Trotter
step counts.

Because the constants are the *point* of these statements (Lesson 17), the
first- and second-order results carry the fully explicit constants of
`lie_trotter_error_rate` and `strang_error_rate_sq` in their hypotheses; the
per-`n` bounds with those explicit constants are restated here as
`lie_trotter_error_explicit` / `strang_error_explicit` (the originals bind
their constants existentially, so the explicit form must be replayed — the
proofs below are verbatim replays of the originals, minus the final `+1`
positivity slack).  For S₄ the single-step constant is itself existential
(it comes from the BCH regime of `exists_norm_s4Func_sub_exp_le_t5`), so the
step-count keeps the `∃ C, ∃ N` shape — with `C` and `N` bound BEFORE `ε`
(Lesson 16: one constant, uniform in every accuracy target).
-/

import LieTrotter.Assembly
import LieTrotter.StrangSplitting
import LieTrotter.Suzuki4Convergence

open Filter Topology NormedSpace

/-!
## First- and second-order step counts (over any `RCLike` field)
-/

section FirstAndSecondOrder

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **Explicit first-order error bound.**  The per-`n` content of
`lie_trotter_error_rate`, with the constant in the statement instead of behind
an `∃`:

  `‖(exp(A/n) exp(B/n))^n - exp(A+B)‖ ≤ 2‖A‖‖B‖ exp(‖A‖+‖B‖) / n`.

This is the tight constant of that proof — the `+1` in
`lie_trotter_error_rate`'s witness exists only to make the constant strictly
positive (Design Decision 5).  Proof: verbatim replay of
`lie_trotter_error_rate` (telescoping + quadratic step error + growth bound),
stopping before the `+1` slack step. -/
theorem lie_trotter_error_explicit (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖(exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)) ^ n - exp (A + B)‖ ≤
      2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) / (n : ℝ) := by
  -- Step 1: Rewrite exp(A+B) = exp((A+B)/n)^n
  have hpow : exp (A + B) = (exp ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (𝕂 := 𝕂) (A + B) n hn).symm
  rw [hpow]
  set P := exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) with hP_def
  set Q := exp ((n : 𝕂)⁻¹ • (A + B)) with hQ_def
  -- Step 2: Apply telescoping norm bound
  have h_telesc := norm_pow_sub_pow_le' P Q n
  -- Step 3: Bound ‖P - Q‖ by step error
  have h_step : ‖P - Q‖ ≤ 2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 *
      Real.exp ((‖A‖ + ‖B‖) / n) := by
    rw [hP_def, hQ_def]
    exact lie_trotter_step_error A B n hn
  -- Step 4: Bound max(‖P‖, ‖Q‖)
  have h_max : max ‖P‖ ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
      rw [norm_inv, RCLike.norm_natCast]
    have h_P : ‖P‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖P‖ = ‖exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)‖ := rfl
        _ ≤ ‖exp ((n : 𝕂)⁻¹ • A)‖ * ‖exp ((n : 𝕂)⁻¹ • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • A‖ * Real.exp ‖(n : 𝕂)⁻¹ • B‖ := by
            gcongr
            · exact norm_exp_le (𝕂 := 𝕂) ((n : 𝕂)⁻¹ • A)
            · exact norm_exp_le (𝕂 := 𝕂) ((n : 𝕂)⁻¹ • B)
        _ = Real.exp (‖(n : 𝕂)⁻¹ • A‖ + ‖(n : 𝕂)⁻¹ • B‖) := (Real.exp_add _ _).symm
        _ = Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A‖ + ‖(n : 𝕂)⁻¹‖ * ‖B‖) := by
            rw [norm_smul, norm_smul]
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, ← mul_add, inv_mul_eq_div]
    have h_Q : ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • (A + B))‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • (A + B)‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A + B‖) := by
            gcongr
            exact norm_smul_le _ _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * (‖A‖ + ‖B‖)) := by
            gcongr
            exact norm_add_le A B
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, inv_mul_eq_div]
    exact max_le h_P h_Q
  -- Step 5: Combine and simplify (no `+1` slack — the bound is exact)
  calc ‖P ^ n - Q ^ n‖
      ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (2 * ‖A‖ * ‖B‖ / (n : ℝ) ^ 2 * Real.exp ((‖A‖ + ‖B‖) / n)) *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ (n - 1) := by
        gcongr
    _ = 2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) / (n : ℝ) := by
        set s := ‖A‖ + ‖B‖
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        have h_pow : Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1) =
            Real.exp (s / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (s / ↑n) ^ n = Real.exp s := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have h_split : ↑n * (2 * ‖A‖ * ‖B‖ / (↑n) ^ 2 * Real.exp (s / ↑n)) *
            Real.exp (s / ↑n) ^ (n - 1) =
            ↑n * (2 * ‖A‖ * ‖B‖ / (↑n) ^ 2) *
            (Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1)) := by ring
        rw [h_split, h_pow, h_exp_pow]
        field_simp

/-- **First-order Trotter step count.**  If

  `2‖A‖‖B‖ exp(‖A‖+‖B‖) + 1 ≤ ε·n`

— the same constant as `lie_trotter_error_rate` — then `n` first-order Trotter
steps achieve accuracy `ε`.  Reading: `n ≥ C/ε`, i.e. `n = O(C/ε)` steps
suffice; with `A → tA`, `B → tB` this is the first-order `n = O(t²/ε)` step
count of Childs et al. 2021 (the `e^{t(‖A‖+‖B‖)}` factor is absorbed into the
constant for fixed `t`). -/
theorem lie_trotter_step_count (A B : 𝔸) (ε : ℝ) (n : ℕ) (hn : 0 < n)
    (hstep : 2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1 ≤ ε * (n : ℝ)) :
    ‖(exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)) ^ n - exp (A + B)‖ ≤ ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  refine (lie_trotter_error_explicit (𝕂 := 𝕂) A B n hn).trans ?_
  rw [div_le_iff₀ hn_pos]
  -- `2‖A‖‖B‖e^s ≤ 2‖A‖‖B‖e^s + 1 ≤ ε·n`
  linarith

/-- **First-order Trotter step count, `Nat.ceil` form.**  Any

  `n ≥ ⌈(2‖A‖‖B‖ exp(‖A‖+‖B‖) + 1)/ε⌉₊`

steps achieve accuracy `ε`.  (Since the constant is `≥ 1` and `ε > 0`, the
ceiling is `≥ 1`, so `0 < n` is automatic.) -/
theorem lie_trotter_step_count_ceil (A B : 𝔸) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : ⌈(2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1) / ε⌉₊ ≤ n) :
    ‖(exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)) ^ n - exp (A + B)‖ ≤ ε := by
  have hC_pos : (0 : ℝ) < 2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1 := by positivity
  have hceil_pos : 0 < ⌈(2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1) / ε⌉₊ :=
    Nat.ceil_pos.mpr (div_pos hC_pos hε)
  have hn_pos : 0 < n := lt_of_lt_of_le hceil_pos hn
  apply lie_trotter_step_count (𝕂 := 𝕂) A B ε n hn_pos
  have h1 : (2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1) / ε ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  have h2 : 2 * ‖A‖ * ‖B‖ * Real.exp (‖A‖ + ‖B‖) + 1 ≤ (n : ℝ) * ε :=
    (div_le_iff₀ hε).mp h1
  linarith

/-!
### Second order (Strang)

The cubic step-error lemma of `StrangSplitting.lean` is `private` there, so it
is replayed verbatim below (together with its two smul-arithmetic helpers)
before the explicit O(1/n²) bound.
-/

omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma half_inv_add_half_inv (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ + (2 * (n : 𝕂))⁻¹ = (n : 𝕂)⁻¹ := by
  have hn_ne : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2n_ne : (2 : 𝕂) * (n : 𝕂) ≠ 0 := mul_ne_zero two_ne_zero hn_ne
  field_simp; norm_num

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma symmetric_smul_eq (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      (n : 𝕂)⁻¹ • (A + B) := by
  have h : (2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A = (n : 𝕂)⁻¹ • A := by
    rw [← add_smul, half_inv_add_half_inv (𝕂 := 𝕂) n hn]
  rw [smul_add]
  have : (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      ((2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A) + (n : 𝕂)⁻¹ • B := by abel
  rw [this, h]

include 𝕂 in
private theorem strang_step_error_cubic (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
      exp ((2 * (n : 𝕂))⁻¹ • A) - exp ((n : 𝕂)⁻¹ • (A + B))‖ ≤
      (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 +
       3 / 8 * ‖A‖ ^ 3) /
        (n : ℝ) ^ 3 * Real.exp ((‖A‖ + ‖B‖) / n) := by
  have hsmul : (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      (n : 𝕂)⁻¹ • (A + B) := symmetric_smul_eq (𝕂 := 𝕂) A B n hn
  rw [← hsmul]
  set a := (2 * (n : 𝕂))⁻¹ • A
  set b := (n : 𝕂)⁻¹ • B
  have h_gen := norm_exp_mul_exp_mul_exp_sub_exp_add_cubic (𝕂 := 𝕂) a b
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h2n_ne : (2 : 𝕂) * (n : 𝕂) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have norm_a : ‖a‖ = ‖A‖ / (2 * n) := by
    show ‖(2 * (n : 𝕂))⁻¹ • A‖ = _
    rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
  have norm_b : ‖b‖ = ‖B‖ / n := by
    show ‖(n : 𝕂)⁻¹ • B‖ = _
    rw [norm_smul, norm_inv_n, div_eq_inv_mul]
  rw [norm_a, norm_b] at h_gen
  calc ‖exp a * exp b * exp a - exp (a + b + a)‖
      ≤ (7 * (‖A‖ / (2 * ↑n)) ^ 2 * (‖B‖ / ↑n) +
         3 * (‖A‖ / (2 * ↑n)) * (‖B‖ / ↑n) ^ 2 +
         3 * (‖A‖ / (2 * ↑n)) ^ 3) *
        Real.exp (2 * (‖A‖ / (2 * ↑n)) + ‖B‖ / ↑n) := h_gen
    _ = (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 +
         3 / 8 * ‖A‖ ^ 3) /
          (↑n) ^ 3 * Real.exp ((‖A‖ + ‖B‖) / ↑n) := by
      field_simp; ring

/-- **Explicit second-order (Strang) error bound.**  The per-`n` content of
`strang_error_rate_sq`, with the constant in the statement:

  `‖S₂(1/n)^n - exp(A+B)‖ ≤ (7/4·‖A‖²‖B‖ + 3/2·‖A‖‖B‖² + 3/8·‖A‖³)
                              · exp(‖A‖+‖B‖) / n²`

where `S₂(1/n) = exp(A/(2n)) exp(B/n) exp(A/(2n))`.  Verbatim replay of
`strang_error_rate_sq`, minus the `+1` positivity slack. -/
theorem strang_error_explicit (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖(exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
      exp ((2 * (n : 𝕂))⁻¹ • A)) ^ n - exp (A + B)‖ ≤
      (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 + 3 / 8 * ‖A‖ ^ 3) *
        Real.exp (‖A‖ + ‖B‖) / (n : ℝ) ^ 2 := by
  set c := 7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 +
       3 / 8 * ‖A‖ ^ 3
  -- Step 1: Rewrite exp(A+B) = exp((A+B)/n)^n
  have hpow : exp (A + B) = (exp ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (𝕂 := 𝕂) (A + B) n hn).symm
  rw [hpow]
  set S := exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
    exp ((2 * (n : 𝕂))⁻¹ • A) with hS_def
  set Q := exp ((n : 𝕂)⁻¹ • (A + B)) with hQ_def
  -- Step 2: Apply telescoping
  have h_telesc := norm_pow_sub_pow_le' S Q n
  -- Step 3: Bound ‖S - Q‖ using CUBIC step error
  have h_step : ‖S - Q‖ ≤ c / (n : ℝ) ^ 3 *
      Real.exp ((‖A‖ + ‖B‖) / n) := by
    rw [hS_def, hQ_def]
    exact strang_step_error_cubic (𝕂 := 𝕂) A B n hn
  -- Step 4: Bound max(‖S‖, ‖Q‖)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have h_max : max ‖S‖ ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
    have norm_half_A : ‖(2 * (n : 𝕂))⁻¹ • A‖ = ‖A‖ / (2 * n) := by
      rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
    have norm_inv_B : ‖(n : 𝕂)⁻¹ • B‖ = ‖B‖ / n := by
      rw [norm_smul, norm_inv_n, div_eq_inv_mul]
    have h_S : ‖S‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖S‖ = ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
              exp ((2 * (n : 𝕂))⁻¹ • A)‖ := rfl
        _ ≤ ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)‖ *
            ‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ := norm_mul_le _ _
        _ ≤ (‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ * ‖exp ((n : 𝕂)⁻¹ • B)‖) *
            ‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ := by
            gcongr; exact norm_mul_le _ _
        _ ≤ (Real.exp ‖(2 * (n : 𝕂))⁻¹ • A‖ * Real.exp ‖(n : 𝕂)⁻¹ • B‖) *
            Real.exp ‖(2 * (n : 𝕂))⁻¹ • A‖ := by
            gcongr
            · exact norm_exp_le (𝕂 := 𝕂) _
            · exact norm_exp_le (𝕂 := 𝕂) _
            · exact norm_exp_le (𝕂 := 𝕂) _
        _ = Real.exp (‖(2 * (n : 𝕂))⁻¹ • A‖ + ‖(n : 𝕂)⁻¹ • B‖ +
            ‖(2 * (n : 𝕂))⁻¹ • A‖) := by
            rw [Real.exp_add, Real.exp_add]
        _ = Real.exp (‖A‖ / (2 * ↑n) + ‖B‖ / ↑n + ‖A‖ / (2 * ↑n)) := by
            rw [norm_half_A, norm_inv_B]
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            congr 1; field_simp; ring
    have h_Q : ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • (A + B))‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • (A + B)‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A + B‖) := by
            gcongr; exact norm_smul_le _ _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * (‖A‖ + ‖B‖)) := by
            gcongr; exact norm_add_le A B
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, inv_mul_eq_div]
    exact max_le h_S h_Q
  -- Step 5: Combine: n · O(1/n³) · exp(s/n)^(n-1) = O(1/n²) · exp(s)
  calc ‖S ^ n - Q ^ n‖
      ≤ n * ‖S - Q‖ * (max ‖S‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (c / (n : ℝ) ^ 3 * Real.exp ((‖A‖ + ‖B‖) / n)) *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ (n - 1) := by
        gcongr
    _ = c * Real.exp (‖A‖ + ‖B‖) / (n : ℝ) ^ 2 := by
        set s := ‖A‖ + ‖B‖
        have h_pow : Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1) =
            Real.exp (s / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (s / ↑n) ^ n = Real.exp s := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have h_split : ↑n * (c / (↑n) ^ 3 * Real.exp (s / ↑n)) *
            Real.exp (s / ↑n) ^ (n - 1) =
            ↑n / (↑n) ^ 3 * c *
            (Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1)) := by ring
        rw [h_split, h_pow, h_exp_pow]
        have hn3 : (↑n : ℝ) / (↑n) ^ 3 = 1 / (↑n) ^ 2 := by
          field_simp
        rw [hn3]; ring

/-- **Second-order (Strang) step count.**  If

  `(7/4·‖A‖²‖B‖ + 3/2·‖A‖‖B‖² + 3/8·‖A‖³) · exp(‖A‖+‖B‖) + 1 ≤ ε·n²`

— the same constant as `strang_error_rate_sq` — then `n` Strang steps achieve
accuracy `ε`.  Reading: `n = O((C/ε)^{1/2})` steps suffice; with `A → tA`,
`B → tB` (so `C = O(t³)` up to the exponential factor) this is the Strang
`n = O(t^{3/2}/ε^{1/2})` step count of Childs et al. 2021. -/
theorem strang_step_count (A B : 𝔸) (ε : ℝ) (n : ℕ) (hn : 0 < n)
    (hstep : (7 / 4 * ‖A‖ ^ 2 * ‖B‖ + 3 / 2 * ‖A‖ * ‖B‖ ^ 2 + 3 / 8 * ‖A‖ ^ 3) *
        Real.exp (‖A‖ + ‖B‖) + 1 ≤ ε * (n : ℝ) ^ 2) :
    ‖(exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
      exp ((2 * (n : 𝕂))⁻¹ • A)) ^ n - exp (A + B)‖ ≤ ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn_pos 2
  refine (strang_error_explicit (𝕂 := 𝕂) A B n hn).trans ?_
  rw [div_le_iff₀ hn2_pos]
  linarith

end FirstAndSecondOrder

/-!
## Fourth-order (Suzuki S₄) step count (over `ℝ`, like `Suzuki4Convergence`)

Here the single-step constant is itself existential — it comes from the BCH
regime `|τ| < δ` of `exists_norm_s4Func_sub_exp_le_t5` — so the step count
keeps the `∃ C, ∃ N` shape of `suzuki4_total_error_quartic`.  Crucially
(Lesson 16), `C` and `N` are bound BEFORE `ε`: one constant and one threshold,
uniform in every accuracy target.
-/

section FourthOrder

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **Fourth-order (Suzuki S₄) step count.**  Under the Suzuki cubic condition
`4p³ + (1-4p)³ = 0`, there are a constant `C > 0` and a threshold `N` —
*independent of `ε`* — such that for every accuracy target `ε > 0`, any
`n ≥ N` with `C ≤ ε·n⁴` satisfies

  `‖S₄(t/n)^n - exp(t(A+B))‖ ≤ ε`.

Reading: `n = O((C/ε)^{1/4})` steps suffice (`N` only marks where the step
size `t/n` enters the BCH regime, and is `ε`-independent); with `C = O(t⁵)`
(up to the exponential factor) this is the fourth-order
`n = O(t^{5/4}/ε^{1/4})` Trotter step count of Childs et al. 2021.
Derived from `suzuki4_total_error_quartic`: `err ≤ C/n⁴ ≤ ε` once
`C ≤ ε·n⁴`. -/
theorem suzuki4_step_count_quartic (A B : 𝔸) (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    ∃ C > 0, ∃ N : ℕ, 0 < N ∧ ∀ ε > 0, ∀ n : ℕ, N ≤ n → C ≤ ε * (n : ℝ) ^ 4 →
      ‖(suzuki4Exp A B p (t / (n : ℝ))) ^ n - exp (t • (A + B))‖ ≤ ε := by
  obtain ⟨C, hC_pos, N, hN_pos, hbound⟩ := suzuki4_total_error_quartic A B p hp t
  refine ⟨C, hC_pos, N, hN_pos, ?_⟩
  intro ε hε n hn hstep
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hN_pos hn)
  have hn4_pos : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos hn_pos 4
  refine (hbound n hn).trans ?_
  rw [div_le_iff₀ hn4_pos]
  exact hstep

end FourthOrder
