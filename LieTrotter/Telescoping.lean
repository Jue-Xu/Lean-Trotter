/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track A: Telescoping Identity and Norm Bound

Purely algebraic results: the telescoping sum identity `X^n - Y^n`
and its norm bound `‖X^n - Y^n‖ ≤ n ‖X-Y‖ max(‖X‖,‖Y‖)^{n-1}`.
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset
open scoped BigOperators

/-!
## A1: Telescoping Sum Identity

We prove `∑_{k<n} X^k (X-Y) Y^{n-1-k} = X^n - Y^n` by induction on `n`,
factoring out `Y` from the inner sum to get the inductive step.
-/

section Telescoping

variable {R : Type*} [Ring R]

/-- The telescoping sum identity:
    `∑_{k<n} X^k (X-Y) Y^{n-1-k} = X^n - Y^n`. -/
theorem telescoping_direct (X Y : R) (n : ℕ) :
    (∑ k ∈ Finset.range n, X ^ k * (X - Y) * Y ^ (n - 1 - k)) =
      X ^ n - Y ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_sub_one]
    have factor_Y : ∑ k ∈ Finset.range m,
        X ^ k * (X - Y) * Y ^ (m - k) =
        (∑ k ∈ Finset.range m, X ^ k * (X - Y) * Y ^ (m - 1 - k)) * Y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have : m - k = (m - 1 - k) + 1 := by omega
      rw [this, pow_succ]
      simp [mul_assoc]
    rw [Nat.sub_self, pow_zero, mul_one, factor_Y, ih]
    noncomm_ring [pow_succ]

end Telescoping

/-!
## A2: Norm Bound from Telescoping

`‖X^n - Y^n‖ ≤ n ‖X-Y‖ max(‖X‖,‖Y‖)^{n-1}`
-/

section NormBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- Norm bound from the telescoping identity:
    `‖X^n - Y^n‖ ≤ n * ‖X-Y‖ * max(‖X‖,‖Y‖)^{n-1}`. -/
theorem norm_pow_sub_pow_le' (X Y : 𝔸) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤
      n * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := by
  let M : ℝ := max ‖X‖ ‖Y‖
  rw [← telescoping_direct]
  calc ‖∑ k ∈ Finset.range n, X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
      ≤ ∑ k ∈ Finset.range n, ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, M ^ (n - 1) * ‖X - Y‖ := by
        refine Finset.sum_le_sum ?_
        intro k hk
        rw [Finset.mem_range] at hk
        have hkn : k + (n - 1 - k) = n - 1 := by omega
        have hX : ‖X‖ ^ k ≤ M ^ k := by
          exact pow_le_pow_left₀ (norm_nonneg X) (le_max_left ‖X‖ ‖Y‖) k
        have hY : ‖Y‖ ^ (n - 1 - k) ≤ M ^ (n - 1 - k) := by
          exact pow_le_pow_left₀ (norm_nonneg Y) (le_max_right ‖X‖ ‖Y‖) (n - 1 - k)
        have hXY : ‖X‖ ^ k * ‖Y‖ ^ (n - 1 - k) ≤ M ^ k * M ^ (n - 1 - k) := by
          exact mul_le_mul hX hY (by positivity) (by positivity)
        calc ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
            ≤ ‖X ^ k‖ * ‖X - Y‖ * ‖Y ^ (n - 1 - k)‖ := by
              calc ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
                  ≤ ‖X ^ k * (X - Y)‖ * ‖Y ^ (n - 1 - k)‖ := norm_mul_le _ _
                _ ≤ (‖X ^ k‖ * ‖X - Y‖) * ‖Y ^ (n - 1 - k)‖ := by
                    gcongr; exact norm_mul_le _ _
          _ ≤ ‖X‖ ^ k * ‖X - Y‖ * ‖Y‖ ^ (n - 1 - k) := by
              gcongr
              · exact norm_pow_le X k
              · exact norm_pow_le Y (n - 1 - k)
          _ = ‖X - Y‖ * (‖X‖ ^ k * ‖Y‖ ^ (n - 1 - k)) := by ring
          _ ≤ ‖X - Y‖ * (M ^ k * M ^ (n - 1 - k)) := by
              exact mul_le_mul_of_nonneg_left hXY (norm_nonneg _)
          _ = ‖X - Y‖ * M ^ (n - 1) := by rw [← pow_add, hkn]
          _ = M ^ (n - 1) * ‖X - Y‖ := by ring
    _ = n * (M ^ (n - 1) * ‖X - Y‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = n * ‖X - Y‖ * M ^ (n - 1) := by ring
    _ = n * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := by rfl

end NormBound
