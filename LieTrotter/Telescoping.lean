/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Track A: Telescoping Identity and Norm Bound

Purely algebraic results: the telescoping sum identity `X^n - Y^n`
and its norm bound `‖X^n - Y^n‖ ≤ n ‖X-Y‖ max(‖X‖,‖Y‖)^{n-1}`.
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Finset.Basic

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
    (∑ k in Finset.range n, X ^ k * (X - Y) * Y ^ (n - 1 - k)) =
      X ^ n - Y ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_sub_one]
    have hm : m - m = 0 := Nat.sub_self m
    rw [hm, pow_zero, mul_one]
    have factor_Y : ∑ k in Finset.range m,
        X ^ k * (X - Y) * Y ^ (m + 1 - 1 - k) =
        (∑ k in Finset.range m, X ^ k * (X - Y) * Y ^ (m - 1 - k)) * Y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have : m + 1 - 1 - k = (m - 1 - k) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [Nat.succ_eq_add_one, factor_Y, ih]
    ring

end Telescoping

/-!
## A2: Norm Bound from Telescoping

`‖X^n - Y^n‖ ≤ n ‖X-Y‖ max(‖X‖,‖Y‖)^{n-1}`
-/

section NormBound

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Norm bound from the telescoping identity:
    `‖X^n - Y^n‖ ≤ n * ‖X-Y‖ * max(‖X‖,‖Y‖)^{n-1}`. -/
theorem norm_pow_sub_pow_le' (X Y : 𝔸) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤
      n * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := by
  rw [← telescoping_direct]
  calc ‖∑ k in Finset.range n, X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
      ≤ ∑ k in Finset.range n, ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range n,
          ‖X‖ ^ k * ‖X - Y‖ * ‖Y‖ ^ (n - 1 - k) := by
        gcongr with k hk
        calc ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
            ≤ ‖X ^ k‖ * ‖X - Y‖ * ‖Y ^ (n - 1 - k)‖ := by
              calc ‖X ^ k * (X - Y) * Y ^ (n - 1 - k)‖
                  ≤ ‖X ^ k * (X - Y)‖ * ‖Y ^ (n - 1 - k)‖ := norm_mul_le _ _
                _ ≤ (‖X ^ k‖ * ‖X - Y‖) * ‖Y ^ (n - 1 - k)‖ := by
                    gcongr; exact norm_mul_le _ _
          _ ≤ ‖X‖ ^ k * ‖X - Y‖ * ‖Y‖ ^ (n - 1 - k) := by
              gcongr
              · exact norm_pow_le X k
              · exact norm_pow_le Y _
    _ ≤ ∑ _k in Finset.range n,
          (max ‖X‖ ‖Y‖) ^ (n - 1) * ‖X - Y‖ := by
        gcongr with k hk
        rw [Finset.mem_range] at hk
        have hkn : k + (n - 1 - k) = n - 1 := by omega
        calc ‖X‖ ^ k * ‖X - Y‖ * ‖Y‖ ^ (n - 1 - k)
            = ‖X - Y‖ * (‖X‖ ^ k * ‖Y‖ ^ (n - 1 - k)) := by ring
          _ ≤ ‖X - Y‖ * ((max ‖X‖ ‖Y‖) ^ k * (max ‖X‖ ‖Y‖) ^ (n - 1 - k)) := by
              gcongr
              · exact le_max_left _ _
              · exact le_max_right _ _
          _ = ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := by
              rw [← pow_add, hkn]
          _ = (max ‖X‖ ‖Y‖) ^ (n - 1) * ‖X - Y‖ := by ring
    _ = n * ‖X - Y‖ * (max ‖X‖ ‖Y‖) ^ (n - 1) := by
        rw [Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
        push_cast
        ring

end NormBound
