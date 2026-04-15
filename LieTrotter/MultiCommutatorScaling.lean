/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Operator Commutator-Scaling Trotter Error

The multi-operator tight bound for the first-order Lie-Trotter formula, matching
the Proposition in Childs et al. (2021), §VII.A:

  ‖∏ exp(aᵢ) - exp(∑ aᵢ)‖ ≤ listCommNorm(as) / 2 * exp(3 * ∑ ‖aᵢ‖)

where `listCommNorm [a₁,...,aₙ] = ∑ᵢ ‖[aᵢ₊₁+⋯+aₙ, aᵢ]‖` is the sum of
commutator norms with suffix sums. This generalizes `norm_lie_trotter_comm_scaling`
from two operators to Γ operators.

## Proof strategy

Induction on the list, same pattern as `MultiOperator.lean`:
  exp(a) * P - exp(a + S) = exp(a) * (P - exp S) + (exp(a) * exp(S) - exp(a + S))
Term 1 uses the inductive hypothesis; Term 2 uses `norm_lie_trotter_comm_scaling`.
-/

import LieTrotter.CommutatorScaling
import LieTrotter.MultiOperator

noncomputable section

open NormedSpace
open scoped BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Definition: commutator sum with suffix sums

`listCommNorm [a₁, a₂, ..., aₙ] = ‖[a₂+⋯+aₙ, a₁]‖ + ‖[a₃+⋯+aₙ, a₂]‖ + ⋯ + 0`
-/

/-- The sum of commutator norms `∑ᵢ ‖(suffix_sum_after_i) * aᵢ - aᵢ * (suffix_sum_after_i)‖`. -/
def listCommNorm : List 𝔸 → ℝ
  | [] => 0
  | a :: rest => ‖rest.sum * a - a * rest.sum‖ + listCommNorm rest

@[simp] lemma listCommNorm_nil : listCommNorm ([] : List 𝔸) = 0 := rfl

@[simp] lemma listCommNorm_cons (a : 𝔸) (rest : List 𝔸) :
    listCommNorm (a :: rest) = ‖rest.sum * a - a * rest.sum‖ + listCommNorm rest := rfl

lemma listCommNorm_nonneg (as : List 𝔸) : 0 ≤ listCommNorm as := by
  induction as with
  | nil => simp
  | cons a rest ih => simp [listCommNorm]; linarith [norm_nonneg (rest.sum * a - a * rest.sum)]

/-!
## Corollary: two-operator commutator bound without smul
-/

/-- Two-operator commutator bound without the `t • ·` smul. Specializes
  `norm_lie_trotter_comm_scaling` at `t = 1`. -/
lemma norm_exp_mul_exp_sub_exp_add_comm (a b : 𝔸) :
    ‖exp a * exp b - exp (a + b)‖ ≤
      ‖a * b - b * a‖ / 2 * Real.exp (‖b‖ + 3 * ‖a‖) := by
  -- Apply norm_lie_trotter_comm_scaling with A := b, B := a, t := 1
  have h := @norm_lie_trotter_comm_scaling 𝔸 _ _ _ _ b a 1 zero_le_one
  simp only [one_smul, one_pow, mul_one, one_mul, add_comm b a] at h
  exact h

/-!
## Main theorem: multi-operator commutator-scaling bound
-/

/-- **Multi-operator commutator-scaling Trotter error:**
  `‖∏ exp(aᵢ) - exp(∑ aᵢ)‖ ≤ listCommNorm(as) / 2 * exp(3 * ∑ ‖aᵢ‖)`.

  Generalizes `norm_lie_trotter_comm_scaling` (two operators) to Γ operators.
  Matches the Proposition in Childs et al. (2021), §VII.A (up to the exponential
  factor, which vanishes for anti-Hermitian operators). -/
theorem norm_list_prod_exp_sub_exp_sum_comm (as : List 𝔸) :
    ‖(as.map (fun a => exp a)).prod - exp as.sum‖ ≤
      listCommNorm as / 2 * Real.exp (3 * (as.map (fun a => ‖a‖)).sum) := by
  induction as with
  | nil => simp [exp_zero]
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set P := (rest.map (fun a => exp a)).prod with hP_def
    set S := rest.sum with hS_def
    set T := (rest.map (fun a => ‖a‖)).sum with hT_def
    have hT : 0 ≤ T := by
      apply List.sum_nonneg; intro x hx
      simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; exact norm_nonneg b
    have hS_le : ‖S‖ ≤ T := norm_list_sum_le rest
    -- Split into two terms
    have split : exp a * P - exp (a + S) =
        exp a * (P - exp S) + (exp a * exp S - exp (a + S)) := by noncomm_ring
    rw [split]
    -- Term 1: ‖exp(a) * (P - exp S)‖ ≤ exp(‖a‖) * IH
    have h_term1 : ‖exp a * (P - exp S)‖ ≤
        Real.exp ‖a‖ * (listCommNorm rest / 2 * Real.exp (3 * T)) := by
      calc ‖exp a * (P - exp S)‖
          ≤ ‖exp a‖ * ‖P - exp S‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖a‖ * (listCommNorm rest / 2 * Real.exp (3 * T)) := by
            gcongr; exact norm_exp_le (𝕂 := ℝ) a
    -- Term 2: ‖exp(a) * exp(S) - exp(a+S)‖ ≤ ‖[S,a]‖/2 * exp(‖S‖+3‖a‖)
    have h_term2 : ‖exp a * exp S - exp (a + S)‖ ≤
        ‖S * a - a * S‖ / 2 * Real.exp (‖S‖ + 3 * ‖a‖) := by
      have := norm_exp_mul_exp_sub_exp_add_comm a S
      rwa [show ‖a * S - S * a‖ = ‖S * a - a * S‖ from by
        rw [show a * S - S * a = -(S * a - a * S) from by noncomm_ring, norm_neg]] at this
    -- Both exponentials are ≤ exp(3(‖a‖+T))
    have hexp1 : Real.exp ‖a‖ * Real.exp (3 * T) ≤ Real.exp (3 * (‖a‖ + T)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp_of_le (by nlinarith [norm_nonneg a])
    have hexp2 : Real.exp (‖S‖ + 3 * ‖a‖) ≤ Real.exp (3 * (‖a‖ + T)) :=
      Real.exp_le_exp_of_le (by nlinarith [norm_nonneg a])
    -- Combine
    calc ‖exp a * (P - exp S) + (exp a * exp S - exp (a + S))‖
        ≤ ‖exp a * (P - exp S)‖ + ‖exp a * exp S - exp (a + S)‖ := norm_add_le _ _
      _ ≤ Real.exp ‖a‖ * (listCommNorm rest / 2 * Real.exp (3 * T)) +
            ‖S * a - a * S‖ / 2 * Real.exp (‖S‖ + 3 * ‖a‖) :=
          add_le_add h_term1 h_term2
      _ ≤ listCommNorm rest / 2 * Real.exp (3 * (‖a‖ + T)) +
            ‖S * a - a * S‖ / 2 * Real.exp (3 * (‖a‖ + T)) := by
          have hLCN := listCommNorm_nonneg rest
          nlinarith [norm_nonneg (S * a - a * S), Real.exp_pos (3 * T),
            Real.exp_pos (‖S‖ + 3 * ‖a‖), Real.exp_pos (3 * (‖a‖ + T))]
      _ = (‖S * a - a * S‖ + listCommNorm rest) / 2 *
            Real.exp (3 * (‖a‖ + T)) := by ring

end
