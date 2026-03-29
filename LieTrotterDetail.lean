/-
# Lie-Trotter Product Formula — Detailed Lemma Proofs

This file provides detailed proofs for the lemmas used in the
Lie-Trotter product formula. We separate these from the main file
for clarity and to allow incremental development.
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Finset.Basic

open Filter Topology NormedSpace Finset
open scoped BigOperators

/-!
## Part 1: Algebraic Identities (no analysis needed)

These are purely ring-theoretic results.
-/

section AlgebraicIdentities

variable {R : Type*} [Ring R]

/-- The telescoping identity: `X^{n+1} - Y^{n+1} = X*(X^n - Y^n) + (X-Y)*Y^n`.
    This is the inductive step for the full telescoping sum. -/
lemma pow_succ_sub_factored (X Y : R) (n : ℕ) :
    X ^ (n + 1) - Y ^ (n + 1) =
      X * (X ^ n - Y ^ n) + (X - Y) * Y ^ n := by
  ring

/-- Telescoping sum identity, version with `Fin n` indexing for cleaner induction. -/
theorem telescoping_sum (X Y : R) :
    ∀ n : ℕ, X ^ n - Y ^ n =
      ∑ k in Finset.range n, X ^ k * (X - Y) * Y ^ (n - 1 - k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ_sub_factored]
    rw [ih, Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      -- Need: X * (X^k * (X-Y) * Y^(n-1-k)) = X^(k+1) * (X-Y) * Y^(n-k)
      -- LHS = X^{k+1} * (X-Y) * Y^{n-1-k}
      -- RHS index: for succ n, the term is X^k * (X-Y) * Y^{n+1-1-k} = X^k * (X-Y) * Y^{n-k}
      -- Wait, let me re-check the indices.
      -- In the sum for n+1: term k is X^k * (X-Y) * Y^{(n+1)-1-k} = X^k * (X-Y) * Y^{n-k}
      -- In X * (sum for n): term k gives X * X^k * (X-Y) * Y^{n-1-k}
      --                                 = X^{k+1} * (X-Y) * Y^{n-1-k}
      -- So we need to reindex: term k+1 in the (n+1)-sum = term k in the rescaled n-sum.
      -- This is getting fiddly. Let's use ring_nf + omega.
      ring_nf
      congr 1
      -- The Y-exponents should match: n - 1 - k = n - (k + 1) when k < n
      sorry -- omega should handle this with the right setup
    · -- The last term: (X - Y) * Y^n = X^0 * (X-Y) * Y^{(n+1)-1-0}? No...
      -- Actually the last term in range (n+1) is k = n:
      -- X^n * (X-Y) * Y^{n+1-1-n} = X^n * (X-Y) * Y^0 = X^n * (X-Y)
      -- And the extra piece is (X-Y) * Y^n
      -- These don't match. We need to be more careful.
      -- The Finset.sum_range_succ puts k=n at the END:
      --   ∑_{k=0}^{n} = ∑_{k=0}^{n-1} + [k=n term]
      -- k=n term: X^n * (X-Y) * Y^{n+1-1-n} = X^n * (X-Y) * Y^0 = X^n * (X-Y)
      -- But we want (X-Y) * Y^n here.
      -- So the identification is wrong. Let me redo this properly.
      sorry

/-- A cleaner version of the telescoping identity using a direct proof.
    We show `X^n - Y^n = ∑_{k < n} X^{n-1-k} * (X - Y) * Y^k`. -/
theorem telescoping_sum' (X Y : R) (n : ℕ) :
    X ^ n - Y ^ n =
      ∑ k in Finset.range n, X ^ (n - 1 - k) * (X - Y) * Y ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- X^{n+1} - Y^{n+1} = (X-Y)*Y^n + X*(X^n - Y^n)
    -- by ring: X^{n+1} - Y^{n+1} = X^{n+1} - X*Y^n + X*Y^n - Y^{n+1}
    --        = X*(X^n - Y^n) + (X - Y)*Y^n
    have step : X ^ (n + 1) - Y ^ (n + 1) =
        (X - Y) * Y ^ n + X * (X ^ n - Y ^ n) := by ring
    rw [step, ih]
    rw [Finset.sum_range_succ']
    -- sum_{k=0}^{n} f(k) = f(0) + sum_{k=0}^{n-1} f(k+1)
    -- Wait, sum_range_succ' gives sum_{k < n+1} = sum_{k < n} f(k+1) + f(0)
    -- Hmm, let me check the API.
    -- Actually Finset.sum_range_succ' :
    --   ∑ k in range (n+1), f k = f 0 + ∑ k in range n, f (k+1)
    -- Hmm, this direction might be messier. Let me try the other way.
    sorry

/-- The simplest correct version: telescoping as a direct ring identity. -/
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
    -- ∑_{k<m} X^k(X-Y)Y^{m-k} + X^m(X-Y)
    -- = ∑_{k<m} X^k(X-Y)Y^{m-k} + X^{m+1} - X^m*Y
    -- Need to relate ∑_{k<m} X^k(X-Y)Y^{m-k} to X^m*Y - Y^{m+1} + (X^m - Y^m)?
    -- Actually let's just use ring + ih
    -- The inner sum for (m+1): terms are X^k * (X-Y) * Y^{m-k} for k < m
    -- The inner sum for m (from ih): terms are X^k * (X-Y) * Y^{m-1-k} for k < m
    -- These differ by a factor of Y in the last position!
    -- So ∑_{k<m} X^k(X-Y)Y^{m-k} = (∑_{k<m} X^k(X-Y)Y^{m-1-k}) * Y = (X^m - Y^m) * Y
    -- Then total = (X^m - Y^m)*Y + X^m*(X-Y)
    --            = X^m*Y - Y^{m+1} + X^{m+1} - X^m*Y
    --            = X^{m+1} - Y^{m+1}  ✓
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

end AlgebraicIdentities

/-!
## Part 2: Norm Estimates for Telescoping

The norm bound that follows from the telescoping identity.
-/

section NormEstimates

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Norm bound from telescoping: `‖X^n - Y^n‖ ≤ n * ‖X-Y‖ * M^{n-1}`
    where `M = max(‖X‖, ‖Y‖)`. -/
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

end NormEstimates

/-!
## Part 3: Exponential Estimates

These require working with the power series definition of `exp`.
The proofs use `NormedSpace.expSeries` and `tsum` bounds.
-/

section ExpEstimates

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- `exp(a) - 1 - a` is the "remainder" after the linear term.
    From the power series exp(a) = ∑_{k≥0} a^k/k!, we get
    exp(a) - 1 - a = ∑_{k≥2} a^k/k!.

    The key bound is: ‖exp(a) - 1 - a‖ ≤ ‖a‖² * (exp(‖a‖) - 1 - ‖a‖) / ‖a‖²
                                          = exp(‖a‖) - 1 - ‖a‖
                                          ≤ ‖a‖²/2 * exp(‖a‖)

    The last inequality uses: for x ≥ 0,
      exp(x) - 1 - x = ∑_{k≥2} x^k/k! ≤ x²/2 * ∑_{k≥0} x^k/k! = x²/2 * exp(x)

    This holds because k! ≥ 2 * (k-2)! for k ≥ 2.
-/
lemma exp_sub_one_sub_bound_real (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp x := by
  -- exp(x) - 1 - x = ∑_{k=2}^∞ x^k/k!
  -- For k ≥ 2: x^k/k! = x²/(k(k-1)) * x^{k-2}/(k-2)! ≤ x²/2 * x^{k-2}/(k-2)!
  -- Summing: ≤ x²/2 * ∑_{j=0}^∞ x^j/j! = x²/2 * exp(x)
  sorry

/-- The product of two exponentials differs from their sum's exponential
    by a term involving the commutator.

    Specifically:
    exp(a) * exp(b) - exp(a + b)
    = exp(a+b) * (exp(-a-b) * exp(a) * exp(b) - 1)

    And exp(-a-b) * exp(a) * exp(b) = exp([a,b]/2 + higher order)
    by BCH, so the leading error is O(‖a‖ * ‖b‖).

    For our purposes, the following crude but sufficient bound works:
    ‖exp(a) * exp(b) - exp(a+b)‖ ≤ f(‖a‖, ‖b‖)
    where f grows quadratically in the smaller argument.
-/

/-- **Crude bound**: For small `a, b`,
    `‖exp(a) * exp(b) - exp(a+b)‖ ≤ 2 * ‖a‖ * ‖b‖ * exp(‖a‖ + ‖b‖)`.

    This is sufficient for the Lie-Trotter proof since we apply it with
    `a = A/n`, `b = B/n`, giving O(1/n²). -/
theorem norm_exp_mul_exp_sub_exp_add' (a b : 𝔸) :
    ‖exp 𝕂 a * exp 𝕂 b - exp 𝕂 (a + b)‖ ≤
      2 * ‖a‖ * ‖b‖ * Real.exp (‖a‖ + ‖b‖) := by
  /- Proof sketch:
     Write exp(a) = 1 + a + R_a where R_a = exp(a) - 1 - a
     Write exp(b) = 1 + b + R_b

     exp(a) * exp(b) = (1 + a + R_a)(1 + b + R_b)
                     = 1 + a + b + ab + R_a + R_b + a*R_b + R_a*b + R_a*R_b

     exp(a+b) = 1 + (a+b) + R_{a+b}

     Difference = ab + R_a + R_b + a*R_b + R_a*b + R_a*R_b - R_{a+b}

     Now:
     • ‖ab‖ ≤ ‖a‖ * ‖b‖
     • |R_a| ≤ ‖a‖²/2 * exp(‖a‖), similarly for R_b
     • The cross terms are bounded by products of these

     But this gives O(‖a‖²) + O(‖b‖²) + O(‖a‖ * ‖b‖) which is
     not purely O(‖a‖ * ‖b‖).

     Better approach: Use the integral formula
     exp(a)*exp(b) - exp(a+b) = ∫₀¹ exp(s*a) * [a, b] * exp((1-s)*a) * exp(b) ds
                                + higher order terms

     For our purposes, the cleanest approach is:
     exp(a)*exp(b) = exp(a+b+C) where C = [a,b]/2 + ...  (BCH)
     so exp(a)*exp(b) - exp(a+b) = exp(a+b) * (exp(C) - 1)
     and ‖exp(C) - 1‖ ≤ exp(‖C‖) - 1 ≤ ‖C‖ * exp(‖C‖)

     But formalizing BCH is very heavy. We use a direct estimate instead. -/

  /- Direct proof using the integral representation:
     Define F(t) = exp(t*a) * exp(t*b) - exp(t*(a+b))
     F(0) = 0
     F'(t) = a*exp(ta)*exp(tb) + exp(ta)*b*exp(tb) - (a+b)*exp(t(a+b))
           = exp(ta) * [a, exp(tb)] * ... (this gets complicated)

     Simplest rigorous bound: use the fact that for any operator norm,
     ‖exp(a)*exp(b) - exp(a+b)‖
       = ‖∑_{j,k≥0} a^j*b^k/(j!k!) - ∑_{m≥0} (a+b)^m/m!‖
       = ‖∑_{m≥2} (∑_{j+k=m} a^j*b^k/(j!k!) - (a+b)^m/m!)‖

     At order m=2: a²/2 + ab + b²/2 - (a²+ab+ba+b²)/2 = (ab-ba)/2 = [a,b]/2
     ‖[a,b]/2‖ ≤ ‖a‖*‖b‖

     Higher orders contribute O(‖a‖*‖b‖*(‖a‖+‖b‖)) etc.

     Total ≤ ‖a‖*‖b‖ * ∑_{m≥0} (‖a‖+‖b‖)^m/m! * C_m
     where C_m accounts for combinatorial factors.
     A crude bound gives the factor of 2 * exp(‖a‖+‖b‖). -/
  sorry

end ExpEstimates

/-!
## Part 4: The Assembly

Putting it all together to prove the Lie-Trotter formula.
-/

section Assembly

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The norm of `exp(c • a)` is bounded by `exp(‖c‖ * ‖a‖)`. -/
lemma norm_exp_smul_le (c : 𝕂) (a : 𝔸) :
    ‖exp 𝕂 (c • a)‖ ≤ Real.exp (‖c‖ * ‖a‖) := by
  sorry -- From norm_exp_le and ‖c • a‖ ≤ ‖c‖ * ‖a‖

/-- `exp(a/n)^n = exp(a)` in a complete normed algebra. -/
lemma exp_div_pow (a : 𝔸) (n : ℕ) (hn : 0 < n) :
    (exp 𝕂 ((n : 𝕂)⁻¹ • a)) ^ n = exp 𝕂 a := by
  -- exp(a/n) commutes with itself, so exp(a/n)^n = exp(n * a/n) = exp(a)
  -- In mathlib: exp_nsmul or exp_pow? We need:
  -- exp(x)^n = exp(n • x) when x commutes with itself (always true)
  -- and n • (n⁻¹ • a) = a
  sorry

/-- **Key convergence rate**: The Lie-Trotter error is O(1/n).

    `‖(exp(A/n) * exp(B/n))^n - exp(A+B)‖ ≤ C/n`

    where `C = 2 * ‖A‖ * ‖B‖ * exp(‖A‖+‖B‖)²`. -/
theorem lie_trotter_error_rate (A B : 𝔸) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖(exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B)) ^ n -
       exp 𝕂 (A + B)‖ ≤ C / n := by
  -- Set C = 2 * ‖A‖ * ‖B‖ * exp(2(‖A‖+‖B‖))
  -- For the case A = 0 or B = 0, the formula is exact (no error).
  -- For A, B ≠ 0:
  refine ⟨2 * ‖A‖ * ‖B‖ * Real.exp (2 * (‖A‖ + ‖B‖)) + 1, by positivity, ?_⟩
  intro n hn
  -- Step 1: Rewrite exp(A+B) = exp((A+B)/n)^n
  have hpow : exp 𝕂 (A + B) = (exp 𝕂 ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (A + B) n hn).symm
  rw [hpow]
  -- Step 2: Set P = exp(A/n) * exp(B/n), Q = exp((A+B)/n)
  set P := exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B) with hP_def
  set Q := exp 𝕂 ((n : 𝕂)⁻¹ • (A + B)) with hQ_def
  -- Step 3: Apply telescoping norm bound
  -- ‖P^n - Q^n‖ ≤ n * ‖P - Q‖ * max(‖P‖, ‖Q‖)^{n-1}
  have h_telesc := norm_pow_sub_pow_le' P Q n
  -- Step 4: Bound ‖P - Q‖ by the step error
  -- ‖P - Q‖ = ‖exp(A/n)*exp(B/n) - exp((A+B)/n)‖ ≤ 2‖A‖‖B‖/n² * exp((‖A‖+‖B‖)/n)
  have h_step : ‖P - Q‖ ≤ 2 * ‖A‖ * ‖B‖ / (n : ℝ)^2 *
      Real.exp ((‖A‖ + ‖B‖) / n) := by
    rw [hP_def, hQ_def]
    -- From norm_exp_mul_exp_sub_exp_add' applied to a = A/n, b = B/n
    -- ‖exp(A/n)*exp(B/n) - exp((A+B)/n)‖ ≤ 2 * ‖A/n‖ * ‖B/n‖ * exp(‖A/n‖+‖B/n‖)
    -- = 2 * (‖A‖/n) * (‖B‖/n) * exp((‖A‖+‖B‖)/n)
    -- = 2 * ‖A‖ * ‖B‖ / n² * exp((‖A‖+‖B‖)/n)
    sorry
  -- Step 5: Bound max(‖P‖, ‖Q‖)
  -- ‖P‖ ≤ exp(‖A‖/n) * exp(‖B‖/n) = exp((‖A‖+‖B‖)/n)
  -- ‖Q‖ ≤ exp(‖A+B‖/n) ≤ exp((‖A‖+‖B‖)/n)
  -- So max(‖P‖, ‖Q‖) ≤ exp((‖A‖+‖B‖)/n)
  have h_max : max ‖P‖ ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
    sorry
  -- Step 6: Combine
  -- ‖P^n - Q^n‖ ≤ n * (2‖A‖‖B‖/n² * exp(s/n)) * exp(s/n)^{n-1}
  --             = 2‖A‖‖B‖/n * exp(s/n)^n
  --             = 2‖A‖‖B‖/n * exp(s)         where s = ‖A‖+‖B‖
  --             ≤ C/n                           ✓
  calc ‖P ^ n - Q ^ n‖
      ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (2 * ‖A‖ * ‖B‖ / (n : ℝ)^2 * Real.exp ((‖A‖ + ‖B‖) / n)) *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ (n - 1) := by
        gcongr
        exact pow_le_pow_left (le_max_left _ _ ▸ norm_nonneg P ▸ le_refl _
          |>.trans (le_max_left _ _) |>.trans h_max |>.le
          |> Real.exp_nonneg _ |>.le |> le_refl _ |>.le
          |> sorry) h_max (n - 1)
    _ = 2 * ‖A‖ * ‖B‖ / n *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ n := by
        -- n/n² = 1/n, and exp(s/n) * exp(s/n)^{n-1} = exp(s/n)^n
        have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
        field_simp
        ring
    _ ≤ 2 * ‖A‖ * ‖B‖ / n * Real.exp (‖A‖ + ‖B‖) := by
        gcongr
        -- exp(s/n)^n ≤ exp(s): this follows from convexity of exp
        -- exp(s/n) ≤ 1 + s/n (when we only need exp(s/n)^n ≤ exp(s))
        -- Actually exp(s/n)^n = exp(s) exactly! Not an inequality.
        -- exp(x)^n = exp(n*x), so exp(s/n)^n = exp(n * s/n) = exp(s)
        rw [← Real.exp_natMul, Nat.cast_comm]
        simp [mul_div_cancel₀]
        sorry
    _ ≤ (2 * ‖A‖ * ‖B‖ * Real.exp (2 * (‖A‖ + ‖B‖)) + 1) / n := by
        sorry

/-- **Main theorem**: The Lie-Trotter product formula. -/
theorem lie_trotter (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp 𝕂 ((n : 𝕂)⁻¹ • A) *
                      exp 𝕂 ((n : 𝕂)⁻¹ • B)) ^ n)
      atTop (nhds (exp 𝕂 (A + B))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get the error rate constant
  obtain ⟨C, hC_pos, hC_bound⟩ := lie_trotter_error_rate (𝕂 := 𝕂) A B
  -- Choose N such that C/N < ε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  calc ‖(exp 𝕂 ((↑n : 𝕂)⁻¹ • A) * exp 𝕂 ((↑n : 𝕂)⁻¹ • B)) ^ n - exp 𝕂 (A + B)‖
      ≤ C / n := hC_bound n hn_pos
    _ ≤ C / (N + 1) := by
        apply div_le_div_of_nonneg_left hC_pos (by positivity : (0:ℝ) < N + 1)
        exact_mod_cast hn
    _ ≤ C / N.succ := by norm_cast
    _ < ε := by
        rw [div_lt_iff (by positivity : (0 : ℝ) < ↑N.succ)]
        calc C = C / ε * ε := by field_simp
          _ < (N + 1) * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              calc C / ε < N := hN
                _ < N + 1 := by linarith
          _ = ↑N.succ * ε := by push_cast; ring

end Assembly

/-!
## Summary of Proof Dependencies

The proof has the following dependency structure:

```
lie_trotter (main theorem)
├── lie_trotter_error_rate (O(1/n) convergence)
│   ├── norm_pow_sub_pow_le' (telescoping norm bound)
│   │   └── telescoping_direct (algebraic identity)  ✓ PROVED
│   ├── norm_exp_mul_exp_sub_exp_add' (step error)
│   │   └── exp_sub_one_sub_bound_real (remainder bound)
│   ├── exp_div_pow (exp(a/n)^n = exp(a))
│   │   └── NormedSpace.exp properties from mathlib
│   └── norm_exp_smul_le (exp norm bound)
└── exists_nat_gt (Archimedean property) ← from mathlib
```

### Status:
- ✅ `telescoping_direct` — fully proved
- ✅ `norm_pow_sub_pow_le'` — proved modulo `gcongr` details
- ✅ `lie_trotter` — proved assuming `lie_trotter_error_rate`
- 🔶 `lie_trotter_error_rate` — structure complete, some `sorry`s in calc chains
- 🔶 `exp_div_pow` — needs mathlib API (should follow from `exp_nsmul`)
- 🔴 `norm_exp_mul_exp_sub_exp_add'` — hardest lemma, needs power series work
- 🔴 `exp_sub_one_sub_bound_real` — real analysis, feasible but tedious
-/
