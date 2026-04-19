/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multinomial expansion of `iteratedDeriv` for products of exp factors

This module provides a general framework for computing iterated derivatives
of products of exp factors at τ=0 via iterated Leibniz rule. It defines
`prodExpList` (product of `exp((cᵢ·τ)•Xᵢ)` factors) and associated sums.

The full multinomial-formula development (h2, h3, h4 iteratedDeriv identities
for s4Func) is incremental research work. This file provides the foundational
definitions and base cases; the full identities require additional combinatorial
reasoning deferred to future sessions.

## What's here

- `prodExpList` definition (the k-factor exp product)
- `sumDList` definition (sum of operator insertions Σcᵢ•Xᵢ)
- `sumCommList` definition (sum of commutators Σᵢ<ⱼ[dᵢ,dⱼ])
- `s4DList` / `s4Func_eq_prodExpList`: connect to s4Func
- `sumDList_s4DList = A + B` (via `suzuki4_free_term`)
- `contDiffAt_prodExpList` / `prodExpList_at_zero`: basic smoothness + boundary

## Remaining work

The multinomial formulas for `iteratedDeriv k (prodExpList L) 0` at k=1, 2, 3, 4
and the instantiation for s4Func. Each requires careful handling of
`iteratedDeriv_mul` / `iteratedDeriv_fun_mul` + Pi.mul vs fun form + ℕ-smul
vs ring multiplication. See the CAPSTONE theorem in `Suzuki4Phase5.lean` for
the architectural reduction of the outer sorries to these three identities
(h2, h3, h4).
-/

import LieTrotter.Suzuki4Phase5

noncomputable section

open NormedSpace Set

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Definitions
-/

/-- Product of exp factors for a list of (X, c) pairs:
  `prodExpList [(X₁,c₁), ..., (Xₙ,cₙ)] τ = exp((c₁τ)•X₁) · ... · exp((cₙτ)•Xₙ)`. -/
noncomputable def prodExpList : List (𝔸 × ℝ) → ℝ → 𝔸
  | [], _ => 1
  | (X, c) :: L, τ => exp ((c * τ) • X) * prodExpList L τ

/-- Sum of operator insertions: `sumDList [(X₁,c₁), ..., (Xₙ,cₙ)] = Σᵢ cᵢ•Xᵢ`. -/
noncomputable def sumDList : List (𝔸 × ℝ) → 𝔸
  | [] => 0
  | (X, c) :: L => c • X + sumDList L

/-- Sum of commutators `[dᵢ, dⱼ]` for i<j in the list.
  Inductive definition: cons prepends by adding `[d_head, Σ_tail d_j]`. -/
noncomputable def sumCommList : List (𝔸 × ℝ) → 𝔸
  | [] => 0
  | (X, c) :: L => sumCommList L + ((c • X) * sumDList L - sumDList L * (c • X))

/-!
## Basic properties
-/

@[simp] lemma prodExpList_nil (τ : ℝ) : prodExpList ([] : List (𝔸 × ℝ)) τ = 1 := rfl

@[simp] lemma prodExpList_cons (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) (τ : ℝ) :
    prodExpList ((X, c) :: L) τ = exp ((c * τ) • X) * prodExpList L τ := rfl

@[simp] lemma sumDList_nil : sumDList ([] : List (𝔸 × ℝ)) = 0 := rfl

@[simp] lemma sumDList_cons (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) :
    sumDList ((X, c) :: L) = c • X + sumDList L := rfl

@[simp] lemma sumCommList_nil : sumCommList ([] : List (𝔸 × ℝ)) = 0 := rfl

@[simp] lemma sumCommList_cons (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) :
    sumCommList ((X, c) :: L) = sumCommList L +
      ((c • X) * sumDList L - sumDList L * (c • X)) := rfl

/-!
## ContDiff of prodExpList

Each exp factor is `ContDiffAt` (from `contDiffAt_exp_smul_mul`), and product
of ContDiffAt is ContDiffAt.
-/

lemma contDiffAt_prodExpList (L : List (𝔸 × ℝ)) (τ : ℝ) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (prodExpList L) τ := by
  induction L with
  | nil =>
    show ContDiffAt ℝ n (fun _ : ℝ => (1 : 𝔸)) τ
    exact contDiffAt_const
  | cons p L ih =>
    obtain ⟨X, c⟩ := p
    show ContDiffAt ℝ n (fun τ => exp ((c * τ) • X) * prodExpList L τ) τ
    exact (contDiffAt_exp_smul_mul X c τ).mul ih

/-!
## Order-0: `prodExpList L 0 = 1`
-/

lemma prodExpList_at_zero (L : List (𝔸 × ℝ)) : prodExpList L 0 = 1 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨X, c⟩ := p
    show exp ((c * 0) • X) * prodExpList L 0 = 1
    rw [mul_zero, zero_smul, exp_zero, ih, one_mul]

lemma iteratedDeriv_prodExpList_order0 (L : List (𝔸 × ℝ)) :
    iteratedDeriv 0 (prodExpList L) 0 = 1 := by
  rw [iteratedDeriv_zero]
  exact prodExpList_at_zero L

/-!
## Order-1: HasDerivAt at 0 gives `sumDList L`
-/

/-- **Order-1 HasDerivAt**: `HasDerivAt (prodExpList L) (sumDList L) 0`. -/
lemma hasDerivAt_prodExpList_at_zero (L : List (𝔸 × ℝ)) :
    HasDerivAt (prodExpList L) (sumDList L) 0 := by
  induction L with
  | nil =>
    show HasDerivAt (fun _ : ℝ => (1 : 𝔸)) 0 0
    exact hasDerivAt_const 0 1
  | cons p L ih =>
    obtain ⟨X, c⟩ := p
    show HasDerivAt (fun τ => exp ((c * τ) • X) * prodExpList L τ) (c • X + sumDList L) 0
    have h_exp : HasDerivAt (fun τ : ℝ => exp ((c * τ) • X)) (c • X) 0 := by
      have h := hasDerivAt_exp_smul_mul X c 0
      -- h : HasDerivAt _ (c • (X * exp((c*0)•X))) 0
      rw [mul_zero, zero_smul, exp_zero, mul_one] at h
      -- h : HasDerivAt _ (c • X) 0
      exact h
    have h_mul := h_exp.mul ih
    -- h_mul : HasDerivAt (fun τ => exp((c*τ)•X) * prodExpList L τ)
    --   (c • X * prodExpList L 0 + exp((c*0)•X) * sumDList L) 0
    convert h_mul using 1
    rw [mul_zero, zero_smul, exp_zero, one_mul, prodExpList_at_zero, mul_one]

/-- **Order-1 at 0**: `iteratedDeriv 1 (prodExpList L) 0 = sumDList L`. -/
lemma iteratedDeriv_prodExpList_order1 (L : List (𝔸 × ℝ)) :
    iteratedDeriv 1 (prodExpList L) 0 = sumDList L := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_prodExpList_at_zero L).deriv

/-!
## Order-2: `iteratedDeriv 2 (prodExpList L) 0 = (sumDList L)² + sumCommList L`

Proof by induction on L using `iteratedDeriv_fun_mul` with n=2. In the
cons case `(X, c) :: L'`:

  iDer 2 (e·prodExpList L') 0
    = 1·iDer 0 e·iDer 2 L' + 2·iDer 1 e·iDer 1 L' + 1·iDer 2 e·iDer 0 L'
    = iDer 2 L' + 2(c•X)·sumDList L' + (c•X)²
    = [(sumDList L')² + sumCommList L'] + 2(c•X)·sumDList L' + (c•X)²   [by IH]

Target RHS: (c•X + sumDList L')² + [sumCommList L' + ((c•X)·sumDList L' - sumDList L'·(c•X))]
    = (c•X)² + (c•X)·sumDList L' + sumDList L'·(c•X) + (sumDList L')²
      + sumCommList L' + (c•X)·sumDList L' - sumDList L'·(c•X)
    = (c•X)² + 2·(c•X)·sumDList L' + (sumDList L')² + sumCommList L'

Equal. The `noncomm_ring` tactic handles the algebraic simplification.
-/

lemma iteratedDeriv_prodExpList_order2 (L : List (𝔸 × ℝ)) :
    iteratedDeriv 2 (prodExpList L) 0 = (sumDList L) ^ 2 + sumCommList L := by
  induction L with
  | nil =>
    show iteratedDeriv 2 (fun _ : ℝ => (1 : 𝔸)) 0 = 0 ^ 2 + 0
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp
  | cons p L ih =>
    obtain ⟨X, c⟩ := p
    -- Apply iteratedDeriv_fun_mul with n=2
    show iteratedDeriv 2 (fun τ => exp ((c * τ) • X) * prodExpList L τ) 0 =
      (c • X + sumDList L) ^ 2 +
        (sumCommList L + (c • X * sumDList L - sumDList L * (c • X)))
    rw [iteratedDeriv_fun_mul (n := 2) (contDiffAt_exp_smul_mul X c 0)
      (contDiffAt_prodExpList L 0)]
    -- Sum unfolds to 3 terms
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDeriv_exp_smul_mul_at_zero,
      show (2 - 0 : ℕ) = 2 from rfl, show (2 - 1 : ℕ) = 1 from rfl,
      show (2 - 2 : ℕ) = 0 from rfl, pow_zero, pow_one, mul_one]
    rw [iteratedDeriv_prodExpList_order0, iteratedDeriv_prodExpList_order1, ih]
    -- Nat.choose normalizations
    have h0 : (Nat.choose 2 0 : ℕ) = 1 := rfl
    have h1 : (Nat.choose 2 1 : ℕ) = 2 := rfl
    have h2 : (Nat.choose 2 2 : ℕ) = 1 := rfl
    rw [h0, h1, h2]
    simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one, pow_two]
    -- Goal after pow_two: all squares become x*x products
    -- The remaining goal is a pure ring + smul identity.
    -- `noncomm_ring` distributes but may leave smul-equivalent forms.
    -- Use combination of noncomm_ring + module for mixed-mode handling.
    have h_expand : (c • X + sumDList L) * (c • X + sumDList L) =
        (c • X) * (c • X) + (c • X) * sumDList L
        + sumDList L * (c • X) + sumDList L * sumDList L := by
      rw [mul_add, add_mul, add_mul]; abel
    rw [h_expand]
    -- Goal has `2 * y` from Nat.cast on LHS; RHS has additive structure.
    -- Convert `2 * y = y + y` to make LHS match.
    rw [show (2 : 𝔸) * (c • X) * sumDList L
        = (c • X) * sumDList L + (c • X) * sumDList L from by noncomm_ring]
    abel

/-!
## Application to s4Func: list representation

`s4DList` gives the 11-factor list for s4Func.
-/

/-- List of (operator, coefficient) pairs for s4Func's 11 exp factors. -/
noncomputable def s4DList (A B : 𝔸) (p : ℝ) : List (𝔸 × ℝ) :=
  [(A, p/2), (B, p), (A, p), (B, p),
   (A, (1-3*p)/2), (B, 1-4*p), (A, (1-3*p)/2),
   (B, p), (A, p), (B, p), (A, p/2)]

/-- `sumDList (s4DList A B p) = A + B`. The 11 insertion coefficients sum to the
  palindromic free term (matches `suzuki4_free_term`). -/
lemma sumDList_s4DList (A B : 𝔸) (p : ℝ) :
    sumDList (s4DList A B p) = A + B := by
  unfold s4DList
  simp only [sumDList_cons, sumDList_nil, add_zero]
  have h := suzuki4_free_term A B p
  linear_combination (norm := module) h

/-- `s4Func A B p = prodExpList (s4DList A B p)`, bridging the left-associated
  s4Func product with the right-associated prodExpList foldr. -/
lemma s4Func_eq_prodExpList (A B : 𝔸) (p : ℝ) :
    s4Func A B p = prodExpList (s4DList A B p) := by
  funext τ
  show s4Func A B p τ = prodExpList (s4DList A B p) τ
  unfold s4Func s4DList
  simp only [prodExpList_cons, prodExpList_nil, mul_one]
  noncomm_ring

/-!
## Helpers for `sumCommList` reductions

Products `(c • X) * (c' • X)` and `(c • X) * (c' • Y)` normalize via
`Algebra.smul_mul_assoc` + `Algebra.mul_smul_comm` + `smul_smul` to
`(c * c') • (X * X)` and `(c * c') • (X * Y)` respectively.
-/

/-- `(c • X) * (c' • X) = (c*c') • (X * X)`. -/
lemma smul_mul_smul_same (X : 𝔸) (c c' : ℝ) :
    (c • X) * (c' • X) = (c * c') • (X * X) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- `(c • X) * (c' • Y) = (c*c') • (X * Y)`. -/
lemma smul_mul_smul_diff (X Y : 𝔸) (c c' : ℝ) :
    (c • X) * (c' • Y) = (c * c') • (X * Y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-- `(c • X) * (c' • Y) * (c'' • Z) = (c*c'*c'') • (X * Y * Z)`. Cubic smul-mul. -/
lemma smul_mul_smul_mul_smul (X Y Z : 𝔸) (c c' c'' : ℝ) :
    (c • X) * (c' • Y) * (c'' • Z) = (c * c' * c'') • (X * Y * Z) := by
  rw [smul_mul_smul_diff, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

/-!
## Remaining bridge: `sumCommList (s4DList A B p) = 0`

The unfold of `sumCommList` on `s4DList` produces 10 nested terms. After
distributing via `mul_add`, `sub_mul`, `smul_mul_smul_same`/`_diff`, and
`sub_self` (to cancel same-type A-A and B-B pairs), the result is a linear
combination of `(A*B - B*A)` with scalar coefficients that match
`s4_pairwise_commutator_sum_zero`.

**Obstacle in current Lean**: `linear_combination (norm := module)` applied
against `s4_pairwise_commutator_sum_zero` fails with `1 = 0` residual —
linear_combination selects the wrong scalar multiplier. Several approaches
tried but none closed:
- `linear_combination h` (default ring norm): fails on non-commutative 𝔸
- `linear_combination (norm := module) h`: module doesn't detect single-basis
  structure after cascaded smul-simp
- `linear_combination (norm := abel)` similar issue

**Path forward**: Factor `(A*B - B*A)` out explicitly via `← add_smul` /
`← neg_smul` simp rewrites to reduce to a pure scalar identity in ℝ, then
close via `ring` over ℝ. Requires careful rewriting choreography.

**Conditional h2**: assuming `sumCommList_s4DList = 0`, h2 follows in three
lines — see theorem statement below.
-/

/-!
## Commutator-expansion helpers

Direct scalar-multiplied commutator identities that avoid the simp pitfalls
of cascaded `smul_mul_assoc`/`mul_smul_comm` rewrites.
-/

/-- `(c • X) * (c' • Y) - (c' • Y) * (c • X) = (c * c') • (X * Y - Y * X)`. -/
lemma smul_mul_sub_comm (X Y : 𝔸) (c c' : ℝ) :
    (c • X) * (c' • Y) - (c' • Y) * (c • X) = (c * c') • (X * Y - Y * X) := by
  rw [smul_mul_smul_diff, smul_mul_smul_diff]
  rw [show c' * c = c * c' from by ring]
  rw [← smul_sub]

/-- Commutator of `(c • X)` with `sumDList L` expands as a folded sum:
  `(c • X) * sumDList L - sumDList L * (c • X) = Σⱼ (c * cⱼ) • (X * Xⱼ - Xⱼ * X)`. -/
lemma smul_mul_sumDList_sub_sumDList_mul_smul (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) :
    (c • X) * sumDList L - sumDList L * (c • X) =
      L.foldr (fun (p : 𝔸 × ℝ) acc => (c * p.2) • (X * p.1 - p.1 * X) + acc) 0 := by
  induction L with
  | nil =>
    show (c • X) * 0 - 0 * (c • X) = 0
    rw [mul_zero, zero_mul, sub_zero]
  | cons p L ih =>
    obtain ⟨Y, c'⟩ := p
    show (c • X) * (c' • Y + sumDList L) - (c' • Y + sumDList L) * (c • X) =
      (c * c') • (X * Y - Y * X) +
        L.foldr (fun p acc => (c * p.2) • (X * p.1 - p.1 * X) + acc) 0
    rw [mul_add, add_mul]
    rw [show (c • X * (c' • Y) + c • X * sumDList L - (c' • Y * (c • X) + sumDList L * (c • X))) =
        ((c • X * (c' • Y) - c' • Y * (c • X)) +
         (c • X * sumDList L - sumDList L * (c • X))) from by abel]
    rw [smul_mul_sub_comm, ih]

/-- **Explicit form of sumCommList**: for each cons step, the commutator-sum
  helper gives us an explicit expansion. -/
lemma sumCommList_cons_expand (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) :
    sumCommList ((X, c) :: L) = sumCommList L +
      L.foldr (fun (p : 𝔸 × ℝ) acc => (c * p.2) • (X * p.1 - p.1 * X) + acc) 0 := by
  rw [sumCommList_cons]
  rw [show (c • X) * sumDList L - sumDList L * (c • X) =
      L.foldr (fun p acc => (c * p.2) • (X * p.1 - p.1 * X) + acc) 0 from
    smul_mul_sumDList_sub_sumDList_mul_smul X c L]

/-- `sumCommList (s4DList A B p) = 0`. -/
lemma sumCommList_s4DList (A B : 𝔸) (p : ℝ) :
    sumCommList (s4DList A B p) = 0 := by
  unfold s4DList
  -- Unfold cons-by-cons using sumCommList_cons_expand, simplifying the folded
  -- inner sums at each step. At each cons (X, c), the expansion contributes
  -- Σⱼ (c * cⱼ) • (X * Xⱼ - Xⱼ * X) for the tail.
  simp only [sumCommList_cons_expand, sumCommList_nil, List.foldr,
    zero_add, add_zero]
  -- Goal: sum of 10 nested foldr contributions = 0. Each contribution is a
  -- smul of (X * Y - Y * X) where X, Y ∈ {A, B}.
  -- For X = Y: X*X - X*X = 0, so term vanishes.
  -- For X ≠ Y: (c * c') • (A * B - B * A) or (c * c') • (B * A - A * B).
  -- Rearrange as (scalar) • (A * B - B * A). Compare to s4_pairwise_commutator_sum_zero.
  have h := s4_pairwise_commutator_sum_zero A B p
  -- Negate B*A - A*B to -(A*B - B*A)
  have hneg : ∀ (c : ℝ), c • (B * A - A * B) = -(c • (A * B - B * A)) := fun c => by
    rw [← smul_neg]; congr 1; noncomm_ring
  -- Apply simp to fold same-type pairs to 0 and convert B*A - A*B to -(A*B - B*A)
  simp only [sub_self, smul_zero, add_zero, zero_add, hneg]
  -- Goal should now match h after additive reordering.
  linear_combination (norm := module) h

/-- **h2 PROVED UNCONDITIONALLY**: `iteratedDeriv 2 (s4Func A B p) 0 = (A + B)^2`. -/
theorem iteratedDeriv_s4Func_order2_eq_sq (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (s4Func A B p) 0 = (A + B) ^ 2 := by
  rw [s4Func_eq_prodExpList, iteratedDeriv_prodExpList_order2,
    sumDList_s4DList, sumCommList_s4DList, add_zero]

/-!
## Order-3 multinomial framework (h3 infrastructure)

The order-3 formula for prodExpList has form:
  `iteratedDeriv 3 (prodExpList L) 0 = (sumDList L)^3 + sumTripleCorr L`

where `sumTripleCorr L` captures all non-commutative corrections to the
naive cube. The recurrence (from order-3 Leibniz on (X,c)::L):

  `sumTripleCorr ((X,c)::L) = sumTripleCorr L + 3·(c•X)·sumCommList L
    + 2·(c•X)·[c•X, sumDList L] + [c•X, sumDList L]·(c•X)
    + 2·[c•X, sumDList L]·sumDList L + sumDList L·[c•X, sumDList L]`

This reduces to the scalar identity `4p³ + q³ = 0` (Phase 3) when applied
to s4DList with Suzuki `p`.
-/

/-- Commutator of `d = c•X` with `sumDList L`, in anticipation of the order-3
  correction formula. -/
noncomputable def commSingleList (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) : 𝔸 :=
  (c • X) * sumDList L - sumDList L * (c • X)

/-- Sum of cubic corrections, captures non-commutative pieces beyond `(Σ dⱼ)³`. -/
noncomputable def sumTripleCorr : List (𝔸 × ℝ) → 𝔸
  | [] => 0
  | (X, c) :: L => sumTripleCorr L + 3 • ((c • X) * sumCommList L)
      + (2 • ((c • X) * commSingleList X c L) + commSingleList X c L * (c • X))
      + (2 • (commSingleList X c L * sumDList L) + sumDList L * commSingleList X c L)

@[simp] lemma sumTripleCorr_nil : sumTripleCorr ([] : List (𝔸 × ℝ)) = 0 := rfl

@[simp] lemma sumTripleCorr_cons (X : 𝔸) (c : ℝ) (L : List (𝔸 × ℝ)) :
    sumTripleCorr ((X, c) :: L) = sumTripleCorr L + 3 • ((c • X) * sumCommList L)
      + (2 • ((c • X) * commSingleList X c L) + commSingleList X c L * (c • X))
      + (2 • (commSingleList X c L * sumDList L) + sumDList L * commSingleList X c L) :=
  rfl

/-- **Order-3 multinomial formula** for prodExpList at τ=0. -/
lemma iteratedDeriv_prodExpList_order3 (L : List (𝔸 × ℝ)) :
    iteratedDeriv 3 (prodExpList L) 0 = (sumDList L) ^ 3 + sumTripleCorr L := by
  induction L with
  | nil =>
    show iteratedDeriv 3 (fun _ : ℝ => (1 : 𝔸)) 0 = 0 ^ 3 + 0
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    simp
  | cons p L ih =>
    obtain ⟨X, c⟩ := p
    -- Apply iteratedDeriv_fun_mul at n=3
    show iteratedDeriv 3 (fun τ => exp ((c * τ) • X) * prodExpList L τ) 0 = _
    rw [iteratedDeriv_fun_mul (n := 3) (contDiffAt_exp_smul_mul X c 0)
      (contDiffAt_prodExpList L 0)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDeriv_exp_smul_mul_at_zero,
      show (3 - 0 : ℕ) = 3 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
      show (3 - 2 : ℕ) = 1 from rfl, show (3 - 3 : ℕ) = 0 from rfl,
      pow_zero, pow_one, mul_one]
    rw [iteratedDeriv_prodExpList_order0, iteratedDeriv_prodExpList_order1, ih]
    rw [iteratedDeriv_prodExpList_order2]
    -- Nat.choose casts for n=3
    have h0 : (Nat.choose 3 0 : ℕ) = 1 := rfl
    have h1 : (Nat.choose 3 1 : ℕ) = 3 := rfl
    have h2 : (Nat.choose 3 2 : ℕ) = 3 := rfl
    have h3 : (Nat.choose 3 3 : ℕ) = 1 := rfl
    rw [h0, h1, h2, h3]
    simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one]
    -- Goal: a ring identity. Use `show` to name everything and close with abel.
    show (sumDList L)^3 + sumTripleCorr L +
         (3 : 𝔸) * (c • X) * ((sumDList L)^2 + sumCommList L) +
         (3 : 𝔸) * (c • X)^2 * sumDList L + (c • X)^3 =
      (c • X + sumDList L)^3 +
      (sumTripleCorr L + 3 • ((c • X) * sumCommList L) +
       (2 • ((c • X) * commSingleList X c L) + commSingleList X c L * (c • X)) +
       (2 • (commSingleList X c L * sumDList L) + sumDList L * commSingleList X c L))
    -- Unfold commSingleList and powers; reduce to an identity in +, *, •
    unfold commSingleList
    -- Convert `3 * y` and `3 • y` to explicit sums
    have h3mul_nat : ∀ (y : 𝔸), (3 : ℕ) • y = y + y + y := fun y => by
      show _ = _; module
    have h2mul_nat : ∀ (y : 𝔸), (2 : ℕ) • y = y + y := fun y => by
      show _ = _; module
    simp only [h3mul_nat, h2mul_nat, pow_two, pow_three]
    -- Convert `(3 : 𝔸) * y` to `y + y + y`
    have h3mul_ring : ∀ (y : 𝔸), (3 : 𝔸) * y = y + y + y := fun y => by
      rw [show (3 : 𝔸) = 1 + 1 + 1 from by norm_num]; noncomm_ring
    simp only [h3mul_ring, mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
    abel

/-!
## h3 conditional bridge

Given `sumTripleCorr (s4DList A B p) = 0` (the Phase 3 operator-level identity),
h3 follows immediately from the order-3 multinomial formula.

**Unconditional proof of the bridge**: unfolds the 11-element sumTripleCorr,
which produces a sum of 10 cons-contributions. Each involves products of dⱼ's
and `commSingleList X c (suffix)` terms. Expanded in the basis of 3-fold
operator monomials {ABA, AB², A²B, BAB, BA², B²A}, the coefficients are
multiples of `4p³ + q³` (all 6 of them), so the sum vanishes for Suzuki p
via `suzuki4_phase3_{aba,a2b,bab}` + `suzuki4_cubic_cancel`.

Estimated effort: ~300-500 lines for the full unfold and coefficient matching.
Deferred to future session.
-/

/-- **h3 conditional on `sumTripleCorr_s4DList = 0`**:
  `iteratedDeriv 3 (s4Func A B p) 0 = (A + B)^3`. -/
theorem iteratedDeriv_s4Func_order3_eq_cb_of_bridge (A B : 𝔸) (p : ℝ)
    (hTriple : sumTripleCorr (s4DList A B p) = 0) :
    iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3 := by
  rw [s4Func_eq_prodExpList, iteratedDeriv_prodExpList_order3,
    sumDList_s4DList, hTriple, add_zero]

/-!
## Alternative: h3 conditional on `IsSuzukiCubic p`

Using the order-3 Leibniz bridge `iteratedDeriv_w4Func_order3_zero_iff_of_order2`
from Suzuki4Phase5.lean, we can express h3 via w4Func:

  Under h2 (PROVED!), order-3 vanishing of w4Func ⟺ h3.

So h3 equals `iteratedDeriv 3 (w4Func A B p) 0 = 0`.

Proving this directly via the w4Func side also requires operator-level
Phase 3 analysis (different bookkeeping but same algebraic content).
-/

/-- **h3 via w4Func bridge**: `iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3`,
  given `iteratedDeriv 3 (w4Func A B p) 0 = 0`.

  This uses the Phase 5 bridge `iteratedDeriv_w4Func_order3_zero_iff_of_order2`
  together with our proved h2 (`iteratedDeriv_s4Func_order2_eq_sq`). -/
theorem iteratedDeriv_s4Func_order3_eq_cb_via_w4Func (A B : 𝔸) (p : ℝ)
    (hW4 : iteratedDeriv 3 (w4Func A B p) 0 = 0) :
    iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  exact (iteratedDeriv_w4Func_order3_zero_iff_of_order2 A B p h2).mp hW4

/-- **h4 via w4Func bridge**: `iteratedDeriv 4 (s4Func A B p) 0 = (A + B) ^ 4`,
  given `iteratedDeriv 4 (w4Func A B p) 0 = 0` and h3. -/
theorem iteratedDeriv_s4Func_order4_eq_q_via_w4Func (A B : 𝔸) (p : ℝ)
    (h3 : iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3)
    (hW4 : iteratedDeriv 4 (w4Func A B p) 0 = 0) :
    iteratedDeriv 4 (s4Func A B p) 0 = (A + B) ^ 4 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  exact (iteratedDeriv_w4Func_order4_zero_iff_of_order23 A B p h2 h3).mp hW4

/-- **Order-2 vanishing of w4Func UNCONDITIONALLY** via proved h2. -/
theorem iteratedDeriv_w4Func_order2_eq_zero (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 2 (w4Func A B p) 0 = 0 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  exact (iteratedDeriv_w4Func_order2_zero_iff A B p).mpr h2

/-!
## Equivalences for h3 via the w4Func bridge

Given proved h2, the three forms of "h3" are equivalent:
  (a) `iteratedDeriv 3 (s4Func A B p) 0 = (A + B)^3`
  (b) `iteratedDeriv 3 (w4Func A B p) 0 = 0`
  (c) `sumTripleCorr (s4DList A B p) = 0`

Any of these proved gives the others. Similarly for h4.
-/

/-- Equivalence (a) ↔ (b) for h3 via proved h2. -/
theorem iteratedDeriv_s4Func_order3_iff_w4Func_zero (A B : 𝔸) (p : ℝ) :
    iteratedDeriv 3 (s4Func A B p) 0 = (A + B) ^ 3 ↔
      iteratedDeriv 3 (w4Func A B p) 0 = 0 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  exact (iteratedDeriv_w4Func_order3_zero_iff_of_order2 A B p h2).symm

/-!
## Operator-level order-3 identity (stated as hypothesis for now)

The full unconditional proof of h3 requires the operator-level identity
  `sumTripleCorr (s4DList A B p) = 0` (for Suzuki p with `4p³ + q³ = 0`)

This reduces via cons-by-cons expansion to the Phase 3 polynomial identities:
- `suzuki4_phase3_aba`: `-30p³ + 24p² - 6p + 1/2 = 0`
- `suzuki4_phase3_a2b`: `15p³ - 12p² + 3p - 1/4 = 0`
- `suzuki4_phase3_bab`: `60p³ - 48p² + 12p - 1 = 0`

all equivalent to `4p³ + (1-4p)³ = 0` (the Suzuki cubic).

Given sumTripleCorr's complex recurrence (3 structural terms per cons),
unfolding for the 11-element s4DList produces ~500 operator-monomial terms.
Coefficient-matching against the 6 Phase 3 monomials (ABA, AB², A²B, BAB, BA², B²A)
requires careful accounting.

**Unconditional Suzuki-specific bridge** (future work, needs the expansion).
-/

/-!
## Final packaged theorem: S₄ O(t⁵) given w4Func vanishings (with h2 FREE)

Using our proved h2, the remaining hypotheses for the CAPSTONE theorem reduce
to `iteratedDeriv k (w4Func A B p) 0 = 0` for k=3 and k=4 (order-1 and order-2
being automatic from `w4Deriv_at_zero` and h2 respectively).
-/

section AntiHermitian_h3_h4

variable [StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]

/-- **S₄ O(t⁵) unconditional on h2**: given order-3 and order-4 vanishings of w4Func,
  conclude the S₄ O(t⁵) bound. The order-2 identity (h2) is filled in from
  our proved `iteratedDeriv_s4Func_order2_eq_sq`.

  This is a strict strengthening of the CAPSTONE: h2 is no longer a hypothesis. -/
theorem norm_suzuki4_order5_with_h2_and_w4Func_vanishings (A B : 𝔸)
    (hA : star A = -A) (hB : star B = -B) (p : ℝ) {t : ℝ} (ht : 0 < t)
    (hW3 : iteratedDeriv 3 (w4Func A B p) 0 = 0)
    (hW4 : iteratedDeriv 4 (w4Func A B p) 0 = 0) :
    ∃ C ≥ 0, ‖suzuki4Exp A B p t - exp (t • (A + B))‖ ≤ C * t ^ 5 := by
  have h2 := iteratedDeriv_s4Func_order2_eq_sq A B p
  have h3 := iteratedDeriv_s4Func_order3_eq_cb_via_w4Func A B p hW3
  have h4 := iteratedDeriv_s4Func_order4_eq_q_via_w4Func A B p h3 hW4
  exact norm_suzuki4_order5_of_s4Func_iteratedDerivs A B hA hB p ht h2 h3 h4

end AntiHermitian_h3_h4

end
