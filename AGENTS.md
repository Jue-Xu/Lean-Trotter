# Lie–Trotter Product Formula — Lean 4 Formalization

## Status (2026-08-02): 0 sorries, 0 own axioms, 0 transitive project axioms for all release headlines

**Fourth-order Trotter formula error bound AND its O(1/n⁴) total-error
convergence theorem are fully proved at the project level.** `#print axioms`
on all release headlines (`norm_suzuki4_childs_form_via_level3`,
`norm_suzuki4_level3_bch`, `norm_suzuki4_level2_bch`,
`bch_w4Deriv_level3_tight`, `bch_w4Deriv_quintic_level2`,
`bch_uniform_integrated`, `norm_suzuki4_level4_uniform`,
`bch_iteratedDeriv_s4Func_order4`, `exists_norm_s4Func_sub_exp_le_t5`,
`suzuki4_convergence_quartic`, `suzuki4_total_error_quartic`, `lie_trotter`)
returns only `[propext, Classical.choice, Quot.sound]` — the standard Lean
foundational axioms.

**The convergence hierarchy is complete:** `lie_trotter` (O(1/n)) →
`symmetric_lie_trotter` (O(1/n²)) → `suzuki4_convergence_quartic` (O(1/n⁴)).

All three formerly-axiomatized `bch_w4Deriv_*` / `bch_uniform_integrated`
results are theorems composing Lean-BCH bridge corollaries with
exp-Lipschitz / triangle-inequality lifts:

| Lean-Trotter theorem | Composes Lean-BCH bridge |
|---|---|
| `bch_w4Deriv_quintic_level2` | `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` |
| `bch_w4Deriv_level3_tight` | `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` |
| `bch_uniform_integrated` | `BCH.suzuki5_log_product_septic_at_suzukiP` |

**The Lean-BCH dependency is pinned at `05e8c52`** (upstream discharge
verified 2026-07-28; integrated status re-audited 2026-08-02). The earlier
`d455ff0` pin had already discharged the B1.c quintic chain; `05e8c52`
also proves the two former septic stepping stones. Consequently the complete
τ⁵ and τ⁷ chains—including `bch_uniform_integrated` and the L4 uniform
refinement—depend only on Lean's standard foundational axioms.

**Headline results:**
1. **Lie–Trotter** (`lie_trotter`, `lie_trotter_error_rate`, O(1/n)) — fully proved.
2. **Strang splitting** (`symmetric_lie_trotter`, O(1/n²)) — fully proved.
3. **Commutator scaling** (first-order, Strang, multi-operator, tighter Strang
   bound `norm_strang_comm_scaling_tight`) — fully proved.
4. **S₄ O(t⁵) abstract form** (`norm_suzuki4_fifth_order`,
   `norm_suzuki4_childs_form`) — closed with explicit residual-bound hypothesis.
4b. **S₄ total-error convergence, O(1/n⁴)** (`suzuki4_convergence_quartic`,
   `suzuki4_total_error_quartic`, `Suzuki4Convergence.lean`, 2026-07-14) —
   fully proved, axiom-free. `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴` and
   `S₄(t/n)ⁿ → exp(t(A+B))`, under only `IsSuzukiCubic p`. Needs **no
   C*-algebra / anti-Hermitian structure** — holds in any complete normed
   algebra with `NormOneClass`. The `*_suzukiP` corollaries discharge even the
   cubic hypothesis at `p = 1/(4−4^{1/3})`, so they are hypothesis-free.
4c. **S₄ sharp (commutator-scaled) bounds, 2026-07-14** — axiom-free, no star
   structure. These put the CAS-certified prefactors **in the statement**, where
   L1–L3 only recorded the *order* `∃C, err ≤ C·τ⁵` (see Lessons 16–17):
   - `norm_suzuki4_level3_explicit`: for `0 ≤ τ < δ`,
     `‖S₄(τ) − exp(τH)‖ ≤ τ⁵·Σγᵢ‖Cᵢ‖ + K'·τ⁶`.
   - `norm_suzuki4_childs_explicit`: the same local form with Childs's
     `Σαᵢ‖Cᵢ‖`.
   - `norm_suzuki4_le_childs_near_zero`: if the leading coefficients differ
     strictly, `‖S₄(τ) − exp(τH)‖ ≤ τ⁵·Σαᵢ‖Cᵢ‖` with **no remainder** on an
     existential neighbourhood of 0. Replaces the vacuous
     `norm_suzuki4_level4_le_childs_when_small`.
   - `suzuki4_total_error_commutator_scaling` (`Suzuki4TightConvergence.lean`):
     for `t ≥ 0` and all sufficiently large `n`,
     **`‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ e^{tK}·(Σγᵢ‖Cᵢ‖)·t⁵/n⁴ + K'/n⁵`** — the
     Childs-shape total error: the `1/n⁴` coefficient is a nested-commutator sum,
     so it collapses as `[A,B] → 0`. Also `..._childs_scaling` with the αᵢ.
4d. **Release corollaries (2026-07-17)** — axiom-free modules for unitary S₄
   total error, commutator-scaled Strang total error, exactness under
   commutation, accuracy-to-step counts, matrix specializations, general-time
   and Gibbs corollaries, and strict comparison of the stored prefactors:
   `Suzuki4UnitaryTotalError.lean`, `StrangTotalErrorCommScaling.lean`,
   `Suzuki4Commute.lean`, `TrotterStepCount.lean`, `MatrixCorollaries.lean`,
   `Suzuki4GapClosers.lean`, and `PrefactorStrict.lean`. The numerical
   companions are documented in `scripts/README.md` and archived as CSVs under
   `claude/`; they are evidence for sampled finite chains, not universal Lean
   theorems.

5. **S₄ BCH-derived bounds** — L1–L4 are axiom-free. NOTE: L1 = L2 = L3
   *as propositions* (all are `∃C, err ≤ C·τ⁵`);
   the coefficient-carrying statements and comparisons live in 4c above:
   - L1 `norm_suzuki4_childs_form_via_level3` (axiom-free) is an order-only
     alias of L3. The coefficient-carrying result is
     `norm_suzuki4_childs_explicit` (Childs's rigorous arXiv Proposition J.1
     coefficients 0.0046–0.0284 plus `K′τ⁶`); the published coefficients are
     not claimed optimal or tight.
   - L2 `norm_suzuki4_level2_bch` (axiom-free) records only the order;
     `norm_suzuki4_level2_explicit` carries the unit coefficients plus `K′τ⁶`.
   - L3 `norm_suzuki4_level3_bch` (axiom-free) records only the order;
     `norm_suzuki4_level3_explicit` carries the γᵢ coefficients plus `K′τ⁶`.
   - **Hypotheses:** L1–L3 need **no star structure** — they hold in
     any complete normed algebra with `NormOneClass`. The C*-algebra typeclasses
     they used to carry were vestigial auto-included section variables (now
     `omit`-ted). Only L4 genuinely requires anti-Hermitian `A, B` in a
     C*-algebra (it carries `star A = -A`, `star B = -B` explicitly).
   - L4 `norm_suzuki4_level4_uniform`: local uniform bound on an existential
     small-τ interval, with R₅ + R₇ (axiom-free at Lean-BCH pin `05e8c52`).
6. **h2 unconditional; h3 under `IsSuzukiCubic p`**
   (`iteratedDeriv_s4Func_order2_eq_sq`, `iteratedDeriv_s4Func_order3_eq_cb`).
7. **h4 (`bch_iteratedDeriv_s4Func_order4`)**: NOW A THEOREM (2026-04-23/24),
   closed via the three-slice chain
   - **SLICE 1** (`Suzuki4BchBound.lean`, `exists_norm_s4Func_sub_exp_le_t5`):
     single-step O(|τ|⁵) bound `‖s4Func A B p τ − exp(τ•(A+B))‖ ≤ C·|τ|⁵`.
     Sorry-free since 2026-04-24 — composes `BCH.norm_s4Func_sub_exp_le_of_IsSuzukiCubic`
     with `BCH.suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic` (Lean-BCH
     opaque-RHS refactor at rev `fffca6c`, corollary closed at rev `c71d8f2`).
   - **SLICE 2** (`TaylorMatch.lean`, `iteratedDeriv_eq_of_norm_le_pow`):
     general Taylor-match-from-norm lemma, sorry-free. If `f, g` are `ContDiff ℝ k`
     and `‖f − g‖ ≤ C·|τ|^{k+1}` near 0, then `iteratedDeriv j f 0 =
     iteratedDeriv j g 0` for `j ≤ k`. Proved via `taylor_isLittleO_univ` +
     polynomial uniqueness.
   - **SLICE 3** (`Suzuki4ViaBCH.lean`): wires SLICE 1 + SLICE 2 +
     Mathlib's `iteratedDeriv_exp_smul_mul_at_zero`.

### Remaining gaps

**Own sorries:** 0. All of `LieTrotter/*.lean` compiles sorry-free.

**Own theorem-level axioms:** 0. All formerly axiomatized BCH-interface
results are now theorems (closed 2026-04-24/26).

**Transitive `sorryAx` dep:** 0.

**Transitive project-specific axioms:** 0. At Lean-BCH pin `05e8c52`,
axiom inspection confirms that the L1–L4 chain—including
`bch_uniform_integrated` and `norm_suzuki4_level4_uniform`—and the convergence
headlines depend only on `[propext, Classical.choice, Quot.sound]`.

There is no remaining sorry/axiom gap in the release theorem chain. `TODO.md`
tracks optional alternative derivations, refinements, and future extensions.

**Retired axioms** (historical):
- `bch_w4Deriv_quintic_level2` — theorem since 2026-04-24 (Lean-BCH bridge).
- `bch_w4Deriv_level3_tight` — theorem since 2026-04-24 (Lean-BCH bridge).
- `bch_uniform_integrated` — theorem since 2026-04-26 (Lean-BCH septic bridge).
- `BCH.symmetric_bch_septic_sub_poly_axiom` and
  `BCH.norm_septic_match_residual_le_axiom` — the former upstream septic
  stepping stones were discharged in Lean-BCH revision `05e8c52` (2026-07-28).
- `bch_iteratedDeriv_s4Func_order4` — theorem since 2026-04-23 (SLICE chain).
- `bch_childs_pointwise_residual` — retired project-local bridge (2026-04-23),
  replaced by the Level-3-derived reproduction of Childs et al.'s rigorous
  arXiv Proposition J.1 bound.
- 4 symmetric-BCH-cubic axioms — retired 2026-04-23 via Lean-BCH direct import.

**Prefactor-bookkeeping note.** The Lean-BCH migration raised the symmetric-BCH
scaling constant from a speculative `10⁴·|c|³·s⁵` to the rigorous
`2·10⁷·|c|³·s⁵` (downstream `suzuki4_bchCubic_sum_bound`: `50000·s⁵ → 10⁸·s⁵`).
This bump is confined to the Path-B composition roadmap
(`norm_suzuki4_order5_via_strang_bch`). It does NOT affect the L1–L4 headline
prefactors, which come from the (now-theorem) `bch_w4Deriv_*` bridges.

See `TODO.md` for the full breakdown of remaining work.

## Goal

Prove the Lie–Trotter product formula in Lean 4 using Mathlib:

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/n}\, e^{B/n}\right)^n$$

for elements $A, B$ in a complete normed algebra $\mathfrak{A}$ over $\mathbb{R}$ or $\mathbb{C}$.

```lean
theorem lie_trotter (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((n : 𝕂)⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)) ^ n)
      atTop (nhds (exp (A + B)))
```

## Constraints

- **Lean:** 4.29.0-rc8 (via `lean-toolchain`)
- **Mathlib:** pinned at commit `06a46dae`
- **Typeclass requirements:** `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]`
- `NormOneClass 𝔸` is required for `norm_pow_le` in newer Mathlib
- `include 𝕂 in` is needed before lemmas where `𝕂` appears in proofs but not types (since `exp` no longer takes a field parameter)

---

## Proof Architecture

```
                        lie_trotter
                            │
                            ▼
                  lie_trotter_error_rate          ← O(1/n) convergence
                   ╱        │         ╲
                  ╱         │          ╲
                 ▼          ▼           ▼
        norm_pow_sub    step_error    exp_div_pow
         _pow_le'     (quadratic)    (exp(a/n)^n=exp(a))
             │              │              │
             ▼              ▼              ▼
     telescoping_     exp_remainder   exp_add_of_commute
       direct          bound           + smul algebra
     (algebraic)      (analysis)       (mathlib API)
```

---

## File Structure

Core Lie–Trotter + Strang + commutator-scaling (all sorry-free):

- `Telescoping.lean`, `ExpBounds.lean`, `StepError.lean`, `ExpDivPow.lean`,
  `Assembly.lean` — Tasks A-E, main `lie_trotter` theorem.
- `StrangSplitting.lean`, `MultiOperator.lean`, `MultiStrang.lean`,
  `Suzuki4.lean` — Strang, multi-operator, Suzuki S₄ integrator definitions.
- `CommutatorScaling.lean`, `MultiCommutatorScaling.lean`,
  `StrangCommutatorScaling.lean`, `MultiStrangCommutatorScaling.lean`,
  `HigherCommutator.lean`, `StrangCommutatorScalingTight.lean` — Track 6
  Duhamel-based commutator-scaling bounds (first-order, Strang, tighter Strang).

S₄ O(t⁵) machinery (Track 7):

- `Suzuki4FullDuhamel.lean` — S₄ O(t³) via 5-S₂ telescoping.
- `Suzuki4CommutatorScaling.lean` — `suzuki4Exp` definition.
- `Suzuki4HasDerivAt.lean` / `Suzuki4Module2.lean` / `Suzuki4Module3.lean` —
  Modules 1-3: HasDerivAt + FTC-2 bridge + residual-bound reduction.
- `Suzuki4Module4.lean` — Module 4a: continuity of `w4Deriv`.
- `Suzuki4DerivExplicit.lean` — Module 4b-A1/A2/A3/B1: explicit derivative.
- `Suzuki4Phase5.lean` — Taylor-reduction + Leibniz bridges + CAPSTONE.
- `Suzuki4MultinomialExpand.lean` — multinomial formulas + h2 + h3.
- `Suzuki4ChildsForm.lean` — Childs-form conditional bound.
- `Suzuki4OrderFive.lean` — S₄ O(t⁵) abstract-form target.
- `Suzuki4StrangBlocks.lean` — S₄ as 5 Strang blocks + Suzuki cubic sum.

BCH bridge + closure of `bch_iteratedDeriv_s4Func_order4` (added 2026-04-23/24):

- `Suzuki4BchBound.lean` — **SLICE 1**: single-step O(|τ|⁵) bound via
  Lean-BCH M6 + `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`.
- `TaylorMatch.lean` — **SLICE 2**: generic Taylor-match-from-norm lemma.
- `Suzuki4ViaBCH.lean` — **SLICE 3** wiring + L1–L4 BCH bounds. The 3 former
  `bch_w4Deriv_*` axioms are now theorems composing Lean-BCH bridge
  corollaries (see top-of-file table).

S₄ total-error convergence (added 2026-07-14):

- `Suzuki4Convergence.lean` — compounds the SLICE 1 step bound into
  `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴` (`suzuki4_total_error_quartic`) and
  `S₄(t/n)ⁿ → exp(t(A+B))` (`suzuki4_convergence_quartic`). Also proves the
  growth bound `norm_suzuki4Exp_le` (`‖S₄(τ)‖ ≤ exp(|τ|·s4Rate)`) by reusing
  Lean-BCH's `norm_suzuki5Product_sub_one_le` rather than re-grinding the
  11-factor product; and bridges the two S₄ spellings
  (`suzuki4Step_eq_suzuki4Exp`) so the O(1/n²) bound of `Suzuki4.lean` is
  upgraded to O(1/n⁴) on the same object (`suzuki4Step_*_quartic`).

Release corollaries and specializations:

- `Suzuki4TightConvergence.lean`, `Suzuki4UnitaryTotalError.lean` —
  commutator-scaled and skew-adjoint S₄ total-error bounds.
- `StrangTotalErrorCommScaling.lean`, `Suzuki4Commute.lean` — Strang total
  error and exact Suzuki degeneration under commutation.
- `TrotterStepCount.lean`, `MatrixCorollaries.lean` — accuracy-to-step counts
  and finite complex-matrix specializations.
- `Suzuki4GapClosers.lean`, `PrefactorStrict.lean` — general-time/Gibbs
  corollaries and formal coefficient-vector comparisons.

Top-level: `LieTrotter.lean` (root import), `lakefile.lean`, `lean-toolchain`,
`AGENTS.md` (this file), `CHANGELOG.md` (lab notes), `TODO.md` (remaining work).

---

## Task Decomposition

### Track 1 — Algebraic (no analysis)

#### Task A: Telescoping (✅ Done)

| Sub-task | Statement | Status |
|----------|-----------|--------|
| A1. `telescoping_direct` | $\sum_{k<n} X^k(X-Y)Y^{n-1-k} = X^n - Y^n$ | ✅ Proved |
| A2. `norm_pow_sub_pow_le'` | $\|X^n - Y^n\| \le n \|X-Y\| M^{n-1}$ | ✅ Proved |

**File:** `LieTrotter/Telescoping.lean`
**Key insight:** Prove the sum *equals* the difference (not the other way) because `Finset.sum_range_succ` peels off the last term. Factor out $Y$ from the inner sum to get the inductive step.

---

### Track 2 — Analysis (exponential series)

#### Task B: Exponential Remainder Bounds (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| B1. `norm_exp_le` | $\|e^a\| \le e^{\|a\|}$ | Easy | ✅ Proved |
| B2. `norm_exp_sub_one_le` | $\|e^a - 1\| \le e^{\|a\|} - 1$ | Easy | ✅ Proved |
| B3. `exp_sub_one_sub_bound_real` | $e^x - 1 - x \le \frac{x^2}{2} e^x$ for $x \ge 0$ | Medium | ✅ Proved |
| B4. `norm_exp_sub_one_sub_le` | $\|e^a - 1 - a\| \le \frac{\|a\|^2}{2} e^{\|a\|}$ | Medium | ✅ Proved |

**File:** `LieTrotter/ExpBounds.lean`

**Proof strategies:**

**Proof techniques used:**

- **B1–B2:** Write `exp` as `∑' n, (n!)⁻¹ • a^n` via `exp_tsum_form`, apply `norm_tsum_le_tsum_norm`, bound each term by `‖a‖^n/n!` via `norm_exp_term_le`, recognize RHS as `Real.exp ‖a‖`. B2 shifts the index by 1 using `tsum_eq_zero_add`.

- **B3:** Write `exp(x)-1-x = ∑' n, x^{n+2}/(n+2)!`, prove termwise `x^{n+2}/(n+2)! ≤ x²/2 · x^n/n!` using auxiliary `two_mul_factorial_le : 2·n! ≤ (n+2)!`, sum via `tsum_le_tsum`, factor out `x²/2` via `tsum_mul_left`.

- **B4:** Same shifted-series technique as B2 (shift by 2), bound norms by `‖a‖^{n+2}/(n+2)!`, recognize sum as `exp(‖a‖)-1-‖a‖`, then apply B3.


---

#### Task C: Quadratic Step Error (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| C1. `norm_exp_mul_exp_sub_exp_add'` | $\|e^a e^b - e^{a+b}\| \le 2\|a\|\|b\| e^{\|a\|+\|b\|}$ | Hard | ✅ Proved |
| C2. `lie_trotter_step_error` | $\|e^{A/n} e^{B/n} - e^{(A+B)/n}\| \le \frac{2\|A\|\|B\|}{n^2} e^{(\|A\|+\|B\|)/n}$ | Medium | ✅ Proved |

**File:** `LieTrotter/StepError.lean`

**C1 proof approach (algebraic factorization):**

The proof uses a cleaner strategy than the second-order expansion:
1. **Algebraic identity** (by `ring`): $e^a e^b - e^{a+b} = (e^a-1)(e^b-1) - (e^{a+b} - e^a - e^b + 1)$
2. **Triangle inequality**: Both parts bounded by $(e^{\|a\|}-1)(e^{\|b\|}-1)$, giving $\le 2(e^{\|a\|}-1)(e^{\|b\|}-1)$
3. **Final bound** via `exp_sub_one_le_mul_exp`: $(e^s-1)(e^t-1) \le st \cdot e^{s+t}$

**C1 cross-term bound** (`norm_exp_cross_term_le`): proved via inductive lemma
`norm_pow_add_sub_pow_sub_pow`: $\|(a+b)^m - a^m - b^m\| \le (\|a\|+\|b\|)^m - \|a\|^m - \|b\|^m$ for $m \ge 1$,
using the identity $(a+b)^{m+1} - a^{m+1} - b^{m+1} = (a+b)((a+b)^m - a^m - b^m) + ab^m + ba^m$.
Then tsum assembly sums to $(e^{\|a\|}-1)(e^{\|b\|}-1)$ via `Real.exp_add` and `ring`.

**C2** proved by applying C1 with $a = A/n$, $b = B/n$, using `norm_smul`, `norm_inv`, `RCLike.norm_natCast`, and `field_simp; ring`.


---

### Track 3 — Connecting Lemmas

#### Task D: `exp(a/n)^n = exp(a)` (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| D1. `exp_div_pow` | $(e^{a/n})^n = e^a$ for $n > 0$ | Medium | ✅ Proved |
| D2. `norm_exp_smul_le` | $\|e^{c \cdot a}\| \le e^{\|c\| \|a\|}$ | Easy | ✅ Proved |

**File:** `LieTrotter/ExpDivPow.lean`

**D1 proof (4 lines):** `rw [← exp_nsmul]; congr 1; rw [nsmul_eq_smul_cast 𝕂 n, smul_smul, mul_inv_cancel₀, one_smul]; exact Nat.cast_ne_zero.mpr (by omega)`

**D2 proof:** `norm_exp_le` (B1) composed with `norm_smul_le` via `gcongr`.


---

### Track 4 — Assembly

#### Task E: Main Theorem (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| E1. `lie_trotter_error_rate` | $\exists C > 0,\; \|P_n^n - e^{A+B}\| \le C/n$ | Medium | ✅ Proved |
| E2. `lie_trotter` | $P_n^n \to e^{A+B}$ | Easy | ✅ Proved |

**File:** `LieTrotter/Assembly.lean`

**E1 proof outline:**
1. Set $P_n = e^{A/n} e^{B/n}$, $Q_n = e^{(A+B)/n}$.
2. $Q_n^n = e^{A+B}$ by Task D.
3. $\|P_n^n - Q_n^n\| \le n \|P_n - Q_n\| M^{n-1}$ by Task A.
4. $\|P_n - Q_n\| \le 2\|A\|\|B\|/n^2 \cdot e^{(\|A\|+\|B\|)/n}$ by Task C.
5. $M \le e^{(\|A\|+\|B\|)/n}$ by Tasks B+D.
6. $e^{(s/n)n} = e^s$ exactly, so everything collapses to $2\|A\|\|B\| e^s / n$.

**E2** is a standard $\varepsilon$-$N$ argument using `Metric.tendsto_atTop` and `exists_nat_gt`.


---

### Track 5 — Extensions (optional)

#### Task F: Corollaries

| Sub-task | Statement | Priority | Status |
|----------|-----------|----------|--------|
| F1. `matrix_lie_trotter` | Specialization to `Matrix (Fin d) (Fin d) ℂ` | Low | ✅ |
| F2. `symmetric_lie_trotter` | Strang splitting: $e^{A+B} = \lim (e^{A/2n} e^{B/n} e^{A/2n})^n$ with O(1/n²) rate | Low | ✅ |

Both optional corollaries are now complete.

---

### Track 6 — Commutator Scaling (Duhamel / variation-of-parameters)

#### Task H: Commutator-Scaling Trotter Error (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| H1. `exp_conj_sub_eq_integral` | $e^{\tau B} A e^{-\tau B} - A = \int_0^\tau e^{sB}[B,A]e^{-sB}ds$ | Medium | ✅ Proved |
| H2. `lie_trotter_integral_error` | $e^{tB}e^{tA} - e^{t(A+B)} = \int_0^t e^{(t-\tau)(A+B)}[e^{\tau B},A]e^{\tau A}d\tau$ | Hard | ✅ Proved |
| H3. `norm_exp_conj_sub_le` | $\|e^{\tau B}Ae^{-\tau B} - A\| \le \|[B,A]\|\|\tau\|e^{2\|\tau\|\|B\|}$ | Medium | ✅ Proved |
| H4. `norm_comm_exp_le` | $\|[e^{\tau B}, A]\| \le \|[B,A]\|\|\tau\|e^{3\|\tau\|\|B\|}$ | Easy | ✅ Proved |
| H5. `norm_lie_trotter_comm_scaling` | For $t\ge0$, $\|e^{tB}e^{tA} - e^{t(A+B)}\| \le \frac12\|[B,A]\|t^2 e^{t(\|A\|+3\|B\|)}$ | Medium | ✅ Proved |

**File:** `LieTrotter/CommutatorScaling.lean`

**Proof strategy (Duhamel via FTC-2, no ODE uniqueness):**
1. Define $w(\tau) = e^{-\tau(A+B)} e^{\tau B} e^{\tau A}$
2. Compute $w'(\tau) = e^{-\tau(A+B)} [e^{\tau B}, A] e^{\tau A}$ via product rule + `Commute.exp_right`
3. FTC-2: $w(t) - w(0) = \int_0^t w'(\tau) d\tau$ → integral error representation (H2)
4. Extract commutator $[B,A]$ from $[e^{\tau B}, A]$ via second FTC on $s \mapsto e^{sB} A e^{-sB}$ (H1)
5. Bound norms using H3, H4, and `norm_integral_le_of_norm_le_const` (H5)

**Key Mathlib API used (new for this track):**
- `hasDerivAt_exp_smul_const'` — derivative $d/dt[e^{tA}] = A \cdot e^{tA}$
- `HasDerivAt.mul` — product rule in `NormedAlgebra`
- `integral_eq_sub_of_hasDerivAt` — FTC-2 for interval integrals
- `ContinuousLinearMap.intervalIntegral_comp_comm` — pull left-multiplication out of integrals
- `norm_integral_le_of_norm_le_const` — constant norm bound for interval integrals
- `Commute.exp_right` — $a$ commutes with $e^b$ when $a$ commutes with $b$

**Design note:** Works over `NormedAlgebra ℝ 𝔸` directly (not general `𝕂`), avoiding the `SMul ℝ 𝔸` instance synthesis issues. For `𝕂 = ℂ` applications, use `NormedAlgebra.restrictScalars ℝ 𝕂 𝔸`.

**Bound:** Tight $t^2/2$ coefficient achieved via `norm_integral_le_of_norm_le` (non-constant bound) + FTC on $x^2/2$.


---

#### Task I: Second-Order Strang Commutator Scaling (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| I1. `exp_conj_sub_comm_eq_double_integral` | Double FTC extracting $[B,[B,A]]$ | Medium | ✅ Proved |
| I2. `norm_exp_conj_sub_comm_le` | $\|e^{\tau B}Ae^{-\tau B} - A - \tau[B,A]\| \le \frac{\|[B,[B,A]]\|}{2}\tau^2 e^{2\tau\|B\|}$ | Medium | ✅ Proved |
| I3. `hasDerivAt_conj_strang` | 4-factor product rule for $w(\tau)=e^{-\tau H}S_2(\tau)$ | Hard | ✅ Proved |
| I4. `norm_strang_comm_scaling` | $\|S_2(t)-e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$ | Hard | ✅ Proved |
| I5. `norm_palindromicProd_sub_exp_sum_comm` | Multi-operator Strang commutator scaling | Medium | ✅ Proved |

**Files:** `LieTrotter/StrangCommutatorScaling.lean`, `LieTrotter/MultiStrangCommutatorScaling.lean`

**Proof strategy (Strang, anti-Hermitian):**
1. FTC-2 on $w(\tau) = e^{-\tau H} S_2(\tau)$ using 4-factor product rule `hasDerivAt_conj_strang`
2. Anti-Hermitian isometry: $\|e^{sX}\| = 1$ in C*-algebras (via `norm_exp_smul_of_skewAdjoint`)
3. First-order cancellation: $[A/2,B] + [B,A/2] = 0$ (exact in the integrand, before taking norms)
4. "Subtract-constant-at-$\tau$" trick: $R_1 + \tau\cdot(\text{conj diff}) = \int_0^\tau (H(s)-H(\tau))ds$ bounded by $C_A\tau^2/2$ using $\|H(s)-H(\tau)\| \le (\tau-s) C_A$ — avoids Fubini/integration-by-parts
5. Coefficient conversion: $A' = A/2$ gives $C_A = \|[A,[A,B]]\|/4$, $C_B = \|[B,[B,A]]\|/2$

**Key Lean technique for I3:** Factor the algebraic identity as $-(E \cdot (n_H + A' + A' + B) \cdot e_A \cdot e_B \cdot e_A) = 0$ using `noncomm_ring` for the free-ring factoring, then $n_H + A' + A' + B = 0$ (since $n_H = -(A+B)$ and $A'+A'=A$) via `abel`.

**Multi-operator (I5):** Induction on operator list, same pattern as `MultiCommutatorScaling.lean`. The `listDoubleCommNorm` sums $\|[S_i,[S_i,a_i]]\|/12 + \|[a_i,[a_i,S_i]]\|/24$ with suffix sums.

---

#### Task J: Higher-Order Commutator Extraction (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| J1. `exp_conj_sub_comm2_eq_triple_integral` | Triple FTC extracting $[B,[B,[B,A]]]$ | Medium | ✅ Proved |
| J2. `norm_exp_conj_sub_comm2_le` | $\|e^{\tau B}Ae^{-\tau B} - A - \tau[B,A] - \frac{\tau^2}{2}[B,[B,A]]\| \le \frac{\|[B,[B,[B,A]]]\|}{6}\tau^3 e^{2\tau\|B\|}$ | Medium | ✅ Proved |
| J3. `norm_exp_conj_sub_comm2_le_of_skewAdjoint` | Anti-Hermitian version: $\le \frac{\|[B,[B,[B,A]]]\|}{6}\tau^3$ (no exp factor) | Easy | ✅ Proved |

**File:** `LieTrotter/HigherCommutator.lean`

**Proof strategy:** Apply `exp_conj_sub_eq_integral` three times iteratively (same pattern as double FTC but one level deeper). The anti-Hermitian version uses isometry to eliminate the exponential factor. Building block for the tighter Strang bound and future S₄ commutator-scaling work.

---

#### Task K: Tighter Strang Commutator-Scaling (✅ Done) — **NEW RESULT**

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| K1. `norm_partA_sub_leading` | PartA remainder ≤ triple commutator · τ³/3 | Medium | ✅ Proved |
| K2. `norm_partB_sub_leading` | PartB remainder ≤ triple commutators · τ³ | Medium | ✅ Proved |
| K3. `norm_strang_comm_scaling_tight` | $\|S_2(t)-e^{tH}\| \le \frac{\|D\|}{6}t^3 + \frac{T}{4}t^4$ | Hard | ✅ Proved |
| K4. `norm_D_le_sum_of_norms` | $\|D\| \le \frac12\|[B,[B,A]]\| + \frac14\|[A,[A,B]]\|$ — the **domination** of the tight leading coeff over the sum-of-norms one, machine-checked (2026-07-15) | Easy | ✅ Proved |

**File:** `LieTrotter/StrangCommutatorScalingTight.lean`

**K4 (2026-07-15, closes the "argued not formalized" gap).** The tight bound
K3 was `‖D‖/6·t³+T/4·t⁴`; that its leading coeff `‖D‖/6` never *exceeds* the
standard `‖[B,[B,A]]‖/12+‖[A,[A,B]]‖/24` was previously only argued in prose.
`norm_D_le_sum_of_norms` now proves `‖D‖ ≤ ½‖[B,[B,A]]‖+¼‖[A,[A,B]]‖` (÷6 gives
the coeff comparison) — axiom-free, **no C*-structure** (only `NormedRing` +
`NormedAlgebra ℝ`, `omit`-ing the auto-included star/complete instances). Proof:
`D = ½[B,[B,A]] − ¼[A,[A,B]]` since `A' = A/2` (scalars pulled through products
via `Algebra.{mul_smul_comm,smul_mul_assoc}` + `simp`), then `norm_sub_le` +
`norm_smul`. The manuscript now says the domination is machine-checked outright
(`apd_tighter_strang.tex`, `norm_D_le_sum_of_norms` cited at line 576).
Committed numerical experiments test nonzero gain on concrete finite-chain
models (`scripts/sweep_strang_alignment.py`, independently checked by
`scripts/verify_strang_alignment_independent.py`, with data in
`claude/strang_alignment_sweep.csv`); these experiments are evidence, not part
of the formal theorem.

**The new result:** Replaces the standard sum-of-norms bound with a tighter norm-of-difference bound:

Standard (Childs et al. 2021):
$$\|S_2(t) - e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$$

Tighter (this work):
$$\|S_2(t) - e^{tH}\| \le \frac{\|D\|}{6}t^3 + \frac{T}{4}t^4$$

where $D = [B,[B,A']] - [A',[A',B]]$ is the **effective double commutator** ($A' = A/2$).

The leading coefficient $\|D\|/6$ is always $\le$ the standard bound by the
triangle inequality, and is strictly tighter when the two double commutators
partially cancel. Concrete finite-chain examples are recorded in the committed
numerical data, but no universal lattice-model percentage is claimed.

**Proof strategy:** Extract the leading order $\tau^2/2 \cdot D$ from the Strang residual $\mathcal{T}_2(\tau)$ before taking norms, bounding the remainder using the triple FTC (Task J).

---

### Track 7 — S₄ Fourth-Order Bound (certified prefactor improvements, ✅ axiom-free through the τ⁷ L4 chain)

#### Task L: Fourth-Order Suzuki Commutator-Scaling

**Goal:** Prove the genuine O(t⁵) S₄ bound and compare its certified prefactors with
Childs et al.'s rigorous arXiv Proposition J.1 bound, whose eight coefficients
range from 0.0046 to 0.0284 and are not claimed to be optimal or tight.

**Status:** All L1–L4 release headlines are axiom-free at Lean-BCH pin
`05e8c52` (former septic stepping stones discharged 2026-07-28; integrated
status re-audited 2026-08-02).

#### Modular architecture (release path complete; optional native alternative open)

| Module | Statement | Status |
|--------|-----------|--------|
| L1. `hasDerivAt_w4` | HasDerivAt for `w₄(τ) = exp(-τH)·S₄(τ)` (12-factor product) | ✅ Proved |
| L2. `norm_suzuki4_diff_eq_norm_relative` | `‖S₄(t)-exp(tH)‖ = ‖w₄(t)-1‖` (anti-Hermitian) | ✅ Proved |
| L3. `norm_w4_sub_one_le_t5_via_residual` | FTC-2 reduction: residual bound → integrated bound | ✅ Proved |
| L3'. `norm_suzuki4_order5_via_module3` | S₄ O(t⁵), conditional on residual bound | ✅ Proved (conditional) |
| L4a. `continuous_w4Deriv` | Continuity of extracted derivative (via analytic / ContDiff) | ✅ Proved |
| L4b-A1. `hasDerivAt_w4Explicit` | HasDerivAt with explicit 12-term derivative | ✅ Proved |
| L4b-A2. `w4Deriv_eq_w4DerivExplicit` | Extracted derivative equals explicit form (uniqueness) | ✅ Proved |
| L4b-A3. `w4DerivExplicit_eq_exp_mul_residual` | Factorization `w4DerivExplicit = exp(-τH)·w4Residual` | ✅ Proved |
| L4b-A3'. `w4Residual_eq_s4Deriv_sub_H_s4` | Cleaner form `w4Residual = s4' - H·s4` | ✅ Proved |
| L4b-B1. `w4Deriv_at_zero` | Order-0 cancellation `w4Deriv 0 = 0` (uses `suzuki4_free_term`) | ✅ Proved |
| L4b-P1. `w4Residual_eq_comm_sum` | Commutator form `w4Residual = Σⱼ [Lⱼ,dⱼ]·Rⱼ` | ✅ Proved |
| L4b-P2. `s4_sumAB_eq_sumBA` + `s4_pairwise_commutator_sum_zero` | Order-1 palindromic identity | ✅ Proved |
| L4b-P3. `suzuki4_phase3_{aba,a2b,bab}` | Six polynomial identities ∝ Suzuki cubic | ✅ Proved |
| L4b-smooth. `contDiff_w4Residual` | `w4Residual` is `ContDiff ℝ n` (for Taylor bounds) | ✅ Proved |
| L4b-Taylor. `exists_norm_w4Residual_t4_bound_of_zero_taylor` | Conditional τ⁴ bound from 4 iteratedDerivWithin vanishings | ✅ Proved |
| L4b-Taylor-0. `iteratedDerivWithin_w4Residual_order0` | Order-0 of w4Residual trivially vanishes | ✅ Proved |
| L4b-Taylor'. `exists_norm_w4Func_sub_one_t5_bound_of_zero_taylor` | Alternative Taylor-reduction for w4Func | ✅ Proved |
| L4b-Taylor-1. `iteratedDerivWithin_w4Func_order1` | Order-1 of w4Func PROVED via `w4Deriv_at_zero` | ✅ Proved |
| L4b-decomp. `w4DerivExplicit_decomp` | `w4DerivExplicit = -H·w4Func + exp(-τH)·s4DerivExplicit` | ✅ Proved |
| L4b-Leibniz. `iteratedDeriv_exp_smul_mul_at_zero` | Base case: iteratedDeriv k exp((c·τ)•X) 0 = (c•X)^k | ✅ Proved |
| L4b-br-2. `iteratedDeriv_w4Func_order2_eq` / `_zero_iff` | Order-2 bridge: w4Func''(0) = s4''(0) - H² | ✅ Proved |
| L4b-br-3. `iteratedDeriv_w4Func_order3_eq` / `_zero_iff_of_order2` | Order-3 bridge (conditional on order-2) | ✅ Proved |
| L4b-br-4. `iteratedDeriv_w4Func_order4_eq` / `_zero_iff_of_order23` | Order-4 bridge (conditional on orders 2, 3) | ✅ Proved |
| L4b-CAPSTONE. `norm_suzuki4_order5_of_s4Func_iteratedDerivs` | S₄ O(τ⁵) **uniformly on [0,t]** given 3 s4Func identities | ✅ Proved (statement **repaired** 2026-07-14: `C` was bound after `t`, making it a tautology — see Lesson 16) |
| L4b-multinomial. `iteratedDeriv_prodExpList_order{0,1,2}` | Multinomial formulas for iteratedDeriv of exp products | ✅ Proved |
| L4b-h2. `iteratedDeriv_s4Func_order2_eq_sq` | **h2: iteratedDeriv 2 s4Func 0 = (A+B)²** | ✅ Proved UNCONDITIONAL |
| L4b-h3-factored. `sumTripleCorr_s4DList_eq_factored` | `sumTripleCorr = (4p³+(1-4p)³) • <op combo>` (operator algebra identity) | ✅ Proved |
| L4b-h3. `iteratedDeriv_s4Func_order3_eq_cb` | **h3: iteratedDeriv 3 s4Func 0 = (A+B)³** (given `IsSuzukiCubic p`) | ✅ Proved |
| L4b-w4-order3. `iteratedDeriv_w4Func_order3_eq_zero` | `iteratedDeriv 3 (w4Func A B p) 0 = 0` (given `IsSuzukiCubic p`) | ✅ Proved |
| L4b-h4-infra. `iteratedDeriv_prodExpList_order4` + `sumQuadCorr` def | h4 infrastructure (order-4 multinomial formula, quartic smul helpers) | ✅ Proved |
| L4b-h4-bridge. `iteratedDeriv_s4Func_order4_eq_q_of_bridge` | h4 conditional on `sumQuadCorr_s4DList = 0` | ✅ Proved |
| L4b-h4-bch. `sumQuadCorr_s4DList_eq_zero_of_bch`, `iteratedDeriv_s4Func_order4_eq_q_of_bch` | h4 via BCH-bridge + IsSuzukiCubic | ✅ Proved |
| L4b-capstone-bch. `norm_suzuki4_order5_via_bch` | S₄ O(τ⁵) uniformly on [0,t], taking only IsSuzukiCubic + BCH identity | ✅ Proved (statement repaired 2026-07-14; note `hBCH` is still an *undischarged* hypothesis) |
| L4b-h4-BCH (alt). | Trotter-native BCH identity `sumQuadCorr = 2·(H·sumTripleCorr+sumTripleCorr·H)` for palindromic | 🔴 Open (module timeout; superseded by SLICE 1+2+3) |
| SLICE 1. `exists_norm_s4Func_sub_exp_le_t5` | Single-step BCH O(|τ|⁵) bound | ✅ Proved (via Lean-BCH M6 + opaque-RHS corollary) |
| SLICE 2. `iteratedDeriv_eq_of_norm_le_pow` | Generic Taylor-match-from-norm | ✅ Proved |
| SLICE 3. `bch_iteratedDeriv_s4Func_order4` | h4 as a theorem (prev. axiom) | ✅ Proved |
| L5. `norm_suzuki4_childs_via_residual` | Conditional Childs-form bound (8 explicit 4-fold commutators) | ✅ Proved |
| L5'. `norm_suzuki4_childs_form_via_level3` | Order-only Childs-labelled corollary of Level 3 (`norm_suzuki4_childs_explicit` carries the coefficients) | ✅ Proved (replaces a retired project-local bridge axiom) |
| L6. `norm_suzuki4Exp_le` | Growth bound `‖S₄(τ)‖ ≤ exp(\|τ\|·s4Rate A B p)` (via Lean-BCH 11-factor peel) | ✅ Proved |
| L7. `suzuki4_total_error_quartic` | **Total error `‖S₄(t/n)ⁿ − exp(t(A+B))‖ ≤ C/n⁴`** | ✅ Proved (axiom-free) |
| L8. `suzuki4_convergence_quartic` | **`S₄(t/n)ⁿ → exp(t(A+B))`** | ✅ Proved (axiom-free) |
| L9. `suzuki4Step_eq_suzuki4Exp` | Bridge `suzuki4Step ℝ A B p n = suzuki4Exp A B p (1/n)` (via `suzuki4Exp_eq_strangProduct`) | ✅ Proved |
| L10. `suzuki4Step_{total_error,convergence}_quartic` | **O(1/n⁴) for `suzuki4Step`** — upgrades `suzuki4_error_rate_sq` (O(1/n²)) on the *same* object | ✅ Proved (axiom-free) |

**Files:**
- `LieTrotter/Suzuki4HasDerivAt.lean` — Module 1
- `LieTrotter/Suzuki4Module2.lean` — Module 2
- `LieTrotter/Suzuki4Module3.lean` — Module 3
- `LieTrotter/Suzuki4Module4.lean` — Module 4a (continuity)
- `LieTrotter/Suzuki4DerivExplicit.lean` — Module 4b-A1/A2/A3 + Phase 1-3 polynomial identities + smoothness + bridge
- `LieTrotter/Suzuki4Phase5.lean` — Taylor-reduction + Leibniz bridges for orders 1-4 + CAPSTONE theorem (conditional closure of S₄ O(t⁵) from 3 s4Func iteratedDeriv identities)
- `LieTrotter/Suzuki4MultinomialExpand.lean` — prodExpList + multinomial formulas + **h2 UNCONDITIONALLY + h3 under IsSuzukiCubic PROVED**
- `LieTrotter/Suzuki4ChildsForm.lean` — Childs et al. arXiv Proposition J.1 form + conditional reduction
- `LieTrotter/Suzuki4OrderFive.lean` — `norm_suzuki4_fifth_order` (closed with an explicit residual hypothesis)

**Current architecture (S₄ O(t⁵) and the τ⁷ L4 chain, axiom-free):**

```
Module 1 (HasDerivAt for 12-factor w₄) ✅
Module 2 (FTC-2 bridge: ‖S₄-exp‖ = ‖w₄-1‖) ✅
Module 3 (FTC-2 reduction: residual bound → C·t⁵/5) ✅
Module 4a (continuous_w4Deriv) ✅
Module 4b-A1/A2/A3 (explicit derivative + factorization + order-0) ✅
Phase 5 Taylor-reduction framework + Leibniz bridges (orders 1-4) ✅
CAPSTONE via h2 + h3 + h4 ✅
       │
       ├── h2 unconditional ✅
       ├── h3 under IsSuzukiCubic p ✅
       └── h4 via SLICE 1+2+3 chain ✅
                SLICE 1: BCH single-step O(|τ|⁵) — sorry-free (2026-04-24)
                SLICE 2: Taylor-match-from-norm — sorry-free
                SLICE 3: wire + iteratedDeriv_exp_smul_mul_at_zero — sorry-free
                Lean-BCH base: `suzuki5_bch_M4b_RHS_le_t5_of_IsSuzukiCubic`
                (closed upstream at rev `c71d8f2`, 2026-04-24; quintic
                discharges at rev `d455ff0`, 2026-05-19; septic discharges at
                rev `05e8c52`, 2026-07-28 — see the top-of-file bridge table).
```

`#print axioms` on `norm_suzuki4_childs_form_via_level3`,
`norm_suzuki4_level3_bch`, `norm_suzuki4_level2_bch`,
`bch_uniform_integrated`, `norm_suzuki4_level4_uniform`,
`bch_iteratedDeriv_s4Func_order4`, `exists_norm_s4Func_sub_exp_le_t5`,
and `lie_trotter` returns only `[propext, Classical.choice, Quot.sound]`.

**Tighter Trotter-native bounds (existing, fully proved):**
- `norm_suzuki4_comm_scaling`: O(t³) via 5-S₂ telescoping (norm-of-sum).
- `norm_suzuki4_tight_proved`: O(t³)+O(t⁴) with norm-of-difference D and
  triple correction T.

The genuine O(t⁵) requires the SIGNED cubic cancellation `4p³+q³=0` applied
at the integrand level (before taking norms). Triangle inequality kills this
cancellation — that's why Modules 1-3's integrand-level FTC-2 reduction is
necessary.

---

---

## Dependency DAG (build order)

```
Phase 1 (parallel):    A (✅)     B1,B2 (✅)     D2 (✅)
                         │           │               │
Phase 2 (parallel):    A (✅)     B3,B4 (✅)     D1 (✅)
                                     │
Phase 3:                           C1 (✅)
                                     │
Phase 4:                           C2 (✅)
                                     │
Phase 5:                           E1 (✅)
                                     │
Phase 6:                           E2 (✅)
```

**All tasks complete.** Critical path was: B3 → B4 → C1 → C2 → E1 → E2

---

## Mathlib API Reference

### Already available (Lean 4 / Mathlib, March 2026)

| Lean Name | Math | Import |
|-----------|------|--------|
| `NormedSpace.exp` | $e^a = \sum_{k=0}^\infty a^k/k!$ | `Analysis.Normed.Algebra.Exponential` |
| `NormedSpace.exp_zero` | $e^0 = 1$ | same |
| `NormedSpace.exp_add_of_commute` | $e^{a+b} = e^a e^b$ when $[a,b]=0$ | same |
| `norm_pow_le` | $\|a^n\| \le \|a\|^n$ | `Analysis.Normed.Ring.Basic` |
| `norm_mul_le` | $\|ab\| \le \|a\| \cdot \|b\|$ | same |
| `Real.exp_add` | $e^{x+y} = e^x e^y$ | `Analysis.SpecialFunctions.ExpDeriv` |
| `Metric.tendsto_atTop` | $\varepsilon$-$N$ characterization | `Topology.MetricSpace.Basic` |
| `exists_nat_gt` | Archimedean property | `Order.Bounds.Basic` |
| `norm_tsum_le_tsum_norm` | $\|\sum a_k\| \le \sum \|a_k\|$ | `Topology.Algebra.InfiniteSum` |

### Verified and used

| Lean Name | Math | Used in |
|-----------|------|---------|
| `NormedSpace.exp_nsmul` | $e^{n \cdot x} = (e^x)^n$ | D1 |
| `NormedSpace.expSeries_summable` | summability of exp series | B1–B4 |
| `Real.hasSum_exp` | `Real.exp x` as a `HasSum` | B1–B4 |
| `Real.summable_pow_div_factorial` | $\sum x^n/n!$ is summable | B1–B4 |
| `Real.add_one_le_exp` | $1 + x \le e^x$ | C1 helper |
| `norm_tsum_le_tsum_norm` | $\|\sum a_k\| \le \sum \|a_k\|$ | B1, B2, B4 |
| `tsum_le_tsum` | termwise comparison for tsums | B1–B4 |
| `tsum_eq_zero_add` | $\sum_{n \ge 0} = f(0) + \sum_{n \ge 1}$ | B2, B3, B4 |
| `tsum_mul_left` | $\sum c \cdot f(n) = c \cdot \sum f(n)$ | B3 |
| `nsmul_eq_smul_cast` | $n \bullet x = (n : \mathbb{K}) \cdot x$ | D1 |
| `RCLike.norm_natCast` | $\|(n : \mathbb{K})\| = n$ | C2 |

| `hasDerivAt_exp_smul_const'` | $d/dt[e^{tA}] = A \cdot e^{tA}$ | H1, H2 |
| `HasDerivAt.mul` | product rule for `NormedAlgebra` | H1, H2 |
| `Commute.exp_right` | $[a,b]=0 \Rightarrow [a, e^b]=0$ | H1, H2 |
| `integral_eq_sub_of_hasDerivAt` | FTC-2 for interval integrals | H1, H2 |
| `ContinuousLinearMap.intervalIntegral_comp_comm` | $L(\int f) = \int L \circ f$ | H2 |
| `norm_integral_le_of_norm_le_const` | $\|\int f\| \le C\|b-a\|$ | H3, H5 |
| `Real.exp_le_exp_of_le` | $a \le b \Rightarrow e^a \le e^b$ | H3, H4, H5 |

### Not in Mathlib (proved ourselves)

- `norm_exp_le` — $\|e^a\| \le e^{\|a\|}$ for general Banach algebras (only `Complex.norm_exp_le_exp_norm` exists for ℂ)
- `exp_sub_one_sub_bound_real` — $e^x - 1 - x \le x^2/2 \cdot e^x$
- `norm_exp_sub_one_le` — $\|e^a - 1\| \le e^{\|a\|} - 1$
- `exp_conj_sub_eq_integral` — $e^{\tau B}Ae^{-\tau B} - A = \int_0^\tau e^{sB}[B,A]e^{-sB}ds$ (conjugation FTC)
- `lie_trotter_integral_error` — integral representation of Trotter error via Duhamel formula
- `norm_lie_trotter_comm_scaling` — commutator-scaling bound $\|e^{tB}e^{tA} - e^{t(A+B)}\| \le \frac{\|[B,A]\|}{2}t^2 e^{t(\|A\|+3\|B\|)}$
- `norm_strang_comm_scaling` — second-order Strang commutator-scaling (anti-Hermitian): $\|S_2(t)-e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$
- `norm_palindromicProd_sub_exp_sum_comm` — multi-operator Strang commutator-scaling (anti-Hermitian)
- `exp_conj_sub_comm2_eq_triple_integral` — triple FTC: $e^{\tau B}Ae^{-\tau B} - A - \tau[B,A] - \frac{\tau^2}{2}[B,[B,A]] = \iiint [B,[B,[B,A]]]$-conjugated
- `norm_exp_conj_sub_comm2_le_of_skewAdjoint` — triple commutator bound (anti-Hermitian): $\le \frac{\|[B,[B,[B,A]]]\|}{6}\tau^3$
- `norm_strang_comm_scaling_tight` — **NEW RESULT**: tighter Strang bound via norm-of-difference: $\|S_2(t)-e^{tH}\| \le \frac{\|D\|}{6}t^3 + \frac{T}{4}t^4$ where $D = [B,[B,A']] - [A',[A',B]]$
- `norm_D_le_sum_of_norms` — the domination $\|D\| \le \frac12\|[B,[B,A]]\| + \frac14\|[A,[A,B]]\|$, so the norm-of-difference leading coeff is machine-checked never to exceed the sum-of-norms one (no C*-structure; 2026-07-15)

---

## How to Build

```bash
cd Lean-Trotter
export PATH="$HOME/.elan/bin:$PATH"  # if lake not on PATH
lake update            # fetch Mathlib + dependencies
lake exe cache get     # download Mathlib oleans (~3 GB)
lake build             # type-checks all modules
```

Expected: `Build completed successfully` with only lint warnings about unused section variables.

---

## `sorry` Census

The release has 40 modules under `LieTrotter/` plus the root import
aggregator `LieTrotter.lean` (41 Lean source files total). A source scan finds
zero executable `sorry` or `admit` terms and zero project declarations of
`axiom`, `constant`, or `opaque`. The release-target `#print axioms`
audit reports only `[propext, Classical.choice, Quot.sound]`, including the
L4/τ⁷ chain at Lean-BCH pin `05e8c52`.

## Design Decisions

1. **Algebraic factorization for C1** (instead of second-order expansion): Used
   $e^a e^b - e^{a+b} = (e^a-1)(e^b-1) - (e^{a+b}-e^a-e^b+1)$
   to split into two terms each bounded by $(e^s-1)(e^t-1)$. This avoids the tedious cross-term bookkeeping of the expansion approach.

2. **Inductive cross-term bound**: Proved $\|(a+b)^m - a^m - b^m\| \le (\|a\|+\|b\|)^m - \|a\|^m - \|b\|^m$ by induction using the identity $(a+b)^{m+1} - a^{m+1} - b^{m+1} = (a+b)((a+b)^m-a^m-b^m) + ab^m + ba^m$. Works in non-commutative algebras without multinomial expansion.

3. **`include 𝕂 in` pattern**: Since `NormedSpace.exp` no longer takes a field parameter in newer Mathlib, `𝕂` doesn't appear in lemma types involving `exp`. Use `include 𝕂 in` before each lemma that needs `𝕂` in its proof body (for `exp_tsum_form`, `exp_summable`, etc.).

4. **`NormOneClass 𝔸`**: Required in newer Mathlib for `norm_pow_le` to work. Added to all section variable declarations.

5. **Error constant**: `C = 2‖A‖‖B‖ exp(‖A‖+‖B‖) + 1` — the `+1` ensures `C > 0` even when `A = 0` or `B = 0`. The bound `2‖A‖‖B‖ exp(‖A‖+‖B‖) / n` is tight (matches the calc chain exactly); only the `+1/n` is slack.

6. **FTC-2 conjugation trick for Duhamel** (instead of ODE uniqueness/Gronwall): Define $w(\tau) = e^{-\tau H} S(\tau)$, compute $w'(\tau)$ via product rule, apply FTC-2 to get $w(t) - w(0) = \int_0^t w'$. This avoids needing ODE existence/uniqueness theory entirely. The Gronwall approach would have required ~40 additional lines.

7. **`NormedAlgebra ℝ 𝔸` for CommutatorScaling** (instead of general `𝕂`): The `HasDerivAt`/`intervalIntegral` machinery requires `SMul ℝ 𝔸`, which is NOT automatically synthesized from `[RCLike 𝕂] [NormedAlgebra 𝕂 𝔸]`. Working over `ℝ` directly avoids the instance synthesis issue. Users with `𝕂 = ℂ` apply `NormedAlgebra.restrictScalars`.

8. **`ContinuousLinearMap.intervalIntegral_comp_comm` for pulling constants through integrals**: In a `NormedRing`, left multiplication by a fixed element is NOT `SMul` — it's ring multiplication. To pull `c * ∫ f` into `∫ c * f`, use `ContinuousLinearMap.mul ℝ 𝔸 c` as the continuous linear map, then `intervalIntegral_comp_comm`.

9. **`noncomm_ring` for free-ring factoring in `hasDerivAt_conj_strang`**: The 4-factor product rule derivative differs from the claimed 𝒯₂·S₂ form by `-(E·(nH+A'+A'+B)·eA·eB·eA)`. The factoring `∑(X_i·eA·eB·eA) = (∑X_i)·eA·eB·eA` is a free noncommutative ring identity that `noncomm_ring` handles. No commutativity rewrites needed for the final step — only `nH + A' + A' + B = 0` via `abel`.

10. **"Subtract-constant-at-τ" trick for integration-by-parts**: To bound `∫₀^τ F(s)ds - τ·F(τ)` (which arises from combining the double-integral remainder with the first-order cancellation), rewrite as `∫₀^τ (F(s)-F(τ))ds` and bound `‖F(s)-F(τ)‖ ≤ (τ-s)·C` via `norm_integral_le_of_norm_le_const` on `F(s)-F(τ) = -∫_s^τ h`. This avoids Fubini entirely.

11. **Anti-Hermitian typeclasses for Strang**: `[StarRing 𝔸] [ContinuousStar 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]` for `norm_exp_smul_of_skewAdjoint` ($\|e^{ta}\|=1$ when $a^*=-a$). The `star_trivial` lemma gives $(\text{star}\, r) = r$ for $r \in \mathbb{R}$, needed in `StarModule.star_smul`.

12. **Coefficient conversion via `Algebra.smul_mul_assoc` / `Algebra.mul_smul_comm`**: To show $[A/2,[A/2,B]] = \frac{1}{4}[A,[A,B]]$, use `Algebra.smul_mul_assoc : r•a*b = r•(a*b)` and `Algebra.mul_smul_comm : a*(r•b) = r•(a*b)` to factor $(1/2)$ scalars through products, then `smul_smul` and `norm_smul`.

13. **Norm-of-difference vs sum-of-norms for tighter bounds**: The standard Strang bound uses $\|\text{PartA}\| + \|\text{PartB}\|$ (triangle inequality). By extracting the common $\tau^2/2$ prefactor as the *effective double commutator* $D = [B,[B,A']] - [A',[A',B]]$ and bounding $\|D\|$ directly, we get a tighter leading coefficient. The remainder is bounded using the triple FTC (iterated one more level). Trade-off: introduces an $O(t^{p+1})$ correction term, but the leading coefficient is provably $\le$ the standard bound and strictly tighter with partial cancellation. This principle extends to any order.

14. **`module` tactic for smul algebra in non-commutative rings**: When `abel` fails on goals involving `smul_sub` with negated scalar terms (e.g., `(-τ)` vs `(-1 * τ)`), the `module` tactic handles the scalar-module structure correctly. Used in `StrangCommutatorScalingTight.lean` for the algebraic decomposition proofs.

15. **Auto-included instance binders hide real generality; trust the linter, and work leaf-first.** L1–L3 carried five C*-algebra typeclasses for months purely because they sat inside a `section` whose `variable` line declared them — Lean auto-includes any instance binder mentioning an included variable, so they landed in every signature unused. Two traps when cleaning this up: (a) a *caller* can look like it uses an instance when it only passes it to a callee that doesn't need it either (L2 was not flagged until its bridges were freed) — so `omit` from the leaves upward and re-run the linter after each round; (b) nested sections can re-declare the same `variable` line, silently doubling every instance argument (`AntiHermitianLevel3` inside `AntiHermitian`). `#check @thm` is the ground truth for what a theorem actually assumes; the doc comment is not.

---

16. **Quantifier order is the theorem. `∃ C` bound *after* `t` is a tautology.**
    Six S₄ "O(t⁵)" results concluded `{t} (ht : 0 < t) : ∃ C ≥ 0, ‖S₄(t) −
    exp(tH)‖ ≤ C·t⁵`. With `t` bound first, `C` may depend on `t` — take
    `C := ‖error(t)‖/t⁵`. The statements were provable for an *arbitrary* algebra
    element with no hypotheses at all, so the `IsSuzukiCubic`, anti-Hermitian and
    BCH hypotheses were inert, and `#print axioms` returning three axioms said
    nothing. The uniformity was available upstream all along
    (`exists_norm_w4Func_sub_one_t5_bound_of_zero_taylor` yields one `C` valid on
    all of `[0,t]`) and was thrown away by instantiating at the endpoint. Fixed
    2026-07-14 by concluding `∃ C ≥ 0, ∀ τ ∈ Icc 0 t, … ≤ C·τ⁵`. **Whenever a
    bound is stated existentially, check that the constant is bound before every
    variable it must be uniform in** — and sanity-check by trying to prove the
    statement with the hypotheses deleted.

17. **A docstring describes the proof; only the statement is the theorem.**
    `norm_suzuki4_level3_bch` was documented (and cited in the manuscript) as
    `‖S₄(t) − e^{tH}‖ ≤ t⁵·Σγᵢ‖Cᵢ‖`, but its *type* was `∃ C ≥ 0, … ≤ C·τ⁵` —
    the CAS-certified γᵢ appeared nowhere in it, only as a witness inside the
    proof. So L1, L2 and L3 were three names for one proposition (L3 is L2 at
    `p = suzukiP`, one line), and the entire "tightness hierarchy" existed only
    in the proofs. Two avoidable steps did the damage: merging `τ⁵·Sbs + K·τ⁶`
    into `(Sbs+K)·τ⁵`, and multiplying through by the exp-Lipschitz factor. Both
    are fixable — `exp u ≤ 1 + u·exp u` makes that factor `1 + O(τ)`, so its
    excess drops into the τ⁶ tail and the leading coefficient survives
    (`norm_suzuki4_level3_explicit`). **If a numeric constant is the point of the
    result, put it in the statement; an `∃ C` records only the order.** Corollary
    for side conditions: a hypothesis constraining an existentially-bound
    constant (`C · X ≤ Y` under `∃ C`) is unfalsifiable — the prover picks `C`
    huge and the implication is vacuous. That is exactly how
    `norm_suzuki4_level4_le_childs_when_small` was provable with zero content.

18. **Audit the manuscript against `#check @thm`, not against the docstrings.**
    Cross-checking `lean4trotter/*.tex` against the Lean statements (2026-07-14)
    turned up drift in exactly one direction: the paper printed the bound we
    *meant* to prove while Lean held the weaker one we *did* prove. The audit
    also caught errors that had nothing to do with Lean and would have shipped:
    E₃ off by 2× against Lean-BCH's `symmetric_bch_cubic_poly` (and against the
    paper's own Strang coefficients); a claimed symmetric-lattice gain example whose stated
    hypothesis `c = −1/2` actually gives ratio 1 (no gain — `r(c) = |2−c|/(2+|c|)`
    is 1 for *every* `c ≤ 0`); γ₂/γ₆ table entries *truncated* rather than ceiled,
    so as printed they fell below `|βᵢ|` and were not upper bounds at all; the
    Childs α-range minimum initially misquoted instead of the correct
    α₃ = 0.0046; "1/6 from the cubic
    integral and 1/2 from the double FTC", which multiplies out to 1/24 and 1/48,
    not 1/12 and 1/24; and code excerpts ASCII-ified into ill-typed Lean (`*`
    where the source has `•`, the algebra `𝔸` and the element `A` both printed
    `A`). **Every displayed bound, coefficient, hypothesis list and code block
    needs a named Lean theorem behind it, checked with `#check @`.** Where the
    paper argues something Lean does not prove (e.g. the Strang norm-of-difference
    dominating the sum-of-norms), say so in place rather than letting the
    surrounding "machine-checked" framing absorb it.

19. **LaTeX: `listings` `literate` only fires inside listings, and only for
    chars you declared.** The manuscript's leancode blocks used `δ` and `τ`,
    which were missing from the `literate` table — pdflatex then hit their raw
    UTF-8 bytes (`CF 84` for `τ`) and reported the useless *"Invalid UTF-8 byte
    84"*. And `𝕂`/`𝔸` are astral-plane (U+1D542/U+1D538): fine inside a listing
    with a `literate` entry, fatal in ordinary prose (`\texttt{include 𝕂 in}`).
    **Do NOT fix the prose case with `\DeclareUnicodeCharacter`** — that was my
    first fix and it broke Overleaf: registering an astral char with the UTF-8
    decoder collides with `listings`' byte-level `literate` machinery on the LaTeX
    **2025-06-01 kernel** (Overleaf's), dying with `Invalid UTF-8 byte sequence
    (\lst@FillFixed@\lst@EC…)` on the char's final byte; older local kernels
    (2024-11-01) tolerate it, so it does *not* reproduce locally. Right fix: keep
    ALL prose ASCII (`$\mathbb{K}$`, `$\mathfrak{A}$`), let `literate` own the
    listings. So "clean local pdfLaTeX build" ≠ "clean Overleaf build" — the
    kernel version differs; when a user reports an Overleaf error you can't
    reproduce, diff the two `LaTeX2e <…>` banner dates first. Separately: long
    unhyphenatable `\texttt{...}` Lean identifiers caused 19 overfull hboxes
    (worst 123pt); `\setlength{\emergencystretch}{3em}` cut that to 6 (worst
    14pt). And when a build dies with a cascading `Missing }` at `\end{document}`,
    look for an unclosed `\caption{` — brace-counting the caption region finds it
    in seconds. (This bit twice: `tab:levels`'s caption had a `\Codex{…}` note as
    its last content, sharing the caption's closing `}` on one line; commenting the
    note with `%` ate that brace. Notes that trail structural braces need the
    brace re-added on its own line.)

20. **Resolved caveats get hidden; open ones get a *visible* flag — and if a
    caveat is closable in ~5 lines of Lean, close it instead of hedging.** After
    the manuscript audit, the `\Codex{…}` notes split into (a) changelog for a
    fix already in the prose — comment those out (`%\Codex`), preserving the trail
    without rendering; and (b) genuinely open issues — those stay visible as
    `\Codex{OPEN ISSUE …}` so a referee/collaborator sees them. Hiding (b) as if
    it were (a) silently re-introduces the overclaim the note was guarding against;
    one such note even said "see the caveat below" where the caveat *was* the note,
    so hiding it dangled the reference. For the Strang norm-of-difference bound, the
    "‖D‖/6 never exceeds the sum-of-norms coeff" domination had been prose-only
    ("argued, not formalized") — the fix was not a hedge but a 20-line theorem
    `norm_D_le_sum_of_norms` (`D = ½[B,[B,A]] − ¼[A,[A,B]]` since `A' = A/2`;
    `norm_sub_le` + `norm_smul`), after which the prose says "machine-checked"
    outright. The formerly open alignment question now has reproducible numerical
    evidence in `scripts/sweep_strang_alignment.py`,
    `scripts/verify_strang_alignment_independent.py`, and
    `claude/strang_alignment_sweep.csv`; it remains empirical evidence rather
    than a formal theorem, and no universal lattice-model percentage is claimed.

## Lessons Learned

Patterns and anti-patterns from this formalization, useful for future Lean projects.

### Proof strategy

- **Find the clean factorization on paper first.** The C1 bound via $(e^a-1)(e^b-1) - \text{cross}$ was half the length of the direct second-order expansion. The Strang cubic bound via commutator extraction was the only approach that worked at all. Spend time on the math before touching Lean.

- **If your bound is weaker than expected, find the cancellation.** Applying C1 twice to the symmetric product gave O(1/n²) step error (= O(1/n) overall), not the expected O(1/n³). The missing ingredient was the commutator cancellation $[a,b] + (-[a,b]) = 0$. The math tells you when you're missing structure.

- **sorry-driven development.** Write all theorem statements with `sorry`, verify they compose, then fill bottom-up. The sorry census (22→9→3→0) is your project dashboard. Treat `sorry` like a type-checked TODO.

- **The `+1` trick for existential witnesses.** Every `∃ C > 0` used `C = (tight bound) + 1` to ensure positivity when the tight bound could be zero. Don't waste time case-splitting on degeneracies.

### Lean / Mathlib workflow

- **Pin your Mathlib version from day one.** Don't run `lake update` mid-project. Our unplanned 4.16→4.29 port took significant effort. When you do port, treat it as a separate task — don't mix math changes with API migration.

- **Copy the closest existing proof.** B2 copied from B1, B4 from B2, Assembly from the telescoping pattern. Proofs written by pattern-matching against existing code compiled on first try. Proofs written "mathematically correct but Lean-naive" took multiple iterations.

- **`ring` vs `noncomm_ring`.** `ring` silently fails on non-commutative goals (produces an unsolved goal, not an error). Always use `noncomm_ring` in non-commutative algebras. This bit us multiple times.

- **`include 𝕂 in` must come before doc comments**, not after. And `variable (𝕂) in` doesn't work when `𝕂` only appears in the proof body (Lean drops unused type-level variables). This was our most time-consuming Lean 4.29 issue.

- **`nlinarith` needs explicit hints for products.** For goals like `a*b*c ≤ d*e*f`, provide intermediate `have` steps with `mul_le_mul_of_nonneg_left` rather than hoping `nlinarith` finds the factorization.

### Agent workflow

- **Agents excel at "fill this sorry given these lemmas."** Parallel agents on B1-B4, C1-C2, D1 (independent tasks with clear specs) worked perfectly.

- **Agents struggle with "figure out the right approach."** The Strang O(1/n²) agent tried three approaches and hit rate limits. Do the mathematical thinking yourself, delegate the Lean typing.

- **Record failed approaches in CHANGELOG.** The `variable (𝕂) in` saga, `omega` on non-linear goals, the triple-product expansion — recording WHY something failed prevented re-attempting dead ends across sessions.

### Calculus in Lean (from CommutatorScaling)

- **`(-u) • B` vs `u • (-B)` vs `-(u • B)`.** These are all equal but syntactically different: `neg_smul`, `smul_neg`, and `sub_eq_add_neg` convert between them. When `hasDerivAt_exp_smul_const'` gives `exp(u•(-B))` but you want `exp((-u)•B)`, use `simp_rw [show ∀ u, (-u) • B = u • (-B) from fun u => by rw [neg_smul, smul_neg]]` to normalize before applying the product rule.

- **`noncomm_ring` can't see through `exp` terms.** For algebraic simplification involving `exp`, `set E := exp(...)` to make it opaque, rewrite commutativity hypotheses (e.g., `B * exp(sB) = exp(sB) * B` via `Commute.exp_right`), then `noncomm_ring` handles the rest. Don't forget `Pi.mul_apply` for pointwise function multiplication.

- **`linarith` only works for ordered types.** For `𝔸`-valued equations from FTC-2, use `exact hftc.symm` or `rw; exact`, not `linarith`.

- **`norm_integral_le_of_norm_le_const` is the workhorse for interval integral bounds.** It requires `∀ x ∈ Ι a b, ‖f x‖ ≤ C` and gives `‖∫ f‖ ≤ C * |b - a|`. The key helper fact: `|s| ≤ |τ|` for `s ∈ Set.uIoc 0 τ` (case split on sign of τ).

---

## References

1. H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
2. A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
3. Mathlib: `Mathlib.Analysis.Normed.Algebra.Exponential`
4. Mathlib: `Mathlib.Analysis.Normed.Algebra.MatrixExponential`

## Imported Claude Cowork project instructions
