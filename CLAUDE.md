# Lie–Trotter Product Formula — Lean 4 Formalization

## Status (2026-04-26): 0 sorries, 0 own axioms, 2 transitive Lean-BCH-private axioms

`#print axioms bch_iteratedDeriv_s4Func_order4`, `exists_norm_s4Func_sub_exp_le_t5`,
and `lie_trotter` all return only `[propext, Classical.choice, Quot.sound]` —
the standard Lean foundational axioms.

All three formerly-axiomatized `bch_w4Deriv_*` / `bch_uniform_integrated`
results are now theorems composing Lean-BCH bridge corollaries with
exp-Lipschitz / triangle-inequality lifts:

| Lean-Trotter theorem | Composes Lean-BCH bridge | Transitive axiom |
|---|---|---|
| `bch_w4Deriv_quintic_level2` | `BCH.suzuki5_log_product_quintic_of_IsSuzukiCubic` | `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) |
| `bch_w4Deriv_level3_tight` | `BCH.suzuki5_log_product_quintic_tight_at_suzukiP` | `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) |
| `bch_uniform_integrated` (NEW 2026-04-26) | `BCH.suzuki5_log_product_septic_at_suzukiP` | `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (R₇) |

**Axiom 3 retired (2026-04-26):** `bch_uniform_integrated` is now a
theorem. The signature was changed from "uniform for all t ≥ 0"
(mathematically false — exp factors dominate polynomial bounds for
large t) to existential-δ "∃ δ > 0, ∃ C ≥ 0, ∀ t ∈ [0, δ),
‖S₄(t) − exp(tH)‖ ≤ C·(t⁵·boundSum + t⁷·R7Bound + t⁸)" (mathematically
correct; matches the FTC-2-derived shape with a single multiplier C
absorbing the exp-Lipschitz inflation and BCH M·τ⁸ tail). Downstream
`norm_suzuki4_level4_uniform` and `norm_suzuki4_level4_le_childs_when_small`
inherit the existential-δ form.

The two remaining transitive Lean-BCH axioms — `B1.c` (3-factor
symmetric BCH quintic Taylor bridge) and the new `R₇` (5-factor
septic identification) — each have full discharge roadmaps:
`claude/lean-bch-B1c-session-prompt.md` and
`claude/lean-bch-suzuki5-R7-followup-session-prompt.md`.

**Headline results:**
1. **Lie–Trotter** (`lie_trotter`, `lie_trotter_error_rate`, O(1/n)) — fully proved.
2. **Strang splitting** (`symmetric_lie_trotter`, O(1/n²)) — fully proved.
3. **Commutator scaling** (first-order, Strang, multi-operator, tighter Strang
   bound `norm_strang_comm_scaling_tight`) — fully proved.
4. **S₄ O(t⁵) abstract form** (`norm_suzuki4_fifth_order`,
   `norm_suzuki4_childs_form`) — closed with explicit residual-bound hypothesis.
5. **S₄ BCH-derived bounds** — closed given the 3 `bch_w4Deriv_*` axioms below:
   - L1 `norm_suzuki4_childs_form_via_level3`: recovers Childs (2021) bound
     (coefficients 0.0047–0.0284) from the CAS-certified Level 3 bound plus
     the Lean-proved termwise inequality γᵢ ≤ αᵢ. No heuristic axiom.
   - L2 `norm_suzuki4_level2_bch`: rigorous BCH bound with unit coefficients.
   - L3 `norm_suzuki4_level3_bch`: tight γᵢ prefactors.
   - L4 `norm_suzuki4_level4_uniform`: finite-t uniform bound with R₅ + R₇.
6. **h2 + h3 unconditional** (`iteratedDeriv_s4Func_order2_eq_sq`,
   `iteratedDeriv_s4Func_order3_eq_cb` under `IsSuzukiCubic p`).
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

**Transitive `sorryAx` dep:** 0. Axiom-inspect confirms:
`bch_iteratedDeriv_s4Func_order4`, `exists_norm_s4Func_sub_exp_le_t5`, and
`lie_trotter` depend only on the standard Lean foundational axioms.

**Transitive Lean-BCH-private axioms** (2):

| Lean-BCH axiom | Used by | Path to close |
|---|---|---|
| `BCH.symmetric_bch_quintic_sub_poly_axiom` (B1.c) | L2, L3 (`bch_w4Deriv_quintic_level2`, `bch_w4Deriv_level3_tight`) | `claude/lean-bch-B1c-session-prompt.md` (3-tier roadmap, ~2-3 weeks) |
| `BCH.suzuki5_log_product_septic_at_suzukiP_axiom` (R₇) | L4 (`bch_uniform_integrated`) | `claude/lean-bch-suzuki5-R7-followup-session-prompt.md` (~4-5 weeks) |

**Retired axioms** (historical):
- `bch_w4Deriv_quintic_level2` — theorem since 2026-04-24 (Lean-BCH bridge).
- `bch_w4Deriv_level3_tight` — theorem since 2026-04-24 (Lean-BCH bridge).
- `bch_uniform_integrated` — theorem since 2026-04-26 (Lean-BCH septic bridge).
- `bch_iteratedDeriv_s4Func_order4` — theorem since 2026-04-23 (SLICE chain).
- `bch_childs_pointwise_residual` (Childs heuristic) — retired 2026-04-23,
  replaced by the Level-3-derived reproduction.
- 4 symmetric-BCH-cubic axioms — retired 2026-04-23 via Lean-BCH direct import.

**Prefactor-bookkeeping note.** The Lean-BCH migration raised the symmetric-BCH
scaling constant from a speculative `10⁴·|c|³·s⁵` to the rigorous
`2·10⁷·|c|³·s⁵` (downstream `suzuki4_bchCubic_sum_bound`: `50000·s⁵ → 10⁸·s⁵`).
This bump is confined to the Path-B composition roadmap
(`norm_suzuki4_order5_via_strang_bch`). It does NOT affect the L1–L4 headline
prefactors, which come from the independent `bch_w4Deriv_*` axioms.

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
- **Mathlib:** latest master (commit `06a46dae` pinned in `lake-manifest.json`)
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
- `Suzuki4ViaBCH.lean` — **SLICE 3** wiring + 3 remaining BCH-interface axioms
  + L1-L4 BCH bounds.

Top-level: `LieTrotter.lean` (root import), `lakefile.lean`, `lean-toolchain`,
`CLAUDE.md` (this file), `CHANGELOG.md` (lab notes), `TODO.md` (remaining work).

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

**Actual lines:** ~170 (including 7 private helper lemmas for the `expSeries`/`tsum` interface)

---

#### Task C: Quadratic Step Error (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| C1. `norm_exp_mul_exp_sub_exp_add'` | $\|e^a e^b - e^{a+b}\| \le 2\|a\|\|b\| e^{\|a\|+\|b\|}$ | Hard | ✅ Proved |
| C2. `lie_trotter_step_error` | $\|e^{A/n} e^{B/n} - e^{(A+B)/n}\| \le \frac{\|A\|\|B\|}{n^2} e^{(\|A\|+\|B\|)/n}$ | Medium | ✅ Proved |

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

**Actual lines:** ~130

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

**Actual lines:** ~20

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

**Estimated lines:** ~60

---

### Track 5 — Extensions (optional)

#### Task F: Corollaries

| Sub-task | Statement | Priority | Status |
|----------|-----------|----------|--------|
| F1. `matrix_lie_trotter` | Specialization to `Matrix (Fin d) (Fin d) ℂ` | Low | 🔴 |
| F2. `symmetric_lie_trotter` | Strang splitting: $e^{A+B} = \lim (e^{A/2n} e^{B/n} e^{A/2n})^n$ with O(1/n²) rate | Low | ✅ |

These are nice-to-haves once the main theorem compiles without `sorry`.

---

### Track 6 — Commutator Scaling (Duhamel / variation-of-parameters)

#### Task H: Commutator-Scaling Trotter Error (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| H1. `exp_conj_sub_eq_integral` | $e^{\tau B} A e^{-\tau B} - A = \int_0^\tau e^{sB}[B,A]e^{-sB}ds$ | Medium | ✅ Proved |
| H2. `lie_trotter_integral_error` | $e^{tB}e^{tA} - e^{t(A+B)} = \int_0^t e^{(t-\tau)(A+B)}[e^{\tau B},A]e^{\tau A}d\tau$ | Hard | ✅ Proved |
| H3. `norm_exp_conj_sub_le` | $\|e^{\tau B}Ae^{-\tau B} - A\| \le \|[B,A]\|\|\tau\|e^{2\|\tau\|\|B\|}$ | Medium | ✅ Proved |
| H4. `norm_comm_exp_le` | $\|[e^{\tau B}, A]\| \le \|[B,A]\|\|\tau\|e^{3\|\tau\|\|B\|}$ | Easy | ✅ Proved |
| H5. `norm_lie_trotter_comm_scaling` | $\|e^{tB}e^{tA} - e^{t(A+B)}\| \le \|[B,A]\|t^2 e^{t(\|A\|+3\|B\|)}$ | Medium | ✅ Proved |

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

**Actual lines:** ~380

---

#### Task I: Second-Order Strang Commutator Scaling (✅ Done)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| I1. `exp_conj_sub_comm_eq_double_integral` | Double FTC extracting $[B,[B,A]]$ | Medium | ✅ Proved |
| I2. `norm_exp_conj_sub_comm_le` | $\|e^{\tau B}Ae^{-\tau B} - A - \tau[B,A]\| \le \frac{\|[B,[B,A]]\|}{2}\tau^2 e^{2\tau\|B\|}$ | Medium | ✅ Proved |
| I3. `hasDerivAt_conj_strang` | 4-factor product rule for $w(\tau)=e^{-\tau H}S_2(\tau)$ | Hard | ✅ Proved |
| I4. `norm_strang_comm_scaling` | $\|S_2(t)-e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$ | Hard | ✅ Proved |
| I5. `norm_palindromicProd_sub_exp_sum_comm` | Multi-operator Strang commutator scaling | Medium | ✅ Proved |

**Files:** `LieTrotter/StrangCommutatorScaling.lean` (~480 lines), `LieTrotter/MultiStrangCommutatorScaling.lean` (~170 lines)

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

**File:** `LieTrotter/HigherCommutator.lean` (~243 lines)

**Proof strategy:** Apply `exp_conj_sub_eq_integral` three times iteratively (same pattern as double FTC but one level deeper). The anti-Hermitian version uses isometry to eliminate the exponential factor. Building block for the tighter Strang bound and future S₄ commutator-scaling work.

---

#### Task K: Tighter Strang Commutator-Scaling (✅ Done) — **NEW RESULT**

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| K1. `norm_partA_sub_leading` | PartA remainder ≤ triple commutator · τ³/3 | Medium | ✅ Proved |
| K2. `norm_partB_sub_leading` | PartB remainder ≤ triple commutators · τ³ | Medium | ✅ Proved |
| K3. `norm_strang_comm_scaling_tight` | $\|S_2(t)-e^{tH}\| \le \frac{\|D\|}{6}t^3 + \frac{T}{4}t^4$ | Hard | ✅ Proved |

**File:** `LieTrotter/StrangCommutatorScalingTight.lean` (~559 lines)

**The new result:** Replaces the standard sum-of-norms bound with a tighter norm-of-difference bound:

Standard (Childs et al. 2021):
$$\|S_2(t) - e^{tH}\| \le \frac{\|[B,[B,A]]\|}{12}t^3 + \frac{\|[A,[A,B]]\|}{24}t^3$$

Tighter (this work):
$$\|S_2(t) - e^{tH}\| \le \frac{\|D\|}{6}t^3 + \frac{T}{4}t^4$$

where $D = [B,[B,A']] - [A',[A',B]]$ is the **effective double commutator** ($A' = A/2$).

The leading coefficient $\|D\|/6$ is always $\le$ the standard bound by the triangle inequality, and strictly tighter when the two double commutators partially cancel. For symmetric lattice Hamiltonians, the improvement can be ~37.5%.

**Proof strategy:** Extract the leading order $\tau^2/2 \cdot D$ from the Strang residual $\mathcal{T}_2(\tau)$ before taking norms, bounding the remainder using the triple FTC (Task J).

---

### Track 7 — S₄ Commutator-Scaling (In Progress)

#### Task L: Fourth-Order Suzuki Commutator-Scaling

**Goal:** Prove the genuine O(t⁵) S₄ bound with smaller prefactors than Childs et al. (Proposition 7), whose 8-term bound with coefficients 0.0047–0.0284 is labeled "heuristic" (not proven tight).

#### Modular architecture (Modules 1-3 complete; Module 4 outstanding)

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
| L4b-CAPSTONE. `norm_suzuki4_order5_of_s4Func_iteratedDerivs` | Close S₄ O(t⁵) given 3 s4Func identities | ✅ Proved |
| L4b-multinomial. `iteratedDeriv_prodExpList_order{0,1,2}` | Multinomial formulas for iteratedDeriv of exp products | ✅ Proved |
| L4b-h2. `iteratedDeriv_s4Func_order2_eq_sq` | **h2: iteratedDeriv 2 s4Func 0 = (A+B)²** | ✅ Proved UNCONDITIONAL |
| L4b-h3-factored. `sumTripleCorr_s4DList_eq_factored` | `sumTripleCorr = (4p³+(1-4p)³) • <op combo>` (operator algebra identity) | ✅ Proved |
| L4b-h3. `iteratedDeriv_s4Func_order3_eq_cb` | **h3: iteratedDeriv 3 s4Func 0 = (A+B)³** (given `IsSuzukiCubic p`) | ✅ Proved |
| L4b-w4-order3. `iteratedDeriv_w4Func_order3_eq_zero` | `iteratedDeriv 3 (w4Func A B p) 0 = 0` (given `IsSuzukiCubic p`) | ✅ Proved |
| L4b-h4-infra. `iteratedDeriv_prodExpList_order4` + `sumQuadCorr` def | h4 infrastructure (order-4 multinomial formula, quartic smul helpers) | ✅ Proved |
| L4b-h4-bridge. `iteratedDeriv_s4Func_order4_eq_q_of_bridge` | h4 conditional on `sumQuadCorr_s4DList = 0` | ✅ Proved |
| L4b-h4-bch. `sumQuadCorr_s4DList_eq_zero_of_bch`, `iteratedDeriv_s4Func_order4_eq_q_of_bch` | h4 via BCH-bridge + IsSuzukiCubic | ✅ Proved |
| L4b-capstone-bch. `norm_suzuki4_order5_via_bch` | S₄ O(t⁵) taking only IsSuzukiCubic + BCH identity | ✅ Proved |
| L4b-h4-BCH (alt). | Trotter-native BCH identity `sumQuadCorr = 2·(H·sumTripleCorr+sumTripleCorr·H)` for palindromic | 🔴 Open (module timeout; superseded by SLICE 1+2+3) |
| SLICE 1. `exists_norm_s4Func_sub_exp_le_t5` | Single-step BCH O(|τ|⁵) bound | ✅ Proved (via Lean-BCH M6 + opaque-RHS corollary) |
| SLICE 2. `iteratedDeriv_eq_of_norm_le_pow` | Generic Taylor-match-from-norm | ✅ Proved |
| SLICE 3. `bch_iteratedDeriv_s4Func_order4` | h4 as a theorem (prev. axiom) | ✅ Proved |
| L5. `norm_suzuki4_childs_via_residual` | Conditional Childs-form bound (8 explicit 4-fold commutators) | ✅ Proved |
| L5'. `norm_suzuki4_childs_form_via_level3` | Childs Prop pf4_bound_2term reproduced from Level 3 | ✅ Proved (replaces retired Childs-heuristic axiom) |

**Files:**
- `LieTrotter/Suzuki4HasDerivAt.lean` (~136 lines) — Module 1
- `LieTrotter/Suzuki4Module2.lean` (~167 lines) — Module 2
- `LieTrotter/Suzuki4Module3.lean` (~170 lines) — Module 3
- `LieTrotter/Suzuki4Module4.lean` (~150 lines) — Module 4a (continuity)
- `LieTrotter/Suzuki4DerivExplicit.lean` (~979 lines) — Module 4b-A1/A2/A3 + Phase 1-3 polynomial identities + smoothness + bridge
- `LieTrotter/Suzuki4Phase5.lean` (~740 lines) — Taylor-reduction + Leibniz bridges for orders 1-4 + CAPSTONE theorem (conditional closure of S₄ O(t⁵) from 3 s4Func iteratedDeriv identities)
- `LieTrotter/Suzuki4MultinomialExpand.lean` (~640 lines) — prodExpList + multinomial formulas + **h2 UNCONDITIONALLY + h3 under IsSuzukiCubic PROVED**
- `LieTrotter/Suzuki4ChildsForm.lean` (~223 lines) — Childs Prop pf4_bound_2term + conditional reduction
- `LieTrotter/Suzuki4OrderFive.lean` (~427 lines) — `norm_suzuki4_fifth_order` (alternative-form research target, 1 sorry)

**Current architecture (S₄ O(t⁵), all closed except transitive Lean-BCH sorry):**

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
                (closed upstream at rev `c71d8f2`, 2026-04-24).
```

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

| File | Count |
|------|-------|
| `LieTrotter/Telescoping.lean` | 0 |
| `LieTrotter/ExpBounds.lean` | 0 |
| `LieTrotter/StepError.lean` | 0 |
| `LieTrotter/ExpDivPow.lean` | 0 |
| `LieTrotter/Assembly.lean` | 0 |
| `LieTrotter/StrangSplitting.lean` | 0 |
| `LieTrotter/MultiOperator.lean` | 0 |
| `LieTrotter/MultiStrang.lean` | 0 |
| `LieTrotter/Suzuki4.lean` | 0 |
| `LieTrotter/CommutatorScaling.lean` | 0 |
| `LieTrotter/MultiCommutatorScaling.lean` | 0 |
| `LieTrotter/StrangCommutatorScaling.lean` | 0 |
| `LieTrotter/MultiStrangCommutatorScaling.lean` | 0 |
| `LieTrotter/HigherCommutator.lean` | 0 |
| `LieTrotter/StrangCommutatorScalingTight.lean` | 0 |
| `LieTrotter/Suzuki4FullDuhamel.lean` | 0 |
| `LieTrotter/Suzuki4CommutatorScaling.lean` | 0 (stubs removed; only `suzuki4Exp` def) |
| `LieTrotter/Suzuki4HasDerivAt.lean` | 0 (Module 1) |
| `LieTrotter/Suzuki4Module2.lean` | 0 (Module 2) |
| `LieTrotter/Suzuki4Module3.lean` | 0 (Module 3 — FTC-2 reduction proved) |
| `LieTrotter/Suzuki4Module4.lean` | 0 (Module 4a — continuity proved) |
| `LieTrotter/Suzuki4DerivExplicit.lean` | 0 (Module 4b-A1/A2/A3/B1 — 4 sub-tasks proved) |
| `LieTrotter/Suzuki4Phase5.lean` | 0 (Phase 5 Taylor-remainder framework + Leibniz bridges + CAPSTONE) |
| `LieTrotter/Suzuki4ChildsForm.lean` | 0 (Childs form with explicit residual hypothesis — closed) |
| `LieTrotter/Suzuki4OrderFive.lean` | 0 (S₄ O(t⁵) with explicit residual hypothesis — closed) |
| `LieTrotter/Suzuki4BchBound.lean` | 0 (SLICE 1 — single-step BCH O(|τ|⁵), since 2026-04-24) |
| `LieTrotter/TaylorMatch.lean` | 0 (SLICE 2 — generic Taylor-match-from-norm) |
| `LieTrotter/Suzuki4ViaBCH.lean` | 0 (SLICE 3 wiring + L1-L4 BCH bounds; 3 `bch_w4Deriv_*` axioms) |
| **Total** | **0** sorries, **0** transitive `sorryAx` (Lean-BCH closed at rev `c71d8f2`) |

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

---

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
