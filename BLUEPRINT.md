# Lie–Trotter Product Formula — Lean 4 Proof Blueprint

## Goal

Prove the Lie–Trotter product formula in Lean 4 using Mathlib:

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/n}\, e^{B/n}\right)^n$$

for elements $A, B$ in a complete normed algebra $\mathfrak{A}$ over $\mathbb{R}$ or $\mathbb{C}$.

```lean
theorem lie_trotter (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp 𝕂 ((n : 𝕂)⁻¹ • A) * exp 𝕂 ((n : 𝕂)⁻¹ • B)) ^ n)
      atTop (nhds (exp 𝕂 (A + B)))
```

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

```
Lean-Trotter/
├── LieTrotter/
│   ├── Telescoping.lean       ← Task A: algebraic identity + norm bound
│   ├── ExpBounds.lean         ← Task B: exp series remainder estimates
│   ├── StepError.lean         ← Task C: quadratic error ‖exp(a)exp(b) − exp(a+b)‖
│   ├── ExpDivPow.lean         ← Task D: exp(a/n)^n = exp(a)
│   └── Assembly.lean          ← Task E: combine into lie_trotter_error_rate + main thm
├── LieTrotter.lean            ← root import file
├── lakefile.lean
├── lean-toolchain
└── BLUEPRINT.md
```

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

#### Task C: Quadratic Step Error (🔶 1 sorry remains)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| C1. `norm_exp_mul_exp_sub_exp_add'` | $\|e^a e^b - e^{a+b}\| \le 2\|a\|\|b\| e^{\|a\|+\|b\|}$ | Hard | 🔶 (1 sorry: `norm_exp_cross_term_le`) |
| C2. `lie_trotter_step_error` | $\|e^{A/n} e^{B/n} - e^{(A+B)/n}\| \le \frac{\|A\|\|B\|}{n^2} e^{(\|A\|+\|B\|)/n}$ | Medium | ✅ Proved |

**File:** `LieTrotter/StepError.lean`

**C1 proof approach (algebraic factorization):**

The proof uses a cleaner strategy than the second-order expansion:
1. **Algebraic identity** (by `ring`): $e^a e^b - e^{a+b} = (e^a-1)(e^b-1) - (e^{a+b} - e^a - e^b + 1)$
2. **Triangle inequality**: Both parts bounded by $(e^{\|a\|}-1)(e^{\|b\|}-1)$, giving $\le 2(e^{\|a\|}-1)(e^{\|b\|}-1)$
3. **Final bound** via `exp_sub_one_le_mul_exp`: $(e^s-1)(e^t-1) \le st \cdot e^{s+t}$

**Remaining sorry**: `norm_exp_cross_term_le` — proves $\|e^{a+b} - e^a - e^b + 1\| \le (e^{\|a\|}-1)(e^{\|b\|}-1)$.
This requires a power series argument: at each order $k \ge 2$, $\|(a+b)^k - a^k - b^k\| \le (\|a\|+\|b\|)^k - \|a\|^k - \|b\|^k$ (cross terms only), then sum to get $(e^{\|a\|+\|b\|} - 1 - (\|a\|+\|b\|)) - (e^{\|a\|} - 1 - \|a\|) - (e^{\|b\|} - 1 - \|b\|) = e^{\|a\|+\|b\|} - e^{\|a\|} - e^{\|b\|} + 1 = (e^{\|a\|}-1)(e^{\|b\|}-1)$.

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

#### Task E: Main Theorem (🔶 2 sorry's remain in E1)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| E1. `lie_trotter_error_rate` | $\exists C > 0,\; \|P_n^n - e^{A+B}\| \le C/n$ | Medium | 🔶 (2 sorry's: max bound + final calc) |
| E2. `lie_trotter` | $P_n^n \to e^{A+B}$ | Easy | ✅ Proved (modulo E1) |

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
| F2. `symmetric_lie_trotter` | Strang splitting: $e^{A+B} = \lim (e^{A/2n} e^{B/n} e^{A/2n})^n$ | Low | 🔴 |

These are nice-to-haves once the main theorem compiles without `sorry`.

---

## Dependency DAG (build order)

```
Phase 1 (parallel):    A (✅)     B1,B2 (✅)     D2 (✅)
                         │           │               │
Phase 2 (parallel):    A (done)   B3,B4 (✅)     D1 (✅)
                                     │
Phase 3:                           C1 (🔶)  ← 1 sorry: norm_exp_cross_term_le
                                     │
Phase 4:                           C2 (✅)
                                     │
Phase 5:              E1 (🔶)  ← 2 sorry's: max bound + final calc
                        │
Phase 6:              E2 (✅)
```

**Critical path:** ~~B3 → B4 →~~ C1 (cross-term) → E1 (assembly calc)

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

### Not in Mathlib (proved ourselves)

- `norm_exp_le` — $\|e^a\| \le e^{\|a\|}$ for general Banach algebras (only `Complex.norm_exp_le_exp_norm` exists for ℂ)
- `exp_sub_one_sub_bound_real` — $e^x - 1 - x \le x^2/2 \cdot e^x$
- `norm_exp_sub_one_le` — $\|e^a - 1\| \le e^{\|a\|} - 1$

---

## How to Build

```bash
cd Lean-Trotter
lake update
lake exe cache get    # download Mathlib oleans (~3 GB)
lake build            # type-checks; will warn on sorry's
```

---

## `sorry` Census

| File | Count | Lemmas |
|------|-------|--------|
| `LieTrotter/Telescoping.lean` | 0 | — |
| `LieTrotter/ExpBounds.lean` | 0 | — |
| `LieTrotter/StepError.lean` | 1 | `norm_exp_cross_term_le` (private helper for C1) |
| `LieTrotter/ExpDivPow.lean` | 0 | — |
| `LieTrotter/Assembly.lean` | 2 | `h_max` bound + final calc step in E1 |
| **Total** | **3** | |

### Remaining sorry details

1. **`norm_exp_cross_term_le`** (StepError.lean:47) — `‖e^{a+b} - e^a - e^b + 1‖ ≤ (e^{\|a\|}-1)(e^{\|b\|}-1)`.
   Requires power series termwise bound: at order $k \ge 2$, the "cross terms" of $(a+b)^k$ satisfy $\|(a+b)^k - a^k - b^k\| \le (\|a\|+\|b\|)^k - \|a\|^k - \|b\|^k$. Sum and use $e^{s+t} - e^s - e^t + 1 = (e^s-1)(e^t-1)$.

2. **`h_max`** (Assembly.lean:58) — `max ‖P‖ ‖Q‖ ≤ exp((‖A‖+‖B‖)/n)`.
   Follows from B1 + `norm_mul_le` for ‖P‖ and B1 + `norm_add_le` for ‖Q‖.

3. **Final calc** (Assembly.lean:69) — Simplify $n \cdot \frac{2\|A\|\|B\|}{n^2} \cdot e^{s/n} \cdot e^{s/n}^{n-1} \le C/n$.
   Uses $e^{s/n}^n = e^s$ (exact equality via `Real.exp_natMul`) and algebra.

---

## References

1. H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
2. A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
3. Mathlib: `Mathlib.Analysis.Normed.Algebra.Exponential`
4. Mathlib: `Mathlib.Analysis.Normed.Algebra.MatrixExponential`
