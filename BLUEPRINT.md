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

#### Task B: Exponential Remainder Bounds (🔴 Not started)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| B1. `norm_exp_le` | $\|e^a\| \le e^{\|a\|}$ | Easy | 🔴 |
| B2. `norm_exp_sub_one_le` | $\|e^a - 1\| \le e^{\|a\|} - 1$ | Easy | 🔴 |
| B3. `exp_sub_one_sub_bound_real` | $e^x - 1 - x \le \frac{x^2}{2} e^x$ for $x \ge 0$ | Medium | 🔴 |
| B4. `norm_exp_sub_one_sub_le` | $\|e^a - 1 - a\| \le \frac{\|a\|^2}{2} e^{\|a\|}$ | Medium | 🔴 |

**File:** `LieTrotter/ExpBounds.lean`

**Proof strategies:**

- **B1–B2:** Follow from the power series $e^a = \sum a^k/k!$, triangle inequality, and comparison with the real exponential. Mathlib has `NormedSpace.exp_series_summable` and `norm_tsum_le_tsum_norm`. Check if `NormedSpace.norm_exp_le_of_norm_le` or similar already exists.

- **B3 (real analysis):**
  $$e^x - 1 - x = \sum_{k=2}^{\infty} \frac{x^k}{k!} \le \frac{x^2}{2} \sum_{j=0}^{\infty} \frac{x^j}{j!} = \frac{x^2}{2} e^x$$
  Uses $k! \ge 2 \cdot (k-2)!$ for $k \ge 2$. In Lean: work with `Real.hasSum_exp` or `Real.exp_eq_tsum`, shift the index by 2, bound factorials with `Nat.factorial_pos` and explicit arithmetic.

- **B4:** Combine B3 with the norm series bound. Write $e^a - 1 - a = \sum_{k \ge 2} a^k/k!$, take norms, reduce to the real bound B3 applied to $\|a\|$.

**Estimated lines:** ~80

---

#### Task C: Quadratic Step Error (🔴 Not started — HARDEST)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| C1. `norm_exp_mul_exp_sub_exp_add'` | $\|e^a e^b - e^{a+b}\| \le 2\|a\|\|b\| e^{\|a\|+\|b\|}$ | Hard | 🔴 |
| C2. `lie_trotter_step_error` | $\|e^{A/n} e^{B/n} - e^{(A+B)/n}\| \le \frac{\|A\|\|B\|}{n^2} e^{(\|A\|+\|B\|)/n}$ | Medium | 🔴 |

**File:** `LieTrotter/StepError.lean`

**C1 is the critical lemma.** Three possible approaches, in order of feasibility:

1. **Second-order expansion (recommended):**
   Write $e^a = 1 + a + R_a$, $e^b = 1 + b + R_b$ with $\|R_a\| \le \|a\|^2 e^{\|a\|}/2$.
   Then $e^a e^b - e^{a+b} = ab + \text{(remainder cross terms)} - R_{a+b}$.
   Bound each piece. The $ab$ term gives $\|a\|\|b\|$; remainders give higher-order terms that are absorbed into the constant 2.

   **Con:** The bookkeeping is tedious — many cross terms to bound individually.

2. **Integral formula (cleaner math, heavier Lean):**
   $$e^{a} e^{b} - e^{a+b} = \int_0^1 e^{sa}\,[a,b]\,e^{(1-s)(a+b)}\,e^{sb}\,ds + \text{h.o.t.}$$
   Requires `MeasureTheory.integral` (Bochner integral) which exists in Mathlib but involves significant API overhead.

3. **Double series manipulation:**
   Expand both sides as double/single power series, cancel terms order by order. The cancellation at order $m$ involves multinomial coefficients vs binomial. Feasible but very fiddly in Lean.

**Recommendation:** Start with approach 1. If the cross-term bookkeeping becomes unmanageable, explore whether a weaker bound (e.g., with a larger constant) simplifies the proof while still giving $O(\|a\|\|b\|)$.

**C2** follows from C1 by substituting $a = A/n$, $b = B/n$ and using $\|c \cdot x\| = |c| \cdot \|x\|$.

**Estimated lines:** ~100

---

### Track 3 — Connecting Lemmas

#### Task D: `exp(a/n)^n = exp(a)` (🔶 Medium)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| D1. `exp_div_pow` | $(e^{a/n})^n = e^a$ for $n > 0$ | Medium | 🔴 |
| D2. `norm_exp_smul_le` | $\|e^{c \cdot a}\| \le e^{\|c\| \|a\|}$ | Easy | 🔴 |

**File:** `LieTrotter/ExpDivPow.lean`

**D1 proof:**
- $a/n$ commutes with itself, so $e^{a/n} \cdot e^{a/n} = e^{2a/n}$ by `exp_add_of_commute`.
- By induction (or `exp_nsmul` if it exists): $e^{a/n}^n = e^{n \cdot a/n} = e^a$.
- The scalar algebra step $n \cdot (n^{-1} \cdot a) = a$ needs `smul_smul` + `mul_inv_cancel` in the scalar field.
- **Mathlib search targets:** `exp_nsmul`, `exp_nat_mul`, `exp_smul_comm`, `Commute.exp_add`.

**D2** follows from `norm_exp_le` (B1) and `norm_smul_le`.

**Estimated lines:** ~30

---

### Track 4 — Assembly

#### Task E: Main Theorem (🔶 Structure done, needs sorry-filling)

| Sub-task | Statement | Difficulty | Status |
|----------|-----------|------------|--------|
| E1. `lie_trotter_error_rate` | $\exists C > 0,\; \|P_n^n - e^{A+B}\| \le C/n$ | Medium | 🔶 (structure done, 4 sorry's) |
| E2. `lie_trotter` | $P_n^n \to e^{A+B}$ | Easy | 🔶 (done modulo E1) |

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
Phase 1 (parallel):    A (✅)     B1,B2 (🔴)     D2 (🔴)
                         │           │               │
Phase 2 (parallel):    A (done)   B3,B4 (🔴)     D1 (🔴)
                                     │
Phase 3:                           C1 (🔴)  ← blocks on B4
                                     │
Phase 4:                           C2 (🔴)  ← blocks on C1
                                     │
Phase 5:              E1 (🔶)  ← blocks on A, C2, D1
                        │
Phase 6:              E2 (🔶)  ← blocks on E1
```

**Critical path:** B3 → B4 → C1 → C2 → E1 → E2

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

### Needs verification (search Mathlib before implementing)

- `exp_nsmul` or `exp_nat_mul` — may give `exp(a)^n = exp(n•a)` directly
- `NormedSpace.norm_exp_le` — may already bound `‖exp(a)‖`
- `expSeries_apply` — access to individual terms of the exponential series
- `Real.exp_bound` or `Real.exp_bound'` — Taylor remainder bounds for real exp

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
| `LieTrotter/ExpBounds.lean` | 4 | B1, B2, B3, B4 |
| `LieTrotter/StepError.lean` | 2 | C1, C2 |
| `LieTrotter/ExpDivPow.lean` | 2 | D1, D2 |
| `LieTrotter/Assembly.lean` | ~4 | calc chain steps in E1 |
| **Total** | **~12** | |

---

## References

1. H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
2. A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
3. Mathlib: `Mathlib.Analysis.Normed.Algebra.Exponential`
4. Mathlib: `Mathlib.Analysis.Normed.Algebra.MatrixExponential`
