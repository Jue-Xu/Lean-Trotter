# Lean-Trotter

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 formalization of the **Lie-Trotter product formula**, **Strang
splitting**, and the fourth-order **Suzuki formula** for complete normed
algebras, including multi-operator generalizations and commutator-scaled error
bounds.

**First-order (Lie-Trotter):** step error $O(1/n^2)$, total error $O(1/n)$

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/n}\cdot e^{B/n}\right)^n, \qquad \left\lVert \left(e^{A/n}\cdot e^{B/n}\right)^n - e^{A+B} \right\rVert \le \frac{C}{n}$$

**Second-order (Strang splitting):** step error $O(1/n^3)$, total error $O(1/n^2)$

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/2n}\cdot e^{B/n}\cdot e^{A/2n}\right)^n, \qquad \left\lVert \left(e^{A/2n}\cdot e^{B/n}\cdot e^{A/2n}\right)^n - e^{A+B} \right\rVert \le \frac{C}{n^2}$$

Both formulas are also proved for **any finite number of operators** $A_1, \ldots, A_m$.

## Status

**Complete.** The project has 0 `sorry`s and 0 project or transitive
non-foundational axioms. `#print axioms` on the Lie-Trotter, Strang, Suzuki τ⁵,
quartic-convergence, and L4 uniform-refinement headlines reports only Lean's
foundational axioms `[propext, Classical.choice, Quot.sound]`. The Lean-BCH
dependency is pinned at `05e8c52`, where the former septic bridge assumptions
used by L4 are theorems.

The full convergence hierarchy is proved:

$$\text{Lie--Trotter }O(1/n)\quad\longrightarrow\quad
  \text{Strang }O(1/n^2)\quad\longrightarrow\quad
  \text{Suzuki }S_4\ O(1/n^4).$$

### Main results

#### Convergence theorems (total error after $n$ steps)

| Theorem | Formula | Total error | Operators |
|---------|---------|-------------|-----------|
| `lie_trotter` | $(e^{A/n} e^{B/n})^n \to e^{A+B}$ | $O(1/n)$ | 2 |
| `symmetric_lie_trotter` | $(e^{A/2n} e^{B/n} e^{A/2n})^n \to e^{A+B}$ | $O(1/n^2)$ | 2 |
| `lie_trotter_list` | $(\prod_i e^{A_i/n})^n \to e^{\sum_i A_i}$ | $O(1/n)$ | $m$ |
| `symmetric_lie_trotter_list` | palindromic product $\to e^{\sum_i A_i}$ | $O(1/n^2)$ | $m$ |
| `suzuki4_convergence_quartic` | $S_4(t/n)^n \to e^{t(A+B)}$ | $O(1/n^4)$ | 2 |

#### Step error bounds (single-step approximation)

| Theorem | Bound | Order |
|---------|-------|-------|
| `norm_exp_mul_exp_sub_exp_add'` | $\lVert e^a e^b - e^{a+b}\rVert \le 2\lVert a\rVert\lVert b\rVert\, e^{\lVert a\rVert+\lVert b\rVert}$ | $O(\lVert a\rVert\lVert b\rVert)$ |
| `norm_exp_mul_exp_mul_exp_sub_exp_add_cubic` | $\lVert e^a e^b e^a-e^{a+b+a}\rVert \le (7\lVert a\rVert^2\lVert b\rVert+3\lVert a\rVert\lVert b\rVert^2+3\lVert a\rVert^3)e^{2\lVert a\rVert+\lVert b\rVert}$ | cubic |

> **Note on "order":** A $k$-th order method has step error $O(1/n^{k+1})$ and total error $O(1/n^k)$ after $n$ steps, because the telescoping assembly multiplies by $n$.

### Module structure

```
LieTrotter/
├── Telescoping.lean       — algebraic telescoping identity + norm bound
├── ExpBounds.lean         — exponential series remainder estimates (B1–B5)
├── StepError.lean         — quadratic step error + commutator extraction
├── ExpDivPow.lean         — exp(a/n)^n = exp(a)
├── Assembly.lean          — O(1/n) convergence rate + main theorem
├── StrangSplitting.lean   — symmetric Lie-Trotter with O(1/n²) rate
├── MultiOperator.lean     — multi-operator first-order (A₁+⋯+Aₘ)
├── MultiStrang.lean       — multi-operator symmetric Strang with O(1/n²)
├── Suzuki4.lean           — fourth-order Suzuki integrator (S₄ from five S₂)
├── Suzuki4Convergence.lean — axiom-free O(1/n⁴) total error and convergence
├── CommutatorScaling.lean — first-order commutator-scaling error (Duhamel/FTC-2)
├── MultiCommutatorScaling.lean    — multi-operator variant
├── StrangCommutatorScaling.lean   — second-order (Strang) commutator-scaling
├── StrangTotalErrorCommScaling.lean — commutator-scaled Strang total error
├── HigherCommutator.lean  — triple FTC for [B,[B,[B,A]]]
├── StrangCommutatorScalingTight.lean — tighter norm-of-difference Strang bound
├── Suzuki4HasDerivAt.lean, Suzuki4Module{2,3,4}.lean, Suzuki4DerivExplicit.lean
│                          — HasDerivAt / FTC-2 scaffolding for S₄
├── Suzuki4ChildsForm.lean — Childs arXiv Proposition J.1 framework (conditional on residual)
├── Suzuki4OrderFive.lean  — S₄ O(t⁵) abstract-form target (conditional on residual)
├── Suzuki4MultinomialExpand.lean — prodExpList + h2; h3 under Suzuki cubic; h4 infra
├── Suzuki4Phase5.lean     — Taylor-reduction + Leibniz bridges + CAPSTONE
├── Suzuki4StrangBlocks.lean — S₄ = 5 Strang blocks; Suzuki cubic sum lemmas
├── Suzuki4ViaBCH.lean     — proved BCH bridges and Level 1–4 bounds
├── Suzuki4TightConvergence.lean — commutator-scaled O(1/n⁴) total error
├── Suzuki4UnitaryTotalError.lean — skew-adjoint/unitary total-error bounds
├── Suzuki4Commute.lean    — exactness when A and B commute
├── Suzuki4GapClosers.lean — general-parameter quartic corollaries
├── PrefactorStrict.lean   — formal strict prefactor comparisons
├── TrotterStepCount.lean  — accuracy-to-step counts (explicit Lie/Strang; existential S₄ constants)
└── MatrixCorollaries.lean — finite complex-matrix specializations
```

### S₄ fourth-order bounds and convergence

`Suzuki4ViaBCH.lean` provides three backward-compatible order statements
(`∃ δ > 0, ∃ C ≥ 0, error ≤ C·t⁵`) and sharper theorems whose types retain
the leading commutator coefficients. All are fully proved (`#print axioms`
reports only Lean's standard three):

- **Level 1 / Childs form:** `norm_suzuki4_childs_form_via_level3` records only
  the order. `norm_suzuki4_childs_explicit` carries the published Childs
  coefficients (0.0046–0.0284) plus an honest `K′t⁶` remainder, while
  `norm_suzuki4_le_childs_near_zero` removes that remainder on a neighbourhood
  of zero under a strict leading-coefficient gap. Childs et al.'s arXiv
  Proposition J.1 is rigorous; its coefficients are not proved tight.
- **Level 2 / unit form:** `norm_suzuki4_level2_bch` records only the order;
  `norm_suzuki4_level2_explicit` carries unit coefficients on the eight
  four-fold commutators plus a `K′t⁶` remainder.
- **Level 3 / BCH form:** `norm_suzuki4_level3_bch` records only the order;
  `norm_suzuki4_level3_explicit` carries the certified γᵢ leading
  coefficients plus a `K′t⁶` remainder.

The companion [Lean-BCH](https://github.com/Jue-Xu/Lean-BCH) project (pin
`05e8c52`) provides the underlying palindromic BCH machinery. **Level 4**
(`norm_suzuki4_level4_uniform`) adds the `t⁷ · bchR7Bound` correction on an
existential small-`t` interval `[0, δ)`; it too is free of transitive
non-foundational axioms at this pin.

`Suzuki4Convergence.lean` compounds the $O(|t|^5)$ single-step estimate into
`suzuki4_total_error_quartic` and `suzuki4_convergence_quartic`, proving
$O(1/n^4)$ total error in any complete normed algebra with `NormOneClass`.
`Suzuki4TightConvergence.lean` makes the leading nested-commutator coefficient
explicit, and `Suzuki4UnitaryTotalError.lean` sharpens the growth factor for
skew-adjoint inputs.

## Building

Requires [Lean 4](https://leanprover.github.io/) (v4.29.0-rc8) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake update lean-bch # fetch the pinned Lean-BCH revision
lake exe cache get    # download Mathlib oleans (~3 GB)
lake build
```

The first clean build also compiles Lean-BCH and can take substantially
longer than an incremental rebuild.

The symbolic derivations and numerical experiments used by the manuscript are
documented in [`scripts/README.md`](scripts/README.md). Install
`scripts/requirements-numerical.txt` and run the listed scripts to regenerate
the archived CSV results under `claude/`.

## Proof outline

### Standard Lie-Trotter (first-order, O(1/n) total error)

1. **Telescoping** (Track A): $X^n - Y^n = \sum_{k<n} X^k(X-Y)Y^{n-1-k}$, giving $\lVert X^n - Y^n\rVert \le n\lVert X-Y\rVert M^{n-1}$.

2. **Exponential bounds** (Track B): From $e^a = \sum a^k/k!$, prove $\lVert e^a\rVert \le e^{\lVert a\rVert}$, the remainder $\lVert e^a - 1 - a\rVert \le \lVert a\rVert^2 e^{\lVert a\rVert}/2$, and the third-order remainder $\lVert e^a - 1 - a - a^2/2\rVert \le \lVert a\rVert^3 e^{\lVert a\rVert}/6$.

3. **Quadratic step error** (Track C): $\lVert e^a e^b - e^{a+b}\rVert \le 2\lVert a\rVert\lVert b\rVert\, e^{\lVert a\rVert+\lVert b\rVert}$, via the factorization $e^a e^b - e^{a+b} = (e^a-1)(e^b-1) - (e^{a+b}-e^a-e^b+1)$ and an inductive cross-term bound.

4. **Assembly** (Tracks D+E): Set $P_n = e^{A/n}e^{B/n}$, $Q_n = e^{(A+B)/n}$. Telescoping gives $\lVert P_n^n - Q_n^n\rVert \le n \cdot \underbrace{O(1/n^2)}_{\text{step error}} \cdot e^{O(1)} = O(1/n)$.

### Strang splitting (second-order, O(1/n²) total error)

5. **Commutator extraction**: Factor $e^a e^b - e^{a+b} = [a,b]/2 + R(a,b)$ where $R$ is cubic. The commutator $[a,b]$ cancels by symmetry in $e^a e^b e^a$.

6. **Cubic step error**: $\lVert e^a e^b e^a - e^{2a+b}\rVert = O(\lVert a\rVert^2\lVert b\rVert + \lVert a\rVert\lVert b\rVert^2)$. With $a = A/2n$, $b = B/n$, this is $O(1/n^3)$.

7. **Assembly**: Telescoping with cubic step error: $n \cdot \underbrace{O(1/n^3)}_{\text{step error}} \cdot e^{O(1)} = O(1/n^2)$.

### Multi-operator generalizations

8. **First-order** ($m$ operators): Induction on the list, peeling off one factor and applying the quadratic step error.

9. **Second-order** ($m$ operators): Recursive palindromic product $S_n(A_1, \ldots, A_m) = e^{A_1/2n} \cdot S_n(A_2, \ldots, A_m) \cdot e^{A_1/2n}$. Induction reduces each step to the 2-operator cubic Strang bound.

### Suzuki S₄ integrator (fourth-order, O(1/n⁴) total error)

10. **Composition:** $S_4(t) = S_2(pt)^2 \cdot S_2((1-4p)t) \cdot S_2(pt)^2$ for $p \in [0,1/2]$. Five S₂ steps have time fractions summing to 1; the middle fraction may be negative.

11. **Fourth-order cancellation and assembly:** If
$4p^3+(1-4p)^3=0$—in particular for
$p=1/(4-4^{1/3})$—the formalized BCH/Taylor argument gives an $O(|t|^5)$
single-step error. Telescoping then proves $O(1/n^4)$ total error and
convergence to $e^{t(A+B)}$.

## References

- H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
- A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
- G. Strang, "On the construction and comparison of difference schemes," *SIAM J. Numer. Anal.* 5(3), 1968.
- [Mathlib: `Analysis.Normed.Algebra.Exponential`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html)

## License

Apache 2.0
