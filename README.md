# Lean-Trotter

A Lean 4 formalization of the **Lie–Trotter product formula** for complete normed algebras:

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/n}\, e^{B/n}\right)^n$$

## Status

**Complete.** All theorems proved, 0 `sorry`s, full build passes.

### Main results

| Theorem | Statement |
|---------|-----------|
| `lie_trotter` | $(e^{A/n} e^{B/n})^n \to e^{A+B}$ as $n \to \infty$ |
| `lie_trotter_error_rate` | $\exists C > 0,\; \lVert(e^{A/n} e^{B/n})^n - e^{A+B}\rVert \le C/n$ |
| `norm_exp_mul_exp_sub_exp_add'` | $\lVert e^a e^b - e^{a+b}\rVert \le 2\lVert a\rVert\lVert b\rVert\, e^{\lVert a\rVert+\lVert b\rVert}$ |

### Module structure

```
LieTrotter/
├── Telescoping.lean    — algebraic telescoping identity + norm bound
├── ExpBounds.lean      — exponential series remainder estimates (B1–B4)
├── StepError.lean      — quadratic step error bound (hardest lemma)
├── ExpDivPow.lean      — exp(a/n)^n = exp(a)
└── Assembly.lean       — O(1/n) convergence rate + main theorem
```

## Building

Requires [Lean 4](https://leanprover.github.io/) (v4.29.0-rc8) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake update
lake exe cache get    # download Mathlib oleans (~3 GB)
lake build
```

## Proof outline

1. **Telescoping identity** (Track A): $X^n - Y^n = \sum_{k<n} X^k(X-Y)Y^{n-1-k}$, giving the norm bound $\lVert X^n - Y^n\rVert \le n\lVert X-Y\rVert M^{n-1}$.

2. **Exponential bounds** (Track B): From the power series $e^a = \sum a^k/k!$, prove $\lVert e^a\rVert \le e^{\lVert a\rVert}$ and the second-order remainder $\lVert e^a - 1 - a\rVert \le \lVert a\rVert^2 e^{\lVert a\rVert}/2$.

3. **Quadratic step error** (Track C): The key estimate $\lVert e^a e^b - e^{a+b}\rVert \le 2\lVert a\rVert\lVert b\rVert\, e^{\lVert a\rVert+\lVert b\rVert}$, proved via the algebraic factorization $e^a e^b - e^{a+b} = (e^a-1)(e^b-1) - (e^{a+b}-e^a-e^b+1)$ and an inductive cross-term bound.

4. **Assembly** (Tracks D+E): Combine via $P_n = e^{A/n}e^{B/n}$, $Q_n = e^{(A+B)/n}$, telescoping gives $\lVert P_n^n - Q_n^n\rVert \le n \cdot O(1/n^2) \cdot e^{O(1)} = O(1/n) \to 0$.

## References

- H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
- A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
- [Mathlib: `Analysis.Normed.Algebra.Exponential`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html)

## License

Apache 2.0
