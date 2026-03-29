# Lean-Trotter

A Lean 4 formalization of the **Lie–Trotter product formula** for complete normed algebras:

$$e^{A+B} = \lim_{n \to \infty} \left(e^{A/n}\, e^{B/n}\right)^n$$

## Status

Work in progress. See [BLUEPRINT.md](BLUEPRINT.md) for the proof plan and task decomposition.

## Building

Requires [Lean 4](https://leanprover.github.io/) (v4.16.0) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake update
lake exe cache get    # download Mathlib oleans
lake build
```

## References

- H. Trotter, "On the product of semi-groups of operators," *Proc. AMS* 10(4), 1959.
- A. Childs et al., "Theory of Trotter Error with Commutator Scaling," *Phys. Rev. X* 11, 011020, 2021.
- [Mathlib: `Analysis.Normed.Algebra.Exponential`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Algebra/Exponential.html)

## License

Apache 2.0
