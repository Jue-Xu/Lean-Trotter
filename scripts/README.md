# CAS-Assisted Computation Scripts

Scripts that compute quantities too intricate for direct Lean formalization,
emitting Lean-ready snippets for the main codebase.

## `compute_bch_prefactors.py`

**Purpose:** Compute the exact BCH-derived prefactors for the Suzuki S₄
4th-order Trotter error, projected onto Childs's 8 four-fold commutator basis.

**Method:** Symbolic non-commutative free algebra over ℚ[p]:
1. Represent elements of the free non-commutative algebra as
   `dict[tuple[int,...], sympy.Expr]` keyed by words (0 = A, 1 = B) with
   coefficients in ℚ[p].
2. Compute `S₂(s) = exp((s/2)A)·exp(sB)·exp((s/2)A)` via truncated
   series expansion.
3. Compute `S₄(τ) = S₂(pτ)·S₂(pτ)·S₂((1-4p)τ)·S₂(pτ)·S₂(pτ)`.
4. Compute `log(S₄(τ)) - τ·(A+B)` via truncated `log(1+x)` series.
5. Reduce using the Suzuki cubic condition `60p³ − 48p² + 12p − 1 = 0`
   (substituting `p³ = (48p² − 12p + 1)/60`).
6. Verify that orders 2, 3, 4 vanish (palindromic + Suzuki cancellations).
7. Extract degree-5 residual `R₅` as a polynomial in words of length 5.
8. Project onto Childs's 8 four-fold commutator basis via
   `sympy.Matrix.gauss_jordan_solve`.
9. Specialize at Suzuki `p = 1/(4 − 4^(1/3)) ≈ 0.414491` to get numerical
   values; emit Lean snippet.

**Dependencies:** `sympy` (tested with 1.13+).

**Usage:**
```bash
python3 compute_bch_prefactors.py
```

**Output (truncated):**
```
======================================================================
Verification: orders 2, 3, 4 vanish under Suzuki condition
======================================================================
  Degree 2: vanishes ✓
  Degree 3: vanishes ✓
  Degree 4: vanishes ✓

======================================================================
Projection onto Childs 8-commutator basis
======================================================================
  C1:  γ = 127p²/144000 + 13p/36000 − 1/24000   (≈ 0.000260)
  C2:  γ = p²/12000 + 13p/6000 − 1/4000          (≈ 0.000662)
  C3:  γ = 0
  C4:  γ = −61p²/9000 + 13p/3000 − 1/2000        (≈ 0.000132)
  C5:  γ = 31p²/9000 − 13p/18000 + 1/12000       (≈ 0.000376)
  C6:  γ = 31p²/3000 − 13p/6000 + 1/4000          (≈ 0.001127)
  C7:  γ = 0
  C8:  γ = p²/18000 + 13p/9000 − 1/6000          (≈ 0.000442)

======================================================================
Comparison with Childs (2021) heuristic coefficients
======================================================================
  C1: ours ≈ 0.000260, childs = 0.00470  [tighter ✓]  (18× tighter)
  C2: ours ≈ 0.000662, childs = 0.00570  [tighter ✓]  ( 9× tighter)
  ... (all 8 coefficients strictly tighter than Childs's heuristics)
```

**Caveats:**

1. **Over-completeness of the Childs basis.** The weight-5 free Lie
   algebra in 2 generators has dimension 6 (Witt's formula), but Childs
   uses 8 commutators, so the projection is not unique. The script chose
   the specific projection with both free parameters set to zero, which
   gives `γ₃ = γ₇ = 0`. Alternative projections redistribute mass.

2. **Leading-order only.** The prefactors bound the leading (τ⁵)
   coefficient of `log(S₄(τ)) − τH`. The pointwise bound on `w4Deriv τ`
   across `[0, t]` includes higher-order (τ⁶, τ⁷, ...) corrections;
   Childs's larger coefficients fold these in. Our prefactors are
   valid at the leading-order asymptote.

3. **Symbolic `p` handled via reduction.** The Suzuki condition
   `4p³+(1-4p)³=0` is used to reduce `p^n` (n ≥ 3) to polynomials of
   degree ≤ 2 in `p`. This correctly models Suzuki-specific cancellations.

## Integration with Lean-Trotter

The emitted Lean snippet is pasted into
`LieTrotter/Suzuki4ViaBCH.lean` as the definition of `bchTightPrefactors`.
Full provenance (polynomial in p + Suzuki reduction + Childs projection +
specialization to Suzuki p) is documented in the Lean docstring.

## Future work

- **Eliminate the over-completeness ambiguity.** Solve the optimization
  problem `min Σᵢ|γᵢ|·‖Cᵢ‖` over all valid projections, to get the
  tightest bound in the Childs basis.

- **Higher-order corrections.** Extend the script to compute a bound
  valid on a nontrivial interval `[0, t]`, folding in τ⁶ and higher
  contributions.

- **Full symbolic p (without reduction).** For a fully symbolic Suzuki
  result, carry `p` symbolically throughout without applying the Suzuki
  cubic reduction until the very end. Currently the script applies
  reduction eagerly for simpler display.
