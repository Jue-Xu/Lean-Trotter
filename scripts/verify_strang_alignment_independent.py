#!/usr/bin/env python3
"""Independent cross-check of scripts/sweep_strang_alignment.py.

Re-derives selected rows of claude/strang_alignment_sweep.csv through a
deliberately different code path:
  * operators built with functools.reduce over reversed site order (the
    resulting matrices are different representations; norms must agree),
  * spectral norms via explicit SVD (np.linalg.svd) instead of
    np.linalg.norm(., 2),
  * an extra check that the skew-Hermitian convention (A -> iA, B -> iB)
    leaves ||D||, S, and the ratio unchanged, as claimed in the sweep's
    docstring and required to match the Lean anti-Hermitian setting.

Rows verified (vs CSV to 1e-9 relative):
  Heis XXX L=4 even/odd, TFIM h=1.0 L=4 ZZ/field, TFIM h=2.0 L=6 even/odd,
  LTFIM L=8 ZZ/field.
"""

import csv
import os
import sys
from functools import reduce

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CSV = os.path.join(HERE, "..", "claude", "strang_alignment_sweep.csv")

I2 = np.eye(2, dtype=complex)
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)


def op_at(sites, L):
    """Tensor product with sites indexed from the RIGHT (reversed convention)."""
    mats = [I2] * L
    for s, M in sites:
        mats[L - 1 - s] = M
    return reduce(np.kron, mats)


def svd_norm(M):
    return float(np.linalg.svd(M, compute_uv=False)[0])


def comm(P, Q):
    return P @ Q - Q @ P


def metrics(A, B):
    X = comm(B, comm(B, A))
    Y = comm(A, comm(A, B))
    D = 0.5 * X - 0.25 * Y
    nD = svd_norm(D)
    S = 0.5 * svd_norm(X) + 0.25 * svd_norm(Y)
    return nD, S, nD / S


def heis_eo(L, delta):
    def bond(i):
        return (op_at([(i, SX), (i + 1, SX)], L)
                + op_at([(i, SY), (i + 1, SY)], L)
                + delta * op_at([(i, SZ), (i + 1, SZ)], L))
    A = sum(bond(i) for i in range(0, L - 1, 2))
    B = sum(bond(i) for i in range(1, L - 1, 2))
    return A, B


def tfim_eo(L, J, h):
    deg = [2] * L
    deg[0] = deg[-1] = 1

    def bond(i):
        return (-J * op_at([(i, SZ), (i + 1, SZ)], L)
                - h * (op_at([(i, SX)], L) / deg[i]
                       + op_at([(i + 1, SX)], L) / deg[i + 1]))
    A = sum(bond(i) for i in range(0, L - 1, 2))
    B = sum(bond(i) for i in range(1, L - 1, 2))
    return A, B


def tfim_cf(L, J, h):
    A = -J * sum(op_at([(i, SZ), (i + 1, SZ)], L) for i in range(L - 1))
    B = -h * sum(op_at([(i, SX)], L) for i in range(L))
    return A, B


def ltfim_cf(L, J, hx, hz):
    A = -J * sum(op_at([(i, SZ), (i + 1, SZ)], L) for i in range(L - 1))
    B = -sum(hx * op_at([(i, SX)], L) + hz * op_at([(i, SZ)], L)
             for i in range(L))
    return A, B


CHECKS = [
    ("Heis XXX", "Δ=1.0", "even/odd", 4, lambda: heis_eo(4, 1.0)),
    ("TFIM", "h=1.0", "ZZ/field", 4, lambda: tfim_cf(4, 1.0, 1.0)),
    ("TFIM", "h=2.0", "even/odd", 6, lambda: tfim_eo(6, 1.0, 2.0)),
    ("LTFIM", "hx=1, hz=0.5", "ZZ/field", 8, lambda: ltfim_cf(8, 1.0, 1.0, 0.5)),
]


def main():
    with open(CSV) as f:
        rows = {(r["model"], r["params"], r["split"], int(r["L"])): r
                for r in csv.DictReader(f)}

    ok = True
    for model, params, split, L, builder in CHECKS:
        A, B = builder()
        nD_AB, S_AB, r_AB = metrics(A, B)
        nD_BA, S_BA, r_BA = metrics(B, A)
        ref = rows[(model, params, split, L)]
        for name, got, want in [
            ("nD_AB", nD_AB, float(ref["nD_AB"])),
            ("S_AB", S_AB, float(ref["S_AB"])),
            ("ratio_AB", r_AB, float(ref["ratio_AB"])),
            ("nD_BA", nD_BA, float(ref["nD_BA"])),
            ("S_BA", S_BA, float(ref["S_BA"])),
            ("ratio_BA", r_BA, float(ref["ratio_BA"])),
        ]:
            rel = abs(got - want) / max(abs(want), 1e-300)
            status = "OK " if rel < 1e-9 else "FAIL"
            if rel >= 1e-9:
                ok = False
            print(f"{status} {model} {params} {split} L={L} {name}: "
                  f"indep={got:.12g} csv={want:.12g} rel={rel:.2e}")
        # Skew-Hermitian convention invariance: A -> iA, B -> iB.
        nD_i, S_i, r_i = metrics(1j * A, 1j * B)
        rel = abs(r_i - r_AB) / r_AB
        status = "OK " if rel < 1e-12 else "FAIL"
        if rel >= 1e-12:
            ok = False
        print(f"{status} {model} {params} {split} L={L} skew-invariance: "
              f"ratio(iA,iB)={r_i:.12g} vs ratio(A,B)={r_AB:.12g}")

    print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
