#!/usr/bin/env python3
"""Numerical sweep settling the OPEN ISSUE in lean4trotter/apd_tighter_strang.tex (~line 279).

Question. The tighter Strang bound (eq:strang-tighter-final) has leading coefficient
    ||D|| / 6,   D = [B,[B,A']] - [A',[A',B]],  A' = A/2,
i.e. D = (1/2)[B,[B,A]] - (1/4)[A,[A,B]], while the standard sum-of-norms bound
(Childs et al. 2021, Prop. 16 in the arXiv version) has leading coefficient
    S / 6,       S = (1/2)||[B,[B,A]]|| + (1/4)||[A,[A,B]]||.
norm_D_le_sum_of_norms (Lean) proves ||D|| <= S always.  Is the gain
    gain = 1 - ||D||/S
ever STRICTLY positive for a physically interesting Hamiltonian H = A + B?

Under the paper's scalar-alignment model  Y ~ c X  with X = [B,[B,A]],
Y = [A,[A,B]] (eq:tighten-ratio), the ratio is r(c) = |2-c| / (2+|c|):
r = 1 for all c <= 0, r < 1 for every c > 0.  Real Hamiltonians need not be
scalar-aligned, so we compute the exact ratio ||D||/S directly (spectral norms,
dense matrices) and report a *descriptive* effective alignment
    c_eff = Re<X,Y>_F / <X,X>_F        (Frobenius projection of Y onto X).

Models (spin-1/2 open chains, L = 4, 6, 8, 10):
  * Heisenberg XXZ (Delta = 0.5, 1.0 [= XXX], 2.0), even-bond / odd-bond split;
  * TFIM  H = -J sum ZZ - h sum X  (J = 1, h = 0.5, 1, 2), two splits:
      - even/odd bonds (field shared onto bonds with 1/degree weights so A+B=H),
      - coupling/field:  A = -J sum ZZ,  B = -h sum X;
  * LTFIM (J = 1, h_x = 1, h_z = 0.5), coupling/field split.

Both orderings (A,B) and (B,A) are computed: the Strang assignment
S2(t) = e^{tA/2} e^{tB} e^{tA/2} is a choice, and swapping exchanges the
roles X <-> Y in D and S.

Norms are computed on the Hermitian A, B directly: the paper's skew-adjoint
setting is A -> iA, B -> iB, under which every double commutator picks up a
global factor i^3 = -i, leaving all the norms (and the ratio) unchanged.

Outputs:
  claude/strang_alignment_sweep.csv   -- full results
  claude/strang_alignment_gain.pdf    -- figure: gain% (best ordering) by config, dots colored by L
  stdout                              -- markdown table
"""

import csv
import os
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(HERE, "..", "claude")

I2 = np.eye(2, dtype=complex)
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)


def kron_list(ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


def site_op(P, i, L):
    return kron_list([P if k == i else I2 for k in range(L)])


def bond_op(P, Q, i, L):
    ops = [I2] * L
    ops[i], ops[i + 1] = P, Q
    return kron_list(ops)


def comm(P, Q):
    return P @ Q - Q @ P


def spec_norm(M):
    return float(np.linalg.norm(M, 2))


# ----------------------------------------------------------------------
# Models.  Each builder returns (A, B) with H = A + B.
# ----------------------------------------------------------------------

def heisenberg_eo(L, delta):
    """XXZ chain, even-bond vs odd-bond split."""
    def bond(i):
        return (bond_op(SX, SX, i, L) + bond_op(SY, SY, i, L)
                + delta * bond_op(SZ, SZ, i, L))
    A = sum(bond(i) for i in range(0, L - 1, 2))
    B = sum(bond(i) for i in range(1, L - 1, 2))
    return A, B


def tfim_eo(L, J, h):
    """TFIM, even/odd bond split; field shared onto bonds with 1/degree weights."""
    deg = [2] * L
    deg[0] = deg[-1] = 1

    def bond(i):
        return (-J * bond_op(SZ, SZ, i, L)
                - h * (site_op(SX, i, L) / deg[i] + site_op(SX, i + 1, L) / deg[i + 1]))
    A = sum(bond(i) for i in range(0, L - 1, 2))
    B = sum(bond(i) for i in range(1, L - 1, 2))
    # sanity: A + B must equal the full Hamiltonian
    H = (-J * sum(bond_op(SZ, SZ, i, L) for i in range(L - 1))
         - h * sum(site_op(SX, i, L) for i in range(L)))
    assert np.allclose(A + B, H), "TFIM even/odd split does not sum to H"
    return A, B


def tfim_cf(L, J, h):
    """TFIM, coupling/field split."""
    A = -J * sum(bond_op(SZ, SZ, i, L) for i in range(L - 1))
    B = -h * sum(site_op(SX, i, L) for i in range(L))
    return A, B


def ltfim_cf(L, J, hx, hz):
    """Longitudinal+transverse-field Ising, coupling/field split."""
    A = -J * sum(bond_op(SZ, SZ, i, L) for i in range(L - 1))
    B = -sum(hx * site_op(SX, i, L) + hz * site_op(SZ, i, L) for i in range(L))
    return A, B


CONFIGS = [
    ("Heis XXZ", "Δ=0.5", "even/odd", lambda L: heisenberg_eo(L, 0.5)),
    ("Heis XXX", "Δ=1.0", "even/odd", lambda L: heisenberg_eo(L, 1.0)),
    ("Heis XXZ", "Δ=2.0", "even/odd", lambda L: heisenberg_eo(L, 2.0)),
    ("TFIM", "h=0.5", "even/odd", lambda L: tfim_eo(L, 1.0, 0.5)),
    ("TFIM", "h=1.0", "even/odd", lambda L: tfim_eo(L, 1.0, 1.0)),
    ("TFIM", "h=2.0", "even/odd", lambda L: tfim_eo(L, 1.0, 2.0)),
    ("TFIM", "h=0.5", "ZZ/field", lambda L: tfim_cf(L, 1.0, 0.5)),
    ("TFIM", "h=1.0", "ZZ/field", lambda L: tfim_cf(L, 1.0, 1.0)),
    ("TFIM", "h=2.0", "ZZ/field", lambda L: tfim_cf(L, 1.0, 2.0)),
    ("LTFIM", "hx=1, hz=0.5", "ZZ/field", lambda L: ltfim_cf(L, 1.0, 1.0, 0.5)),
]

LS = [4, 6, 8, 10]


def analyze(A, B):
    """Return metrics for ordering (A,B) and swapped (B,A).

    Ordering (A,B) means S2(t) = e^{tA/2} e^{tB} e^{tA/2}:
      X = [B,[B,A]], Y = [A,[A,B]],  D = X/2 - Y/4,  S = ||X||/2 + ||Y||/4.
    """
    Xc = comm(B, comm(B, A))
    Yc = comm(A, comm(A, B))
    nX, nY = spec_norm(Xc), spec_norm(Yc)
    out = {}
    for tag, (P, nP, Q, nQ) in {
        "AB": (Xc, nX, Yc, nY),   # X-role, Y-role
        "BA": (Yc, nY, Xc, nX),
    }.items():
        D = 0.5 * P - 0.25 * Q
        nD = spec_norm(D)
        S = 0.5 * nP + 0.25 * nQ
        r = nD / S
        c_eff = float(np.real(np.vdot(P, Q)) / np.real(np.vdot(P, P)))
        out[tag] = dict(nD=nD, S=S, ratio=r, gain=1.0 - r, c_eff=c_eff)
    out["nX"], out["nY"] = nX, nY
    return out


def self_test():
    """Check r(c) = |2-c|/(2+|c|) on manufactured scalar-aligned pairs."""
    rng = np.random.default_rng(0)
    M = rng.normal(size=(8, 8)) + 1j * rng.normal(size=(8, 8))
    Xc = M + M.conj().T
    for c in [-1.0, -0.5, 0.0, 6 / 13, 1.0, 2.0, 3.0]:
        Yc = c * Xc
        nD = spec_norm(0.5 * Xc - 0.25 * Yc)
        S = 0.5 * spec_norm(Xc) + 0.25 * spec_norm(Yc)
        r_expect = abs(2 - c) / (2 + abs(c))
        assert abs(nD / S - r_expect) < 1e-12, (c, nD / S, r_expect)
    print("# self-test r(c) = |2-c|/(2+|c|): OK", file=sys.stderr)


def main():
    self_test()
    rows = []
    for model, params, split, builder in CONFIGS:
        for L in LS:
            A, B = builder(L)
            m = analyze(A, B)
            best = "AB" if m["AB"]["ratio"] <= m["BA"]["ratio"] else "BA"
            rows.append(dict(
                model=model, params=params, split=split, L=L,
                nX=m["nX"], nY=m["nY"],
                nD_AB=m["AB"]["nD"], S_AB=m["AB"]["S"],
                ratio_AB=m["AB"]["ratio"], gain_AB=m["AB"]["gain"],
                c_eff_AB=m["AB"]["c_eff"],
                nD_BA=m["BA"]["nD"], S_BA=m["BA"]["S"],
                ratio_BA=m["BA"]["ratio"], gain_BA=m["BA"]["gain"],
                c_eff_BA=m["BA"]["c_eff"],
                best=best,
                gain_best=m[best]["gain"], ratio_best=m[best]["ratio"],
            ))
            print(f"# done {model} {params} {split} L={L}", file=sys.stderr)

    os.makedirs(OUTDIR, exist_ok=True)
    csv_path = os.path.join(OUTDIR, "strang_alignment_sweep.csv")
    with open(csv_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()), lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    print(f"# wrote {csv_path}", file=sys.stderr)

    # ------------------------------------------------------------------
    # Markdown table
    # ------------------------------------------------------------------
    hdr = ("| Model | Params | Split | L | r(A,B) | gain(A,B)% | c_eff(A,B) "
           "| r(B,A) | gain(B,A)% | c_eff(B,A) | best |")
    sep = "|---|---|---|---|---|---|---|---|---|---|---|"
    print(hdr)
    print(sep)
    for r in rows:
        print(f"| {r['model']} | {r['params']} | {r['split']} | {r['L']} "
              f"| {r['ratio_AB']:.4f} | {100*r['gain_AB']:.2f} | {r['c_eff_AB']:+.3f} "
              f"| {r['ratio_BA']:.4f} | {100*r['gain_BA']:.2f} | {r['c_eff_BA']:+.3f} "
              f"| ({r['best'][0]},{r['best'][1]}) |")

    # ------------------------------------------------------------------
    # Figure: horizontal dot plot, gain% (best ordering) per config,
    # dots colored by L (single-hue sequential ramp: L is ordinal).
    # ------------------------------------------------------------------
    plt.rcParams.update({
        "font.size": 9,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.titlesize": 10,
    })
    labels = [f"{m} {p}\n({s})" for (m, p, s, _) in CONFIGS]
    n_cfg = len(CONFIGS)
    # ColorBrewer Blues, 4 steps light -> dark for L = 4, 6, 8, 10
    lcolors = {4: "#9ecae1", 6: "#6baed6", 8: "#3182bd", 10: "#08519c"}
    loffsets = {4: 0.27, 6: 0.09, 8: -0.09, 10: -0.27}

    fig, ax = plt.subplots(figsize=(5.6, 4.6))
    for i, (model, params, split, _) in enumerate(CONFIGS):
        y0 = n_cfg - 1 - i
        for L in LS:
            r = next(x for x in rows
                     if x["model"] == model and x["params"] == params
                     and x["split"] == split and x["L"] == L)
            ax.plot(100 * r["gain_best"], y0 + loffsets[L], "o",
                    ms=5, mec="white", mew=0.5, color=lcolors[L], zorder=3)
    ax.axvline(0, color="0.45", lw=1, zorder=1)
    ax.set_yticks(range(n_cfg))
    ax.set_yticklabels(labels[::-1])
    ax.set_xlabel(r"gain $1 - \|D\|/S$ (%), best ordering")
    ax.set_title("Tighter Strang bound vs sum-of-norms: alignment sweep")
    ax.grid(axis="x", color="0.88", lw=0.7, zorder=0)
    ax.tick_params(axis="y", length=0)
    handles = [plt.Line2D([], [], marker="o", ls="", ms=5, mec="white",
                          mew=0.5, color=lcolors[L], label=f"L = {L}")
               for L in LS]
    ax.legend(handles=handles, loc="lower right", frameon=False,
              title="chain length")
    fig_path = os.path.join(OUTDIR, "strang_alignment_gain.pdf")
    fig.savefig(fig_path, bbox_inches="tight", transparent=True)
    print(f"# wrote {fig_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
