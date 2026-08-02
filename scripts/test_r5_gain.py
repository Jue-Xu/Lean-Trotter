#!/usr/bin/env python3
"""S4 norm-of-difference gain test: ||R5|| vs sum_k gamma_k ||C_k||.

Tests the comparison discussed in lean4trotter/apd_tighter_strang.tex: the
paper's S4 extension of the norm-of-difference idea
would put ||R5|| (the norm of the single quintic BCH residual) in the bound
instead of the triangle-inequality sum sum_k gamma_k ||C_k||; "we have not
exhibited a specific H = A + B for which ||R5|| falls below
sum_k gamma_k ||C_k|| by a non-negligible margin".

R5 = sum_k beta_k(p) C_k over the 8 Childs commutators
  C1 = [A,[A,[A,[B,A]]]]   C5 = [B,[A,[A,[B,A]]]]
  C2 = [A,[A,[B,[B,A]]]]   C6 = [B,[A,[B,[B,A]]]]
  C3 = [A,[B,[A,[B,A]]]]   C7 = [B,[B,[A,[B,A]]]]
  C4 = [A,[B,[B,[B,A]]]]   C8 = [B,[B,[B,[B,A]]]]
with the CAS-computed projection coefficients (gamma3 = gamma7 = 0 gauge;
see scripts/compute_bch_prefactors.py and the docstring of
`bchTightPrefactors` in LieTrotter/Suzuki4ViaBCH.lean):

  beta1(p) = 127p^2/144000 + 13p/36000 - 1/24000
  beta2(p) =    p^2/12000  + 13p/6000  - 1/4000
  beta3(p) = 0
  beta4(p) = -61p^2/9000   + 13p/3000  - 1/2000
  beta5(p) =  31p^2/9000   - 13p/18000 + 1/12000
  beta6(p) =  31p^2/3000   - 13p/6000  + 1/4000
  beta7(p) = 0
  beta8(p) =    p^2/18000  + 13p/9000  - 1/6000

at the Suzuki point p* = 1/(4 - 4^(1/3)).

Internal consistency checks (abort on failure):
  (i)   ceil(|beta_k(p*)| * 10^6) equals the Lean gamma_k * 10^6
        (260, 663, 0, 132, 376, 1128, 0, 442) -- ties this script to the
        machine-checked `bchTightPrefactors`;
  (ii)  ||R5|| <= sum |beta_k| ||C_k|| <= sum gamma_k ||C_k|| numerically
        in every row (triangle inequality + ceiling property).

Note all beta_k(p*) >= 0, so sum |beta_k|||C_k|| = sum beta_k ||C_k||: the
norm-of-difference gain at S4 order comes entirely from OPERATOR-level
cancellation among the C_k, not from sign cancellation of coefficients.

Models and builders are imported from scripts/sweep_strang_alignment.py,
whose outputs were independently cross-checked
(scripts/verify_strang_alignment_independent.py).

Outputs:
  claude/s4_r5_gain.csv, claude/s4_r5_gain.pdf, markdown table on stdout.
"""

import csv
import os
import sys
from fractions import Fraction

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUTDIR = os.path.join(HERE, "..", "claude")

from sweep_strang_alignment import (  # noqa: E402
    heisenberg_eo, tfim_eo, tfim_cf, ltfim_cf, comm, spec_norm,
)

# The matrix computations use float64.  The coefficient-ceiling check below is
# independent of floating point: it uses exact Fraction interval arithmetic on
# the Lean-proved enclosure 41449/100000 < p* < 41450/100000.
P_STAR = 1.0 / (4.0 - 4.0 ** (1.0 / 3.0))
P_LO = Fraction(41449, 100000)
P_HI = Fraction(41450, 100000)

BETA_COEFFS = [
    (Fraction(127, 144000), Fraction(13, 36000), -Fraction(1, 24000)),
    (Fraction(1, 12000), Fraction(13, 6000), -Fraction(1, 4000)),
    (Fraction(0), Fraction(0), Fraction(0)),
    (-Fraction(61, 9000), Fraction(13, 3000), -Fraction(1, 2000)),
    (Fraction(31, 9000), -Fraction(13, 18000), Fraction(1, 12000)),
    (Fraction(31, 3000), -Fraction(13, 6000), Fraction(1, 4000)),
    (Fraction(0), Fraction(0), Fraction(0)),
    (Fraction(1, 18000), Fraction(13, 9000), -Fraction(1, 6000)),
]


def betas(p):
    return [a * p**2 + b * p + c for a, b, c in BETA_COEFFS]


BETA = [float(beta) for beta in betas(P_STAR)]
GAMMA = [260e-6, 663e-6, 0.0, 132e-6, 376e-6, 1128e-6, 0.0, 442e-6]
ALPHA = [0.0047, 0.0057, 0.0046, 0.0074, 0.0097, 0.0097, 0.0173, 0.0284]

# Commutator words X1,X2,X3 wrapping the innermost [B,A].
WORDS = ["AAA", "AAB", "ABA", "ABB", "BAA", "BAB", "BBA", "BBB"]


def check_ceilings():
    """Certify the Lean gamma grid using exact rational interval arithmetic."""
    lean_grid = [260, 663, 0, 132, 376, 1128, 0, 442]
    p2_lo, p2_hi = P_LO**2, P_HI**2
    for k, ((a, b, c), g) in enumerate(zip(BETA_COEFFS, lean_grid), 1):
        a_terms = (a * p2_lo, a * p2_hi)
        b_terms = (b * P_LO, b * P_HI)
        beta_lo = min(a_terms) + min(b_terms) + c
        beta_hi = max(a_terms) + max(b_terms) + c
        if g == 0:
            assert beta_lo == 0 == beta_hi, f"beta{k} is not identically zero"
        else:
            assert Fraction(g - 1, 10**6) < beta_lo
            assert beta_hi <= Fraction(g, 10**6)
    print("# check (i): ceilings of |beta_k(p*)| match Lean bchTightPrefactors: OK",
          file=sys.stderr)


def childs_comms(A, B):
    inner = comm(B, A)
    ops = {"A": A, "B": B}
    out = []
    for w in WORDS:
        M = inner
        for ch in reversed(w):
            M = comm(ops[ch], M)
        out.append(M)
    return out


def analyze(A, B):
    Cs = childs_comms(A, B)
    nC = [spec_norm(C) for C in Cs]
    R5 = sum(b * C for b, C in zip(BETA, Cs))
    nR5 = spec_norm(R5)
    abs_beta_sum = sum(abs(b) * n for b, n in zip(BETA, nC))
    gamma_sum = sum(g * n for g, n in zip(GAMMA, nC))
    alpha_sum = sum(a * n for a, n in zip(ALPHA, nC))
    # (ii) triangle inequality + ceiling property, numerically
    assert nR5 <= abs_beta_sum * (1 + 1e-9), (nR5, abs_beta_sum)
    assert abs_beta_sum <= gamma_sum * (1 + 1e-9), (abs_beta_sum, gamma_sum)
    return dict(
        nR5=nR5, abs_beta_sum=abs_beta_sum, gamma_sum=gamma_sum,
        alpha_sum=alpha_sum,
        r_op=nR5 / abs_beta_sum,       # operator-level cancellation alone
        r_gamma=nR5 / gamma_sum,       # ||R5|| vs the Level-3 gamma bound
        r_alpha=gamma_sum / alpha_sum, # gamma bound vs Childs bound
    )


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

LS = [4, 6, 8]


def main():
    check_ceilings()
    rows = []
    for model, params, split, builder in CONFIGS:
        for L in LS:
            A, B = builder(L)
            for tag, (P, Q) in {"AB": (A, B), "BA": (B, A)}.items():
                m = analyze(P, Q)
                rows.append(dict(model=model, params=params, split=split,
                                 L=L, order=tag, **m))
            print(f"# done {model} {params} {split} L={L}", file=sys.stderr)

    os.makedirs(OUTDIR, exist_ok=True)
    csv_path = os.path.join(OUTDIR, "s4_r5_gain.csv")
    with open(csv_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()), lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    print(f"# wrote {csv_path}", file=sys.stderr)

    print("| Model | Params | Split | L | order | ‖R₅‖/Σγ‖C‖ | gain% "
          "| op-cancel ‖R₅‖/Σβ‖C‖ | Σγ‖C‖/Σα‖C‖ |")
    print("|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['model']} | {r['params']} | {r['split']} | {r['L']} "
              f"| {r['order']} | {r['r_gamma']:.4f} | {100*(1-r['r_gamma']):.1f} "
              f"| {r['r_op']:.4f} | {r['r_alpha']:.4f} |")

    # Figure: gain of ||R5|| over the gamma bound, per config (best ordering).
    plt.rcParams.update({
        "font.size": 9,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.titlesize": 10,
    })
    labels = [f"{m} {p}\n({s})" for (m, p, s, _) in CONFIGS]
    lcolors = {4: "#9ecae1", 6: "#3182bd", 8: "#08519c"}
    loffsets = {4: 0.22, 6: 0.0, 8: -0.22}
    n_cfg = len(CONFIGS)
    fig, ax = plt.subplots(figsize=(5.6, 4.6))
    for i, (model, params, split, _) in enumerate(CONFIGS):
        y0 = n_cfg - 1 - i
        for L in LS:
            best = min((r for r in rows
                        if r["model"] == model and r["params"] == params
                        and r["split"] == split and r["L"] == L),
                       key=lambda r: r["r_gamma"])
            ax.plot(100 * (1 - best["r_gamma"]), y0 + loffsets[L], "o",
                    ms=5, mec="white", mew=0.5, color=lcolors[L], zorder=3)
    ax.axvline(0, color="0.45", lw=1, zorder=1)
    ax.set_yticks(range(n_cfg))
    ax.set_yticklabels(labels[::-1])
    ax.set_xlabel(r"gain $1 - \|R_5\|/\sum_k \gamma_k\|C_k\|$ (%), best ordering")
    ax.set_title(r"$S_4$ norm-of-difference gain over the Level-3 $\gamma$ bound")
    ax.grid(axis="x", color="0.88", lw=0.7, zorder=0)
    ax.tick_params(axis="y", length=0)
    handles = [plt.Line2D([], [], marker="o", ls="", ms=5, mec="white",
                          mew=0.5, color=lcolors[L], label=f"L = {L}")
               for L in LS]
    ax.legend(handles=handles, loc="lower right", frameon=False,
              title="chain length")
    fig_path = os.path.join(OUTDIR, "s4_r5_gain.pdf")
    fig.savefig(fig_path, bbox_inches="tight", transparent=True)
    print(f"# wrote {fig_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
