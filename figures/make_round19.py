#!/usr/bin/env python3
"""
make_round19.py

Four plates for the results of round nineteen.

  fig_sexticweil     the least -chi(v,v) of an integral point v of the secant
                     lattice S(0,q) whose Orlov square kappa(v,v) has a
                     nonzero F-Weil part (Omega(v) != 0), for the sixteen
                     totally real cubic fields F_0 of item (LVII), ordered by
                     discriminant, and q = 1, k + alpha, k + 1 + alpha
                     (prop:sexticweilmin, rem:sextictargets).  The numbers
                     are read from the transcript of item (LVIII),
                     code/attack/gaps/sextic/transcripts/s3_weil.log, and the
                     statements of the proposition are asserted on them: the
                     least value 192, at Q(zeta_7)^+ with q = 3 + alpha and
                     nowhere else; the values 296 and 488 for q = 1 (and
                     q = 2 + alpha) over Q(zeta_7)^+ and Q(zeta_9)^+; the
                     twenty cases in which F = F_0(sqrt(-q)) contains an
                     imaginary quadratic field; the range 192 to 7080, and
                     296 to 3872 for q = 1.  One cell per case, shaded on a
                     logarithmic scale, the number printed in it.

  fig_mumfordgroups  the four possible groups M^1 = M cap Sp(V,psi) of the
                     motives of a Mumford fourfold (prop:mumfordmotivic):
                     the chain G < G.A_3 < N < Sp(V,psi) with its indices and
                     the jump of the Lie algebra; for each case the dimension
                     of the algebraic classes in V^{(x)2m}, computed here from
                     the non-crossing pairings (c = 2 for m = 2, c = 5 for
                     m = 3) by counting orbits of A_3 and S_3, and checked
                     against the first fundamental theorem for Sp; whether
                     zeta lies in M^1, whether Det and r_1 are algebraic, and
                     whether the exceptional classes are.  Below, the cyclic
                     permutation zeta of the three tensor factors, the
                     subgroups of N/G ~ S_3 stable under a transitive Galois
                     action, and sp(V,psi) = Lie G + S^2V_1 (x) S^2V_2 (x)
                     S^2V_3, 36 = 3 + 3 + 3 + 27, with the eigenvalues -1
                     and 3 of r_1.

  fig_f3primereach   where (F3') and the Hodge conjecture are known by
                     arguments on zero-cycles and on rationally connected
                     fibrations (prop:f3primesmall, prop:f3primefibration,
                     rem:f3primesharp, rem:f3primefrontier), on the plane of
                     n = dim X and d, the least dimension of a closed subset
                     supporting CH_0(X)_Q (d <= dim R for the maximal
                     rationally connected quotient R).  The equivalences of
                     rem:f3primesharp are the arrows, and the first open
                     cases of rem:f3primefrontier are marked open.

  fig_k3threshold    the threshold of prop:k3powers(ii): for t = 1, ..., 21
                     the least n having a partition with t distinct part
                     sizes, computed here by dynamic programming over the
                     part sizes and checked to be t(t+1)/2; each bar is cut
                     into the parts 1, 2, ..., t of the staircase partition.
                     The Hodge conjecture holds for S^[n] below the bar tops;
                     at the top it is equivalent to the algebraicity of
                     det T(S) on S^t, and t = 21, n = 231 is the very
                     general K3 surface.

Every label is written as  \\node[...] at (x,y) {...};  so that checkfigs.py
can read it back.  The plates use the audited canvas of make_core.py: before a
file is written, the ink is compiled without its labels and rasterised, each
label is measured by TeX, and the generator stops if a label meets ink,
another label, or the box that checkfigs.py estimates for another label, or
if a leader crosses ink, a label or another leader.  Pale fills that carry
text (the cells of a table, the shaded regions of a plane) are drawn as a
background that labels may sit on; every stroke, mark, bar and arrow is ink.

Run:  python3 -B make_round19.py [name ...]     (from the figures directory)
This writes fig_<name>.tex, compiles fig_<name>.pdf and the 200 dpi PNG.
"""
import math
import os
import re
import subprocess
import sys
from fractions import Fraction
from itertools import permutations

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import make_core                                    # noqa: E402
from make_core import Fig, f4                       # noqa: E402

GEN = "make_round19.py"
ROOT = os.path.dirname(HERE)
S3LOG = os.path.join(ROOT, "code", "attack", "gaps", "sextic",
                     "transcripts", "s3_weil.log")
TIP = "-{Stealth[length=4.6pt,width=3.6pt]}"
TIPS2 = "{Stealth[length=4.6pt,width=3.6pt]}-{Stealth[length=4.6pt,width=3.6pt]}"
FN = r"\footnotesize"
SN = r"\scriptsize"


# ================================================================== canvas
class Plate(Fig):
    """The audited canvas of make_core.Fig without a camera, with a
    background layer: pale fills that labels may sit on."""

    def __init__(self, name, blurb):
        super().__init__(name, blurb, cam=None, gen=GEN)
        self.bg = []

    # -- layers ----------------------------------------------------------
    def back(self, s):
        self.bg.append(s if s.endswith("\n") else s + "\n")

    def ink(self, s):
        self.flat(s if s.endswith("\n") else s + "\n")

    def tex(self):
        return (make_core.HEAD.format(name=self.name, gen=self.gen,
                                      blurb=self.blurb)
                + "".join(self.bg) + self.body()
                + "".join(self._leader_tex(Q) for Q in self.leaders)
                + "".join(self._label_tex(L) for L in self.labels)
                + make_core.TAIL)

    # -- primitives ------------------------------------------------------
    def rect(self, x0, y0, x1, y1, fill=None, draw=None, lw=0.4, bg=False,
             rc=None, extra=""):
        opts = ["fill=%s" % fill if fill else "fill=none"]
        opts.append("draw=%s,line width=%.2fpt" % (draw, lw) if draw
                    else "draw=none")
        if rc:
            opts.append("rounded corners=%.1fpt" % rc)
        if extra:
            opts.append(extra)
        s = "  \\path[%s] (%s,%s) rectangle (%s,%s);" % (
            ",".join(opts), f4(x0), f4(y0), f4(x1), f4(y1))
        (self.back if bg else self.ink)(s)

    def poly(self, pts, fill=None, draw=None, lw=0.4, bg=False, extra="",
             closed=True):
        opts = ["fill=%s" % fill if fill else "fill=none"]
        opts.append("draw=%s,line width=%.2fpt" % (draw, lw) if draw
                    else "draw=none")
        if extra:
            opts.append(extra)
        s = "  \\path[%s] %s%s;" % (
            ",".join(opts), " -- ".join("(%s,%s)" % (f4(x), f4(y))
                                       for x, y in pts),
            " -- cycle" if closed else "")
        (self.back if bg else self.ink)(s)

    def seg(self, pts, style, bg=False):
        s = "  \\draw[%s] %s;" % (style, " -- ".join(
            "(%s,%s)" % (f4(x), f4(y)) for x, y in pts))
        (self.back if bg else self.ink)(s)

    def bez(self, a, c1, c2, b, style, bg=False):
        s = ("  \\draw[%s] (%s,%s) .. controls (%s,%s) and (%s,%s) .. "
             "(%s,%s);" % (style, f4(a[0]), f4(a[1]), f4(c1[0]), f4(c1[1]),
                           f4(c2[0]), f4(c2[1]), f4(b[0]), f4(b[1])))
        (self.back if bg else self.ink)(s)

    def disc(self, x, y, r_pt, fill, ring="white", lw=0.5):
        self.ink("  \\path[fill=%s,draw=%s,line width=%.2fpt] (%s,%s) circle "
                 "(%.2fpt);" % (fill, ring, lw, f4(x), f4(y), r_pt))

    def ring(self, x, y, r_pt, draw, lw=0.8, fill="white"):
        self.ink("  \\path[fill=%s,draw=%s,line width=%.2fpt] (%s,%s) circle "
                 "(%.2fpt);" % (fill, draw, lw, f4(x), f4(y), r_pt))

    def hatch(self, x0, y0, x1, y1, color, step=0.11, lw=0.35, bg=True):
        """Diagonal hatching clipped to a rectangle."""
        lines = []
        w, h = x1 - x0, y1 - y0
        k = -h
        while k < w:
            lines.append("(%s,%s) -- (%s,%s)" % (f4(x0 + k), f4(y0),
                                                 f4(x0 + k + h), f4(y1)))
            k += step
        s = ("  \\begin{scope}\\clip (%s,%s) rectangle (%s,%s);"
             "\\draw[%s,line width=%.2fpt] %s;\\end{scope}"
             % (f4(x0), f4(y0), f4(x1), f4(y1), color, lw, " ".join(lines)))
        (self.back if bg else self.ink)(s)

    def text(self, x, y, s, anchor="center", color="PInk", font=FN,
             extra=""):
        return self.label(x, y, s, anchor=anchor, color=color, font=font,
                          extra=extra)


def build(name):
    """pdflatex, the 200 dpi PNG, and the cleanup, in the figures folder."""
    r = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                        "-halt-on-error", name + ".tex"], cwd=HERE,
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.stdout.write(r.stdout[-3000:])
        raise SystemExit("pdflatex failed on %s" % name)
    log = r.stdout
    if re.search(r"(Overfull|Underfull) \\hbox", log):
        raise SystemExit("bad box in %s" % name)
    subprocess.run(["pdftoppm", "-png", "-r", "200", "-singlefile",
                    name + ".pdf", name], cwd=HERE, check=True)
    for ext in (".aux", ".log"):
        try:
            os.remove(os.path.join(HERE, name + ext))
        except OSError:
            pass
    print("   built %s.pdf and %s.png" % (name, name))


# ============================================================ sextic Weil
LINE = re.compile(
    r"^\s+(Q\(zeta_7\)\^\+|Q\(zeta_9\)\^\+|disc \d+)\s+q = (1|\d+\+1 a)\s+"
    r"Nm\(q\) = (\d+)\s+min -chi = (\d+)\s+least -chi with Omega != 0: "
    r"(\d+)\s+\((\d+) classes up to sign\).*K = (.*?)\s*$")


def cubic_disc(a, b, c):
    """Discriminant of x^3 + a x^2 + b x + c."""
    return a * a * b * b - 4 * b ** 3 - 4 * a ** 3 * c - 27 * c * c + 18 * a * b * c


def sextic_data():
    """The forty-eight cases of item (LVIII), read from its transcript, with
    the statements of prop:sexticweilmin asserted on them."""
    disc_of = {"Q(zeta_7)^+": cubic_disc(1, -2, -1),    # x^3+x^2-2x-1: 49
               "Q(zeta_9)^+": cubic_disc(0, -3, 1)}     # x^3-3x+1:    81
    assert disc_of == {"Q(zeta_7)^+": 49, "Q(zeta_9)^+": 81}
    rows = []
    for ln in open(S3LOG):
        m = LINE.match(ln)
        if not m:
            continue
        fld, q, nm, lmin, val, ncl, K = m.groups()
        D = disc_of[fld] if fld in disc_of else int(fld.split()[1])
        kq = 0 if q == "1" else int(q.split("+")[0])
        rows.append(dict(field=fld, disc=D, kq=kq, nm=int(nm), lmin=int(lmin),
                         val=int(val), ncl=int(ncl),
                         K=None if K == "none" else K))
    assert len(rows) == 48, len(rows)
    fields = sorted({r["disc"] for r in rows})
    assert len(fields) == 16
    data = {}
    kfield = {}
    for D in fields:
        mine = [r for r in rows if r["disc"] == D]
        assert len(mine) == 3
        ks = sorted(r["kq"] for r in mine if r["kq"])
        assert len(ks) == 2 and ks[1] == ks[0] + 1, (D, ks)
        kfield[D] = ks[0]
        for r in mine:
            row = 0 if r["kq"] == 0 else (1 if r["kq"] == ks[0] else 2)
            data[(D, row)] = r
    # prop:sexticweilmin, asserted on the transcript
    vals = [r["val"] for r in rows]
    assert min(vals) == 192 and vals.count(192) == 1
    best = data[(49, 2)]
    assert best["val"] == 192 and best["kq"] == 3 and best["nm"] == 13
    assert best["K"] is None and best["ncl"] == 1 and best["lmin"] == 192
    assert data[(81, 2)]["val"] == 256 and data[(81, 2)]["nm"] == 17
    assert data[(81, 2)]["lmin"] == 256
    assert data[(49, 0)]["val"] == 296 and data[(81, 0)]["val"] == 488
    assert data[(49, 1)]["val"] == 296 and data[(81, 1)]["val"] == 488
    assert kfield[49] == 2 and kfield[81] == 2
    assert max(vals) == 7080
    q1 = [data[(D, 0)]["val"] for D in fields]
    assert min(q1) == 296 and max(q1) == 3872
    withK = [(D, r) for (D, r), v in data.items() if v["K"]]
    assert len(withK) == 20
    assert all(data[(D, 0)]["K"] == "Q(sqrt(-1))" for D in fields)
    assert data[(49, 1)]["K"] == data[(81, 1)]["K"] == "Q(sqrt(-1))"
    s3 = sorted((D, r) for (D, r), v in data.items()
                if v["K"] == "Q(sqrt(-3))")
    assert s3 == [(321, 1), (1509, 2)], s3
    assert kfield[321] == 2 and kfield[1509] == 3
    assert (data[(321, 1)]["lmin"], data[(321, 1)]["val"]) == (288, 728)
    assert (data[(1509, 2)]["lmin"], data[(1509, 2)]["val"]) == (4608, 6504)
    # with an imaginary quadratic subfield Q(sqrt(-1)) the lattice minimum 32
    # is attained with Omega = 0; without one, the lattice minimum already
    # has Omega != 0
    for (D, r), v in data.items():
        if v["K"] == "Q(sqrt(-1))":
            assert v["lmin"] == 32 < v["val"]
        if v["K"] is None:
            assert v["lmin"] == v["val"]
    return fields, kfield, data


def fig_sexticweil():
    fields, kfield, data = sextic_data()
    F = Plate("fig_sexticweil",
              "Least -chi of an integral flat secant character with a nonzero "
              "F-Weil part, over the 48 cases of prop:sexticweilmin.")
    CW, RH, GAP = 0.86, 0.68, 0.06
    lo, hi = math.log(192), math.log(7080)

    def pct(v):
        return 9 + 63 * (math.log(v) - lo) / (hi - lo)

    def cell(c, r):
        x0 = c * CW
        y1 = (3 - r) * RH
        return x0, y1 - RH + GAP, x0 + CW - GAP, y1

    # the cells, with the value in each
    for c, D in enumerate(fields):
        for r in range(3):
            v = data[(D, r)]
            x0, y0, x1, y1 = cell(c, r)
            p = pct(v["val"])
            F.rect(x0, y0, x1, y1, fill="PIndigo!%d!white" % round(p), bg=True)
            col = "white" if p > 44 else "PInk"
            F.text((x0 + x1) / 2 + 0.02, (y0 + y1) / 2 - 0.07,
                   "$%d$" % v["val"], color=col)
            if v["K"]:
                s = 0.17
                base = "PTeal" if v["K"] == "Q(sqrt(-1))" else "PClay"
                F.poly([(x0, y1), (x0 + s, y1), (x0, y1 - s)], fill=base)
    # the least value, and the two values for q = 1
    x0, y0, x1, y1 = cell(fields.index(49), 2)
    F.rect(x0 + 0.02, y0 + 0.02, x1 - 0.02, y1 - 0.02, draw="PAmber",
           lw=1.5)
    for D in (49, 81):
        x0, y0, x1, y1 = cell(fields.index(D), 0)
        F.rect(x0 + 0.02, y0 + 0.02, x1 - 0.02, y1 - 0.02, draw="PMag",
               lw=1.1, extra="dash pattern=on 2.2pt off 1.1pt")
    # rows
    names = [r"$q=1$", r"$q=k+\alpha$", r"$q=k+1+\alpha$"]
    for r in range(3):
        x0, y0, x1, y1 = cell(0, r)
        F.text(-0.14, (y0 + y1) / 2, names[r], anchor="east")
    # headers: k, the discriminant, the two cyclic fields
    ytop = 3 * RH
    yk, yd, yn = ytop + 0.24, ytop + 0.64, ytop + 1.07
    for c, D in enumerate(fields):
        xc = c * CW + (CW - GAP) / 2
        F.text(xc, yk, "$%d$" % kfield[D], color="PSlate")
        F.text(xc, yd, "$%d$" % D)
    F.text(-0.14, yk, "$k$", anchor="east", color="PSlate")
    F.text(-0.14, yd, r"$\operatorname{disc}F_{0}$", anchor="east")
    xa = fields.index(49) * CW + 0.10
    xb = fields.index(81) * CW + CW - GAP - 0.10
    yb = yd + 0.27
    F.seg([(xa, yb - 0.07), (xa, yb), (xb, yb), (xb, yb - 0.07)],
          "PInk,line width=0.4pt")
    F.text((xa + xb) / 2, yb + 0.07,
           r"$\QQ(\zeta_{7})^{+}$, $\QQ(\zeta_{9})^{+}$", anchor="south")
    wgrid = 16 * CW - GAP
    F.text(wgrid / 2 + 1.3, yn + 0.02,
           r"the sixteen totally real cubic fields $F_{0}$, by discriminant",
           color="PSlate")

    # the logarithmic scale
    ys, hs = -0.62, 0.20
    xs0, xs1 = 3.0, 10.6
    n = 90
    for i in range(n):
        a = xs0 + (xs1 - xs0) * i / n
        b = xs0 + (xs1 - xs0) * (i + 1) / n
        v = math.exp(lo + (hi - lo) * (i + 0.5) / n)
        F.rect(a, ys - hs / 2, b + 0.004, ys + hs / 2,
               fill="PIndigo!%d!white" % round(pct(v)))
    F.rect(xs0, ys - hs / 2, xs1, ys + hs / 2, draw="PRule", lw=0.35)
    for v in (192, 300, 500, 1000, 2000, 3000, 5000, 7080):
        x = xs0 + (xs1 - xs0) * (math.log(v) - lo) / (hi - lo)
        F.seg([(x, ys - hs / 2), (x, ys - hs / 2 - 0.08)],
              "PInk,line width=0.35pt")
        F.text(x, ys - hs / 2 - 0.15, "$%d$" % v, anchor="north", font=SN)
    F.text(xs0 - 0.35, ys, r"$-\chi(v,v)$, least with $\Omega(v)\neq0$",
           anchor="east")

    # the legend
    yl = -1.62
    PITCH = 0.46
    xl = -2.05
    s = 0.22
    # (a) Q(sqrt(-1))
    F.poly([(xl, yl + s / 2), (xl + s, yl + s / 2), (xl, yl - s / 2)],
           fill="PTeal")
    F.text(xl + s + 0.14, yl,
           r"$F=F_{0}(\sqrt{-q})\supset\QQ(\sqrt{-1})$: every $q=1$, and "
           r"$q=2+\alpha$ over $\QQ(\zeta_{7})^{+}$, $\QQ(\zeta_{9})^{+}$; "
           r"lattice minimum $32$, attained with $\Omega=0$",
           anchor="west")
    yl -= PITCH
    F.poly([(xl, yl + s / 2), (xl + s, yl + s / 2), (xl, yl - s / 2)],
           fill="PClay")
    F.text(xl + s + 0.14, yl,
           r"$F\supset\QQ(\sqrt{-3})$: $q=2+\alpha$ at "
           r"$\operatorname{disc}F_{0}=321$, $q=4+\alpha$ at $1509$; "
           r"lattice minima $288$ and $4608$, attained with $\Omega=0$",
           anchor="west")
    yl -= PITCH
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, draw="PAmber", lw=1.5)
    F.text(xl + s + 0.14, yl,
           r"$192=-\chi(v_{*})$, $v_{*}=v(-1,0,2-\alpha^{2},0)$, over "
           r"$\QQ(\zeta_{7})^{+}$ with $q=3+\alpha$: the least of the "
           r"forty-eight, attained only at $\pm v_{*}$",
           anchor="west")
    yl -= PITCH
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, draw="PMag", lw=1.1,
           extra="dash pattern=on 2.2pt off 1.1pt")
    F.text(xl + s + 0.14, yl,
           r"$q=1$: $296$ and $488$; every class with smaller $-\chi$ lies in "
           r"$\ZZ\operatorname{Re}e^{\sqrt{-1}\,\theta}\oplus"
           r"\ZZ\operatorname{Im}e^{\sqrt{-1}\,\theta}$, where $\Omega=0$",
           anchor="west")
    F.write()
    return F.name


# ====================================================== Mumford groups
def noncrossing_pairings(npts):
    """The non-crossing perfect matchings of 0, ..., npts-1 on a circle."""
    if npts == 0:
        return [()]
    out = []
    for j in range(1, npts, 2):          # 0 is paired with j
        for inner in noncrossing_pairings(j - 1):
            for outer in noncrossing_pairings(npts - j - 1):
                out.append(((0, j),)
                           + tuple((a + 1, b + 1) for a, b in inner)
                           + tuple((a + j + 1, b + j + 1) for a, b in outer))
    return out


def mumford_invariant_dims(m):
    """dim of the invariants in V^{(x)2m} of G, G.A_3, N and Sp(V,psi),
    V = V_1 (x) V_2 (x) V_3 of dimension 8: a basis of the G-invariants is
    the triples of non-crossing pairings, which zeta and the transpositions
    permute, so the A_3- and S_3-invariants are the orbits; the
    Sp-invariants are the (2m-1)!! pairings of psi, independent for
    2m <= 8."""
    c = len(noncrossing_pairings(2 * m))
    basis = [(a, b, d) for a in range(c) for b in range(c) for d in range(c)]
    cyc = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    allp = list(permutations(range(3)))

    def orbits(group):
        seen, k = set(), 0
        for x in basis:
            if x in seen:
                continue
            k += 1
            for g in group:
                seen.add(tuple(x[g[i]] for i in range(3)))
        return k
    sp = 1
    for k in range(2 * m - 1, 0, -2):
        sp *= k
    assert 2 * m <= 8
    dims = (c ** 3, orbits(cyc), orbits(allp), sp)
    # Burnside, as in the text of prop:mumfordmotivic
    assert dims[1] == Fraction(c ** 3 + 2 * c, 3)
    assert dims[2] == Fraction(c ** 3 + 3 * c * c + 2 * c, 6)
    return c, dims


def fig_mumfordgroups():
    c2, d2 = mumford_invariant_dims(2)
    c3, d3 = mumford_invariant_dims(3)
    assert (c2, d2) == (2, (8, 4, 4, 3))
    assert (c3, d3) == (5, (125, 45, 35, 15))
    dim_sp = 8 * 9 // 2
    dim_lie_g = 3 * 3
    assert dim_sp == dim_lie_g + 3 * 3 * 3 == 36
    F = Plate("fig_mumfordgroups",
              "The four possible groups M^1 of the motives of a Mumford "
              "fourfold (prop:mumfordmotivic).")

    # ---------------------------------------------------------- the chain
    ys = {"G": 0.0, "GA": 1.30, "N": 2.60, "Sp": 4.10}
    names = {"G": r"$G=\mathrm{Hg}(X)$", "GA": r"$G\cdot A_{3}$",
             "N": r"$N$", "Sp": r"$\mathrm{Sp}(V,\psi)$"}
    XC, BWD, BH = 0.95, 2.00, 0.60
    order = ["G", "GA", "N", "Sp"]
    for k in order:
        y = ys[k]
        fill = "WOchre" if k == "G" else "WSlate"
        F.rect(XC - BWD / 2, y - BH / 2, XC + BWD / 2, y + BH / 2,
               fill=fill, bg=True, rc=3)
        F.rect(XC - BWD / 2, y - BH / 2, XC + BWD / 2, y + BH / 2,
               draw="POchre" if k == "G" else "PSlate", lw=0.9 if k == "G"
               else 0.6, rc=3)
        F.text(XC, y, names[k])
    notes = {("G", "GA"): r"index $3$",
             ("GA", "N"): r"index $2$",
             ("N", "Sp"): r"$\dim 9\subset\dim 36$"}
    for a, b in zip(order, order[1:]):
        y0, y1 = ys[a] + BH / 2, ys[b] - BH / 2
        F.seg([(XC, y0), (XC, y1)], "PInk,line width=0.7pt")
        F.text(XC + 0.14, (y0 + y1) / 2, notes[(a, b)], anchor="west",
               color="PSlate")
    F.text(XC, ys["Sp"] + 0.72, r"$M^{1}=M\cap\mathrm{Sp}(V,\psi)$",
           anchor="south")

    # ---------------------------------------------------------- the table
    cols = [  # (centre, header, entries by case)
        (4.35, r"$X^{4}$\\$m=2$", ["$%d$" % v for v in d2]),
        (5.60, r"$X^{6}$\\$m=3$", ["$%d$" % v for v in d3]),
        (7.35, r"formula\\$c=2,\ 5$",
         [r"$c^{3}$", r"$(c^{3}+2c)/3$", r"$(c^{3}+3c^{2}+2c)/6$",
          r"$(2m-1)(2m-3)\cdots1$"]),
        (9.45, r"$\zeta\in M^{1}$", ["no", "yes", "yes", "yes"]),
        (11.05, r"$\mathrm{Det}$, $r_{1}$\\algebraic",
         ["yes", "yes", "yes", "no"]),
        (12.75, r"exceptional\\classes\\algebraic",
         ["yes", "no", "no", "no"]),
    ]
    xt0, xt1 = 3.55, 13.65
    ytab = ys["Sp"] + 0.55
    # the band of the case M^1 = G
    F.rect(xt0, ys["G"] - 0.33, xt1, ys["G"] + 0.33, fill="WOchre",
           bg=True)
    for x, head, ent in cols:
        F.text(x, ytab + 0.12, head, anchor="south", extra="align=center")
        for k, e in zip(order, ent):
            colr = "PInk"
            if e == "no":
                colr = "PSlate"
            F.text(x, ys[k], e, color=colr)
    F.seg([(xt0, ytab), (xt1, ytab)], "PInk,line width=0.5pt")
    ygrp = ytab + 1.02
    F.seg([(3.75, ygrp), (8.95, ygrp)], "PInk,line width=0.35pt")
    F.text(6.35, ygrp + 0.08,
           r"$\dim$ of the algebraic classes in $V^{\otimes 2m}$",
           anchor="south")
    F.seg([(xt0, ys["G"] - 0.52), (xt1, ys["G"] - 0.52)],
          "PInk,line width=0.5pt")
    F.text((xt0 + xt1) / 2 - 1.2, ys["G"] - 0.72,
           r"$M^{1}=G$ $\Leftrightarrow$ the Hodge conjecture for every "
           r"$X^{n}$ $\Leftrightarrow$ the two exceptional classes of "
           r"$X\times X$ are algebraic\\"
           r"$\Leftrightarrow$ some algebraic class on some power of $X$ is "
           r"not fixed by $\zeta$",
           anchor="north", extra="align=center")

    # ------------------------------------------------ zeta, three factors
    yz = -2.75
    xs = [-0.55, 0.75, 2.05]
    sw, sh = 0.62, 0.46
    for i, x in enumerate(xs):
        F.rect(x - sw / 2, yz - sh / 2, x + sw / 2, yz + sh / 2,
               fill="WBlue", bg=True, rc=2)
        F.rect(x - sw / 2, yz - sh / 2, x + sw / 2, yz + sh / 2,
               draw="PBlue", lw=0.6, rc=2)
        F.text(x, yz, "$V_{%d}$" % (i + 1))
    for a, b in zip(xs, xs[1:]):
        F.text((a + b) / 2, yz, r"$\otimes$")
    arc = "PIndigo,line width=0.75pt," + TIP
    for a, b in zip(xs, xs[1:]):
        F.bez((a + 0.10, yz + sh / 2 + 0.04), (a + 0.25, yz + 0.78),
              (b - 0.25, yz + 0.78), (b - 0.10, yz + sh / 2 + 0.04), arc)
    F.bez((xs[2] - 0.05, yz - sh / 2 - 0.04), (xs[2] - 0.35, yz - 1.05),
          (xs[0] + 0.35, yz - 1.05), (xs[0] + 0.05, yz - sh / 2 - 0.04), arc)
    F.text(xs[1], yz + 0.86, r"$\zeta$", anchor="south", color="PIndigo")
    F.text(xs[1], yz - 1.02,
           r"$v_{1}\otimes v_{2}\otimes v_{3}\mapsto "
           r"v_{3}\otimes v_{1}\otimes v_{2}$", anchor="north")

    # ------------------------------------- N/G and its stable subgroups
    bx, by = 4.9, -3.55
    pos = {"1": (bx + 0.9, by), "A3": (bx, by + 0.85),
           "t12": (bx + 0.95, by + 0.85), "t13": (bx + 1.75, by + 0.85),
           "t23": (bx + 2.55, by + 0.85), "S3": (bx + 0.9, by + 1.70)}
    txt = {"1": r"$1$", "A3": r"$A_{3}$", "S3": r"$S_{3}$",
           "t12": r"$\langle(12)\rangle$", "t13": r"$\langle(13)\rangle$",
           "t23": r"$\langle(23)\rangle$"}

    def link(a, b, style):
        (xa, ya), (xb, yb) = pos[a], pos[b]
        d = math.hypot(xb - xa, yb - ya)
        ua, ub = 0.22 / (yb - ya) * d, 0.22 / (yb - ya) * d
        F.seg([(xa + (xb - xa) * ua / d, ya + (yb - ya) * ua / d),
               (xb - (xb - xa) * ub / d, yb - (yb - ya) * ub / d)], style)
    solid = "PInk,line width=0.6pt"
    grey = "PSlate!55,line width=0.45pt,dash pattern=on 1.6pt off 1.2pt"
    link("1", "A3", solid)
    link("A3", "S3", solid)
    for t in ("t12", "t13", "t23"):
        link("1", t, grey)
        link(t, "S3", grey)
    for k, (x, y) in pos.items():
        F.text(x, y, txt[k], color="PSlate!80" if k.startswith("t")
               else "PInk")
    corr = {"1": r"$G/G$", "A3": r"$G\cdot A_{3}/G$", "S3": r"$N/G$"}
    for k, s in corr.items():
        x, y = pos[k]
        F.text(x - 0.30 if k != "A3" else x - 0.30, y, s, anchor="east",
               color="PSlate", font=SN)

    # ------------------------------------------- sp(V) = Lie G + 27
    cx0, cw, chh = 8.55, 0.17, 0.34
    yb = -2.85
    for i in range(36):
        a = cx0 + i * cw
        if i < 9:
            fill = "PIndigo!%d!white" % (46 if (i // 3) % 2 == 0 else 30)
        else:
            fill = "PAmber!%d!white" % (44 if i % 2 == 0 else 32)
        F.rect(a, yb - chh / 2, a + cw, yb + chh / 2, fill=fill,
               draw="white", lw=0.4)
    F.rect(cx0, yb - chh / 2, cx0 + 36 * cw, yb + chh / 2, draw="PInk",
           lw=0.45)
    for j in range(3):
        a = cx0 + 3 * j * cw
        F.text(a + 1.5 * cw, yb + chh / 2 + 0.07, "$T_{%d}$" % (j + 1),
               anchor="south", font=SN)

    def bracket(x0, x1, y, up=True):
        h = 0.07 if up else -0.07
        F.seg([(x0, y - h), (x0, y), (x1, y), (x1, y - h)],
              "PInk,line width=0.4pt")
    ylb = yb + chh / 2 + 0.52
    bracket(cx0 + 0.02, cx0 + 9 * cw - 0.02, ylb)
    F.text(cx0 + 4.5 * cw, ylb + 0.07,
           r"$\operatorname{Lie}G$, $\dim 9$", anchor="south")
    bracket(cx0 + 9 * cw + 0.02, cx0 + 36 * cw - 0.02, yb + chh / 2 + 0.16)
    F.text(cx0 + 22.5 * cw, yb + chh / 2 + 0.23,
           r"$S^{2}V_{1}\otimes S^{2}V_{2}\otimes S^{2}V_{3}$, irreducible "
           r"under $G$, $\dim 27$", anchor="south")
    F.text(cx0 + 4.5 * cw, yb - chh / 2 - 0.08, r"$r_{1}=-1$",
           anchor="north", font=SN, color="PIndigo")
    F.text(cx0 + 22.5 * cw, yb - chh / 2 - 0.08, r"$r_{1}=3$",
           anchor="north", font=SN, color="POchre")
    ylo = yb - chh / 2 - 0.50
    bracket(cx0 + 0.02, cx0 + 36 * cw - 0.02, ylo, up=False)
    F.text(cx0 + 18 * cw, ylo - 0.07,
           r"$\mathfrak{sp}(V,\psi)\cong S^{2}V$, $\dim 36$; "
           r"$T_{i}\cong S^{2}V_{i}\otimes{\textstyle\bigwedge^{2}}V_{j}"
           r"\otimes{\textstyle\bigwedge^{2}}V_{k}$", anchor="north")
    F.write()
    return F.name


# ======================================================== K3 threshold
def least_n_with_distinct_sizes(tmax, nmax):
    """least[t] = the least n having a partition with exactly t distinct part
    sizes, by dynamic programming over the part sizes s = 1, ..., nmax: a
    size is used with some multiplicity a >= 1 or not at all."""
    reach = [set() for _ in range(nmax + 1)]    # reach[n] = {t}
    reach[0].add(0)
    for s in range(1, nmax + 1):
        new = [set(x) for x in reach]
        for n0 in range(nmax + 1):
            if not reach[n0]:
                continue
            a = 1
            while n0 + a * s <= nmax:
                for t in reach[n0]:
                    if t < tmax:
                        new[n0 + a * s].add(t + 1)
                a += 1
        reach = new
    least = {}
    for n in range(nmax + 1):
        for t in reach[n]:
            least.setdefault(t, n)
    return least


def fig_k3threshold():
    TM = 21
    least = least_n_with_distinct_sizes(TM, 240)
    N = {t: t * (t + 1) // 2 for t in range(0, TM + 1)}
    for t in range(1, TM + 1):
        assert least[t] == N[t], (t, least[t])
    assert N[21] == 231
    F = Plate("fig_k3threshold",
              "The threshold t(t+1)/2 of prop:k3powers(ii): the least n with a "
              "partition of n having t distinct part sizes, t = 1..21.")
    P, BW, SY = 0.60, 0.40, 0.0255
    NTOP = 256
    W = TM * P
    H = NTOP * SY

    def xc(t):
        return (t - 0.5) * P

    # the open region, as background
    F.rect(0, 0, W, H, fill="WClay!80", bg=True)
    # the bars, cut into the parts 1, ..., t
    for t in range(1, TM + 1):
        a, b = xc(t) - BW / 2, xc(t) + BW / 2
        greyed = t <= 2
        for j in range(1, t + 1):
            y0, y1 = N[j - 1] * SY, N[j] * SY
            if greyed:
                fill = "PSlate!%d!white" % (34 if j % 2 else 20)
            else:
                fill = "PTeal!%d!white" % (52 if j % 2 else 30)
            F.rect(a, y0, b, y1, fill=fill)
        edge = "PSlate!80" if greyed else "PTeal!75!black"
        F.rect(a, 0, b, N[t] * SY, draw=edge, lw=0.45)
    # the threshold N(t) at the top of each bar, with its value
    for t in range(1, TM + 1):
        y = N[t] * SY
        F.disc(xc(t), y, 1.9, "PSlate" if t <= 2 else "PAmber", lw=0.55)
        F.text(xc(t), y + 0.13, "$%d$" % N[t], anchor="south", font=SN,
               color="PSlate" if t <= 2 else "PInk")
    # n = 231: a guide from the axis to the last bar
    y231 = 231 * SY
    F.seg([(0, y231), (xc(TM) - BW / 2 - 0.06, y231)],
          "PAmber,line width=0.55pt,dash pattern=on 2.4pt off 1.6pt")
    F.text(0.25, y231 - 0.13,
           r"very general $S$, so $t=21$: the Hodge conjecture holds for "
           r"$S^{[n]}$ with $n\le230$,\\and for $S^{[231]}$ it is "
           r"equivalent to the "
           r"algebraicity of $\det T(S)$ on $S^{21}$",
           anchor="north west", font=FN, extra="align=left")
    # axes
    F.seg([(0, 0), (W, 0)], "PInk,line width=0.5pt")
    F.seg([(0, 0), (0, H)], "PInk,line width=0.5pt")
    for v in (0, 50, 100, 150, 200, 250):
        y = v * SY
        F.seg([(-0.09, y), (0, y)], "PInk,line width=0.4pt")
        F.text(-0.14, y, "$%d$" % v, anchor="east", font=SN)
    F.seg([(-0.09, y231), (0, y231)], "PAmber,line width=0.5pt")
    F.text(-0.14, y231, "$231$", anchor="east", font=SN, color="PAmber")
    for t in range(1, TM + 1):
        F.seg([(xc(t), 0), (xc(t), -0.08)], "PInk,line width=0.4pt")
        F.text(xc(t), -0.16, "$%d$" % t, anchor="north", font=SN)
    F.text(W / 2, -0.58, r"$t$: the number of distinct part sizes of a "
           r"partition of $n$; for $S$ with $E=\QQ$, $t=\dim T(S)$",
           anchor="north")
    F.text(-0.62, H / 2, r"$n$", anchor="east")
    # legend, below
    yl = -1.28
    xl = 0.0
    s = 0.24
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="PTeal!40!white",
           draw="PTeal!75!black", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$n<t(t+1)/2$: the Hodge conjecture holds for $S^{[n]}$; bar $t$ "
           r"is cut into the parts of the partition $(1,2,\dots,t)$",
           anchor="west")
    yl -= 0.46
    F.disc(xl + s / 2, yl, 1.9, "PAmber", lw=0.55)
    F.text(xl + s + 0.14, yl,
           r"$n=t(t+1)/2$: the Hodge conjecture for $S^{[n]}$ "
           r"$\Leftrightarrow$ $\det T(S)$ on $S^{t}$ is algebraic "
           r"$\Leftrightarrow$ it holds for every $S^{k}$",
           anchor="west")
    yl -= 0.46
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="WClay!80",
           draw="PClay!70", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$n>t(t+1)/2$: open; it follows from the algebraicity of "
           r"$\det T(S)$ on $S^{t}$",
           anchor="west")
    yl -= 0.46
    F.rect(xl, yl - s / 2, xl + s, yl + s / 2, fill="PSlate!28!white",
           draw="PSlate!80", lw=0.45)
    F.text(xl + s + 0.14, yl,
           r"$t\le2$ does not occur for a K3 surface with $E=\QQ$",
           anchor="west")
    F.write()
    return F.name


# ================================================================== main
ALL = ["sexticweil", "mumfordgroups", "f3primereach", "k3threshold"]

if __name__ == "__main__":
    which = sys.argv[1:] or ALL
    for w in which:
        name = globals()["fig_" + w]()
        build(name)
