#!/usr/bin/env python3
"""
make_closure.py

One plate for the closure theorem.

  fig_closure    the route of this paper through the rule set of the closure
                 theorem (setup:rules, thm:closure), drawn as a stack of
                 plates, one per level of the derivation.  Each statement is
                 a small solid on the plate of its level, coloured by its
                 standing: indigo for a statement derived by the rules, clay
                 for an open one, grass for what the paper proves, slate for
                 the bounded criterion (P1), which is equivalent to its own
                 conclusion (thm:p1equivalent) and is drawn apart, closed on
                 itself.

                 Level 1 carries the four families: W(K,n,delta_0) and
                 W(K,n,delta) for the imaginary quadratic fields, and
                 W(F,n,delta_0) and W(F,n,delta) for the CM fields of degree at
                 least four; each carries a grass marker, the base point that
                 thm:everyfamily and thm:cmbasepoint put in it.  The three
                 edges inside the level are prop:descent: descent from delta_0
                 to the other discriminants within each field, and scalar
                 extension from the split families of F to those of K, drawn
                 as an arch.  Level 0 carries (P2) once for each family, as in
                 the rule set; with the edges of prop:descent only the form
                 P2_split under W(F,n,delta_0) is needed, and it is drawn
                 heavy, the other three light.  The secant route enters
                 W(K,n,delta_0) from the left.  Under (P2) for the quadratic
                 fields hang the three pillars of thm:p2numerical,
                 thm:p2support and cor:hhfactor, the constraints on an object
                 of the first form, which thm:p2false shows is never met.
                 Above, the spine runs through the Weil classes of every CM
                 field and the conjecture for abelian varieties to HC, with
                 (F2) entering at level 3 and (F3') and (F3) at level 4;
                 (F3) also carries an edge to the conjecture for abelian
                 varieties, prop:f3ishc.

The nodes and edges are those of the rules of closure_graph.py that the route
uses, with the premises proved in the paper (base point, reduction, orbit
density) drawn as the markers on the families.
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from make_core import Fig, orbit_cam, fit, TIPS, smul, addv  # noqa

DZ = 1.70            # the height between two levels
PX, PY = 7.7, 0.95   # the half sides of a plate
BOX = (0.66, 0.40, 0.20)

COL = {"d": "PIndigo", "o": "PClay", "p": "PGrass", "s": "PSlate"}

# name: (x, y, level, standing)
NODES = {
    "HC":       (0.0, 0.0, 5, "d"),
    "HC_ab":    (0.0, 0.0, 4, "d"),
    "F3p":      (3.9, 0.0, 4, "o"),
    "F3":       (-3.9, 0.0, 4, "o"),
    "weil_all": (0.0, 0.0, 3, "d"),
    "F2":       (3.9, 0.0, 3, "o"),
    "weil_iq":  (-3.0, 0.0, 2, "d"),
    "weil_cm":  (3.0, 0.0, 2, "d"),
    "K1":       (-4.5, 0.0, 1, "d"),
    "K0":       (-1.5, 0.0, 1, "d"),
    "F0":       (1.5, 0.0, 1, "d"),
    "F1":       (4.5, 0.0, 1, "d"),
    "P2K1":     (-4.5, 0.0, 0, "o"),
    "P2K0":     (-1.5, 0.0, 0, "o"),
    "P2F0":     (1.5, 0.0, 0, "o"),
    "P2F1":     (4.5, 0.0, 0, "o"),
    "secant":   (0.0, -0.2, 0, "o"),
    "P1":       (6.7, 0.0, 0, "s"),
}

SPINE = "PIndigo,line width=1.35pt," + TIPS
OPEN = "PClay,line width=1.0pt,dash pattern=on 3pt off 1.8pt," + TIPS
PROP = "PGrass,line width=1.45pt," + TIPS
PROPL = "PGrass!55,line width=0.75pt," + TIPS
DESC = "PIndigo!75!PGrass,line width=1.05pt," + TIPS

# (from, to, style); every edge but the three of prop:descent and the one of
# prop:f3ishc joins adjacent levels
EDGES = [
    ("P2F0", "F0", PROP), ("P2K0", "K0", PROPL), ("P2K1", "K1", PROPL),
    ("P2F1", "F1", PROPL), ("secant", "K0", OPEN),
    ("K0", "weil_iq", SPINE), ("K1", "weil_iq", SPINE),
    ("F0", "weil_cm", SPINE), ("F1", "weil_cm", SPINE),
    ("weil_iq", "weil_all", SPINE), ("weil_cm", "weil_all", SPINE),
    ("weil_all", "HC_ab", SPINE), ("F2", "HC_ab", OPEN),
    ("HC_ab", "HC", SPINE), ("F3p", "HC", OPEN), ("F3", "HC", OPEN),
]


def z_of(lv):
    return lv * DZ


def pos(n):
    x, y, lv, _ = NODES[n]
    return (x, y, z_of(lv))


def top(n):
    x, y, z = pos(n)
    return (x, y, z + BOX[2])


def fig_closure():
    cam = orbit_cam((0.0, 0.0, 2.2 * DZ), 0, 15, R=60)
    F = Fig("fig_closure",
            "The route of this paper through the rule set of the closure "
            "theorem, as a stack of plates, one per level of the derivation.",
            cam, gen="make_closure.py")
    plates = [[(-PX, -PY, z_of(lv)), (PX, -PY, z_of(lv)), (PX, PY, z_of(lv)),
               (-PX, PY, z_of(lv))] for lv in range(6)]
    fit(cam, [p for pl in plates for p in pl] + [(0, 0, -1.3)], 13.4)

    order = 0.0                     # explicit painter order, bottom up

    def put(tikz, depth_bias):
        F.add(1e6 - depth_bias, tikz)

    # the three pillars under (P2) for the quadratic fields
    px, py, pz = pos("P2K1")
    pill = [(-0.9, "PTeal"), (0.0, "PAmber"), (0.9, "PViolet")]
    ptops = []
    for dx, colr in pill:
        lo = (px + dx - 0.09, py - 0.09, pz - 1.15)
        hi = (px + dx + 0.09, py + 0.09, pz - 0.02)
        put(F.prism_tikz(lo, hi, colr), order)
        order += 1
        ptops.append((px + dx, py, pz - 1.15))

    for lv in range(6):
        # the plate
        put("  \\path[fill=PSlate!6,draw=PRule,line width=0.45pt] %s -- cycle;\n"
            % F.path(plates[lv]), order)
        order += 1
        # the edges arriving at this level from below
        for a, b, st in EDGES:
            if NODES[b][2] == lv and NODES[a][2] == lv - 1:
                pa, pb = top(a), pos(b)
                put("  \\draw[%s] %s;\n" % (st, F.path([pa, pb])), order)
                order += 1
        # the nodes of this level
        for n, (x, y, l, st) in NODES.items():
            if l != lv:
                continue
            c = COL[st]
            light = n in ("P2K0", "P2K1", "P2F1")
            lo = (x - BOX[0] / 2, y - BOX[1] / 2, z_of(lv))
            hi = (x + BOX[0] / 2, y + BOX[1] / 2, z_of(lv) + BOX[2])
            put(F.prism_tikz(lo, hi, c, opacity=0.55 if light else None),
                order)
            order += 1
            if lv == 1:
                # the base point of the family, a grass marker on the node
                m0 = (x + 0.10, y - 0.08, z_of(lv) + BOX[2])
                m1 = (x + 0.28, y + 0.10, z_of(lv) + BOX[2] + 0.12)
                put(F.prism_tikz(m0, m1, "PGrass"), order)
                order += 1
        # the edges inside the level
        z = z_of(lv) + BOX[2] / 2
        if lv == 1:
            for a, b in (("K0", "K1"), ("F0", "F1")):
                xa, xb = NODES[a][0] + BOX[0] / 2, NODES[b][0] - BOX[0] / 2
                if xb < xa:
                    xa, xb = NODES[a][0] - BOX[0] / 2, NODES[b][0] + BOX[0] / 2
                put("  \\draw[%s] %s;\n" % (DESC, F.path([(xa + 0.05, 0, z),
                                                          (xb - 0.05, 0, z)])),
                    order)
                order += 1
            # scalar extension, F0 -> K0
            xa = NODES["F0"][0] - BOX[0] / 2 - 0.05
            xb = NODES["K0"][0] + BOX[0] / 2 + 0.05
            put("  \\draw[%s] %s;\n" % (DESC, F.path([(xa, 0, z), (xb, 0, z)])),
                order)
            order += 1
        if lv == 4:
            xa = NODES["F3"][0] + BOX[0] / 2 + 0.05
            xb = NODES["HC_ab"][0] - BOX[0] / 2 - 0.05
            put("  \\draw[%s] %s;\n" % (OPEN, F.path([(xa, 0, z), (xb, 0, z)])),
                order)
            order += 1
    # (P1), closed on itself: a loop in a vertical plane over its node
    qx, qy, qz = pos("P1")
    loop = [(qx + 0.36 * math.cos(t), qy, qz + BOX[2] + 0.40 + 0.34 * math.sin(t))
            for t in [-math.pi / 2 + 0.45 + 2 * math.pi * k / 60 for k in range(52)]]
    put("  \\draw[PSlate,line width=0.9pt,%s] %s;\n" % (TIPS, F.path(loop)),
        order)
    order += 1

    # the edges of prop:descent
    F.alabel(F.P((-3.0, 0.0, z_of(1) + BOX[2] / 2)), r"descent",
             color="PIndigo!75!PGrass", prefer=90, spread=30, rmin=0.08,
             rmax=0.9, free=0.05)
    F.alabel(F.P((3.0, 0.0, z_of(1) + BOX[2] / 2)), r"descent",
             color="PIndigo!75!PGrass", prefer=90, spread=30, rmin=0.08,
             rmax=0.9, free=0.05)
    F.alabel(F.P((0.0, 0.0, z_of(1) + BOX[2] / 2)), r"scalar extension",
             color="PIndigo!75!PGrass", prefer=90, spread=30, rmin=0.08,
             rmax=0.9, free=0.05)
    # labels: the nodes
    lab = [
        ("HC", r"$\mathbf{HC}$", "PIndigo", 0),
        ("weil_all", r"Weil classes", "PIndigo", 150),
        ("HC_ab", r"abelian varieties", "PIndigo", 30),
        ("F3p", r"(F3$'$)", "PClay", 0),
        ("F3", r"(F3)", "PClay", 180),
        ("F2", r"(F2)", "PClay", 0),
        ("weil_iq", r"$[K:\QQ]=2$", "PIndigo", 180),
        ("weil_cm", r"$[F:\QQ]\ge4$", "PIndigo", 0),
        ("K0", r"$\mathbf{W}(K,n,\delta_{0})$", "PIndigo", 210),
        ("K1", r"$\mathbf{W}(K,n,\delta)$", "PIndigo", 160),
        ("F0", r"$\mathbf{W}(F,n,\delta_{0})$", "PIndigo", -30),
        ("F1", r"$\mathbf{W}(F,n,\delta)$", "PIndigo", 20),
        ("P2F0", r"$\mathrm{P2}_{\mathrm{split}}$", "PClay", -20),
        ("P2K0", r"(P2)", "PClay!70", 150),
        ("P2K1", r"(P2)", "PClay!70", 20),
        ("P2F1", r"(P2)", "PClay!70", -20),
        ("secant", r"secant route", "PClay", -60),
        ("P1", r"(P1)", "PSlate", 180),
    ]
    for n, t, c, pr in lab:
        x, y, z = pos(n)
        i = F.alabel(F.P((x, y, z + BOX[2] / 2)), t, color=c, prefer=pr,
                     spread=180, rmin=0.30, rmax=2.0, free=0.22)
        if "\\\\" in t:
            F.labels[i]["extra"] = "align=left"
    # the pillars
    for p, t, c, pr in zip(ptops, (r"$\dim\operatorname{Ext}^{2}=2n(2n-1)$",
                                   r"$\operatorname{codim}<n$",
                                   r"$\bigwedge^{*}P\oplus\bigwedge^{*}Q$"),
                           ("PTeal", "PAmber", "PViolet"), (180, -90, 0)):
        F.alabel(F.P(p), t, color=c, prefer=pr, spread=15,
                 rmin=0.35 if pr == -90 else 0.12, rmax=2.5, free=0.05)
    # the key, above the top plate on the left
    q = F.P((-PX, PY, z_of(5)))
    x0, y0 = q[0] + 0.25, q[1] + 0.55
    for dx, c, t in ((0.0, "PIndigo", "derived"), (1.85, "PClay", "open"),
                     (3.35, "PGrass", "proved here")):
        F.swatch(x0 + dx, y0, c, t, font=r"\footnotesize")
    F.write()


if __name__ == "__main__":
    fig_closure()
