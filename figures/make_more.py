#!/usr/bin/env python3
"""
make_more.py

Two plates in three dimensions.

  fig_escape     the Boolean lattice of the three hypotheses of the
                 proposition on which hypotheses Markman's construction
                 escapes, drawn as a genuine unit cube standing on its
                 vertex: the vertex (i,j,k) is the set S of hypotheses (Hm)
                 with the m-th coordinate 1, its height is |S|/sqrt(3), each
                 edge adds one hypothesis and is coloured by it, and the
                 shaded face is the set of positions where (H1) holds, which
                 is where the divisor obstruction already binds.  The
                 hidden vertex and its three edges are dashed.

  fig_lightcone  the Kuga-Satake picture for b = 3: the form
                 q = x^2 + y^2 - z^2 of signature (2,1), its null cone, the
                 two sheets of the hyperboloid q = -1, the positive plane
                 P = {z = 0} with its unit circle and an orthonormal basis
                 e_1, e_2, and the line P-perp meeting the upper sheet in
                 w_P = (0,0,1).  A second positive plane P' = w'-perp, with
                 w' = (sinh s, 0, cosh s) and s = arctanh(1/2), is drawn with
                 its unit ellipse and its normal line, to show the
                 bijection between positive planes and points of one sheet.

Both use the painter's-algorithm renderer of render3d.py, and both place
their labels with the Plate class of make_diagrams.py, which keeps every
label off the ink of the drawing and off every other label.
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from render3d import Camera, Scene, addv, smul                  # noqa: E402
from make_diagrams import (Plate, compile_plate, proj, TIP, soften,  # noqa
                           orbit_eye)

GEN = "make_more.py"


# =================================================================== escape
def fig_escape():
    """The eight positions a secant construction can occupy."""
    r, h = math.sqrt(2.0 / 3.0), 1.0 / math.sqrt(3.0)
    phi = [-90.0, 30.0, 150.0]
    E = [(r * math.cos(math.radians(f)), r * math.sin(math.radians(f)), h)
         for f in phi]
    tgt = (0.0, 0.0, 0.87)
    az, el = -38.0, 8.0
    cam = Camera(eye=orbit_eye(tgt, 30.0, az, el), target=tgt, focal=30.0,
                 scale=3.55)
    sc = Scene(cam)
    pl = Plate("fig_escape", GEN,
               "The eight positions a secant construction can occupy, as the "
               "vertices of a cube standing on its empty vertex.",
               thresh=244)

    def V(i, j, k):
        p = (0.0, 0.0, 0.0)
        for c, e in zip((i, j, k), E):
            if c:
                p = addv(p, e)
        return p

    def face(fixed_axis, val):
        def f(u, v):
            c = [0.0, 0.0, 0.0]
            others = [a for a in range(3) if a != fixed_axis]
            c[fixed_axis] = val
            c[others[0]], c[others[1]] = u, v
            p = (0.0, 0.0, 0.0)
            for ci, e in zip(c, E):
                p = addv(p, smul(ci, e))
            return p
        return f

    # the face (H1) holds, shaded; the other five faintly, for solidity
    sc.surface(face(0, 1.0), (0, 1), (0, 1), 12, 12, base="PClay",
               opacity=0.36, ambient=0.40, diffuse=0.40)
    for ax, val in ((1, 1.0), (2, 1.0), (0, 0.0), (1, 0.0), (2, 0.0)):
        sc.surface(face(ax, val), (0, 1), (0, 1), 8, 8, base="PSlate",
                   opacity=0.10, ambient=0.66, diffuse=0.26)

    col = ["PClay", "PIndigo", "PGrass"]
    # the hidden vertex is where the three faces turned away meet
    view = (math.cos(math.radians(el)) * math.cos(math.radians(az)),
            math.cos(math.radians(el)) * math.sin(math.radians(az)),
            math.sin(math.radians(el)))
    hidden = tuple(0 if sum(a * b for a, b in zip(e, view)) > 0 else 1
                   for e in E)
    verts = [(i, j, k) for i in range(2) for j in range(2) for k in range(2)]
    for v in verts:
        for a in range(3):
            if v[a] == 0:
                w = list(v)
                w[a] = 1
                w = tuple(w)
                if hidden in (v, w):
                    st = "%s!70,line width=0.8pt,dash pattern=on 2.2pt off 1.8pt" \
                        % col[a]
                else:
                    st = "%s,line width=1.25pt" % col[a]
                sc.polyline([V(*v), V(*w)], st, priority=2)
    for v in verts:
        if v == (1, 1, 1):
            st = "circle,fill=PClay,draw=white,line width=0.7pt,inner sep=2.8pt"
        elif v == (0, 0, 0):
            st = "circle,fill=PTeal,draw=white,line width=0.7pt,inner sep=2.8pt"
        elif v == hidden:
            st = "circle,fill=white,draw=PSlate!70,line width=0.7pt,inner sep=1.8pt"
        else:
            st = "circle,fill=white,draw=PInk!80,line width=0.9pt,inner sep=2.0pt"
        sc.dot3(V(*v), st, priority=5)
    pl.add(sc.emit())

    # the grading |S|, read against the heights of the vertices
    xa = min(proj(cam, V(*v))[0] for v in [(1, 0, 0), (0, 1, 0), (0, 0, 1),
                                          (1, 1, 0), (1, 0, 1), (0, 1, 1)])
    xa -= 1.40
    ys = [proj(cam, (0.0, 0.0, m * h))[1] for m in range(4)]
    pl.add("  \\draw[PSlate,line width=0.45pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (xa, ys[0], xa, ys[3]))
    for m in range(4):
        pl.add("  \\draw[PSlate,line width=0.45pt] (%.3f,%.3f) -- (%.3f,%.3f);\n"
               % (xa, ys[m], xa + 0.12, ys[m]))
        pl.put(xa - 0.10, ys[m], r"$|S|=%d$" % m, color="PSlate",
               font=r"\footnotesize", anchor="e")

    def name(v):
        s = [str(a + 1) for a in range(3) if v[a]]
        return r"$\{%s\}$" % ",".join(s)

    order = [(1, 1, 1), (0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
             (1, 1, 0), (1, 0, 1), (0, 1, 1)]
    for v in order:
        if v == (1, 1, 1):
            txt, c, d = r"$\{1,2,3\}$: all three hold", "PClay", [90, 60, 120]
        elif v == (0, 0, 0):
            txt, c, d = r"$\varnothing$: Markman's construction", "PTeal", \
                [-90, -60, -120]
        else:
            txt, c, d = name(v), "PInk", None
        pl.label(proj(cam, V(*v)), txt, color=c, dirs=d, rmin=0.12,
                 rmax=2.2, skip=0.14)
    for a, t in enumerate((r"$+$(H1)", r"$+$(H2)", r"$+$(H3)")):
        mid = smul(0.5, E[a])
        pl.label(proj(cam, mid), t, color=col[a], font=r"\footnotesize",
                 rmin=0.06, rmax=1.5, skip=0.08)
    # the shaded face: a leader from just inside its outer edge
    fp = face(0, 1.0)(0.45, 0.90)
    pl.label(proj(cam, fp), r"(H1) holds", color="PClay",
             dirs=[150, 180, 120], rmin=0.3, rmax=2.0, skip=0.30)

    # (b): the orbit of a Weil class spans the plane.  K = Q(i), n = 2, the
    # plane W(A) (x) R identified with C by alpha -> 1; iota(tau)^* acts by
    # tau^{2n} = N(tau)^n (tau/conj tau)^n, so the directions of the orbit
    # are the points (tau/conj tau)^2 of the unit circle.
    xs = [proj(cam, V(*v))[0] for v in verts]
    ysv = [proj(cam, V(*v))[1] for v in verts]
    cx, cy, rad = max(xs) + 3.75, 0.5 * (min(ysv) + max(ysv)) - 0.25, 1.75
    pl.add("  \\draw[PSlate!60,line width=0.35pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, cx - rad - 0.45, cy, cx + rad + 0.55, cy))
    pl.add("  \\draw[PSlate!60,line width=0.35pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, cx, cy - rad - 0.45, cx, cy + rad + 0.55))
    pl.add("  \\draw[PIndigo,line width=0.8pt] (%.3f,%.3f) circle (%.3f);\n"
           % (cx, cy, rad))
    pl.add("  \\draw[PTeal,line width=1.1pt,dash pattern=on 3pt off 2pt] "
           "(%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (cx - rad - 0.30, cy - 0.0, cx + rad + 0.30, cy))
    seen = []
    for a in range(0, 9):
        for b in range(-8, 9):
            if a * a + b * b == 0 or a * a + b * b > 30 or math.gcd(a, b) != 1:
                continue
            ang = 4 * math.atan2(b, a)
            if any(abs(math.remainder(ang - t, 2 * math.pi)) < 1e-9
                   for t in seen):
                continue
            seen.append(ang)
            px, py = cx + rad * math.cos(ang), cy + rad * math.sin(ang)
            pl.add("  \\node[circle,fill=PIndigo,draw=white,line width=0.4pt,"
                   "inner sep=1.3pt] at (%.3f,%.3f) {};\n" % (px, py))
    pl.add("  \\node[circle,fill=PTeal,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % (cx + rad, cy))
    pl.add("  \\node[circle,fill=PTeal,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % (cx - rad, cy))
    pl.add("  \\node[circle,fill=PInk,inner sep=1.0pt] at (%.3f,%.3f) {};\n"
           % (cx, cy))
    ang = 4 * math.atan2(1, 2)
    pl.add("  \\draw[PIndigo,line width=0.6pt,%s] (%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (TIP, cx, cy, cx + (rad - 0.07) * math.cos(ang),
              cy + (rad - 0.07) * math.sin(ang)))
    pl.label((cx + rad, cy), r"$\alpha$", color="PTeal", dirs=[-60, -30],
             rmax=0.8, skip=0.1)
    pl.label((cx - rad, cy), r"$\iota(1+i)^{*}\alpha$", color="PTeal",
             font=r"\footnotesize", dirs=[-120, -150, -100], rmax=0.9,
             skip=0.1, penalty=2.0)
    pl.label((cx + rad * math.cos(ang), cy + rad * math.sin(ang)),
             r"$\iota(2+i)^{*}\alpha$", color="PIndigo", font=r"\footnotesize",
             dirs=[150, 120, 180], rmax=0.9, skip=0.1)
    pl.label((cx + rad + 0.30, cy), r"$\QQ\alpha$", color="PTeal",
             dirs=[30, 60], rmax=0.5)
    pl.put(cx, cy + rad + 0.95, r"$\HW(A)\otimes\RR$, $K=\QQ(i)$, $n=2$",
           color="PInk")
    pl.put(cx - rad - 0.55, cy + rad + 0.95, r"(b)", color="PInk", anchor="e")
    pl.put(xa - 1.20, cy + rad + 0.95, r"(a)", color="PInk", anchor="e")
    pl.build()
    compile_plate("fig_escape")


# ================================================================ lightcone
def fig_lightcone():
    """The null cone of q = x^2 + y^2 - z^2, the two sheets of q = -1, and
    positive planes with their normal lines."""
    tgt = (0.05, 0.0, 0.0)
    cam = Camera(eye=orbit_eye(tgt, 16.0, -50.0, 16.0), target=tgt,
                 focal=12.0, scale=2.80)
    sc = Scene(cam)
    pl = Plate("fig_lightcone", GEN,
               "The null cone of a form of signature (2,1), the two sheets of "
               "q = -1, and positive planes with their normal lines.",
               thresh=249)
    R = 1.60                      # height of the drawn cone
    RH = math.sqrt(R * R - 1.0)   # radius of the drawn sheet at the same height
    s = math.atanh(0.5)
    ch, sh = math.cosh(s), math.sinh(s)
    w2 = (sh, 0.0, ch)            # the point of the sheet for P'
    e1p = (ch, 0.0, sh)           # an orthonormal basis of P' = w2-perp
    e2p = (0.0, 1.0, 0.0)

    # the null cone q = 0
    for sgn in (1, -1):
        sc.surface(lambda t, rr, sgn=sgn: (rr * math.cos(t), rr * math.sin(t),
                                           sgn * rr),
                   (0, 2 * math.pi), (0.0, R), 48, 10, base="PBlue",
                   opacity=0.22, ambient=0.50, diffuse=0.40)
        for m in range(16):
            t = 2 * math.pi * m / 16
            sc.polyline([(0, 0, 0), (R * math.cos(t), R * math.sin(t),
                                     sgn * R)],
                        "soft,PBlue!55,line width=0.3pt", priority=1)
        sc.curve(lambda t, sgn=sgn: (R * math.cos(t), R * math.sin(t),
                                     sgn * R), (0, 2 * math.pi), 96,
                 "soft,PBlue!80,line width=0.6pt", priority=2, chunk=2)
    # the two sheets of q = -1; the upper one is the period domain
    for sgn, op in ((1, 0.62), (-1, 0.20)):
        sc.surface(lambda t, rr, sgn=sgn: (rr * math.cos(t), rr * math.sin(t),
                                           sgn * math.sqrt(1 + rr * rr)),
                   (0, 2 * math.pi), (0.0, RH), 48, 10, base="POchre",
                   opacity=op, ambient=0.40, diffuse=0.50)
        for rr in (0.45, 0.9):
            zz = sgn * math.sqrt(1 + rr * rr)
            sc.curve(lambda t, rr=rr, zz=zz: (rr * math.cos(t),
                                              rr * math.sin(t), zz),
                     (0, 2 * math.pi), 64,
                     "soft,POchre!80!black,line width=0.3pt", priority=2,
                     chunk=2)
        sc.curve(lambda t, sgn=sgn: (RH * math.cos(t), RH * math.sin(t),
                                     sgn * R), (0, 2 * math.pi), 96,
                 "soft,POchre!85!black,line width=0.6pt", priority=2, chunk=2)
    # the positive plane P = {z = 0}, its unit circle, e_1 and e_2
    L = 1.95
    sc.surface(lambda u, v: (u, v, 0.0), (-L, L), (-L, L), 12, 12,
               base="PClay", opacity=0.16, ambient=0.66, diffuse=0.26)
    corners = [(-L, -L), (L, -L), (L, L), (-L, L)]
    for a, b in zip(corners, corners[1:] + corners[:1]):
        sc.polyline([(a[0], a[1], 0), (b[0], b[1], 0)],
                    "soft,PClay!70,line width=0.4pt", priority=1)
    sc.curve(lambda t: (math.cos(t), math.sin(t), 0.0), (0, 2 * math.pi), 96,
             "PClay,line width=1.0pt", priority=3, chunk=2)
    sc.polyline([(0, 0, 0), (1, 0, 0)], "PClay!80!black,line width=1.1pt," + TIP,
                priority=4)
    sc.polyline([(0, 0, 0), (0, 1, 0)], "PClay!80!black,line width=1.1pt," + TIP,
                priority=4)
    # the second positive plane P', its unit ellipse and its normal line
    sc.curve(lambda t: addv(smul(math.cos(t), e1p), smul(math.sin(t), e2p)),
             (0, 2 * math.pi), 96, "PGrass,line width=0.9pt", priority=3,
             chunk=2)
    sc.surface(lambda u, v: addv(smul(u, e1p), smul(v, e2p)), (-1.0, 1.0),
               (-1.0, 1.0), 10, 10, base="PGrass", opacity=0.12, ambient=0.70,
               diffuse=0.2,
               cull=lambda Q: all(((q[0] / ch) ** 2 + q[1] ** 2) <= 1.0001
                                  for q in Q))
    k = 2.05 / ch
    sc.polyline([smul(-0.30 * k, w2), smul(k, w2)],
                "PGrass!85!black,line width=0.9pt", priority=3)
    # the line P-perp
    sc.polyline([(0, 0, -2.05), (0, 0, 2.05)], "PInk!80,line width=0.9pt",
                priority=3)
    sc.dot3((0, 0, 1.0), "circle,fill=POchre!80!black,draw=white,"
            "line width=0.6pt,inner sep=2.1pt", priority=6)
    sc.dot3(w2, "circle,fill=PGrass,draw=white,line width=0.6pt,"
            "inner sep=2.1pt", priority=6)
    sc.dot3((0, 0, 0), "circle,fill=PInk,inner sep=1.3pt,draw=none",
            priority=6)
    pl.add(soften(sc.emit()))

    def extreme(pts, key):
        return max(pts, key=lambda p: key(proj(cam, p)))

    rim = [(R * math.cos(t), R * math.sin(t), R)
           for t in [2 * math.pi * i / 360 for i in range(360)]]
    hrim = [(RH * math.cos(t), RH * math.sin(t), R)
            for t in [2 * math.pi * i / 360 for i in range(360)]]
    cone_right = smul(0.62, extreme(rim, lambda q: q[0]))
    sheet_left = extreme(hrim, lambda q: -q[0])
    corner = extreme([(a, b, 0.0) for a, b in corners], lambda q: q[0])
    ell = [addv(smul(math.cos(t), e1p), smul(math.sin(t), e2p))
           for t in [2 * math.pi * i / 360 for i in range(360)]]
    ell_left = extreme(ell, lambda q: -q[0] - 0.3 * q[1])

    pl.label(proj(cam, (0, 0, 2.05)), r"$P^{\perp}$", color="PInk",
             dirs=[90, 60, 120], rmax=0.5)
    pl.label(proj(cam, smul(k, w2)), r"$P'^{\perp}$", color="PGrass",
             dirs=[90, 45, 0], rmax=0.5)
    pl.label(proj(cam, (0, 0, 1.0)), r"$w_{P}$", color="POchre!80!black",
             dirs=[180, 150, 210], rmax=3.0, skip=0.12)
    pl.label(proj(cam, w2), r"$w_{P'}$", color="PGrass", dirs=[0, 30, -30],
             rmax=3.0, skip=0.12)
    pl.label(proj(cam, (1.0, 0, 0)), r"$e_{1}$", color="PClay!80!black",
             dirs=[-90, -60, -120], rmax=2.0, skip=0.14)
    pl.label(proj(cam, (0, 1.0, 0)), r"$e_{2}$", color="PClay!80!black",
             dirs=[90, 60], rmax=2.0, skip=0.14)
    pl.label(proj(cam, corner), r"$P=\{z=0\}$", color="PClay",
             dirs=[0, -30, 30], rmax=1.0)
    pl.label(proj(cam, cone_right), r"$q=0$", color="PBlue",
             dirs=[0, -20, 20], rmax=2.0)
    pl.label(proj(cam, sheet_left), r"$q=-1$", color="POchre!80!black",
             dirs=[180, 160, 200], rmax=2.5, skip=0.10)
    pl.label(proj(cam, ell_left), r"$P'$", color="PGrass",
             dirs=[180, 200, 220, 240], rmax=2.5, skip=0.10)
    pl.build()
    compile_plate("fig_lightcone")


if __name__ == "__main__":
    which = sys.argv[1:] or ["escape", "lightcone"]
    if "escape" in which:
        fig_escape()
    if "lightcone" in which:
        fig_lightcone()
