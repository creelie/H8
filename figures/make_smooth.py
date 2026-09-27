#!/usr/bin/env python3
"""
make_smooth.py

One plate for the smooth support theorem.

  fig_bmywindow  (a) the defect 3e(S) - K_S^2 = 24(b^4 - d^2) of the
                 Bogomolov-Miyaoka-Yau inequality for the surface that the
                 theorem on the invariants of a smooth support attaches to
                 the pair (b, d), as a surface over the window
                 1.5 <= b <= 4.5, 0 <= d <= 20, compressed by a signed cube
                 root; its zero locus d = b^2 is the wall, drawn on the
                 surface and on the floor, with the weaker wall d = 5b^2/3
                 where e(S) = 0, the line b = 3, the four admissible
                 discriminants d = 1, 3, 5, 7 above the wall, the equality
                 case d = 9 on it and d = 11, 13, 15 below.
                 (b) the section b = 3: K_S^2 = 3(9+d)(63-d) and
                 3e(S) = 27(9+d)(15-d) against d, meeting at d = 9 in 2916,
                 with the values of the table of invariants at d = 1,3,5,7.

Nothing is drawn by eye.  The heights are the exact values of the formulas
of the theorem, and the tick labels on the vertical axis of (a) are the true
defects at the drawn heights.
"""
import math
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from render3d import Camera, Scene                                # noqa: E402
from make_diagrams import (Plate, compile_plate, proj, TIP, orbit_eye,  # noqa
                           Axes2D, soften, ink_bbox)

GEN = "make_smooth.py"
BLO, BHI = 1.5, 4.5                 # range of b
DLO, DHI = 0.0, 20.0                # range of d
SX, SY, SZ = 1.10, 0.19, 0.17       # drawing scales on b, d and the height
ZF, ZT = -10.5, 10.5                # floor and ceiling, in thousands


def defect(b, d):
    return 24.0 * (b ** 4 - d * d)


def comp(D):
    """The height of the true defect D, in thousands."""
    return D / 1000.0


def P(b, d, h=None):
    """The point over (b, d) at compressed height h (default: the surface)."""
    if h is None:
        h = comp(defect(b, d))
    return ((b - 3.0) * SX, -(d - 10.0) * SY, h * SZ)


def invariants(b, d):
    K2 = 3 * (b * b + d) * (7 * b * b - d)
    e = 3 * (b * b + d) * (5 * b * b - 3 * d)
    chi = (b * b + d) * (3 * b * b - d)
    return K2, e, chi


def fig_bmywindow():
    # the table of the paper, recomputed
    table = {1: (260, 1860, 1260), 3: (288, 2160, 1296), 5: (308, 2436, 1260),
             7: (320, 2688, 1152)}
    for d, (chi, K2, e) in table.items():
        assert invariants(3, d) == (K2, e, chi)
        assert 3 * e - K2 == defect(3, d)
    assert invariants(3, 9)[0] == 3 * invariants(3, 9)[1] == 2916

    tgt = P(3.0, 10.0, 0.0)
    az, el = -128.0, 27.0
    eye = orbit_eye(tgt, 30.0, az, el)
    cam = Camera(eye=eye, target=tgt, focal=30.0, scale=1.42)
    sc = Scene(cam)
    pl = Plate("fig_bmywindow", GEN,
               "The Bogomolov-Miyaoka-Yau defect of a smooth support over "
               "the quarter plane of (b,d), and its section at b = 3.",
               thresh=238)

    def lift(p, eps=0.012):
        """p moved a little towards the eye, so a curve on the surface is
        drawn over the facet it lies on."""
        v = [eye[i] - p[i] for i in range(3)]
        n = math.sqrt(sum(c * c for c in v))
        return tuple(p[i] + eps * v[i] / n for i in range(3))

    top = []            # curves and points on the surface, drawn last

    def on_surface(g, t0, t1, n, style, pr=3):
        pts = [proj(cam, g(t0 + (t1 - t0) * k / n)) for k in range(n + 1)]
        top.append("  \\draw[%s] %s;\n" % (style, " -- ".join(
            "(%.4f,%.4f)" % q for q in pts)))

    def dot_on(p, style):
        top.append("  \\node[%s] at (%.4f,%.4f) {};\n" % ((style,)
                                                          + proj(cam, p)))

    # the box, drawn first as a background: nothing of it is in front of
    # the surface from this side
    bg = Scene(cam)
    # the box: floor, two back walls, their grids at the tick levels
    bg.surface(lambda b, d: P(b, d, ZF), (BLO, BHI), (DLO, DHI), 1, 1,
               base="PSlate", opacity=0.07, ambient=0.8, diffuse=0.1)
    bg.surface(lambda b, h: P(b, DLO, h), (BLO, BHI), (ZF, ZT), 1, 1,
               base="PSlate", opacity=0.05, ambient=0.8, diffuse=0.1)
    bg.surface(lambda d, h: P(BHI, d, h), (DLO, DHI), (ZF, ZT), 1, 1,
               base="PSlate", opacity=0.05, ambient=0.8, diffuse=0.1)
    levels = [0.0, 4000.0, 8000.0]
    for D in [-x for x in levels[1:]] + levels:
        h = comp(D)
        bg.curve(lambda b, h=h: P(b, DLO, h), (BLO, BHI), 30,
                 "soft,PRule!70,line width=0.25pt", priority=0, chunk=2)
        bg.curve(lambda d, h=h: P(BHI, d, h), (DLO, DHI), 30,
                 "soft,PRule!70,line width=0.25pt", priority=0, chunk=2)
    for b in (2, 3, 4):
        bg.curve(lambda h, b=b: P(b, DLO, h), (ZF, ZT), 12,
                 "soft,PRule!70,line width=0.25pt", priority=0, chunk=2)
    for d in (5, 10, 15):
        bg.curve(lambda h, d=d: P(BHI, d, h), (ZF, ZT), 12,
                 "soft,PRule!70,line width=0.25pt", priority=0, chunk=2)
    # the three edges that carry the ticks, and the rest of the box, soft
    for u, v, st in (((BLO, DLO, ZF), (BLO, DHI, ZF), "PSlate!80"),
                     ((BLO, DHI, ZF), (BHI, DHI, ZF), "PSlate!80"),
                     ((BLO, DLO, ZF), (BLO, DLO, ZT), "PSlate!80"),
                     ((BLO, DLO, ZF), (BHI, DLO, ZF), "soft,PSlate!60"),
                     ((BHI, DLO, ZF), (BHI, DHI, ZF), "soft,PSlate!60"),
                     ((BHI, DHI, ZF), (BHI, DHI, ZT), "soft,PSlate!60")):
        bg.curve(lambda t, u=u, v=v: P(*[u[i] + t * (v[i] - u[i])
                                        for i in range(3)]), (0.0, 1.0), 16,
                 "%s,line width=0.4pt" % st, priority=0, chunk=2)

    # the defect surface, opaque, indigo where positive and clay where not
    # two patches whose common boundary is exactly the zero locus d = b^2
    sc.surface(lambda b, s: P(b, s * min(b * b, DHI)), (BLO, BHI), (0.0, 1.0),
               30, 26, base="PIndigo", ambient=0.36, diffuse=0.40)
    bw = math.sqrt(DHI)
    sc.surface(lambda b, s: P(b, b * b + s * (DHI - b * b)), (BLO, bw),
               (0.0, 1.0), 26, 18, base="PClay", ambient=0.36, diffuse=0.40)
    # the mesh b = const, d = const, drawn as soft lines on the surface
    for b in [BLO + 0.5 * i for i in range(7)]:
        on_surface(lambda d, b=b: P(b, d), DLO, DHI, 40,
                   "soft,white!65!PInk,line width=0.25pt", pr=2)
    for d in [DLO + 2.5 * i for i in range(9)]:
        on_surface(lambda b, d=d: P(b, d), BLO, BHI, 30,
                   "soft,white!65!PInk,line width=0.25pt", pr=2)
    # the wall d = b^2 (the zero locus) and the curve e = 0 on the surface
    on_surface(lambda b: P(b, b * b), BLO, math.sqrt(DHI), 60,
               "PMag,line width=1.3pt")
    on_surface(lambda b: P(b, 5 * b * b / 3.0), BLO, math.sqrt(3 * DHI / 5),
               60, "PGrass,line width=1.0pt,dash pattern=on 2.4pt off 1.6pt")
    # the line b = 3 on the surface, and the discriminants on it
    on_surface(lambda d: P(3.0, d), DLO, DHI, 80, "PInk!85,line width=0.6pt")
    for d in (1, 3, 5, 7):
        dot_on(P(3.0, d), "circle,fill=PAmber,draw=white,line width=0.5pt,"
               "inner sep=1.9pt")
    dot_on(P(3.0, 9.0), "circle,fill=PMag,draw=white,line width=0.5pt,"
           "inner sep=2.1pt")
    for d in (11, 13, 15):
        dot_on(P(3.0, d), "circle,draw=PClay,line width=0.8pt,fill=white,"
               "inner sep=1.6pt")
    body = soften(bg.emit() + sc.emit() + "".join(top))
    # close the hairline seams between the facets of the opaque surface
    body = re.sub(r"\\path\[draw=none,fill=(P(?:Indigo|Clay)![0-9]+!white)\]",
                  r"\\path[draw=\1,line width=0.15pt,fill=\1]", body)
    pl.add(body)

    # tick labels of the box
    for b in (2, 3, 4):
        x, y = proj(cam, P(b, DHI, ZF))
        pl.put(x + 0.18, y - 0.18, r"$%d$" % b, color="PSlate",
               font=r"\footnotesize", anchor="w")
    for d in (0, 5, 10, 15, 20):
        x, y = proj(cam, P(BLO, d, ZF))
        pl.put(x - 0.18, y - 0.18, r"$%d$" % d, color="PSlate",
               font=r"\footnotesize", anchor="e")
    names = {0.0: r"$0$", 4000.0: r"$4000$", 8000.0: r"$8000$"}
    for D in [-x for x in levels[1:]] + levels:
        x, y = proj(cam, P(BLO, DLO, comp(D)))
        t = names[abs(D)] if D >= 0 else "$-" + names[-D][1:]
        pl.put(x - 0.12, y, t, color="PSlate", font=r"\footnotesize",
               anchor="e")
    x, y = proj(cam, P(3.0, DHI + 3.0, ZF))
    pl.label((x, y), r"$b$", color="PSlate", dirs=[-60, -90], rmax=0.3)
    xd, yd = proj(cam, P(BLO - 0.55, 10.0, ZF))
    pl.label((xd, yd), r"$d$", color="PSlate", dirs=[-120, -90], rmax=0.3)
    xz, yz = proj(cam, P(BLO, DLO, ZT))
    pl.label((xz, yz), r"$3e(S)-K_{S}^{2}$", color="PSlate", dirs=[90, 60],
             rmax=0.4)

    pl.label(proj(cam, P(math.sqrt(DHI), DHI)), r"$d=b^{2}$",
             color="PMag", dirs=[0, 30, -30, 60], rmax=1.5, skip=0.1)
    bg = math.sqrt(3 * DHI / 5)
    pl.label(proj(cam, P(bg, DHI)), r"$d=\tfrac53b^{2}$",
             color="PGrass", dirs=[-30, 0, -60], rmax=2.0, skip=0.1)
    pl.label(proj(cam, P(3.0, DHI)), r"$b=3$", color="PInk",
             dirs=[-90, -60, -120], rmax=1.5, skip=0.1)
    pl.label(proj(cam, P(3.0, 1.0)), r"$d=1$", color="PAmber!80!black",
             font=r"\footnotesize", dirs=[180, 150, 210, 120], rmax=2.4,
             skip=0.1)

    # (b): the section b = 3
    bx0, by0, bx1, by1 = ink_bbox("".join(pl.parts))
    ax = Axes2D(pl, bx1 + 1.75, by0 + 0.95, 4.8, by1 - by0 - 1.5, (0.0, 16.4),
                (0.0, 4300.0))
    pl.add("  \\path[fill=PClay!8] (%.3f,%.3f) rectangle (%.3f,%.3f);\n"
           % (ax.X(9), ax.Y(0), ax.X(16.4), ax.Y(4300)))
    ax.frame(range(0, 17, 2), range(0, 4001, 1000),
             yfmt=lambda v: "$%d$" % v if v else None)
    K2 = [(d / 10.0, 3 * (9 + d / 10.0) * (63 - d / 10.0)) for d in range(0, 165)]
    E3 = [(d / 10.0, 27 * (9 + d / 10.0) * (15 - d / 10.0))
          for d in range(0, 165)]
    pl.add("  \\draw[PIndigo,line width=1.1pt] %s;\n"
           % " -- ".join("(%.3f,%.3f)" % ax.P(x, y) for x, y in E3 if y >= 0))
    pl.add("  \\draw[PClay,line width=1.1pt] %s;\n"
           % " -- ".join("(%.3f,%.3f)" % ax.P(x, y) for x, y in K2))
    pl.add("  \\draw[PMag,line width=0.5pt,dash pattern=on 1.5pt off 1.5pt] "
           "(%.3f,%.3f) -- (%.3f,%.3f);\n"
           % (ax.X(9), ax.Y(0), ax.X(9), ax.Y(2916)))
    for d in (1, 3, 5, 7):
        k2, e, _ = invariants(3, d)
        pl.add("  \\draw[PAmber,line width=0.5pt,dash pattern=on 1pt off 1pt] "
               "(%.3f,%.3f) -- (%.3f,%.3f);\n"
               % (ax.X(d), ax.Y(k2), ax.X(d), ax.Y(3 * e)))
        for v in (k2, 3 * e):
            pl.add("  \\node[circle,fill=PAmber,draw=white,line width=0.5pt,"
                   "inner sep=1.7pt] at (%.3f,%.3f) {};\n" % ax.P(d, v))
    for d in (11, 13, 15):
        k2, e, _ = invariants(3, d)
        for v in (k2, 3 * e):
            pl.add("  \\node[circle,draw=PClay,line width=0.8pt,fill=white,"
                   "inner sep=1.4pt] at (%.3f,%.3f) {};\n" % ax.P(d, v))
    pl.add("  \\node[circle,fill=PMag,draw=white,line width=0.5pt,"
           "inner sep=2.0pt] at (%.3f,%.3f) {};\n" % ax.P(9, 2916))
    pl.label(ax.P(9, 2916), r"$2916$", color="PMag", font=r"\footnotesize",
             dirs=[-90, -60, -120], rmax=0.9, skip=0.1)
    pl.label(ax.P(3, 3888), r"$3e(S)$", color="PIndigo", dirs=[90, 60, 120],
             rmax=0.8)
    pl.label(ax.P(15.5, 3 * (9 + 15.5) * (63 - 15.5)), r"$K_{S}^{2}$",
             color="PClay", dirs=[90, 60, 120], rmax=0.8)
    pl.label(ax.P(1, 1860), r"$1860$", color="PAmber!80!black",
             font=r"\footnotesize", dirs=[-90, -60, -120, 0], rmax=0.9,
             skip=0.1)
    pl.put(ax.X(8.2), ax.Y(0) - 0.72, r"$d$", color="PSlate")
    pl.put(ax.X(8.2), by1 + 0.25, r"(b)\ \ $b=3$", color="PInk")
    pl.put(bx0 - 1.2, by1 + 0.25, r"(a)", color="PInk", anchor="w")
    pl.build()
    compile_plate("fig_bmywindow")


if __name__ == "__main__":
    fig_bmywindow()
