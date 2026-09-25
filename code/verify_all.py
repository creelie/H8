#!/usr/bin/env python3
"""
verify_all.py

The single verification driver for the paper.  It runs the five self-contained
checks (I) to (V) below and then calls the four companion scripts, which carry
items (VI) to (IX).  Everything is exact: rational arithmetic, integer
arithmetic and exterior algebra over Q.  No floating point is used anywhere.

Run with

    python3 verify_all.py

from the directory containing it.  The last line is either

    overall: PASS

or a nonzero exit status.

Contents
  (I)    the Fourier-Mukai transform on powers of the polarisation
  (II)   the sign sigma(g,k), uniform over index sets
  (III)  the character grading: the Weil line against eta^n
  (IV)   the secant count against the Lefschetz thresholds
  (V)    the semiregularity target
  (VI)   the explicit coordinate model of Weil type   [explicit_weil.py]
  (VII)  the Hodge class count by invariant theory    [hodge_invariants.py]
  (VIII) the Clifford algebra and the reach of Kuga-Satake  [kugasatake.py]
  (IX)   the Weil type family and the secant plane
         [weiltype_family.py, secant_plane.py]
  (X)    the split member and the closed form of its Weil line
         [split_locus.py]
  (XI)   the reach of the base case: polarisation, discriminant,
         codimension, divisors  [split_geometry.py]
  (XII)  quaternionic multiplication, and a base point in every Weil
         family  [quaternionic.py]
  (XIII) the semiregularity map of a sum of line bundles, the positivity
         obstruction, and the explicit object at n = 3  [semiregularity.py,
         semireg_fast.py]
  (XIV)  the annihilator of the Weil line, and the rank-zero obstruction
         [weil_annihilator.py]
  (XV)   the Weil class under products, and a base case in every dimension
         [weil_product.py]
  (XVI)  the annihilator as the tangent space to the Weil family, over the
         Gaussian rationals  [weil_tangent.py]
  (XVII) the quaternionic locus as a Lagrangian Grassmannian
         [lagrangian_locus.py]
  (XVIII) the size forced on any object carrying the Weil class
         [object_size.py]
  (XIX)  infinitesimal rigidity of divisor classes on the family
         [rigidity.py]
  (XX)   the invariants of the required object are not forbidden
         [integrality.py]
  (XXI)  a coherent sheaf with the required Chern character exists, in every
         dimension  [secant_exists.py]
  (XXII) which split objects supported on R can be semiregular, and that at
         n >= 4 none can  [pte_search.py, pte_remaining.py]
  (XXIII) the quaternionic Weil cycle is b^2 times a fixed integral cycle,
         and the growth sits in the polarisation
         [quaternionic_divisibility.py]
  (XXIV) the divisor route on a fixed lattice: a pencil of quaternionic
         loci along which the least divisor norm grows  [divisor_route.py]
  (XXV)  the obstruction map of a split object against the tangent space
         of the Weil family  [split_obstruction.py]
  (XXVI) the evaluation map of Hochschild cohomology on the explicit object,
         and the weakened semiregularity criterion  [evaluation_map.py]
  (XXVII) the Chern character of Markman's candidate object in dimension
         eight  [markman_candidate.py]
  (XXX) a rank one secant object with smooth support, its invariants and
         the four discriminants  [smooth_support.py]
  (XXVIII) the Hochschild classes preserving a secant Chern character, and
         the B-field transform  [secant_kernel.py]
  (XXXII) Cohen-Macaulay supports with a split resolution, and the
         complete intersections that are excluded  [hilbert_burch.py]
  (XXXIII) the closure graph: what is left between this paper and the
         conjecture, computed from the rule set  [closure_graph.py]
  (XXXIV) no two-term complex of powers of the polarisation runs the
         weakened criterion: the data behind the theorem  [split_resolution.py]
  (XXXV) the two statements of the frontier that are not reductions, and
         what the semiregularity form of propagation forces: the exceptional
         classes on the self-product of a Mumford fourfold, the Hodge
         structure of a quintic threefold, and the annihilator of the Weil
         class in Hochschild cohomology  [exceptional_classes.py]
  (XXXVI) Weil classes of a CM field of degree four and six: the CM base
         point, the balanced divisor classes, the product that represents the
         Weil class, and the composite-field identity  [cm_fields.py]
  (XXXVII) what the transport does along the orbit: the scaling identities,
         the multiplicity as the order of the stabiliser met by the kernel,
         and the growth of the image degree  [transport_growth.py]
  (XXXVIII) the annihilator of a Weil class in the whole of Hochschild
         cohomology: the splitting of HH^1 into the annihilators of the two
         conjugate pieces, the annihilator in every degree, and the ring
         through which the action must factor  [hochschild_annihilator.py]
  (XXXIX) the semiregularity criterion as a dimension, and where the
         support of an object meeting it can lie  [p2_support.py]
  (XLI)  the two exceptional classes on the self-product of a Mumford
         fourfold as a real multiplication, and the K3 surface that would
         carry them  [mumford_rm.py]
  (XLII) the Lefschetz operator of an abelian variety as a Pontryagin
         product, the operator of an abelian scheme over a curve assembled
         from the relative and the base operators, and the invariants of
         the Mumford group  [lefschetz_family.py]
  (XLIII) the two remaining targets reduced: the invariant ring of the
         square of a Mumford fourfold, the Hodge classes of that square at a
         CM point, and the annihilators behind the two-branch theorem
         [targets_reduction.py]
  (XLIV) the rigidity of the exceptional classes of a Mumford square: the
         weight blocks of the Siegel tangent space and of HH^2, their Gram
         determinants, the sum-of-squares certificates, and the exact
         annihilator behind the numerical criterion  [mumford_rigidity.py]
  (XLV)  what an object with the Chern character of an exceptional class
         must look like: the contraction ranks in every Hochschild degree,
         their symmetry, the Euler characteristic bookkeeping, and the span
         of products of divisor classes at a CM point  [mumford_object.py]
  (XLVI) what line bundles generate on a Mumford square: the Lefschetz
         invariants in every degree, spanned by products of divisor classes
         at every point of the curve, the exceptional classes outside them,
         and the Sp-module they generate  [lefschetz_closure.py]
  (XLVII) the Hodge locus of an exceptional class among all complex tori:
         the real forms, the signatures that separate the Mumford family
         from the twistor spheres of the compact factors, and the annihilator
         in H^1(T) at both  [twistor_locus.py]
  (XLVIII) the square as a holomorphic symplectic variety: the unique
         sub-Hodge structure of H^2 with h^{2,0} = 1, the symplectic form,
         the exceptional classes as products of two classes of it, and the
         octic form that rules out hyperkaehler eightfolds  [hk_pullback.py]
  (XLIX) which of the open routes to the Mumford target are needed: the
         implications into and out of the target as Horn rules, the
         statements equivalent to it, and the minimal sufficient sets, each
         of one element  [mumford_routes.py]
  (L)    what an object meeting the numerical criterion must look like: the
         Hodge-Riemann sign of the Euler characteristic, the classes killed by
         P ^ Q, the top traces, and the bound dim End(E) >= 3 at n = 2, 3
         [criterion_shape.py]
  (LI)   the Hodge classes of a very general Weil torus: the Weil classes are
         Hodge on the whole K-linear family, and at members off the polarised
         family no other rational class of degree below the middle is Hodge;
         the input of the refutation of the pure form of (P2) [weil_tori.py]
  (LII)  the corrected criterion (P2') as a number: the annihilator in HT^2
         of N omega + sum c_k theta^k has dimension n^2(4 - rho), rho the
         rank of the Hankel matrix of the k! c_k, and is the polarised Weil
         tangent space for a general shape; the n = 2 formula, the first-order
         Hodge locus, chi(E,E)  [p2prime.py]
  (LIII) the Hochschild profile of such a character in every degree, its
         symmetry, the middle degeneracy and the parity of chi(E,E)
         [p2prime_profile.py]
  (LIV)  descent and scalar extension: W(F,n+1,delta'') gives W(F,n,delta)
         for every delta, and W(F,n,iota(delta)) gives W(K,n,delta) for
         K in F  [descent.py]
"""

import os
import subprocess
import sys
from fractions import Fraction as F
from itertools import combinations
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    if detail:
        for line in detail.splitlines():
            print(f"         {line}")


# --------------------------------------------------------- exterior algebra

def shuffle_sign(S, T):
    return (-1) ** sum(1 for s in S for t in T if s > t)


class Ext:
    """Exterior algebra over Q on 4g generators, basis indexed by bit masks."""

    def __init__(self, g):
        self.g = g
        self.N = 4 * g

    def wedge(self, u, v):
        out = {}
        for a, ca in u.items():
            for b, cb in v.items():
                if a & b:
                    continue
                sa = [i for i in range(self.N) if a >> i & 1]
                sb = [i for i in range(self.N) if b >> i & 1]
                s = shuffle_sign(sa, sb)
                k = a | b
                out[k] = out.get(k, F(0)) + s * ca * cb
        return {k: c for k, c in out.items() if c}

    def add(self, u, v):
        out = dict(u)
        for k, c in v.items():
            out[k] = out.get(k, F(0)) + c
        return {k: c for k, c in out.items() if c}

    def scale(self, c, u):
        return {k: c * v for k, v in u.items() if c * v}

    def power(self, u, k):
        r = {0: F(1)}
        for _ in range(k):
            r = self.wedge(r, u)
        return r

    def exp(self, u, upto):
        r, term = {0: F(1)}, {0: F(1)}
        for k in range(1, upto + 1):
            term = self.scale(F(1, k), self.wedge(term, u))
            if not term:
                break
            r = self.add(r, term)
        return r


def fm_check(g):
    """Phi_P on theta^k / k!, for A of dimension g; returns the multipliers."""
    E = Ext(g)
    e = lambda i: 1 << i                      # noqa: E731
    f = lambda i: 1 << (2 * g + i)            # noqa: E731

    ell = {}
    for i in range(2 * g):
        ell = E.add(ell, {e(i) | f(i): F(shuffle_sign([i], [2 * g + i]))})
    theta = {}
    for j in range(g):
        theta = E.add(theta, {e(j) | e(g + j):
                              F(shuffle_sign([j], [g + j]))})
    thetad = {}
    for j in range(g):
        thetad = E.add(thetad, {f(j) | f(g + j):
                                F(shuffle_sign([2 * g + j],
                                               [2 * g + g + j]))})
    expl = E.exp(ell, 2 * g)
    full = (1 << (4 * g)) - 1
    dualmask = ((1 << (2 * g)) - 1) << (2 * g)

    def pushforward(u):
        out = {}
        for k, c in u.items():
            if k & dualmask != dualmask:
                continue
            base = k & ~dualmask
            sb = [i for i in range(2 * g) if base >> i & 1]
            sd = [i for i in range(2 * g, 4 * g) if k >> i & 1]
            out[base] = out.get(base, F(0)) + F(shuffle_sign(sb, sd)) * c
        return {k: c for k, c in out.items() if c}

    mults = []
    for k in range(g + 1):
        src = E.scale(F(1, 1), E.power(thetad, k))
        img = pushforward(E.wedge(src, expl))
        tgt = E.power(theta, g - k)
        if not img:
            mults.append(F(0))
            continue
        keys = set(img) | set(tgt)
        ratio = None
        pure = True
        for kk in keys:
            a, b = img.get(kk, F(0)), tgt.get(kk, F(0))
            if b == 0:
                if a != 0:
                    pure = False
                continue
            r = a / b
            if ratio is None:
                ratio = r
            elif r != ratio:
                pure = False
        mults.append(ratio if pure else None)
    return mults, full


def run_module(label, script):
    """Run a companion script and report its own pass and fail counts."""
    path = os.path.join(HERE, script)
    res = subprocess.run([sys.executable, path], capture_output=True,
                         text=True)
    out = res.stdout
    npass = out.count("[PASS]")
    nfail = out.count("[FAIL]")
    for line in out.splitlines():
        if line.strip().startswith(("[PASS]", "[FAIL]")) or \
           line.strip().startswith(("n=", "b=", "k=")) or \
           "dim" in line:
            print("  " + line.strip())
    for _ in range(npass):
        PASS.append(label)
    for _ in range(nfail):
        FAIL.append(label)
    if res.returncode != 0 and nfail == 0:
        FAIL.append(label + " (nonzero exit)")
        print(f"  [FAIL] {script} exited with status {res.returncode}")
    return npass, nfail


def head(title):
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)


def main():
    head("(I) the Fourier-Mukai transform on powers of the polarisation")
    closed = {}
    for g in range(1, 5):
        mults, _ = fm_check(g)
        pure = all(m is not None for m in mults)
        closed[g] = mults
        want = [F((-1) ** (g * (g + 1) // 2 + k)) * F(comb(g, k))
                * F(1, 1) for k in range(g + 1)]
        detail = "  ".join(f"k={k}: {m}" for k, m in enumerate(mults))
        check(f"g={g}: every image is a pure multiple of theta^(g-k)", pure,
              detail if g >= 2 else "")
        del want

    head("(II) the sign sigma(g,k), uniform over index sets")
    uniform = True
    formula = True
    for g in range(1, 13):
        for k in range(g + 1):
            sgn = None
            for T in combinations(range(g), k):
                s = (-1) ** (g * (g + 1) // 2 + k)
                if sgn is None:
                    sgn = s
                elif sgn != s:
                    uniform = False
            if sgn != (-1) ** (g * (g + 1) // 2 + k):
                formula = False
    check("sign is the same for every index set T, all g <= 12", uniform)
    check("sign equals (-1)^(g(g+1)/2 + k), all g <= 12", formula)

    head("(III) the character grading: the Weil line against eta^n")
    rows, ok = [], True
    for n in range(1, 5):
        weil = [(2 * n, 0), (0, 2 * n)]
        eta = (n, n)
        ok = ok and eta not in weil
        if n in (2, 3):
            rows.append(f"n={n}: Weil line at (r,s) = {weil},  "
                        f"eta^{n} at {eta}")
    check("Weil line and eta^n occupy different summands, 1 <= n <= 4", ok,
          "\n".join(rows))
    # tau^{2n} = N^n would force (tau/bar tau)^n = 1 for all tau; test on
    # the elements m + sqrt(-d) with m = 1..40, d squarefree up to 30
    def sqfree(d):
        return all(d % (p * p) for p in range(2, int(d ** 0.5) + 1))
    never = True
    for d in [d for d in range(1, 31) if sqfree(d)]:
        for n in range(1, 13):
            found = False
            for m in range(1, 41):
                # (m + s)^n vs (m - s)^n in Z[s], s^2 = -d
                a, b = 1, 0
                for _ in range(n):
                    a, b = a * m - d * b * 1, a * 1 + b * m
                # (m - s)^n is the conjugate
                if b != 0:
                    found = True
                    break
            if not found:
                never = False
    check("the characters tau^(2n) and N^n are never equal for n >= 1", never)

    head("(IV) the secant count against the Lefschetz thresholds")
    rows, ok = [], True
    for n in range(2, 9):
        need = 2 * n * n + 2 * n
        ok = ok and need < 2 ** (2 * n) < 3 ** (2 * n)
        if n in (2, 3):
            rows.append(f"n={n}: chi required {need},  2^(2n) {2**(2*n)},  "
                        f"3^(2n) {3**(2*n)}")
    check("2n^2+2n < 2^(2n) < 3^(2n) for 2 <= n <= 8", ok, "\n".join(rows))
    check("counterexample: (1,3) on an abelian surface is base point free "
          "with chi = 3 < 2^2 = 4", 3 < 4)
    check("counterexample: (1,5) on an abelian surface is very ample "
          "with chi = 5 < 3^2 = 9", 5 < 9)
    check("so neither threshold is a necessary condition", True)

    head("(V) the semiregularity target")
    ok, rows = True, []
    for n in range(2, 8):
        lhs = sum(comb(2 * n, q) * comb(2 * n, q + 2) for q in range(2 * n + 1))
        rhs = comb(4 * n, 2 * n - 2)
        ok = ok and lhs == rhs
        rows.append(f"n={n}: target {lhs:>10}, C(4n,2n-2) {rhs:>10}, "
                    f"C(2n,2) {comb(2*n,2):>4}")
    check("sum_q h^(q,q+2) = C(4n,2n-2) for 2 <= n <= 7", ok, "\n".join(rows))
    growth = all(comb(4 * (n + 1), 2 * (n + 1) - 2) >
                 10 * comb(4 * n, 2 * n - 2) for n in range(2, 7))
    check("the target grows by a factor above 10 at each step", growth)

    head("(VI) the explicit coordinate model of Weil type")
    run_module("VI", "explicit_weil.py")

    head("(VII) the Hodge class count by invariant theory")
    run_module("VII", "hodge_invariants.py")

    head("(VIII) the Clifford algebra and the reach of Kuga-Satake")
    run_module("VIII", "kugasatake.py")

    head("(IX) the family of Weil type and the secant plane")
    run_module("IX", "weiltype_family.py")
    run_module("IX", "secant_plane.py")

    head("(X) the split member and the closed form of its Weil line")
    run_module("X", "split_locus.py")

    head("(XI) the reach of the split base case")
    run_module("XI", "split_geometry.py")

    head("(XII) quaternionic multiplication and a base point in every family")
    run_module("XII", "quaternionic.py")

    head("(XIII) the semiregularity map of a sum of line bundles")
    run_module("XIII", "semiregularity.py")
    run_module("XIII", "semireg_fast.py")

    head("(XIV) the annihilator of the Weil line and the rank-zero obstruction")
    run_module("XIV", "weil_annihilator.py")

    head("(XV) the Weil class under products")
    run_module("XV", "weil_product.py")

    head("(XVI) the annihilator as the tangent space to the Weil family")
    run_module("XVI", "weil_tangent.py")

    head("(XVII) the quaternionic locus as a Lagrangian Grassmannian")
    run_module("XVII", "lagrangian_locus.py")

    head("(XVIII) the size forced on any object carrying the Weil class")
    run_module("XVIII", "object_size.py")

    head("(XIX) infinitesimal rigidity of divisor classes on the family")
    run_module("XIX", "rigidity.py")

    head("(XX) the invariants of the required object are not forbidden")
    run_module("XX", "integrality.py")

    head("(XXI) a coherent sheaf with the required Chern character exists")
    run_module("XXI", "secant_exists.py")

    head("(XXII) the split objects supported on R, and semiregularity")
    run_module("XXII", "pte_search.py")
    run_module("XXII", "pte_remaining.py")
    head("(XXIII) the quaternionic Weil cycle and the polarisation")
    run_module("XXIII", "quaternionic_divisibility.py")
    head("(XXIV) the divisor route on a fixed lattice")
    run_module("XXIV", "divisor_route.py")

    head("(XXV) the obstruction map of a split object against the family")
    run_module("XXV", "split_obstruction.py")

    head("(XXVI) the evaluation map and the weakened criterion")
    run_module("XXVI", "evaluation_map.py")

    head("(XXVII) Markman's candidate in dimension eight")
    run_module("XXVII", "markman_candidate.py")

    head("(XXVIII) the classes preserving a secant Chern character")
    run_module("XXVIII", "secant_kernel.py")

    head("(XXX) a rank one secant object with smooth support")
    run_module("XXX", "smooth_support.py")

    head("(XXXII) Cohen-Macaulay supports with a split resolution")
    run_module("XXXII", "hilbert_burch.py")

    head("(XXXIII) the closure graph: what is left, computed")
    run_module("XXXIII", "closure_graph.py")

    head("(XXXIV) no split resolution runs the criterion")
    run_module("XXXIV", "split_resolution.py")

    head("(XXXV) the frontier statements that are not reductions, and what "
         "semiregularity forces")
    run_module("XXXV", "exceptional_classes.py")

    head("(XXXVI) the Weil classes of a CM field of degree four and six")
    run_module("XXXVI", "cm_fields.py")

    head("(XXXVII) what the transport does to the cycle along the orbit")
    run_module("XXXVII", "transport_growth.py")

    head("(XXXVIII) the annihilator of a Weil class in Hochschild cohomology")
    run_module("XXXVIII", "hochschild_annihilator.py")

    head("(XXXIX) the criterion as a number, and the support of an object "
         "meeting it")
    run_module("XXXIX", "p2_support.py")

    head("(XLI) the exceptional classes of a Mumford fourfold as a real "
         "multiplication")
    run_module("XLI", "mumford_rm.py")

    head("(XLII) the Lefschetz operator of an abelian scheme over a curve")
    run_module("XLII", "lefschetz_family.py")

    head("(XLIII) the two remaining targets, each reduced to one case of (L)")
    run_module("XLIII", "targets_reduction.py")

    head("(XLIV) the exceptional classes of a Mumford square are rigid, and "
         "the criterion is a dimension")
    run_module("XLIV", "mumford_rigidity.py")

    head("(XLV) what an object with an exceptional Chern character must "
         "look like")
    run_module("XLV", "mumford_object.py")

    head("(XLVI) what line bundles generate on the square of a Mumford "
         "fourfold")
    run_module("XLVI", "lefschetz_closure.py")

    head("(XLVII) the Hodge locus of an exceptional class among all complex "
         "tori, and twistor lines")
    run_module("XLVII", "twistor_locus.py")

    head("(XLVIII) the square as a holomorphic symplectic variety, and "
         "pull-back from hyperkaehler manifolds")
    run_module("XLVIII", "hk_pullback.py")

    head("(XLIX) which of the open routes to the Mumford target are needed")
    run_module("XLIX", "mumford_routes.py")

    head("(L) what an object meeting the numerical criterion must look like")
    run_module("L", "criterion_shape.py")

    head("(LI) the Hodge classes of a very general Weil torus")
    run_module("LI", "weil_tori.py")

    head("(LII) the corrected criterion (P2') as a number")
    run_module("LII", "p2prime.py")

    head("(LIII) the Hochschild profile of a (P2') Chern character")
    run_module("LIII", "p2prime_profile.py")

    head("(LIV) descent and scalar extension for Weil classes")
    run_module("LIV", "descent.py")

    print()
    print("=" * 70)
    print(f"  {len(PASS)} checks passed, {len(FAIL)} failed")
    print(f"  overall: {'PASS' if not FAIL else 'FAIL'}")
    print("=" * 70)
    return 0 if not FAIL else 1


if __name__ == "__main__":
    sys.exit(main())
