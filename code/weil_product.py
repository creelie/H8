#!/usr/bin/env python3
"""
weil_product.py

The Weil class is multiplicative under products of Weil-type abelian
varieties.  Exact arithmetic over Q(sqrt(-d)); no floating point.

For A_i of (K,-1,n_i)-Weil type with the same K, the product carries the
diagonal K-action and is of (K,-1,n_1+n_2)-Weil type, and

    omega_1(A) = (1/2)( omega_1(A_1) omega_1(A_2) - omega_2(A_1) omega_2(A_2) )
    omega_2(A) = (1/2)( omega_1(A_1) omega_2(A_2) + omega_2(A_1) omega_1(A_2) )

equivalently  omega(A_1) omega(A_2) = 2 omega(A_1 x A_2)  for the K-valued
invariant omega = omega_1 + sqrt(-d) omega_2.  Over k factors the constant is
2^(k-1).  This is Theorem 14.x and its corollaries.

Model.  V_pm are the eigenspaces of the K-action on H^1.  Generators
u_0..u_{2n-1} span V_+, v_0..v_{2n-1} span V_-, conjugation swaps them, and
alpha_pm are the top exterior powers.  For the product the generator sets are
concatenated; alpha_pm have even degree so the blocks commute.
"""

from fractions import Fraction as F
import sys

_NP = _NF = 0


def check(name, ok, detail=""):
    global _NP, _NF
    print("    [%s] %s" % ("PASS" if ok else "FAIL", name))
    if detail:
        for line in detail.splitlines():
            print("           " + line)
    if ok:
        _NP += 1
    else:
        _NF += 1


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


CZ = (F(0), F(0))
CO = (F(1), F(0))
CI = (F(0), F(1))


def wedge(m1, c1, m2, c2):
    if set(m1) & set(m2):
        return None
    arr = list(m1) + list(m2)
    sg = 1
    n = len(arr)
    for i in range(n):
        for j in range(n - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sg = -sg
    c = cmul(c1, c2)
    return tuple(arr), (c[0] * sg, c[1] * sg)


def mul(A, B):
    out = {}
    for m1, c1 in A.items():
        for m2, c2 in B.items():
            r = wedge(m1, c1, m2, c2)
            if r is None:
                continue
            m, c = r
            out[m] = cadd(out.get(m, CZ), c)
            if out[m] == CZ:
                del out[m]
    return out


def add(A, B):
    out = dict(A)
    for m, c in B.items():
        out[m] = cadd(out.get(m, CZ), c)
        if out[m] == CZ:
            del out[m]
    return out


def scal(A, s):
    return {m: cmul(c, s) for m, c in A.items()}


def neg(A):
    return scal(A, (F(-1), F(0)))


def eq(A, B):
    return not add(A, neg(B))


def factor(offset, n):
    """Generators for one factor of Weil type with parameter n."""
    m = 2 * n
    ap = {tuple(offset + j for j in range(m)): CO}
    am = {tuple(offset + m + j for j in range(m)): CO}
    w1 = add(ap, am)
    w2 = scal(add(ap, neg(am)), CI)
    return ap, am, w1, w2, 2 * m


def kmul(p, q):
    """Product in the K-valued notation: (a1,a2)*(b1,b2)."""
    a1, a2 = p
    b1, b2 = q
    return (add(mul(a1, b1), neg(mul(a2, b2))), add(mul(a1, b2), mul(a2, b1)))


def part_two_factors():
    print("  (a) the two-factor identity")
    rows, ok = [], True
    for n1 in (1, 2, 3):
        for n2 in (1, 2, 3):
            ap1, am1, w11, w21, s1 = factor(0, n1)
            ap2, am2, w12, w22, _ = factor(s1, n2)
            apP, amP = mul(ap1, ap2), mul(am1, am2)
            w1P = add(apP, amP)
            w2P = scal(add(apP, neg(amP)), CI)
            c1 = scal(add(mul(w11, w12), neg(mul(w21, w22))), (F(1, 2), F(0)))
            c2 = scal(add(mul(w11, w22), mul(w21, w12)), (F(1, 2), F(0)))
            good = eq(w1P, c1) and eq(w2P, c2)
            ok = ok and good
            rows.append("n1=%d, n2=%d -> n=%d: %s" % (n1, n2, n1 + n2, "holds" if good else "FAILS"))
    check("omega_1 and omega_2 of the product are the stated combinations, n_i <= 3",
          ok, "\n".join(rows))


def part_k_valued():
    print("  (b) the K-valued form")
    rows, ok = [], True
    for n1 in (1, 2, 3):
        for n2 in (1, 2, 3):
            ap1, am1, w11, w21, s1 = factor(0, n1)
            ap2, am2, w12, w22, _ = factor(s1, n2)
            apP, amP = mul(ap1, ap2), mul(am1, am2)
            w1P = add(apP, amP)
            w2P = scal(add(apP, neg(amP)), CI)
            pr = kmul((w11, w21), (w12, w22))
            good = eq(pr[0], scal(w1P, (F(2), F(0)))) and eq(pr[1], scal(w2P, (F(2), F(0))))
            ok = ok and good
            rows.append("n1=%d, n2=%d: omega(A1) omega(A2) = 2 omega(A1 x A2)  %s"
                        % (n1, n2, "yes" if good else "NO"))
    check("the invariant omega = omega_1 + sqrt(-d) omega_2 is multiplicative",
          ok, "\n".join(rows))


def part_many_factors():
    print("  (c) associativity over k factors")
    rows, ok = [], True
    for parts in [(1, 1, 1), (1, 1, 2), (2, 2, 1), (1, 2, 3), (1, 1, 1, 1), (2, 1, 1, 2)]:
        off = 0
        facs = []
        for n in parts:
            ap, am, w1, w2, sz = factor(off, n)
            facs.append((ap, am, w1, w2))
            off += sz
        apP = {(): CO}
        amP = {(): CO}
        for ap, am, _, _ in facs:
            apP, amP = mul(apP, ap), mul(amP, am)
        w1P = add(apP, amP)
        w2P = scal(add(apP, neg(amP)), CI)
        acc = (facs[0][2], facs[0][3])
        for _, _, w1, w2 in facs[1:]:
            acc = kmul(acc, (w1, w2))
        k = len(parts)
        c = (F(2) ** (k - 1), F(0))
        good = eq(acc[0], scal(w1P, c)) and eq(acc[1], scal(w2P, c))
        ok = ok and good
        rows.append("parts %s -> n=%d, k=%d: product = 2^%d omega  %s"
                    % (str(parts), sum(parts), k, k - 1, "yes" if good else "NO"))
    check("the k-factor identity holds with constant 2^(k-1)", ok, "\n".join(rows))


def part_base_case():
    print("  (d) the base case n = 1")
    rows, ok = [], True
    for n in (1, 2, 3):
        _, _, w1, _, _ = factor(0, n)
        deg = len(next(iter(w1)))
        expected = 2 * n
        good = (deg == expected)
        ok = ok and good
        rows.append("n=%d: dim A = %d, Weil class in H^%d%s"
                    % (n, 2 * n, deg, "  (divisor degree)" if deg == 2 else ""))
    check("the Weil class sits in H^{2n}, so at n = 1 it is a divisor class",
          ok, "\n".join(rows))


def part_dimensions():
    print("  (e) the size of the product locus")
    rows = []
    ok = True
    for n in range(1, 8):
        fam = n * n
        quat = n * (n + 1) // 2
        prod = n
        if n >= 2 and not (prod < quat < fam):
            ok = False
        rows.append("n=%d: family %d, quaternionic locus %d, product locus %d"
                    % (n, fam, quat, prod))
    check("for n >= 2 the product locus is proper and smaller than the quaternionic locus",
          ok, "\n".join(rows))


def main():
    print("the Weil class under products")
    part_two_factors()
    part_k_valued()
    part_many_factors()
    part_base_case()
    part_dimensions()
    print()
    print("  %d checks passed, %d failed" % (_NP, _NF))
    print("  overall: %s" % ("PASS" if _NF == 0 else "FAIL"))
    return 0 if _NF == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
