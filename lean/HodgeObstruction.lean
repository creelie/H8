/-
HodgeObstruction.lean

A machine check, by Lean 4's kernel, of the finite arithmetic behind the
results of "Density of the Algebraic Locus of Weil Classes on Abelian Varieties".

The two theorems are statements of algebraic geometry and are not formalised
here; what is formalised is the arithmetic on which each of them turns, and in
both cases that arithmetic is finite and integral.

  * The character obstruction turns on the assertion that the
    characters  tau |-> tau^(2n)  and  tau |-> N(tau)^n  of K^x are distinct.
    Section 1 below verifies this by exhibiting, for each imaginary quadratic
    field in a range and each n in a range, an explicit element tau of the
    ring of integers at which the two values differ.  The verification is
    exact integer arithmetic in Z[sqrt(-d)].

  * The closed form of the cohomological Fourier-Mukai transform turns on a
    permutation sign being uniform over index sets and equal to
    (-1)^(g(g+1)/2 + k).  Section 2 verifies both, as a permutation count.

  * The semiregularity target is the Vandermonde identity of Section 3.

  * The coordinate formula for the two generators of the Weil line turns on
    the powers of sqrt(-d) being rational exactly in even degree, with the
    closed values (-d)^m; Section 6 verifies this and the term counts.

  * The count of Hodge classes on a general abelian variety of Weil type is a
    finite bookkeeping over the character grading once the invariant theory
    has been done by hand; Section 7 carries out that bookkeeping.

  * The reach of the Kuga-Satake construction turns on the equation
    h^(2,0) = 1 having n = 1 as its only solution; Section 8 verifies this
    together with the Clifford dimensions.

  * The pencil of quaternionic loci at n = 2 turns on two integer
    certificates: a pair of 2 x 2 minors whose difference is the constant 2
    (d = 1), and a constant minor -4 (d = 3), which bound the index of the
    lattice Z[i] x_k in its saturation uniformly in k; and on the quadratic
    beta(k) being positive with negative discriminant.  Section 16 checks
    these, together with the two values of k at which beta(k) is a rational
    square and a rational point of the locus can be written down.

  * The obstruction map of a split object against the Weil family has rank
    n^2 - n(n+1)/2 = n(n-1)/2 when its classes span the Neron-Severi group,
    and for the explicit object at n = 3 the kernel of the semiregularity
    map, of dimension 15 = n^2 + n(n-1), contains the n^2 = 9 dimensional
    copy of the tangent space and the 3 dimensional image of the obstruction
    map with trivial intersection.  Section 17 checks this bookkeeping.

  * The evaluation map of Hochschild cohomology on a sum of s line bundles
    cannot be surjective onto the diagonal part of Ext^2 once s >= 5, because
    dim HT^2 = 2 C(2n,2) + 4n^2 is smaller than s C(2n,2); Section 18 checks
    the inequality for 2 <= n <= 30 and 5 <= s <= 40, and the dimensions
    66 and 90 at n = 3, s = 6.

  * Markman's candidate object in dimension eight is built from N = (d+9)/2
    translates of a theta divisor; its Chern character lies on the secant
    plane exactly when the Euler characteristic of the partially normalised
    union is (d+9)(27-d), and the counts and identities that make this so
    are polynomial in d.  Section 19 checks them for every odd d up to 201.

  * The Hochschild classes preserving a secant Chern character a u_t + b v_t
    are cut out by a 2 x 2 system with determinant -(a^2 d + b^2), never zero,
    and the compensation of the Poisson classes is uniform in the degree
    because the coefficients C_k = k! c_k of the character satisfy
    C_(k+1) = -d C_(k-1); the kernel has dimension n(n+1)/2 + n(n-1)/2 = n^2.
    Section 20 checks the three facts.

  * Markman's candidate leaves (d+9)(d-2) of its (d+9)(3d-3) isolated double
    points unnormalised, at least twelve for every odd d >= 3, and
    normalising all of them would move the Euler characteristic to 50 N,
    which never equals the secant value 72 N - 4 N^2 for an integer N.
    Section 21 checks both, so that the local obstruction always has a point
    to act at.

  * Markman's candidate for a quartic CM field turns on four finite facts:
    the Koszul squares of the jet classes of a line bundle on a smooth curve
    and of a skyscraper are the projections to wedge^2 of the normal space,
    the compensated bivectors of the two eigenplanes of the real
    multiplication annihilate the quartic secant space, the contraction
    matrices of the two classes of the candidate have invertible 20 x 20 and
    12 x 12 minors modulo a prime, and the Chern character of the first
    factor is Theta - (d/6) Theta^3 by the bookkeeping of its construction.
    Section 40 checks them, the second and third in the exterior algebra on
    eight generators.

  * The convolutions of line bundles on E^(2n), E = C/Z[i], turn on four
    finite facts: the 2 * 4^(n-1) bundles L_zeta with prod zeta = +-1 give a
    signed sum of exponentials equal to 2 * 4^(n-1) (alpha + conj alpha), a
    count of powers of i; the graphs of pairs carrying a cup product at n = 3
    have 4 and 16 components, so the cup products leave 204 + 45 = 249 of the
    525 diagonal classes; a run through the multiples of the polarisation has
    excess at least 2n - 4; and the one surviving path has Ext degrees
    0, 6, 0, which fixes its shifts, its signs and the threshold 192.
    Section 41 checks them.

Everything is settled by `decide`, in five cases by its kernel-only form
`decide +kernel`, so the kernel checks it.  There is no
`sorry` and no dependence on Mathlib.
-/

set_option maxRecDepth 20000

namespace HodgeObstruction

/-! ## 1.  The character separation

An element of `Z[sqrt(-d)]` is a pair `(a, b)` standing for `a + b*sqrt(-d)`.
-/

abbrev Quad := Int × Int

/-- Multiplication in `Z[sqrt(-d)]`. -/
def qmul (d : Int) (x y : Quad) : Quad :=
  (x.1 * y.1 - d * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Complex conjugation. -/
def qconj (x : Quad) : Quad := (x.1, -x.2)

/-- The norm `N(tau) = tau * conj(tau)`, a rational integer. -/
def qnorm (d : Int) (x : Quad) : Int := x.1 * x.1 + d * x.2 * x.2

/-- Powers. -/
def qpow (d : Int) (x : Quad) : Nat → Quad
  | 0 => (1, 0)
  | k + 1 => qmul d (qpow d x k) x

/-- A rational integer, viewed in `Z[sqrt(-d)]`. -/
def qint (m : Int) : Quad := (m, 0)

def ipow (m : Int) : Nat → Int
  | 0 => 1
  | k + 1 => ipow m k * m

/-- The norm is multiplicative, checked on the data used below. -/
theorem qnorm_mul_check :
    ([1, 2, 3, 7, 11, 19].all fun d =>
      [((2 : Int), (1 : Int)), (1, 1), (3, 2), (1, 2)].all fun x =>
        [((1 : Int), (1 : Int)), (2, 1), (1, 3)].all fun y =>
          qnorm d (qmul d x y) == qnorm d x * qnorm d y) = true := by decide

/-- `tau * conj(tau)` really is the norm. -/
theorem qmul_conj :
    ([1, 2, 3, 7, 11, 19].all fun d =>
      [((2 : Int), (1 : Int)), (1, 1), (3, 2), (1, 2), (5, 3)].all fun x =>
        qmul d x (qconj x) == qint (qnorm d x)) = true := by decide

/-- **The characters differ.**  For every squarefree `d` in the list and every
`n` from `1` to `8`, the element `tau = 2 + sqrt(-d)` satisfies
`tau^(2n) != N(tau)^n`.  Since `tau^(2n)` is the character by which `K^x` acts
on the Weil line and `N(tau)^n` the one by which it acts on `eta^n`, the two
characters are distinct and their isotypic components meet in zero. -/
theorem characters_differ :
    ([1, 2, 3, 7, 11, 19, 43, 67, 163].all fun d =>
      [1, 2, 3, 4, 5, 6, 7, 8].all fun n =>
        qpow d (2, 1) (2 * n) != qint (ipow (qnorm d (2, 1)) n)) = true := by
  decide

/-- The same with other witnesses, to show the phenomenon is not an accident
of the choice of `tau`.  The element `1 + sqrt(-d)` is deliberately absent; see
`bad_witness` below. -/
theorem characters_differ' :
    ([1, 2, 3, 7, 11].all fun d =>
      [1, 2, 3, 4, 5, 6].all fun n =>
        [((4 : Int), (1 : Int)), (3, 2), (5, 2), (2, 3), (5, 1)].all fun t =>
          qpow d t (2 * n) != qint (ipow (qnorm d t) n)) = true := by decide

/-- **Not every witness works, and this is the whole subtlety of Lemma 4.4.**
For `tau = 1 + sqrt(-1)` the ratio `tau / conj(tau)` is `sqrt(-1)`, a primitive
fourth root of unity, so the two characters agree at that single `tau` when
`4 | n`; and for `tau = 1 + sqrt(-3)` the ratio is a primitive sixth root of
unity, so they agree when `3 | n`.  A proof of Lemma 4.4 must therefore choose
its witness, and cannot argue from an arbitrary one. -/
theorem bad_witness :
    (qpow 1 (1, 1) (2 * 4) == qint (ipow (qnorm 1 (1, 1)) 4))
  ∧ (qpow 3 (1, 1) (2 * 3) == qint (ipow (qnorm 3 (1, 1)) 3)) := by decide

/-- The exceptional pairs are exactly those two, within the range searched:
for `tau = 1 + sqrt(-d)` the characters agree only when the ratio is a root of
unity of order dividing `n`, which happens only for `d = 1` with `4 | n` and
`d = 3` with `3 | n`. -/
theorem bad_witness_exceptions :
    ([1, 2, 3, 7, 11, 19].all fun d =>
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].all fun n =>
        (qpow d (1, 1) (2 * n) == qint (ipow (qnorm d (1, 1)) n))
          == ((d == 1 && n % 4 == 0) || (d == 3 && n % 3 == 0)))
      = true := by decide

/-- The two characters agree exactly when `tau^n = conj(tau)^n`, and the
witnesses above show this fails.  Recorded separately because it is the form
in which the statement is used in the paper. -/
theorem ratio_not_root_of_unity :
    ([1, 2, 3, 7, 11, 19].all fun d =>
      [1, 2, 3, 4, 5, 6, 7, 8].all fun n =>
        qpow d (2, 1) n != qpow d (qconj (2, 1)) n) = true := by decide

/-! ## 2.  The sign in the Fourier-Mukai closed form

Generators are numbered `1 .. 2g` for the `e`'s and `2g+1 .. 4g` for the
`f`'s.  For a `k`-subset `T` of `{1,..,g}` the contributing term is the word

    (prod_{j in T} f_j f_{g+j}) . (prod_{i in S} e_i f_i),   S = complement,

and it is compared with the target word

    (prod_{j in U} e_j e_{g+j}) . (f_1 ... f_{2g}),          U = {1..g} \ T.

The sign is the product of the two sorting signs.
-/

/-- Sign of the permutation sorting a list of distinct naturals. -/
def sortSign : List Nat → Int
  | [] => 1
  | x :: xs =>
      (if (xs.filter (fun y => decide (y < x))).length % 2 == 1 then -1 else 1)
        * sortSign xs

def upto (n : Nat) : List Nat := (List.range n).map (· + 1)

/-- The word attached to an index set `T`. -/
def wordOf (g : Nat) (T : List Nat) : List Nat :=
  let S := (upto (2 * g)).filter (fun i => !T.contains i && !T.contains (i - g))
  (T.flatMap fun j => [2 * g + j, 2 * g + g + j]) ++
    (S.flatMap fun i => [i, 2 * g + i])

/-- The target word attached to the complementary set `U`. -/
def targetOf (g : Nat) (T : List Nat) : List Nat :=
  let U := (upto g).filter (fun j => !T.contains j)
  (U.flatMap fun j => [j, g + j]) ++ (upto (2 * g)).map (fun i => 2 * g + i)

def termSign (g : Nat) (T : List Nat) : Int :=
  sortSign (wordOf g T) * sortSign (targetOf g T)

/-- All `k`-subsets of `{1,..,g}`. -/
def subsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (subsets k xs).map (x :: ·) ++ subsets (k + 1) xs

def predSign (g k : Nat) : Int :=
  if (g * (g + 1) / 2 + k) % 2 == 0 then 1 else -1

/-- **The sign is uniform over index sets and equal to the closed form.**
This is the step in the proof of Theorem 5.4 that the reader is most likely to
want checked. -/
theorem sign_uniform_and_closed :
    ([1, 2, 3, 4, 5].all fun g =>
      (List.range (g + 1)).all fun k =>
        (subsets k (upto g)).all fun T =>
          termSign g T == predSign g k) = true := by decide

/-- The subset enumeration is the right one: there are `C(g,k)` of them. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem subsets_count :
    ([1, 2, 3, 4, 5, 6].all fun g =>
      (List.range (g + 1)).all fun k =>
        (subsets k (upto g)).length == choose g k) = true := by decide

/-! ## 3.  The semiregularity target -/

/-- `sum_q C(2n,q) * C(2n,q+2) = C(4n, 2n-2)`, which is Proposition 8.2. -/
theorem semiregularity_target :
    ([1, 2, 3, 4, 5, 6, 7].all fun n =>
      ((List.range (2 * n + 1)).map
        (fun q => choose (2 * n) q * choose (2 * n) (q + 2))).sum
        == choose (4 * n) (2 * n - 2)) = true := by decide

/-! ## 4.  The numerical comparison of Section 7 -/

def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

def pow3 : Nat → Nat
  | 0 => 1
  | k + 1 => 3 * pow3 k

/-- `2n^2 + 2n < 2^(2n) < 3^(2n)` for `2 <= n <= 8`. -/
theorem secant_count_below_thresholds :
    ([2, 3, 4, 5, 6, 7, 8].all fun n =>
      decide (2 * n * n + 2 * n < pow2 (2 * n))
        && decide (pow2 (2 * n) < pow3 (2 * n))) = true := by decide

/-- The two counterexamples of Proposition 7.3, which show that neither
threshold is a necessary condition: an abelian surface carries a
base-point-free system with `chi = 3 < 4` and a very ample one with
`chi = 5 < 9`. -/
theorem thresholds_not_necessary :
    decide (3 < pow2 2) && decide (5 < pow3 2) = true := by decide

/-! ## 5.  The positions in the character grading -/

/-- The Weil line sits at `(2n,0)` and `(0,2n)`, and `eta^n` at `(n,n)`; these
are different cells of the grading for every `n >= 1`. -/
theorem grading_positions_differ :
    ([1, 2, 3, 4, 5, 6, 7, 8].all fun n =>
      ((2 * n, 0) != (n, n)) && ((0, 2 * n) != ((n : Nat), (n : Nat))))
      = true := by decide


/-! ## 6.  The coordinate formula for the Weil classes

Write `delta` for `sqrt(-d)`, that is the element `(0,1)` of `Z[sqrt(-d)]`.
The two generators of the Weil line are

    omega_1 = sum over even |T| of (-1)^(|T|/2) d^(n - |T|/2) w^(T),
    omega_2 = sum over odd  |T| of (-1)^((|T|-1)/2) d^(n - (|T|+1)/2) w^(T),

and both have rational coefficients.  That rests on exactly one fact about the
arithmetic of `Z[sqrt(-d)]`: a power of `delta` is rational precisely in even
degree, with the closed value `(-d)^m` there, and in odd degree it is `delta`
times `(-d)^m`.  All three statements are verified below.
-/

def qdelta : Quad := (0, 1)

/-- **A power of `sqrt(-d)` is rational exactly in even degree.**  This is why
the even part of the expansion gives `omega_1` and the odd part, divided by
`delta`, gives `omega_2`. -/
theorem weil_delta_parity :
    ([1, 2, 3, 5, 7, 11, 19].all fun d =>
      (List.range 21).all fun k =>
        ((qpow d qdelta k).2 == 0) == (k % 2 == 0)) = true := by decide

/-- The even powers in closed form: `delta^(2m) = (-d)^m`. -/
theorem weil_delta_closed_even :
    ([1, 2, 3, 5, 7, 11, 19].all fun d =>
      (List.range 11).all fun m =>
        qpow d qdelta (2 * m) == (ipow (-d) m, 0)) = true := by decide

/-- The odd powers in closed form: `delta^(2m+1) = (-d)^m * delta`. -/
theorem weil_delta_closed_odd :
    ([1, 2, 3, 5, 7, 11, 19].all fun d =>
      (List.range 11).all fun m =>
        qpow d qdelta (2 * m + 1) == (0, ipow (-d) m)) = true := by decide

/-- **Each generator has `2^(2n-1)` terms.**  The even subsets and the odd
subsets of a set of size `2n` are equinumerous, and there are `2^(2n-1)` of
each, so `omega_1` and `omega_2` have the same number of monomials. -/
theorem weil_term_counts :
    ([1, 2, 3, 4, 5, 6].all fun n =>
      (((List.range (2 * n + 1)).filter (fun k => k % 2 == 0)).map
          (fun k => choose (2 * n) k)).sum == pow2 (2 * n - 1)
      && (((List.range (2 * n + 1)).filter (fun k => k % 2 == 1)).map
          (fun k => choose (2 * n) k)).sum == pow2 (2 * n - 1)) = true := by
  decide

/-- **The supports are disjoint.**  A monomial of `omega_1` or `omega_2`
contains exactly one of `x_j, y_j` for every `j`, so its pair of index sets is
`(complement T, T)`; a monomial of a power of `eta` contains both or neither,
so its pair is `(S, S)`.  No pair is of both shapes, which is the coordinate
proof that the Weil line meets the divisor subring in zero.  Index sets are
encoded as bit masks below the given bound. -/
def bitsBelow (n : Nat) : List Nat := List.range (pow2 n)

theorem supports_disjoint :
    ([1, 2, 3].all fun n =>
      (bitsBelow (2 * n)).all fun t =>
        (bitsBelow (2 * n)).all fun s =>
          !(decide (s == (pow2 (2 * n) - 1) - t) && decide (s == t)))
      = true := by decide

/-! ## 7.  The count of Hodge classes

After the invariant theory has been done by hand, the surviving statement is a
count.  In degree `2k` the summand indexed by `(r,s)` with `r + s = 2k`
contributes a one-dimensional space of invariants when `r = s`, and also when
`(r,s)` is `(2n,0)` or `(0,2n)`, and nothing otherwise.  Summing gives `3` in
the middle degree and `1` everywhere else.
-/

/-- The contribution of the summand `(r,s)`. -/
def invContribution (n r s : Nat) : Nat :=
  if r == s then 1
  else if (r == 2 * n && s == 0) || (r == 0 && s == 2 * n) then 1
  else 0

/-- The total over one degree. -/
def hdgDim (n k : Nat) : Nat :=
  ((List.range (2 * n + 1)).filter (fun r => decide (r <= 2 * k)
      && decide (2 * k - r <= 2 * n))).foldl
    (fun acc r => acc + invContribution n r (2 * k - r)) 0

/-- **Three in the middle, one everywhere else.** -/
theorem hodge_dim_count :
    ([1, 2, 3, 4, 5, 6].all fun n =>
      (List.range (2 * n + 1)).all fun k =>
        hdgDim n k == (if k == n then 3 else 1)) = true := by decide

/-- The Weil line is of Hodge type `(p, 2n-p)`, so it consists of Hodge classes
exactly when `p = n`. -/
theorem weil_line_hodge_type :
    ([1, 2, 3, 4, 5, 6].all fun n =>
      (List.range (2 * n + 1)).all fun p =>
        (decide ((p, 2 * n - p) == ((n : Nat), (n : Nat)))) == decide (p == n))
      = true := by decide

/-! ## 8.  The Clifford dimensions and the reach of Kuga-Satake -/

/-- `dim C = 2^b`, `dim C^+ = 2^(b-1)`, `dim KS = 2^(b-2)`. -/
theorem clifford_dimensions :
    ([3, 4, 5, 6, 7, 8, 12, 16, 22].all fun b =>
      pow2 b == 2 * pow2 (b - 1) && pow2 (b - 1) == 2 * pow2 (b - 2))
      = true := by decide

/-- **The K3 type condition has `n = 1` as its only solution.**  On an abelian
variety of Weil type the rational sub-Hodge structures of `H^2` have
`h^(2,0)` equal to `0`, `n^2`, `n(n-1)` or a sum of these, and `h^(2,0) = 1`
forces `n = 1`. -/
theorem k3_type_only_at_one :
    ((List.range 60).all fun m =>
      let n := m + 1
      ((decide (n * n == 1) || decide (n * (n - 1) == 1)
        || decide (n * n + n * (n - 1) == 1)) == decide (n == 1)))
      = true := by decide

/-! ## 9.  The dimension of the Weil family -/

/-- The Weil family has dimension `n^2` inside the moduli of principally
polarised abelian `2n`-folds, of dimension `n(2n+1)`, so the codimension is
`n(n+1)` and is positive for every `n >= 1`. -/
theorem moduli_codimension :
    ((List.range 40).all fun m =>
      let n := m + 1
      decide (n * (2 * n + 1) - n * n == n * (n + 1))
        && decide (n * n < n * (2 * n + 1))) = true := by decide



/-! ## 10.  The reach of the split base case

Three finite facts stand behind the determination of what the construction of
the paper actually reaches.

The discriminant.  The split member has `det H = (-d)^n (d_1...d_n)^2`, and
`(-1)^n det H = d^n p^2` with `p` the Pfaffian.  That this is a norm from
`Q(sqrt(-d))` is exhibited by a witness: for `n = 2m` take `(d^m p, 0)`, and
for `n = 2m+1` take `(0, d^m p)`, since `N(a + b sqrt(-d)) = a^2 + d b^2`.

The codimension.  `n^2 - n(n+1)/2 = n(n-1)/2`, which vanishes only at `n = 1`.

-/

def ipowNat (m : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => ipowNat m k * m

/-- **The discriminant of the split member is a norm.**  For every squarefree
`d` in the list, every `n` up to `6` and every Pfaffian `p` in the list, the
witness above satisfies `a^2 + d b^2 = d^n p^2`. -/
theorem discriminant_is_a_norm :
    ([1, 2, 3, 5, 7, 11, 19].all fun d =>
      [1, 2, 3, 4, 5, 6].all fun n =>
        [1, 2, 6, 56, 168].all fun p =>
          let a := if n % 2 == 0 then ipowNat d (n / 2) * p else 0
          let b := if n % 2 == 0 then 0 else ipowNat d (n / 2) * p
          a * a + d * b * b == ipowNat d n * p * p) = true := by decide

/-- **The codimension of the split locus.** -/
theorem split_codimension :
    ((List.range 30).all fun m =>
      let n := m + 1
      decide (n * n - n * (n + 1) / 2 == n * (n - 1) / 2)
        && decide ((n * (n - 1) / 2 == 0) == (n == 1))) = true := by decide



/-! ## 11.  The discriminant reached by quaternionic multiplication

For `B = (-d, b)` acting on `B^n` the hermitian form is
`diag(2 a_k d, -2 a_k b d)`, so `(-1)^n det H = b^n (2^n d^n prod a_k)^2` and
the discriminant class is `b^n`.  Two finite facts follow.

For `n` odd, `b^n` and `b` differ by the square `(b^((n-1)/2))^2`, so every
class is reached by a single quaternionic factor.  For `n` even, `b^n` is
itself a square; a product of a factor of odd dimension with parameter `b` and
one of odd dimension with parameter `d` then has class `b * d^(n-1)`, and `d`
is a norm, so again every class is reached.
-/

/-- The determinant of the hermitian form of the quaternionic model, up to the
square factor, in the normalised form used in the paper. -/
def quatClass (b n : Nat) : Nat := ipowNat b n

/-- **For `n` odd the class is `b` up to a square.** -/
theorem quat_class_odd :
    ([2, 3, 5, 6, 7, 10, 11].all fun b =>
      [1, 3, 5, 7, 9].all fun n =>
        quatClass b n == b * ipowNat b ((n - 1) / 2) * ipowNat b ((n - 1) / 2))
      = true := by decide

/-- **For `n` even the class is a square.** -/
theorem quat_class_even :
    ([2, 3, 5, 6, 7, 10, 11].all fun b =>
      [2, 4, 6, 8].all fun n =>
        quatClass b n == ipowNat b (n / 2) * ipowNat b (n / 2)) = true := by
  decide

/-- **The product construction reaches every class in even dimension.**  A
factor of dimension one with parameter `b` and a factor of dimension `n-1`
with parameter `d` give class `b * d^(n-1)`; since `d = N(sqrt(-d))` is a norm
and `n-1` is odd, the class is `b` times a norm, and the witness for `d^(n-1)`
being a norm is the pair below. -/
theorem quat_product_class :
    ([1, 2, 3, 5, 7, 11].all fun d =>
      [2, 4, 6, 8].all fun n =>
        let m := (n - 1) / 2
        let a := 0
        let c := ipowNat d m
        a * a + d * c * c == ipowNat d (n - 1)) = true := by decide


/-! ## 12.  The quaternionic locus, and the two numbers the properness
reduction turns on

Left multiplication by an indefinite quaternion algebra commuting with `K`
writes `V` over the reals as `W` tensored with the standard plane, and the
complex structures that survive are the complex structures on the symplectic
space `W`.  So the quaternionic locus is the symmetric space of `Sp(2n,R)`,
of dimension `n(n+1)/2`, inside the period domain of dimension `n^2`.

Two further finite facts are used in the same subsection.  One is that a
witness `tau` with `tau^(2n)` irrational can always be found among
`m + sqrt(-d)` with `m` at most `7`.  The other is the determinant identity
that makes a single nonzero algebraic element of the Weil line drag the whole
line with it: for `w = (w1,w2)` and `t = (a,b)` the determinant of the pair
`w, t*w` is `b*(w1^2 + d*w2^2)`, and the second factor is positive whenever
`w` is nonzero and `d` is.
-/

def quatLocusDim (n : Nat) : Nat := n * (n + 1) / 2

def periodDim (n : Nat) : Nat := n * n

/-- **The quaternionic locus has codimension `n(n-1)/2`**, which vanishes only
at `n = 1`. -/
theorem quat_locus_codimension :
    ((List.range 40).all fun m =>
      let n := m + 1
      decide (quatLocusDim n ≤ periodDim n)
        && decide (periodDim n - quatLocusDim n == n * (n - 1) / 2)
        && (decide (periodDim n - quatLocusDim n == 0) == decide (n == 1)))
      = true := by decide

/-- **At `n = 2` the quaternionic locus is a divisor.**  This is the case in
which infinitude of one fibre of the Hilbert data, rather than density,
suffices. -/
theorem quat_locus_divisor_at_two :
    periodDim 2 = 4 ∧ quatLocusDim 2 = 3 ∧ periodDim 2 - quatLocusDim 2 = 1 := by
  decide

/-- **A witness with irrational `tau^(2n)` exists in a short range.**  For
every field listed and every `n` up to `8`, some `m` between `1` and `7` makes
the second coordinate of `(m + sqrt(-d))^(2n)` nonzero, so that `tau^(2n)` is
not rational. -/
theorem irrational_witness_exists :
    ([1, 2, 3, 7, 11, 19, 43, 67, 163].all fun d =>
      [1, 2, 3, 4, 5, 6, 7, 8].all fun n =>
        [1, 2, 3, 4, 5, 6, 7].any fun m =>
          (qpow d ((m : Int), 1) (2 * n)).2 != 0) = true := by decide

/-- **One nonzero element of the Weil line spans it.**  The determinant of the
pair `w, t*w` in the rational basis of the line is `b*(w1^2 + d*w2^2)`, which
is nonzero as soon as `t` is not rational and `w` is not zero. -/
theorem weil_line_spanned :
    ([1, 2, 3, 7, 11].all fun d =>
      [((1 : Int), (0 : Int)), (0, 1), (1, 1), (2, -3), (-5, 2), (3, 4)].all
        fun w =>
        [((2 : Int), (1 : Int)), (0, 1), (3, -2), (1, 5)].all fun t =>
          let tw := qmul d t w
          (w.1 * tw.2 - w.2 * tw.1
            == t.2 * (w.1 * w.1 + d * w.2 * w.2))
          && (w.1 * tw.2 - w.2 * tw.1 != 0)) = true := by decide


/-! ## 13.  The positivity of the norm form

The last obstruction of the paper is a positivity statement.  If a coherent
sheaf on the split member is filtered by line bundles whose first Chern
classes are `e_i eta + theta_i`, and if its second Chern character is a flat
Hodge class, then the coefficient of `theta^+ theta^-` gives

    sum_i m_i N(u_i) = 0,     m_i >= 1,     u_i in K,

and the norm form `N(a + b sqrt(-d)) = a^2 + d b^2` is positive definite, so
every `u_i` vanishes.  Two finite facts stand behind that step.
-/

/-- **The norm form of an imaginary quadratic field is positive definite.** -/
theorem norm_form_positive :
    ([1, 2, 3, 5, 7, 11, 19, 43, 67, 163].all fun d =>
      (List.range 13).all fun i =>
        (List.range 13).all fun j =>
          let a : Int := (i : Int) - 6
          let b : Int := (j : Int) - 6
          (a == 0 && b == 0) || decide (0 < a * a + d * b * b)) = true := by
  decide

/-- **A positive combination of norms vanishes only when every term does.**
Checked for two summands, multiplicities up to three and coordinates in a
box; the general statement is the same one line of arithmetic. -/
theorem norm_sum_forces_zero :
    ([1, 2, 3, 7].all fun d =>
      [1, 2, 3].all fun m1 =>
        [1, 2, 3].all fun m2 =>
          (List.range 5).all fun i =>
            (List.range 5).all fun j =>
              (List.range 5).all fun k =>
                (List.range 5).all fun l =>
                  let a1 : Int := (i : Int) - 2
                  let b1 : Int := (j : Int) - 2
                  let a2 : Int := (k : Int) - 2
                  let b2 : Int := (l : Int) - 2
                  let t : Int := m1 * (a1 * a1 + d * b1 * b1)
                                 + m2 * (a2 * a2 + d * b2 * b2)
                  decide (t != 0)
                    || (a1 == 0 && b1 == 0 && a2 == 0 && b2 == 0)) = true := by
  decide

/-- **The rank bound behind the search at `n = 2`.**  The semiregularity map
of a sum of `s` line bundles has source of dimension `s * C(2n,2)` and target
of dimension `sum_q C(2n,q) C(2n,q+2)`; at `n = 2` the source overtakes the
target at `s = 5`, and the computation of Section 16 shows it is already not
injective at `s = 4`. -/
theorem semiregularity_source_target :
    (([1, 2, 3, 4].all fun s => decide (s * 6 <= 28))
      && decide (5 * 6 > 28)
      && decide (3 * 6 < 28)) = true := by decide

/-- **The tensor rank gap.**  In the isotypic component for the norm character
squared, `eta^2` has tensor rank `C(2n,2)` and `theta^+ theta^-` has rank one,
so the two are proportional only when `C(2n,2) = 1`, which never happens for
`n >= 2`. -/
theorem tensor_rank_gap :
    ((List.range 40).all fun m =>
      let n := m + 2
      decide (6 <= choose (2 * n) 2) && decide (choose (2 * n) 2 != 1))
      = true := by decide


/-! ## 14.  The secant witness in line bundles

Theorem 14.13 produces a coherent sheaf whose Chern character is a positive
multiple of a rational point of the secant plane, and the multiple together
with the witness is obtained by inverting a Vandermonde matrix.  Two things
are finite there and are checked here: that the Vandermonde nodes are
distinct, so the system is solvable at all, and that the witness recorded in
the paper reproduces the target in every degree.
-/

/-- integer powers by recursion, so that `decide` can evaluate them. -/
def zpow : Int → Nat → Int
  | _, 0 => 1
  | a, (k + 1) => a * zpow a k

/-- the coordinates of `a u_t + b v_t` in the basis `t^k / k!`. -/
def secantTarget (d a b : Int) (k : Nat) : Int :=
  if k % 2 = 0 then a * zpow (-d) (k / 2) else b * zpow (-d) (k / 2)

/-- the witness of Theorem 14.13 at `n = 4`, `d = 3`, `a = b = 1`. -/
def witness4 : List Int := [-23, 66, -54, 20, -3]

/-- `sum_j n_j j^k`, the `k`-th moment of a witness on the nodes `0, 1, ...`. -/
def moment (w : List Int) (k : Nat) : Int :=
  (List.range w.length).foldl (fun s j => s + (w.getD j 0) * zpow (j : Int) k) 0

/-- **The witness reproduces the target in every degree.**  At `n = 4`,
`d = 3`, `a = b = 1` the least multiple is `M = 6`. -/
theorem secant_witness_at_n_four :
    ((List.range 5).all fun k =>
      moment witness4 k == 6 * secantTarget 3 1 1 k) = true := by decide

/-- **The witness has the rank the construction needs**, namely `M a = 6`,
which is positive, so Lemma 14.12 applies to it. -/
theorem secant_witness_rank :
    (witness4.foldl (· + ·) 0 == (6 : Int)) = true := by decide

/-- the Vandermonde product on the nodes `0, 1, ..., n`. -/
def vdm (n : Nat) : Nat :=
  (List.range (n + 1)).foldl
    (fun acc j => acc * ((List.range j).foldl (fun a i => a * (j - i)) 1)) 1

/-- **The Vandermonde matrix on the nodes `0, ..., n` is nonsingular**, so the
system that produces the witness has a unique rational solution. -/
theorem vandermonde_nodes_distinct :
    ((List.range 8).all fun n => decide (0 < vdm (n + 1))) = true := by decide

/-! ## 15.  The level sums of a split object supported on R

Theorem 14.40 turns the diagonal part of the Chern character conditions into
`sum_j M_j N_j^r = 0` for `r = 1, ..., n`, and at `n+1` distinct norms the
`M_j` are forced.  The identities below are the ones the search of item (XXII)
rests on: that the recorded level sums do satisfy the conditions, that the
matrix is nonsingular when there are at most `n` norms, so that the level sums
vanish there, and that the supply of elements of a given norm is what blocks
the smallest case.
-/

/-- `sum_j M_j N_j^r = 0` for `r = 1, 2, 3`, the conditions at `n = 3`. -/
def levelCheck (N M : List Int) : Bool :=
  (List.range 3).all fun r =>
    ((List.range N.length).foldl
      (fun s j => s + (M.getD j 0) * zpow (N.getD j 0) (r + 1)) 0) == 0

/-- **The level sums recorded in Theorem 14.40 satisfy the conditions.** -/
theorem level_sums_forced :
    (levelCheck [1, 2, 3, 4] [4, -6, 4, -1]
      && levelCheck [9, 18, 27, 36] [4, -6, 4, -1]
      && levelCheck [27, 54, 81, 108] [4, -6, 4, -1]
      && levelCheck [33, 66, 99, 132] [4, -6, 4, -1]
      && levelCheck [5, 20, 45, 50] [5, -3, 3, -2]
      && levelCheck [4, 9, 40, 45, 49] [-4, 2, 2, -4, 2]) = true := by decide

/-- **Their totals are the rank of the object**, which must not vanish. -/
theorem level_sums_totals :
    ((([4, -6, 4, -1] : List Int).foldl (· + ·) 0 == 1)
      && (([5, -3, 3, -2] : List Int).foldl (· + ·) 0 == 3)
      && (([-4, 2, 2, -4, 2] : List Int).foldl (· + ·) 0 == -2)) = true := by
  decide

/-- the determinant of `(N_j^r)`, `r = 1, ..., nu`, on distinct positive nodes. -/
def levelDet (N : List Int) : Int :=
  (List.range N.length).foldl
    (fun acc j => acc * (N.getD j 0) *
      ((List.range j).foldl (fun a i => a * ((N.getD j 0) - (N.getD i 0))) 1)) 1

/-- **With at most `n` distinct norms the matrix is nonsingular**, so every
level sum vanishes and the object has rank zero; that is Corollary 14.36. -/
theorem level_matrix_nonsingular :
    ([[1, 2, 3], [1, 2, 4], [2, 3, 5], [5, 20, 45], [9, 18, 27]].all fun N =>
      decide (levelDet N != 0)) = true := by decide

/-- the number of Gaussian integers of a given norm, counted in a box that
contains every one of them for the norms used below. -/
def gaussCount (N : Nat) : Nat :=
  (List.range 15).foldl (fun (s : Nat) (i : Nat) =>
    s + (List.range 15).foldl (fun (t : Nat) (j : Nat) =>
      let x : Int := (i : Int) - 7
      let y : Int := (j : Int) - 7
      t + (if x * x + y * y == (N : Int) then (1 : Nat) else 0)) 0) 0

/-- **The supply of elements of a given norm.** -/
theorem gauss_norm_counts :
    (gaussCount 1 == 4 && gaussCount 2 == 4 && gaussCount 3 == 0
      && gaussCount 4 == 4 && gaussCount 5 == 8 && gaussCount 9 == 4
      && gaussCount 45 == 8) = true := by decide

/-- **The smallest level set is blocked by the supply.**  At the nodes
`1, 2, 3, 4` the forced level sums have `|M_3| = 4`, and the ring of Gaussian
integers has no element of norm `3` at all. -/
theorem norm_supply_blocks_small_case :
    (gaussCount 3 == 0 && decide (gaussCount 3 < 4)) = true := by decide


/-! ## 16.  The pencil of quaternionic loci at `n = 2`

The minors of the matrix with rows `x_k` and `i.x_k` are integer polynomials
of degree at most two in `k`.  For `d = 1` two of them are
`P(k) = -2 - 2k - k^2` and `Q(k) = -2k - k^2`, and `Q - P = 2` identically;
for `d = 3` one minor is the constant `-4`.  A polynomial of degree at most
two that vanishes at three integers vanishes identically, so the checks below
over `-200 <= k <= 200` establish the polynomial identities, and hence the
bounds `N_1 = 2`, `N_3 = 4` on the index for every integer `k`.
-/

/-- The integers from `-200` to `200`. -/
def kRange : List Int := (List.range 401).map fun n => ((n : Nat) : Int) - 200

/-- `d = 1`: the two minors differ by the constant `2` at every `k`, so the gcd
of their values divides `2`. -/
theorem pencil_index_d1 :
    (kRange.all fun k => decide ((0 - 2*k - k*k) - (-2 - 2*k - k*k) = 2)) = true := by
  decide

/-- `d = 3`: the minor `-4` is constant, and the second listed minor is
`-12 - 24k - 12k^2 = -12 (k+1)^2`; the gcd of the two values divides `4`. -/
theorem pencil_index_d3 :
    (kRange.all fun k =>
      decide (Int.gcd (-12 - 24*k - 12*k*k) (-4) ∣ 4)) = true := by
  decide

/-- `4 beta_1(k) = 2 + 2k + k^2` and `9 beta_3(k) = 1 + 2k^2` are positive on
the range, and their discriminants are `-4` and `-8`. -/
theorem pencil_beta_positive :
    (kRange.all fun k => decide (2 + 2*k + k*k > 0 ∧ 1 + 2*k*k > 0)) = true
      ∧ (2*2 - 4*1*2 : Int) = -4 ∧ (0*0 - 4*2*1 : Int) = -8 := by
  decide

/-- The two members of the pencil with `beta(k)` a rational square: `beta_1(-1)
= 1/4` and `beta_3(-2) = 1`. -/
theorem pencil_square_members :
    (2 + 2*(-1 : Int) + (-1)*(-1) = 1) ∧ (1 + 2*(-2 : Int)*(-2) = 9) := by
  decide


/-! ## 17.  The obstruction map of a split object

At a split member the tangent space `T` of the Weil family has dimension
`n^2` and the tangent space of the split locus has dimension `n(n+1)/2`; the
obstruction map of a split object whose classes span the Neron-Severi group
has kernel the latter, so its rank is `n(n-1)/2`, and the even side of the
semiregularity kernel, of dimension `n(n-1)`, is twice that rank.  For the
explicit object at `n = 3` the kernel of the semiregularity map has dimension
`15 = 9 + 6`, the copy of `T` inside it has dimension `9`, the image of the
obstruction map has dimension `3`, the two meet only in zero, and their sum
of dimension `12` leaves a complement of dimension `3`.
-/

/-- The rank of the obstruction map and the even side of the kernel, for
`1 <= n <= 30`: `n^2 - n(n+1)/2 = n(n-1)/2` and `n(n-1) = 2 * (n(n-1)/2)`. -/
theorem split_obstruction_rank :
    ((List.range 30).all fun m =>
      let n := m + 1
      decide (n * n - n * (n + 1) / 2 == n * (n - 1) / 2)
        && decide (n * (n - 1) == 2 * (n * (n - 1) / 2))) = true := by decide

/-- The bookkeeping of the explicit object at `n = 3`: kernel `15 = 9 + 6`,
tangent copy `9 = n^2`, obstruction image `3 = n(n-1)/2`, direct sum `12`,
complement `3`. -/
theorem split_obstruction_count :
    (3 * 3 + 3 * (3 - 1) = 15) ∧ (3 * (3 - 1) / 2 = 3) ∧ (9 + 3 = 12)
      ∧ (15 - 12 = 3) ∧ (12 ≤ 15) := by decide


/-! ## 18.  The evaluation map cannot be surjective

For an abelian `2n`-fold the Hochschild cohomology `HH^2` has dimension
`2 C(2n,2) + 4n^2`, the sum of `h^{0,2}`, `h^1(T)` and `h^0(wedge^2 T)`; for a
sum of `s` line bundles with vanishing off-diagonal `Ext^2` the group
`Ext^2(E,E)` has dimension `s C(2n,2)`.  The inequality
`s C(2n,2) > 2 C(2n,2) + 4n^2` is `(s-2)(2n-1) > 4n`, true for all `s >= 5`
and `n >= 2`.
-/

/-- `C(2n,2) = n(2n-1)`, and the evaluation map is not surjective for
`5 <= s <= 40` summands and `2 <= n <= 30`; at `n = 3`, `s = 6` the two
dimensions are `66` and `90`, and the kernel of the semiregularity map, of
dimension `15 = 9 + 6`, lies in the image. -/
theorem evaluation_not_surjective :
    ((List.range 29).all fun m =>
      let n := m + 2
      (List.range 36).all fun t =>
        let s := t + 5
        decide (s * (n * (2 * n - 1)) > 2 * (n * (2 * n - 1)) + 4 * n * n)) = true
      ∧ (2 * (3 * (2 * 3 - 1)) + 4 * 3 * 3 = 66)
      ∧ (6 * (3 * (2 * 3 - 1)) = 90)
      ∧ (9 + 6 = 15) := by decide


/-! ## 19.  Markman's candidate in dimension eight

With `N = (d+9)/2` divisors, `d` odd: the isolated self-intersection points
number `12 N (N-5) = (d+9)(3d-3)`, at least the `(d+9)(2d-1)` that are
normalised; the Euler characteristic of the partially normalised union is
`110 N - 12 N^2 + 2N(2d-1) = (d+9)(27-d)`; the degree two and four
components of the Chern character then match the secant point `(1,3)`, which
is the pair of identities `9 - 2N = -d` and `81 + 36 N - (d+9)(27-d) = d^2`;
the norm of `3 + sqrt(-d)` is `2N`; and the ranks `8d(d-9)`, `8d(d+9)` of the
transforms are nonzero for `d` not equal to `9`.
-/

theorem markman_candidate_identities :
    ((List.range 100).all fun t =>
      let d : Int := 2 * t + 3
      let N : Int := (d + 9) / 2
      decide (12 * N * (N - 5) = (d + 9) * (3 * d - 3))
        && decide ((d + 9) * (2 * d - 1) ≤ 12 * N * (N - 5))
        && decide (110 * N - 12 * N * N + 2 * N * (2 * d - 1) = (d + 9) * (27 - d))
        && decide (9 - 2 * N = -d)
        && decide (81 + 36 * N - (d + 9) * (27 - d) = d * d)
        && decide (3 * 3 + d = 2 * N)
        && decide (8 * d * (d + 9) ≠ 0)
        && decide (d = 9 ∨ 8 * d * (d - 9) ≠ 0)) = true := by decide

/-! ## 20.  The classes preserving a secant Chern character

For `ch(F) = a u_t + b v_t` write `ch(F) = sum c_k t^k` and `C_k = k! c_k`, so
`C_k = a (-d)^(k/2)` for `k` even and `C_k = b (-d)^((k-1)/2)` for `k` odd.
The classes in `HT^2` preserving `ch(F)` are cut out, in the two lowest
Hodge types, by the matrix `[[a, b], [b, -a d]]` acting on `(Z, W)`, of
determinant `-(a^2 d + b^2)`, which is nonzero for `(a, b) != (0, 0)`; and
the coefficient of `Z` in every higher type is the same combination because
`C_(k+1) = -d C_(k-1)`.  The kernel is then the polarised deformations plus
the compensated Poisson classes, `n(n+1)/2 + n(n-1)/2 = n^2` in all.
-/

/-- `C_k = k! c_k` for the secant character `a u_t + b v_t`. -/
def secantCoeff (d a b : Int) : Nat → Int
  | 0 => a
  | 1 => b
  | k + 2 => -d * secantCoeff d a b k

theorem secant_kernel_arithmetic :
    (((List.range 13).all fun a => (List.range 13).all fun b =>
        (List.range 20).all fun d =>
          let a' : Int := a
          let b' : Int := b
          let d' : Int := d + 1
          (a == 0 && b == 0) || decide (a' * (-a' * d') - b' * b' ≠ 0)
            && decide (a' * (-a' * d') - b' * b' = -(a' * a' * d' + b' * b')))
      && ((List.range 12).all fun k =>
          [1, 2, 3, 5, 7].all fun d =>
            [((1 : Int), (1 : Int)), (1, 3), (2, 1), (0, 1), (3, 0)].all fun ab =>
              secantCoeff d ab.1 ab.2 (k + 2) == -d * secantCoeff d ab.1 ab.2 k)
      && ((List.range 60).all fun n =>
          n * (n + 1) / 2 + n * (n - 1) / 2 == n * n)) = true := by decide

/-! ## 21.  The unnormalised double points of Markman's candidate

With `N = (d+9)/2` and `d` odd, the isolated double points of the support
number `12 N (N-5) = (d+9)(3d-3)`, of which `(d+9)(2d-1)` are normalised;
the difference `(d+9)(d-2)` is at least `12` for `d >= 3`, so a point of type
(i) of the local lemma always exists.  Normalising every isolated point would
give the Euler characteristic `110 N - 12 N^2 + 12 N (N-5) = 50 N`, and the
secant plane needs `(d+9)(27-d) = 72 N - 4 N^2`; these differ for every
integer `N`, the equation `4 N^2 = 22 N` having no integer solution but `0`.
-/

theorem candidate_unnormalised_points :
    (((List.range 100).all fun t =>
        let d : Int := 2 * t + 3
        let N : Int := (d + 9) / 2
        decide ((d + 9) * (3 * d - 3) - (d + 9) * (2 * d - 1) = (d + 9) * (d - 2))
          && decide ((d + 9) * (d - 2) ≥ 12)
          && decide (110 * N - 12 * N * N + 12 * N * (N - 5) = 50 * N)
          && decide (50 * N ≠ 72 * N - 4 * N * N))
      && ((List.range 200).all fun n => n = 0 || 4 * n * n ≠ 22 * n)) = true := by decide


/-! ## 22.  A rank one secant object with smooth support

Theorem 14.118 reads the invariants of a smooth support off the Chern
character.  Writing `N = (b^2+d)/2` for the class multiple, the five numbers
are, cleared of the halves,

    chi = (b^2+d)(3b^2-d),   K^2 = 3(b^2+d)(7b^2-d),   e = 3(b^2+d)(5b^2-3d),
    K^2 + e = 12 chi        (Noether),
    K^2 - e = 6(b^2+d)^2    (self-intersection, since 24 N^2 = 6(b^2+d)^2),
    3 e - K^2 = 24 (b^4 - d^2).

The last line is the whole of the Bogomolov-Miyaoka-Yau inequality: it is
non-negative exactly when `d <= b^2`.  All four are polynomial identities in
`b` and `d`, and the kernel checks them over a box.
-/

/-- `chi(O_S)`, cleared of halves. -/
def sChi (b d : Int) : Int := (b * b + d) * (3 * b * b - d)

/-- `K_S^2`. -/
def sK2 (b d : Int) : Int := 3 * (b * b + d) * (7 * b * b - d)

/-- `e(S)`. -/
def sE (b d : Int) : Int := 3 * (b * b + d) * (5 * b * b - 3 * d)

/-- **Noether's formula and the self-intersection formula.** -/
theorem smooth_invariants :
    ((List.range 12).all fun i =>
      (List.range 40).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        (sK2 b d + sE b d == 12 * sChi b d)
          && (sK2 b d - sE b d == 6 * (b * b + d) * (b * b + d))) = true := by
  decide

/-- **The Bogomolov-Miyaoka-Yau defect is `24(b^4 - d^2)`.** -/
theorem smooth_bmy_defect :
    ((List.range 12).all fun i =>
      (List.range 40).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        3 * sE b d - sK2 b d == 24 * (b * b * b * b - d * d)) = true := by
  decide

/-- **So the inequality is exactly `d <= b^2`.** -/
theorem smooth_bmy_is_d_le_bsq :
    ((List.range 12).all fun i =>
      (List.range 60).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        decide (sK2 b d <= 3 * sE b d) == decide (d <= b * b)) = true := by
  decide

/-- **The Hodge index bound never binds.**  It reads `9N >= 4b^2`, that is
`9(b^2+d) >= 8b^2`, which holds for every `d >= 1`. -/
theorem smooth_index_vacuous :
    ((List.range 12).all fun i =>
      (List.range 60).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        decide (9 * (b * b + d) >= 8 * b * b)) = true := by decide

/-- squarefree, by trial division. -/
def sqFree (m : Nat) : Bool :=
  (List.range (m + 1)).all fun k => k < 2 || m % (k * k) != 0

/-- **The four discriminants at `b = 3`.**  The squarefree `d` with
`d <= 9` and `(9+d)/2` an integer are exactly `1, 3, 5, 7`. -/
theorem smooth_four_discriminants :
    (((List.range 60).map fun j => j + 1).filter fun d =>
      sqFree d && decide (d <= 9) && (d % 2 == 1)) = [1, 3, 5, 7] := by decide

/-- **The table of Theorem 14.118 at `b = 3`.** -/
theorem smooth_table :
    (([1, 3, 5, 7] : List Int).map fun d =>
      (sChi 3 d, sK2 3 d, sE 3 d))
      = [(260, 1860, 1260), (288, 2160, 1296),
         (308, 2436, 1260), (320, 2688, 1152)] := by decide


/-! ## 23.  Cohen-Macaulay supports with a split resolution

Theorem 14.126 turns the Chern character condition for a support resolved by
sums of line bundles into four equations on the twists,

    sum_i p_i^k - sum_j q_j^k = c_k ,   c = (1, b, -d, -d b, d^2),

for k = 0..4.  Three of them combine, under the weight w(x) = x^2 + d, into
the statement that two positive measures share mass, mean and variance: the
combinations c_{k+2} + d c_k vanish for k = 0, 1, 2.  At r = 1 that forces the
two divisor degrees to satisfy p + q = 2b/3 and p q = (b^2/3 + d)/2, and the
quadratic with that sum and product has discriminant -2b^2/9 - 2d, which is
negative for every d >= 1.  The kernel checks all of this, cleared of
denominators: 9 times the discriminant is -2b^2 - 18d.
-/

/-- the target coefficients c_k for k = 0,1,2,3,4. -/
def burchC (b d : Int) : Nat → Int
  | 0 => 1
  | 1 => b
  | 2 => -d
  | 3 => -d * b
  | _ => d * d

/-- **The weight `x^2 + d` annihilates three moments.** -/
theorem burch_weight_identities :
    ((List.range 12).all fun i =>
      (List.range 60).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        (List.range 3).all fun k =>
          burchC b d (k + 2) + d * burchC b d k == 0) = true := by decide

/-- **At `r = 1` the two divisor degrees are not real.**  Nine times the
discriminant of the forced quadratic is `-2b^2 - 18d`, always negative. -/
theorem burch_rank_one_discriminant :
    ((List.range 12).all fun i =>
      (List.range 60).all fun j =>
        let b : Int := (i : Int) + 1
        let d : Int := (j : Int) + 1
        decide (-2 * b * b - 18 * d < 0)) = true := by decide

/-- **The first candidate at rank four solves the moment system**, and is
removed only by the injectivity of the map: `max q` exceeds `max p`. -/
theorem burch_rank_four_witness :
    (((List.range 4).all fun m =>
      let k := m + 1
      (([-8, -5, 0, 1, 2] : List Int).foldl (fun s x => s + x ^ k) 0
        - ([-7, -6, -4, 4] : List Int).foldl (fun s x => s + x ^ k) 0)
        == burchC 3 23 k)
      && decide ((2 : Int) < 4)) = true := by decide

/-! ## 24.  The closure graph: what is left, as a Horn system

Item (XXXIII) of the verification section carries the logical skeleton of the
paper as data: forty-two statements, each proved here, quoted from the
literature, or open, and twenty-two inference rules, each of which is one
theorem of the paper or of the literature it quotes.  This section repeats
that computation in the kernel.

The statements are numbered

    0  HC              the Hodge conjecture          18  sing_vanish
    1  HC_ab                                         19  base_point
    2  weil_all                                      20  reduction
    3  weil_iq                                       21  orbit_dense
    4  weil_triv                                     22  factor
    5  weil_nontriv                                  23  class_cond
    6  s1                                            24  cm_line
    7  w4triv                                        25  ingredients
    8  known                                         26  mar2
    9  red_ab                                        27  mar3
   10  red_weil                                      28  base_point_cm
   11  weil_cm  (derived: every CM field)            29  reduction_cm
   12  P2_iq_s  ((P2), split, quadratic)             30  orbit_dense_cm
   13  secant_all                                    31  lef_B   (Lefschetz B)
   14  Q114                                          32  mot     (all motivated)
   15  smooth_exists                                 33  vhc     (variational)
   16  smooth_vanish                                 34  mot_def (Andre)
   17  sing_exists                                   35  acc_ab  (Deligne, Andre)
                                                     36  red_ab_mod (F3')
   37  P2_iq_ns ((P2), other discriminants)          40  weil_cm_triv
   38  P2_cm_s  ((P2), split, degree >= 4)           41  weil_cm_nontriv
   39  P2_cm_ns ((P2), the rest, degree >= 4)

with 19 to 30, 34 and 35 proved here or quoted, 9, 10, 12 to 18, 31 to 33
and 36 to 39 open, and the rest derived.  The propagation statement (P2) is
carried family by family.  The rules `[4]` gives 5 and `[40]` gives 41 are
descent: `B x Y`, with `Y` of `(F,1)`-Weil type of any discriminant, and a
push-forward against the Weil class of `Y`, which lies in `H^2`, carry the
Weil classes of one family onto those of every family of lower dimension and
every discriminant.  The rule `[40]` gives 4 is scalar extension,
`B -> B (x) O_F`, from the split families of a field of degree at least four
to those of the imaginary quadratic fields it contains.  The consequence operator is monotone and each rule has
one conclusion, so a pass that changes the set adds a conclusion not present
before; there are fewer than thirty-two conclusions, so thirty-two passes
reach the fixed point.

The bounded criterion is absent from the rules: it is equivalent to the
conclusion it would imply, so it is a restatement and not a premise.

The second rule, `[9]` gives 1, is the proposition that the conjecture for
the varieties that are not abelian is the conjecture: it covers `A x P^1` for
every abelian variety `A`, and the conjecture for `A x P^1` gives it for `A`
(pull back along the projection, cup with the class of `A x {0}`, push
forward).  An earlier version of this rule set omitted it.  The last rule,
`[1, 36]` gives 0, is the weaker statement 36, the conjecture modulo abelian
varieties, taken with the conjecture for abelian varieties.

The last three rules are the routes of the literature through motivated
classes.  Under the Lefschetz standard conjecture 31 for every variety the
Lefschetz involution is algebraic and every motivated class is algebraic, so
`[31, 32]` gives 0.  Statement 34 is Andre's theorem that motivated classes
deform in smooth projective families, so `[31, 34]` gives the variational
statement 33 for algebraic classes.  Statement 35 is the theorem of Deligne
and Andre, in Milne's form, that every Hodge class on an abelian variety is
reached from algebraic classes by pull-back and deformation, so `[33, 35]`
gives 1, the conjecture for abelian varieties.

What is checked.  The conjecture is not a consequence of what is proved here.
It is a consequence once statement 9 alone is adjoined, and once any of
`[31, 32]`, `[31, 36]`, `[33, 36]` and `[36, 10, 38]` is; in each of these
five sets every element is necessary.  The sets `[9, 10, 38]`, `[31, 9]` and
`[33, 9]` also suffice and are not minimal, since they contain `[9]`.  Among
the sixteen open statements exactly one, 9, suffices alone, and among all
one hundred and twenty pairs exactly those containing 9 and the pairs
`[31, 32]`, `[31, 36]` and `[33, 36]` suffice.  Statement 33 alone gives the conjecture for
abelian varieties and not the conjecture, and statement 31 gives 33.  And the secant route, granted both of its open
demands, yields the trivial discriminant families and, by descent, every
imaginary quadratic family, and not the fields of higher degree; and the
propagation statement for the split families of the fields of degree at
least four, 38, yields the Weil classes of every CM field.
-/

/-- the rules, as pairs of a premise list and a conclusion. -/
def hcRules : List (List Nat × Nat) :=
  [([1, 9], 0), ([9], 1), ([2, 10], 1), ([3, 11], 2), ([4, 5], 3),
   ([12, 19, 20, 21], 4), ([37, 19, 20, 21], 5),
   ([38, 28, 29, 30], 40), ([39, 28, 29, 30], 41), ([40, 41], 11),
   ([4], 5), ([40], 41), ([40], 4),
   ([13, 14, 20, 22, 23, 25], 4),
   ([15, 16, 24], 6), ([17, 18, 24], 6), ([6, 14, 22, 23], 7),
   ([26, 27], 8),
   ([31, 32], 0), ([31, 34], 33), ([33, 35], 1), ([1, 36], 0)]

/-- what the paper proves or quotes. -/
def hcBase : List Nat :=
  [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 34, 35]

/-- the open statements. -/
def hcOpen : List Nat :=
  [9, 10, 12, 13, 14, 15, 16, 17, 18, 31, 32, 33, 36, 37, 38, 39]

/-- one pass of the consequence operator. -/
def hcStep (s : List Nat) : List Nat :=
  hcRules.foldl
    (fun acc r => if r.1.all (fun p => acc.contains p) then
        (if acc.contains r.2 then acc else r.2 :: acc) else acc) s

/-- the forward closure, after `k` passes. -/
def hcClose (s : List Nat) : Nat → List Nat
  | 0 => s
  | k + 1 => hcStep (hcClose s k)

/-- the conjecture is derivable from what is proved here together with `t`. -/
def hcSuff (t : List Nat) : Bool := (hcClose (hcBase ++ t) 32).contains 0

/-- **The paper does not prove the Hodge conjecture.**  Statement `0` is not
in the closure of what is proved here and quoted from the literature. -/
theorem closure_omits_conjecture :
    (hcClose hcBase 32).contains 0 = false := by decide

/-- **Five minimal sufficient sets, and three that are not minimal.**  The
statement `9` alone, the conjecture for the varieties that are not abelian,
which is the conjecture itself; the Lefschetz standard conjecture `31`
together with the motivatedness of every Hodge class `32`; and the weaker
statement `36`, the conjecture modulo abelian varieties, together with `31`,
with the variational statement `33`, or with `10` and the propagation
statement `38` for the split families of the fields of degree at least four,
which is the route through this paper.  The sets `[9, 10, 38]`, `[31, 9]` and
`[33, 9]` suffice as well, and each contains `[9]`. -/
theorem frontier_suffices :
    (hcSuff [9] && hcSuff [31, 32] && hcSuff [31, 36] && hcSuff [33, 36]
      && hcSuff [36, 10, 38] && hcSuff [9, 10, 38] && hcSuff [31, 9]
      && hcSuff [33, 9]) = true := by
  decide

/-- **Each element of each of the five minimal sets is necessary.**  Dropping
any one of them leaves the conjecture underivable. -/
theorem frontier_minimal :
    (([[9], [31, 32], [31, 36], [33, 36], [36, 10, 38]] : List (List Nat)).all
        fun t => t.all fun f => !hcSuff (t.erase f)) = true := by decide

set_option maxHeartbeats 2000000 in
/-- **Exactly one statement suffices alone, and the pairs that suffice are
those containing it and three more.**  Over the sixteen open statements,
`9` and no other suffices alone, and of the one hundred and twenty pairs
exactly those containing `9` and the pairs `[31, 32]`, `[31, 36]` and
`[33, 36]` suffice.  The kernel evaluates one hundred and thirty-six
closures here, so the heartbeat limit is raised for this one theorem; that
adds no axiom. -/
theorem frontier_smallest :
    (hcOpen.all (fun a => hcSuff [a] == (a == 9))
      && hcOpen.all (fun a => hcOpen.all (fun b =>
          !(a < b) || (hcSuff [a, b] ==
            ((a == 9 || b == 9) || (a == 31 && b == 32)
              || (a == 31 && b == 36) || (a == 33 && b == 36)))))) = true := by
  decide

/-- **The variational statement alone gives the conjecture for abelian
varieties**, hence every Weil class and every class beyond the Weil lines on
an abelian variety, and does not give the conjecture. -/
theorem variational_gives_abelian :
    ((hcClose (hcBase ++ [33]) 32).contains 1 && !hcSuff [33]) = true := by
  decide

/-- **The Lefschetz standard conjecture gives the variational statement**, and
so the conjecture for abelian varieties (Abdulali, Andre), and does not give
the conjecture. -/
theorem lefschetz_gives_abelian :
    ((hcClose (hcBase ++ [31]) 32).contains 33
      && (hcClose (hcBase ++ [31]) 32).contains 1 && !hcSuff [31]) = true := by
  decide

/-- **The secant route descends and stops at the quadratic fields.**  Granting
both of its open demands, `13` and `14`, puts the trivial discriminant `4` in
the closure, and by descent `5` and the whole imaginary quadratic case `3`,
and leaves the fields of higher degree `11` and the conjecture `0` out of
it. -/
theorem secant_route_descends :
    ((hcClose (hcBase ++ [13, 14]) 32).contains 4
      && (hcClose (hcBase ++ [13, 14]) 32).contains 5
      && (hcClose (hcBase ++ [13, 14]) 32).contains 3
      && !(hcClose (hcBase ++ [13, 14]) 32).contains 11
      && !(hcClose (hcBase ++ [13, 14]) 32).contains 0) = true := by decide

/-- **The propagation statement for the split families closes the imaginary
quadratic case, and for the split families of the fields of degree at least
four it closes the Weil classes of every CM field.** -/
theorem propagation_closes :
    ((hcClose (hcBase ++ [12]) 32).contains 3
      && (hcClose (hcBase ++ [38]) 32).contains 3
      && (hcClose (hcBase ++ [38]) 32).contains 2) = true := by decide

/-! ## 25.  The numerical criterion and the support of a semiregular object

Two finite facts carry the theorems that sharpen the semiregularity
criterion.  The first is the count behind its numerical form: the classes of
`HH^2` that survive contraction into the Weil class number
`binom(4n,2) - 4n^2`, and this equals `2 binom(2n,2) = 2n(2n-1)`, the
dimension of `wedge^2 P (+) wedge^2 Q`.  The second is the monomial
separation: write the four pieces `V_+^{1,0}, V_-^{1,0}, V_+^{0,1},
V_-^{0,1}` of `H^1` as four blocks of `n` bits, so that a monomial of the
exterior algebra is a bit mask.  The classes pulled back from `A/B` for an
abelian subvariety `B` tangent to `T_+` use only the blocks `V_-^{1,0}` and
`V_+^{0,1}`, those for `B` tangent to `T_-` only `V_+^{1,0}` and `V_-^{0,1}`,
and neither Weil monomial is a submask of either: so the Weil line meets the
sum of the two subrings in zero.
-/

/-- the block of `n` bits in position `i`. -/
def blk (n i : Nat) : Nat := (2 ^ n - 1) <<< (i * n)

/-- **The count.**  `binom(4n,2) - 4n^2 = 2 binom(2n,2) = 2n(2n-1)`, written
with the binomials in closed form, for every `n` up to sixty. -/
theorem p2_minimal_count :
    ((List.range 60).all fun k =>
      let n := k + 1
      (4 * n * (4 * n - 1)) / 2 - 4 * n * n == 2 * ((2 * n * (2 * n - 1)) / 2)
        && 2 * ((2 * n * (2 * n - 1)) / 2) == 2 * n * (2 * n - 1)) = true := by
  decide

/-- **The monomial separation.**  For `1 <= n <= 12`, neither Weil monomial
`alpha_+ = V_+^{1,0} V_+^{0,1}` nor `alpha_- = V_-^{1,0} V_-^{0,1}` is a
submask of `V_-^{1,0} V_+^{0,1}` or of `V_+^{1,0} V_-^{0,1}`. -/
theorem weil_monomials_separated :
    ((List.range 12).all fun k =>
      let n := k + 1
      let ap := blk n 0 ||| blk n 2
      let am := blk n 1 ||| blk n 3
      let okp := blk n 1 ||| blk n 2
      let okm := blk n 0 ||| blk n 3
      (ap &&& okp != ap) && (ap &&& okm != ap)
        && (am &&& okp != am) && (am &&& okm != am)) = true := by decide


/-! ## 26.  The invariants of the Mumford group

The theorem on the Lefschetz operator of an abelian scheme over a curve needs,
for a Mumford family, that the classes of the fibre invariant under the
monodromy are the powers of the polarisation.  The connected monodromy group
is the Hodge group, a form of `SL_2^3` acting on `V = V_1 (x) V_2 (x) V_3`, so
the count needed is the dimension of the invariants in `wedge^q V`.  The
weights of `V` are the eight vectors `(+-1, +-1, +-1)`; index them by
`j < 8`, the sign in factor `i` being bit `i` of `j`.  A subset of the eight
weights is a bit mask `m < 256`, of size `q`, and its weight in factor `i` is
`2 * #(m & S_i) - q` with `S_0 = 170`, `S_1 = 204`, `S_2 = 240`.  For a
representation of `sl_2` the invariants have dimension `m(0) - m(2)`, the
difference of two weight multiplicities, and for three commuting copies the
dimension is the alternating sum of the multiplicities of the weights
`(2 e_0, 2 e_1, 2 e_2)` over `e in {0,1}^3`.
-/

/-- the number of set bits of `m` among the lowest eight. -/
def pc8 (m : Nat) : Nat := (List.range 8).countP (fun i => m.testBit i)

/-- the multiplicity of the weight `(2 e_0, 2 e_1, 2 e_2)` in `wedge^q V`. -/
def wmult (q e0 e1 e2 : Nat) : Nat :=
  (List.range 256).countP fun m =>
    pc8 m == q && 2 * pc8 (m &&& 170) == q + 2 * e0
      && 2 * pc8 (m &&& 204) == q + 2 * e1
      && 2 * pc8 (m &&& 240) == q + 2 * e2

/-- the dimension of the invariants of `sl_2^3` in `wedge^q V`. -/
def invDim (q : Nat) : Int :=
  (wmult q 0 0 0 : Int) - wmult q 1 0 0 - wmult q 0 1 0 - wmult q 0 0 1
    + wmult q 1 1 0 + wmult q 1 0 1 + wmult q 0 1 1 - wmult q 1 1 1

/-- **The invariants of the Mumford group.**  In `wedge^q V`, `q = 0..8`, the
invariants have dimensions `1, 0, 1, 0, 1, 0, 1, 0, 1`: one in each even
degree, the power of the invariant form, and none in odd degree. -/
theorem mumford_invariants :
    (List.range 9).map invDim = [1, 0, 1, 0, 1, 0, 1, 0, 1] := by decide

/-! ## 27.  Two branches cannot be two objects

On an abelian `2n`-fold of Weil type write `H^1 = V_+^{1,0} + V_-^{1,0} +
V_+^{0,1} + V_-^{0,1}`, each of dimension `n`, as four blocks of bits
`[0,n)`, `[n,2n)`, `[2n,3n)`, `[3n,4n)`.  `HH^1` acts by wedging the classes of
`H^{0,1}` and contracting those of `H^{1,0}`; `P = V_+^{0,1} + T_-` and
`Q = V_-^{0,1} + T_+`.  Each operator maps a monomial to a monomial or to zero,
injectively, so an annihilator is spanned by monomials, and a monomial is of
type `(p,p)` when it has as many bits in the first two blocks as in the last
two.  The theorem checks, for `n = 2` and `n = 3`, that the monomials of type
`(p,p)` killed by every product `q w` with `q` in `Q` and `w` in `HH^1` are
exactly `alpha_-`, those killed by `P HH^1` exactly `alpha_+`, and that none
is killed by all of `HH^1 HH^1`.
-/

/-- an operator: `(true, i)` wedges generator `i`, `(false, i)` contracts it. -/
def opApp (op : Bool × Nat) (m : Nat) : Option Nat :=
  if op.1 then (if m.testBit op.2 then none else some (m ||| (1 <<< op.2)))
  else (if m.testBit op.2 then some (m ^^^ (1 <<< op.2)) else none)

/-- the generators of `P`, of `Q`, and all of `HH^1`. -/
def pGens (n : Nat) : List (Bool × Nat) :=
  (List.range n).map (fun i => (true, 2 * n + i)) ++
  (List.range n).map (fun i => (false, n + i))
def qGens (n : Nat) : List (Bool × Nat) :=
  (List.range n).map (fun i => (true, 3 * n + i)) ++
  (List.range n).map (fun i => (false, i))
def hhGens (n : Nat) : List (Bool × Nat) := pGens n ++ qGens n

/-- `m` is killed by every product `q w`, `q` in `L`, `w` in `HH^1`. -/
def killedBy (n : Nat) (L : List (Bool × Nat)) (m : Nat) : Bool :=
  L.all fun q => (hhGens n).all fun w =>
    match opApp w m with
    | none => true
    | some x => (opApp q x).isNone

/-- the number of set bits of `m` in `[a, a + k)`. -/
def bitsIn (m a k : Nat) : Nat := (List.range k).countP (fun i => m.testBit (a + i))

/-- the monomials of type `(p,p)` killed by the products with `L`. -/
def annPP (n : Nat) (L : List (Bool × Nat)) : List Nat :=
  (List.range (2 ^ (4 * n))).filter fun m =>
    bitsIn m 0 (2 * n) == bitsIn m (2 * n) (2 * n) && killedBy n L m

/-- `alpha_+` and `alpha_-` as bit masks. -/
def alphaPlus (n : Nat) : Nat := (2 ^ n - 1) ||| ((2 ^ n - 1) <<< (2 * n))
def alphaMinus (n : Nat) : Nat := ((2 ^ n - 1) <<< n) ||| ((2 ^ n - 1) <<< (3 * n))

/-- **The two branches of the criterion cannot be two objects.**  For
`n = 2, 3` the classes of type `(p,p)` annihilated by `Q HH^1` are the
multiples of `alpha_-`, by `P HH^1` those of `alpha_+`, and by `HH^1 HH^1`
none. -/
theorem two_branch_annihilator :
    ((annPP 2 (qGens 2) == [alphaMinus 2]) && (annPP 2 (pGens 2) == [alphaPlus 2])
      && (annPP 2 (hhGens 2) == [])
      && (annPP 3 (qGens 3) == [alphaMinus 3]) && (annPP 3 (pGens 3) == [alphaPlus 3])
      && (annPP 3 (hhGens 3) == [])) = true := by decide

/-! ## 28.  The certificates of the rigidity of the Mumford square

Item (XLIV) of the verification section factors the Gram determinant of
every weight block of the contraction into an exceptional class of the square
of a Mumford fourfold, and every factor is one of seventeen quadratic forms in
the coefficients `a0, a1, a2, a3` (or a linear form).  The rigidity theorem
and the numerical criterion rest on one identity for each form: a positive
multiple of the form is a sum of squares of integral linear forms with
positive integral coefficients.  Both sides are polynomials of degree at most
two in each variable, so agreement on the grid `{0,1,2}^4` is agreement as
polynomials, by interpolation in one variable at a time; the theorem checks the
grid.
-/

/-- the square of an integer. -/
def sq (x : Int) : Int := x * x

/-- the seventeen identities at one point. -/
def rigidCert (a0 a1 a2 a3 : Int) : Bool :=
    (2 * (a1 * a1 - a1 * a2 - a1 * a3 + a2 * a2 - a2 * a3 + a3 * a3)) == (sq (a1 - a2) + sq (a1 - a3) + sq (a2 - a3))  -- P1
    && (2 * (a1 * a1 + a1 * a2 + a1 * a3 + a2 * a2 + a2 * a3 + a3 * a3)) == (sq (a1 + a2) + sq (a1 + a3) + sq (a2 + a3))  -- P2
    && (33 * (3 * a0 * a0 - 2 * a0 * a1 - 2 * a0 * a2 - 2 * a0 * a3 + 11 * a1 * a1 - 10 * a1 * a2 - 10 * a1 * a3 + 11 * a2 * a2 - 10 * a2 * a3 + 11 * a3 * a3)) == (3 * sq (-a0 + 11 * a1 - 5 * a2 - 5 * a3) + 8 * sq (-a0 + 6 * a2 - 5 * a3) + 88 * sq (-a0 + a3))  -- Q1
    && (119 * (3 * a0 * a0 + 6 * a0 * a1 - 2 * a0 * a2 + 6 * a0 * a3 + 51 * a1 * a1 + 30 * a1 * a2 + 6 * a1 * a3 + 11 * a2 * a2 + 30 * a2 * a3 + 51 * a3 * a3)) == (21 * sq (a0 + 17 * a1 + 5 * a2 + a3) + 16 * sq (-2 * a0 + 7 * a2 + 15 * a3) + 272 * sq (a0 + 3 * a3))  -- Q2
    && (51 * (3 * a0 * a0 + 6 * a0 * a1 + 6 * a0 * a2 - 2 * a0 * a3 + 51 * a1 * a1 + 6 * a1 * a2 + 30 * a1 * a3 + 51 * a2 * a2 + 30 * a2 * a3 + 11 * a3 * a3)) == (9 * sq (a0 + 17 * a1 + a2 + 5 * a3) + 8 * sq (a0 + 18 * a2 + 5 * a3) + 136 * sq (-a0 + a3))  -- Q3
    && ((a0 * a0 - 6 * a0 * a1 + 2 * a0 * a2 + 2 * a0 * a3 + 9 * a1 * a1 - 6 * a1 * a2 - 6 * a1 * a3 + 17 * a2 * a2 - 30 * a2 * a3 + 17 * a3 * a3)) == (sq (-a0 + 3 * a1 - a2 - a3) + 16 * sq (a2 - a3))  -- Q4
    && ((a2 * a2 + a3 * a3)) == (sq (a2) + sq (a3))  -- R
    && ((a0 * a0 - 2 * a0 * a2 + 3 * a1 * a1 - 6 * a1 * a3 + a2 * a2 + 3 * a3 * a3)) == (sq (a0 - a2) + 3 * sq (a1 - a3))  -- S1
    && ((a0 * a0 + 2 * a0 * a2 + 3 * a1 * a1 + 6 * a1 * a3 + 9 * a2 * a2 + 3 * a3 * a3)) == (sq (a0 + a2) + 3 * sq (a1 + a3) + 8 * sq (a2))  -- S2
    && ((a0 * a0 - 2 * a0 * a3 + 3 * a1 * a1 - 6 * a1 * a2 + 3 * a2 * a2 + a3 * a3)) == (sq (a0 - a3) + 3 * sq (a1 - a2))  -- S3
    && ((a0 * a0 + 2 * a0 * a3 + 3 * a1 * a1 + 6 * a1 * a2 + 3 * a2 * a2 + 9 * a3 * a3)) == (sq (a0 + a3) + 3 * sq (a1 + a2) + 8 * sq (a3))  -- S4
    && (30627 * (9 * a0 * a0 + 2 * a0 * a1 + 2 * a0 * a2 + 2 * a0 * a3 + 73 * a1 * a1 + 2 * a1 * a2 + 2 * a1 * a3 + 73 * a2 * a2 + 2 * a2 * a3 + 73 * a3 * a3)) == (3403 * sq (9 * a0 + a1 + a2 + a3) + 332 * sq (82 * a1 + a2 + a3) + 324 * sq (83 * a2 + a3) + 2231712 * sq (a3))  -- Z1
    && (4095 * (9 * a0 * a0 - 6 * a0 * a1 + 2 * a0 * a2 - 6 * a0 * a3 + 81 * a1 * a1 - 6 * a1 * a2 + 18 * a1 * a3 + 73 * a2 * a2 - 6 * a2 * a3 + 81 * a3 * a3)) == (455 * sq (9 * a0 - 3 * a1 + a2 - 3 * a3) + 364 * sq (30 * a1 - a2 + 3 * a3) + 36 * sq (91 * a2 - 3 * a3) + 324000 * sq (a3))  -- Z2
    && (495 * (9 * a0 * a0 - 6 * a0 * a1 - 6 * a0 * a2 + 2 * a0 * a3 + 81 * a1 * a1 + 18 * a1 * a2 - 6 * a1 * a3 + 81 * a2 * a2 - 6 * a2 * a3 + 73 * a3 * a3)) == (55 * sq (9 * a0 - 3 * a1 - 3 * a2 + a3) + 44 * sq (30 * a1 + 3 * a2 - a3) + 36 * sq (33 * a2 - a3) + 36000 * sq (a3))  -- Z3
    && ((a0 * a0 + 9 * a1 * a1 + 11 * a2 * a2 + 9 * a3 * a3)) == (sq (a0) + 9 * sq (a1) + 11 * sq (a2) + 9 * sq (a3))  -- Z4
    && ((a0 * a0 + 9 * a1 * a1 + 9 * a2 * a2 + 11 * a3 * a3)) == (sq (a0) + 9 * sq (a1) + 9 * sq (a2) + 11 * sq (a3))  -- Z5
    && (57 * (3 * a0 * a0 + 6 * a0 * a1 - 2 * a0 * a2 - 2 * a0 * a3 + 51 * a1 * a1 - 18 * a1 * a2 - 18 * a1 * a3 + 27 * a2 * a2 + 6 * a2 * a3 + 27 * a3 * a3)) == (19 * sq (3 * a0 + 3 * a1 - a2 - a3) + 76 * sq (6 * a1 - a2 - a3) + 4 * sq (19 * a2 + a3) + 1440 * sq (a3))  -- Z6

/-- **The rigidity certificates.**  For each of the forms `P1, P2, Q1, ..., Q4,
R, S1, ..., S4, Z1, ..., Z6` a positive multiple is a sum of squares with
positive coefficients, checked on the grid `{0,1,2}^4`. -/
theorem mumford_rigidity_sos :
    ((List.range 3).all fun i => (List.range 3).all fun j =>
      (List.range 3).all fun k => (List.range 3).all fun l =>
        rigidCert (i : Int) (j : Int) (k : Int) (l : Int)) = true := by
  decide

/-! ## 29.  The self-extension bounds for the Mumford object

Item (XLV) of the verification section computes, block by block and exactly,
the ranks of contraction into an exceptional class of the square of a Mumford
fourfold on the pieces `HT^k` of Hochschild cohomology, `k = 0, ..., 8`:
`1, 16, 119, 328, 560, 328, 119, 16, 1`.  They bound `dim Ext^k(E,E)` from
below for every perfect complex `E` with that Chern character.  The theorem
checks the arithmetic used with them: the list is a palindrome, as the duality
lemma predicts; its alternating sum is `112`, while `chi(E,E) = 0`; its sum is
`1488`; the even degrees give `2 * 1 + 2 * 119 + 560 = 800`, which by
`chi(E,E) = 0` is also a lower bound for the odd degrees; and the Hochschild
bound for the odd degrees is only `2 * (16 + 328) = 688`.
-/

/-- the lower bounds `r_0, ..., r_8`. -/
def extProfile : List Int := [1, 16, 119, 328, 560, 328, 119, 16, 1]

/-- the alternating sum of a list, starting with a plus sign. -/
def altSum : List Int → Int
  | [] => 0
  | x :: xs => x - altSum xs

/-- **The self-extension bounds.** -/
theorem mumford_ext_profile :
    (extProfile.reverse == extProfile
      && altSum extProfile == 112
      && extProfile.foldl (· + ·) 0 == 1488
      && 2 * extProfile.getD 0 0 + 2 * extProfile.getD 2 0
          + extProfile.getD 4 0 == 800
      && 2 * (extProfile.getD 1 0 + extProfile.getD 3 0) == 688
      && 800 - 688 == 112) = true := by
  decide

/-! ## 30.  What line bundles generate on the Mumford square

Item (XLVI) of the verification section computes the invariants of
`Sp(V, psi)` and of the Mumford group in `wedge^k (V (+) V)`, and the monomials
of weight zero for the diagonal torus of `Sp(V, psi)`, which is the Lefschetz
group at a CM point.  This section checks the arithmetic behind those counts.
(i) `wedge^i V` is the sum of the irreducible modules `V(varpi_m)` over the
`m <= 4` with `m <= min(i, 8 - i)` and `m = i` modulo two, so
`Hom_Sp(wedge^i V, wedge^j V)` has dimension the number of `m` allowed for
both; summing over `i + j = k` gives `1, 3, 6, 10, 15, 10, 6, 3, 1` in the
degrees `k = 0, 2, ..., 16`.  The invariants of the Mumford group,
`1, 3, 8, 16, 28, 16, 8, 3, 1` (item (XLIII)), exceed them by
`0, 0, 2, 6, 13, 6, 2, 0, 0`, twenty-nine in all.  (ii) A monomial of weight
zero for the diagonal torus chooses, for each of the four pairs of opposite
weights, the same number `c <= 2` of the two copies on each side, in
`C(2, c)^2` ways, so the counts are the coefficients of `(1 + 4y + y^2)^4`.
(iii) Weyl's dimension formula for `Sp_8`, with `rho = (4, 3, 2, 1)`, gives
`27`, `42` and `308` for `varpi_2`, `varpi_4` and `2 varpi_2`, and
`1 + 27 + 42 + 308 = 378 = 27 * 28 / 2`.
-/

/-- the dimension of `Hom_Sp(wedge^i V, wedge^j V)`. -/
def homSp (i j : Nat) : Nat :=
  (List.range 5).countP fun m =>
    Nat.ble m i && Nat.ble (m + i) 8 && Nat.ble m j && Nat.ble (m + j) 8
      && (i + m) % 2 == 0 && (j + m) % 2 == 0

/-- the dimension of the `Sp(V, psi)`-invariants in `wedge^k (V (+) V)`. -/
def spInv (k : Nat) : Nat :=
  (List.range 9).foldl (fun acc i =>
    if Nat.ble i k && Nat.ble (k - i) 8 then acc + homSp i (k - i) else acc) 0

/-- the invariants of the Mumford group in the even degrees (item (XLIII)). -/
def mumfordInv : List Nat := [1, 3, 8, 16, 28, 16, 8, 3, 1]

/-- the product of two polynomials given by their coefficient lists. -/
def conv (p q : List Nat) : List Nat :=
  (List.range (p.length + q.length - 1)).map fun n =>
    (List.range (n + 1)).foldl (fun acc i => acc + p.getD i 0 * q.getD (n - i) 0) 0

/-- the numerator of Weyl's formula for `Sp_8` at `l = lambda + rho`. -/
def weylNum (l : List Int) : Int :=
  ((List.range 4).foldl (fun acc i =>
    (List.range 4).foldl (fun a j =>
      if i < j then a * (l.getD i 0 ^ 2 - l.getD j 0 ^ 2) else a) acc) 1)
  * l.foldl (fun a b => a * b) 1

/-- **What line bundles generate.**  The counts of the Lefschetz invariants
at a point that is not CM and at a CM point, the Hodge classes that are not
Lefschetz, and the dimension of the module of highest weight `2 varpi_2`. -/
theorem lefschetz_counts :
    (List.range 9).map (fun i => spInv (2 * i)) = [1, 3, 6, 10, 15, 10, 6, 3, 1]
    /\ (List.range 9).map (fun i => mumfordInv.getD i 0 - spInv (2 * i))
        = [0, 0, 2, 6, 13, 6, 2, 0, 0]
    /\ ((List.range 9).map (fun i => spInv (2 * i))).foldl (fun a b => a + b) 0 = 55
    /\ mumfordInv.foldl (fun a b => a + b) 0 = 84
    /\ conv (conv (conv [1, 4, 1] [1, 4, 1]) [1, 4, 1]) [1, 4, 1]
        = [1, 16, 100, 304, 454, 304, 100, 16, 1]
    /\ weylNum [5, 4, 2, 1] = 27 * weylNum [4, 3, 2, 1]
    /\ weylNum [5, 4, 3, 2] = 42 * weylNum [4, 3, 2, 1]
    /\ weylNum [6, 5, 2, 1] = 308 * weylNum [4, 3, 2, 1]
    /\ 1 + 27 + 42 + 308 = 27 * 28 / 2 := by
  decide

/-! ## 31.  The endomorphisms of an object meeting the numerical criterion

Item (L) of the verification section and the theorem on the shape of such an
object.  Write `e_k = dim Ext^k(E,E)` for a perfect complex `E` with
`ch(E) = N omega` on an abelian `2n`-fold of Weil type.  Serre duality gives
`e_k = e_{2n-k}`, the Hochschild action gives `e_1 >= 4n` and, at `n = 3`
and granting its compatibility with contraction in degree three, `e_3 >= 40`,
the criterion is `e_2 = 2n(2n-1)`, and the Hodge-Riemann
relations make `chi = sum (-1)^k e_k` positive.  At `n = 2` this reads
`2 e_0 + 12 = chi + 2 e_1`, at `n = 3` it reads
`2 e_0 + 60 = chi + 2 e_1 + e_3`, and in both cases `e_0 >= 3`: the object has
at least three linearly independent endomorphisms.  The geometry is in the
paper; what is checked here is the arithmetic, for all natural numbers.
-/

/-- **At `n = 2` the criterion forces three endomorphisms.** -/
theorem criterion_endomorphisms_n2 (e0 e1 chi : Nat)
    (h1 : 8 ≤ e1) (hc : 1 ≤ chi)
    (hchi : 2 * e0 + 12 = chi + 2 * e1) : 3 ≤ e0 := by
  have h2 : 2 * 8 ≤ 2 * e1 := Nat.mul_le_mul_left 2 h1
  have hs : 1 + 2 * 8 ≤ chi + 2 * e1 := Nat.add_le_add hc h2
  have h17 : 5 + 12 ≤ 2 * e0 + 12 := hchi ▸ hs
  have h5 : 5 ≤ 2 * e0 := Nat.le_of_add_le_add_right h17
  exact Nat.lt_of_not_le fun h =>
    absurd (Nat.le_trans h5 (Nat.mul_le_mul_left 2 h)) (by decide)

/-- **At `n = 3` the criterion forces three endomorphisms.** -/
theorem criterion_endomorphisms_n3 (e0 e1 e3 chi : Nat)
    (h1 : 12 ≤ e1) (h3 : 40 ≤ e3) (hc : 1 ≤ chi)
    (hchi : 2 * e0 + 60 = chi + 2 * e1 + e3) : 3 ≤ e0 := by
  have h2 : 2 * 12 ≤ 2 * e1 := Nat.mul_le_mul_left 2 h1
  have hs : 1 + 2 * 12 + 40 ≤ chi + 2 * e1 + e3 :=
    Nat.add_le_add (Nat.add_le_add hc h2) h3
  have h65 : 5 + 60 ≤ 2 * e0 + 60 := hchi ▸ hs
  have h5 : 5 ≤ 2 * e0 := Nat.le_of_add_le_add_right h65
  exact Nat.lt_of_not_le fun h =>
    absurd (Nat.le_trans h5 (Nat.mul_le_mul_left 2 h)) (by decide)

/-! ## 32.  The quartic obstruction: arithmetic modulo four

The obstruction to a dimension-count certificate for a quartic CM field at
`n = 2` (the quartic analogue of the theorem that no Orlov product works at
`n = 4`) ends in finitely many statements about squares modulo `4` in the
rings of integers `Z[φ]`, `φ^2 = φ + 1`, of `Q(√5)` and `Z[√2]` of `Q(√2)`,
and about residues of the integers `1, ..., 8`.  An element `a + bφ` or
`a + b√2` modulo `4` is the pair `(a, b)` of residues. -/

/-- The square of `a + bφ` modulo `4`, using `φ^2 = φ + 1`. -/
def sqPhi (a b : Nat) : Nat × Nat := ((a * a + b * b) % 4, (2 * a * b + b * b) % 4)

/-- The square of `a + b√2` modulo `4`. -/
def sqRoot2 (a b : Nat) : Nat × Nat := ((a * a + 2 * b * b) % 4, (2 * a * b) % 4)

/-- **The squares modulo `4` in `Z[φ]`** are `0, 1, 1 + φ, 2 + 3φ`. -/
theorem quartic_squares_mod4_phi :
    ∀ a, a < 4 → ∀ b, b < 4 →
      sqPhi a b = (0, 0) ∨ sqPhi a b = (1, 0) ∨ sqPhi a b = (1, 1) ∨
        sqPhi a b = (2, 3) := by decide

/-- **Neither `-1` nor twice a unit is a square modulo `4` in `Z[φ]`**: the
two cases `Δ = -φ^{2k}` and `Δ = -2ε` of the rank-two argument for `Q(√5)`. -/
theorem quartic_no_square_phi :
    ∀ a, a < 4 → ∀ b, b < 4 →
      sqPhi a b ≠ (3, 0) ∧ sqPhi a b ≠ (2, 0) ∧ sqPhi a b ≠ (0, 2) ∧
        sqPhi a b ≠ (2, 2) := by decide

/-- **The squares modulo `4` in `Z[√2]`** are `0, 1, 2, 3 + 2√2`. -/
theorem quartic_squares_mod4_sqrt2 :
    ∀ a, a < 4 → ∀ b, b < 4 →
      sqRoot2 a b = (0, 0) ∨ sqRoot2 a b = (1, 0) ∨ sqRoot2 a b = (2, 0) ∨
        sqRoot2 a b = (3, 2) := by decide

/-- **`3`, `1 + 3√2` and `1 + √2` are not squares modulo `4` in `Z[√2]`**: the
residues of the totally negative elements of norm `1` and `7`, which settle the
rank-two case for `Q(√2)` without the condition modulo `4` of Section 34. -/
theorem quartic_no_square_sqrt2 :
    ∀ a, a < 4 → ∀ b, b < 4 →
      sqRoot2 a b ≠ (3, 0) ∧ sqRoot2 a b ≠ (1, 3) ∧ sqRoot2 a b ≠ (1, 1) := by
  decide

/-- **The rank-two congruence `m ≡ 9` has no solution `1 ≤ m ≤ 8` modulo `13` or
`17`, and modulo `5` its only solution is `m = 4`.**  Here `m = μ^2 N(Δ)`,
bounded by `8` by the inequality `χ^2 ≥ 4 μ^2 N(Δ)` at `χ = 6`. -/
theorem quartic_rank_two_congruences :
    (∀ m, m < 9 → 1 ≤ m → m % 13 ≠ 9 ∧ m % 17 ≠ 9) ∧
    (∀ m, m < 9 → 1 ≤ m → m % 5 = 4 → m = 4) ∧
    (∀ m, m < 9 → 4 * m ≤ 36) := by decide

/-- **The Euler characteristic of a minimal object.**  A Hochschild-minimal
secant object on a fourfold with `Ext^{<0} = 0` has profile
`1, 8, r, 8, 1`, so `χ = r - 14`; for the three values `r = 18, 20, 12` of the
quartic secant space this is `4, 6, -2`. -/
theorem quartic_euler_minimal :
    (1 + 18 + 1 : Int) - 8 - 8 = 4 ∧ (1 + 20 + 1 : Int) - 8 - 8 = 6 ∧
      (1 + 12 + 1 : Int) - 8 - 8 = -2 := by decide

/-! ## 33.  The Orlov template: the equality count

For secant complexes `F₁, F₂` on a polarised abelian `n`-fold, the Künneth
formula gives `dim Ext²(E,E) = Σ_k e_k e'_{2-k}` for `E = Φ(F₁ ⊠ F₂^∨)`, and the
number the criterion asks for is `6n² - 2n` for `n ≥ 3` and `18` for `n = 2`.
Equality forces the profile `1, 2n, n(n-1)` in degrees `0, 1, 2`. -/

/-- **The equality count**: `1·n(n-1) + (2n)(2n) + n(n-1)·1 = 6n² - 2n`,
for `3 ≤ n ≤ 64`, and `1·1 + 4·4 + 1·1 = 18` at `n = 2`. -/
theorem orlov_equality_count :
    (∀ n, n < 65 → 3 ≤ n →
      n * (n - 1) + (2 * n) * (2 * n) + n * (n - 1) = 6 * n * n - 2 * n) ∧
    1 * 1 + 4 * 4 + 1 * 1 = 18 := by decide

/-- **No Orlov product at `n = 4`.**  The minimal profile `1, 8, 12, 8, 1` has
Euler characteristic `-2`, while a secant character on a principally
polarised fourfold has `χ = 8d(a²d + b²) ≥ 8`. -/
theorem orlov_n4_euler :
    (1 + 12 + 1 : Int) - 8 - 8 = -2 ∧
      ∀ d a b : Nat, 1 ≤ d → 1 ≤ a * a * d + b * b → 8 ≤ 8 * d * (a * a * d + b * b) := by
  refine ⟨by decide, ?_⟩
  intro d a b hd hs
  have h1 : 8 ≤ 8 * d := by
    have h := Nat.mul_le_mul_left 8 hd
    rwa [Nat.mul_one] at h
  have h2 : 8 * d ≤ 8 * d * (a * a * d + b * b) := by
    have h := Nat.mul_le_mul_left (8 * d) hs
    rwa [Nat.mul_one] at h
  exact Nat.le_trans h1 h2

/-! ## 34.  The quartic obstruction for every real quadratic field

For `F₀ = Q(√D)`, `D` squarefree, the rank-two case ends in three conditions
on the integer `m = μ² N(Δ)`, which lies in `[1, 8]`: (a) `m ≡ 9` modulo the
odd part `D_o` of `D`; (b) `m ≡ 0` or `1` modulo `4`, because
`m ≡ (μ N(l₁))²` modulo `4`; (c) `m` is odd when `D ≡ 2` modulo `4`.  Only
`D = 5` and `D = 2` survive, and they are settled by Section 32 and the last
theorem below. -/

/-- **Squares modulo `4` and `8`**: a square is `0` or `1` modulo `4`, an odd
square is `1` modulo `8`, and twice a square is `0` or `2` modulo `8`. -/
theorem quartic_squares_mod4_mod8 :
    (∀ x, x < 4 → x * x % 4 = 0 ∨ x * x % 4 = 1) ∧
    (∀ x, x < 8 → x % 2 = 1 → x * x % 8 = 1) ∧
    (∀ x, x < 8 → 2 * x * x % 8 = 0 ∨ 2 * x * x % 8 = 2) := by decide

/-- **The fields with odd part `3`, `5` or `7`.**  For `D = 3, 7` conditions
(a) and (b) have no common solution in `[1, 8]`; for `D = 6, 10, 14`,
conditions (a), (b), (c), that is `m ≡ 9 (mod D_o)` and `m ≡ 1 (mod 4)`, have
none; for `D = 2` they leave `m = 1, 5`. -/
theorem quartic_rank_two_small_odd_parts :
    (∀ m, m < 9 → 1 ≤ m → ¬ (m % 3 = 0 ∧ (m % 4 = 0 ∨ m % 4 = 1))) ∧
    (∀ m, m < 9 → 1 ≤ m → ¬ (m % 7 = 2 ∧ (m % 4 = 0 ∨ m % 4 = 1))) ∧
    (∀ m, m < 9 → 1 ≤ m → ¬ (m % 3 = 0 ∧ m % 4 = 1)) ∧
    (∀ m, m < 9 → 1 ≤ m → ¬ (m % 5 = 4 ∧ m % 4 = 1)) ∧
    (∀ m, m < 9 → 1 ≤ m → ¬ (m % 7 = 2 ∧ m % 4 = 1)) ∧
    (∀ m, m < 9 → 1 ≤ m → m % 4 = 1 → m = 1 ∨ m = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Odd part at least `10`**: for every modulus `n ≥ 10` and every
`m < 9`, `m` is not `9` modulo `n`, so condition (a) has no solution. -/
theorem quartic_rank_two_large_odd_part (n m : Nat) (hn : 10 ≤ n) (hm : m < 9) :
    m % n ≠ 9 % n := by
  have h9 : 9 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hmn : m < n := Nat.lt_trans hm h9
  rw [Nat.mod_eq_of_lt hmn, Nat.mod_eq_of_lt h9]
  exact Nat.ne_of_lt hm

/-- **The field `Q(√2)`.**  With `m ∈ {1, 5}` and `μ` odd, `N(Δ) ∈ {1, 5}`,
and norms of elements of `Z[√2]` prime to `2` are `±1` modulo `8`, so
`N(Δ) = 1` and `Δ = -(1+√2)^{2k}`, which is `3` or `1 + 2√2` modulo `4`;
neither is a square modulo `4` in `Z[√2]`. -/
theorem quartic_sqrt2_units_mod4 :
    (∀ a, a < 4 → ∀ b, b < 4 →
      sqRoot2 a b ≠ (3, 0) ∧ sqRoot2 a b ≠ (1, 2)) ∧
    ((3 * 3 + 2 * 2 * 2) % 4 = 1 ∧ (2 * 3 * 2) % 4 = 0) ∧
    (5 % 8 ≠ 1 ∧ 5 % 8 ≠ 7) := by decide

/-! ## 35.  Beyond degree four: the count leaves room

For a sextic CM field the secant classes live on a sixfold, where Serre duality
`e_k = e_{6-k}` leaves `e_3 = dim Ext^3(F,F)` free: for a minimal object
(`e_0, e_1, e_2 = 1, 12, r^2`) one has `χ = 2(1 - 12 + r^2) - e_3`.  The
computed profiles `(1, 12, r^2, r^3, r^2, 12, 1)` are listed below; the
threshold `T = r^3 - 2 r^2 + 22` is what `-χ` must reach. -/

/-- **The sextic thresholds.**  For the six computed pairs `(r^2, r^3)` the
threshold `r^3 - 2 r^2 + 22` is `2, -6, 10, 26, 8, 12`; the Euler
characteristic of a minimal object, `2(1 - 12 + r^2) - e_3`, is `-26` at the
generic profile with `e_3 = r^3 = 112`, so there `-χ` must be at least `26`;
and the factor of `χ` on a sextic secant space is `(-4)^3 = -64`. -/
theorem sextic_thresholds :
    ((40 : Int) - 2 * 30 + 22 = 2 ∧ (64 : Int) - 2 * 46 + 22 = -6 ∧
      (96 : Int) - 2 * 54 + 22 = 10 ∧ (112 : Int) - 2 * 54 + 22 = 26 ∧
      (88 : Int) - 2 * 51 + 22 = 8 ∧ (96 : Int) - 2 * 53 + 22 = 12) ∧
    (2 * (1 - 12 + (54 : Int)) - 112 = -26) ∧
    ((-4 : Int) ^ 3 = -64 ∧ (-4 : Int) ^ 2 = 16) := by
  decide

/-! ## 36.  The Weil structure at a CM point and the cycles on the square

The eight weights of the Hodge torus of a Mumford fourfold at a CM point are
the vectors `(+-1, +-1, +-1)`, indexed here by `i < 8` with coordinates
`1 - 2 b_t(i)` for the three bits of `i`, so that the opposite of `i` is
`7 - i`.  The proposition on the Weil structure at a CM point turns on the
following finite facts, which the kernel checks by enumeration.

(i) The four-element sets of weights with sum zero are the six unions of two
opposite pairs and two further sets, the tetrahedra: `T_+`, whose elements
have an even number of entries `-1`, and `T_- = -T_+`; each tetrahedron
meets every opposite pair exactly once.

(ii) On the square the monomials of weight zero in the sixteen classes
`e_w^(1), e_w^(2)` are the four-element subsets of `{0, ..., 15}` (weight
`j % 8`, copy `j / 8`) whose weights sum to zero.  They number `132`; `100`
of them contain an opposite pair, and the remaining `32` are the tetrahedron
monomials, whose weights form `T_+` or `T_-`, `16` for each tetrahedron,
distributed `1, 4, 6, 4, 1` by the number of factors from the first copy.

(iii) The six two-element subsets `S` of `T_+` fall into three pairs
`{S, T_+ - S}` by the set `D(S)` of coordinates in which the two weights of
`S` differ, which has two elements and is the same for `S` and for its
complement.  The coefficients of an exceptional class `omega_a` on the pair
indexed by `{1,2}`, `{1,3}`, `{2,3}` have absolute values `|a_2 - a_3|/2`,
`|a_1 - a_3|/2`, `|a_1 - a_2|/2`; the three values are equal only when
`a_1 = a_2 = a_3`, and two of them are equal exactly along a linear relation
among `a_1, a_2, a_3` with coefficients that are not all equal.

(iv) For the lemma on split CM points: a permutation of the four diagonals of
the cube that permutes the three pairings of the diagonals into two pairs
without fixing any of them is a cycle of length three on the diagonals, and
fixes exactly one diagonal.
-/

/-- the `t`-th coordinate, `t = 0, 1, 2`, of the weight with index `i < 8`. -/
def cmCoord (i t : Nat) : Int := 1 - 2 * ((i / 2 ^ (2 - t)) % 2)

/-- the index of the opposite weight. -/
def cmNeg (i : Nat) : Nat := 7 - i

/-- the number of entries `-1` of the weight `i`. -/
def cmMinusCount (i : Nat) : Nat := i % 2 + (i / 2) % 2 + (i / 4) % 2

/-- the four-element subsets of `{0, ..., n - 1}`, as increasing lists. -/
def cmQuads (n : Nat) : List (List Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).filterMap fun d =>
          if a < b && b < c && c < d then some [a, b, c, d] else none

/-- the sum of the `t`-th coordinates of the weights `j % 8`, `j` in `S`. -/
def cmSum (S : List Nat) (t : Nat) : Int :=
  S.foldl (fun acc j => acc + cmCoord (j % 8) t) 0

/-- weight zero: all three coordinate sums vanish. -/
def cmZero (S : List Nat) : Bool :=
  cmSum S 0 == 0 && cmSum S 1 == 0 && cmSum S 2 == 0

/-- whether the weights of `S` contain an opposite pair. -/
def cmHasOpposite (S : List Nat) : Bool :=
  S.any fun j => S.any fun k => (j % 8) + (k % 8) == 7

/-- the sets of four weights with sum zero. -/
def cmZeroSets : List (List Nat) := (cmQuads 8).filter cmZero

/-- the tetrahedra: zero-sum sets without an opposite pair. -/
def cmTets : List (List Nat) :=
  cmZeroSets.filter fun S => !(cmHasOpposite S)

/-- `T_+` and `T_-`, read off the enumeration. -/
def cmTplus : List Nat := [0, 3, 5, 6]
def cmTminus : List Nat := [1, 2, 4, 7]

/-- **The tetrahedra.**  Eight zero-sum sets, six with two opposite pairs,
and two without, `T_+` with even and `T_-` with odd numbers of entries
`-1`, `T_- = -T_+`, each meeting every opposite pair once. -/
theorem cm_tetrahedra :
    cmZeroSets.length = 8
    /\ (cmZeroSets.filter cmHasOpposite).length = 6
    /\ cmTets = [cmTplus, cmTminus]
    /\ cmTplus.all (fun i => cmMinusCount i % 2 == 0) = true
    /\ cmTminus.all (fun i => cmMinusCount i % 2 == 1) = true
    /\ cmTminus = (cmTplus.map cmNeg).reverse
    /\ (List.range 4).all (fun p =>
        (cmTplus.filter fun i => i == p || i == cmNeg p).length == 1) = true
    /\ (List.range 4).all (fun p =>
        (cmTminus.filter fun i => i == p || i == cmNeg p).length == 1) = true
    := by
  decide

/-- the monomials of weight zero on the square. -/
def cmSquare : List (List Nat) := (cmQuads 16).filter cmZero

/-- the sorted list of weights of a monomial on the square. -/
def cmWeights (S : List Nat) : List Nat :=
  (List.range 8).filter fun i => S.any fun j => j % 8 == i

/-- the number of factors from the first copy. -/
def cmFirst (S : List Nat) : Nat := (S.filter fun j => j < 8).length

/-- **The 132 Hodge classes of the square.**  `100` monomials with an
opposite pair, `32` tetrahedron monomials, `16` for each tetrahedron,
`1, 4, 6, 4, 1` by the number of factors from the first copy. -/
theorem cm_square_monomials :
    cmSquare.length = 132
    /\ (cmSquare.filter cmHasOpposite).length = 100
    /\ (cmSquare.filter fun S => !(cmHasOpposite S)).length = 32
    /\ (cmSquare.filter fun S =>
        !(cmHasOpposite S) && (cmWeights S == cmTplus)).length = 16
    /\ (cmSquare.filter fun S =>
        !(cmHasOpposite S) && (cmWeights S == cmTminus)).length = 16
    /\ (cmSquare.all fun S =>
        cmHasOpposite S || cmWeights S == cmTplus || cmWeights S == cmTminus)
        = true
    /\ (List.range 5).map (fun k => (cmSquare.filter fun S =>
        !(cmHasOpposite S) && (cmWeights S == cmTplus) && cmFirst S == k).length)
        = [1, 4, 6, 4, 1]
    := by
  decide

/-- the set of coordinates in which two weights differ, as a bit mask. -/
def cmDiff (a b : Nat) : Nat :=
  (List.range 3).foldl (fun acc t =>
    if cmCoord a t == cmCoord b t then acc else acc + 2 ^ t) 0

/-- the two-element subsets of `T_+` with their difference sets. -/
def cmPairsOfTplus : List (Prod Nat (Prod Nat Nat)) :=
  [(0, 3, cmDiff 0 3), (0, 5, cmDiff 0 5), (0, 6, cmDiff 0 6),
   (3, 5, cmDiff 3 5), (3, 6, cmDiff 3 6), (5, 6, cmDiff 5 6)]

/-- the number of coordinates in a difference mask. -/
def cmMaskSize (m : Nat) : Nat := m % 2 + (m / 2) % 2 + (m / 4) % 2

/-- **The three pairs.**  Every two-element subset of `T_+` differs in
exactly two coordinates, the complement has the same difference set, and
the three difference sets `{1,2}`, `{1,3}`, `{2,3}` (masks `3`, `5`, `6`)
each occur for exactly two subsets. -/
theorem cm_tetrahedron_pairs :
    (cmPairsOfTplus.all fun p => cmMaskSize p.2.2 == 2) = true
    /\ cmDiff 0 3 = cmDiff 5 6 /\ cmDiff 0 5 = cmDiff 3 6 /\ cmDiff 0 6 = cmDiff 3 5
    /\ (cmPairsOfTplus.filter fun p => p.2.2 == 3).length = 2
    /\ (cmPairsOfTplus.filter fun p => p.2.2 == 5).length = 2
    /\ (cmPairsOfTplus.filter fun p => p.2.2 == 6).length = 2
    := by
  decide

/-- the integers `-b, ..., b`. -/
def cmBox (b : Nat) : List Int :=
  (List.range (2 * b + 1)).map fun (k : Nat) => (Int.ofNat k) - (Int.ofNat b)

/-- **The coefficient profile of an exceptional class.**  For integers
`a_1, a_2, a_3` in the box `[-10, 10]`, the three absolute values
`|a_2 - a_3|`, `|a_1 - a_3|`, `|a_1 - a_2|` coincide only when
`a_1 = a_2 = a_3`, and any two of them coincide exactly along one of two
linear relations, each with coefficients that are not all equal. -/
theorem cm_profile_forces_equal :
    ((cmBox 10).all fun a1 => (cmBox 10).all fun a2 => (cmBox 10).all fun a3 =>
      (!((a2 - a3).natAbs == (a1 - a3).natAbs
          && (a1 - a3).natAbs == (a1 - a2).natAbs)
        || (a1 == a2 && a2 == a3))
      && (((a2 - a3).natAbs == (a1 - a3).natAbs)
          == (a1 == a2 || a1 + a2 == 2 * a3))
      && (((a2 - a3).natAbs == (a1 - a2).natAbs)
          == (2 * a2 == a1 + a3 || a1 == a3))
      && (((a1 - a3).natAbs == (a1 - a2).natAbs)
          == (a2 == a3 || 2 * a1 == a2 + a3))) = true := by
  decide

/-- the permutations of `{0, 1, 2, 3}`, as lists of images. -/
def cmPerms : List (List Nat) :=
  (cmQuadsPerm 4)
where
  cmQuadsPerm (n : Nat) : List (List Nat) :=
    (List.range n).flatMap fun a =>
      (List.range n).flatMap fun b =>
        (List.range n).flatMap fun c =>
          (List.range n).filterMap fun d =>
            if a != b && a != c && a != d && b != c && b != d && c != d
            then some [a, b, c, d] else none

/-- the image of `i` under the permutation `p`. -/
def cmAct (p : List Nat) (i : Nat) : Nat := p.getD i 0

/-- the pairing of the four diagonals into two pairs is recorded by the
partner of `0`, one of `1, 2, 3`; `cmPairingAct p q` is the partner of `0`
in the image of the pairing `q` under `p`. -/
def cmPairingAct (p : List Nat) (q : Nat) : Nat :=
  let a := cmAct p 0
  let b := cmAct p q
  if a == 0 then b else if b == 0 then a
  else (List.range 4).foldl (fun acc x =>
    if x != 0 && x != a && x != b then x else acc) 0

/-- the composite `p (p (p i))`. -/
def cmCube (p : List Nat) (i : Nat) : Nat := cmAct p (cmAct p (cmAct p i))

/-- **Three-cycles on the diagonals.**  A permutation of the four diagonals
that fixes none of the three pairings has order three and exactly one fixed
diagonal; and it is one of the eight three-cycles. -/
theorem cm_pairs_three_cycle :
    cmPerms.length = 24
    /\ (cmPerms.all fun p =>
        ([1, 2, 3].all fun q => cmPairingAct p q != q) ==
        (([0, 1, 2, 3].all fun i => cmCube p i == i)
          && ([0, 1, 2, 3].filter fun i => cmAct p i == i).length == 1
          && ([0, 1, 2, 3].any fun i => cmAct p i != i))) = true
    /\ (cmPerms.filter fun p =>
        [1, 2, 3].all fun q => cmPairingAct p q != q).length = 8
    := by
  decide

/-- the binomial coefficient `C(m, 2)`. -/
def cmChoose2 (m : Nat) : Nat := m * (m - 1) / 2

/-- **Abelian subvarieties of half dimension are semiregular: the count.**
For `1 <= n <= 60`, the annihilator of the class of an abelian subvariety of
dimension `n` in an abelian `2n`-fold has dimension
`2 C(2n,2) - 2 C(n,2) + 3 n^2 = 6 n^2 - n`, and the complement in
`HT^2`, of dimension `2 C(2n,2) + 4 n^2`, has dimension `C(2n,2)`, the
dimension of `Ext^2(O_B, O_B)`. -/
theorem cm_abelian_semiregular_count :
    ((List.range 60).all fun k =>
      let n := k + 1
      (2 * cmChoose2 (2 * n) - 2 * cmChoose2 n + 3 * n * n == 6 * n * n - n)
      && (2 * cmChoose2 (2 * n) + 4 * n * n - (6 * n * n - n)
            == cmChoose2 (2 * n))) = true := by
  decide

/-! ## 37.  The exact rank at a quartic field, and a Delsarte sextic

(i) The theorem on the rank of the criterion at a quartic CM field writes
`r(γ) = 64 + 16 μ + 4 ρ_1 + 4 ρ_2 + R_1 + R_2` with `μ ∈ {0, 1}`,
`ρ_t ∈ {0, 1, 2}`, `R_t ∈ {7, 8}`, subject to two conditions proved there:
`μ = 1` forces `ρ_1, ρ_2 ≥ 1`, and `R_t = 7` forces `ρ_t = 2`.  The allowed
tuples give exactly fifteen values, the least being `80`, reached only at
`(0, 0, 0, 8, 8)`; `100` is not a value; with `ρ_1 = ρ_2` the values are the
nine of the corollary on the least object.

(ii) The loop sextic `x_0^5 x_1 + x_1^5 x_2 + ... + x_5^5 x_0` has exponent
matrix `A = 5 I + P`, `P` the cyclic shift, and `A B = 15624 I` for the
circulant `B` with first row `(3125, -625, 125, -25, 5, -1)`, whose row sums
are all `2604 = 15624 / 6`; so the monomial map with exponents `B` carries the
Fermat sextic of degree `15624` onto the loop sextic.  The coefficients of
`(1 + t + t^2 + t^3 + t^4)^6` in the degrees `0, 6, 12, 18, 24` are
`1, 426, 1751, 426, 1`, and their total is `5^6 = 15625`, the dimension of
the Jacobian ring. -/

/-- the value of the rank at a tuple `(μ, ρ_1, ρ_2, R_1, R_2)`. -/
def qrValue (m r1 r2 R1 R2 : Nat) : Nat := 64 + 16 * m + 4 * r1 + 4 * r2 + R1 + R2

/-- the tuples allowed by the two conditions of the theorem. -/
def qrTuples : List (List Nat) :=
  [0, 1].flatMap fun m => [0, 1, 2].flatMap fun r1 => [0, 1, 2].flatMap fun r2 =>
    [7, 8].flatMap fun R1 => [7, 8].flatMap fun R2 =>
      if (m == 1 && (r1 == 0 || r2 == 0)) || (R1 == 7 && r1 != 2)
          || (R2 == 7 && r2 != 2) then [] else [[m, r1, r2, R1, R2]]

/-- the value at a tuple given as a list. -/
def qrVal (t : List Nat) : Nat :=
  qrValue (t.getD 0 0) (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) (t.getD 4 0)

/-- **The fifteen values of the rank at a quartic field.**  The values over
the allowed tuples are exactly the fifteen listed; `80` is the least and is
reached only at `(0, 0, 0, 8, 8)`; `100` is not a value; and with
`ρ_1 = ρ_2` the values are the nine listed in the corollary. -/
theorem quartic_rank_values :
    ([80, 84, 87, 88, 91, 92, 94, 95, 96, 104, 107, 108, 110, 111, 112].all
        fun v => qrTuples.any fun t => qrVal t == v) = true
    /\ (qrTuples.all fun t =>
        [80, 84, 87, 88, 91, 92, 94, 95, 96, 104, 107, 108, 110, 111,
          112].contains (qrVal t)) = true
    /\ (qrTuples.all fun t => 80 ≤ qrVal t) = true
    /\ (qrTuples.filter fun t => qrVal t == 80) = [[0, 0, 0, 8, 8]]
    /\ (qrTuples.all fun t => qrVal t != 100) = true
    /\ ((qrTuples.filter fun t => t.getD 1 0 == t.getD 2 0).all fun t =>
        [80, 88, 94, 95, 96, 104, 110, 111, 112].contains (qrVal t)) = true
    /\ ([80, 88, 94, 95, 96, 104, 110, 111, 112].all fun v =>
        (qrTuples.filter fun t => t.getD 1 0 == t.getD 2 0).any
          fun t => qrVal t == v) = true := by
  decide

/-- the exponent matrix `A = 5 I + P` of the loop sextic. -/
def loopA (i j : Nat) : Int := if j == i then 5 else if j == (i + 1) % 6 then 1 else 0

/-- the circulant `B` with first row `(3125, -625, 125, -25, 5, -1)`. -/
def loopB (i j : Nat) : Int :=
  [3125, -625, 125, -25, 5, -1].getD ((j + 6 - i) % 6) 0

/-- the product of two `6 × 6` integer matrices given as functions. -/
def mat6Mul (M N : Nat → Nat → Int) (i j : Nat) : Int :=
  (List.range 6).foldl (fun acc k => acc + M i k * N k j) 0

/-- multiplication of polynomials with natural coefficients, as lists. -/
def natPolyMul (f g : List Nat) : List Nat :=
  (List.range (f.length + g.length - 1)).map fun k =>
    (List.range (k + 1)).foldl (fun acc i => acc + f.getD i 0 * g.getD (k - i) 0) 0

/-- `(1 + t + t^2 + t^3 + t^4)^6`, the Hilbert series of the Jacobian ring. -/
def loopHilbert : List Nat :=
  (List.range 6).foldl (fun acc _ => natPolyMul acc [1, 1, 1, 1, 1]) [1]

/-- **The Delsarte cover of the loop sextic.**  `A B = 15624 I` with
`15624 = 5^6 - 1`, every row of `B` sums to `2604 = 15624 / 6`, the Jacobian
ring has dimensions `1, 426, 1751, 426, 1` in the degrees `0, 6, 12, 18, 24`
and total dimension `5^6 = 15625`, and `(-5)^6 ≠ 1`, which is what the product
of the partial derivatives needs for smoothness. -/
theorem delsarte_loop_sextic :
    ((List.range 6).all fun i => (List.range 6).all fun j =>
        mat6Mul loopA loopB i j == if i == j then 15624 else 0) = true
    /\ (15624 : Int) = 5 ^ 6 - 1
    /\ ((List.range 6).all fun i =>
        (List.range 6).foldl (fun acc j => acc + loopB i j) 0 == 2604) = true
    /\ 6 * 2604 = 15624
    /\ ([0, 6, 12, 18, 24].map fun k => loopHilbert.getD k 0) = [1, 426, 1751, 426, 1]
    /\ loopHilbert.foldl (· + ·) 0 = 15625
    /\ loopHilbert.length = 25
    /\ ((-5 : Int) ^ 6 != 1) = true := by
  decide

/-! ## 38.  Hypersurfaces of simplex type

A Laurent polynomial whose exponents are affinely independent has, on the
torus, the lattice `M' ⊆ M` spanned by the differences of its exponents; the
exponent `e` of `M / M'` is the degree of the Fermat variety from which the
whole cohomology of a smooth toric compactification comes.  For a Delsarte
hypersurface with exponent matrix `A` the rows `a_i - a_0`, in the
coordinates `1, ..., N-1` of `M = {x : Σ x_j = 0}`, form a matrix `R`, and
`e` is the least integer with `e R^{-1}` integral.

(i) The Klein quartic `x^3 y + y^3 z + z^3 x`: `det A = 28`, `det R = 7`, and
`C R = 7 I` for an integer matrix `C` not divisible by `7`, so `e = 7`.

(ii) The loop sextic: `det R = 2604 = 2^2 · 3 · 7 · 31`, `C R = 2604 I` for
an integer matrix `C` with, for each of the primes `2, 3, 7, 31`, an entry
that it does not divide, so `e = 2604`, not `15624`.

(iii) The Euler number through the orbits: on the orbit where exactly the
coordinates in `S` are nonzero, the hypersurface meets the torus in the zero
set of the rows supported on `S`; the paper's lemma gives its Euler number,
and the sum is `m` times the Euler number `((1 - m)^N - 1)/m + N` of a smooth
hypersurface of degree `m` in `P^{N-1}`: `-4` for the Klein quartic and `2610`
for the loop sextic and the Fermat sextic. -/
/-- the determinant of a square integer matrix, given as its list of rows, by
expansion along the first row; the first argument bounds the recursion. -/
def detF : Nat → List (List Int) → Int
  | 0, _ => 1
  | n + 1, rows =>
    match rows with
    | [] => 1
    | r :: rs =>
      (List.range r.length).foldl (fun acc j =>
        acc + (if j % 2 == 0 then 1 else -1) * r.getD j 0
          * detF n (rs.map fun row => row.eraseIdx j)) 0

/-- the product of two integer matrices given as lists of rows. -/
def matMulL (P Q : List (List Int)) : List (List Int) :=
  P.map fun row => (List.range (Q.headD []).length).map fun j =>
    (List.range row.length).foldl (fun acc k => acc + row.getD k 0 * (Q.getD k []).getD j 0) 0

/-- `c` times the identity matrix of size `n`. -/
def scalarL (n : Nat) (c : Int) : List (List Int) :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then c else 0

/-- `m` times the Euler number of the Delsarte hypersurface of `A`, summed
over the orbits of the torus of `P^{N-1}`: a coordinate point on which no
monomial survives contributes `m`, a stratum with coordinates `S` on which
exactly `|S| ≥ 2` monomials survive contributes `(-1)^{|S|} |det A_{R,S}|`,
and every other stratum contributes `0`. -/
def eulerTimesM (N m : Nat) (A : List (List Int)) : Int :=
  (List.range (2 ^ N)).foldl (fun acc mask =>
    let S := (List.range N).filter fun j => (mask >>> j) % 2 == 1
    let rows := A.filter fun row =>
      (List.range N).all fun j => S.contains j || row.getD j 0 == 0
    if S.length == 0 then acc
    else if S.length == 1 then acc + (if rows.isEmpty then (m : Int) else 0)
    else if rows.length == S.length then
      acc + (if S.length % 2 == 0 then 1 else -1)
        * ((detF N (rows.map fun row => S.map fun j => row.getD j 0)).natAbs : Int)
    else acc) 0

/-- the Klein quartic `x^3 y + y^3 z + z^3 x`. -/
def kleinA : List (List Int) := [[3, 1, 0], [0, 3, 1], [1, 0, 3]]
def kleinR : List (List Int) := [[2, 1], [-1, 3]]
def kleinC : List (List Int) := [[3, -1], [1, 2]]

/-- the loop sextic, its differences `R` and `C = 2604 R^{-1}`. -/
def loopRows : List (List Int) :=
  (List.range 6).map fun i => (List.range 6).map fun j =>
    if j == i then 5 else if j == (i + 1) % 6 then 1 else 0
def loopR : List (List Int) :=
  [[4, 1, 0, 0, 0], [-1, 5, 1, 0, 0], [-1, 0, 5, 1, 0], [-1, 0, 0, 5, 1],
    [-1, 0, 0, 0, 5]]
def loopC : List (List Int) :=
  [[625, -125, 25, -5, 1], [104, 500, -100, 20, -4], [105, -21, 525, -105, 21],
    [100, -20, 4, 520, -104], [125, -25, 5, -1, 521]]

/-- the Fermat sextic. -/
def fermatRows : List (List Int) := scalarL 6 6

theorem simplex_klein_quartic :
    matMulL kleinC kleinR = scalarL 2 7
    /\ detF 2 kleinR = 7
    /\ detF 3 kleinA = 28
    /\ (kleinC.any fun row => row.any fun x => x % 7 != 0) = true
    /\ eulerTimesM 3 4 kleinA = 4 * (-4)
    /\ (4 : Int) * (-4) = (1 - 4) ^ 3 - 1 + 4 * 3 := by
  decide

theorem simplex_loop_sextic :
    matMulL loopC loopR = scalarL 5 2604
    /\ detF 5 loopR = 2604
    /\ ([2, 3, 7, 31].all fun p => loopC.any fun row => row.any fun x => x % p != 0) = true
    /\ 2604 = 2 ^ 2 * 3 * 7 * 31
    /\ eulerTimesM 6 6 loopRows = 6 * 2610
    /\ eulerTimesM 6 6 fermatRows = 6 * 2610
    /\ (6 : Int) * 2610 = (1 - 6) ^ 6 - 1 + 6 * 6 := by
  decide

/-! ## Section 39. The exceptional places of a character at a quartic field

The annihilator in `H^1(T_A)` of a character `omega + p` at a quartic CM field
(`prop:quarticlocus`) gains a deformation that is not `F`-linear at a real
place `tau_t` exactly when the only monomial of `p` with `theta_t`-exponent
`1`, `2` or `3` is `c_t theta_t^2` and `16 c_t^2 = u_s u_s'`.  The computation
lives in the exterior algebra of `V_s + V_s'`, on the eight generators
`a_{s,k}` (bit `k`), `b_{s,k}` (bit `2 + k`), `a_{s',k}` (bit `4 + k`) and
`b_{s',k}` (bit `6 + k`), with `theta = sum_k a_{s,k} b_{s',k} + a_{s',k} b_{s,k}`
and `alpha_s`, `alpha_s'` the products of the four generators of `V_s`,
`V_s'`.  An element is a list of pairs (bit mask, integer coefficient), and
`vOp x y` replaces the generator `y` by `x`, the action of an element of
`H^1(T_A)`.  The theorem checks:

(i) `theta^4 = 24 alpha_s alpha_s'` and `(alpha_s + alpha_s')^2 = 2 alpha_s alpha_s'`,
so `16 c^2 = u_s u_s'` is `c^2 theta^4 = (3/4) omega_t^2`;

(ii) `theta^3 D = 0` for the four `D = b_{s,k} b_{s',l}`, and the `theta^2 D`
are single monomials with distinct masks, so multiplication by `theta^2` is
injective on `V_s^{0,1} (x) V_s'^{0,1}`;

(iii) the element `xi'_0 = (a_{s,1} -> b_{s',0}) - (a_{s,0} -> b_{s',1})` has
`xi'_0 _| alpha_s = theta b_{s,0} b_{s,1}`, `xi'_0 _| theta = 2 b_{s',0} b_{s',1}`
and `xi'_0 _| theta^2 = 4 theta b_{s',0} b_{s',1}`, and `xi''_0`, with `s` and
`s'` exchanged, the same; so for `xi' = x xi'_0`, `xi'' = y xi''_0` the two
equations are `u_s x + 4 c y = 0` and `u_s' y + 4 c x = 0`, of determinant
`u_s u_s' - 16 c^2`;

(iv) the counts: the rational exceptional characters have rank
`64 + 16 mu + 4 * 2 + 4 * 2 + 7 + 7`, that is `94` or `110`; the annihilator
has dimension `8 + 4 a + b`, the values `8, 9, 10, 12, 13, 16`; and
`so(4,3)` has dimension `21` with maximal compact `so(4) + so(3)` of dimension
`9`, against `15` and `7` for `su(2,2)`, the orbits having dimension
`21 - 16 = 5` and `15 - 11 = 4`. -/
abbrev Ext8 := List (Nat × Int)

/-- the number of set bits of `m` below position `g`. -/
def popBelow (m g : Nat) : Nat :=
  ((List.range g).filter fun i => (m >>> i) % 2 == 1).length

/-- collect equal monomials and drop zero coefficients. -/
def norm8 (f : Ext8) : Ext8 :=
  (List.range 256).filterMap fun m =>
    let c := (f.filter fun p => p.1 == m).foldl (fun a p => a + p.2) 0
    if c == 0 then none else some (m, c)

/-- the sign of the product of the monomials `m1` and `m2`. -/
def wSign (m1 m2 : Nat) : Int :=
  let cnt := (List.range 8).foldl
    (fun acc i => if (m1 >>> i) % 2 == 1 then acc + popBelow m2 i else acc) 0
  if cnt % 2 == 0 then 1 else -1

def wedge8 (f g : Ext8) : Ext8 :=
  norm8 (f.flatMap fun p => g.filterMap fun q =>
    if p.1 &&& q.1 != 0 then none else some (p.1 ||| q.1, wSign p.1 q.1 * p.2 * q.2))

def gen8 (i : Nat) : Ext8 := [(2 ^ i, 1)]
def mono8 (l : List Nat) : Ext8 := l.foldl (fun f i => wedge8 f (gen8 i)) [(0, 1)]
def add8 (f g : Ext8) : Ext8 := norm8 (f ++ g)
def smul8 (c : Int) (f : Ext8) : Ext8 := norm8 (f.map fun p => (p.1, c * p.2))

/-- replace the generator `y` by `x`: contract `y`, then wedge `x`. -/
def vOp (x y : Nat) (f : Ext8) : Ext8 :=
  norm8 (f.filterMap fun p =>
    if (p.1 >>> y) % 2 == 0 then none else
    let s1 : Int := if popBelow p.1 y % 2 == 0 then 1 else -1
    let mm := p.1 - 2 ^ y
    if (mm >>> x) % 2 == 1 then none else
    let s2 : Int := if popBelow mm x % 2 == 0 then 1 else -1
    some (mm + 2 ^ x, s1 * s2 * p.2))

def thetaQ : Ext8 :=
  add8 (add8 (mono8 [0, 6]) (mono8 [1, 7])) (add8 (mono8 [4, 2]) (mono8 [5, 3]))
def alphaS : Ext8 := mono8 [0, 1, 2, 3]
def alphaS' : Ext8 := mono8 [4, 5, 6, 7]
def xiP (f : Ext8) : Ext8 := add8 (vOp 6 1 f) (smul8 (-1) (vOp 7 0 f))
def xiPP (f : Ext8) : Ext8 := add8 (vOp 2 5 f) (smul8 (-1) (vOp 3 4 f))
def theta2Q : Ext8 := wedge8 thetaQ thetaQ
def theta3Q : Ext8 := wedge8 theta2Q thetaQ
def theta4Q : Ext8 := wedge8 theta3Q thetaQ
def dPairs : List Ext8 := [mono8 [2, 6], mono8 [2, 7], mono8 [3, 6], mono8 [3, 7]]

theorem quartic_exceptional_pair :
    theta4Q = smul8 24 (wedge8 alphaS alphaS')
    /\ wedge8 (add8 alphaS alphaS') (add8 alphaS alphaS') = smul8 2 (wedge8 alphaS alphaS')
    /\ (dPairs.all fun d => (wedge8 theta3Q d).isEmpty) = true
    /\ (dPairs.map fun d => ((wedge8 theta2Q d).map Prod.fst)) = [[238], [237], [222], [221]]
    /\ xiP alphaS = wedge8 thetaQ (mono8 [2, 3])
    /\ xiP thetaQ = smul8 2 (mono8 [6, 7])
    /\ xiP theta2Q = smul8 4 (wedge8 thetaQ (mono8 [6, 7]))
    /\ xiPP alphaS' = wedge8 thetaQ (mono8 [6, 7])
    /\ xiPP thetaQ = smul8 2 (mono8 [2, 3])
    /\ xiPP theta2Q = smul8 4 (wedge8 thetaQ (mono8 [2, 3])) := by
  decide

theorem quartic_locus_counts :
    ([0, 1].map fun mu => 64 + 16 * mu + 4 * 2 + 4 * 2 + 7 + 7) = [94, 110]
    /\ ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)].map fun ab : Nat × Nat =>
          8 + 4 * ab.1 + ab.2) = [8, 9, 10, 12, 13, 16]
    /\ 7 * 6 / 2 = 21 /\ 4 * 3 / 2 + 3 * 2 / 2 = 9 /\ 21 - 9 = 12
    /\ 4 * 4 - 1 = 15 /\ 2 * 2 + 2 * 2 - 1 = 7 /\ 15 - 7 = 8
    /\ 21 - 16 = 5 /\ 15 - 11 = 4 /\ 21 - 11 = 2 * 5
    /\ 2 ^ 3 = 8 /\ 4 * 24 = 3 * 2 * 16 := by
  decide

/-! ## 40.  The local obstruction for a quartic secant character

Three finite facts behind Lemma (Free germs on smooth supports), Theorem (The
local obstruction for a quartic secant character) and Proposition (The classes
of Markman's candidate).

(a) The Koszul computation.  For `k = R/(x_1,...,x_c)` over `R = Q[x_1..x_4]`
the resolution is the Koszul complex, the jet chain map of `d/dx_k` is
`-(d/dx_k)` of the differential, and the Yoneda square of two jet classes is
represented by the constant matrix `(-D_k d_1)(-D_l d_2)`, a vector indexed by
the pairs `a < b <= c`; the coboundaries vanish at the origin because every
entry of `d_2` is a linear form.  The theorem computes the vector for every
`k, l <= 4` and `c = 3, 4` and finds it nonzero exactly when `k != l` and both
are at most `c`: the products of the translation classes of a line bundle on
a smooth curve, or of a skyscraper, are the projections to `wedge^2 N`.

(b) The exterior algebra on `H^1(X) = U_1 + U_2` with generators
`0 p_11, 1 p_12, 2 q_11, 3 q_12, 4 p_21, 5 p_22, 6 q_21, 7 q_22`, the classes
`theta_j = p_j1 q_j1 + p_j2 q_j2`, `A_j = 1 - theta_j^2` (the value `q = 2`),
the four classes `A_1 A_2`, `theta_1 theta_2`, `theta_1 A_2`, `theta_2 A_1`
spanning `S(0,2)`, and the action of `HT^2`: a class of `H^{0,2}` by
multiplication, a class of `Hom(H^{1,0},H^{0,1})` as a derivation, a bivector
`d_a d_b` by the composite interior product.  The theorem checks that the
compensated bivectors `x_j = (pi_j _| theta_j^2, 0, pi_j)`, `j = 1, 2`,
annihilate the four spanning classes, and that the six symmetric maps at the
two places annihilate `theta_1` and `theta_2`.

(c) Two rank certificates.  With the stand-in values `f_1 = 2`, `f_2 = 1/2`,
`4 beta' = 16 theta_1 A_2 + theta_2 A_1` and `alpha_0 = theta_1 A_2 + theta_2 A_1`
are integral, and the contraction matrices `HT^2 -> H^*` have `20 x 20` and
`12 x 12` minors that are nonzero modulo the prime `1000003`; the rows and
columns are the ones item (LXVIII) found, and the kernel recomputes the entries
and the rank of the minors.  Rank does not go up under reduction modulo a
prime, so the contraction has rank at least `20`, resp. `12`, over `Q`; with
the `8`, resp. `16`, independent annihilating classes of (b) and of Theorem
(Reduction to the factor) this is equality.
-/

/-- the number of set bits of `m` in positions `[0, a)`. -/
def qBitsBelow (m a : Nat) : Nat := (List.range a).countP (fun i => m.testBit i)

/-- the number of set bits of `m` in positions `(j, 8)`. -/
def qBitsAbove (m j : Nat) : Nat :=
  (List.range 8).countP (fun i => j < i && m.testBit i)

/-- the sign of `e_a e_b -> e_{a | b}` for disjoint masks `a`, `b`, with the
generators written in increasing order. -/
def qShuffleSign (a b : Nat) : Int :=
  if ((List.range 8).foldl (fun s j => if b.testBit j then s + qBitsAbove a j else s) 0) % 2 == 0
  then 1 else -1

/-- an element of the exterior algebra on eight generators: the coefficient
of every monomial `m < 256`. -/
abbrev QElt := List Int

def qZero : QElt := List.replicate 256 0
def qOne : QElt := (List.range 256).map (fun m => if m == 0 then 1 else 0)
def qMono (m : Nat) : QElt := (List.range 256).map (fun k => if k == m then 1 else 0)

def qGet (u : QElt) (m : Nat) : Int := u.getD m 0

def qAdd (u v : QElt) : QElt := List.zipWith (fun a b => a + b) u v
def qScale (c : Int) (u : QElt) : QElt := u.map (fun a => c * a)
def qNeg (u : QElt) : QElt := u.map (fun a => -a)

/-- `c e_m` wedge `u`. -/
def qWedgeMono (m : Nat) (c : Int) (u : QElt) : QElt :=
  (List.range 256).map fun k =>
    if k &&& m == m then
      let n := k ^^^ m
      qShuffleSign m n * c * qGet u n
    else 0

/-- `u` wedge `v`, summing over the nonzero monomials of `u`. -/
def qWedge (u v : QElt) : QElt :=
  (List.range 256).foldl
    (fun acc m => let c := qGet u m; if c == 0 then acc else qAdd acc (qWedgeMono m c v))
    qZero

/-- the interior product with the generator `a`. -/
def qInterior (a : Nat) (u : QElt) : QElt :=
  (List.range 256).map fun k =>
    if k.testBit a then 0
    else
      let n := k ||| (1 <<< a)
      (if qBitsBelow n a % 2 == 0 then 1 else -1) * qGet u n

/-- the even derivation `e_i -> e_k`, `e_j -> 0` for `j != i`. -/
def qDeriv (i k : Nat) (u : QElt) : QElt :=
  (List.range 256).map fun m' =>
    if m'.testBit k && !(m'.testBit i) then
      let m := (m' ^^^ (1 <<< k)) ||| (1 <<< i)
      let lo := if i < k then i else k
      let hi := if i < k then k else i
      let between := (List.range 8).countP (fun j => lo < j && j < hi && m.testBit j)
      (if between % 2 == 0 then 1 else -1) * qGet u m
    else 0

def qIsZero (u : QElt) : Bool := u.all (fun a => a == 0)

/-- `theta_1 = p_11 q_11 + p_12 q_12`, `theta_2 = p_21 q_21 + p_22 q_22`. -/
def qTheta1 : QElt := qAdd (qMono ((1 <<< 0) ||| (1 <<< 2))) (qMono ((1 <<< 1) ||| (1 <<< 3)))
def qTheta2 : QElt := qAdd (qMono ((1 <<< 4) ||| (1 <<< 6))) (qMono ((1 <<< 5) ||| (1 <<< 7)))
def qTheta1Sq : QElt := qWedge qTheta1 qTheta1
def qTheta2Sq : QElt := qWedge qTheta2 qTheta2
/-- `A_j = 1 - theta_j^2`, the value `q = 2`. -/
def qA1 : QElt := qAdd qOne (qNeg qTheta1Sq)
def qA2 : QElt := qAdd qOne (qNeg qTheta2Sq)
/-- the four classes spanning `S(0,2)`. -/
def qSpan : List QElt :=
  [qWedge qA1 qA2, qWedge qTheta1 qTheta2, qWedge qTheta1 qA2, qWedge qTheta2 qA1]
/-- `alpha_0` and `4 beta'` for `f_1 = 2`, `f_2 = 1/2`. -/
def qAlpha0 : QElt := qAdd (qWedge qTheta1 qA2) (qWedge qTheta2 qA1)
def qBeta4 : QElt := qAdd (qScale 16 (qWedge qTheta1 qA2)) (qWedge qTheta2 qA1)

/-- the bivector `pi_j` acting as `i_a i_b` with `(a,b) = (0,1)` or `(4,5)`. -/
def qPi (a b : Nat) (u : QElt) : QElt := qInterior a (qInterior b u)

/-- `x_j _| v = (pi_j _| theta_j^2) v + pi_j _| v`, the value `q = 2`. -/
def qXapply (a b : Nat) (thSq v : QElt) : QElt :=
  qAdd (qWedge (qPi a b thSq) v) (qPi a b v)

/-- **The compensated bivectors annihilate the secant space.**  For
`q = 2` the classes `x_1 = (pi_1 _| theta_1^2, 0, pi_1)` and
`x_2 = (pi_2 _| theta_2^2, 0, pi_2)` kill the four classes spanning `S(0,2)`,
and the six symmetric maps at the two places kill `theta_1` and `theta_2`. -/
theorem quartic_compensated_bivectors :
    ((qSpan.all fun v => qIsZero (qXapply 0 1 qTheta1Sq v) && qIsZero (qXapply 4 5 qTheta2Sq v))
      && ([qTheta1, qTheta2].all fun t =>
          qIsZero (qDeriv 0 2 t) && qIsZero (qDeriv 1 3 t)
          && qIsZero (qAdd (qDeriv 0 3 t) (qDeriv 1 2 t))
          && qIsZero (qDeriv 4 6 t) && qIsZero (qDeriv 5 7 t)
          && qIsZero (qAdd (qDeriv 4 7 t) (qDeriv 5 6 t)))) = true := by
  decide +kernel

/-! ### The rank certificates -/

/-- the `28` rows of the contraction matrix of `v`: six products with the
`(0,2)`-forms `q_a q_b`, sixteen derivations `p_i -> q_k`, six bivectors. -/
def qRows (v : QElt) : List QElt :=
  ([(2,3),(2,6),(2,7),(3,6),(3,7),(6,7)].map fun ab => qWedge (qMono ((1 <<< ab.1) ||| (1 <<< ab.2))) v)
  ++ ((([0,1,4,5].map fun i => [2,3,6,7].map fun k => qDeriv i k v).foldl (fun acc l => acc ++ l) []))
  ++ ([(0,1),(0,4),(0,5),(1,4),(1,5),(4,5)].map fun ab => qPi ab.1 ab.2 v)

def qPrime : Nat := 1000003

def qModP (x : Int) : Nat := (Int.emod x (Int.ofNat qPrime)).toNat

/-- the submatrix on the given rows and columns, reduced modulo the prime. -/
def qMinor (v : QElt) (rows cols : List Nat) : List (List Nat) :=
  let R := qRows v
  rows.map fun i => cols.map fun c => qModP (qGet (R.getD i qZero) c)

/-- modular exponentiation by squaring, with fuel. -/
def qPowModAux : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e == 0 then acc
    else qPowModAux fuel (b * b % qPrime) (e / 2) (if e % 2 == 1 then acc * b % qPrime else acc)

/-- the inverse modulo the prime, by Fermat. -/
def qInv (a : Nat) : Nat := qPowModAux 40 (a % qPrime) (qPrime - 2) 1

/-- subtract `f` times the normalised pivot row, where `f` is the leading
entry of `row`, so that the leading entry becomes zero. -/
def qEliminate (pivot row : List Nat) : List Nat :=
  let f := row.getD 0 0
  List.zipWith (fun r p => (r + (qPrime - f % qPrime) * p) % qPrime) row pivot

/-- the rank modulo the prime: Gaussian elimination on the first column,
which is then dropped. -/
def qRankAux : Nat -> List (List Nat) -> Nat
  | 0, _ => 0
  | fuel + 1, M =>
    match M with
    | [] => 0
    | row0 :: _ =>
      if row0.length == 0 then 0
      else
        match M.find? (fun row => row.getD 0 0 != 0) with
        | none => qRankAux fuel (M.map fun row => row.drop 1)
        | some p =>
          let inv := qInv (p.getD 0 0)
          let pnorm := p.map fun x => x * inv % qPrime
          let rest := (M.filter fun row => row != p).map fun row => (qEliminate pnorm row).drop 1
          1 + qRankAux fuel rest

def qRank (M : List (List Nat)) : Nat := qRankAux 64 M

def qRowsBeta : List Nat := [0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14, 15, 17, 18, 19, 23, 24, 25, 26]
def qColsBeta : List Nat :=
  [12, 68, 72, 77, 78, 92, 132, 136, 141, 142, 192, 197, 212, 216, 221, 222, 228, 232, 237, 238]
def qRowsAlpha : List Nat := [0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 17]
def qColsAlpha : List Nat := [12, 68, 72, 77, 78, 92, 132, 136, 141, 142, 192, 197]

/-- **The contraction ranks of Markman's classes.**  A `20 x 20` minor of the
contraction matrix of `4 beta'` and a `12 x 12` minor of that of `alpha_0` are
invertible modulo `1000003`, so the ranks over `Q` are at least `20` and `12`;
they are at most that by the annihilating classes. -/
theorem quartic_rank_certificates :
    ((qRank (qMinor qBeta4 qRowsBeta qColsBeta) == 20)
      && (qRank (qMinor qAlpha0 qRowsAlpha qColsAlpha) == 12)) = true := by
  decide +kernel

/-! ### The Koszul computation -/

/-- a linear form in `x_1..x_4`: its constant term and four coefficients. -/
abbrev QLin := List Int

def qVar (k : Nat) : QLin := (List.range 5).map fun i => if i == k then 1 else 0
def qLinZero : QLin := List.replicate 5 0
def qLinNeg (l : QLin) : QLin := l.map (fun a => -a)
/-- `d/dx_k` of a linear form, `k = 1..4`. -/
def qDiff (k : Nat) (l : QLin) : Int := l.getD k 0

/-- the pairs `a < b <= c`. -/
def qPairs (c : Nat) : List (Prod Nat Nat) :=
  ((List.range c).map fun a => (List.range c).filterMap fun b =>
      if a + 1 <= b then some (a + 1, b + 1) else none).foldl (fun acc l => acc ++ l) []

/-- `d_1 = (x_1, ..., x_c)`: entry `i`. -/
def qD1 (c i : Nat) : QLin := if i < c then qVar (i + 1) else qLinZero

/-- `d_2 (e_a e_b) = x_a e_b - x_b e_a`: the entry in row `i` and column `(a,b)`. -/
def qD2 (i : Nat) (ab : Prod Nat Nat) : QLin :=
  if i + 1 == ab.2 then qVar ab.1 else if i + 1 == ab.1 then qLinNeg (qVar ab.2) else qLinZero

/-- the constant matrix `(-D_k d_1)(-D_l d_2)` as a vector over the pairs. -/
def qSquare (c k l : Nat) : List Int :=
  (qPairs c).map fun ab =>
    (List.range c).foldl (fun s i => s + qDiff k (qD1 c i) * qDiff l (qD2 i ab)) 0

/-- **The Koszul squares of a line bundle on a smooth curve and of a
skyscraper.**  For `c = 3` and `c = 4` every entry of `d_2` has zero constant
term, and the vector representing `a_k a_l` is nonzero exactly when `k != l`
and both are at most `c`. -/
theorem quartic_koszul_squares :
    ([3, 4].all fun c =>
      ((qPairs c).all fun ab => (List.range c).all fun i => (qD2 i ab).getD 0 0 == 0)
      && ((List.range 4).all fun k => (List.range 4).all fun l =>
            ((qSquare c (k + 1) (l + 1)).any (fun x => x != 0))
              == (k != l && k + 1 <= c && l + 1 <= c))) = true := by
  decide

/-- **A line lies in at most one of two complementary planes.**  For every
nonzero `l` in `[-6,6]^4`, the bivector of the plane `(e_1,e_2)` or that of
`(e_3,e_4)` has nonzero wedge with `l`, that is, nonzero image in
`wedge^2 (T/l)`. -/
theorem quartic_line_two_planes :
    ((List.range 13).all fun a => (List.range 13).all fun b =>
      (List.range 13).all fun c => (List.range 13).all fun d =>
        let l := [Int.ofNat a - 6, Int.ofNat b - 6, Int.ofNat c - 6, Int.ofNat d - 6]
        (l.all fun x => x == 0)
        || ((l.getD 2 0 != 0 || l.getD 3 0 != 0) || (l.getD 0 0 != 0 || l.getD 1 0 != 0))) = true := by
  decide

/-! ### The character of Markman's first factor

In `Q[Theta]/(Theta^5)` with `[pt] = Theta^4/24`, a class is a list of five
coefficients; scaled by `24` they are integers.  The theorem repeats the
bookkeeping of Example 8.2.4 of the paper cited as [Mar25a]: `e_* O_Theta(Theta)`
has `24 ch = (0,24,12,4,1)`, `O_{W_2}` has `24 ch = (0,0,12,-8,3)`, the
twist by `e^Theta` gives `(0,0,12,4,1)`, so the ideal of the Weil divisor
`W_{2,p}` twisted by `Theta` has character exactly `Theta`; `O_{W_1}` has
`24 ch = (0,0,0,4,-3)` and its twist `(0,0,0,4,1)`; and removing `d` curves
meeting the surface in one point each gives `24 ch(F_d) = (0,24,0,-4d,0)`,
that is `ch(F_d) = Theta - (d/6) Theta^3`, with `chi(F_d,F_d) = 8d`. -/

/-- truncated product of two classes scaled by `24`: the result is scaled by `576`. -/
def qTrunc (a b : List Int) : List Int :=
  (List.range 5).map fun k =>
    (List.range (k + 1)).foldl (fun s i => s + a.getD i 0 * b.getD (k - i) 0) 0

def qE24 : List Int := [24, 24, 12, 4, 1]          -- 24 e^Theta
def qOThetaT : List Int := [0, 24, 12, 4, 1]       -- 24 ch(e_* O_Theta(Theta))
def qOW2 : List Int := [0, 0, 12, -8, 3]           -- 24 ch(O_{W_2})
def qOW1 : List Int := [0, 0, 0, 4, -3]            -- 24 ch(O_{W_1})
def qPt : List Int := [0, 0, 0, 0, 1]              -- 24 [pt]

def qListSub (a b : List Int) : List Int := List.zipWith (fun x y => x - y) a b
def qListScale (c : Int) (a : List Int) : List Int := a.map (fun x => c * x)
def qDual (a : List Int) : List Int :=
  (List.range 5).map fun k => if k % 2 == 0 then a.getD k 0 else - a.getD k 0

/-- `24 ch(O_{W_2}(Theta))` and `24 ch(O_{W_1}(Theta))`, as `(24 e^Theta)(24 ch)/24`. -/
def qOW2T : List Int := (qTrunc qE24 qOW2).map (fun x => x / 24)
def qOW1T : List Int := (qTrunc qE24 qOW1).map (fun x => x / 24)
/-- `24 ch(F_d)`. -/
def qFd (d : Nat) : List Int :=
  qListSub (qListSub qOThetaT qOW2T) (qListSub (qListScale (Int.ofNat d) qOW1T) (qListScale (Int.ofNat d) qPt))

/-- **The character of Markman's first factor.**  The twisted classes are the
ones of Example 8.2.4, the ideal of the Weil divisor has character `Theta`,
and `ch(F_d) = Theta - (d/6) Theta^3` with `chi(F_d, F_d) = 8 d`, for `d <= 60`. -/
theorem quartic_first_factor_character :
    ((qTrunc qE24 qOW2).all (fun x => x % 24 == 0) && (qTrunc qE24 qOW1).all (fun x => x % 24 == 0)
      && (qOW2T == [0, 0, 12, 4, 1]) && (qOW1T == [0, 0, 0, 4, 1])
      && (qListSub qOThetaT qOW2T == [0, 24, 0, 0, 0])
      && ((List.range 61).all fun d =>
            (qFd d == [0, 24, 0, -4 * Int.ofNat d, 0])
            && ((qTrunc (qDual (qFd d)) (qFd d)).getD 4 0 == 576 * 8 * Int.ofNat d / 24))) = true := by
  decide

/-! ## 41.  Convolutions of line bundles

Four finite facts behind Proposition (A pure Weil class from line bundles),
Proposition (Nothing enters the diagonal), Proposition (Cup products on the
diagonal) and Theorem (The diagonal on E_0^6).

(a) The pure Weil identity.  Write `zeta_j = i^(e_j)` with `e_j < 4`; the
pieces are the `zeta` with `prod zeta = +-1`, that is `sum e_j` even.  On the
surface `B_j` the exponential of the first Chern class is
`e^(p(a_j + b_j)) (1 + zeta_j c_j + conj(zeta_j) c'_j + c_j c'_j)`, so the
signed sum of `e^(c_1(L_zeta))` is a sum over monomials `m = (m_j)` with
`m_j` one of `1, c_j, c'_j, c_j c'_j` (coded `0, 1, 2, 3`) of the Gaussian
integer `S(m) = sum_zeta prod(zeta) prod_j kappa(m_j, zeta_j)`, where
`kappa` is `1`, `zeta_j`, `conj(zeta_j)`, `1`.  Every factor is a power of
`i`, so `S(m)` is a count of exponents modulo `4`.  The theorem checks, for
`n = 2, 3, 4`, that there are `2 * 4^(n-1)` pieces, half of each sign, and
that `S(m)` is `2 * 4^(n-1)` for `m = (c_1, ..., c_n)` and for
`m = (c'_1, ..., c'_n)`, whose products are `alpha` and `conj(alpha)`, and
`0` for every other monomial.  Since `a_j c_j = b_j c_j = 0` and likewise for
`c'_j`, this is the identity of the proposition.

(b) The cup kernel at `n = 3`.  For each of the six types `tau` of the
diagonal classes, the graph `Gamma_tau` on the `32` pieces has an edge for a
sign change of one coordinate where `tau` vanishes, and for a multiplication
of the other two coordinates by `(i, i)` or `(-i, -i)` where `tau` is `2`.
The theorem grows the component of every piece until it is closed, counts
the components (`4` when `tau` has an entry `2`, `16` otherwise), and adds
up `components * dim` over the types: `3 * 4 * 1 + 3 * 16 * 4 = 204`, and
`204 + 45 = 249` with the classes of the three multiples.

(c) The excess of a run.  The values `p, t_1, t_2, t_3` are distinct; a
step of degree one between pieces with a definite difference has excess `-1`
going up and `2n - 1` going down.  For `3 <= n <= 12`, every placement of
`p` among the `t_i`, and every run `L -> M_(s_1) -> ... -> M_(s_k) -> L`
through distinct multiples, the excess is at least `2n - 4 >= 2`, and a
closed walk through the multiples alone has excess at least `2n - 3`; at
`n = 2` a run of excess `0` exists.

(d) The surviving path.  Along `M_2 -> M_3 -> L -> M_1` with `Ext` degrees
`0, 6, 0` every step has degree one exactly when the shifts are `d, d + 1,
d - 4, d - 3`, and then the product with a class of `H^2(O_A)` lands in
`Ext` degree `3 + d - (d - 3) = 6`, with `sigma_1 = sigma_3 = -sigma_2`.
The target has dimension `(t_2 - t_1)^6`, which is `1` or `64` for the gaps
`1, 2`, leaving `248` or `185` of the `249` classes, both more than
`r = 7 * 3^2 - 2 * 3 = 57`, and at least `192 = 249 - 57` exactly from the
gap `3` on.
-/

/-- all lists of length `n` with entries below `4`. -/
def cvTuples : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (cvTuples n).flatMap (fun t => (List.range 4).map (fun a => a :: t))

def cvSum (l : List Nat) : Nat := l.foldl (· + ·) 0

/-- the pieces: exponent vectors with `prod zeta = +-1`, that is even sum. -/
def cvPieces (n : Nat) : List (List Nat) :=
  (cvTuples n).filter (fun z => cvSum z % 2 == 0)

/-- the exponent of `i` in `kappa(m_j, zeta_j)`: `e` for `c`, `-e` for `c'`,
`0` for `1` and `c c'`. -/
def cvKappa (m e : Nat) : Nat :=
  if m == 1 then e else if m == 2 then (4 - e) % 4 else 0

/-- `S(m)`, as the Gaussian integer `(re, im)`. -/
def cvS (n : Nat) (m : List Nat) : Int × Int :=
  (cvPieces n).foldl (fun acc z =>
    let k := (cvSum z + cvSum (List.zipWith cvKappa m z)) % 4
    if k == 0 then (acc.1 + 1, acc.2) else if k == 1 then (acc.1, acc.2 + 1)
    else if k == 2 then (acc.1 - 1, acc.2) else (acc.1, acc.2 - 1)) (0, 0)

/-- **The pure Weil identity.**  For `n = 2, 3, 4` there are `2 * 4^(n-1)`
pieces, half with `prod zeta = 1`, and the signed sum of the `e^(c_1(L_zeta))`
has coefficient `2 * 4^(n-1)` on `alpha` and on `conj(alpha)` and `0` on
every other monomial in the `c_j`, `c'_j`. -/
theorem conv_pure_weil_identity :
    ([2, 3, 4].all fun n =>
      ((cvPieces n).length == 2 * 4 ^ (n - 1))
      && (((cvPieces n).filter (fun z => cvSum z % 4 == 0)).length == 4 ^ (n - 1))
      && ((cvTuples n).all fun m =>
            cvS n m == (if m.all (· == 1) || m.all (· == 2)
                        then (Int.ofNat (2 * 4 ^ (n - 1)), 0) else (0, 0)))) = true := by
  decide +kernel

/-- the piece `z` with its coordinate `j` multiplied by `i^d`. -/
def cvTurn (z : List Nat) (j d : Nat) : List Nat :=
  (List.range z.length).map (fun k => if k == j then (z.getD k 0 + d) % 4 else z.getD k 0)

/-- the neighbours of `z` in `Gamma_tau`. -/
def cvNbrs (tau z : List Nat) : List (List Nat) :=
  ((List.range z.length).filter (fun j => tau.getD j 0 == 0)).map (fun j => cvTurn z j 2)
  ++ ((List.range z.length).filter (fun j => tau.getD j 0 == 2)).flatMap (fun j =>
       [1, 3].map (fun d =>
         ((List.range z.length).filter (· != j)).foldl (fun w k => cvTurn w k d) z))

def cvInsert (S : List (List Nat)) (w : List Nat) : List (List Nat) :=
  if S.contains w then S else S ++ [w]

def cvGrow (tau : List Nat) (S : List (List Nat)) : List (List Nat) :=
  (S.flatMap (cvNbrs tau)).foldl cvInsert S

def cvReach (tau z : List Nat) : Nat → List (List Nat)
  | 0 => [z]
  | k + 1 => cvGrow tau (cvReach tau z k)

/-- the position of `w` in `P`. -/
def cvIndex (P : List (List Nat)) (w : List Nat) : Nat :=
  (((P.zip (List.range P.length)).find? (fun q => q.1 == w)).map (·.2)).getD P.length

/-- the number of components: pieces that come first in their component. -/
def cvComponents (tau : List Nat) : Nat :=
  let P := cvPieces 3;
  ((List.range P.length).filter (fun i =>
    (cvReach tau (P.getD i []) 6).all (fun w => i ≤ cvIndex P w))).length

/-- the types of the diagonal classes of degree two at `n = 3`. -/
def cvTypes : List (List Nat) :=
  (cvTuples 3).filter (fun t => t.all (· ≤ 2) && cvSum t == 2)

/-- `dim H^(tau_1)(O) (x) H^(tau_2)(O) (x) H^(tau_3)(O)` on three surfaces. -/
def cvDim (tau : List Nat) : Nat := tau.foldl (fun a t => a * (if t == 1 then 2 else 1)) 1

set_option maxHeartbeats 4000000 in
/-- **The cup kernel.**  The six types have dimensions adding up to `15`; the
component of every piece in `Gamma_tau` is closed after six steps and stays
among the pieces; there are `4` components when `tau` has an entry `2` and
`16` otherwise; and the classes constant on components span
`3 * 4 * 1 + 3 * 16 * 4 = 204` dimensions, `249` with the `45` classes of the
multiples, out of `35 * 15 = 525`. -/
theorem conv_cup_kernel :
    (cvTypes.length == 6
      && ((cvTypes.map cvDim).foldl (· + ·) 0 == 15)
      && (cvTypes.all fun tau => (cvPieces 3).all fun z =>
            let R := cvReach tau z 6;
            (cvGrow tau R).length == R.length && R.all (fun w => (cvPieces 3).contains w))
      && (cvTypes.all fun tau => cvComponents tau == (if tau.contains 2 then 4 else 16))
      && ((cvTypes.map (fun tau => cvComponents tau * cvDim tau)).foldl (· + ·) 0 == 204)
      && (204 + 3 * 15 == 249) && (35 * 15 == 525) && (525 - 249 == 276)) = true := by
  decide +kernel

/-- the excess of a step of degree one from the value of rank `a` to that of
rank `b`: `-1` up, `2n - 1` down. -/
def cvStep (n a b : Nat) : Int := if a < b then -1 else 2 * Int.ofNat n - 1

def cvWalk (n : Nat) (vals : List Nat) : Int :=
  ((vals.zip vals.tail).map (fun q => cvStep n q.1 q.2)).foldl (· + ·) 0

/-- the ordered selections of `k` distinct elements of `l`. -/
def cvSelections : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | l, k + 1 => l.flatMap (fun a => (cvSelections (l.filter (· != a)) k).map (a :: ·))

/-- **The excess of a run.**  For `3 <= n <= 12`, with `p` at any rank `r`
among the four values, every run from `L` through distinct multiples back to
`L` has excess at least `2n - 4 >= 2`, and every closed walk through distinct
multiples alone has excess at least `2n - 3`; at `n = 2` the run up through
the three multiples and down once has excess `0`. -/
theorem conv_run_excess :
    (((List.range 10).all fun i =>
      let n := i + 3;
      (List.range 4).all fun r =>
        let ms := (List.range 4).filter (· != r);
        ([1, 2, 3].all fun k => (cvSelections ms k).all fun s =>
            decide (cvWalk n ([r] ++ s ++ [r]) ≥ 2 * Int.ofNat n - 4))
        && ([2, 3].all fun k => (cvSelections ms k).all fun s =>
            decide (cvWalk n (s ++ [s.headD 0]) ≥ 2 * Int.ofNat n - 3))
        && decide (2 * Int.ofNat n - 4 ≥ 2))
    && (cvWalk 2 [0, 1, 2, 3, 0] == 0)) = true := by
  decide +kernel

/-- **The surviving path.**  Along `M_2 -> M_3 -> L -> M_1` with `Ext`
degrees `0, 6, 0`, every step has degree one for the shifts `d, d + 1, d - 4,
d - 3`, the product with `H^2(O_A)` lands in `Ext` degree `6`, and the signs
are `sigma_1 = sigma_3 = -sigma_2`, `prod zeta = sigma_2`; the thresholds of the
theorem follow from `r = 57` and the dimension `(t_2 - t_1)^6` of the
target. -/
theorem conv_esix_thresholds :
    (((List.range 21).all fun i =>
      let d : Int := Int.ofNat i - 10;
      let d2 := d;
      let d3 := d + 1;
      let dL := d - 4;
      let d1 := d - 3;
      (0 - d2 + d3 == 1) && (6 - d3 + dL == 1) && (0 - dL + d1 == 1)
        && (3 + d2 - d1 == 6) && ((d3 - d2) % 2 == 1) && ((d1 - d2) % 2 == 1)
        && ((dL - d2) % 2 == 0))
    && (7 * 3 ^ 2 - 2 * 3 == 57) && (7 * 4 ^ 2 - 2 * 4 == 104) && (7 * 2 ^ 2 - 2 * 2 == 24)
    && (1 ^ 6 == 1) && (2 ^ 6 == 64) && (3 ^ 6 == 729)
    && (249 - 1 == 248) && (249 - 64 == 185) && (185 > 57) && (249 - 57 == 192)
    && (525 - 57 == 468) && (131 * 28 == 3668) && (11 * 6 == 66)
    && ((List.range 20).all fun g => ((g + 1) ^ 6 ≥ 192) == (g + 1 ≥ 3))) = true := by
  decide

/-! ## 42.  The fourfold products, an explicit convolution, and the classes
no product removes

Three finite facts behind Proposition (The fourfold products remove the
classes), Proposition (An explicit convolution), Lemma (Pieces that differ
everywhere) and Theorem (No convolution of these pieces meets the criterion).

(a) Partners.  With `zeta_j = i^(e_j)`, the pieces with `prod zeta = 1`
are the exponent vectors with sum `0` modulo `4`, and those with
`prod zeta = -1` the ones with sum `2` modulo `4`.  On `B_j` the difference of the forms of two pieces has
eigenvalues `+-|zeta_j - zeta'_j|`, and `|zeta_j - zeta'_j|^2` is `2` when
the exponents differ by `1` or `3` and `4` when they differ by `2`.  Every
piece has `3`, `6` and `7` partners of the other parity differing in `1`,
`2` and `3` coordinates; for the `7`, `D = prod_j |zeta_j - zeta'_j|^2` is
`16` six times and `64` once, `160` in all, and over the sixteen pieces of
one parity the `112` such pairs carry `2560` classes.

(b) The shifts of the lemma.  Relative to the shift `r = 0` of the pieces on
the paths, the multiples have the shifts `1, 4, 5` (all above `p`), or
`-1, 3, 4` and `-1, 1, 4` (the first below `p`).  A step from a multiple
above `p` to a piece lowers the shift by `5` and a step from a piece to it
raises it by `1`; for a multiple below `p` it is the other way round.  A step
between two multiples raises the shift by `1` going up in `t` and lowers it
by `5` going down.  The theorem computes `mu_i, nu_i` (the shifts of a piece
one step from or to `M_i`), `lambda_i` and `kappa_i` (the largest and least
shifts of pieces reached from, or reaching, `M_i` through steps between the
multiples), and checks `lambda_i <= 0 <= kappa_k`, `kappa_i >= lambda_i + 2`,
`lambda_i <= mu_i + 2` and `nu_i <= kappa_i + 2` in all three placements.

(c) The counts.  The kernels `35 - 24 = 11` and `35 - 16 = 19` of the
multiplications by `x_1` and `x_3` on a surface at `t = (2, 5, 6)`; the
degrees of the covers, four times the dimensions of the invariant sections;
the dimensions `729 = 3^6`, `16 * 24^3 = 221184` and `4^6 = 4096`; and the
bounds `249 - (45 + 15 * 9) = 69 > 57`, `16 * 12 = 192 > 57` and
`7 - (16 - 10) = 1`.
-/

/-- `|zeta_j - zeta'_j|^2` for exponents `a, b`. -/
def ffGap (a b : Nat) : Nat :=
  let d := (a + 4 - b) % 4
  if d == 0 then 0 else if d == 2 then 4 else 2

/-- the number of coordinates where two exponent vectors differ. -/
def ffDiff (z w : List Nat) : Nat :=
  ((z.zip w).filter (fun q => q.1 != q.2)).length

def ffD (z w : List Nat) : Nat := (z.zip w).foldl (fun a q => a * ffGap q.1 q.2) 1

def ffEven : List (List Nat) := (cvTuples 3).filter (fun z => cvSum z % 4 == 0)
def ffOdd : List (List Nat) := (cvTuples 3).filter (fun z => cvSum z % 4 == 2)

/-- **Partners.**  Each piece has `3, 6, 7` partners of the other parity
differing in `1, 2, 3` coordinates; the `7` have `D = 16, 16, 16, 16, 16, 16,
64`, adding up to `160`; the `112` pairs carry `2560` classes. -/
theorem ff_partner_counts :
    (ffEven.length == 16 && ffOdd.length == 16
      && ([ffEven, ffOdd].all fun P => P.all fun z =>
            let Q := if cvSum z % 4 == 0 then ffOdd else ffEven;
            ((Q.filter (fun w => ffDiff z w == 1)).length == 3)
            && ((Q.filter (fun w => ffDiff z w == 2)).length == 6)
            && ((Q.filter (fun w => ffDiff z w == 3)).length == 7)
            && (((Q.filter (fun w => ffDiff z w == 3)).map (ffD z)).foldl (· + ·) 0 == 160)
            && ((Q.filter (fun w => ffDiff z w == 3)).all fun w => ffD z w == 16 || ffD z w == 64)
            && (((Q.filter (fun w => ffDiff z w == 3)).filter (fun w => ffD z w == 64)).length == 1))
      && (((ffEven.flatMap fun z => ffOdd.filter (fun w => ffDiff z w == 3)).length) == 112)
      && ((ffEven.flatMap fun z => (ffOdd.filter (fun w => ffDiff z w == 3)).map (ffD z)).foldl (· + ·) 0
            == 2560)) = true := by
  decide +kernel

/-- a multiple: its value `t`, its shift, and whether `t > p = 0`. -/
structure ffM where
  t : Int
  d : Int
  above : Bool
deriving DecidableEq

/-- the shift of a piece one step from `M`, and one step to `M`. -/
def ffMu (m : ffM) : Int := if m.above then m.d - 5 else m.d + 1
def ffNu (m : ffM) : Int := if m.above then m.d - 1 else m.d + 5

/-- a step between two multiples is possible in degree. -/
def ffStep (a b : ffM) : Bool :=
  a != b && (if b.t > a.t then b.d == a.d + 1 else b.d == a.d - 5)

/-- the multiples reachable from `a` in at most two steps (`a` included). -/
def ffFrom (L : List ffM) (a : ffM) : List ffM :=
  a :: (L.filter (ffStep a)) ++ (L.filter (ffStep a)).flatMap (fun b => L.filter (ffStep b))

def ffLambda (L : List ffM) (a : ffM) : Int :=
  ((ffFrom L a).map ffMu).foldl max (ffMu a)
def ffKappa (L : List ffM) (a : ffM) : Int :=
  ((L.filter (fun b => (ffFrom L b).contains a)).map ffNu).foldl min (ffNu a)

def ffPlacements : List (List ffM) :=
  [ [⟨2, 1, true⟩, ⟨5, 4, true⟩, ⟨6, 5, true⟩],
    [⟨-2, -1, false⟩, ⟨2, 3, true⟩, ⟨4, 4, true⟩],
    [⟨-2, -1, false⟩, ⟨2, 1, true⟩, ⟨4, 4, true⟩] ]

/-- **The shifts of the lemma.**  In the three placements:
`lambda_i <= 0 <= kappa_k`, `kappa_i >= lambda_i + 2`, `lambda_i <= mu_i + 2`,
`nu_i <= kappa_i + 2`, and the values are those of the table in the proof. -/
theorem ff_shift_table :
    ((ffPlacements.all fun L =>
      (L.all fun a => decide (ffLambda L a ≤ 0) && decide (0 ≤ ffKappa L a)
          && decide (ffKappa L a ≥ ffLambda L a + 2)
          && decide (ffLambda L a ≤ ffMu a + 2) && decide (ffNu a ≤ ffKappa L a + 2)))
    && (ffPlacements.map fun L => L.map fun a => (ffMu a, ffNu a, ffLambda L a, ffKappa L a))
        == [ [(-4, 0, -4, 0), (-1, 3, 0, 3), (0, 4, 0, 3)],
             [(0, 4, 0, 2), (-2, 2, 0, 2), (-1, 3, 0, 2)],
             [(0, 4, 0, 3), (-4, 0, -4, 0), (-1, 3, 0, 3)] ]) = true := by
  decide +kernel

/-- **The counts.**  Kernels, cover degrees, targets and the final bounds. -/
theorem ff_noconvolution_counts :
    ((35 - 24 == 11) && (35 - 16 == 19)
    && (10 * 14 == 4 * 35) && (8 * 12 == 4 * 24) && (2 * 6 == 4 * 3)
    && (6 * 6 == 4 * 9) && (2 * 2 == 4 * 1)
    && (3 ^ 6 == 729) && (16 * 24 ^ 3 == 221184) && (4 ^ 6 == 4096)
    && (16 * 12 == 192) && (249 - 57 == 192)
    && (249 - (45 + 15 * 9) == 69) && (69 > 57) && (16 * 12 > 57)
    && (7 - (16 - 10) == 1) && (16 * 160 == 2560)) = true := by
  decide

/-! ## 43.  Two shifts on `E_0^8`, and diagonal complete intersections of
Vandermonde type

Four finite facts behind Lemma (Shifts along chains at `n = 4`), Theorem
(Two shifts on `E_0^8`), Theorem (Diagonal complete intersections of
Vandermonde type) and Corollary (Two diagonal hypersurfaces).

(a) Partners at `n = 4`.  The `128` pieces are the exponent vectors in
`(Z/4)^4` of even sum, `64` of each parity.  Each has `4, 12, 28, 20`
partners of the other parity differing in `1, 2, 3, 4` coordinates.  Two
pieces differing in one coordinate differ there by `2`, so `zeta'_j/zeta_j =
-1`.  For the `28`, `D = prod |zeta_j - zeta'_j|^2` is `16` twenty-four times
and `64` four times, `640` in all; `64 * 640 = 40960` and the rank of the
polarised criterion is `7 * 16 - 2 * 4 = 104`.

(b) Runs through the multiples.  Only the order of the four values `p, t_1,
t_2, t_3` matters, so they are the ranks `0, 1, 2, 3` with `p` at rank `r`.
A step up raises the shift by `1`, a step down lowers it by `7`
(`Ext` degrees `0` and `8`).  A run goes from `p` through a selection `A` of
distinct multiples and a selection `B` of distinct multiples back to `p`;
the marked step between them is either a component (`A` and `B` not ending
and starting at the same multiple) or a class of `H^1(a, a)` at the common
multiple, which keeps the shift.  Every run lowers the shift by at least `4`.

(c) The degrees of the two-shift theorem.  A chain `c -> ... -> W` through
distinct multiples and a chain `V -> ... -> e` through distinct multiples,
not both empty, give a term of `Ext` degree `4 - U + 7D`.  It is never `3`
when `c = e`, never `0` when `e` is above `c` and never `8` when `e` is below
`c`, the degrees of the group from `c` to `e`.

(d) Vandermonde arithmetic.  The genus of the generalised Fermat curve by
Riemann-Hurwitz and by adjunction, `d = 2..7`, `N = 2..8`; the order
`r! d^(N(r-1))` of `G` at the five cases of the computation; the units of
`Z/d` for `d = 2, 3, 4, 6`, so `|[a]| <= 2`; and the balanced orbits with
six nonzero coordinates in `P^6`: `70`, `490`, `6125` for `d = 3, 4, 6`.
-/

def efPieces : List (List Nat) := (cvTuples 4).filter (fun z => cvSum z % 2 == 0)
def efEven : List (List Nat) := efPieces.filter (fun z => cvSum z % 4 == 0)
def efOdd : List (List Nat) := efPieces.filter (fun z => cvSum z % 4 == 2)

/-- `D = prod |zeta_j - zeta'_j|^2` over the coordinates where they differ. -/
def efD (z w : List Nat) : Nat :=
  ((z.zip w).filter (fun q => q.1 != q.2)).foldl (fun a q => a * ffGap q.1 q.2) 1

/-- **Partners at `n = 4`.** -/
theorem efour_partner_counts :
    (efPieces.length == 128 && efEven.length == 64 && efOdd.length == 64
      && ([efEven, efOdd].all fun P => P.all fun z =>
            let Q := if cvSum z % 4 == 0 then efOdd else efEven;
            let T := Q.filter (fun w => ffDiff z w == 3);
            ((Q.filter (fun w => ffDiff z w == 1)).length == 4)
            && ((Q.filter (fun w => ffDiff z w == 1)).all fun w => efD z w == 4)
            && ((Q.filter (fun w => ffDiff z w == 2)).length == 12)
            && (T.length == 28)
            && ((Q.filter (fun w => ffDiff z w == 4)).length == 20)
            && ((T.map (efD z)).foldl (· + ·) 0 == 640)
            && ((T.filter (fun w => efD z w == 16)).length == 24)
            && ((T.filter (fun w => efD z w == 64)).length == 4))
      && (64 * 640 == 40960) && (7 * 16 - 2 * 4 == 104) && (40960 > 104)) = true := by
  decide +kernel

/-- the change of the shift along a step between values of ranks `a, b`. -/
def efStep (a b : Nat) : Int := if a < b then 1 else -7

def efWalk (vals : List Nat) : Int :=
  ((vals.zip vals.tail).map (fun q => efStep q.1 q.2)).foldl (· + ·) 0

/-- the change of the shift along a run with selections `A`, `B`. -/
def efRunMarkedComponent (r : Nat) (A B : List Nat) : Int := efWalk ([r] ++ A ++ B ++ [r])
def efRunMarkedDiagonal (r : Nat) (A B : List Nat) : Int := efWalk ([r] ++ A ++ B.tail ++ [r])

/-- **Runs through the multiples drop the shift by at least four.** -/
theorem efour_run_drop :
    ((List.range 4).all fun r =>
      let ms := (List.range 4).filter (· != r);
      let sel := [0, 1, 2, 3].flatMap (cvSelections ms);
      sel.all fun A => sel.all fun B =>
        (((A.length + B.length == 0) || (A.getLast? == B.head? && A.length > 0))
          || decide (efRunMarkedComponent r A B ≤ -4))
        && ((A.length == 0 || B.length == 0 || A.getLast? != B.head?)
          || decide (efRunMarkedDiagonal r A B ≤ -4))) = true := by
  decide +kernel

/-- the `Ext` degree `4 - U + 7D` of a term through the chains `A -> W` and
`V -> B`, the values of `W` and `V` being the rank `r` of `p`. -/
def efTermDegree (r : Nat) (A B : List Nat) : Int :=
  4 - efWalk (A ++ [r]) - efWalk ([r] ++ B)

/-- **The degrees of the two-shift theorem.** -/
theorem efour_two_level_degrees :
    ((List.range 4).all fun r =>
      let ms := (List.range 4).filter (· != r);
      let sel := [0, 1, 2, 3].flatMap (cvSelections ms);
      sel.all fun A => sel.all fun B =>
        (A.length + B.length == 0) ||
        (let c := A.headD r; let e := B.getLastD r; let q := efTermDegree r A B;
         if c == e then q != 3 else if c < e then q != 0 else q != 8)) = true := by
  decide +kernel

/-- the `k`-tuples with entries in `1, ..., d - 1`. -/
def vdTuples (d : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (vdTuples d k).flatMap (fun t => ((List.range (d - 1)).map (· + 1)).map (· :: t))

/-- the balanced characters with six nonzero coordinates and a fixed zero:
entries summing to `3d`, of order at least three. -/
def vdBalanced (d : Nat) : Nat :=
  ((vdTuples d 6).filter (fun t => cvSum t == 3 * d
      && d / (t.foldl Nat.gcd d) ≥ 3)).length

def vdFact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * vdFact k

def vdGenusRH (d N : Nat) : Int :=
  (-2 * (Int.ofNat d) ^ N + Int.ofNat (N + 1) * (Int.ofNat d) ^ (N - 1) * (Int.ofNat d - 1))
def vdGenusAdj (d N : Nat) : Int :=
  (Int.ofNat d) ^ (N - 1) * (Int.ofNat (N - 1) * Int.ofNat d - Int.ofNat N - 1)

/-- **Vandermonde arithmetic.** -/
theorem vandermonde_counts :
    (([2, 3, 4, 5, 6, 7].all fun d => [2, 3, 4, 5, 6, 7, 8].all fun N =>
        vdGenusRH d N == vdGenusAdj d N)
      && ([(2, 3, 2, 16), (2, 4, 2, 32), (3, 3, 2, 54), (2, 4, 3, 1536), (3, 4, 2, 162)].all
            fun (d, N, r, f) => vdFact r * d ^ (N * (r - 1)) == f)
      && ([2, 3, 4, 6].map fun d => ((List.range d).filter (fun u => Nat.gcd u d == 1)).length)
            == [1, 2, 2, 2]
      && ([3, 4, 6].map vdBalanced == [20, 140, 1750])
      && ([3, 4, 6].map fun d => 7 * vdBalanced d / 2) == [70, 490, 6125]
      && ([70, 490, 6125].map fun k => 1 + 2 * k) == [141, 981, 12251]) = true := by
  decide +kernel

/-! ## 44.  Very general diagonal complete intersections

Four finite facts behind Theorem (Very general diagonal complete
intersections).

(a) The chain of vanishing cycles.  The intersection matrix of a chain of
`m` curves, `0` on the diagonal, `1` above it and `-1` below it, has
determinant `1` for `m` even and `0` for `m` odd (`m = 1..7`): `2g` cycles
of the chain form a basis of `H_1` of a hyperelliptic curve of genus `g`.

(b) Quadrics.  The number `1 + sum_{j > r/2} C(N+1, 2j)` of Hodge classes of
degree `r` on the very general member equals one plus the number of subsets
of `{0, ..., N}` of even size at least `r + 2` (`N <= 9`); it is `N + 2` for
two quadrics in `P^N`, `N` even, and `2` for a quadric of even dimension.

(c) Cubics.  The number `1 + C(N+1, r+2) C(r+2, r/2+1)` equals one plus the
number of vectors in `{0,1,2}^(N+1)` with exactly `r + 2` nonzero entries,
`r/2 + 1` of them equal to `1`, and sum divisible by `3` (`N <= 7`,
`r = 2, 4`); it is `7, 21, 71` for the Fermat cubics of dimension `2, 4, 6`,
`141` for two cubics in `P^6` and `631` for two cubics in `P^8`.

(d) Signatures of triple covers.  With `n_1, n_2` branch points of exponent
`1, 2` and `n_1 + 2 n_2` divisible by `3`, the eigenspace has signature
`p = (2 n_1 + n_2)/3 - 1`, `q = (n_1 + 2 n_2)/3 - 1`, and then
`n_1 = 2p - q + 1`, `n_2 = 2q - p + 1`, the branch data of Achter and Pries;
it is balanced exactly when `n_1 = n_2`.
-/

/-- the intersection matrix of a chain of `m` vanishing cycles. -/
def vgChain (m : Nat) : List (List Int) :=
  (List.range m).map fun i => (List.range m).map fun j =>
    if j == i + 1 then 1 else if i == j + 1 then -1 else 0

/-- **The chain of vanishing cycles.** -/
theorem vg_chain_determinants :
    ((List.range 7).map fun k => detF (k + 1) (vgChain (k + 1)))
      == [0, 1, 0, 1, 0, 1, 0] := by
  decide +kernel

def vgQuadric (N r : Nat) : Nat :=
  1 + ((List.range (N + 2)).filter fun j => j > r / 2 && 2 * j ≤ N + 1).foldl
        (fun acc j => acc + choose (N + 1) (2 * j)) 0

def vgSubsets (N r : Nat) : Nat :=
  ((List.range (2 ^ (N + 1))).filter fun mask =>
    let s := ((List.range (N + 1)).filter fun i => (mask >>> i) % 2 == 1).length
    s % 2 == 0 && s ≥ r + 2).length

/-- **Hodge classes of very general intersections of quadrics.** -/
theorem vg_quadric_counts :
    (((List.range 7).all fun k => let N := k + 3;
        [2, 4, 6].all fun r => r + 1 > N || vgQuadric N r == 1 + vgSubsets N r)
      && ((List.range 7).all fun k => let N := 2 * k + 4; vgQuadric N (N - 2) == N + 2)
      && ((List.range 7).all fun k => let N := 2 * k + 3; vgQuadric N (N - 1) == 2)
      && (([5, 6, 7, 8, 9].map fun N => vgQuadric N 4) == [2, 8, 30, 94, 257])) = true := by
  decide +kernel

def vgCubic (N r : Nat) : Nat :=
  1 + choose (N + 1) (r + 2) * choose (r + 2) (r / 2 + 1)

/-- all lists of length `n` with entries `0, 1, 2`. -/
def vgTernary : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (vgTernary n).flatMap (fun t => [0, 1, 2].map (· :: t))

def vgBalanced (N r : Nat) : Nat :=
  ((vgTernary (N + 1)).filter fun t =>
    (t.filter (· != 0)).length == r + 2
      && (t.filter (· == 1)).length == r / 2 + 1
      && cvSum t % 3 == 0).length

/-- **Hodge classes of very general intersections of cubics.** -/
theorem vg_cubic_counts :
    (((List.range 5).all fun k => let N := k + 3;
        [2, 4].all fun r => r + 1 > N || vgCubic N r == 1 + vgBalanced N r)
      && (([2, 4, 6].map fun r => vgCubic (r + 1) r) == [7, 21, 71])
      && (vgCubic 6 4 == 141) && (vgCubic 8 6 == 631)) = true := by
  decide +kernel

/-- **Signatures of triple covers.** -/
theorem vg_triple_signatures :
    ((List.range 20).all fun n1 => (List.range 20).all fun n2 =>
      ((n1 + 2 * n2) % 3 != 0 || n1 + n2 < 3) ||
        (let p := (2 * n1 + n2) / 3 - 1; let q := (n1 + 2 * n2) / 3 - 1;
         3 * (p + 1) == 2 * n1 + n2 && 3 * (q + 1) == n1 + 2 * n2
           && n1 + q == 2 * p + 1 && n2 + p == 2 * q + 1
           && (p == q) == (n1 == n2))) = true := by
  decide +kernel

/-! ## 45.  Monodromy of cyclic covers of degree 3, 4 and 6

Five finite facts behind Proposition (Monodromy of cyclic covers), Lemma (The
discriminant of the new part) and Theorem (Very general diagonal complete
intersections), for degree `m ∈ {3, 4, 6}`.  A multiset of nonzero residues
modulo `m` is a count vector `c`, `c_v` the number of entries equal to `v`;
it has `k = sum c_v` points, sum `sum v c_v`, and `m (p + 1) = sum (m - v) c_v`,
`m (q + 1) = sum v c_v`.

(a) The base of the induction.  The vectors with `k = 5, 6` points, sum `0`,
order `m` and `p, q ≥ 1` are `38` up to sign.

(b) The merge lemma, proved by hand in the paper, for `7 ≤ k ≤ 8, 11, 10`
points at `m = 3, 4, 6`: every such vector has two entries `u, w` with
`u + w ≠ 0` whose merge keeps the order `m` and `p, q ≥ 1`.

(c) Norms.  `x^2 + xy + y^2` is never `2` modulo `4`, and is even only when
`x` and `y` are, so `2` is not a norm from `Q(sqrt(-3))` and every norm has
even `2`-adic valuation; `2 = 1 + 1` is a norm from `Q(i)`, and
`3 = 1 + 1 + 1`, `4 = 4` are norms from `Q(sqrt(-3))`.

(d) Counts.  `T_d(k)`, the number of `(s_i) ∈ {1, ..., d-1}^k` with
`sum s_i = dk/2`, computed by a recursion and checked against enumeration
for `(d, k) = (3, 6), (4, 6), (6, 4)`; `T_4(6) = 141`, `T_6(6) = 1751`,
`T_4(8) = 1107`, `T_6(8) = 38165`; the formula of the theorem agrees with a
direct count of the characters for `(d, N, r) = (4, 5, 4), (3, 6, 4),
(6, 4, 2)`, and gives `142`, `988`, `3950`, `1108`, `1752`, `12258`,
`38166`.

(e) A non-split sixfold.  `a = (1, 1, 2, 2, 3, 5, 5, 5)` modulo `6` has sum
`0`, order `6`, `p = q = 3` and one coordinate equal to `3`.
-/

/-- the residues `1, ..., m - 1` present in a count vector `c`. -/
def cyPresent (c : List Nat) : List Nat :=
  ((List.range c.length).filter fun i => c.getD i 0 > 0).map (· + 1)

/-- the order of a count vector modulo `m`. -/
def cyOrder (m : Nat) (c : List Nat) : Nat :=
  m / ((cyPresent c).foldl Nat.gcd m)

def cyK (c : List Nat) : Nat := cvSum c

def cySum (c : List Nat) : Nat :=
  ((List.range c.length).map fun i => (i + 1) * c.getD i 0).foldl (· + ·) 0

/-- `m (p + 1)` and `m (q + 1)`. -/
def cyP1 (m : Nat) (c : List Nat) : Nat :=
  ((List.range c.length).map fun i => (m - (i + 1)) * c.getD i 0).foldl (· + ·) 0

def cyQ1 (c : List Nat) : Nat := cySum c

/-- admissible: sum `0`, order `m`, `p, q ≥ 1`. -/
def cyAdm (m : Nat) (c : List Nat) : Bool :=
  cySum c % m == 0 && cyOrder m c == m && cyP1 m c ≥ 2 * m && cyQ1 c ≥ 2 * m

/-- all count vectors of length `l` with total `k`. -/
def cyVectors : Nat → Nat → List (List Nat)
  | 0, k => if k == 0 then [[]] else []
  | l + 1, k => (List.range (k + 1)).flatMap fun j => (cyVectors l (k - j)).map (j :: ·)

/-- the negative of a count vector: `v ↦ m - v`. -/
def cyNeg (c : List Nat) : List Nat := c.reverse

/-- one representative of each pair `{a, -a}`: the lexicographically larger. -/
def cyRep (c : List Nat) : Bool := decide (cyNeg c ≤ c)

/-- the count vector after merging one entry `u` and one entry `w`. -/
def cyMerge (m : Nat) (c : List Nat) (u w : Nat) : List Nat :=
  let c1 := c.set (u - 1) (c.getD (u - 1) 0 - 1)
  let c2 := c1.set (w - 1) (c1.getD (w - 1) 0 - 1)
  let v := (u + w) % m
  c2.set (v - 1) (c2.getD (v - 1) 0 + 1)

/-- `f` holds at every count vector of length `l` and total `k`, extending `acc`. -/
def cyAll : Nat → Nat → List Nat → (List Nat → Bool) → Bool
  | 0, k, acc, f => k != 0 || f acc.reverse
  | l + 1, k, acc, f => (List.range (k + 1)).all fun j => cyAll l (k - j) (j :: acc) f

def cyHasMerge (m : Nat) (c : List Nat) : Bool :=
  (List.range (m - 1)).any fun i => (List.range (m - 1)).any fun j =>
    let u := i + 1; let w := j + 1
    u ≤ w && (u + w) % m != 0 && c.getD i 0 ≥ 1
      && (if u == w then c.getD i 0 ≥ 2 else c.getD j 0 ≥ 1)
      && cyAdm m (cyMerge m c u w)

/-- **The base of the induction.** -/
theorem cyclic_base_count :
    ([3, 4, 6].foldl (fun acc m => acc + ([5, 6].foldl (fun acc' k =>
        acc' + ((cyVectors (m - 1) k).filter fun c =>
          cyAdm m c && cyRep c).length) 0)) 0) == 38 := by
  decide +kernel

/-- **The merge lemma for few points.** -/
theorem cyclic_merge_small :
    ([3, 4, 6].all fun m => (List.range (if m == 6 then 4 else 3 * m - 7)).all fun i =>
      cyAll (m - 1) (i + 7) [] fun c => !cyAdm m c || cyHasMerge m c) = true := by
  decide +kernel

/-- **Norms from `Q(i)` and `Q(sqrt(-3))`.** -/
theorem cyclic_norms :
    ((List.range 4).all fun x => (List.range 4).all fun y =>
        (x * x + x * y + y * y) % 4 != 2)
      && ((List.range 2).all fun x => (List.range 2).all fun y =>
        (x * x + x * y + y * y) % 2 != 0 || (x == 0 && y == 0))
      && (1 * 1 + 1 * 1 == 2) && (1 * 1 + 1 * 1 + 1 * 1 == 3)
      && (2 * 2 + 2 * 0 + 0 * 0 == 4) = true := by
  decide +kernel

/-- the polynomial `(x + ... + x^(d-1))^k`, as its list of coefficients. -/
def cyPow (d : Nat) : Nat → List Nat
  | 0 => [1]
  | k + 1 =>
    let f := cyPow d k
    (List.range (f.length + d - 1)).map fun e =>
      (List.range (d - 1)).foldl (fun acc j =>
        let s := j + 1; if s ≤ e then acc + f.getD (e - s) 0 else acc) 0

def cyT (d k : Nat) : Nat := (cyPow d k).getD (d * k / 2) 0

/-- all lists of length `n` with entries in `0, ..., d - 1`. -/
def cyTuples (d : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (cyTuples d n).flatMap fun t => (List.range d).map (· :: t)

def cyTEnum (d k : Nat) : Nat :=
  ((cyTuples (d - 1) k).filter fun t => 2 * (cvSum t + k) == d * k).length

/-- the formula of the theorem. -/
def cyFormula (d N r : Nat) : Nat :=
  1 + choose (N + 1) (r + 2) * cyT d (r + 2)
    + (if d % 2 == 0 then
        ((List.range (N + 2)).filter fun j => j ≥ r / 2 + 2 && 2 * j ≤ N + 1).foldl
          (fun acc j => acc + choose (N + 1) (2 * j)) 0
      else 0)

/-- the direct count of the characters that carry a Hodge class. -/
def cyEnum (d N r : Nat) : Nat :=
  1 + ((cyTuples d (N + 1)).filter fun a =>
    let s := a.filter (· != 0)
    let o := d / (s.foldl Nat.gcd d)
    cvSum a % d == 0 && s.length > 0 &&
      (if o == 2 then s.length ≥ r + 2
       else s.length == r + 2 && cvSum (s.map (d - ·)) == d * (r / 2 + 1))).length

/-- **Counts of Hodge classes.** -/
theorem cyclic_vg_counts :
    (cyT 3 6 == cyTEnum 3 6 && cyT 4 6 == cyTEnum 4 6 && cyT 6 4 == cyTEnum 6 4
      && ([cyT 4 6, cyT 6 6, cyT 4 8, cyT 6 8] == [141, 1751, 1107, 38165])
      && cyFormula 4 5 4 == cyEnum 4 5 4 && cyFormula 3 6 4 == cyEnum 3 6 4
      && cyFormula 6 4 2 == cyEnum 6 4 2
      && ([cyFormula 4 5 4, cyFormula 4 6 4, cyFormula 4 7 4, cyFormula 4 7 6,
           cyFormula 6 5 4, cyFormula 6 6 4, cyFormula 6 7 6]
          == [142, 988, 3950, 1108, 1752, 12258, 38166])) = true := by
  decide +kernel

/-- **A non-split sixfold.** -/
theorem cyclic_nonsplit_example :
    (let c := [2, 2, 1, 0, 3]
     cyAdm 6 c && cyK c == 8 && cyP1 6 c == 24 && cyQ1 c == 24 && c.getD 2 0 == 1)
      = true := by
  decide +kernel

end HodgeObstruction

/-! ## The axioms each theorem depends on

Each theorem must report `depends on axioms: []`, or `[propext]` where
propositional extensionality enters through `decide`, and in no case
`sorryAx`.
-/

#print axioms HodgeObstruction.qnorm_mul_check
#print axioms HodgeObstruction.qmul_conj
#print axioms HodgeObstruction.characters_differ
#print axioms HodgeObstruction.characters_differ'
#print axioms HodgeObstruction.bad_witness
#print axioms HodgeObstruction.bad_witness_exceptions
#print axioms HodgeObstruction.ratio_not_root_of_unity
#print axioms HodgeObstruction.sign_uniform_and_closed
#print axioms HodgeObstruction.subsets_count
#print axioms HodgeObstruction.semiregularity_target
#print axioms HodgeObstruction.secant_count_below_thresholds
#print axioms HodgeObstruction.thresholds_not_necessary
#print axioms HodgeObstruction.grading_positions_differ
#print axioms HodgeObstruction.weil_delta_parity
#print axioms HodgeObstruction.weil_delta_closed_even
#print axioms HodgeObstruction.weil_delta_closed_odd
#print axioms HodgeObstruction.weil_term_counts
#print axioms HodgeObstruction.supports_disjoint
#print axioms HodgeObstruction.hodge_dim_count
#print axioms HodgeObstruction.weil_line_hodge_type
#print axioms HodgeObstruction.clifford_dimensions
#print axioms HodgeObstruction.k3_type_only_at_one
#print axioms HodgeObstruction.moduli_codimension
#print axioms HodgeObstruction.discriminant_is_a_norm
#print axioms HodgeObstruction.split_codimension
#print axioms HodgeObstruction.quat_class_odd
#print axioms HodgeObstruction.quat_class_even
#print axioms HodgeObstruction.quat_product_class
#print axioms HodgeObstruction.quat_locus_codimension
#print axioms HodgeObstruction.quat_locus_divisor_at_two
#print axioms HodgeObstruction.irrational_witness_exists
#print axioms HodgeObstruction.weil_line_spanned
#print axioms HodgeObstruction.norm_form_positive
#print axioms HodgeObstruction.norm_sum_forces_zero
#print axioms HodgeObstruction.semiregularity_source_target
#print axioms HodgeObstruction.tensor_rank_gap
#print axioms HodgeObstruction.secant_witness_at_n_four
#print axioms HodgeObstruction.secant_witness_rank
#print axioms HodgeObstruction.vandermonde_nodes_distinct
#print axioms HodgeObstruction.level_sums_forced
#print axioms HodgeObstruction.level_sums_totals
#print axioms HodgeObstruction.level_matrix_nonsingular
#print axioms HodgeObstruction.gauss_norm_counts
#print axioms HodgeObstruction.norm_supply_blocks_small_case
#print axioms HodgeObstruction.pencil_index_d1
#print axioms HodgeObstruction.pencil_index_d3
#print axioms HodgeObstruction.pencil_beta_positive
#print axioms HodgeObstruction.pencil_square_members
#print axioms HodgeObstruction.split_obstruction_rank
#print axioms HodgeObstruction.split_obstruction_count
#print axioms HodgeObstruction.evaluation_not_surjective
#print axioms HodgeObstruction.markman_candidate_identities
#print axioms HodgeObstruction.secant_kernel_arithmetic
#print axioms HodgeObstruction.candidate_unnormalised_points
#print axioms HodgeObstruction.smooth_invariants
#print axioms HodgeObstruction.smooth_bmy_defect
#print axioms HodgeObstruction.smooth_bmy_is_d_le_bsq
#print axioms HodgeObstruction.smooth_index_vacuous
#print axioms HodgeObstruction.smooth_four_discriminants
#print axioms HodgeObstruction.smooth_table
#print axioms HodgeObstruction.burch_weight_identities
#print axioms HodgeObstruction.burch_rank_one_discriminant
#print axioms HodgeObstruction.burch_rank_four_witness
#print axioms HodgeObstruction.closure_omits_conjecture
#print axioms HodgeObstruction.frontier_suffices
#print axioms HodgeObstruction.frontier_minimal
#print axioms HodgeObstruction.frontier_smallest
#print axioms HodgeObstruction.variational_gives_abelian
#print axioms HodgeObstruction.lefschetz_gives_abelian
#print axioms HodgeObstruction.secant_route_descends
#print axioms HodgeObstruction.propagation_closes
#print axioms HodgeObstruction.p2_minimal_count
#print axioms HodgeObstruction.weil_monomials_separated
#print axioms HodgeObstruction.mumford_invariants
#print axioms HodgeObstruction.two_branch_annihilator
#print axioms HodgeObstruction.mumford_rigidity_sos
#print axioms HodgeObstruction.mumford_ext_profile
#print axioms HodgeObstruction.lefschetz_counts
#print axioms HodgeObstruction.criterion_endomorphisms_n2
#print axioms HodgeObstruction.criterion_endomorphisms_n3
#print axioms HodgeObstruction.quartic_squares_mod4_phi
#print axioms HodgeObstruction.quartic_no_square_phi
#print axioms HodgeObstruction.quartic_squares_mod4_sqrt2
#print axioms HodgeObstruction.quartic_no_square_sqrt2
#print axioms HodgeObstruction.quartic_rank_two_congruences
#print axioms HodgeObstruction.quartic_euler_minimal
#print axioms HodgeObstruction.orlov_equality_count
#print axioms HodgeObstruction.orlov_n4_euler
#print axioms HodgeObstruction.quartic_squares_mod4_mod8
#print axioms HodgeObstruction.quartic_rank_two_small_odd_parts
#print axioms HodgeObstruction.quartic_rank_two_large_odd_part
#print axioms HodgeObstruction.quartic_sqrt2_units_mod4
#print axioms HodgeObstruction.sextic_thresholds
#print axioms HodgeObstruction.cm_tetrahedra
#print axioms HodgeObstruction.cm_square_monomials
#print axioms HodgeObstruction.cm_tetrahedron_pairs
#print axioms HodgeObstruction.cm_profile_forces_equal
#print axioms HodgeObstruction.cm_pairs_three_cycle
#print axioms HodgeObstruction.cm_abelian_semiregular_count
#print axioms HodgeObstruction.quartic_rank_values
#print axioms HodgeObstruction.delsarte_loop_sextic
#print axioms HodgeObstruction.simplex_klein_quartic
#print axioms HodgeObstruction.simplex_loop_sextic
#print axioms HodgeObstruction.quartic_exceptional_pair
#print axioms HodgeObstruction.quartic_locus_counts
#print axioms HodgeObstruction.quartic_compensated_bivectors
#print axioms HodgeObstruction.quartic_rank_certificates
#print axioms HodgeObstruction.quartic_koszul_squares
#print axioms HodgeObstruction.quartic_line_two_planes
#print axioms HodgeObstruction.quartic_first_factor_character
#print axioms HodgeObstruction.conv_pure_weil_identity
#print axioms HodgeObstruction.conv_cup_kernel
#print axioms HodgeObstruction.conv_run_excess
#print axioms HodgeObstruction.conv_esix_thresholds
#print axioms HodgeObstruction.ff_partner_counts
#print axioms HodgeObstruction.ff_shift_table
#print axioms HodgeObstruction.ff_noconvolution_counts
#print axioms HodgeObstruction.efour_partner_counts
#print axioms HodgeObstruction.efour_run_drop
#print axioms HodgeObstruction.efour_two_level_degrees
#print axioms HodgeObstruction.vandermonde_counts
#print axioms HodgeObstruction.vg_chain_determinants
#print axioms HodgeObstruction.vg_quadric_counts
#print axioms HodgeObstruction.vg_cubic_counts
#print axioms HodgeObstruction.vg_triple_signatures
#print axioms HodgeObstruction.cyclic_base_count
#print axioms HodgeObstruction.cyclic_merge_small
#print axioms HodgeObstruction.cyclic_norms
#print axioms HodgeObstruction.cyclic_vg_counts
#print axioms HodgeObstruction.cyclic_nonsplit_example
