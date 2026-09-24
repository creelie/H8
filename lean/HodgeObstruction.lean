/-
HodgeObstruction.lean

A machine check, by Lean 4's kernel, of the finite arithmetic behind the
results of "Explicit Base Points and Numerical Propagation for Weil Classes on Abelian Varieties".

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

Everything is settled by `decide`, so the kernel checks it.  There is no
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
paper as data: thirty-six statements, each proved here, quoted from the
literature, or open, and fifteen inference rules, each of which is one
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
   12  P2       (every CM field)                     30  orbit_dense_cm
   13  secant_all                                    31  lef_B   (Lefschetz B)
   14  Q114                                          32  mot     (all motivated)
   15  smooth_exists                                 33  vhc     (variational)
   16  smooth_vanish                                 34  mot_def (Andre)
   17  sing_exists                                   35  acc_ab  (Deligne, Andre)

with 19 to 30, 34 and 35 proved here or quoted, 9, 10, 12 to 18 and 31 to 33
open, and the rest derived.  The consequence operator is monotone and each rule has
one conclusion, so a pass that changes the set adds a conclusion not present
before; there are fewer than thirty-two conclusions, so thirty-two passes
reach the fixed point.

The bounded criterion is absent from the rules: it is equivalent to the
conclusion it would imply, so it is a restatement and not a premise.

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
It is a consequence once the three statements 9, 10 and 12 are adjoined, and
once any of the pairs `[31, 32]`, `[31, 9]` and `[33, 9]` is adjoined; in each
of the four sets every element is necessary.  No single open statement
suffices, and among all sixty-six pairs of the twelve open statements exactly
those three pairs suffice.  Statement 33 alone gives the conjecture for
abelian varieties and not the conjecture, and statement 31 gives 33.  And the secant route, granted both of its open
demands, yields the trivial discriminant families and not the others, while
the propagation statement yields the Weil classes of every CM field.
-/

/-- the rules, as pairs of a premise list and a conclusion. -/
def hcRules : List (List Nat × Nat) :=
  [([1, 9], 0), ([2, 10], 1), ([3, 11], 2), ([4, 5], 3),
   ([12, 19, 20, 21], 4), ([12, 19, 20, 21], 5),
   ([13, 14, 20, 22, 23, 25], 4),
   ([15, 16, 24], 6), ([17, 18, 24], 6), ([6, 14, 22, 23], 7),
   ([26, 27], 8),
   ([12, 28, 29, 30], 11),
   ([31, 32], 0), ([31, 34], 33), ([33, 35], 1)]

/-- what the paper proves or quotes. -/
def hcBase : List Nat :=
  [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 34, 35]

/-- the open statements. -/
def hcOpen : List Nat := [9, 10, 12, 13, 14, 15, 16, 17, 18, 31, 32, 33]

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

/-- **Four sufficient sets.**  The route through this paper: the two
statements `9` and `10` about the classes that no Weil line reaches (the
conjecture for varieties that are not abelian, and for the Hodge classes on
abelian varieties outside the subring of divisor and Weil classes; neither is
a reduction) and the propagation statement `12`, read for every CM field.  The
routes of the literature: the Lefschetz standard conjecture `31` together
with either the motivatedness of every Hodge class `32` or the statement `9`,
and the variational statement `33` together with `9`. -/
theorem frontier_suffices :
    (hcSuff [9, 10, 12] && hcSuff [31, 32] && hcSuff [31, 9]
      && hcSuff [33, 9]) = true := by
  decide

/-- **Each element of each of the four sets is necessary.**  Dropping any one
of them leaves the conjecture underivable. -/
theorem frontier_minimal :
    (([[9, 10, 12], [31, 32], [31, 9], [33, 9]] : List (List Nat)).all
        fun t => t.all fun f => !hcSuff (t.erase f)) = true := by decide

/-- **No single statement suffices, and exactly three pairs do.**  Over the
twelve open statements, no one of them suffices, and of the sixty-six pairs
exactly `[9, 31]`, `[31, 32]` and `[9, 33]` suffice. -/
theorem frontier_smallest :
    (hcOpen.all (fun a => !hcSuff [a])
      && hcOpen.all (fun a => hcOpen.all (fun b =>
          !(a < b) || (hcSuff [a, b] ==
            ((a == 9 && b == 31) || (a == 31 && b == 32)
              || (a == 9 && b == 33)))))) = true := by
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

/-- **The secant route stops at the trivial discriminant.**  Granting both of
its open demands, `13` and `14`, puts `4` in the closure and leaves `5` and
`3` out of it. -/
theorem secant_route_stops :
    ((hcClose (hcBase ++ [13, 14]) 32).contains 4
      && !(hcClose (hcBase ++ [13, 14]) 32).contains 5
      && !(hcClose (hcBase ++ [13, 14]) 32).contains 3) = true := by decide

/-- **The propagation statement closes the imaginary quadratic case, and the
Weil classes of every CM field.** -/
theorem propagation_closes :
    ((hcClose (hcBase ++ [12]) 32).contains 3
      && (hcClose (hcBase ++ [12]) 32).contains 2) = true := by decide

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
#print axioms HodgeObstruction.secant_route_stops
#print axioms HodgeObstruction.propagation_closes
#print axioms HodgeObstruction.p2_minimal_count
#print axioms HodgeObstruction.weil_monomials_separated
#print axioms HodgeObstruction.mumford_invariants
#print axioms HodgeObstruction.two_branch_annihilator
#print axioms HodgeObstruction.mumford_rigidity_sos
#print axioms HodgeObstruction.mumford_ext_profile
#print axioms HodgeObstruction.lefschetz_counts
