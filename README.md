# Explicit Base Points and Obstructions to Propagation for Weil Classes on Abelian Varieties

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22950276.svg)](https://doi.org/10.5281/zenodo.22950276)

Verification code and figure sources for the paper *Explicit Base Points and
Obstructions to Propagation for Weil Classes on Abelian Varieties*, by Deep Bhattacharjee and Ushashi Bhattacharya.

Release v1.0.0 (https://github.com/creelie/H8/releases/tag/v1.0.0) is
archived on Zenodo under DOI 10.5281/zenodo.22950276
(https://doi.org/10.5281/zenodo.22950276); cite that DOI for the code.

Everything here is self-contained. Nothing needs a network connection, a
licence, or a package other than those named below.

## Layout

    code/       exact-arithmetic verification in Python 3 (sympy for secant_plane.py,
                weiltype_family.py, mumford_rigidity.py, mumford_object.py,
                lefschetz_closure.py, twistor_locus.py and hk_pullback.py, numpy
                integer arrays for pte_remaining.py and weil_tori.py)
    verify.ps1  the whole verification on Windows, Python suite then Lean
    lean/       a kernel-checked certificate of the finite arithmetic, Lean 4
    figures/    the generators and TikZ sources of every figure in the paper

## Running the verification

    cd code
    python3 verify_all.py

On Windows, `verify.ps1` at the top level runs the same suite and then the
Lean check:

    powershell -ExecutionPolicy Bypass -File .\verify.ps1

The last lines are

    951 checks passed, 0 failed
    overall: PASS

and the exit status is zero. The driver runs five self-contained checks and
then calls the companion scripts in the same directory:

| script | what it settles |
| --- | --- |
| `verify_all.py` | the Fourier-Mukai transform on powers of the polarisation, the permutation sign, the character grading, the secant count, the semiregularity target |
| `explicit_weil.py` | the coordinate model of Weil type and the two generators of the Weil line |
| `fm_theta.py`, `fm_sign.py` | standalone reruns of items (I) and (II): the transform on powers of the polarisation with the closed form, and the permutation sign up to g = 12; not called by the driver |
| `hodge_invariants.py` | the count of Hodge classes by invariant theory |
| `kugasatake.py` | the Clifford algebra and the reach of the Kuga-Satake construction |
| `weiltype_family.py`, `secant_plane.py` | the family of Weil type and the secant plane |
| `split_locus.py` | the split member and the closed form of its Weil line |
| `split_geometry.py` | the polarisation of the split member (with the eigenvalue check that fixes the convention for the K-action), its discriminant, codimension and divisors |
| `quaternionic.py` | quaternionic multiplication, a base point in every Weil family, and the dimension of the quaternionic locus |
| `semiregularity.py` | the semiregularity map of a sum of line bundles, the positivity obstruction, and the explicit object at n = 3 |
| `semireg_fast.py` | the same ranks modulo a prime, which reaches n = 3 |
| `weil_annihilator.py` | the annihilator of the Weil line in H^{0,2} has dimension n^2, the parity split of the semiregularity map, and the uniform kernel over the whole family |
| `lagrangian_locus.py` | the quaternionic locus as a Lagrangian Grassmannian, and that the real loci sweep the family |
| `integrality.py` | that nothing numerical forbids the object the secant construction needs: the Chern classes are integral and Bogomolov never binds |
| `rigidity.py` | infinitesimal rigidity: the polarisation is the only class that survives the family, and a norm-character class of rank r cuts codimension n.r |
| `object_size.py` | the Riemann-Roch bound on the size of any object carrying the Weil class |
| `weil_product.py` | the Weil class is multiplicative under products, and the base case in every dimension |
| `weil_tangent.py` | the annihilator is the tangent space to the Weil family, over the Gaussian rationals |
| `secant_exists.py` | that a coherent sheaf with the Chern character the secant construction needs exists in every dimension, with an explicit witness in line bundles and the least multiple M |
| `pte_search.py` | which split objects supported on R can be semiregular: the level sums, the level sets that survive them at n = 3, and the exhaustive search that removes them |
| `smooth_support.py` | the invariants a smooth support must have, read off the Chern character, and the Bogomolov-Miyaoka-Yau bound that leaves four discriminants |
| `hilbert_burch.py` | Cohen-Macaulay supports with a split resolution: the complete intersections are excluded outright, ranks two and three are empty, and the candidates at higher rank are printed |
| `closure_graph.py` | the logical skeleton of the paper and of the literature it quotes as a rule set: the conjecture is not in the closure of what is proved; the conjecture for varieties that are not abelian, (F3), gives it for every abelian variety A through A x P^1 and so is the conjecture itself; with (F3'), the conjecture modulo abelian varieties, added, there are exactly five minimal sufficient sets, {(F3)}, {Lefschetz standard conjecture B, every Hodge class motivated}, {B, (F3')}, {variational Hodge conjecture for algebraic classes, (F3')} and the route of the paper {(P2), (F2), (F3')}; (F3') alone gives nothing on abelian varieties; without the two additions the search returns the four sets of the earlier version; and the secant route lies in no minimal set |
| `hochschild_annihilator.py` | the annihilator of a Weil class in the whole exterior algebra HH^*(A) of dimension 2^{4n}: that HH^1 splits as P + Q with P and Q the annihilators of the two conjugate pieces of the class, each of dimension 2n; that the degree-two annihilator is exactly P ^ Q, of dimension 4n^2; the dimension binom(4n,k) - 2 binom(2n,k) in every degree with one extra class at k = 2n; the codimension 2^{2n+1} - 1 of the ideal generated; and the unconditional lower bound dim Ext^2(E,E) >= 2n(2n-1) |
| `p2_support.py` | the finite linear algebra of the numerical form of the semiregularity criterion and of the support theorem: the rank 2n(2n-1) of contraction into the Weil class on HH^2 and its injectivity on wedge^2 P + wedge^2 Q, the class of a point on a torus contracted with a ^ b, the dichotomy in the normal space, the eigenspace bookkeeping in an explicit rational model over Q(i), and the separation of the Weil line from the classes pulled back from quotients by abelian subvarieties tangent to an eigenspace |
| `lefschetz_family.py` | the Lefschetz standard conjecture for the total space of an abelian scheme over a curve with algebraic invariant cycles: on abelian varieties with g <= 4 the operator Lambda equals D^{-1} times the Pontryagin product with l^{g-1}/(g-1)!, computed from mu_* and mu^*; on product families the operator assembled from the relative and base parts satisfies [L, Lambda] = H; and the invariants of the Mumford group in wedge^q V are 1,0,1,0,1,0,1,0,1 |
| `targets_reduction.py` | the two remaining targets reduced to one case of the Lefschetz standard conjecture each: the invariant ring of the square of a Mumford fourfold is generated in degrees 2 and 4; at a CM point every Hodge class of X_c x X_c lies in the ring generated by divisor classes and pull-backs of Hodge classes of X_c, so the Hodge conjecture holds there; and the (p,p) classes annihilated by Q^HH^1, P^HH^1, HH^1^HH^1 are C alpha_-, C alpha_+, 0 |
| `mumford_rigidity.py` | the rigidity of the exceptional classes on the square of a Mumford fourfold: the nine weight blocks of the Siegel tangent space sp^{-1,1} (36) and the 46 blocks of HT^2 = 28 + 64 + 28 by type, weight and exchange parity; every Gram determinant of contraction into omega_a is a positive constant times a product of sums of squares, positive definite forms and linear forms with certificates; the only generic kernel is the derivation of the Mumford curve; the hyperplane a0+a1+a2+a3 = 0 is the one exception, in the bivector blocks; so the annihilator is one dimensional and the numerical criterion is dim Ext^2 = 119 |
| `mumford_object.py` | what a perfect complex with the Chern character of an exceptional class on a Mumford square must look like: the ranks of contraction into the class on HT^k are 1, 16, 119, 328, 560, 328, 119, 16, 1 (exact over Q at a sample point, and modulo a prime at a rational class for the cubic subfield of Q(zeta_7)), symmetric as the duality lemma predicts; chi(E,E) = 0 then forces at least 800 dimensions of odd self-extensions; and at a CM point the products of divisor classes span 100 of the 132 Hodge classes in degree four and miss every exceptional class |
| `lefschetz_closure.py` | what line bundles generate on a Mumford square: the Sp(V, psi)-invariants of wedge^k(V+V) are 1,3,6,10,15,10,6,3,1 and are spanned by products of the three divisor classes; the Hodge classes that are not Lefschetz number 0,0,2,6,13,6,2,0,0; at a CM point the Lefschetz group is the diagonal torus, whose invariants 1,16,100,304,454,... are products of the 16 divisor classes; omega_a is invariant under that torus only when a1 = a2 = a3; and the Sp-module generated by an exceptional class is irreducible of highest weight 2 varpi_2 and dimension 308 |
| `twistor_locus.py` | the Hodge locus of an exceptional class among all complex tori: V_R as the fixed space of the real structure that is quaternionic on the two compact factors and real on the third; psi(x, Jy) has signature (0,8) for the complex structures of the Mumford family and (4,4) for a unit quaternion j of a compact factor; the quaternion k with kj = -jk carries psi(x, Jy) to its negative, so no invariant class of degree two polarises a member of the twistor line; the annihilator of omega_a in H^1(T) (dimension 64) is one dimensional at both kinds of point, the direction of the curve and the direction of the twistor sphere; and the exchange of the first and third factors relates the two computations |
| `hk_pullback.py` | the square of a Mumford fourfold as a holomorphic symplectic variety: iota(x) = (x (x) 1) Psi embeds T = Lie G in H^1 (x) H^1; the Casimirs split H^2 (dimension 120) into pieces of dimensions 3, 27, 27, 27, 27, 3, 3, 3 with (2,0)-parts 0, 0, 9, 9, 9, 0, 0, 1, so iota(T) is the only sub-Hodge structure with h^{2,0} = 1; its (2,0)-form is symplectic; iota_2(C_1) = 3 pi_0 - pi_12 - pi_13 + 3 pi_23 and cyclically, so the exceptional classes are the twisted dual forms of iota(T); det(x_1 + x_2 + x_3) = Delta(N)^2 and iota(x)^8 = 8! det(x) vol, which with the Fujiki relation rules out hyperkaehler eightfolds |
| `mumford_routes.py` | which of the open routes to the Mumford target are needed: sixteen statements and twenty-two Horn rules, each labelled by the theorem that proves it and checked against paper_labels.txt; the target is not in the closure of what is proved; the statements equivalent to it are exactly algebraicity at uncountably many points, B(W x_C W), bounded data at infinitely many points and bounded data modulo p; every minimal set of open statements yielding it has one element, twelve in all; the complex with dim Ext^2 = 119 and the Kuga-Satake statements are stronger than it; (L) and (V) yield it; it yields neither the Hodge conjecture nor (F1), (F2), (F3); and (F3) is equivalent to the Hodge conjecture, so the target is an input to no minimal route to the conjecture |
| `criterion_shape.py` | what an object meeting the numerical criterion must look like: the rational Weil classes are primitive and the intersection form on the Weil plane is (-1)^n-definite (Gram matrices diag(8d^2, 8d) at n = 2 and diag(-32d^3, -32d^2) at n = 3), so chi(E,E) > 0 by Hodge-Riemann; the Hodge classes killed by P ^ Q are exactly the Weil line in every degree, so an indecomposable summand carries the class; the top traces c_P, c_Q are nonzero; and at n = 2, and at n = 3 granting the degree-three compatibility that the paper's corollary on the Hochschild action already grants, the Euler characteristic forces dim End(E) >= 2 + chi/2 >= 3, with the smallest admissible profiles listed, while at n = 4, 5 it does not |
| `weil_tori.py` | the Hodge classes of a very general Weil torus, the input of the theorem that no complex whose Chern character is exactly a Weil class is semiregular: the Weil classes stay of type (n,n) on the whole 2n^2-dimensional K-linear family; at explicit members off the polarised family no rational class of degree 2k, 0 < k < n, is of Hodge type and in degree 2n only the Weil plane is (checked for n = 2 with d = 1, 3 and for n = 3 with d = 2, ranks modulo a prime with both conjugate conditions imposed); and a Kaehler form in V_+ (x) V_- has zero degree against every Weil class |
| `p2prime.py` | the corrected criterion (P2') as a number: for a Chern character N omega + sum c_k theta^k the annihilator in HT^2 has dimension n^2(4 - rho), rho the rank of the Hankel matrix of the k! c_k, so dim Ext^2(E,E) >= (4 + rho) n^2 - 2n with equality forcing injective semiregularity; for a general shape the annihilator is exactly the tangent space of the polarised Weil family; the n = 2 formula with its two exceptional ratios; the first-order Hodge locus; chi(E,E); at the exceptional n = 2 ratio, the stabiliser so(4,3) of the character (dimension 21, trace-form signature (12,9), invariants 1, 0, 0, 0, 1, 0, 0, 0, 1) and the constant sign of int gamma kappa^2 on the Kaehler cone; exact over Q(i) by torus-weight blocks, to n = 4 by default and n = 9 with --extreme |
| `p2prime_profile.py` | the whole Hochschild profile of such a character: the ranks of contraction on every HT^k equal 2 binom(2n,k) + M_k min(k+1, 2n+1-k, r) - [k=n] d, their symmetry, the middle degeneracy, and the parity of chi(E,E), which makes the numerical criterion unattainable at the n = 2 points with rho_2 = 23 |
| `descent.py` | descent and scalar extension for Weil classes: the correspondence pr_{B*}(x . pr_Y^*(eta_Y^{2m-2} y')) maps the Weil classes of B x Y onto those of B, so W(F,n+1,delta'') gives W(F,n,delta) for every discriminant; and W(F,n,iota(delta)) gives W(K,n,delta) for K in F; exact over seven CM fields |
| `transport_growth.py` | the transport of the base cycle along the rational orbit: det(phi) = c^{2G}, phi^* E = c^2 E and phi^* omega = c^{2n} omega on an explicit sample of rational symplectic elements with denominators to 29; the multiplicity of a component as the order of the stabiliser its kernel meets, computed as a lattice index by Smith normal form, against the image degree computed as a Pfaffian; and the contrast between a subtorus the isogeny preserves, where the image degree is constant, and one it does not, where it grows |
| `cm_fields.py` | the Weil classes of a CM field of degree four and six: the CM base point of every family, the balanced divisor classes delta_i(f), the identity that the balanced n-fold product of them is the Weil class w(f) = sum_sigma sigma(f) alpha_sigma, checked for six pairs (F, n) with m = 2, 3 and n = 1, 2, 3, and the identity that the Weil classes of a composite field generate those of its imaginary quadratic subfield |
| `exceptional_classes.py` | the exceptional Hodge classes on the self-product of a Mumford fourfold (eight invariants against six divisor products), the Hodge numbers and adjoint weights that keep the H^3 of a quintic threefold outside abelian type, and the 4n^2-dimensional annihilator of the Weil class in Hochschild cohomology with the two linear-algebra lemmas behind the theorem on the semiregularity form of propagation |
| `mumford_rm.py` | the two exceptional classes on the self-product of a Mumford fourfold as a real multiplication: the commutant of sl(2)^3 on wedge^2 V (four isotypic projectors, ranks 1, 9, 9, 9), the Hodge numbers of the pieces and the K3 type (1,7,1) of the Lie algebra, the product map mu from T (x) T onto H^2(X), the scalar nu by which mu mu^dagger acts on the primitive part U, the transport formula nu g_i g_j with g = e^2/lambda, the norm form 4e^2/lambda of the Kuga-Satake map, and the Kuga-Satake map on the explicit Clifford algebra C(T): C^+(T) = V (x) W with dim W = 32, Psi(v) = v (x) N_i on T_i, and the three N_i anticommuting and independent, which forces the entries of the map to span the cubic field |
| `split_resolution.py` | the data behind the theorem that no two-term complex of powers of the polarisation runs the weakened criterion: the nonzero scalar on a line bundle, the vanishing of H^2 of nontrivial powers on an n-fold with n >= 3, the minimality and secant moments of the three split resolutions found by `hilbert_burch.py`, and the complete-intersection control |
| `paper_labels.txt` | every `\label` of the paper sources, generated from them; `closure_graph.py` checks each theorem label it names against this list |
| `pte_remaining.py` | the three level sets at n = 3 left open by `pte_search.py`, settled by a complete vectorised search (needs numpy) |
| `quaternionic_divisibility.py` | the quaternionic Weil cycle on the lattice O_b^2: it is b^2 times a fixed integral cycle, and the polarisation degree grows like b^2 |
| `divisor_route.py` | the divisor route at n = 2 on one fixed polarised lattice: the K-bilinear classes, the trace identity for the Hodge norm, a pencil of quaternionic loci, and the growth of the least divisor norm along it |
| `split_obstruction.py` | the first-order obstruction map of a split object against the tangent space of the Weil family: kernel the tangent space of the split locus, rank n(n-1)/2, image inside the kernel of the semiregularity map and transverse to the copy of the tangent space there |
| `evaluation_map.py` | the evaluation map of Hochschild cohomology on the explicit split object, in the Hodge basis: the commutative square with the semiregularity map, the rank of the map, and the fact that the whole kernel of the semiregularity map lies in its image, for the explicit object and for every configuration in the box |
| `markman_candidate.py` | the Chern character of Markman's candidate object in dimension eight, exactly: it sits at the point (1,3) of the secant plane for the twist by 3 Theta, the Euler characteristic of the partially normalised union is (d+9)(27-d), and the transforms have nonzero rank |
| `secant_kernel.py` | the Hochschild classes preserving a secant Chern character a u_t + b v_t on an abelian n-fold, n = 3, 4, 5: none in HT^1, and in HT^2 exactly the polarised deformations and the Poisson classes compensated by (d/2) pi _| t^2, n^2 in all, with the controls that the bare and the wrongly compensated classes fail; and the B-field identity x _| (w e^B) = ((e^B x) _| w) e^B |

All arithmetic is exact: `fractions.Fraction`, Python integers, exterior
algebra over the rationals with integer structure constants, or, in
`weil_tangent.py`, the Gaussian rationals built from `fractions.Fraction`.
No step converts to a float. Two scripts, `semireg_fast.py` and
`weil_annihilator.py`, also work modulo a prime, where full rank is a
certificate of full rank in characteristic zero; `weil_tangent.py` uses no
reduction at all.

## Running the Lean check

    cd lean
    elan toolchain install $(cat lean-toolchain)
    lake build
    lean HodgeObstruction.lean

No Mathlib and no dependencies. The file ends with one `#print axioms` line
per theorem; every one must read `does not depend on any axioms`, or
`depends on axioms: [propext]` where propositional extensionality enters
through `decide`, and none may mention `sorryAx`. There are eighty theorems. `lean/README.md` lists them
and says what each one does and does not establish. The workflow in
`.github/workflows/lean.yml` runs the check on every push and fails if the
number of theorems is not eighty, or if any of them depends on an axiom other than propext.

## The Macaulay2 items

Three items of the paper are Ext computations over a polynomial ring and are
carried out in Macaulay2 1.22 with the package `Complexes`:

| script | item | what it settles |
| --- | --- | --- |
| `m2/local_products.m2` | (XXIX) | the local Ext modules and the products of the translation classes at an isolated double point of the support of Markman's candidate, in both local models |
| `m2/lci_products.m2` | (XXXI) | that the local obstruction lives exactly at the germs that are not Cohen-Macaulay: Ext^2(I,I) vanishes at seven Cohen-Macaulay germs, two of them not complete intersections, and not at three that are not Cohen-Macaulay |
| `m2/finite_length_products.m2` | (XL) | that two independent jet classes on a complex with finite length cohomology multiply to a nonzero class whenever its Euler characteristic is nonzero, on eighteen modules and three complexes in two and three variables, and that the hypothesis is sharp: on the cone of the product on the Koszul complex of a point the product vanishes |

Each runs in under a minute:

    cd m2
    M2 --script local_products.m2
    M2 --script lci_products.m2
    M2 --script finite_length_products.m2

Their unedited transcripts are the `.txt` files beside them, and
`m2/README.md` says what each line means. They are not part of
`verify_all.py`.

## Rebuilding the figures

    cd figures
    python3 make_core.py        # the Weil cube, the Hodge spike, the character
                                # grid, the Chern line, the annihilator
    python3 make_plates.py      # the quadric, the Lagrangian sweep, the fibres
    python3 make_secant.py      # the moment curve and the secant plane
    python3 make_smooth.py      # the Bogomolov-Miyaoka-Yau window
    python3 make_more.py        # the hypothesis cube and the null cone
    python3 make_spinor.py      # the spinor quadric and its two rulings
    python3 make_properness.py  # the closed strata of the algebraic locus
    python3 make_diagrams.py    # the Lefschetz ladder, the moduli count, the
                                # signature surface
    python3 make_closure.py     # the closure graph
    python3 make_support.py     # the support theorem
    python3 make_mumford.py     # a Mumford fourfold and its K3 surface
    python3 make_frontier.py    # the five minimal sufficient sets as ribbons,
                                # propagation along a compact Shimura curve,
                                # the Leray summands of an abelian scheme over
                                # a curve with the four operators of the proof,
                                # the rigidity of the Mumford classes, the
                                # audit of the bypass mechanisms, and the
                                # self-extension bounds for the Mumford object
    python3 make_round11.py     # the web of Weil families under descent,
                                # the corrected criterion as a number, and
                                # the Kaehler sign at the exceptional ratio
    for f in fig_*.tex; do pdflatex -interaction=nonstopmode "$f"; done
    python3 checkfigs.py        # must print 0 overlapping label pairs

Six figures, `fig_doublepoint`, `fig_evaluation`, `fig_factor`,
`fig_pencil`, `fig_product` and `fig_tangent`, are block diagrams written
directly in TikZ; their `.tex` files are the sources.

`render3d.py` is a small painter's-algorithm renderer with a perspective
camera and Lambert shading that emits TikZ; the `make_*.py` scripts pass it
their own surfaces, curves, solids and labels. Its constant `DETAIL`, set to
1.5, multiplies every mesh and every sampled curve. `place.py` puts every label
outside the ink rectangle of its own figure and draws a leader to it, and
`checkfigs.py` re-reads the emitted TikZ of every figure and reports any pair
of label boxes that touch; it currently reports none. `palette.tex` holds the
shared colours.

## What is and is not claimed

The theorems of the paper are statements of algebraic geometry and are not
formalised. What is checked here is the arithmetic on which they turn.

The paper does not prove the Hodge conjecture and does not claim to. The
algebraicity of Weil classes on abelian fourfolds, and hence the Hodge
conjecture for abelian varieties of dimension at most five, is a theorem of
Markman (arXiv:2502.03415, arXiv:2509.23403) and is quoted as prior work.

What the paper proves, in every dimension, is the following. The annihilator
of the Weil line in H^{0,2} is canonically the tangent space to the Weil
family, so no object whose Chern character lies on that line is semiregular,
and the weaker hypothesis of Question 11.4 of arXiv:2509.23403 fails for such
objects as well (`weil_annihilator.py`, `evaluation_map.py`). No sum of line
bundles, at any member and in any dimension, satisfies either criterion
(`split_obstruction.py`, `rigidity.py`). For a secant object the local part
of the weakened criterion is a condition on depth, which removes Markman's
candidate in dimension eight (`markman_candidate.py`, `m2/`), and the
Cohen-Macaulay supports that remain admit no resolution by line bundles or
semi-homogeneous bundles that runs the criterion (`hilbert_burch.py`,
`split_resolution.py`).

On the positive side, every Weil family of every CM field, every dimension
and every discriminant has a base point at which the Weil classes are
polynomials in divisor classes (`quaternionic.py`, `cm_fields.py`), and the
conjecture for the family is the algebraicity of one class on one connected
domain. What separates a base point from the family is one propagation
statement: that at one base point some perfect complex with the Weil Chern
character has injective semiregularity map. The paper shows that this holds
as soon as the complex has Ext^2 of dimension 2n(2n-1), the least the
Hochschild computation allows, and that such a complex cannot be supported in
codimension n, so it cannot be carried by any cycle representing the class
(`hochschild_annihilator.py`, `p2_support.py`,
`m2/finite_length_products.m2`). In that form the statement is false, in every
dimension: a complex whose Chern character is exactly a Weil class and whose
semiregularity map is injective would deform along every K-linear deformation
of the abelian variety, hence to very general non-algebraic Weil tori; on those
the only Hodge classes below the top degree are the Weil classes, there are no
subvarieties but points, and every coherent sheaf has vanishing Chern character
in degrees 1 to 2n-1 (Voisin's theorem in dimension four, and the same
argument through Bando-Siu Hermite-Einstein metrics in every dimension). So no
complex meets the Ext^2 criterion (`weil_tori.py` checks the Hodge-theoretic
input). The statement survives in a corrected form, in which the Chern
character may also carry powers of the polarisation; the propagation theorem
holds for it unchanged, and so does a weaker flatness form of it, which
tolerates an object obstructed to first order. For that form the rank of contraction from HT^2 into
the Chern character is (4 + rho) n^2 - 2n for n >= 3, where rho <= 3 is the
rank of a Hankel matrix of the coefficients of the polynomial, and a complex
whose Ext^2 has exactly that dimension meets the criterion; for a general
polynomial the annihilator is exactly the tangent space of the polarised
family. At n = 2 the rank takes the values 12, 16, 18, 20, 22, 23 and 24, and
23 is excluded by parity. The shapes A e^{t theta} + B theta^{2n}, with
t theta the class of a line bundle, which have rho <= 2, are excluded as the
pure form was; for every other shape and n >= 3 the Hodge locus of the Chern
character is the polarised family itself, so that obstruction does not
extend, and at n = 2 one exceptional ratio gives a five-dimensional locus
whose stabiliser is so(4,3) (`p2prime.py`, `p2prime_profile.py`, exact to n = 9, and to
n = 10 in `code/extreme/`). This is a number an object would have to reach;
nothing here constructs one or decides whether one exists.

The Hodge conjecture follows from that statement together with two more, the
algebraicity of the Hodge classes on abelian varieties that divisor and Weil
classes do not generate, and the conjecture for varieties that are not
abelian. The last of these is the conjecture itself: the varieties that are
not abelian include A x P^1 for every abelian variety A, and the conjecture
for A x P^1 gives it for A (pull back along the projection, cup with the
class of A x {0}, push forward), so it alone implies the conjecture for
abelian varieties and then the whole conjecture (Proposition prop:f3ishc of
the paper). An earlier version said the conjecture follows from no two of the
three; that rested on a rule set that omitted this implication, and it was
wrong. The statement that belongs in its place, (F3'), asks for every Hodge
class to be algebraic modulo images of Hodge classes of abelian varieties
under algebraic correspondences. It holds on every variety whose cohomology
is reached from abelian varieties in that way (curves, abelian varieties,
products, surjective images), in degrees 0, 2, 2n-2, 2n, and in dimension at
most three; beyond that it is open, and nothing here closes it (Proposition
prop:f3prime and Remark rem:f3primeopen). With (F3') the three statements are
a minimal route again (`closure_graph.py`, and Section 24 of the Lean file).
The second and
third are not reductions: the self-product of a
Mumford fourfold carries two Hodge classes outside the subring of divisor and
Weil classes, and the H^3 of a very general quintic threefold is not of
abelian type (`exceptional_classes.py`). The two classes on the Mumford
fourfold are the real multiplication by a totally real cubic field on the
primitive part of H^2, and they are algebraic once the Kuga-Satake class of
one of the K3 surfaces of Picard number thirteen attached to the fourfold is
algebraic (`mumford_rm.py`). That Kuga-Satake class is
not known to be algebraic.

With the implications of the literature added, the rule set has exactly five
minimal sufficient sets: the conjecture for varieties that are not abelian
alone; the Lefschetz standard conjecture (L) with the motivatedness of every
Hodge class (M), which together are also equivalent to the conjecture; and
(F3') with (L), with the variational Hodge conjecture for algebraic classes
(V), or with the propagation statement and (F2), the route of the paper, which
is the only one that uses anything proved here. Every member except the
propagation statement is a consequence of the conjecture
(`closure_graph.py`, Section 24 of the Lean file). The propagation statement
is needed only for the split families of the CM fields of degree at least
four. A descent lemma (Proposition prop:descent) links the Weil families: the
product B x Y with an abelian surface Y of Weil type, and a push-forward
against the Weil class of Y, carries the Weil classes of a family in dimension
n+1 to those of every family in dimension n, of every discriminant; and
scalar extension from K to a CM field F containing it carries the Weil
classes of F-families to those of K-families (`descent.py`). An earlier
version said the triples (K, n, delta) are separate problems; that was wrong.
The consequence is that the secant route, granted every demand it makes,
reaches every imaginary quadratic family and still no CM field of higher
degree, so it remains outside every minimal set. One new case of
(L) is proved: for an abelian scheme over a curve whose invariant cycles are
algebraic, the Lefschetz operator is a relative Pontryagin product with
l^{g-1}/(g-1)! plus an operator along the base built from the invariant
cycles, so it is algebraic; this covers the total space of every Mumford
family (`lefschetz_family.py`, `mumford_invariants` in the Lean file). The
mechanism goes back to Tankeev (Izv. Math. 67 (2003)). With Markman's theorem
it gives the Lefschetz standard conjecture for every abelian scheme over a
curve of relative dimension at most four whose invariant classes are Hodge,
and for every fibre power of a family of Weil fourfolds with connected
monodromy SU(V,H), through the Hodge conjecture for all powers of such a
fourfold, which is known (Milne, arXiv:2112.12815) and is reproved in the
paper from the first fundamental theorem for SL. Over its Shimura curve the
total space of a Mumford family satisfies the Hodge conjecture.
For such a total space (L) is exactly propagation of algebraicity along the
curve, so each remaining target becomes one case of (L): one Weil family is
equivalent to (L) for the total space of the family over a curve through a
base point, and the first classes beyond the Weil lines are equivalent to (L)
for the ninefold W x_C W of a Mumford family. Proved outright on the way: the
Hodge conjecture for X_c x X_c at every CM point of a Mumford family, and that
no object meeting the semiregularity criterion is a direct sum of objects with
exterior Ext algebras (`targets_reduction.py`, `two_branch_annihilator` in the
Lean file). The Mumford classes are rigid: the only first order deformation of
the square keeping a rational exceptional class of Hodge type is the direction
of the compact Mumford curve, so no degeneration or larger family reaches them;
propagation along the curve follows from one perfect complex at one CM point
with dim Ext^2 = 119, or from a degree bound at infinitely many CM points
(`mumford_rigidity.py`, `mumford_rigidity_sos` in the Lean file). No
construction from line bundles by cones, tensor products, pull-backs,
push-forwards and Fourier-Mukai functors reaches the Mumford classes, at any
point of the curve, because all of these preserve invariance under the
Lefschetz group (`lefschetz_closure.py`, `lefschetz_counts` in the Lean file).
Among all complex tori, algebraic or not, the component of the Hodge locus of
an exceptional class through the square is the Mumford curve itself, so no
twistor line through a member keeps the class of Hodge type and Markman's
twistor transport for Weil classes cannot move it; the twistor lines on which
the class is of Hodge type carry non-algebraic tori (`twistor_locus.py`).
The square is a holomorphic symplectic variety whose symplectic class generates
the structure T of K3 type inside H^1 (x) H^1, and the exceptional classes are
exactly the dual forms of T twisted by the real multiplication; pull-back of
the dual Beauville-Bogomolov class along a rational map onto a symplectic
subvariety of a hyperkaehler manifold of dimension at least ten, such as the
Hilbert scheme of n >= 5 points on a K3 surface of Picard number thirteen,
would prove them algebraic, and no K3 surface or hyperkaehler eightfold can
serve (`hk_pullback.py`). The five routes that are not closed off are one
statement: specialisation, reduction modulo p and the Lefschetz standard
conjecture for W x_C W are the target itself, the complex with dim Ext^2 = 119
and the Kuga-Satake class imply it, and one of them would suffice; the target
is only the first case of (F2), so a proof of it would leave (F1), the other
cases of (F2) and (F3) open, and (F3) is the whole conjecture
(`mumford_routes.py`).
By Li's theorem (arXiv:2609.27916) the classes are represented by algebraic
cycles at every closed point of every reduction of the curve modulo a prime,
and the target is equivalent to a bound on the Hilbert data of those cycles on
a Zariski dense set of closed points of the arithmetic model. No such complex
and no such bound is known. Nothing here is a proof of the Hodge conjecture.

## Licence

The code and figure sources are released under the MIT licence; see `LICENSE`.
