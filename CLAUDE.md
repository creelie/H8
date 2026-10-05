# Working on this repository

Layout: the repository root is the verification package (shipped as the
`Hodge_Git` zip); `tex/` holds the paper sources (shipped as the `Hodge_tex`
zip). `figures/` and `tex/figures/` are kept identical.

## Delivering a round of changes

Always hand the user all four of these together:

1. the compiled paper, `tex/main.pdf` (also copied to `main.pdf` at the root);
2. the TeX zip, `updatedhodgetex_N.zip`, containing `Hodge_tex/` = the
   contents of `tex/`;
3. the code zip, `githubupdatedhodgecode_N.zip`, containing `Hodge_Git/` =
   everything else in the repository except `tex/` and this file;
4. the repository link, https://github.com/creelie/H8, with the link to the
   branch the work was pushed to.

`N` is the round number (round 5 was the correction that (F3) is equivalent
to the Hodge conjecture; round 6 added its weaker form (F3') and what is known
of it; round 7 added the shape theorem for an object meeting the (P2)
criterion; round 8 proved that criterion false in its pure form, with Chern
character exactly a Weil class, via very general non-algebraic Weil tori
(`thm:p2false`, item (LI), `code/weil_tori.py`), and restated (P2) in the
corrected form of `rem:p2prime`; round 9 retitled the paper "Explicit Base
Points and Obstructions to Propagation for Weil Classes on Abelian Varieties"
and added a Data availability section to `tex/declarations.tex`; round 10
recorded the Zenodo DOI of release v1.0.0; round 11 computed the corrected
criterion (P2') in closed form (`thm:p2primenumber`, `prop:p2primeprofile`,
`prop:p2primelocus`, items (LII), (LIII), `code/p2prime.py`,
`code/p2prime_profile.py`), proved the descent and scalar extension lemma
`prop:descent` (item (LIV), `code/descent.py`), which corrects
`prop:separate` and splits (P2) in the closure graph so that only (P2) for the
split families of the CM fields of degree at least four is needed, added
the flatness form `prop:p2flat` of the criterion, the exceptional n = 2 ratio
`rem:p2primeexceptional`, `prop:powers`, `cor:lefschetzsmall` and
`prop:mumfordfivefold` (with attributions to Milne and Tankeev), and the long
runs of `code/extreme/`; round 12 added Priyabrata Mandal as second and
corresponding author (dagger on Deep Bhattacharjee, double dagger on Mandal,
Ushashi Bhattacharya third), audited every DOI of the bibliography, and added
the quartic CM subsection `ssec:quartic` of `tex/sections/10d_cmfields.tex`
(`prop:quarticquat` to `rem:quarticgap`), the Mumford powers results
`prop:mumfordwhere` to `rem:mumfordpowersopen` after `rem:mumfordks` in
`tex/sections/11_scope.tex`, the objects results `lem:p2primesummands` to
`rem:flatsums` after `prop:p2flat` in `tex/sections/10c_construction.tex`,
`thm:cmpropagation` (iv), (v) restated in the chosen-cycle and corrected
forms, item (LV) with `code/attack/` and `code/attack_checks.py`, and the
figures of `figures/make_round12.py`; round 13 made the paper journal-shaped
(the long chapters split into sections `sec:basepoints`, `sec:propagation`,
`sec:corrected`, `sec:secantobjects`, `sec:beyond`; the computations and the
Lean certificate moved to Appendices D and E, `tex/appendices/D_computations.tex`
and `tex/appendices/E_lean.tex`, with no program names in the paper; a 90-word
abstract), redrew most figures, and attacked the three remaining inputs:
`prop:flatall`, `prop:orlovequality`, `prop:quarticsecant`,
`thm:quarticobstruction`, `prop:f3primestrength`, `prop:orthpowers`, with
`code/attack/gaps/` as part (E) of item (LV) and Lean Sections 32 and 33,
eighty-eight theorems); round 14 proved the description of the integral
classes `lem:quarticlattice` for every real quadratic field by a local
computation, and extended `thm:quarticobstruction` (no dimension-count
certificate from Orlov products) to every quartic CM field through the
arithmetic of `prop:quarticother` modulo the different and modulo 4
(`code/attack/gaps/quartic_obstruction/a1_lattice_local.py`,
`a1_lattice_general.py`, `a1_rank2_arith.py`; Lean Section 34, ninety-two
theorems); round 15 restated `thm:quarticobstruction` in three parts: the exact
formula r(kappa) = r^2(v_1) + 64 + r^2(v_2), correcting the claim that r(kappa)
is always 100, 102 or 104 (it is 88 or 94 for biquadratic F with a class of
N_w = 2), and the flatness of kappa for every quartic CM field when the
B-field is trivial, proved by factorisation over the real places and checked
for seven real quadratic fields (`a1_flat_general.py`, `a1_rkappa_general.py`);
round 16 showed that the count is special to quartic fields: for sextic CM
fields the secant profile is palindromic, chi is negative definite and a
minimal object is not excluded (`code/attack/gaps/sextic/s1_profile.py`,
Lean Section 35, ninety-three theorems); round 17 replaced that proposition by
the subsection `ssec:sextic` of `tex/sections/10d2_quartic.tex`
(`prop:sexticcount`, with closed formulas for r^2 and r^3, the bound
r(kappa) <= 252 < 264 and flatness, and `rem:sexticparity`), with item (LVI),
`code/sextic_count.py`; round 18 tested that count on the lattice of integral
characters (`prop:sexticintegral`, `rem:sexticnoexclusion`, item (LVII),
`code/sextic_lattice.py` with `code/attack/gaps/sextic/s2_lattice.py`): chi is
even, the threshold is at most 26 for every shape, and for sixteen cubic
fields every integral flat character has chi <= -32, so nothing is excluded;
and enlarged the domain of (F3') in `tex/sections/11b_closuregraph.tex`
(`prop:aclosure`: blow-ups, projective bundles, Hilbert schemes, Fermat
hypersurfaces, K3 surfaces with algebraic Kuga-Satake class;
`prop:f3primesmall`: uniruled fourfolds, rationally connected fivefolds;
`rem:f3primefrontier`); round 19 added the F-Weil part of the sextic
characters (`lem:sexticweil`, `prop:sexticweilmin`, least -chi 192 over
Q(zeta_7)^+ with q = 3 + alpha, item (LVIII), `code/sextic_weil.py`), the
quartic kernels on X x X (item (LIX), `code/quartic_kernels.py`), the four
possible motivic groups of a Mumford fourfold and the system generated by the
known classes (`prop:mumfordmotivic`, `prop:mumfordformal`, item (LX),
`code/mumford_motivic.py`), K3 powers and varieties of K3^[n] type
(`prop:k3powers`, threshold t(t+1)/2, S^[231]; `prop:k3ntype`,
`cor:fanolines`; item (LXI), `code/k3_hodge.py`), zero-cycles and
rationally connected fibrations for (F3') (`prop:f3primefibration`,
`rem:f3primesharp`, item (LXII), `code/f3prime_chow.py`), Schoen's product
argument [Sch98, Prop. 10], and `prop:f2isab` with `rem:f2rule`: (F2) is
equivalent to the Hodge conjecture for abelian varieties, so with that rule
adjoined the minimal sets are {F3}, {L,M}, {L,F3'}, {V,F3'}, {F2,F3'} and
P2_split lies in none (checked in `code/closure_graph.py`, the rule set itself
is unchanged); it also made the paper journal-shaped (60-word abstract, the
figures of `figures/make_round19.py`, redrawn `fig_closure` and
`fig_frontier`); round 20 added the routes from outside algebraic geometry
(`ssec:outside` of `tex/sections/11b_closuregraph.tex`: `prop:positivitynotest`,
`lem:cibig`, `thm:massgap`, the conjecture as the vanishing of an integrality
gap for mass-minimising currents, stated for M large, `ex:mumfordmass`,
`rem:outside`; item (LXIII), `code/mumford_mass.py`), the Weil structure of a
Mumford fourfold at a CM point (`prop:cmsource`, `lem:splitcm`,
`rem:cmsource` in `tex/sections/11d_mumfordrigid.tex`; item (LXIV),
`code/cm_source.py`; Lean Section 36, ninety-eight theorems), the figures of
`figures/make_round20.py`, an ethics statement, and Zenodo placeholders for
release v2.0.0 (macros `\zenodoVersionDOI`, `\zenodoConceptDOI` in
`tex/declarations.tex`, and the DOI table in `README.md`); round 21 computed
the rank of the corrected criterion at a quartic CM field exactly
(`thm:quarticrank`: r = 64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2, fifteen
values, least 80 only for constant p, never 100; item (LXV),
`code/quartic_rank.py`), extended `thm:p2false` to every CM field and every
n >= 2 through the Weil tori of the field (`ssec:cmweiltori` of
`tex/sections/10d1_cmfields.tex`: `lem:cmweiltori`,
`prop:cmweiltorussheaves`, `thm:cmpurefalse`), so that a complex meeting the
quartic criterion has non-constant polynomial part and dim Ext^2 >= 88
(`cor:quarticleast`); merged Deep's `lem:absemireg`, `rem:absums` and the
Lean theorem `cm_abelian_semiregular_count`; and proved that Hdg^2 = Ab^2
descends along dominant rational maps (`prop:f3primedominant`), which with
Shioda's monomial cover puts every smooth Delsarte fourfold in the domain of
(F3') (`prop:delsarte`, 29 sextic shapes; item (LXVI), `code/delsarte.py`;
Lean Section 37, one hundred and one theorems), with the figures of
`figures/make_round21.py` (`fig_quarticrank`, `fig_delsarte`); round 22 proved,
by Khovanskii's toric compactification, that a hypersurface of simplex type
(`def:simplextype`, `lem:simplexchart`, `lem:toricmod`, `thm:simplextype` in
`tex/sections/11b_closuregraph.tex`) smooth in a projective toric variety lies
in the domain of (F3') and has its Hodge conjecture reduced to Fermat varieties
of the lattice degree e, so every smooth Delsarte hypersurface of every
dimension and the cyclic covers branched along them are covered
(`cor:delsarteall`, Klein quartic e = 7, loop sextic e = 2604; item (LXVII),
`code/simplex_type.py`; Lean Section 38, one hundred and three theorems;
`fig_simplextype` from `figures/make_round22.py`), and excluded at rank 88 the
characters of theta^4 shape by the Weil tori (`prop:quarticweiltori` in
`tex/sections/10d2_quartic.tex`, check (J) of `code/quartic_rank.py`);
round 23 computed the Hodge locus of every character at a quartic CM field
(`prop:quarticlocus`: the first-order locus is linear, of dimension 8 + 4a + b
with a mid places and b exceptional ones, 16 c_t^2 = u_s u_s'; it is the Weil
tori S_F only for the theta^4 span, the polarised family D_F when both places
are mid, and a Spin(4,3) x Spin(4,3) orbit with NS = 0 when both are
exceptional, ranks 94 or 110), so that the Weil tori exclude exactly the
theta^4 shape at 88 and every other character there needs an object
(`cor:quarticlocus`; check (L) of `code/quartic_rank.py`; Lean Section 39,
one hundred and five theorems), and added `rem:delsartequotient` on quotients
of Delsarte hypersurfaces by diagonal groups (no gain for Greene-Plesser
mirrors); round 24 rebuilt the paper around one proved target, `thm:main`
at the head of the introduction (for every CM field, n >= 2 and discriminant,
the algebraic locus of the Weil classes contains an explicit CM base point, is
dense, and is either the whole domain or meagre, so the Weil classes are
algebraic on every member iff it is closed), retitled it "Density of the
Algebraic Locus of Weil Classes on Abelian Varieties" (Deep asked for no
"and", colon or comma in the title and a single bullseye target), wrote a
50-word "we prove" abstract of that one statement, and decided Markman's explicit quartic
pair [Mar25c, Example 11.2.7] against the weakened criterion
(`lem:freegerm`, `lem:divisorgerm`, `thm:quarticlocal`,
`prop:markmanquarticclasses`, `cor:markmanquarticfails`, `rem:question1122`
before `rem:quarticgap` in `tex/sections/10d2_quartic.tex`: compensated
classes x_j preserve every quartic secant character, and a sheaf locally free
on a smooth curve, or the ideal of a curve in a smooth divisor, fails at such
points, so both sheaves of the example fail; Question 11.2.2 itself stays
open), with item (LXVIII), `code/quartic_local.py` and
`m2/local_germs.m2`, `fig_quarticlocal` from `figures/make_round24.py`, and
Lean Section 40 (one hundred and ten theorems); round 25 recorded the Zenodo
DOIs of release v2.0.0; round 26 added, beside the paper and outside
`verify_all.py`, the working note `notes/fourier_mukai/` (`rank88_note.tex`:
the Fourier-Mukai transforms T_b, S_beta act through an sl_2 at each real
place, and the exponential rank-88 characters with lambda^{-1} in the lattice
of the member are excluded; the linear shape and lambda^{-1} outside that
lattice stay open; `mukai_place.py`, 30 checks, and `smooth_support.py`, 25
checks of another session's smooth-support note), and merged Deep's
Hodge_tex_v25 upload into `tex/sections/10c8_supports.tex` (`lem:smoothinjective`,
`rem:gysinkernel`, `lem:blochduality`, `prop:smoothrank`, `rem:smoothrank`,
`lem:binomialmoments`, `thm:lattice`, `cor:latticeburch`, `rem:latticedefect`;
the injectivity is automatic only on a simple fourfold, and h^0(N) >= 4 comes
from e(S) != 0), with item (LXIX), `code/lattice_congruence.py` (708 checks,
1986 in all; 401 pages; 684 labels); round 27 proved that a Hilbert-Burch
resolution of a secant support has rank r >= 2, and r >= 3 at d = 1, 5 when
its Chern classes are polynomials in Theta (`prop:lowrankburch`,
`rem:lowrankburch` in `tex/sections/10c8_supports.tex`; item (LXX),
`code/burch_rank.py`, 18 checks, 2004 in all; 403 pages; 686 labels), and
corrected Deep's route note on those supports as the working note
`notes/route/` (`route_note.tex`, 6 pages; `route_checks.py`, 19 checks; the
toy search of the first version in `notes/route/toy/`): the fourfolds of Weil
type are Markman's theorem, the route aims at W(K,4,delta) on eightfolds and
needs [Mar25b, Question 11.4], condition (a) runs over all ten polarised
directions, [S] = N Theta^2, and its numerical lemma omitted the vanishing of
Chern classes above the rank. Round 28 made the paper journal-shaped for Annals or Memoirs: title
"Density of Algebraic Loci of Weil Classes on Abelian Varieties" (no "the",
"a", "and", colon or comma), a 60-word "we prove" abstract, the main theorem
`thm:main` with its clause (iv) proved through `lem:cmgeneric` and
`cor:verygeneral` in `tex/sections/10d1_cmfields.tex`, the closing section
`thm:final` in `tex/sections/14_closure.tex` (the conjecture is equivalent to
(F2) and (F3')), the paper in five parts, no MDPI footnote on the title page,
the prose rewritten to state what is proved (hypotheses of the closure
computation are called hypotheses), and Appendices D and E removed: the paper
cites the archive as [BMB26] (no item numbers, no program names, no GitHub
URL), and `COMPUTATIONS.md` at the root lists items (I) to (LXX) and the Lean
table with the results of the paper each one checks (generated by
`code/computations/make_computations.py` from `tex/main.aux`); new 3D figures `fig_mainlocus` and
`fig_twohalves` from `figures/make_round28.py`; plain-text MDPI resubmission
notes for version 6 (no LaTeX, no equations) went with the round 28 zips;
round 29 recorded the version DOI of release v3.0.0 (10.5281/zenodo.23047883)
in `\zenodoCodeID`, the README table and `CITATION.cff`; round 30 added Section
22, "The main theorem in every family" (`tex/sections/13_families.tex`, before
the closure theorem, which is now 23.1): the dichotomy for every flat class
on every smooth projective family (`lem:algstrata`), density of CM points in
a Mumford-Tate domain (`lem:cmdense`), a family with a CM member through
every Hodge class of an abelian variety (`prop:cmfamily`), (F2) equivalent
to propagation of algebraicity from CM members of abelian schemes
(`thm:f2propagation`, via Andre's theorem [Mil20, Theorem 1]), (F3') as the
absence of Hodge classes off the part reached from abelian varieties
(`prop:abpart`), the algebraic locus of a real multiplication on K3 squares
(`setup:rm`, `thm:rmlocus`: dense, contains every CM point, stable under
G(Q) by Buskin, all or meagre), and `thm:twostand`; no code change (2004
checks, 110 Lean theorems, 364 pages, 706 labels); round 31 tightened the
proofs of Section 22 without new labels: `prop:cmfamily` (the multiple of
the class, the component through the CM points), `thm:f2propagation` for
polarised abelian schemes with the split families identified through
`rem:cmmember` and `prop:cmweil`(iv), `setup:rm` (the locus does not depend
on the choice of the K3 surfaces, by Buskin), and `thm:rmlocus`, whose
dichotomy is now proved from local families of polarised K3 surfaces and the
density of G(Q) in G(R)^+ by the Cayley transform instead of a global family
over an arithmetic quotient (no Zariski-closed claim is made there any more);
it also added `fig_cmseed` (the abelian scheme over the component of the Hodge
locus, the dense CM points, strata of the algebraic locus and three fibres
drawn as tori) from `figures/make_round31.py`, four footnotes in Section 22,
a 52-word abstract, the published version of [KOU23] and the chapter DOI of
[Kur65], after every reference of the bibliography was checked online
(publisher pages, DOI and Crossref records, arXiv); 367 pages. Round 32
answered Deep's request to attack the Massey products of length 4 to 6 on
E_0^6 with the subsection `ssec:convolutions` at the end of
`tex/sections/10c6_objects.tex`: `setup:convolution`, `lem:harmonicmodel`
(harmonic model of a twisted complex of line bundles, products as planar
trees), `lem:indexsum`, `thm:fewpieces` (fewer than 2n pieces with
nondegenerate differences never meet the corrected criterion),
`prop:weilpieces` (on E_0^{2n}, E_0 = C/Z[i], the 2 4^{n-1} line bundles
L_zeta with prod zeta = +-1 have signed Chern characters adding up to
2 4^{n-1} (alpha + conj alpha); with three multiples of theta, r = 7n^2 - 2n,
525 diagonal classes against 57 at n = 3), `lem:degreedrop`,
`prop:nothingenters` (for n >= 3 no product reaches the diagonal classes),
`prop:cupkernel` (the cup products leave at least 249 of them),
`thm:esixdiagonal` (only fourfold products along M_{t2} -> M_{t3} -> L ->
M_{t1}, with sigma_1 = sigma_3 = -sigma_2, act, into a space of dimension
(t_2 - t_1)^6, so the criterion needs rank >= 192 and t_2 - t_1 >= 3;
lengths 3, 5, 6 do not act), `prop:mixedplacement` (t_1 <= p - 2 and
p + 2 <= t_2 < t_3: only sigma_1 = sigma_2 = -sigma_3 carries products, of
length four along M_2 -> M_3 -> M_1 -> L_zeta, into sixteen targets of
dimension ((t_2 - p)^2 - 1)^3, total >= 432, or along M_3 -> M_1 -> L_zeta
-> M_2, into (t_3 - t_2)^6; a convolution carries at most one of the two;
the other mixed placement is its dual) and `rem:convolutionsopen` (those
fourfold products are not computed; n = 4 does not close), six footnotes,
the figures `fig_convolutions` and `fig_diagonalbudget` of
`figures/make_round32.py`, item (LXXI), `code/line_bundle_convolutions.py`
(89 checks, 2093 in all; the path search is pruned by a lower bound for the
excess still to come and checked against the exhaustive one), and Lean
Section 41 (one hundred and fourteen theorems); 375 pages, 721 labels.
Round 33 checked the Kuga-Satake class of the Picard-13 surface S_lambda of
`thm:mumfordks` against every proved case of the Kuga-Satake Hodge conjecture
and the literature to 2026, found none that contains it, and recorded the
arithmetic in `rem:mumfordks` of `tex/sections/11c_mumford.tex` (a
Shioda-Inose structure needs transcendental rank at most five; Floccari,
Paranjape and Ingalls-Logan-Patashnick need at most six; S_lambda has rank
nine and a totally real, not CM, endomorphism field); no new labels, no code
change (2093 checks, 114 Lean theorems, 375 pages, 721 labels).
Round 33 continued, at Deep's request for constructions, with the round 32
fourfold Massey family on E_0^6, computed in theta functions after pulling
the pieces back along degree-4 covers of each E_0^2: `prop:fourfoldrank`
(the products have rank 192 on the 192 diagonal classes of type (1,1,0), a
double-precision rank with singular-value ratio 0.016, so the diagonal
count can be met), `prop:explicitconvolution` (an order of the 35 pieces
whose Maurer-Cartan equation is exactly x_1 x_2^zeta = 0 and
sum x_2^zeta x_3^zeta = 0; diagonal kernel <= 57 but dim Ext^2 >= 2560),
`lem:allthree` (Weil pieces of opposite parity differing in all three
coordinates with adjacent shifts give isolated H^3 blocks of dimension
prod |zeta_j - zeta'_j|^2) and `thm:noconvolution` (every convolution of
these pieces with |t_i - p| >= 2 has dim Ext^2 >= 69 > 57, so the route
closes negatively at n = 3, Markman's trivial-discriminant case; n = 4
open), with `rem:convolutionsopen` rewritten, four footnotes, the
double-precision exception stated in the introduction, the title-page
footnote and the computations list, item (LXXII), `code/fourfold_products.py`
(42 checks, 2135 in all), Lean Section 42 (117 theorems), and an
`\enlargethispage{2pt}` at `setup:rm` in `tex/sections/13_families.tex`;
`make_computations.py` now joins item titles that span lines; 379 pages,
726 labels.
Round 34 recorded the version DOI of release v3.1.1 (tag `v3.1.1`, the merge
commit `0b4bd65` of round 33, published by Deep; no v3.1.0 was released),
10.5281/zenodo.23078541, in `\zenodoCodeID`, the release number of the data
availability section and of `BMB26`, the README table and `CITATION.cff`.
Round 35 added a title-page footnote in `tex/main.tex` citing the earlier
preprint of the first and third authors, "Relative secant cycles and Hodge
classes", Preprints.org, doi:10.20944/preprints202602.0462.v5 (checked on
preprints.org), as containing errors and incomplete proofs and replaced by
this paper, with the change of author order, and an `\enlargethispage{3pt}`
at the start of `tex/sections/02_conventions.tex`; no code or label change.
Round 36 added the subsection `ssec:speciallocus` at the end of the
propagation part of `tex/sections/10d1_cmfields.tex` (`def:speciallocus`,
`prop:speciallocus`, `cor:speciallocus`, `thm:escape`, `rem:escape`): the
locus of members with smaller Hodge group contains every member at which
the paper exhibits algebraic Weil classes and has every property of
Sigma_F used in `thm:main`, yet is meagre, so those properties cannot decide
the dichotomy (an obstruction); and, by the Andre-Oort theorem of Pila,
Shankar and Tsimerman ([PST21, Theorem 1.1], with [Tsi18] for A_g; both
checked online), the bounded criterion is needed only along one sequence of
CM points that leaves every proper special subvariety, which exists in the
Hecke orbit (a bypass of the dense orbit, still an equivalence). The
introduction and `thm:final`(iv) cite them; no code change (2135 checks,
117 Lean theorems, 383 pages, 732 labels).
Round 37 polished the text against Deep's writing criteria: the form of the
semiregularity criterion whose Chern character carries powers of the
polarisation is called the polarised form throughout the paper (the section
is `sec:polarised`, the file `tex/sections/10c5_polarised.tex`; the code and
`README.md` keep the older word "corrected" for (P2'), and the item titles
(LII), (LIII) of `code/computations/items.tex` follow the paper), hedges and
traces of revision were removed, and `fig_speciallocus` from
`figures/make_round37.py` draws `prop:speciallocus` and `thm:escape`
(2135 checks, 117 Lean theorems, 383 pages, 733 labels).
Round 38 recorded the version DOI of release v3.2.0 (tag `v3.2.0`, the merge
commit `a80abf6` of rounds 35 to 37, published by Deep),
10.5281/zenodo.23093099, in `\zenodoCodeID`, the release number of the data
availability section and of `BMB26`, the README table and `CITATION.cff`.
Round 39 made Deep Bhattacharjee the only corresponding author at Deep's
request: the dagger stays on Deep, Mandal's double dagger is gone, and the
title-page footnote reads "Corresponding author: Deep Bhattacharjee" with
both of Deep's addresses on one line; the author order is unchanged (Deep,
Mandal, Ushashi Bhattacharya); 383 pages, no code or label change.
Round 40 retitled the paper "Algebraic Loci of Weil Classes from Abelian
Varieties to Diagonal Complete Intersections" (Deep picked it on a decision
card; he asked for a title claiming the Hodge conjecture, which was declined
because nothing proves it), added a second sentence to the abstract, and
proved (F3') for diagonal complete intersections of Vandermonde type
(`thm:vandermonde`, `cor:twodiagonal`, `rem:vandermonde`, `fig_vandermonde`
in `tex/sections/11b_closuregraph.tex`): X = C^r/G for the generalised
Fermat curve C [GDHL09], so X lies in the class A, every smooth complete
intersection of two diagonal hypersurfaces is of this type, the Hodge
conjecture on X reduces to the abelian varieties B_[a] cut out by the
characters, and it holds for d in {3,4,6}, N <= 6 and d = 2, N <= 12
(dimension at most five, Markman and Moonen-Zarhin), in particular for two
diagonal cubics, quartics or sextics in P^6 (70, 490, 6125 Weil orbits); this
uses known (F2) cases and is not new progress on (F2). It also proved the
two-shift case at n = 4 on E_0^8 (`lem:efourshifts`, `thm:efourtwolevels`,
`fig_efourshifts` in `tex/sections/10c6_objects.tex`: dim Ext^2 >= 40960 >
104; three or more shifts stay open in `rem:convolutionsopen`), with items
(LXXIII) `code/diagonal_ci.py` (16 checks; parts (C), (D) in double
precision, no statement rests on them) and (LXXIV)
`code/convolutions_efour.py` (9 checks), Lean Section 43 (121 theorems),
two rows of `tab:scope`, the figures of `figures/make_round40.py`, footnotes,
and the references [Ter88] (doi verified on J-STAGE; by its title it
treats complete intersections of Fermat type and of quadrics; it could not be
read, so any overlap with `thm:vandermonde` is unchecked) and [Har77]; [GDHL09] has no verified DOI and carries none.
2160 checks, 121 Lean theorems, 391 pages, 740 labels. Two stale
`\enlargethispage` commands in `tex/sections/10c4_rank.tex` were removed.
P2_split, (F2) and (F3') remain open. Never use
agents or workflows in this repository's sessions: do the work directly.

Release v1.0.0 (tag `v1.0.0`, commit `ef15bce`) is archived on Zenodo under
DOI 10.5281/zenodo.22950276, release v2.0.0 (tag `v2.0.0`, published by Deep;
it accompanies round 24) under the version DOI 10.5281/zenodo.23038895, and
release v3.0.0 (tag `v3.0.0`, published by Deep; it accompanies round 28)
under 10.5281/zenodo.23047883, release v3.1.1 (tag `v3.1.1`, published
by Deep; it accompanies rounds 30 to 33) under 10.5281/zenodo.23078541, and
release v3.2.0 (tag `v3.2.0`, published by Deep; it accompanies rounds 35 to
37) under 10.5281/zenodo.23093099; the concept DOI of all versions is
10.5281/zenodo.22950275. They are listed in the README table and
`CITATION.cff`. The paper names one DOI for the code, `\zenodoCodeID` in
`tex/declarations.tex` (used by the data availability section and the `BMB26`
bibliography entry), and no GitHub URL; it holds the version DOI of release
v3.2.0. When Deep publishes a later release and sends its version DOI, put it
in `\zenodoCodeID`, the release number of the data availability section and
of `BMB26`, the README table and `CITATION.cff`. There is no separate AI declaration: the use of Claude
for the Python and Lean computations is stated in the Data availability
section.

## Checks before delivering

- `cd code && python3 verify_all.py` ends with `N checks passed, 0 failed`;
  keep the count in `README.md`, `lean/README.md`, `.zenodo.json`,
  `.github/workflows/lean.yml` and `tex/declarations.tex` in step.
- `cd lean && lean HodgeObstruction.lean`: 121 theorems, each axiom-free or
  depending on `propext` only.
- `cd tex && latexmk -pdf main.tex`: 0 errors, 0 overfull or underfull boxes,
  no undefined references.
- Regenerate `code/paper_labels.txt` from the `\label`s in `tex/` whenever
  labels change, and rerun `code/computations/make_computations.py` after
  the build when theorem numbers change, so that `COMPUTATIONS.md` matches
  `tex/main.pdf`.
- When a figure generator in `figures/` changes, rerun it, rebuild its PDF and
  its PNG at 200 dpi, run `python3 figures/checkfigs.py`, and copy the files
  to `tex/figures/`.
