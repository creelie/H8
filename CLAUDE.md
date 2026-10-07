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
Round 41 proved the Hodge conjecture for the very general member of the
Vandermonde family (`lem:vgmonodromy`, `thm:vgvandermonde` after
`thm:vandermonde` in `tex/sections/11b_closuregraph.tex`): for characters of
order two the squared Dehn twists along a chain of vanishing cycles give the
monodromy sp(V_a), whose invariants are the powers of the polarisation
[FH91]; for order three Achter-Pries [AP07, Cor. 3.10] gives SU and a class
only when dim V_a = r and p_a = r/2, an abelian variety of Weil type for
Q(sqrt(-3)) with trivial discriminant, so Markman's theorem applies for r = 4, 6;
hence HC for d = 2 in every dimension and d = 3 with r <= 6, in every P^N
(counts 1 + sum_{j>r/2} C(N+1,2j) and 1 + C(N+1,r+2) C(r+2,r/2+1)). Item
(LXXV), `code/very_general.py` (8 checks, 2168 in all); Lean Section 44 (125
theorems); `fig_vgmonodromy`, `fig_vgscope`, `fig_vgcounts` and the roadmap of
the five parts `fig_roadmap` (label `fig:parts`) from
`figures/make_round41.py`; a strip at the foot of `fig_vandermonde`; the
unused figures `fig_witness`, `fig_multiple`, `fig_hodgecount` placed, and the
duplicate `fig_spinor` with `make_spinor.py` deleted. At Deep's choice "Trim
prose" the side remarks `rem:outside`, `rem:secantplace`, `rem:notreductions`,
`rem:remaindershape`, `rem:targetsstatus`, `rem:routemap`, `rem:quarticgap`,
`rem:sexticnoexclusion`, `rem:thirdclosed`, `rem:whyterminal` and
`rem:p2search` were removed (every proved result stays), with the five
bibliography entries cited only there (BKT20, Kim05, Mil99, Orl05, Voi07);
hedges were rewritten, footnotes added in the introduction, the abstract cut
to two sentences, the keywords to three, the MSC given with section names,
and the contents list set to the parts (`tocdepth` 0, with entries for the
appendices and for the declarations and references). FH91 carries no DOI
(doi.org and Crossref could not be reached to verify it). Stale counts and
round wording were removed from `README.md`, `lean/README.md`,
`.zenodo.json`, the workflow, the figure scripts and the code docstrings.
2168 checks, 125 Lean theorems, 391 pages, 738 labels.
Round 42 proved the degree 4 and 6 analogue of Achter-Pries itself
(`setup:cyclic`, `lem:foxmodel`, `lem:cabling`, `lem:hyperplanes`,
`lem:merge`, `prop:cyclicmonodromy`, `lem:newdisc`, `fig_cyclicmerge` before
`thm:vgvandermonde` in `tex/sections/11b_closuregraph.tex`): for a cyclic
cover of degree m in {3,4,6} with n >= 3 and p, q >= 1 the identity component
of the monodromy contains SL(V_a), by the Fox model of the eigenspace, the
collision of two branch points (Y + KI), a lemma on two copies of SL of a
hyperplane, a merge lemma (proved by hand, checked to k = 40) and 38
computed base cases with n = 3, 4; the discriminant of the new part is
trivial for m = 3, 4, and for m = 6 exactly when an even number of
coordinates equal 3 (2 is not a norm from Q(sqrt(-3))). So `thm:vgvandermonde`
now gives HC for the very general member for d = 2, for d = 3, 4 with r <= 6,
and for d = 6 with r <= 4; for d = 6, r = 6 the classes are algebraic except
on the non-split Weil sixfolds (example (1,1,2,2,3,5,5,5)), which stay open.
Count 1 + C(N+1,r+2) T_d(r+2) + [d even] sum_{j >= r/2+2} C(N+1,2j).
References [Fox53], [DM86] carry no DOI (Crossref and doi.org could not be
reached). Item (LXXVI), `code/cyclic_monodromy.py` (7 checks, 2175 in all);
Lean Section 45 (130 theorems); `figures/make_round42.py`, with
`fig_vgmonodromy`, `fig_vgscope`, `fig_vgcounts` and the strip of
`fig_vandermonde` redrawn; a one-sentence abstract at Deep's request.
2175 checks, 130 Lean theorems, 395 pages, 746 labels.
Round 43 (Deep chose "Three shifts" on a decision card) proved
`thm:efourthreelevels` after `thm:efourtwolevels` in
`tex/sections/10c6_objects.tex`: for a convolution on E_0^8 whose Weil
pieces sit at three consecutive shifts s, s-1, s-2 (one parity class Q at
s-1, the other split into T at s and B at s-2), the 40960 classes of
`thm:efourtwolevels`(i) stay, d_E acts on them only by cup products into
H^5(c,e) with c in T, e in B (multiples excluded by counting up and down
steps), each piece has 960 such target dimensions, and the cut of the
weighted Cayley graph on the 64 ratios is at most 16(960 - lambda_min) =
18432 (least eigenvalue -192, attained by the split zeta_3 zeta_4 in
{1, i}), so dim Ext^2 >= 22528 > 104; shifts not in three consecutive
values stay open in `rem:convolutionsopen`. Item (LXXIV) now covers two and
three shifts (`code/convolutions_efour.py`, parts (F) to (I), 16 checks,
2182 in all); Lean Section 46 (133 theorems, 103 axiom-free, 30 on
`propext`); `fig_efourthree` from `figures/make_round43.py` and the strip of
`fig_efourshifts` redrawn; a row of `tab:scope`.
2182 checks, 133 Lean theorems, 397 pages, 748 labels.
Round 44 excluded every convolution on E_0^8 whose Weil pieces have their
shifts within five consecutive values (`cor:efourfive`, dim Ext^2 >= 640),
after `fig_efourthree` in `tex/sections/10c6_objects.tex`:
`lem:efourspread` (for positive spread d_E has all its leaves between pieces;
the groups H^4 of spread two whose ratio moves all four coordinates, one by
-1, thirteen ratios of weight 256 once and 64 twelve times, are reached by no
coboundary and killed by no term, by the parity count X = |K| - 1; d_E
vanishes on spread three; spread-one H^3 terms drop the shift by one or two),
`lem:cayleycut` (a cut of a Cayley graph weighs at least min_H |H| w(S \ H),
1024 for the group of the 64 ratios of one parity, only at H = 0),
`thm:efourspreadtwo` (one parity at {s, s-2} or {s+2, s, s-2}: >= 1024),
`thm:efourspreadthree` (one parity at s, the other in {s-3, s+3}:
64 1072 - 128 8 = 67584), `prop:efourgap` (one parity at y, pieces at y+1,
none at y-1, y+3, or the dual: >= 640 |T|), and `prop:efourcupkernel` (the
cup products leave at least 484 = 400 + 84 of the 3668 diagonal classes,
exactly 484 for general components, rank 3184 mod 1000003, so longer
products must remove 380); within six values the arrangements single shifts
five apart and {s, s-4} with {s-1, s-5} are left, and wider ones are open in
`rem:convolutionsopen`. Item (LXXVII), `code/efour_blocks.py` (21 checks,
2203 in all; the piece-by-piece part takes about eight minutes); Lean
Section 47 (139 theorems, 106 axiom-free, 33 on `propext`);
`fig_efourspread` from `figures/make_round44.py`; a row of `tab:scope`; an
`\enlargethispage{2pt}` in `tex/sections/11b_closuregraph.tex`.
2203 checks, 139 Lean theorems, 402 pages, 756 labels.
Round 45 settled the two arrangements left within six values
(`lem:efourlonely`, `prop:efoursingle`, `prop:efourpairs`, `cor:efoursix`,
`fig_efoursix`, after `cor:efourfive` in `tex/sections/10c6_objects.tex`):
with each parity at a single shift, at an odd distance g >= 5, a nonzero
term on a diagonal class at a piece a has a as its only piece and runs
through M_1, M_2, M_3 (U = 3, D = 0 or U = 2, D = 1); every step adds 1 to
the shift mod 4, so the four nodes have distinct residues and the multiples
serve at most one of the two shifts, and the 64 28 = 1792 diagonal classes
at the other inject by `prop:nothingenters` (g = 1, 3 by the earlier
theorems); with {s, s-4} and {s-1, s-5} the groups H^3 of
`thm:efourtwolevels` between adjacent shifts are touched by nothing and form
the cut of A u B' in the Cayley graph of the 28 ratios that move three
coordinates and change the parity (weight 640, 636 subgroups, least only at
H = 0), so >= 640. Hence every convolution whose shifts lie in six
consecutive values fails (`cor:efoursix`, >= 640 > 104); wider
arrangements, other than single shifts at any odd distance, stay open in
`rem:convolutionsopen`. Item (LXXVIII), `code/efour_six.py` (6 checks,
2209 in all; about seven minutes, mostly the interleaved splits piece by
piece); Lean Section 48 (144 theorems, 109 axiom-free, 35 on `propext`);
`fig_efoursix` from `figures/make_round45.py`; the row of `tab:scope`.
Round 45 also replaced the one double-precision rank of the paper
(`prop:fourfoldrank`) by a proof in ball arithmetic: `code/fourfold_certified.py`,
part (H) of item (LXXII) (8 checks, about six minutes), reduces every
integral of theta functions to coefficients of holomorphic sections by
(nabla a) b = (d_a nabla(ab) + H)/(d_a + d_b), H holomorphic, finds them by
interpolation at rational points in Arb at 128 bits with the theta tails
bounded, takes the invariant sections on B_j as the image of the projector
of the two half periods, and certifies rank 12 per piece and 192 in all by
Gram determinants whose intervals exclude 0 (also with x1 x2 = x2 x3 = 0,
the sign reversed, t = (2,5,7)); the introduction and the computations list
say that no statement rests on floating point. `fig_product` was redrawn
(the plot to n = 7 with ticks and the shaded codimension).
2217 checks, 144 Lean theorems, 405 pages, 761 labels.
Round 46 was the arXiv v1 pass, a line-by-line read of the whole paper
against Deep's request for a consistent text with no over- or under-claims.
It corrected the constants of the multiplicativity formula `eq:weilmult` and
`cor:prodalg` in `tex/sections/10c2_basepoints.tex` (with
`code/weil_product.py`), made `ex:splitsmall` integral (`code/split_locus.py`),
proved the integrality recursion (`code/integrality.py`, new equation
`eq:omegaprod`), moved `fig_moduli` to Appendix B as `fig:moduli`, and added
`prop:divisortemplate` after `prop:orlovequality` in
`tex/sections/10c5_polarised.tex` (sheaves on divisors in the Orlov template:
the profile allowed by Serre duality and the contraction bounds; a vector
bundle G on a smooth divisor with ch(i_* G) in P_theta needs [D] = b theta,
ch(G) = r S(theta) T_b(theta), r >= 2, no line bundle; the Ext profile of
V|_D; nothing at n = 5), with `code/attack/gaps/orlov_growth/divisor_sheaves.py`
(19 checks, run by `code/attack_checks.py`) and Lean Section 49. Scope
corrections: `cor:fourdiscriminants`, `cor:latticeburch` and the smooth case
hold at the twist 3 Theta only (d <= b^2 in general, d <= 9 at b = 3, d in
{1,3,5,7} when N = (9+d)/2 is an integer); a non-Cohen-Macaulay support has
nonzero local Ext^pd (`cor:cmdichotomy`(i), by Auslander-Buchsbaum and
Nakayama) but is excluded only where two smooth codimension-two branches meet
transversally; for a Cohen-Macaulay support condition (b) of
`thm:factor`(iii) is equivalent to one vanishing in H^1(Z, Ext^1) (the scalar
forced by the trace) and condition (a), first-order extension along the
polarised deformations, remains, so the rule of `tab:rules` for such
supports now cites `cor:cmdichotomy` and its open leaves in
`code/closure_graph.py` include the extension; `rem:markmanscope` says that
nothing here bears on the objects of Markman's proofs; `thm:nosum` is called
vacuous by `thm:p2false`; in the introduction and `thm:final`(iv)
`thm:p2primenumber` is stated as a lower bound for every object, an object
attaining it meeting the criterion (the converse is not proved); the stale "beyond"
entries of `tab:scope` for the pure form now read "nothing"; Appendix B lost
a duplicated footnote and `prop:whichtypes`(ii), (iii) match their proof.
`code/fourfold_certified.py` no longer imports scipy (the workflow installs
only sympy, numpy and python-flint): its pivoted QR is a numpy
Businger-Golub pivoting in `_pivots`.
2218 checks, 147 Lean theorems (110 axiom-free, 37 on `propext`), 411 pages,
763 labels.
Round 47 answered Deep's "verify everything in lean" with Lean Sections 50 to
55 (twenty-two theorems): the annihilator of a Weil class in HH^* at
n = 1, 2, 3 (`lem:annihilator`, item (XXXVIII)); the polarised criterion as
a number (`thm:p2primenumber`, item (LII)) on fourteen characters at n = 3
and one of each Hankel rank at n = 4, by rank certificates (exact
annihilating vectors and images independent modulo 998244353, written by
`lean/generate/make_section51.py` from `code/p2prime.py`; one theorem per
n = 4 case to keep the kernel's memory near 6 GB); `eq:omegaprod`,
`eq:weilmult`, `thm:weilmult` and `ex:splitsmall` (items (XV), (X)); the
secant Chern recursion and rank one (item (XX)); the Gram matrix of the
Weil plane (item (L)(A)); the lattice and Burch-rank results
`thm:lattice`, `prop:lowrankburch` (items (LXIX), (LXX)). Statements for
all d are proved without `omega`, which pulls in Classical.choice and
Quot.sound. `lean/README.md` and `code/computations/lean.tex` now list the
computations that have no Lean counterpart (Macaulay2, ball arithmetic, the
search of (XXII); and exact linear algebra of about thirty items not yet
ported). No Python change (2218 checks); 169 Lean theorems (114 axiom-free,
55 on `propext`).
At Deep's request the Data availability section credits him with the
computations: "carried out by Deep Bhattacharjee in Python, with the C
libraries FLINT and Arb through python-flint, in Macaulay2 and in shell
scripts, and the finite arithmetic was formalised by him in Lean 4", with the
Claude Code sentence kept. Deep also named Julia, C and PARI; the archive
contains none of them, so they are not listed (add them only if such code is
added to the archive).
Round 48 carried the exact linear algebra of the remaining items into Lean,
Sections 56 to 81 (240 theorems): items (I), (XIII), (XVI), (XVIII), (XIX),
(XXIII), (XXIV), (XXXIV) to (XXXVII), (XLI) to (XLIII), (XLVII) to (XLIX),
(LI), (LIII), (LIV) and (LVII) to (LXIII), with rank certificates (exact
kernel vectors, and minors nonsingular modulo 998244353 or 1000033 with
i = 649529, 754974721 with sqrt(-d) sent to a recorded root, or 1000003).
The data blocks are written by `lean/generate/make_*.py` (with `emit.py`);
each reproduces its block of the Lean file verbatim. Parts still outside
Lean are listed in `lean/README.md` and `code/computations/lean.tex`: the
exhaustive searches of (XIII), five shapes at n = 3 and the n = 4, 5 run of
(LIII), (LVIII)(A) to (C), (LIX)(B) to (D), (LX)(F), (LXI)(D), (F) to (H),
besides the Macaulay2 items, the ball arithmetic of (LXXII)(H) and the
search of (XXII). Kernel cost: `decide +kernel` is slow on Int arithmetic
and on densifying long sparse lists, so heavy checks use data constants,
transposed rows, sparse minors, or an argument at the level of indices
(`mumford_motivic_projectors` checks that the exchanges are commuting
involutions and takes ranks as traces of idempotents); keep each theorem
under about 6.5 GB. The abstract gained the very general Vandermonde clause
(quadrics in every dimension, cubics and quartics up to dimension seven),
and two "Clearly" were replaced by reasons. No Python change (2218
checks); 409 Lean theorems (127 axiom-free, 282 on `propext`); 411 pages,
763 labels.
Round 49 answered Deep's asks for a fully analytical, hand-written paper and
for an attempt on (F2) and (F3'). Proofs that rested on code alone now have
hand proofs wherever one exists: among them the rank 45 of ev_E in
`prop:evaluation`, the least eigenvalue -192 in `thm:efourthreelevels`, the
exceptional ratio of `rem:p2primeexceptional` (the Cayley form, so(4,3),
citing [HL82] and [Bry87]), `prop:p2primelocus`(iv), ch(O_S) in
`tex/sections/10c8_supports.tex`, the Weil orbit counts 70, 490, 6125 and
the lattice degrees of `cor:delsarteall`, the pencil `prop:pencil` (Lean
Section 16 now checks its polynomial identities, `code/divisor_route.py`
rewritten), and in the Mumford sections `prop:mumfordwhere`(i) by the skew
Cauchy formula, `lem:mumfordmu`, Steps 2 and 3 of `thm:mumfordpowers` with
`rem:mumforddet`, `thm:mumfordcm` for every power by weight multisets,
`rem:mumfordunitary`, `prop:notwistor`(iii), `prop:hksquare`(i), (ii) (now
with a nonzero rational factor rho in (ii)), `thm:lefschetzclosure`(ii),
(iv), `prop:mumforddivisor` and `prop:mumfordmotivic`. Cross-checks that only
confirmed a hand proof were deleted; the computations that remain are stated
precisely and cited to [BMB26], and the introduction says so.
`thm:pterange`(ii) no longer claims n + 2 norms at n = 7, 8. New:
`lem:pfaffian` (10c3), `prop:jacobiancontinuation` (10c5: line bundles on
C^(g-1) pushed to the Jacobian do not continue the two certificates for
g >= 4), `prop:f3primeample` (11b: ample complete intersections inherit (F3')
and the Hodge conjecture outside the middle degree, and in the middle degree
for a very general member when the vanishing cohomology is not of type
(r/2, r/2)); references [ACGH85], [Mac62], [Bry87]. `verify.ps1` was
rewritten for Windows (Python suite, then the Lean file; logs in
`verify_python.log` and `lean/axioms.txt`; the expected count is read from
the file), and Deep ran the Python suite on his Windows machine (2218 checks
passed, 0 failed). 2218 checks,
409 Lean theorems (128 axiom-free, 281 on `propext`), 416 pages, 766 labels.
Round 50 answered Prof. Mandal's standard, relayed by Deep (journals reject
the paper as computational; the text must be analytical, with no synthetic
phrasing, transitions or hedges), with Deep's choice "Whole monograph" on a
decision card: every statement whose only proof was a computation in
[BMB26] now has a hand proof in the text or is removed. The paper cites
[BMB26] only in the introduction, Appendix A and the data availability
section, and the introduction and the title-page footnote say that no
statement rests on the archive. Hand proofs: the semiregularity, secant and
support chapters; the convolutions on E_0^6; `thm:mumfordrigid` block by
block (`fig_rigidity` redrawn); the lattice degrees of the Delsarte shapes;
the base of `prop:cyclicmonodromy` (the full twist of two branch points with
opposite exponents is a transvection, `lem:mergefive` at five points,
`lem:hyperplanes` from dim Y = 2 with Andre's semisimplicity [And92];
`fig_cyclicmerge` redrawn); `thm:closure` by four closed sets C_1 to C_4,
with `prop:f3primestrength` and `rem:f2rule`; `thm:quarticrank` and
`thm:quarticp2prime`(ii); `prop:sexticintegral`(ii) by the four values of
N_w; and the middle degree of `prop:p2primeprofile` for every n (one coupled
block of size 2^{n+1}, whose kernel is ker((K'H')^2 - |u|^2) after the
Koszul signs are collected). Removed: `prop:fourfoldrank` with its
ball-arithmetic rank, `thm:burchsearch` with `tab:burch`, `fig_extprofile`,
`rem:pterangemeaning`, parts (ii) and (iii) of `prop:quarticexclusions`,
`rem:quarticmixedkernel`, `prop:sexticintegral`(v), `prop:sexticweilmin`,
`fig_sexticweil` and `rem:sextictargets`. `ssec:closure` is titled "Which
hypotheses suffice". No code change (2218 checks, 409 Lean theorems);
`items.tex`, `lean.tex`, `item_labels.json`, `README.md` and `.zenodo.json`
say which computations the paper no longer uses. 412 pages, 759 labels.
Deep also asked for a full unconditional closure of the conjecture; it was
declined, since nothing proves it.
Round 51 retitled the paper "Hodge Conjecture for Very General Vandermonde
Quadric Intersections". Deep asked for a title of the form "every rational
Hodge class is algebraic"; that statement alone is the conjecture and was
declined, and Deep found the first true version ("Every Rational Hodge Class
Is Algebraic on Very General Diagonal Quadric Intersections of Vandermonde
Type") too long. The abstract now leads with that result, and the
introduction defines a Vandermonde quadric intersection and states
`thm:introvandermonde` (Theorem 1.2: `thm:vgvandermonde`(iii) and
`cor:twodiagonal`(ii)) after the plan of the parts. Three
`\enlargethispage` commands (one in the introduction, two at footnotes in
`tex/sections/10c6_objects.tex`) keep the build free of bad boxes, and
revision traces were removed from `.zenodo.json`, `lean/README.md` and
`code/computations/lean.tex`. This is the final PR before the next release;
when Deep sends its version DOI, record it as described below (and the new
archive title in `BMB26`). No code change (2218 checks, 409 Lean theorems);
413 pages, 760 labels.
Round 52 recorded the version DOI of release v4.0.0 (tag `v4.0.0`, the merge
commit `ea2d6c3` of round 51, published by Deep from a prefilled release
link), 10.5281/zenodo.23197107, in `\zenodoCodeID`, the release number of the
data availability section and of `BMB26` (with the archive title of round
51), the README table and `CITATION.cff`. Deep sent the DOI; zenodo.org and
doi.org could not be reached from the session to check the record, while the
GitHub release itself was checked.
Round 53 (Deep: "attempt a full closure", with the OpenAI preprints mirrored
in creelie/math01-openAI; he chose "Weil loci title" on a decision card)
retitled the paper "Algebraic Loci of Weil Classes on Abelian Varieties",
with a one-sentence abstract that leads with `thm:main`, and added Section 23,
`tex/sections/13b_preprints.tex` (`sec:preprints`, before the closure theorem,
now Theorem 24.1). It takes five theorems of the unrefereed preprints
[OAI26a] to [OAI26f] as hypotheses (P1) to (P5) (CM abelian varieties, split
Weil eightfolds, Kuga-Satake classes of K3 surfaces, products of K3 surfaces,
abelian covers and diagonal complete intersections; [OAI26g] is cited and not
used) and proves the deductions by hand: `prop:stabilise` (Schoen's product
with a Weil surface of the same discriminant), `thm:weilsix` (Weil classes on
every Weil sixfold and split eightfold; the very general Vandermonde bounds
become nine for cubics and quartics and seven for sextics),
`lem:cliffordspan` (two-sided multiplications span End C^+, by the character
of a 2-group and Burnside), `lem:ksgenerates`, `thm:kspowers` (HC on
A^k x S^l for the Kuga-Satake variety A of a K3 surface S), `cor:kstype`,
`cor:mumfordall` (every power of a Mumford fourfold), `cor:k3all` (every K3
surface in the class A, HC on Hilbert schemes and moduli spaces, the real
multiplication locus is everything), `prop:k3twosmall` (K3^[2] type with
dim T <= 19, or T embedding in the K3 lattice over Q, through Markman's
[Mar24] and Witt cancellation; open only for six shapes of dimension 20 to
22), `cor:simplexhc`, `cor:vgalldegrees` (every power of the very general
X_{d,r}(lambda), every d, c, r, from `thm:vandermonde` and [OAI26a, Thm 1.1]),
`cor:f2cm` and `rem:remains` (what stays open: Weil eightfolds of nontrivial
discriminant, n >= 5, CM fields of degree >= 4 off CM points, other
exceptional classes, (F3') beyond A). The introduction, `thm:twostand`,
`thm:final`(vi), `rem:f3primefrontier`, `rem:f3primeopen`, `rem:mumfordks`
and `rem:mumfordpowersopen` point to it, always as conditional. The URL
github.com/openai/math could not be opened from the session (proxy 403); the
preprints were read from Deep's mirror. CITATION.cff and `BMB26` keep the
v4.0.0 archive title. No code change (2218 checks, 409 Lean theorems);
423 pages, 779 labels.
Round 54 (Deep: "attempt for a full closure now") sharpened two results of
Section 23 in `tex/sections/13b_preprints.tex`. `prop:k3twosmall` now holds,
under (P4), for every fourfold of K3^[2] type whose Neron-Severi space is
isotropic or represents -2 (the orthogonal of T in the Mukai lattice
H^2 + Qe, q(e) = 2, is then isotropic, and Witt cancellation embeds T in
Lambda_Q); this covers Picard number at least four and every Lagrangian
fibration, the condition is necessary for the argument, and the shapes left
are (2,10), (4,5), (5,4) at rho = 3, (3,7), (7,3) at rho = 2 and (2,11) at
rho = 1. The new `prop:coversreach` (before `rem:remains`) shows that (P5)
with `thm:main` cannot reach the open Weil families: an isotypic part H_chi
of an abelian cover is pulled back from the marked curves, of dimension
3g - 3 + k_chi = 3n - k_chi/2 < m n^2 when it is of (F,n)-Weil type, so its
image is meagre for m >= 2, n >= 2 and for m = 1, n >= 4; the one boundary
case, etale cyclic covers of degree 3, 4, 6 of genus-4 curves (sixfolds),
needs the multiplication map H^0(K + eta) x H^0(K - eta) -> H^0(2K) to be
onto at one point (Griffiths, [Voi02, Ch. 10]). The data availability
section now says, at Deep's request, that Deep Bhattacharjee computed all
the calculations in C, Python, Julia, Macaulay2, Lean 4 and shell scripts
with the assistance of Claude Code, and that the programs in the archive are
those in Python (FLINT and Arb through python-flint), Macaulay2, shell and
the Lean certificate (this replaces the round 47 note that Julia, C and PARI
are not named). No code change (2218 checks, 409 Lean theorems); 424 pages,
780 labels.
P2_split, (F2) and (F3') remain open. Never use
agents or workflows in this repository's sessions: do the work directly.

Release v1.0.0 (tag `v1.0.0`, commit `ef15bce`) is archived on Zenodo under
DOI 10.5281/zenodo.22950276, release v2.0.0 (tag `v2.0.0`, published by Deep;
it accompanies round 24) under the version DOI 10.5281/zenodo.23038895, and
release v3.0.0 (tag `v3.0.0`, published by Deep; it accompanies round 28)
under 10.5281/zenodo.23047883, release v3.1.1 (tag `v3.1.1`, published
by Deep; it accompanies rounds 30 to 33) under 10.5281/zenodo.23078541, and
release v3.2.0 (tag `v3.2.0`, published by Deep; it accompanies rounds 35 to
37) under 10.5281/zenodo.23093099, and release v4.0.0 (tag `v4.0.0`, published
by Deep; it accompanies rounds 38 to 51) under 10.5281/zenodo.23197107; the
concept DOI of all versions is
10.5281/zenodo.22950275. They are listed in the README table and
`CITATION.cff`. The paper names one DOI for the code, `\zenodoCodeID` in
`tex/declarations.tex` (used by the data availability section and the `BMB26`
bibliography entry), and no GitHub URL; it holds the version DOI of release
v4.0.0. When Deep publishes a later release and sends its version DOI, put it
in `\zenodoCodeID`, the release number of the data availability section and
of `BMB26`, the README table and `CITATION.cff`. There is no separate AI declaration: the use of Claude
for the Python and Lean computations is stated in the Data availability
section.

## Checks before delivering

- `cd code && python3 verify_all.py` ends with `N checks passed, 0 failed`;
  keep the count in `README.md`, `lean/README.md`, `.zenodo.json`,
  `.github/workflows/lean.yml` and `tex/declarations.tex` in step.
- `cd lean && lean HodgeObstruction.lean`: 409 theorems, each axiom-free or
  depending on `propext` only; the number, in words, is also in
  `README.md`, `lean/README.md`, `code/computations/lean.tex`, `.zenodo.json`
  and `tex/declarations.tex`, and in figures in the workflow.
- `cd tex && latexmk -pdf main.tex`: 0 errors, 0 overfull or underfull boxes,
  no undefined references.
- Regenerate `code/paper_labels.txt` from the `\label`s in `tex/` whenever
  labels change, and rerun `code/computations/make_computations.py` after
  the build when theorem numbers change, so that `COMPUTATIONS.md` matches
  `tex/main.pdf`.
- When a figure generator in `figures/` changes, rerun it, rebuild its PDF and
  its PNG at 200 dpi, run `python3 figures/checkfigs.py`, and copy the files
  to `tex/figures/`.
