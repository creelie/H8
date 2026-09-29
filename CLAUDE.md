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
1986 in all; 401 pages; 684 labels). P2_split, (F2) and (F3') remain open. Never use agents or
workflows in this repository's sessions: do the work directly.

Release v1.0.0 (tag `v1.0.0`, commit `ef15bce`) is archived on Zenodo under
DOI 10.5281/zenodo.22950276, recorded in the macro `\zenodoFirstDOI` at the
top of `tex/declarations.tex`, in `CITATION.cff` and in `README.md`. Release
v2.0.0 (tag `v2.0.0`, published by Deep; it accompanies round 24) has the
version DOI 10.5281/zenodo.23038895, and the concept DOI of all versions is
10.5281/zenodo.22950275; they are in `\zenodoVersionDOI` and
`\zenodoConceptDOI`, the README table and `CITATION.cff`. A later GitHub
release gets a new version DOI from Zenodo; update all three places then. There is no separate AI declaration: the use of Claude
for the Python and Lean computations is stated in the Data availability
section.

## Checks before delivering

- `cd code && python3 verify_all.py` ends with `N checks passed, 0 failed`;
  keep the count in `README.md`, `.zenodo.json`, `.github/workflows/lean.yml`,
  `tex/appendices/D_computations.tex` and `tex/declarations.tex` in step.
- `cd lean && lean HodgeObstruction.lean`: 110 theorems, each axiom-free or
  depending on `propext` only.
- `cd tex && latexmk -pdf main.tex`: 0 errors, 0 overfull or underfull boxes,
  no undefined references.
- Regenerate `code/paper_labels.txt` from the `\label`s in `tex/` whenever
  labels change, and update the label count quoted in
  `tex/appendices/D_computations.tex`.
- When a figure generator in `figures/` changes, rerun it, rebuild its PDF and
  its PNG at 200 dpi, run `python3 figures/checkfigs.py`, and copy the files
  to `tex/figures/`.
