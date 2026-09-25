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
runs of `code/extreme/`).

Release v1.0.0 (tag `v1.0.0`, commit `ef15bce`) is archived on Zenodo under
DOI 10.5281/zenodo.22950276, recorded in the macro `\zenodoDOI` at the top of
`tex/declarations.tex`, in `CITATION.cff` and in `README.md`. A later GitHub
release gets a new version DOI from Zenodo; update all three places then. There is no separate AI declaration: the use of Claude
for the Python and Lean computations is stated in the Data availability
section.

## Checks before delivering

- `cd code && python3 verify_all.py` ends with `N checks passed, 0 failed`;
  keep the count in `README.md`, `.zenodo.json`, `.github/workflows/lean.yml`,
  `tex/sections/12_verification.tex`, `tex/appendices/D_scripts.tex` and
  `tex/declarations.tex` in step.
- `cd lean && lean HodgeObstruction.lean`: 80 theorems, each axiom-free or
  depending on `propext` only.
- `cd tex && latexmk -pdf main.tex`: 0 errors, 0 overfull or underfull boxes,
  no undefined references.
- Regenerate `code/paper_labels.txt` from the `\label`s in `tex/` whenever
  labels change, and update the label count quoted in
  `tex/sections/12_verification.tex`.
- When a figure generator in `figures/` changes, rerun it, rebuild its PDF and
  its PNG at 200 dpi, run `python3 figures/checkfigs.py`, and copy the files
  to `tex/figures/`.
