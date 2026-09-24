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
of it).

## Checks before delivering

- `cd code && python3 verify_all.py` ends with `N checks passed, 0 failed`;
  keep the count in `README.md`, `.zenodo.json`, `.github/workflows/lean.yml`
  and `tex/sections/12_verification.tex` in step.
- `cd lean && lean HodgeObstruction.lean`: 78 theorems, each axiom-free or
  depending on `propext` only.
- `cd tex && latexmk -pdf main.tex`: 0 errors, 0 overfull or underfull boxes,
  no undefined references.
- Regenerate `code/paper_labels.txt` from the `\label`s in `tex/` whenever
  labels change.
