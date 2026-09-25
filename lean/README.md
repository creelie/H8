# Machine verification for *Explicit Base Points and Obstructions to Propagation for Weil Classes on Abelian Varieties*

`HodgeObstruction.lean` is a certificate, checked by the Lean 4 kernel, of the
finite arithmetic on which the results of the paper turn.

## What this does and does not claim

The theorems of the paper are statements of algebraic geometry and are **not**
formalised. The cohomology of an abelian variety, the Hodge decomposition, the
Fourier-Mukai transform, Grothendieck-Riemann-Roch, the Lefschetz hyperplane
theorem, hard Lefschetz and the invariant theory of `SL_{2n}` are used as
mathematics and none of them is formalised here. What is formalised is every
place where the paper computes.

## Running it

A Lean 4 toolchain and nothing else. No Mathlib, no dependencies.

    elan toolchain install $(cat lean-toolchain)
    lake build
    lean HodgeObstruction.lean

`lake build` builds the package declared in `lakefile.toml`; the second line
prints the axiom report. Each takes about a minute. Silence from the elaborator means the kernel
accepted every theorem; the block at the foot of the file then prints one line
per theorem. Every line must read `does not depend on any axioms`, or
`depends on axioms: [propext]` where propositional extensionality enters
through `decide` or the core lemmas on natural numbers, and none may mention `sorryAx`. The GitHub workflow in
`.github/workflows/lean.yml` enforces all three, and fails the build if the
number of theorems is not eighty or if any of them reaches for a further
axiom.

## The eighty theorems

| theorem | statement |
| --- | --- |
| `qnorm_mul_check` | the norm on `Z[sqrt(-d)]` is multiplicative on the data used |
| `qmul_conj` | `tau * conj(tau)` equals the norm |
| `characters_differ` | `tau^(2n) != N(tau)^n` at `tau = 2 + sqrt(-d)`, nine fields, `n <= 8` |
| `characters_differ'` | the same at five further witnesses |
| `bad_witness` | the witness `tau = 1 + sqrt(-d)` fails at `(d,n) = (1,4)` and `(3,3)` |
| `bad_witness_exceptions` | and fails exactly when `d=1, 4|n` or `d=3, 3|n` |
| `ratio_not_root_of_unity` | `tau^n != conj(tau)^n` at `tau = 2 + sqrt(-d)` |
| `sign_uniform_and_closed` | the Fourier-Mukai sign is uniform over index sets and equals `(-1)^(g(g+1)/2+k)`, `g <= 5` |
| `subsets_count` | the subset enumeration used there has `C(g,k)` members |
| `semiregularity_target` | `sum_q C(2n,q) C(2n,q+2) = C(4n,2n-2)`, `n <= 7` |
| `secant_count_below_thresholds` | `2n^2+2n < 2^(2n) < 3^(2n)`, `2 <= n <= 8` |
| `thresholds_not_necessary` | `3 < 2^2` and `5 < 3^2`, the two retracted claims |
| `grading_positions_differ` | `(2n,0)`, `(0,2n)` and `(n,n)` are distinct cells for `n >= 1` |
| `weil_delta_parity` | `sqrt(-d)^k` is rational exactly when `k` is even, `k <= 20` |
| `weil_delta_closed_even` | `sqrt(-d)^(2m) = (-d)^m` |
| `weil_delta_closed_odd` | `sqrt(-d)^(2m+1) = (-d)^m sqrt(-d)` |
| `weil_term_counts` | each generator of the Weil line has `2^(2n-1)` monomials |
| `supports_disjoint` | a monomial of the Weil line is never a monomial of a power of `eta` |
| `hodge_dim_count` | `dim Hdg^k = 3` for `k = n` and `1` otherwise, `n <= 6` |
| `weil_line_hodge_type` | the Weil line is of type `(n,n)` exactly when the signature is balanced |
| `clifford_dimensions` | `dim C = 2^b`, `dim C^+ = 2^(b-1)`, `dim KS = 2^(b-2)` |
| `k3_type_only_at_one` | `h^(2,0) = 1` on the pieces of `H^2` forces `n = 1` |
| `moduli_codimension` | the Weil family has codimension `n(n+1)` in `A_{2n}` |
| `discriminant_is_a_norm` | `d^n p^2` is a norm from `K`, with an explicit witness |
| `split_codimension` | the split locus has codimension `n(n-1)/2`, zero only at `n=1` |
| `quat_class_odd` | for `n` odd the quaternionic discriminant class is `b` times a square |
| `quat_class_even` | for `n` even it is a square |
| `quat_product_class` | `d^(n-1)` is a norm for `n` even, with an explicit witness |
| `quat_locus_codimension` | the quaternionic locus has dimension `n(n+1)/2` and codimension `n(n-1)/2` |
| `quat_locus_divisor_at_two` | at `n = 2` that locus is a divisor: `4`, `3`, `1` |
| `irrational_witness_exists` | some `m <= 7` makes `(m + sqrt(-d))^(2n)` irrational, `n <= 8` |
| `weil_line_spanned` | the determinant of `w, tau*w` is `b(w1^2 + d w2^2)`, hence nonzero |
| `norm_form_positive` | `a^2 + d b^2 > 0` for every nonzero `(a,b)`, ten fields |
| `norm_sum_forces_zero` | a positive combination of norms vanishes only when every term does |
| `semiregularity_source_target` | the source overtakes the target at `s = 5` when `n = 2` |
| `secant_witness_at_n_four` | the line bundle witness of Theorem 14.13 reproduces `6 (u + v)` in every degree at `n = 4`, `d = 3` |
| `secant_witness_rank` | that witness has rank `6`, which is `M a` and is positive |
| `vandermonde_nodes_distinct` | the Vandermonde product on the nodes `0, ..., n` is nonzero for `n <= 8` |
| `level_sums_forced` | the level sums recorded in Theorem 14.40 satisfy `sum_j M_j N_j^r = 0` for `r = 1,2,3`, at six level sets |
| `level_sums_totals` | their totals are `1`, `3` and `-2`, so none of the objects has rank zero |
| `level_matrix_nonsingular` | with at most `n` distinct norms the matrix `(N_j^r)` is nonsingular, so every level sum vanishes |
| `gauss_norm_counts` | the number of Gaussian integers of norm `1, 2, 3, 4, 5, 9, 45` |
| `norm_supply_blocks_small_case` | at the nodes `1,2,3,4` the forced `|M_3| = 4` while `Z[i]` has no element of norm `3` |
| `pencil_index_d1` | at `d = 1` two minors of the pencil differ by the constant `2` for all `|k| <= 200`, so the index of `Z[i] x_k` divides `N_1 = 2` |
| `pencil_index_d3` | at `d = 3` the constant minor `-4` and a second minor have gcd dividing `4`, so `N_3 = 4` |
| `pencil_beta_positive` | `4 beta_1(k) = 2 + 2k + k^2` and `9 beta_3(k) = 1 + 2k^2` are positive on the range, discriminants `-4` and `-8` |
| `pencil_square_members` | `beta_1(-1) = 1/4` and `beta_3(-2) = 1`, the two members with a rational point of the locus |
| `split_obstruction_rank` | `n^2 - n(n+1)/2 = n(n-1)/2` and `n(n-1) = 2 (n(n-1)/2)` for `n <= 30`: the rank of the obstruction map of a split object and the even side of the semiregularity kernel |
| `split_obstruction_count` | the bookkeeping of the explicit object at `n = 3`: kernel `15 = 9 + 6`, tangent copy `9`, obstruction image `3`, direct sum `12`, complement `3` |
| `evaluation_not_surjective` | `s C(2n,2) > 2 C(2n,2) + 4n^2` for `5 <= s <= 40` and `2 <= n <= 30`, so the evaluation map of a sum of five or more line bundles is not surjective; at `n = 3`, `s = 6` the dimensions are `66` and `90` |
| `markman_candidate_identities` | for odd `d <= 201` and `N = (d+9)/2`: `12N(N-5) = (d+9)(3d-3)`, at least `(d+9)(2d-1)`; `110N - 12N^2 + 2N(2d-1) = (d+9)(27-d)`; `9 - 2N = -d` and `81 + 36N - (d+9)(27-d) = d^2`, the secant point `(1,3)`; `N(3 + sqrt(-d)) = 2N`; the ranks `8d(d+9)` and `8d(d-9)` are nonzero for `d` not `9` |
| `secant_kernel_arithmetic` | the matrix `[[a, b], [b, -ad]]` cutting out the classes that preserve `a u_t + b v_t` has determinant `-(a^2 d + b^2)`, nonzero for `(a,b)` not `(0,0)`, `a, b < 13`, `d <= 20`; the coefficients `C_k = k! c_k` satisfy `C_(k+1) = -d C_(k-1)`, which makes the Poisson compensation uniform in the degree; and `n(n+1)/2 + n(n-1)/2 = n^2` for `n < 60` |
| `candidate_unnormalised_points` | for odd `d <= 201`: `(d+9)(3d-3) - (d+9)(2d-1) = (d+9)(d-2) >= 12`, so Markman's candidate always has an unnormalised double point; normalising every isolated point gives `chi = 50 N`, never the secant value `72 N - 4 N^2` |
| `tensor_rank_gap` | `C(2n,2) >= 6 > 1` for `n >= 2`, the tensor rank separation || `smooth_invariants` | Noether and the self-intersection formula for a smooth support: `K^2 + e = 12 chi` and `K^2 - e = 6(b^2+d)^2` |
| `smooth_bmy_defect` | the Bogomolov-Miyaoka-Yau defect of a smooth support is `24(b^4 - d^2)` |
| `smooth_bmy_is_d_le_bsq` | so the inequality is exactly `d <= b^2`, over a box in `b` and `d` |
| `smooth_index_vacuous` | the Hodge index bound `9(b^2+d) >= 8b^2` holds for every `d >= 1`, so it never binds |
| `smooth_four_discriminants` | the squarefree odd `d <= 9` are exactly `1, 3, 5, 7` |
| `smooth_table` | the invariants at `b = 3` and those four `d`, as printed in the paper |
| `burch_weight_identities` | the weight `x^2+d` annihilates three moments of the difference, `c_{k+2} + d c_k = 0` |
| `burch_rank_one_discriminant` | nine times the discriminant of the rank one quadratic is `-2b^2 - 18d`, always negative |
| `burch_rank_four_witness` | the rank four candidate at `d = 23` solves the moment system and is removed only by injectivity |
| `closure_omits_conjecture` | the Hodge conjecture is not in the forward closure of what the paper proves and quotes |
| `frontier_suffices` | it is in the closure once (F3) alone is adjoined, the conjecture for the varieties that are not abelian, which covers A x P^1 and so is the conjecture itself; once {Lefschetz standard conjecture, every Hodge class motivated} is adjoined; once (F3'), the conjecture modulo abelian varieties, is adjoined with the Lefschetz standard conjecture, with the variational statement for algebraic classes, or with (P2) for the split families of the CM fields of degree at least four and (F2); and, not minimally, once that (P2), (F2), (F3) or {Lefschetz standard conjecture, (F3)} or {variational statement, (F3)} is |
| `frontier_minimal` | in each of the five minimal sets, {(F3)}, {Lefschetz, motivated}, {Lefschetz, (F3')}, {variational, (F3')} and {(P2) for the split families of the fields of degree at least four, (F2), (F3')}, every element is necessary: dropping any one leaves the conjecture underivable |
| `frontier_smallest` | of the sixteen open statements exactly one, (F3), suffices alone, and of the one hundred and twenty pairs exactly those containing (F3) and the pairs {Lefschetz, motivated}, {Lefschetz, (F3')} and {variational, (F3')} suffice |
| `variational_gives_abelian` | the variational statement for algebraic classes alone puts the conjecture for abelian varieties in the closure, and not the conjecture |
| `lefschetz_gives_abelian` | the Lefschetz standard conjecture gives the variational statement, hence the conjecture for abelian varieties, and not the conjecture |
| `secant_route_descends` | granting both open demands of the secant route reaches the trivial discriminant and, by descent, every imaginary quadratic family, and neither the CM fields of higher degree nor the conjecture |
| `propagation_closes` | the propagation statement for the split imaginary quadratic families puts the whole imaginary quadratic case in the closure, and for the split families of the fields of degree at least four it puts the Weil classes of every CM field there |
| `p2_minimal_count` | `binom(4n,2) - 4n^2 = 2 binom(2n,2) = 2n(2n-1)` for every `n <= 60`: the dimension at which the semiregularity criterion is met automatically |
| `mumford_invariants` | the invariants of `sl_2^3` in `wedge^q (V_1 (x) V_2 (x) V_3)` have dimensions `1, 0, 1, 0, 1, 0, 1, 0, 1`, counted from weight multiplicities: the monodromy invariants of a Mumford family are the powers of the polarisation, which the theorem on the Lefschetz operator of an abelian scheme over a curve needs |
| `two_branch_annihilator` | for n = 2, 3 the monomials of type (p,p) killed by `Q HH^1`, `P HH^1` and `HH^1 HH^1` are `alpha_-`, `alpha_+` and none: the annihilators behind the theorem that an object meeting the semiregularity criterion is not a direct sum of objects with exterior Ext algebras |
| `mumford_rigidity_sos` | a positive multiple of each of the seventeen forms P1, P2, Q1..Q4, R, S1..S4, Z1..Z6 is a sum of squares of integral linear forms with positive coefficients, checked on `{0,1,2}^4`, which suffices for polynomials of degree at most two in each variable: the certificates behind the rigidity of the exceptional classes of a Mumford square |
| `mumford_ext_profile` | the lower bounds `1, 16, 119, 328, 560, 328, 119, 16, 1` for the self-extensions of an object with the Chern character of an exceptional class are palindromic, have alternating sum 112 and sum 1488, and give 800 in even degrees against a Hochschild bound of 688 in odd degrees, so chi(E,E) = 0 forces Ext^1 + Ext^3 >= 400 |
| `lefschetz_counts` | the Sp_8-invariants of wedge^*(V+V) number `1, 3, 6, 10, 15, 10, 6, 3, 1` by the decomposition of each wedge^i V into fundamental modules, the Hodge classes of the Mumford square that are not Lefschetz number `0, 0, 2, 6, 13, 6, 2, 0, 0` (twenty-nine), the Lefschetz classes at a CM point are counted by the coefficients `1, 16, 100, 304, 454, ...` of `(1 + 4y + y^2)^4`, and Weyl's formula for Sp_8 gives `27, 42, 308` for `varpi_2, varpi_4, 2 varpi_2`, with `1 + 27 + 42 + 308 = 378` |
| `criterion_endomorphisms_n2` | for all natural numbers, `2 e0 + 12 = chi + 2 e1` with `e1 >= 8` and `chi >= 1` gives `e0 >= 3`: an object meeting the numerical criterion at n = 2 has at least three endomorphisms |
| `criterion_endomorphisms_n3` | for all natural numbers, `2 e0 + 60 = chi + 2 e1 + e3` with `e1 >= 12`, `e3 >= 40` and `chi >= 1` gives `e0 >= 3`: the same at n = 3 |
| `weil_monomials_separated` | neither Weil monomial lies in the exterior algebra on `V_-^{1,0} + V_+^{0,1}` or on `V_+^{1,0} + V_-^{0,1}`, for `n <= 12`: the Weil line misses every class pulled back from a quotient by an abelian subvariety tangent to an eigenspace |


## Two statements that look true and are not

The natural witness `tau = 1 + sqrt(-d)` for the lemma separating the
characters does not work at every field. At `d = 1` the ratio
`tau/conj(tau)` is `sqrt(-1)`, a primitive fourth root of unity, and at
`d = 3` it is a primitive cube root of unity, so at those two fields the
characters agree at that particular `tau`. The lemma is true, but not by that
route, which is why the proof in the paper uses only the finiteness of the
group of roots of unity of `K`. `bad_witness` records the failure.

The exceptional set at `d = 3` is `3 | n`, not `6 | n`; `bad_witness_exceptions`
records the correct condition.

Neither affects the truth of the theorem, and both are the kind of slip that a
careful reading does not catch and a kernel check does.

## Companion scripts

`code/verify_all.py` in the parent directory performs the same checks in exact
rational arithmetic over Q, independently of Lean, together with the exterior
algebra computations that Lean does not carry, and prints
`823 checks passed, 0 failed`.

## Transcript

`axioms.txt` is the unedited output of `lean HodgeObstruction.lean` under
Lean 4.34.0 (x86_64 Linux, commit 293d5d0c): eighty lines, one per
theorem, sixty-nine reading `does not depend on any axioms` and eleven reading
`depends on axioms: [propext]`, exit status 0, no `sorryAx`. `lake build`
completes with the same report. Each run takes about two minutes.
