# Machine verification for *Algebraic Loci of Weil Classes from Abelian Varieties to Diagonal Complete Intersections*

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
number of theorems is not one hundred and thirty-three or if any of them reaches for a further
axiom.

## The one hundred and thirty-three theorems

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
| `tensor_rank_gap` | `C(2n,2) >= 6 > 1` for `n >= 2`, the tensor rank separation |
| `smooth_invariants` | Noether and the self-intersection formula for a smooth support: `K^2 + e = 12 chi` and `K^2 - e = 6(b^2+d)^2` |
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
| `quartic_squares_mod4_phi` | the squares modulo `4` in `Z[phi]`, `phi^2 = phi + 1`, are `0, 1, 1 + phi, 2 + 3 phi` |
| `quartic_no_square_phi` | neither `-1` nor twice a unit is a square modulo `4` in `Z[phi]`: the case `Q(sqrt 5)` of the rank-two argument |
| `quartic_squares_mod4_sqrt2` | the squares modulo `4` in `Z[sqrt 2]` are `0, 1, 2, 3 + 2 sqrt 2` |
| `quartic_no_square_sqrt2` | `3`, `1 + 3 sqrt 2` and `1 + sqrt 2` are not squares modulo `4` in `Z[sqrt 2]` |
| `quartic_rank_two_congruences` | `m = 9` has no solution `1 <= m <= 8` modulo `13` or `17`, and modulo `5` only `m = 4` |
| `quartic_euler_minimal` | the minimal profiles `1, 8, r, 8, 1` with `r = 18, 20, 12` have Euler characteristic `4, 6, -2` |
| `orlov_equality_count` | `n(n-1) + (2n)^2 + n(n-1) = 6n^2 - 2n` for `3 <= n <= 64`, and `1 + 16 + 1 = 18` |
| `orlov_n4_euler` | the minimal profile at `n = 4` has `chi = -2`, while every secant character has `chi = 8d(a^2 d + b^2) >= 8` (for all natural numbers) |
| `quartic_squares_mod4_mod8` | a square is `0` or `1` modulo `4`, an odd square `1` modulo `8`, twice a square `0` or `2` modulo `8` |
| `quartic_rank_two_small_odd_parts` | the rank-two conditions on `m` in `[1, 8]` for `D = 3, 7` and `D = 6, 10, 14` have no solution, and for `D = 2` leave `m = 1, 5` |
| `quartic_rank_two_large_odd_part` | for every modulus `n >= 10` no `m < 9` is `9` modulo `n` (for all natural numbers) |
| `quartic_sqrt2_units_mod4` | `3` and `1 + 2 sqrt 2` are not squares modulo `4` in `Z[sqrt 2]`, `(1 + sqrt 2)^2 = 3 + 2 sqrt 2`, `(3 + 2 sqrt 2)^2 = 1` modulo `4`, and `5` is not `+-1` modulo `8` |
| `sextic_thresholds` | the thresholds `r^3 - 2 r^2 + 22` of the six computed sextic secant profiles are `2, -6, 10, 26, 8, 12`, the generic minimal Euler characteristic is `-26`, and `(-4)^3 = -64` |
| `cm_tetrahedra` | the zero-sum four-sets of the eight weights `(+-1, +-1, +-1)` are six unions of opposite pairs and the two tetrahedra `T_+`, `T_- = -T_+`, each meeting every opposite pair once |
| `cm_square_monomials` | on the square, `132 = 100 + 32` monomials of weight zero, the `32` being tetrahedron monomials distributed `1, 4, 6, 4, 1` on each tetrahedron |
| `cm_tetrahedron_pairs` | the six two-element subsets of `T_+` fall into three pairs by the set of coordinates in which their weights differ |
| `cm_profile_forces_equal` | on the box `[-10, 10]^3`, equal values of `abs(a_2 - a_3)`, `abs(a_1 - a_3)`, `abs(a_1 - a_2)` force `a_1 = a_2 = a_3` |
| `cm_pairs_three_cycle` | a permutation of the four diagonals of the cube fixing none of the three pairings is a three-cycle |
| `cm_abelian_semiregular_count` | for `1 <= n <= 60`, the annihilator of the class of an abelian `n`-fold in an abelian `2n`-fold has dimension `6n^2 - n`, and its complement in `HT^2` has dimension `C(2n, 2)` |
| `quartic_rank_values` | the tuples `(mu, rho_1, rho_2, R_1, R_2)` allowed at a quartic CM field give exactly fifteen values of `64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2`, the least `80` only at `(0, 0, 0, 8, 8)`, never `100`, and nine values when `rho_1 = rho_2` |
| `delsarte_loop_sextic` | for the loop sextic, `A B = 15624 I` with `B` the circulant `(3125, -625, 125, -25, 5, -1)`, rows of `B` summing to `2604`, and Jacobian ring dimensions `1, 426, 1751, 426, 1`, total `15625` |
| `simplex_klein_quartic` | for the Klein quartic, `C R = 7 I` with `R` the exponent matrix in the chart `z = 1` and `C` explicit, `det R = 7`, `det A = 28` for the full exponent matrix, and `C` not zero modulo `7`, so the lattice exponent is `7`; the Euler number summed over the torus strata is `-4`, the value `((1 - 4)^3 - 1 + 12) / 4` of a smooth plane quartic |
| `simplex_loop_sextic` | for the loop sextic, `C R = 2604 I` with `C` explicit, `det R = 2604 = 2^2 * 3 * 7 * 31`, and `C` not zero modulo any of these primes, so the lattice exponent is `2604`; the Euler number summed over the torus strata is `2610` for the loop and for the Fermat sextic, the value `((1 - 6)^6 - 1 + 36) / 6` of a smooth sextic fourfold |
| `quartic_exceptional_pair` | in the exterior algebra of `V_s + V_s'` at a real place of a quartic CM field, `theta^4 = 24 alpha_s alpha_s'` and `(alpha_s + alpha_s')^2 = 2 alpha_s alpha_s'`; `theta^3 D = 0` and the `theta^2 D` are four distinct monomials for `D` in `V_s^{0,1} (x) V_s'^{0,1}`; and the two deformations `xi'_0`, `xi''_0` that are not `F`-linear send `alpha_s`, `theta`, `theta^2` to `theta b_{s,0} b_{s,1}`, `2 b_{s',0} b_{s',1}`, `4 theta b_{s',0} b_{s',1}` and symmetrically, so the place is exceptional exactly when `16 c^2 = u_s u_s'` |
| `quartic_locus_counts` | the rational characters with both places exceptional have rank `94` or `110`; the annihilator of a character has dimension `8 + 4a + b`, one of `8, 9, 10, 12, 13, 16`; `so(4,3)` has dimension `21` and maximal compact subalgebra of dimension `9`, `su(2,2)` has `15` and `7`, and the orbits have dimension `21 - 16 = 5` and `15 - 11 = 4` |
| `quartic_compensated_bivectors` | in the exterior algebra on `H^1(X) = U_1 + U_2`, with `q = 2`, the classes `x_j = (pi_j _| theta_j^2, 0, pi_j)` annihilate the four classes spanning `S(0,2)`, and the six symmetric maps at the two places annihilate `theta_1` and `theta_2` (`decide +kernel`) |
| `quartic_rank_certificates` | a `20 x 20` minor of the contraction matrix of `4 beta'` and a `12 x 12` minor of that of `alpha_0`, for `f_1 = 2`, `f_2 = 1/2`, are invertible modulo `1000003` (`decide +kernel`) |
| `quartic_koszul_squares` | for the Koszul resolution of `R/(x_1,...,x_c)`, `c = 3, 4`, the Yoneda square `a_k a_l` is represented by a nonzero vector exactly when `k != l` and `k, l <= c`, and the coboundaries vanish at the origin |
| `quartic_line_two_planes` | a nonzero vector of `[-6,6]^4` has a nonzero component outside one of two complementary coordinate planes |
| `quartic_first_factor_character` | the pieces of Markman's Example 8.2.4 have the characters used there, `ch(F_d) = Theta - (d/6) Theta^3` and `chi(F_d, F_d) = 8 d` for `d <= 60` |
| `conv_pure_weil_identity` | for `n = 2, 3, 4` there are `2 * 4^(n-1)` exponent vectors `zeta` in `mu_4^n` with `prod zeta = +-1`, half of each sign, and the signed sum of the `e^(c_1(L_zeta))` has coefficient `2 * 4^(n-1)` on `alpha` and on `conj(alpha)` and `0` on every other monomial in the `c_j`, `c'_j` (`decide +kernel`) |
| `conv_cup_kernel` | at `n = 3` the graphs `Gamma_tau` of the six types of diagonal classes have `4` components when `tau` has an entry `2` and `16` otherwise, so the classes constant on components span `3 * 4 * 1 + 3 * 16 * 4 = 204` dimensions, `249` with the `45` classes of the multiples, out of `525` (`decide +kernel`) |
| `conv_run_excess` | for `3 <= n <= 12` and every placement of `p` among the `t_i`, a run from a piece `L_zeta` through distinct multiples back has excess at least `2n - 4 >= 2`, and a closed walk through the multiples alone at least `2n - 3`; at `n = 2` a run of excess `0` exists (`decide +kernel`) |
| `conv_esix_thresholds` | along `M_2 -> M_3 -> L -> M_1` with `Ext` degrees `0, 6, 0` the shifts are `d, d + 1, d - 4, d - 3`, the product lands in `Ext` degree `6` and `sigma_1 = sigma_3 = -sigma_2`; `r = 24, 57, 104` at `n = 2, 3, 4`; `(t_2 - t_1)^6 = 1, 64, 729`, `249 - 64 = 185 > 57`, `249 - 57 = 192`, and `(t_2 - t_1)^6 >= 192` exactly when `t_2 - t_1 >= 3` |
| `ff_partner_counts` | with `zeta_j = i^(e_j)`, the sixteen pieces with `prod zeta = 1` and the sixteen with `prod zeta = -1`; every piece has `3`, `6`, `7` partners of the other parity differing in `1`, `2`, `3` coordinates, and for the `7` the block dimension `D = prod_j |zeta_j - zeta'_j|^2` is `16` six times and `64` once, `160` in all; the `112` pairs carry `2560` classes (`decide +kernel`) |
| `ff_shift_table` | in the three placements of the multiples relative to `p`, the shifts `mu_i`, `nu_i` of a piece one step from or to `M_i` and the extremes `lambda_i`, `kappa_i` over steps between the multiples are those of the table in the proof of the lemma on pieces that differ everywhere, and satisfy `lambda_i <= 0 <= kappa_k`, `kappa_i >= lambda_i + 2`, `lambda_i <= mu_i + 2`, `nu_i <= kappa_i + 2` (`decide +kernel`) |
| `ff_noconvolution_counts` | the kernels `11`, `19` of `x_1`, `x_3` on a surface at `t = (2, 5, 6)`; the cover degrees; `3^6 = 729`, `16 * 24^3 = 221184`, `4^6 = 4096`; and the bounds `249 - (45 + 15 * 9) = 69 > 57` and `16 * 12 = 192 > 57` of the theorem that no convolution of the pieces meets the criterion. The rank `192` of the fourfold products is a floating-point computation and is not certified here |
| `efour_partner_counts` | at `n = 4`, the `128` pieces of `(Z/4)^4` of even sum, `64` of each parity; each has `4, 12, 28, 20` partners of the other parity differing in `1, 2, 3, 4` coordinates, those differing in one coordinate differ there by `2`; the `28` have `D = 16` twenty-four times and `64` four times, `640` in all; `64 * 640 = 40960 > 104 = 7 * 16 - 2 * 4` |
| `efour_run_drop` | with `p` at any rank among the four values, every run from `p` through two selections of distinct multiples back to `p`, the marked step between them a component or a class of `H^1(a, a)`, changes the shift by at most `-4`, a step up by `+1` and a step down by `-7`: the finite core of the lemma on shifts along chains at `n = 4` |
| `efour_two_level_degrees` | with `p` at any rank, every pair of chains `c -> ... -> W`, `V -> ... -> e` through distinct multiples, not both empty, gives `Ext` degree `4 - U + 7D` different from `3` when `c = e`, from `0` when `e` is above `c` and from `8` when `e` is below `c`: the case analysis of the two-shift theorem on `E_0^8` |
| `vandermonde_counts` | the genus of the generalised Fermat curve by Riemann-Hurwitz equals that by adjunction for `d = 2..7`, `N = 2..8`; `r! d^(N(r-1)) = 16, 32, 54, 1536, 162` at the five cases of the fibre count; the units of `Z/d` number `1, 2, 2, 2` for `d = 2, 3, 4, 6`; the balanced characters with six nonzero coordinates and a fixed zero number `20, 140, 1750`, so `70, 490, 6125` orbits in `P^6` and at least `141, 981, 12251` Hodge classes |
| `vg_chain_determinants` | the intersection matrix of a chain of `m` vanishing cycles (`1` above the diagonal, `-1` below) has determinant `1` for `m` even and `0` for `m` odd, `m = 1..7`, so `2g` cycles of the chain form a basis of `H_1` of a hyperelliptic curve of genus `g` |
| `vg_quadric_counts` | `1 + sum_{j > r/2} C(N+1, 2j)` equals one plus the number of subsets of `{0..N}` of even size at least `r + 2`, for `N <= 9`, `r = 2, 4, 6`; it is `N + 2` for two quadrics in `P^N`, `N` even, `2` for a quadric of even dimension, and `2, 8, 30, 94, 257` for `r = 4`, `N = 5..9` |
| `vg_cubic_counts` | `1 + C(N+1, r+2) C(r+2, r/2+1)` equals one plus the number of vectors in `{0,1,2}^(N+1)` with `r + 2` nonzero entries, `r/2 + 1` of them equal to `1`, and sum divisible by `3`, for `N <= 7`, `r = 2, 4`; it is `7, 21, 71` for the Fermat cubics of dimension `2, 4, 6`, `141` for two cubics in `P^6` and `631` for two cubics in `P^8` |
| `vg_triple_signatures` | for `n_1, n_2 < 20` branch points of exponents `1, 2` with `n_1 + 2 n_2` divisible by `3`, the signature `p = (2 n_1 + n_2)/3 - 1`, `q = (n_1 + 2 n_2)/3 - 1` gives back `n_1 = 2p - q + 1`, `n_2 = 2q - p + 1`, the branch data of Achter and Pries, and `p = q` exactly when `n_1 = n_2` |
| `cyclic_base_count` | the vectors of nonzero residues modulo `m = 3, 4, 6` with `5` or `6` coordinates, sum `0`, order `m` and `p, q >= 1`, written as count vectors, number `38` up to sign: the base cases of the proposition on the monodromy of cyclic covers |
| `cyclic_merge_small` | every such vector with `7 <= k <= 8, 11, 10` coordinates at `m = 3, 4, 6` has two entries `u, w` with `u + w != 0` whose merge keeps the order `m` and `p, q >= 1`: a check of the merge lemma, which the paper proves by hand |
| `cyclic_norms` | `x^2 + xy + y^2` is never `2` modulo `4` and is even only for `x, y` even, so `2` is not a norm from `Q(sqrt(-3))` and norms have even `2`-adic valuation; `2 = 1 + 1`, `3 = 1 + 1 + 1` and `4` are norms where the lemma on the discriminant of the new part needs them |
| `cyclic_vg_counts` | `T_d(k)` by a recursion equals the enumeration for `(d, k) = (3, 6), (4, 6), (6, 4)`; `T_4(6) = 141`, `T_6(6) = 1751`, `T_4(8) = 1107`, `T_6(8) = 38165`; the formula of the very general theorem equals a direct count of the characters for `(d, N, r) = (4, 5, 4), (3, 6, 4), (6, 4, 2)` and gives `142, 988, 3950, 1108, 1752, 12258, 38166` |
| `cyclic_nonsplit_example` | `(1, 1, 2, 2, 3, 5, 5, 5)` modulo `6` has sum `0`, order `6`, `p = q = 3` and one coordinate `3`: a character whose abelian sixfold is of non-split Weil type |
| `efour_three_targets` | every piece of `E_0^8` has `18`, `24`, `21` partners of its parity differing in `2`, `3`, `4` coordinates, with groups `H^5` of dimensions `64` (six times) and `16` (twelve times), `16`, and `0`, adding up to `960`; `32 * 960 = 30720` and `40960 - 30720 = 10240 > 104`: the targets of the three-shift theorem |
| `efour_three_degrees` | with `p` at any rank and `delta = 1, 2`, every pair of runs through distinct multiples, not both empty, gives `Ext` degree `3 + delta - U + 7D` different from `3` when `c = e`, from `0` when `e` is above `c` and from `8` when `e` is below `c`: the case analysis of the three-shift theorem |
| `efour_three_spectrum` | the character sums of the weighted Cayley graph of the targets are real and take the values `960, 384, 192, 96, -32, -64, -128, -192`; `64 (960 + 192) / 4 = 18432`, the split `zeta_3 zeta_4 in {1, i}` has weight `18432` in both parities, and `40960 - 18432 = 22528` |


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
`2182 checks passed, 0 failed`.

## Transcript

`axioms.txt` is the unedited output of `lean HodgeObstruction.lean` under
Lean 4.34.0 (x86_64 Linux, commit 293d5d0c): one hundred and thirty-three lines, one per
theorem, one hundred and three reading `does not depend on any axioms` and thirty reading
`depends on axioms: [propext]`, exit status 0, no `sorryAx`. `lake build`
completes with the same report. Each run takes a few minutes.
