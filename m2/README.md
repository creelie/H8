# The Macaulay2 items

## The local products at a double point (item XXIX)

`local_products.m2` recomputes Lemma "Two branches through a point" of the
paper in Macaulay2. Two smooth surfaces `P1 = {x1 = x2 = 0}` and
`P2 = {x3 = x4 = 0}` meet transversally at the origin of `C^4`, and the
candidate object is locally either the ideal `I` of their union (a point that
is not normalised) or the complex `K = [O -> O_{P1} (+) O_{P2}]` (a normalised
point). For each model the script builds a free resolution, the degree `-1`
chain maps `-d/dx_a (d)` that represent the first order deformation along the
translation `d/dx_a`, and their composites, and decides null homotopy.

Run with

    M2 --script local_products.m2

(Macaulay2 1.22 with the package `Complexes`; about ten seconds). The
transcript `local_products.txt` is the unedited output. It reports:

* model `I`: `Ext^2 = k^4`; the products `a_a a_b` vanish exactly for the
  pairs `{1,2}` and `{3,4}` (both directions normal to the same plane); the
  four mixed products are nonzero and span `Ext^2`; the classes anticommute;
  the same pattern is found from the jet modules with `yonedaProduct`;
* model `K`: `Ext^2 = k^2`; the products vanish exactly for the mixed pairs;
  `a_1 a_2` and `a_3 a_4` are nonzero and span `Ext^2`; the classes
  anticommute.

Either pattern is enough for the theorem: the product of two global
translation classes has a nonzero germ at the point, while the compensating
scalar class has none, so the identity `At(F)^2 = -d Theta^2 id` fails and
Markman's candidate does not satisfy the weakened criterion. This item is
independent of the Python suite and is not counted in its checks.

## Where the local obstruction lives (item XXXI)

`lci_products.m2` computes, for ten codimension two germs in `C^4`, the number
of minimal generators, `pdim R/I`, the ranks of a minimal free resolution, and
`Ext^1`, `Ext^2`, `Ext^3` of the ideal against itself; where `Ext^2` is nonzero
it also decides which products of translation classes are nonzero. It uses the
same jet-map conventions as `local_products.m2`.

    M2 --script lci_products.m2

The transcript `lci_products.txt` is the unedited output. It reports that
`Ext^2(I,I) = 0` at all seven Cohen-Macaulay germs, including the fat plane
`(x1,x2)^2` and the cone over the twisted cubic, neither of which is a complete
intersection, and that `Ext^2(I,I) != 0` with nonzero products at all three
germs that are not Cohen-Macaulay: two planes meeting at a point, three planes
meeting pairwise at a point, and a plane with an embedded point. That is the
computation behind the theorem "Cohen-Macaulay supports carry no local
obstruction" of the paper and the remark that follows it.

## Two jet classes on a complex of finite length (item XL)

`finite_length_products.m2` tests the lemma "Two jet classes on a complex of
finite length": over `R = Q[x_1,...,x_c]`, for a bounded complex `M` of free
modules with finite length cohomology and Euler characteristic
`chi(M) = sum (-1)^i length H^i(M)` nonzero, the product of the jet classes
along two independent constant vector fields is nonzero in `Ext^2(M,M)`. The
jet class along `a = sum a_i d/dx_i` is the chain map `-sum a_i d/dx_i (d)`,
as in the other two scripts, and a product vanishes exactly when the composite
is null homotopic.

    M2 --script finite_length_products.m2

The transcript `finite_length_products.txt` is the unedited output: 44 checks.
It first confirms that each input has finite length, then tests every pair of
coordinate directions and one random pair of independent rational directions
on eighteen modules (twelve in two variables, six in three, among them powers
of the maximal ideal, monomial and non-monomial complete intersections, a
Gorenstein algebra of socle degree two and three modules that are not cyclic)
and on three complexes with several cohomology modules; every product is
nonzero. It then shows that the hypothesis on the Euler characteristic is
sharp: on the cone of `J(x2)J(x1) : K -> K[2]`, for `K` the Koszul
resolution of the residue field in two variables, whose two cohomology modules
are both the residue field and whose Euler characteristic is zero, the product
is null homotopic, while on the split complex `k (+) k[1]`, also of Euler
characteristic zero, it is not.

