import IsoGraph.Identities
import IsoGraph.SRG
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Order.Chebyshev

/-!
# Spectral graph theory

The adjacency matrix `CGraph.adjMat` of a graph is real symmetric, so its characteristic
polynomial `CGraph.charpoly` splits over `ℝ` and the *spectrum* `CGraph.spectrum` — the multiset
of roots, equivalently the multiset of `Matrix.IsHermitian.eigenvalues` — has exactly `V` entries.
Both are isomorphism invariants (`charpoly_congr`, `spectrum_congr`), so both descend to
`IsoGraph` at the end of the file.  That last section is mostly written by the `@[toIsoGraph]`
attribute of `IsoGraph/ToIsoGraph.lean`: the four quantities it lifts are named by an
`attribute [toIsoGraph]` line on their congruence, and the facts about them by one on the
`CGraph`-level statement.  What is still written out by hand there is what the attribute cannot
reach — the statements about the products and the complement, and those whose `CGraph` form asks
for a `Nonempty G.V` instance where the quotient wants `0 < G.V`.

## The spectra computed here

| graph        | spectrum                                        |
| ------------ | ----------------------------------------------- |
| `empty n`    | `0` with multiplicity `n`                       |
| `complete n` | `n - 1` once and `-1` with multiplicity `n - 1` |
| `path n`     | `2 cos (π (m + 1) / (n + 1))` for `m < n`       |
| `cycle n`    | `2 cos (2 π m / n)` for `m < n`                 |

The path and the cycle are the two genuinely analytic computations.  For the path the eigenvector
is `sin (π (m + 1) (i + 1) / (n + 1))` and the eigenvalue equation is the product-to-sum identity
`sin_sub_add_sin_add`; the `n` eigenvalues are distinct because `cos` is injective on `[0, π]`, so
`spectrum_eq_of_card_le` pins the whole multiset without any multiplicity bookkeeping.  For the
cycle the adjacency matrix is a circulant, and it is diagonalised outright over `ℂ` by the
discrete Fourier matrix built from `cycZeta n = exp (2 π i / n)`; `charpoly_cycle` then transfers
the factorisation back to `ℝ[X]`.

## How the spectrum behaves under the constructions

* `spectrum_disjUnion` — disjoint union concatenates spectra, because the adjacency matrix is
  block diagonal (`charpoly_disjUnion`).
* `spectrum_tensorProduct` — the tensor (categorical) product multiplies them pairwise, via the
  Kronecker product `adjMat_tensorProduct` and simultaneous diagonalisation
  (`exists_conj_diagonal`).
* `spectrum_cartesianProduct` — the cartesian product *adds* them pairwise, the same way:
  `adjMat_cartesianProduct` is `I ⊗ A H + A G ⊗ I`, and `P₁ ⊗ P₂` diagonalises both summands.
* `spectrum_strongProduct` — the strong product sends `(λ, μ)` to `(1 + λ) (1 + μ) - 1`, because
  `adjMat_strongProduct` is `(A G + I) ⊗ (A H + I) - I`.
* `spectrum_hypercube` — iterating the cartesian product along `hypercube_succ` gives the
  eigenvalues `n - 2 j` of `Q n` with multiplicity `n.choose j`; the induction step is Pascal's
  rule, since `± 1` shifts the eigenvalues of `Q n` into those of `Q (n + 1)`.
* `hasEigenvector_compl` — an eigenvector of `G` orthogonal to the all-ones vector is an
  eigenvector of `Gᶜ` for the eigenvalue `-1 - x`, since `Gᶜ`'s adjacency matrix is `J - I - A`.
  The all-ones vector itself is handled by `hasEigenvector_one_of_isRegularWith`.  For a
  *connected* `k`-regular graph that is the whole story: `eq_of_mulVec_eq_of_isRegularWith` shows
  the `k`-eigenspace is spanned by the all-ones vector, and `spectrum_compl_of_isRegularWith`
  concludes that the spectrum of `Gᶜ` is `n - 1 - k` together with `-1 - x` for each of the
  remaining eigenvalues `x`.

## Trace identities and cospectrality

`sum_spectrum` (the trace is zero) and `sum_sq_spectrum` (the trace of `A ^ 2` is `2 E`) are the
first two moments.  All of them at once: `trace_adjMat_pow` diagonalises every power of `A` with
one conjugation, so `sum_pow_spectrum` identifies the `n`-th moment with the trace of `A ^ n`,
which `adjMat_pow_apply` turns into a count of closed walks
(`sum_pow_spectrum_eq_card_closedWalks`).  At `n = 3` that is the classical triangle count,
`sum_cube_spectrum : ∑ λ ³ = 6 · #triangles`, since a closed walk of length three is a triangle
with a starting point and a direction.  The odd moments of a bipartite graph therefore vanish,
and indeed `spectrum_neg_of_isBipartite` says the whole spectrum is symmetric about zero: the
diagonal sign matrix of the bipartition conjugates `A` into `-A`.
`Cospectral G H` is equality of characteristic polynomials; it is implied by
isomorphism (`Cospectral.of_iso`) and it implies equality of `V` and of `E`, and — by the same
moments — of the triangle count (`Cospectral.cliqueCount_three_eq`) and of the number of closed
walks of every length (`Cospectral.sum_card_closedWalks_eq`).  A graph is
*determined by its spectrum*, `IsDS`, when the converse holds for it.  Two families are proved to
be: `isDS_empty` and `isDS_complete`, the latter by squeezing the degree sequence between
`sum_sq_spectrum` and `SimpleGraph.degree_lt_card_verts`.

## The extreme eigenvalues and the Rayleigh quotient

`lambdaMax` and `lambdaMin` are the largest and smallest eigenvalue of a nonempty graph.
`exists_orthogonal_diagonal` sharpens `exists_conj_diagonal` to an *orthogonal* conjugation, which
turns the quadratic form into a weighted sum of squares in rotated coordinates
(`exists_rotate_quadratic`) and so gives the two halves of the variational principle,
`lambdaMin_mul_le_rayleigh` and `rayleigh_le_lambdaMax`, both attained
(`exists_rayleigh_eq_lambdaMax`).  Test vectors then read off bounds: the all-ones vector gives
`avg_degree_le_lambdaMax` (`2 E ≤ λ_max · V`), and `e u ± e v` across an edge gives
`one_le_lambdaMax` and `lambdaMin_le_neg_one`; the star centred at a vertex of maximum degree
gives `sqrt_maxDeg_le_lambdaMax` (`√Δ ≤ λ_max`).  From the other side,
`abs_le_maxDeg_of_mem_spectrum` bounds every eigenvalue by the maximum degree, by evaluating the
eigenvector equation where the eigenvector is largest, so `λ_max` is trapped between `√Δ` and `Δ`.
Sharper, `λ_max` is the spectral radius: `abs_le_lambdaMax_of_mem_spectrum`, because replacing an
eigenvector by its absolute value keeps the norm and cannot decrease the quadratic form
(`abs_dotProduct_mulVec_le`, nonnegativity of `A`).

The same trick makes the radius monotone in the edge set, `lambdaMax_le_lambdaMax_of_adj`: reading
the absolute value of an eigenvector through a vertex bijection that carries edges to edges only
adds nonnegative terms.  `lambdaMax_le_card_sub_one` caps it at `n - 1`, attained by `Kₙ`.  In the
other extreme, `lambdaMin_eq_neg_lambdaMax_of_isBipartite` says a bipartite graph attains
`-λ_max ≤ λ_min`, since its spectrum is symmetric about zero — the forward half of
`isBipartite_iff_lambdaMin_eq_neg_lambdaMax` below, which is where the converse is proved.  The
two ends of the products (`lambdaMax_disjUnion`, `lambdaMax_cartesianProduct`,
`lambdaMax_tensorProduct`, `lambdaMax_strongProduct` and their
`lambdaMin` counterparts) and of the named families (`lambdaMax_complete`, `lambdaMax_cycle`,
`lambdaMax_path` and the rest, down to the strongly regular ones — `lambdaMax_petersen`,
`lambdaMax_rook`, `lambdaMax_paley` — and `lambdaMax_hypercube` at the very end of the file) are
read off the spectra computed above.  The one family that is not is the join: outside the regular
case no adjacency spectrum of a join is on file, so `lambdaMax_join_of_isRegularWith` computes the
radius of `G ∇ H`, for `k`-regular `G` on `n` vertices and `l`-regular `H` on `m` vertices,
directly from an explicit positive eigenvector.  `adjMat_mulVec_join` is that eigenvector
equation: a vector constant on each side is an eigenvector as soon as `k a + m b = λ a` and
`n a + l b = λ b`, which
happens exactly at the two roots of `(x - k) (x - l) = n m`.  The larger one,
`(k + l + √((k - l) ² + 4 n m)) / 2`, is the spectral radius, and the smaller one is an eigenvalue
too, so `lambdaMin_join_of_isRegularWith_le` bounds the *bottom* of the join's spectrum — an
inequality, since each factor keeps its own eigenvalues on the vectors that sum to zero on each
side.  The cone `K₁ ∇ G` is the case `l = 0`, `m = 1`
(`lambdaMax_join_complete_one`, `lambdaMin_join_complete_one_le`), and the wheel is the cone over
a cycle, giving `lambdaMax_wheel = 1 + √(n + 1)` and `lambdaMin_wheel_le`; that last one is
strict for an even rim, which contributes a smaller `-2`.

The *equality* case is `mulVec_eq_of_rayleigh_eq_lambdaMax`: a vector attaining the maximum is an
eigenvector, since in rotated coordinates the quotient is a weighted average of the eigenvalues.
Applied to the all-ones vector this says that a graph whose largest eigenvalue equals its average
degree is regular (`isRegularWith_of_two_mul_E_eq`), and hence that **regularity is determined by
the spectrum**, `Cospectral.isRegularWith`: the order, the size and `lambdaMax` are all read off
the spectrum, and together they force every degree to be `k`.

The best-known application of the variational principle is **Hoffman's ratio bound**,
`card_mul_sub_lambdaMin_le`: in a `k`-regular graph an independent set `S` gives the test vector
`n · 1_S - |S| · 1`, which is orthogonal to the all-ones vector and spans no edge, so its
Rayleigh quotient is `-k |S| ² / n` and `|S| (k - λ_min) ≤ n (-λ_min)`.  For the triangular graph
`T(n)`, where `k = 2 (n - 2)` and `λ_min = -2`, that is the matching bound
`two_mul_indepNum_triangular_le : 2 α ≤ n`.  Since every colour class is independent, `n ≤ χ α`,
and the ratio bound turns into Hoffman's bound on the chromatic number,
`sub_lambdaMin_le_chromNum_mul : k - λ_min ≤ χ (-λ_min)`, the product form of
`χ ≥ 1 - λ_max / λ_min`.  The Petersen graph is the standard illustration: it is triangle-free,
so no clique forces its chromatic number, but `3 - (-2) ≤ χ · 2` already gives `χ ≥ 3`.

## The diameter

The spectrum bounds the diameter from above, `diameter_lt_card_toFinset_spectrum`: a graph with
`k` *distinct* eigenvalues has diameter at most `k - 1`.  `minSpecPoly`, the product of `X - λ`
over the distinct eigenvalues, annihilates the adjacency matrix — conjugate to the diagonal form
and it becomes `diagonal (p ∘ λ)` — so `A ᵏ` is a combination of the lower powers
(`sum_coeff_smul_adjMat_pow`).  Read that relation at the entry `(u, w)` for a pair at distance
exactly `k`, which `exists_dist_eq` produces by cutting a shortest walk: the walk counts of
`adjMat_pow_apply` make the top term positive and every lower term zero.

## Few distinct eigenvalues

Counting the distinct eigenvalues from the bottom is the converse of the strongly regular story.
One means no edges at all, `card_toFinset_spectrum_eq_one_iff`; two means complete,
`card_toFinset_spectrum_eq_two_iff`, since the same argument makes `A - r` a constant matrix and
the vanishing diagonal then pins the constant to `1`;
and with three `exists_isSRGWith_of_card_toFinset_spectrum_eq_three` says a connected regular
graph is strongly regular.  The converse is `card_toFinset_spectrum_eq_three_of_isSRGWith`: at
most three because every eigenvalue but the degree is a root of the same quadratic, at least three
because a non-adjacent pair is at distance `2`, which is the same distance-two argument that
`IsSRGWith.diameter_eq_two` runs by hand.  Putting the two together,
`Cospectral.exists_isSRGWith` says that **strong regularity is determined by the spectrum**.
Factor `minSpecPoly` as `(X - k) (X - r) (X - s)` — the degree is an eigenvalue, so it is one of
the three — and `aeval_minSpecPoly` turns that into `(A - k) (A - r) (A - s) = 0`.  Hence every
column of `M = (A - r) (A - s)` is a `k`-eigenvector, and since a connected regular graph has `k`
as a *simple* eigenvalue with the all-ones eigenvector, every column is constant; `M` is
symmetric, so all the columns share their constant and `M = t J`
(`exists_forall_eq_of_mul_eq_smul`).  Off the diagonal `M = A ² - (r + s) A`, and
`adjMat_sq_apply` reads `A ²` as a count of common neighbours: adjacent pairs have `t + r + s` of
them and non-adjacent pairs `t`.  Together with `spectrum_isSRGWith` in the other direction,
strong regularity of a connected regular graph *is* the condition "three distinct eigenvalues".

## The energy

`energy` is `∑ |λ|`, the graph energy of chemical graph theory.  Because the eigenvalues sum to
zero, the positive ones carry exactly half of it (`energy_eq_two_mul_sum_posPart`), which puts
`2 λ_max` underneath it (`two_mul_lambdaMax_le_energy`); Cauchy–Schwarz against the second moment
`∑ λ ² = 2 |E|` puts `√(2 |E| n)` on top, **McClelland's bound**, `energy_le_sqrt`.  Expanding
`(∑ |λ|) ²` into its diagonal and off-diagonal halves and using both moments at once puts
`2 √|E|` underneath as well (`two_mul_sqrt_le_energy`), so the energy is pinned into
`[2 √|E|, √(2 |E| n)]`.  It adds over disjoint unions and multiplies over tensor products
(`energy_disjUnion`, `energy_tensorProduct`), it is a cospectral invariant, and it vanishes
exactly on the edgeless graphs (`energy_eq_zero_iff`, again by the second moment).  The named
values are `energy_complete` (`2 (n - 1)`, where the `2 λ_max` bound is tight), `energy_bipartite`
(`2 √(m n)`), `energy_star` (`2 √n`) and `energy_petersen` (`16`).

## The Laplacian

`lapMat` is `L = D - A`, the degree matrix minus the adjacency matrix, and `lapSpectrum` its
multiset of eigenvalues.  Mathlib supplies the two facts that make it useful: `L` is positive
semidefinite, so the eigenvalues are nonnegative (`nonneg_of_mem_lapSpectrum`), and `L x = 0`
exactly when `x` is constant on components.  The all-ones vector is always in the kernel
(`zero_mem_lapSpectrum`), the trace gives `sum_lapSpectrum` — the eigenvalues add up to `2 |E|`,
not to `0` as the adjacency ones do — and rank-nullity turns the kernel description into
`count_zero_lapSpectrum`: **the multiplicity of `0` is the number of components**, so
`count_zero_lapSpectrum_eq_one_iff` reads connectedness straight off the Laplacian spectrum,
with no regularity hypothesis.  For a `k`-regular graph the two spectra are the same information,
`mem_lapSpectrum_iff_of_isRegularWith`: `L = k I - A`, so the Laplacian eigenvalues are `k - λ`.
Conjugating the spectral decomposition of `A` by the same unitary upgrades that to an equality of
multisets, `lapSpectrum_of_isRegularWith`, which turns every regular spectrum already computed
here into a Laplacian one: `lapSpectrum_complete` (`0` once and `n + 1` with multiplicity `n`),
`lapSpectrum_cycle` (`2 - 2 cos (2 π m / n)`) and `lapSpectrum_hypercube` (`2 j` with
multiplicity `n.choose j`).  A disjoint union concatenates Laplacian spectra just as it
does adjacency ones (`lapSpectrum_disjUnion`), which is the component count again, one summand
at a time.

`lapSpectrum_bipartite_self` adds the balanced complete bipartite graph, whose Laplacian
eigenvalues are `0`, `2 (n + 1)` and `n + 1` with multiplicity `2 n`.

`lapMat_compl` is the complement identity `L(G) + L(Ḡ) = n I - J`, and on a vector summing to
zero — where every non-constant Laplacian eigenvector lives — `lapMat_compl_mulVec` turns that
into the eigenvalue statement `μ ↦ n - μ`.  Upgrading that to multisets is
`lapSpectrum_compl_of_isConnected`: **the complement of a connected graph has Laplacian spectrum
`0` together with `n - μ` for every other `μ`.**  A graph and its complement cannot both be
disconnected, so applying the theorem to whichever of the two is connected removes the hypothesis
altogether, `lapSpectrum_compl`.  The proof orthogonally diagonalises `L`
(`exists_orthogonal_lap_diagonal`), notes that on a connected graph the kernel is spanned by the
all-ones vector so exactly one column of the eigenbasis is constant, and computes that in those
coordinates `J` becomes `n` times the corresponding diagonal idempotent; `lapSpectrum_eq_of_conj`
then reads the complement's spectrum off the resulting diagonal.  Complementing the disjoint union
of two complete graphs gives every complete bipartite graph at once, `lapSpectrum_bipartite`
(`0`, `m + n + 2`, `n + 1` with multiplicity `m` and `m + 1` with multiplicity `n`), and the star
`lapSpectrum_star` is its `m = 0` case — worth recording separately because the star is *not*
regular, so `lapSpectrum_of_isRegularWith` says nothing about it.  Complementing a disjoint union
in general is `lapSpectrum_join`: **a join has Laplacian spectrum `0`, the order `n + m`, and each
factor's remaining eigenvalues shifted by the order of the other factor.**  Both ends of it are
immediate: `lapLambdaMax_join` is the order, and `algConn_join` is
`min (a (G) + m, a (H) + n)` — the order itself is never the smallest, because `a (G) ≤ n`.
Read backwards through `spectrum_of_isRegularWith` this also settles the *adjacency* spectrum of a
join, in the one case where the join is regular: if `k + m = n + l` then `G ∇ H` is regular of
that degree and `spectrum_join_of_isRegularWith` says its spectrum is that degree, `k - n`, and
every other eigenvalue of each factor **unchanged** — the shifts of the Laplacian statement cancel
against the degree.  The two new eigenvalues are the two roots of `(x - k) (x - l) = n m` from
`adjMat_mulVec_join`, so this is the case where `lambdaMax_join_of_isRegularWith` and
`lambdaMin_join_of_isRegularWith_le` are both visibly sharp at the ends.

The other non-regular family worth having is the path, `lapSpectrum_path`: the numbers
`2 - 2 cos (π m / n)`.  The eigenvectors are the discrete cosines `cos (π m (j + 1/2) / n)`, whose
half-integer offset is exactly what makes them *reflect* at the two ends — `path_lapMat_mulVec`
says the Laplacian is the second difference for any `g` with `g 0 = g 1` and `g (n + 1) = g n`,
which is the boundary condition a degree-one endpoint imposes, where `path_adjMat_mulVec` needed
`g` to vanish there instead.  `lapSpectrum_eq_of_card_le`, the Laplacian twin of
`spectrum_eq_of_card_le`, then turns `n` distinct eigenvalues into the whole multiset.

The moments of the Laplacian spectrum are the traces of the powers of `L`, `sum_pow_lapSpectrum`,
by the same one-conjugation argument as for the adjacency matrix (`trace_lapMat_pow`).  The second
one is `sum_sq_lapSpectrum`: `∑ μ ² = 2 E + ∑ d (i) ²`, because `L ² = D ² - D A - A D + A ²` and
the two cross terms have zero diagonal — a loopless graph has `A i i = 0`.

Two bounds come out of the same picture:
`le_two_mul_maxDeg_of_mem_lapSpectrum` (`μ ≤ 2 Δ`, the largest-coordinate argument again) and
the sharp `le_card_of_mem_lapSpectrum` (`μ ≤ n`, attained by the complete graph), which reads
`n - μ` off the complement and uses that Laplacian eigenvalues are nonnegative.

`algConn` is the **algebraic connectivity**, the second-smallest Laplacian eigenvalue: the
infimum of `lapSpectrum.erase 0`, taken in `ℝ` so that the one-vertex graph gets `sInf ∅ = 0` by
the usual convention.  On two or more vertices it is attained (`algConn_mem_erase`), and
`count_zero_lapSpectrum` turns it into a connectivity test: `algConn_pos_iff` says it is positive
exactly for a connected graph, because a second `0` survives the erasure precisely when there is
a second component (`algConn_disjUnion`).  It is squeezed between `0` and the order
(`algConn_nonneg`, `algConn_le_card`), the upper end attained by `algConn_complete`.  Every
Laplacian spectrum computed above gives a value, through `algConn_eq_of_isLeast`:
`algConn_bipartite` (the smaller side of `K_{m,n}`), `algConn_star` (always `1`),
`algConn_path` (`2 - 2 cos (π / n)`, shrinking like `1 / n ²`) and, at the `IsoGraph` level where
`lapSpectrum_cycle` lives, `algConn_cycle` (`2 - 2 cos (2 π / n)`, four times the path's value:
closing the path into a cycle doubles the Fiedler frequency).

The variational side is the Laplacian copy of the Rayleigh section above.  What replaces
`⟪v, A v⟫` is `two_mul_lap_quadratic`: **`2 ⟪v, L v⟫ = ∑ i ∑ j A i j (v i - v j) ²`**, the sum of
squared differences across the edges — the identity behind positive semidefiniteness and behind
every bound that follows.  `exists_rotate_lap_quadratic` rotates the same form into a weighted
sum of squares, so `lap_rayleigh_le_lapLambdaMax` bounds it by `μ_max ⟪v, v⟫`, and a test vector
turns that into a lower bound on `μ_max`.  The good one is `Δ` at a vertex of maximum degree,
`-1` at each of its neighbours and `0` elsewhere: the `Δ` edges at the centre contribute
`(Δ + 1) ²` each, every other edge contributes something nonnegative, and the norm is `Δ (Δ + 1)`,
so `maxDeg_add_one_le_lapLambdaMax` gives **`Δ + 1 ≤ μ_max`**.  Together with
`lapLambdaMax_le_two_mul_maxDeg` that pins `μ_max` between `Δ + 1` and `2 Δ`, both attained: the
star at the bottom and any bipartite regular graph, `lapLambdaMax_hypercube` say, at the top.

Reflecting `Δ + 1 ≤ μ_max` in the complement turns it into a bound at the *other* end of the
spectrum, and that bound is **Fiedler's**: `μ_max (Ḡ) = n - a (G)` and `Δ (Ḡ) = n - 1 - δ (G)`,
so `algConn_le_minDeg` reads `a (G) ≤ δ (G)`.  Its hypothesis is that `Ḡ` has an edge, i.e. that
`G` is not complete — and it has to be, since `K_n` has `a = n` and `δ = n - 1`.  Weakening the
conclusion just enough to absorb that one case gives the textbook statement,
`card_sub_one_mul_algConn_le_card_mul_minDeg` (`(n - 1) a ≤ n δ`), or in its usual divided form
`algConn_le_div_mul_minDeg` (`a ≤ n / (n - 1) · δ`), an equality exactly at the complete graph.

The small end has a variational principle of its own, and it is the one that makes `algConn` a
usable quantity: `algConn_mul_le_lap_quadratic` says `a (G) ⟪v, v⟫ ≤ ⟪v, L v⟫` for every `v`
summing to zero.  The proof is `exists_rotate_lap_quadratic_of_sum_eq_zero`, which sharpens the
rotation above by killing the kernel coordinates — on a connected graph an eigenvector for `0` is
constant (`lapMat_mulVec_eq_zero_iff`), so a vector orthogonal to the constants has no component
along it, and what is left are eigenvalues `≥ a (G)`.  A disconnected graph has `a (G) = 0` and
the statement degenerates to `lap_quadratic_nonneg`.  Feeding it the difference of two basis
vectors gives `two_mul_algConn_le_degree_add_degree`: **`2 a (G) ≤ d (u) + d (v)` for any two
non-adjacent `u`, `v`**, which sharpens Fiedler's bound whenever the minimum-degree vertex has a
non-neighbour of small degree.  The test vector that made `algConn` famous is the one built from a
cut: `|Sᶜ|` on `S` and `-|S|` off it, whose quadratic form is `n ²` per crossing edge and whose
squared norm is `n |S| |Sᶜ|`.  What comes out is `algConn_mul_card_mul_card_compl_le`,
**`a (G) |S| |Sᶜ| ≤ n · e (S, Sᶜ)`** — the Fiedler value is a lower bound on edge expansion, and
the reason a spectral gap certifies that a graph cannot be cut cheaply.  Restricting to the small
side of the cut, `2 |S| ≤ n`, makes `|Sᶜ| ≥ n / 2` and the order cancels:
`algConn_mul_card_le_two_mul_cut` is the isoperimetric form **`a (G) |S| ≤ 2 e (S, Sᶜ)`**, a
lower bound on the cut that does not mention the order at all.

`lapLambdaMax` is the other end of the same spectrum, the largest Laplacian eigenvalue, taken as a
supremum for the same reason `algConn` is an infimum.  It is bounded by
`lapLambdaMax_le_card` and `lapLambdaMax_le_two_mul_maxDeg` from above and by the average degree
from below (`two_mul_E_le_card_mul_lapLambdaMax`, since the `n` eigenvalues sum to `2 E`); the
matching averaging bound at the small end is `card_sub_one_mul_algConn_le_two_mul_E`.  What ties
the two ends together is the complement: reflecting the spectrum in `n` sends the largest
eigenvalue to the smallest nonzero one and back, `algConn_compl` (`a (Ḡ) = n - μ_max (G)`) and
`lapLambdaMax_compl` (`μ_max (Ḡ) = n - a (G)`).  It vanishes only in the trivial case
(`lapLambdaMax_eq_zero_iff`, `μ_max = 0 ↔ E = 0`), a disjoint union takes the larger of the two
(`lapLambdaMax_disjUnion`, where `algConn_disjUnion` takes neither), and for a `k`-regular graph
the two spectra are reflections, `lapLambdaMax_of_isRegularWith` (`μ_max = k - λ_min`).
So `lapLambdaMax_complete`, `lapLambdaMax_star` and `lapLambdaMax_bipartite`, all equal to the
order, are `algConn`'s vanishing values — each of the three is a join, so each has a disconnected
complement.  `lapSpectrum_wheel` runs the join formula
on `W_n = K₁ ∇ C_n`, which adds a fourth: the hub raises every rim eigenvalue by one, so
`algConn_wheel` is `3 - 2 cos (2 π / n)` — one more than the rim's — and `lapLambdaMax_wheel` is
the order again.  The hypercube shows the two ends pulling apart: `lapLambdaMax_hypercube` is
`2 n`, twice the degree and so the extreme case of `lapLambdaMax_le_two_mul_maxDeg`, while
`algConn_hypercube` is `2` for every `n ≥ 1` — the Fiedler value does not degrade as the order
doubles, in contrast to the cycle's `Θ (1 / n ²)`.  Its proof uses
`zero_notMem_erase_of_isConnected`, which reads "connected ⇒ the erasure removes the only zero"
straight off `count_zero_lapSpectrum`.  The path and the even cycle read the *top* of the same
cosine ranges that `algConn_path` and `algConn_cycle` read the bottom of: `lapLambdaMax_path` is
`2 - 2 cos (π n / (n + 1))`, climbing to `4` without reaching it, and `lapLambdaMax_cycle_even`
is exactly `4 = 2 Δ`, because `m = n / 2` is an integer only in the even case.  The odd case is
`lapLambdaMax_cycle_odd`, `2 + 2 cos (π / n)`, one reflection away from `lambdaMin_cycle_odd`.

The cartesian product behaves for the Laplacian exactly as it does for the adjacency matrix:
`lapMat_cartesianProduct` is `L G ⊗ I + I ⊗ L H`, the two summands commute and are diagonalised
by the Kronecker product of the two eigenbases, and `lapSpectrum_cartesianProduct` is the
multiset of all sums `μ + ν`.  Both ends follow: `lapLambdaMax_cartesianProduct` adds
(`μ_max (G □ H) = μ_max (G) + μ_max (H)`) and `algConn_cartesianProduct` takes the minimum
(`a (G □ H) = min (a (G), a (H))`), because `a (G) + 0` and `0 + a (H)` are both available and
every other nonzero sum dominates one of them.  No connectivity hypothesis is needed for the
minimum: a disconnected factor sends both sides to `0`.  Since `Q_n = Q_{n-1} □ K₂`, that
recovers `algConn_hypercube` and `lapLambdaMax_hypercube` by induction.

The strongly regular graphs come along for free, since they are regular with a three-point
spectrum `k > r > s`.  `lapSpectrum_of_spectrum_eq` reflects such a spectrum in `k`, and the two
ends are then immediate: `algConn_of_spectrum_eq` is `k - r` and `lapLambdaMax_of_spectrum_eq` is
`k - s`, so **on a strongly regular graph both extreme Laplacian eigenvalues are read off the
two restricted adjacency eigenvalues**, with the larger one governing connectivity.  Every named
family computed above gets its Laplacian data this way: `lapSpectrum_petersen` (`0`, `2` five
times, `5` four times, so `algConn_petersen = 2` and `lapLambdaMax_petersen = 5`),
`lapSpectrum_cocktailParty`, `lapSpectrum_rook`, `lapSpectrum_triangular` and, the irrational
case, `lapSpectrum_paley` (`(q ∓ √q) / 2`, each with multiplicity `(q - 1) / 2`).  Two of them
double as checks on the product formulas: `algConn_rook` is `n` and `lapLambdaMax_rook` is `2 n`,
which is what `algConn_cartesianProduct` and `lapLambdaMax_cartesianProduct` give for
`K_n □ K_n`.

`LapCospectral` is the Laplacian analogue of `Cospectral`, equality of `lapCharpoly` and hence
of `lapSpectrum` (`lapCospectral_iff_lapSpectrum_eq`).  It sees the order, the size and — through
`count_zero_lapSpectrum` — the number of components (`LapCospectral.numComponents_eq`), so
`LapCospectral.isConnected` needs no regularity where `Cospectral.isConnected` does.  The second
moment adds the sum of squared degrees (`LapCospectral.sum_sq_degrees_eq`), and with the first
moment that is enough to pin the whole degree sequence of a regular graph's partner:
`∑ (d (i) - k) ² = ∑ d (i) ² - 2 k ∑ d (i) + n k ²` vanishes, so `LapCospectral.isRegularWith`
makes **regularity a Laplacian spectral invariant**, where the adjacency twin
`Cospectral.isRegularWith` has to route through `lambdaMax`.  For regular
graphs the adjacency notion is the stronger one, `Cospectral.lapCospectral`; without regularity
it is not, and `not_lapCospectral_star_four` is the witness.

## Line graphs

`transpose_mul_incMat` factors the line graph through the incidence matrix `incMat`, as
`Bᵀ B = A(L G) + 2 I`.  Since `Bᵀ B` is positive semidefinite this gives
`neg_two_le_of_mem_spectrum_lineGraph`: no line graph has an eigenvalue below `-2`, the other
half of the reason ADE turns up here.  The bound is attained whenever `B` has a kernel, which it
does as soon as there are more edges than vertices (`neg_two_mem_spectrum_lineGraph`).

For a `k`-regular graph the two products of `B` with its transpose can be played off against each
other: `incMat_mul_transpose_of_isRegularWith` is the companion factorisation `B Bᵀ = A + k I`, and
Sylvester's determinant identity (`Matrix.charpoly_mul_comm_of_le`) equates the two characteristic
polynomials up to a power of `X`.  Feeding both through `charpoly_adjMat_add_smul_one`, which says
an identity shift `A + c I` shifts every eigenvalue by `c`, gives the whole spectrum at once in
`spectrum_lineGraph_of_isRegularWith`: each eigenvalue `λ` of `G` becomes `λ + k - 2`, and the
`|E| - |V|` leftover eigenvalues are all `-2`.  A cycle has as many edges as vertices and `k = 2`,
so nothing moves and nothing is left over (`spectrum_lineGraph_cycle`, cospectrality standing in
for the isomorphism `L(Cₙ) ≅ Cₙ`); `spectrum_lineGraph_petersen` is the other extreme, where the
five surplus edges of the Petersen graph produce five copies of `-2`.

## Strongly regular graphs

`sq_eq_of_isSRGWith` is the identity `A ^ 2 = k I + ℓ A + μ (J - I - A)` read off on an
eigenvector orthogonal to the all-ones vector; `eigenvalue_eq_of_isSRGWith` solves the resulting
quadratic, so the spectrum of a strongly regular graph consists of `k` together with the two
roots `((ℓ - μ) ± √((ℓ - μ) ^ 2 + 4 (k - μ))) / 2`.

The multiplicities come next.  `sq_degree_of_isSRGWith` is the parameter identity
`k ^ 2 = k + ℓ k + μ (n - 1 - k)`, obtained by applying that matrix identity to the all-ones
vector (this avoids the truncated subtraction in Mathlib's `param_eq`), and
`spectrum_isSRGWith` turns it into the whole spectrum: for `μ > 0` and distinct roots `r ≠ s`
of `x ^ 2 = (ℓ - μ) x + (k - μ)`, the spectrum is `k` once together with `r` and `s` with
multiplicities `f` and `g` fixed by the two trace conditions `f + g + 1 = n` and
`k + f r + g s = 0`.  That the degree occurs exactly *once* is the content of the parameter
identity in the form `(k - r) (k - s) = n μ`; no connectivity or eigenspace-dimension theory is
needed, only `∑ λ = 0` and `∑ λ ^ 2 = n k`.  `spectrum_petersen` is the example:
`3, 1⁵, (-2)⁴`.  The same three lines run over the classical families, whose roots are integers
for every parameter: `spectrum_cocktailParty` gives `2n - 2, 0ⁿ, (-2)ⁿ⁻¹`, `spectrum_rook` gives
`2n - 2, (n - 2)^(2n-2), (-2)^((n-1)²)`, and `spectrum_triangular` gives
`2n - 4, (n - 4)ⁿ⁻¹, (-2)^(C(n,2) - n)` — the last two both line graphs, hence both bottoming
out at `-2`.

That every one of those roots came out an integer is no accident: it is the **integrality
condition**, `int_or_conference_of_isSRGWith`.  Eliminating `s` from the trace conditions leaves
`(f - g) r = -(k + g (ℓ - μ))`, so as soon as the two multiplicities differ, `r` is *rational* —
and a rational eigenvalue of a graph is an integer, since `charpoly` is a monic integer polynomial
(`charpoly_eq_map_int`, `isIntegral_of_mem_spectrum`) and `ℤ` is integrally closed in `ℚ`
(`exists_intCast_eq_of_ratCast_mem_spectrum`).  The excluded case `f = g` is exactly
`2 k + (n - 1) (ℓ - μ) = 0`, the conference graphs — the Paley graphs are the standard examples.
`isSquare_discrim_or_conference_of_isSRGWith` restates it as the textbook dichotomy: either the
discriminant `(ℓ - μ) ² + 4 (k - μ)` is a perfect square, or the parameters are of conference type.
`spectrum_paley` is the conference case worked out: for a prime `q = 4t + 1` the Paley graph has
spectrum `2t, ((-1 + √q) / 2)^(2t), ((-1 - √q) / 2)^(2t)`, and the equal multiplicities are forced
by the trace condition itself, which reads `(f - g) √q = 0`.

`degree_of_isSRGWith_moore` is the payoff: run the dichotomy on the parameters
`srg(k² + 1, k, 0, 1)` of a Moore graph of diameter `2`.  The conference branch collapses to
`k = 2`; on the other branch
`c = √(4k - 3)` is a positive integer and eliminating `k` from the trace condition gives
`16 (f - g) c = c⁴ - 2 c² - 15`, so `c ∣ 15` and `k ∈ {3, 7, 57}`.  This is the **Hoffman–Singleton
theorem**, and its four degrees are the pentagon, the Petersen graph, the Hoffman–Singleton graph
and the graph on `3250` vertices nobody has found or ruled out.

## The Smith family and ADE

`IsSmith G` says `2` is the largest eigenvalue of `G` and `IsSubcritical G` says every eigenvalue
is below `2`; `lambdaMax`, the largest eigenvalue of a nonempty graph, restates both as
`isSmith_iff_lambdaMax` and `isSubcritical_iff_lambdaMax`.  Smith's theorem classifies the
connected graphs of each kind: the subcritical ones are the simply-laced Dynkin diagrams
`Aₙ Dₙ E₆ E₇ E₈`, and the critical ones are their affine extensions `Ãₙ D̃ₙ Ẽ₆ Ẽ₇ Ẽ₈`.  The
classification itself is not formalised, but every diagram in it is: `isSubcritical_path`
(`Aₙ`), `isSmith_cycle` (`Ãₙ`), the parametric families
`isSubcritical_dynkinD` and `isSmith_affineD` (`Dₙ` and `D̃ₙ` for every `n ≥ 4`), and the six
exceptional diagrams `dynkinE6`, `dynkinE7`, `dynkinE8` with their affine versions.

The tool is `le_of_mulVec_le`: if some strictly positive `w` satisfies `A w ≤ c w` pointwise then
every eigenvalue is at most `c`, by looking at the vertex maximising `u i / w i`.  Taking `w` to
be the marks of the affine diagram gives the bound for both the affine diagram (with equality —
the marks are literally the Perron eigenvector, `mulVec_affineE8` and friends) and the finite one
it extends.  Strictness for the finite diagrams comes from `two_notMem_spectrum_*`: the linear
system `A v = 2 v` forces `v = 0`, which is the nonsingularity of the Cartan matrix.

## Perron–Frobenius and connectedness of a regular graph

`exists_orthonormal_eigenbasis` packages the orthogonal diagonalisation as a family of unit
eigenvectors in which every vector expands, and `exists_smul_of_count_spectrum_eq_one` reads off
the consequence of an eigenvalue occurring once: its eigenspace is a line, since the expansion of
an eigenvector for `c` is supported on the indices carrying `c`.

For the *largest* eigenvalue of a connected graph the line comes for free, without knowing the
multiplicity in advance.  Because `A` has nonnegative entries, `⟪|v|, A |v|⟫ ≥ ⟪v, A v⟫` while the
norms agree, so `|v|` also attains the maximum of the Rayleigh quotient and is an eigenvector
(`mulVec_abs_of_mulVec_eq_lambdaMax`).  A nonnegative eigenvector of a connected graph is
everywhere positive (`pos_of_mulVec_eq_of_nonneg`): a zero coordinate makes a sum of nonnegative
terms vanish, so the zero spreads along every walk.  That gives the positive Perron vector `w`
(`exists_pos_mulVec_eq_lambdaMax`), and subtracting from any other eigenvector the largest multiple
of `w` that fits under it leaves a nonnegative eigenvector with a zero coordinate, hence zero
(`exists_smul_of_mulVec_eq_lambdaMax`).  Two orthonormal eigenvectors for `λ_max` would then be
nonzero multiples of the same `w`, so `λ_max` is simple: `count_spectrum_lambdaMax_eq_one`.

The Perron vector also settles the equality case of `lambdaMax_le_maxDeg`: at a vertex where `w` is
largest the eigenvector equation squeezes `Δ w x = ∑_{y ∼ x} w y ≤ deg x · w x ≤ Δ w x`, so that
vertex has full degree and `w` is largest at all of its neighbours too; connectedness makes `w`
constant and the equation then reads `deg x = Δ` everywhere.  So a connected graph has
`λ_max = Δ` exactly when it is regular (`lambdaMax_eq_maxDeg_iff`).

For a `k`-regular graph `λ_max = k`, so that pins connectedness down,
`isConnected_iff_count_spectrum_eq_one`: if the graph is disconnected the indicator of a component
is a second eigenvector for `k`, not a multiple of the all-ones vector.  Combined
with `Cospectral.isRegularWith` this makes connectedness spectral as well: `Cospectral.isConnected`.

## Bipartiteness of a connected graph

`spectrum_neg_of_isBipartite` gives one direction — a bipartite graph has a symmetric spectrum, so
`-λ_max` is an eigenvalue of it.  The converse needs connectedness
(`isBipartite_of_neg_lambdaMax_mem_spectrum`).  From `A v = -λ_max v`, `|v|` attains the maximum of
the Rayleigh quotient (its quadratic form is at least `|⟪v, A v⟫| = λ_max ⟪v, v⟫`), so it is a
positive Perron vector; the two quadratic forms then differ by `∑ A x y (|v x||v y| + v x v y)`,
a sum of nonnegative terms equal to zero, so `v x · v y < 0` on every edge and the sign of `v` is a
proper `2`-colouring.  Since `λ_min ≥ -λ_max` always (`neg_lambdaMax_le_lambdaMin`), this reads
`isBipartite_iff_lambdaMin_eq_neg_lambdaMax`, and for a `k`-regular graph
`isBipartite_iff_lambdaMin_eq` (`λ_min = -k`); with `Cospectral.isConnected` it makes bipartiteness
spectral for connected regular graphs (`Cospectral.isBipartite`).

## Not proved here

The full multiset spectrum of a complement (which needs simultaneous diagonalisation with `J`),
`IsDS` for the path and the cycle (which needs the converse direction of Smith's theorem), and
Smith's theorem itself — that the list above is complete.
-/

set_option autoImplicit false

open Polynomial Matrix
open scoped Classical Kronecker

namespace CGraph

/-- The adjacency matrix of `G`, over `ℝ`. -/
noncomputable def adjMat (G : CGraph) : Matrix G.V G.V ℝ := G.toSimple.adjMatrix ℝ

theorem adjMat_apply (G : CGraph) (i j : G.V) :
    G.adjMat i j = if G.Adj i j then 1 else 0 := by
  simp [adjMat, SimpleGraph.adjMatrix_apply]

theorem isHermitian_adjMat (G : CGraph) : G.adjMat.IsHermitian :=
  Matrix.ext fun i j ↦ by
    simp [adjMat, Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, G.symm i j]

/-- The characteristic polynomial. -/
noncomputable def charpoly (G : CGraph) : ℝ[X] := G.adjMat.charpoly

theorem charpoly_eq_matrix_charpoly (G : CGraph) [inst : DecidableEq G.V] :
    G.charpoly = G.adjMat.charpoly :=
  congrArg (fun d ↦ @Matrix.charpoly ℝ _ G.V d _ G.adjMat) (Subsingleton.elim _ _)

/-- The eigenvalues, indexed by the vertices. -/
noncomputable def eigenvalues (G : CGraph) : G.V → ℝ := G.isHermitian_adjMat.eigenvalues

/-- The spectrum: the multiset of eigenvalues, with multiplicity. -/
noncomputable def spectrum (G : CGraph) : Multiset ℝ := G.charpoly.roots

/-! ## Isomorphism invariance -/

theorem adjMat_congr {G H : CGraph} (i : G ≃cg H) :
    G.adjMat = Matrix.reindex i.toEquiv.symm i.toEquiv.symm H.adjMat := by
  ext x y
  simp [adjMat_apply, Matrix.reindex_apply, Matrix.submatrix_apply, i.adj_eq x y]

@[toIsoGraph]
theorem charpoly_congr {G H : CGraph} (i : G ≃cg H) : G.charpoly = H.charpoly := by
  classical
  rw [charpoly_eq_matrix_charpoly, charpoly_eq_matrix_charpoly, adjMat_congr i,
    Matrix.charpoly_reindex]

@[toIsoGraph]
theorem spectrum_congr {G H : CGraph} (i : G ≃cg H) : G.spectrum = H.spectrum := by
  rw [spectrum, spectrum, charpoly_congr i]

/-! ## The size and the degree of the spectrum -/

theorem spectrum_eq_map (G : CGraph) :
    G.spectrum = Finset.univ.val.map G.eigenvalues := by
  simpa [spectrum, charpoly, Function.comp_def]
    using G.isHermitian_adjMat.roots_charpoly_eq_eigenvalues

@[simp, toIsoGraph] theorem card_spectrum (G : CGraph) :
    Multiset.card G.spectrum = Fintype.card G.V := by
  simp [spectrum_eq_map, Finset.card_univ]

@[simp, toIsoGraph] theorem natDegree_charpoly (G : CGraph) :
    G.charpoly.natDegree = Fintype.card G.V :=
  Matrix.charpoly_natDegree_eq_dim _

theorem charpoly_eq_prod (G : CGraph) :
    G.charpoly = ∏ i, (X - C (G.eigenvalues i)) :=
  G.isHermitian_adjMat.charpoly_eq

/-- The characteristic polynomial is the product over the spectrum, so it carries exactly the
information the spectrum does. -/
theorem charpoly_eq_prod_spectrum (G : CGraph) :
    G.charpoly = (G.spectrum.map (fun x ↦ X - C x)).prod := by
  rw [spectrum_eq_map, Multiset.map_map, charpoly_eq_prod]
  rfl

theorem monic_charpoly (G : CGraph) : G.charpoly.Monic := Matrix.charpoly_monic _


theorem scalar_eq_smul_one {n : Type} [Fintype n] [DecidableEq n] (x : ℝ) :
    Matrix.scalar n x = x • (1 : Matrix n n ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

/-! ## Eigenvalues and eigenvectors -/

/-- `v` is an eigenvector of `G` for the eigenvalue `x`. -/
def HasEigenvector (G : CGraph) (x : ℝ) (v : G.V → ℝ) : Prop :=
  v ≠ 0 ∧ G.adjMat.mulVec v = x • v

/-- `x` is an eigenvalue of `G`. -/
def IsEigenvalue (G : CGraph) (x : ℝ) : Prop := ∃ v, G.HasEigenvector x v

theorem isRoot_charpoly_iff (G : CGraph) (x : ℝ) :
    G.charpoly.IsRoot x ↔ G.IsEigenvalue x := by
  have key : ∀ v : G.V → ℝ,
      (Matrix.scalar G.V x - G.adjMat).mulVec v = x • v - G.adjMat.mulVec v := fun v ↦ by
    rw [Matrix.sub_mulVec, scalar_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [Polynomial.IsRoot, charpoly, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h0⟩
    exact ⟨v, hv, by rw [key] at h0; linear_combination (norm := module) -h0⟩
  · rintro ⟨v, hv, h0⟩
    exact ⟨v, hv, by rw [key, h0, sub_self]⟩

theorem mem_spectrum_iff (G : CGraph) (x : ℝ) :
    x ∈ G.spectrum ↔ G.IsEigenvalue x := by
  rw [spectrum, Polynomial.mem_roots G.monic_charpoly.ne_zero, ← isRoot_charpoly_iff]

/-- If at least `|V|` distinct reals are all eigenvalues of `G`, they are exactly the spectrum. -/
theorem spectrum_eq_of_card_le (G : CGraph) (s : Finset ℝ)
    (hcard : Fintype.card G.V ≤ s.card) (hs : ∀ x ∈ s, G.IsEigenvalue x) :
    G.spectrum = s.val := by
  refine (Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.2 fun x ↦ ?_)
    (by simpa using hcard)).symm
  by_cases hx : x ∈ s
  · exact le_trans (Multiset.nodup_iff_count_le_one.1 s.nodup x)
      (Multiset.one_le_count_iff_mem.2 ((mem_spectrum_iff G x).2 (hs x hx)))
  · simp [Multiset.count_eq_zero_of_notMem (fun h ↦ hx (Finset.mem_def.mpr h))]

/-! ## Integrality

The adjacency matrix has integer entries, so the characteristic polynomial is a *monic integer*
polynomial and every eigenvalue is an algebraic integer.  Since `ℤ` is integrally closed in `ℚ`,
a rational eigenvalue is an integer. -/

/-- The adjacency matrix, over `ℤ`. -/
def adjMatInt (G : CGraph) : Matrix G.V G.V ℤ := fun i j ↦ if G.Adj i j then 1 else 0

theorem adjMat_eq_map_adjMatInt (G : CGraph) :
    G.adjMat = G.adjMatInt.map (Int.castRingHom ℝ) := by
  ext i j
  simp [adjMat_apply, adjMatInt, apply_ite]

/-- **The characteristic polynomial has integer coefficients.** -/
theorem charpoly_eq_map_int (G : CGraph) :
    G.charpoly = G.adjMatInt.charpoly.map (Int.castRingHom ℝ) := by
  rw [charpoly_eq_matrix_charpoly, adjMat_eq_map_adjMatInt, Matrix.charpoly_map]

/-- **Every eigenvalue is an algebraic integer**: it is a root of the monic integer polynomial
`charpoly`. -/
theorem isIntegral_of_mem_spectrum (G : CGraph) {x : ℝ} (hx : x ∈ G.spectrum) :
    IsIntegral ℤ x := by
  refine ⟨G.adjMatInt.charpoly, Matrix.charpoly_monic _, ?_⟩
  have h1 : G.charpoly.IsRoot x := (Polynomial.mem_roots G.monic_charpoly.ne_zero).1 hx
  rw [charpoly_eq_map_int] at h1
  rw [Polynomial.eval₂_eq_eval_map]
  simpa [algebraMap_int_eq] using h1

/-- **A rational eigenvalue is an integer**, because `ℤ` is integrally closed in `ℚ`. -/
theorem exists_intCast_eq_of_ratCast_mem_spectrum (G : CGraph) {q : ℚ}
    (hq : (q : ℝ) ∈ G.spectrum) : ∃ z : ℤ, (z : ℝ) = (q : ℝ) := by
  have h1 : IsIntegral ℤ ((algebraMap ℚ ℝ) q) := by
    simpa using G.isIntegral_of_mem_spectrum hq
  have h2 : IsIntegral ℤ q := h1.tower_bot (algebraMap ℚ ℝ).injective
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨z, by rw [← hz]; norm_cast⟩

/-! ## The empty graph and the disjoint union -/

@[simp] theorem adjMat_empty (n : ℕ) : (empty n).adjMat = 0 := by
  ext i j; simp [adjMat_apply]

@[simp] theorem charpoly_empty (n : ℕ) : (empty n).charpoly = X ^ n := by
  simp [charpoly, Matrix.charpoly_zero]

@[simp, toIsoGraph]
theorem spectrum_empty (n : ℕ) :
    (empty n).spectrum = Multiset.replicate n 0 := by
  simp [spectrum, Polynomial.roots_pow, Multiset.nsmul_singleton]

theorem adjMat_disjUnion (G H : CGraph) :
    (disjUnion G H).adjMat = Matrix.fromBlocks G.adjMat 0 0 H.adjMat := by
  ext x y
  cases x <;> cases y <;> simp [adjMat_apply, disjUnion]

@[simp, toIsoGraph] theorem charpoly_disjUnion (G H : CGraph) :
    (disjUnion G H).charpoly = G.charpoly * H.charpoly := by
  classical
  rw [charpoly_eq_matrix_charpoly, adjMat_disjUnion, Matrix.charpoly_fromBlocks_zero₁₂,
    ← charpoly_eq_matrix_charpoly, ← charpoly_eq_matrix_charpoly]

@[simp, toIsoGraph] theorem spectrum_disjUnion (G H : CGraph) :
    (disjUnion G H).spectrum = G.spectrum + H.spectrum := by
  rw [spectrum, charpoly_disjUnion, Polynomial.roots_mul
    (mul_ne_zero G.monic_charpoly.ne_zero H.monic_charpoly.ne_zero)]
  rfl

/-! ## The complete graph -/

theorem charpoly_sub_one {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) :
    (M - 1).charpoly = M.charpoly.comp (X + 1) := by
  refine Polynomial.funext fun t ↦ ?_
  rw [Matrix.eval_charpoly, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Matrix.eval_charpoly]
  congr 1
  rw [scalar_eq_smul_one, scalar_eq_smul_one]
  module

theorem adjMat_complete (n : ℕ) :
    (complete n).adjMat = Matrix.vecMulVec 1 1 - 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [adjMat_apply, complete, compl, Matrix.vecMulVec, h]

theorem charpoly_complete (n : ℕ) :
    (complete (n + 1)).charpoly = (X - C (n : ℝ)) * (X + 1) ^ n := by
  classical
  rw [charpoly_eq_matrix_charpoly, adjMat_complete, charpoly_sub_one, Matrix.charpoly_vecMulVec]
  have hd : (1 : Fin (n + 1) → ℝ) ⬝ᵥ 1 = (n : ℝ) + 1 := by
    simp [dotProduct]
  rw [hd]
  simp only [card_complete, Nat.add_sub_cancel, Polynomial.smul_eq_C_mul]
  simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.one_comp, Polynomial.C_add, Polynomial.C_1]
  ring

@[toIsoGraph]
theorem spectrum_complete (n : ℕ) :
    (complete (n + 1)).spectrum = (n : ℝ) ::ₘ Multiset.replicate n (-1) := by
  have h1 : (X + 1 : ℝ[X]) = X - C (-1) := by simp
  rw [spectrum, charpoly_complete, h1, Polynomial.roots_mul (mul_ne_zero
      (Polynomial.X_sub_C_ne_zero _) (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.roots_X_sub_C, Polynomial.roots_pow, Polynomial.roots_X_sub_C,
    Multiset.nsmul_singleton, Multiset.singleton_add]

/-! ## Regular graphs, complements, tensor products -/

theorem hasEigenvector_one_of_isRegularWith {G : CGraph} [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) : G.HasEigenvector k 1 := by
  refine ⟨fun h0 ↦ ?_, funext fun i ↦ ?_⟩
  · simpa using congrFun h0 (Classical.arbitrary G.V)
  · simpa [adjMat] using
      SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := (1 : ℝ)) h (v := i)

theorem adjMat_compl (G : CGraph) [DecidableEq G.V] :
    (compl G).adjMat = Matrix.vecMulVec 1 1 - 1 - G.adjMat := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [adjMat_apply, compl, Matrix.vecMulVec, adj_self]
  · cases hb : G.Adj i j <;>
      simp [adjMat_apply, compl, Matrix.vecMulVec, h, hb]

theorem compl_adjMatrix_eq (G : CGraph) [DecidableEq G.V] :
    G.toSimpleᶜ.adjMatrix ℝ = Matrix.vecMulVec 1 1 - 1 - G.adjMat := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [SimpleGraph.adjMatrix_apply, adjMat_apply, Matrix.vecMulVec, adj_self]
  · cases hb : G.Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, adjMat_apply, Matrix.vecMulVec, h, hb]

theorem vecMulVec_one_mulVec {G : CGraph} {v : G.V → ℝ} (hsum : ∑ i, v i = 0) :
    Matrix.vecMulVec (1 : G.V → ℝ) 1 *ᵥ v = 0 := by
  funext i; simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, hsum]

theorem compl_adjMatrix_mulVec {G : CGraph} [DecidableEq G.V] {x : ℝ} {v : G.V → ℝ}
    (hsum : ∑ i, v i = 0) (h : G.adjMat *ᵥ v = x • v) :
    G.toSimpleᶜ.adjMatrix ℝ *ᵥ v = (-1 - x) • v := by
  rw [compl_adjMatrix_eq, Matrix.sub_mulVec, Matrix.sub_mulVec, h, Matrix.one_mulVec,
    vecMulVec_one_mulVec hsum]
  module

/-- An eigenvector orthogonal to the all-ones vector is an eigenvector of the complement, with
eigenvalue `-1 - x`. -/
theorem hasEigenvector_compl {G : CGraph} [DecidableEq G.V] {x : ℝ} {v : G.V → ℝ}
    (hsum : ∑ i, v i = 0) (h : G.HasEigenvector x v) :
    (compl G).HasEigenvector (-1 - x) v := by
  refine ⟨h.1, ?_⟩
  rw [adjMat_compl, Matrix.sub_mulVec, Matrix.sub_mulVec, h.2, Matrix.one_mulVec,
    vecMulVec_one_mulVec hsum]
  module

/-- Eigenvalues of a tensor product multiply. -/
theorem hasEigenvector_tensorProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    {x y : ℝ} {u : G.V → ℝ} {w : H.V → ℝ} (hu : G.HasEigenvector x u)
    (hw : H.HasEigenvector y w) :
    (tensorProduct G H).HasEigenvector (x * y) (fun p ↦ u p.1 * w p.2) := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hw0, hw1⟩ := hw
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hu0
  obtain ⟨b₀, hb₀⟩ := Function.ne_iff.1 hw0
  refine ⟨fun hc ↦ mul_ne_zero ha₀ hb₀ (congrFun hc (a₀, b₀)), funext fun p ↦ ?_⟩
  obtain ⟨a, b⟩ := p
  have hga := congrFun hu1 a
  have hhb := congrFun hw1 b
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hga hhb ⊢
  have hsplit : ∀ (c : G.V) (d : H.V),
      (tensorProduct G H).adjMat (a, b) (c, d) * (u c * w d)
        = G.adjMat a c * u c * (H.adjMat b d * w d) := by
    intro c d
    by_cases h1 : G.Adj a c <;> by_cases h2 : H.Adj b d <;>
      simp [adjMat_apply, tensorProduct, h1, h2]
  calc ∑ q : G.V × H.V, (tensorProduct G H).adjMat (a, b) q * (u q.1 * w q.2)
      = ∑ c : G.V, ∑ d : H.V, G.adjMat a c * u c * (H.adjMat b d * w d) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ hsplit c d
    _ = (∑ c, G.adjMat a c * u c) * ∑ d, H.adjMat b d * w d := by rw [Finset.sum_mul_sum]
    _ = x * y * (u a * w b) := by rw [hga, hhb]; ring

/-! ## Strongly regular graphs -/

/-- Every eigenvalue of a strongly regular graph other than the degree satisfies the quadratic
`x² = (ℓ - μ) x + (k - μ)`. -/
theorem sq_eq_of_isSRGWith {G : CGraph} [DecidableEq G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) {x : ℝ} {v : G.V → ℝ} (hsum : ∑ i, v i = 0)
    (hv : G.HasEigenvector x v) : x ^ 2 = ((l : ℝ) - m) * x + ((k : ℝ) - m) := by
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hc := compl_adjMatrix_mulVec hsum hv1
  have hm : G.adjMat * G.adjMat
      = (k : ℝ) • 1 + (l : ℝ) • G.adjMat + (m : ℝ) • (G.toSimpleᶜ.adjMatrix ℝ) := by
    have hme := h.matrix_eq (α := ℝ)
    rw [pow_two] at hme
    simpa [adjMat, Nat.cast_smul_eq_nsmul] using hme
  have hsq : (G.adjMat * G.adjMat) *ᵥ v = (x ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_smul, hv1, smul_smul, ← pow_two]
  have key : (x ^ 2) • v = ((k : ℝ) + l * x + m * (-1 - x)) • v := by
    rw [← hsq, hm, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, hv1, hc]
    module
  have hco := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at hco
  have := mul_right_cancel₀ hi hco
  linarith

theorem adjMat_symm (G : CGraph) (i j : G.V) : G.adjMat i j = G.adjMat j i := by
  simp [adjMat_apply, G.symm i j]

/-- In a `k`-regular graph every row and every column of the adjacency matrix sums to `k`. -/
theorem sum_adjMat_row {G : CGraph} {k : ℕ} (hk : G.IsRegularWith k) (j : G.V) :
    ∑ i, G.adjMat j i = (k : ℝ) := by
  simpa [adjMat, Matrix.mulVec, dotProduct] using
    SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := (1 : ℝ)) hk (v := j)

/-- **An eigenvector for an eigenvalue other than the degree has coordinates summing to zero**: it
is orthogonal to the all-ones eigenvector. -/
theorem sum_eq_zero_of_ne_of_isRegularWith {G : CGraph} {k : ℕ} (hk : G.IsRegularWith k) {x : ℝ}
    {v : G.V → ℝ} (hx : x ≠ k) (hv : G.HasEigenvector x v) : ∑ i, v i = 0 := by
  have h1 : ∑ i, (G.adjMat *ᵥ v) i = x * ∑ i, v i := by
    rw [hv.2]
    simp [Finset.mul_sum]
  have h2 : ∑ i, (G.adjMat *ᵥ v) i = (k : ℝ) * ∑ i, v i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, G.adjMat i j * v j
        = ∑ j, (∑ i, G.adjMat i j) * v j :=
          Finset.sum_congr rfl fun j _ ↦ (Finset.sum_mul _ _ _).symm
      _ = ∑ j, (k : ℝ) * v j := Finset.sum_congr rfl fun j _ ↦ by
          rw [show ∑ i, G.adjMat i j = ∑ i, G.adjMat j i from
            Finset.sum_congr rfl fun i _ ↦ adjMat_symm G i j, sum_adjMat_row hk]
      _ = (k : ℝ) * ∑ j, v j := (Finset.mul_sum _ _ _).symm
  have h3 : (x - k) * ∑ i, v i = 0 := by rw [sub_mul, ← h1, ← h2]; ring
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hx
  · exact h

/-- The degree of a regular graph is an eigenvalue, with the all-ones eigenvector. -/
theorem mem_spectrum_of_isRegularWith {G : CGraph} [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) : (k : ℝ) ∈ G.spectrum :=
  (mem_spectrum_iff G k).2 ⟨1, hasEigenvector_one_of_isRegularWith h⟩

/-- Every eigenvalue of a strongly regular graph other than the degree satisfies the quadratic. -/
theorem sq_eq_of_isSRGWith_of_ne {G : CGraph} [DecidableEq G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) {x : ℝ} (hx : x ≠ k) (hev : G.IsEigenvalue x) :
    x ^ 2 = ((l : ℝ) - m) * x + ((k : ℝ) - m) := by
  obtain ⟨v, hv⟩ := hev
  exact sq_eq_of_isSRGWith h (sum_eq_zero_of_ne_of_isRegularWith h.regular hx hv) hv

/-- The quadratic formula, in the form used for the two non-principal eigenvalues. -/
private theorem eq_of_sq_eq (b c x : ℝ) (h : x ^ 2 = b * x + c) :
    x = (b + Real.sqrt (b ^ 2 + 4 * c)) / 2 ∨ x = (b - Real.sqrt (b ^ 2 + 4 * c)) / 2 := by
  have hd : (0 : ℝ) ≤ b ^ 2 + 4 * c := by nlinarith [sq_nonneg (2 * x - b)]
  have hs : Real.sqrt (b ^ 2 + 4 * c) ^ 2 = b ^ 2 + 4 * c := Real.sq_sqrt hd
  have h2 : (2 * x - b - Real.sqrt (b ^ 2 + 4 * c))
      * (2 * x - b + Real.sqrt (b ^ 2 + 4 * c)) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- **The spectrum of a strongly regular graph.**  Every eigenvalue is either the degree `k` or one
of the two roots `r, s = ½ ((ℓ - μ) ± √((ℓ - μ)² + 4 (k - μ)))` of the quadratic
`x² = (ℓ - μ) x + (k - μ)`; so an `srg(n, k, ℓ, μ)` has at most three distinct eigenvalues. -/
theorem eigenvalue_eq_of_isSRGWith {G : CGraph} [DecidableEq G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) {x : ℝ} (hev : G.IsEigenvalue x) :
    x = k ∨ x = (((l : ℝ) - m) + Real.sqrt (((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m))) / 2
      ∨ x = (((l : ℝ) - m) - Real.sqrt (((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m))) / 2 := by
  by_cases hx : x = (k : ℝ)
  · exact Or.inl hx
  · exact Or.inr (eq_of_sq_eq _ _ _ (sq_eq_of_isSRGWith_of_ne h hx hev))

theorem mem_spectrum_isSRGWith {G : CGraph} [DecidableEq G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) {x : ℝ} (hx : x ∈ G.spectrum) :
    x = k ∨ x = (((l : ℝ) - m) + Real.sqrt (((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m))) / 2
      ∨ x = (((l : ℝ) - m) - Real.sqrt (((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m))) / 2 :=
  eigenvalue_eq_of_isSRGWith h ((mem_spectrum_iff G x).1 hx)

/-! ## The path -/

theorem path_adj_iff (n : ℕ) (i j : (path n).V) :
    (path n).Adj i j = true ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  simp only [path, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, Fin.ext_iff]
  omega

theorem sum_ite_eq_fin (n : ℕ) (g : ℕ → ℝ) (k : ℕ) (hk : n ≤ k → g k = 0) :
    ∑ j : Fin n, (if k = j.1 then g j.1 else 0) = g k := by
  rcases lt_or_ge k n with hkn | hkn
  · rw [Finset.sum_eq_single (⟨k, hkn⟩ : Fin n)]
    · simp
    · intro b _ hb
      exact if_neg fun h ↦ hb (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hk hkn]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have := j.isLt
    exact if_neg (by omega)

theorem sum_ite_succ_fin (n : ℕ) (c : ℝ) (k : ℕ) (hk : k = 0 → c = 0) (hkn : k < n) :
    ∑ j : Fin n, (if j.1 + 1 = k then c else 0) = c := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk hk0]
    refine Finset.sum_eq_zero fun j _ ↦ if_neg (by omega)
  · have hk1 : k - 1 < n := by omega
    rw [Finset.sum_eq_single (⟨k - 1, hk1⟩ : Fin n)]
    · exact if_pos (by show k - 1 + 1 = k; omega)
    · intro b _ hb
      exact if_neg fun h ↦ hb (Fin.ext (by show b.1 = k - 1; omega))
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The adjacency matrix of the path acts on a vector coming from a function on `ℕ` by shifting
one step each way; the two ends are handled by the boundary conditions `f 0 = 0` and
`f (n + 1) = 0`. -/
theorem path_adjMat_mulVec (n : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) (hn : f (n + 1) = 0) (i : Fin n) :
    ((path n).adjMat *ᵥ fun j : Fin n ↦ f (j.1 + 1)) i = f i.1 + f (i.1 + 2) := by
  have hi := i.isLt
  have step : ∀ j : Fin n, (if (path n).Adj i j = true then (1 : ℝ) else 0) * f (j.1 + 1)
      = (if i.1 + 1 = j.1 then f (j.1 + 1) else 0) + (if j.1 + 1 = i.1 then f i.1 else 0) := by
    intro j
    rcases eq_or_ne (i.1 + 1) j.1 with h1 | h1
    · rw [if_pos ((path_adj_iff n i j).2 (Or.inl h1)), if_pos h1, if_neg (by omega)]; ring
    · rcases eq_or_ne (j.1 + 1) i.1 with h2 | h2
      · rw [if_pos ((path_adj_iff n i j).2 (Or.inr h2)), if_neg h1, if_pos h2, h2]; ring
      · rw [if_neg (fun h ↦ (path_adj_iff n i j).1 h |>.elim h1 h2), if_neg h1, if_neg h2]; ring
  simp only [Matrix.mulVec, dotProduct, adjMat_apply]
  calc ∑ j : Fin n, (if (path n).Adj i j = true then (1 : ℝ) else 0) * f (j.1 + 1)
      = ∑ j : Fin n, ((if i.1 + 1 = j.1 then f (j.1 + 1) else 0)
          + (if j.1 + 1 = i.1 then f i.1 else 0)) := Finset.sum_congr rfl fun j _ ↦ step j
    _ = f i.1 + f (i.1 + 2) := by
        rw [Finset.sum_add_distrib,
          sum_ite_eq_fin n (fun k ↦ f (k + 1)) (i.1 + 1) (fun h ↦ by
            have hh : i.1 + 1 = n := by omega
            rw [hh]; exact hn),
          sum_ite_succ_fin n (f i.1) i.1 (fun h ↦ by rw [h]; exact h0) hi]
        ring

theorem sin_sub_add_sin_add (a t : ℝ) :
    Real.sin (t - a) + Real.sin (t + a) = 2 * Real.cos a * Real.sin t := by
  rw [Real.sin_sub, Real.sin_add]; ring

open Real in
/-- The `m`-th eigenvector of the path on `n` vertices, `sin (π (m+1) (j+1) / (n+1))`, with
eigenvalue `2 cos (π (m+1) / (n+1))`. -/
theorem hasEigenvector_path (n : ℕ) (m : Fin n) :
    (path n).HasEigenvector (2 * Real.cos (π * (m.1 + 1) / (n + 1)))
      (fun j : Fin n ↦ Real.sin (π * (m.1 + 1) / (n + 1) * (j.1 + 1))) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set a : ℝ := π * (m.1 + 1) / (n + 1) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have haltpi : a < π := by
    have h1 : (m.1 : ℝ) + 1 < (n : ℝ) + 1 := by
      have := m.isLt; exact_mod_cast Nat.succ_lt_succ this
    rw [ha, div_lt_iff₀ hn1]
    exact mul_lt_mul_of_pos_left h1 Real.pi_pos
  have hf0 : Real.sin (a * ((0 : ℕ) : ℝ)) = 0 := by simp
  have hfn : Real.sin (a * (((n + 1 : ℕ)) : ℝ)) = 0 := by
    have hh : a * ((n + 1 : ℕ) : ℝ) = ((m.1 + 1 : ℕ) : ℝ) * π := by
      rw [ha]; push_cast; field_simp
    rw [hh, Real.sin_nat_mul_pi]
  refine ⟨fun h0 ↦ ?_, funext fun i ↦ ?_⟩
  · have hzero := congrFun h0 (⟨0, m.pos⟩ : Fin n)
    simp only [Pi.zero_apply] at hzero
    rw [show ((⟨0, m.pos⟩ : Fin n).1 : ℝ) + 1 = 1 by norm_num, mul_one] at hzero
    exact absurd hzero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hapos haltpi))
  · have key := path_adjMat_mulVec n (fun k : ℕ ↦ Real.sin (a * k)) hf0 hfn i
    simp only at key
    have hpre : (fun j : Fin n ↦ Real.sin (a * ((j.1 : ℝ) + 1)))
        = fun j : Fin n ↦ Real.sin (a * ((j.1 + 1 : ℕ) : ℝ)) := by
      funext j; norm_num
    rw [hpre, key]
    have hs := sin_sub_add_sin_add a (a * ((i.1 : ℝ) + 1))
    rw [show a * ((i.1 : ℝ) + 1) - a = a * (i.1 : ℝ) by ring,
      show a * ((i.1 : ℝ) + 1) + a = a * ((i.1 : ℝ) + 2) by ring] at hs
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hs]


theorem path_arg_mem_Icc (n : ℕ) (m : Fin n) :
    Real.pi * (m.1 + 1) / (n + 1) ∈ Set.Icc 0 Real.pi := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn1]
  have h1 : (m.1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have := m.isLt
    have : (m.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this.le
    linarith
  exact mul_le_mul_of_nonneg_left h1 Real.pi_pos.le

theorem injective_path_eigenvalue (n : ℕ) :
    Function.Injective (fun m : Fin n ↦ 2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1))) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1
  intro m m' h
  simp only at h
  have hcos := mul_left_cancel₀ (two_ne_zero) h
  have harg := Real.injOn_cos (path_arg_mem_Icc n m) (path_arg_mem_Icc n m') hcos
  have h3 : Real.pi * ((m.1 : ℝ) + 1) = Real.pi * ((m'.1 : ℝ) + 1) := by
    have := congrArg (fun t : ℝ ↦ t * ((n : ℝ) + 1)) harg
    simpa [div_mul_cancel₀, hne] using this
  have h4 := mul_left_cancel₀ Real.pi_ne_zero h3
  have : (m.1 : ℝ) = (m'.1 : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- **The spectrum of the path** `P_n`: the `n` numbers `2 cos (π m / (n + 1))`, `1 ≤ m ≤ n`. -/
@[toIsoGraph]
theorem spectrum_path (n : ℕ) :
    (path n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1))) := by
  classical
  set f : Fin n → ℝ := fun m ↦ 2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1)) with hf
  have hinj : Function.Injective f := injective_path_eigenvalue n
  have hcard : Fintype.card (path n).V ≤ (Finset.image f Finset.univ).card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [path, ofRel]
  have hs : ∀ x ∈ Finset.image f Finset.univ, (path n).IsEigenvalue x := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨_, hasEigenvector_path n m⟩
  rw [spectrum_eq_of_card_le _ _ hcard hs, Finset.image_val_of_injOn hinj.injOn]


/-! ## The cycle

The cycle is diagonalised by the discrete Fourier transform.  Working over `ℂ`, the matrix
`P j m = ζ ^ (j m)` built from a primitive `n`-th root of unity `ζ` is invertible, and it conjugates
the adjacency matrix of `C_n` into the diagonal matrix of the numbers `ζ ^ m + ζ ^ (-m)
= 2 cos (2 π m / n)`.  Since the characteristic polynomial has real coefficients, the real
statement follows by injectivity of `ℝ[X] → ℂ[X]`. -/

private theorem mod_succ_eq (n j : ℕ) (hj : j < n) :
    (j + 1) % n = if j + 1 = n then 0 else j + 1 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with h | h
  · rw [if_pos (by omega), show j + 1 = n from by omega, Nat.mod_self]
  · rw [if_neg (by omega), Nat.mod_eq_of_lt h]

private theorem mod_pred_eq (n i : ℕ) (hi : i < n) :
    (i + n - 1) % n = if i = 0 then n - 1 else i - 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [if_pos rfl, show 0 + n - 1 = n - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg (by omega), show i + n - 1 = n + (i - 1) from by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]

theorem cycle_adj_iff {n : ℕ} (hn : 2 ≤ n) (i j : (cycle n).V) :
    (cycle n).Adj i j = true ↔ ((i.1 + 1) % n = j.1 ∨ (j.1 + 1) % n = i.1) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [cycle, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, Fin.ext_iff]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  revert h
  rw [mod_succ_eq n i.1 hi, mod_succ_eq n j.1 hj]
  split_ifs <;> omega

/-- The two neighbours of `i` in the cycle, named by their labels. -/
private theorem cycle_adj_iff_eq {n : ℕ} (hn : 3 ≤ n) (i j : (cycle n).V) :
    (cycle n).Adj i j = true ↔ (j.1 = (i.1 + 1) % n ∨ j.1 = (i.1 + n - 1) % n) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [cycle_adj_iff (by omega) i j, mod_succ_eq n i.1 hi, mod_succ_eq n j.1 hj,
    mod_pred_eq n i.1 hi]
  split_ifs <;> omega

private theorem cycle_nbr_ne {n : ℕ} (hn : 3 ≤ n) (i : (cycle n).V) :
    (i.1 + 1) % n ≠ (i.1 + n - 1) % n := by
  have hi := i.isLt
  rw [mod_succ_eq n i.1 hi, mod_pred_eq n i.1 hi]
  split_ifs <;> omega

/-- A primitive `n`-th root of unity. -/
private noncomputable def cycZeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

private theorem isPrimitiveRoot_cycZeta {n : ℕ} (hn : 0 < n) :
    IsPrimitiveRoot (cycZeta n) n := Complex.isPrimitiveRoot_exp n hn.ne'

private theorem cycZeta_ne_zero (n : ℕ) : cycZeta n ≠ 0 := Complex.exp_ne_zero _

private theorem cycZeta_pow_n {n : ℕ} (hn : 0 < n) : cycZeta n ^ n = 1 :=
  (isPrimitiveRoot_cycZeta hn).pow_eq_one

private theorem cycZeta_pow_mod {n : ℕ} (hn : 0 < n) (k : ℕ) :
    cycZeta n ^ (k % n) = cycZeta n ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, cycZeta_pow_n hn, one_pow, one_mul]

private theorem cycZeta_pow_congr {n : ℕ} (hn : 0 < n) {k l : ℕ} (h : k % n = l % n) :
    cycZeta n ^ k = cycZeta n ^ l := by
  rw [← cycZeta_pow_mod hn k, h, cycZeta_pow_mod hn l]

private theorem cycZeta_add_inv (n m : ℕ) :
    cycZeta n ^ m + (cycZeta n ^ m)⁻¹ = ((2 * Real.cos (2 * Real.pi * m / n) : ℝ) : ℂ) := by
  have h1 : cycZeta n ^ m = Complex.exp (((2 * Real.pi * m / n : ℝ) : ℂ) * Complex.I) := by
    rw [cycZeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg]
  push_cast [Complex.ofReal_cos]
  ring

/-- The adjacency matrix of the cycle, over `ℂ`. -/
private noncomputable def cycA (n : ℕ) : Matrix (cycle n).V (cycle n).V ℂ :=
  Matrix.of fun i j ↦ if (cycle n).Adj i j then 1 else 0

/-- The discrete Fourier matrix. -/
private noncomputable def cycP (n : ℕ) : Matrix (cycle n).V (cycle n).V ℂ :=
  Matrix.of fun j m ↦ cycZeta n ^ (j.1 * m.1)

/-- Its inverse. -/
private noncomputable def cycQ (n : ℕ) : Matrix (cycle n).V (cycle n).V ℂ :=
  Matrix.of fun m j ↦ (n : ℂ)⁻¹ * (cycZeta n ^ (j.1 * m.1))⁻¹

/-- The eigenvalues of the cycle. -/
private noncomputable def cycEig (n : ℕ) : (cycle n).V → ℂ :=
  fun m ↦ ((2 * Real.cos (2 * Real.pi * m.1 / n) : ℝ) : ℂ)

private theorem cycA_eq (n : ℕ) : cycA n = (cycle n).adjMat.map (Complex.ofRealHom) := by
  ext i j
  by_cases h : (cycle n).Adj i j <;> simp [cycA, adjMat_apply, h]

private theorem cycP_mul_cycQ {n : ℕ} (hn : 0 < n) : cycP n * cycQ n = 1 := by
  have hz := cycZeta_ne_zero n
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  ext j l
  have hterm : ∀ m : (cycle n).V,
      cycZeta n ^ (j.1 * m.1) * ((n : ℂ)⁻¹ * (cycZeta n ^ (l.1 * m.1))⁻¹)
        = (n : ℂ)⁻¹ * (cycZeta n ^ j.1 * (cycZeta n ^ l.1)⁻¹) ^ m.1 := by
    intro m
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul]
    ring
  have hsum : ∑ m : (cycle n).V, cycZeta n ^ (j.1 * m.1) *
        ((n : ℂ)⁻¹ * (cycZeta n ^ (l.1 * m.1))⁻¹)
      = (n : ℂ)⁻¹ * ∑ i ∈ Finset.range n, (cycZeta n ^ j.1 * (cycZeta n ^ l.1)⁻¹) ^ i := by
    rw [Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i ↦ (n : ℂ)⁻¹ * (cycZeta n ^ j.1 * (cycZeta n ^ l.1)⁻¹) ^ i) n]
    exact Finset.sum_congr rfl fun m _ ↦ hterm m
  simp only [Matrix.mul_apply, cycP, cycQ, Matrix.of_apply]
  rw [hsum]
  by_cases hjl : j = l
  · subst hjl
    rw [mul_inv_cancel₀ (pow_ne_zero _ hz), Matrix.one_apply_eq]
    simp
    field_simp
  · have hx1 : cycZeta n ^ j.1 * (cycZeta n ^ l.1)⁻¹ ≠ 1 := by
      intro h
      have hl0 : cycZeta n ^ l.1 ≠ 0 := pow_ne_zero _ hz
      have heq : cycZeta n ^ j.1 = cycZeta n ^ l.1 := by
        field_simp at h; exact h
      exact hjl (Fin.ext ((isPrimitiveRoot_cycZeta hn).pow_inj j.isLt l.isLt heq))
    have hpj : (cycZeta n ^ j.1) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, cycZeta_pow_n hn, one_pow]
    have hpl : (cycZeta n ^ l.1) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, cycZeta_pow_n hn, one_pow]
    have hxn : (cycZeta n ^ j.1 * (cycZeta n ^ l.1)⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hpj, hpl, inv_one, mul_one]
    rw [geom_sum_eq hx1, hxn, sub_self, zero_div, mul_zero, Matrix.one_apply_ne hjl]

private theorem cycQ_mul_cycP {n : ℕ} (hn : 0 < n) : cycQ n * cycP n = 1 :=
  mul_eq_one_comm.mp (cycP_mul_cycQ hn)

private theorem cycA_mul_cycP {n : ℕ} (hn : 3 ≤ n) :
    cycA n * cycP n = cycP n * Matrix.diagonal (cycEig n) := by
  have hn0 : 0 < n := by omega
  ext i m
  have ha : (i.1 + 1) % n < n := Nat.mod_lt _ hn0
  have hb : (i.1 + n - 1) % n < n := Nat.mod_lt _ hn0
  set a : (cycle n).V := ⟨(i.1 + 1) % n, ha⟩ with hadef
  set b : (cycle n).V := ⟨(i.1 + n - 1) % n, hb⟩ with hbdef
  have hab : a ≠ b := fun h ↦ cycle_nbr_ne hn i (congrArg Fin.val h)
  have step : ∀ j : (cycle n).V,
      (if (cycle n).Adj i j = true then (1 : ℂ) else 0) * cycZeta n ^ (j.1 * m.1)
        = (if j = a then cycZeta n ^ (j.1 * m.1) else 0)
          + (if j = b then cycZeta n ^ (j.1 * m.1) else 0) := by
    intro j
    by_cases h1 : j = a
    · have hne : ¬ (j = b) := fun hc ↦ hab (by rw [← h1]; exact hc)
      rw [if_pos h1, if_neg hne, if_pos ((cycle_adj_iff_eq hn i j).2 (Or.inl
        (by rw [h1, hadef])))]
      ring
    · by_cases h2 : j = b
      · rw [if_neg h1, if_pos h2, if_pos ((cycle_adj_iff_eq hn i j).2 (Or.inr
          (by rw [h2, hbdef])))]
        ring
      · have hno : ¬ ((cycle n).Adj i j = true) := by
          intro hadj
          rcases (cycle_adj_iff_eq hn i j).1 hadj with h | h
          · exact h1 (Fin.ext h)
          · exact h2 (Fin.ext h)
        rw [if_neg h1, if_neg h2, if_neg hno]
        ring
  have hsum : ∑ j : (cycle n).V,
      (if (cycle n).Adj i j = true then (1 : ℂ) else 0) * cycZeta n ^ (j.1 * m.1)
        = cycZeta n ^ (a.1 * m.1) + cycZeta n ^ (b.1 * m.1) := by
    calc ∑ j : (cycle n).V,
          (if (cycle n).Adj i j = true then (1 : ℂ) else 0) * cycZeta n ^ (j.1 * m.1)
        = ∑ j : (cycle n).V, ((if j = a then cycZeta n ^ (j.1 * m.1) else 0)
            + (if j = b then cycZeta n ^ (j.1 * m.1) else 0)) :=
          Finset.sum_congr rfl fun j _ ↦ step j
      _ = cycZeta n ^ (a.1 * m.1) + cycZeta n ^ (b.1 * m.1) := by
          rw [Finset.sum_add_distrib]; simp
  have hA : cycZeta n ^ (a.1 * m.1) = cycZeta n ^ (i.1 * m.1) * cycZeta n ^ m.1 := by
    rw [hadef, show ((⟨(i.1 + 1) % n, ha⟩ : (cycle n).V)).1 = (i.1 + 1) % n from rfl,
      cycZeta_pow_congr hn0 ((Nat.mod_modEq (i.1 + 1) n).mul_right m.1),
      show (i.1 + 1) * m.1 = i.1 * m.1 + m.1 from by ring, pow_add]
  have hinv : cycZeta n ^ ((n - 1) * m.1) = (cycZeta n ^ m.1)⁻¹ := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h1 : cycZeta (n' + 1) ^ ((n' + 1 - 1) * m.1) * cycZeta (n' + 1) ^ m.1 = 1 := by
      rw [← pow_add, show (n' + 1 - 1) * m.1 + m.1 = (n' + 1) * m.1 from by simp; ring,
        pow_mul, cycZeta_pow_n hn0, one_pow]
    exact eq_inv_of_mul_eq_one_left h1
  have hB : cycZeta n ^ (b.1 * m.1) = cycZeta n ^ (i.1 * m.1) * (cycZeta n ^ m.1)⁻¹ := by
    rw [hbdef, show ((⟨(i.1 + n - 1) % n, hb⟩ : (cycle n).V)).1 = (i.1 + n - 1) % n from rfl,
      cycZeta_pow_congr hn0 ((Nat.mod_modEq (i.1 + n - 1) n).mul_right m.1),
      show (i.1 + n - 1) * m.1 = i.1 * m.1 + (n - 1) * m.1 from by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [show i.1 + (n' + 1) - 1 = i.1 + n' from by omega]
        ring,
      pow_add, hinv]
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, cycA, cycP, Matrix.of_apply]
  rw [hsum, hA, hB, cycEig, ← cycZeta_add_inv n m.1]
  ring

private theorem cycA_eq_conj {n : ℕ} (hn : 3 ≤ n) :
    cycA n = cycP n * Matrix.diagonal (cycEig n) * cycQ n := by
  calc cycA n = cycA n * (cycP n * cycQ n) := by rw [cycP_mul_cycQ (by omega), mul_one]
    _ = cycA n * cycP n * cycQ n := by rw [mul_assoc]
    _ = cycP n * Matrix.diagonal (cycEig n) * cycQ n := by rw [cycA_mul_cycP hn]

/-- **The characteristic polynomial of the cycle** `C_n`, `n ≥ 3`. -/
theorem charpoly_cycle {n : ℕ} (hn : 3 ≤ n) :
    (cycle n).charpoly = ∏ m : (cycle n).V, (X - C (2 * Real.cos (2 * Real.pi * m.1 / n))) := by
  have hn0 : 0 < n := by omega
  have key : (cycA n).charpoly = ∏ m : (cycle n).V, (X - C (cycEig n m)) := by
    rw [cycA_eq_conj hn, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, cycQ_mul_cycP hn0,
      mul_one, Matrix.charpoly_diagonal]
  rw [cycA_eq, Matrix.charpoly_map, ← charpoly_eq_matrix_charpoly] at key
  refine Polynomial.map_injective (Complex.ofRealHom) Complex.ofReal_injective ?_
  rw [key, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun m _ ↦ by simp [cycEig]

/-- **The spectrum of the cycle** `C_n`, `n ≥ 3`: the numbers `2 cos (2 π m / n)`. -/
theorem spectrum_cycle {n : ℕ} (hn : 3 ≤ n) :
    (cycle n).spectrum
      = Finset.univ.val.map (fun m : (cycle n).V ↦ 2 * Real.cos (2 * Real.pi * m.1 / n)) := by
  rw [spectrum, charpoly_cycle hn,
    show (∏ m : (cycle n).V, (X - C (2 * Real.cos (2 * Real.pi * m.1 / n))))
      = ((Finset.univ.val.map (fun m : (cycle n).V ↦ 2 * Real.cos (2 * Real.pi * m.1 / n))).map
        (fun a ↦ X - C a)).prod from by rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]


/-! ## Diagonalisation

A conjugating matrix together with the diagonal it produces determines the whole spectrum.  Every
graph admits one, by the spectral theorem for Hermitian matrices; exhibiting an explicit one is how
the spectrum of a product is computed. -/

theorem charpoly_eq_prod_of_conj {G : CGraph} {P Q : Matrix G.V G.V ℝ} {d : G.V → ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : G.adjMat * P = P * Matrix.diagonal d) :
    G.charpoly = ∏ i, (X - C (d i)) := by
  have hA : G.adjMat = P * Matrix.diagonal d * Q := by
    calc G.adjMat = G.adjMat * (P * Q) := by rw [hPQ, mul_one]
      _ = G.adjMat * P * Q := by rw [mul_assoc]
      _ = P * Matrix.diagonal d * Q := by rw [h]
  rw [charpoly, hA, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hQP, mul_one,
    Matrix.charpoly_diagonal]

theorem spectrum_eq_of_conj {G : CGraph} {P Q : Matrix G.V G.V ℝ} {d : G.V → ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : G.adjMat * P = P * Matrix.diagonal d) :
    G.spectrum = Finset.univ.val.map d := by
  rw [spectrum, charpoly_eq_prod_of_conj hPQ hQP h,
    show (∏ i, (X - C (d i))) = ((Finset.univ.val.map d).map (fun a ↦ X - C a)).prod from by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- **The spectral theorem**, packaged: every graph is diagonalised by some invertible matrix, with
the eigenvalues on the diagonal. -/
theorem exists_conj_diagonal (G : CGraph) :
    ∃ P Q : Matrix G.V G.V ℝ, P * Q = 1 ∧ Q * P = 1 ∧
      G.adjMat * P = P * Matrix.diagonal G.eigenvalues := by
  have hA := G.isHermitian_adjMat
  set U : Matrix G.V G.V ℝ := ↑hA.eigenvectorUnitary with hUdef
  have hU : U ∈ unitary (Matrix G.V G.V ℝ) := hA.eigenvectorUnitary.2
  have hst : Star.star U * G.adjMat * U = Matrix.diagonal G.eigenvalues := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    exact h
  refine ⟨U, Star.star U, hU.2, hU.1, ?_⟩
  calc G.adjMat * U = U * Star.star U * G.adjMat * U := by rw [hU.2, one_mul]
    _ = U * (Star.star U * G.adjMat * U) := by simp only [mul_assoc]
    _ = U * Matrix.diagonal G.eigenvalues := by rw [hst]

/-- The characteristic polynomial of a conjugate of a diagonal matrix, for a bare matrix rather
than an adjacency matrix. -/
theorem charpoly_eq_prod_of_conj' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M P Q : Matrix ι ι ℝ} {d : ι → ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hM : M * P = P * Matrix.diagonal d) : M.charpoly = ∏ i, (X - C (d i)) := by
  have hA : M = P * Matrix.diagonal d * Q := by
    calc M = M * (P * Q) := by rw [hPQ, mul_one]
      _ = M * P * Q := by rw [mul_assoc]
      _ = P * Matrix.diagonal d * Q := by rw [hM]
  rw [hA, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hQP, mul_one, Matrix.charpoly_diagonal]

/-- **Shifting by the identity shifts every eigenvalue**: `A + c I` has characteristic polynomial
`∏ (X - (λᵢ + c))`. -/
theorem charpoly_adjMat_add_smul_one (G : CGraph) [inst : DecidableEq G.V] (c : ℝ) :
    (G.adjMat + c • (1 : Matrix G.V G.V ℝ)).charpoly = ∏ i, (X - C (G.eigenvalues i + c)) := by
  obtain rfl : inst = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  obtain ⟨P, Q, hPQ, hQP, hd⟩ := G.exists_conj_diagonal
  have hdiag : Matrix.diagonal (fun i ↦ G.eigenvalues i + c)
      = Matrix.diagonal G.eigenvalues + c • (1 : Matrix G.V G.V ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  refine charpoly_eq_prod_of_conj' hPQ hQP ?_
  rw [Matrix.add_mul, hd, Matrix.smul_mul, Matrix.one_mul, hdiag, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one]

/-- The roots of `∏ (X - f i)`, with multiplicity, are the values of `f`. -/
private theorem roots_prod_X_sub_C' {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  rw [show (∏ i, (X - C (f i))) = ((Finset.univ.val.map f).map (fun a ↦ X - C a)).prod from by
      rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]

/-! ## The tensor product -/

theorem adjMat_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).adjMat = G.adjMat ⊗ₖ H.adjMat := by
  ext p q
  by_cases h1 : G.Adj p.1 q.1 <;> by_cases h2 : H.Adj p.2 q.2 <;>
    simp [adjMat_apply, tensorProduct, Matrix.kroneckerMap, h1, h2]

/-- **The eigenvalues of a tensor product are the products of the eigenvalues.** -/
theorem spectrum_tensorProduct (G H : CGraph) [dG : DecidableEq G.V] [dH : DecidableEq H.V] :
    (tensorProduct G H).spectrum
      = Finset.univ.val.map (fun p : G.V × H.V ↦ G.eigenvalues p.1 * H.eigenvalues p.2) := by
  have e1 : dG = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have e2 : dH = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst e1; subst e2
  obtain ⟨P₁, Q₁, h₁, h₁', e₁⟩ := exists_conj_diagonal G
  obtain ⟨P₂, Q₂, h₂, h₂', e₂⟩ := exists_conj_diagonal H
  refine spectrum_eq_of_conj (P := P₁ ⊗ₖ P₂) (Q := Q₁ ⊗ₖ Q₂) ?_ ?_ ?_
  · rw [← Matrix.mul_kronecker_mul, h₁, h₂, Matrix.one_kronecker_one]
    congr!
  · rw [← Matrix.mul_kronecker_mul, h₁', h₂', Matrix.one_kronecker_one]
    congr!
  · rw [adjMat_tensorProduct, ← Matrix.mul_kronecker_mul, e₁, e₂, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    congr!

private theorem map_product_apply₂ {α β : Type} (f : α → ℝ) (g : β → ℝ) (F : ℝ → ℝ → ℝ)
    (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map (fun p ↦ F (f p.1) (g p.2))
      = ((s.map f) ×ˢ (t.map g)).map (fun p ↦ F p.1 p.2) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp [Multiset.cons_product, Multiset.map_map, ih]

theorem spectrum_tensorProduct' (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ p.1 * p.2) := by
  rw [spectrum_tensorProduct, spectrum_eq_map, spectrum_eq_map, ← map_product_apply₂,
    ← Finset.univ_product_univ, Finset.product_val]

/-- The adjacency matrix of a cartesian product is `I ⊗ A H + A G ⊗ I`. -/
theorem adjMat_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).adjMat
      = (1 : Matrix G.V G.V ℝ) ⊗ₖ H.adjMat + G.adjMat ⊗ₖ (1 : Matrix H.V H.V ℝ) := by
  ext p q
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [adjMat_apply, cartesianProduct, Matrix.kroneckerMap, Matrix.one_apply, h1, h2,
      G.loopless, H.loopless]

/-- **The eigenvalues of a cartesian product are the sums of the eigenvalues.** -/
theorem spectrum_cartesianProduct (G H : CGraph) [dG : DecidableEq G.V] [dH : DecidableEq H.V] :
    (cartesianProduct G H).spectrum
      = Finset.univ.val.map (fun p : G.V × H.V ↦ G.eigenvalues p.1 + H.eigenvalues p.2) := by
  have e1 : dG = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have e2 : dH = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst e1; subst e2
  obtain ⟨P₁, Q₁, h₁, h₁', e₁⟩ := exists_conj_diagonal G
  obtain ⟨P₂, Q₂, h₂, h₂', e₂⟩ := exists_conj_diagonal H
  have hdiag : (1 : Matrix G.V G.V ℝ) ⊗ₖ Matrix.diagonal H.eigenvalues
      + Matrix.diagonal G.eigenvalues ⊗ₖ (1 : Matrix H.V H.V ℝ)
      = Matrix.diagonal (fun p : G.V × H.V ↦ G.eigenvalues p.1 + H.eigenvalues p.2) := by
    ext p q
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
      simp [Matrix.kroneckerMap, Matrix.one_apply, Matrix.diagonal_apply, Prod.ext_iff, h1, h2,
        add_comm]
  have key : P₁ ⊗ₖ (P₂ * Matrix.diagonal H.eigenvalues)
      + (P₁ * Matrix.diagonal G.eigenvalues) ⊗ₖ P₂
      = (P₁ ⊗ₖ P₂) * Matrix.diagonal
          (fun p : G.V × H.V ↦ G.eigenvalues p.1 + H.eigenvalues p.2) := by
    rw [← hdiag, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.mul_one]
  refine spectrum_eq_of_conj (P := P₁ ⊗ₖ P₂) (Q := Q₁ ⊗ₖ Q₂) ?_ ?_ ?_
  · rw [← Matrix.mul_kronecker_mul, h₁, h₂, Matrix.one_kronecker_one]
    congr!
  · rw [← Matrix.mul_kronecker_mul, h₁', h₂', Matrix.one_kronecker_one]
    congr!
  · rw [adjMat_cartesianProduct, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, e₁, e₂]
    simp only [Matrix.one_mul]
    rw [key]
    congr!

theorem spectrum_cartesianProduct' (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ p.1 + p.2) := by
  rw [spectrum_cartesianProduct, spectrum_eq_map, spectrum_eq_map, ← map_product_apply₂,
    ← Finset.univ_product_univ, Finset.product_val]

/-- The adjacency matrix of a strong product is `(A G + I) ⊗ (A H + I) - I`. -/
theorem adjMat_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).adjMat = (G.adjMat + 1) ⊗ₖ (H.adjMat + 1) - 1 := by
  ext p q
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    by_cases hA1 : G.Adj p.1 q.1 <;> by_cases hA2 : H.Adj p.2 q.2 <;>
    simp [adjMat_apply, strongProduct, Matrix.kroneckerMap, Matrix.one_apply, Prod.ext_iff,
      Matrix.add_apply, Matrix.sub_apply, h1, h2, hA1, hA2, G.loopless, H.loopless]

/-- **The eigenvalues of a strong product** are `(1 + λ) (1 + μ) - 1`. -/
theorem spectrum_strongProduct (G H : CGraph) [dG : DecidableEq G.V] [dH : DecidableEq H.V] :
    (strongProduct G H).spectrum
      = Finset.univ.val.map (fun p : G.V × H.V ↦
          (1 + G.eigenvalues p.1) * (1 + H.eigenvalues p.2) - 1) := by
  have e1 : dG = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have e2 : dH = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst e1; subst e2
  obtain ⟨P₁, Q₁, h₁, h₁', e₁⟩ := exists_conj_diagonal G
  obtain ⟨P₂, Q₂, h₂, h₂', e₂⟩ := exists_conj_diagonal H
  set D₁ : Matrix G.V G.V ℝ := Matrix.diagonal G.eigenvalues with hD₁
  set D₂ : Matrix H.V H.V ℝ := Matrix.diagonal H.eigenvalues with hD₂
  have hdiag : (D₁ + 1) ⊗ₖ (D₂ + 1) - (1 : Matrix (G.V × H.V) (G.V × H.V) ℝ)
      = Matrix.diagonal (fun p : G.V × H.V ↦
          (1 + G.eigenvalues p.1) * (1 + H.eigenvalues p.2) - 1) := by
    ext p q
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
      simp [hD₁, hD₂, Matrix.kroneckerMap, Matrix.one_apply, Matrix.diagonal_apply, Prod.ext_iff,
        Matrix.add_apply, Matrix.sub_apply, h1, h2]
    all_goals ring
  have key : (P₁ * D₁ + P₁) ⊗ₖ (P₂ * D₂ + P₂) - P₁ ⊗ₖ P₂
      = (P₁ ⊗ₖ P₂) * Matrix.diagonal (fun p : G.V × H.V ↦
          (1 + G.eigenvalues p.1) * (1 + H.eigenvalues p.2) - 1) := by
    rw [show P₁ * D₁ + P₁ = P₁ * (D₁ + 1) by rw [Matrix.mul_add, Matrix.mul_one],
      show P₂ * D₂ + P₂ = P₂ * (D₂ + 1) by rw [Matrix.mul_add, Matrix.mul_one],
      ← hdiag, Matrix.mul_sub, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  refine spectrum_eq_of_conj (P := P₁ ⊗ₖ P₂) (Q := Q₁ ⊗ₖ Q₂) ?_ ?_ ?_
  · rw [← Matrix.mul_kronecker_mul, h₁, h₂, Matrix.one_kronecker_one]
    congr!
  · rw [← Matrix.mul_kronecker_mul, h₁', h₂', Matrix.one_kronecker_one]
    congr!
  · rw [adjMat_strongProduct, Matrix.sub_mul, ← Matrix.mul_kronecker_mul, Matrix.add_mul,
      Matrix.add_mul, e₁, e₂]
    simp only [Matrix.one_mul]
    rw [key]
    congr!

theorem spectrum_strongProduct' (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).spectrum
      = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ (1 + p.1) * (1 + p.2) - 1) := by
  rw [spectrum_strongProduct, spectrum_eq_map, spectrum_eq_map,
    ← map_product_apply₂ G.eigenvalues H.eigenvalues (fun a b ↦ (1 + a) * (1 + b) - 1),
    ← Finset.univ_product_univ, Finset.product_val]

/-- **Powers of the adjacency matrix count walks.** -/
theorem adjMat_pow_apply (G : CGraph) [DecidableEq G.V] (n : ℕ) (u v : G.V) :
    (G.adjMat ^ n) u v = (Fintype.card {w : G.toSimple.Walk u v // w.length = n} : ℝ) := by
  rw [adjMat, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  rfl

/-! ## Traces: the order and the size are read off the spectrum -/

/-- **The eigenvalues sum to zero**, because the adjacency matrix has zero diagonal. -/
@[simp, toIsoGraph] theorem sum_spectrum (G : CGraph) : G.spectrum.sum = 0 := by
  classical
  have h1 : G.adjMat.trace = ∑ i, G.eigenvalues i :=
    G.isHermitian_adjMat.trace_eq_sum_eigenvalues
  have h2 : G.adjMat.trace = 0 := SimpleGraph.trace_adjMatrix (α := ℝ) _
  rw [spectrum_eq_map]
  exact h1.symm.trans h2

/-- **The trace of `A ^ n` is the `n`-th power sum of the eigenvalues.**  A conjugation that
diagonalises `A` diagonalises every power of it. -/
theorem trace_adjMat_pow (G : CGraph) (n : ℕ) :
    (G.adjMat ^ n).trace = ∑ i, G.eigenvalues i ^ n := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_conj_diagonal G
  set D : Matrix G.V G.V ℝ := Matrix.diagonal G.eigenvalues with hD
  have hA : G.adjMat = P * D * Q := by
    calc G.adjMat = G.adjMat * (P * Q) := by rw [hPQ, mul_one]
      _ = G.adjMat * P * Q := by rw [mul_assoc]
      _ = P * D * Q := by rw [h]
  have hpow : ∀ m : ℕ, G.adjMat ^ m = P * D ^ m * Q := by
    intro m
    induction m with
    | zero => simp [hPQ]
    | succ m ih =>
      rw [pow_succ, ih, hA, pow_succ]
      calc P * D ^ m * Q * (P * D * Q) = P * D ^ m * (Q * P) * D * Q := by
            simp only [mul_assoc]
        _ = P * (D ^ m * D) * Q := by rw [hQP]; simp only [mul_assoc, mul_one]
        _ = P * (D ^ m * D) * Q := rfl
  calc (G.adjMat ^ n).trace = (P * D ^ n * Q).trace := by rw [hpow]
    _ = (Q * (P * D ^ n)).trace := by rw [Matrix.trace_mul_comm]
    _ = (D ^ n).trace := by rw [← mul_assoc, hQP, one_mul]
    _ = ∑ i, G.eigenvalues i ^ n := by
        rw [hD, Matrix.diagonal_pow, Matrix.trace_diagonal]
        rfl

theorem trace_adjMat_sq (G : CGraph) :
    (G.adjMat * G.adjMat).trace = ∑ i, (G.eigenvalues i) ^ 2 := by
  rw [← pow_two]
  exact trace_adjMat_pow G 2

/-- **The sum of the squares of the eigenvalues is the sum of the degrees.** -/
theorem sum_sq_spectrum_eq_sum_degrees (G : CGraph) :
    (G.spectrum.map (· ^ 2)).sum = ∑ i, (G.toSimple.degree i : ℝ) := by
  classical
  have h0 : (G.spectrum.map (· ^ 2)).sum = ∑ i, (G.eigenvalues i) ^ 2 := by
    rw [spectrum_eq_map, Multiset.map_map]
    simp only [Finset.sum, Function.comp_def]
  have h : ∀ i, (G.adjMat * G.adjMat) i i = (G.toSimple.degree i : ℝ) := fun i ↦ by
    simpa [adjMat] using SimpleGraph.adjMatrix_mul_self_apply_self (α := ℝ) G.toSimple i
  rw [h0, ← trace_adjMat_sq, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ ↦ h i

/-- **The sum of the squares of the eigenvalues is twice the number of edges.** -/
@[toIsoGraph]
theorem sum_sq_spectrum (G : CGraph) : (G.spectrum.map (· ^ 2)).sum = 2 * (G.E : ℝ) := by
  classical
  have hE : G.E = G.toSimple.edgeFinset.card := rfl
  rw [sum_sq_spectrum_eq_sum_degrees, ← Nat.cast_sum,
    SimpleGraph.sum_degrees_eq_twice_card_edges, hE]
  push_cast
  ring

/-- **The `n`-th moment of the spectrum is the trace of `A ^ n`.** -/
theorem sum_pow_spectrum (G : CGraph) (n : ℕ) :
    (G.spectrum.map (· ^ n)).sum = (G.adjMat ^ n).trace := by
  rw [trace_adjMat_pow, spectrum_eq_map, Multiset.map_map]
  simp only [Finset.sum, Function.comp_def]

/-- **The `n`-th moment of the spectrum counts closed walks of length `n`.** -/
theorem sum_pow_spectrum_eq_card_closedWalks (G : CGraph) (n : ℕ) :
    (G.spectrum.map (· ^ n)).sum
      = ∑ v : G.V, (Fintype.card {w : G.toSimple.Walk v v // w.length = n} : ℝ) := by
  classical
  rw [sum_pow_spectrum, Matrix.trace]
  exact Finset.sum_congr rfl fun v _ ↦ adjMat_pow_apply G n v v

/-! ### The third moment counts triangles -/

/-- The ordered triples of mutually adjacent vertices. -/
private def orderedTriangles (G : CGraph) : Finset (G.V × G.V × G.V) :=
  Finset.univ.filter fun t ↦
    G.toSimple.Adj t.1 t.2.1 ∧ G.toSimple.Adj t.2.1 t.2.2 ∧ G.toSimple.Adj t.2.2 t.1

private theorem trace_adjMat_cube (G : CGraph) :
    (G.adjMat ^ 3).trace = (G.orderedTriangles.card : ℝ) := by
  have hterm : ∀ i k j : G.V, G.adjMat i j * G.adjMat j k * G.adjMat k i
      = if G.toSimple.Adj i j ∧ G.toSimple.Adj j k ∧ G.toSimple.Adj k i then 1 else 0 := by
    intro i k j
    simp only [adjMat_apply, ← toSimple_adj]
    by_cases h1 : G.Adj i j <;> by_cases h2 : G.Adj j k <;> by_cases h3 : G.Adj k i <;>
      simp [h1, h2, h3]
  have h3 : G.adjMat ^ 3 = G.adjMat * G.adjMat * G.adjMat := by
    rw [pow_succ, pow_succ, pow_one]
  rw [h3]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [orderedTriangles, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ hterm i j k

private theorem card_orderedTriangles (G : CGraph) :
    G.orderedTriangles.card = 6 * (G.toSimple.cliqueFinset 3).card := by
  rw [orderedTriangles,
    Finset.card_eq_sum_card_fiberwise (f := fun t : G.V × G.V × G.V ↦ ({t.1, t.2.1, t.2.2} :
      Finset G.V)) (t := G.toSimple.cliqueFinset 3) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ ↦ 6) ?_, Finset.sum_const, smul_eq_mul, mul_comm]
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      SimpleGraph.is3Clique_iff.1 (SimpleGraph.mem_cliqueFinset_iff.1 hs)
    have hset : (Finset.univ.filter fun t : G.V × G.V × G.V ↦
          (G.toSimple.Adj t.1 t.2.1 ∧ G.toSimple.Adj t.2.1 t.2.2 ∧ G.toSimple.Adj t.2.2 t.1) ∧
            ({t.1, t.2.1, t.2.2} : Finset G.V) = {a, b, c})
        = {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} := by
      ext ⟨x, y, z⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hxy, hyz, hzx⟩, heq⟩
        have hx : x ∈ ({a, b, c} : Finset G.V) := heq ▸ (by simp)
        have hy : y ∈ ({a, b, c} : Finset G.V) := heq ▸ (by simp)
        have hz : z ∈ ({a, b, c} : Finset G.V) := heq ▸ (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          rcases hz with rfl | rfl | rfl <;> simp_all
      · have hba := hab.symm
        have hca := hac.symm
        have hcb := hbc.symm
        rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
          refine ⟨⟨by assumption, by assumption, by assumption⟩, ?_⟩ <;>
          (ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    rw [Finset.filter_filter, hset]
    have h1 : a ≠ b := hab.ne
    have h2 : a ≠ c := hac.ne
    have h3 : b ≠ c := hbc.ne
    rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff, h1, h2, h3, h1.symm, h2.symm,
        h3.symm]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff, h1, h2, h3, h1.symm, h2.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff, h1, h2, h3, h2.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff, h1, h3, h2.symm, h3.symm]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff, h1, h1.symm]),
      Finset.card_singleton]
  · rintro ⟨x, y, z⟩ ht
    have ht' : G.toSimple.Adj x y ∧ G.toSimple.Adj y z ∧ G.toSimple.Adj z x := by simpa using ht
    exact SimpleGraph.mem_cliqueFinset_iff.2
      (SimpleGraph.is3Clique_triple_iff.2 ⟨ht'.1, ht'.2.2.symm, ht'.2.1⟩)

/-- **The third moment counts triangles.**  The trace of `A ³` counts closed walks of length
three, and each triangle contributes six of them, one for each ordering of its vertices. -/
@[toIsoGraph]
theorem sum_cube_spectrum (G : CGraph) :
    (G.spectrum.map (· ^ 3)).sum = 6 * (G.cliqueCount 3 : ℝ) := by
  rw [sum_pow_spectrum, trace_adjMat_cube, card_orderedTriangles,
    G.cliqueCount_eq_card_cliqueFinset 3]
  push_cast
  ring

/-! ### Bipartite graphs have a symmetric spectrum -/

/-- **The spectrum of a bipartite graph is symmetric about zero.**  Flipping the sign of one side
of the bipartition conjugates `A` into `-A`, so `A` is similar to minus itself. -/
theorem spectrum_neg_of_isBipartite {G : CGraph} (h : G.IsBipartite) :
    G.spectrum.map (fun x ↦ -x) = G.spectrum := by
  classical
  obtain ⟨c, hc⟩ := h
  set s : G.V → ℝ := fun i ↦ if c i then 1 else -1 with hs
  set S : Matrix G.V G.V ℝ := Matrix.diagonal s with hS
  have hSS : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hci : c i <;> simp [hs, hci]
  have hAS : G.adjMat * S = -(S * G.adjMat) := by
    ext i j
    rw [hS]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
    by_cases hij : G.Adj i j
    · have hsum : s i + s j = 0 := by
        have := hc i j hij
        by_cases hci : c i <;> by_cases hcj : c j <;> simp_all
      linear_combination G.adjMat i j * hsum
    · simp [adjMat_apply, hij]
  obtain ⟨P, Q, hPQ, hQP, hcon⟩ := exists_conj_diagonal G
  have hneg : Matrix.diagonal (fun i ↦ -G.eigenvalues i) = -Matrix.diagonal G.eigenvalues :=
    (Matrix.diagonal_neg _).symm
  have key : G.spectrum = Finset.univ.val.map (fun i ↦ -G.eigenvalues i) := by
    refine spectrum_eq_of_conj (P := S * P) (Q := Q * S) ?_ ?_ ?_
    · calc S * P * (Q * S) = S * (P * Q) * S := by simp only [mul_assoc]
        _ = 1 := by rw [hPQ, mul_one, hSS]
    · calc Q * S * (S * P) = Q * (S * S) * P := by simp only [mul_assoc]
        _ = 1 := by rw [hSS, mul_one, hQP]
    · calc G.adjMat * (S * P) = G.adjMat * S * P := by rw [mul_assoc]
        _ = -(S * G.adjMat) * P := by rw [hAS]
        _ = -(S * (G.adjMat * P)) := by rw [neg_mul, mul_assoc]
        _ = -(S * (P * Matrix.diagonal G.eigenvalues)) := by rw [hcon]
        _ = S * P * Matrix.diagonal (fun i ↦ -G.eigenvalues i) := by
            rw [hneg, Matrix.mul_neg, ← mul_assoc]
  conv_lhs => rw [spectrum_eq_map]
  rw [Multiset.map_map]
  simpa [Function.comp_def] using key.symm

/-! ## The multiplicities of a strongly regular graph -/

/-- **The parameter identity of a strongly regular graph**, `k (k - ℓ - 1) = (n - k - 1) μ`, in
the form the spectrum needs it: apply `A ^ 2 = k I + ℓ A + μ (J - I - A)` to the all-ones
vector. -/
theorem sq_degree_of_isSRGWith {G : CGraph} [DecidableEq G.V] [Nonempty G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) : (k : ℝ) ^ 2 = k + l * k + m * ((n : ℝ) - 1 - k) := by
  obtain ⟨i₀⟩ := ‹Nonempty G.V›
  have hone : G.adjMat *ᵥ (fun _ ↦ (1 : ℝ)) = (k : ℝ) • (fun _ ↦ (1 : ℝ)) :=
    (hasEigenvector_one_of_isRegularWith h.regular).2
  have hmat : G.adjMat * G.adjMat
      = (k : ℝ) • 1 + (l : ℝ) • G.adjMat + (m : ℝ) • (G.toSimpleᶜ.adjMatrix ℝ) := by
    have hme := h.matrix_eq (α := ℝ)
    rw [pow_two] at hme
    simpa [adjMat, Nat.cast_smul_eq_nsmul] using hme
  have hcompl : (G.toSimpleᶜ.adjMatrix ℝ) *ᵥ (fun _ ↦ (1 : ℝ))
      = ((n : ℝ) - 1 - k) • (fun _ ↦ (1 : ℝ)) := by
    rw [compl_adjMatrix_eq, Matrix.sub_mulVec, Matrix.sub_mulVec, hone, Matrix.one_mulVec]
    funext i
    have hcard : (Fintype.card G.V : ℝ) = n := by rw [h.card]
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Finset.card_univ, hcard]
  have hsq : (G.adjMat * G.adjMat) *ᵥ (fun _ ↦ (1 : ℝ)) = ((k : ℝ) ^ 2) • (fun _ ↦ (1 : ℝ)) := by
    rw [← Matrix.mulVec_mulVec, hone, Matrix.mulVec_smul, hone, smul_smul, ← pow_two]
  have key : ((k : ℝ) ^ 2) • (fun _ : G.V ↦ (1 : ℝ))
      = ((k : ℝ) + l * k + m * ((n : ℝ) - 1 - k)) • (fun _ : G.V ↦ (1 : ℝ)) := by
    rw [← hsq, hmat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hone, hcompl]
    module
  simpa using congrFun key i₀

/-- **The spectrum of a strongly regular graph, with multiplicities.**  Given the two roots `r`
and `s` of `x ^ 2 = (ℓ - μ) x + (k - μ)`, an `srg(n, k, ℓ, μ)` with `μ > 0` has spectrum `k` once
and `r`, `s` with multiplicities `f` and `g` determined by `f + g + 1 = n` and `k + f r + g s = 0`
(the trace conditions).  That the degree occurs exactly once is `(k - r) (k - s) = n μ`, the
parameter identity. -/
theorem spectrum_isSRGWith {G : CGraph} [DecidableEq G.V] [Nonempty G.V] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) (hm : 0 < m) {r s : ℝ} (hrs : r + s = (l : ℝ) - m)
    (hprod : r * s = -((k : ℝ) - m)) (hne : r ≠ s) :
    ∃ f g : ℕ, f + g + 1 = n ∧ (k : ℝ) + f * r + g * s = 0 ∧
      G.spectrum = (k : ℝ) ::ₘ (Multiset.replicate f r + Multiset.replicate g s) := by
  have hn : 0 < n := h.card ▸ Fintype.card_pos
  -- the parameter identity, in the form `(k - r) (k - s) = n μ`
  have hkrs : ((k : ℝ) - r) * ((k : ℝ) - s) = (n : ℝ) * m := by
    linear_combination sq_degree_of_isSRGWith h - (k : ℝ) * hrs + hprod
  have hpos : (0 : ℝ) < (n : ℝ) * m := by positivity
  have hkr : (k : ℝ) ≠ r := by
    intro hc
    rw [← hc] at hkrs
    simp at hkrs
    omega
  have hks : (k : ℝ) ≠ s := by
    intro hc
    rw [← hc] at hkrs
    simp at hkrs
    omega
  -- every eigenvalue is `k`, `r` or `s`
  have htri : ∀ x ∈ G.spectrum, x = (k : ℝ) ∨ x = r ∨ x = s := by
    intro x hx
    by_cases hxk : x = (k : ℝ)
    · exact Or.inl hxk
    · have hq := sq_eq_of_isSRGWith_of_ne h hxk ((G.mem_spectrum_iff x).1 hx)
      have : (x - r) * (x - s) = 0 := by linear_combination hq - x * hrs + hprod
      rcases mul_eq_zero.1 this with hc | hc
      · exact Or.inr (Or.inl (sub_eq_zero.1 hc))
      · exact Or.inr (Or.inr (sub_eq_zero.1 hc))
  set e : ℕ := G.spectrum.count (k : ℝ) with he
  set f : ℕ := G.spectrum.count r with hf
  set g : ℕ := G.spectrum.count s with hg
  have hdec : G.spectrum = Multiset.replicate e (k : ℝ)
      + Multiset.replicate f r + Multiset.replicate g s := by
    refine Multiset.ext.2 fun x ↦ ?_
    simp only [Multiset.count_add, Multiset.count_replicate, he, hf, hg]
    by_cases hxk : x = (k : ℝ)
    · subst hxk
      simp [Ne.symm hkr, Ne.symm hks]
    · by_cases hxr : x = r
      · subst hxr
        simp [hkr, Ne.symm hne]
      · by_cases hxs : x = s
        · subst hxs
          simp [hks, hne]
        · have : x ∉ G.spectrum := fun hx ↦ by
            rcases htri x hx with hc | hc | hc <;> simp_all
          simp [Multiset.count_eq_zero.2 this, Ne.symm hxk, Ne.symm hxr, Ne.symm hxs]
  -- the three moment equations
  have hcard : (e : ℝ) + f + g = n := by
    have h1 := congrArg Multiset.card hdec
    rw [card_spectrum, h.card] at h1
    simp only [Multiset.card_add, Multiset.card_replicate] at h1
    exact_mod_cast h1.symm
  have hsum0 : (e : ℝ) * k + f * r + g * s = 0 := by
    have h1 := congrArg Multiset.sum hdec
    rw [G.sum_spectrum] at h1
    simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul] at h1
    linarith [h1]
  have hsq2 : (e : ℝ) * k ^ 2 + f * r ^ 2 + g * s ^ 2 = (n : ℝ) * k := by
    have h1 := G.sum_sq_spectrum_eq_sum_degrees
    have hdeg : ∑ _i : G.V, ((k : ℕ) : ℝ) = (n : ℝ) * k := by
      simp [Finset.card_univ, h.card]
    have h2 : ∑ i, (G.toSimple.degree i : ℝ) = (n : ℝ) * k := by
      rw [← hdeg]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [h.regular i]
    rw [h2, hdec] at h1
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, nsmul_eq_mul] at h1
    linarith [h1]
  -- the degree occurs exactly once
  have hone : (e : ℝ) = 1 := by
    have hkey : (e : ℝ) * (((k : ℝ) - r) * ((k : ℝ) - s)) = (n : ℝ) * m := by
      linear_combination hsq2 - (r + s) * hsum0 + (r * s) * hcard + (n : ℝ) * hprod
    rw [hkrs] at hkey
    rcases mul_eq_zero.1 (by linarith : ((e : ℝ) - 1) * ((n : ℝ) * m) = 0) with hc | hc
    · linarith
    · exact absurd hc (ne_of_gt hpos)
  have he1 : e = 1 := by exact_mod_cast hone
  rw [hone] at hcard hsum0
  refine ⟨f, g, ?_, ?_, ?_⟩
  · have : (f : ℝ) + g + 1 = n := by linarith
    exact_mod_cast this
  · linarith
  · rw [hdec, he1, Multiset.replicate_one, add_assoc]
    rfl

/-- **The integrality condition for strongly regular parameters.**  Either the two non-degree
eigenvalues are integers, or `2 k + (n - 1) (ℓ - μ) = 0` — the *conference graph* case, where `r`
and `s` are irrational conjugates.  The multiplicities `f` and `g` decide which: eliminating `s`
from `k + f r + g s = 0` gives `(f - g) r = -(k + g (ℓ - μ))`, so if `f ≠ g` then `r` is rational
and hence an integer, while if `f = g` the same equation is the conference identity. -/
theorem int_or_conference_of_isSRGWith {G : CGraph} [DecidableEq G.V] [Nonempty G.V]
    {n k l m : ℕ} (h : G.IsSRGWith n k l m) (hm : 0 < m) {r s : ℝ}
    (hrs : r + s = (l : ℝ) - m) (hprod : r * s = -((k : ℝ) - m)) (hne : r ≠ s) :
    (∃ a b : ℤ, r = a ∧ s = b) ∨ 2 * (k : ℝ) + ((n : ℝ) - 1) * ((l : ℝ) - m) = 0 := by
  obtain ⟨f, g, hfg, htr, hspec⟩ := spectrum_isSRGWith h hm hrs hprod hne
  have hn : (n : ℝ) = (f : ℝ) + g + 1 := by exact_mod_cast hfg.symm
  by_cases hfe : (f : ℝ) = (g : ℝ)
  · right
    linear_combination (2 : ℝ) * htr - ((f : ℝ) + g) * hrs + (s - r) * hfe + ((l : ℝ) - m) * hn
  · left
    have hd : (f : ℝ) - g ≠ 0 := sub_ne_zero.2 hfe
    obtain ⟨qr, hqr⟩ : ∃ q : ℚ, (q : ℝ) = r :=
      ⟨-((k : ℚ) + g * ((l : ℚ) - m)) / ((f : ℚ) - g), by
        push_cast
        rw [div_eq_iff hd]
        linear_combination -htr + (g : ℝ) * hrs⟩
    obtain ⟨qs, hqs⟩ : ∃ q : ℚ, (q : ℝ) = s :=
      ⟨((l : ℚ) - m) - qr, by push_cast; rw [hqr]; linarith⟩
    have hspecr : f ≠ 0 → r ∈ G.spectrum := fun hf ↦ by
      rw [hspec]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨hf, rfl⟩)))
    have hspecs : g ≠ 0 → s ∈ G.spectrum := fun hg ↦ by
      rw [hspec]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨hg, rfl⟩)))
    have hmain : ∃ a : ℤ, r = (a : ℝ) := by
      by_cases hf : f = 0
      · have hg : g ≠ 0 := fun hg0 ↦ hfe (by rw [hf, hg0])
        obtain ⟨b, hb⟩ :=
          G.exists_intCast_eq_of_ratCast_mem_spectrum (q := qs) (by rw [hqs]; exact hspecs hg)
        exact ⟨(l : ℤ) - m - b, by push_cast; rw [hb, hqs]; linarith⟩
      · obtain ⟨a, ha⟩ :=
          G.exists_intCast_eq_of_ratCast_mem_spectrum (q := qr) (by rw [hqr]; exact hspecr hf)
        exact ⟨a, by rw [ha, hqr]⟩
    obtain ⟨a, ha⟩ := hmain
    exact ⟨a, (l : ℤ) - m - a, ha, by push_cast; rw [← ha]; linarith⟩

/-- The integrality condition in its textbook form: for a strongly regular graph the discriminant
`(ℓ - μ) ² + 4 (k - μ)` is a perfect square, unless `2 k + (n - 1) (ℓ - μ) = 0`. -/
theorem isSquare_discrim_or_conference_of_isSRGWith {G : CGraph} [DecidableEq G.V] [Nonempty G.V]
    {n k l m : ℕ} (h : G.IsSRGWith n k l m) (hm : 0 < m)
    (hD : 0 < ((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m)) :
    (∃ d : ℤ, ((l : ℤ) - m) ^ 2 + 4 * ((k : ℤ) - m) = d ^ 2)
      ∨ 2 * (k : ℤ) + ((n : ℤ) - 1) * ((l : ℤ) - m) = 0 := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((l : ℝ) - m) ^ 2 + 4 * ((k : ℝ) - m) := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  have hpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hrs : (((l : ℝ) - m) + Real.sqrt D) / 2 + (((l : ℝ) - m) - Real.sqrt D) / 2
      = (l : ℝ) - m := by ring
  have hprod : (((l : ℝ) - m) + Real.sqrt D) / 2 * ((((l : ℝ) - m) - Real.sqrt D) / 2)
      = -((k : ℝ) - m) := by
    have h1 : (((l : ℝ) - m) + Real.sqrt D) / 2 * ((((l : ℝ) - m) - Real.sqrt D) / 2)
        = (((l : ℝ) - m) ^ 2 - Real.sqrt D ^ 2) / 4 := by ring
    rw [h1, hsq, hDdef]
    ring
  have hne : (((l : ℝ) - m) + Real.sqrt D) / 2 ≠ (((l : ℝ) - m) - Real.sqrt D) / 2 := by
    intro hc
    linarith
  rcases int_or_conference_of_isSRGWith h hm hrs hprod hne with ⟨a, b, ha, hb⟩ | hc
  · left
    refine ⟨a - b, ?_⟩
    have h1 : Real.sqrt D = ((a - b : ℤ) : ℝ) := by
      push_cast
      rw [← ha, ← hb]
      ring
    have h2 : ((((l : ℤ) - m) ^ 2 + 4 * ((k : ℤ) - m) : ℤ) : ℝ) = (((a - b : ℤ) : ℝ)) ^ 2 := by
      rw [← h1, hsq, hDdef]
      push_cast
      ring
    exact_mod_cast h2
  · right
    exact_mod_cast hc

/-- **The Hoffman–Singleton parameter theorem.** A Moore graph of diameter `2` and girth `5` is
a strongly regular graph with parameters `srg(k ^ 2 + 1, k, 0, 1)`, and its degree can only be
`2`, `3`, `7` or `57` — realised by the pentagon, the Petersen graph and the Hoffman–Singleton
graph, with the case `k = 57` still open.

The proof is pure arithmetic on top of `int_or_conference_of_isSRGWith`. The eigenvalues other
than `k` are the roots of `x ^ 2 + x - (k - 1)`, so the discriminant is `4 k - 3`. In the
conference case `2 k + k ^ 2 * (0 - 1) = 0` forces `k = 2`. Otherwise `√(4 k - 3)` is a positive
integer `c`, the multiplicity equation reads `(f - g) c = k ^ 2 - 2 k`, and eliminating `k` via
`c ^ 2 = 4 k - 3` turns it into `16 (f - g) c = c ^ 4 - 2 c ^ 2 - 15`; hence `c ∣ 15`, so
`c ∈ {1, 3, 5, 15}` and `k = (c ^ 2 + 3) / 4 ∈ {1, 3, 7, 57}`. -/
theorem degree_of_isSRGWith_moore {G : CGraph} [DecidableEq G.V] {k : ℕ} (hk : 2 ≤ k)
    (h : G.IsSRGWith (k ^ 2 + 1) k 0 1) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  haveI : Nonempty G.V := Fintype.card_pos_iff.1 (by rw [h.card]; positivity)
  have hk0 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.sqrt (4 * (k : ℝ) - 3) := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd]
    exact Real.sqrt_pos.2 (by linarith)
  have hdsq : d ^ 2 = 4 * (k : ℝ) - 3 := by
    rw [hd]
    exact Real.sq_sqrt (by linarith)
  have hrs : (-1 + d) / 2 + (-1 - d) / 2 = ((0 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hprod : (-1 + d) / 2 * ((-1 - d) / 2) = -(((k : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) := by
    push_cast
    linear_combination (-1 / 4 : ℝ) * hdsq
  have hne : (-1 + d) / 2 ≠ (-1 - d) / 2 := by
    intro hc
    linarith
  -- the order and the trace pin down the two multiplicities
  obtain ⟨f, g, h1, h2, -⟩ := spectrum_isSRGWith h (by norm_num) hrs hprod hne
  have h1' : (f : ℝ) + g + 1 = (k : ℝ) ^ 2 + 1 := by exact_mod_cast h1
  have hlin : ((f : ℝ) - g) * d = (k : ℝ) ^ 2 - 2 * k := by linear_combination 2 * h2 + h1'
  rcases int_or_conference_of_isSRGWith h (by norm_num) hrs hprod hne with ⟨a, b, ha, hb⟩ | hconf
  · -- the discriminant is a perfect square, so `d` is a positive integer, and it divides `15`
    obtain ⟨c, hc⟩ : ∃ c : ℤ, ((c : ℤ) : ℝ) = d :=
      ⟨a - b, by push_cast; rw [← ha, ← hb]; ring⟩
    have hc0 : 0 < c := by
      have h0 : (0 : ℝ) < ((c : ℤ) : ℝ) := by rw [hc]; exact hd0
      exact_mod_cast h0
    have hcsq : c * c = 4 * (k : ℤ) - 3 := by
      have h0 : ((c : ℤ) : ℝ) * ((c : ℤ) : ℝ) = 4 * (k : ℝ) - 3 := by
        rw [hc]
        linear_combination hdsq
      exact_mod_cast h0
    have hlin' : ((f : ℤ) - g) * c = (k : ℤ) ^ 2 - 2 * k := by
      have h0 : ((f : ℝ) - g) * ((c : ℤ) : ℝ) = (k : ℝ) ^ 2 - 2 * k := by rw [hc]; exact hlin
      exact_mod_cast h0
    have hdvd : c ∣ 15 :=
      ⟨c ^ 3 - 2 * c - 16 * ((f : ℤ) - g), by
        linear_combination (16 : ℤ) * hlin' + (5 - c * c - 4 * (k : ℤ)) * hcsq⟩
    have hk' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    -- the four positive divisors of `15` leave only `k ∈ {3, 7, 57}`
    have hfin : ∀ e n : ℤ, 0 < e → e ∣ 15 → e * e = 4 * n - 3 → 2 ≤ n →
        n = 2 ∨ n = 3 ∨ n = 7 ∨ n = 57 := by
      intro e n he0 hdv hesq hn
      have hele : e ≤ 15 := Int.le_of_dvd (by norm_num) hdv
      interval_cases e <;> omega
    have := hfin c (k : ℤ) hc0 hdvd hcsq hk'
    omega
  · -- the conference case forces `2 k = k ^ 2`, so `k = 2`
    left
    push_cast at hconf
    have h0 : (k : ℝ) * ((k : ℝ) - 2) = 0 := by linear_combination -hconf
    rcases mul_eq_zero.1 h0 with hc | hc
    · linarith
    · exact_mod_cast (by linarith : (k : ℝ) = 2)

/-- **The spectrum of the Petersen graph**: `3` once, `1` five times, `-2` four times. -/
theorem spectrum_petersen :
    SRG.petersen.spectrum = 3 ::ₘ (Multiset.replicate 5 1 + Multiset.replicate 4 (-2)) := by
  haveI : Nonempty SRG.petersen.V :=
    Fintype.card_pos_iff.1 (by rw [SRG.petersen_srg.card]; norm_num)
  obtain ⟨f, g, h1, h2, h3⟩ :=
    spectrum_isSRGWith SRG.petersen_srg (by norm_num) (r := 1) (s := -2)
      (by norm_num) (by norm_num) (by norm_num)
  have h2' : (f : ℝ) + 3 = 2 * g := by push_cast at h2; linarith
  have h2'' : f + 3 = 2 * g := by exact_mod_cast h2'
  have hf : f = 5 := by omega
  have hg : g = 4 := by omega
  subst hf; subst hg
  rw [h3]
  norm_num

/-- **The spectrum of the cocktail party graph `K_{n×2}`**: `2n - 2` once, `0` with multiplicity
`n` and `-2` with multiplicity `n - 1`. -/
theorem spectrum_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).spectrum
      = (2 * (m : ℝ) + 2) ::ₘ (Multiset.replicate (m + 2) 0 + Multiset.replicate (m + 1) (-2)) := by
  have hsrg := isSRGWith_cocktailParty (m + 2)
  rw [show 2 * (m + 2) - 2 = 2 * m + 2 from by omega,
    show 2 * (m + 2) - 4 = 2 * m from by omega] at hsrg
  haveI : Nonempty (cocktailParty (m + 2)).V :=
    Fintype.card_pos_iff.1 (by rw [hsrg.card]; omega)
  obtain ⟨f, g, h1, h2, h3⟩ := spectrum_isSRGWith hsrg (by omega) (r := 0) (s := -2)
    (by push_cast; ring) (by push_cast; ring) (by norm_num)
  have h1' : (f : ℝ) + g + 1 = 2 * (m + 2) := by exact_mod_cast h1
  push_cast at h2
  have hg : (g : ℝ) = m + 1 := by linarith
  have hf : (f : ℝ) = m + 2 := by linarith
  have hgn : g = m + 1 := by exact_mod_cast hg
  have hfn : f = m + 2 := by exact_mod_cast hf
  rw [h3, hfn, hgn]
  push_cast
  ring_nf

/-- **The spectrum of the rook's graph `K_n □ K_n`**: the degree `2n - 2` once, `n - 2` with
multiplicity `2 (n - 1)`, and `-2` with multiplicity `(n - 1) ²`. -/
theorem spectrum_rook (k : ℕ) :
    (rook (k + 2) (k + 2)).spectrum
      = (2 * (k : ℝ) + 2) ::ₘ (Multiset.replicate (2 * (k + 1)) (k : ℝ)
          + Multiset.replicate ((k + 1) ^ 2) (-2)) := by
  have hsrg := isSRGWith_rook (k + 2)
  rw [show 2 * (k + 2 - 1) = 2 * k + 2 from by omega,
    show k + 2 - 2 = k from by omega] at hsrg
  haveI : Nonempty (rook (k + 2) (k + 2)).V :=
    Fintype.card_pos_iff.1 (by rw [hsrg.card]; positivity)
  obtain ⟨f, g, h1, h2, h3⟩ := spectrum_isSRGWith hsrg (by omega) (r := (k : ℝ)) (s := -2)
    (by push_cast; ring) (by push_cast; ring)
    (by have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; exact ne_of_gt (by linarith))
  have h1' : (f : ℝ) + g + 1 = (k + 2) * (k + 2) := by exact_mod_cast h1
  push_cast at h2
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hf : (f : ℝ) = 2 * (k + 1) := by
    have := mul_right_cancel₀ hk2 (show (f : ℝ) * (k + 2) = (2 * (k + 1)) * (k + 2) by
      linear_combination 2 * h1' + h2)
    exact this
  have hg : (g : ℝ) = (k + 1) ^ 2 := by
    rw [hf] at h1'
    linarith [h1', sq_nonneg ((k : ℝ) + 1)]
  have hfn : f = 2 * (k + 1) := by exact_mod_cast hf
  have hgn : g = (k + 1) ^ 2 := by exact_mod_cast hg
  rw [h3, hfn, hgn]
  push_cast
  ring_nf

/-- **The spectrum of the triangular graph `T(n) = L(Kₙ)`**: the degree `2 (n - 2)` once, `n - 4`
with multiplicity `n - 1`, and `-2` with multiplicity `C(n, 2) - n`. -/
theorem spectrum_triangular (m : ℕ) :
    (triangular (m + 4)).spectrum
      = (2 * (m : ℝ) + 4) ::ₘ (Multiset.replicate (m + 3) (m : ℝ)
          + Multiset.replicate ((m + 4).choose 2 - (m + 4)) (-2)) := by
  have hsrg := isSRGWith_triangular (m + 4) (by omega)
  rw [show 2 * (m + 4 - 2) = 2 * m + 4 from by omega,
    show m + 4 - 2 = m + 2 from by omega] at hsrg
  haveI : Nonempty (triangular (m + 4)).V :=
    Fintype.card_pos_iff.1 (by rw [hsrg.card]; exact Nat.choose_pos (by omega))
  obtain ⟨f, g, h1, h2, h3⟩ := spectrum_isSRGWith hsrg (by omega) (r := (m : ℝ)) (s := -2)
    (by push_cast; ring) (by push_cast; ring)
    (by have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; exact ne_of_gt (by linarith))
  have hN : (((m + 4).choose 2 : ℕ) : ℝ) = ((m : ℝ) + 4) * ((m : ℝ) + 3) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have h1' : (f : ℝ) + g + 1 = ((m : ℝ) + 4) * ((m : ℝ) + 3) / 2 := by
    rw [← hN]; exact_mod_cast h1
  push_cast at h2
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hf : (f : ℝ) = m + 3 :=
    mul_right_cancel₀ hm2 (show (f : ℝ) * (m + 2) = ((m : ℝ) + 3) * (m + 2) by
      linear_combination 2 * h1' + h2)
  have hfn : f = m + 3 := by exact_mod_cast hf
  have hgn : g = (m + 4).choose 2 - (m + 4) := by omega
  rw [h3, hfn, hgn]
  push_cast
  ring_nf

/-- **The spectrum of the Paley graph** `P(q)` for a prime `q = 4t + 1`: the degree `2t` once, and
the two conjugates `(-1 ± √q) / 2`, each with multiplicity `2t`.  This is the conference case of
`int_or_conference_of_isSRGWith` — the one family here whose eigenvalues are irrational, and the
reason the two multiplicities have to agree: `k + f r + g s = 0` reads `(f - g) √q = 0`. -/
theorem spectrum_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).spectrum
      = (2 * (t : ℝ)) ::ₘ
        (Multiset.replicate (2 * t) ((-1 + Real.sqrt (4 * (t : ℝ) + 1)) / 2)
          + Multiset.replicate (2 * t) ((-1 - Real.sqrt (4 * (t : ℝ) + 1)) / 2)) := by
  haveI : NeZero (4 * t + 1) := ⟨by omega⟩
  have hsrg := isSRGWith_paley (4 * t + 1) (by omega)
  rw [show (4 * t + 1 - 1) / 2 = 2 * t from by omega,
    show (4 * t + 1 - 5) / 4 = t - 1 from by omega,
    show (4 * t + 1 - 1) / 4 = t from by omega] at hsrg
  haveI : Nonempty (paley (4 * t + 1)).V :=
    Fintype.card_pos_iff.1 (by rw [hsrg.card]; omega)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt (4 * (t : ℝ) + 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hq]
    exact Real.sqrt_pos.2 (by positivity)
  have hqsq : q ^ 2 = 4 * (t : ℝ) + 1 := by
    rw [hq]
    exact Real.sq_sqrt (by positivity)
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht]
    norm_num
  obtain ⟨f, g, h1, h2, h3⟩ := spectrum_isSRGWith hsrg (by omega)
    (r := (-1 + q) / 2) (s := (-1 - q) / 2)
    (by rw [hcast]; ring)
    (by push_cast; linear_combination (-1 / 4 : ℝ) * hqsq)
    (by intro hc; linarith)
  have h1' : (f : ℝ) + g + 1 = 4 * (t : ℝ) + 1 := by exact_mod_cast h1
  push_cast at h2
  have hkey : ((f : ℝ) - g) * q = 0 := by linear_combination 2 * h2 + h1'
  have hfg : (f : ℝ) = g := by
    rcases mul_eq_zero.1 hkey with hc | hc
    · linarith
    · linarith
  have hfR : (f : ℝ) = 2 * t := by linarith
  have hgR : (g : ℝ) = 2 * t := by linarith
  have hf : f = 2 * t := by exact_mod_cast hfR
  have hg : g = 2 * t := by exact_mod_cast hgR
  rw [h3, hf, hg, hq]
  push_cast
  ring_nf

/-! ## Cospectral graphs and graphs determined by their spectrum -/

/-- Two graphs are **cospectral** when they have the same characteristic polynomial, equivalently
the same eigenvalues with the same multiplicities. -/
def Cospectral (G H : CGraph) : Prop := G.charpoly = H.charpoly

end CGraph

namespace IsoGraph

/-- Two isomorphism classes are **cospectral** when they have the same characteristic polynomial. -/
def Cospectral (G H : IsoGraph) : Prop := G.charpoly = H.charpoly

@[simp, isoTransfer] theorem cospectral_mk (G H : CGraph) :
    Cospectral ⟦G⟧ ⟦H⟧ ↔ G.Cospectral H := Iff.rfl

end IsoGraph

namespace CGraph

@[toIsoGraph]
theorem Cospectral.spectrum_eq {G H : CGraph} (h : Cospectral G H) : G.spectrum = H.spectrum := by
  rw [spectrum, spectrum, h]

theorem Cospectral.refl (G : CGraph) : Cospectral G G := rfl

theorem Cospectral.symm {G H : CGraph} (h : Cospectral G H) : Cospectral H G := Eq.symm h

theorem Cospectral.trans {G H K : CGraph} (h : Cospectral G H) (h' : Cospectral H K) :
    Cospectral G K := Eq.trans h h'

theorem Cospectral.of_iso {G H : CGraph} (i : G ≃cg H) : Cospectral G H := charpoly_congr i

theorem cospectral_iff_spectrum_eq {G H : CGraph} :
    G.Cospectral H ↔ G.spectrum = H.spectrum := by
  refine ⟨Cospectral.spectrum_eq, fun h ↦ ?_⟩
  rw [Cospectral, charpoly_eq_prod_spectrum, charpoly_eq_prod_spectrum, h]

/-- **Cospectral graphs have the same number of vertices.** -/
theorem Cospectral.card_eq {G H : CGraph} (h : Cospectral G H) :
    Fintype.card G.V = Fintype.card H.V := by
  rw [← natDegree_charpoly, ← natDegree_charpoly, h]

/-- **Cospectral graphs have the same number of edges**, by the sum of the squares of the
eigenvalues. -/
@[toIsoGraph]
theorem Cospectral.E_eq {G H : CGraph} (h : Cospectral G H) : G.E = H.E := by
  have h2 : (2 : ℝ) * G.E = 2 * H.E := by
    rw [← sum_sq_spectrum, ← sum_sq_spectrum, h.spectrum_eq]
  have : (G.E : ℝ) = H.E := by linarith
  exact_mod_cast this

/-- **Cospectral graphs have the same number of triangles**, by the sum of the cubes of the
eigenvalues. -/
@[toIsoGraph]
theorem Cospectral.cliqueCount_three_eq {G H : CGraph} (h : Cospectral G H) :
    G.cliqueCount 3 = H.cliqueCount 3 := by
  have h6 : (6 : ℝ) * G.cliqueCount 3 = 6 * H.cliqueCount 3 := by
    rw [← sum_cube_spectrum, ← sum_cube_spectrum, h.spectrum_eq]
  have : (G.cliqueCount 3 : ℝ) = H.cliqueCount 3 := by linarith
  exact_mod_cast this

/-- **Cospectral graphs have the same number of closed walks of every length**, since that count
is the corresponding moment of the spectrum. -/
theorem Cospectral.sum_card_closedWalks_eq {G H : CGraph} (h : Cospectral G H) (n : ℕ) :
    ∑ v : G.V, (Fintype.card {w : G.toSimple.Walk v v // w.length = n} : ℝ)
      = ∑ v : H.V, (Fintype.card {w : H.toSimple.Walk v v // w.length = n} : ℝ) := by
  rw [← sum_pow_spectrum_eq_card_closedWalks, ← sum_pow_spectrum_eq_card_closedWalks,
    h.spectrum_eq]

/-- A graph is **determined by its spectrum** when every cospectral graph is isomorphic to it. -/
def IsDS (G : CGraph) : Prop := ∀ H : CGraph, Cospectral G H → Nonempty (G ≃cg H)

theorem isDS_of_iso {G H : CGraph} (i : G ≃cg H) (h : IsDS G) : IsDS H := fun K hK ↦
  (h K ((Cospectral.of_iso i).trans hK)).map fun j ↦ i.symm.trans j

/-! ### The empty graph and the complete graph are determined by their spectra -/

/-- A graph with no edges is the empty graph on its vertex set. -/
theorem adj_eq_false_of_E_eq_zero {G : CGraph} (h : G.E = 0) (x y : G.V) : G.Adj x y = false := by
  classical
  by_contra hc
  have hadj : G.toSimple.Adj x y := by simpa using hc
  have hmem : s(x, y) ∈ G.toSimple.edgeFinset := by simpa using hadj
  have hpos : 0 < G.toSimple.edgeFinset.card := Finset.card_pos.2 ⟨_, hmem⟩
  have hE : G.E = G.toSimple.edgeFinset.card := rfl
  omega

/-- **The empty graph is determined by its spectrum.** -/
theorem isDS_empty (n : ℕ) : IsDS (empty n) := by
  intro H h
  have hcard : Fintype.card H.V = n := by
    rw [← h.card_eq, card_empty]
  have hE : H.E = 0 := by rw [← h.E_eq, E_empty]
  refine ⟨isoOfAdj (Fintype.equivFinOfCardEq hcard).symm fun x y ↦ ?_⟩
  rw [empty_adj, adj_eq_false_of_E_eq_zero hE]

/-- **The complete graph is determined by its spectrum.**  A cospectral graph has `n` vertices and
`n (n - 1) / 2` edges, so its degrees sum to `n (n - 1)`; since no degree exceeds `n - 1`, every
degree is exactly `n - 1`. -/
theorem isDS_complete (n : ℕ) : IsDS (complete n) := by
  classical
  intro H h
  have hcard : Fintype.card H.V = n := by rw [← h.card_eq, card_complete]
  set e : (complete n).V ≃ H.V := (Fintype.equivFinOfCardEq hcard).symm with he
  rcases n with _ | m
  · exact ⟨isoOfAdj e fun x y ↦ absurd x.isLt (Nat.not_lt_zero _)⟩
  -- the degrees sum to `(m + 1) m`
  have hdeg : ∑ v, H.toSimple.degree v = (m + 1) * m := by
    have h1 : (∑ v, (H.toSimple.degree v : ℝ)) = (m : ℝ) ^ 2 + m := by
      rw [← sum_sq_spectrum_eq_sum_degrees, ← h.spectrum_eq, spectrum_complete]
      simp [Multiset.map_replicate]
    rw [← Nat.cast_sum] at h1
    have h2 : ((∑ v, H.toSimple.degree v : ℕ) : ℝ) = (((m + 1) * m : ℕ) : ℝ) := by
      rw [h1]; push_cast; ring
    exact_mod_cast h2
  -- every degree is at most `m`
  have hle : ∀ v : H.V, H.toSimple.degree v ≤ m := fun v ↦ by
    have := H.toSimple.degree_lt_card_verts v
    omega
  -- hence every degree is exactly `m`
  have hall : ∀ v : H.V, H.toSimple.degree v = m := by
    by_contra hc
    push_neg at hc
    obtain ⟨v, hv⟩ := hc
    have hlt : ∑ u, H.toSimple.degree u < ∑ _u : H.V, m :=
      Finset.sum_lt_sum (fun i _ ↦ hle i) ⟨v, Finset.mem_univ v, lt_of_le_of_ne (hle v) hv⟩
    rw [hdeg, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul] at hlt
    omega
  -- so `H` is complete
  have hadj : ∀ x y : H.V, x ≠ y → H.toSimple.Adj x y := by
    intro x y hxy
    have hsub : H.toSimple.neighborFinset x ⊆ Finset.univ.erase x := fun z hz ↦ by
      rw [SimpleGraph.mem_neighborFinset] at hz
      exact Finset.mem_erase.2 ⟨hz.ne', Finset.mem_univ z⟩
    have hcard' : (Finset.univ.erase x).card ≤ (H.toSimple.neighborFinset x).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard,
        SimpleGraph.card_neighborFinset_eq_degree, hall x]
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard'
    have hy : y ∈ H.toSimple.neighborFinset x := by
      rw [heq]; exact Finset.mem_erase.2 ⟨fun hc ↦ hxy hc.symm, Finset.mem_univ y⟩
    exact (SimpleGraph.mem_neighborFinset _ _ _).1 hy
  refine ⟨isoOfAdj e fun x y ↦ ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · simp [adj_self]
  · have hne : e x ≠ e y := fun hc ↦ hxy (e.injective hc)
    rw [complete_adj, decide_eq_true hxy]
    exact (toSimple_adj H _ _).mp (hadj _ _ hne)

/-! ## Graphs with `A ^ 3 = c A` -/

theorem spectrum_eq_of_cube_eq_smul {G : CGraph} {c : ℝ} (hc : 0 < c)
    (hcube : G.adjMat * G.adjMat * G.adjMat = c • G.adjMat) (hE : (G.E : ℝ) = c) :
    G.spectrum = Real.sqrt c ::ₘ (-Real.sqrt c) ::ₘ
      Multiset.replicate (Fintype.card G.V - 2) 0 := by
  classical
  set r := Real.sqrt c with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hc
  have hr2 : r ^ 2 = c := Real.sq_sqrt hc.le
  have hmem : ∀ x ∈ G.spectrum, x = r ∨ x = -r ∨ x = 0 := by
    intro x hx
    obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff G x).1 hx
    have e1 : (G.adjMat * G.adjMat * G.adjMat) *ᵥ v = (x * x * x) • v := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [hv, Matrix.mulVec_smul, smul_smul]
    have e2 : (G.adjMat * G.adjMat * G.adjMat) *ᵥ v = (c * x) • v := by
      rw [hcube, Matrix.smul_mulVec, hv, smul_smul]
    have e3 : (x * x * x - c * x) • v = 0 := by
      rw [sub_smul, ← e1, e2, sub_self]
    have e4 : x * x * x - c * x = 0 := by
      rcases smul_eq_zero.1 e3 with h | h
      · exact h
      · exact absurd h hv0
    have e5 : x * (x - r) * (x + r) = 0 := by linear_combination e4 - x * hr2
    rcases mul_eq_zero.1 e5 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  obtain ⟨a, ha⟩ : ∃ k, G.spectrum.count r = k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ k, G.spectrum.count (-r) = k := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ k, G.spectrum.count 0 = k := ⟨_, rfl⟩
  set t : Multiset ℝ :=
    Multiset.replicate a r + Multiset.replicate b (-r) + Multiset.replicate z 0 with htdef
  have hrne : r ≠ -r := by intro h; linarith
  have hr0 : r ≠ 0 := hr.ne'
  have hle : t ≤ G.spectrum := by
    refine Multiset.le_iff_count.2 fun x ↦ ?_
    by_cases h1 : x = r
    · subst h1
      simp [htdef, Multiset.count_replicate, Ne.symm hrne, Ne.symm hr0, ha]
    · by_cases h2 : x = -r
      · subst h2
        simp [htdef, Multiset.count_replicate, hrne, Ne.symm (neg_ne_zero.2 hr0), hb]
      · by_cases h3 : x = 0
        · subst h3
          simp [htdef, Multiset.count_replicate, Ne.symm h1, Ne.symm h2, hz]
        · simp [htdef, Multiset.count_replicate, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  have hsub : ∀ x ∈ G.spectrum, x ∈ ({r, -r, 0} : Finset ℝ) := by
    intro x hx
    rcases hmem x hx with h | h | h <;> simp [h]
  have hins1 : r ∉ ({-r, 0} : Finset ℝ) := by simp [hrne, hr0]
  have hins2 : (-r) ∉ ({0} : Finset ℝ) := by simp [neg_eq_zero, hr0]
  have hcard : Multiset.card G.spectrum = a + b + z := by
    rw [← Multiset.sum_count_eq_card hsub, Finset.sum_insert hins1, Finset.sum_insert hins2,
      Finset.sum_singleton, ha, hb, hz, add_assoc]
  have hcardt : Multiset.card t = a + b + z := by simp [htdef]
  have heq : t = G.spectrum := Multiset.eq_of_le_of_card_le hle (by rw [hcard, hcardt])
  have hs0 : (a : ℝ) * r - (b : ℝ) * r = 0 := by
    have h := sum_spectrum G
    rw [← heq] at h
    simpa [htdef, Multiset.sum_replicate, nsmul_eq_mul, sub_eq_add_neg, mul_neg] using h
  have hs2 : ((a : ℝ) + (b : ℝ)) * c = 2 * c := by
    have h := sum_sq_spectrum G
    rw [← heq, hE] at h
    have h' : (a : ℝ) * r ^ 2 + (b : ℝ) * r ^ 2 = 2 * c := by
      simpa [htdef, Multiset.sum_replicate, nsmul_eq_mul, neg_pow] using h
    rw [hr2] at h'
    linarith
  have hab : (a : ℝ) = (b : ℝ) := by
    have hz' : ((a : ℝ) - (b : ℝ)) * r = 0 := by rw [sub_mul]; linarith
    rcases mul_eq_zero.1 hz' with h | h
    · linarith
    · exact absurd h hr0
  have hsum2 : (a : ℝ) + (b : ℝ) = 2 := mul_right_cancel₀ hc.ne' hs2
  have ha1 : a = 1 := by
    have : (a : ℝ) = 1 := by linarith
    exact_mod_cast this
  have hb1 : b = 1 := by
    have : (b : ℝ) = 1 := by linarith
    exact_mod_cast this
  have hzc : z = Fintype.card G.V - 2 := by
    have h := hcard
    rw [card_spectrum, ha1, hb1] at h
    omega
  rw [← heq, htdef, ha1, hb1, hzc]
  simp [← Multiset.singleton_add, add_assoc]

/-! ## Complete bipartite graphs and stars -/

private theorem ones_mul_ones (p q r : ℕ) :
    (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ) *
        (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix (Fin q) (Fin r) ℝ) =
      (q : ℝ) • Matrix.of fun _ _ ↦ (1 : ℝ) := by
  ext i j
  simp [Matrix.mul_apply]

theorem adjMat_bipartite (m n : ℕ) :
    (bipartite m n).adjMat =
      Matrix.fromBlocks 0 (Matrix.of fun _ _ ↦ (1 : ℝ)) (Matrix.of fun _ _ ↦ (1 : ℝ)) 0 := by
  ext x y
  cases x <;> cases y <;> simp [adjMat_apply]

theorem adjMat_bipartite_cube (m n : ℕ) :
    (bipartite m n).adjMat * (bipartite m n).adjMat * (bipartite m n).adjMat =
      ((m * n : ℕ) : ℝ) • (bipartite m n).adjMat := by
  rw [adjMat_bipartite, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply, mul_comm]

theorem spectrum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).spectrum =
      Real.sqrt ((m + 1) * (n + 1)) ::ₘ (-Real.sqrt ((m + 1) * (n + 1)) ::ₘ
        Multiset.replicate (m + n) 0) := by
  have hc : (0 : ℝ) < ((m + 1) * (n + 1) : ℕ) := by positivity
  have h := spectrum_eq_of_cube_eq_smul (G := bipartite (m + 1) (n + 1)) hc
    (adjMat_bipartite_cube (m + 1) (n + 1)) (by simp)
  rw [h, card_bipartite, show m + 1 + (n + 1) - 2 = m + n from by omega]
  norm_num

theorem spectrum_star (n : ℕ) :
    (star (n + 1)).spectrum =
      Real.sqrt (n + 1) ::ₘ (-Real.sqrt (n + 1) ::ₘ Multiset.replicate n 0) := by
  have h := spectrum_bipartite 0 n
  rw [star]
  norm_num at h ⊢
  exact h

/-! ## A cospectral pair -/

/-- The star `K₁,₄` and the disjoint union of the four-cycle `K₂,₂` with an isolated vertex are
cospectral: both spectra are `2, -2, 0, 0, 0`. -/
@[toIsoGraph]
theorem cospectral_star_four :
    (star 4).Cospectral (disjUnion (bipartite 2 2) (empty 1)) := by
  have hs := spectrum_star 3
  have hb := spectrum_bipartite 1 1
  norm_num at hs hb
  rw [cospectral_iff_spectrum_eq, spectrum_disjUnion, spectrum_empty, hs, hb]
  simp [Multiset.cons_add]

/-! ## Bounding the eigenvalues with a positive vector

The tool behind Smith's theorem: a positive vector `w` with `A w ≤ c w` pointwise caps *every*
eigenvalue at `c`, and if `A w = c w` exactly then `c` is attained.  Comparing a graph with a
positive `2`-eigenvector — the *marks* of an affine Dynkin diagram — is what makes the
classification of the graphs of spectral radius `2` elementary. -/

theorem adjMat_nonneg (G : CGraph) (i j : G.V) : 0 ≤ G.adjMat i j := by
  rw [adjMat_apply]; split <;> norm_num

private theorem le_of_mulVec_le_aux {G : CGraph} {c : ℝ} {w : G.V → ℝ} (hw : ∀ i, 0 < w i)
    (hle : ∀ i, (G.adjMat *ᵥ w) i ≤ c * w i) {x : ℝ} {u : G.V → ℝ}
    (hu : G.adjMat *ᵥ u = x • u) {i₀ : G.V} (hi₀ : 0 < u i₀ / w i₀) : x ≤ c := by
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ u i / w i) ⟨i₀, Finset.mem_univ i₀⟩
  set t : ℝ := u p / w p with ht
  have htpos : 0 < t := lt_of_lt_of_le hi₀ (hp i₀ (Finset.mem_univ i₀))
  have hup : u p = t * w p := (div_mul_cancel₀ (u p) (hw p).ne').symm
  have hbound : ∀ j, u j ≤ t * w j := fun j ↦ by
    have h := hp j (Finset.mem_univ j)
    rw [div_le_iff₀ (hw j)] at h
    linarith
  have h1 : x * u p = ∑ j, G.adjMat p j * u j := by
    have h := congrFun hu p
    simpa [Matrix.mulVec, dotProduct] using h.symm
  have h2 : ∑ j, G.adjMat p j * u j ≤ ∑ j, G.adjMat p j * (t * w j) :=
    Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hbound j) (adjMat_nonneg G p j)
  have h3 : ∑ j, G.adjMat p j * (t * w j) = t * (G.adjMat *ᵥ w) p := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h4 : t * (G.adjMat *ᵥ w) p ≤ t * (c * w p) := mul_le_mul_of_nonneg_left (hle p) htpos.le
  have hpos : 0 < t * w p := mul_pos htpos (hw p)
  have h5 : x * (t * w p) ≤ c * (t * w p) :=
    calc x * (t * w p) = x * u p := by rw [hup]
      _ = ∑ j, G.adjMat p j * u j := h1
      _ ≤ ∑ j, G.adjMat p j * (t * w j) := h2
      _ = t * (G.adjMat *ᵥ w) p := h3
      _ ≤ t * (c * w p) := h4
      _ = c * (t * w p) := by ring
  exact le_of_mul_le_mul_right h5 hpos

/-- **The subeigenvector bound.**  If `w` is strictly positive and `A w ≤ c w` coordinatewise then
every eigenvalue of `G` is at most `c`. -/
theorem le_of_mulVec_le {G : CGraph} {c : ℝ} {w : G.V → ℝ} (hw : ∀ i, 0 < w i)
    (hle : ∀ i, (G.adjMat *ᵥ w) i ≤ c * w i) {x : ℝ} (hx : G.IsEigenvalue x) : x ≤ c := by
  obtain ⟨u, hu0, hu⟩ := hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
  simp only [Pi.zero_apply] at hi
  rcases lt_or_gt_of_ne hi with h | h
  · refine le_of_mulVec_le_aux hw hle (u := -u) ?_ (i₀ := i) ?_
    · rw [Matrix.mulVec_neg, hu]; module
    · simpa using div_pos (neg_pos.2 h) (hw i)
  · exact le_of_mulVec_le_aux hw hle hu (div_pos h (hw i))

theorem spectrum_le_of_mulVec_le {G : CGraph} {c : ℝ} {w : G.V → ℝ} (hw : ∀ i, 0 < w i)
    (hle : ∀ i, (G.adjMat *ᵥ w) i ≤ c * w i) {x : ℝ} (hx : x ∈ G.spectrum) : x ≤ c :=
  le_of_mulVec_le hw hle ((mem_spectrum_iff G x).1 hx)

/-- A positive eigenvector realises its eigenvalue. -/
theorem mem_spectrum_of_mulVec_eq {G : CGraph} [Nonempty G.V] {c : ℝ} {w : G.V → ℝ}
    (hw : ∀ i, 0 < w i) (h : G.adjMat *ᵥ w = c • w) : c ∈ G.spectrum :=
  (mem_spectrum_iff G c).2 ⟨w, fun h0 ↦ (hw (Classical.arbitrary G.V)).ne'
    (congrFun h0 (Classical.arbitrary G.V)), h⟩

/-! ### The largest eigenvalue -/

/-- The largest eigenvalue of a nonempty graph. -/
noncomputable def lambdaMax (G : CGraph) [Nonempty G.V] : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty G.eigenvalues

theorem lambdaMax_mem_spectrum (G : CGraph) [Nonempty G.V] : G.lambdaMax ∈ G.spectrum := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G.V)) G.eigenvalues
  rw [spectrum_eq_map, Multiset.mem_map]
  exact ⟨i, Finset.mem_univ_val i, hi.symm⟩

theorem le_lambdaMax {G : CGraph} [Nonempty G.V] {x : ℝ} (hx : x ∈ G.spectrum) :
    x ≤ G.lambdaMax := by
  rw [spectrum_eq_map, Multiset.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem lambdaMax_le_iff (G : CGraph) [Nonempty G.V] {c : ℝ} :
    G.lambdaMax ≤ c ↔ ∀ x ∈ G.spectrum, x ≤ c :=
  ⟨fun h _ hx ↦ (le_lambdaMax hx).trans h, fun h ↦ h _ (lambdaMax_mem_spectrum G)⟩

theorem lambdaMax_lt_iff (G : CGraph) [Nonempty G.V] {c : ℝ} :
    G.lambdaMax < c ↔ ∀ x ∈ G.spectrum, x < c :=
  ⟨fun h _ hx ↦ lt_of_le_of_lt (le_lambdaMax hx) h, fun h ↦ h _ (lambdaMax_mem_spectrum G)⟩

theorem lambdaMax_congr {G H : CGraph} [Nonempty G.V] [Nonempty H.V] (i : G ≃cg H) :
    G.lambdaMax = H.lambdaMax :=
  le_antisymm (le_lambdaMax (spectrum_congr i ▸ lambdaMax_mem_spectrum G))
    (le_lambdaMax ((spectrum_congr i).symm ▸ lambdaMax_mem_spectrum H))

theorem lambdaMax_le_of_mulVec_le {G : CGraph} [Nonempty G.V] {c : ℝ} {w : G.V → ℝ}
    (hw : ∀ i, 0 < w i) (hle : ∀ i, (G.adjMat *ᵥ w) i ≤ c * w i) : G.lambdaMax ≤ c :=
  (lambdaMax_le_iff G).2 fun _ hx ↦ spectrum_le_of_mulVec_le hw hle hx

/-- The largest eigenvalue is nonnegative, because the eigenvalues sum to zero. -/
theorem lambdaMax_nonneg (G : CGraph) [Nonempty G.V] : 0 ≤ G.lambdaMax := by
  by_contra h
  push_neg at h
  have hsum : ∑ i, G.eigenvalues i = 0 := by
    have hs := G.sum_spectrum
    rwa [spectrum_eq_map, ← Finset.sum_eq_multiset_sum] at hs
  have hlt : ∑ i, G.eigenvalues i < ∑ _i : G.V, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦
      lt_of_le_of_lt (Finset.le_sup' _ (Finset.mem_univ i)) h
  simp [hsum] at hlt

/-- The all-ones vector bounds the largest eigenvalue by the maximum degree. -/
theorem lambdaMax_le_maxDeg (G : CGraph) [Nonempty G.V] : G.lambdaMax ≤ (G.maxDeg : ℝ) := by
  refine lambdaMax_le_of_mulVec_le (w := 1) (fun _ ↦ one_pos) fun i ↦ ?_
  have hdeg : (G.adjMat *ᵥ (1 : G.V → ℝ)) i = (G.toSimple.degree i : ℝ) := by
    simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
  rw [hdeg, Pi.one_apply, mul_one]
  exact_mod_cast G.toSimple.degree_le_maxDegree i

/-- For a regular graph the largest eigenvalue is the degree. -/
theorem lambdaMax_of_isRegularWith {G : CGraph} [Nonempty G.V] {k : ℕ} (h : G.IsRegularWith k) :
    G.lambdaMax = (k : ℝ) :=
  le_antisymm
    (lambdaMax_le_of_mulVec_le (w := 1) (fun _ ↦ one_pos) fun i ↦ by
      rw [(hasEigenvector_one_of_isRegularWith h).2]; simp)
    (le_lambdaMax (mem_spectrum_of_isRegularWith h))

/-- The smallest eigenvalue of a nonempty graph. -/
noncomputable def lambdaMin (G : CGraph) [Nonempty G.V] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty G.eigenvalues

theorem lambdaMin_mem_spectrum (G : CGraph) [Nonempty G.V] : G.lambdaMin ∈ G.spectrum := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G.V)) G.eigenvalues
  rw [spectrum_eq_map, Multiset.mem_map]
  exact ⟨i, Finset.mem_univ_val i, hi.symm⟩

theorem lambdaMin_le {G : CGraph} [Nonempty G.V] {x : ℝ} (hx : x ∈ G.spectrum) :
    G.lambdaMin ≤ x := by
  rw [spectrum_eq_map, Multiset.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_lambdaMin_iff (G : CGraph) [Nonempty G.V] {c : ℝ} :
    c ≤ G.lambdaMin ↔ ∀ x ∈ G.spectrum, c ≤ x :=
  ⟨fun h _ hx ↦ h.trans (lambdaMin_le hx), fun h ↦ h _ (lambdaMin_mem_spectrum G)⟩

theorem lt_lambdaMin_iff (G : CGraph) [Nonempty G.V] {c : ℝ} :
    c < G.lambdaMin ↔ ∀ x ∈ G.spectrum, c < x :=
  ⟨fun h _ hx ↦ lt_of_lt_of_le h (lambdaMin_le hx), fun h ↦ h _ (lambdaMin_mem_spectrum G)⟩

theorem lambdaMin_congr {G H : CGraph} [Nonempty G.V] [Nonempty H.V] (i : G ≃cg H) :
    G.lambdaMin = H.lambdaMin :=
  le_antisymm (lambdaMin_le ((spectrum_congr i).symm ▸ lambdaMin_mem_spectrum H))
    (lambdaMin_le (spectrum_congr i ▸ lambdaMin_mem_spectrum G))

theorem lambdaMin_le_lambdaMax (G : CGraph) [Nonempty G.V] : G.lambdaMin ≤ G.lambdaMax :=
  lambdaMin_le (lambdaMax_mem_spectrum G)

/-- The smallest eigenvalue is nonpositive, because the eigenvalues sum to zero. -/
theorem lambdaMin_nonpos (G : CGraph) [Nonempty G.V] : G.lambdaMin ≤ 0 := by
  by_contra h
  push_neg at h
  have hsum : ∑ i, G.eigenvalues i = 0 := by
    have hs := G.sum_spectrum
    rwa [spectrum_eq_map, ← Finset.sum_eq_multiset_sum] at hs
  have hlt : ∑ _i : G.V, (0 : ℝ) < ∑ i, G.eigenvalues i :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦
      lt_of_lt_of_le h (Finset.inf'_le _ (Finset.mem_univ i))
  simp [hsum] at hlt

/-- **Every eigenvalue is bounded in absolute value by the maximum degree.**  Evaluate the
eigenvector equation at a coordinate where `|v|` is largest. -/
theorem abs_le_maxDeg_of_isEigenvalue {G : CGraph} {x : ℝ} (h : G.IsEigenvalue x) :
    |x| ≤ (G.maxDeg : ℝ) := by
  classical
  obtain ⟨u, hu0, hu⟩ := h
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hu0
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) (fun i ↦ |u i|) ⟨i₀, Finset.mem_univ i₀⟩
  have hup : 0 < |u p| := lt_of_lt_of_le (abs_pos.2 hi₀) (hp i₀ (Finset.mem_univ i₀))
  have hrow : ∑ j, G.adjMat p j = (G.toSimple.degree p : ℝ) := by
    have h1 : (G.adjMat *ᵥ (1 : G.V → ℝ)) p = (G.toSimple.degree p : ℝ) := by
      simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
    simpa [Matrix.mulVec, dotProduct] using h1
  have e : x * u p = ∑ j, G.adjMat p j * u j := by
    have h2 := congrFun hu p
    simpa [Matrix.mulVec, dotProduct] using h2.symm
  have key : |x| * |u p| ≤ (G.maxDeg : ℝ) * |u p| := by
    calc |x| * |u p| = |x * u p| := (abs_mul _ _).symm
      _ = |∑ j, G.adjMat p j * u j| := by rw [e]
      _ ≤ ∑ j, |G.adjMat p j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, G.adjMat p j * |u j| := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [abs_mul, abs_of_nonneg (G.adjMat_nonneg p j)]
      _ ≤ ∑ j, G.adjMat p j * |u p| :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (hp j (Finset.mem_univ j)) (G.adjMat_nonneg p j)
      _ = (G.toSimple.degree p : ℝ) * |u p| := by rw [← Finset.sum_mul, hrow]
      _ ≤ (G.maxDeg : ℝ) * |u p| :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast G.toSimple.degree_le_maxDegree p) (abs_nonneg _)
  exact le_of_mul_le_mul_right key hup

theorem abs_le_maxDeg_of_mem_spectrum {G : CGraph} {x : ℝ} (hx : x ∈ G.spectrum) :
    |x| ≤ (G.maxDeg : ℝ) :=
  abs_le_maxDeg_of_isEigenvalue ((G.mem_spectrum_iff x).1 hx)

theorem neg_maxDeg_le_lambdaMin (G : CGraph) [Nonempty G.V] : -(G.maxDeg : ℝ) ≤ G.lambdaMin :=
  (le_lambdaMin_iff G).2 fun _ hx ↦ neg_le_of_abs_le (abs_le_maxDeg_of_mem_spectrum hx)

theorem abs_lambdaMin_le_maxDeg (G : CGraph) [Nonempty G.V] : |G.lambdaMin| ≤ (G.maxDeg : ℝ) :=
  abs_le_maxDeg_of_mem_spectrum (lambdaMin_mem_spectrum G)

/-- Each `eigenvalues i` is a member of the spectrum. -/
theorem eigenvalues_mem_spectrum (G : CGraph) (i : G.V) : G.eigenvalues i ∈ G.spectrum := by
  rw [spectrum_eq_map, Multiset.mem_map]
  exact ⟨i, Finset.mem_univ_val i, rfl⟩

/-- A real symmetric matrix is orthogonally diagonalisable: there is an orthogonal `U` with
`Uᵀ A U` the diagonal matrix of eigenvalues. -/
theorem exists_orthogonal_diagonal (G : CGraph) :
    ∃ U : Matrix G.V G.V ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      Uᵀ * G.adjMat * U = Matrix.diagonal G.eigenvalues := by
  have hA := G.isHermitian_adjMat
  set U : Matrix G.V G.V ℝ := ↑hA.eigenvectorUnitary with hUdef
  have hU : U ∈ unitary (Matrix G.V G.V ℝ) := hA.eigenvectorUnitary.2
  have hst : Star.star U * G.adjMat * U = Matrix.diagonal G.eigenvalues := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    exact h
  have hstar : Star.star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hst
  refine ⟨U, ?_, ?_, hst⟩
  · rw [← hstar]; exact hU.1
  · rw [← hstar]; exact hU.2

/-- **Diagonalising rotates the quadratic form into a weighted sum of squares.**  There are
coordinates `w`, of the same length as `v`, in which `⟪v, A v⟫ = ∑ λ i * w i ^ 2`. -/
theorem exists_rotate_quadratic (G : CGraph) (v : G.V → ℝ) :
    ∃ w : G.V → ℝ, v ⬝ᵥ (G.adjMat *ᵥ v) = ∑ i, G.eigenvalues i * w i ^ 2 ∧
      v ⬝ᵥ v = ∑ i, w i ^ 2 := by
  obtain ⟨U, hUU, hUU', hD⟩ := G.exists_orthogonal_diagonal
  refine ⟨Uᵀ *ᵥ v, ?_, ?_⟩
  · have hA : G.adjMat = U * Matrix.diagonal G.eigenvalues * Uᵀ := by
      rw [← hD]
      calc G.adjMat = U * Uᵀ * G.adjMat * (U * Uᵀ) := by rw [hUU', one_mul, mul_one]
        _ = U * (Uᵀ * G.adjMat * U) * Uᵀ := by simp only [mul_assoc]
    rw [hA, show (U * Matrix.diagonal G.eigenvalues * Uᵀ) *ᵥ v
          = U *ᵥ (Matrix.diagonal G.eigenvalues *ᵥ (Uᵀ *ᵥ v)) by
        simp only [Matrix.mulVec_mulVec, mul_assoc],
      dotProduct_mulVec, show v ᵥ* U = Uᵀ *ᵥ v by
        rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · have hn : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
      rw [dotProduct_mulVec, show (Uᵀ *ᵥ v) ᵥ* Uᵀ = U *ᵥ (Uᵀ *ᵥ v) by
        rw [Matrix.vecMul_transpose], Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rw [← hn]
    exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm

/-- **The Rayleigh quotient is bounded above by the largest eigenvalue.** -/
theorem rayleigh_le_lambdaMax (G : CGraph) [Nonempty G.V] (v : G.V → ℝ) :
    v ⬝ᵥ (G.adjMat *ᵥ v) ≤ G.lambdaMax * (v ⬝ᵥ v) := by
  obtain ⟨w, h1, h2⟩ := G.exists_rotate_quadratic v
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (le_lambdaMax (G.eigenvalues_mem_spectrum i)) (sq_nonneg _)

/-- **The Rayleigh quotient is bounded below by the smallest eigenvalue.** -/
theorem lambdaMin_mul_le_rayleigh (G : CGraph) [Nonempty G.V] (v : G.V → ℝ) :
    G.lambdaMin * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G.adjMat *ᵥ v) := by
  obtain ⟨w, h1, h2⟩ := G.exists_rotate_quadratic v
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (lambdaMin_le (G.eigenvalues_mem_spectrum i)) (sq_nonneg _)

/-- The Rayleigh quotient of `e u + s • e v` across an edge: the quadratic form is `2 s` and the
norm is `1 + s ^ 2`. -/
private theorem rayleigh_pair {G : CGraph} {u v : G.V} (h : G.Adj u v) (s : ℝ) :
    ∃ w : G.V → ℝ, w ⬝ᵥ (G.adjMat *ᵥ w) = 2 * s ∧ w ⬝ᵥ w = 1 + s ^ 2 := by
  classical
  have hne : u ≠ v := by rintro rfl; exact G.loopless u h
  have huv : G.adjMat u v = 1 := by simp [adjMat_apply, h]
  have hvu : G.adjMat v u = 1 := by simp [adjMat_apply, ← G.symm u v, h]
  have huu : G.adjMat u u = 0 := by simp [adjMat_apply, G.loopless u]
  have hvv : G.adjMat v v = 0 := by simp [adjMat_apply, G.loopless v]
  refine ⟨fun x ↦ (if x = u then (1 : ℝ) else 0) + s * (if x = v then 1 else 0), ?_, ?_⟩
  · have hAw : ∀ x, (G.adjMat *ᵥ fun y ↦ (if y = u then (1 : ℝ) else 0)
        + s * (if y = v then 1 else 0)) x = G.adjMat x u + s * G.adjMat x v := fun x ↦ by
      simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm s, ← mul_assoc]
      rw [← Finset.sum_mul, Finset.sum_ite_eq' Finset.univ v (fun y ↦ G.adjMat x y)]
      simp [mul_comm]
    simp only [dotProduct, hAw, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ v (fun y ↦ G.adjMat y u + s * G.adjMat y v)]
    simp only [if_true, Finset.mem_univ, huv, hvu, huu, hvv]
    ring
  · simp only [dotProduct, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul,
      zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_neg hne,
      if_neg hne.symm]
    ring

/-- **A graph with an edge has an eigenvalue at least `1`.** -/
theorem one_le_lambdaMax {G : CGraph} [Nonempty G.V] {u v : G.V} (h : G.Adj u v) :
    1 ≤ G.lambdaMax := by
  obtain ⟨w, h1, h2⟩ := rayleigh_pair h 1
  have := G.rayleigh_le_lambdaMax w
  rw [h1, h2] at this
  norm_num at this
  linarith

/-- **A graph with an edge has an eigenvalue at most `-1`.** -/
theorem lambdaMin_le_neg_one {G : CGraph} [Nonempty G.V] {u v : G.V} (h : G.Adj u v) :
    G.lambdaMin ≤ -1 := by
  obtain ⟨w, h1, h2⟩ := rayleigh_pair h (-1)
  have := G.lambdaMin_mul_le_rayleigh w
  rw [h1, h2] at this
  norm_num at this
  linarith

/-- **The largest eigenvalue is at least the average degree.** -/
theorem avg_degree_le_lambdaMax (G : CGraph) [Nonempty G.V] :
    2 * (G.E : ℝ) ≤ G.lambdaMax * Fintype.card G.V := by
  classical
  have hone : (fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ (G.adjMat *ᵥ fun _ ↦ (1 : ℝ)) = 2 * (G.E : ℝ) := by
    have hdeg : ∀ i, (G.adjMat *ᵥ fun _ : G.V ↦ (1 : ℝ)) i = (G.toSimple.degree i : ℝ) :=
      fun i ↦ by simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
    have hE : G.E = G.toSimple.edgeFinset.card := rfl
    simp only [dotProduct, hdeg, one_mul]
    rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges, hE]
    push_cast
    ring
  have hnorm : (fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ (fun _ ↦ (1 : ℝ)) = (Fintype.card G.V : ℝ) := by
    simp [dotProduct, Finset.card_univ]
  have := G.rayleigh_le_lambdaMax fun _ ↦ (1 : ℝ)
  rwa [hone, hnorm] at this

/-- **`√Δ ≤ λ_max`.**  Weighting a vertex of maximum degree by `√Δ` and each of its neighbours by
`1` gives a vector of norm `2 Δ` whose quadratic form is at least `2 Δ √Δ`: the centre sees `Δ`
neighbours and each neighbour sees the centre. -/
theorem sqrt_maxDeg_le_lambdaMax (G : CGraph) [Nonempty G.V] :
    Real.sqrt (G.maxDeg : ℝ) ≤ G.lambdaMax := by
  obtain ⟨v, hv⟩ := G.toSimple.exists_maximal_degree_vertex
  have hdeg : G.toSimple.degree v = G.maxDeg := hv.symm
  rcases Nat.eq_zero_or_pos G.maxDeg with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.sqrt_zero]
    exact G.lambdaMax_nonneg
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = G.maxDeg := ⟨_, rfl⟩
  have hdpos : 0 < (d : ℝ) := by rw [hd]; exact_mod_cast hpos
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (d : ℝ) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hss : s * s = (d : ℝ) := by rw [hsdef]; exact Real.mul_self_sqrt (le_of_lt hdpos)
  obtain ⟨N, hNdef⟩ : ∃ N : Finset G.V, N = G.toSimple.neighborFinset v := ⟨_, rfl⟩
  have hNcard : N.card = d := by rw [hNdef, hd]; exact hdeg
  have hvN : v ∉ N := by
    rw [hNdef, SimpleGraph.mem_neighborFinset]
    exact G.toSimple.irrefl
  obtain ⟨x, hxdef⟩ : ∃ x : G.V → ℝ, x = fun u ↦ if u = v then s else if u ∈ N then 1 else 0 :=
    ⟨_, rfl⟩
  have hxv : x v = s := by rw [hxdef]; simp
  have hxN : ∀ u ∈ N, x u = 1 := by
    intro u hu
    have hne : u ≠ v := fun h ↦ hvN (h ▸ hu)
    rw [hxdef]
    simp [hne, hu]
  have hx0 : ∀ u, 0 ≤ x u := by
    intro u
    rw [hxdef]
    dsimp only
    split
    · exact hs0
    · split
      · exact zero_le_one
      · exact le_rfl
  have hmulVec : ∀ u : G.V, (G.adjMat *ᵥ x) u = ∑ w ∈ G.toSimple.neighborFinset u, x w := by
    intro u
    simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
  have hAxv : (G.adjMat *ᵥ x) v = (d : ℝ) := by
    rw [hmulVec, ← hNdef, Finset.sum_congr rfl hxN, Finset.sum_const, hNcard, nsmul_eq_mul,
      mul_one]
  have hAxN : ∀ u ∈ N, s ≤ (G.adjMat *ᵥ x) u := by
    intro u hu
    rw [hmulVec, ← hxv]
    refine Finset.single_le_sum (fun w _ ↦ hx0 w) ?_
    rw [SimpleGraph.mem_neighborFinset]
    exact ((SimpleGraph.mem_neighborFinset _ _ _).1 (hNdef ▸ hu)).symm
  have hquad : 2 * (d : ℝ) * s ≤ x ⬝ᵥ (G.adjMat *ᵥ x) := by
    have hsub : insert v N ⊆ (Finset.univ : Finset G.V) := Finset.subset_univ _
    have hstep : ∑ u ∈ insert v N, x u * (G.adjMat *ᵥ x) u ≤ x ⬝ᵥ (G.adjMat *ᵥ x) := by
      rw [dotProduct]
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ ↦ ?_
      refine mul_nonneg (hx0 u) ?_
      rw [hmulVec]
      exact Finset.sum_nonneg fun w _ ↦ hx0 w
    refine le_trans ?_ hstep
    rw [Finset.sum_insert hvN, hxv, hAxv]
    have hN' : ∑ u ∈ N, (s : ℝ) ≤ ∑ u ∈ N, x u * (G.adjMat *ᵥ x) u := by
      refine Finset.sum_le_sum fun u hu ↦ ?_
      rw [hxN u hu, one_mul]
      exact hAxN u hu
    rw [Finset.sum_const, hNcard, nsmul_eq_mul] at hN'
    nlinarith [hN']
  have hnorm : x ⬝ᵥ x = 2 * (d : ℝ) := by
    rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ (insert v N)) ?_]
    · rw [Finset.sum_insert hvN, hxv, Finset.sum_congr rfl fun u hu ↦ by rw [hxN u hu],
        Finset.sum_const, hNcard, nsmul_eq_mul, hss]
      ring
    · intro u _ hu
      have hne : u ≠ v := fun h ↦ hu (h ▸ Finset.mem_insert_self v N)
      have huN : u ∉ N := fun h ↦ hu (Finset.mem_insert_of_mem h)
      rw [hxdef]
      simp [hne, huN]
  have hray := G.rayleigh_le_lambdaMax x
  rw [hnorm] at hray
  have h2 : 2 * (d : ℝ) * s ≤ G.lambdaMax * (2 * (d : ℝ)) := le_trans hquad hray
  rw [← hd, ← hsdef]
  nlinarith [h2, hdpos]

/-- The quadratic form of a graph, as a double sum over ordered pairs. -/
theorem dotProduct_mulVec_eq_sum (G : CGraph) (v : G.V → ℝ) :
    v ⬝ᵥ (G.adjMat *ᵥ v) = ∑ x, ∑ y, G.adjMat x y * (v x * v y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring

/-- **Taking absolute values can only increase the quadratic form**, because `A` has nonnegative
entries. -/
theorem abs_dotProduct_mulVec_le (G : CGraph) (v : G.V → ℝ) :
    |v ⬝ᵥ (G.adjMat *ᵥ v)| ≤ (fun x ↦ |v x|) ⬝ᵥ (G.adjMat *ᵥ fun x ↦ |v x|) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ ↦ ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun y _ ↦ ?_)
  exact le_of_eq (by rw [abs_mul, abs_mul, abs_of_nonneg (adjMat_nonneg G x y)])

/-- **`λ_max` is the spectral radius**: no eigenvalue exceeds it in absolute value.  Replacing an
eigenvector by its absolute value keeps the norm and does not decrease the quadratic form. -/
theorem abs_le_lambdaMax_of_mem_spectrum {G : CGraph} [Nonempty G.V] {x : ℝ}
    (hx : x ∈ G.spectrum) : |x| ≤ G.lambdaMax := by
  obtain ⟨v, hv0, hv⟩ := (G.mem_spectrum_iff _).1 hx
  have hnorm : (fun y ↦ |v y|) ⬝ᵥ (fun y ↦ |v y|) = v ⬝ᵥ v := by
    simp [dotProduct, abs_mul_abs_self]
  have hpos : 0 < v ⬝ᵥ v := by
    obtain ⟨y0, hy0⟩ := Function.ne_iff.1 hv0
    rw [dotProduct]
    exact Finset.sum_pos' (fun y _ ↦ mul_self_nonneg _)
      ⟨y0, Finset.mem_univ _, mul_self_pos.2 hy0⟩
  have h1 : |v ⬝ᵥ (G.adjMat *ᵥ v)| = |x| * (v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hpos]
  have h2 := G.abs_dotProduct_mulVec_le v
  have h3 := G.rayleigh_le_lambdaMax fun y ↦ |v y|
  rw [hnorm] at h3
  rw [h1] at h2
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- Every eigenvalue is at least `-λ_max`. -/
theorem neg_lambdaMax_le_lambdaMin (G : CGraph) [Nonempty G.V] : -G.lambdaMax ≤ G.lambdaMin :=
  (abs_le.1 (abs_le_lambdaMax_of_mem_spectrum G.lambdaMin_mem_spectrum)).1

/-- The bound is attained: an eigenvector for the largest eigenvalue maximises the quotient. -/
theorem exists_rayleigh_eq_lambdaMax (G : CGraph) [Nonempty G.V] :
    ∃ v : G.V → ℝ, v ≠ 0 ∧ v ⬝ᵥ (G.adjMat *ᵥ v) = G.lambdaMax * (v ⬝ᵥ v) := by
  obtain ⟨v, hv0, hv⟩ := (G.mem_spectrum_iff _).1 (lambdaMax_mem_spectrum G)
  exact ⟨v, hv0, by rw [hv, dotProduct_smul, smul_eq_mul]⟩

/-- The bound is attained: an eigenvector for the smallest eigenvalue minimises the quotient. -/
theorem exists_rayleigh_eq_lambdaMin (G : CGraph) [Nonempty G.V] :
    ∃ v : G.V → ℝ, v ≠ 0 ∧ v ⬝ᵥ (G.adjMat *ᵥ v) = G.lambdaMin * (v ⬝ᵥ v) := by
  obtain ⟨v, hv0, hv⟩ := (G.mem_spectrum_iff _).1 (lambdaMin_mem_spectrum G)
  exact ⟨v, hv0, by rw [hv, dotProduct_smul, smul_eq_mul]⟩

/-! ### Monotonicity in the edge set -/

/-- **The spectral radius is monotone in the edge set.**  If `e` embeds the vertices of `H` into
those of `G` carrying edges to edges, then `λ_max(H) ≤ λ_max(G)`: take an eigenvector for
`λ_max(H)`, replace it by its absolute value — which cannot decrease the quadratic form, since
`A` is nonnegative — and read it through `e`, where the extra edges of `G` only add nonnegative
terms. -/
theorem lambdaMax_le_lambdaMax_of_adj {G H : CGraph} [Nonempty G.V] [Nonempty H.V]
    (e : H.V ≃ G.V)
    (hadj : ∀ x y, H.Adj x y → G.Adj (e x) (e y)) : H.lambdaMax ≤ G.lambdaMax := by
  obtain ⟨v, hv0, hv⟩ := (H.mem_spectrum_iff _).1 (lambdaMax_mem_spectrum H)
  set u : H.V → ℝ := fun x ↦ |v x| with hu
  set w : G.V → ℝ := fun z ↦ u (e.symm z) with hw
  have hpos : 0 < v ⬝ᵥ v := by
    obtain ⟨y0, hy0⟩ := Function.ne_iff.1 hv0
    rw [dotProduct]
    exact Finset.sum_pos' (fun y _ ↦ mul_self_nonneg _)
      ⟨y0, Finset.mem_univ _, mul_self_pos.2 hy0⟩
  have hnorm : u ⬝ᵥ u = v ⬝ᵥ v := by simp [hu, dotProduct, abs_mul_abs_self]
  have hnormw : w ⬝ᵥ w = v ⬝ᵥ v := by
    rw [← hnorm, dotProduct, dotProduct, ← Equiv.sum_comp e]
    simp [hw]
  -- the quadratic form of `H` at `|v|` is at least `λ_max(H) ‖v‖²`
  have h1 : H.lambdaMax * (v ⬝ᵥ v) ≤ u ⬝ᵥ (H.adjMat *ᵥ u) := by
    have h2 := H.abs_dotProduct_mulVec_le v
    rw [hv, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hpos] at h2
    refine le_trans ?_ h2
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
  -- reading it through `e` only adds nonnegative terms
  have h3 : u ⬝ᵥ (H.adjMat *ᵥ u) ≤ w ⬝ᵥ (G.adjMat *ᵥ w) := by
    rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, ← Equiv.sum_comp e]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    have hnn : 0 ≤ u x * u y := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hwx : w (e x) = u x := by simp [hw]
    have hwy : w (e y) = u y := by simp [hw]
    rw [hwx, hwy]
    by_cases h : H.Adj x y
    · rw [adjMat_apply, adjMat_apply, if_pos h, if_pos (hadj x y h)]
    · rw [adjMat_apply, if_neg h, zero_mul]
      exact mul_nonneg (adjMat_nonneg G _ _) hnn
  have h4 := G.rayleigh_le_lambdaMax w
  rw [hnormw] at h4
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- **The spectral radius is at most `n - 1`**, since no degree exceeds `n - 1`.  The bound is
attained by `Kₙ`, which is where every graph sits. -/
theorem lambdaMax_le_card_sub_one (G : CGraph) [Nonempty G.V] :
    G.lambdaMax ≤ (Fintype.card G.V : ℝ) - 1 := by
  have h := G.lambdaMax_le_maxDeg
  have h2 := G.maxDeg_lt_card (Classical.arbitrary G.V)
  have h3 : ((G.maxDeg : ℝ)) ≤ (Fintype.card G.V : ℝ) - 1 := by
    have : (G.maxDeg + 1 : ℕ) ≤ Fintype.card G.V := h2
    have := (Nat.cast_le (α := ℝ)).2 this
    push_cast at this
    linarith
  linarith

/-- **A bipartite graph's least eigenvalue is minus its spectral radius.**  The spectrum is
symmetric about zero, so `-λ_max` is itself an eigenvalue, and `-lambdaMax ≤ lambdaMin` always.
The converse, `isBipartite_iff_lambdaMin_eq_neg_lambdaMax`, needs connectedness. -/
theorem lambdaMin_eq_neg_lambdaMax_of_isBipartite {G : CGraph} [Nonempty G.V]
    (h : G.IsBipartite) : G.lambdaMin = -G.lambdaMax := by
  refine le_antisymm (lambdaMin_le ?_) (neg_lambdaMax_le_lambdaMin G)
  rw [← spectrum_neg_of_isBipartite h, Multiset.mem_map]
  exact ⟨G.lambdaMax, lambdaMax_mem_spectrum G, rfl⟩

/-- **A regular bipartite graph has least eigenvalue `-k`.** -/
theorem lambdaMin_of_isRegularWith_of_isBipartite {G : CGraph} [Nonempty G.V] {k : ℕ}
    (hr : G.IsRegularWith k) (hb : G.IsBipartite) : G.lambdaMin = -k := by
  rw [lambdaMin_eq_neg_lambdaMax_of_isBipartite hb, lambdaMax_of_isRegularWith hr]

/-! ### The extreme eigenvalues of the products -/

/-- **A disjoint union takes the larger of the two spectral radii.** -/
theorem lambdaMax_disjUnion (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (disjUnion G H).lambdaMax = max G.lambdaMax H.lambdaMax := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) ?_
  · rw [spectrum_disjUnion, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact (le_lambdaMax hx).trans (le_max_left _ _)
    · exact (le_lambdaMax hx).trans (le_max_right _ _)
  · refine max_le (le_lambdaMax ?_) (le_lambdaMax ?_) <;>
      rw [spectrum_disjUnion, Multiset.mem_add]
    · exact Or.inl (lambdaMax_mem_spectrum G)
    · exact Or.inr (lambdaMax_mem_spectrum H)

/-- **A disjoint union takes the smaller of the two least eigenvalues.** -/
theorem lambdaMin_disjUnion (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (disjUnion G H).lambdaMin = min G.lambdaMin H.lambdaMin := by
  refine le_antisymm (le_min (lambdaMin_le ?_) (lambdaMin_le ?_)) ?_
  · rw [spectrum_disjUnion, Multiset.mem_add]
    exact Or.inl (lambdaMin_mem_spectrum G)
  · rw [spectrum_disjUnion, Multiset.mem_add]
    exact Or.inr (lambdaMin_mem_spectrum H)
  · have hx := lambdaMin_mem_spectrum (disjUnion G H)
    rw [spectrum_disjUnion, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact (min_le_left _ _).trans (lambdaMin_le hx)
    · exact (min_le_right _ _).trans (lambdaMin_le hx)

/-- **A cartesian product adds the spectral radii**, since it adds the spectra. -/
theorem lambdaMax_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (cartesianProduct G H).lambdaMax = G.lambdaMax + H.lambdaMax := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_cartesianProduct'] at hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    exact add_le_add (le_lambdaMax h1) (le_lambdaMax h2)
  · rw [spectrum_cartesianProduct']
    exact Multiset.mem_map.2 ⟨(G.lambdaMax, H.lambdaMax), Multiset.mem_product.2
      ⟨lambdaMax_mem_spectrum G, lambdaMax_mem_spectrum H⟩, rfl⟩

/-- **A cartesian product adds the least eigenvalues** too. -/
theorem lambdaMin_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (cartesianProduct G H).lambdaMin = G.lambdaMin + H.lambdaMin := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_cartesianProduct']
    exact Multiset.mem_map.2 ⟨(G.lambdaMin, H.lambdaMin), Multiset.mem_product.2
      ⟨lambdaMin_mem_spectrum G, lambdaMin_mem_spectrum H⟩, rfl⟩
  · have hx := lambdaMin_mem_spectrum (cartesianProduct G H)
    rw [spectrum_cartesianProduct'] at hx
    obtain ⟨p, hp, hxp⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    rw [← hxp]
    exact add_le_add (lambdaMin_le h1) (lambdaMin_le h2)

/-- **A strong product multiplies the shifted spectral radii.**  The shift `1 + λ` can be
negative at other eigenvalues, but never larger in absolute value than `1 + λ_max`, since
`|λ| ≤ λ_max`. -/
theorem lambdaMax_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (strongProduct G H).lambdaMax = (1 + G.lambdaMax) * (1 + H.lambdaMax) - 1 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_strongProduct'] at hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    have ha : |1 + p.1| ≤ 1 + G.lambdaMax := by
      have := abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h1)
      rw [abs_le]
      constructor <;> linarith
    have hb : |1 + p.2| ≤ 1 + H.lambdaMax := by
      have := abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h2)
      rw [abs_le]
      constructor <;> linarith
    have := (le_abs_self ((1 + p.1) * (1 + p.2))).trans_eq (abs_mul _ _)
    have hmul : |1 + p.1| * |1 + p.2| ≤ (1 + G.lambdaMax) * (1 + H.lambdaMax) :=
      mul_le_mul ha hb (abs_nonneg _) (by linarith [G.lambdaMax_nonneg])
    linarith
  · rw [spectrum_strongProduct']
    exact Multiset.mem_map.2 ⟨(G.lambdaMax, H.lambdaMax), Multiset.mem_product.2
      ⟨lambdaMax_mem_spectrum G, lambdaMax_mem_spectrum H⟩, rfl⟩

/-- **A strong product's least eigenvalue** is the smallest of the three mixed shifted products:
`(1 + λ)(1 + μ)` is bilinear in the pair, so its minimum over the box `[λ_min, λ_max] ×
[μ_min, μ_max]` sits at a corner, and the corner `(λ_max, μ_max)` is the maximum. -/
theorem lambdaMin_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (strongProduct G H).lambdaMin
      = min (min ((1 + G.lambdaMin) * (1 + H.lambdaMin)) ((1 + G.lambdaMin) * (1 + H.lambdaMax)))
          ((1 + G.lambdaMax) * (1 + H.lambdaMin)) - 1 := by
  have hcorner : ∀ x y : ℝ, x ∈ G.spectrum → y ∈ H.spectrum →
      (strongProduct G H).lambdaMin ≤ (1 + x) * (1 + y) - 1 := by
    intro x y hx hy
    refine lambdaMin_le ?_
    rw [spectrum_strongProduct']
    exact Multiset.mem_map.2 ⟨(x, y), Multiset.mem_product.2 ⟨hx, hy⟩, rfl⟩
  refine le_antisymm ?_ ?_
  · have h1 := hcorner _ _ (lambdaMin_mem_spectrum G) (lambdaMin_mem_spectrum H)
    have h2 := hcorner _ _ (lambdaMin_mem_spectrum G) (lambdaMax_mem_spectrum H)
    have h3 := hcorner _ _ (lambdaMax_mem_spectrum G) (lambdaMin_mem_spectrum H)
    simp only [le_sub_iff_add_le, le_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · have hx := lambdaMin_mem_spectrum (strongProduct G H)
    rw [spectrum_strongProduct'] at hx
    obtain ⟨p, hp, hxp⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    rw [← hxp]
    have hG1 := lambdaMin_le h1
    have hG2 := le_lambdaMax h1
    have hH1 := lambdaMin_le h2
    have hH2 := le_lambdaMax h2
    have hGmax : (0 : ℝ) ≤ 1 + G.lambdaMax := by linarith [G.lambdaMax_nonneg]
    have hHmax : (0 : ℝ) ≤ 1 + H.lambdaMax := by linarith [H.lambdaMax_nonneg]
    have key : min (min ((1 + G.lambdaMin) * (1 + H.lambdaMin))
          ((1 + G.lambdaMin) * (1 + H.lambdaMax))) ((1 + G.lambdaMax) * (1 + H.lambdaMin))
        ≤ (1 + p.1) * (1 + p.2) := by
      rcases le_total 0 (1 + p.2) with hb | hb
      · rcases le_total 0 (1 + G.lambdaMin) with ha | ha
        · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (by nlinarith)
        · exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (by nlinarith)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    linarith

/-- **A tensor product multiplies the spectral radii.**  Every other product `x y` is smaller,
since `|x| ≤ λ_max(G)` and `|y| ≤ λ_max(H)`. -/
theorem lambdaMax_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (tensorProduct G H).lambdaMax = G.lambdaMax * H.lambdaMax := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_tensorProduct'] at hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    calc p.1 * p.2 ≤ |p.1 * p.2| := le_abs_self _
      _ = |p.1| * |p.2| := abs_mul _ _
      _ ≤ G.lambdaMax * H.lambdaMax :=
          mul_le_mul (abs_le_lambdaMax_of_mem_spectrum h1) (abs_le_lambdaMax_of_mem_spectrum h2)
            (abs_nonneg _) (lambdaMax_nonneg G)
  · rw [spectrum_tensorProduct']
    exact Multiset.mem_map.2 ⟨(G.lambdaMax, H.lambdaMax), Multiset.mem_product.2
      ⟨lambdaMax_mem_spectrum G, lambdaMax_mem_spectrum H⟩, rfl⟩

/-- **A tensor product's least eigenvalue** is the more negative of the two mixed products. -/
theorem lambdaMin_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (tensorProduct G H).lambdaMin
      = min (G.lambdaMax * H.lambdaMin) (G.lambdaMin * H.lambdaMax) := by
  refine le_antisymm ?_ ?_
  · refine le_min (lambdaMin_le ?_) (lambdaMin_le ?_) <;> rw [spectrum_tensorProduct']
    · exact Multiset.mem_map.2 ⟨(G.lambdaMax, H.lambdaMin), Multiset.mem_product.2
        ⟨lambdaMax_mem_spectrum G, lambdaMin_mem_spectrum H⟩, rfl⟩
    · exact Multiset.mem_map.2 ⟨(G.lambdaMin, H.lambdaMax), Multiset.mem_product.2
        ⟨lambdaMin_mem_spectrum G, lambdaMax_mem_spectrum H⟩, rfl⟩
  · have hx := lambdaMin_mem_spectrum (tensorProduct G H)
    rw [spectrum_tensorProduct'] at hx
    obtain ⟨p, hp, hxp⟩ := Multiset.mem_map.1 hx
    obtain ⟨h1, h2⟩ := Multiset.mem_product.1 hp
    rw [← hxp]
    have hG1 := (abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h1)).1
    have hG2 := (abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h1)).2
    have hH1 := (abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h2)).1
    have hH2 := (abs_le.1 (abs_le_lambdaMax_of_mem_spectrum h2)).2
    have hGl := lambdaMin_le h1
    have hHl := lambdaMin_le h2
    have hGmin := lambdaMin_nonpos G
    have hHmin := lambdaMin_nonpos H
    have hGmax := lambdaMax_nonneg G
    have hHmax := lambdaMax_nonneg H
    rcases le_total 0 p.1 with hp1 | hp1 <;> rcases le_total 0 p.2 with hp2 | hp2
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (min_le_right _ _) (by nlinarith)
    · exact le_trans (min_le_left _ _) (by nlinarith)

/-! ### The extreme eigenvalues of the named families -/

/-- **The spectral radius of the empty graph** is `0`: it has no edges at all. -/
theorem lambdaMax_empty (n : ℕ) : (empty (n + 1)).lambdaMax = 0 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_empty] at hx
    rw [Multiset.eq_of_mem_replicate hx]
  · rw [spectrum_empty]
    exact Multiset.mem_replicate.2 ⟨by omega, rfl⟩

/-- **The least eigenvalue of the empty graph** is `0` as well, the one graph where the two ends
coincide. -/
theorem lambdaMin_empty (n : ℕ) : (empty (n + 1)).lambdaMin = 0 := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_empty]
    exact Multiset.mem_replicate.2 ⟨by omega, rfl⟩
  · have hx := lambdaMin_mem_spectrum (empty (n + 1))
    rw [spectrum_empty] at hx
    rw [Multiset.eq_of_mem_replicate hx]

/-- **The spectral radius of a complete graph** is its degree. -/
theorem lambdaMax_complete (n : ℕ) : (complete (n + 1)).lambdaMax = n := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_complete, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    · rw [Multiset.eq_of_mem_replicate hx]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  · rw [spectrum_complete]
    exact Multiset.mem_cons_self _ _

/-- The complete graph attains it: `λ_max(Kₙ) = n - 1`. -/
theorem lambdaMax_complete_eq_card_sub_one (n : ℕ) :
    (complete (n + 1)).lambdaMax = (Fintype.card (complete (n + 1)).V : ℝ) - 1 := by
  rw [lambdaMax_complete, card_complete]
  push_cast
  ring

/-- **The least eigenvalue of a complete graph** is `-1`, with multiplicity `n - 1`. -/
theorem lambdaMin_complete (n : ℕ) : (complete (n + 2)).lambdaMin = -1 := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_complete]
    exact Multiset.mem_cons_of_mem (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)
  · have hx := lambdaMin_mem_spectrum (complete (n + 2))
    rw [spectrum_complete, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · rw [Multiset.eq_of_mem_replicate h]

/-- **The spectral radius of a cycle** is `2`, attained at the constant eigenvector. -/
theorem lambdaMax_cycle (n : ℕ) : (cycle (n + 3)).lambdaMax = 2 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_cycle (by omega), Multiset.mem_map] at hx
    obtain ⟨m, -, rfl⟩ := hx
    have := Real.cos_le_one (2 * Real.pi * m.1 / ((n + 3 : ℕ) : ℝ))
    linarith
  · rw [spectrum_cycle (by omega), Multiset.mem_map]
    refine ⟨⟨0, by omega⟩, Finset.mem_univ_val _, ?_⟩
    norm_num

/-- **The least eigenvalue of an even cycle** is `-2`: the even cycle is bipartite, so the
spectral radius is attained at both ends. -/
theorem lambdaMin_cycle_even (n : ℕ) : (cycle (2 * n + 4)).lambdaMin = -2 := by
  have hn0 : ((2 * n + 4 : ℕ) : ℝ) ≠ 0 := by positivity
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_cycle (by omega), Multiset.mem_map]
    refine ⟨⟨n + 2, by omega⟩, Finset.mem_univ_val _, ?_⟩
    have harg : 2 * Real.pi * ((⟨n + 2, by omega⟩ : Fin (2 * n + 4)) : ℕ)
        / ((2 * n + 4 : ℕ) : ℝ) = Real.pi := by
      push_cast
      field_simp
      ring
    rw [harg, Real.cos_pi]
    norm_num
  · have hx := lambdaMin_mem_spectrum (cycle (2 * n + 4))
    rw [spectrum_cycle (by omega), Multiset.mem_map] at hx
    obtain ⟨m, -, hm⟩ := hx
    have := Real.neg_one_le_cos (2 * Real.pi * m.1 / ((2 * n + 4 : ℕ) : ℝ))
    rw [← hm]
    linarith

/-- **The least eigenvalue of an odd cycle** is `-2 cos (π / n)`: no angle `2 π m / n` lands on
`π` when `n` is odd, and the closest one misses it by `π / n`. -/
theorem lambdaMin_cycle_odd (n : ℕ) :
    (cycle (2 * n + 3)).lambdaMin = -2 * Real.cos (Real.pi / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_cycle (by omega), Multiset.mem_map]
    refine ⟨⟨n + 1, by omega⟩, Finset.mem_univ_val _, ?_⟩
    have harg : 2 * Real.pi * ((⟨n + 1, by omega⟩ : Fin (2 * n + 3)) : ℕ) / ((2 * n + 3 : ℕ) : ℝ)
        = Real.pi - Real.pi / ((2 * n + 3 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [harg, Real.cos_pi_sub]
    ring
  · have hx := lambdaMin_mem_spectrum (cycle (2 * n + 3))
    rw [spectrum_cycle (by omega), Multiset.mem_map] at hx
    obtain ⟨m, -, hm⟩ := hx
    have hmlt : m.1 < 2 * n + 3 := m.isLt
    have hmR : ((m.1 : ℕ) : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) - 1 := by
      have : (m.1 : ℕ) ≤ 2 * n + 2 := by omega
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this ⊢
      linarith
    have hm0 : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
    rw [← hm]
    by_cases h : 2 * m.1 ≤ 2 * n + 3
    · have h2m : 2 * (m.1 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) - 1 := by
        have : 2 * m.1 ≤ 2 * n + 2 := by omega
        have := (Nat.cast_le (α := ℝ)).2 this
        push_cast at this ⊢
        linarith
      have h1 : Real.pi / ((2 * n + 3 : ℕ) : ℝ)
          ≤ Real.pi - 2 * Real.pi * m.1 / ((2 * n + 3 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hN, sub_mul, div_mul_cancel₀ _ (ne_of_gt hN)]
        nlinarith
      have h2 : Real.pi - 2 * Real.pi * m.1 / ((2 * n + 3 : ℕ) : ℝ) ≤ Real.pi := by
        have : 0 ≤ 2 * Real.pi * m.1 / ((2 * n + 3 : ℕ) : ℝ) := by positivity
        linarith
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) h2 h1
      rw [Real.cos_pi_sub] at hcos
      linarith
    · push_neg at h
      have h1 : Real.pi / ((2 * n + 3 : ℕ) : ℝ)
          ≤ 2 * Real.pi * m.1 / ((2 * n + 3 : ℕ) : ℝ) - Real.pi := by
        rw [div_le_iff₀ hN, sub_mul, div_mul_cancel₀ _ (ne_of_gt hN)]
        have : ((2 * n + 3 : ℕ) : ℝ) + 1 ≤ 2 * (m.1 : ℝ) := by
          have : 2 * n + 3 + 1 ≤ 2 * m.1 := by omega
          have := (Nat.cast_le (α := ℝ)).2 this
          push_cast at this ⊢
          linarith
        nlinarith
      have h2 : 2 * Real.pi * m.1 / ((2 * n + 3 : ℕ) : ℝ) - Real.pi ≤ Real.pi := by
        rw [sub_le_iff_le_add, div_le_iff₀ hN]
        nlinarith
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) h2 h1
      rw [Real.cos_sub_pi] at hcos
      linarith

/-- **The spectral radius of a path** is `2 cos (π / (n + 2))`, just under `2`: cosine is
decreasing, so the largest of the path's eigenvalues is the one at the smallest angle. -/
theorem lambdaMax_path (n : ℕ) :
    (path (n + 1)).lambdaMax = 2 * Real.cos (Real.pi / ((n : ℝ) + 2)) := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_path, Multiset.mem_map] at hx
    obtain ⟨m, -, rfl⟩ := hx
    have hm : (m.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 m.isLt
    have hle : Real.pi / ((n : ℝ) + 2) ≤ Real.pi * ((m.1 : ℝ) + 1) / (((n : ℕ) : ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : (0 : ℝ) ≤ Real.pi * (m.1 : ℝ) * ((n : ℝ) + 2) := by positivity
      nlinarith
    have hub : Real.pi * ((m.1 : ℝ) + 1) / (((n : ℕ) : ℝ) + 1 + 1) ≤ Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hub hle
    push_cast
    push_cast at this
    linarith
  · rw [spectrum_path, Multiset.mem_map]
    refine ⟨⟨0, by omega⟩, Finset.mem_univ_val _, ?_⟩
    push_cast
    ring_nf

/-- **The least eigenvalue of a path** is `-2 cos (π / (n + 2))`: the path is bipartite, so its
spectrum is symmetric about zero, and the extreme angle at the other end is `π - π / (n + 2)`. -/
theorem lambdaMin_path (n : ℕ) :
    (path (n + 1)).lambdaMin = -(2 * Real.cos (Real.pi / ((n : ℝ) + 2))) := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlast : Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 2) = Real.pi - Real.pi / ((n : ℝ) + 2) := by
    field_simp
    ring
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_path, Multiset.mem_map]
    refine ⟨⟨n, by omega⟩, Finset.mem_univ_val _, ?_⟩
    push_cast
    rw [show Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1)
        = Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 2) by ring_nf, hlast, Real.cos_pi_sub]
    ring
  · have hx := lambdaMin_mem_spectrum (path (n + 1))
    rw [spectrum_path, Multiset.mem_map] at hx
    obtain ⟨m, -, hm⟩ := hx
    have hmn : (m.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 m.isLt
    have hle : Real.pi * ((m.1 : ℝ) + 1) / (((n : ℕ) : ℝ) + 1 + 1)
        ≤ Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : (0 : ℝ) ≤ Real.pi * ((n : ℝ) - (m.1 : ℝ)) * ((n : ℝ) + 2) := by
        have : (0 : ℝ) ≤ (n : ℝ) - (m.1 : ℝ) := by linarith
        positivity
      nlinarith
    have hnn : (0 : ℝ) ≤ Real.pi * ((m.1 : ℝ) + 1) / (((n : ℕ) : ℝ) + 1 + 1) := by positivity
    have hub : Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hnn hub hle
    rw [hlast, Real.cos_pi_sub] at hcos
    rw [← hm]
    push_cast
    linarith

/-- **The spectral radius of a complete bipartite graph** is `√(mn)`: its spectrum is
`±√(mn)` together with zeros. -/
theorem lambdaMax_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).lambdaMax = Real.sqrt ((m + 1) * (n + 1)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) := Real.sqrt_nonneg _
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_bipartite] at hx
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · linarith
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hs
  · rw [spectrum_bipartite]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of a complete bipartite graph** is `-√(mn)`: the graph is bipartite,
so its spectrum is symmetric. -/
theorem lambdaMin_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).lambdaMin = -Real.sqrt ((m + 1) * (n + 1)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) := Real.sqrt_nonneg _
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_bipartite]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · have hx := lambdaMin_mem_spectrum (bipartite (m + 1) (n + 1))
    rw [spectrum_bipartite] at hx
    rcases Multiset.mem_cons.1 hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_cons.1 h with h | h
    · rw [h]
    · rw [Multiset.eq_of_mem_replicate h]; linarith

/-- **The spectral radius of a star** is `√n`, the bound `√Δ ≤ λ_max` attained. -/
theorem lambdaMax_star (n : ℕ) : (star (n + 1)).lambdaMax = Real.sqrt (n + 1) := by
  have hs : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_star] at hx
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · linarith
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hs
  · rw [spectrum_star]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of a star** is `-√n`. -/
theorem lambdaMin_star (n : ℕ) : (star (n + 1)).lambdaMin = -Real.sqrt (n + 1) := by
  have hs : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_star]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · have hx := lambdaMin_mem_spectrum (star (n + 1))
    rw [spectrum_star] at hx
    rcases Multiset.mem_cons.1 hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_cons.1 h with h | h
    · rw [h]
    · rw [Multiset.eq_of_mem_replicate h]; linarith

/-- The complete graph `K_{n+1}` is `n`-regular. -/
theorem isRegularWith_complete (n : ℕ) : (complete (n + 1)).IsRegularWith n := by
  intro i
  have hnb : (complete (n + 1)).toSimple.neighborFinset i = Finset.univ.erase i := by
    ext j
    simp [SimpleGraph.mem_neighborFinset, ne_comm]
  rw [SimpleGraph.degree, hnb, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  simp

instance instNonemptyWheelV (n : ℕ) : Nonempty (wheel n).V := ⟨Sum.inl ⟨0, by omega⟩⟩

instance instNonemptyJoinV (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V] :
    Nonempty (join G H).V := inferInstanceAs (Nonempty (G.V ⊕ H.V))

open Matrix in
/-- **The join's eigenvector equation.**  If `G` is `k`-regular on `n` vertices and `H` is
`l`-regular on `m` vertices, then a vector that is constant `a` on `G` and constant `b` on `H` is
an eigenvector of `G ∇ H` for `λ` as soon as the two scalar equations `k a + m b = λ a` and
`n a + l b = λ b` hold. -/
theorem adjMat_mulVec_join {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V] {k l : ℕ}
    (hG : G.IsRegularWith k) (hH : H.IsRegularWith l) {a b lam : ℝ}
    (h1 : (k : ℝ) * a + Fintype.card H.V * b = lam * a)
    (h2 : Fintype.card G.V * a + (l : ℝ) * b = lam * b) :
    (join G H).adjMat *ᵥ Sum.elim (fun _ ↦ a) (fun _ ↦ b)
      = lam • Sum.elim (fun _ ↦ a) (fun _ ↦ b) := by
  set w : (join G H).V → ℝ := Sum.elim (fun _ ↦ a) (fun _ ↦ b) with hwdef
  funext i
  rcases i with u | v
  · have hsplit : ((join G H).adjMat *ᵥ w) (Sum.inl u)
        = (∑ u' : G.V, (join G H).adjMat (Sum.inl u) (Sum.inl u') * w (Sum.inl u'))
          + ∑ v' : H.V, (join G H).adjMat (Sum.inl u) (Sum.inr v') * w (Sum.inr v') :=
      Fintype.sum_sum_type (f := fun x ↦ (join G H).adjMat (Sum.inl u) x * w x)
    have e1 : ∀ u' : G.V, (join G H).adjMat (Sum.inl u) (Sum.inl u') * w (Sum.inl u')
        = G.adjMat u u' * a := by
      intro u'
      rw [adjMat_apply, adjMat_apply, join_adj_inl_inl]
      simp [hwdef]
    have e2 : ∀ v' : H.V, (join G H).adjMat (Sum.inl u) (Sum.inr v') * w (Sum.inr v') = b := by
      intro v'
      rw [adjMat_apply, join_adj_inl_inr]
      simp [hwdef]
    rw [hsplit, Finset.sum_congr rfl fun u' _ ↦ e1 u', Finset.sum_congr rfl fun v' _ ↦ e2 v',
      ← Finset.sum_mul, sum_adjMat_row hG]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Pi.smul_apply, smul_eq_mul,
      hwdef, Sum.elim_inl]
    linarith
  · have hsplit : ((join G H).adjMat *ᵥ w) (Sum.inr v)
        = (∑ u' : G.V, (join G H).adjMat (Sum.inr v) (Sum.inl u') * w (Sum.inl u'))
          + ∑ v' : H.V, (join G H).adjMat (Sum.inr v) (Sum.inr v') * w (Sum.inr v') :=
      Fintype.sum_sum_type (f := fun x ↦ (join G H).adjMat (Sum.inr v) x * w x)
    have e1 : ∀ u' : G.V, (join G H).adjMat (Sum.inr v) (Sum.inl u') * w (Sum.inl u') = a := by
      intro u'
      rw [adjMat_apply, join_adj_inr_inl]
      simp [hwdef]
    have e2 : ∀ v' : H.V, (join G H).adjMat (Sum.inr v) (Sum.inr v') * w (Sum.inr v')
        = H.adjMat v v' * b := by
      intro v'
      rw [adjMat_apply, adjMat_apply, join_adj_inr_inr]
      simp [hwdef]
    rw [hsplit, Finset.sum_congr rfl fun u' _ ↦ e1 u', Finset.sum_congr rfl fun v' _ ↦ e2 v',
      ← Finset.sum_mul, sum_adjMat_row hH]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Pi.smul_apply, smul_eq_mul,
      hwdef, Sum.elim_inr]
    linarith

/-- **The spectral radius of the join of two regular graphs** is the larger root of
`(x - k) (x - l) = n m`: the eigenvector above is positive there, and a positive eigenvector's
eigenvalue bounds the whole spectrum. -/
theorem lambdaMax_join_of_isRegularWith {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] {k l : ℕ} (hG : G.IsRegularWith k) (hH : H.IsRegularWith l) :
    (join G H).lambdaMax
      = ((k : ℝ) + l
          + Real.sqrt (((k : ℝ) - l) ^ 2 + 4 * Fintype.card G.V * Fintype.card H.V)) / 2 := by
  set n : ℕ := Fintype.card G.V with hn
  set m : ℕ := Fintype.card H.V with hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Fintype.card_pos (α := G.V)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Fintype.card_pos (α := H.V)
  set r : ℝ := Real.sqrt (((k : ℝ) - l) ^ 2 + 4 * (n : ℝ) * (m : ℝ)) with hr
  have hr2 : r ^ 2 = ((k : ℝ) - l) ^ 2 + 4 * (n : ℝ) * (m : ℝ) := Real.sq_sqrt (by positivity)
  have hrk : |(k : ℝ) - l| < r := by
    have hrpos : 0 ≤ r := Real.sqrt_nonneg _
    nlinarith [abs_nonneg ((k : ℝ) - l), sq_abs ((k : ℝ) - l)]
  set lam : ℝ := ((k : ℝ) + l + r) / 2 with hlam
  have hbpos : 0 < lam - k := by
    have := lt_of_abs_lt hrk
    rw [hlam]; linarith
  have h1 : (k : ℝ) * (m : ℝ) + (m : ℝ) * (lam - k) = lam * (m : ℝ) := by ring
  have h2 : (n : ℝ) * (m : ℝ) + (l : ℝ) * (lam - k) = lam * (lam - k) := by
    rw [hlam]; nlinarith
  have hmul := adjMat_mulVec_join hG hH h1 h2
  have hwpos : ∀ i : (join G H).V, 0 < Sum.elim (fun _ ↦ (m : ℝ)) (fun _ ↦ lam - k) i := by
    rintro (u | v)
    · exact hm0
    · exact hbpos
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · exact spectrum_le_of_mulVec_le hwpos (fun i ↦ le_of_eq (congrFun hmul i)) hx
  · exact mem_spectrum_of_mulVec_eq hwpos hmul

/-- **The smaller root of the join quadratic is an eigenvalue too**, so it bounds the least
eigenvalue of `G ∇ H` from above.  It need not *be* the least one: the two factors keep their own
eigenvalues on the vectors that sum to zero on each side. -/
theorem lambdaMin_join_of_isRegularWith_le {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] {k l : ℕ} (hG : G.IsRegularWith k) (hH : H.IsRegularWith l) :
    (join G H).lambdaMin
      ≤ ((k : ℝ) + l
          - Real.sqrt (((k : ℝ) - l) ^ 2 + 4 * Fintype.card G.V * Fintype.card H.V)) / 2 := by
  set n : ℕ := Fintype.card G.V with hn
  set m : ℕ := Fintype.card H.V with hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Fintype.card_pos (α := G.V)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Fintype.card_pos (α := H.V)
  set r : ℝ := Real.sqrt (((k : ℝ) - l) ^ 2 + 4 * (n : ℝ) * (m : ℝ)) with hr
  have hr2 : r ^ 2 = ((k : ℝ) - l) ^ 2 + 4 * (n : ℝ) * (m : ℝ) := Real.sq_sqrt (by positivity)
  set lam : ℝ := ((k : ℝ) + l - r) / 2 with hlam
  have h1 : (k : ℝ) * (m : ℝ) + (m : ℝ) * (lam - k) = lam * (m : ℝ) := by ring
  have h2 : (n : ℝ) * (m : ℝ) + (l : ℝ) * (lam - k) = lam * (lam - k) := by
    rw [hlam]; nlinarith
  refine lambdaMin_le ((mem_spectrum_iff _ lam).2 ⟨_, ?_, adjMat_mulVec_join hG hH h1 h2⟩)
  intro h0
  have := congrFun h0 (Sum.inl (Classical.arbitrary G.V))
  simp only [Sum.elim_inl, Pi.zero_apply] at this
  exact absurd this (ne_of_gt hm0)

/-- **The spectral radius of a cone over a regular graph.**  Joining a single vertex to every
vertex of a `k`-regular graph on `n` vertices gives spectral radius `(k + √(k² + 4 n)) / 2`, the
positive root of `x² - k x - n`: the apex eigenvector above is positive at this root, and a
positive eigenvector's eigenvalue bounds the whole spectrum. -/
theorem lambdaMax_join_complete_one {G : CGraph} [DecidableEq G.V] [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) :
    (join (complete 1) G).lambdaMax
      = ((k : ℝ) + Real.sqrt ((k : ℝ) ^ 2 + 4 * Fintype.card G.V)) / 2 := by
  rw [lambdaMax_join_of_isRegularWith (isRegularWith_complete 0) h, card_complete]
  norm_num

/-- **The spectral radius of a wheel** is `1 + √(n + 1)`: the wheel is the cone over a `2`-regular
cycle, so this is the cone formula at `k = 2`. -/
theorem lambdaMax_wheel (m : ℕ) :
    (wheel (m + 3)).lambdaMax = 1 + Real.sqrt ((m : ℝ) + 4) := by
  have h := lambdaMax_join_complete_one (IsoGraph.isRegularWith_cycle m)
  rw [card_cycle] at h
  show (join (complete 1) (cycle (m + 3))).lambdaMax = _
  rw [h, show ((2 : ℕ) : ℝ) ^ 2 + 4 * ((m + 3 : ℕ) : ℝ) = 2 ^ 2 * ((m : ℝ) + 4) by push_cast; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  push_cast
  ring

/-- **The negative root of the cone quadratic is an eigenvalue too**, so it bounds the least
eigenvalue of `K₁ ∇ G` from above.  It need not *be* the least one: for a wheel with an even rim
the rim's own `-2` is smaller. -/
theorem lambdaMin_join_complete_one_le {G : CGraph} [DecidableEq G.V] [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) :
    (join (complete 1) G).lambdaMin
      ≤ ((k : ℝ) - Real.sqrt ((k : ℝ) ^ 2 + 4 * Fintype.card G.V)) / 2 := by
  have h1 := lambdaMin_join_of_isRegularWith_le (isRegularWith_complete 0) h
  rw [card_complete] at h1
  refine h1.trans (le_of_eq ?_)
  norm_num

/-- **The least eigenvalue of a wheel is at most `1 - √(n + 1)`**, the negative root of the cone
quadratic at `k = 2`.  Equality can fail: an even rim contributes `-2`, which is smaller as soon
as the rim has more than three vertices. -/
theorem lambdaMin_wheel_le (m : ℕ) :
    (wheel (m + 3)).lambdaMin ≤ 1 - Real.sqrt ((m : ℝ) + 4) := by
  have h := lambdaMin_join_complete_one_le (IsoGraph.isRegularWith_cycle m)
  rw [card_cycle] at h
  show (join (complete 1) (cycle (m + 3))).lambdaMin ≤ _
  refine h.trans (le_of_eq ?_)
  rw [show ((2 : ℕ) : ℝ) ^ 2 + 4 * ((m + 3 : ℕ) : ℝ) = 2 ^ 2 * ((m : ℝ) + 4) by push_cast; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  push_cast
  ring

/-- **The spectral radius of a grid** is the sum of the two paths'. -/
theorem lambdaMax_grid (m n : ℕ) :
    (cartesianProduct (path (m + 1)) (path (n + 1))).lambdaMax
      = 2 * Real.cos (Real.pi / ((m : ℝ) + 2)) + 2 * Real.cos (Real.pi / ((n : ℝ) + 2)) := by
  rw [lambdaMax_cartesianProduct, lambdaMax_path, lambdaMax_path]

/-- **The least eigenvalue of a grid** is minus the sum of the two paths' radii. -/
theorem lambdaMin_grid (m n : ℕ) :
    (cartesianProduct (path (m + 1)) (path (n + 1))).lambdaMin
      = -(2 * Real.cos (Real.pi / ((m : ℝ) + 2))) + -(2 * Real.cos (Real.pi / ((n : ℝ) + 2))) := by
  rw [lambdaMin_cartesianProduct, lambdaMin_path, lambdaMin_path]

/-- **The spectral radius of a torus** is `4`, the degree: `Cₘ □ Cₙ` is `4`-regular. -/
theorem lambdaMax_torus (m n : ℕ) :
    (cartesianProduct (cycle (m + 3)) (cycle (n + 3))).lambdaMax = 4 := by
  rw [lambdaMax_cartesianProduct, lambdaMax_cycle, lambdaMax_cycle]
  norm_num

/-- **The least eigenvalue of a torus with two even sides** is `-4`: both cycles reach `-2`. -/
theorem lambdaMin_torus_even (m n : ℕ) :
    (cartesianProduct (cycle (2 * m + 4)) (cycle (2 * n + 4))).lambdaMin = -4 := by
  rw [lambdaMin_cartesianProduct, lambdaMin_cycle_even, lambdaMin_cycle_even]
  norm_num

/-- **The spectral radius of a prism** `Cₙ □ K₂` is `3`, its degree. -/
theorem lambdaMax_prism (n : ℕ) : (prism (n + 3)).lambdaMax = 3 := by
  have h2 : (complete 2).lambdaMax = 1 := by
    show (complete (1 + 1)).lambdaMax = 1
    rw [lambdaMax_complete]; norm_num
  show (cartesianProduct (cycle (n + 3)) (complete 2)).lambdaMax = 3
  rw [lambdaMax_cartesianProduct, lambdaMax_cycle, h2]
  norm_num

/-- **The least eigenvalue of a prism with an even cycle** is `-3`. -/
theorem lambdaMin_prism_even (n : ℕ) : (prism (2 * n + 4)).lambdaMin = -3 := by
  have h2 : (complete 2).lambdaMin = -1 := by
    show (complete (0 + 2)).lambdaMin = -1
    rw [lambdaMin_complete]
  show (cartesianProduct (cycle (2 * n + 4)) (complete 2)).lambdaMin = -3
  rw [lambdaMin_cartesianProduct, lambdaMin_cycle_even, h2]
  norm_num

/-- **The spectral radius of a ladder** `Pₙ □ K₂` is the path's, shifted up by `1`. -/
theorem lambdaMax_ladder (n : ℕ) :
    (ladder (n + 1)).lambdaMax = 2 * Real.cos (Real.pi / ((n : ℝ) + 2)) + 1 := by
  have h2 : (complete 2).lambdaMax = 1 := by
    show (complete (1 + 1)).lambdaMax = 1
    rw [lambdaMax_complete]; norm_num
  show (cartesianProduct (path (n + 1)) (complete 2)).lambdaMax = _
  rw [lambdaMax_cartesianProduct, lambdaMax_path, h2]

/-- **The least eigenvalue of a ladder** is minus its radius: the ladder is bipartite, so unlike
the prism it needs no parity hypothesis. -/
theorem lambdaMin_ladder (n : ℕ) :
    (ladder (n + 1)).lambdaMin = -(2 * Real.cos (Real.pi / ((n : ℝ) + 2))) + -1 := by
  have h2 : (complete 2).lambdaMin = -1 := by
    show (complete (0 + 2)).lambdaMin = -1
    rw [lambdaMin_complete]
  show (cartesianProduct (path (n + 1)) (complete 2)).lambdaMin = _
  rw [lambdaMin_cartesianProduct, lambdaMin_path, h2]

/-! ### The extreme eigenvalues of the strongly regular families

Each of these graphs has an explicit spectrum above, with the degree at the top and one other
eigenvalue at the bottom, so both ends are read off the same three-way case split.  The four
integral families all bottom out at `-2`, which is no accident: the Petersen graph, the rook's
graph and the triangular graph are line graphs or complements of them.  Only the Paley graph has
irrational ends. -/

instance : Nonempty SRG.petersen.V :=
  Fintype.card_pos_iff.1 (by rw [SRG.petersen_srg.card]; norm_num)

instance (m : ℕ) : Nonempty (cocktailParty (m + 2)).V :=
  Fintype.card_pos_iff.1 (by rw [(isSRGWith_cocktailParty (m + 2)).card]; omega)

instance (m : ℕ) : Nonempty (triangular (m + 4)).V :=
  Fintype.card_pos_iff.1 (by
    rw [(isSRGWith_triangular (m + 4) (by omega)).card]; exact Nat.choose_pos (by omega))

/-- **The spectral radius of the Petersen graph** is its degree `3`. -/
theorem lambdaMax_petersen : SRG.petersen.lambdaMax = 3 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_petersen, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; norm_num
    · rw [Multiset.eq_of_mem_replicate hx]; norm_num
  · rw [spectrum_petersen]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the Petersen graph** is `-2`, as for every line graph. -/
theorem lambdaMin_petersen : SRG.petersen.lambdaMin = -2 := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_petersen]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by norm_num, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum SRG.petersen
    rw [spectrum_petersen, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; norm_num
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]; norm_num
    · rw [Multiset.eq_of_mem_replicate h]

/-- **The spectral radius of the cocktail party graph** is its degree `2n - 2`. -/
theorem lambdaMax_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).lambdaMax = 2 * (m : ℝ) + 2 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_cocktailParty, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; positivity
    · rw [Multiset.eq_of_mem_replicate hx]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
  · rw [spectrum_cocktailParty]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the cocktail party graph** is `-2`. -/
theorem lambdaMin_cocktailParty (m : ℕ) : (cocktailParty (m + 2)).lambdaMin = -2 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_cocktailParty]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum (cocktailParty (m + 2))
    rw [spectrum_cocktailParty, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]; norm_num
    · rw [Multiset.eq_of_mem_replicate h]

/-- **The spectral radius of the rook's graph** is its degree `2n - 2`. -/
theorem lambdaMax_rook (k : ℕ) : (rook (k + 2) (k + 2)).lambdaMax = 2 * (k : ℝ) + 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_rook, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
  · rw [spectrum_rook]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the rook's graph** is `-2`. -/
theorem lambdaMin_rook (k : ℕ) : (rook (k + 2) (k + 2)).lambdaMin = -2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_rook]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by positivity, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum (rook (k + 2) (k + 2))
    rw [spectrum_rook, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]; linarith
    · rw [Multiset.eq_of_mem_replicate h]

/-- **The spectral radius of the triangular graph** is its degree `2n - 4`. -/
theorem lambdaMax_triangular (m : ℕ) : (triangular (m + 4)).lambdaMax = 2 * (m : ℝ) + 4 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_triangular, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
  · rw [spectrum_triangular]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the triangular graph** is `-2`. -/
theorem lambdaMin_triangular (m : ℕ) : (triangular (m + 4)).lambdaMin = -2 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcard : m + 4 < (m + 4).choose 2 := by
    have h2 : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
      rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 from by omega]
    have h3 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    omega
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_triangular]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum (triangular (m + 4))
    rw [spectrum_triangular, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]; linarith
    · rw [Multiset.eq_of_mem_replicate h]

/-- **The spectral radius of the Paley graph** `P(4t+1)` is its degree `2t`. -/
theorem lambdaMax_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).lambdaMax = 2 * (t : ℝ) := by
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hq0 : (0 : ℝ) ≤ Real.sqrt (4 * (t : ℝ) + 1) := Real.sqrt_nonneg _
  have hq2 : Real.sqrt (4 * (t : ℝ) + 1) ^ 2 = 4 * (t : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_paley t ht, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
      nlinarith [sq_nonneg (Real.sqrt (4 * (t : ℝ) + 1) - 1)]
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
  · rw [spectrum_paley t ht]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the Paley graph** `P(4t+1)` is `(-1 - √(4t+1)) / 2`. -/
theorem lambdaMin_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).lambdaMin = (-1 - Real.sqrt (4 * (t : ℝ) + 1)) / 2 := by
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hq0 : (0 : ℝ) ≤ Real.sqrt (4 * (t : ℝ) + 1) := Real.sqrt_nonneg _
  have hq2 : Real.sqrt (4 * (t : ℝ) + 1) ^ 2 = 4 * (t : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_paley t ht]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum (paley (4 * t + 1))
    rw [spectrum_paley t ht, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]; linarith
    · rw [Multiset.eq_of_mem_replicate h]

/-! ### The equality case: regularity is spectral -/

/-- **The equality case of the variational principle**: a vector whose Rayleigh quotient attains
`lambdaMax` is an eigenvector for it.  In rotated coordinates the quotient is a weighted average
of the eigenvalues, so it can only reach the largest one on the corresponding eigenspace. -/
theorem mulVec_eq_of_rayleigh_eq_lambdaMax (G : CGraph) [Nonempty G.V] {v : G.V → ℝ}
    (hv : v ⬝ᵥ (G.adjMat *ᵥ v) = G.lambdaMax * (v ⬝ᵥ v)) :
    G.adjMat *ᵥ v = G.lambdaMax • v := by
  obtain ⟨U, hUU, hUU', hD⟩ := G.exists_orthogonal_diagonal
  have hA : G.adjMat = U * Matrix.diagonal G.eigenvalues * Uᵀ := by
    rw [← hD]
    calc G.adjMat = U * Uᵀ * G.adjMat * (U * Uᵀ) := by rw [hUU', one_mul, mul_one]
      _ = U * (Uᵀ * G.adjMat * U) * Uᵀ := by simp only [mul_assoc]
  obtain ⟨w, hw⟩ : ∃ w : G.V → ℝ, w = Uᵀ *ᵥ v := ⟨_, rfl⟩
  have hUw : U *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hAv : G.adjMat *ᵥ v = U *ᵥ (Matrix.diagonal G.eigenvalues *ᵥ w) := by
    rw [hA, hw, show (U * Matrix.diagonal G.eigenvalues * Uᵀ) *ᵥ v
      = U *ᵥ (Matrix.diagonal G.eigenvalues *ᵥ (Uᵀ *ᵥ v)) by
      simp only [Matrix.mulVec_mulVec, mul_assoc]]
  have hvT : ∀ x : G.V → ℝ, x ᵥ* U = Uᵀ *ᵥ x := fun x ↦ by
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  have hTU : ∀ x : G.V → ℝ, Uᵀ *ᵥ (U *ᵥ x) = x := fun x ↦ by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have h1 : v ⬝ᵥ (G.adjMat *ᵥ v) = ∑ i, G.eigenvalues i * w i ^ 2 := by
    rw [hAv, ← hUw, dotProduct_mulVec, hvT, hTU]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h2 : v ⬝ᵥ v = ∑ i, w i ^ 2 := by
    rw [← hUw, dotProduct_mulVec, hvT, hTU]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  -- every coordinate off the top eigenspace has to vanish
  have hsum : ∑ i, (G.lambdaMax - G.eigenvalues i) * w i ^ 2 = 0 := by
    have hvv := hv
    rw [h1, h2, Finset.mul_sum] at hvv
    have hsplit : ∑ i, (G.lambdaMax - G.eigenvalues i) * w i ^ 2
        = (∑ i, G.lambdaMax * w i ^ 2) - ∑ i, G.eigenvalues i * w i ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsplit, hvv, sub_self]
  have hzero : ∀ i, (G.lambdaMax - G.eigenvalues i) * w i ^ 2 = 0 :=
    fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      mul_nonneg (sub_nonneg.2 (le_lambdaMax (G.eigenvalues_mem_spectrum j))) (sq_nonneg _)).1
      hsum i (Finset.mem_univ i)
  have hd : ∀ i, G.eigenvalues i * w i = G.lambdaMax * w i := by
    intro i
    rcases mul_eq_zero.1 (hzero i) with h | h
    · rw [sub_eq_zero.1 h]
    · rw [pow_eq_zero_iff two_ne_zero] at h
      rw [h, mul_zero, mul_zero]
  rw [hAv, show Matrix.diagonal G.eigenvalues *ᵥ w = G.lambdaMax • w from
    funext fun i ↦ by rw [Matrix.mulVec_diagonal]; exact hd i, Matrix.mulVec_smul, hUw]

/-- **A graph whose largest eigenvalue is the average degree is regular.**  The all-ones vector
attains the Rayleigh maximum, so it is an eigenvector, and its eigenvalue equation at a vertex
says that the vertex has degree `λ_max`. -/
theorem isRegularWith_of_two_mul_E_eq (G : CGraph) [Nonempty G.V] {k : ℕ}
    (hlam : G.lambdaMax = k) (hE : 2 * G.E = Fintype.card G.V * k) : G.IsRegularWith k := by
  have hdeg : ∀ i, (G.adjMat *ᵥ fun _ : G.V ↦ (1 : ℝ)) i = (G.toSimple.degree i : ℝ) :=
    fun i ↦ by simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
  have hone : (fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ (G.adjMat *ᵥ fun _ ↦ (1 : ℝ)) = 2 * (G.E : ℝ) := by
    have hEd : G.E = G.toSimple.edgeFinset.card := rfl
    simp only [dotProduct, hdeg, one_mul]
    rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges, hEd]
    push_cast
    ring
  have hnorm : (fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ (fun _ ↦ (1 : ℝ)) = (Fintype.card G.V : ℝ) := by
    simp [dotProduct, Finset.card_univ]
  have hcast : (2 * G.E : ℝ) = (Fintype.card G.V : ℝ) * k := by exact_mod_cast hE
  have heq : (fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ (G.adjMat *ᵥ fun _ ↦ (1 : ℝ))
      = G.lambdaMax * ((fun _ : G.V ↦ (1 : ℝ)) ⬝ᵥ fun _ ↦ (1 : ℝ)) := by
    rw [hone, hnorm, hlam]
    push_cast at hcast ⊢
    linarith
  have hvec := G.mulVec_eq_of_rayleigh_eq_lambdaMax heq
  intro i
  have hi := congrFun hvec i
  rw [hdeg i, hlam] at hi
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at hi
  exact_mod_cast hi

/-- **Regularity is determined by the spectrum**: a graph cospectral with a `k`-regular graph is
itself `k`-regular, since the order, the size and the largest eigenvalue are all spectral. -/
@[toIsoGraph]
theorem Cospectral.isRegularWith {G H : CGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : H.IsRegularWith k := by
  rcases isEmpty_or_nonempty H.V with hemp | hne
  · exact fun i ↦ (hemp.false i).elim
  haveI : Nonempty G.V := by
    rw [← Fintype.card_pos_iff] at hne ⊢
    rw [h.card_eq]
    exact hne
  have hspec : G.spectrum = H.spectrum := h.spectrum_eq
  have hlamG : G.lambdaMax = k := lambdaMax_of_isRegularWith hG
  have hlam : H.lambdaMax = k := by
    refine le_antisymm ((lambdaMax_le_iff H).2 fun x hx ↦ ?_) ?_
    · rw [← hlamG]
      exact le_lambdaMax (by rw [hspec]; exact hx)
    · exact le_lambdaMax (by rw [← hspec, ← hlamG]; exact lambdaMax_mem_spectrum G)
  have hEG : 2 * G.E = Fintype.card G.V * k := by
    have hsum : ∑ i : G.V, G.toSimple.degree i = Fintype.card G.V * k := by
      rw [Finset.sum_congr rfl fun i _ ↦ hG i, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [show G.E = G.toSimple.edgeFinset.card from rfl,
      ← SimpleGraph.sum_degrees_eq_twice_card_edges, hsum]
  exact H.isRegularWith_of_two_mul_E_eq hlam (by rw [← h.E_eq, ← h.card_eq]; exact hEG)

/-! ### Hoffman's ratio bound -/

/-- **Hoffman's ratio bound**: in a `k`-regular graph an independent set `S` satisfies
`|S| (k - λ_min) ≤ n (-λ_min)`.  The test vector is the indicator of `S`, corrected to sum to
zero; it spans no edge, so its Rayleigh quotient is `-k |S| ² / n`. -/
theorem card_mul_sub_lambdaMin_le {G : CGraph} [Nonempty G.V] {k : ℕ} (hk : G.IsRegularWith k)
    {S : Finset G.V} (hS : G.toSimple.IsIndepSet (S : Set G.V)) :
    (S.card : ℝ) * ((k : ℝ) - G.lambdaMin)
      ≤ (Fintype.card G.V : ℝ) * (-G.lambdaMin) := by
  set n : ℝ := (Fintype.card G.V : ℝ) with hn_def
  set s : ℝ := (S.card : ℝ) with hs_def
  set lm : ℝ := G.lambdaMin with hlm_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have hs0 : 0 ≤ s := by positivity
  set ind : G.V → ℝ := fun i ↦ if i ∈ S then 1 else 0 with hind_def
  -- the transpose is the matrix itself, and the all-ones vector is a `k`-eigenvector
  have htrans : G.adjMatᵀ = G.adjMat := Matrix.ext fun i j ↦ adjMat_symm G j i
  have hone : G.adjMat *ᵥ (1 : G.V → ℝ) = (k : ℝ) • (1 : G.V → ℝ) :=
    (hasEigenvector_one_of_isRegularWith hk).2
  have h1v : (1 : G.V → ℝ) ᵥ* G.adjMat = (k : ℝ) • (1 : G.V → ℝ) := by
    rw [show G.adjMat = G.adjMatᵀ from htrans.symm, Matrix.vecMul_transpose]
    exact hone
  -- the four dot products of the indicator and the all-ones vector
  have hind_one : ind ⬝ᵥ (1 : G.V → ℝ) = s := by
    simp [dotProduct, hind_def, hs_def]
  have hone_ind : (1 : G.V → ℝ) ⬝ᵥ ind = s := by
    simp [dotProduct, hind_def, hs_def]
  have hind_ind : ind ⬝ᵥ ind = s := by
    simp [dotProduct, hind_def, hs_def, mul_ite]
  have hone_one : (1 : G.V → ℝ) ⬝ᵥ (1 : G.V → ℝ) = n := by
    simp [dotProduct, hn_def, Finset.card_univ]
  -- `S` spans no edge, so the indicator has quadratic form zero
  have hindA : ind ⬝ᵥ (G.adjMat *ᵥ ind) = 0 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · by_cases hij : i = j
        · subst hij; simp [adjMat_apply, G.loopless i]
        · have hadj : ¬ G.toSimple.Adj i j := hS hi hj hij
          rw [toSimple_adj] at hadj
          simp [adjMat_apply, hadj]
      · simp [hind_def, hj]
    · simp [hind_def, hi]
  -- the test vector: `n` times the indicator, corrected by `|S|` times the all-ones vector
  set v : G.V → ℝ := n • ind - s • (1 : G.V → ℝ) with hv_def
  have hnorm : v ⬝ᵥ v = n ^ 2 * s - 2 * n * s * s + s ^ 2 * n := by
    simp only [hv_def, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hind_ind, hind_one, hone_ind, hone_one]
    ring
  have hquad : v ⬝ᵥ (G.adjMat *ᵥ v) = -(2 * n * s * ((k : ℝ) * s)) + s ^ 2 * ((k : ℝ) * n) := by
    simp only [hv_def, Matrix.mulVec_sub, Matrix.mulVec_smul, hone, sub_dotProduct,
      dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hindA, hind_one,
      hone_one]
    have h1A : (1 : G.V → ℝ) ⬝ᵥ (G.adjMat *ᵥ ind) = (k : ℝ) * s := by
      rw [dotProduct_mulVec, h1v, smul_dotProduct, smul_eq_mul, hone_ind]
    rw [h1A]
    ring
  -- Rayleigh
  have hkey := G.lambdaMin_mul_le_rayleigh v
  rw [hnorm, hquad, ← hlm_def] at hkey
  have hL : n * (lm * (n * s - s * s)) = lm * (n ^ 2 * s - 2 * n * s * s + s ^ 2 * n) := by ring
  have hR : n * (-((k : ℝ) * (s * s)))
      = -(2 * n * s * ((k : ℝ) * s)) + s ^ 2 * ((k : ℝ) * n) := by ring
  have h3 : lm * (n * s - s * s) ≤ -((k : ℝ) * (s * s)) :=
    le_of_mul_le_mul_left (by rw [hL, hR]; exact hkey) hn
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]
    have : lm ≤ 0 := by rw [hlm_def]; exact G.lambdaMin_nonpos
    nlinarith
  · have h4 : lm * n - lm * s + (k : ℝ) * s ≤ 0 := by
      refine le_of_mul_le_mul_left ?_ hs
      have hE : s * (lm * n - lm * s + (k : ℝ) * s) = lm * (n * s - s * s) + (k : ℝ) * (s * s) := by
        ring
      rw [hE, mul_zero]
      linarith
    linarith

/-- **Hoffman's ratio bound** in terms of the independence number. -/
theorem indepNum_mul_sub_lambdaMin_le {G : CGraph} [Nonempty G.V] {k : ℕ}
    (hk : G.IsRegularWith k) :
    (G.indepNum : ℝ) * ((k : ℝ) - G.lambdaMin)
      ≤ (Fintype.card G.V : ℝ) * (-G.lambdaMin) := by
  obtain ⟨S, hS, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have := card_mul_sub_lambdaMin_le hk hS
  rwa [hcard] at this

/-- **Hoffman's bound on the chromatic number** of a `k`-regular graph:
`(k - λ_min) ≤ χ · (-λ_min)`, the product form of `χ ≥ 1 - k / λ_min`.  Each colour class is an
independent set, so `n ≤ χ α`, and the ratio bound `indepNum_mul_sub_lambdaMin_le` caps `α`. -/
theorem sub_lambdaMin_le_chromNum_mul {G : CGraph} [Nonempty G.V] {k : ℕ}
    (hk : G.IsRegularWith k) :
    (k : ℝ) - G.lambdaMin ≤ G.chromNum * (-G.lambdaMin) := by
  have hn : (0 : ℝ) < Fintype.card G.V := by exact_mod_cast Fintype.card_pos
  have hα := indepNum_mul_sub_lambdaMin_le hk
  have hχ : (Fintype.card G.V : ℝ) ≤ (G.chromNum : ℝ) * G.indepNum := by
    exact_mod_cast G.card_le_chromNum_mul_indepNum
  have hlm : G.lambdaMin ≤ 0 := G.lambdaMin_nonpos
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hχ0 : (0 : ℝ) ≤ (G.chromNum : ℝ) := Nat.cast_nonneg _
  have hkL : (0 : ℝ) ≤ (k : ℝ) - G.lambdaMin := by linarith
  have h1 : (Fintype.card G.V : ℝ) * ((k : ℝ) - G.lambdaMin)
      ≤ (G.chromNum : ℝ) * ((G.indepNum : ℝ) * ((k : ℝ) - G.lambdaMin)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hχ hkL
  have h2 : (G.chromNum : ℝ) * ((G.indepNum : ℝ) * ((k : ℝ) - G.lambdaMin))
      ≤ (G.chromNum : ℝ) * ((Fintype.card G.V : ℝ) * (-G.lambdaMin)) :=
    mul_le_mul_of_nonneg_left hα hχ0
  exact le_of_mul_le_mul_left (h1.trans (h2.trans (le_of_eq (by ring)))) hn

/-- Hoffman's chromatic bound in its textbook shape: for a regular graph
`λ_max - λ_min ≤ χ · (-λ_min)`, that is `χ ≥ 1 - λ_max / λ_min`. -/
theorem lambdaMax_sub_lambdaMin_le_chromNum_mul {G : CGraph} [Nonempty G.V] {k : ℕ}
    (hk : G.IsRegularWith k) :
    G.lambdaMax - G.lambdaMin ≤ G.chromNum * (-G.lambdaMin) := by
  rw [lambdaMax_of_isRegularWith hk]
  exact sub_lambdaMin_le_chromNum_mul hk

/-- The Petersen graph is triangle-free, so its clique number gives nothing, but the ratio bound
does: `3 - (-2) ≤ χ · 2` forces `3 ≤ χ`. -/
example : 3 ≤ SRG.petersen.chromNum := by
  haveI : Nonempty SRG.petersen.V :=
    Fintype.card_pos_iff.1 (by rw [SRG.petersen_srg.card]; norm_num)
  have hlm : SRG.petersen.lambdaMin = -2 := by
    refine le_antisymm (lambdaMin_le ?_) ((le_lambdaMin_iff _).2 ?_)
    · rw [spectrum_petersen]
      simp
    · intro x hx
      rw [spectrum_petersen] at hx
      simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_replicate] at hx
      rcases hx with rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have h := sub_lambdaMin_le_chromNum_mul SRG.petersen_srg.regular
  rw [hlm] at h
  by_contra hcon
  push_neg at hcon
  have h2 : (SRG.petersen.chromNum : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 hcon
  push_cast at h
  linarith

/-- **The eigenvalues of a path are all `< 2`.** -/
theorem lt_two_of_mem_spectrum_path (n : ℕ) {x : ℝ} (hx : x ∈ (path n).spectrum) : x < 2 := by
  rw [spectrum_path, Multiset.mem_map] at hx
  obtain ⟨m, -, rfl⟩ := hx
  have h0 : (0 : ℝ) < Real.pi * (m.1 + 1) / (n + 1) := by positivity
  have hpi : Real.pi * (m.1 + 1) / (n + 1) ≤ Real.pi := (path_arg_mem_Icc n m).2
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hpi h0
  rw [Real.cos_zero] at this
  linarith

/-- **The eigenvalues of a cycle are all `≤ 2`.** -/
theorem le_two_of_mem_spectrum_cycle {n : ℕ} (hn : 3 ≤ n) {x : ℝ} (hx : x ∈ (cycle n).spectrum) :
    x ≤ 2 := by
  rw [spectrum_cycle hn, Multiset.mem_map] at hx
  obtain ⟨m, -, rfl⟩ := hx
  have := Real.cos_le_one (2 * Real.pi * m.1 / n)
  linarith

/-- **The cycle attains the eigenvalue `2`**: it is the first member of Smith's family. -/
theorem two_mem_spectrum_cycle {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ∈ (cycle n).spectrum := by
  rw [spectrum_cycle hn, Multiset.mem_map]
  refine ⟨⟨0, by omega⟩, Finset.mem_univ_val _, ?_⟩
  norm_num

/-! ### Smith's family and the ADE diagrams

A connected graph whose largest eigenvalue is exactly `2` is a member of **Smith's family**: the
cycles `Ãₙ` and the affine Dynkin diagrams `D̃ₙ, Ẽ₆, Ẽ₇, Ẽ₈`.  Each of these carries a strictly
positive eigenvector for the eigenvalue `2` — the *marks* of the affine root system — and by
`le_of_mulVec_le` that positive eigenvector caps the whole spectrum at `2`.  Deleting a vertex from
a Smith graph leaves the marks as a strict subeigenvector, which is why the finite diagrams
`Aₙ, Dₙ, E₆, E₇, E₈` have all their eigenvalues `< 2`: the same vector still bounds them by `2`,
and `2` itself is not an eigenvalue because the Cartan matrix `2I - A` is nonsingular.

`Aₙ` is the path (`spectrum_path`, `lt_two_of_mem_spectrum_path`) and `Ãₙ` is the cycle
(`spectrum_cycle`, `two_mem_spectrum_cycle`); the exceptional diagrams are defined here, and the
families `Dₙ` and `D̃ₙ` are treated for all `n` at the end of the section. -/

/-- The graph has largest eigenvalue exactly `2`: it belongs to **Smith's family**. -/
def IsSmith (G : CGraph) : Prop := (2 : ℝ) ∈ G.spectrum ∧ ∀ x ∈ G.spectrum, x ≤ 2

/-- Every eigenvalue is `< 2`; for a connected graph this characterises the `ADE` diagrams. -/
def IsSubcritical (G : CGraph) : Prop := ∀ x ∈ G.spectrum, x < 2

/-- Smith's condition, as an equation on the largest eigenvalue. -/
theorem isSmith_iff_lambdaMax (G : CGraph) [Nonempty G.V] : IsSmith G ↔ G.lambdaMax = 2 := by
  refine ⟨fun ⟨h2, hle⟩ ↦ le_antisymm ((lambdaMax_le_iff G).2 hle) (le_lambdaMax h2),
    fun h ↦ ⟨h ▸ lambdaMax_mem_spectrum G, fun x hx ↦ h ▸ le_lambdaMax hx⟩⟩

theorem isSubcritical_iff_lambdaMax (G : CGraph) [Nonempty G.V] :
    IsSubcritical G ↔ G.lambdaMax < 2 :=
  (lambdaMax_lt_iff G).symm

theorem isSubcritical_path (n : ℕ) : IsSubcritical (path n) :=
  fun _ hx ↦ lt_two_of_mem_spectrum_path n hx

theorem isSmith_cycle {n : ℕ} (hn : 3 ≤ n) : IsSmith (cycle n) :=
  ⟨two_mem_spectrum_cycle hn, fun _ hx ↦ le_two_of_mem_spectrum_cycle hn hx⟩

/-- The Dynkin diagram `D₄`, the star with three edges. -/
def dynkinD4 : CGraph := ofEdges 4 [(0, 1), (0, 2), (0, 3)]

/-- The marks of the diagram `dynkinD4`. -/
def marksDynkinD4 : Fin 4 → ℝ := ![2, 1, 1, 1]

theorem marksDynkinD4_pos (i : Fin 4) : 0 < marksDynkinD4 i := by
  fin_cases i <;> norm_num [marksDynkinD4]

set_option linter.unnecessarySeqFocus false in
theorem mulVec_le_dynkinD4 (i : Fin 4) :
    (dynkinD4.adjMat *ᵥ marksDynkinD4) i ≤ 2 * marksDynkinD4 i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinD4, ofEdges, ofRel,
      marksDynkinD4] <;> norm_num

theorem two_notMem_spectrum_dynkinD4 : (2 : ℝ) ∉ dynkinD4.spectrum := by
  intro hx
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff _ _).1 hx
  have h0 := congrFun hv (0 : Fin 4)
  have h1 := congrFun hv (1 : Fin 4)
  have h2 := congrFun hv (2 : Fin 4)
  have h3 := congrFun hv (3 : Fin 4)
  simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinD4, ofEdges,
    ofRel] at h0 h1 h2 h3
  refine hv0 (funext fun i ↦ ?_)
  have e0 : v (0 : Fin 4) = 0 := by linarith
  have e1 : v (1 : Fin 4) = 0 := by linarith
  have e2 : v (2 : Fin 4) = 0 := by linarith
  have e3 : v (3 : Fin 4) = 0 := by linarith
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

theorem lt_two_of_mem_spectrum_dynkinD4 {x : ℝ} (hx : x ∈ dynkinD4.spectrum) : x < 2 :=
  lt_of_le_of_ne (spectrum_le_of_mulVec_le marksDynkinD4_pos mulVec_le_dynkinD4 hx)
    (fun h ↦ two_notMem_spectrum_dynkinD4 (h ▸ hx))

theorem isSubcritical_dynkinD4 : IsSubcritical dynkinD4 :=
  fun _ hx ↦ lt_two_of_mem_spectrum_dynkinD4 hx

/-- The affine diagram `D̃₄`, the star with four edges. -/
def affineD4 : CGraph := ofEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4)]

/-- The marks of the affine diagram `affineD4`. -/
def marksAffineD4 : Fin 5 → ℝ := ![2, 1, 1, 1, 1]

theorem marksAffineD4_pos (i : Fin 5) : 0 < marksAffineD4 i := by
  fin_cases i <;> norm_num [marksAffineD4]

set_option linter.unnecessarySeqFocus false in
theorem mulVec_affineD4 : affineD4.adjMat *ᵥ marksAffineD4 = (2 : ℝ) • marksAffineD4 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, affineD4, ofEdges, ofRel,
      marksAffineD4] <;> norm_num

theorem two_mem_spectrum_affineD4 : (2 : ℝ) ∈ affineD4.spectrum := by
  haveI : Nonempty affineD4.V := ⟨(0 : Fin 5)⟩
  exact mem_spectrum_of_mulVec_eq marksAffineD4_pos mulVec_affineD4

theorem le_two_of_mem_spectrum_affineD4 {x : ℝ} (hx : x ∈ affineD4.spectrum) : x ≤ 2 :=
  spectrum_le_of_mulVec_le marksAffineD4_pos
    (fun i ↦ by simpa using le_of_eq (congrFun mulVec_affineD4 i)) hx

theorem isSmith_affineD4 : IsSmith affineD4 :=
  ⟨two_mem_spectrum_affineD4, fun _ hx ↦ le_two_of_mem_spectrum_affineD4 hx⟩

/-- The Dynkin diagram `E₆`: arms of lengths `2, 2, 1` at a branch vertex. -/
def dynkinE6 : CGraph := ofEdges 6 [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5)]

/-- The marks of the diagram `dynkinE6`. -/
def marksDynkinE6 : Fin 6 → ℝ := ![3, 2, 1, 2, 1, 2]

theorem marksDynkinE6_pos (i : Fin 6) : 0 < marksDynkinE6 i := by
  fin_cases i <;> norm_num [marksDynkinE6]
theorem mulVec_le_dynkinE6 (i : Fin 6) :
    (dynkinE6.adjMat *ᵥ marksDynkinE6) i ≤ 2 * marksDynkinE6 i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE6, ofEdges, ofRel,
      marksDynkinE6] <;> norm_num

theorem two_notMem_spectrum_dynkinE6 : (2 : ℝ) ∉ dynkinE6.spectrum := by
  intro hx
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff _ _).1 hx
  have h0 := congrFun hv (0 : Fin 6)
  have h1 := congrFun hv (1 : Fin 6)
  have h2 := congrFun hv (2 : Fin 6)
  have h3 := congrFun hv (3 : Fin 6)
  have h4 := congrFun hv (4 : Fin 6)
  have h5 := congrFun hv (5 : Fin 6)
  simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE6, ofEdges,
    ofRel] at h0 h1 h2 h3 h4 h5
  refine hv0 (funext fun i ↦ ?_)
  have e0 : v (0 : Fin 6) = 0 := by linarith
  have e1 : v (1 : Fin 6) = 0 := by linarith
  have e2 : v (2 : Fin 6) = 0 := by linarith
  have e3 : v (3 : Fin 6) = 0 := by linarith
  have e4 : v (4 : Fin 6) = 0 := by linarith
  have e5 : v (5 : Fin 6) = 0 := by linarith
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

theorem lt_two_of_mem_spectrum_dynkinE6 {x : ℝ} (hx : x ∈ dynkinE6.spectrum) : x < 2 :=
  lt_of_le_of_ne (spectrum_le_of_mulVec_le marksDynkinE6_pos mulVec_le_dynkinE6 hx)
    (fun h ↦ two_notMem_spectrum_dynkinE6 (h ▸ hx))

theorem isSubcritical_dynkinE6 : IsSubcritical dynkinE6 :=
  fun _ hx ↦ lt_two_of_mem_spectrum_dynkinE6 hx

/-- The affine diagram `Ẽ₆`: three arms of length `2`. -/
def affineE6 : CGraph := ofEdges 7 [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)]

/-- The marks of the affine diagram `affineE6`. -/
def marksAffineE6 : Fin 7 → ℝ := ![3, 2, 1, 2, 1, 2, 1]

theorem marksAffineE6_pos (i : Fin 7) : 0 < marksAffineE6 i := by
  fin_cases i <;> norm_num [marksAffineE6]
theorem mulVec_affineE6 : affineE6.adjMat *ᵥ marksAffineE6 = (2 : ℝ) • marksAffineE6 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, affineE6, ofEdges, ofRel,
      marksAffineE6] <;> norm_num

theorem two_mem_spectrum_affineE6 : (2 : ℝ) ∈ affineE6.spectrum := by
  haveI : Nonempty affineE6.V := ⟨(0 : Fin 7)⟩
  exact mem_spectrum_of_mulVec_eq marksAffineE6_pos mulVec_affineE6

theorem le_two_of_mem_spectrum_affineE6 {x : ℝ} (hx : x ∈ affineE6.spectrum) : x ≤ 2 :=
  spectrum_le_of_mulVec_le marksAffineE6_pos
    (fun i ↦ by simpa using le_of_eq (congrFun mulVec_affineE6 i)) hx

theorem isSmith_affineE6 : IsSmith affineE6 :=
  ⟨two_mem_spectrum_affineE6, fun _ hx ↦ le_two_of_mem_spectrum_affineE6 hx⟩

/-- The Dynkin diagram `E₇`: arms of lengths `1, 3, 2`. -/
def dynkinE7 : CGraph := ofEdges 7 [(0, 1), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6)]

/-- The marks of the diagram `dynkinE7`. -/
def marksDynkinE7 : Fin 7 → ℝ := ![4, 2, 3, 2, 1, 3, 2]

theorem marksDynkinE7_pos (i : Fin 7) : 0 < marksDynkinE7 i := by
  fin_cases i <;> norm_num [marksDynkinE7]
theorem mulVec_le_dynkinE7 (i : Fin 7) :
    (dynkinE7.adjMat *ᵥ marksDynkinE7) i ≤ 2 * marksDynkinE7 i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE7, ofEdges, ofRel,
      marksDynkinE7] <;> norm_num

theorem two_notMem_spectrum_dynkinE7 : (2 : ℝ) ∉ dynkinE7.spectrum := by
  intro hx
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff _ _).1 hx
  have h0 := congrFun hv (0 : Fin 7)
  have h1 := congrFun hv (1 : Fin 7)
  have h2 := congrFun hv (2 : Fin 7)
  have h3 := congrFun hv (3 : Fin 7)
  have h4 := congrFun hv (4 : Fin 7)
  have h5 := congrFun hv (5 : Fin 7)
  have h6 := congrFun hv (6 : Fin 7)
  simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE7, ofEdges,
    ofRel] at h0 h1 h2 h3 h4 h5 h6
  refine hv0 (funext fun i ↦ ?_)
  have e0 : v (0 : Fin 7) = 0 := by linarith
  have e1 : v (1 : Fin 7) = 0 := by linarith
  have e2 : v (2 : Fin 7) = 0 := by linarith
  have e3 : v (3 : Fin 7) = 0 := by linarith
  have e4 : v (4 : Fin 7) = 0 := by linarith
  have e5 : v (5 : Fin 7) = 0 := by linarith
  have e6 : v (6 : Fin 7) = 0 := by linarith
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

theorem lt_two_of_mem_spectrum_dynkinE7 {x : ℝ} (hx : x ∈ dynkinE7.spectrum) : x < 2 :=
  lt_of_le_of_ne (spectrum_le_of_mulVec_le marksDynkinE7_pos mulVec_le_dynkinE7 hx)
    (fun h ↦ two_notMem_spectrum_dynkinE7 (h ▸ hx))

theorem isSubcritical_dynkinE7 : IsSubcritical dynkinE7 :=
  fun _ hx ↦ lt_two_of_mem_spectrum_dynkinE7 hx

/-- The affine diagram `Ẽ₇`: arms of lengths `1, 3, 3`. -/
def affineE7 : CGraph := ofEdges 8 [(0, 1), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7)]

/-- The marks of the affine diagram `affineE7`. -/
def marksAffineE7 : Fin 8 → ℝ := ![4, 2, 3, 2, 1, 3, 2, 1]

theorem marksAffineE7_pos (i : Fin 8) : 0 < marksAffineE7 i := by
  fin_cases i <;> norm_num [marksAffineE7]
theorem mulVec_affineE7 : affineE7.adjMat *ᵥ marksAffineE7 = (2 : ℝ) • marksAffineE7 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, affineE7, ofEdges, ofRel,
      marksAffineE7] <;> norm_num

theorem two_mem_spectrum_affineE7 : (2 : ℝ) ∈ affineE7.spectrum := by
  haveI : Nonempty affineE7.V := ⟨(0 : Fin 8)⟩
  exact mem_spectrum_of_mulVec_eq marksAffineE7_pos mulVec_affineE7

theorem le_two_of_mem_spectrum_affineE7 {x : ℝ} (hx : x ∈ affineE7.spectrum) : x ≤ 2 :=
  spectrum_le_of_mulVec_le marksAffineE7_pos
    (fun i ↦ by simpa using le_of_eq (congrFun mulVec_affineE7 i)) hx

theorem isSmith_affineE7 : IsSmith affineE7 :=
  ⟨two_mem_spectrum_affineE7, fun _ hx ↦ le_two_of_mem_spectrum_affineE7 hx⟩

/-- The Dynkin diagram `E₈`: arms of lengths `1, 2, 4`. -/
def dynkinE8 : CGraph := ofEdges 8 [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7)]

/-- The marks of the diagram `dynkinE8`. -/
def marksDynkinE8 : Fin 8 → ℝ := ![6, 3, 4, 2, 5, 4, 3, 2]

theorem marksDynkinE8_pos (i : Fin 8) : 0 < marksDynkinE8 i := by
  fin_cases i <;> norm_num [marksDynkinE8]
theorem mulVec_le_dynkinE8 (i : Fin 8) :
    (dynkinE8.adjMat *ᵥ marksDynkinE8) i ≤ 2 * marksDynkinE8 i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE8, ofEdges, ofRel,
      marksDynkinE8] <;> norm_num

theorem two_notMem_spectrum_dynkinE8 : (2 : ℝ) ∉ dynkinE8.spectrum := by
  intro hx
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff _ _).1 hx
  have h0 := congrFun hv (0 : Fin 8)
  have h1 := congrFun hv (1 : Fin 8)
  have h2 := congrFun hv (2 : Fin 8)
  have h3 := congrFun hv (3 : Fin 8)
  have h4 := congrFun hv (4 : Fin 8)
  have h5 := congrFun hv (5 : Fin 8)
  have h6 := congrFun hv (6 : Fin 8)
  have h7 := congrFun hv (7 : Fin 8)
  simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, dynkinE8, ofEdges,
    ofRel] at h0 h1 h2 h3 h4 h5 h6 h7
  refine hv0 (funext fun i ↦ ?_)
  have e0 : v (0 : Fin 8) = 0 := by linarith
  have e1 : v (1 : Fin 8) = 0 := by linarith
  have e2 : v (2 : Fin 8) = 0 := by linarith
  have e3 : v (3 : Fin 8) = 0 := by linarith
  have e4 : v (4 : Fin 8) = 0 := by linarith
  have e5 : v (5 : Fin 8) = 0 := by linarith
  have e6 : v (6 : Fin 8) = 0 := by linarith
  have e7 : v (7 : Fin 8) = 0 := by linarith
  fin_cases i <;> simp only [Pi.zero_apply] <;> assumption

theorem lt_two_of_mem_spectrum_dynkinE8 {x : ℝ} (hx : x ∈ dynkinE8.spectrum) : x < 2 :=
  lt_of_le_of_ne (spectrum_le_of_mulVec_le marksDynkinE8_pos mulVec_le_dynkinE8 hx)
    (fun h ↦ two_notMem_spectrum_dynkinE8 (h ▸ hx))

theorem isSubcritical_dynkinE8 : IsSubcritical dynkinE8 :=
  fun _ hx ↦ lt_two_of_mem_spectrum_dynkinE8 hx

/-- The affine diagram `Ẽ₈`: arms of lengths `1, 2, 5`. -/
def affineE8 : CGraph := ofEdges 9 [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- The marks of the affine diagram `affineE8`. -/
def marksAffineE8 : Fin 9 → ℝ := ![6, 3, 4, 2, 5, 4, 3, 2, 1]

theorem marksAffineE8_pos (i : Fin 9) : 0 < marksAffineE8 i := by
  fin_cases i <;> norm_num [marksAffineE8]
theorem mulVec_affineE8 : affineE8.adjMat *ᵥ marksAffineE8 = (2 : ℝ) • marksAffineE8 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjMat_apply, Fin.sum_univ_succ, affineE8, ofEdges, ofRel,
      marksAffineE8] <;> norm_num

theorem two_mem_spectrum_affineE8 : (2 : ℝ) ∈ affineE8.spectrum := by
  haveI : Nonempty affineE8.V := ⟨(0 : Fin 9)⟩
  exact mem_spectrum_of_mulVec_eq marksAffineE8_pos mulVec_affineE8

theorem le_two_of_mem_spectrum_affineE8 {x : ℝ} (hx : x ∈ affineE8.spectrum) : x ≤ 2 :=
  spectrum_le_of_mulVec_le marksAffineE8_pos
    (fun i ↦ by simpa using le_of_eq (congrFun mulVec_affineE8 i)) hx

theorem isSmith_affineE8 : IsSmith affineE8 :=
  ⟨two_mem_spectrum_affineE8, fun _ hx ↦ le_two_of_mem_spectrum_affineE8 hx⟩

/-! ### The parametric families `Dₙ` and `D̃ₙ`

The diagrams `D₄ ⊂ D₅ ⊂ ⋯` and `D̃₄ ⊂ D̃₅ ⊂ ⋯` are handled for every `n` at once.  Both are a
chain of vertices carrying the mark `2` with pendant vertices carrying the mark `1` at the ends:
two at each end for `D̃`, two at one end and one at the other for `D`.  The vertex type is
`Fin (m + 1) ⊕ Fin k`, the chain and the pendant vertices, which keeps the two kinds of sum
apart.  The four lemmas below evaluate a sum along the chain. -/

private theorem chain_split {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j : Fin (m + 1), (if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then u j else 0)
      = (∑ j : Fin (m + 1), if i.1 + 1 = j.1 then u j else 0)
        + ∑ j : Fin (m + 1), (if j.1 + 1 = i.1 then u j else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h1 : i.1 + 1 = j.1 <;> by_cases h2 : j.1 + 1 = i.1
  · omega
  all_goals simp [h1, h2]

private theorem chain_up {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : i.1 < m) :
    (∑ j : Fin (m + 1), if i.1 + 1 = j.1 then u j else 0) = u ⟨i.1 + 1, by omega⟩ := by
  rw [Finset.sum_eq_single (⟨i.1 + 1, by omega⟩ : Fin (m + 1))]
  · simp
  · intro b _ hb
    exact if_neg fun hh ↦ hb (Fin.ext hh.symm)
  · intro hh; exact absurd (Finset.mem_univ _) hh

private theorem chain_up_last {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : i.1 = m) :
    (∑ j : Fin (m + 1), if i.1 + 1 = j.1 then u j else 0) = 0 := by
  refine Finset.sum_eq_zero fun j _ ↦ if_neg ?_
  have := j.isLt
  omega

private theorem chain_down {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : 0 < i.1) :
    (∑ j : Fin (m + 1), if j.1 + 1 = i.1 then u j else 0) = u ⟨i.1 - 1, by omega⟩ := by
  have hlt := i.isLt
  rw [Finset.sum_eq_single (⟨i.1 - 1, by omega⟩ : Fin (m + 1))]
  · exact if_pos (by simp; omega)
  · intro b _ hb
    exact if_neg fun hh ↦ hb (Fin.ext (by simp; omega))
  · intro hh; exact absurd (Finset.mem_univ _) hh

private theorem chain_down_zero {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (h : i.1 = 0) :
    (∑ j : Fin (m + 1), if j.1 + 1 = i.1 then u j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ ↦ if_neg (by omega)

/-! #### The affine diagram `D̃ₘ₊₄` -/

/-- The affine Dynkin diagram `D̃ₘ₊₄`: a chain of `m + 1` vertices, with two pendant vertices
attached at each end.  `affineD 0` is the star `D̃₄`. -/
def affineD (m : ℕ) : CGraph :=
  ofRel (Fin (m + 1) ⊕ Fin 4) fun x y ↦
    match x, y with
    | Sum.inl i, Sum.inl j => i.1 + 1 == j.1
    | Sum.inl i, Sum.inr k => (i.1 == 0 && decide (k.1 ≤ 1)) || (i.1 == m && decide (2 ≤ k.1))
    | Sum.inr _, _ => false

theorem affineD_adj_inl_inl (m : ℕ) (i j : Fin (m + 1)) :
    (affineD m).Adj (Sum.inl i) (Sum.inl j) = true ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  simp only [affineD, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, Sum.inl.injEq, Fin.ext_iff]
  omega

theorem affineD_adj_inl_inr (m : ℕ) (i : Fin (m + 1)) (k : Fin 4) :
    (affineD m).Adj (Sum.inl i) (Sum.inr k) = true ↔
      ((i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ 2 ≤ k.1)) := by
  simp only [affineD, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Bool.true_and, Bool.or_false]

theorem affineD_adj_inr_inl (m : ℕ) (k : Fin 4) (i : Fin (m + 1)) :
    (affineD m).Adj (Sum.inr k) (Sum.inl i) = true ↔
      ((i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ 2 ≤ k.1)) := by
  rw [(affineD m).symm]; exact affineD_adj_inl_inr m i k

theorem affineD_adj_inr_inr (m : ℕ) (k l : Fin 4) :
    (affineD m).Adj (Sum.inr k) (Sum.inr l) = false := by
  simp [affineD, ofRel_adj]

/-- The action of the adjacency matrix of `D̃` at a chain vertex: the two chain neighbours, plus
the pendant vertices at whichever end of the chain the vertex sits. -/
theorem affineD_mulVec_inl (m : ℕ) (v : (affineD m).V → ℝ) (i : Fin (m + 1)) :
    ((affineD m).adjMat *ᵥ v) (Sum.inl i)
      = ((∑ j : Fin (m + 1), if i.1 + 1 = j.1 then v (Sum.inl j) else 0)
          + ∑ j : Fin (m + 1), (if j.1 + 1 = i.1 then v (Sum.inl j) else 0))
        + ((if i.1 = 0 then v (Sum.inr 0) + v (Sum.inr 1) else 0)
          + (if i.1 = m then v (Sum.inr 2) + v (Sum.inr 3) else 0)) := by
  have hchain : ∀ j : Fin (m + 1), (affineD m).adjMat (Sum.inl i) (Sum.inl j) * v (Sum.inl j)
      = if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
    · rw [if_pos ((affineD_adj_inl_inl m i j).2 h), if_pos h, one_mul]
    · rw [if_neg fun hh ↦ h ((affineD_adj_inl_inl m i j).1 hh), if_neg h, zero_mul]
  have hleaf : ∀ k : Fin 4, (affineD m).adjMat (Sum.inl i) (Sum.inr k) * v (Sum.inr k)
      = if (i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ 2 ≤ k.1) then v (Sum.inr k) else 0 := by
    intro k
    rw [adjMat_apply]
    by_cases h : (i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ 2 ≤ k.1)
    · rw [if_pos ((affineD_adj_inl_inr m i k).2 h), if_pos h, one_mul]
    · rw [if_neg fun hh ↦ h ((affineD_adj_inl_inr m i k).1 hh), if_neg h, zero_mul]
  have hsplit : ((affineD m).adjMat *ᵥ v) (Sum.inl i)
      = (∑ j : Fin (m + 1), (affineD m).adjMat (Sum.inl i) (Sum.inl j) * v (Sum.inl j))
        + ∑ k : Fin 4, (affineD m).adjMat (Sum.inl i) (Sum.inr k) * v (Sum.inr k) :=
    Fintype.sum_sum_type (f := fun x ↦ (affineD m).adjMat (Sum.inl i) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf]
  rw [chain_split]
  congr 1
  rw [Fin.sum_univ_four]
  by_cases h0 : i.1 = 0 <;> by_cases hm : i.1 = m <;> simp [h0, hm] <;>
    split_ifs <;> ring

theorem affineD_mulVec_inr_le (m : ℕ) (v : (affineD m).V → ℝ) (k : Fin 4) (hk : k.1 ≤ 1) :
    ((affineD m).adjMat *ᵥ v) (Sum.inr k) = v (Sum.inl ⟨0, Nat.succ_pos m⟩) := by
  have hchain : ∀ j : Fin (m + 1), (affineD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j)
      = if j = (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases hj : j.1 = 0
    · rw [if_pos ((affineD_adj_inr_inl m k j).2 (Or.inl ⟨hj, hk⟩)), if_pos (Fin.ext hj), one_mul]
    · rw [if_neg fun hh ↦ ?_, if_neg fun hh ↦ hj (Fin.ext_iff.1 hh), zero_mul]
      rcases (affineD_adj_inr_inl m k j).1 hh with h | h
      · exact hj h.1
      · omega
  have hleaf : ∀ l : Fin 4, (affineD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) = 0 := by
    intro l
    rw [adjMat_apply, if_neg (by rw [affineD_adj_inr_inr]; simp), zero_mul]
  have hsplit : ((affineD m).adjMat *ᵥ v) (Sum.inr k)
      = (∑ j : Fin (m + 1), (affineD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j))
        + ∑ l : Fin 4, (affineD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) :=
    Fintype.sum_sum_type (f := fun x ↦ (affineD m).adjMat (Sum.inr k) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

theorem affineD_mulVec_inr_ge (m : ℕ) (v : (affineD m).V → ℝ) (k : Fin 4) (hk : 2 ≤ k.1) :
    ((affineD m).adjMat *ᵥ v) (Sum.inr k) = v (Sum.inl ⟨m, Nat.lt_succ_self m⟩) := by
  have hchain : ∀ j : Fin (m + 1), (affineD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j)
      = if j = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases hj : j.1 = m
    · rw [if_pos ((affineD_adj_inr_inl m k j).2 (Or.inr ⟨hj, hk⟩)), if_pos (Fin.ext hj), one_mul]
    · rw [if_neg fun hh ↦ ?_, if_neg fun hh ↦ hj (Fin.ext_iff.1 hh), zero_mul]
      rcases (affineD_adj_inr_inl m k j).1 hh with h | h
      · omega
      · exact hj h.1
  have hleaf : ∀ l : Fin 4, (affineD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) = 0 := by
    intro l
    rw [adjMat_apply, if_neg (by rw [affineD_adj_inr_inr]; simp), zero_mul]
  have hsplit : ((affineD m).adjMat *ᵥ v) (Sum.inr k)
      = (∑ j : Fin (m + 1), (affineD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j))
        + ∑ l : Fin 4, (affineD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) :=
    Fintype.sum_sum_type (f := fun x ↦ (affineD m).adjMat (Sum.inr k) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

/-- The marks of `D̃ₘ₊₄`: `2` along the chain and `1` at the four pendant vertices. -/
def marksAffineD (m : ℕ) : (affineD m).V → ℝ := Sum.elim (fun _ ↦ 2) (fun _ ↦ 1)

theorem marksAffineD_pos (m : ℕ) (x : (affineD m).V) : 0 < marksAffineD m x := by
  rcases x with i | k <;> norm_num [marksAffineD]

theorem mulVec_affineD (m : ℕ) :
    (affineD m).adjMat *ᵥ marksAffineD m = (2 : ℝ) • marksAffineD m := by
  funext x
  rcases x with i | k
  · rw [affineD_mulVec_inl]
    have hi : i.1 ≤ m := Nat.lt_succ_iff.1 i.isLt
    rcases Nat.eq_or_lt_of_le hi with hm | hm
    · rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [chain_up_last _ _ hm, chain_down_zero _ _ h0, if_pos h0, if_pos hm]
        norm_num [marksAffineD]
      · rw [chain_up_last _ _ hm, chain_down _ _ h0, if_neg (by omega), if_pos hm]
        norm_num [marksAffineD]
    · rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [chain_up _ _ hm, chain_down_zero _ _ h0, if_pos h0, if_neg (by omega)]
        norm_num [marksAffineD]
      · rw [chain_up _ _ hm, chain_down _ _ h0, if_neg (by omega), if_neg (by omega)]
        norm_num [marksAffineD]
  · rcases Nat.lt_or_ge k.1 2 with hk | hk
    · rw [affineD_mulVec_inr_le _ _ _ (by omega)]
      norm_num [marksAffineD]
    · rw [affineD_mulVec_inr_ge _ _ _ hk]
      norm_num [marksAffineD]



theorem card_affineD (m : ℕ) : Fintype.card (affineD m).V = m + 5 := by
  show Fintype.card (Fin (m + 1) ⊕ Fin 4) = m + 5
  simp

theorem two_mem_spectrum_affineD (m : ℕ) : (2 : ℝ) ∈ (affineD m).spectrum := by
  haveI : Nonempty (affineD m).V := ⟨Sum.inl ⟨0, Nat.succ_pos m⟩⟩
  exact mem_spectrum_of_mulVec_eq (marksAffineD_pos m) (mulVec_affineD m)

theorem le_two_of_mem_spectrum_affineD (m : ℕ) {x : ℝ} (hx : x ∈ (affineD m).spectrum) : x ≤ 2 :=
  spectrum_le_of_mulVec_le (marksAffineD_pos m)
    (fun i ↦ by simpa using le_of_eq (congrFun (mulVec_affineD m) i)) hx

/-- **Every affine diagram `D̃ₙ` is a Smith graph.** -/
theorem isSmith_affineD (m : ℕ) : IsSmith (affineD m) :=
  ⟨two_mem_spectrum_affineD m, fun _ hx ↦ le_two_of_mem_spectrum_affineD m hx⟩



/-! #### The Dynkin diagram `Dₘ₊₄` -/

/-- The Dynkin diagram `Dₘ₊₄`: a chain of `m + 1` vertices with two pendant vertices at one end
and one at the other.  `dynkinD 0` is the claw `D₄`. -/
def dynkinD (m : ℕ) : CGraph :=
  ofRel (Fin (m + 1) ⊕ Fin 3) fun x y ↦
    match x, y with
    | Sum.inl i, Sum.inl j => i.1 + 1 == j.1
    | Sum.inl i, Sum.inr k => (i.1 == 0 && decide (k.1 ≤ 1)) || (i.1 == m && k.1 == 2)
    | Sum.inr _, _ => false

theorem dynkinD_adj_inl_inl (m : ℕ) (i j : Fin (m + 1)) :
    (dynkinD m).Adj (Sum.inl i) (Sum.inl j) = true ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  simp only [dynkinD, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, Sum.inl.injEq, Fin.ext_iff]
  omega

theorem dynkinD_adj_inl_inr (m : ℕ) (i : Fin (m + 1)) (k : Fin 3) :
    (dynkinD m).Adj (Sum.inl i) (Sum.inr k) = true ↔
      ((i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ k.1 = 2)) := by
  simp only [dynkinD, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Bool.true_and, Bool.or_false]

theorem dynkinD_adj_inr_inl (m : ℕ) (k : Fin 3) (i : Fin (m + 1)) :
    (dynkinD m).Adj (Sum.inr k) (Sum.inl i) = true ↔
      ((i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ k.1 = 2)) := by
  rw [(dynkinD m).symm]; exact dynkinD_adj_inl_inr m i k

theorem dynkinD_adj_inr_inr (m : ℕ) (k l : Fin 3) :
    (dynkinD m).Adj (Sum.inr k) (Sum.inr l) = false := by
  simp [dynkinD, ofRel_adj]

theorem dynkinD_mulVec_inl (m : ℕ) (v : (dynkinD m).V → ℝ) (i : Fin (m + 1)) :
    ((dynkinD m).adjMat *ᵥ v) (Sum.inl i)
      = ((∑ j : Fin (m + 1), if i.1 + 1 = j.1 then v (Sum.inl j) else 0)
          + ∑ j : Fin (m + 1), (if j.1 + 1 = i.1 then v (Sum.inl j) else 0))
        + ((if i.1 = 0 then v (Sum.inr 0) + v (Sum.inr 1) else 0)
          + (if i.1 = m then v (Sum.inr 2) else 0)) := by
  have hchain : ∀ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inl i) (Sum.inl j) * v (Sum.inl j)
      = if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
    · rw [if_pos ((dynkinD_adj_inl_inl m i j).2 h), if_pos h, one_mul]
    · rw [if_neg fun hh ↦ h ((dynkinD_adj_inl_inl m i j).1 hh), if_neg h, zero_mul]
  have hleaf : ∀ k : Fin 3, (dynkinD m).adjMat (Sum.inl i) (Sum.inr k) * v (Sum.inr k)
      = if (i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ k.1 = 2) then v (Sum.inr k) else 0 := by
    intro k
    rw [adjMat_apply]
    by_cases h : (i.1 = 0 ∧ k.1 ≤ 1) ∨ (i.1 = m ∧ k.1 = 2)
    · rw [if_pos ((dynkinD_adj_inl_inr m i k).2 h), if_pos h, one_mul]
    · rw [if_neg fun hh ↦ h ((dynkinD_adj_inl_inr m i k).1 hh), if_neg h, zero_mul]
  have hsplit : ((dynkinD m).adjMat *ᵥ v) (Sum.inl i)
      = (∑ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inl i) (Sum.inl j) * v (Sum.inl j))
        + ∑ k : Fin 3, (dynkinD m).adjMat (Sum.inl i) (Sum.inr k) * v (Sum.inr k) :=
    Fintype.sum_sum_type (f := fun x ↦ (dynkinD m).adjMat (Sum.inl i) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf]
  rw [chain_split]
  congr 1
  rw [Fin.sum_univ_three]
  by_cases h0 : i.1 = 0 <;> by_cases hm : i.1 = m <;> simp [h0, hm]
  all_goals split_ifs <;> ring

theorem dynkinD_mulVec_inr_le (m : ℕ) (v : (dynkinD m).V → ℝ) (k : Fin 3) (hk : k.1 ≤ 1) :
    ((dynkinD m).adjMat *ᵥ v) (Sum.inr k) = v (Sum.inl ⟨0, Nat.succ_pos m⟩) := by
  have hchain : ∀ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j)
      = if j = (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases hj : j.1 = 0
    · rw [if_pos ((dynkinD_adj_inr_inl m k j).2 (Or.inl ⟨hj, hk⟩)), if_pos (Fin.ext hj), one_mul]
    · rw [if_neg fun hh ↦ ?_, if_neg fun hh ↦ hj (Fin.ext_iff.1 hh), zero_mul]
      rcases (dynkinD_adj_inr_inl m k j).1 hh with h | h
      · exact hj h.1
      · omega
  have hleaf : ∀ l : Fin 3, (dynkinD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) = 0 := by
    intro l
    rw [adjMat_apply, if_neg (by rw [dynkinD_adj_inr_inr]; simp), zero_mul]
  have hsplit : ((dynkinD m).adjMat *ᵥ v) (Sum.inr k)
      = (∑ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j))
        + ∑ l : Fin 3, (dynkinD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) :=
    Fintype.sum_sum_type (f := fun x ↦ (dynkinD m).adjMat (Sum.inr k) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

theorem dynkinD_mulVec_inr_two (m : ℕ) (v : (dynkinD m).V → ℝ) (k : Fin 3) (hk : k.1 = 2) :
    ((dynkinD m).adjMat *ᵥ v) (Sum.inr k) = v (Sum.inl ⟨m, Nat.lt_succ_self m⟩) := by
  have hchain : ∀ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j)
      = if j = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) then v (Sum.inl j) else 0 := by
    intro j
    rw [adjMat_apply]
    by_cases hj : j.1 = m
    · rw [if_pos ((dynkinD_adj_inr_inl m k j).2 (Or.inr ⟨hj, hk⟩)), if_pos (Fin.ext hj), one_mul]
    · rw [if_neg fun hh ↦ ?_, if_neg fun hh ↦ hj (Fin.ext_iff.1 hh), zero_mul]
      rcases (dynkinD_adj_inr_inl m k j).1 hh with h | h
      · omega
      · exact hj h.1
  have hleaf : ∀ l : Fin 3, (dynkinD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) = 0 := by
    intro l
    rw [adjMat_apply, if_neg (by rw [dynkinD_adj_inr_inr]; simp), zero_mul]
  have hsplit : ((dynkinD m).adjMat *ᵥ v) (Sum.inr k)
      = (∑ j : Fin (m + 1), (dynkinD m).adjMat (Sum.inr k) (Sum.inl j) * v (Sum.inl j))
        + ∑ l : Fin 3, (dynkinD m).adjMat (Sum.inr k) (Sum.inr l) * v (Sum.inr l) :=
    Fintype.sum_sum_type (f := fun x ↦ (dynkinD m).adjMat (Sum.inr k) x * v x)
  rw [hsplit]
  simp only [hchain, hleaf, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

/-- The marks of `Dₘ₊₄`: `2` along the chain and `1` at the three pendant vertices. -/
def marksDynkinD (m : ℕ) : (dynkinD m).V → ℝ := Sum.elim (fun _ ↦ 2) (fun _ ↦ 1)

theorem marksDynkinD_pos (m : ℕ) (x : (dynkinD m).V) : 0 < marksDynkinD m x := by
  rcases x with i | k <;> norm_num [marksDynkinD]

theorem card_dynkinD (m : ℕ) : Fintype.card (dynkinD m).V = m + 4 := by
  show Fintype.card (Fin (m + 1) ⊕ Fin 3) = m + 4
  simp

theorem mulVec_le_dynkinD (m : ℕ) (x : (dynkinD m).V) :
    ((dynkinD m).adjMat *ᵥ marksDynkinD m) x ≤ 2 * marksDynkinD m x := by
  rcases x with i | k
  · rw [dynkinD_mulVec_inl]
    have hi : i.1 ≤ m := Nat.lt_succ_iff.1 i.isLt
    rcases Nat.eq_or_lt_of_le hi with hm | hm
    · rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [chain_up_last _ _ hm, chain_down_zero _ _ h0, if_pos h0, if_pos hm]
        norm_num [marksDynkinD]
      · rw [chain_up_last _ _ hm, chain_down _ _ h0, if_neg (by omega), if_pos hm]
        norm_num [marksDynkinD]
    · rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [chain_up _ _ hm, chain_down_zero _ _ h0, if_pos h0, if_neg (by omega)]
        norm_num [marksDynkinD]
      · rw [chain_up _ _ hm, chain_down _ _ h0, if_neg (by omega), if_neg (by omega)]
        norm_num [marksDynkinD]
  · rcases Nat.lt_or_ge k.1 2 with hk | hk
    · rw [dynkinD_mulVec_inr_le _ _ _ (by omega)]
      norm_num [marksDynkinD]
    · rw [dynkinD_mulVec_inr_two _ _ _ (by omega)]
      norm_num [marksDynkinD]



set_option maxHeartbeats 1000000 in
/-- **`2` is not an eigenvalue of `Dₙ`.**  An eigenvector for `2` is forced to be constant along
the chain by the recurrence `c(t-1) + c(t+1) = 2 c t` together with the boundary condition at the
forked end; the single pendant vertex at the other end then forces that constant to vanish. -/
theorem two_notMem_spectrum_dynkinD (m : ℕ) : (2 : ℝ) ∉ (dynkinD m).spectrum := by
  intro hx
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff _ _).1 hx
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℝ, ∀ j : Fin (m + 1), v (Sum.inl j) = C j.1 :=
    ⟨fun t ↦ v (Sum.inl ⟨min t m, Nat.lt_succ_of_le (min_le_right t m)⟩), fun j ↦ by
      simp only [min_eq_left (Nat.lt_succ_iff.1 j.isLt), Fin.eta]⟩
  -- the three pendant vertices
  have hp0 : C 0 = 2 * v (Sum.inr 0) := by
    have e := congrFun hv (Sum.inr (0 : Fin 3))
    rw [dynkinD_mulVec_inr_le m v 0 (by norm_num), hC] at e
    simpa using e
  have hp1 : C 0 = 2 * v (Sum.inr 1) := by
    have e := congrFun hv (Sum.inr (1 : Fin 3))
    rw [dynkinD_mulVec_inr_le m v 1 (by norm_num), hC] at e
    simpa using e
  have hp2 : C m = 2 * v (Sum.inr 2) := by
    have e := congrFun hv (Sum.inr (2 : Fin 3))
    rw [dynkinD_mulVec_inr_two m v 2 (by norm_num), hC] at e
    simpa using e
  -- the chain equations
  have hzero : 0 < m → C 1 + (v (Sum.inr 0) + v (Sum.inr 1)) = 2 * C 0 := by
    intro h
    have e := congrFun hv (Sum.inl (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)))
    rw [dynkinD_mulVec_inl, chain_up _ _ (by simpa using h), chain_down_zero _ _ (by simp),
      if_pos (by simp), if_neg (by simp; omega), Pi.smul_apply, smul_eq_mul, hC, hC] at e
    simpa using e
  have hlast : 0 < m → C (m - 1) + v (Sum.inr 2) = 2 * C m := by
    intro h
    have e := congrFun hv (Sum.inl (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)))
    rw [dynkinD_mulVec_inl, chain_up_last _ _ (by simp), chain_down _ _ (by simpa using h),
      if_neg (by simp; omega), if_pos (by simp), Pi.smul_apply, smul_eq_mul, hC, hC] at e
    simpa using e
  have hint : ∀ t : ℕ, t + 1 < m → C (t + 1 + 1) + C t = 2 * C (t + 1) := by
    intro t ht
    have e := congrFun hv (Sum.inl (⟨t + 1, by omega⟩ : Fin (m + 1)))
    rw [dynkinD_mulVec_inl, chain_up _ _ (by simpa using ht), chain_down _ _ (by simp),
      if_neg (by simp), if_neg (by simp; omega), Pi.smul_apply, smul_eq_mul, hC, hC, hC] at e
    simpa using e
  have hsingle : m = 0 → v (Sum.inr 0) + v (Sum.inr 1) + v (Sum.inr 2) = 2 * C 0 := by
    intro h
    have e := congrFun hv (Sum.inl (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)))
    rw [dynkinD_mulVec_inl, chain_up_last _ _ (by simp [h]), chain_down_zero _ _ (by simp),
      if_pos (by simp), if_pos (by simp [h]), Pi.smul_apply, smul_eq_mul, hC] at e
    simpa using e
  -- the chain is constant
  have key : ∀ t : ℕ, t < m → C t = C 0 ∧ C (t + 1) = C 0 := by
    intro t
    induction t with
    | zero =>
      intro h
      refine ⟨rfl, ?_⟩
      simp only [Nat.zero_add]
      have h1 := hzero h
      linarith
    | succ s ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2, ?_⟩
      have h3 := hint s (by omega)
      linarith
  have hall : ∀ t : ℕ, t ≤ m → C t = C 0 := by
    intro t ht
    rcases Nat.lt_or_ge t m with h | h
    · exact (key t h).1
    · have htm : t = m := le_antisymm ht h
      subst htm
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0]
      · have h1 := (key (t - 1) (by omega)).2
        rwa [Nat.sub_add_cancel h0] at h1
  have hC0 : C 0 = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h := hsingle rfl
      linarith
    · have h := hlast hm
      have h1 := hall m le_rfl
      have h2 := hall (m - 1) (by omega)
      linarith
  refine hv0 (funext fun x ↦ ?_)
  have e0 : v (Sum.inr (0 : Fin 3)) = 0 := by linarith
  have e1 : v (Sum.inr (1 : Fin 3)) = 0 := by linarith
  have e2 : v (Sum.inr (2 : Fin 3)) = 0 := by
    have h1 := hall m le_rfl
    linarith
  rcases x with j | k
  · show v (Sum.inl j) = 0
    rw [hC, hall j.1 (Nat.lt_succ_iff.1 j.isLt), hC0]
  · show v (Sum.inr k) = 0
    fin_cases k
    · exact e0
    · exact e1
    · exact e2



theorem lt_two_of_mem_spectrum_dynkinD (m : ℕ) {x : ℝ} (hx : x ∈ (dynkinD m).spectrum) : x < 2 :=
  lt_of_le_of_ne (spectrum_le_of_mulVec_le (marksDynkinD_pos m) (mulVec_le_dynkinD m) hx)
    (fun h ↦ two_notMem_spectrum_dynkinD m (h ▸ hx))

/-- **Every Dynkin diagram `Dₙ` is subcritical.** -/
theorem isSubcritical_dynkinD (m : ℕ) : IsSubcritical (dynkinD m) :=
  fun _ hx ↦ lt_two_of_mem_spectrum_dynkinD m hx

/-- `D₄` in the parametric family is the claw. -/
def dynkinDZeroIso : dynkinD 0 ≃cg dynkinD4 :=
  isoOfAdj (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (by decide)

/-- `D̃₄` in the parametric family is the star with four edges. -/
def affineDZeroIso : affineD 0 ≃cg affineD4 :=
  isoOfAdj (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5) (by decide)

/-! ### Line graphs -/

/-- The incidence matrix: rows indexed by vertices, columns by edges (the vertices of the line
graph), with a `1` exactly when the vertex lies on the edge. -/
def incMat (G : CGraph) [DecidableEq G.V] : Matrix G.V (lineGraph G).V ℝ :=
  Matrix.of fun v e ↦ if v ∈ (e.1 : Sym2 G.V) then 1 else 0

theorem incMat_apply (G : CGraph) [DecidableEq G.V] (v : G.V) (e : (lineGraph G).V) :
    G.incMat v e = if v ∈ (e.1 : Sym2 G.V) then 1 else 0 := rfl

private theorem card_filter_mem {G : CGraph} [DecidableEq G.V] (z : Sym2 G.V) :
    z ∈ G.toSimple.edgeSet → (Finset.univ.filter fun v : G.V ↦ v ∈ z).card = 2 := by
  induction z using Sym2.ind with
  | _ a b =>
    intro hz
    have hab : a ≠ b := G.toSimple.ne_of_adj ((SimpleGraph.mem_edgeSet _).1 hz)
    rw [← Finset.card_pair hab]
    congr 1
    ext v
    simp [Sym2.mem_iff]

private theorem card_filter_mem_inter {G : CGraph} [DecidableEq G.V] {z w : Sym2 G.V}
    (h : z ≠ w) :
    ((Finset.univ.filter fun v : G.V ↦ v ∈ z ∧ v ∈ w).card : ℝ)
      = if ∃ v, v ∈ z ∧ v ∈ w then 1 else 0 := by
  have hle : (Finset.univ.filter fun v : G.V ↦ v ∈ z ∧ v ∈ w).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    exact h (((Sym2.mem_and_mem_iff hab).1 ⟨ha.2.1, hb.2.1⟩).trans
      ((Sym2.mem_and_mem_iff hab).1 ⟨ha.2.2, hb.2.2⟩).symm)
  split_ifs with hex
  · obtain ⟨v, hv⟩ := hex
    have hne : (Finset.univ.filter fun v : G.V ↦ v ∈ z ∧ v ∈ w).Nonempty :=
      ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩⟩
    have hpos := Finset.card_pos.2 hne
    have hone : (Finset.univ.filter fun v : G.V ↦ v ∈ z ∧ v ∈ w).card = 1 := by omega
    rw [hone, Nat.cast_one]
  · have hempty : (Finset.univ.filter fun v : G.V ↦ v ∈ z ∧ v ∈ w) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun {v} _ hv ↦ hex ⟨v, hv⟩
    rw [hempty, Finset.card_empty, Nat.cast_zero]

/-- **The incidence matrix factors the line graph.**  `Bᵀ B = A(L G) + 2 I`: two distinct edges
contribute a `1` when they meet and an edge meets itself in its two endpoints. -/
theorem transpose_mul_incMat (G : CGraph) [DecidableEq G.V] :
    G.incMatᵀ * G.incMat
      = (lineGraph G).adjMat + (2 : ℝ) • (1 : Matrix (lineGraph G).V (lineGraph G).V ℝ) := by
  ext e f
  have hentry : ∀ v : G.V, G.incMatᵀ e v * G.incMat v f
      = if v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V) then (1 : ℝ) else 0 := by
    intro v
    rw [Matrix.transpose_apply, incMat_apply, incMat_apply]
    by_cases h1 : v ∈ (e.1 : Sym2 G.V) <;> by_cases h2 : v ∈ (f.1 : Sym2 G.V) <;> simp [h1, h2]
  have hsum : (G.incMatᵀ * G.incMat) e f
      = ((Finset.univ.filter
          fun v : G.V ↦ v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V)).card : ℝ) := by
    simp only [Matrix.mul_apply, hentry, Finset.sum_boole]
  rw [hsum, Matrix.add_apply]
  by_cases hef : e = f
  · subst hef
    rw [adjMat_apply, if_neg (by simp)]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, zero_add]
    rw [show (Finset.univ.filter fun v : G.V ↦ v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V))
        = Finset.univ.filter fun v : G.V ↦ v ∈ (e.1 : Sym2 G.V) from
      Finset.filter_congr fun v _ ↦ by simp, card_filter_mem e.1 e.2]
    norm_num
  · rw [Matrix.smul_apply, Matrix.one_apply_ne hef, smul_zero, add_zero, adjMat_apply,
      card_filter_mem_inter (fun h ↦ hef (Subtype.ext h))]
    by_cases hmeet : ∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V)
    · rw [if_pos hmeet, if_pos]
      simpa [lineGraph_adj, hef] using hmeet
    · rw [if_neg hmeet, if_neg]
      simpa [lineGraph_adj, hef] using hmeet

/-- **No eigenvalue of a line graph is below `-2`.**  This is the factorisation
`A(L G) + 2 I = Bᵀ B` together with `⟪v, Bᵀ B v⟫ = ‖B v‖² ≥ 0`; it is the spectral half of the
reason the ADE diagrams classify the graphs with least eigenvalue `-2`. -/
theorem neg_two_le_of_mem_spectrum_lineGraph (G : CGraph) [DecidableEq G.V] {x : ℝ}
    (hx : x ∈ (lineGraph G).spectrum) : -2 ≤ x := by
  obtain ⟨v, hv0, hv⟩ := ((lineGraph G).mem_spectrum_iff x).1 hx
  have hBB : v ⬝ᵥ ((G.incMatᵀ * G.incMat) *ᵥ v) = (G.incMat *ᵥ v) ⬝ᵥ (G.incMat *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]
  have hnn : (0 : ℝ) ≤ (G.incMat *ᵥ v) ⬝ᵥ (G.incMat *ᵥ v) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hkey : v ⬝ᵥ ((G.incMatᵀ * G.incMat) *ᵥ v) = (x + 2) * (v ⬝ᵥ v) := by
    rw [transpose_mul_incMat, Matrix.add_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
      (Ne.symm fun h ↦ hv0 (dotProduct_self_eq_zero.1 h))
  have hfin : 0 ≤ (x + 2) * (v ⬝ᵥ v) := by rw [← hkey, hBB]; exact hnn
  nlinarith [hpos, hfin]

/-- **`-2` really is an eigenvalue** as soon as `G` has more edges than vertices: the incidence
matrix then has a kernel, and a vector killed by `B` is an eigenvector of `Bᵀ B - 2 I`. -/
theorem neg_two_mem_spectrum_lineGraph (G : CGraph) [DecidableEq G.V]
    (h : Fintype.card G.V < G.E) : (-2 : ℝ) ∈ (lineGraph G).spectrum := by
  have hinj : ¬ Function.Injective (Matrix.mulVecLin G.incMat) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective (R := ℝ) hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      card_lineGraph] at hle
    omega
  obtain ⟨v, hmem, hne⟩ := Submodule.ne_bot_iff _ |>.1
    fun hbot ↦ hinj (LinearMap.ker_eq_bot.1 hbot)
  have hv : G.incMat *ᵥ v = 0 := hmem
  refine ((lineGraph G).mem_spectrum_iff _).2 ⟨v, hne, ?_⟩
  rw [eq_sub_of_add_eq (transpose_mul_incMat G).symm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    hv, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec, zero_sub]
  module

private theorem lt_choose_two {n : ℕ} (hn : 4 ≤ n) : n < n.choose 2 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h2 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

/-- The line graph of `Kₙ` — the triangular graph `T(n)` — has `-2` in its spectrum for `n ≥ 4`. -/
theorem neg_two_mem_spectrum_lineGraph_complete {n : ℕ} (hn : 4 ≤ n) :
    (-2 : ℝ) ∈ (lineGraph (complete n)).spectrum := by
  refine neg_two_mem_spectrum_lineGraph _ ?_
  rw [E_complete]
  simpa using lt_choose_two hn

/-- The line-graph bound, stated for the smallest eigenvalue. -/
theorem neg_two_le_lambdaMin_lineGraph (G : CGraph) [DecidableEq G.V]
    [Nonempty (lineGraph G).V] : -2 ≤ (lineGraph G).lambdaMin :=
  (le_lambdaMin_iff _).2 fun _ hx ↦ neg_two_le_of_mem_spectrum_lineGraph G hx

/-- The edges through a fixed vertex, seen as vertices of the line graph, are its incidence set. -/
theorem card_filter_mem_incMat {G : CGraph} [DecidableEq G.V] (u : G.V) :
    (Finset.univ.filter fun e : (lineGraph G).V ↦ u ∈ (e.1 : Sym2 G.V)).card
      = G.toSimple.degree u := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  refine Finset.card_bij (fun e _ ↦ (e.1 : Sym2 G.V)) (fun e he ↦ ?_) (fun e _ f _ hef ↦ ?_)
    (fun z hz ↦ ?_)
  · simp only [Finset.mem_filter] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨e.2, he.2⟩
  · exact Subtype.ext hef
  · rw [SimpleGraph.mem_incidenceFinset] at hz
    exact ⟨⟨z, hz.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz.2⟩, rfl⟩

/-- **The incidence matrix factors the graph itself.**  `B Bᵀ = A + k I` for a `k`-regular graph:
two distinct vertices lie on a common edge exactly when they are adjacent, and every vertex lies
on `k` edges. -/
theorem incMat_mul_transpose_of_isRegularWith {G : CGraph} [DecidableEq G.V] {k : ℕ}
    (h : G.IsRegularWith k) :
    G.incMat * G.incMatᵀ = G.adjMat + (k : ℝ) • (1 : Matrix G.V G.V ℝ) := by
  ext u v
  have hentry : ∀ e : (lineGraph G).V, G.incMat u e * G.incMatᵀ e v
      = if u ∈ (e.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V) then (1 : ℝ) else 0 := by
    intro e
    rw [Matrix.transpose_apply, incMat_apply, incMat_apply]
    by_cases h1 : u ∈ (e.1 : Sym2 G.V) <;> by_cases h2 : v ∈ (e.1 : Sym2 G.V) <;> simp [h1, h2]
  have hsum : (G.incMat * G.incMatᵀ) u v
      = ((Finset.univ.filter fun e : (lineGraph G).V ↦
          u ∈ (e.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V)).card : ℝ) := by
    simp only [Matrix.mul_apply, hentry, Finset.sum_boole]
  rw [hsum, Matrix.add_apply]
  by_cases huv : u = v
  · subst huv
    rw [adjMat_apply, if_neg (by simp [G.loopless u]), zero_add]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, and_self]
    rw [card_filter_mem_incMat u, h u]
  · rw [Matrix.smul_apply, Matrix.one_apply_ne huv, smul_zero, add_zero, adjMat_apply]
    by_cases hadj : G.Adj u v
    · have hmem : s(u, v) ∈ G.toSimple.edgeSet := hadj
      have hfil : (Finset.univ.filter fun e : (lineGraph G).V ↦
          u ∈ (e.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V)) = {⟨s(u, v), hmem⟩} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun he ↦ Subtype.ext ((Sym2.mem_and_mem_iff huv).1 he),
          fun he ↦ by rw [he]; simp⟩
      rw [hfil, Finset.card_singleton, if_pos hadj, Nat.cast_one]
    · have hfil : (Finset.univ.filter fun e : (lineGraph G).V ↦
          u ∈ (e.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun {e} _ he ↦ hadj ?_
        have hz := (Sym2.mem_and_mem_iff huv).1 he
        have h2 := e.2
        rw [hz] at h2
        exact h2
      rw [hfil, Finset.card_empty, if_neg hadj, Nat.cast_zero]

/-- **The spectrum of the line graph of a `k`-regular graph.**  Each eigenvalue `λ` of `G`
contributes `λ + k - 2` to `L(G)`, and the remaining `|E| - |V|` eigenvalues are all `-2`.  The
proof is Sylvester's determinant identity applied to `B Bᵀ = A + k I` and `Bᵀ B = A(L G) + 2 I`. -/
theorem spectrum_lineGraph_of_isRegularWith {G : CGraph} [DecidableEq G.V] {k : ℕ}
    (h : G.IsRegularWith k) (hle : Fintype.card G.V ≤ G.E) :
    (lineGraph G).spectrum
      = Multiset.replicate (G.E - Fintype.card G.V) (-2)
        + G.spectrum.map (fun x ↦ x + ((k : ℝ) - 2)) := by
  have hcard : Fintype.card G.V ≤ Fintype.card (lineGraph G).V := by
    rwa [card_lineGraph]
  have hsyl := Matrix.charpoly_mul_comm_of_le G.incMatᵀ G.incMat hcard
  rw [transpose_mul_incMat, incMat_mul_transpose_of_isRegularWith h,
    charpoly_adjMat_add_smul_one (lineGraph G) 2, charpoly_adjMat_add_smul_one G (k : ℝ)] at hsyl
  have hroots := congrArg Polynomial.roots hsyl
  rw [roots_prod_X_sub_C', Polynomial.roots_mul (by
      refine mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) ?_
      exact Finset.prod_ne_zero_iff.2 fun i _ ↦ Polynomial.X_sub_C_ne_zero _),
    Polynomial.roots_X_pow, roots_prod_X_sub_C'] at hroots
  have hL : (lineGraph G).spectrum.map (fun x ↦ x + 2)
      = Multiset.replicate (Fintype.card (lineGraph G).V - Fintype.card G.V) (0 : ℝ)
        + G.spectrum.map (fun x ↦ x + (k : ℝ)) := by
    rw [spectrum_eq_map, spectrum_eq_map, Multiset.map_map, Multiset.map_map]
    simpa [Function.comp_def, Multiset.nsmul_singleton] using hroots
  have := congrArg (Multiset.map (fun x : ℝ ↦ x - 2)) hL
  rw [Multiset.map_map, Multiset.map_add, Multiset.map_replicate, Multiset.map_map,
    card_lineGraph] at this
  simpa [Function.comp_def, add_sub_assoc] using this
/-- **The line graph of a cycle is cospectral with it** (indeed `L(Cₙ) ≅ Cₙ`): there are as many
edges as vertices, so no `-2` is left over, and the shift `k - 2` is zero. -/
theorem spectrum_lineGraph_cycle (n : ℕ) :
    (lineGraph (cycle (n + 3))).spectrum = (cycle (n + 3)).spectrum := by
  rw [spectrum_lineGraph_of_isRegularWith (IsoGraph.isRegularWith_cycle n)
    (by rw [E_cycle, card_cycle])]
  simp

/-- **The spectrum of the line graph of the Petersen graph**, on its `15` edges: `4` once, `2`
five times, `-1` four times and `-2` five times. -/
theorem spectrum_lineGraph_petersen :
    (lineGraph SRG.petersen).spectrum
      = Multiset.replicate 5 (-2 : ℝ)
        + (4 ::ₘ (Multiset.replicate 5 2 + Multiset.replicate 4 (-1))) := by
  have hreg : SRG.petersen.IsRegularWith 3 := SRG.petersen_srg.regular
  have hcard : Fintype.card SRG.petersen.V = 10 := SRG.petersen_srg.card
  have hE : SRG.petersen.E = 15 := by
    have hsum : ∑ i : SRG.petersen.V, SRG.petersen.toSimple.degree i = 30 := by
      rw [Finset.sum_congr rfl fun i _ ↦ hreg i, Finset.sum_const, Finset.card_univ, hcard]
      rfl
    have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges SRG.petersen.toSimple
    rw [hsum] at h2
    rw [show SRG.petersen.E = SRG.petersen.toSimple.edgeFinset.card from rfl]
    omega
  rw [spectrum_lineGraph_of_isRegularWith hreg (by rw [hE, hcard]; norm_num), hE, hcard,
    spectrum_petersen]
  norm_num [Multiset.map_add, Multiset.map_replicate]

/-- **A matching bound out of the ratio bound**: an independent set in the triangular graph
`T(n) = L(Kₙ)` is a matching of `Kₙ`, so it has at most `n / 2` edges.  Spectrally that is
`k = 2 (n - 2)` against `λ_min = -2`. -/
theorem two_mul_indepNum_triangular_le (m : ℕ) :
    2 * (triangular (m + 4)).indepNum ≤ m + 4 := by
  have hsrg := isSRGWith_triangular (m + 4) (by omega)
  rw [show 2 * (m + 4 - 2) = 2 * m + 4 from by omega,
    show m + 4 - 2 = m + 2 from by omega] at hsrg
  haveI : Nonempty (triangular (m + 4)).V :=
    Fintype.card_pos_iff.1 (by rw [hsrg.card]; exact Nat.choose_pos (by omega))
  have hpos : 0 < (m + 4).choose 2 - (m + 4) := by
    have := lt_choose_two (n := m + 4) (by omega)
    omega
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlm : (triangular (m + 4)).lambdaMin = -2 := by
    refine le_antisymm (lambdaMin_le ?_) ((le_lambdaMin_iff _).2 ?_)
    · rw [spectrum_triangular]
      simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_replicate]
      exact Or.inr (Or.inr ⟨by omega, trivial⟩)
    · intro x hx
      rw [spectrum_triangular] at hx
      simp only [Multiset.mem_cons, Multiset.mem_add, Multiset.mem_replicate] at hx
      rcases hx with rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · linarith
      · linarith
      · exact le_rfl
  have h := indepNum_mul_sub_lambdaMin_le hsrg.regular
  rw [hlm, hsrg.card, Nat.cast_choose_two] at h
  push_cast at h
  have h2 : (2 * ((triangular (m + 4)).indepNum : ℝ)) * ((m : ℝ) + 3)
      ≤ ((m : ℝ) + 4) * ((m : ℝ) + 3) := by nlinarith [h]
  have h3 : 2 * ((triangular (m + 4)).indepNum : ℝ) ≤ (m : ℝ) + 4 :=
    le_of_mul_le_mul_right h2 (by linarith)
  exact_mod_cast h3

/-! ## The spectrum of a complement

For a connected `k`-regular graph the whole spectrum of the complement is determined: the
all-ones vector spans the `k`-eigenspace, and every other eigenvector is orthogonal to it, so
`J - I - A` acts on it as `-1 - x`. -/

/-- **On a connected regular graph the degree has a one-dimensional eigenspace**: an eigenvector
for the degree is constant.  At a vertex where the eigenvector is largest, the `k` neighbours
average to that same value, so they all attain it too, and connectivity spreads the equality. -/
theorem eq_of_mulVec_eq_of_isRegularWith {G : CGraph} (hconn : G.IsConnected) {k : ℕ}
    (hreg : G.IsRegularWith k) {v : G.V → ℝ} (hv : G.adjMat *ᵥ v = (k : ℝ) • v) (i j : G.V) :
    v i = v j := by
  classical
  haveI : Nonempty G.V := hconn.nonempty
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset G.V) v
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  have hsum : ∀ x : G.V, ∑ y ∈ G.toSimple.neighborFinset x, v y = k * v x := by
    intro x
    have h1 := congrFun hv x
    rw [show (G.adjMat *ᵥ v) x = ∑ y ∈ G.toSimple.neighborFinset x, v y from by
      simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]] at h1
    simpa using h1
  have step : ∀ x y : G.V, G.toSimple.Adj x y → v x = v p → v y = v p := by
    intro x y hxy hx
    by_contra hne
    have hlt : v y < v p := lt_of_le_of_ne (hp y (Finset.mem_univ y)) hne
    have hcard : (G.toSimple.neighborFinset x).card = k := hreg x
    have h1 : ∑ z ∈ G.toSimple.neighborFinset x, v z
        < ∑ _z ∈ G.toSimple.neighborFinset x, v p :=
      Finset.sum_lt_sum (fun z _ ↦ hp z (Finset.mem_univ z))
        ⟨y, (SimpleGraph.mem_neighborFinset _ _ _).2 hxy, hlt⟩
    rw [hsum x, hx, Finset.sum_const, hcard, nsmul_eq_mul] at h1
    exact lt_irrefl _ h1
  have walkeq : ∀ (x y : G.V) (w : G.toSimple.Walk x y), v x = v p → v y = v p := by
    intro x y w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun hx ↦ ih (step _ _ h hx)
  have hall : ∀ x : G.V, v x = v p := fun x ↦
    (hconn.preconnected p x).elim fun w ↦ walkeq p x w rfl
  rw [hall i, hall j]

/-- **The spectrum of the complement of a connected regular graph.**  The degree `k` is replaced
by `n - 1 - k` and every other eigenvalue `x` by `-1 - x`. -/
theorem spectrum_compl_of_isRegularWith {G : CGraph} [inst : DecidableEq G.V]
    (hconn : G.IsConnected) {k : ℕ} (hreg : G.IsRegularWith k) :
    (compl G).spectrum = ((Fintype.card G.V : ℝ) - 1 - k)
      ::ₘ (G.spectrum.erase (k : ℝ)).map (fun x ↦ -1 - x) := by
  obtain rfl : inst = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  haveI : Nonempty G.V := hconn.nonempty
  have hnpos : (0 : ℝ) < Fintype.card G.V := by exact_mod_cast Fintype.card_pos
  obtain ⟨U, hUU, hUU', hdiag⟩ := exists_orthogonal_diagonal G
  have hAU : G.adjMat * U = U * Matrix.diagonal G.eigenvalues := by
    calc G.adjMat * U = (U * Uᵀ) * (G.adjMat * U) := by rw [hUU', one_mul]
      _ = U * (Uᵀ * G.adjMat * U) := by simp only [mul_assoc]
      _ = U * Matrix.diagonal G.eigenvalues := by rw [hdiag]
  -- the columns of `U` are the eigenvectors
  have hcol : ∀ i, G.adjMat *ᵥ (Uᵀ i) = G.eigenvalues i • (Uᵀ i) := by
    intro i
    funext x
    have h1 : (G.adjMat * U) x i = U x i * G.eigenvalues i := by
      rw [hAU, Matrix.mul_diagonal]
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h1
  have horth : ∀ i j, (Uᵀ i) ⬝ᵥ (Uᵀ j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : (Uᵀ * U) i j = (1 : Matrix G.V G.V ℝ) i j := by rw [hUU]
    rw [Matrix.one_apply] at h1
    simpa [Matrix.mul_apply, dotProduct] using h1
  -- an eigenvector for the degree is constant
  have hconstv : ∀ i, G.eigenvalues i = k → ∀ x y, U x i = U y i := by
    intro i hi x y
    exact eq_of_mulVec_eq_of_isRegularWith hconn hreg (by rw [hcol i, hi]) x y
  set w : G.V → ℝ := fun i ↦ ∑ x, U x i with hw
  have hone : G.adjMat *ᵥ (fun _ ↦ (1 : ℝ)) = (k : ℝ) • (fun _ ↦ (1 : ℝ)) :=
    (hasEigenvector_one_of_isRegularWith hreg).2
  have hwvec : Uᵀ *ᵥ (fun _ ↦ (1 : ℝ)) = w := by
    funext i
    simp [Matrix.mulVec, dotProduct, hw]
  -- `w` is supported on the eigenvalue `k`
  have hzero : ∀ i, G.eigenvalues i ≠ k → w i = 0 := by
    intro i hi
    have h1 : Matrix.diagonal G.eigenvalues *ᵥ w = (k : ℝ) • w := by
      rw [← hwvec, ← hdiag, Matrix.mulVec_mulVec, mul_assoc, mul_assoc, hUU', mul_one,
        ← Matrix.mulVec_mulVec, hone, Matrix.mulVec_smul, hwvec]
    have h2 := congrFun h1 i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h2
    rcases mul_eq_zero.1 (by linarith [h2] : (G.eigenvalues i - k) * w i = 0) with hc | hc
    · exact absurd (sub_eq_zero.1 hc) hi
    · exact hc
  -- some coordinate of `w` is nonzero
  have hwne : w ≠ 0 := by
    intro h0
    have h1 : U *ᵥ w = (fun _ ↦ (1 : ℝ)) := by
      rw [← hwvec, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 (Classical.arbitrary G.V)
    norm_num at h2
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hwne
  have hi₀0 : w i₀ ≠ 0 := by simpa using hi₀
  have hlam : G.eigenvalues i₀ = k := by
    by_contra hcon
    exact hi₀0 (hzero i₀ hcon)
  -- the constant value `c` of the column `i₀`
  obtain ⟨c, hc⟩ : ∃ c, ∀ x, U x i₀ = c :=
    ⟨U (Classical.arbitrary G.V) i₀, fun x ↦ hconstv i₀ hlam x _⟩
  have hwc : w i₀ = c * Fintype.card G.V := by
    rw [hw]
    simp [hc, Finset.card_univ, mul_comm]
  have hcsq : c ^ 2 * Fintype.card G.V = 1 := by
    have h1 := horth i₀ i₀
    rw [if_pos rfl] at h1
    simp only [dotProduct, Matrix.transpose_apply, hc, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    rw [← h1]
    ring
  have hwsq : w i₀ ^ 2 = Fintype.card G.V := by
    rw [hwc, show (c * Fintype.card G.V) ^ 2
      = (c ^ 2 * Fintype.card G.V) * Fintype.card G.V from by ring, hcsq, one_mul]
  -- every other coordinate of `w` vanishes
  have hwvanish : ∀ i, i ≠ i₀ → w i = 0 := by
    intro i hne
    by_cases hi : G.eigenvalues i = k
    · obtain ⟨e, he⟩ : ∃ e, ∀ x, U x i = e :=
        ⟨U (Classical.arbitrary G.V) i, fun x ↦ hconstv i hi x _⟩
      have h1 := horth i i₀
      rw [if_neg hne] at h1
      simp only [dotProduct, Matrix.transpose_apply, he, hc, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at h1
      have hcne : c ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hwc
        exact hi₀0 hwc
      have he0 : e = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h (ne_of_gt hnpos)
        · rcases mul_eq_zero.1 h with h' | h'
          · exact h'
          · exact absurd h' hcne
      rw [hw]
      simp [he, he0]
    · exact hzero i hi
  -- conjugating the complement
  set d : G.V → ℝ := fun i ↦ (if i = i₀ then (Fintype.card G.V : ℝ) else 0) - 1
    - G.eigenvalues i with hdd
  have hJ : Uᵀ * (Matrix.vecMulVec (1 : G.V → ℝ) 1) * U = Matrix.vecMulVec w w := by
    ext i j
    have hrow : ∀ y : G.V, (Uᵀ * Matrix.vecMulVec (1 : G.V → ℝ) 1) i y = w i := fun y ↦ by
      simp [Matrix.mul_apply, hw]
    rw [Matrix.mul_apply]
    simp only [hrow, ← Finset.mul_sum, Matrix.vecMulVec_apply]
    simp [hw]
  have hvv : Matrix.vecMulVec w w
      = Matrix.diagonal (fun i ↦ if i = i₀ then (Fintype.card G.V : ℝ) else 0) := by
    ext i j
    rcases eq_or_ne i i₀ with hi | hi
    · rcases eq_or_ne j i₀ with hj | hj
      · subst hi
        subst hj
        simp [Matrix.vecMulVec_apply, Matrix.diagonal, ← sq, hwsq]
      · subst hi
        simp [Matrix.vecMulVec_apply, Matrix.diagonal, Ne.symm hj, hwvanish j hj]
    · simp [Matrix.vecMulVec_apply, Matrix.diagonal, hi, hwvanish i hi]
  have hdsplit : Matrix.diagonal d
      = Matrix.diagonal (fun i ↦ if i = i₀ then (Fintype.card G.V : ℝ) else 0) - 1
        - Matrix.diagonal G.eigenvalues := by
    rw [hdd, ← Matrix.diagonal_one, ← Matrix.diagonal_sub, ← Matrix.diagonal_sub]
  have hfinal : Uᵀ * (Matrix.vecMulVec (1 : G.V → ℝ) 1 - 1 - G.adjMat) * U
      = Matrix.diagonal d := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, hJ, hvv, hdiag, mul_one,
      hUU, hdsplit]
  have hcon2 : (Matrix.vecMulVec (1 : G.V → ℝ) 1 - 1 - G.adjMat) * U = U * Matrix.diagonal d := by
    calc (Matrix.vecMulVec (1 : G.V → ℝ) 1 - 1 - G.adjMat) * U
        = (U * Uᵀ) * ((Matrix.vecMulVec (1 : G.V → ℝ) 1 - 1 - G.adjMat) * U) := by
          rw [hUU', one_mul]
      _ = U * (Uᵀ * (Matrix.vecMulVec (1 : G.V → ℝ) 1 - 1 - G.adjMat) * U) := by
          simp only [mul_assoc]
      _ = U * Matrix.diagonal d := by rw [hfinal]
  have hspec : (compl G).spectrum = Finset.univ.val.map d :=
    spectrum_eq_of_conj (G := compl G) (P := U) (Q := Uᵀ) (d := d) hUU' hUU
      (by rw [adjMat_compl]; exact hcon2)
  -- unpacking the two multisets
  have hmem : i₀ ∈ (Finset.univ : Finset G.V).val := Finset.mem_univ i₀
  have hsplit : (Finset.univ : Finset G.V).val = i₀ ::ₘ (Finset.univ : Finset G.V).val.erase i₀ :=
    (Multiset.cons_erase hmem).symm
  have hnodup : i₀ ∉ (Finset.univ : Finset G.V).val.erase i₀ := fun h ↦ by
    have hnd := Finset.univ.nodup (α := G.V)
    rw [hsplit] at hnd
    exact (Multiset.nodup_cons.1 hnd).1 h
  have hspecG : G.spectrum.erase (k : ℝ)
      = ((Finset.univ : Finset G.V).val.erase i₀).map G.eigenvalues := by
    rw [spectrum_eq_map]
    conv_lhs => rw [hsplit]
    rw [Multiset.map_cons, hlam, Multiset.erase_cons_head]
  rw [hspec, hspecG, Multiset.map_map]
  conv_lhs => rw [hsplit]
  rw [Multiset.map_cons]
  congr 1
  · simp [hdd, hlam]
  · refine Multiset.map_congr rfl fun i hi ↦ ?_
    have hne : i ≠ i₀ := fun h ↦ hnodup (h ▸ hi)
    simp [hdd, hne]

/-- **The spectral radius of the complement of a regular graph** is again its degree,
`n - 1 - k`: the complement of a regular graph is regular. -/
theorem lambdaMax_compl_of_isRegularWith {G : CGraph} [DecidableEq G.V] [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) :
    (compl G).lambdaMax = ((Fintype.card G.V - 1 - k : ℕ) : ℝ) :=
  lambdaMax_of_isRegularWith h.compl

/-- **The spectrum of the complement of the Petersen graph**: `6` once, `-2` five times and `1`
four times. -/
theorem spectrum_compl_petersen :
    (compl SRG.petersen).spectrum
      = 6 ::ₘ (Multiset.replicate 5 (-2 : ℝ) + Multiset.replicate 4 1) := by
  have hconn : SRG.petersen.IsConnected :=
    SRG.petersen_srg.isConnected (by norm_num) (by norm_num)
  have hreg : SRG.petersen.IsRegularWith 3 := SRG.petersen_srg.regular
  have hcard : Fintype.card SRG.petersen.V = 10 := SRG.petersen_srg.card
  rw [spectrum_compl_of_isRegularWith hconn hreg, hcard, spectrum_petersen]
  norm_num [Multiset.erase_cons_head, Multiset.map_add, Multiset.map_replicate]

/-- **The spectral radius of the complement of the Petersen graph** is its degree `6`. -/
theorem lambdaMax_compl_petersen : (compl SRG.petersen).lambdaMax = 6 := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_compl_petersen, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_refl _
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
  · rw [spectrum_compl_petersen]
    exact Multiset.mem_cons_self _ _

/-- **The least eigenvalue of the complement of the Petersen graph** is `-2`, the complement being
the triangular graph `T (5)` and so a line graph. -/
theorem lambdaMin_compl_petersen : (compl SRG.petersen).lambdaMin = -2 := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_compl_petersen]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
  · have hx := lambdaMin_mem_spectrum (compl SRG.petersen)
    rw [spectrum_compl_petersen, Multiset.mem_cons] at hx
    rcases hx with h | h
    · rw [h]; linarith
    rcases Multiset.mem_add.1 h with h | h
    · rw [Multiset.eq_of_mem_replicate h]
    · rw [Multiset.eq_of_mem_replicate h]; linarith

/-! ## An orthonormal eigenbasis -/

/-- **An orthonormal eigenbasis.**  The columns of the orthogonal matrix diagonalising `A` form a
family `e` of unit eigenvectors, pairwise orthogonal, in which every vector expands. -/
theorem exists_orthonormal_eigenbasis (G : CGraph) :
    ∃ e : G.V → G.V → ℝ,
      (∀ i, G.adjMat *ᵥ e i = G.eigenvalues i • e i) ∧
      (∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0) ∧
      (∀ v : G.V → ℝ, v = ∑ i, (e i ⬝ᵥ v) • e i) := by
  obtain ⟨U, hUU, hUU', hD⟩ := G.exists_orthogonal_diagonal
  have hAU : G.adjMat * U = U * Matrix.diagonal G.eigenvalues := by
    calc G.adjMat * U = U * Uᵀ * G.adjMat * U := by rw [hUU', one_mul]
      _ = U * (Uᵀ * G.adjMat * U) := by simp only [mul_assoc]
      _ = U * Matrix.diagonal G.eigenvalues := by rw [hD]
  refine ⟨fun i x ↦ U x i, fun i ↦ funext fun x ↦ ?_, fun i j ↦ ?_, fun v ↦ funext fun x ↦ ?_⟩
  · have h := congrFun (congrFun hAU x) i
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  · have h := congrFun (congrFun hUU i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    simpa [dotProduct] using h
  · have h : ∀ y, (if x = y then (1 : ℝ) else 0) = ∑ i, U x i * U y i := fun y ↦ by
      have h' := congrFun (congrFun hUU' x) y
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h'
      exact h'.symm
    calc v x = ∑ y, (if x = y then (1 : ℝ) else 0) * v y := by simp
      _ = ∑ y, ∑ i, U x i * U y i * v y := by simp_rw [h, Finset.sum_mul]
      _ = ∑ i, ∑ y, U x i * U y i * v y := Finset.sum_comm
      _ = ∑ i, (∑ y, U y i * v y) * U x i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun y _ ↦ by ring
      _ = _ := by simp [dotProduct]

/-- The multiplicity of `c` in the spectrum counts the indices carrying the eigenvalue `c`. -/
theorem count_spectrum (G : CGraph) (c : ℝ) :
    G.spectrum.count c = (Finset.univ.filter fun i ↦ G.eigenvalues i = c).card := by
  rw [spectrum_eq_map, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-! ## Perron–Frobenius: the largest eigenvalue of a connected graph

Nonnegativity of `A` makes `|v|` an eigenvector whenever `v` is one for `λ_max`, and connectedness
then makes it strictly positive; the top eigenspace is spanned by that positive vector, so `λ_max`
is a simple eigenvalue. -/

/-- **Taking absolute values preserves a `λ_max`-eigenvector.**  Since `A` has nonnegative entries,
`⟪|v|, A |v|⟫ ≥ ⟪v, A v⟫`, while the two vectors have the same norm; so `|v|` also attains the
maximum of the Rayleigh quotient, and an attaining vector is an eigenvector. -/
theorem mulVec_abs_of_mulVec_eq_lambdaMax {G : CGraph} [Nonempty G.V] {v : G.V → ℝ}
    (hv : G.adjMat *ᵥ v = G.lambdaMax • v) :
    G.adjMat *ᵥ (fun x ↦ |v x|) = G.lambdaMax • fun x ↦ |v x| := by
  refine mulVec_eq_of_rayleigh_eq_lambdaMax G (le_antisymm (G.rayleigh_le_lambdaMax _) ?_)
  have hnorm : (fun x ↦ |v x|) ⬝ᵥ (fun x ↦ |v x|) = v ⬝ᵥ v := by
    simp [dotProduct, abs_mul_abs_self]
  have hveq : v ⬝ᵥ (G.adjMat *ᵥ v) = G.lambdaMax * (v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have hq : v ⬝ᵥ (G.adjMat *ᵥ v) ≤ (fun x ↦ |v x|) ⬝ᵥ (G.adjMat *ᵥ fun x ↦ |v x|) :=
    (le_abs_self _).trans (G.abs_dotProduct_mulVec_le v)
  rw [hnorm]
  linarith [hveq ▸ hq]

/-- **A nonnegative eigenvector of a connected graph is strictly positive.**  If it vanished at a
vertex, the eigenvector equation there would be a sum of nonnegative terms equal to zero, so it
would vanish at every neighbour, and connectedness would spread the zero everywhere. -/
theorem pos_of_mulVec_eq_of_nonneg {G : CGraph} (hconn : G.IsConnected) {c : ℝ} {w : G.V → ℝ}
    (hw : G.adjMat *ᵥ w = c • w) (hnn : ∀ x, 0 ≤ w x) (hne : w ≠ 0) (x : G.V) : 0 < w x := by
  classical
  have hnb : ∀ y : G.V, ∑ z ∈ G.toSimple.neighborFinset y, w z = c * w y := by
    intro y
    have h1 := congrFun hw y
    rw [show (G.adjMat *ᵥ w) y = ∑ z ∈ G.toSimple.neighborFinset y, w z from by
      simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]] at h1
    simpa using h1
  have hstep : ∀ y z : G.V, G.toSimple.Adj y z → w y = 0 → w z = 0 := by
    intro y z hyz hy
    refine (Finset.sum_eq_zero_iff_of_nonneg fun u _ ↦ hnn u).1 ?_ z
      ((SimpleGraph.mem_neighborFinset _ _ _).2 hyz)
    rw [hnb y, hy, mul_zero]
  rcases (hnn x).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    refine hne (funext fun y ↦ ?_)
    have hwalk : ∀ (a b : G.V) (p : G.toSimple.Walk a b), w a = 0 → w b = 0 := by
      intro a b p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun ha ↦ ih (hstep _ _ h ha)
    exact (hconn.preconnected x y).elim fun p ↦ hwalk x y p heq.symm

/-- **Perron–Frobenius for a connected graph**: the largest eigenvalue has an everywhere positive
eigenvector. -/
theorem exists_pos_mulVec_eq_lambdaMax {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected) :
    ∃ w : G.V → ℝ, (∀ x, 0 < w x) ∧ G.adjMat *ᵥ w = G.lambdaMax • w := by
  obtain ⟨v, hv0, hv⟩ := (G.mem_spectrum_iff _).1 G.lambdaMax_mem_spectrum
  refine ⟨fun x ↦ |v x|, ?_, mulVec_abs_of_mulVec_eq_lambdaMax hv⟩
  refine pos_of_mulVec_eq_of_nonneg hconn (mulVec_abs_of_mulVec_eq_lambdaMax hv)
    (fun x ↦ abs_nonneg _) ?_
  obtain ⟨x0, hx0⟩ := Function.ne_iff.1 hv0
  exact fun h ↦ hx0 (abs_eq_zero.1 (congrFun h x0))

/-- **The top eigenspace of a connected graph is a line.**  Subtracting the largest multiple of the
positive eigenvector `w` that still fits under `u` leaves a nonnegative eigenvector vanishing
somewhere, which must be zero. -/
theorem exists_smul_of_mulVec_eq_lambdaMax {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected)
    {w u : G.V → ℝ} (hwpos : ∀ x, 0 < w x) (hw : G.adjMat *ᵥ w = G.lambdaMax • w)
    (hu : G.adjMat *ᵥ u = G.lambdaMax • u) : ∃ t : ℝ, u = t • w := by
  classical
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image (Finset.univ : Finset G.V) (fun x ↦ u x / w x)
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = u x0 / w x0 := ⟨_, rfl⟩
  refine ⟨t, ?_⟩
  by_contra hne
  have hzne : u - t • w ≠ 0 := fun h ↦ hne (by
    have := sub_eq_zero.1 h
    simpa using this)
  have hz : G.adjMat *ᵥ (u - t • w) = G.lambdaMax • (u - t • w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hu, hw, smul_sub, smul_comm]
  have hnn : ∀ x, 0 ≤ (u - t • w) x := by
    intro x
    have h1 : t ≤ u x / w x := by rw [htdef]; exact hx0 x (Finset.mem_univ x)
    have h2 : t * w x ≤ u x := (le_div_iff₀ (hwpos x)).1 h1
    simpa using by linarith [h2]
  have hpos := pos_of_mulVec_eq_of_nonneg hconn hz hnn hzne x0
  have hzero : (u - t • w) x0 = 0 := by
    have : t * w x0 = u x0 := by
      rw [htdef, div_mul_cancel₀ _ (ne_of_gt (hwpos x0))]
    simpa using by linarith [this]
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- **The largest eigenvalue of a connected graph is simple.**  Two orthonormal eigenvectors for it
would both be multiples of the same positive vector `w`, hence have inner product a nonzero
multiple of `⟪w, w⟫`. -/
theorem count_spectrum_lambdaMax_eq_one {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected) :
    G.spectrum.count G.lambdaMax = 1 := by
  classical
  obtain ⟨e, heig, hortho, -⟩ := G.exists_orthonormal_eigenbasis
  obtain ⟨w, hwpos, hw⟩ := exists_pos_mulVec_eq_lambdaMax hconn
  have hww : 0 < w ⬝ᵥ w := by
    rw [dotProduct]
    exact Finset.sum_pos (fun x _ ↦ mul_pos (hwpos x) (hwpos x)) ⟨Classical.arbitrary G.V,
      Finset.mem_univ _⟩
  rw [count_spectrum]
  refine le_antisymm (Finset.card_le_one.2 fun i hi j hj ↦ ?_) ?_
  · rw [Finset.mem_filter] at hi hj
    by_contra hne
    obtain ⟨a, ha⟩ := exists_smul_of_mulVec_eq_lambdaMax hconn hwpos hw (hi.2 ▸ heig i)
    obtain ⟨b, hb⟩ := exists_smul_of_mulVec_eq_lambdaMax hconn hwpos hw (hj.2 ▸ heig j)
    have hii : a * a * (w ⬝ᵥ w) = 1 := by
      have := hortho i i
      rw [if_pos rfl, ha, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      linarith [this]
    have hij : a * b * (w ⬝ᵥ w) = 0 := by
      have := hortho i j
      rw [if_neg hne, ha, hb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      linarith [this]
    have hjj : b * b * (w ⬝ᵥ w) = 1 := by
      have := hortho j j
      rw [if_pos rfl, hb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      linarith [this]
    nlinarith [hii, hij, hjj, hww]
  · rw [Finset.one_le_card]
    have hmem := G.lambdaMax_mem_spectrum
    rw [spectrum_eq_map, Multiset.mem_map] at hmem
    obtain ⟨i, -, hi⟩ := hmem
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩

/-- **A connected graph with `λ_max = Δ` is regular.**  At a vertex where the positive Perron
vector `w` is largest, `Δ w x = ∑_{y ∼ x} w y ≤ deg x · w x ≤ Δ w x`, so `x` has full degree and
`w` is again largest at every neighbour; connectedness makes `w` constant, and then the
eigenvector equation reads `deg x = Δ` at every vertex. -/
theorem isRegularWith_of_lambdaMax_eq_maxDeg {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected)
    (h : G.lambdaMax = (G.maxDeg : ℝ)) : G.IsRegularWith G.maxDeg := by
  classical
  obtain ⟨w, hwpos, hw⟩ := exists_pos_mulVec_eq_lambdaMax hconn
  have hnb : ∀ x : G.V, ∑ y ∈ G.toSimple.neighborFinset x, w y = (G.maxDeg : ℝ) * w x := by
    intro x
    have h1 := congrFun hw x
    rw [show (G.adjMat *ᵥ w) x = ∑ y ∈ G.toSimple.neighborFinset x, w y from by
      simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply], h] at h1
    simpa using h1
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image (Finset.univ : Finset G.V) w
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  have hle : ∀ x : G.V, w x ≤ w x0 := fun x ↦ hx0 x (Finset.mem_univ x)
  have hstep : ∀ x : G.V, w x = w x0 →
      G.toSimple.degree x = G.maxDeg ∧ ∀ y ∈ G.toSimple.neighborFinset x, w y = w x0 := by
    intro x hx
    have hdle : G.toSimple.degree x ≤ G.maxDeg := G.degree_le_maxDeg x
    have hsum : ∑ y ∈ G.toSimple.neighborFinset x, w y ≤ (G.toSimple.degree x : ℝ) * w x0 := by
      rw [show (G.toSimple.degree x : ℝ) * w x0
          = ∑ _y ∈ G.toSimple.neighborFinset x, w x0 from by
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]]
      exact Finset.sum_le_sum fun y _ ↦ hle y
    rw [hnb x, hx] at hsum
    have hw0 : 0 < w x0 := hwpos x0
    have hdeg : G.toSimple.degree x = G.maxDeg := by
      have : (G.maxDeg : ℝ) ≤ (G.toSimple.degree x : ℝ) :=
        le_of_mul_le_mul_right (by linarith [hsum]) hw0
      exact le_antisymm hdle (by exact_mod_cast this)
    refine ⟨hdeg, fun y hy ↦ ?_⟩
    have hzero : ∑ z ∈ G.toSimple.neighborFinset x, (w x0 - w z) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        hdeg, nsmul_eq_mul, hnb x, hx]
      ring
    have := (Finset.sum_eq_zero_iff_of_nonneg fun z _ ↦ sub_nonneg.2 (hle z)).1 hzero y hy
    linarith [this]
  have hconst : ∀ x : G.V, w x = w x0 := by
    intro x
    have hwalk : ∀ (a b : G.V) (p : G.toSimple.Walk a b), w a = w x0 → w b = w x0 := by
      intro a b p
      induction p with
      | nil => exact id
      | cons hadj _ ih =>
        exact fun ha ↦ ih ((hstep _ ha).2 _ ((SimpleGraph.mem_neighborFinset _ _ _).2 hadj))
    exact (hconn.preconnected x0 x).elim fun p ↦ hwalk x0 x p rfl
  exact fun x ↦ (hstep x (hconst x)).1

/-- **For a connected graph the largest eigenvalue equals the maximum degree exactly when the graph
is regular**, bracketing `λ_max` strictly below `Δ` otherwise. -/
theorem lambdaMax_eq_maxDeg_iff {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected) :
    G.lambdaMax = (G.maxDeg : ℝ) ↔ G.IsRegularWith G.maxDeg :=
  ⟨isRegularWith_of_lambdaMax_eq_maxDeg hconn, lambdaMax_of_isRegularWith⟩

/-! ## Connectedness of a regular graph is spectral

The degree of a `k`-regular graph is its largest eigenvalue, so for a connected graph it is simple;
conversely the indicator of a component is a second eigenvector for `k` when the graph is not
connected. -/

/-- **A simple eigenvalue has a one-dimensional eigenspace**: if `c` occurs once in the spectrum
then every eigenvector for `c` is a multiple of any fixed nonzero one.  Expanding in an
orthonormal eigenbasis, the coordinates off the `c`-eigenspace vanish, and only one coordinate
is left. -/
theorem exists_smul_of_count_spectrum_eq_one {G : CGraph} {c : ℝ}
    (hc : G.spectrum.count c = 1) {u v : G.V → ℝ} (hu : G.adjMat *ᵥ u = c • u) (hu0 : u ≠ 0)
    (hv : G.adjMat *ᵥ v = c • v) : ∃ a : ℝ, v = a • u := by
  obtain ⟨e, heig, -, hexp⟩ := G.exists_orthonormal_eigenbasis
  have htrans : G.adjMatᵀ = G.adjMat := Matrix.ext fun i j ↦ adjMat_symm G j i
  have hcoord : ∀ z : G.V → ℝ, G.adjMat *ᵥ z = c • z → ∀ i, G.eigenvalues i ≠ c →
      e i ⬝ᵥ z = 0 := by
    intro z hz i hi
    have hvm : e i ᵥ* G.adjMat = G.eigenvalues i • e i := by
      rw [show G.adjMat = G.adjMatᵀ from htrans.symm, Matrix.vecMul_transpose]
      exact heig i
    have h1 : e i ⬝ᵥ (G.adjMat *ᵥ z) = G.eigenvalues i * (e i ⬝ᵥ z) := by
      rw [dotProduct_mulVec, hvm, smul_dotProduct, smul_eq_mul]
    rw [hz, dotProduct_smul, smul_eq_mul] at h1
    have h2 : (G.eigenvalues i - c) * (e i ⬝ᵥ z) = 0 := by linarith [h1]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hi
    · exact h
  rw [count_spectrum] at hc
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.1 hc
  have hsingle : ∀ z : G.V → ℝ, G.adjMat *ᵥ z = c • z → z = (e i0 ⬝ᵥ z) • e i0 := by
    intro z hz
    conv_lhs => rw [hexp z]
    refine Finset.sum_eq_single i0 (fun i _ hi ↦ ?_) fun h ↦ absurd (Finset.mem_univ i0) h
    have hne : G.eigenvalues i ≠ c := by
      intro hEq
      have hmem : i ∈ Finset.univ.filter fun j ↦ G.eigenvalues j = c :=
        Finset.mem_filter.2 ⟨Finset.mem_univ i, hEq⟩
      rw [hi0, Finset.mem_singleton] at hmem
      exact hi hmem
    rw [hcoord z hz i hne, zero_smul]
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = e i0 ⬝ᵥ u := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = e i0 ⬝ᵥ v := ⟨_, rfl⟩
  have hu' : u = b • e i0 := by rw [hbdef]; exact hsingle u hu
  have hv' : v = d • e i0 := by rw [hddef]; exact hsingle v hv
  have hb : b ≠ 0 := by
    intro h0
    exact hu0 (by rw [hu', h0, zero_smul])
  exact ⟨d / b, by rw [hv', hu', smul_smul, div_mul_cancel₀ _ hb]⟩

/-- **The degree of a connected regular graph is a simple eigenvalue.**  It is the largest
eigenvalue of a regular graph, and the largest eigenvalue of a connected graph is simple. -/
theorem count_spectrum_eq_one_of_isConnected {G : CGraph} (hconn : G.IsConnected) {k : ℕ}
    (hreg : G.IsRegularWith k) : G.spectrum.count (k : ℝ) = 1 := by
  haveI : Nonempty G.V := hconn.nonempty
  rw [← lambdaMax_of_isRegularWith hreg]
  exact count_spectrum_lambdaMax_eq_one hconn

/-- **A regular graph whose degree is a simple eigenvalue is connected.**  Otherwise the
indicator of a connected component is a second, non-constant eigenvector for `k`. -/
theorem isConnected_of_count_spectrum_eq_one {G : CGraph} {k : ℕ} (hreg : G.IsRegularWith k)
    (hc : G.spectrum.count (k : ℝ) = 1) : G.IsConnected := by
  haveI : Nonempty G.V := by
    rw [← Fintype.card_pos_iff, ← card_spectrum]
    have h1 : 0 < Multiset.count (k : ℝ) G.spectrum := by omega
    exact lt_of_lt_of_le h1 (Multiset.count_le_card _ _)
  have hone : G.adjMat *ᵥ (1 : G.V → ℝ) = (k : ℝ) • (1 : G.V → ℝ) :=
    (hasEigenvector_one_of_isRegularWith hreg).2
  have hone0 : (1 : G.V → ℝ) ≠ 0 := fun h ↦ by
    simpa using congrFun h (Classical.arbitrary G.V)
  rw [IsConnected, SimpleGraph.connected_iff]
  refine ⟨fun a b ↦ ?_, ‹Nonempty G.V›⟩
  by_contra hnr
  set z : G.V → ℝ := fun x ↦ if G.toSimple.Reachable a x then 1 else 0 with hzdef
  have hz : G.adjMat *ᵥ z = (k : ℝ) • z := by
    funext x
    rw [show (G.adjMat *ᵥ z) x = ∑ y ∈ G.toSimple.neighborFinset x, z y from by
      simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]]
    by_cases hx : G.toSimple.Reachable a x
    · have hall : ∀ y ∈ G.toSimple.neighborFinset x, z y = 1 := by
        intro y hy
        have hy' : G.toSimple.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
        simp [hzdef, hx.trans hy'.reachable]
      have hd : (G.toSimple.neighborFinset x).card = k := hreg x
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hd]
      simp [hzdef, hx]
    · have hall : ∀ y ∈ G.toSimple.neighborFinset x, z y = 0 := by
        intro y hy
        have hy' : G.toSimple.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
        have : ¬ G.toSimple.Reachable a y := fun h ↦ hx (h.trans hy'.symm.reachable)
        simp [hzdef, this]
      rw [Finset.sum_congr rfl hall, Finset.sum_const_zero]
      simp [hzdef, hx]
  obtain ⟨t, ht⟩ := exists_smul_of_count_spectrum_eq_one hc hone hone0 hz
  have hza : z a = 1 := by simp [hzdef]
  have hzb : z b = 0 := by simp [hzdef, hnr]
  rw [ht] at hza hzb
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hza hzb
  exact absurd (hza.symm.trans hzb) one_ne_zero

/-- **Connectedness of a regular graph is read off its spectrum**: the degree is a simple
eigenvalue exactly for the connected ones. -/
theorem isConnected_iff_count_spectrum_eq_one {G : CGraph} {k : ℕ} (hreg : G.IsRegularWith k) :
    G.IsConnected ↔ G.spectrum.count (k : ℝ) = 1 :=
  ⟨fun h ↦ count_spectrum_eq_one_of_isConnected h hreg, isConnected_of_count_spectrum_eq_one hreg⟩

/-- **Connectedness is determined by the spectrum, for a regular graph.** -/
@[toIsoGraph]
theorem Cospectral.isConnected {G H : CGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) (hconn : G.IsConnected) : H.IsConnected :=
  (isConnected_iff_count_spectrum_eq_one (h.isRegularWith hG)).2
    (by rw [← h.spectrum_eq]; exact (isConnected_iff_count_spectrum_eq_one hG).1 hconn)

/-! ## Bipartiteness of a connected graph is spectral

The easy half is `spectrum_neg_of_isBipartite`: the spectrum of a bipartite graph is symmetric, so
`-λ_max` is an eigenvalue whenever `λ_max` is.  The converse needs connectedness, and for a regular
graph it becomes a statement about the degree, `-k` being the smallest possible eigenvalue. -/

/-- **A connected graph with `-λ_max` in its spectrum is bipartite.**  If `A v = -λ_max v` then
`|v|` attains the maximum of the Rayleigh quotient, so it is a positive `λ_max`-eigenvector; the
two quadratic forms then differ by a sum of nonnegative terms which vanishes, forcing
`v x · v y < 0` on every edge.  The sign of `v` is a proper `2`-colouring. -/
theorem isBipartite_of_neg_lambdaMax_mem_spectrum {G : CGraph} [Nonempty G.V]
    (hconn : G.IsConnected) (h : -G.lambdaMax ∈ G.spectrum) : G.IsBipartite := by
  classical
  obtain ⟨v, hv0, hv⟩ := (G.mem_spectrum_iff _).1 h
  obtain ⟨u, hudef⟩ : ∃ u : G.V → ℝ, u = fun y ↦ |v y| := ⟨_, rfl⟩
  have hnorm : u ⬝ᵥ u = v ⬝ᵥ v := by
    rw [hudef]
    simp [dotProduct, abs_mul_abs_self]
  have hpos : 0 < v ⬝ᵥ v := by
    obtain ⟨y0, hy0⟩ := Function.ne_iff.1 hv0
    rw [dotProduct]
    exact Finset.sum_pos' (fun y _ ↦ mul_self_nonneg _)
      ⟨y0, Finset.mem_univ _, mul_self_pos.2 hy0⟩
  have hvv : v ⬝ᵥ (G.adjMat *ᵥ v) = -G.lambdaMax * (v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have heq : u ⬝ᵥ (G.adjMat *ᵥ u) = G.lambdaMax * (u ⬝ᵥ u) := by
    refine le_antisymm (G.rayleigh_le_lambdaMax u) ?_
    have h2 : |v ⬝ᵥ (G.adjMat *ᵥ v)| ≤ u ⬝ᵥ (G.adjMat *ᵥ u) := by
      rw [hudef]
      exact G.abs_dotProduct_mulVec_le v
    rw [hvv, abs_mul, abs_neg, abs_of_nonneg G.lambdaMax_nonneg, abs_of_pos hpos] at h2
    rw [hnorm]
    exact h2
  have hue : G.adjMat *ᵥ u = G.lambdaMax • u := mulVec_eq_of_rayleigh_eq_lambdaMax G heq
  have hu0 : u ≠ 0 := by
    intro h0
    rw [← hnorm, h0] at hpos
    simp [dotProduct] at hpos
  have hupos : ∀ y : G.V, 0 < u y :=
    pos_of_mulVec_eq_of_nonneg hconn hue (fun y ↦ by rw [hudef]; exact abs_nonneg _) hu0
  have hpt : ∀ x y : G.V, 0 ≤ G.adjMat x y * (u x * u y + v x * v y) := by
    intro x y
    refine mul_nonneg (adjMat_nonneg G x y) ?_
    rw [hudef]
    dsimp only
    rw [← abs_mul]
    linarith [neg_abs_le (v x * v y)]
  have hsum : ∑ x, ∑ y, G.adjMat x y * (u x * u y + v x * v y) = 0 := by
    have h1 : ∑ x, ∑ y, G.adjMat x y * (u x * u y + v x * v y)
        = u ⬝ᵥ (G.adjMat *ᵥ u) + v ⬝ᵥ (G.adjMat *ᵥ v) := by
      rw [dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by ring
    rw [h1, heq, hvv, hnorm]
    ring
  have hterm : ∀ x y : G.V, G.adjMat x y * (u x * u y + v x * v y) = 0 := by
    intro x y
    have h1 : ∑ y', G.adjMat x y' * (u x * u y' + v x * v y') = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun x' _ ↦
        Finset.sum_nonneg fun y' _ ↦ hpt x' y').1 hsum x (Finset.mem_univ x)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y' _ ↦ hpt x y').1 h1 y (Finset.mem_univ y)
  refine ⟨fun x ↦ decide (0 < v x), fun x y hxy ↦ ?_⟩
  have hone : G.adjMat x y = 1 := by rw [adjMat_apply]; simp [hxy]
  have hlt : v x * v y < 0 := by
    have := hterm x y
    rw [hone, one_mul] at this
    nlinarith [hupos x, hupos y, this]
  rcases mul_neg_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, not_lt.2 h2.le]
  · simp [h2, not_lt.2 h1.le]

/-- **A connected graph is bipartite exactly when `λ_min = -λ_max`.** -/
theorem isBipartite_iff_lambdaMin_eq_neg_lambdaMax {G : CGraph} [Nonempty G.V]
    (hconn : G.IsConnected) : G.IsBipartite ↔ G.lambdaMin = -G.lambdaMax := by
  refine ⟨lambdaMin_eq_neg_lambdaMax_of_isBipartite, fun hm ↦ ?_⟩
  exact isBipartite_of_neg_lambdaMax_mem_spectrum hconn (hm ▸ G.lambdaMin_mem_spectrum)

/-- **A connected regular graph with `-k` in its spectrum is bipartite**, since `k` is its largest
eigenvalue. -/
theorem isBipartite_of_neg_mem_spectrum {G : CGraph} (hconn : G.IsConnected) {k : ℕ}
    (hreg : G.IsRegularWith k) (hk : -(k : ℝ) ∈ G.spectrum) : G.IsBipartite := by
  haveI : Nonempty G.V := hconn.nonempty
  exact isBipartite_of_neg_lambdaMax_mem_spectrum hconn
    (by rwa [lambdaMax_of_isRegularWith hreg])

/-- **Bipartiteness of a connected regular graph is determined by its spectrum.** -/
theorem isBipartite_iff_neg_mem_spectrum {G : CGraph} (hconn : G.IsConnected) {k : ℕ}
    (hreg : G.IsRegularWith k) : G.IsBipartite ↔ -(k : ℝ) ∈ G.spectrum := by
  refine ⟨fun h ↦ ?_, isBipartite_of_neg_mem_spectrum hconn hreg⟩
  haveI : Nonempty G.V := hconn.nonempty
  rw [← spectrum_neg_of_isBipartite h, Multiset.mem_map]
  exact ⟨(k : ℝ), mem_spectrum_of_isRegularWith hreg, rfl⟩

/-- **A connected regular graph is bipartite exactly when `λ_min = -k`.**  The lower bound
`-Δ ≤ λ_min` is the other half: for a regular graph `-k` is as small as an eigenvalue can be. -/
theorem isBipartite_iff_lambdaMin_eq {G : CGraph} [Nonempty G.V] (hconn : G.IsConnected) {k : ℕ}
    (hreg : G.IsRegularWith k) : G.IsBipartite ↔ G.lambdaMin = -(k : ℝ) := by
  have hmax : G.maxDeg = k := hreg.maxDeg_eq (Classical.arbitrary G.V)
  rw [isBipartite_iff_neg_mem_spectrum hconn hreg]
  refine ⟨fun h ↦ le_antisymm (lambdaMin_le h) ?_, fun h ↦ h ▸ G.lambdaMin_mem_spectrum⟩
  have := G.neg_maxDeg_le_lambdaMin
  rwa [hmax] at this

/-- **Bipartiteness of a connected regular graph is determined by the spectrum.** -/
@[toIsoGraph]
theorem Cospectral.isBipartite {G H : CGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) (hconn : G.IsConnected) (hbip : G.IsBipartite) : H.IsBipartite :=
  (isBipartite_iff_neg_mem_spectrum (h.isConnected hG hconn) (h.isRegularWith hG)).2
    (by rw [← h.spectrum_eq]; exact (isBipartite_iff_neg_mem_spectrum hconn hG).1 hbip)

/-! ## The number of distinct eigenvalues bounds the diameter

`minSpecPoly`, the product of `X - λ` over the *distinct* eigenvalues, annihilates the adjacency
matrix: conjugating to the diagonal form turns `p (A)` into `diagonal (p ∘ λ)`, which is zero.
So `A ᵏ` is a combination of the lower powers, where `k` is the number of distinct eigenvalues.
Comparing the `(u, v)` entry with the walk counts of `adjMat_pow_apply` gives
`dist_lt_card_toFinset_spectrum` and hence `diameter_lt_card_toFinset_spectrum`. -/

/-- The monic polynomial whose roots are the **distinct** eigenvalues of `G`, each once.  It is
the minimal polynomial of the adjacency matrix, though that is not proved here. -/
noncomputable def minSpecPoly (G : CGraph) : ℝ[X] :=
  ∏ x ∈ G.spectrum.toFinset, (X - C x)

theorem monic_minSpecPoly (G : CGraph) : G.minSpecPoly.Monic :=
  monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C x

@[simp] theorem natDegree_minSpecPoly (G : CGraph) :
    G.minSpecPoly.natDegree = G.spectrum.toFinset.card := by
  rw [minSpecPoly, natDegree_prod _ _ fun x _ ↦ X_sub_C_ne_zero x]
  simp

theorem eval_minSpecPoly_eigenvalues (G : CGraph) (i : G.V) :
    G.minSpecPoly.eval (G.eigenvalues i) = 0 := by
  rw [minSpecPoly, eval_prod]
  refine Finset.prod_eq_zero (i := G.eigenvalues i) ?_ (by simp)
  simpa using G.eigenvalues_mem_spectrum i

/-- **The distinct eigenvalues annihilate the adjacency matrix.**  Written out, this says that
`A ^ k` is a linear combination of `1, A, …, A ^ (k - 1)`, with `k` the number of distinct
eigenvalues. -/
theorem sum_coeff_smul_adjMat_pow (G : CGraph) :
    ∑ i ∈ Finset.range (G.spectrum.toFinset.card + 1),
      G.minSpecPoly.coeff i • G.adjMat ^ i = 0 := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_conj_diagonal G
  set D : Matrix G.V G.V ℝ := Matrix.diagonal G.eigenvalues with hD
  have hA : G.adjMat = P * D * Q := by
    calc G.adjMat = G.adjMat * (P * Q) := by rw [hPQ, mul_one]
      _ = G.adjMat * P * Q := by rw [mul_assoc]
      _ = P * D * Q := by rw [h]
  have hpow : ∀ m : ℕ, G.adjMat ^ m = P * D ^ m * Q := by
    intro m
    induction m with
    | zero => simp [hPQ]
    | succ m ih =>
      rw [pow_succ, ih, hA, pow_succ]
      calc P * D ^ m * Q * (P * D * Q) = P * D ^ m * (Q * P) * D * Q := by
            simp only [mul_assoc]
        _ = P * (D ^ m * D) * Q := by rw [hQP]; simp only [mul_assoc, mul_one]
  have hsum : ∑ i ∈ Finset.range (G.spectrum.toFinset.card + 1),
      G.minSpecPoly.coeff i • D ^ i = 0 := by
    ext u v
    rw [Matrix.sum_apply, Matrix.zero_apply]
    by_cases huv : u = v
    · subst huv
      rw [Finset.sum_congr rfl fun i _ ↦
        show (G.minSpecPoly.coeff i • D ^ i) u u = G.minSpecPoly.coeff i * G.eigenvalues u ^ i from
          by simp [hD, Matrix.diagonal_pow, Matrix.diagonal_apply_eq],
        ← G.natDegree_minSpecPoly, ← eval_eq_sum_range]
      exact G.eval_minSpecPoly_eigenvalues u
    · refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [hD, Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ huv]
  calc ∑ i ∈ Finset.range (G.spectrum.toFinset.card + 1),
        G.minSpecPoly.coeff i • G.adjMat ^ i
      = P * (∑ i ∈ Finset.range (G.spectrum.toFinset.card + 1),
          G.minSpecPoly.coeff i • D ^ i) * Q := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hpow, Matrix.mul_smul, Matrix.smul_mul]
    _ = 0 := by rw [hsum]; simp

/-- Below the distance there are no walks at all. -/
theorem adjMat_pow_apply_eq_zero_of_lt_dist (G : CGraph) {u v : G.V} {n : ℕ}
    (h : n < G.toSimple.dist u v) : (G.adjMat ^ n) u v = 0 := by
  rw [adjMat_pow_apply, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
  refine ⟨fun w ↦ ?_⟩
  exact absurd (w.2 ▸ SimpleGraph.dist_le w.1) (not_le.2 h)

/-- At the distance there is one. -/
theorem adjMat_pow_apply_pos_of_dist_eq (G : CGraph) {u v : G.V} {n : ℕ}
    (hr : G.toSimple.Reachable u v) (h : G.toSimple.dist u v = n) :
    0 < (G.adjMat ^ n) u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [adjMat_pow_apply, Nat.cast_pos, Fintype.card_pos_iff]
  exact ⟨⟨p, hp.trans h⟩⟩

/-- **Every distance below an attained one is attained**: cutting a shortest walk at its `i`-th
vertex produces a vertex at distance exactly `i` from the start, because the two halves have
lengths `i` and `d - i` and the triangle inequality leaves no slack. -/
theorem exists_dist_eq (G : CGraph) {u v : G.V} {i : ℕ} (hi : i ≤ G.toSimple.dist u v) :
    ∃ w : G.V, G.toSimple.dist u w = i := by
  rcases Nat.eq_zero_or_pos (G.toSimple.dist u v) with h0 | h0
  · exact ⟨u, by rw [SimpleGraph.dist_self]; omega⟩
  have hr : G.toSimple.Reachable u v := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  refine ⟨p.getVert i, le_antisymm ?_ ?_⟩
  · have := SimpleGraph.dist_le (p.take i)
    simpa [hp, Nat.min_eq_left hi] using this
  · have h1 := SimpleGraph.dist_le (p.drop i)
    rw [SimpleGraph.Walk.drop_length, hp] at h1
    have h2 : G.toSimple.Reachable (p.getVert i) v := (p.drop i).reachable
    have h3 := h2.dist_triangle_right u
    omega

/-- **Two vertices are closer than the number of distinct eigenvalues.**  If `dist u w = k` then
`(A ^ k) u w > 0` while `(A ^ i) u w = 0` for every `i < k`, so the annihilating relation
`∑ i ≤ k, c i A ^ i = 0` reads `1 * (A ^ k) u w = 0` at the entry `(u, w)` — a contradiction. -/
theorem dist_lt_card_toFinset_spectrum (G : CGraph) (u v : G.V) :
    G.toSimple.dist u v < G.spectrum.toFinset.card := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ : ∃ k, G.spectrum.toFinset.card = k := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := G.exists_dist_eq (u := u) (v := v) (i := k) (by omega)
  have hk0 : 0 < k := by
    rw [← hk]
    exact Finset.card_pos.2 ⟨G.eigenvalues u, by simpa using G.eigenvalues_mem_spectrum u⟩
  have hr : G.toSimple.Reachable u w := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  have hzero : ∑ i ∈ Finset.range (k + 1), G.minSpecPoly.coeff i * (G.adjMat ^ i) u w = 0 := by
    have h1 := G.sum_coeff_smul_adjMat_pow
    rw [hk] at h1
    have h2 := congrFun (congrFun h1 u) w
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h2
  rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi ↦ ?_), zero_add] at hzero
  · have hcoeff : G.minSpecPoly.coeff k = 1 := by
      have := G.monic_minSpecPoly.coeff_natDegree
      rwa [G.natDegree_minSpecPoly, hk] at this
    rw [hcoeff, one_mul] at hzero
    exact absurd hzero (ne_of_gt (G.adjMat_pow_apply_pos_of_dist_eq hr hw))
  · rw [Finset.mem_range] at hi
    rw [G.adjMat_pow_apply_eq_zero_of_lt_dist (by omega), mul_zero]

/-- **The number of distinct eigenvalues exceeds the diameter.** -/
theorem diameter_lt_card_toFinset_spectrum (G : CGraph) [Nonempty G.V] :
    G.diameter < G.spectrum.toFinset.card := by
  classical
  obtain ⟨u, v, huv⟩ := SimpleGraph.exists_dist_eq_diam (G := G.toSimple)
  rw [diameter, ← huv]
  exact G.dist_lt_card_toFinset_spectrum u v

/-! ## Few distinct eigenvalues -/

/-- The annihilation of `sum_coeff_smul_adjMat_pow`, packaged as an evaluation of `minSpecPoly`
in the matrix algebra.  This is the form in which the polynomial can be factored. -/
theorem aeval_minSpecPoly (G : CGraph) : aeval G.adjMat G.minSpecPoly = 0 := by
  rw [aeval_eq_sum_range, natDegree_minSpecPoly]
  exact G.sum_coeff_smul_adjMat_pow

/-- The square of the adjacency matrix counts common neighbours.  (On the diagonal that is the
degree; the statement holds there too, since a vertex is not its own neighbour.) -/
theorem adjMat_sq_apply (G : CGraph) (u v : G.V) :
    (G.adjMat ^ 2) u v = (Fintype.card (G.toSimple.commonNeighbors u v) : ℝ) := by
  have hset : Fintype.card (G.toSimple.commonNeighbors u v)
      = (Finset.univ.filter fun w ↦ G.Adj u w = true ∧ G.Adj w v = true).card := by
    rw [← Set.toFinset_card]
    congr 1
    ext w
    simp [SimpleGraph.mem_commonNeighbors, G.symm v w]
  rw [hset, pow_two, Matrix.mul_apply, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [adjMat_apply]
  by_cases h1 : G.Adj u w = true <;> by_cases h2 : G.Adj w v = true <;> simp [h1, h2]

/-- **A symmetric matrix whose columns are `k`-eigenvectors is a multiple of the all-ones
matrix**, when `G` is connected and `k`-regular.  The degree of a connected regular graph is a
simple eigenvalue with the all-ones eigenvector, so every column of `M` is constant; symmetry
then forces the columns to share their constant. -/
theorem exists_forall_eq_of_mul_eq_smul {G : CGraph} {k : ℕ} (hconn : G.IsConnected)
    (hreg : G.IsRegularWith k) {M : Matrix G.V G.V ℝ} (hsymm : ∀ i j, M i j = M j i)
    (hM : G.adjMat * M = (k : ℝ) • M) : ∃ c : ℝ, ∀ i j, M i j = c := by
  haveI : Nonempty G.V := hconn.nonempty
  have hcount := count_spectrum_eq_one_of_isConnected hconn hreg
  have hone : G.adjMat *ᵥ (1 : G.V → ℝ) = (k : ℝ) • 1 :=
    (hasEigenvector_one_of_isRegularWith hreg).2
  have hone0 : (1 : G.V → ℝ) ≠ 0 := by
    intro h
    simpa using congrFun h (Classical.arbitrary G.V)
  have hcol : ∀ j, ∃ a : ℝ, ∀ i, M i j = a := by
    intro j
    have hv : G.adjMat *ᵥ (fun i ↦ M i j) = (k : ℝ) • fun i ↦ M i j := by
      funext i
      have h1 := congrFun (congrFun hM i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1
    obtain ⟨a, ha⟩ := exists_smul_of_count_spectrum_eq_one hcount hone hone0 hv
    exact ⟨a, fun i ↦ by simpa using congrFun ha i⟩
  choose a ha using hcol
  refine ⟨a (Classical.arbitrary G.V), fun i j ↦ ?_⟩
  rw [ha j i, ← ha j (Classical.arbitrary G.V), hsymm _ j]
  exact ha (Classical.arbitrary G.V) j

/-- **A graph with one distinct eigenvalue has no edges.**  The minimal polynomial is `X - r`, so
`A = r` on the diagonal too — and the diagonal of an adjacency matrix is zero. -/
theorem adjMat_eq_zero_of_card_toFinset_spectrum_eq_one {G : CGraph} [Nonempty G.V]
    (h1 : G.spectrum.toFinset.card = 1) : G.adjMat = 0 := by
  obtain ⟨r, hspec⟩ := Finset.card_eq_one.1 h1
  have hpoly : G.minSpecPoly = X - C r := by
    rw [minSpecPoly, hspec, Finset.prod_singleton]
  have hann : G.adjMat - r • 1 = 0 := by
    have h2 := G.aeval_minSpecPoly
    rw [hpoly] at h2
    simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    exact h2
  have hA : G.adjMat = r • (1 : Matrix G.V G.V ℝ) := by
    rw [← sub_eq_zero]; exact hann
  have hr : r = 0 := by
    have h3 := congrFun (congrFun hA (Classical.arbitrary G.V)) (Classical.arbitrary G.V)
    simpa [adjMat_apply, G.adj_self] using h3.symm
  rw [hA, hr, zero_smul]

theorem adj_eq_false_of_card_toFinset_spectrum_eq_one {G : CGraph} [Nonempty G.V]
    (h1 : G.spectrum.toFinset.card = 1) (x y : G.V) : G.Adj x y = false := by
  have h2 := congrFun (congrFun (adjMat_eq_zero_of_card_toFinset_spectrum_eq_one h1) x) y
  rw [adjMat_apply, Matrix.zero_apply] at h2
  by_contra hn
  rw [Bool.not_eq_false] at hn
  rw [if_pos hn] at h2
  exact one_ne_zero h2

/-- **A connected regular graph with two distinct eigenvalues is complete.**  With the spectrum
`{k, r}` the matrix `M = A - r` is a constant `t J` by the same argument, and the vanishing
diagonal of `A` gives `r = -t`.  So every off-diagonal entry of `A` equals `t`, which is `0` or
`1`; and `t = 0` would make `A` the zero matrix, forcing `k = 0 = r`. -/
theorem adj_of_card_toFinset_spectrum_eq_two {G : CGraph} {k : ℕ} (hconn : G.IsConnected)
    (hreg : G.IsRegularWith k) (h2 : G.spectrum.toFinset.card = 2) (i j : G.V) (hij : i ≠ j) :
    G.Adj i j = true := by
  haveI : Nonempty G.V := hconn.nonempty
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1 h2
  have hk : (k : ℝ) ∈ G.spectrum.toFinset := by
    simpa using mem_spectrum_of_isRegularWith hreg
  rw [hset] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  obtain ⟨r, hkr, hspec⟩ : ∃ r : ℝ, (k : ℝ) ≠ r ∧ G.spectrum.toFinset = {(k : ℝ), r} := by
    rcases hk with rfl | rfl
    · exact ⟨b, hab, hset⟩
    · exact ⟨a, hab.symm, by rw [hset]; exact Finset.pair_comm _ _⟩
  have hpoly : G.minSpecPoly = (X - C (k : ℝ)) * (X - C r) := by
    rw [minSpecPoly, hspec, Finset.prod_insert (by simp [hkr]), Finset.prod_singleton]
  have hann : (G.adjMat - (k : ℝ) • 1) * (G.adjMat - r • 1) = 0 := by
    have h1 := G.aeval_minSpecPoly
    rw [hpoly] at h1
    simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h1
    exact h1
  set M : Matrix G.V G.V ℝ := G.adjMat - r • 1 with hMdef
  have hAM : G.adjMat * M = (k : ℝ) • M := by
    rw [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at hann
    exact hann
  have hsymm : ∀ x y, M x y = M y x := by
    intro x y
    rw [hMdef]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, adjMat_symm G x y,
      Matrix.one_apply, eq_comm (a := x) (b := y)]
  obtain ⟨t, ht⟩ := exists_forall_eq_of_mul_eq_smul hconn hreg hsymm hAM
  have hoff : ∀ x y : G.V, x ≠ y → G.adjMat x y = t := by
    intro x y hxy
    have h1 := ht x y
    rw [hMdef] at h1
    simpa [Matrix.one_apply_ne hxy] using h1
  have hdiag : -r = t := by
    have h1 := ht i i
    rw [hMdef] at h1
    simpa [adjMat_apply, G.adj_self] using h1
  rcases eq_or_ne t 0 with h0 | h0
  · exfalso
    have hA : G.adjMat = 0 := by
      ext x y
      rcases eq_or_ne x y with rfl | hxy
      · simp [adjMat_apply, G.adj_self]
      · rw [hoff x y hxy, h0, Matrix.zero_apply]
    have hk0 : (k : ℝ) = 0 := by
      have h1 : G.adjMat *ᵥ (1 : G.V → ℝ) = (k : ℝ) • 1 :=
        (hasEigenvector_one_of_isRegularWith hreg).2
      rw [hA] at h1
      simpa using (congrFun h1 (Classical.arbitrary G.V)).symm
    exact hkr (by rw [hk0]; linarith [hdiag.trans h0])
  · by_contra hn
    have h1 := hoff i j hij
    rw [adjMat_apply, if_neg hn] at h1
    exact h0 h1.symm

/-- **A connected regular graph with three distinct eigenvalues is strongly regular.**  Writing
the spectrum as `{k, r, s}`, the minimal polynomial gives `(A - k) (A - r) (A - s) = 0`, so every
column of `M = (A - r) (A - s)` is a `k`-eigenvector; as `k` is simple and `M` is symmetric,
`M` is a constant matrix `t J`.  Off the diagonal that reads
`#(common neighbours) = t + (r + s) · A`, which is one value on the edges and another off them.

This is the converse of `spectrum_isSRGWith`, and together with it says that strong regularity of
a connected regular graph is exactly the condition "three distinct eigenvalues". -/
@[toIsoGraph]
theorem exists_isSRGWith_of_card_toFinset_spectrum_eq_three {G : CGraph} {k : ℕ}
    (hconn : G.IsConnected) (hreg : G.IsRegularWith k)
    (h3 : G.spectrum.toFinset.card = 3) :
    ∃ l m : ℕ, G.IsSRGWith (Fintype.card G.V) k l m := by
  haveI : Nonempty G.V := hconn.nonempty
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.1 h3
  have hk : (k : ℝ) ∈ G.spectrum.toFinset := by
    simpa using mem_spectrum_of_isRegularWith hreg
  rw [hset] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  -- name the two eigenvalues other than the degree
  obtain ⟨r, s, hkr, hks, hrs, hspec⟩ :
      ∃ r s : ℝ, (k : ℝ) ≠ r ∧ (k : ℝ) ≠ s ∧ r ≠ s ∧
        G.spectrum.toFinset = {(k : ℝ), r, s} := by
    rcases hk with rfl | rfl | rfl
    · exact ⟨b, c, hab, hac, hbc, hset⟩
    · exact ⟨a, c, hab.symm, hbc, hac, by rw [hset]; ext x; simp; tauto⟩
    · exact ⟨a, b, hac.symm, hbc.symm, hab, by rw [hset]; ext x; simp; tauto⟩
  clear hset hab hac hbc hk
  -- the minimal polynomial factors, so `(A - k) (A - r) (A - s) = 0`
  have hpoly : G.minSpecPoly = (X - C (k : ℝ)) * ((X - C r) * (X - C s)) := by
    rw [minSpecPoly, hspec, Finset.prod_insert (by simp [hkr, hks]),
      Finset.prod_insert (by simp [hrs]), Finset.prod_singleton]
  have hann : (G.adjMat - (k : ℝ) • 1) *
      ((G.adjMat - r • 1) * (G.adjMat - s • 1)) = 0 := by
    have h1 := G.aeval_minSpecPoly
    rw [hpoly] at h1
    simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h1
    exact h1
  set M : Matrix G.V G.V ℝ := (G.adjMat - r • 1) * (G.adjMat - s • 1) with hMdef
  have hMeq : M = G.adjMat ^ 2 - (r + s) • G.adjMat + (r * s) • 1 := by
    rw [hMdef]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ← sq]
    module
  have hAM : G.adjMat * M = (k : ℝ) • M := by
    rw [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at hann
    exact hann
  have hAt : G.adjMatᵀ = G.adjMat := Matrix.ext fun i j ↦ adjMat_symm G j i
  have hsymm : ∀ i j, M i j = M j i := by
    have ht : Mᵀ = M := by
      rw [hMeq]
      simp [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
        Matrix.transpose_pow, hAt]
    intro i j
    exact (congrFun (congrFun ht i) j).symm
  obtain ⟨t, ht⟩ := exists_forall_eq_of_mul_eq_smul hconn hreg hsymm hAM
  -- off the diagonal the constant `t` pins down the two common-neighbour counts
  have hoff : ∀ i j, i ≠ j →
      (Fintype.card (G.toSimple.commonNeighbors i j) : ℝ) - (r + s) * G.adjMat i j = t := by
    intro i j hij
    have h1 := ht i j
    rw [hMeq] at h1
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hij, mul_zero, add_zero] at h1
    rwa [adjMat_sq_apply] at h1
  have hadj : ∀ i j, G.toSimple.Adj i j →
      (Fintype.card (G.toSimple.commonNeighbors i j) : ℝ) = t + (r + s) := by
    intro i j hij
    have h1 := hoff i j hij.ne
    rw [adjMat_apply, if_pos (by simpa [toSimple_adj] using hij)] at h1
    linarith
  have hnadj : ∀ i j, i ≠ j → ¬G.toSimple.Adj i j →
      (Fintype.card (G.toSimple.commonNeighbors i j) : ℝ) = t := by
    intro i j hij hnij
    have h1 := hoff i j hij
    rw [adjMat_apply, if_neg (by simpa [toSimple_adj] using hnij)] at h1
    linarith
  -- read off the two parameters as natural numbers
  obtain ⟨l, hl⟩ : ∃ l : ℕ, ∀ v w, G.toSimple.Adj v w →
      Fintype.card (G.toSimple.commonNeighbors v w) = l := by
    by_cases hex : ∃ v w, G.toSimple.Adj v w
    · obtain ⟨v0, w0, h0⟩ := hex
      refine ⟨Fintype.card (G.toSimple.commonNeighbors v0 w0), fun v w hvw ↦ ?_⟩
      exact_mod_cast (hadj v w hvw).trans (hadj v0 w0 h0).symm
    · push_neg at hex
      exact ⟨0, fun v w hvw ↦ absurd hvw (hex v w)⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v w, v ≠ w → ¬G.toSimple.Adj v w →
      Fintype.card (G.toSimple.commonNeighbors v w) = m := by
    by_cases hex : ∃ v w, v ≠ w ∧ ¬G.toSimple.Adj v w
    · obtain ⟨v0, w0, h0, h0'⟩ := hex
      refine ⟨Fintype.card (G.toSimple.commonNeighbors v0 w0), fun v w hvw hn ↦ ?_⟩
      exact_mod_cast (hnadj v w hvw hn).trans (hnadj v0 w0 h0 h0').symm
    · push_neg at hex
      exact ⟨0, fun v w hvw hn ↦ absurd (hex v w hvw) (by simpa using hn)⟩
  exact ⟨l, m, rfl, hreg, hl, fun v w hne hnadj ↦ hm v w hne hnadj⟩

/-- **A strongly regular graph has at most three distinct eigenvalues.**  Every eigenvalue other
than the degree is a root of `X ² - (ℓ - μ) X - (k - μ)`, and a quadratic has at most two. -/
@[toIsoGraph]
theorem card_toFinset_spectrum_le_three_of_isSRGWith {G : CGraph} {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) : G.spectrum.toFinset.card ≤ 3 := by
  set p : ℝ[X] := X ^ 2 - C ((l : ℝ) - m) * X - C ((k : ℝ) - m) with hp
  have hmon : p.Monic := by
    rw [hp]
    monicity!
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree!
  have hsub : G.spectrum.toFinset ⊆ insert (k : ℝ) p.roots.toFinset := by
    intro x hx
    rcases eq_or_ne x (k : ℝ) with rfl | hxk
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero]
      have hev : G.IsEigenvalue x := (G.mem_spectrum_iff x).1 (Multiset.mem_toFinset.1 hx)
      have hq := sq_eq_of_isSRGWith_of_ne h hxk hev
      simp only [hp, IsRoot.def, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
      linarith
  calc G.spectrum.toFinset.card ≤ (insert (k : ℝ) p.roots.toFinset).card :=
        Finset.card_le_card hsub
    _ ≤ p.roots.toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ Multiset.card p.roots + 1 := Nat.add_le_add_right (Multiset.toFinset_card_le _) 1
    _ ≤ p.natDegree + 1 := Nat.add_le_add_right p.card_roots' 1
    _ = 3 := by rw [hdeg]

/-- **A connected strongly regular graph that is not complete has exactly three distinct
eigenvalues.**  The upper bound is the quadratic; for the lower bound, two distinct non-adjacent
vertices are at distance at least `2`, and `dist_lt_card_toFinset_spectrum` does the rest. -/
theorem card_toFinset_spectrum_eq_three_of_isSRGWith {G : CGraph} {n k l m : ℕ}
    (hconn : G.IsConnected) (h : G.IsSRGWith n k l m) {i j : G.V} (hij : i ≠ j)
    (hnadj : G.Adj i j = false) : G.spectrum.toFinset.card = 3 := by
  haveI : Nonempty G.V := ⟨i⟩
  refine le_antisymm (card_toFinset_spectrum_le_three_of_isSRGWith h) ?_
  have h2 : 1 < G.toSimple.dist i j :=
    hconn.one_lt_dist_of_ne_of_not_adj hij (by simp [hnadj])
  have h3 := G.dist_lt_card_toFinset_spectrum i j
  omega

/-- **Strong regularity is determined by the spectrum.**  A graph cospectral with a connected,
non-complete strongly regular graph is itself strongly regular, of the same degree. -/
theorem Cospectral.exists_isSRGWith {G H : CGraph} (hc : G.Cospectral H) {n k l m : ℕ}
    (hconn : G.IsConnected) (h : G.IsSRGWith n k l m) {i j : G.V} (hij : i ≠ j)
    (hnadj : G.Adj i j = false) :
    ∃ l' m' : ℕ, H.IsSRGWith (Fintype.card H.V) k l' m' := by
  have hreg : G.IsRegularWith k := h.regular
  have hHreg : H.IsRegularWith k := CGraph.Cospectral.isRegularWith hc hreg
  have hHconn : H.IsConnected := CGraph.Cospectral.isConnected hc hreg hconn
  have h3 : H.spectrum.toFinset.card = 3 := by
    rw [← cospectral_iff_spectrum_eq.1 hc]
    exact card_toFinset_spectrum_eq_three_of_isSRGWith hconn h hij hnadj
  exact exists_isSRGWith_of_card_toFinset_spectrum_eq_three hHconn hHreg h3

/-! ## The energy of a graph -/

/-- The **energy** of a graph: the sum of the absolute values of its adjacency eigenvalues. -/
noncomputable def energy (G : CGraph) : ℝ := (G.spectrum.map (|·|)).sum

end CGraph

namespace IsoGraph

/-- The energy of an isomorphism class. -/
noncomputable def energy (G : IsoGraph) : ℝ := (G.spectrum.map (|·|)).sum

@[simp, isoTransfer] theorem energy_mk (G : CGraph) : energy ⟦G⟧ = G.energy := rfl

end IsoGraph

namespace CGraph

theorem energy_eq_sum (G : CGraph) : G.energy = ∑ i, |G.eigenvalues i| := by
  rw [energy, spectrum_eq_map, Multiset.map_map]
  rfl

@[toIsoGraph]
theorem energy_nonneg (G : CGraph) : 0 ≤ G.energy := by
  rw [energy_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _

private theorem sum_sq_eigenvalues (G : CGraph) : ∑ i, G.eigenvalues i ^ 2 = 2 * (G.E : ℝ) := by
  have h := G.sum_sq_spectrum
  rwa [spectrum_eq_map, Multiset.map_map, ← Finset.sum_eq_multiset_sum] at h

/-- **The positive eigenvalues carry exactly half the energy**, since all the eigenvalues sum to
zero. -/
theorem energy_eq_two_mul_sum_posPart (G : CGraph) :
    G.energy = 2 * ∑ i, max (G.eigenvalues i) 0 := by
  have h0 : ∑ i, G.eigenvalues i = 0 := by
    have := G.sum_spectrum
    rwa [spectrum_eq_map, ← Finset.sum_eq_multiset_sum] at this
  have hpt : ∀ i, |G.eigenvalues i| = 2 * max (G.eigenvalues i) 0 - G.eigenvalues i := by
    intro i
    rcases le_total 0 (G.eigenvalues i) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  rw [energy_eq_sum, Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h0, sub_zero]

/-- **The energy is at least twice the spectral radius**: the largest eigenvalue is one of the
positive ones, and those carry half the energy. -/
theorem two_mul_lambdaMax_le_energy (G : CGraph) [Nonempty G.V] : 2 * G.lambdaMax ≤ G.energy := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ.val, G.eigenvalues i = G.lambdaMax := by
    have h := G.lambdaMax_mem_spectrum
    rwa [spectrum_eq_map, Multiset.mem_map] at h
  rw [energy_eq_two_mul_sum_posPart]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc G.lambdaMax = max (G.eigenvalues i) 0 := by rw [hi, max_eq_left G.lambdaMax_nonneg]
    _ ≤ ∑ j, max (G.eigenvalues j) 0 :=
        Finset.single_le_sum (fun j _ ↦ le_max_right _ _) (Finset.mem_univ i)

/-- **McClelland's bound**: by Cauchy–Schwarz against `∑ λ ² = 2 |E|`, the energy is at most
`√(2 |E| n)`. -/
@[toIsoGraph]
theorem energy_le_sqrt (G : CGraph) :
    G.energy ≤ Real.sqrt (2 * G.E * Fintype.card G.V) := by
  have hsq : G.energy ^ 2 ≤ 2 * G.E * Fintype.card G.V := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset G.V))
      (f := fun i ↦ |G.eigenvalues i|)
    rw [← energy_eq_sum] at h
    simp only [sq_abs, Finset.card_univ] at h
    rw [sum_sq_eigenvalues] at h
    linarith
  exact (Real.le_sqrt (energy_nonneg G) (by positivity)).2 hsq

/-- **The energy is at least `2 √|E|`.**  Expanding `(∑ |λ|) ²` splits into the diagonal
`∑ λ ² = 2 |E|` and the off-diagonal sum of `|λ i λ j|`, which dominates
`|∑_{i ≠ j} λ i λ j| = |(∑ λ) ² - ∑ λ ²| = 2 |E|`; so the square of the energy is at least
`4 |E|`. -/
@[toIsoGraph]
theorem two_mul_sqrt_le_energy (G : CGraph) : 2 * Real.sqrt G.E ≤ G.energy := by
  have hsum0 : ∑ i, G.eigenvalues i = 0 := by
    have := G.sum_spectrum
    rwa [spectrum_eq_map, ← Finset.sum_eq_multiset_sum] at this
  set T : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, |G.eigenvalues i * G.eigenvalues j| with hT
  set A : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, G.eigenvalues i * G.eigenvalues j with hA
  have hsplit : G.energy ^ 2 = ∑ i, G.eigenvalues i ^ 2 + T := by
    rw [energy_eq_sum, sq, Finset.sum_mul_sum, hT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.add_sum_erase Finset.univ
      (fun j ↦ |G.eigenvalues i| * |G.eigenvalues j|) (Finset.mem_univ i)]
    congr 1
    · rw [abs_mul_abs_self, sq]
    · exact Finset.sum_congr rfl fun j _ ↦ (abs_mul _ _).symm
  have hAval : A = -(2 * (G.E : ℝ)) := by
    have h : ∑ i, ∑ j, G.eigenvalues i * G.eigenvalues j = 0 := by
      rw [← Finset.sum_mul_sum, hsum0, mul_zero]
    have h2 : ∑ i, ∑ j, G.eigenvalues i * G.eigenvalues j = ∑ i, G.eigenvalues i ^ 2 + A := by
      rw [hA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ G.eigenvalues i * G.eigenvalues j) (Finset.mem_univ i), sq]
    rw [h2, sum_sq_eigenvalues] at h
    linarith
  have hTA : |A| ≤ T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
  have key : 4 * (G.E : ℝ) ≤ G.energy ^ 2 := by
    rw [hsplit, sum_sq_eigenvalues]
    have hTge : 2 * (G.E : ℝ) ≤ T := by
      refine le_trans (le_of_eq ?_) hTA
      rw [hAval, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have h4 : Real.sqrt (4 * (G.E : ℝ)) = 2 * Real.sqrt G.E := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hle := Real.sqrt_le_sqrt key
  rwa [h4, Real.sqrt_sq (energy_nonneg G)] at hle

@[simp, toIsoGraph] theorem energy_disjUnion (G H : CGraph) :
    (disjUnion G H).energy = G.energy + H.energy := by
  rw [energy, energy, energy, spectrum_disjUnion, Multiset.map_add, Multiset.sum_add]

/-- **The energy is multiplicative over tensor products**, because the eigenvalues of `G ⊗ H` are
the products `λ μ` and `|λ μ| = |λ| |μ|`. -/
@[simp] theorem energy_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).energy = G.energy * H.energy := by
  have key : ∀ s t : Multiset ℝ, ((s ×ˢ t).map (fun p : ℝ × ℝ ↦ |p.1 * p.2|)).sum
      = (s.map (|·|)).sum * (t.map (|·|)).sum := by
    intro s t
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_map, add_mul]
      congr 1
      simp only [Function.comp_def, abs_mul]
      rw [Multiset.sum_map_mul_left]
  rw [energy, energy, energy, spectrum_tensorProduct', Multiset.map_map]
  exact key G.spectrum H.spectrum

/-- **The energy of a complete graph** is `2 (n - 1)`: the eigenvalues are `n - 1` and `-1`. -/
@[toIsoGraph]
theorem energy_complete (n : ℕ) : (complete (n + 1)).energy = 2 * n := by
  rw [energy, spectrum_complete]
  simp [Multiset.map_replicate, abs_of_nonneg, two_mul]

theorem Cospectral.energy_eq {G H : CGraph} (h : Cospectral G H) : G.energy = H.energy := by
  rw [energy, energy, h.spectrum_eq]

/-- **A graph has zero energy exactly when it has no edges**, since `∑ λ ² = 2 |E|`. -/
@[toIsoGraph]
theorem energy_eq_zero_iff (G : CGraph) : G.energy = 0 ↔ G.E = 0 := by
  have hsq := G.sum_sq_eigenvalues
  constructor
  · intro h
    rw [energy_eq_sum] at h
    have hz : ∀ i, G.eigenvalues i = 0 := fun i ↦ abs_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ abs_nonneg _).1 h i (Finset.mem_univ i))
    have h0 : (2 * G.E : ℝ) = 0 := by
      rw [← hsq]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [hz i]; ring
    have : (G.E : ℝ) = 0 := by linarith
    exact_mod_cast this
  · intro h
    rw [h, Nat.cast_zero, mul_zero] at hsq
    have hz : ∀ i, G.eigenvalues i = 0 := fun i ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (G.eigenvalues j)).1 hsq i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    rw [energy_eq_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [hz i, abs_zero]

@[simp] theorem energy_empty (n : ℕ) : (empty n).energy = 0 := by
  rw [energy, spectrum_empty]
  simp

/-- **The energy of a complete bipartite graph** is `2 √(m n)`. -/
theorem energy_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).energy = 2 * Real.sqrt ((m + 1) * (n + 1)) := by
  rw [energy, spectrum_bipartite]
  simp [abs_of_nonneg (Real.sqrt_nonneg (((m : ℝ) + 1) * ((n : ℝ) + 1)))]
  ring

/-- **The energy of a star** is `2 √n`. -/
theorem energy_star (n : ℕ) : (star (n + 1)).energy = 2 * Real.sqrt (n + 1) := by
  rw [energy, spectrum_star]
  simp [abs_of_nonneg (Real.sqrt_nonneg ((n : ℝ) + 1))]
  ring

/-- **The energy of the Petersen graph** is `16`: `3 + 5 · 1 + 4 · 2`. -/
theorem energy_petersen : SRG.petersen.energy = 16 := by
  rw [energy, spectrum_petersen]
  norm_num [Multiset.map_add, Multiset.map_replicate]

/-! ## The Laplacian -/

/-- The **Laplacian** of `G`: the degree matrix minus the adjacency matrix. -/
noncomputable def lapMat (G : CGraph) : Matrix G.V G.V ℝ := G.toSimple.lapMatrix ℝ

theorem lapMat_eq_diagonal_sub (G : CGraph) :
    G.lapMat = Matrix.diagonal (fun i ↦ (G.toSimple.degree i : ℝ)) - G.adjMat := rfl

theorem lapMat_apply_self (G : CGraph) (i : G.V) :
    G.lapMat i i = (G.toSimple.degree i : ℝ) := by
  rw [lapMat_eq_diagonal_sub]
  simp [adjMat_apply, G.adj_self]

theorem lapMat_apply_of_ne (G : CGraph) {i j : G.V} (hij : i ≠ j) :
    G.lapMat i j = -G.adjMat i j := by
  rw [lapMat_eq_diagonal_sub]
  simp [Matrix.diagonal_apply_ne _ hij]

theorem sum_adjMat_row_eq_degree (G : CGraph) (i : G.V) :
    ∑ j, G.adjMat i j = (G.toSimple.degree i : ℝ) := by
  have h1 : (G.adjMat *ᵥ (1 : G.V → ℝ)) i = (G.toSimple.degree i : ℝ) := by
    simp [adjMat, SimpleGraph.adjMatrix_mulVec_apply]
  simpa [Matrix.mulVec, dotProduct] using h1

theorem lapMat_mulVec_apply (G : CGraph) (v : G.V → ℝ) (i : G.V) :
    (G.lapMat *ᵥ v) i = (∑ j, G.adjMat i j) * v i - ∑ j, G.adjMat i j * v j := by
  rw [lapMat_eq_diagonal_sub, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
    sum_adjMat_row_eq_degree]
  simp [Matrix.mulVec, dotProduct]

theorem isHermitian_lapMat (G : CGraph) : G.lapMat.IsHermitian :=
  Matrix.ext fun i j ↦ by
    have h := G.toSimple.isSymm_lapMatrix (R := ℝ)
    exact congrFun (congrFun h i) j

theorem posSemidef_lapMat (G : CGraph) : G.lapMat.PosSemidef :=
  G.toSimple.posSemidef_lapMatrix ℝ

theorem lapMat_mulVec_one (G : CGraph) : G.lapMat *ᵥ (1 : G.V → ℝ) = 0 :=
  G.toSimple.lapMatrix_mulVec_const_eq_zero (R := ℝ)

/-- The characteristic polynomial of the Laplacian. -/
noncomputable def lapCharpoly (G : CGraph) : ℝ[X] := G.lapMat.charpoly

/-- The **Laplacian spectrum**: the multiset of eigenvalues of `L`, with multiplicity. -/
noncomputable def lapSpectrum (G : CGraph) : Multiset ℝ := G.lapCharpoly.roots

/-- The Laplacian eigenvalues, indexed by the vertices. -/
noncomputable def lapEigenvalues (G : CGraph) : G.V → ℝ := G.isHermitian_lapMat.eigenvalues

theorem lapMat_congr {G H : CGraph} (i : G ≃cg H) :
    G.lapMat = Matrix.reindex i.toEquiv.symm i.toEquiv.symm H.lapMat := by
  ext x y
  rcases eq_or_ne x y with rfl | hxy
  · rw [lapMat_apply_self, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      lapMat_apply_self]
    exact_mod_cast (SimpleGraph.Iso.degree_eq (CGraph.Iso.toSimpleIso i) x).symm
  · rw [lapMat_apply_of_ne _ hxy, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      lapMat_apply_of_ne _ (fun h ↦ hxy (i.toEquiv.injective h))]
    simp [adjMat_apply, i.adj_eq x y]

@[toIsoGraph]
theorem lapCharpoly_congr {G H : CGraph} (i : G ≃cg H) : G.lapCharpoly = H.lapCharpoly := by
  classical
  rw [lapCharpoly, lapCharpoly, lapMat_congr i]
  exact Matrix.charpoly_reindex _ _

@[toIsoGraph]
theorem lapSpectrum_congr {G H : CGraph} (i : G ≃cg H) : G.lapSpectrum = H.lapSpectrum := by
  rw [lapSpectrum, lapSpectrum, lapCharpoly_congr i]

theorem lapSpectrum_eq_map (G : CGraph) :
    G.lapSpectrum = Finset.univ.val.map G.lapEigenvalues := by
  simpa [lapSpectrum, lapCharpoly, Function.comp_def]
    using G.isHermitian_lapMat.roots_charpoly_eq_eigenvalues

@[simp, toIsoGraph] theorem card_lapSpectrum (G : CGraph) :
    Multiset.card G.lapSpectrum = Fintype.card G.V := by
  simp [lapSpectrum_eq_map, Finset.card_univ]

theorem mem_lapSpectrum_iff (G : CGraph) (x : ℝ) :
    x ∈ G.lapSpectrum ↔ ∃ v : G.V → ℝ, v ≠ 0 ∧ G.lapMat *ᵥ v = x • v := by
  have key : ∀ v : G.V → ℝ,
      (Matrix.scalar G.V x - G.lapMat) *ᵥ v = x • v - G.lapMat *ᵥ v := fun v ↦ by
    rw [Matrix.sub_mulVec, scalar_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [lapSpectrum, lapCharpoly, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero,
    Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h0⟩
    exact ⟨v, hv, by rw [key] at h0; linear_combination (norm := module) -h0⟩
  · rintro ⟨v, hv, h0⟩
    exact ⟨v, hv, by rw [key, h0, sub_self]⟩

/-- If at least `|V|` distinct reals are all Laplacian eigenvalues, they are exactly the Laplacian
spectrum. -/
theorem lapSpectrum_eq_of_card_le (G : CGraph) (s : Finset ℝ)
    (hcard : Fintype.card G.V ≤ s.card)
    (hs : ∀ x ∈ s, ∃ v : G.V → ℝ, v ≠ 0 ∧ G.lapMat *ᵥ v = x • v) :
    G.lapSpectrum = s.val := by
  refine (Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.2 fun x ↦ ?_)
    (by simpa using hcard)).symm
  by_cases hx : x ∈ s
  · exact le_trans (Multiset.nodup_iff_count_le_one.1 s.nodup x)
      (Multiset.one_le_count_iff_mem.2 ((mem_lapSpectrum_iff G x).2 (hs x hx)))
  · simp [Multiset.count_eq_zero_of_notMem (fun h ↦ hx (Finset.mem_def.mpr h))]

/-- **The Laplacian eigenvalues are nonnegative**: `L` is positive semidefinite. -/
@[toIsoGraph]
theorem nonneg_of_mem_lapSpectrum (G : CGraph) {x : ℝ} (hx : x ∈ G.lapSpectrum) : 0 ≤ x := by
  rw [lapSpectrum_eq_map, Multiset.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact G.posSemidef_lapMat.eigenvalues_nonneg i

/-- **Zero is always a Laplacian eigenvalue**, with the all-ones eigenvector. -/
theorem zero_mem_lapSpectrum (G : CGraph) [Nonempty G.V] : 0 ∈ G.lapSpectrum := by
  refine (G.mem_lapSpectrum_iff 0).2 ⟨1, ?_, by simpa using G.lapMat_mulVec_one⟩
  intro h
  simpa using congrFun h (Classical.arbitrary G.V)

theorem trace_lapMat (G : CGraph) : G.lapMat.trace = ∑ i, (G.toSimple.degree i : ℝ) :=
  Finset.sum_congr rfl fun i _ ↦ G.lapMat_apply_self i

/-- **The Laplacian eigenvalues sum to twice the number of edges**: the trace of `L` is the sum of
the degrees. -/
@[toIsoGraph]
theorem sum_lapSpectrum (G : CGraph) : G.lapSpectrum.sum = 2 * (G.E : ℝ) := by
  have h1 : G.lapSpectrum.sum = ∑ i, G.lapEigenvalues i := by rw [lapSpectrum_eq_map]; rfl
  have h2 : G.lapMat.trace = ∑ i, G.lapEigenvalues i := by
    simpa [lapEigenvalues] using G.isHermitian_lapMat.trace_eq_sum_eigenvalues
  have h3 : ∑ i, (G.toSimple.degree i : ℝ) = ((2 * G.E : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
    rfl
  rw [h1, ← h2, trace_lapMat, h3]
  push_cast
  ring

theorem lapMat_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.lapMat = (k : ℝ) • 1 - G.adjMat := by
  have hd : (fun i ↦ (G.toSimple.degree i : ℝ)) = fun _ : G.V ↦ (k : ℝ) :=
    funext fun i ↦ by rw [h i]
  rw [lapMat_eq_diagonal_sub, Matrix.smul_one_eq_diagonal, hd]

/-- **For a `k`-regular graph the Laplacian eigenvalues are `k` minus the adjacency
eigenvalues.** -/
theorem mem_lapSpectrum_iff_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) (x : ℝ) :
    x ∈ G.lapSpectrum ↔ ((k : ℝ) - x) ∈ G.spectrum := by
  rw [mem_lapSpectrum_iff, mem_spectrum_iff]
  have key : ∀ v : G.V → ℝ, G.lapMat *ᵥ v = x • v ↔ G.adjMat *ᵥ v = ((k : ℝ) - x) • v := by
    intro v
    rw [lapMat_of_isRegularWith h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    constructor <;> intro hv <;> linear_combination (norm := module) -hv
  exact ⟨fun ⟨v, hv, h0⟩ ↦ ⟨v, hv, (key v).1 h0⟩, fun ⟨v, hv, h0⟩ ↦ ⟨v, hv, (key v).2 h0⟩⟩

/-- The kernel of the Laplacian is the space of functions constant on components. -/
theorem lapMat_mulVec_eq_zero_iff (G : CGraph) {v : G.V → ℝ} :
    G.lapMat *ᵥ v = 0 ↔ ∀ i j : G.V, G.toSimple.Reachable i j → v i = v j :=
  G.toSimple.lapMatrix_mulVec_eq_zero_iff_forall_reachable

/-- **The multiplicity of `0` in the Laplacian spectrum is the number of components.** -/
@[toIsoGraph]
theorem count_zero_lapSpectrum (G : CGraph) : G.lapSpectrum.count 0 = G.numComponents := by
  classical
  have hnull : Module.finrank ℝ (LinearMap.ker G.lapMat.mulVecLin) = G.numComponents := by
    rw [numComponents, Nat.card_eq_fintype_card,
      SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
    congr 1
  have hrank : G.lapMat.rank + Module.finrank ℝ (LinearMap.ker G.lapMat.mulVecLin) =
      Fintype.card G.V := by
    rw [Matrix.rank, LinearMap.finrank_range_add_finrank_ker]
    simp
  have hne : G.lapMat.rank = (Finset.univ.filter fun i ↦ ¬ G.lapEigenvalues i = 0).card := by
    rw [G.isHermitian_lapMat.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rfl
  have hsplit : (Finset.univ.filter fun i ↦ G.lapEigenvalues i = 0).card +
      (Finset.univ.filter fun i ↦ ¬ G.lapEigenvalues i = 0).card = Fintype.card G.V := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hcount : G.lapSpectrum.count 0 =
      (Finset.univ.filter fun i ↦ G.lapEigenvalues i = 0).card := by
    rw [lapSpectrum_eq_map, Multiset.count_map]
    simp only [Finset.card, Finset.filter_val, eq_comm]
  omega

/-- **Connectedness is visible in the Laplacian spectrum**: `0` is a simple eigenvalue exactly
when the graph is connected. -/
theorem count_zero_lapSpectrum_eq_one_iff (G : CGraph) :
    G.lapSpectrum.count 0 = 1 ↔ G.IsConnected := by
  rw [count_zero_lapSpectrum, numComponents_eq_one_iff]

theorem monic_lapCharpoly (G : CGraph) : G.lapCharpoly.Monic := Matrix.charpoly_monic _

theorem lapCharpoly_eq_matrix_charpoly (G : CGraph) [inst : DecidableEq G.V] :
    G.lapCharpoly = G.lapMat.charpoly :=
  congrArg (fun d ↦ @Matrix.charpoly ℝ _ G.V d _ G.lapMat) (Subsingleton.elim _ _)

theorem degree_empty (n : ℕ) (i : (empty n).V) : (empty n).toSimple.degree i = 0 := by
  rw [SimpleGraph.degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  rw [SimpleGraph.mem_neighborFinset, toSimple_adj, empty_adj] at hj
  exact Bool.false_ne_true hj

@[simp] theorem lapMat_empty (n : ℕ) : (empty n).lapMat = 0 := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [lapMat_apply_self, degree_empty]
    simp
  · rw [lapMat_apply_of_ne _ hij]
    simp [adjMat_apply, empty_adj]

@[simp, toIsoGraph] theorem lapSpectrum_empty (n : ℕ) :
    (empty n).lapSpectrum = Multiset.replicate n 0 := by
  simp [lapSpectrum, lapCharpoly, Polynomial.roots_pow, Multiset.nsmul_singleton]

theorem lapMat_disjUnion (G H : CGraph) :
    (disjUnion G H).lapMat = Matrix.fromBlocks G.lapMat 0 0 H.lapMat := by
  ext x y
  simp only [lapMat_eq_diagonal_sub, Matrix.sub_apply, Matrix.diagonal_apply]
  cases x <;> cases y <;>
    simp only [degree_disjUnion_inl, degree_disjUnion_inr] <;>
    simp [adjMat_apply, disjUnion, Matrix.diagonal_apply]

@[simp] theorem lapCharpoly_disjUnion (G H : CGraph) :
    (disjUnion G H).lapCharpoly = G.lapCharpoly * H.lapCharpoly := by
  classical
  rw [lapCharpoly_eq_matrix_charpoly, lapMat_disjUnion, Matrix.charpoly_fromBlocks_zero₁₂,
    ← lapCharpoly_eq_matrix_charpoly, ← lapCharpoly_eq_matrix_charpoly]

/-- **The Laplacian spectrum of a disjoint union is the sum of the spectra.** -/
@[simp, toIsoGraph] theorem lapSpectrum_disjUnion (G H : CGraph) :
    (disjUnion G H).lapSpectrum = G.lapSpectrum + H.lapSpectrum := by
  rw [lapSpectrum, lapSpectrum, lapSpectrum, lapCharpoly_disjUnion, Polynomial.roots_mul
    (mul_ne_zero G.monic_lapCharpoly.ne_zero H.monic_lapCharpoly.ne_zero)]

/-- For a `k`-regular graph the Laplacian is `k • 1 - A`, so its characteristic polynomial is
the adjacency one with every eigenvalue `λ` replaced by `k - λ`. -/
theorem lapCharpoly_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.lapCharpoly = ∏ i, (X - C ((k : ℝ) - G.eigenvalues i)) := by
  classical
  have hA := G.isHermitian_adjMat
  have hd : (Matrix.diagonal fun i ↦ (k : ℝ) - G.eigenvalues i)
      = ((k : ℝ) • 1 : Matrix G.V G.V ℝ)
        - Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [eigenvalues]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hL : G.lapMat = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal fun i ↦ (k : ℝ) - G.eigenvalues i) := by
    rw [hd, map_sub, map_smul, map_one, ← hA.spectral_theorem, lapMat_of_isRegularWith h]
  rw [lapCharpoly_eq_matrix_charpoly, hL, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm,
    ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

/-- **The Laplacian spectrum of a `k`-regular graph is `k` minus its adjacency spectrum**,
with multiplicities. -/
@[toIsoGraph]
theorem lapSpectrum_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.lapSpectrum = G.spectrum.map (fun x ↦ (k : ℝ) - x) := by
  have hroot : ∀ i : G.V, (X - C ((k : ℝ) - G.eigenvalues i)).roots
      = {(k : ℝ) - G.eigenvalues i} := fun i ↦ Polynomial.roots_X_sub_C _
  rw [lapSpectrum, lapCharpoly_of_isRegularWith h, Polynomial.roots_prod]
  · simp only [hroot, Multiset.bind_singleton, spectrum_eq_map, Multiset.map_map,
      Function.comp_def]
  · exact Finset.prod_ne_zero_iff.2 fun i _ ↦ Polynomial.X_sub_C_ne_zero _

/-- The same statement read backwards: **the adjacency spectrum of a `k`-regular graph is `k`
minus its Laplacian spectrum**. -/
@[toIsoGraph]
theorem spectrum_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.spectrum = G.lapSpectrum.map (fun x ↦ (k : ℝ) - x) := by
  rw [lapSpectrum_of_isRegularWith h, Multiset.map_map]
  simp

theorem isRegularWith_empty (n : ℕ) : (empty n).IsRegularWith 0 := by
  intro v
  simp [SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet, empty,
    CGraph.toSimple]

/-- **The Laplacian spectrum of the complete graph** `K_{n+1}`: `0` once, and `n + 1` with
multiplicity `n`. -/
@[toIsoGraph]
theorem lapSpectrum_complete (n : ℕ) :
    (complete (n + 1)).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate n ((n : ℝ) + 1) := by
  rw [lapSpectrum_of_isRegularWith (isRegularWith_complete n), spectrum_complete,
    Multiset.map_cons, Multiset.map_replicate]
  norm_num

theorem lapCharpoly_eq_prod_of_conj {G : CGraph} {P Q : Matrix G.V G.V ℝ} {d : G.V → ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : G.lapMat * P = P * Matrix.diagonal d) :
    G.lapCharpoly = ∏ i, (X - C (d i)) := by
  have hA : G.lapMat = P * Matrix.diagonal d * Q := by
    calc G.lapMat = G.lapMat * (P * Q) := by rw [hPQ, mul_one]
      _ = G.lapMat * P * Q := by rw [mul_assoc]
      _ = P * Matrix.diagonal d * Q := by rw [h]
  rw [lapCharpoly, hA, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hQP, mul_one,
    Matrix.charpoly_diagonal]

theorem lapSpectrum_eq_of_conj {G : CGraph} {P Q : Matrix G.V G.V ℝ} {d : G.V → ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (h : G.lapMat * P = P * Matrix.diagonal d) :
    G.lapSpectrum = Finset.univ.val.map d := by
  rw [lapSpectrum, lapCharpoly_eq_prod_of_conj hPQ hQP h,
    show (∏ i, (X - C (d i))) = ((Finset.univ.val.map d).map (fun a ↦ X - C a)).prod from by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- The Laplacian, too, is orthogonally diagonalisable. -/
theorem exists_orthogonal_lap_diagonal (G : CGraph) :
    ∃ U : Matrix G.V G.V ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      Uᵀ * G.lapMat * U = Matrix.diagonal G.lapEigenvalues := by
  have hA := G.isHermitian_lapMat
  set U : Matrix G.V G.V ℝ := ↑hA.eigenvectorUnitary with hUdef
  have hU : U ∈ unitary (Matrix G.V G.V ℝ) := hA.eigenvectorUnitary.2
  have hst : Star.star U * G.lapMat * U = Matrix.diagonal G.lapEigenvalues := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    exact h
  have hstar : Star.star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hst
  refine ⟨U, ?_, ?_, hst⟩
  · rw [← hstar]; exact hU.1
  · rw [← hstar]; exact hU.2

/-- Every power of `L` is diagonalised by the same orthogonal matrix, so its trace is the sum of
the `n`-th powers of the Laplacian eigenvalues. -/
theorem trace_lapMat_pow (G : CGraph) (n : ℕ) :
    (G.lapMat ^ n).trace = ∑ i, G.lapEigenvalues i ^ n := by
  obtain ⟨U, hUU, hUU', hdiag⟩ := exists_orthogonal_lap_diagonal G
  set D : Matrix G.V G.V ℝ := Matrix.diagonal G.lapEigenvalues with hD
  have hA : G.lapMat = U * D * Uᵀ := by
    calc G.lapMat = (U * Uᵀ) * G.lapMat * (U * Uᵀ) := by rw [hUU', one_mul, mul_one]
      _ = U * (Uᵀ * G.lapMat * U) * Uᵀ := by simp only [mul_assoc]
      _ = U * D * Uᵀ := by rw [hdiag]
  have hpow : ∀ m : ℕ, G.lapMat ^ m = U * D ^ m * Uᵀ := by
    intro m
    induction m with
    | zero => simp [hUU']
    | succ m ih =>
      rw [pow_succ, ih, hA, pow_succ]
      calc U * D ^ m * Uᵀ * (U * D * Uᵀ) = U * D ^ m * (Uᵀ * U) * D * Uᵀ := by
            simp only [mul_assoc]
        _ = U * (D ^ m * D) * Uᵀ := by rw [hUU]; simp only [mul_assoc, mul_one]
  calc (G.lapMat ^ n).trace = (U * D ^ n * Uᵀ).trace := by rw [hpow]
    _ = (Uᵀ * (U * D ^ n)).trace := by rw [Matrix.trace_mul_comm]
    _ = (D ^ n).trace := by rw [← mul_assoc, hUU, one_mul]
    _ = ∑ i, G.lapEigenvalues i ^ n := by
        rw [hD, Matrix.diagonal_pow, Matrix.trace_diagonal]
        rfl

/-- **The moments of the Laplacian spectrum are the traces of the powers of `L`.** -/
theorem sum_pow_lapSpectrum (G : CGraph) (n : ℕ) :
    (G.lapSpectrum.map (· ^ n)).sum = (G.lapMat ^ n).trace := by
  rw [trace_lapMat_pow, lapSpectrum_eq_map, Multiset.map_map]
  simp only [Finset.sum, Function.comp_def]

/-- **The second moment of the Laplacian spectrum**: `∑ μ ² = 2 E + ∑ d (i) ²`.  The trace of
`L ²` is the trace of `D ²` plus the trace of `A ²`, the cross terms `D A` and `A D` having zero
diagonal because the graph is loopless. -/
theorem sum_sq_lapSpectrum (G : CGraph) :
    (G.lapSpectrum.map (· ^ 2)).sum
      = 2 * (G.E : ℝ) + ∑ i, (G.toSimple.degree i : ℝ) ^ 2 := by
  set D : Matrix G.V G.V ℝ := Matrix.diagonal (fun i ↦ (G.toSimple.degree i : ℝ)) with hD
  have hDA : (D * G.adjMat).trace = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Matrix.diag_apply, hD, Matrix.diagonal_mul]
    simp [adjMat_apply, G.adj_self]
  have hAD : (G.adjMat * D).trace = 0 := by
    rw [Matrix.trace_mul_comm]
    exact hDA
  have hDD : (D * D).trace = ∑ i, (G.toSimple.degree i : ℝ) ^ 2 := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  have hAA : (G.adjMat * G.adjMat).trace = 2 * (G.E : ℝ) := by
    rw [← pow_two, ← sum_pow_spectrum, ← sum_sq_spectrum]
  rw [sum_pow_lapSpectrum, pow_two, lapMat_eq_diagonal_sub, ← hD, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, hDA, hAD, hDD, hAA]
  ring

/-- **The Laplacians of a graph and of its complement add up to `n I - J`.** -/
theorem lapMat_compl (G : CGraph) [DecidableEq G.V] :
    (compl G).lapMat
      = (Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ) - Matrix.vecMulVec 1 1 - G.lapMat := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.one_apply, mul_one,
    smul_eq_mul]
  rcases eq_or_ne i j with rfl | hij
  · have hlt : G.toSimple.degree i < Fintype.card G.V := G.toSimple.degree_lt_card_verts i
    have h1 : 1 + G.toSimple.degree i ≤ Fintype.card G.V := by omega
    have hcast : ((Fintype.card G.V - 1 - G.toSimple.degree i : ℕ) : ℝ)
        = (Fintype.card G.V : ℝ) - 1 - G.toSimple.degree i := by
      rw [Nat.sub_sub, Nat.cast_sub h1]
      push_cast
      ring
    rw [lapMat_apply_self (compl G), lapMat_apply_self G, degree_compl, hcast]
    simp
  · rw [lapMat_apply_of_ne (compl G) hij, lapMat_apply_of_ne G hij, adjMat_compl]
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.one_apply, mul_one,
      Matrix.one_apply_ne hij]
    ring

/-- On a vector summing to zero — which is where all the non-constant Laplacian eigenvectors
live — the complement's Laplacian acts as `n` minus the graph's own. -/
theorem lapMat_compl_mulVec (G : CGraph) [DecidableEq G.V] {v : G.V → ℝ} (hv : ∑ i, v i = 0)
    {mu : ℝ} (hmu : G.lapMat *ᵥ v = mu • v) :
    (compl G).lapMat *ᵥ v = ((Fintype.card G.V : ℝ) - mu) • v := by
  rw [lapMat_compl, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    vecMulVec_one_mulVec hv, hmu]
  module

theorem isRegularWith_bipartite_self (n : ℕ) : (bipartite n n).IsRegularWith n := by
  have h := IsoGraph.isRegularWith_bipartite_self n
  rwa [IsoGraph.bipartite, IsoGraph.isRegularWith_mk] at h

/-- **The Laplacian spectrum of the complete bipartite graph** `K_{n+1,n+1}`: `0`, `2 (n + 1)`,
and `n + 1` with multiplicity `2 n`. -/
theorem lapSpectrum_bipartite_self (n : ℕ) :
    (bipartite (n + 1) (n + 1)).lapSpectrum
      = 0 ::ₘ ((2 * (n + 1) : ℝ) ::ₘ Multiset.replicate (2 * n) ((n : ℝ) + 1)) := by
  have hsq : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 1)) = (n : ℝ) + 1 :=
    Real.sqrt_mul_self (by positivity)
  rw [lapSpectrum_of_isRegularWith (isRegularWith_bipartite_self (n + 1)), spectrum_bipartite n n]
  push_cast
  rw [hsq, Multiset.map_cons, Multiset.map_cons, Multiset.map_replicate,
    show n + n = 2 * n from by ring]
  norm_num
  ring

/-- **The Laplacian spectrum of the complement of a connected graph.**  The eigenvalue `0` of the
constant vector stays `0`, and every other eigenvalue `μ` becomes `n - μ`. -/
theorem lapSpectrum_compl_of_isConnected {G : CGraph} [inst : DecidableEq G.V]
    (hconn : G.IsConnected) :
    (compl G).lapSpectrum
      = 0 ::ₘ (G.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x) := by
  obtain rfl : inst = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  haveI : Nonempty G.V := hconn.nonempty
  have hnpos : (0 : ℝ) < Fintype.card G.V := by exact_mod_cast Fintype.card_pos
  obtain ⟨U, hUU, hUU', hdiag⟩ := exists_orthogonal_lap_diagonal G
  have hAU : G.lapMat * U = U * Matrix.diagonal G.lapEigenvalues := by
    calc G.lapMat * U = (U * Uᵀ) * (G.lapMat * U) := by rw [hUU', one_mul]
      _ = U * (Uᵀ * G.lapMat * U) := by simp only [mul_assoc]
      _ = U * Matrix.diagonal G.lapEigenvalues := by rw [hdiag]
  -- the columns of `U` are the eigenvectors
  have hcol : ∀ i, G.lapMat *ᵥ (Uᵀ i) = G.lapEigenvalues i • (Uᵀ i) := by
    intro i
    funext x
    have h1 : (G.lapMat * U) x i = U x i * G.lapEigenvalues i := by
      rw [hAU, Matrix.mul_diagonal]
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h1
  have horth : ∀ i j, (Uᵀ i) ⬝ᵥ (Uᵀ j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : (Uᵀ * U) i j = (1 : Matrix G.V G.V ℝ) i j := by rw [hUU]
    rw [Matrix.one_apply] at h1
    simpa [Matrix.mul_apply, dotProduct] using h1
  -- on a connected graph a kernel vector of `L` is constant
  have hconstv : ∀ i, G.lapEigenvalues i = 0 → ∀ x y, U x i = U y i := by
    intro i hi x y
    have h0 : G.lapMat *ᵥ (Uᵀ i) = 0 := by rw [hcol i, hi, zero_smul]
    exact (G.lapMat_mulVec_eq_zero_iff.1 h0) x y (hconn.preconnected x y)
  set w : G.V → ℝ := fun i ↦ ∑ x, U x i with hw
  have hone : G.lapMat *ᵥ (fun _ ↦ (1 : ℝ)) = 0 := by simpa using G.lapMat_mulVec_one
  have hwvec : Uᵀ *ᵥ (fun _ ↦ (1 : ℝ)) = w := by
    funext i
    simp [Matrix.mulVec, dotProduct, hw]
  -- `w` is supported on the eigenvalue `0`
  have hzero : ∀ i, G.lapEigenvalues i ≠ 0 → w i = 0 := by
    intro i hi
    have h1 : Matrix.diagonal G.lapEigenvalues *ᵥ w = 0 := by
      rw [← hwvec, ← hdiag, Matrix.mulVec_mulVec, mul_assoc, mul_assoc, hUU', mul_one,
        ← Matrix.mulVec_mulVec, hone, Matrix.mulVec_zero]
    have h2 := congrFun h1 i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at h2
    exact (mul_eq_zero.1 h2).resolve_left hi
  -- some coordinate of `w` is nonzero
  have hwne : w ≠ 0 := by
    intro h0
    have h1 : U *ᵥ w = (fun _ ↦ (1 : ℝ)) := by
      rw [← hwvec, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 (Classical.arbitrary G.V)
    norm_num at h2
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hwne
  have hi₀0 : w i₀ ≠ 0 := by simpa using hi₀
  have hlam : G.lapEigenvalues i₀ = 0 := by
    by_contra hcon
    exact hi₀0 (hzero i₀ hcon)
  -- the constant value `c` of the column `i₀`
  obtain ⟨c, hc⟩ : ∃ c, ∀ x, U x i₀ = c :=
    ⟨U (Classical.arbitrary G.V) i₀, fun x ↦ hconstv i₀ hlam x _⟩
  have hwc : w i₀ = c * Fintype.card G.V := by
    rw [hw]
    simp [hc, Finset.card_univ, mul_comm]
  have hcsq : c ^ 2 * Fintype.card G.V = 1 := by
    have h1 := horth i₀ i₀
    rw [if_pos rfl] at h1
    simp only [dotProduct, Matrix.transpose_apply, hc, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    rw [← h1]
    ring
  have hwsq : w i₀ ^ 2 = Fintype.card G.V := by
    rw [hwc, show (c * Fintype.card G.V) ^ 2
      = (c ^ 2 * Fintype.card G.V) * Fintype.card G.V from by ring, hcsq, one_mul]
  -- every other coordinate of `w` vanishes
  have hwvanish : ∀ i, i ≠ i₀ → w i = 0 := by
    intro i hne
    by_cases hi : G.lapEigenvalues i = 0
    · obtain ⟨e, he⟩ : ∃ e, ∀ x, U x i = e :=
        ⟨U (Classical.arbitrary G.V) i, fun x ↦ hconstv i hi x _⟩
      have h1 := horth i i₀
      rw [if_neg hne] at h1
      simp only [dotProduct, Matrix.transpose_apply, he, hc, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at h1
      have hcne : c ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hwc
        exact hi₀0 hwc
      have he0 : e = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h (ne_of_gt hnpos)
        · rcases mul_eq_zero.1 h with h' | h'
          · exact h'
          · exact absurd h' hcne
      rw [hw]
      simp [he, he0]
    · exact hzero i hi
  -- conjugating the complement
  set d : G.V → ℝ := fun i ↦ (Fintype.card G.V : ℝ)
    - (if i = i₀ then (Fintype.card G.V : ℝ) else 0) - G.lapEigenvalues i with hdd
  have hJ : Uᵀ * (Matrix.vecMulVec (1 : G.V → ℝ) 1) * U = Matrix.vecMulVec w w := by
    ext i j
    have hrow : ∀ y : G.V, (Uᵀ * Matrix.vecMulVec (1 : G.V → ℝ) 1) i y = w i := fun y ↦ by
      simp [Matrix.mul_apply, hw]
    rw [Matrix.mul_apply]
    simp only [hrow, ← Finset.mul_sum, Matrix.vecMulVec_apply]
    simp [hw]
  have hvv : Matrix.vecMulVec w w
      = Matrix.diagonal (fun i ↦ if i = i₀ then (Fintype.card G.V : ℝ) else 0) := by
    ext i j
    rcases eq_or_ne i i₀ with hi | hi
    · rcases eq_or_ne j i₀ with hj | hj
      · subst hi
        subst hj
        simp [Matrix.vecMulVec_apply, Matrix.diagonal, ← sq, hwsq]
      · subst hi
        simp [Matrix.vecMulVec_apply, Matrix.diagonal, Ne.symm hj, hwvanish j hj]
    · simp [Matrix.vecMulVec_apply, Matrix.diagonal, hi, hwvanish i hi]
  have hNd : ((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ))
      = Matrix.diagonal (fun _ ↦ (Fintype.card G.V : ℝ)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  have hdsplit : Matrix.diagonal d
      = Matrix.diagonal (fun _ ↦ (Fintype.card G.V : ℝ))
        - Matrix.diagonal (fun i ↦ if i = i₀ then (Fintype.card G.V : ℝ) else 0)
        - Matrix.diagonal G.lapEigenvalues := by
    rw [hdd, ← Matrix.diagonal_sub, ← Matrix.diagonal_sub]
  have hfinal : Uᵀ * ((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ)
      - Matrix.vecMulVec (1 : G.V → ℝ) 1 - G.lapMat) * U = Matrix.diagonal d := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, hJ, hvv, hdiag,
      Matrix.mul_smul, mul_one, Matrix.smul_mul, hUU, hNd, hdsplit]
  have hcon2 : ((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ)
      - Matrix.vecMulVec (1 : G.V → ℝ) 1 - G.lapMat) * U = U * Matrix.diagonal d := by
    calc ((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ)
          - Matrix.vecMulVec (1 : G.V → ℝ) 1 - G.lapMat) * U
        = (U * Uᵀ) * (((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ)
            - Matrix.vecMulVec (1 : G.V → ℝ) 1 - G.lapMat) * U) := by rw [hUU', one_mul]
      _ = U * (Uᵀ * ((Fintype.card G.V : ℝ) • (1 : Matrix G.V G.V ℝ)
            - Matrix.vecMulVec (1 : G.V → ℝ) 1 - G.lapMat) * U) := by simp only [mul_assoc]
      _ = U * Matrix.diagonal d := by rw [hfinal]
  have hspec : (compl G).lapSpectrum = Finset.univ.val.map d :=
    lapSpectrum_eq_of_conj (G := compl G) (P := U) (Q := Uᵀ) (d := d) hUU' hUU
      (by rw [lapMat_compl]; exact hcon2)
  -- unpacking the two multisets
  have hmem : i₀ ∈ (Finset.univ : Finset G.V).val := Finset.mem_univ i₀
  have hsplit : (Finset.univ : Finset G.V).val = i₀ ::ₘ (Finset.univ : Finset G.V).val.erase i₀ :=
    (Multiset.cons_erase hmem).symm
  have hnodup : i₀ ∉ (Finset.univ : Finset G.V).val.erase i₀ := fun h ↦ by
    have hnd := Finset.univ.nodup (α := G.V)
    rw [hsplit] at hnd
    exact (Multiset.nodup_cons.1 hnd).1 h
  have hspecG : G.lapSpectrum.erase 0
      = ((Finset.univ : Finset G.V).val.erase i₀).map G.lapEigenvalues := by
    rw [lapSpectrum_eq_map]
    conv_lhs => rw [hsplit]
    rw [Multiset.map_cons, hlam, Multiset.erase_cons_head]
  rw [hspec, hspecG, Multiset.map_map]
  conv_lhs => rw [hsplit]
  rw [Multiset.map_cons]
  congr 1
  · simp [hdd, hlam]
  · refine Multiset.map_congr rfl fun i hi ↦ ?_
    have hne : i ≠ i₀ := fun h ↦ hnodup (h ▸ hi)
    simp [hdd, hne]

/-- The complement identity the other way round: a connected graph's Laplacian spectrum is
recovered from its complement's. -/
theorem lapSpectrum_eq_of_compl {G : CGraph} [DecidableEq G.V] (hconn : G.IsConnected) :
    G.lapSpectrum
      = 0 ::ₘ ((compl G).lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x) := by
  haveI : Nonempty G.V := hconn.nonempty
  have h := lapSpectrum_compl_of_isConnected (G := G) hconn
  rw [h, Multiset.erase_cons_head, Multiset.map_map]
  rw [show ((fun x ↦ (Fintype.card G.V : ℝ) - x) ∘ fun x ↦ (Fintype.card G.V : ℝ) - x) = id from
    funext fun x ↦ by simp, Multiset.map_id]
  exact (Multiset.cons_erase G.zero_mem_lapSpectrum).symm

/-- **The Laplacian spectrum of the complement**, with no hypothesis at all: a graph and its
complement cannot both be disconnected. -/
theorem lapSpectrum_compl (G : CGraph) [DecidableEq G.V] [Nonempty G.V] :
    (compl G).lapSpectrum
      = 0 ::ₘ (G.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x) := by
  by_cases hpre : G.toSimple.Preconnected
  · exact lapSpectrum_compl_of_isConnected ⟨hpre⟩
  · haveI : Nonempty (compl G).V := ‹Nonempty G.V›
    have hc : (compl G).IsConnected := G.isConnected_compl_of_not_preconnected hpre
    have h := lapSpectrum_eq_of_compl (G := compl G) hc
    rw [compl_compl, card_compl] at h
    exact h

/-- **The Laplacian spectrum of the complete bipartite graph** `K_{m+1,n+1}`: `0`, `m + n + 2`,
`n + 1` with multiplicity `m`, and `m + 1` with multiplicity `n`. -/
@[toIsoGraph]
theorem lapSpectrum_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).lapSpectrum
      = 0 ::ₘ (((m : ℝ) + (n : ℝ) + 2)
          ::ₘ (Multiset.replicate m ((n : ℝ) + 1) + Multiset.replicate n ((m : ℝ) + 1))) := by
  classical
  have hcompl : compl (bipartite (m + 1) (n + 1))
      = disjUnion (complete (m + 1)) (complete (n + 1)) := by
    simp [bipartite]
  have hcard : Fintype.card (bipartite (m + 1) (n + 1)).V = m + 1 + (n + 1) :=
    card_bipartite _ _
  rw [lapSpectrum_eq_of_compl (isConnected_bipartite m n), hcard, hcompl,
    lapSpectrum_disjUnion, lapSpectrum_complete, lapSpectrum_complete]
  rw [show (0 : ℝ) ::ₘ Multiset.replicate m ((m : ℝ) + 1)
      + (0 : ℝ) ::ₘ Multiset.replicate n ((n : ℝ) + 1)
      = 0 ::ₘ (Multiset.replicate m ((m : ℝ) + 1)
        + (0 : ℝ) ::ₘ Multiset.replicate n ((n : ℝ) + 1)) from by
    rw [Multiset.cons_add]]
  rw [Multiset.erase_cons_head, Multiset.map_add, Multiset.map_cons, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.add_cons]
  push_cast
  congr 2
  · ring
  · congr 1
    · congr 1
      ring
    · congr 1
      ring

/-- **The Laplacian spectrum of the star** `K₁,ₙ₊₁`: `0`, `n + 2`, and `1` with multiplicity `n`.
The star is not regular, so this does not come from `lapSpectrum_of_isRegularWith`; it is the
`m = 0` case of `lapSpectrum_bipartite`. -/
@[toIsoGraph]
theorem lapSpectrum_star (n : ℕ) :
    (star (n + 1)).lapSpectrum = 0 ::ₘ (((n : ℝ) + 2) ::ₘ Multiset.replicate n 1) := by
  have h := lapSpectrum_bipartite 0 n
  norm_num at h
  rw [star]
  exact h

/-- **The Laplacian spectrum of a join**: `0`, the order `n + m`, and every other eigenvalue of
each factor shifted by the order of the other factor. -/
theorem lapSpectrum_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (join G H).lapSpectrum
      = 0 ::ₘ (((Fintype.card G.V : ℝ) + Fintype.card H.V)
          ::ₘ ((G.lapSpectrum.erase 0).map (fun x ↦ x + (Fintype.card H.V : ℝ))
             + (H.lapSpectrum.erase 0).map (fun x ↦ x + (Fintype.card G.V : ℝ)))) := by
  haveI : Nonempty (disjUnion (compl G) (compl H)).V := ⟨Sum.inl (Classical.arbitrary G.V)⟩
  have hK := lapSpectrum_compl (disjUnion (compl G) (compl H))
  rw [lapSpectrum_disjUnion, lapSpectrum_compl G, lapSpectrum_compl H, card_disjUnion, card_compl,
    card_compl] at hK
  rw [join, hK]
  rw [show (0 : ℝ) ::ₘ (G.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x)
      + (0 : ℝ) ::ₘ (H.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card H.V : ℝ) - x)
      = 0 ::ₘ (0 ::ₘ ((G.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x)
          + (H.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card H.V : ℝ) - x))) from by
    rw [Multiset.cons_add, Multiset.add_cons]]
  rw [Multiset.erase_cons_head, Multiset.map_cons, Multiset.map_add, Multiset.map_map,
    Multiset.map_map]
  simp only [Function.comp_def]
  congr 1
  congr 1
  · push_cast
    ring
  · congr 1
    · exact Multiset.map_congr rfl fun x _ ↦ by push_cast; ring
    · exact Multiset.map_congr rfl fun x _ ↦ by push_cast; ring

/-- **The adjacency spectrum of a regular join**.  If `G` is `k`-regular on `n` vertices and `H`
is `l`-regular on `m` vertices with `k + m = n + l`, so that `G ∇ H` is regular of that common
degree, then the join has that degree as an eigenvalue, `k - n` as a second one, and keeps every
*other* eigenvalue of each factor unchanged. -/
theorem spectrum_join_of_isRegularWith {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] {k l m : ℕ} (hG : G.IsRegularWith k) (hH : H.IsRegularWith l)
    (h1 : k + Fintype.card H.V = m) (h2 : Fintype.card G.V + l = m) :
    (join G H).spectrum
      = (m : ℝ) ::ₘ (((k : ℝ) - Fintype.card G.V)
          ::ₘ (G.spectrum.erase (k : ℝ) + H.spectrum.erase (l : ℝ))) := by
  have hinj : Function.Injective (fun x : ℝ ↦ (k : ℝ) - x) := fun a b hab ↦ by
    simpa using hab
  have hinj' : Function.Injective (fun x : ℝ ↦ (l : ℝ) - x) := fun a b hab ↦ by
    simpa using hab
  have hGe : G.lapSpectrum.erase 0 = (G.spectrum.erase (k : ℝ)).map (fun x ↦ (k : ℝ) - x) := by
    rw [lapSpectrum_of_isRegularWith hG, Multiset.map_erase _ hinj]
    simp
  have hHe : H.lapSpectrum.erase 0 = (H.spectrum.erase (l : ℝ)).map (fun x ↦ (l : ℝ) - x) := by
    rw [lapSpectrum_of_isRegularWith hH, Multiset.map_erase _ hinj']
    simp
  have hhead : (m : ℝ) - ((Fintype.card G.V : ℝ) + Fintype.card H.V)
      = (k : ℝ) - Fintype.card G.V := by
    rw [← h1]; push_cast; ring
  have hk : ∀ x : ℝ, (m : ℝ) - ((k : ℝ) - x + (Fintype.card H.V : ℝ)) = x := fun x ↦ by
    rw [← h1]; push_cast; ring
  have hl : ∀ x : ℝ, (m : ℝ) - ((l : ℝ) - x + (Fintype.card G.V : ℝ)) = x := fun x ↦ by
    rw [← h2]; push_cast; ring
  rw [spectrum_of_isRegularWith (hG.join hH h1 h2), lapSpectrum_join, hGe, hHe]
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_add, Multiset.map_map, Multiset.map_map,
    Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, sub_zero, hhead, hk, hl, Multiset.map_id']

/-- The adjacency matrix of the path acting on a vector coming from a function on `ℕ`, with no
boundary condition: the missing neighbour at each end simply contributes nothing. -/
theorem path_adjMat_mulVec' (n : ℕ) (g : ℕ → ℝ) (i : Fin n) :
    ((path n).adjMat *ᵥ fun j : Fin n ↦ g (j.1 + 1)) i
      = (if i.1 = 0 then 0 else g i.1) + (if i.1 + 2 = n + 1 then 0 else g (i.1 + 2)) := by
  have hi := i.isLt
  set f : ℕ → ℝ := fun k ↦ if k = 0 then 0 else if k = n + 1 then 0 else g k with hf
  have h0 : f 0 = 0 := by simp [hf]
  have hn : f (n + 1) = 0 := by simp [hf]
  have hv : (fun j : Fin n ↦ g (j.1 + 1)) = fun j : Fin n ↦ f (j.1 + 1) := by
    funext j
    have hj := j.isLt
    rw [hf]
    simp only
    rw [if_neg (by omega), if_neg (by omega)]
  rw [hv, path_adjMat_mulVec n f h0 hn i]
  have hleft : f i.1 = if i.1 = 0 then 0 else g i.1 := by
    rw [hf]
    simp only
    split_ifs <;> first | rfl | omega
  have hright : f (i.1 + 2) = if i.1 + 2 = n + 1 then 0 else g (i.1 + 2) := by
    rw [hf]
    simp only
    rw [if_neg (show i.1 + 2 ≠ 0 by omega)]
  rw [hleft, hright]

/-- The Laplacian of the path acts as the second difference, provided the function is extended
past the two ends by reflection: `g 0 = g 1` and `g (n + 1) = g n`. -/
theorem path_lapMat_mulVec (n : ℕ) (g : ℕ → ℝ) (h0 : g 0 = g 1) (hn : g (n + 1) = g n)
    (i : Fin n) :
    ((path n).lapMat *ᵥ fun j : Fin n ↦ g (j.1 + 1)) i
      = 2 * g (i.1 + 1) - g i.1 - g (i.1 + 2) := by
  have hi := i.isLt
  have hrow := path_adjMat_mulVec' n (fun _ ↦ (1 : ℝ)) i
  have hsum : ∑ j, (path n).adjMat i j
      = (if i.1 = 0 then 0 else (1 : ℝ)) + (if i.1 + 2 = n + 1 then 0 else 1) := by
    rw [← hrow]
    simp [Matrix.mulVec, dotProduct]
  have hdot : ∑ j, (path n).adjMat i j * g (j.1 + 1)
      = (if i.1 = 0 then 0 else g i.1) + (if i.1 + 2 = n + 1 then 0 else g (i.1 + 2)) := by
    rw [← path_adjMat_mulVec' n g i]
    simp [Matrix.mulVec, dotProduct]
  rw [lapMat_mulVec_apply, hsum, hdot]
  rcases Nat.eq_zero_or_pos i.1 with hi0 | hi0
  · rcases eq_or_ne (i.1 + 2) (n + 1) with h2 | h2
    · rw [if_pos hi0, if_pos h2, if_pos hi0, if_pos h2]
      have e1 : g i.1 = g 1 := by rw [hi0, h0]
      have e2 : g (i.1 + 2) = g (i.1 + 1) := by
        rw [show i.1 + 2 = n + 1 from h2, hn]
        congr 1
        omega
      rw [e1, e2, show i.1 + 1 = 1 from by omega]
      ring
    · rw [if_pos hi0, if_neg h2, if_pos hi0, if_neg h2]
      have e1 : g i.1 = g (i.1 + 1) := by rw [hi0, h0]
      rw [e1]
      ring
  · rcases eq_or_ne (i.1 + 2) (n + 1) with h2 | h2
    · rw [if_neg (by omega), if_pos h2, if_neg (by omega), if_pos h2]
      have e2 : g (i.1 + 2) = g (i.1 + 1) := by
        rw [show i.1 + 2 = n + 1 from h2, hn]
        congr 1
        omega
      rw [e2]
      ring
    · rw [if_neg (by omega), if_neg h2, if_neg (by omega), if_neg h2]
      ring

open Real in
/-- The `m`-th Laplacian eigenvector of the path on `n` vertices, `cos (π m (j + 1/2) / n)`, with
eigenvalue `2 - 2 cos (π m / n)`. -/
theorem hasLapEigenvector_path (n : ℕ) (m : Fin n) :
    (fun j : Fin n ↦ Real.cos (π * m.1 / n * ((j.1 : ℝ) + 1 - 1 / 2))) ≠ 0 ∧
      (path n).lapMat *ᵥ (fun j : Fin n ↦ Real.cos (π * m.1 / n * ((j.1 : ℝ) + 1 - 1 / 2)))
        = (2 - 2 * Real.cos (π * m.1 / n))
          • fun j : Fin n ↦ Real.cos (π * m.1 / n * ((j.1 : ℝ) + 1 - 1 / 2)) := by
  have hn0 : 0 < n := m.pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set a : ℝ := π * m.1 / n with ha
  set g : ℕ → ℝ := fun k ↦ Real.cos (a * ((k : ℝ) - 1 / 2)) with hg
  have hanonneg : 0 ≤ a := by rw [ha]; positivity
  have haltpi : a < π := by
    have h1 : (m.1 : ℝ) < (n : ℝ) := by exact_mod_cast m.isLt
    rw [ha, div_lt_iff₀ hnR]
    nlinarith [Real.pi_pos]
  have hg01 : g 0 = g 1 := by
    rw [hg]
    simp only [Nat.cast_zero, Nat.cast_one, zero_sub]
    rw [show a * -(1 / 2 : ℝ) = -(a * (1 - 1 / 2)) from by ring, Real.cos_neg]
  have hgn : g (n + 1) = g n := by
    have hkey : Real.cos (a * ((n : ℝ) + 1 - 1 / 2)) - Real.cos (a * ((n : ℝ) - 1 / 2))
        = -2 * Real.sin (a * n) * Real.sin (a * (1 / 2)) := by
      rw [Real.cos_sub_cos]
      ring_nf
    have hsin : Real.sin (a * n) = 0 := by
      have : a * n = (m.1 : ℝ) * π := by rw [ha]; field_simp
      rw [this, Real.sin_nat_mul_pi]
    rw [hg]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [hkey, hsin, mul_eq_zero_of_left (mul_eq_zero_of_right (-2 : ℝ) hsin)
      (Real.sin (a * (1 / 2)))]
  have hvec : (fun j : Fin n ↦ Real.cos (a * ((j.1 : ℝ) + 1 - 1 / 2)))
      = fun j : Fin n ↦ g (j.1 + 1) := by
    funext j
    rw [hg]
    push_cast
    ring_nf
  constructor
  · intro h0
    have hzero := congrFun h0 (⟨0, hn0⟩ : Fin n)
    simp only [Pi.zero_apply] at hzero
    rw [show ((⟨0, hn0⟩ : Fin n).1 : ℝ) + 1 - 1 / 2 = 1 / 2 from by norm_num] at hzero
    have hpos : 0 < Real.cos (a * (1 / 2)) := by
      refine Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rw [hvec]
    funext i
    rw [path_lapMat_mulVec n g hg01 hgn i]
    have hcos : g i.1 + g (i.1 + 2) = 2 * Real.cos a * g (i.1 + 1) := by
      rw [hg]
      simp only
      push_cast
      rw [show a * ((i.1 : ℝ) - 1 / 2) = a * ((i.1 : ℝ) + 1 - 1 / 2) - a from by ring,
        show a * ((i.1 : ℝ) + 2 - 1 / 2) = a * ((i.1 : ℝ) + 1 - 1 / 2) + a from by ring,
        Real.cos_sub, Real.cos_add]
      ring
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [hcos]

/-- **The Laplacian spectrum of the path** `P_n`: the `n` numbers `2 - 2 cos (π m / n)`,
`0 ≤ m < n`.  The path is not regular, so this does not follow from `spectrum_path`; the
eigenvectors are the discrete cosines `cos (π m (j + 1/2) / n)`, which satisfy the reflecting
boundary condition the Laplacian imposes at the two ends. -/
@[toIsoGraph]
theorem lapSpectrum_path (n : ℕ) :
    (path n).lapSpectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 - 2 * Real.cos (Real.pi * m.1 / n)) := by
  classical
  set f : Fin n → ℝ := fun m ↦ 2 - 2 * Real.cos (Real.pi * m.1 / n) with hf
  have hinj : Function.Injective f := by
    intro m m' h
    rw [hf] at h
    simp only [sub_right_inj] at h
    have hn0 : 0 < n := m.pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hmem : ∀ k : Fin n, Real.pi * k.1 / n ∈ Set.Icc 0 Real.pi := by
      intro k
      refine ⟨by positivity, ?_⟩
      have h1 : (k.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast k.isLt.le
      rw [div_le_iff₀ hnR]
      nlinarith [Real.pi_pos]
    have hcos := mul_left_cancel₀ (two_ne_zero) h
    have harg := Real.injOn_cos (hmem m) (hmem m') hcos
    have h3 : Real.pi * (m.1 : ℝ) = Real.pi * (m'.1 : ℝ) := by
      have := congrArg (fun t : ℝ ↦ t * (n : ℝ)) harg
      simpa [div_mul_cancel₀, ne_of_gt hnR] using this
    exact Fin.ext (by exact_mod_cast mul_left_cancel₀ Real.pi_ne_zero h3)
  have hcard : Fintype.card (path n).V ≤ (Finset.image f Finset.univ).card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [path, ofRel]
  have hs : ∀ x ∈ Finset.image f Finset.univ,
      ∃ v : (path n).V → ℝ, v ≠ 0 ∧ (path n).lapMat *ᵥ v = x • v := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨_, hasLapEigenvector_path n m⟩
  rw [lapSpectrum_eq_of_card_le _ _ hcard hs, Finset.image_val_of_injOn hinj.injOn]

/-- **Every Laplacian eigenvalue is at most twice the maximum degree.**  Evaluate the
eigenvector equation at a coordinate where `|v|` is largest, as for `abs_le_maxDeg_of_mem_spectrum`
in the adjacency case. -/
@[toIsoGraph]
theorem le_two_mul_maxDeg_of_mem_lapSpectrum {G : CGraph} {x : ℝ} (hx : x ∈ G.lapSpectrum) :
    x ≤ 2 * (G.maxDeg : ℝ) := by
  classical
  obtain ⟨u, hu0, hu⟩ := (G.mem_lapSpectrum_iff x).1 hx
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hu0
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G.V) (fun i ↦ |u i|) ⟨i₀, Finset.mem_univ i₀⟩
  have hup : 0 < |u p| := lt_of_lt_of_le (abs_pos.2 hi₀) (hp i₀ (Finset.mem_univ i₀))
  set d : ℝ := (G.toSimple.degree p : ℝ) with hd
  have hrow : ∑ j, G.adjMat p j = d := G.sum_adjMat_row_eq_degree p
  have hL : (G.lapMat *ᵥ u) p = d * u p - ∑ j, G.adjMat p j * u j := by
    rw [G.lapMat_mulVec_apply u p, hrow]
  have e : (x - d) * u p = -∑ j, G.adjMat p j * u j := by
    have h2 : (G.lapMat *ᵥ u) p = x * u p := by rw [hu]; simp
    rw [hL] at h2
    linarith
  have key : |x - d| * |u p| ≤ d * |u p| := by
    calc |x - d| * |u p| = |(x - d) * u p| := (abs_mul _ _).symm
      _ = |∑ j, G.adjMat p j * u j| := by rw [e, abs_neg]
      _ ≤ ∑ j, |G.adjMat p j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, G.adjMat p j * |u j| := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [abs_mul, abs_of_nonneg (G.adjMat_nonneg p j)]
      _ ≤ ∑ j, G.adjMat p j * |u p| :=
            Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (hp j (Finset.mem_univ j)) (G.adjMat_nonneg p j)
      _ = d * |u p| := by rw [← Finset.sum_mul, hrow]
  have habs : |x - d| ≤ d := le_of_mul_le_mul_right key hup
  have hdle : d ≤ (G.maxDeg : ℝ) := by
    rw [hd]
    exact_mod_cast G.toSimple.degree_le_maxDegree p
  have := (abs_le.1 habs).2
  linarith

/-- A Laplacian eigenvector for a nonzero eigenvalue sums to zero: it is orthogonal to the
all-ones vector, which spans the kernel direction the Laplacian always has. -/
theorem sum_eq_zero_of_lapMat_mulVec {G : CGraph} {v : G.V → ℝ} {x : ℝ} (hx : x ≠ 0)
    (h : G.lapMat *ᵥ v = x • v) : ∑ i, v i = 0 := by
  have hsymm : G.lapMatᵀ = G.lapMat := G.toSimple.isSymm_lapMatrix (R := ℝ)
  have hvm : (1 : G.V → ℝ) ᵥ* G.lapMat = 0 := by
    rw [← Matrix.mulVec_transpose, hsymm, G.lapMat_mulVec_one]
  have h1 : (1 : G.V → ℝ) ⬝ᵥ (G.lapMat *ᵥ v) = 0 := by
    rw [Matrix.dotProduct_mulVec, hvm, zero_dotProduct]
  rw [h] at h1
  have h2 : x * ∑ i, v i = 0 := by simpa [dotProduct, Finset.mul_sum] using h1
  exact (mul_eq_zero.1 h2).resolve_left hx

/-- **Every Laplacian eigenvalue is at most the number of vertices**, the sharp bound, attained
by the complete graph.  On an eigenvector for `x ≠ 0` — which sums to zero — the complement's
Laplacian acts as `n - x`, and that is nonnegative. -/
theorem le_card_of_mem_lapSpectrum (G : CGraph) [DecidableEq G.V] {x : ℝ}
    (hx : x ∈ G.lapSpectrum) : x ≤ Fintype.card G.V := by
  rcases eq_or_ne x 0 with rfl | hx0
  · positivity
  obtain ⟨v, hv0, hv⟩ := (G.mem_lapSpectrum_iff x).1 hx
  have hsum : ∑ i, v i = 0 := sum_eq_zero_of_lapMat_mulVec hx0 hv
  have hmem : ((Fintype.card G.V : ℝ) - x) ∈ (compl G).lapSpectrum :=
    ((compl G).mem_lapSpectrum_iff _).2 ⟨v, hv0, G.lapMat_compl_mulVec hsum hv⟩
  have := (compl G).nonneg_of_mem_lapSpectrum hmem
  linarith

/-! ### Algebraic connectivity -/

/-- **Algebraic connectivity**, the Fiedler value: the second-smallest Laplacian eigenvalue, that
is the smallest one left after discarding the copy of `0` that every nonempty graph has.  On the
empty and the one-vertex graph nothing is left, and `sInf ∅ = 0` gives the usual convention. -/
noncomputable def algConn (G : CGraph) : ℝ := sInf {x : ℝ | x ∈ G.lapSpectrum.erase 0}

end CGraph

namespace IsoGraph

/-- **Algebraic connectivity** of an isomorphism class: the second-smallest Laplacian
eigenvalue. -/
noncomputable def algConn (G : IsoGraph) : ℝ := sInf {x : ℝ | x ∈ G.lapSpectrum.erase 0}

@[simp, isoTransfer] theorem algConn_mk (G : CGraph) : algConn ⟦G⟧ = G.algConn := rfl

end IsoGraph

namespace CGraph

@[toIsoGraph]
theorem algConn_nonneg (G : CGraph) : 0 ≤ G.algConn :=
  Real.sInf_nonneg fun _ hx ↦ G.nonneg_of_mem_lapSpectrum (Multiset.mem_of_mem_erase hx)

@[toIsoGraph]
theorem algConn_le {G : CGraph} {x : ℝ} (hx : x ∈ G.lapSpectrum.erase 0) : G.algConn ≤ x :=
  csInf_le (Multiset.finite_toSet _).bddBelow hx

/-- On two or more vertices the algebraic connectivity really is attained: it is a Laplacian
eigenvalue. -/
@[toIsoGraph]
theorem algConn_mem_erase (G : CGraph) (h : 2 ≤ Fintype.card G.V) :
    G.algConn ∈ G.lapSpectrum.erase 0 := by
  haveI : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  have hcard : Multiset.card (G.lapSpectrum.erase 0) = Fintype.card G.V - 1 := by
    rw [Multiset.card_erase_of_mem G.zero_mem_lapSpectrum, card_lapSpectrum]
    rfl
  have hpos : 0 < Multiset.card (G.lapSpectrum.erase 0) := by omega
  obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  exact Set.Nonempty.csInf_mem ⟨y, hy⟩ (Multiset.finite_toSet _)

@[toIsoGraph]
theorem algConn_mem_lapSpectrum (G : CGraph) (h : 2 ≤ Fintype.card G.V) :
    G.algConn ∈ G.lapSpectrum :=
  Multiset.mem_of_mem_erase (G.algConn_mem_erase h)

/-- To compute an algebraic connectivity it is enough to exhibit a least element of the punctured
Laplacian spectrum. -/
@[toIsoGraph]
theorem algConn_eq_of_isLeast {G : CGraph} {a : ℝ} (hmem : a ∈ G.lapSpectrum.erase 0)
    (hle : ∀ x ∈ G.lapSpectrum.erase 0, a ≤ x) : G.algConn = a :=
  le_antisymm (algConn_le hmem) (le_csInf ⟨a, hmem⟩ hle)

/-- **The algebraic connectivity is positive exactly for a connected graph** (on at least two
vertices): the multiplicity of `0` is the number of components, so a second `0` survives the
erasure precisely when the graph falls apart. -/
@[toIsoGraph]
theorem algConn_pos_iff (G : CGraph) (h : 2 ≤ Fintype.card G.V) :
    0 < G.algConn ↔ G.IsConnected := by
  constructor
  · intro hpos
    by_contra hcon
    have hne : G.numComponents ≠ 1 := fun hc ↦ hcon (G.numComponents_eq_one_iff.1 hc)
    have hpos' : 0 < G.numComponents := G.numComponents_pos_iff.2 (by omega)
    have hcount : 2 ≤ G.lapSpectrum.count 0 := by
      rw [count_zero_lapSpectrum]
      omega
    have h0 : (0 : ℝ) ∈ G.lapSpectrum.erase 0 := by
      rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self]
      omega
    exact absurd (algConn_le h0) (not_le.2 hpos)
  · intro hcon
    have hmem := G.algConn_mem_erase h
    have hcount : G.lapSpectrum.count 0 = 1 := G.count_zero_lapSpectrum_eq_one_iff.2 hcon
    have hne : G.algConn ≠ 0 := by
      intro h0
      rw [h0, ← Multiset.one_le_count_iff_mem, Multiset.count_erase_self, hcount] at hmem
      omega
    exact lt_of_le_of_ne G.algConn_nonneg (Ne.symm hne)

theorem algConn_eq_zero_of_not_isConnected {G : CGraph} (h : 2 ≤ Fintype.card G.V)
    (hcon : ¬ G.IsConnected) : G.algConn = 0 :=
  le_antisymm (not_lt.1 fun hpos ↦ hcon ((G.algConn_pos_iff h).1 hpos)) G.algConn_nonneg

/-- **The algebraic connectivity is at most the order**, with equality for the complete graph. -/
theorem algConn_le_card (G : CGraph) [DecidableEq G.V] (h : 2 ≤ Fintype.card G.V) :
    G.algConn ≤ Fintype.card G.V :=
  G.le_card_of_mem_lapSpectrum (G.algConn_mem_lapSpectrum h)

/-- **A disjoint union has algebraic connectivity `0`** as soon as both pieces are nonempty. -/
theorem algConn_disjUnion (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (disjUnion G H).algConn = 0 := by
  have h0G : (0 : ℝ) ∈ G.lapSpectrum := G.zero_mem_lapSpectrum
  have h0H : (0 : ℝ) ∈ H.lapSpectrum := H.zero_mem_lapSpectrum
  have hmem : (0 : ℝ) ∈ (disjUnion G H).lapSpectrum.erase 0 := by
    rw [lapSpectrum_disjUnion]
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h0G
    rw [ht, Multiset.cons_add, Multiset.erase_cons_head]
    exact Multiset.mem_add.2 (Or.inr h0H)
  exact le_antisymm (algConn_le hmem) (disjUnion G H).algConn_nonneg

/-- **The algebraic connectivity of the complete graph is its order**, the extreme case of
`algConn_le_card`. -/
@[toIsoGraph]
theorem algConn_complete (n : ℕ) : (complete (n + 2)).algConn = (n : ℝ) + 2 := by
  have hspec : (complete (n + 2)).lapSpectrum
      = 0 ::ₘ Multiset.replicate (n + 1) ((n : ℝ) + 2) := by
    have h := lapSpectrum_complete (n + 1)
    push_cast at h ⊢
    convert h using 3
    ring
  have herase : (complete (n + 2)).lapSpectrum.erase 0
      = Multiset.replicate (n + 1) ((n : ℝ) + 2) := by
    rw [hspec, Multiset.erase_cons_head]
  have hcard : 2 ≤ Fintype.card (complete (n + 2)).V := by
    rw [card_complete]
    omega
  have hmem := (complete (n + 2)).algConn_mem_erase hcard
  rw [herase] at hmem
  exact Multiset.eq_of_mem_replicate hmem

/-- **The algebraic connectivity of a complete bipartite graph is the size of its smaller side.**
(The one exception is `K₁,₁ = K₂`, where the smaller side has one vertex but `a = 2`; the
hypothesis `1 ≤ m + n` rules it out.) -/
@[toIsoGraph]
theorem algConn_bipartite (m n : ℕ) (h : 1 ≤ m + n) :
    (bipartite (m + 1) (n + 1)).algConn = min ((m : ℝ) + 1) ((n : ℝ) + 1) := by
  have herase : (bipartite (m + 1) (n + 1)).lapSpectrum.erase 0
      = ((m : ℝ) + (n : ℝ) + 2)
        ::ₘ (Multiset.replicate m ((n : ℝ) + 1) + Multiset.replicate n ((m : ℝ) + 1)) := by
    rw [lapSpectrum_bipartite, Multiset.erase_cons_head]
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase]
    rcases Nat.le_total m n with hmn | hmn
    · have hmin : min ((m : ℝ) + 1) ((n : ℝ) + 1) = (m : ℝ) + 1 :=
        min_eq_left (by exact_mod_cast Nat.add_le_add_right hmn 1)
      rw [hmin]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
    · have hmin : min ((m : ℝ) + 1) ((n : ℝ) + 1) = (n : ℝ) + 1 :=
        min_eq_right (by exact_mod_cast Nat.add_le_add_right hmn 1)
      rw [hmin]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)))
  · intro x hx
    rw [herase, Multiset.mem_cons, Multiset.mem_add] at hx
    have hm1 : min ((m : ℝ) + 1) ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := min_le_left _ _
    have hn1 : min ((m : ℝ) + 1) ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := min_le_right _ _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases hx with rfl | hx
    · linarith
    rcases hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hn1
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hm1

/-- **The star has algebraic connectivity `1`.** -/
@[toIsoGraph]
theorem algConn_star (n : ℕ) : (star (n + 2)).algConn = 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h := algConn_bipartite 0 (n + 1) (by omega)
  norm_num at h
  rw [min_eq_left (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1 + 1)] at h
  rw [star]
  exact h

open Real in
/-- **The algebraic connectivity of the path** `P_{n+2}` is `2 - 2 cos (π / (n + 2))`: of the
eigenvalues `2 - 2 cos (π m / (n + 2))` the one at `m = 0` is the erased zero and the cosine is
decreasing, so `m = 1` gives the smallest of the rest.  It shrinks like `1 / n ²`, which is why
the path is the connected graph the Fiedler value calls worst-connected. -/
@[toIsoGraph]
theorem algConn_path (n : ℕ) :
    (path (n + 2)).algConn = 2 - 2 * Real.cos (π / ((n : ℝ) + 2)) := by
  have hpi : 0 < π := Real.pi_pos
  have hN : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  set f : Fin (n + 2) → ℝ := fun m ↦ 2 - 2 * Real.cos (π * m.1 / ((n : ℝ) + 2)) with hf
  have hspec : (path (n + 2)).lapSpectrum = Finset.univ.val.map f := by
    rw [lapSpectrum_path, hf]
    push_cast
    rfl
  have h0 : f 0 = 0 := by
    rw [hf]
    simp
  have hmem0 : (0 : Fin (n + 2)) ∈ Finset.univ.val := Finset.mem_univ_val _
  have huniv : (Finset.univ.val : Multiset (Fin (n + 2)))
      = 0 ::ₘ Finset.univ.val.erase 0 := (Multiset.cons_erase hmem0).symm
  have herase : (path (n + 2)).lapSpectrum.erase 0
      = (Finset.univ.val.erase (0 : Fin (n + 2))).map f := by
    rw [hspec]
    conv_lhs => rw [huniv]
    rw [Multiset.map_cons, h0, Multiset.erase_cons_head]
  have hone : f 1 = 2 - 2 * Real.cos (π / ((n : ℝ) + 2)) := by
    rw [hf]
    simp only [Fin.val_one]
    norm_num
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase, ← hone]
    refine Multiset.mem_map_of_mem f ?_
    refine (Multiset.mem_erase_of_ne ?_).2 (Finset.mem_univ_val _)
    simp
  · intro x hx
    rw [herase] at hx
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hx
    have hm0 : m ≠ 0 := by
      intro hzero
      subst hzero
      rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self] at hm
      have hle1 := Multiset.nodup_iff_count_le_one.1 Finset.univ.nodup (0 : Fin (n + 2))
      omega
    have hm1 : 1 ≤ m.1 := by
      rcases Nat.eq_zero_or_pos m.1 with h | h
      · exact absurd (Fin.ext h) hm0
      · exact h
    have hm1R : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast hm1
    have hmltR : (m.1 : ℝ) ≤ (n : ℝ) + 2 := by
      have : m.1 ≤ n + 2 := m.isLt.le
      exact_mod_cast this
    have hle : π / ((n : ℝ) + 2) ≤ π * m.1 / ((n : ℝ) + 2) := by
      gcongr
      nlinarith
    have hub : π * m.1 / ((n : ℝ) + 2) ≤ π := by
      rw [div_le_iff₀ hN]
      nlinarith
    have hcos : Real.cos (π * m.1 / ((n : ℝ) + 2)) ≤ Real.cos (π / ((n : ℝ) + 2)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hub hle
    have hfm : f m = 2 - 2 * Real.cos (π * m.1 / ((n : ℝ) + 2)) := rfl
    rw [hfm]
    linarith

/-! ### The largest Laplacian eigenvalue -/

/-- The **largest Laplacian eigenvalue**, the other end of the Laplacian spectrum from `algConn`.
As with `algConn` the supremum is taken in `ℝ`, so the empty graph gets `sSup ∅ = 0`. -/
noncomputable def lapLambdaMax (G : CGraph) : ℝ := sSup {x : ℝ | x ∈ G.lapSpectrum}

end CGraph

namespace IsoGraph

/-- The **largest Laplacian eigenvalue** of an isomorphism class. -/
noncomputable def lapLambdaMax (G : IsoGraph) : ℝ := sSup {x : ℝ | x ∈ G.lapSpectrum}

@[simp, isoTransfer] theorem lapLambdaMax_mk (G : CGraph) :
    lapLambdaMax ⟦G⟧ = G.lapLambdaMax := rfl

end IsoGraph

namespace CGraph

@[toIsoGraph]
theorem le_lapLambdaMax {G : CGraph} {x : ℝ} (hx : x ∈ G.lapSpectrum) : x ≤ G.lapLambdaMax :=
  le_csSup (Multiset.finite_toSet _).bddAbove hx

theorem lapLambdaMax_mem_lapSpectrum (G : CGraph) [Nonempty G.V] :
    G.lapLambdaMax ∈ G.lapSpectrum :=
  Set.Nonempty.csSup_mem ⟨0, G.zero_mem_lapSpectrum⟩ (Multiset.finite_toSet _)

/-- To compute a largest Laplacian eigenvalue it is enough to exhibit a greatest element of the
Laplacian spectrum. -/
@[toIsoGraph]
theorem lapLambdaMax_eq_of_isGreatest {G : CGraph} {a : ℝ} (hmem : a ∈ G.lapSpectrum)
    (hle : ∀ x ∈ G.lapSpectrum, x ≤ a) : G.lapLambdaMax = a :=
  le_antisymm (csSup_le ⟨a, hmem⟩ hle) (le_lapLambdaMax hmem)

theorem lapLambdaMax_nonneg (G : CGraph) [Nonempty G.V] : 0 ≤ G.lapLambdaMax :=
  le_lapLambdaMax G.zero_mem_lapSpectrum

@[toIsoGraph]
theorem algConn_le_lapLambdaMax (G : CGraph) (h : 2 ≤ Fintype.card G.V) :
    G.algConn ≤ G.lapLambdaMax :=
  le_lapLambdaMax (G.algConn_mem_lapSpectrum h)

/-- **The largest Laplacian eigenvalue is at most the number of vertices.** -/
theorem lapLambdaMax_le_card (G : CGraph) [Nonempty G.V] [DecidableEq G.V] :
    G.lapLambdaMax ≤ Fintype.card G.V :=
  G.le_card_of_mem_lapSpectrum G.lapLambdaMax_mem_lapSpectrum

theorem lapLambdaMax_le_two_mul_maxDeg (G : CGraph) [Nonempty G.V] :
    G.lapLambdaMax ≤ 2 * (G.maxDeg : ℝ) :=
  le_two_mul_maxDeg_of_mem_lapSpectrum G.lapLambdaMax_mem_lapSpectrum

/-- **The largest Laplacian eigenvalue is at least the average degree**: the `n` eigenvalues sum
to `2 E`. -/
theorem two_mul_E_le_card_mul_lapLambdaMax (G : CGraph) :
    2 * (G.E : ℝ) ≤ Fintype.card G.V * G.lapLambdaMax := by
  have hsum : G.lapSpectrum.sum ≤ Multiset.card G.lapSpectrum • G.lapLambdaMax :=
    Multiset.sum_le_card_nsmul _ _ fun x hx ↦ le_lapLambdaMax hx
  rw [G.sum_lapSpectrum, G.card_lapSpectrum, nsmul_eq_mul] at hsum
  exact hsum

/-- **The algebraic connectivity is at most the average of the nonzero eigenvalues**: the `n - 1`
of them left after the erasure still sum to `2 E`. -/
theorem card_sub_one_mul_algConn_le_two_mul_E (G : CGraph) [Nonempty G.V] :
    (Fintype.card G.V - 1 : ℕ) * G.algConn ≤ 2 * (G.E : ℝ) := by
  have hsum : (G.lapSpectrum.erase 0).sum = 2 * (G.E : ℝ) := by
    have hcons := Multiset.cons_erase G.zero_mem_lapSpectrum
    have h2 : G.lapSpectrum.sum = 0 + (G.lapSpectrum.erase 0).sum := by
      conv_lhs => rw [← hcons]
      rw [Multiset.sum_cons]
    rw [G.sum_lapSpectrum] at h2
    linarith
  have hcard : Multiset.card (G.lapSpectrum.erase 0) = Fintype.card G.V - 1 := by
    rw [Multiset.card_erase_of_mem G.zero_mem_lapSpectrum, card_lapSpectrum]
    rfl
  have h := Multiset.card_nsmul_le_sum (s := G.lapSpectrum.erase 0) (a := G.algConn)
    fun x hx ↦ algConn_le hx
  rw [hsum, hcard, nsmul_eq_mul] at h
  exact h

/-- **The complement swaps the two ends of the Laplacian spectrum**: `μ_max (Ḡ) = n - a (G)`. -/
theorem lapLambdaMax_compl (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (h : 2 ≤ Fintype.card G.V) :
    (compl G).lapLambdaMax = Fintype.card G.V - G.algConn := by
  haveI : Nonempty (compl G).V := ‹Nonempty G.V›
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_compl]
    exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ (G.algConn_mem_erase h))
  · intro x hx
    rw [lapSpectrum_compl, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · have := G.algConn_le_card h
      have hcard : (0 : ℝ) ≤ Fintype.card G.V := by positivity
      linarith
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := algConn_le hy
      linarith

/-- **The complement swaps the two ends of the Laplacian spectrum**: `a (Ḡ) = n - μ_max (G)`. -/
theorem algConn_compl (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (h : 2 ≤ Fintype.card G.V) :
    (compl G).algConn = Fintype.card G.V - G.lapLambdaMax := by
  haveI : Nonempty (compl G).V := ‹Nonempty G.V›
  have herase : (compl G).lapSpectrum.erase 0
      = (G.lapSpectrum.erase 0).map (fun x ↦ (Fintype.card G.V : ℝ) - x) := by
    rw [lapSpectrum_compl, Multiset.erase_cons_head]
  have hmax : G.lapLambdaMax ∈ G.lapSpectrum.erase 0 := by
    rcases eq_or_ne G.lapLambdaMax 0 with h0 | h0
    · -- every eigenvalue is squeezed between `0` and `μ_max = 0`, so the spectrum is all zeros
      have hall : ∀ x ∈ G.lapSpectrum, x = 0 := fun x hx ↦
        le_antisymm (h0 ▸ le_lapLambdaMax hx) (G.nonneg_of_mem_lapSpectrum hx)
      have hrep : G.lapSpectrum = Multiset.replicate (Fintype.card G.V) 0 := by
        rw [Multiset.eq_replicate]
        exact ⟨G.card_lapSpectrum, hall⟩
      have hcount : (G.lapSpectrum.erase 0).count 0 = Fintype.card G.V - 1 := by
        rw [Multiset.count_erase_self, hrep, Multiset.count_replicate_self]
      rw [h0, ← Multiset.one_le_count_iff_mem, hcount]
      omega
    · exact (Multiset.mem_erase_of_ne h0).2 G.lapLambdaMax_mem_lapSpectrum
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase]
    exact Multiset.mem_map_of_mem _ hmax
  · intro x hx
    rw [herase] at hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    have := le_lapLambdaMax (Multiset.mem_of_mem_erase hy)
    linarith

/-- **The largest Laplacian eigenvalue of the complete graph** `K_{n+2}` is its order. -/
@[toIsoGraph]
theorem lapLambdaMax_complete (n : ℕ) : (complete (n + 2)).lapLambdaMax = (n : ℝ) + 2 := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [show n + 2 = (n + 1) + 1 from rfl, lapSpectrum_complete]
    refine Multiset.mem_cons_of_mem (Multiset.mem_replicate.2 ⟨by omega, ?_⟩)
    push_cast
    ring
  · intro x hx
    rw [show n + 2 = (n + 1) + 1 from rfl, lapSpectrum_complete, Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · positivity
    · rw [Multiset.eq_of_mem_replicate hx]
      push_cast
      ring_nf
      rfl

/-- **The largest Laplacian eigenvalue of the star** `K₁,ₙ₊₁` is its order: the star is a join, and
a join always attains the bound `lapLambdaMax_le_card`. -/
@[toIsoGraph]
theorem lapLambdaMax_star (n : ℕ) : (star (n + 1)).lapLambdaMax = (n : ℝ) + 2 := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_star]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · intro x hx
    rw [lapSpectrum_star, Multiset.mem_cons, Multiset.mem_cons] at hx
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases hx with rfl | rfl | hx
    · linarith
    · linarith
    · rw [Multiset.eq_of_mem_replicate hx]
      linarith

/-- **The largest Laplacian eigenvalue of the complete bipartite graph** `K_{m+1,n+1}` is its
order, like every join. -/
@[toIsoGraph]
theorem lapLambdaMax_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).lapLambdaMax = (m : ℝ) + (n : ℝ) + 2 := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_bipartite]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · intro x hx
    rw [lapSpectrum_bipartite] at hx
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · positivity
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · rw [Multiset.eq_of_mem_replicate hx]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

open Real in
/-- **The largest Laplacian eigenvalue of the path** `P_{n+1}` is `2 - 2 cos (π n / (n + 1))`, the
top of the same cosine range whose bottom is `algConn_path`.  It climbs to `4` as `n → ∞` but never
reaches it: a path is bipartite but not regular. -/
@[toIsoGraph]
theorem lapLambdaMax_path (n : ℕ) :
    (path (n + 1)).lapLambdaMax = 2 - 2 * Real.cos (Real.pi * n / ((n : ℝ) + 1)) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpi : 0 < π := Real.pi_pos
  set f : Fin (n + 1) → ℝ := fun m ↦ 2 - 2 * Real.cos (Real.pi * m.1 / ((n : ℝ) + 1)) with hf
  have hspec : (path (n + 1)).lapSpectrum = Finset.univ.val.map f := by
    rw [lapSpectrum_path, hf]
    push_cast
    rfl
  have hlast : f (Fin.last n) = 2 - 2 * Real.cos (Real.pi * n / ((n : ℝ) + 1)) := rfl
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [hspec, ← hlast]
    exact Multiset.mem_map_of_mem f (Finset.mem_univ_val _)
  · intro x hx
    rw [hspec] at hx
    obtain ⟨m, _, rfl⟩ := Multiset.mem_map.1 hx
    have hmn : (m.1 : ℝ) ≤ (n : ℝ) := by
      have : m.1 ≤ n := Nat.lt_succ_iff.1 m.isLt
      exact_mod_cast this
    have hle : Real.pi * m.1 / ((n : ℝ) + 1) ≤ Real.pi * n / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by nlinarith) hN.le
    have hpiLe : Real.pi * n / ((n : ℝ) + 1) ≤ π := by
      rw [div_le_iff₀ hN]
      nlinarith
    have hcos : Real.cos (Real.pi * n / ((n : ℝ) + 1))
        ≤ Real.cos (Real.pi * m.1 / ((n : ℝ) + 1)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpiLe hle
    have hfm : f m = 2 - 2 * Real.cos (Real.pi * m.1 / ((n : ℝ) + 1)) := rfl
    rw [hfm]
    linarith

/-- **A disjoint union takes the larger of the two largest eigenvalues**, where `algConn_disjUnion`
takes neither: the small end collapses to `0` but the large end does not interact. -/
theorem lapLambdaMax_disjUnion (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (disjUnion G H).lapLambdaMax = max G.lapLambdaMax H.lapLambdaMax := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_disjUnion, Multiset.mem_add]
    rcases le_total G.lapLambdaMax H.lapLambdaMax with hle | hle
    · refine Or.inr ?_
      rw [max_eq_right hle]
      exact lapLambdaMax_mem_lapSpectrum H
    · refine Or.inl ?_
      rw [max_eq_left hle]
      exact lapLambdaMax_mem_lapSpectrum G
  · intro x hx
    rw [lapSpectrum_disjUnion, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact le_max_of_le_left (le_lapLambdaMax hx)
    · exact le_max_of_le_right (le_lapLambdaMax hx)

/-- **A `k`-regular graph's two spectra are reflections of each other**, so the largest Laplacian
eigenvalue is `k - λ_min`. -/
theorem lapLambdaMax_of_isRegularWith {G : CGraph} [Nonempty G.V] {k : ℕ}
    (h : G.IsRegularWith k) : G.lapLambdaMax = (k : ℝ) - G.lambdaMin := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_of_isRegularWith h]
    exact Multiset.mem_map_of_mem _ (lambdaMin_mem_spectrum G)
  · intro x hx
    rw [lapSpectrum_of_isRegularWith h] at hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    have := lambdaMin_le hy
    linarith

/-- **The largest Laplacian eigenvalue of the empty graph** is `0`: its Laplacian is the zero
matrix, so `μ_max = 0 - λ_min` collapses. -/
theorem lapLambdaMax_empty (n : ℕ) : (empty (n + 1)).lapLambdaMax = 0 := by
  rw [lapLambdaMax_of_isRegularWith (isRegularWith_empty (n + 1)), lambdaMin_empty]
  norm_num

/-- **The largest Laplacian eigenvalue vanishes exactly on the edgeless graph**: the spectrum is
nonnegative and sums to `2 E`. -/
theorem lapLambdaMax_eq_zero_iff (G : CGraph) [Nonempty G.V] :
    G.lapLambdaMax = 0 ↔ G.E = 0 := by
  constructor
  · intro h
    have hall : ∀ x ∈ G.lapSpectrum, x = 0 := fun x hx ↦
      le_antisymm (h ▸ le_lapLambdaMax hx) (nonneg_of_mem_lapSpectrum G hx)
    have hsum : G.lapSpectrum.sum = 0 := Multiset.sum_eq_zero hall
    rw [sum_lapSpectrum] at hsum
    exact_mod_cast (by linarith : (G.E : ℝ) = 0)
  · intro h
    refine lapLambdaMax_eq_of_isGreatest G.zero_mem_lapSpectrum ?_
    intro x hx
    have hsum : G.lapSpectrum.sum = 0 := by rw [sum_lapSpectrum, h]; norm_num
    have := Multiset.single_le_sum (fun y hy ↦ nonneg_of_mem_lapSpectrum G hy) x hx
    linarith

theorem lapEigenvalues_mem_lapSpectrum (G : CGraph) (i : G.V) :
    G.lapEigenvalues i ∈ G.lapSpectrum := by
  rw [lapSpectrum_eq_map]
  exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)

/-- **The Laplacian quadratic form is the sum of the squared differences across the edges**,
each edge counted twice: `2 ⟪v, L v⟫ = ∑ i ∑ j A i j (v i - v j) ²`.  This is the identity that
makes `L` positive semidefinite and is the source of every variational bound below. -/
theorem two_mul_lap_quadratic (G : CGraph) (v : G.V → ℝ) :
    2 * (v ⬝ᵥ (G.lapMat *ᵥ v)) = ∑ i, ∑ j, G.adjMat i j * (v i - v j) ^ 2 := by
  have hexp : ∀ i j : G.V, G.adjMat i j * (v i - v j) ^ 2
      = G.adjMat i j * v i ^ 2 + G.adjMat i j * v j ^ 2
        - 2 * (G.adjMat i j * (v i * v j)) := fun i j ↦ by ring
  have hrow : ∀ i : G.V, ∑ j, G.adjMat i j * v i ^ 2
      = (G.toSimple.degree i : ℝ) * v i ^ 2 := fun i ↦ by
    rw [← Finset.sum_mul, sum_adjMat_row_eq_degree]
  have hcol : ∑ i, ∑ j, G.adjMat i j * v j ^ 2 = ∑ j, (G.toSimple.degree j : ℝ) * v j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_mul]
    congr 1
    rw [← sum_adjMat_row_eq_degree]
    exact Finset.sum_congr rfl fun i _ ↦ G.adjMat_symm i j
  have hlhs : v ⬝ᵥ (G.lapMat *ᵥ v)
      = ∑ i, ((G.toSimple.degree i : ℝ) * v i ^ 2 - ∑ j, G.adjMat i j * (v i * v j)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lapMat_mulVec_apply, sum_adjMat_row_eq_degree, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hrowsum : ∀ i : G.V, ∑ j, G.adjMat i j * (v i - v j) ^ 2
      = (G.toSimple.degree i : ℝ) * v i ^ 2 + (∑ j, G.adjMat i j * v j ^ 2)
        - 2 * ∑ j, G.adjMat i j * (v i * v j) := fun i ↦ by
    simp only [hexp]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow i, ← Finset.mul_sum]
  have hL2 : ∑ i, ((G.toSimple.degree i : ℝ) * v i ^ 2 - ∑ j, G.adjMat i j * (v i * v j))
      = (∑ i, (G.toSimple.degree i : ℝ) * v i ^ 2)
        - ∑ i, ∑ j, G.adjMat i j * (v i * v j) := Finset.sum_sub_distrib _ _
  have hR2 : ∑ i, ∑ j, G.adjMat i j * (v i - v j) ^ 2
      = (∑ i, (G.toSimple.degree i : ℝ) * v i ^ 2) + (∑ i, ∑ j, G.adjMat i j * v j ^ 2)
        - 2 * ∑ i, ∑ j, G.adjMat i j * (v i * v j) := by
    rw [Finset.sum_congr rfl (fun i _ ↦ hrowsum i), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hlhs, hL2, hR2, hcol]
  ring

/-- **The Laplacian is positive semidefinite**, immediately from the sum-of-squares identity. -/
theorem lap_quadratic_nonneg (G : CGraph) (v : G.V → ℝ) : 0 ≤ v ⬝ᵥ (G.lapMat *ᵥ v) := by
  have h := G.two_mul_lap_quadratic v
  have hnn : 0 ≤ ∑ i, ∑ j, G.adjMat i j * (v i - v j) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (G.adjMat_nonneg i j) (sq_nonneg _)
  linarith

/-- The Laplacian analogue of `exists_rotate_quadratic`. -/
theorem exists_rotate_lap_quadratic (G : CGraph) (v : G.V → ℝ) :
    ∃ w : G.V → ℝ, v ⬝ᵥ (G.lapMat *ᵥ v) = ∑ i, G.lapEigenvalues i * w i ^ 2 ∧
      v ⬝ᵥ v = ∑ i, w i ^ 2 := by
  obtain ⟨U, hUU, hUU', hD⟩ := G.exists_orthogonal_lap_diagonal
  refine ⟨Uᵀ *ᵥ v, ?_, ?_⟩
  · have hL : G.lapMat = U * Matrix.diagonal G.lapEigenvalues * Uᵀ := by
      rw [← hD]
      calc G.lapMat = U * Uᵀ * G.lapMat * (U * Uᵀ) := by rw [hUU', one_mul, mul_one]
        _ = U * (Uᵀ * G.lapMat * U) * Uᵀ := by simp only [mul_assoc]
    rw [hL, show (U * Matrix.diagonal G.lapEigenvalues * Uᵀ) *ᵥ v
          = U *ᵥ (Matrix.diagonal G.lapEigenvalues *ᵥ (Uᵀ *ᵥ v)) by
        simp only [Matrix.mulVec_mulVec, mul_assoc],
      dotProduct_mulVec, show v ᵥ* U = Uᵀ *ᵥ v by
        rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · have hn : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
      rw [dotProduct_mulVec, show (Uᵀ *ᵥ v) ᵥ* Uᵀ = U *ᵥ (Uᵀ *ᵥ v) by
        rw [Matrix.vecMul_transpose], Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rw [← hn]
    exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm

/-- On a connected graph the rotation of `exists_rotate_lap_quadratic` kills the kernel
direction as well: the columns of the diagonalising matrix belonging to the eigenvalue `0` are
constant vectors, so a vector summing to zero has no component along any of them. -/
theorem exists_rotate_lap_quadratic_of_sum_eq_zero (G : CGraph) (hconn : G.IsConnected)
    (v : G.V → ℝ) (hv : ∑ i, v i = 0) :
    ∃ w : G.V → ℝ, v ⬝ᵥ (G.lapMat *ᵥ v) = ∑ i, G.lapEigenvalues i * w i ^ 2 ∧
      v ⬝ᵥ v = ∑ i, w i ^ 2 ∧ ∀ i, G.lapEigenvalues i = 0 → w i = 0 := by
  haveI : Nonempty G.V := hconn.nonempty
  obtain ⟨U, hUU, hUU', hD⟩ := G.exists_orthogonal_lap_diagonal
  have hL : G.lapMat = U * Matrix.diagonal G.lapEigenvalues * Uᵀ := by
    rw [← hD]
    calc G.lapMat = U * Uᵀ * G.lapMat * (U * Uᵀ) := by rw [hUU', one_mul, mul_one]
      _ = U * (Uᵀ * G.lapMat * U) * Uᵀ := by simp only [mul_assoc]
  have hLU : G.lapMat * U = U * Matrix.diagonal G.lapEigenvalues := by
    calc G.lapMat * U = (U * Uᵀ) * (G.lapMat * U) := by rw [hUU', one_mul]
      _ = U * (Uᵀ * G.lapMat * U) := by simp only [mul_assoc]
      _ = U * Matrix.diagonal G.lapEigenvalues := by rw [hD]
  refine ⟨Uᵀ *ᵥ v, ?_, ?_, ?_⟩
  · rw [hL, show (U * Matrix.diagonal G.lapEigenvalues * Uᵀ) *ᵥ v
          = U *ᵥ (Matrix.diagonal G.lapEigenvalues *ᵥ (Uᵀ *ᵥ v)) by
        simp only [Matrix.mulVec_mulVec, mul_assoc],
      dotProduct_mulVec, show v ᵥ* U = Uᵀ *ᵥ v by
        rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · have hn : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
      rw [dotProduct_mulVec, show (Uᵀ *ᵥ v) ᵥ* Uᵀ = U *ᵥ (Uᵀ *ᵥ v) by
        rw [Matrix.vecMul_transpose], Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rw [← hn]
    exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  · intro i hi
    have hcol : G.lapMat *ᵥ (Uᵀ i) = 0 := by
      funext x
      have h1 : (G.lapMat * U) x i = U x i * G.lapEigenvalues i := by
        rw [hLU, Matrix.mul_diagonal]
      rw [hi, mul_zero] at h1
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h1
    obtain ⟨r₀⟩ := ‹Nonempty G.V›
    have hconst : ∀ r, U r i = U r₀ i := fun r ↦
      (G.lapMat_mulVec_eq_zero_iff.1 hcol) r r₀ (hconn.preconnected r r₀)
    calc (Uᵀ *ᵥ v) i = ∑ r, U r i * v r := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      _ = ∑ r, U r₀ i * v r := Finset.sum_congr rfl fun r _ ↦ by rw [hconst r]
      _ = U r₀ i * ∑ r, v r := by rw [Finset.mul_sum]
      _ = 0 := by rw [hv, mul_zero]

/-- **The Laplacian Rayleigh quotient is bounded above by the largest Laplacian eigenvalue.** -/
theorem lap_rayleigh_le_lapLambdaMax (G : CGraph) [Nonempty G.V] (v : G.V → ℝ) :
    v ⬝ᵥ (G.lapMat *ᵥ v) ≤ G.lapLambdaMax * (v ⬝ᵥ v) := by
  obtain ⟨w, h1, h2⟩ := G.exists_rotate_lap_quadratic v
  rw [h1, h2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_right (le_lapLambdaMax (G.lapEigenvalues_mem_lapSpectrum i)) (sq_nonneg _)

/-- **The largest Laplacian eigenvalue exceeds the maximum degree**: `Δ + 1 ≤ μ_max`.  The test
vector is `Δ` at a vertex of maximum degree, `-1` at each of its neighbours and `0` elsewhere;
its Rayleigh quotient is already `Δ + 1`, since the `Δ` edges at the centre each contribute
`(Δ + 1) ²` and every other edge contributes something nonnegative. -/
theorem maxDeg_add_one_le_lapLambdaMax (G : CGraph) [Nonempty G.V] (h : 0 < G.E) :
    (G.maxDeg : ℝ) + 1 ≤ G.lapLambdaMax := by
  classical
  have hΔ : 0 < G.maxDeg := by
    rcases Nat.eq_zero_or_pos G.maxDeg with h0 | h0
    · exfalso
      have hle := G.two_mul_E_le_card_mul_maxDeg
      rw [h0, Nat.mul_zero] at hle
      omega
    · exact h0
  obtain ⟨c, hc⟩ := G.exists_degree_eq_maxDeg (Classical.arbitrary G.V)
  set d : ℝ := (G.maxDeg : ℝ) with hd
  have hd1 : (1 : ℝ) ≤ d := by
    rw [hd]
    exact_mod_cast hΔ
  set x : G.V → ℝ := fun i ↦ (if i = c then d else 0) - G.adjMat c i with hx
  have hrow : ∑ j, G.adjMat c j = d := by rw [sum_adjMat_row_eq_degree, hc]
  have hAsq : ∀ i j : G.V, G.adjMat i j * G.adjMat i j = G.adjMat i j := fun i j ↦ by
    rw [adjMat_apply]
    split <;> norm_num
  have hcc : G.adjMat c c = 0 := by simp [adjMat_apply, G.adj_self]
  have hxc : x c = d := by rw [hx]; simp [hcc]
  have hxne : ∀ i, i ≠ c → x i = -G.adjMat c i := fun i hi ↦ by rw [hx]; simp [hi]
  -- the squared norm of the test vector
  have hnorm : x ⬝ᵥ x = d ^ 2 + d := by
    have hterm : ∀ i : G.V, x i * x i
        = (if i = c then d ^ 2 else 0) + G.adjMat c i
          - 2 * ((if i = c then d else 0) * G.adjMat c i) := fun i ↦ by
      rw [hx]
      simp only
      rcases eq_or_ne i c with rfl | hi
      · simp [hcc]
        ring
      · simp only [if_neg hi]
        rw [zero_sub, neg_mul_neg, hAsq c i]
        ring
    rw [dotProduct, Finset.sum_congr rfl fun i _ ↦ hterm i]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrow, Finset.sum_ite_eq' Finset.univ c,
      if_pos (Finset.mem_univ c)]
    have hzero : ∑ i, 2 * ((if i = c then d else 0) * G.adjMat c i) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rcases eq_or_ne i c with rfl | hi
      · simp [hcc]
      · simp [hi]
    rw [hzero]
    ring
  -- the quadratic form, from below
  have hquad : d * (d + 1) ^ 2 ≤ x ⬝ᵥ (G.lapMat *ᵥ x) := by
    set f : G.V → G.V → ℝ := fun i j ↦ G.adjMat i j * (x i - x j) ^ 2 with hf
    have hfnn : ∀ i j, 0 ≤ f i j := fun i j ↦ by
      rw [hf]
      exact mul_nonneg (G.adjMat_nonneg i j) (sq_nonneg _)
    have hfcc : f c c = 0 := by rw [hf]; simp [hcc]
    have hrowc : ∑ j, f c j = d * (d + 1) ^ 2 := by
      have hterm : ∀ j : G.V, f c j = G.adjMat c j * (d + 1) ^ 2 := fun j ↦ by
        rw [hf]
        simp only
        by_cases hadj : G.Adj c j
        · have hjc : j ≠ c := by
            rintro rfl
            simp [G.adj_self] at hadj
          rw [hxc, hxne j hjc, adjMat_apply, if_pos hadj]
          ring
        · rw [adjMat_apply, if_neg hadj]
          ring
      rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.sum_mul, hrow]
    have hcolc : ∑ i, f i c = d * (d + 1) ^ 2 := by
      have hterm : ∀ i : G.V, f i c = f c i := fun i ↦ by
        rw [hf]
        simp only [G.adjMat_symm i c]
        ring_nf
      rw [Finset.sum_congr rfl fun i _ ↦ hterm i, hrowc]
    have hsplit : ∑ i, ∑ j, f i j = (∑ j, f c j) + ∑ i ∈ Finset.univ.erase c, ∑ j, f i j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ c)).symm
    have hlow : ∑ i ∈ Finset.univ.erase c, f i c ≤ ∑ i ∈ Finset.univ.erase c, ∑ j, f i j :=
      Finset.sum_le_sum fun i _ ↦ Finset.single_le_sum (fun j _ ↦ hfnn i j) (Finset.mem_univ c)
    have herase : ∑ i ∈ Finset.univ.erase c, f i c = d * (d + 1) ^ 2 := by
      have hb : f c c + ∑ i ∈ Finset.univ.erase c, f i c = ∑ i, f i c :=
        Finset.add_sum_erase Finset.univ (fun i ↦ f i c) (Finset.mem_univ c)
      rw [hfcc, zero_add, hcolc] at hb
      exact hb
    have h2 : 2 * (x ⬝ᵥ (G.lapMat *ᵥ x)) = ∑ i, ∑ j, f i j := G.two_mul_lap_quadratic x
    rw [hsplit, hrowc] at h2
    linarith [herase ▸ hlow]
  -- and from above
  have hup : x ⬝ᵥ (G.lapMat *ᵥ x) ≤ G.lapLambdaMax * (d ^ 2 + d) := by
    have := G.lap_rayleigh_le_lapLambdaMax x
    rwa [hnorm] at this
  have hdpos : 0 < d := by linarith
  have hkey : d * (d + 1) ^ 2 ≤ G.lapLambdaMax * (d * (d + 1)) := by
    have : d ^ 2 + d = d * (d + 1) := by ring
    rw [← this]
    linarith
  have hpos : 0 < d * (d + 1) := by nlinarith
  by_contra hcon
  push_neg at hcon
  nlinarith [hkey, hpos]

/-! ### Fiedler's bound on the algebraic connectivity -/

/-- **The variational characterisation of the Fiedler value**, the lower half: on every vector
orthogonal to the all-ones vector the Laplacian quadratic form is at least `a (G) ⟪v, v⟫`.  On a
connected graph this is the eigenvalue expansion with the kernel term removed; on a disconnected
one `a (G) = 0` and the statement is positive semidefiniteness. -/
theorem algConn_mul_le_lap_quadratic (G : CGraph) [Nonempty G.V] (v : G.V → ℝ)
    (hv : ∑ i, v i = 0) : G.algConn * (v ⬝ᵥ v) ≤ v ⬝ᵥ (G.lapMat *ᵥ v) := by
  by_cases hconn : G.IsConnected
  · obtain ⟨w, hq, hn, hker⟩ := G.exists_rotate_lap_quadratic_of_sum_eq_zero hconn v hv
    rw [hq, hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rcases eq_or_ne (G.lapEigenvalues i) 0 with h0 | h0
    · rw [hker i h0, h0]
      simp
    · exact mul_le_mul_of_nonneg_right
        (algConn_le ((Multiset.mem_erase_of_ne h0).2 (G.lapEigenvalues_mem_lapSpectrum i)))
        (sq_nonneg _)
  · have hcard : 2 ≤ Fintype.card G.V := by
      by_contra hlt
      push_neg at hlt
      haveI : Subsingleton G.V := Fintype.card_le_one_iff_subsingleton.1 (by omega)
      have hpre : G.toSimple.Preconnected := fun x y ↦ by
        rw [Subsingleton.elim x y]
      exact hconn ⟨hpre⟩
    have h0 : G.algConn = 0 :=
      le_antisymm (not_lt.1 fun hp ↦ hconn ((G.algConn_pos_iff hcard).1 hp)) G.algConn_nonneg
    rw [h0, zero_mul]
    exact G.lap_quadratic_nonneg v

/-- **The Fiedler value is at most the average degree of any two non-adjacent vertices.**  The
test vector is `1` at one of them, `-1` at the other and `0` elsewhere; it sums to zero, has
squared norm `2`, and the quadratic form on it is `d (u) + d (v)` because `u` and `v` contribute
no edge between themselves. -/
theorem two_mul_algConn_le_degree_add_degree (G : CGraph) [Nonempty G.V] {u v : G.V}
    (huv : u ≠ v) (h : ¬ G.Adj u v) :
    2 * G.algConn ≤ (G.toSimple.degree u : ℝ) + G.toSimple.degree v := by
  set x : G.V → ℝ := fun i ↦ (if i = u then 1 else 0) - (if i = v then 1 else 0) with hx
  have hdot : ∀ y : G.V → ℝ, x ⬝ᵥ y = y u - y v := fun y ↦ by
    simp [hx, dotProduct, sub_mul, Finset.sum_sub_distrib]
  have hxu : x u = 1 := by simp [hx, huv]
  have hxv : x v = -1 := by simp [hx, Ne.symm huv]
  have hsum : ∑ i, x i = 0 := by
    simp [hx, Finset.sum_sub_distrib]
  have hnorm : x ⬝ᵥ x = 2 := by rw [hdot x, hxu, hxv]; ring
  have hmv : ∀ i : G.V, (G.lapMat *ᵥ x) i = G.lapMat i u - G.lapMat i v := fun i ↦ by
    rw [show (G.lapMat *ᵥ x) i = x ⬝ᵥ (fun j ↦ G.lapMat i j) from by
      rw [dotProduct_comm]; rfl, hdot]
  have hauv : G.lapMat u v = 0 := by
    rw [lapMat_apply_of_ne G huv, adjMat_apply, if_neg h, neg_zero]
  have havu : G.lapMat v u = 0 := by
    rw [lapMat_apply_of_ne G (Ne.symm huv), G.adjMat_symm v u, adjMat_apply, if_neg h, neg_zero]
  have hquad : x ⬝ᵥ (G.lapMat *ᵥ x) = (G.toSimple.degree u : ℝ) + G.toSimple.degree v := by
    rw [hdot, hmv, hmv, hauv, havu, lapMat_apply_self, lapMat_apply_self]
    ring
  have := G.algConn_mul_le_lap_quadratic x hsum
  rw [hnorm, hquad] at this
  linarith

/-- **The Fiedler value bounds edge expansion from below**: for every set `S` of vertices,
`a (G) |S| |Sᶜ| ≤ n · e (S, Sᶜ)`, where `e (S, Sᶜ) = ∑_{i ∈ S} ∑_{j ∉ S} A i j` counts the edges
leaving `S`.  The test vector is `|Sᶜ|` on `S` and `-|S|` off it: it sums to zero, its squared
norm is `n |S| |Sᶜ|`, and every crossing edge contributes `n ²` to the quadratic form. -/
theorem algConn_mul_card_mul_card_compl_le (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (S : Finset G.V) :
    G.algConn * ((S.card : ℝ) * (Sᶜ.card : ℝ))
      ≤ Fintype.card G.V * ∑ i ∈ S, ∑ j ∈ Sᶜ, G.adjMat i j := by
  set n : ℝ := (Fintype.card G.V : ℝ) with hn
  set a : ℝ := (S.card : ℝ) with ha
  set b : ℝ := (Sᶜ.card : ℝ) with hb
  set e : ℝ := ∑ i ∈ S, ∑ j ∈ Sᶜ, G.adjMat i j with he
  have hab : a + b = n := by
    rw [ha, hb, hn, ← Nat.cast_add, Finset.card_add_card_compl]
  set x : G.V → ℝ := fun i ↦ if i ∈ S then b else -a with hx
  have hxS : ∀ i ∈ S, x i = b := fun i hi ↦ by rw [hx]; exact if_pos hi
  have hxSc : ∀ i ∈ Sᶜ, x i = -a := fun i hi ↦ by
    rw [hx]; exact if_neg (Finset.mem_compl.1 hi)
  -- the test vector sums to zero
  have hsum : ∑ i, x i = 0 := by
    rw [← Finset.sum_add_sum_compl S, Finset.sum_congr rfl hxS, Finset.sum_congr rfl hxSc,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ha, ← hb]
    ring
  -- and has squared norm `n |S| |Sᶜ|`
  have hnorm : x ⬝ᵥ x = n * (a * b) := by
    rw [dotProduct, ← Finset.sum_add_sum_compl S,
      Finset.sum_congr rfl (fun i hi ↦ by rw [hxS i hi] :
        ∀ i ∈ S, x i * x i = b * b),
      Finset.sum_congr rfl (fun i hi ↦ by rw [hxSc i hi] :
        ∀ i ∈ Sᶜ, x i * x i = -a * -a),
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← ha, ← hb, ← hab]
    ring
  -- the quadratic form counts the crossing edges
  set f : G.V → G.V → ℝ := fun i j ↦ G.adjMat i j * (x i - x j) ^ 2 with hf
  have hS : ∀ i ∈ S, ∑ j, f i j = n ^ 2 * ∑ j ∈ Sᶜ, G.adjMat i j := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S]
    have h1 : ∑ j ∈ S, f i j = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by rw [hf]; simp only [hxS i hi, hxS j hj]; ring
    have h2 : ∑ j ∈ Sᶜ, f i j = n ^ 2 * ∑ j ∈ Sᶜ, G.adjMat i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [hf]
      simp only [hxS i hi, hxSc j hj]
      rw [show b - -a = n by linarith]
      ring
    rw [h1, h2, zero_add]
  have hSc : ∀ i ∈ Sᶜ, ∑ j, f i j = n ^ 2 * ∑ j ∈ S, G.adjMat i j := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S]
    have h1 : ∑ j ∈ S, f i j = n ^ 2 * ∑ j ∈ S, G.adjMat i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [hf]
      simp only [hxSc i hi, hxS j hj]
      rw [show -a - b = -n by linarith]
      ring
    have h2 : ∑ j ∈ Sᶜ, f i j = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by rw [hf]; simp only [hxSc i hi, hxSc j hj]; ring
    rw [h1, h2, add_zero]
  have hsymm : ∑ i ∈ Sᶜ, ∑ j ∈ S, G.adjMat i j = e := by
    rw [he, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ G.adjMat_symm j i
  have htot : ∑ i, ∑ j, f i j = 2 * (n ^ 2 * e) := by
    rw [← Finset.sum_add_sum_compl S, Finset.sum_congr rfl hS, Finset.sum_congr rfl hSc,
      ← Finset.mul_sum, ← Finset.mul_sum, hsymm, ← he]
    ring
  have hquad : x ⬝ᵥ (G.lapMat *ᵥ x) = n ^ 2 * e := by
    have h2 : 2 * (x ⬝ᵥ (G.lapMat *ᵥ x)) = ∑ i, ∑ j, f i j := G.two_mul_lap_quadratic x
    rw [htot] at h2
    linarith
  have hkey := G.algConn_mul_le_lap_quadratic x hsum
  rw [hnorm, hquad] at hkey
  have hnpos : (0 : ℝ) < n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  have hcancel : n * (G.algConn * (a * b)) ≤ n * (n * e) := by nlinarith
  exact le_of_mul_le_mul_left hcancel hnpos

/-- **A spectral gap forbids a cheap cut**: for a set `S` of at most half the vertices, the number
of edges leaving `S` is at least `a (G) |S| / 2`.  This is the previous bound with `|Sᶜ| ≥ n / 2`
substituted and the order cancelled. -/
theorem algConn_mul_card_le_two_mul_cut (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (S : Finset G.V) (hS : 2 * S.card ≤ Fintype.card G.V) :
    G.algConn * S.card ≤ 2 * ∑ i ∈ S, ∑ j ∈ Sᶜ, G.adjMat i j := by
  have hkey := G.algConn_mul_card_mul_card_compl_le S
  have hb : (Sᶜ.card : ℝ) = (Fintype.card G.V : ℝ) - S.card := by
    have : (S.card : ℝ) + (Sᶜ.card : ℝ) = Fintype.card G.V := by
      rw [← Nat.cast_add, Finset.card_add_card_compl]
    linarith
  rw [hb] at hkey
  have hhalf : 2 * (S.card : ℝ) ≤ (Fintype.card G.V : ℝ) := by exact_mod_cast hS
  have hnpos : (0 : ℝ) < (Fintype.card G.V : ℝ) := by exact_mod_cast Fintype.card_pos
  have h3 : 0 ≤ G.algConn * (S.card : ℝ) * ((Fintype.card G.V : ℝ) - 2 * S.card) :=
    mul_nonneg (mul_nonneg G.algConn_nonneg (Nat.cast_nonneg _)) (by linarith)
  refine le_of_mul_le_mul_left ?_ hnpos
  nlinarith [hkey, h3]

/-- **Fiedler's inequality for a graph that is not complete**: `a (G) ≤ δ (G)`.  Read in the
complement, `Δ + 1 ≤ μ_max` says `n - 1 - δ (G) + 1 ≤ n - a (G)`; the hypothesis is exactly what
`Δ + 1 ≤ μ_max` needs, namely that `Ḡ` has an edge. -/
theorem algConn_le_minDeg (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (h : 2 ≤ Fintype.card G.V) (hc : 0 < (compl G).E) :
    G.algConn ≤ G.minDeg := by
  haveI : Nonempty (compl G).V := ‹Nonempty G.V›
  have h1 : ((compl G).maxDeg : ℝ) + 1 ≤ (compl G).lapLambdaMax :=
    (compl G).maxDeg_add_one_le_lapLambdaMax hc
  rw [G.lapLambdaMax_compl h] at h1
  have hδ : G.minDeg ≤ Fintype.card G.V - 1 :=
    le_trans G.minDeg_le_maxDeg (by have := G.maxDeg_lt_card (Classical.arbitrary G.V); omega)
  have h1' : (1 : ℕ) ≤ Fintype.card G.V := by omega
  have h2 : ((compl G).maxDeg : ℝ) = (Fintype.card G.V : ℝ) - 1 - G.minDeg := by
    rw [maxDeg_compl G (Classical.arbitrary G.V), Nat.cast_sub hδ, Nat.cast_sub h1']
    push_cast
    ring
  rw [h2] at h1
  linarith

/-- **Fiedler's bound**, in the form that also covers the complete graph: `(n - 1) · a ≤ n · δ`.
For `K_n` it is an equality, `a = n` and `δ = n - 1`; for every other graph the sharper
`algConn_le_minDeg` applies. -/
theorem card_sub_one_mul_algConn_le_card_mul_minDeg (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (h : 2 ≤ Fintype.card G.V) :
    ((Fintype.card G.V : ℝ) - 1) * G.algConn ≤ Fintype.card G.V * G.minDeg := by
  haveI : Nonempty (compl G).V := ‹Nonempty G.V›
  have hn : (2 : ℝ) ≤ Fintype.card G.V := by exact_mod_cast h
  have hδ0 : (0 : ℝ) ≤ G.minDeg := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (compl G).E with h0 | hpos
  · -- the complement is edgeless, so `G` is complete: `a = n` and `δ = n - 1`
    have hmax : (compl G).maxDeg = 0 := by
      have := (compl G).maxDeg_le_two_mul_E (Classical.arbitrary G.V)
      omega
    have hδ : Fintype.card G.V - 1 ≤ G.minDeg := by
      have := maxDeg_compl G (Classical.arbitrary G.V)
      omega
    have hδ' : (Fintype.card G.V : ℝ) - 1 ≤ G.minDeg := by
      have h1' : (1 : ℕ) ≤ Fintype.card G.V := by omega
      have hc : ((Fintype.card G.V - 1 : ℕ) : ℝ) ≤ (G.minDeg : ℝ) := by exact_mod_cast hδ
      rwa [Nat.cast_sub h1', Nat.cast_one] at hc
    have hlam : (compl G).lapLambdaMax ≤ 0 := by
      have := (compl G).lapLambdaMax_le_two_mul_maxDeg
      rw [hmax] at this
      simpa using this
    rw [G.lapLambdaMax_compl h] at hlam
    have hac : G.algConn ≤ Fintype.card G.V := G.algConn_le_card h
    have haeq : G.algConn = Fintype.card G.V := le_antisymm hac (by linarith)
    rw [haeq]
    nlinarith
  · have := G.algConn_le_minDeg h hpos
    nlinarith [G.algConn_nonneg]

/-- **Fiedler's bound in its usual form**: `a (G) ≤ n / (n - 1) · δ (G)`. -/
theorem algConn_le_div_mul_minDeg (G : CGraph) [Nonempty G.V] [DecidableEq G.V]
    (h : 2 ≤ Fintype.card G.V) :
    G.algConn ≤ (Fintype.card G.V : ℝ) / ((Fintype.card G.V : ℝ) - 1) * G.minDeg := by
  have hn : (2 : ℝ) ≤ Fintype.card G.V := by exact_mod_cast h
  have hpos : (0 : ℝ) < (Fintype.card G.V : ℝ) - 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith [G.card_sub_one_mul_algConn_le_card_mul_minDeg h]

/-- **The largest Laplacian eigenvalue of a join is its order.**  A join has a disconnected
complement, so this is `algConn_compl` read backwards; here it is read straight off
`lapSpectrum_join`. -/
theorem lapLambdaMax_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (join G H).lapLambdaMax = (Fintype.card G.V : ℝ) + Fintype.card H.V := by
  have hG0 : (0 : ℝ) ≤ Fintype.card G.V := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) ≤ Fintype.card H.V := Nat.cast_nonneg _
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_join]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · intro x hx
    rw [lapSpectrum_join, Multiset.mem_cons, Multiset.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · linarith
    · linarith
    rcases Multiset.mem_add.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := G.le_card_of_mem_lapSpectrum (Multiset.mem_of_mem_erase hy)
      linarith
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := H.le_card_of_mem_lapSpectrum (Multiset.mem_of_mem_erase hy)
      linarith

/-- **The algebraic connectivity of a join**: each factor's Fiedler value shifted by the order of
the other factor, whichever is smaller.  The order `n + m` itself is never the smallest, since
`a (G) ≤ n`. -/
theorem algConn_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : 2 ≤ Fintype.card G.V) (hH : 2 ≤ Fintype.card H.V) :
    (join G H).algConn
      = min (G.algConn + Fintype.card H.V) (H.algConn + Fintype.card G.V) := by
  haveI : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  haveI : Nonempty H.V := Fintype.card_pos_iff.1 (by omega)
  have hmemG : G.algConn ∈ G.lapSpectrum.erase 0 := G.algConn_mem_erase hG
  have hmemH : H.algConn ∈ H.lapSpectrum.erase 0 := H.algConn_mem_erase hH
  have hGle : G.algConn ≤ Fintype.card G.V := G.algConn_le_card hG
  have hHle : H.algConn ≤ Fintype.card H.V := H.algConn_le_card hH
  have herase : (join G H).lapSpectrum.erase 0
      = ((Fintype.card G.V : ℝ) + Fintype.card H.V)
          ::ₘ ((G.lapSpectrum.erase 0).map (fun x ↦ x + (Fintype.card H.V : ℝ))
             + (H.lapSpectrum.erase 0).map (fun x ↦ x + (Fintype.card G.V : ℝ))) := by
    rw [lapSpectrum_join, Multiset.erase_cons_head]
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase]
    refine Multiset.mem_cons_of_mem ?_
    rcases le_total (G.algConn + Fintype.card H.V) (H.algConn + Fintype.card G.V) with hle | hle
    · rw [min_eq_left hle]
      exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ hmemG))
    · rw [min_eq_right hle]
      exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ hmemH))
  · intro x hx
    rw [herase, Multiset.mem_cons] at hx
    have hminG := min_le_left (G.algConn + (Fintype.card H.V : ℝ))
      (H.algConn + (Fintype.card G.V : ℝ))
    have hminH := min_le_right (G.algConn + (Fintype.card H.V : ℝ))
      (H.algConn + (Fintype.card G.V : ℝ))
    rcases hx with rfl | hx
    · linarith
    rcases Multiset.mem_add.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := G.algConn_le hy
      linarith
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := H.algConn_le hy
      linarith

/-! ### The Laplacian of a cartesian product -/

/-- The Laplacian of a cartesian product is `L G ⊗ I + I ⊗ L H`, the same shape as
`adjMat_cartesianProduct`: the degree of `(g, h)` is `deg g + deg h`. -/
theorem lapMat_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).lapMat
      = G.lapMat ⊗ₖ (1 : Matrix H.V H.V ℝ) + (1 : Matrix G.V G.V ℝ) ⊗ₖ H.lapMat := by
  ext p q
  rw [lapMat_eq_diagonal_sub, Matrix.sub_apply, adjMat_cartesianProduct]
  rcases eq_or_ne p q with rfl | hpq
  · simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply_eq, lapMat_apply_self, adjMat_apply, G.adj_self, H.adj_self,
      degree_cartesianProduct]
    push_cast
    norm_num
  · simp only [Matrix.diagonal_apply, if_neg hpq]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h ↦ hpq (Prod.ext h1 h)
      simp [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2,
        H.lapMat_apply_of_ne h2]
    · by_cases h2 : p.2 = q.2
      · simp [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2,
          G.lapMat_apply_of_ne h1]
      · simp [Matrix.add_apply, Matrix.kroneckerMap_apply, h1, h2]

/-- **The Laplacian eigenvalues of a cartesian product are the sums of the Laplacian
eigenvalues**, exactly as for the adjacency matrix (`spectrum_cartesianProduct`): the two
Laplacians are simultaneously diagonalised by the Kronecker product of their eigenbases. -/
theorem lapSpectrum_cartesianProduct (G H : CGraph) [dG : DecidableEq G.V] [dH : DecidableEq H.V] :
    (cartesianProduct G H).lapSpectrum
      = Finset.univ.val.map
          (fun p : G.V × H.V ↦ G.lapEigenvalues p.1 + H.lapEigenvalues p.2) := by
  have e1 : dG = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have e2 : dH = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst e1; subst e2
  obtain ⟨U₁, h₁, h₁', e₁⟩ := exists_orthogonal_lap_diagonal G
  obtain ⟨U₂, h₂, h₂', e₂⟩ := exists_orthogonal_lap_diagonal H
  have k₁ : G.lapMat * U₁ = U₁ * Matrix.diagonal G.lapEigenvalues := by
    rw [← e₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₁', Matrix.one_mul]
  have k₂ : H.lapMat * U₂ = U₂ * Matrix.diagonal H.lapEigenvalues := by
    rw [← e₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h₂', Matrix.one_mul]
  have hdiag : Matrix.diagonal G.lapEigenvalues ⊗ₖ (1 : Matrix H.V H.V ℝ)
      + (1 : Matrix G.V G.V ℝ) ⊗ₖ Matrix.diagonal H.lapEigenvalues
      = Matrix.diagonal
          (fun p : G.V × H.V ↦ G.lapEigenvalues p.1 + H.lapEigenvalues p.2) := by
    ext p q
    by_cases hp1 : p.1 = q.1 <;> by_cases hp2 : p.2 = q.2 <;>
      simp [Matrix.kroneckerMap, Matrix.one_apply, Matrix.diagonal_apply, Prod.ext_iff, hp1, hp2]
  have key : (U₁ * Matrix.diagonal G.lapEigenvalues) ⊗ₖ U₂
      + U₁ ⊗ₖ (U₂ * Matrix.diagonal H.lapEigenvalues)
      = (U₁ ⊗ₖ U₂) * Matrix.diagonal
          (fun p : G.V × H.V ↦ G.lapEigenvalues p.1 + H.lapEigenvalues p.2) := by
    rw [← hdiag, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.mul_one]
  refine lapSpectrum_eq_of_conj (P := U₁ ⊗ₖ U₂) (Q := U₁ᵀ ⊗ₖ U₂ᵀ) ?_ ?_ ?_
  · rw [← Matrix.mul_kronecker_mul, h₁', h₂', Matrix.one_kronecker_one]
    congr!
  · rw [← Matrix.mul_kronecker_mul, h₁, h₂, Matrix.one_kronecker_one]
    congr!
  · rw [lapMat_cartesianProduct, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, k₁, k₂]
    simp only [Matrix.one_mul]
    rw [key]
    congr!

theorem lapSpectrum_cartesianProduct' (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).lapSpectrum
      = (G.lapSpectrum ×ˢ H.lapSpectrum).map (fun p ↦ p.1 + p.2) := by
  rw [lapSpectrum_cartesianProduct, lapSpectrum_eq_map, lapSpectrum_eq_map,
    ← map_product_apply₂, ← Finset.univ_product_univ, Finset.product_val]

/-- **The largest Laplacian eigenvalue of a cartesian product** is the sum of the two. -/
theorem lapLambdaMax_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] :
    (cartesianProduct G H).lapLambdaMax = G.lapLambdaMax + H.lapLambdaMax := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_cartesianProduct']
    refine Multiset.mem_map.2 ⟨(G.lapLambdaMax, H.lapLambdaMax), ?_, rfl⟩
    exact Multiset.mem_product.2
      ⟨lapLambdaMax_mem_lapSpectrum G, lapLambdaMax_mem_lapSpectrum H⟩
  · intro x hx
    rw [lapSpectrum_cartesianProduct'] at hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hp1, hp2⟩ := Multiset.mem_product.1 hp
    exact add_le_add (le_lapLambdaMax hp1) (le_lapLambdaMax hp2)

/-- **The algebraic connectivity of a cartesian product** is the smaller of the two: `a (G) + 0`
and `0 + a (H)` are both eigenvalues of the product, and every other nonzero sum is at least one
of them.  No connectivity hypothesis is needed — if either factor is disconnected both sides
are `0`. -/
theorem algConn_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : 2 ≤ Fintype.card G.V) (hH : 2 ≤ Fintype.card H.V) :
    (cartesianProduct G H).algConn = min G.algConn H.algConn := by
  haveI : Nonempty G.V := Fintype.card_pos_iff.1 (by omega)
  haveI : Nonempty H.V := Fintype.card_pos_iff.1 (by omega)
  set gs : Multiset ℝ := G.lapSpectrum.erase 0 with hgs
  set hs : Multiset ℝ := H.lapSpectrum.erase 0 with hhs
  have hGc : G.lapSpectrum = 0 ::ₘ gs := (Multiset.cons_erase G.zero_mem_lapSpectrum).symm
  have hHc : H.lapSpectrum = 0 ::ₘ hs := (Multiset.cons_erase H.zero_mem_lapSpectrum).symm
  have herase : (cartesianProduct G H).lapSpectrum.erase 0
      = hs + (gs ×ˢ (0 ::ₘ hs)).map (fun p ↦ p.1 + p.2) := by
    rw [lapSpectrum_cartesianProduct']
    conv_lhs => rw [hGc, hHc]
    rw [Multiset.cons_product, Multiset.map_add, Multiset.map_map, Multiset.map_cons]
    simp only [Function.comp_def, zero_add, add_zero, Multiset.map_id']
    rw [Multiset.cons_add, Multiset.erase_cons_head]
  have hmemG : G.algConn ∈ gs := G.algConn_mem_erase hG
  have hmemH : H.algConn ∈ hs := H.algConn_mem_erase hH
  have hmem : min G.algConn H.algConn ∈ (cartesianProduct G H).lapSpectrum.erase 0 := by
    rw [herase]
    rcases le_total G.algConn H.algConn with hle | hle
    · rw [min_eq_left hle]
      refine Multiset.mem_add.2 (Or.inr ?_)
      refine Multiset.mem_map.2 ⟨(G.algConn, 0), ?_, by ring⟩
      exact Multiset.mem_product.2 ⟨hmemG, Multiset.mem_cons_self _ _⟩
    · rw [min_eq_right hle]
      exact Multiset.mem_add.2 (Or.inl hmemH)
  refine algConn_eq_of_isLeast hmem ?_
  intro x hx
  rw [herase] at hx
  rcases Multiset.mem_add.1 hx with hx | hx
  · have := H.algConn_le hx
    have hmin := min_le_right G.algConn H.algConn
    linarith
  · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hp1, hp2⟩ := Multiset.mem_product.1 hp
    have h1 := G.algConn_le hp1
    have h2 : 0 ≤ p.2 := by
      rcases Multiset.mem_cons.1 hp2 with heq | hp2
      · exact le_of_eq heq.symm
      · exact H.nonneg_of_mem_lapSpectrum (Multiset.mem_of_mem_erase hp2)
    have hmin := min_le_left G.algConn H.algConn
    linarith

/-- **The Laplacian spectrum of a regular graph with a two-eigenvalue adjacency spectrum.**
Every strongly regular graph has this shape, so this is the bridge from `spectrum_isSRGWith`
to the Laplacian. -/
theorem lapSpectrum_of_spectrum_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) {f g : ℕ}
    {d r s : ℝ} (hd : (k : ℝ) = d)
    (hspec : G.spectrum = d ::ₘ (Multiset.replicate f r + Multiset.replicate g s)) :
    G.lapSpectrum
      = 0 ::ₘ (Multiset.replicate f (d - r) + Multiset.replicate g (d - s)) := by
  subst hd
  rw [lapSpectrum_of_isRegularWith h, hspec, Multiset.map_cons, Multiset.map_add,
    Multiset.map_replicate, Multiset.map_replicate, sub_self]

/-- **The largest Laplacian eigenvalue of a strongly regular graph is `k - s`.** -/
theorem lapLambdaMax_of_spectrum_eq {G : CGraph} [Nonempty G.V] {k : ℕ} (h : G.IsRegularWith k)
    {f g : ℕ} {d r s : ℝ} (hd : (k : ℝ) = d) (hg : 0 < g) (hsr : s ≤ r) (hsk : s ≤ d)
    (hspec : G.spectrum = d ::ₘ (Multiset.replicate f r + Multiset.replicate g s)) :
    G.lapLambdaMax = d - s := by
  have hlap := lapSpectrum_of_spectrum_eq h hd hspec
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [hlap]
    refine Multiset.mem_cons_of_mem (Multiset.mem_add.2 (Or.inr ?_))
    exact Multiset.mem_replicate.2 ⟨hg.ne', rfl⟩
  · intro x hx
    rw [hlap] at hx
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · linarith
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; linarith
    · rw [Multiset.eq_of_mem_replicate hx]

/-- **The algebraic connectivity of a strongly regular graph is `k - r`.** -/
theorem algConn_of_spectrum_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k)
    {f g : ℕ} {d r s : ℝ} (hd : (k : ℝ) = d) (hf : 0 < f) (hsr : s ≤ r)
    (hspec : G.spectrum = d ::ₘ (Multiset.replicate f r + Multiset.replicate g s)) :
    G.algConn = d - r := by
  have hlap := lapSpectrum_of_spectrum_eq h hd hspec
  have herase : G.lapSpectrum.erase 0
      = Multiset.replicate f (d - r) + Multiset.replicate g (d - s) := by
    rw [hlap, Multiset.erase_cons_head]
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨hf.ne', rfl⟩))
  · intro x hx
    rw [herase] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
    · rw [Multiset.eq_of_mem_replicate hx]; linarith

/-! ### The Laplacian of the named strongly regular graphs -/

/-- **The Laplacian spectrum of the Petersen graph**: `0`, `2` five times, `5` four times. -/
theorem lapSpectrum_petersen :
    SRG.petersen.lapSpectrum = 0 ::ₘ (Multiset.replicate 5 2 + Multiset.replicate 4 5) := by
  have h := lapSpectrum_of_spectrum_eq (k := 3) SRG.petersen_srg.regular (by norm_num)
    spectrum_petersen
  rw [h]
  norm_num

theorem algConn_petersen : SRG.petersen.algConn = 2 := by
  have h := algConn_of_spectrum_eq (k := 3) SRG.petersen_srg.regular (f := 5) (g := 4)
    (by norm_num) (by norm_num) (by norm_num) spectrum_petersen
  rw [h]
  norm_num

theorem lapLambdaMax_petersen : SRG.petersen.lapLambdaMax = 5 := by
  haveI : Nonempty SRG.petersen.V :=
    Fintype.card_pos_iff.1 (by rw [SRG.petersen_srg.card]; norm_num)
  have h := lapLambdaMax_of_spectrum_eq (k := 3) SRG.petersen_srg.regular (f := 5) (g := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) spectrum_petersen
  rw [h]
  norm_num

/-- The regularity of the cocktail party graph, with the degree in normal form. -/
theorem isRegularWith_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).IsRegularWith (2 * m + 2) := by
  have h := (isSRGWith_cocktailParty (m + 2)).regular
  rwa [show 2 * (m + 2) - 2 = 2 * m + 2 from by omega] at h

/-- **The Laplacian spectrum of the cocktail party graph `K_{n×2}`**: `0` once, `2n - 2` with
multiplicity `n` and `2n` with multiplicity `n - 1`. -/
theorem lapSpectrum_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).lapSpectrum
      = 0 ::ₘ (Multiset.replicate (m + 2) (2 * (m : ℝ) + 2)
          + Multiset.replicate (m + 1) (2 * (m : ℝ) + 4)) := by
  have h := lapSpectrum_of_spectrum_eq (isRegularWith_cocktailParty m) (by push_cast; ring)
    (spectrum_cocktailParty m)
  rw [h]
  ring_nf

theorem algConn_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).algConn = 2 * (m : ℝ) + 2 := by
  have h := algConn_of_spectrum_eq (isRegularWith_cocktailParty m) (f := m + 2) (g := m + 1)
    (by push_cast; ring) (by omega) (by norm_num) (spectrum_cocktailParty m)
  rw [h]
  ring

theorem lapLambdaMax_cocktailParty (m : ℕ) :
    (cocktailParty (m + 2)).lapLambdaMax = 2 * (m : ℝ) + 4 := by
  haveI : Nonempty (cocktailParty (m + 2)).V :=
    Fintype.card_pos_iff.1 (by rw [(isSRGWith_cocktailParty (m + 2)).card]; omega)
  have h := lapLambdaMax_of_spectrum_eq (isRegularWith_cocktailParty m) (f := m + 2) (g := m + 1)
    (by push_cast; ring) (by omega) (by norm_num)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (spectrum_cocktailParty m)
  rw [h]
  ring

theorem isRegularWith_rook (k : ℕ) : (rook (k + 2) (k + 2)).IsRegularWith (2 * k + 2) := by
  have h := (isSRGWith_rook (k + 2)).regular
  rwa [show 2 * (k + 2 - 1) = 2 * k + 2 from by omega] at h

/-- **The Laplacian spectrum of the rook's graph `K_n □ K_n`**: `0` once, `n` with multiplicity
`2 (n - 1)` and `2n` with multiplicity `(n - 1) ²` — exactly what `lapSpectrum_cartesianProduct`
gives for `K_n □ K_n`. -/
theorem lapSpectrum_rook (k : ℕ) :
    (rook (k + 2) (k + 2)).lapSpectrum
      = 0 ::ₘ (Multiset.replicate (2 * (k + 1)) ((k : ℝ) + 2)
          + Multiset.replicate ((k + 1) ^ 2) (2 * (k : ℝ) + 4)) := by
  have h := lapSpectrum_of_spectrum_eq (isRegularWith_rook k) (by push_cast; ring)
    (spectrum_rook k)
  rw [h]
  ring_nf

theorem algConn_rook (k : ℕ) : (rook (k + 2) (k + 2)).algConn = (k : ℝ) + 2 := by
  have h := algConn_of_spectrum_eq (isRegularWith_rook k) (f := 2 * (k + 1)) (g := (k + 1) ^ 2)
    (by push_cast; ring) (by omega) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (spectrum_rook k)
  rw [h]
  ring

theorem lapLambdaMax_rook (k : ℕ) :
    (rook (k + 2) (k + 2)).lapLambdaMax = 2 * (k : ℝ) + 4 := by
  haveI : Nonempty (rook (k + 2) (k + 2)).V :=
    Fintype.card_pos_iff.1 (by rw [(isSRGWith_rook (k + 2)).card]; positivity)
  have h := lapLambdaMax_of_spectrum_eq (isRegularWith_rook k) (f := 2 * (k + 1))
    (g := (k + 1) ^ 2) (by push_cast; ring) (by positivity)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (spectrum_rook k)
  rw [h]
  ring

theorem isRegularWith_triangular (m : ℕ) :
    (triangular (m + 4)).IsRegularWith (2 * m + 4) := by
  have h := (isSRGWith_triangular (m + 4) (by omega)).regular
  rwa [show 2 * (m + 4 - 2) = 2 * m + 4 from by omega] at h

/-- **The Laplacian spectrum of the triangular graph `T(n) = L(Kₙ)`**: `0` once, `n` with
multiplicity `n - 1`, and `2n - 2` with multiplicity `C(n, 2) - n`. -/
theorem lapSpectrum_triangular (m : ℕ) :
    (triangular (m + 4)).lapSpectrum
      = 0 ::ₘ (Multiset.replicate (m + 3) ((m : ℝ) + 4)
          + Multiset.replicate ((m + 4).choose 2 - (m + 4)) (2 * (m : ℝ) + 6)) := by
  have h := lapSpectrum_of_spectrum_eq (isRegularWith_triangular m) (by push_cast; ring)
    (spectrum_triangular m)
  rw [h]
  ring_nf

theorem algConn_triangular (m : ℕ) : (triangular (m + 4)).algConn = (m : ℝ) + 4 := by
  have h := algConn_of_spectrum_eq (isRegularWith_triangular m) (f := m + 3)
    (g := (m + 4).choose 2 - (m + 4)) (by push_cast; ring) (by omega)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (spectrum_triangular m)
  rw [h]
  ring

theorem lapLambdaMax_triangular (m : ℕ) :
    (triangular (m + 4)).lapLambdaMax = 2 * (m : ℝ) + 6 := by
  haveI : Nonempty (triangular (m + 4)).V :=
    Fintype.card_pos_iff.1
      (by rw [(isSRGWith_triangular (m + 4) (by omega)).card]; exact Nat.choose_pos (by omega))
  have hch : m + 4 < (m + 4).choose 2 := by
    have h1 : (m + 4).choose 2 = (m + 3) + ((m + 2) + (m + 2).choose 2) := by
      rw [Nat.choose_succ_succ (m + 3) 1, Nat.choose_succ_succ (m + 2) 1]
      simp [Nat.choose_one_right]
    have h2 : 0 < (m + 2).choose 2 := Nat.choose_pos (by omega)
    omega
  have h := lapLambdaMax_of_spectrum_eq (isRegularWith_triangular m) (f := m + 3)
    (g := (m + 4).choose 2 - (m + 4)) (by push_cast; ring) (by omega)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) (spectrum_triangular m)
  rw [h]
  ring

theorem isRegularWith_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).IsRegularWith (2 * t) := by
  haveI : NeZero (4 * t + 1) := ⟨by omega⟩
  have h := (isSRGWith_paley (4 * t + 1) (by omega)).regular
  rwa [show (4 * t + 1 - 1) / 2 = 2 * t from by omega] at h

/-- **The Laplacian spectrum of the Paley graph** `P(q)`, `q = 4t + 1` prime: `0` once, and
`(q ∓ √q) / 2` each with multiplicity `(q - 1) / 2`. -/
theorem lapSpectrum_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).lapSpectrum
      = 0 ::ₘ
        (Multiset.replicate (2 * t) ((4 * (t : ℝ) + 1 - Real.sqrt (4 * (t : ℝ) + 1)) / 2)
          + Multiset.replicate (2 * t)
              ((4 * (t : ℝ) + 1 + Real.sqrt (4 * (t : ℝ) + 1)) / 2)) := by
  have h := lapSpectrum_of_spectrum_eq (isRegularWith_paley t ht) (by push_cast; ring)
    (spectrum_paley t ht)
  rw [h]
  ring_nf

theorem algConn_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).algConn
      = (4 * (t : ℝ) + 1 - Real.sqrt (4 * (t : ℝ) + 1)) / 2 := by
  have hq : 0 < Real.sqrt (4 * (t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have h := algConn_of_spectrum_eq (isRegularWith_paley t ht) (f := 2 * t) (g := 2 * t)
    (by push_cast; ring) (by omega) (by linarith) (spectrum_paley t ht)
  rw [h]
  ring

theorem lapLambdaMax_paley (t : ℕ) (ht : 0 < t) [Fact (Nat.Prime (4 * t + 1))] :
    (paley (4 * t + 1)).lapLambdaMax
      = (4 * (t : ℝ) + 1 + Real.sqrt (4 * (t : ℝ) + 1)) / 2 := by
  haveI : NeZero (4 * t + 1) := ⟨by omega⟩
  haveI : Nonempty (paley (4 * t + 1)).V :=
    Fintype.card_pos_iff.1 (by rw [(isSRGWith_paley (4 * t + 1) (by omega)).card]; omega)
  have hq : 0 < Real.sqrt (4 * (t : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hqle : Real.sqrt (4 * (t : ℝ) + 1) ≤ 4 * (t : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (t : ℝ) + 1 by positivity), hq]
  have h := lapLambdaMax_of_spectrum_eq (isRegularWith_paley t ht) (f := 2 * t) (g := 2 * t)
    (by push_cast; ring) (by omega) (by linarith) (by linarith) (spectrum_paley t ht)
  rw [h]
  ring

/-! ### Laplacian cospectrality -/

@[simp, toIsoGraph] theorem natDegree_lapCharpoly (G : CGraph) :
    G.lapCharpoly.natDegree = Fintype.card G.V :=
  Matrix.charpoly_natDegree_eq_dim _

theorem lapCharpoly_eq_prod (G : CGraph) :
    G.lapCharpoly = ∏ i, (X - C (G.lapEigenvalues i)) :=
  G.isHermitian_lapMat.charpoly_eq

theorem lapCharpoly_eq_prod_lapSpectrum (G : CGraph) :
    G.lapCharpoly = (G.lapSpectrum.map (fun x ↦ X - C x)).prod := by
  rw [lapSpectrum_eq_map, Multiset.map_map, lapCharpoly_eq_prod]
  rfl

/-- Two graphs are **Laplacian cospectral** when their Laplacian characteristic polynomials
agree. -/
def LapCospectral (G H : CGraph) : Prop := G.lapCharpoly = H.lapCharpoly

end CGraph

namespace IsoGraph

/-- Two isomorphism classes are **Laplacian cospectral** when their Laplacian characteristic
polynomials agree. -/
def LapCospectral (G H : IsoGraph) : Prop := G.lapCharpoly = H.lapCharpoly

@[simp, isoTransfer] theorem lapCospectral_mk (G H : CGraph) :
    LapCospectral ⟦G⟧ ⟦H⟧ ↔ G.LapCospectral H := Iff.rfl

end IsoGraph

namespace CGraph

@[toIsoGraph]
theorem LapCospectral.lapSpectrum_eq {G H : CGraph} (h : LapCospectral G H) :
    G.lapSpectrum = H.lapSpectrum := by
  rw [lapSpectrum, lapSpectrum, h]

theorem LapCospectral.refl (G : CGraph) : LapCospectral G G := rfl

theorem LapCospectral.symm {G H : CGraph} (h : LapCospectral G H) : LapCospectral H G := Eq.symm h

theorem LapCospectral.trans {G H K : CGraph} (h : LapCospectral G H) (h' : LapCospectral H K) :
    LapCospectral G K := Eq.trans h h'

theorem LapCospectral.of_iso {G H : CGraph} (i : G ≃cg H) : LapCospectral G H :=
  lapCharpoly_congr i

@[toIsoGraph]
theorem lapCospectral_iff_lapSpectrum_eq (G H : CGraph) :
    G.LapCospectral H ↔ G.lapSpectrum = H.lapSpectrum := by
  refine ⟨LapCospectral.lapSpectrum_eq, fun h ↦ ?_⟩
  rw [LapCospectral, lapCharpoly_eq_prod_lapSpectrum, lapCharpoly_eq_prod_lapSpectrum, h]

/-- **Laplacian cospectral graphs have the same number of vertices.** -/
theorem LapCospectral.card_eq {G H : CGraph} (h : LapCospectral G H) :
    Fintype.card G.V = Fintype.card H.V := by
  rw [← natDegree_lapCharpoly, ← natDegree_lapCharpoly, h]

/-- **Laplacian cospectral graphs have the same number of edges**, by the trace. -/
@[toIsoGraph]
theorem LapCospectral.E_eq {G H : CGraph} (h : LapCospectral G H) : G.E = H.E := by
  have h2 : (2 : ℝ) * G.E = 2 * H.E := by
    rw [← sum_lapSpectrum, ← sum_lapSpectrum, h.lapSpectrum_eq]
  have : (G.E : ℝ) = H.E := by linarith
  exact_mod_cast this

/-- **Laplacian cospectral graphs have the same number of connected components** — a statement
with no analogue for the adjacency spectrum, which needs regularity to see connectedness. -/
@[toIsoGraph]
theorem LapCospectral.numComponents_eq {G H : CGraph} (h : LapCospectral G H) :
    G.numComponents = H.numComponents := by
  rw [← count_zero_lapSpectrum, ← count_zero_lapSpectrum, h.lapSpectrum_eq]

/-- **Connectedness is a Laplacian spectral invariant.** -/
@[toIsoGraph]
theorem LapCospectral.isConnected {G H : CGraph} (h : LapCospectral G H) (hG : G.IsConnected) :
    H.IsConnected := by
  rw [← count_zero_lapSpectrum_eq_one_iff] at hG ⊢
  rw [← h.lapSpectrum_eq]
  exact hG

/-- **Laplacian cospectral graphs have the same sum of squared degrees**, by the second moment:
`∑ μ ² = 2 E + ∑ d (i) ²` and the number of edges is already an invariant. -/
theorem LapCospectral.sum_sq_degrees_eq {G H : CGraph} (h : LapCospectral G H) :
    ∑ i, (G.toSimple.degree i : ℝ) ^ 2 = ∑ i, (H.toSimple.degree i : ℝ) ^ 2 := by
  have h2 : (G.lapSpectrum.map (· ^ 2)).sum = (H.lapSpectrum.map (· ^ 2)).sum := by
    rw [h.lapSpectrum_eq]
  rw [sum_sq_lapSpectrum, sum_sq_lapSpectrum, h.E_eq] at h2
  linarith

/-- **Regularity is a Laplacian spectral invariant.**  The first two moments pin the degree
sequence of a Laplacian cospectral partner of a `k`-regular graph: its degrees sum to `n k` and
its squared degrees to `n k ²`, so `∑ (d (i) - k) ² = 0` and every degree is `k`.  The adjacency
twin `Cospectral.isRegularWith` needs the extremal eigenvalue instead. -/
@[toIsoGraph]
theorem LapCospectral.isRegularWith {G H : CGraph} (h : LapCospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : H.IsRegularWith k := by
  classical
  have hcard : Fintype.card H.V = Fintype.card G.V := h.card_eq.symm
  -- the degrees of `H` sum to `n k`
  have hdegsum : ∑ i, H.toSimple.degree i = ∑ i, G.toSimple.degree i := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.sum_degrees_eq_twice_card_edges]
    have hE1 : G.E = G.toSimple.edgeFinset.card := rfl
    have hE2 : H.E = H.toSimple.edgeFinset.card := rfl
    have := h.E_eq
    omega
  have hGsum : ∑ i, G.toSimple.degree i = Fintype.card G.V * k := by
    rw [Finset.sum_congr rfl fun i _ ↦ hG i, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hlin : ∑ i, (H.toSimple.degree i : ℝ) = Fintype.card G.V * (k : ℝ) := by
    rw [← Nat.cast_sum, hdegsum, hGsum]
    push_cast
    ring
  -- and their squares to `n k ²`
  have hGsq : ∑ i, (G.toSimple.degree i : ℝ) ^ 2 = Fintype.card G.V * (k : ℝ) ^ 2 := by
    have hpt : ∀ i : G.V, (G.toSimple.degree i : ℝ) ^ 2 = (k : ℝ) ^ 2 := fun i ↦ by rw [hG i]
    rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsq : ∑ i, (H.toSimple.degree i : ℝ) ^ 2 = Fintype.card G.V * (k : ℝ) ^ 2 := by
    rw [← h.sum_sq_degrees_eq]
    exact hGsq
  -- so the variance vanishes
  have hvar : ∑ i, ((H.toSimple.degree i : ℝ) - k) ^ 2 = 0 := by
    have hpt : ∀ i : H.V, ((H.toSimple.degree i : ℝ) - k) ^ 2
        = (H.toSimple.degree i : ℝ) ^ 2 - 2 * k * (H.toSimple.degree i : ℝ) + k ^ 2 :=
      fun i ↦ by ring
    rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsq, hlin, hcard]
    ring
  intro v
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg
    ((H.toSimple.degree i : ℝ) - k)).1 hvar v (Finset.mem_univ v)
  have h1 : (H.toSimple.degree v : ℝ) = (k : ℝ) := by
    have := sq_eq_zero_iff.1 h0
    linarith
  exact_mod_cast h1

/-- **Laplacian cospectral graphs have the same algebraic connectivity**, straight from the
definition. -/
@[toIsoGraph]
theorem LapCospectral.algConn_eq {G H : CGraph} (h : LapCospectral G H) :
    G.algConn = H.algConn := by
  rw [algConn, algConn, h.lapSpectrum_eq]

/-- **Laplacian cospectral graphs have the same largest Laplacian eigenvalue**, likewise. -/
@[toIsoGraph]
theorem LapCospectral.lapLambdaMax_eq {G H : CGraph} (h : LapCospectral G H) :
    G.lapLambdaMax = H.lapLambdaMax := by
  rw [lapLambdaMax, lapLambdaMax, h.lapSpectrum_eq]

/-- For regular graphs the two notions agree in one direction: cospectral regular graphs are
Laplacian cospectral. -/
@[toIsoGraph]
theorem Cospectral.lapCospectral {G H : CGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : LapCospectral G H := by
  rw [lapCospectral_iff_lapSpectrum_eq, lapSpectrum_of_isRegularWith hG,
    lapSpectrum_of_isRegularWith (h.isRegularWith hG), h.spectrum_eq]

end CGraph

namespace IsoGraph

/-! ## The spectrum of an isomorphism class

The characteristic polynomial and the spectrum are isomorphism invariants, so they descend to
`IsoGraph`: `@[toIsoGraph]` on the two congruences below writes `IsoGraph.charpoly` and
`IsoGraph.spectrum`, each as a `Quotient.lift`, with the `charpoly_mk` and `spectrum_mk` lemmas
that evaluate them on a representative.  The rest of the section is transferred the same way, and
`IsoGraph/ToIsoGraph.lean` explains how. -/

theorem spectrum_eq_roots_charpoly (G : IsoGraph) : G.spectrum = G.charpoly.roots :=
  Quotient.inductionOn G fun _ ↦ rfl

theorem spectrum_cycle {n : ℕ} (hn : 3 ≤ n) :
    (cycle n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (2 * Real.pi * m.1 / n)) :=
  CGraph.spectrum_cycle hn

/-- **The energy is multiplicative over tensor products.** -/
@[simp] theorem energy_tensorProduct (G H : IsoGraph) :
    (G ⊗g H).energy = G.energy * H.energy :=
  Quotient.inductionOn₂ G H fun g h ↦ by
    rw [tensorProduct_mk, energy_mk, energy_mk, energy_mk, CGraph.energy_tensorProduct g h]

theorem spectrum_tensorProduct (G H : IsoGraph) :
    (G ⊗g H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ p.1 * p.2) :=
  Quotient.inductionOn₂ G H fun g h ↦ by
    rw [tensorProduct_mk, spectrum_mk, spectrum_mk, spectrum_mk,
      CGraph.spectrum_tensorProduct' g h]

theorem spectrum_cartesianProduct (G H : IsoGraph) :
    (G □g H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ p.1 + p.2) :=
  Quotient.inductionOn₂ G H fun g h ↦ by
    rw [cartesianProduct_mk, spectrum_mk, spectrum_mk, spectrum_mk,
      CGraph.spectrum_cartesianProduct' g h]

theorem spectrum_strongProduct (G H : IsoGraph) :
    (G ⊠g H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ (1 + p.1) * (1 + p.2) - 1) :=
  Quotient.inductionOn₂ G H fun g h ↦ by
    rw [strongProduct_mk, spectrum_mk, spectrum_mk, spectrum_mk,
      CGraph.spectrum_strongProduct' g h]

/-- Pascal's rule, on multisets of eigenvalues. -/
private theorem sum_replicate_choose_succ (n : ℕ) (v : ℕ → ℝ) :
    ∑ j ∈ Finset.range (n + 1 + 1), Multiset.replicate ((n + 1).choose j) (v j)
      = ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose j) (v j)
        + ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose j) (v (j + 1)) := by
  have hz : ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose (j + 1)) (v (j + 1))
      = ∑ j ∈ Finset.range n, Multiset.replicate (n.choose (j + 1)) (v (j + 1)) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Multiset.replicate_zero, add_zero]
  rw [Finset.sum_range_succ' (fun j ↦ Multiset.replicate ((n + 1).choose j) (v j)) (n + 1),
    Finset.sum_range_succ' (fun j ↦ Multiset.replicate (n.choose j) (v j)) n]
  simp only [Nat.choose_succ_succ, Multiset.replicate_add, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [hz]
  abel

/-- The spectrum of `K₂`, in the form the products below consume. -/
private theorem spectrum_complete_two :
    (complete 2).spectrum = (1 : ℝ) ::ₘ Multiset.replicate 1 (-1) := by
  have := spectrum_complete 1
  norm_num at this
  simpa using this

/-- Multiplying a multiset by the spectrum `{1, -1}` of `K₂`. -/
private theorem product_pm_one (s : Multiset ℝ) :
    (s ×ˢ ((1 : ℝ) ::ₘ Multiset.replicate 1 (-1))).map (fun p ↦ p.1 + p.2)
      = s.map (fun x ↦ x + 1) + s.map (fun x ↦ x + (-1)) := by
  rw [Multiset.replicate_one, Multiset.product_cons,
    show ({-1} : Multiset ℝ) = (-1 : ℝ) ::ₘ 0 from rfl, Multiset.product_cons,
    Multiset.product_zero, add_zero]
  simp [Multiset.map_add, Multiset.map_map]

private theorem map_finset_sum {ι : Type*} (s : Finset ι) (m : ι → Multiset ℝ) (f : ℝ → ℝ) :
    (∑ x ∈ s, m x).map f = ∑ x ∈ s, (m x).map f :=
  map_sum (Multiset.mapAddMonoidHom f) m s

/-- **The spectrum of the hypercube**: `Q n` has eigenvalue `n - 2 j` with multiplicity
`n.choose j`.  `Q (n + 1) = Q n □ K₂` adds `±1` to every eigenvalue, and Pascal's rule does the
rest. -/
theorem spectrum_hypercube (n : ℕ) :
    (hypercube n).spectrum
      = ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose j) ((n : ℝ) - 2 * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hypercube_succ, spectrum_cartesianProduct, spectrum_complete_two, product_pm_one, ih]
    push_cast
    rw [sum_replicate_choose_succ n (fun j ↦ (n : ℝ) + 1 - 2 * j)]
    congr 1
    · rw [map_finset_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Multiset.map_replicate]
      ring_nf
    · rw [map_finset_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Multiset.map_replicate]
      push_cast
      ring_nf

/-- **The spectrum of a grid**: the two paths' eigenvalues add. -/
theorem spectrum_grid (m n : ℕ) :
    (path m □g path n).spectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          2 * Real.cos (Real.pi * (p.1.1 + 1) / (m + 1))
            + 2 * Real.cos (Real.pi * (p.2.1 + 1) / (n + 1))) := by
  rw [spectrum_cartesianProduct, spectrum_path, spectrum_path,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ a + b), ← Finset.univ_product_univ,
    Finset.product_val]

/-- **The spectrum of a torus**: the two cycles' eigenvalues add. -/
theorem spectrum_cartesianProduct_cycle {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    (cycle m □g cycle n).spectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          2 * Real.cos (2 * Real.pi * p.1.1 / m) + 2 * Real.cos (2 * Real.pi * p.2.1 / n)) := by
  rw [spectrum_cartesianProduct, spectrum_cycle hm, spectrum_cycle hn,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ a + b), ← Finset.univ_product_univ,
    Finset.product_val]

/-- **The spectrum of a cylinder**: a cycle's eigenvalues plus a path's. -/
theorem spectrum_cartesianProduct_cycle_path {m : ℕ} (hm : 3 ≤ m) (n : ℕ) :
    (cycle m □g path n).spectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          2 * Real.cos (2 * Real.pi * p.1.1 / m)
            + 2 * Real.cos (Real.pi * (p.2.1 + 1) / (n + 1))) := by
  rw [spectrum_cartesianProduct, spectrum_cycle hm, spectrum_path,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ a + b), ← Finset.univ_product_univ,
    Finset.product_val]

/-- **The spectrum of a prism**: `Cₙ □ K₂` shifts the cycle's eigenvalues by `±1`. -/
theorem spectrum_prism {n : ℕ} (hn : 3 ≤ n) :
    (prism n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (2 * Real.pi * m.1 / n) + 1)
        + Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (2 * Real.pi * m.1 / n) - 1) := by
  rw [show prism n = cycle n □g complete 2 from rfl, spectrum_cartesianProduct,
    spectrum_complete_two, product_pm_one, spectrum_cycle hn, Multiset.map_map,
    Multiset.map_map]
  rfl

/-- **The spectrum of a ladder**: `Pₙ □ K₂` shifts the path's eigenvalues by `±1`. -/
theorem spectrum_ladder (n : ℕ) :
    (ladder n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1)) + 1)
        + Finset.univ.val.map (fun m : Fin n ↦
            2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1)) - 1) := by
  rw [show ladder n = path n □g complete 2 from rfl, spectrum_cartesianProduct,
    spectrum_complete_two, product_pm_one, spectrum_path, Multiset.map_map, Multiset.map_map]
  rfl

/-- **The spectrum of a king graph**: the strong product multiplies the shifted eigenvalues of
the two paths and shifts back. -/
theorem spectrum_king (m n : ℕ) :
    (path m ⊠g path n).spectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          (1 + 2 * Real.cos (Real.pi * (p.1.1 + 1) / (m + 1)))
              * (1 + 2 * Real.cos (Real.pi * (p.2.1 + 1) / (n + 1))) - 1) := by
  rw [spectrum_strongProduct, spectrum_path, spectrum_path,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ (1 + a) * (1 + b) - 1), ← Finset.univ_product_univ,
    Finset.product_val]

/-! ### Determined by the spectrum -/

/-- Cospectral graphs have the same order. -/
theorem Cospectral.V_eq {G H : IsoGraph} (h : Cospectral G H) : G.V = H.V := by
  rw [← natDegree_charpoly, ← natDegree_charpoly, h]

/-- A graph is **determined by its spectrum** when no other isomorphism class is cospectral. -/
def IsDS (G : IsoGraph) : Prop := ∀ H : IsoGraph, Cospectral G H → G = H

theorem isDS_mk_iff (G : CGraph) : IsDS ⟦G⟧ ↔ G.IsDS := by
  constructor
  · intro h H hc
    exact Quotient.exact (h ⟦H⟧ hc)
  · intro h H hc
    induction H using Quotient.inductionOn with
    | _ H => exact Quotient.sound (h H hc)

theorem isDS_empty (n : ℕ) : IsDS (empty n) := (isDS_mk_iff _).2 (CGraph.isDS_empty n)

theorem isDS_complete (n : ℕ) : IsDS (complete n) := (isDS_mk_iff _).2 (CGraph.isDS_complete n)

/-- **Not every graph is determined by its spectrum.**  The star `K₁,₄` is cospectral with
`K₂,₂ ⊔ K₁`, which is disconnected. -/
theorem not_isDS_star_four : ¬ IsDS (star 4) := by
  intro h
  have h1 : (star 4 : IsoGraph).numComponents = 1 := numComponents_star 4
  rw [h _ cospectral_star_four] at h1
  simp at h1

/-! ### Line graphs -/

theorem neg_two_le_of_mem_spectrum_lineGraph (G : IsoGraph) {x : ℝ} :
    x ∈ G.lineGraph.spectrum → -2 ≤ x := by
  classical
  refine Quotient.inductionOn G fun g hx ↦ ?_
  rw [lineGraph_mk, spectrum_mk] at hx
  exact CGraph.neg_two_le_of_mem_spectrum_lineGraph g hx

/-! ### The diameter -/

/-- **The number of distinct eigenvalues exceeds the diameter.** -/
theorem diameter_lt_card_toFinset_spectrum (G : IsoGraph) (hG : 0 < G.V) :
    G.diameter < G.spectrum.toFinset.card := by
  classical
  induction G using Quotient.inductionOn with
  | h g =>
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
    exact g.diameter_lt_card_toFinset_spectrum

/-! ### Few distinct eigenvalues -/

@[simp] theorem card_toFinset_spectrum_empty (n : ℕ) :
    (empty (n + 1)).spectrum.toFinset.card = 1 := by
  have hset : (Multiset.replicate (n + 1) (0 : ℝ)).toFinset = {0} := by
    ext x
    rw [Multiset.mem_toFinset, Multiset.mem_replicate]
    simp
  rw [spectrum_empty, hset, Finset.card_singleton]

/-- **A graph with one distinct eigenvalue has no edges.** -/
theorem eq_empty_of_card_toFinset_spectrum_eq_one {G : IsoGraph}
    (h1 : G.spectrum.toFinset.card = 1) : G = empty G.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [spectrum_mk] at h1
    haveI : Nonempty g.V := by
      rw [← Fintype.card_pos_iff, ← CGraph.card_spectrum]
      by_contra hc
      have hz : g.spectrum = 0 := Multiset.card_eq_zero.1 (by omega)
      rw [hz] at h1
      simp at h1
    exact mk_eq_empty fun x y ↦
      CGraph.adj_eq_false_of_card_toFinset_spectrum_eq_one h1 x y

/-- **One distinct eigenvalue characterises the edgeless graphs.** -/
theorem card_toFinset_spectrum_eq_one_iff {G : IsoGraph} (hV : 1 ≤ G.V) :
    G.spectrum.toFinset.card = 1 ↔ G = empty G.V := by
  refine ⟨eq_empty_of_card_toFinset_spectrum_eq_one, fun h ↦ ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, G.V = n + 1 := ⟨G.V - 1, by omega⟩
  rw [h, hn, card_toFinset_spectrum_empty]

@[simp] theorem card_toFinset_spectrum_complete (n : ℕ) :
    (complete (n + 2)).spectrum.toFinset.card = 2 := by
  have hne : ((n + 1 : ℕ) : ℝ) ≠ -1 := by
    intro h
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast at h
    linarith
  have hset : (complete (n + 2)).spectrum.toFinset = {((n + 1 : ℕ) : ℝ), -1} := by
    rw [show n + 2 = (n + 1) + 1 from rfl, spectrum_complete (n + 1)]
    ext x
    rw [Multiset.toFinset_cons, Finset.mem_insert, Multiset.mem_toFinset, Multiset.mem_replicate]
    simp
  rw [hset]
  exact Finset.card_pair hne

/-- **A connected regular graph with two distinct eigenvalues is complete.** -/
theorem eq_complete_of_card_toFinset_spectrum_eq_two {G : IsoGraph} {k : ℕ}
    (hconn : G.IsConnected) (hreg : G.IsRegularWith k)
    (h2 : G.spectrum.toFinset.card = 2) : G = complete G.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    exact mk_eq_complete fun x y hxy ↦
      CGraph.adj_of_card_toFinset_spectrum_eq_two hconn hreg h2 x y hxy

/-- **Two distinct eigenvalues characterises the complete graphs** among the connected regular
graphs on at least two vertices. -/
theorem card_toFinset_spectrum_eq_two_iff {G : IsoGraph} {k : ℕ} (hconn : G.IsConnected)
    (hreg : G.IsRegularWith k) (hV : 2 ≤ G.V) :
    G.spectrum.toFinset.card = 2 ↔ G = complete G.V := by
  refine ⟨eq_complete_of_card_toFinset_spectrum_eq_two hconn hreg, fun h ↦ ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, G.V = n + 2 := ⟨G.V - 2, by omega⟩
  rw [h, hn, card_toFinset_spectrum_complete]

/-- **A connected strongly regular graph that is not complete has exactly three distinct
eigenvalues.** -/
theorem card_toFinset_spectrum_eq_three_of_isSRGWith {G : IsoGraph} {n k l m : ℕ}
    (hconn : G.IsConnected) (h : G.IsSRGWith n k l m) (hE : G.E < G.V.choose 2) :
    G.spectrum.toFinset.card = 3 := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [E_mk, V_mk] at hE
    rw [isSRGWith_mk] at h
    rw [isConnected_mk] at hconn
    rw [spectrum_mk]
    obtain ⟨i, j, hij, hnadj⟩ := CGraph.exists_not_adj_of_E_lt g hE
    exact CGraph.card_toFinset_spectrum_eq_three_of_isSRGWith hconn h hij hnadj

/-- **Strong regularity is determined by the spectrum.** -/
theorem Cospectral.exists_isSRGWith {G H : IsoGraph} (hc : Cospectral G H) {n k l m : ℕ}
    (hconn : G.IsConnected) (h : G.IsSRGWith n k l m) (hE : G.E < G.V.choose 2) :
    ∃ l' m' : ℕ, H.IsSRGWith H.V k l' m' := by
  refine exists_isSRGWith_of_card_toFinset_spectrum_eq_three
    (Cospectral.isConnected hc h.isRegularWith hconn)
    (Cospectral.isRegularWith hc h.isRegularWith) ?_
  rw [← hc.spectrum_eq]
  exact card_toFinset_spectrum_eq_three_of_isSRGWith hconn h hE

/-! ### The Laplacian -/

/-- **The Laplacian spectrum of the cycle** `C_n`, `n ≥ 3`: the numbers `2 - 2 cos (2 π m / n)`. -/
theorem lapSpectrum_cycle {n : ℕ} (hn : 3 ≤ n) :
    (cycle n).lapSpectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 - 2 * Real.cos (2 * Real.pi * m.1 / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [lapSpectrum_of_isRegularWith (isRegularWith_cycle m), spectrum_cycle hn, Multiset.map_map]
  norm_num [Function.comp_def]

/-- **The Laplacian spectrum of the hypercube** `Q_n`: `2 j` with multiplicity `n.choose j`. -/
theorem lapSpectrum_hypercube (n : ℕ) :
    (hypercube n).lapSpectrum
      = ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose j) (2 * j : ℝ) := by
  rw [lapSpectrum_of_isRegularWith (isRegularWith_hypercube n), spectrum_hypercube,
    ← Multiset.coe_mapAddMonoidHom, map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate]
  rw [Finset.mem_range] at hj
  congr 1
  ring

/-- **The Laplacian spectrum of the complement.**  The eigenvalue `0` of the constant vector stays
`0`, and every other eigenvalue `μ` becomes `n - μ`. -/
theorem lapSpectrum_compl {G : IsoGraph} (hG : 0 < G.V) :
    Gᶜ.lapSpectrum = 0 ::ₘ (G.lapSpectrum.erase 0).map (fun x ↦ (G.V : ℝ) - x) := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at hG
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
    rw [compl_mk, lapSpectrum_mk, lapSpectrum_mk, V_mk]
    exact CGraph.lapSpectrum_compl g

/-- **The Laplacian spectrum of a join**: `0`, the order `n + m`, and every other eigenvalue of
each factor shifted by the order of the other factor. -/
theorem lapSpectrum_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).lapSpectrum
      = 0 ::ₘ (((G.V : ℝ) + H.V)
          ::ₘ ((G.lapSpectrum.erase 0).map (fun x ↦ x + (H.V : ℝ))
             + (H.lapSpectrum.erase 0).map (fun x ↦ x + (G.V : ℝ)))) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      classical
      rw [V_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
      haveI : Nonempty h.V := Fintype.card_pos_iff.1 hH
      rw [join_mk, lapSpectrum_mk, lapSpectrum_mk, lapSpectrum_mk, V_mk, V_mk]
      exact CGraph.lapSpectrum_join g h

/-- **The adjacency spectrum of a regular join**: if `G` is `k`-regular on `G.V` vertices and `H`
is `l`-regular on `H.V` vertices with `k + H.V = m = G.V + l`, so that `G ∇g H` is `m`-regular,
then the join has the eigenvalues `m` and `k - G.V` and keeps every *other* eigenvalue of each
factor unchanged. -/
theorem spectrum_join_of_isRegularWith {G H : IsoGraph} (hG0 : 0 < G.V) (hH0 : 0 < H.V) {k l m : ℕ}
    (hG : G.IsRegularWith k) (hH : H.IsRegularWith l) (h1 : k + H.V = m) (h2 : G.V + l = m) :
    (G ∇g H).spectrum
      = (m : ℝ) ::ₘ (((k : ℝ) - G.V)
          ::ₘ (G.spectrum.erase (k : ℝ) + H.spectrum.erase (l : ℝ))) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      classical
      rw [V_mk] at hG0 hH0 h1 h2
      rw [isRegularWith_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG0
      haveI : Nonempty h.V := Fintype.card_pos_iff.1 hH0
      rw [join_mk, spectrum_mk, spectrum_mk, spectrum_mk, V_mk]
      exact CGraph.spectrum_join_of_isRegularWith hG hH h1 h2

/-- **The Laplacian spectrum of the wheel** `W_n`: the hub contributes the order `n + 1`, and every
nonzero eigenvalue of the rim is shifted by one. -/
theorem lapSpectrum_wheel {n : ℕ} (hn : 0 < n) :
    (wheel n).lapSpectrum
      = 0 ::ₘ (((n : ℝ) + 1) ::ₘ ((cycle n).lapSpectrum.erase 0).map (fun x ↦ x + 1)) := by
  have hV : (complete 1).V = 1 := V_complete 1
  have hVc : (cycle n).V = n := V_cycle n
  have h := lapSpectrum_join (G := complete 1) (H := cycle n) (by rw [hV]; omega)
    (by rw [hVc]; omega)
  rw [wheel_eq_join, h, hV, hVc]
  have hone : (complete 1).lapSpectrum = {0} := by simp
  rw [hone]
  norm_num [add_comm (1 : ℝ) (n : ℝ)]

/-- **Every Laplacian eigenvalue is at most the number of vertices.** -/
theorem le_V_of_mem_lapSpectrum {G : IsoGraph} {x : ℝ} (hx : x ∈ G.lapSpectrum) : x ≤ G.V := by
  induction G using Quotient.inductionOn with
  | h g => exact g.le_card_of_mem_lapSpectrum hx

/-! ### Laplacian cospectrality -/

theorem lapSpectrum_eq_roots_lapCharpoly (G : IsoGraph) : G.lapSpectrum = G.lapCharpoly.roots :=
  Quotient.inductionOn G fun _ ↦ rfl

theorem algConn_le_V (G : IsoGraph) (h : 2 ≤ G.V) : G.algConn ≤ G.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h ⊢
    exact g.algConn_le_card h

attribute [simp] IsoGraph.algConn_complete IsoGraph.algConn_star

open Real in
/-- **The algebraic connectivity of the cycle** `C_{n+3}` is `2 - 2 cos (2 π / (n + 3))`.  The
eigenvalue at `m` and the one at `n + 3 - m` agree, so the smallest survivor of the erasure sits
at both ends of the range, `m = 1` and `m = n + 2`. -/
theorem algConn_cycle (n : ℕ) :
    (cycle (n + 3)).algConn = 2 - 2 * Real.cos (2 * π / ((n : ℝ) + 3)) := by
  have hpi : 0 < π := Real.pi_pos
  have hN : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  set f : Fin (n + 3) → ℝ := fun m ↦ 2 - 2 * Real.cos (2 * π * m.1 / ((n : ℝ) + 3)) with hf
  have hspec : (cycle (n + 3)).lapSpectrum = Finset.univ.val.map f := by
    rw [lapSpectrum_cycle (by omega), hf]
    push_cast
    rfl
  have h0 : f 0 = 0 := by
    rw [hf]
    simp
  have hmem0 : (0 : Fin (n + 3)) ∈ Finset.univ.val := Finset.mem_univ_val _
  have huniv : (Finset.univ.val : Multiset (Fin (n + 3)))
      = 0 ::ₘ Finset.univ.val.erase 0 := (Multiset.cons_erase hmem0).symm
  have herase : (cycle (n + 3)).lapSpectrum.erase 0
      = (Finset.univ.val.erase (0 : Fin (n + 3))).map f := by
    rw [hspec]
    conv_lhs => rw [huniv]
    rw [Multiset.map_cons, h0, Multiset.erase_cons_head]
  have hone : f 1 = 2 - 2 * Real.cos (2 * π / ((n : ℝ) + 3)) := by
    rw [hf]
    simp only [Fin.val_one]
    norm_num
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase, ← hone]
    refine Multiset.mem_map_of_mem f ?_
    refine (Multiset.mem_erase_of_ne ?_).2 (Finset.mem_univ_val _)
    simp
  · intro x hx
    rw [herase] at hx
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hx
    have hm0 : m ≠ 0 := by
      intro hzero
      subst hzero
      rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self] at hm
      have hle1 := Multiset.nodup_iff_count_le_one.1 Finset.univ.nodup (0 : Fin (n + 3))
      omega
    have hm1 : 1 ≤ m.1 := by
      rcases Nat.eq_zero_or_pos m.1 with h | h
      · exact absurd (Fin.ext h) hm0
      · exact h
    have hm1R : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast hm1
    have hmR : (m.1 : ℝ) + 1 ≤ (n : ℝ) + 3 := by
      have : m.1 + 1 ≤ n + 3 := m.isLt
      exact_mod_cast this
    -- the angle `2 π m / (n + 3)` lies between `2 π / (n + 3)` and `2 π - 2 π / (n + 3)`
    have hlow : 2 * π / ((n : ℝ) + 3) ≤ 2 * π * m.1 / ((n : ℝ) + 3) :=
      div_le_div_of_nonneg_right (by nlinarith) hN.le
    have hhigh : 2 * π * m.1 / ((n : ℝ) + 3) ≤ 2 * π - 2 * π / ((n : ℝ) + 3) := by
      rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hN]
      nlinarith
    have hcos : Real.cos (2 * π * m.1 / ((n : ℝ) + 3))
        ≤ Real.cos (2 * π / ((n : ℝ) + 3)) := by
      rcases le_total (2 * π * m.1 / ((n : ℝ) + 3)) π with hle | hle
      · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hle hlow
      · rw [← Real.cos_two_pi_sub]
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
    have hfm : f m = 2 - 2 * Real.cos (2 * π * m.1 / ((n : ℝ) + 3)) := rfl
    rw [hfm]
    linarith

theorem algConn_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).algConn = 0 := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
      haveI : Nonempty h'.V := Fintype.card_pos_iff.1 hH
      exact CGraph.algConn_disjUnion g h'

theorem lapLambdaMax_mem_lapSpectrum (G : IsoGraph) (h : 0 < G.V) :
    G.lapLambdaMax ∈ G.lapSpectrum := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 h
    exact g.lapLambdaMax_mem_lapSpectrum

theorem lapLambdaMax_nonneg (G : IsoGraph) (h : 0 < G.V) : 0 ≤ G.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 h
    exact g.lapLambdaMax_nonneg

/-- **The largest Laplacian eigenvalue is at most the number of vertices.** -/
theorem lapLambdaMax_le_V (G : IsoGraph) (h : 0 < G.V) : G.lapLambdaMax ≤ G.V :=
  le_V_of_mem_lapSpectrum (G.lapLambdaMax_mem_lapSpectrum h)

theorem lapLambdaMax_le_two_mul_maxDeg (G : IsoGraph) (h : 0 < G.V) :
    G.lapLambdaMax ≤ 2 * (G.maxDeg : ℝ) :=
  le_two_mul_maxDeg_of_mem_lapSpectrum (G.lapLambdaMax_mem_lapSpectrum h)

/-- **The largest Laplacian eigenvalue is at least the average degree.** -/
theorem two_mul_E_le_V_mul_lapLambdaMax (G : IsoGraph) :
    2 * (G.E : ℝ) ≤ G.V * G.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g => exact g.two_mul_E_le_card_mul_lapLambdaMax

/-- **The algebraic connectivity is at most the average of the nonzero eigenvalues.** -/
theorem V_sub_one_mul_algConn_le_two_mul_E (G : IsoGraph) (h : 0 < G.V) :
    ((G.V - 1 : ℕ) : ℝ) * G.algConn ≤ 2 * (G.E : ℝ) := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [V_mk] at h ⊢
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 h
    exact g.card_sub_one_mul_algConn_le_two_mul_E

/-- **The complement swaps the two ends of the Laplacian spectrum**: `μ_max (Ḡ) = n - a (G)`. -/
theorem lapLambdaMax_compl {G : IsoGraph} (h : 2 ≤ G.V) :
    Gᶜ.lapLambdaMax = G.V - G.algConn := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 (by omega)
    rw [compl_mk, lapLambdaMax_mk, algConn_mk, V_mk]
    exact g.lapLambdaMax_compl h

/-- **The complement swaps the two ends of the Laplacian spectrum**: `a (Ḡ) = n - μ_max (G)`. -/
theorem algConn_compl {G : IsoGraph} (h : 2 ≤ G.V) :
    Gᶜ.algConn = G.V - G.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 (by omega)
    rw [compl_mk, algConn_mk, lapLambdaMax_mk, V_mk]
    exact g.algConn_compl h

attribute [simp] IsoGraph.lapLambdaMax_complete IsoGraph.lapLambdaMax_star
  IsoGraph.lapLambdaMax_bipartite

/-- **The largest Laplacian eigenvalue of an even cycle** is `4 = 2 Δ`, the bound
`lapLambdaMax_le_two_mul_maxDeg` attained: the eigenvalue `2 - 2 cos (2 π m / n)` reaches its
ceiling at `m = n / 2`, which is an integer only when `n` is even. -/
theorem lapLambdaMax_cycle_even {n : ℕ} (hn : 2 ≤ n) : (cycle (2 * n)).lapLambdaMax = 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  set f : Fin (2 * n) → ℝ :=
    fun m ↦ 2 - 2 * Real.cos (2 * Real.pi * m.1 / ((2 * n : ℕ) : ℝ)) with hf
  have hspec : (cycle (2 * n)).lapSpectrum = Finset.univ.val.map f := by
    rw [lapSpectrum_cycle (by omega)]
  have hmid : f ⟨n, by omega⟩ = 4 := by
    have harg : 2 * Real.pi * ((⟨n, by omega⟩ : Fin (2 * n)) : ℕ) / ((2 * n : ℕ) : ℝ)
        = Real.pi := by
      push_cast
      field_simp
    rw [hf]
    simp only [harg, Real.cos_pi]
    ring
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [hspec, ← hmid]
    exact Multiset.mem_map_of_mem f (Finset.mem_univ_val _)
  · intro x hx
    rw [hspec] at hx
    obtain ⟨m, _, rfl⟩ := Multiset.mem_map.1 hx
    have hcos := Real.neg_one_le_cos (2 * Real.pi * m.1 / ((2 * n : ℕ) : ℝ))
    have hfm : f m = 2 - 2 * Real.cos (2 * Real.pi * m.1 / ((2 * n : ℕ) : ℝ)) := rfl
    rw [hfm]
    linarith

/-- **The largest Laplacian eigenvalue of an odd cycle** is `2 + 2 cos (π / n)`, just short of the
even cycle's `4`: the closest an odd cycle's angles come to `π` is `π - π / n`, so its adjacency
spectrum stops at `-2 cos (π / n)` and the reflection `μ_max = 2 - λ_min` stops with it. -/
theorem lapLambdaMax_cycle_odd (n : ℕ) :
    (cycle (2 * n + 3)).lapLambdaMax = 2 + 2 * Real.cos (Real.pi / ((2 * n + 3 : ℕ) : ℝ)) := by
  have hr : (CGraph.cycle (2 * n + 3)).IsRegularWith 2 := isRegularWith_cycle (2 * n)
  rw [cycle_def, lapLambdaMax_mk, CGraph.lapLambdaMax_of_isRegularWith hr,
    CGraph.lambdaMin_cycle_odd]
  push_cast
  ring

/-- **A disjoint union takes the larger of the two largest eigenvalues**, where
`algConn_disjUnion` takes neither. -/
theorem lapLambdaMax_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).lapLambdaMax = max G.lapLambdaMax H.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
      haveI : Nonempty h'.V := Fintype.card_pos_iff.1 hH
      exact CGraph.lapLambdaMax_disjUnion g h'

/-- **The largest Laplacian eigenvalue vanishes exactly on the edgeless graph.** -/
theorem lapLambdaMax_eq_zero_iff (G : IsoGraph) (h : 0 < G.V) :
    G.lapLambdaMax = 0 ↔ G.E = 0 := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 h
    exact g.lapLambdaMax_eq_zero_iff

/-- **The Laplacian eigenvalues of a cartesian product are the sums of the Laplacian
eigenvalues.** -/
theorem lapSpectrum_cartesianProduct (G H : IsoGraph) :
    (G □g H).lapSpectrum = (G.lapSpectrum ×ˢ H.lapSpectrum).map (fun p ↦ p.1 + p.2) :=
  Quotient.inductionOn₂ G H fun g h ↦ by
    rw [cartesianProduct_mk, lapSpectrum_mk, lapSpectrum_mk, lapSpectrum_mk,
      CGraph.lapSpectrum_cartesianProduct' g h]

/-- Adding the Laplacian spectrum `{0, 2}` of `K₂` to a multiset. -/
private theorem lap_product_zero_two (s : Multiset ℝ) :
    (s ×ˢ ((0 : ℝ) ::ₘ Multiset.replicate 1 2)).map (fun p ↦ p.1 + p.2)
      = s.map (fun x ↦ x + 0) + s.map (fun x ↦ x + 2) := by
  rw [Multiset.replicate_one, Multiset.product_cons,
    show ({2} : Multiset ℝ) = (2 : ℝ) ::ₘ 0 from rfl, Multiset.product_cons,
    Multiset.product_zero, add_zero]
  simp [Multiset.map_add, Multiset.map_map]

/-- **The Laplacian spectrum of a grid**: the two paths' Laplacian eigenvalues add. -/
theorem lapSpectrum_grid (m n : ℕ) :
    (path m □g path n).lapSpectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          (2 - 2 * Real.cos (Real.pi * p.1.1 / m))
            + (2 - 2 * Real.cos (Real.pi * p.2.1 / n))) := by
  rw [lapSpectrum_cartesianProduct, lapSpectrum_path, lapSpectrum_path,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ a + b), ← Finset.univ_product_univ,
    Finset.product_val]

/-- **The Laplacian spectrum of a torus**: the two cycles' Laplacian eigenvalues add. -/
theorem lapSpectrum_cartesianProduct_cycle {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    (cycle m □g cycle n).lapSpectrum
      = Finset.univ.val.map (fun p : Fin m × Fin n ↦
          (2 - 2 * Real.cos (2 * Real.pi * p.1.1 / m))
            + (2 - 2 * Real.cos (2 * Real.pi * p.2.1 / n))) := by
  rw [lapSpectrum_cartesianProduct, lapSpectrum_cycle hm, lapSpectrum_cycle hn,
    ← CGraph.map_product_apply₂ _ _ (fun a b ↦ a + b), ← Finset.univ_product_univ,
    Finset.product_val]

/-- **The Laplacian spectrum of a prism**: `Cₙ □ K₂` keeps the cycle's Laplacian eigenvalues and
repeats them shifted up by `2`. -/
theorem lapSpectrum_prism {n : ℕ} (hn : 3 ≤ n) :
    (prism n).lapSpectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 - 2 * Real.cos (2 * Real.pi * m.1 / n))
        + Finset.univ.val.map (fun m : Fin n ↦ 4 - 2 * Real.cos (2 * Real.pi * m.1 / n)) := by
  rw [show prism n = cycle n □g complete 2 from rfl, lapSpectrum_cartesianProduct,
    show (complete 2).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate 1 2 from by
      have := lapSpectrum_complete 1
      norm_num at this
      simpa using this,
    lap_product_zero_two, lapSpectrum_cycle hn, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def]
  congr 1 <;> exact Multiset.map_congr rfl fun x _ ↦ by ring

/-- **The Laplacian spectrum of a ladder**: `Pₙ □ K₂` keeps the path's Laplacian eigenvalues and
repeats them shifted up by `2`. -/
theorem lapSpectrum_ladder (n : ℕ) :
    (ladder n).lapSpectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 - 2 * Real.cos (Real.pi * m.1 / n))
        + Finset.univ.val.map (fun m : Fin n ↦ 4 - 2 * Real.cos (Real.pi * m.1 / n)) := by
  rw [show ladder n = path n □g complete 2 from rfl, lapSpectrum_cartesianProduct,
    show (complete 2).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate 1 2 from by
      have := lapSpectrum_complete 1
      norm_num at this
      simpa using this,
    lap_product_zero_two, lapSpectrum_path, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def]
  congr 1 <;> exact Multiset.map_congr rfl fun x _ ↦ by ring

/-- **The largest Laplacian eigenvalue of a cartesian product** is the sum of the two. -/
theorem lapLambdaMax_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G □g H).lapLambdaMax = G.lapLambdaMax + H.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
      haveI : Nonempty h'.V := Fintype.card_pos_iff.1 hH
      rw [cartesianProduct_mk, lapLambdaMax_mk, lapLambdaMax_mk, lapLambdaMax_mk]
      exact CGraph.lapLambdaMax_cartesianProduct g h'

/-- **The algebraic connectivity of a cartesian product** is the smaller of the two. -/
theorem algConn_cartesianProduct {G H : IsoGraph} (hG : 2 ≤ G.V) (hH : 2 ≤ H.V) :
    (G □g H).algConn = min G.algConn H.algConn := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      rw [cartesianProduct_mk, algConn_mk, algConn_mk, algConn_mk]
      exact CGraph.algConn_cartesianProduct g h' hG hH

/-! ### The Laplacian of the grid, the torus and the cylinder -/

/-- **The largest Laplacian eigenvalue of a grid** is the sum of the two paths'. -/
theorem lapLambdaMax_grid (m n : ℕ) :
    (path (m + 1) □g path (n + 1)).lapLambdaMax
      = (2 - 2 * Real.cos (Real.pi * m / ((m : ℝ) + 1)))
        + (2 - 2 * Real.cos (Real.pi * n / ((n : ℝ) + 1))) := by
  rw [lapLambdaMax_cartesianProduct (by simp) (by simp), lapLambdaMax_path, lapLambdaMax_path]

/-- **The largest Laplacian eigenvalue of an even torus** is `8 = 2 Δ`, the bound
`lapLambdaMax_le_two_mul_maxDeg` attained. -/
theorem lapLambdaMax_cartesianProduct_cycle_even {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (cycle (2 * m) □g cycle (2 * n)).lapLambdaMax = 8 := by
  rw [lapLambdaMax_cartesianProduct (by simp; omega) (by simp; omega), lapLambdaMax_cycle_even hm,
    lapLambdaMax_cycle_even hn]
  norm_num

/-- **The largest Laplacian eigenvalue of a cylinder with an even cycle**. -/
theorem lapLambdaMax_cartesianProduct_cycle_even_path {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    (cycle (2 * m) □g path (n + 1)).lapLambdaMax
      = 4 + (2 - 2 * Real.cos (Real.pi * n / ((n : ℝ) + 1))) := by
  rw [lapLambdaMax_cartesianProduct (by simp; omega) (by simp), lapLambdaMax_cycle_even hm,
    lapLambdaMax_path]

/-- **The algebraic connectivity of a grid** is the longer side's: `a = 2 - 2 cos (π / (n + 2))`
for `m ≤ n`.  The cartesian product takes the minimum, and `2 - 2 cos (π / (k + 2))` decreases
in `k`. -/
theorem algConn_grid {m n : ℕ} (h : m ≤ n) :
    (path (m + 2) □g path (n + 2)).algConn = 2 - 2 * Real.cos (Real.pi / ((n : ℝ) + 2)) := by
  rw [algConn_cartesianProduct (by simp) (by simp), algConn_path, algConn_path, min_eq_right]
  have h1 : (0 : ℝ) ≤ Real.pi / ((n : ℝ) + 2) := by positivity
  have h2 : Real.pi / ((n : ℝ) + 2) ≤ Real.pi / ((m : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    exact_mod_cast Nat.cast_le.2 (by omega : m + 2 ≤ n + 2)
  have h3 : Real.pi / ((m : ℝ) + 2) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
  have := Real.cos_le_cos_of_nonneg_of_le_pi h1 h3 h2
  linarith

/-- **The algebraic connectivity of a torus** is the longer cycle's. -/
theorem algConn_cartesianProduct_cycle {m n : ℕ} (h : m ≤ n) :
    (cycle (m + 3) □g cycle (n + 3)).algConn
      = 2 - 2 * Real.cos (2 * Real.pi / ((n : ℝ) + 3)) := by
  rw [algConn_cartesianProduct (by simp) (by simp), algConn_cycle, algConn_cycle,
    min_eq_right]
  have h1 : (0 : ℝ) ≤ 2 * Real.pi / ((n : ℝ) + 3) := by positivity
  have h2 : 2 * Real.pi / ((n : ℝ) + 3) ≤ 2 * Real.pi / ((m : ℝ) + 3) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.cast_le.2 (by omega : m + 3 ≤ n + 3)
  have h3 : 2 * Real.pi / ((m : ℝ) + 3) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
  have := Real.cos_le_cos_of_nonneg_of_le_pi h1 h3 h2
  linarith

/-- **The algebraic connectivity of a cylinder** is the smaller of the cycle's and the path's. -/
theorem algConn_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 3) □g path (n + 2)).algConn
      = min (2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)))
          (2 - 2 * Real.cos (Real.pi / ((n : ℝ) + 2))) := by
  rw [algConn_cartesianProduct (by simp) (by simp), algConn_cycle, algConn_path]

/-- **The algebraic connectivity of a prism** is the cycle's, once the cycle is long enough that
its Fiedler value drops below the rung's `2`. -/
theorem algConn_prism (n : ℕ) :
    (prism (n + 4)).algConn = 2 - 2 * Real.cos (2 * Real.pi / ((n : ℝ) + 4)) := by
  rw [show prism (n + 4) = cycle (n + 1 + 3) □g complete (0 + 2) from by norm_num,
    algConn_cartesianProduct (by simp) (by simp), algConn_cycle, algConn_complete, min_eq_left]
  · push_cast
    ring_nf
  · have h1 : 2 * Real.pi / ((n : ℝ) + 1 + 3) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
    have h2 : (0 : ℝ) ≤ Real.cos (2 * Real.pi / ((n : ℝ) + 1 + 3)) := by
      refine Real.cos_nonneg_of_mem_Icc ⟨?_, h1⟩
      have : (0 : ℝ) ≤ 2 * Real.pi / ((n : ℝ) + 1 + 3) := by positivity
      linarith [Real.pi_pos]
    push_cast
    linarith

/-- **The largest Laplacian eigenvalue of an even prism** is `6 = 2 Δ`: the even prism is
bipartite and cubic. -/
theorem lapLambdaMax_prism_even {n : ℕ} (hn : 2 ≤ n) : (prism (2 * n)).lapLambdaMax = 6 := by
  rw [show prism (2 * n) = cycle (2 * n) □g complete (0 + 2) from by norm_num,
    lapLambdaMax_cartesianProduct (by simp; omega) (by simp), lapLambdaMax_cycle_even hn,
    lapLambdaMax_complete]
  norm_num

/-- **The largest Laplacian eigenvalue of a ladder** is the path's plus the rung's `2`; unlike the
prism it never reaches `2 Δ = 6`, because the path factor falls short of `4`. -/
theorem lapLambdaMax_ladder (n : ℕ) :
    (ladder (n + 1)).lapLambdaMax = 4 - 2 * Real.cos (Real.pi * n / ((n : ℝ) + 1)) := by
  rw [show ladder (n + 1) = path (n + 1) □g complete (0 + 2) from by norm_num,
    lapLambdaMax_cartesianProduct (by simp) (by simp), lapLambdaMax_path, lapLambdaMax_complete]
  norm_num
  ring

/-- **The algebraic connectivity of a ladder** is the path's: the rungs contribute `2`, and
`2 - 2 cos (π / (n + 2))` never reaches it. -/
theorem algConn_ladder (n : ℕ) :
    (ladder (n + 2)).algConn = 2 - 2 * Real.cos (Real.pi / ((n : ℝ) + 2)) := by
  rw [show ladder (n + 2) = path (n + 2) □g complete (0 + 2) from by norm_num,
    algConn_cartesianProduct (by simp) (by simp), algConn_path, algConn_complete, min_eq_left]
  have h1 : Real.pi / ((n : ℝ) + 2) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
  have h2 : (0 : ℝ) ≤ Real.cos (Real.pi / ((n : ℝ) + 2)) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, h1⟩
    have : (0 : ℝ) ≤ Real.pi / ((n : ℝ) + 2) := by positivity
    linarith [Real.pi_pos]
  push_cast
  linarith

/-- **`Δ + 1 ≤ μ_max`**, at the `IsoGraph` level. -/
theorem maxDeg_add_one_le_lapLambdaMax {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.E) :
    (G.maxDeg : ℝ) + 1 ≤ G.lapLambdaMax := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [V_mk] at hV
    rw [E_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 hV
    rw [maxDeg_mk, lapLambdaMax_mk]
    exact CGraph.maxDeg_add_one_le_lapLambdaMax g h

/-- **Fiedler's inequality for a graph that is not complete**: `a (G) ≤ δ (G)`. -/
theorem algConn_le_minDeg {G : IsoGraph} (h : 2 ≤ G.V) (hc : 0 < Gᶜ.E) :
    G.algConn ≤ minDeg G := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h
    rw [compl_mk, E_mk] at hc
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 (by omega)
    rw [algConn_mk, minDeg_mk]
    exact g.algConn_le_minDeg h hc

/-- **Fiedler's bound**: `(n - 1) · a (G) ≤ n · δ (G)`, an equality for the complete graph. -/
theorem V_sub_one_mul_algConn_le_V_mul_minDeg {G : IsoGraph} (h : 2 ≤ G.V) :
    ((G.V : ℝ) - 1) * G.algConn ≤ (G.V : ℝ) * minDeg G := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 (by omega)
    rw [algConn_mk, minDeg_mk, V_mk]
    exact g.card_sub_one_mul_algConn_le_card_mul_minDeg h

/-- **Fiedler's bound in its usual form**: `a (G) ≤ n / (n - 1) · δ (G)`. -/
theorem algConn_le_div_mul_minDeg {G : IsoGraph} (h : 2 ≤ G.V) :
    G.algConn ≤ (G.V : ℝ) / ((G.V : ℝ) - 1) * minDeg G := by
  induction G using Quotient.inductionOn with
  | h g =>
    classical
    rw [V_mk] at h
    haveI : Nonempty g.V := Fintype.card_pos_iff.1 (by omega)
    rw [algConn_mk, minDeg_mk, V_mk]
    exact g.algConn_le_div_mul_minDeg h

theorem lapLambdaMax_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).lapLambdaMax = (G.V : ℝ) + H.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      haveI : Nonempty g.V := Fintype.card_pos_iff.1 hG
      haveI : Nonempty h'.V := Fintype.card_pos_iff.1 hH
      rw [join_mk, lapLambdaMax_mk, V_mk, V_mk]
      exact CGraph.lapLambdaMax_join g h'

theorem algConn_join {G H : IsoGraph} (hG : 2 ≤ G.V) (hH : 2 ≤ H.V) :
    (G ∇g H).algConn = min (G.algConn + H.V) (H.algConn + G.V) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h' =>
      rw [V_mk] at hG hH
      rw [join_mk, algConn_mk, algConn_mk, algConn_mk, V_mk, V_mk]
      exact CGraph.algConn_join g h' hG hH

/-- **The largest Laplacian eigenvalue of the wheel** is its order: the wheel is a join, so its
complement is disconnected. -/
theorem lapLambdaMax_wheel {n : ℕ} (hn : 0 < n) : (wheel n).lapLambdaMax = (n : ℝ) + 1 := by
  have hVc : (cycle n).V = n := V_cycle n
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_wheel hn]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  · intro x hx
    rw [lapSpectrum_wheel hn, Multiset.mem_cons, Multiset.mem_cons] at hx
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases hx with rfl | rfl | hx
    · linarith
    · linarith
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hyle : y ≤ (cycle n).V := le_V_of_mem_lapSpectrum (Multiset.mem_of_mem_erase hy)
      rw [hVc] at hyle
      linarith

/-- **The algebraic connectivity of the wheel** `W_n` for `n ≥ 3`: one more than the rim's, since
the hub is joined to every rim vertex.  At `n = 3` this is `a (K₄) = 4`. -/
theorem algConn_wheel {n : ℕ} (hn : 3 ≤ n) :
    (wheel n).algConn = 3 - 2 * Real.cos (2 * Real.pi / (n : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hVc : (cycle (m + 3)).V = m + 3 := V_cycle _
  have hcyc : (cycle (m + 3)).algConn = 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)) :=
    algConn_cycle m
  have hmem : (cycle (m + 3)).algConn ∈ (cycle (m + 3)).lapSpectrum.erase 0 :=
    algConn_mem_erase _ (by rw [hVc]; omega)
  have herase : (wheel (m + 3)).lapSpectrum.erase 0
      = (((m : ℕ) : ℝ) + 3 + 1)
          ::ₘ ((cycle (m + 3)).lapSpectrum.erase 0).map (fun x ↦ x + 1) := by
    rw [lapSpectrum_wheel (by omega), Multiset.erase_cons_head]
    push_cast
    ring_nf
  have hval : (3 : ℝ) - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3))
      = (cycle (m + 3)).algConn + 1 := by
    rw [hcyc]
    ring
  have hle : (cycle (m + 3)).algConn ≤ (m : ℝ) + 3 := by
    have := algConn_le_V (cycle (m + 3)) (by rw [hVc]; omega)
    rw [hVc] at this
    push_cast at this
    linarith
  refine algConn_eq_of_isLeast ?_ ?_
  · rw [herase]
    push_cast
    rw [hval]
    exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hmem)
  · intro x hx
    rw [herase] at hx
    push_cast
    rw [hval]
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · linarith
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have := algConn_le hy
      linarith

/-- On a connected graph the erasure removes the only zero. -/
theorem zero_notMem_erase_of_isConnected {G : IsoGraph} (h : G.IsConnected) :
    (0 : ℝ) ∉ G.lapSpectrum.erase 0 := by
  intro hmem
  have h1 : G.lapSpectrum.count 0 = 1 := by
    rw [count_zero_lapSpectrum, (numComponents_eq_one_iff G).2 h]
  have h2 : (G.lapSpectrum.erase 0).count 0 = 0 := by
    rw [Multiset.count_erase_self, h1]
  rw [← Multiset.one_le_count_iff_mem, h2] at hmem
  omega

/-- **The largest Laplacian eigenvalue of the hypercube** `Q_n` is `2 n`, twice its degree — the
extreme case of `lapLambdaMax_le_two_mul_maxDeg`, as it must be for a bipartite graph. -/
theorem lapLambdaMax_hypercube (n : ℕ) : (hypercube n).lapLambdaMax = 2 * (n : ℝ) := by
  refine lapLambdaMax_eq_of_isGreatest ?_ ?_
  · rw [lapSpectrum_hypercube]
    refine Multiset.mem_sum.2 ⟨n, Finset.self_mem_range_succ n, ?_⟩
    exact Multiset.mem_replicate.2 ⟨by simp, rfl⟩
  · intro x hx
    rw [lapSpectrum_hypercube] at hx
    obtain ⟨j, hj, hxj⟩ := Multiset.mem_sum.1 hx
    rw [Multiset.eq_of_mem_replicate hxj]
    rw [Finset.mem_range] at hj
    have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hj
    linarith

/-- **The algebraic connectivity of the hypercube** `Q_n` is `2`, for every `n ≥ 1`: the Fiedler
value does not degrade as the cube grows, even though the order doubles each time. -/
theorem algConn_hypercube {n : ℕ} (hn : 0 < n) : (hypercube n).algConn = 2 := by
  have hcon : IsConnected (hypercube n) := isConnected_hypercube n
  refine algConn_eq_of_isLeast ?_ ?_
  · refine (Multiset.mem_erase_of_ne (by norm_num)).2 ?_
    rw [lapSpectrum_hypercube]
    refine Multiset.mem_sum.2 ⟨1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · refine Multiset.mem_replicate.2 ⟨?_, ?_⟩
      · rw [Nat.choose_one_right]
        omega
      · norm_num
  · intro x hx
    have hne : x ≠ 0 := fun h0 ↦ zero_notMem_erase_of_isConnected hcon (h0 ▸ hx)
    have hmem := Multiset.mem_of_mem_erase hx
    rw [lapSpectrum_hypercube] at hmem
    obtain ⟨j, hj, hxj⟩ := Multiset.mem_sum.1 hmem
    rw [Multiset.eq_of_mem_replicate hxj] at hne ⊢
    have hj0 : j ≠ 0 := by
      rintro rfl
      norm_num at hne
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0
    linarith

/-- Laplacian cospectral graphs have the same order. -/
theorem LapCospectral.V_eq {G H : IsoGraph} (h : LapCospectral G H) : G.V = H.V := by
  rw [← natDegree_lapCharpoly, ← natDegree_lapCharpoly, h]

/-- **The Laplacian spectrum separates the standard cospectral pair.**  `K₁,₄` and `K₂,₂ ⊔ K₁`
are cospectral (`cospectral_star_four`) but have one and two components, so by
`LapCospectral.numComponents_eq` they are not Laplacian cospectral.  Regularity really is needed
in `Cospectral.lapCospectral`. -/
theorem not_lapCospectral_star_four :
    ¬ LapCospectral (star 4) (bipartite 2 2 ⊕g empty 1) := by
  intro h
  have h1 := h.numComponents_eq
  simp at h1

end IsoGraph

/-! ## The hypercube's extreme eigenvalues

`hypercube_succ` is an isomorphism rather than an equality, so the induction that computes `Q n`'s
spectrum has to run in `IsoGraph`.  Transporting the answer back across `spectrum_mk` is
definitional, and the two ends follow as for the other families — which is why this one section
sits after `end IsoGraph` instead of with the rest. -/

namespace CGraph

/-- **The spectrum of the hypercube** at the level of concrete graphs.  `hypercube_succ` is an
isomorphism rather than an equality, so the statement is made in `IsoGraph` and transported back
here. -/
theorem spectrum_hypercube (n : ℕ) :
    (hypercube n).spectrum
      = ∑ j ∈ Finset.range (n + 1), Multiset.replicate (n.choose j) ((n : ℝ) - 2 * j) :=
  IsoGraph.spectrum_hypercube n

/-- **The spectral radius of the hypercube** `Q_n` is `n`, its degree. -/
theorem lambdaMax_hypercube (n : ℕ) : (hypercube n).lambdaMax = n := by
  refine le_antisymm ((lambdaMax_le_iff _).2 fun x hx ↦ ?_) (le_lambdaMax ?_)
  · rw [spectrum_hypercube, Multiset.mem_sum] at hx
    obtain ⟨j, hj, hx⟩ := hx
    rw [Multiset.eq_of_mem_replicate hx]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · rw [spectrum_hypercube, Multiset.mem_sum]
    exact ⟨0, Finset.mem_range.2 (by omega), by simp⟩

/-- **The least eigenvalue of the hypercube** `Q_n` is `-n`: the cube is bipartite, so its
spectrum is symmetric. -/
theorem lambdaMin_hypercube (n : ℕ) : (hypercube n).lambdaMin = -n := by
  refine le_antisymm (lambdaMin_le ?_) ?_
  · rw [spectrum_hypercube, Multiset.mem_sum]
    refine ⟨n, Finset.mem_range.2 (by omega), ?_⟩
    rw [Nat.choose_self]
    simpa using by ring
  · have hx := lambdaMin_mem_spectrum (hypercube n)
    rw [spectrum_hypercube, Multiset.mem_sum] at hx
    obtain ⟨j, hj, hx⟩ := hx
    have hj' := Finset.mem_range.1 hj
    rw [Multiset.eq_of_mem_replicate hx]
    have hjn : (j : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 (by omega : j ≤ n)
    linarith

end CGraph
