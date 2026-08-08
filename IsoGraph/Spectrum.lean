import IsoGraph.Identities
import IsoGraph.SRG
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Spectral graph theory

The adjacency matrix `CGraph.adjMat` of a graph is real symmetric, so its characteristic
polynomial `CGraph.charpoly` splits over `ℝ` and the *spectrum* `CGraph.spectrum` — the multiset
of roots, equivalently the multiset of `Matrix.IsHermitian.eigenvalues` — has exactly `V` entries.
Both are isomorphism invariants (`charpoly_congr`, `spectrum_congr`), so both descend to
`IsoGraph` at the end of the file.

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
into the eigenvalue statement `μ ↦ n - μ`.

`LapCospectral` is the Laplacian analogue of `Cospectral`, equality of `lapCharpoly` and hence
of `lapSpectrum` (`lapCospectral_iff_lapSpectrum_eq`).  It sees the order, the size and — through
`count_zero_lapSpectrum` — the number of components (`LapCospectral.numComponents_eq`), so
`LapCospectral.isConnected` needs no regularity where `Cospectral.isConnected` does.  For regular
graphs the adjacency notion is the stronger one: `Cospectral.lapCospectral`.

## Line graphs

`transpose_mul_incMat` factors the line graph through the incidence matrix `incMat`, as
`Bᵀ B = A(L G) + 2 I`.  Since `Bᵀ B` is positive semidefinite this gives
`neg_two_le_of_mem_spectrum_lineGraph`: no line graph has an eigenvalue below `-2`, the other
half of the reason ADE turns up here.  The bound is attained whenever `B` has a kernel, which it
does as soon as there are more edges than vertices (`neg_two_mem_spectrum_lineGraph`).

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

/-- The eigenvalues, indexed by the vertices. -/
noncomputable def eigenvalues (G : CGraph) : G.V → ℝ := G.isHermitian_adjMat.eigenvalues

/-- The spectrum: the multiset of eigenvalues, with multiplicity. -/
noncomputable def spectrum (G : CGraph) : Multiset ℝ := G.charpoly.roots

theorem spectrum_eq_map (G : CGraph) :
    G.spectrum = Finset.univ.val.map G.eigenvalues := by
  simpa [spectrum, charpoly, Function.comp_def]
    using G.isHermitian_adjMat.roots_charpoly_eq_eigenvalues

@[simp] theorem card_spectrum (G : CGraph) :
    Multiset.card G.spectrum = Fintype.card G.V := by
  simp [spectrum_eq_map, Finset.card_univ]

@[simp] theorem natDegree_charpoly (G : CGraph) :
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


theorem charpoly_eq_matrix_charpoly (G : CGraph) [inst : DecidableEq G.V] :
    G.charpoly = G.adjMat.charpoly :=
  congrArg (fun d ↦ @Matrix.charpoly ℝ _ G.V d _ G.adjMat) (Subsingleton.elim _ _)

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

/-! ## Isomorphism invariance -/

theorem adjMat_congr {G H : CGraph} (i : G ≃cg H) :
    G.adjMat = Matrix.reindex i.toEquiv.symm i.toEquiv.symm H.adjMat := by
  ext x y
  simp [adjMat_apply, Matrix.reindex_apply, Matrix.submatrix_apply, i.adj_eq x y]

theorem charpoly_congr {G H : CGraph} (i : G ≃cg H) : G.charpoly = H.charpoly := by
  classical
  rw [charpoly_eq_matrix_charpoly, charpoly_eq_matrix_charpoly, adjMat_congr i,
    Matrix.charpoly_reindex]

theorem spectrum_congr {G H : CGraph} (i : G ≃cg H) : G.spectrum = H.spectrum := by
  rw [spectrum, spectrum, charpoly_congr i]

/-! ## The empty graph and the disjoint union -/

@[simp] theorem adjMat_empty (n : ℕ) : (empty n).adjMat = 0 := by
  ext i j; simp [adjMat_apply]

@[simp] theorem charpoly_empty (n : ℕ) : (empty n).charpoly = X ^ n := by
  simp [charpoly, Matrix.charpoly_zero]

@[simp] theorem spectrum_empty (n : ℕ) : (empty n).spectrum = Multiset.replicate n 0 := by
  simp [spectrum, Polynomial.roots_pow, Multiset.nsmul_singleton]

theorem adjMat_disjUnion (G H : CGraph) :
    (disjUnion G H).adjMat = Matrix.fromBlocks G.adjMat 0 0 H.adjMat := by
  ext x y
  cases x <;> cases y <;> simp [adjMat_apply, disjUnion]

@[simp] theorem charpoly_disjUnion (G H : CGraph) :
    (disjUnion G H).charpoly = G.charpoly * H.charpoly := by
  classical
  rw [charpoly_eq_matrix_charpoly, adjMat_disjUnion, Matrix.charpoly_fromBlocks_zero₁₂,
    ← charpoly_eq_matrix_charpoly, ← charpoly_eq_matrix_charpoly]

@[simp] theorem spectrum_disjUnion (G H : CGraph) :
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
@[simp] theorem sum_spectrum (G : CGraph) : G.spectrum.sum = 0 := by
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
theorem Cospectral.E_eq {G H : CGraph} (h : Cospectral G H) : G.E = H.E := by
  have h2 : (2 : ℝ) * G.E = 2 * H.E := by
    rw [← sum_sq_spectrum, ← sum_sq_spectrum, h.spectrum_eq]
  have : (G.E : ℝ) = H.E := by linarith
  exact_mod_cast this

/-- **Cospectral graphs have the same number of triangles**, by the sum of the cubes of the
eigenvalues. -/
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
theorem dynkinD_zero_iso : Nonempty (dynkinD 0 ≃cg dynkinD4) :=
  ⟨isoOfAdj (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (by decide)⟩

/-- `D̃₄` in the parametric family is the star with four edges. -/
theorem affineD_zero_iso : Nonempty (affineD 0 ≃cg affineD4) :=
  ⟨isoOfAdj (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5) (by decide)⟩

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
  refine ⟨fun hb ↦ le_antisymm ?_ (G.neg_lambdaMax_le_lambdaMin), fun hm ↦ ?_⟩
  · refine lambdaMin_le ?_
    rw [← spectrum_neg_of_isBipartite hb, Multiset.mem_map]
    exact ⟨G.lambdaMax, G.lambdaMax_mem_spectrum, rfl⟩
  · exact isBipartite_of_neg_lambdaMax_mem_spectrum hconn (hm ▸ G.lambdaMin_mem_spectrum)

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

theorem lapSpectrum_eq_map (G : CGraph) :
    G.lapSpectrum = Finset.univ.val.map G.lapEigenvalues := by
  simpa [lapSpectrum, lapCharpoly, Function.comp_def]
    using G.isHermitian_lapMat.roots_charpoly_eq_eigenvalues

@[simp] theorem card_lapSpectrum (G : CGraph) :
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

/-- **The Laplacian eigenvalues are nonnegative**: `L` is positive semidefinite. -/
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

theorem lapCharpoly_congr {G H : CGraph} (i : G ≃cg H) : G.lapCharpoly = H.lapCharpoly := by
  classical
  rw [lapCharpoly, lapCharpoly, lapMat_congr i]
  exact Matrix.charpoly_reindex _ _

theorem lapSpectrum_congr {G H : CGraph} (i : G ≃cg H) : G.lapSpectrum = H.lapSpectrum := by
  rw [lapSpectrum, lapSpectrum, lapCharpoly_congr i]

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

@[simp] theorem lapSpectrum_empty (n : ℕ) :
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
@[simp] theorem lapSpectrum_disjUnion (G H : CGraph) :
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
theorem lapSpectrum_of_isRegularWith {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.lapSpectrum = G.spectrum.map (fun x ↦ (k : ℝ) - x) := by
  have hroot : ∀ i : G.V, (X - C ((k : ℝ) - G.eigenvalues i)).roots
      = {(k : ℝ) - G.eigenvalues i} := fun i ↦ Polynomial.roots_X_sub_C _
  rw [lapSpectrum, lapCharpoly_of_isRegularWith h, Polynomial.roots_prod]
  · simp only [hroot, Multiset.bind_singleton, spectrum_eq_map, Multiset.map_map,
      Function.comp_def]
  · exact Finset.prod_ne_zero_iff.2 fun i _ ↦ Polynomial.X_sub_C_ne_zero _

theorem isRegularWith_complete (n : ℕ) : (complete (n + 1)).IsRegularWith n := by
  intro i
  have hnb : (complete (n + 1)).toSimple.neighborFinset i = Finset.univ.erase i := by
    ext j
    simp [SimpleGraph.mem_neighborFinset, ne_comm]
  rw [SimpleGraph.degree, hnb, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  simp

/-- **The Laplacian spectrum of the complete graph** `K_{n+1}`: `0` once, and `n + 1` with
multiplicity `n`. -/
theorem lapSpectrum_complete (n : ℕ) :
    (complete (n + 1)).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate n ((n : ℝ) + 1) := by
  rw [lapSpectrum_of_isRegularWith (isRegularWith_complete n), spectrum_complete,
    Multiset.map_cons, Multiset.map_replicate]
  norm_num

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

/-! ### Laplacian cospectrality -/

@[simp] theorem natDegree_lapCharpoly (G : CGraph) :
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

theorem LapCospectral.lapSpectrum_eq {G H : CGraph} (h : LapCospectral G H) :
    G.lapSpectrum = H.lapSpectrum := by
  rw [lapSpectrum, lapSpectrum, h]

theorem LapCospectral.refl (G : CGraph) : LapCospectral G G := rfl

theorem LapCospectral.symm {G H : CGraph} (h : LapCospectral G H) : LapCospectral H G := Eq.symm h

theorem LapCospectral.trans {G H K : CGraph} (h : LapCospectral G H) (h' : LapCospectral H K) :
    LapCospectral G K := Eq.trans h h'

theorem LapCospectral.of_iso {G H : CGraph} (i : G ≃cg H) : LapCospectral G H :=
  lapCharpoly_congr i

theorem lapCospectral_iff_lapSpectrum_eq (G H : CGraph) :
    G.LapCospectral H ↔ G.lapSpectrum = H.lapSpectrum := by
  refine ⟨LapCospectral.lapSpectrum_eq, fun h ↦ ?_⟩
  rw [LapCospectral, lapCharpoly_eq_prod_lapSpectrum, lapCharpoly_eq_prod_lapSpectrum, h]

/-- **Laplacian cospectral graphs have the same number of vertices.** -/
theorem LapCospectral.card_eq {G H : CGraph} (h : LapCospectral G H) :
    Fintype.card G.V = Fintype.card H.V := by
  rw [← natDegree_lapCharpoly, ← natDegree_lapCharpoly, h]

/-- **Laplacian cospectral graphs have the same number of edges**, by the trace. -/
theorem LapCospectral.E_eq {G H : CGraph} (h : LapCospectral G H) : G.E = H.E := by
  have h2 : (2 : ℝ) * G.E = 2 * H.E := by
    rw [← sum_lapSpectrum, ← sum_lapSpectrum, h.lapSpectrum_eq]
  have : (G.E : ℝ) = H.E := by linarith
  exact_mod_cast this

/-- **Laplacian cospectral graphs have the same number of connected components** — a statement
with no analogue for the adjacency spectrum, which needs regularity to see connectedness. -/
theorem LapCospectral.numComponents_eq {G H : CGraph} (h : LapCospectral G H) :
    G.numComponents = H.numComponents := by
  rw [← count_zero_lapSpectrum, ← count_zero_lapSpectrum, h.lapSpectrum_eq]

/-- **Connectedness is a Laplacian spectral invariant.** -/
theorem LapCospectral.isConnected {G H : CGraph} (h : LapCospectral G H) (hG : G.IsConnected) :
    H.IsConnected := by
  rw [← count_zero_lapSpectrum_eq_one_iff] at hG ⊢
  rw [← h.lapSpectrum_eq]
  exact hG

/-- For regular graphs the two notions agree in one direction: cospectral regular graphs are
Laplacian cospectral. -/
theorem Cospectral.lapCospectral {G H : CGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : LapCospectral G H := by
  rw [lapCospectral_iff_lapSpectrum_eq, lapSpectrum_of_isRegularWith hG,
    lapSpectrum_of_isRegularWith (h.isRegularWith hG), h.spectrum_eq]

end CGraph

namespace IsoGraph

/-! ## The spectrum of an isomorphism class

The characteristic polynomial and the spectrum are isomorphism invariants (`CGraph.charpoly_congr`,
`CGraph.spectrum_congr`), so they descend to `IsoGraph`. -/

/-- The characteristic polynomial of an isomorphism class. -/
noncomputable def charpoly (G : IsoGraph) : ℝ[X] :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.charpoly
    (fun _ _ ⟨i⟩ ↦ CGraph.charpoly_congr i) G

@[simp] theorem charpoly_mk (G : CGraph) : charpoly ⟦G⟧ = G.charpoly := rfl

/-- The spectrum of an isomorphism class. -/
noncomputable def spectrum (G : IsoGraph) : Multiset ℝ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.spectrum
    (fun _ _ ⟨i⟩ ↦ CGraph.spectrum_congr i) G

@[simp] theorem spectrum_mk (G : CGraph) : spectrum ⟦G⟧ = G.spectrum := rfl

theorem spectrum_eq_roots_charpoly (G : IsoGraph) : G.spectrum = G.charpoly.roots :=
  Quotient.inductionOn G fun _ ↦ rfl

@[simp] theorem card_spectrum (G : IsoGraph) : Multiset.card G.spectrum = G.V :=
  Quotient.inductionOn G fun g ↦ g.card_spectrum

@[simp] theorem natDegree_charpoly (G : IsoGraph) : G.charpoly.natDegree = G.V :=
  Quotient.inductionOn G fun g ↦ g.natDegree_charpoly

@[simp] theorem sum_spectrum (G : IsoGraph) : G.spectrum.sum = 0 :=
  Quotient.inductionOn G fun g ↦ g.sum_spectrum

theorem sum_sq_spectrum (G : IsoGraph) : (G.spectrum.map (· ^ 2)).sum = 2 * (G.E : ℝ) :=
  Quotient.inductionOn G fun g ↦ g.sum_sq_spectrum

/-- **The third moment counts triangles**, six times over. -/
theorem sum_cube_spectrum (G : IsoGraph) :
    (G.spectrum.map (· ^ 3)).sum = 6 * (G.cliqueCount 3 : ℝ) :=
  Quotient.inductionOn G fun g ↦ g.sum_cube_spectrum

@[simp] theorem spectrum_empty (n : ℕ) : (empty n).spectrum = Multiset.replicate n 0 :=
  CGraph.spectrum_empty n

theorem spectrum_complete (n : ℕ) :
    (complete (n + 1)).spectrum = (n : ℝ) ::ₘ Multiset.replicate n (-1) :=
  CGraph.spectrum_complete n

theorem spectrum_path (n : ℕ) :
    (path n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (Real.pi * (m.1 + 1) / (n + 1))) :=
  CGraph.spectrum_path n

theorem spectrum_cycle {n : ℕ} (hn : 3 ≤ n) :
    (cycle n).spectrum
      = Finset.univ.val.map (fun m : Fin n ↦ 2 * Real.cos (2 * Real.pi * m.1 / n)) :=
  CGraph.spectrum_cycle hn

@[simp] theorem charpoly_disjUnion (G H : IsoGraph) :
    (G ⊕g H).charpoly = G.charpoly * H.charpoly :=
  Quotient.inductionOn₂ G H fun g h ↦ CGraph.charpoly_disjUnion g h

@[simp] theorem spectrum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).spectrum = G.spectrum + H.spectrum :=
  Quotient.inductionOn₂ G H fun g h ↦ CGraph.spectrum_disjUnion g h

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
    have h2 : (complete 2).spectrum = (1 : ℝ) ::ₘ Multiset.replicate 1 (-1) := by
      have := spectrum_complete 1
      norm_num at this
      simpa using this
    rw [hypercube_succ, spectrum_cartesianProduct, h2, product_pm_one, ih]
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

/-! ### Determined by the spectrum -/

/-- Two isomorphism classes are **cospectral** when they have the same characteristic polynomial. -/
def Cospectral (G H : IsoGraph) : Prop := G.charpoly = H.charpoly

theorem Cospectral.spectrum_eq {G H : IsoGraph} (h : Cospectral G H) : G.spectrum = H.spectrum := by
  rw [spectrum_eq_roots_charpoly, spectrum_eq_roots_charpoly, h]

@[simp] theorem cospectral_mk (G H : CGraph) : Cospectral ⟦G⟧ ⟦H⟧ ↔ G.Cospectral H := Iff.rfl

/-- Cospectral graphs have the same order. -/
theorem Cospectral.V_eq {G H : IsoGraph} (h : Cospectral G H) : G.V = H.V := by
  rw [← natDegree_charpoly, ← natDegree_charpoly, h]

/-- Cospectral graphs have the same number of edges. -/
theorem Cospectral.E_eq {G H : IsoGraph} (h : Cospectral G H) : G.E = H.E :=
  Quotient.inductionOn₂ G H (fun _ _ h ↦ CGraph.Cospectral.E_eq h) h

/-- Cospectral graphs have the same number of triangles. -/
theorem Cospectral.cliqueCount_three_eq {G H : IsoGraph} (h : Cospectral G H) :
    G.cliqueCount 3 = H.cliqueCount 3 :=
  Quotient.inductionOn₂ G H (fun _ _ h ↦ CGraph.Cospectral.cliqueCount_three_eq h) h

/-- **Regularity is determined by the spectrum.** -/
theorem Cospectral.isRegularWith {G H : IsoGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : H.IsRegularWith k :=
  Quotient.inductionOn₂ G H (fun _ _ h hG ↦ CGraph.Cospectral.isRegularWith h hG) h hG

/-- **Connectedness of a regular graph is determined by the spectrum.** -/
theorem Cospectral.isConnected {G H : IsoGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) (hconn : G.IsConnected) : H.IsConnected :=
  Quotient.inductionOn₂ G H
    (fun _ _ h hG hconn ↦ CGraph.Cospectral.isConnected h hG hconn) h hG hconn

/-- **Bipartiteness of a connected regular graph is determined by the spectrum.** -/
theorem Cospectral.isBipartite {G H : IsoGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) (hconn : G.IsConnected) (hbip : IsBipartite G) : IsBipartite H :=
  Quotient.inductionOn₂ G H
    (fun _ _ h hG hconn hbip ↦ CGraph.Cospectral.isBipartite h hG hconn hbip) h hG hconn hbip

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

theorem cospectral_star_four : Cospectral (star 4) (bipartite 2 2 ⊕g empty 1) := by
  rw [star_def, bipartite_def, empty_def, disjUnion_mk, cospectral_mk]
  exact CGraph.cospectral_star_four

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

/-- **A strongly regular graph has at most three distinct eigenvalues.** -/
theorem card_toFinset_spectrum_le_three_of_isSRGWith {G : IsoGraph} {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) : G.spectrum.toFinset.card ≤ 3 := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [spectrum_mk]
    rw [isSRGWith_mk] at h
    exact CGraph.card_toFinset_spectrum_le_three_of_isSRGWith h

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

/-- **A connected regular graph with three distinct eigenvalues is strongly regular.** -/
theorem exists_isSRGWith_of_card_toFinset_spectrum_eq_three {G : IsoGraph} {k : ℕ}
    (hconn : G.IsConnected) (hreg : G.IsRegularWith k) (h3 : G.spectrum.toFinset.card = 3) :
    ∃ l m : ℕ, G.IsSRGWith G.V k l m := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [spectrum_mk] at h3
    rw [isConnected_mk] at hconn
    rw [isRegularWith_mk] at hreg
    rw [V_mk]
    simpa only [isSRGWith_mk] using
      CGraph.exists_isSRGWith_of_card_toFinset_spectrum_eq_three hconn hreg h3

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

/-- The Laplacian spectrum of an isomorphism class. -/
noncomputable def lapSpectrum (G : IsoGraph) : Multiset ℝ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.lapSpectrum
    (fun _ _ ⟨i⟩ ↦ CGraph.lapSpectrum_congr i) G

@[simp] theorem lapSpectrum_mk (G : CGraph) : lapSpectrum ⟦G⟧ = G.lapSpectrum := rfl

@[simp] theorem card_lapSpectrum (G : IsoGraph) : Multiset.card G.lapSpectrum = G.V :=
  Quotient.inductionOn G fun g ↦ g.card_lapSpectrum

theorem nonneg_of_mem_lapSpectrum {G : IsoGraph} {x : ℝ} (hx : x ∈ G.lapSpectrum) : 0 ≤ x := by
  induction G using Quotient.inductionOn with
  | h g => exact g.nonneg_of_mem_lapSpectrum hx

theorem sum_lapSpectrum (G : IsoGraph) : G.lapSpectrum.sum = 2 * (G.E : ℝ) :=
  Quotient.inductionOn G fun g ↦ g.sum_lapSpectrum

/-- **The multiplicity of `0` in the Laplacian spectrum is the number of components.** -/
theorem count_zero_lapSpectrum (G : IsoGraph) : G.lapSpectrum.count 0 = G.numComponents :=
  Quotient.inductionOn G fun g ↦ g.count_zero_lapSpectrum

@[simp] theorem lapSpectrum_empty (n : ℕ) : (empty n).lapSpectrum = Multiset.replicate n 0 :=
  CGraph.lapSpectrum_empty n

/-- **The Laplacian spectrum of a disjoint union is the sum of the spectra.** -/
@[simp] theorem lapSpectrum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).lapSpectrum = G.lapSpectrum + H.lapSpectrum :=
  Quotient.inductionOn₂ G H fun g h ↦ CGraph.lapSpectrum_disjUnion g h

/-- **The Laplacian spectrum of a `k`-regular graph is `k` minus its adjacency spectrum.** -/
theorem lapSpectrum_of_isRegularWith {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.lapSpectrum = G.spectrum.map (fun x ↦ (k : ℝ) - x) := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [isRegularWith_mk] at h
    rw [lapSpectrum_mk, spectrum_mk, CGraph.lapSpectrum_of_isRegularWith h]

/-- **The Laplacian spectrum of the complete graph** `K_{n+1}`: `0` once, and `n + 1` with
multiplicity `n`. -/
theorem lapSpectrum_complete (n : ℕ) :
    (complete (n + 1)).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate n ((n : ℝ) + 1) :=
  CGraph.lapSpectrum_complete n

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

/-! ### Laplacian cospectrality -/

/-- The Laplacian characteristic polynomial of an isomorphism class. -/
noncomputable def lapCharpoly (G : IsoGraph) : ℝ[X] :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.lapCharpoly
    (fun _ _ ⟨i⟩ ↦ CGraph.lapCharpoly_congr i) G

@[simp] theorem lapCharpoly_mk (G : CGraph) : lapCharpoly ⟦G⟧ = G.lapCharpoly := rfl

@[simp] theorem natDegree_lapCharpoly (G : IsoGraph) : G.lapCharpoly.natDegree = G.V :=
  Quotient.inductionOn G fun g ↦ g.natDegree_lapCharpoly

theorem lapSpectrum_eq_roots_lapCharpoly (G : IsoGraph) : G.lapSpectrum = G.lapCharpoly.roots :=
  Quotient.inductionOn G fun _ ↦ rfl

/-- Two isomorphism classes are **Laplacian cospectral** when their Laplacian characteristic
polynomials agree. -/
def LapCospectral (G H : IsoGraph) : Prop := G.lapCharpoly = H.lapCharpoly

@[simp] theorem lapCospectral_mk (G H : CGraph) :
    LapCospectral ⟦G⟧ ⟦H⟧ ↔ G.LapCospectral H := Iff.rfl

theorem LapCospectral.lapSpectrum_eq {G H : IsoGraph} (h : LapCospectral G H) :
    G.lapSpectrum = H.lapSpectrum := by
  rw [lapSpectrum_eq_roots_lapCharpoly, lapSpectrum_eq_roots_lapCharpoly, h]

theorem lapCospectral_iff_lapSpectrum_eq (G H : IsoGraph) :
    LapCospectral G H ↔ G.lapSpectrum = H.lapSpectrum :=
  Quotient.inductionOn₂ G H fun g h ↦ CGraph.lapCospectral_iff_lapSpectrum_eq g h

/-- Laplacian cospectral graphs have the same order. -/
theorem LapCospectral.V_eq {G H : IsoGraph} (h : LapCospectral G H) : G.V = H.V := by
  rw [← natDegree_lapCharpoly, ← natDegree_lapCharpoly, h]

/-- Laplacian cospectral graphs have the same number of edges. -/
theorem LapCospectral.E_eq {G H : IsoGraph} (h : LapCospectral G H) : G.E = H.E :=
  Quotient.inductionOn₂ G H (fun _ _ h ↦ CGraph.LapCospectral.E_eq h) h

/-- **Laplacian cospectral graphs have the same number of connected components.** -/
theorem LapCospectral.numComponents_eq {G H : IsoGraph} (h : LapCospectral G H) :
    G.numComponents = H.numComponents :=
  Quotient.inductionOn₂ G H (fun _ _ h ↦ CGraph.LapCospectral.numComponents_eq h) h

/-- **Connectedness is a Laplacian spectral invariant**, with no regularity hypothesis. -/
theorem LapCospectral.isConnected {G H : IsoGraph} (h : LapCospectral G H) (hG : G.IsConnected) :
    H.IsConnected :=
  Quotient.inductionOn₂ G H (fun _ _ h hG ↦ CGraph.LapCospectral.isConnected h hG) h hG

/-- Cospectral regular graphs are Laplacian cospectral. -/
theorem Cospectral.lapCospectral {G H : IsoGraph} (h : Cospectral G H) {k : ℕ}
    (hG : G.IsRegularWith k) : LapCospectral G H :=
  Quotient.inductionOn₂ G H (fun _ _ h hG ↦ CGraph.Cospectral.lapCospectral h hG) h hG

end IsoGraph
