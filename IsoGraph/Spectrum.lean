import IsoGraph.Identities
import IsoGraph.SRG
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.RingTheory.RootsOfUnity.Complex

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
isomorphism (`Cospectral.of_iso`) and it implies equality of `V` and of `E`.  A graph is
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
`one_le_lambdaMax` and `lambdaMin_le_neg_one`.  From the other side,
`abs_le_maxDeg_of_mem_spectrum` bounds every eigenvalue by the maximum degree, by evaluating the
eigenvector equation where the eigenvector is largest.

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

end IsoGraph
