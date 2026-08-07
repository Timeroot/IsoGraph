import IsoGraph.Identities
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
* `hasEigenvector_compl` — for the complement only the eigenvector statement is proved: an
  eigenvector of `G` orthogonal to the all-ones vector is an eigenvector of `Gᶜ` for the
  eigenvalue `-1 - x`, since `Gᶜ`'s adjacency matrix is `J - I - A`.  The all-ones vector itself
  is handled by `hasEigenvector_one_of_isRegularWith`, so for a `k`-regular graph this determines
  every eigenvalue.

## Trace identities and cospectrality

`sum_spectrum` (the trace is zero) and `sum_sq_spectrum` (the trace of `A ^ 2` is `2 E`) are the
first two moments.  `Cospectral G H` is equality of characteristic polynomials; it is implied by
isomorphism (`Cospectral.of_iso`) and it implies equality of `V` and of `E`.  A graph is
*determined by its spectrum*, `IsDS`, when the converse holds for it.  Two families are proved to
be: `isDS_empty` and `isDS_complete`, the latter by squeezing the degree sequence between
`sum_sq_spectrum` and `SimpleGraph.degree_lt_card_verts`.

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

## The Smith family and ADE

`IsSmith G` says `2` is the largest eigenvalue of `G` and `IsSubcritical G` says every eigenvalue
is below `2`.  Smith's theorem classifies the connected graphs of each kind: the subcritical ones
are the simply-laced Dynkin diagrams `Aₙ Dₙ E₆ E₇ E₈`, and the critical ones are their affine
extensions `Ãₙ D̃ₙ Ẽ₆ Ẽ₇ Ẽ₈`.  The classification itself is not formalised, but every diagram in
it is: `isSubcritical_path` (`Aₙ`), `isSmith_cycle` (`Ãₙ`), the parametric families
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

private theorem map_product_mul {α β : Type} (f : α → ℝ) (g : β → ℝ)
    (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map (fun p ↦ f p.1 * g p.2) = ((s.map f) ×ˢ (t.map g)).map (fun p ↦ p.1 * p.2) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp [Multiset.cons_product, Multiset.map_map, ih]

theorem spectrum_tensorProduct' (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).spectrum = (G.spectrum ×ˢ H.spectrum).map (fun p ↦ p.1 * p.2) := by
  rw [spectrum_tensorProduct, spectrum_eq_map, spectrum_eq_map, ← map_product_mul,
    ← Finset.univ_product_univ, Finset.product_val]

/-! ## Traces: the order and the size are read off the spectrum -/

/-- **The eigenvalues sum to zero**, because the adjacency matrix has zero diagonal. -/
@[simp] theorem sum_spectrum (G : CGraph) : G.spectrum.sum = 0 := by
  classical
  have h1 : G.adjMat.trace = ∑ i, G.eigenvalues i :=
    G.isHermitian_adjMat.trace_eq_sum_eigenvalues
  have h2 : G.adjMat.trace = 0 := SimpleGraph.trace_adjMatrix (α := ℝ) _
  rw [spectrum_eq_map]
  exact h1.symm.trans h2

theorem trace_adjMat_sq (G : CGraph) :
    (G.adjMat * G.adjMat).trace = ∑ i, (G.eigenvalues i) ^ 2 := by
  classical
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_conj_diagonal G
  set D : Matrix G.V G.V ℝ := Matrix.diagonal G.eigenvalues with hD
  have hA : G.adjMat = P * D * Q := by
    calc G.adjMat = G.adjMat * (P * Q) := by rw [hPQ, mul_one]
      _ = G.adjMat * P * Q := by rw [mul_assoc]
      _ = P * D * Q := by rw [h]
  calc (G.adjMat * G.adjMat).trace = (P * (D * D) * Q).trace := by
        rw [hA]
        congr 1
        calc P * D * Q * (P * D * Q) = P * D * (Q * P) * D * Q := by
              simp only [mul_assoc]
          _ = P * (D * D) * Q := by rw [hQP]; simp only [mul_assoc, mul_one]
    _ = (Q * (P * (D * D))).trace := by rw [Matrix.trace_mul_comm]
    _ = (D * D).trace := by rw [← mul_assoc, hQP, one_mul]
    _ = ∑ i, (G.eigenvalues i) ^ 2 := by
        rw [hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
        exact Finset.sum_congr rfl fun i _ ↦ (sq _).symm

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
