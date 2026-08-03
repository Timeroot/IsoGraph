import IsoGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Perm

/-!
# Invariants

An *invariant* here is a quantity attached to a `CGraph` that is unchanged by isomorphism, and so
descends to `IsoGraph`.  Each one appears twice:

* at the `CGraph` level, as a thin wrapper around the corresponding Mathlib notion for
  `G.toSimple` — this is the form statements about concrete graphs are proved in;
* at the `IsoGraph` level, as a `Quotient.lift` of it, whose side condition is exactly
  isomorphism-invariance.

The `SimpleGraph.Iso` section below supplies the invariance lemmas that Mathlib does not already
have.
-/

open Fintype

/-! ## Isomorphism-invariance lemmas for `SimpleGraph` -/

namespace SimpleGraph.Iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- The image of an `n`-clique under an isomorphism is an `n`-clique. -/
theorem isNClique_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNClique n s) :
    G'.IsNClique n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact f.map_adj_iff.2 (h.1 hx hy fun e ↦ hab (by rw [e]))

/-- The image of an independent `n`-set under an isomorphism is an independent `n`-set. -/
theorem isNIndepSet_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNIndepSet n s) :
    G'.IsNIndepSet n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact fun hadj ↦ h.1 hx hy (fun e ↦ hab (by rw [e])) (f.map_adj_iff.1 hadj)

theorem cliqueNum_eq (f : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f.symm hs⟩⟩

theorem indepNum_eq (f : G ≃g G') : G.indepNum = G'.indepNum := by
  unfold SimpleGraph.indepNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f.symm hs⟩⟩

/-- Isomorphic graphs have the same multiset of degrees. -/
theorem degrees_eq [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]
    (f : G ≃g G') :
    (Finset.univ.val.map fun v ↦ G.degree v) = Finset.univ.val.map fun w ↦ G'.degree w := by
  conv_rhs => rw [← Finset.map_univ_equiv f.toEquiv]
  rw [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun v _ ↦ ?_
  exact (f.degree_eq v).symm

/-- Pushing a walk forward along an isomorphism can only shorten the extended distance; applying
this to `f` and to `f.symm` gives `edist_eq`. -/
private theorem edist_le_of_iso (f : G ≃g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  rw [SimpleGraph.edist_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨w, rfl⟩
  simpa using SimpleGraph.edist_le (w.map f.toHom)

/-- Isomorphisms preserve the extended distance. -/
theorem edist_eq (f : G ≃g G') (u v : V) : G.edist u v = G'.edist (f u) (f v) :=
  le_antisymm (by simpa using edist_le_of_iso f.symm (f u) (f v)) (edist_le_of_iso f u v)

/-- Isomorphic graphs have the same extended diameter. -/
theorem ediam_eq (f : G ≃g G') : G.ediam = G'.ediam := by
  refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
    (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
  · rw [edist_eq f]; exact SimpleGraph.edist_le_ediam
  · rw [edist_eq f.symm]; exact SimpleGraph.edist_le_ediam

/-- Isomorphic graphs have the same diameter. -/
theorem diam_eq (f : G ≃g G') : G.diam = G'.diam :=
  congrArg ENat.toNat (ediam_eq f)

/-- An isomorphism restricts to a bijection between common neighbourhoods. -/
def commonNeighborsEquiv (f : G ≃g G') (v w : V) :
    G.commonNeighbors v w ≃ G'.commonNeighbors (f v) (f w) :=
  Equiv.subtypeEquiv f.toEquiv fun x ↦ by
    simp [SimpleGraph.mem_commonNeighbors, f.map_adj_iff]

theorem card_commonNeighbors_eq [Fintype V] [Fintype W] [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (f : G ≃g G') (v w : V) :
    Fintype.card (G.commonNeighbors v w) = Fintype.card (G'.commonNeighbors (f v) (f w)) :=
  Fintype.card_congr (commonNeighborsEquiv f v w)

section StronglyRegular

variable [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj] {n k ℓ μ : ℕ}

/-- Strong regularity transfers along an isomorphism. -/
theorem isSRGWith_of_iso (f : G ≃g G') (h : G.IsSRGWith n k ℓ μ) : G'.IsSRGWith n k ℓ μ where
  card := by rw [← Fintype.card_congr f.toEquiv]; exact h.card
  regular v := by
    obtain ⟨u, rfl⟩ := f.surjective v
    rw [f.degree_eq u]
    exact h.regular u
  of_adj v w hvw := by
    obtain ⟨u, rfl⟩ := f.surjective v
    obtain ⟨t, rfl⟩ := f.surjective w
    rw [← card_commonNeighbors_eq f]
    exact h.of_adj u t (f.map_adj_iff.1 hvw)
  of_not_adj := by
    intro v w hne hvw
    obtain ⟨u, rfl⟩ := f.surjective v
    obtain ⟨t, rfl⟩ := f.surjective w
    rw [← card_commonNeighbors_eq f]
    exact h.of_not_adj (fun e ↦ hne (congrArg f e)) fun hut ↦ hvw (f.map_adj_iff.2 hut)

/-- Isomorphic graphs are strongly regular with the same parameters. -/
theorem isSRGWith_iff (f : G ≃g G') : G.IsSRGWith n k ℓ μ ↔ G'.IsSRGWith n k ℓ μ :=
  ⟨isSRGWith_of_iso f, isSRGWith_of_iso f.symm⟩

end StronglyRegular

end SimpleGraph.Iso

/-! ## Invariants of a `CGraph` -/

namespace CGraph

variable (G : CGraph)

/-- Independence number: the size of a largest set of pairwise non-adjacent vertices. -/
noncomputable def indepNum : ℕ := G.toSimple.indepNum

/-- Clique number: the size of a largest set of pairwise adjacent vertices. -/
noncomputable def cliqueNum : ℕ := G.toSimple.cliqueNum

/-- Number of edges. -/
def E : ℕ := G.toSimple.edgeFinset.card

/-- Sorted degree sequence. -/
def degSequence : List ℕ := (Finset.univ.val.map fun v ↦ G.toSimple.degree v).sort (· ≤ ·)

/-- The graph is connected (in particular, nonempty). -/
def IsConnected : Prop := G.toSimple.Connected

/-- The graph has no cycles. -/
def IsAcyclic : Prop := G.toSimple.IsAcyclic

/-- Diameter, i.e. the largest distance between two vertices — `0` if the graph is disconnected
(this is Mathlib's convention for `SimpleGraph.diam`). -/
noncomputable def diameter : ℕ := G.toSimple.diam

/-- The graph is a tree. -/
def IsTree : Prop := G.toSimple.IsTree

/-- The graph is *strongly regular* with parameters `(n, k, ℓ, μ)`: it has `n` vertices, every
vertex has degree `k`, adjacent vertices have `ℓ` common neighbours, and distinct non-adjacent
vertices have `μ`.  Unlike the invariants above this one takes the parameters as arguments; it is
a property, not a number, and `IsoGraph/SRG.lean` is a table of graphs satisfying it. -/
def IsSRGWith (n k ℓ μ : ℕ) : Prop := G.toSimple.IsSRGWith n k ℓ μ

/-- The neighbours of `v`, as a `Finset`.  Same thing as `G.toSimple.neighborFinset v`
(`neighborFinset_eq_nbrs`), but phrased with `CGraph.Adj` so that it can be computed with and
rewritten by the `…_adj` simp lemmas of `IsoGraph/Constructions.lean`. -/
def nbrs (v : G.V) : Finset G.V := Finset.univ.filter fun w ↦ G.Adj v w = true

@[simp] theorem mem_nbrs (v w : G.V) : w ∈ G.nbrs v ↔ G.Adj v w = true := by simp [nbrs]

theorem neighborFinset_eq_nbrs (v : G.V) : G.toSimple.neighborFinset v = G.nbrs v := by
  ext w; simp

theorem card_commonNeighbors [DecidableEq G.V] (v w : G.V) :
    Fintype.card (G.toSimple.commonNeighbors v w) = (G.nbrs v ∩ G.nbrs w).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext x
  simp [SimpleGraph.mem_commonNeighbors]

/-- **Strong regularity, spelled out in `Finset` terms.**  No `SimpleGraph`, no `Fintype.card` of
a subtype and no `Sym2`: just the neighbour sets of `nbrs` and their intersections, which is the
form in which the families of `IsoGraph/SRG.lean` are proved. -/
theorem isSRGWith_of [DecidableEq G.V] {n k ℓ μ : ℕ} (hn : Fintype.card G.V = n)
    (hk : ∀ v, (G.nbrs v).card = k)
    (hℓ : ∀ v w, G.Adj v w = true → (G.nbrs v ∩ G.nbrs w).card = ℓ)
    (hμ : ∀ v w, v ≠ w → G.Adj v w = false → (G.nbrs v ∩ G.nbrs w).card = μ) :
    G.IsSRGWith n k ℓ μ where
  card := hn
  regular v := by rw [SimpleGraph.degree, neighborFinset_eq_nbrs, hk]
  of_adj v w h := by rw [card_commonNeighbors]; exact hℓ v w h
  of_not_adj v w hne h := by
    rw [card_commonNeighbors]
    exact hμ v w hne (by simpa using h)

/-! ### Bipartiteness -/

/-- The graph is *bipartite*: some two-colouring of the vertices leaves no edge monochromatic.
Stated with `Bool` rather than with a pair of vertex sets, which is what makes it directly usable
as the splitting criterion for the bipartite double cover in `IsoGraph/Identities.lean`. -/
def IsBipartite : Prop := ∃ c : G.V → Bool, ∀ x y, G.Adj x y → c x ≠ c y

/-- Bipartiteness transfers along an isomorphism. -/
theorem isBipartite_of_iso {G H : CGraph} (i : G ≃cg H) (h : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun v ↦ c (i.symm v), fun x y hxy ↦ hc _ _ ?_⟩
  rw [← i.adj_eq, i.apply_symm_apply, i.apply_symm_apply]
  exact hxy

/-- Bipartiteness is 2-colourability, in Mathlib's sense. -/
theorem isBipartite_iff_colorable : G.IsBipartite ↔ G.toSimple.Colorable 2 := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨SimpleGraph.Coloring.mk (fun v ↦ if c v then 1 else 0) ?_⟩
    intro x y hxy
    have hne := hc x y (by simpa using hxy)
    rcases hcx : c x <;> rcases hcy : c y <;> simp_all
  · rintro ⟨c⟩
    refine ⟨fun v ↦ decide (c v = 1), fun x y hxy ↦ ?_⟩
    have hne : c x ≠ c y := c.valid (by simpa using hxy)
    have hx := (c x).isLt
    have hy := (c y).isLt
    have : (c x).1 ≠ (c y).1 := fun h ↦ hne (Fin.ext h)
    simp only [ne_eq, decide_eq_decide, Fin.ext_iff]
    omega

/-- Bipartiteness is decidable: there are only `2 ^ n` colourings to try.  Like the transitivity
instances below this is exponential, and meant for small graphs only. -/
instance [DecidableEq G.V] : Decidable G.IsBipartite :=
  decidable_of_iff (∃ c : G.V → Bool, ∀ x y, G.Adj x y → c x ≠ c y) Iff.rfl

/-! ### Transitivity

Two symmetry properties, stated directly in terms of `CGraph.Iso` automorphisms rather than in
terms of a group action.  They are what makes the clique sums of `IsoGraph/CliqueSum.lean`
well defined: gluing at a vertex is unambiguous exactly when the automorphism group can move any
vertex to any other, and gluing along an edge when it can move any *arc* to any other. -/

/-- The automorphism group acts transitively on vertices. -/
def IsVertexTransitive : Prop := ∀ u v : G.V, ∃ σ : G ≃cg G, σ u = v

/-- The automorphism group acts transitively on arcs, i.e. on *ordered* pairs of adjacent
vertices.  This is strictly stronger than edge-transitivity, which only asks for the unordered
pairs. -/
def IsArcTransitive : Prop :=
  ∀ u v u' v' : G.V, G.Adj u v → G.Adj u' v' → ∃ σ : G ≃cg G, σ u = u' ∧ σ v = v'

/-- A permutation of the vertices that preserves adjacency is an automorphism. -/
def autoOfPerm {G : CGraph} (σ : Equiv.Perm G.V) (h : ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y) :
    G ≃cg G :=
  ⟨σ, by intro x y; simp [h x y]⟩

@[simp] theorem autoOfPerm_apply {G : CGraph} (σ : Equiv.Perm G.V)
    (h : ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y) (x : G.V) : autoOfPerm σ h x = σ x := rfl

theorem isVertexTransitive_iff [DecidableEq G.V] :
    G.IsVertexTransitive ↔
      ∀ u v : G.V, ∃ σ : Equiv.Perm G.V, (∀ x y, G.Adj (σ x) (σ y) = G.Adj x y) ∧ σ u = v := by
  constructor
  · intro h u v
    obtain ⟨σ, hσ⟩ := h u v
    exact ⟨σ.toEquiv, fun x y ↦ σ.adj_eq x y, hσ⟩
  · intro h u v
    obtain ⟨σ, hσ, huv⟩ := h u v
    exact ⟨autoOfPerm σ hσ, huv⟩

theorem isArcTransitive_iff [DecidableEq G.V] :
    G.IsArcTransitive ↔
      ∀ u v u' v' : G.V, G.Adj u v → G.Adj u' v' →
        ∃ σ : Equiv.Perm G.V, (∀ x y, G.Adj (σ x) (σ y) = G.Adj x y) ∧ σ u = u' ∧ σ v = v' := by
  constructor
  · intro h u v u' v' huv hu'v'
    obtain ⟨σ, hσ⟩ := h u v u' v' huv hu'v'
    exact ⟨σ.toEquiv, fun x y ↦ σ.adj_eq x y, hσ⟩
  · intro h u v u' v' huv hu'v'
    obtain ⟨σ, hσ, h₁, h₂⟩ := h u v u' v' huv hu'v'
    exact ⟨autoOfPerm σ hσ, h₁, h₂⟩

/-- Transitivity transfers along an isomorphism. -/
theorem isVertexTransitive_of_iso {G H : CGraph} (i : G ≃cg H) (h : G.IsVertexTransitive) :
    H.IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ⟩ := h (i.symm u) (i.symm v)
  exact ⟨(i.symm.trans σ).trans i, by simp [hσ]⟩

theorem isArcTransitive_of_iso {G H : CGraph} (i : G ≃cg H) (h : G.IsArcTransitive) :
    H.IsArcTransitive := by
  intro u v u' v' huv hu'v'
  have h₁ : G.Adj (i.symm u) (i.symm v) := by
    rw [← i.adj_eq, i.apply_symm_apply, i.apply_symm_apply]; exact huv
  have h₂ : G.Adj (i.symm u') (i.symm v') := by
    rw [← i.adj_eq, i.apply_symm_apply, i.apply_symm_apply]; exact hu'v'
  obtain ⟨σ, hσ₁, hσ₂⟩ := h _ _ _ _ h₁ h₂
  exact ⟨(i.symm.trans σ).trans i, by simp [hσ₁], by simp [hσ₂]⟩

/-! Both `IsConnected` and `IsAcyclic` are decidable — but only once the vertex type has a
`DecidableEq`, which a `Fintype` alone does not give.  Constructions that produce a concrete
vertex type supply it; see `IsoGraph/Constructions.lean`. -/

instance [DecidableEq G.V] : Decidable G.IsConnected :=
  inferInstanceAs (Decidable G.toSimple.Connected)

instance [DecidableEq G.V] : Decidable G.IsAcyclic :=
  decidable_of_iff (∀ (v w : G.V) (p q : G.toSimple.Path v w), p = q)
    SimpleGraph.isAcyclic_iff_path_unique.symm

instance [DecidableEq G.V] : Decidable G.IsTree :=
  decidable_of_iff (G.IsConnected ∧ G.IsAcyclic)
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- Strong regularity is decidable: it is four bounded quantifications over the vertex type.  The
`DecidableEq` is needed only for the "distinct and non-adjacent" clause.

This runs in time `O(n³)`, so `native_decide` settles it for the graphs of `IsoGraph/SRG.lean`;
the kernel would not get far. -/
instance [DecidableEq G.V] (n k ℓ μ : ℕ) : Decidable (G.IsSRGWith n k ℓ μ) :=
  decidable_of_iff
    (Fintype.card G.V = n ∧ (∀ v, G.toSimple.degree v = k) ∧
      (∀ v w, G.toSimple.Adj v w → Fintype.card (G.toSimple.commonNeighbors v w) = ℓ) ∧
      (∀ v w, v ≠ w → ¬G.toSimple.Adj v w → Fintype.card (G.toSimple.commonNeighbors v w) = μ))
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, fun _ _ hne ↦ h₄ _ _ hne⟩,
      fun h ↦ ⟨h.card, h.regular, h.of_adj, fun _ _ hne ↦ h.of_not_adj hne⟩⟩

/-- Vertex-transitivity is decidable by enumerating the `n!` permutations of the vertex type — so
this is for tiny graphs only, and the structural lemmas of `IsoGraph/Constructions.lean` are the
way to settle anything larger.  Even `native_decide` starts to labour at eight vertices. -/
instance [DecidableEq G.V] : Decidable G.IsVertexTransitive :=
  decidable_of_iff _ (isVertexTransitive_iff G).symm

/-- Arc-transitivity is decidable, with the same `n!` caveat as `IsVertexTransitive`. -/
instance [DecidableEq G.V] : Decidable G.IsArcTransitive :=
  decidable_of_iff _ (isArcTransitive_iff G).symm

end CGraph

/-! ## Invariants of an `IsoGraph`

Each is a `Quotient.lift` of the corresponding `CGraph` invariant; the side condition is exactly
the isomorphism-invariance lemma above. -/

namespace IsoGraph

/-- Independence number. -/
noncomputable def indepNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.indepNum
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.indepNum_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem indepNum_mk (G : CGraph) :
    indepNum (Quotient.mk _ G) = G.indepNum := rfl

/-- Clique number. -/
noncomputable def cliqueNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.cliqueNum
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.cliqueNum_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem cliqueNum_mk (G : CGraph) :
    cliqueNum (Quotient.mk _ G) = G.cliqueNum := rfl

/-- Number of edges. -/
def E (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.E
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.card_edgeFinset_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem E_mk (G : CGraph) : E (Quotient.mk _ G) = G.E := rfl

/-- Sorted degree sequence. -/
def degSequence (G : IsoGraph) : List ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.degSequence
    (fun _ _ ⟨i⟩ ↦ congrArg (fun m : Multiset ℕ ↦ m.sort (· ≤ ·))
      (SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem degSequence_mk (G : CGraph) :
    degSequence (Quotient.mk _ G) = G.degSequence := rfl

/-- Connectivity. -/
def IsConnected (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsConnected
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.connected_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isConnected_mk (G : CGraph) :
    IsConnected (Quotient.mk _ G) = G.IsConnected := rfl

/-- Acyclicity. -/
def IsAcyclic (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsAcyclic
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.isAcyclic_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isAcyclic_mk (G : CGraph) :
    IsAcyclic (Quotient.mk _ G) = G.IsAcyclic := rfl

/-- Being a tree. -/
def IsTree (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsTree
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.isTree_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isTree_mk (G : CGraph) : IsTree (Quotient.mk _ G) = G.IsTree := rfl

/-- Strong regularity with given parameters. -/
def IsSRGWith (G : IsoGraph) (n k ℓ μ : ℕ) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) (fun H ↦ H.IsSRGWith n k ℓ μ)
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.isSRGWith_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isSRGWith_mk (G : CGraph) (n k ℓ μ : ℕ) :
    IsSRGWith (Quotient.mk _ G) n k ℓ μ = G.IsSRGWith n k ℓ μ := rfl

/-- Diameter. -/
noncomputable def diameter (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.diameter
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.diam_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem diameter_mk (G : CGraph) : diameter (Quotient.mk _ G) = G.diameter := rfl

/-- Bipartiteness. -/
def IsBipartite (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsBipartite
    (fun _ _ ⟨i⟩ ↦ propext ⟨CGraph.isBipartite_of_iso i, CGraph.isBipartite_of_iso i.symm⟩) G

@[simp] theorem isBipartite_mk (G : CGraph) :
    IsBipartite (Quotient.mk _ G) = G.IsBipartite := rfl

/-- Vertex-transitivity. -/
def IsVertexTransitive (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsVertexTransitive
    (fun _ _ ⟨i⟩ ↦ propext ⟨CGraph.isVertexTransitive_of_iso i,
      CGraph.isVertexTransitive_of_iso i.symm⟩) G

@[simp] theorem isVertexTransitive_mk (G : CGraph) :
    IsVertexTransitive (Quotient.mk _ G) = G.IsVertexTransitive := rfl

/-- Arc-transitivity. -/
def IsArcTransitive (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsArcTransitive
    (fun _ _ ⟨i⟩ ↦ propext ⟨CGraph.isArcTransitive_of_iso i,
      CGraph.isArcTransitive_of_iso i.symm⟩) G

@[simp] theorem isArcTransitive_mk (G : CGraph) :
    IsArcTransitive (Quotient.mk _ G) = G.IsArcTransitive := rfl

end IsoGraph
