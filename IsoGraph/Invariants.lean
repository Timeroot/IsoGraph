import IsoGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.VertexCover

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

/-- The `n`-cliques of two isomorphic graphs are in bijection, so there are equally many. -/
theorem cliqueSet_ncard_eq (f : G ≃g G') (n : ℕ) :
    (G.cliqueSet n).ncard = (G'.cliqueSet n).ncard := by
  have himg : G'.cliqueSet n
      = (fun s : Finset V ↦ s.map ⟨f, f.injective⟩) '' G.cliqueSet n := by
    ext t
    simp only [Set.mem_image, mem_cliqueSet_iff]
    constructor
    · intro ht
      refine ⟨t.map ⟨f.symm, f.symm.injective⟩, isNClique_map f.symm ht, ?_⟩
      rw [Finset.map_map]
      ext x
      simp
    · rintro ⟨s, hs, rfl⟩
      exact isNClique_map f hs
  rw [himg, Set.ncard_image_of_injective _ (Finset.map_injective _)]

/-- The independent `n`-sets of two isomorphic graphs are in bijection, so there are equally
many. -/
theorem indepSetSet_ncard_eq (f : G ≃g G') (n : ℕ) :
    (G.indepSetSet n).ncard = (G'.indepSetSet n).ncard := by
  have himg : G'.indepSetSet n
      = (fun s : Finset V ↦ s.map ⟨f, f.injective⟩) '' G.indepSetSet n := by
    ext t
    simp only [Set.mem_image, mem_indepSetSet_iff]
    constructor
    · intro ht
      refine ⟨t.map ⟨f.symm, f.symm.injective⟩, isNIndepSet_map f.symm ht, ?_⟩
      rw [Finset.map_map]
      ext x
      simp
    · rintro ⟨s, hs, rfl⟩
      exact isNIndepSet_map f hs
  rw [himg, Set.ncard_image_of_injective _ (Finset.map_injective _)]

/-- Isomorphic graphs have equally many connected components. -/
theorem numComponents_eq (f : G ≃g G') :
    Nat.card G.ConnectedComponent = Nat.card G'.ConnectedComponent :=
  Nat.card_congr f.connectedComponentEquiv

/-- Conjugating by an isomorphism is a bijection between the automorphism groups. -/
def autEquiv (f : G ≃g G') : (G ≃g G) ≃ (G' ≃g G') where
  toFun a := (f.symm.trans a).trans f
  invFun b := (f.trans b).trans f.symm
  left_inv a := by ext v; simp
  right_inv b := by ext v; simp

/-- Isomorphic graphs have equally many automorphisms. -/
theorem autCount_eq (f : G ≃g G') : Nat.card (G ≃g G) = Nat.card (G' ≃g G') :=
  Nat.card_congr (autEquiv f)

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

/-- Isomorphisms preserve eccentricity. -/
theorem eccent_eq (f : G ≃g G') (u : V) : G.eccent u = G'.eccent (f u) := by
  unfold SimpleGraph.eccent
  refine le_antisymm (iSup_le fun v ↦ ?_) (iSup_le fun w ↦ ?_)
  · rw [edist_eq f]
    exact le_iSup (G'.edist (f u)) (f v)
  · have hw : G'.edist (f u) w = G.edist u (f.symm w) := by
      rw [edist_eq f u (f.symm w), f.apply_symm_apply]
    rw [hw]
    exact le_iSup (G.edist u) (f.symm w)

/-- Isomorphic graphs have the same radius. -/
theorem radius_eq (f : G ≃g G') : G.radius = G'.radius := by
  unfold SimpleGraph.radius
  refine le_antisymm (le_iInf fun w ↦ ?_) (le_iInf fun u ↦ ?_)
  · have hw : G'.eccent w = G.eccent (f.symm w) := by
      rw [eccent_eq f, f.apply_symm_apply]
    rw [hw]
    exact iInf_le _ (f.symm w)
  · rw [eccent_eq f]
    exact iInf_le _ (f u)

/-- An isomorphism restricts to a bijection between common neighbourhoods. -/
def commonNeighborsEquiv (f : G ≃g G') (v w : V) :
    G.commonNeighbors v w ≃ G'.commonNeighbors (f v) (f w) :=
  Equiv.subtypeEquiv f.toEquiv fun x ↦ by
    simp [SimpleGraph.mem_commonNeighbors, f.map_adj_iff]

theorem card_commonNeighbors_eq [Fintype V] [Fintype W] [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (f : G ≃g G') (v w : V) :
    Fintype.card (G.commonNeighbors v w) = Fintype.card (G'.commonNeighbors (f v) (f w)) :=
  Fintype.card_congr (commonNeighborsEquiv f v w)

/-- Isomorphic graphs have the same chromatic number. -/
theorem chromaticNumber_eq (f : G ≃g G') : G.chromaticNumber = G'.chromaticNumber :=
  le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

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

/-- **Girth is an isomorphism invariant**: an isomorphism carries cycles to cycles of the same
length, in both directions, so the infimum of cycle lengths is the same on both sides. -/
theorem egirth_eq (f : G ≃g G') : G.egirth = G'.egirth := by
  refine le_antisymm (le_egirth.2 fun a w hw ↦ ?_) (le_egirth.2 fun a w hw ↦ ?_)
  · have h := egirth_le_length (hw.map (f := f.symm.toHom) f.symm.injective)
    rwa [Walk.length_map] at h
  · have h := egirth_le_length (hw.map (f := f.toHom) f.injective)
    rwa [Walk.length_map] at h

theorem girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  rw [girth, girth, f.egirth_eq]

end SimpleGraph.Iso

/-! ## Invariants of a `CGraph` -/

namespace CGraph

variable (G : CGraph)

/-- Independence number: the size of a largest set of pairwise non-adjacent vertices. -/
noncomputable def indepNum : ℕ := G.toSimple.indepNum

/-- Clique number: the size of a largest set of pairwise adjacent vertices. -/
noncomputable def cliqueNum : ℕ := G.toSimple.cliqueNum

/-- The number of `n`-cliques, i.e. of `n`-element sets of pairwise adjacent vertices. -/
noncomputable def cliqueCount (n : ℕ) : ℕ := (G.toSimple.cliqueSet n).ncard

theorem cliqueCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) (n : ℕ) :
    G.cliqueCount n = H.cliqueCount n :=
  SimpleGraph.Iso.cliqueSet_ncard_eq (CGraph.Iso.toSimpleIso i) n

/-- With decidable equality on the vertices the clique count is the cardinality of Mathlib's
`cliqueFinset`; this is the bridge that makes it computable. -/
theorem cliqueCount_eq_card_cliqueFinset [DecidableEq G.V] (n : ℕ) :
    G.cliqueCount n = (G.toSimple.cliqueFinset n).card := by
  rw [cliqueCount, ← SimpleGraph.coe_cliqueFinset, Set.ncard_coe_finset]

/-- The number of independent `n`-sets, i.e. of `n`-element sets of pairwise non-adjacent
vertices. -/
noncomputable def indepCount (n : ℕ) : ℕ := (G.toSimple.indepSetSet n).ncard

theorem indepCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) (n : ℕ) :
    G.indepCount n = H.indepCount n :=
  SimpleGraph.Iso.indepSetSet_ncard_eq (CGraph.Iso.toSimpleIso i) n

/-- With decidable equality on the vertices the count is the cardinality of Mathlib's
`indepSetFinset`. -/
theorem indepCount_eq_card_indepSetFinset [DecidableEq G.V] (n : ℕ) :
    G.indepCount n = (G.toSimple.indepSetFinset n).card := by
  rw [indepCount, ← Set.ncard_coe_finset]
  congr 1
  ext s
  simp [SimpleGraph.indepSetSet]

/-- The number of connected components. -/
noncomputable def numComponents : ℕ := Nat.card G.toSimple.ConnectedComponent

theorem numComponents_eq_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.numComponents = H.numComponents :=
  SimpleGraph.Iso.numComponents_eq (CGraph.Iso.toSimpleIso i)

/-- With decidable equality on the vertices the components form a `Fintype`. -/
theorem numComponents_eq_card [DecidableEq G.V] :
    G.numComponents = Fintype.card G.toSimple.ConnectedComponent :=
  Nat.card_eq_fintype_card

/-- The number of automorphisms, i.e. the order of the automorphism group. -/
noncomputable def autCount : ℕ := Nat.card (G.toSimple ≃g G.toSimple)

instance instFiniteAut : Finite (G.toSimple ≃g G.toSimple) :=
  Finite.of_injective (fun a : G.toSimple ≃g G.toSimple ↦ a.toEquiv)
    (fun _ _ h ↦ by ext v; exact congrArg (fun e : G.V ≃ G.V ↦ e v) h)

theorem autCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.autCount = H.autCount :=
  SimpleGraph.Iso.autCount_eq (CGraph.Iso.toSimpleIso i)

/-- Number of edges. -/
def E : ℕ := G.toSimple.edgeFinset.card

/-- The multiset of vertex degrees.  This is the degree sequence before sorting; the identities
of `IsoGraph/Identities.lean` are much easier to state and prove for the multiset, and nothing is
lost, since `degSequence` is exactly its `sort` (`coe_degSequence`). -/
def degMultiset : Multiset ℕ := Finset.univ.val.map fun v ↦ G.toSimple.degree v

/-- Sorted degree sequence. -/
def degSequence : List ℕ := G.degMultiset.sort (· ≤ ·)

theorem degSequence_eq_sort : G.degSequence = G.degMultiset.sort (· ≤ ·) := rfl

@[simp] theorem coe_degSequence : (G.degSequence : Multiset ℕ) = G.degMultiset :=
  Multiset.sort_eq _ _

/-- Maximum degree, `0` on the empty graph. -/
def maxDeg (G : CGraph) : ℕ := G.toSimple.maxDegree

/-- Minimum degree, `0` on the empty graph. -/
def minDeg (G : CGraph) : ℕ := G.toSimple.minDegree

/-- The graph is connected (in particular, nonempty). -/
def IsConnected : Prop := G.toSimple.Connected

/-- The graph has no cycles. -/
def IsAcyclic : Prop := G.toSimple.IsAcyclic

/-- Girth: the length of a shortest cycle, and `0` for an acyclic graph (Mathlib's convention,
the same kind of junk value as `diameter` uses for a disconnected graph). -/
noncomputable def girth : ℕ := G.toSimple.girth

/-- Diameter, i.e. the largest distance between two vertices — `0` if the graph is disconnected
(this is Mathlib's convention for `SimpleGraph.diam`). -/
noncomputable def diameter : ℕ := G.toSimple.diam

/-- Radius: the least eccentricity of a vertex, i.e. how far from the rest of the graph the most
central vertex is.  `0` for an empty or disconnected graph, the same junk convention `diameter`
uses. -/
noncomputable def radius : ℕ := G.toSimple.radius.toNat

/-- Vertex cover number: the size of a smallest set of vertices meeting every edge. -/
noncomputable def coverNum : ℕ := G.toSimple.vertexCoverNum.toNat

/-- A set of vertices *dominates* the graph if every vertex either lies in it or has a
neighbour in it. -/
def IsDominatingSet (s : Finset G.V) : Prop := ∀ v : G.V, v ∈ s ∨ ∃ u ∈ s, G.Adj u v

/-- Domination number: the size of a smallest dominating set.  The whole vertex set dominates,
so the infimum is over a nonempty set of naturals. -/
noncomputable def domNum : ℕ := sInf {n | ∃ s : Finset G.V, s.card = n ∧ G.IsDominatingSet s}

theorem isDominatingSet_univ : G.IsDominatingSet Finset.univ := fun v ↦ Or.inl (Finset.mem_univ v)

/-- A dominating set is carried to a dominating set by an isomorphism. -/
theorem IsDominatingSet.map {G H : CGraph} (i : G ≃cg H) {s : Finset G.V}
    (h : G.IsDominatingSet s) : H.IsDominatingSet (s.map i.toEquiv.toEmbedding) := by
  intro v
  rcases h (i.symm v) with hv | ⟨u, hu, hadj⟩
  · exact Or.inl (Finset.mem_map.2 ⟨i.symm v, hv, by simp⟩)
  · refine Or.inr ⟨i u, Finset.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    have h2 := i.adj_eq u (i.symm v)
    rw [i.apply_symm_apply] at h2
    rw [h2]
    exact hadj

theorem domNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.domNum = H.domNum := by
  have hset : {n | ∃ s : Finset G.V, s.card = n ∧ G.IsDominatingSet s}
      = {n | ∃ s : Finset H.V, s.card = n ∧ H.IsDominatingSet s} := by
    ext n
    constructor
    · rintro ⟨s, rfl, hs⟩
      exact ⟨s.map i.toEquiv.toEmbedding, Finset.card_map _, hs.map i⟩
    · rintro ⟨s, rfl, hs⟩
      exact ⟨s.map i.symm.toEquiv.toEmbedding, Finset.card_map _, hs.map i.symm⟩
  unfold domNum
  rw [hset]

/-- Chromatic number. -/
noncomputable def chromNum : ℕ := G.toSimple.chromaticNumber.toNat

theorem chromaticNumber_ne_top : G.toSimple.chromaticNumber ≠ ⊤ :=
  SimpleGraph.chromaticNumber_ne_top_iff_exists.2 ⟨_, G.toSimple.colorable_of_fintype⟩

@[simp] theorem coe_chromNum : (G.chromNum : ℕ∞) = G.toSimple.chromaticNumber :=
  ENat.coe_toNat G.chromaticNumber_ne_top

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

/-- The number of `n`-cliques. -/
noncomputable def cliqueCount (G : IsoGraph) (n : ℕ) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ CGraph.cliqueCount g n)
    (fun _ _ ⟨i⟩ ↦ CGraph.cliqueCount_eq_of_iso i n) G

@[simp] theorem cliqueCount_mk (G : CGraph) (n : ℕ) :
    cliqueCount (Quotient.mk _ G) n = G.cliqueCount n := rfl

/-- The number of independent `n`-sets. -/
noncomputable def indepCount (G : IsoGraph) (n : ℕ) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ CGraph.indepCount g n)
    (fun _ _ ⟨i⟩ ↦ CGraph.indepCount_eq_of_iso i n) G

@[simp] theorem indepCount_mk (G : CGraph) (n : ℕ) :
    indepCount (Quotient.mk _ G) n = G.indepCount n := rfl

/-- The number of connected components. -/
noncomputable def numComponents (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.numComponents
    (fun _ _ ⟨i⟩ ↦ CGraph.numComponents_eq_of_iso i) G

@[simp] theorem numComponents_mk (G : CGraph) :
    numComponents (Quotient.mk _ G) = G.numComponents := rfl

/-- Number of edges. -/
def E (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.E
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.card_edgeFinset_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem E_mk (G : CGraph) : E (Quotient.mk _ G) = G.E := rfl

/-- The multiset of vertex degrees. -/
def degMultiset (G : IsoGraph) : Multiset ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.degMultiset
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem degMultiset_mk (G : CGraph) :
    degMultiset (Quotient.mk _ G) = G.degMultiset := rfl

/-- Sorted degree sequence. -/
def degSequence (G : IsoGraph) : List ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.degSequence
    (fun _ _ ⟨i⟩ ↦ congrArg (fun m : Multiset ℕ ↦ m.sort (· ≤ ·))
      (SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem degSequence_mk (G : CGraph) :
    degSequence (Quotient.mk _ G) = G.degSequence := rfl

theorem degSequence_eq_sort (G : IsoGraph) : degSequence G = (degMultiset G).sort (· ≤ ·) := by
  induction G using Quotient.inductionOn with | _ g => rfl

@[simp] theorem coe_degSequence (G : IsoGraph) : (degSequence G : Multiset ℕ) = degMultiset G := by
  induction G using Quotient.inductionOn with | _ g => exact Multiset.sort_eq _ _

/-- Maximum degree. -/
def maxDeg (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.maxDeg
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.maxDegree_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem maxDeg_mk (G : CGraph) : maxDeg (Quotient.mk _ G) = G.maxDeg := rfl

/-- Minimum degree. -/
def minDeg (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.minDeg
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.minDegree_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem minDeg_mk (G : CGraph) : minDeg (Quotient.mk _ G) = G.minDeg := rfl

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

/-- Girth. -/
noncomputable def girth (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.girth
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.girth_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem girth_mk (G : CGraph) : girth (Quotient.mk _ G) = G.girth := rfl

/-- Diameter. -/
noncomputable def diameter (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.diameter
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.diam_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem diameter_mk (G : CGraph) : diameter (Quotient.mk _ G) = G.diameter := rfl

/-- Radius. -/
noncomputable def radius (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.radius
    (fun _ _ ⟨i⟩ ↦ congrArg ENat.toNat
      (SimpleGraph.Iso.radius_eq (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem radius_mk (G : CGraph) : radius (Quotient.mk _ G) = G.radius := rfl

/-- Vertex cover number. -/
noncomputable def coverNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.coverNum
    (fun _ _ ⟨i⟩ ↦ congrArg ENat.toNat
      (SimpleGraph.vertexCoverNum_congr (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem coverNum_mk (G : CGraph) : coverNum (Quotient.mk _ G) = G.coverNum := rfl

/-- Domination number. -/
noncomputable def domNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.domNum
    (fun _ _ ⟨i⟩ ↦ CGraph.domNum_eq_of_iso i) G

@[simp] theorem domNum_mk (G : CGraph) : domNum (Quotient.mk _ G) = G.domNum := rfl

/-- Chromatic number. -/
noncomputable def chromNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.chromNum
    (fun _ _ ⟨i⟩ ↦ congrArg ENat.toNat
      (SimpleGraph.Iso.chromaticNumber_eq (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem chromNum_mk (G : CGraph) : chromNum (Quotient.mk _ G) = G.chromNum := rfl

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

/-- The number of automorphisms. -/
noncomputable def autCount (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.autCount
    (fun _ _ ⟨i⟩ ↦ CGraph.autCount_eq_of_iso i) G

@[simp] theorem autCount_mk (G : CGraph) : autCount (Quotient.mk _ G) = G.autCount := rfl

end IsoGraph
