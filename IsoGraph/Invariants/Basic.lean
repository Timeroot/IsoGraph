import IsoGraph.ToIsoGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import IsoGraph.ForMathlib.SimpleGraph

/-!
# Invariants

An *invariant* here is a quantity attached to a `CGraph` that is unchanged by isomorphism, and so
descends to `IsoGraph`.  Each one is written once, at the `CGraph` level, as a thin wrapper around
the corresponding Mathlib notion for `G.toSimple` — this is the form statements about concrete
graphs are proved in — and is followed by its invariance theorem, tagged `@[toIsoGraph]`.  That
attribute generates the `IsoGraph`-level copy, a `Quotient.lift` whose side condition is exactly
the invariance theorem, together with the `@[simp]` lemma saying the two agree on representatives.

The `SimpleGraph.Iso` section below supplies the invariance lemmas that Mathlib does not already
have.
-/

open Fintype

/-! ## Invariants of a `CGraph` -/

namespace CGraph

variable (G : CGraph)

/-- Independence number: the size of a largest set of pairwise non-adjacent vertices. -/
noncomputable def indepNum : ℕ := G.toSimple.indepNum

@[toIsoGraph]
theorem indepNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.indepNum = H.indepNum :=
  SimpleGraph.Iso.indepNum_eq (CGraph.Iso.toSimpleIso i)

/-- Clique number: the size of a largest set of pairwise adjacent vertices. -/
noncomputable def cliqueNum : ℕ := G.toSimple.cliqueNum

@[toIsoGraph]
theorem cliqueNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.cliqueNum = H.cliqueNum :=
  SimpleGraph.Iso.cliqueNum_eq (CGraph.Iso.toSimpleIso i)

/-- The number of `n`-cliques, i.e. of `n`-element sets of pairwise adjacent vertices. -/
noncomputable def cliqueCount (n : ℕ) : ℕ := (G.toSimple.cliqueSet n).ncard

@[toIsoGraph]
theorem cliqueCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) (n : ℕ) :
    G.cliqueCount n = H.cliqueCount n :=
  SimpleGraph.Iso.cliqueSet_ncard_eq (CGraph.Iso.toSimpleIso i) n

/-- With decidable equality on the vertices the clique count is the cardinality of Mathlib's
`cliqueFinset`; this is the bridge that makes it computable. -/
theorem cliqueCount_eq_card_cliqueFinset (n : ℕ) :
    G.cliqueCount n = (G.toSimple.cliqueFinset n).card := by
  rw [cliqueCount, ← SimpleGraph.coe_cliqueFinset, Set.ncard_coe_finset]

/-- The number of independent `n`-sets, i.e. of `n`-element sets of pairwise non-adjacent
vertices. -/
noncomputable def indepCount (n : ℕ) : ℕ := (G.toSimple.indepSetSet n).ncard

@[toIsoGraph]
theorem indepCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) (n : ℕ) :
    G.indepCount n = H.indepCount n :=
  SimpleGraph.Iso.indepSetSet_ncard_eq (CGraph.Iso.toSimpleIso i) n

/-- With decidable equality on the vertices the count is the cardinality of Mathlib's
`indepSetFinset`. -/
theorem indepCount_eq_card_indepSetFinset (n : ℕ) :
    G.indepCount n = (G.toSimple.indepSetFinset n).card := by
  rw [indepCount, ← Set.ncard_coe_finset]
  congr 1
  ext s
  simp [SimpleGraph.indepSetSet]

/-- The number of connected components. -/
noncomputable def numComponents : ℕ := Nat.card G.toSimple.ConnectedComponent

@[toIsoGraph]
theorem numComponents_eq_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.numComponents = H.numComponents :=
  SimpleGraph.Iso.numComponents_eq (CGraph.Iso.toSimpleIso i)

/-- With decidable equality on the vertices the components form a `Fintype`. -/
theorem numComponents_eq_card :
    G.numComponents = Fintype.card G.toSimple.ConnectedComponent :=
  Nat.card_eq_fintype_card

/-- The number of automorphisms, i.e. the order of the automorphism group. -/
noncomputable def autCount : ℕ := Nat.card (G.toSimple ≃g G.toSimple)

instance instFiniteAut : Finite (G.toSimple ≃g G.toSimple) :=
  Finite.of_injective (fun a : G.toSimple ≃g G.toSimple ↦ a.toEquiv)
    (fun _ _ h ↦ by ext v; exact congrArg (fun e : G.V ≃ G.V ↦ e v) h)

@[toIsoGraph]
theorem autCount_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.autCount = H.autCount :=
  SimpleGraph.Iso.autCount_eq (CGraph.Iso.toSimpleIso i)

/-- Number of edges. -/
def E : ℕ := G.toSimple.edgeFinset.card

@[toIsoGraph]
theorem E_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.E = H.E :=
  SimpleGraph.Iso.card_edgeFinset_eq (CGraph.Iso.toSimpleIso i)

/-- The degree of a vertex.  A wrapper around Mathlib's, so that the count below has somewhere to
attach; `deg_eq_degree` erases it, and no statement need ever mention it. -/
def deg (v : G.V) : ℕ := G.toSimple.degree v

@[simp] theorem deg_eq_degree (v : G.V) : G.deg v = G.toSimple.degree v := rfl

/-! ### Counting by a list scan

`E` and `deg` are cardinalities of a `Finset` — the right *statement*, since every Mathlib lemma
about `edgeFinset` and `degree` then applies to them, but on the graphs the algorithms run on it
is a `Finset (Sym2 G.V)` built to settle a question one pass over the enumeration answers.  `E`
guards every call of the containment search and `deg` is read at every node of it, so both are
redirected by `@[csimp]` to that pass.  The specifications above are untouched. -/

/-- **The degree, counted along the enumeration.** -/
theorem degree_eq_countP (v : G.V) :
    G.toSimple.degree v = (FinEnum.toList G.V).countP (G.Adj v) := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_def,
    Finset.filter_val]
  show (Multiset.filter _ (Finset.univ : Finset G.V).val).card = _
  rw [show (Finset.univ : Finset G.V).val = ↑(FinEnum.toList G.V) from rfl,
    ← Multiset.countP_eq_card_filter]
  simp

/-- What `deg` runs. -/
def degFast (v : G.V) : ℕ := (FinEnum.toList G.V).countP (G.Adj v)

@[csimp] theorem deg_eq_degFast : @deg = @degFast :=
  funext fun G ↦ funext fun v ↦ G.degree_eq_countP v

/-- What `E` runs: the adjacent ordered pairs, halved.  One scan of the adjacency function, where
`edgeFinset.card` builds the edge set of a `Sym2`. -/
def EFast : ℕ :=
  let vs := FinEnum.toList G.V
  (vs.map fun v ↦ vs.countP (G.Adj v)).sum / 2

@[csimp] theorem E_eq_EFast : @E = @EFast := by
  funext G
  have h : ∑ v : G.V, G.toSimple.degree v =
      ((FinEnum.toList G.V).map fun v ↦ (FinEnum.toList G.V).countP (G.Adj v)).sum := by
    rw [Finset.sum_eq_multiset_sum,
      show (Finset.univ : Finset G.V).val = ↑(FinEnum.toList G.V) from rfl]
    simp [degree_eq_countP]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at h
  show G.toSimple.edgeFinset.card = _ / 2
  omega

/-- The multiset of vertex degrees.  This is the degree sequence before sorting; the identities
of `IsoGraph/SmallGraphs.lean` are much easier to state and prove for the multiset, and
nothing is lost, since `degSequence` is exactly its `sort` (`coe_degSequence`). -/
def degMultiset : Multiset ℕ := Finset.univ.val.map fun v ↦ G.toSimple.degree v

@[toIsoGraph]
theorem degMultiset_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.degMultiset = H.degMultiset :=
  SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i)

/-- Sorted degree sequence. -/
def degSequence : List ℕ := G.degMultiset.sort (· ≤ ·)

@[toIsoGraph]
theorem degSequence_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.degSequence = H.degSequence :=
  congrArg (fun m : Multiset ℕ ↦ m.sort (· ≤ ·)) (degMultiset_eq_of_iso i)

@[toIsoGraph]
theorem degSequence_eq_sort : G.degSequence = G.degMultiset.sort (· ≤ ·) := rfl

@[simp, toIsoGraph] theorem coe_degSequence : (G.degSequence : Multiset ℕ) = G.degMultiset :=
  Multiset.sort_eq _ _

/-- Maximum degree, `0` on the empty graph. -/
def maxDeg (G : CGraph) : ℕ := G.toSimple.maxDegree

@[toIsoGraph]
theorem maxDeg_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.maxDeg = H.maxDeg :=
  SimpleGraph.Iso.maxDegree_eq (CGraph.Iso.toSimpleIso i)

/-- Minimum degree, `0` on the empty graph. -/
def minDeg (G : CGraph) : ℕ := G.toSimple.minDegree

@[toIsoGraph]
theorem minDeg_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.minDeg = H.minDeg :=
  SimpleGraph.Iso.minDegree_eq (CGraph.Iso.toSimpleIso i)

/-- The graph is connected (in particular, nonempty). -/
def IsConnected : Prop := G.toSimple.Connected

@[toIsoGraph]
theorem isConnected_iff_of_iso {G H : CGraph} (i : G ≃cg H) : G.IsConnected ↔ H.IsConnected :=
  SimpleGraph.Iso.connected_iff (CGraph.Iso.toSimpleIso i)

/-- **A function that is constant along the edges of a connected graph is constant.**  Walk
induction, once, so that the constructions that need it do not each redo it. -/
theorem eq_of_forall_adj {G : CGraph} (hG : G.IsConnected) {α : Type} {φ : G.V → α}
    (h : ∀ x y, G.Adj x y → φ x = φ y) (x y : G.V) : φ x = φ y := by
  obtain ⟨w⟩ := hG.preconnected x y
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- The graph has no cycles. -/
def IsAcyclic : Prop := G.toSimple.IsAcyclic

@[toIsoGraph]
theorem isAcyclic_iff_of_iso {G H : CGraph} (i : G ≃cg H) : G.IsAcyclic ↔ H.IsAcyclic :=
  SimpleGraph.Iso.isAcyclic_iff (CGraph.Iso.toSimpleIso i)

/-- Girth: the length of a shortest cycle, and `0` for an acyclic graph (Mathlib's convention,
the same kind of junk value as `diameter` uses for a disconnected graph). -/
noncomputable def girth : ℕ := G.toSimple.girth

@[toIsoGraph]
theorem girth_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.girth = H.girth :=
  SimpleGraph.Iso.girth_eq (CGraph.Iso.toSimpleIso i)

/-- Diameter, i.e. the largest distance between two vertices — `0` if the graph is disconnected
(this is Mathlib's convention for `SimpleGraph.diam`). -/
noncomputable def diameter : ℕ := G.toSimple.diam

@[toIsoGraph]
theorem diameter_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.diameter = H.diameter :=
  SimpleGraph.Iso.diam_eq (CGraph.Iso.toSimpleIso i)

/-- Radius: the least eccentricity of a vertex, i.e. how far from the rest of the graph the most
central vertex is.  `0` for an empty or disconnected graph, the same junk convention `diameter`
uses. -/
noncomputable def radius : ℕ := G.toSimple.radius.toNat

@[toIsoGraph]
theorem radius_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.radius = H.radius :=
  congrArg ENat.toNat (SimpleGraph.Iso.radius_eq (CGraph.Iso.toSimpleIso i))

/-- Vertex cover number: the size of a smallest set of vertices meeting every edge. -/
noncomputable def coverNum : ℕ := G.toSimple.vertexCoverNum.toNat

@[toIsoGraph]
theorem coverNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.coverNum = H.coverNum :=
  congrArg ENat.toNat (SimpleGraph.vertexCoverNum_congr (CGraph.Iso.toSimpleIso i))

/-- A set of vertices *dominates* the graph if every vertex either lies in it or has a
neighbour in it. -/
def IsDominatingSet (s : Finset G.V) : Prop := ∀ v : G.V, v ∈ s ∨ ∃ u ∈ s, G.Adj u v

/-- Dominating sets are recognised by a bounded check over the vertices, so `decide` can verify a
proposed one. -/
instance decidableIsDominatingSet (G : CGraph) : DecidablePred G.IsDominatingSet := fun s ↦
  decidable_of_iff (∀ v : G.V, v ∈ s ∨ ∃ u ∈ s, G.Adj u v) Iff.rfl

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

@[toIsoGraph]
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
  ENat.natCast_toNat G.chromaticNumber_ne_top

@[toIsoGraph]
theorem chromNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.chromNum = H.chromNum :=
  congrArg ENat.toNat (SimpleGraph.Iso.chromaticNumber_eq (CGraph.Iso.toSimpleIso i))

/-- The graph is a tree. -/
def IsTree : Prop := G.toSimple.IsTree

@[toIsoGraph]
theorem isTree_iff_of_iso {G H : CGraph} (i : G ≃cg H) : G.IsTree ↔ H.IsTree :=
  SimpleGraph.Iso.isTree_iff (CGraph.Iso.toSimpleIso i)

/-- The graph is *strongly regular* with parameters `(n, k, ℓ, μ)`: it has `n` vertices, every
vertex has degree `k`, adjacent vertices have `ℓ` common neighbours, and distinct non-adjacent
vertices have `μ`.  Unlike the invariants above this one takes the parameters as arguments; it is
a property, not a number, and `IsoGraph/SmallGraphs/Defs/SRG.lean` is a table of graphs
satisfying it. -/
def IsSRGWith (n k ℓ μ : ℕ) : Prop := G.toSimple.IsSRGWith n k ℓ μ

@[toIsoGraph]
theorem isSRGWith_iff_of_iso {G H : CGraph} (i : G ≃cg H) (n k ℓ μ : ℕ) :
    G.IsSRGWith n k ℓ μ ↔ H.IsSRGWith n k ℓ μ :=
  SimpleGraph.Iso.isSRGWith_iff (CGraph.Iso.toSimpleIso i)

/-- The graph is *`k`-regular*: every vertex has exactly `k` neighbours.  Like `IsSRGWith` this
takes its parameter as an argument, and it is the first condition of strong regularity. -/
def IsRegularWith (k : ℕ) : Prop := G.toSimple.IsRegularOfDegree k

@[toIsoGraph]
theorem isRegularWith_iff_of_iso {G H : CGraph} (i : G ≃cg H) (k : ℕ) :
    G.IsRegularWith k ↔ H.IsRegularWith k :=
  SimpleGraph.Iso.isRegularOfDegree_iff (CGraph.Iso.toSimpleIso i)

/-- The neighbours of `v`, as a `Finset`.  Same thing as `G.toSimple.neighborFinset v`
(`neighborFinset_eq_nbrs`), but phrased with `CGraph.Adj` so that it can be computed with and
rewritten by the `…_adj` simp lemmas of `IsoGraph/Core/Defs.lean`. -/
def nbrs (v : G.V) : Finset G.V := Finset.univ.filter fun w ↦ G.Adj v w = true

@[simp] theorem mem_nbrs (v w : G.V) : w ∈ G.nbrs v ↔ G.Adj v w = true := by simp [nbrs]

theorem neighborFinset_eq_nbrs (v : G.V) : G.toSimple.neighborFinset v = G.nbrs v := by
  ext w; simp

theorem card_commonNeighbors (v w : G.V) :
    Fintype.card (G.toSimple.commonNeighbors v w) = (G.nbrs v ∩ G.nbrs w).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext x
  simp [SimpleGraph.mem_commonNeighbors]

/-- **Strong regularity, spelled out in `Finset` terms.**  No `SimpleGraph`, no `Fintype.card` of
a subtype and no `Sym2`: just the neighbour sets of `nbrs` and their intersections, which is the
form in which the families of `IsoGraph/SmallGraphs/Defs/SRG.lean` are proved. -/
theorem isSRGWith_of {n k ℓ μ : ℕ} (hn : FinEnum.card G.V = n)
    (hk : ∀ v, (G.nbrs v).card = k)
    (hℓ : ∀ v w, G.Adj v w = true → (G.nbrs v ∩ G.nbrs w).card = ℓ)
    (hμ : ∀ v w, v ≠ w → G.Adj v w = false → (G.nbrs v ∩ G.nbrs w).card = μ) :
    G.IsSRGWith n k ℓ μ where
  card := G.fintypeCard.trans hn
  regular v := by rw [SimpleGraph.degree, neighborFinset_eq_nbrs, hk]
  of_adj v w h := by rw [card_commonNeighbors]; exact hℓ v w h
  of_not_adj v w hne h := by
    rw [card_commonNeighbors]
    exact hμ v w hne (by simpa using h)

/-! ### Bipartiteness -/

/-- The graph is *bipartite*: some two-colouring of the vertices leaves no edge monochromatic.
Stated with `Bool` rather than with a pair of vertex sets, which is what makes it directly usable
as the splitting criterion for the bipartite double cover in `IsoGraph/SmallGraphs.lean`. -/
def IsBipartite : Prop := ∃ c : G.V → Bool, ∀ x y, G.Adj x y → c x ≠ c y

/-- Bipartiteness transfers along an isomorphism. -/
@[toIsoGraph]
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
instance : Decidable G.IsBipartite :=
  decidable_of_iff (∃ c : G.V → Bool, ∀ x y, G.Adj x y → c x ≠ c y) Iff.rfl

/-! ### Transitivity

Two symmetry properties, stated directly in terms of `CGraph.Iso` automorphisms rather than in
terms of a group action.  They are what makes the clique sums of `IsoGraph/Core/CliqueSum.lean`
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

theorem isVertexTransitive_iff :
    G.IsVertexTransitive ↔
      ∀ u v : G.V, ∃ σ : Equiv.Perm G.V, (∀ x y, G.Adj (σ x) (σ y) = G.Adj x y) ∧ σ u = v := by
  constructor
  · intro h u v
    obtain ⟨σ, hσ⟩ := h u v
    exact ⟨σ.toEquiv, fun x y ↦ σ.adj_eq x y, hσ⟩
  · intro h u v
    obtain ⟨σ, hσ, huv⟩ := h u v
    exact ⟨autoOfPerm σ hσ, huv⟩

theorem isArcTransitive_iff :
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
@[toIsoGraph]
theorem isVertexTransitive_of_iso {G H : CGraph} (i : G ≃cg H) (h : G.IsVertexTransitive) :
    H.IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ⟩ := h (i.symm u) (i.symm v)
  exact ⟨(i.symm.trans σ).trans i, by simp [hσ]⟩

@[toIsoGraph]
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
vertex type supply it; see `IsoGraph/Core/Defs.lean`. -/

instance : Decidable G.IsConnected :=
  inferInstanceAs (Decidable G.toSimple.Connected)

instance : Decidable G.IsAcyclic :=
  decidable_of_iff (∀ (v w : G.V) (p q : G.toSimple.Path v w), p = q)
    ⟨fun h ↦ SimpleGraph.isAcyclic_iff_subsingleton_path.2 fun v w ↦ ⟨h v w⟩,
      fun h v w ↦ @Subsingleton.elim _ (h.subsingleton_path v w)⟩

instance : Decidable G.IsTree :=
  decidable_of_iff (G.IsConnected ∧ G.IsAcyclic)
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- Strong regularity is decidable: it is four bounded quantifications over the vertex type.  The
`DecidableEq` is needed only for the "distinct and non-adjacent" clause.

This runs in time `O(n³)`, so `native_decide` settles it for the graphs of
`IsoGraph/SmallGraphs/Defs/SRG.lean`; the kernel would not get far. -/
instance (n k ℓ μ : ℕ) : Decidable (G.IsSRGWith n k ℓ μ) :=
  decidable_of_iff
    (FinEnum.card G.V = n ∧ (∀ v, G.toSimple.degree v = k) ∧
      (∀ v w, G.toSimple.Adj v w → Fintype.card (G.toSimple.commonNeighbors v w) = ℓ) ∧
      (∀ v w, v ≠ w → ¬G.toSimple.Adj v w → Fintype.card (G.toSimple.commonNeighbors v w) = μ))
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨G.fintypeCard.trans h₁, h₂, h₃, fun _ _ hne ↦ h₄ _ _ hne⟩,
      fun h ↦ ⟨G.fintypeCard.symm.trans h.card, h.regular, h.of_adj,
        fun _ _ hne ↦ h.of_not_adj hne⟩⟩

/-- Regularity is the second conjunct of strong regularity, and decidable on its own: one
bounded quantification, and no `DecidableEq` needed. -/
instance (k : ℕ) : Decidable (G.IsRegularWith k) :=
  decidable_of_iff (∀ v, G.toSimple.degree v = k) Iff.rfl

/-- Vertex-transitivity is decidable by enumerating the `n!` permutations of the vertex type — so
this is for tiny graphs only, and the structural lemmas of `IsoGraph/Core/Defs.lean` are
the way to settle anything larger.  Even `native_decide` starts to labour at eight vertices. -/
instance : Decidable G.IsVertexTransitive :=
  decidable_of_iff _ (isVertexTransitive_iff G).symm

/-- Arc-transitivity is decidable, with the same `n!` caveat as `IsVertexTransitive`. -/
instance : Decidable G.IsArcTransitive :=
  decidable_of_iff _ (isArcTransitive_iff G).symm

end CGraph
