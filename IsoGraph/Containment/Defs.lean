import IsoGraph.Graphs.Quotient
import IsoGraph.Invariants.Basic

/-!
# Containment relations

The orderings a graph theorist puts on graphs — subgraph, induced subgraph, minor, immersion, and
the rest — are all of the same kind: `H` sits inside `G` when there is a *map* of one into the
other with some property.  Each one is written here twice.

* At the level of `CGraph` it is **data**: a structure carrying the map and its properties, so
  that `H.SubgraphOf G` is the type of embeddings of `H` into `G` as a subgraph, not the statement
  that one exists.  The structures extend one another where the relations do — an
  `InducedSubgraphOf` *is* a `SubgraphOf` with an extra field — so that the weakenings are the
  inherited projections, and every one of them has `ofIso`, `refl` and (where it is proved) `trans`.
* At the level of `IsoGraph` it is a **`Prop`**: `Nonempty` of the corresponding structure,
  descended to the quotient.  `ofIso` and `trans` together are exactly what that descent needs —
  transporting a containment along isomorphisms of both sides is composing with two isomorphisms.

Each relation that has `refl` and `trans` then becomes a scoped order instance on `IsoGraph`,
with `empty 0` as the bottom element where it is one.  The scopes are `IsoGraph.Subgraph`,
`IsoGraph.InducedSubgraph`, `IsoGraph.Hom` and `IsoGraph.Quotient` here, and `IsoGraph.Minor`,
`IsoGraph.InducedMinor`, `IsoGraph.Contraction`, `IsoGraph.TopMinor` and `IsoGraph.Immersion` in
`Containment/Minors.lean`; only one should be open at a time, since they all use `≤`.

## The relations

| structure | the data | order on `IsoGraph` |
| --- | --- | --- |
| `Hom` (Mathlib's, as `→cg`) | a map carrying edges to edges | `HasHomInto`, a preorder |
| `SubgraphOf` | an injective such map | `IsSubgraphOf`, a partial order |
| `InducedSubgraphOf` | injective, and reflecting edges | `IsInducedSubgraphOf`, a partial order |
| `QuotientOf` | a surjective such map, the other way | `HasQuotient`, a partial order |
| `MinorOf` | connected branch sets, one per vertex | `IsMinorOf`, a preorder |
| `InducedMinorOf` | branch sets that reflect edges too | `IsInducedMinorOf`, a preorder |
| `ContractionOf` | induced, and no vertex deleted | `IsContractionOf`, a preorder |
| `TopMinorOf` | branch vertices and internally disjoint paths | `IsTopMinorOf` |
| `ImmersionOf` | branch vertices and edge-disjoint trails | `IsImmersionMinorOf` |

The hom order is only a preorder, and not by omission: `K₂` and `K₂ ⊕g K₁` map into each other and
are not isomorphic.  The subgraph, induced subgraph and quotient orders are partial orders, because
the two maps of an antisymmetry are forced to be bijections and then to reflect adjacency;
`isoOfInjective` is the lemma that does it, by counting edges.  The other five relations are
antisymmetric as well, by arguments that live in `Containment/Minors.lean`.

`TopMinorOf` and `ImmersionOf` are the two whose transitivity is not proved *here*.  Both hold —
the proof substitutes a path or trail of `G` for each edge of the paths in `K` — but the
substitution is a development of its own, and `Containment/Minors.lean` carries it out.  What is
proved for both here is `ofIso`, `refl`, the weakening of a `SubgraphOf` and (for immersions) of a
`TopMinorOf`, and the descent to `IsoGraph` as a reflexive relation.

## Branch sets

A minor is presented as a partial map `branch : G.V → Option H.V` — the vertex of `H` that a
vertex of `G` is contracted into, if it is not deleted — rather than as a family of sets, since
disjointness is then automatic and composition is `Option.bind`.  Connectedness of a branch set is
`ConnectedOn`, which asks for a walk *in `G`* staying inside the set rather than for connectedness
of an induced subgraph: the walks of the induced graph would have to be transported back and forth
at every step of the composition, and this way they do not.
-/

set_option autoImplicit false

namespace CGraph

/-! ## Two conveniences about isomorphisms -/

/-- An isomorphism, as a homomorphism of the underlying `SimpleGraph`s — the form `Walk.map`
asks for. -/
def Iso.toSimpleHom {G G' : CGraph} (j : G ≃cg G') : G.toSimple →g G'.toSimple :=
  j.toRelEmbedding.toRelHom

@[simp] theorem Iso.coe_toSimpleHom {G G' : CGraph} (j : G ≃cg G') : ⇑j.toSimpleHom = ⇑j := rfl

/-- Adjacency pulled back along an isomorphism.  Note that `i.symm` has type `RelIso`, not
`CGraph.Iso`, so `adj_eq` has to be named in full. -/
theorem Iso.symm_adj {H H' : CGraph} (i : H ≃cg H') {x y : H'.V} (h : H'.Adj x y) :
    H.Adj (i.symm x) (i.symm y) :=
  (Iso.adj_eq i.symm x y).trans h

/-! ## Connected sets of vertices -/

/-- `G.ConnectedOn s`: `s` is nonempty, and any two of its vertices are joined by a walk of `G`
that never leaves `s`.  This is the connectedness of the subgraph induced on `s`, stated with
walks of `G` itself. -/
structure ConnectedOn (G : CGraph) (s : Set G.V) : Prop where
  /-- A connected set is nonempty. -/
  nonempty : s.Nonempty
  /-- Any two vertices of the set are joined by a walk inside it. -/
  walk : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∃ w : G.toSimple.Walk u v, ∀ z ∈ w.support, z ∈ s

theorem connectedOn_singleton (G : CGraph) (x : G.V) : G.ConnectedOn {x} where
  nonempty := ⟨x, rfl⟩
  walk := by
    rintro u rfl v rfl
    exact ⟨.nil, by simp⟩

/-- **Adding a vertex adjacent to a connected set keeps it connected.**  This is how a search
grows a branch set: one vertex at a time, each attached to what is already there. -/
theorem ConnectedOn.insert {G : CGraph} {s : Set G.V} {v u : G.V} (hs : G.ConnectedOn s)
    (hu : u ∈ s) (hadj : G.Adj v u) : G.ConnectedOn (Insert.insert v s) where
  nonempty := ⟨v, Set.mem_insert _ _⟩
  walk := by
    have key : ∀ b ∈ s, ∃ w : G.toSimple.Walk v b, ∀ z ∈ w.support, z ∈ Insert.insert v s := by
      intro b hb
      obtain ⟨p, hp⟩ := hs.walk hu hb
      refine ⟨.cons (show G.toSimple.Adj v u from hadj) p, ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (hp z hz)
    rintro a ha b hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact ⟨.nil, fun z hz ↦ by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ Set.mem_insert _ _⟩
      · exact key b hb
    · rcases hb with rfl | hb
      · obtain ⟨w, hw⟩ := key a ha
        exact ⟨w.reverse, by simpa using hw⟩
      · obtain ⟨w, hw⟩ := hs.walk ha hb
        exact ⟨w, fun z hz ↦ Set.mem_insert_of_mem _ (hw z hz)⟩

/-- **Any nonempty proper subset of a connected set has an edge leaving it.**  Dually to
`ConnectedOn.insert`, this is why growing a branch set one adjacent vertex at a time can reach
all of it. -/
theorem ConnectedOn.exists_adj_of_ssubset {G : CGraph} {s t : Set G.V} (hs : G.ConnectedOn s)
    (hts : t ⊆ s) {u : G.V} (hu : u ∈ t) {w : G.V} (hw : w ∈ s) (hwt : w ∉ t) :
    ∃ a ∈ t, ∃ b ∈ s, b ∉ t ∧ G.Adj a b := by
  obtain ⟨p, hp⟩ := hs.walk (hts hu) hw
  clear hw
  induction p with
  | @nil a => exact absurd hu hwt
  | @cons a m c hadj p ih =>
    by_cases hm : m ∈ t
    · exact ih hm hwt fun z hz ↦ hp z (by simp [hz])
    · exact ⟨a, hu, m, hp m (by simp [SimpleGraph.Walk.start_mem_support]), hm, hadj⟩

/-- **A union of connected sets indexed by a connected set is connected**, provided every edge of
the index graph is realised by an edge between the corresponding sets.  This is the one lemma the
transitivity of the minor relation needs: the branch sets of a minor of a minor are unions of
branch sets, indexed by the branch sets one level up. -/
theorem connectedOn_biUnion {G K : CGraph} {t : Set K.V} {F : K.V → Set G.V}
    (ht : K.ConnectedOn t) (hF : ∀ k ∈ t, G.ConnectedOn (F k))
    (hedge : ∀ k ∈ t, ∀ k' ∈ t, K.Adj k k' → ∃ u ∈ F k, ∃ v ∈ F k', G.Adj u v) :
    G.ConnectedOn (⋃ k ∈ t, F k) := by
  have key : ∀ {k k' : K.V} (w : K.toSimple.Walk k k'), (∀ z ∈ w.support, z ∈ t) →
      ∀ u ∈ F k, ∀ v ∈ F k', ∃ p : G.toSimple.Walk u v, ∀ z ∈ p.support, z ∈ ⋃ k ∈ t, F k := by
    intro k k' w
    induction w with
    | @nil a =>
      intro hsup u hu v hv
      have ha : a ∈ t := hsup _ (by simp)
      obtain ⟨p, hp⟩ := (hF _ ha).walk hu hv
      exact ⟨p, fun z hz ↦ Set.mem_biUnion ha (hp z hz)⟩
    | @cons a b c hadj w ih =>
      intro hsup u hu v hv
      have ha : a ∈ t := hsup _ (by simp)
      have hb : b ∈ t := hsup _ (by simp [SimpleGraph.Walk.start_mem_support])
      obtain ⟨u', hu', v', hv', hedge'⟩ := hedge a ha b hb hadj
      obtain ⟨p₁, hp₁⟩ := (hF a ha).walk hu hu'
      obtain ⟨p₂, hp₂⟩ := ih (fun z hz ↦ hsup z (by simp [hz])) v' hv' v hv
      refine ⟨p₁.append (SimpleGraph.Walk.cons hedge' p₂), fun z hz ↦ ?_⟩
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact Set.mem_biUnion ha (hp₁ z hz)
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Set.mem_biUnion ha hu'
        · exact hp₂ z hz
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := ht.nonempty
    obtain ⟨u, hu⟩ := (hF k hk).nonempty
    exact ⟨u, Set.mem_biUnion hk hu⟩
  · rintro u hu v hv
    rw [Set.mem_iUnion₂] at hu hv
    obtain ⟨k, hk, hu⟩ := hu
    obtain ⟨k', hk', hv⟩ := hv
    obtain ⟨w, hw⟩ := ht.walk hk hk'
    exact key w hw u hu v hv

/-! ## An injective map that misses no edge

The antisymmetry of every order in this file comes down to one lemma: a map that is injective and
carries edges to edges, between graphs with no more vertices and no more edges the other way
round, is an isomorphism.  Both counts are forced to be equalities, the vertex map is a bijection,
and the induced map on edges is a bijection too, so every edge upstairs comes from an edge
downstairs. -/

/-- The edge map of an injective homomorphism is injective, so a subgraph has no more edges than
the graph it sits in. -/
theorem E_le_of_injective {H G : CGraph} (f : H.V → G.V) (hinj : Function.Injective f)
    (hadj : ∀ x y, H.Adj x y → G.Adj (f x) (f y)) : H.E ≤ G.E := by
  let φ : H.toSimple →g G.toSimple := ⟨f, fun {x y} h ↦ hadj x y h⟩
  have hφ : Function.Injective φ.mapEdgeSet := SimpleGraph.Hom.mapEdgeSet.injective φ hinj
  rw [E, E, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_le_of_injective _ hφ

/-- **An injective homomorphism onto a graph with no more vertices and no more edges is an
isomorphism.** -/
noncomputable def isoOfInjective {H G : CGraph} (f : H.V → G.V) (hinj : Function.Injective f)
    (hadj : ∀ x y, H.Adj x y → G.Adj (f x) (f y))
    (hcard : Fintype.card G.V ≤ Fintype.card H.V) (hE : G.E ≤ H.E) : H ≃cg G := by
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective f hinj) hcard⟩
  have hEeq : H.E = G.E := le_antisymm (E_le_of_injective f hinj hadj) hE
  let φ : H.toSimple →g G.toSimple := ⟨f, fun {x y} h ↦ hadj x y h⟩
  have hφ : Function.Injective φ.mapEdgeSet := SimpleGraph.Hom.mapEdgeSet.injective φ hinj
  have hcards : Fintype.card G.toSimple.edgeSet ≤ Fintype.card H.toSimple.edgeSet := by
    rw [← SimpleGraph.edgeFinset_card, ← SimpleGraph.edgeFinset_card, ← E, ← E, hEeq]
  have hsurj : Function.Surjective φ.mapEdgeSet :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨hφ, le_antisymm (Fintype.card_le_of_injective _ hφ) hcards⟩ |>.2
  refine isoOfAdj (Equiv.ofBijective f hbij) fun x y ↦ ?_
  show G.Adj (f x) (f y) = H.Adj x y
  refine Bool.eq_iff_iff.2 ⟨fun h ↦ ?_, fun h ↦ hadj x y h⟩
  obtain ⟨⟨e, he⟩, he'⟩ := hsurj ⟨s(f x, f y), h⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hmap : s(f a, f b) = s(f x, f y) := congrArg Subtype.val he'
    rw [Sym2.eq_iff] at hmap
    rcases hmap with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [hinj ha, hinj hb] at he; exact he
    · rw [hinj ha, hinj hb] at he; rw [H.symm]; exact he

/-! ## Subgraphs -/

/-- `H.SubgraphOf G`: `H` is a subgraph of `G`, as data — an injection of the vertices of `H` into
those of `G` that carries every edge of `H` to an edge of `G`. -/
structure SubgraphOf (H G : CGraph) where
  /-- The map on vertices. -/
  toFun : H.V → G.V
  /-- The map on vertices is injective. -/
  injective' : Function.Injective toFun
  /-- Edges go to edges. -/
  map_adj' : ∀ x y, H.Adj x y → G.Adj (toFun x) (toFun y)

/-- `H.InducedSubgraphOf G`: `H` is an *induced* subgraph of `G` — a `SubgraphOf` whose map
reflects adjacency as well as preserving it, so that `H` is what `G` induces on the image. -/
structure InducedSubgraphOf (H G : CGraph) extends SubgraphOf H G where
  /-- Non-edges go to non-edges. -/
  adj_map' : ∀ x y, G.Adj (toFun x) (toFun y) → H.Adj x y

/-- `H.QuotientOf G`: `H` is a homomorphic image of `G` — a surjection of the vertices of `G` onto
those of `H` carrying edges to edges.  The direction is chosen so that, as with the others, the
larger graph is the second argument. -/
structure QuotientOf (H G : CGraph) where
  /-- The map on vertices, from the larger graph down. -/
  toFun : G.V → H.V
  /-- The map on vertices is surjective. -/
  surjective' : Function.Surjective toFun
  /-- Edges go to edges. -/
  map_adj' : ∀ x y, G.Adj x y → H.Adj (toFun x) (toFun y)

namespace SubgraphOf

variable {H G K : CGraph}

instance : FunLike (H.SubgraphOf G) H.V G.V where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp] theorem coe_mk (f : H.V → G.V) (hinj hadj) :
    ⇑(⟨f, hinj, hadj⟩ : H.SubgraphOf G) = f := rfl

theorem injective (f : H.SubgraphOf G) : Function.Injective f := f.injective'

theorem map_adj (f : H.SubgraphOf G) {x y : H.V} (h : H.Adj x y) : G.Adj (f x) (f y) :=
  f.map_adj' x y h

/-- An isomorphism is in particular a subgraph inclusion. -/
def ofIso (i : H ≃cg G) : H.SubgraphOf G where
  toFun := i
  injective' := (RelIso.injective i)
  map_adj' x y h := by rw [i.adj_eq]; exact h

/-- Every graph is a subgraph of itself. -/
def refl (G : CGraph) : G.SubgraphOf G := ofIso (RelIso.refl _)

/-- A subgraph of a subgraph is a subgraph. -/
def trans (f : H.SubgraphOf G) (g : G.SubgraphOf K) : H.SubgraphOf K where
  toFun x := g (f x)
  injective' := g.injective.comp f.injective
  map_adj' _ _ h := g.map_adj (f.map_adj h)

/-- A subgraph inclusion is in particular a homomorphism. -/
def toHom (f : H.SubgraphOf G) : H →cg G := ⟨f, fun h ↦ f.map_adj h⟩

theorem E_le (f : H.SubgraphOf G) : H.E ≤ G.E :=
  E_le_of_injective f f.injective f.map_adj'

theorem card_le (f : H.SubgraphOf G) : Fintype.card H.V ≤ Fintype.card G.V :=
  Fintype.card_le_of_injective f f.injective

/-- **Two graphs that are subgraphs of each other are isomorphic.** -/
noncomputable def antisymm (f : H.SubgraphOf G) (g : G.SubgraphOf H) : H ≃cg G :=
  isoOfInjective f f.injective f.map_adj' g.card_le g.E_le

end SubgraphOf

namespace InducedSubgraphOf

variable {H G K : CGraph}

instance : FunLike (H.InducedSubgraphOf G) H.V G.V where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _, _⟩, _⟩ := f
    obtain ⟨⟨_, _, _⟩, _⟩ := g
    congr

@[simp] theorem coe_mk (f : H.V → G.V) (hinj hadj hadj') :
    ⇑(⟨⟨f, hinj, hadj⟩, hadj'⟩ : H.InducedSubgraphOf G) = f := rfl

@[simp] theorem coe_toSubgraphOf (f : H.InducedSubgraphOf G) : ⇑f.toSubgraphOf = ⇑f := rfl

theorem injective (f : H.InducedSubgraphOf G) : Function.Injective f := f.injective'

theorem map_adj (f : H.InducedSubgraphOf G) {x y : H.V} (h : H.Adj x y) : G.Adj (f x) (f y) :=
  f.map_adj' x y h

theorem adj_map (f : H.InducedSubgraphOf G) {x y : H.V} (h : G.Adj (f x) (f y)) : H.Adj x y :=
  f.adj_map' x y h

theorem adj_eq (f : H.InducedSubgraphOf G) (x y : H.V) : G.Adj (f x) (f y) = H.Adj x y :=
  Bool.eq_iff_iff.2 ⟨fun h ↦ f.adj_map h, fun h ↦ f.map_adj h⟩

/-- An isomorphism is in particular an induced subgraph inclusion. -/
def ofIso (i : H ≃cg G) : H.InducedSubgraphOf G where
  toSubgraphOf := SubgraphOf.ofIso i
  adj_map' x y h := by
    have h' : G.Adj (i x) (i y) = true := h
    rwa [i.adj_eq] at h'

/-- Every graph is an induced subgraph of itself. -/
def refl (G : CGraph) : G.InducedSubgraphOf G := ofIso (RelIso.refl _)

/-- An induced subgraph of an induced subgraph is one. -/
def trans (f : H.InducedSubgraphOf G) (g : G.InducedSubgraphOf K) : H.InducedSubgraphOf K where
  toSubgraphOf := f.toSubgraphOf.trans g.toSubgraphOf
  adj_map' _ _ h := f.adj_map (g.adj_map h)

/-- **Two graphs that are induced subgraphs of each other are isomorphic.**  No edge count is
needed: the vertex map is already a bijection that reflects adjacency. -/
noncomputable def antisymm (f : H.InducedSubgraphOf G) (g : G.InducedSubgraphOf H) : H ≃cg G := by
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨f.injective, le_antisymm (Fintype.card_le_of_injective f f.injective)
        (Fintype.card_le_of_injective g g.injective)⟩
  exact isoOfAdj (Equiv.ofBijective f hbij) fun x y ↦ f.adj_eq x y

end InducedSubgraphOf

namespace QuotientOf

variable {H G K : CGraph}

instance : FunLike (H.QuotientOf G) G.V H.V where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

theorem surjective (f : H.QuotientOf G) : Function.Surjective f := f.surjective'

theorem map_adj (f : H.QuotientOf G) {x y : G.V} (h : G.Adj x y) : H.Adj (f x) (f y) :=
  f.map_adj' x y h

theorem card_le (f : H.QuotientOf G) : Fintype.card H.V ≤ Fintype.card G.V :=
  Fintype.card_le_of_surjective _ f.surjective

/-- An isomorphism presents either graph as a quotient of the other. -/
def ofIso (i : H ≃cg G) : H.QuotientOf G where
  toFun := i.symm
  surjective' x := ⟨i x, RelIso.symm_apply_apply i x⟩
  map_adj' _ _ h := Iso.symm_adj i h

/-- Every graph is a quotient of itself. -/
def refl (G : CGraph) : G.QuotientOf G where
  toFun := id
  surjective' := Function.surjective_id
  map_adj' _ _ h := h

/-- A quotient of a quotient is a quotient. -/
def trans (f : H.QuotientOf G) (g : G.QuotientOf K) : H.QuotientOf K where
  toFun x := f (g x)
  surjective' := f.surjective.comp g.surjective
  map_adj' _ _ h := f.map_adj (g.map_adj h)

/-- **Two graphs that are quotients of each other are isomorphic**: the vertex maps are bijections,
so each is an injective homomorphism, and the edge counts pin them down. -/
noncomputable def antisymm (f : H.QuotientOf G) (g : G.QuotientOf H) : H ≃cg G := by
  have hcard : Fintype.card H.V = Fintype.card G.V :=
    le_antisymm (Fintype.card_le_of_surjective _ f.surjective)
      (Fintype.card_le_of_surjective _ g.surjective)
  have hginj : Function.Injective ⇑g :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨g.surjective, hcard⟩ |>.1
  have hfinj : Function.Injective ⇑f :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨f.surjective, hcard.symm⟩ |>.1
  exact isoOfInjective ⇑g hginj g.map_adj' (le_of_eq hcard.symm)
    (E_le_of_injective ⇑f hfinj f.map_adj')

end QuotientOf

/-! ## Minors -/

/-- `H.MinorOf G`: `H` is a minor of `G`, as data — a partial map from the vertices of `G` to
those of `H`, the *branch map*, whose fibres are connected and nonempty and which realises every
edge of `H` by an edge of `G` between the corresponding fibres. -/
structure MinorOf (H G : CGraph) where
  /-- The vertex of `H` a vertex of `G` is contracted into, if it is not deleted. -/
  branch : G.V → Option H.V
  /-- Every branch set is nonempty and connected. -/
  connectedOn' : ∀ x : H.V, G.ConnectedOn {v | branch v = some x}
  /-- Every edge of `H` comes from an edge of `G` between the two branch sets. -/
  map_adj' : ∀ x y : H.V, H.Adj x y →
    ∃ u v, branch u = some x ∧ branch v = some y ∧ G.Adj u v

/-- `H.InducedMinorOf G`: `H` is an *induced* minor of `G` — a minor whose branch map has no edges
between the branch sets of non-adjacent vertices. -/
structure InducedMinorOf (H G : CGraph) extends MinorOf H G where
  /-- An edge between two different branch sets is an edge of `H`. -/
  adj_map' : ∀ x y : H.V, x ≠ y →
    (∃ u v, branch u = some x ∧ branch v = some y ∧ G.Adj u v) → H.Adj x y

/-- `H.ContractionOf G`: `H` is a *contraction* of `G` — an induced minor that deletes nothing.
The branch sets then partition the vertices of `G` into connected blocks, one per vertex of `H`,
with two blocks joined in `H` exactly when an edge of `G` runs between them: `H` is `G` with each
block shrunk to a point.

Deleting nothing is the one extra field.  It is a `Prop` on the partial branch map rather than a
total map `G.V → H.V`, so that a contraction *is* an induced minor by the inherited projection and
inherits its transitivity, its antisymmetry and its edge count; `ContractionOf.toFun` reads the
total map back off, and is what to compute with. -/
structure ContractionOf (H G : CGraph) extends InducedMinorOf H G where
  /-- No vertex of `G` is deleted. -/
  total' : ∀ u : G.V, (branch u).isSome

namespace MinorOf

variable {H G K : CGraph}

theorem connectedOn (f : H.MinorOf G) (x : H.V) : G.ConnectedOn {v | f.branch v = some x} :=
  f.connectedOn' x

theorem map_adj (f : H.MinorOf G) {x y : H.V} (h : H.Adj x y) :
    ∃ u v, f.branch u = some x ∧ f.branch v = some y ∧ G.Adj u v :=
  f.map_adj' x y h

/-- An isomorphism is in particular a minor model. -/
def ofIso (i : H ≃cg G) : H.MinorOf G where
  branch v := some (i.symm v)
  connectedOn' x := by
    have h : {v : G.V | some (i.symm v) = some x} = {i x} := by
      ext v
      simp only [Set.mem_setOf_eq, Option.some.injEq, Set.mem_singleton_iff]
      exact ⟨fun hv ↦ by rw [← hv]; simp, fun hv ↦ by rw [hv]; simp⟩
    rw [h]
    exact connectedOn_singleton G (i x)
  map_adj' x y h := by
    refine ⟨i x, i y, by simp, by simp, ?_⟩
    rw [i.adj_eq]
    exact h

/-- Every graph is a minor of itself. -/
def refl (G : CGraph) : G.MinorOf G := ofIso (RelIso.refl _)

/-- **A minor of a minor is a minor**: compose the branch maps with `Option.bind`, and the branch
sets of the composite are the unions supplied by `connectedOn_biUnion`. -/
def trans (f : H.MinorOf K) (g : K.MinorOf G) : H.MinorOf G where
  branch v := (g.branch v).bind f.branch
  connectedOn' x := by
    have hset : {v : G.V | (g.branch v).bind f.branch = some x}
        = ⋃ k ∈ {k : K.V | f.branch k = some x}, {v : G.V | g.branch v = some k} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro hv
        rcases hk : g.branch v with _ | k
        · rw [hk] at hv; simp at hv
        · exact ⟨k, by rw [hk] at hv; simpa using hv, rfl⟩
      · rintro ⟨k, hk, hv⟩
        rw [hv]
        simpa using hk
    rw [hset]
    refine connectedOn_biUnion (f.connectedOn x) (fun k _ ↦ g.connectedOn k) ?_
    intro k _ k' _ hkk'
    obtain ⟨u, v, hu, hv, huv⟩ := g.map_adj hkk'
    exact ⟨u, hu, v, hv, huv⟩
  map_adj' x y h := by
    obtain ⟨k, k', hk, hk', hkk'⟩ := f.map_adj h
    obtain ⟨u, v, hu, hv, huv⟩ := g.map_adj hkk'
    exact ⟨u, v, by rw [hu]; simpa using hk, by rw [hv]; simpa using hk', huv⟩

@[simp] theorem trans_branch (f : H.MinorOf K) (g : K.MinorOf G) (v : G.V) :
    (f.trans g).branch v = (g.branch v).bind f.branch := rfl

/-- The branch sets are nonempty and disjoint, so a minor has no more vertices. -/
theorem card_le (f : H.MinorOf G) : Fintype.card H.V ≤ Fintype.card G.V := by
  choose r hr using fun x : H.V ↦ (f.connectedOn x).nonempty
  simp only [Set.mem_setOf_eq] at hr
  refine Fintype.card_le_of_injective r fun x y h ↦ ?_
  have hx := hr x
  rw [h, hr y] at hx
  exact (Option.some_inj.mp hx).symm

end MinorOf

namespace InducedMinorOf

variable {H G K : CGraph}

theorem adj_map (f : H.InducedMinorOf G) {x y : H.V} (hxy : x ≠ y)
    (h : ∃ u v, f.branch u = some x ∧ f.branch v = some y ∧ G.Adj u v) : H.Adj x y :=
  f.adj_map' x y hxy h

/-- An isomorphism is in particular an induced minor model. -/
def ofIso (i : H ≃cg G) : H.InducedMinorOf G where
  toMinorOf := MinorOf.ofIso i
  adj_map' x y _ := by
    rintro ⟨u, v, hu, hv, huv⟩
    simp only [MinorOf.ofIso, Option.some.injEq] at hu hv
    subst hu; subst hv
    rw [← i.adj_eq]
    simpa using huv

/-- Every graph is an induced minor of itself. -/
def refl (G : CGraph) : G.InducedMinorOf G := ofIso (RelIso.refl _)

/-- An induced minor of an induced minor is one. -/
def trans (f : H.InducedMinorOf K) (g : K.InducedMinorOf G) : H.InducedMinorOf G where
  toMinorOf := f.toMinorOf.trans g.toMinorOf
  adj_map' x y hxy := by
    rintro ⟨u, v, hu, hv, huv⟩
    rw [MinorOf.trans_branch] at hu hv
    rcases hk : g.branch u with _ | k
    · rw [hk] at hu; simp at hu
    · rcases hk' : g.branch v with _ | k'
      · rw [hk'] at hv; simp at hv
      · rw [hk] at hu
        rw [hk'] at hv
        simp only [Option.bind_some] at hu hv
        rcases eq_or_ne k k' with rfl | hkk'
        · exact absurd (hu.symm.trans hv) (by simpa using hxy)
        · exact f.adj_map hxy ⟨k, k', hu, hv, g.adj_map hkk' ⟨u, v, hk, hk', huv⟩⟩

end InducedMinorOf

namespace ContractionOf

variable {H G K : CGraph}

theorem total (f : H.ContractionOf G) (u : G.V) : (f.branch u).isSome := f.total' u

/-- The vertex of `H` a vertex of `G` is contracted into.  A contraction deletes nothing, so this
is defined everywhere, and it is the map a computation should use. -/
def toFun (f : H.ContractionOf G) (u : G.V) : H.V := (f.branch u).get (f.total u)

theorem branch_injective : Function.Injective fun f : H.ContractionOf G ↦ f.branch := by
  rintro ⟨⟨⟨bf, _, _⟩, _⟩, _⟩ ⟨⟨⟨bg, _, _⟩, _⟩, _⟩ h
  have hb : bf = bg := h
  subst hb
  rfl

instance : FunLike (H.ContractionOf G) G.V H.V where
  coe := toFun
  coe_injective' f g h := branch_injective (funext fun u ↦
    (Option.some_get (f.total u)).symm.trans
      ((congrArg some (congrFun h u)).trans (Option.some_get (g.total u))))

theorem branch_eq (f : H.ContractionOf G) (u : G.V) : f.branch u = some (f u) :=
  (Option.some_get (f.total u)).symm

@[simp] theorem branch_eq_some_iff (f : H.ContractionOf G) {u : G.V} {x : H.V} :
    f.branch u = some x ↔ f u = x := by
  rw [f.branch_eq u, Option.some_inj]

/-- The blocks are the fibres of `toFun`, and each of them is connected. -/
theorem connectedOn (f : H.ContractionOf G) (x : H.V) : G.ConnectedOn {v | f v = x} := by
  have h : {v : G.V | f v = x} = {v | f.branch v = some x} :=
    Set.ext fun v ↦ (f.branch_eq_some_iff).symm
  rw [h]
  exact f.connectedOn' x

/-- Every block is nonempty, so a contraction hits every vertex of `H`. -/
theorem surjective (f : H.ContractionOf G) : Function.Surjective f := fun x ↦
  (f.connectedOn x).nonempty

theorem map_adj (f : H.ContractionOf G) {x y : H.V} (h : H.Adj x y) :
    ∃ u v, f u = x ∧ f v = y ∧ G.Adj u v := by
  obtain ⟨u, v, hu, hv, huv⟩ := f.toInducedMinorOf.toMinorOf.map_adj h
  exact ⟨u, v, f.branch_eq_some_iff.mp hu, f.branch_eq_some_iff.mp hv, huv⟩

/-- An edge of `G` between two different blocks is an edge of `H`. -/
theorem adj_map (f : H.ContractionOf G) {u v : G.V} (h : G.Adj u v) (huv : f u ≠ f v) :
    H.Adj (f u) (f v) :=
  f.toInducedMinorOf.adj_map huv ⟨u, v, f.branch_eq u, f.branch_eq v, h⟩

/-- An isomorphism contracts nothing at all. -/
def ofIso (i : H ≃cg G) : H.ContractionOf G where
  toInducedMinorOf := InducedMinorOf.ofIso i
  total' _ := rfl

@[simp] theorem ofIso_apply (i : H ≃cg G) (u : G.V) : ofIso i u = i.symm u := rfl

/-- Every graph is a contraction of itself. -/
def refl (G : CGraph) : G.ContractionOf G := ofIso (RelIso.refl _)

/-- **A contraction of a contraction is a contraction**: composing two total branch maps leaves
nothing deleted. -/
def trans (f : H.ContractionOf K) (g : K.ContractionOf G) : H.ContractionOf G where
  toInducedMinorOf := f.toInducedMinorOf.trans g.toInducedMinorOf
  total' u := by
    show ((g.branch u).bind f.branch).isSome
    rw [g.branch_eq u, Option.bind_some, f.branch_eq]
    rfl

@[simp] theorem trans_apply (f : H.ContractionOf K) (g : K.ContractionOf G) (u : G.V) :
    (f.trans g) u = f (g u) := by
  have h : (f.trans g).branch u = some (f (g u)) := by
    show ((g.branch u).bind f.branch) = _
    rw [g.branch_eq u, Option.bind_some, f.branch_eq]
  exact (f.trans g).branch_eq_some_iff.mp h

/-- The blocks are nonempty and disjoint, so a contraction has no more vertices. -/
theorem card_le (f : H.ContractionOf G) : Fintype.card H.V ≤ Fintype.card G.V :=
  f.toInducedMinorOf.toMinorOf.card_le

end ContractionOf

/-! ## Topological minors and immersions

The last two relations replace the edges of `H` by walks of `G` between the images of the
endpoints.  For a topological minor the walks are paths, meeting each other only at branch
vertices; for an immersion they are trails, sharing no edge.  Both index the walks by an adjacency
proof, `H.Adj x y`, which by proof irrelevance is the same as indexing them by the ordered pair —
whence the field asking that the walk of `(y, x)` be the reverse of the walk of `(x, y)`. -/

/-- `H.TopMinorOf G`: `H` is a topological minor of `G` — an injection of the vertices of `H` into
those of `G` and, for every edge of `H`, a path of `G` between the images of its endpoints, such
that a vertex on two paths with different endpoints is a branch vertex, and the only branch
vertices on a path are the images of its own endpoints. -/
structure TopMinorOf (H G : CGraph) where
  /-- The branch vertices. -/
  toFun : H.V → G.V
  /-- The branch vertices are distinct. -/
  injective' : Function.Injective toFun
  /-- The path replacing an edge. -/
  path : ∀ {x y : H.V}, H.Adj x y → G.toSimple.Walk (toFun x) (toFun y)
  /-- Each of them is a path. -/
  isPath' : ∀ {x y : H.V} (h : H.Adj x y), (path h).IsPath
  /-- The path of an edge read backwards is the reverse path. -/
  reverse' : ∀ {x y : H.V} (h : H.Adj x y) (h' : H.Adj y x), path h' = (path h).reverse
  /-- The only branch vertices on a path are its endpoints. -/
  branch' : ∀ {x y : H.V} (h : H.Adj x y) (z : H.V), toFun z ∈ (path h).support → z = x ∨ z = y
  /-- Two paths with different endpoints meet only at branch vertices. -/
  disjoint' : ∀ {x y : H.V} (h : H.Adj x y) {x' y' : H.V} (h' : H.Adj x' y'),
    s(x, y) ≠ s(x', y') → ∀ z ∈ (path h).support, z ∈ (path h').support → ∃ b : H.V, z = toFun b

/-- `H.ImmersionOf G`: `H` immerses in `G` — an injection of the vertices of `H` into those of `G`
and, for every edge of `H`, a trail of `G` between the images of its endpoints, no two of them
sharing an edge.  Unlike a topological minor the trails may run through branch vertices and
through each other. -/
structure ImmersionOf (H G : CGraph) where
  /-- The branch vertices. -/
  toFun : H.V → G.V
  /-- The branch vertices are distinct. -/
  injective' : Function.Injective toFun
  /-- The trail replacing an edge. -/
  walk : ∀ {x y : H.V}, H.Adj x y → G.toSimple.Walk (toFun x) (toFun y)
  /-- Each of them is a trail. -/
  isTrail' : ∀ {x y : H.V} (h : H.Adj x y), (walk h).IsTrail
  /-- The trail of an edge read backwards is the reverse trail. -/
  reverse' : ∀ {x y : H.V} (h : H.Adj x y) (h' : H.Adj y x), walk h' = (walk h).reverse
  /-- Trails of different edges share no edge. -/
  edgeDisjoint' : ∀ {x y : H.V} (h : H.Adj x y) {x' y' : H.V} (h' : H.Adj x' y'),
    s(x, y) ≠ s(x', y') → ∀ e ∈ (walk h).edges, e ∉ (walk h').edges

namespace TopMinorOf

variable {H G : CGraph}

theorem injective (f : H.TopMinorOf G) : Function.Injective f.toFun := f.injective'

/-- A subgraph is a topological minor: every path is a single edge. -/
def ofSubgraphOf (f : H.SubgraphOf G) : H.TopMinorOf G where
  toFun := f
  injective' := f.injective
  path h := SimpleGraph.Walk.cons (f.map_adj h) SimpleGraph.Walk.nil
  isPath' := fun {x y} h ↦ by
    have hne : f x ≠ f y := (show G.toSimple.Adj (f x) (f y) from f.map_adj h).ne
    simp [SimpleGraph.Walk.cons_isPath_iff, hne]
  reverse' := fun h h' ↦ by simp
  branch' := fun {x y} h z hz ↦ by
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz
    · exact Or.inl (f.injective hz)
    · exact Or.inr (f.injective hz)
  disjoint' := fun {x y} h {x' y'} h' _ z hz _ ↦ by
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact ⟨x, rfl⟩
    · exact ⟨y, rfl⟩

/-- An isomorphism is in particular a topological minor model. -/
def ofIso (i : H ≃cg G) : H.TopMinorOf G := ofSubgraphOf (SubgraphOf.ofIso i)

/-- Every graph is a topological minor of itself. -/
def refl (G : CGraph) : G.TopMinorOf G := ofIso (RelIso.refl _)

/-- **Transport a topological minor model along isomorphisms of both graphs**: reindex the
branch vertices and push the paths forward.  Transitivity would let this be a composition of
three models; without it, this is what the descent to `IsoGraph` uses. -/
def congr {H' G' : CGraph} (f : H.TopMinorOf G) (i : H ≃cg H') (j : G ≃cg G') :
    H'.TopMinorOf G' where
  toFun x := j (f.toFun (i.symm x))
  injective' _ _ h := RelIso.injective i.symm (f.injective (RelIso.injective j h))
  path h := (f.path (i.symm_adj h)).map j.toSimpleHom
  isPath' _ := SimpleGraph.Walk.map_isPath_of_injective (RelIso.injective j) (f.isPath' _)
  reverse' h h' := by
    rw [SimpleGraph.Walk.reverse_map, f.reverse' (i.symm_adj h) (i.symm_adj h')]
  branch' := fun {x y} h z hz ↦ by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨a, ha, hja⟩ := hz
    have hae : a = f.toFun (i.symm z) := RelIso.injective j hja
    subst hae
    rcases f.branch' (i.symm_adj h) (i.symm z) ha with hz | hz
    · exact Or.inl (RelIso.injective i.symm hz)
    · exact Or.inr (RelIso.injective i.symm hz)
  disjoint' := fun {x y} h {x' y'} h' hne z hz hz' ↦ by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz hz'
    obtain ⟨a, ha, hja⟩ := hz
    obtain ⟨a', ha', hja'⟩ := hz'
    have haa : a = a' := RelIso.injective j (hja.trans hja'.symm)
    subst haa
    have hne' : s(i.symm x, i.symm y) ≠ s(i.symm x', i.symm y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨RelIso.injective i.symm h1, RelIso.injective i.symm h2⟩
      · exact Or.inr ⟨RelIso.injective i.symm h1, RelIso.injective i.symm h2⟩
    obtain ⟨b, rfl⟩ := f.disjoint' (i.symm_adj h) (i.symm_adj h') hne' a ha ha'
    exact ⟨i b, by rw [← hja, i.symm_apply_apply]; rfl⟩

end TopMinorOf

namespace ImmersionOf

variable {H G : CGraph}

theorem injective (f : H.ImmersionOf G) : Function.Injective f.toFun := f.injective'

theorem card_le (f : H.ImmersionOf G) : Fintype.card H.V ≤ Fintype.card G.V :=
  Fintype.card_le_of_injective _ f.injective

/-- **A topological minor is an immersion**: paths are trails, and two paths that shared an edge
would share both of its endpoints, which are then branch vertices of both, forcing the two edges
of `H` to be the same one. -/
def ofTopMinorOf (f : H.TopMinorOf G) : H.ImmersionOf G where
  toFun := f.toFun
  injective' := f.injective
  walk h := f.path h
  isTrail' h := (f.isPath' h).isTrail
  reverse' h h' := f.reverse' h h'
  edgeDisjoint' := by
    intro x y h x' y' h' hne e he he'
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.toSimple.Adj a b := SimpleGraph.Walk.adj_of_mem_edges _ he
      have ha : a ∈ (f.path h).support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he
      have hb : b ∈ (f.path h).support := SimpleGraph.Walk.snd_mem_support_of_mem_edges _ he
      have ha' : a ∈ (f.path h').support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he'
      have hb' : b ∈ (f.path h').support := SimpleGraph.Walk.snd_mem_support_of_mem_edges _ he'
      obtain ⟨ba, rfl⟩ := f.disjoint' h h' hne a ha ha'
      obtain ⟨bb, rfl⟩ := f.disjoint' h h' hne b hb hb'
      have hbab : ba ≠ bb := fun hc ↦ hab.ne (by rw [hc])
      have h1 := f.branch' h ba ha
      have h2 := f.branch' h bb hb
      have h3 := f.branch' h' ba ha'
      have h4 := f.branch' h' bb hb'
      refine hne ?_
      rw [Sym2.eq_iff]
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
        rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
          first
            | exact absurd rfl hbab
            | (subst h3; subst h4; tauto)

/-- A subgraph is an immersion. -/
def ofSubgraphOf (f : H.SubgraphOf G) : H.ImmersionOf G := ofTopMinorOf (TopMinorOf.ofSubgraphOf f)

/-- An isomorphism is in particular an immersion. -/
def ofIso (i : H ≃cg G) : H.ImmersionOf G := ofSubgraphOf (SubgraphOf.ofIso i)

/-- Every graph immerses in itself. -/
def refl (G : CGraph) : G.ImmersionOf G := ofIso (RelIso.refl _)

/-- **Transport an immersion along isomorphisms of both graphs.**  As for topological minors, this
is what the descent to `IsoGraph` uses in place of transitivity. -/
def congr {H' G' : CGraph} (f : H.ImmersionOf G) (i : H ≃cg H') (j : G ≃cg G') :
    H'.ImmersionOf G' where
  toFun x := j (f.toFun (i.symm x))
  injective' _ _ h := RelIso.injective i.symm (f.injective (RelIso.injective j h))
  walk h := (f.walk (i.symm_adj h)).map j.toSimpleHom
  isTrail' _ := SimpleGraph.Walk.map_isTrail_of_injective (RelIso.injective j) (f.isTrail' _)
  reverse' h h' := by
    rw [SimpleGraph.Walk.reverse_map, f.reverse' (i.symm_adj h) (i.symm_adj h')]
  edgeDisjoint' := fun {x y} h {x' y'} h' hne e he he' ↦ by
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he he'
    obtain ⟨e₁, he₁, hme₁⟩ := he
    obtain ⟨e₂, he₂, hme₂⟩ := he'
    have h12 : e₁ = e₂ := Sym2.map.injective (RelIso.injective j) (hme₁.trans hme₂.symm)
    subst h12
    have hne' : s(i.symm x, i.symm y) ≠ s(i.symm x', i.symm y') := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨RelIso.injective i.symm h1, RelIso.injective i.symm h2⟩
      · exact Or.inr ⟨RelIso.injective i.symm h1, RelIso.injective i.symm h2⟩
    exact f.edgeDisjoint' (i.symm_adj h) (i.symm_adj h') hne' e₁ he₁ he₂

end ImmersionOf

/-! ## The weakenings between the relations

Everything that is not an inherited projection.  An induced subgraph is a subgraph and an induced
minor is a minor by `toSubgraphOf` and `toMinorOf`; the rest are here. -/

variable {H G : CGraph}

/-- A subgraph is a minor: delete what is not in the image, contract nothing. -/
noncomputable def SubgraphOf.toMinorOf (f : H.SubgraphOf G) : H.MinorOf G where
  branch v := if h : ∃ x, f x = v then some h.choose else none
  connectedOn' x := by
    have hset : {v : G.V | (if h : ∃ x, f x = v then some h.choose else none) = some x}
        = {f x} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hv
        by_cases h : ∃ y, f y = v
        · rw [dif_pos h, Option.some.injEq] at hv
          rw [← h.choose_spec, hv]
        · rw [dif_neg h] at hv; exact absurd hv (by simp)
      · rintro rfl
        have h : ∃ y, f y = f x := ⟨x, rfl⟩
        rw [dif_pos h, Option.some.injEq]
        exact f.injective h.choose_spec
    rw [hset]
    exact connectedOn_singleton G (f x)
  map_adj' x y h := by
    have hx : ∃ z, f z = f x := ⟨x, rfl⟩
    have hy : ∃ z, f z = f y := ⟨y, rfl⟩
    refine ⟨f x, f y, ?_, ?_, f.map_adj h⟩
    · rw [dif_pos hx, Option.some.injEq]; exact f.injective hx.choose_spec
    · rw [dif_pos hy, Option.some.injEq]; exact f.injective hy.choose_spec

/-- An induced subgraph is an induced minor. -/
noncomputable def InducedSubgraphOf.toInducedMinorOf (f : H.InducedSubgraphOf G) :
    H.InducedMinorOf G where
  toMinorOf := f.toSubgraphOf.toMinorOf
  adj_map' x y _ := by
    rintro ⟨u, v, hu, hv, huv⟩
    simp only [SubgraphOf.toMinorOf] at hu hv
    by_cases hx : ∃ z, f.toSubgraphOf z = u
    · by_cases hy : ∃ z, f.toSubgraphOf z = v
      · rw [dif_pos hx, Option.some.injEq] at hu
        rw [dif_pos hy, Option.some.injEq] at hv
        rw [← hx.choose_spec, ← hy.choose_spec, hu, hv] at huv
        exact f.adj_map huv
      · rw [dif_neg hy] at hv; exact absurd hv (by simp)
    · rw [dif_neg hx] at hu; exact absurd hu (by simp)

/-- A homomorphism onto every vertex is a quotient map; this is the shape a `QuotientOf` gives
back as a plain homomorphism. -/
def QuotientOf.toHom (f : H.QuotientOf G) : G →cg H := ⟨f, fun h ↦ f.map_adj h⟩

/-! ## The empty graph

`empty 0` sits below everything in all of these orders but the quotient and contraction ones,
where a map *onto* no vertices needs no vertices to start from. -/

/-- The homomorphism out of the empty graph. -/
def homEmptyZero (G : CGraph) : empty 0 →cg G := ⟨fun x ↦ x.elim0, fun {a} _ ↦ a.elim0⟩

/-- The empty graph is a subgraph of every graph. -/
def SubgraphOf.emptyZero (G : CGraph) : (empty 0).SubgraphOf G where
  toFun x := x.elim0
  injective' a _ _ := a.elim0
  map_adj' x _ _ := x.elim0

/-- The empty graph is an induced subgraph of every graph. -/
def InducedSubgraphOf.emptyZero (G : CGraph) : (empty 0).InducedSubgraphOf G where
  toSubgraphOf := SubgraphOf.emptyZero G
  adj_map' x _ _ := x.elim0

/-- The empty graph is a minor of every graph. -/
def MinorOf.emptyZero (G : CGraph) : (empty 0).MinorOf G where
  branch _ := none
  connectedOn' x := x.elim0
  map_adj' x _ _ := x.elim0

/-- The empty graph is an induced minor of every graph. -/
def InducedMinorOf.emptyZero (G : CGraph) : (empty 0).InducedMinorOf G where
  toMinorOf := MinorOf.emptyZero G
  adj_map' x _ _ _ := x.elim0

/-- The empty graph is a topological minor of every graph. -/
def TopMinorOf.emptyZero (G : CGraph) : (empty 0).TopMinorOf G :=
  TopMinorOf.ofSubgraphOf (SubgraphOf.emptyZero G)

/-- The empty graph immerses in every graph. -/
def ImmersionOf.emptyZero (G : CGraph) : (empty 0).ImmersionOf G :=
  ImmersionOf.ofSubgraphOf (SubgraphOf.emptyZero G)

end CGraph

/-! ## On isomorphism classes

Each relation descends to `IsoGraph` as the `Prop` that some containment exists.  The side
condition of the descent is that the relation is invariant under isomorphism of either side, which
`ofIso` and `trans` give: pre- and post-compose. -/

namespace IsoGraph

open CGraph

/-- `H.HasHomInto G`: some homomorphism `H → G` exists. -/
def HasHomInto : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H →cg G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨(j.toRelEmbedding.toRelHom.comp f).comp i.symm.toRelEmbedding.toRelHom⟩,
      fun ⟨f⟩ ↦ ⟨(j.symm.toRelEmbedding.toRelHom.comp f).comp i.toRelEmbedding.toRelHom⟩⟩

@[simp, isoTransfer] theorem hasHomInto_mk (H G : CGraph) :
    HasHomInto ⟦H⟧ ⟦G⟧ ↔ Nonempty (H →cg G) := Iff.rfl

/-- `H.IsSubgraphOf G`: `H` is isomorphic to a subgraph of `G`. -/
def IsSubgraphOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.SubgraphOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((SubgraphOf.ofIso i.symm).trans f).trans (SubgraphOf.ofIso j)⟩,
      fun ⟨f⟩ ↦ ⟨((SubgraphOf.ofIso i).trans f).trans (SubgraphOf.ofIso j.symm)⟩⟩

@[simp, isoTransfer] theorem isSubgraphOf_mk (H G : CGraph) :
    IsSubgraphOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.SubgraphOf G) := Iff.rfl

/-- `H.IsInducedSubgraphOf G`: `H` is isomorphic to an induced subgraph of `G`. -/
def IsInducedSubgraphOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.InducedSubgraphOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((InducedSubgraphOf.ofIso i.symm).trans f).trans (InducedSubgraphOf.ofIso j)⟩,
      fun ⟨f⟩ ↦ ⟨((InducedSubgraphOf.ofIso i).trans f).trans (InducedSubgraphOf.ofIso j.symm)⟩⟩

@[simp, isoTransfer] theorem isInducedSubgraphOf_mk (H G : CGraph) :
    IsInducedSubgraphOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.InducedSubgraphOf G) := Iff.rfl

/-- `G.HasQuotient H`: `H` is a homomorphic image of `G` under a surjection.  The map runs from
the left argument to the right one, as in `HasHomInto`; the order it induces runs the other way,
since a quotient is *below* what it is a quotient of. -/
def HasQuotient : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun G H ↦ Nonempty (H.QuotientOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((QuotientOf.ofIso j.symm).trans f).trans (QuotientOf.ofIso i)⟩,
      fun ⟨f⟩ ↦ ⟨((QuotientOf.ofIso j).trans f).trans (QuotientOf.ofIso i.symm)⟩⟩

@[simp, isoTransfer] theorem hasQuotient_mk (G H : CGraph) :
    HasQuotient ⟦G⟧ ⟦H⟧ ↔ Nonempty (H.QuotientOf G) := Iff.rfl

/-- `H.IsMinorOf G`: `H` is a minor of `G`. -/
def IsMinorOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.MinorOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((MinorOf.ofIso i.symm).trans f).trans (MinorOf.ofIso j)⟩,
      fun ⟨f⟩ ↦ ⟨((MinorOf.ofIso i).trans f).trans (MinorOf.ofIso j.symm)⟩⟩

@[simp, isoTransfer] theorem isMinorOf_mk (H G : CGraph) :
    IsMinorOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.MinorOf G) := Iff.rfl

/-- `H.IsInducedMinorOf G`: `H` is an induced minor of `G`. -/
def IsInducedMinorOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.InducedMinorOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((InducedMinorOf.ofIso i.symm).trans f).trans (InducedMinorOf.ofIso j)⟩,
      fun ⟨f⟩ ↦ ⟨((InducedMinorOf.ofIso i).trans f).trans (InducedMinorOf.ofIso j.symm)⟩⟩

@[simp, isoTransfer] theorem isInducedMinorOf_mk (H G : CGraph) :
    IsInducedMinorOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.InducedMinorOf G) := Iff.rfl

/-- `H.IsContractionOf G`: `H` is a contraction of `G` — the result of partitioning `G` into
connected blocks and shrinking each to a point. -/
def IsContractionOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.ContractionOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨((ContractionOf.ofIso i.symm).trans f).trans (ContractionOf.ofIso j)⟩,
      fun ⟨f⟩ ↦ ⟨((ContractionOf.ofIso i).trans f).trans (ContractionOf.ofIso j.symm)⟩⟩

@[simp, isoTransfer] theorem isContractionOf_mk (H G : CGraph) :
    IsContractionOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.ContractionOf G) := Iff.rfl

/-! The last two have no `trans`, so their invariance is proved instead by transporting a single
model along isomorphisms of both sides: `TopMinorOf.congr` and `ImmersionOf.congr`. -/

/-- `H.IsTopMinorOf G`: `H` is a topological minor of `G`. -/
def IsTopMinorOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.TopMinorOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨f.congr i j⟩, fun ⟨f⟩ ↦ ⟨f.congr i.symm j.symm⟩⟩

@[simp, isoTransfer] theorem isTopMinorOf_mk (H G : CGraph) :
    IsTopMinorOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.TopMinorOf G) := Iff.rfl

/-- `H.IsImmersionMinorOf G`: `H` immerses in `G`. -/
def IsImmersionMinorOf : IsoGraph → IsoGraph → Prop :=
  Quotient.lift₂ (fun H G ↦ Nonempty (H.ImmersionOf G)) fun _ _ _ _ ⟨i⟩ ⟨j⟩ ↦ propext
    ⟨fun ⟨f⟩ ↦ ⟨f.congr i j⟩, fun ⟨f⟩ ↦ ⟨f.congr i.symm j.symm⟩⟩

@[simp, isoTransfer] theorem isImmersionMinorOf_mk (H G : CGraph) :
    IsImmersionMinorOf ⟦H⟧ ⟦G⟧ ↔ Nonempty (H.ImmersionOf G) := Iff.rfl

/-! ## Reflexivity, transitivity and antisymmetry -/

theorem hasHomInto_refl (G : IsoGraph) : G.HasHomInto G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨RelHom.id _⟩

theorem hasHomInto_trans {H G K : IsoGraph} (h₁ : H.HasHomInto G) (h₂ : G.HasHomInto K) :
    H.HasHomInto K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨g.comp f⟩

theorem isSubgraphOf_refl (G : IsoGraph) : G.IsSubgraphOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨SubgraphOf.refl g⟩

theorem isSubgraphOf_trans {H G K : IsoGraph} (h₁ : H.IsSubgraphOf G) (h₂ : G.IsSubgraphOf K) :
    H.IsSubgraphOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

theorem isSubgraphOf_antisymm {H G : IsoGraph} (h₁ : H.IsSubgraphOf G) (h₂ : G.IsSubgraphOf H) :
    H = G := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨f.antisymm g⟩

theorem isInducedSubgraphOf_refl (G : IsoGraph) : G.IsInducedSubgraphOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨InducedSubgraphOf.refl g⟩

theorem isInducedSubgraphOf_trans {H G K : IsoGraph} (h₁ : H.IsInducedSubgraphOf G)
    (h₂ : G.IsInducedSubgraphOf K) : H.IsInducedSubgraphOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

theorem isInducedSubgraphOf_antisymm {H G : IsoGraph} (h₁ : H.IsInducedSubgraphOf G)
    (h₂ : G.IsInducedSubgraphOf H) : H = G := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨f.antisymm g⟩

theorem hasQuotient_refl (G : IsoGraph) : G.HasQuotient G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨QuotientOf.refl g⟩

theorem hasQuotient_trans {G K L : IsoGraph} (h₁ : G.HasQuotient K) (h₂ : K.HasQuotient L) :
    G.HasQuotient L := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ G K L ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨g.trans f⟩

theorem hasQuotient_antisymm {G H : IsoGraph} (h₁ : G.HasQuotient H) (h₂ : H.HasQuotient G) :
    G = H := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ G H ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨(f.antisymm g).symm⟩

theorem isMinorOf_refl (G : IsoGraph) : G.IsMinorOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨MinorOf.refl g⟩

theorem isMinorOf_trans {H G K : IsoGraph} (h₁ : H.IsMinorOf G) (h₂ : G.IsMinorOf K) :
    H.IsMinorOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

theorem isInducedMinorOf_refl (G : IsoGraph) : G.IsInducedMinorOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨InducedMinorOf.refl g⟩

theorem isInducedMinorOf_trans {H G K : IsoGraph} (h₁ : H.IsInducedMinorOf G)
    (h₂ : G.IsInducedMinorOf K) : H.IsInducedMinorOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

theorem isContractionOf_refl (G : IsoGraph) : G.IsContractionOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨ContractionOf.refl g⟩

theorem isContractionOf_trans {H G K : IsoGraph} (h₁ : H.IsContractionOf G)
    (h₂ : G.IsContractionOf K) : H.IsContractionOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

theorem isTopMinorOf_refl (G : IsoGraph) : G.IsTopMinorOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨TopMinorOf.refl g⟩

theorem isImmersionMinorOf_refl (G : IsoGraph) : G.IsImmersionMinorOf G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨ImmersionOf.refl g⟩

/-! ## The weakenings -/

theorem IsInducedSubgraphOf.isSubgraphOf {H G : IsoGraph} (h : H.IsInducedSubgraphOf G) :
    H.IsSubgraphOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toSubgraphOf⟩

theorem IsSubgraphOf.hasHomInto {H G : IsoGraph} (h : H.IsSubgraphOf G) : H.HasHomInto G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toHom⟩

theorem HasQuotient.hasHomInto {G H : IsoGraph} (h : G.HasQuotient H) : G.HasHomInto H := by
  revert h
  refine Quotient.inductionOn₂ G H ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toHom⟩

theorem IsSubgraphOf.isMinorOf {H G : IsoGraph} (h : H.IsSubgraphOf G) : H.IsMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toMinorOf⟩

theorem IsInducedSubgraphOf.isInducedMinorOf {H G : IsoGraph} (h : H.IsInducedSubgraphOf G) :
    H.IsInducedMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toInducedMinorOf⟩

theorem IsInducedMinorOf.isMinorOf {H G : IsoGraph} (h : H.IsInducedMinorOf G) : H.IsMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toMinorOf⟩

/-- A contraction is an induced minor: it is one that happens to delete nothing.  It is *not* a
quotient, though the map runs the same way — the blocks of a quotient are independent sets and the
blocks of a contraction are connected, so neither relation implies the other. -/
theorem IsContractionOf.isInducedMinorOf {H G : IsoGraph} (h : H.IsContractionOf G) :
    H.IsInducedMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toInducedMinorOf⟩

theorem IsContractionOf.isMinorOf {H G : IsoGraph} (h : H.IsContractionOf G) : H.IsMinorOf G :=
  h.isInducedMinorOf.isMinorOf

theorem IsSubgraphOf.isTopMinorOf {H G : IsoGraph} (h : H.IsSubgraphOf G) : H.IsTopMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨TopMinorOf.ofSubgraphOf f⟩

theorem IsTopMinorOf.isImmersionMinorOf {H G : IsoGraph} (h : H.IsTopMinorOf G) :
    H.IsImmersionMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨ImmersionOf.ofTopMinorOf f⟩

/-! ## What the relations say about the counts -/

theorem IsSubgraphOf.V_le {H G : IsoGraph} (h : H.IsSubgraphOf G) : H.V ≤ G.V := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.card_le

theorem IsSubgraphOf.E_le {H G : IsoGraph} (h : H.IsSubgraphOf G) : H.E ≤ G.E := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.E_le

theorem HasQuotient.V_le {G H : IsoGraph} (h : G.HasQuotient H) : H.V ≤ G.V := by
  revert h
  refine Quotient.inductionOn₂ G H ?_
  rintro _ _ ⟨f⟩
  exact f.card_le

theorem IsMinorOf.V_le {H G : IsoGraph} (h : H.IsMinorOf G) : H.V ≤ G.V := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.card_le

theorem IsImmersionMinorOf.V_le {H G : IsoGraph} (h : H.IsImmersionMinorOf G) : H.V ≤ G.V := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.card_le

theorem IsTopMinorOf.V_le {H G : IsoGraph} (h : H.IsTopMinorOf G) : H.V ≤ G.V :=
  h.isImmersionMinorOf.V_le

theorem IsInducedSubgraphOf.V_le {H G : IsoGraph} (h : H.IsInducedSubgraphOf G) : H.V ≤ G.V :=
  h.isSubgraphOf.V_le

theorem IsContractionOf.V_le {H G : IsoGraph} (h : H.IsContractionOf G) : H.V ≤ G.V :=
  h.isMinorOf.V_le

theorem IsInducedMinorOf.V_le {H G : IsoGraph} (h : H.IsInducedMinorOf G) : H.V ≤ G.V :=
  h.isMinorOf.V_le

/-! ## The empty graph at the bottom -/

theorem empty_zero_hasHomInto (G : IsoGraph) : HasHomInto (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨CGraph.homEmptyZero g⟩

theorem empty_zero_isSubgraphOf (G : IsoGraph) : IsSubgraphOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨SubgraphOf.emptyZero g⟩

theorem empty_zero_isInducedSubgraphOf (G : IsoGraph) : IsInducedSubgraphOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨InducedSubgraphOf.emptyZero g⟩

theorem empty_zero_isMinorOf (G : IsoGraph) : IsMinorOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨MinorOf.emptyZero g⟩

theorem empty_zero_isInducedMinorOf (G : IsoGraph) : IsInducedMinorOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨InducedMinorOf.emptyZero g⟩

theorem empty_zero_isTopMinorOf (G : IsoGraph) : IsTopMinorOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨TopMinorOf.emptyZero g⟩

theorem empty_zero_isImmersionMinorOf (G : IsoGraph) : IsImmersionMinorOf (empty 0) G := by
  induction G using Quotient.inductionOn with
  | h g => exact ⟨ImmersionOf.emptyZero g⟩

/-! ## The orders

One scope each, since they all put a different `≤` on the same type; opening two of them at once
is an ambiguity, not a refinement. -/

namespace Hom

/-- The homomorphism order.  Only a preorder: `K₂` and `K₂ ⊕g K₁` map into one another. -/
scoped instance : Preorder IsoGraph where
  le := HasHomInto
  le_refl := hasHomInto_refl
  le_trans _ _ _ := hasHomInto_trans

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.HasHomInto G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_hasHomInto

end Hom

namespace Subgraph

/-- The subgraph order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsSubgraphOf
  le_refl := isSubgraphOf_refl
  le_trans _ _ _ := isSubgraphOf_trans
  le_antisymm _ _ := isSubgraphOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsSubgraphOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isSubgraphOf

end Subgraph

namespace InducedSubgraph

/-- The induced subgraph order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsInducedSubgraphOf
  le_refl := isInducedSubgraphOf_refl
  le_trans _ _ _ := isInducedSubgraphOf_trans
  le_antisymm _ _ := isInducedSubgraphOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsInducedSubgraphOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isInducedSubgraphOf

end InducedSubgraph

namespace Quotient

/-- The order by homomorphic images: `H ≤ G` when `H` is a quotient of `G`, so the surjection runs
downwards.  It has no bottom element: a surjection onto the empty graph has to start from the empty
graph. -/
scoped instance : PartialOrder IsoGraph where
  le H G := G.HasQuotient H
  le_refl := hasQuotient_refl
  le_trans _ _ _ h₁ h₂ := hasQuotient_trans h₂ h₁
  le_antisymm _ _ h₁ h₂ := hasQuotient_antisymm h₂ h₁

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ G.HasQuotient H := Iff.rfl

end Quotient

/-! The two minor relations are partial orders as well, but their antisymmetry needs an argument of
its own; `Containment/Minors.lean` gives it, and declares the `IsoGraph.Minor` and
`IsoGraph.InducedMinor` scopes there. -/

/-! ## The orders in use

One scope at a time, and `≤`, `<` and `⊥` mean that relation. -/

section Examples

open scoped IsoGraph.Subgraph

example : (⊥ : IsoGraph) = empty 0 := rfl
example (G : IsoGraph) : (⊥ : IsoGraph) ≤ G := bot_le
example {H G : IsoGraph} (h : H ≤ G) : H.E ≤ G.E := IsSubgraphOf.E_le h
example {H G K : IsoGraph} (h₁ : H ≤ G) (h₂ : G ≤ K) : H ≤ K := h₁.trans h₂

end Examples

section Examples

open scoped IsoGraph.Hom

example (G : IsoGraph) : (⊥ : IsoGraph) ≤ G := bot_le
example {H G : IsoGraph} (h : H.IsInducedSubgraphOf G) : H ≤ G := h.isSubgraphOf.hasHomInto

end Examples

end IsoGraph
