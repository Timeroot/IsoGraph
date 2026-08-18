import IsoGraph.Values.Identities.Operators

/-!
# The algebra of graphs

`IsoGraph` carries two "sums" — the disjoint union `⊕g` and the join `∇g` — and four "products" —
the cartesian `□g`, tensor `⊗g`, strong `⊠g` and lexicographic `·g` ones.  All six share the same
units: the graph on no vertices is the zero of both sums and annihilates every product, and the
graph on one vertex is the one of three of the products.  This module packages that into the
algebraic classes of `Mathlib`.

None of it is an instance on `IsoGraph` itself.  `+`, `*`, `0` and `1` on graphs are notation to be
opted into, and *which* operation they denote is a choice; so each combination gets a scope of its
own.  The underlying data — one `Zero`, one `One`, two `Add`s and four `Mul`s — is declared once,
as plain definitions, and re-tagged `scoped instance` in every namespace that wants it, so no two
scopes can disagree about `0`, `1`, or the meaning of an operation they share.

| scope | `+` | `*` | what it opens |
| --- | --- | --- | --- |
| `IsoGraph.DisjUnion` | `⊕g` | | `AddCancelCommMonoid` |
| `IsoGraph.Join` | `∇g` | | `AddCancelCommMonoid` |
| `IsoGraph.CartesianProduct` | | `□g` | `CommMonoidWithZero`, `NoZeroDivisors` |
| `IsoGraph.TensorProduct` | | `⊗g` | `SemigroupWithZero`, `CommMagma`, `NoZeroDivisors` |
| `IsoGraph.StrongProduct` | | `⊠g` | `CommMonoidWithZero`, `NoZeroDivisors` |
| `IsoGraph.LexProduct` | | `·g` | `MonoidWithZero`, `NoZeroDivisors` |
| `IsoGraph.Semiring` | `⊕g` | `□g` | `CommSemiring` |
| `IsoGraph.StrongSemiring` | `⊕g` | `⊠g` | `CommSemiring` |
| `IsoGraph.TensorSemiring` | `⊕g` | `⊗g` | `NonUnitalCommSemiring` |
| `IsoGraph.LexSemiring` | `⊕g` | `·g` | `MonoidWithZero`, `RightDistribClass` |
| `IsoGraph.JoinLexSemiring` | `∇g` | `·g` | `MonoidWithZero`, `RightDistribClass` |

Where the table is ragged, it is because the missing law is false.

* **The tensor product has no unit.**  A unit would have to be a single vertex with a loop at it,
  and a `CGraph` is loopless: `empty 1 ⊗g G` is `empty G.V`.  So `⊗g` gets a `SemigroupWithZero`
  and a `CommMagma` where the other three products get a `CommMonoidWithZero`, and `1` is not part
  of either tensor scope.
* **The lexicographic product distributes on one side only.**  `(G ⊕g H) ·g K = G ·g K ⊕g H ·g K`
  and the same over `∇g`, because the first factor is the outer one; but `G ·g (H ⊕g K)` joins the
  two copies of `G`'s edges across the union, so it is not `G ·g H ⊕g G ·g K`.  Hence a
  `RightDistribClass` rather than a `Semiring`.
* **Those five pairs are the only ones that distribute.**  No product distributes over the join:
  in `(G ∇g H) □g K` two vertices over different sides and different `K`-coordinates are
  non-adjacent, while in `(G □g K) ∇g (H □g K)` everything across the join is adjacent — and the
  same computation rules out `⊗g` and `⊠g`.  The lexicographic product is the exception because
  complementation exchanges `⊕g` with `∇g` and fixes `·g` up to complementing the factors.
* **No product is cancellative.**  Already `empty 1 ⊗g complete 2 = empty 1 ⊗g empty 2` with
  `empty 1 ≠ 0`.  For the other three, cancellation is a theorem about unique prime factorisation
  and is not attempted here; what they do get is `NoZeroDivisors`, which is just the vertex count.

Both sums, on the other hand, *are* cancellative, and that is the one fact in this module that
needs an argument rather than a list of names.  It comes from the decomposition of a graph into its
connected components, which is the first section: `comps G` is the multiset of the isomorphism
classes of the components of `G`, it is additive over `⊕g` because the components of a disjoint
union are those of the factors, and a graph is the sum of its components, so a common summand can
be cancelled in the multiset and put back together.  Cancelling a join follows, since
`G ∇g H = (Gᶜ ⊕g Hᶜ)ᶜ`.
-/

set_option autoImplicit false

/-! ## The connected components of a graph

A graph is the disjoint union of the subgraphs induced on its connected components.  `restrict`
cuts out an induced subgraph, `splitIso` splits a graph along any set of vertices closed under
adjacency, and `part` takes the union of a chosen set of components; the decomposition itself is
`sigmaUnionComponent`, and `comps` records it as a multiset of isomorphism classes. -/

namespace CGraph

open SimpleGraph

variable {G H : CGraph}

/-- Components can be told apart: reachability is decidable, so equality of the classes it
generates is too. -/
instance instDecidableEqConnectedComponent (G : CGraph) :
    DecidableEq G.toSimple.ConnectedComponent :=
  @Quotient.decidableEq _ G.toSimple.reachableSetoid
    (inferInstance : DecidableRel G.toSimple.Reachable)

/-- The subgraph induced on a set of vertices. -/
def restrict (G : CGraph) (p : G.V → Prop) [DecidablePred p] : CGraph where
  V := {v : G.V // p v}
  Adj a b := G.Adj a b
  symm a b := G.symm a b
  loopless a := G.loopless a

@[simp] theorem restrict_adj (G : CGraph) (p : G.V → Prop) [DecidablePred p]
    (a b : {v : G.V // p v}) : (G.restrict p).Adj a b = G.Adj a b := rfl

/-- Restriction depends only on the set of vertices restricted to. -/
def restrictCongr (G : CGraph) (p q : G.V → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v ↔ q v) : G.restrict p ≃cg G.restrict q :=
  isoOfAdj (G := G.restrict p) (H := G.restrict q) (Equiv.subtypeEquivRight h) (fun _ _ ↦ rfl)

/-- Restricting to every vertex changes nothing. -/
def restrictUniv (G : CGraph) : G.restrict (fun _ ↦ True) ≃cg G :=
  isoOfAdj (G := G.restrict _) (H := G) (Equiv.subtypeUnivEquiv (fun _ ↦ trivial)) (fun _ _ ↦ rfl)

/-- Restricting to no vertex leaves the graph on no vertices. -/
noncomputable def restrictOfIsEmpty (G : CGraph) (p : G.V → Prop) [DecidablePred p]
    (h : ∀ v, ¬ p v) : G.restrict p ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ absurd x.2 (h x.1))
    (FinEnum.card_eq_zero_iff.2 ⟨fun x ↦ h x.1 x.2⟩)

/-- **A graph splits along any set of vertices closed under adjacency**: no edge crosses, so it is
the disjoint union of the two induced subgraphs. -/
def splitIso (G : CGraph) (p : G.V → Prop) [DecidablePred p]
    (hp : ∀ a b, G.Adj a b → p a → p b) :
    G ≃cg G.restrict p ⊕g G.restrict (fun v ↦ ¬ p v) :=
  (isoOfAdj (G := G.restrict p ⊕g G.restrict (fun v ↦ ¬ p v)) (H := G)
    (Equiv.sumCompl p) (by
      rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
      · rfl
      · exact Bool.eq_false_iff.2 (fun h ↦ hb (hp a b h ha))
      · exact Bool.eq_false_iff.2 (fun h ↦ ha (hp b a (by rw [G.symm]; exact h) hb))
      · rfl)).symm

/-- The components of a graph, enumerated.  Reachability is decidable on a finite graph, so the
components are a quotient by a decidable relation; `ofSurjective` lists the vertices' components
and deduplicates. -/
instance instFinEnumConnectedComponent (G : CGraph) : FinEnum G.toSimple.ConnectedComponent :=
  letI : DecidableEq G.toSimple.ConnectedComponent :=
    @Quotient.decidableEq _ G.toSimple.reachableSetoid
      (inferInstance : DecidableRel G.toSimple.Reachable)
  FinEnum.ofSurjective G.toSimple.connectedComponentMk fun c ↦ Quot.exists_rep c

/-- The subgraph induced on a single connected component. -/
def component (G : CGraph) (c : G.toSimple.ConnectedComponent) : CGraph :=
  G.restrict (fun v ↦ G.toSimple.connectedComponentMk v = c)

@[simp] theorem component_adj (G : CGraph) (c : G.toSimple.ConnectedComponent)
    (a b : {v : G.V // G.toSimple.connectedComponentMk v = c}) :
    (G.component c).Adj a b = G.Adj a b := rfl

/-- Lying in a fixed component is closed under adjacency. -/
theorem component_closed (G : CGraph) (c : G.toSimple.ConnectedComponent) (a b : G.V)
    (h : G.Adj a b) (ha : G.toSimple.connectedComponentMk a = c) :
    G.toSimple.connectedComponentMk b = c := by
  rw [← ha]
  exact (SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable (G := G.toSimple) h)).symm

/-- **A graph is the disjoint union of its connected components.** -/
def sigmaUnionComponent (G : CGraph) :
    sigmaUnion (fun c : G.toSimple.ConnectedComponent ↦ G.component c) ≃cg G :=
  isoOfAdj (G := sigmaUnion (fun c ↦ G.component c)) (H := G)
    (Equiv.sigmaFiberEquiv G.toSimple.connectedComponentMk) (by
      rintro ⟨c, v, hv⟩ ⟨d, w, hw⟩
      by_cases h : c = d
      · subst h
        exact (sigmaUnion_adj_mk (fun c ↦ G.component c) c ⟨v, hv⟩ ⟨w, hw⟩).symm
      · rw [sigmaUnion_adj_ne _ _ _ _ _ h, Bool.eq_false_iff, ne_eq]
        intro hadj
        exact h (by rw [← hv, ← hw]; exact (component_closed G _ v w hadj rfl).symm))

/-- The union of a set of connected components. -/
def part (G : CGraph) (S : Finset G.toSimple.ConnectedComponent) : CGraph :=
  G.restrict (fun v ↦ G.toSimple.connectedComponentMk v ∈ S)

/-- No components at all is the graph on no vertices. -/
noncomputable def partEmpty (G : CGraph) : G.part ∅ ≃cg empty 0 :=
  restrictOfIsEmpty G _ (fun _ ↦ Finset.notMem_empty _)

/-- All the components together are the whole graph. -/
def partUniv (G : CGraph) : G.part Finset.univ ≃cg G :=
  (restrictCongr G _ (fun _ ↦ True) (fun _ ↦ ⟨fun _ ↦ trivial, fun _ ↦ Finset.mem_univ _⟩)).trans
    (restrictUniv G)

/-- The distinguished component of a union of components. -/
private def partInsertLeft (G : CGraph) (c : G.toSimple.ConnectedComponent)
    (S : Finset G.toSimple.ConnectedComponent) :
    (G.part (insert c S)).restrict (fun x ↦ G.toSimple.connectedComponentMk x.1 = c)
      ≃cg G.component c :=
  isoOfAdj (G := (G.part (insert c S)).restrict
      (fun x ↦ G.toSimple.connectedComponentMk x.1 = c)) (H := G.component c)
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun v ↦ G.toSimple.connectedComponentMk v ∈ insert c S)
        (fun v ↦ G.toSimple.connectedComponentMk v = c)).trans
      (Equiv.subtypeEquivRight fun _ ↦
        ⟨And.right, fun h ↦ ⟨Finset.mem_insert.2 (Or.inl h), h⟩⟩))
    (fun _ _ ↦ rfl)

/-- The other components of a union of components. -/
private def partInsertRight (G : CGraph) (c : G.toSimple.ConnectedComponent)
    (S : Finset G.toSimple.ConnectedComponent) (hc : c ∉ S) :
    (G.part (insert c S)).restrict (fun x ↦ ¬ G.toSimple.connectedComponentMk x.1 = c)
      ≃cg G.part S :=
  isoOfAdj (G := (G.part (insert c S)).restrict
      (fun x ↦ ¬ G.toSimple.connectedComponentMk x.1 = c)) (H := G.part S)
    ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun v ↦ G.toSimple.connectedComponentMk v ∈ insert c S)
        (fun v ↦ ¬ G.toSimple.connectedComponentMk v = c)).trans
      (Equiv.subtypeEquivRight fun _ ↦
        ⟨fun h ↦ (Finset.mem_insert.1 h.1).resolve_left h.2,
          fun h ↦ ⟨Finset.mem_insert_of_mem h, fun he ↦ hc (he ▸ h)⟩⟩))
    (fun _ _ ↦ rfl)

/-- **Peeling one component off a union of components.** -/
def partInsert (G : CGraph) (c : G.toSimple.ConnectedComponent)
    (S : Finset G.toSimple.ConnectedComponent) (hc : c ∉ S) :
    G.part (insert c S) ≃cg G.component c ⊕g G.part S :=
  (splitIso (G.part (insert c S)) (fun x ↦ G.toSimple.connectedComponentMk x.1 = c)
    (fun a b hab ha ↦ component_closed G c a.1 b.1 hab ha)).trans
    (Iso.disjUnion (partInsertLeft G c S) (partInsertRight G c S hc))

/-- The connected components of a graph, as a multiset of isomorphism classes. -/
def comps (G : CGraph) : Multiset IsoGraph :=
  (Finset.univ : Finset G.toSimple.ConnectedComponent).val.map fun c ↦ (⟦G.component c⟧ : IsoGraph)

/-- An isomorphism restricts to each component. -/
def Iso.component {G H : CGraph} (σ : G ≃cg H) (c : G.toSimple.ConnectedComponent) :
    G.component c ≃cg H.component ((Iso.toSimpleIso σ).connectedComponentEquiv c) :=
  isoOfAdj (G := G.component c)
    (H := H.component ((Iso.toSimpleIso σ).connectedComponentEquiv c))
    (SimpleGraph.ConnectedComponent.isoEquivSupp (Iso.toSimpleIso σ) c)
    (fun x y ↦ σ.adj_eq x.1 y.1)

/-- **Isomorphic graphs have the same components.** -/
@[toIsoGraph]
theorem comps_eq_of_iso {G H : CGraph} (σ : G ≃cg H) : G.comps = H.comps := by
  have hmap : G.comps
      = (Finset.univ : Finset G.toSimple.ConnectedComponent).val.map
          (fun c ↦ (⟦H.component ((Iso.toSimpleIso σ).connectedComponentEquiv c)⟧ : IsoGraph)) :=
    Multiset.map_congr rfl fun c _ ↦ Quotient.sound ⟨Iso.component σ c⟩
  have huniv : (Finset.univ : Finset G.toSimple.ConnectedComponent).val.map
      (Iso.toSimpleIso σ).connectedComponentEquiv = (Finset.univ : Finset _).val := by
    have h := congrArg Finset.val
      (Finset.map_univ_equiv (Iso.toSimpleIso σ).connectedComponentEquiv)
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  rw [hmap, comps, ← huniv, Multiset.map_map]
  rfl

theorem disjUnionComponentEquiv_inl (G H : CGraph) (v : G.V) :
    disjUnionComponentEquiv G H ((G ⊕g H).toSimple.connectedComponentMk (Sum.inl v))
      = Sum.inl (G.toSimple.connectedComponentMk v) := rfl

theorem disjUnionComponentEquiv_inr (G H : CGraph) (w : H.V) :
    disjUnionComponentEquiv G H ((G ⊕g H).toSimple.connectedComponentMk (Sum.inr w))
      = Sum.inr (H.toSimple.connectedComponentMk w) := rfl

/-- A component of the left factor is a component of a disjoint union. -/
def componentDisjUnionInl (G H : CGraph) (c : G.toSimple.ConnectedComponent) :
    G.component c ≃cg (G ⊕g H).component ((disjUnionComponentEquiv G H).symm (Sum.inl c)) :=
  isoOfAdj (G := G.component c)
    (H := (G ⊕g H).component ((disjUnionComponentEquiv G H).symm (Sum.inl c)))
    (equivOfBijective (f := fun v : {v : G.V // G.toSimple.connectedComponentMk v = c} ↦
        (⟨Sum.inl v.1, by
          apply (disjUnionComponentEquiv G H).injective
          rw [disjUnionComponentEquiv_inl, Equiv.apply_symm_apply, v.2]⟩ :
        {x : (G ⊕g H).V // (G ⊕g H).toSimple.connectedComponentMk x
          = (disjUnionComponentEquiv G H).symm (Sum.inl c)}))
      ⟨fun a b h ↦ Subtype.ext (Sum.inl_injective (Subtype.ext_iff.1 h)), by
        rintro ⟨x | x, hx⟩
        · refine ⟨⟨x, ?_⟩, rfl⟩
          have := congrArg (disjUnionComponentEquiv G H) hx
          rw [disjUnionComponentEquiv_inl, Equiv.apply_symm_apply] at this
          exact Sum.inl_injective this
        · exfalso
          have := congrArg (disjUnionComponentEquiv G H) hx
          rw [disjUnionComponentEquiv_inr, Equiv.apply_symm_apply] at this
          exact Sum.inr_ne_inl this⟩)
    (fun _ _ ↦ rfl)

/-- A component of the right factor is a component of a disjoint union. -/
def componentDisjUnionInr (G H : CGraph) (c : H.toSimple.ConnectedComponent) :
    H.component c ≃cg (G ⊕g H).component ((disjUnionComponentEquiv G H).symm (Sum.inr c)) :=
  isoOfAdj (G := H.component c)
    (H := (G ⊕g H).component ((disjUnionComponentEquiv G H).symm (Sum.inr c)))
    (equivOfBijective (f := fun v : {v : H.V // H.toSimple.connectedComponentMk v = c} ↦
        (⟨Sum.inr v.1, by
          apply (disjUnionComponentEquiv G H).injective
          rw [disjUnionComponentEquiv_inr, Equiv.apply_symm_apply, v.2]⟩ :
        {x : (G ⊕g H).V // (G ⊕g H).toSimple.connectedComponentMk x
          = (disjUnionComponentEquiv G H).symm (Sum.inr c)}))
      ⟨fun a b h ↦ Subtype.ext (Sum.inr_injective (Subtype.ext_iff.1 h)), by
        rintro ⟨x | x, hx⟩
        · exfalso
          have := congrArg (disjUnionComponentEquiv G H) hx
          rw [disjUnionComponentEquiv_inl, Equiv.apply_symm_apply] at this
          exact Sum.inl_ne_inr this
        · refine ⟨⟨x, ?_⟩, rfl⟩
          have := congrArg (disjUnionComponentEquiv G H) hx
          rw [disjUnionComponentEquiv_inr, Equiv.apply_symm_apply] at this
          exact Sum.inr_injective this⟩)
    (fun _ _ ↦ rfl)

/-- **The components of a disjoint union are those of the two factors.** -/
@[toIsoGraph simp comps_disjUnion]
theorem comps_disjUnion (G H : CGraph) : (G ⊕g H).comps = G.comps + H.comps := by
  have huniv : (Finset.univ : Finset (G ⊕g H).toSimple.ConnectedComponent).val.map
      (disjUnionComponentEquiv G H) = (Finset.univ : Finset _).val := by
    have h := congrArg Finset.val (Finset.map_univ_equiv (disjUnionComponentEquiv G H))
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  have hmap : ∀ f : (G ⊕g H).toSimple.ConnectedComponent → IsoGraph,
      (Finset.univ : Finset (G ⊕g H).toSimple.ConnectedComponent).val.map f
        = (Finset.univ : Finset (G.toSimple.ConnectedComponent
            ⊕ H.toSimple.ConnectedComponent)).val.map
          (fun s ↦ f ((disjUnionComponentEquiv G H).symm s)) := by
    intro f
    rw [← huniv, Multiset.map_map]
    exact Multiset.map_congr rfl fun c _ ↦ by
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [comps, hmap]
  rw [show (Finset.univ : Finset (G.toSimple.ConnectedComponent
      ⊕ H.toSimple.ConnectedComponent)).val
      = (Finset.univ : Finset G.toSimple.ConnectedComponent).val.map Sum.inl
        + (Finset.univ : Finset H.toSimple.ConnectedComponent).val.map Sum.inr from rfl]
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · exact Multiset.map_congr rfl fun c _ ↦ Quotient.sound ⟨(componentDisjUnionInl G H c).symm⟩
  · exact Multiset.map_congr rfl fun c _ ↦ Quotient.sound ⟨(componentDisjUnionInr G H c).symm⟩

end CGraph

/-! ## The operations, as data

One `Zero`, one `One`, an `Add` for each sum and a `Mul` for each product.  They are definitions
rather than instances: the scopes below are what turn them on, and they turn on *these*, so any
two scopes agree wherever they overlap. -/

namespace IsoGraph

/-- Zero is the graph on no vertices, for both sums and all four products. -/
def instZero : Zero IsoGraph := ⟨empty 0⟩

/-- One is the graph on a single vertex. -/
def instOne : One IsoGraph := ⟨empty 1⟩

/-- Addition as the disjoint union. -/
def instAddDisjUnion : Add IsoGraph := ⟨disjUnion⟩

/-- Addition as the join. -/
def instAddJoin : Add IsoGraph := ⟨join⟩

/-- Multiplication as the cartesian product. -/
def instMulCartesianProduct : Mul IsoGraph := ⟨cartesianProduct⟩

/-- Multiplication as the tensor product. -/
def instMulTensorProduct : Mul IsoGraph := ⟨tensorProduct⟩

/-- Multiplication as the strong product. -/
def instMulStrongProduct : Mul IsoGraph := ⟨strongProduct⟩

/-- Multiplication as the lexicographic product. -/
def instMulLexProduct : Mul IsoGraph := ⟨lexProduct⟩

section

attribute [local instance] instZero instAddDisjUnion

/-- The disjoint union is a commutative monoid with the empty graph for unit.  This is the
auxiliary version, used to state the component decomposition that proves cancellation; the scoped
instance is the `AddCancelCommMonoid` of the next section. -/
def addCommMonoidDisjUnionAux : AddCommMonoid IsoGraph where
  add_assoc := disjUnion_assoc
  zero_add := empty_zero_disjUnion
  add_zero := disjUnion_empty_zero
  add_comm := disjUnion_comm
  nsmul := nsmulRec

end

end IsoGraph

/-! ## Both sums are cancellative

A graph is the sum, over the disjoint union, of its connected components; the multiset of those
components is additive; and multisets cancel.  The join then cancels because complementation
exchanges it with the disjoint union. -/

section Cancellation

open IsoGraph

attribute [local instance] IsoGraph.instZero IsoGraph.instAddDisjUnion
  IsoGraph.addCommMonoidDisjUnionAux

namespace CGraph

/-- A union of components is the sum of those components. -/
theorem quot_part (G : CGraph) (S : Finset G.toSimple.ConnectedComponent) :
    (⟦G.part S⟧ : IsoGraph) = (∑ c ∈ S, ⟦G.component c⟧ : IsoGraph) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Quotient.sound (s := isoSetoid) ⟨G.partEmpty⟩]
    rfl
  | insert c S hc ih =>
    rw [Finset.sum_insert hc, ← ih, Quotient.sound (s := isoSetoid) ⟨G.partInsert c S hc⟩]
    rfl

/-- **A graph is the sum of its connected components.** -/
theorem sum_comps (G : CGraph) : G.comps.sum = (⟦G⟧ : IsoGraph) := by
  have h : (⟦G.part Finset.univ⟧ : IsoGraph) = ⟦G⟧ := Quotient.sound ⟨G.partUniv⟩
  rw [← h, quot_part]
  rfl

end CGraph

namespace IsoGraph

/-- **A graph is the sum of its connected components.** -/
@[simp] theorem sum_comps (a : IsoGraph) : a.comps.sum = a := by
  induction a using Quotient.ind with
  | _ G => rw [comps_mk]; exact CGraph.sum_comps G

end IsoGraph

/-- **The disjoint union is cancellative**: two graphs with a common summand and the same union
have the same components, hence are isomorphic. -/
theorem IsoGraph.disjUnion_left_cancel {a b c : IsoGraph} (h : a ⊕g b = a ⊕g c) : b = c := by
  have hc : a.comps + b.comps = a.comps + c.comps := by
    rw [← comps_disjUnion, ← comps_disjUnion, h]
  rw [← sum_comps b, ← sum_comps c, add_left_cancel hc]

/-- **The join is cancellative**, being the disjoint union of the complements. -/
theorem IsoGraph.join_left_cancel {a b c : IsoGraph} (h : a ∇g b = a ∇g c) : b = c := by
  have h2 : aᶜ ⊕g bᶜ = aᶜ ⊕g cᶜ := by
    have h3 := congrArg (fun x : IsoGraph ↦ xᶜ) h
    simpa only [join, compl_compl] using h3
  have h4 := IsoGraph.disjUnion_left_cancel h2
  rw [← compl_compl b, h4, compl_compl]

end Cancellation

/-! ## The bundled structures

Each of these is built under the data instances it needs, made `local` for the duration; every
field is one of the identities proved in `Identities/Identifications.lean` or
`Graphs/Quotient.lean`.  They are still definitions, not instances — the scopes come next. -/

namespace IsoGraph

section DisjUnionData

attribute [local instance] instZero instAddDisjUnion

/-- **The disjoint union is a cancellative commutative monoid.** -/
def addCancelCommMonoidDisjUnion : AddCancelCommMonoid IsoGraph where
  __ := addCommMonoidDisjUnionAux
  add_left_cancel _ _ _ h := disjUnion_left_cancel h

/-- Both cancellation laws for the disjoint union, without the monoid structure. -/
def isCancelAddDisjUnion : @IsCancelAdd IsoGraph instAddDisjUnion where
  add_left_cancel _ _ _ h := disjUnion_left_cancel h
  add_right_cancel a b c h := disjUnion_left_cancel
    (a := a) (by rw [disjUnion_comm a b, disjUnion_comm a c]; exact h)

end DisjUnionData

section JoinData

attribute [local instance] instZero instAddJoin

/-- **The join is a cancellative commutative monoid**, again with the empty graph for unit. -/
def addCancelCommMonoidJoin : AddCancelCommMonoid IsoGraph where
  add_assoc := join_assoc
  zero_add := empty_zero_join
  add_zero := join_empty_zero
  add_comm := join_comm
  nsmul := nsmulRec
  add_left_cancel _ _ _ h := join_left_cancel h

/-- Both cancellation laws for the join, without the monoid structure. -/
def isCancelAddJoin : @IsCancelAdd IsoGraph instAddJoin where
  add_left_cancel _ _ _ h := join_left_cancel h
  add_right_cancel a b c h := join_left_cancel
    (a := a) (by rw [join_comm a b, join_comm a c]; exact h)

end JoinData

/-- A product with no vertices has a factor with no vertices. -/
private theorem eq_zero_or_eq_zero_of_V_mul {a b c : IsoGraph} (hV : c.V = a.V * b.V)
    (h : c = empty 0) : a = empty 0 ∨ b = empty 0 := by
  rw [h, V_empty] at hV
  exact (Nat.mul_eq_zero.1 hV.symm).imp V_eq_zero_iff.1 V_eq_zero_iff.1

section CartesianData

attribute [local instance] instZero instOne instMulCartesianProduct

/-- **The cartesian product is a commutative monoid** with the one-vertex graph for unit, and the
empty graph annihilates it. -/
def commMonoidWithZeroCartesianProduct : CommMonoidWithZero IsoGraph where
  mul_assoc := cartesianProduct_assoc
  one_mul := empty_one_cartesianProduct
  mul_one := cartesianProduct_empty_one
  mul_comm := cartesianProduct_comm
  zero_mul := empty_zero_cartesianProduct
  mul_zero := cartesianProduct_empty_zero
  npow := npowRec

/-- A cartesian product is empty only if a factor is. -/
def noZeroDivisorsCartesianProduct : NoZeroDivisors IsoGraph where
  eq_zero_or_eq_zero_of_mul_eq_zero h := eq_zero_or_eq_zero_of_V_mul (V_cartesianProduct _ _) h

end CartesianData

section TensorData

attribute [local instance] instZero instMulTensorProduct

/-- **The tensor product is a semigroup** annihilated by the empty graph.  It has no unit: the
would-be unit is a single vertex with a loop, and `CGraph`s are loopless. -/
def semigroupWithZeroTensorProduct : SemigroupWithZero IsoGraph where
  mul_assoc := tensorProduct_assoc
  zero_mul := empty_zero_tensorProduct
  mul_zero := tensorProduct_empty_zero

/-- The tensor product is commutative. -/
def commMagmaTensorProduct : CommMagma IsoGraph where
  mul_comm := tensorProduct_comm

/-- A tensor product is empty only if a factor is. -/
def noZeroDivisorsTensorProduct : NoZeroDivisors IsoGraph where
  eq_zero_or_eq_zero_of_mul_eq_zero h := eq_zero_or_eq_zero_of_V_mul (V_tensorProduct _ _) h

end TensorData

section StrongData

attribute [local instance] instZero instOne instMulStrongProduct

/-- **The strong product is a commutative monoid** with the same unit and zero as the cartesian
one. -/
def commMonoidWithZeroStrongProduct : CommMonoidWithZero IsoGraph where
  mul_assoc := strongProduct_assoc
  one_mul := empty_one_strongProduct
  mul_one := strongProduct_empty_one
  mul_comm := strongProduct_comm
  zero_mul := empty_zero_strongProduct
  mul_zero := strongProduct_empty_zero
  npow := npowRec

/-- A strong product is empty only if a factor is. -/
def noZeroDivisorsStrongProduct : NoZeroDivisors IsoGraph where
  eq_zero_or_eq_zero_of_mul_eq_zero h := eq_zero_or_eq_zero_of_V_mul (V_strongProduct _ _) h

end StrongData

section LexData

attribute [local instance] instZero instOne instMulLexProduct

/-- **The lexicographic product is a monoid** with the same unit and zero as the other products.
It is not commutative: `empty 2 ·g complete 2` is two disjoint edges and `complete 2 ·g empty 2` is
the four-cycle. -/
def monoidWithZeroLexProduct : MonoidWithZero IsoGraph where
  mul_assoc := lexProduct_assoc
  one_mul := empty_one_lexProduct
  mul_one := lexProduct_empty_one
  zero_mul := empty_zero_lexProduct
  mul_zero := lexProduct_empty_zero
  npow := npowRec

/-- A lexicographic product is empty only if a factor is. -/
def noZeroDivisorsLexProduct : NoZeroDivisors IsoGraph where
  eq_zero_or_eq_zero_of_mul_eq_zero h := eq_zero_or_eq_zero_of_V_mul (V_lexProduct _ _) h

end LexData

/-! ## The scopes

The single-operation scopes first, then the five pairs that distribute.  Each of them exports the
`rfl` lemmas identifying `+`, `*`, `0` and `1` with the graph constructions, so a proof can drop
back down to the notation of the rest of the library at any point. -/

namespace DisjUnion

attribute [scoped instance] instZero instAddDisjUnion addCancelCommMonoidDisjUnion

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ⊕g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl

end DisjUnion

namespace Join

attribute [scoped instance] instZero instAddJoin addCancelCommMonoidJoin

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ∇g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl

end Join

namespace CartesianProduct

attribute [scoped instance] instZero instOne instMulCartesianProduct
  commMonoidWithZeroCartesianProduct noZeroDivisorsCartesianProduct

@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G □g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

end CartesianProduct

namespace TensorProduct

attribute [scoped instance] instZero instMulTensorProduct semigroupWithZeroTensorProduct
  commMagmaTensorProduct noZeroDivisorsTensorProduct

@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ⊗g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl

end TensorProduct

namespace StrongProduct

attribute [scoped instance] instZero instOne instMulStrongProduct
  commMonoidWithZeroStrongProduct noZeroDivisorsStrongProduct

@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ⊠g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

end StrongProduct

namespace LexProduct

attribute [scoped instance] instZero instOne instMulLexProduct monoidWithZeroLexProduct
  noZeroDivisorsLexProduct

@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ·g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

end LexProduct

/-! ### The disjoint union and the cartesian product -/

namespace Semiring

attribute [scoped instance] instZero instOne instAddDisjUnion instMulCartesianProduct
  isCancelAddDisjUnion noZeroDivisorsCartesianProduct

/-- **The graphs form a commutative semiring** under the disjoint union and the cartesian product,
with the graph on no vertices for zero and the graph on one vertex for one.  The four operations
are the definitions above, so `+` and `*` are the graph constructions themselves and not a copy of
them: `add_eq` and `mul_eq` hold by `rfl`.  After `open scoped IsoGraph.Semiring`, `ring` proves
identities like `(G ⊕g H) □g (G ⊕g H) = G □g G ⊕g empty 2 □g (G □g H) ⊕g H □g H`. -/
scoped instance instCommSemiring : CommSemiring IsoGraph where
  __ := addCommMonoidDisjUnionAux
  __ := commMonoidWithZeroCartesianProduct
  left_distrib := cartesianProduct_disjUnion
  right_distrib := disjUnion_cartesianProduct
  zero_mul := empty_zero_cartesianProduct
  mul_zero := cartesianProduct_empty_zero

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ⊕g H := rfl
@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G □g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

/-- The numeral `n` is the graph on `n` vertices with no edges. -/
@[scoped simp] theorem natCast_eq (n : ℕ) : (n : IsoGraph) = empty n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, ih]
    exact disjUnion_empty n 1

/-- The literal `n` is the graph on `n` vertices with no edges. -/
@[scoped simp] theorem ofNat_eq (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : IsoGraph) = empty (OfNat.ofNat n) := by
  rw [← Nat.cast_ofNat (n := n), natCast_eq]

/-- **The order of a graph is a semiring homomorphism** to `ℕ`: the disjoint union adds vertex
counts and the cartesian product multiplies them. -/
def VHom : IsoGraph →+* ℕ where
  toFun G := G.V
  map_one' := V_empty 1
  map_mul' := V_cartesianProduct
  map_zero' := V_empty 0
  map_add' := V_disjUnion

@[scoped simp] theorem coe_VHom : ⇑VHom = IsoGraph.V := rfl

end Semiring

/-! ### The disjoint union and the strong product -/

namespace StrongSemiring

attribute [scoped instance] instZero instOne instAddDisjUnion instMulStrongProduct
  isCancelAddDisjUnion noZeroDivisorsStrongProduct

/-- **The graphs form a commutative semiring** under the disjoint union and the strong product,
with the same zero and one as under the cartesian product. -/
scoped instance instCommSemiring : CommSemiring IsoGraph where
  __ := addCommMonoidDisjUnionAux
  __ := commMonoidWithZeroStrongProduct
  left_distrib := strongProduct_disjUnion
  right_distrib := disjUnion_strongProduct
  zero_mul := empty_zero_strongProduct
  mul_zero := strongProduct_empty_zero

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ⊕g H := rfl
@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ⊠g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

/-- The numeral `n` is the graph on `n` vertices with no edges. -/
@[scoped simp] theorem natCast_eq (n : ℕ) : (n : IsoGraph) = empty n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, ih]
    exact disjUnion_empty n 1

/-- **The order of a graph is a semiring homomorphism** to `ℕ` for the strong product too. -/
def VHom : IsoGraph →+* ℕ where
  toFun G := G.V
  map_one' := V_empty 1
  map_mul' := V_strongProduct
  map_zero' := V_empty 0
  map_add' := V_disjUnion

@[scoped simp] theorem coe_VHom : ⇑VHom = IsoGraph.V := rfl

end StrongSemiring

/-! ### The disjoint union and the tensor product -/

namespace TensorSemiring

attribute [scoped instance] instZero instAddDisjUnion instMulTensorProduct
  isCancelAddDisjUnion noZeroDivisorsTensorProduct

/-- **The graphs form a non-unital commutative semiring** under the disjoint union and the tensor
product.  Only the unit is missing; everything else — associativity, commutativity, both
distributive laws and the annihilating zero — holds. -/
scoped instance instNonUnitalCommSemiring : NonUnitalCommSemiring IsoGraph where
  __ := addCommMonoidDisjUnionAux
  __ := semigroupWithZeroTensorProduct
  mul_comm := tensorProduct_comm
  left_distrib := tensorProduct_disjUnion
  right_distrib := disjUnion_tensorProduct

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ⊕g H := rfl
@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ⊗g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl

end TensorSemiring

/-! ### The lexicographic product, over both sums -/

namespace LexSemiring

attribute [scoped instance] instZero instOne instAddDisjUnion instMulLexProduct
  addCancelCommMonoidDisjUnion monoidWithZeroLexProduct noZeroDivisorsLexProduct

/-- **The lexicographic product distributes over the disjoint union in its first factor**, and
only there: the second factor is the inner one, and `G ·g (H ⊕g K)` keeps `G`'s edges between the
copy of `H` and the copy of `K`. -/
scoped instance instRightDistribClass : RightDistribClass IsoGraph where
  right_distrib := disjUnion_lexProduct

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ⊕g H := rfl
@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ·g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

end LexSemiring

namespace JoinLexSemiring

attribute [scoped instance] instZero instOne instAddJoin instMulLexProduct
  addCancelCommMonoidJoin monoidWithZeroLexProduct noZeroDivisorsLexProduct

/-- **The lexicographic product distributes over the join in its first factor** — the same law as
over the disjoint union, carried across by complementation. -/
scoped instance instRightDistribClass : RightDistribClass IsoGraph where
  right_distrib := join_lexProduct

@[scoped simp] theorem add_eq (G H : IsoGraph) : G + H = G ∇g H := rfl
@[scoped simp] theorem mul_eq (G H : IsoGraph) : G * H = G ·g H := rfl
@[scoped simp] theorem zero_eq : (0 : IsoGraph) = empty 0 := rfl
@[scoped simp] theorem one_eq : (1 : IsoGraph) = empty 1 := rfl

end JoinLexSemiring

end IsoGraph
