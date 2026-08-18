import IsoGraph.Containment.Minors

/-!
# The operations against the orders

`Values/Identities/Semiring.lean` gives `IsoGraph` two sums, the disjoint union `⊕g` and the join
`∇g`, and four products, the cartesian `□g`, tensor `⊗g`, strong `⊠g` and lexicographic `·g` ones.
`Containment/Defs.lean` gives it nine containment relations.  This file asks, for each of the
fifty-four pairs, whether the operation is **monotone** in that relation: if `H` sits inside `G`
and `H'` inside `G'`, does `H op H'` sit inside `G op G'`?

| | `⊕g` | `∇g` | `□g` | `⊗g` | `⊠g` | `·g` |
| --- | --- | --- | --- | --- | --- | --- |
| `≤ₕ` homomorphism | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| `≤ₛ` subgraph | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| `≤ᵢₛ` induced subgraph | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| `≤/` quotient | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| `≤ₘ` minor | ✓ | ✓ | ✓ | ? | ✓ | ✓ |
| `≤ᵢₘ` induced minor | ✓ | ✓ | ✓ | ? | ✓ | ? |
| `≤ₚ` contraction | ✓ | ✓ | ✓ | ? | ✓ | ? |
| `≤ₜₘ` topological minor | ✓ | ✓ | ✓ | ? | ? | ? |
| `≤ₑ` immersion | ✓ | ✓ | ✓ | ? | ? | ? |

Each `✓` is a theorem here, at both levels: a construction on the `CGraph` models, which is what a
search would have to output, and the statement about `IsoGraph` that it lifts to, e.g.
`IsSubgraphOf.disjUnion : H ≤ₛ G → H' ≤ₛ G' → H ⊕g H' ≤ₛ G ⊕g G'`.  The lifting is one lemma,
`IsoGraph.mono₂`, applied to the `_mk` bridge of the relation and the `_mk` bridge of the
operation; the work is all on `CGraph`.

The first four relations are maps of vertices with a condition on each edge, so all six operations
carry them: the map is `Sum.map` or `Prod.map`, and the adjacency conditions are the twelve
`*_map_adj` and `*_adj_map` lemmas at the top of the file.  The minor relations are harder, since
a branch set of the product has to stay connected: `connectedOn_prod` says that a product of
connected sets is connected in any graph that has the edges of the cartesian product, which covers
`□g`, `⊠g` and `·g` but *not* `⊗g` — the tensor product of two connected graphs is disconnected
when both are bipartite.  Whether the tensor product is monotone in the minor orders by some other
model is left open, as is the lexicographic product for the two *induced* minor relations, where
the obstruction is different: an edge inside a branch set of the first factor is an edge of the
lexicographic product whatever the second coordinates do, and nothing makes it induced.  The last
two relations replace an edge by a path or a trail, and get the two sums and the cartesian
product: an edge inside a summand keeps that summand's walk, an edge across a join is an edge of
the join of the hosts, and an edge of `□g` moves one coordinate and so takes that factor's walk
along one row or one column of the product.  Over the other three products they are left open,
because there an edge of one factor can be replaced by a walk that moves both coordinates, and two
such walks would have to be kept apart by hand.
-/

set_option autoImplicit false

namespace CGraph

variable {A B A' B' : CGraph}

/-! ## Transport of adjacency along the operations -/

theorem disjUnion_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A ⊕g A').Adj x y → (B ⊕g B').Adj (Sum.map f f' x) (Sum.map f f' y) := by
  rintro (a | b) (c | d) h
  · simpa using hf _ _ (by simpa using h)
  · simp at h
  · simp at h
  · simpa using hf' _ _ (by simpa using h)

theorem disjUnion_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B ⊕g B').Adj (Sum.map f f' x) (Sum.map f f' y) → (A ⊕g A').Adj x y := by
  rintro (a | b) (c | d) h
  · simpa using hf _ _ (by simpa using h)
  · simp at h
  · simp at h
  · simpa using hf' _ _ (by simpa using h)

theorem join_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A ∇g A').Adj x y → (B ∇g B').Adj (Sum.map f f' x) (Sum.map f f' y) := by
  rintro (a | b) (c | d) h
  · simpa using hf _ _ (by simpa using h)
  · simp
  · simp
  · simpa using hf' _ _ (by simpa using h)

theorem join_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B ∇g B').Adj (Sum.map f f' x) (Sum.map f f' y) → (A ∇g A').Adj x y := by
  rintro (a | b) (c | d) h
  · show (A ∇g A').Adj (Sum.inl (a : A.V)) (Sum.inl (c : A.V))
    simpa using hf _ _ (by simpa using h)
  · show (A ∇g A').Adj (Sum.inl (a : A.V)) (Sum.inr (d : A'.V))
    simp
  · show (A ∇g A').Adj (Sum.inr (b : A'.V)) (Sum.inl (c : A.V))
    simp
  · show (A ∇g A').Adj (Sum.inr (b : A'.V)) (Sum.inr (d : A'.V))
    simpa using hf' _ _ (by simpa using h)

theorem cartesianProduct_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A □g A').Adj x y → (B □g B').Adj (Prod.map f f' x) (Prod.map f f' y) := by
  intro x y h
  simp only [cartesianProduct_adj, Prod.map_fst, Prod.map_snd, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨congrArg f h₁, hf' _ _ h₂⟩
  · exact Or.inr ⟨hf _ _ h₁, congrArg f' h₂⟩

theorem cartesianProduct_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hinj : Function.Injective f) (hinj' : Function.Injective f')
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B □g B').Adj (Prod.map f f' x) (Prod.map f f' y) → (A □g A').Adj x y := by
  intro x y h
  simp only [cartesianProduct_adj, Prod.map_fst, Prod.map_snd, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨hinj h₁, hf' _ _ h₂⟩
  · exact Or.inr ⟨hf _ _ h₁, hinj' h₂⟩

theorem tensorProduct_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A ⊗g A').Adj x y → (B ⊗g B').Adj (Prod.map f f' x) (Prod.map f f' y) := by
  intro x y h
  simp only [tensorProduct_adj, Prod.map_fst, Prod.map_snd, Bool.and_eq_true] at h ⊢
  exact ⟨hf _ _ h.1, hf' _ _ h.2⟩

theorem tensorProduct_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B ⊗g B').Adj (Prod.map f f' x) (Prod.map f f' y) → (A ⊗g A').Adj x y := by
  intro x y h
  simp only [tensorProduct_adj, Prod.map_fst, Prod.map_snd, Bool.and_eq_true] at h ⊢
  exact ⟨hf _ _ h.1, hf' _ _ h.2⟩

theorem strongProduct_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A ⊠g A').Adj x y → (B ⊠g B').Adj (Prod.map f f' x) (Prod.map f f' y) := by
  intro x y h
  simp only [strongProduct_adj, Prod.map_fst, Prod.map_snd, ne_eq, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h ⊢
  obtain ⟨hne, h₁, h₂⟩ := h
  refine ⟨fun e ↦ hne ?_, h₁.imp (congrArg f) (hf _ _), h₂.imp (congrArg f') (hf' _ _)⟩
  -- distinct vertices stay distinct: the two differ in some coordinate, and there a collapsed
  -- pair cannot have been an edge, since `B` is loopless
  have e₁ : f x.1 = f y.1 := by simpa using congrArg Prod.fst e
  have e₂ : f' x.2 = f' y.2 := by simpa using congrArg Prod.snd e
  have c₁ : x.1 = y.1 := by
    rcases h₁ with h₁ | h₁
    · exact h₁
    · have hb := hf _ _ h₁
      rw [e₁] at hb
      simp [B.loopless] at hb
  have c₂ : x.2 = y.2 := by
    rcases h₂ with h₂ | h₂
    · exact h₂
    · have hb := hf' _ _ h₂
      rw [e₂] at hb
      simp [B'.loopless] at hb
  exact Prod.ext c₁ c₂

theorem strongProduct_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hinj : Function.Injective f) (hinj' : Function.Injective f')
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B ⊠g B').Adj (Prod.map f f' x) (Prod.map f f' y) → (A ⊠g A').Adj x y := by
  intro x y h
  simp only [strongProduct_adj, Prod.map_fst, Prod.map_snd, ne_eq, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h ⊢
  obtain ⟨hne, h₁, h₂⟩ := h
  exact ⟨fun e ↦ hne (by rw [e]), h₁.imp (fun e ↦ hinj e) (hf _ _),
    h₂.imp (fun e ↦ hinj' e) (hf' _ _)⟩

theorem lexProduct_map_adj {f : A.V → B.V} {f' : A'.V → B'.V}
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y))
    (hf' : ∀ x y, A'.Adj x y → B'.Adj (f' x) (f' y)) :
    ∀ x y, (A ·g A').Adj x y → (B ·g B').Adj (Prod.map f f' x) (Prod.map f f' y) := by
  intro x y h
  simp only [lexProduct_adj, Prod.map_fst, Prod.map_snd, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact h.imp (hf _ _) fun h ↦ ⟨congrArg f h.1, hf' _ _ h.2⟩

theorem lexProduct_adj_map {f : A.V → B.V} {f' : A'.V → B'.V}
    (hinj : Function.Injective f)
    (hf : ∀ x y, B.Adj (f x) (f y) → A.Adj x y)
    (hf' : ∀ x y, B'.Adj (f' x) (f' y) → A'.Adj x y) :
    ∀ x y, (B ·g B').Adj (Prod.map f f' x) (Prod.map f f' y) → (A ·g A').Adj x y := by
  intro x y h
  simp only [lexProduct_adj, Prod.map_fst, Prod.map_snd, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  exact h.imp (hf _ _) fun h ↦ ⟨hinj h.1, hf' _ _ h.2⟩

/-- Injectivity of `Sum.inl` at the vertex type of a `join`, as `disjUnion_inl_eq_inl` does it for
the disjoint union: definitional equality with `G.V ⊕ H.V` is not reducible, so `Sum.inl.injEq`
does not fire here either. -/
theorem join_inl_eq_inl (G H : CGraph) (a b : G.V) :
    (@Eq (G ∇g H).V (Sum.inl a) (Sum.inl b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inl_injective h, fun h ↦ h ▸ rfl⟩

/-- Injectivity of `Sum.inr` at the vertex type of a `join`; see `join_inl_eq_inl`. -/
theorem join_inr_eq_inr (G H : CGraph) (a b : H.V) :
    (@Eq (G ∇g H).V (Sum.inr a) (Sum.inr b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inr_injective h, fun h ↦ h ▸ rfl⟩

/-! ## Connected sets travel along maps -/

def toSimpleHom_of {f : A.V → B.V} (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y)) :
    A.toSimple →g B.toSimple where
  toFun := f
  map_rel' := fun {x y} h ↦ hf x y h

theorem ConnectedOn.map {s : Set A.V} (hs : A.ConnectedOn s) (f : A.V → B.V)
    (hf : ∀ x y, A.Adj x y → B.Adj (f x) (f y)) : B.ConnectedOn (f '' s) where
  nonempty := hs.nonempty.image f
  walk := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨w, hw⟩ := hs.walk ha hb
    refine ⟨(w.map (toSimpleHom_of hf) : B.toSimple.Walk (f a) (f b)), ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨z', hw z' hz', rfl⟩

/-- `ConnectedOn.map` against a set given in some other form — which is how a branch set of a
sum or a product of two minor models arrives, its vertex type only definitionally a sum. -/
theorem ConnectedOn.image_eq {s : Set A.V} (hs : A.ConnectedOn s) (m : A.V → B.V)
    (hm : ∀ x y, A.Adj x y → B.Adj (m x) (m y)) {t : Set B.V} (ht : t = m '' s) :
    B.ConnectedOn t :=
  ht ▸ hs.map m hm

/-- **A product of connected sets is connected**, in any graph that has the edges of the
cartesian product: walk along a row, then along a column.  `m` is the identity in every use, and
is there only because the vertex type of a product graph is a product of vertex types
definitionally rather than syntactically. -/
theorem connectedOn_prod {C : CGraph} (m : B.V × B'.V → C.V)
    (hrow : ∀ (u : B.V) (v v' : B'.V), B'.Adj v v' → C.Adj (m (u, v)) (m (u, v')))
    (hcol : ∀ (u u' : B.V) (v : B'.V), B.Adj u u' → C.Adj (m (u, v)) (m (u', v)))
    {s : Set B.V} {t : Set B'.V} (hs : B.ConnectedOn s) (ht : B'.ConnectedOn t)
    {r : Set C.V} (hr : r = m '' (s ×ˢ t)) : C.ConnectedOn r := by
  have himg : m '' (s ×ˢ t) = ⋃ u ∈ s, (fun v ↦ m (u, v)) '' t := by
    ext z
    simp only [Set.mem_image, Set.mem_prod, Set.mem_iUnion, Prod.exists]
    exact ⟨fun ⟨u, v, ⟨hu, hv⟩, hz⟩ ↦ ⟨u, hu, v, hv, hz⟩,
      fun ⟨u, hu, v, hv, hz⟩ ↦ ⟨u, v, ⟨hu, hv⟩, hz⟩⟩
  rw [hr, himg]
  refine connectedOn_biUnion hs (fun u _ ↦ ht.map _ (fun a c h ↦ hrow u a c h)) ?_
  intro k hk k' hk' hadj
  obtain ⟨v, hv⟩ := ht.nonempty
  exact ⟨m (k, v), ⟨v, hv, rfl⟩, m (k', v), ⟨v, hv, rfl⟩, hcol k k' v hadj⟩

/-! ## The minor family, on the two sums -/

namespace MinorOf

/-- The branch map of a sum of two minor models: contract in each summand separately.  The type is
the bare `B.V ⊕ B'.V`, which is the vertex type of both `B ⊕g B'` and `B ∇g B'` — definitionally,
which is enough for the two constructors below to use it and *not* enough for `simp`, so the two
lemmas after it are stated at the bare type too and used with `exact`. -/
def sumBranch (f : A.MinorOf B) (f' : A'.MinorOf B') : B.V ⊕ B'.V → Option (A.V ⊕ A'.V) :=
  Sum.elim (fun u ↦ (f.branch u).map Sum.inl) (fun u ↦ (f'.branch u).map Sum.inr)

theorem setOf_sumBranch_inl (f : A.MinorOf B) (f' : A'.MinorOf B') (x : A.V) :
    {v : B.V ⊕ B'.V | sumBranch f f' v = some (Sum.inl x)}
      = Sum.inl '' {v | f.branch v = some x} := by
  ext (v | v) <;> simp [sumBranch, Option.map_eq_some_iff]

theorem setOf_sumBranch_inr (f : A.MinorOf B) (f' : A'.MinorOf B') (x : A'.V) :
    {v : B.V ⊕ B'.V | sumBranch f f' v = some (Sum.inr x)}
      = Sum.inr '' {v | f'.branch v = some x} := by
  ext (v | v) <;> simp [sumBranch, Option.map_eq_some_iff]

theorem sumBranch_inl (f : A.MinorOf B) (f' : A'.MinorOf B') {u : B.V} {x : A.V}
    (h : f.branch u = some x) : sumBranch f f' (Sum.inl u) = some (Sum.inl x) := by
  simp [sumBranch, h]

theorem sumBranch_inr (f : A.MinorOf B) (f' : A'.MinorOf B') {u : B'.V} {x : A'.V}
    (h : f'.branch u = some x) : sumBranch f f' (Sum.inr u) = some (Sum.inr x) := by
  simp [sumBranch, h]

theorem sumBranch_eq_inl (f : A.MinorOf B) (f' : A'.MinorOf B') {u : B.V ⊕ B'.V} {x : A.V}
    (h : sumBranch f f' u = some (Sum.inl x)) : ∃ w, u = Sum.inl w ∧ f.branch w = some x := by
  rcases u with w | w
  · exact ⟨w, rfl, by simpa [sumBranch, Option.map_eq_some_iff] using h⟩
  · simp [sumBranch, Option.map_eq_some_iff] at h

theorem sumBranch_eq_inr (f : A.MinorOf B) (f' : A'.MinorOf B') {u : B.V ⊕ B'.V} {x : A'.V}
    (h : sumBranch f f' u = some (Sum.inr x)) : ∃ w, u = Sum.inr w ∧ f'.branch w = some x := by
  rcases u with w | w
  · simp [sumBranch, Option.map_eq_some_iff] at h
  · exact ⟨w, rfl, by simpa [sumBranch, Option.map_eq_some_iff] using h⟩

theorem sumBranch_isSome (f : A.MinorOf B) (f' : A'.MinorOf B')
    (h : ∀ u, (f.branch u).isSome) (h' : ∀ u, (f'.branch u).isSome) (u : B.V ⊕ B'.V) :
    (sumBranch f f' u).isSome := by
  rcases u with w | w
  · rcases hb : f.branch w with _ | y
    · exact absurd (h w) (by simp [hb])
    · simp [sumBranch, hb]
  · rcases hb : f'.branch w with _ | y
    · exact absurd (h' w) (by simp [hb])
    · simp [sumBranch, hb]

/-- **The disjoint union of two minor models.**  Contract each summand into its own, and no edge
of the union ever runs between them. -/
def disjUnion (f : A.MinorOf B) (f' : A'.MinorOf B') : (A ⊕g A').MinorOf (B ⊕g B') where
  branch := sumBranch (A := A) (B := B) (A' := A') (B' := B') f f'
  connectedOn' := by
    rintro (x | x)
    · refine (f.connectedOn x).image_eq (Sum.inl : B.V → (B ⊕g B').V)
        (fun a c h ↦ by simpa using h) ?_
      exact setOf_sumBranch_inl f f' x
    · refine (f'.connectedOn x).image_eq (Sum.inr : B'.V → (B ⊕g B').V)
        (fun a c h ↦ by simpa using h) ?_
      exact setOf_sumBranch_inr f f' x
  map_adj' := by
    rintro (x | x) (y | y) h
    · obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj (by simpa using h)
      exact ⟨Sum.inl u, Sum.inl v, sumBranch_inl f f' hu, sumBranch_inl f f' hv,
        by simpa using huv⟩
    · simp at h
    · simp at h
    · obtain ⟨u, v, hu, hv, huv⟩ := f'.map_adj (by simpa using h)
      exact ⟨Sum.inr u, Sum.inr v, sumBranch_inr f f' hu, sumBranch_inr f f' hv,
        by simpa using huv⟩

/-- **The join of two minor models.**  The same branch map as the disjoint union: the join only
adds edges, which can only help a branch set stay connected, and every edge across is realised by
any pair of branch vertices. -/
def join (f : A.MinorOf B) (f' : A'.MinorOf B') : (A ∇g A').MinorOf (B ∇g B') where
  branch := sumBranch (A := A) (B := B) (A' := A') (B' := B') f f'
  connectedOn' := by
    rintro (x | x)
    · refine (f.connectedOn x).image_eq (Sum.inl : B.V → (B ∇g B').V) (fun a c h ↦ ?_) ?_
      · show (B ∇g B').Adj (Sum.inl (a : B.V)) (Sum.inl (c : B.V))
        simpa using h
      · exact setOf_sumBranch_inl f f' x
    · refine (f'.connectedOn x).image_eq (Sum.inr : B'.V → (B ∇g B').V) (fun a c h ↦ ?_) ?_
      · show (B ∇g B').Adj (Sum.inr (a : B'.V)) (Sum.inr (c : B'.V))
        simpa using h
      · exact setOf_sumBranch_inr f f' x
  map_adj' := by
    rintro (x | x) (y | y) h
    · obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj (by simpa using h)
      refine ⟨Sum.inl u, Sum.inl v, sumBranch_inl f f' hu, sumBranch_inl f f' hv, ?_⟩
      show (B ∇g B').Adj (Sum.inl (u : B.V)) (Sum.inl (v : B.V))
      simpa using huv
    · obtain ⟨u, hu⟩ := (f.connectedOn x).nonempty
      obtain ⟨v, hv⟩ := (f'.connectedOn y).nonempty
      refine ⟨Sum.inl u, Sum.inr v, sumBranch_inl f f' hu, sumBranch_inr f f' hv, ?_⟩
      show (B ∇g B').Adj (Sum.inl (u : B.V)) (Sum.inr (v : B'.V))
      simp
    · obtain ⟨u, hu⟩ := (f'.connectedOn x).nonempty
      obtain ⟨v, hv⟩ := (f.connectedOn y).nonempty
      refine ⟨Sum.inr u, Sum.inl v, sumBranch_inr f f' hu, sumBranch_inl f f' hv, ?_⟩
      show (B ∇g B').Adj (Sum.inr (u : B'.V)) (Sum.inl (v : B.V))
      simp
    · obtain ⟨u, v, hu, hv, huv⟩ := f'.map_adj (by simpa using h)
      refine ⟨Sum.inr u, Sum.inr v, sumBranch_inr f f' hu, sumBranch_inr f f' hv, ?_⟩
      show (B ∇g B').Adj (Sum.inr (u : B'.V)) (Sum.inr (v : B'.V))
      simpa using huv


/-! ### Products -/

/-- The branch map of a product of two minor models: contract in each coordinate, keeping a vertex
only when both of its coordinates survive. -/
def prodBranch (f : A.MinorOf B) (f' : A'.MinorOf B') : B.V × B'.V → Option (A.V × A'.V) :=
  fun p ↦ (f.branch p.1).bind fun x ↦ (f'.branch p.2).map fun y ↦ (x, y)

theorem prodBranch_eq_some (f : A.MinorOf B) (f' : A'.MinorOf B')
    {p : B.V × B'.V} {q : A.V × A'.V} :
    prodBranch f f' p = some q ↔ f.branch p.1 = some q.1 ∧ f'.branch p.2 = some q.2 := by
  obtain ⟨u, v⟩ := p
  obtain ⟨x, y⟩ := q
  simp only [prodBranch, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨x, ha, y, hb, rfl, rfl⟩

theorem setOf_prodBranch (f : A.MinorOf B) (f' : A'.MinorOf B') (x : A.V) (y : A'.V) :
    {p : B.V × B'.V | prodBranch f f' p = some (x, y)}
      = (fun p ↦ p) '' ({u | f.branch u = some x} ×ˢ {v | f'.branch v = some y}) := by
  ext ⟨u, v⟩
  simp only [Set.mem_setOf_eq, prodBranch_eq_some, Set.image_id', Set.mem_prod]

theorem prodBranch_isSome (f : A.MinorOf B) (f' : A'.MinorOf B')
    (h : ∀ u, (f.branch u).isSome) (h' : ∀ u, (f'.branch u).isSome) (p : B.V × B'.V) :
    (prodBranch f f' p).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h p.1)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h' p.2)
  rw [(prodBranch_eq_some f f' (q := (x, y))).mpr ⟨hx, hy⟩]
  rfl

/-- **The cartesian product of two minor models.**  A branch set is a product of branch sets,
which is connected because a product of connected sets is, and an edge of the product pattern
moves in one coordinate only, so one edge between branch sets realises it. -/
def cartesianProduct (f : A.MinorOf B) (f' : A'.MinorOf B') : (A □g A').MinorOf (B □g B') where
  branch := prodBranch (A := A) (B := B) (A' := A') (B' := B') f f'
  connectedOn' := by
    rintro ⟨x, y⟩
    refine connectedOn_prod (C := B □g B') (fun p ↦ p) (fun u v v' h ↦ ?_) (fun u u' v h ↦ ?_)
      (f.connectedOn x) (f'.connectedOn y) ?_
    · simp [cartesianProduct_adj, h]
    · simp [cartesianProduct_adj, h]
    · exact setOf_prodBranch f f' x y
  map_adj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, h⟩ | ⟨h, rfl⟩
    · obtain ⟨v, v', hv, hv', hvv⟩ := f'.map_adj h
      obtain ⟨u, hu⟩ := (f.connectedOn x).nonempty
      exact ⟨(u, v), (u, v'), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
        (prodBranch_eq_some f f').mpr ⟨hu, hv'⟩, by simp [cartesianProduct_adj, hvv]⟩
    · obtain ⟨u, u', hu, hu', huu⟩ := f.map_adj h
      obtain ⟨v, hv⟩ := (f'.connectedOn y).nonempty
      exact ⟨(u, v), (u', v), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
        (prodBranch_eq_some f f').mpr ⟨hu', hv⟩, by simp [cartesianProduct_adj, huu]⟩

/-- **The strong product of two minor models.**  The strong product has all the edges of the
cartesian one, so the branch sets stay connected, and an edge that moves in both coordinates is
realised by one edge in each. -/
def strongProduct (f : A.MinorOf B) (f' : A'.MinorOf B') : (A ⊠g A').MinorOf (B ⊠g B') where
  branch := prodBranch (A := A) (B := B) (A' := A') (B' := B') f f'
  connectedOn' := by
    rintro ⟨x, y⟩
    refine connectedOn_prod (C := B ⊠g B') (fun p ↦ p) (fun u v v' h ↦ ?_) (fun u u' v h ↦ ?_)
      (f.connectedOn x) (f'.connectedOn y) ?_
    · have hne : v ≠ v' := fun e ↦ by rw [e] at h; simp [B'.loopless] at h
      simp [strongProduct_adj, h, hne, Prod.ext_iff]
    · have hne : u ≠ u' := fun e ↦ by rw [e] at h; simp [B.loopless] at h
      simp [strongProduct_adj, h, hne, Prod.ext_iff]
    · exact setOf_prodBranch f f' x y
  map_adj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [strongProduct_adj, ne_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, not_and] at h
    obtain ⟨hne, h₁, h₂⟩ := h
    rcases h₁ with rfl | h₁
    · rcases h₂ with rfl | h₂
      · exact absurd rfl (hne rfl)
      · obtain ⟨v, v', hv, hv', hvv⟩ := f'.map_adj h₂
        obtain ⟨u, hu⟩ := (f.connectedOn x).nonempty
        have hnev : v ≠ v' := fun e ↦ by rw [e] at hvv; simp [B'.loopless] at hvv
        exact ⟨(u, v), (u, v'), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
          (prodBranch_eq_some f f').mpr ⟨hu, hv'⟩,
          by simp [strongProduct_adj, hvv, hnev, Prod.ext_iff]⟩
    · obtain ⟨u, u', hu, hu', huu⟩ := f.map_adj h₁
      have hneu : u ≠ u' := fun e ↦ by rw [e] at huu; simp [B.loopless] at huu
      rcases h₂ with rfl | h₂
      · obtain ⟨v, hv⟩ := (f'.connectedOn y).nonempty
        exact ⟨(u, v), (u', v), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
          (prodBranch_eq_some f f').mpr ⟨hu', hv⟩,
          by simp [strongProduct_adj, huu, hneu, Prod.ext_iff]⟩
      · obtain ⟨v, v', hv, hv', hvv⟩ := f'.map_adj h₂
        exact ⟨(u, v), (u', v'), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
          (prodBranch_eq_some f f').mpr ⟨hu', hv'⟩,
          by simp [strongProduct_adj, huu, hvv, hneu, Prod.ext_iff]⟩

/-- **The lexicographic product of two minor models.**  An edge of the first factor joins any two
branch sets above it, and above a fixed vertex the second factor is contracted as it is. -/
def lexProduct (f : A.MinorOf B) (f' : A'.MinorOf B') : (A ·g A').MinorOf (B ·g B') where
  branch := prodBranch (A := A) (B := B) (A' := A') (B' := B') f f'
  connectedOn' := by
    rintro ⟨x, y⟩
    refine connectedOn_prod (C := B ·g B') (fun p ↦ p) (fun u v v' h ↦ ?_) (fun u u' v h ↦ ?_)
      (f.connectedOn x) (f'.connectedOn y) ?_
    · simp [lexProduct_adj, h]
    · simp [lexProduct_adj, h]
    · exact setOf_prodBranch f f' x y
  map_adj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [lexProduct_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨rfl, h⟩
    · obtain ⟨u, u', hu, hu', huu⟩ := f.map_adj h
      obtain ⟨v, hv⟩ := (f'.connectedOn y).nonempty
      obtain ⟨v', hv'⟩ := (f'.connectedOn y').nonempty
      exact ⟨(u, v), (u', v'), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
        (prodBranch_eq_some f f').mpr ⟨hu', hv'⟩, by simp [lexProduct_adj, huu]⟩
    · obtain ⟨v, v', hv, hv', hvv⟩ := f'.map_adj h
      obtain ⟨u, hu⟩ := (f.connectedOn x).nonempty
      exact ⟨(u, v), (u, v'), (prodBranch_eq_some f f').mpr ⟨hu, hv⟩,
        (prodBranch_eq_some f f').mpr ⟨hu, hv'⟩, by simp [lexProduct_adj, hvv]⟩

end MinorOf


namespace InducedMinorOf

/-- **The disjoint union of two induced minor models.**  No edge of the union runs between the
summands, so nothing has to be checked across. -/
def disjUnion (f : A.InducedMinorOf B) (f' : A'.InducedMinorOf B') :
    (A ⊕g A').InducedMinorOf (B ⊕g B') where
  toMinorOf := f.toMinorOf.disjUnion f'.toMinorOf
  adj_map' := by
    rintro (x | x) (y | y) hxy ⟨u, v, hu, hv, huv⟩
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inl _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inl _ _ hv
      have := f.adj_map (fun e ↦ hxy (by rw [e])) ⟨u', v', hu', hv', by simpa using huv⟩
      simpa using this
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inl _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inr _ _ hv
      simp at huv
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inr _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inl _ _ hv
      simp at huv
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inr _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inr _ _ hv
      have := f'.adj_map (fun e ↦ hxy (by rw [e])) ⟨u', v', hu', hv', by simpa using huv⟩
      simpa using this

/-- **The join of two induced minor models.**  Every edge across is an edge of the join, so the
cases that the disjoint union rules out are the ones the join makes trivial. -/
def join (f : A.InducedMinorOf B) (f' : A'.InducedMinorOf B') :
    (A ∇g A').InducedMinorOf (B ∇g B') where
  toMinorOf := f.toMinorOf.join f'.toMinorOf
  adj_map' := by
    rintro (x | x) (y | y) hxy ⟨u, v, hu, hv, huv⟩
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inl _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inl _ _ hv
      have hb : B.Adj u' v' := by
        have : (B ∇g B').Adj (Sum.inl (u' : B.V)) (Sum.inl (v' : B.V)) := huv
        simpa using this
      have := f.adj_map (fun e ↦ hxy (by rw [e])) ⟨u', v', hu', hv', hb⟩
      show (A ∇g A').Adj (Sum.inl (x : A.V)) (Sum.inl (y : A.V))
      simpa using this
    · show (A ∇g A').Adj (Sum.inl (x : A.V)) (Sum.inr (y : A'.V))
      simp
    · show (A ∇g A').Adj (Sum.inr (x : A'.V)) (Sum.inl (y : A.V))
      simp
    · obtain ⟨u', rfl, hu'⟩ := MinorOf.sumBranch_eq_inr _ _ hu
      obtain ⟨v', rfl, hv'⟩ := MinorOf.sumBranch_eq_inr _ _ hv
      have hb : B'.Adj u' v' := by
        have : (B ∇g B').Adj (Sum.inr (u' : B'.V)) (Sum.inr (v' : B'.V)) := huv
        simpa using this
      have := f'.adj_map (fun e ↦ hxy (by rw [e])) ⟨u', v', hu', hv', hb⟩
      show (A ∇g A').Adj (Sum.inr (x : A'.V)) (Sum.inr (y : A'.V))
      simpa using this

/-- **The cartesian product of two induced minor models.**  An edge of the host product moves in
one coordinate only, and the other coordinate pins the two branch sets to the same vertex of that
factor, so the edge comes from an edge of the corresponding factor of the pattern. -/
def cartesianProduct (f : A.InducedMinorOf B) (f' : A'.InducedMinorOf B') :
    (A □g A').InducedMinorOf (B □g B') where
  toMinorOf := f.toMinorOf.cartesianProduct f'.toMinorOf
  adj_map' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy ⟨u, v, hu, hv, huv⟩
    have hu' := (MinorOf.prodBranch_eq_some f.toMinorOf f'.toMinorOf).mp hu
    have hv' := (MinorOf.prodBranch_eq_some f.toMinorOf f'.toMinorOf).mp hv
    have hu₁ : f.branch u.1 = some x := hu'.1
    have hu₂ : f'.branch u.2 = some y := hu'.2
    have hv₁ : f.branch v.1 = some x' := hv'.1
    have hv₂ : f'.branch v.2 = some y' := hv'.2
    simp only [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      at huv ⊢
    rcases huv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁] at hu₁
      have hx : x = x' := Option.some.inj (hu₁.symm.trans hv₁)
      subst hx
      have hy : y ≠ y' := fun e ↦ hxy (by rw [e])
      exact Or.inl ⟨rfl, f'.adj_map hy ⟨u.2, v.2, hu₂, hv₂, h₂⟩⟩
    · rw [h₂] at hu₂
      have hy : y = y' := Option.some.inj (hu₂.symm.trans hv₂)
      subst hy
      have hx : x ≠ x' := fun e ↦ hxy (by rw [e])
      exact Or.inr ⟨f.adj_map hx ⟨u.1, v.1, hu₁, hv₁, h₁⟩, rfl⟩

/-- **The strong product of two induced minor models.**  In each coordinate separately the host
edge either stays inside one branch set, which forces the two pattern vertices to agree there, or
crosses between two of them, which is an edge of that factor of the pattern. -/
def strongProduct (f : A.InducedMinorOf B) (f' : A'.InducedMinorOf B') :
    (A ⊠g A').InducedMinorOf (B ⊠g B') where
  toMinorOf := f.toMinorOf.strongProduct f'.toMinorOf
  adj_map' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy ⟨u, v, hu, hv, huv⟩
    have hu' := (MinorOf.prodBranch_eq_some f.toMinorOf f'.toMinorOf).mp hu
    have hv' := (MinorOf.prodBranch_eq_some f.toMinorOf f'.toMinorOf).mp hv
    have hu₁ : f.branch u.1 = some x := hu'.1
    have hu₂ : f'.branch u.2 = some y := hu'.2
    have hv₁ : f.branch v.1 = some x' := hv'.1
    have hv₂ : f'.branch v.2 = some y' := hv'.2
    simp only [strongProduct_adj, ne_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, not_and] at huv ⊢
    obtain ⟨-, h₁, h₂⟩ := huv
    refine ⟨fun e e' ↦ hxy (by rw [e, e']), ?_, ?_⟩
    · rcases eq_or_ne x x' with rfl | hx
      · exact Or.inl rfl
      · rcases h₁ with h₁ | h₁
        · rw [h₁] at hu₁
          exact absurd (Option.some.inj (hu₁.symm.trans hv₁)) hx
        · exact Or.inr (f.adj_map hx ⟨u.1, v.1, hu₁, hv₁, h₁⟩)
    · rcases eq_or_ne y y' with rfl | hy
      · exact Or.inl rfl
      · rcases h₂ with h₂ | h₂
        · rw [h₂] at hu₂
          exact absurd (Option.some.inj (hu₂.symm.trans hv₂)) hy
        · exact Or.inr (f'.adj_map hy ⟨u.2, v.2, hu₂, hv₂, h₂⟩)

end InducedMinorOf

namespace ContractionOf

/-- **The disjoint union of two contractions.**  Nothing is deleted on either side. -/
def disjUnion (f : A.ContractionOf B) (f' : A'.ContractionOf B') :
    (A ⊕g A').ContractionOf (B ⊕g B') where
  toInducedMinorOf := f.toInducedMinorOf.disjUnion f'.toInducedMinorOf
  total' := MinorOf.sumBranch_isSome _ _ f.total f'.total

/-- **The join of two contractions.** -/
def join (f : A.ContractionOf B) (f' : A'.ContractionOf B') :
    (A ∇g A').ContractionOf (B ∇g B') where
  toInducedMinorOf := f.toInducedMinorOf.join f'.toInducedMinorOf
  total' := MinorOf.sumBranch_isSome _ _ f.total f'.total

/-- **The cartesian product of two contractions.** -/
def cartesianProduct (f : A.ContractionOf B) (f' : A'.ContractionOf B') :
    (A □g A').ContractionOf (B □g B') where
  toInducedMinorOf := f.toInducedMinorOf.cartesianProduct f'.toInducedMinorOf
  total' := MinorOf.prodBranch_isSome _ _ f.total f'.total

/-- **The strong product of two contractions.** -/
def strongProduct (f : A.ContractionOf B) (f' : A'.ContractionOf B') :
    (A ⊠g A').ContractionOf (B ⊠g B') where
  toInducedMinorOf := f.toInducedMinorOf.strongProduct f'.toInducedMinorOf
  total' := MinorOf.prodBranch_isSome _ _ f.total f'.total

end ContractionOf

/-! ## The four map relations, on the two sums -/

namespace Hom

def disjUnion (f : A →cg B) (f' : A' →cg B') : (A ⊕g A') →cg (B ⊕g B') where
  toFun := Sum.map f f'
  map_rel' := by
    intro x y h
    exact disjUnion_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

def join (f : A →cg B) (f' : A' →cg B') : (A ∇g A') →cg (B ∇g B') where
  toFun := Sum.map f f'
  map_rel' := by
    intro x y h
    exact join_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

def cartesianProduct (f : A →cg B) (f' : A' →cg B') : (A □g A') →cg (B □g B') where
  toFun := Prod.map f f'
  map_rel' := by
    intro x y h
    exact cartesianProduct_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

def tensorProduct (f : A →cg B) (f' : A' →cg B') : (A ⊗g A') →cg (B ⊗g B') where
  toFun := Prod.map f f'
  map_rel' := by
    intro x y h
    exact tensorProduct_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

def strongProduct (f : A →cg B) (f' : A' →cg B') : (A ⊠g A') →cg (B ⊠g B') where
  toFun := Prod.map f f'
  map_rel' := by
    intro x y h
    exact strongProduct_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

def lexProduct (f : A →cg B) (f' : A' →cg B') : (A ·g A') →cg (B ·g B') where
  toFun := Prod.map f f'
  map_rel' := by
    intro x y h
    exact lexProduct_map_adj (fun _ _ ↦ f.map_rel) (fun _ _ ↦ f'.map_rel) x y h

end Hom

namespace SubgraphOf

def disjUnion (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') : (A ⊕g A').SubgraphOf (B ⊕g B') where
  toFun := Sum.map f f'
  injective' := f.injective.sumMap f'.injective
  map_adj' := disjUnion_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def join (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') : (A ∇g A').SubgraphOf (B ∇g B') where
  toFun := Sum.map f f'
  injective' := f.injective.sumMap f'.injective
  map_adj' := join_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def cartesianProduct (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') :
    (A □g A').SubgraphOf (B □g B') where
  toFun := Prod.map f f'
  injective' := f.injective.prodMap f'.injective
  map_adj' := cartesianProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def tensorProduct (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') :
    (A ⊗g A').SubgraphOf (B ⊗g B') where
  toFun := Prod.map f f'
  injective' := f.injective.prodMap f'.injective
  map_adj' := tensorProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def strongProduct (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') :
    (A ⊠g A').SubgraphOf (B ⊠g B') where
  toFun := Prod.map f f'
  injective' := f.injective.prodMap f'.injective
  map_adj' := strongProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def lexProduct (f : A.SubgraphOf B) (f' : A'.SubgraphOf B') :
    (A ·g A').SubgraphOf (B ·g B') where
  toFun := Prod.map f f'
  injective' := f.injective.prodMap f'.injective
  map_adj' := lexProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

end SubgraphOf

namespace InducedSubgraphOf

def disjUnion (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ⊕g A').InducedSubgraphOf (B ⊕g B') where
  toSubgraphOf := f.toSubgraphOf.disjUnion f'.toSubgraphOf
  adj_map' := disjUnion_adj_map (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

def join (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ∇g A').InducedSubgraphOf (B ∇g B') where
  toSubgraphOf := f.toSubgraphOf.join f'.toSubgraphOf
  adj_map' := join_adj_map (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

def cartesianProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A □g A').InducedSubgraphOf (B □g B') where
  toSubgraphOf := f.toSubgraphOf.cartesianProduct f'.toSubgraphOf
  adj_map' :=
    cartesianProduct_adj_map f.injective f'.injective (fun _ _ ↦ f.adj_map)
      (fun _ _ ↦ f'.adj_map)

def tensorProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ⊗g A').InducedSubgraphOf (B ⊗g B') where
  toSubgraphOf := f.toSubgraphOf.tensorProduct f'.toSubgraphOf
  adj_map' := tensorProduct_adj_map (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

def strongProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ⊠g A').InducedSubgraphOf (B ⊠g B') where
  toSubgraphOf := f.toSubgraphOf.strongProduct f'.toSubgraphOf
  adj_map' :=
    strongProduct_adj_map f.injective f'.injective (fun _ _ ↦ f.adj_map)
      (fun _ _ ↦ f'.adj_map)

def lexProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ·g A').InducedSubgraphOf (B ·g B') where
  toSubgraphOf := f.toSubgraphOf.lexProduct f'.toSubgraphOf
  adj_map' := lexProduct_adj_map f.injective (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

end InducedSubgraphOf

namespace QuotientOf

def disjUnion (f : A.QuotientOf B) (f' : A'.QuotientOf B') : (A ⊕g A').QuotientOf (B ⊕g B') where
  toFun := Sum.map f f'
  surjective' := f.surjective.sumMap f'.surjective
  map_adj' := disjUnion_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def join (f : A.QuotientOf B) (f' : A'.QuotientOf B') : (A ∇g A').QuotientOf (B ∇g B') where
  toFun := Sum.map f f'
  surjective' := f.surjective.sumMap f'.surjective
  map_adj' := join_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def cartesianProduct (f : A.QuotientOf B) (f' : A'.QuotientOf B') :
    (A □g A').QuotientOf (B □g B') where
  toFun := Prod.map f f'
  surjective' := f.surjective.prodMap f'.surjective
  map_adj' := cartesianProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def tensorProduct (f : A.QuotientOf B) (f' : A'.QuotientOf B') :
    (A ⊗g A').QuotientOf (B ⊗g B') where
  toFun := Prod.map f f'
  surjective' := f.surjective.prodMap f'.surjective
  map_adj' := tensorProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def strongProduct (f : A.QuotientOf B) (f' : A'.QuotientOf B') :
    (A ⊠g A').QuotientOf (B ⊠g B') where
  toFun := Prod.map f f'
  surjective' := f.surjective.prodMap f'.surjective
  map_adj' := strongProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

def lexProduct (f : A.QuotientOf B) (f' : A'.QuotientOf B') :
    (A ·g A').QuotientOf (B ·g B') where
  toFun := Prod.map f f'
  surjective' := f.surjective.prodMap f'.surjective
  map_adj' := lexProduct_map_adj (fun _ _ ↦ f.map_adj) (fun _ _ ↦ f'.map_adj)

end QuotientOf

/-! ## Topological minors and immersions, on the two sums and the cartesian product

The last two relations replace an edge of `H` by a walk of `G`, so a construction on them has to
say which walk each edge of the operation gets.  An edge inside a summand keeps that summand's
walk, carried over by `Sum.inl` or `Sum.inr`; an edge across the join is an edge of the join of
the hosts, and gets a walk of one edge; the disjoint union has no edges across.  An edge of a
cartesian product moves exactly one of the two coordinates and keeps the other, so it keeps the
walk of that factor, run along the row or the column that the other coordinate names.  Two such
walks meet only where a row meets a column, which is a branch vertex of the product, and they
never share an edge, since an edge of a row and an edge of a column are never the same edge.

The other three products are not attempted: there an edge of `H` can move both coordinates, so
its walk would have to be routed through the product itself, and two walks routed that way would
have to be kept apart by hand. -/

/-! ### The two summands as homomorphisms -/

/-- `Sum.inl` as a homomorphism into a disjoint union. -/
def inlHom (B B' : CGraph) : B.toSimple →g (B ⊕g B').toSimple where
  toFun := Sum.inl
  map_rel' {_ _} h := by simpa using h

/-- `Sum.inr` as a homomorphism into a disjoint union. -/
def inrHom (B B' : CGraph) : B'.toSimple →g (B ⊕g B').toSimple where
  toFun := Sum.inr
  map_rel' {_ _} h := by simpa using h

/-- `inlHom` is `Sum.inl`. -/
@[simp] theorem inlHom_apply (B B' : CGraph) (u : B.V) :
    inlHom B B' u = (Sum.inl u : (B ⊕g B').V) := rfl

/-- `inrHom` is `Sum.inr`. -/
@[simp] theorem inrHom_apply (B B' : CGraph) (u : B'.V) :
    inrHom B B' u = (Sum.inr u : (B ⊕g B').V) := rfl

/-- `inlHom` is injective, which is what `Walk.map` asks for. -/
theorem inlHom_injective (B B' : CGraph) : Function.Injective ⇑(inlHom B B') :=
  fun _ _ h ↦ Sum.inl_injective h

/-- `inrHom` is injective, which is what `Walk.map` asks for. -/
theorem inrHom_injective (B B' : CGraph) : Function.Injective ⇑(inrHom B B') :=
  fun _ _ h ↦ Sum.inr_injective h

/-- Every vertex of one side of a join is adjacent to every vertex of the other. -/
theorem toSimple_join_inl_inr (B B' : CGraph) (u : B.V) (v : B'.V) :
    (B ∇g B').toSimple.Adj (Sum.inl u) (Sum.inr v) := by simp

/-- Every vertex of one side of a join is adjacent to every vertex of the other. -/
theorem toSimple_join_inr_inl (B B' : CGraph) (u : B'.V) (v : B.V) :
    (B ∇g B').toSimple.Adj (Sum.inr u) (Sum.inl v) := by simp

/-- `Sum.inl` as a homomorphism into a join. -/
def joinInlHom (B B' : CGraph) : B.toSimple →g (B ∇g B').toSimple where
  toFun := Sum.inl
  map_rel' {u v} h := by
    show (B ∇g B').Adj (Sum.inl u) (Sum.inl v) = true
    rw [join_adj_inl_inl]
    exact h

/-- `Sum.inr` as a homomorphism into a join. -/
def joinInrHom (B B' : CGraph) : B'.toSimple →g (B ∇g B').toSimple where
  toFun := Sum.inr
  map_rel' {u v} h := by
    show (B ∇g B').Adj (Sum.inr u) (Sum.inr v) = true
    rw [join_adj_inr_inr]
    exact h

/-- The underlying function of `inlHom`, for rewriting under `Walk.map`. -/
@[simp] theorem coe_inlHom (B B' : CGraph) :
    ⇑(inlHom B B') = (Sum.inl : B.V → (B ⊕g B').V) := rfl

/-- The underlying function of `inrHom`, for rewriting under `Walk.map`. -/
@[simp] theorem coe_inrHom (B B' : CGraph) :
    ⇑(inrHom B B') = (Sum.inr : B'.V → (B ⊕g B').V) := rfl

/-- The underlying function of `joinInlHom`, for rewriting under `Walk.map`. -/
@[simp] theorem coe_joinInlHom (B B' : CGraph) :
    ⇑(joinInlHom B B') = (Sum.inl : B.V → (B ∇g B').V) := rfl

/-- The underlying function of `joinInrHom`, for rewriting under `Walk.map`. -/
@[simp] theorem coe_joinInrHom (B B' : CGraph) :
    ⇑(joinInrHom B B') = (Sum.inr : B'.V → (B ∇g B').V) := rfl

/-- `joinInlHom` is `Sum.inl`. -/
@[simp] theorem joinInlHom_apply (B B' : CGraph) (u : B.V) :
    joinInlHom B B' u = (Sum.inl u : (B ∇g B').V) := rfl

/-- `joinInrHom` is `Sum.inr`. -/
@[simp] theorem joinInrHom_apply (B B' : CGraph) (u : B'.V) :
    joinInrHom B B' u = (Sum.inr u : (B ∇g B').V) := rfl

/-- An edge inside the left summand is not an edge inside the right one. -/
theorem sym2_map_inl_ne_map_inr {α β : Type*} (e : Sym2 α) (e' : Sym2 β) :
    Sym2.map (Sum.inl : α → α ⊕ β) e ≠ Sym2.map Sum.inr e' := by
  induction e using Sym2.ind with | _ x y =>
  induction e' using Sym2.ind with | _ u v =>
  simp

/-- An edge inside the left summand is not an edge across. -/
theorem sym2_map_inl_ne_cross {α β : Type*} (e : Sym2 α) (u : α) (v : β) :
    Sym2.map (Sum.inl : α → α ⊕ β) e ≠ s(Sum.inl u, Sum.inr v) := by
  induction e using Sym2.ind with | _ x y => simp

/-- An edge inside the left summand is not an edge across. -/
theorem sym2_map_inl_ne_cross' {α β : Type*} (e : Sym2 α) (u : α) (v : β) :
    Sym2.map (Sum.inl : α → α ⊕ β) e ≠ s(Sum.inr v, Sum.inl u) := by
  induction e using Sym2.ind with | _ x y => simp

/-- An edge inside the right summand is not an edge across. -/
theorem sym2_map_inr_ne_cross {α β : Type*} (e : Sym2 β) (u : α) (v : β) :
    Sym2.map (Sum.inr : β → α ⊕ β) e ≠ s(Sum.inl u, Sum.inr v) := by
  induction e using Sym2.ind with | _ x y => simp

/-- An edge inside the right summand is not an edge across. -/
theorem sym2_map_inr_ne_cross' {α β : Type*} (e : Sym2 β) (u : α) (v : β) :
    Sym2.map (Sum.inr : β → α ⊕ β) e ≠ s(Sum.inr v, Sum.inl u) := by
  induction e using Sym2.ind with | _ x y => simp

/-- Two edges across a sum are equal only if both of their ends are. -/
theorem sym2_cross_eq {α β : Type*} {u u' : α} {v v' : β}
    (h : s(Sum.inl u, Sum.inr v) = s(Sum.inl u', Sum.inr v')) : u = u' ∧ v = v' := by
  rw [Sym2.eq_iff] at h
  simpa using h

/-- Two edges across a sum are equal only if both of their ends are. -/
theorem sym2_cross_eq' {α β : Type*} {u u' : α} {v v' : β}
    (h : s(Sum.inl u, Sum.inr v) = s(Sum.inr v', Sum.inl u')) : u = u' ∧ v = v' := by
  rw [Sym2.eq_iff] at h
  simpa using h

/-- Two edges across a sum are equal only if both of their ends are. -/
theorem sym2_cross_eq'' {α β : Type*} {u u' : α} {v v' : β}
    (h : s(Sum.inr v, Sum.inl u) = s(Sum.inr v', Sum.inl u')) : u = u' ∧ v = v' := by
  rw [Sym2.eq_iff] at h
  exact ((by simpa using h : v = v' ∧ u = u').symm)

/-! ### The two factors of a cartesian product as homomorphisms -/

/-- A row of a cartesian product: `(·, q)` as a homomorphism. -/
def fstHom (B B' : CGraph) (q : B'.V) : B.toSimple →g (B □g B').toSimple where
  toFun p := (p, q)
  map_rel' {u v} h := by
    show (B □g B').Adj (u, q) (v, q) = true
    simp only [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨h, trivial⟩

/-- A column of a cartesian product: `(p, ·)` as a homomorphism. -/
def sndHom (B B' : CGraph) (p : B.V) : B'.toSimple →g (B □g B').toSimple where
  toFun q := (p, q)
  map_rel' {u v} h := by
    show (B □g B').Adj (p, u) (p, v) = true
    simp only [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨trivial, h⟩

@[simp] theorem coe_fstHom (B B' : CGraph) (q : B'.V) :
    ⇑(fstHom B B' q) = fun p ↦ (p, q) := rfl

@[simp] theorem coe_sndHom (B B' : CGraph) (p : B.V) :
    ⇑(sndHom B B' p) = fun q ↦ (p, q) := rfl

theorem fstHom_injective (B B' : CGraph) (q : B'.V) : Function.Injective ⇑(fstHom B B' q) :=
  fun _ _ h ↦ congrArg Prod.fst h

theorem sndHom_injective (B B' : CGraph) (p : B.V) : Function.Injective ⇑(sndHom B B' p) :=
  fun _ _ h ↦ congrArg Prod.snd h

theorem mem_support_sndHom {p : B.V} {u v : B'.V} (w : B'.toSimple.Walk u v)
    (z : B.V × B'.V) :
    z ∈ (w.map (sndHom B B' p)).support ↔ z.1 = p ∧ z.2 ∈ w.support := by
  simp only [SimpleGraph.Walk.support_map, List.mem_map, coe_sndHom]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨rfl, hq⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨z.2, h₂, by rw [← h₁]⟩

theorem mem_support_fstHom {q : B'.V} {u v : B.V} (w : B.toSimple.Walk u v)
    (z : B.V × B'.V) :
    z ∈ (w.map (fstHom B B' q)).support ↔ z.2 = q ∧ z.1 ∈ w.support := by
  simp only [SimpleGraph.Walk.support_map, List.mem_map, coe_fstHom]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨rfl, hp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨z.1, h₂, by rw [← h₁]⟩

theorem mem_edges_sndHom {p : B.V} {u v : B'.V} (w : B'.toSimple.Walk u v)
    (e : Sym2 (B.V × B'.V)) :
    e ∈ (w.map (sndHom B B' p)).edges ↔ ∃ e₀ ∈ w.edges, Sym2.map (fun q ↦ (p, q)) e₀ = e := by
  simp [SimpleGraph.Walk.edges_map]

theorem mem_edges_fstHom {q : B'.V} {u v : B.V} (w : B.toSimple.Walk u v)
    (e : Sym2 (B.V × B'.V)) :
    e ∈ (w.map (fstHom B B' q)).edges ↔ ∃ e₀ ∈ w.edges, Sym2.map (fun p ↦ (p, q)) e₀ = e := by
  simp [SimpleGraph.Walk.edges_map]

/-- An edge of a cartesian product that keeps the first coordinate moves along the second. -/
theorem cartesianProduct_adj_of_fst_eq {x₁ y₁ : A.V} {x₂ y₂ : A'.V}
    (h : (A □g A').Adj (x₁, x₂) (y₁, y₂)) (hx : x₁ = y₁) : A'.Adj x₂ y₂ := by
  subst hx
  simpa [A.loopless x₁] using h

/-- An edge of a cartesian product that moves the first coordinate keeps the second. -/
theorem cartesianProduct_adj_of_fst_ne {x₁ y₁ : A.V} {x₂ y₂ : A'.V}
    (h : (A □g A').Adj (x₁, x₂) (y₁, y₂)) (hx : x₁ ≠ y₁) : A.Adj x₁ y₁ ∧ x₂ = y₂ := by
  simpa [hx] using h

/-- A column of a cartesian product and a row of it share no edge. -/
theorem sym2_map_col_ne_row {α β : Type*} {a : α} {c : β} {e : Sym2 β} {e' : Sym2 α}
    (he : ¬ e.IsDiag) :
    Sym2.map (fun q : β ↦ (a, q)) e ≠ Sym2.map (fun p : α ↦ (p, c)) e' := by
  induction e using Sym2.ind with | _ u v => ?_
  induction e' using Sym2.ind with | _ p p' => ?_
  simp only [Sym2.isDiag_iff_proj_eq] at he
  intro h
  rw [Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ | ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ <;> exact he (h₁.trans h₂.symm)

/-- Two columns of a cartesian product that share an edge are the same column. -/
theorem sym2_map_col_eq {α β : Type*} {a a' : α} {e e' : Sym2 β}
    (h : Sym2.map (fun q : β ↦ (a, q)) e = Sym2.map (fun q : β ↦ (a', q)) e') : a = a' := by
  induction e using Sym2.ind with | _ u v => ?_
  induction e' using Sym2.ind with | _ u' v' => ?_
  rw [Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h

/-- Two rows of a cartesian product that share an edge are the same row. -/
theorem sym2_map_row_eq {α β : Type*} {c c' : β} {e e' : Sym2 α}
    (h : Sym2.map (fun p : α ↦ (p, c)) e = Sym2.map (fun p : α ↦ (p, c')) e') : c = c' := by
  induction e using Sym2.ind with | _ u v => ?_
  induction e' using Sym2.ind with | _ u' v' => ?_
  rw [Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨-, h⟩, -⟩ | ⟨⟨-, h⟩, -⟩ <;> exact h

/-- Two edges in the same column of a cartesian product are different if the columns' edges
are. -/
theorem sym2_col_ne {α β : Type*} {a : α} {u v u' v' : β}
    (h : s((a, u), (a, v)) ≠ (s((a, u'), (a, v')) : Sym2 (α × β))) : s(u, v) ≠ s(u', v') := by
  intro he
  refine h ?_
  rw [Sym2.eq_iff] at he ⊢
  simpa using he

/-- Two edges in the same row of a cartesian product are different if the rows' edges are. -/
theorem sym2_row_ne {α β : Type*} {c : β} {u v u' v' : α}
    (h : s((u, c), (v, c)) ≠ (s((u', c), (v', c)) : Sym2 (α × β))) : s(u, v) ≠ s(u', v') := by
  intro he
  refine h ?_
  rw [Sym2.eq_iff] at he ⊢
  simpa using he

/-! ### Topological minors -/

namespace TopMinorOf

/-- The path replacing an edge of a disjoint union: the edge lies in one summand, and so does its
path. -/
def sumPath (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    ∀ (x y : A.V ⊕ A'.V), (A ⊕g A').Adj x y →
      (B ⊕g B').toSimple.Walk (Sum.map f.toFun f'.toFun x) (Sum.map f.toFun f'.toFun y)
  | Sum.inl _, Sum.inl _, h => (f.path (by simpa using h)).map (inlHom B B')
  | Sum.inl _, Sum.inr _, h => absurd h (by simp)
  | Sum.inr _, Sum.inl _, h => absurd h (by simp)
  | Sum.inr _, Sum.inr _, h => (f'.path (by simpa using h)).map (inrHom B B')

/-- **The disjoint union of two topological minor models.** -/
def disjUnion (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    (A ⊕g A').TopMinorOf (B ⊕g B') where
  toFun := Sum.map f.toFun f'.toFun
  injective' := f.injective.sumMap f'.injective
  path {x y} h := sumPath f f' x y h
  isPath' := by
    rintro (a | b) (c | d) h
    · exact SimpleGraph.Walk.map_isPath_of_injective (inlHom_injective B B') (f.isPath' _)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact SimpleGraph.Walk.map_isPath_of_injective (inrHom_injective B B') (f'.isPath' _)
  reverse' := by
    rintro (a | b) (c | d) h h'
    · show (f.path _).map (inlHom B B') = ((f.path _).map (inlHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f.reverse' (show A.Adj a c by simpa using h)]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · show (f'.path _).map (inrHom B B') = ((f'.path _).map (inrHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f'.reverse' (show A'.Adj b d by simpa using h)]
  branch' := by
    rintro (a | b) (c | d) h (z | z) hz
    all_goals first
      | simp only [disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, Bool.false_eq_true] at h
      | skip
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inlHom_apply,
        Sum.map_inl] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact (f.branch' (by simpa using h) z (Sum.inl_injective hwz ▸ hw)).imp
        (congrArg Sum.inl) (congrArg Sum.inl)
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inlHom_apply,
        Sum.map_inr] at hz
      simp at hz
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inrHom_apply,
        Sum.map_inl] at hz
      simp at hz
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inrHom_apply,
        Sum.map_inr] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact (f'.branch' (by simpa using h) z (Sum.inr_injective hwz ▸ hw)).imp
        (congrArg Sum.inr) (congrArg Sum.inr)
  disjoint' := by
    rintro (a | b) (c | d) h (a' | b') (c' | d') h' hne z hz hz'
    all_goals first
      | simp only [disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, Bool.false_eq_true] at h
      | simp only [disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, Bool.false_eq_true] at h'
      | skip
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inlHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      obtain ⟨t, rfl⟩ := f.disjoint' (by simpa using h) (by simpa using h')
        (fun e ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inl) e)) w hw
        (Sum.inl_injective hww ▸ hw')
      exact ⟨Sum.inl t, rfl⟩
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inlHom_apply,
        inrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      simp at hww
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inlHom_apply,
        inrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      simp at hww
    · simp only [sumPath, SimpleGraph.Walk.support_map, List.mem_map, inrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      obtain ⟨t, rfl⟩ := f'.disjoint' (by simpa using h) (by simpa using h')
        (fun e ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inr) e)) w hw
        (Sum.inr_injective hww ▸ hw')
      exact ⟨Sum.inr t, rfl⟩

/-- The path replacing an edge of a join: an edge inside a summand keeps that summand's path,
and an edge across is an edge of the join already. -/
def joinPath (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    ∀ (x y : (A ∇g A').V), (A ∇g A').Adj x y →
      (B ∇g B').toSimple.Walk (Sum.map f.toFun f'.toFun x) (Sum.map f.toFun f'.toFun y)
  | Sum.inl _, Sum.inl _, h => (f.path (by simpa using h)).map (joinInlHom B B')
  | Sum.inl _, Sum.inr _, _ => .cons (toSimple_join_inl_inr B B' _ _) .nil
  | Sum.inr _, Sum.inl _, _ => .cons (toSimple_join_inr_inl B B' _ _) .nil
  | Sum.inr _, Sum.inr _, h => (f'.path (by simpa using h)).map (joinInrHom B B')

/-- **The join of two topological minor models.**  Every edge across the join is an edge of the
join of the hosts, so the paths that the disjoint union has no need of are the ones the join makes
a single edge. -/
def join (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    (A ∇g A').TopMinorOf (B ∇g B') where
  toFun := Sum.map f.toFun f'.toFun
  injective' := f.injective.sumMap f'.injective
  path {x y} h := joinPath f f' x y h
  isPath' := by
    rintro (a | b) (c | d) h
    · exact SimpleGraph.Walk.map_isPath_of_injective
        (fun _ _ hh ↦ Sum.inl_injective hh) (f.isPath' _)
    · simp [joinPath, SimpleGraph.Walk.cons_isPath_iff]
    · simp [joinPath, SimpleGraph.Walk.cons_isPath_iff]
    · exact SimpleGraph.Walk.map_isPath_of_injective
        (fun _ _ hh ↦ Sum.inr_injective hh) (f'.isPath' _)
  reverse' := by
    rintro (a | b) (c | d) h h'
    · show (f.path _).map (joinInlHom B B') = ((f.path _).map (joinInlHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f.reverse' (show A.Adj a c by simpa using h)]
    · show SimpleGraph.Walk.cons _ _ = _
      simp [joinPath]
    · show SimpleGraph.Walk.cons _ _ = _
      simp [joinPath]
    · show (f'.path _).map (joinInrHom B B') = ((f'.path _).map (joinInrHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f'.reverse' (show A'.Adj b d by simpa using h)]
  branch' := by
    rintro (a | b) (c | d) h (z | z) hz
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInlHom_apply,
        Sum.map_inl] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact (f.branch' (by simpa using h) z (Sum.inl_injective hwz ▸ hw)).imp
        (congrArg Sum.inl) (congrArg Sum.inl)
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInlHom_apply,
        Sum.map_inr] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact absurd hwz (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.map_inl, Sum.map_inr] at hz
      rcases hz with hz | hz
      · exact Or.inl (congrArg Sum.inl (f.injective (Sum.inl_injective hz)))
      · exact absurd hz (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.map_inl, Sum.map_inr] at hz
      rcases hz with hz | hz
      · exact absurd hz (by simp)
      · exact Or.inr (congrArg Sum.inr (f'.injective (Sum.inr_injective hz)))
    · simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.map_inl, Sum.map_inr] at hz
      rcases hz with hz | hz
      · exact absurd hz (by simp)
      · exact Or.inr (congrArg Sum.inl (f.injective (Sum.inl_injective hz)))
    · simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.map_inl, Sum.map_inr] at hz
      rcases hz with hz | hz
      · exact Or.inl (congrArg Sum.inr (f'.injective (Sum.inr_injective hz)))
      · exact absurd hz (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInrHom_apply,
        Sum.map_inl] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact absurd hwz (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInrHom_apply,
        Sum.map_inr] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      exact (f'.branch' (by simpa using h) z (Sum.inr_injective hwz ▸ hw)).imp
        (congrArg Sum.inr) (congrArg Sum.inr)
  disjoint' := by
    rintro (a | b) (c | d) h (a' | b') (c' | d') h' hne z hz hz'
    all_goals first
      | (simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hz
         rcases hz with rfl | rfl <;>
           first
             | exact ⟨Sum.inl a, rfl⟩ | exact ⟨Sum.inr b, rfl⟩
             | exact ⟨Sum.inl c, rfl⟩ | exact ⟨Sum.inr d, rfl⟩)
      | (simp only [joinPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hz'
         rcases hz' with rfl | rfl <;>
           first
             | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr b', rfl⟩
             | exact ⟨Sum.inl c', rfl⟩ | exact ⟨Sum.inr d', rfl⟩)
      | skip
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInlHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      obtain ⟨t, rfl⟩ := f.disjoint' (by simpa using h) (by simpa using h')
        (fun e ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inl) e)) w hw
        (Sum.inl_injective hww ▸ hw')
      exact ⟨Sum.inl t, rfl⟩
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInlHom_apply,
        joinInrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      exact absurd hww (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInlHom_apply,
        joinInrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      exact absurd hww (by simp)
    · simp only [joinPath, SimpleGraph.Walk.support_map, List.mem_map, joinInrHom_apply] at hz hz'
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨w', hw', hww⟩ := hz'
      obtain ⟨t, rfl⟩ := f'.disjoint' (by simpa using h) (by simpa using h')
        (fun e ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inr) e)) w hw
        (Sum.inr_injective hww ▸ hw')
      exact ⟨Sum.inr t, rfl⟩

/-- The path replacing an edge of a cartesian product: an edge that moves the first coordinate
takes the path of the first factor, at a fixed second coordinate, and vice versa. -/
def prodPath (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    ∀ (x y : A.V × A'.V), (A □g A').Adj x y →
      (B □g B').toSimple.Walk (Prod.map f.toFun f'.toFun x) (Prod.map f.toFun f'.toFun y)
  | (x₁, x₂), (y₁, y₂), h =>
    if hx : x₁ = y₁ then
      ((f'.path (cartesianProduct_adj_of_fst_eq h hx)).map (sndHom B B' (f.toFun x₁))).copy rfl
        (by rw [hx]; rfl)
    else
      ((f.path (cartesianProduct_adj_of_fst_ne h hx).1).map (fstHom B B' (f'.toFun x₂))).copy rfl
        (by rw [(cartesianProduct_adj_of_fst_ne h hx).2]; rfl)

/-- An edge along the second coordinate takes the second factor's path, in one column. -/
theorem prodPath_col (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') {x₁ : A.V} {x₂ y₂ : A'.V}
    (h : (A □g A').Adj (x₁, x₂) (x₁, y₂)) (ha : A'.Adj x₂ y₂) :
    prodPath f f' (x₁, x₂) (x₁, y₂) h = (f'.path ha).map (sndHom B B' (f.toFun x₁)) := by
  rw [prodPath, dif_pos rfl]
  rfl

/-- An edge along the first coordinate takes the first factor's path, in one row. -/
theorem prodPath_row (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') {x₁ y₁ : A.V} {x₂ : A'.V}
    (hx : x₁ ≠ y₁) (h : (A □g A').Adj (x₁, x₂) (y₁, x₂)) (ha : A.Adj x₁ y₁) :
    prodPath f f' (x₁, x₂) (y₁, x₂) h = (f.path ha).map (fstHom B B' (f'.toFun x₂)) := by
  rw [prodPath, dif_neg hx]
  rfl

/-- A topological minor of each factor is a topological minor of the cartesian product. -/
def cartesianProduct (f : A.TopMinorOf B) (f' : A'.TopMinorOf B') :
    (A □g A').TopMinorOf (B □g B') where
  toFun := Prod.map f.toFun f'.toFun
  injective' := f.injective.prodMap f'.injective
  path {x y} h := prodPath f f' x y h
  isPath' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    by_cases hx : x₁ = y₁
    · subst hx
      rw [prodPath_col f f' h (cartesianProduct_adj_of_fst_eq h rfl)]
      exact SimpleGraph.Walk.map_isPath_of_injective (sndHom_injective B B' _) (f'.isPath' _)
    · obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      rw [prodPath_row f f' hx h ha]
      exact SimpleGraph.Walk.map_isPath_of_injective (fstHom_injective B B' _) (f.isPath' _)
  reverse' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h h'
    by_cases hx : x₁ = y₁
    · subst hx
      rw [prodPath_col f f' h (cartesianProduct_adj_of_fst_eq h rfl),
        prodPath_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl),
        SimpleGraph.Walk.reverse_map,
        f'.reverse' (cartesianProduct_adj_of_fst_eq h rfl)]
    · obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      obtain ⟨ha', -⟩ := cartesianProduct_adj_of_fst_ne h' (Ne.symm hx)
      rw [prodPath_row f f' (Ne.symm hx) h' ha', prodPath_row f f' hx h ha,
        SimpleGraph.Walk.reverse_map, f.reverse' ha]
  branch' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h ⟨z₁, z₂⟩ hz
    by_cases hx : x₁ = y₁
    · subst hx
      rw [prodPath_col f f' h (cartesianProduct_adj_of_fst_eq h rfl),
        mem_support_sndHom] at hz
      obtain ⟨hz₁, hz₂⟩ := hz
      have : z₁ = x₁ := f.injective hz₁
      subst this
      exact (f'.branch' (cartesianProduct_adj_of_fst_eq h rfl) z₂ hz₂).imp
        (fun hh ↦ by rw [hh]) (fun hh ↦ by rw [hh])
    · obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      rw [prodPath_row f f' hx h ha, mem_support_fstHom] at hz
      obtain ⟨hz₂, hz₁⟩ := hz
      have : z₂ = x₂ := f'.injective hz₂
      subst this
      exact (f.branch' ha z₁ hz₁).imp (fun hh ↦ by rw [hh]) (fun hh ↦ by rw [hh])
  disjoint' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h ⟨x₁', x₂'⟩ ⟨y₁', y₂'⟩ h' hne ⟨z₁, z₂⟩ hz hz'
    by_cases hx : x₁ = y₁ <;> by_cases hx' : x₁' = y₁'
    · -- two columns
      subst hx
      subst hx'
      rw [prodPath_col f f' h (cartesianProduct_adj_of_fst_eq h rfl), mem_support_sndHom] at hz
      rw [prodPath_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl), mem_support_sndHom] at hz'
      obtain ⟨hz₁, hz₂⟩ := hz
      obtain ⟨hz₁', hz₂'⟩ := hz'
      have : x₁ = x₁' := f.injective (hz₁.symm.trans hz₁')
      subst this
      obtain ⟨b, hb⟩ := f'.disjoint' (cartesianProduct_adj_of_fst_eq h rfl)
        (cartesianProduct_adj_of_fst_eq h' rfl) (sym2_col_ne hne) z₂ hz₂ hz₂'
      exact ⟨(x₁, b), Prod.ext hz₁ hb⟩
    · -- a column and a row
      subst hx
      obtain ⟨ha', rfl⟩ := cartesianProduct_adj_of_fst_ne h' hx'
      rw [prodPath_col f f' h (cartesianProduct_adj_of_fst_eq h rfl), mem_support_sndHom] at hz
      rw [prodPath_row f f' hx' h' ha', mem_support_fstHom] at hz'
      exact ⟨(x₁, x₂'), Prod.ext hz.1 hz'.1⟩
    · -- a row and a column
      subst hx'
      obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      rw [prodPath_row f f' hx h ha, mem_support_fstHom] at hz
      rw [prodPath_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl), mem_support_sndHom] at hz'
      exact ⟨(x₁', x₂), Prod.ext hz'.1 hz.1⟩
    · -- two rows
      obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      obtain ⟨ha', rfl⟩ := cartesianProduct_adj_of_fst_ne h' hx'
      rw [prodPath_row f f' hx h ha, mem_support_fstHom] at hz
      rw [prodPath_row f f' hx' h' ha', mem_support_fstHom] at hz'
      obtain ⟨hz₂, hz₁⟩ := hz
      obtain ⟨hz₂', hz₁'⟩ := hz'
      have : x₂ = x₂' := f'.injective (hz₂.symm.trans hz₂')
      subst this
      obtain ⟨b, hb⟩ := f.disjoint' ha ha' (sym2_row_ne hne) z₁ hz₁ hz₁'
      exact ⟨(b, x₂), Prod.ext hb hz₂⟩

end TopMinorOf

/-! ### Immersions -/

namespace ImmersionOf

/-- The trail replacing an edge of a disjoint union: the edge lies in one summand, and so does
its trail. -/
def sumWalk (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    ∀ (x y : A.V ⊕ A'.V), (A ⊕g A').Adj x y →
      (B ⊕g B').toSimple.Walk (Sum.map f.toFun f'.toFun x) (Sum.map f.toFun f'.toFun y)
  | Sum.inl _, Sum.inl _, h => (f.walk (by simpa using h)).map (inlHom B B')
  | Sum.inl _, Sum.inr _, h => absurd h (by simp)
  | Sum.inr _, Sum.inl _, h => absurd h (by simp)
  | Sum.inr _, Sum.inr _, h => (f'.walk (by simpa using h)).map (inrHom B B')

/-- **The disjoint union of two immersions.** -/
def disjUnion (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    (A ⊕g A').ImmersionOf (B ⊕g B') where
  toFun := Sum.map f.toFun f'.toFun
  injective' := f.injective.sumMap f'.injective
  walk {x y} h := sumWalk f f' x y h
  isTrail' := by
    rintro (a | b) (c | d) h
    · exact SimpleGraph.Walk.map_isTrail_of_injective (inlHom_injective B B') (f.isTrail' _)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact SimpleGraph.Walk.map_isTrail_of_injective (inrHom_injective B B') (f'.isTrail' _)
  reverse' := by
    rintro (a | b) (c | d) h h'
    · show (f.walk _).map (inlHom B B') = ((f.walk _).map (inlHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f.reverse' (show A.Adj a c by simpa using h)]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · show (f'.walk _).map (inrHom B B') = ((f'.walk _).map (inrHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f'.reverse' (show A'.Adj b d by simpa using h)]
  edgeDisjoint' := by
    rintro (a | b) (c | d) h (a' | b') (c' | d') h' hne e he he'
    all_goals first
      | simp only [disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, Bool.false_eq_true] at h
      | simp only [disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, Bool.false_eq_true] at h'
      | skip
    · simp only [sumWalk, SimpleGraph.Walk.edges_map, List.mem_map, coe_inlHom] at he he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact f.edgeDisjoint' (by simpa using h) (by simpa using h')
        (fun eq ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inl) eq))
        e₀ he₀ (Sym2.map.injective Sum.inl_injective hee ▸ he₁)
    · simp only [sumWalk, SimpleGraph.Walk.edges_map, List.mem_map, coe_inlHom, coe_inrHom]
        at he he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_map_inr e₀ e₁ hee.symm
    · simp only [sumWalk, SimpleGraph.Walk.edges_map, List.mem_map, coe_inlHom, coe_inrHom]
        at he he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_map_inr e₁ e₀ hee
    · simp only [sumWalk, SimpleGraph.Walk.edges_map, List.mem_map, coe_inrHom] at he he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact f'.edgeDisjoint' (by simpa using h) (by simpa using h')
        (fun eq ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inr) eq))
        e₀ he₀ (Sym2.map.injective Sum.inr_injective hee ▸ he₁)

/-- The trail replacing an edge of a join: an edge inside a summand keeps that summand's trail, and
an edge across is an edge of the join already. -/
def joinWalk (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    ∀ (x y : (A ∇g A').V), (A ∇g A').Adj x y →
      (B ∇g B').toSimple.Walk (Sum.map f.toFun f'.toFun x) (Sum.map f.toFun f'.toFun y)
  | Sum.inl _, Sum.inl _, h => (f.walk (by simpa using h)).map (joinInlHom B B')
  | Sum.inl _, Sum.inr _, _ => .cons (toSimple_join_inl_inr B B' _ _) .nil
  | Sum.inr _, Sum.inl _, _ => .cons (toSimple_join_inr_inl B B' _ _) .nil
  | Sum.inr _, Sum.inr _, h => (f'.walk (by simpa using h)).map (joinInrHom B B')

/-- **The join of two immersions.** -/
def join (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    (A ∇g A').ImmersionOf (B ∇g B') where
  toFun := Sum.map f.toFun f'.toFun
  injective' := f.injective.sumMap f'.injective
  walk {x y} h := joinWalk f f' x y h
  isTrail' := by
    rintro (a | b) (c | d) h
    · exact SimpleGraph.Walk.map_isTrail_of_injective
        (fun _ _ hh ↦ Sum.inl_injective hh) (f.isTrail' _)
    · simp [joinWalk]
    · simp [joinWalk]
    · exact SimpleGraph.Walk.map_isTrail_of_injective
        (fun _ _ hh ↦ Sum.inr_injective hh) (f'.isTrail' _)
  reverse' := by
    rintro (a | b) (c | d) h h'
    · show (f.walk _).map (joinInlHom B B') = ((f.walk _).map (joinInlHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f.reverse' (show A.Adj a c by simpa using h)]
    · show SimpleGraph.Walk.cons _ _ = _
      simp [joinWalk]
    · show SimpleGraph.Walk.cons _ _ = _
      simp [joinWalk]
    · show (f'.walk _).map (joinInrHom B B') = ((f'.walk _).map (joinInrHom B B')).reverse
      rw [SimpleGraph.Walk.reverse_map, f'.reverse' (show A'.Adj b d by simpa using h)]
  edgeDisjoint' := by
    rintro (a | b) (c | d) h (a' | b') (c' | d') h' hne e he he'
    all_goals simp only [joinWalk, SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      coe_joinInlHom, coe_joinInrHom] at he he'
    · obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact f.edgeDisjoint' (by simpa using h) (by simpa using h')
        (fun eq ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inl) eq))
        e₀ he₀ (Sym2.map.injective Sum.inl_injective hee ▸ he₁)
    · obtain ⟨e₀, he₀, rfl⟩ := he
      exact sym2_map_inl_ne_cross e₀ _ _ he'
    · obtain ⟨e₀, he₀, rfl⟩ := he
      exact sym2_map_inl_ne_cross' e₀ _ _ he'
    · obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_map_inr e₀ e₁ hee.symm
    · obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_cross e₁ _ _ (hee.trans he)
    · obtain ⟨hu, hv⟩ := sym2_cross_eq (he.symm.trans he')
      exact hne (by rw [f.injective hu, f'.injective hv])
    · obtain ⟨hu, hv⟩ := sym2_cross_eq' (he.symm.trans he')
      exact hne (by rw [f.injective hu, f'.injective hv]; exact Sym2.eq_swap)
    · obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inr_ne_cross e₁ _ _ (hee.trans he)
    · obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_cross' e₁ _ _ (hee.trans he)
    · obtain ⟨hu, hv⟩ := sym2_cross_eq' (he'.symm.trans he)
      exact hne (by rw [f.injective hu, f'.injective hv]; exact Sym2.eq_swap)
    · obtain ⟨hu, hv⟩ := sym2_cross_eq'' (he.symm.trans he')
      exact hne (by rw [f.injective hu, f'.injective hv])
    · obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inr_ne_cross' e₁ _ _ (hee.trans he)
    · obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact sym2_map_inl_ne_map_inr e₁ e₀ hee
    · obtain ⟨e₀, he₀, rfl⟩ := he
      exact sym2_map_inr_ne_cross e₀ _ _ he'
    · obtain ⟨e₀, he₀, rfl⟩ := he
      exact sym2_map_inr_ne_cross' e₀ _ _ he'
    · obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, hee⟩ := he'
      exact f'.edgeDisjoint' (by simpa using h) (by simpa using h')
        (fun eq ↦ hne (by simpa only [Sym2.map_pair_eq] using congrArg (Sym2.map Sum.inr) eq))
        e₀ he₀ (Sym2.map.injective Sum.inr_injective hee ▸ he₁)

/-- The trail replacing an edge of a cartesian product. -/
def prodWalk (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    ∀ (x y : A.V × A'.V), (A □g A').Adj x y →
      (B □g B').toSimple.Walk (Prod.map f.toFun f'.toFun x) (Prod.map f.toFun f'.toFun y)
  | (x₁, x₂), (y₁, y₂), h =>
    if hx : x₁ = y₁ then
      ((f'.walk (cartesianProduct_adj_of_fst_eq h hx)).map (sndHom B B' (f.toFun x₁))).copy rfl
        (by rw [hx]; rfl)
    else
      ((f.walk (cartesianProduct_adj_of_fst_ne h hx).1).map (fstHom B B' (f'.toFun x₂))).copy rfl
        (by rw [(cartesianProduct_adj_of_fst_ne h hx).2]; rfl)

/-- An edge along the second coordinate takes the second factor's trail, in one column. -/
theorem prodWalk_col (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') {x₁ : A.V} {x₂ y₂ : A'.V}
    (h : (A □g A').Adj (x₁, x₂) (x₁, y₂)) (ha : A'.Adj x₂ y₂) :
    prodWalk f f' (x₁, x₂) (x₁, y₂) h = (f'.walk ha).map (sndHom B B' (f.toFun x₁)) := by
  rw [prodWalk, dif_pos rfl]
  rfl

/-- An edge along the first coordinate takes the first factor's trail, in one row. -/
theorem prodWalk_row (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') {x₁ y₁ : A.V} {x₂ : A'.V}
    (hx : x₁ ≠ y₁) (h : (A □g A').Adj (x₁, x₂) (y₁, x₂)) (ha : A.Adj x₁ y₁) :
    prodWalk f f' (x₁, x₂) (y₁, x₂) h = (f.walk ha).map (fstHom B B' (f'.toFun x₂)) := by
  rw [prodWalk, dif_neg hx]
  rfl

/-- An immersion of each factor is an immersion of the cartesian product. -/
def cartesianProduct (f : A.ImmersionOf B) (f' : A'.ImmersionOf B') :
    (A □g A').ImmersionOf (B □g B') where
  toFun := Prod.map f.toFun f'.toFun
  injective' := f.injective.prodMap f'.injective
  walk {x y} h := prodWalk f f' x y h
  isTrail' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    by_cases hx : x₁ = y₁
    · subst hx
      rw [prodWalk_col f f' h (cartesianProduct_adj_of_fst_eq h rfl)]
      exact SimpleGraph.Walk.map_isTrail_of_injective (sndHom_injective B B' _) (f'.isTrail' _)
    · obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      rw [prodWalk_row f f' hx h ha]
      exact SimpleGraph.Walk.map_isTrail_of_injective (fstHom_injective B B' _) (f.isTrail' _)
  reverse' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h h'
    by_cases hx : x₁ = y₁
    · subst hx
      rw [prodWalk_col f f' h (cartesianProduct_adj_of_fst_eq h rfl),
        prodWalk_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl),
        SimpleGraph.Walk.reverse_map,
        f'.reverse' (cartesianProduct_adj_of_fst_eq h rfl)]
    · obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      obtain ⟨ha', -⟩ := cartesianProduct_adj_of_fst_ne h' (Ne.symm hx)
      rw [prodWalk_row f f' (Ne.symm hx) h' ha', prodWalk_row f f' hx h ha,
        SimpleGraph.Walk.reverse_map, f.reverse' ha]
  edgeDisjoint' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h ⟨x₁', x₂'⟩ ⟨y₁', y₂'⟩ h' hne e he he'
    by_cases hx : x₁ = y₁ <;> by_cases hx' : x₁' = y₁'
    · -- two columns
      subst hx
      subst hx'
      rw [prodWalk_col f f' h (cartesianProduct_adj_of_fst_eq h rfl), mem_edges_sndHom] at he
      rw [prodWalk_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl), mem_edges_sndHom] at he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, he₂⟩ := he'
      have hxx : x₁ = x₁' := f.injective (sym2_map_col_eq he₂.symm)
      subst hxx
      refine f'.edgeDisjoint' (cartesianProduct_adj_of_fst_eq h rfl)
        (cartesianProduct_adj_of_fst_eq h' rfl) (sym2_col_ne hne) e₀ he₀ ?_
      exact (Sym2.map.injective (sndHom_injective B B' (f.toFun x₁)) he₂.symm) ▸ he₁
    · -- a column and a row
      subst hx
      obtain ⟨ha', rfl⟩ := cartesianProduct_adj_of_fst_ne h' hx'
      rw [prodWalk_col f f' h (cartesianProduct_adj_of_fst_eq h rfl), mem_edges_sndHom] at he
      rw [prodWalk_row f f' hx' h' ha', mem_edges_fstHom] at he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, -, he₂⟩ := he'
      exact sym2_map_col_ne_row
        (SimpleGraph.not_isDiag_of_mem_edgeSet _
          (SimpleGraph.Walk.edges_subset_edgeSet _ he₀)) he₂.symm
    · -- a row and a column
      subst hx'
      obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      rw [prodWalk_row f f' hx h ha, mem_edges_fstHom] at he
      rw [prodWalk_col f f' h' (cartesianProduct_adj_of_fst_eq h' rfl), mem_edges_sndHom] at he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, he₂⟩ := he'
      exact sym2_map_col_ne_row
        (SimpleGraph.not_isDiag_of_mem_edgeSet _
          (SimpleGraph.Walk.edges_subset_edgeSet _ he₁)) he₂
    · -- two rows
      obtain ⟨ha, rfl⟩ := cartesianProduct_adj_of_fst_ne h hx
      obtain ⟨ha', rfl⟩ := cartesianProduct_adj_of_fst_ne h' hx'
      rw [prodWalk_row f f' hx h ha, mem_edges_fstHom] at he
      rw [prodWalk_row f f' hx' h' ha', mem_edges_fstHom] at he'
      obtain ⟨e₀, he₀, rfl⟩ := he
      obtain ⟨e₁, he₁, he₂⟩ := he'
      have hxx : x₂ = x₂' := f'.injective (sym2_map_row_eq he₂.symm)
      subst hxx
      refine f.edgeDisjoint' ha ha' (sym2_row_ne hne) e₀ he₀ ?_
      exact (Sym2.map.injective (fstHom_injective B B' (f'.toFun x₂)) he₂.symm) ▸ he₁

end ImmersionOf

end CGraph

namespace IsoGraph

/-- Lift a construction on the `CGraph` models of a relation to the classes. -/
theorem mono₂ {r : IsoGraph → IsoGraph → Prop} {R : CGraph → CGraph → Type}
    {opI : IsoGraph → IsoGraph → IsoGraph} {op : CGraph → CGraph → CGraph}
    (hr : ∀ a b : CGraph, r ⟦a⟧ ⟦b⟧ ↔ Nonempty (R a b))
    (hop : ∀ a b : CGraph, opI ⟦a⟧ ⟦b⟧ = ⟦op a b⟧)
    (mk : ∀ {a b c d : CGraph}, R a b → R c d → R (op a c) (op b d))
    {H G H' G' : IsoGraph} (h : r H G) (h' : r H' G') : r (opI H H') (opI G G') := by
  revert h h'
  induction H, G using Quotient.inductionOn₂ with
  | h a b =>
    induction H', G' using Quotient.inductionOn₂ with
    | h c d =>
      rw [hr, hr, hop, hop, hr]
      rintro ⟨f⟩ ⟨f'⟩
      exact ⟨mk f f'⟩

variable {H G H' G' : IsoGraph}

theorem HasHomInto.disjUnion (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H ⊕g H' ≤ₕ G ⊕g G' :=
  mono₂ hasHomInto_mk disjUnion_mk CGraph.Hom.disjUnion h h'

theorem HasHomInto.join (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H ∇g H' ≤ₕ G ∇g G' :=
  mono₂ hasHomInto_mk join_mk CGraph.Hom.join h h'

theorem IsSubgraphOf.disjUnion (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H ⊕g H' ≤ₛ G ⊕g G' :=
  mono₂ isSubgraphOf_mk disjUnion_mk CGraph.SubgraphOf.disjUnion h h'

theorem IsSubgraphOf.join (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H ∇g H' ≤ₛ G ∇g G' :=
  mono₂ isSubgraphOf_mk join_mk CGraph.SubgraphOf.join h h'

theorem IsInducedSubgraphOf.disjUnion (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H ⊕g H' ≤ᵢₛ G ⊕g G' :=
  mono₂ isInducedSubgraphOf_mk disjUnion_mk CGraph.InducedSubgraphOf.disjUnion h h'

theorem IsInducedSubgraphOf.join (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H ∇g H' ≤ᵢₛ G ∇g G' :=
  mono₂ isInducedSubgraphOf_mk join_mk CGraph.InducedSubgraphOf.join h h'

theorem HasQuotient.disjUnion (h : H ≤/ G) (h' : H' ≤/ G') : H ⊕g H' ≤/ G ⊕g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk disjUnion_mk
    CGraph.QuotientOf.disjUnion h h'

theorem HasQuotient.join (h : H ≤/ G) (h' : H' ≤/ G') : H ∇g H' ≤/ G ∇g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk join_mk
    CGraph.QuotientOf.join h h'

theorem IsMinorOf.disjUnion (h : H ≤ₘ G) (h' : H' ≤ₘ G') : H ⊕g H' ≤ₘ G ⊕g G' :=
  mono₂ isMinorOf_mk disjUnion_mk CGraph.MinorOf.disjUnion h h'

theorem IsMinorOf.join (h : H ≤ₘ G) (h' : H' ≤ₘ G') : H ∇g H' ≤ₘ G ∇g G' :=
  mono₂ isMinorOf_mk join_mk CGraph.MinorOf.join h h'

theorem IsInducedMinorOf.disjUnion (h : H ≤ᵢₘ G) (h' : H' ≤ᵢₘ G') : H ⊕g H' ≤ᵢₘ G ⊕g G' :=
  mono₂ isInducedMinorOf_mk disjUnion_mk CGraph.InducedMinorOf.disjUnion h h'

theorem IsInducedMinorOf.join (h : H ≤ᵢₘ G) (h' : H' ≤ᵢₘ G') : H ∇g H' ≤ᵢₘ G ∇g G' :=
  mono₂ isInducedMinorOf_mk join_mk CGraph.InducedMinorOf.join h h'

theorem IsContractionOf.disjUnion (h : H ≤ₚ G) (h' : H' ≤ₚ G') : H ⊕g H' ≤ₚ G ⊕g G' :=
  mono₂ isContractionOf_mk disjUnion_mk CGraph.ContractionOf.disjUnion h h'

theorem IsContractionOf.join (h : H ≤ₚ G) (h' : H' ≤ₚ G') : H ∇g H' ≤ₚ G ∇g G' :=
  mono₂ isContractionOf_mk join_mk CGraph.ContractionOf.join h h'

theorem IsTopMinorOf.disjUnion (h : H ≤ₜₘ G) (h' : H' ≤ₜₘ G') : H ⊕g H' ≤ₜₘ G ⊕g G' :=
  mono₂ isTopMinorOf_mk disjUnion_mk CGraph.TopMinorOf.disjUnion h h'

theorem IsTopMinorOf.join (h : H ≤ₜₘ G) (h' : H' ≤ₜₘ G') : H ∇g H' ≤ₜₘ G ∇g G' :=
  mono₂ isTopMinorOf_mk join_mk CGraph.TopMinorOf.join h h'

theorem IsImmersionMinorOf.disjUnion (h : H ≤ₑ G) (h' : H' ≤ₑ G') : H ⊕g H' ≤ₑ G ⊕g G' :=
  mono₂ isImmersionMinorOf_mk disjUnion_mk CGraph.ImmersionOf.disjUnion h h'

theorem IsImmersionMinorOf.join (h : H ≤ₑ G) (h' : H' ≤ₑ G') : H ∇g H' ≤ₑ G ∇g G' :=
  mono₂ isImmersionMinorOf_mk join_mk CGraph.ImmersionOf.join h h'

theorem HasHomInto.cartesianProduct (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H □g H' ≤ₕ G □g G' :=
  mono₂ hasHomInto_mk cartesianProduct_mk CGraph.Hom.cartesianProduct h h'

theorem IsSubgraphOf.cartesianProduct (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H □g H' ≤ₛ G □g G' :=
  mono₂ isSubgraphOf_mk cartesianProduct_mk CGraph.SubgraphOf.cartesianProduct h h'

theorem IsInducedSubgraphOf.cartesianProduct (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H □g H' ≤ᵢₛ G □g G' :=
  mono₂ isInducedSubgraphOf_mk cartesianProduct_mk CGraph.InducedSubgraphOf.cartesianProduct h h'

theorem HasQuotient.cartesianProduct (h : H ≤/ G) (h' : H' ≤/ G') : H □g H' ≤/ G □g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk cartesianProduct_mk
    CGraph.QuotientOf.cartesianProduct h h'

theorem IsMinorOf.cartesianProduct (h : H ≤ₘ G) (h' : H' ≤ₘ G') : H □g H' ≤ₘ G □g G' :=
  mono₂ isMinorOf_mk cartesianProduct_mk CGraph.MinorOf.cartesianProduct h h'

theorem IsInducedMinorOf.cartesianProduct (h : H ≤ᵢₘ G) (h' : H' ≤ᵢₘ G') : H □g H' ≤ᵢₘ G □g G' :=
  mono₂ isInducedMinorOf_mk cartesianProduct_mk CGraph.InducedMinorOf.cartesianProduct h h'

theorem IsContractionOf.cartesianProduct (h : H ≤ₚ G) (h' : H' ≤ₚ G') : H □g H' ≤ₚ G □g G' :=
  mono₂ isContractionOf_mk cartesianProduct_mk CGraph.ContractionOf.cartesianProduct h h'

theorem IsTopMinorOf.cartesianProduct (h : H ≤ₜₘ G) (h' : H' ≤ₜₘ G') : H □g H' ≤ₜₘ G □g G' :=
  mono₂ isTopMinorOf_mk cartesianProduct_mk CGraph.TopMinorOf.cartesianProduct h h'

theorem IsImmersionMinorOf.cartesianProduct (h : H ≤ₑ G) (h' : H' ≤ₑ G') : H □g H' ≤ₑ G □g G' :=
  mono₂ isImmersionMinorOf_mk cartesianProduct_mk CGraph.ImmersionOf.cartesianProduct h h'

theorem HasHomInto.tensorProduct (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H ⊗g H' ≤ₕ G ⊗g G' :=
  mono₂ hasHomInto_mk tensorProduct_mk CGraph.Hom.tensorProduct h h'

theorem IsSubgraphOf.tensorProduct (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H ⊗g H' ≤ₛ G ⊗g G' :=
  mono₂ isSubgraphOf_mk tensorProduct_mk CGraph.SubgraphOf.tensorProduct h h'

theorem IsInducedSubgraphOf.tensorProduct (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H ⊗g H' ≤ᵢₛ G ⊗g G' :=
  mono₂ isInducedSubgraphOf_mk tensorProduct_mk CGraph.InducedSubgraphOf.tensorProduct h h'

theorem HasQuotient.tensorProduct (h : H ≤/ G) (h' : H' ≤/ G') : H ⊗g H' ≤/ G ⊗g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk tensorProduct_mk
    CGraph.QuotientOf.tensorProduct h h'

theorem HasHomInto.strongProduct (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H ⊠g H' ≤ₕ G ⊠g G' :=
  mono₂ hasHomInto_mk strongProduct_mk CGraph.Hom.strongProduct h h'

theorem IsSubgraphOf.strongProduct (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H ⊠g H' ≤ₛ G ⊠g G' :=
  mono₂ isSubgraphOf_mk strongProduct_mk CGraph.SubgraphOf.strongProduct h h'

theorem IsInducedSubgraphOf.strongProduct (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H ⊠g H' ≤ᵢₛ G ⊠g G' :=
  mono₂ isInducedSubgraphOf_mk strongProduct_mk CGraph.InducedSubgraphOf.strongProduct h h'

theorem HasQuotient.strongProduct (h : H ≤/ G) (h' : H' ≤/ G') : H ⊠g H' ≤/ G ⊠g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk strongProduct_mk
    CGraph.QuotientOf.strongProduct h h'

theorem IsMinorOf.strongProduct (h : H ≤ₘ G) (h' : H' ≤ₘ G') : H ⊠g H' ≤ₘ G ⊠g G' :=
  mono₂ isMinorOf_mk strongProduct_mk CGraph.MinorOf.strongProduct h h'

theorem IsInducedMinorOf.strongProduct (h : H ≤ᵢₘ G) (h' : H' ≤ᵢₘ G') : H ⊠g H' ≤ᵢₘ G ⊠g G' :=
  mono₂ isInducedMinorOf_mk strongProduct_mk CGraph.InducedMinorOf.strongProduct h h'

theorem IsContractionOf.strongProduct (h : H ≤ₚ G) (h' : H' ≤ₚ G') : H ⊠g H' ≤ₚ G ⊠g G' :=
  mono₂ isContractionOf_mk strongProduct_mk CGraph.ContractionOf.strongProduct h h'

theorem HasHomInto.lexProduct (h : H ≤ₕ G) (h' : H' ≤ₕ G') : H ·g H' ≤ₕ G ·g G' :=
  mono₂ hasHomInto_mk lexProduct_mk CGraph.Hom.lexProduct h h'

theorem IsSubgraphOf.lexProduct (h : H ≤ₛ G) (h' : H' ≤ₛ G') : H ·g H' ≤ₛ G ·g G' :=
  mono₂ isSubgraphOf_mk lexProduct_mk CGraph.SubgraphOf.lexProduct h h'

theorem IsInducedSubgraphOf.lexProduct (h : H ≤ᵢₛ G) (h' : H' ≤ᵢₛ G') : H ·g H' ≤ᵢₛ G ·g G' :=
  mono₂ isInducedSubgraphOf_mk lexProduct_mk CGraph.InducedSubgraphOf.lexProduct h h'

theorem HasQuotient.lexProduct (h : H ≤/ G) (h' : H' ≤/ G') : H ·g H' ≤/ G ·g G' :=
  mono₂ (R := fun a b ↦ b.QuotientOf a) hasQuotient_mk lexProduct_mk
    CGraph.QuotientOf.lexProduct h h'

theorem IsMinorOf.lexProduct (h : H ≤ₘ G) (h' : H' ≤ₘ G') : H ·g H' ≤ₘ G ·g G' :=
  mono₂ isMinorOf_mk lexProduct_mk CGraph.MinorOf.lexProduct h h'

end IsoGraph
