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
| `≤ₜₘ` topological minor | ? | ? | ? | ? | ? | ? |
| `≤ₑ` immersion | ? | ? | ? | ? | ? | ? |

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
two relations, which replace an edge by a path or a trail, are not attempted at all.
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

theorem prodBranch_eq_some (f : A.MinorOf B) (f' : A'.MinorOf B') {p : B.V × B'.V} {q : A.V × A'.V} :
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
  adj_map' := cartesianProduct_adj_map f.injective f'.injective (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

def tensorProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ⊗g A').InducedSubgraphOf (B ⊗g B') where
  toSubgraphOf := f.toSubgraphOf.tensorProduct f'.toSubgraphOf
  adj_map' := tensorProduct_adj_map (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

def strongProduct (f : A.InducedSubgraphOf B) (f' : A'.InducedSubgraphOf B') :
    (A ⊠g A').InducedSubgraphOf (B ⊠g B') where
  toSubgraphOf := f.toSubgraphOf.strongProduct f'.toSubgraphOf
  adj_map' := strongProduct_adj_map f.injective f'.injective (fun _ _ ↦ f.adj_map) (fun _ _ ↦ f'.adj_map)

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
