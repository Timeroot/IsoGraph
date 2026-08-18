import IsoGraph.Graphs.Constructions

/-!
# Clique sums

Gluing two graphs along a shared clique.  Only the two smallest cases are here:

* the **one-clique sum** `oneCliqueSum G H`, which identifies a vertex of `G` with a vertex
  of `H`;
* the **two-clique sum** `twoCliqueSum G H`, which identifies an edge of `G` with an edge of `H`.

Both are built from a version that takes the glued vertices (resp. edges) explicitly —
`vertexSum` and `edgeSum` — on the vertex type `G.V ⊕ {v : H.V // v ≠ w}`, so nothing is
quotiented: the copy of `H` simply loses the vertices that `G` already provides, and the
neighbours they had in `H` are re-attached to the corresponding vertices of `G`.

## Why the choice does not matter

Writing `oneCliqueSum G H` without saying *where* to glue is only honest if the answer does not
depend on it, which is exactly what transitivity buys:

* `vertexSum_iso`: if `G` and `H` are vertex-transitive, any two choices of glueing vertices give
  isomorphic graphs;
* `edgeSum_iso`: if `G` and `H` are arc-transitive, any two choices of glueing edges do.

So the distinguished vertex and edge supplied by the `Pointed` and `EdgePointed` classes below
are a matter of convenience, not of definition, and `oneCliqueSum_iso` / `twoCliqueSum_iso` say
so.  (The classes are needed because a `Fintype` is a `Multiset`, from which no *computable*
"first vertex" can be extracted; a distinguished vertex has to be supplied, not found.)

## What it is good for

Several of the graphs in `IsoGraph/Graphs/NamedSmallGraphs.lean` are clique sums, and saying so is
clearer than the complement-of-a-disjoint-union spellings they had before:

    paw       = oneCliqueSum K₃ K₂          butterfly = oneCliqueSum K₃ K₃
    diamond   = twoCliqueSum K₃ K₃          house     = twoCliqueSum K₃ C₄
    domino    = twoCliqueSum C₄ C₄
-/

namespace CGraph

/-! ## Gluing at a given vertex or edge -/

/-- Glue `H` to `G` by identifying the vertex `w` of `H` with the vertex `u` of `G`: the vertices
are those of `G` together with those of `H` other than `w`, and a leftover vertex of `H` is joined
to `u` exactly when it was joined to `w`. -/
def vertexSum (G : CGraph) (u : G.V) (H : CGraph) (w : H.V) :
    CGraph where
  V := G.V ⊕ {v : H.V // v ≠ w}
  Adj x y :=
    match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => decide (a = u) && H.Adj w b.1
    | .inr a, .inl b => decide (b = u) && H.Adj w a.1
    | .inr a, .inr b => H.Adj a.1 b.1
  symm x y := by
    cases x <;> cases y <;> simp [G.symm, H.symm]
  loopless x := by
    cases x <;> simp [G.loopless, H.loopless]

@[simp] theorem card_vertexSum (G : CGraph) (u : G.V) (H : CGraph)
 (w : H.V) :
    FinEnum.card (vertexSum G u H w).V = FinEnum.card G.V + (FinEnum.card H.V - 1) := by
  rw [show FinEnum.card (vertexSum G u H w).V = Fintype.card (G.V ⊕ {v : H.V // v ≠ w}) from
      FinEnum.card_eq_fintypeCard.trans (Fintype.card_congr' rfl),
    Fintype.card_sum, Fintype.card_subtype_compl fun v ↦ v = w, Fintype.card_subtype_eq,
    ← FinEnum.card_eq_fintypeCard (α := G.V), ← FinEnum.card_eq_fintypeCard (α := H.V)]

/-- Glue `H` to `G` by identifying the edge `w₁w₂` of `H` with the edge `u₁u₂` of `G`. -/
def edgeSum (G : CGraph) (u₁ u₂ : G.V) (H : CGraph)
    (w₁ w₂ : H.V) : CGraph where
  V := G.V ⊕ {v : H.V // v ≠ w₁ ∧ v ≠ w₂}
  Adj x y :=
    match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => (decide (a = u₁) && H.Adj w₁ b.1) || (decide (a = u₂) && H.Adj w₂ b.1)
    | .inr a, .inl b => (decide (b = u₁) && H.Adj w₁ a.1) || (decide (b = u₂) && H.Adj w₂ a.1)
    | .inr a, .inr b => H.Adj a.1 b.1
  symm x y := by
    cases x <;> cases y <;> simp [G.symm, H.symm]
  loopless x := by
    cases x <;> simp [G.loopless, H.loopless]

theorem card_edgeSum (G : CGraph) (u₁ u₂ : G.V) (H : CGraph)
    {w₁ w₂ : H.V} (h : w₁ ≠ w₂) :
    FinEnum.card (edgeSum G u₁ u₂ H w₁ w₂).V = FinEnum.card G.V + (FinEnum.card H.V - 2) := by
  rw [show FinEnum.card (edgeSum G u₁ u₂ H w₁ w₂).V
      = Fintype.card (G.V ⊕ {v : H.V // v ≠ w₁ ∧ v ≠ w₂}) from
    FinEnum.card_eq_fintypeCard.trans (Fintype.card_congr' rfl)]
  have e : Fintype.card {v : H.V // v ≠ w₁ ∧ v ≠ w₂} =
      Fintype.card {v : H.V // ¬(v = w₁ ∨ v = w₂)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun v ↦ by simp [not_or])
  have h2 : Fintype.card {v : H.V // v = w₁ ∨ v = w₂} = 2 := by
    rw [Fintype.card_subtype,
      show (Finset.univ.filter fun v : H.V ↦ v = w₁ ∨ v = w₂) = {w₁, w₂} by ext v; simp,
      Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]
  rw [Fintype.card_sum, e, Fintype.card_subtype_compl, h2,
    ← FinEnum.card_eq_fintypeCard (α := G.V), ← FinEnum.card_eq_fintypeCard (α := H.V)]

/-! ## Independence of the choice -/

/-- Gluing at any pair of vertices gives the same graph up to isomorphism, provided both sides are
vertex-transitive: move `u` to `u'` and `w` to `w'` by automorphisms, and the two sums correspond
vertex by vertex. -/
theorem vertexSum_iso (G : CGraph) (H : CGraph)
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) (u u' : G.V) (w w' : H.V) :
    Nonempty (vertexSum G u H w ≃cg vertexSum G u' H w') := by
  obtain ⟨σ, hσ⟩ := hG u u'
  obtain ⟨τ, hτ⟩ := hH w w'
  have hτne : ∀ v : H.V, v ≠ w ↔ τ v ≠ w' := by
    intro v
    rw [← hτ, (RelIso.injective τ).ne_iff]
  refine ⟨⟨Equiv.sumCongr σ.toEquiv (Equiv.subtypeEquiv τ.toEquiv fun v ↦ hτne v), ?_⟩⟩
  intro x y
  cases x with
  | inl a => cases y with
    | inl b =>
        show (G.Adj (σ a) (σ b) = true) ↔ (G.Adj a b = true)
        rw [σ.adj_eq]
    | inr b =>
        show ((decide (σ a = u') && H.Adj w' (τ b.1)) = true) ↔
          ((decide (a = u) && H.Adj w b.1) = true)
        rw [← hσ, ← hτ, τ.adj_eq]
        simp [(RelIso.injective σ).eq_iff]
  | inr a => cases y with
    | inl b =>
        show ((decide (σ b = u') && H.Adj w' (τ a.1)) = true) ↔
          ((decide (b = u) && H.Adj w a.1) = true)
        rw [← hσ, ← hτ, τ.adj_eq]
        simp [(RelIso.injective σ).eq_iff]
    | inr b =>
        show (H.Adj (τ a.1) (τ b.1) = true) ↔ (H.Adj a.1 b.1 = true)
        rw [τ.adj_eq]

/-- Gluing along any pair of edges gives the same graph up to isomorphism, provided both sides are
arc-transitive.  Arc- rather than merely edge-transitivity is what is needed: the two endpoints
have to be matched up in a prescribed order. -/
theorem edgeSum_iso (G : CGraph) (H : CGraph)
    (hG : G.IsArcTransitive) (hH : H.IsArcTransitive) {u₁ u₂ u₁' u₂' : G.V}
    {w₁ w₂ w₁' w₂' : H.V} (hu : G.Adj u₁ u₂) (hu' : G.Adj u₁' u₂') (hw : H.Adj w₁ w₂)
    (hw' : H.Adj w₁' w₂') :
    Nonempty (edgeSum G u₁ u₂ H w₁ w₂ ≃cg edgeSum G u₁' u₂' H w₁' w₂') := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := hG u₁ u₂ u₁' u₂' hu hu'
  obtain ⟨τ, hτ₁, hτ₂⟩ := hH w₁ w₂ w₁' w₂' hw hw'
  have hτne : ∀ v : H.V, (v ≠ w₁ ∧ v ≠ w₂) ↔ (τ v ≠ w₁' ∧ τ v ≠ w₂') := by
    intro v
    rw [← hτ₁, ← hτ₂, (RelIso.injective τ).ne_iff, (RelIso.injective τ).ne_iff]
  refine ⟨⟨Equiv.sumCongr σ.toEquiv (Equiv.subtypeEquiv τ.toEquiv fun v ↦ hτne v), ?_⟩⟩
  intro x y
  cases x with
  | inl a => cases y with
    | inl b =>
        show (G.Adj (σ a) (σ b) = true) ↔ (G.Adj a b = true)
        rw [σ.adj_eq]
    | inr b =>
        show (((decide (σ a = u₁') && H.Adj w₁' (τ b.1)) ||
          (decide (σ a = u₂') && H.Adj w₂' (τ b.1))) = true) ↔
          (((decide (a = u₁) && H.Adj w₁ b.1) || (decide (a = u₂) && H.Adj w₂ b.1)) = true)
        rw [← hσ₁, ← hσ₂, ← hτ₁, ← hτ₂, τ.adj_eq, τ.adj_eq]
        simp [(RelIso.injective σ).eq_iff]
  | inr a => cases y with
    | inl b =>
        show (((decide (σ b = u₁') && H.Adj w₁' (τ a.1)) ||
          (decide (σ b = u₂') && H.Adj w₂' (τ a.1))) = true) ↔
          (((decide (b = u₁) && H.Adj w₁ a.1) || (decide (b = u₂) && H.Adj w₂ a.1)) = true)
        rw [← hσ₁, ← hσ₂, ← hτ₁, ← hτ₂, τ.adj_eq, τ.adj_eq]
        simp [(RelIso.injective σ).eq_iff]
    | inr b =>
        show (H.Adj (τ a.1) (τ b.1) = true) ↔ (H.Adj a.1 b.1 = true)
        rw [τ.adj_eq]

/-! ## Distinguished vertices and edges -/

/-- A graph with a distinguished vertex, for `oneCliqueSum` to glue at.  For a vertex-transitive
graph the choice is immaterial — see `oneCliqueSum_iso`. -/
class Pointed (G : CGraph) where
  /-- The distinguished vertex. -/
  pt : G.V

/-- A graph with a distinguished edge, for `twoCliqueSum` to glue along.  For an arc-transitive
graph the choice is immaterial — see `twoCliqueSum_iso`. -/
class EdgePointed (G : CGraph) where
  /-- The first endpoint of the distinguished edge. -/
  fst : G.V
  /-- The second endpoint of the distinguished edge. -/
  snd : G.V
  /-- The endpoints are indeed adjacent. -/
  adj : G.Adj fst snd

instance (n : ℕ) : Pointed (empty (n + 1)) := ⟨(0 : Fin (n + 1))⟩
instance (n : ℕ) : Pointed (complete (n + 1)) := ⟨(0 : Fin (n + 1))⟩
instance (n : ℕ) : Pointed (cycle (n + 1)) := ⟨(0 : Fin (n + 1))⟩
instance (n : ℕ) : Pointed (path (n + 1)) := ⟨(0 : Fin (n + 1))⟩

instance (n : ℕ) : EdgePointed (complete (n + 2)) where
  fst := (0 : Fin (n + 2))
  snd := (1 : Fin (n + 2))
  adj := by
    simp only [complete, compl_adj, empty_adj, Bool.not_false, Bool.and_true, decide_eq_true_eq,
      ne_eq]
    exact Fin.ne_of_val_ne (by simp)

instance (n : ℕ) : EdgePointed (cycle (n + 2)) where
  fst := (0 : Fin (n + 2))
  snd := (1 : Fin (n + 2))
  adj := by simp [cycle]

/-! ## The clique sums -/

/-- The **one-clique sum**: `G` and `H` glued at a single vertex. -/
def oneCliqueSum (G H : CGraph) [Pointed G] [Pointed H] :
    CGraph :=
  vertexSum G Pointed.pt H Pointed.pt

/-- The **two-clique sum**: `G` and `H` glued along a single edge. -/
def twoCliqueSum (G H : CGraph) [EdgePointed G]
    [EdgePointed H] : CGraph :=
  edgeSum G EdgePointed.fst EdgePointed.snd H EdgePointed.fst EdgePointed.snd

@[simp] theorem card_oneCliqueSum (G H : CGraph) [Pointed G]
    [Pointed H] :
    FinEnum.card (oneCliqueSum G H).V = FinEnum.card G.V + (FinEnum.card H.V - 1) :=
  card_vertexSum _ _ _ _

theorem card_twoCliqueSum (G H : CGraph) [EdgePointed G]
    [EdgePointed H] (h : (EdgePointed.fst : H.V) ≠ EdgePointed.snd) :
    FinEnum.card (twoCliqueSum G H).V = FinEnum.card G.V + (FinEnum.card H.V - 2) :=
  card_edgeSum _ _ _ _ h

/-- The one-clique sum of vertex-transitive graphs really is *the* one-clique sum: gluing at the
distinguished vertices gives the same graph as gluing anywhere else. -/
theorem oneCliqueSum_iso (G H : CGraph) [Pointed G] [Pointed H]
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) (u : G.V) (w : H.V) :
    Nonempty (oneCliqueSum G H ≃cg vertexSum G u H w) :=
  vertexSum_iso G H hG hH _ u _ w

/-- The two-clique sum of arc-transitive graphs really is *the* two-clique sum. -/
theorem twoCliqueSum_iso (G H : CGraph) [EdgePointed G]
    [EdgePointed H] (hG : G.IsArcTransitive) (hH : H.IsArcTransitive) {u₁ u₂ : G.V} {w₁ w₂ : H.V}
    (hu : G.Adj u₁ u₂) (hw : H.Adj w₁ w₂) :
    Nonempty (twoCliqueSum G H ≃cg edgeSum G u₁ u₂ H w₁ w₂) :=
  edgeSum_iso G H hG hH EdgePointed.adj hu EdgePointed.adj hw

end CGraph
