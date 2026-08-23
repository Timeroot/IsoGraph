import IsoGraph.Algebra.Connected

/-!
# Unique factorisation of connected graphs

Unique factorisation fails in the graph semiring: `IsoGraph.Semiring.exists_factorisations_ne`
exhibits a graph with two genuinely different factorisations into irreducibles.  The graph there is
disconnected, and that is the whole story — Sabidussi (1960) and Vizing (1963) proved that a
connected graph factors uniquely into irreducibles under the cartesian product.  This file proves
that theorem.

## Packaging

The connected graphs are a `Submonoid` of `IsoGraph` under the cartesian product, not a
`MonoidWithZero`: the empty graph is not connected, so there is no zero to be had.  Mathlib's
`UniqueFactorizationMonoid` wants a `CancelCommMonoidWithZero` and is therefore out of reach twice
over, once for the missing zero and once because the ambient monoid is not a cancellation monoid in
any way we have proved.  Adjoining a zero with `WithZero` would buy nothing, since the statement we
actually want is the naked one: two multisets of irreducibles with the same product are equal.  The
only unit is `K₁` (`isUnit_iff`), so `Associated a b ↔ a = b` and there is no "up to associates" to
carry around; multiset equality on the nose is the right form of the conclusion.

## What is proved

Existence, `exists_multiset_prod_eq_of_isConnected`: every connected graph is a product of
irreducible connected graphs, by well-founded descent on the number of vertices.

Uniqueness, `multiset_eq_of_prod_eq`: two multisets of irreducibles with the same connected product
are equal.  `existsUnique_multiset_prod_eq` packages the two halves.  Along the way the cartesian
product is shown to cancel connected graphs (`mul_left_cancel_of_isConnected`), so the submonoid of
connected graphs is a `CancelCommMonoid` in which irreducibles have the prime divisor property
(`dvd_or_dvd_submonoid`).

## How

Everything rests on one geometric statement, the *refinement property* `exists_refinement`: if a
connected graph carries two cartesian factorisations, `a * b = c * d`, then there are four "corner"
graphs with

    a = p * q,   b = r * s,   c = p * r,   d = q * s.

The corners are the subgraphs cut out by intersecting the layers of the two factorisations through
a single base point.  Three facts make that work.  Distances in a cartesian product add
coordinatewise (`edist_cartesianProduct`), so the corner of a rectangle lies on a shortest path
(`corner_mem_interval`) and a shortest path between two vertices of a layer stays inside the layer
(`eq_snd_of_mem_interval`); hence layers are convex (`isConvex_layer`).  A convex set of a product
is then closed under mixing coordinates, and `boxSplit` turns any such set into the cartesian
product of its own row and column.  Convexity is metric, so it does not know which factorisation it
came from — that is exactly what lets two factorisations refine each other.

Cancellation and primality both follow.  For cancellation, refine `a * b = a * c` and induct on the
number of vertices: either the shared corner `p` is smaller than `a`, and the induction hypothesis
applies, or it is all of `a` and the other three corners collapse.  For primality
(`dvd_or_dvd_of_irreducible`), refine `p * k = a * b` and use irreducibility of `p` to collapse one
of its two corners to `K₁`.  Note the hypothesis that `a * b` be connected: `Prime p` on the nose,
for the `CommMonoidWithZero` structure on all of `IsoGraph`, would need the disconnected case too,
and that is a separate argument about connected components.

## The Djoković–Winkler relation

The last section records `Θ`, the relation whose transitive closure cuts a graph into directions,
with the fact that no chain of `Θ`-steps can lead from an edge of one cartesian factor to an edge of
the other (`eq_snd_iff_of_reflTransGen`).  This is the route the Handbook of Product Graphs
(Hammack–Imrich–Klavžar, chapter 6) takes to the same theorem.  It is not needed above, but it is
the standard invariant for reading a factorisation off a graph.  Beware that `Θ*` is *not* the
product relation, which is `(Θ ∪ τ)*` for `τ` the unit-square relation.
-/

namespace IsoGraph.CartesianProduct

/-! ## Connected graphs as a monoid -/

/-- A cartesian product is connected only if its left factor is. -/
theorem isConnected_of_mul_left {a b : IsoGraph} (h : (a * b).IsConnected) : a.IsConnected :=
  (isConnected_cartesianProduct.1 h).1

/-- A cartesian product is connected only if its right factor is. -/
theorem isConnected_of_mul_right {a b : IsoGraph} (h : (a * b).IsConnected) : b.IsConnected :=
  (isConnected_cartesianProduct.1 h).2

/-- The only unit is the graph on one vertex. -/
theorem eq_one_of_isUnit {a : IsoGraph} (h : IsUnit a) : a = 1 :=
  V_eq_one_iff.1 ((isUnit_iff a).1 h)

/-- A divisor of a connected graph is connected, being one of its cartesian factors. -/
theorem isConnected_of_dvd {a b : IsoGraph} (hb : b.IsConnected) (h : a ∣ b) : a.IsConnected := by
  obtain ⟨c, rfl⟩ := h
  exact isConnected_of_mul_left hb

/-- Divisibility among connected graphs is divisibility in the ambient monoid: the cofactor of a
connected graph is automatically connected, so there is nothing to check. -/
theorem dvd_iff_coe_dvd {a b : connectedSubmonoid} : a ∣ b ↔ (a : IsoGraph) ∣ (b : IsoGraph) := by
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨(c : IsoGraph), congrArg Subtype.val hc⟩, fun ⟨c, hc⟩ ↦ ?_⟩
  have hb : (b : IsoGraph).IsConnected := b.2
  rw [hc] at hb
  exact ⟨⟨c, isConnected_of_mul_right hb⟩, Subtype.ext hc⟩

/-- A connected graph is a unit of the submonoid exactly when it is one of the whole monoid. -/
theorem isUnit_submonoid_iff {a : connectedSubmonoid} : IsUnit a ↔ (a : IsoGraph).V = 1 := by
  refine ⟨fun h ↦ (isUnit_iff _).1 (h.map (Submonoid.subtype connectedSubmonoid)), fun h ↦ ?_⟩
  have ha : a = 1 := Subtype.ext (V_eq_one_iff.1 h)
  exact ha ▸ isUnit_one

/-- Irreducibility in the submonoid of connected graphs agrees with irreducibility in `IsoGraph`,
because both factors of a connected graph are connected. -/
theorem irreducible_submonoid_iff {a : connectedSubmonoid} :
    Irreducible a ↔ Irreducible (a : IsoGraph) := by
  have ha2 : (a : IsoGraph).IsConnected := a.2
  constructor
  · refine fun h ↦ ⟨fun hu ↦ h.1 (isUnit_submonoid_iff.2 ((isUnit_iff _).1 hu)), fun x y hxy ↦ ?_⟩
    have hxy' := ha2
    rw [hxy] at hxy'
    have hsplit : a = (⟨x, isConnected_of_mul_left hxy'⟩ : connectedSubmonoid)
        * ⟨y, isConnected_of_mul_right hxy'⟩ := Subtype.ext hxy
    rcases h.2 hsplit with hu | hu
    · exact Or.inl ((isUnit_iff x).2 (isUnit_submonoid_iff.1 hu))
    · exact Or.inr ((isUnit_iff y).2 (isUnit_submonoid_iff.1 hu))
  · refine fun h ↦ ⟨fun hu ↦ h.1 ((isUnit_iff _).2 (isUnit_submonoid_iff.1 hu)), fun x y hxy ↦ ?_⟩
    have hsplit : (a : IsoGraph) = (x : IsoGraph) * (y : IsoGraph) := congrArg Subtype.val hxy
    rcases h.2 hsplit with hu | hu
    · exact Or.inl (isUnit_submonoid_iff.2 ((isUnit_iff _).1 hu))
    · exact Or.inr (isUnit_submonoid_iff.2 ((isUnit_iff _).1 hu))

/-- **Every connected graph is a cartesian product of irreducible connected graphs.**  This is the
existence half of Sabidussi–Vizing, and it costs nothing beyond well-founded descent on the number
of vertices: the factors of a connected graph are connected, so a factorisation of the ambient
monoid is automatically one of the submonoid.  The empty multiset covers `K₁`. -/
theorem exists_multiset_prod_eq_of_isConnected {a : IsoGraph} (ha : a.IsConnected) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, b.IsConnected ∧ Irreducible b) ∧ f.prod = a := by
  obtain ⟨f, hf, hfp⟩ := exists_multiset_prod_eq (a := a) (fun h ↦ by
    have hp := ha.V_pos
    rw [h] at hp
    simp at hp)
  exact ⟨f, fun b hb ↦ ⟨isConnected_of_dvd (hfp ▸ ha) (hfp ▸ Multiset.dvd_prod hb), hf b hb⟩, hfp⟩

end IsoGraph.CartesianProduct

namespace CGraph

/-! ## Distances, intervals and convexity -/

/-- **Distance in a cartesian product is the sum of the coordinate distances.**  One walks in the
two coordinates independently, so there is nothing to gain by interleaving the moves. -/
theorem edist_cartesianProduct (G H : CGraph) (p q : (G □g H).V) :
    (G □g H).toSimple.edist p q
      = G.toSimple.edist p.1 q.1 + H.toSimple.edist p.2 q.2 := by
  rw [toSimple_cartesianProduct]
  exact SimpleGraph.edist_boxProd p q

/-- The metric interval from `x` to `y`: the vertices lying on some shortest path between them. -/
def interval (G : CGraph) (x y : G.V) : Set G.V :=
  {w | G.toSimple.edist x w + G.toSimple.edist w y = G.toSimple.edist x y}

@[simp] theorem mem_interval {G : CGraph} {x y w : G.V} :
    w ∈ interval G x y ↔
      G.toSimple.edist x w + G.toSimple.edist w y = G.toSimple.edist x y := Iff.rfl

theorem left_mem_interval {G : CGraph} (x y : G.V) : x ∈ interval G x y := by
  simp

theorem right_mem_interval {G : CGraph} (x y : G.V) : y ∈ interval G x y := by
  simp

/-- A set of vertices is convex when it contains every shortest path between two of its
members. -/
def IsConvex (G : CGraph) (S : Set G.V) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → interval G x y ⊆ S

/-- **The corner of a rectangle lies on a shortest path.**  In a cartesian product one may travel
first in one coordinate and then in the other without losing any time, so the corner `(a₁, b₂)` of
the rectangle spanned by `a` and `b` is on a geodesic between them. -/
theorem corner_mem_interval {G H : CGraph} (a b : (G □g H).V) :
    ((a.1, b.2) : (G □g H).V) ∈ interval (G □g H) a b := by
  show (G □g H).toSimple.edist a (a.1, b.2) + (G □g H).toSimple.edist (a.1, b.2) b
      = (G □g H).toSimple.edist a b
  rw [edist_cartesianProduct, edist_cartesianProduct, edist_cartesianProduct]
  simp only [SimpleGraph.edist_self, zero_add, add_zero]
  exact add_comm _ _

/-- **A convex set of vertices in a cartesian product is a box.**  Given two members `a` and `b` of
the set, the corner `(a₁, b₂)` lies on a shortest path between them and so belongs to the set as
well; that is exactly the statement that the set is the product of its two projections.  This is the
form in which convexity enters the Sabidussi–Vizing proof. -/
theorem eq_prod_image_of_isConvex {G H : CGraph} {S : Set (G □g H).V}
    (hS : IsConvex (G □g H) S) : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S) := by
  ext p
  refine ⟨fun hp ↦ ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩, ?_⟩
  rintro ⟨⟨a, ha, ha1⟩, ⟨b, hb, hb2⟩⟩
  have hp : ((a.1, b.2) : (G □g H).V) = p := Prod.ext ha1 hb2
  exact hp ▸ hS ha hb (corner_mem_interval a b)

/-- A vertex on a shortest path between two vertices of a layer stays in that layer, provided the
two are a finite distance apart.  Straying in the second coordinate costs moves that the triangle
inequality in the first coordinate cannot refund. -/
theorem eq_snd_of_mem_interval {G H : CGraph} {x y w : (G □g H).V}
    (hfin : (G □g H).toSimple.edist x y ≠ ⊤) (hxy : x.2 = y.2)
    (hw : w ∈ interval (G □g H) x y) : w.2 = x.2 := by
  rw [mem_interval, edist_cartesianProduct, edist_cartesianProduct, edist_cartesianProduct,
    ← hxy, SimpleGraph.edist_self, add_zero] at hw
  rw [edist_cartesianProduct, ← hxy, SimpleGraph.edist_self, add_zero] at hfin
  have hkey : G.toSimple.edist x.1 w.1 + G.toSimple.edist w.1 y.1
      + (H.toSimple.edist x.2 w.2 + H.toSimple.edist w.2 x.2)
      = G.toSimple.edist x.1 y.1 := by
    rw [← hw]; abel
  have htri : G.toSimple.edist x.1 y.1
      ≤ G.toSimple.edist x.1 w.1 + G.toSimple.edist w.1 y.1 := SimpleGraph.edist_triangle
  have hle : G.toSimple.edist x.1 y.1
      + (H.toSimple.edist x.2 w.2 + H.toSimple.edist w.2 x.2)
      ≤ G.toSimple.edist x.1 y.1 + 0 :=
    calc G.toSimple.edist x.1 y.1 + (H.toSimple.edist x.2 w.2 + H.toSimple.edist w.2 x.2)
        ≤ G.toSimple.edist x.1 w.1 + G.toSimple.edist w.1 y.1
          + (H.toSimple.edist x.2 w.2 + H.toSimple.edist w.2 x.2) := add_le_add htri le_rfl
      _ = G.toSimple.edist x.1 y.1 := hkey
      _ = G.toSimple.edist x.1 y.1 + 0 := (add_zero _).symm
  have hzero : H.toSimple.edist x.2 w.2 + H.toSimple.edist w.2 x.2 = 0 :=
    le_antisymm ((ENat.add_le_add_iff_left hfin).1 hle) (zero_le _)
  exact (SimpleGraph.edist_eq_zero_iff.1 (add_eq_zero.1 hzero).1).symm

/-- **Layers are convex.**  The copies of `G` inside a connected `G □g H` are convex sets of
vertices; connectedness is what makes the distances finite. -/
theorem isConvex_layer {G H : CGraph} (h : (G □g H).IsConnected) (b : H.V) :
    IsConvex (G □g H) {p : (G □g H).V | p.2 = b} := by
  intro x hx y hy w hw
  have hfin : (G □g H).toSimple.edist x y ≠ ⊤ :=
    SimpleGraph.edist_ne_top_iff_reachable.2 (h.preconnected x y)
  show w.2 = b
  rw [eq_snd_of_mem_interval hfin (hx.trans hy.symm) hw]
  exact hx

/-- An isomorphism preserves the extended distance. -/
theorem edist_iso {G H : CGraph} (i : G ≃cg H) (x y : G.V) :
    H.toSimple.edist (i x) (i y) = G.toSimple.edist x y :=
  (SimpleGraph.Iso.edist_eq i.toSimpleIso x y).symm

/-- Convexity pulls back along an isomorphism.  Intervals are metric, so this is immediate; it is
also the whole reason the refinement property below works, since it means a convex set does not
remember which product structure exhibited it. -/
theorem isConvex_map {G H : CGraph} (i : G ≃cg H) {S : Set H.V} (hS : IsConvex H S) :
    IsConvex G {v | i v ∈ S} := by
  intro x hx y hy w hw
  refine hS hx hy ?_
  rw [mem_interval] at hw ⊢
  rw [edist_iso i, edist_iso i, edist_iso i]
  exact hw

/-- **Layers in the first coordinate are convex** as well, by symmetry of the product. -/
theorem isConvex_layer_fst {G H : CGraph} (h : (G □g H).IsConnected) (a : G.V) :
    IsConvex (G □g H) {p : (G □g H).V | p.1 = a} := by
  have h' : (H □g G).IsConnected := by
    rw [isConnected_cartesianProduct_iff] at h ⊢
    exact ⟨h.2, h.1⟩
  exact isConvex_map (Iso.cartesianProductComm G H) (isConvex_layer h' a)

/-- A convex set of a cartesian product is closed under mixing the coordinates of two of its
members: the mixture is a corner of the rectangle they span, so it lies on a shortest path. -/
theorem mix_mem_of_isConvex {X Y : CGraph} {S : Set (X □g Y).V} (hS : IsConvex (X □g Y) S)
    {p q : (X □g Y).V} (hp : p ∈ S) (hq : q ∈ S) : ((p.1, q.2) : (X □g Y).V) ∈ S :=
  hS hp hq (corner_mem_interval p q)

/-- The same, for a product structure carried by an isomorphism rather than by the graph itself. -/
theorem mix_mem_of_isConvex' {G X Y : CGraph} (i : G ≃cg X □g Y) {S : Set G.V}
    (hS : IsConvex G S) {p q : G.V} (hp : p ∈ S) (hq : q ∈ S) :
    i.symm ((i p).1, (i q).2) ∈ S := by
  have hS' : IsConvex (X □g Y) {w | i.symm w ∈ S} := isConvex_map i.symm hS
  have hp' : (i p) ∈ {w | i.symm w ∈ S} := by simpa using hp
  have hq' : (i q) ∈ {w | i.symm w ∈ S} := by simpa using hq
  exact mix_mem_of_isConvex hS' hp' hq'

/-! ## Splitting a graph along a convex set -/

/-- Restriction transports along an isomorphism. -/
def restrictIso {G H : CGraph} (i : G ≃cg H) (s : G.V → Prop) [DecidablePred s] :
    G.restrict s ≃cg H.restrict (fun w ↦ s (i.symm w)) :=
  isoOfAdj (G := G.restrict s) (H := H.restrict _)
    ⟨fun v ↦ ⟨i v.1, by simpa using v.2⟩, fun w ↦ ⟨i.symm w.1, w.2⟩,
      fun v ↦ Subtype.ext (by simp), fun w ↦ Subtype.ext (by simp)⟩
    (fun x y ↦ i.adj_eq x.1 y.1)

/-- The row of a cartesian product through a fixed second coordinate is the first factor. -/
def restrictRow (X Y : CGraph) (y₀ : Y.V) : (X □g Y).restrict (fun p ↦ p.2 = y₀) ≃cg X :=
  isoOfAdj (G := (X □g Y).restrict _) (H := X)
    ⟨fun p ↦ p.1.1, fun x ↦ ⟨(x, y₀), rfl⟩,
      fun p ↦ Subtype.ext (Prod.ext rfl p.2.symm), fun _ ↦ rfl⟩
    (fun x y ↦ by
      show X.Adj x.1.1 y.1.1 = (X □g Y).Adj x.1 y.1
      have hx : x.1.2 = y₀ := x.2
      have hy : y.1.2 = y₀ := y.2
      have hl : Y.Adj y₀ y₀ = false := Bool.eq_false_iff.2 (Y.loopless y₀)
      rw [cartesianProduct_adj, hx, hy, hl]
      simp)

/-- The column of a cartesian product through a fixed first coordinate is the second factor. -/
def restrictCol (X Y : CGraph) (x₀ : X.V) : (X □g Y).restrict (fun p ↦ p.1 = x₀) ≃cg Y :=
  isoOfAdj (G := (X □g Y).restrict _) (H := Y)
    ⟨fun p ↦ p.1.2, fun y ↦ ⟨(x₀, y), rfl⟩,
      fun p ↦ Subtype.ext (Prod.ext p.2.symm rfl), fun _ ↦ rfl⟩
    (fun x y ↦ by
      show Y.Adj x.1.2 y.1.2 = (X □g Y).Adj x.1 y.1
      have hx : x.1.1 = x₀ := x.2
      have hy : y.1.1 = x₀ := y.2
      have hl : X.Adj x₀ x₀ = false := Bool.eq_false_iff.2 (X.loopless x₀)
      rw [cartesianProduct_adj, hx, hy, hl]
      simp)

/-- **A set closed under mixing coordinates splits as a cartesian product**: the subgraph a
cartesian product induces on such a set is the product of the subgraphs it induces on the set's row
and column through any one of its points.  The map is `p ↦ ((p₁, t₂), (t₁, p₂))`, and it is
adjacency-preserving because the two coordinates of the product move independently. -/
def boxSplit (X Y : CGraph) (s : (X □g Y).V → Prop) [DecidablePred s]
    (hmix : ∀ p q, s p → s q → s ((p.1, q.2) : (X □g Y).V))
    (t : (X □g Y).V) (ht : s t) :
    (X □g Y).restrict s
      ≃cg (X □g Y).restrict (fun p ↦ s p ∧ p.2 = t.2)
          □g (X □g Y).restrict (fun p ↦ s p ∧ p.1 = t.1) :=
  isoOfAdj (G := (X □g Y).restrict s)
    (H := (X □g Y).restrict (fun p ↦ s p ∧ p.2 = t.2)
          □g (X □g Y).restrict (fun p ↦ s p ∧ p.1 = t.1))
    { toFun := fun p ↦ (⟨(p.1.1, t.2), hmix p.1 t p.2 ht, rfl⟩,
        ⟨(t.1, p.1.2), hmix t p.1 ht p.2, rfl⟩)
      invFun := fun uv ↦ ⟨(uv.1.1.1, uv.2.1.2), hmix uv.1.1 uv.2.1 uv.1.2.1 uv.2.2.1⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun uv ↦ Prod.ext (Subtype.ext (Prod.ext rfl uv.1.2.2.symm))
        (Subtype.ext (Prod.ext uv.2.2.2.symm rfl)) }
    (fun x y ↦ by
      have hlX : X.Adj t.1 t.1 = false := Bool.eq_false_iff.2 (X.loopless t.1)
      have hlY : Y.Adj t.2 t.2 = false := Bool.eq_false_iff.2 (Y.loopless t.2)
      show ((X □g Y).restrict (fun p ↦ s p ∧ p.2 = t.2)
          □g (X □g Y).restrict (fun p ↦ s p ∧ p.1 = t.1)).Adj _ _ = (X □g Y).Adj x.1 y.1
      rw [Bool.eq_iff_iff]
      simp [cartesianProduct_adj, hlX, hlY]
      refine or_congr (and_congr_left' ?_) (and_congr_right' ?_)
      · exact ⟨fun h ↦ congrArg
            (fun z : ((X □g Y).restrict (fun p ↦ s p ∧ p.2 = t.2)).V ↦ z.1.1) h,
          fun h ↦ Subtype.ext (Prod.ext h rfl)⟩
      · exact ⟨fun h ↦ congrArg
            (fun z : ((X □g Y).restrict (fun p ↦ s p ∧ p.1 = t.1)).V ↦ z.1.2) h,
          fun h ↦ Subtype.ext (Prod.ext rfl h)⟩)

/-- `boxSplit` for a product structure carried by an isomorphism: the row and the column are cut out
by the coordinates of `i`, but the pieces stay inside `G`. -/
def boxSplit' {G X Y : CGraph} (i : G ≃cg X □g Y) (s : G.V → Prop) [DecidablePred s]
    (hmix : ∀ p q, s p → s q → s (i.symm ((i p).1, (i q).2)))
    (t : G.V) (ht : s t) :
    G.restrict s ≃cg G.restrict (fun p ↦ s p ∧ (i p).2 = (i t).2)
        □g G.restrict (fun p ↦ s p ∧ (i p).1 = (i t).1) :=
  (restrictIso i s).trans
    (((boxSplit X Y (fun w ↦ s (i.symm w))
        (fun p q hp hq ↦ by simpa using hmix (i.symm p) (i.symm q) hp hq)
        (i t) (by simpa using ht)).trans
      (Iso.cartesianProduct
        ((restrictCongr _ _ (fun w ↦ s (i.symm w) ∧ (i (i.symm w)).2 = (i t).2)
          (fun w ↦ by simp)).trans
          (restrictIso i (fun p ↦ s p ∧ (i p).2 = (i t).2)).symm)
        ((restrictCongr _ _ (fun w ↦ s (i.symm w) ∧ (i (i.symm w)).1 = (i t).1)
          (fun w ↦ by simp)).trans
          (restrictIso i (fun p ↦ s p ∧ (i p).1 = (i t).1)).symm))))

/-! ## The refinement property -/

/-- **Two cartesian factorisations of a connected graph have a common refinement.**  Fix a base
point.  Each factorisation has a row and a column through it, four layers in all, and each layer is
convex.  Convexity is a metric condition, so the layers of one factorisation are closed under
mixing the coordinates of the *other*; `boxSplit` then cuts each of the four layers into the two
corners it meets, and the four corners are shared between the two factorisations. -/
theorem exists_iso_refinement {A B C D : CGraph} (hconn : (A □g B).IsConnected)
    (i : A □g B ≃cg C □g D) :
    ∃ P Q R S : CGraph, Nonempty (A ≃cg P □g Q) ∧ Nonempty (B ≃cg R □g S) ∧
      Nonempty (C ≃cg P □g R) ∧ Nonempty (D ≃cg Q □g S) := by
  obtain ⟨v₀⟩ := hconn.nonempty
  have hCD : (C □g D).IsConnected := (isConnected_iff_of_iso i).1 hconn
  have hα : IsConvex (A □g B) {p : (A □g B).V | p.2 = v₀.2} := isConvex_layer hconn v₀.2
  have hβ : IsConvex (A □g B) {p : (A □g B).V | p.1 = v₀.1} := isConvex_layer_fst hconn v₀.1
  have hγ : IsConvex (A □g B) {p : (A □g B).V | (i p).2 = (i v₀).2} :=
    isConvex_map i (isConvex_layer hCD (i v₀).2)
  have hδ : IsConvex (A □g B) {p : (A □g B).V | (i p).1 = (i v₀).1} :=
    isConvex_map i (isConvex_layer_fst hCD (i v₀).1)
  refine ⟨(A □g B).restrict (fun v ↦ v.2 = v₀.2 ∧ (i v).2 = (i v₀).2),
    (A □g B).restrict (fun v ↦ v.2 = v₀.2 ∧ (i v).1 = (i v₀).1),
    (A □g B).restrict (fun v ↦ v.1 = v₀.1 ∧ (i v).2 = (i v₀).2),
    (A □g B).restrict (fun v ↦ v.1 = v₀.1 ∧ (i v).1 = (i v₀).1), ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact (restrictRow A B v₀.2).symm.trans
      (boxSplit' i _ (fun p q hp hq ↦ mix_mem_of_isConvex' i hα hp hq) v₀ rfl)
  · exact (restrictCol A B v₀.1).symm.trans
      (boxSplit' i _ (fun p q hp hq ↦ mix_mem_of_isConvex' i hβ hp hq) v₀ rfl)
  · refine (((restrictIso i (fun v ↦ (i v).2 = (i v₀).2)).trans
        ((restrictCongr (C □g D) (fun w ↦ (i (i.symm w)).2 = (i v₀).2)
            (fun w ↦ w.2 = (i v₀).2) (fun w ↦ by simp)).trans
          (restrictRow C D (i v₀).2))).symm).trans ?_
    exact (boxSplit A B _ (fun p q hp hq ↦ mix_mem_of_isConvex hγ hp hq) v₀ rfl).trans
      (Iso.cartesianProduct (restrictCongr _ _ _ (fun _ ↦ and_comm))
        (restrictCongr _ _ _ (fun _ ↦ and_comm)))
  · refine (((restrictIso i (fun v ↦ (i v).1 = (i v₀).1)).trans
        ((restrictCongr (C □g D) (fun w ↦ (i (i.symm w)).1 = (i v₀).1)
            (fun w ↦ w.1 = (i v₀).1) (fun w ↦ by simp)).trans
          (restrictCol C D (i v₀).1))).symm).trans ?_
    exact (boxSplit A B _ (fun p q hp hq ↦ mix_mem_of_isConvex hδ hp hq) v₀ rfl).trans
      (Iso.cartesianProduct (restrictCongr _ _ _ (fun _ ↦ and_comm))
        (restrictCongr _ _ _ (fun _ ↦ and_comm)))

/-! ## The Djoković–Winkler relation -/

/-- **The Djoković–Winkler relation** `Θ`, on ordered pairs of vertices rather than on edges, so
that it needs no bundling.  Two pairs are related when the two ways of matching their endpoints give
different total distances; for edges of a connected graph this says they are "opposite sides of a
square", and the classes of its transitive closure cut a graph into directions. -/
def Theta (G : CGraph) (e f : G.V × G.V) : Prop :=
  G.toSimple.edist e.1 f.1 + G.toSimple.edist e.2 f.2
    ≠ G.toSimple.edist e.1 f.2 + G.toSimple.edist e.2 f.1

/-- `Θ` is symmetric. -/
theorem theta_comm {G : CGraph} {e f : G.V × G.V} : Theta G e f ↔ Theta G f e := by
  have h1 : G.toSimple.edist f.1 e.1 = G.toSimple.edist e.1 f.1 := SimpleGraph.edist_comm
  have h2 : G.toSimple.edist f.2 e.2 = G.toSimple.edist e.2 f.2 := SimpleGraph.edist_comm
  have h3 : G.toSimple.edist f.1 e.2 = G.toSimple.edist e.2 f.1 := SimpleGraph.edist_comm
  have h4 : G.toSimple.edist f.2 e.1 = G.toSimple.edist e.1 f.2 := SimpleGraph.edist_comm
  show _ ↔ (G.toSimple.edist f.1 e.1 + G.toSimple.edist f.2 e.2
    ≠ G.toSimple.edist f.1 e.2 + G.toSimple.edist f.2 e.1)
  rw [h1, h2, h3, h4, add_comm (G.toSimple.edist e.2 f.1) (G.toSimple.edist e.1 f.2)]
  exact Iff.rfl

/-- `Θ` does not depend on how the first pair is oriented. -/
theorem theta_swap_left {G : CGraph} {e f : G.V × G.V} :
    Theta G e f ↔ Theta G (e.2, e.1) f := by
  show _ ↔ (G.toSimple.edist e.2 f.1 + G.toSimple.edist e.1 f.2
    ≠ G.toSimple.edist e.2 f.2 + G.toSimple.edist e.1 f.1)
  rw [add_comm (G.toSimple.edist e.2 f.1), add_comm (G.toSimple.edist e.2 f.2)]
  exact ne_comm

/-- **`Θ` is reflexive on edges.**  The two matchings compare `0 + 0` with twice the length of the
edge, so they agree only if the edge is a loop, which no simple graph has. -/
theorem theta_self {G : CGraph} {x y : G.V} (h : G.Adj x y = true) : Theta G (x, y) (x, y) := by
  have hne : x ≠ y := by rintro rfl; exact G.loopless _ h
  simp only [Theta, SimpleGraph.edist_self, add_zero]
  intro hc
  have hz : x = y ∧ y = x := by simpa using hc.symm
  exact hne hz.1

/-- An edge of a cartesian product moves in exactly one of the two coordinates. -/
theorem cartesianProduct_adj_cases {G H : CGraph} {p q : (G □g H).V}
    (h : (G □g H).Adj p q = true) : (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.2 = q.2 ∧ p.1 ≠ q.1) := by
  rw [cartesianProduct_adj] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    refine Or.inl ⟨of_decide_eq_true h1, fun hc ↦ ?_⟩
    rw [hc] at h2
    exact H.loopless _ h2
  · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    refine Or.inr ⟨of_decide_eq_true h2, fun hc ↦ ?_⟩
    rw [hc] at h1
    exact G.loopless _ h1

/-- **`Θ` never relates an edge of one factor to an edge of the other.**  Distances add
coordinatewise, and a pair that moves only in the first coordinate contributes the same second
coordinate to both matchings, so the two sums agree term by term. -/
theorem not_theta_cartesianProduct {G H : CGraph} {e f : (G □g H).V × (G □g H).V}
    (he : e.1.2 = e.2.2) (hf : f.1.1 = f.2.1) : ¬ Theta (G □g H) e f := by
  simp only [Theta, edist_cartesianProduct, ne_eq, not_not, he, hf]
  abel

/-- A single `Θ`-step: two edges related by `Θ`. -/
def ThetaStep (G : CGraph) (e f : G.V × G.V) : Prop :=
  G.Adj e.1 e.2 = true ∧ G.Adj f.1 f.2 = true ∧ Theta G e f

/-- A `Θ`-step of a cartesian product joins two edges of the same factor. -/
theorem eq_snd_iff_of_thetaStep {G H : CGraph} {e f : (G □g H).V × (G □g H).V}
    (h : ThetaStep (G □g H) e f) : (e.1.2 = e.2.2) ↔ (f.1.2 = f.2.2) := by
  obtain ⟨he, hf, hth⟩ := h
  constructor
  · intro hE
    by_contra hF
    exact not_theta_cartesianProduct hE ((cartesianProduct_adj_cases hf).resolve_right
      (fun hc ↦ hF hc.1)).1 hth
  · intro hF
    by_contra hE
    exact not_theta_cartesianProduct hF ((cartesianProduct_adj_cases he).resolve_right
      (fun hc ↦ hE hc.1)).1 (theta_comm.1 hth)

/-- **A chain of `Θ`-steps cannot change direction in a cartesian product**: the `Θ*`-class of an
edge of `G □g H` consists of edges of the same factor.  This is the easy half of the classification
of the classes; the hard half, that each class is exactly a direction of some factorisation, is the
Handbook's route to `exists_iso_refinement`, which the convexity argument above reaches without
it. -/
theorem eq_snd_iff_of_reflTransGen {G H : CGraph} {e f : (G □g H).V × (G □g H).V}
    (h : Relation.ReflTransGen (ThetaStep (G □g H)) e f) :
    (e.1.2 = e.2.2) ↔ (f.1.2 = f.2.2) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (eq_snd_iff_of_thetaStep hstep)

end CGraph

namespace IsoGraph.CartesianProduct

/-! ## Sabidussi–Vizing -/

/-- **The refinement property**, for isomorphism classes: two cartesian factorisations of a
connected graph are both coarsenings of one factorisation into four. -/
theorem exists_refinement {a b c d : IsoGraph} (hconn : (a * b).IsConnected)
    (h : a * b = c * d) :
    ∃ p q r s : IsoGraph, a = p * q ∧ b = r * s ∧ c = p * r ∧ d = q * s := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  obtain ⟨B, rfl⟩ := Quotient.exists_rep b
  obtain ⟨C, rfl⟩ := Quotient.exists_rep c
  obtain ⟨D, rfl⟩ := Quotient.exists_rep d
  simp only [mul_eq, cartesianProduct_mk, isConnected_mk] at hconn h
  obtain ⟨i⟩ := Quotient.exact h
  obtain ⟨P, Q, R, S, ⟨iA⟩, ⟨iB⟩, ⟨iC⟩, ⟨iD⟩⟩ := CGraph.exists_iso_refinement hconn i
  refine ⟨⟦P⟧, ⟦Q⟧, ⟦R⟧, ⟦S⟧, ?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_eq, cartesianProduct_mk]
  · exact Quotient.sound ⟨iA⟩
  · exact Quotient.sound ⟨iB⟩
  · exact Quotient.sound ⟨iC⟩
  · exact Quotient.sound ⟨iD⟩

/-- Cancellation, by descent on the number of vertices of the cancelled factor. -/
private theorem mul_left_cancel_aux :
    ∀ (n : ℕ) (a b c : IsoGraph), a.V = n → (a * b).IsConnected → a * b = a * c → b = c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn hab h
    have ha : a.IsConnected := isConnected_of_mul_left hab
    obtain ⟨p, q, r, s, hpq, hrs, hpr, hqs⟩ := exists_refinement hab h
    have hV : a.V = p.V * q.V := by rw [hpq, mul_eq, V_cartesianProduct]
    have hVpos : 0 < a.V := ha.V_pos
    have hp0 : 0 < p.V := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, Nat.zero_mul] at hV; omega
    have hq0 : 0 < q.V := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, Nat.mul_zero] at hV; omega
    rcases eq_or_lt_of_le (show 1 ≤ q.V from hq0) with hq1 | hq2
    · -- `q` is a single vertex, so `a = p`; then `r` is a single vertex too
      have hq : q = 1 := V_eq_one_iff.1 hq1.symm
      have hap : a = p := by rw [hpq, hq, mul_one]
      have har : a = a * r := by
        conv_rhs => rw [hap]
        exact hpr
      have hr1 : (1 : ℕ) = r.V := by
        have hVr : a.V * 1 = a.V * r.V := by
          simpa [mul_eq, V_cartesianProduct] using congrArg IsoGraph.V har
        exact Nat.eq_of_mul_eq_mul_left hVpos hVr
      have hr : r = 1 := V_eq_one_iff.1 hr1.symm
      rw [hrs, hr, one_mul, hqs, hq, one_mul]
    · -- `q` has at least two vertices, so `p` is strictly smaller than `a`
      have hplt : p.V < n := hn ▸ hV ▸ (Nat.lt_mul_iff_one_lt_right hp0).2 hq2
      have hpc : (p * q).IsConnected := hpq ▸ ha
      have hqr : q = r := ih p.V hplt p q r rfl hpc (by rw [← hpq, hpr])
      rw [hrs, ← hqr, hqs]

/-- **The cartesian product cancels a connected factor.**  The strong product cancels too
(`IsoGraph.strongProduct_left_cancel`), but by a homomorphism-counting argument that says nothing
about this one. -/
theorem mul_left_cancel_of_isConnected {a b c : IsoGraph} (hab : (a * b).IsConnected)
    (h : a * b = a * c) : b = c :=
  mul_left_cancel_aux a.V a b c rfl hab h

/-- **An irreducible graph dividing a connected product divides one of the factors.**  Refine
`p * k = a * b`: the four corners give `p = P * Q`, `a = P * R` and `b = Q * S`, and irreducibility
collapses `P` or `Q` to `K₁`, leaving `p` equal to the other one. -/
theorem dvd_or_dvd_of_irreducible {p a b : IsoGraph} (hp : Irreducible p)
    (hab : (a * b).IsConnected) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨P, Q, R, S, hPQ, hRS, hPR, hQS⟩ := exists_refinement (hk ▸ hab) hk.symm
  rcases hp.2 hPQ with hu | hu
  · have hpQ : p = Q := by rw [hPQ, eq_one_of_isUnit hu, one_mul]
    exact Or.inr ⟨S, by rw [hQS, hpQ]⟩
  · have hpP : p = P := by rw [hPQ, eq_one_of_isUnit hu, mul_one]
    exact Or.inl ⟨R, by rw [hPR, hpP]⟩

/-- An irreducible graph dividing a connected product of graphs divides one of them. -/
theorem exists_mem_of_dvd_prod {p : IsoGraph} (hp : Irreducible p) :
    ∀ g : Multiset IsoGraph, g.prod.IsConnected → p ∣ g.prod → ∃ q ∈ g, p ∣ q := by
  intro g
  induction g using Multiset.induction with
  | empty =>
    intro _ hdvd
    rw [Multiset.prod_zero] at hdvd
    exact absurd (isUnit_of_dvd_one hdvd) hp.1
  | cons q g ih =>
    intro hcon hdvd
    rw [Multiset.prod_cons] at hcon hdvd
    rcases dvd_or_dvd_of_irreducible hp hcon hdvd with hq | hg
    · exact ⟨q, Multiset.mem_cons_self q g, hq⟩
    · obtain ⟨x, hx, hxd⟩ := ih (isConnected_of_mul_right hcon) hg
      exact ⟨x, Multiset.mem_cons_of_mem hx, hxd⟩

/-- **Sabidussi–Vizing.**  Two multisets of irreducibles with the same connected product are equal.
The induction is the usual one: a member of the first multiset divides the product of the second,
hence one of its members, which being irreducible must equal it since the only unit is `K₁`; cancel
and recurse. -/
theorem multiset_eq_of_prod_eq :
    ∀ f g : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) → (∀ b ∈ g, Irreducible b) →
      f.prod.IsConnected → f.prod = g.prod → f = g := by
  intro f
  induction f using Multiset.induction with
  | empty =>
    intro g _ hg _ hprod
    rw [Multiset.prod_zero] at hprod
    exact (Multiset.eq_zero_of_forall_notMem fun q hq ↦
      (hg q hq).1 (isUnit_of_dvd_one (hprod ▸ Multiset.dvd_prod hq))).symm
  | cons p f ih =>
    intro g hf hg hcon hprod
    rw [Multiset.prod_cons] at hcon hprod
    have hfc : f.prod.IsConnected := isConnected_of_mul_right hcon
    have hpi : Irreducible p := hf p (Multiset.mem_cons_self p f)
    obtain ⟨q, hq, hpq⟩ := exists_mem_of_dvd_prod hpi g (hprod ▸ hcon) ⟨f.prod, hprod.symm⟩
    obtain ⟨c, hc⟩ := hpq
    have hqp : q = p := by
      rcases (hg q hq).2 hc with hu | hu
      · exact absurd hu hpi.1
      · rw [hc, eq_one_of_isUnit hu, mul_one]
    subst hqp
    have hgsplit : g.prod = q * (g.erase q).prod := by
      conv_lhs => rw [← Multiset.cons_erase hq]
      rw [Multiset.prod_cons]
    have hrest : f.prod = (g.erase q).prod :=
      mul_left_cancel_of_isConnected hcon (hprod.trans hgsplit)
    have hfg : f = g.erase q :=
      ih _ (fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb))
        (fun b hb ↦ hg b (Multiset.mem_of_mem_erase hb)) hfc hrest
    rw [hfg, Multiset.cons_erase hq]

/-- **Unique factorisation of connected graphs**, existence and uniqueness in one statement. -/
theorem existsUnique_multiset_prod_eq {a : IsoGraph} (ha : a.IsConnected) :
    ∃! f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := by
  obtain ⟨f, hf, hfp⟩ := exists_multiset_prod_eq_of_isConnected ha
  refine ⟨f, ⟨fun b hb ↦ (hf b hb).2, hfp⟩, ?_⟩
  rintro g ⟨hg, hgp⟩
  exact multiset_eq_of_prod_eq g f hg (fun b hb ↦ (hf b hb).2) (hgp ▸ ha) (hgp.trans hfp.symm)

/-- The connected graphs cancel: `connectedSubmonoid` is a `CancelCommMonoid`.  It is not a
`CancelCommMonoidWithZero`, and so not a `UniqueFactorizationMonoid` in Mathlib's sense, only
because the empty graph is not connected and there is no zero to adjoin usefully. -/
instance : CancelCommMonoid connectedSubmonoid :=
  { (inferInstance : CommMonoid connectedSubmonoid) with
    mul_left_cancel := fun a b _ h ↦ Subtype.ext
      (mul_left_cancel_of_isConnected (isConnected_cartesianProduct.2 ⟨a.2, b.2⟩)
        (congrArg Subtype.val h)) }

/-- Irreducibles of the monoid of connected graphs have the prime divisor property.  `Prime` itself
is not available here — it wants a `CommMonoidWithZero`, and there is no zero — but this is what it
would say. -/
theorem dvd_or_dvd_submonoid {p a b : connectedSubmonoid} (hp : Irreducible p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases dvd_or_dvd_of_irreducible (irreducible_submonoid_iff.1 hp)
    (isConnected_cartesianProduct.2 ⟨a.2, b.2⟩) (dvd_iff_coe_dvd.1 h) with h' | h'
  · exact Or.inl (dvd_iff_coe_dvd.2 h')
  · exact Or.inr (dvd_iff_coe_dvd.2 h')

end IsoGraph.CartesianProduct
