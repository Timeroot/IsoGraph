import IsoGraph.Algebra.Connected

/-!
# Unique factorisation of connected graphs

Unique factorisation fails in the graph semiring: `IsoGraph.Semiring.exists_factorisations_ne`
exhibits a graph with two genuinely different factorisations into irreducibles.  The graph there is
disconnected, and that is the whole story — Sabidussi (1960) and Vizing (1963) proved that a
connected graph factors uniquely into irreducibles under the cartesian product.  This file collects
what that theorem needs.

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

Existence is unconditional: `exists_multiset_prod_eq_of_isConnected` says every connected graph is a
product of irreducible connected graphs, by well-founded descent on the number of vertices.

Uniqueness is proved *modulo its two inputs*.  `multiset_eq_of_prod_eq` derives it from

* cancellation, `a * b = a * c → b = c` for connected `a`; and
* Sabidussi–Vizing proper, that an irreducible connected graph is prime.

Neither hypothesis is discharged here.  The repository has cancellation for the strong product only
(`IsoGraph.strongProduct_left_cancel`), by a homomorphism-counting argument that does not transfer
to the cartesian product.

## Towards the missing inputs

The second half of the file is the standard machinery for the real proof, in the form the
Handbook of Product Graphs (Hammack–Imrich–Klavžar, chapter 6) uses it.  Distances in a cartesian
product add coordinatewise (`edist_cartesianProduct`), from which the two geometric facts follow:
the corner of a rectangle lies on a shortest path (`corner_mem_interval`), so a convex set of
vertices in a product is a box (`eq_prod_image_of_isConvex`); and a shortest path between two
vertices of a layer stays inside that layer (`eq_snd_of_mem_interval`), so layers are convex
(`isConvex_layer`).

Then there is the Djoković–Winkler relation `Θ` on ordered pairs of vertices, and the observation
that no `Θ`-step of a cartesian product can lead from an edge of one factor to an edge of the other
(`not_theta_cartesianProduct`), so no chain of them can either (`eq_snd_iff_of_reflTransGen`).  That
is the easy half of the picture.  Beware that the transitive closure `Θ*` is *not* the product
relation, which is `(Θ ∪ τ)*` for `τ` the unit-square relation; the missing half is the argument
that a `Θ*`-class is a coordinate direction, and it is what the two hypotheses above wait on.
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

/-- **Sabidussi–Vizing, reduced to its two inputs.**  Given cancellation for connected graphs and
the implication irreducible ⟹ prime for connected graphs, two multisets of irreducibles with the
same connected product are equal.  The proof is the usual induction: a prime member of the first
multiset divides the product of the second, hence one of its members, which being irreducible must
equal it since the only unit is `K₁`; cancel and recurse.

Neither hypothesis is proved here, and neither is cheap.  Cancellation under the cartesian product
is a theorem in its own right, and the second hypothesis is Sabidussi–Vizing itself. -/
theorem multiset_eq_of_prod_eq
    (hcancel : ∀ a b c : IsoGraph, a.IsConnected → a * b = a * c → b = c)
    (hprime : ∀ p : IsoGraph, p.IsConnected → Irreducible p → Prime p) :
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
    have hpc : p.IsConnected := isConnected_of_mul_left hcon
    have hfc : f.prod.IsConnected := isConnected_of_mul_right hcon
    have hpi : Irreducible p := hf p (Multiset.mem_cons_self p f)
    obtain ⟨q, hq, hpq⟩ :=
      (hprime p hpc hpi).exists_mem_multiset_dvd (hprod ▸ Dvd.intro f.prod rfl)
    obtain ⟨c, hc⟩ := hpq
    have hqp : q = p := by
      rcases (hg q hq).2 hc with hu | hu
      · exact absurd hu hpi.1
      · rw [hc, eq_one_of_isUnit hu, mul_one]
    subst hqp
    have hgsplit : g.prod = q * (g.erase q).prod := by
      conv_lhs => rw [← Multiset.cons_erase hq]
      rw [Multiset.prod_cons]
    have hrest : f.prod = (g.erase q).prod := hcancel q _ _ hpc (hprod.trans hgsplit)
    have hfg : f = g.erase q :=
      ih _ (fun b hb ↦ hf b (Multiset.mem_cons_of_mem hb))
        (fun b hb ↦ hg b (Multiset.mem_of_mem_erase hb)) hfc hrest
    rw [hfg, Multiset.cons_erase hq]

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
of the classes; the hard half, that each class is exactly a direction of some factorisation, is what
Sabidussi–Vizing still needs. -/
theorem eq_snd_iff_of_reflTransGen {G H : CGraph} {e f : (G □g H).V × (G □g H).V}
    (h : Relation.ReflTransGen (ThetaStep (G □g H)) e f) :
    (e.1.2 = e.2.2) ↔ (f.1.2 = f.2.2) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (eq_snd_iff_of_thetaStep hstep)

end CGraph
