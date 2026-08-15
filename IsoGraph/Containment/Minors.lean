import IsoGraph.Containment.Defs

/-!
# More about minors

`Containment/Defs.lean` leaves the two minor relations as preorders, because their antisymmetry
needs an argument the subgraph relations do not.  It is supplied here, and with it the two orders
become partial orders — which is why the `IsoGraph.Minor` and `IsoGraph.InducedMinor` scopes are
declared in this file and not in `Defs.lean`.

The argument goes through one observation, `MinorOf.toSubgraphOf`: **a minor with as many vertices
as the graph it is a minor of is a subgraph of it.**  The branch sets are nonempty and disjoint, so
if there are as many of them as there are vertices then each is a singleton and none is left over;
picking the representatives is then an injective map that carries edges to edges.  Antisymmetry is
that observation applied twice, followed by `SubgraphOf.antisymm`.

Also here: `MinorOf.E_le`, that a minor has no more edges than its host.  Each edge of `H` is
realised by an edge of `G` between the two branch sets, and the branch map recovers which edge of
`H` it came from, so the choice is injective.  Together with `MinorOf.card_le` this is the pair of
counting bounds that a minor search prunes with.

The other half of the file is `ImmersionOf.trans`, the substitution of a trail of `G` for each edge
of a trail of `K`, which gives the `IsoGraph.Immersion` preorder.  The same substitution for
`TopMinorOf` — where internal *vertex* disjointness has to be maintained as well — is still not
proved.
-/

set_option autoImplicit false

namespace CGraph

namespace MinorOf

variable {H G : CGraph}

/-! ## Representatives of the branch sets -/

/-- A chosen vertex of `G` in the branch set of `x`.  Every branch set is nonempty, so there is
one; when the vertex counts agree it is the only one (`branch_eq_some_iff`). -/
noncomputable def rep (f : H.MinorOf G) (x : H.V) : G.V := (f.connectedOn x).nonempty.choose

theorem branch_rep (f : H.MinorOf G) (x : H.V) : f.branch (f.rep x) = some x :=
  (f.connectedOn x).nonempty.choose_spec

theorem rep_injective (f : H.MinorOf G) : Function.Injective f.rep := by
  intro x y h
  have hx := f.branch_rep x
  rw [h, f.branch_rep y] at hx
  exact (Option.some_inj.mp hx).symm

theorem rep_surjective (f : H.MinorOf G) (hcard : Fintype.card G.V ≤ Fintype.card H.V) :
    Function.Surjective f.rep :=
  ((Fintype.bijective_iff_injective_and_card _).2
    ⟨f.rep_injective, le_antisymm f.card_le hcard⟩).2

/-- When the two vertex counts agree, the branch sets are exactly the singletons `{rep x}`. -/
theorem branch_eq_some_iff (f : H.MinorOf G) (hcard : Fintype.card G.V ≤ Fintype.card H.V)
    {u : G.V} {x : H.V} : f.branch u = some x ↔ u = f.rep x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.branch_rep x⟩
  obtain ⟨z, rfl⟩ := f.rep_surjective hcard u
  rw [f.branch_rep z] at h
  rw [Option.some_inj.mp h]

/-! ## A minor that contracts nothing -/

/-- **A minor with as many vertices as its host is a subgraph of it.**  There is no room to
contract or to delete: every branch set is a single vertex, and the map picking it is an injective
homomorphism. -/
noncomputable def toSubgraphOf (f : H.MinorOf G) (hcard : Fintype.card G.V ≤ Fintype.card H.V) :
    H.SubgraphOf G where
  toFun := f.rep
  injective' := f.rep_injective
  map_adj' x y h := by
    obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj h
    rw [f.branch_eq_some_iff hcard] at hu hv
    subst hu
    subst hv
    exact huv

/-- **Two graphs each a minor of the other are isomorphic.** -/
noncomputable def antisymm (f : H.MinorOf G) (g : G.MinorOf H) : H ≃cg G :=
  SubgraphOf.antisymm (f.toSubgraphOf g.card_le) (g.toSubgraphOf f.card_le)

/-! ## Counting edges -/

/-- **A minor has no more edges than its host.**  Choose, for every edge of `H`, an edge of `G`
between the corresponding branch sets; pushing that edge through the branch map returns the edge
of `H` it was chosen for, so distinct edges get distinct choices. -/
theorem E_le (f : H.MinorOf G) : H.E ≤ G.E := by
  classical
  have hex : ∀ e : H.toSimple.edgeSet, ∃ d : G.toSimple.edgeSet,
      Sym2.map f.branch (d : Sym2 G.V) = Sym2.map some (e : Sym2 H.V) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj (by simpa using he)
      exact ⟨⟨s(u, v), by simpa using huv⟩, by simp [hu, hv]⟩
  choose Φ hΦ using hex
  have hinj : Function.Injective Φ := by
    intro e e' h
    have h1 : Sym2.map some (e : Sym2 H.V) = Sym2.map some (e' : Sym2 H.V) := by
      rw [← hΦ e, ← hΦ e', h]
    exact Subtype.ext (Sym2.map.injective (Option.some_injective _) h1)
  rw [E, E, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_le_of_injective Φ hinj

end MinorOf

namespace InducedMinorOf

variable {H G : CGraph}

/-- An induced minor with as many vertices as its host is an induced subgraph of it.  The
reflection of adjacency is `adj_map'` off the diagonal, and looplessness on it. -/
noncomputable def toInducedSubgraphOf (f : H.InducedMinorOf G)
    (hcard : Fintype.card G.V ≤ Fintype.card H.V) : H.InducedSubgraphOf G where
  toSubgraphOf := f.toMinorOf.toSubgraphOf hcard
  adj_map' x y h := by
    rcases eq_or_ne x y with rfl | hxy
    · exact absurd h (by simpa using G.loopless _)
    · exact f.adj_map hxy ⟨_, _, f.branch_rep x, f.branch_rep y, h⟩

/-- **Two graphs each an induced minor of the other are isomorphic.** -/
noncomputable def antisymm (f : H.InducedMinorOf G) (g : G.InducedMinorOf H) : H ≃cg G :=
  f.toMinorOf.antisymm g.toMinorOf

theorem E_le (f : H.InducedMinorOf G) : H.E ≤ G.E := f.toMinorOf.E_le

end InducedMinorOf

/-! ## Immersions compose

Of the two relations that replace an edge by a walk, the immersion is the one whose transitivity
is short, because edge-disjointness survives substitution on its own: replace every edge of a trail
of `K` by its trail in `G` and nothing can be repeated, since the trail of `K` uses each of its
edges once and distinct edges of `K` go to disjoint sets of edges of `G`.  A topological minor
would need the same for *vertices*, which substitution does not give for free. -/

namespace ImmersionOf

variable {H K G : CGraph}

/-- A walk of `K`, with each of its edges replaced by the trail of `G` that the immersion sends
that edge to. -/
def lift (g : K.ImmersionOf G) : {a b : K.V} → K.toSimple.Walk a b →
    G.toSimple.Walk (g.toFun a) (g.toFun b)
  | _, _, .nil => .nil
  | _, _, .cons hab w => (g.walk hab).append (g.lift w)

@[simp] theorem lift_nil (g : K.ImmersionOf G) (a : K.V) :
    g.lift (.nil : K.toSimple.Walk a a) = .nil := rfl

@[simp] theorem lift_cons (g : K.ImmersionOf G) {a b c : K.V} (hab : K.toSimple.Adj a b)
    (w : K.toSimple.Walk b c) : g.lift (.cons hab w) = (g.walk hab).append (g.lift w) := rfl

theorem lift_append (g : K.ImmersionOf G) {a b c : K.V} (p : K.toSimple.Walk a b)
    (q : K.toSimple.Walk b c) : g.lift (p.append q) = (g.lift p).append (g.lift q) := by
  induction p with
  | nil => simp
  | cons hab p ih => simp [ih, SimpleGraph.Walk.append_assoc]

theorem lift_reverse (g : K.ImmersionOf G) {a b : K.V} (p : K.toSimple.Walk a b) :
    g.lift p.reverse = (g.lift p).reverse := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.reverse_cons, lift_append, ih, lift_cons, lift_nil,
      SimpleGraph.Walk.append_nil, lift_cons, SimpleGraph.Walk.reverse_append,
      g.reverse' hab hab.symm]

/-- Every edge of a lifted walk comes from an edge of the walk. -/
theorem exists_of_mem_lift_edges (g : K.ImmersionOf G) {a b : K.V} (p : K.toSimple.Walk a b)
    {e : Sym2 G.V} (he : e ∈ (g.lift p).edges) :
    ∃ (c d : K.V) (hcd : K.Adj c d), s(c, d) ∈ p.edges ∧ e ∈ (g.walk hcd).edges := by
  induction p with
  | nil => simp at he
  | @cons a b c hab p ih =>
    rw [lift_cons, SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact ⟨a, b, hab, by simp, he⟩
    · obtain ⟨c', d', hcd, hmem, he'⟩ := ih he
      exact ⟨c', d', hcd, by simp [hmem], he'⟩

theorem lift_isTrail (g : K.ImmersionOf G) {a b : K.V} {p : K.toSimple.Walk a b}
    (hp : p.IsTrail) : (g.lift p).IsTrail := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.isTrail_cons] at hp
    rw [lift_cons, SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_append]
    refine List.Nodup.append (g.isTrail' hab).edges_nodup (ih hp.1).edges_nodup ?_
    rw [List.disjoint_left]
    intro e he he'
    obtain ⟨c', d', hcd, hmem, he''⟩ := g.exists_of_mem_lift_edges p he'
    have hne : s(a, b) ≠ s(c', d') := fun hEq ↦ hp.2 (hEq ▸ hmem)
    exact g.edgeDisjoint' hab hcd hne e he he''

/-- **An immersion of an immersion is an immersion.** -/
def trans (f : H.ImmersionOf K) (g : K.ImmersionOf G) : H.ImmersionOf G where
  toFun x := g.toFun (f.toFun x)
  injective' _ _ h := f.injective (g.injective h)
  walk h := g.lift (f.walk h)
  isTrail' h := g.lift_isTrail (f.isTrail' h)
  reverse' h h' := by rw [f.reverse' h h', g.lift_reverse]
  edgeDisjoint' := fun {_ _} h {_ _} h' hne e he he' ↦ by
    obtain ⟨c, d, hcd, hmem, hce⟩ := g.exists_of_mem_lift_edges (f.walk h) he
    obtain ⟨c', d', hcd', hmem', hce'⟩ := g.exists_of_mem_lift_edges (f.walk h') he'
    refine g.edgeDisjoint' hcd hcd' (fun hEq ↦ ?_) e hce hce'
    refine f.edgeDisjoint' h h' hne _ hmem ?_
    rw [hEq]
    exact hmem'

end ImmersionOf

end CGraph

namespace IsoGraph

open CGraph

/-! ## On isomorphism classes -/

theorem isMinorOf_antisymm {H G : IsoGraph} (h₁ : H.IsMinorOf G) (h₂ : G.IsMinorOf H) : H = G := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨f.antisymm g⟩

theorem isInducedMinorOf_antisymm {H G : IsoGraph} (h₁ : H.IsInducedMinorOf G)
    (h₂ : G.IsInducedMinorOf H) : H = G := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨f.antisymm g⟩

theorem IsMinorOf.E_le {H G : IsoGraph} (h : H.IsMinorOf G) : H.E ≤ G.E := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.E_le

theorem IsInducedMinorOf.E_le {H G : IsoGraph} (h : H.IsInducedMinorOf G) : H.E ≤ G.E :=
  h.isMinorOf.E_le

theorem IsSubgraphOf.of_isMinorOf {H G : IsoGraph} (h : H.IsMinorOf G) (hV : G.V ≤ H.V) :
    H.IsSubgraphOf G := by
  revert h hV
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ hV
  exact ⟨f.toSubgraphOf hV⟩

theorem isImmersionMinorOf_trans {H G K : IsoGraph} (h₁ : H.IsImmersionMinorOf G)
    (h₂ : G.IsImmersionMinorOf K) : H.IsImmersionMinorOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

/-! ## The two minor orders -/

namespace Minor

/-- The minor order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsMinorOf
  le_refl := isMinorOf_refl
  le_trans _ _ _ := isMinorOf_trans
  le_antisymm _ _ := isMinorOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsMinorOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isMinorOf

end Minor

namespace InducedMinor

/-- The induced minor order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsInducedMinorOf
  le_refl := isInducedMinorOf_refl
  le_trans _ _ _ := isInducedMinorOf_trans
  le_antisymm _ _ := isInducedMinorOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsInducedMinorOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isInducedMinorOf

end InducedMinor

namespace Immersion

/-- The immersion order.  Only a preorder here: the antisymmetry would need every trail of a
counting-tight immersion to be a single edge, which is not proved. -/
scoped instance : Preorder IsoGraph where
  le := IsImmersionMinorOf
  le_refl := isImmersionMinorOf_refl
  le_trans _ _ _ := isImmersionMinorOf_trans

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsImmersionMinorOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isImmersionMinorOf

end Immersion

section Examples

open scoped IsoGraph.Minor

example (G : IsoGraph) : (⊥ : IsoGraph) ≤ G := bot_le
example {H G : IsoGraph} (h₁ : H ≤ G) (h₂ : G ≤ H) : H = G := le_antisymm h₁ h₂
example {H G : IsoGraph} (h : H ≤ G) : H.V ≤ G.V ∧ H.E ≤ G.E := ⟨h.V_le, h.E_le⟩

end Examples

end IsoGraph
