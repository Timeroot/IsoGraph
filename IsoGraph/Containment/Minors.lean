import IsoGraph.Containment.Defs

/-!
# More about minors

`Containment/Defs.lean` leaves the minor relations as preorders, because their antisymmetry needs
an argument the subgraph relations do not.  It is supplied here, and with it the orders become
partial orders — which is why the `IsoGraph.Minor`, `IsoGraph.InducedMinor` and
`IsoGraph.Contraction` scopes are declared in this file and not in `Defs.lean`.

The argument goes through one observation, `MinorOf.toSubgraphOf`: **a minor with as many vertices
as the graph it is a minor of is a subgraph of it.**  The branch sets are nonempty and disjoint, so
if there are as many of them as there are vertices then each is a singleton and none is left over;
picking the representatives is then an injective map that carries edges to edges.  Antisymmetry is
that observation applied twice, followed by `SubgraphOf.antisymm`.  A contraction gets its
antisymmetry the same way, and its order has no bottom element: a contraction keeps every vertex,
so nothing but `empty 0` is a contraction of `empty 0`.

Also here: `MinorOf.E_le`, that a minor has no more edges than its host.  Each edge of `H` is
realised by an edge of `G` between the two branch sets, and the branch map recovers which edge of
`H` it came from, so the choice is injective.  Together with `MinorOf.card_le` this is the pair of
counting bounds that a minor search prunes with.

The other half of the file is transitivity for the two relations that replace an edge by a walk:
`TopMinorOf.trans` substitutes a path of `G` for each edge of a path of `K`, `ImmersionOf.trans`
does the same with trails, and both descend to orders on `IsoGraph`.  Antisymmetry comes with them
— for topological minors by way of `TopMinorOf.toMinorOf`, **a topological minor is a minor**, and
for immersions by counting edges — so all five of `IsoGraph.Minor`, `IsoGraph.InducedMinor`,
`IsoGraph.Contraction`, `IsoGraph.TopMinor` and `IsoGraph.Immersion` are partial orders.
-/

set_option autoImplicit false

namespace CGraph

/-- Every edge of `toSimple` comes from an adjacent pair. -/
theorem exists_adj_of_mem_edgeSet {H : CGraph} (e : H.toSimple.edgeSet) :
    ∃ (a b : H.V) (_ : H.Adj a b), (e : Sym2 H.V) = s(a, b) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, by simpa using he, rfl⟩

/-- An injective rank on the vertices, used to break ties between them.  Noncomputable: a bare
`Fintype` gives no computable enumeration of its elements, and no rank definable from `Fintype`
and `DecidableEq` alone could be one, since it would have to be invariant under every permutation
of the type and hence constant. -/
noncomputable def vrank (G : CGraph) (x : G.V) : ℕ := (Finset.univ : Finset G.V).toList.idxOf x

theorem vrank_injective (G : CGraph) : Function.Injective G.vrank :=
  fun _ _ h ↦ (List.idxOf_inj (by simp)).mp h

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

namespace ContractionOf

variable {H G : CGraph}

/-- A contraction with as many vertices as its host contracts nothing: every block is a single
vertex, and the contraction is an induced subgraph inclusion the other way. -/
noncomputable def toInducedSubgraphOf (f : H.ContractionOf G)
    (hcard : Fintype.card G.V ≤ Fintype.card H.V) : H.InducedSubgraphOf G :=
  f.toInducedMinorOf.toInducedSubgraphOf hcard

/-- **Two graphs each a contraction of the other are isomorphic.** -/
noncomputable def antisymm (f : H.ContractionOf G) (g : G.ContractionOf H) : H ≃cg G :=
  f.toInducedMinorOf.antisymm g.toInducedMinorOf

theorem E_le (f : H.ContractionOf G) : H.E ≤ G.E := f.toInducedMinorOf.E_le

end ContractionOf

/-! ## Topological minors compose

Substituting a path of `G` for each edge of a path of `K` gives a path again: a repeated vertex
would sit on two of the substituted paths, hence — by the disjointness the model asks for — at a
branch vertex, and the only branch vertices on a substituted path are the images of its own two
ends, so the repeat was already one in the original.  That is `TopMinorOf.lift_isPath`, and
`TopMinorOf.trans` is the model built from it.

Also here: **a topological minor is a minor**, `TopMinorOf.toMinorOf`.  Contract each subdivided
path onto one of its two ends and the branch sets that come out are connected and realise every
edge of `H`.  Which end is a choice, and it has to be made the same way on both readings of an
edge, so the construction takes a rank `H.V → ℕ` and keeps the lower-ranked end.  In that rank it
is computable; a bare `Fintype` gives no computable way to tell its elements apart, so
`TopMinorOf.toMinorOf'`, which supplies a rank of its own, is not. -/

namespace TopMinorOf

variable {H K G : CGraph}

/-- A walk of `K`, with each of its edges replaced by the path of `G` that the topological minor
model sends that edge to. -/
def lift (g : K.TopMinorOf G) : {a b : K.V} → K.toSimple.Walk a b →
    G.toSimple.Walk (g.toFun a) (g.toFun b)
  | _, _, .nil => .nil
  | _, _, .cons hab w => (g.path hab).append (g.lift w)

@[simp] theorem lift_nil (g : K.TopMinorOf G) (a : K.V) :
    g.lift (.nil : K.toSimple.Walk a a) = .nil := rfl

@[simp] theorem lift_cons (g : K.TopMinorOf G) {a b c : K.V} (hab : K.toSimple.Adj a b)
    (w : K.toSimple.Walk b c) : g.lift (.cons hab w) = (g.path hab).append (g.lift w) := rfl

theorem lift_append (g : K.TopMinorOf G) {a b c : K.V} (p : K.toSimple.Walk a b)
    (q : K.toSimple.Walk b c) : g.lift (p.append q) = (g.lift p).append (g.lift q) := by
  induction p with
  | nil => simp
  | cons hab p ih => simp [ih, SimpleGraph.Walk.append_assoc]

theorem lift_reverse (g : K.TopMinorOf G) {a b : K.V} (p : K.toSimple.Walk a b) :
    g.lift p.reverse = (g.lift p).reverse := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.reverse_cons, lift_append, ih, lift_cons, lift_nil,
      SimpleGraph.Walk.append_nil, lift_cons, SimpleGraph.Walk.reverse_append,
      g.reverse' hab hab.symm]

/-- Every vertex of a lifted walk is either its far end or a vertex of the path substituted for
one of the walk's edges. -/
theorem exists_of_mem_lift_support (g : K.TopMinorOf G) {a b : K.V} (p : K.toSimple.Walk a b)
    {z : G.V} (hz : z ∈ (g.lift p).support) : z = g.toFun b ∨
      ∃ (c d : K.V) (hcd : K.Adj c d), s(c, d) ∈ p.edges ∧ z ∈ (g.path hcd).support := by
  induction p with
  | nil => exact Or.inl (by simpa using hz)
  | @cons a b c hab p ih =>
    rw [lift_cons, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact Or.inr ⟨a, b, hab, by simp, hz⟩
    · rcases ih hz with hz' | ⟨c', d', hcd, hmem, hz'⟩
      · exact Or.inl hz'
      · exact Or.inr ⟨c', d', hcd, by simp [hmem], hz'⟩

/-- **Substituting a path for each edge of a path gives a path.** -/
theorem lift_isPath (g : K.TopMinorOf G) {a b : K.V} {p : K.toSimple.Walk a b} (hp : p.IsPath) :
    (g.lift p).IsPath := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hnd := (ih hp.1).support_nodup
    rw [SimpleGraph.Walk.support_eq_cons (g.lift p)] at hnd
    have hhead : g.toFun b ∉ (g.lift p).support.tail := (List.nodup_cons.mp hnd).1
    rw [lift_cons, SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    refine List.Nodup.append (g.isPath' hab).support_nodup (List.nodup_cons.mp hnd).2 ?_
    rw [List.disjoint_left]
    intro z hz hz'
    rcases g.exists_of_mem_lift_support p (List.mem_of_mem_tail hz') with hzc | ⟨c', d', hcd,
      hmem, hz2⟩
    · rcases g.branch' hab c (hzc ▸ hz) with rfl | rfl
      · exact hp.2 p.end_mem_support
      · exact hhead (hzc ▸ hz')
    · rcases eq_or_ne s(a, b) s(c', d') with hEq | hne
      · rw [← hEq] at hmem
        exact hp.2 (p.fst_mem_support_of_mem_edges hmem)
      · obtain ⟨e, rfl⟩ := g.disjoint' hab hcd hne z hz hz2
        rcases g.branch' hab e hz with rfl | rfl
        · rcases g.branch' hcd e hz2 with rfl | rfl
          · exact hp.2 (p.fst_mem_support_of_mem_edges hmem)
          · exact hp.2 (p.snd_mem_support_of_mem_edges hmem)
        · exact hhead hz'

/-- **A topological minor of a topological minor is a topological minor.** -/
def trans (f : H.TopMinorOf K) (g : K.TopMinorOf G) : H.TopMinorOf G where
  toFun x := g.toFun (f.toFun x)
  injective' _ _ h := f.injective (g.injective h)
  path h := g.lift (f.path h)
  isPath' h := g.lift_isPath (f.isPath' h)
  reverse' h h' := by rw [f.reverse' h h', g.lift_reverse]
  branch' := fun {x y} h z hz ↦ by
    rcases g.exists_of_mem_lift_support (f.path h) hz with hzc | ⟨c, d, hcd, hmem, hz2⟩
    · exact Or.inr (f.injective (g.injective hzc))
    · rcases g.branch' hcd (f.toFun z) hz2 with h1 | h1
      · exact f.branch' h z (by rw [h1]; exact (f.path h).fst_mem_support_of_mem_edges hmem)
      · exact f.branch' h z (by rw [h1]; exact (f.path h).snd_mem_support_of_mem_edges hmem)
  disjoint' := fun {x y} h {x' y'} h' hne z hz hz' ↦ by
    rcases g.exists_of_mem_lift_support (f.path h) hz with hzc | ⟨c, d, hcd, hmem, hz2⟩
    · exact ⟨y, hzc⟩
    rcases g.exists_of_mem_lift_support (f.path h') hz' with hzc' | ⟨c', d', hcd', hmem', hz2'⟩
    · exact ⟨y', hzc'⟩
    rcases eq_or_ne s(c, d) s(c', d') with hEq | hEq2
    · -- one edge of `K` on both paths of `H`, which forces the two edges of `H` to have the
      -- same pair of ends
      exfalso
      have hc' : c ∈ (f.path h').support ∧ d ∈ (f.path h').support := by
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨(f.path h').fst_mem_support_of_mem_edges hmem',
            (f.path h').snd_mem_support_of_mem_edges hmem'⟩
        · exact ⟨(f.path h').snd_mem_support_of_mem_edges hmem',
            (f.path h').fst_mem_support_of_mem_edges hmem'⟩
      obtain ⟨b₁, hb₁⟩ := f.disjoint' h h' hne c
        ((f.path h).fst_mem_support_of_mem_edges hmem) hc'.1
      obtain ⟨b₂, hb₂⟩ := f.disjoint' h h' hne d
        ((f.path h).snd_mem_support_of_mem_edges hmem) hc'.2
      have hb : b₁ ≠ b₂ := fun hc ↦ K.loopless c ((hb₁.trans (by rw [hc, ← hb₂])) ▸ hcd)
      have h1 := f.branch' h b₁ (hb₁ ▸ (f.path h).fst_mem_support_of_mem_edges hmem)
      have h2 := f.branch' h b₂ (hb₂ ▸ (f.path h).snd_mem_support_of_mem_edges hmem)
      have h3 := f.branch' h' b₁ (hb₁ ▸ hc'.1)
      have h4 := f.branch' h' b₂ (hb₂ ▸ hc'.2)
      have key : ∀ {u v : H.V}, b₁ = u ∨ b₁ = v → b₂ = u ∨ b₂ = v → s(b₁, b₂) = s(u, v) := by
        rintro u v (rfl | rfl) (rfl | rfl)
        · exact absurd rfl hb
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hb
      exact hne ((key h1 h2).symm.trans (key h3 h4))
    · obtain ⟨e, rfl⟩ := g.disjoint' hcd hcd' hEq2 z hz2 hz2'
      have he1 : e ∈ (f.path h).support := by
        rcases g.branch' hcd e hz2 with h1 | h1
        · rw [h1]; exact (f.path h).fst_mem_support_of_mem_edges hmem
        · rw [h1]; exact (f.path h).snd_mem_support_of_mem_edges hmem
      have he2 : e ∈ (f.path h').support := by
        rcases g.branch' hcd' e hz2' with h1 | h1
        · rw [h1]; exact (f.path h').fst_mem_support_of_mem_edges hmem'
        · rw [h1]; exact (f.path h').snd_mem_support_of_mem_edges hmem'
      obtain ⟨b, rfl⟩ := f.disjoint' h h' hne e he1 he2
      exact ⟨b, rfl⟩

/-! ### A topological minor is a minor -/

/-- Does `u` lie on the path substituted for the edge `x — y`, oriented away from `x` and stopping
short of the far branch vertex?  This is the half-open piece of that path which `x` claims. -/
def edgeOwns (f : H.TopMinorOf G) (rank : H.V → ℕ) (u : G.V) (x y : H.V) : Bool :=
  if h : H.Adj x y = true then
    decide (rank x < rank y) && decide (u ≠ f.toFun y) && decide (u ∈ (f.path h).support)
  else false

/-- Does the branch set of `x` contain `u`?  Either `u` is the branch vertex itself, or it is an
interior vertex of one of the paths leaving `x` towards a higher-ranked neighbour. -/
def ownsB (f : H.TopMinorOf G) (rank : H.V → ℕ) (u : G.V) (x : H.V) : Bool :=
  decide (u = f.toFun x) || decide (∃ y : H.V, f.edgeOwns rank u x y = true)

theorem ownsB_eq_true_iff (f : H.TopMinorOf G) (rank : H.V → ℕ) (u : G.V) (x : H.V) :
    f.ownsB rank u x = true ↔ u = f.toFun x ∨
      ∃ (y : H.V) (h : H.Adj x y), rank x < rank y ∧ u ≠ f.toFun y ∧
        u ∈ (f.path h).support := by
  rw [ownsB, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  refine or_congr Iff.rfl ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨y, h, h1, h2, h3⟩ ↦ ⟨y, ?_⟩⟩
  · rw [edgeOwns] at hy
    split at hy
    · rename_i hadj
      simp only [Bool.and_eq_true, decide_eq_true_iff] at hy
      exact ⟨y, hadj, hy.1.1, hy.1.2, hy.2⟩
    · simp at hy
  · rw [edgeOwns, dif_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨⟨h1, h2⟩, h3⟩

/-- **The branch sets are disjoint.**  Two paths meeting away from the branch vertices meet at
one, which is an end of both; the orientation by `rank` then rules out the end that is not the
tail. -/
theorem ownsB_unique (f : H.TopMinorOf G) (rank : H.V → ℕ) (u : G.V) {x x' : H.V}
    (hx : f.ownsB rank u x = true) (hx' : f.ownsB rank u x' = true) : x = x' := by
  rw [f.ownsB_eq_true_iff] at hx hx'
  rcases hx with hux | ⟨y, hxy, hlt, huy, hu⟩ <;>
    rcases hx' with hux' | ⟨y', hxy', hlt', huy', hu'⟩
  · exact f.injective (hux.symm.trans hux')
  · rcases f.branch' hxy' x (hux ▸ hu') with h1 | h1
    · exact h1
    · exact absurd (hux.trans (congrArg f.toFun h1)) huy'
  · rcases f.branch' hxy x' (hux' ▸ hu) with h1 | h1
    · exact h1.symm
    · exact absurd (hux'.trans (congrArg f.toFun h1)) huy
  · rcases eq_or_ne s(x, y) s(x', y') with hEq | hEq
    · rw [Sym2.eq_iff] at hEq
      rcases hEq with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · rw [h1, h2] at hlt; omega
    · obtain ⟨b, hb⟩ := f.disjoint' hxy hxy' hEq u hu hu'
      rcases f.branch' hxy b (hb ▸ hu) with h1 | h1
      · rcases f.branch' hxy' b (hb ▸ hu') with h2 | h2
        · exact h1.symm.trans h2
        · exact absurd (hb.trans (congrArg f.toFun h2)) huy'
      · exact absurd (hb.trans (congrArg f.toFun h1)) huy

theorem ownsB_existsUnique (f : H.TopMinorOf G) (rank : H.V → ℕ) {u : G.V}
    (h : ∃ x : H.V, f.ownsB rank u x = true) :
    ∃! a : H.V, a ∈ (Finset.univ : Finset H.V) ∧ (fun x ↦ f.ownsB rank u x = true) a := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, ⟨Finset.mem_univ x, hx⟩, fun y hy ↦ f.ownsB_unique rank u hy.2 hx⟩

/-- **The branch map of a topological minor**: each vertex of `G` goes to the unique vertex of `H`
owning it, if there is one. -/
def branch (f : H.TopMinorOf G) (rank : H.V → ℕ) (u : G.V) : Option H.V :=
  if h : ∃ x : H.V, f.ownsB rank u x = true then
    some (Finset.choose (fun x ↦ f.ownsB rank u x = true) Finset.univ
      (f.ownsB_existsUnique rank h))
  else none

theorem branch_eq_some_iff (f : H.TopMinorOf G) (rank : H.V → ℕ) {u : G.V} {x : H.V} :
    f.branch rank u = some x ↔ f.ownsB rank u x = true := by
  rw [branch]
  split
  · rw [Option.some_inj]
    rename_i hex
    have hp := Finset.choose_property (fun x ↦ f.ownsB rank u x = true)
      (Finset.univ : Finset H.V) (f.ownsB_existsUnique rank hex)
    exact ⟨fun h ↦ h ▸ hp, fun hx ↦ f.ownsB_unique rank u hp hx⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun hx ↦ h ⟨x, hx⟩

theorem branch_toFun (f : H.TopMinorOf G) (rank : H.V → ℕ) (x : H.V) :
    f.branch rank (f.toFun x) = some x := by
  rw [f.branch_eq_some_iff, f.ownsB_eq_true_iff]
  exact Or.inl rfl

theorem branch_eq_of_mem_path (f : H.TopMinorOf G) (rank : H.V → ℕ) {x y : H.V} (hxy : H.Adj x y)
    (hlt : rank x < rank y) {u : G.V} (hne : u ≠ f.toFun y) (hu : u ∈ (f.path hxy).support) :
    f.branch rank u = some x := by
  rw [f.branch_eq_some_iff, f.ownsB_eq_true_iff]
  exact Or.inr ⟨y, hxy, hlt, hne, hu⟩

/-- Every vertex of the branch set of `x` is joined to `f x` inside that branch set: walk back
along the path it sits on. -/
private theorem exists_walk_to_toFun (f : H.TopMinorOf G) (rank : H.V → ℕ) {x : H.V} {u : G.V}
    (hu : f.branch rank u = some x) :
    ∃ w : G.toSimple.Walk u (f.toFun x), ∀ z ∈ w.support, f.branch rank z = some x := by
  rw [f.branch_eq_some_iff, f.ownsB_eq_true_iff] at hu
  rcases hu with rfl | ⟨y, hxy, hlt, huy, hmem⟩
  · refine ⟨.nil, fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ f.branch_toFun rank x
  · have hnot := SimpleGraph.Walk.endpoint_notMem_support_takeUntil (f.isPath' hxy) hmem
      (Ne.symm huy)
    refine ⟨((f.path hxy).takeUntil u hmem).reverse, fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    refine f.branch_eq_of_mem_path rank hxy hlt ?_
      (SimpleGraph.Walk.support_takeUntil_subset _ _ hz)
    rintro rfl
    exact hnot hz

theorem connectedOn_branch (f : H.TopMinorOf G) (rank : H.V → ℕ) (x : H.V) :
    G.ConnectedOn {v | f.branch rank v = some x} where
  nonempty := ⟨f.toFun x, f.branch_toFun rank x⟩
  walk := by
    intro u hu v hv
    obtain ⟨p, hp⟩ := f.exists_walk_to_toFun rank hu
    obtain ⟨q, hq⟩ := f.exists_walk_to_toFun rank hv
    refine ⟨p.append q.reverse, fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hp z hz
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      exact hq z hz

/-- The last edge of the path of `x — y` joins the branch set of `x` to the branch vertex of
`y`. -/
private theorem exists_edge_of_lt (f : H.TopMinorOf G) (rank : H.V → ℕ) {x y : H.V}
    (hxy : H.Adj x y) (hlt : rank x < rank y) :
    ∃ u v, f.branch rank u = some x ∧ f.branch rank v = some y ∧ G.Adj u v := by
  have hne : f.toFun x ≠ f.toFun y := fun hc ↦ H.loopless x (f.injective hc ▸ hxy)
  have hnil : ¬ (f.path hxy).reverse.Nil := SimpleGraph.Walk.not_nil_of_ne (Ne.symm hne)
  have hadj : G.toSimple.Adj (f.toFun y) (f.path hxy).reverse.snd :=
    (f.path hxy).reverse.adj_snd hnil
  have hmem : (f.path hxy).reverse.snd ∈ (f.path hxy).support := by
    have h0 := List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support hnil)
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h0
  exact ⟨_, _, f.branch_eq_of_mem_path rank hxy hlt hadj.ne' hmem, f.branch_toFun rank y,
    hadj.symm⟩

theorem exists_edge (f : H.TopMinorOf G) {rank : H.V → ℕ} (hrank : Function.Injective rank)
    {x y : H.V} (hxy : H.Adj x y) :
    ∃ u v, f.branch rank u = some x ∧ f.branch rank v = some y ∧ G.Adj u v := by
  have hne : x ≠ y := fun hc ↦ H.loopless x (hc ▸ hxy)
  rcases lt_or_gt_of_ne (fun hc ↦ hne (hrank hc)) with hlt | hlt
  · exact f.exists_edge_of_lt rank hxy hlt
  · obtain ⟨u, v, hu, hv, huv⟩ := f.exists_edge_of_lt rank (H.symm x y ▸ hxy) hlt
    exact ⟨v, u, hv, hu, by rw [G.symm]; exact huv⟩

/-- **A topological minor is a minor**: contract each subdivided path onto the lower-ranked of its
two ends.  The rank orients the edges of `H`, and it has to be supplied, since a bare `Fintype`
offers no computable way to tell two vertices apart. -/
def toMinorOf (f : H.TopMinorOf G) (rank : H.V → ℕ) (hrank : Function.Injective rank) :
    H.MinorOf G where
  branch := f.branch rank
  connectedOn' := f.connectedOn_branch rank
  map_adj' _ _ h := f.exists_edge hrank h

/-- `TopMinorOf.toMinorOf` with a rank of its own, for when there is none to hand.  Noncomputable,
for the same reason `CGraph.vrank` is. -/
noncomputable def toMinorOf' (f : H.TopMinorOf G) : H.MinorOf G :=
  f.toMinorOf H.vrank H.vrank_injective

/-- **Two graphs each a topological minor of the other are isomorphic.** -/
noncomputable def antisymm (f : H.TopMinorOf G) (g : G.TopMinorOf H) : H ≃cg G :=
  MinorOf.antisymm f.toMinorOf' g.toMinorOf'

theorem E_le (f : H.TopMinorOf G) : H.E ≤ G.E := f.toMinorOf'.E_le

end TopMinorOf

/-! ## Immersions compose

Of the two relations that replace an edge by a walk, the immersion is the one whose transitivity
is short, because edge-disjointness survives substitution on its own: replace every edge of a trail
of `K` by its trail in `G` and nothing can be repeated, since the trail of `K` uses each of its
edges once and distinct edges of `K` go to disjoint sets of edges of `G`.  Vertex-disjointness,
which the topological minor above needs, takes more care.

The antisymmetry here is a counting argument rather than a structural one.  Choose one edge of `G`
on each trail, injectively, and `H` has no more edges than `G` — that is `ImmersionOf.E_le`.  When
the counts agree the choice is onto, so every edge of every trail is that trail's own choice, so
each trail, having no repeated edge, is a single edge, and the immersion is a subgraph
embedding. -/

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

/-! ### Immersions are antisymmetric -/

/-- Two trails that share an edge are the trails of the same edge of `H`. -/
theorem eq_of_mem_edges (f : H.ImmersionOf G) {x y x' y' : H.V} (h : H.Adj x y) (h' : H.Adj x' y')
    {e : Sym2 G.V} (he : e ∈ (f.walk h).edges) (he' : e ∈ (f.walk h').edges) :
    s(x, y) = s(x', y') := by
  by_contra hne
  exact f.edgeDisjoint' h h' hne e he he'

/-- The trail of an edge has at least one edge: its two ends are distinct branch vertices. -/
theorem walk_edges_ne_nil (f : H.ImmersionOf G) {x y : H.V} (h : H.Adj x y) :
    (f.walk h).edges ≠ [] := by
  intro he
  have hlen : (f.walk h).length = 0 := by
    rw [← (f.walk h).length_edges, he, List.length_nil]
  exact H.loopless _ (f.injective (SimpleGraph.Walk.eq_of_length_eq_zero hlen) ▸ h)

/-- **One edge of `G` chosen on each trail**, injectively: distinct edges of `H` have trails
sharing no edge, so their choices differ. -/
theorem exists_edgeRep (f : H.ImmersionOf G) :
    ∃ Φ : H.toSimple.edgeSet → G.toSimple.edgeSet, Function.Injective Φ ∧
      ∀ (e : H.toSimple.edgeSet) (x y : H.V) (h : H.Adj x y), (e : Sym2 H.V) = s(x, y) →
        (Φ e : Sym2 G.V) ∈ (f.walk h).edges := by
  have hex : ∀ e : H.toSimple.edgeSet, ∃ d : G.toSimple.edgeSet,
      ∀ (x y : H.V) (h : H.Adj x y), (e : Sym2 H.V) = s(x, y) →
        (d : Sym2 G.V) ∈ (f.walk h).edges := by
    intro e
    obtain ⟨a, b, hab, hea⟩ := exists_adj_of_mem_edgeSet e
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (f.walk_edges_ne_nil hab)
    refine ⟨⟨d, (f.walk hab).edges_subset_edgeSet hd⟩, ?_⟩
    intro x y h hxy
    rw [hea, Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hd
    · rw [f.reverse' hab h, SimpleGraph.Walk.edges_reverse, List.mem_reverse]
      exact hd
  choose Φ hΦ using hex
  refine ⟨Φ, ?_, hΦ⟩
  intro e e' hEq
  obtain ⟨a, b, hab, hea⟩ := exists_adj_of_mem_edgeSet e
  obtain ⟨a', b', ha'b', hea'⟩ := exists_adj_of_mem_edgeSet e'
  have h1 := hΦ e a b hab hea
  have h2 := hΦ e' a' b' ha'b' hea'
  rw [hEq] at h1
  exact Subtype.ext (hea.trans ((f.eq_of_mem_edges hab ha'b' h1 h2).trans hea'.symm))

/-- **An immersion has no more edges than its host.** -/
theorem E_le (f : H.ImmersionOf G) : H.E ≤ G.E := by
  obtain ⟨Φ, hinj, -⟩ := f.exists_edgeRep
  rw [E, E, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_le_of_injective Φ hinj

/-- Every edge of `H` goes to a single edge of `G` once the edge counts are tight: the chosen
edges already exhaust `G`, so a second edge on some trail would be one another trail has taken. -/
theorem adj_map_of_E_le (f : H.ImmersionOf G) (hE : G.E ≤ H.E) {x y : H.V} (h : H.Adj x y) :
    G.Adj (f.toFun x) (f.toFun y) := by
  obtain ⟨Φ, hinj, hspec⟩ := f.exists_edgeRep
  have hcard : Fintype.card G.toSimple.edgeSet ≤ Fintype.card H.toSimple.edgeSet := by
    rw [← SimpleGraph.edgeFinset_card, ← SimpleGraph.edgeFinset_card, ← E, ← E]; exact hE
  have hsurj : Function.Surjective Φ :=
    ((Fintype.bijective_iff_injective_and_card Φ).2
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective Φ hinj) hcard⟩).2
  have hall : ∀ d ∈ (f.walk h).edges, d = (Φ ⟨s(x, y), by simpa using h⟩ : Sym2 G.V) := by
    intro d hd
    obtain ⟨e₁, he₁⟩ := hsurj ⟨d, (f.walk h).edges_subset_edgeSet hd⟩
    obtain ⟨a, b, hab, hea⟩ := exists_adj_of_mem_edgeSet e₁
    have hcoe : (Φ e₁ : Sym2 G.V) = d := by rw [he₁]
    have h1 : d ∈ (f.walk hab).edges := hcoe ▸ hspec e₁ a b hab hea
    have hEq : e₁ = ⟨s(x, y), by simpa using h⟩ :=
      Subtype.ext (hea.trans (f.eq_of_mem_edges hab h h1 hd))
    rw [← hEq, hcoe]
  have hnodup : (f.walk h).edges.Nodup := (f.isTrail' h).edges_nodup
  have hsub : (f.walk h).edges.toFinset ⊆ {(Φ ⟨s(x, y), by simpa using h⟩ : Sym2 G.V)} := by
    intro d hd
    simpa using hall d (List.mem_toFinset.mp hd)
  have hlen : (f.walk h).length ≤ 1 := by
    rw [← (f.walk h).length_edges, ← List.toFinset_card_of_nodup hnodup]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  have hne : (f.walk h).length ≠ 0 := fun h0 ↦
    f.walk_edges_ne_nil h (List.eq_nil_of_length_eq_zero (by rw [(f.walk h).length_edges, h0]))
  exact SimpleGraph.Walk.adj_of_length_eq_one (p := f.walk h) (by omega)

/-- **A counting-tight immersion is a subgraph embedding.** -/
def toSubgraphOf (f : H.ImmersionOf G) (hE : G.E ≤ H.E) : H.SubgraphOf G where
  toFun := f.toFun
  injective' := f.injective
  map_adj' _ _ h := f.adj_map_of_E_le hE h

/-- **Two graphs each immersing in the other are isomorphic.** -/
noncomputable def antisymm (f : H.ImmersionOf G) (g : G.ImmersionOf H) : H ≃cg G :=
  SubgraphOf.antisymm (f.toSubgraphOf g.E_le) (g.toSubgraphOf f.E_le)

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

theorem isContractionOf_antisymm {H G : IsoGraph} (h₁ : H.IsContractionOf G)
    (h₂ : G.IsContractionOf H) : H = G := by
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

theorem IsContractionOf.E_le {H G : IsoGraph} (h : H.IsContractionOf G) : H.E ≤ G.E :=
  h.isMinorOf.E_le

/-- A contraction of a graph with no vertices has no vertices: this is why the contraction order
has no bottom element. -/
theorem eq_empty_zero_of_isContractionOf {H : IsoGraph} (h : H.IsContractionOf (empty 0)) :
    H = empty 0 := by
  revert h
  refine Quotient.inductionOn H ?_
  rintro K ⟨f⟩
  have hK : IsEmpty K.V := ⟨fun x ↦ (f.surjective x).elim fun v _ ↦ v.elim0⟩
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  exact Quotient.sound ⟨⟨Equiv.equivOfIsEmpty K.V (CGraph.empty 0).V, fun {a} ↦ hK.elim a⟩⟩

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

theorem isImmersionMinorOf_antisymm {H G : IsoGraph} (h₁ : H.IsImmersionMinorOf G)
    (h₂ : G.IsImmersionMinorOf H) : H = G := by
  revert h₁ h₂
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩ ⟨g⟩
  exact Quotient.sound ⟨f.antisymm g⟩

theorem IsImmersionMinorOf.E_le {H G : IsoGraph} (h : H.IsImmersionMinorOf G) : H.E ≤ G.E := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact f.E_le

theorem isTopMinorOf_trans {H G K : IsoGraph} (h₁ : H.IsTopMinorOf G) (h₂ : G.IsTopMinorOf K) :
    H.IsTopMinorOf K := by
  revert h₁ h₂
  refine Quotient.inductionOn₃ H G K ?_
  rintro _ _ _ ⟨f⟩ ⟨g⟩
  exact ⟨f.trans g⟩

/-- **A topological minor is a minor**: contract every subdivided path onto one of its ends. -/
theorem IsTopMinorOf.isMinorOf {H G : IsoGraph} (h : H.IsTopMinorOf G) : H.IsMinorOf G := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro _ _ ⟨f⟩
  exact ⟨f.toMinorOf'⟩

theorem isTopMinorOf_antisymm {H G : IsoGraph} (h₁ : H.IsTopMinorOf G) (h₂ : G.IsTopMinorOf H) :
    H = G := isMinorOf_antisymm h₁.isMinorOf h₂.isMinorOf

theorem IsTopMinorOf.E_le {H G : IsoGraph} (h : H.IsTopMinorOf G) : H.E ≤ G.E :=
  h.isMinorOf.E_le

/-! ## The containment orders -/

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

namespace Contraction

/-- The contraction order: `H ≤ G` when `H` is `G` with a partition into connected blocks shrunk
to points.  Like the quotient order and unlike the other minor orders it has no bottom element —
a contraction of `empty 0` is `empty 0`, since every vertex of the host has to go somewhere and
every vertex of the image has to come from somewhere. -/
scoped instance : PartialOrder IsoGraph where
  le := IsContractionOf
  le_refl := isContractionOf_refl
  le_trans _ _ _ := isContractionOf_trans
  le_antisymm _ _ := isContractionOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsContractionOf G := Iff.rfl

end Contraction

namespace TopMinor

/-- The topological minor order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsTopMinorOf
  le_refl := isTopMinorOf_refl
  le_trans _ _ _ := isTopMinorOf_trans
  le_antisymm _ _ := isTopMinorOf_antisymm

theorem le_iff (H G : IsoGraph) : H ≤ G ↔ H.IsTopMinorOf G := Iff.rfl

scoped instance : OrderBot IsoGraph where
  bot := empty 0
  bot_le := empty_zero_isTopMinorOf

end TopMinor

namespace Immersion

/-- The immersion order. -/
scoped instance : PartialOrder IsoGraph where
  le := IsImmersionMinorOf
  le_refl := isImmersionMinorOf_refl
  le_trans _ _ _ := isImmersionMinorOf_trans
  le_antisymm _ _ := isImmersionMinorOf_antisymm

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
