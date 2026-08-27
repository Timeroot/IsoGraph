import IsoGraph.Containment.Monotone

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Splitting a containment along a disjoint union

`Containment/Monotone.lean` asks whether an operation preserves a containment; this file asks the
converse question for the disjoint union, and answers the half of it that is about the *maps*: if
`H ⊕g K` sits inside `C ⊕g D`, how do the two sit inside the two?

Each vertex of the pattern lands in one summand of the host, and no edge of the pattern can join
two vertices that land in different ones, because the host has no edge between its summands.  So
the pattern is cut in two by the side its vertices go to, and the cut is along whole connected
pieces: `H` splits as `H₁ ⊕g H₂` and `K` as `K₁ ⊕g K₂`, with `H₁ ⊕g K₁` inside `C` and
`H₂ ⊕g K₂` inside `D`.  That is `SubgraphOf.exists_split`, and `IsSubgraphOf.exists_split_disjUnion`
on isomorphism classes; `Containment/Ordered.lean` turns it into the cancellation theorem
`H ⊕g K ≤ₛ G ⊕g K → H ≤ₛ G` by induction on the number of vertices of `K`.

Seven of the nine relations split this way, each by the same three steps — a `side` function on
the pattern, constant on edges; the two halves `splitLeft` and `splitRight`, induced on the
vertices of each side; and `exists_split`, which reassembles them.  What differs is what has to
cross with the vertices.  For an inclusion, nothing does.  For a minor, an induced minor or a
contraction it is the branch sets, which must stay connected in the summand they land in, so the
file first pulls connectedness back along an induced subgraph inclusion: a walk of the host all of
whose vertices are in the image comes from a walk of the subgraph, because the induced condition
takes each step and injectivity makes it unique.  For a topological minor or an immersion it is
the paths and trails themselves, which are *data* and not just an existence statement — the axioms
relate the path of an edge to the path of its reverse — so the pulled-back walk gets a name,
`walkLeft`, and the lemmas that say what its support, edges and reverse are.  The homomorphism and
quotient orders are the two that do not split, and they are also the two where the disjoint union
does not cancel.

The construction the cut needs is `CGraph.induce G s`, the subgraph of `G` on the vertices where
`s` is true, on the subtype `{v // s v}`.  It is not in `Core/Defs.lean` with the rest
of the constructions because it cannot follow them to `IsoGraph`: its second argument is a
predicate on the vertices of *this* representative, and an isomorphism class has no vertices.  It
comes with the two isomorphisms that make it useful here — `Iso.induceSplit`, which is the
splitting itself, and `Iso.induceDisjUnion`, which says that inducing on a disjoint union induces
on each summand.

The complement appears near the end, for one reason: `(G ∇g H)ᶜ = Gᶜ ⊕g Hᶜ`, so a fact about the
join follows from the same fact about the disjoint union in any order that complementation
preserves.  The induced subgraph order is the one that does — `InducedSubgraphOf.compl` — and it
is how the join is cancelled there.

The join itself never splits: every vertex of one side is adjacent to every vertex of the other,
so no edge of the pattern forces its two ends onto the same side.  The last section does the one
case where that does not matter.  When the graph joined on is a single vertex the pattern's apex
has nowhere to go but the host's apex or the host's base, and either way the map can be repaired
by hand: `exists_map_of_join_complete_one` restricts a map of one cone into another to a map of
the two bases, and keeps injectivity and surjectivity while it does, so the three orders whose
maps are total each get their cancellation from it.
-/

set_option autoImplicit false

namespace Sum

variable {α β : Type}

theorem eq_inl_getLeft (x : α ⊕ β) (h : x.isLeft) : x = .inl (x.getLeft h) :=
  eq_left_iff_getLeft_eq.2 ⟨h, rfl⟩

theorem eq_inr_getRight (x : α ⊕ β) (h : x.isRight) : x = .inr (x.getRight h) :=
  eq_right_iff_getRight_eq.2 ⟨h, rfl⟩

end Sum

namespace CGraph

/-! ## The subgraph induced on a set of vertices -/

/-- The subgraph of `G` induced on the vertices where `s` is true. -/
def induce (G : CGraph) (s : G.V → Bool) : CGraph where
  V := {v : G.V // s v}
  Adj x y := G.Adj x y
  symm x y := G.symm x y
  loopless x := G.loopless x

@[simp] theorem induce_adj (G : CGraph) (s : G.V → Bool) (x y : (G.induce s).V) :
    (G.induce s).Adj x y = G.Adj x.1 y.1 := rfl

/-- What `G` induces on a set of its vertices is an induced subgraph of `G`. -/
def InducedSubgraphOf.induce (G : CGraph) (s : G.V → Bool) :
    (G.induce s).InducedSubgraphOf G where
  toFun := Subtype.val
  injective' := Subtype.val_injective
  map_adj' _ _ h := h
  adj_map' _ _ h := h

/-- The vertices of `G`, sorted into the two sides of `s`. -/
def induceSplitEquiv (G : CGraph) (s : G.V → Bool) :
    G.V ≃ (G.induce s ⊕g G.induce fun v ↦ !s v).V where
  toFun v := if h : s v then .inl ⟨v, h⟩ else .inr ⟨v, by simp [h]⟩
  invFun x := Sum.elim Subtype.val Subtype.val x
  left_inv v := by by_cases h : s v <;> simp [h]
  right_inv x := by
    rcases x with ⟨v, hv⟩ | ⟨v, hv⟩
    · simp [hv]
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      simp [hv]

theorem induceSplitEquiv_apply_pos (G : CGraph) (s : G.V → Bool) (v : G.V) (h : s v) :
    induceSplitEquiv G s v = .inl ⟨v, h⟩ := dif_pos h

theorem induceSplitEquiv_apply_neg (G : CGraph) (s : G.V → Bool) (v : G.V) (h : ¬s v) :
    induceSplitEquiv G s v = .inr ⟨v, by simp [h]⟩ := dif_neg h

/-- **A graph no edge of which crosses `s` is the disjoint union of its two sides.** -/
def Iso.induceSplit (G : CGraph) (s : G.V → Bool) (h : ∀ x y, G.Adj x y → s x = s y) :
    G ≃cg G.induce s ⊕g G.induce fun v ↦ !s v :=
  isoOfAdj (H := G.induce s ⊕g G.induce fun v ↦ !s v) (induceSplitEquiv G s) fun x y ↦ by
    by_cases hx : s x <;> by_cases hy : s y
    · rw [induceSplitEquiv_apply_pos _ _ _ hx, induceSplitEquiv_apply_pos _ _ _ hy]; rfl
    · rw [induceSplitEquiv_apply_pos _ _ _ hx, induceSplitEquiv_apply_neg _ _ _ hy]
      exact (Bool.eq_false_iff.2 fun hadj ↦ hy (h x y hadj ▸ hx)).symm
    · rw [induceSplitEquiv_apply_neg _ _ _ hx, induceSplitEquiv_apply_pos _ _ _ hy]
      exact (Bool.eq_false_iff.2 fun hadj ↦ hx (h x y hadj ▸ hy)).symm
    · rw [induceSplitEquiv_apply_neg _ _ _ hx, induceSplitEquiv_apply_neg _ _ _ hy]; rfl

/-- Inducing on a disjoint union induces on each summand. -/
def Iso.induceDisjUnion (G H : CGraph) (s : (G ⊕g H).V → Bool) :
    (G ⊕g H).induce s ≃cg G.induce (fun v ↦ s (.inl v)) ⊕g H.induce fun v ↦ s (.inr v) :=
  isoOfAdj (G := (G ⊕g H).induce s)
    { toFun := fun x ↦ match x with
        | ⟨.inl a, ha⟩ => .inl ⟨a, ha⟩
        | ⟨.inr b, hb⟩ => .inr ⟨b, hb⟩
      invFun := fun x ↦ match x with
        | .inl ⟨a, ha⟩ => ⟨.inl a, ha⟩
        | .inr ⟨b, hb⟩ => ⟨.inr b, hb⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl }
    (by rintro ⟨_ | _, _⟩ ⟨_ | _, _⟩ <;> rfl)

/-! ## Walks pulled back into an induced subgraph -/

section Walks

variable {A G : CGraph}

/-- A subgraph inclusion, as a homomorphism of the underlying `SimpleGraph`s — the form
`Walk.map` asks for. -/
def SubgraphOf.toSimpleHom (f : A.SubgraphOf G) : A.toSimple →g G.toSimple := f.toHom

@[simp] theorem SubgraphOf.coe_toSimpleHom (f : A.SubgraphOf G) : ⇑f.toSimpleHom = ⇑f := rfl

/-- **A walk of the host that never leaves an induced subgraph comes from a walk of it.**  The
induced condition is what lets each step be taken in the subgraph, and injectivity is what makes
the vertex it passes through unique. -/
theorem InducedSubgraphOf.exists_walk_map (f : A.InducedSubgraphOf G) :
    ∀ {p q : G.V} (w : G.toSimple.Walk p q), (∀ z ∈ w.support, ∃ a : A.V, f a = z) →
      ∀ (u v : A.V) (hu : f u = p) (hv : f v = q),
        ∃ w' : A.toSimple.Walk u v, w'.map f.toSubgraphOf.toSimpleHom = w.copy hu.symm hv.symm := by
  intro p q w
  induction w with
  | @nil a =>
    intro _ u v hu hv
    have huv : u = v := f.injective (hu.trans hv.symm)
    subst huv
    subst hu
    exact ⟨.nil, rfl⟩
  | @cons a b c hadj w ih =>
    intro hw u v hu hv
    obtain ⟨m, hm⟩ := hw b (by simp)
    subst hu
    subst hm
    subst hv
    have hadj' : A.toSimple.Adj u m := f.adj_map hadj
    obtain ⟨w', hw'⟩ := ih (fun z hz ↦ hw z (by simp [hz])) m v rfl rfl
    refine ⟨.cons hadj' w', ?_⟩
    rw [SimpleGraph.Walk.map_cons]
    simp only [SimpleGraph.Walk.copy_rfl_rfl] at hw' ⊢
    rw [hw']

/-- **Connectedness pulls back along an induced subgraph inclusion**: a set of the host that is
connected and lies in the image is connected in the subgraph.  This is what the minor relations
need to be cut in two, since their branch sets have to stay connected on both sides. -/
theorem ConnectedOn.pullback (f : A.InducedSubgraphOf G) {s : Set G.V} (hs : G.ConnectedOn s)
    (hsub : ∀ v ∈ s, ∃ a : A.V, f a = v) : A.ConnectedOn {a | f a ∈ s} := by
  constructor
  · obtain ⟨v, hv⟩ := hs.nonempty
    obtain ⟨a, rfl⟩ := hsub v hv
    exact ⟨a, hv⟩
  · intro u hu v hv
    obtain ⟨w, hw⟩ := hs.walk hu hv
    obtain ⟨w', hw'⟩ := f.exists_walk_map w (fun z hz ↦ hsub z (hw z hz)) u v rfl rfl
    refine ⟨w', fun z hz ↦ ?_⟩
    have hmem : f z ∈ (w.copy rfl rfl).support := by
      rw [← hw', SimpleGraph.Walk.support_map]
      exact List.mem_map_of_mem hz
    simp only [SimpleGraph.Walk.copy_rfl_rfl] at hmem
    exact hw _ hmem

/-- The walk of the subgraph that a walk of the host staying inside it comes from.  The topological
minor and immersion relations need the pulled-back walk as *data* and not just as an existence
statement, because their axioms relate the walks of an edge and of its reverse. -/
noncomputable def InducedSubgraphOf.pullbackWalk (f : A.InducedSubgraphOf G) {u v : A.V}
    (w : G.toSimple.Walk (f u) (f v)) (hw : ∀ z ∈ w.support, ∃ a : A.V, f a = z) :
    A.toSimple.Walk u v :=
  (f.exists_walk_map w hw u v rfl rfl).choose

theorem InducedSubgraphOf.map_pullbackWalk (f : A.InducedSubgraphOf G) {u v : A.V}
    (w : G.toSimple.Walk (f u) (f v)) (hw : ∀ z ∈ w.support, ∃ a : A.V, f a = z) :
    (f.pullbackWalk w hw).map f.toSubgraphOf.toSimpleHom = w :=
  (f.exists_walk_map w hw u v rfl rfl).choose_spec

/-- The pullback is the only walk with that image, so a fact about it follows from exhibiting any
walk that maps to `w`. -/
theorem InducedSubgraphOf.pullbackWalk_eq (f : A.InducedSubgraphOf G) {u v : A.V}
    {w : G.toSimple.Walk (f u) (f v)} (hw : ∀ z ∈ w.support, ∃ a : A.V, f a = z)
    {w' : A.toSimple.Walk u v} (hw' : w'.map f.toSubgraphOf.toSimpleHom = w) :
    f.pullbackWalk w hw = w' :=
  SimpleGraph.Walk.map_injective_of_injective (f := f.toSubgraphOf.toSimpleHom) f.injective u v
    ((f.map_pullbackWalk w hw).trans hw'.symm)

end Walks

/-! ## The two sides of a disjoint union -/

section Sides

variable {C D : CGraph}

/-- The left summand is an induced subgraph of a disjoint union. -/
def InducedSubgraphOf.inl (C D : CGraph) : C.InducedSubgraphOf (C ⊕g D) where
  toFun := Sum.inl
  injective' := Sum.inl_injective
  map_adj' _ _ h := h
  adj_map' _ _ h := h

/-- The right summand is an induced subgraph of a disjoint union. -/
def InducedSubgraphOf.inr (C D : CGraph) : D.InducedSubgraphOf (C ⊕g D) where
  toFun := Sum.inr
  injective' := Sum.inr_injective
  map_adj' _ _ h := h
  adj_map' _ _ h := h

@[simp] theorem InducedSubgraphOf.coe_inl (C D : CGraph) :
    ⇑(InducedSubgraphOf.inl C D) = Sum.inl := rfl

@[simp] theorem InducedSubgraphOf.coe_inr (C D : CGraph) :
    ⇑(InducedSubgraphOf.inr C D) = Sum.inr := rfl

/-- Adjacent vertices of a disjoint union are on the same side. -/
theorem isLeft_eq_of_adj {u v : (C ⊕g D).V} (h : (C ⊕g D).Adj u v) : u.isLeft = v.isLeft := by
  cases u <;> cases v <;> simp_all

/-- A walk of a disjoint union never crosses between the summands. -/
theorem isLeft_of_mem_support {p q : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk p q) :
    ∀ z ∈ w.support, z.isLeft = p.isLeft := by
  induction w with
  | nil => simp
  | @cons a b c hadj w ih =>
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · rw [ih z hz, isLeft_eq_of_adj hadj]

theorem isLeft_of_mem_support' {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isLeft) {z : (C ⊕g D).V} (hz : z ∈ w.support) : z.isLeft :=
  (isLeft_of_mem_support w z hz).trans hu

theorem isRight_of_mem_support' {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isRight) {z : (C ⊕g D).V} (hz : z ∈ w.support) : z.isRight := by
  have h := isLeft_of_mem_support w z hz
  cases z <;> cases u <;> simp_all

/-- A connected set of a disjoint union lies wholly in one summand. -/
theorem ConnectedOn.isLeft_eq {s : Set (C ⊕g D).V} (hs : (C ⊕g D).ConnectedOn s) {u : (C ⊕g D).V}
    (hu : u ∈ s) {v : (C ⊕g D).V} (hv : v ∈ s) : u.isLeft = v.isLeft := by
  obtain ⟨w, _⟩ := hs.walk hu hv
  exact (isLeft_of_mem_support w v w.end_mem_support).symm

/-- A walk of a disjoint union out of the left summand stays inside the image of `Sum.inl`. -/
theorem exists_inl_of_mem_support {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isLeft) (hv : v.isLeft) :
    ∀ z ∈ (w.copy (Sum.eq_inl_getLeft u hu) (Sum.eq_inl_getLeft v hv)).support,
      ∃ a : C.V, (InducedSubgraphOf.inl C D) a = z := fun z hz ↦ by
  rw [SimpleGraph.Walk.support_copy] at hz
  exact ⟨z.getLeft (isLeft_of_mem_support' w hu hz),
    (Sum.eq_inl_getLeft z (isLeft_of_mem_support' w hu hz)).symm⟩

/-- A walk of a disjoint union out of the right summand stays inside the image of `Sum.inr`. -/
theorem exists_inr_of_mem_support {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isRight) (hv : v.isRight) :
    ∀ z ∈ (w.copy (Sum.eq_inr_getRight u hu) (Sum.eq_inr_getRight v hv)).support,
      ∃ a : D.V, (InducedSubgraphOf.inr C D) a = z := fun z hz ↦ by
  rw [SimpleGraph.Walk.support_copy] at hz
  exact ⟨z.getRight (isRight_of_mem_support' w hu hz),
    (Sum.eq_inr_getRight z (isRight_of_mem_support' w hu hz)).symm⟩

/-- A walk of a disjoint union between two vertices of the left summand, read as a walk there. -/
noncomputable def walkLeft {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isLeft) (hv : v.isLeft) : C.toSimple.Walk (u.getLeft hu) (v.getLeft hv) :=
  (InducedSubgraphOf.inl C D).pullbackWalk _ (exists_inl_of_mem_support w hu hv)

/-- A walk of a disjoint union between two vertices of the right summand, read as a walk there. -/
noncomputable def walkRight {u v : (C ⊕g D).V} (w : (C ⊕g D).toSimple.Walk u v)
    (hu : u.isRight) (hv : v.isRight) : D.toSimple.Walk (u.getRight hu) (v.getRight hv) :=
  (InducedSubgraphOf.inr C D).pullbackWalk _ (exists_inr_of_mem_support w hu hv)

variable {u v : (C ⊕g D).V}

theorem map_walkLeft (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isLeft) (hv : v.isLeft) :
    (walkLeft w hu hv).map (InducedSubgraphOf.inl C D).toSubgraphOf.toSimpleHom
      = w.copy (Sum.eq_inl_getLeft u hu) (Sum.eq_inl_getLeft v hv) :=
  (InducedSubgraphOf.inl C D).map_pullbackWalk _ (exists_inl_of_mem_support w hu hv)

theorem map_walkRight (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isRight) (hv : v.isRight) :
    (walkRight w hu hv).map (InducedSubgraphOf.inr C D).toSubgraphOf.toSimpleHom
      = w.copy (Sum.eq_inr_getRight u hu) (Sum.eq_inr_getRight v hv) :=
  (InducedSubgraphOf.inr C D).map_pullbackWalk _ (exists_inr_of_mem_support w hu hv)

theorem support_walkLeft (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isLeft) (hv : v.isLeft) :
    (walkLeft w hu hv).support.map Sum.inl = w.support := by
  have h := congrArg SimpleGraph.Walk.support (map_walkLeft w hu hv)
  rwa [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_copy] at h

theorem support_walkRight (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isRight) (hv : v.isRight) :
    (walkRight w hu hv).support.map Sum.inr = w.support := by
  have h := congrArg SimpleGraph.Walk.support (map_walkRight w hu hv)
  rwa [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_copy] at h

theorem edges_walkLeft (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isLeft) (hv : v.isLeft) :
    (walkLeft w hu hv).edges.map (Sym2.map Sum.inl) = w.edges := by
  have h := congrArg SimpleGraph.Walk.edges (map_walkLeft w hu hv)
  rwa [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_copy] at h

theorem edges_walkRight (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isRight) (hv : v.isRight) :
    (walkRight w hu hv).edges.map (Sym2.map Sum.inr) = w.edges := by
  have h := congrArg SimpleGraph.Walk.edges (map_walkRight w hu hv)
  rwa [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_copy] at h

theorem reverse_walkLeft (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isLeft) (hv : v.isLeft) :
    walkLeft w.reverse hv hu = (walkLeft w hu hv).reverse :=
  (InducedSubgraphOf.inl C D).pullbackWalk_eq _ (by
    rw [← SimpleGraph.Walk.reverse_map, map_walkLeft w hu hv, SimpleGraph.Walk.reverse_copy])

theorem reverse_walkRight (w : (C ⊕g D).toSimple.Walk u v) (hu : u.isRight) (hv : v.isRight) :
    walkRight w.reverse hv hu = (walkRight w hu hv).reverse :=
  (InducedSubgraphOf.inr C D).pullbackWalk_eq _ (by
    rw [← SimpleGraph.Walk.reverse_map, map_walkRight w hu hv, SimpleGraph.Walk.reverse_copy])

end Sides

/-! ## Cutting an inclusion in two -/

namespace SubgraphOf

variable {A C D : CGraph}

/-- Which side of a disjoint union each vertex of the pattern lands on. -/
def side (f : A.SubgraphOf (C ⊕g D)) (v : A.V) : Bool := (f v).isLeft

/-- No edge of the pattern crosses the sides: the host has no edge between its summands. -/
theorem side_eq_of_adj (f : A.SubgraphOf (C ⊕g D)) {x y : A.V} (h : A.Adj x y) :
    f.side x = f.side y := by
  have hadj := f.map_adj h
  cases hx : f x <;> cases hy : f y <;> rw [hx, hy] at hadj <;> simp_all [side]

theorem isRight_of_not_side (f : A.SubgraphOf (C ⊕g D)) {v : A.V} (h : !f.side v) :
    (f v).isRight := by
  cases hv : f v <;> simp_all [side]

/-- The part of a subgraph inclusion that lands in the left summand. -/
def splitLeft (f : A.SubgraphOf (C ⊕g D)) : (A.induce f.side).SubgraphOf C where
  toFun x := (f x.1).getLeft x.2
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2]
    exact congrArg Sum.inl hxy
  map_adj' x y hadj := by
    have h := f.map_adj (show A.Adj x.1 y.1 from hadj)
    rwa [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2] at h

/-- The part of a subgraph inclusion that lands in the right summand. -/
def splitRight (f : A.SubgraphOf (C ⊕g D)) : (A.induce fun v ↦ !f.side v).SubgraphOf D where
  toFun x := (f x.1).getRight (f.isRight_of_not_side x.2)
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inr_getRight (f x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.isRight_of_not_side y.2)]
    exact congrArg Sum.inr hxy
  map_adj' x y hadj := by
    have h := f.map_adj (show A.Adj x.1 y.1 from hadj)
    rwa [Sum.eq_inr_getRight (f x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.isRight_of_not_side y.2)] at h

/-- **A subgraph inclusion between two disjoint unions splits into four.**  Each summand of the
pattern is cut in two by the summand of the host its vertices land in. -/
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).SubgraphOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).SubgraphOf c) ∧ Nonempty ((h₂ ⊕g k₂).SubgraphOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

end SubgraphOf

namespace InducedSubgraphOf

variable {A C D : CGraph}

@[inherit_doc SubgraphOf.side]
def side (f : A.InducedSubgraphOf (C ⊕g D)) (v : A.V) : Bool := f.toSubgraphOf.side v

/-- The part of an induced subgraph inclusion that lands in the left summand. -/
def splitLeft (f : A.InducedSubgraphOf (C ⊕g D)) : (A.induce f.side).InducedSubgraphOf C where
  toSubgraphOf := f.toSubgraphOf.splitLeft
  adj_map' x y hadj := by
    refine f.adj_map (x := x.1) (y := y.1) ?_
    rw [Sum.eq_inl_getLeft (f x.1) x.2, Sum.eq_inl_getLeft (f y.1) y.2]
    exact hadj

/-- The part of an induced subgraph inclusion that lands in the right summand. -/
def splitRight (f : A.InducedSubgraphOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.side v).InducedSubgraphOf D where
  toSubgraphOf := f.toSubgraphOf.splitRight
  adj_map' x y hadj := by
    refine f.adj_map (x := x.1) (y := y.1) ?_
    rw [Sum.eq_inr_getRight (f x.1) (f.toSubgraphOf.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f y.1) (f.toSubgraphOf.isRight_of_not_side y.2)]
    exact hadj

@[inherit_doc SubgraphOf.exists_split]
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).InducedSubgraphOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).InducedSubgraphOf c) ∧ Nonempty ((h₂ ⊕g k₂).InducedSubgraphOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.toSubgraphOf.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.toSubgraphOf.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

/-- **Complementation carries an induced subgraph inclusion to one between the complements.**  An
induced subgraph is decided by which vertices it keeps, and both graphs trade their edges for
their non-edges at once. -/
def compl {H G : CGraph} (f : H.InducedSubgraphOf G) : Hᶜ.InducedSubgraphOf Gᶜ where
  toFun := f
  injective' := f.injective
  map_adj' x y h := by
    simp only [compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true'] at h ⊢
    exact ⟨fun he ↦ h.1 (f.injective he), by rw [f.adj_eq]; exact h.2⟩
  adj_map' x y h := by
    simp only [compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true'] at h ⊢
    exact ⟨fun he ↦ h.1 (congrArg f he), by rw [← f.adj_eq]; exact h.2⟩

end InducedSubgraphOf

section Minors

variable {A C D : CGraph}

namespace MinorOf

/-- Which side of a disjoint union a branch set lies in. -/
noncomputable def side (f : A.MinorOf (C ⊕g D)) (x : A.V) : Bool :=
  ((f.connectedOn x).nonempty.choose).isLeft

theorem isLeft_eq_side (f : A.MinorOf (C ⊕g D)) {x : A.V} {v : (C ⊕g D).V}
    (hv : f.branch v = some x) : v.isLeft = f.side x :=
  (f.connectedOn x).isLeft_eq hv (f.connectedOn x).nonempty.choose_spec

/-- No edge of the pattern crosses the sides. -/
theorem side_eq_of_adj (f : A.MinorOf (C ⊕g D)) {x y : A.V} (h : A.Adj x y) :
    f.side x = f.side y := by
  obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj h
  rw [← f.isLeft_eq_side hu, ← f.isLeft_eq_side hv]
  exact isLeft_eq_of_adj huv

theorem eq_inl (f : A.MinorOf (C ⊕g D)) {x : A.V} (hx : f.side x) {v : (C ⊕g D).V}
    (hv : f.branch v = some x) : ∃ w : C.V, v = .inl w := by
  cases v with
  | inl w => exact ⟨w, rfl⟩
  | inr w => exact absurd ((f.isLeft_eq_side hv).trans hx) (by simp)

theorem eq_inr (f : A.MinorOf (C ⊕g D)) {x : A.V} (hx : !f.side x) {v : (C ⊕g D).V}
    (hv : f.branch v = some x) : ∃ w : D.V, v = .inr w := by
  cases v with
  | inl w => exact absurd (f.isLeft_eq_side hv) (by simp_all)
  | inr w => exact ⟨w, rfl⟩

/-- The branch map of the part of a minor model that lies in the left summand. -/
noncomputable def branchLeft (f : A.MinorOf (C ⊕g D)) (w : C.V) : Option (A.induce f.side).V :=
  (f.branch (.inl w)).bind fun x ↦ if h : f.side x then some ⟨x, h⟩ else none

theorem branchLeft_eq_some (f : A.MinorOf (C ⊕g D)) (w : C.V) (x : (A.induce f.side).V) :
    f.branchLeft w = some x ↔ f.branch (.inl w) = some x.1 := by
  rcases hb : f.branch (Sum.inl w) with _ | y
  · simp [branchLeft, hb]
  · by_cases hy : f.side y
    · simp only [branchLeft, hb, Option.bind_some, dif_pos hy, Option.some.injEq]
      exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
    · refine ⟨fun h ↦ by simp [branchLeft, hb, hy] at h, fun h ↦ ?_⟩
      have hxy : y = x.1 := by simpa using h
      subst hxy
      exact absurd x.2 hy

/-- The branch map of the part of a minor model that lies in the right summand. -/
noncomputable def branchRight (f : A.MinorOf (C ⊕g D)) (w : D.V) :
    Option (A.induce fun v ↦ !f.side v).V :=
  (f.branch (.inr w)).bind fun x ↦ if h : !f.side x then some ⟨x, h⟩ else none

theorem branchRight_eq_some (f : A.MinorOf (C ⊕g D)) (w : D.V)
    (x : (A.induce fun v ↦ !f.side v).V) :
    f.branchRight w = some x ↔ f.branch (.inr w) = some x.1 := by
  rcases hb : f.branch (Sum.inr w) with _ | y
  · simp [branchRight, hb]
  · by_cases hy : !f.side y
    · simp only [branchRight, hb, Option.bind_some, dif_pos hy, Option.some.injEq]
      exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
    · refine ⟨fun h ↦ by
        simp only [branchRight, hb, Option.bind_some, dif_neg hy] at h
        exact absurd h (by simp), fun h ↦ ?_⟩
      have hxy : y = x.1 := by simpa using h
      subst hxy
      exact absurd x.2 hy

/-- The part of a minor model that lies in the left summand. -/
noncomputable def splitLeft (f : A.MinorOf (C ⊕g D)) : (A.induce f.side).MinorOf C where
  branch := f.branchLeft
  connectedOn' x := by
    have hset : {w : C.V | f.branchLeft w = some x}
        = {a : C.V | (InducedSubgraphOf.inl C D) a ∈ {v | f.branch v = some x.1}} := by
      ext w
      simpa using f.branchLeft_eq_some w x
    rw [hset]
    refine ConnectedOn.pullback _ (f.connectedOn x.1) fun v hv ↦ ?_
    obtain ⟨u, rfl⟩ := f.eq_inl x.2 hv
    exact ⟨u, rfl⟩
  map_adj' x y h := by
    obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj (show A.Adj x.1 y.1 from h)
    obtain ⟨u', rfl⟩ := f.eq_inl x.2 hu
    obtain ⟨v', rfl⟩ := f.eq_inl y.2 hv
    exact ⟨u', v', (f.branchLeft_eq_some u' x).2 hu, (f.branchLeft_eq_some v' y).2 hv,
      by simpa using huv⟩

/-- The part of a minor model that lies in the right summand. -/
noncomputable def splitRight (f : A.MinorOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.side v).MinorOf D where
  branch := f.branchRight
  connectedOn' x := by
    have hset : {w : D.V | f.branchRight w = some x}
        = {a : D.V | (InducedSubgraphOf.inr C D) a ∈ {v | f.branch v = some x.1}} := by
      ext w
      simpa using f.branchRight_eq_some w x
    rw [hset]
    refine ConnectedOn.pullback _ (f.connectedOn x.1) fun v hv ↦ ?_
    obtain ⟨u, rfl⟩ := f.eq_inr x.2 hv
    exact ⟨u, rfl⟩
  map_adj' x y h := by
    obtain ⟨u, v, hu, hv, huv⟩ := f.map_adj (show A.Adj x.1 y.1 from h)
    obtain ⟨u', rfl⟩ := f.eq_inr x.2 hu
    obtain ⟨v', rfl⟩ := f.eq_inr y.2 hv
    exact ⟨u', v', (f.branchRight_eq_some u' x).2 hu, (f.branchRight_eq_some v' y).2 hv,
      by simpa using huv⟩

/-- **A minor model of a disjoint union splits into four.** -/
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).MinorOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).MinorOf c) ∧ Nonempty ((h₂ ⊕g k₂).MinorOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

end MinorOf

namespace InducedMinorOf

/-- The part of an induced minor model that lies in the left summand. -/
noncomputable def splitLeft (f : A.InducedMinorOf (C ⊕g D)) :
    (A.induce f.toMinorOf.side).InducedMinorOf C where
  toMinorOf := f.toMinorOf.splitLeft
  adj_map' x y hne := by
    rintro ⟨u, v, hu, hv, huv⟩
    refine f.adj_map (x := x.1) (y := y.1) (fun he ↦ hne (Subtype.ext he)) ?_
    exact ⟨.inl u, .inl v, (f.toMinorOf.branchLeft_eq_some u x).1 hu,
      (f.toMinorOf.branchLeft_eq_some v y).1 hv, by simpa using huv⟩

/-- The part of an induced minor model that lies in the right summand. -/
noncomputable def splitRight (f : A.InducedMinorOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.toMinorOf.side v).InducedMinorOf D where
  toMinorOf := f.toMinorOf.splitRight
  adj_map' x y hne := by
    rintro ⟨u, v, hu, hv, huv⟩
    refine f.adj_map (x := x.1) (y := y.1) (fun he ↦ hne (Subtype.ext he)) ?_
    exact ⟨.inr u, .inr v, (f.toMinorOf.branchRight_eq_some u x).1 hu,
      (f.toMinorOf.branchRight_eq_some v y).1 hv, by simpa using huv⟩

@[inherit_doc MinorOf.exists_split]
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).InducedMinorOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).InducedMinorOf c) ∧ Nonempty ((h₂ ⊕g k₂).InducedMinorOf d) :=
  ⟨h.induce fun v ↦ f.toMinorOf.side (.inl v), h.induce fun v ↦ !f.toMinorOf.side (.inl v),
    k.induce fun v ↦ f.toMinorOf.side (.inr v), k.induce fun v ↦ !f.toMinorOf.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.toMinorOf.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.toMinorOf.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.toMinorOf.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.toMinorOf.side v) (RelIso.refl _)⟩⟩

end InducedMinorOf

namespace ContractionOf

/-- The part of a contraction that lies in the left summand. -/
noncomputable def splitLeft (f : A.ContractionOf (C ⊕g D)) :
    (A.induce f.toMinorOf.side).ContractionOf C where
  toInducedMinorOf := f.toInducedMinorOf.splitLeft
  total' w := by
    rcases hb : f.branch (Sum.inl w) with _ | x
    · exact absurd (f.total (Sum.inl w)) (by simp [hb])
    · have hx : f.toMinorOf.side x := (f.toMinorOf.isLeft_eq_side hb).symm
      exact Option.isSome_of_eq_some
        ((f.toMinorOf.branchLeft_eq_some w ⟨x, hx⟩).2 hb)

/-- The part of a contraction that lies in the right summand. -/
noncomputable def splitRight (f : A.ContractionOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.toMinorOf.side v).ContractionOf D where
  toInducedMinorOf := f.toInducedMinorOf.splitRight
  total' w := by
    rcases hb : f.branch (Sum.inr w) with _ | x
    · exact absurd (f.total (Sum.inr w)) (by simp [hb])
    · have hx : !f.toMinorOf.side x := by
        have := f.toMinorOf.isLeft_eq_side hb
        simp_all
      exact Option.isSome_of_eq_some
        ((f.toMinorOf.branchRight_eq_some w ⟨x, hx⟩).2 hb)

@[inherit_doc MinorOf.exists_split]
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).ContractionOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).ContractionOf c) ∧ Nonempty ((h₂ ⊕g k₂).ContractionOf d) :=
  ⟨h.induce fun v ↦ f.toMinorOf.side (.inl v), h.induce fun v ↦ !f.toMinorOf.side (.inl v),
    k.induce fun v ↦ f.toMinorOf.side (.inr v), k.induce fun v ↦ !f.toMinorOf.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.toMinorOf.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.toMinorOf.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.toMinorOf.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.toMinorOf.side v) (RelIso.refl _)⟩⟩

end ContractionOf

namespace TopMinorOf

/-- Which side of a disjoint union each branch vertex lands on. -/
def side (f : A.TopMinorOf (C ⊕g D)) (x : A.V) : Bool := (f.toFun x).isLeft

/-- No edge of the pattern crosses the sides: its path would have to. -/
theorem side_eq_of_adj (f : A.TopMinorOf (C ⊕g D)) {x y : A.V} (h : A.Adj x y) :
    f.side x = f.side y :=
  (isLeft_of_mem_support (f.path h) _ (f.path h).end_mem_support).symm

theorem isRight_of_not_side (f : A.TopMinorOf (C ⊕g D)) {v : A.V} (h : !f.side v) :
    (f.toFun v).isRight := by
  cases hv : f.toFun v <;> simp_all [side]

/-- The part of a topological minor model that lies in the left summand. -/
noncomputable def splitLeft (f : A.TopMinorOf (C ⊕g D)) : (A.induce f.side).TopMinorOf C where
  toFun x := (f.toFun x.1).getLeft x.2
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inl_getLeft (f.toFun x.1) x.2, Sum.eq_inl_getLeft (f.toFun y.1) y.2]
    exact congrArg Sum.inl hxy
  path {x y} h := walkLeft (f.path (show A.Adj x.1 y.1 from h)) x.2 y.2
  isPath' {x y} h := by
    have hn := (f.isPath' (show A.Adj x.1 y.1 from h)).support_nodup
    rw [← support_walkLeft (f.path (show A.Adj x.1 y.1 from h)) x.2 y.2] at hn
    exact SimpleGraph.Walk.isPath_def _ |>.2 (List.Nodup.of_map _ hn)
  reverse' {x y} h h' := by
    rw [show f.path (show A.Adj y.1 x.1 from h')
        = (f.path (show A.Adj x.1 y.1 from h)).reverse from f.reverse' _ _]
    exact reverse_walkLeft _ x.2 y.2
  branch' {x y} h z hz := by
    have hz' : f.toFun z.1 ∈ (f.path (show A.Adj x.1 y.1 from h)).support := by
      rw [← support_walkLeft (f.path (show A.Adj x.1 y.1 from h)) x.2 y.2,
        Sum.eq_inl_getLeft (f.toFun z.1) z.2]
      exact List.mem_map_of_mem (f := Sum.inl) hz
    rcases f.branch' _ z.1 hz' with hzx | hzy
    · exact Or.inl (Subtype.ext hzx)
    · exact Or.inr (Subtype.ext hzy)
  disjoint' {x y} h {x' y'} h' hne z hz hz' := by
    have hne' : s(x.1, y.1) ≠ s(x'.1, y'.1) := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have hzl : (Sum.inl z : (C ⊕g D).V) ∈ (f.path (show A.Adj x.1 y.1 from h)).support := by
      rw [← support_walkLeft (f.path (show A.Adj x.1 y.1 from h)) x.2 y.2]
      exact List.mem_map_of_mem (f := Sum.inl) hz
    have hzl' : (Sum.inl z : (C ⊕g D).V) ∈ (f.path (show A.Adj x'.1 y'.1 from h')).support := by
      rw [← support_walkLeft (f.path (show A.Adj x'.1 y'.1 from h')) x'.2 y'.2]
      exact List.mem_map_of_mem (f := Sum.inl) hz'
    obtain ⟨b, hb⟩ := f.disjoint' _ _ hne' _ hzl hzl'
    have hbside : f.side b := by show (f.toFun b).isLeft = true; rw [← hb]; rfl
    exact ⟨⟨b, hbside⟩, Sum.inl_injective (hb.trans (Sum.eq_inl_getLeft (f.toFun b) hbside))⟩

/-- The part of a topological minor model that lies in the right summand. -/
noncomputable def splitRight (f : A.TopMinorOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.side v).TopMinorOf D where
  toFun x := (f.toFun x.1).getRight (f.isRight_of_not_side x.2)
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inr_getRight (f.toFun x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f.toFun y.1) (f.isRight_of_not_side y.2)]
    exact congrArg Sum.inr hxy
  path {x y} h := walkRight (f.path (show A.Adj x.1 y.1 from h))
    (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)
  isPath' {x y} h := by
    have hn := (f.isPath' (show A.Adj x.1 y.1 from h)).support_nodup
    rw [← support_walkRight (f.path (show A.Adj x.1 y.1 from h))
      (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)] at hn
    exact SimpleGraph.Walk.isPath_def _ |>.2 (List.Nodup.of_map _ hn)
  reverse' {x y} h h' := by
    rw [show f.path (show A.Adj y.1 x.1 from h')
        = (f.path (show A.Adj x.1 y.1 from h)).reverse from f.reverse' _ _]
    exact reverse_walkRight _ (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)
  branch' {x y} h z hz := by
    have hz' : f.toFun z.1 ∈ (f.path (show A.Adj x.1 y.1 from h)).support := by
      rw [← support_walkRight (f.path (show A.Adj x.1 y.1 from h))
          (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2),
        Sum.eq_inr_getRight (f.toFun z.1) (f.isRight_of_not_side z.2)]
      exact List.mem_map_of_mem (f := Sum.inr) hz
    rcases f.branch' _ z.1 hz' with hzx | hzy
    · exact Or.inl (Subtype.ext hzx)
    · exact Or.inr (Subtype.ext hzy)
  disjoint' {x y} h {x' y'} h' hne z hz hz' := by
    have hne' : s(x.1, y.1) ≠ s(x'.1, y'.1) := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have hzl : (Sum.inr z : (C ⊕g D).V) ∈ (f.path (show A.Adj x.1 y.1 from h)).support := by
      rw [← support_walkRight (f.path (show A.Adj x.1 y.1 from h))
        (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)]
      exact List.mem_map_of_mem (f := Sum.inr) hz
    have hzl' : (Sum.inr z : (C ⊕g D).V) ∈ (f.path (show A.Adj x'.1 y'.1 from h')).support := by
      rw [← support_walkRight (f.path (show A.Adj x'.1 y'.1 from h'))
        (f.isRight_of_not_side x'.2) (f.isRight_of_not_side y'.2)]
      exact List.mem_map_of_mem (f := Sum.inr) hz'
    obtain ⟨b, hb⟩ := f.disjoint' _ _ hne' _ hzl hzl'
    have hbside : !f.side b := by
      show (!(f.toFun b).isLeft) = true
      rw [← hb]; rfl
    exact ⟨⟨b, hbside⟩,
      Sum.inr_injective (hb.trans (Sum.eq_inr_getRight (f.toFun b) (f.isRight_of_not_side hbside)))⟩

/-- **A topological minor model of a disjoint union splits into four.** -/
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).TopMinorOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).TopMinorOf c) ∧ Nonempty ((h₂ ⊕g k₂).TopMinorOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

end TopMinorOf

namespace ImmersionOf

/-- Which side of a disjoint union each branch vertex lands on. -/
def side (f : A.ImmersionOf (C ⊕g D)) (x : A.V) : Bool := (f.toFun x).isLeft

/-- No edge of the pattern crosses the sides: its trail would have to. -/
theorem side_eq_of_adj (f : A.ImmersionOf (C ⊕g D)) {x y : A.V} (h : A.Adj x y) :
    f.side x = f.side y :=
  (isLeft_of_mem_support (f.walk h) _ (f.walk h).end_mem_support).symm

theorem isRight_of_not_side (f : A.ImmersionOf (C ⊕g D)) {v : A.V} (h : !f.side v) :
    (f.toFun v).isRight := by
  cases hv : f.toFun v <;> simp_all [side]

/-- The part of an immersion that lies in the left summand. -/
noncomputable def splitLeft (f : A.ImmersionOf (C ⊕g D)) : (A.induce f.side).ImmersionOf C where
  toFun x := (f.toFun x.1).getLeft x.2
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inl_getLeft (f.toFun x.1) x.2, Sum.eq_inl_getLeft (f.toFun y.1) y.2]
    exact congrArg Sum.inl hxy
  walk {x y} h := walkLeft (f.walk (show A.Adj x.1 y.1 from h)) x.2 y.2
  isTrail' {x y} h := by
    have hn := (f.isTrail' (show A.Adj x.1 y.1 from h)).edges_nodup
    rw [← edges_walkLeft (f.walk (show A.Adj x.1 y.1 from h)) x.2 y.2] at hn
    exact SimpleGraph.Walk.isTrail_def _ |>.2 (List.Nodup.of_map _ hn)
  reverse' {x y} h h' := by
    rw [show f.walk (show A.Adj y.1 x.1 from h')
        = (f.walk (show A.Adj x.1 y.1 from h)).reverse from f.reverse' _ _]
    exact reverse_walkLeft _ x.2 y.2
  edgeDisjoint' {x y} h {x' y'} h' hne e he he' := by
    have hne' : s(x.1, y.1) ≠ s(x'.1, y'.1) := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    refine f.edgeDisjoint' (show A.Adj x.1 y.1 from h) (show A.Adj x'.1 y'.1 from h') hne'
      (Sym2.map Sum.inl e) ?_ ?_
    · rw [← edges_walkLeft (f.walk (show A.Adj x.1 y.1 from h)) x.2 y.2]
      exact List.mem_map_of_mem (f := Sym2.map Sum.inl) he
    · rw [← edges_walkLeft (f.walk (show A.Adj x'.1 y'.1 from h')) x'.2 y'.2]
      exact List.mem_map_of_mem (f := Sym2.map Sum.inl) he'

/-- The part of an immersion that lies in the right summand. -/
noncomputable def splitRight (f : A.ImmersionOf (C ⊕g D)) :
    (A.induce fun v ↦ !f.side v).ImmersionOf D where
  toFun x := (f.toFun x.1).getRight (f.isRight_of_not_side x.2)
  injective' x y hxy := by
    apply Subtype.ext
    apply f.injective
    rw [Sum.eq_inr_getRight (f.toFun x.1) (f.isRight_of_not_side x.2),
      Sum.eq_inr_getRight (f.toFun y.1) (f.isRight_of_not_side y.2)]
    exact congrArg Sum.inr hxy
  walk {x y} h := walkRight (f.walk (show A.Adj x.1 y.1 from h))
    (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)
  isTrail' {x y} h := by
    have hn := (f.isTrail' (show A.Adj x.1 y.1 from h)).edges_nodup
    rw [← edges_walkRight (f.walk (show A.Adj x.1 y.1 from h))
      (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)] at hn
    exact SimpleGraph.Walk.isTrail_def _ |>.2 (List.Nodup.of_map _ hn)
  reverse' {x y} h h' := by
    rw [show f.walk (show A.Adj y.1 x.1 from h')
        = (f.walk (show A.Adj x.1 y.1 from h)).reverse from f.reverse' _ _]
    exact reverse_walkRight _ (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)
  edgeDisjoint' {x y} h {x' y'} h' hne e he he' := by
    have hne' : s(x.1, y.1) ≠ s(x'.1, y'.1) := by
      rw [Ne, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine hne ?_ <;> rw [Sym2.eq_iff]
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    refine f.edgeDisjoint' (show A.Adj x.1 y.1 from h) (show A.Adj x'.1 y'.1 from h') hne'
      (Sym2.map Sum.inr e) ?_ ?_
    · rw [← edges_walkRight (f.walk (show A.Adj x.1 y.1 from h))
        (f.isRight_of_not_side x.2) (f.isRight_of_not_side y.2)]
      exact List.mem_map_of_mem (f := Sym2.map Sum.inr) he
    · rw [← edges_walkRight (f.walk (show A.Adj x'.1 y'.1 from h'))
        (f.isRight_of_not_side x'.2) (f.isRight_of_not_side y'.2)]
      exact List.mem_map_of_mem (f := Sym2.map Sum.inr) he'

/-- **An immersion of a disjoint union splits into four.** -/
theorem exists_split {h k c d : CGraph} (f : (h ⊕g k).ImmersionOf (c ⊕g d)) :
    ∃ h₁ h₂ k₁ k₂ : CGraph, Nonempty (h ≃cg h₁ ⊕g h₂) ∧ Nonempty (k ≃cg k₁ ⊕g k₂) ∧
      Nonempty ((h₁ ⊕g k₁).ImmersionOf c) ∧ Nonempty ((h₂ ⊕g k₂).ImmersionOf d) :=
  ⟨h.induce fun v ↦ f.side (.inl v), h.induce fun v ↦ !f.side (.inl v),
    k.induce fun v ↦ f.side (.inr v), k.induce fun v ↦ !f.side (.inr v),
    ⟨Iso.induceSplit h _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inl x) (.inl y) from hxy)⟩,
    ⟨Iso.induceSplit k _ fun x y hxy ↦
      f.side_eq_of_adj (show (h ⊕g k).Adj (.inr x) (.inr y) from hxy)⟩,
    ⟨f.splitLeft.congr (Iso.induceDisjUnion h k f.side) (RelIso.refl _)⟩,
    ⟨f.splitRight.congr (Iso.induceDisjUnion h k fun v ↦ !f.side v) (RelIso.refl _)⟩⟩

end ImmersionOf

end Minors

/-! ## Cancelling a cone

The join does not split — every vertex of one side is adjacent to every vertex of the other, so
nothing forces a component of the pattern to stay on one side — but when what is joined on is a
single vertex there is nowhere for it to go, and the map can be repaired by hand. -/

section Cone

variable {A B : CGraph}

/-- The cone has one apex. -/
theorem complete_one_subsingleton (a b : (complete 1).V) : a = b :=
  Subsingleton.elim (α := Fin 1) a b

/-- **Cancelling a cone.**  A map of the cone over `A` into the cone over `B` that carries edges
to edges restricts to one of `A` into `B`, and keeps injectivity and surjectivity while it does.

There are two cases.  Either the apex goes to the apex, and then nothing else can — a vertex of
`A` is adjacent to the apex, and the apex is adjacent to no vertex of the cone but the ones of
`B` — so the map already runs from `A` to `B`.  Or the apex goes to a vertex `b₀` of `B`, which is
then adjacent to the image of every vertex of `A`; sending to `b₀` everything that lands on the
apex is again a map of the kind, because two vertices of `A` cannot both land there. -/
theorem exists_map_of_join_complete_one (f : (A ∇g complete 1).V → (B ∇g complete 1).V)
    (hadj : ∀ x y, (A ∇g complete 1).Adj x y → (B ∇g complete 1).Adj (f x) (f y)) :
    ∃ g : A.V → B.V, (∀ x y, A.Adj x y → B.Adj (g x) (g y)) ∧
      (Function.Injective f → Function.Injective g) ∧
      (Function.Surjective f → Function.Surjective g) := by
  let v : (complete 1).V := (0 : Fin 1)
  have hap : ∀ x : A.V, (B ∇g complete 1).Adj (f (Sum.inl x)) (f (Sum.inr v)) := fun x ↦
    hadj _ _ (by simp [join_adj_inl_inr])
  rcases hz : f (Sum.inr v) with b₀ | u
  · -- the apex goes to a vertex of `B`, adjacent to the image of everything
    refine ⟨fun x ↦ Sum.elim id (fun _ ↦ b₀) (f (Sum.inl x)), ?_, ?_, ?_⟩
    · intro a b hab
      have hf : (B ∇g complete 1).Adj (f (Sum.inl a)) (f (Sum.inl b)) :=
        hadj _ _ (by simpa [join_adj_inl_inl] using hab)
      have ha := hap a
      have hb := hap b
      rw [hz] at ha hb
      rcases hx : f (Sum.inl a) with ba | ua <;> rcases hy : f (Sum.inl b) with bb | ub <;>
        rw [hx] at hf ha <;> rw [hy] at hf hb <;>
        simp only [hx, hy, Sum.elim_inl, Sum.elim_inr, id_eq]
      · rwa [join_adj_inl_inl] at hf
      · rwa [join_adj_inl_inl] at ha
      · rw [B.symm]; rwa [join_adj_inl_inl] at hb
      · rw [join_adj_inr_inr, complete_one_subsingleton ua ub] at hf
        simp at hf
    · intro hinj a b hg
      simp only at hg
      rcases hx : f (Sum.inl a) with ba | ua <;> rcases hy : f (Sum.inl b) with bb | ub <;>
        rw [hx, hy] at hg <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at hg
      · exact Sum.inl_injective (hinj (by rw [hx, hy, hg]))
      · exact absurd (hinj (show f (Sum.inl a) = f (Sum.inr v) by rw [hx, hz, hg]))
          Sum.inl_ne_inr
      · exact absurd (hinj (show f (Sum.inr v) = f (Sum.inl b) by rw [hy, hz, hg]))
          Sum.inr_ne_inl
      · exact Sum.inl_injective (hinj (by rw [hx, hy, complete_one_subsingleton ua ub]))
    · intro hsurj y
      obtain ⟨x, hx⟩ := hsurj (Sum.inl y)
      rcases x with a | w
      · exact ⟨a, by simp [hx]⟩
      · -- the apex side of the source goes to `b₀`, so `y` is `b₀`, and something else goes there
        rw [complete_one_subsingleton w v, hz] at hx
        obtain ⟨x', hx'⟩ := hsurj (Sum.inr v)
        rcases x' with a' | w'
        · refine ⟨a', ?_⟩
          show Sum.elim id (fun _ ↦ b₀) (f (Sum.inl a')) = y
          rw [hx', Sum.elim_inr, Sum.inl_injective hx]
        · rw [complete_one_subsingleton w' v, hz] at hx'
          exact absurd hx' Sum.inl_ne_inr
  · -- the apex goes to the apex, and then nothing else can
    have hleft : ∀ x : A.V, (f (Sum.inl x)).isLeft := by
      intro x
      have hx' := hap x
      rw [hz] at hx'
      rcases hx : f (Sum.inl x) with b | w
      · rfl
      · rw [hx, join_adj_inr_inr, complete_one_subsingleton w u] at hx'
        simp at hx'
    refine ⟨fun x ↦ (f (Sum.inl x)).getLeft (hleft x), ?_, ?_, ?_⟩
    · intro a b hab
      have hf : (B ∇g complete 1).Adj (f (Sum.inl a)) (f (Sum.inl b)) :=
        hadj _ _ (by simpa [join_adj_inl_inl] using hab)
      rw [Sum.eq_inl_getLeft _ (hleft a), Sum.eq_inl_getLeft _ (hleft b), join_adj_inl_inl] at hf
      exact hf
    · intro hinj a b hg
      refine Sum.inl_injective (hinj ?_)
      rw [Sum.eq_inl_getLeft _ (hleft a), Sum.eq_inl_getLeft _ (hleft b)]
      exact congrArg Sum.inl hg
    · intro hsurj y
      obtain ⟨x, hx⟩ := hsurj (Sum.inl y)
      rcases x with a | w
      · refine ⟨a, ?_⟩
        show (f (Sum.inl a)).getLeft (hleft a) = y
        exact Sum.inl_injective ((Sum.eq_inl_getLeft _ (hleft a)).symm.trans hx)
      · rw [complete_one_subsingleton w v, hz] at hx
        exact absurd hx Sum.inr_ne_inl

/-- **A homomorphism of one cone into another comes from one of the bases.** -/
theorem nonempty_hom_of_join_complete_one (f : (A ∇g complete 1) →cg (B ∇g complete 1)) :
    Nonempty (A →cg B) := by
  obtain ⟨g, hg, -, -⟩ := exists_map_of_join_complete_one (⇑f) fun _ _ h ↦ f.map_rel h
  exact ⟨⟨g, fun {a b} h ↦ hg a b h⟩⟩

/-- **A cone inside a cone puts the base inside the base.** -/
theorem nonempty_subgraphOf_of_join_complete_one
    (f : (A ∇g complete 1).SubgraphOf (B ∇g complete 1)) : Nonempty (A.SubgraphOf B) := by
  obtain ⟨g, hg, hinj, -⟩ := exists_map_of_join_complete_one (⇑f) fun _ _ h ↦ f.map_adj h
  exact ⟨⟨g, hinj f.injective, hg⟩⟩

/-- **A cone that is a quotient of a cone has a base that is a quotient of the base.** -/
theorem nonempty_quotientOf_of_join_complete_one
    (f : (A ∇g complete 1).QuotientOf (B ∇g complete 1)) : Nonempty (A.QuotientOf B) := by
  obtain ⟨g, hg, -, hsurj⟩ := exists_map_of_join_complete_one (⇑f) fun _ _ h ↦ f.map_adj h
  exact ⟨⟨g, hsurj f.surjective, hg⟩⟩

end Cone

end CGraph

/-! ## On isomorphism classes -/

namespace IsoGraph

/-- **A subgraph inclusion between two disjoint unions splits into four.**  Each summand of the
pattern is cut in two by the summand of the host its vertices land in. -/
theorem IsSubgraphOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₛ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₛ C ∧ H₂ ⊕g K₂ ≤ₛ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isSubgraphOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isSubgraphOf_mk]; exact fc,
    by rw [disjUnion_mk, isSubgraphOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsInducedSubgraphOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ᵢₛ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ᵢₛ C ∧ H₂ ⊕g K₂ ≤ᵢₛ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isInducedSubgraphOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isInducedSubgraphOf_mk]; exact fc,
    by rw [disjUnion_mk, isInducedSubgraphOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsMinorOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₘ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₘ C ∧ H₂ ⊕g K₂ ≤ₘ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isMinorOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isMinorOf_mk]; exact fc,
    by rw [disjUnion_mk, isMinorOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsInducedMinorOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ᵢₘ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ᵢₘ C ∧ H₂ ⊕g K₂ ≤ᵢₘ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isInducedMinorOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isInducedMinorOf_mk]; exact fc,
    by rw [disjUnion_mk, isInducedMinorOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsContractionOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₚ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₚ C ∧ H₂ ⊕g K₂ ≤ₚ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isContractionOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isContractionOf_mk]; exact fc,
    by rw [disjUnion_mk, isContractionOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsTopMinorOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₜₘ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₜₘ C ∧ H₂ ⊕g K₂ ≤ₜₘ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isTopMinorOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isTopMinorOf_mk]; exact fc,
    by rw [disjUnion_mk, isTopMinorOf_mk]; exact fd⟩

@[inherit_doc IsSubgraphOf.exists_split_disjUnion]
theorem IsImmersionMinorOf.exists_split_disjUnion {H K C D : IsoGraph} (hf : H ⊕g K ≤ₑ C ⊕g D) :
    ∃ H₁ H₂ K₁ K₂ : IsoGraph, H = H₁ ⊕g H₂ ∧ K = K₁ ⊕g K₂ ∧
      H₁ ⊕g K₁ ≤ₑ C ∧ H₂ ⊕g K₂ ≤ₑ D := by
  revert hf
  refine Quotient.inductionOn₂ H K ?_
  intro h k
  refine Quotient.inductionOn₂ C D ?_
  rintro c d hf
  rw [disjUnion_mk, disjUnion_mk, isImmersionMinorOf_mk] at hf
  obtain ⟨f⟩ := hf
  obtain ⟨h₁, h₂, k₁, k₂, ih, ik, fc, fd⟩ := f.exists_split
  exact ⟨⟦h₁⟧, ⟦h₂⟧, ⟦k₁⟧, ⟦k₂⟧, by rw [disjUnion_mk]; exact Quotient.sound ih,
    by rw [disjUnion_mk]; exact Quotient.sound ik,
    by rw [disjUnion_mk, isImmersionMinorOf_mk]; exact fc,
    by rw [disjUnion_mk, isImmersionMinorOf_mk]; exact fd⟩

@[inherit_doc CGraph.InducedSubgraphOf.compl]
theorem IsInducedSubgraphOf.compl {H G : IsoGraph} (h : H ≤ᵢₛ G) : Hᶜ ≤ᵢₛ Gᶜ := by
  revert h
  refine Quotient.inductionOn₂ H G ?_
  rintro h g ⟨f⟩
  exact ⟨f.compl⟩

end IsoGraph
