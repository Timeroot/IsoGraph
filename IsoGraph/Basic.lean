import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sort
import IsoGraph.Spec

/-!
# Graphs up to isomorphism

This file follows `isograph_draft.txt`: a bundled, computable graph type `CGraph`, its
isomorphisms, and the quotient `IsoGraph` of graphs up to isomorphism.

Everything that has to be lifted through the quotient — in particular the canonical
representative `IsoGraph.toCGraph` — is reduced here to the single obligation
`IsoGraph.Canon.canonAdj_relabel` of `IsoGraph.Spec`, namely that the canonical labelling
algorithm is invariant under renaming vertices.  No other `sorry` remains in this file.
-/

open Fintype

/-- Computable graphs with bundled vertex type. -/
structure CGraph where
  /-- The vertex type. -/
  V : Type
  [fin : Fintype V]
  /-- The adjacency relation, as a decidable predicate. -/
  Adj : V → V → Bool
  /-- Adjacency is symmetric. -/
  symm x y : Adj x y = Adj y x
  /-- There are no loops. -/
  loopless x : ¬Adj x x

attribute [instance] CGraph.fin

/-- Two `CGraph`s with the same vertex type and the same adjacency function are equal: the
`Fintype` field is a subsingleton and the remaining fields are propositions. -/
theorem CGraph.ext' {G H : CGraph} (hV : G.V = H.V) (hA : HEq G.Adj H.Adj) : G = H := by
  obtain ⟨V₁, A₁, s₁, l₁⟩ := G
  obtain ⟨V₂, A₂, s₂, l₂⟩ := H
  simp only at hV hA
  subst hV
  cases hA
  congr 1
  exact Subsingleton.elim _ _

/-! ## `CGraph` is equivalent to `SimpleGraph` -/

/-- The `SimpleGraph` underlying a `CGraph`. -/
def CGraph.toSimple (G : CGraph) : SimpleGraph G.V where
  Adj x y := G.Adj x y
  symm := by intro x y h; show G.Adj y x = true; rw [← G.symm x y]; exact h
  loopless := ⟨fun x h => G.loopless x h⟩

@[simp] theorem CGraph.toSimple_adj (G : CGraph) (x y : G.V) :
    G.toSimple.Adj x y ↔ G.Adj x y = true := Iff.rfl

instance (G : CGraph) : DecidableRel G.toSimple.Adj :=
  fun x y => decidable_of_iff (G.Adj x y = true) Iff.rfl

/-- A decidable `SimpleGraph` as a `CGraph`. -/
def SimpleGraph.toCGraph {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    CGraph where
  V := V
  Adj x y := decide (G.Adj x y)
  symm x y := by simp [G.adj_comm]
  loopless x := by simp

noncomputable def CGraph.simpleEquiv : CGraph ≃ Σ V, Fintype V × SimpleGraph V where
  toFun G := ⟨G.V, inferInstance, G.toSimple⟩
  invFun := fun ⟨V, _, G⟩ ↦ open Classical in G.toCGraph
  left_inv G := by
    refine CGraph.ext' rfl (heq_of_eq ?_)
    funext x y
    simp [SimpleGraph.toCGraph, CGraph.toSimple]
  right_inv := by
    rintro ⟨V, inst, G⟩
    have hG : (open Classical in G.toCGraph).toSimple = G := by
      ext x y
      simp [SimpleGraph.toCGraph, CGraph.toSimple]
    simp only [hG]
    exact congrArg (fun i : Fintype V ↦ (⟨V, (i, G)⟩ : Σ V, Fintype V × SimpleGraph V))
      (Subsingleton.elim _ _)

namespace CGraph

variable (G H I : CGraph)

/-- A graph homomorphism. -/
abbrev Hom (G H : CGraph) :=
  RelHom (G.Adj · ·) (H.Adj · ·)

/-- A graph embedding. -/
abbrev Embedding (G H : CGraph) :=
  RelEmbedding (G.Adj · ·) (H.Adj · ·)

/-- A graph isomorphism. -/
abbrev Iso (G H : CGraph) :=
  RelIso (G.Adj · ·) (H.Adj · ·)

@[inherit_doc] infixl:50 " →cg " => Hom
@[inherit_doc] infixl:50 " ↪cg " => Embedding
@[inherit_doc] infixl:50 " ≃cg " => Iso

theorem hom_eq : (G →cg H) = (G.toSimple →g H.toSimple) := by
  rfl

theorem embedding_eq : (G ↪cg H) = (G.toSimple ↪g H.toSimple) := by
  rfl

theorem iso_eq : (G ≃cg H) = (G.toSimple ≃g H.toSimple) := by
  rfl

/-- A `CGraph` isomorphism *is* an isomorphism of the underlying `SimpleGraph`s (`iso_eq` is
`rfl`); this is the coercion that lets Mathlib's graph API be used directly. -/
def Iso.toSimpleIso {G H : CGraph} (i : G ≃cg H) : G.toSimple ≃g H.toSimple := i

theorem Iso.card_eq (i : G ≃cg H) : Fintype.card G.V = Fintype.card H.V := by
  convert Fintype.ofEquiv_card i.toEquiv.symm

/-- An isomorphism transports adjacency, as `Bool`s. -/
theorem Iso.adj_eq {G H : CGraph} (i : G ≃cg H) (x y : G.V) : H.Adj (i x) (i y) = G.Adj x y :=
  Bool.eq_iff_iff.2 i.map_rel_iff

example (f : G ≃cg H) (g : H ≃cg I) : G ≃cg I := f.trans g

instance isoSetoid : Setoid CGraph where
  r G H := Nonempty (G ≃cg H)
  iseqv := by
    refine ⟨fun _ ↦ ⟨RelIso.refl _⟩, ?_, ?_⟩
    · rintro _ _ ⟨i⟩
      exact ⟨i.symm⟩
    · rintro _ _ _ ⟨i⟩ ⟨j⟩
      exact ⟨i.trans j⟩

end CGraph

/-- A graph, up to isomorphism. -/
def IsoGraph :=
  Quotient CGraph.isoSetoid

/-- Number of vertices of an `IsoGraph`. -/
def IsoGraph.V (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ Fintype.card g.V) (fun _ _ ⟨i⟩ ↦ CGraph.Iso.card_eq _ _ i) G

/-! ## The canonical labelling

The algorithm of `IsoGraph.Canonical` works on `{0, …, n-1}`; `IsoGraph.Spec` packages it as a
permutation of `Fin n`, and here we transport that along an arbitrary enumeration of an abstract
vertex type. -/

namespace CGraph

/-- An arbitrary enumeration of the vertices.  Which one is chosen does not matter — that is the
content of `CGraph.Iso.canonicalLabelling_eq`. -/
noncomputable def enum (G : CGraph) : G.V ≃ Fin (Fintype.card G.V) :=
  Fintype.equivFin G.V

/-- The adjacency of `G` transported to `Fin (Fintype.card G.V)` along `G.enum`. -/
noncomputable def adjFin (G : CGraph) :
    Fin (Fintype.card G.V) → Fin (Fintype.card G.V) → Bool :=
  fun a b ↦ G.Adj (G.enum.symm a) (G.enum.symm b)

/-- Efficient canonical labelling of a `CGraph`.

Computable in the vertex type `Fin n` (see `IsoGraph.Canon.canonPerm`); for an abstract vertex
type it is noncomputable only because choosing an enumeration `G.V ≃ Fin (card G.V)` is. -/
noncomputable def canonicalLabelling (G : CGraph) : Fin (Fintype.card G.V) ≃ G.V :=
  (IsoGraph.Canon.canonPerm _ G.adjFin).trans G.enum.symm

/-- Reading `G`'s adjacency through its canonical labelling gives exactly the canonical form
computed by the algorithm. -/
theorem adj_canonicalLabelling (G : CGraph) (x y : Fin (Fintype.card G.V)) :
    G.Adj (G.canonicalLabelling x) (G.canonicalLabelling y) =
      IsoGraph.Canon.canonAdj _ G.adjFin x y := rfl

/-- The bijection of index sets induced by an isomorphism. -/
noncomputable def Iso.finEquiv {G H : CGraph} (i : G ≃cg H) :
    Fin (Fintype.card G.V) ≃ Fin (Fintype.card H.V) :=
  G.enum.symm.trans (i.toEquiv.trans H.enum)

theorem Iso.adjFin_finEquiv {G H : CGraph} (i : G ≃cg H) (a b : Fin (Fintype.card G.V)) :
    H.adjFin ((CGraph.Iso.finEquiv i) a) ((CGraph.Iso.finEquiv i) b) = G.adjFin a b := by
  simp only [adjFin, Iso.finEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    RelIso.coe_fn_toEquiv]
  exact CGraph.Iso.adj_eq i _ _

end CGraph

/-- `HEq` of two adjacency functions on `Fin m` and `Fin n`, from `m = n` and pointwise
agreement. -/
theorem IsoGraph.Canon.heq_adj {m n : ℕ} (h : m = n) {f : Fin m → Fin m → Bool}
    {g : Fin n → Fin n → Bool} (hfg : ∀ x y, f x y = g (h ▸ x) (h ▸ y)) : HEq f g := by
  subst h
  exact heq_of_eq (funext fun x ↦ funext fun y ↦ hfg x y)

/-- The canonical labelling is appropriately invariant under isomorphism: reading either graph
through its own canonical labelling gives the *same* adjacency matrix. -/
theorem CGraph.Iso.canonicalLabelling_eq {G H : CGraph} (i : G ≃cg H)
    (x y : Fin (Fintype.card G.V)) :
    G.Adj (G.canonicalLabelling x) (G.canonicalLabelling y) =
    H.Adj (H.canonicalLabelling (CGraph.Iso.card_eq G H i ▸ x))
      (H.canonicalLabelling (CGraph.Iso.card_eq G H i ▸ y)) := by
  rw [CGraph.adj_canonicalLabelling, CGraph.adj_canonicalLabelling]
  exact IsoGraph.Canon.canonAdj_congr (CGraph.Iso.card_eq G H i) (CGraph.Iso.finEquiv i)
    (CGraph.Iso.adjFin_finEquiv i) x y

/-! ## A canonical representative, and the quotient -/

namespace CGraph

/-- The canonical representative of the isomorphism class of `G`: the same graph, relabelled onto
`Fin (Fintype.card G.V)` so that its adjacency matrix is the canonical one. -/
noncomputable def canonicalize (G : CGraph) : CGraph where
  V := Fin (Fintype.card G.V)
  Adj := IsoGraph.Canon.canonAdj _ G.adjFin
  symm x y := IsoGraph.Canon.canonAdj_comm (fun _ _ ↦ G.symm _ _) x y
  loopless x := IsoGraph.Canon.canonAdj_irrefl (fun _ ↦ G.loopless _) x

/-- Isomorphic graphs have *equal* canonical representatives.  This is what makes `IsoGraph`
usable: it turns the isomorphism relation into equality. -/
theorem canonicalize_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.canonicalize = H.canonicalize := by
  refine CGraph.ext' (show Fin (Fintype.card G.V) = Fin (Fintype.card H.V) by
    rw [CGraph.Iso.card_eq G H i]) ?_
  refine IsoGraph.Canon.heq_adj (CGraph.Iso.card_eq G H i) ?_
  exact IsoGraph.Canon.canonAdj_congr (CGraph.Iso.card_eq G H i) (CGraph.Iso.finEquiv i) (CGraph.Iso.adjFin_finEquiv i)

/-- The canonical representative really is isomorphic to the original graph. -/
noncomputable def isoCanonicalize (G : CGraph) : G ≃cg G.canonicalize where
  toEquiv := G.canonicalLabelling.symm
  map_rel_iff' := by
    intro a b
    show (G.Adj (G.canonicalLabelling (G.canonicalLabelling.symm a))
        (G.canonicalLabelling (G.canonicalLabelling.symm b)) = true) ↔ (G.Adj a b = true)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end CGraph

/-- A canonical path out of the quotient type. -/
noncomputable def IsoGraph.toCGraph (G : IsoGraph) : CGraph :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.canonicalize (fun _ _ ⟨i⟩ ↦ CGraph.canonicalize_eq_of_iso i) G

@[simp] theorem IsoGraph.toCGraph_mk (G : CGraph) :
    IsoGraph.toCGraph (Quotient.mk _ G) = G.canonicalize := rfl

/-- `IsoGraph.toCGraph` is a section of the quotient map: it picks a representative of the class.
Together with `Quotient.sound` this gives an *efficient* `DecidableEq` for `IsoGraph`, by
comparing canonical forms. -/
theorem IsoGraph.mk_toCGraph (G : IsoGraph) : Quotient.mk _ G.toCGraph = G := by
  induction G using Quotient.inductionOn with
  | h g => exact Quotient.sound ⟨g.isoCanonicalize.symm⟩

/-! ## Invariants of an `IsoGraph`

Each of these is a `Quotient.lift` of a graph invariant; the side condition is that the invariant
is unchanged by isomorphism. -/

namespace SimpleGraph.Iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- The image of an `n`-clique under an isomorphism is an `n`-clique. -/
theorem isNClique_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNClique n s) :
    G'.IsNClique n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact f.map_adj_iff.2 (h.1 hx hy fun e ↦ hab (by rw [e]))

/-- The image of an independent `n`-set under an isomorphism is an independent `n`-set. -/
theorem isNIndepSet_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNIndepSet n s) :
    G'.IsNIndepSet n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact fun hadj ↦ h.1 hx hy (fun e ↦ hab (by rw [e])) (f.map_adj_iff.1 hadj)

theorem cliqueNum_eq (f : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f.symm hs⟩⟩

theorem indepNum_eq (f : G ≃g G') : G.indepNum = G'.indepNum := by
  unfold SimpleGraph.indepNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f.symm hs⟩⟩

/-- Isomorphic graphs have the same multiset of degrees. -/
theorem degrees_eq [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]
    (f : G ≃g G') :
    (Finset.univ.val.map fun v ↦ G.degree v) = Finset.univ.val.map fun w ↦ G'.degree w := by
  conv_rhs => rw [← Finset.map_univ_equiv f.toEquiv]
  rw [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun v _ ↦ ?_
  exact (f.degree_eq v).symm

end SimpleGraph.Iso

namespace IsoGraph

variable (G : IsoGraph)

/-- Independence number. -/
noncomputable def indepNum : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ g.toSimple.indepNum)
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.indepNum_eq (CGraph.Iso.toSimpleIso i)) G

/-- Clique number. -/
noncomputable def cliqueNum : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ g.toSimple.cliqueNum)
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.cliqueNum_eq (CGraph.Iso.toSimpleIso i)) G

/-- Number of edges of an `IsoGraph`. -/
def E : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ g.toSimple.edgeFinset.card)
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.card_edgeFinset_eq (CGraph.Iso.toSimpleIso i)) G

/-- Sorted degree sequence of an `IsoGraph`. -/
def degSequence : List ℕ :=
  Quotient.lift (s := CGraph.isoSetoid)
    (fun g ↦ (Finset.univ.val.map fun v ↦ g.toSimple.degree v).sort (· ≤ ·))
    (fun _ _ ⟨i⟩ ↦ congrArg (fun m : Multiset ℕ ↦ m.sort (· ≤ ·))
      (SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i))) G

-- connected : Bool, acyclic : Bool, diameter : ℕ, etc. — all aiming for fast computation.

end IsoGraph

-- Then we can define various ways to build them:
-- IsoGraph.complete (n : ℕ), IsoGraph.path (n : ℕ), IsoGraph.thetaGraph (xs : List ℕ),
-- IsoGraph.cycle (n : ℕ), disjoint union, complement, join, strong product, cartesian product,
-- tensor product, lexicographical product, kneser graph, bipartite graph (m n : ℕ),
-- k-partite graph (ds : List ℕ), line graph, mycielskian.
