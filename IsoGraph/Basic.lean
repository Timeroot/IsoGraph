import Mathlib
import IsoGraph.Canonical

/-!
# Graphs up to isomorphism

This file follows `isograph_draft.txt`: a bundled, computable graph type `CGraph`, its
isomorphisms, and the quotient `IsoGraph` of graphs up to isomorphism.

The bridge to the canonical labelling algorithm of `IsoGraph.Canonical` lives in the
`IsoGraph.Canon` section below.  The algorithm returns a raw `Array Nat`; `permOfArrays` turns it
into an honest `Equiv.Perm (Fin n)` by *checking at run time* that it really is a permutation and
falling back to the identity otherwise.  That keeps the `Equiv` total and proof-free, and isolates
the one genuinely deep obligation — that the canonical form is an isomorphism invariant — in
`CGraph.Iso.canonicalLabelling_eq`.
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

/-! ## `CGraph` is equivalent to `SimpleGraph` -/

/-- The `SimpleGraph` underlying a `CGraph`. -/
def CGraph.toSimple (G : CGraph) : SimpleGraph G.V where
  Adj x y := G.Adj x y
  symm := by intro x y h; show G.Adj y x = true; rw [← G.symm x y]; exact h
  loopless := ⟨fun x h => G.loopless x h⟩

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
  left_inv := sorry
  right_inv := sorry

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

theorem Iso.card_eq (i : G ≃cg H) : Fintype.card G.V = Fintype.card H.V := by
  convert Fintype.ofEquiv_card i.toEquiv.symm

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
  Quotient.lift (fun g ↦ Fintype.card g.V) (fun _ _ ⟨i⟩ ↦ CGraph.Iso.card_eq _ _ i) G

/-! ## The canonical labelling

The algorithm of `IsoGraph.Canonical` works on `{0, …, n-1}`; here we wrap it as a permutation of
`Fin n` and then transport it along an arbitrary enumeration of an abstract vertex type. -/

namespace IsoGraph.Canon

/-- Read an array of naturals as a function `Fin n → Fin n`, sending out-of-range entries to
themselves. -/
def finFn (n : Nat) (a : Array Nat) (i : Fin n) : Fin n :=
  if h : a[i.1]! < n then ⟨a[i.1]!, h⟩ else i

/-- Build a permutation of `Fin n` out of an array and its claimed inverse.

The two arrays are *checked* (in `O(n)`) to be mutually inverse, and the identity is returned if
they are not.  So this is total and needs no facts about the algorithm that produced them; the
fallback is unreachable in practice. -/
def permOfArrays (n : Nat) (a b : Array Nat) : Equiv.Perm (Fin n) :=
  if h : (∀ i, finFn n b (finFn n a i) = i) ∧ (∀ i, finFn n a (finFn n b i) = i) then
    { toFun := finFn n a, invFun := finFn n b, left_inv := h.1, right_inv := h.2 }
  else Equiv.refl _

/-- The inverse of an array-encoded permutation of `{0, …, n-1}`. -/
def invArray (n : Nat) (a : Array Nat) : Array Nat := Id.run do
  let mut b := Array.replicate n 0
  for i in [0:n] do
    if a[i]! < n then b := b.set! a[i]! i
  return b

/-- Adjacency oracle on `{0, …, n-1}` coming from an adjacency function on `Fin n`. -/
def oracleOfFin (n : Nat) (adj : Fin n → Fin n → Bool) (v w : Nat) : Bool :=
  if hv : v < n then if hw : w < n then adj ⟨v, hv⟩ ⟨w, hw⟩ else false else false

/-- The canonical labelling of a graph on `Fin n`: canonical position `i` holds the vertex
`canonPerm n adj i`. -/
def canonPerm (n : Nat) (adj : Fin n → Fin n → Bool) : Equiv.Perm (Fin n) :=
  let lab := canonicalLabellingOfOracle n (oracleOfFin n adj)
  permOfArrays n lab (invArray n lab)

/-- The canonical adjacency function of a graph on `Fin n`: the graph relabelled so that its
adjacency matrix is the canonical one. -/
def canonAdj (n : Nat) (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j ↦ adj (canonPerm n adj i) (canonPerm n adj j)

end IsoGraph.Canon

/-- Efficient canonical labelling of a `CGraph`.

Computable in the vertex type `Fin n` (see `IsoGraph.Canon.canonPerm`); for an abstract vertex
type it is noncomputable only because choosing an enumeration `G.V ≃ Fin (card G.V)` is.  The
choice does not matter: that is exactly the content of `CGraph.Iso.canonicalLabelling_eq`. -/
noncomputable def CGraph.canonicalLabelling (G : CGraph) : Fin (Fintype.card G.V) ≃ G.V :=
  let e : G.V ≃ Fin (Fintype.card G.V) := Fintype.equivFin G.V
  (IsoGraph.Canon.canonPerm _ fun i j ↦ G.Adj (e.symm i) (e.symm j)).trans e.symm

/-- The canonical labelling is appropriately invariant under isomorphism. -/
theorem CGraph.Iso.canonicalLabelling_eq {G H : CGraph} (i : G ≃cg H)
    (x y : Fin (Fintype.card G.V)) :
    G.Adj (G.canonicalLabelling x) (G.canonicalLabelling y) =
    H.Adj (H.canonicalLabelling (CGraph.Iso.card_eq G H i ▸ x))
      (H.canonicalLabelling (CGraph.Iso.card_eq G H i ▸ y)) := by
  sorry

-- We can use this to construct a function `canonicalize : CGraph → CGraph` so that `G ≃cg H`
-- implies `G.canonicalize = H.canonicalize`, and then lift to the quotient type.

/-- A canonical path out of the quotient type. -/
def IsoGraph.toCGraph (G : IsoGraph) : CGraph :=
  Quotient.lift sorry sorry G

-- An *efficient* `DecidableEq` for `IsoGraph` then follows from comparing canonical forms.

namespace IsoGraph

variable (G : IsoGraph)

--TODO: make computable.
noncomputable def indepNum : ℕ :=
  Quotient.lift (fun g ↦ g.toSimple.indepNum) sorry G

--TODO: make computable.
noncomputable def cliqueNum : ℕ :=
  Quotient.lift (fun g ↦ g.toSimple.cliqueNum) sorry G

/-- Number of edges of an `IsoGraph`. -/
def E : ℕ :=
  Quotient.lift (fun g ↦ (Finset.univ.filter fun p : g.V × g.V ↦ g.Adj p.1 p.2).card / 2)
    sorry G

/-- Sorted degree sequence of an `IsoGraph`. -/
def degSequence : List ℕ :=
  Quotient.lift
    (fun g ↦ (Finset.univ.val.map fun v ↦ (Finset.univ.filter fun w ↦ g.Adj v w).card).sort
      (· ≤ ·))
    sorry G

-- connected : Bool, acyclic : Bool, diameter : ℕ, etc. — all aiming for fast computation.

end IsoGraph

-- Then we can define various ways to build them:
-- IsoGraph.complete (n : ℕ), IsoGraph.path (n : ℕ), IsoGraph.thetaGraph (xs : List ℕ),
-- IsoGraph.cycle (n : ℕ), disjoint union, complement, join, strong product, cartesian product,
-- tensor product, lexicographical product, kneser graph, bipartite graph (m n : ℕ),
-- k-partite graph (ds : List ℕ), line graph, mycielskian.
