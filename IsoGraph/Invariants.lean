import IsoGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-!
# Invariants

An *invariant* here is a quantity attached to a `CGraph` that is unchanged by isomorphism, and so
descends to `IsoGraph`.  Each one appears twice:

* at the `CGraph` level, as a thin wrapper around the corresponding Mathlib notion for
  `G.toSimple` — this is the form statements about concrete graphs are proved in;
* at the `IsoGraph` level, as a `Quotient.lift` of it, whose side condition is exactly
  isomorphism-invariance.

The `SimpleGraph.Iso` section below supplies the invariance lemmas that Mathlib does not already
have.
-/

open Fintype

/-! ## Isomorphism-invariance lemmas for `SimpleGraph` -/

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

/-- Pushing a walk forward along an isomorphism can only shorten the extended distance; applying
this to `f` and to `f.symm` gives `edist_eq`. -/
private theorem edist_le_of_iso (f : G ≃g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  rw [SimpleGraph.edist_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨w, rfl⟩
  simpa using SimpleGraph.edist_le (w.map f.toHom)

/-- Isomorphisms preserve the extended distance. -/
theorem edist_eq (f : G ≃g G') (u v : V) : G.edist u v = G'.edist (f u) (f v) :=
  le_antisymm (by simpa using edist_le_of_iso f.symm (f u) (f v)) (edist_le_of_iso f u v)

/-- Isomorphic graphs have the same extended diameter. -/
theorem ediam_eq (f : G ≃g G') : G.ediam = G'.ediam := by
  refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
    (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
  · rw [edist_eq f]; exact SimpleGraph.edist_le_ediam
  · rw [edist_eq f.symm]; exact SimpleGraph.edist_le_ediam

/-- Isomorphic graphs have the same diameter. -/
theorem diam_eq (f : G ≃g G') : G.diam = G'.diam :=
  congrArg ENat.toNat (ediam_eq f)

end SimpleGraph.Iso

/-! ## Invariants of a `CGraph` -/

namespace CGraph

variable (G : CGraph)

/-- Independence number: the size of a largest set of pairwise non-adjacent vertices. -/
noncomputable def indepNum : ℕ := G.toSimple.indepNum

/-- Clique number: the size of a largest set of pairwise adjacent vertices. -/
noncomputable def cliqueNum : ℕ := G.toSimple.cliqueNum

/-- Number of edges. -/
def E : ℕ := G.toSimple.edgeFinset.card

/-- Sorted degree sequence. -/
def degSequence : List ℕ := (Finset.univ.val.map fun v ↦ G.toSimple.degree v).sort (· ≤ ·)

/-- The graph is connected (in particular, nonempty). -/
def IsConnected : Prop := G.toSimple.Connected

/-- The graph has no cycles. -/
def IsAcyclic : Prop := G.toSimple.IsAcyclic

/-- Diameter, i.e. the largest distance between two vertices — `0` if the graph is disconnected
(this is Mathlib's convention for `SimpleGraph.diam`). -/
noncomputable def diameter : ℕ := G.toSimple.diam

/-- The graph is a tree. -/
def IsTree : Prop := G.toSimple.IsTree

/-! Both `IsConnected` and `IsAcyclic` are decidable — but only once the vertex type has a
`DecidableEq`, which a `Fintype` alone does not give.  Constructions that produce a concrete
vertex type supply it; see `IsoGraph/Constructions.lean`. -/

instance [DecidableEq G.V] : Decidable G.IsConnected :=
  inferInstanceAs (Decidable G.toSimple.Connected)

instance [DecidableEq G.V] : Decidable G.IsAcyclic :=
  decidable_of_iff (∀ (v w : G.V) (p q : G.toSimple.Path v w), p = q)
    SimpleGraph.isAcyclic_iff_path_unique.symm

instance [DecidableEq G.V] : Decidable G.IsTree :=
  decidable_of_iff (G.IsConnected ∧ G.IsAcyclic)
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

end CGraph

/-! ## Invariants of an `IsoGraph`

Each is a `Quotient.lift` of the corresponding `CGraph` invariant; the side condition is exactly
the isomorphism-invariance lemma above. -/

namespace IsoGraph

/-- Independence number. -/
noncomputable def indepNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.indepNum
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.indepNum_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem indepNum_mk (G : CGraph) :
    indepNum (Quotient.mk _ G) = G.indepNum := rfl

/-- Clique number. -/
noncomputable def cliqueNum (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.cliqueNum
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.cliqueNum_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem cliqueNum_mk (G : CGraph) :
    cliqueNum (Quotient.mk _ G) = G.cliqueNum := rfl

/-- Number of edges. -/
def E (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.E
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.card_edgeFinset_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem E_mk (G : CGraph) : E (Quotient.mk _ G) = G.E := rfl

/-- Sorted degree sequence. -/
def degSequence (G : IsoGraph) : List ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.degSequence
    (fun _ _ ⟨i⟩ ↦ congrArg (fun m : Multiset ℕ ↦ m.sort (· ≤ ·))
      (SimpleGraph.Iso.degrees_eq (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem degSequence_mk (G : CGraph) :
    degSequence (Quotient.mk _ G) = G.degSequence := rfl

/-- Connectivity. -/
def IsConnected (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsConnected
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.connected_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isConnected_mk (G : CGraph) :
    IsConnected (Quotient.mk _ G) = G.IsConnected := rfl

/-- Acyclicity. -/
def IsAcyclic (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsAcyclic
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.isAcyclic_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isAcyclic_mk (G : CGraph) :
    IsAcyclic (Quotient.mk _ G) = G.IsAcyclic := rfl

/-- Being a tree. -/
def IsTree (G : IsoGraph) : Prop :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.IsTree
    (fun _ _ ⟨i⟩ ↦ propext (SimpleGraph.Iso.isTree_iff (CGraph.Iso.toSimpleIso i))) G

@[simp] theorem isTree_mk (G : CGraph) : IsTree (Quotient.mk _ G) = G.IsTree := rfl

/-- Diameter. -/
noncomputable def diameter (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.diameter
    (fun _ _ ⟨i⟩ ↦ SimpleGraph.Iso.diam_eq (CGraph.Iso.toSimpleIso i)) G

@[simp] theorem diameter_mk (G : CGraph) : diameter (Quotient.mk _ G) = G.diameter := rfl

end IsoGraph
