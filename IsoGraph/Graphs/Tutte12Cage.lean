import IsoGraph.Invariants.Certificates
import IsoGraph.Graphs.SRG

/-!
# The Tutte 12-cage

The unique `(3, 12)`-cage, on a hundred and twenty-six vertices, also called the Benson graph: the
incidence graph of the generalized hexagon `GH(2, 2)`, and the largest cubic cage with a name.

It has a module of its own because its girth is, with the Balaban 11-cage, one of the two most
expensive checks in the library: ruling out every cycle shorter than twelve walks `126 · 3 · 2¹⁰`
closed walks through the neighbour table.  In its own module the check runs in parallel with the
rest of the gallery instead of in series with it.

The graph is given by its LCF code, spelled out as `ofEdges 126 (lcfEdges tutte12CageCode 7)`
rather than as `lcf tutte12CageCode 7` so that the vertex type is literally `Fin 126`; the two are
the same graph.
-/

set_option maxRecDepth 4000

namespace NamedGraphs

open CGraph CGraph.Enum

/-- The LCF code of the Tutte 12-cage. -/
def tutte12CageCode : List ℤ :=
  [17, 27, -13, -59, -35, 35, -11, 13, -53, 53, -27, 21, 57, 11, -21, -57, 59, -17]

/-- The Tutte 12-cage, also called the Benson graph: the unique `(3, 12)`-cage, and the incidence
graph of the generalized hexagon `GH(2, 2)`. -/
abbrev tutte12Cage : CGraph := ofEdges 126 (lcfEdges tutte12CageCode 7)

@[simp] theorem card_tutte12Cage : Fintype.card tutte12Cage.V = 126 := card_ofEdges _ _

@[simp] theorem E_tutte12Cage : tutte12Cage.E = 189 := by native_decide

theorem isRegularWith_tutte12Cage : tutte12Cage.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 126) (by native_decide)

@[simp] theorem isConnected_tutte12Cage : tutte12Cage.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 126)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_tutte12Cage : tutte12Cage.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Tutte 12-cage. -/
def tutte12CageTbl : List (List tutte12Cage.V) := tutte12Cage.nbrTable (List.finRange 126)

/-- The neighbours of `a` in the Tutte 12-cage. -/
def tutte12CageNb (a : tutte12Cage.V) : List tutte12Cage.V := tutte12CageTbl.getD a.1 []

theorem tutte12Cage_nb : ∀ a b : tutte12Cage.V, b ∈ tutte12CageNb a ↔ tutte12Cage.Adj a b := by
  native_decide

set_option maxHeartbeats 4000000 in
/-- The Tutte 12-cage has girth twelve. -/
@[simp] theorem girth_tutte12Cage : tutte12Cage.girth = 12 := by
  have hcyc : tutte12Cage.girth ≤ 12 :=
    girth_le_of_cycleList
      (vtx 126 0) [vtx 126 17, vtx 126 16, vtx 126 15, vtx 126 14, vtx 126 13, vtx 126 12,
        vtx 126 69, vtx 126 70, vtx 126 3, vtx 126 2, vtx 126 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ tutte12Cage.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 126 0) [vtx 126 17, vtx 126 16, vtx 126 15, vtx 126 14, vtx 126 13, vtx 126 12,
        vtx 126 69, vtx 126 70, vtx 126 3, vtx 126 2, vtx 126 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (twelve_le_girth_of_nbrList tutte12Cage_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

end NamedGraphs
