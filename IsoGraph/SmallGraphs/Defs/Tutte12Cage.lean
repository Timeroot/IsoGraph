import IsoGraph.SmallGraphs.Defs.Balaban11Cage

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The Tutte 12-cage

The Tutte 12-cage: the unique (3, 12)-cage, on 126 vertices.
-/

section
set_option maxRecDepth 4000

-- the girth conditions nest bounded quantifiers over the graph's vertex type, and each level costs

-- a `Fintype` and a `DecidableEq` that now come through the graph's `FinEnum`; the default

-- instance-search budget runs out around the sixth

end

namespace NamedGraphs

section
set_option maxRecDepth 4000
set_option synthInstance.maxSize 512
open CGraph CGraph.Enum

/-- The LCF code of the Tutte 12-cage. -/
def tutte12CageCode : List ℤ :=
  [17, 27, -13, -59, -35, 35, -11, 13, -53, 53, -27, 21, 57, 11, -21, -57, 59, -17]

/-- The Tutte 12-cage, also called the Benson graph: the unique `(3, 12)`-cage, and the incidence
graph of the generalized hexagon `GH(2, 2)`. -/
abbrev tutte12Cage : CGraph := ofEdges 126 (lcfEdges tutte12CageCode 7)

@[simp] theorem card_tutte12Cage : FinEnum.card tutte12Cage.V = 126 := card_ofEdges _ _

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

-- Measured: 538 889 heartbeats.  The fifteen `native_decide` searches are free; the cost is the
-- elaborator's, in stating and typechecking the nine hypotheses of `twelve_le_girth_of_nbrList`
-- over a 126-vertex neighbour table.
set_option maxHeartbeats 1600000 in
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

end

end NamedGraphs
