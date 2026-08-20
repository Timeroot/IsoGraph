import IsoGraph.SmallGraphs.Defs.Cages

/-!
# The Balaban 11-cage

The Balaban 11-cage: the unique (3, 11)-cage, on 112 vertices.
-/

section
set_option maxRecDepth 4000

-- the girth conditions nest eight bounded quantifiers over `balaban11Cage.V`, and each level costs

-- a `Fintype` and a `DecidableEq` that now come through the graph's `FinEnum`; the default

-- instance-search budget runs out at the sixth

end

namespace NamedGraphs

section
set_option maxRecDepth 4000
set_option synthInstance.maxSize 512
open CGraph CGraph.Enum

/-- The LCF code of the Balaban 11-cage. -/
def balaban11CageCode : List ℤ :=
  [44, 26, -47, -15, 35, -39, 11, -27, 38, -37, 43, 14, 28, 51, -29, -16, 41, -11, -26, 15, 22, -51,
    -35, 36, 52, -14, -33, -26, -46, 52, 26, 16, 43, 33, -15, 17, -53, 23, -42, -35, -28, 30, -22,
    45, -44, 16, -38, -16, 50, -55, 20, 28, -17, -43, 47, 34, -26, -41, 11, -36, -23, -16, 41, 17,
    -51, 26, -33, 47, 17, -11, -20, -30, 21, 29, 36, -43, -52, 10, 39, -28, -17, -52, 51, 26, 37,
    -17, 10, -10, -45, -34, 17, -26, 27, -21, 46, 53, -10, 29, -50, 35, 15, -47, -29, -41, 26, 33,
    55, -17, 42, -26, -36, 16]

/-- The Balaban 11-cage: the unique `(3, 11)`-cage, on a hundred and twelve vertices. -/
abbrev balaban11Cage : CGraph := ofEdges 112 (lcfEdges balaban11CageCode 1)

@[simp] theorem card_balaban11Cage : FinEnum.card balaban11Cage.V = 112 := card_ofEdges _ _

@[simp] theorem E_balaban11Cage : balaban11Cage.E = 168 := by native_decide

theorem isRegularWith_balaban11Cage : balaban11Cage.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 112) (by native_decide)

@[simp] theorem isConnected_balaban11Cage : balaban11Cage.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 112)) (by norm_num) (by native_decide)

/-- The Balaban 11-cage has odd girth, so it is not bipartite. -/
@[simp] theorem not_isBipartite_balaban11Cage : ¬ balaban11Cage.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 112 (by norm_num) [0, 111, 15, 16, 17, 6, 5, 4, 3, 2, 1])
    11 rfl (by decide) rfl

/-- The neighbour table of the Balaban 11-cage. -/
def balaban11CageTbl : List (List balaban11Cage.V) := balaban11Cage.nbrTable (List.finRange 112)

/-- The neighbours of `a` in the Balaban 11-cage. -/
def balaban11CageNb (a : balaban11Cage.V) : List balaban11Cage.V := balaban11CageTbl.getD a.1 []

theorem balaban11Cage_nb :
    ∀ a b : balaban11Cage.V, b ∈ balaban11CageNb a ↔ balaban11Cage.Adj a b := by
  native_decide

set_option maxHeartbeats 4000000 in
/-- The Balaban 11-cage has girth eleven. -/
@[simp] theorem girth_balaban11Cage : balaban11Cage.girth = 11 := by
  have hcyc : balaban11Cage.girth ≤ 11 :=
    girth_le_of_cycleList
      (vtx 112 0) [vtx 112 111, vtx 112 15, vtx 112 16, vtx 112 17, vtx 112 6, vtx 112 5, vtx 112 4,
        vtx 112 3, vtx 112 2, vtx 112 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ balaban11Cage.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 112 0) [vtx 112 111, vtx 112 15, vtx 112 16, vtx 112 17, vtx 112 6, vtx 112 5, vtx 112 4,
        vtx 112 3, vtx 112 2, vtx 112 1]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (eleven_le_girth_of_nbrList balaban11Cage_nb
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
