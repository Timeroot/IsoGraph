import IsoGraph.SmallGraphs.Defs.Solids

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The cages

The cages that are too large to define by hand: their edge lists, and the certificates that pin
down their girth.
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

/-- The LCF code of the Harries graph. -/
def harriesCode : List ℤ :=
  [-29, -19, -13, 13, 21, -27, 27, 33, -13, 13, 19, -21, -33, 29]

/-- The Harries graph: one of the three `(3, 10)`-cages, with automorphism group of order one
hundred and twenty. -/
abbrev harries : CGraph := ofEdges 70 (lcfEdges harriesCode 5)

/-- The LCF code of the Harries–Wong graph. -/
def harriesWongCode : List ℤ :=
  [9, 25, 31, -17, 17, 33, 9, -29, -15, -9, 9, 25, -25, 29, 17, -9, 9, -27, 35, -9, 9, -17, 21, 27,
    -29, -9, -25, 13, 19, -9, -33, -17, 19, -31, 27, 11, -25, 29, -33, 13, -13, 21, -29, -21, 25, 9,
    -11, -19, 29, 9, -27, -19, -13, -35, -9, 9, 17, 25, -9, 9, 27, -27, -21, 15, -9, 29, -29, 33,
    -9, -25]

/-- The Harries–Wong graph: the least symmetric of the three `(3, 10)`-cages, with automorphism
group of order twenty-four. -/
abbrev harriesWong : CGraph := ofEdges 70 (lcfEdges harriesWongCode 1)

/-- The LCF code of the Gray graph. -/
def grayCode : List ℤ :=
  [-25, 7, -7, 13, -13, 25]

/-- The Gray graph: the smallest cubic semi-symmetric graph, edge-transitive and regular but not
vertex-transitive.  It is the incidence graph of the `3 × 3 × 3` grid of points and its
twenty-seven axis-parallel lines. -/
abbrev gray : CGraph := ofEdges 54 (lcfEdges grayCode 9)

/-- The LCF code of the Foster graph. -/
def fosterCode : List ℤ :=
  [17, -9, 37, -37, 9, -17]

/-- The Foster graph: the cubic distance-transitive graph on ninety vertices, the largest of the
twelve. -/
abbrev foster : CGraph := ofEdges 90 (lcfEdges fosterCode 15)

@[simp] theorem card_harries : FinEnum.card harries.V = 70 := card_ofEdges _ _

@[simp] theorem E_harries : harries.E = 105 := by native_decide

theorem isRegularWith_harries : harries.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 70) (by native_decide)

@[simp] theorem isConnected_harries : harries.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 70)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_harries : harries.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Harries graph. -/
def harriesTbl : List (List harries.V) := harries.nbrTable (List.finRange 70)

/-- The neighbours of `a` in the Harries graph. -/
def harriesNb (a : harries.V) : List harries.V := harriesTbl.getD a.1 []

theorem harries_nb : ∀ a b : harries.V, b ∈ harriesNb a ↔ harries.Adj a b := by
  native_decide

/-- The Harries graph has girth ten. -/
@[simp] theorem girth_harries : harries.girth = 10 := by
  obtain ⟨hcyc, hnac⟩ := girth_le_and_not_isAcyclic_of_cycleList harries
    (vtx 70 0) [vtx 70 41, vtx 70 40, vtx 70 7, vtx 70 6, vtx 70 5, vtx 70 4, vtx 70 3, vtx 70 2,
      vtx 70 1]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (le_girth_of_nbrList 10 harries_nb (by native_decide) hnac)

@[simp] theorem card_harriesWong : FinEnum.card harriesWong.V = 70 := card_ofEdges _ _

@[simp] theorem E_harriesWong : harriesWong.E = 105 := by native_decide

theorem isRegularWith_harriesWong : harriesWong.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 70) (by native_decide)

@[simp] theorem isConnected_harriesWong : harriesWong.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 70)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_harriesWong : harriesWong.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Harries–Wong graph. -/
def harriesWongTbl : List (List harriesWong.V) := harriesWong.nbrTable (List.finRange 70)

/-- The neighbours of `a` in the Harries–Wong graph. -/
def harriesWongNb (a : harriesWong.V) : List harriesWong.V := harriesWongTbl.getD a.1 []

theorem harriesWong_nb : ∀ a b : harriesWong.V, b ∈ harriesWongNb a ↔ harriesWong.Adj a b := by
  native_decide

/-- The Harries–Wong graph has girth ten. -/
@[simp] theorem girth_harriesWong : harriesWong.girth = 10 := by
  obtain ⟨hcyc, hnac⟩ := girth_le_and_not_isAcyclic_of_cycleList harriesWong
    (vtx 70 0) [vtx 70 9, vtx 70 8, vtx 70 7, vtx 70 6, vtx 70 5, vtx 70 4, vtx 70 3, vtx 70 2,
      vtx 70 1]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (le_girth_of_nbrList 10 harriesWong_nb (by native_decide) hnac)

@[simp] theorem card_gray : FinEnum.card gray.V = 54 := card_ofEdges _ _

@[simp] theorem E_gray : gray.E = 81 := by native_decide

theorem isRegularWith_gray : gray.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 54) (by native_decide)

@[simp] theorem isConnected_gray : gray.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 54)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_gray : gray.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Gray graph. -/
def grayTbl : List (List gray.V) := gray.nbrTable (List.finRange 54)

/-- The neighbours of `a` in the Gray graph. -/
def grayNb (a : gray.V) : List gray.V := grayTbl.getD a.1 []

theorem gray_nb : ∀ a b : gray.V, b ∈ grayNb a ↔ gray.Adj a b := by
  native_decide

/-- The Gray graph has girth eight. -/
@[simp] theorem girth_gray : gray.girth = 8 := by
  obtain ⟨hcyc, hnac⟩ := girth_le_and_not_isAcyclic_of_cycleList gray
    (vtx 54 0) [vtx 54 29, vtx 54 28, vtx 54 15, vtx 54 14, vtx 54 7, vtx 54 8, vtx 54 1]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (le_girth_of_nbrList 8 gray_nb (by native_decide) hnac)

@[simp] theorem card_foster : FinEnum.card foster.V = 90 := card_ofEdges _ _

@[simp] theorem E_foster : foster.E = 135 := by native_decide

theorem isRegularWith_foster : foster.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 90) (by native_decide)

@[simp] theorem isConnected_foster : foster.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 90)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_foster : foster.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-- The neighbour table of the Foster graph. -/
def fosterTbl : List (List foster.V) := foster.nbrTable (List.finRange 90)

/-- The neighbours of `a` in the Foster graph. -/
def fosterNb (a : foster.V) : List foster.V := fosterTbl.getD a.1 []

theorem foster_nb : ∀ a b : foster.V, b ∈ fosterNb a ↔ foster.Adj a b := by
  native_decide

/-- The Foster graph has girth ten. -/
@[simp] theorem girth_foster : foster.girth = 10 := by
  obtain ⟨hcyc, hnac⟩ := girth_le_and_not_isAcyclic_of_cycleList foster
    (vtx 90 0) [vtx 90 17, vtx 90 16, vtx 90 15, vtx 90 14, vtx 90 13, vtx 90 4, vtx 90 3,
      vtx 90 2, vtx 90 1]
    (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (le_girth_of_nbrList 10 foster_nb (by native_decide) hnac)

end

end NamedGraphs
