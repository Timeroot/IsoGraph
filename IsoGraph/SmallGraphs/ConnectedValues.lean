import IsoGraph.SmallGraphs.Operators

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The connected graphs on at most six vertices: the four co-NP invariants

`SmallGraphs.Defs.Small` names every connected graph on at most six vertices; this file says what
`α`, `ω`, `χ` and `χ'` come to on each of them.  A few of the values are already simp lemmas about
the families the graph is an alias for — `α(K₆)` is `indepNum_complete` — and those are not
repeated here.

The proofs are the two-sided pattern of `SmallGraphs.SatValues`, but the graphs are small enough
that everything except the refutations is `decide`:

* the witness — an independent set, a clique, a colouring, an edge colouring — is a table checked
  by `le_indepNum_of_nodup`, `le_cliqueNum_of_nodup`, `chromNum_le_of_colouring` and
  `edgeChromNum_mk_le_of_colouring`;
* the refutation goes to `graph_sat`, and mostly does not have to: `χ ≥ ω` by
  `cliqueNum_le_chromNum` settles the lower bound for every graph here but four, and `χ' ≥ Δ` by
  `maxDeg_le_edgeChromNum` settles it for every graph here but eight.

The four that need a colour more than their largest clique are `C₅`, the 5-tadpole, `θ(2, 2, 3)`
and the 5-wheel; the eight of class two are `K₃`, `C₅`, `K₅`, `K₅` less an edge, `K₂,₃` plus an
edge, and the complements of the cross, the fish and `K₂ ⊕ claw`.
-/

namespace SmallGraphs

open CGraph

set_option maxRecDepth 10000

/-! ## One vertex -/

/-! ## Two vertices -/

/-- A proper one-edge-colouring of `K2`, as a symmetric table on the vertices. -/
def K2EdgeCol : K2.V → K2.V → Fin 1 :=
  ![![0, 0], ![0, 0]]

/-- **The edge chromatic number of `K2` is one.** -/
@[simp] theorem edgeChromNum_K2 : K2.edgeChromNum = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K2)
      K2EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K2
    rwa [show K2.maxDeg = 1 from by decide] at h

/-! ## Three vertices -/

/-- **The independence number of `P3` is two.** -/
@[simp] theorem indepNum_P3 : P3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := P3)
    (l := ([0, 2] : List (Fin 3)))
    (by decide) (by decide)

/-- **The clique number of `P3` is two.** -/
@[simp] theorem cliqueNum_P3 : P3.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := P3)
    (l := ([0, 1] : List (Fin 3)))
    (by decide) (by decide)

/-- A proper two-edge-colouring of `P3`, as a symmetric table on the vertices. -/
def P3EdgeCol : P3.V → P3.V → Fin 2 :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]

/-- **The edge chromatic number of `P3` is two.** -/
@[simp] theorem edgeChromNum_P3 : P3.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := P3)
      P3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum P3
    rwa [show P3.maxDeg = 2 from by decide] at h

/-- A proper three-edge-colouring of `K3`, as a symmetric table on the vertices. -/
def K3EdgeCol : K3.V → K3.V → Fin 3 :=
  ![![0, 0, 1], ![0, 0, 2], ![1, 2, 0]]

/-- **The edge chromatic number of `K3` is three.** -/
@[simp] theorem edgeChromNum_K3 : K3.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K3)
      K3EdgeCol (by decide) (by decide)
  · have h : 2 < K3.edgeChromNum := by graph_sat
    omega

/-! ## Four vertices -/

/-- **The clique number of `C4` is two.** -/
@[simp] theorem cliqueNum_C4 : C4.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := C4)
    (l := ([0, 1] : List (Fin 4)))
    (by decide) (by decide)

/-- A proper two-colouring of `C4`. -/
def C4Col : C4.V → Fin 2 :=
  ![0, 1, 0, 1]

/-- **The chromatic number of `C4` is two.** -/
@[simp] theorem chromNum_C4 : C4.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring C4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum C4
  rwa [cliqueNum_C4] at h

/-- A proper two-edge-colouring of `C4`, as a symmetric table on the vertices. -/
def C4EdgeCol : C4.V → C4.V → Fin 2 :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]

/-- **The edge chromatic number of `C4` is two.** -/
@[simp] theorem edgeChromNum_C4 : C4.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := C4)
      C4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum C4
    rwa [show C4.maxDeg = 2 from by decide] at h

/-- **The independence number of `P4` is two.** -/
@[simp] theorem indepNum_P4 : P4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := P4)
    (l := ([0, 2] : List (Fin 4)))
    (by decide) (by decide)

/-- **The clique number of `P4` is two.** -/
@[simp] theorem cliqueNum_P4 : P4.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := P4)
    (l := ([0, 1] : List (Fin 4)))
    (by decide) (by decide)

/-- A proper two-edge-colouring of `P4`, as a symmetric table on the vertices. -/
def P4EdgeCol : P4.V → P4.V → Fin 2 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]]

/-- **The edge chromatic number of `P4` is two.** -/
@[simp] theorem edgeChromNum_P4 : P4.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := P4)
      P4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum P4
    rwa [show P4.maxDeg = 2 from by decide] at h

/-- **The independence number of `K1_3` is three.** -/
@[simp] theorem indepNum_K1_3 : K1_3.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K1_3)
    (l := ([1, 2, 3] : List (Fin 4)).map (FinEnum.equiv (α := K1_3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K1_3` is two.** -/
@[simp] theorem cliqueNum_K1_3 : K1_3.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_3)
    (l := ([0, 1] : List (Fin 4)).map (FinEnum.equiv (α := K1_3.V)).symm)
    (by decide) (by decide)

/-- A proper two-colouring of `K1_3`. -/
def K1_3Col : K1_3.V → Fin 2 := fun v =>
  ![0, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K1_3` is two.** -/
@[simp] theorem chromNum_K1_3 : K1_3.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K1_3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_3
  rwa [cliqueNum_K1_3] at h

/-- A proper three-edge-colouring of `K1_3`, as a symmetric table on the vertices. -/
def K1_3EdgeCol : K1_3.V → K1_3.V → Fin 3 := fun x y =>
  ![![0, 0, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_3` is three.** -/
@[simp] theorem edgeChromNum_K1_3 : K1_3.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_3)
      K1_3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_3
    rwa [show K1_3.maxDeg = 3 from by decide] at h

/-- `claw` is another name for `K1_3`, so it has the same four values; the simp lemmas are the
ones about `K1_3`. -/
theorem indepNum_claw : claw.indepNum = 3 := indepNum_K1_3
theorem cliqueNum_claw : claw.cliqueNum = 2 := cliqueNum_K1_3
theorem chromNum_claw : claw.chromNum = 2 := chromNum_K1_3
theorem edgeChromNum_claw : claw.edgeChromNum = 3 := edgeChromNum_K1_3

/-- **The independence number of `paw` is two.** -/
@[simp] theorem indepNum_paw : paw.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := paw)
    (l := ([1, 3] : List (Fin 4)).map (FinEnum.equiv (α := paw.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `paw` is three.** -/
@[simp] theorem cliqueNum_paw : paw.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := paw)
    (l := ([0, 1, 2] : List (Fin 4)).map (FinEnum.equiv (α := paw.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `paw`. -/
def pawCol : paw.V → Fin 3 := fun v =>
  ![0, 1, 2, 1] (FinEnum.equiv v)

/-- **The chromatic number of `paw` is three.** -/
@[simp] theorem chromNum_paw : paw.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring pawCol (by decide)) ?_
  have h := cliqueNum_le_chromNum paw
  rwa [cliqueNum_paw] at h

/-- A proper three-edge-colouring of `paw`, as a symmetric table on the vertices. -/
def pawEdgeCol : paw.V → paw.V → Fin 3 := fun x y =>
  ![![0, 0, 1, 2], ![0, 0, 2, 0], ![1, 2, 0, 0], ![2, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `paw` is three.** -/
@[simp] theorem edgeChromNum_paw : paw.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := paw)
      pawEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum paw
    rwa [show paw.maxDeg = 3 from by decide] at h

/-- **The independence number of `diamond` is two.** -/
@[simp] theorem indepNum_diamond : diamond.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamond)
    (l := ([2, 3] : List (Fin 4)).map (FinEnum.equiv (α := diamond.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `diamond` is three.** -/
@[simp] theorem cliqueNum_diamond : diamond.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamond)
    (l := ([0, 1, 2] : List (Fin 4)).map (FinEnum.equiv (α := diamond.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `diamond`. -/
def diamondCol : diamond.V → Fin 3 := fun v =>
  ![0, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `diamond` is three.** -/
@[simp] theorem chromNum_diamond : diamond.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamond
  rwa [cliqueNum_diamond] at h

/-- A proper three-edge-colouring of `diamond`, as a symmetric table on the vertices. -/
def diamondEdgeCol : diamond.V → diamond.V → Fin 3 := fun x y =>
  ![![0, 0, 1, 2], ![0, 0, 2, 1], ![1, 2, 0, 0], ![2, 1, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `diamond` is three.** -/
@[simp] theorem edgeChromNum_diamond : diamond.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamond)
      diamondEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamond
    rwa [show diamond.maxDeg = 3 from by decide] at h

/-- A proper three-edge-colouring of `K4`, as a symmetric table on the vertices. -/
def K4EdgeCol : K4.V → K4.V → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 0, 2, 1], ![1, 2, 0, 0], ![2, 1, 0, 0]]

/-- **The edge chromatic number of `K4` is three.** -/
@[simp] theorem edgeChromNum_K4 : K4.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K4)
      K4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K4
    rwa [show K4.maxDeg = 3 from by decide] at h

/-! ## Five vertices -/

/-- **The clique number of `C5` is two.** -/
@[simp] theorem cliqueNum_C5 : C5.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := C5)
    (l := ([0, 1] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `C5`. -/
def C5Col : C5.V → Fin 3 :=
  ![0, 1, 0, 1, 2]

/-- **The chromatic number of `C5` is three.** -/
@[simp] theorem chromNum_C5 : C5.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring C5Col (by decide)) ?_
  have h : 2 < C5.chromNum := by graph_sat
  omega

/-- A proper three-edge-colouring of `C5`, as a symmetric table on the vertices. -/
def C5EdgeCol : C5.V → C5.V → Fin 3 :=
  ![![0, 0, 0, 0, 1], ![0, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 2], ![1, 0, 0, 2, 0]]

/-- **The edge chromatic number of `C5` is three.** -/
@[simp] theorem edgeChromNum_C5 : C5.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := C5)
      C5EdgeCol (by decide) (by decide)
  · have h : 2 < C5.edgeChromNum := by graph_sat
    omega

/-- **The independence number of `P5` is three.** -/
@[simp] theorem indepNum_P5 : P5.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := P5)
    (l := ([0, 2, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `P5` is two.** -/
@[simp] theorem cliqueNum_P5 : P5.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := P5)
    (l := ([0, 1] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper two-edge-colouring of `P5`, as a symmetric table on the vertices. -/
def P5EdgeCol : P5.V → P5.V → Fin 2 :=
  ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0]]

/-- **The edge chromatic number of `P5` is two.** -/
@[simp] theorem edgeChromNum_P5 : P5.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := P5)
      P5EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum P5
    rwa [show P5.maxDeg = 2 from by decide] at h

/-- A proper two-colouring of `K2_3`. -/
def K2_3Col : K2_3.V → Fin 2 := fun v =>
  ![0, 0, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K2_3` is two.** -/
@[simp] theorem chromNum_K2_3 : K2_3.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K2_3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K2_3
  simpa using h

/-- A proper three-edge-colouring of `K2_3`, as a symmetric table on the vertices. -/
def K2_3EdgeCol : K2_3.V → K2_3.V → Fin 3 := fun x y =>
  ![![0, 0, 0, 1, 2], ![0, 0, 1, 2, 0], ![0, 1, 0, 0, 0], ![1, 2, 0, 0, 0],
   ![2, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K2_3` is three.** -/
@[simp] theorem edgeChromNum_K2_3 : K2_3.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K2_3)
      K2_3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K2_3
    rwa [show K2_3.maxDeg = 3 from by decide] at h

/-- **The independence number of `k23PlusEdge` is two.** -/
@[simp] theorem indepNum_k23PlusEdge : k23PlusEdge.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := k23PlusEdge)
    (l := ([0, 1] : List (Fin 5)).map (FinEnum.equiv (α := k23PlusEdge.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `k23PlusEdge` is three.** -/
@[simp] theorem cliqueNum_k23PlusEdge : k23PlusEdge.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := k23PlusEdge)
    (l := ([0, 2, 3] : List (Fin 5)).map (FinEnum.equiv (α := k23PlusEdge.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `k23PlusEdge`. -/
def k23PlusEdgeCol : k23PlusEdge.V → Fin 3 := fun v =>
  ![0, 0, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `k23PlusEdge` is three.** -/
@[simp] theorem chromNum_k23PlusEdge : k23PlusEdge.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring k23PlusEdgeCol (by decide)) ?_
  have h := cliqueNum_le_chromNum k23PlusEdge
  rwa [cliqueNum_k23PlusEdge] at h

/-- A proper four-edge-colouring of `k23PlusEdge`, as a symmetric table on the vertices. -/
def k23PlusEdgeEdgeCol : k23PlusEdge.V → k23PlusEdge.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2], ![0, 0, 0, 0, 1], ![0, 0, 0, 2, 3], ![1, 0, 2, 0, 0],
   ![2, 1, 3, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `k23PlusEdge` is four.** -/
@[simp] theorem edgeChromNum_k23PlusEdge : k23PlusEdge.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := k23PlusEdge)
      k23PlusEdgeEdgeCol (by decide) (by decide)
  · have h : 3 < k23PlusEdge.edgeChromNum := by graph_sat
    omega

/-- **The independence number of `fork` is three.** -/
@[simp] theorem indepNum_fork : fork.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := fork)
    (l := ([1, 2, 3] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `fork` is two.** -/
@[simp] theorem cliqueNum_fork : fork.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := fork)
    (l := ([0, 1] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper two-colouring of `fork`. -/
def forkCol : fork.V → Fin 2 :=
  ![0, 1, 1, 1, 0]

/-- **The chromatic number of `fork` is two.** -/
@[simp] theorem chromNum_fork : fork.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring forkCol (by decide)) ?_
  have h := cliqueNum_le_chromNum fork
  rwa [cliqueNum_fork] at h

/-- A proper three-edge-colouring of `fork`, as a symmetric table on the vertices. -/
def forkEdgeCol : fork.V → fork.V → Fin 3 :=
  ![![0, 0, 1, 2, 0], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `fork` is three.** -/
@[simp] theorem edgeChromNum_fork : fork.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := fork)
      forkEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum fork
    rwa [show fork.maxDeg = 3 from by decide] at h

/-- **The independence number of `banner` is three.** -/
@[simp] theorem indepNum_banner : banner.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := banner)
    (l := ([1, 3, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `banner` is two.** -/
@[simp] theorem cliqueNum_banner : banner.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := banner)
    (l := ([0, 1] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper two-colouring of `banner`. -/
def bannerCol : banner.V → Fin 2 :=
  ![0, 1, 0, 1, 1]

/-- **The chromatic number of `banner` is two.** -/
@[simp] theorem chromNum_banner : banner.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring bannerCol (by decide)) ?_
  have h := cliqueNum_le_chromNum banner
  rwa [cliqueNum_banner] at h

/-- A proper three-edge-colouring of `banner`, as a symmetric table on the vertices. -/
def bannerEdgeCol : banner.V → banner.V → Fin 3 :=
  ![![0, 0, 0, 1, 2], ![0, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0]]

/-- **The edge chromatic number of `banner` is three.** -/
@[simp] theorem edgeChromNum_banner : banner.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := banner)
      bannerEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum banner
    rwa [show banner.maxDeg = 3 from by decide] at h

/-- **The independence number of `bull` is three.** -/
@[simp] theorem indepNum_bull : bull.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := bull)
    (l := ([2, 3, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `bull` is three.** -/
@[simp] theorem cliqueNum_bull : bull.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := bull)
    (l := ([0, 1, 2] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `bull`. -/
def bullCol : bull.V → Fin 3 :=
  ![0, 1, 2, 1, 0]

/-- **The chromatic number of `bull` is three.** -/
@[simp] theorem chromNum_bull : bull.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring bullCol (by decide)) ?_
  have h := cliqueNum_le_chromNum bull
  rwa [cliqueNum_bull] at h

/-- A proper three-edge-colouring of `bull`, as a symmetric table on the vertices. -/
def bullEdgeCol : bull.V → bull.V → Fin 3 :=
  ![![0, 0, 1, 2, 0], ![0, 0, 2, 0, 1], ![1, 2, 0, 0, 0], ![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]

/-- **The edge chromatic number of `bull` is three.** -/
@[simp] theorem edgeChromNum_bull : bull.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := bull)
      bullEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum bull
    rwa [show bull.maxDeg = 3 from by decide] at h

/-- **The independence number of `house` is two.** -/
@[simp] theorem indepNum_house : house.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := house)
    (l := ([0, 3] : List (Fin 5)).map (FinEnum.equiv (α := house.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `house` is three.** -/
@[simp] theorem cliqueNum_house : house.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := house)
    (l := ([0, 1, 2] : List (Fin 5)).map (FinEnum.equiv (α := house.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `house`. -/
def houseCol : house.V → Fin 3 := fun v =>
  ![0, 1, 2, 0, 1] (FinEnum.equiv v)

/-- **The chromatic number of `house` is three.** -/
@[simp] theorem chromNum_house : house.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring houseCol (by decide)) ?_
  have h := cliqueNum_le_chromNum house
  rwa [cliqueNum_house] at h

/-- A proper three-edge-colouring of `house`, as a symmetric table on the vertices. -/
def houseEdgeCol : house.V → house.V → Fin 3 := fun x y =>
  ![![0, 0, 1, 0, 2], ![0, 0, 2, 1, 0], ![1, 2, 0, 0, 0], ![0, 1, 0, 0, 0],
   ![2, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `house` is three.** -/
@[simp] theorem edgeChromNum_house : house.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := house)
      houseEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum house
    rwa [show house.maxDeg = 3 from by decide] at h

/-- **The independence number of `kite` is two.** -/
@[simp] theorem indepNum_kite : kite.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := kite)
    (l := ([0, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `kite` is three.** -/
@[simp] theorem cliqueNum_kite : kite.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := kite)
    (l := ([0, 1, 2] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `kite`. -/
def kiteCol : kite.V → Fin 3 :=
  ![0, 1, 2, 2, 0]

/-- **The chromatic number of `kite` is three.** -/
@[simp] theorem chromNum_kite : kite.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring kiteCol (by decide)) ?_
  have h := cliqueNum_le_chromNum kite
  rwa [cliqueNum_kite] at h

/-- A proper three-edge-colouring of `kite`, as a symmetric table on the vertices. -/
def kiteEdgeCol : kite.V → kite.V → Fin 3 :=
  ![![0, 0, 1, 2, 0], ![0, 0, 2, 1, 0], ![1, 2, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `kite` is three.** -/
@[simp] theorem edgeChromNum_kite : kite.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := kite)
      kiteEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum kite
    rwa [show kite.maxDeg = 3 from by decide] at h

/-- **The independence number of `tadpole32` is two.** -/
@[simp] theorem indepNum_tadpole32 : tadpole32.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := tadpole32)
    (l := ([0, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `tadpole32` is three.** -/
@[simp] theorem cliqueNum_tadpole32 : tadpole32.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := tadpole32)
    (l := ([0, 1, 2] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `tadpole32`. -/
def tadpole32Col : tadpole32.V → Fin 3 :=
  ![0, 1, 2, 1, 0]

/-- **The chromatic number of `tadpole32` is three.** -/
@[simp] theorem chromNum_tadpole32 : tadpole32.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring tadpole32Col (by decide)) ?_
  have h := cliqueNum_le_chromNum tadpole32
  rwa [cliqueNum_tadpole32] at h

/-- A proper three-edge-colouring of `tadpole32`, as a symmetric table on the vertices. -/
def tadpole32EdgeCol : tadpole32.V → tadpole32.V → Fin 3 :=
  ![![0, 0, 1, 2, 0], ![0, 0, 2, 0, 0], ![1, 2, 0, 0, 0], ![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `tadpole32` is three.** -/
@[simp] theorem edgeChromNum_tadpole32 : tadpole32.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tadpole32)
      tadpole32EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum tadpole32
    rwa [show tadpole32.maxDeg = 3 from by decide] at h

/-- **The independence number of `K1_4` is four.** -/
@[simp] theorem indepNum_K1_4 : K1_4.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K1_4)
    (l := ([1, 2, 3, 4] : List (Fin 5)).map (FinEnum.equiv (α := K1_4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K1_4` is two.** -/
@[simp] theorem cliqueNum_K1_4 : K1_4.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_4)
    (l := ([0, 1] : List (Fin 5)).map (FinEnum.equiv (α := K1_4.V)).symm)
    (by decide) (by decide)

/-- A proper two-colouring of `K1_4`. -/
def K1_4Col : K1_4.V → Fin 2 := fun v =>
  ![0, 1, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K1_4` is two.** -/
@[simp] theorem chromNum_K1_4 : K1_4.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K1_4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_4
  rwa [cliqueNum_K1_4] at h

/-- A proper four-edge-colouring of `K1_4`, as a symmetric table on the vertices. -/
def K1_4EdgeCol : K1_4.V → K1_4.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 3], ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_4` is four.** -/
@[simp] theorem edgeChromNum_K1_4 : K1_4.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_4)
      K1_4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_4
    rwa [show K1_4.maxDeg = 4 from by decide] at h

/-- **The independence number of `butterfly` is two.** -/
@[simp] theorem indepNum_butterfly : butterfly.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := butterfly)
    (l := ([1, 3] : List (Fin 5)).map (FinEnum.equiv (α := butterfly.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `butterfly` is three.** -/
@[simp] theorem cliqueNum_butterfly : butterfly.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := butterfly)
    (l := ([0, 1, 2] : List (Fin 5)).map (FinEnum.equiv (α := butterfly.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `butterfly`. -/
def butterflyCol : butterfly.V → Fin 3 := fun v =>
  ![0, 1, 2, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `butterfly` is three.** -/
@[simp] theorem chromNum_butterfly : butterfly.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring butterflyCol (by decide)) ?_
  have h := cliqueNum_le_chromNum butterfly
  rwa [cliqueNum_butterfly] at h

/-- A proper four-edge-colouring of `butterfly`, as a symmetric table on the vertices. -/
def butterflyEdgeCol : butterfly.V → butterfly.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 0, 0], ![1, 2, 0, 0, 0], ![2, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `butterfly` is four.** -/
@[simp] theorem edgeChromNum_butterfly : butterfly.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := butterfly)
      butterflyEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum butterfly
    rwa [show butterfly.maxDeg = 4 from by decide] at h

/-- **The independence number of `W4` is two.** -/
@[simp] theorem indepNum_W4 : W4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := W4)
    (l := ([1, 3] : List (Fin 5)).map (FinEnum.equiv (α := W4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `W4` is three.** -/
@[simp] theorem cliqueNum_W4 : W4.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := W4)
    (l := ([0, 1, 2] : List (Fin 5)).map (FinEnum.equiv (α := W4.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `W4`. -/
def W4Col : W4.V → Fin 3 := fun v =>
  ![0, 1, 2, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `W4` is three.** -/
@[simp] theorem chromNum_W4 : W4.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring W4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum W4
  rwa [cliqueNum_W4] at h

/-- A proper four-edge-colouring of `W4`, as a symmetric table on the vertices. -/
def W4EdgeCol : W4.V → W4.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 0, 1], ![1, 2, 0, 3, 0], ![2, 0, 3, 0, 0],
   ![3, 1, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `W4` is four.** -/
@[simp] theorem edgeChromNum_W4 : W4.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := W4)
      W4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum W4
    rwa [show W4.maxDeg = 4 from by decide] at h

/-- **The independence number of `cricket` is three.** -/
@[simp] theorem indepNum_cricket : cricket.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := cricket)
    (l := ([1, 3, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `cricket` is three.** -/
@[simp] theorem cliqueNum_cricket : cricket.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := cricket)
    (l := ([0, 1, 2] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `cricket`. -/
def cricketCol : cricket.V → Fin 3 :=
  ![0, 1, 2, 1, 1]

/-- **The chromatic number of `cricket` is three.** -/
@[simp] theorem chromNum_cricket : cricket.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring cricketCol (by decide)) ?_
  have h := cliqueNum_le_chromNum cricket
  rwa [cliqueNum_cricket] at h

/-- A proper four-edge-colouring of `cricket`, as a symmetric table on the vertices. -/
def cricketEdgeCol : cricket.V → cricket.V → Fin 4 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 0, 0], ![1, 2, 0, 0, 0], ![2, 0, 0, 0, 0], ![3, 0, 0, 0, 0]]

/-- **The edge chromatic number of `cricket` is four.** -/
@[simp] theorem edgeChromNum_cricket : cricket.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := cricket)
      cricketEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum cricket
    rwa [show cricket.maxDeg = 4 from by decide] at h

/-- **The independence number of `gem` is two.** -/
@[simp] theorem indepNum_gem : gem.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := gem)
    (l := ([1, 3] : List (Fin 5)).map (FinEnum.equiv (α := gem.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `gem` is three.** -/
@[simp] theorem cliqueNum_gem : gem.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := gem)
    (l := ([0, 1, 2] : List (Fin 5)).map (FinEnum.equiv (α := gem.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `gem`. -/
def gemCol : gem.V → Fin 3 := fun v =>
  ![0, 1, 2, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `gem` is three.** -/
@[simp] theorem chromNum_gem : gem.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring gemCol (by decide)) ?_
  have h := cliqueNum_le_chromNum gem
  rwa [cliqueNum_gem] at h

/-- A proper four-edge-colouring of `gem`, as a symmetric table on the vertices. -/
def gemEdgeCol : gem.V → gem.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 0, 0], ![1, 2, 0, 0, 0], ![2, 0, 0, 0, 1],
   ![3, 0, 0, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `gem` is four.** -/
@[simp] theorem edgeChromNum_gem : gem.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := gem)
      gemEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum gem
    rwa [show gem.maxDeg = 4 from by decide] at h

/-- **The independence number of `dart` is three.** -/
@[simp] theorem indepNum_dart : dart.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := dart)
    (l := ([2, 3, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `dart` is three.** -/
@[simp] theorem cliqueNum_dart : dart.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := dart)
    (l := ([0, 1, 2] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper three-colouring of `dart`. -/
def dartCol : dart.V → Fin 3 :=
  ![0, 1, 2, 2, 1]

/-- **The chromatic number of `dart` is three.** -/
@[simp] theorem chromNum_dart : dart.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring dartCol (by decide)) ?_
  have h := cliqueNum_le_chromNum dart
  rwa [cliqueNum_dart] at h

/-- A proper four-edge-colouring of `dart`, as a symmetric table on the vertices. -/
def dartEdgeCol : dart.V → dart.V → Fin 4 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 1, 0], ![1, 2, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 0, 0, 0]]

/-- **The edge chromatic number of `dart` is four.** -/
@[simp] theorem edgeChromNum_dart : dart.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := dart)
      dartEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum dart
    rwa [show dart.maxDeg = 4 from by decide] at h

/-- **The independence number of `lollipop41` is two.** -/
@[simp] theorem indepNum_lollipop41 : lollipop41.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := lollipop41)
    (l := ([1, 4] : List (Fin 5)))
    (by decide) (by decide)

/-- **The clique number of `lollipop41` is four.** -/
@[simp] theorem cliqueNum_lollipop41 : lollipop41.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := lollipop41)
    (l := ([0, 1, 2, 3] : List (Fin 5)))
    (by decide) (by decide)

/-- A proper four-colouring of `lollipop41`. -/
def lollipop41Col : lollipop41.V → Fin 4 :=
  ![0, 1, 2, 3, 1]

/-- **The chromatic number of `lollipop41` is four.** -/
@[simp] theorem chromNum_lollipop41 : lollipop41.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring lollipop41Col (by decide)) ?_
  have h := cliqueNum_le_chromNum lollipop41
  rwa [cliqueNum_lollipop41] at h

/-- A proper four-edge-colouring of `lollipop41`, as a symmetric table on the vertices. -/
def lollipop41EdgeCol : lollipop41.V → lollipop41.V → Fin 4 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 1, 0], ![1, 2, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 0, 0, 0]]

/-- **The edge chromatic number of `lollipop41` is four.** -/
@[simp] theorem edgeChromNum_lollipop41 : lollipop41.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := lollipop41)
      lollipop41EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum lollipop41
    rwa [show lollipop41.maxDeg = 4 from by decide] at h

/-- **The clique number of `book3` is three.** -/
@[simp] theorem cliqueNum_book3 : book3.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := book3)
    (l := ([0, 1, 2] : List (Fin 5)).map (FinEnum.equiv (α := book3.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `book3`. -/
def book3Col : book3.V → Fin 3 := fun v =>
  ![0, 1, 2, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `book3` is three.** -/
@[simp] theorem chromNum_book3 : book3.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring book3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum book3
  rwa [cliqueNum_book3] at h

/-- A proper four-edge-colouring of `book3`, as a symmetric table on the vertices. -/
def book3EdgeCol : book3.V → book3.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 3, 1], ![1, 2, 0, 0, 0], ![2, 3, 0, 0, 0],
   ![3, 1, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `book3` is four.** -/
@[simp] theorem edgeChromNum_book3 : book3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := book3)
      book3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum book3
    rwa [show book3.maxDeg = 4 from by decide] at h

/-- **The independence number of `K5MinusP3` is two.** -/
@[simp] theorem indepNum_K5MinusP3 : K5MinusP3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K5MinusP3)
    (l := ([0, 1] : List (Fin 5)).map (FinEnum.equiv (α := K5MinusP3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K5MinusP3` is four.** -/
@[simp] theorem cliqueNum_K5MinusP3 : K5MinusP3.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K5MinusP3)
    (l := ([0, 2, 3, 4] : List (Fin 5)).map (FinEnum.equiv (α := K5MinusP3.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K5MinusP3`. -/
def K5MinusP3Col : K5MinusP3.V → Fin 4 := fun v =>
  ![0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K5MinusP3` is four.** -/
@[simp] theorem chromNum_K5MinusP3 : K5MinusP3.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K5MinusP3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K5MinusP3
  rwa [cliqueNum_K5MinusP3] at h

/-- A proper four-edge-colouring of `K5MinusP3`, as a symmetric table on the vertices. -/
def K5MinusP3EdgeCol : K5MinusP3.V → K5MinusP3.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2], ![0, 0, 0, 2, 3], ![0, 0, 0, 3, 1], ![1, 2, 3, 0, 0],
   ![2, 3, 1, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K5MinusP3` is four.** -/
@[simp] theorem edgeChromNum_K5MinusP3 : K5MinusP3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K5MinusP3)
      K5MinusP3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K5MinusP3
    rwa [show K5MinusP3.maxDeg = 4 from by decide] at h

/-- **The independence number of `K5MinusEdge` is two.** -/
@[simp] theorem indepNum_K5MinusEdge : K5MinusEdge.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K5MinusEdge)
    (l := ([0, 1] : List (Fin 5)).map (FinEnum.equiv (α := K5MinusEdge.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K5MinusEdge` is four.** -/
@[simp] theorem cliqueNum_K5MinusEdge : K5MinusEdge.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K5MinusEdge)
    (l := ([0, 2, 3, 4] : List (Fin 5)).map (FinEnum.equiv (α := K5MinusEdge.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K5MinusEdge`. -/
def K5MinusEdgeCol : K5MinusEdge.V → Fin 4 := fun v =>
  ![0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K5MinusEdge` is four.** -/
@[simp] theorem chromNum_K5MinusEdge : K5MinusEdge.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K5MinusEdgeCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K5MinusEdge
  rwa [cliqueNum_K5MinusEdge] at h

/-- A proper five-edge-colouring of `K5MinusEdge`, as a symmetric table on the vertices. -/
def K5MinusEdgeEdgeCol : K5MinusEdge.V → K5MinusEdge.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2], ![0, 0, 1, 2, 3], ![0, 1, 0, 3, 4], ![1, 2, 3, 0, 0],
   ![2, 3, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K5MinusEdge` is five.** -/
@[simp] theorem edgeChromNum_K5MinusEdge : K5MinusEdge.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K5MinusEdge)
      K5MinusEdgeEdgeCol (by decide) (by decide)
  · have h : 4 < K5MinusEdge.edgeChromNum := by graph_sat
    omega

/-- A proper five-edge-colouring of `K5`, as a symmetric table on the vertices. -/
def K5EdgeCol : K5.V → K5.V → Fin 5 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 2, 3, 4], ![1, 2, 0, 4, 0], ![2, 3, 4, 0, 1], ![3, 4, 0, 1, 0]]

/-- **The edge chromatic number of `K5` is five.** -/
@[simp] theorem edgeChromNum_K5 : K5.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K5)
      K5EdgeCol (by decide) (by decide)
  · have h : 4 < K5.edgeChromNum := by graph_sat
    omega

/-! ## Six vertices -/

/-- **The independence number of `P6` is three.** -/
@[simp] theorem indepNum_P6 : P6.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := P6)
    (l := ([0, 2, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `P6` is two.** -/
@[simp] theorem cliqueNum_P6 : P6.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := P6)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-edge-colouring of `P6`, as a symmetric table on the vertices. -/
def P6EdgeCol : P6.V → P6.V → Fin 2 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `P6` is two.** -/
@[simp] theorem edgeChromNum_P6 : P6.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := P6)
      P6EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum P6
    rwa [show P6.maxDeg = 2 from by decide] at h

/-- **The independence number of `spider113` is four.** -/
@[simp] theorem indepNum_spider113 : spider113.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := spider113)
    (l := ([1, 2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `spider113` is two.** -/
@[simp] theorem cliqueNum_spider113 : spider113.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := spider113)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `spider113`. -/
def spider113Col : spider113.V → Fin 2 :=
  ![0, 1, 1, 1, 0, 1]

/-- **The chromatic number of `spider113` is two.** -/
@[simp] theorem chromNum_spider113 : spider113.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring spider113Col (by decide)) ?_
  have h := cliqueNum_le_chromNum spider113
  rwa [cliqueNum_spider113] at h

/-- A proper three-edge-colouring of `spider113`, as a symmetric table on the vertices. -/
def spider113EdgeCol : spider113.V → spider113.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]

/-- **The edge chromatic number of `spider113` is three.** -/
@[simp] theorem edgeChromNum_spider113 : spider113.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := spider113)
      spider113EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum spider113
    rwa [show spider113.maxDeg = 3 from by decide] at h

/-- **The independence number of `spider122` is three.** -/
@[simp] theorem indepNum_spider122 : spider122.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := spider122)
    (l := ([0, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `spider122` is two.** -/
@[simp] theorem cliqueNum_spider122 : spider122.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := spider122)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `spider122`. -/
def spider122Col : spider122.V → Fin 2 :=
  ![0, 1, 1, 0, 1, 0]

/-- **The chromatic number of `spider122` is two.** -/
@[simp] theorem chromNum_spider122 : spider122.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring spider122Col (by decide)) ?_
  have h := cliqueNum_le_chromNum spider122
  rwa [cliqueNum_spider122] at h

/-- A proper three-edge-colouring of `spider122`, as a symmetric table on the vertices. -/
def spider122EdgeCol : spider122.V → spider122.V → Fin 3 :=
  ![![0, 0, 1, 0, 2, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `spider122` is three.** -/
@[simp] theorem edgeChromNum_spider122 : spider122.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := spider122)
      spider122EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum spider122
    rwa [show spider122.maxDeg = 3 from by decide] at h

/-- **The independence number of `cross` is four.** -/
@[simp] theorem indepNum_cross : cross.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := cross)
    (l := ([1, 2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `cross` is two.** -/
@[simp] theorem cliqueNum_cross : cross.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := cross)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `cross`. -/
def crossCol : cross.V → Fin 2 :=
  ![0, 1, 1, 1, 1, 0]

/-- **The chromatic number of `cross` is two.** -/
@[simp] theorem chromNum_cross : cross.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring crossCol (by decide)) ?_
  have h := cliqueNum_le_chromNum cross
  rwa [cliqueNum_cross] at h

/-- A proper four-edge-colouring of `cross`, as a symmetric table on the vertices. -/
def crossEdgeCol : cross.V → cross.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `cross` is four.** -/
@[simp] theorem edgeChromNum_cross : cross.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := cross)
      crossEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum cross
    rwa [show cross.maxDeg = 4 from by decide] at h

/-- **The independence number of `H` is four.** -/
@[simp] theorem indepNum_H : H.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := H)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `H` is two.** -/
@[simp] theorem cliqueNum_H : H.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := H)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `H`. -/
def HCol : H.V → Fin 2 :=
  ![0, 1, 1, 1, 0, 0]

/-- **The chromatic number of `H` is two.** -/
@[simp] theorem chromNum_H : H.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring HCol (by decide)) ?_
  have h := cliqueNum_le_chromNum H
  rwa [cliqueNum_H] at h

/-- A proper three-edge-colouring of `H`, as a symmetric table on the vertices. -/
def HEdgeCol : H.V → H.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 1, 2], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0]]

/-- **The edge chromatic number of `H` is three.** -/
@[simp] theorem edgeChromNum_H : H.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := H)
      HEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum H
    rwa [show H.maxDeg = 3 from by decide] at h

/-- **The independence number of `K1_5` is five.** -/
@[simp] theorem indepNum_K1_5 : K1_5.indepNum = 5 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K1_5)
    (l := ([1, 2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K1_5.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K1_5` is two.** -/
@[simp] theorem cliqueNum_K1_5 : K1_5.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_5)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K1_5.V)).symm)
    (by decide) (by decide)

/-- A proper two-colouring of `K1_5`. -/
def K1_5Col : K1_5.V → Fin 2 := fun v =>
  ![0, 1, 1, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K1_5` is two.** -/
@[simp] theorem chromNum_K1_5 : K1_5.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K1_5Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_5
  rwa [cliqueNum_K1_5] at h

/-- A proper five-edge-colouring of `K1_5`, as a symmetric table on the vertices. -/
def K1_5EdgeCol : K1_5.V → K1_5.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_5` is five.** -/
@[simp] theorem edgeChromNum_K1_5 : K1_5.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_5)
      K1_5EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_5
    rwa [show K1_5.maxDeg = 5 from by decide] at h

/-- **The clique number of `C6` is two.** -/
@[simp] theorem cliqueNum_C6 : C6.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := C6)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `C6`. -/
def C6Col : C6.V → Fin 2 :=
  ![0, 1, 0, 1, 0, 1]

/-- **The chromatic number of `C6` is two.** -/
@[simp] theorem chromNum_C6 : C6.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring C6Col (by decide)) ?_
  have h := cliqueNum_le_chromNum C6
  rwa [cliqueNum_C6] at h

/-- A proper two-edge-colouring of `C6`, as a symmetric table on the vertices. -/
def C6EdgeCol : C6.V → C6.V → Fin 2 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `C6` is two.** -/
@[simp] theorem edgeChromNum_C6 : C6.edgeChromNum = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := C6)
      C6EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum C6
    rwa [show C6.maxDeg = 2 from by decide] at h

/-- **The independence number of `tadpole33` is three.** -/
@[simp] theorem indepNum_tadpole33 : tadpole33.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := tadpole33)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `tadpole33` is three.** -/
@[simp] theorem cliqueNum_tadpole33 : tadpole33.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := tadpole33)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `tadpole33`. -/
def tadpole33Col : tadpole33.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 1]

/-- **The chromatic number of `tadpole33` is three.** -/
@[simp] theorem chromNum_tadpole33 : tadpole33.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring tadpole33Col (by decide)) ?_
  have h := cliqueNum_le_chromNum tadpole33
  rwa [cliqueNum_tadpole33] at h

/-- A proper three-edge-colouring of `tadpole33`, as a symmetric table on the vertices. -/
def tadpole33EdgeCol : tadpole33.V → tadpole33.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]

/-- **The edge chromatic number of `tadpole33` is three.** -/
@[simp] theorem edgeChromNum_tadpole33 : tadpole33.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tadpole33)
      tadpole33EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum tadpole33
    rwa [show tadpole33.maxDeg = 3 from by decide] at h

/-- **The independence number of `tadpole42` is three.** -/
@[simp] theorem indepNum_tadpole42 : tadpole42.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := tadpole42)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `tadpole42` is two.** -/
@[simp] theorem cliqueNum_tadpole42 : tadpole42.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := tadpole42)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `tadpole42`. -/
def tadpole42Col : tadpole42.V → Fin 2 :=
  ![0, 1, 0, 1, 1, 0]

/-- **The chromatic number of `tadpole42` is two.** -/
@[simp] theorem chromNum_tadpole42 : tadpole42.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring tadpole42Col (by decide)) ?_
  have h := cliqueNum_le_chromNum tadpole42
  rwa [cliqueNum_tadpole42] at h

/-- A proper three-edge-colouring of `tadpole42`, as a symmetric table on the vertices. -/
def tadpole42EdgeCol : tadpole42.V → tadpole42.V → Fin 3 :=
  ![![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `tadpole42` is three.** -/
@[simp] theorem edgeChromNum_tadpole42 : tadpole42.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tadpole42)
      tadpole42EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum tadpole42
    rwa [show tadpole42.maxDeg = 3 from by decide] at h

/-- **The independence number of `tadpole51` is three.** -/
@[simp] theorem indepNum_tadpole51 : tadpole51.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := tadpole51)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `tadpole51` is two.** -/
@[simp] theorem cliqueNum_tadpole51 : tadpole51.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := tadpole51)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `tadpole51`. -/
def tadpole51Col : tadpole51.V → Fin 3 :=
  ![0, 1, 0, 1, 2, 1]

/-- **The chromatic number of `tadpole51` is three.** -/
@[simp] theorem chromNum_tadpole51 : tadpole51.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring tadpole51Col (by decide)) ?_
  have h : 2 < tadpole51.chromNum := by graph_sat
  omega

/-- A proper three-edge-colouring of `tadpole51`, as a symmetric table on the vertices. -/
def tadpole51EdgeCol : tadpole51.V → tadpole51.V → Fin 3 :=
  ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0],
   ![1, 0, 0, 2, 0, 0], ![2, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `tadpole51` is three.** -/
@[simp] theorem edgeChromNum_tadpole51 : tadpole51.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := tadpole51)
      tadpole51EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum tadpole51
    rwa [show tadpole51.maxDeg = 3 from by decide] at h

/-- **The independence number of `net` is three.** -/
@[simp] theorem indepNum_net : net.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := net)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `net` is three.** -/
@[simp] theorem cliqueNum_net : net.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := net)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `net`. -/
def netCol : net.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 0]

/-- **The chromatic number of `net` is three.** -/
@[simp] theorem chromNum_net : net.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring netCol (by decide)) ?_
  have h := cliqueNum_le_chromNum net
  rwa [cliqueNum_net] at h

/-- A proper three-edge-colouring of `net`, as a symmetric table on the vertices. -/
def netEdgeCol : net.V → net.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 1, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `net` is three.** -/
@[simp] theorem edgeChromNum_net : net.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := net)
      netEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum net
    rwa [show net.maxDeg = 3 from by decide] at h

/-- **The independence number of `c3Pendants210` is four.** -/
@[simp] theorem indepNum_c3Pendants210 : c3Pendants210.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c3Pendants210)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c3Pendants210` is three.** -/
@[simp] theorem cliqueNum_c3Pendants210 : c3Pendants210.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c3Pendants210)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `c3Pendants210`. -/
def c3Pendants210Col : c3Pendants210.V → Fin 3 :=
  ![0, 1, 2, 1, 1, 0]

/-- **The chromatic number of `c3Pendants210` is three.** -/
@[simp] theorem chromNum_c3Pendants210 : c3Pendants210.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring c3Pendants210Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c3Pendants210
  rwa [cliqueNum_c3Pendants210] at h

/-- A proper four-edge-colouring of `c3Pendants210`, as a symmetric table on the vertices. -/
def c3Pendants210EdgeCol : c3Pendants210.V → c3Pendants210.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 0, 0, 1], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c3Pendants210` is four.** -/
@[simp] theorem edgeChromNum_c3Pendants210 : c3Pendants210.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c3Pendants210)
      c3Pendants210EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c3Pendants210
    rwa [show c3Pendants210.maxDeg = 4 from by decide] at h

/-- **The independence number of `c3Pendants300` is four.** -/
@[simp] theorem indepNum_c3Pendants300 : c3Pendants300.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c3Pendants300)
    (l := ([1, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c3Pendants300` is three.** -/
@[simp] theorem cliqueNum_c3Pendants300 : c3Pendants300.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c3Pendants300)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `c3Pendants300`. -/
def c3Pendants300Col : c3Pendants300.V → Fin 3 :=
  ![0, 1, 2, 1, 1, 1]

/-- **The chromatic number of `c3Pendants300` is three.** -/
@[simp] theorem chromNum_c3Pendants300 : c3Pendants300.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring c3Pendants300Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c3Pendants300
  rwa [cliqueNum_c3Pendants300] at h

/-- A proper five-edge-colouring of `c3Pendants300`, as a symmetric table on the vertices. -/
def c3Pendants300EdgeCol : c3Pendants300.V → c3Pendants300.V → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c3Pendants300` is five.** -/
@[simp] theorem edgeChromNum_c3Pendants300 : c3Pendants300.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c3Pendants300)
      c3Pendants300EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c3Pendants300
    rwa [show c3Pendants300.maxDeg = 5 from by decide] at h

/-- **The independence number of `c3Legs12` is three.** -/
@[simp] theorem indepNum_c3Legs12 : c3Legs12.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c3Legs12)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c3Legs12` is three.** -/
@[simp] theorem cliqueNum_c3Legs12 : c3Legs12.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c3Legs12)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `c3Legs12`. -/
def c3Legs12Col : c3Legs12.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 1]

/-- **The chromatic number of `c3Legs12` is three.** -/
@[simp] theorem chromNum_c3Legs12 : c3Legs12.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring c3Legs12Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c3Legs12
  rwa [cliqueNum_c3Legs12] at h

/-- A proper three-edge-colouring of `c3Legs12`, as a symmetric table on the vertices. -/
def c3Legs12EdgeCol : c3Legs12.V → c3Legs12.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 1, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c3Legs12` is three.** -/
@[simp] theorem edgeChromNum_c3Legs12 : c3Legs12.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c3Legs12)
      c3Legs12EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c3Legs12
    rwa [show c3Legs12.maxDeg = 3 from by decide] at h

/-- **The independence number of `c3Legs12Same` is three.** -/
@[simp] theorem indepNum_c3Legs12Same : c3Legs12Same.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c3Legs12Same)
    (l := ([1, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c3Legs12Same` is three.** -/
@[simp] theorem cliqueNum_c3Legs12Same : c3Legs12Same.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c3Legs12Same)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `c3Legs12Same`. -/
def c3Legs12SameCol : c3Legs12Same.V → Fin 3 :=
  ![0, 1, 2, 1, 1, 0]

/-- **The chromatic number of `c3Legs12Same` is three.** -/
@[simp] theorem chromNum_c3Legs12Same : c3Legs12Same.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring c3Legs12SameCol (by decide)) ?_
  have h := cliqueNum_le_chromNum c3Legs12Same
  rwa [cliqueNum_c3Legs12Same] at h

/-- A proper four-edge-colouring of `c3Legs12Same`, as a symmetric table on the vertices. -/
def c3Legs12SameEdgeCol : c3Legs12Same.V → c3Legs12Same.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c3Legs12Same` is four.** -/
@[simp] theorem edgeChromNum_c3Legs12Same : c3Legs12Same.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c3Legs12Same)
      c3Legs12SameEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c3Legs12Same
    rwa [show c3Legs12Same.maxDeg = 4 from by decide] at h

/-- **The independence number of `c3Fork` is three.** -/
@[simp] theorem indepNum_c3Fork : c3Fork.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c3Fork)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c3Fork` is three.** -/
@[simp] theorem cliqueNum_c3Fork : c3Fork.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c3Fork)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `c3Fork`. -/
def c3ForkCol : c3Fork.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 0]

/-- **The chromatic number of `c3Fork` is three.** -/
@[simp] theorem chromNum_c3Fork : c3Fork.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring c3ForkCol (by decide)) ?_
  have h := cliqueNum_le_chromNum c3Fork
  rwa [cliqueNum_c3Fork] at h

/-- A proper three-edge-colouring of `c3Fork`, as a symmetric table on the vertices. -/
def c3ForkEdgeCol : c3Fork.V → c3Fork.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 1],
   ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]

/-- **The edge chromatic number of `c3Fork` is three.** -/
@[simp] theorem edgeChromNum_c3Fork : c3Fork.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c3Fork)
      c3ForkEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c3Fork
    rwa [show c3Fork.maxDeg = 3 from by decide] at h

/-- **The independence number of `c4Pendants1010` is four.** -/
@[simp] theorem indepNum_c4Pendants1010 : c4Pendants1010.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c4Pendants1010)
    (l := ([1, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c4Pendants1010` is two.** -/
@[simp] theorem cliqueNum_c4Pendants1010 : c4Pendants1010.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c4Pendants1010)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `c4Pendants1010`. -/
def c4Pendants1010Col : c4Pendants1010.V → Fin 2 :=
  ![0, 1, 0, 1, 1, 1]

/-- **The chromatic number of `c4Pendants1010` is two.** -/
@[simp] theorem chromNum_c4Pendants1010 : c4Pendants1010.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring c4Pendants1010Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c4Pendants1010
  rwa [cliqueNum_c4Pendants1010] at h

/-- A proper three-edge-colouring of `c4Pendants1010`, as a symmetric table on the vertices. -/
def c4Pendants1010EdgeCol : c4Pendants1010.V → c4Pendants1010.V → Fin 3 :=
  ![![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 2], ![1, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0]]

/-- **The edge chromatic number of `c4Pendants1010` is three.** -/
@[simp] theorem edgeChromNum_c4Pendants1010 : c4Pendants1010.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c4Pendants1010)
      c4Pendants1010EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c4Pendants1010
    rwa [show c4Pendants1010.maxDeg = 3 from by decide] at h

/-- **The independence number of `c4Pendants1100` is three.** -/
@[simp] theorem indepNum_c4Pendants1100 : c4Pendants1100.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c4Pendants1100)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c4Pendants1100` is two.** -/
@[simp] theorem cliqueNum_c4Pendants1100 : c4Pendants1100.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c4Pendants1100)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `c4Pendants1100`. -/
def c4Pendants1100Col : c4Pendants1100.V → Fin 2 :=
  ![0, 1, 0, 1, 1, 0]

/-- **The chromatic number of `c4Pendants1100` is two.** -/
@[simp] theorem chromNum_c4Pendants1100 : c4Pendants1100.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring c4Pendants1100Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c4Pendants1100
  rwa [cliqueNum_c4Pendants1100] at h

/-- A proper three-edge-colouring of `c4Pendants1100`, as a symmetric table on the vertices. -/
def c4Pendants1100EdgeCol : c4Pendants1100.V → c4Pendants1100.V → Fin 3 :=
  ![![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 2], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c4Pendants1100` is three.** -/
@[simp] theorem edgeChromNum_c4Pendants1100 : c4Pendants1100.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c4Pendants1100)
      c4Pendants1100EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c4Pendants1100
    rwa [show c4Pendants1100.maxDeg = 3 from by decide] at h

/-- **The independence number of `c4Pendants2000` is four.** -/
@[simp] theorem indepNum_c4Pendants2000 : c4Pendants2000.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := c4Pendants2000)
    (l := ([1, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `c4Pendants2000` is two.** -/
@[simp] theorem cliqueNum_c4Pendants2000 : c4Pendants2000.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := c4Pendants2000)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `c4Pendants2000`. -/
def c4Pendants2000Col : c4Pendants2000.V → Fin 2 :=
  ![0, 1, 0, 1, 1, 1]

/-- **The chromatic number of `c4Pendants2000` is two.** -/
@[simp] theorem chromNum_c4Pendants2000 : c4Pendants2000.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring c4Pendants2000Col (by decide)) ?_
  have h := cliqueNum_le_chromNum c4Pendants2000
  rwa [cliqueNum_c4Pendants2000] at h

/-- A proper four-edge-colouring of `c4Pendants2000`, as a symmetric table on the vertices. -/
def c4Pendants2000EdgeCol : c4Pendants2000.V → c4Pendants2000.V → Fin 4 :=
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `c4Pendants2000` is four.** -/
@[simp] theorem edgeChromNum_c4Pendants2000 : c4Pendants2000.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := c4Pendants2000)
      c4Pendants2000EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum c4Pendants2000
    rwa [show c4Pendants2000.maxDeg = 4 from by decide] at h

/-- **The independence number of `theta223` is three.** -/
@[simp] theorem indepNum_theta223 : theta223.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := theta223)
    (l := ([2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `theta223` is two.** -/
@[simp] theorem cliqueNum_theta223 : theta223.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := theta223)
    (l := ([0, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `theta223`. -/
def theta223Col : theta223.V → Fin 3 :=
  ![0, 0, 1, 1, 1, 2]

/-- **The chromatic number of `theta223` is three.** -/
@[simp] theorem chromNum_theta223 : theta223.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring theta223Col (by decide)) ?_
  have h : 2 < theta223.chromNum := by graph_sat
  omega

/-- A proper three-edge-colouring of `theta223`, as a symmetric table on the vertices. -/
def theta223EdgeCol : theta223.V → theta223.V → Fin 3 :=
  ![![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 2], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0]]

/-- **The edge chromatic number of `theta223` is three.** -/
@[simp] theorem edgeChromNum_theta223 : theta223.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := theta223)
      theta223EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum theta223
    rwa [show theta223.maxDeg = 3 from by decide] at h

/-- **The independence number of `theta124` is three.** -/
@[simp] theorem indepNum_theta124 : theta124.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := theta124)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `theta124` is three.** -/
@[simp] theorem cliqueNum_theta124 : theta124.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := theta124)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `theta124`. -/
def theta124Col : theta124.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 2]

/-- **The chromatic number of `theta124` is three.** -/
@[simp] theorem chromNum_theta124 : theta124.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring theta124Col (by decide)) ?_
  have h := cliqueNum_le_chromNum theta124
  rwa [cliqueNum_theta124] at h

/-- A proper three-edge-colouring of `theta124`, as a symmetric table on the vertices. -/
def theta124EdgeCol : theta124.V → theta124.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 0, 1], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 2], ![0, 1, 0, 0, 2, 0]]

/-- **The edge chromatic number of `theta124` is three.** -/
@[simp] theorem edgeChromNum_theta124 : theta124.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := theta124)
      theta124EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum theta124
    rwa [show theta124.maxDeg = 3 from by decide] at h

/-- **The independence number of `domino` is three.** -/
@[simp] theorem indepNum_domino : domino.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := domino)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := domino.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `domino` is two.** -/
@[simp] theorem cliqueNum_domino : domino.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := domino)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := domino.V)).symm)
    (by decide) (by decide)

/-- A proper two-colouring of `domino`. -/
def dominoCol : domino.V → Fin 2 := fun v =>
  ![0, 1, 0, 1, 0, 1] (FinEnum.equiv v)

/-- **The chromatic number of `domino` is two.** -/
@[simp] theorem chromNum_domino : domino.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring dominoCol (by decide)) ?_
  have h := cliqueNum_le_chromNum domino
  rwa [cliqueNum_domino] at h

/-- A proper three-edge-colouring of `domino`, as a symmetric table on the vertices. -/
def dominoEdgeCol : domino.V → domino.V → Fin 3 := fun x y =>
  ![![0, 0, 0, 1, 0, 2], ![0, 0, 1, 0, 2, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![0, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `domino` is three.** -/
@[simp] theorem edgeChromNum_domino : domino.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := domino)
      dominoEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum domino
    rwa [show domino.maxDeg = 3 from by decide] at h

/-- **The independence number of `barbell` is two.** -/
@[simp] theorem indepNum_barbell : barbell.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := barbell)
    (l := ([0, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `barbell` is three.** -/
@[simp] theorem cliqueNum_barbell : barbell.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := barbell)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `barbell`. -/
def barbellCol : barbell.V → Fin 3 :=
  ![0, 1, 2, 1, 0, 2]

/-- **The chromatic number of `barbell` is three.** -/
@[simp] theorem chromNum_barbell : barbell.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring barbellCol (by decide)) ?_
  have h := cliqueNum_le_chromNum barbell
  rwa [cliqueNum_barbell] at h

/-- A proper three-edge-colouring of `barbell`, as a symmetric table on the vertices. -/
def barbellEdgeCol : barbell.V → barbell.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 1],
   ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 1, 2, 0]]

/-- **The edge chromatic number of `barbell` is three.** -/
@[simp] theorem edgeChromNum_barbell : barbell.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := barbell)
      barbellEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum barbell
    rwa [show barbell.maxDeg = 3 from by decide] at h

/-- **The independence number of `fish` is three.** -/
@[simp] theorem indepNum_fish : fish.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := fish)
    (l := ([1, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := fish.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `fish` is three.** -/
@[simp] theorem cliqueNum_fish : fish.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := fish)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := fish.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `fish`. -/
def fishCol : fish.V → Fin 3 := fun v =>
  ![0, 1, 2, 1, 0, 1] (FinEnum.equiv v)

/-- **The chromatic number of `fish` is three.** -/
@[simp] theorem chromNum_fish : fish.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring fishCol (by decide)) ?_
  have h := cliqueNum_le_chromNum fish
  rwa [cliqueNum_fish] at h

/-- A proper four-edge-colouring of `fish`, as a symmetric table on the vertices. -/
def fishEdgeCol : fish.V → fish.V → Fin 4 := fun x y =>
  ![![0, 0, 1, 2, 0, 3], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 1], ![3, 0, 0, 0, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `fish` is four.** -/
@[simp] theorem edgeChromNum_fish : fish.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := fish)
      fishEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum fish
    rwa [show fish.maxDeg = 4 from by decide] at h

/-- **The independence number of `housePendantApex` is three.** -/
@[simp] theorem indepNum_housePendantApex : housePendantApex.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := housePendantApex)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `housePendantApex` is three.** -/
@[simp] theorem cliqueNum_housePendantApex : housePendantApex.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := housePendantApex)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `housePendantApex`. -/
def housePendantApexCol : housePendantApex.V → Fin 3 :=
  ![0, 1, 0, 1, 2, 1]

/-- **The chromatic number of `housePendantApex` is three.** -/
@[simp] theorem chromNum_housePendantApex : housePendantApex.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring housePendantApexCol (by decide)) ?_
  have h := cliqueNum_le_chromNum housePendantApex
  rwa [cliqueNum_housePendantApex] at h

/-- A proper three-edge-colouring of `housePendantApex`, as a symmetric table on the vertices. -/
def housePendantApexEdgeCol : housePendantApex.V → housePendantApex.V → Fin 3 :=
  ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 0, 2, 0], ![0, 1, 0, 2, 0, 0], ![0, 0, 2, 0, 0, 0],
   ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `housePendantApex` is three.** -/
@[simp] theorem edgeChromNum_housePendantApex : housePendantApex.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := housePendantApex)
      housePendantApexEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum housePendantApex
    rwa [show housePendantApex.maxDeg = 3 from by decide] at h

/-- **The independence number of `housePendantRoof` is three.** -/
@[simp] theorem indepNum_housePendantRoof : housePendantRoof.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := housePendantRoof)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `housePendantRoof` is three.** -/
@[simp] theorem cliqueNum_housePendantRoof : housePendantRoof.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := housePendantRoof)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `housePendantRoof`. -/
def housePendantRoofCol : housePendantRoof.V → Fin 3 :=
  ![0, 1, 0, 1, 2, 0]

/-- **The chromatic number of `housePendantRoof` is three.** -/
@[simp] theorem chromNum_housePendantRoof : housePendantRoof.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring housePendantRoofCol (by decide)) ?_
  have h := cliqueNum_le_chromNum housePendantRoof
  rwa [cliqueNum_housePendantRoof] at h

/-- A proper four-edge-colouring of `housePendantRoof`, as a symmetric table on the vertices. -/
def housePendantRoofEdgeCol : housePendantRoof.V → housePendantRoof.V → Fin 4 :=
  ![![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 2, 3], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0],
   ![1, 2, 0, 3, 0, 0], ![0, 3, 0, 0, 0, 0]]

/-- **The edge chromatic number of `housePendantRoof` is four.** -/
@[simp] theorem edgeChromNum_housePendantRoof : housePendantRoof.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := housePendantRoof)
      housePendantRoofEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum housePendantRoof
    rwa [show housePendantRoof.maxDeg = 4 from by decide] at h

/-- **The independence number of `housePendantBase` is three.** -/
@[simp] theorem indepNum_housePendantBase : housePendantBase.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := housePendantBase)
    (l := ([0, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `housePendantBase` is three.** -/
@[simp] theorem cliqueNum_housePendantBase : housePendantBase.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := housePendantBase)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `housePendantBase`. -/
def housePendantBaseCol : housePendantBase.V → Fin 3 :=
  ![0, 1, 0, 1, 2, 1]

/-- **The chromatic number of `housePendantBase` is three.** -/
@[simp] theorem chromNum_housePendantBase : housePendantBase.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring housePendantBaseCol (by decide)) ?_
  have h := cliqueNum_le_chromNum housePendantBase
  rwa [cliqueNum_housePendantBase] at h

/-- A proper three-edge-colouring of `housePendantBase`, as a symmetric table on the vertices. -/
def housePendantBaseEdgeCol : housePendantBase.V → housePendantBase.V → Fin 3 :=
  ![![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 2, 0], ![0, 1, 0, 2, 0, 0], ![0, 0, 2, 0, 0, 0],
   ![1, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `housePendantBase` is three.** -/
@[simp] theorem edgeChromNum_housePendantBase : housePendantBase.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := housePendantBase)
      housePendantBaseEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum housePendantBase
    rwa [show housePendantBase.maxDeg = 3 from by decide] at h

/-- **The independence number of `diamondPendantsTips` is three.** -/
@[simp] theorem indepNum_diamondPendantsTips : diamondPendantsTips.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondPendantsTips)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondPendantsTips` is three.** -/
@[simp] theorem cliqueNum_diamondPendantsTips : diamondPendantsTips.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondPendantsTips)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondPendantsTips`. -/
def diamondPendantsTipsCol : diamondPendantsTips.V → Fin 3 :=
  ![0, 1, 2, 2, 0, 0]

/-- **The chromatic number of `diamondPendantsTips` is three.** -/
@[simp] theorem chromNum_diamondPendantsTips : diamondPendantsTips.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondPendantsTipsCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondPendantsTips
  rwa [cliqueNum_diamondPendantsTips] at h

/-- A proper three-edge-colouring of `diamondPendantsTips`, as a symmetric table on the
vertices. -/
def diamondPendantsTipsEdgeCol : diamondPendantsTips.V → diamondPendantsTips.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `diamondPendantsTips` is three.** -/
@[simp] theorem edgeChromNum_diamondPendantsTips : diamondPendantsTips.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondPendantsTips)
      diamondPendantsTipsEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondPendantsTips
    rwa [show diamondPendantsTips.maxDeg = 3 from by decide] at h

/-- **The independence number of `diamondPendantsHubs` is four.** -/
@[simp] theorem indepNum_diamondPendantsHubs : diamondPendantsHubs.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondPendantsHubs)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondPendantsHubs` is three.** -/
@[simp] theorem cliqueNum_diamondPendantsHubs : diamondPendantsHubs.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondPendantsHubs)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondPendantsHubs`. -/
def diamondPendantsHubsCol : diamondPendantsHubs.V → Fin 3 :=
  ![0, 1, 2, 2, 1, 0]

/-- **The chromatic number of `diamondPendantsHubs` is three.** -/
@[simp] theorem chromNum_diamondPendantsHubs : diamondPendantsHubs.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondPendantsHubsCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondPendantsHubs
  rwa [cliqueNum_diamondPendantsHubs] at h

/-- A proper four-edge-colouring of `diamondPendantsHubs`, as a symmetric table on the vertices. -/
def diamondPendantsHubsEdgeCol : diamondPendantsHubs.V → diamondPendantsHubs.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 1, 0, 3], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0]]

/-- **The edge chromatic number of `diamondPendantsHubs` is four.** -/
@[simp] theorem edgeChromNum_diamondPendantsHubs : diamondPendantsHubs.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondPendantsHubs)
      diamondPendantsHubsEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondPendantsHubs
    rwa [show diamondPendantsHubs.maxDeg = 4 from by decide] at h

/-- **The independence number of `diamondPendantsTipHub` is three.** -/
@[simp] theorem indepNum_diamondPendantsTipHub : diamondPendantsTipHub.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondPendantsTipHub)
    (l := ([1, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondPendantsTipHub` is three.** -/
@[simp] theorem cliqueNum_diamondPendantsTipHub : diamondPendantsTipHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondPendantsTipHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondPendantsTipHub`. -/
def diamondPendantsTipHubCol : diamondPendantsTipHub.V → Fin 3 :=
  ![0, 1, 2, 2, 0, 1]

/-- **The chromatic number of `diamondPendantsTipHub` is three.** -/
@[simp] theorem chromNum_diamondPendantsTipHub : diamondPendantsTipHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondPendantsTipHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondPendantsTipHub
  rwa [cliqueNum_diamondPendantsTipHub] at h

/-- A proper four-edge-colouring of `diamondPendantsTipHub`, as a symmetric table on the
vertices. -/
def diamondPendantsTipHubEdgeCol : diamondPendantsTipHub.V → diamondPendantsTipHub.V → Fin 4 :=
  ![![0, 0, 1, 2, 0, 3], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `diamondPendantsTipHub` is four.** -/
@[simp] theorem edgeChromNum_diamondPendantsTipHub : diamondPendantsTipHub.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondPendantsTipHub)
      diamondPendantsTipHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondPendantsTipHub
    rwa [show diamondPendantsTipHub.maxDeg = 4 from by decide] at h

/-- **The independence number of `diamondPendantsSameTip` is three.** -/
@[simp] theorem indepNum_diamondPendantsSameTip : diamondPendantsSameTip.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondPendantsSameTip)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondPendantsSameTip` is three.** -/
@[simp] theorem cliqueNum_diamondPendantsSameTip : diamondPendantsSameTip.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondPendantsSameTip)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondPendantsSameTip`. -/
def diamondPendantsSameTipCol : diamondPendantsSameTip.V → Fin 3 :=
  ![0, 1, 2, 2, 0, 0]

/-- **The chromatic number of `diamondPendantsSameTip` is three.** -/
@[simp] theorem chromNum_diamondPendantsSameTip : diamondPendantsSameTip.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondPendantsSameTipCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondPendantsSameTip
  rwa [cliqueNum_diamondPendantsSameTip] at h

/-- A proper four-edge-colouring of `diamondPendantsSameTip`, as a symmetric table on the
vertices. -/
def diamondPendantsSameTipEdgeCol : diamondPendantsSameTip.V → diamondPendantsSameTip.V → Fin 4 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 3], ![2, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0]]

/-- **The edge chromatic number of `diamondPendantsSameTip` is four.** -/
@[simp] theorem edgeChromNum_diamondPendantsSameTip : diamondPendantsSameTip.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondPendantsSameTip)
      diamondPendantsSameTipEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondPendantsSameTip
    rwa [show diamondPendantsSameTip.maxDeg = 4 from by decide] at h

/-- **The independence number of `diamondPendantsSameHub` is four.** -/
@[simp] theorem indepNum_diamondPendantsSameHub : diamondPendantsSameHub.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondPendantsSameHub)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondPendantsSameHub` is three.** -/
@[simp] theorem cliqueNum_diamondPendantsSameHub : diamondPendantsSameHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondPendantsSameHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondPendantsSameHub`. -/
def diamondPendantsSameHubCol : diamondPendantsSameHub.V → Fin 3 :=
  ![0, 1, 2, 2, 1, 1]

/-- **The chromatic number of `diamondPendantsSameHub` is three.** -/
@[simp] theorem chromNum_diamondPendantsSameHub : diamondPendantsSameHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondPendantsSameHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondPendantsSameHub
  rwa [cliqueNum_diamondPendantsSameHub] at h

/-- A proper five-edge-colouring of `diamondPendantsSameHub`, as a symmetric table on the
vertices. -/
def diamondPendantsSameHubEdgeCol : diamondPendantsSameHub.V → diamondPendantsSameHub.V → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `diamondPendantsSameHub` is five.** -/
@[simp] theorem edgeChromNum_diamondPendantsSameHub : diamondPendantsSameHub.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondPendantsSameHub)
      diamondPendantsSameHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondPendantsSameHub
    rwa [show diamondPendantsSameHub.maxDeg = 5 from by decide] at h

/-- **The independence number of `diamondTailTip` is three.** -/
@[simp] theorem indepNum_diamondTailTip : diamondTailTip.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondTailTip)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondTailTip` is three.** -/
@[simp] theorem cliqueNum_diamondTailTip : diamondTailTip.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondTailTip)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondTailTip`. -/
def diamondTailTipCol : diamondTailTip.V → Fin 3 :=
  ![0, 1, 2, 2, 0, 1]

/-- **The chromatic number of `diamondTailTip` is three.** -/
@[simp] theorem chromNum_diamondTailTip : diamondTailTip.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondTailTipCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondTailTip
  rwa [cliqueNum_diamondTailTip] at h

/-- A proper three-edge-colouring of `diamondTailTip`, as a symmetric table on the vertices. -/
def diamondTailTipEdgeCol : diamondTailTip.V → diamondTailTip.V → Fin 3 :=
  ![![0, 0, 1, 2, 0, 0], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]

/-- **The edge chromatic number of `diamondTailTip` is three.** -/
@[simp] theorem edgeChromNum_diamondTailTip : diamondTailTip.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondTailTip)
      diamondTailTipEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondTailTip
    rwa [show diamondTailTip.maxDeg = 3 from by decide] at h

/-- **The independence number of `diamondTailHub` is three.** -/
@[simp] theorem indepNum_diamondTailHub : diamondTailHub.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := diamondTailHub)
    (l := ([2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `diamondTailHub` is three.** -/
@[simp] theorem cliqueNum_diamondTailHub : diamondTailHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := diamondTailHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `diamondTailHub`. -/
def diamondTailHubCol : diamondTailHub.V → Fin 3 :=
  ![0, 1, 2, 2, 1, 0]

/-- **The chromatic number of `diamondTailHub` is three.** -/
@[simp] theorem chromNum_diamondTailHub : diamondTailHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring diamondTailHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum diamondTailHub
  rwa [cliqueNum_diamondTailHub] at h

/-- A proper four-edge-colouring of `diamondTailHub`, as a symmetric table on the vertices. -/
def diamondTailHubEdgeCol : diamondTailHub.V → diamondTailHub.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `diamondTailHub` is four.** -/
@[simp] theorem edgeChromNum_diamondTailHub : diamondTailHub.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := diamondTailHub)
      diamondTailHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum diamondTailHub
    rwa [show diamondTailHub.maxDeg = 4 from by decide] at h

/-- **The independence number of `k23PendantDeg3` is four.** -/
@[simp] theorem indepNum_k23PendantDeg3 : k23PendantDeg3.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := k23PendantDeg3)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `k23PendantDeg3` is two.** -/
@[simp] theorem cliqueNum_k23PendantDeg3 : k23PendantDeg3.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := k23PendantDeg3)
    (l := ([0, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `k23PendantDeg3`. -/
def k23PendantDeg3Col : k23PendantDeg3.V → Fin 2 :=
  ![0, 0, 1, 1, 1, 1]

/-- **The chromatic number of `k23PendantDeg3` is two.** -/
@[simp] theorem chromNum_k23PendantDeg3 : k23PendantDeg3.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring k23PendantDeg3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum k23PendantDeg3
  rwa [cliqueNum_k23PendantDeg3] at h

/-- A proper four-edge-colouring of `k23PendantDeg3`, as a symmetric table on the vertices. -/
def k23PendantDeg3EdgeCol : k23PendantDeg3.V → k23PendantDeg3.V → Fin 4 :=
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 0, 3, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 3, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `k23PendantDeg3` is four.** -/
@[simp] theorem edgeChromNum_k23PendantDeg3 : k23PendantDeg3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := k23PendantDeg3)
      k23PendantDeg3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum k23PendantDeg3
    rwa [show k23PendantDeg3.maxDeg = 4 from by decide] at h

/-- **The independence number of `k23PendantDeg2` is three.** -/
@[simp] theorem indepNum_k23PendantDeg2 : k23PendantDeg2.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := k23PendantDeg2)
    (l := ([0, 1, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `k23PendantDeg2` is two.** -/
@[simp] theorem cliqueNum_k23PendantDeg2 : k23PendantDeg2.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := k23PendantDeg2)
    (l := ([0, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `k23PendantDeg2`. -/
def k23PendantDeg2Col : k23PendantDeg2.V → Fin 2 :=
  ![0, 0, 1, 1, 1, 0]

/-- **The chromatic number of `k23PendantDeg2` is two.** -/
@[simp] theorem chromNum_k23PendantDeg2 : k23PendantDeg2.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring k23PendantDeg2Col (by decide)) ?_
  have h := cliqueNum_le_chromNum k23PendantDeg2
  rwa [cliqueNum_k23PendantDeg2] at h

/-- A proper three-edge-colouring of `k23PendantDeg2`, as a symmetric table on the vertices. -/
def k23PendantDeg2EdgeCol : k23PendantDeg2.V → k23PendantDeg2.V → Fin 3 :=
  ![![0, 0, 0, 1, 2, 0], ![0, 0, 1, 2, 0, 0], ![0, 1, 0, 0, 0, 2], ![1, 2, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0]]

/-- **The edge chromatic number of `k23PendantDeg2` is three.** -/
@[simp] theorem edgeChromNum_k23PendantDeg2 : k23PendantDeg2.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := k23PendantDeg2)
      k23PendantDeg2EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum k23PendantDeg2
    rwa [show k23PendantDeg2.maxDeg = 3 from by decide] at h

/-- **The independence number of `butterflyPendant` is three.** -/
@[simp] theorem indepNum_butterflyPendant : butterflyPendant.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := butterflyPendant)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `butterflyPendant` is three.** -/
@[simp] theorem cliqueNum_butterflyPendant : butterflyPendant.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := butterflyPendant)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `butterflyPendant`. -/
def butterflyPendantCol : butterflyPendant.V → Fin 3 :=
  ![0, 1, 2, 1, 2, 0]

/-- **The chromatic number of `butterflyPendant` is three.** -/
@[simp] theorem chromNum_butterflyPendant : butterflyPendant.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring butterflyPendantCol (by decide)) ?_
  have h := cliqueNum_le_chromNum butterflyPendant
  rwa [cliqueNum_butterflyPendant] at h

/-- A proper four-edge-colouring of `butterflyPendant`, as a symmetric table on the vertices. -/
def butterflyPendantEdgeCol : butterflyPendant.V → butterflyPendant.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 0, 0, 1], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]

/-- **The edge chromatic number of `butterflyPendant` is four.** -/
@[simp] theorem edgeChromNum_butterflyPendant : butterflyPendant.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := butterflyPendant)
      butterflyPendantEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum butterflyPendant
    rwa [show butterflyPendant.maxDeg = 4 from by decide] at h

/-- **The independence number of `butterflyPendantHub` is three.** -/
@[simp] theorem indepNum_butterflyPendantHub : butterflyPendantHub.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := butterflyPendantHub)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `butterflyPendantHub` is three.** -/
@[simp] theorem cliqueNum_butterflyPendantHub : butterflyPendantHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := butterflyPendantHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `butterflyPendantHub`. -/
def butterflyPendantHubCol : butterflyPendantHub.V → Fin 3 :=
  ![0, 1, 2, 1, 2, 1]

/-- **The chromatic number of `butterflyPendantHub` is three.** -/
@[simp] theorem chromNum_butterflyPendantHub : butterflyPendantHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring butterflyPendantHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum butterflyPendantHub
  rwa [cliqueNum_butterflyPendantHub] at h

/-- A proper five-edge-colouring of `butterflyPendantHub`, as a symmetric table on the vertices. -/
def butterflyPendantHubEdgeCol : butterflyPendantHub.V → butterflyPendantHub.V → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `butterflyPendantHub` is five.** -/
@[simp] theorem edgeChromNum_butterflyPendantHub : butterflyPendantHub.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := butterflyPendantHub)
      butterflyPendantHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum butterflyPendantHub
    rwa [show butterflyPendantHub.maxDeg = 5 from by decide] at h

/-- **The independence number of `prism3` is two.** -/
@[simp] theorem indepNum_prism3 : prism3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := prism3)
    (l := ([0, 3] : List (Fin 6)).map (FinEnum.equiv (α := prism3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `prism3` is three.** -/
@[simp] theorem cliqueNum_prism3 : prism3.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := prism3)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := prism3.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `prism3`. -/
def prism3Col : prism3.V → Fin 3 := fun v =>
  ![0, 1, 1, 2, 2, 0] (FinEnum.equiv v)

/-- **The chromatic number of `prism3` is three.** -/
@[simp] theorem chromNum_prism3 : prism3.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring prism3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum prism3
  rwa [cliqueNum_prism3] at h

/-- A proper three-edge-colouring of `prism3`, as a symmetric table on the vertices. -/
def prism3EdgeCol : prism3.V → prism3.V → Fin 3 := fun x y =>
  ![![0, 0, 1, 0, 2, 0], ![0, 0, 0, 1, 0, 2], ![1, 0, 0, 2, 0, 0], ![0, 1, 2, 0, 0, 0],
   ![2, 0, 0, 0, 0, 1], ![0, 2, 0, 0, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `prism3` is three.** -/
@[simp] theorem edgeChromNum_prism3 : prism3.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := prism3)
      prism3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum prism3
    rwa [show prism3.maxDeg = 3 from by decide] at h

/-- **The independence number of `sun3` is three.** -/
@[simp] theorem indepNum_sun3 : sun3.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := sun3)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `sun3` is three.** -/
@[simp] theorem cliqueNum_sun3 : sun3.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := sun3)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `sun3`. -/
def sun3Col : sun3.V → Fin 3 :=
  ![0, 1, 2, 0, 1, 2]

/-- **The chromatic number of `sun3` is three.** -/
@[simp] theorem chromNum_sun3 : sun3.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring sun3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum sun3
  rwa [cliqueNum_sun3] at h

/-- A proper four-edge-colouring of `sun3`, as a symmetric table on the vertices. -/
def sun3EdgeCol : sun3.V → sun3.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 2], ![0, 0, 0, 3, 1, 0], ![0, 1, 3, 0, 2, 0],
   ![0, 0, 1, 2, 0, 3], ![1, 2, 0, 0, 3, 0]]

/-- **The edge chromatic number of `sun3` is four.** -/
@[simp] theorem edgeChromNum_sun3 : sun3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := sun3)
      sun3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum sun3
    rwa [show sun3.maxDeg = 4 from by decide] at h

/-- **The independence number of `lollipop42` is two.** -/
@[simp] theorem indepNum_lollipop42 : lollipop42.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := lollipop42)
    (l := ([0, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `lollipop42` is four.** -/
@[simp] theorem cliqueNum_lollipop42 : lollipop42.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := lollipop42)
    (l := ([0, 1, 2, 3] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `lollipop42`. -/
def lollipop42Col : lollipop42.V → Fin 4 :=
  ![0, 1, 2, 3, 1, 0]

/-- **The chromatic number of `lollipop42` is four.** -/
@[simp] theorem chromNum_lollipop42 : lollipop42.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring lollipop42Col (by decide)) ?_
  have h := cliqueNum_le_chromNum lollipop42
  rwa [cliqueNum_lollipop42] at h

/-- A proper four-edge-colouring of `lollipop42`, as a symmetric table on the vertices. -/
def lollipop42EdgeCol : lollipop42.V → lollipop42.V → Fin 4 :=
  ![![0, 0, 1, 2, 3, 0], ![0, 0, 2, 1, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `lollipop42` is four.** -/
@[simp] theorem edgeChromNum_lollipop42 : lollipop42.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := lollipop42)
      lollipop42EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum lollipop42
    rwa [show lollipop42.maxDeg = 4 from by decide] at h

/-- **The independence number of `coP6` is two.** -/
@[simp] theorem indepNum_coP6 : coP6.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coP6)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coP6` is three.** -/
@[simp] theorem cliqueNum_coP6 : coP6.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coP6)
    (l := ([0, 2, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coP6`. -/
def coP6Col : coP6.V → Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

/-- **The chromatic number of `coP6` is three.** -/
@[simp] theorem chromNum_coP6 : coP6.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coP6Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coP6
  rwa [cliqueNum_coP6] at h

/-- A proper four-edge-colouring of `coP6`, as a symmetric table on the vertices. -/
def coP6EdgeCol : coP6.V → coP6.V → Fin 4 :=
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 2, 0, 1], ![0, 0, 0, 0, 1, 2], ![1, 2, 0, 0, 0, 0],
   ![2, 0, 1, 0, 0, 0], ![3, 1, 2, 0, 0, 0]]

/-- **The edge chromatic number of `coP6` is four.** -/
@[simp] theorem edgeChromNum_coP6 : coP6.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coP6)
      coP6EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coP6
    rwa [show coP6.maxDeg = 4 from by decide] at h

/-- **The independence number of `coSpider113` is two.** -/
@[simp] theorem indepNum_coSpider113 : coSpider113.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coSpider113)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coSpider113` is four.** -/
@[simp] theorem cliqueNum_coSpider113 : coSpider113.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coSpider113)
    (l := ([1, 2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coSpider113`. -/
def coSpider113Col : coSpider113.V → Fin 4 :=
  ![0, 0, 1, 2, 2, 3]

/-- **The chromatic number of `coSpider113` is four.** -/
@[simp] theorem chromNum_coSpider113 : coSpider113.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coSpider113Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coSpider113
  rwa [cliqueNum_coSpider113] at h

/-- A proper four-edge-colouring of `coSpider113`, as a symmetric table on the vertices. -/
def coSpider113EdgeCol : coSpider113.V → coSpider113.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 2, 3], ![0, 0, 0, 3, 1, 2], ![0, 1, 3, 0, 0, 0],
   ![0, 2, 1, 0, 0, 0], ![1, 3, 2, 0, 0, 0]]

/-- **The edge chromatic number of `coSpider113` is four.** -/
@[simp] theorem edgeChromNum_coSpider113 : coSpider113.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coSpider113)
      coSpider113EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coSpider113
    rwa [show coSpider113.maxDeg = 4 from by decide] at h

/-- **The independence number of `coSpider122` is two.** -/
@[simp] theorem indepNum_coSpider122 : coSpider122.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coSpider122)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coSpider122` is three.** -/
@[simp] theorem cliqueNum_coSpider122 : coSpider122.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coSpider122)
    (l := ([0, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coSpider122`. -/
def coSpider122Col : coSpider122.V → Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

/-- **The chromatic number of `coSpider122` is three.** -/
@[simp] theorem chromNum_coSpider122 : coSpider122.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coSpider122Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coSpider122
  rwa [cliqueNum_coSpider122] at h

/-- A proper four-edge-colouring of `coSpider122`, as a symmetric table on the vertices. -/
def coSpider122EdgeCol : coSpider122.V → coSpider122.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 2, 3, 0], ![0, 1, 0, 0, 0, 2], ![0, 2, 0, 0, 1, 3],
   ![0, 3, 0, 1, 0, 0], ![1, 0, 2, 3, 0, 0]]

/-- **The edge chromatic number of `coSpider122` is four.** -/
@[simp] theorem edgeChromNum_coSpider122 : coSpider122.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coSpider122)
      coSpider122EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coSpider122
    rwa [show coSpider122.maxDeg = 4 from by decide] at h

/-- **The independence number of `coCross` is two.** -/
@[simp] theorem indepNum_coCross : coCross.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coCross)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coCross` is four.** -/
@[simp] theorem cliqueNum_coCross : coCross.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coCross)
    (l := ([1, 2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coCross`. -/
def coCrossCol : coCross.V → Fin 4 :=
  ![0, 0, 1, 2, 3, 3]

/-- **The chromatic number of `coCross` is four.** -/
@[simp] theorem chromNum_coCross : coCross.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coCrossCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coCross
  rwa [cliqueNum_coCross] at h

/-- A proper five-edge-colouring of `coCross`, as a symmetric table on the vertices. -/
def coCrossEdgeCol : coCross.V → coCross.V → Fin 5 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 2, 3], ![0, 0, 0, 2, 3, 1], ![0, 1, 2, 0, 0, 4],
   ![0, 2, 3, 0, 0, 0], ![0, 3, 1, 4, 0, 0]]

/-- **The edge chromatic number of `coCross` is five.** -/
@[simp] theorem edgeChromNum_coCross : coCross.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coCross)
      coCrossEdgeCol (by decide) (by decide)
  · have h : 4 < coCross.edgeChromNum := by graph_sat
    omega

/-- **The independence number of `coH` is two.** -/
@[simp] theorem indepNum_coH : coH.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coH)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coH` is four.** -/
@[simp] theorem cliqueNum_coH : coH.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coH)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coH`. -/
def coHCol : coH.V → Fin 4 :=
  ![0, 1, 0, 2, 1, 3]

/-- **The chromatic number of `coH` is four.** -/
@[simp] theorem chromNum_coH : coH.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coHCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coH
  rwa [cliqueNum_coH] at h

/-- A proper four-edge-colouring of `coH`, as a symmetric table on the vertices. -/
def coHEdgeCol : coH.V → coH.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 1, 3], ![0, 1, 2, 0, 3, 0],
   ![0, 0, 1, 3, 0, 2], ![1, 0, 3, 0, 2, 0]]

/-- **The edge chromatic number of `coH` is four.** -/
@[simp] theorem edgeChromNum_coH : coH.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coH)
      coHEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coH
    rwa [show coH.maxDeg = 4 from by decide] at h

/-- **The independence number of `coTadpole33` is three.** -/
@[simp] theorem indepNum_coTadpole33 : coTadpole33.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coTadpole33)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coTadpole33` is three.** -/
@[simp] theorem cliqueNum_coTadpole33 : coTadpole33.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coTadpole33)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coTadpole33`. -/
def coTadpole33Col : coTadpole33.V → Fin 3 :=
  ![0, 0, 0, 1, 1, 2]

/-- **The chromatic number of `coTadpole33` is three.** -/
@[simp] theorem chromNum_coTadpole33 : coTadpole33.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coTadpole33Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coTadpole33
  rwa [cliqueNum_coTadpole33] at h

/-- A proper four-edge-colouring of `coTadpole33`, as a symmetric table on the vertices. -/
def coTadpole33EdgeCol : coTadpole33.V → coTadpole33.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 3],
   ![0, 1, 2, 0, 0, 0], ![1, 2, 0, 3, 0, 0]]

/-- **The edge chromatic number of `coTadpole33` is four.** -/
@[simp] theorem edgeChromNum_coTadpole33 : coTadpole33.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coTadpole33)
      coTadpole33EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coTadpole33
    rwa [show coTadpole33.maxDeg = 4 from by decide] at h

/-- **The independence number of `coTadpole42` is two.** -/
@[simp] theorem indepNum_coTadpole42 : coTadpole42.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coTadpole42)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coTadpole42` is three.** -/
@[simp] theorem cliqueNum_coTadpole42 : coTadpole42.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coTadpole42)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coTadpole42`. -/
def coTadpole42Col : coTadpole42.V → Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

/-- **The chromatic number of `coTadpole42` is three.** -/
@[simp] theorem chromNum_coTadpole42 : coTadpole42.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coTadpole42Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coTadpole42
  rwa [cliqueNum_coTadpole42] at h

/-- A proper four-edge-colouring of `coTadpole42`, as a symmetric table on the vertices. -/
def coTadpole42EdgeCol : coTadpole42.V → coTadpole42.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 2], ![0, 0, 0, 0, 1, 3], ![0, 1, 0, 0, 2, 0],
   ![0, 0, 1, 2, 0, 0], ![1, 2, 3, 0, 0, 0]]

/-- **The edge chromatic number of `coTadpole42` is four.** -/
@[simp] theorem edgeChromNum_coTadpole42 : coTadpole42.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coTadpole42)
      coTadpole42EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coTadpole42
    rwa [show coTadpole42.maxDeg = 4 from by decide] at h

/-- **The independence number of `coTadpole51` is two.** -/
@[simp] theorem indepNum_coTadpole51 : coTadpole51.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coTadpole51)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coTadpole51` is three.** -/
@[simp] theorem cliqueNum_coTadpole51 : coTadpole51.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coTadpole51)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coTadpole51`. -/
def coTadpole51Col : coTadpole51.V → Fin 3 :=
  ![0, 1, 1, 2, 2, 0]

/-- **The chromatic number of `coTadpole51` is three.** -/
@[simp] theorem chromNum_coTadpole51 : coTadpole51.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coTadpole51Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coTadpole51
  rwa [cliqueNum_coTadpole51] at h

/-- A proper four-edge-colouring of `coTadpole51`, as a symmetric table on the vertices. -/
def coTadpole51EdgeCol : coTadpole51.V → coTadpole51.V → Fin 4 :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 1], ![1, 0, 0, 0, 0, 3],
   ![0, 1, 2, 0, 0, 0], ![0, 2, 1, 3, 0, 0]]

/-- **The edge chromatic number of `coTadpole51` is four.** -/
@[simp] theorem edgeChromNum_coTadpole51 : coTadpole51.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coTadpole51)
      coTadpole51EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coTadpole51
    rwa [show coTadpole51.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC3Pendants210` is three.** -/
@[simp] theorem indepNum_coC3Pendants210 : coC3Pendants210.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC3Pendants210)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC3Pendants210` is four.** -/
@[simp] theorem cliqueNum_coC3Pendants210 : coC3Pendants210.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC3Pendants210)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coC3Pendants210`. -/
def coC3Pendants210Col : coC3Pendants210.V → Fin 4 :=
  ![0, 0, 0, 1, 2, 3]

/-- **The chromatic number of `coC3Pendants210` is four.** -/
@[simp] theorem chromNum_coC3Pendants210 : coC3Pendants210.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coC3Pendants210Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coC3Pendants210
  rwa [cliqueNum_coC3Pendants210] at h

/-- A proper four-edge-colouring of `coC3Pendants210`, as a symmetric table on the vertices. -/
def coC3Pendants210EdgeCol : coC3Pendants210.V → coC3Pendants210.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 2, 0, 3], ![0, 0, 2, 0, 3, 1],
   ![0, 1, 0, 3, 0, 2], ![0, 0, 3, 1, 2, 0]]

/-- **The edge chromatic number of `coC3Pendants210` is four.** -/
@[simp] theorem edgeChromNum_coC3Pendants210 : coC3Pendants210.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC3Pendants210)
      coC3Pendants210EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC3Pendants210
    rwa [show coC3Pendants210.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC3Legs12` is three.** -/
@[simp] theorem indepNum_coC3Legs12 : coC3Legs12.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC3Legs12)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC3Legs12` is three.** -/
@[simp] theorem cliqueNum_coC3Legs12 : coC3Legs12.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC3Legs12)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coC3Legs12`. -/
def coC3Legs12Col : coC3Legs12.V → Fin 3 :=
  ![0, 0, 0, 1, 2, 2]

/-- **The chromatic number of `coC3Legs12` is three.** -/
@[simp] theorem chromNum_coC3Legs12 : coC3Legs12.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coC3Legs12Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coC3Legs12
  rwa [cliqueNum_coC3Legs12] at h

/-- A proper four-edge-colouring of `coC3Legs12`, as a symmetric table on the vertices. -/
def coC3Legs12EdgeCol : coC3Legs12.V → coC3Legs12.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 1, 3, 0], ![0, 0, 1, 0, 2, 3],
   ![0, 0, 3, 2, 0, 0], ![1, 2, 0, 3, 0, 0]]

/-- **The edge chromatic number of `coC3Legs12` is four.** -/
@[simp] theorem edgeChromNum_coC3Legs12 : coC3Legs12.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC3Legs12)
      coC3Legs12EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC3Legs12
    rwa [show coC3Legs12.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC3Legs12Same` is three.** -/
@[simp] theorem indepNum_coC3Legs12Same : coC3Legs12Same.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC3Legs12Same)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC3Legs12Same` is three.** -/
@[simp] theorem cliqueNum_coC3Legs12Same : coC3Legs12Same.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC3Legs12Same)
    (l := ([1, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coC3Legs12Same`. -/
def coC3Legs12SameCol : coC3Legs12Same.V → Fin 3 :=
  ![0, 0, 0, 1, 2, 2]

/-- **The chromatic number of `coC3Legs12Same` is three.** -/
@[simp] theorem chromNum_coC3Legs12Same : coC3Legs12Same.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coC3Legs12SameCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coC3Legs12Same
  rwa [cliqueNum_coC3Legs12Same] at h

/-- A proper four-edge-colouring of `coC3Legs12Same`, as a symmetric table on the vertices. -/
def coC3Legs12SameEdgeCol : coC3Legs12Same.V → coC3Legs12Same.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 2, 0, 3], ![0, 0, 2, 0, 3, 1],
   ![0, 1, 0, 3, 0, 0], ![0, 2, 3, 1, 0, 0]]

/-- **The edge chromatic number of `coC3Legs12Same` is four.** -/
@[simp] theorem edgeChromNum_coC3Legs12Same : coC3Legs12Same.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC3Legs12Same)
      coC3Legs12SameEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC3Legs12Same
    rwa [show coC3Legs12Same.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC3Fork` is three.** -/
@[simp] theorem indepNum_coC3Fork : coC3Fork.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC3Fork)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC3Fork` is three.** -/
@[simp] theorem cliqueNum_coC3Fork : coC3Fork.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC3Fork)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coC3Fork`. -/
def coC3ForkCol : coC3Fork.V → Fin 3 :=
  ![0, 0, 0, 1, 1, 2]

/-- **The chromatic number of `coC3Fork` is three.** -/
@[simp] theorem chromNum_coC3Fork : coC3Fork.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coC3ForkCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coC3Fork
  rwa [cliqueNum_coC3Fork] at h

/-- A proper four-edge-colouring of `coC3Fork`, as a symmetric table on the vertices. -/
def coC3ForkEdgeCol : coC3Fork.V → coC3Fork.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 0],
   ![0, 1, 2, 0, 0, 3], ![1, 2, 0, 0, 3, 0]]

/-- **The edge chromatic number of `coC3Fork` is four.** -/
@[simp] theorem edgeChromNum_coC3Fork : coC3Fork.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC3Fork)
      coC3ForkEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC3Fork
    rwa [show coC3Fork.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC4Pendants1010` is two.** -/
@[simp] theorem indepNum_coC4Pendants1010 : coC4Pendants1010.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC4Pendants1010)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC4Pendants1010` is four.** -/
@[simp] theorem cliqueNum_coC4Pendants1010 : coC4Pendants1010.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC4Pendants1010)
    (l := ([1, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coC4Pendants1010`. -/
def coC4Pendants1010Col : coC4Pendants1010.V → Fin 4 :=
  ![0, 0, 1, 1, 2, 3]

/-- **The chromatic number of `coC4Pendants1010` is four.** -/
@[simp] theorem chromNum_coC4Pendants1010 : coC4Pendants1010.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coC4Pendants1010Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coC4Pendants1010
  rwa [cliqueNum_coC4Pendants1010] at h

/-- A proper four-edge-colouring of `coC4Pendants1010`, as a symmetric table on the vertices. -/
def coC4Pendants1010EdgeCol : coC4Pendants1010.V → coC4Pendants1010.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 2, 3],
   ![0, 1, 3, 2, 0, 0], ![1, 2, 0, 3, 0, 0]]

/-- **The edge chromatic number of `coC4Pendants1010` is four.** -/
@[simp] theorem edgeChromNum_coC4Pendants1010 : coC4Pendants1010.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC4Pendants1010)
      coC4Pendants1010EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC4Pendants1010
    rwa [show coC4Pendants1010.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC4Pendants1100` is two.** -/
@[simp] theorem indepNum_coC4Pendants1100 : coC4Pendants1100.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC4Pendants1100)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC4Pendants1100` is three.** -/
@[simp] theorem cliqueNum_coC4Pendants1100 : coC4Pendants1100.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC4Pendants1100)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coC4Pendants1100`. -/
def coC4Pendants1100Col : coC4Pendants1100.V → Fin 3 :=
  ![0, 1, 2, 2, 0, 1]

/-- **The chromatic number of `coC4Pendants1100` is three.** -/
@[simp] theorem chromNum_coC4Pendants1100 : coC4Pendants1100.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coC4Pendants1100Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coC4Pendants1100
  rwa [cliqueNum_coC4Pendants1100] at h

/-- A proper four-edge-colouring of `coC4Pendants1100`, as a symmetric table on the vertices. -/
def coC4Pendants1100EdgeCol : coC4Pendants1100.V → coC4Pendants1100.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 3, 2],
   ![0, 1, 2, 3, 0, 0], ![1, 0, 3, 2, 0, 0]]

/-- **The edge chromatic number of `coC4Pendants1100` is four.** -/
@[simp] theorem edgeChromNum_coC4Pendants1100 : coC4Pendants1100.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC4Pendants1100)
      coC4Pendants1100EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC4Pendants1100
    rwa [show coC4Pendants1100.maxDeg = 4 from by decide] at h

/-- **The independence number of `coC4Pendants2000` is two.** -/
@[simp] theorem indepNum_coC4Pendants2000 : coC4Pendants2000.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coC4Pendants2000)
    (l := ([0, 1] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coC4Pendants2000` is four.** -/
@[simp] theorem cliqueNum_coC4Pendants2000 : coC4Pendants2000.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coC4Pendants2000)
    (l := ([1, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coC4Pendants2000`. -/
def coC4Pendants2000Col : coC4Pendants2000.V → Fin 4 :=
  ![0, 0, 1, 1, 2, 3]

/-- **The chromatic number of `coC4Pendants2000` is four.** -/
@[simp] theorem chromNum_coC4Pendants2000 : coC4Pendants2000.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coC4Pendants2000Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coC4Pendants2000
  rwa [cliqueNum_coC4Pendants2000] at h

/-- A proper four-edge-colouring of `coC4Pendants2000`, as a symmetric table on the vertices. -/
def coC4Pendants2000EdgeCol : coC4Pendants2000.V → coC4Pendants2000.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 3, 1],
   ![0, 1, 2, 3, 0, 0], ![0, 2, 3, 1, 0, 0]]

/-- **The edge chromatic number of `coC4Pendants2000` is four.** -/
@[simp] theorem edgeChromNum_coC4Pendants2000 : coC4Pendants2000.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coC4Pendants2000)
      coC4Pendants2000EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coC4Pendants2000
    rwa [show coC4Pendants2000.maxDeg = 4 from by decide] at h

/-- **The independence number of `coTheta223` is two.** -/
@[simp] theorem indepNum_coTheta223 : coTheta223.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coTheta223)
    (l := ([0, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coTheta223` is three.** -/
@[simp] theorem cliqueNum_coTheta223 : coTheta223.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coTheta223)
    (l := ([2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coTheta223`. -/
def coTheta223Col : coTheta223.V → Fin 3 :=
  ![0, 1, 0, 1, 2, 2]

/-- **The chromatic number of `coTheta223` is three.** -/
@[simp] theorem chromNum_coTheta223 : coTheta223.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coTheta223Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coTheta223
  rwa [cliqueNum_coTheta223] at h

/-- A proper three-edge-colouring of `coTheta223`, as a symmetric table on the vertices. -/
def coTheta223EdgeCol : coTheta223.V → coTheta223.V → Fin 3 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 2], ![0, 0, 1, 0, 2, 0],
   ![0, 1, 0, 2, 0, 0], ![1, 0, 2, 0, 0, 0]]

/-- **The edge chromatic number of `coTheta223` is three.** -/
@[simp] theorem edgeChromNum_coTheta223 : coTheta223.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coTheta223)
      coTheta223EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coTheta223
    rwa [show coTheta223.maxDeg = 3 from by decide] at h

/-- **The independence number of `coTheta124` is three.** -/
@[simp] theorem indepNum_coTheta124 : coTheta124.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coTheta124)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coTheta124` is three.** -/
@[simp] theorem cliqueNum_coTheta124 : coTheta124.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coTheta124)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coTheta124`. -/
def coTheta124Col : coTheta124.V → Fin 3 :=
  ![0, 0, 0, 1, 1, 2]

/-- **The chromatic number of `coTheta124` is three.** -/
@[simp] theorem chromNum_coTheta124 : coTheta124.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coTheta124Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coTheta124
  rwa [cliqueNum_coTheta124] at h

/-- A proper three-edge-colouring of `coTheta124`, as a symmetric table on the vertices. -/
def coTheta124EdgeCol : coTheta124.V → coTheta124.V → Fin 3 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 2],
   ![0, 1, 2, 0, 0, 0], ![1, 0, 0, 2, 0, 0]]

/-- **The edge chromatic number of `coTheta124` is three.** -/
@[simp] theorem edgeChromNum_coTheta124 : coTheta124.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coTheta124)
      coTheta124EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coTheta124
    rwa [show coTheta124.maxDeg = 3 from by decide] at h

/-- **The independence number of `coDomino` is two.** -/
@[simp] theorem indepNum_coDomino : coDomino.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDomino)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := coDomino.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coDomino` is three.** -/
@[simp] theorem cliqueNum_coDomino : coDomino.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDomino)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := coDomino.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coDomino`. -/
def coDominoCol : coDomino.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coDomino` is three.** -/
@[simp] theorem chromNum_coDomino : coDomino.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDominoCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDomino
  rwa [cliqueNum_coDomino] at h

/-- A proper three-edge-colouring of `coDomino`, as a symmetric table on the vertices. -/
def coDominoEdgeCol : coDomino.V → coDomino.V → Fin 3 := fun x y =>
  ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 2, 1], ![0, 1, 0, 0, 0, 2],
   ![1, 0, 2, 0, 0, 0], ![0, 0, 1, 2, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coDomino` is three.** -/
@[simp] theorem edgeChromNum_coDomino : coDomino.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDomino)
      coDominoEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDomino
    rwa [show coDomino.maxDeg = 3 from by decide] at h

/-- **The independence number of `coBarbell` is three.** -/
@[simp] theorem indepNum_coBarbell : coBarbell.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coBarbell)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coBarbell` is two.** -/
@[simp] theorem cliqueNum_coBarbell : coBarbell.cliqueNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coBarbell)
    (l := ([0, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper two-colouring of `coBarbell`. -/
def coBarbellCol : coBarbell.V → Fin 2 :=
  ![0, 0, 0, 1, 1, 1]

/-- **The chromatic number of `coBarbell` is two.** -/
@[simp] theorem chromNum_coBarbell : coBarbell.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring coBarbellCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coBarbell
  rwa [cliqueNum_coBarbell] at h

/-- A proper three-edge-colouring of `coBarbell`, as a symmetric table on the vertices. -/
def coBarbellEdgeCol : coBarbell.V → coBarbell.V → Fin 3 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 0],
   ![0, 1, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0]]

/-- **The edge chromatic number of `coBarbell` is three.** -/
@[simp] theorem edgeChromNum_coBarbell : coBarbell.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coBarbell)
      coBarbellEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coBarbell
    rwa [show coBarbell.maxDeg = 3 from by decide] at h

/-- **The independence number of `coFish` is three.** -/
@[simp] theorem indepNum_coFish : coFish.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coFish)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := coFish.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coFish` is three.** -/
@[simp] theorem cliqueNum_coFish : coFish.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coFish)
    (l := ([1, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := coFish.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coFish`. -/
def coFishCol : coFish.V → Fin 3 := fun v =>
  ![0, 0, 0, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coFish` is three.** -/
@[simp] theorem chromNum_coFish : coFish.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coFishCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coFish
  rwa [cliqueNum_coFish] at h

/-- A proper four-edge-colouring of `coFish`, as a symmetric table on the vertices. -/
def coFishEdgeCol : coFish.V → coFish.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 3],
   ![0, 1, 2, 0, 0, 0], ![0, 2, 0, 3, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coFish` is four.** -/
@[simp] theorem edgeChromNum_coFish : coFish.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coFish)
      coFishEdgeCol (by decide) (by decide)
  · have h : 3 < coFish.edgeChromNum := by graph_sat
    omega

/-- **The independence number of `coHousePendantApex` is three.** -/
@[simp] theorem indepNum_coHousePendantApex : coHousePendantApex.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coHousePendantApex)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coHousePendantApex` is three.** -/
@[simp] theorem cliqueNum_coHousePendantApex : coHousePendantApex.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coHousePendantApex)
    (l := ([1, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coHousePendantApex`. -/
def coHousePendantApexCol : coHousePendantApex.V → Fin 3 :=
  ![0, 0, 1, 1, 0, 2]

/-- **The chromatic number of `coHousePendantApex` is three.** -/
@[simp] theorem chromNum_coHousePendantApex : coHousePendantApex.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coHousePendantApexCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coHousePendantApex
  rwa [cliqueNum_coHousePendantApex] at h

/-- A proper four-edge-colouring of `coHousePendantApex`, as a symmetric table on the vertices. -/
def coHousePendantApexEdgeCol : coHousePendantApex.V → coHousePendantApex.V → Fin 4 :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![1, 0, 0, 0, 0, 3],
   ![0, 0, 1, 0, 0, 0], ![0, 1, 2, 3, 0, 0]]

/-- **The edge chromatic number of `coHousePendantApex` is four.** -/
@[simp] theorem edgeChromNum_coHousePendantApex : coHousePendantApex.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coHousePendantApex)
      coHousePendantApexEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coHousePendantApex
    rwa [show coHousePendantApex.maxDeg = 4 from by decide] at h

/-- **The independence number of `coHousePendantRoof` is three.** -/
@[simp] theorem indepNum_coHousePendantRoof : coHousePendantRoof.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coHousePendantRoof)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coHousePendantRoof` is three.** -/
@[simp] theorem cliqueNum_coHousePendantRoof : coHousePendantRoof.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coHousePendantRoof)
    (l := ([0, 2, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coHousePendantRoof`. -/
def coHousePendantRoofCol : coHousePendantRoof.V → Fin 3 :=
  ![0, 0, 1, 1, 0, 2]

/-- **The chromatic number of `coHousePendantRoof` is three.** -/
@[simp] theorem chromNum_coHousePendantRoof : coHousePendantRoof.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coHousePendantRoofCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coHousePendantRoof
  rwa [cliqueNum_coHousePendantRoof] at h

/-- A proper four-edge-colouring of `coHousePendantRoof`, as a symmetric table on the vertices. -/
def coHousePendantRoofEdgeCol : coHousePendantRoof.V → coHousePendantRoof.V → Fin 4 :=
  ![![0, 0, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 1], ![1, 0, 0, 0, 0, 3],
   ![0, 0, 2, 0, 0, 0], ![2, 0, 1, 3, 0, 0]]

/-- **The edge chromatic number of `coHousePendantRoof` is four.** -/
@[simp] theorem edgeChromNum_coHousePendantRoof : coHousePendantRoof.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coHousePendantRoof)
      coHousePendantRoofEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coHousePendantRoof
    rwa [show coHousePendantRoof.maxDeg = 4 from by decide] at h

/-- **The independence number of `coHousePendantBase` is three.** -/
@[simp] theorem indepNum_coHousePendantBase : coHousePendantBase.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coHousePendantBase)
    (l := ([0, 1, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coHousePendantBase` is three.** -/
@[simp] theorem cliqueNum_coHousePendantBase : coHousePendantBase.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coHousePendantBase)
    (l := ([0, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coHousePendantBase`. -/
def coHousePendantBaseCol : coHousePendantBase.V → Fin 3 :=
  ![0, 0, 1, 1, 0, 2]

/-- **The chromatic number of `coHousePendantBase` is three.** -/
@[simp] theorem chromNum_coHousePendantBase : coHousePendantBase.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coHousePendantBaseCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coHousePendantBase
  rwa [cliqueNum_coHousePendantBase] at h

/-- A proper four-edge-colouring of `coHousePendantBase`, as a symmetric table on the vertices. -/
def coHousePendantBaseEdgeCol : coHousePendantBase.V → coHousePendantBase.V → Fin 4 :=
  ![![0, 0, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 3],
   ![0, 0, 1, 0, 0, 0], ![2, 1, 0, 3, 0, 0]]

/-- **The edge chromatic number of `coHousePendantBase` is four.** -/
@[simp] theorem edgeChromNum_coHousePendantBase : coHousePendantBase.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coHousePendantBase)
      coHousePendantBaseEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coHousePendantBase
    rwa [show coHousePendantBase.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondPendantsTips` is three.** -/
@[simp] theorem indepNum_coDiamondPendantsTips : coDiamondPendantsTips.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondPendantsTips)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondPendantsTips` is three.** -/
@[simp] theorem cliqueNum_coDiamondPendantsTips : coDiamondPendantsTips.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondPendantsTips)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coDiamondPendantsTips`. -/
def coDiamondPendantsTipsCol : coDiamondPendantsTips.V → Fin 3 :=
  ![0, 0, 0, 1, 2, 1]

/-- **The chromatic number of `coDiamondPendantsTips` is three.** -/
@[simp] theorem chromNum_coDiamondPendantsTips : coDiamondPendantsTips.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondPendantsTipsCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondPendantsTips
  rwa [cliqueNum_coDiamondPendantsTips] at h

/-- A proper four-edge-colouring of `coDiamondPendantsTips`, as a symmetric table on the
vertices. -/
def coDiamondPendantsTipsEdgeCol : coDiamondPendantsTips.V → coDiamondPendantsTips.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 2, 0],
   ![0, 1, 0, 2, 0, 3], ![1, 0, 2, 0, 3, 0]]

/-- **The edge chromatic number of `coDiamondPendantsTips` is four.** -/
@[simp] theorem edgeChromNum_coDiamondPendantsTips : coDiamondPendantsTips.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondPendantsTips)
      coDiamondPendantsTipsEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondPendantsTips
    rwa [show coDiamondPendantsTips.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondPendantsHubs` is three.** -/
@[simp] theorem indepNum_coDiamondPendantsHubs : coDiamondPendantsHubs.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondPendantsHubs)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondPendantsHubs` is four.** -/
@[simp] theorem cliqueNum_coDiamondPendantsHubs : coDiamondPendantsHubs.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondPendantsHubs)
    (l := ([2, 3, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper four-colouring of `coDiamondPendantsHubs`. -/
def coDiamondPendantsHubsCol : coDiamondPendantsHubs.V → Fin 4 :=
  ![0, 0, 0, 1, 2, 3]

/-- **The chromatic number of `coDiamondPendantsHubs` is four.** -/
@[simp] theorem chromNum_coDiamondPendantsHubs : coDiamondPendantsHubs.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondPendantsHubsCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondPendantsHubs
  rwa [cliqueNum_coDiamondPendantsHubs] at h

/-- A proper four-edge-colouring of `coDiamondPendantsHubs`, as a symmetric table on the
vertices. -/
def coDiamondPendantsHubsEdgeCol : coDiamondPendantsHubs.V → coDiamondPendantsHubs.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 1],
   ![0, 0, 1, 2, 0, 3], ![0, 0, 2, 1, 3, 0]]

/-- **The edge chromatic number of `coDiamondPendantsHubs` is four.** -/
@[simp] theorem edgeChromNum_coDiamondPendantsHubs : coDiamondPendantsHubs.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondPendantsHubs)
      coDiamondPendantsHubsEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondPendantsHubs
    rwa [show coDiamondPendantsHubs.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondPendantsTipHub` is three.** -/
@[simp] theorem indepNum_coDiamondPendantsTipHub : coDiamondPendantsTipHub.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondPendantsTipHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondPendantsTipHub` is three.** -/
@[simp] theorem cliqueNum_coDiamondPendantsTipHub : coDiamondPendantsTipHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondPendantsTipHub)
    (l := ([1, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coDiamondPendantsTipHub`. -/
def coDiamondPendantsTipHubCol : coDiamondPendantsTipHub.V → Fin 3 :=
  ![0, 0, 1, 0, 1, 2]

/-- **The chromatic number of `coDiamondPendantsTipHub` is three.** -/
@[simp] theorem chromNum_coDiamondPendantsTipHub : coDiamondPendantsTipHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondPendantsTipHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondPendantsTipHub
  rwa [cliqueNum_coDiamondPendantsTipHub] at h

/-- A proper four-edge-colouring of `coDiamondPendantsTipHub`, as a symmetric table on the
vertices. -/
def coDiamondPendantsTipHubEdgeCol :
    coDiamondPendantsTipHub.V → coDiamondPendantsTipHub.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 2, 1],
   ![0, 1, 0, 2, 0, 3], ![0, 0, 2, 1, 3, 0]]

/-- **The edge chromatic number of `coDiamondPendantsTipHub` is four.** -/
@[simp] theorem edgeChromNum_coDiamondPendantsTipHub :
    coDiamondPendantsTipHub.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondPendantsTipHub)
      coDiamondPendantsTipHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondPendantsTipHub
    rwa [show coDiamondPendantsTipHub.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondPendantsSameTip` is three.** -/
@[simp] theorem indepNum_coDiamondPendantsSameTip : coDiamondPendantsSameTip.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondPendantsSameTip)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondPendantsSameTip` is three.** -/
@[simp] theorem cliqueNum_coDiamondPendantsSameTip : coDiamondPendantsSameTip.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondPendantsSameTip)
    (l := ([0, 4, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coDiamondPendantsSameTip`. -/
def coDiamondPendantsSameTipCol : coDiamondPendantsSameTip.V → Fin 3 :=
  ![0, 0, 1, 0, 1, 2]

/-- **The chromatic number of `coDiamondPendantsSameTip` is three.** -/
@[simp] theorem chromNum_coDiamondPendantsSameTip : coDiamondPendantsSameTip.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondPendantsSameTipCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondPendantsSameTip
  rwa [cliqueNum_coDiamondPendantsSameTip] at h

/-- A proper four-edge-colouring of `coDiamondPendantsSameTip`, as a symmetric table on the
vertices. -/
def coDiamondPendantsSameTipEdgeCol :
    coDiamondPendantsSameTip.V → coDiamondPendantsSameTip.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 2, 0],
   ![0, 1, 0, 2, 0, 3], ![1, 2, 0, 0, 3, 0]]

/-- **The edge chromatic number of `coDiamondPendantsSameTip` is four.** -/
@[simp] theorem edgeChromNum_coDiamondPendantsSameTip :
    coDiamondPendantsSameTip.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondPendantsSameTip)
      coDiamondPendantsSameTipEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondPendantsSameTip
    rwa [show coDiamondPendantsSameTip.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondTailTip` is three.** -/
@[simp] theorem indepNum_coDiamondTailTip : coDiamondTailTip.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondTailTip)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondTailTip` is three.** -/
@[simp] theorem cliqueNum_coDiamondTailTip : coDiamondTailTip.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondTailTip)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coDiamondTailTip`. -/
def coDiamondTailTipCol : coDiamondTailTip.V → Fin 3 :=
  ![0, 0, 0, 1, 2, 2]

/-- **The chromatic number of `coDiamondTailTip` is three.** -/
@[simp] theorem chromNum_coDiamondTailTip : coDiamondTailTip.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondTailTipCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondTailTip
  rwa [cliqueNum_coDiamondTailTip] at h

/-- A proper four-edge-colouring of `coDiamondTailTip`, as a symmetric table on the vertices. -/
def coDiamondTailTipEdgeCol : coDiamondTailTip.V → coDiamondTailTip.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 1, 0, 2, 0, 0], ![1, 0, 2, 3, 0, 0]]

/-- **The edge chromatic number of `coDiamondTailTip` is four.** -/
@[simp] theorem edgeChromNum_coDiamondTailTip : coDiamondTailTip.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondTailTip)
      coDiamondTailTipEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondTailTip
    rwa [show coDiamondTailTip.maxDeg = 4 from by decide] at h

/-- **The independence number of `coDiamondTailHub` is three.** -/
@[simp] theorem indepNum_coDiamondTailHub : coDiamondTailHub.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coDiamondTailHub)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coDiamondTailHub` is three.** -/
@[simp] theorem cliqueNum_coDiamondTailHub : coDiamondTailHub.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coDiamondTailHub)
    (l := ([2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coDiamondTailHub`. -/
def coDiamondTailHubCol : coDiamondTailHub.V → Fin 3 :=
  ![0, 0, 0, 1, 2, 2]

/-- **The chromatic number of `coDiamondTailHub` is three.** -/
@[simp] theorem chromNum_coDiamondTailHub : coDiamondTailHub.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coDiamondTailHubCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coDiamondTailHub
  rwa [cliqueNum_coDiamondTailHub] at h

/-- A proper four-edge-colouring of `coDiamondTailHub`, as a symmetric table on the vertices. -/
def coDiamondTailHubEdgeCol : coDiamondTailHub.V → coDiamondTailHub.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 0, 1, 2, 0, 0], ![0, 1, 2, 3, 0, 0]]

/-- **The edge chromatic number of `coDiamondTailHub` is four.** -/
@[simp] theorem edgeChromNum_coDiamondTailHub : coDiamondTailHub.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coDiamondTailHub)
      coDiamondTailHubEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coDiamondTailHub
    rwa [show coDiamondTailHub.maxDeg = 4 from by decide] at h

/-- **The independence number of `coK23PendantDeg2` is two.** -/
@[simp] theorem indepNum_coK23PendantDeg2 : coK23PendantDeg2.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK23PendantDeg2)
    (l := ([0, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coK23PendantDeg2` is three.** -/
@[simp] theorem cliqueNum_coK23PendantDeg2 : coK23PendantDeg2.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK23PendantDeg2)
    (l := ([0, 1, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coK23PendantDeg2`. -/
def coK23PendantDeg2Col : coK23PendantDeg2.V → Fin 3 :=
  ![0, 1, 2, 0, 1, 2]

/-- **The chromatic number of `coK23PendantDeg2` is three.** -/
@[simp] theorem chromNum_coK23PendantDeg2 : coK23PendantDeg2.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coK23PendantDeg2Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coK23PendantDeg2
  rwa [cliqueNum_coK23PendantDeg2] at h

/-- A proper four-edge-colouring of `coK23PendantDeg2`, as a symmetric table on the vertices. -/
def coK23PendantDeg2EdgeCol : coK23PendantDeg2.V → coK23PendantDeg2.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 2, 3],
   ![0, 0, 1, 2, 0, 0], ![1, 2, 0, 3, 0, 0]]

/-- **The edge chromatic number of `coK23PendantDeg2` is four.** -/
@[simp] theorem edgeChromNum_coK23PendantDeg2 : coK23PendantDeg2.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK23PendantDeg2)
      coK23PendantDeg2EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coK23PendantDeg2
    rwa [show coK23PendantDeg2.maxDeg = 4 from by decide] at h

/-- **The independence number of `coButterflyPendant` is three.** -/
@[simp] theorem indepNum_coButterflyPendant : coButterflyPendant.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coButterflyPendant)
    (l := ([0, 1, 2] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `coButterflyPendant` is three.** -/
@[simp] theorem cliqueNum_coButterflyPendant : coButterflyPendant.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coButterflyPendant)
    (l := ([2, 3, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper three-colouring of `coButterflyPendant`. -/
def coButterflyPendantCol : coButterflyPendant.V → Fin 3 :=
  ![0, 0, 0, 1, 1, 2]

/-- **The chromatic number of `coButterflyPendant` is three.** -/
@[simp] theorem chromNum_coButterflyPendant : coButterflyPendant.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coButterflyPendantCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coButterflyPendant
  rwa [cliqueNum_coButterflyPendant] at h

/-- A proper four-edge-colouring of `coButterflyPendant`, as a symmetric table on the vertices. -/
def coButterflyPendantEdgeCol : coButterflyPendant.V → coButterflyPendant.V → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 2, 0, 1], ![0, 0, 2, 0, 0, 3],
   ![0, 1, 0, 0, 0, 2], ![0, 0, 1, 3, 2, 0]]

/-- **The edge chromatic number of `coButterflyPendant` is four.** -/
@[simp] theorem edgeChromNum_coButterflyPendant : coButterflyPendant.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coButterflyPendant)
      coButterflyPendantEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coButterflyPendant
    rwa [show coButterflyPendant.maxDeg = 4 from by decide] at h

/-- A proper five-edge-colouring of `K6`, as a symmetric table on the vertices. -/
def K6EdgeCol : K6.V → K6.V → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 3, 4, 1], ![1, 2, 0, 4, 0, 3], ![2, 3, 4, 0, 1, 0],
   ![3, 4, 0, 1, 0, 2], ![4, 1, 3, 0, 2, 0]]

/-- **The edge chromatic number of `K6` is five.** -/
@[simp] theorem edgeChromNum_K6 : K6.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6)
      K6EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6
    rwa [show K6.maxDeg = 5 from by decide] at h

/-- **The independence number of `W5` is two.** -/
@[simp] theorem indepNum_W5 : W5.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := W5)
    (l := ([1, 3] : List (Fin 6)).map (FinEnum.equiv (α := W5.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `W5` is three.** -/
@[simp] theorem cliqueNum_W5 : W5.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := W5)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := W5.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `W5`. -/
def W5Col : W5.V → Fin 4 := fun v =>
  ![0, 1, 2, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `W5` is four.** -/
@[simp] theorem chromNum_W5 : W5.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring W5Col (by decide)) ?_
  have h : 3 < W5.chromNum := by graph_sat
  omega

/-- A proper five-edge-colouring of `W5`, as a symmetric table on the vertices. -/
def W5EdgeCol : W5.V → W5.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 0, 0, 1], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 1, 0],
   ![3, 0, 0, 1, 0, 0], ![4, 1, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `W5` is five.** -/
@[simp] theorem edgeChromNum_W5 : W5.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := W5)
      W5EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum W5
    rwa [show W5.maxDeg = 5 from by decide] at h

/-- **The independence number of `fan5` is three.** -/
@[simp] theorem indepNum_fan5 : fan5.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := fan5)
    (l := ([1, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := fan5.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `fan5` is three.** -/
@[simp] theorem cliqueNum_fan5 : fan5.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := fan5)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := fan5.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `fan5`. -/
def fan5Col : fan5.V → Fin 3 := fun v =>
  ![0, 1, 2, 1, 2, 1] (FinEnum.equiv v)

/-- **The chromatic number of `fan5` is three.** -/
@[simp] theorem chromNum_fan5 : fan5.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring fan5Col (by decide)) ?_
  have h := cliqueNum_le_chromNum fan5
  rwa [cliqueNum_fan5] at h

/-- A proper five-edge-colouring of `fan5`, as a symmetric table on the vertices. -/
def fan5EdgeCol : fan5.V → fan5.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 0, 0, 0], ![1, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 1, 0],
   ![3, 0, 0, 1, 0, 0], ![4, 0, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `fan5` is five.** -/
@[simp, toIsoGraph] theorem edgeChromNum_fan5 : fan5.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := fan5)
      fan5EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum fan5
    rwa [show fan5.maxDeg = 5 from by decide] at h

/-- **The independence number of `lollipop51` is two.** -/
@[simp] theorem indepNum_lollipop51 : lollipop51.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := lollipop51)
    (l := ([1, 5] : List (Fin 6)))
    (by decide) (by decide)

/-- **The clique number of `lollipop51` is five.** -/
@[simp] theorem cliqueNum_lollipop51 : lollipop51.cliqueNum = 5 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := lollipop51)
    (l := ([0, 1, 2, 3, 4] : List (Fin 6)))
    (by decide) (by decide)

/-- A proper five-colouring of `lollipop51`. -/
def lollipop51Col : lollipop51.V → Fin 5 :=
  ![0, 1, 2, 3, 4, 1]

/-- **The chromatic number of `lollipop51` is five.** -/
@[simp] theorem chromNum_lollipop51 : lollipop51.chromNum = 5 := by
  refine le_antisymm (chromNum_le_of_colouring lollipop51Col (by decide)) ?_
  have h := cliqueNum_le_chromNum lollipop51
  rwa [cliqueNum_lollipop51] at h

/-- A proper five-edge-colouring of `lollipop51`, as a symmetric table on the vertices. -/
def lollipop51EdgeCol : lollipop51.V → lollipop51.V → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 3, 4, 0], ![1, 2, 0, 4, 0, 0], ![2, 3, 4, 0, 1, 0],
   ![3, 4, 0, 1, 0, 0], ![4, 0, 0, 0, 0, 0]]

/-- **The edge chromatic number of `lollipop51` is five.** -/
@[simp] theorem edgeChromNum_lollipop51 : lollipop51.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := lollipop51)
      lollipop51EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum lollipop51
    rwa [show lollipop51.maxDeg = 5 from by decide] at h

/-- **The clique number of `book4` is three.** -/
@[simp] theorem cliqueNum_book4 : book4.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := book4)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := book4.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `book4`. -/
def book4Col : book4.V → Fin 3 := fun v =>
  ![0, 1, 2, 2, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `book4` is three.** -/
@[simp] theorem chromNum_book4 : book4.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring book4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum book4
  rwa [cliqueNum_book4] at h

/-- A proper five-edge-colouring of `book4`, as a symmetric table on the vertices. -/
def book4EdgeCol : book4.V → book4.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 1, 4, 3], ![1, 2, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0],
   ![3, 4, 0, 0, 0, 0], ![4, 3, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `book4` is five.** -/
@[simp] theorem edgeChromNum_book4 : book4.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := book4)
      book4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum book4
    rwa [show book4.maxDeg = 5 from by decide] at h

/-- **The clique number of `K1_1_1_3` is four.** -/
@[simp] theorem cliqueNum_K1_1_1_3 : K1_1_1_3.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_1_1_3)
    (l := ([0, 1, 2, 3] : List (Fin 6)).map (FinEnum.equiv (α := K1_1_1_3.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K1_1_1_3`. -/
def K1_1_1_3Col : K1_1_1_3.V → Fin 4 := fun v =>
  ![0, 1, 2, 3, 3, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K1_1_1_3` is four.** -/
@[simp] theorem chromNum_K1_1_1_3 : K1_1_1_3.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K1_1_1_3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_1_1_3
  rwa [cliqueNum_K1_1_1_3] at h

/-- A proper five-edge-colouring of `K1_1_1_3`, as a symmetric table on the vertices. -/
def K1_1_1_3EdgeCol : K1_1_1_3.V → K1_1_1_3.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 3, 4, 1], ![1, 2, 0, 4, 0, 3], ![2, 3, 4, 0, 0, 0],
   ![3, 4, 0, 0, 0, 0], ![4, 1, 3, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_1_1_3` is five.** -/
@[simp] theorem edgeChromNum_K1_1_1_3 : K1_1_1_3.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_1_1_3)
      K1_1_1_3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_1_1_3
    rwa [show K1_1_1_3.maxDeg = 5 from by decide] at h

/-- **The clique number of `K1_2_3` is three.** -/
@[simp] theorem cliqueNum_K1_2_3 : K1_2_3.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_2_3)
    (l := ([0, 1, 3] : List (Fin 6)).map (FinEnum.equiv (α := K1_2_3.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K1_2_3`. -/
def K1_2_3Col : K1_2_3.V → Fin 3 := fun v =>
  ![0, 1, 1, 2, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K1_2_3` is three.** -/
@[simp] theorem chromNum_K1_2_3 : K1_2_3.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K1_2_3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_2_3
  rwa [cliqueNum_K1_2_3] at h

/-- A proper five-edge-colouring of `K1_2_3`, as a symmetric table on the vertices. -/
def K1_2_3EdgeCol : K1_2_3.V → K1_2_3.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 0, 1, 2, 3], ![1, 0, 0, 0, 4, 2], ![2, 1, 0, 0, 0, 0],
   ![3, 2, 4, 0, 0, 0], ![4, 3, 2, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_2_3` is five.** -/
@[simp] theorem edgeChromNum_K1_2_3 : K1_2_3.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_2_3)
      K1_2_3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_2_3
    rwa [show K1_2_3.maxDeg = 5 from by decide] at h

/-- **The clique number of `K1_1_2_2` is four.** -/
@[simp] theorem cliqueNum_K1_1_2_2 : K1_1_2_2.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K1_1_2_2)
    (l := ([0, 1, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := K1_1_2_2.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K1_1_2_2`. -/
def K1_1_2_2Col : K1_1_2_2.V → Fin 4 := fun v =>
  ![0, 1, 2, 2, 3, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K1_1_2_2` is four.** -/
@[simp] theorem chromNum_K1_1_2_2 : K1_1_2_2.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K1_1_2_2Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K1_1_2_2
  rwa [cliqueNum_K1_1_2_2] at h

/-- A proper five-edge-colouring of `K1_1_2_2`, as a symmetric table on the vertices. -/
def K1_1_2_2EdgeCol : K1_1_2_2.V → K1_1_2_2.V → Fin 5 := fun x y =>
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 2, 3, 4, 1], ![1, 2, 0, 0, 0, 3], ![2, 3, 0, 0, 1, 0],
   ![3, 4, 0, 1, 0, 0], ![4, 1, 3, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K1_1_2_2` is five.** -/
@[simp] theorem edgeChromNum_K1_1_2_2 : K1_1_2_2.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K1_1_2_2)
      K1_1_2_2EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K1_1_2_2
    rwa [show K1_1_2_2.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusEdge` is two.** -/
@[simp] theorem indepNum_K6MinusEdge : K6MinusEdge.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusEdge)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusEdge.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusEdge` is five.** -/
@[simp] theorem cliqueNum_K6MinusEdge : K6MinusEdge.cliqueNum = 5 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusEdge)
    (l := ([0, 2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusEdge.V)).symm)
    (by decide) (by decide)

/-- A proper five-colouring of `K6MinusEdge`. -/
def K6MinusEdgeCol : K6MinusEdge.V → Fin 5 := fun v =>
  ![0, 0, 1, 2, 3, 4] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusEdge` is five.** -/
@[simp] theorem chromNum_K6MinusEdge : K6MinusEdge.chromNum = 5 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusEdgeCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusEdge
  rwa [cliqueNum_K6MinusEdge] at h

/-- A proper five-edge-colouring of `K6MinusEdge`, as a symmetric table on the vertices. -/
def K6MinusEdgeEdgeCol : K6MinusEdge.V → K6MinusEdge.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 2, 3, 0], ![0, 1, 0, 3, 4, 2], ![1, 2, 3, 0, 0, 4],
   ![2, 3, 4, 0, 0, 1], ![3, 0, 2, 4, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusEdge` is five.** -/
@[simp] theorem edgeChromNum_K6MinusEdge : K6MinusEdge.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusEdge)
      K6MinusEdgeEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusEdge
    rwa [show K6MinusEdge.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusP3` is two.** -/
@[simp] theorem indepNum_K6MinusP3 : K6MinusP3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusP3)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusP3` is five.** -/
@[simp] theorem cliqueNum_K6MinusP3 : K6MinusP3.cliqueNum = 5 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusP3)
    (l := ([0, 2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP3.V)).symm)
    (by decide) (by decide)

/-- A proper five-colouring of `K6MinusP3`. -/
def K6MinusP3Col : K6MinusP3.V → Fin 5 := fun v =>
  ![0, 0, 1, 2, 3, 4] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusP3` is five.** -/
@[simp] theorem chromNum_K6MinusP3 : K6MinusP3.chromNum = 5 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusP3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusP3
  rwa [cliqueNum_K6MinusP3] at h

/-- A proper five-edge-colouring of `K6MinusP3`, as a symmetric table on the vertices. -/
def K6MinusP3EdgeCol : K6MinusP3.V → K6MinusP3.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 2, 4, 1], ![1, 0, 2, 0, 3, 4],
   ![2, 1, 4, 3, 0, 0], ![3, 2, 1, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusP3` is five.** -/
@[simp] theorem edgeChromNum_K6MinusP3 : K6MinusP3.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusP3)
      K6MinusP3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusP3
    rwa [show K6MinusP3.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusP4` is two.** -/
@[simp] theorem indepNum_K6MinusP4 : K6MinusP4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusP4)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusP4` is four.** -/
@[simp] theorem cliqueNum_K6MinusP4 : K6MinusP4.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusP4)
    (l := ([0, 2, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP4.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusP4`. -/
def K6MinusP4Col : K6MinusP4.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusP4` is four.** -/
@[simp] theorem chromNum_K6MinusP4 : K6MinusP4.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusP4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusP4
  rwa [cliqueNum_K6MinusP4] at h

/-- A proper five-edge-colouring of `K6MinusP4`, as a symmetric table on the vertices. -/
def K6MinusP4EdgeCol : K6MinusP4.V → K6MinusP4.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 4, 1], ![1, 0, 0, 0, 3, 4],
   ![2, 1, 4, 3, 0, 0], ![3, 2, 1, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusP4` is five.** -/
@[simp] theorem edgeChromNum_K6MinusP4 : K6MinusP4.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusP4)
      K6MinusP4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusP4
    rwa [show K6MinusP4.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusC4` is two.** -/
@[simp] theorem indepNum_K6MinusC4 : K6MinusC4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusC4)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusC4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusC4` is four.** -/
@[simp] theorem cliqueNum_K6MinusC4 : K6MinusC4.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusC4)
    (l := ([0, 2, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusC4.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusC4`. -/
def K6MinusC4Col : K6MinusC4.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusC4` is four.** -/
@[simp] theorem chromNum_K6MinusC4 : K6MinusC4.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusC4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusC4
  rwa [cliqueNum_K6MinusC4] at h

/-- A proper five-edge-colouring of `K6MinusC4`, as a symmetric table on the vertices. -/
def K6MinusC4EdgeCol : K6MinusC4.V → K6MinusC4.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 1], ![0, 0, 0, 0, 3, 4], ![0, 0, 0, 0, 4, 3],
   ![1, 2, 3, 4, 0, 0], ![2, 1, 4, 3, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusC4` is five.** -/
@[simp] theorem edgeChromNum_K6MinusC4 : K6MinusC4.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusC4)
      K6MinusC4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusC4
    rwa [show K6MinusC4.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusClaw` is two.** -/
@[simp] theorem indepNum_K6MinusClaw : K6MinusClaw.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusClaw)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusClaw.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusClaw` is five.** -/
@[simp] theorem cliqueNum_K6MinusClaw : K6MinusClaw.cliqueNum = 5 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusClaw)
    (l := ([1, 2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusClaw.V)).symm)
    (by decide) (by decide)

/-- A proper five-colouring of `K6MinusClaw`. -/
def K6MinusClawCol : K6MinusClaw.V → Fin 5 := fun v =>
  ![0, 0, 1, 2, 3, 4] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusClaw` is five.** -/
@[simp] theorem chromNum_K6MinusClaw : K6MinusClaw.chromNum = 5 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusClawCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusClaw
  rwa [cliqueNum_K6MinusClaw] at h

/-- A proper five-edge-colouring of `K6MinusClaw`, as a symmetric table on the vertices. -/
def K6MinusClawEdgeCol : K6MinusClaw.V → K6MinusClaw.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 2, 3], ![0, 0, 0, 4, 1, 2], ![0, 1, 4, 0, 3, 0],
   ![0, 2, 1, 3, 0, 4], ![1, 3, 2, 0, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusClaw` is five.** -/
@[simp] theorem edgeChromNum_K6MinusClaw : K6MinusClaw.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusClaw)
      K6MinusClawEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusClaw
    rwa [show K6MinusClaw.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusPaw` is three.** -/
@[simp] theorem indepNum_K6MinusPaw : K6MinusPaw.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusPaw)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusPaw.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusPaw` is four.** -/
@[simp] theorem cliqueNum_K6MinusPaw : K6MinusPaw.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusPaw)
    (l := ([1, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusPaw.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusPaw`. -/
def K6MinusPawCol : K6MinusPaw.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusPaw` is four.** -/
@[simp] theorem chromNum_K6MinusPaw : K6MinusPaw.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusPawCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusPaw
  rwa [cliqueNum_K6MinusPaw] at h

/-- A proper five-edge-colouring of `K6MinusPaw`, as a symmetric table on the vertices. -/
def K6MinusPawEdgeCol : K6MinusPaw.V → K6MinusPaw.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 3, 0], ![0, 0, 1, 0, 2, 3],
   ![0, 1, 3, 2, 0, 4], ![1, 2, 0, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusPaw` is five.** -/
@[simp] theorem edgeChromNum_K6MinusPaw : K6MinusPaw.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusPaw)
      K6MinusPawEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusPaw
    rwa [show K6MinusPaw.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusDiamond` is three.** -/
@[simp] theorem indepNum_K6MinusDiamond : K6MinusDiamond.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusDiamond)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusDiamond.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusDiamond` is four.** -/
@[simp] theorem cliqueNum_K6MinusDiamond : K6MinusDiamond.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusDiamond)
    (l := ([2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusDiamond.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusDiamond`. -/
def K6MinusDiamondCol : K6MinusDiamond.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusDiamond` is four.** -/
@[simp] theorem chromNum_K6MinusDiamond : K6MinusDiamond.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusDiamondCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusDiamond
  rwa [cliqueNum_K6MinusDiamond] at h

/-- A proper five-edge-colouring of `K6MinusDiamond`, as a symmetric table on the vertices. -/
def K6MinusDiamondEdgeCol : K6MinusDiamond.V → K6MinusDiamond.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 3, 2],
   ![0, 1, 2, 3, 0, 4], ![1, 0, 3, 2, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusDiamond` is five.** -/
@[simp] theorem edgeChromNum_K6MinusDiamond : K6MinusDiamond.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusDiamond)
      K6MinusDiamondEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusDiamond
    rwa [show K6MinusDiamond.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusK2P3` is two.** -/
@[simp] theorem indepNum_K6MinusK2P3 : K6MinusK2P3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusK2P3)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK2P3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusK2P3` is four.** -/
@[simp] theorem cliqueNum_K6MinusK2P3 : K6MinusK2P3.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusK2P3)
    (l := ([0, 2, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK2P3.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusK2P3`. -/
def K6MinusK2P3Col : K6MinusK2P3.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusK2P3` is four.** -/
@[simp] theorem chromNum_K6MinusK2P3 : K6MinusK2P3.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusK2P3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusK2P3
  rwa [cliqueNum_K6MinusK2P3] at h

/-- A proper five-edge-colouring of `K6MinusK2P3`, as a symmetric table on the vertices. -/
def K6MinusK2P3EdgeCol : K6MinusK2P3.V → K6MinusK2P3.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 2, 0, 4], ![0, 1, 0, 0, 3, 2], ![1, 2, 0, 0, 0, 0],
   ![2, 0, 3, 0, 0, 1], ![3, 4, 2, 0, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusK2P3` is five.** -/
@[simp] theorem edgeChromNum_K6MinusK2P3 : K6MinusK2P3.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusK2P3)
      K6MinusK2P3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusK2P3
    rwa [show K6MinusK2P3.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusP5` is two.** -/
@[simp] theorem indepNum_K6MinusP5 : K6MinusP5.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusP5)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP5.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusP5` is four.** -/
@[simp] theorem cliqueNum_K6MinusP5 : K6MinusP5.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusP5)
    (l := ([0, 2, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusP5.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusP5`. -/
def K6MinusP5Col : K6MinusP5.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusP5` is four.** -/
@[simp] theorem chromNum_K6MinusP5 : K6MinusP5.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusP5Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusP5
  rwa [cliqueNum_K6MinusP5] at h

/-- A proper five-edge-colouring of `K6MinusP5`, as a symmetric table on the vertices. -/
def K6MinusP5EdgeCol : K6MinusP5.V → K6MinusP5.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 3, 1], ![1, 0, 0, 0, 0, 4],
   ![2, 1, 3, 0, 0, 0], ![3, 2, 1, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusP5` is five.** -/
@[simp] theorem edgeChromNum_K6MinusP5 : K6MinusP5.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusP5)
      K6MinusP5EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusP5
    rwa [show K6MinusP5.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusFork` is two.** -/
@[simp] theorem indepNum_K6MinusFork : K6MinusFork.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusFork)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusFork.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusFork` is four.** -/
@[simp] theorem cliqueNum_K6MinusFork : K6MinusFork.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusFork)
    (l := ([1, 2, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusFork.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusFork`. -/
def K6MinusForkCol : K6MinusFork.V → Fin 4 := fun v =>
  ![0, 0, 1, 2, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusFork` is four.** -/
@[simp] theorem chromNum_K6MinusFork : K6MinusFork.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusForkCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusFork
  rwa [cliqueNum_K6MinusFork] at h

/-- A proper five-edge-colouring of `K6MinusFork`, as a symmetric table on the vertices. -/
def K6MinusForkEdgeCol : K6MinusFork.V → K6MinusFork.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 2, 3], ![0, 0, 0, 3, 1, 2], ![0, 1, 3, 0, 0, 0],
   ![0, 2, 1, 0, 0, 4], ![1, 3, 2, 0, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusFork` is five.** -/
@[simp] theorem edgeChromNum_K6MinusFork : K6MinusFork.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusFork)
      K6MinusForkEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusFork
    rwa [show K6MinusFork.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusK23` is two.** -/
@[simp] theorem indepNum_K6MinusK23 : K6MinusK23.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusK23)
    (l := ([0, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK23.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusK23` is four.** -/
@[simp] theorem cliqueNum_K6MinusK23 : K6MinusK23.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusK23)
    (l := ([2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK23.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusK23`. -/
def K6MinusK23Col : K6MinusK23.V → Fin 4 := fun v =>
  ![0, 1, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusK23` is four.** -/
@[simp] theorem chromNum_K6MinusK23 : K6MinusK23.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusK23Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusK23
  rwa [cliqueNum_K6MinusK23] at h

/-- A proper five-edge-colouring of `K6MinusK23`, as a symmetric table on the vertices. -/
def K6MinusK23EdgeCol : K6MinusK23.V → K6MinusK23.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 3], ![0, 0, 0, 0, 2, 4],
   ![0, 0, 1, 2, 0, 0], ![1, 2, 3, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusK23` is five.** -/
@[simp] theorem edgeChromNum_K6MinusK23 : K6MinusK23.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusK23)
      K6MinusK23EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusK23
    rwa [show K6MinusK23.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusK23PlusEdge` is three.** -/
@[simp] theorem indepNum_K6MinusK23PlusEdge : K6MinusK23PlusEdge.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusK23PlusEdge)
    (l := ([0, 2, 3] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK23PlusEdge.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusK23PlusEdge` is three.** -/
@[simp] theorem cliqueNum_K6MinusK23PlusEdge : K6MinusK23PlusEdge.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusK23PlusEdge)
    (l := ([0, 1, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusK23PlusEdge.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusK23PlusEdge`. -/
def K6MinusK23PlusEdgeCol : K6MinusK23PlusEdge.V → Fin 3 := fun v =>
  ![0, 1, 0, 0, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusK23PlusEdge` is three.** -/
@[simp] theorem chromNum_K6MinusK23PlusEdge : K6MinusK23PlusEdge.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusK23PlusEdgeCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusK23PlusEdge
  rwa [cliqueNum_K6MinusK23PlusEdge] at h

/-- A proper five-edge-colouring of `K6MinusK23PlusEdge`, as a symmetric table on the vertices. -/
def K6MinusK23PlusEdgeEdgeCol : K6MinusK23PlusEdge.V → K6MinusK23PlusEdge.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 2], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 3],
   ![0, 0, 0, 0, 0, 4], ![1, 2, 0, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusK23PlusEdge` is five.** -/
@[simp] theorem edgeChromNum_K6MinusK23PlusEdge : K6MinusK23PlusEdge.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusK23PlusEdge)
      K6MinusK23PlusEdgeEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusK23PlusEdge
    rwa [show K6MinusK23PlusEdge.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusBanner` is two.** -/
@[simp] theorem indepNum_K6MinusBanner : K6MinusBanner.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusBanner)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBanner.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusBanner` is four.** -/
@[simp] theorem cliqueNum_K6MinusBanner : K6MinusBanner.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusBanner)
    (l := ([1, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBanner.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusBanner`. -/
def K6MinusBannerCol : K6MinusBanner.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusBanner` is four.** -/
@[simp] theorem chromNum_K6MinusBanner : K6MinusBanner.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusBannerCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusBanner
  rwa [cliqueNum_K6MinusBanner] at h

/-- A proper five-edge-colouring of `K6MinusBanner`, as a symmetric table on the vertices. -/
def K6MinusBannerEdgeCol : K6MinusBanner.V → K6MinusBanner.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3], ![0, 0, 0, 0, 3, 4],
   ![0, 1, 2, 3, 0, 0], ![1, 2, 3, 4, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusBanner` is five.** -/
@[simp] theorem edgeChromNum_K6MinusBanner : K6MinusBanner.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusBanner)
      K6MinusBannerEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusBanner
    rwa [show K6MinusBanner.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusBull` is three.** -/
@[simp] theorem indepNum_K6MinusBull : K6MinusBull.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusBull)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBull.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusBull` is four.** -/
@[simp] theorem cliqueNum_K6MinusBull : K6MinusBull.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusBull)
    (l := ([2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBull.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusBull`. -/
def K6MinusBullCol : K6MinusBull.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusBull` is four.** -/
@[simp] theorem chromNum_K6MinusBull : K6MinusBull.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusBullCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusBull
  rwa [cliqueNum_K6MinusBull] at h

/-- A proper five-edge-colouring of `K6MinusBull`, as a symmetric table on the vertices. -/
def K6MinusBullEdgeCol : K6MinusBull.V → K6MinusBull.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 1, 3, 0], ![0, 0, 1, 0, 2, 3],
   ![0, 0, 3, 2, 0, 4], ![1, 2, 0, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusBull` is five.** -/
@[simp] theorem edgeChromNum_K6MinusBull : K6MinusBull.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusBull)
      K6MinusBullEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusBull
    rwa [show K6MinusBull.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusKite` is three.** -/
@[simp] theorem indepNum_K6MinusKite : K6MinusKite.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusKite)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusKite.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusKite` is three.** -/
@[simp] theorem cliqueNum_K6MinusKite : K6MinusKite.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusKite)
    (l := ([0, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusKite.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusKite`. -/
def K6MinusKiteCol : K6MinusKite.V → Fin 3 := fun v =>
  ![0, 0, 1, 0, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusKite` is three.** -/
@[simp] theorem chromNum_K6MinusKite : K6MinusKite.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusKiteCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusKite
  rwa [cliqueNum_K6MinusKite] at h

/-- A proper five-edge-colouring of `K6MinusKite`, as a symmetric table on the vertices. -/
def K6MinusKiteEdgeCol : K6MinusKite.V → K6MinusKite.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 1, 0, 2, 0, 4], ![1, 0, 2, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusKite` is five.** -/
@[simp] theorem edgeChromNum_K6MinusKite : K6MinusKite.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusKite)
      K6MinusKiteEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusKite
    rwa [show K6MinusKite.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusTadpole32` is three.** -/
@[simp] theorem indepNum_K6MinusTadpole32 : K6MinusTadpole32.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusTadpole32)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusTadpole32.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusTadpole32` is three.** -/
@[simp] theorem cliqueNum_K6MinusTadpole32 : K6MinusTadpole32.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusTadpole32)
    (l := ([0, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusTadpole32.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusTadpole32`. -/
def K6MinusTadpole32Col : K6MinusTadpole32.V → Fin 3 := fun v =>
  ![0, 0, 0, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusTadpole32` is three.** -/
@[simp] theorem chromNum_K6MinusTadpole32 : K6MinusTadpole32.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusTadpole32Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusTadpole32
  rwa [cliqueNum_K6MinusTadpole32] at h

/-- A proper five-edge-colouring of `K6MinusTadpole32`, as a symmetric table on the vertices. -/
def K6MinusTadpole32EdgeCol : K6MinusTadpole32.V → K6MinusTadpole32.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 1, 0, 0, 3],
   ![0, 1, 2, 0, 0, 4], ![1, 2, 0, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusTadpole32` is five.** -/
@[simp] theorem edgeChromNum_K6MinusTadpole32 : K6MinusTadpole32.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusTadpole32)
      K6MinusTadpole32EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusTadpole32
    rwa [show K6MinusTadpole32.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusButterfly` is three.** -/
@[simp] theorem indepNum_K6MinusButterfly : K6MinusButterfly.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusButterfly)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusButterfly.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusButterfly` is three.** -/
@[simp] theorem cliqueNum_K6MinusButterfly : K6MinusButterfly.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusButterfly)
    (l := ([1, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusButterfly.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusButterfly`. -/
def K6MinusButterflyCol : K6MinusButterfly.V → Fin 3 := fun v =>
  ![0, 0, 0, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusButterfly` is three.** -/
@[simp] theorem chromNum_K6MinusButterfly : K6MinusButterfly.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusButterflyCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusButterfly
  rwa [cliqueNum_K6MinusButterfly] at h

/-- A proper five-edge-colouring of `K6MinusButterfly`, as a symmetric table on the vertices. -/
def K6MinusButterflyEdgeCol : K6MinusButterfly.V → K6MinusButterfly.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 2, 0, 1], ![0, 0, 2, 0, 0, 3],
   ![0, 1, 0, 0, 0, 4], ![0, 2, 1, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusButterfly` is five.** -/
@[simp] theorem edgeChromNum_K6MinusButterfly : K6MinusButterfly.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusButterfly)
      K6MinusButterflyEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusButterfly
    rwa [show K6MinusButterfly.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusCricket` is three.** -/
@[simp] theorem indepNum_K6MinusCricket : K6MinusCricket.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusCricket)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusCricket.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusCricket` is four.** -/
@[simp] theorem cliqueNum_K6MinusCricket : K6MinusCricket.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusCricket)
    (l := ([1, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusCricket.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusCricket`. -/
def K6MinusCricketCol : K6MinusCricket.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusCricket` is four.** -/
@[simp] theorem chromNum_K6MinusCricket : K6MinusCricket.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusCricketCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusCricket
  rwa [cliqueNum_K6MinusCricket] at h

/-- A proper five-edge-colouring of `K6MinusCricket`, as a symmetric table on the vertices. -/
def K6MinusCricketEdgeCol : K6MinusCricket.V → K6MinusCricket.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 2, 0, 3], ![0, 0, 2, 0, 3, 1],
   ![0, 1, 0, 3, 0, 4], ![0, 2, 3, 1, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusCricket` is five.** -/
@[simp] theorem edgeChromNum_K6MinusCricket : K6MinusCricket.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusCricket)
      K6MinusCricketEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusCricket
    rwa [show K6MinusCricket.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusGem` is three.** -/
@[simp] theorem indepNum_K6MinusGem : K6MinusGem.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusGem)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusGem.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusGem` is three.** -/
@[simp] theorem cliqueNum_K6MinusGem : K6MinusGem.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusGem)
    (l := ([1, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusGem.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusGem`. -/
def K6MinusGemCol : K6MinusGem.V → Fin 3 := fun v =>
  ![0, 0, 0, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusGem` is three.** -/
@[simp] theorem chromNum_K6MinusGem : K6MinusGem.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusGemCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusGem
  rwa [cliqueNum_K6MinusGem] at h

/-- A proper five-edge-colouring of `K6MinusGem`, as a symmetric table on the vertices. -/
def K6MinusGemEdgeCol : K6MinusGem.V → K6MinusGem.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 3],
   ![0, 1, 0, 0, 0, 4], ![0, 2, 1, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusGem` is five.** -/
@[simp] theorem edgeChromNum_K6MinusGem : K6MinusGem.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusGem)
      K6MinusGemEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusGem
    rwa [show K6MinusGem.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusDart` is three.** -/
@[simp] theorem indepNum_K6MinusDart : K6MinusDart.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusDart)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusDart.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusDart` is four.** -/
@[simp] theorem cliqueNum_K6MinusDart : K6MinusDart.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusDart)
    (l := ([2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusDart.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusDart`. -/
def K6MinusDartCol : K6MinusDart.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusDart` is four.** -/
@[simp] theorem chromNum_K6MinusDart : K6MinusDart.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusDartCol (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusDart
  rwa [cliqueNum_K6MinusDart] at h

/-- A proper five-edge-colouring of `K6MinusDart`, as a symmetric table on the vertices. -/
def K6MinusDartEdgeCol : K6MinusDart.V → K6MinusDart.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 0, 1, 2, 0, 4], ![0, 1, 2, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusDart` is five.** -/
@[simp] theorem edgeChromNum_K6MinusDart : K6MinusDart.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusDart)
      K6MinusDartEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusDart
    rwa [show K6MinusDart.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusLollipop41` is four.** -/
@[simp] theorem indepNum_K6MinusLollipop41 : K6MinusLollipop41.indepNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusLollipop41)
    (l := ([0, 1, 2, 3] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusLollipop41.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusLollipop41` is three.** -/
@[simp] theorem cliqueNum_K6MinusLollipop41 : K6MinusLollipop41.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusLollipop41)
    (l := ([1, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusLollipop41.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `K6MinusLollipop41`. -/
def K6MinusLollipop41Col : K6MinusLollipop41.V → Fin 3 := fun v =>
  ![0, 0, 0, 0, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusLollipop41` is three.** -/
@[simp] theorem chromNum_K6MinusLollipop41 : K6MinusLollipop41.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusLollipop41Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusLollipop41
  rwa [cliqueNum_K6MinusLollipop41] at h

/-- A proper five-edge-colouring of `K6MinusLollipop41`, as a symmetric table on the vertices. -/
def K6MinusLollipop41EdgeCol : K6MinusLollipop41.V → K6MinusLollipop41.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 0, 1, 2, 0, 4], ![0, 1, 2, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusLollipop41` is five.** -/
@[simp] theorem edgeChromNum_K6MinusLollipop41 : K6MinusLollipop41.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusLollipop41)
      K6MinusLollipop41EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusLollipop41
    rwa [show K6MinusLollipop41.maxDeg = 5 from by decide] at h

/-- **The independence number of `K6MinusBook3` is three.** -/
@[simp] theorem indepNum_K6MinusBook3 : K6MinusBook3.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := K6MinusBook3)
    (l := ([0, 1, 2] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBook3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `K6MinusBook3` is four.** -/
@[simp] theorem cliqueNum_K6MinusBook3 : K6MinusBook3.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := K6MinusBook3)
    (l := ([2, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := K6MinusBook3.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `K6MinusBook3`. -/
def K6MinusBook3Col : K6MinusBook3.V → Fin 4 := fun v =>
  ![0, 0, 0, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `K6MinusBook3` is four.** -/
@[simp] theorem chromNum_K6MinusBook3 : K6MinusBook3.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring K6MinusBook3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K6MinusBook3
  rwa [cliqueNum_K6MinusBook3] at h

/-- A proper five-edge-colouring of `K6MinusBook3`, as a symmetric table on the vertices. -/
def K6MinusBook3EdgeCol : K6MinusBook3.V → K6MinusBook3.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 2, 3],
   ![0, 0, 1, 2, 0, 4], ![0, 1, 2, 3, 4, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K6MinusBook3` is five.** -/
@[simp] theorem edgeChromNum_K6MinusBook3 : K6MinusBook3.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K6MinusBook3)
      K6MinusBook3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K6MinusBook3
    rwa [show K6MinusBook3.maxDeg = 5 from by decide] at h

/-- A proper two-colouring of `K3_3`. -/
def K3_3Col : K3_3.V → Fin 2 := fun v =>
  ![0, 0, 0, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K3_3` is two.** -/
@[simp] theorem chromNum_K3_3 : K3_3.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K3_3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K3_3
  simpa using h

/-- A proper three-edge-colouring of `K3_3`, as a symmetric table on the vertices. -/
def K3_3EdgeCol : K3_3.V → K3_3.V → Fin 3 := fun x y =>
  ![![0, 0, 0, 0, 1, 2], ![0, 0, 0, 1, 2, 0], ![0, 0, 0, 2, 0, 1], ![0, 1, 2, 0, 0, 0],
   ![1, 2, 0, 0, 0, 0], ![2, 0, 1, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K3_3` is three.** -/
@[simp] theorem edgeChromNum_K3_3 : K3_3.edgeChromNum = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K3_3)
      K3_3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K3_3
    rwa [show K3_3.maxDeg = 3 from by decide] at h

/-- A proper two-colouring of `K2_4`. -/
def K2_4Col : K2_4.V → Fin 2 := fun v =>
  ![0, 0, 1, 1, 1, 1] (FinEnum.equiv v)

/-- **The chromatic number of `K2_4` is two.** -/
@[simp] theorem chromNum_K2_4 : K2_4.chromNum = 2 := by
  refine le_antisymm (chromNum_le_of_colouring K2_4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum K2_4
  simpa using h

/-- A proper four-edge-colouring of `K2_4`, as a symmetric table on the vertices. -/
def K2_4EdgeCol : K2_4.V → K2_4.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 0, 3, 2], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 3, 0, 0, 0, 0], ![3, 2, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `K2_4` is four.** -/
@[simp] theorem edgeChromNum_K2_4 : K2_4.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := K2_4)
      K2_4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum K2_4
    rwa [show K2_4.maxDeg = 4 from by decide] at h

/-- **The clique number of `octahedron` is three.** -/
@[simp] theorem cliqueNum_octahedron : octahedron.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := octahedron)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := octahedron.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `octahedron`. -/
def octahedronCol : octahedron.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `octahedron` is three.** -/
@[simp] theorem chromNum_octahedron : octahedron.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring octahedronCol (by decide)) ?_
  have h := cliqueNum_le_chromNum octahedron
  rwa [cliqueNum_octahedron] at h

/-- A proper four-edge-colouring of `octahedron`, as a symmetric table on the vertices. -/
def octahedronEdgeCol : octahedron.V → octahedron.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 2, 3, 1, 0], ![0, 2, 0, 0, 3, 1], ![1, 3, 0, 0, 0, 2],
   ![2, 1, 3, 0, 0, 0], ![3, 0, 1, 2, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `octahedron` is four.** -/
@[simp] theorem edgeChromNum_octahedron : octahedron.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := octahedron)
      octahedronEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum octahedron
    rwa [show octahedron.maxDeg = 4 from by decide] at h

/-- **The independence number of `coK2C4` is two.** -/
@[simp] theorem indepNum_coK2C4 : coK2C4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK2C4)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := coK2C4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coK2C4` is three.** -/
@[simp] theorem cliqueNum_coK2C4 : coK2C4.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK2C4)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := coK2C4.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coK2C4`. -/
def coK2C4Col : coK2C4.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coK2C4` is three.** -/
@[simp] theorem chromNum_coK2C4 : coK2C4.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coK2C4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coK2C4
  rwa [cliqueNum_coK2C4] at h

/-- A proper four-edge-colouring of `coK2C4`, as a symmetric table on the vertices. -/
def coK2C4EdgeCol : coK2C4.V → coK2C4.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 3, 0, 2], ![0, 1, 0, 0, 3, 0], ![1, 3, 0, 0, 0, 0],
   ![2, 0, 3, 0, 0, 0], ![3, 2, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coK2C4` is four.** -/
@[simp] theorem edgeChromNum_coK2C4 : coK2C4.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK2C4)
      coK2C4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coK2C4
    rwa [show coK2C4.maxDeg = 4 from by decide] at h

/-- **The independence number of `coK2P4` is two.** -/
@[simp] theorem indepNum_coK2P4 : coK2P4.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK2P4)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := coK2P4.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coK2P4` is three.** -/
@[simp] theorem cliqueNum_coK2P4 : coK2P4.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK2P4)
    (l := ([0, 2, 4] : List (Fin 6)).map (FinEnum.equiv (α := coK2P4.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coK2P4`. -/
def coK2P4Col : coK2P4.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coK2P4` is three.** -/
@[simp] theorem chromNum_coK2P4 : coK2P4.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coK2P4Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coK2P4
  rwa [cliqueNum_coK2P4] at h

/-- A proper four-edge-colouring of `coK2P4`, as a symmetric table on the vertices. -/
def coK2P4EdgeCol : coK2P4.V → coK2P4.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 2, 3, 1, 0], ![0, 2, 0, 0, 3, 1], ![1, 3, 0, 0, 0, 2],
   ![2, 1, 3, 0, 0, 0], ![3, 0, 1, 2, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coK2P4` is four.** -/
@[simp] theorem edgeChromNum_coK2P4 : coK2P4.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK2P4)
      coK2P4EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coK2P4
    rwa [show coK2P4.maxDeg = 4 from by decide] at h

/-- **The independence number of `coK2Claw` is two.** -/
@[simp] theorem indepNum_coK2Claw : coK2Claw.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK2Claw)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := coK2Claw.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coK2Claw` is four.** -/
@[simp] theorem cliqueNum_coK2Claw : coK2Claw.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK2Claw)
    (l := ([0, 3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := coK2Claw.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `coK2Claw`. -/
def coK2ClawCol : coK2Claw.V → Fin 4 := fun v =>
  ![0, 0, 1, 1, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `coK2Claw` is four.** -/
@[simp] theorem chromNum_coK2Claw : coK2Claw.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coK2ClawCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coK2Claw
  rwa [cliqueNum_coK2Claw] at h

/-- A proper five-edge-colouring of `coK2Claw`, as a symmetric table on the vertices. -/
def coK2ClawEdgeCol : coK2Claw.V → coK2Claw.V → Fin 5 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 0, 3, 4], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 4, 2],
   ![2, 3, 0, 4, 0, 0], ![3, 4, 0, 2, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coK2Claw` is five.** -/
@[simp] theorem edgeChromNum_coK2Claw : coK2Claw.edgeChromNum = 5 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK2Claw)
      coK2ClawEdgeCol (by decide) (by decide)
  · have h : 4 < coK2Claw.edgeChromNum := by graph_sat
    omega

/-- **The independence number of `coK2Paw` is three.** -/
@[simp] theorem indepNum_coK2Paw : coK2Paw.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK2Paw)
    (l := ([2, 3, 4] : List (Fin 6)).map (FinEnum.equiv (α := coK2Paw.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coK2Paw` is three.** -/
@[simp] theorem cliqueNum_coK2Paw : coK2Paw.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK2Paw)
    (l := ([0, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := coK2Paw.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coK2Paw`. -/
def coK2PawCol : coK2Paw.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coK2Paw` is three.** -/
@[simp] theorem chromNum_coK2Paw : coK2Paw.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coK2PawCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coK2Paw
  rwa [cliqueNum_coK2Paw] at h

/-- A proper four-edge-colouring of `coK2Paw`, as a symmetric table on the vertices. -/
def coK2PawEdgeCol : coK2Paw.V → coK2Paw.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 3, 0, 2], ![0, 1, 0, 0, 0, 0], ![1, 3, 0, 0, 0, 0],
   ![2, 0, 0, 0, 0, 1], ![3, 2, 0, 0, 1, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coK2Paw` is four.** -/
@[simp] theorem edgeChromNum_coK2Paw : coK2Paw.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK2Paw)
      coK2PawEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coK2Paw
    rwa [show coK2Paw.maxDeg = 4 from by decide] at h

/-- **The independence number of `coK2Diamond` is three.** -/
@[simp] theorem indepNum_coK2Diamond : coK2Diamond.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coK2Diamond)
    (l := ([2, 3, 4] : List (Fin 6)).map (FinEnum.equiv (α := coK2Diamond.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coK2Diamond` is three.** -/
@[simp] theorem cliqueNum_coK2Diamond : coK2Diamond.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coK2Diamond)
    (l := ([0, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := coK2Diamond.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coK2Diamond`. -/
def coK2DiamondCol : coK2Diamond.V → Fin 3 := fun v =>
  ![0, 0, 1, 1, 1, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coK2Diamond` is three.** -/
@[simp] theorem chromNum_coK2Diamond : coK2Diamond.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coK2DiamondCol (by decide)) ?_
  have h := cliqueNum_le_chromNum coK2Diamond
  rwa [cliqueNum_coK2Diamond] at h

/-- A proper four-edge-colouring of `coK2Diamond`, as a symmetric table on the vertices. -/
def coK2DiamondEdgeCol : coK2Diamond.V → coK2Diamond.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 1, 0, 3, 2], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![2, 3, 0, 0, 0, 0], ![3, 2, 0, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coK2Diamond` is four.** -/
@[simp] theorem edgeChromNum_coK2Diamond : coK2Diamond.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coK2Diamond)
      coK2DiamondEdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coK2Diamond
    rwa [show coK2Diamond.maxDeg = 4 from by decide] at h

/-- **The independence number of `coP3P3` is two.** -/
@[simp] theorem indepNum_coP3P3 : coP3P3.indepNum = 2 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coP3P3)
    (l := ([0, 1] : List (Fin 6)).map (FinEnum.equiv (α := coP3P3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coP3P3` is four.** -/
@[simp] theorem cliqueNum_coP3P3 : coP3P3.cliqueNum = 4 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coP3P3)
    (l := ([0, 2, 3, 5] : List (Fin 6)).map (FinEnum.equiv (α := coP3P3.V)).symm)
    (by decide) (by decide)

/-- A proper four-colouring of `coP3P3`. -/
def coP3P3Col : coP3P3.V → Fin 4 := fun v =>
  ![0, 0, 1, 2, 2, 3] (FinEnum.equiv v)

/-- **The chromatic number of `coP3P3` is four.** -/
@[simp] theorem chromNum_coP3P3 : coP3P3.chromNum = 4 := by
  refine le_antisymm (chromNum_le_of_colouring coP3P3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coP3P3
  rwa [cliqueNum_coP3P3] at h

/-- A proper four-edge-colouring of `coP3P3`, as a symmetric table on the vertices. -/
def coP3P3EdgeCol : coP3P3.V → coP3P3.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 2, 0, 1], ![0, 0, 0, 3, 1, 2], ![1, 2, 3, 0, 0, 0],
   ![2, 0, 1, 0, 0, 0], ![3, 1, 2, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coP3P3` is four.** -/
@[simp] theorem edgeChromNum_coP3P3 : coP3P3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coP3P3)
      coP3P3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coP3P3
    rwa [show coP3P3.maxDeg = 4 from by decide] at h

/-- **The independence number of `coP3K3` is three.** -/
@[simp] theorem indepNum_coP3K3 : coP3K3.indepNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_indepNum_of_nodup (G := coP3K3)
    (l := ([3, 4, 5] : List (Fin 6)).map (FinEnum.equiv (α := coP3K3.V)).symm)
    (by decide) (by decide)

/-- **The clique number of `coP3K3` is three.** -/
@[simp] theorem cliqueNum_coP3K3 : coP3K3.cliqueNum = 3 := by
  refine le_antisymm (by graph_sat) ?_
  exact le_cliqueNum_of_nodup (G := coP3K3)
    (l := ([0, 2, 3] : List (Fin 6)).map (FinEnum.equiv (α := coP3K3.V)).symm)
    (by decide) (by decide)

/-- A proper three-colouring of `coP3K3`. -/
def coP3K3Col : coP3K3.V → Fin 3 := fun v =>
  ![0, 0, 1, 2, 2, 2] (FinEnum.equiv v)

/-- **The chromatic number of `coP3K3` is three.** -/
@[simp] theorem chromNum_coP3K3 : coP3K3.chromNum = 3 := by
  refine le_antisymm (chromNum_le_of_colouring coP3K3Col (by decide)) ?_
  have h := cliqueNum_le_chromNum coP3K3
  rwa [cliqueNum_coP3K3] at h

/-- A proper four-edge-colouring of `coP3K3`, as a symmetric table on the vertices. -/
def coP3K3EdgeCol : coP3K3.V → coP3K3.V → Fin 4 := fun x y =>
  ![![0, 0, 0, 1, 2, 3], ![0, 0, 0, 0, 1, 2], ![0, 0, 0, 2, 3, 1], ![1, 0, 2, 0, 0, 0],
   ![2, 1, 3, 0, 0, 0], ![3, 2, 1, 0, 0, 0]] (FinEnum.equiv x) (FinEnum.equiv y)

/-- **The edge chromatic number of `coP3K3` is four.** -/
@[simp] theorem edgeChromNum_coP3K3 : coP3K3.edgeChromNum = 4 := by
  refine le_antisymm ?_ ?_
  · rw [← IsoGraph.edgeChromNum_mk]
    exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := coP3K3)
      coP3K3EdgeCol (by decide) (by decide)
  · have h := maxDeg_le_edgeChromNum coP3K3
    rwa [show coP3K3.maxDeg = 4 from by decide] at h

end SmallGraphs
