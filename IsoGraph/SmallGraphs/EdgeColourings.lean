import IsoGraph.SmallGraphs.Extremal
-- `Fractional` re-exports `Sat`; importing it here is what puts the fractional fast path in
-- front of `graph_sat` for the whole gallery downstream of this file.
import IsoGraph.Fractional

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Edge colourings

Chromatic indices proved by exhibiting a colouring, and the class-two proofs that go with them: the
Petersen graph, the tadpole, the cocktail party graph, the hypercube and the flower snark.
-/

namespace CGraph

section
variable {G H : CGraph}

/-- The pendant colouring of `doubleStar m n`, clamped into `Fin (max m n + 1)`. -/
def doubleStarCol (m n : ℕ) (p q : (doubleStar m n).V) : Fin (max m n + 1) :=
  ⟨min (doubleStarIdx m p.1 q.1) (max m n), by omega⟩

theorem doubleStarCol_symm (m n : ℕ) (p q : (doubleStar m n).V) :
    doubleStarCol m n p q = doubleStarCol m n q p := by
  refine Fin.ext ?_
  show min (doubleStarIdx m p.1 q.1) (max m n) = min (doubleStarIdx m q.1 p.1) (max m n)
  rw [doubleStarIdx_symm]

theorem doubleStarCol_proper (m n : ℕ) (u v w : (doubleStar m n).V)
    (huv : (doubleStar m n).Adj u v = true) (huw : (doubleStar m n).Adj u w = true) (hvw : v ≠ w) :
    doubleStarCol m n u v ≠ doubleStarCol m n u w := by
  rw [doubleStar_adj_val] at huv huw
  have hvw' : v.1 ≠ w.1 := fun hh ↦ hvw (Fin.ext hh)
  have bu := u.isLt
  have bv := v.isLt
  have bw := w.isLt
  intro hcol
  have hval : min (doubleStarIdx m u.1 v.1) (max m n) =
      min (doubleStarIdx m u.1 w.1) (max m n) := congrArg Fin.val hcol
  unfold doubleStarIdx at hval
  split_ifs at hval <;> omega

/-! ### Transporting the labels to the vertices of `cocktailParty (n + 2)` -/

theorem cp_fst_lt {n : ℕ} (x : (cocktailParty (n + 2)).V) : x.1.1 < n + 2 := by
  have h := x.1.isLt
  simpa using h

theorem cp_snd_lt {n : ℕ} (x : (cocktailParty (n + 2)).V) : x.2.1 < 2 := by
  have h := x.2.isLt
  simpa using h

theorem cp_vertex_ext {n : ℕ} (x y : (cocktailParty (n + 2)).V) (h1 : x.1.1 = y.1.1)
    (h2 : x.2.1 = y.2.1) : x = y := by
  obtain ⟨i, a⟩ := x
  obtain ⟨i', b⟩ := y
  have hii : i = i' := Fin.ext h1
  subst hii
  simp only at h2
  rw [show a = b from Fin.ext h2]

/-- The edge colouring of the cocktail party graph. -/
def cpCol (n : ℕ) (x y : (cocktailParty (n + 2)).V) : Fin (2 * n + 2) :=
  ⟨min ((cpRaw n x.1.1 x.2.1 y.1.1 y.2.1).val - 1) (2 * n + 1), by omega⟩

theorem cpCol_symm (n : ℕ) (x y : (cocktailParty (n + 2)).V) : cpCol n x y = cpCol n y x := by
  refine Fin.ext ?_
  show min ((cpRaw n x.1.1 x.2.1 y.1.1 y.2.1).val - 1) (2 * n + 1)
    = min ((cpRaw n y.1.1 y.2.1 x.1.1 x.2.1).val - 1) (2 * n + 1)
  rw [cpRaw_comm]

/-- Adjacent cocktail party vertices lie in different parts. -/
theorem cp_adj_iff {n : ℕ} (x y : (cocktailParty (n + 2)).V) :
    (cocktailParty (n + 2)).Adj x y = true ↔ x.1.1 ≠ y.1.1 := by
  rw [show (cocktailParty (n + 2)).Adj x y
      = (completeMultipartite (List.replicate (n + 2) 2)).Adj x y from rfl,
    completeMultipartite_adj]
  simp [Fin.val_eq_val]

theorem cpCol_proper (n : ℕ) (u v w : (cocktailParty (n + 2)).V)
    (huv : (cocktailParty (n + 2)).Adj u v = true)
    (huw : (cocktailParty (n + 2)).Adj u w = true) (hvw : v ≠ w) : cpCol n u v ≠ cpCol n u w := by
  rw [cp_adj_iff] at huv huw
  have bu := cp_fst_lt u
  have bv := cp_fst_lt v
  have bw := cp_fst_lt w
  have cu := cp_snd_lt u
  have cv := cp_snd_lt v
  have cw := cp_snd_lt w
  have hnv : cpRaw n u.1.1 u.2.1 v.1.1 v.2.1 ≠ 0 := cpRaw_ne_zero n _ _ _ _ bu bv cu cv huv
  have hnw : cpRaw n u.1.1 u.2.1 w.1.1 w.2.1 ≠ 0 := cpRaw_ne_zero n _ _ _ _ bu bw cu cw huw
  have hlv : (cpRaw n u.1.1 u.2.1 v.1.1 v.2.1).val < 2 * n + 3 := ZMod.val_lt _
  have hlw : (cpRaw n u.1.1 u.2.1 w.1.1 w.2.1).val < 2 * n + 3 := ZMod.val_lt _
  have hpv : (cpRaw n u.1.1 u.2.1 v.1.1 v.2.1).val ≠ 0 := by
    intro hc
    exact hnv (by rw [← ZMod.natCast_zmod_val (cpRaw n u.1.1 u.2.1 v.1.1 v.2.1), hc]; simp)
  have hpw : (cpRaw n u.1.1 u.2.1 w.1.1 w.2.1).val ≠ 0 := by
    intro hc
    exact hnw (by rw [← ZMod.natCast_zmod_val (cpRaw n u.1.1 u.2.1 w.1.1 w.2.1), hc]; simp)
  intro hcol
  have hval : (cpRaw n u.1.1 u.2.1 v.1.1 v.2.1).val = (cpRaw n u.1.1 u.2.1 w.1.1 w.2.1).val := by
    have h3 : min ((cpRaw n u.1.1 u.2.1 v.1.1 v.2.1).val - 1) (2 * n + 1)
        = min ((cpRaw n u.1.1 u.2.1 w.1.1 w.2.1).val - 1) (2 * n + 1) := congrArg Fin.val hcol
    omega
  have hraw : cpRaw n u.1.1 u.2.1 v.1.1 v.2.1 = cpRaw n u.1.1 u.2.1 w.1.1 w.2.1 :=
    ZMod.val_injective _ hval
  refine hvw ?_
  unfold cpRaw at hraw
  by_cases hu : u.1.1 = 0 ∧ u.2.1 = 0
  · rw [if_pos hu, if_pos hu] at hraw
    have hv0 : ¬(v.1.1 = 0 ∧ v.2.1 = 0) := by omega
    have hw0 : ¬(w.1.1 = 0 ∧ w.2.1 = 0) := by omega
    have h4 := cpVal_inj n _ _ _ _ bv bw cv cw hv0 hw0 (cp_two_mul_inj n hraw)
    exact cp_vertex_ext v w h4.1 h4.2
  · rw [if_neg hu, if_neg hu] at hraw
    by_cases hv : v.1.1 = 0 ∧ v.2.1 = 0
    · exfalso
      have hw0 : ¬(w.1.1 = 0 ∧ w.2.1 = 0) := by
        rintro ⟨hw1, hw2⟩
        exact hvw (cp_vertex_ext v w (by omega) (by omega))
      rw [if_pos hv, if_neg hw0] at hraw
      have h5 : cpVal n u.1.1 u.2.1 = cpVal n w.1.1 w.2.1 := by
        have h2 : cpVal n u.1.1 u.2.1 + cpVal n u.1.1 u.2.1
            = cpVal n u.1.1 u.2.1 + cpVal n w.1.1 w.2.1 := by rw [← hraw]; ring
        exact add_left_cancel h2
      have h6 := cpVal_inj n _ _ _ _ bu bw cu cw hu hw0 h5
      omega
    · by_cases hw : w.1.1 = 0 ∧ w.2.1 = 0
      · exfalso
        rw [if_neg hv, if_pos hw] at hraw
        have h5 : cpVal n u.1.1 u.2.1 = cpVal n v.1.1 v.2.1 := by
          have h2 : cpVal n u.1.1 u.2.1 + cpVal n u.1.1 u.2.1
              = cpVal n u.1.1 u.2.1 + cpVal n v.1.1 v.2.1 := by rw [hraw]; ring
          exact add_left_cancel h2
        have h6 := cpVal_inj n _ _ _ _ bu bv cu cv hu hv h5
        omega
      · rw [if_neg hv, if_neg hw] at hraw
        have h4 := cpVal_inj n _ _ _ _ bv bw cv cw hv hw (add_left_cancel hraw)
        exact cp_vertex_ext v w h4.1 h4.2

def tri6Idx (s : (triangular 6).V) : ℕ :=
  tri6Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def tri6Col (x y : (triangular 6).V) : Fin 9 :=
  ⟨min ((tri6ColTable.getD (tri6Idx x) []).getD (tri6Idx y) 0) 8, by omega⟩

theorem tri6Col_symm : ∀ x y : (triangular 6).V, tri6Col x y = tri6Col y x := by
  native_decide

theorem tri6Col_proper : ∀ u v w : (triangular 6).V, (triangular 6).Adj u v = true →
    (triangular 6).Adj u w = true → v ≠ w → tri6Col u v ≠ tri6Col u w := by
  native_decide

def tri7Idx (s : (triangular 7).V) : ℕ :=
  tri7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def tri7Col (x y : (triangular 7).V) : Fin 11 :=
  ⟨min ((tri7ColTable.getD (tri7Idx x) []).getD (tri7Idx y) 0) 10, by omega⟩

theorem tri7Col_symm : ∀ x y : (triangular 7).V, tri7Col x y = tri7Col y x := by
  native_decide

theorem tri7Col_proper : ∀ u v w : (triangular 7).V, (triangular 7).Adj u v = true →
    (triangular 7).Adj u w = true → v ≠ w → tri7Col u v ≠ tri7Col u w := by
  native_decide

def kneser73Idx (s : (kneser 7 3).V) : ℕ :=
  triples7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def kneser73Col (x y : (kneser 7 3).V) : Fin 5 :=
  ⟨min ((kneser73ColTable.getD (kneser73Idx x) []).getD (kneser73Idx y) 0) 4, by omega⟩

theorem kneser73Col_symm : ∀ x y : (kneser 7 3).V, kneser73Col x y = kneser73Col y x := by
  native_decide

theorem kneser73Col_proper : ∀ u v w : (kneser 7 3).V, (kneser 7 3).Adj u v = true →
    (kneser 7 3).Adj u w = true → v ≠ w → kneser73Col u v ≠ kneser73Col u w := by
  native_decide

def johnson73Idx (s : (johnson 7 3).V) : ℕ :=
  triples7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def johnson73Col (x y : (johnson 7 3).V) : Fin 13 :=
  ⟨min ((johnson73ColTable.getD (johnson73Idx x) []).getD (johnson73Idx y) 0) 12, by omega⟩

theorem johnson73Col_symm : ∀ x y : (johnson 7 3).V, johnson73Col x y = johnson73Col y x := by
  native_decide

theorem johnson73Col_proper : ∀ u v w : (johnson 7 3).V, (johnson 7 3).Adj u v = true →
    (johnson 7 3).Adj u w = true → v ≠ w → johnson73Col u v ≠ johnson73Col u w := by
  native_decide

def rook33Idx (x : (rook 3 3).V) : ℕ := x.1.1 * 3 + x.2.1

def rook33Col (x y : (rook 3 3).V) : Fin 5 :=
  ⟨min ((rook33ColTable.getD (rook33Idx x) []).getD (rook33Idx y) 0) 4, by omega⟩

theorem rook33Col_symm : ∀ x y : (rook 3 3).V, rook33Col x y = rook33Col y x := by
  native_decide

theorem rook33Col_proper : ∀ u v w : (rook 3 3).V, (rook 3 3).Adj u v = true →
    (rook 3 3).Adj u w = true → v ≠ w → rook33Col u v ≠ rook33Col u w := by
  native_decide

def paley13Idx (x : (paley 13).V) : ℕ := x.1

def paley13Col (x y : (paley 13).V) : Fin 7 :=
  ⟨min ((paley13ColTable.getD (paley13Idx x) []).getD (paley13Idx y) 0) 6, by omega⟩

theorem paley13Col_symm : ∀ x y : (paley 13).V, paley13Col x y = paley13Col y x := by
  native_decide

theorem paley13Col_proper : ∀ u v w : (paley 13).V, (paley 13).Adj u v = true →
    (paley 13).Adj u w = true → v ≠ w → paley13Col u v ≠ paley13Col u w := by
  native_decide

/-! ## The Petersen graph is class two

The Petersen graph is cubic, so Vizing gives `χ' ≤ 4`, and the table `pet10ColTable` realises that
bound.  The lower bound is a SAT refutation on the line graph — see `four_le_edgeChromNum_petersen`
in `IsoGraph/SmallGraphs/Operators.lean`. -/

def petVerts : List (kneser 5 2).V :=
  (List.range 32).filterMap fun m ↦
    if h : (Finset.univ.filter fun i : Fin 5 ↦ m / 2 ^ i.1 % 2 = 1).card = 2 then
      some ⟨_, h⟩
    else none

def petVert0 : (kneser 5 2).V := ⟨{0, 1}, by decide⟩

def pet10Idx (s : (kneser 5 2).V) : ℕ :=
  pet10Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def pet10Col (x y : (kneser 5 2).V) : Fin 4 :=
  ⟨min ((pet10ColTable.getD (pet10Idx x) []).getD (pet10Idx y) 0) 3, by omega⟩

theorem pet10Col_symm : ∀ x y : (kneser 5 2).V, pet10Col x y = pet10Col y x := by
  native_decide

theorem pet10Col_proper : ∀ u v w : (kneser 5 2).V, (kneser 5 2).Adj u v = true →
    (kneser 5 2).Adj u w = true → v ≠ w → pet10Col u v ≠ pet10Col u w := by
  native_decide

/-! ## The automorphism group of the Petersen graph -/

/-- The ten vertices of the Petersen graph, indexed in the bitmask order of `pet10Masks`. -/
def petAt (i : Fin 10) : (kneser 5 2).V := petVerts.getD i.1 petVert0

/-- The index of a vertex of the Petersen graph in `petAt`. -/
def petIdx (v : (kneser 5 2).V) : Fin 10 := ⟨min (pet10Idx v) 9, by omega⟩

theorem petAt_petIdx : ∀ v : (kneser 5 2).V, petAt (petIdx v) = v := by native_decide

theorem petIdx_petAt : ∀ i : Fin 10, petIdx (petAt i) = i := by native_decide

/-- Adjacency of the Petersen graph as a table on the ten indices: two vertices are adjacent
exactly when their bitmasks are disjoint. -/
def petAdjT (i j : Fin 10) : Bool :=
  (pet10Masks.getD i.1 0 &&& pet10Masks.getD j.1 0) == 0

theorem petAdjT_eq : ∀ i j : Fin 10, (kneser 5 2).Adj (petAt i) (petAt j) = petAdjT i j := by
  native_decide

theorem petAdjT_map (f : kneser 5 2 ≃cg kneser 5 2) (i j : Fin 10) :
    petAdjT (petIdx (f (petAt i))) (petIdx (f (petAt j))) = petAdjT i j := by
  rw [← petAdjT_eq, petAt_petIdx, petAt_petIdx, Iso.adj_eq, petAdjT_eq]

theorem petIdx_map_ne (f : kneser 5 2 ≃cg kneser 5 2) {i j : Fin 10} (hij : i ≠ j) :
    petIdx (f (petAt i)) ≠ petIdx (f (petAt j)) := by
  intro heq
  refine hij ?_
  have h1 : f (petAt i) = f (petAt j) := by
    rw [← petAt_petIdx (f (petAt i)), ← petAt_petIdx (f (petAt j)), heq]
  have h2 : petAt i = petAt j := f.injective h1
  rw [← petIdx_petAt i, ← petIdx_petAt j, h2]

-- The six nested binders build a deep `Decidable` instance, which is what the `maxSize` wall is
-- for.  The search runs as compiled code and costs 6 856 heartbeats.
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000000 in
/-- **The stabiliser of a `3`-arc in the Petersen graph is trivial**, as a search over the six
vertices that are not on the arc `petAt 0 – petAt 5 – petAt 6 – petAt 2`.  Twelve of the forty-five
adjacency constraints already pin the six images down, so the case split is `10 ^ 6` wide and each
leaf tests at most twelve table lookups. -/
theorem petStabSearch : ∀ x1 x3 x4 x7 x8 x9 : Fin 10,
    petAdjT x4 6 = petAdjT 4 6 ∧ petAdjT 5 x7 = petAdjT 5 7 ∧ petAdjT 5 x8 = petAdjT 5 8 ∧
      petAdjT 0 x9 = petAdjT 0 9 ∧ petAdjT 2 x9 = petAdjT 2 9 ∧ petAdjT x1 x7 = petAdjT 1 7 ∧
      petAdjT x1 x9 = petAdjT 1 9 ∧ petAdjT x3 x7 = petAdjT 3 7 ∧ petAdjT x3 x8 = petAdjT 3 8 ∧
      petAdjT x4 x7 = petAdjT 4 7 ∧ petAdjT x4 x8 = petAdjT 4 8 ∧ petAdjT x4 x9 = petAdjT 4 9 →
    x1 = 1 ∧ x3 = 3 ∧ x4 = 4 ∧ x7 = 7 ∧ x8 = 8 ∧ x9 = 9 := by
  native_decide

/-- An automorphism of the Petersen graph fixing the `3`-arc `petAt 0 – petAt 5 – petAt 6 –
petAt 2` pointwise is the identity. -/
theorem petAut_fix (h : kneser 5 2 ≃cg kneser 5 2)
    (e0 : h (petAt 0) = petAt 0) (e2 : h (petAt 2) = petAt 2)
    (e5 : h (petAt 5) = petAt 5) (e6 : h (petAt 6) = petAt 6) :
    ∀ v, h v = v := by
  have hx := petAdjT_map h
  have hx0 : petIdx (h (petAt 0)) = 0 := by rw [e0, petIdx_petAt]
  have hx2 : petIdx (h (petAt 2)) = 2 := by rw [e2, petIdx_petAt]
  have hx5 : petIdx (h (petAt 5)) = 5 := by rw [e5, petIdx_petAt]
  have hx6 : petIdx (h (petAt 6)) = 6 := by rw [e6, petIdx_petAt]
  have c46 := hx 4 6
  rw [hx6] at c46
  have c57 := hx 5 7
  rw [hx5] at c57
  have c58 := hx 5 8
  rw [hx5] at c58
  have c09 := hx 0 9
  rw [hx0] at c09
  have c29 := hx 2 9
  rw [hx2] at c29
  have c17 := hx 1 7
  have c19 := hx 1 9
  have c37 := hx 3 7
  have c38 := hx 3 8
  have c47 := hx 4 7
  have c48 := hx 4 8
  have c49 := hx 4 9
  obtain ⟨k1, k3, k4, k7, k8, k9⟩ := petStabSearch
    (petIdx (h (petAt 1))) (petIdx (h (petAt 3))) (petIdx (h (petAt 4)))
    (petIdx (h (petAt 7))) (petIdx (h (petAt 8))) (petIdx (h (petAt 9)))
    ⟨c46, c57, c58, c09, c29, c17, c19, c37, c38, c47, c48, c49⟩
  have g : ∀ i : Fin 10, petIdx (h (petAt i)) = i := by
    intro i
    fin_cases i
    exacts [hx0, k1, hx2, k3, k4, hx5, hx6, k7, k8, k9]
  have hv : ∀ i : Fin 10, h (petAt i) = petAt i := by
    intro i
    rw [← petAt_petIdx (h (petAt i)), g i]
  intro v
  calc h v = h (petAt (petIdx v)) := by rw [petAt_petIdx]
    _ = petAt (petIdx v) := hv _
    _ = v := petAt_petIdx v

/-- **Two automorphisms of the Petersen graph that agree on a `3`-arc are equal.** -/
theorem petAut_ext {f g : kneser 5 2 ≃cg kneser 5 2}
    (e0 : f (petAt 0) = g (petAt 0)) (e2 : f (petAt 2) = g (petAt 2))
    (e5 : f (petAt 5) = g (petAt 5)) (e6 : f (petAt 6) = g (petAt 6)) : f = g := by
  have hcomp : ∀ v, (f.trans g.symm) v = g.symm (f v) := fun _ ↦ rfl
  have key : ∀ v, g.symm (f v) = v := by
    intro v
    rw [← hcomp]
    refine petAut_fix (f.trans g.symm) ?_ ?_ ?_ ?_ v
    · rw [hcomp, e0, RelIso.symm_apply_apply]
    · rw [hcomp, e2, RelIso.symm_apply_apply]
    · rw [hcomp, e5, RelIso.symm_apply_apply]
    · rw [hcomp, e6, RelIso.symm_apply_apply]
  refine RelIso.ext fun v ↦ ?_
  have h2 := congrArg g (key v)
  rwa [RelIso.apply_symm_apply] at h2

/-- The `3`-arcs of the Petersen graph, as index quadruples. -/
abbrev PetArc : Type :=
  {q : Fin 10 × Fin 10 × Fin 10 × Fin 10 //
    petAdjT q.1 q.2.1 = true ∧ petAdjT q.2.1 q.2.2.1 = true ∧
      petAdjT q.2.2.1 q.2.2.2 = true ∧ q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2}

theorem card_petArc : Nat.card PetArc = 120 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The `3`-arc that an automorphism sends the base arc to.  This is a faithful record of the
automorphism, which is what `autCount_kneser_five_two_le` turns into a bound. -/
def petCode (f : kneser 5 2 ≃cg kneser 5 2) : PetArc :=
  ⟨(petIdx (f (petAt 0)), petIdx (f (petAt 5)), petIdx (f (petAt 6)), petIdx (f (petAt 2))),
    (petAdjT_map f 0 5).trans (by decide), (petAdjT_map f 5 6).trans (by decide),
    (petAdjT_map f 6 2).trans (by decide), petIdx_map_ne f (by decide),
    petIdx_map_ne f (by decide)⟩

/-- **The Petersen graph has at most `120` automorphisms**: an automorphism is recorded faithfully
by the image of one fixed `3`-arc, and there are `10 · 3 · 2 · 2 = 120` `3`-arcs. -/
theorem autCount_kneser_five_two_le : (kneser 5 2).autCount ≤ 120 := by
  have : Finite (kneser 5 2 ≃cg kneser 5 2) := (kneser 5 2).instFiniteAut
  have hinj : Function.Injective petCode := by
    intro f g hfg
    have h1 := congrArg Subtype.val hfg
    have q0 : petIdx (f (petAt 0)) = petIdx (g (petAt 0)) := congrArg (fun p ↦ p.1) h1
    have q5 : petIdx (f (petAt 5)) = petIdx (g (petAt 5)) := congrArg (fun p ↦ p.2.1) h1
    have q6 : petIdx (f (petAt 6)) = petIdx (g (petAt 6)) := congrArg (fun p ↦ p.2.2.1) h1
    have q2 : petIdx (f (petAt 2)) = petIdx (g (petAt 2)) := congrArg (fun p ↦ p.2.2.2) h1
    refine petAut_ext ?_ ?_ ?_ ?_
    · rw [← petAt_petIdx (f (petAt 0)), ← petAt_petIdx (g (petAt 0)), q0]
    · rw [← petAt_petIdx (f (petAt 2)), ← petAt_petIdx (g (petAt 2)), q2]
    · rw [← petAt_petIdx (f (petAt 5)), ← petAt_petIdx (g (petAt 5)), q5]
    · rw [← petAt_petIdx (f (petAt 6)), ← petAt_petIdx (g (petAt 6)), q6]
  have := Nat.card_le_card_of_injective petCode hinj
  rwa [card_petArc] at this

/-- Distinct permutations of the five-element ground set give distinct automorphisms of the
Petersen graph. -/
theorem kneserAuto_five_two_injective : Function.Injective (kneserAuto 5 2) := by
  intro π ρ hpr
  have key : ∀ s : Finset (Fin 5), ∀ hs : s.card = 2, s.image π = s.image ρ := by
    intro s hs
    exact congrArg Subtype.val (DFunLike.congr_fun hpr ⟨s, hs⟩)
  refine Equiv.ext fun a ↦ ?_
  obtain ⟨b, c, hba, hca, hbc⟩ : ∃ b c : Fin 5, b ≠ a ∧ c ≠ a ∧ b ≠ c := by
    revert a; decide
  have h1 := key {a, b} (by rw [Finset.card_pair (Ne.symm hba)])
  have h2 := key {a, c} (by rw [Finset.card_pair (Ne.symm hca)])
  simp only [Finset.image_insert, Finset.image_singleton] at h1 h2
  have m1 : π a ∈ ({ρ a, ρ b} : Finset (Fin 5)) := by
    rw [← h1]; exact Finset.mem_insert_self _ _
  have m2 : π a ∈ ({ρ a, ρ c} : Finset (Fin 5)) := by
    rw [← h2]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.1 m1 with h | h
  · exact h
  · rcases Finset.mem_insert.1 m2 with h' | h'
    · exact h'
    · rw [Finset.mem_singleton] at h h'
      exact absurd (ρ.injective (h.symm.trans h')) hbc

theorem le_autCount_kneser_five_two : 120 ≤ (kneser 5 2).autCount := by
  have : Finite (kneser 5 2 ≃cg kneser 5 2) := (kneser 5 2).instFiniteAut
  have h := Nat.card_le_card_of_injective _ kneserAuto_five_two_injective
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rwa [hc] at h

/-- **The Petersen graph has exactly `120` automorphisms**: its automorphism group is the
symmetric group `S₅` acting on the five-element ground set of `K(5, 2)`. -/
theorem autCount_kneser_five_two : (kneser 5 2).autCount = 120 :=
  le_antisymm autCount_kneser_five_two_le le_autCount_kneser_five_two

/-! ### The tadpole -/

/-- The cycle part of a tadpole is a copy of `cycle m`. -/
theorem cycle_adj_of_tadpole_adj {m k : ℕ} {u v : (tadpole m k).V} (hu : u.1 < m) (hv : v.1 < m)
    (h : (tadpole m k).Adj u v = true) :
    (cycle m).Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩ = true := by
  rw [tadpole_adj_val] at h
  simp only [List.mem_append, mem_cycleEdges, mem_legEdges] at h
  rw [cycle_adj_val]
  simp only [mod_succ_norm hu, mod_succ_norm hv]
  refine ⟨by omega, ?_⟩
  split_ifs <;> omega

theorem tadpole_adj_of_cycle_adj {m k : ℕ} {u v : (cycle m).V} {u' v' : (tadpole m k).V}
    (hu : u'.1 = u.1) (hv : v'.1 = v.1) (h : (cycle m).Adj u v = true) :
    (tadpole m k).Adj u' v' = true := by
  have hul := u.isLt
  have hvl := v.isLt
  rw [cycle_adj_val] at h
  obtain ⟨hne, h⟩ := h
  rw [mod_succ_norm hul, mod_succ_norm hvl] at h
  rw [tadpole_adj_val]
  refine ⟨by omega, ?_⟩
  rw [List.mem_append, List.mem_append]
  simp only [mem_cycleEdges]
  rcases h with h | h
  · exact Or.inl (Or.inl (by split_ifs at h <;> omega))
  · exact Or.inr (Or.inl (by split_ifs at h <;> omega))

/-- A vertex on the leg of a tadpole has at most one neighbour below it. -/
theorem tadpole_high_nbr_unique {m k : ℕ} {x a b : (tadpole m k).V} (hx : m ≤ x.1)
    (ha : (tadpole m k).Adj x a = true) (hb : (tadpole m k).Adj x b = true)
    (hax : a.1 ≤ x.1) (hbx : b.1 ≤ x.1) : a = b := by
  rw [tadpole_adj_val] at ha hb
  simp only [List.mem_append, mem_cycleEdges, mem_legEdges] at ha hb
  exact Fin.ext (by omega)

/-- A cycle with a tail has as many edges as vertices, so it cannot be a tree. -/
@[toIsoGraph]
theorem not_isAcyclic_tadpole (m k : ℕ) : ¬ (tadpole (m + 3) k).IsAcyclic :=
  not_isAcyclic_of_map (G := cycle (m + 3)) (fun v ↦ ⟨v.1, by have := v.isLt; omega⟩)
    (fun a b hab ↦ Fin.ext (by simpa using congrArg Fin.val hab))
    (fun _ _ hxy ↦ tadpole_adj_of_cycle_adj rfl rfl hxy) (not_isAcyclic_cycle m)

/-- **The girth of a tadpole is the length of its cycle**: the leg contributes no cycle. -/
@[toIsoGraph]
theorem girth_tadpole (m k : ℕ) : (tadpole (m + 3) k).girth = m + 3 := by
  refine le_antisymm ?_ ?_
  · have h := girth_le_card_of_map (G := cycle (m + 3)) (H := tadpole (m + 3) k)
      (fun v ↦ ⟨v.1, by have := v.isLt; omega⟩)
      (fun a b hab ↦ Fin.ext (by simpa using congrArg Fin.val hab))
      (fun _ _ hxy ↦ tadpole_adj_of_cycle_adj rfl rfl hxy) (not_isAcyclic_cycle m)
    rwa [card_cycle] at h
  · refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_)
      (not_isAcyclic_tadpole m k)
    have hlow : ∀ a ∈ u :: vs, a.1 < m + 3 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨w, hw, hwM⟩ := hcon
      obtain ⟨x, hx, hxmax⟩ := exists_max_weight (fun v : (tadpole (m + 3) k).V ↦ v.1) u vs
      obtain ⟨a, b, ha, hb, hab, hxa, hxb⟩ := cycleList_two_nbrs h2 hnd hch hcl hx
      exact hab (tadpole_high_nbr_unique (Nat.le_trans hwM (hxmax w hw)) hxa hxb
        (hxmax a ha) (hxmax b hb))
    exact no_short_cycleList_of_labels (H := tadpole (m + 3) k) (by omega) (fun v ↦ v.1) u vs
      hlow (fun a _ b _ hab ↦ Fin.ext hab)
      (fun a ha b hb hadj _ _ ↦ cycle_adj_of_tadpole_adj (hlow a ha) (hlow b hb) hadj)
      h2 hlt hnd hch hcl

/-- Every edge at a pendant vertex is a pendant edge. -/
theorem cyclePendant_pendant_edge {m : ℕ} {ks : List ℕ} (hks : ks.length ≤ m)
    {x a : (cyclePendant m ks).V} (hx : m ≤ x.1)
    (ha : (cyclePendant m ks).Adj x a = true) : (a.1, x.1) ∈ pendantEdges 0 m ks := by
  rw [cyclePendant_adj_val] at ha
  obtain ⟨hne, h⟩ := ha
  rw [List.mem_append, List.mem_append] at h
  rcases h with (hc | hp) | (hc | hp)
  · rw [mem_cycleEdges] at hc; omega
  · have := mem_pendantEdges_bound 0 m ks x.1 a.1 hp; omega
  · rw [mem_cycleEdges] at hc; omega
  · exact hp

/-- A pendant vertex has exactly one neighbour. -/
theorem cyclePendant_high_nbr_unique {m : ℕ} {ks : List ℕ} (hks : ks.length ≤ m)
    {x a b : (cyclePendant m ks).V} (hx : m ≤ x.1)
    (ha : (cyclePendant m ks).Adj x a = true) (hb : (cyclePendant m ks).Adj x b = true) :
    a = b :=
  Fin.ext (pendantEdges_unique_owner 0 m ks a.1 b.1 x.1
    (cyclePendant_pendant_edge hks hx ha) (cyclePendant_pendant_edge hks hx hb))

theorem cycle_adj_of_cyclePendant_adj {m : ℕ} {ks : List ℕ} {u v : (cyclePendant m ks).V}
    (hu : u.1 < m) (hv : v.1 < m) (h : (cyclePendant m ks).Adj u v = true) :
    (cycle m).Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩ = true := by
  rw [cyclePendant_adj_val] at h
  obtain ⟨hne, h⟩ := h
  rw [List.mem_append, List.mem_append] at h
  rw [cycle_adj_val]
  simp only [mod_succ_norm hu, mod_succ_norm hv]
  refine ⟨hne, ?_⟩
  rcases h with (hc | hp) | (hc | hp)
  · rw [mem_cycleEdges] at hc; split_ifs <;> omega
  · exfalso; have := mem_pendantEdges_bound 0 m ks u.1 v.1 hp; omega
  · rw [mem_cycleEdges] at hc; split_ifs <;> omega
  · exfalso; have := mem_pendantEdges_bound 0 m ks v.1 u.1 hp; omega

theorem cyclePendant_adj_of_cycle_adj {m : ℕ} {ks : List ℕ} {u v : (cycle m).V}
    {u' v' : (cyclePendant m ks).V} (hu : u'.1 = u.1) (hv : v'.1 = v.1)
    (h : (cycle m).Adj u v = true) : (cyclePendant m ks).Adj u' v' = true := by
  have hul := u.isLt
  have hvl := v.isLt
  rw [cycle_adj_val] at h
  obtain ⟨hne, h⟩ := h
  simp only [mod_succ_norm hul, mod_succ_norm hvl] at h
  rw [cyclePendant_adj_val]
  refine ⟨by omega, ?_⟩
  rw [List.mem_append, List.mem_append]
  simp only [mem_cycleEdges]
  rcases h with h | h
  · exact Or.inl (Or.inl (by split_ifs at h <;> omega))
  · exact Or.inr (Or.inl (by split_ifs at h <;> omega))

theorem not_isAcyclic_cyclePendant (m : ℕ) (ks : List ℕ) :
    ¬ (cyclePendant (m + 3) ks).IsAcyclic :=
  not_isAcyclic_of_map (G := cycle (m + 3)) (fun v ↦ ⟨v.1, by have := v.isLt; omega⟩)
    (fun a b hab ↦ Fin.ext (by simpa using congrArg Fin.val hab))
    (fun _ _ hxy ↦ cyclePendant_adj_of_cycle_adj rfl rfl hxy) (not_isAcyclic_cycle m)

/-- **The girth of a cycle with pendant vertices is the length of the cycle.** -/
@[toIsoGraph]
theorem girth_cyclePendant (m : ℕ) (ks : List ℕ) (hks : ks.length ≤ m + 3) :
    (cyclePendant (m + 3) ks).girth = m + 3 := by
  refine le_antisymm ?_ ?_
  · have hle := girth_le_card_of_map (G := cycle (m + 3)) (H := cyclePendant (m + 3) ks)
      (fun v ↦ ⟨v.1, by have := v.isLt; omega⟩)
      (fun a b hab ↦ Fin.ext (by simpa using congrArg Fin.val hab))
      (fun _ _ hxy ↦ cyclePendant_adj_of_cycle_adj rfl rfl hxy) (not_isAcyclic_cycle m)
    rwa [card_cycle] at hle
  · refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_)
      (not_isAcyclic_cyclePendant m ks)
    have hlow : ∀ a ∈ u :: vs, a.1 < m + 3 := by
      intro a ha
      by_contra hcon
      push Not at hcon
      obtain ⟨p, q, hp, hq, hpq, hap, haq⟩ := cycleList_two_nbrs h2 hnd hch hcl ha
      exact hpq (cyclePendant_high_nbr_unique hks hcon hap haq)
    exact no_short_cycleList_of_labels (H := cyclePendant (m + 3) ks) (by omega) (fun v ↦ v.1) u vs
      hlow (fun a _ b _ hab ↦ Fin.ext hab)
      (fun a ha b hb hadj _ _ ↦ cycle_adj_of_cyclePendant_adj (hlow a ha) (hlow b hb) hadj)
      h2 hlt hnd hch hcl

/-- The grid contains `⌊mn/2⌋` disjoint edges. -/
theorem le_indepNum_lineGraph_grid (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (path m □g path n)).indepNum := by
  refine le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
  intro p q h
  rw [cartesianProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (path_adj_val n p.2 q.2).2 ⟨by omega, h2⟩⟩
  · exact Or.inr ⟨(path_adj_val m p.1 q.1).2 ⟨by omega, Or.inl h2⟩, h1⟩

/-- The king graph contains `⌊mn/2⌋` disjoint edges: the grid's own matching. -/
theorem le_indepNum_lineGraph_king (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (path m ⊠g path n)).indepNum := by
  refine le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
  intro p q h
  rw [strongProduct_adj]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨fun he ↦ ?_, Or.inl h1, Or.inr ((path_adj_val n p.2 q.2).2 ⟨by omega, h2⟩)⟩
    rw [he] at h2
    omega
  · refine ⟨fun he ↦ ?_, Or.inr ((path_adj_val m p.1 q.1).2 ⟨by omega, Or.inl h2⟩), Or.inl h1⟩
    rw [he] at h2
    omega

/-- The torus contains `⌊mn/2⌋` disjoint edges: it contains the grid, so the boustrophedon
matching of `le_indepNum_lineGraph_board` works unchanged. -/
theorem le_indepNum_lineGraph_torus (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (cycle m □g cycle n)).indepNum := by
  refine le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
  intro p q h
  rw [cartesianProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have hp1 := p.1.isLt
  have hq1 := q.1.isLt
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, (cycle_adj_val n p.2 q.2).2 ⟨by omega, ?_⟩⟩
    rcases h2 with h2 | h2
    · exact Or.inl (by rw [h2]; exact Nat.mod_eq_of_lt hq2)
    · exact Or.inr (by rw [h2]; exact Nat.mod_eq_of_lt hp2)
  · exact Or.inr ⟨(cycle_adj_val m p.1 q.1).2
      ⟨by omega, Or.inl (by rw [h2]; exact Nat.mod_eq_of_lt hq1)⟩, h1⟩

/-- The cylinder contains `⌊mn/2⌋` disjoint edges, again by the grid's matching. -/
theorem le_indepNum_lineGraph_cylinder (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (cycle m □g path n)).indepNum := by
  refine le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
  intro p q h
  rw [cartesianProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have hp1 := p.1.isLt
  have hq1 := q.1.isLt
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (path_adj_val n p.2 q.2).2 ⟨by omega, h2⟩⟩
  · exact Or.inr ⟨(cycle_adj_val m p.1 q.1).2
      ⟨by omega, Or.inl (by rw [h2]; exact Nat.mod_eq_of_lt hq1)⟩, h1⟩

/-! ### The automorphism group of the hypercube -/

/-- Two hypercube vertices are adjacent exactly when they differ in a single coordinate. -/
theorem hypercube_adj_iff {n : ℕ} (x y : Fin n → Bool) :
    (hypercube n).Adj x y = true ↔ ∃ i, x i ≠ y i ∧ ∀ k, k ≠ i → x k = y k := by
  rw [hypercube_adj, beq_iff_eq, Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, fun k hk ↦ ?_⟩
    · have hmem : i ∈ Finset.univ.filter fun t ↦ x t ≠ y t := by
        rw [hi]; exact Finset.mem_singleton_self i
      exact (Finset.mem_filter.1 hmem).2
    · by_contra hne
      have hmem : k ∈ Finset.univ.filter fun t ↦ x t ≠ y t :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
      rw [hi, Finset.mem_singleton] at hmem
      exact hk hmem
  · rintro ⟨i, hne, hrest⟩
    refine ⟨i, Finset.ext fun k ↦ ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h ↦ by by_contra hk; exact h (hrest k hk), fun h ↦ h ▸ hne⟩

/-- The same, phrased as a single flipped bit. -/
theorem hypercube_adj_iff_update {n : ℕ} (x y : Fin n → Bool) :
    (hypercube n).Adj x y = true ↔ ∃ i, y = Function.update x i (!x i) := by
  rw [hypercube_adj_iff]
  constructor
  · rintro ⟨i, hne, hrest⟩
    refine ⟨i, funext fun k ↦ ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      revert hne; cases x k <;> cases y k <;> simp
    · rw [Function.update_of_ne hk]
      exact (hrest k hk).symm
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_, fun k hk ↦ ?_⟩
    · rw [Function.update_self]; cases x i <;> simp
    · rw [Function.update_of_ne hk]

/-- Flipping one coordinate moves to a neighbour. -/
theorem hypercube_adj_update {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) (hb : x i ≠ b) :
    (hypercube n).Adj x (Function.update x i b) = true :=
  (hypercube_adj_iff x _).2
    ⟨i, by rwa [Function.update_self], fun k hk ↦ by rw [Function.update_of_ne hk]⟩

/-- **Two vertices of the hypercube at distance two have exactly two common neighbours.**  If `u`
and `v` differ precisely in the coordinates `i` and `j`, anything adjacent to both is `u` with the
`i`-th bit changed to `v`'s or `u` with the `j`-th bit changed to `v`'s. -/
theorem hypercube_common {n : ℕ} (u v y : Fin n → Bool) (i j : Fin n) (hij : i ≠ j)
    (hi : u i ≠ v i) (hj : u j ≠ v j) (hrest : ∀ k, k ≠ i → k ≠ j → u k = v k)
    (h1 : (hypercube n).Adj y u = true) (h2 : (hypercube n).Adj y v = true) :
    y = Function.update u i (v i) ∨ y = Function.update u j (v j) := by
  obtain ⟨a, hane, harest⟩ := (hypercube_adj_iff y u).1 h1
  obtain ⟨b, hbne, hbrest⟩ := (hypercube_adj_iff y v).1 h2
  have key : ∀ c : Fin n, y c ≠ u c → (∀ k, k ≠ c → y k = u k) → u c ≠ v c →
      y = Function.update u c (v c) := by
    intro c k1 k2 k3
    funext k
    by_cases hk : k = c
    · subst hk
      rw [Function.update_self]
      revert k1 k3; cases y k <;> cases u k <;> cases v k <;> simp
    · rw [Function.update_of_ne hk]; exact k2 k hk
  have hab : a = i ∨ a = j := by
    by_contra hc
    push Not at hc
    have hyi : y i = u i := harest i (Ne.symm hc.1)
    have hyj : y j = u j := harest j (Ne.symm hc.2)
    by_cases hb : b = i
    · exact hj (hyj.symm.trans (hbrest j (by rw [hb]; exact Ne.symm hij)))
    · exact hi (hyi.symm.trans (hbrest i (Ne.symm hb)))
  rcases hab with rfl | rfl
  · exact Or.inl (key _ hane harest hi)
  · exact Or.inr (key _ hane harest hj)

/-- Clearing a coordinate deletes it from the support. -/
theorem hypercube_filter_update_false {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (Finset.univ.filter fun t ↦ Function.update x i false t = true)
      = (Finset.univ.filter fun t ↦ x t = true).erase i := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases ht : t = i
  · subst ht; simp
  · simp [ht]

/-- Clearing a set coordinate shrinks the support by one. -/
theorem hypercube_card_update_false {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    (Finset.univ.filter fun t ↦ Function.update x i false t = true).card
      = (Finset.univ.filter fun t ↦ x t = true).card - 1 := by
  rw [hypercube_filter_update_false]
  exact Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)

/-- **The hypercube is rigid above the weight-one strings.**  An automorphism fixing the zero
string and every string of weight one is the identity: induct on the weight, and read a vertex of
weight `k ≥ 2` off as the common neighbour of two of its weight-`k - 1` neighbours that is not the
weight-`k - 2` vertex below both, which the induction hypothesis has already pinned down. -/
theorem hypercube_aut_eq_id {n : ℕ} (f : hypercube n ≃cg hypercube n)
    (h0 : f (fun _ ↦ false) = fun _ ↦ false)
    (he : ∀ j : Fin n, f (fun k ↦ decide (k = j)) = fun k ↦ decide (k = j)) (x : Fin n → Bool) :
    f x = x := by
  classical
  suffices H : ∀ m (y : Fin n → Bool),
      (Finset.univ.filter fun t ↦ y t = true).card ≤ m → f y = y from H _ x le_rfl
  intro m
  induction m with
  | zero =>
    intro y hy
    have hy0 : y = fun _ ↦ false := by
      funext t
      by_contra ht
      have hmem : t ∈ Finset.univ.filter fun s ↦ y s = true :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using ht⟩
      have := Finset.card_pos.2 ⟨t, hmem⟩
      omega
    rw [hy0]; exact h0
  | succ m ih =>
    intro y hy
    by_cases hle : (Finset.univ.filter fun t ↦ y t = true).card ≤ m
    · exact ih y hle
    have hcard : (Finset.univ.filter fun t ↦ y t = true).card = m + 1 := by omega
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard
      have hy1 : y = fun k ↦ decide (k = j) := by
        funext t
        by_cases ht : t = j
        · subst ht
          have hmem : t ∈ Finset.univ.filter fun s ↦ y s = true :=
            hj ▸ Finset.mem_singleton_self t
          simpa using (Finset.mem_filter.1 hmem).2
        · have hmem : t ∉ Finset.univ.filter fun s ↦ y s = true := by
            rw [hj]; simpa using ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hmem
          simp [ht, hmem]
      rw [hy1]; exact he j
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1
      (by omega : 1 < (Finset.univ.filter fun t ↦ y t = true).card)
    have hyi : y i = true := (Finset.mem_filter.1 hi).2
    have hyj : y j = true := (Finset.mem_filter.1 hj).2
    obtain ⟨u, hu⟩ : ∃ u : Fin n → Bool, u = Function.update y i false := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin n → Bool, v = Function.update y j false := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : Fin n → Bool, w = Function.update u j false := ⟨_, rfl⟩
    have hui : u i = false := by rw [hu, Function.update_self]
    have hvj : v j = false := by rw [hv, Function.update_self]
    have huk : ∀ k, k ≠ i → u k = y k := fun k hk ↦ by rw [hu, Function.update_of_ne hk]
    have hvk : ∀ k, k ≠ j → v k = y k := fun k hk ↦ by rw [hv, Function.update_of_ne hk]
    have huj : u j = true := by rw [huk j (Ne.symm hij)]; exact hyj
    have hcu : (Finset.univ.filter fun t ↦ u t = true).card ≤ m := by
      rw [hu, hypercube_card_update_false y i hyi, hcard]
      omega
    have hcv : (Finset.univ.filter fun t ↦ v t = true).card ≤ m := by
      rw [hv, hypercube_card_update_false y j hyj, hcard]
      omega
    have hcw : (Finset.univ.filter fun t ↦ w t = true).card ≤ m := by
      rw [hw, hypercube_card_update_false u j huj]; omega
    have hfu : f u = u := ih u hcu
    have hfv : f v = v := ih v hcv
    have hfw : f w = w := ih w hcw
    have hA : (hypercube n).Adj (f y) u = true := by
      rw [← hfu, f.adj_eq, hu]
      exact hypercube_adj_update y i false (by rw [hyi]; simp)
    have hB : (hypercube n).Adj (f y) v = true := by
      rw [← hfv, f.adj_eq, hv]
      exact hypercube_adj_update y j false (by rw [hyj]; simp)
    have hci : u i ≠ v i := by rw [hui, hvk i hij, hyi]; simp
    have hcj : u j ≠ v j := by rw [huj, hvj]; simp
    have hcr : ∀ k, k ≠ i → k ≠ j → u k = v k := fun k h1 h2 ↦ by rw [huk k h1, hvk k h2]
    rcases hypercube_common u v (f y) i j hij hci hcj hcr hA hB with hc | hc
    · rw [hc]
      funext k
      by_cases hk : k = i
      · subst hk; rw [Function.update_self]; exact hvk k hij
      · rw [Function.update_of_ne hk]; exact huk k hk
    · exfalso
      have hfyw : f y = w := by rw [hc, hvj, hw]
      have hyw : y = w := f.injective (by rw [hfyw, hfw])
      have hcon : y i = w i := by rw [← hyw]
      rw [hw, Function.update_of_ne hij, hui, hyi] at hcon
      simp at hcon

/-- The automorphism of the hypercube built from a coordinate permutation and a translation. -/
def cubeAutOf (n : ℕ) (p : Equiv.Perm (Fin n) × (Fin n → Bool)) : hypercube n ≃cg hypercube n :=
  (cubeCoord n p.1).trans (cubeXor n p.2)

theorem cubeAutOf_apply (n : ℕ) (p : Equiv.Perm (Fin n) × (Fin n → Bool)) (x : Fin n → Bool)
    (i : Fin n) : cubeAutOf n p x i = (x (p.1.symm i) ^^ p.2 i) := rfl

theorem cubeAutOf_zero (n : ℕ) (p : Equiv.Perm (Fin n) × (Fin n → Bool)) :
    cubeAutOf n p (fun _ ↦ false) = p.2 := by
  funext i; rw [cubeAutOf_apply]; simp

theorem cubeAutOf_unit (n : ℕ) (p : Equiv.Perm (Fin n) × (Fin n → Bool)) (j : Fin n) :
    cubeAutOf n p (fun k ↦ decide (k = j)) = fun i ↦ (decide (i = p.1 j) ^^ p.2 i) := by
  funext i
  rw [cubeAutOf_apply]
  congr 1
  rw [decide_eq_decide]
  exact Equiv.symm_apply_eq p.1

theorem cubeAutOf_injective (n : ℕ) : Function.Injective (cubeAutOf n) := by
  rintro ⟨τ, d⟩ ⟨τ', d'⟩ h
  have h0 : ∀ x : Fin n → Bool, cubeAutOf n (τ, d) x = cubeAutOf n (τ', d') x := fun x ↦ by rw [h]
  have hd : d = d' := by
    have := h0 (fun _ ↦ false)
    rwa [cubeAutOf_zero, cubeAutOf_zero] at this
  subst hd
  have hτ : τ = τ' := by
    refine Equiv.ext fun j ↦ ?_
    have hj := congrFun (h0 (fun k ↦ decide (k = j))) (τ j)
    rw [cubeAutOf_unit, cubeAutOf_unit] at hj
    simp only [decide_true] at hj
    have hdec : decide (τ j = τ' j) = true := by
      revert hj; cases d (τ j) <;> cases hq : decide (τ j = τ' j) <;> simp
    exact of_decide_eq_true hdec
  rw [hτ]

theorem cubeAutOf_surjective (n : ℕ) : Function.Surjective (cubeAutOf n) := by
  classical
  intro f
  have hzu : ∀ j : Fin n,
      (hypercube n).Adj (fun _ ↦ false) (fun k ↦ decide (k = j)) = true := fun j ↦
    (hypercube_adj_iff _ _).2 ⟨j, by simp, fun k hk ↦ by simp [hk]⟩
  have hstep : ∀ j : Fin n, ∃ i, f (fun k ↦ decide (k = j))
      = Function.update (f fun _ ↦ false) i (!(f fun _ ↦ false) i) := by
    intro j
    rw [← hypercube_adj_iff_update, f.adj_eq]
    exact hzu j
  choose σ hσ using hstep
  have hσinj : Function.Injective σ := by
    intro j l hjl
    have hfj : f (fun k ↦ decide (k = j)) = f (fun k ↦ decide (k = l)) := by
      rw [hσ j, hσ l, hjl]
    have := f.injective hfj
    have hj := congrFun this j
    simpa using hj
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin n), ∀ j, τ j = σ j :=
    ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj), fun _ ↦ rfl⟩
  refine ⟨(τ, f fun _ ↦ false), ?_⟩
  have hg0 : cubeAutOf n (τ, f fun _ ↦ false) (fun _ ↦ false) = f (fun _ ↦ false) :=
    cubeAutOf_zero n _
  have hgu : ∀ j : Fin n, cubeAutOf n (τ, f fun _ ↦ false) (fun k ↦ decide (k = j))
      = f (fun k ↦ decide (k = j)) := by
    intro j
    rw [cubeAutOf_unit, hσ j, hτ j]
    funext i
    by_cases hi : i = σ j
    · subst hi; rw [Function.update_self]; simp
    · rw [Function.update_of_ne hi]; simp [hi]
  set g := cubeAutOf n (τ, f fun _ ↦ false) with hgdef
  have hk : ∀ x, (f.trans g.symm) x = x := by
    refine hypercube_aut_eq_id (f.trans g.symm) ?_ ?_
    · show g.symm (f fun _ ↦ false) = fun _ ↦ false
      rw [← hg0]
      exact g.symm_apply_apply _
    · intro j
      show g.symm (f fun k ↦ decide (k = j)) = fun k ↦ decide (k = j)
      rw [← hgu j]
      exact g.symm_apply_apply _
  refine DFunLike.ext _ _ fun x ↦ ?_
  have := hk x
  show g x = f x
  have hx : g.symm (f x) = x := this
  conv_lhs => rw [← hx]
  exact g.apply_symm_apply _

end

end CGraph

namespace NamedGraphs

open CGraph

/-! ## The flower snark is class two

`flowerSnark` is cubic, so Vizing gives `χ' ≤ 4`, and `flowerSnarkColTable` realises that bound.
The lower bound is where the exhaustive method used for the Petersen graph stops: thirty edges over
three colours is a `3 ^ 30` case split.  Instead the goal goes to `graph_sat`, which bit-blasts the
line graph — twenty bits of colour class per edge — and asks a SAT solver, and the refutation comes
back in seconds. -/

/-- A proper `4`-edge-colouring of the flower snark `J₅`, as a symmetric twenty by twenty table;
the entries off the edge set are `0`. -/
def flowerSnarkColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table `flowerSnarkColTable` read as a colouring of the edges, clamped into `Fin 4`. -/
def flowerSnarkCol (x y : flowerSnark.V) : Fin 4 :=
  ⟨min ((flowerSnarkColTable.getD x.1 []).getD y.1 0) 3, by omega⟩

theorem flowerSnarkCol_symm : ∀ x y : flowerSnark.V, flowerSnarkCol x y = flowerSnarkCol y x := by
  native_decide

theorem flowerSnarkCol_proper : ∀ u v w : flowerSnark.V, flowerSnark.Adj u v = true →
    flowerSnark.Adj u w = true → v ≠ w → flowerSnarkCol u v ≠ flowerSnarkCol u w := by
  native_decide

theorem edgeChromNum_flowerSnark_le : flowerSnark.edgeChromNum ≤ 4 := by
  rw [← IsoGraph.edgeChromNum_mk]
  exact IsoGraph.edgeChromNum_mk_le_of_colouring (G := flowerSnark)
    flowerSnarkCol flowerSnarkCol_symm flowerSnarkCol_proper

/-- **The flower snark `J₅` is a snark**: it is cubic, but three colours do not suffice for its
thirty edges.  The refutation is a SAT proof, replayed through `bv_decide`'s LRAT checker. -/
theorem four_le_edgeChromNum_flowerSnark : 4 ≤ flowerSnark.edgeChromNum := by
  show 3 < flowerSnark.edgeChromNum
  graph_sat native

/-- **The chromatic index of the flower snark is four.** -/
@[simp] theorem edgeChromNum_flowerSnark : flowerSnark.edgeChromNum = 4 :=
  le_antisymm edgeChromNum_flowerSnark_le four_le_edgeChromNum_flowerSnark

end NamedGraphs

namespace IsoGraph

/-- **The matching number of a torus**: `ν(Cₘ □ Cₙ) = ⌊mn/2⌋`.  The torus contains the grid, so
it inherits the boustrophedon matching, and `2ν ≤ n` is the matching bound. -/
@[simp] theorem matchNum_cartesianProduct_cycle (m n : ℕ) :
    (cycle m □g cycle n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (cycle m □g cycle n).two_mul_matchNum_le_V
    rw [V_cartesianProduct, V_cycle, V_cycle] at h
    omega
  · rw [matchNum_eq, cycle_def, cycle_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_torus m n

/-- **The matching number of a cylinder**: `ν(Cₘ □ Pₙ) = ⌊mn/2⌋`. -/
@[simp] theorem matchNum_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle m □g path n).matchNum = m * n / 2 := by
  refine le_antisymm ?_ ?_
  · have h := (cycle m □g path n).two_mul_matchNum_le_V
    rw [V_cartesianProduct, V_cycle, V_path] at h
    omega
  · rw [matchNum_eq, cycle_def, path_def, cartesianProduct_mk, lineGraph_mk, indepNum_mk]
    exact CGraph.le_indepNum_lineGraph_cylinder m n

end IsoGraph
