import IsoGraph.Values.Identities.Automorphisms
import IsoGraph.ForMathlib.List
import IsoGraph.ForMathlib.Nat

/-!
# Edge colourings, the Petersen graph, and the girth of the cycles

The edge chromatic numbers that need an explicit colouring: the double star, the Grötzsch graph,
the cocktail party graphs (class one), the odd-order regular graphs (class two, by parity), and the
Petersen graph, whose class-two proof is the exhaustive one.  The automorphism group of the
Petersen graph is computed here too, since it is the same `native_decide`.

The module closes with the girth of the cycles and of the decorated cycles, and with the
independence, covering and domination numbers of the grid and the king graph.
-/

set_option autoImplicit false

namespace CGraph

variable {G H : CGraph}

/-! ### The double star and the Grötzsch graph

Two more class-one graphs, by two more explicit colourings.  The double star is a tree, so nothing
but the pendant edges at each hub can clash; the Grötzsch graph is small enough to hand the
properness check to the kernel. -/

/-- The colour of the edge between vertices `a` and `b` of `doubleStar m n`, as a natural: the
central edge gets `0`, the `i`-th pendant of the left hub gets `i + 1`, and the `j`-th pendant of
the right hub gets `j + 1`.  Off the edge set the value is junk. -/
def doubleStarIdx (m a b : ℕ) : ℕ :=
  if a = 0 then b - 1
  else if b = 0 then a - 1
  else if a = 1 then b - 1 - m
  else if b = 1 then a - 1 - m
  else 0

theorem doubleStarIdx_symm (m a b : ℕ) : doubleStarIdx m a b = doubleStarIdx m b a := by
  unfold doubleStarIdx
  split_ifs <;> omega

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

/-- A proper five-edge-colouring of the Grötzsch graph, as a symmetric table indexed by
`0–4` (the pentagon), `5–9` (their Mycielski copies) and `10` (the apex).  Off the edge set the
entries are junk zeroes. -/
def grotzschColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0],
   [0, 0, 1, 0, 0, 2, 0, 3, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 3, 0, 2, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 4, 0, 1, 0],
   [1, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0],
   [2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3],
   [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4],
   [0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0]]

/-- The indexing of `grotzschColTable` as a function on the vertices themselves. -/
def grotzschIdx : (mycielskian (cycle 5)).V → ℕ
  | none => 10
  | some (Sum.inl a) => a.1
  | some (Sum.inr a) => 5 + a.1

/-- The five-edge-colouring of the Grötzsch graph read off `grotzschColTable`. -/
def grotzschCol (x y : (mycielskian (cycle 5)).V) : Fin 5 :=
  ⟨min ((grotzschColTable.getD (grotzschIdx x) []).getD (grotzschIdx y) 0) 4, by omega⟩

theorem grotzschCol_symm : ∀ x y : (mycielskian (cycle 5)).V,
    grotzschCol x y = grotzschCol y x := by native_decide

theorem grotzschCol_proper : ∀ u v w : (mycielskian (cycle 5)).V,
    (mycielskian (cycle 5)).Adj u v = true → (mycielskian (cycle 5)).Adj u w = true → v ≠ w →
    grotzschCol u v ≠ grotzschCol u w := by native_decide

/-- The five Mycielski shadows of the Grötzsch graph.  They are pairwise non-adjacent, and no
independent set is larger. -/
def grotzschShadows : Finset (mycielskian (cycle 5)).V :=
  Finset.image (fun i : Fin 5 => (some (Sum.inr i) : (mycielskian (cycle 5)).V)) Finset.univ

theorem isMaximumIndepSet_grotzschShadows :
    (mycielskian (cycle 5)).toSimple.IsMaximumIndepSet grotzschShadows := by
  rw [SimpleGraph.isMaximumIndepSet_iff]
  native_decide

theorem card_grotzschShadows : grotzschShadows.card = 5 := by decide

theorem indepNum_mycielskian_cycle_five : (mycielskian (cycle 5)).indepNum = 5 := by
  have h := SimpleGraph.maximumIndepSet_card_eq_indepNum _ isMaximumIndepSet_grotzschShadows
  rw [show (mycielskian (cycle 5)).indepNum = (mycielskian (cycle 5)).toSimple.indepNum from rfl,
    ← h, card_grotzschShadows]

/-! ## The cocktail party graph is class one

`K_{(n+2)×2}` is `K_{2n+4}` minus a perfect matching.  Label the vertices of `K_{2n+4}` by
`ZMod (2n+3) ∪ {∞}` and colour the edge `{a, b}` by `a + b` and the edge `{a, ∞}` by `2a`; that
is the round-robin `1`-factorisation, whose colour class `0` is the matching
`{∞, 0}, {1, -1}, …, {n+1, -(n+1)}`.  Choosing the parts of the cocktail party graph to be exactly
that matching deletes colour `0`, leaving `2n+2` colours. -/

/-- The label of the cocktail party vertex `(i, j)` as a natural number below `2 * n + 3`.  The
vertex `(0, 0)` is the point at infinity and its label is not used. -/
def cpCode (n i j : ℕ) : ℕ := if i = 0 then 0 else if j = 0 then i else 2 * n + 3 - i

theorem cpCode_lt (n i j : ℕ) (hi : i < n + 2) : cpCode n i j < 2 * n + 3 := by
  unfold cpCode; split_ifs <;> omega

theorem cpCode_eq_zero_iff (n i j : ℕ) (hi : i < n + 2) : cpCode n i j = 0 ↔ i = 0 := by
  unfold cpCode; constructor <;> intro h <;> split_ifs at * <;> omega

theorem cpCode_inj (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2) (hj' : j' < 2)
    (h0 : ¬(i = 0 ∧ j = 0)) (h0' : ¬(i' = 0 ∧ j' = 0)) (h : cpCode n i j = cpCode n i' j') :
    i = i' ∧ j = j' := by
  unfold cpCode at h; split_ifs at h <;> omega

/-- The label of `(i, j)` in `ZMod (2 * n + 3)`. -/
def cpVal (n i j : ℕ) : ZMod (2 * n + 3) := ((cpCode n i j : ℕ) : ZMod (2 * n + 3))

/-- The colour of the ordered pair `(i, j), (i', j')` in `ZMod (2 * n + 3)`. -/
def cpRaw (n i j i' j' : ℕ) : ZMod (2 * n + 3) :=
  if i = 0 ∧ j = 0 then 2 * cpVal n i' j'
  else if i' = 0 ∧ j' = 0 then 2 * cpVal n i j
  else cpVal n i j + cpVal n i' j'

instance cpNeZero (n : ℕ) : NeZero (2 * n + 3) := ⟨by omega⟩

theorem cp_natCast_inj (n a b : ℕ) (ha : a < 2 * n + 3) (hb : b < 2 * n + 3)
    (h : (a : ZMod (2 * n + 3)) = (b : ZMod (2 * n + 3))) : a = b := by
  have h2 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at h2

/-- Two is invertible modulo the odd number `2 * n + 3`. -/
theorem cp_two_mul_inj (n : ℕ) {a b : ZMod (2 * n + 3)} (h : 2 * a = 2 * b) : a = b := by
  have hz : ((2 * n + 3 : ℕ) : ZMod (2 * n + 3)) = 0 := ZMod.natCast_self _
  push_cast at hz
  have key : ((n : ZMod (2 * n + 3)) + 2) * 2 = 1 := by linear_combination hz
  calc a = ((n : ZMod (2 * n + 3)) + 2) * 2 * a := by rw [key, one_mul]
    _ = ((n : ZMod (2 * n + 3)) + 2) * (2 * a) := by ring
    _ = ((n : ZMod (2 * n + 3)) + 2) * (2 * b) := by rw [h]
    _ = ((n : ZMod (2 * n + 3)) + 2) * 2 * b := by ring
    _ = b := by rw [key, one_mul]

theorem cpVal_inj (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2) (hj' : j' < 2)
    (h0 : ¬(i = 0 ∧ j = 0)) (h0' : ¬(i' = 0 ∧ j' = 0)) (h : cpVal n i j = cpVal n i' j') :
    i = i' ∧ j = j' :=
  cpCode_inj n i j i' j' hi hi' hj hj' h0 h0'
    (cp_natCast_inj n _ _ (cpCode_lt n i j hi) (cpCode_lt n i' j' hi') h)

theorem cpVal_eq_zero_iff (n i j : ℕ) (hi : i < n + 2) : cpVal n i j = 0 ↔ i = 0 := by
  rw [← cpCode_eq_zero_iff n i j hi]
  constructor
  · intro h
    have h2 : ((cpCode n i j : ℕ) : ZMod (2 * n + 3)) = ((0 : ℕ) : ZMod (2 * n + 3)) := by
      simpa using h
    exact cp_natCast_inj n _ _ (cpCode_lt n i j hi) (by omega) h2
  · intro h; unfold cpVal; rw [h]; simp

theorem cpRaw_comm (n i j i' j' : ℕ) : cpRaw n i j i' j' = cpRaw n i' j' i j := by
  unfold cpRaw
  by_cases h : i = 0 ∧ j = 0 <;> by_cases h' : i' = 0 ∧ j' = 0
  · rw [if_pos h, if_pos h']
    rw [show cpVal n i' j' = 0 from by unfold cpVal cpCode; rw [if_pos h'.1]; simp,
      show cpVal n i j = 0 from by unfold cpVal cpCode; rw [if_pos h.1]; simp]
  · rw [if_pos h, if_neg h', if_pos h]
  · rw [if_neg h, if_pos h', if_pos h']
  · rw [if_neg h, if_neg h', if_neg h', if_neg h]
    exact add_comm _ _

/-- The colour of an edge is never `0`: colour `0` is exactly the deleted perfect matching. -/
theorem cpRaw_ne_zero (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2)
    (hj' : j' < 2) (hne : i ≠ i') : cpRaw n i j i' j' ≠ 0 := by
  unfold cpRaw
  split_ifs with h h'
  · intro hc
    have h2 : cpVal n i' j' = 0 := cp_two_mul_inj n (by rw [hc]; ring)
    rw [cpVal_eq_zero_iff n i' j' hi'] at h2
    omega
  · intro hc
    have h2 : cpVal n i j = 0 := cp_two_mul_inj n (by rw [hc]; ring)
    rw [cpVal_eq_zero_iff n i j hi] at h2
    omega
  · intro hc
    unfold cpVal at hc
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hb := cpCode_lt n i j hi
    have hb' := cpCode_lt n i' j' hi'
    have hk2 : k < 2 := by nlinarith
    interval_cases k
    · unfold cpCode at hk; split_ifs at hk <;> omega
    · unfold cpCode at hk; split_ifs at hk <;> omega

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

/-! ## Explicit edge colourings for the odd-order regular graphs

Each of these graphs is `k`-regular on an odd number of vertices, hence class two, so its
chromatic index is `k + 1` by Vizing; the tables below are the witnessing colourings, checked by
`native_decide` on the pairs (symmetry) and on the triples (properness). -/

def tri6Masks : List ℕ :=
  [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48]

def tri6Idx (s : (triangular 6).V) : ℕ :=
  tri6Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def tri6ColTable : List (List ℕ) :=
  [[0, 0, 3, 4, 6, 0, 8, 1, 0, 0, 5, 2, 0, 0, 0], [0, 0, 7, 6, 0, 1, 3, 0, 8, 0, 4, 0, 2, 0, 0],
   [3, 7, 0, 0, 1, 4, 0, 8, 2, 0, 0, 6, 0, 0, 0], [4, 6, 0, 0, 3, 2, 7, 0, 0, 8, 1, 0, 0, 5, 0],
   [6, 0, 1, 3, 0, 8, 0, 5, 0, 4, 0, 0, 0, 7, 0], [0, 1, 4, 2, 8, 0, 0, 0, 5, 7, 0, 0, 3, 0, 0],
   [8, 3, 0, 7, 0, 0, 0, 4, 0, 1, 6, 0, 0, 0, 5], [1, 0, 8, 0, 5, 0, 4, 0, 7, 0, 0, 3, 0, 0, 6],
   [0, 8, 2, 0, 0, 5, 0, 7, 0, 6, 0, 0, 1, 0, 3], [0, 0, 0, 8, 4, 7, 1, 0, 6, 0, 0, 0, 0, 3, 2],
   [5, 4, 0, 1, 0, 0, 6, 0, 0, 0, 0, 8, 7, 2, 0], [2, 0, 6, 0, 0, 0, 0, 3, 0, 0, 8, 0, 5, 4, 7],
   [0, 2, 0, 0, 0, 3, 0, 0, 1, 0, 7, 5, 0, 6, 4], [0, 0, 0, 5, 7, 0, 0, 0, 0, 3, 2, 4, 6, 0, 8],
   [0, 0, 0, 0, 0, 0, 5, 6, 3, 2, 0, 7, 4, 8, 0]]

def tri6Col (x y : (triangular 6).V) : Fin 9 :=
  ⟨min ((tri6ColTable.getD (tri6Idx x) []).getD (tri6Idx y) 0) 8, by omega⟩

theorem tri6Col_symm : ∀ x y : (triangular 6).V, tri6Col x y = tri6Col y x := by
  native_decide

theorem tri6Col_proper : ∀ u v w : (triangular 6).V, (triangular 6).Adj u v = true →
    (triangular 6).Adj u w = true → v ≠ w → tri6Col u v ≠ tri6Col u w := by
  native_decide

def tri7Masks : List ℕ :=
  [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96]

def tri7Idx (s : (triangular 7).V) : ℕ :=
  tri7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def tri7ColTable : List (List ℕ) :=
  [[0, 10, 3, 0, 2, 0, 8, 7, 0, 0, 9, 6, 0, 0, 0, 1, 5, 0, 0, 0, 0], [10, 0, 5, 9, 0, 8, 2, 0, 4,
   0, 0, 0, 1, 0, 0, 3, 0, 7, 0, 0, 0], [3, 5, 0, 0, 8, 9, 0, 6, 0, 0, 0, 1, 7, 0, 0, 0, 4, 2, 0,
   0, 0], [0, 9, 0, 0, 3, 4, 1, 0, 0, 8, 10, 0, 0, 5, 0, 7, 0, 0, 2, 0, 0], [2, 0, 8, 3, 0, 10, 0,
   1, 0, 5, 0, 7, 0, 9, 0, 0, 6, 0, 0, 0, 0], [0, 8, 9, 4, 10, 0, 0, 0, 1, 0, 0, 0, 3, 6, 0, 0, 0,
   5, 7, 0, 0], [8, 2, 0, 1, 0, 0, 0, 0, 9, 7, 5, 0, 0, 0, 3, 6, 0, 0, 0, 4, 0], [7, 0, 6, 0, 1, 0,
   0, 0, 3, 9, 0, 10, 0, 0, 4, 0, 2, 0, 0, 8, 0], [0, 4, 0, 0, 0, 1, 9, 3, 0, 2, 0, 0, 10, 0, 7, 0,
   0, 8, 0, 6, 0], [0, 0, 0, 8, 5, 0, 7, 9, 2, 0, 0, 0, 0, 4, 10, 0, 0, 0, 6, 1, 0], [9, 0, 0, 10,
   0, 0, 5, 0, 0, 0, 0, 4, 6, 7, 8, 2, 0, 0, 0, 0, 3], [6, 0, 1, 0, 7, 0, 0, 10, 0, 0, 4, 0, 2, 8,
   5, 0, 3, 0, 0, 0, 0], [0, 1, 7, 0, 0, 3, 0, 0, 10, 0, 6, 2, 0, 0, 9, 0, 0, 4, 0, 0, 5], [0, 0,
   0, 5, 9, 6, 0, 0, 0, 4, 7, 8, 0, 0, 1, 0, 0, 0, 3, 0, 2], [0, 0, 0, 0, 0, 0, 3, 4, 7, 10, 8, 5,
   9, 1, 0, 0, 0, 0, 0, 2, 6], [1, 3, 0, 7, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8, 0, 9, 10, 4],
   [5, 0, 4, 0, 6, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 8, 0, 9, 1, 0, 10], [0, 7, 2, 0, 0, 5, 0, 0, 8, 0,
   0, 0, 4, 0, 0, 0, 9, 0, 10, 3, 1], [0, 0, 0, 2, 0, 7, 0, 0, 0, 6, 0, 0, 0, 3, 0, 9, 1, 10, 0, 5,
   8], [0, 0, 0, 0, 0, 0, 4, 8, 6, 1, 0, 0, 0, 0, 2, 10, 0, 3, 5, 0, 9], [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 3, 0, 5, 2, 6, 4, 10, 1, 8, 9, 0]]

def tri7Col (x y : (triangular 7).V) : Fin 11 :=
  ⟨min ((tri7ColTable.getD (tri7Idx x) []).getD (tri7Idx y) 0) 10, by omega⟩

theorem tri7Col_symm : ∀ x y : (triangular 7).V, tri7Col x y = tri7Col y x := by
  native_decide

theorem tri7Col_proper : ∀ u v w : (triangular 7).V, (triangular 7).Adj u v = true →
    (triangular 7).Adj u w = true → v ≠ w → tri7Col u v ≠ tri7Col u w := by
  native_decide

def triples7Masks : List ℕ :=
  [7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56, 67, 69, 70, 73,
   74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 112]

def kneser73Idx (s : (kneser 7 3).V) : ℕ :=
  triples7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def kneser73ColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
   0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 0, 0, 0, 3, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0,
   0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1,
   0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
   0, 0, 3, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4,
   0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0,
   0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2,
   4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0,
   4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0,
   0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def kneser73Col (x y : (kneser 7 3).V) : Fin 5 :=
  ⟨min ((kneser73ColTable.getD (kneser73Idx x) []).getD (kneser73Idx y) 0) 4, by omega⟩

theorem kneser73Col_symm : ∀ x y : (kneser 7 3).V, kneser73Col x y = kneser73Col y x := by
  native_decide

theorem kneser73Col_proper : ∀ u v w : (kneser 7 3).V, (kneser 7 3).Adj u v = true →
    (kneser 7 3).Adj u w = true → v ≠ w → kneser73Col u v ≠ kneser73Col u w := by
  native_decide

def johnson73Idx (s : (johnson 7 3).V) : ℕ :=
  triples7Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def johnson73ColTable : List (List ℕ) :=
  [[0, 0, 12, 6, 7, 2, 10, 0, 0, 0, 5, 3, 11, 0, 0, 0, 0, 0, 0, 0, 4, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0], [0, 0, 8, 3, 1, 0, 0, 5, 7, 0, 10, 0, 0, 12, 4, 0, 0, 0, 0, 0, 6, 0, 0, 11, 2, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0], [12, 8, 0, 2, 0, 3, 0, 0, 0, 7, 0, 10, 0, 4, 0, 1, 0, 0, 0, 0, 0,
   11, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0], [6, 3, 2, 0, 0, 0, 12, 0, 10, 4, 0, 0, 1, 0, 5, 8,
   0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0], [7, 1, 0, 0, 0, 5, 2, 11, 12, 0, 4,
   0, 0, 0, 0, 0, 9, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0], [2, 0, 3, 0, 5, 0, 1,
   4, 0, 8, 0, 6, 0, 0, 0, 0, 7, 0, 0, 0, 0, 10, 0, 0, 0, 0, 11, 0, 9, 0, 0, 0, 0, 0, 0], [10, 0,
   0, 12, 2, 1, 0, 0, 6, 9, 0, 0, 5, 0, 0, 0, 0, 4, 11, 0, 0, 0, 3, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0,
   0, 0], [0, 5, 0, 0, 11, 4, 0, 0, 8, 10, 0, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 0, 12, 0, 0, 9, 0,
   0, 2, 0, 0, 0, 0, 0], [0, 7, 0, 10, 12, 0, 6, 8, 0, 0, 0, 0, 0, 0, 9, 0, 0, 2, 0, 5, 0, 0, 0, 0,
   3, 0, 0, 1, 0, 11, 0, 0, 0, 0, 0], [0, 0, 7, 4, 0, 8, 9, 10, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 3,
   11, 0, 0, 0, 0, 0, 1, 0, 0, 2, 6, 0, 0, 0, 0, 0], [5, 10, 0, 0, 4, 0, 0, 0, 0, 0, 0, 12, 3, 1,
   2, 0, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 6, 0, 0, 0], [3, 0, 10, 0, 0, 6, 0, 0, 0, 0,
   12, 0, 8, 9, 0, 11, 5, 0, 7, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0], [11, 0, 0, 1, 0,
   0, 5, 0, 0, 0, 3, 8, 0, 0, 6, 2, 0, 0, 9, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 4, 7, 0, 0], [0,
   12, 4, 0, 0, 0, 0, 3, 0, 0, 1, 9, 0, 0, 10, 7, 11, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 5, 0,
   0, 0, 0], [0, 4, 0, 5, 0, 0, 0, 0, 9, 0, 2, 0, 6, 10, 0, 0, 0, 12, 0, 8, 0, 0, 0, 0, 7, 0, 0, 0,
   0, 0, 0, 3, 0, 11, 0], [0, 0, 1, 8, 0, 0, 0, 0, 0, 5, 0, 11, 2, 7, 0, 0, 0, 0, 6, 4, 0, 0, 0, 0,
   0, 9, 0, 0, 0, 0, 0, 0, 3, 12, 0], [0, 0, 0, 0, 9, 7, 0, 6, 0, 0, 8, 5, 0, 11, 0, 0, 0, 3, 4, 0,
   0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 1], [0, 0, 0, 0, 6, 0, 4, 0, 2, 0, 9, 0, 0, 0, 12, 0,
   3, 0, 8, 10, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 5, 0, 0, 11], [0, 0, 0, 0, 0, 0, 11, 0, 0, 3, 0,
   7, 9, 0, 0, 6, 4, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 12, 0, 5], [0, 0, 0, 0, 0, 0, 0,
   1, 5, 11, 0, 0, 0, 6, 8, 4, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 3, 12], [4, 6,
   0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 8, 5, 1, 0, 10, 12, 0, 0, 11, 2, 0,
   0, 0], [8, 0, 11, 0, 0, 10, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 12, 0, 0, 3, 5, 0,
   7, 0, 6, 0, 4, 0, 0], [9, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 8, 12, 0, 0,
   6, 2, 0, 4, 5, 0, 0, 7, 11, 0, 0], [0, 11, 6, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
   0, 5, 0, 0, 0, 4, 7, 1, 0, 0, 10, 8, 0, 0, 9, 0], [0, 2, 0, 9, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 7,
   0, 0, 0, 0, 0, 1, 0, 6, 4, 0, 10, 0, 5, 0, 0, 0, 11, 0, 8, 0], [0, 0, 5, 11, 0, 0, 0, 0, 0, 1,
   0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 2, 7, 10, 0, 0, 0, 8, 12, 0, 0, 6, 4, 0], [0, 0, 0, 0, 0,
   11, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 5, 0, 1, 0, 0, 0, 6, 12, 7, 3, 0, 0, 0, 4],
   [0, 0, 0, 0, 10, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 12, 0, 4, 0, 5, 0, 6, 0, 11, 3, 0,
   9, 0, 0, 2], [0, 0, 0, 0, 0, 9, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 7, 5, 0, 0, 8, 12,
   11, 0, 4, 0, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0, 0, 2, 11, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0,
   10, 0, 12, 7, 3, 4, 0, 0, 0, 0, 1, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 5, 0, 0, 10, 0,
   0, 0, 11, 6, 0, 8, 0, 0, 3, 0, 0, 0, 0, 12, 0, 2, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0,
   3, 0, 0, 5, 0, 0, 2, 0, 7, 0, 11, 0, 0, 9, 0, 0, 12, 0, 8, 10, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 2, 7, 0, 0, 3, 0, 0, 12, 0, 0, 4, 11, 0, 0, 6, 0, 0, 1, 0, 0, 8, 0, 5, 10], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 12, 0, 0, 0, 3, 0, 0, 0, 9, 8, 4, 0, 0, 0, 1, 2, 10, 5, 0, 7],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 11, 5, 12, 0, 0, 0, 0, 0, 0, 4, 2, 3, 8, 9,
   0, 10, 7, 0]]

def johnson73Col (x y : (johnson 7 3).V) : Fin 13 :=
  ⟨min ((johnson73ColTable.getD (johnson73Idx x) []).getD (johnson73Idx y) 0) 12, by omega⟩

theorem johnson73Col_symm : ∀ x y : (johnson 7 3).V, johnson73Col x y = johnson73Col y x := by
  native_decide

theorem johnson73Col_proper : ∀ u v w : (johnson 7 3).V, (johnson 7 3).Adj u v = true →
    (johnson 7 3).Adj u w = true → v ≠ w → johnson73Col u v ≠ johnson73Col u w := by
  native_decide

def rook33Idx (x : (rook 3 3).V) : ℕ := x.1.1 * 3 + x.2.1

def rook33ColTable : List (List ℕ) :=
  [[0, 1, 3, 0, 0, 0, 2, 0, 0], [1, 0, 4, 0, 3, 0, 0, 0, 0], [3, 4, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
   0, 2, 3, 4, 0, 0], [0, 3, 0, 2, 0, 4, 0, 1, 0], [0, 0, 0, 3, 4, 0, 0, 0, 2], [2, 0, 0, 4, 0, 0,
   0, 3, 0], [0, 0, 0, 0, 1, 0, 3, 0, 4], [0, 0, 1, 0, 0, 2, 0, 4, 0]]

def rook33Col (x y : (rook 3 3).V) : Fin 5 :=
  ⟨min ((rook33ColTable.getD (rook33Idx x) []).getD (rook33Idx y) 0) 4, by omega⟩

theorem rook33Col_symm : ∀ x y : (rook 3 3).V, rook33Col x y = rook33Col y x := by
  native_decide

theorem rook33Col_proper : ∀ u v w : (rook 3 3).V, (rook 3 3).Adj u v = true →
    (rook 3 3).Adj u w = true → v ≠ w → rook33Col u v ≠ rook33Col u w := by
  native_decide

def paley13Idx (x : (paley 13).V) : ℕ := x.1

def paley13ColTable : List (List ℕ) :=
  [[0, 2, 0, 3, 6, 0, 0, 0, 0, 1, 0, 0, 5], [2, 0, 4, 0, 0, 5, 0, 0, 0, 0, 1, 6, 0], [0, 4, 0, 5,
   0, 2, 3, 0, 0, 0, 0, 0, 1], [3, 0, 5, 0, 4, 0, 1, 6, 0, 0, 0, 0, 0], [6, 0, 0, 4, 0, 1, 0, 3, 2,
   0, 0, 0, 0], [0, 5, 2, 0, 1, 0, 6, 0, 0, 4, 0, 0, 0], [0, 0, 3, 1, 0, 6, 0, 5, 0, 0, 4, 0, 0],
   [0, 0, 0, 6, 3, 0, 5, 0, 4, 0, 2, 1, 0], [0, 0, 0, 0, 2, 0, 0, 4, 0, 5, 0, 3, 6], [1, 0, 0, 0,
   0, 4, 0, 0, 5, 0, 6, 0, 2], [0, 1, 0, 0, 0, 0, 4, 2, 0, 6, 0, 5, 0], [0, 6, 0, 0, 0, 0, 0, 1, 3,
   0, 5, 0, 4], [5, 0, 1, 0, 0, 0, 0, 0, 6, 2, 0, 4, 0]]

def paley13Col (x y : (paley 13).V) : Fin 7 :=
  ⟨min ((paley13ColTable.getD (paley13Idx x) []).getD (paley13Idx y) 0) 6, by omega⟩

theorem paley13Col_symm : ∀ x y : (paley 13).V, paley13Col x y = paley13Col y x := by
  native_decide

theorem paley13Col_proper : ∀ u v w : (paley 13).V, (paley 13).Adj u v = true →
    (paley 13).Adj u w = true → v ≠ w → paley13Col u v ≠ paley13Col u w := by
  native_decide

/-! ## The Petersen graph is class two

The Petersen graph is cubic, so Vizing gives `χ' ≤ 4`; the table `pet10ColTable` realises that
bound.  For the lower bound the fifteen edges are listed as `petEdge 0, …, petEdge 14` and the
thirty adjacencies of the line graph between them are checked once, by `native_decide`; then
`petSearch` — an exhaustive `3 ^ 15` case split, again by `native_decide` — says no assignment of
three colours to those fifteen edges avoids all thirty conflicts. -/

def petVerts : List (kneser 5 2).V :=
  (List.range 32).filterMap fun m ↦
    if h : (Finset.univ.filter fun i : Fin 5 ↦ m / 2 ^ i.1 % 2 = 1).card = 2 then
      some ⟨_, h⟩
    else none

def petVert0 : (kneser 5 2).V := ⟨{0, 1}, by decide⟩

def petVert1 : (kneser 5 2).V := ⟨{2, 3}, by decide⟩

def petEdge0 : (lineGraph (kneser 5 2)).V := ⟨s(petVert0, petVert1), by decide⟩

/-- The fifteen edges of the Petersen graph, as vertices of its line graph. -/
def petEdgeList : List (lineGraph (kneser 5 2)).V :=
  petVerts.zipIdx.flatMap fun p ↦ petVerts.zipIdx.filterMap fun q ↦
    if h : p.2 < q.2 ∧ s(p.1, q.1) ∈ (kneser 5 2).toSimple.edgeSet then some ⟨_, h.2⟩ else none

def petEdge (i : ℕ) : (lineGraph (kneser 5 2)).V := petEdgeList.getD i petEdge0

def petPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 13), (0, 14), (1, 2), (1, 10), (1, 12), (2, 5), (2, 8), (3, 4), (3, 5),
   (3, 11), (3, 12), (4, 5), (4, 9), (4, 14), (5, 8), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8),
   (7, 11), (7, 13), (9, 10), (9, 14), (10, 12), (11, 12), (11, 13), (13, 14)]

theorem petEdgeAdj : ∀ p ∈ petPairs,
    (lineGraph (kneser 5 2)).Adj (petEdge p.1) (petEdge p.2) = true := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- No assignment of three colours to the fifteen edges of the Petersen graph avoids all thirty
conflicts: an exhaustive `3 ^ 15` case split. -/
theorem petSearch : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Fin 3,
    ¬ (c0 ≠ c1 ∧ c0 ≠ c2 ∧ c0 ≠ c13 ∧ c0 ≠ c14 ∧ c1 ≠ c2 ∧ c1 ≠ c10 ∧ c1 ≠ c12 ∧ c2 ≠ c5 ∧ c2 ≠ c8 ∧
      c3 ≠ c4 ∧ c3 ≠ c5 ∧ c3 ≠ c11 ∧ c3 ≠ c12 ∧ c4 ≠ c5 ∧ c4 ≠ c9 ∧ c4 ≠ c14 ∧ c5 ≠ c8 ∧ c6 ≠ c7 ∧
      c6 ≠ c8 ∧ c6 ≠ c9 ∧ c6 ≠ c10 ∧ c7 ≠ c8 ∧ c7 ≠ c11 ∧ c7 ≠ c13 ∧ c9 ≠ c10 ∧ c9 ≠ c14 ∧
      c10 ≠ c12 ∧ c11 ≠ c12 ∧ c11 ≠ c13 ∧ c13 ≠ c14) := by
  native_decide

theorem petersen_no_three_colouring (col : (lineGraph (kneser 5 2)).V → Fin 3) :
    ∃ e f, (lineGraph (kneser 5 2)).Adj e f = true ∧ col e = col f := by
  by_contra hcon
  push_neg at hcon
  exact petSearch (col (petEdge 0)) (col (petEdge 1)) (col (petEdge 2)) (col (petEdge 3))
    (col (petEdge 4)) (col (petEdge 5)) (col (petEdge 6)) (col (petEdge 7)) (col (petEdge 8))
    (col (petEdge 9)) (col (petEdge 10)) (col (petEdge 11)) (col (petEdge 12)) (col (petEdge 13))
    (col (petEdge 14))
    ⟨hcon _ _ (petEdgeAdj (0, 1) (by decide)), hcon _ _ (petEdgeAdj (0, 2) (by decide)),
      hcon _ _ (petEdgeAdj (0, 13) (by decide)), hcon _ _ (petEdgeAdj (0, 14) (by decide)),
      hcon _ _ (petEdgeAdj (1, 2) (by decide)), hcon _ _ (petEdgeAdj (1, 10) (by decide)),
      hcon _ _ (petEdgeAdj (1, 12) (by decide)), hcon _ _ (petEdgeAdj (2, 5) (by decide)),
      hcon _ _ (petEdgeAdj (2, 8) (by decide)), hcon _ _ (petEdgeAdj (3, 4) (by decide)),
      hcon _ _ (petEdgeAdj (3, 5) (by decide)), hcon _ _ (petEdgeAdj (3, 11) (by decide)),
      hcon _ _ (petEdgeAdj (3, 12) (by decide)), hcon _ _ (petEdgeAdj (4, 5) (by decide)),
      hcon _ _ (petEdgeAdj (4, 9) (by decide)), hcon _ _ (petEdgeAdj (4, 14) (by decide)),
      hcon _ _ (petEdgeAdj (5, 8) (by decide)), hcon _ _ (petEdgeAdj (6, 7) (by decide)),
      hcon _ _ (petEdgeAdj (6, 8) (by decide)), hcon _ _ (petEdgeAdj (6, 9) (by decide)),
      hcon _ _ (petEdgeAdj (6, 10) (by decide)), hcon _ _ (petEdgeAdj (7, 8) (by decide)),
      hcon _ _ (petEdgeAdj (7, 11) (by decide)), hcon _ _ (petEdgeAdj (7, 13) (by decide)),
      hcon _ _ (petEdgeAdj (9, 10) (by decide)), hcon _ _ (petEdgeAdj (9, 14) (by decide)),
      hcon _ _ (petEdgeAdj (10, 12) (by decide)), hcon _ _ (petEdgeAdj (11, 12) (by decide)),
      hcon _ _ (petEdgeAdj (11, 13) (by decide)), hcon _ _ (petEdgeAdj (13, 14) (by decide))⟩

/-! ### A four-edge-colouring of the Petersen graph -/

def pet10Masks : List ℕ := [3, 5, 6, 9, 10, 12, 17, 18, 20, 24]

def pet10Idx (s : (kneser 5 2).V) : ℕ :=
  pet10Masks.findIdx (fun m ↦ m == (s.1.sum fun i ↦ 2 ^ i.1))

def pet10ColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 2, 3, 0], [0, 0, 0, 0, 0, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 1, 3, 0, 0],
   [0, 0, 2, 0, 3, 1, 0, 0, 0, 0], [0, 1, 0, 2, 0, 3, 0, 0, 0, 0], [1, 0, 0, 3, 2, 0, 0, 0, 0, 0],
   [2, 3, 1, 0, 0, 0, 0, 0, 0, 0]]

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 2000000 in
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
  haveI : Finite (kneser 5 2 ≃cg kneser 5 2) := (kneser 5 2).instFiniteAut
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
  haveI : Finite (kneser 5 2 ≃cg kneser 5 2) := (kneser 5 2).instFiniteAut
  have h := Nat.card_le_card_of_injective _ kneserAuto_five_two_injective
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rwa [hc] at h

/-- **The Petersen graph has exactly `120` automorphisms**: its automorphism group is the
symmetric group `S₅` acting on the five-element ground set of `K(5, 2)`. -/
theorem autCount_kneser_five_two : (kneser 5 2).autCount = 120 :=
  le_antisymm autCount_kneser_five_two_le le_autCount_kneser_five_two

/-! ## The girth of a cycle

`Cₙ` has girth `n`.  The upper bound is the general fact that a cycle uses no more vertices than
the graph has.  For the lower bound, a shorter cycle would miss some vertex `x`; rotating the
labels so that `x` becomes `n - 1` carries the missed cycle into `path n`, which is acyclic. -/

/-- **A graph with a cycle has girth at most its order**: the support of a cycle, minus its
repeated endpoint, is a list of distinct vertices as long as the cycle. -/
theorem girth_le_V {G : CGraph} (h : ¬ G.IsAcyclic) : G.girth ≤ Fintype.card G.V := by
  simp only [IsAcyclic, SimpleGraph.IsAcyclic, not_forall, not_not] at h
  obtain ⟨v, c, hc⟩ := h
  refine le_trans (girth_le_length hc) ?_
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  calc c.length = c.support.tail.length := hlen.symm
    _ ≤ Fintype.card G.V := hc.support_nodup.length_le_card

/-- Relabelling `cycle N` so that `x` becomes the last label `N - 1`, cutting the cycle open at
`x`.  Every vertex other than `x` lands strictly below `N - 1`. -/
def cycRot {N : ℕ} (x y : Fin N) : Fin N :=
  ⟨if x.1 < y.1 then y.1 - x.1 - 1 else y.1 + N - x.1 - 1, by
    have := x.isLt; have := y.isLt; split_ifs <;> omega⟩

theorem cycRot_val {N : ℕ} (x y : Fin N) :
    (cycRot x y).1 = if x.1 < y.1 then y.1 - x.1 - 1 else y.1 + N - x.1 - 1 := rfl

theorem cycRot_injective {N : ℕ} (x : Fin N) : Function.Injective (cycRot x) := by
  intro y z h
  have hy := y.isLt
  have hz := z.isLt
  have hx := x.isLt
  have h' : (cycRot x y).1 = (cycRot x z).1 := by rw [h]
  rw [cycRot_val, cycRot_val] at h'
  refine Fin.ext ?_
  split_ifs at h' <;> omega

/-- Only the cut vertex reaches the top label. -/
theorem cycRot_lt {N : ℕ} {x y : Fin N} (h : y ≠ x) : (cycRot x y).1 + 1 < N := by
  have hy := y.isLt
  have hx := x.isLt
  have h' : y.1 ≠ x.1 := fun hh ↦ h (Fin.ext hh)
  rw [cycRot_val]
  split_ifs <;> omega

/-- Away from the cut vertex, a cycle edge becomes a path edge. -/
theorem path_adj_cycRot {N : ℕ} (hN : 3 ≤ N) {x y z : Fin N} (hy : y ≠ x) (hz : z ≠ x)
    (h : (cycle N).Adj y z = true) : (path N).Adj (cycRot x y) (cycRot x z) = true := by
  have hy' := cycRot_lt hy
  have hz' := cycRot_lt hz
  have hyl := y.isLt
  have hzl := z.isLt
  have hxl := x.isLt
  have hyx : y.1 ≠ x.1 := fun hh ↦ hy (Fin.ext hh)
  have hzx : z.1 ≠ x.1 := fun hh ↦ hz (Fin.ext hh)
  rw [cycle_adj_eq_iff hN] at h
  have hs : (y.1 + 1) % N = if y.1 + 1 = N then 0 else y.1 + 1 := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hyl) with hq | hq
    · rw [if_pos (by omega), show y.1 + 1 = N from by omega, Nat.mod_self]
    · rw [if_neg (by omega), Nat.mod_eq_of_lt hq]
  have hp : (y.1 + N - 1) % N = if y.1 = 0 then N - 1 else y.1 - 1 := by
    rcases Nat.eq_zero_or_pos y.1 with hq | hq
    · rw [if_pos hq, show y.1 + N - 1 = N - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg (by omega), show y.1 + N - 1 = N + (y.1 - 1) from by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
  rw [hs, hp] at h
  rw [path_adj_val]
  rw [cycRot_val] at hy' hz'
  refine ⟨fun hh ↦ ?_, ?_⟩
  · rw [cycRot_val, cycRot_val] at hh
    split_ifs at hh h <;> omega
  · rw [cycRot_val, cycRot_val]
    split_ifs at h ⊢ <;> omega

/-- **No short cycle in `Cₙ`.**  A closed chain of fewer than `n` distinct vertices misses one,
and rotating that vertex to the top turns the chain into a cycle in the acyclic `path n`. -/
theorem cycle_no_short_cycleList {N : ℕ} (hN : 3 ≤ N) (u : (cycle N).V) (vs : List (cycle N).V)
    (h2 : 2 ≤ vs.length) (hlt : vs.length + 1 < N) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun a b ↦ (cycle N).Adj a b) (u :: vs))
    (hcl : (cycle N).Adj (vs.getLastD u) u) : False := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin N, x ∉ u :: vs := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin N)) ⊆ (u :: vs).toFinset :=
      fun a _ ↦ List.mem_toFinset.2 (hcon a)
    have h1 := Finset.card_le_card hsub
    have h2' : (u :: vs).toFinset.card ≤ (u :: vs).length := List.toFinset_card_le _
    simp only [Finset.card_univ, Fintype.card_fin, List.length_cons] at h1 h2'
    omega
  have hmem : ∀ a ∈ u :: vs, a ≠ x := fun a ha hax ↦ hx (hax ▸ ha)
  refine absurd (isAcyclic_path N) ?_
  refine not_isAcyclic_of_cycleList (G := path N) (cycRot x u) (vs.map (cycRot x)) ?_ ?_ ?_ ?_
  · simpa using h2
  · rw [show cycRot x u :: vs.map (cycRot x) = (u :: vs).map (cycRot x) from rfl]
    exact hnd.map (cycRot_injective x)
  · rw [show cycRot x u :: vs.map (cycRot x) = (u :: vs).map (cycRot x) from rfl]
    refine (List.isChain_map (cycRot x)).2 ?_
    exact hch.imp_of_mem_imp fun a b ha hb hab ↦
      path_adj_cycRot hN (hmem a ha) (hmem b hb) hab
  · rw [getLastD_map]
    exact path_adj_cycRot hN (hmem _ List.getLastD_mem_cons) (hmem u (by simp)) hcl

/-- **The girth of a cycle is its length.** -/
@[toIsoGraph]
theorem girth_cycle (n : ℕ) : (cycle (n + 3)).girth = n + 3 := by
  refine le_antisymm ?_ ?_
  · have h := girth_le_V (not_isAcyclic_cycle n)
    rwa [card_cycle] at h
  · exact le_girth_of_forall_cycleList
      (fun u vs h2 hlt hnd hch hcl ↦
        cycle_no_short_cycleList (by omega) u vs h2 hlt hnd hch hcl)
      (not_isAcyclic_cycle n)

/-! ## The girth of the decorated cycles

`girth_cycle` says a cycle has no shortcut; the tadpole and the cycle-with-pendants say that
gluing a tree onto a cycle adds no cycle at all.  The two proofs share the same three pieces: a
general `girth_le_card_of_map` for the upper bound, `cycleList_two_nbrs` (each vertex of a closed
nodup chain has two distinct neighbours in it) to show every chain vertex lies on the cycle, and
`no_short_cycleList_of_labels`, which pushes such a chain into `cycle M` and appeals to
`cycle_no_short_cycleList`.
-/

/-! ## The girth of the decorated cycles -/

/-- **An injective homomorphism carries cycles to cycles.** -/
theorem not_isAcyclic_of_map {G H : CGraph} (f : G.V → H.V) (hinj : Function.Injective f)
    (hadj : ∀ x y, G.Adj x y = true → H.Adj (f x) (f y) = true) (hnac : ¬ G.IsAcyclic) :
    ¬ H.IsAcyclic := by
  simp only [IsAcyclic, SimpleGraph.IsAcyclic, not_forall, not_not] at hnac
  obtain ⟨v, c, hc⟩ := hnac
  obtain ⟨u, vs, hlen, hnd, hch, hcl⟩ := exists_cycleList_of_isCycle hc
  have h3 := hc.three_le_length
  refine not_isAcyclic_of_cycleList (f u) (vs.map f) (by simp only [List.length_map]; omega)
    ?_ ?_ ?_
  · rw [show f u :: vs.map f = (u :: vs).map f from rfl]
    exact hnd.map hinj
  · rw [show f u :: vs.map f = (u :: vs).map f from rfl]
    exact (List.isChain_map f).2 (hch.imp_of_mem_imp fun a b _ _ hab ↦ hadj a b hab)
  · rw [getLastD_map]
    exact hadj _ _ hcl

/-- Rewriting the index of a list lookup.  Mathlib's `getElem_congr_idx` is stated for a general
`GetElem` with the index implicit; this specialisation to lists, with the list explicit, is what
the cycle-list manipulations below can apply directly. -/
theorem getElem_congr_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i]'hi = l[j]'(h ▸ hi) := by subst h; rfl

/-- **Girth is monotone along an injective homomorphism.**  A cycle of `G` maps to a cycle of `H`,
so `H` has girth at most the order of `G` as soon as `G` has a cycle at all. -/
theorem girth_le_card_of_map {G H : CGraph} (f : G.V → H.V) (hinj : Function.Injective f)
    (hadj : ∀ x y, G.Adj x y = true → H.Adj (f x) (f y) = true) (hnac : ¬ G.IsAcyclic) :
    H.girth ≤ Fintype.card G.V := by
  simp only [IsAcyclic, SimpleGraph.IsAcyclic, not_forall, not_not] at hnac
  obtain ⟨v, c, hc⟩ := hnac
  obtain ⟨u, vs, hlen, hnd, hch, hcl⟩ := exists_cycleList_of_isCycle hc
  have h3 := hc.three_le_length
  have hmap : H.girth ≤ (vs.map f).length + 1 := by
    refine girth_le_of_cycleList (f u) (vs.map f) (by simp only [List.length_map]; omega) ?_ ?_ ?_
    · rw [show f u :: vs.map f = (u :: vs).map f from rfl]
      exact hnd.map hinj
    · rw [show f u :: vs.map f = (u :: vs).map f from rfl]
      exact (List.isChain_map f).2 (hch.imp_of_mem_imp fun a b _ _ hab ↦ hadj a b hab)
    · rw [getLastD_map]
      exact hadj _ _ hcl
  rw [List.length_map] at hmap
  exact le_trans hmap (by simpa using hnd.length_le_card)

/-- **Every vertex of a cycle list has two distinct neighbours in the list**: its predecessor and
its successor around the closed chain. -/
theorem cycleList_two_nbrs {G : CGraph} {u : G.V} {vs : List G.V}
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u)
    {x : G.V} (hx : x ∈ u :: vs) :
    ∃ a b, a ∈ u :: vs ∧ b ∈ u :: vs ∧ a ≠ b ∧ G.Adj x a = true ∧ G.Adj x b = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hn : (u :: vs).length = vs.length + 1 := List.length_cons ..
  have hi' : i < vs.length + 1 := by omega
  have hlast : (u :: vs)[vs.length]'(by simp) = vs.getLastD u := (getLastD_eq_getElem vs u).symm
  have hhead : (u :: vs)[0]'(by simp) = u := rfl
  have hsucc : ∀ j : ℕ, ∀ _ : j < vs.length + 1,
      G.Adj ((u :: vs)[j]'(by omega)) ((u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
        (by split_ifs <;> omega)) = true := by
    intro j hj
    by_cases hje : j + 1 = vs.length + 1
    · have e1 : (u :: vs)[j]'(by omega) = vs.getLastD u :=
        (getElem_congr_idx (u :: vs) (show j = vs.length from by omega) (by omega)).trans hlast
      have e2 : (u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
          (by split_ifs; omega) = u :=
        (getElem_congr_idx (u :: vs)
          (show (if j + 1 = vs.length + 1 then 0 else j + 1) = 0 from if_pos hje)
          (by split_ifs; omega)).trans hhead
      rw [e1, e2]
      exact hcl
    · have e2 : (u :: vs)[if j + 1 = vs.length + 1 then 0 else j + 1]'
          (by split_ifs; omega) = (u :: vs)[j + 1]'(by omega) :=
        getElem_congr_idx (u :: vs) (if_neg hje) (by split_ifs; omega)
      rw [e2]
      exact List.isChain_iff_getElem.1 hch j (by omega)
  refine ⟨(u :: vs)[if i + 1 = vs.length + 1 then 0 else i + 1]'(by split_ifs <;> omega),
    (u :: vs)[if i = 0 then vs.length else i - 1]'(by split_ifs <;> omega),
    List.getElem_mem _, List.getElem_mem _, ?_, hsucc i hi', ?_⟩
  · intro heq
    have := (List.Nodup.getElem_inj_iff hnd).1 heq
    split_ifs at this <;> omega
  · have hprev := hsucc (if i = 0 then vs.length else i - 1) (by split_ifs <;> omega)
    have e3 : (u :: vs)[if (if i = 0 then vs.length else i - 1) + 1 = vs.length + 1 then 0
          else (if i = 0 then vs.length else i - 1) + 1]'(by split_ifs <;> omega)
        = (u :: vs)[i]'(by omega) :=
      getElem_congr_idx (u :: vs) (by split_ifs <;> omega) (by split_ifs <;> omega)
    rw [e3] at hprev
    rw [G.symm]
    exact hprev

/-- A closed nodup chain of a graph `H` whose vertices carry distinct labels below `M`, with
adjacent vertices carrying adjacent labels, is impossible when the chain is shorter than `M`:
it would be a short cycle in `cycle M`. -/
theorem no_short_cycleList_of_labels {H : CGraph} {M : ℕ} (hM : 3 ≤ M) (gv : H.V → ℕ)
    (u : H.V) (vs : List H.V) (hbd : ∀ a ∈ u :: vs, gv a < M)
    (hginj : ∀ a ∈ u :: vs, ∀ b ∈ u :: vs, gv a = gv b → a = b)
    (hgadj : ∀ a ∈ u :: vs, ∀ b ∈ u :: vs, H.Adj a b = true →
      ∀ (ha : gv a < M) (hb : gv b < M), (cycle M).Adj ⟨gv a, ha⟩ ⟨gv b, hb⟩ = true)
    (h2 : 2 ≤ vs.length) (hlt : vs.length + 1 < M) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ H.Adj x y) (u :: vs)) (hcl : H.Adj (vs.getLastD u) u) :
    False := by
  obtain ⟨g, hgval⟩ : ∃ g : H.V → (cycle M).V, ∀ a ∈ u :: vs, (g a).1 = gv a :=
    ⟨fun v ↦ ⟨min (gv v) (M - 1), by omega⟩,
      fun a ha ↦ show min (gv a) (M - 1) = gv a from by have := hbd a ha; omega⟩
  have hmap : ∀ a, a ∈ u :: vs → ∀ b, b ∈ u :: vs → H.Adj a b = true →
      (cycle M).Adj (g a) (g b) = true := by
    intro a ha b hb hab
    have ea : g a = ⟨gv a, hbd a ha⟩ := Fin.ext (hgval a ha)
    have eb : g b = ⟨gv b, hbd b hb⟩ := Fin.ext (hgval b hb)
    rw [ea, eb]
    exact hgadj a ha b hb hab _ _
  have hlastmem : vs.getLastD u ∈ u :: vs := List.getLastD_mem_cons
  refine cycle_no_short_cycleList hM (g u) (vs.map g) (by simpa using h2) (by simpa using hlt)
    ?_ ?_ ?_
  · rw [show g u :: vs.map g = (u :: vs).map g from rfl]
    refine hnd.map_on fun a ha b hb hab ↦ ?_
    exact hginj a ha b hb ((hgval a ha).symm.trans ((congrArg Fin.val hab).trans (hgval b hb)))
  · rw [show g u :: vs.map g = (u :: vs).map g from rfl]
    exact (List.isChain_map g).2 (hch.imp_of_mem_imp fun a b ha hb hab ↦ hmap a ha b hb hab)
  · rw [getLastD_map]
    exact hmap _ hlastmem u (by simp) hcl

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
      push_neg at hcon
      obtain ⟨w, hw, hwM⟩ := hcon
      obtain ⟨x, hx, hxmax⟩ := exists_max_weight (fun v : (tadpole (m + 3) k).V ↦ v.1) u vs
      obtain ⟨a, b, ha, hb, hab, hxa, hxb⟩ := cycleList_two_nbrs h2 hnd hch hcl hx
      exact hab (tadpole_high_nbr_unique (Nat.le_trans hwM (hxmax w hw)) hxa hxb
        (hxmax a ha) (hxmax b hb))
    exact no_short_cycleList_of_labels (H := tadpole (m + 3) k) (by omega) (fun v ↦ v.1) u vs
      hlow (fun a _ b _ hab ↦ Fin.ext hab)
      (fun a ha b hb hadj _ _ ↦ cycle_adj_of_tadpole_adj (hlow a ha) (hlow b hb) hadj)
      h2 hlt hnd hch hcl

/-! ### The cycle with pendant vertices -/

/-- A pendant vertex hangs off exactly one vertex of the cycle. -/
theorem pendantEdges_unique_owner : ∀ (v off : ℕ) (ks : List ℕ) (p p' q : ℕ),
    (p, q) ∈ pendantEdges v off ks → (p', q) ∈ pendantEdges v off ks → p = p'
  | _, _, [], _, _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, p', q => by
      intro h h'
      have hb : ∀ r s : ℕ, (r, s) ∈ (List.range k).map (fun i ↦ (v, off + i)) →
          r = v ∧ s < off + k := by
        intro r s hr
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hr
        obtain ⟨i, hi, h1, h2⟩ := hr
        omega
      rw [pendantEdges, List.mem_append] at h h'
      rcases h with h | h <;> rcases h' with h' | h'
      · exact ((hb p q h).1).trans ((hb p' q h').1).symm
      · have hq := (hb p q h).2
        have := (mem_pendantEdges_bound (v + 1) (off + k) ks p' q h').2.1
        omega
      · have hq := (hb p' q h').2
        have := (mem_pendantEdges_bound (v + 1) (off + k) ks p q h).2.1
        omega
      · exact pendantEdges_unique_owner (v + 1) (off + k) ks p p' q h h'

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
      push_neg at hcon
      obtain ⟨p, q, hp, hq, hpq, hap, haq⟩ := cycleList_two_nbrs h2 hnd hch hcl ha
      exact hpq (cyclePendant_high_nbr_unique hks hcon hap haq)
    exact no_short_cycleList_of_labels (H := cyclePendant (m + 3) ks) (by omega) (fun v ↦ v.1) u vs
      hlow (fun a _ b _ hab ↦ Fin.ext hab)
      (fun a ha b hb hadj _ _ ↦ cycle_adj_of_cyclePendant_adj (hlow a ha) (hlow b hb) hadj)
      h2 hlt hnd hch hcl

/-! ## The grid and the king graph: independence, covering, domination, matching -/

/-- Two kings in the same `2 × 2` block of the board are a single move apart, so rounding both
coordinates down to the block index is injective on an independent set. -/
theorem indepNum_strongProduct_path_le (m n : ℕ) :
    (strongProduct (path m) (path n)).indepNum ≤ ((m + 1) / 2) * ((n + 1) / 2) := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (strongProduct (path m) (path n)).toSimple.exists_isNIndepSet_indepNum
  have hmaps : ∀ p ∈ s, ((p.1.1 / 2, p.2.1 / 2) : ℕ × ℕ) ∈
      (Finset.range ((m + 1) / 2)) ×ˢ (Finset.range ((n + 1) / 2)) := by
    intro p _
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hinj : ∀ p ∈ (s : Set (strongProduct (path m) (path n)).V),
      ∀ q ∈ (s : Set (strongProduct (path m) (path n)).V),
      ((p.1.1 / 2, p.2.1 / 2) : ℕ × ℕ) = (q.1.1 / 2, q.2.1 / 2) → p = q := by
    intro p hp q hq heq
    by_contra hpq
    have hd1 : p.1.1 / 2 = q.1.1 / 2 := congrArg Prod.fst heq
    have hd2 : p.2.1 / 2 = q.2.1 / 2 := congrArg Prod.snd heq
    refine hs hp hq hpq ?_
    rw [CGraph.toSimple_adj, strongProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    refine ⟨hpq, ?_, ?_⟩
    · by_cases he : p.1.1 = q.1.1
      · exact Or.inl (Fin.ext he)
      · exact Or.inr ((path_adj_val m p.1 q.1).2 ⟨he, by omega⟩)
    · by_cases he : p.2.1 = q.2.1
      · exact Or.inl (Fin.ext he)
      · exact Or.inr ((path_adj_val n p.2 q.2).2 ⟨he, by omega⟩)
  calc (strongProduct (path m) (path n)).indepNum
      = s.card := hcard.symm
    _ ≤ ((Finset.range ((m + 1) / 2)) ×ˢ (Finset.range ((n + 1) / 2))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ((m + 1) / 2) * ((n + 1) / 2) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- One half of "a king moves to a neighbouring square": consecutive or equal indices in a path
give the `Pₖ`-component of a strong-product adjacency. -/
theorem path_step_or_eq {k : ℕ} (p q : (path k).V)
    (h : p.1 = q.1 ∨ p.1 + 1 = q.1 ∨ q.1 + 1 = p.1) :
    (decide (p = q) || (path k).Adj p q) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr ((path_adj_val k p q).2 ⟨by omega, by omega⟩)

/-- The converse of `path_step_or_eq`. -/
theorem val_step_or_eq_of_path_step {k : ℕ} {p q : (path k).V}
    (h : (decide (p = q) || (path k).Adj p q) = true) :
    p.1 = q.1 ∨ p.1 + 1 = q.1 ∨ q.1 + 1 = p.1 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr ((path_adj_val k p q).1 h).2

/-- **Kings every third rank and file dominate the board.**  The king at block `(a, b)` sits on
square `(3a + 1, 3b + 1)`, pushed back to the last rank or file when that would fall off the
board, and covers the whole `3 × 3` block. -/
theorem domNum_strongProduct_path_le (m n : ℕ) :
    (strongProduct (path m) (path n)).domNum ≤ ((m + 2) / 3) * ((n + 2) / 3) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  let f : ℕ × ℕ → (strongProduct (path m) (path n)).V := fun ab ↦
    (⟨min (3 * ab.1 + 1) (m - 1), by omega⟩, ⟨min (3 * ab.2 + 1) (n - 1), by omega⟩)
  have hf1 : ∀ ab : ℕ × ℕ, (f ab).1.1 = min (3 * ab.1 + 1) (m - 1) := fun _ ↦ rfl
  have hf2 : ∀ ab : ℕ × ℕ, (f ab).2.1 = min (3 * ab.2 + 1) (n - 1) := fun _ ↦ rfl
  have hmem : ∀ v : (strongProduct (path m) (path n)).V,
      f (v.1.1 / 3, v.2.1 / 3) ∈
        (Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).image f := by
    intro v
    refine Finset.mem_image_of_mem f ?_
    have h1 := v.1.isLt
    have h2 := v.2.isLt
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  have hdom : (strongProduct (path m) (path n)).IsDominatingSet
      ((Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).image f) := by
    intro v
    have h1 := v.1.isLt
    have h2 := v.2.isLt
    have e1 := hf1 (v.1.1 / 3, v.2.1 / 3)
    have e2 := hf2 (v.1.1 / 3, v.2.1 / 3)
    by_cases hv : f (v.1.1 / 3, v.2.1 / 3) = v
    · exact Or.inl (hv ▸ hmem v)
    · refine Or.inr ⟨f (v.1.1 / 3, v.2.1 / 3), hmem v, ?_⟩
      rw [strongProduct_adj]
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨hv, path_step_or_eq _ _ (by omega), path_step_or_eq _ _ (by omega)⟩
  simpa [Finset.card_product] using
    (domNum_le_card_of_isDominatingSet hdom).trans (Finset.card_image_le)

/-- **A king cannot cover two squares three files apart.**  The `⌈m/3⌉ · ⌈n/3⌉` squares with both
coordinates divisible by `3` have pairwise disjoint closed neighbourhoods, so every dominating set
has at least that many kings — rounding a king's coordinates to the block it covers is onto. -/
theorem le_domNum_strongProduct_path (m n : ℕ) :
    ((m + 2) / 3) * ((n + 2) / 3) ≤ (strongProduct (path m) (path n)).domNum := by
  classical
  obtain ⟨s, hcard, hs⟩ := (strongProduct (path m) (path n)).exists_isDominatingSet_domNum
  rw [← hcard]
  have hsurj : Set.SurjOn (fun p : (strongProduct (path m) (path n)).V ↦
      (((p.1.1 + 1) / 3, (p.2.1 + 1) / 3) : ℕ × ℕ)) ↑s
      ↑(Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)) := by
    rintro ⟨a, b⟩ hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hab
    obtain ⟨ha, hb⟩ := hab
    have ha3 : 3 * a < m := by omega
    have hb3 : 3 * b < n := by omega
    have hkey : ∀ u : (strongProduct (path m) (path n)).V,
        (u.1.1 = 3 * a ∨ u.1.1 + 1 = 3 * a ∨ 3 * a + 1 = u.1.1) →
        (u.2.1 = 3 * b ∨ u.2.1 + 1 = 3 * b ∨ 3 * b + 1 = u.2.1) →
        (((u.1.1 + 1) / 3, (u.2.1 + 1) / 3) : ℕ × ℕ) = (a, b) := by
      intro u h1 h2
      simp only [Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    rcases hs ((⟨3 * a, ha3⟩, ⟨3 * b, hb3⟩) :
        (strongProduct (path m) (path n)).V) with hv | ⟨u, hu, hadj⟩
    · exact ⟨_, hv, hkey _ (Or.inl rfl) (Or.inl rfl)⟩
    · rw [strongProduct_adj] at hadj
      simp only [Bool.and_eq_true] at hadj
      exact ⟨u, hu, hkey u (val_step_or_eq_of_path_step hadj.2.1)
        (val_step_or_eq_of_path_step hadj.2.2)⟩
  calc ((m + 2) / 3) * ((n + 2) / 3)
      = (Finset.range ((m + 2) / 3) ×ˢ Finset.range ((n + 2) / 3)).card := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]
    _ ≤ s.card := Finset.card_le_card_of_surjOn _ hsurj

/-! ### The boustrophedon numbering of a board -/

/-- **Consecutive squares of the boustrophedon numbering are adjacent.**  Numbering an `m × n`
board row by row, left to right along the even rows and right to left along the odd ones, two
squares whose numbers differ by one share a row and are neighbouring columns, or share a column
and are neighbouring rows. -/
theorem snake_step {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + (if x % 2 = 0 then y else n - 1 - y) + 1
      = x' * n + (if x' % 2 = 0 then y' else n - 1 - y')) :
    (x = x' ∧ (y + 1 = y' ∨ y' + 1 = y)) ∨ (y = y' ∧ x + 1 = x') := by
  have hs : (if x % 2 = 0 then y else n - 1 - y) < n := by split; omega; omega
  have hs' : (if x' % 2 = 0 then y' else n - 1 - y') < n := by split; omega; omega
  rcases row_col_step hs hs' h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · subst h1
    exact Or.inl ⟨rfl, by split_ifs at h2 <;> omega⟩
  · exact Or.inr ⟨by split_ifs at h2 h3 <;> omega, h1⟩

/-- The boustrophedon numbering is injective. -/
theorem snake_inj {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + (if x % 2 = 0 then y else n - 1 - y)
      = x' * n + (if x' % 2 = 0 then y' else n - 1 - y')) : x = x' ∧ y = y' := by
  have hs : (if x % 2 = 0 then y else n - 1 - y) < n := by split; omega; omega
  have hs' : (if x' % 2 = 0 then y' else n - 1 - y') < n := by split; omega; omega
  obtain ⟨h1, h2⟩ := row_col_eq hs hs' h
  subst h1
  exact ⟨rfl, by split_ifs at h2 <;> omega⟩

/-- **The independence number of a grid is at most `⌈mn/2⌉`.**  The boustrophedon numbering is a
Hamiltonian path, so pairing up the squares numbered `2i` and `2i + 1` partitions the board into
`⌈mn/2⌉` edges and single squares, and an independent set meets each of them once. -/
theorem indepNum_cartesianProduct_path_le (m n : ℕ) :
    (cartesianProduct (path m) (path n)).indepNum ≤ (m * n + 1) / 2 := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (cartesianProduct (path m) (path n)).toSimple.exists_isNIndepSet_indepNum
  let L : (cartesianProduct (path m) (path n)).V → ℕ := fun p ↦
    p.1.1 * n + (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1)
  have hLval : ∀ p : (cartesianProduct (path m) (path n)).V,
      L p = p.1.1 * n + (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1) := fun _ ↦ rfl
  have hLlt : ∀ p : (cartesianProduct (path m) (path n)).V, L p < m * n := by
    intro p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    have h3 : (p.1.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n h1
    have h4 : (p.1.1 + 1) * n = p.1.1 * n + n := by ring
    have h5 : (if p.1.1 % 2 = 0 then p.2.1 else n - 1 - p.2.1) < n := by split; omega; omega
    rw [hLval]
    omega
  have hstep : ∀ p q : (cartesianProduct (path m) (path n)).V, L p + 1 = L q →
      (cartesianProduct (path m) (path n)).Adj p q = true := by
    intro p q h
    have h1 := p.2.isLt
    have h2 := q.2.isLt
    rw [hLval, hLval] at h
    rw [cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rcases snake_step h1 h2 h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Or.inl ⟨Fin.ext hx, (path_adj_val n p.2 q.2).2 ⟨by omega, by omega⟩⟩
    · exact Or.inr ⟨(path_adj_val m p.1 q.1).2 ⟨by omega, by omega⟩, Fin.ext hy⟩
  have hmaps : ∀ p ∈ s, L p / 2 ∈ Finset.range ((m * n + 1) / 2) := by
    intro p _
    have := hLlt p
    simp only [Finset.mem_range]
    omega
  have hinj : ∀ p ∈ (s : Set (cartesianProduct (path m) (path n)).V),
      ∀ q ∈ (s : Set (cartesianProduct (path m) (path n)).V), L p / 2 = L q / 2 → p = q := by
    intro p hp q hq heq
    by_contra hpq
    have hne : L p ≠ L q := by
      intro he
      rw [hLval, hLval] at he
      obtain ⟨h1, h2⟩ := snake_inj p.2.isLt q.2.isLt he
      exact hpq (Prod.ext (Fin.ext h1) (Fin.ext h2))
    have hadj : (cartesianProduct (path m) (path n)).Adj p q = true := by
      rcases (by omega : L p + 1 = L q ∨ L q + 1 = L p) with h | h
      · exact hstep p q h
      · rw [(cartesianProduct (path m) (path n)).symm]
        exact hstep q p h
    exact hs hp hq hpq (by rw [CGraph.toSimple_adj]; exact hadj)
  calc (cartesianProduct (path m) (path n)).indepNum
      = s.card := hcard.symm
    _ ≤ (Finset.range ((m * n + 1) / 2)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (m * n + 1) / 2 := Finset.card_range _

/-! ### Matchings from a list of disjoint edges -/

/-- **`k` pairwise disjoint edges give `ν ≥ k`.**  Each edge is a vertex of the line graph, and
disjointness is exactly non-adjacency there. -/
theorem le_indepNum_lineGraph_of_pairing {G : CGraph} {k : ℕ}
    (a b : Fin k → G.V) (hadj : ∀ i, G.Adj (a i) (b i) = true)
    (hdisj : ∀ i j : Fin k, i ≠ j → a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j) :
    k ≤ (lineGraph G).indepNum := by
  classical
  let E : Fin k → (lineGraph G).V := fun i ↦
    ⟨Sym2.mk (a i, b i), by rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact hadj i⟩
  have hEinj : Function.Injective E := by
    intro i j hij
    by_contra hne
    obtain ⟨h1, h2, h3, h4⟩ := hdisj i j hne
    have hval : Sym2.mk (a i, b i) = Sym2.mk (a j, b j) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.1 hval with ⟨he, _⟩ | ⟨he, _⟩
    · exact h1 he
    · exact h2 he
  let S : Finset (lineGraph G).V := Finset.univ.image E
  have hScard : S.card = k := by
    rw [Finset.card_image_of_injective _ hEinj, Finset.card_fin]
  have hSindep : (lineGraph G).toSimple.IsIndepSet (S : Set (lineGraph G).V) := by
    intro e he f hf hef
    simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at he hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    have hij : i ≠ j := fun h ↦ hef (by rw [h])
    obtain ⟨h1, h2, h3, h4⟩ := hdisj i j hij
    rw [toSimple_adj, lineGraph_adj]
    simp only [E, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Sym2.mem_iff, not_and, not_exists]
    rintro - v (rfl | rfl) (h | h)
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  have := hSindep.card_le_indepNum
  rwa [hScard] at this

/-- **The boustrophedon matching of a board.**  Pairing the square numbered `2i` with the one
numbered `2i + 1` gives `⌊mn/2⌋` disjoint edges in any graph on the board that contains the grid
adjacencies. -/
theorem le_indepNum_lineGraph_board {m n : ℕ} (G : CGraph)
    (φ : (path m).V × (path n).V → G.V) (hφ : Function.Injective φ)
    (hadj : ∀ p q : (path m).V × (path n).V,
      ((p.1 = q.1 ∧ (p.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = p.2.1)) ∨ (p.2 = q.2 ∧ p.1.1 + 1 = q.1.1)) →
      G.Adj (φ p) (φ q) = true) :
    m * n / 2 ≤ (lineGraph G).indepNum := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  let P : ℕ → (path m).V × (path n).V := fun k ↦
    (⟨min (k / n) (m - 1), by omega⟩,
      ⟨if (k / n) % 2 = 0 then k % n else n - 1 - k % n,
        by have := Nat.mod_lt k hn; split; omega; omega⟩)
  have hProw : ∀ k, (P k).1.1 = min (k / n) (m - 1) := fun _ ↦ rfl
  have hPcol : ∀ k, (P k).2.1 = if (k / n) % 2 = 0 then k % n else n - 1 - k % n := fun _ ↦ rfl
  have hPval : ∀ k, k < m * n →
      (P k).1.1 * n + (if (P k).1.1 % 2 = 0 then (P k).2.1 else n - 1 - (P k).2.1) = k := by
    intro k hk
    have hdiv : k / n < m := (Nat.div_lt_iff_lt_mul hn).2 hk
    have hmod : k % n < n := Nat.mod_lt k hn
    have hrow : (P k).1.1 = k / n := by rw [hProw]; omega
    rw [hrow, hPcol]
    split_ifs with hpar
    · exact Nat.div_add_mod' k n
    · rw [show n - 1 - (n - 1 - k % n) = k % n by omega]
      exact Nat.div_add_mod' k n
  have hPinj : ∀ s t, s < m * n → t < m * n → P s = P t → s = t := by
    intro s t hs ht hst
    rw [← hPval s hs, ← hPval t ht, hst]
  have hstep : ∀ s, s + 1 < m * n → G.Adj (φ (P s)) (φ (P (s + 1))) = true := by
    intro s hs
    refine hadj _ _ ?_
    have h1 := hPval s (by omega)
    have h2 := hPval (s + 1) hs
    have hy := (P s).2.isLt
    have hy' := (P (s + 1)).2.isLt
    rcases snake_step (n := n) (x := (P s).1.1) (y := (P s).2.1) (x' := (P (s + 1)).1.1)
      (y' := (P (s + 1)).2.1) hy hy' (by omega) with ⟨hx, hcol⟩ | ⟨hcol, hx⟩
    · exact Or.inl ⟨Fin.ext hx, hcol⟩
    · exact Or.inr ⟨Fin.ext hcol, hx⟩
  have hlt : ∀ i : Fin (m * n / 2), 2 * i.1 + 1 < m * n := by
    intro i
    have := i.isLt
    omega
  refine le_indepNum_lineGraph_of_pairing (fun i ↦ φ (P (2 * i.1)))
    (fun i ↦ φ (P (2 * i.1 + 1))) (fun i ↦ hstep _ (hlt i)) ?_
  have hne : ∀ s t, s < m * n → t < m * n → s ≠ t → φ (P s) ≠ φ (P t) := by
    intro s t hs ht hst h
    exact hst (hPinj s t hs ht (hφ h))
  intro i j hij
  have hij' : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
  exact ⟨hne _ _ (by have := hlt i; omega) (by have := hlt j; omega) (by omega),
    hne _ _ (by have := hlt i; omega) (hlt j) (by omega),
    hne _ _ (hlt i) (by have := hlt j; omega) (by omega),
    hne _ _ (hlt i) (hlt j) (by omega)⟩

/-- The grid contains `⌊mn/2⌋` disjoint edges. -/
theorem le_indepNum_lineGraph_grid (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (cartesianProduct (path m) (path n))).indepNum := by
  refine le_indepNum_lineGraph_board _ (fun p ↦ p) (fun _ _ h ↦ h) ?_
  intro p q h
  rw [cartesianProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (path_adj_val n p.2 q.2).2 ⟨by omega, h2⟩⟩
  · exact Or.inr ⟨(path_adj_val m p.1 q.1).2 ⟨by omega, Or.inl h2⟩, h1⟩

/-- The king graph contains `⌊mn/2⌋` disjoint edges: the grid's own matching. -/
theorem le_indepNum_lineGraph_king (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (strongProduct (path m) (path n))).indepNum := by
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


/-! ### The independence number of a torus with an even side -/

/-- **The checkerboard on a torus with an even side.**  Take the first even number of rows and,
in row `a`, the columns congruent to `a` mod `2`.  Two chosen squares in the same row are two
columns apart, and two in adjacent rows are in columns of opposite parity, so the set is
independent; the wrap-around is safe in the column direction because `n` is even, and in the row
direction because the last row used is `2⌊m/2⌋ - 1`, which is adjacent to row `0` only when `m`
is even, when it has the opposite parity. -/
theorem le_indepNum_cartesianProduct_cycle (m n : ℕ) (hev : n % 2 = 0) :
    n * (m / 2) ≤ (cartesianProduct (cycle m) (cycle n)).indepNum := by
  classical
  let Φ : Fin (2 * (m / 2)) × Fin (n / 2) → (cartesianProduct (cycle m) (cycle n)).V := fun ab ↦
    (⟨ab.1.1, by have := ab.1.isLt; omega⟩, ⟨2 * ab.2.1 + ab.1.1 % 2, by have := ab.2.isLt; omega⟩)
  have hΦ1 : ∀ ab, (Φ ab).1.1 = ab.1.1 := fun _ ↦ rfl
  have hΦ2 : ∀ ab, (Φ ab).2.1 = 2 * ab.2.1 + ab.1.1 % 2 := fun _ ↦ rfl
  have hrow : ∀ ab, (Φ ab).1.1 < m := by
    intro ab; rw [hΦ1]; have := ab.1.isLt; omega
  have hcol : ∀ ab, (Φ ab).2.1 < n := by
    intro ab; rw [hΦ2]; have := ab.2.isLt; omega
  have hinj : Function.Injective Φ := by
    intro x y h
    have h1 : (Φ x).1.1 = (Φ y).1.1 := by rw [h]
    have h2 : (Φ x).2.1 = (Φ y).2.1 := by rw [h]
    simp only [hΦ1] at h1
    simp only [hΦ2] at h2
    exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))
  set S : Finset (cartesianProduct (cycle m) (cycle n)).V := Finset.univ.image Φ with hS
  have hindep : (cartesianProduct (cycle m) (cycle n)).toSimple.IsIndepSet
      (S : Set (cartesianProduct (cycle m) (cycle n)).V) := by
    intro p hp q hq _
    simp only [hS, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hp hq
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    have hx1 := x.1.isLt
    have hx2 := x.2.isLt
    have hy1 := y.1.isLt
    have hy2 := y.2.isLt
    rw [toSimple_adj, cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and]
    refine ⟨fun heq hadj ↦ ?_, fun hadj heq ↦ ?_⟩
    · have hv := (cycle_adj_val n (Φ x).2 (Φ y).2).1 hadj
      have hr : (Φ x).1.1 = (Φ y).1.1 := by rw [heq]
      rw [mod_succ_norm (hcol x), mod_succ_norm (hcol y)] at hv
      simp only [hΦ1] at hr
      simp only [hΦ2] at hv
      rcases hv.2 with hv | hv <;> split_ifs at hv <;> omega
    · have hv := (cycle_adj_val m (Φ x).1 (Φ y).1).1 hadj
      have hc : (Φ x).2.1 = (Φ y).2.1 := by rw [heq]
      rw [mod_succ_norm (hrow x), mod_succ_norm (hrow y)] at hv
      simp only [hΦ2] at hc
      simp only [hΦ1] at hv
      rcases hv.2 with hv | hv <;> split_ifs at hv <;> omega
  have hcard : S.card = n * (m / 2) := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    have hn2 : 2 * (n / 2) = n := by omega
    calc 2 * (m / 2) * (n / 2) = m / 2 * (2 * (n / 2)) := by ring
      _ = n * (m / 2) := by rw [hn2]; ring
  exact hcard ▸ hindep.card_le_indepNum

/-- The torus contains `⌊mn/2⌋` disjoint edges: it contains the grid, so the boustrophedon
matching of `le_indepNum_lineGraph_board` works unchanged. -/
theorem le_indepNum_lineGraph_torus (m n : ℕ) :
    m * n / 2 ≤ (lineGraph (cartesianProduct (cycle m) (cycle n))).indepNum := by
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
    m * n / 2 ≤ (lineGraph (cartesianProduct (cycle m) (path n))).indepNum := by
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

/-! ### Edge colourings of a cartesian product

The two factors' edges never meet outside a common vertex, and at a vertex of `G □ H` the edges
in the `G` direction and the edges in the `H` direction are told apart by whether the first
coordinate moves.  So the two palettes can simply be laid side by side. -/

/-- Colour an edge of `G □ H` with `H`'s palette if it moves the second coordinate, and with
`G`'s palette otherwise, the two palettes placed side by side in `Fin (k + l)`. -/
def prodCol {G H : CGraph} {k l : ℕ}
    (c : G.V → G.V → Fin k) (d : H.V → H.V → Fin l) (p q : G.V × H.V) : Fin (k + l) :=
  if p.1 = q.1 then Fin.natAdd k (d p.2 q.2) else Fin.castAdd l (c p.1 q.1)

theorem prodCol_symm {G H : CGraph} {k l : ℕ}
    {c : G.V → G.V → Fin k} {d : H.V → H.V → Fin l}
    (hc : ∀ x y, c x y = c y x) (hd : ∀ x y, d x y = d y x) (p q : G.V × H.V) :
    prodCol c d p q = prodCol c d q p := by
  unfold prodCol
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h.symm, hd]
  · rw [if_neg h, if_neg (fun hh ↦ h hh.symm), hc]

/-- **The chromatic index of a cartesian product is at most the sum of the two factors'.** -/
theorem chromNum_lineGraph_cartesianProduct_le {G H : CGraph}
    {k l : ℕ} (c : G.V → G.V → Fin k) (d : H.V → H.V → Fin l)
    (hc : ∀ x y, c x y = c y x) (hd : ∀ x y, d x y = d y x)
    (hcp : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w)
    (hdp : ∀ u v w : H.V, H.Adj u v = true → H.Adj u w = true → v ≠ w → d u v ≠ d u w) :
    (lineGraph (cartesianProduct G H)).chromNum ≤ k + l := by
  refine chromNum_lineGraph_le_of_edgeColouring (G := cartesianProduct G H) (prodCol c d)
    (prodCol_symm hc hd) ?_
  intro u v w huv huw hvw
  rw [cartesianProduct_adj] at huv huw
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at huv huw
  unfold prodCol
  have hu1 : ∀ x : G.V × H.V, G.Adj u.1 x.1 = true → ¬ u.1 = x.1 := by
    intro x hx h
    rw [← h] at hx
    exact G.loopless u.1 hx
  rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases huw with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [if_pos h1, if_pos h3]
    have hne : v.2 ≠ w.2 := fun h ↦ hvw (Prod.ext (h1 ▸ h3) h)
    refine fun hh ↦ hdp u.2 v.2 w.2 h2 h4 hne (Fin.ext ?_)
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd] at hval
    omega
  · rw [if_pos h1, if_neg (hu1 w h3)]
    intro hh
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd, Fin.castAdd, Fin.castLE] at hval
    have := (c u.1 w.1).isLt
    omega
  · rw [if_neg (hu1 v h1), if_pos h3]
    intro hh
    have hval := congrArg Fin.val hh
    simp only [Fin.natAdd, Fin.castAdd, Fin.castLE] at hval
    have := (c u.1 v.1).isLt
    omega
  · rw [if_neg (hu1 v h1), if_neg (hu1 w h3)]
    have hne : v.1 ≠ w.1 := fun h ↦ hvw (Prod.ext h (h2 ▸ h4))
    refine fun hh ↦ hcp u.1 v.1 w.1 h1 h3 hne (Fin.ext ?_)
    have hval := congrArg Fin.val hh
    simp only [Fin.castAdd, Fin.castLE] at hval
    omega

/-- A proper colouring of the line graph *is* an edge colouring: read it back as a symmetric
function on ordered pairs, with a fixed junk value off the edges.  This is the converse of
`chromNum_lineGraph_le_of_edgeColouring`, and it needs a colour to spare for the junk. -/
theorem exists_edgeColouring {G : CGraph} {k : ℕ}
    (h : (lineGraph G).chromNum ≤ k) (j : Fin k) :
    ∃ c : G.V → G.V → Fin k, (∀ x y, c x y = c y x) ∧
      ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w := by
  obtain ⟨col⟩ := chromNum_le_iff_colorable.1 h
  refine ⟨fun x y ↦ if hxy : s(x, y) ∈ G.toSimple.edgeSet then col ⟨s(x, y), hxy⟩ else j, ?_, ?_⟩
  · intro x y
    simp only [Sym2.eq_swap]
  · intro u v w huv huw hvw
    have hev : s(u, v) ∈ G.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact huv
    have hew : s(u, w) ∈ G.toSimple.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, toSimple_adj]; exact huw
    beta_reduce
    rw [dif_pos hev, dif_pos hew]
    refine col.valid ?_
    have hne : (⟨s(u, v), hev⟩ : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) ≠ ⟨s(u, w), hew⟩ := by
      intro hh
      exact hvw ((Sym2.congr_right).1 (Subtype.ext_iff.1 hh))
    show (lineGraph G).Adj _ _ = true
    rw [lineGraph_adj]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hne, u, by simp, by simp⟩

/-- **The chromatic index of a cartesian product is at most the sum of the two factors'**, with
no explicit colouring in sight: read one back out of each factor's line-graph colouring. -/
theorem chromNum_lineGraph_cartesianProduct_le_add {G H : CGraph}
 (hG : 0 < (lineGraph G).chromNum) (hH : 0 < (lineGraph H).chromNum) :
    (lineGraph (cartesianProduct G H)).chromNum
      ≤ (lineGraph G).chromNum + (lineGraph H).chromNum := by
  obtain ⟨c, hc, hcp⟩ := exists_edgeColouring (G := G) le_rfl ⟨0, hG⟩
  obtain ⟨d, hd, hdp⟩ := exists_edgeColouring (G := H) le_rfl ⟨0, hH⟩
  exact chromNum_lineGraph_cartesianProduct_le c d hc hd hcp hdp

/-! ### The independence number of a torus with two odd sides -/

/-- Two entries of one column of the staircase are never cyclically adjacent. -/
theorem staircase_same (a c i i' : ℕ) (hi : i ≤ a) (hi' : i' ≤ a) :
    (c + 2 * i + 1) % (2 * a + 3) ≠ (c + 2 * i') % (2 * a + 3) := by
  intro he
  have h1 : c + (2 * i + 1) ≡ c + 2 * i' [MOD 2 * a + 3] := by
    simpa [Nat.add_assoc] using he
  exact two_mul_succ_not_modEq a i i' hi hi' (Nat.ModEq.add_left_cancel' _ h1)

/-- Entries of two neighbouring columns never coincide. -/
theorem staircase_clash (a s t i i' : ℕ) (hi : i ≤ a) (hi' : i' ≤ a)
    (hst : (s + 1) % (2 * a + 3) = t % (2 * a + 3)) :
    (s + 2 * i) % (2 * a + 3) ≠ (t + 2 * i') % (2 * a + 3) := by
  intro he
  have h1 : s + 2 * i ≡ t + 2 * i' [MOD 2 * a + 3] := he
  have h2 : t + 2 * i' ≡ s + 1 + 2 * i' [MOD 2 * a + 3] :=
    Nat.ModEq.add_right _ (Nat.ModEq.symm hst)
  have h3 : s + 2 * i ≡ s + (1 + 2 * i') [MOD 2 * a + 3] := by
    simpa [Nat.add_assoc] using h1.trans h2
  have h4 : 2 * i ≡ 1 + 2 * i' [MOD 2 * a + 3] := Nat.ModEq.add_left_cancel' _ h3
  exact two_mul_succ_not_modEq a i' i hi' hi (by simpa [Nat.add_comm] using h4.symm)

/-- **The staircase on a torus with two odd sides.** -/
theorem le_indepNum_cartesianProduct_cycle_odd (a b : ℕ) (hab : a ≤ b) :
    (2 * b + 3) * (a + 1) ≤
      (cartesianProduct (cycle (2 * a + 3)) (cycle (2 * b + 3))).indepNum := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ,
      w = fun j ↦ if j ≤ a + b + 3 then j else 2 * (a + b + 3) - j := ⟨_, rfl⟩
  have hstep : ∀ j j' : ℕ, j < 2 * b + 3 → (j + 1) % (2 * b + 3) = j' →
      w j + 1 ≡ w j' [MOD 2 * a + 3] ∨ w j' + 1 ≡ w j [MOD 2 * a + 3] := by
    intro j j' hj hj'
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hlt | heq
    · have hjj : j' = j + 1 := by rw [← hj']; exact Nat.mod_eq_of_lt hlt
      subst hjj
      simp only [hw]
      split_ifs with h1 h2 h2
      · exact Or.inl (Nat.ModEq.refl _)
      · refine Or.inr ?_
        have he : 2 * (a + b + 3) - (j + 1) + 1 = j := by omega
        rw [he]
      · exact absurd h2 (by omega)
      · refine Or.inr ?_
        have he : 2 * (a + b + 3) - (j + 1) + 1 = 2 * (a + b + 3) - j := by omega
        rw [he]
    · have hj0 : j = 2 * b + 2 := by omega
      have hj'0 : j' = 0 := by rw [← hj', hj0]; simp
      subst hj0; subst hj'0
      simp only [hw]
      rcases eq_or_lt_of_le hab with rfl | hlt'
      · refine Or.inl ?_
        rw [if_pos (by omega), if_pos (by omega)]
        show (2 * a + 2 + 1) % (2 * a + 3) = 0 % (2 * a + 3)
        simp
      · refine Or.inr ?_
        rw [if_pos (by omega)]
        have he : (if 2 * b + 2 ≤ a + b + 3 then 2 * b + 2
            else 2 * (a + b + 3) - (2 * b + 2)) = 2 * a + 3 + 1 := by
          split_ifs with h <;> omega
        rw [he]
        show (0 + 1) % (2 * a + 3) = (2 * a + 3 + 1) % (2 * a + 3)
        rw [Nat.add_mod_left]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin (2 * b + 3) × Fin (a + 1) →
      (cartesianProduct (cycle (2 * a + 3)) (cycle (2 * b + 3))).V,
      Φ = fun x ↦ (⟨(w x.1.1 + 2 * x.2.1) % (2 * a + 3), Nat.mod_lt _ (by omega)⟩, x.1) :=
    ⟨_, rfl⟩
  have hΦ1 : ∀ x, (Φ x).1.1 = (w x.1.1 + 2 * x.2.1) % (2 * a + 3) := by simp [hΦ]
  have hΦ2 : ∀ x, (Φ x).2 = x.1 := by simp [hΦ]
  have hinj : Function.Injective Φ := by
    intro x y h
    have h2 : x.1 = y.1 := by rw [← hΦ2 x, ← hΦ2 y, h]
    have h1 : (Φ x).1.1 = (Φ y).1.1 := by rw [h]
    rw [hΦ1, hΦ1, h2] at h1
    have hme : w y.1.1 + 2 * x.2.1 ≡ w y.1.1 + 2 * y.2.1 [MOD 2 * a + 3] := h1
    have h3 : 2 * x.2.1 ≡ 2 * y.2.1 [MOD 2 * a + 3] := Nat.ModEq.add_left_cancel' _ hme
    have hx := x.2.isLt
    have hy := y.2.isLt
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact Prod.ext h2 (Fin.ext (by omega))
  set S : Finset (cartesianProduct (cycle (2 * a + 3)) (cycle (2 * b + 3))).V :=
    Finset.univ.image Φ with hS
  have hindep : (cartesianProduct (cycle (2 * a + 3)) (cycle (2 * b + 3))).toSimple.IsIndepSet
      (S : Set (cartesianProduct (cycle (2 * a + 3)) (cycle (2 * b + 3))).V) := by
    intro P hP Q hQ _
    simp only [hS, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hP hQ
    obtain ⟨x, rfl⟩ := hP
    obtain ⟨y, rfl⟩ := hQ
    have hxi := x.2.isLt
    have hyi := y.2.isLt
    have hxj := x.1.isLt
    have hyj := y.1.isLt
    rw [toSimple_adj, cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and]
    refine ⟨fun heq hadj ↦ ?_, fun hadj heq ↦ ?_⟩
    · have hrow : (w x.1.1 + 2 * x.2.1) % (2 * a + 3)
          = (w y.1.1 + 2 * y.2.1) % (2 * a + 3) := by
        rw [← hΦ1, ← hΦ1, heq]
      have hv := (cycle_adj_val (2 * b + 3) (Φ x).2 (Φ y).2).1 hadj
      rw [hΦ2, hΦ2] at hv
      rcases hv.2 with hc | hc
      · rcases hstep x.1.1 y.1.1 hxj hc with h | h
        · exact staircase_clash a (w x.1.1) (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) h hrow
        · exact staircase_clash a (w y.1.1) (w x.1.1) y.2.1 x.2.1 (by omega) (by omega) h
            hrow.symm
      · rcases hstep y.1.1 x.1.1 hyj hc with h | h
        · exact staircase_clash a (w y.1.1) (w x.1.1) y.2.1 x.2.1 (by omega) (by omega) h
            hrow.symm
        · exact staircase_clash a (w x.1.1) (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) h hrow
    · have hcol : x.1 = y.1 := by rw [← hΦ2 x, ← hΦ2 y, heq]
      have hv := (cycle_adj_val (2 * a + 3) (Φ x).1 (Φ y).1).1 hadj
      rw [hΦ1, hΦ1, hcol] at hv
      rcases hv.2 with hr | hr
      · rw [Nat.mod_add_mod] at hr
        exact staircase_same a (w y.1.1) x.2.1 y.2.1 (by omega) (by omega) hr
      · rw [Nat.mod_add_mod] at hr
        exact staircase_same a (w y.1.1) y.2.1 x.2.1 (by omega) (by omega) hr
  have hcard : S.card = (2 * b + 3) * (a + 1) := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  exact hcard ▸ hindep.card_le_indepNum

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
    push_neg at hc
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

end CGraph
