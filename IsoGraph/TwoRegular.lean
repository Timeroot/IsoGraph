import IsoGraph.Spectrum
import IsoGraph.SmallGraphs

/-!
# Two-regular graphs

Every vertex of a connected graph of degree two has exactly two neighbours, so from any starting
arc there is only one way to walk: at each step, leave by the edge you did not arrive on.  The walk
is deterministic, it is reversible, and the graph is finite, so it must close up into a cycle — and
because the graph is connected, that cycle is the whole graph.  That is the only content of this
file: **a connected 2-regular graph is a cycle** (`eq_cycle_of_isRegularWith_two`), together with
what follows from it spectrally.

The spectral consequence is that cycles are determined by their spectrum.  A graph cospectral with
`Cₙ` is regular of the same degree and connected (both are read off the characteristic polynomial,
in `Spectrum.lean`), so it is 2-regular and connected, so it is a cycle on the same number of
vertices.  `Spectrum.lean` lists `IsDS` for the cycle among the things it does not prove; this file
closes that gap, without going through Smith's classification of the graphs of spectral radius at
most two.

The last section spends the criterion on the named families.  For most of them only one member is
2-regular and connected, so only one member is settled — the square turns up four times over, as
`Q₂`, as `K₂,₂`, as the two-rung ladder and as the cocktail party graph on two pairs.  The general
question stays open for all of these families; `IsDS` is hard, and the library records where it is
known rather than pretending otherwise.
-/

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

namespace CGraph

/-! ## Connected 2-regular graphs are cycles -/

section TwoRegular

variable {H : CGraph}

/-- The neighbour of `v` other than `u`; junk (namely `u`) when there is no other neighbour. -/
private noncomputable def othNbr (u v : H.V) : H.V :=
  if h : ((H.toSimple.neighborFinset v).erase u).Nonempty then h.choose else u

private theorem card_erase_nbrs (hreg : H.IsRegularWith 2) {u v : H.V}
    (h : H.toSimple.Adj v u) : ((H.toSimple.neighborFinset v).erase u).card = 1 := by
  have hmem : u ∈ H.toSimple.neighborFinset v := by simpa using h
  have hd : (H.toSimple.neighborFinset v).card = 2 := hreg v
  rw [Finset.card_erase_of_mem hmem, hd]

private theorem othNbr_mem (hreg : H.IsRegularWith 2) {u v : H.V} (h : H.toSimple.Adj v u) :
    othNbr u v ∈ (H.toSimple.neighborFinset v).erase u := by
  have hpos : ((H.toSimple.neighborFinset v).erase u).Nonempty := by
    rw [← Finset.card_pos, card_erase_nbrs hreg h]; omega
  rw [othNbr, dif_pos hpos]
  exact hpos.choose_spec

private theorem adj_othNbr (hreg : H.IsRegularWith 2) {u v : H.V} (h : H.toSimple.Adj v u) :
    H.toSimple.Adj v (othNbr u v) := by
  simpa using (Finset.mem_erase.1 (othNbr_mem hreg h)).2

private theorem othNbr_ne (hreg : H.IsRegularWith 2) {u v : H.V} (h : H.toSimple.Adj v u) :
    othNbr u v ≠ u := (Finset.mem_erase.1 (othNbr_mem hreg h)).1

private theorem eq_othNbr (hreg : H.IsRegularWith 2) {u v x : H.V} (h : H.toSimple.Adj v u)
    (hx : H.toSimple.Adj v x) (hxu : x ≠ u) : x = othNbr u v := by
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 (card_erase_nbrs hreg h)
  have h1 : x ∈ (H.toSimple.neighborFinset v).erase u :=
    Finset.mem_erase.2 ⟨hxu, by simpa using hx⟩
  have h2 := othNbr_mem hreg h
  rw [hy, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

private theorem othNbr_othNbr (hreg : H.IsRegularWith 2) {u v : H.V} (h : H.toSimple.Adj v u) :
    othNbr (othNbr u v) v = u :=
  (eq_othNbr hreg (adj_othNbr hreg h) h (othNbr_ne hreg h).symm).symm

/-! ### The walk that follows the two-regular graph around -/

private noncomputable def arcStep (p : H.V × H.V) : H.V × H.V := (p.2, othNbr p.1 p.2)

private noncomputable def arcWalk (a : H.V × H.V) (k : ℕ) : H.V × H.V := arcStep^[k] a

private noncomputable def cyc (a : H.V × H.V) (k : ℕ) : H.V := (arcWalk a k).1

variable {a : H.V × H.V}

private theorem arcWalk_succ (a : H.V × H.V) (k : ℕ) :
    arcWalk a (k + 1) = arcStep (arcWalk a k) := Function.iterate_succ_apply' _ _ _

private theorem arcWalk_snd (a : H.V × H.V) (k : ℕ) : (arcWalk a k).2 = cyc a (k + 1) := by
  show (arcWalk a k).2 = (arcWalk a (k + 1)).1
  rw [arcWalk_succ]
  rfl

private theorem adj_cyc (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ) :
    H.toSimple.Adj (cyc a k) (cyc a (k + 1)) := by
  have key : ∀ k, H.toSimple.Adj (arcWalk a k).1 (arcWalk a k).2 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => rw [arcWalk_succ]; exact adj_othNbr hreg ih.symm
  have h := key k
  rwa [arcWalk_snd] at h

private theorem cyc_succ_succ (a : H.V × H.V) (k : ℕ) :
    cyc a (k + 2) = othNbr (cyc a k) (cyc a (k + 1)) := by
  have h1 : cyc a (k + 2) = (arcWalk a (k + 1)).2 := (arcWalk_snd a (k + 1)).symm
  rw [h1, arcWalk_succ a k]
  show othNbr (arcWalk a k).1 (arcWalk a k).2 = othNbr (cyc a k) (cyc a (k + 1))
  rw [arcWalk_snd]
  rfl

private theorem cyc_ne (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ) :
    cyc a (k + 2) ≠ cyc a k := by
  rw [cyc_succ_succ]
  exact othNbr_ne hreg (adj_cyc hreg h0 k).symm

private theorem cyc_prev (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ) :
    cyc a k = othNbr (cyc a (k + 2)) (cyc a (k + 1)) := by
  rw [cyc_succ_succ, othNbr_othNbr hreg (adj_cyc hreg h0 k).symm]

private theorem eq_cyc_succ_succ (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ)
    {x : H.V} (hx : H.toSimple.Adj (cyc a (k + 1)) x) (hne : x ≠ cyc a k) :
    x = cyc a (k + 2) := by
  rw [cyc_succ_succ]
  exact eq_othNbr hreg (adj_cyc hreg h0 k).symm hx hne

private theorem eq_cyc_of_adj (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ)
    {x : H.V} (hx : H.toSimple.Adj (cyc a (k + 1)) x) (hne : x ≠ cyc a (k + 2)) :
    x = cyc a k := by
  rw [cyc_prev hreg h0 k]
  exact eq_othNbr hreg (adj_cyc hreg h0 (k + 1)) hx hne

private theorem cyc_nbr (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) (k : ℕ)
    {x : H.V} (hx : H.toSimple.Adj (cyc a (k + 1)) x) : x = cyc a k ∨ x = cyc a (k + 2) := by
  by_cases h : x = cyc a k
  · exact Or.inl h
  · exact Or.inr (eq_cyc_succ_succ hreg h0 k hx h)

/-! ### Periodicity -/

private theorem arcWalk_inj_step (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2)
    {i j : ℕ} (h : arcWalk a (i + 1) = arcWalk a (j + 1)) : arcWalk a i = arcWalk a j := by
  have h1 : cyc a (i + 1) = cyc a (j + 1) := congrArg Prod.fst h
  have h2 : cyc a (i + 2) = cyc a (j + 2) := by
    have h3 := congrArg Prod.snd h
    rwa [arcWalk_snd, arcWalk_snd] at h3
  have h4 : cyc a i = cyc a j := by
    rw [cyc_prev hreg h0 i, cyc_prev hreg h0 j, h1, h2]
  exact Prod.ext h4 (by rw [arcWalk_snd, arcWalk_snd, h1])

private theorem arcWalk_shift (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) :
    ∀ i d, arcWalk a (i + d) = arcWalk a i → arcWalk a d = arcWalk a 0 := by
  intro i
  induction i with
  | zero => intro d h; simpa using h
  | succ i ih =>
    intro d h
    refine ih d (arcWalk_inj_step hreg h0 ?_)
    rw [show i + d + 1 = i + 1 + d from by omega]
    exact h

private theorem exists_period (hreg : H.IsRegularWith 2) (h0 : H.toSimple.Adj a.1 a.2) :
    ∃ p, 0 < p ∧ arcWalk a p = arcWalk a 0 := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (arcWalk a)
  rcases Nat.lt_or_ge i j with h | h
  · exact ⟨j - i, by omega, arcWalk_shift hreg h0 i (j - i)
      (by rw [show i + (j - i) = j from by omega]; exact heq.symm)⟩
  · exact ⟨i - j, by omega, arcWalk_shift hreg h0 j (i - j)
      (by rw [show j + (i - j) = i from by omega]; exact heq)⟩

/-! ### The classification -/

/-- **A connected 2-regular graph is a cycle.** -/
theorem nonempty_iso_cycle_of_isRegularWith_two {H : CGraph} {N : ℕ}
    (hreg : H.IsRegularWith 2) (hconn : H.IsConnected) (hcard : Fintype.card H.V = N) :
    Nonempty (H ≃cg cycle N) := by
  classical
  obtain ⟨v₀⟩ := hconn.nonempty
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, H.toSimple.Adj v₀ v₁ := by
    have hd : (H.toSimple.neighborFinset v₀).card = 2 := hreg v₀
    have hne : (H.toSimple.neighborFinset v₀).Nonempty := by
      rw [← Finset.card_pos, hd]; omega
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simpa using hx⟩
  set a : H.V × H.V := (v₀, v₁) with ha
  have h0 : H.toSimple.Adj a.1 a.2 := hv₁
  have hex : ∃ p, 0 < p ∧ arcWalk a p = arcWalk a 0 := exists_period hreg h0
  obtain ⟨p, hp0, hpw, hmin⟩ :
      ∃ p, 0 < p ∧ arcWalk a p = arcWalk a 0 ∧
        ∀ q, q < p → ¬(0 < q ∧ arcWalk a q = arcWalk a 0) :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun q hq ↦ Nat.find_min hex hq⟩
  -- the walk is periodic with period `p`
  have hper : ∀ k, arcWalk a (k + p) = arcWalk a k := by
    intro k
    induction k with
    | zero => simpa using hpw
    | succ k ih =>
      rw [show k + 1 + p = k + p + 1 from by omega, arcWalk_succ, ih, ← arcWalk_succ]
  have hcycper : ∀ k, cyc a (k + p) = cyc a k := fun k ↦ congrArg Prod.fst (hper k)
  have hmodw : ∀ m, arcWalk a m = arcWalk a (m % p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m p with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have hm : m - p < m := by omega
        have h1 : arcWalk a m = arcWalk a (m - p) := by
          conv_lhs => rw [show m = m - p + p from by omega]
          exact hper (m - p)
        rw [h1, ih (m - p) hm, ← Nat.mod_eq_sub_mod h]
  have hmod : ∀ m, cyc a m = cyc a (m % p) := fun m ↦ congrArg Prod.fst (hmodw m)
  -- the arcs `arcWalk a 0, …, arcWalk a (p-1)` are distinct
  have hinjw : ∀ i j, i < p → j < p → arcWalk a i = arcWalk a j → i = j := by
    intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact hmin (j - i) (by omega) ⟨by omega, arcWalk_shift hreg h0 i (j - i)
        (by rw [show i + (j - i) = j from by omega]; exact hij.symm)⟩
    · exact hmin (i - j) (by omega) ⟨by omega, arcWalk_shift hreg h0 j (i - j)
        (by rw [show j + (i - j) = i from by omega]; exact hij)⟩
  have hp3 : 3 ≤ p := by
    have hne1 : p ≠ 1 := by
      intro h
      have h1 : cyc a 1 = cyc a 0 := by have := hcycper 0; rw [h] at this; simpa using this
      exact (adj_cyc hreg h0 0).ne' h1
    have hne2 : p ≠ 2 := by
      intro h
      have h1 : cyc a 2 = cyc a 0 := by have := hcycper 0; rw [h] at this; simpa using this
      exact cyc_ne hreg h0 0 h1
    omega
  -- the vertices `cyc a 0, …, cyc a (p-1)` are distinct
  have key : ∀ i d, 0 < d → i + d < p → cyc a i = cyc a (i + d) → False := by
    intro i d hd hip hEq
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hbase0 : cyc a (i + 0) = cyc a (i + (e + 1)) := by simpa using hEq
    have hshift : cyc a (i + e + 1) = cyc a i := by
      rw [show i + e + 1 = i + (e + 1) from by omega]; exact hEq.symm
    have hbase1 : cyc a (i + 1) = cyc a (i + e) := by
      refine eq_cyc_of_adj hreg h0 (i + e) ?_ ?_
      · rw [hshift]; exact adj_cyc hreg h0 i
      · intro hcon
        have harc : arcWalk a i = arcWalk a (i + e + 1) := by
          refine Prod.ext hshift.symm ?_
          rw [arcWalk_snd, arcWalk_snd, hcon]
        exact absurd (hinjw i (i + e + 1) (by omega) (by omega) harc) (by omega)
    have hkey : ∀ t u, t + u = e + 1 → cyc a (i + t) = cyc a (i + u) := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        match t with
        | 0 =>
          intro u hu
          rw [show u = e + 1 from by omega]; exact hbase0
        | 1 =>
          intro u hu
          rw [show u = e from by omega]; exact hbase1
        | (t + 2) =>
          intro u hu
          have ih1 : cyc a (i + (t + 1)) = cyc a (i + (u + 1)) := ih (t + 1) (by omega) (u + 1)
            (by omega)
          have ih0 : cyc a (i + t) = cyc a (i + (u + 2)) := ih t (by omega) (u + 2) (by omega)
          calc cyc a (i + (t + 2))
              = othNbr (cyc a (i + t)) (cyc a (i + (t + 1))) := by
                rw [show i + (t + 2) = i + t + 2 from by omega,
                  show i + (t + 1) = i + t + 1 from by omega]
                exact cyc_succ_succ a (i + t)
            _ = othNbr (cyc a (i + (u + 2))) (cyc a (i + (u + 1))) := by rw [ih0, ih1]
            _ = cyc a (i + u) := by
                rw [show i + (u + 2) = i + u + 2 from by omega,
                  show i + (u + 1) = i + u + 1 from by omega]
                exact (cyc_prev hreg h0 (i + u)).symm
    rcases Nat.even_or_odd (e + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm1 : 1 ≤ m := by omega
      refine cyc_ne hreg h0 (i + (m - 1)) ?_
      rw [show i + (m - 1) + 2 = i + (m + 1) from by omega]
      exact hkey (m + 1) (m - 1) (by omega)
    · refine (adj_cyc hreg h0 (i + m)).ne ?_
      rw [show i + m + 1 = i + (m + 1) from by omega]
      exact hkey m (m + 1) (by omega)
  have hinj : ∀ i j, i < p → j < p → cyc a i = cyc a j → i = j := by
    intro i j hi hj h
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact key i (j - i) (by omega) (by omega)
        (by rw [show i + (j - i) = j from by omega]; exact h)
    · exact key j (i - j) (by omega) (by omega)
        (by rw [show j + (i - j) = i from by omega]; exact h.symm)
  -- and they exhaust the graph
  set S : Finset H.V := (Finset.range p).image (cyc a) with hS
  have hmemS : ∀ m, cyc a m ∈ S := by
    intro m
    rw [hS, Finset.mem_image]
    exact ⟨m % p, Finset.mem_range.2 (Nat.mod_lt _ hp0), (hmod m).symm⟩
  have hstepS : ∀ x y : H.V, H.toSimple.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hk1 : cyc a k = cyc a (k + p - 1 + 1) := by
      rw [show k + p - 1 + 1 = k + p from by omega]
      exact (hcycper k).symm
    rw [hk1] at hxy
    rcases cyc_nbr hreg h0 (k + p - 1) hxy with h | h <;> rw [h] <;> exact hmemS _
  have hphi : ∀ u v : H.V, H.Adj u v → (fun w ↦ decide (w ∈ S)) u = (fun w ↦ decide (w ∈ S)) v := by
    intro u v huv
    have huv' : H.toSimple.Adj u v := huv
    simp only [decide_eq_decide]
    exact ⟨hstepS u v huv', hstepS v u huv'.symm⟩
  have huniv : ∀ x : H.V, x ∈ S := by
    intro x
    have h := eq_of_forall_adj hconn hphi (cyc a 0) x
    simp only [decide_eq_decide] at h
    exact h.1 (hmemS 0)
  have hcardS : S.card = p := by
    rw [hS]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hinj i j (Finset.mem_range.1 (Finset.mem_coe.1 hi))
      (Finset.mem_range.1 (Finset.mem_coe.1 hj)) hij
  have hpN : p = N := by
    rw [← hcard, ← hcardS, Finset.eq_univ_iff_forall.2 huniv, Finset.card_univ]
  subst hpN
  -- the neighbours of `cyc a i`, for `i < p`
  have hnbr : ∀ i j, i < p → j < p →
      (H.toSimple.Adj (cyc a i) (cyc a j) ↔ ((i + 1) % p = j ∨ (j + 1) % p = i)) := by
    intro i j hi hj
    constructor
    · intro hadj
      have hk1 : cyc a i = cyc a (i + p - 1 + 1) := by
        rw [show i + p - 1 + 1 = i + p from by omega]; exact (hcycper i).symm
      rw [hk1] at hadj
      rcases cyc_nbr hreg h0 (i + p - 1) hadj with h | h
      · right
        have hjv : j = (i + p - 1) % p := by
          refine hinj j _ hj (Nat.mod_lt _ hp0) ?_
          rw [h, hmod (i + p - 1)]
        rcases Nat.eq_zero_or_pos i with rfl | hi1
        · have : j = p - 1 := by
            rw [hjv, show 0 + p - 1 = p - 1 from by omega]
            exact Nat.mod_eq_of_lt (by omega)
          rw [this, show p - 1 + 1 = p from by omega, Nat.mod_self]
        · have : j = i - 1 := by
            rw [hjv, show i + p - 1 = p + (i - 1) from by omega, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          rw [this, show i - 1 + 1 = i from by omega]
          exact Nat.mod_eq_of_lt hi
      · left
        refine hinj ((i + 1) % p) j (Nat.mod_lt _ hp0) hj ?_
        rw [← hmod (i + 1), h, show i + p - 1 + 2 = i + 1 + p from by omega, hcycper]
    · intro h
      rcases h with h | h
      · have : cyc a j = cyc a (i + 1) := by rw [← h, ← hmod]
        rw [this]; exact adj_cyc hreg h0 i
      · have : cyc a i = cyc a (j + 1) := by rw [← h, ← hmod]
        rw [this]; exact (adj_cyc hreg h0 j).symm
  -- assemble the isomorphism
  have hcardV : Fintype.card (cycle p).V = Fintype.card H.V := by
    rw [hcard, CGraph.fintypeCard, card_cycle]
  refine ⟨(isoOfAdj (H := H) (G := cycle p)
    (equivOfBijective (f := fun i : (cycle p).V ↦ cyc a i.1) ?_) ?_).symm⟩
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, hcardV⟩
    intro i j hij
    exact Fin.ext (hinj i.1 j.1 i.2 j.2 hij)
  · intro x y
    have hx : (x : Fin p).1 < p := x.2
    have hy : (y : Fin p).1 < p := y.2
    rw [Bool.eq_iff_iff, cycle_adj_iff (by omega)]
    simpa using hnbr x.1 y.1 hx hy

/-- A 2-regular graph with a vertex has at least three of them. -/
theorem three_le_card_of_isRegularWith_two (hreg : H.IsRegularWith 2) (v : H.V) :
    3 ≤ Fintype.card H.V := by
  classical
  have hv : v ∉ H.toSimple.neighborFinset v := by simp
  have h1 : (insert v (H.toSimple.neighborFinset v)).card = 3 := by
    have h2 : (H.toSimple.neighborFinset v).card = 2 := hreg v
    rw [Finset.card_insert_of_notMem hv, h2]
  have h2 := Finset.card_le_univ (insert v (H.toSimple.neighborFinset v))
  rw [h1] at h2
  exact h2

/-- **Cycles are determined by their spectrum.**  A graph cospectral with `Cₙ` is regular of
degree `2` and connected, hence a cycle on the same number of vertices. -/
theorem isDS_cycle (n : ℕ) : (cycle (n + 3)).IsDS := by
  intro H h
  have hcard : Fintype.card H.V = n + 3 := by
    rw [H.fintypeCard, ← h.card_eq, card_cycle]
  have hcyc : (cycle (n + 3)).IsRegularWith 2 := degree_cycle n
  have hreg : H.IsRegularWith 2 := h.isRegularWith hcyc
  have hconn : H.IsConnected := h.isConnected hcyc (isConnected_cycle (n + 2))
  exact (nonempty_iso_cycle_of_isRegularWith_two hreg hconn hcard).elim fun e ↦ ⟨e.symm⟩

end TwoRegular

end CGraph

namespace IsoGraph

/-! ## Connected 2-regular graphs -/

/-- **A connected 2-regular graph is a cycle.** -/
theorem eq_cycle_of_isRegularWith_two {G : IsoGraph} (hreg : G.IsRegularWith 2)
    (hconn : G.IsConnected) : G = cycle G.V := by
  induction G using Quotient.inductionOn with
  | _ G =>
    exact (CGraph.nonempty_iso_cycle_of_isRegularWith_two hreg hconn G.fintypeCard).elim
      fun e ↦ Quotient.sound ⟨e⟩

/-- A connected 2-regular graph has at least three vertices. -/
theorem three_le_V_of_isRegularWith_two {G : IsoGraph} (hreg : G.IsRegularWith 2)
    (hconn : G.IsConnected) : 3 ≤ G.V := by
  induction G using Quotient.inductionOn with
  | _ G =>
    have hconn' : G.IsConnected := hconn
    obtain ⟨v⟩ := hconn'.nonempty
    have h := CGraph.three_le_card_of_isRegularWith_two (H := G) hreg v
    rwa [G.fintypeCard] at h

/-- **Cycles are determined by their spectrum.** -/
theorem isDS_cycle (n : ℕ) : IsDS (cycle (n + 3)) := (isDS_mk_iff _).2 (CGraph.isDS_cycle n)

/-- **A connected 2-regular graph is determined by its spectrum**: it is a cycle, and cycles
are.  This is the only nontrivial family for which the library settles the question. -/
theorem isDS_of_isRegularWith_two {G : IsoGraph} (hreg : G.IsRegularWith 2)
    (hconn : G.IsConnected) : G.IsDS := by
  obtain ⟨n, hn⟩ : ∃ n, G.V = n + 3 :=
    ⟨G.V - 3, by have := three_le_V_of_isRegularWith_two hreg hconn; omega⟩
  rw [eq_cycle_of_isRegularWith_two hreg hconn, hn]
  exact isDS_cycle n

/-! ### The members of the named families that are cycles -/

theorem isDS_circulant_one (n : ℕ) : IsDS (circulant (n + 3) [1]) := by
  rw [circulant_one]; exact isDS_cycle n

theorem isDS_tadpole_zero (m : ℕ) : IsDS (tadpole (m + 3) 0) := by
  rw [tadpole_zero]; exact isDS_cycle m

theorem isDS_cyclePendant_replicate_zero (m j : ℕ) :
    IsDS (cyclePendant (m + 3) (List.replicate j 0)) := by
  rw [cyclePendant_replicate_zero]; exact isDS_cycle m

theorem isDS_thetaGraph_pair (a b : ℕ) (h : 1 ≤ a + b) : IsDS (thetaGraph [a, b]) :=
  isDS_of_isRegularWith_two (isRegularWith_thetaGraph_pair a b h) (isConnected_thetaGraph_pair a b)

theorem isDS_ladder_two : IsDS (ladder 2) := by rw [ladder_two]; exact isDS_cycle 1

theorem isDS_prism_two : IsDS (prism 2) := by rw [prism_two]; exact isDS_cycle 1

theorem isDS_crown_three : IsDS (crown 3) := by rw [crown_three]; exact isDS_cycle 3

theorem isDS_cocktailParty_two : IsDS (cocktailParty 2) := by
  rw [cocktailParty_two]; exact isDS_cycle 1

theorem isDS_completeMultipartite_two_two : IsDS (completeMultipartite [2, 2]) :=
  isDS_cocktailParty_two

theorem isDS_bipartite_two_two : IsDS (bipartite 2 2) := by
  rw [bipartite_two_two]; exact isDS_cycle 1

theorem isDS_hypercube_two : IsDS (hypercube 2) := by rw [hypercube_two]; exact isDS_cycle 1

theorem isDS_turan_four_two : IsDS (turan 4 2) := by
  rw [turan_two]; exact isDS_bipartite_two_two

theorem isDS_paley_five : IsDS (paley 5) := by rw [paley_five]; exact isDS_cycle 2

end IsoGraph
