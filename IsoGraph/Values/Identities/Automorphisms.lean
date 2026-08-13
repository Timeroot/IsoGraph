import IsoGraph.Values.Identities.Extremal
import IsoGraph.ForMathlib.SimpleGraph

/-!
# Automorphism counts, regularity, and matchings

How many automorphisms the families have.  The complete bipartite graphs, the cycles and the
wheels are done by hand, by writing the automorphism group as a product of symmetric groups and
counting; the constructions inherit theirs from their factors.  The handshaking lemma is proved
here because the automorphism counts of the regular families need it.

The rest is regularity and what follows from it: degrees in the line graph, matchings and their
relation to independent sets and covers, and the first edge colourings written out by hand — the
ladder, the crown and the prism.
-/

set_option autoImplicit false

namespace CGraph

variable {G H : CGraph}

/-! ### The automorphism count of a cycle

The star was fixed by pinning down one vertex; a cycle is pinned down by pinning down an *arc*.
Every vertex of `Cₙ` has exactly two neighbours, so once an automorphism is known on two adjacent
vertices it is forced everywhere: walking around the rim, the next vertex is the unique neighbour
of the current one other than the previous.  That makes the pair `(f 0, which neighbour of f 0 is
f 1)` a faithful record of `f`, of which there are only `2n`, and arc-transitivity supplies the
matching lower bound.
-/

private theorem cyc_mod_succ (N j : ℕ) (hj : j < N) :
    (j + 1) % N = if j + 1 = N then 0 else j + 1 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with h | h
  · rw [if_pos (by omega), show j + 1 = N from by omega, Nat.mod_self]
  · rw [if_neg (by omega), Nat.mod_eq_of_lt h]

private theorem cyc_mod_pred (N i : ℕ) (hi : i < N) :
    (i + N - 1) % N = if i = 0 then N - 1 else i - 1 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [if_pos rfl, show 0 + N - 1 = N - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg (by omega), show i + N - 1 = N + (i - 1) from by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]

/-- The two neighbours of `i` in a cycle of length at least three, named by their labels. -/
theorem cycle_adj_eq_iff {N : ℕ} (hN : 3 ≤ N) (i j : (cycle N).V) :
    (cycle N).Adj i j = true ↔ (j.1 = (i.1 + 1) % N ∨ j.1 = (i.1 + N - 1) % N) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [cycle_adj_val N i j, cyc_mod_succ N i.1 hi, cyc_mod_succ N j.1 hj, cyc_mod_pred N i.1 hi]
  split_ifs <;> omega

/-- Those two neighbours really are distinct once the cycle has length at least three. -/
theorem cycle_nbrs_ne {N : ℕ} (hN : 3 ≤ N) (i : (cycle N).V) :
    (i.1 + 1) % N ≠ (i.1 + N - 1) % N := by
  have hi := i.isLt
  rw [cyc_mod_succ N i.1 hi, cyc_mod_pred N i.1 hi]
  split_ifs <;> omega

/-- Consecutive labels are adjacent, no wraparound involved. -/
theorem cycle_adj_of_succ {N : ℕ} {u v : (cycle N).V} (h : u.1 + 1 = v.1) :
    (cycle N).Adj u v = true := by
  rw [cycle_adj_val]
  exact ⟨by omega, Or.inl (by rw [h]; exact Nat.mod_eq_of_lt v.isLt)⟩

/-- **A vertex of a cycle has at most two neighbours**: of three neighbours of `y`, if `v` and `w`
both differ from `u` then they are equal. -/
theorem cycle_nbr_unique {N : ℕ} (hN : 3 ≤ N) {y u v w : (cycle N).V}
    (hu : (cycle N).Adj y u = true) (hv : (cycle N).Adj y v = true)
    (hw : (cycle N).Adj y w = true) (huv : u ≠ v) (huw : u ≠ w) : v = w := by
  rw [cycle_adj_eq_iff hN] at hu hv hw
  have hne := cycle_nbrs_ne hN y
  have huv' : u.1 ≠ v.1 := fun h ↦ huv (Fin.ext h)
  have huw' : u.1 ≠ w.1 := fun h ↦ huw (Fin.ext h)
  refine Fin.ext ?_
  generalize (y.1 + 1) % N = p at hu hv hw hne
  generalize (y.1 + N - 1) % N = q at hu hv hw hne
  omega

/-- **An automorphism of a cycle is pinned down by where it sends two adjacent vertices.**  Walk
around the cycle: each next vertex is the unique neighbour of the current one other than the
previous, so agreement propagates from the first step to every vertex. -/
theorem cycle_aut_eq {N : ℕ} (hN : 3 ≤ N) {f g : cycle N ≃cg cycle N}
    (h0 : f ⟨0, by omega⟩ = g ⟨0, by omega⟩) (h1 : f ⟨1, by omega⟩ = g ⟨1, by omega⟩) :
    f = g := by
  have key : ∀ k, ∀ hk : k < N, f ⟨k, hk⟩ = g ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      match k, ih with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | (m + 2), ih =>
        have hm : m < N := by omega
        have hm1 : m + 1 < N := by omega
        have hfa : f ⟨m, hm⟩ = g ⟨m, hm⟩ := ih m (by omega) hm
        have hfb : f ⟨m + 1, hm1⟩ = g ⟨m + 1, hm1⟩ := ih (m + 1) (by omega) hm1
        have hba : (cycle N).Adj ⟨m + 1, hm1⟩ ⟨m, hm⟩ = true := by
          rw [(cycle N).symm]
          exact cycle_adj_of_succ rfl
        have hbc : (cycle N).Adj ⟨m + 1, hm1⟩ ⟨m + 2, hk⟩ = true := cycle_adj_of_succ rfl
        have hac : f ⟨m, hm⟩ ≠ f ⟨m + 2, hk⟩ := fun h ↦ by
          have h2 : (⟨m, hm⟩ : Fin N) = ⟨m + 2, hk⟩ := f.injective h
          simp only [Fin.mk.injEq] at h2
          omega
        refine cycle_nbr_unique hN (y := f ⟨m + 1, hm1⟩) (u := f ⟨m, hm⟩) ?_ ?_ ?_ hac ?_
        · rw [f.adj_eq]; exact hba
        · rw [f.adj_eq]; exact hbc
        · rw [hfb, g.adj_eq]; exact hbc
        · rw [hfa]
          refine fun h ↦ ?_
          have h2 : (⟨m, hm⟩ : Fin N) = ⟨m + 2, hk⟩ := g.injective h
          simp only [Fin.mk.injEq] at h2
          omega
  refine RelIso.ext fun x ↦ ?_
  obtain ⟨v, hv⟩ := x
  exact key v hv

/-- **A cycle has at most `2n` automorphisms.**  An automorphism is determined by the image of
`0` and the image of `1`, and the latter is one of the two neighbours of the former, so the pair
`(f 0, which neighbour)` is a complete and faithful record of `f`. -/
theorem autCount_cycle_le {N : ℕ} (hN : 3 ≤ N) : (cycle N).autCount ≤ 2 * N := by
  have h0N : 0 < N := by omega
  have h1N : 1 < N := by omega
  set code : (cycle N ≃cg cycle N) → (cycle N).V × Bool := fun f ↦
    (f ⟨0, h0N⟩, decide ((f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + 1) % N)) with hcode
  have hadj01 : (cycle N).Adj ⟨0, h0N⟩ ⟨1, h1N⟩ = true := cycle_adj_of_succ rfl
  have hnbr : ∀ f : cycle N ≃cg cycle N,
      (f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + 1) % N ∨
        (f ⟨1, h1N⟩).1 = ((f ⟨0, h0N⟩).1 + N - 1) % N := by
    intro f
    rw [← cycle_adj_eq_iff hN, f.adj_eq]
    exact hadj01
  have hinj : Function.Injective code := by
    intro f g h
    rw [hcode] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨he0, heb⟩ := h
    refine cycle_aut_eq hN he0 ?_
    refine Fin.ext ?_
    have hf := hnbr f
    have hg := hnbr g
    rw [he0] at hf
    rw [he0, decide_eq_decide] at heb
    have hne := cycle_nbrs_ne hN (g ⟨0, h0N⟩)
    generalize ((g ⟨0, h0N⟩).1 + 1) % N = p at hf hg heb hne
    generalize ((g ⟨0, h0N⟩).1 + N - 1) % N = q at hf hg hne
    omega
  have hcard : Nat.card ((cycle N).V × Bool) = 2 * N := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, card_cycle, Fintype.card_bool]
    omega
  have := Nat.card_le_card_of_injective code hinj
  rw [hcard] at this
  exact this

/-- The automorphism count is `1` exactly for an asymmetric graph. -/
theorem autCount_eq_one_iff (G : CGraph) :
    G.autCount = 1 ↔ ∀ a : G.toSimple ≃g G.toSimple, a = RelIso.refl _ := by
  rw [autCount, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, -⟩ a
    exact hsub.elim a _
  · intro h
    exact ⟨⟨fun a b ↦ (h a).trans (h b).symm⟩, ⟨RelIso.refl _⟩⟩

/-! ### Automorphisms versus degrees and symmetry -/

/-- Automorphisms preserve degrees, so a graph whose vertices all have distinct degrees is
asymmetric. -/
theorem autCount_eq_one_of_degree_injective (G : CGraph)
    (h : Function.Injective fun v : G.V ↦ G.toSimple.degree v) : G.autCount = 1 := by
  rw [autCount_eq_one_iff]
  intro a
  ext v
  exact h (SimpleGraph.Iso.degree_eq a v)

/-- A vertex-transitive graph has at least `|V|` automorphisms: the automorphisms carrying a fixed
base vertex to each vertex in turn are already pairwise distinct. -/
theorem card_le_autCount_of_isVertexTransitive (G : CGraph) [Nonempty G.V]
    (h : G.IsVertexTransitive) : Fintype.card G.V ≤ G.autCount := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  choose f hf using h v₀
  haveI : Finite (G ≃cg G) := G.instFiniteAut
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (f u) v₀ = (f v) v₀ := by rw [huv]
    rw [hf u, hf v] at h1
    exact h1
  calc Fintype.card G.V = Nat.card G.V := Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (G ≃cg G) := Nat.card_le_card_of_injective f hinj
    _ = G.autCount := rfl

/-- An arc-transitive graph has at least `2|E|` automorphisms, one for each arc. -/
@[toIsoGraph]
theorem two_mul_E_le_autCount_of_isArcTransitive (G : CGraph) (h : G.IsArcTransitive) :
    2 * G.E ≤ G.autCount := by
  classical
  rcases Nat.eq_zero_or_pos G.E with hE | hE
  · simp [hE]
  obtain ⟨u₀, v₀, h₀⟩ := exists_adj_of_E_pos hE
  haveI : Finite (G ≃cg G) := G.instFiniteAut
  choose f hf1 hf2 using fun d : G.toSimple.Dart ↦
    h u₀ v₀ d.toProd.1 d.toProd.2 h₀ d.adj
  have hinj : Function.Injective f := by
    intro d e hde
    apply SimpleGraph.Dart.ext
    have h1 : (f d) u₀ = (f e) u₀ := by rw [hde]
    have h2 : (f d) v₀ = (f e) v₀ := by rw [hde]
    rw [hf1 d, hf1 e] at h1
    rw [hf2 d, hf2 e] at h2
    exact Prod.ext h1 h2
  calc 2 * G.E = Fintype.card G.toSimple.Dart :=
        (SimpleGraph.dart_card_eq_twice_card_edges _).symm
    _ = Nat.card G.toSimple.Dart := Fintype.card_eq_nat_card
    _ ≤ Nat.card (G ≃cg G) := Nat.card_le_card_of_injective f hinj
    _ = G.autCount := rfl

/-- Too few automorphisms to move a base vertex everywhere. -/
@[toIsoGraph]
theorem not_isVertexTransitive_of_autCount_lt (G : CGraph) [Nonempty G.V]
    (h : G.autCount < Fintype.card G.V) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.card_le_autCount_of_isVertexTransitive hvt) (by omega)

/-- Too few automorphisms to move a base arc everywhere. -/
@[toIsoGraph]
theorem not_isArcTransitive_of_autCount_lt (G : CGraph) (h : G.autCount < 2 * G.E) :
    ¬ G.IsArcTransitive := fun hat ↦
  absurd (G.two_mul_E_le_autCount_of_isArcTransitive hat) (by omega)

/-- **The cycle `Cₙ` has exactly `2n` automorphisms** for `n ≥ 3`: its automorphism group is the
dihedral group of order `2n`.  The lower bound is arc-transitivity together with the edge count,
and the upper bound is `autCount_cycle_le`. -/
@[toIsoGraph]
theorem autCount_cycle (n : ℕ) : (cycle (n + 3)).autCount = 2 * (n + 3) := by
  have hle := autCount_cycle_le (N := n + 3) (by omega)
  have hge := two_mul_E_le_autCount_of_isArcTransitive _ (isArcTransitive_cycle (n + 3))
  rw [E_cycle] at hge
  omega

/-! ### The automorphism count of a wheel

A wheel is a cone over a cycle, and once the rim is long enough the hub is recognisable: it is the
only vertex adjacent to every other one, since a rim vertex misses the rim vertex two steps along.
Every automorphism therefore fixes the hub and permutes the rim, and what it does to the rim is an
automorphism of the cycle.  That restriction map is injective, so the wheel has no more symmetry
than its rim, and the join bound `le_autCount_wheel` says it has no less.
-/

private theorem cyc_mod_two (N i : ℕ) (hN : 2 ≤ N) (hi : i < N) :
    (i + 2) % N = if i + 2 = N then 0 else if i + 2 = N + 1 then 1 else i + 2 := by
  rcases lt_trichotomy (i + 2) N with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), Nat.mod_eq_of_lt h]
  · rw [if_pos h, ← h, Nat.mod_self]
  · have h1 : i + 2 = N + 1 := by omega
    rw [if_neg (by omega), if_pos h1, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem wheel_adj_inr_inr {N : ℕ} (u v : (cycle N).V) :
    (wheel N).Adj (Sum.inr u) (Sum.inr v) = (cycle N).Adj u v := by
  simp [wheel]

theorem wheel_adj_inl_inr {N : ℕ} (a : (complete 1).V) (v : (cycle N).V) :
    (wheel N).Adj (Sum.inl a) (Sum.inr v) = true := by
  simp [wheel]

/-- The hub of a wheel is unique: `complete 1` has just one vertex.  Stated as a plain equation
rather than obtained from a `Subsingleton` instance because typeclass search does not unfold
`(complete 1).V`. -/
theorem complete_one_elim {a b : (complete 1).V} : a = b := Subsingleton.elim (α := Fin 1) a b

/-- In a cycle of length at least four, every vertex misses some other vertex: the vertex two
steps along is neither the vertex itself nor one of its two neighbours. -/
theorem exists_cycle_non_adj {N : ℕ} (hN : 4 ≤ N) (b : (cycle N).V) :
    ∃ c : (cycle N).V, c ≠ b ∧ (cycle N).Adj b c = false := by
  have hb := b.isLt
  have hlt : (b.1 + 2) % N < N := Nat.mod_lt _ (by omega)
  have key : (b.1 + 2) % N ≠ b.1 ∧ (b.1 + 2) % N ≠ (b.1 + 1) % N ∧
      (b.1 + 2) % N ≠ (b.1 + N - 1) % N := by
    rw [cyc_mod_two N b.1 (by omega) hb, cyc_mod_succ N b.1 hb, cyc_mod_pred N b.1 hb]
    refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  refine ⟨⟨(b.1 + 2) % N, hlt⟩, Fin.ne_of_val_ne key.1, ?_⟩
  rw [Bool.eq_false_iff, ne_eq, cycle_adj_eq_iff (by omega)]
  rintro (h | h)
  · exact key.2.1 h
  · exact key.2.2 h

/-- The hub is the only vertex of a wheel adjacent to every other one, once the rim has length at
least four. -/
theorem eq_inl_of_adj_all {N : ℕ} (hN : 4 ≤ N) {x : (wheel N).V}
    (hx : ∀ y : (wheel N).V, y ≠ x → (wheel N).Adj x y = true) :
    ∃ a : (complete 1).V, x = Sum.inl a := by
  rcases x with a | b
  · exact ⟨a, rfl⟩
  · obtain ⟨c, hcb, hadj⟩ := exists_cycle_non_adj hN b
    have h := hx (Sum.inr c) fun hi ↦ hcb (Sum.inr.inj hi)
    rw [wheel_adj_inr_inr, hadj] at h
    exact absurd h (by simp)

/-- **Every automorphism of a wheel fixes the hub** once the rim has length at least four. -/
theorem wheel_hub {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (a : (complete 1).V) :
    f (Sum.inl a) = Sum.inl a := by
  have hall : ∀ y : (wheel N).V, y ≠ f (Sum.inl a) → (wheel N).Adj (f (Sum.inl a)) y = true := by
    intro y hy
    obtain ⟨z, rfl⟩ : ∃ z, f z = y := ⟨f.symm y, f.apply_symm_apply y⟩
    rw [f.adj_eq]
    rcases z with a' | c
    · exact absurd (complete_one_elim (a := a') (b := a)) fun h ↦ hy (by rw [h])
    · exact wheel_adj_inl_inr a c
  obtain ⟨a', ha'⟩ := eq_inl_of_adj_all hN hall
  rw [ha', complete_one_elim (a := a') (b := a)]

/-- The rim component of the image of a rim vertex.  The fallback branch is never taken. -/
def wheelRim {N : ℕ} (f : wheel N ≃cg wheel N) (b : (cycle N).V) : (cycle N).V :=
  Sum.elim (fun _ : (complete 1).V ↦ b) (id : (cycle N).V → (cycle N).V) (f (Sum.inr b))

theorem wheel_rim_exists {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b : (cycle N).V) :
    ∃ c, f (Sum.inr b) = Sum.inr c := by
  rcases hb : f (Sum.inr b) with a | c
  · exact absurd (f.injective (hb.trans (wheel_hub hN f a).symm)) (by simp)
  · exact ⟨c, rfl⟩

theorem wheelRim_spec {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b : (cycle N).V) :
    f (Sum.inr b) = Sum.inr (wheelRim f b) := by
  obtain ⟨c, hc⟩ := wheel_rim_exists hN f b
  simp only [wheelRim, hc, Sum.elim_inr, id_eq]

theorem wheelRim_injective {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) :
    Function.Injective (wheelRim f) := by
  intro b c h
  have hbc : f (Sum.inr b) = f (Sum.inr c) := by
    rw [wheelRim_spec hN, wheelRim_spec hN, h]
  exact Sum.inr.inj (f.injective hbc)

theorem wheelRim_adj {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b c : (cycle N).V) :
    (cycle N).Adj (wheelRim f b) (wheelRim f c) = (cycle N).Adj b c := by
  have h1 : (wheel N).Adj (f (Sum.inr b)) (f (Sum.inr c))
      = (wheel N).Adj (Sum.inr b) (Sum.inr c) := f.adj_eq _ _
  rw [wheelRim_spec hN, wheelRim_spec hN, wheel_adj_inr_inr, wheel_adj_inr_inr] at h1
  exact h1

/-- **Restricting an automorphism of a wheel to its rim** gives an automorphism of the cycle. -/
noncomputable def wheelToCycle {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) :
    cycle N ≃cg cycle N :=
  autoOfPerm (G := cycle N)
    (Equiv.ofBijective (wheelRim f) (Finite.injective_iff_bijective.1 (wheelRim_injective hN f)))
    fun x y ↦ wheelRim_adj hN f x y

theorem wheelToCycle_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (wheelToCycle hN) := by
  intro f g h
  refine RelIso.ext fun x ↦ ?_
  rcases x with a | b
  · rw [wheel_hub hN f a, wheel_hub hN g a]
  · have hb : wheelRim f b = wheelRim g b :=
      congrArg (fun e : cycle N ≃cg cycle N ↦ e b) h
    rw [wheelRim_spec hN f b, wheelRim_spec hN g b, hb]

/-- **A wheel has at most `2n` automorphisms** once its rim has length at least four: the hub is
fixed, and what is left is an automorphism of the rim. -/
theorem autCount_wheel_le {N : ℕ} (hN : 4 ≤ N) : (wheel N).autCount ≤ 2 * N := by
  haveI : Finite (cycle N ≃cg cycle N) := (cycle N).instFiniteAut
  have h := Nat.card_le_card_of_injective (wheelToCycle hN) (wheelToCycle_injective hN)
  have h2 : (wheel N).autCount ≤ (cycle N).autCount := h
  exact h2.trans (autCount_cycle_le (by omega))

/-! ### The handshaking lemma -/

/-- **Handshaking lemma.**  A graph has evenly many vertices of odd degree. -/
theorem even_card_odd_degree (G : CGraph) :
    Even (Finset.univ.filter fun v : G.V ↦ Odd (G.toSimple.degree v)).card :=
  SimpleGraph.even_card_odd_degree_vertices G.toSimple

/-- The handshaking lemma, read off the degree multiset. -/
@[toIsoGraph]
theorem even_countP_odd_degMultiset (G : CGraph) :
    Even (G.degMultiset.countP fun d ↦ Odd d) := by
  have h : (G.degMultiset.countP fun d ↦ Odd d)
      = (Finset.univ.filter fun v : G.V ↦ Odd (G.toSimple.degree v)).card := by
    rw [degMultiset, Multiset.countP_map]
    rfl
  rw [h]
  exact G.even_card_odd_degree

/-- The handshaking lemma, read off the degree sequence. -/
@[toIsoGraph]
theorem even_countP_odd_degSequence (G : CGraph) :
    Even (G.degSequence.countP fun d ↦ decide (Odd d)) := by
  rw [degSequence, ← Multiset.coe_countP, Multiset.sort_eq]
  exact G.even_countP_odd_degMultiset

/-- If some vertex has odd degree then so does another one. -/
theorem exists_ne_odd_degree (G : CGraph) {v : G.V} (h : Odd (G.toSimple.degree v)) :
    ∃ w, w ≠ v ∧ Odd (G.toSimple.degree w) :=
  SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree G.toSimple v h

/-- A graph all of whose degrees are odd has evenly many vertices. -/
theorem even_card_of_forall_odd_degree (G : CGraph) (h : ∀ v, Odd (G.toSimple.degree v)) :
    Even (Fintype.card G.V) := by
  have hc := G.even_card_odd_degree
  rwa [Finset.filter_true_of_mem fun v _ ↦ h v, Finset.card_univ] at hc

/-- **An odd-regular graph has evenly many vertices.**  There is no cubic graph on five
vertices. -/
theorem even_card_of_isRegularOfDegree_odd (G : CGraph) {k : ℕ} (hk : Odd k)
    (h : G.toSimple.IsRegularOfDegree k) : Even (Fintype.card G.V) :=
  G.even_card_of_forall_odd_degree fun v ↦ by rw [h v]; exact hk

/-- On an odd number of vertices, some vertex has even degree. -/
theorem exists_even_degree_of_odd_card (G : CGraph) (h : Odd (Fintype.card G.V)) :
    ∃ v, Even (G.toSimple.degree v) := by
  by_contra hc
  push_neg at hc
  exact Nat.not_even_iff_odd.2 h
    (G.even_card_of_forall_odd_degree fun v ↦ Nat.not_even_iff_odd.1 (hc v))

/-! ### Automorphisms of the constructions

An automorphism of each factor gives an automorphism of a disjoint union, a join, or any of the
four products, and different pairs give different automorphisms.  So the automorphism count of a
construction is at least the product of the counts of its factors. -/

/-- The counting step shared by all the constructions below: an injective way of building an
automorphism of `K` out of one automorphism of `G` and one of `H`. -/
private theorem mul_autCount_le_autCount {K : CGraph}
    (f : (G ≃cg G) → (H ≃cg H) → (K ≃cg K))
    (hf : ∀ a a' b b', f a b = f a' b' → a = a' ∧ b = b') :
    G.autCount * H.autCount ≤ K.autCount := by
  haveI : Finite (K ≃cg K) := K.instFiniteAut
  have hinj : Function.Injective fun p : (G ≃cg G) × (H ≃cg H) ↦ f p.1 p.2 := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := hf a a' b b' h
    rw [h1, h2]
  calc G.autCount * H.autCount = Nat.card ((G ≃cg G) × (H ≃cg H)) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (K ≃cg K) := Nat.card_le_card_of_injective _ hinj
    _ = K.autCount := rfl

/-- An automorphism of each side, acting on the disjoint union. -/
def disjUnionAuto (a : G ≃cg G) (b : H ≃cg H) : disjUnion G H ≃cg disjUnion G H :=
  autoOfPerm (G := disjUnion G H) (Equiv.sumCongr a.toEquiv b.toEquiv) (by
    rintro (x | x) (y | y)
    · exact a.adj_eq x y
    · rfl
    · rfl
    · exact b.adj_eq x y)

@[simp] theorem disjUnionAuto_inl (a : G ≃cg G) (b : H ≃cg H) (x : G.V) :
    disjUnionAuto a b (.inl x) = .inl (a x) := rfl

@[simp] theorem disjUnionAuto_inr (a : G ≃cg G) (b : H ≃cg H) (y : H.V) :
    disjUnionAuto a b (.inr y) = .inr (b y) := rfl

@[toIsoGraph]
theorem autCount_mul_le_autCount_disjUnion (G H : CGraph) :
    G.autCount * H.autCount ≤ (disjUnion G H).autCount :=
  mul_autCount_le_autCount disjUnionAuto fun a a' b b' h ↦ by
    refine ⟨?_, ?_⟩
    · ext x
      exact Sum.inl_injective
        (congrArg (fun σ : disjUnion G H ≃cg disjUnion G H ↦ σ (.inl x)) h)
    · ext y
      exact Sum.inr_injective
        (congrArg (fun σ : disjUnion G H ≃cg disjUnion G H ↦ σ (.inr y)) h)

@[toIsoGraph]
theorem autCount_mul_le_autCount_join (G H : CGraph) :
    G.autCount * H.autCount ≤ (join G H).autCount := by
  have h := autCount_mul_le_autCount_disjUnion Gᶜ Hᶜ
  rwa [autCount_compl, autCount_compl, ← autCount_compl (disjUnion Gᶜ Hᶜ)] at h

/-- Swapping the two copies of a graph in a disjoint union with itself. -/
def disjUnionSwapAuto (G : CGraph) : disjUnion G G ≃cg disjUnion G G :=
  autoOfPerm (G := disjUnion G G) (Equiv.sumComm G.V G.V) (by
    rintro (x | x) (y | y) <;> rfl)

@[simp] theorem disjUnionSwapAuto_inl (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inl x) = .inr x := rfl

@[simp] theorem disjUnionSwapAuto_inr (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inr x) = .inl x := rfl

/-- Two copies of the same graph can also be exchanged, which doubles the bound. -/
@[toIsoGraph]
theorem two_mul_autCount_mul_le_autCount_disjUnion_self (G : CGraph) [Nonempty G.V] :
    2 * (G.autCount * G.autCount) ≤ (disjUnion G G).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  haveI : Finite (disjUnion G G ≃cg disjUnion G G) := (disjUnion G G).instFiniteAut
  set f : Bool × (G ≃cg G) × (G ≃cg G) → (disjUnion G G ≃cg disjUnion G G) :=
    fun p ↦ if p.1 then (disjUnionAuto p.2.1 p.2.2).trans (disjUnionSwapAuto G)
      else disjUnionAuto p.2.1 p.2.2 with hfdef
  -- The two copies are told apart by which side `inl x₀` lands in, and each factor is read back
  -- off by forgetting the side.
  have hside : ∀ (c : Bool) (a b : G ≃cg G), (f (c, a, b) (Sum.inl x₀)).isRight = c := by
    rintro (_ | _) a b <;> simp [hfdef]
  have hfst : ∀ (c : Bool) (a b : G ≃cg G) (x : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inl x)) = a x := by
    rintro (_ | _) a b x <;> simp [hfdef]
  have hsnd : ∀ (c : Bool) (a b : G ≃cg G) (y : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inr y)) = b y := by
    rintro (_ | _) a b y <;> simp [hfdef]
  have hinj : Function.Injective f := by
    rintro ⟨c, a, b⟩ ⟨c', a', b'⟩ h
    have hc : c = c' := by rw [← hside c a b, ← hside c' a' b', h]
    subst hc
    have ha : a = a' := by
      ext x
      rw [← hfst c a b x, ← hfst c a' b' x, h]
    have hb : b = b' := by
      ext y
      rw [← hsnd c a b y, ← hsnd c a' b' y, h]
    rw [ha, hb]
  calc 2 * (G.autCount * G.autCount) = Nat.card (Bool × (G ≃cg G) × (G ≃cg G)) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
        rfl
    _ ≤ Nat.card (disjUnion G G ≃cg disjUnion G G) := Nat.card_le_card_of_injective f hinj
    _ = (disjUnion G G).autCount := rfl

/-- An automorphism of each factor, acting coordinatewise on the Cartesian product. -/
def cartesianProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    cartesianProduct G H ≃cg cartesianProduct G H :=
  autoOfPerm (G := cartesianProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (cartesianProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [cartesianProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff]

@[simp] theorem cartesianProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : cartesianProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the tensor product. -/
def tensorProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    tensorProduct G H ≃cg tensorProduct G H :=
  autoOfPerm (G := tensorProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (tensorProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [tensorProduct_adj, a.adj_eq, b.adj_eq]

@[simp] theorem tensorProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : tensorProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the strong product. -/
def strongProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    strongProduct G H ≃cg strongProduct G H :=
  autoOfPerm (G := strongProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (strongProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [strongProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff, ne_eq, Prod.ext_iff]

@[simp] theorem strongProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : strongProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the lexicographic product. -/
def lexProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    lexProduct G H ≃cg lexProduct G H :=
  autoOfPerm (G := lexProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (lexProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [lexProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff]

@[simp] theorem lexProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : lexProductAuto a b x = (a x.1, b x.2) := rfl

@[toIsoGraph]
theorem autCount_mul_le_autCount_cartesianProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (cartesianProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount cartesianProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg
      (fun σ : cartesianProduct G H ≃cg cartesianProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg
      (fun σ : cartesianProduct G H ≃cg cartesianProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_tensorProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (tensorProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount tensorProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : tensorProduct G H ≃cg tensorProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : tensorProduct G H ≃cg tensorProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_strongProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (strongProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount strongProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : strongProduct G H ≃cg strongProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : strongProduct G H ≃cg strongProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

@[toIsoGraph]
theorem autCount_mul_le_autCount_lexProduct (G H : CGraph)
 [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (lexProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount lexProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : lexProduct G H ≃cg lexProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : lexProduct G H ≃cg lexProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

/-! ### Vertices, edges and components -/

/-- Every vertex that is not the chosen root of its component has a neighbour strictly closer to
that root. -/
theorem exists_adj_dist_lt (G : CGraph) {v r : G.V} (hr : G.toSimple.Reachable v r) (hv : v ≠ r) :
    ∃ u, G.toSimple.Adj v u ∧ G.toSimple.dist u r < G.toSimple.dist v r := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hpos : 0 < G.toSimple.dist v r := hr.pos_dist_of_ne hv
  have hnp : ¬ p.Nil := by
    simp only [SimpleGraph.Walk.nil_iff_length_eq, hp]
    omega
  refine ⟨p.snd, p.adj_snd hnp, ?_⟩
  have h1 : G.toSimple.dist p.snd r ≤ p.tail.length := SimpleGraph.dist_le p.tail
  have h2 : p.tail.length + 1 = p.length := p.length_tail_add_one hnp
  omega

/-- Choosing, in every component, one vertex to be the root, and sending every other vertex to the
edge joining it to a neighbour closer to that root, embeds `V` minus the roots into `E`:
`|V| ≤ |E| + c(G)`. -/
@[toIsoGraph V_le_E_add_numComponents]
theorem card_le_E_add_numComponents (G : CGraph) :
    Fintype.card G.V ≤ G.E + G.numComponents := by
  classical
  rcases isEmpty_or_nonempty G.V with hV | hV
  · simp [Fintype.card_eq_zero]
  choose r hr using G.surjective_connectedComponentMk
  set root : G.V → G.V := fun v ↦ r (G.toSimple.connectedComponentMk v) with hroot
  have hreach : ∀ v, G.toSimple.Reachable v (root v) := by
    intro v
    apply SimpleGraph.ConnectedComponent.exact
    rw [hroot]
    exact (hr _).symm
  have hrootroot : ∀ c, root (r c) = r c := fun c ↦ by rw [hroot]; simp only [hr]
  -- the roots form a set of size `c(G)`
  have hinj : Function.Injective r := fun c d h ↦ by rw [← hr c, ← hr d, h]
  have himg : Finset.univ.filter (fun v ↦ v = root v) = Finset.univ.image r := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact fun h ↦ ⟨G.toSimple.connectedComponentMk v, h.symm⟩
    · rintro ⟨c, rfl⟩
      exact (hrootroot c).symm
  have hroots : (Finset.univ.filter (fun v ↦ v = root v)).card = G.numComponents := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  -- and every other vertex picks out an edge, injectively
  choose! u hu1 hu2 using fun v (hv : v ≠ root v) ↦ G.exists_adj_dist_lt (hreach v) hv
  have hne : ∀ {v w : G.V}, G.toSimple.Adj v w → root v = root w := fun {v w} h ↦ by
    rw [hroot]
    simp only
    rw [SimpleGraph.ConnectedComponent.sound h.reachable]
  have hmaps : ∀ v ∈ Finset.univ.filter (fun v ↦ ¬ v = root v),
      s(v, u v) ∈ G.toSimple.edgeFinset := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simpa using hu1 v hv
  have hinjOn : Set.InjOn (fun v ↦ s(v, u v))
      (Finset.univ.filter (fun v ↦ ¬ v = root v) : Finset G.V) := by
    intro v hv w hw h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have hrw : root v = root w := hne (h2 ▸ hu1 v hv)
      have d1 := hu2 v hv
      have d2 := hu2 w hw
      rw [← h1] at d2
      rw [h2, hrw] at d1
      omega
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G.V)) (p := fun v ↦ v = root v)
  have hle : (Finset.univ.filter (fun v ↦ ¬ v = root v)).card ≤ G.E :=
    Finset.card_le_card_of_injOn _ hmaps hinjOn
  rw [Finset.card_univ] at hcards
  omega

/-- A connected graph has at least `|V| - 1` edges. -/
theorem card_le_E_add_one_of_isConnected (G : CGraph) (h : G.IsConnected) :
    Fintype.card G.V ≤ G.E + 1 := by
  have := G.card_le_E_add_numComponents
  rw [(numComponents_eq_one_iff G).2 h] at this
  exact this

/-- Each edge can merge at most two components, so a graph with few edges has many components. -/
theorem card_sub_E_le_numComponents (G : CGraph) :
    Fintype.card G.V - G.E ≤ G.numComponents := by
  have := G.card_le_E_add_numComponents
  omega

/-- More components than vertices is impossible, so a graph with fewer components than vertices
has an edge. -/
theorem E_pos_of_numComponents_lt_card (G : CGraph) (h : G.numComponents < Fintype.card G.V) :
    0 < G.E := by
  have := G.card_le_E_add_numComponents
  omega

/-! ### The clique number of the Mycielskian -/

/-- The Mycielskian creates no new cliques: apart from the edges at the apex, every clique is a
clique of `G` in disguise. -/
@[toIsoGraph]
theorem cliqueNum_mycielskian (G : CGraph) [Nonempty G.V] :
    (mycielskian G).cliqueNum = max G.cliqueNum 2 := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  apply le_antisymm
  · obtain ⟨t, ht, hcard⟩ := (mycielskian G).toSimple.exists_isNClique_cliqueNum
    show (mycielskian G).toSimple.cliqueNum ≤ _
    rw [← hcard]
    by_cases hnone : (none : (mycielskian G).V) ∈ t
    · -- the apex is adjacent only to the copies, which are pairwise non-adjacent
      refine le_trans ?_ (le_max_right _ _)
      by_contra hc
      push_neg at hc
      have hcard' : 1 < (t.erase none).card := by
        rw [Finset.card_erase_of_mem hnone]
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard'
      have hinr : ∀ z ∈ t.erase none, ∃ b, z = some (.inr b) := by
        intro z hz
        have hzn : z ≠ none := Finset.ne_of_mem_erase hz
        have hadj := ht (by simpa using hnone) (by simpa using Finset.mem_of_mem_erase hz)
          (Ne.symm hzn)
        match z, hzn with
        | some (.inl b), _ => simp [CGraph.toSimple_adj] at hadj
        | some (.inr b), _ => exact ⟨b, rfl⟩
      obtain ⟨b, rfl⟩ := hinr x hx
      obtain ⟨c, rfl⟩ := hinr y hy
      have := ht (by simpa using Finset.mem_of_mem_erase hx)
        (by simpa using Finset.mem_of_mem_erase hy) hxy
      simp [CGraph.toSimple_adj] at this
    · -- no apex: forgetting which copy a vertex is in gives a clique of `G` of the same size
      refine le_trans ?_ (le_max_left _ _)
      set f : (mycielskian G).V → G.V := fun x ↦ x.elim a₀ (Sum.elim id id) with hf
      have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj (f x) (f y) = true := by
        intro x hx y hy hxy
        have h := ht (by simpa using hx) (by simpa using hy) hxy
        match x, (by rintro rfl; exact hnone hx : x ≠ none),
            y, (by rintro rfl; exact hnone hy : y ≠ none) with
        | some (.inl b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inl b), _, some (.inr c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inr c), _ => simp [CGraph.toSimple_adj] at h
      have hinj : Set.InjOn f t := by
        intro x hx y hy hfxy
        by_contra hxy
        have := hadj x hx y hy hxy
        rw [hfxy] at this
        exact absurd this (by simp [G.loopless])
      have hclique : G.toSimple.IsClique ((t.image f : Finset G.V) : Set G.V) := by
        intro u hu v hv huv
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        rw [CGraph.toSimple_adj]
        exact hadj x hx y hy fun h ↦ huv (by rw [h])
      calc t.card = (t.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ G.cliqueNum := hclique.card_le_cliqueNum
  · refine max_le ?_ ?_
    · -- `G` embeds as the `inl` copy
      obtain ⟨t, ht, hcard⟩ := G.toSimple.exists_isNClique_cliqueNum
      have hemb : Function.Injective (fun a : G.V ↦ (some (.inl a) : (mycielskian G).V)) := by
        intro a b h
        simpa using h
      have hclique : (mycielskian G).toSimple.IsClique
          ((t.map ⟨_, hemb⟩ : Finset (mycielskian G).V) : Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
          Function.Embedding.coeFn_mk] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        have := ht hx hy fun h ↦ huv (by rw [h])
        rw [CGraph.toSimple_adj] at this ⊢
        simpa using this
      calc G.cliqueNum = (t.map ⟨_, hemb⟩).card := by
            rw [Finset.card_map]; exact hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum
    · -- the apex together with any copy is an edge
      have hclique : (mycielskian G).toSimple.IsClique
          (({none, some (.inr a₀)} : Finset (mycielskian G).V) :
            Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
          simp_all [CGraph.toSimple_adj]
      have hcard : ({none, some (.inr a₀)} : Finset (mycielskian G).V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      calc (2 : ℕ) = ({none, some (.inr a₀)} : Finset (mycielskian G).V).card := hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum

/-- Mycielski's construction preserves triangle-freeness. -/
@[toIsoGraph]
theorem cliqueNum_mycielskian_eq_two (G : CGraph) [Nonempty G.V]
    (h : G.cliqueNum ≤ 2) : (mycielskian G).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian]
  omega

/-! ### Edge counts of the strong and lexicographic products -/

private theorem sum_degree_add_one (K : CGraph) :
    ∑ v : K.V, (K.toSimple.degree v + 1) = 2 * K.E + Fintype.card K.V := by
  rw [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]
  rfl

theorem E_strongProduct (G H : CGraph) :
    (strongProduct G H).E
      = Fintype.card G.V * H.E + Fintype.card H.V * G.E + 2 * G.E * H.E := by
  have hdeg : ∀ p : G.V × H.V, (strongProduct G H).toSimple.degree p + 1
      = (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) := by
    intro p
    have h := degree_strongProduct G H p
    have hpos : 1 ≤ (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hdegsum : ∑ p : G.V × H.V, (strongProduct G H).toSimple.degree p
      = 2 * (strongProduct G H).E := SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hstrong : ∑ p : G.V × H.V, ((strongProduct G H).toSimple.degree p + 1)
      = 2 * (strongProduct G H).E + Fintype.card G.V * Fintype.card H.V := by
    rw [Finset.sum_add_distrib, hdegsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod]
  have key : 2 * (strongProduct G H).E + Fintype.card G.V * Fintype.card H.V
      = (2 * G.E + Fintype.card G.V) * (2 * H.E + Fintype.card H.V) := by
    rw [← hstrong, ← sum_degree_add_one G, ← sum_degree_add_one H, Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b)
  have expand : (2 * G.E + Fintype.card G.V) * (2 * H.E + Fintype.card H.V)
      = 2 * (Fintype.card G.V * H.E + Fintype.card H.V * G.E + 2 * G.E * H.E)
        + Fintype.card G.V * Fintype.card H.V := by ring
  rw [expand] at key
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel key)

theorem E_lexProduct (G H : CGraph) :
    (lexProduct G H).E
      = Fintype.card H.V * Fintype.card H.V * G.E + Fintype.card G.V * H.E := by
  have hdeg : ∀ p : G.V × H.V, (lexProduct G H).toSimple.degree p
      = G.toSimple.degree p.1 * Fintype.card H.V + H.toSimple.degree p.2 :=
    fun p ↦ degree_lexProduct G H p
  have hG : ∑ a : G.V, G.toSimple.degree a = 2 * G.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hH : ∑ b : H.V, H.toSimple.degree b = 2 * H.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hlex : ∑ p : G.V × H.V, (lexProduct G H).toSimple.degree p
      = 2 * (lexProduct G H).E := SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hfibre : ∀ a : G.V,
      ∑ b : H.V, (G.toSimple.degree a * Fintype.card H.V + H.toSimple.degree b)
        = G.toSimple.degree a * (Fintype.card H.V * Fintype.card H.V) + 2 * H.E := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, hH]
    ring
  have key : 2 * (lexProduct G H).E
      = 2 * (Fintype.card H.V * Fintype.card H.V * G.E + Fintype.card G.V * H.E) := by
    rw [← hlex, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b),
      Finset.sum_congr rfl fun a _ ↦ hfibre a, Finset.sum_add_distrib, ← Finset.sum_mul, hG,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-! ### Domination in disjoint unions, joins and cartesian products -/

theorem isDominatingSet_disjSum {G H : CGraph} {s : Finset G.V} {t : Finset H.V}
    (hs : G.IsDominatingSet s) (ht : H.IsDominatingSet t) :
    (disjUnion G H).IsDominatingSet (s.disjSum t) := by
  intro v
  rcases v with a | b
  · rcases hs a with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inl_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inl u, Finset.inl_mem_disjSum.2 hu, by simpa using hadj⟩
  · rcases ht b with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inr_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inr u, Finset.inr_mem_disjSum.2 hu, by simpa using hadj⟩

/-- **Domination is additive over components**: the two sides of a disjoint union have to be
dominated separately, and any two dominating sets can be put side by side. -/
@[toIsoGraph]
theorem domNum_disjUnion (G H : CGraph) :
    (disjUnion G H).domNum = G.domNum + H.domNum := by
  apply le_antisymm
  · obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
    obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
    have h := domNum_le_card_of_isDominatingSet (isDominatingSet_disjSum hsdom htdom)
    rwa [Finset.card_disjSum, hs, ht] at h
  · obtain ⟨u, hu, hudom⟩ := (disjUnion G H).exists_isDominatingSet_domNum
    have hG : G.IsDominatingSet u.toLeft := by
      intro v
      rcases hudom (Sum.inl v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toLeft.2 h)
      · rcases w with a | b
        · exact Or.inr ⟨a, Finset.mem_toLeft.2 hw, by simpa using hadj⟩
        · simp at hadj
    have hH : H.IsDominatingSet u.toRight := by
      intro v
      rcases hudom (Sum.inr v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toRight.2 h)
      · rcases w with a | b
        · simp at hadj
        · exact Or.inr ⟨b, Finset.mem_toRight.2 hw, by simpa using hadj⟩
    have h1 := domNum_le_card_of_isDominatingSet hG
    have h2 := domNum_le_card_of_isDominatingSet hH
    have h3 : u.toLeft.card + u.toRight.card = u.card :=
      Finset.card_toLeft_add_card_toRight
    omega

/-- One vertex from each side dominates a join. -/
@[toIsoGraph]
theorem domNum_join_le_two (G H : CGraph)
    [Nonempty G.V] [Nonempty H.V] : (join G H).domNum ≤ 2 := by
  obtain ⟨a⟩ := ‹Nonempty G.V›
  obtain ⟨b⟩ := ‹Nonempty H.V›
  have hdom : (join G H).IsDominatingSet {Sum.inl a, Sum.inr b} := by
    intro v
    rcases v with x | y
    · by_cases h : x = a
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inr b, by simp, join_adj_inr_inl G H b x⟩
    · by_cases h : y = b
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inl a, by simp, join_adj_inl_inr G H a y⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  have hcard : ({Sum.inl a, Sum.inr b} : Finset (join G H).V).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- A single vertex dominates a join exactly when it is universal on its own side: the other side
is seen for free. -/
theorem domNum_join_eq_one_iff (G H : CGraph) :
    (join G H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  rw [domNum_eq_one_iff, domNum_eq_one_iff, domNum_eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    rcases v with a | b
    · refine Or.inl ⟨a, fun u hu ↦ ?_⟩
      have := hv (Sum.inl u) fun h ↦ hu (Sum.inl_injective h)
      simpa using this
    · refine Or.inr ⟨b, fun u hu ↦ ?_⟩
      have := hv (Sum.inr u) fun h ↦ hu (Sum.inr_injective h)
      simpa using this
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Sum.inl a, fun u hu ↦ ?_⟩
      rcases u with c | d
      · rw [join_adj_inl_inl]
        exact ha c fun h ↦ hu (congrArg Sum.inl h)
      · exact join_adj_inl_inr G H a d
    · refine ⟨Sum.inr b, fun u hu ↦ ?_⟩
      rcases u with c | d
      · exact join_adj_inr_inl G H b c
      · rw [join_adj_inr_inr]
        exact hb d fun h ↦ hu (congrArg Sum.inr h)

/-- Without a universal vertex on either side, a join needs exactly two dominating vertices. -/
@[toIsoGraph]
theorem domNum_join_eq_two (G H : CGraph)
    [Nonempty G.V] [Nonempty H.V] (hG : G.domNum ≠ 1) (hH : H.domNum ≠ 1) :
    (join G H).domNum = 2 := by
  haveI : Nonempty (join G H).V := ⟨Sum.inl (Classical.arbitrary G.V)⟩
  have h1 := domNum_join_le_two G H
  have h2 := (join G H).domNum_pos (Fintype.card_pos_iff.2 ‹Nonempty (join G H).V›)
  have h3 : (join G H).domNum ≠ 1 := fun h ↦ by
    rcases (domNum_join_eq_one_iff G H).1 h with h | h
    · exact hG h
    · exact hH h
  omega

/-- A dominating set of `G`, spread over every fibre, dominates `G □ H`. -/
@[toIsoGraph]
theorem domNum_cartesianProduct_le (G H : CGraph) :
    (cartesianProduct G H).domNum ≤ G.domNum * Fintype.card H.V := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (cartesianProduct G H).IsDominatingSet (s ×ˢ Finset.univ) := by
    rintro ⟨x, y⟩
    rcases hsdom x with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
    · refine Or.inr ⟨(u, y), Finset.mem_product.2 ⟨hu, Finset.mem_univ _⟩, ?_⟩
      rw [cartesianProduct_adj]
      simp [hadj]
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, Finset.card_univ, hs] at h

/-! ### The radius of a cartesian product -/

/-- **The radius of a cartesian product is the sum of the radii.**  Both factors have to be
connected: the radius of a disconnected graph is the junk value `0`. -/
@[toIsoGraph]
theorem radius_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (cartesianProduct G H).radius = G.radius + H.radius := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hGtop : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hG
  have hHtop : H.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hH
  have h : (cartesianProduct G H).toSimple.radius = G.toSimple.radius + H.toSimple.radius := by
    rw [toSimple_cartesianProduct]
    exact radius_boxProd _ _
  show (cartesianProduct G H).toSimple.radius.toNat = _
  rw [h, ENat.toNat_add hGtop hHtop]
  rfl

/-- Adding edges cannot increase the diameter: the strong product is at most as wide as the
cartesian product living inside it. -/
@[toIsoGraph]
theorem diameter_strongProduct_le (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (strongProduct G H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (cartesianProduct G H).IsConnected :=
    (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (cartesianProduct G H).V := hcp.nonempty
  have hne : (cartesianProduct G H).toSimple.ediam ≠ ⊤ :=
    SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_strongProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-- The same bound for the lexicographic product. -/
@[toIsoGraph]
theorem diameter_lexProduct_le (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (lexProduct G H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (cartesianProduct G H).IsConnected :=
    (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (cartesianProduct G H).V := hcp.nonempty
  have hne : (cartesianProduct G H).toSimple.ediam ≠ ⊤ :=
    SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_lexProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-! ### Domination in the graph products -/

/-- **Vizing's bound for the strong product**: a product of dominating sets dominates, because a
vertex of `G ⊠ H` is either equal or adjacent to a dominator in each coordinate. -/
@[toIsoGraph]
theorem domNum_strongProduct_le (G H : CGraph) :
    (strongProduct G H).domNum ≤ G.domNum * H.domNum := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
  have hdom : (strongProduct G H).IsDominatingSet (s ×ˢ t) := by
    rintro ⟨x, y⟩
    have hx : ∃ u ∈ s, u = x ∨ G.Adj u x = true := by
      rcases hsdom x with h | ⟨u, hu, hadj⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨u, hu, Or.inr hadj⟩
    have hy : ∃ v ∈ t, v = y ∨ H.Adj v y = true := by
      rcases htdom y with h | ⟨v, hv, hadj⟩
      · exact ⟨y, h, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr hadj⟩
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    by_cases hpq : ((u, v) : (strongProduct G H).V) = (x, y)
    · exact Or.inl (hpq ▸ Finset.mem_product.2 ⟨hu, hv⟩)
    · refine Or.inr ⟨(u, v), Finset.mem_product.2 ⟨hu, hv⟩, ?_⟩
      rw [strongProduct_adj]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨hpq, hux, hvy⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, hs, ht] at h

/-- Forgetting the second coordinate turns a dominating set of `G[H]` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_lexProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (lexProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (lexProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (lexProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [lexProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with h1 | ⟨h1, -⟩
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- **A blow-up by a dominated graph does not change the domination number**: if some vertex of `H`
sees all of `H`, then a dominating set of `G` lifted into that vertex's fibre dominates `G[H]`. -/
@[toIsoGraph]
theorem domNum_lexProduct (G H : CGraph)
    (hH : H.domNum = 1) : (lexProduct G H).domNum = G.domNum := by
  obtain ⟨x, hx⟩ := (domNum_eq_one_iff H).1 hH
  haveI : Nonempty H.V := ⟨x⟩
  refine le_antisymm ?_ (domNum_le_domNum_lexProduct G H)
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (lexProduct G H).IsDominatingSet (s.image fun v ↦ (v, x)) := by
    rintro ⟨u, y⟩
    rcases hsdom u with h | ⟨v, hv, hadj⟩
    · by_cases hy : y = x
      · exact Or.inl (Finset.mem_image.2 ⟨u, h, by rw [hy]⟩)
      · refine Or.inr ⟨(u, x), Finset.mem_image.2 ⟨u, h, rfl⟩, ?_⟩
        rw [lexProduct_adj]
        simp [hx y hy]
    · refine Or.inr ⟨(v, x), Finset.mem_image.2 ⟨v, hv, rfl⟩, ?_⟩
      rw [lexProduct_adj]
      simp [hadj]
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  rw [Finset.card_image_of_injective _ fun a b hab ↦ congrArg Prod.fst hab, hs]

/-- Forgetting the second coordinate turns a dominating set of `G □ H` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_cartesianProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (cartesianProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (cartesianProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (cartesianProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [cartesianProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- Forgetting the second coordinate turns a dominating set of `G ⊠ H` into one of `G`. -/
@[toIsoGraph]
theorem domNum_le_domNum_strongProduct (G H : CGraph)
    [Nonempty H.V] : G.domNum ≤ (strongProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (strongProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (strongProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [strongProduct_adj] at hadj
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hadj
      rcases hadj.2.1 with h1 | h1
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-! ### Independence numbers of the graph products -/

/-- Independence number is antitone in the graph: adding edges can only shrink it. -/
private theorem indepNum_anti {α : Type} [Fintype α] {S T : SimpleGraph α} (h : S ≤ T) :
    T.indepNum ≤ S.indepNum := by
  obtain ⟨s, hs, hcard⟩ := T.exists_isNIndepSet_indepNum
  have hind : S.IsIndepSet (s : Set α) := by
    intro x hx y hy hxy hadj
    exact hs hx hy hxy (h hadj)
  exact hcard ▸ hind.card_le_indepNum

/-- The strong product is a subgraph of the lexicographic product. -/
theorem strongProduct_le_lexProduct (G H : CGraph) :
    (strongProduct G H).toSimple ≤ (lexProduct G H).toSimple := by
  intro p q hpq
  rw [CGraph.toSimple_adj, strongProduct_adj] at hpq
  rw [CGraph.toSimple_adj, lexProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hpq ⊢
  obtain ⟨hne, h1, h2⟩ := hpq
  rcases h1 with h1 | h1
  · refine Or.inr ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (Prod.ext h1 h2) hne
    · exact h2
  · exact Or.inl h1

/-- **A product of independent sets is independent in the strong product**, so
`α(G) · α(H) ≤ α(G ⊠ H)`.  This is the inequality behind the Shannon capacity of a graph. -/
@[toIsoGraph]
theorem indepNum_mul_indepNum_le_indepNum_strongProduct (G H : CGraph)
 :
    G.indepNum * H.indepNum ≤ (strongProduct G H).indepNum := by
  have h := indepNum_anti (strongProduct_le_lexProduct G H)
  rwa [show (lexProduct G H).toSimple.indepNum = G.indepNum * H.indepNum from
    indepNum_lexProduct G H] at h

/-- The same product set is independent in the (sparser) cartesian product. -/
@[toIsoGraph]
theorem indepNum_mul_indepNum_le_indepNum_cartesianProduct (G H : CGraph)
 :
    G.indepNum * H.indepNum ≤ (cartesianProduct G H).indepNum :=
  le_trans (indepNum_mul_indepNum_le_indepNum_strongProduct G H)
    (indepNum_anti (cartesianProduct_le_strongProduct G H))

/-- In the tensor product a whole slab `S ×ˢ univ` over an independent set `S` is independent,
because every tensor edge moves in *both* coordinates: `α(G) · |V(H)| ≤ α(G × H)`. -/
@[toIsoGraph indepNum_mul_V_le_indepNum_tensorProduct]
theorem indepNum_mul_card_le_indepNum_tensorProduct (G H : CGraph)
 :
    G.indepNum * Fintype.card H.V ≤ (tensorProduct G H).indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hind : (tensorProduct G H).toSimple.IsIndepSet
      ((s ×ˢ (Finset.univ : Finset H.V) : Finset (G.V × H.V)) : Set (G.V × H.V)) := by
    intro p hp q hq hpq hadj
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    rw [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true] at hadj
    have hne : p.1 ≠ q.1 := fun h ↦ G.loopless q.1 (h ▸ hadj.1)
    exact hs hp.1 hq.1 hne hadj.1
  calc G.indepNum * Fintype.card H.V
      = (s ×ˢ (Finset.univ : Finset H.V)).card := by
        rw [Finset.card_product, hcard, Finset.card_univ]
        rfl
    _ ≤ _ := hind.card_le_indepNum

/-- Fibrewise counting: an independent set of `G □ H` meets each fibre `{a} × V(H)` in an
independent set of `H`, so `α(G □ H) ≤ |V(G)| · α(H)`. -/
@[toIsoGraph]
theorem indepNum_cartesianProduct_le (G H : CGraph) :
    (cartesianProduct G H).indepNum ≤ Fintype.card G.V * H.indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := (cartesianProduct G H).toSimple.exists_isNIndepSet_indepNum
  have hfib : ∀ a : G.V, (s.filter fun p ↦ p.1 = a).card ≤ H.indepNum := by
    intro a
    have hindH : H.toSimple.IsIndepSet
        (((s.filter fun p ↦ p.1 = a).image Prod.snd : Finset H.V) : Set H.V) := by
      intro y hy z hz hyz hadj
      rw [Finset.mem_coe, Finset.mem_image] at hy hz
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨q, hq, rfl⟩ := hz
      rw [Finset.mem_filter] at hp hq
      refine hs hp.1 hq.1 (fun h ↦ hyz (congrArg Prod.snd h)) ?_
      rw [CGraph.toSimple_adj, cartesianProduct_adj]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨hp.2.trans hq.2.symm, hadj⟩
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd
      (fun p hp ↦ Finset.mem_image_of_mem _ hp) ?_) hindH.card_le_indepNum
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq
  have hsum : s.card = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ ↦ Finset.mem_univ p.1
  calc (cartesianProduct G H).indepNum = s.card := hcard.symm
    _ = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card := hsum
    _ ≤ ∑ _a : G.V, H.indepNum := Finset.sum_le_sum fun a _ ↦ hfib a
    _ = Fintype.card G.V * H.indepNum := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The strong product has at least as many edges as the cartesian one, so the same bound holds. -/
@[toIsoGraph]
theorem indepNum_strongProduct_le (G H : CGraph) :
    (strongProduct G H).indepNum ≤ Fintype.card G.V * H.indepNum :=
  le_trans (indepNum_anti (cartesianProduct_le_strongProduct G H))
    (indepNum_cartesianProduct_le G H)

/-! ### Colouring the strong product -/

/-- **The strong product multiplies chromatic numbers, at worst**: it sits inside the
lexicographic product, which is already known to satisfy `χ ≤ χ(G)·χ(H)`, and colourings pull
back along subgraph inclusions. -/
@[toIsoGraph]
theorem chromNum_strongProduct_le (G H : CGraph) :
    (strongProduct G H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2
    ((chromNum_le_iff_colorable.1 (chromNum_lexProduct_le G H)).mono_left
      (strongProduct_le_lexProduct G H))

/-- Both factors appear as fibres of the cartesian product, which the strong product contains,
so `max χ(G) χ(H) ≤ χ(G ⊠ H)`. -/
theorem max_chromNum_le_chromNum_strongProduct (G H : CGraph)
    (a : G.V) (b : H.V) : max G.chromNum H.chromNum ≤ (strongProduct G H).chromNum := by
  rw [← chromNum_cartesianProduct G H a b]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_strongProduct G H))

/-- The same sandwich for the lexicographic product. -/
theorem max_chromNum_le_chromNum_lexProduct (G H : CGraph)
    (a : G.V) (b : H.V) : max G.chromNum H.chromNum ≤ (lexProduct G H).chromNum := by
  rw [← chromNum_cartesianProduct G H a b]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_lexProduct G H))

/-- Cliques multiply in the strong product, so `ω(G)·ω(H) ≤ χ(G ⊠ H)`: the lower bound coming
from cliques is itself multiplicative. -/
@[toIsoGraph]
theorem cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (G H : CGraph)
 :
    G.cliqueNum * H.cliqueNum ≤ (strongProduct G H).chromNum := by
  have h := (strongProduct G H).cliqueNum_le_chromNum
  rwa [cliqueNum_strongProduct] at h

/-- The tensor product of two graphs with an edge has an edge, hence needs two colours.  Together
with `chromNum_tensorProduct_le` this pins `χ(G × H) = 2` as soon as one factor is bipartite and
both have an edge.  In general the lower bound is the hard direction: Hedetniemi's conjecture that
`χ(G × H) = min χ(G) χ(H)` is false. -/
@[toIsoGraph]
theorem two_le_chromNum_tensorProduct {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) : 2 ≤ (tensorProduct G H).chromNum := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  refine two_le_chromNum_of_adj (a := ((a, b) : (tensorProduct G H).V)) (b := (a', b')) ?_
  rw [tensorProduct_adj]
  simp [ha, hb]

/-- One bipartite factor is enough: if `G` is bipartite and both factors have an edge then
`χ(G × H) = 2`. -/
@[toIsoGraph]
theorem chromNum_tensorProduct_eq_two {G H : CGraph}
    (hG : G.IsBipartite) (hGE : 0 < G.E) (hHE : 0 < H.E) :
    (tensorProduct G H).chromNum = 2 :=
  le_antisymm
    (le_trans (chromNum_tensorProduct_le G H)
      (le_trans (min_le_left _ _) (isBipartite_iff_chromNum_le_two.1 hG)))
    (two_le_chromNum_tensorProduct hGE hHE)


/-! ### Nordhaus–Gaddum for the domination number -/

/-- **`γ(G) + γ(Gᶜ) ≤ |V| + 1`.**  Each graph satisfies `γ + Δ ≤ |V|`, and complementation turns
the maximum degree into `|V| - 1 - δ`, so the two bounds add up with `δ ≤ Δ` to spare. -/
@[toIsoGraph domNum_add_domNum_compl_le_V_add_one]
theorem domNum_add_domNum_compl_le_card_add_one (G : CGraph) :
    G.domNum + Gᶜ.domNum ≤ Fintype.card G.V + 1 := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : Fintype.card G.V = 0 := Fintype.card_eq_zero
    have h2 := G.domNum_le_card
    have h3 := Gᶜ.domNum_le_card
    have h4 : Fintype.card Gᶜ.V = Fintype.card G.V := rfl
    omega
  haveI := hne
  obtain ⟨v₀⟩ := hne
  have h1 := G.domNum_add_maxDeg_le_card
  have h2 := Gᶜ.domNum_add_maxDeg_le_card
  rw [maxDeg_compl (G := G), show Fintype.card Gᶜ.V = Fintype.card G.V from rfl] at h2
  have h3 := G.minDeg_le_maxDeg
  have h4 := G.maxDeg_lt_card v₀
  omega

/-- Two vertices in different components dominate the complement: whatever `x` is, it is
unreachable from one of them, hence adjacent to it in `Gᶜ`. -/
theorem domNum_compl_le_two_of_not_reachable (G : CGraph) {a b : G.V}
    (h : ¬ G.toSimple.Reachable a b) : Gᶜ.domNum ≤ 2 := by
  classical
  have hdom : Gᶜ.IsDominatingSet ({a, b} : Finset G.V) := by
    intro x
    by_cases hxa : x = a
    · exact Or.inl (by simp [hxa])
    by_cases hxb : x = b
    · exact Or.inl (by simp [hxb])
    by_cases hr : G.toSimple.Reachable a x
    · refine Or.inr ⟨b, by simp, ?_⟩
      have hbx : ¬ G.toSimple.Reachable b x := fun hbx ↦ h (hr.trans hbx.symm)
      simpa using compl_adj_of_not_reachable G hbx
    · exact Or.inr ⟨a, by simp, by simpa using compl_adj_of_not_reachable G hr⟩
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- A disconnected graph has a complement that two vertices dominate. -/
@[toIsoGraph]
theorem domNum_compl_le_two_of_not_isConnected (G : CGraph) [Nonempty G.V]
    (h : ¬ G.IsConnected) : Gᶜ.domNum ≤ 2 := by
  rw [IsConnected, SimpleGraph.connected_iff] at h
  push_neg at h
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.toSimple.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact absurd (h fun a b ↦ hc a b) (not_isEmpty_iff.2 ‹Nonempty G.V›)
  exact domNum_compl_le_two_of_not_reachable G hab

/-- A graph and its complement cannot both have a universal vertex once there are two vertices,
so `3 ≤ γ(G) + γ(Gᶜ)`. -/
@[toIsoGraph]
theorem three_le_domNum_add_domNum_compl (G : CGraph)
    (hV : 2 ≤ Fintype.card G.V) : 3 ≤ G.domNum + Gᶜ.domNum := by
  have hG : 0 < G.domNum := G.domNum_pos (by omega)
  have hGc : 0 < Gᶜ.domNum :=
    Gᶜ.domNum_pos (by rw [show Fintype.card Gᶜ.V = Fintype.card G.V from rfl]; omega)
  by_contra hc
  have h1 : G.domNum = 1 := by omega
  have h2 : Gᶜ.domNum = 1 := by omega
  obtain ⟨v, hv⟩ := (domNum_eq_one_iff G).1 h1
  obtain ⟨w, hw⟩ := (domNum_eq_one_iff Gᶜ).1 h2
  by_cases hvw : w = v
  · subst hvw
    obtain ⟨u, hu⟩ : ∃ u : G.V, u ≠ w := by
      by_contra hc'
      push_neg at hc'
      have : Fintype.card G.V ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ (hc' a).trans (hc' b).symm
      omega
    have h3 := hv u hu
    have h4 := hw u hu
    rw [compl_adj] at h4
    simp [h3] at h4
  · have h3 := hv w hvw
    have h4 := hw v (fun h ↦ hvw h.symm)
    rw [compl_adj] at h4
    rw [G.symm v w] at h3
    simp [h3] at h4


/-! ### Nordhaus–Gaddum for the clique and independence numbers -/

/-- A single vertex is a one-element independent set. -/
theorem one_le_indepNum_of_vertex {G : CGraph} (a : G.V) : 1 ≤ G.indepNum := by
  classical
  have hind : G.toSimple.IsIndepSet ((({a} : Finset G.V)) : Set G.V) := by
    intro x hx y hy hxy
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  simpa using hind.card_le_indepNum

/-- Two distinct non-adjacent vertices form a two-element independent set. -/
theorem two_le_indepNum {G : CGraph} {a b : G.V} (hab : a ≠ b) (h : ¬ G.Adj a b) :
    2 ≤ G.indepNum := by
  classical
  have hind : G.toSimple.IsIndepSet ((({a, b} : Finset G.V)) : Set G.V) := by
    intro x hx y hy hxy hadj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rw [toSimple_adj] at hadj
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact h hadj
    · exact h ((G.symm _ _).symm ▸ hadj)
    · exact hxy rfl
  have := hind.card_le_indepNum
  rwa [Finset.card_pair hab] at this

/-- **Nordhaus–Gaddum for the clique number**: `ω(G) + α(G) ≤ |V| + 1`, since `ω ≤ χ` and
`χ(G) + α(G) ≤ |V| + 1`.  Equality holds for both the complete and the edgeless graph. -/
@[toIsoGraph cliqueNum_add_indepNum_le_V_add_one]
theorem cliqueNum_add_indepNum_le_card_add_one (G : CGraph) :
    G.cliqueNum + G.indepNum ≤ Fintype.card G.V + 1 :=
  le_trans (Nat.add_le_add_right G.cliqueNum_le_chromNum _)
    G.chromNum_add_indepNum_le_card_add_one

/-- On two or more vertices, `3 ≤ ω(G) + α(G)`: any two distinct vertices are either adjacent,
giving a two-clique, or non-adjacent, giving a two-element independent set. -/
@[toIsoGraph]
theorem three_le_cliqueNum_add_indepNum (G : CGraph) (hV : 2 ≤ Fintype.card G.V) :
    3 ≤ G.cliqueNum + G.indepNum := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := G.V) (by omega)
  by_cases h : G.Adj a b
  · have h1 := two_le_cliqueNum h
    have h2 := one_le_indepNum_of_vertex a
    omega
  · have h1 := one_le_cliqueNum_of_vertex a
    have h2 := two_le_indepNum hab h
    omega


/-! ### Regular graphs -/

theorem isRegularWith_iff_forall_degree {G : CGraph} {k : ℕ} :
    G.IsRegularWith k ↔ ∀ v : G.V, G.toSimple.degree v = k := Iff.rfl

@[toIsoGraph]
theorem IsRegularWith.degSequence {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.degSequence = List.replicate (Fintype.card G.V) k := degSequence_of_regular G h

/-- Squeezing the degrees between the two extremes forces regularity. -/
@[toIsoGraph]
theorem isRegularWith_of_maxDeg_le_of_le_minDeg {G : CGraph} {k : ℕ}
    (h1 : G.maxDeg ≤ k) (h2 : k ≤ G.minDeg) : G.IsRegularWith k := fun v ↦
  le_antisymm (le_trans (G.degree_le_maxDeg v) h1) (le_trans h2 (G.minDeg_le_degree v))

theorem IsRegularWith.maxDeg_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) (v₀ : G.V) :
    G.maxDeg = k :=
  le_antisymm (maxDeg_le_of_forall fun v ↦ (h v).le) (h v₀ ▸ G.degree_le_maxDeg v₀)

theorem IsRegularWith.minDeg_eq {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) (v₀ : G.V) :
    G.minDeg = k :=
  le_antisymm (h v₀ ▸ G.minDeg_le_degree v₀) (le_minDeg_of_forall v₀ fun v ↦ (h v).ge)

/-- **Strongly regular graphs are regular**, with the same degree parameter. -/
@[toIsoGraph]
theorem IsSRGWith.isRegularWith {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    G.IsRegularWith k := SimpleGraph.IsSRGWith.regular h

/-- **The complement of a `k`-regular graph is `(n - 1 - k)`-regular.** -/
@[toIsoGraph]
theorem IsRegularWith.compl {G : CGraph} {k : ℕ} (h : G.IsRegularWith k) :
    Gᶜ.IsRegularWith (Fintype.card G.V - 1 - k) := fun v ↦ by
  rw [degree_compl, h v]

/-- A disjoint union of two `k`-regular graphs is `k`-regular. -/
@[toIsoGraph]
theorem IsRegularWith.disjUnion {G H : CGraph} {k : ℕ} (hG : G.IsRegularWith k)
    (hH : H.IsRegularWith k) : (disjUnion G H).IsRegularWith k := by
  rintro (a | b)
  · rw [degree_disjUnion_inl]; exact hG a
  · rw [degree_disjUnion_inr]; exact hH b

/-- A join is regular exactly when the two sides end up with the same total degree: each vertex
of `G` picks up all of `H` and vice versa. -/
@[toIsoGraph]
theorem IsRegularWith.join {G H : CGraph} {k l m : ℕ}
    (hG : G.IsRegularWith k) (hH : H.IsRegularWith l)
    (h1 : k + Fintype.card H.V = m) (h2 : Fintype.card G.V + l = m) :
    (join G H).IsRegularWith m := by
  rintro (a | b)
  · rw [degree_join_inl, hG a]; exact h1
  · rw [degree_join_inr, hH b]; exact h2


/-! ### Degrees in the line graph -/

/-- The degree of the edge `s(u, v)` as a vertex of the line graph: the other edges at `u`
and the other edges at `v`, with no overlap. -/
theorem degree_lineGraph_mk (G : CGraph) {u v : G.V}
    (h : s(u, v) ∈ G.toSimple.edgeSet) :
    (lineGraph G).toSimple.degree ⟨s(u, v), h⟩
      = G.toSimple.degree u + G.toSimple.degree v - 2 := by
  have hadj : G.toSimple.Adj u v := h
  have huv : u ≠ v := hadj.ne
  have hu : 0 < G.toSimple.degree u :=
    G.toSimple.degree_pos_iff_exists_adj u |>.2 ⟨v, hadj⟩
  have hv : 0 < G.toSimple.degree v :=
    G.toSimple.degree_pos_iff_exists_adj v |>.2 ⟨u, hadj.symm⟩
  rw [degree_lineGraph]
  show ∑ w ∈ (s(u, v) : Sym2 G.V).toFinset, (G.toSimple.degree w - 1) = _
  rw [Sym2.toFinset_mk_eq, Finset.sum_pair huv]
  omega

/-- Every vertex of the line graph is an edge `s(u, v)` of `G`. -/
theorem lineGraph_vertex_cases {G : CGraph}
    {motive : (lineGraph G).V → Prop}
    (h : ∀ (u v : G.V) (huv : s(u, v) ∈ G.toSimple.edgeSet), motive ⟨s(u, v), huv⟩)
    (e : (lineGraph G).V) : motive e := by
  obtain ⟨e, he⟩ := e
  obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
  exact h u v he

/-- The line graph of a `k`-regular graph is `(2k - 2)`-regular. -/
@[toIsoGraph]
theorem IsRegularWith.lineGraph {G : CGraph} {k : ℕ}
    (h : G.IsRegularWith k) : (CGraph.lineGraph G).IsRegularWith (2 * k - 2) := by
  refine lineGraph_vertex_cases fun u v huv ↦ ?_
  rw [degree_lineGraph_mk G huv, h u, h v]
  omega

@[toIsoGraph]
theorem maxDeg_lineGraph_le (G : CGraph) :
    (lineGraph G).maxDeg ≤ 2 * G.maxDeg - 2 := by
  refine maxDeg_le_of_forall (lineGraph_vertex_cases fun u v huv ↦ ?_)
  rw [degree_lineGraph_mk G huv]
  have h1 := G.degree_le_maxDeg u
  have h2 := G.degree_le_maxDeg v
  omega

theorem le_minDeg_lineGraph (G : CGraph) (e₀ : (lineGraph G).V) :
    2 * G.minDeg - 2 ≤ (lineGraph G).minDeg := by
  refine le_minDeg_of_forall e₀ (lineGraph_vertex_cases fun u v huv ↦ ?_)
  rw [degree_lineGraph_mk G huv]
  have h1 := G.minDeg_le_degree u
  have h2 := G.minDeg_le_degree v
  omega

/-! ### Consequences of regularity -/

theorem adj_eq_false_of_isRegularWith_zero {G : CGraph} (h : G.IsRegularWith 0) (x y : G.V) :
    G.Adj x y = false := by
  by_contra hxy
  have hadj : G.toSimple.Adj x y := by
    simp only [toSimple_adj]
    simpa using hxy
  have hpos : 0 < G.toSimple.degree x := (G.toSimple.degree_pos_iff_exists_adj x).2 ⟨y, hadj⟩
  have hd : G.toSimple.degree x = 0 := h x
  omega

/-! ### Cliques in the line graph -/

/-- The edges at a fixed vertex are pairwise adjacent in the line graph, so they form a clique
of size `deg v`. -/
theorem degree_le_cliqueNum_lineGraph (G : CGraph) (v : G.V) :
    G.toSimple.degree v ≤ (lineGraph G).cliqueNum := by
  classical
  set T : Finset (lineGraph G).V := {e | v ∈ e.1} with hT
  have hmemT : ∀ e : (lineGraph G).V, e ∈ T ↔ v ∈ e.1 := by
    intro e; rw [hT]; simp
  have hcl : (lineGraph G).toSimple.IsClique (T : Set (lineGraph G).V) := by
    intro e he f hf hef
    rw [Finset.mem_coe, hmemT] at he hf
    rw [toSimple_adj, lineGraph_adj]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    exact ⟨hef, v, he, hf⟩
  have hcard : T.card = G.toSimple.degree v := by
    rw [← SimpleGraph.card_incidenceFinset_eq_degree]
    refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
    · intro e he
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨e.2, (hmemT e).1 he⟩
    · intro e _ f _ h
      exact Subtype.ext h
    · intro x hx
      rw [SimpleGraph.mem_incidenceFinset] at hx
      exact ⟨⟨x, hx.1⟩, (hmemT _).2 hx.2, rfl⟩
  have hle := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)
  rw [← hcard]
  exact hle

@[toIsoGraph]
theorem maxDeg_le_cliqueNum_lineGraph (G : CGraph) :
    G.maxDeg ≤ (lineGraph G).cliqueNum :=
  maxDeg_le_of_forall fun v ↦ degree_le_cliqueNum_lineGraph G v

/-! ### Matchings -/

/-- Distinct non-adjacent vertices of the line graph are vertex-disjoint edges of `G`. -/
theorem disjoint_of_not_adj_lineGraph (G : CGraph)
    {e f : (lineGraph G).V} (hef : e ≠ f) (h : ¬ (lineGraph G).toSimple.Adj e f) :
    Disjoint e.1.toFinset f.1.toFinset := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  refine h ?_
  rw [toSimple_adj, lineGraph_adj]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  exact ⟨hef, v, Sym2.mem_toFinset.1 hv, Sym2.mem_toFinset.1 hv'⟩

/-- A matching is an independent set in the line graph, and its edges use `2ν` distinct
vertices, so `2ν ≤ n`. -/
theorem two_mul_indepNum_lineGraph_le_card (G : CGraph) :
    2 * (lineGraph G).indepNum ≤ Fintype.card G.V := by
  classical
  obtain ⟨S, hS, hcard⟩ := (lineGraph G).toSimple.exists_isNIndepSet_indepNum
  have hb : (S.biUnion fun e ↦ e.1.toFinset).card = ∑ e ∈ S, e.1.toFinset.card := by
    refine Finset.card_biUnion fun e he f hf hef ↦ ?_
    exact disjoint_of_not_adj_lineGraph G hef (hS (by simpa using he) (by simpa using hf) hef)
  have hsum : ∑ e ∈ S, e.1.toFinset.card = 2 * S.card := by
    rw [Finset.sum_congr rfl fun e _ ↦
      Sym2.card_toFinset_of_not_isDiag e.1 (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hle : (S.biUnion fun e ↦ e.1.toFinset).card ≤ Fintype.card G.V :=
    le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hdef : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  omega


/-! ### Matchings versus independent sets -/

/-- Every edge of `G` has an endpoint outside a given independent set. -/
theorem one_le_card_sdiff_of_isIndepSet (G : CGraph) {I : Finset G.V}
    (hI : G.toSimple.IsIndepSet (I : Set G.V)) (e : (lineGraph G).V) :
    1 ≤ (e.1.toFinset \ I).card := by
  classical
  revert e
  refine lineGraph_vertex_cases fun u v huv ↦ ?_
  have hadj : G.toSimple.Adj u v := huv
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  by_cases hu : u ∈ I
  · exact ⟨v, Finset.mem_sdiff.2 ⟨by simp, fun hv ↦
      hI (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hadj.ne hadj⟩⟩
  · exact ⟨u, Finset.mem_sdiff.2 ⟨by simp, hu⟩⟩

/-- `ν + α ≤ n`: the edges of a matching are disjoint, and each one contributes a vertex
outside a maximum independent set. -/
theorem indepNum_lineGraph_add_indepNum_le_card (G : CGraph) :
    (lineGraph G).indepNum + G.indepNum ≤ Fintype.card G.V := by
  classical
  obtain ⟨M, hM, hMcard⟩ := (lineGraph G).toSimple.exists_isNIndepSet_indepNum
  obtain ⟨I, hI, hIcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcard : (M.biUnion fun e ↦ e.1.toFinset \ I).card
      = ∑ e ∈ M, (e.1.toFinset \ I).card := by
    refine Finset.card_biUnion fun e he f hf hef ↦ ?_
    exact (disjoint_of_not_adj_lineGraph G hef
      (hM (by simpa using he) (by simpa using hf) hef)).mono
      Finset.sdiff_subset Finset.sdiff_subset
  have h1 : M.card ≤ (M.biUnion fun e ↦ e.1.toFinset \ I).card := by
    rw [hcard]
    calc M.card = ∑ _e ∈ M, 1 := by simp
      _ ≤ ∑ e ∈ M, (e.1.toFinset \ I).card :=
        Finset.sum_le_sum fun e _ ↦ one_le_card_sdiff_of_isIndepSet G hI e
  have h2 : (M.biUnion fun e ↦ e.1.toFinset \ I) ⊆ Finset.univ \ I := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨e, _, hve⟩ := hv
    rw [Finset.mem_sdiff] at hve ⊢
    exact ⟨Finset.mem_univ v, hve.2⟩
  have h3 : (Finset.univ \ I).card = Fintype.card G.V - I.card := by
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
  have h4 := Finset.card_le_card h2
  have h5 : I.card ≤ Fintype.card G.V := Finset.card_le_univ I
  have hdefM : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  have hdefI : G.indepNum = G.toSimple.indepNum := rfl
  omega


/-! ### Girth three from strong regularity -/

/-- **A strongly regular graph with `ℓ > 0` has girth three**: `k > 0` produces an edge, and
`ℓ > 0` says its two endpoints have a common neighbour, which closes a triangle. -/
@[toIsoGraph]
theorem IsSRGWith.girth_eq_three {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) (hk : 0 < k) (hℓ : 0 < ℓ) : G.girth = 3 := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hcard : Fintype.card G.V = n := h'.card
  obtain ⟨u⟩ := Fintype.card_pos_iff.1 (show 0 < Fintype.card G.V by omega)
  have hdeg : G.toSimple.degree u = k := h'.regular u
  obtain ⟨v, hv⟩ := (G.toSimple.degree_pos_iff_exists_adj u).1 (by omega)
  have hpos : 0 < Fintype.card (G.toSimple.commonNeighbors u v) := by
    rw [h'.of_adj u v hv]; exact hℓ
  obtain ⟨w, hw⟩ := Fintype.card_pos_iff.1 hpos
  exact girth_eq_three_of_triangle ((toSimple_adj _ _ _).1 hv)
    ((toSimple_adj _ _ _).1 hw.2) ((toSimple_adj _ _ _).1 hw.1.symm)

/-! ### Unmatched vertices form an independent set -/

/-- If `M` is a maximum independent set of the line graph — a maximum matching of `G` — then the
vertices it misses are pairwise non-adjacent: an edge between two of them could be added to `M`. -/
theorem isIndepSet_sdiff_biUnion {G : CGraph}
    {M : Finset (lineGraph G).V} (hM : (lineGraph G).toSimple.IsIndepSet (M : Set (lineGraph G).V))
    (hMcard : M.card = (lineGraph G).indepNum) :
    G.toSimple.IsIndepSet ((Finset.univ \ M.biUnion fun e ↦ e.1.toFinset : Finset G.V) :
      Set G.V) := by
  classical
  intro u hu v hv huv hadj
  have hu' : u ∉ M.biUnion fun e ↦ e.1.toFinset := (Finset.mem_sdiff.1 hu).2
  have hv' : v ∉ M.biUnion fun e ↦ e.1.toFinset := (Finset.mem_sdiff.1 hv).2
  set e : (lineGraph G).V := ⟨s(u, v), hadj⟩ with he
  have hnotmem : e ∉ M := by
    intro hmem
    exact hu' (Finset.mem_biUnion.2 ⟨e, hmem, Sym2.mem_toFinset.2 (Sym2.mem_mk_left u v)⟩)
  have hind : (lineGraph G).toSimple.IsIndepSet ((insert e M : Finset (lineGraph G).V) :
      Set (lineGraph G).V) := by
    intro f hf g hg hfg
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hf hg
    have key : ∀ f : (lineGraph G).V, f ∈ M → ¬ (lineGraph G).toSimple.Adj e f := by
      intro f hf hadj'
      rw [toSimple_adj, lineGraph_adj] at hadj'
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hadj'
      obtain ⟨w, hw1, hw2⟩ := hadj'.2
      have hwmem : w ∈ M.biUnion fun f ↦ f.1.toFinset :=
        Finset.mem_biUnion.2 ⟨f, hf, Sym2.mem_toFinset.2 hw2⟩
      rcases Sym2.mem_iff.1 hw1 with rfl | rfl
      · exact hu' hwmem
      · exact hv' hwmem
    rcases hf with rfl | hf
    · rcases hg with rfl | hg
      · exact absurd rfl hfg
      · exact key g hg
    · rcases hg with rfl | hg
      · exact fun h ↦ key f hf h.symm
      · exact hM hf hg hfg
  have hcard := hind.card_le_indepNum
  rw [Finset.card_insert_of_notMem hnotmem, hMcard] at hcard
  have hdefL : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  omega

/-- **Every graph has a maximum matching whose vertices dominate all the edges**, in the counting
form `|V| ≤ α(G) + 2ν(G)`. -/
theorem card_le_indepNum_add_two_mul_indepNum_lineGraph (G : CGraph) :
    Fintype.card G.V ≤ G.indepNum + 2 * (lineGraph G).indepNum := by
  classical
  obtain ⟨M, hM, hMcard⟩ := (lineGraph G).toSimple.exists_isNIndepSet_indepNum
  have hb : (M.biUnion fun e ↦ e.1.toFinset).card = ∑ e ∈ M, e.1.toFinset.card := by
    refine Finset.card_biUnion fun e he f hf hef ↦ ?_
    exact disjoint_of_not_adj_lineGraph G hef (hM (by simpa using he) (by simpa using hf) hef)
  have hsum : ∑ e ∈ M, e.1.toFinset.card = 2 * M.card := by
    rw [Finset.sum_congr rfl fun e _ ↦
      Sym2.card_toFinset_of_not_isDiag e.1 (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hle := (isIndepSet_sdiff_biUnion hM hMcard).card_le_indepNum
  have hsdiff : (Finset.univ \ M.biUnion fun e ↦ e.1.toFinset).card
      = Fintype.card G.V - (M.biUnion fun e ↦ e.1.toFinset).card := by
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
  have hsub : (M.biUnion fun e ↦ e.1.toFinset).card ≤ Fintype.card G.V :=
    le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
  have hdef : G.indepNum = G.toSimple.indepNum := rfl
  have hdefL : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  omega

/-! ### Edge colourings by hand

An edge colouring is a vertex colouring of the line graph, and the translation between the two is
pure `Sym2` bookkeeping that has no business being repeated once per graph.  The next theorem does
it once: hand it a symmetric function on *ordered* pairs of vertices which separates any two edges
at a common vertex, and it produces the bound on the chromatic number of the line graph.  Values on
non-adjacent pairs are junk and are never looked at, so the colouring can be written down as a
plain formula with no side conditions. -/

/-- An explicit proper edge colouring bounds the chromatic number of the line graph, hence the
edge chromatic number.  The colouring is a symmetric function on ordered pairs; only its values
on edges matter, so its values elsewhere are unconstrained. -/
theorem chromNum_lineGraph_le_of_edgeColouring {G : CGraph} {k : ℕ}
    (c : G.V → G.V → Fin k) (hsymm : ∀ x y, c x y = c y x)
    (hproper : ∀ u v w : G.V, G.Adj u v = true → G.Adj u w = true → v ≠ w → c u v ≠ c u w) :
    (lineGraph G).chromNum ≤ k := by
  rw [chromNum_le_iff_colorable]
  refine ⟨SimpleGraph.Coloring.mk (fun e ↦ Sym2.lift ⟨c, hsymm⟩ e.1) ?_⟩
  intro e f hef
  have hadj : (lineGraph G).Adj e f = true := hef
  rw [lineGraph_adj] at hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hadj
  obtain ⟨hne, v, hve, hvf⟩ := hadj
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hve
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.1 hvf
  have hxy : x ≠ y := fun h ↦ hne (Subtype.ext (by rw [hx, hy, h]))
  have hvx : G.Adj v x = true := by
    have h := e.2
    rw [hx, SimpleGraph.mem_edgeSet] at h
    exact h
  have hvy : G.Adj v y = true := by
    have h := f.2
    rw [hy, SimpleGraph.mem_edgeSet] at h
    exact h
  show Sym2.lift ⟨c, hsymm⟩ e.1 ≠ Sym2.lift ⟨c, hsymm⟩ f.1
  rw [hx, hy, Sym2.lift_mk, Sym2.lift_mk]
  exact hproper v x y hvx hvy hxy

/-! ### A three-edge-colouring of the ladder

The ladder `P_N □ K₂` is cubic in the middle, so three colours are the least it can hope for, and
three suffice: give every rung the third colour and alternate the other two along both rails.  A
rail edge is determined by the smaller of its two endpoints' indices, and that index's parity is
the colour. -/

/-- Three colours for the ladder: the rungs take colour `2`, and a rail edge takes the parity of
the lower of the two rungs it joins. -/
def ladderCol (N : ℕ) (p q : Fin N × Fin 2) : Fin 3 :=
  if p.1 = q.1 then 2 else if min p.1.1 q.1.1 % 2 = 0 then 0 else 1

theorem ladderCol_symm (N : ℕ) (p q : Fin N × Fin 2) : ladderCol N p q = ladderCol N q p := by
  unfold ladderCol
  rw [Nat.min_comm]
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem ladderCol_proper (N : ℕ) (u v w : (cartesianProduct (path N) (complete 2)).V)
    (huv : (cartesianProduct (path N) (complete 2)).Adj u v = true)
    (huw : (cartesianProduct (path N) (complete 2)).Adj u w = true) (hvw : v ≠ w) :
    ladderCol N u v ≠ ladderCol N u w := by
  rw [cartesianProduct_adj] at huv huw
  simp only [path, complete_adj, ofRel_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, ne_eq] at huv huw
  unfold ladderCol
  rcases huv with ⟨hv1, hv2⟩ | ⟨⟨hv1, hv2⟩, hv3⟩
  · rcases huw with ⟨hw1, hw2⟩ | ⟨⟨hw1, hw2⟩, hw3⟩
    · exfalso
      refine hvw (Prod.ext (hv1.symm.trans hw1) (Fin.ext ?_))
      have b1 := u.2.isLt
      have b2 := v.2.isLt
      have b3 := w.2.isLt
      have e1 : u.2.1 ≠ v.2.1 := fun hh ↦ hv2 (Fin.ext hh)
      have e2 : u.2.1 ≠ w.2.1 := fun hh ↦ hw2 (Fin.ext hh)
      omega
    · rw [if_pos hv1, if_neg hw1]
      split_ifs <;> decide
  · rcases huw with ⟨hw1, hw2⟩ | ⟨⟨hw1, hw2⟩, hw3⟩
    · rw [if_neg hv1, if_pos hw1]
      split_ifs <;> decide
    · rw [if_neg hv1, if_neg hw1]
      have hne : v.1.1 ≠ w.1.1 := fun h ↦
        hvw (Prod.ext (Fin.ext h) (hv3.symm.trans hw3))
      have hu := u.1.isLt
      have hv := v.1.isLt
      have hw := w.1.isLt
      have hpar : min u.1.1 v.1.1 % 2 ≠ min u.1.1 w.1.1 % 2 := by omega
      by_cases h1 : min u.1.1 v.1.1 % 2 = 0
      · rw [if_pos h1, if_neg (by omega)]
        decide
      · rw [if_neg h1, if_pos (by omega)]
        decide

/-! ### An `n`-edge-colouring of the crown

The crown `S_{n+2}^0 = K_{n+2} ⊗ K₂` is the complete bipartite graph `K_{n+2,n+2}` with a perfect
matching deleted, so it is `(n+1)`-regular and needs at least `n+1` colours.  It is also a Cayley
graph of `ℤ/(n+2)`, and the standard colouring of `K_{m,m}` by the difference of the two indices
restricts to it: the deleted matching is exactly the pairs of difference `0`, so the differences
that occur are the `n+1` nonzero ones. -/

/-- The cyclic distance from `c` up to `a`, as a natural number in `[0, N)`. -/
def crownIdx (N : ℕ) (a c : Fin N) : ℕ := if c.1 ≤ a.1 then a.1 - c.1 else a.1 + N - c.1

theorem crownIdx_lt (N : ℕ) (a c : Fin N) : crownIdx N a c < N := by
  have ha := a.isLt
  have hc := c.isLt
  unfold crownIdx
  split_ifs <;> omega

theorem crownIdx_pos (N : ℕ) {a c : Fin N} (h : a ≠ c) : 0 < crownIdx N a c := by
  have ha := a.isLt
  have hc := c.isLt
  have h' : (a : ℕ) ≠ (c : ℕ) := fun hh ↦ h (Fin.ext hh)
  unfold crownIdx
  split_ifs <;> omega

theorem crownIdx_inj (N : ℕ) (a c c' : Fin N) (h : crownIdx N a c = crownIdx N a c') : c = c' := by
  have ha := a.isLt
  have hc := c.isLt
  have hc' := c'.isLt
  refine Fin.ext ?_
  unfold crownIdx at h
  split_ifs at h <;> omega

theorem crownIdx_inj_left (N : ℕ) (a a' c : Fin N) (h : crownIdx N a c = crownIdx N a' c) :
    a = a' := by
  have ha := a.isLt
  have ha' := a'.isLt
  have hc := c.isLt
  refine Fin.ext ?_
  unfold crownIdx at h
  split_ifs at h <;> omega

/-- `n + 1` colours for the crown: the edge from `(a, 0)` to `(c, 1)` takes the cyclic difference
`a - c`, which is never zero because the difference-zero pairs are the deleted matching. -/
def crownCol (n : ℕ) (p q : Fin (n + 2) × Fin 2) : Fin (n + 1) :=
  if p.2 = q.2 then 0
  else if (p.2 : ℕ) = 0 then ⟨crownIdx (n + 2) p.1 q.1 - 1, by
      have := crownIdx_lt (n + 2) p.1 q.1; omega⟩
  else ⟨crownIdx (n + 2) q.1 p.1 - 1, by have := crownIdx_lt (n + 2) q.1 p.1; omega⟩

theorem crownCol_symm (n : ℕ) (p q : Fin (n + 2) × Fin 2) : crownCol n p q = crownCol n q p := by
  unfold crownCol
  by_cases h : p.2 = q.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hp := p.2.isLt
    have hq := q.2.isLt
    have h' : (p.2 : ℕ) ≠ (q.2 : ℕ) := fun hh ↦ h (Fin.ext hh)
    by_cases h0 : (p.2 : ℕ) = 0
    · rw [if_pos h0, if_neg (by omega)]
    · rw [if_neg h0, if_pos (by omega)]

theorem crownCol_proper (n : ℕ) (u v w : (tensorProduct (complete (n + 2)) (complete 2)).V)
    (huv : (tensorProduct (complete (n + 2)) (complete 2)).Adj u v = true)
    (huw : (tensorProduct (complete (n + 2)) (complete 2)).Adj u w = true) (hvw : v ≠ w) :
    crownCol n u v ≠ crownCol n u w := by
  rw [tensorProduct_adj] at huv huw
  simp only [complete_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at huv huw
  obtain ⟨huv1, huv2⟩ := huv
  obtain ⟨huw1, huw2⟩ := huw
  have hu2 := u.2.isLt
  have hv2 := v.2.isLt
  have hw2 := w.2.isLt
  have h2 : v.2 = w.2 := by
    refine Fin.ext ?_
    have e1 : u.2.1 ≠ v.2.1 := fun hh ↦ huv2 (Fin.ext hh)
    have e2 : u.2.1 ≠ w.2.1 := fun hh ↦ huw2 (Fin.ext hh)
    omega
  have h1 : v.1 ≠ w.1 := fun hh ↦ hvw (Prod.ext hh h2)
  unfold crownCol
  rw [if_neg huv2, if_neg huw2]
  by_cases h0 : u.2.1 = 0
  · rw [if_pos h0, if_pos h0]
    intro hcol
    have hce : crownIdx (n + 2) u.1 v.1 - 1 = crownIdx (n + 2) u.1 w.1 - 1 :=
      congrArg Fin.val hcol
    have p1 := crownIdx_pos (n + 2) huv1
    have p2 := crownIdx_pos (n + 2) huw1
    exact h1 (crownIdx_inj (n + 2) u.1 v.1 w.1 (by omega))
  · rw [if_neg h0, if_neg h0]
    intro hcol
    have hce : crownIdx (n + 2) v.1 u.1 - 1 = crownIdx (n + 2) w.1 u.1 - 1 :=
      congrArg Fin.val hcol
    have p1 := crownIdx_pos (n + 2) (Ne.symm huv1)
    have p2 := crownIdx_pos (n + 2) (Ne.symm huw1)
    exact h1 (crownIdx_inj_left (n + 2) v.1 w.1 u.1 (by omega))

/-! ### A three-edge-colouring of the prism

`Cₙ □ K₂` is cubic, so three colours is the best possible, and the graph is Hamiltonian: run along
the top rim, drop down the last rung, come back along the bottom rim and close up through the first
rung.  Alternating two colours along that cycle leaves the remaining rungs as a perfect matching for
the third colour.  The formula below does exactly that, in a shape `omega` can reason about. -/

/-- Three colours for the prism `Cₙ □ K₂`, read off a Hamiltonian cycle: go around the top rim,
drop down, come back along the bottom rim and close up.  Alternating two colours along that cycle
leaves the remaining perfect matching for the third. -/
def prismCol (N : ℕ) (p q : Fin N × Fin 2) : Fin 3 :=
  if p.1.1 = q.1.1 then
    (if p.1.1 = 0 then 1 else if p.1.1 + 1 = N then (if N % 2 = 0 then 1 else 0) else 2)
  else if (p.1.1 = 0 ∧ q.1.1 + 1 = N) ∨ (q.1.1 = 0 ∧ p.1.1 + 1 = N) then 2
  else if min p.1.1 q.1.1 % 2 = 0 then 0 else 1

theorem prismCol_symm (N : ℕ) (p q : Fin N × Fin 2) : prismCol N p q = prismCol N q p := by
  unfold prismCol
  rw [Nat.min_comm p.1.1 q.1.1]
  by_cases h : p.1.1 = q.1.1
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : (p.1.1 = 0 ∧ q.1.1 + 1 = N) ∨ (q.1.1 = 0 ∧ p.1.1 + 1 = N)
    · have h2' : (q.1.1 = 0 ∧ p.1.1 + 1 = N) ∨ (p.1.1 = 0 ∧ q.1.1 + 1 = N) := h2.symm
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬((q.1.1 = 0 ∧ p.1.1 + 1 = N) ∨ (p.1.1 = 0 ∧ q.1.1 + 1 = N)) :=
        fun hh ↦ h2 hh.symm
      rw [if_neg h2, if_neg h2']

theorem prismCol_proper (n : ℕ) (u v w : (cartesianProduct (cycle (n + 3)) (complete 2)).V)
    (huv : (cartesianProduct (cycle (n + 3)) (complete 2)).Adj u v = true)
    (huw : (cartesianProduct (cycle (n + 3)) (complete 2)).Adj u w = true) (hvw : v ≠ w) :
    prismCol (n + 3) u v ≠ prismCol (n + 3) u w := by
  rw [cartesianProduct_adj] at huv huw
  simp only [complete_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    at huv huw
  have step : ∀ x y : (cartesianProduct (cycle (n + 3)) (complete 2)).V,
      (x.1 = y.1 ∧ ¬ x.2 = y.2) ∨ ((cycle (n + 3)).Adj x.1 y.1 = true ∧ x.2 = y.2) →
      (x.1.1 = y.1.1 ∧ x.2.1 ≠ y.2.1) ∨
        ((x.1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = x.1.1 ∨ (x.1.1 = 0 ∧ y.1.1 + 1 = n + 3) ∨
          (y.1.1 = 0 ∧ x.1.1 + 1 = n + 3)) ∧ x.2.1 = y.2.1) := by
    rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨congrArg Fin.val h1, fun hh ↦ h2 (Fin.ext hh)⟩
    · refine Or.inr ⟨?_, congrArg Fin.val h2⟩
      have bx := x.1.isLt
      have by' := y.1.isLt
      rw [cycle_adj_eq_iff (by omega)] at h1
      rw [cyc_mod_succ (n + 3) x.1.1 bx, cyc_mod_pred (n + 3) x.1.1 bx] at h1
      split_ifs at h1 <;> omega
  have hv := step u v huv
  have hw := step u w huw
  have hne : v.1.1 ≠ w.1.1 ∨ v.2.1 ≠ w.2.1 := by
    by_contra hc
    push_neg at hc
    exact hvw (Prod.ext (Fin.ext hc.1) (Fin.ext hc.2))
  have bu := u.1.isLt
  have bv := v.1.isLt
  have bw := w.1.isLt
  have cu := u.2.isLt
  have cv := v.2.isLt
  have cw := w.2.isLt
  unfold prismCol
  rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
  · rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
    · exfalso; omega
    · have huw' : u.1.1 ≠ w.1.1 := by omega
      rw [if_pos hv1, if_neg huw']
      split_ifs <;> first | decide | (exfalso; omega)
  · rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
    · have huv' : u.1.1 ≠ v.1.1 := by omega
      rw [if_neg huv', if_pos hw1]
      split_ifs <;> first | decide | (exfalso; omega)
    · have huv' : u.1.1 ≠ v.1.1 := by omega
      have huw' : u.1.1 ≠ w.1.1 := by omega
      have hvw' : v.1.1 ≠ w.1.1 := by omega
      rw [if_neg huv', if_neg huw']
      split_ifs <;> first | decide | (exfalso; omega)

end CGraph
