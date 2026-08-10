import IsoGraph.Constructions

/-!
# Certificates for the invariants of a concrete graph

The invariants of `IsoGraph/Invariants.lean` are defined by quantifying over all of a graph: the
girth is an infimum over every cycle, regularity is a condition on every vertex, bipartiteness
asks for a two-colouring to exist.  For a graph given by an explicit edge list none of those is
directly checkable, and this file supplies the bridges that make them so.  Each theorem below
turns a *finite, checkable witness* into one of those statements:

* a list of vertices that closes up into a cycle bounds the girth from above
  (`girth_le_of_cycleList`), and forbids acyclicity (`not_isAcyclic_of_cycleList`);
* a neighbour table with no short closed walk in it bounds the girth from below
  (`five_le_girth_of_nbrList` up to `twelve_le_girth_of_nbrList`), by unfolding the search over
  cycles of length below the bound into nested quantifiers over the table;
* a closed walk of odd length, or a triangle, forbids a two-colouring
  (`not_isBipartite_of_odd_walk`, `not_isBipartite_of_triangle`);
* a constant degree sequence is regularity (`isRegularWith_of_degSequence`);
* a numbering of the vertices in which every vertex but the first has a neighbour of smaller
  number is connectivity (`isConnected_of_backEdge`).

The witnesses themselves are small — a list of ten vertices, a table of neighbour lists — so the
side conditions are decidable statements about concrete data.

Girth is the delicate one, and it is handled in two halves.  An upper bound needs a single cycle,
produced from a list of vertices by `exists_cycle_of_cycleList`.  A lower bound needs the absence
of every shorter cycle; `le_girth_of_forall_cycleList` reduces that to a statement about lists of
vertices, and the `_le_girth_of_nbrList` family then reduces *that* to nested membership tests in
a neighbour table, one lemma per bound because the number of nested quantifiers grows with it.
-/

set_option autoImplicit false

namespace CGraph

variable {G H : CGraph}

/-! ## Regularity from a degree sequence -/


/-- Constant neighbour counts are exactly regularity. -/
theorem isRegularOfDegree_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.toSimple.IsRegularOfDegree k := fun v ↦ by
  rw [SimpleGraph.degree, neighborFinset_eq_nbrs, h]

theorem card_nbrs_eq_degree (G : CGraph) (v : G.V) : (G.nbrs v).card = G.toSimple.degree v := by
  rw [SimpleGraph.degree, neighborFinset_eq_nbrs]

/-- A constant degree sequence gives back the degree of every vertex. -/
theorem card_nbrs_of_degSequence {n k : ℕ} (h : G.degSequence = List.replicate n k) (v : G.V) :
    (G.nbrs v).card = k := by
  have hm : G.toSimple.degree v ∈ G.degSequence := by
    rw [degSequence, degMultiset, Multiset.mem_sort, Multiset.mem_map]
    exact ⟨v, Finset.mem_univ_val v, rfl⟩
  rw [h, List.mem_replicate] at hm
  rw [card_nbrs_eq_degree, hm.2]

/-- Constant neighbour counts are exactly regularity. -/
theorem isRegularWith_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.IsRegularWith k := isRegularOfDegree_of_card_nbrs G h

/-- A constant degree sequence is exactly regularity; this is the bridge that turns the whole
`degSequence` table into a table of regular graphs. -/
theorem isRegularWith_of_degSequence {G : CGraph} {n k : ℕ}
    (h : G.degSequence = List.replicate n k) : G.IsRegularWith k :=
  isRegularWith_of_card_nbrs G fun v ↦ card_nbrs_of_degSequence h v

/-! ## Connectivity -/

/-- **A back edge from every vertex but the first gives connectivity.**  If the vertices are
numbered by `e` so that each vertex other than number zero has a neighbour with a strictly smaller
number, then the graph is connected: induction on the number walks any vertex down to the first.

The hypothesis is decidable and cheap — `n²` adjacency queries — whereas deciding
`SimpleGraph.Connected` directly is not usable at these sizes. -/
theorem isConnected_of_backEdge {n : ℕ} {G : CGraph} (e : G.V ≃ Fin n) (hn : 0 < n)
    (h : ∀ v : G.V, 0 < (e v).1 → ∃ w : G.V, (e w).1 < (e v).1 ∧ G.Adj v w) : G.IsConnected := by
  have key : ∀ m : ℕ, ∀ x : G.V, (e x).1 = m → G.toSimple.Reachable x (e.symm ⟨0, hn⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hxe : x = e.symm ⟨0, hn⟩ := by
          rw [← e.symm_apply_apply x]; congr 1; exact Fin.ext hx
        exact hxe ▸ SimpleGraph.Reachable.refl _
      · obtain ⟨w, hlt, hadj⟩ := h x (by omega)
        exact (SimpleGraph.Adj.reachable ((toSimple_adj _ _ _).2 hadj)).trans
          (ih (e w).1 (by omega) w rfl)
  have : Nonempty G.V := ⟨e.symm ⟨0, hn⟩⟩
  exact ⟨fun u v ↦ (key _ u rfl).trans (key _ v rfl).symm⟩

/-! ## Bipartiteness -/

/-- **A graph with a triangle in it is not bipartite**: three mutually adjacent vertices need
three colours. -/
theorem not_isBipartite_of_triangle {G : CGraph} {a b d : G.V} (hab : G.Adj a b)
    (had : G.Adj a d) (hbd : G.Adj b d) : ¬ G.IsBipartite := by
  rintro ⟨c, hc⟩
  have h1 := hc a b hab
  have h2 := hc a d had
  refine hc b d hbd ?_
  revert h1 h2
  cases c a <;> cases c b <;> cases c d <;> simp

/-! ### Odd closed walks -/

/-- **A closed walk of odd length forbids a two-colouring.**  Walking along `f` the colour
alternates with the parity of the step count, so returning to the start after an odd number of
steps is impossible. -/
theorem not_isBipartite_of_odd_walk {G : CGraph} (f : ℕ → G.V) (m : ℕ) (hodd : m % 2 = 1)
    (h : ∀ k < m, G.Adj (f k) (f (k + 1))) (hclose : f m = f 0) : ¬ G.IsBipartite := by
  rintro ⟨c, hc⟩
  have alt : ∀ k ≤ m, c (f k) = xor (c (f 0)) (decide (k % 2 = 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hstep := hc (f k) (f (k + 1)) (h k (by omega))
      rw [ih (by omega)] at hstep
      have hpar : (decide ((k + 1) % 2 = 1)) = !(decide (k % 2 = 1)) := by
        rcases Nat.mod_two_eq_zero_or_one k with h' | h' <;> simp [Nat.add_mod, h']
      rw [hpar]
      revert hstep
      rcases c (f (k + 1)) <;> rcases c (f 0) <;> rcases (decide (k % 2 = 1)) <;> simp
  have hm := alt m le_rfl
  rw [hclose, hodd] at hm
  simp at hm

/-- The closed walk on `Fin N` that runs round the list `vs` of vertex numbers.  Paired with
`not_isBipartite_of_odd_walk`, an odd `vs` witnesses that a graph is not bipartite. -/
def walkOn (N : ℕ) (hN : 0 < N) (vs : List ℕ) (k : ℕ) : Fin N :=
  ⟨vs.getD (k % vs.length) 0 % N, Nat.mod_lt _ hN⟩

/-! ### The Mycielskian -/

/-- **The Mycielskian of a graph with an edge is not bipartite.**  An edge `a – b` of `G` closes up
into a pentagon `a – b – a' – w – b' – a` through the two shadows and the apex.  Concretely: `a'`
and `b'` are forced to copy the colours of `a` and `b`, which differ, and the apex is adjacent to
both. -/
theorem not_isBipartite_mycielskian {G : CGraph} [DecidableEq G.V] {a b : G.V} (hab : G.Adj a b) :
    ¬ (mycielskian G).IsBipartite := by
  rintro ⟨c, hc⟩
  have h1 := hc (some (.inl a)) (some (.inl b)) hab
  have h2 := hc (some (.inr a)) (some (.inl b)) hab
  have h3 := hc (some (.inl a)) (some (.inr b)) hab
  have h4 := hc none (some (.inr a)) rfl
  have h5 := hc none (some (.inr b)) rfl
  revert h1 h2 h3 h4 h5
  cases c none <;> cases c (some (.inl a)) <;> cases c (some (.inl b)) <;>
    cases c (some (.inr a)) <;> cases c (some (.inr b)) <;> simp

/-- **The Mycielskian of a graph without isolated vertices is connected.**  The apex sees every
shadow, and every shadow sees the neighbours of the vertex it shadows. -/
theorem isConnected_mycielskian {G : CGraph} [DecidableEq G.V] (h : ∀ v : G.V, ∃ w, G.Adj v w) :
    (mycielskian G).IsConnected := by
  have hapex : ∀ a : G.V, (mycielskian G).toSimple.Adj none (some (Sum.inr a)) := fun a ↦
    (toSimple_adj (mycielskian G) none (some (Sum.inr a))).2 rfl
  have hnone : ∀ x : (mycielskian G).V, (mycielskian G).toSimple.Reachable none x := by
    rintro (_ | (a | a))
    · exact .refl _
    · obtain ⟨w, hw⟩ := h a
      have hwa : (mycielskian G).toSimple.Adj (some (Sum.inr w)) (some (Sum.inl a)) :=
        (toSimple_adj (mycielskian G) (some (Sum.inr w)) (some (Sum.inl a))).2
          ((G.symm w a).trans hw)
      exact (hapex w).reachable.trans hwa.reachable
    · exact (hapex a).reachable
  have : Nonempty (mycielskian G).V := ⟨none⟩
  exact ⟨fun u v ↦ (hnone u).symm.trans (hnone v)⟩

/-! ## Girth -/

theorem girth_eq_zero_iff (G : CGraph) : G.girth = 0 ↔ G.IsAcyclic :=
  SimpleGraph.girth_eq_zero

theorem three_le_girth {G : CGraph} (h : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  SimpleGraph.three_le_girth h

theorem girth_le_length {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a} (h : w.IsCycle) :
    G.girth ≤ w.length :=
  SimpleGraph.girth_le_length h

theorem not_isAcyclic_of_isCycle {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a}
    (h : w.IsCycle) : ¬ G.IsAcyclic := fun hac ↦ hac w h

/-- Three mutually adjacent vertices are a shortest possible cycle. -/
theorem exists_cycle_of_triangle {G : CGraph} {a b c : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) :
    ∃ (x : G.V) (w : G.toSimple.Walk x x), w.IsCycle ∧ w.length = 3 := by
  have hab' : G.toSimple.Adj a b := (toSimple_adj G a b).2 hab
  have hbc' : G.toSimple.Adj b c := (toSimple_adj G b c).2 hbc
  have hca' : G.toSimple.Adj c a := (toSimple_adj G c a).2 hca
  have hcyc : (SimpleGraph.Walk.cons hab' (.cons hbc' (.cons hca' .nil))).IsCycle := by
    have h1 := hab'.ne
    have h2 := hbc'.ne
    have h3 := hca'.ne
    simp [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def, h1, h2, h3,
      h1.symm, h3.symm]
  exact ⟨a, _, hcyc, by simp⟩

theorem not_isAcyclic_of_triangle {G : CGraph} {a b c : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) : ¬ G.IsAcyclic := by
  obtain ⟨_, _, hw, _⟩ := exists_cycle_of_triangle hab hbc hca
  exact not_isAcyclic_of_isCycle hw

theorem girth_eq_three_of_triangle {G : CGraph} {a b c : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) : G.girth = 3 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_triangle hab hbc hca
  exact le_antisymm (hl ▸ girth_le_length hw) (three_le_girth (not_isAcyclic_of_isCycle hw))

/-- A cycle of length three is a triangle: this is the shape a shortest cycle takes. -/
theorem exists_triangle_of_girth_eq_three {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a}
    (hw : w.IsCycle) (hl : w.length = 3) :
    ∃ x y z : G.V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x := by
  cases w with
  | nil => simp at hl
  | cons hab w1 =>
    cases w1 with
    | nil => simp at hl
    | cons hbc w2 =>
      cases w2 with
      | nil => simp at hl
      | cons hca w3 =>
        cases w3 with
        | cons _ _ => simp at hl
        | nil =>
          exact ⟨_, _, _, (toSimple_adj _ _ _).1 hab, (toSimple_adj _ _ _).1 hbc,
            (toSimple_adj _ _ _).1 hca⟩

/-- **A triangle-free graph with a cycle has girth at least four.** -/
theorem four_le_girth {G : CGraph}
    (htri : ∀ x y z : G.V, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hnac : ¬ G.IsAcyclic) : 4 ≤ G.girth := by
  have hle : (4 : ℕ∞) ≤ G.toSimple.egirth := by
    refine SimpleGraph.le_egirth.2 fun a w hw ↦ ?_
    have h3 := hw.three_le_length
    rcases Nat.lt_or_ge w.length 4 with hlt | hge
    · obtain ⟨x, y, z, h1, h2, h3⟩ := exists_triangle_of_girth_eq_three hw (by omega)
      exact absurd (htri x y z h1 h2 h3) not_false
    · exact_mod_cast hge
  exact ENat.toNat_le_toNat hle (SimpleGraph.egirth_eq_top.not.2 hnac)

/-- Four vertices in a square give a cycle of length four. -/
theorem exists_cycle_of_square {G : CGraph} {a b c d : G.V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) :
    ∃ (x : G.V) (w : G.toSimple.Walk x x), w.IsCycle ∧ w.length = 4 := by
  have hab' : G.toSimple.Adj a b := (toSimple_adj G a b).2 hab
  have hbc' : G.toSimple.Adj b c := (toSimple_adj G b c).2 hbc
  have hcd' : G.toSimple.Adj c d := (toSimple_adj G c d).2 hcd
  have hda' : G.toSimple.Adj d a := (toSimple_adj G d a).2 hda
  have hcyc : (SimpleGraph.Walk.cons hab' (.cons hbc' (.cons hcd' (.cons hda' .nil)))).IsCycle := by
    have h1 := hab'.ne
    have h2 := hbc'.ne
    have h3 := hcd'.ne
    have h4 := hda'.ne
    simp [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def, h1, h2, h3, h4,
      h1.symm, h4.symm, hac, hac.symm, hbd]
  exact ⟨a, _, hcyc, by simp⟩

theorem not_isAcyclic_of_square {G : CGraph} {a b c d : G.V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : ¬ G.IsAcyclic := by
  obtain ⟨_, _, hw, _⟩ := exists_cycle_of_square hab hbc hcd hda hac hbd
  exact not_isAcyclic_of_isCycle hw

theorem girth_le_four_of_square {G : CGraph} {a b c d : G.V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : G.girth ≤ 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square hab hbc hcd hda hac hbd
  exact hl ▸ girth_le_length hw

/-- A cycle of length four is a square. -/
theorem exists_square_of_length_four {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a}
    (hw : w.IsCycle) (hl : w.length = 4) :
    ∃ x y z t : G.V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z t ∧ G.Adj t x ∧ x ≠ z ∧ y ≠ t := by
  cases w with
  | nil => simp at hl
  | cons hab w1 =>
    cases w1 with
    | nil => simp at hl
    | cons hbc w2 =>
      cases w2 with
      | nil => simp at hl
      | cons hcd w3 =>
        cases w3 with
        | nil => simp at hl
        | cons hda w4 =>
          cases w4 with
          | cons _ _ => simp at hl
          | nil =>
            have hnd := hw.support_nodup
            simp [SimpleGraph.Walk.support] at hnd
            exact ⟨_, _, _, _, (toSimple_adj _ _ _).1 hab, (toSimple_adj _ _ _).1 hbc,
              (toSimple_adj _ _ _).1 hcd, (toSimple_adj _ _ _).1 hda,
              fun h ↦ hnd.2.1.2 h.symm, hnd.1.2.1⟩

/-- **A graph with no triangle and no square, but with a cycle, has girth at least five.** -/
theorem five_le_girth {G : CGraph}
    (htri : ∀ x y z : G.V, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hsq : ∀ x y z t : G.V, G.Adj x y → G.Adj y z → G.Adj z t → G.Adj t x → x = z ∨ y = t)
    (hnac : ¬ G.IsAcyclic) : 5 ≤ G.girth := by
  have hle : (5 : ℕ∞) ≤ G.toSimple.egirth := by
    refine SimpleGraph.le_egirth.2 fun a w hw ↦ ?_
    have h3 := hw.three_le_length
    rcases Nat.lt_or_ge w.length 5 with hlt | hge
    · interval_cases h : w.length
      · obtain ⟨x, y, z, h1, h2, h3⟩ := exists_triangle_of_girth_eq_three hw h
        exact absurd (htri x y z h1 h2 h3) not_false
      · obtain ⟨x, y, z, t, h1, h2, h3, h4, hxz, hyt⟩ := exists_square_of_length_four hw h
        rcases hsq x y z t h1 h2 h3 h4 with h | h
        · exact absurd h hxz
        · exact absurd h hyt
    · exact_mod_cast hge
  exact ENat.toNat_le_toNat hle (SimpleGraph.egirth_eq_top.not.2 hnac)

/-- **A bipartite graph with a cycle has girth at least four.** -/
theorem four_le_girth_of_isBipartite {G : CGraph} (hb : G.IsBipartite) (hnac : ¬ G.IsAcyclic) :
    4 ≤ G.girth :=
  four_le_girth (fun x _ z h1 h2 h3 ↦
    not_isBipartite_of_triangle h1 ((G.symm x z).trans h3) h2 hb) hnac


/-- Five vertices in a pentagon give a cycle of length five. -/
theorem exists_cycle_of_pentagon {G : CGraph} {a b c d e : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) (hac : a ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e) (hce : c ≠ e) :
    ∃ (x : G.V) (w : G.toSimple.Walk x x), w.IsCycle ∧ w.length = 5 := by
  have hab' : G.toSimple.Adj a b := (toSimple_adj G a b).2 hab
  have hbc' : G.toSimple.Adj b c := (toSimple_adj G b c).2 hbc
  have hcd' : G.toSimple.Adj c d := (toSimple_adj G c d).2 hcd
  have hde' : G.toSimple.Adj d e := (toSimple_adj G d e).2 hde
  have hea' : G.toSimple.Adj e a := (toSimple_adj G e a).2 hea
  have hcyc :
      (SimpleGraph.Walk.cons hab' (.cons hbc' (.cons hcd' (.cons hde' (.cons hea' .nil))))).IsCycle := by
    have h1 := hab'.ne
    have h2 := hbc'.ne
    have h3 := hcd'.ne
    have h4 := hde'.ne
    have h5 := hea'.ne
    simp [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def, h1, h2, h3, h4, h5,
      h1.symm, h5.symm, hac, hac.symm, had, had.symm, hbd, hbe, hce]
  exact ⟨a, _, hcyc, by simp⟩

theorem not_isAcyclic_of_pentagon {G : CGraph} {a b c d e : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) (hac : a ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e) (hce : c ≠ e) : ¬ G.IsAcyclic := by
  obtain ⟨_, _, hw, _⟩ := exists_cycle_of_pentagon hab hbc hcd hde hea hac had hbd hbe hce
  exact not_isAcyclic_of_isCycle hw

theorem girth_le_five_of_pentagon {G : CGraph} {a b c d e : G.V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) (hac : a ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e) (hce : c ≠ e) : G.girth ≤ 5 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_pentagon hab hbc hcd hde hea hac had hbd hbe hce
  exact hl ▸ girth_le_length hw
/-! ## Cycles as lists of vertices

The girth ladder above stops at five, one hand-written rung per length.  A *cycle list* states
the same thing once, at every length: a list `u :: vs` of distinct vertices, consecutive ones
adjacent, with the last adjacent back to `u`.  `exists_cycleList_of_isCycle` reads one off a
cycle, `exists_cycle_of_cycleList` builds the cycle back up, and `le_girth_of_forall_cycleList`
is the lower bound.  With a precomputed neighbour table (`nbrTable`) the hypotheses of
`six_le_girth_of_nbrList` and friends are one `native_decide` each, which is how the cubic cages
of `IsoGraph/NamedGraphs.lean` get their girth. -/

theorem getLastD_support {V : Type} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (x : V) :
    p.support.getLastD x = v := by
  induction p generalizing x with
  | nil => rfl
  | cons h q ih => rw [SimpleGraph.Walk.support_cons, List.getLastD_cons]; exact ih _

theorem exists_cycleList_of_isCycle {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a}
    (hw : w.IsCycle) :
    ∃ (u : G.V) (vs : List G.V), vs.length + 1 = w.length ∧ (u :: vs).Nodup ∧
      List.IsChain (fun x y ↦ G.Adj x y) (u :: vs) ∧ G.Adj (vs.getLastD u) u := by
  cases w with
  | nil => exact absurd rfl hw.ne_nil
  | @cons _ b _ h p =>
    refine ⟨b, p.support.tail, ?_, ?_, ?_, ?_⟩
    · simp [SimpleGraph.Walk.length_support]
    · rw [← SimpleGraph.Walk.support_eq_cons]
      simpa using hw.support_nodup
    · rw [← SimpleGraph.Walk.support_eq_cons]
      exact p.isChain_adj_support
    · have hl : p.support.getLastD b = a := getLastD_support p b
      rw [SimpleGraph.Walk.support_eq_cons p, List.getLastD_cons] at hl
      rw [hl]
      exact h

/-- A chain of adjacencies is a walk. -/
theorem exists_walk_of_isChain {G : CGraph} : ∀ (u : G.V) (vs : List G.V),
    List.IsChain (fun x y ↦ G.Adj x y) (u :: vs) →
    ∃ p : G.toSimple.Walk u (vs.getLastD u), p.support = u :: vs := by
  intro u vs
  induction vs generalizing u with
  | nil => exact fun _ ↦ ⟨.nil, rfl⟩
  | cons b t ih =>
    intro hch
    obtain ⟨hub, hch'⟩ := List.isChain_cons_cons.1 hch
    obtain ⟨q, hq⟩ := ih b hch'
    rw [List.getLastD_cons]
    refine ⟨.cons ((toSimple_adj G u b).2 hub) q, ?_⟩
    rw [SimpleGraph.Walk.support_cons, hq]

/-- In a path of length at least two, the two endpoints are not joined by an edge of the path. -/
theorem not_mem_edges_of_isPath {V : Type} {G : SimpleGraph V} {u v : V} :
    ∀ (p : G.Walk u v), p.IsPath → 2 ≤ p.length → s(u, v) ∉ p.edges := by
  intro p
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    intro hp hlen hmem
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · have hbc : b = c := by
        rcases Sym2.eq_iff.1 heq with ⟨_, hbc⟩ | ⟨hac, _⟩
        · exact hbc.symm
        · exact absurd hac h.ne
      subst hbc
      rw [SimpleGraph.Walk.isPath_iff_eq_nil] at hp
      simp [hp.1] at hlen
    · exact hp.2 (q.fst_mem_support_of_mem_edges hmem)

/-- **A list of vertices, read back as a cycle.** -/
theorem exists_cycle_of_cycleList {G : CGraph} (u : G.V) (vs : List G.V)
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u) :
    ∃ (x : G.V) (w : G.toSimple.Walk x x), w.IsCycle ∧ w.length = vs.length + 1 := by
  obtain ⟨p, hp⟩ := exists_walk_of_isChain u vs hch
  have hpath : p.IsPath := SimpleGraph.Walk.IsPath.mk' (hp ▸ hnd)
  have hlen : p.length = vs.length := by
    have hs := SimpleGraph.Walk.length_support p
    rw [hp] at hs
    simpa using hs.symm
  have hadj : G.toSimple.Adj u (vs.getLastD u) := ((toSimple_adj G _ u).2 hcl).symm
  refine ⟨u, .cons hadj p.reverse, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
    exact not_mem_edges_of_isPath p hpath (by omega)
  · simp [hlen]

/-- A cycle list of length `n` bounds the girth by `n`. -/
theorem girth_le_of_cycleList {G : CGraph} (u : G.V) (vs : List G.V)
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u) :
    G.girth ≤ vs.length + 1 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_cycleList u vs h2 hnd hch hcl
  exact hl ▸ girth_le_length hw

/-- A graph with a cycle list is not acyclic. -/
theorem not_isAcyclic_of_cycleList {G : CGraph} (u : G.V) (vs : List G.V)
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u) :
    ¬ G.IsAcyclic := by
  obtain ⟨_, _, hw, _⟩ := exists_cycle_of_cycleList u vs h2 hnd hch hcl
  exact not_isAcyclic_of_isCycle hw

/-- **A graph with a cycle but no short cycle list has large girth.** -/
theorem le_girth_of_forall_cycleList {G : CGraph} {L : ℕ}
    (h : ∀ (u : G.V) (vs : List G.V), 2 ≤ vs.length → vs.length + 1 < L → (u :: vs).Nodup →
      List.IsChain (fun x y ↦ G.Adj x y) (u :: vs) → G.Adj (vs.getLastD u) u → False)
    (hnac : ¬ G.IsAcyclic) : L ≤ G.girth := by
  have hle : (L : ℕ∞) ≤ G.toSimple.egirth := by
    refine SimpleGraph.le_egirth.2 fun a w hw ↦ ?_
    rcases Nat.lt_or_ge w.length L with hlt | hge
    · obtain ⟨u, vs, hlen, hnd, hch, hcl⟩ := exists_cycleList_of_isCycle hw
      have h3 := hw.three_le_length
      exact absurd (h u vs (by omega) (by omega) hnd hch hcl) not_false
    · exact_mod_cast hge
  exact ENat.toNat_le_toNat hle (SimpleGraph.egirth_eq_top.not.2 hnac)

/-- The third entry of a list without duplicates differs from the first. -/
theorem ne_of_nodup_cons₂ {α : Type*} {x y z : α} {l : List α}
    (h : (x :: y :: z :: l).Nodup) : z ≠ x := by
  rintro rfl
  exact (List.nodup_cons.1 h).1 (by simp)

/-- A member of a list that differs from `y` is still a member after `y` is erased.  This is
`List.mem_erase_of_ne` with the arguments in the order the girth wrappers below need them. -/
theorem mem_erase_of_ne_of_mem {α : Type*} [DecidableEq α] {x y : α} {l : List α} (hne : x ≠ y)
    (hx : x ∈ l) : x ∈ l.erase y :=
  (List.mem_erase_of_ne hne).2 hx

/-- **Girth at least five** from a neighbour list, as `six_le_girth_of_nbrList` at length
five. -/
theorem five_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (hnac : ¬ G.IsAcyclic) : 5 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least six from a neighbour list.**  `nb` is a list of neighbours of each vertex —
in practice a precomputed table, which is what makes the search below cheap — and the hypotheses
say that no closed walk of three, four or five steps along it has distinct vertices.  A graph with
a cycle and no such short cycle has girth at least six.

Each step after the first erases the previous vertex from the neighbour list, which is sound
because the walk is required to have distinct vertices and cuts the branching factor of the search
from the degree to the degree minus one — a factor of two per step on a cubic graph, which is the
difference between minutes and hours at the lengths the cages below need. -/
theorem six_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (hnac : ¬ G.IsAcyclic) : 6 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least seven** from a neighbour list, as `six_le_girth_of_nbrList` at length
seven. -/
theorem seven_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (hnac : ¬ G.IsAcyclic) : 7 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, t⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least eight** from a neighbour list, as `six_le_girth_of_nbrList` at length
eight. -/
theorem eight_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (h7 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e,
      ¬ (a ∈ nb g ∧ [a, b, c, d, e, f, g].Nodup))
    (hnac : ¬ G.IsAcyclic) : 8 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, t⟩⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h7 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least nine** from a neighbour list, as `six_le_girth_of_nbrList` at length
nine. -/
theorem nine_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (h7 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e,
      ¬ (a ∈ nb g ∧ [a, b, c, d, e, f, g].Nodup))
    (h8 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f,
      ¬ (a ∈ nb h ∧ [a, b, c, d, e, f, g, h].Nodup))
    (hnac : ¬ G.IsAcyclic) : 9 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, t⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h7 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h8 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least ten** from a neighbour list, as `six_le_girth_of_nbrList` at length
ten. -/
theorem ten_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (h7 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e,
      ¬ (a ∈ nb g ∧ [a, b, c, d, e, f, g].Nodup))
    (h8 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f,
      ¬ (a ∈ nb h ∧ [a, b, c, d, e, f, g, h].Nodup))
    (h9 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g,
      ¬ (a ∈ nb i ∧ [a, b, c, d, e, f, g, h, i].Nodup))
    (hnac : ¬ G.IsAcyclic) : 10 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, t⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h7 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h8 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h9 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2)) ⟨(hnb _
      _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least eleven** from a neighbour list, as `six_le_girth_of_nbrList` at length
eleven. -/
theorem eleven_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (h7 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e,
      ¬ (a ∈ nb g ∧ [a, b, c, d, e, f, g].Nodup))
    (h8 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f,
      ¬ (a ∈ nb h ∧ [a, b, c, d, e, f, g, h].Nodup))
    (h9 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g,
      ¬ (a ∈ nb i ∧ [a, b, c, d, e, f, g, h, i].Nodup))
    (h10 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ∀ f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g, ∀ j ∈
      (nb i).erase h,
      ¬ (a ∈ nb j ∧ [a, b, c, d, e, f, g, h, i, j].Nodup))
    (hnac : ¬ G.IsAcyclic) : 11 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k,
    t⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h7 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h8 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h9 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2)) ⟨(hnb _
      _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h10 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2.1)) j
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- **Girth at least twelve** from a neighbour list, as `six_le_girth_of_nbrList` at length
twelve. -/
theorem twelve_le_girth_of_nbrList {G : CGraph} [DecidableEq G.V]
    {nb : G.V → List G.V} (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h3 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a,
      ¬ (a ∈ nb c ∧ [a, b, c].Nodup))
    (h4 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b,
      ¬ (a ∈ nb d ∧ [a, b, c, d].Nodup))
    (h5 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ¬ (a ∈ nb e ∧ [a, b, c, d, e].Nodup))
    (h6 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d,
      ¬ (a ∈ nb f ∧ [a, b, c, d, e, f].Nodup))
    (h7 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e,
      ¬ (a ∈ nb g ∧ [a, b, c, d, e, f, g].Nodup))
    (h8 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f,
      ¬ (a ∈ nb h ∧ [a, b, c, d, e, f, g, h].Nodup))
    (h9 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c, ∀
      f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g,
      ¬ (a ∈ nb i ∧ [a, b, c, d, e, f, g, h, i].Nodup))
    (h10 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ∀ f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g, ∀ j ∈
      (nb i).erase h,
      ¬ (a ∈ nb j ∧ [a, b, c, d, e, f, g, h, i, j].Nodup))
    (h11 : ∀ a : G.V, ∀ b ∈ nb a, ∀ c ∈ (nb b).erase a, ∀ d ∈ (nb c).erase b, ∀ e ∈ (nb d).erase c,
      ∀ f ∈ (nb e).erase d, ∀ g ∈ (nb f).erase e, ∀ h ∈ (nb g).erase f, ∀ i ∈ (nb h).erase g, ∀ j ∈
      (nb i).erase h, ∀ k ∈ (nb j).erase i,
      ¬ (a ∈ nb k ∧ [a, b, c, d, e, f, g, h, i, j, k].Nodup))
    (hnac : ¬ G.IsAcyclic) : 12 ≤ G.girth := by
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨j, _ | ⟨k, _ |
    ⟨l, t⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h3 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h4 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h5 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2)) ⟨(hnb
      _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h6 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h7 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h8 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2))
      ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h9 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2)) ⟨(hnb _
      _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h10 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2.1)) j
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    exact h11 u b ((hnb _ _).2 hch.1) c (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd) ((hnb _ _).2
      hch.2.1)) d (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons) ((hnb _ _).2 hch.2.2.1)) e
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.1)) f
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.1)) g (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.1)) h (mem_erase_of_ne_of_mem
      (ne_of_nodup_cons₂ hnd.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.1)) i (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2 hch.2.2.2.2.2.2.2.1)) j
      (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.2.2.1)) k (mem_erase_of_ne_of_mem (ne_of_nodup_cons₂
      hnd.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons) ((hnb _ _).2
      hch.2.2.2.2.2.2.2.2.2)) ⟨(hnb _ _).2 hcl, hnd⟩
  · simp only [List.length_cons] at hlt
    omega

/-- The neighbour lists of every vertex in `l`, as a table indexed by position in `l`. -/
def nbrTable (G : CGraph) (l : List G.V) : List (List G.V) :=
  l.map fun a ↦ l.filter fun b ↦ G.Adj a b

end CGraph
