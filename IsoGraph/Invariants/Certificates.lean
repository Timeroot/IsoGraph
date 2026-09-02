import IsoGraph.Core.Defs
import IsoGraph.ForMathlib.List
import IsoGraph.ForMathlib.SimpleGraph

/-!
# Certificates for the invariants of a concrete graph

The invariants of `IsoGraph/Invariants/Basic.lean` are defined by quantifying over all of a graph:
the girth is an infimum over every cycle, regularity is a condition on every vertex, bipartiteness
asks for a two-colouring to exist.  For a graph given by an explicit edge list none of those is
directly checkable, and this file supplies the bridges that make them so.  Each theorem below
turns a *finite, checkable witness* into one of those statements:

* a list of vertices that closes up into a cycle bounds the girth from above
  (`girth_le_of_cycleList`), and forbids acyclicity (`not_isAcyclic_of_cycleList`);
* a neighbour table with no short closed walk in it bounds the girth from below
  (`le_girth_of_nbrList`), by searching the table for one;
* a closed walk of odd length, or a triangle, forbids a two-colouring
  (`not_isBipartite_of_odd_walk`, `not_isBipartite_of_triangle`);
* a constant degree sequence is regularity (`isRegularWith_of_degSequence`);
* a numbering of the vertices in which every vertex but the first has a neighbour of smaller
  number is connectivity (`isConnected_of_backEdge`), and for a graph whose numbering does not
  oblige, the order a breadth-first search finds the vertices in does just as well
  (`isConnected_of_bfsOrder`); both are the same descent argument (`isConnected_of_rank`).

The witnesses themselves are small — a list of ten vertices, a table of neighbour lists — so the
side conditions are decidable statements about concrete data.

Girth is the delicate one, and it is handled in two halves.  An upper bound needs a single cycle,
produced from a list of vertices by `exists_cycle_of_cycleList`.  A lower bound needs the absence
of every shorter cycle; `le_girth_of_forall_cycleList` reduces that to a statement about lists of
vertices, and `le_girth_of_nbrList` reduces *that* to `cycleSearch`, a depth-first search of a
neighbour table that a single `native_decide` runs to exhaustion.
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
@[toIsoGraph]
theorem isRegularWith_of_degSequence {G : CGraph} {n k : ℕ}
    (h : G.degSequence = List.replicate n k) : G.IsRegularWith k :=
  isRegularWith_of_card_nbrs G fun v ↦ card_nbrs_of_degSequence h v

/-! ## Connectivity -/

/-- **Descent to a root gives connectivity.**  If every vertex but one has a neighbour of strictly
smaller rank, then the graph is connected: strong induction on the rank walks any vertex down to
the root, and two vertices meet there.

Nothing is asked of the rank function beyond the descent itself, so any computable function will
do — the numbering of the vertices in `isConnected_of_backEdge`, or the order a search finds them
in as in `isConnected_of_bfsOrder`. -/
theorem isConnected_of_rank {G : CGraph} (r : G.V → ℕ) (v₀ : G.V)
    (h : ∀ v : G.V, v ≠ v₀ → ∃ w : G.V, r w < r v ∧ G.Adj v w) : G.IsConnected := by
  have key : ∀ m : ℕ, ∀ x : G.V, r x = m → G.toSimple.Reachable x v₀ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx
      by_cases hx0 : x = v₀
      · exact hx0 ▸ SimpleGraph.Reachable.refl _
      · obtain ⟨w, hlt, hadj⟩ := h x hx0
        exact (SimpleGraph.Adj.reachable ((toSimple_adj _ _ _).2 hadj)).trans
          (ih (r w) (hx ▸ hlt) w rfl)
  have : Nonempty G.V := ⟨v₀⟩
  exact ⟨fun u v ↦ (key _ u rfl).trans (key _ v rfl).symm⟩

/-- **A back edge from every vertex but the first gives connectivity.**  If the vertices are
numbered by `e` so that each vertex other than number zero has a neighbour with a strictly smaller
number, then the graph is connected: the number is a rank in the sense of `isConnected_of_rank`.

The hypothesis is decidable and cheap — `n²` adjacency queries — whereas deciding
`SimpleGraph.Connected` directly is not usable at these sizes. -/
theorem isConnected_of_backEdge {n : ℕ} {G : CGraph} (e : G.V ≃ Fin n) (hn : 0 < n)
    (h : ∀ v : G.V, 0 < (e v).1 → ∃ w : G.V, (e w).1 < (e v).1 ∧ G.Adj v w) : G.IsConnected :=
  isConnected_of_rank (fun v ↦ (e v).1) (e.symm ⟨0, hn⟩) fun v hv ↦ h v <| by
    rcases Nat.eq_zero_or_pos (e v).1 with h0 | h0
    · refine absurd ?_ hv
      rw [← e.symm_apply_apply v]
      congr 1
      exact Fin.ext h0
    · exact h0

/-- One round of a breadth-first search through `vs`: the vertices already seen, followed by those
not yet seen that have a seen neighbour.  The search stops when a round finds nothing new, so the
`k` rounds allowed are only an upper bound. -/
def bfsAux (G : CGraph) (vs : List G.V) : ℕ → List G.V → List G.V
  | 0, seen => seen
  | k + 1, seen =>
    let new := vs.filter fun v ↦ !seen.contains v && seen.any fun u ↦ G.Adj u v
    if new.isEmpty then seen else bfsAux G vs k (seen ++ new)

/-- The vertices of `vs` in the order a breadth-first search from `v₀` reaches them.  Vertices in
another component are simply absent from the list. -/
def bfsOrder (G : CGraph) (vs : List G.V) (v₀ : G.V) : List G.V :=
  bfsAux G vs vs.length [v₀]

/-- **Search order is a certificate of connectivity.**  If every vertex but `v₀` has a neighbour
that comes earlier in the list `l`, the graph is connected — position in `l` is a rank.

The list to pass is `G.bfsOrder`, which is exactly the order a breadth-first search from `v₀`
finds the vertices in, and which therefore satisfies the hypothesis as soon as the graph is
connected at all.  Unlike `isConnected_of_backEdge` this asks nothing of how the vertices are
numbered, which matters for the graphs that are *built* rather than tabulated: a construction
numbers its vertices as the construction goes, not as a search would. -/
theorem isConnected_of_bfsOrder {G : CGraph} (l : List G.V) (v₀ : G.V)
    (h : ∀ v : G.V, v ≠ v₀ → ∃ w : G.V, l.idxOf w < l.idxOf v ∧ G.Adj v w) : G.IsConnected :=
  isConnected_of_rank (fun v ↦ l.idxOf v) v₀ h

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
theorem not_isBipartite_mycielskian {G : CGraph} {a b : G.V} (hab : G.Adj a b) :
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
theorem isConnected_mycielskian {G : CGraph} (h : ∀ v : G.V, ∃ w, G.Adj v w) :
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

@[toIsoGraph]
theorem girth_eq_zero_iff {G : CGraph} : G.girth = 0 ↔ G.IsAcyclic :=
  SimpleGraph.girth_eq_zero

@[toIsoGraph]
theorem three_le_girth {G : CGraph} (h : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  SimpleGraph.three_le_girth h

theorem girth_le_length {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a} (h : w.IsCycle) :
    G.girth ≤ w.length :=
  SimpleGraph.Walk.IsCycle.girth_le_length h

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
@[toIsoGraph]
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
of `IsoGraph/SmallGraphs/Defs/Named.lean` get their girth. -/

theorem exists_cycleList_of_isCycle {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a}
    (hw : w.IsCycle) :
    ∃ (u : G.V) (vs : List G.V), vs.length + 1 = w.length ∧ (u :: vs).Nodup ∧
      List.IsChain (fun x y ↦ G.Adj x y) (u :: vs) ∧ G.Adj (vs.getLastD u) u := by
  cases w with
  | nil => exact absurd rfl hw.ne_nil
  | @cons _ b _ h p =>
    refine ⟨b, p.support.tail, ?_, ?_, ?_, ?_⟩
    · simp [SimpleGraph.Walk.length_support]
    · rw [SimpleGraph.Walk.cons_tail_support]
      simpa using hw.support_nodup
    · rw [SimpleGraph.Walk.cons_tail_support]
      exact p.isChain_adj_support
    · have hl : p.support.getLastD b = a := getLastD_support p b
      rw [← SimpleGraph.Walk.cons_tail_support p, List.getLastD_cons] at hl
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

/-- **Both halves of a cycle list at once**: the girth bound and the cycle.  A girth is an
antisymmetry between the two, and giving the list twice means checking it twice — for the graphs
below, three `native_decide`s twice over.  The graph is explicit, unlike everywhere else in this
file: a conjunction is usually destructured without an expected type, and then nothing else in the
arguments says which graph the vertices belong to. -/
theorem girth_le_and_not_isAcyclic_of_cycleList (G : CGraph) (u : G.V) (vs : List G.V)
    (h2 : 2 ≤ vs.length) (hnd : (u :: vs).Nodup)
    (hch : List.IsChain (fun x y ↦ G.Adj x y) (u :: vs)) (hcl : G.Adj (vs.getLastD u) u) :
    G.girth ≤ vs.length + 1 ∧ ¬ G.IsAcyclic := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_cycleList u vs h2 hnd hch hcl
  exact ⟨hl ▸ girth_le_length hw, not_isAcyclic_of_isCycle hw⟩

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

/-- **A depth-first search for a short cycle through `a`**, walking the neighbour list `nb`.
`path` is the walk so far, in reverse, so its head is where the search has got to and `a` is where
it has to close up; `fuel` bounds the steps left, so the cycles found are those of length at most
`fuel`.

The search refuses to revisit a vertex.  Nothing is lost by that — a cycle has distinct vertices —
and it is what keeps the search cheap: on a cubic graph the branching factor drops from three to
two, which at the lengths the cages below need is the difference between minutes and hours. -/
def cycleSearch {G : CGraph} (nb : G.V → List G.V) (a : G.V) : ℕ → List G.V → Bool
  | 0, _ => false
  | fuel + 1, path =>
    (nb (path.headD a)).any fun v =>
      if v = a then decide (2 ≤ path.length)
      else if v ∈ path then false
      else cycleSearch nb a fuel (v :: path)

private theorem cycleSearch_succ {G : CGraph} (nb : G.V → List G.V) (a : G.V) (fuel : ℕ)
    (path : List G.V) :
    cycleSearch nb a (fuel + 1) path =
      (nb (path.headD a)).any fun v =>
        if v = a then decide (2 ≤ path.length)
        else if v ∈ path then false
        else cycleSearch nb a fuel (v :: path) := rfl

/-- **The search finds every cycle list it has the fuel for.**  The induction is on the part of
the walk still to come, carrying the part already walked as `path`, in reverse; the first step of
the search is the case `path = []`, where the head is `a` itself. -/
private theorem cycleSearch_of_cycleList {G : CGraph} {nb : G.V → List G.V}
    (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b) (a : G.V) :
    ∀ (rest : List G.V) (fuel : ℕ) (path : List G.V), rest.length + 1 ≤ fuel →
      2 ≤ path.length + rest.length → (a :: (path ++ rest)).Nodup →
      List.IsChain (fun x y ↦ G.Adj x y) (path.headD a :: rest) →
      G.Adj (rest.getLastD (path.headD a)) a → cycleSearch nb a fuel path = true := by
  intro rest
  induction rest with
  | nil =>
    intro fuel path hf h2 _ _ hcl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [cycleSearch_succ, List.any_eq_true]
    exact ⟨a, (hnb _ _).2 (by simpa using hcl), by simp; omega⟩
  | cons w rest' ih =>
    intro fuel path hf h2 hnd hch hcl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hnd' : (a :: (w :: path ++ rest')).Nodup := ((List.perm_middle.cons a).nodup_iff).1 hnd
    have hwa : ¬ w = a := fun h ↦ (List.nodup_cons.1 hnd').1 (by simp [h])
    have hwp : w ∉ path := by
      have := (List.nodup_cons.1 hnd').2
      simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at this
      exact this.1.1
    rw [List.isChain_cons_cons] at hch
    rw [cycleSearch_succ, List.any_eq_true]
    refine ⟨w, (hnb _ _).2 hch.1, ?_⟩
    simp only [hwa, ite_false, hwp]
    refine ih f (w :: path) (by simp at hf ⊢; omega) (by simp at h2 ⊢; omega) hnd' ?_ ?_
    · simpa using hch.2
    · rw [List.getLastD_cons] at hcl; exact hcl

/-- **Girth at least `L` from a neighbour list.**  `nb` is a list of neighbours of each vertex —
in practice a precomputed table, which is what makes the search below cheap — and the hypothesis
says that no cycle of length less than `L` closes up anywhere in it.  A graph with a cycle and no
cycle that short has girth at least `L`.

One `native_decide`, at every `L`.  The alternative is to unfold the search into `L` nested
quantifiers over the table and let the elaborator state them, and that is the expensive way round:
the searches are a second's work either way, but each level of quantifier costs a `Fintype` and a
`DecidableEq` over the vertex type, and by the twelfth those instances are the compile time.  The
girth of the Tutte 12-cage took a hundred and sixteen seconds that way, and three this way. -/
theorem le_girth_of_nbrList {G : CGraph} {nb : G.V → List G.V} (L : ℕ)
    (hnb : ∀ a b : G.V, b ∈ nb a ↔ G.Adj a b)
    (h : ∀ a : G.V, cycleSearch nb a (L - 1) [] = false)
    (hnac : ¬ G.IsAcyclic) : L ≤ G.girth := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact Nat.zero_le _
  refine le_girth_of_forall_cycleList (fun u vs h2 hlt hnd hch hcl ↦ ?_) hnac
  have hfound := cycleSearch_of_cycleList hnb u vs (L - 1) [] (by omega) (by simpa using h2)
    (by simpa using hnd) (by simpa using hch) (by simpa using hcl)
  rw [h u] at hfound
  exact Bool.noConfusion hfound

/-- The neighbour lists of every vertex in `l`, as a table indexed by position in `l`. -/
def nbrTable (G : CGraph) (l : List G.V) : List (List G.V) :=
  l.map fun a ↦ l.filter fun b ↦ G.Adj a b

end CGraph
