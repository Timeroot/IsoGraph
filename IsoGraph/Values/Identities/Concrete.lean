import IsoGraph.Invariants.Certificates
import IsoGraph.Graphs.Quotient
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Nat.Choose.Bounds
import IsoGraph.ForMathlib.Nat
import IsoGraph.ForMathlib.SimpleGraph

/-!
# The concrete families, and the invariants of the products

The first of four modules of `CGraph`-level identities — the level at which everything here is
proved, before `@[toIsoGraph]` carries it to the quotient.

This one starts with the families that are given by explicit data: the circulants, the graphs built
by `ofEdges`, and the decorated cycles and trees in their degenerate cases, together with the
relabellings that identify them and the two-colourings that show which of them are bipartite.  It
then turns to the four products, and proves for each the things the tables will need: which
vertices are adjacent, the degree sequence, the clique number, the diameter, the chromatic number.
The Mycielskian raising the chromatic number by one and the greedy colouring of a Kneser graph
close it out.
-/

set_option autoImplicit false

namespace CGraph

/-! ## Circulants

`circulant_congr` says that only the differences in `(0, n)` matter, and the three corollaries
normalise a connection set: drop a `0`, drop a repeat, and replace `k` by `n - k`. -/

/-- **Only the differences in `(0, n)` matter.**  A circulant only ever asks whether its
connection set contains a difference of two distinct vertices, so two connection sets agreeing
there give the same graph — on the nose, not just up to isomorphism. -/
@[toIsoGraph]
theorem circulant_congr (n : ℕ) (S T : List ℕ)
    (h : ∀ d, 0 < d → d < n → S.contains d = T.contains d) :
    circulant n S = circulant n T := by
  refine (eq_ofRel (circulant n S) (fun x y ↦ T.contains ((y.1 + n - x.1) % n))
    fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  obtain ⟨-, hp, hq⟩ := circulant_diff_facts n x y hne
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  show (decide (x ≠ y) && (S.contains ((y.1 + n - x.1) % n) ||
    S.contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and, h _ hp (Nat.mod_lt _ hn), h _ hq (Nat.mod_lt _ hn)]

/-- A `0` in the connection set contributes nothing: `x` and `y` differ by `0` only when they are
equal, and a circulant has no loops. -/
@[toIsoGraph]
theorem circulant_zero_cons (n : ℕ) (S : List ℕ) :
    circulant n (0 :: S) = circulant n S :=
  circulant_congr n _ _ fun d hd _ ↦ by
    have h0 : (d == 0) = false := by simp; omega
    simp only [List.contains_cons, h0, Bool.false_or]

/-- A repeated entry in the connection set contributes nothing. -/
@[toIsoGraph]
theorem circulant_dup_cons (n k : ℕ) (S : List ℕ) :
    circulant n (k :: k :: S) = circulant n (k :: S) :=
  circulant_congr n _ _ fun d _ _ ↦ by
    simp only [List.contains_cons]
    cases (d == k) <;> simp

/-- **The connection set is symmetric.**  A circulant joins `x` to `y` when either difference is
listed, so replacing an entry `k` by `n - k` does not change the graph. -/
@[toIsoGraph]
theorem circulant_neg_cons (n k : ℕ) (hk : k ≤ n) (S : List ℕ) :
    circulant n (k :: S) = circulant n ((n - k) :: S) := by
  refine (eq_ofRel (circulant n (k :: S))
    (fun x y ↦ ((n - k) :: S).contains ((y.1 + n - x.1) % n)) fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  obtain ⟨hsum, hp, hq⟩ := circulant_diff_facts n x y hne
  have key : ((y.1 + n - x.1) % n = k ∨ (x.1 + n - y.1) % n = k) ↔
      ((y.1 + n - x.1) % n = n - k ∨ (x.1 + n - y.1) % n = n - k) := by omega
  show (decide (x ≠ y) && ((k :: S).contains ((y.1 + n - x.1) % n) ||
    (k :: S).contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and]
  refine Bool.eq_iff_iff.2 ?_
  simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq]
  tauto

/-- The connection set of `Paley(13)` is `{±1, ±3, ±4}`. -/
@[toIsoGraph]
theorem paley_thirteen_eq_circulant : paley 13 = circulant 13 [1, 3, 4] :=
  eq_ofRel _ _ (by decide)

/-- The connection set of `Paley(17)` is `{±1, ±2, ±4, ±8}`. -/
@[toIsoGraph]
theorem paley_seventeen_eq_circulant : paley 17 = circulant 17 [1, 2, 4, 8] :=
  eq_ofRel _ _ (by decide)

/-! ## Bipartiteness

`CGraph.IsBipartite` is a two-colouring of the vertices with no monochromatic edge.  The
constructions carry colourings around in the obvious way, and a colouring is exactly what
`Iso.tensorTwoOfColouring` needs to split the double cover. -/

/-- A disjoint union of bipartite graphs is bipartite. -/
theorem IsBipartite.disjUnion {G H : CGraph} (hG : G.IsBipartite) (hH : H.IsBipartite) :
    (CGraph.disjUnion G H).IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  obtain ⟨d, hd⟩ := hH
  refine ⟨Sum.elim c d, ?_⟩
  rintro (x | x) (y | y) hxy <;> simp only [Sum.elim_inl, Sum.elim_inr] at *
  · exact hc x y (by simpa using hxy)
  · simp at hxy
  · simp at hxy
  · exact hd x y (by simpa using hxy)

/-- A Cartesian product of bipartite graphs is bipartite: take the `xor` of the two colourings. -/
theorem IsBipartite.cartesianProduct {G H : CGraph}
    (hG : G.IsBipartite) (hH : H.IsBipartite) : (CGraph.cartesianProduct G H).IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  obtain ⟨d, hd⟩ := hH
  refine ⟨fun p ↦ xor (c p.1) (d p.2), ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.cartesianProduct_adj] at hxy
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hxy
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hd y y' h2
    subst h1
    simpa using fun h ↦ this (by simpa using h)
  · have := hc x x' h1
    subst h2
    simpa using fun h ↦ this (by simpa using h)

/-- A tensor product is bipartite as soon as one factor is: colour by that factor. -/
theorem IsBipartite.tensorProduct_left {G H : CGraph}
    (hG : G.IsBipartite) : (CGraph.tensorProduct G H).IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  refine ⟨fun p ↦ c p.1, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.tensorProduct_adj] at hxy
  simp only [Bool.and_eq_true] at hxy
  exact hc x x' hxy.1

theorem IsBipartite.tensorProduct_right {G H : CGraph}
    (hH : H.IsBipartite) : (CGraph.tensorProduct G H).IsBipartite := by
  obtain ⟨c, hc⟩ := hH
  refine ⟨fun p ↦ c p.2, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.tensorProduct_adj] at hxy
  simp only [Bool.and_eq_true] at hxy
  exact hc y y' hxy.2

/-- A summand of a bipartite disjoint union is bipartite: restrict the colouring. -/
theorem IsBipartite.of_disjUnion_left {G H : CGraph} (h : (CGraph.disjUnion G H).IsBipartite) :
    G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a ↦ c (.inl a), fun x y hxy ↦ hc _ _ (by rwa [disjUnion_adj_inl_inl])⟩

theorem IsBipartite.of_disjUnion_right {G H : CGraph} (h : (CGraph.disjUnion G H).IsBipartite) :
    H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b ↦ c (.inr b), fun x y hxy ↦ hc _ _ (by rwa [disjUnion_adj_inr_inr])⟩

/-- A factor of a bipartite Cartesian product is bipartite: a fixed vertex of the other factor
cuts out a copy of it. -/
theorem IsBipartite.of_cartesianProduct_left {G H : CGraph}
    (hH : Nonempty H.V) (h : (CGraph.cartesianProduct G H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨b⟩ := hH
  refine ⟨fun a ↦ c (a, b), fun x y hxy ↦ hc (x, b) (y, b) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

theorem IsBipartite.of_cartesianProduct_right {G H : CGraph}
    (hG : Nonempty G.V) (h : (CGraph.cartesianProduct G H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨a⟩ := hG
  refine ⟨fun b ↦ c (a, b), fun x y hxy ↦ hc (a, x) (a, y) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

/-- **Odd cycles are not bipartite.**  Walking around the cycle, the colour alternates with the
parity of the index; coming back to `0` from the last vertex, which has even index, contradicts
the edge that closes the cycle. -/
@[toIsoGraph]
theorem not_isBipartite_cycle_odd (m : ℕ) : ¬ (CGraph.cycle (2 * m + 3)).IsBipartite := by
  set n := 2 * m + 3 with hn
  rintro ⟨c, hc⟩
  have adj : ∀ (k l : ℕ) (hk : k < n) (hl : l < n), k ≠ l → (k + 1) % n = l →
      c (⟨k, hk⟩ : Fin n) ≠ c (⟨l, hl⟩ : Fin n) := by
    intro k l hk hl hne hkl
    refine hc ⟨k, hk⟩ ⟨l, hl⟩ ?_
    simp only [CGraph.cycle, CGraph.ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq, ne_eq, Fin.ext_iff]
    exact ⟨hne, Or.inl hkl⟩
  have hz : 0 < n := by omega
  have alt : ∀ (k : ℕ) (hk : k < n),
      c (⟨k, hk⟩ : Fin n) = xor (c (⟨0, hz⟩ : Fin n)) (decide (k % 2 = 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hstep := adj k (k + 1) (by omega) hk (by omega) (Nat.mod_eq_of_lt hk)
      rw [ih (by omega)] at hstep
      have hpar : (decide ((k + 1) % 2 = 1)) = !(decide (k % 2 = 1)) := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.add_mod, h]
      rw [hpar]
      revert hstep
      rcases c (⟨k + 1, hk⟩ : Fin n) <;> rcases c (⟨0, hz⟩ : Fin n) <;>
        rcases (decide (k % 2 = 1)) <;> simp
  have hlast := alt (n - 1) (by omega)
  have hwrap : (n - 1 + 1) % n = 0 := by rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  have hclose := adj (n - 1) 0 (by omega) (by omega) (by omega) hwrap
  rw [hlast] at hclose
  have : (n - 1) % 2 = 0 := by omega
  rw [this] at hclose
  simp at hclose

@[toIsoGraph]
theorem not_isBipartite_complete (n : ℕ) : ¬ (CGraph.complete (n + 3)).IsBipartite := by
  have hadj : ∀ i j : Fin (n + 3), i.1 ≠ j.1 → (CGraph.complete (n + 3)).Adj i j := by
    intro i j hij
    simp only [CGraph.complete_adj, decide_eq_true_eq, ne_eq, Fin.ext_iff]
    exact hij
  exact not_isBipartite_of_triangle (a := (⟨0, by omega⟩ : (CGraph.complete (n + 3)).V))
    (b := ⟨1, by omega⟩) (d := ⟨2, by omega⟩) (hadj _ _ (by simp)) (hadj _ _ (by simp))
    (hadj _ _ (by simp))

/-- A side of a bipartite join is bipartite: restrict the colouring. -/
theorem IsBipartite.of_join_left {G H : CGraph}
    (h : (CGraph.join G H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a ↦ c (.inl a), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inl_inl])⟩

theorem IsBipartite.of_join_right {G H : CGraph}
    (h : (CGraph.join G H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b ↦ c (.inr b), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inr_inr])⟩

/-- An edge on one side of a join, together with any vertex on the other side, is a triangle. -/
theorem not_isBipartite_join_of_adj_left {G H : CGraph}
    {a b : G.V} (hab : G.Adj a b) (c : H.V) : ¬ (CGraph.join G H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inl a) (b := .inl b) (d := .inr c)
    (by rwa [join_adj_inl_inl]) (join_adj_inl_inr G H a c) (join_adj_inl_inr G H b c)

theorem not_isBipartite_join_of_adj_right {G H : CGraph}
    {a b : H.V} (hab : H.Adj a b) (c : G.V) : ¬ (CGraph.join G H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inr a) (b := .inr b) (d := .inl c)
    (by rwa [join_adj_inr_inr]) (join_adj_inr_inl G H a c) (join_adj_inr_inl G H b c)

/-- Three nonempty sides give a triangle, whatever the graphs on them are. -/
theorem not_isBipartite_join_join {G H K : CGraph}
 (a : G.V) (b : H.V) (c : K.V) :
    ¬ (CGraph.join G (CGraph.join H K)).IsBipartite :=
  not_isBipartite_of_triangle (a := .inl a) (b := .inr (.inl b)) (d := .inr (.inr c))
    (join_adj_inl_inr _ _ _ _) (join_adj_inl_inr _ _ _ _)
    (by rw [join_adj_inr_inr, join_adj_inl_inr])

/-! ## Edge lists

The `ofEdges`-based families are all built from `pathEdges`, `cycleEdges`, `cliqueEdges` and
`legEdges`; the lemmas here put each of those lists in closed form and read off its membership,
which is what turns a degenerate case of one of those families into a named graph. -/

theorem pathEdges_cons_cons (a b : ℕ) (l : List ℕ) :
    pathEdges (a :: b :: l) = (a, b) :: pathEdges (b :: l) := rfl

theorem pathEdges_map_succ : ∀ l : List ℕ,
    pathEdges (l.map (· + 1)) = (pathEdges l).map (fun p ↦ (p.1 + 1, p.2 + 1))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      have ih := pathEdges_map_succ (b :: rest)
      simp only [List.map_cons] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, List.map_cons, ih]

theorem pathEdges_concat : ∀ (l : List ℕ) (b x : ℕ),
    pathEdges (l ++ [b, x]) = pathEdges (l ++ [b]) ++ [(b, x)]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: c :: rest, b, x => by
      have ih := pathEdges_concat (c :: rest) b x
      simp only [List.cons_append] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, ih, List.cons_append]

/-- The edges of the path `0, 1, …, m`, in closed form. -/
theorem pathEdges_range : ∀ m : ℕ,
    pathEdges (List.range (m + 1)) = (List.range m).map (fun i ↦ (i, i + 1))
  | 0 => rfl
  | m + 1 => by
      have h : (List.range (m + 1)).map (· + 1) = 1 :: ((List.range m).map (· + 1)).map (· + 1) := by
        conv_lhs => rw [List.range_succ_eq_map]
        simp
      conv_lhs => rw [List.range_succ_eq_map]
      rw [h, pathEdges_cons_cons, ← h, pathEdges_map_succ, pathEdges_range m]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.map_map]
      rfl

@[simp] theorem mem_pathEdges_range (m a b : ℕ) :
    ((a, b) ∈ pathEdges (List.range (m + 1))) ↔ (b = a + 1 ∧ a < m) := by
  rw [pathEdges_range]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨rfl, hi⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl, rfl⟩

@[simp] theorem cycleEdges_zero : cycleEdges 0 = [] := rfl

/-- The edges of a cycle: the path `0, 1, …, m` together with the wrap-around edge. -/
theorem cycleEdges_succ (k : ℕ) :
    cycleEdges (k + 1) = (List.range k).map (fun i ↦ (i, i + 1)) ++ [(k, 0)] := by
  rw [cycleEdges, List.range_succ, List.append_assoc,
    show ([k] ++ [0] : List ℕ) = [k, 0] from rfl, pathEdges_concat, ← List.range_succ,
    pathEdges_range]

@[simp] theorem mem_cycleEdges_succ (k a b : ℕ) :
    ((a, b) ∈ cycleEdges (k + 1)) ↔ ((b = a + 1 ∧ a < k) ∨ (a = k ∧ b = 0)) := by
  rw [cycleEdges_succ]
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hi⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, ha⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Membership in `cycleEdges` without splitting the length into a successor.  This is the form to
use when the length is a numeral, where `mem_cycleEdges_succ` does not fire. -/
theorem mem_cycleEdges (m a b : ℕ) :
    ((a, b) ∈ cycleEdges m) ↔ ((b = a + 1 ∧ a + 1 < m) ∨ (a + 1 = m ∧ b = 0)) := by
  cases m with
  | zero => simp only [cycleEdges_zero, List.not_mem_nil, false_iff]; omega
  | succ k => rw [mem_cycleEdges_succ]; omega

@[simp] theorem cliqueEdges_zero : cliqueEdges 0 = [] := rfl
@[simp] theorem cliqueEdges_one : cliqueEdges 1 = [] := rfl

@[simp] theorem mem_cliqueEdges (m a b : ℕ) : ((a, b) ∈ cliqueEdges m) ↔ (a < b ∧ b < m) := by
  simp only [cliqueEdges, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, -, x, ⟨hx, hix⟩, rfl, rfl⟩
    exact ⟨hix, hx⟩
  · rintro ⟨hab, hb⟩
    exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl, rfl⟩

@[simp] theorem legEdges_zero (v off : ℕ) : legEdges v off 0 = [] := rfl

/-- A leg of `k` fresh vertices hung off vertex `0`, when the fresh vertices start at `1`, is just
the path `0, 1, …, k`. -/
theorem legEdges_zero_one (k : ℕ) : legEdges 0 1 k = pathEdges (List.range (k + 1)) := by
  rw [List.range_succ_eq_map]
  simp only [legEdges]

/-- A leg hung off vertex `0` whose fresh vertices also start at `0`: the same path, with a loop
at `0` in front of it (which `ofEdges` discards). -/
theorem legEdges_zero_zero (k : ℕ) : legEdges 0 0 k = pathEdges (0 :: List.range k) := by
  simp only [legEdges, Nat.add_zero, List.map_id_fun', id_eq]

@[simp] theorem mem_pathEdges_zero_cons_range (k a b : ℕ) :
    ((a, b) ∈ pathEdges (0 :: List.range k)) ↔
      ((a = 0 ∧ b = 0 ∧ 0 < k) ∨ (b = a + 1 ∧ a + 1 < k)) := by
  rcases k with _ | j
  · simp [pathEdges]
  · have h : (0 :: List.range (j + 1)) = 0 :: 0 :: (List.range j).map (· + 1) := by
      conv_lhs => rw [List.range_succ_eq_map]
    rw [h, pathEdges_cons_cons, ← List.range_succ_eq_map]
    simp only [List.mem_cons, Prod.mk.injEq, mem_pathEdges_range]
    omega

/-! ## Degenerate cases of the decorated cycles and trees

Each family below is an `ofEdges` over `Fin n`, so its degenerate cases are equalities of graphs
on the nose, not merely isomorphisms: the edge list literally becomes the edge list of a cycle, a
clique or a path. -/

theorem ofEdges_nil (n : ℕ) : ofEdges n [] = empty n := by
  rw [empty_eq_ofRel]
  rfl

/-- Two edge lists that meet the same unordered pairs of *distinct* vertices describe the same
graph: `ofEdges` ignores the orientation of each pair, and discards the diagonal. -/
theorem ofEdges_congr (n : ℕ) (es fs : List (ℕ × ℕ))
    (h : ∀ p q : ℕ, p ≠ q → (((p, q) ∈ es ∨ (q, p) ∈ es) ↔ ((p, q) ∈ fs ∨ (q, p) ∈ fs))) :
    ofEdges n es = ofEdges n fs := by
  refine eq_ofRel (ofEdges n es) (fun i j ↦ fs.contains (i.1, j.1)) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact h x.1 y.1 fun hv ↦ hxy (Fin.ext hv)

/-- Replacing a prefix of the edge list by an equivalent one does not change the graph.  This is
the shape the decorated families come in: a cycle or clique part, followed by the legs. -/
theorem ofEdges_append_congr (n : ℕ) (es fs gs : List (ℕ × ℕ))
    (h : ∀ p q : ℕ, p ≠ q → (((p, q) ∈ es ∨ (q, p) ∈ es) ↔ ((p, q) ∈ fs ∨ (q, p) ∈ fs))) :
    ofEdges n (es ++ gs) = ofEdges n (fs ++ gs) := by
  refine ofEdges_congr _ _ _ fun p q hpq ↦ ?_
  simp only [List.mem_append]
  obtain ⟨h1, h2⟩ := h p q hpq
  constructor
  · rintro ((he | hg) | (he | hg))
    · exact (h1 (Or.inl he)).imp Or.inl Or.inl
    · exact Or.inl (Or.inr hg)
    · exact (h1 (Or.inr he)).imp Or.inl Or.inl
    · exact Or.inr (Or.inr hg)
  · rintro ((he | hg) | (he | hg))
    · exact (h2 (Or.inl he)).imp Or.inl Or.inl
    · exact Or.inl (Or.inr hg)
    · exact (h2 (Or.inr he)).imp Or.inl Or.inl
    · exact Or.inr (Or.inr hg)

theorem ofEdges_cycleEdges (m : ℕ) : ofEdges m (cycleEdges m) = cycle m := by
  refine eq_ofRel (ofEdges m (cycleEdges m)) (fun i j ↦ (i.1 + 1) % m == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rcases m with _ | k
  · exact absurd x.isLt (by omega)
  · have hx : x.1 < k + 1 := x.isLt
    have hy : y.1 < k + 1 := y.isLt
    have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
    have e1 := succ_mod_eq_iff (d := k + 1) (x := x.1) (y := y.1) hx
    have e2 := succ_mod_eq_iff (d := k + 1) (x := y.1) (y := x.1) hy
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_cycleEdges_succ]
    omega

/-- The one-vertex "cycle" is a single loop, which `ofEdges` discards. -/
theorem ofEdges_cycleEdges_one_append (n : ℕ) (es : List (ℕ × ℕ)) :
    ofEdges n (cycleEdges 1 ++ es) = ofEdges n es := by
  have hcyc : ∀ a b : ℕ, ((a, b) ∈ cycleEdges 1) ↔ (a = 0 ∧ b = 0) := by
    intro a b; rw [mem_cycleEdges]; omega
  refine ofEdges_congr _ _ _ fun p q hpq ↦ ?_
  simp only [List.mem_append, hcyc]
  constructor
  · rintro ((⟨rfl, rfl⟩ | he) | (⟨rfl, rfl⟩ | he))
    · exact absurd rfl hpq
    · exact Or.inl he
    · exact absurd rfl hpq
    · exact Or.inr he
  · exact fun he ↦ he.imp Or.inr Or.inr

theorem ofEdges_cliqueEdges (m : ℕ) : ofEdges m (cliqueEdges m) = complete m := by
  rw [complete_eq_ofRel]
  refine eq_ofRel (ofEdges m (cliqueEdges m)) _ ?_
  intro x y hxy
  have hne : (x : Fin m).1 ≠ (y : Fin m).1 := fun h ↦ hxy (Fin.ext h)
  have hx : (x : Fin m).1 < m := x.isLt
  have hy : (y : Fin m).1 < m := y.isLt
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_cliqueEdges, or_self, iff_true]
  omega

theorem ofEdges_legEdges_one (k : ℕ) : ofEdges (1 + k) (legEdges 0 1 k) = path (1 + k) := by
  refine eq_ofRel (ofEdges (1 + k) (legEdges 0 1 k)) (fun i j ↦ i.1 + 1 == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    legEdges_zero_one, List.contains_eq_mem]
  have hx : (x : Fin (1 + k)).1 < 1 + k := x.isLt
  have hy : (y : Fin (1 + k)).1 < 1 + k := y.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_pathEdges_range]
  omega

theorem ofEdges_legEdges_zero (k : ℕ) : ofEdges k (legEdges 0 0 k) = path k := by
  refine eq_ofRel (ofEdges k (legEdges 0 0 k)) (fun i j ↦ i.1 + 1 == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    legEdges_zero_zero, List.contains_eq_mem]
  have hx : (x : Fin k).1 < k := x.isLt
  have hy : (y : Fin k).1 < k := y.isLt
  have hne : (x : Fin k).1 ≠ (y : Fin k).1 := fun h ↦ hxy (Fin.ext h)
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_pathEdges_zero_cons_range]
  omega

/-- A tadpole with no tail is a cycle. -/
@[simp, toIsoGraph] theorem tadpole_zero (m : ℕ) : tadpole m 0 = cycle m := by
  rw [tadpole, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cycleEdges]

/-- A tadpole with no cycle is a path. -/
@[simp, toIsoGraph] theorem tadpole_zero_left (k : ℕ) : tadpole 0 k = path k := by
  rw [tadpole, cycleEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A tadpole whose cycle is a single vertex is a path: the "cycle" is a loop, which `ofEdges`
discards. -/
@[simp, toIsoGraph] theorem tadpole_one (k : ℕ) : tadpole 1 k = path (1 + k) := by
  rw [tadpole, ofEdges_cycleEdges_one_append, ofEdges_legEdges_one]

/-- A lollipop with no stick is a complete graph. -/
@[simp, toIsoGraph] theorem lollipop_zero (m : ℕ) : lollipop m 0 = complete m := by
  rw [lollipop, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cliqueEdges]

/-- A lollipop with no clique is a path. -/
@[simp, toIsoGraph] theorem lollipop_zero_left (k : ℕ) : lollipop 0 k = path k := by
  rw [lollipop, cliqueEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A lollipop whose clique is a single vertex is a path. -/
@[simp, toIsoGraph] theorem lollipop_one (k : ℕ) : lollipop 1 k = path (1 + k) := by
  rw [lollipop, cliqueEdges_one, List.nil_append, ofEdges_legEdges_one]

/-- `K₂` and `C₂` have the same edges, so a lollipop on two vertices is a tadpole. -/
theorem lollipop_two (k : ℕ) : lollipop 2 k = tadpole 2 k := by
  rw [lollipop, tadpole]
  refine ofEdges_append_congr _ _ _ _ fun p q _ ↦ ?_
  simp only [mem_cliqueEdges, mem_cycleEdges]
  omega

/-- `K₃` and `C₃` have the same edges, so a lollipop on three vertices is a tadpole. -/
theorem lollipop_three (k : ℕ) : lollipop 3 k = tadpole 3 k := by
  rw [lollipop, tadpole]
  refine ofEdges_append_congr _ _ _ _ fun p q _ ↦ ?_
  simp only [mem_cliqueEdges, mem_cycleEdges]
  omega

/-- A spider with an empty leg is the spider without it. -/
@[toIsoGraph]
theorem spider_zero_cons (ks : List ℕ) : spider (0 :: ks) = spider ks := by
  rw [spider, spider, List.sum_cons, Nat.zero_add,
    show spiderEdges 1 (0 :: ks) = spiderEdges 1 ks from by
      rw [spiderEdges, legEdges_zero, List.nil_append, Nat.add_zero]]

/-- The legs of a spider split along a split of the list of leg lengths, the second block starting
where the first one left off. -/
theorem spiderEdges_append : ∀ (pre post : List ℕ) (off : ℕ),
    spiderEdges off (pre ++ post) = spiderEdges off pre ++ spiderEdges (off + pre.sum) post
  | [], _, off => by rw [List.nil_append, spiderEdges, List.nil_append, List.sum_nil, Nat.add_zero]
  | k :: pre, post, off => by
      rw [List.cons_append, spiderEdges, spiderEdges, spiderEdges_append pre post (off + k),
        List.append_assoc, List.sum_cons,
        show off + k + pre.sum = off + (k + pre.sum) from by omega]

/-- A spider ignores its empty legs wherever they sit in the list, not just at the front. -/
@[toIsoGraph]
theorem spider_append_zero_cons (pre post : List ℕ) :
    spider (pre ++ 0 :: post) = spider (pre ++ post) := by
  have hsum : (pre ++ 0 :: post).sum = (pre ++ post).sum := by
    simp only [List.sum_append, List.sum_cons, Nat.zero_add]
  rw [spider, spider, hsum, spiderEdges_append, spiderEdges_append, spiderEdges, legEdges_zero,
    List.nil_append, Nat.add_zero]

/-- A spider with a single leg is a path. -/
@[simp, toIsoGraph] theorem spider_singleton (k : ℕ) : spider [k] = path (1 + k) := by
  rw [spider, show spiderEdges 1 [k] = legEdges 0 1 k from by simp [spiderEdges],
    show (1 : ℕ) + [k].sum = 1 + k from by simp, ofEdges_legEdges_one]

theorem spiderEdges_replicate_zero : ∀ (off j : ℕ), spiderEdges off (List.replicate j 0) = []
  | _, 0 => rfl
  | off, j + 1 => by
      rw [List.replicate_succ, spiderEdges, legEdges_zero, List.nil_append,
        spiderEdges_replicate_zero (off + 0) j]

/-- A spider all of whose legs are empty is a single vertex. -/
@[simp, toIsoGraph]
theorem spider_replicate_zero (j : ℕ) :
    spider (List.replicate j 0) = empty 1 := by
  rw [spider, spiderEdges_replicate_zero,
    show (1 : ℕ) + (List.replicate j 0).sum = 1 from by simp, ofEdges_nil]

@[simp, toIsoGraph] theorem spider_nil : spider [] = empty 1 := spider_replicate_zero 0

theorem pendantEdges_replicate_zero : ∀ (v off j : ℕ), pendantEdges v off (List.replicate j 0) = []
  | _, _, 0 => rfl
  | v, off, j + 1 => by
      rw [List.replicate_succ, pendantEdges, List.range_zero, List.map_nil, List.nil_append,
        pendantEdges_replicate_zero (v + 1) (off + 0) j]

/-- A cycle carrying no pendant vertices is a cycle. -/
@[simp, toIsoGraph] theorem cyclePendant_replicate_zero (m j : ℕ) :
    cyclePendant m (List.replicate j 0) = cycle m := by
  rw [cyclePendant, pendantEdges_replicate_zero, List.append_nil,
    show m + (List.replicate j 0).sum = m from by simp, ofEdges_cycleEdges]

@[simp, toIsoGraph] theorem cyclePendant_nil (m : ℕ) : cyclePendant m [] = cycle m :=
  cyclePendant_replicate_zero m 0

/-- Pendant vertices attached beyond the end of the cycle are no vertices at all. -/
theorem pendantEdges_append_zero : ∀ (v off : ℕ) (ks : List ℕ),
    pendantEdges v off (ks ++ [0]) = pendantEdges v off ks
  | _, _, [] => by simp [pendantEdges]
  | v, off, k :: ks => by
      rw [List.cons_append, pendantEdges, pendantEdges, pendantEdges_append_zero (v + 1) (off + k)]

/-- A cycle with a trailing empty block of pendant vertices is the cycle without that block. -/
@[toIsoGraph]
theorem cyclePendant_append_zero (m : ℕ) (ks : List ℕ) :
    cyclePendant m (ks ++ [0]) = cyclePendant m ks := by
  have hsum : (ks ++ [0]).sum = ks.sum := by simp
  rw [cyclePendant, cyclePendant, pendantEdges_append_zero, hsum]

/-- Two paths of length one between the poles of a theta graph are the same single edge, so one of
them can be dropped. -/
@[toIsoGraph]
theorem thetaGraph_zero_zero_cons (ks : List ℕ) :
    thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks) := by
  rw [thetaGraph, thetaGraph]
  simp only [List.sum_cons, Nat.zero_add]
  refine ofEdges_congr _ _ _ fun p q _ ↦ ?_
  simp only [thetaEdges, List.mem_cons]
  tauto

/-! ## Relabellings for the `ofEdges` families

The `IsoGraph` identities at the end of this file that are *not* on-the-nose equalities of
`CGraph`s — a two-legged spider is a path, a one-path theta graph is a path, a double star with
leaves on one side only is a star — all need an explicit relabelling of `Fin n`.  This block
collects those relabellings together with the membership lemmas for the edge lists they act on,
and, in each case, the piece of pure arithmetic that says the relabelling matches the edges up.
Keeping the arithmetic separate is not just tidiness: stated as one goal, the disjunction over
all the edge shapes is large enough that `omega` spends minutes on it. -/

@[simp] theorem pathEdges_nil : pathEdges [] = [] := rfl
@[simp] theorem pathEdges_singleton (a : ℕ) : pathEdges [a] = [] := rfl

theorem pathEdges_map_add (c : ℕ) : ∀ l : List ℕ,
    pathEdges (l.map (· + c)) = (pathEdges l).map (fun p ↦ (p.1 + c, p.2 + c))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      have ih := pathEdges_map_add c (b :: rest)
      simp only [List.map_cons] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, List.map_cons, ih]

theorem legEdges_succ (v off j : ℕ) :
    legEdges v off (j + 1) = (v, off) :: (List.range j).map (fun i ↦ (i + off, i + 1 + off)) := by
  have h : (List.range (j + 1)).map (· + off)
      = off :: ((List.range j).map (· + 1)).map (· + off) := by
    conv_lhs => rw [List.range_succ_eq_map]
    simp [Nat.add_assoc]
  rw [legEdges, h, pathEdges_cons_cons, ← h, pathEdges_map_add, pathEdges_range, List.map_map]
  rfl

@[simp] theorem mem_legEdges (v off k p q : ℕ) :
    ((p, q) ∈ legEdges v off k) ↔
      ((p = v ∧ q = off ∧ 0 < k) ∨ (off ≤ p ∧ q = p + 1 ∧ p + 1 < off + k)) := by
  rcases k with _ | j
  · simp only [legEdges, List.range_zero, List.map_nil, pathEdges_singleton, List.not_mem_nil,
      Nat.lt_irrefl, Nat.add_zero, false_iff, not_or, not_and]
    exact ⟨fun _ _ ↦ not_false, fun _ _ ↦ by omega⟩
  · rw [legEdges_succ]
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hp, hq⟩)
      · exact Or.inl ⟨rfl, rfl, Nat.succ_pos j⟩
      · exact Or.inr (by omega)
    · rintro (⟨rfl, rfl, -⟩ | ⟨h1, rfl, h3⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨p - off, by omega, by omega, by omega⟩

/-- Adjacency in `path n`, phrased entirely in terms of the underlying naturals. -/
theorem path_adj_val (n : ℕ) (u v : (path n).V) :
    (path n).Adj u v = true ↔ (u.1 ≠ v.1 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)) := by
  have huv : (u = v) ↔ (u.1 = v.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
  simp only [path, ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ne_eq, huv]

/-- Adjacency in `ofEdges n es`, phrased entirely in terms of the underlying naturals. -/
theorem ofEdges_adj_val (n : ℕ) (es : List (ℕ × ℕ)) (u v : (ofEdges n es).V) :
    (ofEdges n es).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ es ∨ (v.1, u.1) ∈ es)) := by
  have huv : (u = v) ↔ (u.1 = v.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
  simp only [ofEdges, ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    ne_eq, huv, List.contains_eq_mem]

/-- Adjacency in `spider ks`, phrased entirely in terms of the underlying naturals. -/
theorem spider_adj_val (ks : List ℕ) (u v : (spider ks).V) :
    (spider ks).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ spiderEdges 1 ks ∨ (v.1, u.1) ∈ spiderEdges 1 ks)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `tadpole m k`, phrased entirely in terms of the underlying naturals. -/
theorem tadpole_adj_val (m k : ℕ) (u v : (tadpole m k).V) :
    (tadpole m k).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ cycleEdges m ++ legEdges 0 m k ∨
        (v.1, u.1) ∈ cycleEdges m ++ legEdges 0 m k)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `cyclePendant m ks`, phrased entirely in terms of the underlying naturals. -/
theorem cyclePendant_adj_val (m : ℕ) (ks : List ℕ) (u v : (cyclePendant m ks).V) :
    (cyclePendant m ks).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ cycleEdges m ++ pendantEdges 0 m ks ∨
        (v.1, u.1) ∈ cycleEdges m ++ pendantEdges 0 m ks)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `thetaGraph xs`, phrased entirely in terms of the underlying naturals. -/
theorem thetaGraph_adj_val (xs : List ℕ) (u v : (thetaGraph xs).V) :
    (thetaGraph xs).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ thetaEdges 2 xs ∨ (v.1, u.1) ∈ thetaEdges 2 xs)) :=
  ofEdges_adj_val _ _ u v

/-- Folding the interval `[0, a]` of `Fin N` back on itself, fixing everything above `a`.  This
is the relabelling that straightens a two-legged spider into a path: the two legs, which run
outwards from the centre, become one run from `a` down to `0` and one from `0` up. -/
def foldAt (a N : ℕ) (h : a < N) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 ≤ a then a - p.1 else p.1, by have := p.isLt; split <;> omega⟩
  invFun p := ⟨if p.1 ≤ a then a - p.1 else p.1, by have := p.isLt; split <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 ≤ a then a - p.1 else p.1) ≤ a then a - (if p.1 ≤ a then a - p.1 else p.1)
      else (if p.1 ≤ a then a - p.1 else p.1)) = p.1
    by_cases h1 : p.1 ≤ a
    · rw [if_pos h1, if_pos (by omega : a - p.1 ≤ a)]
      omega
    · rw [if_neg h1, if_neg h1]
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 ≤ a then a - p.1 else p.1) ≤ a then a - (if p.1 ≤ a then a - p.1 else p.1)
      else (if p.1 ≤ a then a - p.1 else p.1)) = p.1
    by_cases h1 : p.1 ≤ a
    · rw [if_pos h1, if_pos (by omega : a - p.1 ≤ a)]
      omega
    · rw [if_neg h1, if_neg h1]

@[simp] theorem foldAt_apply (a N : ℕ) (h : a < N) (p : Fin N) :
    (foldAt a N h p).1 = if p.1 ≤ a then a - p.1 else p.1 := rfl

/-- The arithmetic heart of `spider_pair`: after folding `[0, a]` back on itself, the two legs
of the spider `[a, b]` become a single run of consecutive naturals.  Both sides are spelled out
in the shape produced by `mem_legEdges`. -/
theorem foldAt_pair_iff (a b p q : ℕ) (hp : p < 1 + a + b) (hq : q < 1 + a + b) :
    ((if p ≤ a then a - p else p) ≠ (if q ≤ a then a - q else q) ∧
        ((if p ≤ a then a - p else p) + 1 = (if q ≤ a then a - q else q) ∨
          (if q ≤ a then a - q else q) + 1 = (if p ≤ a then a - p else p))) ↔
      (p ≠ q ∧
        ((((p = 0 ∧ q = 1 ∧ 0 < a) ∨ (1 ≤ p ∧ q = p + 1 ∧ p + 1 < 1 + a)) ∨
            ((p = 0 ∧ q = 1 + a ∧ 0 < b) ∨ (1 + a ≤ p ∧ q = p + 1 ∧ p + 1 < 1 + a + b))) ∨
          (((q = 0 ∧ p = 1 ∧ 0 < a) ∨ (1 ≤ q ∧ p = q + 1 ∧ q + 1 < 1 + a)) ∨
            ((q = 0 ∧ p = 1 + a ∧ 0 < b) ∨ (1 + a ≤ q ∧ p = q + 1 ∧ q + 1 < 1 + a + b))))) := by
  constructor
  · rintro ⟨hne, h⟩
    by_cases h1 : p ≤ a <;> by_cases h2 : q ≤ a
    · rw [if_pos h1, if_pos h2] at hne h
      rcases h with h | h
      · -- `q + 1 = p`, an edge of the first leg traversed towards the centre
        by_cases hq0 : q = 0
        · exact ⟨by omega, Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))⟩
        · exact ⟨by omega, Or.inr (Or.inl (Or.inr ⟨by omega, by omega, by omega⟩))⟩
      · by_cases hp0 : p = 0
        · exact ⟨by omega, Or.inl (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))⟩
        · exact ⟨by omega, Or.inl (Or.inl (Or.inr ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_pos h1, if_neg h2] at hne h
      -- only `a - p + 1 = q` is possible, forcing `p = 0` and `q = 1 + a`
      exact ⟨by omega, Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_neg h1, if_pos h2] at hne h
      exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_neg h1, if_neg h2] at hne h
      rcases h with h | h
      · exact ⟨by omega, Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩
      · exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩
  · rintro ⟨-, (((h | h) | (h | h)) | ((h | h) | (h | h)))⟩ <;> split_ifs <;> omega

/-! ### Theta graphs with no internal vertices -/

theorem thetaEdges_replicate_zero : ∀ (off j : ℕ),
    thetaEdges off (List.replicate j 0) = List.replicate j (0, 1)
  | _, 0 => rfl
  | off, j + 1 => by
      rw [List.replicate_succ, thetaEdges, thetaEdges_replicate_zero off j, List.replicate_succ]

@[toIsoGraph]
theorem thetaGraph_nil : thetaGraph [] = empty 2 := ofEdges_nil 2

@[simp] theorem mem_thetaEdges_replicate_zero (off j p q : ℕ) :
    ((p, q) ∈ thetaEdges off (List.replicate j 0)) ↔ (0 < j ∧ p = 0 ∧ q = 1) := by
  rw [thetaEdges_replicate_zero]
  simp only [List.mem_replicate, Prod.mk.injEq, ne_eq]
  constructor
  · rintro ⟨hj, rfl, rfl⟩
    exact ⟨Nat.pos_of_ne_zero hj, rfl, rfl⟩
  · rintro ⟨hj, rfl, rfl⟩
    exact ⟨by omega, rfl, rfl⟩

/-- A theta graph all of whose paths are single edges is just that edge. -/
@[toIsoGraph]
theorem thetaGraph_replicate_zero (j : ℕ) :
    thetaGraph (List.replicate (j + 1) 0) = complete 2 := by
  have hs : (List.replicate (j + 1) (0 : ℕ)).sum = 0 := by simp
  rw [thetaGraph, hs]
  refine (eq_ofRel (ofEdges (2 + 0) (thetaEdges 2 (List.replicate (j + 1) 0)))
    (fun _ _ ↦ true) ?_).trans (complete_eq_ofRel 2).symm
  intro x y hxy
  have hx : x.1 < 2 := x.isLt
  have hy : y.1 < 2 := y.isLt
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_thetaEdges_replicate_zero, or_self, iff_true]
  omega

/-! ### Theta graphs with a single path: rotating the tail -/

theorem mem_thetaEdges_singleton (k p q : ℕ) :
    ((p, q) ∈ thetaEdges 2 [k + 1]) ↔
      ((p = 0 ∧ q = 2) ∨ (p = 2 + k ∧ q = 1) ∨ (2 ≤ p ∧ q = p + 1 ∧ p < 2 + k)) := by
  simp only [thetaEdges, List.append_nil, List.mem_cons, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, rfl, h3⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨p - 2, by omega, by omega, by omega⟩)

/-- Rotating the interval `[1, N-1]` of `Fin N` one step down, fixing `0`.  This is the
relabelling that straightens a one-path theta graph into a path: the second pole, which sits at
`1`, gets moved to the far end. -/
def rotTail (N : ℕ) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1, by
    have := p.isLt; split_ifs <;> omega⟩
  invFun p := ⟨if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1, by
    have := p.isLt; split_ifs <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) = 0 then 0
      else if (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) = N - 1 then 1
      else (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) + 1) = p.1
    split_ifs <;> omega
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) = 0 then 0
      else if (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) = 1 then N - 1
      else (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) - 1) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim

@[simp] theorem rotTail_apply (N : ℕ) (p : Fin N) :
    (rotTail N p).1 = if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1 := rfl

/-- The arithmetic heart of `thetaGraph_singleton`: after rotating the tail, the two poles and the
one internal path of the theta graph become a single run of consecutive naturals.  Both sides are
spelled out in the exact shape produced by `mem_thetaEdges_singleton`. -/
theorem rotTail_pair_iff (k p q : ℕ) (hp : p < k + 3) (hq : q < k + 3) :
    ((if p = 0 then 0 else if p = 1 then k + 2 else p - 1) ≠
        (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) ∧
      ((if p = 0 then 0 else if p = 1 then k + 2 else p - 1) + 1 =
          (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) ∨
        (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) + 1 =
          (if p = 0 then 0 else if p = 1 then k + 2 else p - 1))) ↔
      (p ≠ q ∧
        (((p = 0 ∧ q = 2) ∨ (p = 2 + k ∧ q = 1) ∨ (2 ≤ p ∧ q = p + 1 ∧ p < 2 + k)) ∨
          ((q = 0 ∧ p = 2) ∨ (q = 2 + k ∧ p = 1) ∨ (2 ≤ q ∧ p = q + 1 ∧ q < 2 + k)))) := by
  have dir : ∀ a b : ℕ, a < k + 3 → b < k + 3 →
      (((if a = 0 then 0 else if a = 1 then k + 2 else a - 1) + 1 =
          (if b = 0 then 0 else if b = 1 then k + 2 else b - 1)) ↔
        ((a = 0 ∧ b = 2) ∨ (a = 2 + k ∧ b = 1) ∨ (2 ≤ a ∧ b = a + 1 ∧ a < 2 + k))) := by
    intro a b ha hb
    split_ifs <;> first
      | omega
      | (rw [false_iff]; omega)
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨fun hpq ↦ hne (by rw [hpq]), Or.inl ((dir p q hp hq).1 h)⟩
    · exact ⟨fun hpq ↦ hne (by rw [hpq]), Or.inr ((dir q p hq hp).1 h)⟩
  · rintro ⟨-, h | h⟩
    · have h' := (dir p q hp hq).2 h
      refine ⟨?_, Or.inl h'⟩
      rw [← h']
      exact (Nat.lt_succ_self _).ne
    · have h' := (dir q p hq hp).2 h
      refine ⟨?_, Or.inr h'⟩
      rw [← h']
      exact ((Nat.lt_succ_self _).ne).symm

/-! ### Double stars -/

@[simp] theorem mem_doubleStarEdges (m n p q : ℕ) :
    ((p, q) ∈ ((0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
        ((List.range n).map fun i ↦ (1, 2 + m + i))))) ↔
      ((p = 0 ∧ q = 1) ∨ (p = 0 ∧ 2 ≤ q ∧ q < 2 + m) ∨
        (p = 1 ∧ 2 + m ≤ q ∧ q < 2 + m + n)) := by
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨q - 2, by omega, rfl, by omega⟩)
    · exact Or.inr (Or.inr ⟨q - (2 + m), by omega, rfl, by omega⟩)

/-- Swapping the vertices `0` and `1` of `Fin N`. -/
def swapZeroOne (N : ℕ) (h : 1 < N) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1, by
    have := p.isLt; split_ifs <;> omega⟩
  invFun p := ⟨if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1, by
    have := p.isLt; split_ifs <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 0 then 1
      else if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 1 then 0
      else (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1)) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 0 then 1
      else if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 1 then 0
      else (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1)) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim

@[simp] theorem swapZeroOne_apply (N : ℕ) (h : 1 < N) (p : Fin N) :
    (swapZeroOne N h p).1 = if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1 := rfl

/-! ### The one-legged spider, as an edge list -/

theorem spiderEdges_replicate_one : ∀ (off n : ℕ),
    spiderEdges off (List.replicate n 1) = (List.range n).map (fun i ↦ (0, off + i))
  | _, 0 => rfl
  | off, n + 1 => by
      have ih := spiderEdges_replicate_one (off + 1) n
      rw [List.replicate_succ, spiderEdges, ih, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      simp only [legEdges, List.range_one, List.map_cons, List.map_nil, pathEdges_cons_cons,
        pathEdges_singleton, List.cons_append, List.nil_append, Nat.add_zero, Function.comp_def]
      congr 1
      · rw [Nat.zero_add]
      · exact List.map_congr_left fun i _ ↦ Prod.ext rfl (by omega)

@[simp] theorem mem_spiderEdges_replicate_one (off n p q : ℕ) :
    ((p, q) ∈ spiderEdges off (List.replicate n 1)) ↔ (p = 0 ∧ off ≤ q ∧ q < off + n) := by
  rw [spiderEdges_replicate_one]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨q - off, by omega, rfl, by omega⟩

/-- A one-vertex "cycle" carrying `k` pendant vertices is the `k`-legged spider whose legs all
have length one: the loop is discarded, and the pendant edges are the legs. -/
theorem cyclePendant_one_eq_spider (k : ℕ) :
    cyclePendant 1 [k] = spider (List.replicate k 1) := by
  have hsum : (1 : ℕ) + ([k] : List ℕ).sum = 1 + (List.replicate k 1).sum := by simp
  have hes : pendantEdges 0 1 [k] = spiderEdges 1 (List.replicate k 1) := by
    rw [spiderEdges_replicate_one]
    simp only [pendantEdges, List.append_nil]
  rw [cyclePendant, spider, hsum, hes, ofEdges_cycleEdges_one_append]

/-! ### A cycle with a single pendant vertex -/

/-- A cycle carrying a single pendant vertex is a tadpole with a leg of length one. -/
@[toIsoGraph]
theorem cyclePendant_singleton_one (m : ℕ) : cyclePendant m [1] = tadpole m 1 := by
  rw [cyclePendant, tadpole, show ([1] : List ℕ).sum = 1 from rfl,
    show pendantEdges 0 m [1] = legEdges 0 m 1 from by
      simp [pendantEdges, legEdges, pathEdges]]

/-! ### Swapping the two centres of a double star -/

/-- The relabelling that exchanges the two centres of a double star, carrying the leaves of each
along with it. -/
def doubleStarSwapFwd (m n v : ℕ) : ℕ :=
  if v = 0 then 1 else if v = 1 then 0 else if v < 2 + m then v + n else v - m

theorem doubleStarSwapFwd_lt (m n v : ℕ) (h : v < 2 + m + n) :
    doubleStarSwapFwd m n v < 2 + n + m := by
  unfold doubleStarSwapFwd; split_ifs <;> omega

theorem doubleStarSwapFwd_fwd (m n v : ℕ) (h : v < 2 + m + n) :
    doubleStarSwapFwd n m (doubleStarSwapFwd m n v) = v := by
  unfold doubleStarSwapFwd
  split_ifs <;> first | omega | exact (‹False›).elim

/-- The relabelling that exchanges the two centres of a double star. -/
def doubleStarSwap (m n : ℕ) : Fin (2 + m + n) ≃ Fin (2 + n + m) where
  toFun p := ⟨doubleStarSwapFwd m n p.1, doubleStarSwapFwd_lt m n p.1 p.isLt⟩
  invFun p := ⟨doubleStarSwapFwd n m p.1, doubleStarSwapFwd_lt n m p.1 p.isLt⟩
  left_inv p := Fin.ext (doubleStarSwapFwd_fwd m n p.1 p.isLt)
  right_inv p := Fin.ext (doubleStarSwapFwd_fwd n m p.1 p.isLt)

@[simp] theorem doubleStarSwap_apply (m n : ℕ) (p : Fin (2 + m + n)) :
    (doubleStarSwap m n p).1 = doubleStarSwapFwd m n p.1 := rfl

/-- Adjacency in `doubleStar m n`, phrased entirely in terms of the underlying naturals. -/
theorem doubleStar_adj_val (m n : ℕ) (u v : (doubleStar m n).V) :
    (doubleStar m n).Adj u v = true ↔
      (u.1 ≠ v.1 ∧
        (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
            (u.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + n)) ∨
          ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + m) ∨
            (v.1 = 1 ∧ 2 + m ≤ u.1 ∧ u.1 < 2 + m + n)))) := by
  simp only [doubleStar]
  rw [ofEdges_adj_val]
  simp only [mem_doubleStarEdges]

/-! ### Theta graphs with two paths: the cycle -/

/-- Adjacency in `cycle n`, phrased entirely in terms of the underlying naturals. -/
theorem cycle_adj_val (n : ℕ) (u v : (cycle n).V) :
    (cycle n).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1 + 1) % n = v.1 ∨ (v.1 + 1) % n = u.1)) := by
  have huv : (u = v) ↔ (u.1 = v.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
  simp only [cycle, ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ne_eq, huv]

/-- One path of a theta graph splits off the front of the edge list. -/
theorem thetaEdges_cons (off k : ℕ) (rest : List ℕ) :
    thetaEdges off (k :: rest) = thetaEdges off [k] ++ thetaEdges (off + k) rest := by
  cases k with
  | zero => rfl
  | succ j => simp only [thetaEdges, List.append_nil, Nat.add_assoc]

theorem mem_thetaEdges_single (off k p q : ℕ) :
    ((p, q) ∈ thetaEdges off [k]) ↔
      ((k = 0 ∧ p = 0 ∧ q = 1) ∨ (0 < k ∧ p = 0 ∧ q = off) ∨
        (0 < k ∧ p = off + k - 1 ∧ q = 1) ∨ (off ≤ p ∧ q = p + 1 ∧ p + 1 < off + k)) := by
  rcases k with _ | j
  · simp only [thetaEdges, List.mem_singleton, Prod.mk.injEq, true_and]
    omega
  · simp only [thetaEdges, List.append_nil, List.mem_cons, List.mem_map, List.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    · rintro (⟨h, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h1, rfl, h3⟩)
      · exact absurd h (by omega)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨p - off, by omega, by omega, by omega⟩)

/-- The relabelling that reads a theta graph with two paths off as a cycle: the first path is
traversed away from the pole `0`, the second one back towards it. -/
def thetaCycleFwd (a b v : ℕ) : ℕ :=
  if v = 0 then 0 else if v = 1 then a + 1 else if v < 2 + a then v - 1 else 2 * a + b + 3 - v

/-- The inverse of `thetaCycleFwd`. -/
def thetaCycleBwd (a b u : ℕ) : ℕ :=
  if u = 0 then 0 else if u ≤ a then u + 1 else if u = a + 1 then 1 else 2 * a + b + 3 - u

theorem thetaCycleFwd_lt (a b v : ℕ) (h : v < 2 + a + b) : thetaCycleFwd a b v < 2 + a + b := by
  unfold thetaCycleFwd
  split_ifs <;> omega

theorem thetaCycleBwd_lt (a b u : ℕ) (h : u < 2 + a + b) : thetaCycleBwd a b u < 2 + a + b := by
  unfold thetaCycleBwd
  split_ifs <;> omega

theorem thetaCycleBwd_fwd (a b v : ℕ) (h : v < 2 + a + b) :
    thetaCycleBwd a b (thetaCycleFwd a b v) = v := by
  unfold thetaCycleFwd thetaCycleBwd
  split_ifs <;> first | omega | exact (‹False›).elim

theorem thetaCycleFwd_bwd (a b u : ℕ) (h : u < 2 + a + b) :
    thetaCycleFwd a b (thetaCycleBwd a b u) = u := by
  unfold thetaCycleFwd thetaCycleBwd
  split_ifs <;> first | omega | exact (‹False›).elim

/-- The relabelling of `thetaGraph [a, b]` as `cycle (2 + a + b)`. -/
def thetaCyclePerm (a b : ℕ) : Equiv.Perm (Fin (2 + a + b)) where
  toFun p := ⟨thetaCycleFwd a b p.1, thetaCycleFwd_lt a b p.1 p.isLt⟩
  invFun p := ⟨thetaCycleBwd a b p.1, thetaCycleBwd_lt a b p.1 p.isLt⟩
  left_inv p := Fin.ext (thetaCycleBwd_fwd a b p.1 p.isLt)
  right_inv p := Fin.ext (thetaCycleFwd_bwd a b p.1 p.isLt)

@[simp] theorem thetaCyclePerm_apply (a b : ℕ) (p : Fin (2 + a + b)) :
    (thetaCyclePerm a b p).1 = thetaCycleFwd a b p.1 := rfl

/-- The arithmetic heart of `thetaGraph_pair`: one step forward around the cycle is one edge of
the first path, or one edge of the second path taken backwards. -/
theorem thetaCycle_step (a b p q : ℕ) (hp : p < 2 + a + b) (hq : q < 2 + a + b) :
    ((thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q) ↔
      ((p, q) ∈ thetaEdges 2 [a] ∨ (q, p) ∈ thetaEdges (2 + a) [b]) := by
  rw [mem_thetaEdges_single, mem_thetaEdges_single, succ_mod_eq_iff (thetaCycleFwd_lt a b p hp)]
  constructor
  · intro h
    unfold thetaCycleFwd at h
    split_ifs at h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first
      | (exfalso; omega)
      | (refine Or.inl (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inl (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inl (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))) <;> omega)
  · intro h
    unfold thetaCycleFwd
    rcases h with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) |
      (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
      subst h2 <;>
      split_ifs <;>
      (try simp only [and_true, and_false, false_or, or_false]) <;>
      first | omega | exact (‹False›).elim

/-- One step forward around the cycle already forces the two endpoints apart. -/
theorem thetaCycle_step_ne (a b p q : ℕ) (hp : p < 2 + a + b)
    (h : (thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q) :
    thetaCycleFwd a b p ≠ thetaCycleFwd a b q := by
  intro he
  rw [← he] at h
  exact succ_mod_ne (by omega) (thetaCycleFwd_lt a b p hp) h

/-- Adjacency in `thetaGraph [a, b]` matches adjacency in `cycle (2 + a + b)` under
`thetaCycleFwd`. -/
theorem thetaCycle_adj_iff (a b p q : ℕ) (hp : p < 2 + a + b) (hq : q < 2 + a + b) :
    (thetaCycleFwd a b p ≠ thetaCycleFwd a b q ∧
        ((thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q ∨
          (thetaCycleFwd a b q + 1) % (2 + a + b) = thetaCycleFwd a b p)) ↔
      (p ≠ q ∧
        (((p, q) ∈ thetaEdges 2 [a] ∨ (p, q) ∈ thetaEdges (2 + a) [b]) ∨
          ((q, p) ∈ thetaEdges 2 [a] ∨ (q, p) ∈ thetaEdges (2 + a) [b]))) := by
  constructor
  · rintro ⟨hne, hs | hs⟩
    · refine ⟨fun he ↦ hne (by rw [he]), ?_⟩
      rcases (thetaCycle_step a b p q hp hq).1 hs with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)
    · refine ⟨fun he ↦ hne (by rw [he]), ?_⟩
      rcases (thetaCycle_step a b q p hq hp).1 hs with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
  · rintro ⟨-, (h | h) | (h | h)⟩
    · have hs := (thetaCycle_step a b p q hp hq).2 (Or.inl h)
      exact ⟨thetaCycle_step_ne a b p q hp hs, Or.inl hs⟩
    · have hs := (thetaCycle_step a b q p hq hp).2 (Or.inr h)
      exact ⟨fun he ↦ thetaCycle_step_ne a b q p hq hs he.symm, Or.inr hs⟩
    · have hs := (thetaCycle_step a b q p hq hp).2 (Or.inl h)
      exact ⟨fun he ↦ thetaCycle_step_ne a b q p hq hs he.symm, Or.inr hs⟩
    · have hs := (thetaCycle_step a b p q hp hq).2 (Or.inr h)
      exact ⟨thetaCycle_step_ne a b p q hp hs, Or.inl hs⟩

/-! ### Exchanging two blocks of vertices

The legs of a spider may be permuted, which on edge lists is the exchange of two adjacent blocks
of consecutive vertices.  This is the only relabelling in this file that acts on an edge list left
abstract: the parts of the list below and above the two blocks are arbitrary, subject only to
living on the vertices they are supposed to live on. -/

/-- Every vertex touched by `spiderEdges off ks` is either the centre `0` or one of the fresh
vertices in `[off, off + ks.sum)`; the second endpoint is always a fresh one. -/
theorem mem_spiderEdges_bound : ∀ (off : ℕ) (ks : List ℕ) (p q : ℕ),
    (p, q) ∈ spiderEdges off ks →
      (p = 0 ∨ (off ≤ p ∧ p < off + ks.sum)) ∧ (off ≤ q ∧ q < off + ks.sum)
  | _, [], _, _ => by simp [spiderEdges]
  | off, k :: rest, p, q => by
      intro h
      rw [spiderEdges, List.mem_append] at h
      simp only [List.sum_cons]
      rcases h with h | h
      · rw [mem_legEdges] at h
        omega
      · have := mem_spiderEdges_bound (off + k) rest p q h
        omega

/-- Exchange the blocks `[s, s + a)` and `[s + a, s + a + b)`, fixing everything else. -/
def swapBlocksFwd (s a b x : ℕ) : ℕ :=
  if x < s then x else if x < s + a then x + b else if x < s + a + b then x - a else x

theorem swapBlocksFwd_of_lt (s a b x : ℕ) (h : x < s) : swapBlocksFwd s a b x = x := by
  unfold swapBlocksFwd; rw [if_pos h]

theorem swapBlocksFwd_of_ge (s a b x : ℕ) (h : s + a + b ≤ x) : swapBlocksFwd s a b x = x := by
  unfold swapBlocksFwd; split_ifs <;> omega

theorem swapBlocksFwd_lt_iff (s a b x : ℕ) : swapBlocksFwd s a b x < s ↔ x < s := by
  unfold swapBlocksFwd; split_ifs <;> omega

theorem swapBlocksFwd_ge_iff (s a b x : ℕ) :
    s + a + b ≤ swapBlocksFwd s a b x ↔ s + a + b ≤ x := by
  unfold swapBlocksFwd; split_ifs <;> omega

theorem swapBlocksFwd_eq_zero_iff (s a b x : ℕ) (hs : 0 < s) :
    swapBlocksFwd s a b x = 0 ↔ x = 0 := by
  unfold swapBlocksFwd; split_ifs <;> omega

theorem swapBlocksFwd_lt (s a b N x : ℕ) (hN : s + a + b ≤ N) (hx : x < N) :
    swapBlocksFwd s a b x < N := by
  unfold swapBlocksFwd; split_ifs <;> omega

/-- Exchanging the two blocks back again is the identity: the inverse of `swapBlocksFwd s a b` is
`swapBlocksFwd s b a`. -/
theorem swapBlocksFwd_bwd (s a b x : ℕ) :
    swapBlocksFwd s b a (swapBlocksFwd s a b x) = x := by
  unfold swapBlocksFwd; split_ifs <;> omega

theorem swapBlocksFwd_inj (s a b u v : ℕ) (h : swapBlocksFwd s a b u = swapBlocksFwd s a b v) :
    u = v := by
  rw [← swapBlocksFwd_bwd s a b u, ← swapBlocksFwd_bwd s a b v, h]

/-- The block exchange as a permutation of `Fin N`. -/
def swapBlocks (s a b N : ℕ) (hN : s + a + b ≤ N) : Equiv.Perm (Fin N) where
  toFun p := ⟨swapBlocksFwd s a b p.1, swapBlocksFwd_lt s a b N p.1 hN p.isLt⟩
  invFun p := ⟨swapBlocksFwd s b a p.1,
    swapBlocksFwd_lt s b a N p.1 (by omega) p.isLt⟩
  left_inv p := Fin.ext (swapBlocksFwd_bwd s a b p.1)
  right_inv p := Fin.ext (swapBlocksFwd_bwd s b a p.1)

@[simp] theorem swapBlocks_apply (s a b N : ℕ) (hN : s + a + b ≤ N) (p : Fin N) :
    (swapBlocks s a b N hN p).1 = swapBlocksFwd s a b p.1 := rfl

/-- The block exchange carries the two legs onto each other: the leg of length `a` starting at `s`
goes to the leg of length `a` starting at `s + b`, and the leg of length `b` starting at `s + a`
goes to the leg of length `b` starting at `s`.  Stated in the directed form, so that `omega` never
sees more than two disjuncts on either side. -/
theorem swapBlocks_leg_iff (s a b p q : ℕ) (hs : 0 < s) :
    (((swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ legEdges 0 s b) ∨
      ((swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ legEdges 0 (s + b) a)) ↔
    (((p, q) ∈ legEdges 0 s a) ∨ ((p, q) ∈ legEdges 0 (s + a) b)) := by
  simp only [mem_legEdges]
  unfold swapBlocksFwd
  -- Splitting the iff and the two disjunctions by hand keeps each `omega` call small, and trying
  -- `exfalso` first disposes of the impossible branches without any search over the goal.
  split_ifs <;> constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
    first
      | (exfalso; omega)
      | omega

/-- Exchanging two adjacent blocks of vertices is an isomorphism of `ofEdges` graphs, provided the
edge list splits as `P ++ (M ++ Q)` with `P` and `Q` supported on vertices the exchange fixes and
with `M` carried onto `M'`. -/
theorem nonempty_iso_ofEdges_swapBlocks (N s a b : ℕ) (P M M' Q : List (ℕ × ℕ))
    (hN : s + a + b ≤ N)
    (hP : ∀ p q : ℕ, (p, q) ∈ P → swapBlocksFwd s a b p = p ∧ swapBlocksFwd s a b q = q)
    (hQ : ∀ p q : ℕ, (p, q) ∈ Q → swapBlocksFwd s a b p = p ∧ swapBlocksFwd s a b q = q)
    (hM : ∀ p q : ℕ,
      ((swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ M') ↔ ((p, q) ∈ M)) :
    Nonempty (ofEdges N (P ++ (M ++ Q)) ≃cg ofEdges N (P ++ (M' ++ Q))) := by
  have hfix : ∀ R : List (ℕ × ℕ),
      (∀ p q : ℕ, (p, q) ∈ R → swapBlocksFwd s a b p = p ∧ swapBlocksFwd s a b q = q) →
      ∀ u v : ℕ, ((swapBlocksFwd s a b u, swapBlocksFwd s a b v) ∈ R) ↔ ((u, v) ∈ R) := by
    intro R hR u v
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := hR _ _ h
      rwa [swapBlocksFwd_inj s a b _ _ h1, swapBlocksFwd_inj s a b _ _ h2] at h
    · intro h
      obtain ⟨h1, h2⟩ := hR _ _ h
      rwa [h1, h2]
  have hPiff := hfix P hP
  have hQiff := hfix Q hQ
  set E : (ofEdges N (P ++ (M ++ Q))).V ≃ (ofEdges N (P ++ (M' ++ Q))).V :=
    swapBlocks s a b N hN with hE
  refine ⟨isoOfAdj E ?_⟩
  intro x y
  have hval : ∀ p : (ofEdges N (P ++ (M ++ Q))).V,
      (E p).1 = swapBlocksFwd s a b p.1 := fun _ ↦ rfl
  have hne : (swapBlocksFwd s a b x.1 ≠ swapBlocksFwd s a b y.1) ↔ (x.1 ≠ y.1) :=
    not_congr ⟨swapBlocksFwd_inj s a b x.1 y.1, fun h ↦ by rw [h]⟩
  rw [Bool.eq_iff_iff, ofEdges_adj_val, ofEdges_adj_val, hval x, hval y]
  simp only [List.mem_append]
  exact and_congr hne
    (or_congr (or_congr (hPiff _ _) (or_congr (hM _ _) (hQiff _ _)))
      (or_congr (hPiff _ _) (or_congr (hM _ _) (hQiff _ _))))

/-- Two legs hanging off the centre `0` may be exchanged.  `P` is the part of the edge list that
lives below the two blocks and `Q` the part that lives above them (the centre `0`, which both may
touch, is fixed by the relabelling). -/
theorem nonempty_iso_ofEdges_swap_legs (N s a b : ℕ) (P Q : List (ℕ × ℕ))
    (hs : 0 < s) (hN : s + a + b ≤ N)
    (hP : ∀ p q : ℕ, (p, q) ∈ P → p < s ∧ q < s)
    (hQ : ∀ p q : ℕ, (p, q) ∈ Q → (p = 0 ∨ s + a + b ≤ p) ∧ s + a + b ≤ q) :
    Nonempty (ofEdges N (P ++ (legEdges 0 s a ++ (legEdges 0 (s + a) b ++ Q)))
      ≃cg ofEdges N (P ++ (legEdges 0 s b ++ (legEdges 0 (s + b) a ++ Q)))) := by
  have hkey : ∀ u : ℕ, (u = 0 ∨ s + a + b ≤ u) → swapBlocksFwd s a b u = u := by
    rintro u (rfl | h)
    · exact swapBlocksFwd_of_lt s a b 0 hs
    · exact swapBlocksFwd_of_ge s a b u h
  have h := nonempty_iso_ofEdges_swapBlocks N s a b P
    (legEdges 0 s a ++ legEdges 0 (s + a) b) (legEdges 0 s b ++ legEdges 0 (s + b) a) Q hN
    (fun p q hpq ↦ ⟨swapBlocksFwd_of_lt s a b p (hP p q hpq).1,
      swapBlocksFwd_of_lt s a b q (hP p q hpq).2⟩)
    (fun p q hpq ↦ ⟨hkey p (hQ p q hpq).1, hkey q (Or.inr (hQ p q hpq).2)⟩)
    (fun p q ↦ by simp only [List.mem_append]; exact swapBlocks_leg_iff s a b p q hs)
  rwa [List.append_assoc, List.append_assoc] at h

/-! ### Exchanging two paths of a theta graph -/

/-- The block exchange carries the path with `a` internal vertices onto the copy of it that starts
`b` further along. -/
theorem swapBlocksFwd_theta_fst (s a b p q : ℕ) (hs : 2 ≤ s)
    (h : (p, q) ∈ thetaEdges s [a]) :
    (swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ thetaEdges (s + b) [a] := by
  rw [mem_thetaEdges_single] at h ⊢
  unfold swapBlocksFwd
  -- Naming the disjunct to prove keeps each `omega` call small; left with the four-fold
  -- disjunction as its goal it would search the whole case tree.
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine Or.inl ⟨?_, ?_, ?_⟩ <;> omega)
      | (refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)) <;> omega)

/-- The block exchange carries the path with `b` internal vertices back onto the first block. -/
theorem swapBlocksFwd_theta_snd (s a b p q : ℕ) (hs : 2 ≤ s)
    (h : (p, q) ∈ thetaEdges (s + a) [b]) :
    (swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ thetaEdges s [b] := by
  rw [mem_thetaEdges_single] at h ⊢
  unfold swapBlocksFwd
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine Or.inl ⟨?_, ?_, ?_⟩ <;> omega)
      | (refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)) <;> omega)

theorem swapBlocks_theta_iff (s a b p q : ℕ) (hs : 2 ≤ s) :
    (((swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ thetaEdges s [b]) ∨
      ((swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ thetaEdges (s + b) [a])) ↔
    (((p, q) ∈ thetaEdges s [a]) ∨ ((p, q) ∈ thetaEdges (s + a) [b])) := by
  constructor
  · rintro (h | h)
    · have h' := swapBlocksFwd_theta_fst s b a _ _ hs h
      rw [swapBlocksFwd_bwd, swapBlocksFwd_bwd] at h'
      exact Or.inr h'
    · have h' := swapBlocksFwd_theta_snd s b a _ _ hs h
      rw [swapBlocksFwd_bwd, swapBlocksFwd_bwd] at h'
      exact Or.inl h'
  · rintro (h | h)
    · exact Or.inr (swapBlocksFwd_theta_fst s a b p q hs h)
    · exact Or.inl (swapBlocksFwd_theta_snd s a b p q hs h)

/-- The paths of a theta graph split along a split of the list of path lengths. -/
theorem thetaEdges_append : ∀ (pre post : List ℕ) (off : ℕ),
    thetaEdges off (pre ++ post) = thetaEdges off pre ++ thetaEdges (off + pre.sum) post
  | [], _, off => by rw [List.nil_append, thetaEdges, List.nil_append, List.sum_nil, Nat.add_zero]
  | k :: pre, post, off => by
      rw [List.cons_append, thetaEdges_cons, thetaEdges_append pre post (off + k),
        thetaEdges_cons off k pre, List.append_assoc, List.sum_cons,
        show off + k + pre.sum = off + (k + pre.sum) from by omega]

/-- Every vertex touched by `thetaEdges off ks` is either a pole or one of the fresh vertices in
`[off, off + ks.sum)`. -/
theorem mem_thetaEdges_bound : ∀ (off : ℕ) (ks : List ℕ) (p q : ℕ),
    (p, q) ∈ thetaEdges off ks →
      (p < 2 ∨ (off ≤ p ∧ p < off + ks.sum)) ∧ (q < 2 ∨ (off ≤ q ∧ q < off + ks.sum))
  | _, [], _, _ => by simp [thetaEdges]
  | off, k :: rest, p, q => by
      intro h
      rw [thetaEdges_cons, List.mem_append] at h
      simp only [List.sum_cons]
      rcases h with h | h
      · rw [mem_thetaEdges_single] at h
        omega
      · have := mem_thetaEdges_bound (off + k) rest p q h
        omega

/-- Two paths of a theta graph may be exchanged, up to the relabelling that swaps the two blocks
of internal vertices. -/
theorem nonempty_iso_ofEdges_swap_theta (N s a b : ℕ) (P Q : List (ℕ × ℕ))
    (hs : 2 ≤ s) (hN : s + a + b ≤ N)
    (hP : ∀ p q : ℕ, (p, q) ∈ P → p < s ∧ q < s)
    (hQ : ∀ p q : ℕ, (p, q) ∈ Q →
      (p < 2 ∨ s + a + b ≤ p) ∧ (q < 2 ∨ s + a + b ≤ q)) :
    Nonempty (ofEdges N (P ++ ((thetaEdges s [a] ++ thetaEdges (s + a) [b]) ++ Q))
      ≃cg ofEdges N (P ++ ((thetaEdges s [b] ++ thetaEdges (s + b) [a]) ++ Q))) := by
  have hkey : ∀ u : ℕ, (u < 2 ∨ s + a + b ≤ u) → swapBlocksFwd s a b u = u := by
    rintro u (h | h)
    · exact swapBlocksFwd_of_lt s a b u (by omega)
    · exact swapBlocksFwd_of_ge s a b u h
  exact nonempty_iso_ofEdges_swapBlocks N s a b P _ _ Q hN
    (fun p q hpq ↦ ⟨swapBlocksFwd_of_lt s a b p (hP p q hpq).1,
      swapBlocksFwd_of_lt s a b q (hP p q hpq).2⟩)
    (fun p q hpq ↦ ⟨hkey p (hQ p q hpq).1, hkey q (hQ p q hpq).2⟩)
    (fun p q ↦ by simp only [List.mem_append]; exact swapBlocks_theta_iff s a b p q hs)

/-! ### Theta graphs whose paths all carry one internal vertex -/

/-- The edges of such a theta graph: each of the `j` midpoints is joined to both poles. -/
theorem mem_thetaEdges_replicate_one : ∀ (j off p q : ℕ),
    ((p, q) ∈ thetaEdges off (List.replicate j 1)) ↔
      ((p = 0 ∧ off ≤ q ∧ q < off + j) ∨ (off ≤ p ∧ p < off + j ∧ q = 1))
  | 0, off, p, q => by
      simp only [List.replicate_zero, thetaEdges, List.not_mem_nil, false_iff]
      omega
  | j + 1, off, p, q => by
      rw [List.replicate_succ, thetaEdges_cons, List.mem_append, mem_thetaEdges_single,
        mem_thetaEdges_replicate_one j (off + 1) p q]
      omega

/-! ## Two-colourings of the decorated families

A spider, a cycle with pendant vertices, and a tadpole are all two-colourable, but the colour of a
vertex is not a function of its number alone: it depends on which leg or which pendant block the
vertex sits in.  The two functions here recover that information from the list of block lengths,
by the same recursion the edge lists themselves are built by. -/

/-! ### The distance from the centre of a spider -/

/-- The distance from the centre `0` to the vertex `v` of a spider whose legs, of lengths `ks`,
start at `off`.  Vertices below `off` — the centre — are at distance `0`. -/
def spiderDepth : ℕ → List ℕ → ℕ → ℕ
  | _, [], _ => 0
  | off, k :: rest, v =>
      if v < off then 0 else if v < off + k then v - off + 1 else spiderDepth (off + k) rest v

theorem spiderDepth_of_lt : ∀ (off : ℕ) (ks : List ℕ) (v : ℕ), v < off → spiderDepth off ks v = 0
  | _, [], _, _ => rfl
  | off, k :: rest, v, h => by rw [spiderDepth, if_pos h]

theorem spiderDepth_cons_of_ge (off k : ℕ) (rest : List ℕ) (v : ℕ) (h : off + k ≤ v) :
    spiderDepth off (k :: rest) v = spiderDepth (off + k) rest v := by
  rw [spiderDepth, if_neg (by omega), if_neg (by omega)]

/-- Along every edge of a spider the distance from the centre changes by one. -/
theorem spiderDepth_parity : ∀ (off : ℕ) (ks : List ℕ) (p q : ℕ), 0 < off →
    (p, q) ∈ spiderEdges off ks →
      (spiderDepth off ks p + spiderDepth off ks q) % 2 = 1
  | _, [], _, _, _ => by simp [spiderEdges]
  | off, k :: rest, p, q, hoff => by
      intro h
      rw [spiderEdges, List.mem_append] at h
      rcases h with h | h
      · rw [mem_legEdges] at h
        rcases h with ⟨rfl, rfl, hk⟩ | ⟨h1, rfl, h3⟩
        · rw [spiderDepth, if_pos hoff, spiderDepth, if_neg (by omega), if_pos (by omega)]
          omega
        · rw [spiderDepth, if_neg (by omega), if_pos (by omega), spiderDepth, if_neg (by omega),
            if_pos (by omega)]
          omega
      · have hb := mem_spiderEdges_bound (off + k) rest p q h
        have hp : spiderDepth off (k :: rest) p = spiderDepth (off + k) rest p := by
          rcases hb.1 with rfl | hp
          · rw [spiderDepth_of_lt _ _ _ hoff, spiderDepth_of_lt _ _ _ (by omega)]
          · exact spiderDepth_cons_of_ge off k rest p (by omega)
        rw [hp, spiderDepth_cons_of_ge off k rest q (by omega)]
        exact spiderDepth_parity (off + k) rest p q (by omega) h

/-! ### The owner of a pendant vertex -/

/-- For a vertex `x` of `cyclePendant m ks`: `x` itself if it lies on the cycle, and one more than
the cycle vertex it hangs off if it is a pendant.  Its parity is a proper two-colouring when the
cycle is even. -/
def pendantOwner (m : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ
  | _, _, [], x => x
  | v, off, k :: ks, x =>
      if x < m then x else if x < off + k then v + 1 else pendantOwner m (v + 1) (off + k) ks x

theorem pendantOwner_of_lt : ∀ (m v off : ℕ) (ks : List ℕ) (x : ℕ), x < m →
    pendantOwner m v off ks x = x
  | _, _, _, [], _, _ => rfl
  | m, v, off, _ :: _, x, h => by rw [pendantOwner, if_pos h]

/-- Every pendant edge runs from one of the cycle vertices `v, …, v + ks.length - 1` to a fresh
vertex in `[off, off + ks.sum)`. -/
theorem mem_pendantEdges_bound : ∀ (v off : ℕ) (ks : List ℕ) (p q : ℕ),
    (p, q) ∈ pendantEdges v off ks →
      (v ≤ p ∧ p < v + ks.length) ∧ (off ≤ q ∧ q < off + ks.sum)
  | _, _, [], _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, q => by
      intro h
      rw [pendantEdges, List.mem_append] at h
      simp only [List.length_cons, List.sum_cons]
      rcases h with h | h
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨i, hi, rfl, rfl⟩ := h
        omega
      · have := mem_pendantEdges_bound (v + 1) (off + k) ks p q h
        omega

/-- Along every pendant edge the parity of `pendantOwner` changes. -/
theorem pendantOwner_parity (m : ℕ) : ∀ (v off : ℕ) (ks : List ℕ) (p q : ℕ),
    v + ks.length ≤ m → m ≤ off → (p, q) ∈ pendantEdges v off ks →
      (pendantOwner m v off ks p + pendantOwner m v off ks q) % 2 = 1
  | _, _, [], _, _, _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, q, hv, hoff => by
      intro h
      rw [pendantEdges, List.mem_append] at h
      rcases h with h | h
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨i, hi, rfl, rfl⟩ := h
        rw [pendantOwner, if_pos (by simp only [List.length_cons] at hv; omega), pendantOwner,
          if_neg (by omega), if_pos (by omega)]
        omega
      · have hb := mem_pendantEdges_bound (v + 1) (off + k) ks p q h
        simp only [List.length_cons] at hv
        have hrec := pendantOwner_parity m (v + 1) (off + k) ks p q (by omega) (by omega) h
        rw [pendantOwner_of_lt m (v + 1) (off + k) ks p (by omega)] at hrec
        rwa [pendantOwner, if_pos (by omega), pendantOwner, if_neg (by omega), if_neg (by omega)]

/-! ### The distance from a pole of a theta graph -/

/-- The distance from the pole `0` to the vertex `v` of a theta graph whose paths, carrying the
numbers of internal vertices `xs`, start at `off` — except that the far pole `1` is given the
value `b`.  The parity of this is a proper two-colouring as soon as every path length `k`
satisfies `(k + b) % 2 = 1`: `b = 1` covers the paths with an even number of internal vertices,
which put the two poles in different classes, and `b = 0` the odd ones, which put them in the
same class. -/
def thetaDepth (b off : ℕ) (xs : List ℕ) (v : ℕ) : ℕ :=
  if v = 1 then b else spiderDepth off xs v

theorem thetaDepth_cons (b off k : ℕ) (rest : List ℕ) (v : ℕ) (hoff : 2 ≤ off)
    (h : v < 2 ∨ off + k ≤ v) :
    thetaDepth b off (k :: rest) v = thetaDepth b (off + k) rest v := by
  unfold thetaDepth
  split_ifs with hv
  · rfl
  · rcases h with h | h
    · rw [spiderDepth_of_lt _ _ _ (by omega), spiderDepth_of_lt _ _ _ (by omega)]
    · exact spiderDepth_cons_of_ge off k rest v h

/-- Along every edge of a theta graph whose path lengths all have the parity `b` asks for, the
parity of `thetaDepth` changes.  The far end of a path with `k` internal vertices is at distance
`k` from the near pole, so `(k + b) % 2 = 1` is exactly what makes the two poles disagree. -/
theorem thetaDepth_parity : ∀ (b off : ℕ) (xs : List ℕ) (p q : ℕ), 2 ≤ off →
    (∀ k ∈ xs, (k + b) % 2 = 1) → (p, q) ∈ thetaEdges off xs →
      (thetaDepth b off xs p + thetaDepth b off xs q) % 2 = 1
  | _, _, [], _, _, _, _ => by simp [thetaEdges]
  | b, off, k :: rest, p, q, hoff, hpar => by
      intro h
      rw [thetaEdges_cons, List.mem_append] at h
      have hk : (k + b) % 2 = 1 := hpar k (List.mem_cons_self ..)
      rcases h with h | h
      · rw [mem_thetaEdges_single] at h
        unfold thetaDepth
        rcases h with ⟨rfl, rfl, rfl⟩ | ⟨hk0, rfl, rfl⟩ | ⟨hk0, rfl, rfl⟩ | ⟨h1, rfl, h3⟩
        · rw [if_neg (by omega), if_pos rfl, spiderDepth, if_pos (by omega)]
          omega
        · rw [if_neg (by omega), if_neg (by omega), spiderDepth, if_pos (by omega), spiderDepth,
            if_neg (by omega), if_pos (by omega)]
          omega
        · rw [if_pos rfl, if_neg (by omega), spiderDepth, if_neg (by omega), if_pos (by omega)]
          omega
        · rw [if_neg (by omega), if_neg (by omega), spiderDepth, if_neg (by omega),
            if_pos (by omega), spiderDepth, if_neg (by omega), if_pos (by omega)]
          omega
      · have hb := mem_thetaEdges_bound (off + k) rest p q h
        rw [thetaDepth_cons b off k rest p hoff (by omega),
          thetaDepth_cons b off k rest q hoff (by omega)]
        exact thetaDepth_parity b (off + k) rest p q (by omega)
          (fun x hx ↦ hpar x (List.mem_cons_of_mem k hx)) h

/-- A graph given by an edge list is not bipartite once its edges include an odd cycle through
`0, 1, …, m-1`: walking `k ↦ k % m` around that cycle is a closed walk of odd length. -/
theorem not_isBipartite_ofEdges_of_odd_cycle (N m : ℕ) (es : List (ℕ × ℕ)) (hodd : m % 2 = 1)
    (h3 : 3 ≤ m) (hN : m ≤ N)
    (hsub : ∀ p q : ℕ, (p, q) ∈ cycleEdges m → ((p, q) ∈ es ∨ (q, p) ∈ es)) :
    ¬ (ofEdges N es).IsBipartite := by
  have hm : 0 < m := by omega
  refine not_isBipartite_of_odd_walk (G := ofEdges N es)
    (fun k ↦ (⟨k % m, Nat.lt_of_lt_of_le (Nat.mod_lt _ hm) hN⟩ : Fin N)) m hodd ?_
    (Fin.ext (by simp))
  intro k hk
  dsimp only
  have h1 : k % m = k := Nat.mod_eq_of_lt hk
  rcases Nat.lt_or_ge (k + 1) m with h | h
  · have h2 : (k + 1) % m = k + 1 := Nat.mod_eq_of_lt h
    exact (ofEdges_adj_val N es _ _).2 ⟨by simp only [ne_eq, h1, h2]; omega,
      hsub _ _ ((mem_cycleEdges m _ _).2 (Or.inl ⟨by simp only [h1, h2], by simp only [h1]; omega⟩))⟩
  · have h2 : (k + 1) % m = 0 := by rw [show k + 1 = m by omega, Nat.mod_self]
    exact (ofEdges_adj_val N es _ _).2 ⟨by simp only [ne_eq, h1, h2]; omega,
      hsub _ _ ((mem_cycleEdges m _ _).2 (Or.inr ⟨by simp only [h1]; omega, h2⟩))⟩

/-! ### Triangles and odd cycles in graphs on sets -/

/-- The block `[a, a + k)` as a `k`-element subset of `Fin n`. -/
private def kneserBlock (n k a : ℕ) (h : a + k ≤ n) : {s : Finset (Fin n) // s.card = k} :=
  ⟨(Finset.Ico a (a + k)).attachFin (fun x hx ↦ by
      simp only [Finset.mem_Ico] at hx; omega),
   by rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩

private theorem mem_kneserBlock {n k a : ℕ} {h : a + k ≤ n} (i : Fin n) :
    i ∈ (kneserBlock n k a h).1 ↔ a ≤ i.1 ∧ i.1 < a + k := by
  simp [kneserBlock, Finset.mem_attachFin]

private theorem mk_mem_kneserBlock {n k a : ℕ} {h : a + k ≤ n} (i : ℕ) (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∈ (kneserBlock n k a h).1 ↔ a ≤ i ∧ i < a + k := by
  simp [kneserBlock, Finset.mem_attachFin]

private theorem kneserBlock_ne {n k a b : ℕ} {ha : a + k ≤ n} {hb : b + k ≤ n} (hk : 0 < k)
    (hab : a ≠ b) : kneserBlock n k a ha ≠ kneserBlock n k b hb := by
  intro hEq
  have h1 : (⟨a, by omega⟩ : Fin n) ∈ (kneserBlock n k a ha).1 :=
    (mk_mem_kneserBlock _ _).2 (by omega)
  have h2 : (⟨b, by omega⟩ : Fin n) ∈ (kneserBlock n k b hb).1 :=
    (mk_mem_kneserBlock _ _).2 (by omega)
  rw [hEq, mk_mem_kneserBlock] at h1
  rw [← hEq, mk_mem_kneserBlock] at h2
  omega

/-- **Kneser graphs with room for three disjoint blocks are not bipartite.** -/
@[toIsoGraph]
theorem not_isBipartite_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    ¬ (CGraph.kneser n k).IsBipartite := by
  refine not_isBipartite_of_triangle
    (a := kneserBlock n k 0 (by omega)) (b := kneserBlock n k k (by omega))
    (d := kneserBlock n k (2 * k) (by omega)) ?_ ?_ ?_ <;>
  · rw [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨kneserBlock_ne hk (by omega), ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_kneserBlock, mem_kneserBlock] at hx
    omega

/-- The `(k+1)`-element subset `{0, …, k-1} ∪ {k + j}` of `Fin n`. -/
private def johnsonTri (n k j : ℕ) (h : k + j < n) : {s : Finset (Fin n) // s.card = k + 1} :=
  ⟨(insert (k + j) (Finset.range k)).attachFin (fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_range] at hx; omega),
   by rw [Finset.card_attachFin, Finset.card_insert_of_notMem (by simp), Finset.card_range]⟩

private theorem mem_johnsonTri {n k j : ℕ} {h : k + j < n} (i : Fin n) :
    i ∈ (johnsonTri n k j h).1 ↔ i.1 = k + j ∨ i.1 < k := by
  simp [johnsonTri, Finset.mem_attachFin]

private theorem mk_mem_johnsonTri {n k j : ℕ} {h : k + j < n} (i : ℕ) (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∈ (johnsonTri n k j h).1 ↔ i = k + j ∨ i < k := by
  simp [johnsonTri, Finset.mem_attachFin]

private theorem johnsonTri_ne {n k j j' : ℕ} {h : k + j < n} {h' : k + j' < n} (hjj : j ≠ j') :
    johnsonTri n k j h ≠ johnsonTri n k j' h' := by
  intro hEq
  have h1 : (⟨k + j, h⟩ : Fin n) ∈ (johnsonTri n k j h).1 :=
    (mk_mem_johnsonTri _ _).2 (Or.inl rfl)
  rw [hEq, mk_mem_johnsonTri] at h1
  omega

private theorem johnsonTri_inter {n k j j' : ℕ} {h : k + j < n} {h' : k + j' < n} (hjj : j ≠ j') :
    ((johnsonTri n k j h).1 ∩ (johnsonTri n k j' h').1).card = k := by
  have key : (johnsonTri n k j h).1 ∩ (johnsonTri n k j' h').1
      = (Finset.range k).attachFin (n := n) (fun x hx ↦ by
          simp only [Finset.mem_range] at hx; omega) := by
    ext i
    simp only [Finset.mem_inter, mem_johnsonTri, Finset.mem_attachFin, Finset.mem_range]
    omega
  rw [key, Finset.card_attachFin, Finset.card_range]

/-- **Johnson graphs on at least `k + 2` points are not bipartite.** -/
@[toIsoGraph]
theorem not_isBipartite_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    ¬ (CGraph.johnson n k).IsBipartite := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine not_isBipartite_of_triangle
    (a := johnsonTri n k 0 (by omega)) (b := johnsonTri n k 1 (by omega))
    (d := johnsonTri n k 2 (by omega)) ?_ ?_ ?_ <;>
  · rw [johnson_adj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.add_sub_cancel]
    exact ⟨johnsonTri_ne (by omega), johnsonTri_inter (by omega)⟩

/-- The outer five-cycle of the Petersen graph, as a walk in `kneser 5 2`. -/
private def petersenWalk (k : ℕ) : (CGraph.kneser 5 2).V :=
  if k % 5 = 0 then ⟨{0, 1}, by decide⟩
  else if k % 5 = 1 then ⟨{2, 3}, by decide⟩
  else if k % 5 = 2 then ⟨{4, 0}, by decide⟩
  else if k % 5 = 3 then ⟨{1, 2}, by decide⟩
  else ⟨{3, 4}, by decide⟩

/-- **The Petersen graph is not bipartite**: it has no triangle, but it does have a five-cycle. -/
theorem not_isBipartite_kneser_five_two : ¬ (CGraph.kneser 5 2).IsBipartite :=
  not_isBipartite_of_odd_walk petersenWalk 5 (by decide) (by decide) (by decide)

/-! ### Parity in the folded cube -/

/-- Positions where `x` and `y` are both `true` are counted twice on the right, so the number of
positions where they differ has the same parity as the total number of `true`s. -/
theorem card_ne_add_two_mul (n : ℕ) (x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ x i ≠ y i).card
        + 2 * (Finset.univ.filter fun i ↦ x i = true ∧ y i = true).card
      = (Finset.univ.filter fun i ↦ x i = true).card
        + (Finset.univ.filter fun i ↦ y i = true).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases x i <;> cases y i <;> simp

theorem card_ne_parity (n : ℕ) (x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ x i ≠ y i).card % 2
      = ((Finset.univ.filter fun i ↦ x i = true).card
          + (Finset.univ.filter fun i ↦ y i = true).card) % 2 := by
  have := card_ne_add_two_mul n x y
  omega

/-- The bit-string whose first `k` coordinates are `true`.  Running `k` from `0` to `n` walks from
one antipode of the cube to the other, one coordinate at a time. -/
def prefixVec (n k : ℕ) : Fin n → Bool := fun i ↦ decide (i.1 < k)

theorem card_prefixVec_step (n k : ℕ) (hk : k < n) :
    (Finset.univ.filter fun i ↦ prefixVec n k i ≠ prefixVec n (k + 1) i).card = 1 := by
  rw [show (Finset.univ.filter fun i ↦ prefixVec n k i ≠ prefixVec n (k + 1) i)
      = {(⟨k, hk⟩ : Fin n)} from ?_]
  · simp
  · ext i
    simp only [prefixVec, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, decide_eq_decide,
      Finset.mem_singleton, Fin.ext_iff]
    omega

theorem card_prefixVec_full (n : ℕ) :
    (Finset.univ.filter fun i ↦ prefixVec n 0 i ≠ prefixVec n n i).card = n := by
  rw [show (Finset.univ.filter fun i ↦ prefixVec n 0 i ≠ prefixVec n n i) = Finset.univ from ?_]
  · simp
  · ext i
    simp only [prefixVec, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, decide_eq_decide,
      iff_true]
    omega

/-! ## Two small facts about one-vertex graphs -/

/-- No vertex is adjacent to itself, as an equation of `Bool`s. -/
theorem adj_self (G : CGraph) (x : G.V) : G.Adj x x = false :=
  (Bool.not_eq_true _).mp (G.loopless x)


/-- A graph with a single vertex has no edges. -/
theorem adj_eq_false_of_subsingleton {G : CGraph} [Subsingleton G.V] (x y : G.V) :
    G.Adj x y = false := by
  cases Subsingleton.elim x y
  exact (Bool.not_eq_true _).mp (G.loopless x)

/-- Splitting the Hamming distance of two bit-strings of length `n + 1` off its first coordinate:
what `hypercube_succ` runs on. -/
theorem card_ne_succ (n : ℕ) (x y : Fin (n + 1) → Bool) :
    (Finset.univ.filter fun i : Fin (n + 1) ↦ x i ≠ y i).card
      = (if x 0 ≠ y 0 then 1 else 0)
        + (Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]

/-! ### The Cartesian product as a box product -/

/-- The Cartesian product is Mathlib's box product on the underlying simple graphs. -/
theorem toSimple_cartesianProduct (G H : CGraph) :
    (cartesianProduct G H).toSimple = SimpleGraph.boxProd G.toSimple H.toSimple := by
  ext p q
  simp only [CGraph.toSimple_adj, cartesianProduct_adj, SimpleGraph.boxProd_adj,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem isConnected_cartesianProduct_iff (G H : CGraph) :
    (cartesianProduct G H).IsConnected ↔ G.IsConnected ∧ H.IsConnected := by
  show (cartesianProduct G H).toSimple.Connected ↔ _
  rw [toSimple_cartesianProduct]
  exact SimpleGraph.connected_boxProd

/-- Euler's count for trees, on `CGraph`: a graph is a tree exactly when it is connected and has
one fewer edge than it has vertices. -/
@[toIsoGraph isTree_iff]
theorem isTree_iff_isConnected_and_E (G : CGraph) :
    G.IsTree ↔ G.IsConnected ∧ G.E + 1 = Fintype.card G.V := by
  show G.toSimple.IsTree ↔ _
  rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rfl

/-- A connected graph has at least one fewer edge than it has vertices. -/
@[toIsoGraph IsConnected.V_le_E_add_one]
theorem IsConnected.card_le_E_add_one {G : CGraph} (h : G.IsConnected) :
    Fintype.card G.V ≤ G.E + 1 := by
  have := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one h
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at this

/-- A graph with a positive edge count has an edge. -/
theorem exists_adj_of_E_pos {G : CGraph} (h : 0 < G.E) : ∃ a b, G.Adj a b := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he⟩

/-! ### The strong and lexicographic products contain the Cartesian one -/

theorem cartesianProduct_le_strongProduct (G H : CGraph) :
    (cartesianProduct G H).toSimple ≤ (strongProduct G H).toSimple := by
  intro p q hpq
  rw [CGraph.toSimple_adj, cartesianProduct_adj] at hpq
  rw [CGraph.toSimple_adj, strongProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hpq ⊢
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hpq
  · refine ⟨fun hq ↦ ?_, Or.inl h1, Or.inr h2⟩
    rw [hq, adj_self] at h2
    exact Bool.noConfusion h2
  · refine ⟨fun hq ↦ ?_, Or.inr h1, Or.inl h2⟩
    rw [hq, adj_self] at h1
    exact Bool.noConfusion h1

theorem cartesianProduct_le_lexProduct (G H : CGraph) :
    (cartesianProduct G H).toSimple ≤ (lexProduct G H).toSimple := by
  intro p q hpq
  rw [CGraph.toSimple_adj, cartesianProduct_adj] at hpq
  rw [CGraph.toSimple_adj, lexProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq ⊢
  tauto

@[toIsoGraph]
theorem isConnected_strongProduct {G H : CGraph}
    (hG : G.IsConnected) (hH : H.IsConnected) : (strongProduct G H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_strongProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

@[toIsoGraph]
theorem isConnected_lexProduct {G H : CGraph}
    (hG : G.IsConnected) (hH : H.IsConnected) : (lexProduct G H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_lexProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

/-! ### Triangles in the strong and lexicographic products -/

theorem not_isBipartite_strongProduct {G H : CGraph}
    {a b : G.V} {c d : H.V} (hab : G.Adj a b) (hcd : H.Adj c d) :
    ¬ (strongProduct G H).IsBipartite := by
  have hba : G.Adj b a := by rwa [G.symm]
  have hdc : H.Adj d c := by rwa [H.symm]
  refine not_isBipartite_of_triangle (a := (a, c)) (b := (b, d)) (d := (a, d)) ?_ ?_ ?_ <;>
  · rw [strongProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq, Prod.mk.injEq,
      not_and]
    refine ⟨?_, by tauto, by tauto⟩
    intro h1 h2
    first
      | (rw [h2, adj_self] at hcd; exact Bool.noConfusion hcd)
      | (rw [h1, adj_self] at hab; exact Bool.noConfusion hab)

theorem not_isBipartite_lexProduct {G H : CGraph}
    {a b : G.V} {c d : H.V} (hab : G.Adj a b) (hcd : H.Adj c d) :
    ¬ (lexProduct G H).IsBipartite := by
  have hba : G.Adj b a := by rwa [G.symm]
  refine not_isBipartite_of_triangle (a := (a, c)) (b := (a, d)) (d := (b, c)) ?_ ?_ ?_ <;>
  · rw [lexProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    tauto

@[simp, toIsoGraph]
theorem length_degSequence (G : CGraph) :
    G.degSequence.length = Fintype.card G.V := by
  rw [degSequence, degMultiset, Multiset.length_sort, Multiset.card_map, Finset.card_val,
    Finset.card_univ]

/-- The handshake lemma: the degrees add up to twice the edge count. -/
@[toIsoGraph]
theorem sum_degSequence (G : CGraph) : G.degSequence.sum = 2 * G.E := by
  have h : ((G.degSequence : List ℕ) : Multiset ℕ)
      = Finset.univ.val.map fun v ↦ G.toSimple.degree v := Multiset.sort_eq _ _
  have h2 : G.degSequence.sum = (Finset.univ.val.map fun v ↦ G.toSimple.degree v).sum := by
    rw [← h]; rfl
  rw [h2]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

/-- A regular graph has a constant degree sequence. -/
theorem degSequence_of_regular (G : CGraph) {k : ℕ} (h : G.toSimple.IsRegularOfDegree k) :
    G.degSequence = List.replicate (Fintype.card G.V) k := by
  rw [List.eq_replicate_iff]
  refine ⟨G.length_degSequence, fun b hb ↦ ?_⟩
  rw [degSequence, degMultiset, Multiset.mem_sort, Multiset.mem_map] at hb
  obtain ⟨v, -, rfl⟩ := hb
  exact h v

/-- Strongly regular graphs are regular, so their degree sequence is constant. -/
@[toIsoGraph]
theorem IsSRGWith.degSequence {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    G.degSequence = List.replicate n k := by
  rw [degSequence_of_regular G h.regular, h.card]

/-- Any sum over the vertices of a function of the degree is a sum over the degree sequence. -/
theorem sum_degSequence_map (G : CGraph) (f : ℕ → ℕ) :
    (G.degSequence.map f).sum = ∑ v : G.V, f (G.toSimple.degree v) := by
  have h : ((G.degSequence : List ℕ) : Multiset ℕ)
      = Finset.univ.val.map fun v ↦ G.toSimple.degree v := Multiset.sort_eq _ _
  have h2 : (G.degSequence.map f).sum = (((G.degSequence : List ℕ) : Multiset ℕ).map f).sum := rfl
  rw [h2, h, Multiset.map_map]
  rfl

/-- The line graph's edge count, phrased so that it only mentions the degree sequence. -/
theorem E_lineGraph_eq_sum_degSequence (G : CGraph) :
    (lineGraph G).E = (G.degSequence.map fun d ↦ d.choose 2).sum := by
  rw [sum_degSequence_map, E_lineGraph]

theorem degSequence_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.degSequence = List.replicate (Fintype.card G.V) k :=
  degSequence_of_regular G (isRegularOfDegree_of_card_nbrs G h)

@[simp, toIsoGraph] theorem degSequence_kneser {n k : ℕ} (hk : 1 ≤ k) :
    (kneser n k).degSequence = List.replicate (n.choose k) ((n - k).choose k) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_kneser hk), card_kneser]

@[simp] theorem degSequence_rook (m n : ℕ) :
    (rook m n).degSequence = List.replicate (m * n) ((n - 1) + (m - 1)) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_rook)]
  congr 1
  simp only [rook, card_cartesianProduct, card_complete]

variable {G H : CGraph}

/-! ### Neighbours in the four products -/

theorem nbrs_cartesianProduct (p : (cartesianProduct G H).V) :
    (cartesianProduct G H).nbrs p
      = (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) ∪ (G.nbrs p.1 ×ˢ ({p.2} : Finset H.V)) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, cartesianProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem card_nbrs_cartesianProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (cartesianProduct G H).V) : ((cartesianProduct G H).nbrs p).card = k + l := by
  rw [nbrs_cartesianProduct, Finset.card_union_of_disjoint, Finset.card_product,
    Finset.card_product, Finset.card_singleton, Finset.card_singleton, hG, hH, one_mul, mul_one,
    Nat.add_comm]
  refine Finset.disjoint_product.2 (Or.inr ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_tensorProduct (p : (tensorProduct G H).V) :
    (tensorProduct G H).nbrs p = G.nbrs p.1 ×ˢ H.nbrs p.2 := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, tensorProduct_adj]
  simp only [Finset.mem_product, mem_nbrs, Bool.and_eq_true]

theorem card_nbrs_tensorProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (tensorProduct G H).V) : ((tensorProduct G H).nbrs p).card = k * l := by
  rw [nbrs_tensorProduct, Finset.card_product, hG, hH]

theorem nbrs_lexProduct (p : (lexProduct G H).V) :
    (lexProduct G H).nbrs p
      = (G.nbrs p.1 ×ˢ (Finset.univ : Finset H.V)) ∪ (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, lexProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Finset.mem_univ, and_true, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

theorem card_nbrs_lexProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (lexProduct G H).V) :
    ((lexProduct G H).nbrs p).card = k * Fintype.card H.V + l := by
  rw [nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_univ, hG, hH, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_strongProduct (p : (strongProduct G H).V) :
    (strongProduct G H).nbrs p
      = ((G.nbrs p.1 ∪ {p.1}) ×ˢ (H.nbrs p.2 ∪ {p.2})) \ {p} := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, strongProduct_adj]
  simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_union,
    mem_nbrs, Finset.mem_singleton, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
  constructor
  · rintro ⟨hne, h1, h2⟩
    exact ⟨⟨h1.symm.imp id Eq.symm, h2.symm.imp id Eq.symm⟩, fun h ↦ hne h.symm⟩
  · rintro ⟨⟨h1, h2⟩, hne⟩
    exact ⟨fun h ↦ hne h.symm, h1.symm.imp Eq.symm id, h2.symm.imp Eq.symm id⟩

theorem card_nbrs_strongProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (strongProduct G H).V) :
    ((strongProduct G H).nbrs p).card = (k + 1) * (l + 1) - 1 := by
  have hdG : ((G.nbrs p.1 ∪ {p.1}) : Finset G.V).card = k + 1 := by
    rw [Finset.card_union_of_disjoint, Finset.card_singleton, hG]
    rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
    exact Bool.noConfusion
  have hdH : ((H.nbrs p.2 ∪ {p.2}) : Finset H.V).card = l + 1 := by
    rw [Finset.card_union_of_disjoint, Finset.card_singleton, hH]
    rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
    exact Bool.noConfusion
  have hmem : ({p} : Finset (G.V × H.V)) ⊆ (G.nbrs p.1 ∪ {p.1}) ×ˢ (H.nbrs p.2 ∪ {p.2}) := by
    rw [Finset.singleton_subset_iff, Finset.mem_product]
    exact ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _),
      Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  rw [nbrs_strongProduct, Finset.card_sdiff, Finset.inter_eq_left.2 hmem, Finset.card_product,
    hdG, hdH, Finset.card_singleton]

/-! ### Degree sequences of the four products -/

theorem degSequence_cartesianProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (cartesianProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_cartesianProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_cartesianProduct]

theorem degSequence_tensorProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (tensorProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k * l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_tensorProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_tensorProduct]

theorem degSequence_lexProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (lexProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k * Fintype.card H.V + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_lexProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_lexProduct]

theorem degSequence_strongProduct {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (strongProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) ((k + 1) * (l + 1) - 1) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_strongProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_strongProduct]

/-- An automorphism cannot change a degree, so a vertex-transitive graph is regular. -/
theorem degree_eq_of_isVertexTransitive {G : CGraph} (h : G.IsVertexTransitive) (u v : G.V) :
    G.toSimple.degree u = G.toSimple.degree v := by
  obtain ⟨σ, hσ⟩ := h u v
  rw [← hσ]
  exact (SimpleGraph.Iso.degree_eq σ.toSimpleIso u).symm

@[toIsoGraph]
theorem exists_degSequence_replicate_of_isVertexTransitive {G : CGraph}
    (h : G.IsVertexTransitive) : ∃ k, G.degSequence = List.replicate (Fintype.card G.V) k := by
  cases isEmpty_or_nonempty G.V with
  | inl hE =>
    refine ⟨0, ?_⟩
    have hnil : G.degSequence = [] :=
      List.eq_nil_of_length_eq_zero (by rw [length_degSequence]; exact Fintype.card_eq_zero)
    rw [hnil, Fintype.card_eq_zero]
    rfl
  | inr hN =>
    obtain ⟨v₀⟩ := hN
    exact ⟨G.toSimple.degree v₀,
      degSequence_of_regular G fun v ↦ degree_eq_of_isVertexTransitive h v v₀⟩

/-! ### Graphs of diameter two -/

/-- If `u` and `v` are equal, adjacent, or joined by a path of length two, they are at distance
at most two. -/
theorem edist_le_two {G : CGraph} {u v : G.V}
    (h : u = v ∨ G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v) :
    G.toSimple.edist u v ≤ 2 := by
  rcases h with rfl | hadj | ⟨w, h1, h2⟩
  · simp
  · rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]
    norm_num
  · refine le_trans (SimpleGraph.edist_le
      (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))) ?_
    simp

/-- A *two-step* graph: any two distinct vertices are adjacent or have a common neighbour. -/
theorem ediam_le_two (G : CGraph)
    (h : ∀ u v : G.V, u ≠ v → G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v) :
    G.toSimple.ediam ≤ 2 :=
  SimpleGraph.ediam_le_of_edist_le fun u v ↦
    edist_le_two (by by_cases huv : u = v; exacts [Or.inl huv, Or.inr (h u v huv)])

theorem diameter_le_two (G : CGraph)
    (h : ∀ u v : G.V, u ≠ v → G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v) :
    G.diameter ≤ 2 := by
  have h2 := ENat.toNat_le_toNat (G.ediam_le_two h) (by simp)
  simpa [diameter, SimpleGraph.diam] using h2

/-- A two-step graph with a non-adjacent pair has diameter exactly two. -/
theorem diameter_eq_two (G : CGraph)
    (h : ∀ u v : G.V, u ≠ v → G.toSimple.Adj u v ∨ ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v)
    {u v : G.V} (hne : u ≠ v) (hadj : ¬ G.toSimple.Adj u v) : G.diameter = 2 := by
  have h1 : 1 ≤ G.toSimple.edist u v :=
    ENat.one_le_iff_ne_zero.2 fun h0 ↦ hne (SimpleGraph.edist_eq_zero_iff.1 h0)
  have h2 : G.toSimple.edist u v ≠ 1 := fun he ↦ hadj (SimpleGraph.edist_eq_one_iff_adj.1 he)
  have h3 : (2 : ℕ∞) ≤ G.toSimple.edist u v := by
    have := Order.add_one_le_of_lt (lt_of_le_of_ne h1 (Ne.symm h2))
    simpa using this
  have heq : G.toSimple.ediam = 2 :=
    le_antisymm (G.ediam_le_two h) (le_trans h3 SimpleGraph.edist_le_ediam)
  rw [diameter, SimpleGraph.diam, heq]
  rfl

/-- A graph with a nonzero diameter is connected: the diameter of a disconnected graph is `0` by
convention. -/
@[toIsoGraph]
theorem isConnected_of_diameter_ne_zero (G : CGraph) (h : G.diameter ≠ 0) : G.IsConnected := by
  have hnt : Nontrivial G.V := SimpleGraph.nontrivial_of_diam_ne_zero h
  exact SimpleGraph.connected_of_ediam_ne_top (SimpleGraph.ediam_ne_top_of_diam_ne_zero h)

/-! ### Strongly regular graphs of diameter two -/

/-- In a strongly regular graph with `μ > 0`, any two distinct non-adjacent vertices have a
common neighbour — that is what `μ` counts. -/
theorem IsSRGWith.exists_common_neighbor {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hμ : 0 < μ) {u v : G.V} (hne : u ≠ v) (hadj : ¬ G.toSimple.Adj u v) :
    ∃ w, G.toSimple.Adj u w ∧ G.toSimple.Adj w v := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hcard : 0 < Fintype.card (G.toSimple.commonNeighbors u v) := by
    rw [h'.of_not_adj hne hadj]; exact hμ
  obtain ⟨w, hw⟩ := Fintype.card_pos_iff.1 hcard
  exact ⟨w, hw.1, hw.2.symm⟩

/-- A strongly regular graph that is not complete has a non-adjacent pair. -/
theorem IsSRGWith.exists_not_adj {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hk : k + 1 < n) : ∃ u v : G.V, u ≠ v ∧ ¬ G.toSimple.Adj u v := by
  classical
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have hn : Fintype.card G.V = n := h'.card
  obtain ⟨u⟩ := Fintype.card_pos_iff.1 (show 0 < Fintype.card G.V by omega)
  by_contra hcon
  push_neg at hcon
  have hnbrs : G.nbrs u = Finset.univ.erase u := by
    ext w
    simp only [mem_nbrs, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hw
      rintro rfl
      rw [adj_self] at hw
      exact Bool.noConfusion hw
    · intro hw
      exact hcon u w (Ne.symm hw)
  have hcard : (G.nbrs u).card = k := by rw [card_nbrs_eq_degree, h'.regular u]
  rw [hnbrs, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hn] at hcard
  omega

/-- **A strongly regular graph with `μ > 0` is connected**: any two non-adjacent vertices are
joined by a path of length two. -/
@[toIsoGraph]
theorem IsSRGWith.isConnected {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) (hμ : 0 < μ)
    (hn : 0 < n) : G.IsConnected := by
  have h' : G.toSimple.IsSRGWith n k ℓ μ := h
  have : Nonempty G.V := Fintype.card_pos_iff.1 (by rw [h'.card]; exact hn)
  refine SimpleGraph.connected_of_ediam_ne_top (ne_top_of_le_ne_top (by simp) (G.ediam_le_two ?_))
  intro u v huv
  by_cases hadj : G.toSimple.Adj u v
  · exact Or.inl hadj
  · exact Or.inr (h.exists_common_neighbor hμ huv hadj)

/-- **A strongly regular graph with `μ > 0` that is not complete has diameter two.** -/
@[toIsoGraph]
theorem IsSRGWith.diameter_eq_two {G : CGraph} {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hμ : 0 < μ) (hk : k + 1 < n) : G.diameter = 2 := by
  obtain ⟨u, v, hne, hadj⟩ := h.exists_not_adj hk
  refine G.diameter_eq_two (fun a b hab ↦ ?_) hne hadj
  by_cases hab2 : G.toSimple.Adj a b
  · exact Or.inl hab2
  · exact Or.inr (h.exists_common_neighbor hμ hab hab2)

/-! ### Joins have diameter at most two -/

/-- A graph with fewer than `V choose 2` edges has a non-adjacent pair: if every two distinct
vertices were adjacent it would be regular of degree `V - 1`, and the handshake lemma would make
the edge count exactly `V choose 2`. -/
theorem exists_not_adj_of_E_lt (G : CGraph) (h : G.E < (Fintype.card G.V).choose 2) :
    ∃ u v : G.V, u ≠ v ∧ G.Adj u v = false := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ u v : G.V, u ≠ v → G.Adj u v = true := by
    intro u v huv
    simpa using hcon u v huv
  have hnbrs : ∀ u : G.V, (G.nbrs u).card = Fintype.card G.V - 1 := by
    intro u
    have hu : G.nbrs u = Finset.univ.erase u := by
      ext w
      simp only [mem_nbrs, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro hw rfl
        rw [adj_self] at hw
        exact Bool.noConfusion hw
      · intro hw
        exact hall u w (Ne.symm hw)
    rw [hu, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
  have h2 : 2 * G.E = Fintype.card G.V * (Fintype.card G.V - 1) := by
    rw [← sum_degSequence, degSequence_of_card_nbrs G hnbrs, List.sum_replicate, smul_eq_mul]
  rw [Nat.choose_two_right] at h
  set m := Fintype.card G.V * (Fintype.card G.V - 1) with hm
  omega

/-- In a join, two vertices on the same side have a common neighbour on the other side, and two
vertices on opposite sides are adjacent. -/
theorem two_step_join (G H : CGraph) [Nonempty G.V]
    [Nonempty H.V] (u v : (join G H).V) (huv : u ≠ v) :
    (join G H).toSimple.Adj u v ∨
      ∃ w, (join G H).toSimple.Adj u w ∧ (join G H).toSimple.Adj w v := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  rcases u with a | b <;> rcases v with c | d
  · exact Or.inr ⟨Sum.inr b₀, by simp, by simp⟩
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inr ⟨Sum.inl a₀, by simp, by simp⟩

@[toIsoGraph]
theorem diameter_join_le_two (G H : CGraph) [Nonempty G.V]
    [Nonempty H.V] : (join G H).diameter ≤ 2 :=
  diameter_le_two _ (two_step_join G H)

/-- A join is of diameter exactly two as soon as one side has a non-adjacent pair. -/
theorem diameter_join_of_not_adj (G H : CGraph)
    [Nonempty H.V] {a c : G.V} (hne : a ≠ c) (hadj : G.Adj a c = false) :
    (join G H).diameter = 2 := by
  haveI : Nonempty G.V := ⟨a⟩
  refine diameter_eq_two _ (two_step_join G H) (u := Sum.inl a) (v := Sum.inl c) ?_ ?_
  · exact fun h ↦ hne (Sum.inl.inj h)
  · simp [hadj]

/-! ### The complement of a disconnected graph -/

/-- Unreachable vertices are adjacent in the complement. -/
theorem compl_adj_of_not_reachable (G : CGraph) {u w : G.V}
    (h : ¬ G.toSimple.Reachable u w) : Gᶜ.toSimple.Adj u w := by
  have hne : u ≠ w := by rintro rfl; exact h (SimpleGraph.Reachable.refl u)
  have hadj : G.Adj u w = false := by
    by_contra hc
    exact h (SimpleGraph.Adj.reachable (show G.toSimple.Adj u w by simpa using hc))
  simp [hadj, hne]

/-- **The complement of a disconnected graph is a two-step graph.**  Two vertices in different
components are already adjacent in the complement; two vertices in the same component are both
non-adjacent to anything in another component. -/
theorem two_step_compl (G : CGraph) (h : ¬ G.toSimple.Preconnected)
    (u v : G.V) (_huv : u ≠ v) :
    Gᶜ.toSimple.Adj u v ∨
      ∃ w, Gᶜ.toSimple.Adj u w ∧ Gᶜ.toSimple.Adj w v := by
  by_cases hr : G.toSimple.Reachable u v
  · obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ G.toSimple.Reachable x y := by
      unfold SimpleGraph.Preconnected at h
      push_neg at h
      exact h
    have key : ∀ w : G.V, ¬ G.toSimple.Reachable u w →
        Gᶜ.toSimple.Adj u w ∧ Gᶜ.toSimple.Adj w v := fun w hw ↦
      ⟨G.compl_adj_of_not_reachable hw,
        (G.compl_adj_of_not_reachable fun hvw ↦ hw (hr.trans hvw)).symm⟩
    by_cases hux : G.toSimple.Reachable u x
    · exact Or.inr ⟨y, key y fun huy ↦ hxy (hux.symm.trans huy)⟩
    · exact Or.inr ⟨x, key x hux⟩
  · exact Or.inl (G.compl_adj_of_not_reachable hr)

theorem diameter_compl_le_two (G : CGraph) (h : ¬ G.toSimple.Preconnected) :
    Gᶜ.diameter ≤ 2 :=
  diameter_le_two _ (two_step_compl G h)

/-- **The complement of a disconnected graph is connected.** -/
theorem isConnected_compl_of_not_preconnected (G : CGraph) [Nonempty G.V]
    (h : ¬ G.toSimple.Preconnected) : Gᶜ.IsConnected := by
  haveI : Nonempty Gᶜ.V := ‹Nonempty G.V›
  exact SimpleGraph.connected_of_ediam_ne_top
    (ne_top_of_le_ne_top (by simp) (ediam_le_two _ (two_step_compl G h)))

/-- If the graph is disconnected and has an edge, its complement has diameter exactly two. -/
theorem diameter_compl_eq_two (G : CGraph) (h : ¬ G.toSimple.Preconnected)
    (hE : 0 < G.E) : Gᶜ.diameter = 2 := by
  obtain ⟨u, v, hne, hadj⟩ := exists_not_adj_of_E_lt Gᶜ
    (show Gᶜ.E < (Fintype.card G.V).choose 2 by have hc := G.E_compl; omega)
  refine diameter_eq_two _ (two_step_compl G h) hne fun hc ↦ ?_
  have hc' : Gᶜ.Adj u v = true := by simpa using hc
  rw [hc'] at hadj
  exact Bool.noConfusion hadj

/-! ### Degree multisets of the binary constructions -/

private theorem univ_val_sum (α β : Type*) [Fintype α] [Fintype β] :
    (Finset.univ : Finset (α ⊕ β)).val
      = (Finset.univ : Finset α).val.map Sum.inl + (Finset.univ : Finset β).val.map Sum.inr :=
  rfl

theorem nbrs_disjUnion_inl (G H : CGraph) (a : G.V) :
    (disjUnion G H).nbrs (Sum.inl a) = (G.nbrs a).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem nbrs_disjUnion_inr (G H : CGraph) (b : H.V) :
    (disjUnion G H).nbrs (Sum.inr b) = (H.nbrs b).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem degree_disjUnion_inl (G H : CGraph) (a : G.V) :
    (disjUnion G H).toSimple.degree (Sum.inl a) = G.toSimple.degree a := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_disjUnion_inl, Finset.card_map]

theorem degree_disjUnion_inr (G H : CGraph) (b : H.V) :
    (disjUnion G H).toSimple.degree (Sum.inr b) = H.toSimple.degree b := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_disjUnion_inr, Finset.card_map]

/-- **The degree multiset of a disjoint union** is the sum of the two degree multisets. -/
@[toIsoGraph]
theorem degMultiset_disjUnion (G H : CGraph) :
    (disjUnion G H).degMultiset = G.degMultiset + H.degMultiset := by
  unfold degMultiset
  rw [univ_val_sum, Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · exact Multiset.map_congr rfl fun v _ ↦ degree_disjUnion_inl G H v
  · exact Multiset.map_congr rfl fun v _ ↦ degree_disjUnion_inr G H v

theorem nbrs_compl (G : CGraph) (v : G.V) :
    Gᶜ.nbrs v = (G.nbrs v)ᶜ.erase v := by
  ext w
  simp only [mem_nbrs, compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true',
    Finset.mem_erase, Finset.mem_compl, Bool.not_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun he ↦ h1 he.symm, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun he ↦ h1 he.symm, h2⟩

theorem degree_compl (G : CGraph) (v : G.V) :
    Gᶜ.toSimple.degree v = Fintype.card G.V - 1 - G.toSimple.degree v := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_compl]
  have hv : v ∈ (G.nbrs v)ᶜ := by simp [adj_self]
  rw [Finset.card_erase_of_mem hv, Finset.card_compl]
  omega

theorem degree_le (G : CGraph) (v : G.V) :
    G.toSimple.degree v + 1 ≤ Fintype.card G.V := by
  rw [← card_nbrs_eq_degree]
  have hv : v ∉ G.nbrs v := by simp [adj_self]
  have hsub := Finset.card_le_card (Finset.subset_univ (insert v (G.nbrs v)))
  rw [Finset.card_insert_of_notMem hv, Finset.card_univ] at hsub
  omega

theorem degree_join_inl (G H : CGraph) (a : G.V) :
    (join G H).toSimple.degree (Sum.inl a) = G.toSimple.degree a + Fintype.card H.V := by
  have hd := G.degree_le a
  show ((disjUnion Gᶜ Hᶜ)ᶜ).toSimple.degree (Sum.inl a) = _
  rw [degree_compl, degree_disjUnion_inl, degree_compl, card_disjUnion, card_compl, card_compl]
  omega

theorem degree_join_inr (G H : CGraph) (b : H.V) :
    (join G H).toSimple.degree (Sum.inr b) = Fintype.card G.V + H.toSimple.degree b := by
  have hd := H.degree_le b
  show ((disjUnion Gᶜ Hᶜ)ᶜ).toSimple.degree (Sum.inr b) = _
  rw [degree_compl, degree_disjUnion_inr, degree_compl, card_disjUnion, card_compl, card_compl]
  omega

/-- **The degree multiset of a join**: every vertex picks up all the vertices on the other side. -/
theorem degMultiset_join (G H : CGraph) :
    (join G H).degMultiset = G.degMultiset.map (· + Fintype.card H.V)
      + H.degMultiset.map (· + Fintype.card G.V) := by
  unfold degMultiset
  rw [univ_val_sum, Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map,
    Multiset.map_map]
  congr 1
  · exact Multiset.map_congr rfl fun v _ ↦ degree_join_inl G H v
  · refine Multiset.map_congr rfl fun v _ ↦ ?_
    show (join G H).toSimple.degree (Sum.inr v) = H.toSimple.degree v + Fintype.card G.V
    rw [degree_join_inr, Nat.add_comm]

/-- **The degree multiset of the complement**: every degree is replaced by its "co-degree". -/
theorem degMultiset_compl (G : CGraph) :
    Gᶜ.degMultiset = G.degMultiset.map (fun d ↦ Fintype.card G.V - 1 - d) := by
  unfold degMultiset
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun v _ ↦ degree_compl G v

/-! ### The degrees of a path -/

theorem path_adj {n : ℕ} (i j : Fin n) :
    (path n).Adj i j = (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) :=
  rfl

theorem mem_nbrs_path {n : ℕ} (i j : Fin n) :
    j ∈ (path n).nbrs i ↔ j.1 = i.1 + 1 ∨ i.1 = j.1 + 1 := by
  rw [mem_nbrs, path_adj]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq, Fin.ext_iff]
  omega

theorem card_nbrs_path {n : ℕ} (i : Fin n) :
    ((path n).nbrs i).card = (if i.1 + 1 < n then 1 else 0) + (if 0 < i.1 then 1 else 0) := by
  have hi := i.isLt
  by_cases hn : i.1 + 1 < n <;> by_cases h0 : 0 < i.1
  · have h : (path n).nbrs i = ({⟨i.1 - 1, by omega⟩, ⟨i.1 + 1, hn⟩} : Finset (Fin n)) :=
      @Finset.ext (Fin n) _ _ fun j ↦ by
        have hj := j.isLt
        rw [mem_nbrs_path]
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.eq_mk_iff_val_eq]
        omega
    rw [h, Finset.card_pair (Fin.ne_of_val_ne (show i.1 - 1 ≠ i.1 + 1 by omega))]
    simp [hn, h0]
  · have h : (path n).nbrs i = ({⟨i.1 + 1, hn⟩} : Finset (Fin n)) :=
      @Finset.ext (Fin n) _ _ fun j ↦ by
        have hj := j.isLt
        rw [mem_nbrs_path]
        simp only [Finset.mem_singleton, Fin.eq_mk_iff_val_eq]
        omega
    rw [h, Finset.card_singleton]
    simp [hn, h0]
  · have h : (path n).nbrs i = ({⟨i.1 - 1, by omega⟩} : Finset (Fin n)) :=
      @Finset.ext (Fin n) _ _ fun j ↦ by
        have hj := j.isLt
        rw [mem_nbrs_path]
        simp only [Finset.mem_singleton, Fin.eq_mk_iff_val_eq]
        omega
    rw [h, Finset.card_singleton]
    simp [hn, h0]
  · have h : (path n).nbrs i = (∅ : Finset (Fin n)) :=
      @Finset.ext (Fin n) _ _ fun j ↦ by
        have hj := j.isLt
        rw [mem_nbrs_path]
        simp only [Finset.notMem_empty, iff_false]
        omega
    rw [h]
    simp [hn, h0]

theorem degree_path {n : ℕ} (i : Fin n) :
    (path n).toSimple.degree i = (if i.1 + 1 < n then 1 else 0) + (if 0 < i.1 then 1 else 0) := by
  rw [← card_nbrs_eq_degree]
  exact card_nbrs_path i

private theorem univ_val_map_val (n : ℕ) :
    (Finset.univ : Finset (Fin n)).val.map Fin.val = Multiset.range n := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, List.map_coe_finRange_eq_range]
  rfl

/-- The degrees of the path, listed vertex by vertex: the two ends have degree one and everything
in between has degree two. -/
@[toIsoGraph degMultiset_path_eq]
theorem degMultiset_path (n : ℕ) :
    (path n).degMultiset
      = (Multiset.range n).map fun k ↦ (if k + 1 < n then 1 else 0) + (if 0 < k then 1 else 0) := by
  unfold degMultiset
  rw [show (fun i : (path n).V ↦ (path n).toSimple.degree i)
      = (fun k ↦ (if k + 1 < n then 1 else 0) + (if 0 < k then 1 else 0)) ∘ Fin.val from
    funext degree_path, ← Multiset.map_map, univ_val_map_val]

/-! ### Degree multisets of the four products -/

private theorem univ_val_map_prod {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℕ) :
    (Finset.univ : Finset (α × β)).val.map (fun p ↦ f p.1 p.2)
      = (Finset.univ : Finset α).val.bind fun a ↦ (Finset.univ : Finset β).val.map (f a) := by
  rw [← Finset.univ_product_univ, Finset.product_val]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind]
  exact Multiset.bind_congr fun a _ ↦ Multiset.map_map _ _ _

theorem degree_cartesianProduct (G H : CGraph)
    (p : (cartesianProduct G H).V) :
    (cartesianProduct G H).toSimple.degree p
      = G.toSimple.degree p.1 + H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_cartesianProduct, Finset.card_union_of_disjoint, Finset.card_product,
    Finset.card_product, Finset.card_singleton, Finset.card_singleton, one_mul, mul_one,
    Nat.add_comm]
  refine Finset.disjoint_product.2 (Or.inr ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem degree_tensorProduct (G H : CGraph)
    (p : (tensorProduct G H).V) :
    (tensorProduct G H).toSimple.degree p = G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_tensorProduct, Finset.card_product]

theorem degree_lexProduct (G H : CGraph)
    (p : (lexProduct G H).V) :
    (lexProduct G H).toSimple.degree p
      = G.toSimple.degree p.1 * Fintype.card H.V + H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_univ, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem degree_strongProduct (G H : CGraph)
    (p : (strongProduct G H).V) :
    (strongProduct G H).toSimple.degree p
      = (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) - 1 := by
  have hdG : ((G.nbrs p.1 ∪ {p.1}) : Finset G.V).card = G.toSimple.degree p.1 + 1 := by
    rw [Finset.card_union_of_disjoint, Finset.card_singleton, card_nbrs_eq_degree]
    rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
    exact Bool.noConfusion
  have hdH : ((H.nbrs p.2 ∪ {p.2}) : Finset H.V).card = H.toSimple.degree p.2 + 1 := by
    rw [Finset.card_union_of_disjoint, Finset.card_singleton, card_nbrs_eq_degree]
    rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
    exact Bool.noConfusion
  have hmem : ({p} : Finset (G.V × H.V)) ⊆ (G.nbrs p.1 ∪ {p.1}) ×ˢ (H.nbrs p.2 ∪ {p.2}) := by
    rw [Finset.singleton_subset_iff, Finset.mem_product]
    exact ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _),
      Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  rw [← card_nbrs_eq_degree, nbrs_strongProduct, Finset.card_sdiff,
    Finset.inter_eq_left.2 hmem, Finset.card_product, hdG, hdH, Finset.card_singleton]

theorem degMultiset_cartesianProduct (G H : CGraph) :
    (cartesianProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_cartesianProduct G H p]
  refine Eq.trans (univ_val_map_prod fun a b ↦ G.toSimple.degree a + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_tensorProduct (G H : CGraph) :
    (tensorProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_tensorProduct G H p]
  refine Eq.trans (univ_val_map_prod fun a b ↦ G.toSimple.degree a * H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_lexProduct (G H : CGraph) :
    (lexProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * Fintype.card H.V + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_lexProduct G H p]
  refine Eq.trans (univ_val_map_prod
    fun a b ↦ G.toSimple.degree a * Fintype.card H.V + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_strongProduct (G H : CGraph) :
    (strongProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ (d + 1) * (e + 1) - 1 := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_strongProduct G H p]
  refine Eq.trans (univ_val_map_prod
    fun a b ↦ (G.toSimple.degree a + 1) * (H.toSimple.degree b + 1) - 1) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦
    (Multiset.map_map (fun e ↦ (G.toSimple.degree a + 1) * (e + 1) - 1)
      (fun v ↦ H.toSimple.degree v) _).symm

/-! ### Clique numbers of the cartesian, tensor and lexicographic products -/

section CliqueProducts

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
private theorem clique_card_le {S : SimpleGraph X} {t : Finset X} (h : S.IsClique (t : Set X)) :
    t.card ≤ S.cliqueNum :=
  h.card_le_cliqueNum

omit [Fintype X] [DecidableEq X] in
private theorem cliqueNum_le_of_forall {S : SimpleGraph X} {n : ℕ}
    (h : ∀ t : Finset X, S.IsClique (t : Set X) → t.card ≤ n) : S.cliqueNum ≤ n := by
  obtain ⟨t, ht, hcard⟩ := S.exists_isNClique_cliqueNum
  exact hcard ▸ h t ht

omit [Fintype X] [DecidableEq X] in
private theorem exists_isClique_card {S : SimpleGraph X} {n : ℕ} (h : n ≤ S.cliqueNum) :
    ∃ t : Finset X, S.IsClique (t : Set X) ∧ t.card = n := by
  obtain ⟨t, ht, hcard⟩ := S.exists_isNClique_cliqueNum
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq (s := t) (n := n) (by omega)
  exact ⟨u, ht.subset (by exact_mod_cast hu), hucard⟩

omit [DecidableEq X] in
private theorem one_le_cliqueNum {S : SimpleGraph X} (a : X) : 1 ≤ S.cliqueNum := by
  have h : S.IsClique (({a} : Finset X) : Set X) := by simp
  simpa using clique_card_le h

/-- The fibre bound: a finset whose first-coordinate projection is a clique and whose fibres
project to cliques has at most `ω(S) * ω(T)` elements. -/
private theorem card_le_mul_of_fibers {S : SimpleGraph X} {T : SimpleGraph Y}
    (s : Finset (X × Y)) (h1 : S.IsClique ((s.image Prod.fst : Finset X) : Set X))
    (h2 : ∀ a : X, T.IsClique (((s.filter fun p ↦ p.1 = a).image Prod.snd : Finset Y) : Set Y)) :
    s.card ≤ S.cliqueNum * T.cliqueNum := by
  have hfib : ∀ a : X, (s.filter fun p ↦ p.1 = a).card ≤ T.cliqueNum := by
    intro a
    have hinj : Set.InjOn Prod.snd
        (((s.filter fun p ↦ p.1 = a) : Finset (X × Y)) : Set (X × Y)) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) hxy
    rw [← Finset.card_image_of_injOn hinj]
    exact clique_card_le (h2 a)
  calc s.card = ∑ a ∈ s.image Prod.fst, (s.filter fun p ↦ p.1 = a).card :=
        Finset.card_eq_sum_card_fiberwise fun x hx ↦ Finset.mem_image_of_mem _ hx
    _ ≤ ∑ _a ∈ s.image Prod.fst, T.cliqueNum := Finset.sum_le_sum fun a _ ↦ hfib a
    _ = (s.image Prod.fst).card * T.cliqueNum := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ S.cliqueNum * T.cliqueNum := Nat.mul_le_mul_right _ (clique_card_le h1)

/-- A clique of a graph with cartesian-product adjacency lies in a single row or a single column,
so its clique number is the larger of the two.  The two vertices `a₀` and `b₀` are what rules out
the empty product, whose clique number is `0`. -/
private theorem cliqueNum_of_cartesian_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} (a₀ : X) (b₀ : Y)
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ (p.1 = q.1 ∧ T.Adj p.2 q.2) ∨ (S.Adj p.1 q.1 ∧ p.2 = q.2)) :
    P.cliqueNum = max S.cliqueNum T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ ?_) (max_le ?_ ?_)
  · by_cases hcard : s.card ≤ 1
    · exact hcard.trans (le_max_of_le_left (one_le_cliqueNum a₀))
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
      rcases (hadj p q).1 (hs (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq) hpq) with
        ⟨h1, -⟩ | ⟨-, h1⟩
      · -- every vertex of `s` lies in the row `p.1`
        have hall : ∀ r ∈ s, r.1 = p.1 := by
          intro r hr
          by_contra hne
          have hrp : r.2 = p.2 := by
            rcases (hadj r p).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hp)
              fun h ↦ hne (congrArg Prod.fst h)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd h hne
            · exact h
          have hrq : r.2 = q.2 := by
            rcases (hadj r q).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hq)
              fun h ↦ hne ((congrArg Prod.fst h).trans h1.symm)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd (h.trans h1.symm) hne
            · exact h
          exact hpq (Prod.ext h1 (hrp.symm.trans hrq))
        have hinj : Set.InjOn Prod.snd (s : Set (X × Y)) := fun x hx y hy hxy ↦
          Prod.ext ((hall x (Finset.mem_coe.1 hx)).trans (hall y (Finset.mem_coe.1 hy)).symm) hxy
        have hclique : T.IsClique ((s.image Prod.snd : Finset Y) : Set Y) := by
          intro b hb b' hb' hne
          rw [Finset.coe_image, Set.mem_image] at hb hb'
          obtain ⟨x, hx, rfl⟩ := hb
          obtain ⟨y, hy, rfl⟩ := hb'
          have hxy : x ≠ y := fun h ↦ hne (congrArg Prod.snd h)
          rcases (hadj x y).1 (hs hx hy hxy) with ⟨-, h⟩ | ⟨-, h⟩
          · exact h
          · exact absurd (Prod.ext ((hall x (Finset.mem_coe.1 hx)).trans
              (hall y (Finset.mem_coe.1 hy)).symm) h) hxy
        exact le_max_of_le_right (Finset.card_image_of_injOn hinj ▸ clique_card_le hclique)
      · -- every vertex of `s` lies in the column `p.2`
        have hall : ∀ r ∈ s, r.2 = p.2 := by
          intro r hr
          by_contra hne
          have hrp : r.1 = p.1 := by
            rcases (hadj r p).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hp)
              fun h ↦ hne (congrArg Prod.snd h)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hne
          have hrq : r.1 = q.1 := by
            rcases (hadj r q).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hq)
              fun h ↦ hne ((congrArg Prod.snd h).trans h1.symm)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd (h.trans h1.symm) hne
          exact hpq (Prod.ext (hrp.symm.trans hrq) h1)
        have hinj : Set.InjOn Prod.fst (s : Set (X × Y)) := fun x hx y hy hxy ↦
          Prod.ext hxy ((hall x (Finset.mem_coe.1 hx)).trans (hall y (Finset.mem_coe.1 hy)).symm)
        have hclique : S.IsClique ((s.image Prod.fst : Finset X) : Set X) := by
          intro a ha a' ha' hne
          rw [Finset.coe_image, Set.mem_image] at ha ha'
          obtain ⟨x, hx, rfl⟩ := ha
          obtain ⟨y, hy, rfl⟩ := ha'
          have hxy : x ≠ y := fun h ↦ hne (congrArg Prod.fst h)
          rcases (hadj x y).1 (hs hx hy hxy) with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd (Prod.ext h ((hall x (Finset.mem_coe.1 hx)).trans
              (hall y (Finset.mem_coe.1 hy)).symm)) hxy
          · exact h
        exact le_max_of_le_left (Finset.card_image_of_injOn hinj ▸ clique_card_le hclique)
  · -- a maximum clique of `S`, times the single vertex `b₀`
    obtain ⟨t, ht, htcard⟩ := exists_isClique_card (le_refl S.cliqueNum)
    have hcard : (t ×ˢ ({b₀} : Finset Y)).card = S.cliqueNum := by
      rw [Finset.card_product, Finset.card_singleton, mul_one, htcard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hx hy
    have hne : x.1 ≠ y.1 := fun h ↦ hxy (Prod.ext h (hx.2.trans hy.2.symm))
    exact (hadj x y).2 (Or.inr ⟨ht (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) hne,
      hx.2.trans hy.2.symm⟩)
  · -- the single vertex `a₀`, times a maximum clique of `T`
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (le_refl T.cliqueNum)
    have hcard : (({a₀} : Finset X) ×ˢ u).card = T.cliqueNum := by
      rw [Finset.card_product, Finset.card_singleton, one_mul, hucard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hx hy
    have hne : x.2 ≠ y.2 := fun h ↦ hxy (Prod.ext (hx.1.trans hy.1.symm) h)
    exact (hadj x y).2 (Or.inl ⟨hx.1.trans hy.1.symm,
      hu (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2) hne⟩)

/-- Both projections of a clique of a graph with tensor-product adjacency are injective cliques,
and conversely any pairing of two cliques of the same size is one, so its clique number is the
smaller of the two. -/
private theorem cliqueNum_of_tensor_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ S.Adj p.1 q.1 ∧ T.Adj p.2 q.2) :
    P.cliqueNum = min S.cliqueNum T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ le_min ?_ ?_) ?_
  · have hinj : Set.InjOn Prod.fst (s : Set (X × Y)) := by
      intro x hx y hy hxy
      by_contra hne
      exact ((hadj x y).1 (hs hx hy hne)).1.ne hxy
    have hclique : S.IsClique ((s.image Prod.fst : Finset X) : Set X) := by
      intro a ha a' ha' hne
      rw [Finset.coe_image, Set.mem_image] at ha ha'
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := ha'
      exact ((hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.fst h))).1
    exact Finset.card_image_of_injOn hinj ▸ clique_card_le hclique
  · have hinj : Set.InjOn Prod.snd (s : Set (X × Y)) := by
      intro x hx y hy hxy
      by_contra hne
      exact ((hadj x y).1 (hs hx hy hne)).2.ne hxy
    have hclique : T.IsClique ((s.image Prod.snd : Finset Y) : Set Y) := by
      intro b hb b' hb' hne
      rw [Finset.coe_image, Set.mem_image] at hb hb'
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨y, hy, rfl⟩ := hb'
      exact ((hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.snd h))).2
    exact Finset.card_image_of_injOn hinj ▸ clique_card_le hclique
  · obtain ⟨t, ht, htcard⟩ := exists_isClique_card (min_le_left S.cliqueNum T.cliqueNum)
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (min_le_right S.cliqueNum T.cliqueNum)
    have hcards : Fintype.card {a // a ∈ t} = Fintype.card {b // b ∈ u} := by
      rw [Fintype.card_coe, Fintype.card_coe, htcard, hucard]
    obtain ⟨e⟩ : Nonempty ({a // a ∈ t} ≃ {b // b ∈ u}) := ⟨Fintype.equivOfCardEq hcards⟩
    have hfinj : Function.Injective fun z : {a // a ∈ t} ↦ (z.1, (e z).1) :=
      fun z z' hzz' ↦ Subtype.ext (congrArg Prod.fst hzz')
    have hcard : (t.attach.image fun z ↦ (z.1, (e z).1)).card = min S.cliqueNum T.cliqueNum := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_attach, htcard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro p hp q hq hpq
    rw [Finset.coe_image, Set.mem_image] at hp hq
    obtain ⟨z, -, rfl⟩ := hp
    obtain ⟨z', -, rfl⟩ := hq
    have hzz' : z ≠ z' := fun h ↦ hpq (by rw [h])
    exact (hadj _ _).2
      ⟨ht (Finset.mem_coe.2 z.2) (Finset.mem_coe.2 z'.2) fun h ↦ hzz' (Subtype.ext h),
        hu (Finset.mem_coe.2 (e z).2) (Finset.mem_coe.2 (e z').2)
          fun h ↦ hzz' (e.injective (Subtype.ext h))⟩

/-- A graph with lexicographic-product adjacency multiplies the two clique numbers. -/
private theorem cliqueNum_of_lex_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ S.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ T.Adj p.2 q.2)) :
    P.cliqueNum = S.cliqueNum * T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ card_le_mul_of_fibers s ?_ ?_) ?_
  · intro a ha a' ha' hne
    rw [Finset.coe_image, Set.mem_image] at ha ha'
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    rcases (hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.fst h)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  · intro a b hb b' hb' hne
    rw [Finset.coe_image, Set.mem_image] at hb hb'
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨y, hy, rfl⟩ := hb'
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    rcases (hadj x y).1 (hs (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1)
      fun h ↦ hne (congrArg Prod.snd h)) with h | ⟨-, h⟩
    · exact absurd (hx.2.trans hy.2.symm) h.ne
    · exact h
  · obtain ⟨t, ht, htcard⟩ := exists_isClique_card (le_refl S.cliqueNum)
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (le_refl T.cliqueNum)
    have hcard : (t ×ˢ u).card = S.cliqueNum * T.cliqueNum := by
      rw [Finset.card_product, htcard, hucard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    by_cases h : x.1 = y.1
    · exact (hadj x y).2 (Or.inr ⟨h, hu (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2)
        fun h2 ↦ hxy (Prod.ext h h2)⟩)
    · exact (hadj x y).2 (Or.inl (ht (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) h))

end CliqueProducts

/-- A clique of `G □ H` lives in a single row or a single column, so the cartesian product has the
larger of the two clique numbers.  Both factors have to be nonempty: otherwise the product is the
empty graph, whose clique number is `0`. -/
theorem cliqueNum_cartesianProduct (G H : CGraph)
    (a : G.V) (b : H.V) :
    (cartesianProduct G H).cliqueNum = max G.cliqueNum H.cliqueNum :=
  cliqueNum_of_cartesian_adj (S := G.toSimple) (T := H.toSimple)
    (P := (cartesianProduct G H).toSimple) a b fun p q ↦ by
      simp only [CGraph.toSimple_adj, cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

/-- The tensor product has the smaller of the two clique numbers. -/
theorem cliqueNum_tensorProduct (G H : CGraph) :
    (tensorProduct G H).cliqueNum = min G.cliqueNum H.cliqueNum :=
  cliqueNum_of_tensor_adj (S := G.toSimple) (T := H.toSimple)
    (P := (tensorProduct G H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true]

/-- The lexicographic product multiplies clique numbers, just like the strong product. -/
theorem cliqueNum_lexProduct (G H : CGraph) :
    (lexProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum :=
  cliqueNum_of_lex_adj (S := G.toSimple) (T := H.toSimple)
    (P := (lexProduct G H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, lexProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

/-! ### The diameter of a Cartesian product -/

/-- **The diameter of a Cartesian product is the sum of the diameters.**  Both factors have to be
connected: the diameter of a disconnected graph is the junk value `0`. -/
@[toIsoGraph]
theorem diameter_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (cartesianProduct G H).diameter = G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hGtop : G.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hG
  have hHtop : H.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hH
  have h : (cartesianProduct G H).toSimple.ediam = G.toSimple.ediam + H.toSimple.ediam := by
    rw [toSimple_cartesianProduct]
    exact ediam_boxProd _ _
  show (cartesianProduct G H).toSimple.diam = G.toSimple.diam + H.toSimple.diam
  unfold SimpleGraph.diam
  rw [h, ENat.toNat_add hGtop hHtop]

@[simp, toIsoGraph] theorem diameter_empty (n : ℕ) : (empty n).diameter = 0 := by
  show (empty n).toSimple.diam = 0
  rw [empty_toSimple]
  exact SimpleGraph.diam_bot

theorem diameter_disjUnion (G H : CGraph) (hG : 0 < Fintype.card G.V)
    (hH : 0 < Fintype.card H.V) : (disjUnion G H).diameter = 0 :=
  SimpleGraph.diam_eq_zero_of_not_connected (not_isConnected_disjUnion G H hG hH)

theorem chromNum_le_iff_colorable {G : CGraph} {n : ℕ} : G.chromNum ≤ n ↔ G.toSimple.Colorable n := by
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable, ← coe_chromNum, Nat.cast_le]

theorem colorable_chromNum {G : CGraph} : G.toSimple.Colorable G.chromNum := chromNum_le_iff_colorable.1 le_rfl

theorem le_chromNum_iff {G : CGraph} {n : ℕ} : n ≤ G.chromNum ↔ ∀ m, G.toSimple.Colorable m → n ≤ m := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, SimpleGraph.le_chromaticNumber_iff_colorable]

theorem chromNum_eq_iff {G : CGraph} {n : ℕ} :
    G.chromNum = n ↔ G.toSimple.Colorable n ∧ ∀ m, G.toSimple.Colorable m → n ≤ m := by
  rw [le_antisymm_iff, chromNum_le_iff_colorable, le_chromNum_iff]

/-! ### The cycle is Mathlib's `cycleGraph` -/

/-- One step around `cycle n`, in Mathlib's `Fin`-subtraction phrasing. -/
private theorem cycle_step_iff {n : ℕ} {u v : Fin n} (h : u.1 ≠ v.1) :
    (u.1 + 1) % n = v.1 ↔ (v - u).val = 1 := by
  have hu := u.isLt
  have hv := v.isLt
  rcases lt_or_ge u.1 v.1 with hlt | hle
  · rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 hlt.le), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 (by omega))]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hu) with he | hlt2
    · rw [show u.1 + 1 = n from he, Nat.mod_self]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `CGraph.cycle n` is Mathlib's `SimpleGraph.cycleGraph n`. -/
@[simp] theorem cycle_toSimple (n : ℕ) : (cycle n).toSimple = SimpleGraph.cycleGraph n := by
  ext u v
  rw [CGraph.toSimple_adj, cycle_adj_val]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact SimpleGraph.cycleGraph_adj'.2 (Or.inr ((cycle_step_iff hne).1 h))
    · exact SimpleGraph.cycleGraph_adj'.2 (Or.inl ((cycle_step_iff (Ne.symm hne)).1 h))
  · intro hadj
    have hne : u.1 ≠ v.1 := fun he ↦ hadj.ne (Fin.ext he)
    rcases SimpleGraph.cycleGraph_adj'.1 hadj with h | h
    · exact ⟨hne, Or.inr ((cycle_step_iff (Ne.symm hne)).2 h)⟩
    · exact ⟨hne, Or.inl ((cycle_step_iff hne).2 h)⟩

/-! ### Values of the chromatic number -/

theorem chromNum_eq_of_chromaticNumber {G : CGraph} {n : ℕ}
    (h : G.toSimple.chromaticNumber = n) : G.chromNum = n := by
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum, h]

@[toIsoGraph chromNum_le_V]
theorem chromNum_le_card (G : CGraph) : G.chromNum ≤ Fintype.card G.V := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.chromaticNumber_le_card

/-- A clique needs one colour per vertex, so `ω(G) ≤ χ(G)`. -/
@[toIsoGraph]
theorem cliqueNum_le_chromNum (G : CGraph) : G.cliqueNum ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.cliqueNum_le_chromaticNumber

theorem two_le_chromNum_of_adj {G : CGraph} {a b : G.V} (h : G.Adj a b) : 2 ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.two_le_chromaticNumber_of_adj h

/-- Two colours suffice exactly when the graph is bipartite. -/
@[toIsoGraph]
theorem isBipartite_iff_chromNum_le_two {G : CGraph} : G.IsBipartite ↔ G.chromNum ≤ 2 :=
  G.isBipartite_iff_colorable.trans chromNum_le_iff_colorable.symm

@[simp, toIsoGraph] theorem chromNum_empty_zero : (empty 0).chromNum = 0 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : IsEmpty (empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_eq_zero_of_isEmpty)

@[simp, toIsoGraph] theorem chromNum_empty (n : ℕ) : (empty (n + 1)).chromNum = 1 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : Nonempty (empty (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_bot (V := (empty (n + 1)).V))

/-- **`K_n` needs `n` colours.** -/
@[simp, toIsoGraph] theorem chromNum_complete (n : ℕ) : (complete n).chromNum = n :=
  chromNum_eq_of_chromaticNumber (by rw [complete_toSimple, SimpleGraph.chromaticNumber_top,
    card_complete])

@[simp, toIsoGraph] theorem chromNum_path (n : ℕ) : (path (n + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [path_toSimple]; exact SimpleGraph.chromaticNumber_pathGraph _ (by omega))

/-- **An even cycle is bipartite.** -/
@[toIsoGraph]
theorem chromNum_cycle_even (m : ℕ) : (cycle (2 * m + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [cycle_toSimple]
    exact SimpleGraph.chromaticNumber_cycleGraph_of_even _ (by omega) ⟨m + 1, by omega⟩)

/-- **An odd cycle needs three colours.** -/
@[toIsoGraph]
theorem chromNum_cycle_odd (m : ℕ) : (cycle (2 * m + 3)).chromNum = 3 :=
  chromNum_eq_of_chromaticNumber (by
    rw [cycle_toSimple]
    exact SimpleGraph.chromaticNumber_cycleGraph_of_odd _ (by omega) ⟨m + 1, by omega⟩)

/-- The underlying simple graph of a disjoint union is Mathlib's `SimpleGraph.sum`. -/
theorem toSimple_disjUnion (G H : CGraph) :
    (disjUnion G H).toSimple = G.toSimple.sum H.toSimple := by
  ext x y
  cases x <;> cases y <;> simp [SimpleGraph.sum_adj, CGraph.toSimple_adj]

/-- **Colouring the two halves of a disjoint union is independent.** -/
@[simp, toIsoGraph] theorem chromNum_disjUnion (G H : CGraph) :
    (disjUnion G H).chromNum = max G.chromNum H.chromNum := by
  have hmax : ((max G.chromNum H.chromNum : ℕ) : ℕ∞)
      = max (G.chromNum : ℕ∞) (H.chromNum : ℕ∞) := by
    rcases le_total G.chromNum H.chromNum with h | h
    · rw [max_eq_right h, max_eq_right (Nat.cast_le.2 h)]
    · rw [max_eq_left h, max_eq_left (Nat.cast_le.2 h)]
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum, toSimple_disjUnion,
    SimpleGraph.chromaticNumber_sum, hmax, coe_chromNum, coe_chromNum]

theorem toSimple_ne_bot_iff {G : CGraph} : G.toSimple ≠ ⊥ ↔ 0 < G.E := by
  show _ ↔ 0 < G.toSimple.edgeFinset.card
  rw [Finset.card_pos, SimpleGraph.edgeFinset_nonempty]

theorem chromNum_eq_iff_chromaticNumber {G : CGraph} {n : ℕ} :
    G.chromNum = n ↔ G.toSimple.chromaticNumber = n := by
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum]

/-- **A graph is 2-chromatic exactly when it is bipartite and has an edge.** -/
@[toIsoGraph]
theorem chromNum_eq_two_iff {G : CGraph} : G.chromNum = 2 ↔ G.IsBipartite ∧ 0 < G.E := by
  rw [chromNum_eq_iff_chromaticNumber, ← toSimple_ne_bot_iff, isBipartite_iff_colorable]
  exact_mod_cast SimpleGraph.chromaticNumber_eq_two_iff

@[toIsoGraph]
theorem chromNum_eq_zero_iff {G : CGraph} : G.chromNum = 0 ↔ Fintype.card G.V = 0 := by
  rw [chromNum_eq_iff_chromaticNumber, Fintype.card_eq_zero_iff]
  exact ⟨fun h ↦ SimpleGraph.isEmpty_of_chromaticNumber_eq_zero (by exact_mod_cast h),
    fun h ↦ by exact_mod_cast SimpleGraph.chromaticNumber_eq_zero_of_isEmpty⟩

/-- Anything that is not bipartite needs at least three colours. -/
@[toIsoGraph]
theorem three_le_chromNum {G : CGraph} (h : ¬ G.IsBipartite) : 3 ≤ G.chromNum := by
  rw [isBipartite_iff_chromNum_le_two] at h; omega

/-- Projecting a tensor product onto a factor is a graph homomorphism, so it cannot need more
colours than either factor. -/
private theorem chromaticNumber_le_of_hom_fst {X Y : Type} {S : SimpleGraph X}
    {P : SimpleGraph (X × Y)} (hadj : ∀ p q : X × Y, P.Adj p q → S.Adj p.1 q.1) :
    P.chromaticNumber ≤ S.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom ⟨Prod.fst, fun {a b} h ↦ hadj a b h⟩

private theorem chromaticNumber_le_of_hom_snd {X Y : Type} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} (hadj : ∀ p q : X × Y, P.Adj p q → T.Adj p.2 q.2) :
    P.chromaticNumber ≤ T.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom ⟨Prod.snd, fun {a b} h ↦ hadj a b h⟩

/-- **A tensor product is no harder to colour than either factor.** -/
@[toIsoGraph]
theorem chromNum_tensorProduct_le (G H : CGraph) :
    (tensorProduct G H).chromNum ≤ min G.chromNum H.chromNum := by
  rw [le_min_iff, ← Nat.cast_le (α := ℕ∞), ← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum,
    coe_chromNum]
  refine ⟨chromaticNumber_le_of_hom_fst (S := G.toSimple) (P := (tensorProduct G H).toSimple)
      fun p q h ↦ ?_,
    chromaticNumber_le_of_hom_snd (T := H.toSimple) (P := (tensorProduct G H).toSimple)
      fun p q h ↦ ?_⟩
  · have h' : G.Adj p.1 q.1 = true ∧ H.Adj p.2 q.2 = true := by simpa using h
    exact h'.1
  · have h' : G.Adj p.1 q.1 = true ∧ H.Adj p.2 q.2 = true := by simpa using h
    exact h'.2

section ChromProducts

variable {X Y : Type} [Fintype X] [Fintype Y]

/-! ### The join -/

omit [Fintype X] [Fintype Y] in
/-- Two colourings with disjoint palettes colour a join. -/
private theorem colorable_of_join_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {J : SimpleGraph (X ⊕ Y)} {a b : ℕ}
    (hll : ∀ x y, J.Adj (.inl x) (.inl y) → S.Adj x y)
    (hrr : ∀ x y, J.Adj (.inr x) (.inr y) → T.Adj x y)
    (hS : S.Colorable a) (hT : T.Colorable b) : J.Colorable (a + b) := by
  obtain ⟨cS⟩ := hS
  obtain ⟨cT⟩ := hT
  refine ⟨SimpleGraph.Coloring.mk
    (Sum.elim (fun x ↦ (cS x).castAdd b) (fun y ↦ (cT y).natAdd a)) ?_⟩
  intro v w hadj
  cases v with
  | inl x =>
    cases w with
    | inl y =>
      refine fun h ↦ cS.valid (hll x y hadj) (Fin.ext ?_)
      simpa using congrArg Fin.val h
    | inr y =>
      refine Fin.ne_of_val_ne ?_
      have := (cS x).isLt
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd]
      omega
  | inr x =>
    cases w with
    | inl y =>
      refine Fin.ne_of_val_ne ?_
      have := (cS y).isLt
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd]
      omega
    | inr y =>
      refine fun h ↦ cT.valid (hrr x y hadj) (Fin.ext ?_)
      simpa using congrArg Fin.val h

/-- In a join every colour is used on one side only, so the two palettes are disjoint and the
chromatic numbers add. -/
private theorem chromaticNumber_add_le_of_join_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {J : SimpleGraph (X ⊕ Y)} {n : ℕ}
    (hll : ∀ x y, S.Adj x y → J.Adj (.inl x) (.inl y))
    (hrr : ∀ x y, T.Adj x y → J.Adj (.inr x) (.inr y))
    (hlr : ∀ x y, J.Adj (.inl x) (.inr y))
    (hc : J.Colorable n) : S.chromaticNumber + T.chromaticNumber ≤ n := by
  classical
  obtain ⟨c⟩ := hc
  set A : Finset (Fin n) := Finset.univ.image fun x : X ↦ c (.inl x) with hA
  set B : Finset (Fin n) := Finset.univ.image fun y : Y ↦ c (.inr y) with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hA, Finset.mem_image] at hz
    rw [hB, Finset.mem_image] at hz'
    obtain ⟨x, -, hx⟩ := hz
    obtain ⟨y, -, hy⟩ := hz'
    exact c.valid (hlr x y) (hx.trans hy.symm)
  have hcard : A.card + B.card ≤ n := by
    have h := Finset.card_le_univ (A ∪ B)
    rwa [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at h
  have hSA : S.Colorable A.card := by
    have C : S.Coloring {z // z ∈ A} :=
      SimpleGraph.Coloring.mk (fun x ↦ ⟨c (.inl x), by rw [hA, Finset.mem_image]; exact ⟨x, by simp⟩⟩)
        fun {v w} h he ↦ c.valid (hll v w h) (congrArg Subtype.val he)
    simpa using C.colorable
  have hTB : T.Colorable B.card := by
    have C : T.Coloring {z // z ∈ B} :=
      SimpleGraph.Coloring.mk (fun y ↦ ⟨c (.inr y), by rw [hB, Finset.mem_image]; exact ⟨y, by simp⟩⟩)
        fun {v w} h he ↦ c.valid (hrr v w h) (congrArg Subtype.val he)
    simpa using C.colorable
  calc S.chromaticNumber + T.chromaticNumber
      ≤ (A.card : ℕ∞) + (B.card : ℕ∞) :=
        add_le_add hSA.chromaticNumber_le hTB.chromaticNumber_le
    _ = ((A.card + B.card : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ (n : ℕ∞) := Nat.cast_le.2 hcard

/-! ### The cartesian product -/

omit [Fintype X] [Fintype Y] in
/-- Colouring `G □ H` by the *sum* of the two coordinate colours, in `ZMod n`: an edge changes
exactly one coordinate, so the sums differ by cancellation. -/
private theorem colorable_of_cartesian_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} {n : ℕ}
    (hadj : ∀ p q : X × Y, P.Adj p q → (p.1 = q.1 ∧ T.Adj p.2 q.2) ∨ (S.Adj p.1 q.1 ∧ p.2 = q.2))
    (hS : S.Colorable n) (hT : T.Colorable n) : P.Colorable n := by
  cases n with
  | zero =>
    haveI : IsEmpty X := SimpleGraph.isEmpty_of_colorable_zero hS
    haveI : IsEmpty (X × Y) := inferInstance
    exact SimpleGraph.Colorable.of_isEmpty 0
  | succ m =>
    obtain ⟨cS⟩ := hS
    obtain ⟨cT⟩ := hT
    refine ⟨SimpleGraph.Coloring.mk (fun p ↦ cS p.1 + cT p.2) ?_⟩
    intro v w hvw
    show cS v.1 + cT v.2 ≠ cS w.1 + cT w.2
    rcases hadj v w hvw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      exact fun h ↦ cT.valid h2 (add_left_cancel h)
    · rw [h2]
      exact fun h ↦ cS.valid h1 (add_right_cancel h)

omit [Fintype X] [Fintype Y] in
/-- A copy of `G` sits inside `G □ H` as a row. -/
private theorem chromaticNumber_le_of_cartesian_left {S : SimpleGraph X}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, (S.Adj p.1 q.1 ∧ p.2 = q.2) → P.Adj p q) (y : Y) :
    S.chromaticNumber ≤ P.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom
    ⟨fun x ↦ (x, y), fun {a b} h ↦ hadj (a, y) (b, y) ⟨h, rfl⟩⟩

omit [Fintype X] [Fintype Y] in
/-- A copy of `H` sits inside `G □ H` as a column. -/
private theorem chromaticNumber_le_of_cartesian_right {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, (p.1 = q.1 ∧ T.Adj p.2 q.2) → P.Adj p q) (x : X) :
    T.chromaticNumber ≤ P.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom
    ⟨fun y ↦ (x, y), fun {a b} h ↦ hadj (x, a) (x, b) ⟨rfl, h⟩⟩

/-! ### The lexicographic product -/

omit [Fintype X] [Fintype Y] in
/-- Colouring `G[H]` by the pair of coordinate colours. -/
private theorem colorable_of_lex_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} {a b : ℕ}
    (hadj : ∀ p q : X × Y, P.Adj p q → S.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ T.Adj p.2 q.2))
    (hS : S.Colorable a) (hT : T.Colorable b) : P.Colorable (a * b) := by
  obtain ⟨cS⟩ := hS
  obtain ⟨cT⟩ := hT
  have C : P.Coloring (Fin a × Fin b) :=
    SimpleGraph.Coloring.mk (fun p ↦ (cS p.1, cT p.2)) fun {v w} h he ↦ by
      rcases hadj v w h with h' | ⟨h1, h2⟩
      · exact cS.valid h' (congrArg Prod.fst he)
      · exact cT.valid h2 (congrArg Prod.snd he)
  simpa using C.colorable

end ChromProducts

/-- **The chromatic numbers of a join add.** -/
theorem chromNum_join (G H : CGraph) :
    (join G H).chromNum = G.chromNum + H.chromNum := by
  have hll : ∀ x y : G.V, (join G H).toSimple.Adj (.inl x) (.inl y) ↔ G.toSimple.Adj x y := by
    intro x y
    rw [CGraph.toSimple_adj, CGraph.toSimple_adj, join_adj_inl_inl]
  have hrr : ∀ x y : H.V, (join G H).toSimple.Adj (.inr x) (.inr y) ↔ H.toSimple.Adj x y := by
    intro x y
    rw [CGraph.toSimple_adj, CGraph.toSimple_adj, join_adj_inr_inr]
  have hlr : ∀ (x : G.V) (y : H.V), (join G H).toSimple.Adj (.inl x) (.inr y) := by
    intro x y
    rw [CGraph.toSimple_adj, join_adj_inl_inr]
  refine le_antisymm (chromNum_le_iff_colorable.2 ?_) ?_
  · exact colorable_of_join_adj (S := G.toSimple) (T := H.toSimple)
      (J := (join G H).toSimple) (fun x y h ↦ (hll x y).1 h) (fun x y h ↦ (hrr x y).1 h)
      colorable_chromNum colorable_chromNum
  · refine le_chromNum_iff.2 fun m hm ↦ ?_
    have h := chromaticNumber_add_le_of_join_adj (S := G.toSimple) (T := H.toSimple)
      (J := (join G H).toSimple) (fun x y h ↦ (hll x y).2 h) (fun x y h ↦ (hrr x y).2 h) hlr hm
    rw [← coe_chromNum, ← coe_chromNum, ← Nat.cast_add, Nat.cast_le] at h
    exact h

/-- **Sabidussi's theorem**: the chromatic number of a cartesian product is the larger of the two.
Both factors have to be nonempty — the product of anything with the empty graph is empty. -/
theorem chromNum_cartesianProduct (G H : CGraph)
    (a : G.V) (b : H.V) :
    (cartesianProduct G H).chromNum = max G.chromNum H.chromNum := by
  have hle : ∀ p q : G.V × H.V,
      (cartesianProduct G H).toSimple.Adj p q →
        (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2) := by
    intro p q h
    simpa using h
  have hge : ∀ p q : G.V × H.V,
      ((p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2)) →
        (cartesianProduct G H).toSimple.Adj p q := by
    intro p q h
    rw [CGraph.toSimple_adj, cartesianProduct_adj]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [CGraph.toSimple_adj] at h2
      simp [h1, h2]
    · rw [CGraph.toSimple_adj] at h1
      simp [h1, h2]
  refine le_antisymm (chromNum_le_iff_colorable.2 ?_) (max_le ?_ ?_)
  · exact colorable_of_cartesian_adj (S := G.toSimple) (T := H.toSimple)
      (P := (cartesianProduct G H).toSimple) hle
      (colorable_chromNum.mono (le_max_left _ _)) (colorable_chromNum.mono (le_max_right _ _))
  · rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum]
    exact chromaticNumber_le_of_cartesian_left (S := G.toSimple)
      (P := (cartesianProduct G H).toSimple) (fun p q h ↦ hge p q (Or.inr h)) b
  · rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum]
    exact chromaticNumber_le_of_cartesian_right (T := H.toSimple)
      (P := (cartesianProduct G H).toSimple) (fun p q h ↦ hge p q (Or.inl h)) a

/-- **The lexicographic product multiplies chromatic numbers, at worst.** -/
@[toIsoGraph]
theorem chromNum_lexProduct_le (G H : CGraph) :
    (lexProduct G H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2 <|
    colorable_of_lex_adj (S := G.toSimple) (T := H.toSimple) (P := (lexProduct G H).toSimple)
      (fun p q h ↦ by simpa using h) colorable_chromNum colorable_chromNum

/-- One colour is enough exactly when there is a vertex but no edge. -/
@[toIsoGraph]
theorem chromNum_eq_one_iff {G : CGraph} : G.chromNum = 1 ↔ G.E = 0 ∧ 0 < Fintype.card G.V := by
  have hb : G.toSimple = ⊥ ↔ G.E = 0 := by
    rw [← not_iff_not, ← ne_eq, toSimple_ne_bot_iff]
    omega
  rw [chromNum_eq_iff_chromaticNumber, Nat.cast_one, SimpleGraph.chromaticNumber_eq_one_iff, hb,
    Fintype.card_pos_iff]

/-- **Every colour class is an independent set**, so `|V| ≤ χ·α`. -/
@[toIsoGraph V_le_chromNum_mul_indepNum]
theorem card_le_chromNum_mul_indepNum (G : CGraph) :
    Fintype.card G.V ≤ G.chromNum * G.indepNum := by
  classical
  obtain ⟨c⟩ := G.colorable_chromNum
  have hfib : ∀ i : Fin G.chromNum,
      (Finset.univ.filter fun v ↦ c v = i).card ≤ G.indepNum := by
    intro i
    refine SimpleGraph.IsIndepSet.card_le_indepNum ?_
    intro x hx y hy hne hadj
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    exact c.valid hadj (hx.2.trans hy.2.symm)
  have hsum : Fintype.card G.V
      = ∑ i : Fin G.chromNum, (Finset.univ.filter fun v ↦ c v = i).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun v _ ↦ Finset.mem_univ (c v)
  calc Fintype.card G.V = ∑ i : Fin G.chromNum, (Finset.univ.filter fun v ↦ c v = i).card := hsum
    _ ≤ ∑ _i : Fin G.chromNum, G.indepNum := Finset.sum_le_sum fun i _ ↦ hfib i
    _ = G.chromNum * G.indepNum := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]

/-! ### The Mycielskian raises the chromatic number by one -/

/-- A colouring of `G` extends to the Mycielskian with one extra colour: each shadow copies its
original, and the apex takes the new colour. -/
private theorem colorable_mycielskian (G : CGraph) {n : ℕ}
    (h : G.toSimple.Colorable n) : (mycielskian G).toSimple.Colorable (n + 1) := by
  obtain ⟨c⟩ := h
  have hne : ∀ a b : G.V, G.Adj a b = true → (c a).castSucc ≠ (c b).castSucc := fun a b hab hcc ↦
    c.valid ((CGraph.toSimple_adj G a b).2 hab) (Fin.castSucc_injective n hcc)
  refine ⟨SimpleGraph.Coloring.mk
    (fun x : Option (G.V ⊕ G.V) ↦ Option.elim x (Fin.last n)
      (Sum.elim (fun a ↦ (c a).castSucc) fun a ↦ (c a).castSucc)) ?_⟩
  intro v w hvw
  rw [CGraph.toSimple_adj] at hvw
  rcases v with _ | (a | a) <;> rcases w with _ | (b | b) <;>
    simp only [mycielskian_adj_none_none, mycielskian_adj_none_inl, mycielskian_adj_none_inr,
      mycielskian_adj_inl_none, mycielskian_adj_inl_inl, mycielskian_adj_inl_inr,
      mycielskian_adj_inr_none, mycielskian_adj_inr_inl, mycielskian_adj_inr_inr,
      Bool.false_eq_true] at hvw
  · exact (Fin.castSucc_lt_last (c b)).ne'
  · exact hne a b hvw
  · exact hne a b hvw
  · exact (Fin.castSucc_lt_last (c a)).ne
  · exact hne a b hvw

/-- Conversely a colouring of the Mycielskian gives back a colouring of `G` with one colour fewer:
recolour every vertex that got the apex's colour with the colour of its shadow. -/
private theorem colorable_of_colorable_mycielskian (G : CGraph) {n : ℕ}
    (h : (mycielskian G).toSimple.Colorable n) : G.toSimple.Colorable (n - 1) := by
  classical
  obtain ⟨f⟩ := h
  set z : Fin n := f none with hz
  have hshadow : ∀ a : G.V, f (some (.inr a)) ≠ z :=
    fun a ↦ (f.valid (by rw [CGraph.toSimple_adj, mycielskian_adj_none_inr] : _)).symm
  have hll : ∀ a b : G.V, G.Adj a b = true →
      f (some (.inl a)) ≠ f (some (.inl b)) := fun a b hab ↦
    f.valid (by rw [CGraph.toSimple_adj, mycielskian_adj_inl_inl]; exact hab)
  have hrl : ∀ a b : G.V, G.Adj a b = true →
      f (some (.inr a)) ≠ f (some (.inl b)) := fun a b hab ↦
    f.valid (by rw [CGraph.toSimple_adj, mycielskian_adj_inr_inl]; exact hab)
  have hlr : ∀ a b : G.V, G.Adj a b = true →
      f (some (.inl a)) ≠ f (some (.inr b)) := fun a b hab ↦
    f.valid (by rw [CGraph.toSimple_adj, mycielskian_adj_inl_inr]; exact hab)
  have C : G.toSimple.Coloring {x : Fin n // x ≠ z} :=
    SimpleGraph.Coloring.mk
      (fun a ↦ if ha : f (some (.inl a)) = z then ⟨f (some (.inr a)), hshadow a⟩
        else ⟨f (some (.inl a)), ha⟩)
      (by
        intro a b hab hcc
        rw [CGraph.toSimple_adj] at hab
        by_cases ha : f (some (.inl a)) = z <;> by_cases hb : f (some (.inl b)) = z <;>
          simp only [ha, hb, dif_pos, dif_neg, not_false_iff, Subtype.mk.injEq] at hcc
        · exact hll a b hab (ha.trans hb.symm)
        · exact hrl a b hab hcc
        · exact hlr a b hab hcc
        · exact hll a b hab hcc)
  have hcard : Fintype.card {x : Fin n // x ≠ z} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  exact hcard ▸ C.colorable

/-- **Mycielski's construction raises the chromatic number by exactly one.** -/
theorem chromNum_mycielskian (G : CGraph) :
    (mycielskian G).chromNum = G.chromNum + 1 := by
  have hpos : 0 < (mycielskian G).chromNum := by
    rcases Nat.eq_zero_or_pos (mycielskian G).chromNum with h | h
    · rw [chromNum_eq_zero_iff, card_mycielskian] at h
      omega
    · exact h
  have h1 : (mycielskian G).chromNum ≤ G.chromNum + 1 :=
    chromNum_le_iff_colorable.2 (colorable_mycielskian G colorable_chromNum)
  have h2 : G.chromNum ≤ (mycielskian G).chromNum - 1 :=
    chromNum_le_iff_colorable.2 (colorable_of_colorable_mycielskian G colorable_chromNum)
  omega

/-! ### The greedy colouring of a Kneser graph -/

/-- The heart of the Kneser bound: two disjoint `k`-sets cannot have the same capped minimum.
Below the cap they would share their smallest element; at the cap both sets live in the top
`n - (n - 2k + 1)` elements, which is fewer than the `2k` they need between them. -/
private theorem kneser_color_ne {n k : ℕ} (hk : 0 < k) {s t : Finset (Fin n)}
    (hs : s.card = k) (ht : t.card = k) (hinter : s ∩ t = ∅)
    {ms mt : Fin n} (hms : ms ∈ s) (hmsle : ∀ x ∈ s, ms ≤ x)
    (hmt : mt ∈ t) (hmtle : ∀ x ∈ t, mt ≤ x) :
    min (ms : ℕ) (n - 2 * k + 1) ≠ min (mt : ℕ) (n - 2 * k + 1) := by
  classical
  intro heq
  set c := n - 2 * k + 1 with hc
  rcases lt_or_ge (ms : ℕ) c with hlt | hge
  · -- the two smallest elements agree, so the sets meet
    rw [min_eq_left hlt.le] at heq
    have hmt' : (mt : ℕ) = (ms : ℕ) := by
      rcases lt_or_ge (mt : ℕ) c with h | h
      · rw [min_eq_left h.le] at heq; omega
      · rw [min_eq_right h] at heq; omega
    have hmem : ms ∈ s ∩ t := Finset.mem_inter.2 ⟨hms, Fin.ext hmt' ▸ hmt⟩
    rw [hinter] at hmem
    simp at hmem
  · -- both sets live above the cap, and there is no room for `2k` vertices there
    rw [min_eq_right hge] at heq
    have hget : c ≤ (mt : ℕ) := by
      rcases lt_or_ge (mt : ℕ) c with h | h
      · rw [min_eq_left h.le] at heq; omega
      · exact h
    have hsub : s ∪ t ⊆ Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ) := by
      intro x hx
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.1 hx with h | h
      · exact le_trans hge (hmsle x h)
      · exact le_trans hget (hmtle x h)
    have hdisj : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.2 hinter
    have hcard : (s ∪ t).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, hs, ht]; ring
    have hfil : (Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ)).card ≤ n - c := by
      have h := Finset.card_le_card_of_injOn (f := fun x : Fin n ↦ (x : ℕ))
        (s := Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ)) (t := Finset.Ico c n)
        (fun x hx ↦ Finset.mem_Ico.2 ⟨(Finset.mem_filter.1 hx).2, x.isLt⟩)
        (fun x _ y _ h ↦ Fin.ext h)
      rwa [Nat.card_Ico] at h
    have hle := le_trans (Finset.card_le_card hsub) hfil
    omega

/-- **`χ(K(n, k)) ≤ n - 2k + 2`.**  Colour a `k`-set by its smallest element, capped at
`n - 2k + 1`. -/
@[toIsoGraph]
theorem chromNum_kneser_le (n k : ℕ) (hk : 0 < k) :
    (kneser n k).chromNum ≤ n - 2 * k + 2 := by
  classical
  rw [chromNum_le_iff_colorable, SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  have hnonempty : ∀ s : {s : Finset (Fin n) // s.card = k}, (s : Finset (Fin n)).Nonempty := by
    intro s
    rw [← Finset.card_pos, s.2]
    exact hk
  refine ⟨SimpleGraph.Coloring.mk
    (fun s : {s : Finset (Fin n) // s.card = k} ↦
      min ((s : Finset (Fin n)).min' (hnonempty s)) (n - 2 * k + 1)) ?_, fun s ↦ ?_⟩
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hadj
    rw [CGraph.toSimple_adj, kneser_adj] at hadj
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Subtype.mk.injEq] at hadj
    exact kneser_color_ne hk hs ht hadj.2 (s.min'_mem _) (fun x hx ↦ s.min'_le x hx)
      (t.min'_mem _) fun x hx ↦ t.min'_le x hx
  · exact lt_of_le_of_lt (min_le_right _ _) (by omega)

/-! ### Girth -/

/-- A product of two graphs with an edge each contains a square. -/
theorem girth_cartesianProduct_le_four {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) : (cartesianProduct G H).girth ≤ 4 := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  have hbne : b ≠ b' := by rintro rfl; exact absurd hb (by simp [H.loopless])
  refine girth_le_four_of_square (a := ((a, b) : (cartesianProduct G H).V)) (b := (a', b))
    (c := (a', b')) (d := (a, b')) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-! ### Girth three and the clique number -/

/-- **Girth three means a triangle**, and a triangle is a three-clique: so a graph has girth
three exactly when its clique number is at least three.  Every entry of the `cliqueNum` table is
therefore also a girth-three certificate. -/
@[toIsoGraph]
theorem girth_eq_three_iff {G : CGraph} : G.girth = 3 ↔ 3 ≤ G.cliqueNum := by
  classical
  constructor
  · intro h
    have hnac : ¬ G.IsAcyclic := by
      intro hac
      rw [girth_eq_zero_iff.2 hac] at h
      omega
    obtain ⟨a, w, hw, hlen⟩ := SimpleGraph.exists_girth_eq_length.2 hnac
    obtain ⟨x, y, z, h1, h2, h3⟩ := exists_triangle_of_girth_eq_three hw (hlen.symm.trans h)
    have h1' : G.toSimple.Adj x y := (toSimple_adj _ _ _).2 h1
    have h2' : G.toSimple.Adj y z := (toSimple_adj _ _ _).2 h2
    have h3' : G.toSimple.Adj z x := (toSimple_adj _ _ _).2 h3
    have hcl : G.toSimple.IsNClique 3 {x, y, z} :=
      SimpleGraph.is3Clique_triple_iff.2 ⟨h1', h3'.symm, h2'⟩
    have := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl.isClique)
    rwa [hcl.card_eq] at this
  · intro h
    obtain ⟨s, hs⟩ := G.toSimple.exists_isNClique_cliqueNum
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 3) (show 3 ≤ s.card by rw [hs.card_eq]; exact h)
    have hcl : G.toSimple.IsNClique 3 t := ⟨hs.isClique.subset hts, htc⟩
    obtain ⟨x, y, z, -, -, -, rfl⟩ := Finset.card_eq_three.1 htc
    rw [SimpleGraph.is3Clique_triple_iff] at hcl
    exact girth_eq_three_of_triangle ((toSimple_adj _ _ _).1 hcl.1)
      ((toSimple_adj _ _ _).1 hcl.2.2) ((toSimple_adj _ _ _).1 hcl.2.1.symm)

@[toIsoGraph]
theorem girth_eq_three_of_cliqueNum {G : CGraph} (h : 3 ≤ G.cliqueNum) : G.girth = 3 :=
  girth_eq_three_iff.2 h

/-- **A triangle-free graph with a cycle has girth at least four**, stated through the clique
number. -/
@[toIsoGraph]
theorem four_le_girth_of_cliqueNum {G : CGraph} (hcl : G.cliqueNum ≤ 2) (hnac : ¬ G.IsAcyclic) :
    4 ≤ G.girth := by
  have h3 := three_le_girth hnac
  have : G.girth ≠ 3 := fun h ↦ by have := girth_eq_three_iff.1 h; omega
  omega

/-! ### Girth five from strong regularity -/

/-- **A strongly regular graph with `ℓ = 0` and `μ = 1` has girth at least five**: `ℓ = 0` rules
out triangles and `μ = 1` rules out squares, since the two opposite corners of a square would
share two neighbours. -/
theorem IsSRGWith.five_le_girth {G : CGraph} {n k : ℕ} (h : G.IsSRGWith n k 0 1)
    (hnac : ¬ G.IsAcyclic) : 5 ≤ G.girth := by
  have h' : G.toSimple.IsSRGWith n k 0 1 := h
  refine _root_.CGraph.five_le_girth (fun x y z h1 h2 h3 ↦ ?_) (fun x y z t h1 h2 h3 h4 ↦ ?_) hnac
  · have hzx : G.toSimple.Adj z x := (toSimple_adj _ _ _).2 h3
    have hemp := h'.of_adj z x hzx
    rw [Fintype.card_eq_zero_iff] at hemp
    exact hemp.false ⟨y, ((toSimple_adj _ _ _).2 h2).symm, (toSimple_adj _ _ _).2 h1⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hxz, hyt⟩ := hcon
    have hy : y ∈ G.toSimple.commonNeighbors x z :=
      ⟨(toSimple_adj _ _ _).2 h1, ((toSimple_adj _ _ _).2 h2).symm⟩
    have ht : t ∈ G.toSimple.commonNeighbors x z :=
      ⟨((toSimple_adj _ _ _).2 h4).symm, (toSimple_adj _ _ _).2 h3⟩
    by_cases hadj : G.toSimple.Adj x z
    · have hemp := h'.of_adj x z hadj
      rw [Fintype.card_eq_zero_iff] at hemp
      exact hemp.false ⟨y, hy⟩
    · have hcard := h'.of_not_adj hxz hadj
      have h2card : 1 < Fintype.card (G.toSimple.commonNeighbors x z) :=
        Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨y, hy⟩, ⟨t, ht⟩, by simpa using hyt⟩
      omega

/-! ### Girth four -/

/-- A bipartite graph with a square has girth exactly four. -/
theorem girth_eq_four_of_square_of_isBipartite {G : CGraph} (hb : G.IsBipartite) {a b c d : G.V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c)
    (hbd : b ≠ d) : G.girth = 4 :=
  le_antisymm (girth_le_four_of_square hab hbc hcd hda hac hbd)
    (four_le_girth_of_isBipartite hb (not_isAcyclic_of_square hab hbc hcd hda hac hbd))

/-- **A Cartesian product of two bipartite graphs with an edge each has girth four**: the two
edges span a square, and the product is bipartite so there is no triangle. -/
@[toIsoGraph]
theorem girth_cartesianProduct {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) (hbG : G.IsBipartite) (hbH : H.IsBipartite) :
    (cartesianProduct G H).girth = 4 := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  refine girth_eq_four_of_square_of_isBipartite (hbG.cartesianProduct hbH)
    (a := ((a, b) : (cartesianProduct G H).V)) (b := (a', b)) (c := (a', b')) (d := (a, b'))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-- **A triangle in a Cartesian product projects to a triangle in a factor.**  Each product edge
moves exactly one coordinate; a triangle whose edges do not all move the same coordinate would
need an edge moving both. -/
theorem triangle_cartesianProduct {G H : CGraph}
    (hG : ∀ x y z : G.V, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hH : ∀ x y z : H.V, H.Adj x y → H.Adj y z → H.Adj z x → False)
    (x y z : (cartesianProduct G H).V) (h1 : (cartesianProduct G H).Adj x y)
    (h2 : (cartesianProduct G H).Adj y z) (h3 : (cartesianProduct G H).Adj z x) : False := by
  have hne : ∀ a b : (cartesianProduct G H).V, (cartesianProduct G H).Adj a b →
      (G.Adj a.1 b.1 ∧ a.2 = b.2 ∧ a.1 ≠ b.1) ∨ (H.Adj a.2 b.2 ∧ a.1 = b.1 ∧ a.2 ≠ b.2) := by
    intro a b hab
    rw [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, decide_eq_true_eq] at hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha, fun h ↦ H.loopless b.2 (h ▸ hb)⟩
    · exact Or.inl ⟨ha, hb, fun h ↦ G.loopless b.1 (h ▸ ha)⟩
  rcases hne _ _ h1 with ⟨g1, e1, n1⟩ | ⟨g1, e1, n1⟩ <;>
    rcases hne _ _ h2 with ⟨g2, e2, n2⟩ | ⟨g2, e2, n2⟩ <;>
      rcases hne _ _ h3 with ⟨g3, e3, n3⟩ | ⟨g3, e3, n3⟩
  all_goals first
    | exact hG _ _ _ g1 g2 g3
    | exact hH _ _ _ g1 g2 g3
    | simp_all

/-- **A Cartesian product of two triangle-free graphs with an edge each has girth four.** -/
@[toIsoGraph]
theorem girth_cartesianProduct_of_cliqueNum_le_two {G H : CGraph}
 (hG : 0 < G.E) (hH : 0 < H.E) (hcG : G.cliqueNum ≤ 2)
    (hcH : H.cliqueNum ≤ 2) : (cartesianProduct G H).girth = 4 := by
  have tri : ∀ (K : CGraph), K.cliqueNum ≤ 2 →
      ∀ x y z : K.V, K.Adj x y → K.Adj y z → K.Adj z x → False := by
    intro K hK x y z h1 h2 h3
    have := girth_eq_three_iff.1 (girth_eq_three_of_triangle h1 h2 h3)
    omega
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  have hbne : b ≠ b' := by rintro rfl; exact absurd hb (by simp [H.loopless])
  refine le_antisymm (girth_cartesianProduct_le_four hG hH)
    (four_le_girth (triangle_cartesianProduct (tri G hcG) (tri H hcH)) ?_)
  refine not_isAcyclic_of_square (a := ((a, b) : (cartesianProduct G H).V)) (b := (a', b))
    (c := (a', b')) (d := (a, b')) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-- **A Kneser graph with room for three disjoint blocks has girth three.** -/
@[toIsoGraph]
theorem girth_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) : (kneser n k).girth = 3 := by
  refine girth_eq_three_of_triangle
    (a := kneserBlock n k 0 (by omega)) (b := kneserBlock n k k (by omega))
    (c := kneserBlock n k (2 * k) (by omega)) ?_ ?_ ?_ <;>
  · rw [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨kneserBlock_ne hk (by omega), ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_kneserBlock, mem_kneserBlock] at hx
    omega

/-- **A Johnson graph on at least `k + 2` points has girth three**: three `k`-sets sharing a
common `(k-1)`-set are pairwise adjacent. -/
@[toIsoGraph]
theorem girth_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) : (johnson n k).girth = 3 := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine girth_eq_three_of_triangle
    (a := johnsonTri n k 0 (by omega)) (b := johnsonTri n k 1 (by omega))
    (c := johnsonTri n k 2 (by omega)) ?_ ?_ ?_ <;>
  · rw [johnson_adj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.add_sub_cancel]
    exact ⟨johnsonTri_ne (by omega), johnsonTri_inter (by omega)⟩

/-- **The complete bipartite graph `K_{m+2,n+2}` has girth four.** -/
@[toIsoGraph]
theorem girth_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).girth = 4 := by
  have hb : (bipartite (m + 2) (n + 2)).IsBipartite :=
    ⟨Sum.elim (fun _ ↦ false) (fun _ ↦ true), by rintro (a | b) (c | d) hadj <;> simp at hadj ⊢⟩
  refine girth_eq_four_of_square_of_isBipartite hb
    (a := (Sum.inl ⟨0, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (b := (Sum.inr ⟨0, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (c := (Sum.inl ⟨1, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (d := (Sum.inr ⟨1, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (by rw [bipartite_adj_inl_inr]) (by rw [bipartite_adj_inr_inl])
    (by rw [bipartite_adj_inl_inr]) (by rw [bipartite_adj_inr_inl]) ?_ ?_
  · intro h
    have h2 : (⟨0, by omega⟩ : Fin (m + 2)) = ⟨1, by omega⟩ := Sum.inl.inj h
    simp at h2
  · intro h
    have h2 : (⟨0, by omega⟩ : Fin (n + 2)) = ⟨1, by omega⟩ := Sum.inr.inj h
    simp at h2

end CGraph
