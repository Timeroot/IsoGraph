import IsoGraph.Core.Counts

/-!
# Connectivity, girth, distance and acyclicity

Connectivity, girth, distance and acyclicity for the core constructions: components of a disjoint
union and of a Cartesian product, the diameter and radius of a join and of the products,
bipartiteness, triangles and odd cycles, girth, and when a graph is a tree or a forest.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

@[simp] theorem isAcyclic_empty (n : ℕ) : (empty n).IsAcyclic := by
  simp [IsAcyclic]

@[simp] theorem isConnected_empty_one : (empty 1).IsConnected := by
  simp only [IsConnected]
  decide

@[simp] theorem isConnected_complete (n : ℕ) : (complete (n + 1)).IsConnected := by
  have : Nonempty (complete (n + 1)).V := ⟨(0 : Fin (n + 1))⟩
  simp [IsConnected]

@[simp] theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 := by
  simp [CGraph.diameter]
  have : Nontrivial (Fin (n + 2)) := inferInstance
  exact SimpleGraph.diam_top (α := Fin (n + 2))

@[simp] theorem isConnected_path (n : ℕ) : (path (n + 1)).IsConnected := by
  simpa [IsConnected] using SimpleGraph.pathGraph_connected n

@[simp] theorem isAcyclic_path (n : ℕ) : (path n).IsAcyclic := by
  simp [IsAcyclic, path_toSimple]
  intro v c hc
  have hne : c ≠ SimpleGraph.Walk.nil := hc.isCircuit.ne_nil
  have htrail := hc.isCircuit.isTrail
  -- No edges in pathGraph n when n ≤ 1
  by_cases hn : n ≤ 1
  · -- pathGraph n has no edges
    have no_edges : ∀ (a b : Fin n), ¬(SimpleGraph.pathGraph n).Adj a b := by
      intro a b hab
      rw [SimpleGraph.pathGraph_adj] at hab
      omega
    -- In a graph with no edges, every walk is nil. Contradiction with hne.
    have all_walks_nil : ∀ ⦃x y : Fin n⦄ (w : (SimpleGraph.pathGraph n).Walk x y), w.length = 0 := by
      intro x y w
      induction w with
      | nil => simp
      | cons hab w' ih =>
        exact absurd hab (no_edges _ _)
    exact hne (by
      have h0 : c.length = 0 := all_walks_nil c
      rw [SimpleGraph.Walk.length_eq_zero_iff] at h0
      exact h0)
  · -- n ≥ 2: use cut lemma
    -- Helper: In pathGraph n, adjacent vertices have indices differing by exactly 1.
    have adj_idx : ∀ (a b : Fin n), (SimpleGraph.pathGraph n).Adj a b → (a.val = b.val + 1 ∨ b.val = a.val + 1) := by
      intro a b hab
      rw [SimpleGraph.pathGraph_adj] at hab
      omega
    -- Helper: The only edge between {0..k} and {k+1..n-1} is {⟨k,...⟩, ⟨k+1,...⟩}.
    -- Specifically, if Adj x y, x.val ≤ k, and y.val ≥ k+1, then {x,y} = {⟨k,...⟩, ⟨k+1,...⟩}.
    have crossing_edge_unique : ∀ (k : ℕ) (hk : k + 1 < n) (x y : Fin n)
      (hadj : (SimpleGraph.pathGraph n).Adj x y) (hx : x.val ≤ k) (hy : k + 1 ≤ y.val),
      Sym2.mk (x, y) = Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) := by
      intro k hk x y hadj hx hy
      have hadj' := adj_idx x y hadj
      obtain hx1 | hy1 := hadj'
      · -- x.val = y.val + 1, but x ≤ k < y, impossible
        omega
      · -- y.val = x.val + 1, and x ≤ k < y, so x = k, y = k+1
        have hxval : x.val = k := by omega
        have hyval : y.val = k + 1 := by omega
        have hxFin : x = ⟨k, by omega⟩ := Fin.ext hxval
        have hyFin' : y = ⟨k + 1, hk⟩ := Fin.ext hyval
        exact congr_arg Sym2.mk (Prod.ext hxFin hyFin')
    -- Cut lemma: any walk from index ≥ k+1 to index ≤ k uses the crossing edge.
    have cut_lemma : ∀ (k : ℕ) (hk : k + 1 < n) (x y : Fin n) (hx : k + 1 ≤ x.val) (hy : y.val ≤ k)
      (w : (SimpleGraph.pathGraph n).Walk x y),
      Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) ∈ w.edges := by
      intro k hk x y hx hy w
      induction w with
      | nil =>
        simp at hx hy
        omega
      | @cons u v w huv rest ih =>
        -- huv : Adj u v, rest : Walk v w, ih : for walk v → w
        -- hx : k+1 ≤ u.val, hy : w.val ≤ k
        by_cases hv : v.val ≤ k
        · -- Edge huv crosses: u.val ≥ k+1, v.val ≤ k. Use crossing_edge_unique with (v, u).
          have hcross : Sym2.mk (v, u) = Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) :=
            crossing_edge_unique k hk v u (huv.symm) (by omega) (by omega)
          have : Sym2.mk (v, u) = Sym2.mk (u, v) := by
            symm
            show Sym2.mk (u, v) = Sym2.mk (v, u)
            dsimp only [Sym2.mk]
            exact Quot.sound (Sym2.Rel.swap u v)
          rw [SimpleGraph.Walk.edges_cons, ← hcross, this]
          exact List.Mem.head _
        · -- v.val ≥ k+1, recurse on rest
          push_neg at hv
          have := ih hv hy
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ this
    -- Sym2 symmetry helper
    have symm_edge : ∀ (a b : (path n).V), Sym2.mk (b, a) = Sym2.mk (a, b) := by
      intro a b
      dsimp only [Sym2.mk]
      exact Quot.sound (Sym2.Rel.swap b a)
    -- Now handle c. Decompose.
    cases c
    · exact absurd rfl hne
    · rename_i v_star huv rest
      have edge_in_cons : Sym2.mk (v, v_star) ∈ (SimpleGraph.Walk.cons huv rest).edges := by
        simp [SimpleGraph.Walk.edges_cons]
      obtain hvw | hvw := adj_idx v v_star huv
      · -- v.val = v_star.val + 1, so v_star < v. rest goes low→high.
        set k := v_star.val
        have hk : k + 1 < n := by omega
        have hvk : (v : (path n).V).val = k + 1 := hvw
        let vki : (path n).V := ⟨k, by omega⟩
        let VKI : (path n).V := ⟨k + 1, by omega⟩
        have hv_eq : v = VKI := Fin.ext hvk
        let crossing : Sym2 ((path n).V) := Sym2.mk (vki, VKI)
        have hedge_eq : Sym2.mk (v, v_star) = crossing := by
          subst hv_eq; exact symm_edge vki VKI
        -- reverse rest : Walk v v_star, high→low
        have hmem_rev : crossing ∈ (SimpleGraph.Walk.reverse rest).edges := by
          have h1 : k + 1 ≤ (v : Fin n).val := hvk.ge
          have h2 : (v_star : Fin n).val ≤ k := le_rfl
          convert cut_lemma k hk v v_star h1 h2 (SimpleGraph.Walk.reverse rest) using 1
        rw [SimpleGraph.Walk.edges_reverse] at hmem_rev
        have hmem : crossing ∈ rest.edges := by
          rw [List.mem_reverse] at hmem_rev; exact hmem_rev
        have hnodu := htrail.edges_nodup
        rw [SimpleGraph.Walk.edges_cons] at hnodu edge_in_cons
        rw [hedge_eq] at edge_in_cons
        have hnotin : crossing ∉ rest.edges := by
          intro h
          rw [hedge_eq.symm] at h
          exact (List.nodup_cons.mp hnodu).1 h
        exact hnotin hmem
      · -- v_star.val = v.val + 1, so v_star > v. rest goes high→low.
        set k := (v : (path n).V).val
        have hk : k + 1 < n := by omega
        let vki : (path n).V := ⟨k, by omega⟩
        let VKI : (path n).V := ⟨k + 1, by omega⟩
        have hvstar_eq : v_star = VKI := Fin.ext hvw
        let crossing : Sym2 ((path n).V) := Sym2.mk (vki, VKI)
        have hedge_eq : Sym2.mk (v, v_star) = crossing := by
          subst hvstar_eq; rfl
        have hmem : crossing ∈ rest.edges :=
          cut_lemma k hk v_star v (by omega) (by omega) rest
        have hnodu := htrail.edges_nodup
        rw [SimpleGraph.Walk.edges_cons] at hnodu edge_in_cons
        rw [hedge_eq] at edge_in_cons
        have hnotin : crossing ∉ rest.edges := by
          intro h
          rw [hedge_eq.symm] at h
          exact (List.nodup_cons.mp hnodu).1 h
        exact hnotin hmem

@[simp] theorem isTree_path (n : ℕ) : (path (n + 1)).IsTree :=
  ⟨isConnected_path n, isAcyclic_path (n + 1)⟩

@[simp] theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := by
  simp [diameter, path_toSimple]
  rw [SimpleGraph.diam]
  -- Build walks from 0 to i of length i for all i : Fin (n+1)
  have walk0to : ∀ i : Fin (n + 1), ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk 0 i, p.length = i.val := by
    intro i
    induction i using Fin.induction with
    | zero =>
      let p : (SimpleGraph.pathGraph (n + 1)).Walk 0 0 := .nil
      exact ⟨p, rfl⟩
    | succ i ih =>
      obtain ⟨p, hp⟩ := ih
      have hadj : (SimpleGraph.pathGraph (n + 1)).Adj (i.castSucc) (i.succ) := by
        simp [SimpleGraph.pathGraph_adj]
      let single : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ :=
        SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ)
      have hsingle : single.length = 1 := by simp [single]
      exact ⟨p.append single, by simp [hp, hsingle]⟩
  -- From this, edist 0 i ≤ ↑i.val
  have edist0_le : ∀ i : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).edist 0 i ≤ ↑(i.val : ℕ) := by
    intro i
    obtain ⟨p, hp⟩ := walk0to i
    rw [SimpleGraph.edist]
    exact le_trans (iInf_le (f := fun w : (SimpleGraph.pathGraph (n + 1)).Walk 0 i => (w.length : ℕ∞)) p) (by simp [hp])
  -- upWalk i : walk from castSucc i to succ i of length 1, for i : Fin n
  have upWalk : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ, p.length = 1 := by
    intro i
    exact ⟨SimpleGraph.Walk.cons (by simp [SimpleGraph.pathGraph_adj])
      (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ), by simp⟩
  -- downWalk i : walk from succ i to castSucc i, by reversing upWalk
  have downWalk : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.castSucc, p.length = 1 := by
    intro i
    obtain ⟨q, hq⟩ := upWalk i
    exact ⟨q.reverse, by simp [hq]⟩
  -- Monotone up walk: for u v with u.val ≤ v.val, walk from u to v of length v - u
  -- By induction on the difference. This is complex; let me use a simpler approach.
  -- For any i : Fin (n+1) and k : ℕ with i.val + k ≤ n, walk from i to ⟨i+k, ...⟩ of length k.
  -- Adjacency between any i and i+1 in pathGraph (n+1)
  have adj_succ : ∀ i : Fin n, (SimpleGraph.pathGraph (n + 1)).Adj i.castSucc i.succ := by
    intro i; simp [SimpleGraph.pathGraph_adj]
  -- Walk from i to i.succ of length 1
  have walk_succ : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ, p.length = 1 := by
    intro i
    exact ⟨SimpleGraph.Walk.cons (adj_succ i)
      (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ), by simp⟩
  -- Build walk from i to j (where j = i + k) by iterating walk_succ k times
  -- Target vertex: i + k in Fin (n+1), when i.val + k < n + 1
  let addK (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1) : Fin (n + 1) := ⟨i.val + k, hk⟩
  have upWalkAny : ∀ (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1),
      ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i (addK i k hk), p.length = k := by
    intro i k hk
    induction k with
    | zero =>
      exact ⟨.nil, rfl⟩
    | succ m ih =>
      obtain ⟨p, hp⟩ := ih (by omega)
      have hm : (i : ℕ) + m < n := by omega
      obtain ⟨q, hq⟩ := walk_succ ⟨i.val + m, hm⟩
      exact ⟨p.append q, by simp [hp, hq]⟩
  -- hupper: edist u v ≤ ↑n for all u, v
  have hinner : ∀ {u v : Fin (n + 1)}, (u : ℕ) ≤ v → (SimpleGraph.pathGraph (n + 1)).edist u v ≤ ↑n := by
    intro u v huv
    have hvk : (u : ℕ) + (v - u) < n + 1 := by omega
    have hkep : addK u (v - u) hvk = v := by
      ext; simp [addK, Nat.add_sub_of_le huv]
    obtain ⟨p, hp⟩ := upWalkAny u (v - u) hvk
    have hedist_le : (SimpleGraph.pathGraph (n + 1)).edist u (addK u (v - u) hvk) ≤ ↑(v - u : ℕ) := by
      exact SimpleGraph.edist_le p |>.trans (by rw [hp])
    rw [hkep] at hedist_le
    exact hedist_le.trans (Nat.cast_le.mpr (by omega))
  have hupper : ∀ u v : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).edist u v ≤ ↑n := by
    intro u v
    by_cases huv : (u : ℕ) ≤ v
    · exact hinner huv
    · rw [SimpleGraph.edist_comm]
      exact hinner (le_of_lt (not_le.mp huv))
  -- hexist_upper
  have hexist_upper : (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ ≤ ↑n := hupper 0 ⟨n, Nat.lt_succ_self n⟩
  -- Key: for any walk, b.val ≤ a.val + walk.length
  have walk_pot : ∀ {a b : Fin (n + 1)} (p : (SimpleGraph.pathGraph (n + 1)).Walk a b),
      (b : ℕ) ≤ (a : ℕ) + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | @cons u v w hadj p ih =>
      have hadj' : (SimpleGraph.pathGraph (n + 1)).Adj u v := hadj
      rw [SimpleGraph.pathGraph_adj] at hadj'
      have : (v : ℕ) ≤ (u : ℕ) + 1 := by
        rcases hadj' with h | h <;> omega
      simp [SimpleGraph.Walk.length_cons]
      omega
  -- hexist_lower: edist 0 last ≥ ↑n
  have hexist_lower : ↑(n : ℕ∞) ≤ (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ := by
    rw [SimpleGraph.edist]
    by_cases hne : Nonempty ((SimpleGraph.pathGraph (n + 1)).Walk 0 ⟨n, Nat.lt_succ_self n⟩)
    · apply le_ciInf
      intro p
      have := walk_pot p
      simp at this ⊢
      exact_mod_cast this
    · push_neg at hne
      simp
  -- hexist
  have hexist : (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ = ↑n :=
    le_antisymm hexist_upper hexist_lower
  -- iSup bounds
  have hiSup_ge : ↑(n : ℕ∞) ≤ ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 := by
    rw [← hexist]
    exact le_iSup (f := fun p : (Fin (n + 1)) × (Fin (n + 1)) => (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2) ⟨0, ⟨n, Nat.lt_succ_self n⟩⟩
  have hiSup_le : ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 ≤ ↑(n : ℕ∞) :=
    ciSup_le fun p => hupper p.1 p.2
  have hisup : ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 = ↑(n : ℕ∞) :=
    le_antisymm hiSup_le hiSup_ge
  have : ⨆ u : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).eccent u = ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 := by
    simp only [SimpleGraph.eccent]
    have : ∀ {f : Fin (n + 1) → Fin (n + 1) → ℕ∞}, (⨆ u, ⨆ v, f u v) = ⨆ p : Fin (n + 1) × Fin (n + 1), f p.1 p.2 := by
      intro f
      exact iSup_prod' f
    exact this
  have hediam : (SimpleGraph.pathGraph (n + 1)).ediam = ⨆ u : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).eccent u := by
    simp [SimpleGraph.ediam]
  rw [hediam, this, hisup]
  simp

@[simp] theorem isConnected_cycle (n : ℕ) : (cycle (n + 1)).IsConnected := by
  rcases n with _ | n
  · -- n = 0: cycle 1, single vertex, trivially connected
    show (cycle 1).toSimple.Connected
    let _ : Nonempty (cycle 1).V := ⟨⟨0, by omega⟩⟩
    have huv : ∀ (u v : (cycle 1).V), u = v := by
      intro u v
      have hu : u.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ u.is_lt)
      have hv : v.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ v.is_lt)
      exact Fin.ext (hu.trans hv.symm)
    exact { preconnected := fun u v => by rw [huv u v] }
  · -- n ≥ 1: m ≥ 2
    set m := n + 1 + 1
    -- step_adj: from i can go to (i+1)%m
    have step_adj : ∀ i : Fin m, (cycle m).toSimple.Adj i ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
      intro i
      simp only [cycle, toSimple_adj, ofRel_adj]
      have hi_lt : (i : ℕ) < m := i.is_lt
      have hne : (i : ℕ) ≠ (i.val + 1) % m := by
        intro h
        have him1 : (i : ℕ) + 1 ≤ m := by omega
        by_cases hlt : (i : ℕ) + 1 < m
        · have hmod : ((i : ℕ) + 1) % m = (i : ℕ) + 1 := Nat.mod_eq_of_lt hlt
          rw [hmod] at h; omega
        · have hneq : (i : ℕ) + 1 = m := by omega
          have hmod2 : ((i : ℕ) + 1) % m = 0 := by rw [hneq]; simp
          rw [hmod2] at h; omega
      set j : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩
      have hne' : i ≠ j := by
        intro h; have := congr_arg Fin.val h; simp [j] at this; exact hne this
      simp [hne', j]
    -- Walk step: reachability from i to (i+k)%m for any k
    have walk_step : ∀ (i : Fin m) (k : ℕ), (cycle m).toSimple.Reachable i ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ := by
      intro i k
      induction k with
      | zero =>
        show (cycle m).toSimple.Reachable i ⟨(i.val + 0) % m, Nat.mod_lt _ (by omega)⟩
        simp [Nat.mod_eq_of_lt (by omega : (i : ℕ) < m)]
      | succ k ih =>
        show (cycle m).toSimple.Reachable i ⟨(i.val + (k + 1)) % m, Nat.mod_lt _ (by omega)⟩
        have hstep : (cycle m).toSimple.Adj ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ ⟨((i.val + k) + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
          convert step_adj ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ using 2
          simp
        obtain ⟨w⟩ := ih
        exact ⟨w.concat hstep⟩
    -- Reachability between any two vertices
    have reach_all : ∀ (i j : Fin m), (cycle m).toSimple.Reachable i j := by
      intro i j
      let k := j.val + m - i.val
      have hk : (i.val + k) % m = j.val := by
        simp [k]
        have : (i.val + (j.val + m - i.val)) = j.val + m := by omega
        have h1 : (↑i + (↑j + m - ↑i)) = ↑j + m := ‹_›
        rw [h1]
        have h2 : ((↑j + m) % m : ℕ) = ↑j := by
          simp [Nat.mod_eq_of_lt (by omega : (j : ℕ) < m)]
        exact h2
      have h_eq : j = ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ := by
        exact Fin.ext hk.symm
      rw [h_eq]
      exact walk_step i k
    exact { preconnected := reach_all, nonempty := ⟨⟨0, by omega⟩⟩ }

@[simp] theorem not_isAcyclic_cycle (n : ℕ) : ¬(cycle (n + 3)).IsAcyclic := by
  by_contra h_ac
  simp only [IsAcyclic, CGraph.IsAcyclic] at h_ac
  have hconn : (cycle (n + 3)).IsConnected := isConnected_cycle (n + 2)
  have hE : (cycle (n + 3)).E = n + 3 := E_cycle n
  have htree_simple : (cycle (n + 3)).toSimple.IsTree := ⟨hconn, h_ac⟩
  -- Need: for a tree, edgeFinset.card = card V - 1
  have h1 : (cycle (n + 3)).toSimple.IsTree := htree_simple
  -- A tree on V vertices has |V|-1 edges. We know |V| = n+3 and |E| = n+3, contradiction.
  have hV : FinEnum.card (cycle (n + 3)).V = n + 3 := card_cycle (n + 3)
  -- A tree is a minimal connected graph: removing any edge disconnects it.
  -- Also, a tree on V vertices has |V|-1 edges. Let me find/search for this.
  -- Alternative: use that G.toSimple is a tree, so it has a unique path between any two vertices,
  -- and use rank of graphic matroid... too complex.
  -- Let me try to prove |E| = |V|-1 for a tree by using SimpleGraph's tree lemmas.
  have h_edges := SimpleGraph.IsTree.card_edgeFinset h1
  rw [← FinEnum.card_eq_fintypeCard, hV] at h_edges
  -- h_edges : edgeFinset.card + 1 = n + 3
  -- hE : edgeFinset.card = n + 3 (via CGraph.E)
  have : (cycle (n + 3)).toSimple.edgeFinset.card = (cycle (n + 3)).E := by
    simp [CGraph.E]
  rw [hE] at this
  omega

@[simp] theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 := by
  show (cycle (n + 1)).toSimple.diam = (n + 1) / 2
  simp only [SimpleGraph.diam]
  set m : ℕ := (n + 1) / 2
  show ((cycle (n + 1)).toSimple.ediam).toNat = m
  by_cases hn : n = 0
  · subst hn
    simp [m]
    exact Or.inl (by show Subsingleton (Fin 1); exact inferInstance)
  have h_edge : ∀ i : Fin (n + 1), (cycle (n + 1)).toSimple.Adj i (i + 1) := by
    intro i
    simp [cycle, ofRel_adj, toSimple_adj]
    exact ⟨hn, Or.inl (by rw [Fin.val_add]; simp)⟩
  -- Clockwise walk of length t from u to (u + t)
  let finAdd : ℕ → Fin (n + 1) := fun t => ⟨t % (n + 1), Nat.mod_lt t (Nat.succ_pos n)⟩
  have h_edist_walk : ∀ (u : Fin (n + 1)) (t : ℕ), t ≤ n → (cycle (n + 1)).toSimple.edist u (u + finAdd t) ≤ (t : ℕ∞) := by
    intro u t
    induction t with
    | zero =>
      intro ht
      simp [finAdd, SimpleGraph.edist_self]
    | succ t ih =>
      intro ht
      have hstep : (u + finAdd t) + 1 = u + finAdd (t + 1) := by
        simp [finAdd, Fin.add_def, Nat.add_assoc]
      have hedge : (cycle (n + 1)).toSimple.Adj (u + finAdd t) (u + finAdd (t + 1)) := by
        rw [← hstep]
        exact h_edge (u + finAdd t)
      have h_edist_succ : (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) ≤ 1 := by
        have : (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) ≤ ↑(SimpleGraph.Walk.nil.cons hedge).length := SimpleGraph.Walk.edist_le (SimpleGraph.Walk.nil.cons hedge)
        simpa using this
      calc (cycle (n + 1)).toSimple.edist u (u + finAdd (t + 1))
          ≤ (cycle (n + 1)).toSimple.edist u (u + finAdd t) +
              (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) :=
            SimpleGraph.edist_triangle
        _ ≤ ↑t + 1 := by
            exact add_le_add (ih (by omega)) h_edist_succ
        _ = ↑(t + 1) := by push_cast; rfl
  have h_edist_le : ∀ u v : Fin (n + 1), (cycle (n + 1)).toSimple.edist u v ≤ (m : ℕ∞) := by
    intro u v
    let t : ℕ := (v.val + (n + 1) - u.val) % (n + 1)  -- clockwise distance, 0 ≤ t ≤ n
    -- min(t, (n+1)-t) ≤ m
    have hmin : t ≤ m ∨ (n + 1 - t) ≤ m := by
      have ht : t < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
      have ht_le : t ≤ n := Nat.le_of_lt_succ ht
      have : t + (n + 1 - t) = n + 1 := by omega
      by_contra h
      push_neg at h
      omega
    -- Helper: u + (v - u) = v in Fin (n+1)
    have hfin_add_sub : ∀ (u v : Fin (n + 1)), u + (v - u) = v := by
      intro u v
      ext
      simp
    -- Helper: Fin.val of subtraction
    have ht_def : t = (v - u).val := by
      simp [t, Fin.sub_def]
      have : (v : ℕ) + (n + 1) - u = (n + 1 - u + v : ℕ) := by omega
      rw [this]
    let t' : ℕ := (u.val + (n + 1) - v.val) % (n + 1)
    have ht'_def : t' = (u - v).val := by
      simp [t', Fin.sub_def]
      have : (u : ℕ) + (n + 1) - v = (n + 1 - v + u : ℕ) := by omega
      rw [this]
    rcases hmin with htle | hbtle
    · -- clockwise walk from u to v has edist ≤ t ≤ m
      have huv : v = u + finAdd t := by
        have : finAdd t = (v - u : Fin (n + 1)) := by
          ext; simp [finAdd, ht_def]
          omega
        rw [this]
        exact (hfin_add_sub u v).symm
      rw [huv]
      exact (h_edist_walk u t (by omega)).trans (WithBot.coe_le_coe.mpr htle)
    · -- counterclockwise: use symmetry and walk from v to u clockwise
      rw [SimpleGraph.edist_comm]
      -- clockwise distance from v to u
      have ht'_le_n : t' ≤ n := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos n))
      -- t' ≤ m (since t' = (n+1-t) % (n+1) and hbtle says n+1-t ≤ m)
      have ht'_le_m : t' ≤ m := by
        by_cases ht0 : t = 0
        · simp [t']
          omega
        · -- t > 0 case: t' + t = n + 1
          have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
          have ht_lt : t < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
          have ht'_lt : t' < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
          have htsum : t' + t = n + 1 := by
            have hsum_zero : (u - v : Fin (n + 1)) + (v - u) = 0 := by
              ext; simp
            have hval : ((u - v).val + (v - u).val) % (n + 1) = 0 := by
              have h1 : ((u - v : Fin (n + 1)) + (v - u)).val = (0 : Fin (n + 1)).val := by rw [hsum_zero]
              rw [Fin.val_add] at h1
              simp at h1
              exact h1
            have hvu_val : (v - u).val = t := ht_def.symm
            have hu_val : (u - v).val = t' := ht'_def.symm
            have hpos : 0 < (v - u).val := hvu_val ▸ ht_pos
            have hlt : (v - u).val < n + 1 := (v - u).isLt
            have hlt' : (u - v).val < n + 1 := (u - v).isLt
            have hdvd : (n + 1 : ℕ) ∣ ((u - v).val + (v - u).val) := Nat.dvd_of_mod_eq_zero hval
            obtain ⟨k, hk⟩ := hdvd
            rcases k with (_ | _ | k) <;> simp at hk
            · exfalso
              have h1 : (v - u : Fin (n + 1)) = 0 := hk.2
              have h2 : (v - u).val = 0 := by simpa using h1
              omega
            · rw [← hvu_val, ← hu_val]; exact hk
            · exfalso
              have hge : (n + 1) * (k + 1 + 1) ≥ 2 * (n + 1) := by nlinarith
              omega
          omega
      have huv' : u = v + finAdd t' := by
        have : finAdd t' = (u - v : Fin (n + 1)) := by
          ext; simp [finAdd, ht'_def]
          omega
        rw [this]
        exact (hfin_add_sub v u).symm
      rw [huv']
      exact (h_edist_walk v t' ht'_le_n).trans (WithBot.coe_le_coe.mpr ht'_le_m)
  have h_ediam_le : (cycle (n + 1)).toSimple.ediam ≤ (m : ℕ∞) :=
    SimpleGraph.ediam_le_of_edist_le h_edist_le
  -- Potential function for lower bounds
  let f : Fin (n + 1) → ℤ := fun i => min ((i : ℤ)) ((n + 1) - (i : ℤ))
  have hf_adj : ∀ {i j : Fin (n + 1)}, (cycle (n + 1)).toSimple.Adj i j → |(f j : ℤ) - (f i : ℤ)| ≤ 1 := by
    intro i j hij
    -- Characterize edges: Adj i j ↔ j = i + 1 ∨ i = j + 1 in Fin (n+1)
    simp [cycle, ofRel_adj, toSimple_adj] at hij
    rcases hij with ⟨hne, hj|hi⟩
    · -- j = i + 1
      have hij1 : j = i + 1 := by
        ext; simp [Fin.val_add] at hj ⊢; omega
      rw [hij1]
      simp only [f]
      rw [abs_sub_le_iff]
      by_cases hmax : (i : ℕ) = n
      · -- i is the last element, i+1 wraps to 0
        have : (i + 1 : Fin (n + 1)) = 0 := by
          ext; simp [Fin.val_add, hmax]
        rw [this]
        simp only [Fin.val_zero]
        simp
        constructor <;> omega
      · -- i.val < n, so (i+1).val = i.val + 1
        have hi_lt_n : (i : ℕ) < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hmax
        have hmod : ((i : ℕ) + 1) % (n + 1) = (i : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
        have hval_i1 : ((i + 1 : Fin (n + 1)) : ℤ) = (i : ℤ) + 1 := by
          simp [Fin.val_add, hmod]
        rw [hval_i1]
        set a := (i : ℤ) with ha_def
        simp only [Int.min_def]
        split <;> split <;> omega
    · -- i = j + 1
      have hij2 : i = j + 1 := by
        ext; simp [Fin.val_add] at hi ⊢; omega
      rw [hij2]
      simp only [f]
      rw [abs_sub_le_iff]
      by_cases hmax : (j : ℕ) = n
      · have : (j + 1 : Fin (n + 1)) = 0 := by
          ext; simp [Fin.val_add, hmax]
        rw [this]
        simp only [Fin.val_zero]
        simp
        constructor <;> omega
      · have hj_lt_n : (j : ℕ) < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hmax
        have hmod : ((j : ℕ) + 1) % (n + 1) = (j : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
        have hval_j1 : ((j + 1 : Fin (n + 1)) : ℤ) = (j : ℤ) + 1 := by
          simp [Fin.val_add, hmod]
        rw [hval_j1]
        set a := (j : ℤ) with ha_def
        simp only [Int.min_def]
        split <;> split <;> omega
  have hf_walk : ∀ {u v : Fin (n + 1)} (w : (cycle (n + 1)).toSimple.Walk u v),
      |(f v : ℤ) - (f u : ℤ)| ≤ (w.length : ℤ) := by
    intro u v w
    induction w with
    | nil => simp [SimpleGraph.Walk.length]
    | @cons u' w' hstep ih pw ihw =>
      calc |(f hstep : ℤ) - (f u' : ℤ)|
          = |((f hstep : ℤ) - (f w' : ℤ)) + ((f w' : ℤ) - (f u' : ℤ))| := by
            congr 1; ring
        _ ≤ |(f hstep : ℤ) - (f w' : ℤ)| + |(f w' : ℤ) - (f u' : ℤ)| := abs_add_le _ _
        _ ≤ (pw.length : ℤ) + 1 := by
            exact add_le_add ihw (hf_adj ih)
        _ = (SimpleGraph.Walk.cons ih pw).length := by simp [SimpleGraph.Walk.length]
  have hf0 : f (0 : Fin (n + 1)) = 0 := by
    show min ((0 : ℤ)) ((n : ℤ) + 1 - (0 : ℤ)) = 0
    simp; omega
  have hfm : f ⟨m, by omega⟩ = (m : ℤ) := by
    show min ((m : ℤ)) ((n : ℤ) + 1 - (m : ℤ)) = (m : ℤ)
    exact min_eq_left (by omega)
  have h_lb : ∀ {w : (cycle (n + 1)).toSimple.Walk (0 : Fin (n + 1)) ⟨m, by omega⟩}, (m : ℤ) ≤ (w.length : ℤ) := by
    intro w
    have := hf_walk w
    rw [hfm, hf0] at this
    simpa using this
  have h_edist_ge : ∃ u v : Fin (n + 1), (m : ℕ∞) ≤ (cycle (n + 1)).toSimple.edist u v := by
    refine ⟨(0 : Fin (n + 1)), (⟨m, by omega⟩ : Fin (n + 1)), ?_⟩
    let base : Fin (n + 1) := ⟨0, by omega⟩
    have hfinAdd : base + finAdd m = ⟨m, by omega⟩ := by
      ext; simp [finAdd, base]; omega
    have hreach : (cycle (n + 1)).toSimple.Reachable base ⟨m, by omega⟩ := by
      rw [← hfinAdd]
      have hne : (cycle (n + 1)).toSimple.edist base (base + finAdd m) ≠ ⊤ := by
        have : (m : ℕ∞) ≠ ⊤ := by simp
        exact ne_top_of_le_ne_top this (h_edist_walk base m (by omega))
      exact (SimpleGraph.edist_ne_top_iff_reachable).mp hne
    -- Reachable: use le_csInf
    rw [SimpleGraph.edist]
    apply le_csInf
    · exact ⟨_, ⟨hreach.some, rfl⟩⟩
    · rintro _ ⟨w, rfl⟩
      show (m : ℕ∞) ≤ ↑w.length
      exact_mod_cast @h_lb w
  obtain ⟨u, v, huv⟩ := h_edist_ge
  have h_m_le_ediam : (m : ℕ∞) ≤ (cycle (n + 1)).toSimple.ediam :=
    huv.trans (SimpleGraph.edist_le_ediam)
  have h_ediam_eq : (cycle (n + 1)).toSimple.ediam = (m : ℕ∞) := le_antisymm h_ediam_le h_m_le_ediam
  rw [h_ediam_eq]
  simp

/-- A disjoint union of two nonempty graphs is disconnected. -/
theorem not_isConnected_disjUnion (hG : 0 < FinEnum.card G.V) (hH : 0 < FinEnum.card H.V) :
    ¬(G ⊕g H).IsConnected := by
  simp only [CGraph.IsConnected]
  intro h
  have hGne : Nonempty G.V := FinEnum.card_pos_iff.mp hG
  have hHne : Nonempty H.V := FinEnum.card_pos_iff.mp hH
  let a := hGne.some
  let b := hHne.some
  have hr : (G ⊕g H).toSimple.Reachable (.inl a) (.inr b) := h (Sum.inl a) (.inr b)
  -- Key lemma: adjacency preserves "side" (inl vs inr)
  let side : (G.V ⊕ H.V) → Bool := fun | Sum.inl _ => true | Sum.inr _ => false
  have side_eq_of_adj : ∀ (x y : G.V ⊕ H.V), (G ⊕g H).Adj x y → side x = side y := by
    intro x y h_adj
    cases x with
    | inl a =>
      cases y with
      | inl c => simp [side]
      | inr d => simp [disjUnion_adj_inl_inr] at h_adj
    | inr b =>
      cases y with
      | inl c => simp [disjUnion_adj_inr_inl] at h_adj
      | inr d => simp [side]
  -- Adjacency preserves side, so Reachability preserves side
  have keep_side : ∀ {u v : G.V ⊕ H.V}, (G ⊕g H).toSimple.Reachable u v → side u = side v := by
    intro u v huv
    show side u = side v
    induction huv
    rename_i w
    induction w with
    | nil => rfl
    | @cons w' x y hp e ih => rw [side_eq_of_adj _ _ hp, ih]
  -- inl a and inr b have different sides, contradiction
  have hside : side (.inl a) = true := rfl
  have hside2 : side (.inr b) = false := rfl
  have := keep_side hr
  simp [hside, hside2] at this

theorem isConnected_join
    (hG : 0 < FinEnum.card G.V) (hH : 0 < FinEnum.card H.V) : (G ∇g H).IsConnected := by
  simp only [IsConnected, join, CGraph.toSimple]
  have hcross : ∀ (a : G.V) (b : H.V),
      ((G ∇g H).toSimple.Adj (Sum.inl a) (Sum.inr b) = true) := by
    simp [join, CGraph.toSimple, disjUnion_adj_inl_inr]
  have hcross' : ∀ (a : G.V) (b : H.V),
      ((G ∇g H).toSimple.Adj (Sum.inr b) (Sum.inl a) = true) := by
    simp [join, CGraph.toSimple, disjUnion_adj_inr_inl]
  set J := (G ∇g H).toSimple
  obtain ⟨a0⟩ := FinEnum.card_pos_iff.mp hG
  obtain ⟨b0⟩ := FinEnum.card_pos_iff.mp hH
  let walk_inl_inr (a : G.V) (b : H.V) : J.Walk (Sum.inl a) (Sum.inr b) :=
    SimpleGraph.Walk.cons (by rw [hcross a b]) SimpleGraph.Walk.nil
  let walk_inr_inl (b : H.V) (a : G.V) : J.Walk (Sum.inr b) (Sum.inl a) :=
    SimpleGraph.Walk.cons (by rw [hcross' a b]) SimpleGraph.Walk.nil
  have hreach : ∀ v : (G ∇g H).V, J.Reachable (Sum.inl a0) v := by
    intro v
    match v with
    | Sum.inl a => exact ⟨(walk_inl_inr a0 b0).append (walk_inr_inl b0 a)⟩
    | Sum.inr b => exact ⟨walk_inl_inr a0 b⟩
  show J.Connected
  have hne : Nonempty (G.join H).V := ⟨Sum.inl a0⟩
  exact ⟨fun u v => ⟨(SimpleGraph.Reachable.symm (hreach u)).some.append ((hreach v).some)⟩⟩

end

/-! ## Bipartiteness

`CGraph.IsBipartite` is a two-colouring of the vertices with no monochromatic edge.  The
constructions carry colourings around in the obvious way, and a colouring is exactly what
`Iso.tensorTwoOfColouring` needs to split the double cover. -/

/-- A disjoint union of bipartite graphs is bipartite. -/
theorem IsBipartite.disjUnion {G H : CGraph} (hG : G.IsBipartite) (hH : H.IsBipartite) :
    (G ⊕g H).IsBipartite := by
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
    (hG : G.IsBipartite) (hH : H.IsBipartite) : (G □g H).IsBipartite := by
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
@[toIsoGraph isBipartite_tensorProduct_left]
theorem IsBipartite.tensorProduct_left {G H : CGraph}
    (hG : G.IsBipartite) : (G ⊗g H).IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  refine ⟨fun p ↦ c p.1, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.tensorProduct_adj] at hxy
  simp only [Bool.and_eq_true] at hxy
  exact hc x x' hxy.1

@[toIsoGraph isBipartite_tensorProduct_right]
theorem IsBipartite.tensorProduct_right {G H : CGraph}
    (hH : H.IsBipartite) : (G ⊗g H).IsBipartite := by
  obtain ⟨c, hc⟩ := hH
  refine ⟨fun p ↦ c p.2, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.tensorProduct_adj] at hxy
  simp only [Bool.and_eq_true] at hxy
  exact hc y y' hxy.2

/-- A summand of a bipartite disjoint union is bipartite: restrict the colouring. -/
theorem IsBipartite.of_disjUnion_left {G H : CGraph} (h : (G ⊕g H).IsBipartite) :
    G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a ↦ c (.inl a), fun x y hxy ↦ hc _ _ (by rwa [disjUnion_adj_inl_inl])⟩

theorem IsBipartite.of_disjUnion_right {G H : CGraph} (h : (G ⊕g H).IsBipartite) :
    H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b ↦ c (.inr b), fun x y hxy ↦ hc _ _ (by rwa [disjUnion_adj_inr_inr])⟩

/-- A factor of a bipartite Cartesian product is bipartite: a fixed vertex of the other factor
cuts out a copy of it. -/
theorem IsBipartite.of_cartesianProduct_left {G H : CGraph}
    (hH : Nonempty H.V) (h : (G □g H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨b⟩ := hH
  refine ⟨fun a ↦ c (a, b), fun x y hxy ↦ hc (x, b) (y, b) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

theorem IsBipartite.of_cartesianProduct_right {G H : CGraph}
    (hG : Nonempty G.V) (h : (G □g H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨a⟩ := hG
  refine ⟨fun b ↦ c (a, b), fun x y hxy ↦ hc (a, x) (a, y) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

/-- **A Cartesian product of nonempty graphs is bipartite exactly when both factors are.** -/
@[toIsoGraph]
theorem isBipartite_cartesianProduct_iff {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G □g H).IsBipartite ↔ G.IsBipartite ∧ H.IsBipartite :=
  ⟨fun h ↦ ⟨h.of_cartesianProduct_left ‹Nonempty H.V›, h.of_cartesianProduct_right ‹Nonempty G.V›⟩,
    fun h ↦ IsBipartite.cartesianProduct h.1 h.2⟩

/-- **Every acyclic graph is bipartite**: a forest two-colours. -/
@[toIsoGraph]
theorem isBipartite_of_isAcyclic {G : CGraph} (h : G.IsAcyclic) : G.IsBipartite := by
  rw [isBipartite_iff_colorable]
  exact h.isBipartite

/-- **A tree is exactly a connected acyclic graph.** -/
@[toIsoGraph]
theorem isTree_iff_isConnected_and_isAcyclic (G : CGraph) :
    G.IsTree ↔ G.IsConnected ∧ G.IsAcyclic :=
  SimpleGraph.isTree_iff _

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
@[toIsoGraph]
theorem IsBipartite.of_join_left {G H : CGraph}
    (h : (G ∇g H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a ↦ c (.inl a), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inl_inl])⟩

@[toIsoGraph]
theorem IsBipartite.of_join_right {G H : CGraph}
    (h : (G ∇g H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b ↦ c (.inr b), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inr_inr])⟩

/-- An edge on one side of a join, together with any vertex on the other side, is a triangle. -/
theorem not_isBipartite_join_of_adj_left {G H : CGraph}
    {a b : G.V} (hab : G.Adj a b) (c : H.V) : ¬ (G ∇g H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inl a) (b := .inl b) (d := .inr c)
    (by rwa [join_adj_inl_inl]) (join_adj_inl_inr G H a c) (join_adj_inl_inr G H b c)

theorem not_isBipartite_join_of_adj_right {G H : CGraph}
    {a b : H.V} (hab : H.Adj a b) (c : G.V) : ¬ (G ∇g H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inr a) (b := .inr b) (d := .inl c)
    (by rwa [join_adj_inr_inr]) (join_adj_inr_inl G H a c) (join_adj_inr_inl G H b c)

/-- Three nonempty sides give a triangle, whatever the graphs on them are. -/
@[toIsoGraph]
theorem not_isBipartite_join_join {G H K : CGraph}
    [Nonempty G.V] [Nonempty H.V] [Nonempty K.V] :
    ¬ (G ∇g (H ∇g K)).IsBipartite := by
  obtain ⟨a⟩ := ‹Nonempty G.V›
  obtain ⟨b⟩ := ‹Nonempty H.V›
  obtain ⟨c⟩ := ‹Nonempty K.V›
  exact not_isBipartite_of_triangle (a := .inl a) (b := .inr (.inl b)) (d := .inr (.inr c))
    (join_adj_inl_inr _ _ _ _) (join_adj_inl_inr _ _ _ _)
    (by rw [join_adj_inr_inr, join_adj_inl_inr])

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

theorem isConnected_cartesianProduct_iff (G H : CGraph) :
    (G □g H).IsConnected ↔ G.IsConnected ∧ H.IsConnected := by
  show (G □g H).toSimple.Connected ↔ _
  rw [toSimple_cartesianProduct]
  exact SimpleGraph.connected_boxProd

/-- Euler's count for trees, on `CGraph`: a graph is a tree exactly when it is connected and has
one fewer edge than it has vertices. -/
@[toIsoGraph isTree_iff]
theorem isTree_iff_isConnected_and_E (G : CGraph) :
    G.IsTree ↔ G.IsConnected ∧ G.E + 1 = FinEnum.card G.V := by
  show G.toSimple.IsTree ↔ _
  rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, ← FinEnum.card_eq_fintypeCard']
  rfl

/-- A connected graph has at least one fewer edge than it has vertices. -/
@[toIsoGraph IsConnected.V_le_E_add_one]
theorem IsConnected.card_le_E_add_one {G : CGraph} (h : G.IsConnected) :
    FinEnum.card G.V ≤ G.E + 1 := by
  have := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one h
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    ← FinEnum.card_eq_fintypeCard'] at this

@[toIsoGraph]
theorem isConnected_strongProduct {G H : CGraph}
    (hG : G.IsConnected) (hH : H.IsConnected) : (G ⊠g H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_strongProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

@[toIsoGraph]
theorem isConnected_lexProduct {G H : CGraph}
    (hG : G.IsConnected) (hH : H.IsConnected) : (G ·g H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_lexProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

/-! ### Triangles in the strong and lexicographic products -/

@[toIsoGraph]
theorem not_isBipartite_strongProduct {G H : CGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ (G ⊠g H).IsBipartite := by
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := exists_adj_of_E_pos hH
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

@[toIsoGraph]
theorem not_isBipartite_lexProduct {G H : CGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ (G ·g H).IsBipartite := by
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := exists_adj_of_E_pos hH
  have hba : G.Adj b a := by rwa [G.symm]
  refine not_isBipartite_of_triangle (a := (a, c)) (b := (a, d)) (d := (b, c)) ?_ ?_ ?_ <;>
  · rw [lexProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    tauto

section
variable {G H : CGraph}

/-- **A diameter upper bound from a family of walks.**  If every pair of vertices is joined by a
walk of length at most `k`, the diameter is at most `k`. -/
theorem diameter_le_of_walks (G : CGraph) (k : ℕ)
    (h : ∀ u v : G.V, ∃ p : G.toSimple.Walk u v, p.length ≤ k) : G.diameter ≤ k := by
  have hup : G.toSimple.ediam ≤ (k : ℕ∞) :=
    SimpleGraph.ediam_le_of_edist_le fun u v ↦ by
      obtain ⟨p, hp⟩ := h u v
      exact le_trans p.edist_le (by exact_mod_cast hp)
  have h2 := ENat.toNat_le_toNat hup (by simp)
  simpa [diameter, SimpleGraph.diam] using h2

/-- **A diameter certificate.**  Walks of length at most `k` between all pairs, together with one
pair `a`, `b` that no shorter walk joins, pin the diameter to `k`. -/
theorem diameter_eq_of_walks (G : CGraph) (k : ℕ) {a b : G.V}
    (hle : ∀ u v : G.V, ∃ p : G.toSimple.Walk u v, p.length ≤ k)
    (hge : ∀ p : G.toSimple.Walk a b, k ≤ p.length) : G.diameter = k := by
  have hup : G.toSimple.ediam ≤ (k : ℕ∞) :=
    SimpleGraph.ediam_le_of_edist_le fun u v ↦ by
      obtain ⟨p, hp⟩ := hle u v
      exact le_trans p.edist_le (by exact_mod_cast hp)
  have hlow : (k : ℕ∞) ≤ G.toSimple.ediam :=
    le_trans (SimpleGraph.le_edist_of_forall_walk fun p ↦ by exact_mod_cast hge p)
      (SimpleGraph.edist_le_ediam (u := a) (v := b))
  rw [diameter, SimpleGraph.diam, le_antisymm hup hlow]
  rfl

/-- **A radius upper bound from a centre.**  A vertex that reaches everything in at most `k` steps
witnesses `radius ≤ k`. -/
theorem radius_le_of_walks (G : CGraph) (k : ℕ) (c : G.V)
    (h : ∀ u : G.V, ∃ p : G.toSimple.Walk c u, p.length ≤ k) : G.radius ≤ k := by
  have hup : G.toSimple.radius ≤ (k : ℕ∞) :=
    le_trans SimpleGraph.radius_le_eccent <| iSup_le fun u ↦ by
      obtain ⟨p, hp⟩ := h u
      exact le_trans p.edist_le (by exact_mod_cast hp)
  have h2 := ENat.toNat_le_toNat hup (by simp)
  simpa [radius] using h2

/-- **A radius certificate.**  A centre reaching everything in at most `k` steps, together with a
vertex at distance at least `k` from *every* vertex, pins the radius to `k`. -/
theorem radius_eq_of_walks (G : CGraph) (k : ℕ) (c : G.V)
    (hle : ∀ u : G.V, ∃ p : G.toSimple.Walk c u, p.length ≤ k)
    (hge : ∀ v : G.V, ∃ w : G.V, ∀ p : G.toSimple.Walk v w, k ≤ p.length) : G.radius = k := by
  have hup : G.toSimple.radius ≤ (k : ℕ∞) :=
    le_trans SimpleGraph.radius_le_eccent <| iSup_le fun u ↦ by
      obtain ⟨p, hp⟩ := hle u
      exact le_trans p.edist_le (by exact_mod_cast hp)
  have hlow : (k : ℕ∞) ≤ G.toSimple.radius := by
    refine le_iInf fun v ↦ ?_
    obtain ⟨w, hw⟩ := hge v
    exact le_trans (SimpleGraph.le_edist_of_forall_walk fun p ↦ by exact_mod_cast hw p)
      SimpleGraph.edist_le_eccent
  rw [radius, le_antisymm hup hlow]
  rfl

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

/-! ### The diameter of a Cartesian product -/

/-- **The diameter of a Cartesian product is the sum of the diameters.**  Both factors have to be
connected: the diameter of a disconnected graph is the junk value `0`. -/
@[toIsoGraph]
theorem diameter_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (G □g H).diameter = G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hGtop : G.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hG
  have hHtop : H.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hH
  have h : (G □g H).toSimple.ediam = G.toSimple.ediam + H.toSimple.ediam := by
    rw [toSimple_cartesianProduct]
    exact ediam_boxProd _ _
  show (G □g H).toSimple.diam = G.toSimple.diam + H.toSimple.diam
  unfold SimpleGraph.diam
  rw [h, ENat.toNat_add hGtop hHtop]

@[simp, toIsoGraph] theorem diameter_empty (n : ℕ) : (empty n).diameter = 0 := by
  show (empty n).toSimple.diam = 0
  rw [empty_toSimple]
  exact SimpleGraph.diam_bot

theorem diameter_disjUnion (G H : CGraph) (hG : 0 < FinEnum.card G.V)
    (hH : 0 < FinEnum.card H.V) : (G ⊕g H).diameter = 0 :=
  SimpleGraph.diam_eq_zero_of_not_connected (not_isConnected_disjUnion G H hG hH)

/-! ### Girth -/

/-- A product of two graphs with an edge each contains a square. -/
theorem girth_cartesianProduct_le_four {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) : (G □g H).girth ≤ 4 := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  have hbne : b ≠ b' := by rintro rfl; exact absurd hb (by simp [H.loopless])
  refine girth_le_four_of_square (a := ((a, b) : (G □g H).V)) (b := (a', b))
    (c := (a', b')) (d := (a, b')) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-! ### The girth of a disjoint union

A cycle of `G ⊕ H` never crosses between the two sides, so it is a cycle of one of them.  Proving
that means carrying a walk back along the inclusion, which `Sum` makes into a small dependent
induction: the endpoints are `inl` by hypothesis and every step keeps them there, so the walk is
the image of a walk of the factor, and being a cycle transfers because the inclusion is injective.
-/

/-- A walk of a disjoint union between two vertices of the left factor is the image of a walk of
that factor, and of the *same* walk: the inclusion carries it back exactly. -/
private theorem exists_walk_of_inl {G H : CGraph} {u v : (G ⊕g H).V}
    (w : (G ⊕g H).toSimple.Walk u v) :
    ∀ (a b : G.V) (hu : u = Sum.inl a) (hv : v = Sum.inl b),
      ∃ w' : G.toSimple.Walk a b, w'.map (disjUnionInl G H) = w.copy hu hv := by
  induction w with
  | nil =>
    rintro a b rfl hv
    cases Sum.inl_injective hv
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hadj p ih =>
    rintro a b rfl hv
    match y, hadj with
    | Sum.inl c, hadj =>
      have hac : G.toSimple.Adj a c := by simpa [CGraph.toSimple_adj] using hadj
      obtain ⟨w', hw'⟩ := ih c b rfl hv
      refine ⟨SimpleGraph.Walk.cons hac w', ?_⟩
      subst hv
      simp only [SimpleGraph.Walk.copy_rfl_rfl, SimpleGraph.Walk.map_cons]
      rw [hw']
      rfl
    | Sum.inr d, hadj => exact absurd hadj (by simp [CGraph.toSimple_adj])

/-- The mirror image of `exists_walk_of_inl` on the right factor. -/
private theorem exists_walk_of_inr {G H : CGraph} {u v : (G ⊕g H).V}
    (w : (G ⊕g H).toSimple.Walk u v) :
    ∀ (a b : H.V) (hu : u = Sum.inr a) (hv : v = Sum.inr b),
      ∃ w' : H.toSimple.Walk a b, w'.map (disjUnionInr G H) = w.copy hu hv := by
  induction w with
  | nil =>
    rintro a b rfl hv
    cases Sum.inr_injective hv
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hadj p ih =>
    rintro a b rfl hv
    match y, hadj with
    | Sum.inr c, hadj =>
      have hac : H.toSimple.Adj a c := by simpa [CGraph.toSimple_adj] using hadj
      obtain ⟨w', hw'⟩ := ih c b rfl hv
      refine ⟨SimpleGraph.Walk.cons hac w', ?_⟩
      subst hv
      simp only [SimpleGraph.Walk.copy_rfl_rfl, SimpleGraph.Walk.map_cons]
      rw [hw']
      rfl
    | Sum.inl d, hadj => exact absurd hadj (by simp [CGraph.toSimple_adj])

/-- **A cycle of a disjoint union based in the left factor is a cycle of that factor**, of the
same length. -/
theorem exists_cycle_of_inl {G H : CGraph} {a : G.V}
    {w : (G ⊕g H).toSimple.Walk (Sum.inl a) (Sum.inl a)} (hw : w.IsCycle) :
    ∃ w' : G.toSimple.Walk a a, w'.IsCycle ∧ w'.length = w.length := by
  obtain ⟨w', hw'⟩ := exists_walk_of_inl w a a rfl rfl
  rw [SimpleGraph.Walk.copy_rfl_rfl] at hw'
  refine ⟨w', ?_, ?_⟩
  · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := disjUnionInl G H) Sum.inl_injective).1 (hw' ▸ hw)
  · rw [← hw', SimpleGraph.Walk.length_map]

/-- **A cycle of a disjoint union based in the right factor is a cycle of that factor**, of the
same length. -/
theorem exists_cycle_of_inr {G H : CGraph} {b : H.V}
    {w : (G ⊕g H).toSimple.Walk (Sum.inr b) (Sum.inr b)} (hw : w.IsCycle) :
    ∃ w' : H.toSimple.Walk b b, w'.IsCycle ∧ w'.length = w.length := by
  obtain ⟨w', hw'⟩ := exists_walk_of_inr w b b rfl rfl
  rw [SimpleGraph.Walk.copy_rfl_rfl] at hw'
  refine ⟨w', ?_, ?_⟩
  · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := disjUnionInr G H) Sum.inr_injective).1 (hw' ▸ hw)
  · rw [← hw', SimpleGraph.Walk.length_map]

/-- **A disjoint union is acyclic exactly when both sides are.** -/
@[toIsoGraph simp]
theorem isAcyclic_disjUnion : (G ⊕g H).IsAcyclic ↔ G.IsAcyclic ∧ H.IsAcyclic := by
  constructor
  · intro h
    exact ⟨fun a w hw ↦ h _ (hw.map (f := disjUnionInl G H) Sum.inl_injective),
      fun b w hw ↦ h _ (hw.map (f := disjUnionInr G H) Sum.inr_injective)⟩
  · rintro ⟨hG, hH⟩ u w hw
    match u with
    | Sum.inl a => obtain ⟨w', hw', -⟩ := exists_cycle_of_inl hw; exact hG _ hw'
    | Sum.inr b => obtain ⟨w', hw', -⟩ := exists_cycle_of_inr hw; exact hH _ hw'

private theorem girth_disjUnion_le_left {G : CGraph} (H : CGraph) (hG : ¬ G.IsAcyclic) :
    (G ⊕g H).girth ≤ G.girth := by
  obtain ⟨a, w, hw, hlen⟩ := SimpleGraph.exists_girth_eq_length.2 hG
  have h := SimpleGraph.girth_le_length (hw.map (f := disjUnionInl G H) Sum.inl_injective)
  rw [SimpleGraph.Walk.length_map] at h
  show (G ⊕g H).toSimple.girth ≤ G.toSimple.girth
  rw [hlen]
  exact h

private theorem girth_disjUnion_le_right {H : CGraph} (G : CGraph) (hH : ¬ H.IsAcyclic) :
    (G ⊕g H).girth ≤ H.girth := by
  obtain ⟨b, w, hw, hlen⟩ := SimpleGraph.exists_girth_eq_length.2 hH
  have h := SimpleGraph.girth_le_length (hw.map (f := disjUnionInr G H) Sum.inr_injective)
  rw [SimpleGraph.Walk.length_map] at h
  show (G ⊕g H).toSimple.girth ≤ H.toSimple.girth
  rw [hlen]
  exact h

/-- A shortest cycle of a disjoint union is a shortest cycle of the side it lives on. -/
private theorem exists_side_girth {G H : CGraph} (h : ¬ (G ⊕g H).IsAcyclic) :
    (¬ G.IsAcyclic ∧ G.girth ≤ (G ⊕g H).girth) ∨
      (¬ H.IsAcyclic ∧ H.girth ≤ (G ⊕g H).girth) := by
  obtain ⟨u, w, hw, hlen⟩ := SimpleGraph.exists_girth_eq_length.2 h
  match u with
  | Sum.inl a =>
    obtain ⟨w', hw', hl⟩ := exists_cycle_of_inl hw
    refine Or.inl ⟨fun hac ↦ hac _ hw', ?_⟩
    show G.toSimple.girth ≤ (G ⊕g H).toSimple.girth
    rw [hlen, ← hl]
    exact SimpleGraph.girth_le_length hw'
  | Sum.inr b =>
    obtain ⟨w', hw', hl⟩ := exists_cycle_of_inr hw
    refine Or.inr ⟨fun hac ↦ hac _ hw', ?_⟩
    show H.toSimple.girth ≤ (G ⊕g H).toSimple.girth
    rw [hlen, ← hl]
    exact SimpleGraph.girth_le_length hw'

/-- **The girth of a disjoint union.**  A cycle lives on one side, so the shortest cycle is the
shorter of the two sides' shortest — except that the `0`-for-acyclic convention means an acyclic
side has to be skipped rather than minimised over, which is what the two `if`s do. -/
@[toIsoGraph]
theorem girth_disjUnion :
    (G ⊕g H).girth =
      if G.girth = 0 then H.girth else if H.girth = 0 then G.girth else min G.girth H.girth := by
  by_cases hG : G.IsAcyclic <;> by_cases hH : H.IsAcyclic
  · rw [if_pos (girth_eq_zero_iff.2 hG), girth_eq_zero_iff.2 hH]
    exact girth_eq_zero_iff.2 (isAcyclic_disjUnion.2 ⟨hG, hH⟩)
  · have hne : ¬ (G ⊕g H).IsAcyclic := fun h ↦ hH (isAcyclic_disjUnion.1 h).2
    rw [if_pos (girth_eq_zero_iff.2 hG)]
    refine le_antisymm (girth_disjUnion_le_right G hH) ?_
    rcases exists_side_girth hne with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd hG h
    · exact h
  · have hne : ¬ (G ⊕g H).IsAcyclic := fun h ↦ hG (isAcyclic_disjUnion.1 h).1
    rw [if_neg (girth_eq_zero_iff.not.2 hG), if_pos (girth_eq_zero_iff.2 hH)]
    refine le_antisymm (girth_disjUnion_le_left H hG) ?_
    rcases exists_side_girth hne with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hH h
  · rw [if_neg (girth_eq_zero_iff.not.2 hG), if_neg (girth_eq_zero_iff.not.2 hH)]
    have hne : ¬ (G ⊕g H).IsAcyclic := fun h ↦ hG (isAcyclic_disjUnion.1 h).1
    refine le_antisymm (le_min (girth_disjUnion_le_left H hG)
      (girth_disjUnion_le_right G hH)) ?_
    rcases exists_side_girth hne with ⟨-, h⟩ | ⟨-, h⟩
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) h

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

/-- **A graph whose girth is not three has no triangle**, so its cliques are its edges. -/
@[toIsoGraph]
theorem cliqueNum_le_two_of_girth_ne_three {G : CGraph} (h : G.girth ≠ 3) : G.cliqueNum ≤ 2 := by
  by_contra hc
  exact h (girth_eq_three_of_cliqueNum (by omega))

/-- **A triangle-free graph with a cycle has girth at least four**, stated through the clique
number. -/
@[toIsoGraph]
theorem four_le_girth_of_cliqueNum {G : CGraph} (hcl : G.cliqueNum ≤ 2) (hnac : ¬ G.IsAcyclic) :
    4 ≤ G.girth := by
  have h3 := three_le_girth hnac
  have : G.girth ≠ 3 := fun h ↦ by have := girth_eq_three_iff.1 h; omega
  omega

/-! ### Two graphs of girth five -/

/-- **The five-cycle has girth five.** -/
@[toIsoGraph]
theorem girth_cycle_five : (cycle 5).girth = 5 := by
  refine le_antisymm ?_ (five_le_girth (by decide) (by decide) (not_isAcyclic_cycle 2))
  exact girth_le_five_of_pentagon (a := (0 : Fin 5)) (b := (1 : Fin 5)) (c := (2 : Fin 5))
    (d := (3 : Fin 5)) (e := (4 : Fin 5))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))

/-! ### The radius -/

/-- The most central vertex is no further from the rest than the least central one. -/
@[toIsoGraph]
theorem radius_le_diameter (G : CGraph) : G.radius ≤ G.diameter := by
  by_cases hc : G.toSimple.Connected
  · haveI : Nonempty G.V := hc.nonempty
    have hd : G.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hc
    exact ENat.toNat_le_toNat SimpleGraph.radius_le_ediam hd
  · have h : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_not_connected hc
    simp [radius, h]

/-- Walking through a central vertex crosses the graph in at most `2r` steps. -/
@[toIsoGraph]
theorem diameter_le_two_mul_radius (G : CGraph) : G.diameter ≤ 2 * G.radius := by
  by_cases hc : G.toSimple.Connected
  · haveI : Nonempty G.V := hc.nonempty
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 (SimpleGraph.radius_ne_top_iff.2 hc)
    have h := SimpleGraph.ediam_le_two_mul_radius (G := G.toSimple)
    rw [← hr] at h
    have h2 : G.toSimple.ediam ≤ ((2 * r : ℕ) : ℕ∞) := by
      rwa [Nat.cast_mul, Nat.cast_ofNat]
    have h3 := ENat.toNat_le_toNat h2 (ENat.coe_ne_top _)
    simpa [radius, ← hr] using h3
  · have h : G.toSimple.diam = 0 := SimpleGraph.diam_eq_zero_of_not_connected hc
    simp [diameter, h]

@[toIsoGraph]
theorem radius_pos (G : CGraph) (hc : G.IsConnected) (hV : 1 < FinEnum.card G.V) :
    0 < G.radius := by
  haveI : Nonempty G.V := hc.nonempty
  haveI : Nontrivial G.V :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rwa [← FinEnum.card_eq_fintypeCard'])
  have h0 : G.toSimple.radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
  have ht : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hc
  have : G.radius ≠ 0 := by
    simp only [radius, ne_eq, ENat.toNat_eq_zero]
    tauto
  omega

/-- A vertex adjacent to everything else is at distance one from the rest, so it makes the
radius `1` — provided there is something else. -/
theorem radius_eq_one_of_universal {v : G.V} (h : ∀ u, u ≠ v → G.Adj v u)
    (hV : 1 < FinEnum.card G.V) : G.radius = 1 := by
  haveI : Nontrivial G.V :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rwa [← FinEnum.card_eq_fintypeCard'])
  have hle : G.toSimple.eccent v ≤ 1 :=
    (SimpleGraph.eccent_le_one_iff v).2 fun u hu ↦ (toSimple_adj _ _ _).2 (h u (Ne.symm hu))
  have h1 : G.toSimple.radius ≤ 1 := le_trans SimpleGraph.radius_le_eccent hle
  have h0 : G.toSimple.radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
  have : G.toSimple.radius = 1 := le_antisymm h1 (ENat.one_le_iff_ne_zero.2 h0)
  simp [radius, this]

/-- Conversely, radius `1` produces a vertex adjacent to everything else. -/
theorem exists_universal_of_radius_eq_one (G : CGraph) (h : G.radius = 1) :
    ∃ v : G.V, ∀ u, u ≠ v → G.Adj v u := by
  have hne : G.toSimple.radius ≠ ⊤ := by
    intro htop
    rw [radius, htop] at h
    simp at h
  haveI : Nonempty G.V := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hne SimpleGraph.radius_eq_top_of_isEmpty
  obtain ⟨v, hv⟩ := SimpleGraph.exists_eccent_eq_radius (G := G.toSimple)
  refine ⟨v, fun u hu ↦ ?_⟩
  have h1 : G.toSimple.radius = 1 := by
    rw [radius] at h
    rcases ENat.ne_top_iff_exists.1 hne with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [ENat.toNat_coe] at h
    rw [h]
    rfl
  have : G.toSimple.eccent v ≤ 1 := by rw [hv, h1]
  exact (toSimple_adj _ _ _).1 ((SimpleGraph.eccent_le_one_iff v).1 this u (Ne.symm hu))

/-! ### Counting connected components -/

@[toIsoGraph]
theorem numComponents_eq_zero_iff (G : CGraph) :
    G.numComponents = 0 ↔ FinEnum.card G.V = 0 := by
  rw [numComponents, Nat.card_eq_zero, FinEnum.card_eq_zero_iff]
  simp only [or_iff_left (not_infinite_iff_finite.2 inferInstance)]
  exact ⟨fun h ↦ ⟨fun v ↦ h.false (G.toSimple.connectedComponentMk v)⟩, fun _ ↦ inferInstance⟩

@[toIsoGraph]
theorem numComponents_pos_iff (G : CGraph) : 0 < G.numComponents ↔ 0 < FinEnum.card G.V := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, ne_eq, ne_eq, numComponents_eq_zero_iff]

/-- A graph is connected exactly when it has one component. -/
@[toIsoGraph]
theorem numComponents_eq_one_iff (G : CGraph) : G.numComponents = 1 ↔ G.IsConnected := by
  rw [numComponents, Nat.card_eq_one_iff_unique, IsConnected, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hsub, hne⟩
    refine ⟨fun u v ↦ SimpleGraph.ConnectedComponent.exact (hsub.elim _ _), ?_⟩
    obtain ⟨c⟩ := hne
    exact SimpleGraph.ConnectedComponent.ind (β := fun _ ↦ Nonempty G.V) (fun v ↦ ⟨v⟩) c
  · rintro ⟨hpre, hne⟩
    exact ⟨hpre.subsingleton_connectedComponent, inferInstance⟩

/-- A connected graph has a vertex, there being a component for it to be. -/
@[toIsoGraph IsConnected.V_pos]
theorem IsConnected.card_pos {G : CGraph} (h : G.IsConnected) : 0 < FinEnum.card G.V :=
  (numComponents_pos_iff G).1 (by rw [(numComponents_eq_one_iff G).2 h]; omega)

/-- Each component contains at least one vertex. -/
@[toIsoGraph numComponents_le_V]
theorem numComponents_le_card (G : CGraph) : G.numComponents ≤ FinEnum.card G.V := by
  rw [numComponents, FinEnum.card_eq_fintypeCard', ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ (Quot.mk_surjective)

@[simp, toIsoGraph] theorem numComponents_empty (n : ℕ) : (empty n).numComponents = n := by
  rw [numComponents, empty_toSimple]
  have : Function.Bijective ((⊥ : SimpleGraph (Fin n)).connectedComponentMk) := by
    refine ⟨fun u v h ↦ ?_, Quot.mk_surjective⟩
    exact SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.exact h)
  rw [← Nat.card_eq_of_bijective _ this, Nat.card_eq_fintype_card, Fintype.card_fin]

@[simp, toIsoGraph] theorem numComponents_complete (n : ℕ) : (complete (n + 1)).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_complete n)

/-! ### Components of a Cartesian product -/

/-- Reachability in a box product is reachability in both factors, so the components of a box
product are the pairs of components. -/
private theorem card_connectedComponent_boxProd {α β : Type*} (S : SimpleGraph α)
    (T : SimpleGraph β) :
    Nat.card (S.boxProd T).ConnectedComponent
      = Nat.card S.ConnectedComponent * Nat.card T.ConnectedComponent := by
  set φ : (S.boxProd T).ConnectedComponent → S.ConnectedComponent × T.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift
      (fun p ↦ (S.connectedComponentMk p.1, T.connectedComponentMk p.2))
      (fun p q w _ ↦ by
        obtain ⟨h1, h2⟩ := SimpleGraph.reachable_boxProd.1 ⟨w⟩
        exact Prod.ext (SimpleGraph.ConnectedComponent.sound h1)
          (SimpleGraph.ConnectedComponent.sound h2)) with hφ
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y
      induction x using SimpleGraph.ConnectedComponent.ind with | _ p =>
      induction y using SimpleGraph.ConnectedComponent.ind with | _ q =>
      intro h
      have h1 : S.connectedComponentMk p.1 = S.connectedComponentMk q.1 := congrArg Prod.fst h
      have h2 : T.connectedComponentMk p.2 = T.connectedComponentMk q.2 := congrArg Prod.snd h
      exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.reachable_boxProd.2
        ⟨SimpleGraph.ConnectedComponent.exact h1, SimpleGraph.ConnectedComponent.exact h2⟩)
    · rintro ⟨c, d⟩
      obtain ⟨a, rfl⟩ := Quot.exists_rep c
      obtain ⟨b, rfl⟩ := Quot.exists_rep d
      exact ⟨(S.boxProd T).connectedComponentMk (a, b), rfl⟩
  rw [Nat.card_eq_of_bijective φ hbij, Nat.card_prod]

/-- **The components of a Cartesian product are the pairs of components.** -/
theorem numComponents_cartesianProduct (G H : CGraph) :
    (G □g H).numComponents = G.numComponents * H.numComponents := by
  rw [numComponents, numComponents, numComponents, toSimple_cartesianProduct]
  exact card_connectedComponent_boxProd _ _

/-! ### A minimum-degree condition for connectedness -/

/-- **A graph with `2δ(G) + 1 ≥ |V|` is connected**: two nonadjacent vertices have too many
neighbours between them to avoid sharing one. -/
@[toIsoGraph isConnected_of_V_le_two_mul_minDeg]
theorem isConnected_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : FinEnum.card G.V ≤ 2 * G.minDeg + 1) : G.IsConnected := by
  classical
  rw [IsConnected, SimpleGraph.connected_iff]
  refine ⟨fun u v ↦ ?_, inferInstance⟩
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.refl u
  by_cases hadj : G.toSimple.Adj u v
  · exact hadj.reachable
  -- neither neighbourhood contains `u` or `v`
  set T : Finset G.V := (Finset.univ.erase u).erase v with hT
  have hu : G.toSimple.neighborFinset u ⊆ T := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact Finset.mem_erase.2 ⟨fun hwv ↦ hadj (hwv ▸ hw),
      Finset.mem_erase.2 ⟨fun hwu ↦ (hwu ▸ hw).ne rfl, Finset.mem_univ w⟩⟩
  have hv : G.toSimple.neighborFinset v ⊆ T := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact Finset.mem_erase.2 ⟨fun hwv ↦ (hwv ▸ hw).ne rfl,
      Finset.mem_erase.2 ⟨fun hwu ↦ hadj (hwu ▸ hw).symm, Finset.mem_univ w⟩⟩
  have hTcard : T.card = FinEnum.card G.V - 2 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨fun h' ↦ huv h'.symm, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), FinEnum.card_univ]
    omega
  have hdu : G.minDeg ≤ (G.toSimple.neighborFinset u).card := G.minDeg_le_degree u
  have hdv : G.minDeg ≤ (G.toSimple.neighborFinset v).card := G.minDeg_le_degree v
  have hunion : (G.toSimple.neighborFinset u ∪ G.toSimple.neighborFinset v).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset hu hv)
  have hinter := Finset.card_union_add_card_inter
    (G.toSimple.neighborFinset u) (G.toSimple.neighborFinset v)
  have hcard2 : 2 ≤ FinEnum.card G.V := by
    have hle : ({u, v} : Finset G.V).card ≤ FinEnum.card G.V := by
      rw [← FinEnum.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rwa [Finset.card_pair huv] at hle
  have hpos : 0 < (G.toSimple.neighborFinset u ∩ G.toSimple.neighborFinset v).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
  exact hw.1.reachable.trans hw.2.reachable.symm

theorem numComponents_eq_one_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : FinEnum.card G.V ≤ 2 * G.minDeg + 1) : G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 (G.isConnected_of_card_le_two_mul_minDeg h)

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

/-! ### The radius of a cartesian product -/

/-- **The radius of a cartesian product is the sum of the radii.**  Both factors have to be
connected: the radius of a disconnected graph is the junk value `0`. -/
@[toIsoGraph]
theorem radius_cartesianProduct (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (G □g H).radius = G.radius + H.radius := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hGtop : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hG
  have hHtop : H.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hH
  have h : (G □g H).toSimple.radius = G.toSimple.radius + H.toSimple.radius := by
    rw [toSimple_cartesianProduct]
    exact radius_boxProd _ _
  show (G □g H).toSimple.radius.toNat = _
  rw [h, ENat.toNat_add hGtop hHtop]
  rfl

/-! ### The strong product carries the `ℓ∞` product metric -/

theorem strongProduct_toSimple_adj (G H : CGraph) (p q : (G ⊠g H).V) :
    (G ⊠g H).toSimple.Adj p q ↔
      p ≠ q ∧ ((p.1 = q.1 ∨ G.toSimple.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.toSimple.Adj p.2 q.2)) := by
  simp [CGraph.toSimple_adj]

theorem edist_fst_le_length {p q : (G ⊠g H).V} (W : (G ⊠g H).toSimple.Walk p q) :
    G.toSimple.edist p.1 q.1 ≤ W.length := by
  induction W with
  | nil => simp
  | @cons a b c hab rest ih =>
    rw [SimpleGraph.Walk.length_cons]
    rcases ((strongProduct_toSimple_adj G H a b).1 hab).2.1 with heq | hadj
    · rw [heq]
      exact le_trans ih (by exact_mod_cast Nat.le_add_right rest.length 1)
    · calc G.toSimple.edist a.1 c.1
          ≤ G.toSimple.edist a.1 b.1 + G.toSimple.edist b.1 c.1 := SimpleGraph.edist_triangle
        _ ≤ 1 + (rest.length : ℕ∞) := add_le_add (le_trans (SimpleGraph.Walk.edist_le
              (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)) (by simp)) ih
        _ = ((rest.length + 1 : ℕ) : ℕ∞) := by push_cast; ring

theorem edist_snd_le_length {p q : (G ⊠g H).V} (W : (G ⊠g H).toSimple.Walk p q) :
    H.toSimple.edist p.2 q.2 ≤ W.length := by
  induction W with
  | nil => simp
  | @cons a b c hab rest ih =>
    rw [SimpleGraph.Walk.length_cons]
    rcases ((strongProduct_toSimple_adj G H a b).1 hab).2.2 with heq | hadj
    · rw [heq]
      exact le_trans ih (by exact_mod_cast Nat.le_add_right rest.length 1)
    · calc H.toSimple.edist a.2 c.2
          ≤ H.toSimple.edist a.2 b.2 + H.toSimple.edist b.2 c.2 := SimpleGraph.edist_triangle
        _ ≤ 1 + (rest.length : ℕ∞) := add_le_add (le_trans (SimpleGraph.Walk.edist_le
              (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)) (by simp)) ih
        _ = ((rest.length + 1 : ℕ) : ℕ∞) := by push_cast; ring

private theorem exists_walk_strongProduct_aux (G H : CGraph) : ∀ (n : ℕ) {g₁ g₂ : G.V}
    {h₁ h₂ : H.V} (WG : G.toSimple.Walk g₁ g₂) (WH : H.toSimple.Walk h₁ h₂),
    WG.length + WH.length ≤ n →
    ∃ W : (G ⊠g H).toSimple.Walk (g₁, h₁) (g₂, h₂), W.length ≤ max WG.length WH.length := by
  let toSPG (h₀ : H.V) : G.toSimple →g (G ⊠g H).toSimple :=
    { toFun := fun g ↦ (g, h₀)
      map_rel' := @fun a b hab ↦ (strongProduct_toSimple_adj G H (a, h₀) (b, h₀)).2
        ⟨fun h ↦ hab.ne (congrArg Prod.fst h), Or.inr hab, Or.inl rfl⟩ }
  let toSPH (g₀ : G.V) : H.toSimple →g (G ⊠g H).toSimple :=
    { toFun := fun h ↦ (g₀, h)
      map_rel' := @fun a b hab ↦ (strongProduct_toSimple_adj G H (g₀, a) (g₀, b)).2
        ⟨fun h ↦ hab.ne (congrArg Prod.snd h), Or.inl rfl, Or.inr hab⟩ }
  intro n
  induction n with
  | zero =>
    intro g₁ g₂ h₁ h₂ WG WH hle
    obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (p := WG) (by omega)
    obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (p := WH) (by omega)
    exact ⟨.nil, by simp⟩
  | succ m ih =>
    intro g₁ g₂ h₁ h₂ WG WH hle
    by_cases hg : WG.length = 0
    · obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (p := WG) hg
      exact ⟨WH.map (toSPH g₁), by simp [hg]⟩
    · by_cases hh : WH.length = 0
      · obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero (p := WH) hh
        exact ⟨WG.map (toSPG h₁), by simp [hh]⟩
      · cases WG with
        | nil => exact absurd rfl hg
        | cons hab WGtail =>
          cases WH with
          | nil => exact absurd rfl hh
          | cons hcd WHtail =>
            obtain ⟨W, hW⟩ := ih WGtail WHtail (by
              simp only [SimpleGraph.Walk.length_cons] at hle ⊢; omega)
            refine ⟨SimpleGraph.Walk.cons ((strongProduct_toSimple_adj G H _ _).2
              ⟨by rintro ⟨rfl, rfl⟩; exact hab.ne rfl, Or.inr hab, Or.inr hcd⟩) W, ?_⟩
            simp only [SimpleGraph.Walk.length_cons] at hW ⊢
            omega

/-- **Walks in a strong product move in both coordinates at once.**  Two walks, one in each
factor, combine into a single walk in the strong product whose length is the *maximum* of the
two: the shorter one waits in place while the longer one catches up. -/
theorem exists_walk_strongProduct {g₁ g₂ : G.V} {h₁ h₂ : H.V} (WG : G.toSimple.Walk g₁ g₂)
    (WH : H.toSimple.Walk h₁ h₂) :
    ∃ W : (G ⊠g H).toSimple.Walk (g₁, h₁) (g₂, h₂), W.length ≤ max WG.length WH.length :=
  exists_walk_strongProduct_aux G H _ WG WH le_rfl

/-- **The strong product carries the `ℓ∞` product metric.** -/
theorem edist_strongProduct (G H : CGraph) (p q : (G ⊠g H).V) :
    (G ⊠g H).toSimple.edist p q =
      max (G.toSimple.edist p.1 q.1) (H.toSimple.edist p.2 q.2) := by
  refine le_antisymm ?_ (SimpleGraph.le_edist_of_forall_walk fun W ↦
    max_le (edist_fst_le_length W) (edist_snd_le_length W))
  by_cases hg : G.toSimple.edist p.1 q.1 = ⊤
  · simp [hg]
  by_cases hh : H.toSimple.edist p.2 q.2 = ⊤
  · simp [hh]
  obtain ⟨WG, hWG⟩ := SimpleGraph.exists_walk_of_edist_ne_top hg
  obtain ⟨WH, hWH⟩ := SimpleGraph.exists_walk_of_edist_ne_top hh
  obtain ⟨W, hW⟩ := exists_walk_strongProduct WG WH
  calc (G ⊠g H).toSimple.edist p q ≤ (W.length : ℕ∞) := SimpleGraph.Walk.edist_le W
    _ ≤ ((max WG.length WH.length : ℕ) : ℕ∞) := by exact_mod_cast hW
    _ = max (WG.length : ℕ∞) (WH.length : ℕ∞) := by
        rcases le_total WG.length WH.length with h | h <;> simp [h, Nat.cast_le.2 h]
    _ ≤ max (G.toSimple.edist p.1 q.1) (H.toSimple.edist p.2 q.2) := max_le_max hWG.le hWH.le

/-- The eccentricity of a vertex of a strong product is the larger of the two coordinate
eccentricities. -/
theorem eccent_strongProduct (G H : CGraph) (p : (G ⊠g H).V) :
    (G ⊠g H).toSimple.eccent p =
      max (G.toSimple.eccent p.1) (H.toSimple.eccent p.2) := by
  simp only [SimpleGraph.eccent, edist_strongProduct]
  refine le_antisymm (iSup_le fun v ↦ max_le_max (le_iSup _ v.1) (le_iSup _ v.2)) (max_le ?_ ?_)
  · exact iSup_le fun a ↦ le_trans (le_max_left _ (H.toSimple.edist p.2 p.2))
      (le_iSup (fun v : (G ⊠g H).V ↦
        max (G.toSimple.edist p.1 v.1) (H.toSimple.edist p.2 v.2)) (a, p.2))
  · exact iSup_le fun b ↦ le_trans (le_max_right (G.toSimple.edist p.1 p.1) _)
      (le_iSup (fun v : (G ⊠g H).V ↦
        max (G.toSimple.edist p.1 v.1) (H.toSimple.edist p.2 v.2)) (p.1, b))

/-- The extended diameter of a strong product is the larger of the two diameters. -/
theorem ediam_strongProduct (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    (G ⊠g H).toSimple.ediam = max G.toSimple.ediam H.toSimple.ediam := by
  simp only [SimpleGraph.ediam, eccent_strongProduct]
  refine le_antisymm (iSup_le fun v ↦ max_le_max (le_iSup _ v.1) (le_iSup _ v.2)) (max_le ?_ ?_)
  · exact iSup_le fun a ↦ le_trans (le_max_left _ (H.toSimple.eccent (Classical.arbitrary H.V)))
      (le_iSup (fun v : (G ⊠g H).V ↦ max (G.toSimple.eccent v.1) (H.toSimple.eccent v.2))
        (a, Classical.arbitrary H.V))
  · exact iSup_le fun b ↦ le_trans (le_max_right (G.toSimple.eccent (Classical.arbitrary G.V)) _)
      (le_iSup (fun v : (G ⊠g H).V ↦ max (G.toSimple.eccent v.1) (H.toSimple.eccent v.2))
        (Classical.arbitrary G.V, b))

/-- The radius of a strong product is the larger of the two radii. -/
theorem radius_strongProduct_enat (G H : CGraph) :
    (G ⊠g H).toSimple.radius = max G.toSimple.radius H.toSimple.radius := by
  rcases isEmpty_or_nonempty G.V with hG | hG
  · haveI := hG
    haveI : IsEmpty (G ⊠g H).V := ⟨fun p ↦ hG.elim p.1⟩
    rw [SimpleGraph.radius_eq_top_of_isEmpty,
      SimpleGraph.radius_eq_top_of_isEmpty (G := G.toSimple)]
    simp
  rcases isEmpty_or_nonempty H.V with hH | hH
  · haveI := hH
    haveI : IsEmpty (G ⊠g H).V := ⟨fun p ↦ hH.elim p.2⟩
    rw [SimpleGraph.radius_eq_top_of_isEmpty,
      SimpleGraph.radius_eq_top_of_isEmpty (G := H.toSimple)]
    simp
  simp only [SimpleGraph.radius, eccent_strongProduct]
  refine le_antisymm ?_ (le_iInf fun u ↦ max_le_max (iInf_le _ u.1) (iInf_le _ u.2))
  obtain ⟨a, ha⟩ := ENat.exists_eq_iInf G.toSimple.eccent
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf H.toSimple.eccent
  exact le_trans (iInf_le (fun v : (G ⊠g H).V ↦
    max (G.toSimple.eccent v.1) (H.toSimple.eccent v.2)) (a, b)) (le_of_eq (by rw [ha, hb]))

/-- Adding edges cannot increase the diameter: the strong product is at most as wide as the
cartesian product living inside it. -/
@[toIsoGraph]
theorem diameter_strongProduct_le (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (G ⊠g H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (G □g H).IsConnected := (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (G □g H).V := hcp.nonempty
  have hne : (G □g H).toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_strongProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-- The same bound for the lexicographic product. -/
@[toIsoGraph]
theorem diameter_lexProduct_le (G H : CGraph)
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (G ·g H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (G □g H).IsConnected := (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (G □g H).V := hcp.nonempty
  have hne : (G □g H).toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_lexProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-! ## The girth of a cycle

`Cₙ` has girth `n`.  The upper bound is the general fact that a cycle uses no more vertices than
the graph has.  For the lower bound, a shorter cycle would miss some vertex `x`; rotating the
labels so that `x` becomes `n - 1` carries the missed cycle into `path n`, which is acyclic. -/

/-- **A graph with a cycle has girth at most its order**: the support of a cycle, minus its
repeated endpoint, is a list of distinct vertices as long as the cycle. -/
theorem girth_le_V {G : CGraph} (h : ¬ G.IsAcyclic) : G.girth ≤ FinEnum.card G.V := by
  simp only [IsAcyclic, SimpleGraph.IsAcyclic, not_forall, not_not] at h
  obtain ⟨v, c, hc⟩ := h
  refine le_trans (girth_le_length hc) ?_
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  calc c.length = c.support.tail.length := hlen.symm
    _ ≤ FinEnum.card G.V := by
        rw [FinEnum.card_eq_fintypeCard']; exact hc.support_nodup.length_le_card

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

/-- **Girth is monotone along an injective homomorphism.**  A cycle of `G` maps to a cycle of `H`,
so `H` has girth at most the order of `G` as soon as `G` has a cycle at all. -/
theorem girth_le_card_of_map {G H : CGraph} (f : G.V → H.V) (hinj : Function.Injective f)
    (hadj : ∀ x y, G.Adj x y = true → H.Adj (f x) (f y) = true) (hnac : ¬ G.IsAcyclic) :
    H.girth ≤ FinEnum.card G.V := by
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

end

end CGraph

namespace IsoGraph

/-! ### Bipartiteness

A proper two-colouring is exactly what makes the bipartite double cover of the next section
split, so the two belong together: the colourings are built here and cashed in there. -/

@[simp] theorem isBipartite_disjUnion {G H : IsoGraph} (hG : IsBipartite G) (hH : IsBipartite H) :
    IsBipartite (G ⊕g H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  exact CGraph.IsBipartite.disjUnion hG hH

@[simp] theorem isBipartite_cartesianProduct {G H : IsoGraph} (hG : IsBipartite G) (hH : IsBipartite H) :
    IsBipartite (G □g H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk]
  exact CGraph.IsBipartite.cartesianProduct hG hH

/-- A disjoint union is bipartite exactly when both summands are. -/
@[simp] theorem isBipartite_disjUnion_iff {G H : IsoGraph} :
    IsBipartite (G ⊕g H) ↔ IsBipartite G ∧ IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [disjUnion_mk, isBipartite_mk, isBipartite_mk, isBipartite_mk]
  exact ⟨fun h ↦ ⟨h.of_disjUnion_left, h.of_disjUnion_right⟩,
    fun h ↦ CGraph.IsBipartite.disjUnion h.1 h.2⟩

@[simp] theorem isBipartite_empty (n : ℕ) : IsBipartite (empty n) := by
  rw [empty_def, isBipartite_mk]
  exact ⟨fun _ ↦ false, by simp⟩

theorem not_isBipartite_complete_three : ¬ IsBipartite (complete 3) := not_isBipartite_complete 0

theorem not_isBipartite_cycle_three : ¬ IsBipartite (cycle 3) := not_isBipartite_cycle_odd 0

theorem not_isBipartite_cycle_five : ¬ IsBipartite (cycle 5) := not_isBipartite_cycle_odd 1

theorem not_isBipartite_join_left {G H : IsoGraph} (hG : ¬ IsBipartite G) :
    ¬ IsBipartite (G ∇g H) := fun h ↦ hG h.of_join_left

theorem not_isBipartite_join_right {G H : IsoGraph} (hH : ¬ IsBipartite H) :
    ¬ IsBipartite (G ∇g H) := fun h ↦ hH h.of_join_right

/-! ### Connectivity -/

@[simp] theorem isConnected_empty_one : IsConnected (empty 1) := CGraph.isConnected_empty_one

@[simp] theorem isConnected_complete (n : ℕ) : IsConnected (complete (n + 1)) :=
  CGraph.isConnected_complete n

@[simp] theorem isConnected_path (n : ℕ) : IsConnected (path (n + 1)) := CGraph.isConnected_path n

@[simp] theorem isConnected_cycle (n : ℕ) : IsConnected (cycle (n + 1)) :=
  CGraph.isConnected_cycle n

@[simp] theorem isAcyclic_empty (n : ℕ) : IsAcyclic (empty n) := CGraph.isAcyclic_empty n

@[simp] theorem isAcyclic_path (n : ℕ) : IsAcyclic (path n) := CGraph.isAcyclic_path n

@[simp] theorem isTree_path (n : ℕ) : IsTree (path (n + 1)) := CGraph.isTree_path n

@[simp] theorem not_isAcyclic_cycle (n : ℕ) : ¬ IsAcyclic (cycle (n + 3)) :=
  CGraph.not_isAcyclic_cycle n

/-- A join of two nonempty graphs is connected, whatever the two graphs are. -/
@[simp] theorem isConnected_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (G ∇g H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, isConnected_mk]
  rw [V_mk] at hG hH
  exact CGraph.isConnected_join _ _ hG hH

/-- The Cartesian product is connected exactly when both factors are. -/
@[simp] theorem isConnected_cartesianProduct {G H : IsoGraph} :
    IsConnected (G □g H) ↔ IsConnected G ∧ IsConnected H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, isConnected_mk,
    isConnected_mk, isConnected_mk]
  exact CGraph.isConnected_cartesianProduct_iff _ _

@[simp] theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 :=
  CGraph.diameter_complete n

@[simp] theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := CGraph.diameter_path n

@[simp] theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 :=
  CGraph.diameter_cycle n

/-! ### The diameter of a Cartesian product -/

@[simp] theorem diameter_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ⊕g H).diameter = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, diameter_mk]
  rw [V_mk] at hG hH
  exact CGraph.diameter_disjUnion _ _ hG hH

/-- The `m × n` torus, a Cartesian product of two cycles. -/
theorem diameter_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 1) □g cycle (n + 1)).diameter = (m + 1) / 2 + (n + 1) / 2 := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_cycle n), diameter_cycle m,
    diameter_cycle n]

theorem ne_of_diameter_ne {G H : IsoGraph} (h : G.diameter ≠ H.diameter) : G ≠ H :=
  ne_of_apply_ne diameter h

theorem ne_of_isConnected {G H : IsoGraph} (hG : IsConnected G) (hH : ¬ IsConnected H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isAcyclic {G H : IsoGraph} (hG : IsAcyclic G) (hH : ¬ IsAcyclic H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isTree {G H : IsoGraph} (hG : IsTree G) (hH : ¬ IsTree H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isBipartite {G H : IsoGraph} (hG : IsBipartite G) (hH : ¬ IsBipartite H) : G ≠ H :=
  ne_of_pred hG hH

/-! ### Girth -/

theorem ne_of_girth_ne {G H : IsoGraph} (h : G.girth ≠ H.girth) : G ≠ H := fun hgh ↦ h (hgh ▸ rfl)

/-! ### Girth of the named graphs -/

@[simp] theorem girth_empty (n : ℕ) : (empty n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_empty n)

@[simp] theorem girth_path (n : ℕ) : (path n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_path n)

/-! ### Counting connected components -/

theorem numComponents_eq_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) :
    G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 h

/-! ### The component-count table -/

@[simp] theorem numComponents_path (n : ℕ) : (path (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_path n)

@[simp] theorem numComponents_cycle (n : ℕ) : (cycle (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_cycle n)

/-! ### Components of a Cartesian product -/

/-- **The components of a Cartesian product are the pairs of components.** -/
@[simp] theorem numComponents_cartesianProduct (G H : IsoGraph) :
    (G □g H).numComponents = G.numComponents * H.numComponents := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, numComponents_mk,
    numComponents_mk, numComponents_mk]
  exact CGraph.numComponents_cartesianProduct _ _

/-! ### A minimum-degree condition for connectedness -/

theorem numComponents_eq_one_of_V_le_two_mul_minDeg (G : IsoGraph) (hV : 0 < G.V)
    (h : G.V ≤ 2 * minDeg G + 1) : G.numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_of_V_le_two_mul_minDeg (G := G) hV h)

theorem radius_cartesianProduct_self {G : IsoGraph} (hG : IsConnected G) :
    (G □g G).radius = 2 * G.radius := by
  rw [radius_cartesianProduct hG hG, two_mul]

/-! ### Girth three from strong regularity and from line graphs -/

/-- The edges at a vertex of degree three form a triangle in the line graph. -/
theorem girth_lineGraph_eq_three {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    (IsoGraph.lineGraph G).girth = 3 :=
  girth_eq_three_of_cliqueNum (le_trans h G.maxDeg_le_cliqueNum_lineGraph)

/-! ### Acyclicity from girth

`girth_eq_zero_iff` says that a graph is acyclic exactly when its girth is `0`, so every entry
in the girth table for the named families immediately rules out acyclicity — and, since a tree is
in particular acyclic, rules out being a tree as well. -/

theorem not_isAcyclic_of_girth_pos {G : IsoGraph} (h : 0 < G.girth) : ¬ IsAcyclic G := by
  rw [← girth_eq_zero_iff]
  omega

theorem girth_pos_of_not_isAcyclic {G : IsoGraph} (h : ¬ IsAcyclic G) : 0 < G.girth :=
  Nat.pos_of_ne_zero fun h0 ↦ h (girth_eq_zero_iff.1 h0)

theorem not_isTree_of_girth_pos {G : IsoGraph} (h : 0 < G.girth) : ¬ IsTree G :=
  fun ht ↦ not_isAcyclic_of_girth_pos h ((isTree_iff_isConnected_and_isAcyclic G).1 ht).2

/-- A graph with a vertex of degree at least three has a triangle in its line graph. -/
theorem not_isAcyclic_lineGraph {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    ¬ IsAcyclic (IsoGraph.lineGraph G) :=
  not_isAcyclic_of_girth_pos (by rw [girth_lineGraph_eq_three h]; omega)

/-- The radius of a path is `⌊n/2⌋`. -/
@[simp] theorem radius_path (n : ℕ) : (path (n + 1)).radius = (n + 1) / 2 := by
  simp [radius, IsoGraph.path, CGraph.radius]
  -- Goal: (SimpleGraph.pathGraph (n + 1)).radius.toNat = (n + 1) / 2
  set m := n + 1
  let G := SimpleGraph.pathGraph m
  -- adj_succ: edge between castSucc i and succ i for i : Fin n
  have adj_succ : ∀ i : Fin n, G.Adj i.castSucc i.succ := by
    intro i; simp [G, SimpleGraph.pathGraph_adj]
  -- walk from castSucc i to succ i, length 1
  have walk_succ : ∀ i : Fin n, ∃ p : G.Walk i.castSucc i.succ, p.length = 1 := by
    intro i; exact ⟨SimpleGraph.Walk.cons (adj_succ i) (.nil), by simp⟩
  -- walk from succ i to castSucc i, length 1 (reverse)
  have walk_prev : ∀ i : Fin n, ∃ p : G.Walk i.succ i.castSucc, p.length = 1 := by
    intro i; obtain ⟨q, hq⟩ := walk_succ i; exact ⟨q.reverse, by simp [hq]⟩
  -- walk from 0 to i of length i.val
  have walk0to : ∀ i : Fin (n + 1), ∃ p : G.Walk 0 i, p.length = (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero => exact ⟨.nil, rfl⟩
    | succ i ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨q, hq⟩ := walk_succ i
      exact ⟨p.append q, by simp [hp, hq]⟩
  -- walk from i to 0 of length i.val (reverse of walk0to)
  have waveto0 : ∀ i : Fin (n + 1), ∃ p : G.Walk i 0, p.length = (i : ℕ) := by
    intro i; obtain ⟨p, hp⟩ := walk0to i; exact ⟨p.reverse, by simp [hp]⟩
  -- walk from i to (last) of length (n - i.val)
  -- addK: i + k as Fin (n+1)
  let addK (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1) : Fin (n + 1) := ⟨i.val + k, hk⟩
  -- upWalkAny: walk from i to addK i k hk of length k (going right)
  have upWalkAny : ∀ (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1),
      ∃ p : G.Walk i (addK i k hk), p.length = k := by
    intro i k hk
    induction k with
    | zero => exact ⟨.nil, rfl⟩
    | succ m ih =>
      obtain ⟨p, hp⟩ := ih (by omega)
      have hm : (i : ℕ) + m < n := by omega
      obtain ⟨q, hq⟩ := walk_succ ⟨i.val + m, hm⟩
      exact ⟨p.append q, by simp [hp, hq]⟩

  -- edist upper bounds
  have edist_to_zero : ∀ i : Fin (n + 1), G.edist i 0 ≤ ↑(i : ℕ) := by
    intro i; obtain ⟨p, hp⟩ := waveto0 i
    rw [SimpleGraph.edist]
    exact le_trans (iInf_le _ p) (by simp [hp])
  have edist_to_last : ∀ i : Fin (n + 1), G.edist i ⟨n, Nat.lt_succ_self n⟩ ≤ ↑(n - (i : ℕ)) := by
    intro i
    have hk : (i : ℕ) + (n - (i : ℕ)) < n + 1 := by omega
    have hkep : addK i (n - (i : ℕ)) hk = ⟨n, Nat.lt_succ_self n⟩ := by
      ext; simp [addK, Nat.add_sub_of_le (show (i : ℕ) ≤ n from i.is_le)]
    rw [← hkep]
    obtain ⟨p, hp⟩ := upWalkAny i (n - (i : ℕ)) hk
    rw [SimpleGraph.edist]
    exact le_trans (iInf_le _ p) (by simp [hp])
  -- walk_pot: for any walk from a to b in pathGraph, b.val ≤ a.val + p.length
  have walk_pot : ∀ {a b : Fin (n + 1)} (p : G.Walk a b), (b : ℕ) ≤ (a : ℕ) + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | @cons u v w hadj p ih =>
      have hadj' : G.Adj u v := hadj
      simp [G, SimpleGraph.pathGraph_adj] at hadj'
      have : (v : ℕ) ≤ (u : ℕ) + 1 := by omega
      simp [SimpleGraph.Walk.length_cons]
      omega
  have edist_from_zero_ge : ∀ i : Fin (n + 1), ↑(i : ℕ) ≤ G.edist i 0 := by
    intro i
    rw [SimpleGraph.edist_comm]
    have hconn : G.Connected := SimpleGraph.pathGraph_connected n
    have hreach : G.Reachable 0 i := hconn 0 i
    have : Nonempty (G.Walk 0 i) := hreach
    rw [SimpleGraph.edist]
    have key : ∀ p : G.Walk 0 i, (i : ℕ∞) ≤ ↑p.length := by
      intro p
      have hpot := walk_pot p
      simp at hpot
      exact Nat.cast_le.mpr hpot
    exact le_ciInf key
  -- lower bound: edist i last ≥ n - i.val
  have edist_to_last_ge :
      ∀ i : Fin (n + 1), ↑(n - (i : ℕ)) ≤ G.edist i ⟨n, Nat.lt_succ_self n⟩ := by
    intro i
    have hconn : G.Connected := SimpleGraph.pathGraph_connected n
    have hreach : G.Reachable i ⟨n, Nat.lt_succ_self n⟩ := hconn i ⟨n, Nat.lt_succ_self n⟩
    have hwalk : Nonempty (G.Walk i ⟨n, Nat.lt_succ_self n⟩) := hreach
    rw [SimpleGraph.edist]
    have key : ∀ p : G.Walk i ⟨n, Nat.lt_succ_self n⟩, (n - (i : ℕ) : ℕ∞) ≤ ↑p.length := by
      intro p
      have hpot := walk_pot p
      show (↑(n - (i : ℕ)) : ℕ∞) ≤ ↑(p.length : ℕ)
      simp at hpot
      exact Nat.cast_le.mpr (by omega)
    exact le_ciInf key
  -- eccent bounds
  -- edist_le_diff_of_le: for u v with u.val ≤ v.val, edist u v ≤ ↑(v - u)
  have edist_le_diff_of_le :
      ∀ {u v : Fin (n + 1)}, (u : ℕ) ≤ v → G.edist u v ≤ ↑((v : ℕ) - (u : ℕ)) := by
    intro u v huv
    have hvk : (u : ℕ) + (v - u) < n + 1 := by omega
    have hkep : addK u (v - u) hvk = v := by ext; simp [addK, Nat.add_sub_of_le huv]
    obtain ⟨p, hp⟩ := upWalkAny u (v - u) hvk
    have := SimpleGraph.edist_le p
    rw [hp] at this
    simpa [hkep] using this
  have eccent_lower : ∀ i : Fin (n + 1), (max ((i : ℕ)) (n - (i : ℕ)) : ℕ∞) ≤ G.eccent i := by
    intro i
    unfold SimpleGraph.eccent
    have hbdd : BddAbove (Set.range (G.edist i)) := by
      have := Set.toFinite (Set.range (G.edist i))
      exact this.bddAbove
    refine max_le ?_ ?_
    · -- i.val ≤ eccent i: use edist i 0 ≥ i.val
      have : (↑((i : ℕ)) : ℕ∞) ≤ G.edist i 0 := edist_from_zero_ge i
      exact le_trans this (le_ciSup hbdd 0)
    · -- n - i.val ≤ eccent i: use edist i last ≥ n - i.val
      have : (↑(n - (i : ℕ)) : ℕ∞) ≤ G.edist i ⟨n, Nat.lt_succ_self n⟩ := edist_to_last_ge i
      exact le_trans this (le_ciSup hbdd ⟨n, Nat.lt_succ_self n⟩)
  have eccent_upper : ∀ i : Fin (n + 1), G.eccent i ≤ (max ((i : ℕ)) (n - (i : ℕ)) : ℕ∞) := by
    intro i
    unfold SimpleGraph.eccent
    apply ciSup_le
    intro j
    by_cases huv : (i : ℕ) ≤ (j : ℕ)
    · -- j ≥ i: edist i j ≤ ↑(j - i) ≤ ↑(n - i) ≤ max(i, n-i)
      have h1 : G.edist i j ≤ ↑((j : ℕ) - (i : ℕ)) := edist_le_diff_of_le huv
      have h2 : (↑((j : ℕ) - (i : ℕ)) : ℕ∞) ≤ (↑(n - (i : ℕ)) : ℕ∞) := Nat.cast_le.mpr (by omega)
      have h3 : (↑(n - (i : ℕ)) : ℕ∞) ≤ (max ((i : ℕ)) (n - (i : ℕ)) : ℕ∞) := by
        apply Nat.cast_le.mpr; exact le_max_right _ _
      exact le_trans (le_trans h1 h2) h3
    · -- j < i: edist i j = edist j i ≤ ↑(i - j) ≤ ↑i ≤ max(i, n-i)
      push_neg at huv
      have h1 : G.edist i j = G.edist j i := by rw [SimpleGraph.edist_comm]
      have h2 : G.edist j i ≤ ↑((i : ℕ) - (j : ℕ)) := edist_le_diff_of_le (le_of_lt huv)
      have h3 : (↑((i : ℕ) - (j : ℕ)) : ℕ∞) ≤ (↑((i : ℕ)) : ℕ∞) := Nat.cast_le.mpr (by omega)
      have h4 : (↑((i : ℕ)) : ℕ∞) ≤ (max ((i : ℕ)) (n - (i : ℕ)) : ℕ∞) := by
        apply Nat.cast_le.mpr; exact le_max_left _ _
      exact h1.symm ▸ le_trans (le_trans h2 h3) h4
  -- eccent i = max(i, n - i)
  have eccent_eq : ∀ i : Fin (n + 1), G.eccent i = (max ((i : ℕ)) (n - (i : ℕ)) : ℕ∞) := by
    intro i; exact le_antisymm (eccent_upper i) (eccent_lower i)
  -- radius = ⨅ i, ↑(max(i, n-i))
  have radius_eq : G.radius = (⨅ u : Fin (n + 1), (max ((u : ℕ)) (n - (u : ℕ)) : ℕ∞)) := by
    simp [SimpleGraph.radius, eccent_eq]
    rfl
  -- For all u : Fin (n+1), max(u, n-u) ≥ (n+1)/2 in ℕ
  have ge_half : ∀ u : Fin (n + 1), (n + 1) / 2 ≤ max ((u : ℕ)) (n - (u : ℕ)) := by
    intro u
    have hle : (n + 1) / 2 ≤ (u : ℕ) ∨ (n + 1) / 2 ≤ n - (u : ℕ) := by
      by_contra h
      push_neg at h
      omega
    exact hle.elim (fun h => h.trans (le_max_left _ _)) (fun h => h.trans (le_max_right _ _))
  -- There exists u with max(u, n-u) = (n+1)/2: take u = n/2
  have exists_eq_half : ∃ u : Fin (n + 1), max ((u : ℕ)) (n - (u : ℕ)) = (n + 1) / 2 := by
    refine ⟨⟨n / 2, by omega⟩, ?_⟩
    simp
    omega

  -- Bridge lemmas in ℕ∞
  have coe_tsub : ∀ (a b : ℕ), b ≤ a → (↑a : ℕ∞) - ↑b = ↑(a - b) := by
    intro a b hab
    simp
  have cast_max : ∀ (a b : ℕ), max (↑a : ℕ∞) (↑b : ℕ∞) = ↑(max a b) := by
    intro a b
    by_cases h : a ≤ b
    · rw [max_eq_right h, max_eq_right (by exact Nat.cast_le.mpr h)]
    · rw [max_eq_left (le_of_not_ge h), max_eq_left (by exact Nat.cast_le.mpr (le_of_not_ge h))]
  -- Key: f u = ↑(max (↑u) (n - ↑u))
  have f_eq : ∀ u : Fin (n + 1), max (↑↑u) (↑n - ↑↑u : ℕ∞) = ↑(max ((u : ℕ)) (n - (u : ℕ))) := by
    intro u
    rw [coe_tsub n (u : ℕ) u.is_le, cast_max]
  -- The inf of max(u, n-u) over u is (n+1)/2 (in ℕ∞)
  have inf_eq_half :
      (⨅ u : Fin (n + 1), max (↑↑u) (↑n - ↑↑u : ℕ∞)) = (↑((n + 1) / 2 : ℕ) : ℕ∞) := by
    have hbdd : BddBelow (Set.range (fun u : Fin (n + 1) => max (↑↑u) (↑n - ↑↑u : ℕ∞))) := by
      exact ⟨0, fun _ ⟨_, _⟩ => by positivity⟩
    apply le_antisymm
    · obtain ⟨u, hu⟩ := exists_eq_half
      have : max (↑↑u) (↑n - ↑↑u : ℕ∞) = ↑((n + 1) / 2 : ℕ) := by
        rw [f_eq u, hu]
      exact this ▸ ciInf_le hbdd u
    · apply le_ciInf
      intro u
      rw [f_eq u]
      exact_mod_cast ge_half u
  rw [radius_eq, inf_eq_half]
  simp [m]

/-! ### Connectivity of the strong and lexicographic products -/

@[simp] theorem numComponents_strongProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) : (G ⊠g H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_strongProduct hG hH)

@[simp] theorem numComponents_lexProduct {G H : IsoGraph} (hG : IsConnected G)
    (hH : IsConnected H) : (G ·g H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_lexProduct hG hH)

/-- The line graph of a connected graph with at least one edge is connected. -/
theorem isConnected_lineGraph {G : IsoGraph} (hG : IsConnected G) (hE : 0 < G.E) :
    IsConnected (lineGraph G) := by
  set H := G.toCGraph with hH_def
  rw [← IsoGraph.mk_toCGraph G]
  rw [lineGraph_mk H]
  rw [isConnected_mk]
  simp only [hH_def] at *
  have hG' : G.toCGraph.IsConnected := by
    rw [← isConnected_mk (G := G.toCGraph), IsoGraph.mk_toCGraph]
    exact hG
  have hE' : 0 < G.toCGraph.E := by
    rw [← E_mk (G := G.toCGraph), IsoGraph.mk_toCGraph]
    exact hE
  -- Theorem: line graph of a connected graph with edges is connected.
  have hedges : G.toCGraph.toSimple.edgeFinset.Nonempty := Finset.card_pos.mp
    (by rwa [CGraph.E] at hE')
  obtain ⟨e₀, he₀⟩ := hedges
  have he₀' : e₀ ∈ G.toCGraph.toSimple.edgeSet := by simpa using he₀
  set e₀' : (CGraph.lineGraph G.toCGraph).V := ⟨e₀, he₀'⟩
  -- For any vertex v of G, if some edge incident to v is reachable from e₀', then all edges
  -- incident to v are reachable from e₀'
  -- (because edges incident to the same vertex form a clique in the line graph)
  -- For any edge f of G, since G is connected, there's a path of vertices from an endpoint of e₀ to
  -- an endpoint of f.
  -- By induction along this path, all edges incident to vertices on the path are reachable. In
  -- particular, edges incident to the other endpoint of f are reachable, so f is reachable.
  -- Step 1: edges incident to a vertex u are pairwise reachable (they form a clique)
  have hclique : ∀ (u : G.toCGraph.V) (f g : (CGraph.lineGraph G.toCGraph).V),
      u ∈ f.1 → u ∈ g.1 → SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple f g := by
    intro u f g huf hug
    by_cases hfg : f = g
    · rw [hfg]
    · have hadj : (CGraph.lineGraph G.toCGraph).Adj f g = true := by
        rw [CGraph.lineGraph_adj]
        simp [hfg]
        exact ⟨u, huf, hug⟩
      exact (CGraph.toSimple_adj _ _ _).mpr hadj |>.reachable
  -- Pick an endpoint a of e₀
  -- Get endpoints of e₀: e₀'.1 is a Sym2 of V, and it's in edgeSet so it's an actual edge.
  -- I need at least one vertex from e₀'.1. I'll use induction on Sym2.
  have h_sym2_mem : ∀ (s : Sym2 (G.toCGraph.V)), ∃ v : G.toCGraph.V, v ∈ s := by
    intro s
    change Quot (Sym2.Rel (G.toCGraph.V)) at s
    obtain ⟨p, rfl⟩ := Quot.exists_rep s
    refine ⟨p.1, ?_⟩
    show Sym2.Mem p.1 (Quot.mk (Sym2.Rel G.toCGraph.V) p)
    simp [Sym2.Mem]
    exact ⟨p.2, Or.inl rfl⟩
  obtain ⟨a, ha_mem⟩ := h_sym2_mem e₀'.1
  -- All edges incident to a are reachable from e₀' (clique at a, using e₀' itself)
  have hreach_a : ∀ f : (CGraph.lineGraph G.toCGraph).V, a ∈ f.1 →
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f := by
    intro f hf
    exact hclique a e₀' f ha_mem hf
  -- A vertex is "swept" if all edges incident to it are reachable from e₀'
  let Swept (v : G.toCGraph.V) : Prop := ∀ f : (CGraph.lineGraph G.toCGraph).V, v ∈ f.1 →
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f
  have hswept_a : Swept a := hreach_a
  -- Sweep propagates along adjacencies
  have hsweep_prop : ∀ u v : G.toCGraph.V, G.toCGraph.Adj u v = true → Swept u → Swept v := by
    intro u v huv ih
    -- The edge {u,v} is incident to u, hence reachable
    let fe : (CGraph.lineGraph G.toCGraph).V := ⟨Sym2.mk ⟨u, v⟩, by
      simpa [CGraph.toSimple_adj, SimpleGraph.mem_edgeSet] using huv⟩
    have hfe_u : u ∈ fe.1 := by simp [fe]
    have hfe_v : v ∈ fe.1 := by simp [fe]
    have hfe_reach := ih fe hfe_u
    intro g hg_v
    exact hfe_reach.trans (hclique v fe g hfe_v hg_v)
  -- All vertices are swept (by connectedness, from a)
  have hswept_all : ∀ v : G.toCGraph.V, Swept v := by
    intro v
    have hswept_all' : ∀ {u w : G.toCGraph.V} (w' : G.toCGraph.toSimple.Walk u w), Swept u → Swept w
      := by
      intro u w w'
      induction w' with
      | nil => exact id
      | cons hadj tail ih =>
        intro hu
        exact ih (hsweep_prop _ _ hadj hu)
    have hreach : G.toCGraph.toSimple.Reachable a v := by
      change G.toCGraph.toSimple.Connected at hG'
      exact hG' a v
    obtain ⟨w⟩ := hreach
    exact hswept_all' w hswept_a
  -- All edges of G are reachable
  have hreach_all_edges : ∀ f : (CGraph.lineGraph G.toCGraph).V,
      SimpleGraph.Reachable (CGraph.lineGraph G.toCGraph).toSimple e₀' f := by
    intro f
    obtain ⟨v, hv⟩ := h_sym2_mem f.1
    exact hswept_all v f hv
  letI : Nonempty (CGraph.lineGraph G.toCGraph).V := ⟨e₀'⟩
  exact SimpleGraph.Connected.mk (fun e f => (hreach_all_edges e).symm.trans (hreach_all_edges f))

/-- **A graph of girth three is not bipartite**: a bipartite graph with a cycle has girth at
least four. -/
theorem not_isBipartite_of_girth_eq_three {G : IsoGraph} (h : G.girth = 3) : ¬ IsBipartite G := by
  intro hb
  have := four_le_girth_of_isBipartite hb (not_isAcyclic_of_girth_pos (by omega))
  omega

/-- **The line graph of a graph with a degree-three vertex is not bipartite**: the three edges
at that vertex form a triangle. -/
theorem not_isBipartite_lineGraph {G : IsoGraph} (h : 3 ≤ G.maxDeg) :
    ¬ IsBipartite (lineGraph G) :=
  not_isBipartite_of_girth_eq_three (girth_lineGraph_eq_three h)

theorem isConnected_tensorProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H)
    (hb : ¬ IsBipartite G) (hE : 0 < H.E) : IsConnected (G ⊗g H) := by
  -- Lift to CGraph level
  have hG_iso : Quotient.mk _ G.toCGraph = G := IsoGraph.mk_toCGraph G
  have hH_iso : Quotient.mk _ H.toCGraph = H := IsoGraph.mk_toCGraph H
  have htensor : G ⊗g H = ⟦G.toCGraph ⊗g H.toCGraph⟧ := by
    conv_lhs => rw [← hG_iso, ← hH_iso]
    exact tensorProduct_mk _ _
  rw [htensor, isConnected_mk]
  -- Now goal: CGraph.IsConnected (tensorProduct G.toCGraph H.toCGraph)
  have hGC : CGraph.IsConnected G.toCGraph := by
    have := IsoGraph.isConnected_mk G.toCGraph
    rw [hG_iso] at this; exact this.mp hG
  have hHC : CGraph.IsConnected H.toCGraph := by
    have := IsoGraph.isConnected_mk H.toCGraph
    rw [hH_iso] at this; exact this.mp hH
  have hB : ¬ CGraph.IsBipartite G.toCGraph := by
    have h2 : G.IsBipartite ↔ G.toCGraph.IsBipartite := by
      rw [← IsoGraph.isBipartite_mk, hG_iso]
    exact fun h => hb (h2.mpr h)
  have hED : 0 < H.toCGraph.E := by
    have h := IsoGraph.E_mk H.toCGraph
    rw [hH_iso] at h; rw [h] at hE; exact hE
  -- Goal: CGraph.IsConnected (tensorProduct G.toCGraph H.toCGraph)
  -- Unfold to SimpleGraph level
  rw [CGraph.IsConnected]
  -- Hs	V is G.V × H.V
  -- Adj in tensor product: (g1,h1) ~ (g2,h2) ↔ G.Adj g1 g2 ∧ H.Adj h1 h2
  -- Key idea (Weichsel's theorem): 
  --   - G is connected + non-bipartite → from any g, closed walks of both parities
  --   - H is connected + has an edge → from any h, can reach any h' with both parities
  --   → tensor product is connected
  -- Step 1: Get an edge in H.toSimple
  have hHne : Nonempty H.toCGraph.V := hHC.nonempty
  have hGne : Nonempty G.toCGraph.V := hGC.nonempty
  have hVne : Nonempty ((G.toCGraph ⊗g H.toCGraph).V) := 
    ⟨(Classical.choice hGne, Classical.choice hHne)⟩
  -- Step 2: Work at SimpleGraph level
  set Gs := G.toCGraph.toSimple
  set Hs := H.toCGraph.toSimple
  have hGCs : SimpleGraph.Connected Gs := hGC
  have hBs : ¬ SimpleGraph.IsBipartite Gs := by
    show ¬ G.toCGraph.toSimple.IsBipartite
    intro h
    apply hB
    rw [CGraph.isBipartite_iff_colorable]
    exact h
  -- Get an edge in Hs from hED
  have hHedge : ∃ (u v : H.toCGraph.V), Hs.Adj u v := by
    simp only [Hs, CGraph.toSimple_adj]
    have hne : H.toCGraph.toSimple ≠ ⊥ :=
      (CGraph.toSimple_ne_bot_iff (G := H.toCGraph)).symm.mp hED
    have hne_card : 0 < H.toCGraph.toSimple.edgeFinset.card :=
      Finset.card_pos.mpr (SimpleGraph.edgeFinset_nonempty.mpr hne)
    have hne : H.toCGraph.toSimple.edgeFinset.Nonempty := Finset.card_pos.mp hne_card
    obtain ⟨e, he⟩ := hne
    rcases e with ⟨a, b⟩
    have hadj : Hs.Adj a b := by
      have := SimpleGraph.mem_edgeFinset.mp he
      exact this
    exact ⟨a, b, hadj⟩
  obtain ⟨u₀, v₀, huv₀⟩ := hHedge
  -- Reachability in tensor product:
  -- Key facts:
  -- 1. Walk extension in H: from any walk in H, I can add 2 to its length by going u₀-v₀-u₀
  -- 2. G is connected and non-bipartite: from any g1 to any g2, walks of both parities exist
  --    (using the odd closed walk from non-bipartiteness)
  -- 3. Pair walks of same length in G and H to get a walk in G ⊗ H
  -- Strategy: from (g₀, u₀) to (g, h):
  --   - Get a walk in H from u₀ to h of length d (by connectivity of Hs)
  --   - Pad to even length 2k ≥ d using edge (u₀,v₀)
  --   - Get a walk in G from g₀ to g of the same even length (G is connected and nonbipartite)
  --   - Pair to get walk in tensor product
  -- Let T be the tensor product simple graph
  set T := (G.toCGraph.tensorProduct H.toCGraph).toSimple
  -- Get a base vertex
  let g₀ := Classical.choice hGne
  set base : (G.toCGraph.tensorProduct H.toCGraph).V := (g₀, u₀)
  -- Goal: T.Connected
  -- We show preconnected + nonempty
  apply SimpleGraph.Connected.mk
  · -- Preconnected: all reachable from base
    have hreach_H_u : ∀ h : H.toCGraph.V, Hs.Reachable h u₀ := fun h => (hHC.preconnected h u₀)
    have hreach_H_v : ∀ h : H.toCGraph.V, Hs.Reachable h v₀ := fun h => (hHC.preconnected h v₀)
    -- Walk pairing in tensor product: equal-length walks pair to a walk in T
    have walk_pair_aux : ∀ {g1 g2 : G.toCGraph.V} {h1 h2 : H.toCGraph.V} {L : ℕ},
        ∀ (wG : Gs.Walk g1 g2) (wH : Hs.Walk h1 h2), wG.length = L → wH.length = L →
        T.Reachable (g1, h1) (g2, h2) := by
      intro g1 g2 h1 h2 L wG wH hwG hwH
      induction L generalizing g1 g2 h1 h2 wG wH with
      | zero =>
        have hg : g1 = g2 := by
          induction wG with
          | nil => rfl
          | cons _ _ ih => simp at hwG
        have hh : h1 = h2 := by
          induction wH with
          | nil => rfl
          | cons _ _ ih => simp at hwH
        rw [hg, hh]
      | succ L ih =>
        cases wG with
        | nil => simp at hwG
        | @cons g1 g1' g2 hadj_wG rest_wG =>
          cases wH with
          | nil => simp at hwH
          | @cons h1 h1' h2 hadj_wH rest_wH =>
            have hwG' : rest_wG.length = L := by
              simp [SimpleGraph.Walk.length] at hwG; linarith
            have hwH' : rest_wH.length = L := by
              simp [SimpleGraph.Walk.length] at hwH; linarith
            have hr := ih rest_wG rest_wH hwG' hwH'
            have hadj_T : T.Adj (g1, h1) (g1', h1') := by
              simp [T, CGraph.toSimple_adj]
              exact ⟨hadj_wG, hadj_wH⟩
            exact ⟨SimpleGraph.Walk.cons hadj_T hr.some⟩
    -- Reachability from g₀ in Gs
    have hreach_g₀ : ∀ v : G.toCGraph.V, Gs.Reachable g₀ v := fun v => (hGCs.preconnected g₀) v
    let walkTo : ∀ v : G.toCGraph.V, Gs.Walk g₀ v := fun v => (hreach_g₀ v).some
    -- Odd closed walk at g₀ from ¬bipartite (by contradiction + coloring)
    have hodd_closed : ∃ (w : Gs.Walk g₀ g₀), w.length % 2 = 1 := by
      by_contra h_even
      push_neg at h_even
      have hwelldef : ∀ (v : G.toCGraph.V) (w1 w2 : Gs.Walk g₀ v),
          w1.length % 2 = w2.length % 2 := by
        intro v w1 w2
        have h1 : (w1.append w2.reverse).length = w1.length + w2.length := by
          rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
        have h2 := h_even (w1.append w2.reverse)
        rw [h1] at h2
        omega
      let color : G.toCGraph.V → Fin 2 := fun v => ⟨(walkTo v).length % 2, Nat.mod_lt _ (by omega)⟩
      have hcolor_adj : ∀ {u v : G.toCGraph.V}, Gs.Adj u v → color u ≠ color v := by
        intro u v hadj
        simp only [color]
        let hcons : Gs.Walk g₀ v :=
          (walkTo u).append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
        have hlen : hcons.length = (walkTo u).length + 1 := by
          simp [hcons, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
            SimpleGraph.Walk.length_nil]
        have hwd := hwelldef v (walkTo v) hcons
        rw [hlen] at hwd
        exact Fin.ne_of_val_ne (by omega : (walkTo u).length % 2 ≠ (walkTo v).length % 2)
      exact hBs ⟨color, hcolor_adj⟩
    obtain ⟨wOdd, hwOdd⟩ := hodd_closed
    -- Odd closed walk at any vertex g
    let oddAtG : ∀ g : G.toCGraph.V, Gs.Walk g g := fun g =>
      (walkTo g).reverse.append (wOdd.append (walkTo g))
    have hoddAtG_len : ∀ g, (oddAtG g).length % 2 = 1 := by
      intro g
      simp [oddAtG, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
      omega
    -- Even closed walk at g (append two odd closed walks)
    let evenAtG : ∀ g : G.toCGraph.V, Gs.Walk g g :=
      fun g => oddAtG g |> SimpleGraph.Walk.append <| oddAtG g
    have hevenAtG_len' : ∀ g, (evenAtG g).length = 2 * (oddAtG g).length := by
      intro g; simp [evenAtG, SimpleGraph.Walk.length_append]
      ring
    have hoddAtG_pos : ∀ g, 0 < (oddAtG g).length := by
      intro g; by_contra h; have := hoddAtG_len g
      simp [show (oddAtG g).length = 0 from le_antisymm (le_of_not_gt h) (Nat.zero_le _)] at this
    -- Pad G walk by k even detours (adds 2*(oddAtG target).length per detour)
    let padWalkGAt (target : G.toCGraph.V) : ∀ (w : Gs.Walk g₀ target) (k : ℕ), Gs.Walk g₀ target :=
      fun w k => Nat.rec w (fun _ w' => w'.append (evenAtG target)) k
    have hpadiWalkGAt_len : ∀ (target : G.toCGraph.V) (w : Gs.Walk g₀ target) (k : ℕ),
        (padWalkGAt target w k).length = w.length + k * (2 * (oddAtG target).length) := by
      intro target w k; induction k with
      | zero => simp [padWalkGAt]
      | succ k ih => simp [padWalkGAt, hevenAtG_len']; linarith
    -- Pad H-walk: prepend u₀→v₀→u₀ detour adds +2 to length
    let padWalk : ∀ {target : H.toCGraph.V} (w : Hs.Walk u₀ target) (k : ℕ), Hs.Walk u₀ target :=
      fun w k => Nat.rec w
        (fun _ w' => SimpleGraph.Walk.cons huv₀ (SimpleGraph.Walk.cons (Hs.symm huv₀) w')) k
    have hpadiWalk_len : ∀ {target : H.toCGraph.V} (w : Hs.Walk u₀ target) (k : ℕ),
        (padWalk w k).length = w.length + 2 * k := by
      intro target w k
      induction k with
      | zero => simp [padWalk]
      | succ k ih => simp [padWalk, SimpleGraph.Walk.length_cons]; linarith
    -- Walk of given parity from g₀ to g
    have hwalk_parity : ∀ (g : G.toCGraph.V) (p : Bool),
        ∃ (w : Gs.Walk g₀ g), w.length % 2 = (if p then 1 else 0) := by
      intro g p
      have hodd_len : (oddAtG g).length % 2 = 1 := hoddAtG_len g
      have happend_len : ∀ (w : Gs.Walk g₀ g),
          (w.append (oddAtG g)).length = w.length + (oddAtG g).length := by
        intro w; rw [SimpleGraph.Walk.length_append]
      by_cases hp : p
      · -- p = true, need % 2 = 1
        by_cases hd : (walkTo g).length % 2 = 1
        · exact ⟨walkTo g, by simp [hp]; exact hd⟩
        · exact ⟨(walkTo g).append (oddAtG g), by simp [hp, happend_len]; omega⟩
      · -- p = false, need % 2 = 0
        simp [hp]
        by_cases hd : (walkTo g).length % 2 = 0
        · exact ⟨walkTo g, hd⟩
        · exact ⟨(walkTo g).append (oddAtG g), by simp [happend_len]; omega⟩
    -- Now prove Preconnected
    have h_preconn : ∀ (p : (G.toCGraph.tensorProduct H.toCGraph).V), T.Reachable base p := by
      intro ⟨g, h⟩
      let wH₀ : Hs.Walk u₀ h := (hreach_H_u h).some.reverse
      let p' : Bool := wH₀.length % 2 = 1
      obtain ⟨wG_base, hwG_par⟩ := hwalk_parity g p'
      have hwG_par' : wG_base.length % 2 = wH₀.length % 2 := by
        unfold p' at hwG_par
        have := Nat.mod_lt wH₀.length two_pos
        interval_cases wH₀.length % 2 <;> simp at hwG_par ⊢ <;> exact hwG_par
      let odd_len_g := (oddAtG g).length
      let m := wH₀.length + 1
      let wG' := padWalkGAt g wG_base m
      have hm_pos : 0 < m := by simp [m]
      have hodd_pos : 0 < (oddAtG g).length := hoddAtG_pos g
      have hwG'_len : wG'.length ≥ wH₀.length := by
        rw [hpadiWalkGAt_len g wG_base m]
        show wH₀.length ≤ wG_base.length + (wH₀.length + 1) * (2 * (oddAtG g).length)
        nlinarith [hoddAtG_pos g]
      have hwG'_par : wG'.length % 2 = wG_base.length % 2 := by
        rw [hpadiWalkGAt_len g wG_base m]
        simp [Nat.add_mod, Nat.mul_mod, Nat.zero_mod]
      have hwG'_par' : wG'.length % 2 = wH₀.length % 2 := by rw [hwG'_par, hwG_par']
      have hwG'_par' : wG'.length % 2 = wH₀.length % 2 := by rw [hwG'_par, hwG_par']
      let L := wG'.length
      let k := L - wH₀.length
      have hk_even : 2 ∣ k := by omega
      obtain ⟨n, hn⟩ := hk_even
      let wH_padded := padWalk wH₀ n
      have hwH_pad_len : wH_padded.length = L := by
        rw [hpadiWalk_len]; omega
      exact walk_pair_aux wG' wH_padded rfl hwH_pad_len
    show T.Preconnected
    intro p q
    exact (h_preconn p).symm.trans (h_preconn q)

/-- With no isolated vertex every original reaches a shadow, and every shadow reaches the apex. -/
theorem isConnected_mycielskian (G : IsoGraph) (h : 0 < G.minDeg) :
    IsConnected (mycielskian G) := by
  induction G using Quotient.inductionOn with | _ H =>
  classical
  have hH : 0 < H.minDeg := by rwa [minDeg_mk] at h
  rw [mycielskian_mk, isConnected_mk]
  -- Goal: H.mycielskian.IsConnected
  show SimpleGraph.Connected (H.mycielskian.toSimple)
  rw [SimpleGraph.connected_iff]
  have hab : ∀ a : H.V, ∃ b : H.V, H.Adj a b = true := by
    intro a
    have hmin : H.minDeg = H.toSimple.minDegree := rfl
    have hdeg_ge : H.toSimple.minDegree ≤ H.toSimple.degree a :=
      SimpleGraph.minDegree_le_degree _ a
    have hdeg : 0 < H.toSimple.degree a := by omega
    rw [SimpleGraph.degree, Finset.card_pos] at hdeg
    obtain ⟨b, hb⟩ := hdeg
    simp [SimpleGraph.mem_neighborFinset] at hb
    exact ⟨b, hb⟩
  constructor
  · -- Preconnected: everyone reaches everyone via apex `none`
    intro u v
    -- Everyone reaches none, none reaches everyone → everyone reaches everyone
    have hto_apex : ∀ w : (H.mycielskian).V, (H.mycielskian).toSimple.Reachable w none := by
      intro w
      cases w with
      | none => rfl
      | some w =>
        cases w with
        | inl a =>
          obtain ⟨b, hb⟩ := hab a
          show (H.mycielskian.toSimple).Reachable _ _
          have h1 : H.mycielskian.Adj (some (.inl a)) (some (.inr b)) = true := by
            rw [CGraph.mycielskian_adj_inl_inr H a b, hb]
          have h2 : H.mycielskian.Adj (some (.inr
              b)) none = true := CGraph.mycielskian_adj_inr_none H b
          exact ((SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h1)
            (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h2)
                SimpleGraph.Walk.nil)).reachable)
        | inr b =>
          show (H.mycielskian.toSimple).Reachable _ _
          have : H.mycielskian.Adj (some (.inr
              b)) none = true := CGraph.mycielskian_adj_inr_none H b
          exact (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact this)
              SimpleGraph.Walk.nil).reachable
    have h_apex_to : ∀ w : (H.mycielskian).V, (H.mycielskian).toSimple.Reachable none w := by
      intro w
      cases w with
      | none => exact SimpleGraph.Reachable.refl none
      | some w =>
        cases w with
        | inl c =>
          obtain ⟨d, hd⟩ := hab c
          show (H.mycielskian.toSimple).Reachable none _
          have h1 : H.mycielskian.Adj none (some (.inr
              d)) = true := CGraph.mycielskian_adj_none_inr H d
          have h2 : H.mycielskian.Adj (some (.inr d)) (some (.inl c)) = true := by
            rw [CGraph.mycielskian_adj_inr_inl H d c]
            exact (H.symm d c).trans hd
          exact ((SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h1)
            (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact h2)
                SimpleGraph.Walk.nil)).reachable)
        | inr b =>
          show (H.mycielskian.toSimple).Reachable none _
          have : H.mycielskian.Adj none (some (.inr
              b)) = true := CGraph.mycielskian_adj_none_inr H b
          exact (SimpleGraph.Walk.cons (by show (H.mycielskian.toSimple).Adj _ _; exact this)
              SimpleGraph.Walk.nil).reachable
    exact (hto_apex u).trans (h_apex_to v)
  · -- Nonempty
    exact ⟨none⟩

/-! ### The lexicographic product of a complete graph with a cycle -/

theorem isConnected_lexProduct_complete_cycle (m n : ℕ) :
    IsConnected (complete (m + 1) ·g cycle (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_cycle n)

/-! ### The lexicographic product of a complete graph with a path -/

theorem isConnected_lexProduct_complete_path (m n : ℕ) :
    IsConnected (complete (m + 1) ·g path (n + 1)) :=
  isConnected_lexProduct (isConnected_complete m) (isConnected_path n)

theorem girth_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G + maxDeg H) : (lineGraph (G □g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_cartesianProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V)
    (hH : 0 < H.V) (h3 : 3 ≤ maxDeg G + maxDeg H) : ¬ IsBipartite (lineGraph (G □g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_cartesianProduct hG hH]; exact h3)

theorem girth_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ max (maxDeg G + H.V) (G.V + maxDeg H)) : (lineGraph (G ∇g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_join hG hH]; exact h3)

theorem girth_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) : (lineGraph (G ⊗g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_tensorProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * maxDeg H) : ¬ IsBipartite (lineGraph (G ⊗g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_tensorProduct hG hH]; exact h3)

theorem girth_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) : (lineGraph (G ·g H)).girth = 3 :=
  girth_lineGraph_eq_three (by rw [maxDeg_lexProduct hG hH]; exact h3)

theorem not_isBipartite_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (h3 : 3 ≤ maxDeg G * H.V + maxDeg H) : ¬ IsBipartite (lineGraph (G ·g H)) :=
  not_isBipartite_lineGraph (by rw [maxDeg_lexProduct hG hH]; exact h3)

end IsoGraph
