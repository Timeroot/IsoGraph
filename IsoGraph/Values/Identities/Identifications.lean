import IsoGraph.Values.Identities.EdgeColourings

/-!
# The equations between the constructions

The point of the quotient: on `IsoGraph`, "the complement of the 5-cycle is the 5-cycle" is an
equation, and this module collects the hundred or so of them.  Vertex counts first, then the two
recognition lemmas `mk_eq_empty` and `mk_eq_complete` that settle every degenerate case, then
family by family — the join and what is built from it, the complement, disjoint unions, the small
sporadic identities, the complete multipartite graphs, the circulants, Paley, Kneser and Johnson,
the hypercubes and folded cubes, the decorated cycles and trees, and the four products.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## Vertex counts -/

@[simp] theorem V_empty (n : ℕ) : (empty n).V = n := CGraph.card_empty n
@[simp] theorem V_complete (n : ℕ) : (complete n).V = n := CGraph.card_complete n
@[simp] theorem V_path (n : ℕ) : (path n).V = n := CGraph.card_path n
@[simp] theorem V_cycle (n : ℕ) : (cycle n).V = n := CGraph.card_cycle n
@[simp] theorem V_bipartite (m n : ℕ) : (bipartite m n).V = m + n := CGraph.card_bipartite m n
@[simp] theorem V_star (n : ℕ) : (star n).V = 1 + n := CGraph.card_star n
@[simp] theorem V_kneser (n k : ℕ) : (kneser n k).V = n.choose k := CGraph.card_kneser n k
@[simp] theorem V_johnson (n k : ℕ) : (johnson n k).V = n.choose k := CGraph.card_johnson n k
@[simp] theorem V_hypercube (n : ℕ) : (hypercube n).V = 2 ^ n := CGraph.card_hypercube n
@[simp] theorem V_paley (q : ℕ) : (paley q).V = q := CGraph.card_paley q
@[simp] theorem V_circulant (n : ℕ) (S : List ℕ) : (circulant n S).V = n :=
  CGraph.card_circulant n S
@[simp] theorem V_foldedCube (n : ℕ) : (foldedCube n).V = 2 ^ n := CGraph.card_foldedCube n
@[simp] theorem V_wheel (n : ℕ) : (wheel n).V = 1 + n := by
  show Fintype.card (CGraph.wheel n).V = _
  simp [CGraph.wheel]
@[simp] theorem V_thetaGraph (xs : List ℕ) : (thetaGraph xs).V = 2 + xs.sum :=
  CGraph.card_thetaGraph xs
@[simp] theorem V_tadpole (m k : ℕ) : (tadpole m k).V = m + k := CGraph.card_tadpole m k
@[simp] theorem V_lollipop (m k : ℕ) : (lollipop m k).V = m + k := CGraph.card_lollipop m k
@[simp] theorem V_spider (legs : List ℕ) : (spider legs).V = 1 + legs.sum :=
  CGraph.card_spider legs
@[simp] theorem V_doubleStar (m n : ℕ) : (doubleStar m n).V = 2 + m + n :=
  CGraph.card_doubleStar m n
@[simp] theorem V_cyclePendant (m : ℕ) (ks : List ℕ) : (cyclePendant m ks).V = m + ks.sum :=
  CGraph.card_cyclePendant m ks

@[simp] theorem V_compl (G : IsoGraph) : Gᶜ.V = G.V := by
  induction G using Quotient.inductionOn with
  | h g => show Fintype.card (CGraph.compl g.canonicalize).V = _; simp

@[simp] theorem V_disjUnion (G H : IsoGraph) : (G ⊕g H).V = G.V + H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h => exact CGraph.card_disjUnion g h

@[simp] theorem V_join (G H : IsoGraph) : (G ∇g H).V = G.V + H.V := by
  show (Gᶜ ⊕g Hᶜ)ᶜ.V = _
  simp

@[simp] theorem V_cartesianProduct (G H : IsoGraph) :
    (G □g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.cartesianProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_tensorProduct (G H : IsoGraph) : (G ⊗g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.tensorProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_strongProduct (G H : IsoGraph) : (G ⊠g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.strongProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_lexProduct (G H : IsoGraph) : (G ·g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.lexProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_lineGraph (G : IsoGraph) : (lineGraph G).V = G.E := by
  induction G using Quotient.inductionOn with
  | h g =>
    show Fintype.card (CGraph.lineGraph g.canonicalize).V = _
    rw [CGraph.card_lineGraph, ← E_mk, mk_canonicalize]

@[simp] theorem V_mycielskian (G : IsoGraph) : (mycielskian G).V = 2 * G.V + 1 := by
  induction G using Quotient.inductionOn with
  | h g =>
    show Fintype.card (CGraph.mycielskian g.canonicalize).V = _
    simp

/-! ## Recognising `empty` and `complete`

Every degenerate identity in this file goes through one of these two: a graph with no edges is
`empty` on its vertex count, and a graph with all of them is `complete`.  Neither needs an
explicit bijection — `Fintype.equivFin` supplies one, and it is used only inside a proof, so its
noncomputability costs nothing. -/

/-- A graph with no edges is the edgeless graph on its vertex count. -/
theorem mk_eq_empty {G : CGraph} (h : ∀ x y, G.Adj x y = false) :
    (⟦G⟧ : IsoGraph) = empty (Fintype.card G.V) :=
  Quotient.sound ⟨CGraph.isoOfAdj (Fintype.equivFin G.V) fun x y ↦ (h x y).symm⟩

/-- A graph in which every two distinct vertices are adjacent is the complete graph on its vertex
count. -/
theorem mk_eq_complete {G : CGraph} (h : ∀ x y, x ≠ y → G.Adj x y = true) :
    (⟦G⟧ : IsoGraph) = complete (Fintype.card G.V) :=
  Quotient.sound ⟨CGraph.isoOfAdj (Fintype.equivFin G.V) fun x y ↦ by
    rw [CGraph.complete_adj]
    by_cases hxy : x = y
    · cases hxy
      rw [(Bool.not_eq_true _).mp (G.loopless x)]
      simp
    · rw [h x y hxy]
      exact decide_eq_true fun hh ↦ hxy ((Fintype.equivFin G.V).injective hh)⟩

/-- A graph with no vertices is the empty graph on `0` vertices. -/
theorem mk_eq_empty_zero {G : CGraph} [IsEmpty G.V] : (⟦G⟧ : IsoGraph) = empty 0 := by
  rw [mk_eq_empty (G := G) fun x _ ↦ isEmptyElim x, Fintype.card_eq_zero]

/-! ## The join, and the constructions built from it

The `IsoGraph`-level `join`, defined as `(disjUnion Gᶜ Hᶜ)ᶜ` with no lift of its own, agrees
with `CGraph.join`; that is `join_mk`, in `IsoGraph/Graphs/Quotient.lean`. -/

theorem join_def (G H : IsoGraph) : G ∇g H = (Gᶜ ⊕g Hᶜ)ᶜ := rfl

theorem bipartite_eq_compl (m n : ℕ) :
    bipartite m n = (complete m ⊕g complete n)ᶜ := by
  rw [complete_def, complete_def, disjUnion_mk, compl_mk]
  rfl

theorem star_eq_bipartite (n : ℕ) : star n = bipartite 1 n := rfl

theorem wheel_eq_join (n : ℕ) : wheel n = complete 1 ∇g cycle n := by
  rw [complete_def, cycle_def, join_mk]
  rfl

/-! ## Complementation -/

@[simp] theorem compl_compl (G : IsoGraph) : Gᶜᶜ = G := by
  induction G using Quotient.inductionOn with
  | h g =>
    show (show IsoGraph from ⟦CGraph.compl g.canonicalize⟧)ᶜ = ⟦g⟧
    rw [compl_mk, CGraph.compl_compl]
    exact mk_canonicalize g

@[simp] theorem compl_empty (n : ℕ) : (empty n)ᶜ = complete n := by
  rw [empty_def, compl_mk]
  rfl

@[simp] theorem compl_complete (n : ℕ) : (complete n)ᶜ = empty n := by
  rw [← compl_empty, compl_compl]

@[simp] theorem compl_join (G H : IsoGraph) :
    (G ∇g H)ᶜ = Gᶜ ⊕g Hᶜ := by
  show (Gᶜ ⊕g Hᶜ)ᶜᶜ = _
  rw [compl_compl]

@[simp] theorem compl_disjUnion (G H : IsoGraph) :
    (G ⊕g H)ᶜ = Gᶜ ∇g Hᶜ := by
  show _ = (Gᶜᶜ ⊕g Hᶜᶜ)ᶜ
  rw [compl_compl, compl_compl]

@[simp] theorem compl_bipartite (m n : ℕ) :
    (bipartite m n)ᶜ = complete m ⊕g complete n := by
  rw [bipartite_eq_compl, compl_compl]

/-! ## Disjoint unions -/

theorem disjUnion_comm (G H : IsoGraph) : G ⊕g H = H ⊕g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h => exact Quotient.sound (CGraph.disjUnion_comm g h)

theorem disjUnion_assoc (G H K : IsoGraph) :
    (G ⊕g H) ⊕g K = G ⊕g (H ⊕g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k => exact Quotient.sound (CGraph.disjUnion_assoc g h k)

@[simp] theorem disjUnion_empty_zero (G : IsoGraph) : G ⊕g empty 0 = G := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [empty_def, disjUnion_mk]
    exact Quotient.sound ⟨CGraph.isoOfAdj
      (G := CGraph.disjUnion g (CGraph.empty 0)) (H := g)
      (Equiv.sumEmpty g.V (CGraph.empty 0).V)
      (by rintro (a | a) (b | b) <;> first
            | rfl
            | exact (IsEmpty.false a).elim
            | exact (IsEmpty.false b).elim)⟩

@[simp] theorem empty_zero_disjUnion (G : IsoGraph) : empty 0 ⊕g G = G := by
  rw [disjUnion_comm, disjUnion_empty_zero]

@[simp] theorem disjUnion_empty (m n : ℕ) : empty m ⊕g empty n = empty (m + n) := by
  rw [empty_def, empty_def, disjUnion_mk,
    mk_eq_empty (G := CGraph.disjUnion (CGraph.empty m) (CGraph.empty n))
      (by rintro (a | a) (b | b) <;> rfl)]
  simp

/-! ## Joins -/

theorem join_comm (G H : IsoGraph) : G ∇g H = H ∇g G := by
  show (Gᶜ ⊕g Hᶜ)ᶜ = (Hᶜ ⊕g Gᶜ)ᶜ
  rw [disjUnion_comm]

theorem join_assoc (G H K : IsoGraph) : (G ∇g H) ∇g K = G ∇g (H ∇g K) := by
  show ((G ∇g H)ᶜ ⊕g Kᶜ)ᶜ
    = (Gᶜ ⊕g (H ∇g K)ᶜ)ᶜ
  show ((Gᶜ ⊕g Hᶜ)ᶜᶜ ⊕g Kᶜ)ᶜ
    = (Gᶜ ⊕g (Hᶜ ⊕g Kᶜ)ᶜᶜ)ᶜ
  rw [compl_compl, compl_compl, disjUnion_assoc]

/-! ## Small graphs

The degenerate cases: everything with at most two vertices, and the handful of coincidences
between named families that only happen at small size. -/

@[simp] theorem complete_zero : complete 0 = empty 0 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem complete_one : complete 1 = empty 1 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem path_zero : path 0 = empty 0 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem path_one : path 1 = empty 1 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem path_two : path 2 = complete 2 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem cycle_zero : cycle 0 = empty 0 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem cycle_one : cycle 1 = empty 1 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

@[simp] theorem cycle_two : cycle 2 = complete 2 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

/-- The triangle is the complete graph on three vertices.  Not a `simp` lemma: neither side is
obviously the simpler one, and rewriting `cycle 3` away would defeat statements about cycles. -/
theorem cycle_three : cycle 3 = complete 3 :=
  Quotient.sound ⟨CGraph.isoOfAdj (Equiv.refl _) (by decide)⟩

/-- The 5-cycle is self-complementary. -/
@[simp] theorem compl_cycle_five : (cycle 5)ᶜ = cycle 5 := by
  rw [cycle_def, compl_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩ : Equiv.Perm (Fin 5))
    (by decide)⟩

/-- The path on four vertices is self-complementary. -/
@[simp] theorem compl_path_four : (path 4)ᶜ = path 4 := by
  rw [path_def, compl_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4))
    (by decide)⟩

/-! ## Bipartite, star, wheel -/

theorem bipartite_eq_join (m n : ℕ) : bipartite m n = empty m ∇g empty n := by
  rw [join_def, compl_empty, compl_empty, bipartite_eq_compl]

@[simp] theorem join_empty_zero (G : IsoGraph) : G ∇g empty 0 = G := by
  rw [join_def, compl_empty, complete_zero, disjUnion_empty_zero, compl_compl]

@[simp] theorem empty_zero_join (G : IsoGraph) : empty 0 ∇g G = G := by
  rw [join_comm, join_empty_zero]

@[simp] theorem join_complete (m n : ℕ) : complete m ∇g complete n = complete (m + n) := by
  rw [join_def, compl_complete, compl_complete, disjUnion_empty, compl_empty]

@[simp] theorem bipartite_zero_right (m : ℕ) : bipartite m 0 = empty m := by
  rw [bipartite_eq_join, join_empty_zero]

@[simp] theorem bipartite_zero_left (n : ℕ) : bipartite 0 n = empty n := by
  rw [bipartite_eq_join, empty_zero_join]

theorem bipartite_one_one : bipartite 1 1 = complete 2 := by
  rw [bipartite_eq_join, ← complete_one, join_complete]

@[simp] theorem star_zero : star 0 = empty 1 := by
  rw [star_eq_bipartite, bipartite_zero_right]

theorem star_one : star 1 = complete 2 := by
  rw [star_eq_bipartite, bipartite_one_one]

/-- The complement of a star is its centre, isolated, next to a clique on the leaves. -/
theorem compl_star (n : ℕ) : (star n)ᶜ = empty 1 ⊕g complete n := by
  rw [star_eq_bipartite, compl_bipartite, complete_one]

/-- `K_{2,2}` is the square. -/
theorem bipartite_two_two : bipartite 2 2 = cycle 4 := by
  rw [bipartite_def, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.bipartite 2 2) (H := CGraph.cycle 4)
    (⟨Sum.elim ![0, 2] ![1, 3], ![.inl 0, .inr 0, .inl 1, .inr 1], by decide, by decide⟩ :
      (Fin 2 ⊕ Fin 2) ≃ Fin 4)
    (by decide)⟩

/-- The complement of the square is a perfect matching. -/
@[simp] theorem compl_cycle_four : (cycle 4)ᶜ = complete 2 ⊕g complete 2 := by
  rw [← bipartite_two_two, compl_bipartite]

@[simp] theorem wheel_zero : wheel 0 = empty 1 := by
  rw [wheel_eq_join, cycle_zero, join_empty_zero, complete_one]

theorem wheel_one : wheel 1 = complete 2 := by
  rw [wheel_eq_join, cycle_one, ← complete_one, join_complete]

theorem wheel_two : wheel 2 = complete 3 := by
  rw [wheel_eq_join, cycle_two, join_complete]

theorem wheel_three : wheel 3 = complete 4 := by
  rw [wheel_eq_join, cycle_three, join_complete]

/-- The hub of a wheel is joined to everything, so it is isolated in the complement. -/
theorem compl_wheel (n : ℕ) : (wheel n)ᶜ = empty 1 ⊕g (cycle n)ᶜ := by
  rw [wheel_eq_join, compl_join, compl_complete]

/-- Likewise for the fan, which is a hub joined to a path rather than a cycle. -/
theorem compl_fan (n : ℕ) : (fan n)ᶜ = empty 1 ⊕g (path n)ᶜ := by
  show (complete 1 ∇g path n)ᶜ = _
  rw [compl_join, compl_complete]

/-! ## Complete multipartite graphs

A single part is an independent set, and `cocktailParty 1` is that case; two singleton parts and
one part of size `n` is the book `B_n`, whose first two members are complete.

The workhorse is `completeMultipartite_cons`: peeling the first part off turns the dependent
`Σ i : Fin ds.length, _` vertex type into a `Sum`, so the whole family becomes reachable by
`join`-level rewriting.  Everything after it — the append rule, `[a, b] = bipartite a b`,
`cocktailParty 2 = cycle 4`, the vertex count — is a consequence. -/

@[simp] theorem completeMultipartite_nil : completeMultipartite [] = empty 0 := by
  rw [completeMultipartite_def,
    mk_eq_empty (G := CGraph.completeMultipartite []) (by decide)]
  simp

/-- One part: no edges at all. -/
@[simp] theorem completeMultipartite_singleton (n : ℕ) : completeMultipartite [n] = empty n := by
  have h : ∀ x y : (CGraph.completeMultipartite [n]).V,
      (CGraph.completeMultipartite [n]).Adj x y = false := by
    haveI : Subsingleton (Fin [n].length) := inferInstanceAs (Subsingleton (Fin 1))
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain rfl : i = j := Subsingleton.elim i j
    show (CGraph.compl (CGraph.sigmaUnion
      fun i : Fin [n].length ↦ CGraph.complete ([n].get i))).Adj ⟨i, a⟩ ⟨i, b⟩ = false
    rw [CGraph.compl_adj, CGraph.sigmaUnion_adj_mk, CGraph.complete_adj]
    by_cases hab : a = b <;> simp [hab]
  rw [completeMultipartite_def, mk_eq_empty h]
  simp

@[simp] theorem cocktailParty_one : cocktailParty 1 = empty 2 :=
  completeMultipartite_singleton 2

theorem book_zero : book 0 = complete 2 := by
  show completeMultipartite [1, 1, 0] = complete 2
  rw [completeMultipartite_def,
    mk_eq_complete (G := CGraph.completeMultipartite [1, 1, 0]) (by decide)]
  simp

theorem book_one : book 1 = complete 3 := by
  show completeMultipartite [1, 1, 1] = complete 3
  rw [completeMultipartite_def,
    mk_eq_complete (G := CGraph.completeMultipartite [1, 1, 1]) (by decide)]
  simp

/-- Peeling off the first part: the rest of the multipartite graph, joined to an independent
set of the first part's size. -/
theorem completeMultipartite_cons (d : ℕ) (ds : List ℕ) :
    completeMultipartite (d :: ds) = empty d ∇g completeMultipartite ds := by
  have h : (⟦CGraph.sigmaUnion fun i : Fin (d :: ds).length ↦ CGraph.complete ((d :: ds).get i)⟧ :
      IsoGraph)
      = disjUnion ⟦CGraph.complete d⟧
        ⟦CGraph.sigmaUnion fun i : Fin ds.length ↦ CGraph.complete (ds.get i)⟧ := by
    rw [disjUnion_mk]
    exact Quotient.sound
      ⟨CGraph.Iso.sigmaUnionSucc fun i : Fin (d :: ds).length ↦ CGraph.complete ((d :: ds).get i)⟩
  show (⟦CGraph.compl (CGraph.sigmaUnion
      fun i : Fin (d :: ds).length ↦ CGraph.complete ((d :: ds).get i))⟧ : IsoGraph) = _
  rw [← compl_mk, h, compl_disjUnion, ← complete_def, compl_complete, compl_mk]
  rfl

@[simp] theorem completeMultipartite_zero_cons (ds : List ℕ) :
    completeMultipartite (0 :: ds) = completeMultipartite ds := by
  rw [completeMultipartite_cons, empty_zero_join]

theorem completeMultipartite_append (ds es : List ℕ) :
    completeMultipartite (ds ++ es)
      = completeMultipartite ds ∇g completeMultipartite es := by
  induction ds with
  | nil => rw [List.nil_append, completeMultipartite_nil, empty_zero_join]
  | cons d ds ih =>
    rw [List.cons_append, completeMultipartite_cons, ih, completeMultipartite_cons, join_assoc]

theorem compl_completeMultipartite_cons (d : ℕ) (ds : List ℕ) :
    (completeMultipartite (d :: ds))ᶜ
      = complete d ⊕g (completeMultipartite ds)ᶜ := by
  rw [completeMultipartite_cons, compl_join, compl_empty]

theorem completeMultipartite_pair (a b : ℕ) : completeMultipartite [a, b] = bipartite a b := by
  rw [completeMultipartite_cons, completeMultipartite_singleton, bipartite_eq_join]

theorem star_eq_completeMultipartite (n : ℕ) : star n = completeMultipartite [1, n] := by
  rw [completeMultipartite_pair, star_eq_bipartite]

theorem completeMultipartite_replicate_one (n : ℕ) :
    completeMultipartite (List.replicate n 1) = complete n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, completeMultipartite_cons, ih, ← complete_one, join_complete,
      Nat.add_comm]

@[simp] theorem V_completeMultipartite (ds : List ℕ) : (completeMultipartite ds).V = ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => rw [completeMultipartite_cons, V_join, V_empty, ih, List.sum_cons]

@[simp] theorem cocktailParty_two : cocktailParty 2 = cycle 4 := by
  show completeMultipartite [2, 2] = cycle 4
  rw [completeMultipartite_pair, bipartite_two_two]

theorem book_eq_join (n : ℕ) : book n = complete 2 ∇g empty n := by
  show completeMultipartite [1, 1, n] = _
  rw [completeMultipartite_cons, completeMultipartite_pair, bipartite_eq_join, ← join_assoc,
    ← bipartite_eq_join, bipartite_one_one]

/-- The complement of the book `B_n` is its spine, edgeless, next to a clique on the pages. -/
theorem compl_book (n : ℕ) : (book n)ᶜ = empty 2 ⊕g complete n := by
  rw [book_eq_join, compl_join, compl_complete, compl_empty]

/-! ## Circulants

`CGraph.circulant_one_eq_cycle` is an equality of `CGraph`s already, so these are one-liners. -/

@[simp] theorem circulant_nil (n : ℕ) : circulant n [] = empty n := by
  rw [circulant_def, CGraph.circulant_nil, empty_def]

@[simp] theorem circulant_one (n : ℕ) : circulant n [1] = cycle n := by
  rw [circulant_def, CGraph.circulant_one_eq_cycle, cycle_def]

attribute [simp] IsoGraph.circulant_zero_cons IsoGraph.circulant_dup_cons

/-- The step `n - 1` runs around the cycle backwards. -/
theorem circulant_pred (n : ℕ) (hn : 1 ≤ n) : circulant n [n - 1] = cycle n := by
  rw [← circulant_neg_cons n 1 hn [], circulant_one]

/-- The cycle written with the symmetric connection set `{±1}`. -/
theorem circulant_one_pred (n : ℕ) (hn : 1 ≤ n) : circulant n [1, n - 1] = cycle n := by
  rw [circulant_neg_cons n 1 hn [n - 1], circulant_dup_cons, circulant_pred n hn]

/-- **A perfect matching, as a circulant.**  `circulant (2m) {m}` joins `i` to `i + m` and to
nothing else, so it is `m` disjoint edges — the Cartesian product of an edgeless graph with `K₂`.
-/
theorem circulant_matching (m : ℕ) :
    circulant (2 * (m + 1)) [m + 1] = empty (m + 1) □g complete 2 := by
  rw [circulant_def, empty_def, complete_def, cartesianProduct_mk]
  exact Quotient.sound ⟨(CGraph.Iso.circulantMatching m).symm⟩

/-- The `m = 0` case of both readings: one edge. -/
theorem circulant_two_one : circulant 2 [1] = complete 2 := by
  rw [circulant_one, cycle_two]

/-! ## Paley graphs -/

/-- **Paley graphs are self-complementary**, because multiplication by a non-residue exchanges
the squares with the non-squares.  The general statement needs the multiplicative structure of
`GF(q)`; these two are the witnesses `x ↦ 2x` mod `13` and `x ↦ 3x` mod `17`. -/
@[simp] theorem compl_paley_thirteen : (paley 13)ᶜ = paley 13 := by
  rw [paley_def, compl_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleyThirteenIso.symm⟩

@[simp] theorem compl_paley_seventeen : (paley 17)ᶜ = paley 17 := by
  rw [paley_def, compl_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleySeventeenIso.symm⟩

/-- **`paley 9` is not the Paley graph of order 9.**  `CGraph.paley` reads its differences in
`ZMod q`, which is a field only for prime `q`; at `q = 9` the squares are `{0, 1, 4, 7}`, so the
graph joins `x` to `y` exactly when `x - y` is not a multiple of `3` and one gets the complete
tripartite graph `K₃,₃,₃` rather than the rook's graph `R(3, 3)` that `GF(9)` would give. -/
theorem compl_paley_nine :
    (paley 9)ᶜ = complete 3 ⊕g (complete 3 ⊕g complete 3) := by
  rw [paley_def, compl_mk, complete_def, disjUnion_mk, disjUnion_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleyNineIso.symm⟩

theorem paley_nine : paley 9 = completeMultipartite [3, 3, 3] := by
  have h : (completeMultipartite [3, 3, 3])ᶜ
      = complete 3 ⊕g (complete 3 ⊕g complete 3) := by
    rw [compl_completeMultipartite_cons, compl_completeMultipartite_cons,
      compl_completeMultipartite_cons, completeMultipartite_nil, compl_empty, complete_zero,
      disjUnion_empty_zero]
  rw [← compl_compl (paley 9), compl_paley_nine, ← h, compl_compl]

/-! ## Kneser and Johnson graphs

The degenerate parameters.  `kneser n k` and `johnson n k` both have
`{s : Finset (Fin n) // s.card = k}` for a vertex type, of size `n.choose k`; for `k = 0` there is
one vertex, for `k = 1` the vertices are the points of `Fin n` and both graphs are complete, and
once `n < 2 * k` no two `k`-sets are disjoint so the Kneser graph has no edges at all. -/

@[simp] theorem kneser_zero (n : ℕ) : kneser n 0 = empty 1 := by
  have h : ∀ s t : (CGraph.kneser n 0).V, (CGraph.kneser n 0).Adj s t = false := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    have hst : s = t := by rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht]
    cases hst
    simp
  rw [kneser_def, mk_eq_empty h]
  simp

@[simp] theorem kneser_one (n : ℕ) : kneser n 1 = complete n := by
  have h : ∀ s t : (CGraph.kneser n 1).V, s ≠ t → (CGraph.kneser n 1).Adj s t = true := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ht
    have hab : a ≠ b := by rintro rfl; exact hne rfl
    simp [hne, Finset.singleton_inter_of_notMem, hab]
  rw [kneser_def, mk_eq_complete h]
  simp

/-- Once `n < 2 * k` there are no two disjoint `k`-subsets of `Fin n`, so the Kneser graph is
edgeless. -/
theorem kneser_eq_empty (n k : ℕ) (hn : n < 2 * k) : kneser n k = empty (n.choose k) := by
  have h : ∀ s t : (CGraph.kneser n k).V, (CGraph.kneser n k).Adj s t = false := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    rw [CGraph.kneser_adj]
    rcases Bool.eq_false_or_eq_true (decide (s ∩ t = ∅)) with hd | hd
    · exfalso
      have hdisj : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.2 (of_decide_eq_true hd)
      have hcard : (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint hdisj
      have hle : (s ∪ t).card ≤ n := by simpa using Finset.card_le_univ (s ∪ t)
      omega
    · simp [hd]
  rw [kneser_def, mk_eq_empty h]
  simp

@[simp] theorem johnson_zero (n : ℕ) : johnson n 0 = empty 1 := by
  have h : ∀ s t : (CGraph.johnson n 0).V, (CGraph.johnson n 0).Adj s t = false := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    have hst : s = t := by rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht]
    cases hst
    simp
  rw [johnson_def, mk_eq_empty h]
  simp

@[simp] theorem johnson_one (n : ℕ) : johnson n 1 = complete n := by
  have h : ∀ s t : (CGraph.johnson n 1).V, s ≠ t → (CGraph.johnson n 1).Adj s t = true := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ht
    have hab : a ≠ b := by rintro rfl; exact hne rfl
    simp [hne, Finset.singleton_inter_of_notMem, hab]
  rw [johnson_def, mk_eq_complete h]
  simp

/-- There is only one `n`-subset of `Fin n`. -/
@[simp] theorem kneser_self (n : ℕ) : kneser n n = empty 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact kneser_zero 0
  · rw [kneser_eq_empty n n (by omega), Nat.choose_self]

@[simp] theorem johnson_self (n : ℕ) : johnson n n = empty 1 := by
  have h : ∀ s t : (CGraph.johnson n n).V, (CGraph.johnson n n).Adj s t = false := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    have hst : s = t := by
      rw [Finset.eq_univ_of_card s (by simpa using hs),
        Finset.eq_univ_of_card t (by simpa using ht)]
    cases hst
    simp
  rw [johnson_def, mk_eq_empty h]
  simp

/-- **`J(n, k) = J(n, n - k)`**: taking complements is an isomorphism of Johnson graphs.  It is
not a `simp` lemma — it would rewrite forever. -/
theorem johnson_compl (n k : ℕ) (hk : k ≤ n) : johnson n k = johnson n (n - k) := by
  rw [johnson_def, johnson_def]
  exact Quotient.sound ⟨CGraph.Iso.johnsonCompl n k hk⟩

/-- The other end of `johnson_one`: the `n`-subsets of an `(n+1)`-set also form a clique. -/
@[simp] theorem johnson_pred (n : ℕ) : johnson (n + 1) n = complete (n + 1) := by
  rw [johnson_compl (n + 1) n (by omega), show n + 1 - n = 1 from by omega, johnson_one]

/-- One step further down: the `n`-subsets of an `(n+2)`-set form a triangular graph. -/
theorem johnson_sub_two (n : ℕ) : johnson (n + 2) n = triangular (n + 2) := by
  rw [johnson_compl (n + 2) n (by omega), show n + 2 - n = 2 from by omega]

/-- The triangular graph is the complement of the Petersen-style Kneser graph on 2-sets. -/
theorem triangular_eq_compl_kneser (n : ℕ) : triangular n = (kneser n 2)ᶜ := by
  rw [kneser_def, compl_mk]
  exact Quotient.sound ⟨CGraph.johnsonTwoIso n⟩

/-- Any two of the three 2-subsets of `Fin 3` meet, so `T(3) = K₃`. -/
theorem triangular_three : triangular 3 = complete 3 := by
  show johnson 3 2 = complete 3
  rw [johnson_def, mk_eq_complete (G := CGraph.johnson 3 2) (by decide)]
  simp

/-- The three ways to split `{0, 1, 2, 3}` into two pairs. -/
private def kneserFourTwoMap : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → (CGraph.kneser 4 2).V
  | .inl 0 => ⟨{0, 1}, by decide⟩
  | .inl 1 => ⟨{2, 3}, by decide⟩
  | .inr (.inl 0) => ⟨{0, 2}, by decide⟩
  | .inr (.inl 1) => ⟨{1, 3}, by decide⟩
  | .inr (.inr 0) => ⟨{0, 3}, by decide⟩
  | .inr (.inr 1) => ⟨{1, 2}, by decide⟩

theorem kneser_four_two :
    kneser 4 2 = complete 2 ⊕g (complete 2 ⊕g complete 2) := by
  rw [kneser_def, complete_def, disjUnion_mk, disjUnion_mk]
  symm
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.disjUnion (CGraph.complete 2)
      (CGraph.disjUnion (CGraph.complete 2) (CGraph.complete 2)))
    (H := CGraph.kneser 4 2)
    (Equiv.ofBijective kneserFourTwoMap (by decide)) (by decide)⟩

theorem triangular_four : triangular 4 = cocktailParty 3 := by
  have h : (cocktailParty 3)ᶜ
      = complete 2 ⊕g (complete 2 ⊕g complete 2) := by
    show (completeMultipartite [2, 2, 2])ᶜ = _
    rw [compl_completeMultipartite_cons, compl_completeMultipartite_cons,
      compl_completeMultipartite_cons, completeMultipartite_nil, compl_empty, complete_zero,
      disjUnion_empty_zero]
  rw [triangular_eq_compl_kneser, kneser_four_two, ← h, compl_compl]

/-! ## Hypercubes -/

@[simp] theorem hypercube_zero : hypercube 0 = empty 1 := by
  rw [hypercube_def, mk_eq_empty (G := CGraph.hypercube 0) (by decide)]
  simp

@[simp] theorem hypercube_one : hypercube 1 = complete 2 := by
  rw [hypercube_def, mk_eq_complete (G := CGraph.hypercube 1) (by decide)]
  simp

/-- The square is the two-dimensional cube. -/
theorem hypercube_two : hypercube 2 = cycle 4 := by
  rw [hypercube_def, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.hypercube 2) (H := CGraph.cycle 4)
    (⟨fun x ↦ if x 0 then (if x 1 then 2 else 1) else (if x 1 then 3 else 0),
      ![![false, false], ![true, false], ![true, true], ![false, true]],
      by decide, by decide⟩ : (Fin 2 → Bool) ≃ Fin 4)
    (by decide)⟩

/-- **`Q_{n+1} = Q_n □ K₂`**, the recursion `CGraph.hypercube` is written to avoid: splitting a
bit-string of length `n + 1` into its first bit and the rest turns "differ in exactly one place"
into the cartesian product's "agree on one side and differ on the other".  `CGraph.card_ne_succ`
does the counting. -/
theorem hypercube_succ (n : ℕ) :
    hypercube (n + 1) = hypercube n □g complete 2 := by
  rw [hypercube_def, hypercube_def n, complete_def, cartesianProduct_mk]
  refine Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.hypercube (n + 1))
    (H := CGraph.cartesianProduct (CGraph.hypercube n) (CGraph.complete 2))
    (⟨fun x ↦ (fun i ↦ x i.succ, if x 0 then 1 else 0),
      fun p ↦ Fin.cons (decide (p.2 = 1)) p.1,
      fun x ↦ by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · cases hx : x 0 <;> simp [hx]
        · simp,
      fun p ↦ by
        obtain ⟨f, k⟩ := p
        refine Prod.ext ?_ ?_
        · funext i; simp
        · fin_cases k <;> simp⟩ : (Fin (n + 1) → Bool) ≃ ((Fin n → Bool) × Fin 2))
    fun x y ↦ ?_⟩
  show ((decide ((fun i : Fin n ↦ x i.succ) = fun i : Fin n ↦ y i.succ) &&
      (CGraph.complete 2).Adj ((if x 0 then 1 else 0 : Fin 2))
        ((if y 0 then 1 else 0 : Fin 2))) ||
      ((CGraph.hypercube n).Adj (fun i : Fin n ↦ x i.succ) (fun i : Fin n ↦ y i.succ) &&
        decide (((if x 0 then 1 else 0 : Fin 2)) = (if y 0 then 1 else 0 : Fin 2)))) =
    (CGraph.hypercube (n + 1)).Adj x y
  rw [CGraph.hypercube_adj, CGraph.hypercube_adj, CGraph.complete_adj, CGraph.card_ne_succ]
  have hfun : decide ((fun i : Fin n ↦ x i.succ) = fun i : Fin n ↦ y i.succ)
      = decide ((Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card = 0) :=
    decide_eq_decide.2 (by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
      simp)
  rw [hfun]
  generalize (Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card = s
  cases hx0 : x 0 <;> cases hy0 : y 0 <;> cases s <;> simp

/-! ## Folded cubes

`foldedCube n` joins each pair of antipodal vertices of `Q_n`.  For `n ≤ 2` every pair of distinct
bit-strings differs in one place or in all of them, so the graph is complete; at `n = 3` the four
new edges make each vertex adjacent to the whole opposite parity class. -/

@[simp] theorem foldedCube_zero : foldedCube 0 = empty 1 := by
  rw [foldedCube_def, mk_eq_empty (G := CGraph.foldedCube 0) (by decide)]
  simp

@[simp] theorem foldedCube_one : foldedCube 1 = complete 2 := by
  rw [foldedCube_def, mk_eq_complete (G := CGraph.foldedCube 1) (by decide)]
  simp

theorem foldedCube_two : foldedCube 2 = complete 4 := by
  rw [foldedCube_def, mk_eq_complete (G := CGraph.foldedCube 2) (by decide)]
  simp

/-- Antipodal bit-strings of odd length have opposite parity, so every edge of `foldedCube 3`
crosses the parity classes — and each of its 4-regular vertices meets all four vertices on the
other side. -/
theorem foldedCube_three : foldedCube 3 = bipartite 4 4 := by
  rw [foldedCube_def, bipartite_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.foldedCube 3) (H := CGraph.bipartite 4 4)
    (⟨fun x ↦ if xor (xor (x 0) (x 1)) (x 2) then
          .inr (if x 1 then (if x 2 then 3 else 2) else (if x 2 then 1 else 0))
        else .inl (if x 1 then (if x 2 then 3 else 2) else (if x 2 then 1 else 0)),
      Sum.elim
        ![![false, false, false], ![true, false, true], ![true, true, false], ![false, true, true]]
        ![![true, false, false], ![false, false, true], ![false, true, false], ![true, true, true]],
      by decide, by decide⟩ : (Fin 3 → Bool) ≃ (Fin 4 ⊕ Fin 4))
    (by decide)⟩

/-! ## Decorated cycles and trees

The `ofEdges`-based families — tadpoles, lollipops, spiders and cycles with pendant vertices —
degenerate into the named families when one of their parameters vanishes.  Every one of these is
already an equality of `CGraph`s (see the `CGraph` section above), and so descends to the
quotient. -/

/-- On two or three vertices a clique is a cycle, so the lollipop and the tadpole coincide.  Which
side is the normal form is a matter of taste, so neither of these is a `simp` lemma. -/
theorem lollipop_two_eq_tadpole (k : ℕ) : lollipop 2 k = tadpole 2 k := by
  rw [lollipop_def, tadpole_def, CGraph.lollipop_two]

theorem lollipop_three_eq_tadpole (k : ℕ) : lollipop 3 k = tadpole 3 k := by
  rw [lollipop_def, tadpole_def, CGraph.lollipop_three]

attribute [simp] IsoGraph.spider_zero_cons

/-- Two adjacent legs of a spider may be exchanged. -/
theorem spider_swap (pre post : List ℕ) (a b : ℕ) :
    spider (pre ++ a :: b :: post) = spider (pre ++ b :: a :: post) := by
  have hsum : (pre ++ b :: a :: post).sum = (pre ++ a :: b :: post).sum := by
    simp only [List.sum_append, List.sum_cons]; omega
  have hL : CGraph.spiderEdges 1 (pre ++ a :: b :: post)
      = CGraph.spiderEdges 1 pre ++ (CGraph.legEdges 0 (1 + pre.sum) a ++
          (CGraph.legEdges 0 (1 + pre.sum + a) b ++
            CGraph.spiderEdges (1 + pre.sum + a + b) post)) := by
    rw [CGraph.spiderEdges_append, CGraph.spiderEdges, CGraph.spiderEdges]
  have hR : CGraph.spiderEdges 1 (pre ++ b :: a :: post)
      = CGraph.spiderEdges 1 pre ++ (CGraph.legEdges 0 (1 + pre.sum) b ++
          (CGraph.legEdges 0 (1 + pre.sum + b) a ++
            CGraph.spiderEdges (1 + pre.sum + a + b) post)) := by
    rw [CGraph.spiderEdges_append, CGraph.spiderEdges, CGraph.spiderEdges,
      show 1 + pre.sum + b + a = 1 + pre.sum + a + b from by omega]
  rw [spider_def, spider_def, CGraph.spider, CGraph.spider, hsum, hL, hR]
  refine Quotient.sound (CGraph.nonempty_iso_ofEdges_swap_legs _ (1 + pre.sum) a b _ _
    (by omega) ?_ ?_ ?_)
  · simp only [List.sum_append, List.sum_cons]
    omega
  · intro p q h
    have := CGraph.mem_spiderEdges_bound 1 pre p q h
    omega
  · intro p q h
    have := CGraph.mem_spiderEdges_bound (1 + pre.sum + a + b) post p q h
    omega

/-- The spider depends only on the multiset of its leg lengths. -/
theorem spider_perm_append {ks ls : List ℕ} (h : ks.Perm ls) :
    ∀ pre : List ℕ, spider (pre ++ ks) = spider (pre ++ ls) := by
  induction h with
  | nil => intro pre; rfl
  | cons x _ ih =>
      intro pre
      simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [x])
  | swap x y l => intro pre; exact spider_swap pre l y x
  | trans _ _ ih1 ih2 => intro pre; exact (ih1 pre).trans (ih2 pre)

theorem spider_perm {ks ls : List ℕ} (h : ks.Perm ls) : spider ks = spider ls := by
  simpa using spider_perm_append h []

attribute [simp] IsoGraph.cyclePendant_append_zero IsoGraph.thetaGraph_zero_zero_cons

/-! ## Decorated cycles and trees, up to isomorphism

Unlike the identities just above, these are not equalities of `CGraph`s: both sides are the same
graph drawn with a different numbering of the vertices, so each one carries an explicit
relabelling (`CGraph.foldAt`, `CGraph.rotTail`, `CGraph.swapZeroOne`, `finSumFinEquiv`). -/

@[simp] theorem spider_pair (a b : ℕ) : spider [a, b] = path (1 + a + b) := by
  rw [spider_def, path_def]
  have hN : (1 : ℕ) + ([a, b] : List ℕ).sum = 1 + a + b := by simp [Nat.add_assoc]
  have hes : CGraph.spiderEdges 1 [a, b]
      = CGraph.legEdges 0 1 a ++ CGraph.legEdges 0 (1 + a) b := by
    simp [CGraph.spiderEdges]
  set E : (CGraph.spider [a, b]).V ≃ (CGraph.path (1 + a + b)).V :=
    (finCongr hN).trans (CGraph.foldAt a (1 + a + b) (by omega)) with hE
  refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
  intro x y
  have hEz : ∀ z : (CGraph.spider [a, b]).V, (E z).1 = if z.1 ≤ a then a - z.1 else z.1 := by
    intro z; rw [hE]; rfl
  have hx : x.1 < 1 + a + b := hN ▸ x.isLt
  have hy : y.1 < 1 + a + b := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hEz x, hEz y]
  simp only [CGraph.spider]
  rw [CGraph.ofEdges_adj_val, hes]
  simp only [List.mem_append, CGraph.mem_legEdges]
  exact CGraph.foldAt_pair_iff a b x.1 y.1 hx hy

attribute [simp] IsoGraph.thetaGraph_nil IsoGraph.thetaGraph_replicate_zero

/-- A theta graph with a single path is a path. -/
@[simp] theorem thetaGraph_singleton (k : ℕ) : thetaGraph [k] = path (k + 2) := by
  rcases k with _ | k
  · exact thetaGraph_replicate_zero 0 |>.trans (path_two).symm
  rw [thetaGraph_def, path_def]
  have hN : 2 + ([k + 1] : List ℕ).sum = k + 3 := by simp; omega
  set E : (CGraph.thetaGraph [k + 1]).V ≃ (CGraph.path (k + 1 + 2)).V :=
    (finCongr hN).trans (CGraph.rotTail (k + 3)) with hE
  refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
  intro x y
  have hEz : ∀ z : (CGraph.thetaGraph [k + 1]).V,
      (E z).1 = if z.1 = 0 then 0 else if z.1 = 1 then k + 2 else z.1 - 1 := fun _ ↦ rfl
  have hx : x.1 < k + 3 := hN ▸ x.isLt
  have hy : y.1 < k + 3 := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hEz x, hEz y]
  simp only [CGraph.thetaGraph]
  rw [CGraph.ofEdges_adj_val]
  simp only [CGraph.mem_thetaEdges_singleton]
  exact CGraph.rotTail_pair_iff k x.1 y.1 hx hy

@[simp] theorem spider_replicate_one (n : ℕ) : spider (List.replicate n 1) = star n := by
  rw [spider_def, star_def]
  have hN : (1 : ℕ) + (List.replicate n 1).sum = 1 + n := by simp
  have key : (⟦CGraph.star n⟧ : IsoGraph) = ⟦CGraph.spider (List.replicate n 1)⟧ := by
    set E : (CGraph.star n).V ≃ (CGraph.spider (List.replicate n 1)).V :=
      (finSumFinEquiv (m := 1) (n := n)).trans (finCongr hN.symm) with hE
    refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete n).V, (E (Sum.inr b)).1 = 1 + b.1 := fun _ ↦ rfl
    have hsp : ∀ u v : (CGraph.spider (List.replicate n 1)).V,
        ((CGraph.spider (List.replicate n 1)).Adj u v = true ↔
          (u.1 ≠ v.1 ∧ ((u.1 = 0 ∧ 1 ≤ v.1 ∧ v.1 < 1 + n) ∨
            (v.1 = 0 ∧ 1 ≤ u.1 ∧ u.1 < 1 + n)))) := by
      intro u v
      simp only [CGraph.spider]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_spiderEdges_replicate_one]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hsp]
    · -- both are the centre, and `Fin 1` is a subsingleton
      rw [hl a, hl b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega
  exact key.symm

/-- Every spider all of whose legs have length one is a star. -/
theorem spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) : spider ks = star ks.length := by
  obtain ⟨n, rfl⟩ : ∃ n, ks = List.replicate n 1 := ⟨ks.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
  rw [spider_replicate_one, List.length_replicate]

/-- A single vertex carrying `k` pendant vertices is the star `K_{1,k}`. -/
@[simp] theorem cyclePendant_one (k : ℕ) : cyclePendant 1 [k] = star k := by
  rw [cyclePendant_def, CGraph.cyclePendant_one_eq_spider, ← spider_def, spider_replicate_one]

/-- The star with two leaves is the path on three vertices. -/
theorem star_two : star 2 = path 3 := by
  rw [← spider_replicate_one 2, show List.replicate 2 1 = [1, 1] from rfl, spider_pair]

/-- A double star with no leaves on the second centre is a star. -/
@[simp] theorem doubleStar_right_zero (m : ℕ) : doubleStar m 0 = star (m + 1) := by
  rw [doubleStar_def, star_def]
  have hN : 1 + (m + 1) = 2 + m + 0 := by omega
  have key : (⟦CGraph.star (m + 1)⟧ : IsoGraph) = ⟦CGraph.doubleStar m 0⟧ := by
    set E : (CGraph.star (m + 1)).V ≃ (CGraph.doubleStar m 0).V :=
      (finSumFinEquiv (m := 1) (n := m + 1)).trans (finCongr hN) with hE
    refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete (m + 1)).V, (E (Sum.inr b)).1 = 1 + b.1 := fun _ ↦ rfl
    have hds : ∀ u v : (CGraph.doubleStar m 0).V,
        ((CGraph.doubleStar m 0).Adj u v = true ↔
          (u.1 ≠ v.1 ∧
            (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
                (u.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + 0)) ∨
              ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + m) ∨
                (v.1 = 1 ∧ 2 + m ≤ u.1 ∧ u.1 < 2 + m + 0))))) := by
      intro u v
      simp only [CGraph.doubleStar]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_doubleStarEdges]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hds]
    · rw [hl a, hl b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < m + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < m + 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < m + 1 := a.isLt
      have hb : b.1 < m + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega
  exact key.symm

/-- A double star with no leaves on the first centre is a star. -/
@[simp] theorem doubleStar_left_zero (n : ℕ) : doubleStar 0 n = star (n + 1) := by
  rw [doubleStar_def, star_def]
  have hN : 1 + (n + 1) = 2 + 0 + n := by omega
  have key : (⟦CGraph.star (n + 1)⟧ : IsoGraph) = ⟦CGraph.doubleStar 0 n⟧ := by
    set E : (CGraph.star (n + 1)).V ≃ (CGraph.doubleStar 0 n).V :=
      ((finSumFinEquiv (m := 1) (n := n + 1)).trans (finCongr hN)).trans
        (CGraph.swapZeroOne (2 + 0 + n) (by omega)) with hE
    refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = 1 := by
      intro a
      have ha : a.1 = 0 := Nat.lt_one_iff.mp a.isLt
      show (if a.1 = 0 then 1 else if a.1 = 1 then 0 else a.1) = 1
      rw [if_pos ha]
    have hr : ∀ b : (CGraph.complete (n + 1)).V,
        (E (Sum.inr b)).1 = if b.1 = 0 then 0 else 1 + b.1 := by
      intro b
      show (if 1 + b.1 = 0 then 1 else if 1 + b.1 = 1 then 0 else 1 + b.1)
        = if b.1 = 0 then 0 else 1 + b.1
      split_ifs <;> omega
    have hds : ∀ u v : (CGraph.doubleStar 0 n).V,
        ((CGraph.doubleStar 0 n).Adj u v = true ↔
          (u.1 ≠ v.1 ∧
            (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + 0) ∨
                (u.1 = 1 ∧ 2 + 0 ≤ v.1 ∧ v.1 < 2 + 0 + n)) ∨
              ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + 0) ∨
                (v.1 = 1 ∧ 2 + 0 ≤ u.1 ∧ u.1 < 2 + 0 + n))))) := by
      intro u v
      simp only [CGraph.doubleStar]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_doubleStarEdges]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hds]
    · rw [hl a, hl b]
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have hb : b.1 < n + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · rw [if_pos hb0]
        simp
      · rw [if_neg (by omega : ¬ b.1 = 0)]
        simp only [true_and, and_true]
        omega
    · rw [hr a, hl b]
      have ha : a.1 < n + 1 := a.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      rcases Nat.eq_zero_or_pos a.1 with ha0 | ha0
      · rw [if_pos ha0]
        simp
      · rw [if_neg (by omega : ¬ a.1 = 0)]
        simp only [true_and, and_true]
        omega
    · rw [hr a, hr b]
      have ha : a.1 < n + 1 := a.isLt
      have hb : b.1 < n + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      rcases Nat.eq_zero_or_pos a.1 with ha0 | ha0 <;>
        rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · rw [if_pos ha0, if_pos hb0]
        simp only [true_and]
        omega
      · rw [if_pos ha0, if_neg (by omega : ¬ b.1 = 0)]
        simp only [true_and]
        omega
      · rw [if_neg (by omega : ¬ a.1 = 0), if_pos hb0]
        simp only [true_and]
        omega
      · rw [if_neg (by omega : ¬ a.1 = 0), if_neg (by omega : ¬ b.1 = 0)]
        omega
  exact key.symm

attribute [simp] IsoGraph.cyclePendant_singleton_one

/-- A theta graph with two paths is a cycle. -/
@[simp] theorem thetaGraph_pair (a b : ℕ) : thetaGraph [a, b] = cycle (2 + a + b) := by
  rw [thetaGraph_def, cycle_def]
  have hN : 2 + ([a, b] : List ℕ).sum = 2 + a + b := by simp; omega
  set E : (CGraph.thetaGraph [a, b]).V ≃ (CGraph.cycle (2 + a + b)).V :=
    (finCongr hN).trans (CGraph.thetaCyclePerm a b) with hE
  refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
  intro x y
  have hEz : ∀ z : (CGraph.thetaGraph [a, b]).V,
      (E z).1 = CGraph.thetaCycleFwd a b z.1 := fun _ ↦ rfl
  have hx : x.1 < 2 + a + b := hN ▸ x.isLt
  have hy : y.1 < 2 + a + b := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.cycle_adj_val, hEz x, hEz y]
  simp only [CGraph.thetaGraph]
  rw [CGraph.ofEdges_adj_val,
    show CGraph.thetaEdges 2 [a, b] = CGraph.thetaEdges 2 [a] ++ CGraph.thetaEdges (2 + a) [b] from
      CGraph.thetaEdges_cons 2 a [b]]
  simp only [List.mem_append]
  exact CGraph.thetaCycle_adj_iff a b x.1 y.1 hx hy

/-- The two ends of a double star can be exchanged. -/
theorem doubleStar_comm (m n : ℕ) : doubleStar m n = doubleStar n m := by
  rw [doubleStar_def, doubleStar_def]
  set E : (CGraph.doubleStar m n).V ≃ (CGraph.doubleStar n m).V :=
    CGraph.doubleStarSwap m n with hE
  refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
  intro x y
  have hx : x.1 < 2 + m + n := x.isLt
  have hy : y.1 < 2 + m + n := y.isLt
  have hval : ∀ p : (CGraph.doubleStar m n).V,
      (E p).1 = CGraph.doubleStarSwapFwd m n p.1 := fun _ ↦ rfl
  rw [Bool.eq_iff_iff, CGraph.doubleStar_adj_val, CGraph.doubleStar_adj_val, hval x, hval y]
  unfold CGraph.doubleStarSwapFwd
  split_ifs <;>
    (try simp only [false_and, false_or, true_and, and_true, or_false, true_or, or_true,
      or_self]) <;> omega

/-- Two adjacent paths of a theta graph may be exchanged. -/
theorem thetaGraph_swap (pre post : List ℕ) (a b : ℕ) :
    thetaGraph (pre ++ a :: b :: post) = thetaGraph (pre ++ b :: a :: post) := by
  have hsum : (pre ++ b :: a :: post).sum = (pre ++ a :: b :: post).sum := by
    simp only [List.sum_append, List.sum_cons]; omega
  have hL : CGraph.thetaEdges 2 (pre ++ a :: b :: post)
      = CGraph.thetaEdges 2 pre ++ ((CGraph.thetaEdges (2 + pre.sum) [a] ++
          CGraph.thetaEdges (2 + pre.sum + a) [b]) ++
            CGraph.thetaEdges (2 + pre.sum + a + b) post) := by
    rw [CGraph.thetaEdges_append, CGraph.thetaEdges_cons (2 + pre.sum) a (b :: post),
      CGraph.thetaEdges_cons (2 + pre.sum + a) b post, List.append_assoc]
  have hR : CGraph.thetaEdges 2 (pre ++ b :: a :: post)
      = CGraph.thetaEdges 2 pre ++ ((CGraph.thetaEdges (2 + pre.sum) [b] ++
          CGraph.thetaEdges (2 + pre.sum + b) [a]) ++
            CGraph.thetaEdges (2 + pre.sum + a + b) post) := by
    rw [CGraph.thetaEdges_append, CGraph.thetaEdges_cons (2 + pre.sum) b (a :: post),
      CGraph.thetaEdges_cons (2 + pre.sum + b) a post,
      show 2 + pre.sum + b + a = 2 + pre.sum + a + b from by omega, List.append_assoc]
  rw [thetaGraph_def, thetaGraph_def, CGraph.thetaGraph, CGraph.thetaGraph, hsum, hL, hR]
  refine Quotient.sound (CGraph.nonempty_iso_ofEdges_swap_theta _ (2 + pre.sum) a b _ _
    (by omega) ?_ ?_ ?_)
  · simp only [List.sum_append, List.sum_cons]
    omega
  · intro p q h
    have := CGraph.mem_thetaEdges_bound 2 pre p q h
    omega
  · intro p q h
    have := CGraph.mem_thetaEdges_bound (2 + pre.sum + a + b) post p q h
    omega

/-- The theta graph depends only on the multiset of its path lengths. -/
theorem thetaGraph_perm_append {xs ys : List ℕ} (h : xs.Perm ys) :
    ∀ pre : List ℕ, thetaGraph (pre ++ xs) = thetaGraph (pre ++ ys) := by
  induction h with
  | nil => intro pre; rfl
  | cons x _ ih =>
      intro pre
      simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [x])
  | swap x y l => intro pre; exact thetaGraph_swap pre l y x
  | trans _ _ ih1 ih2 => intro pre; exact (ih1 pre).trans (ih2 pre)

theorem thetaGraph_perm {xs ys : List ℕ} (h : xs.Perm ys) : thetaGraph xs = thetaGraph ys := by
  simpa using thetaGraph_perm_append h []

/-- Swapping the two paths of a two-path theta graph. -/
theorem thetaGraph_pair_comm (a b : ℕ) : thetaGraph [a, b] = thetaGraph [b, a] :=
  thetaGraph_perm (List.Perm.swap b a [])

/-- A theta graph all of whose paths have a single internal vertex is the complete bipartite
graph `K_{2,n}`: the two poles on one side, the `n` midpoints on the other. -/
@[simp] theorem thetaGraph_replicate_one (n : ℕ) :
    thetaGraph (List.replicate n 1) = bipartite 2 n := by
  rw [thetaGraph_def, bipartite_def]
  have hN : (2 : ℕ) + (List.replicate n 1).sum = 2 + n := by simp
  have key : (⟦CGraph.bipartite 2 n⟧ : IsoGraph) = ⟦CGraph.thetaGraph (List.replicate n 1)⟧ := by
    set E : (CGraph.bipartite 2 n).V ≃ (CGraph.thetaGraph (List.replicate n 1)).V :=
      (finSumFinEquiv (m := 2) (n := n)).trans (finCongr hN.symm) with hE
    refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
    have hl : ∀ a : (CGraph.complete 2).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete n).V, (E (Sum.inr b)).1 = 2 + b.1 := fun _ ↦ rfl
    have hth : ∀ u v : (CGraph.thetaGraph (List.replicate n 1)).V,
        ((CGraph.thetaGraph (List.replicate n 1)).Adj u v = true ↔
          (u.1 ≠ v.1 ∧ (((u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + n) ∨
              (2 ≤ u.1 ∧ u.1 < 2 + n ∧ v.1 = 1)) ∨
            ((v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + n) ∨ (2 ≤ v.1 ∧ v.1 < 2 + n ∧ u.1 = 1))))) := by
      intro u v
      rw [CGraph.thetaGraph_adj_val]
      simp only [CGraph.mem_thetaEdges_replicate_one]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hth]
    · rw [hl a, hl b]
      have ha : a.1 < 2 := a.isLt
      have hb : b.1 < 2 := b.isLt
      simp only [CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 2 := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < 2 := b.isLt
      simp only [CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega
  exact key.symm

/-- Every theta graph whose paths all have a single internal vertex is complete bipartite. -/
theorem thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) :
    thetaGraph xs = bipartite 2 xs.length := by
  obtain ⟨n, rfl⟩ : ∃ n, xs = List.replicate n 1 := ⟨xs.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
  rw [thetaGraph_replicate_one, List.length_replicate]

/-- A tadpole whose cycle is `C₂` — a single edge — is a path.  The relabelling swaps the two
vertices of the cycle, so that the tail leaves from the far end. -/
@[simp] theorem tadpole_two (k : ℕ) : tadpole 2 k = path (2 + k) := by
  rw [tadpole_def, path_def]
  set E : (CGraph.tadpole 2 k).V ≃ (CGraph.path (2 + k)).V :=
    CGraph.swapZeroOne (2 + k) (by omega) with hE
  refine Quotient.sound ⟨CGraph.isoOfAdj E ?_⟩
  intro x y
  have hx : x.1 < 2 + k := x.isLt
  have hy : y.1 < 2 + k := y.isLt
  have hval : ∀ p : (CGraph.tadpole 2 k).V,
      (E p).1 = if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1 := fun _ ↦ rfl
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hval x, hval y]
  simp only [CGraph.tadpole]
  rw [CGraph.ofEdges_adj_val]
  simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges]
  -- `simp_all` substitutes the branch hypotheses `x.1 = 0`, `x.1 = 1`, … into the membership
  -- disjunctions, which prunes most of them before `omega` has to case on them.
  split_ifs <;> (try simp_all) <;> omega

/-- A lollipop whose clique is `K₂` is a path. -/
@[simp] theorem lollipop_two (k : ℕ) : lollipop 2 k = path (2 + k) := by
  rw [lollipop_two_eq_tadpole, tadpole_two]

/-! ## Products

The one-vertex graph is a unit for the cartesian, strong and lexicographic products and an
absorbing element for the tensor product, which has no edges as soon as one factor has none.
`empty 1` rather than `complete 1` throughout: the two are equal, and `complete_one` puts
`empty 1` in `simp` normal form. -/

theorem cartesianProduct_comm (G H : IsoGraph) : G □g H = H □g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.cartesianProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.cartesianProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.cartesianProductComm _ _⟩

theorem tensorProduct_comm (G H : IsoGraph) : G ⊗g H = H ⊗g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.tensorProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.tensorProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.tensorProductComm _ _⟩

theorem strongProduct_comm (G H : IsoGraph) : G ⊠g H = H ⊠g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.strongProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.strongProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.strongProductComm _ _⟩

@[simp] theorem cartesianProduct_empty_one (G : IsoGraph) : G □g empty 1 = G := by
  haveI : Unique (CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, cartesianProduct_mk]
    refine Quotient.sound ⟨CGraph.isoOfAdj
      (G := CGraph.cartesianProduct g.canonicalize (CGraph.empty 1)) (H := g.canonicalize)
      (Equiv.prodUnique g.canonicalize.V (CGraph.empty 1).V) fun x y ↦ ?_⟩
    show g.canonicalize.Adj x.1 y.1 = _
    rw [CGraph.cartesianProduct_adj, Subsingleton.elim x.2 y.2]
    simp

@[simp] theorem empty_one_cartesianProduct (G : IsoGraph) : empty 1 □g G = G := by
  rw [cartesianProduct_comm, cartesianProduct_empty_one]

@[simp] theorem strongProduct_empty_one (G : IsoGraph) : G ⊠g empty 1 = G := by
  haveI : Unique (CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, strongProduct_mk]
    refine Quotient.sound ⟨CGraph.isoOfAdj
      (G := CGraph.strongProduct g.canonicalize (CGraph.empty 1)) (H := g.canonicalize)
      (Equiv.prodUnique g.canonicalize.V (CGraph.empty 1).V) fun x y ↦ ?_⟩
    show g.canonicalize.Adj x.1 y.1 = _
    rw [CGraph.strongProduct_adj]
    by_cases hx : x.1 = y.1
    · have hxy : x = y := Prod.ext hx (Subsingleton.elim _ _)
      cases hxy
      simp [CGraph.adj_self]
    · have hxy : x ≠ y := fun hh ↦ hx (congrArg Prod.fst hh)
      simp [hx, hxy, Subsingleton.elim x.2 y.2]

@[simp] theorem empty_one_strongProduct (G : IsoGraph) : empty 1 ⊠g G = G := by
  rw [strongProduct_comm, strongProduct_empty_one]

@[simp] theorem lexProduct_empty_one (G : IsoGraph) : G ·g empty 1 = G := by
  haveI : Unique (CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    refine Quotient.sound ⟨CGraph.isoOfAdj
      (G := CGraph.lexProduct g.canonicalize (CGraph.empty 1)) (H := g.canonicalize)
      (Equiv.prodUnique g.canonicalize.V (CGraph.empty 1).V) fun x y ↦ ?_⟩
    show g.canonicalize.Adj x.1 y.1 = _
    rw [CGraph.lexProduct_adj]
    simp

@[simp] theorem empty_one_lexProduct (G : IsoGraph) : empty 1 ·g G = G := by
  haveI : Unique (CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    refine Quotient.sound ⟨CGraph.isoOfAdj
      (G := CGraph.lexProduct (CGraph.empty 1) g.canonicalize) (H := g.canonicalize)
      (Equiv.uniqueProd g.canonicalize.V (CGraph.empty 1).V) fun x y ↦ ?_⟩
    show g.canonicalize.Adj x.2 y.2 = _
    rw [CGraph.lexProduct_adj, Subsingleton.elim x.1 y.1]
    simp

/-- A Cartesian product of edgeless graphs is edgeless. -/
@[simp] theorem cartesianProduct_empty (m n : ℕ) :
    empty m □g empty n = empty (m * n) := by
  rw [empty_def, empty_def, cartesianProduct_mk,
    mk_eq_empty (G := CGraph.cartesianProduct (CGraph.empty m) (CGraph.empty n)) (by simp)]
  simp

/-- The tensor product with an edgeless graph is edgeless. -/
@[simp] theorem tensorProduct_empty (G : IsoGraph) (n : ℕ) :
    G ⊗g empty n = empty (G.V * n) := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, tensorProduct_mk,
      mk_eq_empty (G := CGraph.tensorProduct g.canonicalize (CGraph.empty n)) (by simp)]
    simp

@[simp] theorem empty_tensorProduct (n : ℕ) (G : IsoGraph) :
    empty n ⊗g G = empty (n * G.V) := by
  rw [tensorProduct_comm, tensorProduct_empty, Nat.mul_comm]

/-- The strong product of complete graphs is complete. -/
@[simp] theorem strongProduct_complete (m n : ℕ) :
    complete m ⊠g complete n = complete (m * n) := by
  have h : ∀ x y : (CGraph.strongProduct (CGraph.complete m) (CGraph.complete n)).V, x ≠ y →
      (CGraph.strongProduct (CGraph.complete m) (CGraph.complete n)).Adj x y = true := by
    intro x y hxy
    simp [CGraph.strongProduct_adj, hxy]
  rw [complete_def, complete_def, strongProduct_mk, mk_eq_complete h]
  simp

/-- The lexicographic product of complete graphs is complete. -/
@[simp] theorem lexProduct_complete (m n : ℕ) :
    complete m ·g complete n = complete (m * n) := by
  have h : ∀ x y : (CGraph.lexProduct (CGraph.complete m) (CGraph.complete n)).V, x ≠ y →
      (CGraph.lexProduct (CGraph.complete m) (CGraph.complete n)).Adj x y = true := by
    intro x y hxy
    by_cases hx : x.1 = y.1
    · have h2 : x.2 ≠ y.2 := fun h2 ↦ hxy (Prod.ext hx h2)
      simp [CGraph.lexProduct_adj, hx, h2]
    · simp [CGraph.lexProduct_adj, hx]
  rw [complete_def, complete_def, lexProduct_mk, mk_eq_complete h]
  simp

/-! ### Zero vertices, and associativity

A factor with no vertices annihilates every product, and all four products are associative. -/

@[simp] theorem cartesianProduct_empty_zero (G : IsoGraph) :
    G □g empty 0 = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, cartesianProduct_mk]
    haveI : IsEmpty (CGraph.cartesianProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_cartesianProduct (G : IsoGraph) :
    empty 0 □g G = empty 0 := by
  rw [cartesianProduct_comm, cartesianProduct_empty_zero]

@[simp] theorem strongProduct_empty_zero (G : IsoGraph) :
    G ⊠g empty 0 = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, strongProduct_mk]
    haveI : IsEmpty (CGraph.strongProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_strongProduct (G : IsoGraph) :
    empty 0 ⊠g G = empty 0 := by
  rw [strongProduct_comm, strongProduct_empty_zero]

@[simp] theorem lexProduct_empty_zero (G : IsoGraph) : G ·g empty 0 = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    haveI : IsEmpty (CGraph.lexProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_lexProduct (G : IsoGraph) : empty 0 ·g G = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    haveI : IsEmpty (CGraph.lexProduct (CGraph.empty 0) g.canonicalize).V :=
      inferInstanceAs (IsEmpty ((CGraph.empty 0).V × g.canonicalize.V))
    exact mk_eq_empty_zero

theorem cartesianProduct_assoc (G H K : IsoGraph) :
    (G □g H) □g K = G □g (H □g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          cartesianProduct_mk, cartesianProduct_mk, cartesianProduct_mk, cartesianProduct_mk]
        exact Quotient.sound ⟨CGraph.Iso.cartesianProductAssoc _ _ _⟩

theorem tensorProduct_assoc (G H K : IsoGraph) :
    (G ⊗g H) ⊗g K = G ⊗g (H ⊗g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          tensorProduct_mk, tensorProduct_mk, tensorProduct_mk, tensorProduct_mk]
        exact Quotient.sound ⟨CGraph.Iso.tensorProductAssoc _ _ _⟩

theorem strongProduct_assoc (G H K : IsoGraph) :
    (G ⊠g H) ⊠g K = G ⊠g (H ⊠g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          strongProduct_mk, strongProduct_mk, strongProduct_mk, strongProduct_mk]
        exact Quotient.sound ⟨CGraph.Iso.strongProductAssoc _ _ _⟩

theorem lexProduct_assoc (G H K : IsoGraph) :
    (G ·g H) ·g K = G ·g (H ·g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          lexProduct_mk, lexProduct_mk, lexProduct_mk, lexProduct_mk]
        exact Quotient.sound ⟨CGraph.Iso.lexProductAssoc _ _ _⟩

/-! ### Distributivity over disjoint unions

Every product distributes over `disjUnion`: on the left and the right for the three commutative
products, and on the left only for the lexicographic one.  These are good `simp` lemmas — they push
`disjUnion` outwards, so a product of unions normalises to a union of products. -/

@[simp] theorem cartesianProduct_disjUnion (G H K : IsoGraph) :
    G □g (H ⊕g K)
      = (G □g H) ⊕g (G □g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          disjUnion_mk, cartesianProduct_mk, cartesianProduct_mk, cartesianProduct_mk,
          disjUnion_mk]
        exact Quotient.sound ⟨CGraph.Iso.cartesianProductDisjUnion _ _ _⟩

@[simp] theorem disjUnion_cartesianProduct (G H K : IsoGraph) :
    (G ⊕g H) □g K
      = (G □g K) ⊕g (H □g K) := by
  rw [cartesianProduct_comm, cartesianProduct_disjUnion, cartesianProduct_comm,
    cartesianProduct_comm K H]

@[simp] theorem tensorProduct_disjUnion (G H K : IsoGraph) :
    G ⊗g (H ⊕g K) = (G ⊗g H) ⊕g (G ⊗g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          disjUnion_mk, tensorProduct_mk, tensorProduct_mk, tensorProduct_mk, disjUnion_mk]
        exact Quotient.sound ⟨CGraph.Iso.tensorProductDisjUnion _ _ _⟩

@[simp] theorem disjUnion_tensorProduct (G H K : IsoGraph) :
    (G ⊕g H) ⊗g K = (G ⊗g K) ⊕g (H ⊗g K) := by
  rw [tensorProduct_comm, tensorProduct_disjUnion, tensorProduct_comm, tensorProduct_comm K H]

@[simp] theorem strongProduct_disjUnion (G H K : IsoGraph) :
    G ⊠g (H ⊕g K) = (G ⊠g H) ⊕g (G ⊠g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          disjUnion_mk, strongProduct_mk, strongProduct_mk, strongProduct_mk, disjUnion_mk]
        exact Quotient.sound ⟨CGraph.Iso.strongProductDisjUnion _ _ _⟩

@[simp] theorem disjUnion_strongProduct (G H K : IsoGraph) :
    (G ⊕g H) ⊠g K = (G ⊠g K) ⊕g (H ⊠g K) := by
  rw [strongProduct_comm, strongProduct_disjUnion, strongProduct_comm, strongProduct_comm K H]

/-- The lexicographic product distributes over `disjUnion` in its first factor only. -/
@[simp] theorem disjUnion_lexProduct (G H K : IsoGraph) :
    (G ⊕g H) ·g K = (G ·g K) ⊕g (H ·g K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k =>
        rw [← mk_canonicalize g, ← mk_canonicalize h, ← mk_canonicalize k,
          disjUnion_mk, lexProduct_mk, lexProduct_mk, lexProduct_mk, disjUnion_mk]
        exact Quotient.sound ⟨CGraph.Iso.lexProductDisjUnion _ _ _⟩

/-- Multiplying by two independent vertices doubles the graph.  The same holds for the strong and
lexicographic products, but not for the tensor product, which is edgeless here. -/
theorem empty_two_cartesianProduct (G : IsoGraph) :
    empty 2 □g G = G ⊕g G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_cartesianProduct,
    empty_one_cartesianProduct]

theorem cartesianProduct_empty_two (G : IsoGraph) :
    G □g empty 2 = G ⊕g G := by
  rw [cartesianProduct_comm, empty_two_cartesianProduct]

theorem empty_two_strongProduct (G : IsoGraph) :
    empty 2 ⊠g G = G ⊕g G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_strongProduct,
    empty_one_strongProduct]

theorem strongProduct_empty_two (G : IsoGraph) :
    G ⊠g empty 2 = G ⊕g G := by
  rw [strongProduct_comm, empty_two_strongProduct]

theorem empty_two_lexProduct (G : IsoGraph) : empty 2 ·g G = G ⊕g G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_lexProduct,
    empty_one_lexProduct]

/-! ### Copies and blow-ups

`empty n □ G` is `n` disjoint copies of `G`, and `K_n[G]` is `n` copies with every pair of copies
joined; the two are complements of each other.  The complete multipartite graphs with equal parts
are exactly the blow-ups of a clique by an independent set. -/

/-- Peeling one copy off `empty (n+1) □ G`. -/
theorem empty_succ_cartesianProduct (n : ℕ) (G : IsoGraph) :
    empty (n + 1) □g G = G ⊕g (empty n □g G) := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1, ← disjUnion_empty, disjUnion_cartesianProduct,
    empty_one_cartesianProduct]

/-- **The lexicographic product is the one whose complement is a product of complements.** -/
@[simp] theorem compl_lexProduct (G H : IsoGraph) :
    (G ·g H)ᶜ = Gᶜ ·g Hᶜ := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, compl_mk, compl_mk, compl_mk,
        lexProduct_mk]
      exact Quotient.sound ⟨CGraph.Iso.complLexProduct _ _⟩

/-- With an edgeless first factor the lexicographic and Cartesian products agree: both are `n`
disjoint copies. -/
theorem empty_lexProduct (n : ℕ) (G : IsoGraph) :
    empty n ·g G = empty n □g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk, cartesianProduct_mk]
    exact Quotient.sound ⟨CGraph.Iso.emptyLexProduct _ _⟩

/-- And so does the strong product. -/
theorem empty_strongProduct (n : ℕ) (G : IsoGraph) :
    empty n ⊠g G = empty n □g G := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, strongProduct_mk, cartesianProduct_mk]
    exact Quotient.sound ⟨CGraph.Iso.emptyStrongProduct _ _⟩

/-- `K_m[G]` is `m` copies of `G` with every pair of copies joined — the complement of `m` disjoint
copies of `Gᶜ`. -/
theorem complete_lexProduct (m : ℕ) (G : IsoGraph) :
    complete m ·g G = (empty m □g Gᶜ)ᶜ := by
  conv_lhs => rw [← compl_compl (complete m ·g G)]
  rw [compl_lexProduct, compl_complete, empty_lexProduct]

/-- The complement of a complete multipartite graph with `m` equal parts is `m` disjoint cliques. -/
theorem compl_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d))ᶜ
      = empty m □g complete d := by
  induction m with
  | zero =>
    rw [List.replicate_zero, completeMultipartite_nil, compl_empty, complete_zero,
      empty_zero_cartesianProduct]
  | succ m ih =>
    rw [List.replicate_succ, compl_completeMultipartite_cons, ih, empty_succ_cartesianProduct]

/-- **Equal parts make a blow-up**: `K_{m×d}` is `K_m` with each vertex blown up to `d`
independent ones. -/
theorem completeMultipartite_replicate (m d : ℕ) :
    completeMultipartite (List.replicate m d) = complete m ·g empty d := by
  rw [complete_lexProduct, compl_empty, ← compl_completeMultipartite_replicate, compl_compl]

/-- `paley 9` is `K₃` with every vertex blown up to three. -/
theorem paley_nine_eq_lexProduct : paley 9 = complete 3 ·g empty 3 := by
  rw [paley_nine, show ([3, 3, 3] : List ℕ) = List.replicate 3 3 from rfl,
    completeMultipartite_replicate]

/-- The complement of the cocktail-party graph is a perfect matching. -/
theorem compl_cocktailParty (n : ℕ) :
    (cocktailParty n)ᶜ = empty n □g complete 2 :=
  compl_completeMultipartite_replicate n 2

/-- The cocktail party graph is the complement of a perfect matching, and the matching is a
circulant. -/
theorem compl_cocktailParty_eq_circulant (m : ℕ) :
    (cocktailParty (m + 1))ᶜ = circulant (2 * (m + 1)) [m + 1] := by
  rw [compl_cocktailParty, circulant_matching]

theorem cocktailParty_eq_lexProduct (m : ℕ) :
    cocktailParty m = complete m ·g empty 2 :=
  completeMultipartite_replicate m 2

/-- The balanced complete bipartite graph is the two-part blow-up. -/
theorem bipartite_self_eq_lexProduct (n : ℕ) :
    bipartite n n = complete 2 ·g empty n := by
  rw [← completeMultipartite_replicate 2 n, show List.replicate 2 n = [n, n] from rfl,
    completeMultipartite_pair]

/-- The lexicographic product distributes over `join` in its first factor, for the same reason it
distributes over `disjUnion`: the two are exchanged by complementation. -/
theorem join_lexProduct (G H K : IsoGraph) :
    (G ∇g H) ·g K = (G ·g K) ∇g (H ·g K) := by
  conv_lhs => rw [← compl_compl ((G ∇g H) ·g K)]
  rw [compl_lexProduct, compl_join, disjUnion_lexProduct, ← compl_lexProduct G K,
    ← compl_lexProduct H K, ← join_def]

@[simp] theorem lexProduct_empty (m n : ℕ) : empty m ·g empty n = empty (m * n) := by
  rw [empty_lexProduct, cartesianProduct_empty]

@[simp] theorem strongProduct_empty (m n : ℕ) :
    empty m ⊠g empty n = empty (m * n) := by
  rw [empty_strongProduct, cartesianProduct_empty]

/-- **Blowing up a complete multipartite graph multiplies its parts.**  Replacing every vertex by
`d` independent ones keeps the graph complete multipartite, with each part `d` times as large. -/
theorem lexProduct_completeMultipartite_empty (ds : List ℕ) (d : ℕ) :
    completeMultipartite ds ·g empty d = completeMultipartite (ds.map (· * d)) := by
  induction ds with
  | nil => rw [List.map_nil, completeMultipartite_nil, empty_zero_lexProduct]
  | cons a ds ih =>
    rw [completeMultipartite_cons, join_lexProduct, ih, lexProduct_empty, List.map_cons,
      completeMultipartite_cons]

/-- The two-part case: blowing up `K_{a,b}` gives `K_{ad,bd}`. -/
theorem bipartite_mul (a b d : ℕ) :
    bipartite (a * d) (b * d) = bipartite a b ·g empty d := by
  rw [← completeMultipartite_pair, ← completeMultipartite_pair,
    lexProduct_completeMultipartite_empty]
  rfl

/-- **`Q_{m+n} = Q_m □ Q_n`**: splitting a bit-string of length `m + n` into its first `m` and
last `n` bits.  Iterating `hypercube_succ` is all it takes. -/
theorem hypercube_add (m n : ℕ) :
    hypercube (m + n) = hypercube m □g hypercube n := by
  induction n with
  | zero => rw [Nat.add_zero, hypercube_zero, cartesianProduct_empty_one]
  | succ n ih =>
    rw [← Nat.add_assoc, hypercube_succ, ih, cartesianProduct_assoc, ← hypercube_succ]

/-- `Q₄` is the `4 × 4` torus. -/
theorem hypercube_four : hypercube 4 = cycle 4 □g cycle 4 := by
  rw [show hypercube 4 = hypercube (2 + 2) from rfl, hypercube_add, hypercube_two]

/-! ### Rooks and ladders -/

theorem rook_one_left (n : ℕ) : rook 1 n = complete n := by
  show complete 1 □g complete n = complete n
  rw [complete_one, empty_one_cartesianProduct]

theorem rook_one_right (m : ℕ) : rook m 1 = complete m := by
  show complete m □g complete 1 = complete m
  rw [complete_one, cartesianProduct_empty_one]

theorem rook_comm (m n : ℕ) : rook m n = rook n m := cartesianProduct_comm _ _

/-- The `2 × 2` rook's graph is the square. -/
theorem rook_two_two : rook 2 2 = cycle 4 := by
  show complete 2 □g complete 2 = cycle 4
  rw [complete_def, cartesianProduct_mk, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.cartesianProduct (CGraph.complete 2) (CGraph.complete 2))
    (H := CGraph.cycle 4)
    (⟨fun p ↦ if p.1 = 0 then (if p.2 = 0 then 0 else 1) else (if p.2 = 0 then 3 else 2),
      ![(0, 0), (0, 1), (1, 1), (1, 0)], by decide, by decide⟩ : (Fin 2 × Fin 2) ≃ Fin 4)
    (by decide)⟩

/-- The complement of the rook's graph is the tensor product of the two complete graphs — the
`CGraph`-level `CGraph.compl_rook`, transported to the quotient. -/
theorem compl_rook (m n : ℕ) :
    (rook m n)ᶜ = complete m ⊗g complete n := by
  have hrook : (rook m n : IsoGraph) = ⟦CGraph.rook m n⟧ := by
    rw [show (rook m n : IsoGraph) = complete m □g complete n from rfl,
      complete_def, complete_def, cartesianProduct_mk]
  rw [hrook, compl_mk, CGraph.compl_rook, complete_def, complete_def, tensorProduct_mk]

/-- `K₂ × K₂` is a perfect matching: the tensor product keeps only the two "diagonal" moves. -/
theorem tensorProduct_complete_two_two :
    complete 2 ⊗g complete 2 = complete 2 ⊕g complete 2 := by
  rw [← compl_rook, rook_two_two, compl_cycle_four]

@[simp] theorem rook_zero_left (n : ℕ) : rook 0 n = empty 0 := by
  show complete 0 □g complete n = empty 0
  rw [complete_zero, empty_zero_cartesianProduct]

@[simp] theorem rook_zero_right (m : ℕ) : rook m 0 = empty 0 := by
  show complete m □g complete 0 = empty 0
  rw [complete_zero, cartesianProduct_empty_zero]

/-- The two-rung ladder is the square. -/
theorem ladder_two : ladder 2 = cycle 4 := by
  show path 2 □g complete 2 = cycle 4
  rw [path_two]
  exact rook_two_two

theorem ladder_one : ladder 1 = complete 2 := by
  show path 1 □g complete 2 = complete 2
  rw [path_one, empty_one_cartesianProduct]

/-- The two-rung prism is the square. -/
theorem prism_two : prism 2 = cycle 4 := by
  show cycle 2 □g complete 2 = cycle 4
  rw [cycle_two]
  exact rook_two_two

/-- `K₂ □ K₃` is the triangular prism. -/
theorem rook_two_three : rook 2 3 = prism 3 := by
  show complete 2 □g complete 3 = cycle 3 □g complete 2
  rw [cycle_three, cartesianProduct_comm]

/-- The complement of the hexagon is the triangular prism: `i ~ i + 2` gives the two triangles and
`i ~ i + 3` the matching between them. -/
theorem compl_cycle_six : (cycle 6)ᶜ = prism 3 := by
  show (cycle 6)ᶜ = cycle 3 □g complete 2
  rw [cycle_def, compl_mk, cycle_def, complete_def, cartesianProduct_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.compl (CGraph.cycle 6))
    (H := CGraph.cartesianProduct (CGraph.cycle 3) (CGraph.complete 2))
    (⟨![(0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1)],
      fun p ↦ ![![0, 3], ![2, 5], ![4, 1]] p.1 p.2, by decide, by decide⟩ :
        Fin 6 ≃ (Fin 3 × Fin 2))
    (by decide)⟩

theorem compl_prism_three : (prism 3)ᶜ = cycle 6 := by
  rw [← compl_cycle_six, compl_compl]

/-- The cube graph is the four-rung prism. -/
theorem hypercube_three : hypercube 3 = prism 4 := by
  show hypercube 3 = cycle 4 □g complete 2
  rw [hypercube_succ, hypercube_two]

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

/-- A Cartesian product of nonempty graphs is bipartite exactly when both factors are. -/
theorem isBipartite_cartesianProduct_iff {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsBipartite (G □g H) ↔ IsBipartite G ∧ IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk, isBipartite_mk, isBipartite_mk, isBipartite_mk]
  have hG' : Nonempty G.canonicalize.V := Fintype.card_pos_iff.1 hG
  have hH' : Nonempty H.canonicalize.V := Fintype.card_pos_iff.1 hH
  exact ⟨fun h ↦ ⟨h.of_cartesianProduct_left hH', h.of_cartesianProduct_right hG'⟩,
    fun h ↦ CGraph.IsBipartite.cartesianProduct h.1 h.2⟩

theorem isBipartite_tensorProduct_left {G H : IsoGraph} (hG : IsBipartite G) :
    IsBipartite (G ⊗g H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [tensorProduct_mk]
  exact CGraph.IsBipartite.tensorProduct_left hG

theorem isBipartite_tensorProduct_right {G H : IsoGraph} (hH : IsBipartite H) :
    IsBipartite (G ⊗g H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [tensorProduct_mk]
  exact CGraph.IsBipartite.tensorProduct_right hH

@[simp] theorem isBipartite_empty (n : ℕ) : IsBipartite (empty n) := by
  rw [empty_def, isBipartite_mk]
  exact ⟨fun _ ↦ false, by simp⟩

@[simp] theorem isBipartite_bipartite (m n : ℕ) : IsBipartite (bipartite m n) := by
  rw [bipartite_def, isBipartite_mk]
  exact ⟨Sum.elim (fun _ ↦ false) (fun _ ↦ true), by
    rintro (a | b) (c | d) hadj <;> simp at hadj ⊢⟩

@[simp] theorem isBipartite_star (n : ℕ) : IsBipartite (star n) := by
  rw [star_eq_bipartite]; exact isBipartite_bipartite 1 n

@[simp] theorem isBipartite_complete_two : IsBipartite (complete 2) := by
  rw [← bipartite_one_one]; exact isBipartite_bipartite 1 1

@[simp] theorem isBipartite_path (n : ℕ) : IsBipartite (path n) := by
  rw [path_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin n).1 % 2 = 1), fun i j hij ↦ ?_⟩
  simp only [CGraph.path, CGraph.ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, ne_eq] at hij
  simp only [ne_eq, decide_eq_decide]
  omega

@[simp] theorem isBipartite_cycle_even (m : ℕ) : IsBipartite (cycle (2 * m)) := by
  rw [cycle_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin (2 * m)).1 % 2 = 1), fun i j hij ↦ ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  have key : ∀ x y : Fin (2 * m), (x.1 + 1) % (2 * m) = y.1 → (x.1 + y.1) % 2 = 1 := by
    intro x y hxy
    have hx := x.isLt
    have hy := y.isLt
    rcases Nat.lt_or_ge (x.1 + 1) (2 * m) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hxy
      omega
    · have : x.1 + 1 = 2 * m := by omega
      rw [this, Nat.mod_self] at hxy
      omega
  simp only [CGraph.cycle, CGraph.ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, ne_eq] at hij
  have := hij.2
  simp only [ne_eq, decide_eq_decide]
  rcases this with h | h
  · have := key i j h
    omega
  · have := key j i h
    omega

@[simp] theorem isBipartite_hypercube (n : ℕ) : IsBipartite (hypercube n) := by
  induction n with
  | zero => rw [hypercube_zero]; exact isBipartite_empty 1
  | succ n ih =>
    rw [hypercube_succ]
    exact isBipartite_cartesianProduct ih isBipartite_complete_two

@[simp] theorem isBipartite_ladder (n : ℕ) : IsBipartite (ladder n) :=
  isBipartite_cartesianProduct (isBipartite_path n) isBipartite_complete_two

@[simp] theorem isBipartite_prism_even (m : ℕ) : IsBipartite (prism (2 * m)) :=
  isBipartite_cartesianProduct (isBipartite_cycle_even m) isBipartite_complete_two

/-- **A spider is a tree, hence bipartite**: colour a vertex by the parity of its distance from
the centre. -/
@[simp] theorem isBipartite_spider (ks : List ℕ) : IsBipartite (spider ks) := by
  rw [spider_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.spiderDepth 1 ks (i : Fin (1 + ks.sum)).1 % 2 = 1),
    fun x y hxy ↦ ?_⟩
  rw [CGraph.spider_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with h | h
  · have := CGraph.spiderDepth_parity 1 ks x.1 y.1 Nat.one_pos h
    omega
  · have := CGraph.spiderDepth_parity 1 ks y.1 x.1 Nat.one_pos h
    omega

/-- **A double star is a tree, hence bipartite**: one centre goes with the leaves of the other. -/
@[simp] theorem isBipartite_doubleStar (m n : ℕ) : IsBipartite (doubleStar m n) := by
  rw [doubleStar_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin (2 + m + n)).1 = 1 ∨
    (2 ≤ (i : Fin (2 + m + n)).1 ∧ (i : Fin (2 + m + n)).1 < 2 + m)), fun x y hxy ↦ ?_⟩
  rw [CGraph.doubleStar_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  omega

/-- **A tadpole with an even cycle is bipartite**: the tail continues the alternation around the
cycle, which closes up because the cycle has even length. -/
@[simp] theorem isBipartite_tadpole_even (m k : ℕ) : IsBipartite (tadpole (2 * m) k) := by
  rw [tadpole_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((if (i : Fin (2 * m + k)).1 < 2 * m then (i : Fin (2 * m + k)).1
    else (i : Fin (2 * m + k)).1 + 1) % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.tadpole_adj_val] at hxy
  simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hxy
  simp only [ne_eq, decide_eq_decide]
  obtain ⟨hne, h⟩ := hxy
  split_ifs <;> omega

/-- **A cycle of even length with pendant vertices is bipartite**: a pendant takes the colour
opposite to the cycle vertex it hangs off. -/
@[simp] theorem isBipartite_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t) :
    IsBipartite (cyclePendant (2 * t) ks) := by
  rw [cyclePendant_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.pendantOwner (2 * t) 0 (2 * t) ks
    (i : Fin (2 * t + ks.sum)).1 % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.cyclePendant_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  have key : ∀ p q : ℕ, (p, q) ∈ CGraph.cycleEdges (2 * t) ++ CGraph.pendantEdges 0 (2 * t) ks →
      (CGraph.pendantOwner (2 * t) 0 (2 * t) ks p
        + CGraph.pendantOwner (2 * t) 0 (2 * t) ks q) % 2 = 1 := by
    intro p q hpq
    rw [List.mem_append] at hpq
    rcases hpq with hpq | hpq
    · rw [CGraph.mem_cycleEdges] at hpq
      rw [CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega),
        CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega)]
      omega
    · exact CGraph.pendantOwner_parity (2 * t) 0 (2 * t) ks p q (by omega) (by omega) hpq
  rcases hxy.2 with hm | hm
  · have := key x.1 y.1 hm
    omega
  · have := key y.1 x.1 hm
    omega

/-- **A theta graph is bipartite as soon as its paths all have the same parity of length.**  The
colouring is `thetaDepth b`, with `b` recording which class the far pole falls into. -/
theorem isBipartite_thetaGraph_of_parity {xs : List ℕ} (b : ℕ)
    (h : ∀ k ∈ xs, (k + b) % 2 = 1) : IsBipartite (thetaGraph xs) := by
  rw [thetaGraph_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.thetaDepth b 2 xs (i : Fin (2 + xs.sum)).1 % 2 = 1),
    fun x y hxy ↦ ?_⟩
  rw [CGraph.thetaGraph_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with hm | hm
  · have := CGraph.thetaDepth_parity b 2 xs x.1 y.1 (by omega) h hm
    omega
  · have := CGraph.thetaDepth_parity b 2 xs y.1 x.1 (by omega) h hm
    omega

/-- Every path of odd length: the two poles get opposite colours. -/
@[simp] theorem isBipartite_thetaGraph_even {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 0) :
    IsBipartite (thetaGraph xs) :=
  isBipartite_thetaGraph_of_parity 1 fun k hk ↦ by have := h k hk; omega

/-- Every path of even length: the two poles get the same colour. -/
@[simp] theorem isBipartite_thetaGraph_odd {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 1) :
    IsBipartite (thetaGraph xs) :=
  isBipartite_thetaGraph_of_parity 0 fun k hk ↦ by have := h k hk; omega

theorem not_isBipartite_complete_three : ¬ IsBipartite (complete 3) := not_isBipartite_complete 0

theorem not_isBipartite_cycle_three : ¬ IsBipartite (cycle 3) := not_isBipartite_cycle_odd 0

theorem not_isBipartite_cycle_five : ¬ IsBipartite (cycle 5) := not_isBipartite_cycle_odd 1

/-- Two paths of different parity close up into an odd cycle, and then the graph is not
bipartite. -/
theorem not_isBipartite_thetaGraph_pair {a b : ℕ} (h : (a + b) % 2 = 1) :
    ¬ IsBipartite (thetaGraph [a, b]) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 3 := ⟨(a + b) / 2, by omega⟩
  rw [thetaGraph_pair, hm]
  exact not_isBipartite_cycle_odd m

/-- A tadpole whose cycle is odd is not bipartite. -/
theorem not_isBipartite_tadpole_odd (m k : ℕ) : ¬ IsBipartite (tadpole (2 * m + 3) k) := by
  rw [tadpole_def, isBipartite_mk]
  exact CGraph.not_isBipartite_ofEdges_of_odd_cycle _ (2 * m + 3) _ (by omega) (by omega)
    (by omega) fun _ _ h ↦ Or.inl (List.mem_append_left _ h)

/-- A cycle with pendant vertices is not bipartite when the cycle is odd. -/
theorem not_isBipartite_cyclePendant_odd (m : ℕ) (ks : List ℕ) :
    ¬ IsBipartite (cyclePendant (2 * m + 3) ks) := by
  rw [cyclePendant_def, isBipartite_mk]
  exact CGraph.not_isBipartite_ofEdges_of_odd_cycle _ (2 * m + 3) _ (by omega) (by omega)
    (by omega) fun _ _ h ↦ Or.inl (List.mem_append_left _ h)

/-- A lollipop is never bipartite: its head is a complete graph on at least three vertices, and
the triangle `0, 1, 2` sits inside it. -/
theorem not_isBipartite_lollipop (m k : ℕ) : ¬ IsBipartite (lollipop (m + 3) k) := by
  rw [lollipop_def, isBipartite_mk]
  refine CGraph.not_isBipartite_ofEdges_of_odd_cycle _ 3 _ (by omega) (by omega) (by omega) ?_
  intro p q h
  rw [CGraph.mem_cycleEdges] at h
  rcases h with ⟨rfl, h⟩ | ⟨h, rfl⟩
  · exact Or.inl (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨by omega, by omega⟩))
  · exact Or.inr (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨by omega, by omega⟩))

/-- A wheel is not bipartite: the hub and any edge of the rim form a triangle. -/
theorem not_isBipartite_wheel (n : ℕ) : ¬ IsBipartite (wheel (n + 3)) := by
  rw [wheel_def, isBipartite_mk]
  refine CGraph.not_isBipartite_of_triangle (a := Sum.inl (0 : Fin 1))
    (b := Sum.inr ⟨0, by omega⟩) (d := Sum.inr ⟨1, by omega⟩)
    (by simp [CGraph.wheel]) (by simp [CGraph.wheel]) ?_
  show (CGraph.join (CGraph.complete 1) (CGraph.cycle (n + 3))).Adj _ _ = true
  rw [CGraph.join_adj_inr_inr, CGraph.cycle_adj_val]
  show (0 : ℕ) ≠ 1 ∧ ((0 + 1) % (n + 3) = 1 ∨ (1 + 1) % (n + 3) = 0)
  exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt (by omega))⟩

/-- Each edge of `foldedCube n` flips either one coordinate or all `n` of them, so for odd `n`
every edge changes the parity of the number of `true`s. -/
@[simp] theorem isBipartite_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) :
    IsBipartite (foldedCube n) := by
  rw [foldedCube_def, isBipartite_mk]
  refine ⟨fun x ↦ decide ((Finset.univ.filter fun i ↦ x i = true).card % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.foldedCube_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hxy
  have hpar := CGraph.card_ne_parity n x y
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with h | h <;> rw [h] at hpar <;> omega

/-- For even `n` the antipodal edges close an odd cycle: flip the coordinates one at a time from
`0…0` to `1…1`, which takes `n` steps, and come back in one. -/
theorem not_isBipartite_foldedCube_of_even {n : ℕ} (h2 : n % 2 = 0) (hn : 0 < n) :
    ¬ IsBipartite (foldedCube n) := by
  rw [foldedCube_def, isBipartite_mk]
  refine CGraph.not_isBipartite_of_odd_walk
    (fun k ↦ (if k ≤ n then CGraph.prefixVec n k else CGraph.prefixVec n 0 :
      (CGraph.foldedCube n).V)) (n + 1) (by omega) ?_ ?_
  · intro k hk
    dsimp only
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have hcard := CGraph.card_prefixVec_step n k hkn
      have hne : CGraph.prefixVec n k ≠ CGraph.prefixVec n (k + 1) := by
        intro he
        rw [he] at hcard
        simp at hcard
      rw [if_pos (by omega), if_pos (by omega), CGraph.foldedCube_adj, hcard]
      simp [hne]
    · have hkn' : k = n := by omega
      subst hkn'
      have hcard := CGraph.card_prefixVec_full k
      have hne : CGraph.prefixVec k 0 ≠ CGraph.prefixVec k k := by
        intro he
        have := congrFun he ⟨0, by omega⟩
        simp [CGraph.prefixVec] at this
        omega
      rw [if_pos (by omega), if_neg (by omega), CGraph.foldedCube_adj,
        show (Finset.univ.filter fun i ↦ CGraph.prefixVec k k i ≠ CGraph.prefixVec k 0 i)
          = (Finset.univ.filter fun i ↦ CGraph.prefixVec k 0 i ≠ CGraph.prefixVec k k i) from
          Finset.filter_congr fun i _ ↦ by exact ne_comm, hcard]
      simp [Ne.symm hne]
  · dsimp only
    rw [if_neg (by omega), if_pos (by omega)]

theorem not_isBipartite_foldedCube_even (m : ℕ) : ¬ IsBipartite (foldedCube (2 * m + 2)) :=
  not_isBipartite_foldedCube_of_even (by omega) (by omega)

/-- **A circulant on an even number of vertices whose connection set is all odd is bipartite.**
Colour a vertex by the parity of its index: a step of odd length always crosses, because reducing
mod an even `n` does not change parity. -/
theorem isBipartite_circulant {n : ℕ} {S : List ℕ} (hn : n % 2 = 0) (hS : ∀ d ∈ S, d % 2 = 1) :
    IsBipartite (circulant n S) := by
  rw [circulant_def, isBipartite_mk]
  refine ⟨fun x ↦ decide (x.1 % 2 = 1), fun x y hxy ↦ ?_⟩
  have hadj : (decide (x ≠ y) && (S.contains ((y.1 + n - x.1) % n) ||
      S.contains ((x.1 + n - y.1) % n))) = true := hxy
  rw [Bool.and_eq_true, Bool.or_eq_true] at hadj
  have h1 := sub_mod_cases x.isLt y.isLt
  have h2 := sub_mod_cases y.isLt x.isLt
  simp only [ne_eq, decide_eq_decide]
  rcases hadj.2 with h | h
  · have := hS _ (List.mem_of_elem_eq_true h)
    omega
  · have := hS _ (List.mem_of_elem_eq_true h)
    omega

/-- **A circulant on an odd number of vertices is not bipartite** as soon as its connection set
contains a difference that does something.  Stepping by `d` returns to the start after `n` steps,
and `n` is odd. -/
theorem not_isBipartite_circulant_of_odd {n : ℕ} {S : List ℕ} (hn : n % 2 = 1) (d : ℕ)
    (hd : d ∈ S) (h0 : 0 < d) (hdn : d < n) : ¬ IsBipartite (circulant n S) := by
  rw [circulant_def, isBipartite_mk]
  have hpos : 0 < n := by omega
  refine CGraph.not_isBipartite_of_odd_walk
    (fun k ↦ (⟨k * d % n, Nat.mod_lt _ hpos⟩ : Fin n)) n hn ?_
    (Fin.ext (by simp [Nat.mul_mod_right]))
  intro k _
  have ha : k * d % n < n := Nat.mod_lt _ hpos
  have hb : (k + 1) * d % n = (k * d % n + d) % n := by
    rw [show (k + 1) * d = k * d + d by ring, Nat.add_mod, Nat.mod_eq_of_lt hdn]
  have key : ((k + 1) * d % n + n - k * d % n) % n = d ∧ k * d % n ≠ (k + 1) * d % n := by
    rcases Nat.lt_or_ge (k * d % n + d) n with h | h
    · rw [hb, Nat.mod_eq_of_lt h]
      refine ⟨?_, by omega⟩
      rw [show k * d % n + d + n - k * d % n = d + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hdn
    · have he : (k * d % n + d) % n = k * d % n + d - n := by
        conv_lhs => rw [show k * d % n + d = (k * d % n + d - n) + n by omega]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hb, he]
      refine ⟨?_, by omega⟩
      rw [show k * d % n + d - n + n - k * d % n = d by omega]
      exact Nat.mod_eq_of_lt hdn
  show (decide _ && (S.contains _ || S.contains _)) = true
  rw [key.1]
  simp only [Bool.and_eq_true, Bool.or_eq_true, ne_eq, decide_eq_true_eq, Fin.mk.injEq]
  exact ⟨key.2, Or.inl (List.elem_eq_true_of_mem hd)⟩

/-- The rook's graph has a triangle in each row. -/
@[simp] theorem not_isBipartite_rook (m n : ℕ) : ¬ IsBipartite (rook (m + 3) (n + 1)) := by
  show ¬ IsBipartite (complete (m + 3) □g complete (n + 1))
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_complete m h.1

/-- A prism over an odd cycle is not bipartite. -/
@[simp] theorem not_isBipartite_prism_odd (m : ℕ) : ¬ IsBipartite (prism (2 * m + 3)) := by
  show ¬ IsBipartite (cycle (2 * m + 3) □g complete 2)
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_cycle_odd m h.1

attribute [simp] IsoGraph.not_isBipartite_kneser IsoGraph.not_isBipartite_johnson

/-- Triangular graphs on at least four points contain a triangle. -/
theorem not_isBipartite_triangular {n : ℕ} (h : 4 ≤ n) : ¬ IsBipartite (triangular n) :=
  not_isBipartite_johnson (by omega) (by omega)

/-- **The Petersen graph is not bipartite**: it is triangle-free, but it has a five-cycle. -/
@[simp] theorem not_isBipartite_petersen : ¬ IsBipartite petersen := by
  show ¬ IsBipartite (kneser 5 2)
  rw [kneser_def, isBipartite_mk]
  exact CGraph.not_isBipartite_kneser_five_two

/-- A side of a bipartite join is bipartite. -/
theorem IsBipartite.of_join_left {G H : IsoGraph} (h : IsBipartite (G ∇g H)) : IsBipartite G := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [join_mk, isBipartite_mk] at h
  rw [isBipartite_mk]
  exact h.of_join_left

theorem IsBipartite.of_join_right {G H : IsoGraph} (h : IsBipartite (G ∇g H)) :
    IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [join_mk, isBipartite_mk] at h
  rw [isBipartite_mk]
  exact h.of_join_right

theorem not_isBipartite_join_left {G H : IsoGraph} (hG : ¬ IsBipartite G) :
    ¬ IsBipartite (G ∇g H) := fun h ↦ hG h.of_join_left

theorem not_isBipartite_join_right {G H : IsoGraph} (hH : ¬ IsBipartite H) :
    ¬ IsBipartite (G ∇g H) := fun h ↦ hH h.of_join_right

/-- **A join of three nonempty graphs is never bipartite.** -/
theorem not_isBipartite_join_join {G H K : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hK : 0 < K.V) : ¬ IsBipartite (G ∇g (H ∇g K)) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  induction K using Quotient.inductionOn with | _ K =>
  rw [← mk_canonicalize G, ← mk_canonicalize H, ← mk_canonicalize K] at *
  rw [join_mk, join_mk, isBipartite_mk]
  obtain ⟨a⟩ : Nonempty G.canonicalize.V := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ : Nonempty H.canonicalize.V := Fintype.card_pos_iff.1 hH
  obtain ⟨c⟩ : Nonempty K.canonicalize.V := Fintype.card_pos_iff.1 hK
  exact CGraph.not_isBipartite_join_join a b c

/-- **Complete multipartite graphs with three nonempty parts are not bipartite.** -/
@[simp] theorem not_isBipartite_completeMultipartite (a b c : ℕ) (ds : List ℕ) :
    ¬ IsBipartite (completeMultipartite ((a + 1) :: (b + 1) :: (c + 1) :: ds)) := by
  rw [completeMultipartite_cons, completeMultipartite_cons, completeMultipartite_cons]
  exact not_isBipartite_join_join (by simp) (by simp) (by simp)

/-- Every page of a book meets the spine in a triangle. -/
@[simp] theorem not_isBipartite_book (n : ℕ) : ¬ IsBipartite (book (n + 1)) :=
  not_isBipartite_completeMultipartite 0 0 n []

/-- The cocktail party graph on three or more pairs is not bipartite. -/
@[simp] theorem not_isBipartite_cocktailParty (n : ℕ) : ¬ IsBipartite (cocktailParty (n + 3)) := by
  show ¬ IsBipartite (completeMultipartite (List.replicate (n + 3) 2))
  rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
  exact not_isBipartite_completeMultipartite 1 1 1 _

/-- The hub of a fan sees an edge of the path. -/
@[simp] theorem not_isBipartite_fan (n : ℕ) : ¬ IsBipartite (fan (n + 2)) := by
  show ¬ IsBipartite (complete 1 ∇g path (n + 2))
  rw [complete_def, path_def, join_mk, isBipartite_mk]
  refine CGraph.not_isBipartite_join_of_adj_right
    (a := (⟨0, by omega⟩ : (CGraph.path (n + 2)).V)) (b := ⟨1, by omega⟩) ?_ ⟨0, by omega⟩
  rw [CGraph.path_adj_val]
  exact ⟨by simp, Or.inl rfl⟩

/-! ### Bipartite double covers

The tensor product with `K₂` is the bipartite double cover.  Over a bipartite graph it comes apart
into two copies of the original — one application of the colouring built in the previous section —
and over an odd cycle it does not, giving the cycle of twice the length instead. -/

/-- **A double cover splits whenever the graph is 2-coloured**, for a graph presented as a
`CGraph` together with a colouring.  `tensorProduct_complete_two_of_isBipartite` is the same
statement with the colouring existentially quantified. -/
theorem tensorProduct_complete_two_of_colouring (G : CGraph) [DecidableEq G.V] (c : G.V → Bool)
    (h : ∀ x y, G.Adj x y = true → c x ≠ c y) :
    complete 2 ⊗g ⟦G⟧ = ⟦G⟧ ⊕g ⟦G⟧ := by
  rw [← empty_two_cartesianProduct ⟦G⟧, complete_def, tensorProduct_mk, empty_def,
    cartesianProduct_mk]
  exact Quotient.sound ⟨CGraph.Iso.tensorTwoOfColouring G c h⟩

/-- **The double cover of a bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    complete 2 ⊗g G = G ⊕g G := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [← mk_canonicalize G] at *
  obtain ⟨c, hc⟩ := h
  exact tensorProduct_complete_two_of_colouring _ c hc

theorem tensorProduct_complete_two_hypercube (n : ℕ) :
    complete 2 ⊗g hypercube n = hypercube n ⊕g hypercube n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_hypercube n)

theorem tensorProduct_complete_two_prism (m : ℕ) :
    complete 2 ⊗g prism (2 * m) = prism (2 * m) ⊕g prism (2 * m) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_prism_even m)

/-- **The double cover of a path is two paths.** -/
theorem tensorProduct_complete_two_path (n : ℕ) :
    complete 2 ⊗g path n = path n ⊕g path n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_path n)

/-- **The double cover of an even cycle is two cycles.** -/
theorem tensorProduct_complete_two_cycle (m : ℕ) :
    complete 2 ⊗g cycle (2 * m) = cycle (2 * m) ⊕g cycle (2 * m) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_cycle_even m)

/-- **The double cover of a complete bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_bipartite (m n : ℕ) :
    complete 2 ⊗g bipartite m n = bipartite m n ⊕g bipartite m n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_bipartite m n)

/-- The double cover of a star is two stars. -/
theorem tensorProduct_complete_two_star (n : ℕ) :
    complete 2 ⊗g star n = star n ⊕g star n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_star n)

/-- **The double cover of a ladder is two ladders.** -/
theorem tensorProduct_complete_two_ladder (n : ℕ) :
    complete 2 ⊗g ladder n = ladder n ⊕g ladder n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_ladder n)

/-- **The double cover of an odd cycle is one cycle of twice the length.**  The bound starts at
`C₃`: `cycle 1` is edgeless, so its double cover is too, while `cycle 2` is an edge. -/
theorem tensorProduct_complete_two_cycle_odd (m : ℕ) :
    complete 2 ⊗g cycle (2 * m + 3) = cycle (2 * (2 * m + 3)) := by
  rw [complete_def, cycle_def, tensorProduct_mk, cycle_def]
  exact Quotient.sound ⟨(CGraph.Iso.cycleTensorTwo m).symm⟩

theorem tensorProduct_complete_two_cycle_three :
    complete 2 ⊗g cycle 3 = cycle 6 :=
  tensorProduct_complete_two_cycle_odd 0

theorem tensorProduct_complete_two_cycle_five :
    complete 2 ⊗g cycle 5 = cycle 10 :=
  tensorProduct_complete_two_cycle_odd 1

end IsoGraph
