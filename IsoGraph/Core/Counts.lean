import IsoGraph.Core.Identities

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Order, size and degrees

Order, size and degrees of the core constructions: how many vertices and edges the complement, the
disjoint union, the join and the four products have, what their degree sequences and degree
multisets look like, and the handshaking lemma that ties the two together.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

/-! ### The empty graph -/

@[simp] theorem empty_toSimple (n : ℕ) : (empty n).toSimple = ⊥ := by
  ext i j
  simp

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := by
  simp [E]

@[simp] theorem degSequence_empty (n : ℕ) : (empty n).degSequence = List.replicate n 0 := by
  unfold CGraph.degSequence CGraph.degMultiset
  have hdeg : ∀ x : Fin n, (empty n).toSimple.degree x = 0 := by
    intro x
    rw [SimpleGraph.degree]
    simp [SimpleGraph.neighborFinset]
  have : ∀ v : Fin n, (empty n).toSimple.degree v = 0 := hdeg
  simp only [this]
  -- Step 1: The multiset Finset.univ.val has card n
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  -- Step 2: map of constant 0 on Finset.univ.val is replicate n 0
  have hms : Multiset.map (fun x : Fin n => (0 : ℕ)) (Finset.univ : Finset (Fin n)).val = Multiset.replicate n 0 := by
    have : ∀ (m : Multiset (Fin n)), Multiset.map (fun _ => (0 : ℕ)) m = Multiset.replicate m.card 0 := by
      intro m; induction m using Multiset.induction with
      | empty => simp
      | cons a s ih => simp [ih, Multiset.card_cons]
    rw [this]
    show Multiset.replicate ((Finset.univ : Finset (Fin n)).val.card) 0 = Multiset.replicate n 0
    rw [show (Finset.univ : Finset (Fin n)).val.card = (Finset.univ : Finset (Fin n)).card from rfl]
    rw [hcard]
  have hgoal : ((Multiset.map (fun x : Fin n => (0 : ℕ)) Finset.univ.val).sort
      (fun x1 x2 => x1 ≤ x2)) = ((Multiset.replicate n 0).sort (fun x1 x2 => x1 ≤ x2)) := by
    rw [hms]
  have goal : ∀ (a : ℕ) (n : ℕ), (Multiset.replicate n a).sort (fun x1 x2 => x1 ≤ x2) = List.replicate n a := by
    intro a n
    set s := (Multiset.replicate n a).sort (fun x1 x2 => x1 ≤ x2)
    have hsort_eq : s = (List.replicate n a).mergeSort (fun x1 x2 => decide (x1 ≤ x2)) := by
      rfl
    have hperm : s.Perm (List.replicate n a) := by
      rw [hsort_eq]
      exact List.mergeSort_perm _ _
    have hlength : s.length = n := by
      simpa [List.length_replicate] using hperm.length_eq
    have hall : ∀ x ∈ s, x = a := by
      intro x hx
      have hmem := hperm.subset hx
      exact Multiset.eq_of_mem_replicate hmem
    have hsorted_aux : ∀ (l : List ℕ), (∀ x ∈ l, x = a) → List.Pairwise (· ≤ ·) l := by
      intro l hall; induction l with
      | nil => trivial
      | cons hd tl ih =>
        simp [List.pairwise_cons]
        refine ⟨fun x hx => ?_, ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))⟩
        rw [hall x (List.mem_cons_of_mem _ hx), hall hd List.mem_cons_self]
    have hsorted_s := hsorted_aux s hall
    have huv : ∀ (l : List ℕ), (∀ x ∈ l, x = a) → List.Pairwise (· ≤ ·) l →
        l = List.replicate l.length a := by
      intro l hall hsort
      induction l with
      | nil => simp
      | cons hd tl ihl =>
        have hdal := hall hd List.mem_cons_self
        have htllen : ∀ x ∈ tl, x = a := fun x hxtl => hall x (List.mem_cons_of_mem _ hxtl)
        have hsort_tl : List.Pairwise (· ≤ ·) tl := hsort.tail
        have h1 : a :: List.replicate tl.length a = List.replicate (tl.length + 1) a := by
          rw [List.replicate_succ]
        rw [ihl htllen hsort_tl, hdal, h1]
        simp [List.length_replicate]
    rw [huv s hall hsorted_s, hlength]
  refine Eq.trans ?_ (hgoal.trans (goal 0 n))
  exact congrArg (fun s : Finset (Fin n) ↦ (Multiset.map (fun _ ↦ (0 : ℕ)) s.val).sort (· ≤ ·))
    (Finset.univ_inst_eq _ _)

/-! ### The complement -/

@[simp] theorem compl_toSimple : Gᶜ.toSimple = G.toSimpleᶜ := by
  ext x y
  simp [G.symm x y, SimpleGraph.compl_adj]

/-- A graph and its complement share out all the pairs between them. -/
theorem E_compl :
    Gᶜ.E + G.E = (FinEnum.card G.V).choose 2 := by
  simp only [CGraph.E]
  have h1 : Gᶜ.toSimple.edgeFinset = G.toSimpleᶜ.edgeFinset := by
    simp [compl_toSimple]
  rw [h1]
  have h_disj : Disjoint G.toSimple.edgeFinset G.toSimpleᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [SimpleGraph.mem_edgeFinset] at hx hxc
    induction x using Sym2.ind with
    | h v w =>
      rw [SimpleGraph.mem_edgeSet] at hx hxc
      rw [SimpleGraph.compl_adj] at hxc
      exact absurd hx hxc.2
  have h_union : G.toSimple.edgeFinset ∪ G.toSimpleᶜ.edgeFinset = (⊤ : SimpleGraph G.V).edgeFinset := by
    ext e
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    show (e ∈ G.toSimple.edgeSet ∨ e ∈ G.toSimpleᶜ.edgeSet) ↔ e ∈ (⊤ : SimpleGraph G.V).edgeSet
    constructor
    · rintro (h | h)
      · exact SimpleGraph.edgeSet_mono le_top h
      · exact SimpleGraph.edgeSet_mono le_top h
    · intro h
      by_cases he : e ∈ G.toSimple.edgeSet
      · exact Or.inl he
      · exact Or.inr (by
          show e ∈ G.toSimpleᶜ.edgeSet
          induction e using Sym2.ind with
          | h v w =>
            simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj] at he ⊢
            have hvne : v ≠ w := by
              by_contra h'
              rw [h'] at h
              simp at h
            exact ⟨hvne, he⟩)
  have h_card : G.toSimpleᶜ.edgeFinset.card + G.toSimple.edgeFinset.card =
    (⊤ : SimpleGraph G.V).edgeFinset.card := by
    have := Finset.card_union_of_disjoint (h_disj.symm)
    rw [Finset.union_comm] at this
    rw [← this, h_union]
  rw [h_card, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    ← FinEnum.card_eq_fintypeCard]

/-- Everything is reflexively adjacent in a complete graph; this is `adjR` (see the reflexive
exponential, above) but it has to wait for `complete_adj`. -/
@[simp] theorem adjR_complete (n : ℕ) (x y : (complete n).V) : (complete n).adjR x y = true := by
  by_cases h : x = y <;> simp [adjR, h]

@[simp] theorem complete_toSimple (n : ℕ) : (complete n).toSimple = ⊤ := by
  simp [complete]

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := by
  have h : (complete n).E = Fintype.card ↥(⊤ : SimpleGraph (Fin n)).edgeSet := by
    simp [E, SimpleGraph.edgeFinset_card]
    congr!
  rw [h, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

@[simp] theorem degSequence_complete (n : ℕ) :
    (complete n).degSequence = List.replicate n (n - 1) := by
  have htosimple : (complete n).toSimple = SimpleGraph.completeGraph (Fin n) := by
    ext x y
    simp [CGraph.toSimple, complete, empty_adj]
  show (complete n).degSequence = _
  have hdeg : ∀ v : (complete n).V, (complete n).toSimple.degree v = n - 1 := by
    intro v
    simp [htosimple, SimpleGraph.degree, SimpleGraph.neighborFinset]
    have : (Finset.univ.filter (fun x : Fin n => x ≠ v)).card = n - 1 := by
      simp [Finset.filter_ne', Fintype.card_fin]
    convert this using 1
    congr 1; ext x; simp [ne_eq, eq_comm]
  unfold CGraph.degSequence CGraph.degMultiset
  rw [show (fun v : (complete n).V => (complete n).toSimple.degree v) = fun _ => n - 1 from funext hdeg]
  have hcard : Multiset.card (Finset.univ : Finset (complete n).V).val = n := by
    have h1 : (Finset.univ : Finset (complete n).V).card = FinEnum.card (complete n).V :=
      FinEnum.card_univ
    rw [Finset.card_val, h1, card_complete]
  have h1 : Multiset.map (fun x : (complete n).V => n - 1) (Finset.univ : Finset (complete n).V).val = Multiset.replicate n (n - 1) := by
    have hmap : ∀ (s : Multiset (complete n).V) (a : ℕ),
        Multiset.map (fun _ : (complete n).V => a) s = Multiset.replicate (Multiset.card s) a := by
      intro s a; induction s using Multiset.induction with
      | empty => simp
      | cons b s ih => simp [ih, Multiset.replicate_succ]
    rw [hmap, hcard]
  rw [h1]
  let L := (Multiset.replicate n (n - 1)).sort (fun x1 x2 => x1 ≤ x2)
  have hofL : Multiset.ofList L = Multiset.replicate n (n - 1) := Multiset.sort_eq _ _
  have hsorted : ∀ {l : List ℕ} {m a : ℕ}, List.Pairwise (· ≤ ·) l → (∀ x ∈ l, x = a) → l.length = m → l = List.replicate m a := by
    intro l m a hpair hine hlen
    induction l generalizing m a with
    | nil =>
      rw [List.length_nil] at hlen; subst hlen; rfl
    | cons b l ih =>
      simp [List.mem_cons, List.length] at hine hlen
      have hb : b = a := hine.1
      have pile : List.Pairwise (fun x1 x2 => x1 ≤ x2) l := hpair.tail
      have hinel : ∀ x ∈ l, x = a := hine.2
      have hllen : l.length = m - 1 := by omega
      rw [hb, ih pile hinel hllen]
      rcases m with _ | m <;> simp [List.replicate] at hlen ⊢
  have hpair : List.Pairwise (fun x1 x2 => x1 ≤ x2) L := by
    exact Multiset.pairwise_sort (Multiset.replicate n (n - 1)) (fun x1 x2 => x1 ≤ x2)
  have hine : ∀ x ∈ L, x = n - 1 := by
    intro x hx
    have hmem : x ∈ (Multiset.replicate n (n - 1) : Multiset ℕ) := by
      rwa [← hofL, Multiset.mem_coe]
    rw [Multiset.mem_replicate] at hmem; exact hmem.2
  have hlen : L.length = n := by
    have h1 := congr_arg Multiset.card hofL
    simp [Multiset.card_replicate] at h1
    rwa [show L.length = Multiset.card (L : Multiset ℕ) from by rfl] at h1 ⊢
  exact hsorted hpair hine hlen

/-! ### Paths and cycles -/

@[simp] theorem path_toSimple (n : ℕ) : (path n).toSimple = SimpleGraph.pathGraph n := by
  ext i j
  simp only [toSimple_adj, path, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, SimpleGraph.pathGraph_adj, ne_eq, Fin.ext_iff]
  omega

/-- Adjacency in `cycle n`, phrased entirely in terms of the underlying naturals. -/
theorem cycle_adj_val (n : ℕ) (u v : (cycle n).V) :
    (cycle n).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1 + 1) % n = v.1 ∨ (v.1 + 1) % n = u.1)) := by
  have huv : (u = v) ↔ (u.1 = v.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
  simp only [cycle, ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ne_eq, huv]

/-- **Every vertex of a cycle has exactly two neighbours**: the label one step forward and the
label one step back. -/
theorem neighborFinset_cycle (n : ℕ) (v : Fin (n + 3)) :
    (cycle (n + 3)).toSimple.neighborFinset v = {v + 1, v + ⟨n + 2, by omega⟩} := by
  have hnext : ∀ x : Fin (n + 3), ((x + 1 : Fin (n + 3)) : ℕ) = (x.1 + 1) % (n + 3) := fun x ↦ by
    simp [Fin.val_add]
  have hprev : ∀ x : Fin (n + 3), ((x + ⟨n + 2, by omega⟩ : Fin (n + 3)) : ℕ)
      = (x.1 + (n + 2)) % (n + 3) := fun x ↦ by simp [Fin.val_add]
  -- Reduce every `%` in sight: the numerators here are all below `2 * (n + 3)`.
  have hlo : ∀ a : ℕ, a < n + 3 → a % (n + 3) = a := fun a h ↦ Nat.mod_eq_of_lt h
  have hhi : ∀ a : ℕ, n + 3 ≤ a → a < 2 * (n + 3) → a % (n + 3) = a - (n + 3) := by
    intro a h1 h2
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  -- "One step forward from `x` is `y`" and "one step back from `y` is `x`" say the same thing.
  have hback : ∀ x y : Fin (n + 3),
      (x.1 + 1) % (n + 3) = y.1 ↔ x.1 = (y.1 + (n + 2)) % (n + 3) := by
    intro x y
    have hx := x.isLt
    have hy := y.isLt
    rcases lt_or_ge (x.1 + 1) (n + 3) with h | h
    · rw [hlo _ h]
      rcases lt_or_ge (y.1 + (n + 2)) (n + 3) with h2 | h2
      · rw [hlo _ h2]; omega
      · rw [hhi _ h2 (by omega)]; omega
    · rw [hhi _ h (by omega)]
      rcases lt_or_ge (y.1 + (n + 2)) (n + 3) with h2 | h2
      · rw [hlo _ h2]; omega
      · rw [hhi _ h2 (by omega)]; omega
  have heq1 : ∀ u : Fin (n + 3), u = v + 1 ↔ u.1 = (v.1 + 1) % (n + 3) := by
    intro u; rw [Fin.ext_iff, hnext]
  have heq2 : ∀ u : Fin (n + 3),
      u = v + ⟨n + 2, by omega⟩ ↔ u.1 = (v.1 + (n + 2)) % (n + 3) := by
    intro u; rw [Fin.ext_iff, hprev]
  have hv := v.isLt
  ext u
  simp only [SimpleGraph.mem_neighborFinset, toSimple_adj, Finset.mem_insert, Finset.mem_singleton,
    heq1, heq2]
  rw [cycle_adj_val]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h.symm
    · exact Or.inr ((hback u v).1 h)
  · have hu := u.isLt
    rintro (h | h)
    · refine ⟨fun hvu ↦ ?_, Or.inl h.symm⟩
      rcases lt_or_ge (v.1 + 1) (n + 3) with h' | h'
      · rw [hlo _ h'] at h; omega
      · rw [hhi _ h' (by omega)] at h; omega
    · refine ⟨fun hvu ↦ ?_, Or.inr ((hback u v).2 h)⟩
      rcases lt_or_ge (v.1 + (n + 2)) (n + 3) with h' | h'
      · rw [hlo _ h'] at h; omega
      · rw [hhi _ h' (by omega)] at h; omega

private theorem degree_cycle_fin (n : ℕ) (v : Fin (n + 3)) :
    (cycle (n + 3)).toSimple.degree v = 2 := by
  have hne : (v + 1 : Fin (n + 3)) ≠ v + ⟨n + 2, by omega⟩ := fun h ↦ by
    have h2 := congrArg Fin.val (add_left_cancel h)
    simp at h2
  rw [SimpleGraph.degree, neighborFinset_cycle, Finset.card_pair hne]

/-- **A cycle is two-regular.** -/
theorem degree_cycle (n : ℕ) (v : (cycle (n + 3)).V) :
    (cycle (n + 3)).toSimple.degree v = 2 := degree_cycle_fin n v

/-- **A cycle has as many edges as vertices**: it is two-regular, so the handshake lemma counts
each of the `n + 3` vertices twice. -/
@[simp] theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := by
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges (cycle (n + 3)).toSimple
  simp only [degree_cycle, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
  rw [show Fintype.card (cycle (n + 3)).V = n + 3 by simp] at h2
  show (cycle (n + 3)).toSimple.edgeFinset.card = n + 3
  omega

/-! ### Disjoint unions and joins -/

theorem nbrs_disjUnion_inl (G H : CGraph) (a : G.V) :
    (G ⊕g H).nbrs (Sum.inl a) = (G.nbrs a).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem nbrs_disjUnion_inr (G H : CGraph) (b : H.V) :
    (G ⊕g H).nbrs (Sum.inr b) = (H.nbrs b).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem degree_disjUnion_inl (G H : CGraph) (a : G.V) :
    (G ⊕g H).toSimple.degree (Sum.inl a) = G.toSimple.degree a := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_disjUnion_inl, Finset.card_map]

theorem degree_disjUnion_inr (G H : CGraph) (b : H.V) :
    (G ⊕g H).toSimple.degree (Sum.inr b) = H.toSimple.degree b := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_disjUnion_inr, Finset.card_map]

/-- **A disjoint union has the edges of both its parts**: every vertex keeps the degree it had,
so the handshake lemma splits along the sum. -/
@[simp] theorem E_disjUnion : (G ⊕g H).E = G.E + H.E := by
  have hsum : ∑ w : (G ⊕g H).V, (G ⊕g H).toSimple.degree w =
      (∑ u : G.V, (G ⊕g H).toSimple.degree (Sum.inl u)) +
        ∑ v : H.V, (G ⊕g H).toSimple.degree (Sum.inr v) :=
    (Finset.sum_univ_inst_eq _ (instFintypeSum G.V H.V) _).trans (Fintype.sum_sum_type _)
  simp only [degree_disjUnion_inl, degree_disjUnion_inr] at hsum
  have h1 := SimpleGraph.sum_degrees_eq_twice_card_edges (G ⊕g H).toSimple
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple
  have h3 := SimpleGraph.sum_degrees_eq_twice_card_edges H.toSimple
  show (G ⊕g H).toSimple.edgeFinset.card
    = G.toSimple.edgeFinset.card + H.toSimple.edgeFinset.card
  omega

@[simp] theorem E_join :
    (G ∇g H).E = G.E + H.E + FinEnum.card G.V * FinEnum.card H.V := by
  have h1 : (G ∇g H).E + (Gᶜ ⊕g Hᶜ).E = (FinEnum.card (G ∇g H).V).choose 2 := by
    rw [join_eq_compl_disjUnion]
    exact E_compl _
  have h2 : (Gᶜ ⊕g Hᶜ).E = Gᶜ.E + Hᶜ.E := E_disjUnion _ _
  have h3 : Gᶜ.E + G.E = (FinEnum.card G.V).choose 2 := E_compl G
  have h4 : Hᶜ.E + H.E = (FinEnum.card H.V).choose 2 := E_compl H
  have h5 : FinEnum.card (G ∇g H).V = FinEnum.card G.V + FinEnum.card H.V := card_join G H
  rw [h5] at h1
  rw [h2] at h1
  have h_choose : ∀ (m n : ℕ), (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 from by omega]
      rw [Nat.choose_succ_succ]
      have hchoose1 : (m + n).choose 1 = m + n := by simp
      rw [hchoose1]
      rw [Nat.choose_succ_succ]
      rw [Nat.choose_one_right]
      linarith
  rw [h_choose] at h1
  linarith [h3, h4]

/-! ### Products -/

@[simp] theorem E_cartesianProduct :
    (G □g H).E = FinEnum.card G.V * H.E + FinEnum.card H.V * G.E := by
  dsimp only [CGraph.E]
  -- Step 1: Show that toSimple of cartesianProduct equals SimpleGraph.prodCartesian
  have huv : ∀ p q : G.V × H.V, (G □g H).toSimple.Adj p q ↔
      (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2) := by
    intro p q
    simp only [cartesianProduct_adj, CGraph.toSimple_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  -- Handshaking lemma for cartesianProduct
  have hhand_CP : ∑ v : G.V × H.V, (G □g H).toSimple.degree v =
      FinEnum.card H.V * ∑ g : G.V, G.toSimple.degree g + FinEnum.card G.V * ∑ h : H.V, H.toSimple.degree h := by
    have hdeg : ∀ g : G.V, ∀ h : H.V,
        (G □g H).toSimple.degree (g, h) = G.toSimple.degree g + H.toSimple.degree h := by
      intro g h
      have hns_finset : (G □g H).toSimple.neighborFinset (g, h) =
          Finset.image (fun h' => (g, h')) (H.toSimple.neighborFinset h) ∪
          Finset.image (fun g' => (g', h)) (G.toSimple.neighborFinset g) := by
        ext ⟨g', h'⟩
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image]
        rw [huv]
        constructor
        · rintro (⟨heq, hadj⟩ | ⟨hadj, heq⟩)
          · exact Or.inl ⟨h', hadj, Prod.ext heq rfl⟩
          · exact Or.inr ⟨g', hadj, Prod.ext rfl heq⟩
        · rintro (h | h)
          · obtain ⟨a, hadj, heq⟩ := h
            have h1 : g = g' := congr_arg Prod.fst heq
            have h2 : a = h' := congr_arg Prod.snd heq
            subst h1; subst h2; exact Or.inl ⟨rfl, hadj⟩
          · obtain ⟨a, hadj, heq⟩ := h
            have h1 : a = g' := congr_arg Prod.fst heq
            have h2 : h = h' := congr_arg Prod.snd heq
            subst h1; subst h2; exact Or.inr ⟨hadj, rfl⟩
      rw [SimpleGraph.degree, hns_finset, SimpleGraph.degree, SimpleGraph.degree]
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
        · ring
        · exact fun a b h => by injection h
        · exact fun a b h => by injection h
      · rw [Finset.disjoint_left]
        intro x hx hy
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨b, hb, hb'⟩
        have heq' : (b, h) = (g, a) := hb'
        have hb_eq_g : b = g := congr_arg Prod.fst heq'
        have hh_eq_a : h = a := congr_arg Prod.snd heq'
        subst hb_eq_g; subst hh_eq_a
        simp [SimpleGraph.mem_neighborFinset] at ha
    -- `Fintype.sum_prod_type` first: rewriting the degree before splitting the sum leaves the
    -- pair inside the `Fintype (neighborSet …)` instance, and the inner summand is then not
    -- constant in the second component.
    rw [Fintype.sum_prod_type,
      Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun h _ ↦ hdeg g h]
    simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.card_univ,
      ← FinEnum.card_eq_fintypeCard]
  -- Use handshaking lemma
  have hhand : 2 * (G □g H).toSimple.edgeFinset.card =
      ∑ v : G.V × H.V, (G □g H).toSimple.degree v :=
    ((SimpleGraph.sum_degrees_eq_twice_card_edges (G := (G □g H).toSimple)).symm).trans
      (Finset.sum_univ_inst_eq _ _ _)
  have hhand_G : ∑ g : G.V, G.toSimple.degree g = 2 * G.toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple
  have hhand_H : ∑ h : H.V, H.toSimple.degree h = 2 * H.toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H.toSimple
  rw [hhand_CP] at hhand
  rw [hhand_G, hhand_H] at hhand
  linarith

@[simp] theorem E_tensorProduct :
    (G ⊗g H).E = 2 * G.E * H.E := by
  simp only [CGraph.E]
  have hadj : ∀ (p q : G.V × H.V), (G.tensorProduct H).toSimple.Adj p q ↔ G.Adj p.1 q.1 = true ∧ H.Adj p.2 q.2 = true := by
    intro ⟨v1, v2⟩ ⟨w1, w2⟩
    simp [tensorProduct_adj, CGraph.toSimple_adj]
  have hdeg : ∀ (g : G.V) (h : H.V),
      (G.tensorProduct H).toSimple.degree (g, h) = G.toSimple.degree g * H.toSimple.degree h := by
    intro g h
    simp only [SimpleGraph.degree]
    set NGfinset := G.toSimple.neighborFinset g
    set NHfinset := H.toSimple.neighborFinset h
    have hfinset : (G.tensorProduct H).toSimple.neighborFinset (g, h) = NGfinset ×ˢ NHfinset := by
      ext ⟨g', h'⟩
      simp only [SimpleGraph.mem_neighborFinset]
      rw [hadj, Finset.mem_product]
      simp [NGfinset, NHfinset, SimpleGraph.mem_neighborFinset]
    rw [hfinset, Finset.card_product]
  -- The vertex type of tensorProduct is G.V × H.V (definitionally)
  -- Sum of degrees in tensor product (over its vertex type)
  have hsum_tensor : ∑ p : (G ⊗g H).V, (G ⊗g H).toSimple.degree p = 2 * (G ⊗g H).toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  -- Rewrite sum over tensorProduct vertices as sum over G.V × H.V
  have hsum_reindex : ∑ p : (G ⊗g H).V, (G ⊗g H).toSimple.degree p =
    ∑ p : G.V × H.V, G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
    have : ∀ p : (G ⊗g H).V, (G ⊗g H).toSimple.degree p =
      G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
      rintro ⟨g, h⟩
      exact hdeg g h
    rw [Finset.sum_congr rfl (fun p _ => this p)]
    exact Finset.sum_univ_inst_eq _ _ _
  -- Factor the double sum using Finset.sum_product'
  have hfactor : ∑ p : G.V × H.V, G.toSimple.degree p.1 * H.toSimple.degree p.2 =
    (∑ g : G.V, G.toSimple.degree g) * (∑ h : H.V, H.toSimple.degree h) := by
    calc ∑ p : G.V × H.V, G.toSimple.degree p.1 * H.toSimple.degree p.2
        = ∑ g : G.V, ∑ h : H.V, G.toSimple.degree g * H.toSimple.degree h := by
          rw [show (Finset.univ : Finset (G.V × H.V)) = Finset.univ ×ˢ Finset.univ from rfl]
          rw [Finset.sum_product]
      _ = (∑ g : G.V, G.toSimple.degree g) * (∑ h : H.V, H.toSimple.degree h) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun g _ => Finset.mul_sum _ _ _ |>.symm)
  -- Handshaking for G and H
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple] at hfactor
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges H.toSimple] at hfactor
  -- Now: 2 * |E(tensor)| = 2 * |E(G)| * (2 * |E(H)|), so |E(tensor)| = 2 * |E(G)| * |E(H)|
  linarith

@[simp] theorem card_lineGraph : FinEnum.card (lineGraph G).V = G.E := by
  rw [E, SimpleGraph.edgeFinset_card, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_congr' rfl


/-- **Adjacency in a line graph**, as a `SimpleGraph`: two distinct edges sharing an endpoint. -/
theorem lineGraph_toSimple_adj (e f : (lineGraph G).V) :
    (lineGraph G).toSimple.Adj e f ↔
      e ≠ f ∧ ∃ v : G.V, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V) := by
  simp [CGraph.toSimple, CGraph.lineGraph_adj, Bool.and_eq_true]

/-- A vertex of a line graph is an edge of the original, so it has an endpoint. -/
theorem exists_mem_lineGraph_vertex (e : (lineGraph G).V) : ∃ v : G.V, v ∈ (e.1 : Sym2 G.V) := by
  obtain ⟨se, _⟩ := e
  induction se using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left _ _⟩

/-- **Two edges sharing an endpoint are at distance at most one in the line graph.** -/
theorem edist_lineGraph_le_one (e f : (lineGraph G).V) (v : G.V)
    (hev : v ∈ (e.1 : Sym2 G.V)) (hfv : v ∈ (f.1 : Sym2 G.V)) :
    (lineGraph G).toSimple.edist e f ≤ 1 := by
  by_cases heq : e = f
  · rw [heq]; simp
  · exact le_trans (SimpleGraph.Walk.edist_le (SimpleGraph.Walk.cons
      ((lineGraph_toSimple_adj G e f).2 ⟨heq, v, hev, hfv⟩) SimpleGraph.Walk.nil)) (by simp)

/-- **A walk lifts to the line graph**: a walk from `u` to `v` and an edge `e` at `u` produce an
edge `e'` at `v` no further from `e` than the walk is long.  Each step of the walk moves to the
edge it traverses, which shares its tail with the edge reached before it. -/
theorem exists_edist_lineGraph_le_length : ∀ {u v : G.V} (w : G.toSimple.Walk u v)
    (e : (lineGraph G).V), u ∈ (e.1 : Sym2 G.V) →
      ∃ e' : (lineGraph G).V, v ∈ (e'.1 : Sym2 G.V) ∧
        (lineGraph G).toSimple.edist e e' ≤ w.length := by
  intro u v w e hu
  induction w using SimpleGraph.Walk.rec generalizing e with
  | nil => exact ⟨e, hu, by rw [SimpleGraph.edist_self]; simp⟩
  | @cons x y z hxy wtail ih =>
    let ep : (lineGraph G).V :=
      ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] using hxy⟩
    obtain ⟨e', hz, hd⟩ := ih ep (Sym2.mem_mk_right _ _)
    refine ⟨e', hz, le_trans ((lineGraph G).toSimple.edist_triangle.trans
      (add_le_add (edist_lineGraph_le_one G e ep x hu (Sym2.mem_mk_left _ _)) hd)) ?_⟩
    show (1 : ℕ∞) + ↑wtail.length ≤ ↑(wtail.length + 1)
    simp [Nat.cast_add, add_comm]

/-- The degree of an edge `e` in `lineGraph G`: each endpoint `v` of `e` contributes the
`G.degree v - 1` other edges incident to `v`, and no edge is counted twice because two
distinct endpoints cannot both lie on a third edge. -/
theorem degree_lineGraph (e : (lineGraph G).V) :
    (lineGraph G).toSimple.degree e = ∑ v ∈ e.1.toFinset, (G.toSimple.degree v - 1) := by
  set S := G.toSimple
  have heqmem : ∀ e : Sym2 G.V, e ∈ S.edgeSet ↔ e ∈ S.edgeFinset := by
    intro e; simp [SimpleGraph.mem_edgeFinset]
  rw [SimpleGraph.degree]
  set ee := e.1
  have hee_mem : ee ∈ S.edgeFinset := (heqmem ee).mp e.2
  have hneighbor_val :
    Finset.image (fun f : (lineGraph G).V => f.1) (G.lineGraph.toSimple.neighborFinset e) =
    Finset.filter (fun f => f ≠ ee ∧ ∃ v ∈ ee.toFinset, v ∈ f.toFinset) S.edgeFinset := by
    ext f
    simp [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · rintro ⟨a, hadj, ha⟩
      subst ha
      have hadj' : e ≠ a ∧ ∃ v, v ∈ ee ∧ v ∈ a.1 :=
        (lineGraph_toSimple_adj G e a).mp (by simpa using hadj)
      exact ⟨a.2, fun h => hadj'.1 (Subtype.ext (h.symm)), hadj'.2⟩
    · rintro ⟨hf1, hf2, v, hv1, hv2⟩
      have hf1' : f ∈ S.edgeFinset := (heqmem f).mp hf1
      let fe : (lineGraph G).V := ⟨f, (heqmem f).mpr hf1'⟩
      have hne : e ≠ fe := fun h => hf2 ((congr_arg Subtype.val h).symm)
      have hmem : ∃ w : G.V, w ∈ e.1 ∧ w ∈ fe.1 := ⟨v, hv1, hv2⟩
      exact ⟨fe, ⟨hne, hmem⟩, rfl⟩
  have hcard_eq : (G.lineGraph.toSimple.neighborFinset e).card =
      ({f ∈ S.edgeFinset | f ≠ ee ∧ ∃ v ∈ ee.toFinset, v ∈ f.toFinset}).card := by
    rw [← hneighbor_val]
    exact (Finset.card_image_of_injective _ Subtype.coe_injective).symm
  rw [hcard_eq]
  -- Split the other edges at `ee` by which endpoint of `ee` they meet.
  have hdecomp : {f ∈ S.edgeFinset | f ≠ ee ∧ ∃ v ∈ ee.toFinset, v ∈ f.toFinset} =
      Finset.biUnion ee.toFinset (fun v => S.incidenceFinset v \ {ee}) := by
    ext f
    simp [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter,
          SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨hf1, hf2, a, ha, havf⟩
      exact ⟨a, ha, ⟨hf1, havf⟩, hf2⟩
    · rintro ⟨a, ha, hfa, hf2⟩
      exact ⟨hfa.1, hf2, a, ha, hfa.2⟩
  rw [hdecomp, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun v hv ↦ ?_
    have hEE : ee ∈ S.incidenceFinset v := by
      rw [S.mem_incidenceFinset]
      exact ⟨(heqmem ee).mpr hee_mem, Sym2.mem_toFinset.mp hv⟩
    have hsubset : {ee} ⊆ S.incidenceFinset v := Finset.singleton_subset_iff.mpr hEE
    have hcard_v : (S.incidenceFinset v).card = S.degree v :=
      S.card_incidenceFinset_eq_degree v
    rw [Finset.card_sdiff_of_subset hsubset, Finset.card_singleton, hcard_v]
  -- The pieces are disjoint: an edge meeting both endpoints of `ee` *is* `ee`.
  · intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro f hfv hfw
    simp [Finset.mem_sdiff, Finset.mem_singleton] at hfv hfw
    obtain ⟨⟨-, hvf⟩, hfne⟩ := hfv
    obtain ⟨⟨-, hwf⟩, -⟩ := hfw
    exact hfne (Sym2.eq_of_ne_mem hvw hvf hwf (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hw))
@[simp] theorem E_lineGraph :
    (lineGraph G).E = (∑ v : G.V, (G.toSimple.degree v).choose 2) := by
  set S := G.toSimple
  show (lineGraph G).toSimple.edgeFinset.card = ∑ v, (S.degree v).choose 2
  -- Key fact: (lineGraph G).toSimple.Adj x y ↔ x ≠ y ∧ ∃ v, v ∈ ↑x ∧ v ∈ ↑y
  -- Handshaking
  have hhand : 2 * (lineGraph G).toSimple.edgeFinset.card =
      ∑ e : (lineGraph G).V, (lineGraph G).toSimple.degree e :=
    (SimpleGraph.sum_degrees_eq_twice_card_edges (lineGraph G).toSimple).symm
  -- Build equivalence between (lineGraph G).V and S.edgeFinset
  have heqmem : ∀ e : Sym2 G.V, e ∈ S.edgeSet ↔ e ∈ S.edgeFinset := by
    intro e; simp [SimpleGraph.mem_edgeFinset]
  let vequiv : (lineGraph G).V ≃ S.edgeFinset :=
    { toFun := fun x => ⟨x.1, (heqmem x.1).mp x.2⟩
      invFun := fun e => ⟨e.1, (heqmem e.1).mpr e.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun e => Subtype.ext rfl }
  -- For each edge e of G (vertex of lineGraph G), its degree in LG
  have hdeg : ∀ e : (lineGraph G).V,
      (lineGraph G).toSimple.degree e = ∑ v ∈ e.1.toFinset, (S.degree v - 1) :=
    fun e ↦ degree_lineGraph G e
  -- Sum of degrees in LG = ∑ e ∈ E(G), ∑ v ∈ e, (deg(v) - 1)
  have hsum_deg : ∑ e : (lineGraph G).V, (lineGraph G).toSimple.degree e =
      ∑ e ∈ S.edgeFinset, ∑ v ∈ e.toFinset, (S.degree v - 1) := by
    rw [Finset.sum_congr rfl fun e _ => hdeg e]
    rw [← Finset.sum_coe_sort S.edgeFinset]
    rw [← Equiv.sum_comp vequiv]
    simp [vequiv]
  -- Double counting
  have hdouble : ∑ e ∈ S.edgeFinset, ∑ v ∈ e.toFinset, (S.degree v - 1) =
      ∑ v : G.V, ∑ e ∈ S.incidenceFinset v, (S.degree v - 1) := by
    have hfilter : ∀ v : G.V, Finset.filter (fun e => v ∈ e.toFinset) S.edgeFinset = S.incidenceFinset v := by
      intro v
      ext e
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet]
    have step1 : ∀ e ∈ S.edgeFinset, ∑ v ∈ e.toFinset, (S.degree v - 1) =
        ∑ v : G.V, if v ∈ e.toFinset then (S.degree v - 1) else 0 := by
      intro e he
      simp [Finset.sum_ite]
      rw [show (∑ v with v ∈ e, (S.degree v - 1)) = ∑ v ∈ (Finset.univ.filter (fun v => v ∈ e)), (S.degree v - 1) from rfl]
      rw [show Finset.univ.filter (fun v => v ∈ e) = e.toFinset from by ext v; simp [Sym2.mem_toFinset]]
    rw [Finset.sum_congr rfl step1, Finset.sum_comm]
    rw [Finset.sum_congr rfl]
    intro v _
    rw [← hfilter v, Finset.sum_filter]
  -- Inner sum
  have hinner : ∀ v, ∑ e ∈ S.incidenceFinset v, (S.degree v - 1) = S.degree v * (S.degree v - 1) := by
    intro v
    rw [Finset.sum_const, smul_eq_mul]
    have hcard : (S.incidenceFinset v).card = S.degree v :=
      S.card_incidenceFinset_eq_degree v
    rw [hcard]
  have Halle : ∑ v : G.V, S.degree v * (S.degree v - 1) =
      2 * ∑ v : G.V, (S.degree v).choose 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.choose_two_right]
    have h2 : 2 ∣ S.degree v * (S.degree v - 1) := by
      rcases Nat.even_or_odd (S.degree v) with h | h
      · exact h.two_dvd.mul_right _
      · obtain ⟨k, hk⟩ := h
        rw [hk]
        exact dvd_mul_of_dvd_right (by omega) _
    omega
  have hchain : 2 * (lineGraph G).toSimple.edgeFinset.card =
      2 * ∑ v, (S.degree v).choose 2 := by
    rw [hhand, hsum_deg, hdouble, Finset.sum_congr rfl fun v _ => hinner v, Halle]
  exact mul_left_cancel₀ two_ne_zero hchain

@[simp] theorem card_mycielskian :
    FinEnum.card (mycielskian G).V = 2 * FinEnum.card G.V + 1 := by
  simp [mycielskian, two_mul]

private theorem some_inl_inj {K : CGraph} :
    Function.Injective (fun b : K.V ↦ (some (Sum.inl b) : Option (K.V ⊕ K.V))) :=
  fun _ _ h ↦ Sum.inl_injective (Option.some_injective (K.V ⊕ K.V) h)

private theorem some_inr_inj {K : CGraph} :
    Function.Injective (fun b : K.V ↦ (some (Sum.inr b) : Option (K.V ⊕ K.V))) :=
  fun _ _ h ↦ Sum.inr_injective (Option.some_injective (K.V ⊕ K.V) h)

/-- The neighbours of an original vertex of a Mycielskian: its old neighbours and their shadows. -/
theorem neighborFinset_mycielskian_inl (a : G.V) :
    (mycielskian G).toSimple.neighborFinset (some (Sum.inl a)) =
      (Finset.image (fun b : G.V ↦ some (Sum.inl b)) (G.toSimple.neighborFinset a) ∪
        Finset.image (fun b : G.V ↦ some (Sum.inr b)) (G.toSimple.neighborFinset a)) := by
  ext y
  simp [mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
  rcases y with _ | y | y <;> simp

/-- The neighbours of a shadow vertex: the neighbours of the vertex it shadows, and the apex. -/
theorem neighborFinset_mycielskian_inr (a : G.V) :
    (mycielskian G).toSimple.neighborFinset (some (Sum.inr a)) =
      Finset.image (fun b : G.V ↦ some (Sum.inl b)) (G.toSimple.neighborFinset a) ∪ {none} := by
  ext y
  simp [mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
  rcases y with _ | y | y <;> simp

/-- The apex of a Mycielskian sees exactly the shadows. -/
theorem neighborFinset_mycielskian_none :
    (mycielskian G).toSimple.neighborFinset none =
      Finset.image (fun b : G.V ↦ some (Sum.inr b)) Finset.univ := by
  ext y
  simp [mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
  rcases y with _ | y | y <;> simp

/-- **An original vertex of a Mycielskian has twice its old degree**: it keeps its old neighbours
and gains their shadows. -/
theorem degree_mycielskian_inl (a : G.V) :
    (mycielskian G).toSimple.degree (some (Sum.inl a)) = 2 * G.toSimple.degree a := by
  rw [SimpleGraph.degree, neighborFinset_mycielskian_inl, Finset.card_union_of_disjoint
    (by rw [Finset.disjoint_left]; simp [Finset.mem_image]),
    Finset.card_image_of_injective _ some_inl_inj,
    Finset.card_image_of_injective _ some_inr_inj, SimpleGraph.degree]
  ring

/-- **A shadow vertex has the degree of the vertex it shadows, plus one** for the apex. -/
theorem degree_mycielskian_inr (a : G.V) :
    (mycielskian G).toSimple.degree (some (Sum.inr a)) = G.toSimple.degree a + 1 := by
  rw [SimpleGraph.degree, neighborFinset_mycielskian_inr, Finset.card_union_of_disjoint
    (by simp [Finset.disjoint_singleton_right]),
    Finset.card_image_of_injective _ some_inl_inj]
  rfl

/-- **The apex of a Mycielskian is adjacent to every shadow**, so its degree is the order of `G`. -/
theorem degree_mycielskian_none :
    (mycielskian G).toSimple.degree none = FinEnum.card G.V := by
  rw [SimpleGraph.degree, neighborFinset_mycielskian_none,
    Finset.card_image_of_injective _ some_inr_inj]
  simp

/-- **A Mycielskian triples the edge count and adds one edge per vertex**: each old edge is joined
by its two mixed copies, and the apex contributes one edge to every shadow. -/
@[simp] theorem E_mycielskian :
    (mycielskian G).E = 3 * G.E + FinEnum.card G.V := by
  unfold CGraph.E
  have hhand_myc := (mycielskian G).toSimple.sum_degrees_eq_twice_card_edges
  have hhand_G := G.toSimple.sum_degrees_eq_twice_card_edges
  -- The handshake lemma on both sides, so it suffices to add up the degrees computed above.
  have target : ∑ v : Option (G.V ⊕ G.V), (mycielskian G).toSimple.degree v =
      3 * ∑ v : G.V, G.toSimple.degree v + 2 * FinEnum.card G.V := by
    rw [Fintype.sum_option, Fintype.sum_sum_type, degree_mycielskian_none]
    simp only [degree_mycielskian_inl, degree_mycielskian_inr, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    rw [show Fintype.card G.V = FinEnum.card G.V by simp]
    ring
  rw [show (∑ v : Option (G.V ⊕ G.V), (mycielskian G).toSimple.degree v)
      = 2 * (mycielskian G).toSimple.edgeFinset.card from
    (Finset.sum_univ_inst_eq _ _ _).trans hhand_myc] at target
  rw [show (∑ v : G.V, G.toSimple.degree v) = 2 * G.toSimple.edgeFinset.card from hhand_G] at target
  omega

end

section
open Fintype
variable {m n : ℕ}

/-- The vertices whose part avoids `S` are the fibres over `Sᶜ`, so there are `∑ j ∈ Sᶜ, ds.get j`
of them. -/
theorem card_filter_fst_notMem (ds : List ℕ) (S : Finset (Fin ds.length)) :
    (Finset.univ.filter fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦ z.1 ∉ S).card
      = ∑ j ∈ Sᶜ, ds.get j := by
  rw [show (Finset.univ.filter fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦ z.1 ∉ S)
      = Sᶜ.sigma (fun _ ↦ Finset.univ) from
    Finset.ext (α := Σ i : Fin ds.length, (complete (ds.get i)).V) fun z ↦ by simp]
  rw [Finset.card_sigma]
  simp

end

section
open Fintype
variable (G : CGraph)

/-- An automorphism of `G` maps edges to edges, bijectively. -/
def edgePerm (σ : G ≃cg G) : Equiv.Perm {e : Sym2 G.V // e ∈ G.toSimple.edgeSet} where
  toFun e := ⟨Sym2.map σ e.1, σ.toSimpleIso.toHom.map_mem_edgeSet e.2⟩
  invFun e := ⟨Sym2.map σ.symm e.1, (Iso.toSimpleIso σ.symm).toHom.map_mem_edgeSet e.2⟩
  left_inv e := by ext : 1; simp [Sym2.map_map]
  right_inv e := by ext : 1; simp [Sym2.map_map]

@[simp] theorem edgePerm_coe (σ : G ≃cg G) (x : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) :
    ((G.edgePerm σ x : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) : Sym2 G.V)
      = Sym2.map σ (x : Sym2 G.V) := rfl

end

end CGraph

namespace CGraph.Iso

section
variable {G G' H H' : CGraph}

-- Measured: 308 114 heartbeats.  All of it is elaborator work — `Fintype.bijective_iff_injective_
-- and_card` and `equivOfBijective` reduce the two `Fintype` instances on `Sym2`-indexed subtypes.
set_option maxHeartbeats 800000 in
/-- **The line graph of a disjoint union is the disjoint union of the line graphs**: an edge of
`G + H` lies wholly in `G` or wholly in `H`, and two edges on opposite sides never meet.

The forward map `sumEdge` is injective, and both sides have `E G + E H` vertices, so
`Fintype.bijective_iff_injective_and_card` makes it a bijection and `equivOfBijective` inverts
it by search. -/
@[toIsoGraph simp lineGraph_disjUnion]
def lineGraphDisjUnion (G H : CGraph) :
    CGraph.lineGraph (G ⊕g H) ≃cg
      CGraph.lineGraph G ⊕g CGraph.lineGraph H := by
  have hcard : Fintype.card ((CGraph.lineGraph G).V ⊕ (CGraph.lineGraph H).V)
      = Fintype.card (CGraph.lineGraph (G ⊕g H)).V := by
    rw [Fintype.card_sum, ← FinEnum.card_eq_fintypeCard (α := (CGraph.lineGraph G).V),
      ← FinEnum.card_eq_fintypeCard (α := (CGraph.lineGraph H).V),
      ← FinEnum.card_eq_fintypeCard (α := (CGraph.lineGraph (G ⊕g H)).V),
      CGraph.card_lineGraph, CGraph.card_lineGraph, CGraph.card_lineGraph,
      CGraph.E_disjUnion]
  have hbij : Function.Bijective (sumEdge G H) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨sumEdge_inj G H, hcard⟩
  have hmem : ∀ (e : (CGraph.lineGraph G).V) (v : (G ⊕g H).V),
      v ∈ (((equivOfBijective hbij) (.inl e)).1 : Sym2 (G ⊕g H).V)
        ↔ ∃ a ∈ (e.1 : Sym2 G.V), Sum.inl a = v :=
    fun _ _ ↦ Sym2.mem_map
  have hmem' : ∀ (e : (CGraph.lineGraph H).V) (v : (G ⊕g H).V),
      v ∈ (((equivOfBijective hbij) (.inr e)).1 : Sym2 (G ⊕g H).V)
        ↔ ∃ a ∈ (e.1 : Sym2 H.V), Sum.inr a = v :=
    fun _ _ ↦ Sym2.mem_map
  refine (isoOfAdj (G := CGraph.lineGraph G ⊕g CGraph.lineGraph H)
    (H := CGraph.lineGraph (G ⊕g H))
    (equivOfBijective hbij) ?_).symm
  rintro (e | e) (f | f) <;> rw [CGraph.lineGraph_adj]
  · show _ = (CGraph.lineGraph G).Adj e f
    rw [CGraph.lineGraph_adj]
    congr 1
    · exact decide_eq_decide.2
        (not_congr ⟨fun h ↦ Sum.inl_injective (sumEdge_inj G H h), fun h ↦ by rw [h]⟩)
    · refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        obtain ⟨a, ha, rfl⟩ := (hmem e v).1 hv1
        obtain ⟨b, hb, hab⟩ := (hmem f _).1 hv2
        exact ⟨a, ha, by rwa [Sum.inl_injective hab] at hb⟩
      · rintro ⟨v, hv1, hv2⟩
        exact ⟨Sum.inl v, (hmem e _).2 ⟨v, hv1, rfl⟩, (hmem f _).2 ⟨v, hv2, rfl⟩⟩
  · show _ = false
    refine Bool.and_eq_false_iff.2 (Or.inr (decide_eq_false ?_))
    rintro ⟨v, hv1, hv2⟩
    obtain ⟨a, -, rfl⟩ := (hmem e v).1 hv1
    obtain ⟨b, -, hb⟩ := (hmem' f _).1 hv2
    exact absurd hb (by simp)
  · show _ = false
    refine Bool.and_eq_false_iff.2 (Or.inr (decide_eq_false ?_))
    rintro ⟨v, hv1, hv2⟩
    obtain ⟨a, -, rfl⟩ := (hmem' e v).1 hv1
    obtain ⟨b, -, hb⟩ := (hmem f _).1 hv2
    exact absurd hb (by simp)
  · show _ = (CGraph.lineGraph H).Adj e f
    rw [CGraph.lineGraph_adj]
    congr 1
    · exact decide_eq_decide.2
        (not_congr ⟨fun h ↦ Sum.inr_injective (sumEdge_inj G H h), fun h ↦ by rw [h]⟩)
    · refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        obtain ⟨a, ha, rfl⟩ := (hmem' e v).1 hv1
        obtain ⟨b, hb, hab⟩ := (hmem' f _).1 hv2
        exact ⟨a, ha, by rwa [Sum.inr_injective hab] at hb⟩
      · rintro ⟨v, hv1, hv2⟩
        exact ⟨Sum.inr v, (hmem' e _).2 ⟨v, hv1, rfl⟩, (hmem' f _).2 ⟨v, hv2, rfl⟩⟩

end

end CGraph.Iso

namespace CGraph

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
  simp only [ofEdges_adj, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    ne_eq, huv, List.contains_eq_mem]

/-- **A list covering the neighbours of `v` bounds its degree.**  Together with
`le_degree_ofEdges` this turns a degree computation in a graph given by an edge list into two
membership arguments about lists of naturals, with no `Finset` left at the call site. -/
theorem degree_ofEdges_le (n : ℕ) (es : List (ℕ × ℕ)) (v : (ofEdges n es).V) (l : List ℕ)
    (hl : ∀ w : ℕ, w ≠ v.1 → ((v.1, w) ∈ es ∨ (w, v.1) ∈ es) → w ∈ l) :
    (ofEdges n es).toSimple.degree v ≤ l.length := by
  classical
  have hinj : Function.Injective (fun u : (ofEdges n es).V ↦ u.1) := fun a b h ↦ Fin.ext h
  calc (ofEdges n es).toSimple.degree v
      = ((ofEdges n es).nbrs v).card := (card_nbrs_eq_degree _ _).symm
    _ = (((ofEdges n es).nbrs v).image (fun u : (ofEdges n es).V ↦ u.1)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ l.toFinset.card := Finset.card_le_card (by
        intro w hw
        simp only [Finset.mem_image, mem_nbrs] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        obtain ⟨hne, hadj⟩ := (ofEdges_adj_val n es v u).1 hu
        exact List.mem_toFinset.2 (hl u.1 (Ne.symm hne) hadj))
    _ ≤ l.length := List.toFinset_card_le l

/-- A duplicate-free list of neighbours of `v` bounds its degree from below. -/
theorem le_degree_ofEdges (n : ℕ) (es : List (ℕ × ℕ)) (v : (ofEdges n es).V) (l : List ℕ)
    (hnd : l.Nodup)
    (hl : ∀ w ∈ l, w < n ∧ w ≠ v.1 ∧ ((v.1, w) ∈ es ∨ (w, v.1) ∈ es)) :
    l.length ≤ (ofEdges n es).toSimple.degree v := by
  classical
  have hsub : l.toFinset ⊆ ((ofEdges n es).nbrs v).image (fun u : (ofEdges n es).V ↦ u.1) := by
    intro w hw
    obtain ⟨hwn, hne, hadj⟩ := hl w (List.mem_toFinset.1 hw)
    refine Finset.mem_image.2 ⟨⟨w, hwn⟩, ?_, rfl⟩
    exact (mem_nbrs _ _ _).2 ((ofEdges_adj_val n es v ⟨w, hwn⟩).2 ⟨Ne.symm hne, hadj⟩)
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (((ofEdges n es).nbrs v).image (fun u : (ofEdges n es).V ↦ u.1)).card :=
        Finset.card_le_card hsub
    _ ≤ ((ofEdges n es).nbrs v).card := Finset.card_image_le
    _ = _ := card_nbrs_eq_degree _ _

/-- **The degree of a vertex of `ofEdges n es`, read off a list of its neighbours.**  The list
must be duplicate-free, live in `Fin n`, avoid `v` itself, and contain exactly those vertices
joined to `v` by an entry of `es` in one orientation or the other. -/
theorem degree_ofEdges (n : ℕ) (es : List (ℕ × ℕ)) (v : (ofEdges n es).V) (l : List ℕ)
    (hnd : l.Nodup) (hlt : ∀ w ∈ l, w < n) (hv : v.1 ∉ l)
    (hmem : ∀ w : ℕ, w ≠ v.1 → (((v.1, w) ∈ es ∨ (w, v.1) ∈ es) ↔ w ∈ l)) :
    (ofEdges n es).toSimple.degree v = l.length := by
  refine le_antisymm (degree_ofEdges_le n es v l fun w hne hw ↦ (hmem w hne).1 hw)
    (le_degree_ofEdges n es v l hnd fun w hw ↦ ?_)
  have hne : w ≠ v.1 := by rintro rfl; exact hv hw
  exact ⟨hlt w hw, hne, (hmem w hne).2 hw⟩

/-- **Checking a property of every edge of `ofEdges n es` costs `es`, not `n²`.**  Deciding
`∀ u v, (ofEdges n es).Adj u v = true → p u v` by exhaustion runs the adjacency test on all `n²`
pairs, and each test that comes out false is a full scan of `es`; running down `es` instead tests
`p` once per entry per orientation, and never asks whether anything is *not* an edge.  For the
hundred-vertex graphs of `SmallGraphs/Defs/` the difference is minutes against seconds. -/
theorem forall_adj_ofEdges {n : ℕ} [NeZero n] {es : List (ℕ × ℕ)} (p : Fin n → Fin n → Bool)
    (h : ∀ e ∈ es, p (vtx n e.1) (vtx n e.2) = true ∧ p (vtx n e.2) (vtx n e.1) = true)
    {u v : (ofEdges n es).V} (huv : (ofEdges n es).Adj u v = true) : p u v = true := by
  have hu : vtx n u.1 = u := Fin.ext (Nat.mod_eq_of_lt u.2)
  have hv : vtx n v.1 = v := Fin.ext (Nat.mod_eq_of_lt v.2)
  rcases (ofEdges_adj_val n es u v).1 huv with ⟨-, hm | hm⟩
  · have := (h _ hm).1; rwa [hu, hv] at this
  · have := (h _ hm).2; rwa [hu, hv] at this

/-- **The edge count of `ofEdges n es`**: if `es` lists no loop, no repeat and no reversed
repeat, and stays inside `Fin n`, then the edges of `ofEdges n es` are exactly its entries, so
there are `es.length` of them. -/
theorem E_ofEdges_of_nodup {n : ℕ} {es : List (ℕ × ℕ)} (hn : ∀ p ∈ es, p.1 < n ∧ p.2 < n)
    (hnooops : ∀ p ∈ es, p.1 ≠ p.2) (hnorev : ∀ p ∈ es, (p.2, p.1) ∉ es) (hnodup : es.Nodup) :
    (ofEdges n es).E = es.length := by
  induction es with
  | nil =>
    have : ofEdges n [] = empty n := by
      exact ext' rfl (heq_of_eq (funext fun i => funext fun j =>
          by simp [ofEdges_adj, empty]))
    rw [this, E_empty, List.length_nil]
  | cons e es' ih =>
    unfold E
    set ue : Fin n := ⟨e.1, (hn e (by simp)).1⟩
    set ve : Fin n := ⟨e.2, (hn e (by simp)).2⟩
    set edge_e : Sym2 (Fin n) := s(ue, ve)
    have he_not_in_es' : e ∉ es' := by
      intro h
      have hd := hnodup
      simp [List.nodup_cons] at hd
      exact hd.1 h
    have hrev_not_in_es' : (e.2, e.1) ∉ es' := by
      intro h
      have hmem : (e.2, e.1) ∈ e :: es' := by simp [h]
      exact absurd (hnorev (e.2, e.1) hmem) (by simp [List.mem_cons])
    have hdisjoint : edge_e ∉ (ofEdges n es').toSimple.edgeFinset := by
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, toSimple_adj,
          ofEdges_adj_val] at he
      rcases he.2 with h | h
      · exact he_not_in_es' h
      · exact hrev_not_in_es' h
    -- Now show the edgeFinset equality
    have hedgeFinset_eq : (ofEdges n (e :: es')).toSimple.edgeFinset =
        (insert edge_e (ofEdges n es').toSimple.edgeFinset) := by
      ext x
      show x ∈ (ofEdges n (e :: es')).toSimple.edgeFinset ↔
          x ∈ insert edge_e (ofEdges n es').toSimple.edgeFinset
      have hdef : (ofEdges n (e :: es')).V = Fin n := rfl
      change x ∈ (ofEdges n (e :: es')).toSimple.edgeFinset ↔
          x ∈ insert edge_e (ofEdges n es').toSimple.edgeFinset at *
      induction x using Sym2.ind with
      | h u v =>
        simp [SimpleGraph.mem_edgeFinset, Finset.mem_insert, SimpleGraph.mem_edgeSet,
          toSimple_adj, ofEdges_adj_val]
        dsimp only [ofEdges] at u v
        simp only [edge_e]
        rw [Sym2.eq_iff]
        have heq1 : (u = ue ↔ ↑u = e.1) := by simp [ue, Fin.ext_iff]
        have heq2 : (v = ve ↔ ↑v = e.2) := by simp [ve, Fin.ext_iff]
        have heq3 : (u = ve ↔ ↑u = e.2) := by simp [ve, Fin.ext_iff]
        have heq4 : (v = ue ↔ ↑v = e.1) := by simp [ue, Fin.ext_iff]
        have heq5 : ((↑u, ↑v) = e ↔ ↑u = e.1 ∧ ↑v = e.2) := Prod.ext_iff
        have heq6 : ((↑v, ↑u) = e ↔ ↑v = e.1 ∧ ↑u = e.2) := Prod.ext_iff
        rw [heq5, heq6, heq1, heq2, heq3, heq4]
        have hnooops_e : e.1 ≠ e.2 := hnooops e (by simp)
        have huvFin : (u : ℕ) = (v : ℕ) ↔ u = v := Fin.ext_iff.symm
        have hA_notC : (↑u = e.1 ∧ ↑v = e.2) → ¬(↑u = ↑v) := by
          intro ⟨ha, hb⟩ huv
          have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
          exact hnooops_e (by rw [ha, hb] at huv'; exact huv')
        have hB_notC : (↑v = e.1 ∧ ↑u = e.2) → ¬(↑u = ↑v) := by
          intro ⟨ha, hb⟩ huv
          have huv' : (u : ℕ) = (v : ℕ) := congr_arg (fun x : Fin n => (x : ℕ)) huv
          exact hnooops_e (by rw [hb, ha] at huv'; exact huv'.symm)
        have hB'_notC : (↑v = e.1 ∧ ↑u = e.2) → ¬(↑u = ↑v) := hB_notC
        have hB_eq_B' : (↑u = e.2 ∧ ↑v = e.1) ↔ (↑v = e.1 ∧ ↑u = e.2) := and_comm
        have hAB_notC : (↑u = e.1 ∧ ↑v = e.2 ∨ ↑u = e.2 ∧ ↑v = e.1) → ¬(↑u = ↑v) := by
          rintro (hA | hB'')
          · exact hA_notC hA
          · exact hB_notC ⟨hB''.2, hB''.1⟩
        constructor
        · rintro ⟨hne, hmem⟩
          rcases hmem with hAD | hBD' | hF
          · rcases hAD with hA | hD
            · exact .inl (.inl hA)
            · exact .inr ⟨hne, .inl hD⟩
          · exact .inl (.inr (hB_eq_B'.mpr hBD'))
          · exact .inr ⟨hne, .inr hF⟩
        · rintro (hAB | ⟨hne, hDF⟩)
          · have hnotC := hAB_notC hAB
            exact ⟨by intro huv; exact hnotC (Fin.ext_iff.mpr huv),
                   Or.elim hAB (fun hA => Or.inl (Or.inl hA))
                     (fun hB'' => Or.inr (Or.inl (hB_eq_B'.mp hB'')))⟩
          · exact ⟨hne, Or.elim hDF (fun hD => Or.inl (Or.inr hD)) (fun hF => Or.inr (Or.inr hF))⟩
    rw [hedgeFinset_eq, Finset.card_insert_of_notMem hdisjoint]
    simp [List.length_cons]
    exact ih
      (fun p hp => ⟨(hn p (by simp [hp])).1, (hn p (by simp [hp])).2⟩)
      (fun p hp => hnooops p (by simp [hp]))
      (fun p hp => by
        have h := hnorev p (by simp [hp])
        exact fun hm => h (by simp [hm]))
      hnodup.tail

/-- **The edge count of a sorted edge list**: the common case of `E_ofEdges_of_nodup`, where
every entry `(a, b)` has `a < b < n`.  This is the normal form the edge lists of
`SmallGraphs/Defs/` are in. -/
theorem E_ofEdges (n : ℕ) (es : List (ℕ × ℕ)) (hlt : ∀ p ∈ es, p.1 < p.2)
    (hbound : ∀ p ∈ es, p.2 < n) (hnup : List.Nodup es) : (ofEdges n es).E = es.length :=
  E_ofEdges_of_nodup (fun p hp ↦ ⟨lt_trans (hlt p hp) (hbound p hp), hbound p hp⟩)
    (fun p hp ↦ Nat.ne_of_lt (hlt p hp))
    (fun p hp hmem ↦ by
      have h1 : p.1 < p.2 := hlt p hp
      have h2 : p.2 < p.1 := hlt _ hmem
      omega)
    hnup

/-- **A clique on `m` vertices contributes `m.choose 2` edges**, since its edge list is a sorted
list of distinct pairs and `ofEdges` on it is `complete m`. -/
@[simp] theorem length_cliqueEdges (m : ℕ) : (cliqueEdges m).length = m.choose 2 := by
  have h := E_ofEdges m (cliqueEdges m) (fun ⟨a, b⟩ hp ↦ ((mem_cliqueEdges m a b).1 hp).1)
    (fun ⟨a, b⟩ hp ↦ ((mem_cliqueEdges m a b).1 hp).2) (cliqueEdges_nodup m)
  rw [ofEdges_cliqueEdges, E_complete] at h
  exact h.symm

/-! ## Two small facts about one-vertex graphs -/

/-- No vertex is adjacent to itself, as an equation of `Bool`s. -/
theorem adj_self (G : CGraph) (x : G.V) : G.Adj x x = false :=
  (Bool.not_eq_true _).mp (G.loopless x)

/-- A graph with a single vertex has no edges. -/
theorem adj_eq_false_of_subsingleton {G : CGraph} [Subsingleton G.V] (x y : G.V) :
    G.Adj x y = false := by
  cases Subsingleton.elim x y
  exact (Bool.not_eq_true _).mp (G.loopless x)

/-! ### The Cartesian product as a box product -/

/-- The Cartesian product is Mathlib's box product on the underlying simple graphs. -/
theorem toSimple_cartesianProduct (G H : CGraph) :
    (G □g H).toSimple = SimpleGraph.boxProd G.toSimple H.toSimple := by
  ext p q
  simp only [CGraph.toSimple_adj, cartesianProduct_adj, SimpleGraph.boxProd_adj,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- A graph with a positive edge count has an edge. -/
theorem exists_adj_of_E_pos {G : CGraph} (h : 0 < G.E) : ∃ a b, G.Adj a b := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he⟩

/-! ### The strong and lexicographic products contain the Cartesian one -/

theorem cartesianProduct_le_strongProduct (G H : CGraph) :
    (G □g H).toSimple ≤ (G ⊠g H).toSimple := by
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
    (G □g H).toSimple ≤ (G ·g H).toSimple := by
  intro p q hpq
  rw [CGraph.toSimple_adj, cartesianProduct_adj] at hpq
  rw [CGraph.toSimple_adj, lexProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq ⊢
  tauto

@[simp, toIsoGraph]
theorem length_degSequence (G : CGraph) :
    G.degSequence.length = FinEnum.card G.V := by
  rw [degSequence, degMultiset, Multiset.length_sort, Multiset.card_map, Finset.card_val,
    FinEnum.card_univ]

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
    G.degSequence = List.replicate (FinEnum.card G.V) k := by
  rw [List.eq_replicate_iff]
  refine ⟨G.length_degSequence, fun b hb ↦ ?_⟩
  rw [degSequence, degMultiset, Multiset.mem_sort, Multiset.mem_map] at hb
  obtain ⟨v, -, rfl⟩ := hb
  exact h v

section
variable {G H : CGraph}

/-! ### Neighbours in the four products -/

theorem nbrs_cartesianProduct (p : (G □g H).V) :
    (G □g H).nbrs p
      = (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) ∪ (G.nbrs p.1 ×ˢ ({p.2} : Finset H.V)) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, cartesianProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem card_nbrs_cartesianProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (G □g H).V) : ((G □g H).nbrs p).card = k + l := by
  rw [nbrs_cartesianProduct, Finset.card_union_of_disjoint, Finset.card_product,
    Finset.card_product, Finset.card_singleton, Finset.card_singleton, hG, hH, one_mul, mul_one,
    Nat.add_comm]
  refine Finset.disjoint_product.2 (Or.inr ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_tensorProduct (p : (G ⊗g H).V) :
    (G ⊗g H).nbrs p = G.nbrs p.1 ×ˢ H.nbrs p.2 := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, tensorProduct_adj]
  simp only [Finset.mem_product, mem_nbrs, Bool.and_eq_true]

theorem card_nbrs_tensorProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (G ⊗g H).V) : ((G ⊗g H).nbrs p).card = k * l := by
  rw [nbrs_tensorProduct, Finset.card_product, hG, hH]

theorem nbrs_lexProduct (p : (G ·g H).V) :
    (G ·g H).nbrs p
      = (G.nbrs p.1 ×ˢ (Finset.univ : Finset H.V)) ∪ (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, lexProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Finset.mem_univ, and_true, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

theorem card_nbrs_lexProduct {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (G ·g H).V) :
    ((G ·g H).nbrs p).card = k * FinEnum.card H.V + l := by
  rw [nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, FinEnum.card_univ, hG, hH, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_strongProduct (p : (G ⊠g H).V) :
    (G ⊠g H).nbrs p
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
    (p : (G ⊠g H).V) :
    ((G ⊠g H).nbrs p).card = (k + 1) * (l + 1) - 1 := by
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
      push Not at h
      exact h
    have key : ∀ w : G.V, ¬ G.toSimple.Reachable u w →
        Gᶜ.toSimple.Adj u w ∧ Gᶜ.toSimple.Adj w v := fun w hw ↦
      ⟨G.compl_adj_of_not_reachable hw,
        (G.compl_adj_of_not_reachable fun hvw ↦ hw (hr.trans hvw)).symm⟩
    by_cases hux : G.toSimple.Reachable u x
    · exact Or.inr ⟨y, key y fun huy ↦ hxy (hux.symm.trans huy)⟩
    · exact Or.inr ⟨x, key x hux⟩
  · exact Or.inl (G.compl_adj_of_not_reachable hr)

/- The `Fintype` on the sum is taken as an argument rather than synthesised: the vertex type of a
disjoint union counts with the instance its own `FinEnum` induces, not with the one for a sum, and
the two are only propositionally equal.  The canonical case is `univ_val_sum'`, split off so that
the instance it is stated about is fixed by its own context rather than found in this one, where
`i` itself is a candidate. -/

private theorem univ_val_sum (α β : Type*) [Fintype α] [Fintype β] (i : Fintype (α ⊕ β)) :
    (@Finset.univ (α ⊕ β) i).val
      = (Finset.univ : Finset α).val.map Sum.inl + (Finset.univ : Finset β).val.map Sum.inr :=
  (congrArg Finset.val (Finset.univ_inst_eq i _)).trans (univ_val_sum' α β)

/-- **The degree multiset of a disjoint union** is the sum of the two degree multisets. -/
@[toIsoGraph]
theorem degMultiset_disjUnion (G H : CGraph) :
    (G ⊕g H).degMultiset = G.degMultiset + H.degMultiset := by
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
    Gᶜ.toSimple.degree v = FinEnum.card G.V - 1 - G.toSimple.degree v := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_compl]
  have hv : v ∈ (G.nbrs v)ᶜ := by simp [adj_self]
  rw [Finset.card_erase_of_mem hv, Finset.card_compl, ← FinEnum.card_eq_fintypeCard']
  omega

theorem degree_le (G : CGraph) (v : G.V) :
    G.toSimple.degree v + 1 ≤ FinEnum.card G.V := by
  rw [← card_nbrs_eq_degree]
  have hv : v ∉ G.nbrs v := by simp [adj_self]
  have hsub := Finset.card_le_card (Finset.subset_univ (insert v (G.nbrs v)))
  rw [Finset.card_insert_of_notMem hv, FinEnum.card_univ] at hsub
  omega

theorem nbrs_join_inl (G H : CGraph) (a : G.V) :
    (G ∇g H).nbrs (Sum.inl a)
      = (G.nbrs a).map ⟨Sum.inl, Sum.inl_injective⟩
        ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem nbrs_join_inr (G H : CGraph) (b : H.V) :
    (G ∇g H).nbrs (Sum.inr b)
      = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
        ∪ (H.nbrs b).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext w
  rcases w with c | d <;> simp

theorem degree_join_inl (G H : CGraph) (a : G.V) :
    (G ∇g H).toSimple.degree (Sum.inl a) = G.toSimple.degree a + FinEnum.card H.V := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_join_inl,
    Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]), Finset.card_map,
    Finset.card_map, FinEnum.card_univ]

theorem degree_join_inr (G H : CGraph) (b : H.V) :
    (G ∇g H).toSimple.degree (Sum.inr b) = FinEnum.card G.V + H.toSimple.degree b := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_join_inr,
    Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]), Finset.card_map,
    Finset.card_map, FinEnum.card_univ]

/-- **The degree multiset of a join**: every vertex picks up all the vertices on the other side. -/
theorem degMultiset_join (G H : CGraph) :
    (G ∇g H).degMultiset = G.degMultiset.map (· + FinEnum.card H.V)
      + H.degMultiset.map (· + FinEnum.card G.V) := by
  unfold degMultiset
  rw [univ_val_sum, Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map,
    Multiset.map_map]
  congr 1
  · exact Multiset.map_congr rfl fun v _ ↦ degree_join_inl G H v
  · refine Multiset.map_congr rfl fun v _ ↦ ?_
    show (G ∇g H).toSimple.degree (Sum.inr v) = H.toSimple.degree v + FinEnum.card G.V
    rw [degree_join_inr, Nat.add_comm]

/-- **The degree multiset of the complement**: every degree is replaced by its "co-degree". -/
theorem degMultiset_compl (G : CGraph) :
    Gᶜ.degMultiset = G.degMultiset.map (fun d ↦ FinEnum.card G.V - 1 - d) := by
  unfold degMultiset
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun v _ ↦ degree_compl G v

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

private theorem univ_val_map_val' (n : ℕ) :
    (Finset.univ : Finset (Fin n)).val.map Fin.val = Multiset.range n := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, List.map_coe_finRange_eq_range]
  rfl

private theorem univ_val_map_val (n : ℕ) (i : Fintype (Fin n)) :
    (@Finset.univ (Fin n) i).val.map Fin.val = Multiset.range n :=
  (congrArg (fun s : Finset (Fin n) ↦ s.val.map Fin.val) (Finset.univ_inst_eq i _)).trans
    (univ_val_map_val' n)

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

/- As with `univ_val_sum`, the product's `Fintype` is an argument: the four products all count
their vertices with the instance their own `FinEnum` induces. -/

private theorem univ_val_map_prod {α β : Type} [Fintype α] [Fintype β] (i : Fintype (α × β))
    (f : α → β → ℕ) :
    (@Finset.univ (α × β) i).val.map (fun p ↦ f p.1 p.2)
      = (Finset.univ : Finset α).val.bind fun a ↦ (Finset.univ : Finset β).val.map (f a) :=
  (congrArg (fun s : Finset (α × β) ↦ s.val.map fun p ↦ f p.1 p.2)
    (Finset.univ_inst_eq i _)).trans (univ_val_map_prod' f)

theorem degree_cartesianProduct (G H : CGraph)
    (p : (G □g H).V) :
    (G □g H).toSimple.degree p
      = G.toSimple.degree p.1 + H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_cartesianProduct, Finset.card_union_of_disjoint, Finset.card_product,
    Finset.card_product, Finset.card_singleton, Finset.card_singleton, one_mul, mul_one,
    Nat.add_comm]
  refine Finset.disjoint_product.2 (Or.inr ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem degree_tensorProduct (G H : CGraph)
    (p : (G ⊗g H).V) :
    (G ⊗g H).toSimple.degree p = G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_tensorProduct, Finset.card_product]

theorem degree_lexProduct (G H : CGraph)
    (p : (G ·g H).V) :
    (G ·g H).toSimple.degree p
      = G.toSimple.degree p.1 * FinEnum.card H.V + H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, FinEnum.card_univ, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem degree_strongProduct (G H : CGraph)
    (p : (G ⊠g H).V) :
    (G ⊠g H).toSimple.degree p
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
    (G □g H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_cartesianProduct G H p]
  refine Eq.trans (univ_val_map_prod (α := G.V) (β := H.V) _
    fun a b ↦ G.toSimple.degree a + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_tensorProduct (G H : CGraph) :
    (G ⊗g H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_tensorProduct G H p]
  refine Eq.trans (univ_val_map_prod (α := G.V) (β := H.V) _
    fun a b ↦ G.toSimple.degree a * H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_lexProduct (G H : CGraph) :
    (G ·g H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * FinEnum.card H.V + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_lexProduct G H p]
  refine Eq.trans (univ_val_map_prod (α := G.V) (β := H.V) _
    fun a b ↦ G.toSimple.degree a * FinEnum.card H.V + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_strongProduct (G H : CGraph) :
    (G ⊠g H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ (d + 1) * (e + 1) - 1 := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_strongProduct G H p]
  refine Eq.trans (univ_val_map_prod (α := G.V) (β := H.V) _
    fun a b ↦ (G.toSimple.degree a + 1) * (H.toSimple.degree b + 1) - 1) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦
    (Multiset.map_map (fun e ↦ (G.toSimple.degree a + 1) * (e + 1) - 1)
      (fun v ↦ H.toSimple.degree v) _).symm

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

/-- The underlying simple graph of a disjoint union is Mathlib's `SimpleGraph.sum`. -/
theorem toSimple_disjUnion (G H : CGraph) :
    (G ⊕g H).toSimple = G.toSimple.sum H.toSimple := by
  ext x y
  cases x <;> cases y <;> simp [SimpleGraph.sum_adj, CGraph.toSimple_adj]

theorem toSimple_ne_bot_iff {G : CGraph} : G.toSimple ≠ ⊥ ↔ 0 < G.E := by
  show _ ↔ 0 < G.toSimple.edgeFinset.card
  rw [Finset.card_pos, SimpleGraph.edgeFinset_nonempty]

/-! ### Basic API -/

theorem degree_le_maxDeg (G : CGraph) (v : G.V) : G.toSimple.degree v ≤ G.maxDeg :=
  SimpleGraph.degree_le_maxDegree _ v

theorem minDeg_le_degree (G : CGraph) (v : G.V) : G.minDeg ≤ G.toSimple.degree v :=
  SimpleGraph.minDegree_le_degree _ v

theorem maxDeg_le_of_forall {G : CGraph} {k : ℕ} (h : ∀ v, G.toSimple.degree v ≤ k) :
    G.maxDeg ≤ k :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ k h

theorem le_minDeg_of_forall {G : CGraph} {k : ℕ} (v₀ : G.V)
    (h : ∀ v, k ≤ G.toSimple.degree v) : k ≤ G.minDeg :=
  haveI : Nonempty G.V := ⟨v₀⟩
  SimpleGraph.le_minDegree_of_forall_le_degree _ k h

theorem exists_degree_eq_maxDeg (G : CGraph) (v₀ : G.V) :
    ∃ v : G.V, G.toSimple.degree v = G.maxDeg := by
  have : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_maximal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

theorem exists_degree_eq_minDeg (G : CGraph) (v₀ : G.V) :
    ∃ v : G.V, G.toSimple.degree v = G.minDeg := by
  have : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_minimal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

@[toIsoGraph]
theorem minDeg_le_maxDeg (G : CGraph) : G.minDeg ≤ G.maxDeg :=
  SimpleGraph.minDegree_le_maxDegree _

@[toIsoGraph maxDeg_lt_V]
theorem maxDeg_lt_card {G : CGraph} [Nonempty G.V] : G.maxDeg < FinEnum.card G.V := by
  rw [FinEnum.card_eq_fintypeCard']
  exact SimpleGraph.maxDegree_lt_card_verts _

theorem mem_degMultiset {G : CGraph} {d : ℕ} :
    d ∈ G.degMultiset ↔ ∃ v : G.V, G.toSimple.degree v = d := by
  unfold degMultiset
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, Finset.mem_univ_val v, hv⟩

/-- **A bound on every entry of the degree multiset bounds the maximum degree.** -/
@[toIsoGraph]
theorem maxDeg_le_of_degMultiset {G : CGraph} {k : ℕ} (h : ∀ d ∈ G.degMultiset, d ≤ k) :
    G.maxDeg ≤ k :=
  maxDeg_le_of_forall fun v ↦ h _ (mem_degMultiset.2 ⟨v, rfl⟩)

/-- The maximum degree is the largest entry of the degree multiset. -/
@[toIsoGraph]
theorem maxDeg_eq_sup (G : CGraph) : G.maxDeg = G.degMultiset.sup := by
  refine le_antisymm ?_ (Multiset.sup_le.2 fun d hd ↦ ?_)
  · rcases isEmpty_or_nonempty G.V with h | h
    · rw [maxDeg, SimpleGraph.maxDegree_of_subsingleton]
      exact Nat.zero_le _
    · obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg h.some
      exact hv ▸ Multiset.le_sup (mem_degMultiset.2 ⟨v, rfl⟩)
  · obtain ⟨v, hv⟩ := mem_degMultiset.1 hd
    exact hv ▸ G.degree_le_maxDeg v

@[toIsoGraph]
theorem maxDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, d ≤ k) : G.maxDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (maxDeg_le_of_forall fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))
    (hv ▸ G.degree_le_maxDeg v)

@[toIsoGraph]
theorem minDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, k ≤ d) : G.minDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (hv ▸ G.minDeg_le_degree v)
    (le_minDeg_of_forall v fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))

/-- Half the handshake lemma: the degree sum is squeezed between `|V|·δ` and `|V|·Δ`. -/
@[toIsoGraph V_mul_minDeg_le]
theorem card_mul_minDeg_le (G : CGraph) : FinEnum.card G.V * G.minDeg ≤ 2 * G.E := by
  calc FinEnum.card G.V * G.minDeg = ∑ _v : G.V, G.minDeg := by
        rw [Finset.sum_const, FinEnum.card_univ, smul_eq_mul]
    _ ≤ ∑ v : G.V, G.toSimple.degree v := Finset.sum_le_sum fun v _ ↦ G.minDeg_le_degree v
    _ = 2 * G.E := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

@[toIsoGraph two_mul_E_le_V_mul_maxDeg]
theorem two_mul_E_le_card_mul_maxDeg (G : CGraph) : 2 * G.E ≤ FinEnum.card G.V * G.maxDeg := by
  calc 2 * G.E = ∑ v : G.V, G.toSimple.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple).symm
    _ ≤ ∑ _v : G.V, G.maxDeg := Finset.sum_le_sum fun v _ ↦ G.degree_le_maxDeg v
    _ = FinEnum.card G.V * G.maxDeg := by rw [Finset.sum_const, FinEnum.card_univ, smul_eq_mul]

/-- One vertex's degree is at most the whole degree sum, so `Δ ≤ 2|E|`; in particular a graph
with no edges has no vertex of positive degree. -/
@[toIsoGraph]
theorem maxDeg_le_two_mul_E {G : CGraph} [Nonempty G.V] : G.maxDeg ≤ 2 * G.E := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  calc G.maxDeg = G.toSimple.degree v := hv.symm
    _ ≤ ∑ u : G.V, G.toSimple.degree u :=
        Finset.single_le_sum (f := fun u : G.V ↦ G.toSimple.degree u)
          (fun u _ ↦ Nat.zero_le _) (Finset.mem_univ v)
    _ = 2 * G.E := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

/-! ### The disjoint union, the join and the complement -/

@[toIsoGraph]
theorem maxDeg_disjUnion (G H : CGraph) :
    (G ⊕g H).maxDeg = max G.maxDeg H.maxDeg := by
  refine le_antisymm (maxDeg_le_of_forall ?_) (max_le ?_ ?_)
  · rintro (a | b)
    · rw [degree_disjUnion_inl]; exact le_max_of_le_left (G.degree_le_maxDeg a)
    · rw [degree_disjUnion_inr]; exact le_max_of_le_right (H.degree_le_maxDeg b)
  · refine maxDeg_le_of_forall fun a ↦ ?_
    rw [← degree_disjUnion_inl G H a]
    exact degree_le_maxDeg _ _
  · refine maxDeg_le_of_forall fun b ↦ ?_
    rw [← degree_disjUnion_inr G H b]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_disjUnion {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G ⊕g H).minDeg = min G.minDeg H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  refine le_antisymm (le_min ?_ ?_) (le_minDeg_of_forall (Sum.inl a₀) ?_)
  · rw [← ha, ← degree_disjUnion_inl G H a]
    exact minDeg_le_degree _ _
  · rw [← hb, ← degree_disjUnion_inr G H b]
    exact minDeg_le_degree _ _
  · rintro (a | b)
    · rw [degree_disjUnion_inl]; exact le_trans (min_le_left _ _) (G.minDeg_le_degree a)
    · rw [degree_disjUnion_inr]; exact le_trans (min_le_right _ _) (H.minDeg_le_degree b)

@[toIsoGraph]
theorem maxDeg_join {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G ∇g H).maxDeg
      = max (G.maxDeg + FinEnum.card H.V) (FinEnum.card G.V + H.maxDeg) := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  refine le_antisymm (maxDeg_le_of_forall ?_) (max_le ?_ ?_)
  · rintro (a' | b')
    · rw [degree_join_inl]
      exact le_max_of_le_left (Nat.add_le_add_right (G.degree_le_maxDeg a') _)
    · rw [degree_join_inr]
      exact le_max_of_le_right (Nat.add_le_add_left (H.degree_le_maxDeg b') _)
  · rw [← ha, ← degree_join_inl G H a]
    exact degree_le_maxDeg _ _
  · rw [← hb, ← degree_join_inr G H b]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_join {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G ∇g H).minDeg
      = min (G.minDeg + FinEnum.card H.V) (FinEnum.card G.V + H.minDeg) := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  refine le_antisymm (le_min ?_ ?_) (le_minDeg_of_forall (Sum.inl a₀) ?_)
  · rw [← ha, ← degree_join_inl G H a]
    exact minDeg_le_degree _ _
  · rw [← hb, ← degree_join_inr G H b]
    exact minDeg_le_degree _ _
  · rintro (a' | b')
    · rw [degree_join_inl]
      exact le_trans (min_le_left _ _) (Nat.add_le_add_right (G.minDeg_le_degree a') _)
    · rw [degree_join_inr]
      exact le_trans (min_le_right _ _) (Nat.add_le_add_left (H.minDeg_le_degree b') _)

/-- **Complementation swaps the two extreme degrees.** -/
@[toIsoGraph]
theorem maxDeg_compl {G : CGraph} [Nonempty G.V] :
    Gᶜ.maxDeg = FinEnum.card G.V - 1 - G.minDeg := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_minDeg v₀
  refine le_antisymm (maxDeg_le_of_forall fun w ↦ ?_) ?_
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.minDeg_le_degree w) _
  · rw [← hv, ← degree_compl]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_compl {G : CGraph} [Nonempty G.V] :
    Gᶜ.minDeg = FinEnum.card G.V - 1 - G.maxDeg := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  refine le_antisymm ?_ (le_minDeg_of_forall v₀ fun w ↦ ?_)
  · rw [← hv, ← degree_compl]
    exact minDeg_le_degree _ _
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.degree_le_maxDeg w) _

/-! ### The four products -/

@[toIsoGraph]
theorem maxDeg_cartesianProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G □g H).maxDeg = G.maxDeg + H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (G □g H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_cartesianProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G □g H).minDeg = G.minDeg + H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (G □g H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (G □g H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.minDeg_le_degree _) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_tensorProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ⊗g H).maxDeg = G.maxDeg * H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (G ⊗g H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_tensorProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ⊗g H).minDeg = G.minDeg * H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (G ⊗g H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (G ⊗g H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.minDeg_le_degree _) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_lexProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ·g H).maxDeg = G.maxDeg * FinEnum.card H.V + H.maxDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_lexProduct G H ((a, b) : (G ·g H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.degree_le_maxDeg _)) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_lexProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ·g H).minDeg = G.minDeg * FinEnum.card H.V + H.minDeg := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_lexProduct G H ((a, b) : (G ·g H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (G ·g H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.minDeg_le_degree _)) (H.minDeg_le_degree _)

@[toIsoGraph]
theorem maxDeg_strongProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ⊠g H).maxDeg = (G.maxDeg + 1) * (H.maxDeg + 1) - 1 := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_strongProduct G H ((a, b) : (G ⊠g H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.degree_le_maxDeg _) _)
      (Nat.add_le_add_right (H.degree_le_maxDeg _) _)) 1
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

@[toIsoGraph]
theorem minDeg_strongProduct {G H : CGraph}
    [Nonempty G.V] [Nonempty H.V] :
    (G ⊠g H).minDeg = (G.minDeg + 1) * (H.minDeg + 1) - 1 := by
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  obtain ⟨b₀⟩ := ‹Nonempty H.V›
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_strongProduct G H ((a, b) : (G ⊠g H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (G ⊠g H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.minDeg_le_degree _) _)
      (Nat.add_le_add_right (H.minDeg_le_degree _) _)) 1

/-! ### Counting cliques in a disjoint union -/

/-- A clique of a disjoint union that has at least one vertex lies wholly on one of the two
sides, because no edge crosses between them. -/
theorem isNClique_disjUnion_iff {n : ℕ} {s : Finset (G ⊕g H).V} :
    (G ⊕g H).toSimple.IsNClique (n + 1) s ↔ (∃ t : Finset G.V, G.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (∃ t : Finset H.V, H.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inr, Sum.inr_injective⟩) := by
  constructor
  · rintro ⟨hcl, hcard⟩
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    match x, hx with
    | .inl a, ha =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (G ⊕g H).V) := by
        intro y hy
        match y, hy with
        | .inl b, _ => simp
        | .inr d, hd =>
          exact absurd (hcl (by simpa using ha) (by simpa using hd) (by simp))
            (by simp [CGraph.toSimple_adj])
      obtain ⟨t, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      refine Or.inl ⟨t, ⟨?_, by simpa using hcard⟩, rfl⟩
      intro b hb c hc hbc
      have hb' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (G ⊕g H).V) (Finset.mem_coe.1 hb))
      have hc' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (G ⊕g H).V) (Finset.mem_coe.1 hc))
      have := hcl hb' hc' (Sum.inl_injective.ne hbc)
      simpa [CGraph.toSimple_adj] using this
    | .inr b, hb =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (G ⊕g H).V) := by
        intro y hy
        match y, hy with
        | .inr d, _ => simp
        | .inl a, ha =>
          exact absurd (hcl (by simpa using ha) (by simpa using hb) (by simp))
            (by simp [CGraph.toSimple_adj])
      obtain ⟨t, -, rfl⟩ := Finset.subset_map_iff.1 hsub
      refine Or.inr ⟨t, ⟨?_, by simpa using hcard⟩, rfl⟩
      intro c hc d hd hcd
      have hc' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (G ⊕g H).V) (Finset.mem_coe.1 hc))
      have hd' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (G ⊕g H).V) (Finset.mem_coe.1 hd))
      have := hcl hc' hd' (Sum.inr_injective.ne hcd)
      simpa [CGraph.toSimple_adj] using this
  · rintro (⟨t, ⟨hcl, hcard⟩, rfl⟩ | ⟨t, ⟨hcl, hcard⟩, rfl⟩)
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      show (G ⊕g H).toSimple.Adj (Sum.inl a) (Sum.inl b)
      rw [CGraph.toSimple_adj, disjUnion_adj_inl_inl]
      exact hcl ha hb this
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      show (G ⊕g H).toSimple.Adj (Sum.inr a) (Sum.inr b)
      rw [CGraph.toSimple_adj, disjUnion_adj_inr_inr]
      exact hcl ha hb this

/-! ### The components of a disjoint union -/

/-- The inclusion of the left factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInl (G H : CGraph) : G.toSimple →g (G ⊕g H).toSimple where
  toFun := Sum.inl
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- The inclusion of the right factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInr (G H : CGraph) : H.toSimple →g (G ⊕g H).toSimple where
  toFun := Sum.inr
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- Send a vertex of a disjoint union to its component on whichever side it lives. -/
private def duSplit (G H : CGraph) :
    (G ⊕g H).V → G.toSimple.ConnectedComponent ⊕ H.toSimple.ConnectedComponent :=
  Sum.map G.toSimple.connectedComponentMk H.toSimple.connectedComponentMk

private theorem duSplit_eq_of_adj {u v : (G ⊕g H).V}
    (h : (G ⊕g H).toSimple.Adj u v) : duSplit G H u = duSplit G H v := by
  match u, v with
  | Sum.inl a, Sum.inl c =>
    have : G.toSimple.Adj a c := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]
  | Sum.inl a, Sum.inr d => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inl b => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inr d =>
    have : H.toSimple.Adj c d := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]

private theorem duSplit_eq_of_reachable {u v : (G ⊕g H).V}
    (h : (G ⊕g H).toSimple.Reachable u v) : duSplit G H u = duSplit G H v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (duSplit_eq_of_adj hadj).trans ih

/-- **The components of a disjoint union are those of the two factors.** -/
def disjUnionComponentEquiv (G H : CGraph) :
    (G ⊕g H).toSimple.ConnectedComponent ≃
      G.toSimple.ConnectedComponent ⊕ H.toSimple.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.lift (duSplit G H)
    (fun _ _ p _ ↦ duSplit_eq_of_reachable ⟨p⟩)
  invFun := Sum.elim (SimpleGraph.ConnectedComponent.map (disjUnionInl G H))
    (SimpleGraph.ConnectedComponent.map (disjUnionInr G H))
  left_inv := by
    refine SimpleGraph.ConnectedComponent.ind (fun v ↦ ?_)
    match v with
    | Sum.inl a => rfl
    | Sum.inr b => rfl
  right_inv := by
    rintro (c | c)
    · induction c using SimpleGraph.ConnectedComponent.ind with | _ a => rfl
    · induction c using SimpleGraph.ConnectedComponent.ind with | _ b => rfl

/-! ### Components versus the other invariants -/

theorem surjective_connectedComponentMk (G : CGraph) :
    Function.Surjective G.toSimple.connectedComponentMk :=
  fun c ↦ Quot.exists_rep c

/-- An automorphism cannot change the number of neighbours of a vertex. -/
theorem card_nbrs_aut {G : CGraph} (f : G ≃cg G) (x : G.V) :
    (G.nbrs (f x)).card = (G.nbrs x).card := by
  rw [card_nbrs_eq_degree, card_nbrs_eq_degree]
  exact SimpleGraph.Iso.degree_eq f.toSimpleIso x

/-! ### The automorphism count of a cycle

The star was fixed by pinning down one vertex; a cycle is pinned down by pinning down an *arc*.
Every vertex of `Cₙ` has exactly two neighbours, so once an automorphism is known on two adjacent
vertices it is forced everywhere: walking around the rim, the next vertex is the unique neighbour
of the current one other than the previous.  That makes the pair `(f 0, which neighbour of f 0 is
f 1)` a faithful record of `f`, of which there are only `2n`, and arc-transitivity supplies the
matching lower bound.
-/

theorem cyc_mod_succ (N j : ℕ) (hj : j < N) :
    (j + 1) % N = if j + 1 = N then 0 else j + 1 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with h | h
  · rw [if_pos (by omega), show j + 1 = N from by omega, Nat.mod_self]
  · rw [if_neg (by omega), Nat.mod_eq_of_lt h]

theorem cyc_mod_pred (N i : ℕ) (hi : i < N) :
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

/-- An arc-transitive graph has at least `2|E|` automorphisms, one for each arc. -/
@[toIsoGraph]
theorem two_mul_E_le_autCount_of_isArcTransitive (G : CGraph) (h : G.IsArcTransitive) :
    2 * G.E ≤ G.autCount := by
  classical
  rcases Nat.eq_zero_or_pos G.E with hE | hE
  · simp [hE]
  obtain ⟨u₀, v₀, h₀⟩ := exists_adj_of_E_pos hE
  have : Finite (G ≃cg G) := G.instFiniteAut
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
    Even (FinEnum.card G.V) := by
  have hc := G.even_card_odd_degree
  rwa [Finset.filter_true_of_mem fun v _ ↦ h v, FinEnum.card_univ] at hc

/-- **An odd-regular graph has evenly many vertices.**  There is no cubic graph on five
vertices. -/
theorem even_card_of_isRegularOfDegree_odd (G : CGraph) {k : ℕ} (hk : Odd k)
    (h : G.toSimple.IsRegularOfDegree k) : Even (FinEnum.card G.V) :=
  G.even_card_of_forall_odd_degree fun v ↦ by rw [h v]; exact hk

/-- On an odd number of vertices, some vertex has even degree. -/
theorem exists_even_degree_of_odd_card (G : CGraph) (h : Odd (FinEnum.card G.V)) :
    ∃ v, Even (G.toSimple.degree v) := by
  by_contra hc
  push Not at hc
  exact Nat.not_even_iff_odd.2 h
    (G.even_card_of_forall_odd_degree fun v ↦ Nat.not_even_iff_odd.1 (hc v))

@[simp] theorem disjUnionAuto_inl (a : G ≃cg G) (b : H ≃cg H) (x : G.V) :
    disjUnionAuto a b (.inl x) = .inl (a x) := rfl

@[simp] theorem disjUnionAuto_inr (a : G ≃cg G) (b : H ≃cg H) (y : H.V) :
    disjUnionAuto a b (.inr y) = .inr (b y) := rfl

@[simp] theorem disjUnionSwapAuto_inl (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inl x) = .inr x := rfl

@[simp] theorem disjUnionSwapAuto_inr (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inr x) = .inl x := rfl

@[simp] theorem cartesianProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : cartesianProductAuto a b x = (a x.1, b x.2) := rfl

@[simp] theorem tensorProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : tensorProductAuto a b x = (a x.1, b x.2) := rfl

@[simp] theorem strongProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : strongProductAuto a b x = (a x.1, b x.2) := rfl

@[simp] theorem lexProductAuto_apply (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : lexProductAuto a b x = (a x.1, b x.2) := rfl

/-! ### Edge counts of the strong and lexicographic products -/

private theorem sum_degree_add_one (K : CGraph) :
    ∑ v : K.V, (K.toSimple.degree v + 1) = 2 * K.E + FinEnum.card K.V := by
  rw [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_const,
    FinEnum.card_univ, smul_eq_mul, mul_one]
  rfl

theorem E_strongProduct (G H : CGraph) :
    (G ⊠g H).E
      = FinEnum.card G.V * H.E + FinEnum.card H.V * G.E + 2 * G.E * H.E := by
  have hdeg : ∀ p : G.V × H.V, (G ⊠g H).toSimple.degree p + 1
      = (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) := by
    intro p
    have h := degree_strongProduct G H p
    have hpos : 1 ≤ (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  -- The binder `p : G.V × H.V` picks Mathlib's product `Fintype`, while `(G ⊠g H).E` counts with
  -- the one the product graph's own `FinEnum` induces; the two agree, but only propositionally.
  have hdegsum' : ∑ p : (G ⊠g H).V, (G ⊠g H).toSimple.degree p = 2 * (G ⊠g H).E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hdegsum : ∑ p : G.V × H.V, (G ⊠g H).toSimple.degree p = 2 * (G ⊠g H).E :=
    (Finset.sum_univ_inst_eq _ _ _).trans hdegsum'
  have hstrong : ∑ p : G.V × H.V, ((G ⊠g H).toSimple.degree p + 1)
      = 2 * (G ⊠g H).E + FinEnum.card G.V * FinEnum.card H.V := by
    rw [Finset.sum_add_distrib, hdegsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, ← FinEnum.card_eq_fintypeCard' (α := G.V),
      ← FinEnum.card_eq_fintypeCard' (α := H.V)]
  have key : 2 * (G ⊠g H).E + FinEnum.card G.V * FinEnum.card H.V
      = (2 * G.E + FinEnum.card G.V) * (2 * H.E + FinEnum.card H.V) := by
    rw [← hstrong, ← sum_degree_add_one G, ← sum_degree_add_one H, Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b)
  have expand : (2 * G.E + FinEnum.card G.V) * (2 * H.E + FinEnum.card H.V)
      = 2 * (FinEnum.card G.V * H.E + FinEnum.card H.V * G.E + 2 * G.E * H.E)
        + FinEnum.card G.V * FinEnum.card H.V := by ring
  rw [expand] at key
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel key)

theorem E_lexProduct (G H : CGraph) :
    (G ·g H).E
      = FinEnum.card H.V * FinEnum.card H.V * G.E + FinEnum.card G.V * H.E := by
  have hdeg : ∀ p : G.V × H.V, (G ·g H).toSimple.degree p
      = G.toSimple.degree p.1 * FinEnum.card H.V + H.toSimple.degree p.2 :=
    fun p ↦ degree_lexProduct G H p
  have hG : ∑ a : G.V, G.toSimple.degree a = 2 * G.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hH : ∑ b : H.V, H.toSimple.degree b = 2 * H.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  -- as in `E_strongProduct`, the product binder's `Fintype` is not the product graph's own
  have hlex' : ∑ p : (G ·g H).V, (G ·g H).toSimple.degree p = 2 * (G ·g H).E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hlex : ∑ p : G.V × H.V, (G ·g H).toSimple.degree p = 2 * (G ·g H).E :=
    (Finset.sum_univ_inst_eq _ _ _).trans hlex'
  have hfibre : ∀ a : G.V,
      ∑ b : H.V, (G.toSimple.degree a * FinEnum.card H.V + H.toSimple.degree b)
        = G.toSimple.degree a * (FinEnum.card H.V * FinEnum.card H.V) + 2 * H.E := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_const, FinEnum.card_univ, smul_eq_mul, hH]
    ring
  have key : 2 * (G ·g H).E
      = 2 * (FinEnum.card H.V * FinEnum.card H.V * G.E + FinEnum.card G.V * H.E) := by
    rw [← hlex, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b),
      Finset.sum_congr rfl fun a _ ↦ hfibre a, Finset.sum_add_distrib, ← Finset.sum_mul, hG,
      Finset.sum_const, FinEnum.card_univ, smul_eq_mul]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-! ### Domination in disjoint unions, joins and cartesian products -/

theorem isDominatingSet_disjSum {G H : CGraph} {s : Finset G.V} {t : Finset H.V}
    (hs : G.IsDominatingSet s) (ht : H.IsDominatingSet t) :
    (G ⊕g H).IsDominatingSet (s.disjSum t) := by
  intro v
  rcases v with a | b
  · rcases hs a with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inl_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inl u, Finset.inl_mem_disjSum.2 hu, by simpa using hadj⟩
  · rcases ht b with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inr_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inr u, Finset.inr_mem_disjSum.2 hu, by simpa using hadj⟩

/-! ### Independence numbers of the graph products -/

/-- Independence number is antitone in the graph: adding edges can only shrink it. -/
theorem indepNum_anti {α : Type} [Fintype α] {S T : SimpleGraph α} (h : S ≤ T) :
    T.indepNum ≤ S.indepNum := by
  obtain ⟨s, hs, hcard⟩ := T.exists_isNIndepSet_indepNum
  have hind : S.IsIndepSet (s : Set α) := by
    intro x hx y hy hxy hadj
    exact hs hx hy hxy (h hadj)
  exact hcard ▸ hind.card_le_indepNum

/-- The strong product is a subgraph of the lexicographic product. -/
theorem strongProduct_le_lexProduct (G H : CGraph) :
    (G ⊠g H).toSimple ≤ (G ·g H).toSimple := by
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

theorem ladderCol_proper (N : ℕ) (u v w : (path N □g complete 2).V)
    (huv : (path N □g complete 2).Adj u v = true)
    (huw : (path N □g complete 2).Adj u w = true) (hvw : v ≠ w) :
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

theorem crownCol_proper (n : ℕ) (u v w : (complete (n + 2) ⊗g complete 2).V)
    (huv : (complete (n + 2) ⊗g complete 2).Adj u v = true)
    (huw : (complete (n + 2) ⊗g complete 2).Adj u w = true) (hvw : v ≠ w) :
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

theorem prismCol_proper (n : ℕ) (u v w : (cycle (n + 3) □g complete 2).V)
    (huv : (cycle (n + 3) □g complete 2).Adj u v = true)
    (huw : (cycle (n + 3) □g complete 2).Adj u w = true) (hvw : v ≠ w) :
    prismCol (n + 3) u v ≠ prismCol (n + 3) u w := by
  rw [cartesianProduct_adj] at huv huw
  simp only [complete_adj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    at huv huw
  have step : ∀ x y : (cycle (n + 3) □g complete 2).V,
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
    push Not at hc
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

end

end CGraph

namespace IsoGraph

/-! ## Vertex counts -/

@[simp] theorem V_empty (n : ℕ) : (empty n).V = n := CGraph.card_empty n

@[simp] theorem V_complete (n : ℕ) : (complete n).V = n := CGraph.card_complete n

@[simp] theorem V_path (n : ℕ) : (path n).V = n := CGraph.card_path n

@[simp] theorem V_cycle (n : ℕ) : (cycle n).V = n := CGraph.card_cycle n

@[simp] theorem V_compl (G : IsoGraph) : Gᶜ.V = G.V := by
  induction G using Quotient.inductionOn with
  | h g => show FinEnum.card gᶜ.V = _; simp

@[simp] theorem V_disjUnion (G H : IsoGraph) : (G ⊕g H).V = G.V + H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h => exact CGraph.card_disjUnion g h

@[simp] theorem V_join (G H : IsoGraph) : (G ∇g H).V = G.V + H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h => exact CGraph.card_join g h

@[simp] theorem V_cartesianProduct (G H : IsoGraph) :
    (G □g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show FinEnum.card (g □g h).V = _
      simp

@[simp] theorem V_tensorProduct (G H : IsoGraph) : (G ⊗g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show FinEnum.card (g ⊗g h).V = _
      simp

@[simp] theorem V_strongProduct (G H : IsoGraph) : (G ⊠g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show FinEnum.card (g ⊠g h).V = _
      simp

@[simp] theorem V_lexProduct (G H : IsoGraph) : (G ·g H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show FinEnum.card (g ·g h).V = _
      simp

@[simp] theorem V_exponential (G H : IsoGraph) : (G ^g H).V = G.V ^ H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show FinEnum.card (g ^g h).V = _
      simp

@[simp] theorem V_lineGraph (G : IsoGraph) : (lineGraph G).V = G.E := by
  induction G using Quotient.inductionOn with
  | h g =>
    show FinEnum.card (CGraph.lineGraph g).V = _
    rw [CGraph.card_lineGraph, ← E_mk]

@[simp] theorem V_mycielskian (G : IsoGraph) : (mycielskian G).V = 2 * G.V + 1 := by
  induction G using Quotient.inductionOn with
  | h g =>
    show FinEnum.card (CGraph.mycielskian g).V = _
    simp

/-! ## Recognising `empty` and `complete`

Every degenerate identity in this file goes through one of these two: a graph with no edges is
`empty` on its vertex count, and a graph with all of them is `complete`.  Neither needs an
explicit bijection — the vertex type's own `FinEnum.equiv` supplies one. -/

/-- A graph with no edges is the edgeless graph on its vertex count. -/
theorem mk_eq_empty {G : CGraph} (h : ∀ x y, G.Adj x y = false) :
    (⟦G⟧ : IsoGraph) = empty (FinEnum.card G.V) :=
  Quotient.sound ⟨CGraph.isoOfAdj (FinEnum.equiv (α := G.V)) fun x y ↦ (h x y).symm⟩

/-- A graph in which every two distinct vertices are adjacent is the complete graph on its vertex
count. -/
theorem mk_eq_complete {G : CGraph} (h : ∀ x y, x ≠ y → G.Adj x y = true) :
    (⟦G⟧ : IsoGraph) = complete (FinEnum.card G.V) :=
  Quotient.sound ⟨CGraph.isoOfAdj (FinEnum.equiv (α := G.V)) fun x y ↦ by
    rw [CGraph.complete_adj]
    by_cases hxy : x = y
    · cases hxy
      rw [(Bool.not_eq_true _).mp (G.loopless x)]
      simp
    · rw [h x y hxy]
      exact decide_eq_true fun hh ↦ hxy ((FinEnum.equiv (α := G.V)).injective hh)⟩

/-- The converse of `mk_eq_complete`: a graph whose class is `complete` has every edge. -/
theorem adj_of_mk_eq_complete {G : CGraph} {n : ℕ} (h : (⟦G⟧ : IsoGraph) = complete n)
    {x y : G.V} (hxy : x ≠ y) : G.Adj x y = true := by
  obtain ⟨i⟩ := Quotient.exact h
  rw [← i.adj_eq x y, CGraph.complete_adj]
  exact decide_eq_true fun hc ↦ hxy (i.injective hc)

/-- The converse of `mk_eq_empty`: a graph whose class is `empty` has no edge. -/
theorem adj_eq_false_of_mk_eq_empty {G : CGraph} {n : ℕ} (h : (⟦G⟧ : IsoGraph) = empty n)
    (x y : G.V) : G.Adj x y = false := by
  obtain ⟨i⟩ := Quotient.exact h
  rw [← i.adj_eq x y, CGraph.empty_adj]

/-- A graph with no vertices is the empty graph on `0` vertices. -/
theorem mk_eq_empty_zero {G : CGraph} [IsEmpty G.V] : (⟦G⟧ : IsoGraph) = empty 0 := by
  rw [mk_eq_empty (G := G) fun x _ ↦ isEmptyElim x, FinEnum.card_eq_zero_iff.2 ‹IsEmpty G.V›]

/-- A graph is the empty graph on `0` vertices exactly when it has no vertices. -/
@[simp] theorem V_eq_zero_iff {G : IsoGraph} : G.V = 0 ↔ G = empty 0 := by
  constructor
  · induction G using Quotient.inductionOn with
    | h g =>
      intro h
      have : IsEmpty g.V := FinEnum.card_eq_zero_iff.1 h
      exact mk_eq_empty_zero
  · rintro rfl
    exact V_empty 0

/-- A graph is the empty graph on `1` vertex exactly when it has one vertex: with a single vertex
there is no edge to draw. -/
@[simp] theorem V_eq_one_iff {G : IsoGraph} : G.V = 1 ↔ G = empty 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, V_empty]⟩
  induction G using Quotient.inductionOn with
  | h g =>
    have hcard : FinEnum.card g.V = 1 := h
    have : Subsingleton g.V := by
      have hfin := FinEnum.card_eq_fintypeCard (α := g.V)
      rw [hcard] at hfin
      exact Fintype.card_le_one_iff_subsingleton.1 (le_of_eq hfin.symm)
    rw [show (empty 1 : IsoGraph) = empty (FinEnum.card g.V) by rw [hcard]]
    exact mk_eq_empty fun x y ↦ by
      rw [Subsingleton.elim x y]; simpa using g.loopless y

end IsoGraph

namespace CGraph

/-! ### Bipartite, star, wheel -/

/-- A graph with no edges is the edgeless graph on its vertex count. -/
noncomputable def isoEmptyOfCard {G : CGraph} {n : ℕ} (h : ∀ x y, G.Adj x y = false)
    (hn : FinEnum.card G.V = n) : G ≃cg empty n :=
  isoOfAdj ((FinEnum.equiv (α := G.V)).trans (finCongr hn)) fun x y ↦ (h x y).symm

/-- A graph in which every two distinct vertices are adjacent is the complete graph on its
vertex count. -/
noncomputable def isoCompleteOfCard {G : CGraph} {n : ℕ} (h : ∀ x y, x ≠ y → G.Adj x y = true)
    (hn : FinEnum.card G.V = n) : G ≃cg complete n :=
  isoOfAdj ((FinEnum.equiv (α := G.V)).trans (finCongr hn)) fun x y ↦ by
    rw [complete_adj]
    by_cases hxy : x = y
    · cases hxy
      rw [(Bool.not_eq_true _).mp (G.loopless x)]
      simp
    · rw [h x y hxy]
      exact decide_eq_true fun hh ↦ hxy
        (((FinEnum.equiv (α := G.V)).trans (finCongr hn)).injective hh)

/-- The tensor product with an edgeless graph is edgeless. -/
@[toIsoGraph simp tensorProduct_empty]
noncomputable def tensorProductEmpty (G : CGraph) (n : ℕ) :
    G ⊗g empty n ≃cg empty (FinEnum.card G.V * n) :=
  isoEmptyOfCard (by simp) (by simp)

@[toIsoGraph simp empty_tensorProduct]
noncomputable def emptyTensorProduct (n : ℕ) (G : CGraph) :
    empty n ⊗g G ≃cg empty (n * FinEnum.card G.V) :=
  isoEmptyOfCard (by simp) (by simp)

end CGraph

namespace IsoGraph

@[simp] theorem E_disjUnion (G H : IsoGraph) : (G ⊕g H).E = G.E + H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.E_disjUnion g h

@[simp] theorem E_join (G H : IsoGraph) : (G ∇g H).E = G.E + H.E + G.V * H.V := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_join _ _

@[simp] theorem E_cartesianProduct (G H : IsoGraph) :
    (G □g H).E = G.V * H.E + H.V * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_cartesianProduct _ _

@[simp] theorem E_tensorProduct (G H : IsoGraph) : (G ⊗g H).E = 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, E_mk, E_mk, E_mk]
  exact CGraph.E_tensorProduct _ _

@[simp] theorem E_mycielskian (G : IsoGraph) : (mycielskian G).E = 3 * G.E + G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, E_mk, E_mk, V_mk]
  exact CGraph.E_mycielskian _

@[simp] theorem degMultiset_join (G H : IsoGraph) :
    degMultiset (G ∇g H) = (degMultiset G).map (· + H.V) + (degMultiset H).map (· + G.V) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, degMultiset_mk, degMultiset_mk,
    degMultiset_mk, V_mk, V_mk]
  exact CGraph.degMultiset_join _ _

@[simp] theorem degMultiset_compl (G : IsoGraph) :
    degMultiset Gᶜ = (degMultiset G).map (fun d ↦ G.V - 1 - d) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_compl _

/-! ### Degree multisets of the four products

The vertex set of a product is a product, so its degree multiset is a `Multiset.bind`: run over
the degrees of the left factor, and for each of them map the degrees of the right factor through
whatever the product does to a pair of degrees. -/

@[simp] theorem degMultiset_cartesianProduct (G H : IsoGraph) :
    degMultiset (G □g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_cartesianProduct _ _

@[simp] theorem degMultiset_tensorProduct (G H : IsoGraph) :
    degMultiset (G ⊗g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_tensorProduct _ _

@[simp] theorem degMultiset_lexProduct (G H : IsoGraph) :
    degMultiset (G ·g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * H.V + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_lexProduct _ _

@[simp] theorem degMultiset_strongProduct (G H : IsoGraph) :
    degMultiset (G ⊠g H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ (d + 1) * (e + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_strongProduct _ _

/-! ### Maximum and minimum degree -/

/-! ### Basic API -/

/-- A regular graph, read off its degree multiset: both extremes are the common degree. -/
theorem maxDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : maxDeg G = k :=
  maxDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ le_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

theorem minDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : minDeg G = k :=
  minDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ ge_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

theorem ne_of_maxDeg_ne {G H : IsoGraph} (h : maxDeg G ≠ maxDeg H) : G ≠ H :=
  ne_of_apply_ne maxDeg h

theorem ne_of_minDeg_ne {G H : IsoGraph} (h : minDeg G ≠ minDeg H) : G ≠ H :=
  ne_of_apply_ne minDeg h

/-! ### Greedy colouring and Nordhaus–Gaddum -/

/-! ### Edge counts of the strong and lexicographic products -/

@[simp] theorem E_strongProduct (G H : IsoGraph) :
    (G ⊠g H).E = G.V * H.E + H.V * G.E + 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_strongProduct _ _

@[simp] theorem E_lexProduct (G H : IsoGraph) :
    (G ·g H).E = H.V * H.V * G.E + G.V * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_lexProduct _ _

theorem E_strongProduct_eq_add (G H : IsoGraph) :
    (G ⊠g H).E = (G □g H).E + (G ⊗g H).E := by
  rw [E_strongProduct, E_cartesianProduct, E_tensorProduct]

theorem le_minDeg_lineGraph {G : IsoGraph} (h : 0 < G.E) :
    2 * G.minDeg - 2 ≤ (lineGraph G).minDeg := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [E_mk] at h
  rw [lineGraph_mk, minDeg_mk, minDeg_mk]
  refine CGraph.le_minDeg_lineGraph _ ?_
  have hcard : 0 < FinEnum.card (CGraph.lineGraph g.canonicalize).V := by
    rwa [CGraph.card_lineGraph]
  exact (FinEnum.card_pos_iff.1 hcard).some

/-- Each original vertex of `μ(G)` has its degree doubled, each shadow gains the apex, and the
apex sees every shadow. -/
@[simp] theorem degMultiset_mycielskian (G : IsoGraph) :
    (mycielskian G).degMultiset
      = G.degMultiset.map (fun d ↦ 2 * d) + G.degMultiset.map (fun d ↦ d + 1) + {G.V} := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, degMultiset_mk, degMultiset_mk, V_mk]
  set F := g.canonicalize
  let H := (CGraph.mycielskian F).toSimple
  -- The three kinds of vertex, with the degrees computed once and for all above.
  have hdeg_inl : ∀ a : F.V, H.degree (some (Sum.inl a)) = 2 * F.toSimple.degree a :=
    CGraph.degree_mycielskian_inl F
  have hdeg_inr : ∀ a : F.V, H.degree (some (Sum.inr a)) = F.toSimple.degree a + 1 :=
    CGraph.degree_mycielskian_inr F
  have hdeg_none : H.degree none = FinEnum.card F.V := CGraph.degree_mycielskian_none F
  -- Now compute degMultiset.  Unfolding leaves the goal talking about
  -- `(CGraph.mycielskian F).toSimple` and counting with the `Fintype` the graph's own `FinEnum`
  -- induces; the `show` folds the graph back to `H`, and the rewrite moves to Mathlib's `Fintype`
  -- on `Option`, which is the instance the split below is `rfl` for.
  unfold CGraph.degMultiset
  show Multiset.map (fun v => H.degree v) (Finset.univ : Finset (CGraph.mycielskian F).V).val = _
  rw [show (Finset.univ : Finset (CGraph.mycielskian F).V) =
      (Finset.univ : Finset (Option (F.V ⊕ F.V))) from Finset.univ_inst_eq _ _]
  have option_split_FV_FV :
      Multiset.map (fun v => H.degree v) (Finset.univ : Finset (Option (F.V ⊕ F.V))).val =
        [(fun v => H.degree v) none] +
        Multiset.map (fun v => H.degree v) ((Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some,
            Option.some_injective (F.V ⊕ F.V)⟩).val := by
    have : (Finset.univ : Finset (Option (F.V ⊕ F.V))).val =
        none ::ₘ ((Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some, Option.some_injective (F.V ⊕
            F.V)⟩).val := by
      rfl
    rw [this]; simp [Multiset.map_cons]
  rw [option_split_FV_FV]
  -- univ(F.V ⊕ F.V).val = univ(F.V).val.map inl + univ(F.V).val.map inr
  have hsum_univ : (Finset.univ : Finset (F.V ⊕ F.V)).val =
      (Finset.univ : Finset F.V).val.map Sum.inl + (Finset.univ : Finset F.V).val.map Sum.inr := by
    rfl
  simp only [hdeg_none]
  -- Rewrite the Finset.map over Option (F.V ⊕ F.V) to expose inl/inr
  have hmap_split : (Finset.univ : Finset (F.V ⊕ F.V)).map ⟨some, Option.some_injective _⟩ =
      ((Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) ∪
      ((Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) := by
    ext x; simp
  have hdisjoint : Disjoint
      ((Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V)))
      ((Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ :
          F.V ↪ Option (F.V ⊕ F.V))) := by
    rw [Finset.disjoint_left]
    simp
  rw [hmap_split]
  have hcoe_union :
      ((Finset.map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕
          F.V)) Finset.univ ∪
        Finset.map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕
            F.V)) Finset.univ : Finset (Option (F.V ⊕ F.V))).val
      = (Finset.map (⟨fun a => some (Sum.inl a), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V
          ⊕ F.V)) Finset.univ).val +
        (Finset.map (⟨fun b => some (Sum.inr b), fun x y h => by cases h; rfl⟩ : F.V ↪ Option (F.V
            ⊕ F.V)) Finset.univ).val) := by
    set S1 := (Finset.univ : Finset F.V).map (⟨fun a => some (Sum.inl a), fun x y h =>
        by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕ F.V))
    set S2 := (Finset.univ : Finset F.V).map (⟨fun b => some (Sum.inr b), fun x y h =>
        by cases h; rfl⟩ : F.V ↪ Option (F.V ⊕ F.V))
    have : (S1 ∪ S2 : Finset (Option (F.V ⊕ F.V))) = S1.disjUnion S2 hdisjoint := by
      simp [Finset.disjUnion_eq_union]
    rw [this]
    simp [Finset.disjUnion]
  rw [hcoe_union, Multiset.map_add]
  have hmap_inl : Multiset.map (fun v => H.degree v)
      (Finset.map (⟨fun a => some (Sum.inl a), fun x y h => Sum.inl_injective
          (Option.some_injective _ h)⟩ : F.V ↪ Option (F.V ⊕ F.V)) Finset.univ).val =
      Multiset.map (fun a => H.degree (some (Sum.inl a))) Finset.univ.val := by
    simp [Finset.map_val, Multiset.map_map]
  have hmap_inr : Multiset.map (fun v => H.degree v)
      (Finset.map (⟨fun b => some (Sum.inr b), fun x y h => Sum.inr_injective
          (Option.some_injective _ h)⟩ : F.V ↪ Option (F.V ⊕ F.V)) Finset.univ).val =
      Multiset.map (fun b => H.degree (some (Sum.inr b))) Finset.univ.val := by
    simp [Finset.map_val, Multiset.map_map]
  rw [hmap_inl, hmap_inr]
  rw [Multiset.map_congr rfl fun x _ => hdeg_inl x, Multiset.map_congr rfl fun x _ => hdeg_inr x]
  simp only [F]
  simp
  -- What is left is the apex's degree, on the left as the head of the multiset and on the right
  -- as a singleton summand.
  rw [add_comm _ ({FinEnum.card g.V} : Multiset ℕ), Multiset.singleton_add]

/-- The minimum degree of a Mycielskian: the three kinds of vertex give `2δ`, `δ + 1` and `n`. -/
theorem minDeg_mycielskian (G : IsoGraph) (h : 0 < G.V) :
    (mycielskian G).minDeg = min (min (2 * G.minDeg) (G.minDeg + 1)) G.V := by
  induction G using Quotient.inductionOn' with | _ G0
  let H := G0.canonicalize
  have hG : (⟦G0⟧ : IsoGraph) = ⟦H⟧ := (mk_canonicalize G0).symm
  have hmyci : mycielskian (⟦G0⟧ : IsoGraph) = ⟦H.mycielskian⟧ := by
    rw [hG, IsoGraph.mycielskian_mk]
  have hmindeg : (mycielskian (⟦G0⟧ : IsoGraph)).minDeg = H.mycielskian.minDeg := by
    rw [hmyci, minDeg_mk]
  have hv : IsoGraph.V ⟦G0⟧ = FinEnum.card H.V := by
    simp [V_mk, H, CGraph.canonicalize_V]
  rw [hmindeg, hv, minDeg_mk]
  have hmindeg_eq : G0.minDeg = H.minDeg := by
    unfold CGraph.minDeg H
    exact SimpleGraph.Iso.minDegree_eq (CGraph.Iso.toSimpleIso G0.isoCanonicalize)
  rw [hmindeg_eq]
  have hDM_iso := degMultiset_mycielskian ⟦H⟧
  rw [degMultiset_mk] at hDM_iso
  -- `degMultiset_mk` again, to read `(mycielskian ⟦H⟧).degMultiset` as
  -- `H.mycielskian.degMultiset`
  rw [IsoGraph.mycielskian_mk, degMultiset_mk] at hDM_iso
  have hVH : V ⟦H⟧ = FinEnum.card H.V := by simp [IsoGraph.V]
  have hVH_pos : 0 < V ⟦H⟧ := hG.symm ▸ h
  have hHpos : 0 < FinEnum.card H.V := hVH.symm ▸ hVH_pos
  have : Nonempty H.V := FinEnum.card_pos_iff.mp hHpos
  have hmin_mem : H.minDeg ∈ H.degMultiset := by
    obtain ⟨v, hv⟩ := H.exists_degree_eq_minDeg (Classical.choice ‹Nonempty H.V›)
    exact CGraph.mem_degMultiset.2 ⟨v, hv⟩
  have hge_min : ∀ d ∈ H.degMultiset, H.minDeg ≤ d := by
    intro d hd
    obtain ⟨v, hv⟩ := CGraph.mem_degMultiset.1 hd
    exact hv ▸ H.minDeg_le_degree v
  have h2min_mem : 2 * H.minDeg ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr
        ⟨H.minDeg, hmin_mem, rfl⟩))))
  have hmin1_mem : H.minDeg + 1 ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr
        ⟨H.minDeg, hmin_mem, rfl⟩))))
  have hcard_mem : FinEnum.card H.V ∈ H.mycielskian.degMultiset := by
    rw [hDM_iso, hVH]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
  have hkmem :
      min (min (2 * H.minDeg) (H.minDeg + 1)) (FinEnum.card H.V) ∈ H.mycielskian.degMultiset := by
    have : min (2 * H.minDeg) (H.minDeg + 1) ∈ H.mycielskian.degMultiset := by
      rcases le_total (2 * H.minDeg) (H.minDeg + 1) with h | h
      · rw [min_eq_left h]
        exact h2min_mem
      · rw [min_eq_right h]
        exact hmin1_mem
    rcases le_total (min (2 * H.minDeg) (H.minDeg + 1)) (FinEnum.card H.V) with h | h
    · rw [min_eq_left h]
      exact this
    · rw [min_eq_right h]
      exact hcard_mem
  have hlower : ∀ d ∈ H.mycielskian.degMultiset, min (min (2 * H.minDeg) (H.minDeg +
      1)) (FinEnum.card H.V) ≤ d := by
    intro d hd
    rw [hDM_iso] at hd
    simp only [Multiset.mem_add, Multiset.mem_map, Multiset.mem_singleton] at hd
    rcases hd with h | h
    · rcases h with h | h
      · -- 2 * a = d
        obtain ⟨a, ha, rfl⟩ := h
        exact min_le_of_left_le (min_le_of_left_le (by linarith [hge_min a ha]))
      · -- a + 1 = d
        obtain ⟨a, ha, hd_eq⟩ := h
        rw [← hd_eq]
        exact min_le_of_left_le (min_le_of_right_le (by linarith [hge_min a ha]))
    · -- d = V ⟦H⟧
      subst h
      exact min_le_right _ _
  exact CGraph.minDeg_eq_of_degMultiset hkmem hlower

/-- In the Mycielskian each original vertex has its degree doubled, each shadow vertex has one
more neighbour than its original, and the apex sees every shadow. -/
@[simp] theorem maxDeg_mycielskian (G : IsoGraph) :
    maxDeg (mycielskian G) = max (2 * maxDeg G) G.V := by
  induction G using Quotient.inductionOn with
  | h g =>
    simp [maxDeg_mk, mycielskian_mk, IsoGraph.V]
    set H : CGraph := g.mycielskian
    set Hs := H.toSimple
    -- The three kinds of vertex, with the degrees computed once and for all in `Core/Counts`.
    have hdeg_inl : ∀ a : g.V, Hs.degree (some (Sum.inl a)) = 2 * g.toSimple.degree a :=
      CGraph.degree_mycielskian_inl g
    have hdeg_inr : ∀ a : g.V, Hs.degree (some (Sum.inr a)) = g.toSimple.degree a + 1 :=
      CGraph.degree_mycielskian_inr g
    have hdeg_none : Hs.degree none = FinEnum.card g.V := CGraph.degree_mycielskian_none g
    -- Now prove maxDeg ≤ ...
    apply le_antisymm
    · -- All vertices of H have degree ≤ max (2 * maxDeg g) |V(g)|
      apply CGraph.maxDeg_le_of_forall
      intro v
      rcases v with _ | (v | v)
      · rw [hdeg_none]
        exact le_max_of_le_right (le_refl _)
      · rw [hdeg_inl]
        exact le_max_of_le_left (by linarith [CGraph.degree_le_maxDeg g v])
      · rw [hdeg_inr]
        have h1 : g.toSimple.degree v + 1 ≤ FinEnum.card g.V := by
          linarith [CGraph.degree_le_maxDeg g v, @CGraph.maxDeg_lt_card g ⟨v⟩]
        exact le_max_of_le_right h1
    · -- Reverse: max (2 * maxDeg g) |V(g)| ≤ maxDeg H
      have hnone : FinEnum.card g.V ≤ H.maxDeg := by
        rw [← hdeg_none]
        exact CGraph.degree_le_maxDeg H none
      have hinl_maxdeg : 2 * g.maxDeg ≤ H.maxDeg := by
        rcases isEmpty_or_nonempty g.V with hempty | ⟨v₀⟩
        · simp [CGraph.maxDeg]
        · obtain ⟨v, hv⟩ := CGraph.exists_degree_eq_maxDeg g (v₀.some)
          rw [← hv, ← hdeg_inl]
          exact CGraph.degree_le_maxDeg H (some (Sum.inl v))
      exact max_le hinl_maxdeg hnone

/-- All `n` shadows are pairwise non-adjacent. -/
theorem V_le_indepNum_mycielskian (G : IsoGraph) : G.V ≤ (mycielskian G).indepNum := by
  induction G using Quotient.inductionOn with
  | h g =>
    simp [V, indepNum, mycielskian]
    -- Goal: FinEnum.card g.V ≤ g.mycielskian.indepNum
    -- The shadows form an independent set of size FinEnum.card g.V
    let n := FinEnum.card g.V
    let shadows : Finset (CGraph.mycielskian g).V := Finset.image (some ∘
        Sum.inr) Finset.univ
    have hind : (CGraph.mycielskian g).toSimple.IsIndepSet (shadows : Set _) := by
      intro x hx y hy hne hadj
      simp [shadows] at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      subst hi hj
      simp [CGraph.toSimple_adj] at hadj
    have hcard : shadows.card = n := by
      have hinj : Function.Injective (some ∘ Sum.inr : g.V → (CGraph.mycielskian g).V) := by
        intro a b h
        have := Option.some_injective _ h
        exact Sum.inr_injective this
      simp [shadows, Finset.card_image_of_injective _ hinj]
      rfl
    show n ≤ (CGraph.mycielskian g).indepNum
    exact hcard ▸ hind.card_le_indepNum

/-! ### The line graph of a Mycielskian -/

theorem E_pos_mycielskian {G : IsoGraph} (h : 0 < G.V) : 0 < (mycielskian G).E := by
  rw [E_mycielskian]
  omega

theorem maxDeg_lineGraph_mycielskian_le (G : IsoGraph) :
    maxDeg (lineGraph (mycielskian G)) ≤ 2 * max (2 * maxDeg G) G.V - 2 := by
  have hm := maxDeg_lineGraph_le (mycielskian G)
  rwa [maxDeg_mycielskian] at hm

theorem le_minDeg_lineGraph_mycielskian {G : IsoGraph} (hV : 0 < G.V) :
    2 * min (min (2 * G.minDeg) (G.minDeg + 1)) G.V - 2
      ≤ minDeg (lineGraph (mycielskian G)) := by
  have hm := le_minDeg_lineGraph (G := mycielskian G) (E_pos_mycielskian hV)
  rwa [minDeg_mycielskian G hV] at hm

theorem maxDeg_mycielskian_lineGraph (G : IsoGraph) :
    maxDeg (mycielskian (lineGraph G)) = max (2 * maxDeg (lineGraph G)) G.E := by
  rw [maxDeg_mycielskian, V_lineGraph]

theorem E_le_indepNum_mycielskian_lineGraph (G : IsoGraph) :
    G.E ≤ (mycielskian (lineGraph G)).indepNum := by
  have h := V_le_indepNum_mycielskian (lineGraph G)
  rwa [V_lineGraph] at h

/-! ### The iterated Mycielskian -/

theorem minDeg_mycielskian_of_pos {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    (mycielskian G).minDeg = min (G.minDeg + 1) G.V := by
  have hm := minDeg_mycielskian G hV
  omega

@[simp] theorem V_mycielskian_mycielskian (G : IsoGraph) :
    (mycielskian (mycielskian G)).V = 4 * G.V + 3 := by
  rw [V_mycielskian, V_mycielskian]
  omega

@[simp] theorem E_mycielskian_mycielskian (G : IsoGraph) :
    (mycielskian (mycielskian G)).E = 9 * G.E + 5 * G.V + 1 := by
  rw [E_mycielskian, E_mycielskian, V_mycielskian]
  omega

theorem maxDeg_mycielskian_mycielskian (G : IsoGraph) :
    maxDeg (mycielskian (mycielskian G)) = max (2 * max (2 * maxDeg G) G.V) (2 * G.V + 1) := by
  rw [maxDeg_mycielskian, maxDeg_mycielskian, V_mycielskian]

theorem V_le_indepNum_mycielskian_mycielskian (G : IsoGraph) :
    2 * G.V + 1 ≤ (mycielskian (mycielskian G)).indepNum := by
  have h := V_le_indepNum_mycielskian (mycielskian G)
  rwa [V_mycielskian] at h

/-! ### Edge positivity for the binary operators -/

theorem E_pos_cartesianProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G □g H).E := by
  have h := Nat.mul_pos hH hG
  rw [E_cartesianProduct]
  omega

theorem E_pos_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) : 0 < (G ∇g H).E := by
  have h := Nat.mul_pos hG hH
  rw [E_join]
  omega

theorem E_pos_disjUnion_left {G H : IsoGraph} (hG : 0 < G.E) : 0 < (G ⊕g H).E := by
  rw [E_disjUnion]
  omega

theorem E_pos_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G ⊠g H).E := by
  have h := Nat.mul_pos hH hG
  rw [E_strongProduct]
  omega

/-! ### The line graph of a Cartesian product -/

theorem maxDeg_lineGraph_cartesianProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G □g H)) ≤ 2 * (maxDeg G + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G □g H)
  rwa [maxDeg_cartesianProduct hG hH] at h

theorem le_minDeg_lineGraph_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G □g H).E) :
    2 * (minDeg G + minDeg H) - 2 ≤ minDeg (lineGraph (G □g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_cartesianProduct hG hH] at h

/-! ### The line graph of a join -/

theorem maxDeg_lineGraph_join_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ∇g H)) ≤ 2 * max (maxDeg G + H.V) (G.V + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ∇g H)
  rwa [maxDeg_join hG hH] at h

theorem le_minDeg_lineGraph_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    2 * min (minDeg G + H.V) (G.V + minDeg H) - 2 ≤ minDeg (lineGraph (G ∇g H)) := by
  have h := le_minDeg_lineGraph (E_pos_join hG hH)
  rwa [minDeg_join hG hH] at h

/-! ### The line graph of a disjoint union -/

theorem maxDeg_lineGraph_disjUnion_le (G H : IsoGraph) :
    maxDeg (lineGraph (G ⊕g H)) ≤ 2 * max (maxDeg G) (maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊕g H)
  rwa [maxDeg_disjUnion] at h

theorem le_minDeg_lineGraph_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊕g H).E) :
    2 * min (minDeg G) (minDeg H) - 2 ≤ minDeg (lineGraph (G ⊕g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_disjUnion hG hH] at h

/-! ### The line graph of a strong product -/

theorem maxDeg_lineGraph_strongProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ⊠g H)) ≤ 2 * ((maxDeg G + 1) * (maxDeg H + 1) - 1) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊠g H)
  rwa [maxDeg_strongProduct hG hH] at h

theorem le_minDeg_lineGraph_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊠g H).E) :
    2 * ((minDeg G + 1) * (minDeg H + 1) - 1) - 2 ≤ minDeg (lineGraph (G ⊠g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_strongProduct hG hH] at h

/-! ### The Mycielskian of a join -/

@[simp] theorem V_mycielskian_join (G H : IsoGraph) :
    (mycielskian (G ∇g H)).V = 2 * G.V + 2 * H.V + 1 := by
  rw [V_mycielskian, V_join]
  omega

@[simp] theorem E_mycielskian_join (G H : IsoGraph) :
    (mycielskian (G ∇g H)).E = 3 * G.E + 3 * H.E + 3 * (G.V * H.V) + G.V + H.V := by
  rw [E_mycielskian, E_join, V_join]
  omega

theorem maxDeg_mycielskian_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ∇g H))
      = max (2 * max (maxDeg G + H.V) (G.V + maxDeg H)) (G.V + H.V) := by
  rw [maxDeg_mycielskian, maxDeg_join hG hH, V_join]

/-! ### The Mycielskian of a Cartesian product -/

@[simp] theorem E_mycielskian_cartesianProduct (G H : IsoGraph) :
    (mycielskian (G □g H)).E = 3 * (G.V * H.E) + 3 * (H.V * G.E) + G.V * H.V := by
  rw [E_mycielskian, E_cartesianProduct, V_cartesianProduct]
  omega

theorem maxDeg_mycielskian_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G □g H)) = max (2 * (maxDeg G + maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_cartesianProduct hG hH, V_cartesianProduct]

/-! ### The Mycielskian of a disjoint union -/

@[simp] theorem V_mycielskian_disjUnion (G H : IsoGraph) :
    (mycielskian (G ⊕g H)).V = 2 * G.V + 2 * H.V + 1 := by
  rw [V_mycielskian, V_disjUnion]
  omega

@[simp] theorem E_mycielskian_disjUnion (G H : IsoGraph) :
    (mycielskian (G ⊕g H)).E = 3 * G.E + 3 * H.E + G.V + H.V := by
  rw [E_mycielskian, E_disjUnion, V_disjUnion]
  omega

/-! ### The Mycielskian of a strong product -/

@[simp] theorem E_mycielskian_strongProduct (G H : IsoGraph) :
    (mycielskian (G ⊠g H)).E
      = 3 * (G.V * H.E) + 3 * (H.V * G.E) + 3 * (2 * G.E * H.E) + G.V * H.V := by
  rw [E_mycielskian, E_strongProduct, V_strongProduct]
  omega

/-! ### Edge positivity for the tensor and lexicographic products -/

theorem E_pos_tensorProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    0 < (G ⊗g H).E := by
  rw [E_tensorProduct]
  exact Nat.mul_pos (by omega) hH

theorem E_pos_lexProduct_left {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    0 < (G ·g H).E := by
  have h : 0 < H.V * H.V * G.E := Nat.mul_pos (Nat.mul_pos hH hH) hG
  rw [E_lexProduct]
  omega

theorem E_pos_lexProduct_right {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.E) :
    0 < (G ·g H).E := by
  have h : 0 < G.V * H.E := Nat.mul_pos hG hH
  rw [E_lexProduct]
  omega

/-! ### The line graph of a tensor product -/

theorem maxDeg_lineGraph_tensorProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ⊗g H)) ≤ 2 * (maxDeg G * maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ⊗g H)
  rwa [maxDeg_tensorProduct hG hH] at h

theorem le_minDeg_lineGraph_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ⊗g H).E) :
    2 * (minDeg G * minDeg H) - 2 ≤ minDeg (lineGraph (G ⊗g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_tensorProduct hG hH] at h

/-! ### The line graph of a lexicographic product -/

theorem maxDeg_lineGraph_lexProduct_le {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lineGraph (G ·g H)) ≤ 2 * (maxDeg G * H.V + maxDeg H) - 2 := by
  have h := maxDeg_lineGraph_le (G ·g H)
  rwa [maxDeg_lexProduct hG hH] at h

theorem le_minDeg_lineGraph_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < (G ·g H).E) :
    2 * (minDeg G * H.V + minDeg H) - 2 ≤ minDeg (lineGraph (G ·g H)) := by
  have h := le_minDeg_lineGraph hE
  rwa [minDeg_lexProduct hG hH] at h

/-! ### The Mycielskian of a tensor product -/

theorem maxDeg_mycielskian_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ⊗g H)) = max (2 * (maxDeg G * maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_tensorProduct hG hH, V_tensorProduct]

/-! ### The Mycielskian of a lexicographic product -/

@[simp] theorem E_mycielskian_lexProduct (G H : IsoGraph) :
    (mycielskian (G ·g H)).E = 3 * (H.V * H.V * G.E) + 3 * (G.V * H.E) + G.V * H.V := by
  rw [E_mycielskian, E_lexProduct, V_lexProduct]
  omega

theorem maxDeg_mycielskian_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (mycielskian (G ·g H)) = max (2 * (maxDeg G * H.V + maxDeg H)) (G.V * H.V) := by
  rw [maxDeg_mycielskian, maxDeg_lexProduct hG hH, V_lexProduct]

/-! ### No Mycielskian of a regular graph is transitive

`μ(G)` keeps the old degrees at `2k` on the copied vertices but gives the apex degree `|V|`, so as
soon as `G` is `k`-regular with `k ≥ 2` the Mycielskian has two different degrees.  The minimum
degree stays positive, so arc-transitivity fails as well. -/

theorem minDeg_mycielskian_pos {G : IsoGraph} (hV : 0 < G.V) (hδ : 0 < G.minDeg) :
    0 < minDeg (mycielskian G) := by
  rw [minDeg_mycielskian G hV]
  omega

end IsoGraph
