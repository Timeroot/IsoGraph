import IsoGraph.SmallGraphs.Symmetry

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Colourings, cliques and independent sets of the named graphs

Chromatic numbers and indices, clique and independence numbers, covers, dominating sets and
matchings of the named graphs.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

@[simp] theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n := by
  rw [bipartite_eq_compl, indepNum_compl, cliqueNum_disjUnion, cliqueNum_complete,
    cliqueNum_complete]

@[simp] theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 := by
  simp only [bipartite_eq_compl, cliqueNum_compl, indepNum_disjUnion, indepNum_complete]
  omega

/-- The supremum of a list, read through `Finset.sup` over its indices, is `List.max?`. -/
private theorem sup_get_eq_max? (l : List ℕ) (s : Finset (Fin l.length)) (hs : ∀ i, i ∈ s) :
    (s.sup fun i ↦ l.get i) = l.max?.getD 0 := by
  rw [Finset.eq_univ_iff_forall.mpr hs]
  clear hs
  clear s
  induction l with
  | nil => simp [List.max?]
  | cons a tl ih =>
    simp only [List.length_cons]
    have hsplit : ∀ f : Fin (tl.length + 1) → ℕ, Finset.univ.sup f =
        max (f 0) (Finset.univ.sup fun i : Fin tl.length ↦ f i.succ) := by
      intro f
      have huniv : (Finset.univ : Finset (Fin (tl.length + 1))) =
          {(0 : Fin (tl.length + 1))} ∪ Finset.image Fin.succ (Finset.univ : Finset
            (Fin tl.length)) := by
        ext i; simp [Finset.mem_univ]
      rw [huniv, Finset.sup_union, Finset.sup_singleton, Finset.sup_image]
      rfl
    rw [hsplit, show ((a :: tl).get 0 : ℕ) = a from rfl,
      Finset.sup_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ (by simp : (a :: tl).get i.succ =
        tl.get i)), ih]
    cases htl : tl.max? with
    | none => simp_all
    | some b => simp [List.max?_cons, htl]

/-- **The independence number of a complete multipartite graph is its largest part.**  Complements
into `cliqueNum_sigmaUnion`: a clique of the disjoint union of the parts is a subset of one
part. -/
@[simp] theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 := by
  simp only [completeMultipartite_eq_compl, indepNum_compl, cliqueNum_sigmaUnion,
    cliqueNum_complete]
  exact sup_get_eq_max? ds _ (fun i ↦ by simp)

end

section
open Fintype
variable (G : CGraph)

/-! ### Sanity checks

The decision procedure agrees with the structural lemmas on small cases, and does see asymmetry
where there is some. -/

example : (cycle 4).IsVertexTransitive := by decide

example : (cycle 4).IsArcTransitive := by decide

example : (complete 3).IsArcTransitive := by decide

example : ¬(path 4).IsVertexTransitive := by decide

example : ¬(star 3).IsVertexTransitive := by decide

example : (bipartite 2 2).IsArcTransitive := by decide

example : (hypercube 2).IsArcTransitive := by decide

example : (kneser 4 2).IsArcTransitive := by
  set_option maxRecDepth 4000 in decide

/-- The structural lemmas give the same answers. -/
example : (bipartite 2 2).IsVertexTransitive := isVertexTransitive_bipartite_self 2

example : (lineGraph (cycle 4)).IsVertexTransitive :=
  isVertexTransitive_lineGraph _ (isArcTransitive_cycle 4)

example : (cycle 4 □g complete 2).IsVertexTransitive :=
  isVertexTransitive_cartesianProduct _ _ (isVertexTransitive_cycle 4)
    (isVertexTransitive_complete 2)

example : ((kneser 4 2)ᶜ).IsVertexTransitive :=
  isVertexTransitive_compl _ (isVertexTransitive_kneser 4 2)

end

section
variable {G H : CGraph}

theorem chromNum_eq_iff_chromaticNumber {G : CGraph} {n : ℕ} :
    G.chromNum = n ↔ G.toSimple.chromaticNumber = n := by
  rw [← Nat.cast_inj (R := ℕ∞), coe_chromNum]

/-- **A graph is 2-chromatic exactly when it is bipartite and has an edge.** -/
@[toIsoGraph]
theorem chromNum_eq_two_iff {G : CGraph} : G.chromNum = 2 ↔ G.IsBipartite ∧ 0 < G.E := by
  rw [chromNum_eq_iff_chromaticNumber, ← toSimple_ne_bot_iff, isBipartite_iff_colorable]
  exact_mod_cast SimpleGraph.chromaticNumber_eq_two_iff

@[toIsoGraph]
theorem chromNum_eq_zero_iff {G : CGraph} : G.chromNum = 0 ↔ FinEnum.card G.V = 0 := by
  rw [chromNum_eq_iff_chromaticNumber, FinEnum.card_eq_zero_iff]
  exact ⟨fun h ↦ SimpleGraph.chromaticNumber_eq_zero_iff.mp (by exact_mod_cast h),
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
    (G ⊗g H).chromNum ≤ min G.chromNum H.chromNum := by
  rw [le_min_iff, ← Nat.cast_le (α := ℕ∞), ← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum,
    coe_chromNum]
  refine ⟨chromaticNumber_le_of_hom_fst (S := G.toSimple) (P := (G ⊗g H).toSimple)
      fun p q h ↦ ?_,
    chromaticNumber_le_of_hom_snd (T := H.toSimple) (P := (G ⊗g H).toSimple)
      fun p q h ↦ ?_⟩
  · have h' : G.Adj p.1 q.1 = true ∧ H.Adj p.2 q.2 = true := by simpa using h
    exact h'.1
  · have h' : G.Adj p.1 q.1 = true ∧ H.Adj p.2 q.2 = true := by simpa using h
    exact h'.2

/-- **The chromatic numbers of a join add.** -/
theorem chromNum_join (G H : CGraph) :
    (G ∇g H).chromNum = G.chromNum + H.chromNum := by
  have hll : ∀ x y : G.V, (G ∇g H).toSimple.Adj (.inl x) (.inl y) ↔ G.toSimple.Adj x y := by
    intro x y
    rw [CGraph.toSimple_adj, CGraph.toSimple_adj, join_adj_inl_inl]
  have hrr : ∀ x y : H.V, (G ∇g H).toSimple.Adj (.inr x) (.inr y) ↔ H.toSimple.Adj x y := by
    intro x y
    rw [CGraph.toSimple_adj, CGraph.toSimple_adj, join_adj_inr_inr]
  have hlr : ∀ (x : G.V) (y : H.V), (G ∇g H).toSimple.Adj (.inl x) (.inr y) := by
    intro x y
    rw [CGraph.toSimple_adj, join_adj_inl_inr]
  refine le_antisymm (chromNum_le_iff_colorable.2 ?_) ?_
  · exact colorable_of_join_adj (S := G.toSimple) (T := H.toSimple)
      (J := (G ∇g H).toSimple) (fun x y h ↦ (hll x y).1 h) (fun x y h ↦ (hrr x y).1 h)
      colorable_chromNum colorable_chromNum
  · refine le_chromNum_iff.2 fun m hm ↦ ?_
    have h := chromaticNumber_add_le_of_join_adj (S := G.toSimple) (T := H.toSimple)
      (J := (G ∇g H).toSimple) (fun x y h ↦ (hll x y).2 h) (fun x y h ↦ (hrr x y).2 h) hlr hm
    rw [← coe_chromNum, ← coe_chromNum, ← Nat.cast_add, Nat.cast_le] at h
    exact h

/-- **Sabidussi's theorem**: the chromatic number of a cartesian product is the larger of the two.
Both factors have to be nonempty — the product of anything with the empty graph is empty. -/
@[toIsoGraph]
theorem chromNum_cartesianProduct {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    (G □g H).chromNum = max G.chromNum H.chromNum := by
  obtain ⟨a⟩ := ‹Nonempty G.V›
  obtain ⟨b⟩ := ‹Nonempty H.V›
  have hle : ∀ p q : G.V × H.V,
      (G □g H).toSimple.Adj p q →
        (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2) := by
    intro p q h
    simpa using h
  have hge : ∀ p q : G.V × H.V,
      ((p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2)) →
        (G □g H).toSimple.Adj p q := by
    intro p q h
    rw [CGraph.toSimple_adj, cartesianProduct_adj]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [CGraph.toSimple_adj] at h2
      simp [h1, h2]
    · rw [CGraph.toSimple_adj] at h1
      simp [h1, h2]
  refine le_antisymm (chromNum_le_iff_colorable.2 ?_) (max_le ?_ ?_)
  · exact colorable_of_cartesian_adj (S := G.toSimple) (T := H.toSimple)
      (P := (G □g H).toSimple) hle
      (colorable_chromNum.mono (le_max_left _ _)) (colorable_chromNum.mono (le_max_right _ _))
  · rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum]
    exact chromaticNumber_le_of_cartesian_left (S := G.toSimple)
      (P := (G □g H).toSimple) (fun p q h ↦ hge p q (Or.inr h)) b
  · rw [← Nat.cast_le (α := ℕ∞), coe_chromNum, coe_chromNum]
    exact chromaticNumber_le_of_cartesian_right (T := H.toSimple)
      (P := (G □g H).toSimple) (fun p q h ↦ hge p q (Or.inl h)) a

/-- **The lexicographic product multiplies chromatic numbers, at worst.** -/
@[toIsoGraph]
theorem chromNum_lexProduct_le (G H : CGraph) :
    (G ·g H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2 <|
    colorable_of_lex_adj (S := G.toSimple) (T := H.toSimple) (P := (G ·g H).toSimple)
      (fun p q h ↦ by simpa using h) colorable_chromNum colorable_chromNum

/-- One colour is enough exactly when there is a vertex but no edge. -/
@[toIsoGraph]
theorem chromNum_eq_one_iff {G : CGraph} : G.chromNum = 1 ↔ G.E = 0 ∧ 0 < FinEnum.card G.V := by
  have hb : G.toSimple = ⊥ ↔ G.E = 0 := by
    rw [← not_iff_not, ← ne_eq, toSimple_ne_bot_iff]
    omega
  rw [chromNum_eq_iff_chromaticNumber, Nat.cast_one, SimpleGraph.chromaticNumber_eq_one_iff, hb,
    FinEnum.card_pos_iff]

/-- **Every colour class is an independent set**, so `|V| ≤ χ·α`. -/
@[toIsoGraph V_le_chromNum_mul_indepNum]
theorem card_le_chromNum_mul_indepNum (G : CGraph) :
    FinEnum.card G.V ≤ G.chromNum * G.indepNum := by
  classical
  obtain ⟨c⟩ := G.colorable_chromNum
  have hfib : ∀ i : Fin G.chromNum,
      (Finset.univ.filter fun v ↦ c v = i).card ≤ G.indepNum := by
    intro i
    refine SimpleGraph.IsIndepSet.card_le_indepNum ?_
    intro x hx y hy hne hadj
    rw [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    exact c.valid hadj (hx.2.trans hy.2.symm)
  have hsum : FinEnum.card G.V
      = ∑ i : Fin G.chromNum, (Finset.univ.filter fun v ↦ c v = i).card := by
    rw [← FinEnum.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun v _ ↦ Finset.mem_univ (c v)
  calc FinEnum.card G.V = ∑ i : Fin G.chromNum, (Finset.univ.filter fun v ↦ c v = i).card := hsum
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
          simp only [ha, hb, dite_eq_left, dite_eq_right, not_false_iff, Subtype.mk.injEq] at hcc
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

/-- **A bipartite graph is triangle-free**, hence has clique number at most two. -/
@[toIsoGraph]
theorem cliqueNum_le_two_of_isBipartite {G : CGraph} (hb : G.IsBipartite) : G.cliqueNum ≤ 2 := by
  classical
  by_contra hcon
  obtain ⟨s, hs⟩ := G.toSimple.exists_isNClique_cliqueNum
  obtain ⟨t, hts, htc⟩ :=
    Finset.exists_subset_card_eq (n := 3)
      (show 3 ≤ s.card by rw [hs.card_eq]; exact Nat.not_le.1 hcon)
  have hcl : G.toSimple.IsNClique 3 t := ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
  obtain ⟨x, y, z, -, -, -, rfl⟩ := Finset.card_eq_three.1 htc
  rw [SimpleGraph.is3Clique_triple_iff] at hcl
  exact not_isBipartite_of_triangle ((toSimple_adj _ _ _).1 hcl.1)
    ((toSimple_adj _ _ _).1 hcl.2.1) ((toSimple_adj _ _ _).1 hcl.2.2) hb

/-- Contrapositive of Mantel: a graph with more than `|V|²/4` edges has a triangle. -/
theorem three_le_cliqueNum_of_card_sq_lt (G : CGraph)
    (h : (FinEnum.card G.V) ^ 2 < 4 * G.E) : 3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_card_sq (by omega)) (by omega)

/-! ### Counting cliques

`cliqueCount n` counts the `n`-element cliques.  The first three values are forced — there is
one empty clique, `|V|` singletons and one clique per edge — and after that the count is tied to
the clique number: it vanishes exactly when `n` exceeds `ω(G)`. -/

@[simp, toIsoGraph] theorem cliqueCount_zero (G : CGraph) : G.cliqueCount 0 = 1 := by
  have h : G.toSimple.cliqueSet 0 = {∅} := by
    ext s
    simp
  rw [cliqueCount, h, Set.ncard_singleton]

@[simp, toIsoGraph] theorem cliqueCount_one (G : CGraph) : G.cliqueCount 1 = FinEnum.card G.V := by
  have h : G.toSimple.cliqueSet 1 = (fun a : G.V ↦ ({a} : Finset G.V)) '' Set.univ := by
    ext s
    simp [eq_comm]
  rw [cliqueCount, h, Set.ncard_image_of_injective _ Finset.singleton_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard']

/-- The `2`-cliques are exactly the edges. -/
@[simp] theorem cliqueCount_two (G : CGraph) : G.cliqueCount 2 = G.E := by
  have h : G.toSimple.cliqueSet 2 = Sym2.toFinset '' G.toSimple.edgeSet := by
    ext s
    simp only [SimpleGraph.mem_cliqueSet_iff, Set.mem_image]
    constructor
    · rintro ⟨hcl, hcard⟩
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
      refine ⟨s(a, b), ?_, by rw [Sym2.toFinset_mk_eq]⟩
      exact hcl (by simp) (by simp) hab
    · rintro ⟨e, he, rfl⟩
      induction e with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rw [Sym2.toFinset_mk_eq]
        refine ⟨?_, Finset.card_pair he.ne⟩
        simpa using SimpleGraph.isClique_pair.2 (fun _ ↦ he)
  have hinj : Set.InjOn Sym2.toFinset G.toSimple.edgeSet := by
    intro e₁ he₁ e₂ he₂ heq
    induction e₁ with
    | _ a b =>
      induction e₂ with
      | _ c d =>
        rw [SimpleGraph.mem_edgeSet] at he₁
        have ha : a ∈ Sym2.toFinset s(c, d) := by rw [← heq, Sym2.toFinset_mk_eq]; simp
        have hb : b ∈ Sym2.toFinset s(c, d) := by rw [← heq, Sym2.toFinset_mk_eq]; simp
        exact Sym2.eq_of_ne_mem he₁.ne (by simp) (by simp)
          (Sym2.mem_toFinset.1 ha) (Sym2.mem_toFinset.1 hb)
  rw [cliqueCount, h, hinj.ncard_image, E, SimpleGraph.edgeFinset,
    ← Set.ncard_eq_toFinset_card']

@[toIsoGraph]
theorem cliqueCount_eq_zero_iff (G : CGraph) (n : ℕ) : G.cliqueCount n = 0 ↔ G.cliqueNum < n := by
  rw [cliqueCount, Set.ncard_eq_zero (Set.toFinite _), SimpleGraph.cliqueSet_eq_empty_iff,
    cliqueFree_iff_cliqueNum_lt]
  rfl

@[toIsoGraph]
theorem cliqueCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.cliqueCount n ↔ n ≤ G.cliqueNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, cliqueCount_eq_zero_iff]
  omega

theorem cliqueCount_eq_zero_of_cliqueNum_lt {G : CGraph} {n : ℕ} (h : G.cliqueNum < n) :
    G.cliqueCount n = 0 :=
  (cliqueCount_eq_zero_iff G n).2 h

@[toIsoGraph]
theorem cliqueCount_le_choose (G : CGraph) (n : ℕ) :
    G.cliqueCount n ≤ (FinEnum.card G.V).choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset G n, FinEnum.card_eq_fintypeCard']
  exact SimpleGraph.card_cliqueFinset_le

theorem cliqueCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : FinEnum.card G.V < n) :
    G.cliqueCount n = 0 :=
  Nat.le_zero.1 ((cliqueCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- A graph has a triangle exactly when its girth is three, so the triangle count vanishes
exactly when the girth is anything else. -/
@[toIsoGraph]
theorem cliqueCount_three_eq_zero_iff (G : CGraph) : G.cliqueCount 3 = 0 ↔ G.girth ≠ 3 := by
  rw [cliqueCount_eq_zero_iff, ne_eq, girth_eq_three_iff]
  omega

theorem cliqueCount_two_eq_zero_iff (G : CGraph) : G.cliqueCount 2 = 0 ↔ G.E = 0 := by
  classical
  rw [cliqueCount_two]

/-- A graph needs `n` colours before it can have an `n`-clique. -/
theorem cliqueCount_eq_zero_of_chromNum_lt {G : CGraph} {n : ℕ} (h : G.chromNum < n) :
    G.cliqueCount n = 0 :=
  cliqueCount_eq_zero_of_cliqueNum_lt (lt_of_le_of_lt (cliqueNum_le_chromNum G) h)

/-- Bipartite graphs are triangle-free. -/
@[toIsoGraph]
theorem cliqueCount_three_eq_zero_of_isBipartite {G : CGraph} (h : G.IsBipartite) :
    G.cliqueCount 3 = 0 :=
  cliqueCount_eq_zero_of_chromNum_lt
    (lt_of_le_of_lt (isBipartite_iff_chromNum_le_two.1 h) (by omega))

/-- Every subset of the complete graph is a clique, so the count is a binomial coefficient. -/
@[simp, toIsoGraph]
theorem cliqueCount_complete (m n : ℕ) :
    (complete m).cliqueCount n = m.choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  have h : (complete m).toSimple.cliqueFinset n = Finset.univ.powersetCard n := by
    ext s
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, Finset.mem_powersetCard,
      complete_toSimple]
    simp [SimpleGraph.IsClique, Set.Pairwise]
  rw [h, Finset.card_powersetCard, FinEnum.card_univ, card_complete]

@[simp, toIsoGraph] theorem cliqueCount_empty (m n : ℕ) : (empty m).cliqueCount (n + 2) = 0 := by
  refine cliqueCount_eq_zero_of_cliqueNum_lt ?_
  rw [cliqueNum_empty]
  omega

/-! ### Counting independent sets

Independent sets are cliques of the complement, so the whole clique-count API transfers through
`cliqueCount_compl`: each fact below is its clique-count counterpart read through `compl`. -/

@[simp, toIsoGraph] theorem indepCount_zero (G : CGraph) : G.indepCount 0 = 1 := by
  classical
  rw [← cliqueCount_compl]
  exact cliqueCount_zero _

@[simp, toIsoGraph] theorem indepCount_one (G : CGraph) : G.indepCount 1 = FinEnum.card G.V := by
  classical
  rw [← cliqueCount_compl, cliqueCount_one, card_compl]

@[toIsoGraph]
theorem indepCount_eq_zero_iff (G : CGraph) (n : ℕ) :
    G.indepCount n = 0 ↔ G.indepNum < n := by
  classical
  rw [← cliqueCount_compl, cliqueCount_eq_zero_iff, cliqueNum_compl]

@[toIsoGraph]
theorem indepCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.indepCount n ↔ n ≤ G.indepNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, indepCount_eq_zero_iff]
  omega

theorem indepCount_eq_zero_of_indepNum_lt {G : CGraph} {n : ℕ} (h : G.indepNum < n) :
    G.indepCount n = 0 :=
  (indepCount_eq_zero_iff G n).2 h

@[toIsoGraph]
theorem indepCount_le_choose (G : CGraph) (n : ℕ) :
    G.indepCount n ≤ (FinEnum.card G.V).choose n := by
  classical
  rw [← cliqueCount_compl]
  have h := cliqueCount_le_choose Gᶜ n
  rwa [card_compl] at h

theorem indepCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : FinEnum.card G.V < n) :
    G.indepCount n = 0 :=
  Nat.le_zero.1 ((indepCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- The independent pairs are exactly the non-edges. -/
@[toIsoGraph]
theorem indepCount_two_add_E (G : CGraph) :
    G.indepCount 2 + G.E = (FinEnum.card G.V).choose 2 := by
  rw [← cliqueCount_compl, cliqueCount_two]
  exact E_compl G

/-- Every set of vertices of the empty graph is independent. -/
@[simp, toIsoGraph] theorem indepCount_empty (m n : ℕ) : (empty m).indepCount n = m.choose n := by
  rw [← cliqueCount_compl]
  exact cliqueCount_complete m n

@[simp, toIsoGraph]
theorem indepCount_complete (m n : ℕ) :
    (complete m).indepCount (n + 2) = 0 := by
  rw [← cliqueCount_compl, show (complete m)ᶜ = empty m from compl_compl (empty m)]
  exact cliqueCount_empty m n

/-- Cliques never cross between the two sides, so from size one on the counts simply add. -/
@[toIsoGraph simp]
theorem cliqueCount_disjUnion (G H : CGraph) (n : ℕ) :
    (G ⊕g H).cliqueCount (n + 1) = G.cliqueCount (n + 1) + H.cliqueCount (n + 1) := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset, cliqueCount_eq_card_cliqueFinset,
    cliqueCount_eq_card_cliqueFinset]
  set fl : Finset G.V ↪ Finset (G ⊕g H).V :=
    ⟨Finset.map ⟨Sum.inl, Sum.inl_injective⟩, Finset.map_injective _⟩ with hfl
  set fr : Finset H.V ↪ Finset (G ⊕g H).V :=
    ⟨Finset.map ⟨Sum.inr, Sum.inr_injective⟩, Finset.map_injective _⟩ with hfr
  have hset : (G ⊕g H).toSimple.cliqueFinset (n + 1)
      = (G.toSimple.cliqueFinset (n + 1)).map fl
        ∪ (H.toSimple.cliqueFinset (n + 1)).map fr := by
    ext s
    simp only [Finset.mem_union, Finset.mem_map, SimpleGraph.mem_cliqueFinset_iff, hfl, hfr,
      Function.Embedding.coeFn_mk]
    rw [isNClique_disjUnion_iff]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact Or.inl ⟨t, ht, rfl⟩
      · exact Or.inr ⟨t, ht, rfl⟩
  have hdisj : Disjoint ((G.toSimple.cliqueFinset (n + 1)).map fl)
      ((H.toSimple.cliqueFinset (n + 1)).map fr) := by
    rw [Finset.disjoint_left]
    rintro s hs hs'
    simp only [Finset.mem_map, SimpleGraph.mem_cliqueFinset_iff, hfl, hfr,
      Function.Embedding.coeFn_mk] at hs hs'
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨u, -, hu⟩ := hs'
    obtain ⟨a, ha⟩ : t.Nonempty := Finset.card_pos.1 (by rw [ht.card_eq]; omega)
    have : (Sum.inl a : (G ⊕g H).V) ∈ u.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      rw [hu]; simpa using ha
    simp at this
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

/-- Dually, independent sets never cross a join. -/
theorem indepCount_join (G H : CGraph) (n : ℕ) :
    (G ∇g H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  classical
  rw [join_eq_compl_disjUnion, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl,
    cliqueCount_compl]

/-! ### Counting cliques across a join

Across a join every vertex of the one side sees every vertex of the other, so a set of vertices
is a clique exactly when both of its halves are.  Splitting an `n`-clique by how many vertices it
takes from the left turns the count into a convolution: the clique-counting sequences of the two
factors multiply as generating functions. -/

/-- A set of vertices of a join is a clique exactly when both of its halves are: the crossing
pairs are adjacent for free. -/
theorem isClique_join_iff {G H : CGraph} {s : Finset (G ∇g H).V} :
    (G ∇g H).toSimple.IsClique ↑s ↔
      G.toSimple.IsClique ↑s.toLeft ∧ H.toSimple.IsClique ↑s.toRight := by
  constructor
  · intro h
    refine ⟨fun a ha b hb hab ↦ ?_, fun a ha b hb hab ↦ ?_⟩
    · have := h (Finset.mem_coe.2 (Finset.mem_toLeft.1 (Finset.mem_coe.1 ha)))
        (Finset.mem_coe.2 (Finset.mem_toLeft.1 (Finset.mem_coe.1 hb)))
        (fun he ↦ hab (Sum.inl_injective he))
      simpa using this
    · have := h (Finset.mem_coe.2 (Finset.mem_toRight.1 (Finset.mem_coe.1 ha)))
        (Finset.mem_coe.2 (Finset.mem_toRight.1 (Finset.mem_coe.1 hb)))
        (fun he ↦ hab (Sum.inr_injective he))
      simpa using this
  · rintro ⟨h1, h2⟩ x hx y hy hxy
    match x, y with
    | .inl a, .inl b =>
      have := h1 (Finset.mem_coe.2 (Finset.mem_toLeft.2 (Finset.mem_coe.1 hx)))
        (Finset.mem_coe.2 (Finset.mem_toLeft.2 (Finset.mem_coe.1 hy)))
        (fun he ↦ hxy (congrArg Sum.inl he))
      simpa using this
    | .inl a, .inr d => simp
    | .inr b, .inl c => simp
    | .inr b, .inr d =>
      have := h2 (Finset.mem_coe.2 (Finset.mem_toRight.2 (Finset.mem_coe.1 hx)))
        (Finset.mem_coe.2 (Finset.mem_toRight.2 (Finset.mem_coe.1 hy)))
        (fun he ↦ hxy (congrArg Sum.inr he))
      simpa using this

/-- **The cliques of a join convolve**: an `n`-clique of `G ∇ H` is an `i`-clique of `G` beside an
`(n - i)`-clique of `H`, and every such pair occurs once. -/
@[toIsoGraph]
theorem cliqueCount_join (G H : CGraph) (n : ℕ) :
    (G ∇g H).cliqueCount n
      = ∑ i ∈ Finset.range (n + 1), G.cliqueCount i * H.cliqueCount (n - i) := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  have hmem : ∀ s ∈ (G ∇g H).toSimple.cliqueFinset n, s.toLeft.card ∈ Finset.range (n + 1) := by
    intro s hs
    rw [SimpleGraph.mem_cliqueFinset_iff] at hs
    have hsum : s.toLeft.card + s.toRight.card = s.card := Finset.card_toLeft_add_card_toRight
    rw [hs.card_eq] at hsum
    exact Finset.mem_range.2 (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : i ≤ n := by have := Finset.mem_range.1 hi; omega
  rw [cliqueCount_eq_card_cliqueFinset, cliqueCount_eq_card_cliqueFinset, ← Finset.card_product]
  refine Finset.card_bij (fun s _ ↦ (s.toLeft, s.toRight)) ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hs
    obtain ⟨⟨hcl, hcard⟩, hi'⟩ := hs
    rw [isClique_join_iff] at hcl
    have hsum : s.toLeft.card + s.toRight.card = n := by
      rw [Finset.card_toLeft_add_card_toRight, hcard]
    have hleft : s.toLeft ∈ G.toSimple.cliqueFinset i :=
      SimpleGraph.mem_cliqueFinset_iff.2 ⟨hcl.1, hi'⟩
    have hright : s.toRight ∈ H.toSimple.cliqueFinset (n - i) :=
      SimpleGraph.mem_cliqueFinset_iff.2 ⟨hcl.2, by omega⟩
    exact Finset.mem_product.2 ⟨hleft, hright⟩
  · intro s hs t ht hst
    rw [Prod.mk.injEq] at hst
    rw [← Finset.toLeft_disjSum_toRight (u := s), ← Finset.toLeft_disjSum_toRight (u := t),
      hst.1, hst.2]
  · rintro ⟨t, u⟩ htu
    rw [Finset.mem_product, SimpleGraph.mem_cliqueFinset_iff,
      SimpleGraph.mem_cliqueFinset_iff] at htu
    refine ⟨t.disjSum u, ?_, by simp⟩
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨⟨?_, ?_⟩, by simp [htu.1.card_eq]⟩
    · rw [isClique_join_iff]
      simpa using ⟨htu.1.isClique, htu.2.isClique⟩
    · rw [Finset.card_disjSum, htu.1.card_eq, htu.2.card_eq]
      omega

/-- The complementary statement: independent sets of a disjoint union convolve. -/
@[toIsoGraph]
theorem indepCount_disjUnion (G H : CGraph) (n : ℕ) :
    (G ⊕g H).indepCount n
      = ∑ i ∈ Finset.range (n + 1), G.indepCount i * H.indepCount (n - i) := by
  rw [← cliqueCount_compl, compl_disjUnion, cliqueCount_join]
  simp only [cliqueCount_compl]

/-- Triangles of a join: one from each side, plus an edge on one side against a vertex of the
other. -/
@[toIsoGraph]
theorem cliqueCount_join_three (G H : CGraph) :
    (G ∇g H).cliqueCount 3
      = G.cliqueCount 3 + H.cliqueCount 3
        + G.E * FinEnum.card H.V + FinEnum.card G.V * H.E := by
  rw [cliqueCount_join]
  simp [Finset.sum_range_succ]
  ring

/-- Independent triples of a disjoint union, the same way round. -/
@[toIsoGraph]
theorem indepCount_disjUnion_three (G H : CGraph) :
    (G ⊕g H).indepCount 3
      = G.indepCount 3 + H.indepCount 3
        + G.indepCount 2 * FinEnum.card H.V + FinEnum.card G.V * H.indepCount 2 := by
  rw [indepCount_disjUnion]
  simp [Finset.sum_range_succ]
  ring

/-! ### Colouring the strong product -/

/-- **The strong product multiplies chromatic numbers, at worst**: it sits inside the
lexicographic product, which is already known to satisfy `χ ≤ χ(G)·χ(H)`, and colourings pull
back along subgraph inclusions. -/
@[toIsoGraph]
theorem chromNum_strongProduct_le (G H : CGraph) :
    (G ⊠g H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2
    ((chromNum_le_iff_colorable.1 (chromNum_lexProduct_le G H)).mono_left
      (strongProduct_le_lexProduct G H))

/-- Both factors appear as fibres of the cartesian product, which the strong product contains,
so `max χ(G) χ(H) ≤ χ(G ⊠ H)`. -/
@[toIsoGraph]
theorem max_chromNum_le_chromNum_strongProduct {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    max G.chromNum H.chromNum ≤ (G ⊠g H).chromNum := by
  rw [← chromNum_cartesianProduct (G := G) (H := H)]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_strongProduct G H))

/-- The same sandwich for the lexicographic product. -/
@[toIsoGraph]
theorem max_chromNum_le_chromNum_lexProduct {G H : CGraph} [Nonempty G.V] [Nonempty H.V] :
    max G.chromNum H.chromNum ≤ (G ·g H).chromNum := by
  rw [← chromNum_cartesianProduct (G := G) (H := H)]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_lexProduct G H))

/-- Cliques multiply in the strong product, so `ω(G)·ω(H) ≤ χ(G ⊠ H)`: the lower bound coming
from cliques is itself multiplicative. -/
@[toIsoGraph]
theorem cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (G H : CGraph)
 :
    G.cliqueNum * H.cliqueNum ≤ (G ⊠g H).chromNum := by
  have h := (G ⊠g H).cliqueNum_le_chromNum
  rwa [cliqueNum_strongProduct] at h

/-- **The strong product multiplies clique cover numbers, at worst**: `θ(G ⊠ H) ≤ θ(G)·θ(H)`.
A clique of `G ⊠ H` is a clique of `G` times a clique of `H`, so the pairwise products of a clique
cover of each factor cover the product.  Dually — and this is the proof — the complement of a
strong product is the co-normal product of the two complements, which `colorable_of_conormal_adj`
colours coordinatewise.

Together with `indepNum_mul_indepNum_le_indepNum_strongProduct` this brackets the strong product
between `α(G)·α(H)` and `θ(G)·θ(H)`; the failure of the lower bound to be an equality is what
makes the Shannon capacity of a graph interesting. -/
@[toIsoGraph]
theorem cliqueCoverNum_strongProduct_le (G H : CGraph) :
    (G ⊠g H).cliqueCoverNum ≤ G.cliqueCoverNum * H.cliqueCoverNum := by
  show ((G ⊠g H)ᶜ).chromNum ≤ _
  refine chromNum_le_iff_colorable.2 (colorable_of_conormal_adj (S := (Gᶜ).toSimple)
    (T := (Hᶜ).toSimple) ?_ colorable_chromNum colorable_chromNum)
  intro p q h
  simp only [CGraph.toSimple_adj, compl_adj, strongProduct_adj, Bool.and_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not, ne_eq] at h ⊢
  tauto

/-- The tensor product of two graphs with an edge has an edge, hence needs two colours.  Together
with `chromNum_tensorProduct_le` this pins `χ(G × H) = 2` as soon as one factor is bipartite and
both have an edge.  In general the lower bound is the hard direction: Hedetniemi's conjecture that
`χ(G × H) = min χ(G) χ(H)` is false. -/
@[toIsoGraph]
theorem two_le_chromNum_tensorProduct {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) : 2 ≤ (G ⊗g H).chromNum := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  refine two_le_chromNum_of_adj (a := ((a, b) : (G ⊗g H).V)) (b := (a', b')) ?_
  rw [tensorProduct_adj]
  simp [ha, hb]

/-- One bipartite factor is enough: if `G` is bipartite and both factors have an edge then
`χ(G × H) = 2`. -/
@[toIsoGraph]
theorem chromNum_tensorProduct_eq_two {G H : CGraph}
    (hG : G.IsBipartite) (hGE : 0 < G.E) (hHE : 0 < H.E) :
    (G ⊗g H).chromNum = 2 :=
  le_antisymm
    (le_trans (chromNum_tensorProduct_le G H)
      (le_trans (min_le_left _ _) (isBipartite_iff_chromNum_le_two.1 hG)))
    (two_le_chromNum_tensorProduct hGE hHE)

/-- `ν + α ≤ n`: the edges of a matching are disjoint, and each one contributes a vertex
outside a maximum independent set. -/
theorem indepNum_lineGraph_add_indepNum_le_card (G : CGraph) :
    (lineGraph G).indepNum + G.indepNum ≤ FinEnum.card G.V := by
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
  have h3 : (Finset.univ \ I).card = FinEnum.card G.V - I.card := by
    rw [Finset.card_sdiff, FinEnum.card_univ, Finset.inter_univ]
  have h4 := Finset.card_le_card h2
  have h5 : I.card ≤ FinEnum.card G.V := by
    rw [FinEnum.card_eq_fintypeCard']; exact Finset.card_le_univ I
  have hdefM : (lineGraph G).indepNum = (lineGraph G).toSimple.indepNum := rfl
  have hdefI : G.indepNum = G.toSimple.indepNum := rfl
  omega

/-- **The chromatic index of a cartesian product is at most the sum of the two factors'**, with
no explicit colouring in sight: read one back out of each factor's line-graph colouring. -/
theorem chromNum_lineGraph_cartesianProduct_le_add {G H : CGraph}
 (hG : 0 < (lineGraph G).chromNum) (hH : 0 < (lineGraph H).chromNum) :
    (lineGraph (G □g H)).chromNum
      ≤ (lineGraph G).chromNum + (lineGraph H).chromNum := by
  obtain ⟨c, hc, hcp⟩ := exists_edgeColouring (G := G) le_rfl ⟨0, hG⟩
  obtain ⟨d, hd, hdp⟩ := exists_edgeColouring (G := H) le_rfl ⟨0, hH⟩
  exact chromNum_lineGraph_cartesianProduct_le c d hc hd hcp hdp

end

end CGraph

namespace IsoGraph

/-! ### Bipartite double covers

The tensor product with `K₂` is the bipartite double cover.  Over a bipartite graph it comes apart
into two copies of the original — one application of the colouring built in the previous section —
and over an odd cycle it does not, giving the cycle of twice the length instead. -/

/-- **A double cover splits whenever the graph is 2-coloured**, for a graph presented as a
`CGraph` together with a colouring.  `tensorProduct_complete_two_of_isBipartite` is the same
statement with the colouring existentially quantified. -/
theorem tensorProduct_complete_two_of_colouring (G : CGraph) (c : G.V → Bool)
    (h : ∀ x y, G.Adj x y = true → c x ≠ c y) :
    complete 2 ⊗g ⟦G⟧ = ⟦G⟧ ⊕g ⟦G⟧ := by
  rw [← empty_two_cartesianProduct ⟦G⟧, complete_def, tensorProduct_mk, empty_def,
    cartesianProduct_mk]
  exact Quotient.sound ⟨CGraph.Iso.tensorTwoOfColouring G c h⟩

/-! ### The chromatic number of a join and of the products -/

/-- **The chromatic numbers of a join add.** -/
@[simp] theorem chromNum_join (G H : IsoGraph) :
    (G ∇g H).chromNum = G.chromNum + H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, chromNum_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_join _ _

/-! ### The Mycielskian and the Kneser bound -/

/-- **Mycielski's construction raises the chromatic number by exactly one.** -/
@[simp] theorem chromNum_mycielskian (G : IsoGraph) :
    (mycielskian G).chromNum = G.chromNum + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_mycielskian _

/-- A graph with more than `|V|²/4` edges contains a triangle, so its girth is `3`. -/
theorem three_le_cliqueNum_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) :
    3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_V_sq (by omega)) (by omega)

/-- The general contrapositive of Turán: beating the Turán density forces a bigger clique. -/
theorem lt_cliqueNum_of_lt (G : IsoGraph) {r : ℕ} (hr : 0 < r)
    (h : (r - 1) * G.V ^ 2 < 2 * r * G.E) : r < G.cliqueNum := by
  by_contra hcon
  exact absurd (G.two_mul_mul_E_le hr (Nat.not_lt.1 hcon)) (by omega)

/-! ### The Ramsey number `R(3, 3)` -/

/-- The same for a graph of girth other than three, in particular any bipartite graph. -/
theorem three_le_indepNum_of_girth_ne_three (G : IsoGraph) (h : 6 ≤ G.V) (hg : G.girth ≠ 3) :
    3 ≤ G.indepNum := by
  refine G.three_le_indepNum_of_cliqueNum_le_two h ?_
  by_contra hcon
  exact hg (girth_eq_three_iff.2 (by omega))

theorem three_le_indepNum_of_isBipartite (G : IsoGraph) (h : 6 ≤ G.V) (hb : IsBipartite G) :
    3 ≤ G.indepNum :=
  G.three_le_indepNum_of_cliqueNum_le_two h (cliqueNum_le_two_of_isBipartite hb)

/-! ### `R(3, 3) = 6`: five vertices are not enough -/

/-- The five-cycle has neither a triangle nor three pairwise non-adjacent vertices, so the bound
`R(3, 3) ≤ 6` cannot be improved. -/
theorem cliqueNum_cycle_five : (cycle 5).cliqueNum = 2 := by
  have hle : (cycle 5).cliqueNum ≤ 2 := by
    by_contra hcon
    have := girth_eq_three_iff.2 (show 3 ≤ (cycle 5).cliqueNum by omega)
    rw [girth_cycle_five] at this
    omega
  have hge : 2 ≤ (cycle 5).cliqueNum := two_le_cliqueNum_of_E_pos (by simp)
  omega

/-! ### Where the cover number sits among the other invariants -/

/-- Turned around, this is a lower bound on the cover number, and via Gallai an upper bound on
the independence number. -/
theorem indepNum_mul_maxDeg_le (G : IsoGraph) :
    G.E + G.indepNum * G.maxDeg ≤ G.V * G.maxDeg := by
  have h1 := G.E_le_coverNum_mul_maxDeg
  have h2 := G.coverNum_add_indepNum
  calc G.E + G.indepNum * G.maxDeg ≤ G.coverNum * G.maxDeg + G.indepNum * G.maxDeg :=
        Nat.add_le_add_right h1 _
    _ = (G.coverNum + G.indepNum) * G.maxDeg := by ring
    _ = G.V * G.maxDeg := by rw [h2]

/-- A vertex-transitive graph with an edge has an independent set of at most half its vertices. -/
theorem two_mul_indepNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) (hE : 0 < G.E) :
    2 * G.indepNum ≤ G.V := by
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hE
  calc 2 * G.indepNum = G.indepNum * 2 := by ring
    _ ≤ G.indepNum * G.cliqueNum := Nat.mul_le_mul_left _ h1
    _ ≤ G.V := indepNum_mul_cliqueNum_le_V h

/-- Dually, a vertex-transitive graph that is not complete has a clique of at most half its
vertices (`2 ≤ α` says exactly that some pair of vertices is non-adjacent). -/
theorem two_mul_cliqueNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) (hα : 2 ≤ G.indepNum) :
    2 * G.cliqueNum ≤ G.V :=
  le_trans (Nat.mul_le_mul_right _ hα) (indepNum_mul_cliqueNum_le_V h)

/-- The clique–coclique bound and the greedy bound `|V| ≤ χ · α` sandwich `|V|` between two
products with the same first factor, so a vertex-transitive graph has `ω ≤ χ` with room to spare
whenever the bound is not tight. -/
theorem indepNum_mul_cliqueNum_le_chromNum_mul_indepNum {G : IsoGraph} (h : IsVertexTransitive G) :
    G.indepNum * G.cliqueNum ≤ G.chromNum * G.indepNum :=
  le_trans (indepNum_mul_cliqueNum_le_V h) (V_le_chromNum_mul_indepNum G)

/-- In a vertex-transitive graph the independence number and the vertex cover number are related
by `ω · (|V| - τ) ≤ |V|`. -/
theorem cliqueNum_mul_V_sub_coverNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) :
    G.cliqueNum * (G.V - G.coverNum) ≤ G.V := by
  rw [← indepNum_eq_V_sub_coverNum, Nat.mul_comm]
  exact indepNum_mul_cliqueNum_le_V h

/-- Cycles: the clique–coclique bound recovers `α(C_n) ≤ ⌊n/2⌋`. -/
theorem two_mul_indepNum_cycle_le (n : ℕ) : 2 * (cycle (n + 3)).indepNum ≤ n + 3 := by
  have hE : 0 < (cycle (n + 3)).E := by simp
  have := two_mul_indepNum_le_V (isVertexTransitive_cycle (n + 3)) hE
  rwa [V_cycle] at this

/-- `γ(Cₙ) ≥ n/3`. -/
theorem le_domNum_cycle (n : ℕ) : n + 3 ≤ (cycle (n + 3)).domNum * 3 := by
  have h := le_domNum_of_regular (G := cycle (n + 3)) (k := 2) (maxDeg_cycle n)
  rwa [V_cycle] at h

/-! ### Counting cliques -/

@[simp] theorem cliqueCount_two (G : IsoGraph) : G.cliqueCount 2 = G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, E_mk]
  classical
  exact CGraph.cliqueCount_two _

/-! ### Counting independent sets -/

@[simp] theorem cliqueCount_compl (G : IsoGraph) (n : ℕ) :
    Gᶜ.cliqueCount n = G.indepCount n := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, cliqueCount_mk, indepCount_mk]
  exact CGraph.cliqueCount_compl _ n

@[simp] theorem indepCount_compl (G : IsoGraph) (n : ℕ) :
    Gᶜ.indepCount n = G.cliqueCount n := by
  rw [← cliqueCount_compl Gᶜ, compl_compl]

/-! ### Counting cliques in a disjoint union -/

@[simp] theorem indepCount_join (G H : IsoGraph) (n : ℕ) :
    (G ∇g H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  rw [join_def, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl, cliqueCount_compl]

/-! ### When a product runs out of cliques

For the three products and for the line graph the clique number is known exactly, so
`cliqueCount_eq_zero_iff` says precisely how far up the counts stay positive. -/

theorem cliqueCount_strongProduct_eq_zero_iff (G H : IsoGraph) (n : ℕ) :
    (G ⊠g H).cliqueCount n = 0 ↔ G.cliqueNum * H.cliqueNum < n := by
  rw [cliqueCount_eq_zero_iff, cliqueNum_strongProduct]

theorem cliqueCount_lexProduct_eq_zero_iff (G H : IsoGraph) (n : ℕ) :
    (G ·g H).cliqueCount n = 0 ↔ G.cliqueNum * H.cliqueNum < n := by
  rw [cliqueCount_eq_zero_iff, cliqueNum_lexProduct]

/-- A clique of the tensor product is the graph of a bijection between a clique of `G` and one of
`H`, so it dies as soon as either factor does. -/
theorem cliqueCount_tensorProduct_eq_zero_iff (G H : IsoGraph) (n : ℕ) :
    (G ⊗g H).cliqueCount n = 0 ↔ min G.cliqueNum H.cliqueNum < n := by
  rw [cliqueCount_eq_zero_iff, cliqueNum_tensorProduct]

/-- Cliques of a line graph are stars, once there is a vertex of degree three to carry them. -/
theorem cliqueCount_lineGraph_eq_zero_iff {G : IsoGraph} (h : 3 ≤ maxDeg G) (n : ℕ) :
    (lineGraph G).cliqueCount n = 0 ↔ maxDeg G < n := by
  rw [cliqueCount_eq_zero_iff, cliqueNum_lineGraph_of_three_le_maxDeg h]

/-- Independent sets of a line graph are matchings. -/
theorem indepCount_lineGraph_eq_zero_iff (G : IsoGraph) (n : ℕ) :
    (lineGraph G).indepCount n = 0 ↔ G.matchNum < n := by
  rw [indepCount_eq_zero_iff, indepNum_lineGraph]

/-- The complement of a lexicographic product is the lexicographic product of the complements, so
the independent sets run out at `α(G)·α(H)`. -/
theorem indepCount_lexProduct_eq_zero_iff (G H : IsoGraph) (n : ℕ) :
    (G ·g H).indepCount n = 0 ↔ G.indepNum * H.indepNum < n := by
  rw [← cliqueCount_compl, compl_lexProduct, cliqueCount_lexProduct_eq_zero_iff,
    cliqueNum_compl, cliqueNum_compl]

/-! ### The clique number of the Mycielskian -/

/-- **Mycielski's theorem**: there are triangle-free graphs of arbitrarily large chromatic
number.  Iterating the Mycielskian from `K₁` keeps the clique number at most two while raising
the chromatic number by one each time. -/
theorem exists_cliqueNum_le_two_and_le_chromNum (k : ℕ) :
    ∃ G : IsoGraph, 0 < G.V ∧ G.cliqueNum ≤ 2 ∧ k ≤ G.chromNum := by
  induction k with
  | zero => exact ⟨complete 1, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨G, hV, hw, hc⟩ := ih
    refine ⟨mycielskian G, ?_, ?_, ?_⟩
    · rw [V_mycielskian]
      omega
    · rw [cliqueNum_mycielskian G hV]
      omega
    · rw [chromNum_mycielskian]
      omega

/-- The same statement with triangles counted rather than measured by the clique number. -/
theorem exists_cliqueCount_three_eq_zero_and_le_chromNum (k : ℕ) :
    ∃ G : IsoGraph, G.cliqueCount 3 = 0 ∧ k ≤ G.chromNum := by
  obtain ⟨G, -, hw, hc⟩ := exists_cliqueNum_le_two_and_le_chromNum k
  exact ⟨G, (cliqueCount_eq_zero_iff G 3).2 (by omega), hc⟩

/-- The mirror bound `τ(G) · |V(H)| ≤ τ(G □ H)`. -/
theorem coverNum_mul_V_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (G □g H).coverNum := by
  rw [cartesianProduct_comm]
  have h := V_mul_coverNum_le_coverNum_cartesianProduct H G
  rwa [mul_comm] at h

/-- The mirror bound for the strong product. -/
theorem coverNum_mul_V_le_coverNum_strongProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (G ⊠g H).coverNum := by
  rw [strongProduct_comm]
  have h := V_mul_coverNum_le_coverNum_strongProduct H G
  rwa [mul_comm] at h

/-- A slab `S × V(H)` is independent in the tensor product, so covering it is cheap:
`τ(G × H) ≤ τ(G)·|V(H)|`. -/
theorem coverNum_tensorProduct_le (G H : IsoGraph) :
    (G ⊗g H).coverNum ≤ G.coverNum * H.V := by
  have h1 : G.coverNum * H.V = G.V * H.V - G.indepNum * H.V := by
    rw [coverNum_eq, Nat.sub_mul]
  have h2 := indepNum_mul_V_le_indepNum_tensorProduct G H
  have h3 := (G ⊗g H).coverNum_add_indepNum
  rw [V_tensorProduct] at h3
  omega

/-- The mirror bound `τ(G × H) ≤ |V(G)|·τ(H)`. -/
theorem coverNum_tensorProduct_le' (G H : IsoGraph) :
    (G ⊗g H).coverNum ≤ G.V * H.coverNum := by
  rw [tensorProduct_comm]
  have h := coverNum_tensorProduct_le H G
  rwa [mul_comm] at h

@[simp] theorem edgeChromNum_empty (n : ℕ) : (empty n).edgeChromNum = 0 := by
  rw [edgeChromNum_eq, lineGraph_empty, chromNum_empty_zero]

theorem matchNum_pos (G : IsoGraph) (h : 0 < G.E) : 0 < G.matchNum := by
  rw [matchNum_eq]
  exact one_le_indepNum (by rwa [V_lineGraph])

@[simp] theorem matchNum_eq_zero_iff (G : IsoGraph) : G.matchNum = 0 ↔ G.E = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hE
    have := G.matchNum_pos (Nat.pos_of_ne_zero hE)
    omega
  · have := G.matchNum_le_E
    omega

@[simp] theorem matchNum_empty (n : ℕ) : (empty n).matchNum = 0 := by
  rw [matchNum_eq, lineGraph_empty, indepNum_empty]

/-! ### Matchings versus independent sets and covers -/

/-- Since an independent set meets each edge of a matching at most once, `ν + α ≤ n`. -/
@[toIsoGraph matchNum_add_indepNum_le_V]
theorem _root_.CGraph.matchNum_add_indepNum_le_card (G : CGraph) :
    G.matchNum + G.indepNum ≤ FinEnum.card G.V :=
  CGraph.indepNum_lineGraph_add_indepNum_le_card G

/-- `ν ≤ τ`: distinct edges of a matching need distinct vertices of a vertex cover.  Here it
falls out of `ν + α ≤ n` and Gallai's identity `τ + α = n`. -/
theorem matchNum_le_coverNum (G : IsoGraph) : G.matchNum ≤ G.coverNum := by
  have h1 := G.matchNum_add_indepNum_le_V
  have h2 := G.coverNum_add_indepNum
  omega

/-- A graph with a perfect matching has independence number at most `n / 2`. -/
theorem two_mul_indepNum_le_V_of_two_mul_matchNum_eq (G : IsoGraph)
    (h : 2 * G.matchNum = G.V) : 2 * G.indepNum ≤ G.V := by
  have h1 := G.matchNum_add_indepNum_le_V
  omega

theorem cliqueCoverNum_le_V_sub_cliqueNum_add_one (G : IsoGraph) :
    G.cliqueCoverNum ≤ G.V - G.cliqueNum + 1 := by
  have h := chromNum_le_V_sub_indepNum_add_one Gᶜ
  rw [cliqueCoverNum_eq]
  rwa [V_compl, indepNum_compl] at h

@[simp] theorem cliqueCoverNum_eq_zero_iff {G : IsoGraph} : G.cliqueCoverNum = 0 ↔ G.V = 0 := by
  rw [cliqueCoverNum_eq, chromNum_eq_zero_iff, V_compl]

/-- An edgeless graph needs one clique per vertex. -/
@[simp] theorem cliqueCoverNum_empty (n : ℕ) : (empty n).cliqueCoverNum = n := by
  rw [cliqueCoverNum_eq, compl_empty, chromNum_complete]

@[simp] theorem cliqueCoverNum_complete_zero : (complete 0).cliqueCoverNum = 0 := by
  rw [cliqueCoverNum_eq, compl_complete, chromNum_empty_zero]

@[simp] theorem cliqueCoverNum_complete (n : ℕ) : (complete (n + 1)).cliqueCoverNum = 1 := by
  rw [cliqueCoverNum_eq, compl_complete, chromNum_empty]

/-- Cliques never cross a disjoint union, so the clique covers add. -/
@[simp] theorem cliqueCoverNum_disjUnion (G H : IsoGraph) :
    (G ⊕g H).cliqueCoverNum = G.cliqueCoverNum + H.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, compl_disjUnion, chromNum_join, cliqueCoverNum_eq, cliqueCoverNum_eq]

@[simp] theorem cliqueCoverNum_join (G H : IsoGraph) :
    (G ∇g H).cliqueCoverNum = max G.cliqueCoverNum H.cliqueCoverNum := by
  rw [cliqueCoverNum_eq, compl_join, chromNum_disjUnion, cliqueCoverNum_eq, cliqueCoverNum_eq]

/-- A bipartite graph with an edge has `χ = ω = 2`. -/
theorem chromNum_eq_cliqueNum_of_isBipartite {G : IsoGraph} (hb : IsBipartite G) (hE : 0 < G.E) :
    G.chromNum = G.cliqueNum := by
  have h1 : G.chromNum = 2 := chromNum_eq_two_iff.2 ⟨hb, hE⟩
  have h2 := cliqueNum_le_two_of_isBipartite hb
  have h3 := two_le_cliqueNum_of_E_pos hE
  omega

/-- An acyclic graph has no triangle, so no clique on three vertices. -/
theorem cliqueNum_le_two_of_isAcyclic {G : IsoGraph} (h : IsAcyclic G) : G.cliqueNum ≤ 2 := by
  by_contra hc
  exact not_isAcyclic_of_girth_pos
    (by rw [girth_eq_three_of_cliqueNum (by omega)]; omega) h

theorem cliqueCount_three_eq_zero_of_isAcyclic {G : IsoGraph} (h : IsAcyclic G) :
    G.cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_iff G |>.2 (by rw [girth_eq_zero_iff.2 h]; omega)

/-- A tree on at least two vertices has an edge, and no triangle. -/
theorem cliqueNum_of_isTree {G : IsoGraph} (h : IsTree G) (hV : 2 ≤ G.V) : G.cliqueNum = 2 := by
  have h1 := h.E_add_one
  have h2 := two_le_cliqueNum_of_E_pos (G := G) (by omega)
  have h3 := cliqueNum_le_two_of_isAcyclic ((isTree_iff_isConnected_and_isAcyclic G).1 h).2
  omega

/-! ### Bounds on the chromatic index of the regular families -/

theorem sub_one_le_edgeChromNum_complete (n : ℕ) : n - 1 ≤ (complete n).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (complete n)
  rwa [maxDeg_complete] at h

theorem edgeChromNum_complete_le (n : ℕ) : (complete n).edgeChromNum ≤ 2 * (n - 1) - 1 := by
  have h := edgeChromNum_le_two_mul_maxDeg_sub_one (complete n)
  rwa [maxDeg_complete] at h

/-! ### The two-approximation for vertex covers

A maximum matching leaves an independent set behind, so `|V| ≤ α + 2ν`; with Gallai's identity
`α + τ = |V|` this is the classical `τ ≤ 2ν`.  Together with `ν ≤ τ` it says that a maximum
matching always determines the vertex cover number to within a factor of two. -/

@[toIsoGraph V_le_indepNum_add_two_mul_matchNum]
theorem _root_.CGraph.card_le_indepNum_add_two_mul_matchNum (G : CGraph) :
    FinEnum.card G.V ≤ G.indepNum + 2 * G.matchNum :=
  CGraph.card_le_indepNum_add_two_mul_indepNum_lineGraph G

/-- **The vertex cover number is at most twice the matching number.**  This is the guarantee
behind the greedy two-approximation algorithm for minimum vertex cover. -/
theorem coverNum_le_two_mul_matchNum (G : IsoGraph) : G.coverNum ≤ 2 * G.matchNum := by
  have h1 := G.V_le_indepNum_add_two_mul_matchNum
  have h2 := G.coverNum_add_indepNum
  omega

theorem matchNum_le_coverNum_le_two_mul_matchNum (G : IsoGraph) :
    G.matchNum ≤ G.coverNum ∧ G.coverNum ≤ 2 * G.matchNum :=
  ⟨G.matchNum_le_coverNum, G.coverNum_le_two_mul_matchNum⟩

/-! ### Cliques in cycles and wheels

A cycle is vertex-transitive, so `α · ω ≤ n`; since `α(Cₙ) = ⌊n/2⌋` is more than a third of `n`
once `n ≥ 4`, this alone forces `ω = 2` — the cycle is triangle-free, with no need to inspect
its walks. -/

@[simp] theorem cliqueNum_cycle_three : (cycle 3).cliqueNum = 3 := by
  rw [cycle_three, cliqueNum_complete]

/-- **A cycle of length at least four is triangle-free.** -/
@[simp] theorem cliqueNum_cycle (n : ℕ) : (cycle (n + 4)).cliqueNum = 2 := by
  show (cycle (n + 1 + 3)).cliqueNum = 2
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_cycle (n + 1 + 3))
  rw [V_cycle, indepNum_cycle] at h
  have h2 : 2 ≤ (cycle (n + 1 + 3)).cliqueNum :=
    two_le_cliqueNum_of_E_pos (by rw [E_cycle]; omega)
  by_contra hc
  have h3 : (n + 1 + 3) / 2 * 3 ≤ (n + 1 + 3) / 2 * (cycle (n + 1 + 3)).cliqueNum :=
    Nat.mul_le_mul (le_refl _) (by omega)
  omega

/-! ### The domination number of a cycle -/

/-- **The domination number of a cycle**: `γ(Cₙ) = ⌈n/3⌉`.  The upper bound picks every third
vertex, `0, 3, 6, …`; the lower bound is the general `3γ ≥ n` bound for cubic-or-less graphs
already available as `le_domNum_cycle`. -/
@[simp] theorem domNum_cycle (n : ℕ) : (cycle (n + 3)).domNum = (n + 5) / 3 := by
  apply le_antisymm
  · simp only [IsoGraph.cycle, IsoGraph.domNum_mk]
    set m := (n + 5) / 3
    set s : Finset (CGraph.cycle (n + 3)).V :=
      Finset.image (fun i : Fin m => ⟨3 * (i : ℕ), by omega⟩) Finset.univ
    have hcard : s.card = m := by
      rw [Finset.card_image_of_injective]
      · simp [Finset.card_univ, Fintype.card_fin]
      · intro a b hab
        rw [Fin.ext_iff] at hab
        simp at hab
        exact Fin.ext (by omega)
    have hdom : (CGraph.cycle (n + 3)).IsDominatingSet s := by
      intro v
      have hvlt : v.val < n + 3 := v.2
      have hmod : v.val % 3 = 0 ∨ v.val % 3 = 1 ∨ v.val % 3 = 2 := by omega
      have mem_s_of_zero_mod : ∀ k hk, k % 3 = 0 → (⟨k, hk⟩ : (CGraph.cycle (n + 3)).V) ∈ s := by
        intro k hk h0
        simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨k / 3, by omega⟩, by simp; omega⟩
      rcases hmod with h0 | h1 | h2
      · left; exact mem_s_of_zero_mod v.val hvlt h0
      · right
        have hv1 : 1 ≤ v.val := by omega
        set u : (CGraph.cycle (n + 3)).V := ⟨v.val - 1, by omega⟩
        refine ⟨u, mem_s_of_zero_mod _ _ (by omega), ?_⟩
        have huv : (u.val + 1) % (n + 3) = v.val := by
          show ((v.val - 1) + 1) % (n + 3) = v.val
          simp [Nat.sub_add_cancel hv1]
          omega
        rw [CGraph.cycle_adj_val]
        have hne : u.val ≠ v.val := by
          show (v.val - 1) ≠ v.val
          omega
        show _ ∧ _
        exact ⟨hne, Or.inl huv⟩
      · by_cases hvlast : v.val = n + 2
        · right
          set u : (CGraph.cycle (n + 3)).V := ⟨0, by omega⟩
          refine ⟨u, mem_s_of_zero_mod _ _ (by omega), ?_⟩
          show (CGraph.cycle (n + 3)).Adj u v = true
          rw [CGraph.cycle_adj_val]
          simp [u, hvlast]
        · right
          set u : (CGraph.cycle (n + 3)).V := ⟨v.val + 1, by omega⟩
          refine ⟨u, mem_s_of_zero_mod _ _ (by omega), ?_⟩
          have hvlt2 : v.val + 1 < n + 3 := by omega
          show (CGraph.cycle (n + 3)).Adj u v = true
          have huval : u.val = v.val + 1 := by simp [u]
          rw [CGraph.cycle_adj_val, huval]
          have hmod2 : (v.val + 1) % (n + 3) = v.val + 1 := Nat.mod_eq_of_lt hvlt2
          exact ⟨by omega, Or.inr hmod2⟩
    exact le_trans (CGraph.domNum_le_card_of_isDominatingSet hdom) hcard.le
  · have hlb := le_domNum_cycle n
    omega

/-- The total domination-style consequence: a cycle needs at least a third of its vertices
dominated, and `⌈n/3⌉` is exactly a third when `3 ∣ n`. -/
theorem three_mul_domNum_cycle (m : ℕ) : 3 * (cycle (3 * m + 3)).domNum = 3 * m + 3 := by
  rw [show 3 * m + 3 = (3 * m) + 3 from rfl, domNum_cycle]
  omega

/-- The independence number of a tensor product is at least the larger of the two "column"
bounds: an independent set of one factor lifts to a whole slab. -/
theorem indepNum_tensorProduct_ge {G H : IsoGraph} :
    max (G.indepNum * H.V) (G.V * H.indepNum) ≤ (G ⊗g H).indepNum := by
  exact max_le (indepNum_mul_V_le_indepNum_tensorProduct G H)
    (V_mul_indepNum_le_indepNum_tensorProduct G H)

/-! ### Clique covers of the products

No clique meets an independent set twice, so `α ≤ θ`, and the independent sets that a product
inherits from its factors bound the clique cover number from below.  Only the strong product also
has an upper bound of the same shape, `cliqueCoverNum_strongProduct_le`; in the cartesian and
tensor products a clique is confined to a fibre and the two sides are genuinely far apart. -/

theorem indepNum_mul_indepNum_le_cliqueCoverNum_cartesianProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (G □g H).cliqueCoverNum :=
  le_trans (indepNum_mul_indepNum_le_indepNum_cartesianProduct G H)
    (indepNum_le_cliqueCoverNum _)

theorem indepNum_mul_indepNum_le_cliqueCoverNum_strongProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (G ⊠g H).cliqueCoverNum :=
  le_trans (indepNum_mul_indepNum_le_indepNum_strongProduct G H) (indepNum_le_cliqueCoverNum _)

theorem indepNum_mul_V_le_cliqueCoverNum_tensorProduct (G H : IsoGraph) :
    G.indepNum * H.V ≤ (G ⊗g H).cliqueCoverNum :=
  le_trans (indepNum_mul_V_le_indepNum_tensorProduct G H) (indepNum_le_cliqueCoverNum _)

/-- A bipartite graph with a near-perfect matching has the largest independent set its vertex
count allows: one colour class already has `⌈|V| / 2⌉` vertices, and the matching stops anything
bigger. -/
theorem indepNum_of_isBipartite_of_matchNum {G : IsoGraph} (h : IsBipartite G) (hE : 0 < G.E)
    (hm : G.V ≤ 2 * G.matchNum + 1) : G.indepNum = (G.V + 1) / 2 := by
  have hlb := V_le_chromNum_mul_indepNum G
  rw [chromNum_eq_two_iff.mpr ⟨h, hE⟩] at hlb
  have hsum := coverNum_add_indepNum G
  have hcov := matchNum_le_coverNum G
  have h2 := two_mul_matchNum_le_V G
  omega

/-- The complementary statement: the cover takes the other half. -/
theorem coverNum_of_isBipartite_of_matchNum {G : IsoGraph} (h : IsBipartite G) (hE : 0 < G.E)
    (hm : G.V ≤ 2 * G.matchNum + 1) : G.coverNum = G.V / 2 := by
  have h1 := indepNum_of_isBipartite_of_matchNum h hE hm
  have hsum := coverNum_add_indepNum G
  omega

/-- The complement of a lexicographic product is the lexicographic product of the complements,
so a clique cover splits the same way a colouring does. -/
theorem cliqueCoverNum_lexProduct_le (G H : IsoGraph) :
    (G ·g H).cliqueCoverNum ≤ G.cliqueCoverNum * H.cliqueCoverNum := by
  simp only [cliqueCoverNum_eq, compl_lexProduct]
  exact chromNum_lexProduct_le _ _

/-! ### Edge chromatic lower bounds from the maximum degree

`Δ ≤ χ'` because the edges at a vertex pairwise conflict.  Until Vizing's theorem is available
this is the only entry many of these cells can have, but it is a sharp one: for every class-one
graph it is the answer.
-/

/-- The Mycielskian's apex sees every shadow, and the original vertices double their degree. -/
theorem le_edgeChromNum_mycielskian (G : IsoGraph) :
    max (2 * maxDeg G) G.V ≤ (mycielskian G).edgeChromNum := by
  have h := maxDeg_le_edgeChromNum (mycielskian G)
  rwa [maxDeg_mycielskian] at h

/-- The Mycielskian of a triangle-free graph is triangle-free: that is the whole point of the
construction. -/
theorem cliqueCount_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : G.cliqueNum ≤ 2) :
    (mycielskian G).cliqueCount 3 = 0 :=
  (cliqueCount_eq_zero_iff _ 3).2 (by rw [cliqueNum_mycielskian_eq_two hV h]; omega)

theorem cliqueNum_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 4) □g cycle (n + 4)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := cycle (m + 4)) (H := cycle (n + 4))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

theorem indepNum_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) □g cycle (n + 4))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_cartesianProduct_cycle]

/-! ### Colourings and metrics of the strong and lexicographic products -/

/-- If both factors have chromatic number equal to their clique number, the strong product does
too: the clique bound below meets the product colouring above. -/
theorem chromNum_strongProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ⊠g H).chromNum = G.cliqueNum * H.cliqueNum := by
  have h1 := chromNum_strongProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ⊠g H)
  rw [cliqueNum_strongProduct] at h2
  rw [hG, hH] at h1
  omega

/-- The same for the lexicographic product. -/
theorem chromNum_lexProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ·g H).chromNum = G.cliqueNum * H.cliqueNum := by
  have h1 := chromNum_lexProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ·g H)
  rw [cliqueNum_lexProduct] at h2
  rw [hG, hH] at h1
  omega

theorem chromNum_eq_cliqueNum_cycle_even (m : ℕ) :
    (cycle (2 * m + 4)).chromNum = (cycle (2 * m + 4)).cliqueNum := by
  rw [cliqueNum_cycle, show 2 * m + 4 = 2 * (m + 1) + 2 from by ring, chromNum_cycle_even]

theorem chromNum_strongProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ⊠g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_strongProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

theorem chromNum_lexProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ·g cycle (2 * n + 4)).chromNum = 4 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

/-! ### The cartesian product of a complete graph with a cycle -/

theorem cliqueNum_cartesianProduct_complete_cycle (m n : ℕ) :
    (complete (m + 2) □g cycle (n + 4)).cliqueNum = m + 2 := by
  have h := cliqueNum_cartesianProduct (G := complete (m + 2)) (H := cycle (n + 4))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [cliqueNum_complete, cliqueNum_cycle] at h
  omega

theorem chromNum_cartesianProduct_complete_cycle_even (m t : ℕ) :
    (complete (m + 2) □g cycle (2 * t + 2)).chromNum = m + 2 := by
  have h := chromNum_cartesianProduct (G := complete (m + 2)) (H := cycle (2 * t + 2))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_complete, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_complete_cycle_odd (m t : ℕ) :
    (complete (m + 3) □g cycle (2 * t + 3)).chromNum = m + 3 := by
  have h := chromNum_cartesianProduct (G := complete (m + 3)) (H := cycle (2 * t + 3))
    (by rw [V_complete]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_complete, chromNum_cycle_odd] at h
  omega

/-! ### Colouring the torus and the cylinder -/

theorem chromNum_cartesianProduct_cycle_even_even (a b : ℕ) :
    (cycle (2 * a + 2) □g cycle (2 * b + 2)).chromNum = 2 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 2)) (H := cycle (2 * b + 2))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_even, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_even (a b : ℕ) :
    (cycle (2 * a + 3) □g cycle (2 * b + 2)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := cycle (2 * b + 2))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_odd, chromNum_cycle_even] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_odd (a b : ℕ) :
    (cycle (2 * a + 3) □g cycle (2 * b + 3)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := cycle (2 * b + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle]; omega)
  rw [chromNum_cycle_odd, chromNum_cycle_odd] at h
  omega

theorem chromNum_cartesianProduct_cycle_even_path (a n : ℕ) :
    (cycle (2 * a + 2) □g path (n + 2)).chromNum = 2 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 2)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [chromNum_cycle_even, chromNum_path] at h
  omega

theorem chromNum_cartesianProduct_cycle_odd_path (a n : ℕ) :
    (cycle (2 * a + 3) □g path (n + 2)).chromNum = 3 := by
  have h := chromNum_cartesianProduct (G := cycle (2 * a + 3)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [chromNum_cycle_odd, chromNum_path] at h
  omega

theorem cliqueNum_mycielskian_cycle (m : ℕ) :
    (mycielskian (cycle (m + 4))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (cycle (m + 4)) (by rw [V_cycle]; omega)
  rw [cliqueNum_cycle] at h
  omega

end IsoGraph
