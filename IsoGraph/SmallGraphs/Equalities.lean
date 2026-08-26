import IsoGraph.SmallGraphs.Defs.Tutte12Cage

/-!
# Equalities between the named graphs

Special cases in which one named graph *is* another: the complement of a Kneser graph, a triangular
graph as a Kneser graph, a Paley graph over `ZMod q` as the field version, a complete bipartite
graph as a join.  These are the `simp` lemmas that put a named graph into normal form, so they come
before anything that computes an invariant.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

/-- **The complement of the rook's graph is the tensor product of complete graphs**: two squares
of the board are non-adjacent in `Kₘ □ Kₙ` exactly when they agree in neither coordinate.  Both
sides are literally on `Fin m × Fin n`, so this is an equality of `CGraph`s. -/
theorem compl_rook (m n : ℕ) :
    (rook m n)ᶜ = complete m ⊗g complete n := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun p ↦ funext fun q ↦ ?_))
  rw [compl_adj, cartesianProduct_adj, tensorProduct_adj, complete_adj, complete_adj]
  have hpq : (p = q) ↔ (p.1 = q.1 ∧ p.2 = q.2) := Prod.ext_iff
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, hpq]

end

section
open Fintype
variable {m n : ℕ}

/-! ### Kneser graphs

`kneser n k` is strongly regular only for `k ≤ 2` (or in the degenerate case `n = 2k`): two
non-adjacent `k`-sets meeting in `i` points have `(n - 2k + i).choose k` common neighbours, and
`i` ranges over `1, …, k-1`.  The degree and the adjacent-pair count, on the other hand, are
uniform for every `k`; those are `card_nbrs_kneser` and `card_nbrs_inter_kneser`. -/

/-- The `k`-subsets of `Fin n` avoiding a set `S` are exactly the `k`-subsets of `Sᶜ`, so there
are `(n - |S|).choose k` of them. -/
theorem card_filter_kneser_disjoint {k : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter fun u : {u : Finset (Fin n) // u.card = k} ↦ u.1 ∩ S = ∅).card
      = (n - S.card).choose k := by
  have hc : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
  rw [← hc, ← Finset.card_powersetCard k Sᶜ]
  refine Finset.card_bij (fun u _ ↦ u.1) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine Finset.mem_powersetCard.2 ⟨fun x hx ↦ Finset.mem_compl.2 fun hxS ↦ ?_, u.2⟩
    have : x ∈ u.1 ∩ S := Finset.mem_inter.2 ⟨hx, hxS⟩
    rw [hu] at this
    exact absurd this (Finset.notMem_empty x)
  · exact fun a _ b _ hab ↦ Subtype.ext hab
  · intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.1 hT
    refine ⟨⟨T, hTcard⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine Finset.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
    exact Finset.mem_compl.1 (hTsub (Finset.mem_inter.1 hx).1) (Finset.mem_inter.1 hx).2

/-! ### The Paley graph of a finite field -/

/-- The **Paley graph** of a finite field: `x ~ y` when `y - x` is a nonzero square.  For
`Fintype.card F % 4 = 1` this is `paley (Fintype.card F)` up to isomorphism; see `paleyIso`. -/
@[toIsoGraph]
def paleyField (F : Type) [Field F] [FinEnum F] : CGraph :=
  cayleyAdd F fun z ↦ decide (quadraticChar F z = 1)

end

section
open Fintype
variable {m n : ℕ}
variable {F : Type} [Field F] [FinEnum F]

theorem paleyField_adj (hq : Fintype.card F % 4 = 1) (x y : F) :
    (paleyField F).Adj x y = decide (quadraticChar F (y - x) = 1) := by
  show (cayleyAdd F fun z ↦ decide (quadraticChar F z = 1)).Adj x y = _
  rw [cayleyAdd_adj, show x - y = -(y - x) by ring, quadraticChar_neg' hq]
  by_cases h : x = y
  · subst h
    simp
  · simp [h]

/-- Multiplying by a non-square turns adjacency in a Paley graph into adjacency in its
complement: `χ (g * (y - x)) = -χ (y - x)`. -/
theorem paleyField_adj_mul (hq : Fintype.card F % 4 = 1) {g : F} (hg : ¬ IsSquare g) (x y : F) :
    (paleyField F).Adj (g * x) (g * y) = ((paleyField F)ᶜ).Adj x y := by
  have hg0 : g ≠ 0 := ne_zero_of_not_isSquare hg
  have hχg : quadraticChar F g = -1 :=
    (quadraticChar_dichotomy hg0).resolve_left fun h ↦
      hg ((quadraticChar_one_iff_isSquare hg0).1 h)
  rw [paleyField_adj hq, compl_adj, paleyField_adj hq,
    show g * y - g * x = g * (y - x) from by ring, map_mul, hχg]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    rcases quadraticChar_dichotomy hne with h | h <;> rw [h] <;> simp [hxy]

/-- **Paley graphs of fields are self-complementary**: multiplication by a fixed non-square is an
isomorphism from the complement onto the graph. -/
def Iso.complPaleyField (hq : Fintype.card F % 4 = 1) {g : F} (hg : ¬ IsSquare g) :
    (paleyField F)ᶜ ≃cg paleyField F :=
  isoOfAdj (G := (paleyField F)ᶜ) (H := paleyField F)
    (show F ≃ F from Equiv.mulLeft₀ g (ne_zero_of_not_isSquare hg)) (paleyField_adj_mul hq hg)

end

section
open Fintype
variable {m n : ℕ}

/-! ### `paley q` is the field version over `ZMod q` -/

theorem paley_adj_eq (q : ℕ) [NeZero q] [Fact q.Prime] (a b : ZMod q) :
    (paley q).Adj (zmodEquivFin q a) (zmodEquivFin q b) = (paleyField (ZMod q)).Adj a b := by
  have key : ∀ u v : ZMod q,
      (qrTable q)[((zmodEquivFin q v).1 + q - (zmodEquivFin q u).1) % q]!
        = decide (∃ r : ZMod q, r ≠ 0 ∧ r * r = v - u) := by
    intro u v
    show (qrTable q)[(v.val + q - u.val) % q]! = _
    rw [zmod_val_sub u v, qrTable_getElem q _ (ZMod.val_lt (v - u))]
    simp only [exists_sq_iff_val]
  show (ofRel (Fin q) _).Adj _ _ = (cayleyAdd (ZMod q) _).Adj a b
  rw [ofRel_adj, cayleyAdd_adj]
  show (decide ((zmodEquivFin q a) ≠ (zmodEquivFin q b)) &&
      ((qrTable q)[((zmodEquivFin q b).1 + q - (zmodEquivFin q a).1) % q]! ||
       (qrTable q)[((zmodEquivFin q a).1 + q - (zmodEquivFin q b).1) % q]!)) = _
  rw [key a b, key b a,
    show decide ((zmodEquivFin q a) ≠ (zmodEquivFin q b)) = decide (a ≠ b) from by
      simp [EmbeddingLike.apply_eq_iff_eq]]
  -- both sides are now `decide (a ≠ b) && (· || ·)`; the two disjuncts differ only in how they
  -- say "is a nonzero square", and `simp` must not be let near them — it unfolds the character
  -- to `quadraticCharFun` and then the `Fintype` instance in `quadraticChar_eq_one_iff` no longer
  -- matches the one `paleyField` was elaborated with
  exact congrArg₂ (· && ·) rfl (congrArg₂ (· || ·)
    (decide_eq_decide.2 (quadraticChar_eq_one_iff _).symm)
    (decide_eq_decide.2 (quadraticChar_eq_one_iff _).symm))

/-- For a prime `q`, `paley q` is the Paley graph of the field `ZMod q`. -/
@[toIsoGraph paleyField_zmod]
def paleyIso (q : ℕ) [NeZero q] [Fact q.Prime] : paleyField (ZMod q) ≃cg paley q :=
  ⟨zmodEquivFin q, fun {a b} ↦
    iff_of_eq (congrArg (fun x : Bool ↦ x = true) (paley_adj_eq q a b))⟩

/-- **`paley q` is self-complementary**, as data: transport `Iso.complPaleyField` — multiplication
by the non-residue `g` — along `paleyIso q`.  Naming the non-residue keeps this computable; for
the bare existence statement see `Iso.complPaley`. -/
def Iso.complPaleyOfNotIsSquare (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) {g : ZMod q}
    (hg : ¬ IsSquare g) : (paley q)ᶜ ≃cg paley q :=
  (Iso.compl (paleyIso q)).symm.trans
    ((Iso.complPaleyField (F := ZMod q)
      (by rw [← @FinEnum.card_eq_fintypeCard (ZMod q) _ FinEnum.instFintype]; exact hq)
      hg).trans (paleyIso q))

/-- Every prime `q ≡ 1 mod 4` has a non-residue, so `paley q` is self-complementary.  Choosing
one is the only classical step, and `Iso.complPaleyOfNotIsSquare` avoids it when a witness is
known. -/
noncomputable def Iso.complPaley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q)ᶜ ≃cg paley q :=
  Iso.complPaleyOfNotIsSquare q hq
    (Classical.choose_spec (FiniteField.exists_nonsquare (F := ZMod q) (by
      rw [ZMod.ringChar_zmod_n]; omega)))

end

section
open Fintype
variable (G : CGraph)

/-! ### Complete bipartite graphs

`K_{m,n}` has the permutations of each side as automorphisms; when the two sides have the same
size it may also swap them, and that is exactly what arc-transitivity needs. -/

/-- Permuting the two sides of `K_{n,n}` separately. -/
def bipartiteCongr (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : bipartite n n ≃cg bipartite n n :=
  autoOfPerm (G := bipartite n n) (Equiv.sumCongr σ τ) fun x y ↦ by
    show (bipartite n n).Adj (Sum.map σ τ x) (Sum.map σ τ y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

/-- Swapping the two sides of `K_{n,n}`. -/
def bipartiteSwap (n : ℕ) : bipartite n n ≃cg bipartite n n :=
  autoOfPerm (G := bipartite n n) (Equiv.sumComm (Fin n) (Fin n)) fun x y ↦ by
    show (bipartite n n).Adj (Sum.swap x) (Sum.swap y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

/-- Permuting the rays of the star `K_{1,n}` and fixing its centre. -/
def starAut (n : ℕ) (σ : Equiv.Perm (Fin n)) : bipartite 1 n ≃cg bipartite 1 n :=
  autoOfPerm (G := bipartite 1 n) (Equiv.sumCongr (Equiv.refl (Fin 1)) σ) fun x y ↦ by
    show (bipartite 1 n).Adj (Sum.map id σ x) (Sum.map id σ y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

/-- An automorphism of `G` permutes its edges, hence acts on its line graph. -/
def lineGraphAuto (σ : G ≃cg G) : lineGraph G ≃cg lineGraph G :=
  autoOfPerm (G := lineGraph G) (G.edgePerm σ) fun e f ↦ by
    obtain ⟨e, he⟩ := e
    obtain ⟨f, hf⟩ := f
    show (lineGraph G).Adj (G.edgePerm σ ⟨e, he⟩) (G.edgePerm σ ⟨f, hf⟩) = _
    simp only [lineGraph_adj, ne_eq, Subtype.ext_iff, edgePerm_coe, Sym2.mem_map,
      (Sym2.map.injective (RelIso.injective σ)).eq_iff]
    congr 1
    refine decide_eq_decide.2 ⟨?_, ?_⟩
    · rintro ⟨v, ⟨a, ha, rfl⟩, b, hb, hσ⟩
      exact ⟨a, ha, by rwa [RelIso.injective σ hσ] at hb⟩
    · rintro ⟨v, hv, hv'⟩
      exact ⟨σ v, ⟨v, hv, rfl⟩, v, hv', rfl⟩

/-- A permutation of the ground set is an automorphism of the Kneser graph. -/
def kneserAuto (n k : ℕ) (π : Equiv.Perm (Fin n)) : kneser n k ≃cg kneser n k :=
  autoOfPerm (G := kneser n k) (kneserPerm n k π) fun s t ↦ by
    obtain ⟨s, hs⟩ := s
    obtain ⟨t, ht⟩ := t
    show (kneser n k).Adj (kneserPerm n k π ⟨s, hs⟩) (kneserPerm n k π ⟨t, ht⟩) = _
    simp only [kneser_adj, ne_eq, Subtype.ext_iff, kneserPerm_coe,
      (Finset.image_injective π.injective).eq_iff, ← Finset.image_inter _ _ π.injective,
      Finset.image_eq_empty]

/-- A permutation of the ground set is an automorphism of the Johnson graph: it permutes the
`k`-subsets and preserves the size of an intersection. -/
def johnsonAuto (n k : ℕ) (π : Equiv.Perm (Fin n)) : johnson n k ≃cg johnson n k :=
  autoOfPerm (G := johnson n k) (kneserPerm n k π) fun s t ↦ by
    obtain ⟨s, hs⟩ := s
    obtain ⟨t, ht⟩ := t
    show (johnson n k).Adj (kneserPerm n k π ⟨s, hs⟩) (kneserPerm n k π ⟨t, ht⟩) = _
    simp only [johnson_adj, ne_eq, Subtype.ext_iff, kneserPerm_coe,
      (Finset.image_injective π.injective).eq_iff, ← Finset.image_inter _ _ π.injective,
      Finset.card_image_of_injective _ π.injective]

end

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

/-- Spider edges point away from the centre: the second endpoint is the larger one. -/
theorem spiderEdges_lt : ∀ (off : ℕ) (ks : List ℕ), 0 < off → ∀ p q,
    (p, q) ∈ spiderEdges off ks → p < q := by
  intro off ks
  induction ks generalizing off with
  | nil => simp [spiderEdges]
  | cons k rest ih =>
    intro hoff p q hpq
    rw [spiderEdges, List.mem_append] at hpq
    rcases hpq with h | h
    · rw [mem_legEdges] at h
      omega
    · exact ih (off + k) (by omega) p q h

/-- Every vertex of a leg has a predecessor along that leg. -/
theorem exists_mem_spiderEdges_snd : ∀ (off : ℕ) (ks : List ℕ) (q : ℕ), off ≤ q →
    q < off + ks.sum → ∃ p, (p, q) ∈ spiderEdges off ks := by
  intro off ks
  induction ks generalizing off with
  | nil => intro q h1 h2; simp only [List.sum_nil, Nat.add_zero] at h2; omega
  | cons k rest ih =>
    intro q h1 h2
    simp only [List.sum_cons] at h2
    by_cases hq : q < off + k
    · refine ⟨if q = off then 0 else q - 1, ?_⟩
      rw [spiderEdges, List.mem_append]
      refine Or.inl ?_
      rw [mem_legEdges]
      split_ifs with hqo
      · exact Or.inl ⟨rfl, hqo, by omega⟩
      · exact Or.inr ⟨by omega, by omega, by omega⟩
    · obtain ⟨p, hp⟩ := ih (off + k) q (by omega) (by omega)
      exact ⟨p, by rw [spiderEdges, List.mem_append]; exact Or.inr hp⟩

/-- A leg vertex has exactly one predecessor. -/
theorem spiderEdges_snd_unique : ∀ (off : ℕ) (ks : List ℕ), 0 < off → ∀ p p' q,
    (p, q) ∈ spiderEdges off ks → (p', q) ∈ spiderEdges off ks → p = p' := by
  intro off ks
  induction ks generalizing off with
  | nil => simp [spiderEdges]
  | cons k rest ih =>
    intro hoff p p' q h h'
    rw [spiderEdges, List.mem_append] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · rw [mem_legEdges] at h h'
      omega
    · exfalso
      rw [mem_legEdges] at h
      have := mem_spiderEdges_bound (off + k) rest p' q h'
      omega
    · exfalso
      rw [mem_legEdges] at h'
      have := mem_spiderEdges_bound (off + k) rest p q h
      omega
    · exact ih (off + k) (by omega) p p' q h h'

/-- A spider with a nonempty leg has an edge at its centre. -/
theorem exists_mem_spiderEdges_zero : ∀ (off : ℕ) (ks : List ℕ), 0 < ks.sum →
    ∃ q, (0, q) ∈ spiderEdges off ks := by
  intro off ks
  induction ks generalizing off with
  | nil => intro h; simp at h
  | cons k rest ih =>
    intro h
    simp only [List.sum_cons] at h
    by_cases hk : 0 < k
    · exact ⟨off, by
        rw [spiderEdges, List.mem_append]
        exact Or.inl ((mem_legEdges 0 off k 0 off).2 (Or.inl ⟨rfl, rfl, hk⟩))⟩
    · obtain ⟨q, hq⟩ := ih (off + k) (by omega)
      exact ⟨q, by rw [spiderEdges, List.mem_append]; exact Or.inr hq⟩

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

section
variable {G H : CGraph}

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

end

@[toIsoGraph simp empty_one_cartesianProduct]
def emptyOneCartesianProduct (G : CGraph) : empty 1 □g G ≃cg G :=
  (Iso.cartesianProductComm _ _).trans (Iso.cartesianProductEmptyOne G)

@[toIsoGraph simp empty_one_strongProduct]
def emptyOneStrongProduct (G : CGraph) : empty 1 ⊠g G ≃cg G :=
  (Iso.strongProductComm _ _).trans (Iso.strongProductEmptyOne G)

/-- A Cartesian product of edgeless graphs is edgeless. -/
@[toIsoGraph simp cartesianProduct_empty]
noncomputable def cartesianProductEmpty (m n : ℕ) :
    empty m □g empty n ≃cg empty (m * n) :=
  isoEmptyOfCard (by simp) (by simp)

/-- The strong product of complete graphs is complete. -/
@[toIsoGraph simp strongProduct_complete]
noncomputable def strongProductComplete (m n : ℕ) :
    complete m ⊠g complete n ≃cg complete (m * n) := by
  refine isoCompleteOfCard ?_ (by simp)
  intro x y hxy
  simp [strongProduct_adj, hxy]

/-- The lexicographic product of complete graphs is complete. -/
@[toIsoGraph simp lexProduct_complete]
noncomputable def lexProductComplete (m n : ℕ) :
    complete m ·g complete n ≃cg complete (m * n) := by
  refine isoCompleteOfCard ?_ (by simp)
  intro x y hxy
  by_cases hx : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h2 ↦ hxy (Prod.ext hx h2)
    simp [lexProduct_adj, hx, h2]
  · simp [lexProduct_adj, hx]

/-! ### Zero vertices

A factor with no vertices annihilates every product. -/

@[toIsoGraph simp cartesianProduct_empty_zero]
noncomputable def cartesianProductEmptyZero (G : CGraph) :
    G □g empty 0 ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.2.elim0) (by simp)

@[toIsoGraph simp empty_zero_cartesianProduct]
noncomputable def emptyZeroCartesianProduct (G : CGraph) :
    empty 0 □g G ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.1.elim0) (by simp)

@[toIsoGraph simp tensorProduct_empty_zero]
noncomputable def tensorProductEmptyZero (G : CGraph) :
    G ⊗g empty 0 ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.2.elim0) (by simp)

@[toIsoGraph simp empty_zero_tensorProduct]
noncomputable def emptyZeroTensorProduct (G : CGraph) :
    empty 0 ⊗g G ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.1.elim0) (by simp)

@[toIsoGraph simp strongProduct_empty_zero]
noncomputable def strongProductEmptyZero (G : CGraph) :
    G ⊠g empty 0 ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.2.elim0) (by simp)

@[toIsoGraph simp empty_zero_strongProduct]
noncomputable def emptyZeroStrongProduct (G : CGraph) :
    empty 0 ⊠g G ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.1.elim0) (by simp)

@[toIsoGraph simp lexProduct_empty_zero]
noncomputable def lexProductEmptyZero (G : CGraph) : G ·g empty 0 ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.2.elim0) (by simp)

@[toIsoGraph simp empty_zero_lexProduct]
noncomputable def emptyZeroLexProduct (G : CGraph) : empty 0 ·g G ≃cg empty 0 :=
  isoEmptyOfCard (fun x _ ↦ x.1.elim0) (by simp)

/-! ### Distributivity over disjoint unions

Every product distributes over `disjUnion`: on the left and the right for the three commutative
products, and on the left only for the lexicographic one.  These are good `simp` lemmas — they push
`disjUnion` outwards, so a product of unions normalises to a union of products.  The left-hand
forms are in `IsoGraph/Core/Quotient.lean`; the right-hand ones follow by commutativity. -/

@[toIsoGraph simp disjUnion_cartesianProduct]
def disjUnionCartesianProduct (G H K : CGraph) :
    (G ⊕g H) □g K
      ≃cg G □g K ⊕g H □g K :=
  (Iso.cartesianProductComm _ _).trans
    ((Iso.cartesianProductDisjUnion K G H).trans
      (Iso.disjUnion (Iso.cartesianProductComm _ _) (Iso.cartesianProductComm _ _)))

@[toIsoGraph simp disjUnion_tensorProduct]
def disjUnionTensorProduct (G H K : CGraph) :
    (G ⊕g H) ⊗g K ≃cg G ⊗g K ⊕g H ⊗g K :=
  (Iso.tensorProductComm _ _).trans
    ((Iso.tensorProductDisjUnion K G H).trans
      (Iso.disjUnion (Iso.tensorProductComm _ _) (Iso.tensorProductComm _ _)))

@[toIsoGraph simp disjUnion_strongProduct]
def disjUnionStrongProduct (G H K : CGraph) :
    (G ⊕g H) ⊠g K ≃cg G ⊠g K ⊕g H ⊠g K :=
  (Iso.strongProductComm _ _).trans
    ((Iso.strongProductDisjUnion K G H).trans
      (Iso.disjUnion (Iso.strongProductComm _ _) (Iso.strongProductComm _ _)))

/-- Multiplying by two independent vertices doubles the graph.  The same holds for the strong and
lexicographic products, but not for the tensor product, which is edgeless here. -/
@[toIsoGraph empty_two_cartesianProduct]
noncomputable def emptyTwoCartesianProduct (G : CGraph) :
    empty 2 □g G ≃cg G ⊕g G :=
  (Iso.cartesianProduct (disjUnionEmpty 1 1).symm (RelIso.refl _)).trans
    ((disjUnionCartesianProduct (empty 1) (empty 1) G).trans
      (Iso.disjUnion (emptyOneCartesianProduct G) (emptyOneCartesianProduct G)))

@[toIsoGraph cartesianProduct_empty_two]
noncomputable def cartesianProductEmptyTwo (G : CGraph) :
    G □g empty 2 ≃cg G ⊕g G :=
  (Iso.cartesianProductComm _ _).trans (emptyTwoCartesianProduct G)

@[toIsoGraph empty_two_strongProduct]
noncomputable def emptyTwoStrongProduct (G : CGraph) :
    empty 2 ⊠g G ≃cg G ⊕g G :=
  (Iso.strongProduct (disjUnionEmpty 1 1).symm (RelIso.refl _)).trans
    ((disjUnionStrongProduct (empty 1) (empty 1) G).trans
      (Iso.disjUnion (emptyOneStrongProduct G) (emptyOneStrongProduct G)))

@[toIsoGraph strongProduct_empty_two]
noncomputable def strongProductEmptyTwo (G : CGraph) :
    G ⊠g empty 2 ≃cg G ⊕g G :=
  (Iso.strongProductComm _ _).trans (emptyTwoStrongProduct G)

@[toIsoGraph empty_two_lexProduct]
noncomputable def emptyTwoLexProduct (G : CGraph) : empty 2 ·g G ≃cg G ⊕g G :=
  (Iso.lexProduct (disjUnionEmpty 1 1).symm (RelIso.refl _)).trans
    ((Iso.lexProductDisjUnion (empty 1) (empty 1) G).trans
      (Iso.disjUnion (Iso.emptyOneLexProduct G) (Iso.emptyOneLexProduct G)))

/-! ### Copies and blow-ups

`empty n □ G` is `n` disjoint copies of `G`, and `K_n[G]` is `n` copies with every pair of copies
joined; the two are complements of each other.  The complete multipartite graphs with equal parts
are exactly the blow-ups of a clique by an independent set. -/

/-- Peeling one copy off `empty (n+1) □ G`. -/
@[toIsoGraph empty_succ_cartesianProduct]
noncomputable def emptySuccCartesianProduct (n : ℕ) (G : CGraph) :
    empty (n + 1) □g G ≃cg G ⊕g empty n □g G := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1]
  exact (Iso.cartesianProduct (disjUnionEmpty 1 n).symm (RelIso.refl _)).trans
    ((disjUnionCartesianProduct (empty 1) (empty n) G).trans
      (Iso.disjUnion (emptyOneCartesianProduct G) (RelIso.refl _)))

/-- `K_m[G]` is `m` copies of `G` with every pair of copies joined — the complement of `m` disjoint
copies of `Gᶜ`. -/
@[toIsoGraph complete_lexProduct]
def completeLexProduct (m : ℕ) (G : CGraph) :
    complete m ·g G ≃cg (empty m □g Gᶜ)ᶜ := by
  rw [show complete m ·g G = ((complete m ·g G)ᶜ)ᶜ from (compl_compl _).symm]
  exact Iso.compl ((Iso.complLexProduct (complete m) G).trans
    (by rw [compl_complete]; exact Iso.emptyLexProduct m Gᶜ))

/-- The lexicographic product distributes over `join` in its first factor, for the same reason it
distributes over `disjUnion`: the two are exchanged by complementation. -/
@[toIsoGraph join_lexProduct]
def joinLexProduct (G H K : CGraph) :
    (G ∇g H) ·g K ≃cg G ·g K ∇g H ·g K := by
  rw [show (G ∇g H) ·g K = (((G ∇g H) ·g K)ᶜ)ᶜ from (compl_compl _).symm, show G ·g K ∇g H ·g K
      = ((G ·g K)ᶜ ⊕g (H ·g K)ᶜ)ᶜ from rfl]
  refine Iso.compl ((Iso.complLexProduct (G ∇g H) K).trans ?_)
  rw [compl_join]
  exact (Iso.lexProductDisjUnion Gᶜ Hᶜ Kᶜ).trans
    (Iso.disjUnion (Iso.complLexProduct G K).symm (Iso.complLexProduct H K).symm)

@[toIsoGraph simp lexProduct_empty]
noncomputable def lexProductEmpty (m n : ℕ) : empty m ·g empty n ≃cg empty (m * n) :=
  (Iso.emptyLexProduct m (empty n)).trans (cartesianProductEmpty m n)

@[toIsoGraph simp strongProduct_empty]
noncomputable def strongProductEmpty (m n : ℕ) :
    empty m ⊠g empty n ≃cg empty (m * n) :=
  (Iso.emptyStrongProduct m (empty n)).trans (cartesianProductEmpty m n)

end CGraph

namespace IsoGraph

/-! ## Line graphs and Mycielskians

The line graph turns a graph's edges into vertices, so the identities here are counted by `E`
rather than `V`: `lineGraph (star n)` is complete on `E (star n) = n` vertices, and
`lineGraph (complete n)` is the triangular graph `T(n) = J(n, 2)` on `C(n, 2)` of them. -/

@[simp] theorem lineGraph_empty (n : ℕ) : lineGraph (empty n) = empty 0 := by
  have hbot : (CGraph.empty n).toSimple = ⊥ := by
    ext a b
    simp [CGraph.toSimple]
  have h : ∀ e f : (CGraph.lineGraph (CGraph.empty n)).V,
      (CGraph.lineGraph (CGraph.empty n)).Adj e f = false := by
    rintro ⟨e, he⟩ f
    rw [hbot] at he
    simp at he
  rw [empty_def, lineGraph_mk, mk_eq_empty h, CGraph.card_lineGraph, CGraph.E_empty]

/-! Each of the standard families is determined by its parameter. -/

@[simp] theorem empty_inj {m n : ℕ} : empty m = empty n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem complete_inj {m n : ℕ} : complete m = complete n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem path_inj {m n : ℕ} : path m = path n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem cycle_inj {m n : ℕ} : cycle m = cycle n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem mycielskian_empty_zero : mycielskian (empty 0) = empty 1 := by
  have h : ∀ x y : (CGraph.mycielskian (CGraph.empty 0)).V,
      (CGraph.mycielskian (CGraph.empty 0)).Adj x y = false := by
    have : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rintro (_ | (a | a)) (_ | (b | b)) <;> first | rfl | exact isEmptyElim a | exact isEmptyElim b
  rw [empty_def, mycielskian_mk, mk_eq_empty h]
  simp

end IsoGraph
