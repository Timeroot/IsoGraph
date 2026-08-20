import IsoGraph.SmallGraphs.Defs.Families

/-!
# The constructions on isomorphism classes

The constructions of `Core.Defs`, lifted through `IsoGraph = Quotient CGraph.isoSetoid`.  Each
operation is shown to respect isomorphism, gets its notation on the quotient, and gets the
structural laws that make the lift usable: associativity, commutativity, the units, and
distributivity of the products over the disjoint union.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

@[simp, toIsoGraph] theorem compl_compl : Gᶜᶜ = G := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  rcases eq_or_ne x y with rfl | h
  · simp [G.loopless x]
  · simp [h, G.symm x y]

end

/-! ## Isomorphism congruences

Each construction below has to be shown to respect isomorphism before it can be lifted to the
quotient.  All of them are the same shape — a bijection of vertices that carries adjacency to
adjacency — so they are all built from `isoOfAdj`.  The ones that are tagged `@[toIsoGraph]` are
exactly the ones a construction is lifted along; the rest are isomorphisms between concrete
graphs, which the attribute reads as equations of isomorphism classes elsewhere.
-/

/-- Injectivity of `Sum.inl`, stated at the vertex type of a `disjUnion` rather than at a bare
`⊕`.  The two are definitionally equal but not *reducibly* so, and `simp` matches up to reducible
unfolding only — so `Sum.inl.injEq` does not fire on a goal about `(disjUnion G H).V`. -/
theorem disjUnion_inl_eq_inl (G H : CGraph) (a b : G.V) :
    (@Eq (G ⊕g H).V (Sum.inl a) (Sum.inl b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inl_injective h, fun h ↦ h ▸ rfl⟩

/-- Injectivity of `Sum.inr` at the vertex type of a `disjUnion`; see `disjUnion_inl_eq_inl`. -/
theorem disjUnion_inr_eq_inr (G H : CGraph) (a b : H.V) :
    (@Eq (G ⊕g H).V (Sum.inr a) (Sum.inr b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inr_injective h, fun h ↦ h ▸ rfl⟩

/-- `Prod.mk.injEq`, restated at the vertex type of a `lexProduct`.  Same reducibility gap as
`disjUnion_inl_eq_inl`: the pair equality that `compl` puts in front of a product adjacency lives
at `(lexProduct G H).V`, and `simp` will not see it as an equality of pairs. -/
theorem lexProduct_pair_eq (G H : CGraph)
    (a c : G.V) (b d : H.V) :
    (@Eq (G ·g H).V (a, b) (c, d)) = (a = c ∧ b = d) :=
  Prod.mk.injEq a b c d

/-- Complementation, as a bijection from the `k`-subsets of `Fin n` to the `(n - k)`-subsets. -/
def complSubsets (n k : ℕ) (hk : k ≤ n) :
    {s : Finset (Fin n) // s.card = k} ≃ {s : Finset (Fin n) // s.card = n - k} where
  toFun s := ⟨s.1ᶜ, by rw [Finset.card_compl, s.2, Fintype.card_fin]⟩
  invFun s := ⟨s.1ᶜ, by rw [Finset.card_compl, s.2, Fintype.card_fin]; omega⟩
  left_inv s := by ext : 1; exact _root_.compl_compl s.1
  right_inv s := by ext : 1; exact _root_.compl_compl s.1

@[simp] theorem complSubsets_coe (n k : ℕ) (hk : k ≤ n) (s : {s : Finset (Fin n) // s.card = k}) :
    ((complSubsets n k hk s : {s : Finset (Fin n) // s.card = n - k}) : Finset (Fin n)) = s.1ᶜ :=
  rfl

/-- The two differences between distinct vertices of `circulant n S` are both nonzero and sum to
`n`: one goes forwards around the cycle, the other backwards. -/
theorem circulant_diff_facts (n : ℕ) (x y : Fin n) (hxy : x.1 ≠ y.1) :
    (y.1 + n - x.1) % n + (x.1 + n - y.1) % n = n ∧
      0 < (y.1 + n - x.1) % n ∧ 0 < (x.1 + n - y.1) % n := by
  have h1 := sub_mod_cases x.isLt y.isLt
  have h2 := sub_mod_cases y.isLt x.isLt
  omega

/-- Peel the first fibre off a dependent sigma type indexed by `Fin (n + 1)`.  Mathlib has no
such equivalence, and it is what lets `sigmaUnion` over `Fin (n + 1)` be recognised as a
disjoint union. -/
def sigmaFinSuccEquiv {n : ℕ} (α : Fin (n + 1) → Type) :
    (Σ i, α i) ≃ α 0 ⊕ Σ i : Fin n, α i.succ where
  toFun p := Fin.cases (motive := fun i ↦ α i → (α 0 ⊕ Σ i : Fin n, α i.succ))
    Sum.inl (fun j x ↦ Sum.inr ⟨j, x⟩) p.1 p.2
  invFun := Sum.elim (fun x ↦ ⟨0, x⟩) (fun p ↦ ⟨p.1.succ, p.2⟩)
  left_inv := by
    rintro ⟨i, x⟩
    induction i using Fin.cases <;> rfl
  right_inv := by rintro (x | ⟨j, x⟩) <;> rfl

/-- Pushing an edge of `G` forward into `G + H` gives an edge of `G + H`. -/
private theorem mem_edgeSet_map_inl (G H : CGraph) (e : Sym2 G.V)
    (he : e ∈ G.toSimple.edgeSet) :
    Sym2.map Sum.inl e ∈ (G ⊕g H).toSimple.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
    rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, disjUnion_adj_inl_inl]
    exact he

/-- Pushing an edge of `H` forward into `G + H` gives an edge of `G + H`. -/
private theorem mem_edgeSet_map_inr (G H : CGraph) (e : Sym2 H.V)
    (he : e ∈ H.toSimple.edgeSet) :
    Sym2.map Sum.inr e ∈ (G ⊕g H).toSimple.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
    rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, disjUnion_adj_inr_inr]
    exact he

/-- An edge of `G` or an edge of `H`, read as an edge of `G + H`.  It is onto because the two
sides have the same number of edges, so `lineGraphDisjUnion` never has to name an inverse. -/
def sumEdge (G H : CGraph) :
    (lineGraph G).V ⊕ (lineGraph H).V → (lineGraph (G ⊕g H)).V
  | .inl e => ⟨Sym2.map Sum.inl e.1, mem_edgeSet_map_inl G H e.1 e.2⟩
  | .inr e => ⟨Sym2.map Sum.inr e.1, mem_edgeSet_map_inr G H e.1 e.2⟩

theorem sumEdge_inj (G H : CGraph) :
    Function.Injective (sumEdge G H) := by
  rintro (⟨e, he⟩ | ⟨e, he⟩) (⟨f, hf⟩ | ⟨f, hf⟩) h <;>
    replace h : Sym2.map _ e = Sym2.map _ f := congrArg Subtype.val h
  · exact congrArg Sum.inl (Subtype.ext (Sym2.map.injective Sum.inl_injective h))
  · induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ c d =>
        rw [Sym2.map_pair_eq, Sym2.map_pair_eq] at h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by simp)
  · induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ c d =>
        rw [Sym2.map_pair_eq, Sym2.map_pair_eq] at h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by simp)
  · exact congrArg Sum.inr (Subtype.ext (Sym2.map.injective Sum.inr_injective h))

end CGraph

namespace CGraph.Iso

section
variable {G G' H H' : CGraph}

/-- Disjoint union respects isomorphism. -/
@[toIsoGraph]
def disjUnion (i : G ≃cg G') (j : H ≃cg H') :
    G ⊕g H ≃cg G' ⊕g H' :=
  isoOfAdj (G := G ⊕g H) (H := G' ⊕g H')
    (Equiv.sumCongr i.toEquiv j.toEquiv) fun x y ↦ by
      rcases x with a | b <;> rcases y with c | d
      · show (G' ⊕g H').Adj (.inl (i a)) (.inl (i c)) = _
        rw [disjUnion_adj_inl_inl, i.adj_eq]; rfl
      · show (G' ⊕g H').Adj (.inl (i a)) (.inr (j d)) = _
        rfl
      · show (G' ⊕g H').Adj (.inr (j b)) (.inl (i c)) = _
        rfl
      · show (G' ⊕g H').Adj (.inr (j b)) (.inr (j d)) = _
        rw [disjUnion_adj_inr_inr, j.adj_eq]; rfl

/-- The join respects isomorphism; it is a complement of a disjoint union of complements. -/
def join
    (i : G ≃cg G') (j : H ≃cg H') : G ∇g H ≃cg G' ∇g H' :=
  Iso.compl (Iso.disjUnion (Iso.compl i) (Iso.compl j))

/-- The cartesian product respects isomorphism. -/
@[toIsoGraph]
def cartesianProduct
    (i : G ≃cg G') (j : H ≃cg H') :
    G □g H ≃cg G' □g H' :=
  isoOfAdj (G := G □g H) (H := G' □g H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show ((decide (i x.1 = i y.1) && H'.Adj (j x.2) (j y.2)) ||
        (G'.Adj (i x.1) (i y.1) && decide (j x.2 = j y.2))) = _
      rw [i.adj_eq, j.adj_eq, show decide (i x.1 = i y.1) = decide (x.1 = y.1) from by simp,
        show decide (j x.2 = j y.2) = decide (x.2 = y.2) from by simp]
      rfl

/-- The tensor product respects isomorphism. -/
@[toIsoGraph]
def tensorProduct
    (i : G ≃cg G') (j : H ≃cg H') :
    G ⊗g H ≃cg G' ⊗g H' :=
  isoOfAdj (G := G ⊗g H) (H := G' ⊗g H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show (G'.Adj (i x.1) (i y.1) && H'.Adj (j x.2) (j y.2)) = _
      rw [i.adj_eq, j.adj_eq]
      rfl

/-- The strong product respects isomorphism. -/
@[toIsoGraph]
def strongProduct
    (i : G ≃cg G') (j : H ≃cg H') :
    G ⊠g H ≃cg G' ⊠g H' :=
  isoOfAdj (G := G ⊠g H) (H := G' ⊠g H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show (decide ((i x.1, j x.2) ≠ (i y.1, j y.2)) &&
        ((decide (i x.1 = i y.1) || G'.Adj (i x.1) (i y.1)) &&
          (decide (j x.2 = j y.2) || H'.Adj (j x.2) (j y.2)))) = _
      rw [i.adj_eq, j.adj_eq, show decide (i x.1 = i y.1) = decide (x.1 = y.1) from by simp,
        show decide (j x.2 = j y.2) = decide (x.2 = y.2) from by simp,
        show decide ((i x.1, j x.2) ≠ (i y.1, j y.2)) = decide (x ≠ y) from
          decide_eq_decide.2 (not_congr (by
            simp only [Prod.ext_iff, EmbeddingLike.apply_eq_iff_eq]
            exact (Prod.ext_iff (x := (x : G.V × H.V)) (y := y)).symm))]
      rfl

/-- The lexicographic product respects isomorphism. -/
@[toIsoGraph]
def lexProduct
    (i : G ≃cg G') (j : H ≃cg H') :
    G ·g H ≃cg G' ·g H' :=
  isoOfAdj (G := G ·g H) (H := G' ·g H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show (G'.Adj (i x.1) (i y.1) ||
        (decide (i x.1 = i y.1) && H'.Adj (j x.2) (j y.2))) = _
      rw [i.adj_eq, j.adj_eq, show decide (i x.1 = i y.1) = decide (x.1 = y.1) from by simp]
      rfl

/-- The exponential respects isomorphism. -/
@[toIsoGraph]
def exponential (i : G ≃cg G') (j : H ≃cg H') : G ^g H ≃cg G' ^g H' := by
  have key : ∀ (f : H.V → G.V) (u : H.V),
      (Equiv.arrowCongr j.toEquiv i.toEquiv) f (j u) = i (f u) := by
    intro f u
    show i (f (j.toEquiv.symm (j.toEquiv u))) = i (f u)
    rw [Equiv.symm_apply_apply]
  refine isoOfAdj (G := G ^g H) (H := G' ^g H')
    (Equiv.arrowCongr j.toEquiv i.toEquiv) fun f f' ↦ ?_
  rw [exponential_adj, exponential_adj]
  congr 1
  · exact decide_eq_decide.2 (not_congr (Equiv.apply_eq_iff_eq _))
  · refine decide_eq_decide.2 ⟨fun h u v huv ↦ ?_, fun h u v huv ↦ ?_⟩
    · rw [← i.adj_eq, ← key f u, ← key f' v]
      exact h (j u) (j v) (by rw [j.adj_eq]; exact huv)
    · show G'.Adj (i (f (j.symm u))) (i (f' (j.symm v))) = true
      rw [i.adj_eq]
      exact h _ _ (by rw [← j.adj_eq]; simpa using huv)

/-- The reflexive exponential respects isomorphism. -/
@[toIsoGraph]
def homExponential (i : G ≃cg G') (j : H ≃cg H') : G ^hg H ≃cg G' ^hg H' := by
  refine isoOfAdjR (G := G ^hg H) (H := G' ^hg H')
    { toFun := fun f ↦ ⟨fun u ↦ i (f.1 (j.symm u)), fun u v huv ↦ by
        rw [i.adjR_eq]; exact f.2 _ _ (by rwa [j.adjR_symm_eq])⟩
      invFun := fun g ↦ ⟨fun u ↦ i.symm (g.1 (j u)), fun u v huv ↦ by
        rw [i.adjR_symm_eq]; exact g.2 _ _ (by rwa [j.adjR_eq])⟩
      left_inv := fun f ↦ Subtype.ext (funext fun u ↦ by simp)
      right_inv := fun g ↦ Subtype.ext (funext fun u ↦ by simp) } ?_
  intro f f'
  rw [adjR_homExponential, adjR_homExponential, decide_eq_decide]
  constructor
  · intro h u v huv
    have hj := h (j u) (j v) (by rwa [j.adjR_eq])
    simpa [i.adjR_eq] using hj
  · intro h u v huv
    show G'.adjR (i (f.1 (j.symm u))) (i (f'.1 (j.symm v))) = true
    rw [i.adjR_eq]
    exact h _ _ (by rwa [j.adjR_symm_eq])

end

end CGraph.Iso

namespace IsoGraph

/-! ## Notation

One symbol per binary operation, each suffixed with `g` in the style of Mathlib's `⊕g` for
`SimpleGraph.sum` — which stays in scope, and which the overload resolves against by type.  The
same six tokens already stand for the operations on `CGraph`, and are overloaded again here: `G ⊕g
H` is the disjoint union of graphs or of classes according to what `G` and `H` are.  The squared
symbols follow Mathlib's `□` for `SimpleGraph.boxProd`; of the alternative box characters only `□`
(`\square`) has a Lean input abbreviation.  Complementation is the `Compl` instance of
`IsoGraph/Core/Defs.lean` rather than a notation of its own.

The four products bind more tightly than the two sums, and the two exponentials more tightly still
and to the right, so `G ⊕g H □g K ^g L` is `G ⊕g (H □g (K ^g L))`.  Seven of the eight operations
on classes are generated by the `@[toIsoGraph]` attributes above, so their tokens can be declared
here; the join is defined a few lines below, and takes its token there. -/

@[inherit_doc] infixl:60 " ⊕g " => IsoGraph.disjUnion
@[inherit_doc] infixl:70 " □g " => IsoGraph.cartesianProduct
@[inherit_doc] infixl:70 " ⊗g " => IsoGraph.tensorProduct
@[inherit_doc] infixl:70 " ⊠g " => IsoGraph.strongProduct
@[inherit_doc] infixl:70 " ·g " => IsoGraph.lexProduct
@[inherit_doc] infixr:75 " ^g " => IsoGraph.exponential
@[inherit_doc] infixr:75 " ^hg " => IsoGraph.homExponential

/-! ## The join

The one operation here that is not generated.  On both levels the join is a complement of a
disjoint union of complements, so it inherits its well-definedness from the two of them and needs
no `Quotient.lift` of its own — and, more to the point, the identities of
`IsoGraph/SmallGraphs/Identifications.lean` are proved from that definition by `rfl`, which a
lift would not give them.

It comes here, in the middle of the congruences, because the isomorphisms below are transported to
`IsoGraph` by `@[toIsoGraph]`, which can only see through `CGraph.join` once its bridge is in the
`isoTransfer` set. -/

/-- The join of two isomorphism classes: a disjoint union with all edges across. -/
def join (G H : IsoGraph) : IsoGraph := (Gᶜ ⊕g Hᶜ)ᶜ

@[inherit_doc] infixl:60 " ∇g " => IsoGraph.join

/-- The join is a complement of a disjoint union of complements on both levels, so its bridge is
the two others put together. -/
@[simp, isoTransfer] theorem join_mk (G H : CGraph) :
    ⟦G⟧ ∇g ⟦H⟧ = ⟦G ∇g H⟧ := by
  rw [join, compl_mk, compl_mk, disjUnion_mk, compl_mk]
  rfl

isograph_bridge CGraph.join ↦ IsoGraph.join via IsoGraph.join_mk

end IsoGraph

namespace CGraph.Iso

section
variable {G G' H H' : CGraph}

/-! ### Distributivity over disjoint unions

All four products distribute over a disjoint union — the cartesian, tensor and strong products in
either factor (they are commutative), the lexicographic product only in its first.  On vertices
the bijection is `Equiv.prodSumDistrib` (resp. `Equiv.sumProdDistrib`), and adjacency is checked
on each of the four ways of pairing an `inl` with an `inr`. -/

/-- The cartesian product distributes over disjoint unions. -/
@[toIsoGraph simp cartesianProduct_disjUnion]
def cartesianProductDisjUnion (G H K : CGraph)
 :
    G □g (H ⊕g K) ≃cg
      G □g H ⊕g G □g K :=
  isoOfAdj (G := G □g (H ⊕g K))
    (H := G □g H ⊕g G □g K)
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (G □g H ⊕g G □g K).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl]
      · show (G □g H ⊕g G □g K).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (G □g H ⊕g G □g K).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (G □g H ⊕g G □g K).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr])

/-- The tensor product distributes over disjoint unions. -/
@[toIsoGraph simp tensorProduct_disjUnion]
def tensorProductDisjUnion (G H K : CGraph)
 :
    G ⊗g (H ⊕g K) ≃cg
      G ⊗g H ⊕g G ⊗g K :=
  isoOfAdj (G := G ⊗g (H ⊕g K))
    (H := G ⊗g H ⊕g G ⊗g K)
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (G ⊗g H ⊕g G ⊗g K).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (G ⊗g H ⊕g G ⊗g K).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (G ⊗g H ⊕g G ⊗g K).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (G ⊗g H ⊕g G ⊗g K).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp)

/-- The strong product distributes over disjoint unions. -/
@[toIsoGraph simp strongProduct_disjUnion]
def strongProductDisjUnion (G H K : CGraph)
 :
    G ⊠g (H ⊕g K) ≃cg
      G ⊠g H ⊕g G ⊠g K :=
  isoOfAdj (G := G ⊠g (H ⊕g K))
    (H := G ⊠g H ⊕g G ⊠g K)
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (G ⊠g H ⊕g G ⊠g K).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl, Prod.ext_iff]
      · show (G ⊠g H ⊕g G ⊠g K).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (G ⊠g H ⊕g G ⊠g K).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (G ⊠g H ⊕g G ⊠g K).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr, Prod.ext_iff])

/-- The lexicographic product distributes over disjoint unions in its *first* factor.  It does not
distribute in the second: `K₂[K₁ + K₁]` is `K₄`, not `K₂[K₁] + K₂[K₁] = K₂ + K₂`. -/
@[toIsoGraph simp disjUnion_lexProduct]
def lexProductDisjUnion (G H K : CGraph) :
    (G ⊕g H) ·g K ≃cg
      G ·g K ⊕g H ·g K :=
  isoOfAdj (G := (G ⊕g H) ·g K)
    (H := G ·g K ⊕g H ·g K)
    (Equiv.sumProdDistrib G.V H.V K.V) (by
      rintro ⟨(a | a), b⟩ ⟨(c | c), d⟩
      · show (G ·g K ⊕g H ·g K).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl]
      · show (G ·g K ⊕g H ·g K).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (G ·g K ⊕g H ·g K).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (G ·g K ⊕g H ·g K).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr])

/-! ### Units

The graph with no vertices is a unit for the disjoint union and for the join, and the graph with
one vertex is a unit for the cartesian, strong and lexicographic products.  `empty 0` and `empty 1`
rather than `complete 0` and `complete 1`: the two agree, and `complete_zero` and `complete_one`
put the `empty` form in `simp` normal form.  The tensor product has no unit — `G ⊗ K₁` is edgeless
— and the lexicographic product, alone among these, needs both sides. -/

/-- Adding no vertices at all changes nothing. -/
@[toIsoGraph simp disjUnion_empty_zero]
def disjUnionEmptyZero (G : CGraph) : G ⊕g _root_.CGraph.empty 0 ≃cg G :=
  letI : IsEmpty (_root_.CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  isoOfAdj (G := G ⊕g _root_.CGraph.empty 0) (H := G)
    (Equiv.sumEmpty G.V (_root_.CGraph.empty 0).V) (by
      rintro (a | a) (b | b)
      · rfl
      · exact (show Fin 0 from b).elim0
      · exact (show Fin 0 from a).elim0
      · exact (show Fin 0 from a).elim0)

/-- Joining no vertices at all changes nothing. -/
@[toIsoGraph simp join_empty_zero]
def joinEmptyZero (G : CGraph) :
    G ∇g _root_.CGraph.empty 0 ≃cg G :=
  letI : IsEmpty (_root_.CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  isoOfAdj (G := G ∇g _root_.CGraph.empty 0) (H := G)
    (Equiv.sumEmpty G.V (_root_.CGraph.empty 0).V) (by
      rintro (a | a) (b | b)
      · show G.Adj a b = _
        simp
      · exact (show Fin 0 from b).elim0
      · exact (show Fin 0 from a).elim0
      · exact (show Fin 0 from a).elim0)

/-- The one-vertex graph is a unit for the cartesian product. -/
@[toIsoGraph simp cartesianProduct_empty_one]
def cartesianProductEmptyOne (G : CGraph) :
    G □g _root_.CGraph.empty 1 ≃cg G :=
  letI : Unique (_root_.CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  isoOfAdj (G := G □g _root_.CGraph.empty 1) (H := G)
    (Equiv.prodUnique G.V (_root_.CGraph.empty 1).V) fun x y ↦ by
      show G.Adj x.1 y.1 = _
      rw [CGraph.cartesianProduct_adj, Subsingleton.elim x.2 y.2]
      simp

/-- The one-vertex graph is a unit for the strong product. -/
@[toIsoGraph simp strongProduct_empty_one]
def strongProductEmptyOne (G : CGraph) :
    G ⊠g _root_.CGraph.empty 1 ≃cg G :=
  letI : Unique (_root_.CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  isoOfAdj (G := G ⊠g _root_.CGraph.empty 1) (H := G)
    (Equiv.prodUnique G.V (_root_.CGraph.empty 1).V) fun x y ↦ by
      show G.Adj x.1 y.1 = _
      rw [CGraph.strongProduct_adj]
      by_cases hx : x.1 = y.1
      · have hxy : x = y := Prod.ext hx (Subsingleton.elim _ _)
        cases hxy
        simp [(Bool.not_eq_true _).mp (G.loopless x.1)]
      · have hxy : x ≠ y := fun hh ↦ hx (congrArg Prod.fst hh)
        simp [hx, hxy, Subsingleton.elim x.2 y.2]

/-- The one-vertex graph is a right unit for the lexicographic product. -/
@[toIsoGraph simp lexProduct_empty_one]
def lexProductEmptyOne (G : CGraph) :
    G ·g _root_.CGraph.empty 1 ≃cg G :=
  letI : Unique (_root_.CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  isoOfAdj (G := G ·g _root_.CGraph.empty 1) (H := G)
    (Equiv.prodUnique G.V (_root_.CGraph.empty 1).V) fun x y ↦ by
      show G.Adj x.1 y.1 = _
      rw [CGraph.lexProduct_adj]
      simp

/-- The one-vertex graph is a left unit for the lexicographic product. -/
@[toIsoGraph simp empty_one_lexProduct]
def emptyOneLexProduct (G : CGraph) :
    _root_.CGraph.empty 1 ·g G ≃cg G :=
  letI : Unique (_root_.CGraph.empty 1).V := inferInstanceAs (Unique (Fin 1))
  isoOfAdj (G := _root_.CGraph.empty 1 ·g G) (H := G)
    (Equiv.uniqueProd G.V (_root_.CGraph.empty 1).V) fun x y ↦ by
      show G.Adj x.2 y.2 = _
      rw [CGraph.lexProduct_adj, Subsingleton.elim x.1 y.1]
      simp

/-! ### Line graphs and Mycielskians

Two more unary constructions.  The line graph transports along `SimpleGraph.Iso.mapEdgeSet`, and
the Mycielskian along the same bijection applied to the original vertices, their shadows and the
apex. -/

/-- The Mycielskian respects isomorphism. -/
@[toIsoGraph]
def mycielskian (i : G ≃cg G') :
    CGraph.mycielskian G ≃cg CGraph.mycielskian G' :=
  isoOfAdj (G := CGraph.mycielskian G) (H := CGraph.mycielskian G')
    (Equiv.optionCongr (Equiv.sumCongr i.toEquiv i.toEquiv)) fun x y ↦ by
      rcases x with _ | (a | a) <;> rcases y with _ | (b | b) <;>
        first
          | rfl
          | exact i.adj_eq a b

/-- The line graph respects isomorphism: an isomorphism carries edges to edges, and two edges
meet exactly when their images do. -/
@[toIsoGraph]
def lineGraph (i : G ≃cg G') :
    CGraph.lineGraph G ≃cg CGraph.lineGraph G' :=
  isoOfAdj (G := CGraph.lineGraph G) (H := CGraph.lineGraph G')
    i.toSimpleIso.mapEdgeSet fun e f ↦ by
      have hcoe : ∀ e : (CGraph.lineGraph G).V,
          ((i.toSimpleIso.mapEdgeSet e).1 : Sym2 G'.V) = Sym2.map (fun v ↦ i v) e.1 :=
        fun _ ↦ rfl
      show (decide (i.toSimpleIso.mapEdgeSet e ≠ i.toSimpleIso.mapEdgeSet f) &&
        decide (∃ v, v ∈ ((i.toSimpleIso.mapEdgeSet e).1 : Sym2 G'.V) ∧
          v ∈ ((i.toSimpleIso.mapEdgeSet f).1 : Sym2 G'.V))) = _
      rw [CGraph.lineGraph_adj, hcoe e, hcoe f]
      congr 1
      · exact decide_eq_decide.2 (not_congr (EmbeddingLike.apply_eq_iff_eq _))
      · refine decide_eq_decide.2 ⟨?_, ?_⟩
        · rintro ⟨v, hv1, hv2⟩
          rw [Sym2.mem_map] at hv1 hv2
          obtain ⟨a, ha, rfl⟩ := hv1
          obtain ⟨b, hb, hab⟩ := hv2
          refine ⟨a, ha, ?_⟩
          have hba : b = a := i.toEquiv.injective hab
          rwa [hba] at hb
        · rintro ⟨v, hv1, hv2⟩
          exact ⟨i v, Sym2.mem_map.2 ⟨v, hv1, rfl⟩, Sym2.mem_map.2 ⟨v, hv2, rfl⟩⟩

-- the vertex type here is a subtype of `Sym2` of a sum, so every `Fintype` instance in sight is a

-- tower the elaborator has to unfold to check the four `show`s below against

/-! ### Disjoint unions of families -/

/-- A `sigmaUnion` over `Fin (n + 1)` is the disjoint union of its first fibre with the
`sigmaUnion` of the rest. -/
def sigmaUnionSucc {n : ℕ} (F : Fin (n + 1) → CGraph) :
    sigmaUnion F ≃cg F 0 ⊕g (sigmaUnion fun i : Fin n ↦ F i.succ) :=
  isoOfAdj (G := sigmaUnion F)
    (H := F 0 ⊕g (sigmaUnion fun i : Fin n ↦ F i.succ))
    (sigmaFinSuccEquiv fun i ↦ (F i).V) (by
      rintro ⟨i, a⟩ ⟨j, b⟩
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (sigmaUnion_adj_mk F 0 a b).symm
        | succ j => exact (sigmaUnion_adj_ne F _ _ a b (Fin.succ_ne_zero j).symm).symm
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (sigmaUnion_adj_ne F _ _ a b (Fin.succ_ne_zero i)).symm
        | succ j =>
          by_cases h : i = j
          · subst h
            show (sigmaUnion fun i : Fin n ↦ F i.succ).Adj ⟨i, a⟩ ⟨i, b⟩ = _
            rw [sigmaUnion_adj_mk, sigmaUnion_adj_mk]
          · show (sigmaUnion fun i : Fin n ↦ F i.succ).Adj ⟨i, a⟩ ⟨j, b⟩ = _
            rw [sigmaUnion_adj_ne _ _ _ _ _ h,
              sigmaUnion_adj_ne F _ _ a b (fun hh ↦ h (Fin.succ_injective n hh))])

/-! ### Blow-ups, and Johnson duality -/

/-- **`(G[H])ᶜ = Gᶜ[Hᶜ]`**: of the four products, the lexicographic one is the only whose
complement is again a product — of the complements.  Two pairs are non-adjacent in
`G[H]` exactly when the first coordinates are non-adjacent, or equal with the second coordinates
non-adjacent. -/
@[toIsoGraph simp compl_lexProduct]
def complLexProduct (G H : CGraph) :
    (G ·g H)ᶜ ≃cg Gᶜ ·g Hᶜ :=
  isoOfAdj (G := (G ·g H)ᶜ)
    (H := Gᶜ ·g Hᶜ) (Equiv.refl (G.V × H.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (Gᶜ ·g Hᶜ).Adj (a, b) (c, d)
        = ((G ·g H)ᶜ).Adj (a, b) (c, d)
      rcases eq_or_ne a c with rfl | hac
      · simp [Bool.eq_false_iff.2 (G.loopless a), lexProduct_pair_eq]
      · simp [hac, lexProduct_pair_eq])

/-- **`(empty n)[G] = (empty n) □ G`**: with an edgeless first factor, both products are `n`
disjoint copies of `G`. -/
@[toIsoGraph empty_lexProduct]
def emptyLexProduct (n : ℕ) (G : CGraph) :
    CGraph.empty n ·g G ≃cg CGraph.empty n □g G :=
  isoOfAdj (G := CGraph.empty n ·g G)
    (H := CGraph.empty n □g G) (Equiv.refl ((CGraph.empty n).V × G.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (CGraph.empty n □g G).Adj (a, b) (c, d)
        = (CGraph.empty n ·g G).Adj (a, b) (c, d)
      simp)

/-- **`(empty n) ⊠ G = (empty n) □ G`**: likewise for the strong product.  Only the tensor
product breaks ranks here — with an edgeless factor it is edgeless. -/
@[toIsoGraph empty_strongProduct]
def emptyStrongProduct (n : ℕ) (G : CGraph) :
    CGraph.empty n ⊠g G ≃cg CGraph.empty n □g G :=
  isoOfAdj (G := CGraph.empty n ⊠g G)
    (H := CGraph.empty n □g G) (Equiv.refl ((CGraph.empty n).V × G.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (CGraph.empty n □g G).Adj (a, b) (c, d)
        = (CGraph.empty n ⊠g G).Adj (a, b) (c, d)
      rcases eq_or_ne a c with rfl | hac
      · rcases eq_or_ne b d with rfl | hbd
        · simp [Bool.eq_false_iff.2 (G.loopless b)]
        · simp [hbd]
      · simp [hac])

/-- **`J(n, k) ≅ J(n, n - k)`**: complementing every set turns an intersection of size `k - 1`
into one of size `(n - k) - 1`, since `|sᶜ ∩ tᶜ| = n - |s ∪ t|` and `|s ∪ t| = 2k - |s ∩ t|`.

The arithmetic is truncated subtraction throughout, which is why the two sets have to be distinct
before `omega` will believe it: `s = t` forces `|s ∩ t| = k`, and then both `k - 1` tests fail for
the wrong reason. -/
@[toIsoGraph johnson_compl]
def johnsonCompl (n k : ℕ) (hk : k ≤ n) :
    CGraph.johnson n k ≃cg CGraph.johnson n (n - k) :=
  isoOfAdj (G := CGraph.johnson n k) (H := CGraph.johnson n (n - k)) (complSubsets n k hk) (by
    intro s t
    rw [CGraph.johnson_adj, CGraph.johnson_adj]
    have key : s ≠ t →
        ((((complSubsets n k hk) s).1 ∩ ((complSubsets n k hk) t).1).card = n - k - 1
          ↔ (s.1 ∩ t.1).card = k - 1) := by
      intro hst
      show ((s.1ᶜ ∩ t.1ᶜ).card = n - k - 1) ↔ _
      have hclt : (s.1 ∩ t.1).card < k := by
        refine lt_of_le_of_ne (by
          have h := Finset.card_le_card (Finset.inter_subset_left (s₁ := s.1) (s₂ := t.1))
          have h' := s.2
          omega) fun h ↦ hst ?_
        have h1 : s.1 ∩ t.1 = s.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [s.2, h])
        have h2 : s.1 ∩ t.1 = t.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [t.2, h])
        exact Subtype.ext (h1.symm.trans h2)
      have hcompl : (s.1ᶜ ∩ t.1ᶜ).card = n - (s.1 ∪ t.1).card := by
        rw [← Finset.compl_union, Finset.card_compl, Fintype.card_fin]
      have hU : (s.1 ∪ t.1).card + (s.1 ∩ t.1).card = k + k := by
        rw [Finset.card_union_add_card_inter, s.2, t.2]
      have hUn : (s.1 ∪ t.1).card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      rw [hcompl]
      omega
    refine Bool.eq_iff_iff.2 ?_
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hst : s ≠ t := fun h ↦ h1 (congrArg (complSubsets n k hk) h)
      exact ⟨hst, (key hst).1 h2⟩
    · rintro ⟨hst, h2⟩
      exact ⟨fun h ↦ hst ((complSubsets n k hk).injective h), (key hst).2 h2⟩)

/-! ### Paley graphs -/

/-- The three residue classes mod `3`, which are the parts of the (degenerate) `paley 9`. -/
private def paleyNineMap : Fin 3 ⊕ Fin 3 ⊕ Fin 3 → (CGraph.paley 9).V
  | .inl i => ⟨3 * i.1, by omega⟩
  | .inr (.inl i) => ⟨3 * i.1 + 1, by omega⟩
  | .inr (.inr i) => ⟨3 * i.1 + 2, by omega⟩

/-- Which residue class mod `3` a vertex of `paley 9` lies in: the inverse of `paleyNineMap`. -/
private def paleyNineClass : (CGraph.paley 9).V → Fin 3 ⊕ Fin 3 ⊕ Fin 3 :=
  ![.inl 0, .inr (.inl 0), .inr (.inr 0), .inl 1, .inr (.inl 1), .inr (.inr 1),
    .inl 2, .inr (.inl 2), .inr (.inr 2)]

private def paleyNineEquiv : (CGraph.paley 9).V ≃ (Fin 3 ⊕ Fin 3 ⊕ Fin 3) where
  toFun := paleyNineClass
  invFun := paleyNineMap
  left_inv := by decide
  right_inv := by decide

/-- `paley 9` is `K₃,₃,₃`: its complement is three triangles, the residue classes mod `3`.
(Nine is not prime, so this is not an instance of `Iso.complPaleyOfNotIsSquare`.) -/
def complPaleyNine :
    (CGraph.paley 9)ᶜ ≃cg CGraph.complete 3 ⊕g (CGraph.complete 3 ⊕g CGraph.complete 3) :=
  isoOfAdj (G := (CGraph.paley 9)ᶜ)
    (H := CGraph.complete 3 ⊕g (CGraph.complete 3 ⊕g CGraph.complete 3))
    paleyNineEquiv (by decide)

end

end CGraph.Iso

namespace IsoGraph

/-! ## Abbreviations

Exactly as on `CGraph`: these are notation for the constructions above, not new definitions. -/

/-- The book graph with `n` pages. -/
abbrev book (n : ℕ) : IsoGraph := completeMultipartite [1, 1, n]

/-- The fan graph on a path of `n` vertices. -/
abbrev fan (n : ℕ) : IsoGraph := complete 1 ∇g path n

/-- The `n`-rung ladder. -/
abbrev ladder (n : ℕ) : IsoGraph := path n □g complete 2

/-- The `n`-gonal prism. -/
abbrev prism (n : ℕ) : IsoGraph := cycle n □g complete 2

/-- The triangular graph `T(n)`. -/
abbrev triangular (n : ℕ) : IsoGraph := johnson n 2

/-- The `m × n` rook's graph. -/
abbrev rook (m n : ℕ) : IsoGraph := complete m □g complete n

/-- The cocktail party graph on `n` pairs. -/
abbrev cocktailParty (n : ℕ) : IsoGraph := completeMultipartite (List.replicate n 2)

/-- The Petersen graph, as the Kneser graph on the 2-subsets of a 5-set. -/
abbrev petersen : IsoGraph := kneser 5 2

/-- The Turán graph `T(n, r)`: the complete multipartite graph whose `r` parts are as equal as
possible and hold `n` vertices in total. -/
abbrev turan (n r : ℕ) : IsoGraph :=
  completeMultipartite (List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r))

/-- The friendship (windmill) graph `F_n`: `n` triangles glued at a common vertex. -/
abbrev friendship (n : ℕ) : IsoGraph :=
  complete 1 ∇g (empty n □g complete 2)

/-- The crown graph `S_n`: the complete bipartite graph `K_{n,n}` with a perfect matching
removed, equivalently the bipartite double cover of `K_n`. -/
abbrev crown (n : ℕ) : IsoGraph := complete n ⊗g complete 2

/-! ## Two odds and ends

Everything else on this page is generated: `@[toIsoGraph]` on a construction produces the
construction on classes and the bridge to it, and `@[toIsoGraph]` on one of the congruences above
produces the `Quotient.lift` along it.  These two are what is left over — the vertex count, whose
`CGraph`-level side is a `Fintype.card` rather than a construction, and the fact that
canonicalising does not change the class. -/

@[simp, isoTransfer] theorem V_mk (G : CGraph) : IsoGraph.V ⟦G⟧ = FinEnum.card G.V := rfl

isograph_bridge CGraph.V ↦ IsoGraph.V via IsoGraph.V_mk

/-- A graph and its canonical representative are the same isomorphism class. -/
theorem mk_canonicalize (G : CGraph) : (⟦G.canonicalize⟧ : IsoGraph) = ⟦G⟧ :=
  Quotient.sound ⟨G.isoCanonicalize.symm⟩

end IsoGraph
