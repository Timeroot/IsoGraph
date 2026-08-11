import IsoGraph.Graphs.Constructions

/-!
# The constructions, on isomorphism classes

`IsoGraph/Graphs/Constructions.lean` builds graphs as `CGraph`s: concrete data, with a concrete
vertex type.  This file carries each of those constructions across to `IsoGraph`, the quotient by
isomorphism, so that the tables of `IsoGraph/Values/Identities.lean` can be stated there.

## Lifting a construction

Every construction with no arguments — `empty`, `complete`, `kneser`, … — lifts by definition:
`IsoGraph.complete n` is just `⟦CGraph.complete n⟧`.  The unary and binary ones need more care,
because most of them ask for a `DecidableEq` on the vertex type and a bare `CGraph` does not
supply one.  Two ways out:

* `disjUnion` needs no `DecidableEq`, so it lifts through `Quotient.lift₂` directly, and
  `disjUnion_mk` is `rfl`;
* the rest are applied to `G.canonicalize`, whose vertex type is `Fin (Fintype.card G.V)` — and
  so has a `DecidableEq` — before descending.  The construction stays computable, and the price
  is that `compl_mk` and friends are not `rfl`.

Either way the side condition of the lift is an isomorphism-congruence: `CGraph.Iso.compl`,
`CGraph.Iso.cartesianProduct`, … in the first section, each built from `CGraph.isoOfAdj`.

`join` needs no lift of its own: it is `compl (disjUnion (compl G) (compl H))` on `IsoGraph` just
as on `CGraph`, so well-definedness is inherited.

The first section is more than the congruences the lifts need: it is every isomorphism between
concrete graphs that `IsoGraph/Values/Identities.lean` goes on to read as an equation of isomorphism
classes — associativity and distributivity of the products, blow-ups, bipartite double covers,
the Paley graphs.  They live here because they are constructions, not facts about invariants.
-/

set_option autoImplicit false

namespace CGraph

/-! ## Isomorphism congruences

Each construction below has to be shown to respect isomorphism before it can be lifted to the
quotient.  All of them are the same shape — a bijection of vertices that carries adjacency to
adjacency — so they are all built from `isoOfAdj`.
-/

/-- Build an isomorphism out of a bijection of vertices that carries adjacency to adjacency on
the nose.  For two concrete small graphs the hypothesis is a `decide`. -/
def isoOfAdj {G H : CGraph} (e : G.V ≃ H.V) (h : ∀ x y, H.Adj (e x) (e y) = G.Adj x y) :
    G ≃cg H := ⟨e, fun {a b} ↦ by rw [h]⟩

@[simp] theorem isoOfAdj_apply {G H : CGraph} (e : G.V ≃ H.V)
    (h : ∀ x y, H.Adj (e x) (e y) = G.Adj x y) (x : G.V) : isoOfAdj e h x = e x := rfl

/-- The canonical representative has `Fin n` for its vertex type, so it has a `DecidableEq`.
This is what makes the lifts below computable. -/
instance instDecidableEqCanonicalizeV (G : CGraph) : DecidableEq G.canonicalize.V :=
  inferInstanceAs (DecidableEq (Fin (Fintype.card G.V)))

/-- Equality of pairs, as a `Bool`: it splits into the two component tests. -/
theorem decide_prod_eq {α β : Type} [DecidableEq α] [DecidableEq β] (p q : α × β) :
    decide (p = q) = (decide (p.1 = q.1) && decide (p.2 = q.2)) :=
  (decide_eq_decide.2 Prod.ext_iff).trans (Bool.decide_and _ _)

/-- Injectivity of `Sum.inl`, stated at the vertex type of a `disjUnion` rather than at a bare
`⊕`.  The two are definitionally equal but not *reducibly* so, and `simp` matches up to reducible
unfolding only — so `Sum.inl.injEq` does not fire on a goal about `(disjUnion G H).V`. -/
theorem disjUnion_inl_eq_inl (G H : CGraph) (a b : G.V) :
    (@Eq (disjUnion G H).V (Sum.inl a) (Sum.inl b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inl_injective h, fun h ↦ h ▸ rfl⟩

/-- Injectivity of `Sum.inr` at the vertex type of a `disjUnion`; see `disjUnion_inl_eq_inl`. -/
theorem disjUnion_inr_eq_inr (G H : CGraph) (a b : H.V) :
    (@Eq (disjUnion G H).V (Sum.inr a) (Sum.inr b)) = (a = b) :=
  propext ⟨fun h ↦ Sum.inr_injective h, fun h ↦ h ▸ rfl⟩

/-- `Prod.mk.injEq`, restated at the vertex type of a `lexProduct`.  Same reducibility gap as
`disjUnion_inl_eq_inl`: the pair equality that `compl` puts in front of a product adjacency lives
at `(lexProduct G H).V`, and `simp` will not see it as an equality of pairs. -/
theorem lexProduct_pair_eq (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a c : G.V) (b d : H.V) :
    (@Eq (lexProduct G H).V (a, b) (c, d)) = (a = c ∧ b = d) :=
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

/-- The successor relation of a cycle, with the wrap-around split off.  `omega` cannot see through
a `%` whose modulus is a variable, so every step around a `cycle n` is turned into this
disjunction before the arithmetic starts. -/
theorem succ_mod_eq_iff {d x y : ℕ} (hx : x < d) :
    (x + 1) % d = y ↔ (x + 1 = d ∧ y = 0) ∨ (x + 1 < d ∧ y = x + 1) := by
  rcases Nat.lt_or_ge (x + 1) d with h | h
  · rw [Nat.mod_eq_of_lt h]
    constructor
    · rintro rfl; exact Or.inr ⟨h, rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨-, h2⟩) <;> omega
  · have hd : x + 1 = d := by omega
    rw [hd, Nat.mod_self]
    constructor
    · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩) <;> omega

/-- Reduction mod `d` below `2 * d`, again as a disjunction `omega` can use. -/
theorem mod_of_lt_two_mul {d x : ℕ} (hx : x < 2 * d) :
    (x < d ∧ x % d = x) ∨ (d ≤ x ∧ x % d = x - d) := by
  rcases Nat.lt_or_ge x d with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- The difference `y - x` around a cycle of length `d`, again as a disjunction: `(y + d - x) % d`
is `y - x` going forwards and `d - (x - y)` going backwards.  This is the third member of the
`succ_mod_eq_iff` / `mod_of_lt_two_mul` family of "`omega` cannot divide" workarounds, and it is
what makes circulant differences tractable. -/
theorem sub_mod_cases {d x y : ℕ} (hx : x < d) (hy : y < d) :
    (x ≤ y ∧ (y + d - x) % d = y - x) ∨ (y < x ∧ (y + d - x) % d = d - (x - y)) := by
  rcases Nat.lt_or_ge y x with h | h
  · refine Or.inr ⟨h, ?_⟩
    rw [show y + d - x = d - (x - y) by omega, Nat.mod_eq_of_lt (by omega)]
  · refine Or.inl ⟨h, ?_⟩
    rw [show y + d - x = (y - x) + d by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

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
    Sym2.map Sum.inl e ∈ (disjUnion G H).toSimple.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
    rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, disjUnion_adj_inl_inl]
    exact he

/-- Pushing an edge of `H` forward into `G + H` gives an edge of `G + H`. -/
private theorem mem_edgeSet_map_inr (G H : CGraph) (e : Sym2 H.V)
    (he : e ∈ H.toSimple.edgeSet) :
    Sym2.map Sum.inr e ∈ (disjUnion G H).toSimple.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj] at he
    rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, disjUnion_adj_inr_inr]
    exact he

/-- An edge of `G` or an edge of `H`, read as an edge of `G + H`.  It is onto because the two
sides have the same number of edges, so `lineGraphDisjUnion` never has to name an inverse. -/
private def sumEdge (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (lineGraph G).V ⊕ (lineGraph H).V → (lineGraph (disjUnion G H)).V
  | .inl e => ⟨Sym2.map Sum.inl e.1, mem_edgeSet_map_inl G H e.1 e.2⟩
  | .inr e => ⟨Sym2.map Sum.inr e.1, mem_edgeSet_map_inr G H e.1 e.2⟩

private theorem sumEdge_inj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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

namespace Iso

variable {G G' H H' : CGraph}

/-- Complementation respects isomorphism. -/
def compl [DecidableEq G.V] [DecidableEq G'.V] (i : G ≃cg G') :
    CGraph.compl G ≃cg CGraph.compl G' :=
  isoOfAdj (G := CGraph.compl G) (H := CGraph.compl G') i.toEquiv fun x y ↦ by
    show (decide (i x ≠ i y) && !G'.Adj (i x) (i y)) = (decide (x ≠ y) && !G.Adj x y)
    rw [i.adj_eq, show decide (i x ≠ i y) = decide (x ≠ y) from by simp]

/-- Disjoint union respects isomorphism. -/
def disjUnion (i : G ≃cg G') (j : H ≃cg H') :
    CGraph.disjUnion G H ≃cg CGraph.disjUnion G' H' :=
  isoOfAdj (G := CGraph.disjUnion G H) (H := CGraph.disjUnion G' H')
    (Equiv.sumCongr i.toEquiv j.toEquiv) fun x y ↦ by
      rcases x with a | b <;> rcases y with c | d
      · show (CGraph.disjUnion G' H').Adj (.inl (i a)) (.inl (i c)) = _
        rw [disjUnion_adj_inl_inl, i.adj_eq]; rfl
      · show (CGraph.disjUnion G' H').Adj (.inl (i a)) (.inr (j d)) = _
        rfl
      · show (CGraph.disjUnion G' H').Adj (.inr (j b)) (.inl (i c)) = _
        rfl
      · show (CGraph.disjUnion G' H').Adj (.inr (j b)) (.inr (j d)) = _
        rw [disjUnion_adj_inr_inr, j.adj_eq]; rfl

/-- The join respects isomorphism; it is a complement of a disjoint union of complements. -/
def join [DecidableEq G.V] [DecidableEq G'.V] [DecidableEq H.V] [DecidableEq H'.V]
    (i : G ≃cg G') (j : H ≃cg H') : CGraph.join G H ≃cg CGraph.join G' H' :=
  Iso.compl (Iso.disjUnion (Iso.compl i) (Iso.compl j))

/-- The cartesian product respects isomorphism. -/
def cartesianProduct [DecidableEq G.V] [DecidableEq G'.V] [DecidableEq H.V] [DecidableEq H'.V]
    (i : G ≃cg G') (j : H ≃cg H') :
    CGraph.cartesianProduct G H ≃cg CGraph.cartesianProduct G' H' :=
  isoOfAdj (G := CGraph.cartesianProduct G H) (H := CGraph.cartesianProduct G' H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show ((decide (i x.1 = i y.1) && H'.Adj (j x.2) (j y.2)) ||
        (G'.Adj (i x.1) (i y.1) && decide (j x.2 = j y.2))) = _
      rw [i.adj_eq, j.adj_eq, show decide (i x.1 = i y.1) = decide (x.1 = y.1) from by simp,
        show decide (j x.2 = j y.2) = decide (x.2 = y.2) from by simp]
      rfl

/-- The tensor product respects isomorphism. -/
def tensorProduct [DecidableEq G.V] [DecidableEq G'.V] [DecidableEq H.V] [DecidableEq H'.V]
    (i : G ≃cg G') (j : H ≃cg H') :
    CGraph.tensorProduct G H ≃cg CGraph.tensorProduct G' H' :=
  isoOfAdj (G := CGraph.tensorProduct G H) (H := CGraph.tensorProduct G' H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show (G'.Adj (i x.1) (i y.1) && H'.Adj (j x.2) (j y.2)) = _
      rw [i.adj_eq, j.adj_eq]
      rfl

/-- The strong product respects isomorphism. -/
def strongProduct [DecidableEq G.V] [DecidableEq G'.V] [DecidableEq H.V] [DecidableEq H'.V]
    (i : G ≃cg G') (j : H ≃cg H') :
    CGraph.strongProduct G H ≃cg CGraph.strongProduct G' H' :=
  isoOfAdj (G := CGraph.strongProduct G H) (H := CGraph.strongProduct G' H')
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
def lexProduct [DecidableEq G.V] [DecidableEq G'.V] [DecidableEq H.V] [DecidableEq H'.V]
    (i : G ≃cg G') (j : H ≃cg H') :
    CGraph.lexProduct G H ≃cg CGraph.lexProduct G' H' :=
  isoOfAdj (G := CGraph.lexProduct G H) (H := CGraph.lexProduct G' H')
    (Equiv.prodCongr i.toEquiv j.toEquiv) fun x y ↦ by
      show (G'.Adj (i x.1) (i y.1) ||
        (decide (i x.1 = i y.1) && H'.Adj (j x.2) (j y.2))) = _
      rw [i.adj_eq, j.adj_eq, show decide (i x.1 = i y.1) = decide (x.1 = y.1) from by simp]
      rfl

/-- The cartesian product is commutative. -/
def cartesianProductComm (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    CGraph.cartesianProduct G H ≃cg CGraph.cartesianProduct H G :=
  isoOfAdj (G := CGraph.cartesianProduct G H) (H := CGraph.cartesianProduct H G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show ((decide (x.2 = y.2) && G.Adj x.1 y.1) || (H.Adj x.2 y.2 && decide (x.1 = y.1))) = _
      rw [CGraph.cartesianProduct_adj]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      generalize decide (x.1 = y.1) = c
      generalize decide (x.2 = y.2) = d
      revert a b c d
      decide

/-- The tensor product is commutative. -/
def tensorProductComm (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    CGraph.tensorProduct G H ≃cg CGraph.tensorProduct H G :=
  isoOfAdj (G := CGraph.tensorProduct G H) (H := CGraph.tensorProduct H G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show (H.Adj x.2 y.2 && G.Adj x.1 y.1) = _
      rw [CGraph.tensorProduct_adj]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      revert a b
      decide

/-- The strong product is commutative. -/
def strongProductComm (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    CGraph.strongProduct G H ≃cg CGraph.strongProduct H G :=
  isoOfAdj (G := CGraph.strongProduct G H) (H := CGraph.strongProduct H G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show (decide ((x.2, x.1) ≠ (y.2, y.1)) &&
        ((decide (x.2 = y.2) || H.Adj x.2 y.2) && (decide (x.1 = y.1) || G.Adj x.1 y.1))) = _
      rw [CGraph.strongProduct_adj,
        show decide ((x.2, x.1) ≠ (y.2, y.1)) = decide (x ≠ y) from
          decide_eq_decide.2 (not_congr (by
            simp only [Prod.ext_iff]
            exact and_comm.trans (Prod.ext_iff (x := (x : G.V × H.V)) (y := y)).symm))]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      generalize decide (x.1 = y.1) = c
      generalize decide (x.2 = y.2) = d
      generalize decide (x ≠ y) = e
      revert a b c d e
      decide

/-! ### Associativity

All four products are associative, and all four proofs are the same: `Equiv.prodAssoc` on the
vertices, `decide_prod_eq` to break the equality tests on pairs apart, and `decide` on the
resulting identity between two Boolean expressions in six variables. -/

/-- The cartesian product is associative. -/
def cartesianProductAssoc (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [DecidableEq K.V] :
    CGraph.cartesianProduct (CGraph.cartesianProduct G H) K ≃cg
      CGraph.cartesianProduct G (CGraph.cartesianProduct H K) :=
  isoOfAdj (G := CGraph.cartesianProduct (CGraph.cartesianProduct G H) K)
    (H := CGraph.cartesianProduct G (CGraph.cartesianProduct H K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show ((decide (x.1.1 = y.1.1) &&
          (CGraph.cartesianProduct H K).Adj (x.1.2, x.2) (y.1.2, y.2)) ||
        (G.Adj x.1.1 y.1.1 && decide (((x.1.2, x.2) : H.V × K.V) = (y.1.2, y.2)))) = _
      rw [CGraph.cartesianProduct_adj, CGraph.cartesianProduct_adj, CGraph.cartesianProduct_adj,
        decide_prod_eq ((x.1.2, x.2) : H.V × K.V), decide_prod_eq x.1 y.1]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      generalize decide (x.2 = y.2) = c
      revert p q r a b c
      decide

/-- The tensor product is associative. -/
def tensorProductAssoc (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V] [DecidableEq K.V] :
    CGraph.tensorProduct (CGraph.tensorProduct G H) K ≃cg
      CGraph.tensorProduct G (CGraph.tensorProduct H K) :=
  isoOfAdj (G := CGraph.tensorProduct (CGraph.tensorProduct G H) K)
    (H := CGraph.tensorProduct G (CGraph.tensorProduct H K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (G.Adj x.1.1 y.1.1 && (CGraph.tensorProduct H K).Adj (x.1.2, x.2) (y.1.2, y.2)) = _
      rw [CGraph.tensorProduct_adj, CGraph.tensorProduct_adj, CGraph.tensorProduct_adj]
      exact (Bool.and_assoc _ _ _).symm

/-- The lexicographic product is associative. -/
def lexProductAssoc (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V] [DecidableEq K.V] :
    CGraph.lexProduct (CGraph.lexProduct G H) K ≃cg
      CGraph.lexProduct G (CGraph.lexProduct H K) :=
  isoOfAdj (G := CGraph.lexProduct (CGraph.lexProduct G H) K)
    (H := CGraph.lexProduct G (CGraph.lexProduct H K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (G.Adj x.1.1 y.1.1 || (decide (x.1.1 = y.1.1) &&
        (CGraph.lexProduct H K).Adj (x.1.2, x.2) (y.1.2, y.2))) = _
      rw [CGraph.lexProduct_adj, CGraph.lexProduct_adj, CGraph.lexProduct_adj,
        decide_prod_eq x.1 y.1]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      revert p q r a b
      decide

/-- The strong product is associative. -/
def strongProductAssoc (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V] [DecidableEq K.V] :
    CGraph.strongProduct (CGraph.strongProduct G H) K ≃cg
      CGraph.strongProduct G (CGraph.strongProduct H K) :=
  isoOfAdj (G := CGraph.strongProduct (CGraph.strongProduct G H) K)
    (H := CGraph.strongProduct G (CGraph.strongProduct H K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (decide (((x.1.1, x.1.2, x.2) : G.V × H.V × K.V) ≠ (y.1.1, y.1.2, y.2)) &&
        ((decide (x.1.1 = y.1.1) || G.Adj x.1.1 y.1.1) &&
          (decide (((x.1.2, x.2) : H.V × K.V) = (y.1.2, y.2)) ||
            (CGraph.strongProduct H K).Adj (x.1.2, x.2) (y.1.2, y.2)))) = _
      simp only [CGraph.strongProduct_adj, decide_not, decide_prod_eq]
      rw [show decide (x.1 = y.1)
          = (decide (x.1.1 = y.1.1) && decide (x.1.2 = y.1.2)) from decide_prod_eq _ _]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      generalize decide (x.2 = y.2) = c
      revert p q r a b c
      decide

/-! ### Distributivity over disjoint unions

All four products distribute over a disjoint union — the cartesian, tensor and strong products in
either factor (they are commutative), the lexicographic product only in its first.  On vertices
the bijection is `Equiv.prodSumDistrib` (resp. `Equiv.sumProdDistrib`), and adjacency is checked
on each of the four ways of pairing an `inl` with an `inr`. -/

/-- The cartesian product distributes over disjoint unions. -/
def cartesianProductDisjUnion (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [DecidableEq K.V] :
    CGraph.cartesianProduct G (_root_.CGraph.disjUnion H K) ≃cg
      _root_.CGraph.disjUnion (CGraph.cartesianProduct G H) (CGraph.cartesianProduct G K) :=
  isoOfAdj (G := CGraph.cartesianProduct G (_root_.CGraph.disjUnion H K))
    (H := _root_.CGraph.disjUnion (CGraph.cartesianProduct G H) (CGraph.cartesianProduct G K))
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (_root_.CGraph.disjUnion (CGraph.cartesianProduct G H)
          (CGraph.cartesianProduct G K)).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl]
      · show (_root_.CGraph.disjUnion (CGraph.cartesianProduct G H)
          (CGraph.cartesianProduct G K)).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.cartesianProduct G H)
          (CGraph.cartesianProduct G K)).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.cartesianProduct G H)
          (CGraph.cartesianProduct G K)).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr])

/-- The tensor product distributes over disjoint unions. -/
def tensorProductDisjUnion (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [DecidableEq K.V] :
    CGraph.tensorProduct G (_root_.CGraph.disjUnion H K) ≃cg
      _root_.CGraph.disjUnion (CGraph.tensorProduct G H) (CGraph.tensorProduct G K) :=
  isoOfAdj (G := CGraph.tensorProduct G (_root_.CGraph.disjUnion H K))
    (H := _root_.CGraph.disjUnion (CGraph.tensorProduct G H) (CGraph.tensorProduct G K))
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (_root_.CGraph.disjUnion (CGraph.tensorProduct G H)
          (CGraph.tensorProduct G K)).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.tensorProduct G H)
          (CGraph.tensorProduct G K)).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.tensorProduct G H)
          (CGraph.tensorProduct G K)).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.tensorProduct G H)
          (CGraph.tensorProduct G K)).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp)

/-- The strong product distributes over disjoint unions. -/
def strongProductDisjUnion (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [DecidableEq K.V] :
    CGraph.strongProduct G (_root_.CGraph.disjUnion H K) ≃cg
      _root_.CGraph.disjUnion (CGraph.strongProduct G H) (CGraph.strongProduct G K) :=
  isoOfAdj (G := CGraph.strongProduct G (_root_.CGraph.disjUnion H K))
    (H := _root_.CGraph.disjUnion (CGraph.strongProduct G H) (CGraph.strongProduct G K))
    (Equiv.prodSumDistrib G.V H.V K.V) (by
      rintro ⟨a, (b | b)⟩ ⟨c, (d | d)⟩
      · show (_root_.CGraph.disjUnion (CGraph.strongProduct G H)
          (CGraph.strongProduct G K)).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl, Prod.ext_iff]
      · show (_root_.CGraph.disjUnion (CGraph.strongProduct G H)
          (CGraph.strongProduct G K)).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.strongProduct G H)
          (CGraph.strongProduct G K)).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.strongProduct G H)
          (CGraph.strongProduct G K)).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr, Prod.ext_iff])

/-- The lexicographic product distributes over disjoint unions in its *first* factor.  It does not
distribute in the second: `K₂[K₁ + K₁]` is `K₄`, not `K₂[K₁] + K₂[K₁] = K₂ + K₂`. -/
def lexProductDisjUnion (G H K : CGraph) [DecidableEq G.V] [DecidableEq H.V] [DecidableEq K.V] :
    CGraph.lexProduct (_root_.CGraph.disjUnion G H) K ≃cg
      _root_.CGraph.disjUnion (CGraph.lexProduct G K) (CGraph.lexProduct H K) :=
  isoOfAdj (G := CGraph.lexProduct (_root_.CGraph.disjUnion G H) K)
    (H := _root_.CGraph.disjUnion (CGraph.lexProduct G K) (CGraph.lexProduct H K))
    (Equiv.sumProdDistrib G.V H.V K.V) (by
      rintro ⟨(a | a), b⟩ ⟨(c | c), d⟩
      · show (_root_.CGraph.disjUnion (CGraph.lexProduct G K)
          (CGraph.lexProduct H K)).Adj (Sum.inl (a, b)) (Sum.inl (c, d)) = _
        simp [disjUnion_inl_eq_inl]
      · show (_root_.CGraph.disjUnion (CGraph.lexProduct G K)
          (CGraph.lexProduct H K)).Adj (Sum.inl (a, b)) (Sum.inr (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.lexProduct G K)
          (CGraph.lexProduct H K)).Adj (Sum.inr (a, b)) (Sum.inl (c, d)) = _
        simp
      · show (_root_.CGraph.disjUnion (CGraph.lexProduct G K)
          (CGraph.lexProduct H K)).Adj (Sum.inr (a, b)) (Sum.inr (c, d)) = _
        simp [disjUnion_inr_eq_inr])

/-! ### Line graphs and Mycielskians

Two more unary constructions.  The line graph transports along `SimpleGraph.Iso.mapEdgeSet`, and
the Mycielskian along the same bijection applied to the original vertices, their shadows and the
apex. -/

/-- The Mycielskian respects isomorphism. -/
def mycielskian [DecidableEq G.V] [DecidableEq G'.V] (i : G ≃cg G') :
    CGraph.mycielskian G ≃cg CGraph.mycielskian G' :=
  isoOfAdj (G := CGraph.mycielskian G) (H := CGraph.mycielskian G')
    (Equiv.optionCongr (Equiv.sumCongr i.toEquiv i.toEquiv)) fun x y ↦ by
      rcases x with _ | (a | a) <;> rcases y with _ | (b | b) <;>
        first
          | rfl
          | exact i.adj_eq a b

/-- The line graph respects isomorphism: an isomorphism carries edges to edges, and two edges
meet exactly when their images do. -/
def lineGraph [DecidableEq G.V] [DecidableEq G'.V] (i : G ≃cg G') :
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

/-- **The line graph of a disjoint union is the disjoint union of the line graphs**: an edge of
`G + H` lies wholly in `G` or wholly in `H`, and two edges on opposite sides never meet.

The forward map `sumEdge` is injective, and both sides have `E G + E H` vertices, so
`Fintype.bijective_iff_injective_and_card` supplies the inverse — which is why this is
`noncomputable`. -/
noncomputable def lineGraphDisjUnion (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    CGraph.lineGraph (_root_.CGraph.disjUnion G H) ≃cg
      _root_.CGraph.disjUnion (CGraph.lineGraph G) (CGraph.lineGraph H) := by
  have hcard : Fintype.card ((CGraph.lineGraph G).V ⊕ (CGraph.lineGraph H).V)
      = Fintype.card (CGraph.lineGraph (_root_.CGraph.disjUnion G H)).V := by
    rw [Fintype.card_sum, CGraph.card_lineGraph, CGraph.card_lineGraph, CGraph.card_lineGraph,
      CGraph.E_disjUnion]
  have hbij : Function.Bijective (sumEdge G H) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨sumEdge_inj G H, hcard⟩
  have hmem : ∀ (e : (CGraph.lineGraph G).V) (v : (_root_.CGraph.disjUnion G H).V),
      v ∈ (((Equiv.ofBijective (sumEdge G H) hbij) (.inl e)).1 :
            Sym2 (_root_.CGraph.disjUnion G H).V)
        ↔ ∃ a ∈ (e.1 : Sym2 G.V), Sum.inl a = v :=
    fun _ _ ↦ Sym2.mem_map
  have hmem' : ∀ (e : (CGraph.lineGraph H).V) (v : (_root_.CGraph.disjUnion G H).V),
      v ∈ (((Equiv.ofBijective (sumEdge G H) hbij) (.inr e)).1 :
            Sym2 (_root_.CGraph.disjUnion G H).V)
        ↔ ∃ a ∈ (e.1 : Sym2 H.V), Sum.inr a = v :=
    fun _ _ ↦ Sym2.mem_map
  refine (isoOfAdj (G := _root_.CGraph.disjUnion (CGraph.lineGraph G) (CGraph.lineGraph H))
    (H := CGraph.lineGraph (_root_.CGraph.disjUnion G H))
    (Equiv.ofBijective _ hbij) ?_).symm
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

/-! ### Disjoint unions of families -/

/-- A `sigmaUnion` over `Fin (n + 1)` is the disjoint union of its first fibre with the
`sigmaUnion` of the rest. -/
def sigmaUnionSucc {n : ℕ} (F : Fin (n + 1) → CGraph) [∀ i, DecidableEq (F i).V] :
    sigmaUnion F ≃cg _root_.CGraph.disjUnion (F 0) (sigmaUnion fun i : Fin n ↦ F i.succ) :=
  isoOfAdj (G := sigmaUnion F)
    (H := _root_.CGraph.disjUnion (F 0) (sigmaUnion fun i : Fin n ↦ F i.succ))
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

/-- **`compl (G[H]) = (compl G)[compl H]`**: of the four products, the lexicographic one is the
only whose complement is again a product — of the complements.  Two pairs are non-adjacent in
`G[H]` exactly when the first coordinates are non-adjacent, or equal with the second coordinates
non-adjacent. -/
def complLexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    CGraph.compl (CGraph.lexProduct G H) ≃cg
      CGraph.lexProduct (CGraph.compl G) (CGraph.compl H) :=
  isoOfAdj (G := CGraph.compl (CGraph.lexProduct G H))
    (H := CGraph.lexProduct (CGraph.compl G) (CGraph.compl H)) (Equiv.refl (G.V × H.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (CGraph.lexProduct (CGraph.compl G) (CGraph.compl H)).Adj (a, b) (c, d)
        = (CGraph.compl (CGraph.lexProduct G H)).Adj (a, b) (c, d)
      rcases eq_or_ne a c with rfl | hac
      · simp [Bool.eq_false_iff.2 (G.loopless a), lexProduct_pair_eq]
      · simp [hac, lexProduct_pair_eq])

/-- **`(empty n)[G] = (empty n) □ G`**: with an edgeless first factor, both products are `n`
disjoint copies of `G`. -/
def emptyLexProduct (n : ℕ) (G : CGraph) [DecidableEq G.V] :
    CGraph.lexProduct (CGraph.empty n) G ≃cg CGraph.cartesianProduct (CGraph.empty n) G :=
  isoOfAdj (G := CGraph.lexProduct (CGraph.empty n) G)
    (H := CGraph.cartesianProduct (CGraph.empty n) G) (Equiv.refl ((CGraph.empty n).V × G.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (CGraph.cartesianProduct (CGraph.empty n) G).Adj (a, b) (c, d)
        = (CGraph.lexProduct (CGraph.empty n) G).Adj (a, b) (c, d)
      simp)

/-- **`(empty n) ⊠ G = (empty n) □ G`**: likewise for the strong product.  Only the tensor
product breaks ranks here — with an edgeless factor it is edgeless. -/
def emptyStrongProduct (n : ℕ) (G : CGraph) [DecidableEq G.V] :
    CGraph.strongProduct (CGraph.empty n) G ≃cg CGraph.cartesianProduct (CGraph.empty n) G :=
  isoOfAdj (G := CGraph.strongProduct (CGraph.empty n) G)
    (H := CGraph.cartesianProduct (CGraph.empty n) G) (Equiv.refl ((CGraph.empty n).V × G.V)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩
      show (CGraph.cartesianProduct (CGraph.empty n) G).Adj (a, b) (c, d)
        = (CGraph.strongProduct (CGraph.empty n) G).Adj (a, b) (c, d)
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

/-! ### Bipartite double covers

`K₂ × G` is the bipartite double cover of `G`.  It splits into two copies of `G` exactly when `G`
is bipartite, and for an odd cycle it is the cycle of twice the length. -/

/-- Twisting the `K₂` coordinate by a 2-colouring of the other coordinate.  This is the bijection
that turns a bipartite double cover into two disjoint copies. -/
def colourTwist (G : CGraph) (c : G.V → Bool) : (Fin 2 × G.V) ≃ (Fin 2 × G.V) where
  toFun p := (⟨(p.1.1 + (if c p.2 then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩, p.2)
  invFun p := (⟨(p.1.1 + (if c p.2 then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩, p.2)
  left_inv p := by
    have h := p.1.isLt
    refine Prod.ext (Fin.ext ?_) rfl
    simp only
    rcases c p.2 <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega
  right_inv p := by
    have h := p.1.isLt
    refine Prod.ext (Fin.ext ?_) rfl
    simp only
    rcases c p.2 <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

/-- **A double cover splits whenever the graph is 2-coloured.**  If `c` is a proper 2-colouring of
`G` — that is, if `G` is bipartite — then twisting the `K₂` coordinate by the colour carries the
tensor product onto the Cartesian one, which is two disjoint copies. -/
def tensorTwoOfColouring (G : CGraph) [DecidableEq G.V] (c : G.V → Bool)
    (h : ∀ x y, G.Adj x y = true → c x ≠ c y) :
    CGraph.tensorProduct (CGraph.complete 2) G ≃cg CGraph.cartesianProduct (CGraph.empty 2) G :=
  isoOfAdj (G := CGraph.tensorProduct (CGraph.complete 2) G)
    (H := CGraph.cartesianProduct (CGraph.empty 2) G) (colourTwist G c) (by
      rintro ⟨a, x⟩ ⟨b, y⟩
      show (CGraph.cartesianProduct (CGraph.empty 2) G).Adj
          (⟨(a.1 + (if c x then 1 else 0)) % 2, _⟩, x)
          (⟨(b.1 + (if c y then 1 else 0)) % 2, _⟩, y)
        = (CGraph.tensorProduct (CGraph.complete 2) G).Adj (a, x) (b, y)
      rw [CGraph.cartesianProduct_adj, CGraph.tensorProduct_adj]
      simp only [CGraph.empty_adj, CGraph.complete_adj, Bool.false_and, Bool.or_false]
      rcases hxy : G.Adj x y with _ | _
      · simp
      · have hne := h x y hxy
        have ha := a.isLt
        have hb := b.isLt
        simp only [Bool.and_true]
        rw [show (decide ((⟨(a.1 + (if c x then 1 else 0)) % 2,
              Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
            = ⟨(b.1 + (if c y then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩))
          = decide ((a.1 + (if c x then 1 else 0)) % 2
            = (b.1 + (if c y then 1 else 0)) % 2) from by simp [Fin.ext_iff]]
        rw [show (decide (a ≠ b)) = decide (a.1 ≠ b.1) from by
          simp only [decide_eq_decide, ne_eq, not_iff_not]
          exact ⟨fun hh ↦ congrArg Fin.val hh, fun hh ↦ Fin.ext hh⟩]
        congr 1
        simp only [eq_iff_iff, ne_eq]
        rcases hcx : c x <;> rcases hcy : c y <;>
          simp only [if_true, if_false, Bool.false_eq_true] <;>
          first
            | omega
            | exact absurd (hcx.trans hcy.symm) hne)

/-- The Chinese remainder bijection `Fin (2n) ≃ Fin 2 × Fin n` for odd `n`, as the reduction
`k ↦ (k % 2, k % n)`.  Injectivity is elementary rather than a coprimality argument: `k` and
`k % n` differ by `0` or `n`, and `n` is odd, so the two residues pin `k` down. -/
noncomputable def crtEquiv (m : ℕ) : Fin (2 * (2 * m + 3)) ≃ (Fin 2 × Fin (2 * m + 3)) :=
  Equiv.ofBijective
    (fun k ↦ (⟨k.1 % 2, Nat.mod_lt _ (by omega)⟩, ⟨k.1 % (2 * m + 3), Nat.mod_lt _ (by omega)⟩))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro k l hkl
      have hk := mod_of_lt_two_mul (d := 2 * m + 3) k.isLt
      have hl := mod_of_lt_two_mul (d := 2 * m + 3) l.isLt
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hkl
      exact Fin.ext (by omega), by simp⟩)

/-- **The double cover of an odd cycle is the cycle of twice the length.**  Under the Chinese
remainder bijection, stepping once around `C_{2n}` changes the parity *and* steps once around
`C_n` — which is exactly an edge of `K₂ × C_n`. -/
noncomputable def cycleTensorTwo (m : ℕ) :
    CGraph.cycle (2 * (2 * m + 3)) ≃cg
      CGraph.tensorProduct (CGraph.complete 2) (CGraph.cycle (2 * m + 3)) :=
  isoOfAdj (G := CGraph.cycle (2 * (2 * m + 3)))
    (H := CGraph.tensorProduct (CGraph.complete 2) (CGraph.cycle (2 * m + 3))) (crtEquiv m) (by
      intro k l
      show (CGraph.tensorProduct (CGraph.complete 2) (CGraph.cycle (2 * m + 3))).Adj
          (⟨k.1 % 2, _⟩, ⟨k.1 % (2 * m + 3), _⟩) (⟨l.1 % 2, _⟩, ⟨l.1 % (2 * m + 3), _⟩)
        = (CGraph.cycle (2 * (2 * m + 3))).Adj k l
      have hn : 0 < 2 * m + 3 := by omega
      have e1 := succ_mod_eq_iff (d := 2 * m + 3) (x := k.1 % (2 * m + 3))
        (y := l.1 % (2 * m + 3)) (Nat.mod_lt _ hn)
      have e2 := succ_mod_eq_iff (d := 2 * m + 3) (x := l.1 % (2 * m + 3))
        (y := k.1 % (2 * m + 3)) (Nat.mod_lt _ hn)
      have e3 := succ_mod_eq_iff (d := 2 * (2 * m + 3)) (x := k.1) (y := l.1) k.isLt
      have e4 := succ_mod_eq_iff (d := 2 * (2 * m + 3)) (x := l.1) (y := k.1) l.isLt
      have hk := mod_of_lt_two_mul (d := 2 * m + 3) k.isLt
      have hl := mod_of_lt_two_mul (d := 2 * m + 3) l.isLt
      refine Bool.eq_iff_iff.2 ?_
      simp only [CGraph.tensorProduct_adj, CGraph.complete_adj, CGraph.cycle, CGraph.ofRel_adj,
        Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq, Fin.ext_iff]
      rw [e1, e2, e3, e4]
      omega)

/-! ### Matchings as circulants -/

/-- Splitting `Fin (2m)` into `Fin m × Fin 2` by `k ↦ (k % m, k / m)`, written in the direction
`(i, a) ↦ i + m * a` so that the adjacency computation never has to divide. -/
noncomputable def finTwoMul (m : ℕ) : (Fin (m + 1) × Fin 2) ≃ Fin (2 * (m + 1)) :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1.1 + (m + 1) * p.2.1, by
      have hp := p.1.isLt
      have h2 : p.2.1 = 0 ∨ p.2.1 = 1 := by omega
      rcases h2 with h | h <;> rw [h] <;> omega⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.1 + (m + 1) * a.1 = j.1 + (m + 1) * b.1 := congrArg Fin.val hij
      have ha2 : a.1 = 0 ∨ a.1 = 1 := by omega
      have hb2 : b.1 = 0 ∨ b.1 = 1 := by omega
      have hab : i = j ∧ a = b := by
        rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;> rw [ha, hb] at hij' <;>
          exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      rw [hab.1, hab.2], by simp [Nat.mul_comm]⟩)

/-- **A perfect matching, as a circulant.**  `circulant (2m) {m}` joins `i` to `i + m`, so it is
`m` disjoint edges. -/
noncomputable def circulantMatching (m : ℕ) :
    CGraph.cartesianProduct (CGraph.empty (m + 1)) (CGraph.complete 2) ≃cg
      CGraph.circulant (2 * (m + 1)) [m + 1] :=
  isoOfAdj (G := CGraph.cartesianProduct (CGraph.empty (m + 1)) (CGraph.complete 2))
    (H := CGraph.circulant (2 * (m + 1)) [m + 1]) (finTwoMul m) (by
      rintro ⟨i, a⟩ ⟨j, b⟩
      have hi := i.isLt
      have hj := j.isLt
      have ha2 : a.1 = 0 ∨ a.1 = 1 := by omega
      have hb2 : b.1 = 0 ∨ b.1 = 1 := by omega
      have hx : i.1 + (m + 1) * a.1 < 2 * (m + 1) := by
        rcases ha2 with h | h <;> rw [h] <;> omega
      have hy : j.1 + (m + 1) * b.1 < 2 * (m + 1) := by
        rcases hb2 with h | h <;> rw [h] <;> omega
      have hIJ : (i = j) ↔ (i.1 = j.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
      show (CGraph.circulant (2 * (m + 1)) [m + 1]).Adj
          (⟨i.1 + (m + 1) * a.1, hx⟩ : Fin (2 * (m + 1)))
          (⟨j.1 + (m + 1) * b.1, hy⟩ : Fin (2 * (m + 1)))
        = (CGraph.cartesianProduct (CGraph.empty (m + 1)) (CGraph.complete 2)).Adj (i, a) (j, b)
      rw [CGraph.cartesianProduct_adj]
      simp only [CGraph.circulant, CGraph.ofRel_adj, CGraph.empty_adj, CGraph.complete_adj,
        Bool.false_and, Bool.or_false, List.contains_cons, List.contains_nil]
      refine Bool.eq_iff_iff.2 ?_
      rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;>
        · have h1 := sub_mod_cases hx hy
          have h2 := sub_mod_cases hy hx
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq,
            Fin.ext_iff, hIJ]
          rw [ha, hb] at h1 h2 ⊢
          omega)

/-! ### Paley graphs -/

/-- The three residue classes mod `3`, which are the parts of the (degenerate) `paley 9`. -/
private def paleyNineMap : Fin 3 ⊕ Fin 3 ⊕ Fin 3 → (CGraph.paley 9).V
  | .inl i => ⟨3 * i.1, by omega⟩
  | .inr (.inl i) => ⟨3 * i.1 + 1, by omega⟩
  | .inr (.inr i) => ⟨3 * i.1 + 2, by omega⟩

/-- `paley 9` is `K₃,₃,₃`: its complement is three triangles, the residue classes mod `3`. -/
noncomputable def paleyNineIso :
    CGraph.disjUnion (CGraph.complete 3)
        (CGraph.disjUnion (CGraph.complete 3) (CGraph.complete 3)) ≃cg
      CGraph.compl (CGraph.paley 9) :=
  isoOfAdj (Equiv.ofBijective paleyNineMap (by decide)) (by decide)

/-- Multiplication by the non-residue `2` mod `13` exchanges edges with non-edges. -/
noncomputable def paleyThirteenIso : CGraph.paley 13 ≃cg CGraph.compl (CGraph.paley 13) :=
  isoOfAdj (Equiv.ofBijective (fun x : Fin 13 ↦ (⟨2 * x.1 % 13, by omega⟩ : Fin 13))
    (by decide)) (by decide)

/-- Multiplication by the non-residue `3` mod `17`. -/
noncomputable def paleySeventeenIso : CGraph.paley 17 ≃cg CGraph.compl (CGraph.paley 17) :=
  isoOfAdj (Equiv.ofBijective (fun x : Fin 17 ↦ (⟨3 * x.1 % 17, by omega⟩ : Fin 17))
    (by decide)) (by decide)

end Iso

end CGraph

namespace IsoGraph

/-! ## The constructions, on the quotient

Each of these is the corresponding `CGraph` construction, read as an isomorphism class.  The
ones taking a graph as an argument are the interesting cases; see the module docstring. -/

/-- The edgeless graph on `n` vertices. -/
def empty (n : ℕ) : IsoGraph := ⟦CGraph.empty n⟧

/-- The complete graph on `n` vertices. -/
def complete (n : ℕ) : IsoGraph := ⟦CGraph.complete n⟧

/-- The path on `n` vertices. -/
def path (n : ℕ) : IsoGraph := ⟦CGraph.path n⟧

/-- The cycle on `n` vertices. -/
def cycle (n : ℕ) : IsoGraph := ⟦CGraph.cycle n⟧

/-- The complete bipartite graph `K_{m,n}`. -/
def bipartite (m n : ℕ) : IsoGraph := ⟦CGraph.bipartite m n⟧

/-- The complete multipartite graph with parts of the given sizes. -/
def completeMultipartite (ds : List ℕ) : IsoGraph := ⟦CGraph.completeMultipartite ds⟧

/-- The star with `n` leaves. -/
def star (n : ℕ) : IsoGraph := ⟦CGraph.star n⟧

/-- The wheel with an `n`-cycle rim. -/
def wheel (n : ℕ) : IsoGraph := ⟦CGraph.wheel n⟧

/-- The Kneser graph `K(n, k)`. -/
def kneser (n k : ℕ) : IsoGraph := ⟦CGraph.kneser n k⟧

/-- The Johnson graph `J(n, k)`. -/
def johnson (n k : ℕ) : IsoGraph := ⟦CGraph.johnson n k⟧

/-- The `n`-dimensional hypercube `Q_n`. -/
def hypercube (n : ℕ) : IsoGraph := ⟦CGraph.hypercube n⟧

/-- The folded `n`-cube. -/
def foldedCube (n : ℕ) : IsoGraph := ⟦CGraph.foldedCube n⟧

/-- The circulant graph on `n` vertices with connection set `S`. -/
def circulant (n : ℕ) (S : List ℕ) : IsoGraph := ⟦CGraph.circulant n S⟧

/-- The Paley graph on `q` vertices. -/
def paley (q : ℕ) : IsoGraph := ⟦CGraph.paley q⟧

/-- The Paley graph of a finite field. -/
def paleyField (F : Type) [Field F] [Fintype F] [DecidableEq F] : IsoGraph :=
  ⟦CGraph.paleyField F⟧

/-- The theta graph with the given path lengths. -/
def thetaGraph (xs : List ℕ) : IsoGraph := ⟦CGraph.thetaGraph xs⟧

/-- The `(m, k)`-tadpole. -/
def tadpole (m k : ℕ) : IsoGraph := ⟦CGraph.tadpole m k⟧

/-- The `(m, k)`-lollipop. -/
def lollipop (m k : ℕ) : IsoGraph := ⟦CGraph.lollipop m k⟧

/-- The spider with the given leg lengths. -/
def spider (legs : List ℕ) : IsoGraph := ⟦CGraph.spider legs⟧

/-- The double star `S_{m,n}`. -/
def doubleStar (m n : ℕ) : IsoGraph := ⟦CGraph.doubleStar m n⟧

/-- The `m`-cycle with pendant paths of the given lengths. -/
def cyclePendant (m : ℕ) (ks : List ℕ) : IsoGraph := ⟦CGraph.cyclePendant m ks⟧

/-- The generalized Petersen graph `GP(n, k)`. -/
def gp (n k : ℕ) : IsoGraph := ⟦CGraph.gp n k⟧

/-- The LCF graph: an `ss.length * r`-cycle with the chords given by repeating the jump sequence
`ss` `r` times. -/
def lcf (ss : List ℤ) (r : ℕ) : IsoGraph := ⟦CGraph.lcf ss r⟧

/-! ### Operations -/

/-- The complement of an isomorphism class. -/
def compl (G : IsoGraph) : IsoGraph :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ ⟦CGraph.compl g.canonicalize⟧)
    (by
      rintro g h ⟨i⟩
      exact Quotient.sound
        ⟨CGraph.Iso.compl (g.isoCanonicalize.symm.trans (i.trans h.isoCanonicalize))⟩) G

/-- Complementation is written `Gᶜ`.  There is no such instance for `CGraph`, whose complement
needs a `DecidableEq` on the vertex type and so cannot be a bare `α → α`.

Note that `⟦g⟧ᶜ` does not elaborate — instance search sees the type `Quotient CGraph.isoSetoid`
and will not unfold `IsoGraph` to reach it.  Write `(show IsoGraph from ⟦g⟧)ᶜ`; a type ascription
is *not* enough, since it leaves the inferred type unchanged. -/
instance : Compl IsoGraph := ⟨compl⟩

theorem compl_eq (G : IsoGraph) : Gᶜ = compl G := rfl

@[simp] theorem compl_mk (G : CGraph) [DecidableEq G.V] :
    (show IsoGraph from ⟦G⟧)ᶜ = ⟦CGraph.compl G⟧ :=
  Quotient.sound ⟨CGraph.Iso.compl G.isoCanonicalize.symm⟩

/-- The disjoint union of two isomorphism classes. -/
def disjUnion (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.disjUnion g h⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.disjUnion i j⟩) G H

/-- The join of two isomorphism classes: a disjoint union with all edges across. -/
def join (G H : IsoGraph) : IsoGraph := (disjUnion Gᶜ Hᶜ)ᶜ

/-- The cartesian product of two isomorphism classes. -/
def cartesianProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.cartesianProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.cartesianProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

/-- The tensor product of two isomorphism classes. -/
def tensorProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.tensorProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.tensorProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

/-- The strong product of two isomorphism classes. -/
def strongProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.strongProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.strongProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

/-- The lexicographic product of two isomorphism classes. -/
def lexProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.lexProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.lexProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

/-! ### Notation

One symbol per binary operation, each suffixed with `g` in the style of Mathlib's `⊕g` for
`SimpleGraph.sum` — which stays in scope, and which the overload resolves against by type.  The
squared symbols follow Mathlib's `□` for `SimpleGraph.boxProd`; of the alternative box characters
only `□` (`\square`) has a Lean input abbreviation.  Complementation is the `Compl` instance
above rather than a notation of its own.

The four products bind more tightly than the two sums, so `G ⊕g H □g K` is `G ⊕g (H □g K)`. -/

@[inherit_doc] infixl:60 " ⊕g " => IsoGraph.disjUnion
@[inherit_doc] infixl:60 " ∇g " => IsoGraph.join
@[inherit_doc] infixl:70 " □g " => IsoGraph.cartesianProduct
@[inherit_doc] infixl:70 " ⊗g " => IsoGraph.tensorProduct
@[inherit_doc] infixl:70 " ⊠g " => IsoGraph.strongProduct
@[inherit_doc] infixl:70 " ·g " => IsoGraph.lexProduct

@[simp] theorem disjUnion_mk (G H : CGraph) :
    ⟦G⟧ ⊕g ⟦H⟧ = ⟦CGraph.disjUnion G H⟧ := rfl

@[simp] theorem cartesianProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    ⟦G⟧ □g ⟦H⟧ = ⟦CGraph.cartesianProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.cartesianProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

@[simp] theorem tensorProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    ⟦G⟧ ⊗g ⟦H⟧ = ⟦CGraph.tensorProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.tensorProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

@[simp] theorem strongProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    ⟦G⟧ ⊠g ⟦H⟧ = ⟦CGraph.strongProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.strongProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

@[simp] theorem lexProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    ⟦G⟧ ·g ⟦H⟧ = ⟦CGraph.lexProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.lexProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

/-- The join is a complement of a disjoint union of complements on both levels, so its bridge is
the two others put together. -/
@[simp] theorem join_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (⟦G⟧ : IsoGraph) ∇g ⟦H⟧ = ⟦CGraph.join G H⟧ := by
  rw [join, compl_mk, compl_mk, disjUnion_mk, compl_mk]
  rfl

/-- The line graph of an isomorphism class: its vertices are the edges, adjacent when they meet. -/
def lineGraph (G : IsoGraph) : IsoGraph :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ ⟦CGraph.lineGraph g.canonicalize⟧)
    (by
      rintro g h ⟨i⟩
      exact Quotient.sound
        ⟨CGraph.Iso.lineGraph (g.isoCanonicalize.symm.trans (i.trans h.isoCanonicalize))⟩) G

@[simp] theorem lineGraph_mk (G : CGraph) [DecidableEq G.V] :
    lineGraph ⟦G⟧ = ⟦CGraph.lineGraph G⟧ :=
  Quotient.sound ⟨CGraph.Iso.lineGraph G.isoCanonicalize.symm⟩

/-- The Mycielskian of an isomorphism class. -/
def mycielskian (G : IsoGraph) : IsoGraph :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ ⟦CGraph.mycielskian g.canonicalize⟧)
    (by
      rintro g h ⟨i⟩
      exact Quotient.sound
        ⟨CGraph.Iso.mycielskian (g.isoCanonicalize.symm.trans (i.trans h.isoCanonicalize))⟩) G

@[simp] theorem mycielskian_mk (G : CGraph) [DecidableEq G.V] :
    mycielskian ⟦G⟧ = ⟦CGraph.mycielskian G⟧ :=
  Quotient.sound ⟨CGraph.Iso.mycielskian G.isoCanonicalize.symm⟩

/-! ### Abbreviations

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

/-! ## Bridging to `CGraph`

Each of these is `rfl`, naming the `CGraph` representative of a construction defined on
`IsoGraph`. -/

theorem empty_def (n : ℕ) : empty n = ⟦CGraph.empty n⟧ := rfl
theorem complete_def (n : ℕ) : complete n = ⟦CGraph.complete n⟧ := rfl
theorem path_def (n : ℕ) : path n = ⟦CGraph.path n⟧ := rfl
theorem cycle_def (n : ℕ) : cycle n = ⟦CGraph.cycle n⟧ := rfl
theorem bipartite_def (m n : ℕ) : bipartite m n = ⟦CGraph.bipartite m n⟧ := rfl
theorem completeMultipartite_def (ds : List ℕ) :
    completeMultipartite ds = ⟦CGraph.completeMultipartite ds⟧ := rfl
theorem star_def (n : ℕ) : star n = ⟦CGraph.star n⟧ := rfl
theorem wheel_def (n : ℕ) : wheel n = ⟦CGraph.wheel n⟧ := rfl
theorem kneser_def (n k : ℕ) : kneser n k = ⟦CGraph.kneser n k⟧ := rfl
theorem johnson_def (n k : ℕ) : johnson n k = ⟦CGraph.johnson n k⟧ := rfl
theorem hypercube_def (n : ℕ) : hypercube n = ⟦CGraph.hypercube n⟧ := rfl
theorem foldedCube_def (n : ℕ) : foldedCube n = ⟦CGraph.foldedCube n⟧ := rfl
theorem circulant_def (n : ℕ) (S : List ℕ) : circulant n S = ⟦CGraph.circulant n S⟧ := rfl
theorem paley_def (q : ℕ) : paley q = ⟦CGraph.paley q⟧ := rfl
theorem paleyField_def (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    paleyField F = ⟦CGraph.paleyField F⟧ := rfl
theorem thetaGraph_def (xs : List ℕ) : thetaGraph xs = ⟦CGraph.thetaGraph xs⟧ := rfl
theorem tadpole_def (m k : ℕ) : tadpole m k = ⟦CGraph.tadpole m k⟧ := rfl
theorem lollipop_def (m k : ℕ) : lollipop m k = ⟦CGraph.lollipop m k⟧ := rfl
theorem spider_def (legs : List ℕ) : spider legs = ⟦CGraph.spider legs⟧ := rfl
theorem doubleStar_def (m n : ℕ) : doubleStar m n = ⟦CGraph.doubleStar m n⟧ := rfl
theorem cyclePendant_def (m : ℕ) (ks : List ℕ) :
    cyclePendant m ks = ⟦CGraph.cyclePendant m ks⟧ := rfl
theorem gp_def (n k : ℕ) : gp n k = ⟦CGraph.gp n k⟧ := rfl
theorem lcf_def (ss : List ℤ) (r : ℕ) : lcf ss r = ⟦CGraph.lcf ss r⟧ := rfl

/-- A graph and its canonical representative are the same isomorphism class. -/
theorem mk_canonicalize (G : CGraph) : (⟦G.canonicalize⟧ : IsoGraph) = ⟦G⟧ :=
  Quotient.sound ⟨G.isoCanonicalize.symm⟩

/-! ## Vertex counts -/

@[simp] theorem V_mk (G : CGraph) : IsoGraph.V ⟦G⟧ = Fintype.card G.V := rfl

/-! ## The transfer set

These are the lemmas the `@[toIsoGraph]` attribute rewrites with, backwards, to turn a
`CGraph`-level statement into its `IsoGraph`-level counterpart.  Most hold by `rfl`; the products,
the complement, the line graph and the Mycielskian do not, because the `IsoGraph`-level operation
canonicalises its arguments first, and the attribute transports the proof along the rewrite rather
than relying on the two statements being definitionally equal.

Each of the non-`rfl` ones asks for a `DecidableEq` on the vertex type, so a fact about `Gᶜ` for a
*variable* `G` only transfers if it carries that instance; for the concrete graphs of the tables
it is always found. -/

attribute [isoTransfer] IsoGraph.V_mk IsoGraph.disjUnion_mk IsoGraph.compl_mk IsoGraph.join_mk
  IsoGraph.cartesianProduct_mk IsoGraph.tensorProduct_mk IsoGraph.strongProduct_mk
  IsoGraph.lexProduct_mk IsoGraph.lineGraph_mk IsoGraph.mycielskian_mk
  IsoGraph.empty_def IsoGraph.complete_def IsoGraph.path_def IsoGraph.cycle_def
  IsoGraph.bipartite_def IsoGraph.completeMultipartite_def IsoGraph.star_def IsoGraph.wheel_def
  IsoGraph.kneser_def IsoGraph.johnson_def IsoGraph.hypercube_def IsoGraph.foldedCube_def
  IsoGraph.circulant_def IsoGraph.paley_def IsoGraph.paleyField_def IsoGraph.thetaGraph_def
  IsoGraph.tadpole_def IsoGraph.lollipop_def IsoGraph.spider_def IsoGraph.doubleStar_def
  IsoGraph.cyclePendant_def IsoGraph.gp_def IsoGraph.lcf_def

/-! ## Two isomorphisms tagged from a distance

`johnsonTwoIso` and `paleyIso` are used inside `IsoGraph/Graphs/Constructions.lean` itself, so they
are declared there — before any of the constructions above exist, and so before `@[toIsoGraph]`
could say what they mean.  They are tagged here instead.  This is the one place in the library where
the attribute is applied by a command rather than written on the declaration, and the reason is the
one that justifies it: the statement it generates depends on definitions the declaration cannot
see. -/

attribute [toIsoGraph johnson_two_eq_compl_kneser] CGraph.johnsonTwoIso
attribute [toIsoGraph paleyField_zmod] CGraph.paleyIso

end IsoGraph
