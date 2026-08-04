import IsoGraph.Constructions

/-!
# Constructions on `IsoGraph`, and the identities between them

`IsoGraph/Constructions.lean` builds graphs as `CGraph`s: concrete data, with a concrete vertex
type.  Two of those are *equal* only when the vertex types are equal and the adjacency functions
agree on the nose, which is far too fine a relation for statements like "the complement of the
5-cycle is the 5-cycle".  On `IsoGraph`, the quotient by isomorphism, that statement is an honest
equation, and this file collects a hundred or so of them.

## Lifting a construction

Every construction with no arguments — `empty`, `complete`, `kneser`, … — lifts by definition:
`IsoGraph.complete n` is just `⟦CGraph.complete n⟧`.  The unary and binary ones need more care,
because most of them ask for a `DecidableEq` on the vertex type and a bare `CGraph` does not
supply one.  Two ways out:

* `disjUnion` needs no `DecidableEq`, so it lifts through `Quotient.lift₂` directly, and
  `disjUnion_mk` is `rfl`;
* the rest are applied to `G.canonicalize`, whose vertex type is `Fin (Fintype.card G.V)` — and
  so has a `DecidableEq` — before descending.  The construction stays computable, and the price
  is that `compl_mk` and friends are proved rather than `rfl`.

Either way the side condition of the lift is an isomorphism-congruence: `CGraph.Iso.compl`,
`CGraph.Iso.cartesianProduct`, … in the first section, each built from `CGraph.isoOfAdj`.

`join` needs no lift of its own: it is `compl (disjUnion (compl G) (compl H))` on `IsoGraph` just
as on `CGraph`, so well-definedness is inherited.

## Proving an identity

Three tools cover almost everything.

* `IsoGraph.mk_eq_empty` and `IsoGraph.mk_eq_complete`: a graph with no edges is `empty` on its
  vertex count, and a graph with all of them is `complete`.  These two settle every degenerate
  case — `kneser n 0`, `hypercube 1`, `lexProduct (complete m) (complete n)`, … — with no
  bijection to write down, since `Fintype.equivFin` supplies one.
* `CGraph.isoOfAdj e (by decide)` for the small sporadic identities: `cycle 3 = complete 3`,
  `compl (cycle 5) = cycle 5`, `hypercube 2 = cycle 4`.  The permutation is written out as a
  vector and the kernel checks all `n²` adjacencies.
* Rewriting with the identities already proved.  `join`, `bipartite`, `star`, `wheel`, `rook`, …
  are all built from `compl`, `disjUnion` and the products, so their identities follow from
  those without ever descending to `CGraph` again — see `join_complete`, `wheel_three` or
  `bipartite_one_one`.
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

/-- Equality of pairs, as a `Bool`.  The associativity proofs below rewrite with this until every
equality test is between vertices of a single factor, and then hand the resulting Boolean
tautology to `decide`. -/
theorem decide_prod_eq {α β : Type} [DecidableEq α] [DecidableEq β] (p q : α × β) :
    decide (p = q) = (decide (p.1 = q.1) && decide (p.2 = q.2)) :=
  (decide_eq_decide.2 Prod.ext_iff).trans (Bool.decide_and _ _)

/-- Injectivity of `Sum.inl`, stated at the vertex type of a `disjUnion` rather than at a bare
`⊕`.  The two are definitionally equal but not *reducibly* so, and `simp` matches up to reducible
unfolding only — so `Sum.inl.injEq` does not fire on a goal about `(disjUnion G H).V`.  The
distributivity proofs below need exactly this. -/
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

/-- **Only the differences in `(0, n)` matter.**  A circulant only ever asks whether its
connection set contains a difference of two distinct vertices, so two connection sets agreeing
there give the same graph — on the nose, not just up to isomorphism. -/
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
theorem circulant_zero_cons (n : ℕ) (S : List ℕ) :
    circulant n (0 :: S) = circulant n S :=
  circulant_congr n _ _ fun d hd _ ↦ by
    have h0 : (d == 0) = false := by simp; omega
    simp only [List.contains_cons, h0, Bool.false_or]

/-- A repeated entry in the connection set contributes nothing. -/
theorem circulant_dup_cons (n k : ℕ) (S : List ℕ) :
    circulant n (k :: k :: S) = circulant n (k :: S) :=
  circulant_congr n _ _ fun d _ _ ↦ by
    simp only [List.contains_cons]
    cases (d == k) <;> simp

/-- **The connection set is symmetric.**  A circulant joins `x` to `y` when either difference is
listed, so replacing an entry `k` by `n - k` does not change the graph. -/
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
this is `Equiv.prodSumDistrib` (resp. `Equiv.sumProdDistrib`); the four `rintro` cases then reduce
to the four ways of pairing `inl`/`inr`.  Each case needs an explicit `show` first: the equivalence
is applied to a pair whose second component is *definitionally* but not reducibly a `Sum`, so
`simp` cannot see through it on its own. -/

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

/-- The connection set of `Paley(13)` is `{±1, ±3, ±4}`. -/
theorem paley_thirteen_eq_circulant : paley 13 = circulant 13 [1, 3, 4] :=
  eq_ofRel _ _ (by decide)

/-- The connection set of `Paley(17)` is `{±1, ±2, ±4, ±8}`. -/
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
theorem IsBipartite.cartesianProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
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
theorem IsBipartite.tensorProduct_left {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsBipartite) : (CGraph.tensorProduct G H).IsBipartite := by
  obtain ⟨c, hc⟩ := hG
  refine ⟨fun p ↦ c p.1, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [CGraph.tensorProduct_adj] at hxy
  simp only [Bool.and_eq_true] at hxy
  exact hc x x' hxy.1

theorem IsBipartite.tensorProduct_right {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
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
theorem IsBipartite.of_cartesianProduct_left {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hH : Nonempty H.V) (h : (CGraph.cartesianProduct G H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨b⟩ := hH
  refine ⟨fun a ↦ c (a, b), fun x y hxy ↦ hc (x, b) (y, b) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

theorem IsBipartite.of_cartesianProduct_right {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : Nonempty G.V) (h : (CGraph.cartesianProduct G H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨a⟩ := hG
  refine ⟨fun b ↦ c (a, b), fun x y hxy ↦ hc (a, x) (a, y) ?_⟩
  rw [cartesianProduct_adj]
  simp [hxy]

/-- **Odd cycles are not bipartite.**  Walking around the cycle, the colour alternates with the
parity of the index; coming back to `0` from the last vertex, which has even index, contradicts
the edge that closes the cycle. -/
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

theorem not_isBipartite_complete (n : ℕ) : ¬ (CGraph.complete (n + 3)).IsBipartite := by
  have hadj : ∀ i j : Fin (n + 3), i.1 ≠ j.1 → (CGraph.complete (n + 3)).Adj i j := by
    intro i j hij
    simp only [CGraph.complete_adj, decide_eq_true_eq, ne_eq, Fin.ext_iff]
    exact hij
  exact not_isBipartite_of_triangle (a := (⟨0, by omega⟩ : (CGraph.complete (n + 3)).V))
    (b := ⟨1, by omega⟩) (d := ⟨2, by omega⟩) (hadj _ _ (by simp)) (hadj _ _ (by simp))
    (hadj _ _ (by simp))

/-- A side of a bipartite join is bipartite: restrict the colouring. -/
theorem IsBipartite.of_join_left {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (h : (CGraph.join G H).IsBipartite) : G.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun a ↦ c (.inl a), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inl_inl])⟩

theorem IsBipartite.of_join_right {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (h : (CGraph.join G H).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun b ↦ c (.inr b), fun x y hxy ↦ hc _ _ (by rwa [join_adj_inr_inr])⟩

/-- An edge on one side of a join, together with any vertex on the other side, is a triangle. -/
theorem not_isBipartite_join_of_adj_left {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    {a b : G.V} (hab : G.Adj a b) (c : H.V) : ¬ (CGraph.join G H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inl a) (b := .inl b) (d := .inr c)
    (by rwa [join_adj_inl_inl]) (join_adj_inl_inr G H a c) (join_adj_inl_inr G H b c)

theorem not_isBipartite_join_of_adj_right {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    {a b : H.V} (hab : H.Adj a b) (c : G.V) : ¬ (CGraph.join G H).IsBipartite :=
  not_isBipartite_of_triangle (a := .inr a) (b := .inr b) (d := .inl c)
    (by rwa [join_adj_inr_inr]) (join_adj_inr_inl G H a c) (join_adj_inr_inl G H b c)

/-- Three nonempty sides give a triangle, whatever the graphs on them are. -/
theorem not_isBipartite_join_join {G H K : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    [DecidableEq K.V] (a : G.V) (b : H.V) (c : K.V) :
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
@[simp] theorem tadpole_zero (m : ℕ) : tadpole m 0 = cycle m := by
  rw [tadpole, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cycleEdges]

/-- A tadpole with no cycle is a path. -/
@[simp] theorem tadpole_zero_left (k : ℕ) : tadpole 0 k = path k := by
  rw [tadpole, cycleEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A tadpole whose cycle is a single vertex is a path: the "cycle" is a loop, which `ofEdges`
discards. -/
@[simp] theorem tadpole_one (k : ℕ) : tadpole 1 k = path (1 + k) := by
  rw [tadpole, ofEdges_cycleEdges_one_append, ofEdges_legEdges_one]

/-- A lollipop with no stick is a complete graph. -/
@[simp] theorem lollipop_zero (m : ℕ) : lollipop m 0 = complete m := by
  rw [lollipop, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cliqueEdges]

/-- A lollipop with no clique is a path. -/
@[simp] theorem lollipop_zero_left (k : ℕ) : lollipop 0 k = path k := by
  rw [lollipop, cliqueEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A lollipop whose clique is a single vertex is a path. -/
@[simp] theorem lollipop_one (k : ℕ) : lollipop 1 k = path (1 + k) := by
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
theorem spider_append_zero_cons (pre post : List ℕ) :
    spider (pre ++ 0 :: post) = spider (pre ++ post) := by
  have hsum : (pre ++ 0 :: post).sum = (pre ++ post).sum := by
    simp only [List.sum_append, List.sum_cons, Nat.zero_add]
  rw [spider, spider, hsum, spiderEdges_append, spiderEdges_append, spiderEdges, legEdges_zero,
    List.nil_append, Nat.add_zero]

/-- A spider with a single leg is a path. -/
@[simp] theorem spider_singleton (k : ℕ) : spider [k] = path (1 + k) := by
  rw [spider, show spiderEdges 1 [k] = legEdges 0 1 k from by simp [spiderEdges],
    show (1 : ℕ) + [k].sum = 1 + k from by simp, ofEdges_legEdges_one]

theorem spiderEdges_replicate_zero : ∀ (off j : ℕ), spiderEdges off (List.replicate j 0) = []
  | _, 0 => rfl
  | off, j + 1 => by
      rw [List.replicate_succ, spiderEdges, legEdges_zero, List.nil_append,
        spiderEdges_replicate_zero (off + 0) j]

/-- A spider all of whose legs are empty is a single vertex. -/
@[simp] theorem spider_replicate_zero (j : ℕ) : spider (List.replicate j 0) = empty 1 := by
  rw [spider, spiderEdges_replicate_zero,
    show (1 : ℕ) + (List.replicate j 0).sum = 1 from by simp, ofEdges_nil]

@[simp] theorem spider_nil : spider [] = empty 1 := spider_replicate_zero 0

theorem pendantEdges_replicate_zero : ∀ (v off j : ℕ), pendantEdges v off (List.replicate j 0) = []
  | _, _, 0 => rfl
  | v, off, j + 1 => by
      rw [List.replicate_succ, pendantEdges, List.range_zero, List.map_nil, List.nil_append,
        pendantEdges_replicate_zero (v + 1) (off + 0) j]

/-- A cycle carrying no pendant vertices is a cycle. -/
@[simp] theorem cyclePendant_replicate_zero (m j : ℕ) :
    cyclePendant m (List.replicate j 0) = cycle m := by
  rw [cyclePendant, pendantEdges_replicate_zero, List.append_nil,
    show m + (List.replicate j 0).sum = m from by simp, ofEdges_cycleEdges]

@[simp] theorem cyclePendant_nil (m : ℕ) : cyclePendant m [] = cycle m :=
  cyclePendant_replicate_zero m 0

/-- Pendant vertices attached beyond the end of the cycle are no vertices at all. -/
theorem pendantEdges_append_zero : ∀ (v off : ℕ) (ks : List ℕ),
    pendantEdges v off (ks ++ [0]) = pendantEdges v off ks
  | _, _, [] => by simp [pendantEdges]
  | v, off, k :: ks => by
      rw [List.cons_append, pendantEdges, pendantEdges, pendantEdges_append_zero (v + 1) (off + k)]

/-- A cycle with a trailing empty block of pendant vertices is the cycle without that block. -/
theorem cyclePendant_append_zero (m : ℕ) (ks : List ℕ) :
    cyclePendant m (ks ++ [0]) = cyclePendant m ks := by
  have hsum : (ks ++ [0]).sum = ks.sum := by simp
  rw [cyclePendant, cyclePendant, pendantEdges_append_zero, hsum]

/-- Two paths of length one between the poles of a theta graph are the same single edge, so one of
them can be dropped. -/
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
in the exact shape produced by `mem_legEdges`, so that the graph-level proof can just apply this. -/
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

/-- A step around a cycle of length at least two never stands still. -/
theorem succ_mod_ne {d x : ℕ} (h2 : 2 ≤ d) (hx : x < d) : (x + 1) % d ≠ x := by
  by_cases h : x + 1 = d
  · rw [h, Nat.mod_self]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

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
  split_ifs <;> omega

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
  split_ifs <;> omega

/-- The block exchange carries the path with `b` internal vertices back onto the first block. -/
theorem swapBlocksFwd_theta_snd (s a b p q : ℕ) (hs : 2 ≤ s)
    (h : (p, q) ∈ thetaEdges (s + a) [b]) :
    (swapBlocksFwd s a b p, swapBlocksFwd s a b q) ∈ thetaEdges s [b] := by
  rw [mem_thetaEdges_single] at h ⊢
  unfold swapBlocksFwd
  split_ifs <;> omega

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
theorem toSimple_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).toSimple = SimpleGraph.boxProd G.toSimple H.toSimple := by
  ext p q
  simp only [CGraph.toSimple_adj, cartesianProduct_adj, SimpleGraph.boxProd_adj,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem isConnected_cartesianProduct_iff (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).IsConnected ↔ G.IsConnected ∧ H.IsConnected := by
  show (cartesianProduct G H).toSimple.Connected ↔ _
  rw [toSimple_cartesianProduct]
  exact SimpleGraph.connected_boxProd

/-- Euler's count for trees, on `CGraph`: a graph is a tree exactly when it is connected and has
one fewer edge than it has vertices. -/
theorem isTree_iff_isConnected_and_E (G : CGraph) :
    G.IsTree ↔ G.IsConnected ∧ G.E + 1 = Fintype.card G.V := by
  show G.toSimple.IsTree ↔ _
  rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  rfl

/-- A connected graph has at least one fewer edge than it has vertices. -/
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

theorem cartesianProduct_le_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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

theorem cartesianProduct_le_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).toSimple ≤ (lexProduct G H).toSimple := by
  intro p q hpq
  rw [CGraph.toSimple_adj, cartesianProduct_adj] at hpq
  rw [CGraph.toSimple_adj, lexProduct_adj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq ⊢
  tauto

theorem isConnected_strongProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsConnected) (hH : H.IsConnected) : (strongProduct G H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_strongProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

theorem isConnected_lexProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsConnected) (hH : H.IsConnected) : (lexProduct G H).IsConnected :=
  SimpleGraph.Connected.mono (cartesianProduct_le_lexProduct G H)
    ((isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩)

/-! ### Triangles in the strong and lexicographic products -/

theorem not_isBipartite_strongProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
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

theorem not_isBipartite_lexProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    {a b : G.V} {c d : H.V} (hab : G.Adj a b) (hcd : H.Adj c d) :
    ¬ (lexProduct G H).IsBipartite := by
  have hba : G.Adj b a := by rwa [G.symm]
  refine not_isBipartite_of_triangle (a := (a, c)) (b := (a, d)) (d := (b, c)) ?_ ?_ ?_ <;>
  · rw [lexProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    tauto

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

/-! ### Operations -/

/-- The complement of an isomorphism class. -/
def compl (G : IsoGraph) : IsoGraph :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ ⟦CGraph.compl g.canonicalize⟧)
    (by
      rintro g h ⟨i⟩
      exact Quotient.sound
        ⟨CGraph.Iso.compl (g.isoCanonicalize.symm.trans (i.trans h.isoCanonicalize))⟩) G

@[simp] theorem compl_mk (G : CGraph) [DecidableEq G.V] : compl ⟦G⟧ = ⟦CGraph.compl G⟧ :=
  Quotient.sound ⟨CGraph.Iso.compl G.isoCanonicalize.symm⟩

/-- The disjoint union of two isomorphism classes. -/
def disjUnion (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.disjUnion g h⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.disjUnion i j⟩) G H

@[simp] theorem disjUnion_mk (G H : CGraph) :
    disjUnion ⟦G⟧ ⟦H⟧ = ⟦CGraph.disjUnion G H⟧ := rfl

/-- The join of two isomorphism classes: a disjoint union with all edges across. -/
def join (G H : IsoGraph) : IsoGraph := compl (disjUnion (compl G) (compl H))

/-- The cartesian product of two isomorphism classes. -/
def cartesianProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.cartesianProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.cartesianProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

@[simp] theorem cartesianProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    cartesianProduct ⟦G⟧ ⟦H⟧ = ⟦CGraph.cartesianProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.cartesianProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

/-- The tensor product of two isomorphism classes. -/
def tensorProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.tensorProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.tensorProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

@[simp] theorem tensorProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    tensorProduct ⟦G⟧ ⟦H⟧ = ⟦CGraph.tensorProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.tensorProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

/-- The strong product of two isomorphism classes. -/
def strongProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.strongProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.strongProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

@[simp] theorem strongProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    strongProduct ⟦G⟧ ⟦H⟧ = ⟦CGraph.strongProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.strongProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

/-- The lexicographic product of two isomorphism classes. -/
def lexProduct (G H : IsoGraph) : IsoGraph :=
  Quotient.lift₂ (s₁ := CGraph.isoSetoid) (s₂ := CGraph.isoSetoid)
    (fun g h ↦ ⟦CGraph.lexProduct g.canonicalize h.canonicalize⟧)
    (by
      rintro g₁ h₁ g₂ h₂ ⟨i⟩ ⟨j⟩
      exact Quotient.sound ⟨CGraph.Iso.lexProduct
        (g₁.isoCanonicalize.symm.trans (i.trans g₂.isoCanonicalize))
        (h₁.isoCanonicalize.symm.trans (j.trans h₂.isoCanonicalize))⟩) G H

@[simp] theorem lexProduct_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    lexProduct ⟦G⟧ ⟦H⟧ = ⟦CGraph.lexProduct G H⟧ :=
  Quotient.sound ⟨CGraph.Iso.lexProduct G.isoCanonicalize.symm H.isoCanonicalize.symm⟩

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
abbrev fan (n : ℕ) : IsoGraph := join (complete 1) (path n)

/-- The `n`-rung ladder. -/
abbrev ladder (n : ℕ) : IsoGraph := cartesianProduct (path n) (complete 2)

/-- The `n`-gonal prism. -/
abbrev prism (n : ℕ) : IsoGraph := cartesianProduct (cycle n) (complete 2)

/-- The triangular graph `T(n)`. -/
abbrev triangular (n : ℕ) : IsoGraph := johnson n 2

/-- The `m × n` rook's graph. -/
abbrev rook (m n : ℕ) : IsoGraph := cartesianProduct (complete m) (complete n)

/-- The cocktail party graph on `n` pairs. -/
abbrev cocktailParty (n : ℕ) : IsoGraph := completeMultipartite (List.replicate n 2)

/-- The Petersen graph, as the Kneser graph on the 2-subsets of a 5-set. -/
abbrev petersen : IsoGraph := kneser 5 2

/-! ## Bridging to `CGraph`

Each of these is `rfl`; they are stated so that a proof can move an identity down to the level of
`CGraph` by `rw` without having to unfold a definition. -/

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
theorem thetaGraph_def (xs : List ℕ) : thetaGraph xs = ⟦CGraph.thetaGraph xs⟧ := rfl
theorem tadpole_def (m k : ℕ) : tadpole m k = ⟦CGraph.tadpole m k⟧ := rfl
theorem lollipop_def (m k : ℕ) : lollipop m k = ⟦CGraph.lollipop m k⟧ := rfl
theorem spider_def (legs : List ℕ) : spider legs = ⟦CGraph.spider legs⟧ := rfl
theorem doubleStar_def (m n : ℕ) : doubleStar m n = ⟦CGraph.doubleStar m n⟧ := rfl
theorem cyclePendant_def (m : ℕ) (ks : List ℕ) :
    cyclePendant m ks = ⟦CGraph.cyclePendant m ks⟧ := rfl

/-- A graph and its canonical representative are the same isomorphism class. -/
theorem mk_canonicalize (G : CGraph) : (⟦G.canonicalize⟧ : IsoGraph) = ⟦G⟧ :=
  Quotient.sound ⟨G.isoCanonicalize.symm⟩

/-! ## Vertex counts -/

@[simp] theorem V_mk (G : CGraph) : IsoGraph.V ⟦G⟧ = Fintype.card G.V := rfl

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

@[simp] theorem V_compl (G : IsoGraph) : (compl G).V = G.V := by
  induction G using Quotient.inductionOn with
  | h g => show Fintype.card (CGraph.compl g.canonicalize).V = _; simp

@[simp] theorem V_disjUnion (G H : IsoGraph) : (disjUnion G H).V = G.V + H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h => exact CGraph.card_disjUnion g h

@[simp] theorem V_join (G H : IsoGraph) : (join G H).V = G.V + H.V := by
  show (compl (disjUnion (compl G) (compl H))).V = _
  simp

@[simp] theorem V_cartesianProduct (G H : IsoGraph) :
    (cartesianProduct G H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.cartesianProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_tensorProduct (G H : IsoGraph) : (tensorProduct G H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.tensorProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_strongProduct (G H : IsoGraph) : (strongProduct G H).V = G.V * H.V := by
  induction G using Quotient.inductionOn with
  | h g => induction H using Quotient.inductionOn with
    | h h =>
      show Fintype.card (CGraph.strongProduct g.canonicalize h.canonicalize).V = _
      simp

@[simp] theorem V_lexProduct (G H : IsoGraph) : (lexProduct G H).V = G.V * H.V := by
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

`join_mk` is what makes the rest of this section possible: it says the `IsoGraph`-level `join`,
defined as `compl (disjUnion (compl G) (compl H))` with no lift of its own, agrees with
`CGraph.join`. -/

@[simp] theorem join_mk (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    join ⟦G⟧ ⟦H⟧ = ⟦CGraph.join G H⟧ := by
  show compl (disjUnion (compl ⟦G⟧) (compl ⟦H⟧)) = _
  rw [compl_mk, compl_mk, disjUnion_mk, compl_mk]
  rfl

theorem join_def (G H : IsoGraph) : join G H = compl (disjUnion (compl G) (compl H)) := rfl

theorem bipartite_eq_compl (m n : ℕ) :
    bipartite m n = compl (disjUnion (complete m) (complete n)) := by
  rw [complete_def, complete_def, disjUnion_mk, compl_mk]
  rfl

theorem star_eq_bipartite (n : ℕ) : star n = bipartite 1 n := rfl

theorem wheel_eq_join (n : ℕ) : wheel n = join (complete 1) (cycle n) := by
  rw [complete_def, cycle_def, join_mk]
  rfl

/-! ## Complementation -/

@[simp] theorem compl_compl (G : IsoGraph) : compl (compl G) = G := by
  induction G using Quotient.inductionOn with
  | h g =>
    show compl ⟦CGraph.compl g.canonicalize⟧ = ⟦g⟧
    rw [compl_mk, CGraph.compl_compl]
    exact mk_canonicalize g

@[simp] theorem compl_empty (n : ℕ) : compl (empty n) = complete n := by
  rw [empty_def, compl_mk]
  rfl

@[simp] theorem compl_complete (n : ℕ) : compl (complete n) = empty n := by
  rw [← compl_empty, compl_compl]

@[simp] theorem compl_join (G H : IsoGraph) :
    compl (join G H) = disjUnion (compl G) (compl H) := by
  show compl (compl (disjUnion (compl G) (compl H))) = _
  rw [compl_compl]

@[simp] theorem compl_disjUnion (G H : IsoGraph) :
    compl (disjUnion G H) = join (compl G) (compl H) := by
  show _ = compl (disjUnion (compl (compl G)) (compl (compl H)))
  rw [compl_compl, compl_compl]

@[simp] theorem compl_bipartite (m n : ℕ) :
    compl (bipartite m n) = disjUnion (complete m) (complete n) := by
  rw [bipartite_eq_compl, compl_compl]

/-! ## Disjoint unions -/

theorem disjUnion_comm (G H : IsoGraph) : disjUnion G H = disjUnion H G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h => exact Quotient.sound (CGraph.disjUnion_comm g h)

theorem disjUnion_assoc (G H K : IsoGraph) :
    disjUnion (disjUnion G H) K = disjUnion G (disjUnion H K) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      induction K using Quotient.inductionOn with
      | h k => exact Quotient.sound (CGraph.disjUnion_assoc g h k)

@[simp] theorem disjUnion_empty_zero (G : IsoGraph) : disjUnion G (empty 0) = G := by
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

@[simp] theorem empty_zero_disjUnion (G : IsoGraph) : disjUnion (empty 0) G = G := by
  rw [disjUnion_comm, disjUnion_empty_zero]

@[simp] theorem disjUnion_empty (m n : ℕ) : disjUnion (empty m) (empty n) = empty (m + n) := by
  rw [empty_def, empty_def, disjUnion_mk,
    mk_eq_empty (G := CGraph.disjUnion (CGraph.empty m) (CGraph.empty n))
      (by rintro (a | a) (b | b) <;> rfl)]
  simp

/-! ## Joins -/

theorem join_comm (G H : IsoGraph) : join G H = join H G := by
  show compl (disjUnion (compl G) (compl H)) = compl (disjUnion (compl H) (compl G))
  rw [disjUnion_comm]

theorem join_assoc (G H K : IsoGraph) : join (join G H) K = join G (join H K) := by
  show compl (disjUnion (compl (join G H)) (compl K))
    = compl (disjUnion (compl G) (compl (join H K)))
  show compl (disjUnion (compl (compl (disjUnion (compl G) (compl H)))) (compl K))
    = compl (disjUnion (compl G) (compl (compl (disjUnion (compl H) (compl K)))))
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
@[simp] theorem compl_cycle_five : compl (cycle 5) = cycle 5 := by
  rw [cycle_def, compl_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩ : Equiv.Perm (Fin 5))
    (by decide)⟩

/-- The path on four vertices is self-complementary. -/
@[simp] theorem compl_path_four : compl (path 4) = path 4 := by
  rw [path_def, compl_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4))
    (by decide)⟩

/-! ## Bipartite, star, wheel -/

theorem bipartite_eq_join (m n : ℕ) : bipartite m n = join (empty m) (empty n) := by
  rw [join_def, compl_empty, compl_empty, bipartite_eq_compl]

@[simp] theorem join_empty_zero (G : IsoGraph) : join G (empty 0) = G := by
  rw [join_def, compl_empty, complete_zero, disjUnion_empty_zero, compl_compl]

@[simp] theorem empty_zero_join (G : IsoGraph) : join (empty 0) G = G := by
  rw [join_comm, join_empty_zero]

@[simp] theorem join_complete (m n : ℕ) : join (complete m) (complete n) = complete (m + n) := by
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
theorem compl_star (n : ℕ) : compl (star n) = disjUnion (empty 1) (complete n) := by
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
@[simp] theorem compl_cycle_four : compl (cycle 4) = disjUnion (complete 2) (complete 2) := by
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
theorem compl_wheel (n : ℕ) : compl (wheel n) = disjUnion (empty 1) (compl (cycle n)) := by
  rw [wheel_eq_join, compl_join, compl_complete]

/-- Likewise for the fan, which is a hub joined to a path rather than a cycle. -/
theorem compl_fan (n : ℕ) : compl (fan n) = disjUnion (empty 1) (compl (path n)) := by
  show compl (join (complete 1) (path n)) = _
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
    completeMultipartite (d :: ds) = join (empty d) (completeMultipartite ds) := by
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
      = join (completeMultipartite ds) (completeMultipartite es) := by
  induction ds with
  | nil => rw [List.nil_append, completeMultipartite_nil, empty_zero_join]
  | cons d ds ih =>
    rw [List.cons_append, completeMultipartite_cons, ih, completeMultipartite_cons, join_assoc]

theorem compl_completeMultipartite_cons (d : ℕ) (ds : List ℕ) :
    compl (completeMultipartite (d :: ds))
      = disjUnion (complete d) (compl (completeMultipartite ds)) := by
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

theorem book_eq_join (n : ℕ) : book n = join (complete 2) (empty n) := by
  show completeMultipartite [1, 1, n] = _
  rw [completeMultipartite_cons, completeMultipartite_pair, bipartite_eq_join, ← join_assoc,
    ← bipartite_eq_join, bipartite_one_one]

/-- The complement of the book `B_n` is its spine, edgeless, next to a clique on the pages. -/
theorem compl_book (n : ℕ) : compl (book n) = disjUnion (empty 2) (complete n) := by
  rw [book_eq_join, compl_join, compl_complete, compl_empty]

/-! ## Circulants

`CGraph.circulant_one_eq_cycle` is an equality of `CGraph`s already, so these are one-liners. -/

@[simp] theorem circulant_nil (n : ℕ) : circulant n [] = empty n := by
  rw [circulant_def, CGraph.circulant_nil, empty_def]

@[simp] theorem circulant_one (n : ℕ) : circulant n [1] = cycle n := by
  rw [circulant_def, CGraph.circulant_one_eq_cycle, cycle_def]

/-- A `0` in the connection set is inert. -/
@[simp] theorem circulant_zero_cons (n : ℕ) (S : List ℕ) :
    circulant n (0 :: S) = circulant n S := by
  rw [circulant_def, circulant_def, CGraph.circulant_zero_cons]

/-- Only the differences in `(0, n)` matter. -/
theorem circulant_congr (n : ℕ) (S T : List ℕ)
    (h : ∀ d, 0 < d → d < n → S.contains d = T.contains d) :
    circulant n S = circulant n T := by
  rw [circulant_def, circulant_def, CGraph.circulant_congr n S T h]

/-- A repeated entry in the connection set is inert. -/
@[simp] theorem circulant_dup_cons (n k : ℕ) (S : List ℕ) :
    circulant n (k :: k :: S) = circulant n (k :: S) := by
  rw [circulant_def, circulant_def, CGraph.circulant_dup_cons]

/-- The connection set may be negated entry by entry.  Not a `simp` lemma: it would loop. -/
theorem circulant_neg_cons (n k : ℕ) (hk : k ≤ n) (S : List ℕ) :
    circulant n (k :: S) = circulant n ((n - k) :: S) := by
  rw [circulant_def, circulant_def, CGraph.circulant_neg_cons n k hk]

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
    circulant (2 * (m + 1)) [m + 1] = cartesianProduct (empty (m + 1)) (complete 2) := by
  rw [circulant_def, empty_def, complete_def, cartesianProduct_mk]
  exact Quotient.sound ⟨(CGraph.Iso.circulantMatching m).symm⟩

/-- The `m = 0` case of both readings: one edge. -/
theorem circulant_two_one : circulant 2 [1] = complete 2 := by
  rw [circulant_one, cycle_two]

/-! ## Paley graphs -/

/-- The nonzero squares mod `5` are `{1, 4} = {±1}`, so `Paley(5)` is the pentagon — and the
identity map on `Fin 5` is already the isomorphism. -/
theorem paley_five : paley 5 = cycle 5 := by
  rw [paley_def, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.paley 5) (H := CGraph.cycle 5) (Equiv.refl (Fin 5)) (by decide)⟩

/-- `Paley(13)` and `Paley(17)` as circulants: their connection sets are the nonzero squares,
`{±1, ±3, ±4}` and `{±1, ±2, ±4, ±8}`, and `ofRel` symmetrises the rest. -/
theorem paley_thirteen_eq_circulant : paley 13 = circulant 13 [1, 3, 4] := by
  rw [paley_def, circulant_def, CGraph.paley_thirteen_eq_circulant]

theorem paley_seventeen_eq_circulant : paley 17 = circulant 17 [1, 2, 4, 8] := by
  rw [paley_def, circulant_def, CGraph.paley_seventeen_eq_circulant]

/-- **Paley graphs are self-complementary**, because multiplication by a non-residue exchanges
the squares with the non-squares.  The general statement needs the multiplicative structure of
`GF(q)`; these two are the witnesses `x ↦ 2x` mod `13` and `x ↦ 3x` mod `17`. -/
@[simp] theorem compl_paley_thirteen : compl (paley 13) = paley 13 := by
  rw [paley_def, compl_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleyThirteenIso.symm⟩

@[simp] theorem compl_paley_seventeen : compl (paley 17) = paley 17 := by
  rw [paley_def, compl_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleySeventeenIso.symm⟩

/-- **`paley 9` is not the Paley graph of order 9.**  `CGraph.paley` reads its differences in
`ZMod q`, which is a field only for prime `q`; at `q = 9` the squares are `{0, 1, 4, 7}`, so the
graph joins `x` to `y` exactly when `x - y` is not a multiple of `3` and one gets the complete
tripartite graph `K₃,₃,₃` rather than the rook's graph `R(3, 3)` that `GF(9)` would give. -/
theorem compl_paley_nine :
    compl (paley 9) = disjUnion (complete 3) (disjUnion (complete 3) (complete 3)) := by
  rw [paley_def, compl_mk, complete_def, disjUnion_mk, disjUnion_mk]
  exact Quotient.sound ⟨CGraph.Iso.paleyNineIso.symm⟩

theorem paley_nine : paley 9 = completeMultipartite [3, 3, 3] := by
  have h : compl (completeMultipartite [3, 3, 3])
      = disjUnion (complete 3) (disjUnion (complete 3) (complete 3)) := by
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
theorem triangular_eq_compl_kneser (n : ℕ) : triangular n = compl (kneser n 2) := by
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
    kneser 4 2 = disjUnion (complete 2) (disjUnion (complete 2) (complete 2)) := by
  rw [kneser_def, complete_def, disjUnion_mk, disjUnion_mk]
  symm
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.disjUnion (CGraph.complete 2)
      (CGraph.disjUnion (CGraph.complete 2) (CGraph.complete 2)))
    (H := CGraph.kneser 4 2)
    (Equiv.ofBijective kneserFourTwoMap (by decide)) (by decide)⟩

theorem triangular_four : triangular 4 = cocktailParty 3 := by
  have h : compl (cocktailParty 3)
      = disjUnion (complete 2) (disjUnion (complete 2) (complete 2)) := by
    show compl (completeMultipartite [2, 2, 2]) = _
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
    hypercube (n + 1) = cartesianProduct (hypercube n) (complete 2) := by
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
already an equality of `CGraph`s (see the `CGraph` section above), so the proofs here only have to
move the identity across the quotient. -/

@[simp] theorem tadpole_zero (m : ℕ) : tadpole m 0 = cycle m := by
  rw [tadpole_def, cycle_def, CGraph.tadpole_zero]

@[simp] theorem tadpole_zero_left (k : ℕ) : tadpole 0 k = path k := by
  rw [tadpole_def, path_def, CGraph.tadpole_zero_left]

@[simp] theorem tadpole_one (k : ℕ) : tadpole 1 k = path (1 + k) := by
  rw [tadpole_def, path_def, CGraph.tadpole_one]

@[simp] theorem lollipop_zero (m : ℕ) : lollipop m 0 = complete m := by
  rw [lollipop_def, complete_def, CGraph.lollipop_zero]

@[simp] theorem lollipop_zero_left (k : ℕ) : lollipop 0 k = path k := by
  rw [lollipop_def, path_def, CGraph.lollipop_zero_left]

@[simp] theorem lollipop_one (k : ℕ) : lollipop 1 k = path (1 + k) := by
  rw [lollipop_def, path_def, CGraph.lollipop_one]

/-- On two or three vertices a clique is a cycle, so the lollipop and the tadpole coincide.  Which
side is the normal form is a matter of taste, so neither of these is a `simp` lemma. -/
theorem lollipop_two_eq_tadpole (k : ℕ) : lollipop 2 k = tadpole 2 k := by
  rw [lollipop_def, tadpole_def, CGraph.lollipop_two]

theorem lollipop_three_eq_tadpole (k : ℕ) : lollipop 3 k = tadpole 3 k := by
  rw [lollipop_def, tadpole_def, CGraph.lollipop_three]

@[simp] theorem spider_singleton (k : ℕ) : spider [k] = path (1 + k) := by
  rw [spider_def, path_def, CGraph.spider_singleton]

@[simp] theorem spider_zero_cons (ks : List ℕ) : spider (0 :: ks) = spider ks := by
  rw [spider_def, spider_def, CGraph.spider_zero_cons]

/-- The general form of `spider_zero_cons`.  It is not a `simp` lemma: its left-hand side is an
append, which does not match a spider given by a list literal. -/
theorem spider_append_zero_cons (pre post : List ℕ) :
    spider (pre ++ 0 :: post) = spider (pre ++ post) := by
  rw [spider_def, spider_def, CGraph.spider_append_zero_cons]

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

@[simp] theorem spider_replicate_zero (j : ℕ) : spider (List.replicate j 0) = empty 1 := by
  rw [spider_def, empty_def, CGraph.spider_replicate_zero]

@[simp] theorem spider_nil : spider [] = empty 1 := spider_replicate_zero 0

@[simp] theorem cyclePendant_replicate_zero (m j : ℕ) :
    cyclePendant m (List.replicate j 0) = cycle m := by
  rw [cyclePendant_def, cycle_def, CGraph.cyclePendant_replicate_zero]

@[simp] theorem cyclePendant_nil (m : ℕ) : cyclePendant m [] = cycle m :=
  cyclePendant_replicate_zero m 0

@[simp] theorem cyclePendant_append_zero (m : ℕ) (ks : List ℕ) :
    cyclePendant m (ks ++ [0]) = cyclePendant m ks := by
  rw [cyclePendant_def, cyclePendant_def, CGraph.cyclePendant_append_zero]

@[simp] theorem thetaGraph_zero_zero_cons (ks : List ℕ) :
    thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks) := by
  rw [thetaGraph_def, thetaGraph_def, CGraph.thetaGraph_zero_zero_cons]

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

@[simp] theorem thetaGraph_nil : thetaGraph [] = empty 2 := by
  rw [thetaGraph_def, empty_def, CGraph.thetaGraph_nil]

/-- A theta graph all of whose paths are single edges is just that edge. -/
@[simp] theorem thetaGraph_replicate_zero (j : ℕ) :
    thetaGraph (List.replicate (j + 1) 0) = complete 2 := by
  rw [thetaGraph_def, complete_def, CGraph.thetaGraph_replicate_zero]

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

@[simp] theorem cyclePendant_singleton_one (m : ℕ) : cyclePendant m [1] = tadpole m 1 := by
  rw [cyclePendant_def, tadpole_def, CGraph.cyclePendant_singleton_one]

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
  split_ifs <;>
    (try simp only [false_or, and_true, or_false, or_true, or_self]) <;> omega

/-- A lollipop whose clique is `K₂` is a path. -/
@[simp] theorem lollipop_two (k : ℕ) : lollipop 2 k = path (2 + k) := by
  rw [lollipop_two_eq_tadpole, tadpole_two]

/-! ## Products

The one-vertex graph is a unit for the cartesian, strong and lexicographic products and an
absorbing element for the tensor product, which has no edges as soon as one factor has none.
`empty 1` rather than `complete 1` throughout: the two are equal, and `complete_one` puts
`empty 1` in `simp` normal form. -/

theorem cartesianProduct_comm (G H : IsoGraph) : cartesianProduct G H = cartesianProduct H G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.cartesianProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.cartesianProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.cartesianProductComm _ _⟩

theorem tensorProduct_comm (G H : IsoGraph) : tensorProduct G H = tensorProduct H G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.tensorProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.tensorProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.tensorProductComm _ _⟩

theorem strongProduct_comm (G H : IsoGraph) : strongProduct G H = strongProduct H G := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      show (⟦CGraph.strongProduct g.canonicalize h.canonicalize⟧ : IsoGraph)
        = ⟦CGraph.strongProduct h.canonicalize g.canonicalize⟧
      exact Quotient.sound ⟨CGraph.Iso.strongProductComm _ _⟩

@[simp] theorem cartesianProduct_empty_one (G : IsoGraph) : cartesianProduct G (empty 1) = G := by
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

@[simp] theorem empty_one_cartesianProduct (G : IsoGraph) : cartesianProduct (empty 1) G = G := by
  rw [cartesianProduct_comm, cartesianProduct_empty_one]

@[simp] theorem strongProduct_empty_one (G : IsoGraph) : strongProduct G (empty 1) = G := by
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

@[simp] theorem empty_one_strongProduct (G : IsoGraph) : strongProduct (empty 1) G = G := by
  rw [strongProduct_comm, strongProduct_empty_one]

@[simp] theorem lexProduct_empty_one (G : IsoGraph) : lexProduct G (empty 1) = G := by
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

@[simp] theorem empty_one_lexProduct (G : IsoGraph) : lexProduct (empty 1) G = G := by
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
    cartesianProduct (empty m) (empty n) = empty (m * n) := by
  rw [empty_def, empty_def, cartesianProduct_mk,
    mk_eq_empty (G := CGraph.cartesianProduct (CGraph.empty m) (CGraph.empty n)) (by simp)]
  simp

/-- The tensor product with an edgeless graph is edgeless. -/
@[simp] theorem tensorProduct_empty (G : IsoGraph) (n : ℕ) :
    tensorProduct G (empty n) = empty (G.V * n) := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, tensorProduct_mk,
      mk_eq_empty (G := CGraph.tensorProduct g.canonicalize (CGraph.empty n)) (by simp)]
    simp

@[simp] theorem empty_tensorProduct (n : ℕ) (G : IsoGraph) :
    tensorProduct (empty n) G = empty (n * G.V) := by
  rw [tensorProduct_comm, tensorProduct_empty, Nat.mul_comm]

/-- The strong product of complete graphs is complete. -/
@[simp] theorem strongProduct_complete (m n : ℕ) :
    strongProduct (complete m) (complete n) = complete (m * n) := by
  have h : ∀ x y : (CGraph.strongProduct (CGraph.complete m) (CGraph.complete n)).V, x ≠ y →
      (CGraph.strongProduct (CGraph.complete m) (CGraph.complete n)).Adj x y = true := by
    intro x y hxy
    simp [CGraph.strongProduct_adj, hxy]
  rw [complete_def, complete_def, strongProduct_mk, mk_eq_complete h]
  simp

/-- The lexicographic product of complete graphs is complete. -/
@[simp] theorem lexProduct_complete (m n : ℕ) :
    lexProduct (complete m) (complete n) = complete (m * n) := by
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
    cartesianProduct G (empty 0) = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, cartesianProduct_mk]
    haveI : IsEmpty (CGraph.cartesianProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_cartesianProduct (G : IsoGraph) :
    cartesianProduct (empty 0) G = empty 0 := by
  rw [cartesianProduct_comm, cartesianProduct_empty_zero]

@[simp] theorem strongProduct_empty_zero (G : IsoGraph) :
    strongProduct G (empty 0) = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, strongProduct_mk]
    haveI : IsEmpty (CGraph.strongProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_strongProduct (G : IsoGraph) :
    strongProduct (empty 0) G = empty 0 := by
  rw [strongProduct_comm, strongProduct_empty_zero]

@[simp] theorem lexProduct_empty_zero (G : IsoGraph) : lexProduct G (empty 0) = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    haveI : IsEmpty (CGraph.lexProduct g.canonicalize (CGraph.empty 0)).V :=
      inferInstanceAs (IsEmpty (g.canonicalize.V × (CGraph.empty 0).V))
    exact mk_eq_empty_zero

@[simp] theorem empty_zero_lexProduct (G : IsoGraph) : lexProduct (empty 0) G = empty 0 := by
  haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk]
    haveI : IsEmpty (CGraph.lexProduct (CGraph.empty 0) g.canonicalize).V :=
      inferInstanceAs (IsEmpty ((CGraph.empty 0).V × g.canonicalize.V))
    exact mk_eq_empty_zero

theorem cartesianProduct_assoc (G H K : IsoGraph) :
    cartesianProduct (cartesianProduct G H) K = cartesianProduct G (cartesianProduct H K) := by
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
    tensorProduct (tensorProduct G H) K = tensorProduct G (tensorProduct H K) := by
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
    strongProduct (strongProduct G H) K = strongProduct G (strongProduct H K) := by
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
    lexProduct (lexProduct G H) K = lexProduct G (lexProduct H K) := by
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
    cartesianProduct G (disjUnion H K)
      = disjUnion (cartesianProduct G H) (cartesianProduct G K) := by
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
    cartesianProduct (disjUnion G H) K
      = disjUnion (cartesianProduct G K) (cartesianProduct H K) := by
  rw [cartesianProduct_comm, cartesianProduct_disjUnion, cartesianProduct_comm,
    cartesianProduct_comm K H]

@[simp] theorem tensorProduct_disjUnion (G H K : IsoGraph) :
    tensorProduct G (disjUnion H K) = disjUnion (tensorProduct G H) (tensorProduct G K) := by
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
    tensorProduct (disjUnion G H) K = disjUnion (tensorProduct G K) (tensorProduct H K) := by
  rw [tensorProduct_comm, tensorProduct_disjUnion, tensorProduct_comm, tensorProduct_comm K H]

@[simp] theorem strongProduct_disjUnion (G H K : IsoGraph) :
    strongProduct G (disjUnion H K) = disjUnion (strongProduct G H) (strongProduct G K) := by
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
    strongProduct (disjUnion G H) K = disjUnion (strongProduct G K) (strongProduct H K) := by
  rw [strongProduct_comm, strongProduct_disjUnion, strongProduct_comm, strongProduct_comm K H]

/-- The lexicographic product distributes over `disjUnion` in its first factor only. -/
@[simp] theorem disjUnion_lexProduct (G H K : IsoGraph) :
    lexProduct (disjUnion G H) K = disjUnion (lexProduct G K) (lexProduct H K) := by
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
    cartesianProduct (empty 2) G = disjUnion G G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_cartesianProduct,
    empty_one_cartesianProduct]

theorem cartesianProduct_empty_two (G : IsoGraph) :
    cartesianProduct G (empty 2) = disjUnion G G := by
  rw [cartesianProduct_comm, empty_two_cartesianProduct]

theorem empty_two_strongProduct (G : IsoGraph) :
    strongProduct (empty 2) G = disjUnion G G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_strongProduct,
    empty_one_strongProduct]

theorem strongProduct_empty_two (G : IsoGraph) :
    strongProduct G (empty 2) = disjUnion G G := by
  rw [strongProduct_comm, empty_two_strongProduct]

theorem empty_two_lexProduct (G : IsoGraph) : lexProduct (empty 2) G = disjUnion G G := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ← disjUnion_empty, disjUnion_lexProduct,
    empty_one_lexProduct]

/-! ### Copies and blow-ups

`empty n □ G` is `n` disjoint copies of `G`, and `K_n[G]` is `n` copies with every pair of copies
joined; the two are complements of each other.  The complete multipartite graphs with equal parts
are exactly the blow-ups of a clique by an independent set. -/

/-- Peeling one copy off `empty (n+1) □ G`. -/
theorem empty_succ_cartesianProduct (n : ℕ) (G : IsoGraph) :
    cartesianProduct (empty (n + 1)) G = disjUnion G (cartesianProduct (empty n) G) := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1, ← disjUnion_empty, disjUnion_cartesianProduct,
    empty_one_cartesianProduct]

/-- **The lexicographic product is the one whose complement is a product of complements.** -/
@[simp] theorem compl_lexProduct (G H : IsoGraph) :
    compl (lexProduct G H) = lexProduct (compl G) (compl H) := by
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
    lexProduct (empty n) G = cartesianProduct (empty n) G := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, lexProduct_mk, cartesianProduct_mk]
    exact Quotient.sound ⟨CGraph.Iso.emptyLexProduct _ _⟩

/-- And so does the strong product. -/
theorem empty_strongProduct (n : ℕ) (G : IsoGraph) :
    strongProduct (empty n) G = cartesianProduct (empty n) G := by
  induction G using Quotient.inductionOn with
  | h g =>
    rw [← mk_canonicalize g, empty_def, strongProduct_mk, cartesianProduct_mk]
    exact Quotient.sound ⟨CGraph.Iso.emptyStrongProduct _ _⟩

/-- `K_m[G]` is `m` copies of `G` with every pair of copies joined — the complement of `m` disjoint
copies of `compl G`. -/
theorem complete_lexProduct (m : ℕ) (G : IsoGraph) :
    lexProduct (complete m) G = compl (cartesianProduct (empty m) (compl G)) := by
  conv_lhs => rw [← compl_compl (lexProduct (complete m) G)]
  rw [compl_lexProduct, compl_complete, empty_lexProduct]

/-- The complement of a complete multipartite graph with `m` equal parts is `m` disjoint cliques. -/
theorem compl_completeMultipartite_replicate (m d : ℕ) :
    compl (completeMultipartite (List.replicate m d))
      = cartesianProduct (empty m) (complete d) := by
  induction m with
  | zero =>
    rw [List.replicate_zero, completeMultipartite_nil, compl_empty, complete_zero,
      empty_zero_cartesianProduct]
  | succ m ih =>
    rw [List.replicate_succ, compl_completeMultipartite_cons, ih, empty_succ_cartesianProduct]

/-- **Equal parts make a blow-up**: `K_{m×d}` is `K_m` with each vertex blown up to `d`
independent ones. -/
theorem completeMultipartite_replicate (m d : ℕ) :
    completeMultipartite (List.replicate m d) = lexProduct (complete m) (empty d) := by
  rw [complete_lexProduct, compl_empty, ← compl_completeMultipartite_replicate, compl_compl]

/-- `paley 9` is `K₃` with every vertex blown up to three. -/
theorem paley_nine_eq_lexProduct : paley 9 = lexProduct (complete 3) (empty 3) := by
  rw [paley_nine, show ([3, 3, 3] : List ℕ) = List.replicate 3 3 from rfl,
    completeMultipartite_replicate]

/-- The complement of the cocktail-party graph is a perfect matching. -/
theorem compl_cocktailParty (n : ℕ) :
    compl (cocktailParty n) = cartesianProduct (empty n) (complete 2) :=
  compl_completeMultipartite_replicate n 2

/-- The cocktail party graph is the complement of a perfect matching, and the matching is a
circulant. -/
theorem compl_cocktailParty_eq_circulant (m : ℕ) :
    compl (cocktailParty (m + 1)) = circulant (2 * (m + 1)) [m + 1] := by
  rw [compl_cocktailParty, circulant_matching]

theorem cocktailParty_eq_lexProduct (m : ℕ) :
    cocktailParty m = lexProduct (complete m) (empty 2) :=
  completeMultipartite_replicate m 2

/-- The balanced complete bipartite graph is the two-part blow-up. -/
theorem bipartite_self_eq_lexProduct (n : ℕ) :
    bipartite n n = lexProduct (complete 2) (empty n) := by
  rw [← completeMultipartite_replicate 2 n, show List.replicate 2 n = [n, n] from rfl,
    completeMultipartite_pair]

/-- The lexicographic product distributes over `join` in its first factor, for the same reason it
distributes over `disjUnion`: the two are exchanged by complementation. -/
theorem join_lexProduct (G H K : IsoGraph) :
    lexProduct (join G H) K = join (lexProduct G K) (lexProduct H K) := by
  conv_lhs => rw [← compl_compl (lexProduct (join G H) K)]
  rw [compl_lexProduct, compl_join, disjUnion_lexProduct, ← compl_lexProduct G K,
    ← compl_lexProduct H K, ← join_def]

@[simp] theorem lexProduct_empty (m n : ℕ) : lexProduct (empty m) (empty n) = empty (m * n) := by
  rw [empty_lexProduct, cartesianProduct_empty]

@[simp] theorem strongProduct_empty (m n : ℕ) :
    strongProduct (empty m) (empty n) = empty (m * n) := by
  rw [empty_strongProduct, cartesianProduct_empty]

/-- **Blowing up a complete multipartite graph multiplies its parts.**  Replacing every vertex by
`d` independent ones keeps the graph complete multipartite, with each part `d` times as large. -/
theorem lexProduct_completeMultipartite_empty (ds : List ℕ) (d : ℕ) :
    lexProduct (completeMultipartite ds) (empty d) = completeMultipartite (ds.map (· * d)) := by
  induction ds with
  | nil => rw [List.map_nil, completeMultipartite_nil, empty_zero_lexProduct]
  | cons a ds ih =>
    rw [completeMultipartite_cons, join_lexProduct, ih, lexProduct_empty, List.map_cons,
      completeMultipartite_cons]

/-- The two-part case: blowing up `K_{a,b}` gives `K_{ad,bd}`. -/
theorem bipartite_mul (a b d : ℕ) :
    bipartite (a * d) (b * d) = lexProduct (bipartite a b) (empty d) := by
  rw [← completeMultipartite_pair, ← completeMultipartite_pair,
    lexProduct_completeMultipartite_empty]
  rfl

/-- **`Q_{m+n} = Q_m □ Q_n`**: splitting a bit-string of length `m + n` into its first `m` and
last `n` bits.  Iterating `hypercube_succ` is all it takes. -/
theorem hypercube_add (m n : ℕ) :
    hypercube (m + n) = cartesianProduct (hypercube m) (hypercube n) := by
  induction n with
  | zero => rw [Nat.add_zero, hypercube_zero, cartesianProduct_empty_one]
  | succ n ih =>
    rw [← Nat.add_assoc, hypercube_succ, ih, cartesianProduct_assoc, ← hypercube_succ]

/-- `Q₄` is the `4 × 4` torus. -/
theorem hypercube_four : hypercube 4 = cartesianProduct (cycle 4) (cycle 4) := by
  rw [show hypercube 4 = hypercube (2 + 2) from rfl, hypercube_add, hypercube_two]

/-! ### Rooks and ladders -/

theorem rook_one_left (n : ℕ) : rook 1 n = complete n := by
  show cartesianProduct (complete 1) (complete n) = complete n
  rw [complete_one, empty_one_cartesianProduct]

theorem rook_one_right (m : ℕ) : rook m 1 = complete m := by
  show cartesianProduct (complete m) (complete 1) = complete m
  rw [complete_one, cartesianProduct_empty_one]

theorem rook_comm (m n : ℕ) : rook m n = rook n m := cartesianProduct_comm _ _

/-- The `2 × 2` rook's graph is the square. -/
theorem rook_two_two : rook 2 2 = cycle 4 := by
  show cartesianProduct (complete 2) (complete 2) = cycle 4
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
    compl (rook m n) = tensorProduct (complete m) (complete n) := by
  have hrook : (rook m n : IsoGraph) = ⟦CGraph.rook m n⟧ := by
    rw [show (rook m n : IsoGraph) = cartesianProduct (complete m) (complete n) from rfl,
      complete_def, complete_def, cartesianProduct_mk]
  rw [hrook, compl_mk, CGraph.compl_rook, complete_def, complete_def, tensorProduct_mk]

/-- `K₂ × K₂` is a perfect matching: the tensor product keeps only the two "diagonal" moves. -/
theorem tensorProduct_complete_two_two :
    tensorProduct (complete 2) (complete 2) = disjUnion (complete 2) (complete 2) := by
  rw [← compl_rook, rook_two_two, compl_cycle_four]

@[simp] theorem rook_zero_left (n : ℕ) : rook 0 n = empty 0 := by
  show cartesianProduct (complete 0) (complete n) = empty 0
  rw [complete_zero, empty_zero_cartesianProduct]

@[simp] theorem rook_zero_right (m : ℕ) : rook m 0 = empty 0 := by
  show cartesianProduct (complete m) (complete 0) = empty 0
  rw [complete_zero, cartesianProduct_empty_zero]

/-- The two-rung ladder is the square. -/
theorem ladder_two : ladder 2 = cycle 4 := by
  show cartesianProduct (path 2) (complete 2) = cycle 4
  rw [path_two]
  exact rook_two_two

theorem ladder_one : ladder 1 = complete 2 := by
  show cartesianProduct (path 1) (complete 2) = complete 2
  rw [path_one, empty_one_cartesianProduct]

/-- The two-rung prism is the square. -/
theorem prism_two : prism 2 = cycle 4 := by
  show cartesianProduct (cycle 2) (complete 2) = cycle 4
  rw [cycle_two]
  exact rook_two_two

/-- `K₂ □ K₃` is the triangular prism. -/
theorem rook_two_three : rook 2 3 = prism 3 := by
  show cartesianProduct (complete 2) (complete 3) = cartesianProduct (cycle 3) (complete 2)
  rw [cycle_three, cartesianProduct_comm]

/-- The complement of the hexagon is the triangular prism: `i ~ i + 2` gives the two triangles and
`i ~ i + 3` the matching between them. -/
theorem compl_cycle_six : compl (cycle 6) = prism 3 := by
  show compl (cycle 6) = cartesianProduct (cycle 3) (complete 2)
  rw [cycle_def, compl_mk, cycle_def, complete_def, cartesianProduct_mk]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.compl (CGraph.cycle 6))
    (H := CGraph.cartesianProduct (CGraph.cycle 3) (CGraph.complete 2))
    (⟨![(0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1)],
      fun p ↦ ![![0, 3], ![2, 5], ![4, 1]] p.1 p.2, by decide, by decide⟩ :
        Fin 6 ≃ (Fin 3 × Fin 2))
    (by decide)⟩

theorem compl_prism_three : compl (prism 3) = cycle 6 := by
  rw [← compl_cycle_six, compl_compl]

/-- The cube graph is the four-rung prism. -/
theorem hypercube_three : hypercube 3 = prism 4 := by
  show hypercube 3 = cartesianProduct (cycle 4) (complete 2)
  rw [hypercube_succ, hypercube_two]

/-! ### Bipartiteness

A proper two-colouring is exactly what makes the bipartite double cover of the next section
split, so the two belong together: the colourings are built here and cashed in there. -/

@[simp] theorem isBipartite_disjUnion {G H : IsoGraph} (hG : IsBipartite G) (hH : IsBipartite H) :
    IsBipartite (disjUnion G H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  exact CGraph.IsBipartite.disjUnion hG hH

@[simp] theorem isBipartite_cartesianProduct {G H : IsoGraph} (hG : IsBipartite G) (hH : IsBipartite H) :
    IsBipartite (cartesianProduct G H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk]
  exact CGraph.IsBipartite.cartesianProduct hG hH

/-- A disjoint union is bipartite exactly when both summands are. -/
@[simp] theorem isBipartite_disjUnion_iff {G H : IsoGraph} :
    IsBipartite (disjUnion G H) ↔ IsBipartite G ∧ IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [disjUnion_mk, isBipartite_mk, isBipartite_mk, isBipartite_mk]
  exact ⟨fun h ↦ ⟨h.of_disjUnion_left, h.of_disjUnion_right⟩,
    fun h ↦ CGraph.IsBipartite.disjUnion h.1 h.2⟩

/-- A Cartesian product of nonempty graphs is bipartite exactly when both factors are. -/
theorem isBipartite_cartesianProduct_iff {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsBipartite (cartesianProduct G H) ↔ IsBipartite G ∧ IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk, isBipartite_mk, isBipartite_mk, isBipartite_mk]
  have hG' : Nonempty G.canonicalize.V := Fintype.card_pos_iff.1 hG
  have hH' : Nonempty H.canonicalize.V := Fintype.card_pos_iff.1 hH
  exact ⟨fun h ↦ ⟨h.of_cartesianProduct_left hH', h.of_cartesianProduct_right hG'⟩,
    fun h ↦ CGraph.IsBipartite.cartesianProduct h.1 h.2⟩

theorem isBipartite_tensorProduct_left {G H : IsoGraph} (hG : IsBipartite G) :
    IsBipartite (tensorProduct G H) := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [tensorProduct_mk]
  exact CGraph.IsBipartite.tensorProduct_left hG

theorem isBipartite_tensorProduct_right {G H : IsoGraph} (hH : IsBipartite H) :
    IsBipartite (tensorProduct G H) := by
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

theorem not_isBipartite_complete (n : ℕ) : ¬ IsBipartite (complete (n + 3)) := by
  rw [complete_def, isBipartite_mk]
  exact CGraph.not_isBipartite_complete n

theorem not_isBipartite_complete_three : ¬ IsBipartite (complete 3) := not_isBipartite_complete 0

/-- **Odd cycles are not bipartite.** -/
theorem not_isBipartite_cycle_odd (m : ℕ) : ¬ IsBipartite (cycle (2 * m + 3)) := by
  rw [cycle_def, isBipartite_mk]
  exact CGraph.not_isBipartite_cycle_odd m

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
  have h1 := CGraph.sub_mod_cases x.isLt y.isLt
  have h2 := CGraph.sub_mod_cases y.isLt x.isLt
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
  show ¬ IsBipartite (cartesianProduct (complete (m + 3)) (complete (n + 1)))
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_complete m h.1

/-- A prism over an odd cycle is not bipartite. -/
@[simp] theorem not_isBipartite_prism_odd (m : ℕ) : ¬ IsBipartite (prism (2 * m + 3)) := by
  show ¬ IsBipartite (cartesianProduct (cycle (2 * m + 3)) (complete 2))
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_cycle_odd m h.1

/-- **Kneser graphs with room for three disjoint blocks are not bipartite.** -/
@[simp] theorem not_isBipartite_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    ¬ IsBipartite (kneser n k) := by
  rw [kneser_def, isBipartite_mk]
  exact CGraph.not_isBipartite_kneser hk h

/-- **Johnson graphs on at least `k + 2` points are not bipartite.** -/
@[simp] theorem not_isBipartite_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    ¬ IsBipartite (johnson n k) := by
  rw [johnson_def, isBipartite_mk]
  exact CGraph.not_isBipartite_johnson hk h

/-- Triangular graphs on at least four points contain a triangle. -/
theorem not_isBipartite_triangular {n : ℕ} (h : 4 ≤ n) : ¬ IsBipartite (triangular n) :=
  not_isBipartite_johnson (by omega) (by omega)

/-- **The Petersen graph is not bipartite**: it is triangle-free, but it has a five-cycle. -/
@[simp] theorem not_isBipartite_petersen : ¬ IsBipartite petersen := by
  show ¬ IsBipartite (kneser 5 2)
  rw [kneser_def, isBipartite_mk]
  exact CGraph.not_isBipartite_kneser_five_two

/-- A side of a bipartite join is bipartite. -/
theorem IsBipartite.of_join_left {G H : IsoGraph} (h : IsBipartite (join G H)) : IsBipartite G := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [join_mk, isBipartite_mk] at h
  rw [isBipartite_mk]
  exact h.of_join_left

theorem IsBipartite.of_join_right {G H : IsoGraph} (h : IsBipartite (join G H)) :
    IsBipartite H := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [join_mk, isBipartite_mk] at h
  rw [isBipartite_mk]
  exact h.of_join_right

theorem not_isBipartite_join_left {G H : IsoGraph} (hG : ¬ IsBipartite G) :
    ¬ IsBipartite (join G H) := fun h ↦ hG h.of_join_left

theorem not_isBipartite_join_right {G H : IsoGraph} (hH : ¬ IsBipartite H) :
    ¬ IsBipartite (join G H) := fun h ↦ hH h.of_join_right

/-- **A join of three nonempty graphs is never bipartite.** -/
theorem not_isBipartite_join_join {G H K : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hK : 0 < K.V) : ¬ IsBipartite (join G (join H K)) := by
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
  show ¬ IsBipartite (join (complete 1) (path (n + 2)))
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
    tensorProduct (complete 2) ⟦G⟧ = disjUnion ⟦G⟧ ⟦G⟧ := by
  rw [← empty_two_cartesianProduct ⟦G⟧, complete_def, tensorProduct_mk, empty_def,
    cartesianProduct_mk]
  exact Quotient.sound ⟨CGraph.Iso.tensorTwoOfColouring G c h⟩

/-- **The double cover of a bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    tensorProduct (complete 2) G = disjUnion G G := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [← mk_canonicalize G] at *
  obtain ⟨c, hc⟩ := h
  exact tensorProduct_complete_two_of_colouring _ c hc

theorem tensorProduct_complete_two_hypercube (n : ℕ) :
    tensorProduct (complete 2) (hypercube n) = disjUnion (hypercube n) (hypercube n) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_hypercube n)

theorem tensorProduct_complete_two_prism (m : ℕ) :
    tensorProduct (complete 2) (prism (2 * m)) = disjUnion (prism (2 * m)) (prism (2 * m)) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_prism_even m)

/-- **The double cover of a path is two paths.** -/
theorem tensorProduct_complete_two_path (n : ℕ) :
    tensorProduct (complete 2) (path n) = disjUnion (path n) (path n) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_path n)

/-- **The double cover of an even cycle is two cycles.** -/
theorem tensorProduct_complete_two_cycle (m : ℕ) :
    tensorProduct (complete 2) (cycle (2 * m)) = disjUnion (cycle (2 * m)) (cycle (2 * m)) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_cycle_even m)

/-- **The double cover of a complete bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_bipartite (m n : ℕ) :
    tensorProduct (complete 2) (bipartite m n) = disjUnion (bipartite m n) (bipartite m n) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_bipartite m n)

/-- The double cover of a star is two stars. -/
theorem tensorProduct_complete_two_star (n : ℕ) :
    tensorProduct (complete 2) (star n) = disjUnion (star n) (star n) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_star n)

/-- **The double cover of a ladder is two ladders.** -/
theorem tensorProduct_complete_two_ladder (n : ℕ) :
    tensorProduct (complete 2) (ladder n) = disjUnion (ladder n) (ladder n) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_ladder n)

/-- **The double cover of an odd cycle is one cycle of twice the length.**  The bound starts at
`C₃`: `cycle 1` is edgeless, so its double cover is too, while `cycle 2` is an edge. -/
theorem tensorProduct_complete_two_cycle_odd (m : ℕ) :
    tensorProduct (complete 2) (cycle (2 * m + 3)) = cycle (2 * (2 * m + 3)) := by
  rw [complete_def, cycle_def, tensorProduct_mk, cycle_def]
  exact Quotient.sound ⟨(CGraph.Iso.cycleTensorTwo m).symm⟩

theorem tensorProduct_complete_two_cycle_three :
    tensorProduct (complete 2) (cycle 3) = cycle 6 :=
  tensorProduct_complete_two_cycle_odd 0

theorem tensorProduct_complete_two_cycle_five :
    tensorProduct (complete 2) (cycle 5) = cycle 10 :=
  tensorProduct_complete_two_cycle_odd 1

/-! ## Line graphs and Mycielskians

The line graph turns a graph's edges into vertices, so the identities here are counted by `E`
rather than `V`: `lineGraph (star n)` is complete on `E (star n) = n` vertices, and
`lineGraph (complete n)` is the triangular graph `T(n) = J(n, 2)` on `C(n, 2)` of them. -/

/-- **The line graph of a disjoint union is the disjoint union of the line graphs.** -/
@[simp] theorem lineGraph_disjUnion (G H : IsoGraph) :
    lineGraph (disjUnion G H) = disjUnion (lineGraph G) (lineGraph H) := by
  induction G using Quotient.inductionOn with
  | h g =>
    induction H using Quotient.inductionOn with
    | h h =>
      rw [← mk_canonicalize g, ← mk_canonicalize h, disjUnion_mk, lineGraph_mk, lineGraph_mk,
        lineGraph_mk, disjUnion_mk]
      exact Quotient.sound ⟨CGraph.Iso.lineGraphDisjUnion _ _⟩

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

/-- Every edge of a star contains the centre, so any two of them meet: the line graph of a star
is complete. -/
@[simp] theorem lineGraph_star (n : ℕ) : lineGraph (star n) = complete n := by
  obtain ⟨c, hcentre⟩ : ∃ c : (CGraph.star n).V, ∀ e : (CGraph.lineGraph (CGraph.star n)).V,
      c ∈ (e.1 : Sym2 (CGraph.star n).V) := by
    refine ⟨(Sum.inl 0 : Fin 1 ⊕ Fin n), ?_⟩
    rintro ⟨e, he⟩
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [SimpleGraph.mem_edgeSet] at he
      rcases a with x | x <;> rcases b with y | y
      · exact absurd he (by simp [CGraph.toSimple, CGraph.star])
      · exact (Subsingleton.elim (0 : Fin 1) x) ▸ Sym2.mem_mk_left _ _
      · exact (Subsingleton.elim (0 : Fin 1) y) ▸ Sym2.mem_mk_right _ _
      · exact absurd he (by simp [CGraph.toSimple, CGraph.star])
  have h : ∀ e f : (CGraph.lineGraph (CGraph.star n)).V, e ≠ f →
      (CGraph.lineGraph (CGraph.star n)).Adj e f = true := by
    intro e f hef
    rw [CGraph.lineGraph_adj, decide_eq_true hef, Bool.true_and, decide_eq_true_eq]
    exact ⟨c, hcentre e, hcentre f⟩
  rw [star_def, lineGraph_mk, mk_eq_complete h, CGraph.card_lineGraph, CGraph.E_star]

/-- **The line graph of a complete graph is the triangular graph.**  An edge of `Kₙ` is a
two-element subset of `Fin n`, and two distinct such subsets meet exactly when they meet in
*one* point — which is the adjacency of `J(n, 2)`. -/
@[simp] theorem lineGraph_complete (n : ℕ) : lineGraph (complete n) = johnson n 2 := by
  have hcard : ∀ e : (CGraph.lineGraph (CGraph.complete n)).V,
      (e.1 : Sym2 (Fin n)).toFinset.card = 2 := by
    rintro ⟨e, he⟩
    exact Sym2.card_toFinset_of_not_isDiag e (SimpleGraph.not_isDiag_of_mem_edgeSet _ he)
  set F : (CGraph.lineGraph (CGraph.complete n)).V → (CGraph.johnson n 2).V :=
    fun e ↦ ⟨(e.1 : Sym2 (Fin n)).toFinset, hcard e⟩ with hF
  have hmem : ∀ (e : (CGraph.lineGraph (CGraph.complete n)).V) (v : Fin n),
      v ∈ (F e).1 ↔ v ∈ (e.1 : Sym2 (Fin n)) := fun _ _ ↦ Sym2.mem_toFinset
  have hinj : Function.Injective F := by
    rintro ⟨e, he⟩ ⟨f, hf⟩ hef
    refine Subtype.ext ?_
    revert he hf hef
    induction e using Sym2.ind with
    | _ a b =>
      induction f using Sym2.ind with
      | _ c d =>
        intro he hf hef
        have hab : a ≠ b := by
          simpa [CGraph.toSimple] using SimpleGraph.not_isDiag_of_mem_edgeSet _ he
        have hset : ({a, b} : Finset (Fin n)) = {c, d} := by
          simpa [hF, Sym2.toFinset_mk_eq] using congrArg Subtype.val hef
        have ha : a = c ∨ a = d := by
          have hmem : a ∈ ({c, d} : Finset (Fin n)) := by rw [← hset]; simp
          simpa using hmem
        have hb : b = c ∨ b = d := by
          have hmem : b ∈ ({c, d} : Finset (Fin n)) := by rw [← hset]; simp
          simpa using hmem
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · exact absurd rfl hab
          · rfl
        · rcases hb with rfl | rfl
          · exact Sym2.eq_swap
          · exact absurd rfl hab
  have hsurj : Function.Surjective F := by
    rintro ⟨s, hs⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
    refine ⟨⟨s(a, b), ?_⟩, ?_⟩
    · show (CGraph.complete n).toSimple.Adj a b
      simpa [CGraph.toSimple] using hab
    · exact Subtype.ext (by simpa [hF] using Sym2.toFinset_mk_eq (x := a) (y := b))
  have hadj : ∀ e f, (CGraph.johnson n 2).Adj (F e) (F f)
      = (CGraph.lineGraph (CGraph.complete n)).Adj e f := by
    intro e f
    rw [CGraph.johnson_adj, CGraph.lineGraph_adj]
    by_cases hef : e = f
    · subst hef
      simp
    · rw [decide_eq_true hef, decide_eq_true (show F e ≠ F f from fun h ↦ hef (hinj h)),
        Bool.true_and, Bool.true_and,
        show (((F e).1 ∩ (F f).1).card == 2 - 1)
          = decide (((F e).1 ∩ (F f).1).card = 1) from
          Bool.beq_eq_decide_eq _ _]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · intro hone
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
        have hv' : v ∈ (F e).1 ∩ (F f).1 := by rw [hv]; simp
        rw [Finset.mem_inter] at hv'
        exact ⟨v, (hmem e v).1 hv'.1, (hmem f v).1 hv'.2⟩
      · rintro ⟨v, hv1, hv2⟩
        have hvmem : v ∈ (F e).1 ∩ (F f).1 :=
          Finset.mem_inter.2 ⟨(hmem e v).2 hv1, (hmem f v).2 hv2⟩
        have hpos : 1 ≤ ((F e).1 ∩ (F f).1).card := Finset.card_pos.2 ⟨v, hvmem⟩
        have hle : ((F e).1 ∩ (F f).1).card ≤ 2 :=
          le_of_le_of_eq (Finset.card_le_card Finset.inter_subset_left) (F e).2
        have hne2 : ((F e).1 ∩ (F f).1).card ≠ 2 := by
          intro htwo
          have h1 : (F e).1 ∩ (F f).1 = (F e).1 :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [htwo, (F e).2])
          have h2 : (F e).1 ∩ (F f).1 = (F f).1 :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [htwo, (F f).2])
          exact hef (hinj (Subtype.ext (h1.symm.trans h2)))
        omega
  rw [complete_def, lineGraph_mk, johnson_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj (Equiv.ofBijective F ⟨hinj, hsurj⟩) hadj⟩

/-- The same statement under the other name for `J(n, 2)`. -/
theorem lineGraph_complete_eq_triangular (n : ℕ) : lineGraph (complete n) = triangular n :=
  lineGraph_complete n

/-! ### Edge counts

`V_*` reads the vertex count of every family off its `CGraph` counterpart; these do the same for
the edge count.  The operations all follow the same script: push the quotient through with
`mk_canonicalize`, replace the constructor by its `CGraph` form, and apply the `CGraph` lemma. -/

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := CGraph.E_empty n

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := CGraph.E_complete n

@[simp] theorem E_path (n : ℕ) : (path (n + 1)).E = n := CGraph.E_path n

@[simp] theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := CGraph.E_cycle n

@[simp] theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := CGraph.E_bipartite m n

@[simp] theorem E_star (n : ℕ) : (star n).E = n := CGraph.E_star n

@[simp] theorem E_disjUnion (G H : IsoGraph) : (disjUnion G H).E = G.E + H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.E_disjUnion g h

/-- A graph and its complement share out all the pairs between them. -/
theorem E_compl_add (G : IsoGraph) : (compl G).E + G.E = G.V.choose 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, E_mk, E_mk, V_mk]
  exact CGraph.E_compl _

@[simp] theorem E_join (G H : IsoGraph) : (join G H).E = G.E + H.E + G.V * H.V := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_join _ _

@[simp] theorem E_cartesianProduct (G H : IsoGraph) :
    (cartesianProduct G H).E = G.V * H.E + H.V * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_cartesianProduct _ _

@[simp] theorem E_tensorProduct (G H : IsoGraph) : (tensorProduct G H).E = 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, E_mk, E_mk, E_mk]
  exact CGraph.E_tensorProduct _ _

@[simp] theorem E_mycielskian (G : IsoGraph) : (mycielskian G).E = 3 * G.E + G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, E_mk, E_mk, V_mk]
  exact CGraph.E_mycielskian _

/-- One more point adds one pair for each old point. -/
theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- Splitting `a + b` points into two groups splits the pairs into three kinds. -/
theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, choose_two_succ, choose_two_succ, ih]
    ring

/-! Derived edge counts. -/

@[simp] theorem E_wheel (n : ℕ) : (wheel (n + 3)).E = 2 * (n + 3) := by
  rw [wheel_eq_join, E_join, E_complete, E_cycle, V_complete, V_cycle]
  norm_num
  omega

theorem E_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).E + (ds.map (·.choose 2)).sum = ds.sum.choose 2 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, E_join, V_empty, V_completeMultipartite, E_empty,
      List.map_cons, List.sum_cons, List.sum_cons, choose_two_add]
    omega

/-- The hypercube is `n`-regular on `2 ^ n` vertices. -/
theorem E_hypercube (n : ℕ) : 2 * (hypercube n).E = n * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hypercube_succ, E_cartesianProduct, V_hypercube, V_complete, E_complete]
    norm_num
    ring_nf
    ring_nf at ih
    omega

@[simp] theorem E_ladder (n : ℕ) : (ladder (n + 1)).E = 3 * n + 1 := by
  show (cartesianProduct (path (n + 1)) (complete 2)).E = _
  rw [E_cartesianProduct, V_path, V_complete, E_path, E_complete]
  norm_num
  omega

@[simp] theorem E_prism (n : ℕ) : (prism (n + 3)).E = 3 * (n + 3) := by
  show (cartesianProduct (cycle (n + 3)) (complete 2)).E = _
  rw [E_cartesianProduct, V_cycle, V_complete, E_cycle, E_complete]
  norm_num
  omega

@[simp] theorem E_rook (m n : ℕ) : (rook m n).E = m * n.choose 2 + n * m.choose 2 := by
  show (cartesianProduct (complete m) (complete n)).E = _
  rw [E_cartesianProduct, V_complete, V_complete, E_complete, E_complete]

/-! ### Connectivity -/

@[simp] theorem isConnected_empty_one : IsConnected (empty 1) := CGraph.isConnected_empty_one

@[simp] theorem isConnected_complete (n : ℕ) : IsConnected (complete (n + 1)) :=
  CGraph.isConnected_complete n

@[simp] theorem isConnected_path (n : ℕ) : IsConnected (path (n + 1)) := CGraph.isConnected_path n

@[simp] theorem isConnected_cycle (n : ℕ) : IsConnected (cycle (n + 1)) :=
  CGraph.isConnected_cycle n

@[simp] theorem isConnected_bipartite (m n : ℕ) : IsConnected (bipartite (m + 1) (n + 1)) :=
  CGraph.isConnected_bipartite m n

@[simp] theorem isAcyclic_empty (n : ℕ) : IsAcyclic (empty n) := CGraph.isAcyclic_empty n

@[simp] theorem isAcyclic_path (n : ℕ) : IsAcyclic (path n) := CGraph.isAcyclic_path n

@[simp] theorem isTree_path (n : ℕ) : IsTree (path (n + 1)) := CGraph.isTree_path n

@[simp] theorem not_isAcyclic_cycle (n : ℕ) : ¬ IsAcyclic (cycle (n + 3)) :=
  CGraph.not_isAcyclic_cycle n

@[simp] theorem isConnected_star (n : ℕ) : IsConnected (star n) := by
  cases n with
  | zero => rw [star_zero]; exact isConnected_empty_one
  | succ n => exact isConnected_bipartite 0 n

/-- A disjoint union of two nonempty graphs is disconnected. -/
theorem not_isConnected_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ IsConnected (disjUnion G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, isConnected_mk]
  rw [V_mk] at hG hH
  exact CGraph.not_isConnected_disjUnion _ _ hG hH

/-- A join of two nonempty graphs is connected, whatever the two graphs are. -/
@[simp] theorem isConnected_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (join G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, isConnected_mk]
  rw [V_mk] at hG hH
  exact CGraph.isConnected_join _ _ hG hH

/-- The Cartesian product is connected exactly when both factors are. -/
@[simp] theorem isConnected_cartesianProduct {G H : IsoGraph} :
    IsConnected (cartesianProduct G H) ↔ IsConnected G ∧ IsConnected H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, isConnected_mk,
    isConnected_mk, isConnected_mk]
  exact CGraph.isConnected_cartesianProduct_iff _ _

@[simp] theorem isConnected_wheel (n : ℕ) : IsConnected (wheel (n + 1)) := by
  rw [wheel_eq_join]
  exact isConnected_join (by simp) (by simp)

@[simp] theorem isConnected_hypercube (n : ℕ) : IsConnected (hypercube n) := by
  induction n with
  | zero => rw [hypercube_zero]; exact isConnected_empty_one
  | succ n ih =>
    rw [hypercube_succ, isConnected_cartesianProduct]
    exact ⟨ih, isConnected_complete 1⟩

@[simp] theorem isConnected_ladder (n : ℕ) : IsConnected (ladder (n + 1)) := by
  show IsConnected (cartesianProduct (path (n + 1)) (complete 2))
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_path n, isConnected_complete 1⟩

@[simp] theorem isConnected_prism (n : ℕ) : IsConnected (prism (n + 1)) := by
  show IsConnected (cartesianProduct (cycle (n + 1)) (complete 2))
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_cycle n, isConnected_complete 1⟩

@[simp] theorem isConnected_rook (m n : ℕ) : IsConnected (rook (m + 1) (n + 1)) := by
  show IsConnected (cartesianProduct (complete (m + 1)) (complete (n + 1)))
  rw [isConnected_cartesianProduct]
  exact ⟨isConnected_complete m, isConnected_complete n⟩

/-! ### Trees, and Euler's count -/

theorem isTree_iff_isConnected_and_isAcyclic (G : IsoGraph) :
    IsTree G ↔ IsConnected G ∧ IsAcyclic G := by
  induction G using Quotient.inductionOn with | _ g =>
  exact SimpleGraph.isTree_iff _

/-- A graph is a tree exactly when it is connected and has one fewer edge than vertices. -/
theorem isTree_iff (G : IsoGraph) : IsTree G ↔ IsConnected G ∧ G.E + 1 = G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.isTree_iff_isConnected_and_E g

theorem IsTree.E_add_one {G : IsoGraph} (h : IsTree G) : G.E + 1 = G.V :=
  ((isTree_iff G).1 h).2

/-- A connected graph has at least one fewer edge than it has vertices. -/
theorem IsConnected.V_le_E_add_one {G : IsoGraph} (h : IsConnected G) : G.V ≤ G.E + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.IsConnected.card_le_E_add_one h

/-- Too few edges to be connected. -/
theorem not_isConnected_of_E_add_one_lt {G : IsoGraph} (h : G.E + 1 < G.V) : ¬ IsConnected G :=
  fun hc ↦ absurd hc.V_le_E_add_one (by omega)

@[simp] theorem not_isConnected_empty (n : ℕ) : ¬ IsConnected (empty (n + 2)) :=
  not_isConnected_of_E_add_one_lt (by simp)

@[simp] theorem isTree_star (n : ℕ) : IsTree (star n) := by
  rw [isTree_iff, E_star, V_star]
  exact ⟨isConnected_star n, by omega⟩

@[simp] theorem not_isTree_cycle (n : ℕ) : ¬ IsTree (cycle (n + 3)) := by
  rw [isTree_iff, E_cycle, V_cycle]
  rintro ⟨-, h⟩
  omega

@[simp] theorem not_isTree_complete (n : ℕ) : ¬ IsTree (complete (n + 3)) := by
  rw [isTree_iff, E_complete, V_complete]
  rintro ⟨-, h⟩
  rw [show n + 3 = (n + 2) + 1 from rfl, choose_two_succ] at h
  have : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  omega

@[simp] theorem not_isTree_wheel (n : ℕ) : ¬ IsTree (wheel (n + 3)) := by
  rw [isTree_iff, E_wheel, V_wheel]
  rintro ⟨-, h⟩
  omega

@[simp] theorem not_isTree_prism (n : ℕ) : ¬ IsTree (prism (n + 3)) := by
  rw [isTree_iff, E_prism]
  rintro ⟨-, h⟩
  rw [show prism (n + 3) = cartesianProduct (cycle (n + 3)) (complete 2) from rfl,
    V_cartesianProduct, V_cycle, V_complete] at h
  omega

@[simp] theorem not_isTree_ladder (n : ℕ) : ¬ IsTree (ladder (n + 2)) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, isTree_iff, E_ladder]
  rintro ⟨-, h⟩
  rw [show ladder (n + 1 + 1) = cartesianProduct (path (n + 2)) (complete 2) from rfl,
    V_cartesianProduct, V_path, V_complete] at h
  omega

/-- Anything connected that is not a tree has a cycle. -/
theorem not_isAcyclic_of_isConnected {G : IsoGraph} (hc : IsConnected G) (h : ¬ IsTree G) :
    ¬ IsAcyclic G :=
  fun ha ↦ h ((isTree_iff_isConnected_and_isAcyclic G).2 ⟨hc, ha⟩)

@[simp] theorem not_isAcyclic_complete (n : ℕ) : ¬ IsAcyclic (complete (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_complete (n + 2)) (not_isTree_complete n)

@[simp] theorem not_isAcyclic_wheel (n : ℕ) : ¬ IsAcyclic (wheel (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_wheel (n + 2)) (not_isTree_wheel n)

@[simp] theorem not_isAcyclic_prism (n : ℕ) : ¬ IsAcyclic (prism (n + 3)) :=
  not_isAcyclic_of_isConnected (isConnected_prism (n + 2)) (not_isTree_prism n)

@[simp] theorem not_isAcyclic_ladder (n : ℕ) : ¬ IsAcyclic (ladder (n + 2)) :=
  not_isAcyclic_of_isConnected (isConnected_ladder (n + 1)) (not_isTree_ladder n)

/-! ### Connectivity of the join families -/

/-- A complete multipartite graph with two nonempty parts is connected. -/
theorem isConnected_completeMultipartite (a b : ℕ) (ds : List ℕ) :
    IsConnected (completeMultipartite ((a + 1) :: (b + 1) :: ds)) := by
  rw [completeMultipartite_cons]
  exact isConnected_join (by simp) (by simp)

@[simp] theorem isConnected_book (n : ℕ) : IsConnected (book n) :=
  isConnected_completeMultipartite 0 0 [n]

@[simp] theorem isConnected_cocktailParty (n : ℕ) : IsConnected (cocktailParty (n + 2)) := by
  show IsConnected (completeMultipartite (List.replicate (n + 2) 2))
  rw [List.replicate_succ, List.replicate_succ]
  exact isConnected_completeMultipartite 1 1 _

@[simp] theorem isConnected_fan (n : ℕ) : IsConnected (fan (n + 1)) := by
  show IsConnected (join (complete 1) (path (n + 1)))
  exact isConnected_join (by simp) (by simp)

/-! ### Cliques, independent sets and diameter -/

@[simp] theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := CGraph.indepNum_empty n

@[simp] theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 :=
  CGraph.cliqueNum_empty n

@[simp] theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n :=
  CGraph.cliqueNum_complete n

@[simp] theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 :=
  CGraph.indepNum_complete n

@[simp] theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 :=
  CGraph.indepNum_cycle n

@[simp] theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n :=
  CGraph.indepNum_bipartite m n

@[simp] theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 :=
  CGraph.cliqueNum_bipartite m n

@[simp] theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 :=
  CGraph.diameter_complete n

@[simp] theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := CGraph.diameter_path n

@[simp] theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 :=
  CGraph.diameter_cycle n

@[simp] theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 :=
  CGraph.diameter_bipartite m n

@[simp] theorem indepNum_compl (G : IsoGraph) : (compl G).indepNum = G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.indepNum_compl _

@[simp] theorem cliqueNum_compl (G : IsoGraph) : (compl G).cliqueNum = G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, indepNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_compl _

@[simp] theorem indepNum_disjUnion (G H : IsoGraph) :
    (disjUnion G H).indepNum = G.indepNum + H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.indepNum_disjUnion _ _

@[simp] theorem cliqueNum_disjUnion (G H : IsoGraph) :
    (disjUnion G H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.cliqueNum_disjUnion _ _

@[simp] theorem cliqueNum_join (G H : IsoGraph) :
    (join G H).cliqueNum = G.cliqueNum + H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_join _ _

@[simp] theorem indepNum_join (G H : IsoGraph) :
    (join G H).indepNum = max G.indepNum H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, indepNum_mk, indepNum_mk, indepNum_mk]
  exact CGraph.indepNum_join _ _

@[simp] theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 :=
  CGraph.indepNum_completeMultipartite ds

@[simp] theorem indepNum_lexProduct (G H : IsoGraph) :
    (lexProduct G H).indepNum = G.indepNum * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_lexProduct _ _

@[simp] theorem cliqueNum_strongProduct (G H : IsoGraph) :
    (strongProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_strongProduct _ _

/-! Derived clique and independence numbers. -/

@[simp] theorem cliqueNum_star (n : ℕ) : (star (n + 1)).cliqueNum = 2 :=
  cliqueNum_bipartite 0 n

@[simp] theorem indepNum_star (n : ℕ) : (star n).indepNum = max 1 n := indepNum_bipartite 1 n

@[simp] theorem indepNum_wheel (n : ℕ) : (wheel (n + 3)).indepNum = (n + 3) / 2 := by
  rw [wheel_eq_join, indepNum_join, indepNum_complete, indepNum_cycle]
  omega

@[simp] theorem cliqueNum_book (n : ℕ) : (book n).cliqueNum = 2 + min n 1 := by
  rw [book_eq_join, cliqueNum_join, cliqueNum_complete, cliqueNum_empty]

@[simp] theorem indepNum_book (n : ℕ) : (book n).indepNum = max 1 n := by
  rw [book_eq_join, indepNum_join, indepNum_complete, indepNum_empty]
  norm_num

private theorem max?_replicate (a n : ℕ) : (List.replicate (n + 1) a).max? = some a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.max?_cons, ih]; simp

@[simp] theorem indepNum_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).indepNum = 2 := by
  show (completeMultipartite (List.replicate (n + 1) 2)).indepNum = 2
  rw [indepNum_completeMultipartite, max?_replicate]
  rfl

@[simp] theorem cliqueNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).cliqueNum = (ds.map (min · 1)).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, cliqueNum_join, cliqueNum_empty, ih, List.map_cons,
      List.sum_cons]

@[simp] theorem cliqueNum_cocktailParty (n : ℕ) : (cocktailParty n).cliqueNum = n := by
  show (completeMultipartite (List.replicate n 2)).cliqueNum = n
  rw [cliqueNum_completeMultipartite, List.map_replicate]
  simp

/-! ### Connectivity and triangles in the strong and lexicographic products -/

theorem isConnected_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    IsConnected (strongProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, isConnected_mk]
  rw [isConnected_mk] at hG hH
  exact CGraph.isConnected_strongProduct hG hH

theorem isConnected_lexProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    IsConnected (lexProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, isConnected_mk]
  rw [isConnected_mk] at hG hH
  exact CGraph.isConnected_lexProduct hG hH

theorem not_isBipartite_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsBipartite (strongProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, isBipartite_mk]
  rw [E_mk] at hG hH
  obtain ⟨a, b, hab⟩ := CGraph.exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := CGraph.exists_adj_of_E_pos hH
  exact CGraph.not_isBipartite_strongProduct hab hcd

theorem not_isBipartite_lexProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    ¬ IsBipartite (lexProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, isBipartite_mk]
  rw [E_mk] at hG hH
  obtain ⟨a, b, hab⟩ := CGraph.exists_adj_of_E_pos hG
  obtain ⟨c, d, hcd⟩ := CGraph.exists_adj_of_E_pos hH
  exact CGraph.not_isBipartite_lexProduct hab hcd

@[simp] theorem E_complete_pos (n : ℕ) : 0 < (complete (n + 2)).E := by
  rw [E_complete]
  exact Nat.choose_pos (by omega)

/-! ### The Petersen graph -/

@[simp] theorem V_petersen : petersen.V = 10 := by
  rw [V_kneser]
  rfl

/-- The complement of the Petersen graph is the triangular graph `T(5)`, the Johnson graph
`J(5, 2)`. -/
theorem compl_petersen : compl petersen = triangular 5 := by
  rw [triangular_eq_compl_kneser]

/-- **The Petersen graph is the complement of the line graph of `K₅`** — Kneser's original
description of it. -/
theorem petersen_eq_compl_lineGraph : petersen = compl (lineGraph (complete 5)) := by
  rw [lineGraph_complete_eq_triangular, ← compl_petersen, compl_compl]

/-- `L(K₃) = K₃`. -/
theorem lineGraph_complete_three : lineGraph (complete 3) = complete 3 := by
  rw [lineGraph_complete_eq_triangular, triangular_three]

/-- `L(K₄) = T(4)` is the octahedron. -/
theorem lineGraph_complete_four : lineGraph (complete 4) = cocktailParty 3 := by
  rw [lineGraph_complete_eq_triangular, triangular_four]

/-- `L(C₃) = C₃`, the triangle being its own line graph. -/
theorem lineGraph_cycle_three : lineGraph (cycle 3) = cycle 3 := by
  rw [cycle_three, lineGraph_complete_three]

/-- Successor mod `n + 3`, the "next vertex" map along the cycle. -/
private def cyc (n : ℕ) (i : Fin (n + 3)) : Fin (n + 3) :=
  ⟨(i.1 + 1) % (n + 3), Nat.mod_lt _ (by omega)⟩

private theorem cyc_val (n : ℕ) (i : Fin (n + 3)) : (cyc n i).1 = (i.1 + 1) % (n + 3) := rfl

private theorem cyc_ne (n : ℕ) (i : Fin (n + 3)) : cyc n i ≠ i := by
  intro h
  have h1 : (i.1 + 1) % (n + 3) = i.1 := congrArg Fin.val h
  have hi := i.2
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · rw [show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega

private theorem cyc_inj (n : ℕ) : Function.Injective (cyc n) := by
  intro i j h
  have h1 : (i.1 + 1) % (n + 3) = (j.1 + 1) % (n + 3) := congrArg Fin.val h
  have hi := i.2
  have hj := j.2
  refine Fin.ext ?_
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with h2 | h2 <;>
    rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · rw [Nat.mod_eq_of_lt h2, show j.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [Nat.mod_eq_of_lt h3, show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · omega

/-- Two steps along the cycle never return to where they started — this is the only place
`n ≥ 3` is used, and it is what rules out `L(C₂) = C₂`. -/
private theorem cyc_cyc_ne (n : ℕ) (j : Fin (n + 3)) : cyc n (cyc n j) ≠ j := by
  intro h
  have h1 : ((j.1 + 1) % (n + 3) + 1) % (n + 3) = j.1 := congrArg Fin.val h
  have hj := j.2
  rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1
    rcases Nat.lt_or_ge (j.1 + 1 + 1) (n + 3) with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1; omega
    · rw [show j.1 + 1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [show j.1 + 1 = n + 3 by omega, Nat.mod_self,
      Nat.mod_eq_of_lt (by omega : 0 + 1 < n + 3)] at h1
    omega

/-- Cycle adjacency in terms of `cyc`. -/
private theorem cycle_adj_cyc (n : ℕ) (i j : Fin (n + 3)) :
    (CGraph.cycle (n + 3)).Adj i j = decide (i ≠ j ∧ (cyc n i = j ∨ cyc n j = i)) := by
  have key : ∀ a b : Fin (n + 3), ((a.1 + 1) % (n + 3) == b.1) = decide (cyc n a = b) := by
    intro a b
    rw [Bool.beq_eq_decide_eq]
    exact decide_eq_decide.2 (by rw [Fin.ext_iff, cyc_val])
  show (decide (i ≠ j) && (((i.1 + 1) % (n + 3) == j.1) || ((j.1 + 1) % (n + 3) == i.1))) = _
  rw [key i j, key j i, Bool.decide_and, Bool.decide_or]

private theorem cyc_adj (n : ℕ) (i : Fin (n + 3)) :
    s(i, cyc n i) ∈ (CGraph.cycle (n + 3)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, cycle_adj_cyc]
  exact decide_eq_true ⟨Ne.symm (cyc_ne n i), Or.inl rfl⟩

/-- The edge of `Cₙ` running from `i` to its successor.  Every edge is of this form, so this is
the bijection `Fin n ≃ E(Cₙ)` witnessing `L(Cₙ) = Cₙ`. -/
private def cycEdge (n : ℕ) (i : Fin (n + 3)) : (CGraph.lineGraph (CGraph.cycle (n + 3))).V :=
  ⟨s(i, cyc n i), cyc_adj n i⟩

private theorem mem_cycEdge (n : ℕ) (v i : Fin (n + 3)) :
    v ∈ ((cycEdge n i).1 : Sym2 (Fin (n + 3))) ↔ v = i ∨ v = cyc n i := Sym2.mem_iff

private theorem cycEdge_inj (n : ℕ) : Function.Injective (cycEdge n) := by
  intro i j h
  have h1 : s(i, cyc n i) = s(j, cyc n j) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact h2
  · exact absurd (h2 ▸ h3) (cyc_cyc_ne n j)

/-- **The cycle is its own line graph**, for `n ≥ 3`.  The edges of `Cₙ` are the consecutive pairs
`{i, i+1}`, and two of them share a vertex exactly when their indices are consecutive.  Injectivity
is where `n ≥ 3` enters: for `n = 2` the two "edges" `{0, 1}` and `{1, 0}` coincide. -/
@[simp] theorem lineGraph_cycle (n : ℕ) : lineGraph (cycle (n + 3)) = cycle (n + 3) := by
  have hcard : Fintype.card (Fin (n + 3))
      = Fintype.card (CGraph.lineGraph (CGraph.cycle (n + 3))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_cycle, Fintype.card_fin]
  have hbij : Function.Bijective (cycEdge n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨cycEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin (n + 3),
      (CGraph.lineGraph (CGraph.cycle (n + 3))).Adj (cycEdge n i) (cycEdge n j)
        = (CGraph.cycle (n + 3)).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, cycle_adj_cyc]
    by_cases hij : i = j
    · subst hij; simp
    · rw [decide_eq_true (show cycEdge n i ≠ cycEdge n j from fun h ↦ hij (cycEdge_inj n h)),
        Bool.true_and, Bool.decide_and, decide_eq_true hij, Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_cycEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
        · exact absurd (h1.symm.trans h2) hij
        · exact Or.inr (h2.symm.trans h1)
        · exact Or.inl (h1.symm.trans h2)
        · exact absurd (cyc_inj n (h1.symm.trans h2)) hij
      · rintro (h | h)
        · exact ⟨j, (mem_cycEdge n j i).2 (Or.inr h.symm), (mem_cycEdge n j j).2 (Or.inl rfl)⟩
        · exact ⟨i, (mem_cycEdge n i i).2 (Or.inl rfl), (mem_cycEdge n i j).2 (Or.inr h.symm)⟩
  rw [cycle_def, lineGraph_mk]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (cycEdge n) hbij) hadj).symm⟩

/-- `L(C₄) = C₄`. -/
theorem lineGraph_cycle_four : lineGraph (cycle 4) = cycle 4 := lineGraph_cycle 1

/-- `L(C₅) = C₅`.  Together with `compl_cycle_five`, the pentagon is both self-complementary and
its own line graph. -/
theorem lineGraph_cycle_five : lineGraph (cycle 5) = cycle 5 := lineGraph_cycle 2

/-- Path adjacency at the level of the underlying naturals.  Note that `i ≠ j` is implied by
either disjunct, so it drops out. -/
private theorem path_adj_val (n : ℕ) (i j : Fin n) :
    (CGraph.path n).Adj i j = decide (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  show (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) = _
  by_cases h : i = j
  · subst h; simp
  · rw [decide_eq_true h, Bool.true_and, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq,
      ← Bool.decide_or]

private theorem pathEdge_adj (n : ℕ) (i : Fin n) :
    s(i.castSucc, i.succ) ∈ (CGraph.path (n + 1)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, path_adj_val]
  exact decide_eq_true (Or.inl (by simp))

/-- The `i`-th edge of the path `0 — 1 — ⋯ — n`. -/
private def pathEdge (n : ℕ) (i : Fin n) : (CGraph.lineGraph (CGraph.path (n + 1))).V :=
  ⟨s(i.castSucc, i.succ), pathEdge_adj n i⟩

private theorem mem_pathEdge (n : ℕ) (v : Fin (n + 1)) (i : Fin n) :
    v ∈ ((pathEdge n i).1 : Sym2 (Fin (n + 1))) ↔ v = i.castSucc ∨ v = i.succ := Sym2.mem_iff

private theorem pathEdge_inj (n : ℕ) : Function.Injective (pathEdge n) := by
  intro i j h
  have h1 : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact Fin.ext (by simpa using congrArg Fin.val h2)
  · have hv2 := congrArg Fin.val h2
    have hv3 := congrArg Fin.val h3
    simp only [Fin.val_castSucc, Fin.val_succ] at hv2 hv3
    omega

/-- **The line graph of a path is the shorter path**: `L(Pₙ₊₁) = Pₙ`.  Unlike the cycle this needs
no size hypothesis — `L(P₁) = P₀` is the empty graph. -/
@[simp] theorem lineGraph_path (n : ℕ) : lineGraph (path (n + 1)) = path n := by
  have hcard : Fintype.card (Fin n)
      = Fintype.card (CGraph.lineGraph (CGraph.path (n + 1))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_path, Fintype.card_fin]
  have hbij : Function.Bijective (pathEdge n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨pathEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin n,
      (CGraph.lineGraph (CGraph.path (n + 1))).Adj (pathEdge n i) (pathEdge n j)
        = (CGraph.path n).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, path_adj_val]
    by_cases hij : i = j
    · subst hij; simp
    · have hval : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
      rw [decide_eq_true (show pathEdge n i ≠ pathEdge n j from fun h ↦ hij (pathEdge_inj n h)),
        Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_pathEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2 <;>
          · have h3 := congrArg Fin.val (h1.symm.trans h2)
            simp only [Fin.val_castSucc, Fin.val_succ] at h3
            omega
      · rintro (h | h)
        · exact ⟨i.succ, (mem_pathEdge n _ i).2 (Or.inr rfl),
            (mem_pathEdge n _ j).2 (Or.inl (Fin.ext (by simpa using h)))⟩
        · exact ⟨i.castSucc, (mem_pathEdge n _ i).2 (Or.inl rfl),
            (mem_pathEdge n _ j).2 (Or.inr (Fin.ext (by simpa using h.symm)))⟩
  rw [path_def, lineGraph_mk]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (pathEdge n) hbij) hadj).symm⟩

/-- `L(P₃) = P₂ = K₂`. -/
theorem lineGraph_path_three : lineGraph (path 3) = complete 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, lineGraph_path, path_two]

private theorem bipartiteEdge_adj (m n : ℕ) (p : Fin m × Fin n) :
    s(Sum.inl p.1, Sum.inr p.2) ∈ (CGraph.bipartite m n).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj]
  exact CGraph.bipartite_adj_inl_inr m n p.1 p.2

/-- The edge of `K_{m,n}` joining the `i`-th left vertex to the `j`-th right vertex — that is,
the square `(i, j)` of the board. -/
private def bipartiteEdge (m n : ℕ) (p : Fin m × Fin n) :
    (CGraph.lineGraph (CGraph.bipartite m n)).V :=
  ⟨s(Sum.inl p.1, Sum.inr p.2), bipartiteEdge_adj m n p⟩

private theorem mem_bipartiteEdge (m n : ℕ) (v : Fin m ⊕ Fin n) (p : Fin m × Fin n) :
    v ∈ ((bipartiteEdge m n p).1 : Sym2 (Fin m ⊕ Fin n))
      ↔ v = Sum.inl p.1 ∨ v = Sum.inr p.2 := Sym2.mem_iff

private theorem bipartiteEdge_inj (m n : ℕ) : Function.Injective (bipartiteEdge m n) := by
  intro p q h
  have h1 : s(Sum.inl p.1, Sum.inr p.2) = s(Sum.inl q.1, Sum.inr q.2) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, h3⟩ | ⟨h2, _⟩
  · exact Prod.ext_iff.2 ⟨by simpa using h2, by simpa using h3⟩
  · exact absurd h2 (by simp)

/-- **The line graph of a complete bipartite graph is the rook's graph**: `L(K_{m,n}) = Kₘ □ Kₙ`.
An edge of `K_{m,n}` *is* a square `(i, j)` of the `m × n` board, and two squares share a vertex
exactly when they share a row or a column. -/
@[simp] theorem lineGraph_bipartite (m n : ℕ) : lineGraph (bipartite m n) = rook m n := by
  have hcard : Fintype.card (Fin m × Fin n)
      = Fintype.card (CGraph.lineGraph (CGraph.bipartite m n)).V := by
    rw [CGraph.card_lineGraph, CGraph.E_bipartite, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  have hbij : Function.Bijective (bipartiteEdge m n) :=
    Fintype.bijective_iff_injective_and_card _ |>.2 ⟨bipartiteEdge_inj m n, hcard⟩
  have hadj : ∀ p q : Fin m × Fin n,
      (CGraph.lineGraph (CGraph.bipartite m n)).Adj (bipartiteEdge m n p) (bipartiteEdge m n q)
        = (CGraph.rook m n).Adj p q := by
    intro p q
    rw [CGraph.lineGraph_adj, CGraph.rook_adj]
    by_cases hpq : p = q
    · subst hpq; simp
    · have hne : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun h ↦ hpq (Prod.ext_iff.2 h)
      rw [decide_eq_true (show bipartiteEdge m n p ≠ bipartiteEdge m n q from
          fun h ↦ hpq (bipartiteEdge_inj m n h)),
        Bool.true_and, ← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_or]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_bipartiteEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
        · have : p.1 = q.1 := by simpa using h1.symm.trans h2
          exact Or.inl ⟨this, fun hd ↦ hne ⟨this, hd⟩⟩
        · exact absurd (h1.symm.trans h2) (by simp)
        · exact absurd (h1.symm.trans h2) (by simp)
        · have : p.2 = q.2 := by simpa using h1.symm.trans h2
          exact Or.inr ⟨fun hc ↦ hne ⟨hc, this⟩, this⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact ⟨Sum.inl p.1, (mem_bipartiteEdge m n _ p).2 (Or.inl rfl),
            (mem_bipartiteEdge m n _ q).2 (Or.inl (by rw [h]))⟩
        · exact ⟨Sum.inr p.2, (mem_bipartiteEdge m n _ p).2 (Or.inr rfl),
            (mem_bipartiteEdge m n _ q).2 (Or.inr (by rw [h]))⟩
  have hrook : (rook m n : IsoGraph) = ⟦CGraph.rook m n⟧ := by
    rw [show (rook m n : IsoGraph) = cartesianProduct (complete m) (complete n) from rfl,
      complete_def, complete_def, cartesianProduct_mk]
  rw [bipartite_def, lineGraph_mk, hrook]
  exact Quotient.sound ⟨(CGraph.isoOfAdj (Equiv.ofBijective (bipartiteEdge m n) hbij) hadj).symm⟩

@[simp] theorem mycielskian_empty_zero : mycielskian (empty 0) = empty 1 := by
  have h : ∀ x y : (CGraph.mycielskian (CGraph.empty 0)).V,
      (CGraph.mycielskian (CGraph.empty 0)).Adj x y = false := by
    haveI : IsEmpty (CGraph.empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rintro (_ | (a | a)) (_ | (b | b)) <;> first | rfl | exact isEmptyElim a | exact isEmptyElim b
  rw [empty_def, mycielskian_mk, mk_eq_empty h]
  simp

/-- Relabelling for `mycielskian_empty`: the apex becomes the centre of the star, the shadow
vertices become its leaves, and the original vertices are the isolated part. -/
private def mycielskianEmptyEquiv (n : ℕ) :
    (Fin 1 ⊕ Fin n) ⊕ Fin n ≃ Option (Fin n ⊕ Fin n) where
  toFun x := match x with
    | .inl (.inl _) => none
    | .inl (.inr i) => some (.inr i)
    | .inr i => some (.inl i)
  invFun x := match x with
    | none => .inl (.inl 0)
    | some (.inr i) => .inl (.inr i)
    | some (.inl i) => .inr i
  left_inv := by
    rintro ((j | i) | i)
    · rw [Subsingleton.elim (0 : Fin 1) j]
    · rfl
    · rfl
  right_inv := by rintro (_ | (i | i)) <;> rfl

/-- The Mycielskian of an edgeless graph: the apex together with the `n` shadow vertices forms a
star, and the `n` original vertices stay isolated. -/
theorem mycielskian_empty (n : ℕ) :
    mycielskian (empty n) = disjUnion (star n) (empty n) := by
  rw [empty_def, mycielskian_mk, star_def, disjUnion_mk]
  refine Quotient.sound ⟨(CGraph.isoOfAdj
    (G := CGraph.disjUnion (CGraph.star n) (CGraph.empty n))
    (H := CGraph.mycielskian (CGraph.empty n))
    (mycielskianEmptyEquiv n)
    (by
      rintro ((j | i) | i) ((k | i') | i')
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj none (some (.inl i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inr i)) (some (.inl i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) none = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) (some (.inr i')) = _
        simp [CGraph.star]
      · show (CGraph.mycielskian (CGraph.empty n)).Adj (some (.inl i)) (some (.inl i')) = _
        simp [CGraph.star])).symm⟩

/-- **The Mycielskian of `K₂` is the 5-cycle**: two vertices, their two shadows and the apex,
strung together as `u₀ — u₁ — w₀ — z — w₁ — u₀`. -/
theorem mycielskian_complete_two : mycielskian (complete 2) = cycle 5 := by
  rw [complete_def, mycielskian_mk, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.mycielskian (CGraph.complete 2)) (H := CGraph.cycle 5)
    (⟨fun x ↦ match x with
        | none => 3
        | some (.inl a) => if a = 0 then 0 else 1
        | some (.inr a) => if a = 0 then 2 else 4,
      ![some (.inl 0), some (.inl 1), some (.inr 0), none, some (.inr 1)],
      by decide, by decide⟩ : Option (Fin 2 ⊕ Fin 2) ≃ Fin 5)
    (by decide)⟩

/-! ### Bipartiteness of the Mycielskian

The Mycielskian raises the chromatic number by one, so the only way for it to be bipartite is for
it to start from nothing at all. -/

theorem not_isBipartite_mycielskian_mk {G : CGraph} [DecidableEq G.V] {a b : G.V}
    (hab : G.Adj a b) : ¬ IsBipartite (mycielskian ⟦G⟧) := by
  rw [mycielskian_mk, isBipartite_mk]
  exact CGraph.not_isBipartite_mycielskian hab

/-- The Mycielskian is bipartite only in the degenerate edgeless case, where it is a star beside
some isolated vertices. -/
@[simp] theorem isBipartite_mycielskian_empty (n : ℕ) : IsBipartite (mycielskian (empty n)) := by
  rw [mycielskian_empty]
  exact isBipartite_disjUnion (isBipartite_star n) (isBipartite_empty n)

@[simp] theorem not_isBipartite_mycielskian_complete (n : ℕ) :
    ¬ IsBipartite (mycielskian (complete (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.complete (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by simp)

/-- Mycielski's construction really does leave the bipartite world: even applied to a complete
bipartite graph it produces something with an odd cycle. -/
@[simp] theorem not_isBipartite_mycielskian_bipartite (m n : ℕ) :
    ¬ IsBipartite (mycielskian (bipartite (m + 1) (n + 1))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.bipartite (m + 1) (n + 1)) (a := .inl ⟨0, by omega⟩)
    (b := .inr ⟨0, by omega⟩) (by simp)

@[simp] theorem not_isBipartite_mycielskian_cycle (n : ℕ) :
    ¬ IsBipartite (mycielskian (cycle (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.cycle (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by
      rw [CGraph.cycle_adj_val]
      show (0 : ℕ) ≠ 1 ∧ ((0 + 1) % (n + 2) = 1 ∨ (1 + 1) % (n + 2) = 0)
      exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt (by omega))⟩)

@[simp] theorem not_isBipartite_mycielskian_path (n : ℕ) :
    ¬ IsBipartite (mycielskian (path (n + 2))) :=
  not_isBipartite_mycielskian_mk (G := CGraph.path (n + 2)) (a := ⟨0, by omega⟩)
    (b := ⟨1, by omega⟩) (by simp [CGraph.path])

@[simp] theorem not_isBipartite_mycielskian_star (n : ℕ) :
    ¬ IsBipartite (mycielskian (star (n + 1))) := by
  rw [star_eq_bipartite]
  exact not_isBipartite_mycielskian_bipartite 0 n

/-! ## The simp set at work

These are not new facts — they are a regression test that the `@[simp]` lemmas above compose the
way they are meant to, and that none of them loops. -/

example : compl (compl (cycle 5)) = cycle 5 := by simp

example (n : ℕ) : cartesianProduct (empty 0) (cycle n) = empty 0 := by simp

example (G : IsoGraph) : lexProduct (empty 1) (lexProduct G (empty 1)) = G := by simp

example : circulant 7 [0, 3, 3] = circulant 7 [3] := by simp

example (n : ℕ) : IsBipartite (hypercube n) := by simp
example (ks : List ℕ) : IsBipartite (spider ks) := by simp
example (m n : ℕ) : IsBipartite (doubleStar m n) := by simp
example (k : ℕ) : IsBipartite (tadpole 6 k) := isBipartite_tadpole_even 3 k
example : IsBipartite (cyclePendant 4 [1, 1]) := isBipartite_cyclePendant_even 2 [1, 1] (by decide)
example : IsBipartite (thetaGraph [0, 2, 4]) := isBipartite_thetaGraph_even (by decide)
example : IsBipartite (thetaGraph [1, 3, 5]) := isBipartite_thetaGraph_odd (by decide)
example : ¬ IsBipartite (thetaGraph [0, 1]) := not_isBipartite_thetaGraph_pair (by decide)
example (k : ℕ) : ¬ IsBipartite (tadpole 5 k) := not_isBipartite_tadpole_odd 1 k
example : ¬ IsBipartite (cyclePendant 3 [1, 0, 2]) := not_isBipartite_cyclePendant_odd 0 [1, 0, 2]
example : ¬ IsBipartite (lollipop 4 2) := not_isBipartite_lollipop 1 2
example : ¬ IsBipartite (wheel 5) := not_isBipartite_wheel 2
example : ¬ IsBipartite (mycielskian (cycle 5)) := by simp
example : IsBipartite (mycielskian (empty 3)) := by simp
example : IsBipartite (foldedCube 5) := isBipartite_foldedCube_odd (by decide)
example : ¬ IsBipartite (foldedCube 4) := not_isBipartite_foldedCube_even 1
example : IsBipartite (circulant 8 [1, 3]) := isBipartite_circulant (by decide) (by decide)
example : ¬ IsBipartite (circulant 7 [2]) :=
  not_isBipartite_circulant_of_odd (by decide) 2 (by decide) (by omega) (by omega)
example : ¬ IsBipartite (kneser 6 2) := by simp
example : ¬ IsBipartite (johnson 5 2) := by simp
example : ¬ IsBipartite (triangular 5) := not_isBipartite_triangular (by omega)
example : ¬ IsBipartite petersen := by simp
example : ¬ IsBipartite (rook 3 3) := not_isBipartite_rook 0 2
example : ¬ IsBipartite (book 3) := by simp
example : ¬ IsBipartite (cocktailParty 4) := by simp
example : ¬ IsBipartite (fan 5) := by simp
example (G : IsoGraph) : ¬ IsBipartite (join (cycle 3) G) :=
  not_isBipartite_join_left not_isBipartite_cycle_three
example : ¬ IsBipartite (completeMultipartite [2, 3, 4]) :=
  not_isBipartite_completeMultipartite 1 2 3 []
example : ¬ IsBipartite (prism 5) := not_isBipartite_prism_odd 1
example (G H : IsoGraph) (h : IsBipartite (disjUnion G H)) : IsBipartite G := by simp_all
example (n : ℕ) : IsBipartite (thetaGraph (List.replicate n 1)) := by simp

example (m n : ℕ) : IsBipartite (disjUnion (ladder m) (bipartite m n)) := by simp

example (m n : ℕ) : IsBipartite (cartesianProduct (cycle (2 * m)) (path n)) := by simp

example (n : ℕ) :
    tensorProduct (complete 2) (hypercube n) = disjUnion (hypercube n) (hypercube n) :=
  tensorProduct_complete_two_of_isBipartite _ (by simp)

example : circulant 9 [0, 1] = cycle 9 := by simp

example : compl (paley 13) = paley 13 := by simp

example : petersen.V = 10 := by simp [Nat.choose]

example (G H : IsoGraph) : (disjUnion (compl (compl G)) H).V = G.V + H.V := by simp

example (m n : ℕ) : (rook m n).V = m * n := by simp

example (n : ℕ) : lineGraph (empty n) = empty 0 := by simp

example (n : ℕ) : tensorProduct (empty n) (complete 3) = empty (n * 3) := by simp

example : tadpole 3 0 = complete 3 := by rw [tadpole_zero, cycle_three]
example (k : ℕ) : spider [k] = lollipop 1 k := by simp
example : lollipop 3 0 = complete 3 := by simp
example : spider [1] = complete 2 := by simp
example (m : ℕ) : IsBipartite (tadpole (2 * m) 0) := by simp
example : cyclePendant 5 [] = cycle 5 := by simp
example : compl (cyclePendant 5 []) = cycle 5 := by simp
example : spider [2, 2] = path 5 := by simp
example : thetaGraph [3] = path 5 := by simp
example (j : ℕ) : thetaGraph (List.replicate (j + 1) 0) = complete 2 := by simp
example (n : ℕ) : spider (List.replicate n 1) = star n := by simp
example : doubleStar 0 3 = star 4 := by simp
example : doubleStar 3 0 = star 4 := by simp
example : doubleStar 0 1 = path 3 := by rw [doubleStar_left_zero, star_two]
example : thetaGraph [1, 1] = cycle 4 := by simp
example : thetaGraph [0, 2] = cycle 4 := by simp
example : thetaGraph [1, 2] = cycle 5 := by simp
example : thetaGraph [0, 0] = complete 2 := by simp
example : thetaGraph [0, 1] = complete 3 := by rw [thetaGraph_pair, show 2 + 0 + 1 = 3 from rfl,
  cycle_three]
example (m : ℕ) : cyclePendant m [1] = tadpole m 1 := by simp
example : doubleStar 2 3 = doubleStar 3 2 := by rw [doubleStar_comm]
example : spider [0, 2, 0, 3] = spider [2, 0, 3] := by simp
example : tadpole 2 4 = path 6 := by simp
example : lollipop 2 4 = path 6 := by simp
example (k : ℕ) : lollipop 3 k = tadpole 3 k := by rw [lollipop_three_eq_tadpole]
example (ks : List ℕ) : thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks) := by simp
example : tadpole 1 5 = path 6 := by simp
example : spider [2, 0, 3] = spider [2, 3] := by simpa using spider_append_zero_cons [2] [3]
example : cyclePendant 3 [1, 0] = cyclePendant 3 [1] := by
  simpa using cyclePendant_append_zero 3 [1]
example : cyclePendant 1 [3] = star 3 := by simp
example : cyclePendant 1 [2] = path 3 := by rw [cyclePendant_one, star_two]
example : spider [1, 3, 2] = spider [2, 1, 3] := spider_perm (by decide)
example (ks : List ℕ) : spider (ks ++ [0]) = spider (0 :: ks) :=
  spider_perm (List.perm_append_singleton 0 ks)
example (a b : ℕ) : spider [a, b] = spider [b, a] := spider_perm (List.Perm.swap b a [])
example : thetaGraph [1, 2, 3] = thetaGraph [3, 1, 2] := thetaGraph_perm (by decide)
example (xs : List ℕ) : thetaGraph (xs ++ [0]) = thetaGraph (0 :: xs) :=
  thetaGraph_perm (List.perm_append_singleton 0 xs)

example : thetaGraph [1, 1, 1, 1] = bipartite 2 4 := by
  rw [show ([1, 1, 1, 1] : List ℕ) = List.replicate 4 1 from rfl, thetaGraph_replicate_one]
example : thetaGraph [1, 1] = cycle 4 := by simp
example (n : ℕ) : thetaGraph (List.replicate n 1) = bipartite 2 n := by simp

example : IsConnected (prism 6) := by simp
example : IsConnected (hypercube 4) := by simp
example : ¬ IsConnected (disjUnion (cycle 3) (cycle 4)) :=
  not_isConnected_disjUnion (by simp) (by simp)
example (G : IsoGraph) (h : IsConnected G) : IsConnected (cartesianProduct G (path 3)) := by
  simp [h]

example : ¬ IsAcyclic (wheel 5) := by simp
example : IsTree (star 7) := by simp
example : ¬ IsConnected (empty 3) := by simp
example : IsConnected (book 4) := by simp
example (G : IsoGraph) (h : IsTree G) (hv : G.V = 10) : G.E = 9 := by
  have := h.E_add_one
  omega

example : (cocktailParty 4).cliqueNum = 4 := by simp
example : (book 5).indepNum = 5 := by simp
example : (wheel 7).indepNum = 3 := by simp
example : (compl (complete 5)).indepNum = 5 := by simp
example : (star 6).cliqueNum = 2 := by simp
example : (lexProduct (empty 3) (empty 4)).indepNum = 12 := by simp

example : IsConnected (strongProduct (path 3) (cycle 4)) :=
  isConnected_strongProduct (by simp) (by simp)

example : ¬ IsBipartite (lexProduct (complete 2) (complete 2)) :=
  not_isBipartite_lexProduct (by simp) (by simp)

example : ¬ IsBipartite (strongProduct (path 2) (path 2)) :=
  not_isBipartite_strongProduct (by simp) (by simp)

example : (wheel 6).E = 12 := by simp
example : (prism 6).E = 18 := by simp
example : (rook 3 3).E = 18 := by simp [Nat.choose]
example : (hypercube 4).E = 32 := by
  have := E_hypercube 4
  omega
example : (completeMultipartite [1, 1, 3]).E = 7 := by
  have := E_completeMultipartite [1, 1, 3]
  simp [Nat.choose] at this
  omega

end IsoGraph
