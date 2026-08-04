import IsoGraph.Constructions
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Nat.Choose.Bounds

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

@[simp] theorem length_degSequence (G : CGraph) : G.degSequence.length = Fintype.card G.V := by
  rw [degSequence, degMultiset, Multiset.length_sort, Multiset.card_map, Finset.card_val,
    Finset.card_univ]

/-- The handshake lemma: the degrees add up to twice the edge count. -/
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
theorem E_lineGraph_eq_sum_degSequence (G : CGraph) [DecidableEq G.V] :
    (lineGraph G).E = (G.degSequence.map fun d ↦ d.choose 2).sum := by
  rw [sum_degSequence_map, E_lineGraph]

/-- Constant neighbour counts are exactly regularity. -/
theorem isRegularOfDegree_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.toSimple.IsRegularOfDegree k := fun v ↦ by
  rw [SimpleGraph.degree, neighborFinset_eq_nbrs, h]

theorem degSequence_of_card_nbrs (G : CGraph) {k : ℕ} (h : ∀ v, (G.nbrs v).card = k) :
    G.degSequence = List.replicate (Fintype.card G.V) k :=
  degSequence_of_regular G (isRegularOfDegree_of_card_nbrs G h)

@[simp] theorem degSequence_kneser {n k : ℕ} (hk : 1 ≤ k) :
    (kneser n k).degSequence = List.replicate (n.choose k) ((n - k).choose k) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_kneser hk), card_kneser]

@[simp] theorem degSequence_rook (m n : ℕ) :
    (rook m n).degSequence = List.replicate (m * n) ((n - 1) + (m - 1)) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_rook)]
  congr 1
  simp only [rook, card_cartesianProduct, card_complete]

variable {G H : CGraph}

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

/-! ### Neighbours in the four products -/

theorem nbrs_cartesianProduct [DecidableEq G.V] [DecidableEq H.V] (p : (cartesianProduct G H).V) :
    (cartesianProduct G H).nbrs p
      = (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) ∪ (G.nbrs p.1 ×ˢ ({p.2} : Finset H.V)) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, cartesianProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem card_nbrs_cartesianProduct [DecidableEq G.V] [DecidableEq H.V] {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (cartesianProduct G H).V) : ((cartesianProduct G H).nbrs p).card = k + l := by
  rw [nbrs_cartesianProduct, Finset.card_union_of_disjoint, Finset.card_product,
    Finset.card_product, Finset.card_singleton, Finset.card_singleton, hG, hH, one_mul, mul_one,
    Nat.add_comm]
  refine Finset.disjoint_product.2 (Or.inr ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_tensorProduct [DecidableEq G.V] [DecidableEq H.V] (p : (tensorProduct G H).V) :
    (tensorProduct G H).nbrs p = G.nbrs p.1 ×ˢ H.nbrs p.2 := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, tensorProduct_adj]
  simp only [Finset.mem_product, mem_nbrs, Bool.and_eq_true]

theorem card_nbrs_tensorProduct [DecidableEq G.V] [DecidableEq H.V] {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (tensorProduct G H).V) : ((tensorProduct G H).nbrs p).card = k * l := by
  rw [nbrs_tensorProduct, Finset.card_product, hG, hH]

theorem nbrs_lexProduct [DecidableEq G.V] [DecidableEq H.V] (p : (lexProduct G H).V) :
    (lexProduct G H).nbrs p
      = (G.nbrs p.1 ×ˢ (Finset.univ : Finset H.V)) ∪ (({p.1} : Finset G.V) ×ˢ H.nbrs p.2) := by
  refine Finset.ext (α := G.V × H.V) fun q ↦ ?_
  rw [mem_nbrs, lexProduct_adj]
  simp only [Finset.mem_union, Finset.mem_product, mem_nbrs,
    Finset.mem_singleton, Finset.mem_univ, and_true, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

theorem card_nbrs_lexProduct [DecidableEq G.V] [DecidableEq H.V] {k l : ℕ}
    (hG : ∀ v, (G.nbrs v).card = k) (hH : ∀ w, (H.nbrs w).card = l)
    (p : (lexProduct G H).V) :
    ((lexProduct G H).nbrs p).card = k * Fintype.card H.V + l := by
  rw [nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_univ, hG, hH, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem nbrs_strongProduct [DecidableEq G.V] [DecidableEq H.V] (p : (strongProduct G H).V) :
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

theorem card_nbrs_strongProduct [DecidableEq G.V] [DecidableEq H.V] {k l : ℕ}
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

theorem degSequence_cartesianProduct [DecidableEq G.V] [DecidableEq H.V] {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (cartesianProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_cartesianProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_cartesianProduct]

theorem degSequence_tensorProduct [DecidableEq G.V] [DecidableEq H.V] {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (tensorProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k * l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_tensorProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_tensorProduct]

theorem degSequence_lexProduct [DecidableEq G.V] [DecidableEq H.V] {m k n l : ℕ}
    (hG : G.degSequence = List.replicate m k) (hH : H.degSequence = List.replicate n l) :
    (lexProduct G H).degSequence
      = List.replicate (Fintype.card G.V * Fintype.card H.V) (k * Fintype.card H.V + l) := by
  rw [degSequence_of_card_nbrs _
    (card_nbrs_lexProduct (card_nbrs_of_degSequence hG) (card_nbrs_of_degSequence hH)),
    card_lexProduct]

theorem degSequence_strongProduct [DecidableEq G.V] [DecidableEq H.V] {m k n l : ℕ}
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
theorem two_step_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V]
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

theorem diameter_join_le_two (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V]
    [Nonempty H.V] : (join G H).diameter ≤ 2 :=
  diameter_le_two _ (two_step_join G H)

/-- A join is of diameter exactly two as soon as one side has a non-adjacent pair. -/
theorem diameter_join_of_not_adj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty H.V] {a c : G.V} (hne : a ≠ c) (hadj : G.Adj a c = false) :
    (join G H).diameter = 2 := by
  haveI : Nonempty G.V := ⟨a⟩
  refine diameter_eq_two _ (two_step_join G H) (u := Sum.inl a) (v := Sum.inl c) ?_ ?_
  · exact fun h ↦ hne (Sum.inl.inj h)
  · simp [hadj]

/-! ### The complement of a disconnected graph -/

/-- Unreachable vertices are adjacent in the complement. -/
theorem compl_adj_of_not_reachable (G : CGraph) [DecidableEq G.V] {u w : G.V}
    (h : ¬ G.toSimple.Reachable u w) : (compl G).toSimple.Adj u w := by
  have hne : u ≠ w := by rintro rfl; exact h (SimpleGraph.Reachable.refl u)
  have hadj : G.Adj u w = false := by
    by_contra hc
    exact h (SimpleGraph.Adj.reachable (show G.toSimple.Adj u w by simpa using hc))
  simp [hadj, hne]

/-- **The complement of a disconnected graph is a two-step graph.**  Two vertices in different
components are already adjacent in the complement; two vertices in the same component are both
non-adjacent to anything in another component. -/
theorem two_step_compl (G : CGraph) [DecidableEq G.V] (h : ¬ G.toSimple.Preconnected)
    (u v : G.V) (_huv : u ≠ v) :
    (compl G).toSimple.Adj u v ∨
      ∃ w, (compl G).toSimple.Adj u w ∧ (compl G).toSimple.Adj w v := by
  by_cases hr : G.toSimple.Reachable u v
  · obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ G.toSimple.Reachable x y := by
      unfold SimpleGraph.Preconnected at h
      push_neg at h
      exact h
    have key : ∀ w : G.V, ¬ G.toSimple.Reachable u w →
        (compl G).toSimple.Adj u w ∧ (compl G).toSimple.Adj w v := fun w hw ↦
      ⟨G.compl_adj_of_not_reachable hw,
        (G.compl_adj_of_not_reachable fun hvw ↦ hw (hr.trans hvw)).symm⟩
    by_cases hux : G.toSimple.Reachable u x
    · exact Or.inr ⟨y, key y fun huy ↦ hxy (hux.symm.trans huy)⟩
    · exact Or.inr ⟨x, key x hux⟩
  · exact Or.inl (G.compl_adj_of_not_reachable hr)

theorem diameter_compl_le_two (G : CGraph) [DecidableEq G.V] (h : ¬ G.toSimple.Preconnected) :
    (compl G).diameter ≤ 2 :=
  diameter_le_two _ (two_step_compl G h)

/-- **The complement of a disconnected graph is connected.** -/
theorem isConnected_compl_of_not_preconnected (G : CGraph) [DecidableEq G.V] [Nonempty G.V]
    (h : ¬ G.toSimple.Preconnected) : (compl G).IsConnected := by
  haveI : Nonempty (compl G).V := ‹Nonempty G.V›
  exact SimpleGraph.connected_of_ediam_ne_top
    (ne_top_of_le_ne_top (by simp) (ediam_le_two _ (two_step_compl G h)))

/-- If the graph is disconnected and has an edge, its complement has diameter exactly two. -/
theorem diameter_compl_eq_two (G : CGraph) [DecidableEq G.V] (h : ¬ G.toSimple.Preconnected)
    (hE : 0 < G.E) : (compl G).diameter = 2 := by
  obtain ⟨u, v, hne, hadj⟩ := exists_not_adj_of_E_lt (compl G)
    (show (compl G).E < (Fintype.card G.V).choose 2 by have hc := G.E_compl; omega)
  refine diameter_eq_two _ (two_step_compl G h) hne fun hc ↦ ?_
  have hc' : (compl G).Adj u v = true := by simpa using hc
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
theorem degMultiset_disjUnion (G H : CGraph) :
    (disjUnion G H).degMultiset = G.degMultiset + H.degMultiset := by
  unfold degMultiset
  rw [univ_val_sum, Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · exact Multiset.map_congr rfl fun v _ ↦ degree_disjUnion_inl G H v
  · exact Multiset.map_congr rfl fun v _ ↦ degree_disjUnion_inr G H v

theorem nbrs_compl (G : CGraph) [DecidableEq G.V] (v : G.V) :
    (compl G).nbrs v = (G.nbrs v)ᶜ.erase v := by
  ext w
  simp only [mem_nbrs, compl_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true',
    Finset.mem_erase, Finset.mem_compl, Bool.not_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun he ↦ h1 he.symm, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun he ↦ h1 he.symm, h2⟩

theorem degree_compl (G : CGraph) [DecidableEq G.V] (v : G.V) :
    (compl G).toSimple.degree v = Fintype.card G.V - 1 - G.toSimple.degree v := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, nbrs_compl]
  have hv : v ∈ (G.nbrs v)ᶜ := by simp [adj_self]
  rw [Finset.card_erase_of_mem hv, Finset.card_compl]
  omega

theorem degree_le (G : CGraph) [DecidableEq G.V] (v : G.V) :
    G.toSimple.degree v + 1 ≤ Fintype.card G.V := by
  rw [← card_nbrs_eq_degree]
  have hv : v ∉ G.nbrs v := by simp [adj_self]
  have hsub := Finset.card_le_card (Finset.subset_univ (insert v (G.nbrs v)))
  rw [Finset.card_insert_of_notMem hv, Finset.card_univ] at hsub
  omega

theorem degree_join_inl (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (a : G.V) :
    (join G H).toSimple.degree (Sum.inl a) = G.toSimple.degree a + Fintype.card H.V := by
  have hd := G.degree_le a
  show (compl (disjUnion (compl G) (compl H))).toSimple.degree (Sum.inl a) = _
  rw [degree_compl, degree_disjUnion_inl, degree_compl, card_disjUnion, card_compl, card_compl]
  omega

theorem degree_join_inr (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (b : H.V) :
    (join G H).toSimple.degree (Sum.inr b) = Fintype.card G.V + H.toSimple.degree b := by
  have hd := H.degree_le b
  show (compl (disjUnion (compl G) (compl H))).toSimple.degree (Sum.inr b) = _
  rw [degree_compl, degree_disjUnion_inr, degree_compl, card_disjUnion, card_compl, card_compl]
  omega

/-- **The degree multiset of a join**: every vertex picks up all the vertices on the other side. -/
theorem degMultiset_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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
theorem degMultiset_compl (G : CGraph) [DecidableEq G.V] :
    (compl G).degMultiset = G.degMultiset.map (fun d ↦ Fintype.card G.V - 1 - d) := by
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

theorem degree_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
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

theorem degree_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p : (tensorProduct G H).V) :
    (tensorProduct G H).toSimple.degree p = G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_tensorProduct, Finset.card_product]

theorem degree_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p : (lexProduct G H).V) :
    (lexProduct G H).toSimple.degree p
      = G.toSimple.degree p.1 * Fintype.card H.V + H.toSimple.degree p.2 := by
  rw [← card_nbrs_eq_degree, ← card_nbrs_eq_degree, ← card_nbrs_eq_degree,
    nbrs_lexProduct, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_univ, one_mul]
  refine Finset.disjoint_product.2 (Or.inl ?_)
  rw [Finset.disjoint_singleton_right, mem_nbrs, adj_self]
  exact Bool.noConfusion

theorem degree_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
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

theorem degMultiset_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_cartesianProduct G H p]
  refine Eq.trans (univ_val_map_prod fun a b ↦ G.toSimple.degree a + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_tensorProduct G H p]
  refine Eq.trans (univ_val_map_prod fun a b ↦ G.toSimple.degree a * H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).degMultiset
      = G.degMultiset.bind fun d ↦ H.degMultiset.map fun e ↦ d * Fintype.card H.V + e := by
  unfold degMultiset
  rw [Multiset.map_congr rfl fun p _ ↦ degree_lexProduct G H p]
  refine Eq.trans (univ_val_map_prod
    fun a b ↦ G.toSimple.degree a * Fintype.card H.V + H.toSimple.degree b) ?_
  rw [Multiset.bind_map]
  exact Multiset.bind_congr fun a _ ↦ (Multiset.map_map _ _ _).symm

theorem degMultiset_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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
theorem cliqueNum_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a : G.V) (b : H.V) :
    (cartesianProduct G H).cliqueNum = max G.cliqueNum H.cliqueNum :=
  cliqueNum_of_cartesian_adj (S := G.toSimple) (T := H.toSimple)
    (P := (cartesianProduct G H).toSimple) a b fun p q ↦ by
      simp only [CGraph.toSimple_adj, cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

/-- The tensor product has the smaller of the two clique numbers. -/
theorem cliqueNum_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).cliqueNum = min G.cliqueNum H.cliqueNum :=
  cliqueNum_of_tensor_adj (S := G.toSimple) (T := H.toSimple)
    (P := (tensorProduct G H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true]

/-- The lexicographic product multiplies clique numbers, just like the strong product. -/
theorem cliqueNum_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum :=
  cliqueNum_of_lex_adj (S := G.toSimple) (T := H.toSimple)
    (P := (lexProduct G H).toSimple) fun p q ↦ by
      simp only [CGraph.toSimple_adj, lexProduct_adj, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]

/-! ### The diameter of a Cartesian product -/

/-- Distances in a box product add, so extremal distances do too: the box product of two nonempty
finite graphs has the sum of the two extended diameters. -/
theorem ediam_boxProd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : SimpleGraph α) (T : SimpleGraph β) :
    (S.boxProd T).ediam = S.ediam + T.ediam := by
  refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun p q ↦ ?_) ?_
  · rw [SimpleGraph.edist_boxProd]
    exact add_le_add SimpleGraph.edist_le_ediam SimpleGraph.edist_le_ediam
  · obtain ⟨a, a', ha⟩ := SimpleGraph.exists_edist_eq_ediam_of_finite (G := S)
    obtain ⟨b, b', hb⟩ := SimpleGraph.exists_edist_eq_ediam_of_finite (G := T)
    rw [← ha, ← hb, ← SimpleGraph.edist_boxProd (x := (a, b)) (y := (a', b'))]
    exact SimpleGraph.edist_le_ediam

/-- **The diameter of a Cartesian product is the sum of the diameters.**  Both factors have to be
connected: the diameter of a disconnected graph is the junk value `0`. -/
theorem diameter_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
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

@[simp] theorem diameter_empty (n : ℕ) : (empty n).diameter = 0 := by
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

theorem chromNum_le_card (G : CGraph) : G.chromNum ≤ Fintype.card G.V := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.chromaticNumber_le_card

/-- A clique needs one colour per vertex, so `ω(G) ≤ χ(G)`. -/
theorem cliqueNum_le_chromNum (G : CGraph) : G.cliqueNum ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.cliqueNum_le_chromaticNumber

theorem two_le_chromNum_of_adj {G : CGraph} {a b : G.V} (h : G.Adj a b) : 2 ≤ G.chromNum := by
  rw [← Nat.cast_le (α := ℕ∞), coe_chromNum]
  exact SimpleGraph.two_le_chromaticNumber_of_adj h

/-- Two colours suffice exactly when the graph is bipartite. -/
theorem isBipartite_iff_chromNum_le_two {G : CGraph} : G.IsBipartite ↔ G.chromNum ≤ 2 :=
  G.isBipartite_iff_colorable.trans chromNum_le_iff_colorable.symm

@[simp] theorem chromNum_empty_zero : (empty 0).chromNum = 0 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : IsEmpty (empty 0).V := inferInstanceAs (IsEmpty (Fin 0))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_eq_zero_of_isEmpty)

@[simp] theorem chromNum_empty (n : ℕ) : (empty (n + 1)).chromNum = 1 :=
  chromNum_eq_of_chromaticNumber (by
    haveI : Nonempty (empty (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))
    rw [empty_toSimple]
    exact SimpleGraph.chromaticNumber_bot (V := (empty (n + 1)).V))

/-- **`K_n` needs `n` colours.** -/
@[simp] theorem chromNum_complete (n : ℕ) : (complete n).chromNum = n :=
  chromNum_eq_of_chromaticNumber (by rw [complete_toSimple, SimpleGraph.chromaticNumber_top,
    card_complete])

@[simp] theorem chromNum_path (n : ℕ) : (path (n + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [path_toSimple]; exact SimpleGraph.chromaticNumber_pathGraph _ (by omega))

/-- **An even cycle is bipartite.** -/
theorem chromNum_cycle_even (m : ℕ) : (cycle (2 * m + 2)).chromNum = 2 :=
  chromNum_eq_of_chromaticNumber (by
    rw [cycle_toSimple]
    exact SimpleGraph.chromaticNumber_cycleGraph_of_even _ (by omega) ⟨m + 1, by omega⟩)

/-- **An odd cycle needs three colours.** -/
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
@[simp] theorem chromNum_disjUnion (G H : CGraph) :
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
theorem chromNum_eq_two_iff {G : CGraph} : G.chromNum = 2 ↔ G.IsBipartite ∧ 0 < G.E := by
  rw [chromNum_eq_iff_chromaticNumber, ← toSimple_ne_bot_iff, isBipartite_iff_colorable]
  exact_mod_cast SimpleGraph.chromaticNumber_eq_two_iff

theorem chromNum_eq_zero_iff {G : CGraph} : G.chromNum = 0 ↔ Fintype.card G.V = 0 := by
  rw [chromNum_eq_iff_chromaticNumber, Fintype.card_eq_zero_iff]
  exact ⟨fun h ↦ SimpleGraph.isEmpty_of_chromaticNumber_eq_zero (by exact_mod_cast h),
    fun h ↦ by exact_mod_cast SimpleGraph.chromaticNumber_eq_zero_of_isEmpty⟩

/-- Anything that is not bipartite needs at least three colours. -/
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
theorem chromNum_tensorProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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
theorem chromNum_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
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
theorem chromNum_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
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
theorem chromNum_lexProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2 <|
    colorable_of_lex_adj (S := G.toSimple) (T := H.toSimple) (P := (lexProduct G H).toSimple)
      (fun p q h ↦ by simpa using h) colorable_chromNum colorable_chromNum

/-- One colour is enough exactly when there is a vertex but no edge. -/
theorem chromNum_eq_one_iff {G : CGraph} : G.chromNum = 1 ↔ G.E = 0 ∧ 0 < Fintype.card G.V := by
  have hb : G.toSimple = ⊥ ↔ G.E = 0 := by
    rw [← not_iff_not, ← ne_eq, toSimple_ne_bot_iff]
    omega
  rw [chromNum_eq_iff_chromaticNumber, Nat.cast_one, SimpleGraph.chromaticNumber_eq_one_iff, hb,
    Fintype.card_pos_iff]

/-- **Every colour class is an independent set**, so `|V| ≤ χ·α`. -/
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
private theorem colorable_mycielskian (G : CGraph) [DecidableEq G.V] {n : ℕ}
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
private theorem colorable_of_colorable_mycielskian (G : CGraph) [DecidableEq G.V] {n : ℕ}
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
theorem chromNum_mycielskian (G : CGraph) [DecidableEq G.V] :
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

theorem girth_eq_zero_iff (G : CGraph) : G.girth = 0 ↔ G.IsAcyclic :=
  SimpleGraph.girth_eq_zero

theorem three_le_girth {G : CGraph} (h : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  SimpleGraph.three_le_girth h

theorem girth_le_length {G : CGraph} {a : G.V} {w : G.toSimple.Walk a a} (h : w.IsCycle) :
    G.girth ≤ w.length :=
  SimpleGraph.girth_le_length h

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
theorem four_le_girth_of_isBipartite {G : CGraph} (hb : G.IsBipartite) (hnac : ¬ G.IsAcyclic) :
    4 ≤ G.girth :=
  four_le_girth (fun x _ z h1 h2 h3 ↦
    not_isBipartite_of_triangle h1 ((G.symm x z).trans h3) h2 hb) hnac

/-- A product of two graphs with an edge each contains a square. -/
theorem girth_cartesianProduct_le_four {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
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

/-! ### Girth three and the clique number -/

/-- **Girth three means a triangle**, and a triangle is a three-clique: so a graph has girth
three exactly when its clique number is at least three.  Every entry of the `cliqueNum` table is
therefore also a girth-three certificate. -/
theorem girth_eq_three_iff {G : CGraph} : G.girth = 3 ↔ 3 ≤ G.cliqueNum := by
  classical
  constructor
  · intro h
    have hnac : ¬ G.IsAcyclic := by
      intro hac
      rw [(girth_eq_zero_iff G).2 hac] at h
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

theorem girth_eq_three_of_cliqueNum {G : CGraph} (h : 3 ≤ G.cliqueNum) : G.girth = 3 :=
  girth_eq_three_iff.2 h

/-- **A triangle-free graph with a cycle has girth at least four**, stated through the clique
number. -/
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
theorem girth_cartesianProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
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

/-- **The complete bipartite graph `K_{m+2,n+2}` has girth four.** -/
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

/-! ### Two graphs of girth five -/

/-- **The five-cycle has girth five.** -/
theorem girth_cycle_five : (cycle 5).girth = 5 := by
  refine le_antisymm ?_ (five_le_girth (by decide) (by decide) (not_isAcyclic_cycle 2))
  exact girth_le_five_of_pentagon (a := (0 : Fin 5)) (b := (1 : Fin 5)) (c := (2 : Fin 5))
    (d := (3 : Fin 5)) (e := (4 : Fin 5))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The Petersen graph has girth five**: it is strongly regular with `ℓ = 0` and `μ = 1`, so it
has neither a triangle nor a square, and its outer five-cycle realises the bound. -/
theorem girth_kneser_five_two : (kneser 5 2).girth = 5 := by
  have hpent := girth_le_five_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hnac := not_isAcyclic_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact le_antisymm hpent ((isSRGWith_kneser_two 5).five_le_girth hnac)

/-- An edge is a two-clique. -/
theorem two_le_cliqueNum {G : CGraph} {a b : G.V} (hab : G.Adj a b) : 2 ≤ G.cliqueNum := by
  classical
  have hne : a ≠ b := ((toSimple_adj G a b).2 hab).ne
  have hcl : G.toSimple.IsClique ((({a, b} : Finset G.V)) : Set G.V) := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.2 fun _ ↦ (toSimple_adj G a b).2 hab
  have := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)
  rwa [Finset.card_pair hne] at this

/-- A single vertex is a one-clique. -/
theorem one_le_cliqueNum_of_vertex {G : CGraph} (a : G.V) : 1 ≤ G.cliqueNum := by
  classical
  have hcl : G.toSimple.IsClique ((({a} : Finset G.V)) : Set G.V) := by simp
  have := SimpleGraph.IsClique.card_le_cliqueNum (tc := hcl)
  simpa using this

theorem two_le_cliqueNum_of_E_pos {G : CGraph} (h : 0 < G.E) : 2 ≤ G.cliqueNum := by
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos h
  exact two_le_cliqueNum hab

/-! ### Maximum and minimum degree -/

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
  haveI : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_maximal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

theorem exists_degree_eq_minDeg (G : CGraph) (v₀ : G.V) :
    ∃ v : G.V, G.toSimple.degree v = G.minDeg := by
  haveI : Nonempty G.V := ⟨v₀⟩
  obtain ⟨v, hv⟩ := SimpleGraph.exists_minimal_degree_vertex G.toSimple
  exact ⟨v, hv.symm⟩

theorem minDeg_le_maxDeg (G : CGraph) : G.minDeg ≤ G.maxDeg :=
  SimpleGraph.minDegree_le_maxDegree _

theorem maxDeg_lt_card (G : CGraph) (v₀ : G.V) : G.maxDeg < Fintype.card G.V :=
  haveI : Nonempty G.V := ⟨v₀⟩
  SimpleGraph.maxDegree_lt_card_verts _

theorem mem_degMultiset {G : CGraph} {d : ℕ} :
    d ∈ G.degMultiset ↔ ∃ v : G.V, G.toSimple.degree v = d := by
  unfold degMultiset
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, Finset.mem_univ_val v, hv⟩

/-- The maximum degree is the largest entry of the degree multiset. -/
theorem maxDeg_eq_sup (G : CGraph) : G.maxDeg = G.degMultiset.sup := by
  refine le_antisymm ?_ (Multiset.sup_le.2 fun d hd ↦ ?_)
  · rcases isEmpty_or_nonempty G.V with h | h
    · rw [maxDeg, SimpleGraph.maxDegree_of_isEmpty]
      exact Nat.zero_le _
    · obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg h.some
      exact hv ▸ Multiset.le_sup (mem_degMultiset.2 ⟨v, rfl⟩)
  · obtain ⟨v, hv⟩ := mem_degMultiset.1 hd
    exact hv ▸ G.degree_le_maxDeg v

theorem maxDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, d ≤ k) : G.maxDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (maxDeg_le_of_forall fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))
    (hv ▸ G.degree_le_maxDeg v)

theorem minDeg_eq_of_degMultiset {G : CGraph} {k : ℕ} (hmem : k ∈ G.degMultiset)
    (hle : ∀ d ∈ G.degMultiset, k ≤ d) : G.minDeg = k := by
  obtain ⟨v, hv⟩ := mem_degMultiset.1 hmem
  exact le_antisymm (hv ▸ G.minDeg_le_degree v)
    (le_minDeg_of_forall v fun w ↦ hle _ (mem_degMultiset.2 ⟨w, rfl⟩))

/-- Half the handshake lemma: the degree sum is squeezed between `|V|·δ` and `|V|·Δ`. -/
theorem card_mul_minDeg_le (G : CGraph) : Fintype.card G.V * G.minDeg ≤ 2 * G.E := by
  calc Fintype.card G.V * G.minDeg = ∑ _v : G.V, G.minDeg := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ v : G.V, G.toSimple.degree v := Finset.sum_le_sum fun v _ ↦ G.minDeg_le_degree v
    _ = 2 * G.E := SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple

theorem two_mul_E_le_card_mul_maxDeg (G : CGraph) : 2 * G.E ≤ Fintype.card G.V * G.maxDeg := by
  calc 2 * G.E = ∑ v : G.V, G.toSimple.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple).symm
    _ ≤ ∑ _v : G.V, G.maxDeg := Finset.sum_le_sum fun v _ ↦ G.degree_le_maxDeg v
    _ = Fintype.card G.V * G.maxDeg := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ### The disjoint union, the join and the complement -/

theorem maxDeg_disjUnion (G H : CGraph) :
    (disjUnion G H).maxDeg = max G.maxDeg H.maxDeg := by
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

theorem minDeg_disjUnion (G H : CGraph) (a₀ : G.V) (b₀ : H.V) :
    (disjUnion G H).minDeg = min G.minDeg H.minDeg := by
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

theorem maxDeg_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (a₀ : G.V) (b₀ : H.V) :
    (join G H).maxDeg
      = max (G.maxDeg + Fintype.card H.V) (Fintype.card G.V + H.maxDeg) := by
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

theorem minDeg_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (a₀ : G.V) (b₀ : H.V) :
    (join G H).minDeg
      = min (G.minDeg + Fintype.card H.V) (Fintype.card G.V + H.minDeg) := by
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
theorem maxDeg_compl (G : CGraph) [DecidableEq G.V] (v₀ : G.V) :
    (compl G).maxDeg = Fintype.card G.V - 1 - G.minDeg := by
  obtain ⟨v, hv⟩ := G.exists_degree_eq_minDeg v₀
  refine le_antisymm (maxDeg_le_of_forall fun w ↦ ?_) ?_
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.minDeg_le_degree w) _
  · rw [← hv, ← degree_compl]
    exact degree_le_maxDeg _ _

theorem minDeg_compl (G : CGraph) [DecidableEq G.V] (v₀ : G.V) :
    (compl G).minDeg = Fintype.card G.V - 1 - G.maxDeg := by
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  refine le_antisymm ?_ (le_minDeg_of_forall v₀ fun w ↦ ?_)
  · rw [← hv, ← degree_compl]
    exact minDeg_le_degree _ _
  · rw [degree_compl]
    exact Nat.sub_le_sub_left (G.degree_le_maxDeg w) _

/-! ### The four products -/

theorem maxDeg_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (cartesianProduct G H).maxDeg = G.maxDeg + H.maxDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (cartesianProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

theorem minDeg_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (cartesianProduct G H).minDeg = G.minDeg + H.minDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_cartesianProduct G H ((a, b) : (cartesianProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (cartesianProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_cartesianProduct]
    exact Nat.add_le_add (G.minDeg_le_degree _) (H.minDeg_le_degree _)

theorem maxDeg_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (tensorProduct G H).maxDeg = G.maxDeg * H.maxDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (tensorProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.degree_le_maxDeg _) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

theorem minDeg_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (tensorProduct G H).minDeg = G.minDeg * H.minDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_tensorProduct G H ((a, b) : (tensorProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (tensorProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_tensorProduct]
    exact Nat.mul_le_mul (G.minDeg_le_degree _) (H.minDeg_le_degree _)

theorem maxDeg_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (lexProduct G H).maxDeg = G.maxDeg * Fintype.card H.V + H.maxDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_lexProduct G H ((a, b) : (lexProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.degree_le_maxDeg _)) (H.degree_le_maxDeg _)
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

theorem minDeg_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (lexProduct G H).minDeg = G.minDeg * Fintype.card H.V + H.minDeg := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_lexProduct G H ((a, b) : (lexProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (lexProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_lexProduct]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (G.minDeg_le_degree _)) (H.minDeg_le_degree _)

theorem maxDeg_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (strongProduct G H).maxDeg = (G.maxDeg + 1) * (H.maxDeg + 1) - 1 := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_maxDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_maxDeg b₀
  have h := degree_strongProduct G H ((a, b) : (strongProduct G H).V)
  dsimp only at h
  refine le_antisymm (maxDeg_le_of_forall fun p ↦ ?_) ?_
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.degree_le_maxDeg _) _)
      (Nat.add_le_add_right (H.degree_le_maxDeg _) _)) 1
  · rw [← ha, ← hb, ← h]
    exact degree_le_maxDeg _ _

theorem minDeg_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a₀ : G.V) (b₀ : H.V) :
    (strongProduct G H).minDeg = (G.minDeg + 1) * (H.minDeg + 1) - 1 := by
  obtain ⟨a, ha⟩ := G.exists_degree_eq_minDeg a₀
  obtain ⟨b, hb⟩ := H.exists_degree_eq_minDeg b₀
  have h := degree_strongProduct G H ((a, b) : (strongProduct G H).V)
  dsimp only at h
  refine le_antisymm ?_ (le_minDeg_of_forall ((a₀, b₀) : (strongProduct G H).V) fun p ↦ ?_)
  · rw [← ha, ← hb, ← h]
    exact minDeg_le_degree _ _
  · rw [degree_strongProduct]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul (Nat.add_le_add_right (G.minDeg_le_degree _) _)
      (Nat.add_le_add_right (H.minDeg_le_degree _) _)) 1

/-! ### Greedy colouring and Nordhaus–Gaddum -/

section Greedy

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **Greedy colouring**: a graph all of whose degrees are at most `d` is `(d + 1)`-colourable.
The colouring is built one vertex at a time: a vertex has at most `d` neighbours already
coloured, so one of the `d + 1` colours is still free for it. -/
private theorem colorable_of_forall_degree_le (S : SimpleGraph X) [DecidableRel S.Adj] {d : ℕ}
    (hd : ∀ v, S.degree v ≤ d) : S.Colorable (d + 1) := by
  classical
  have key : ∀ s : Finset X, ∃ c : X → Fin (d + 1),
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨fun _ ↦ 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨k, hk⟩ : ∃ k : Fin (d + 1), k ∉ (S.neighborFinset a).image c := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (d + 1))) ⊆ (S.neighborFinset a).image c :=
          fun k _ ↦ hcon k
        have h1 := Finset.card_le_card hsub
        have h2 : ((S.neighborFinset a).image c).card ≤ d :=
          le_trans (Finset.card_image_le) (hd a)
        rw [Finset.card_univ, Fintype.card_fin] at h1
        omega
      refine ⟨Function.update c a k, fun x hx y hy hxy ↦ ?_⟩
      have hax : ∀ z ∈ s, z ≠ a := fun z hz h ↦ ha (h ▸ hz)
      rcases Finset.mem_insert.1 hx with rfl | hx' <;>
        rcases Finset.mem_insert.1 hy with rfl | hy'
      · exact absurd rfl hxy.ne
      · rw [Function.update_self, Function.update_of_ne (hax y hy')]
        intro h
        exact hk (Finset.mem_image.2 ⟨y, by simp [hxy], h.symm⟩)
      · rw [Function.update_self, Function.update_of_ne (hax x hx')]
        intro h
        exact hk (Finset.mem_image.2 ⟨x, by simp [hxy.symm], h⟩)
      · rw [Function.update_of_ne (hax x hx'), Function.update_of_ne (hax y hy')]
        exact hc x hx' y hy' hxy
  obtain ⟨c, hc⟩ := key Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c fun {x y} hxy ↦
    hc x (Finset.mem_univ x) y (Finset.mem_univ y) hxy⟩

end Greedy

/-! ### Greedy colouring -/

/-- **The greedy bound** `χ ≤ Δ + 1`. -/
theorem chromNum_le_maxDeg_add_one (G : CGraph) : G.chromNum ≤ G.maxDeg + 1 := by
  classical
  exact chromNum_le_iff_colorable.2
    (colorable_of_forall_degree_le G.toSimple fun v ↦ G.degree_le_maxDeg v)

/-- Contrapositive of the greedy bound: a `k`-chromatic graph has a vertex of degree `k - 1`. -/
theorem chromNum_le_maxDeg (G : CGraph) (h : 2 ≤ G.chromNum) : G.chromNum - 1 ≤ G.maxDeg := by
  have := G.chromNum_le_maxDeg_add_one
  omega

/-- Independence version of the greedy bound: `|V| ≤ (Δ + 1)·α`. -/
theorem card_le_maxDeg_add_one_mul_indepNum (G : CGraph) :
    Fintype.card G.V ≤ (G.maxDeg + 1) * G.indepNum :=
  le_trans G.card_le_chromNum_mul_indepNum
    (Nat.mul_le_mul_right _ G.chromNum_le_maxDeg_add_one)

/-! ### Colouring around a maximum independent set -/

/-- Colour a maximum independent set with a single colour and every other vertex with its own:
`χ ≤ |V| - α + 1`. -/
theorem chromNum_le_card_sub_indepNum_add_one (G : CGraph) :
    G.chromNum ≤ Fintype.card G.V - G.indepNum + 1 := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcard' : s.card = G.indepNum := hcard
  have hcompl : Fintype.card {v : G.V // v ∉ s} = Fintype.card G.V - G.indepNum := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hcard']
  obtain ⟨e⟩ : Nonempty ({v : G.V // v ∉ s} ≃ Fin (Fintype.card G.V - G.indepNum)) :=
    ⟨Fintype.equivFinOfCardEq hcompl⟩
  set f : G.V → ℕ := fun v ↦ if h : v ∈ s then 0 else (e ⟨v, h⟩ : ℕ) + 1 with hf
  refine chromNum_le_iff_colorable.2 ((SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).2
    ⟨SimpleGraph.Coloring.mk f ?_, fun v ↦ ?_⟩)
  · intro x y hxy
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · exact absurd hxy (hs (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy.ne)
    · simp [hf, hx, hy]
    · simp [hf, hx, hy]
    · simp only [hf, dif_neg hx, dif_neg hy, ne_eq, Nat.add_right_cancel_iff]
      intro h
      exact hxy.ne (congrArg Subtype.val (e.injective (Fin.val_injective h)))
  · show f v < _
    by_cases h : v ∈ s
    · simp [hf, h]
    · simp only [hf, dif_neg h]
      have := (e ⟨v, h⟩).isLt
      omega

/-- The same bound in additive form. -/
theorem chromNum_add_indepNum_le_card_add_one (G : CGraph) :
    G.chromNum + G.indepNum ≤ Fintype.card G.V + 1 := by
  have h := G.chromNum_le_card_sub_indepNum_add_one
  have h2 : G.indepNum ≤ Fintype.card G.V := by
    obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
    have hcard' : G.indepNum = s.card := hcard.symm
    rw [hcard', ← Finset.card_univ]
    exact Finset.card_le_univ s
  omega

section NordhausGaddum

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The number of colours needed to colour just the vertices of `s` properly, ignoring every
vertex outside `s`.  This is the chromatic number of the subgraph induced on `s`, phrased so
that induction can add one vertex at a time. -/
private noncomputable def chromOn (S : SimpleGraph X) (s : Finset X) : ℕ :=
  sInf {n | ∃ c : X → ℕ, (∀ v ∈ s, c v < n) ∧ ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y}

omit [Fintype X] [DecidableEq X] in
private theorem chromOn_le {S : SimpleGraph X} {s : Finset X} {n : ℕ} (c : X → ℕ)
    (hb : ∀ v ∈ s, c v < n) (hp : ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y) :
    chromOn S s ≤ n :=
  Nat.sInf_le ⟨c, hb, hp⟩

omit [DecidableEq X] in
private theorem exists_chromOn_coloring (S : SimpleGraph X) (s : Finset X) :
    ∃ c : X → ℕ, (∀ v ∈ s, c v < chromOn S s) ∧
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y := by
  have hne : {n | ∃ c : X → ℕ, (∀ v ∈ s, c v < n) ∧
      ∀ x ∈ s, ∀ y ∈ s, S.Adj x y → c x ≠ c y}.Nonempty := by
    refine ⟨Fintype.card X, fun v ↦ (Fintype.equivFin X v : ℕ),
      fun v _ ↦ (Fintype.equivFin X v).isLt, fun x _ y _ hxy h ↦ ?_⟩
    exact hxy.ne ((Fintype.equivFin X).injective (Fin.val_injective h))
  exact Nat.sInf_mem hne

omit [Fintype X] [DecidableEq X] in
private theorem chromOn_empty (S : SimpleGraph X) : chromOn S ∅ = 0 :=
  Nat.le_zero.1 (chromOn_le (fun _ ↦ 0) (by simp) (by simp))

private theorem chromOn_insert_le (S : SimpleGraph X) (a : X) (s : Finset X) :
    chromOn S (insert a s) ≤ chromOn S s + 1 := by
  obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring S s
  refine chromOn_le (Function.update c a (chromOn S s)) ?_ ?_
  · intro v hv
    rcases eq_or_ne v a with rfl | hva
    · rw [Function.update_self]; omega
    · rw [Function.update_of_ne hva]
      have := hb v ((Finset.mem_insert.1 hv).resolve_left hva)
      omega
  · intro x hx y hy hxy
    rcases eq_or_ne x a with rfl | hxa
    · rcases eq_or_ne y x with rfl | hyx
      · exact absurd rfl hxy.ne
      · rw [Function.update_self, Function.update_of_ne hyx]
        exact fun h ↦ absurd (hb y ((Finset.mem_insert.1 hy).resolve_left hyx)) (by omega)
    · rcases eq_or_ne y a with rfl | hya
      · rw [Function.update_self, Function.update_of_ne hxa]
        exact fun h ↦ absurd (hb x ((Finset.mem_insert.1 hx).resolve_left hxa)) (by omega)
      · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
        exact hp x ((Finset.mem_insert.1 hx).resolve_left hxa)
          y ((Finset.mem_insert.1 hy).resolve_left hya) hxy

/-- If the neighbours of `a` inside `s` fit into a set smaller than `χ(s)`, then `a` can reuse
one of the colours already in play: adding it costs nothing. -/
private theorem chromOn_insert_le_of_lt (S : SimpleGraph X) {a : X} {s t : Finset X} (ha : a ∉ s)
    (ht : ∀ v ∈ s, S.Adj a v → v ∈ t) (hlt : t.card < chromOn S s) :
    chromOn S (insert a s) ≤ chromOn S s := by
  obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring S s
  obtain ⟨k, hk⟩ : ((Finset.range (chromOn S s)) \ (t.image c)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff (t.image c) (Finset.range (chromOn S s))
    have h2 : (t.image c).card ≤ t.card := Finset.card_image_le
    have h3 : (Finset.range (chromOn S s)).card = chromOn S s := Finset.card_range _
    omega
  rw [Finset.mem_sdiff, Finset.mem_range] at hk
  obtain ⟨hklt, hkni⟩ := hk
  have hane : ∀ v ∈ s, v ≠ a := fun v hv h ↦ ha (h ▸ hv)
  refine chromOn_le (Function.update c a k) ?_ ?_
  · intro v hv
    rcases eq_or_ne v a with rfl | hva
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hva]
      exact hb v ((Finset.mem_insert.1 hv).resolve_left hva)
  · intro x hx y hy hxy
    rcases eq_or_ne x a with rfl | hxa
    · have hys : y ∈ s := (Finset.mem_insert.1 hy).resolve_left (Ne.symm hxy.ne)
      rw [Function.update_self, Function.update_of_ne (hane y hys)]
      exact fun h ↦ hkni (Finset.mem_image.2 ⟨y, ht y hys hxy, h.symm⟩)
    · rcases eq_or_ne y a with rfl | hya
      · have hxs : x ∈ s := (Finset.mem_insert.1 hx).resolve_left hxa
        rw [Function.update_self, Function.update_of_ne (hane x hxs)]
        exact fun h ↦ hkni (Finset.mem_image.2 ⟨x, ht x hxs hxy.symm, h⟩)
      · rw [Function.update_of_ne hxa, Function.update_of_ne hya]
        exact hp x ((Finset.mem_insert.1 hx).resolve_left hxa)
          y ((Finset.mem_insert.1 hy).resolve_left hya) hxy

/-- **Nordhaus–Gaddum, sum form**, in the `chromOn` formulation: colouring `s` in `S` and in its
complement together costs at most `|s| + 1` colours. -/
private theorem chromOn_add_chromOn_compl_le (S : SimpleGraph X) (s : Finset X) :
    chromOn S s + chromOn Sᶜ s ≤ s.card + 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp [chromOn_empty]
  | insert a s ha ih =>
    have h1 := chromOn_insert_le S a s
    have h2 := chromOn_insert_le Sᶜ a s
    rw [Finset.card_insert_of_notMem ha]
    by_cases hA : chromOn S (insert a s) ≤ chromOn S s
    · omega
    by_cases hB : chromOn Sᶜ (insert a s) ≤ chromOn Sᶜ s
    · omega
    have hpa : chromOn S s ≤ (s.filter fun v ↦ S.Adj a v).card := by
      by_contra hcon
      push_neg at hcon
      exact hA (chromOn_insert_le_of_lt S ha (fun v hv hadj ↦ Finset.mem_filter.2 ⟨hv, hadj⟩) hcon)
    have hqa : chromOn Sᶜ s ≤ (s.filter fun v ↦ ¬ S.Adj a v).card := by
      by_contra hcon
      push_neg at hcon
      refine hB (chromOn_insert_le_of_lt Sᶜ ha (fun v hv hadj ↦ Finset.mem_filter.2 ⟨hv, ?_⟩) hcon)
      exact (SimpleGraph.compl_adj S a v).1 hadj |>.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := s) (p := fun v ↦ S.Adj a v)
    omega

end NordhausGaddum

private theorem chromNum_eq_chromOn_univ (G : CGraph) [DecidableEq G.V] :
    G.chromNum = chromOn G.toSimple Finset.univ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨c, hb, hp⟩ := exists_chromOn_coloring G.toSimple Finset.univ
    refine chromNum_le_iff_colorable.2 ((SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).2
      ⟨SimpleGraph.Coloring.mk c fun {x y} hxy ↦
        hp x (Finset.mem_univ x) y (Finset.mem_univ y) hxy, fun v ↦ hb v (Finset.mem_univ v)⟩)
  · obtain ⟨C, hC⟩ := (SimpleGraph.colorable_iff_exists_bdd_nat_coloring _).1 G.colorable_chromNum
    exact chromOn_le (fun v ↦ C v) (fun v _ ↦ hC v)
      (fun x _ y _ hxy ↦ C.valid hxy)

/-- **Nordhaus–Gaddum, sum form**: `χ(G) + χ(Gᶜ) ≤ |V| + 1`. -/
theorem chromNum_add_chromNum_compl_le_card_add_one (G : CGraph) [DecidableEq G.V] :
    G.chromNum + (compl G).chromNum ≤ Fintype.card G.V + 1 := by
  have h := chromOn_add_chromOn_compl_le G.toSimple (Finset.univ : Finset G.V)
  rw [Finset.card_univ] at h
  rwa [G.chromNum_eq_chromOn_univ, show (compl G).chromNum = chromOn G.toSimpleᶜ Finset.univ from
    by rw [(compl G).chromNum_eq_chromOn_univ, compl_toSimple]]

section Turan

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Being `n`-clique-free is the same as having clique number below `n`. -/
private theorem cliqueFree_iff_cliqueNum_lt {S : SimpleGraph X} {n : ℕ} :
    S.CliqueFree n ↔ S.cliqueNum < n := by
  constructor
  · intro hcf
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs⟩ := S.exists_isNClique_cliqueNum
    obtain ⟨t, hts, htc⟩ :=
      Finset.exists_subset_card_eq (n := n) (show n ≤ s.card by rw [hs.card_eq]; exact hcon)
    exact hcf t ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
  · intro hlt s hs
    exact absurd (hs.card_eq ▸ hs.isClique.card_le_cliqueNum) (by omega)

omit [DecidableEq X] in
/-- **Turán's theorem**, in the loose form `2r·|E| ≤ (r - 1)·|V|²`: a graph with no `K_{r+1}`
has at most as many edges as the Turán graph, which has at most that many. -/
private theorem mul_card_edgeFinset_le_of_cliqueFree {S : SimpleGraph X} [DecidableRel S.Adj]
    {r : ℕ} (hr : 0 < r) (cf : S.CliqueFree (r + 1)) :
    2 * r * S.edgeFinset.card ≤ (r - 1) * (Fintype.card X) ^ 2 := by
  classical
  obtain ⟨H, _, maxH⟩ := SimpleGraph.exists_isTuranMaximal (V := X) hr
  have h1 : S.edgeFinset.card ≤ H.edgeFinset.card := maxH.2 cf
  have h3 : H.edgeFinset.card = (SimpleGraph.turanGraph (Fintype.card X) r).edgeFinset.card :=
    ((SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH).some.card_edgeFinset_eq
  calc 2 * r * S.edgeFinset.card
      ≤ 2 * r * (SimpleGraph.turanGraph (Fintype.card X) r).edgeFinset.card := by
        rw [← h3]; exact Nat.mul_le_mul_left _ h1
    _ ≤ (r - 1) * (Fintype.card X) ^ 2 := SimpleGraph.mul_card_edgeFinset_turanGraph_le

end Turan

/-! ### Turán's theorem -/

/-- **Turán's theorem**: a graph whose clique number is at most `r` has `2r·|E| ≤ (r - 1)·|V|²`
edges. -/
theorem two_mul_mul_E_le (G : CGraph) {r : ℕ} (hr : 0 < r) (h : G.cliqueNum ≤ r) :
    2 * r * G.E ≤ (r - 1) * (Fintype.card G.V) ^ 2 :=
  mul_card_edgeFinset_le_of_cliqueFree hr
    (cliqueFree_iff_cliqueNum_lt.2 (Nat.lt_succ_of_le h))

/-- **Mantel's theorem**: a triangle-free graph has at most `|V|²/4` edges. -/
theorem four_mul_E_le_card_sq (G : CGraph) (h : G.cliqueNum ≤ 2) :
    4 * G.E ≤ (Fintype.card G.V) ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-- **A bipartite graph is triangle-free**, hence has clique number at most two. -/
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
    (h : (Fintype.card G.V) ^ 2 < 4 * G.E) : 3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_card_sq (by omega)) (by omega)

section Ramsey

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- **The key pigeonhole step.**  If `v` has three neighbours in `T`, then either two of them are
adjacent — giving a triangle through `v` — or they are pairwise non-adjacent, giving a triangle in
the complement. -/
private theorem three_le_cliqueNum_of_neighbors (T : SimpleGraph X) (v : X) (A : Finset X)
    (hA : ∀ x ∈ A, T.Adj v x) (hcard : 3 ≤ A.card) :
    3 ≤ T.cliqueNum ∨ 3 ≤ Tᶜ.cliqueNum := by
  classical
  by_cases hex : ∃ x ∈ A, ∃ y ∈ A, T.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hex
    left
    have hcl : T.IsNClique 3 {v, x, y} :=
      SimpleGraph.is3Clique_triple_iff.2 ⟨hA x hx, hA y hy, hxy⟩
    have := hcl.isClique.card_le_cliqueNum
    rwa [hcl.card_eq] at this
  · push_neg at hex
    right
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 3) hcard
    have hcl : Tᶜ.IsClique (t : Set X) := by
      intro x hx y hy hxy
      exact ⟨hxy, hex x (hts (Finset.mem_coe.1 hx)) y (hts (Finset.mem_coe.1 hy))⟩
    have := hcl.card_le_cliqueNum
    rwa [htc] at this

/-- **Ramsey's theorem for `R(3, 3)`, complement form**: on six or more vertices, either the graph
or its complement contains a triangle.  Fix a vertex `v`: of the five other vertices, three are
neighbours of `v` or three are non-neighbours, and either way the pigeonhole step above applies. -/
private theorem three_le_cliqueNum_or_compl (T : SimpleGraph X) (h : 6 ≤ Fintype.card X) :
    3 ≤ T.cliqueNum ∨ 3 ≤ Tᶜ.cliqueNum := by
  classical
  obtain ⟨v⟩ : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  set N := T.neighborFinset v with hN
  set M := (Finset.univ : Finset X) \ insert v N with hM
  have hvN : v ∉ N := by simp [hN]
  have hins := Finset.card_le_univ (insert v N)
  rw [Finset.card_insert_of_notMem hvN] at hins
  have hcards : N.card + M.card + 1 = Fintype.card X := by
    rw [hM, Finset.card_univ_diff, Finset.card_insert_of_notMem hvN]
    omega
  have hMadj : ∀ x ∈ M, Tᶜ.Adj v x := by
    intro x hx
    rw [hM, Finset.mem_sdiff, Finset.mem_insert] at hx
    push_neg at hx
    refine (SimpleGraph.compl_adj _ _ _).2 ⟨fun hvx ↦ hx.2.1 hvx.symm, fun hadj ↦ hx.2.2 ?_⟩
    rw [hN, SimpleGraph.mem_neighborFinset]
    exact hadj
  rcases (show 3 ≤ N.card ∨ 3 ≤ M.card by omega) with hc | hc
  · exact three_le_cliqueNum_of_neighbors T v N
      (fun x hx ↦ (SimpleGraph.mem_neighborFinset _ _ _).1 hx) hc
  · have := three_le_cliqueNum_of_neighbors Tᶜ v M hMadj hc
    rw [or_comm] at this
    simpa using this

omit [Fintype X] [DecidableEq X] in
/-- **Erdős–Szekeres**: inside any vertex set of size at least `C(s + t, s)` there is a clique of
size `s` or a clique of size `t` in the complement.  The induction is the classical one: pick a
vertex `v` of `u`, split the rest into the neighbours `A` and non-neighbours `B` of `v`; Pascal's
rule says `|A| ≥ C(s - 1 + t, s - 1)` or `|B| ≥ C(s + t - 1, s)`, and in each case the smaller
instance either already gives what is wanted or gives a set that `v` extends. -/
private theorem exists_clique_or_clique_compl (T : SimpleGraph X) :
    ∀ (s t : ℕ) (u : Finset X), (s + t).choose s ≤ u.card →
      (∃ c ⊆ u, T.IsClique (c : Set X) ∧ c.card = s) ∨
      (∃ c ⊆ u, Tᶜ.IsClique (c : Set X) ∧ c.card = t) := by
  classical
  intro s
  induction s with
  | zero => exact fun t u _ ↦ Or.inl ⟨∅, by simp, by simp, rfl⟩
  | succ s ihs =>
    intro t
    induction t with
    | zero => exact fun u _ ↦ Or.inr ⟨∅, by simp, by simp, rfl⟩
    | succ t iht =>
      intro u hu
      have hpascal : (s + 1 + (t + 1)).choose (s + 1)
          = (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        have e1 : s + 1 + (t + 1) = s + t + 1 + 1 := by omega
        have e2 : s + (t + 1) = s + t + 1 := by omega
        have e3 : s + 1 + t = s + t + 1 := by omega
        rw [e1, e2, e3, Nat.choose_succ_succ]
      have hpos : 0 < u.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hu
      obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
      set A := (u.erase v).filter (fun x ↦ T.Adj v x) with hA
      set B := (u.erase v).filter (fun x ↦ ¬ T.Adj v x) with hB
      have hsplit : A.card + B.card = (u.erase v).card :=
        Finset.card_filter_add_card_filter_not _
      have herase : (u.erase v).card = u.card - 1 := Finset.card_erase_of_mem hv
      have hAu : A ⊆ u := fun x hx ↦ Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
      have hBu : B ⊆ u := fun x hx ↦ Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
      rcases (show (s + (t + 1)).choose s ≤ A.card ∨ (s + 1 + t).choose (s + 1) ≤ B.card by
        omega) with hc | hc
      · rcases ihs (t + 1) A hc with ⟨c, hcA, hcl, hcard⟩ | ⟨c, hcA, hcl, hcard⟩
        · left
          have hvc : v ∉ c := fun hmem ↦
            (Finset.mem_erase.1 (Finset.mem_filter.1 (hcA hmem)).1).1 rfl
          refine ⟨insert v c, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx
            · exact hv
            · exact hAu (hcA hx)
          · rw [Finset.coe_insert]
            exact hcl.insert fun b hb _ ↦ (Finset.mem_filter.1 (hcA (Finset.mem_coe.1 hb))).2
          · rw [Finset.card_insert_of_notMem hvc, hcard]
        · exact Or.inr ⟨c, fun x hx ↦ hAu (hcA hx), hcl, hcard⟩
      · rcases iht B hc with ⟨c, hcB, hcl, hcard⟩ | ⟨c, hcB, hcl, hcard⟩
        · exact Or.inl ⟨c, fun x hx ↦ hBu (hcB hx), hcl, hcard⟩
        · right
          have hvc : v ∉ c := fun hmem ↦
            (Finset.mem_erase.1 (Finset.mem_filter.1 (hcB hmem)).1).1 rfl
          refine ⟨insert v c, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx
            · exact hv
            · exact hBu (hcB hx)
          · rw [Finset.coe_insert]
            refine hcl.insert fun b hb hne ↦ (SimpleGraph.compl_adj _ _ _).2 ⟨hne, ?_⟩
            exact (Finset.mem_filter.1 (hcB (Finset.mem_coe.1 hb))).2
          · rw [Finset.card_insert_of_notMem hvc, hcard]

end Ramsey

/-! ### The Ramsey number `R(3, 3)` -/

/-- **`R(3, 3) ≤ 6`**: any graph on at least six vertices has three mutually adjacent vertices or
three mutually non-adjacent ones. -/
theorem three_le_cliqueNum_or_three_le_indepNum (G : CGraph) (h : 6 ≤ Fintype.card G.V) :
    3 ≤ G.cliqueNum ∨ 3 ≤ G.indepNum := by
  classical
  have := three_le_cliqueNum_or_compl G.toSimple h
  rwa [SimpleGraph.cliqueNum_compl] at this

/-- Triangle-free form: a triangle-free graph on six or more vertices has three pairwise
non-adjacent vertices. -/
theorem three_le_indepNum_of_cliqueNum_le_two (G : CGraph) (h : 6 ≤ Fintype.card G.V)
    (hcl : G.cliqueNum ≤ 2) : 3 ≤ G.indepNum := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · omega
  · exact h'

/-! ### Ramsey numbers in general -/

/-- **Ramsey's theorem**, `R(s, t) ≤ C(s + t, s)`: a graph on at least `C(s + t, s)` vertices has
a clique on `s` vertices or an independent set on `t` vertices. -/
theorem le_cliqueNum_or_le_indepNum (G : CGraph) {s t : ℕ}
    (h : (s + t).choose s ≤ Fintype.card G.V) : s ≤ G.cliqueNum ∨ t ≤ G.indepNum := by
  classical
  rcases exists_clique_or_clique_compl G.toSimple s t Finset.univ
      (by rwa [Finset.card_univ]) with ⟨c, -, hcl, hcard⟩ | ⟨c, -, hcl, hcard⟩
  · exact Or.inl (hcard ▸ hcl.card_le_cliqueNum)
  · refine Or.inr ?_
    have := hcl.card_le_cliqueNum
    rw [hcard, SimpleGraph.cliqueNum_compl] at this
    exact this

section Gallai

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- **Gallai's identity** at the level of `SimpleGraph`: the complement of a vertex cover is an
independent set and vice versa, so `τ + α = |V|`. -/
private theorem vertexCoverNum_toNat_add_indepNum (S : SimpleGraph X) :
    S.vertexCoverNum.toNat + S.indepNum = Fintype.card X := by
  classical
  obtain ⟨s, hs⟩ := S.exists_isNIndepSet_indepNum
  have hα : s.card = S.indepNum := hs.card_eq
  have hαle : S.indepNum ≤ Fintype.card X := by
    rw [← hα, ← Finset.card_univ]
    exact Finset.card_le_univ s
  -- `τ ≤ |V| - α`, using the complement of a maximum independent set as a cover.
  have hle : S.vertexCoverNum.toNat + S.indepNum ≤ Fintype.card X := by
    have hcov : S.IsVertexCover ((s : Set X)ᶜ) :=
      SimpleGraph.isVertexCover_compl.2 hs.isIndepSet
    have h1 := hcov.vertexCoverNum_le
    rw [← Finset.coe_compl, Set.encard_coe_eq_coe_finsetCard, Finset.card_compl] at h1
    have h2 : S.vertexCoverNum.toNat ≤ Fintype.card X - s.card := by
      have := ENat.toNat_le_toNat h1 (by simp)
      simpa using this
    omega
  -- `|V| - α ≤ τ`, since the complement of a minimum cover is independent.
  have hge : Fintype.card X ≤ S.vertexCoverNum.toNat + S.indepNum := by
    obtain ⟨c, hcard, hcov⟩ := S.vertexCoverNum_exists
    have hind : S.IsIndepSet cᶜ := SimpleGraph.isIndepSet_compl_iff_isVertexCover.2 hcov
    have hfin : S.IsIndepSet ((cᶜ.toFinset : Finset X) : Set X) := by
      rwa [Set.coe_toFinset]
    have h1 : (cᶜ.toFinset : Finset X).card ≤ S.indepNum := hfin.card_le_indepNum
    have h2 : c.toFinset.card + cᶜ.toFinset.card = Fintype.card X := by
      rw [Set.toFinset_compl, Finset.card_compl]
      have := Finset.card_le_univ c.toFinset
      omega
    have h3 : S.vertexCoverNum.toNat = c.toFinset.card := by
      have hc : c.encard = (c.toFinset.card : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
      rw [← hcard, hc]
      simp
    omega
  omega

omit [DecidableEq X] in
/-- A minimum vertex cover, as a `Finset`. -/
private theorem exists_cover_finset (S : SimpleGraph X) :
    ∃ C : Finset X, (∀ ⦃x y⦄, S.Adj x y → x ∈ C ∨ y ∈ C) ∧
      C.card = S.vertexCoverNum.toNat := by
  classical
  obtain ⟨c, hcard, hcov⟩ := S.vertexCoverNum_exists
  refine ⟨c.toFinset, fun x y hxy ↦ ?_, ?_⟩
  · simpa using hcov hxy
  · have hc : c.encard = (c.toFinset.card : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
    rw [← hcard, hc]
    simp

/-- **Every edge meets the cover**, so the edges are covered by the incidence sets of the `τ`
cover vertices, each of which has at most `Δ` edges: `|E| ≤ τ·Δ`. -/
private theorem card_edgeFinset_le_vertexCoverNum_mul_maxDegree (S : SimpleGraph X)
    [DecidableRel S.Adj] :
    S.edgeFinset.card ≤ S.vertexCoverNum.toNat * S.maxDegree := by
  classical
  obtain ⟨C, hC, hcard⟩ := exists_cover_finset S
  have hsub : S.edgeFinset ⊆ C.biUnion (fun v ↦ S.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hC he with hx | hy
    · exact Finset.mem_biUnion.2 ⟨x, hx, by
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨(SimpleGraph.mem_edgeSet _).2 he, by simp⟩⟩
    · exact Finset.mem_biUnion.2 ⟨y, hy, by
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨(SimpleGraph.mem_edgeSet _).2 he, by simp⟩⟩
  calc S.edgeFinset.card ≤ (C.biUnion (fun v ↦ S.incidenceFinset v)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ C, (S.incidenceFinset v).card := Finset.card_biUnion_le
    _ ≤ C.card * S.maxDegree := by
        rw [← smul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun v _ ↦ ?_
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact SimpleGraph.degree_le_maxDegree S v
    _ = S.vertexCoverNum.toNat * S.maxDegree := by rw [hcard]

end Gallai

/-! ### The vertex cover number -/

/-- **Gallai's identity**: a set of vertices is a vertex cover exactly when its complement is
independent, so `τ(G) + α(G) = |V|`. -/
theorem coverNum_add_indepNum (G : CGraph) :
    G.coverNum + G.indepNum = Fintype.card G.V := by
  classical
  exact vertexCoverNum_toNat_add_indepNum G.toSimple

/-- **`|E| ≤ τ·Δ`**: each of the `τ` cover vertices takes care of at most `Δ` edges. -/
theorem E_le_coverNum_mul_maxDeg (G : CGraph) : G.E ≤ G.coverNum * G.maxDeg := by
  classical
  exact card_edgeFinset_le_vertexCoverNum_mul_maxDegree G.toSimple

/-- A vertex cover needs at most one vertex per edge. -/
theorem coverNum_le_E (G : CGraph) : G.coverNum ≤ G.E := by
  classical
  have h := G.toSimple.vertexCoverNum_le_encard_edgeSet
  have he : G.toSimple.edgeSet.encard = (G.E : ℕ∞) := by
    rw [← SimpleGraph.coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard]
    rfl
  rw [he] at h
  simpa using ENat.toNat_le_toNat h (by simp)

/-- A graph with an edge is not independent as a whole. -/
theorem indepNum_lt_card_of_E_pos (G : CGraph) (h : 0 < G.E) :
    G.indepNum < Fintype.card G.V := by
  classical
  obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos h
  obtain ⟨s, hs⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hcards : s.card = G.indepNum := hs.card_eq
  have hle : G.indepNum ≤ Fintype.card G.V := by
    rw [← hcards, ← Finset.card_univ]
    exact Finset.card_le_univ s
  rcases Nat.lt_or_ge G.indepNum (Fintype.card G.V) with h' | h'
  · exact h'
  · exfalso
    have huniv : s = Finset.univ := Finset.eq_univ_of_card s (by rw [hcards]; omega)
    have hmem : ∀ x : G.V, x ∈ (s : Set G.V) := by
      intro x
      rw [huniv]
      simp
    exact hs.isIndepSet (hmem a) (hmem b) ((toSimple_adj _ _ _).2 hab).ne
      ((toSimple_adj _ _ _).2 hab)

section CliqueCoclique

variable {G : CGraph} [DecidableEq G.V]

/-- The automorphism group of `G`, as a `Finset` of permutations of the vertex type.  Working
with permutations rather than with `G ≃cg G` keeps everything inside `Fintype` land. -/
private def autFinset (G : CGraph) [DecidableEq G.V] : Finset (Equiv.Perm G.V) :=
  Finset.univ.filter fun σ ↦ ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y

private theorem mem_autFinset {σ : Equiv.Perm G.V} :
    σ ∈ autFinset G ↔ ∀ x y, G.Adj (σ x) (σ y) = G.Adj x y := by
  simp [autFinset]

private theorem one_mem_autFinset : (1 : Equiv.Perm G.V) ∈ autFinset G := by
  rw [mem_autFinset]; intro x y; rfl

private theorem mul_mem_autFinset {σ τ : Equiv.Perm G.V} (hσ : σ ∈ autFinset G)
    (hτ : τ ∈ autFinset G) : σ * τ ∈ autFinset G := by
  rw [mem_autFinset] at hσ hτ ⊢
  intro x y
  simp only [Equiv.Perm.mul_apply]
  rw [hσ, hτ]

private theorem inv_mem_autFinset {σ : Equiv.Perm G.V} (hσ : σ ∈ autFinset G) :
    σ⁻¹ ∈ autFinset G := by
  rw [mem_autFinset] at hσ ⊢
  intro x y
  have h := hσ (σ⁻¹ x) (σ⁻¹ y)
  simpa using h.symm

private theorem mem_autFinset_of_iso (σ : G ≃cg G) : σ.toEquiv ∈ autFinset G := by
  rw [mem_autFinset]
  intro x y
  exact σ.adj_eq x y

/-- All fibres of the map `σ ↦ σ c` have the same size, for a vertex-transitive graph: the
fibre over `(c, v)` is carried onto the fibre over `(c', v')` by `σ ↦ β σ α` for automorphisms
`α : c' ↦ c` and `β : v ↦ v'`. -/
private theorem card_autFinset_filter_eq (hvt : G.IsVertexTransitive) (c v c' v' : G.V) :
    ((autFinset G).filter fun σ ↦ σ c = v).card
      = ((autFinset G).filter fun σ ↦ σ c' = v').card := by
  obtain ⟨a, ha⟩ := hvt c' c
  obtain ⟨b, hb⟩ := hvt v v'
  set α : Equiv.Perm G.V := a.toEquiv with hα
  set β : Equiv.Perm G.V := b.toEquiv with hβ
  have hαmem : α ∈ autFinset G := mem_autFinset_of_iso a
  have hβmem : β ∈ autFinset G := mem_autFinset_of_iso b
  have hac : α c' = c := ha
  have hbv : β v = v' := hb
  refine Finset.card_nbij' (fun σ ↦ β * σ * α) (fun τ ↦ β⁻¹ * τ * α⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hσ ⊢
    refine ⟨mul_mem_autFinset (mul_mem_autFinset hβmem hσ.1) hαmem, ?_⟩
    simp only [Equiv.Perm.mul_apply, hac, hσ.2, hbv]
  · intro τ hτ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hτ ⊢
    refine ⟨mul_mem_autFinset (mul_mem_autFinset (inv_mem_autFinset hβmem) hτ.1)
      (inv_mem_autFinset hαmem), ?_⟩
    have hc : α⁻¹ c = c' := by rw [← hac]; simp
    have hv : β⁻¹ v' = v := by rw [← hbv]; simp
    simp only [Equiv.Perm.mul_apply, hc, hτ.2, hv]
  · intro σ _
    group
  · intro τ _
    group

end CliqueCoclique

/-! ### The clique–coclique bound -/

/-- **The clique–coclique bound**: in a vertex-transitive graph, `α · ω ≤ |V|`.

The proof is a double count of the pairs `(σ, c)` with `σ` an automorphism, `c` a vertex of a
fixed maximum clique `C`, and `σ c` in a fixed maximum independent set `S`.  For each `σ` there
is at most one such `c`, since `σ C` is a clique and `S` is independent; on the other hand each
of the `|C| · |S|` pairs `(c, v)` is realised by exactly `|Aut G| / |V|` automorphisms, because
the action is transitive. -/
theorem indepNum_mul_cliqueNum_le_card (G : CGraph) (hvt : G.IsVertexTransitive) :
    G.indepNum * G.cliqueNum ≤ Fintype.card G.V := by
  classical
  obtain ⟨S, hS, hScard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  obtain ⟨C, hC, hCcard⟩ := G.toSimple.exists_isNClique_cliqueNum
  rcases Finset.eq_empty_or_nonempty C with rfl | ⟨c₀, hc₀⟩
  · rw [Finset.card_empty] at hCcard
    have hz : G.cliqueNum = 0 := hCcard.symm
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
  set Γ : Finset (Equiv.Perm G.V) := autFinset G with hΓ
  set m : ℕ := (Γ.filter fun σ ↦ σ c₀ = c₀).card with hm
  -- every fibre has size `m`
  have hfib : ∀ c v : G.V, (Γ.filter fun σ ↦ σ c = v).card = m := fun c v ↦
    card_autFinset_filter_eq hvt c v c₀ c₀
  -- the fibres over a fixed `c` partition the automorphism group
  have hcard : Γ.card = Fintype.card G.V * m := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := fun σ : Equiv.Perm G.V ↦ σ c₀) (s := Γ) (t := Finset.univ)
      (fun x _ ↦ Finset.mem_univ _)
    rw [this]
    rw [Finset.sum_congr rfl fun v _ ↦ hfib c₀ v, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  -- the double count
  set N : ℕ := ∑ σ ∈ Γ, (C.filter fun c ↦ σ c ∈ S).card with hN
  have hupper : N ≤ Γ.card := by
    have hone : ∀ σ ∈ Γ, (C.filter fun c ↦ σ c ∈ S).card ≤ 1 := by
      intro σ hσ
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hne
      have hadj : G.toSimple.Adj x y := hC hx.1 hy.1 hne
      have hadj' : G.toSimple.Adj (σ x) (σ y) := by
        rw [toSimple_adj] at hadj ⊢
        rw [(mem_autFinset.1 hσ) x y]
        exact hadj
      exact hS hx.2 hy.2 (fun h ↦ hne (σ.injective h)) hadj'
    calc N ≤ Γ.card • 1 := Finset.sum_le_card_nsmul _ _ 1 hone
      _ = Γ.card := by simp
  have hlower : N = C.card * (S.card * m) := by
    have h1 : N = ∑ c ∈ C, (Γ.filter fun σ ↦ σ c ∈ S).card := by
      simp only [hN, Finset.card_filter]
      exact Finset.sum_comm
    have h2 : ∀ c : G.V, (Γ.filter fun σ ↦ σ c ∈ S).card = S.card * m := by
      intro c
      have h3 := Finset.card_eq_sum_card_fiberwise
        (f := fun σ : Equiv.Perm G.V ↦ σ c) (s := Γ.filter fun σ ↦ σ c ∈ S) (t := S)
        (fun x hx ↦ (Finset.mem_filter.1 hx).2)
      rw [h3]
      have h4 : ∀ v ∈ S, ((Γ.filter fun σ ↦ σ c ∈ S).filter fun σ ↦ σ c = v).card = m := by
        intro v hv
        rw [Finset.filter_filter]
        rw [Finset.filter_congr (q := fun σ ↦ σ c = v) fun σ _ ↦
          ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hv, h⟩⟩]
        exact hfib c v
      rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul]
    rw [h1, Finset.sum_congr rfl fun c _ ↦ h2 c, Finset.sum_const, smul_eq_mul]
  -- put the two halves together and cancel the common factor `m`
  have hmpos : 0 < m := by
    rw [hm]
    refine Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨one_mem_autFinset, rfl⟩⟩
  have hfinal : S.card * C.card * m ≤ Fintype.card G.V * m := by
    calc S.card * C.card * m = C.card * (S.card * m) := by ring
      _ = N := hlower.symm
      _ ≤ Γ.card := hupper
      _ = Fintype.card G.V * m := hcard
  have := Nat.le_of_mul_le_mul_right hfinal hmpos
  rwa [hScard, hCcard] at this

/-- A graph with `α · ω > |V|` cannot be vertex-transitive. -/
theorem not_isVertexTransitive_of_card_lt (G : CGraph)
    (h : Fintype.card G.V < G.indepNum * G.cliqueNum) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.indepNum_mul_cliqueNum_le_card hvt) (by omega)

/-! ### The domination number -/

theorem domNum_le_card_of_isDominatingSet {s : Finset G.V} (h : G.IsDominatingSet s) :
    G.domNum ≤ s.card :=
  Nat.sInf_le ⟨s, rfl, h⟩

/-- A dominating set of the minimum size `γ`. -/
theorem exists_isDominatingSet_domNum (G : CGraph) :
    ∃ s : Finset G.V, s.card = G.domNum ∧ G.IsDominatingSet s := by
  have hne : {n | ∃ s : Finset G.V, s.card = n ∧ G.IsDominatingSet s}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, rfl, isDominatingSet_univ G⟩
  obtain ⟨s, hcard, hs⟩ := Nat.sInf_mem hne
  exact ⟨s, hcard, hs⟩

theorem domNum_le_card (G : CGraph) : G.domNum ≤ Fintype.card G.V := by
  have := domNum_le_card_of_isDominatingSet (isDominatingSet_univ G)
  rwa [Finset.card_univ] at this

@[simp] theorem domNum_eq_zero_iff (G : CGraph) : G.domNum = 0 ↔ Fintype.card G.V = 0 := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
    rw [h, Finset.card_eq_zero] at hcard
    subst hcard
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun v ↦ ?_⟩
    rcases hs v with hv | ⟨u, hu, -⟩
    · simp at hv
    · simp at hu
  · intro h
    have := G.domNum_le_card
    omega

theorem domNum_pos (G : CGraph) (h : 0 < Fintype.card G.V) : 0 < G.domNum := by
  have := (G.domNum_eq_zero_iff).not.2 (by omega : ¬ Fintype.card G.V = 0)
  omega

/-- A vertex adjacent to everything else dominates on its own. -/
theorem domNum_eq_one_of_universal {v : G.V} (h : ∀ u, u ≠ v → G.Adj v u) : G.domNum = 1 := by
  have hdom : G.IsDominatingSet {v} := by
    intro u
    by_cases huv : u = v
    · exact Or.inl (by simp [huv])
    · exact Or.inr ⟨v, by simp, h u huv⟩
  have h1 := domNum_le_card_of_isDominatingSet hdom
  rw [Finset.card_singleton] at h1
  have h2 : 0 < Fintype.card G.V := Fintype.card_pos_iff.2 ⟨v⟩
  have := G.domNum_pos h2
  omega

/-- **The degree bound** `|V| ≤ γ·(Δ + 1)`: each vertex of a dominating set covers itself and at
most `Δ` neighbours. -/
theorem card_le_domNum_mul_maxDeg_add_one (G : CGraph) :
    Fintype.card G.V ≤ G.domNum * (G.maxDeg + 1) := by
  classical
  obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
  have hsub : (Finset.univ : Finset G.V)
      ⊆ s.biUnion fun u ↦ insert u (G.toSimple.neighborFinset u) := by
    intro v _
    rcases hs v with hv | ⟨u, hu, hadj⟩
    · exact Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_insert_self _ _⟩
    · refine Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_insert_of_mem ?_⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact (toSimple_adj _ _ _).2 hadj
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := s)
    (t := fun u ↦ insert u (G.toSimple.neighborFinset u))
  have h3 : ∀ u ∈ s, (insert u (G.toSimple.neighborFinset u)).card ≤ G.maxDeg + 1 := by
    intro u _
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := G.degree_le_maxDeg u
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have h4 := Finset.sum_le_card_nsmul _ _ _ h3
  rw [Finset.card_univ] at h1
  rw [smul_eq_mul, hcard] at h4
  omega

/-- **`γ ≤ α`**: a *maximum* independent set is dominating, since a vertex it failed to dominate
could be added to it. -/
theorem domNum_le_indepNum (G : CGraph) : G.domNum ≤ G.indepNum := by
  classical
  obtain ⟨S, hS, hScard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hdom : G.IsDominatingSet S := by
    intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨hv, hne⟩ := hcon
    have hnadj : ∀ u ∈ S, ¬ G.toSimple.Adj u v := by
      intro u hu hadj
      exact hne u hu ((toSimple_adj _ _ _).1 hadj)
    have hins : G.toSimple.IsIndepSet (insert v (S : Set G.V)) := by
      refine (Set.pairwise_insert_of_symmetric ?_).2 ⟨hS, ?_⟩
      · intro a b hab h
        exact hab h.symm
      · intro b hb _
        exact fun h ↦ hnadj b hb h.symm
    rw [← Finset.coe_insert] at hins
    have hcard := hins.card_le_indepNum
    rw [Finset.card_insert_of_notMem hv, hScard] at hcard
    omega
  have h := domNum_le_card_of_isDominatingSet hdom
  rw [hScard] at h
  exact h

/-- **`γ + Δ ≤ |V|`**: the complement of the neighbourhood of a vertex of maximum degree is
dominating. -/
theorem domNum_add_maxDeg_le_card (G : CGraph) : G.domNum + G.maxDeg ≤ Fintype.card G.V := by
  classical
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : Fintype.card G.V = 0 := Fintype.card_eq_zero
    have h2 := G.domNum_le_card
    have h3 : G.maxDeg = 0 := by rw [maxDeg, SimpleGraph.maxDegree_of_isEmpty]
    omega
  obtain ⟨v₀⟩ := hne
  obtain ⟨v, hv⟩ := G.exists_degree_eq_maxDeg v₀
  set T : Finset G.V := Finset.univ \ G.toSimple.neighborFinset v with hT
  have hdom : G.IsDominatingSet T := by
    intro u
    by_cases hu : u ∈ T
    · exact Or.inl hu
    · refine Or.inr ⟨v, ?_, ?_⟩
      · rw [hT, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, by simp⟩
      · rw [hT, Finset.mem_sdiff] at hu
        push_neg at hu
        have := hu (Finset.mem_univ u)
        rw [SimpleGraph.mem_neighborFinset] at this
        exact (toSimple_adj _ _ _).2 (by simpa using this)
  have hcardT : T.card = Fintype.card G.V - G.maxDeg := by
    rw [hT, Finset.card_univ_diff, SimpleGraph.card_neighborFinset_eq_degree, hv]
  have h1 := domNum_le_card_of_isDominatingSet hdom
  have h2 : G.maxDeg < Fintype.card G.V := G.maxDeg_lt_card v₀
  omega

/-- **`γ ≤ τ`** for a graph with no isolated vertex: a vertex cover dominates, since every vertex
has an edge and the far end of it is in the cover. -/
theorem domNum_le_coverNum (G : CGraph) (h : 1 ≤ G.minDeg) : G.domNum ≤ G.coverNum := by
  classical
  obtain ⟨C, hC, hCcard⟩ := exists_cover_finset G.toSimple
  have hdom : G.IsDominatingSet C := by
    intro v
    by_cases hv : v ∈ C
    · exact Or.inl hv
    · have hdeg : 1 ≤ G.toSimple.degree v := le_trans h (G.minDeg_le_degree v)
      have hne : (G.toSimple.neighborFinset v).Nonempty := by
        rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨u, hu⟩ := hne
      rw [SimpleGraph.mem_neighborFinset] at hu
      rcases hC hu with hmem | hmem
      · exact absurd hmem hv
      · exact Or.inr ⟨u, hmem, (toSimple_adj _ _ _).2 hu.symm⟩
  have := domNum_le_card_of_isDominatingSet hdom
  rw [hCcard] at this
  exact this

/-! ### The domination number of the small families -/

theorem domNum_empty (n : ℕ) : (empty n).domNum = n := by
  refine le_antisymm ?_ ?_
  · have := (empty n).domNum_le_card
    rwa [card_empty] at this
  · obtain ⟨s, hcard, hs⟩ := (empty n).exists_isDominatingSet_domNum
    have huniv : s = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 fun v ↦ ?_
      rcases hs v with hv | ⟨u, -, hadj⟩
      · exact hv
      · simp at hadj
    rw [huniv, Finset.card_univ, card_empty] at hcard
    omega

theorem domNum_complete (n : ℕ) : (complete (n + 1)).domNum = 1 :=
  domNum_eq_one_of_universal (v := (0 : Fin (n + 1))) fun u hu ↦ by
    simpa using Ne.symm hu

theorem domNum_star (n : ℕ) : (star n).domNum = 1 := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  refine domNum_eq_one_of_universal (v := (Sum.inl 0 : Fin 1 ⊕ Fin n)) fun u hu ↦ ?_
  match u with
  | Sum.inl a => exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  | Sum.inr b => exact bipartite_adj_inl_inr 1 n 0 b

/-! ### The radius -/

/-- The most central vertex is no further from the rest than the least central one. -/
theorem radius_le_diameter (G : CGraph) : G.radius ≤ G.diameter := by
  by_cases hc : G.toSimple.Connected
  · haveI : Nonempty G.V := hc.nonempty
    have hd : G.toSimple.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hc
    exact ENat.toNat_le_toNat SimpleGraph.radius_le_ediam hd
  · have h : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_not_connected hc
    simp [radius, h]

/-- Walking through a central vertex crosses the graph in at most `2r` steps. -/
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

theorem radius_pos (G : CGraph) (hc : G.IsConnected) (hV : 1 < Fintype.card G.V) :
    0 < G.radius := by
  haveI : Nonempty G.V := hc.nonempty
  haveI : Nontrivial G.V := Fintype.one_lt_card_iff_nontrivial.1 hV
  have h0 : G.toSimple.radius ≠ 0 := SimpleGraph.radius_ne_zero_of_nontrivial
  have ht : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hc
  have : G.radius ≠ 0 := by
    simp only [radius, ne_eq, ENat.toNat_eq_zero]
    tauto
  omega

/-- A vertex adjacent to everything else is at distance one from the rest, so it makes the
radius `1` — provided there is something else. -/
theorem radius_eq_one_of_universal {v : G.V} (h : ∀ u, u ≠ v → G.Adj v u)
    (hV : 1 < Fintype.card G.V) : G.radius = 1 := by
  haveI : Nontrivial G.V := Fintype.one_lt_card_iff_nontrivial.1 hV
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

/-- A graph is dominated by a single vertex exactly when it has a universal vertex. -/
theorem domNum_eq_one_iff (G : CGraph) :
    G.domNum = 1 ↔ ∃ v : G.V, ∀ u, u ≠ v → G.Adj v u := by
  constructor
  · intro h
    obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
    rw [h, Finset.card_eq_one] at hcard
    obtain ⟨v, rfl⟩ := hcard
    refine ⟨v, fun u hu ↦ ?_⟩
    rcases hs u with hmem | ⟨w, hw, hadj⟩
    · exact absurd (Finset.mem_singleton.1 hmem) hu
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact hadj
  · rintro ⟨v, hv⟩
    exact domNum_eq_one_of_universal hv

/-- The apex of a join with a single vertex sees the whole graph, so it dominates it. -/
theorem domNum_join_complete_one (G : CGraph) [DecidableEq G.V] :
    (join (complete 1) G).domNum = 1 := by
  haveI : Subsingleton (complete 1).V := inferInstanceAs (Subsingleton (Fin 1))
  haveI : Subsingleton (compl (complete 1)).V := inferInstanceAs (Subsingleton (Fin 1))
  refine domNum_eq_one_of_universal
    (v := (Sum.inl (0 : Fin 1) : (join (complete 1) G).V)) fun u hu ↦ ?_
  rcases u with a | b
  · exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  · exact join_adj_inl_inr (complete 1) G _ b

theorem domNum_wheel (n : ℕ) : (wheel n).domNum = 1 := domNum_join_complete_one (cycle n)

/-- **Radius one and domination number one are the same condition** on a graph with at least two
vertices: both say that some vertex sees the whole graph. -/
theorem radius_eq_one_iff_domNum_eq_one (G : CGraph) (hV : 1 < Fintype.card G.V) :
    G.radius = 1 ↔ G.domNum = 1 := by
  rw [domNum_eq_one_iff]
  exact ⟨G.exists_universal_of_radius_eq_one, fun ⟨_, hv⟩ ↦ radius_eq_one_of_universal hv hV⟩

/-- **A vertex-transitive graph has radius equal to its diameter**: every vertex is as central as
every other, so the least and the greatest eccentricity agree. -/
theorem radius_eq_diameter_of_isVertexTransitive (G : CGraph) (h : G.IsVertexTransitive) :
    G.radius = G.diameter := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : G.toSimple.radius = ⊤ := SimpleGraph.radius_eq_top_of_isEmpty
    have h2 : G.toSimple.diam = 0 := by
      rw [SimpleGraph.diam_eq_zero]
      exact Or.inr (by infer_instance)
    simp [radius, diameter, h1, h2]
  · have key : G.toSimple.radius = G.toSimple.ediam := by
      rw [SimpleGraph.radius_eq_ediam_iff]
      refine ⟨G.toSimple.eccent Classical.ofNonempty, fun u ↦ ?_⟩
      obtain ⟨σ, hσ⟩ := h Classical.ofNonempty u
      rw [← hσ]
      exact (SimpleGraph.Iso.eccent_eq (CGraph.Iso.toSimpleIso σ) _).symm
    simp [radius, diameter, SimpleGraph.diam, key]

/-! ### Counting cliques

`cliqueCount n` counts the `n`-element cliques.  The first three values are forced — there is
one empty clique, `|V|` singletons and one clique per edge — and after that the count is tied to
the clique number: it vanishes exactly when `n` exceeds `ω(G)`. -/

@[simp] theorem cliqueCount_zero (G : CGraph) : G.cliqueCount 0 = 1 := by
  have h : G.toSimple.cliqueSet 0 = {∅} := by
    ext s
    simp
  rw [cliqueCount, h, Set.ncard_singleton]

@[simp] theorem cliqueCount_one (G : CGraph) : G.cliqueCount 1 = Fintype.card G.V := by
  have h : G.toSimple.cliqueSet 1 = (fun a : G.V ↦ ({a} : Finset G.V)) '' Set.univ := by
    ext s
    simp [eq_comm]
  rw [cliqueCount, h, Set.ncard_image_of_injective _ Finset.singleton_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The `2`-cliques are exactly the edges. -/
@[simp] theorem cliqueCount_two (G : CGraph) [DecidableEq G.V] : G.cliqueCount 2 = G.E := by
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

theorem cliqueCount_eq_zero_iff (G : CGraph) (n : ℕ) : G.cliqueCount n = 0 ↔ G.cliqueNum < n := by
  rw [cliqueCount, Set.ncard_eq_zero (Set.toFinite _), SimpleGraph.cliqueSet_eq_empty_iff,
    cliqueFree_iff_cliqueNum_lt]
  rfl

theorem cliqueCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.cliqueCount n ↔ n ≤ G.cliqueNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, cliqueCount_eq_zero_iff]
  omega

theorem cliqueCount_eq_zero_of_cliqueNum_lt {G : CGraph} {n : ℕ} (h : G.cliqueNum < n) :
    G.cliqueCount n = 0 :=
  (cliqueCount_eq_zero_iff G n).2 h

theorem cliqueCount_le_choose (G : CGraph) (n : ℕ) :
    G.cliqueCount n ≤ (Fintype.card G.V).choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  exact SimpleGraph.card_cliqueFinset_le

theorem cliqueCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : Fintype.card G.V < n) :
    G.cliqueCount n = 0 :=
  Nat.le_zero.1 ((cliqueCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- A graph has a triangle exactly when its girth is three, so the triangle count vanishes
exactly when the girth is anything else. -/
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
theorem cliqueCount_three_eq_zero_of_isBipartite {G : CGraph} (h : G.IsBipartite) :
    G.cliqueCount 3 = 0 :=
  cliqueCount_eq_zero_of_chromNum_lt
    (lt_of_le_of_lt (isBipartite_iff_chromNum_le_two.1 h) (by omega))

/-- Every subset of the complete graph is a clique, so the count is a binomial coefficient. -/
@[simp] theorem cliqueCount_complete (m n : ℕ) : (complete m).cliqueCount n = m.choose n := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset]
  have h : (complete m).toSimple.cliqueFinset n = Finset.univ.powersetCard n := by
    ext s
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, Finset.mem_powersetCard,
      complete_toSimple]
    simp [SimpleGraph.IsClique, Set.Pairwise]
  rw [h, Finset.card_powersetCard, Finset.card_univ, card_complete]

@[simp] theorem cliqueCount_empty (m n : ℕ) : (empty m).cliqueCount (n + 2) = 0 := by
  refine cliqueCount_eq_zero_of_cliqueNum_lt ?_
  rw [cliqueNum_empty]
  omega

/-! ### Counting independent sets

Independent sets are cliques of the complement, so the whole clique-count API transfers: each
fact below is its clique-count counterpart read through `compl`. -/

@[simp] theorem cliqueCount_compl (G : CGraph) [DecidableEq G.V] (n : ℕ) :
    (compl G).cliqueCount n = G.indepCount n := by
  rw [cliqueCount, indepCount]
  congr 1
  ext s
  simp [compl_toSimple]

@[simp] theorem indepCount_compl (G : CGraph) [DecidableEq G.V] (n : ℕ) :
    (compl G).indepCount n = G.cliqueCount n := by
  rw [← cliqueCount_compl (compl G), compl_compl]

@[simp] theorem indepCount_zero (G : CGraph) : G.indepCount 0 = 1 := by
  classical
  rw [← cliqueCount_compl]
  exact cliqueCount_zero _

@[simp] theorem indepCount_one (G : CGraph) : G.indepCount 1 = Fintype.card G.V := by
  classical
  rw [← cliqueCount_compl, cliqueCount_one, card_compl]

theorem indepCount_eq_zero_iff (G : CGraph) (n : ℕ) :
    G.indepCount n = 0 ↔ G.indepNum < n := by
  classical
  rw [← cliqueCount_compl, cliqueCount_eq_zero_iff, cliqueNum_compl]

theorem indepCount_pos_iff (G : CGraph) (n : ℕ) : 0 < G.indepCount n ↔ n ≤ G.indepNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, indepCount_eq_zero_iff]
  omega

theorem indepCount_eq_zero_of_indepNum_lt {G : CGraph} {n : ℕ} (h : G.indepNum < n) :
    G.indepCount n = 0 :=
  (indepCount_eq_zero_iff G n).2 h

theorem indepCount_le_choose (G : CGraph) (n : ℕ) :
    G.indepCount n ≤ (Fintype.card G.V).choose n := by
  classical
  rw [← cliqueCount_compl]
  have h := cliqueCount_le_choose (compl G) n
  rwa [card_compl] at h

theorem indepCount_eq_zero_of_card_lt {G : CGraph} {n : ℕ} (h : Fintype.card G.V < n) :
    G.indepCount n = 0 :=
  Nat.le_zero.1 ((indepCount_le_choose G n).trans (Nat.choose_eq_zero_of_lt h).le)

/-- The independent pairs are exactly the non-edges. -/
theorem indepCount_two_add_E (G : CGraph) [DecidableEq G.V] :
    G.indepCount 2 + G.E = (Fintype.card G.V).choose 2 := by
  rw [← cliqueCount_compl, cliqueCount_two]
  exact E_compl G

/-- Every set of vertices of the empty graph is independent. -/
@[simp] theorem indepCount_empty (m n : ℕ) : (empty m).indepCount n = m.choose n := by
  rw [← cliqueCount_compl]
  exact cliqueCount_complete m n

@[simp] theorem indepCount_complete (m n : ℕ) : (complete m).indepCount (n + 2) = 0 := by
  rw [← cliqueCount_compl, show compl (complete m) = empty m from compl_compl (empty m)]
  exact cliqueCount_empty m n

/-! ### Counting cliques in a disjoint union -/

/-- A clique of a disjoint union that has at least one vertex lies wholly on one of the two
sides, because no edge crosses between them. -/
theorem isNClique_disjUnion_iff {n : ℕ} {s : Finset (disjUnion G H).V} :
    (disjUnion G H).toSimple.IsNClique (n + 1) s ↔
      (∃ t : Finset G.V, G.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inl, Sum.inl_injective⟩) ∨
      (∃ t : Finset H.V, H.toSimple.IsNClique (n + 1) t ∧
          s = t.map ⟨Sum.inr, Sum.inr_injective⟩) := by
  constructor
  · rintro ⟨hcl, hcard⟩
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    match x, hx with
    | .inl a, ha =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) := by
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
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hb))
      have hc' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hc))
      have := hcl hb' hc' (Sum.inl_injective.ne hbc)
      simpa [CGraph.toSimple_adj] using this
    | .inr b, hb =>
      have hsub : s ⊆ Finset.univ.map
          (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) := by
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
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hc))
      have hd' := Finset.mem_coe.2 (Finset.mem_map_of_mem
        (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ (disjUnion G H).V) (Finset.mem_coe.1 hd))
      have := hcl hc' hd' (Sum.inr_injective.ne hcd)
      simpa [CGraph.toSimple_adj] using this
  · rintro (⟨t, ⟨hcl, hcard⟩, rfl⟩ | ⟨t, ⟨hcl, hcard⟩, rfl⟩)
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      simpa [CGraph.toSimple_adj] using hcl ha hb this
    · refine ⟨?_, by simpa using hcard⟩
      rintro _ hx _ hy hxy
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have : a ≠ b := fun h ↦ hxy (by rw [h])
      simpa [CGraph.toSimple_adj] using hcl ha hb this

/-- Cliques never cross between the two sides, so from size one on the counts simply add. -/
theorem cliqueCount_disjUnion (G H : CGraph) (n : ℕ) :
    (disjUnion G H).cliqueCount (n + 1) = G.cliqueCount (n + 1) + H.cliqueCount (n + 1) := by
  classical
  rw [cliqueCount_eq_card_cliqueFinset, cliqueCount_eq_card_cliqueFinset,
    cliqueCount_eq_card_cliqueFinset]
  set fl : Finset G.V ↪ Finset (disjUnion G H).V :=
    ⟨Finset.map ⟨Sum.inl, Sum.inl_injective⟩, Finset.map_injective _⟩ with hfl
  set fr : Finset H.V ↪ Finset (disjUnion G H).V :=
    ⟨Finset.map ⟨Sum.inr, Sum.inr_injective⟩, Finset.map_injective _⟩ with hfr
  have hset : (disjUnion G H).toSimple.cliqueFinset (n + 1)
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
    have : (Sum.inl a : (disjUnion G H).V) ∈ u.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      rw [hu]; simpa using ha
    simp at this
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

/-- Dually, independent sets never cross a join. -/
theorem indepCount_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (n : ℕ) :
    (join G H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  classical
  rw [join, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl, cliqueCount_compl]

/-- An independent set of `K_{m,n}` is a set of vertices on one side. -/
@[simp] theorem indepCount_bipartite (m n k : ℕ) :
    (bipartite m n).indepCount (k + 1) = m.choose (k + 1) + n.choose (k + 1) := by
  classical
  rw [bipartite, indepCount_compl, cliqueCount_disjUnion, cliqueCount_complete,
    cliqueCount_complete]

/-! ### Counting connected components -/

theorem numComponents_eq_zero_iff (G : CGraph) :
    G.numComponents = 0 ↔ Fintype.card G.V = 0 := by
  rw [numComponents, Nat.card_eq_zero, Fintype.card_eq_zero_iff]
  simp only [or_iff_left (not_infinite_iff_finite.2 inferInstance)]
  exact ⟨fun h ↦ ⟨fun v ↦ h.false (G.toSimple.connectedComponentMk v)⟩, fun _ ↦ inferInstance⟩

theorem numComponents_pos_iff (G : CGraph) : 0 < G.numComponents ↔ 0 < Fintype.card G.V := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, ne_eq, ne_eq, numComponents_eq_zero_iff]

/-- A graph is connected exactly when it has one component. -/
theorem numComponents_eq_one_iff (G : CGraph) : G.numComponents = 1 ↔ G.IsConnected := by
  rw [numComponents, Nat.card_eq_one_iff_unique, IsConnected, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hsub, hne⟩
    refine ⟨fun u v ↦ SimpleGraph.ConnectedComponent.exact (hsub.elim _ _), ?_⟩
    obtain ⟨c⟩ := hne
    exact SimpleGraph.ConnectedComponent.ind (β := fun _ ↦ Nonempty G.V) (fun v ↦ ⟨v⟩) c
  · rintro ⟨hpre, hne⟩
    exact ⟨hpre.subsingleton_connectedComponent, inferInstance⟩

/-- Each component contains at least one vertex. -/
theorem numComponents_le_card (G : CGraph) : G.numComponents ≤ Fintype.card G.V := by
  rw [numComponents, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ (Quot.mk_surjective)

@[simp] theorem numComponents_empty (n : ℕ) : (empty n).numComponents = n := by
  rw [numComponents, empty_toSimple]
  have : Function.Bijective ((⊥ : SimpleGraph (Fin n)).connectedComponentMk) := by
    refine ⟨fun u v h ↦ ?_, Quot.mk_surjective⟩
    exact SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.exact h)
  rw [← Nat.card_eq_of_bijective _ this, Nat.card_eq_fintype_card, Fintype.card_fin]

@[simp] theorem numComponents_complete (n : ℕ) : (complete (n + 1)).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_complete n)

/-! ### The components of a disjoint union -/

/-- The inclusion of the left factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInl (G H : CGraph) : G.toSimple →g (disjUnion G H).toSimple where
  toFun := Sum.inl
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- The inclusion of the right factor of a disjoint union, as a graph homomorphism. -/
def disjUnionInr (G H : CGraph) : H.toSimple →g (disjUnion G H).toSimple where
  toFun := Sum.inr
  map_rel' {a b} h := by simpa [CGraph.toSimple_adj] using h

/-- Send a vertex of a disjoint union to its component on whichever side it lives. -/
private def duSplit (G H : CGraph) :
    (disjUnion G H).V → G.toSimple.ConnectedComponent ⊕ H.toSimple.ConnectedComponent :=
  Sum.map G.toSimple.connectedComponentMk H.toSimple.connectedComponentMk

private theorem duSplit_eq_of_adj {u v : (disjUnion G H).V}
    (h : (disjUnion G H).toSimple.Adj u v) : duSplit G H u = duSplit G H v := by
  match u, v with
  | Sum.inl a, Sum.inl c =>
    have : G.toSimple.Adj a c := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]
  | Sum.inl a, Sum.inr d => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inl b => exact absurd h (by simp [CGraph.toSimple_adj])
  | Sum.inr c, Sum.inr d =>
    have : H.toSimple.Adj c d := by simpa [CGraph.toSimple_adj] using h
    simp [duSplit, SimpleGraph.ConnectedComponent.eq, this.reachable]

private theorem duSplit_eq_of_reachable {u v : (disjUnion G H).V}
    (h : (disjUnion G H).toSimple.Reachable u v) : duSplit G H u = duSplit G H v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (duSplit_eq_of_adj hadj).trans ih

/-- **The components of a disjoint union are those of the two factors.** -/
def disjUnionComponentEquiv (G H : CGraph) :
    (disjUnion G H).toSimple.ConnectedComponent ≃
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

@[simp] theorem numComponents_disjUnion (G H : CGraph) :
    (disjUnion G H).numComponents = G.numComponents + H.numComponents := by
  rw [numComponents, numComponents, numComponents,
    Nat.card_congr (disjUnionComponentEquiv G H), Nat.card_sum]

/-- **At most one of a graph and its complement is disconnected.** -/
theorem numComponents_compl_eq_one (G : CGraph) [DecidableEq G.V] (h : 2 ≤ G.numComponents) :
    (compl G).numComponents = 1 := by
  have hne : Nonempty G.V := Fintype.card_pos_iff.1
    ((numComponents_pos_iff G).1 (by omega))
  rw [numComponents_eq_one_iff]
  refine G.isConnected_compl_of_not_preconnected (fun hpre ↦ ?_)
  have : Subsingleton G.toSimple.ConnectedComponent := hpre.subsingleton_connectedComponent
  have : G.numComponents = 1 := by
    rw [numComponents]
    exact Nat.card_eq_one_iff_unique.2 ⟨this, inferInstance⟩
  omega

/-! ### Components versus the other invariants -/

theorem surjective_connectedComponentMk (G : CGraph) :
    Function.Surjective G.toSimple.connectedComponentMk :=
  fun c ↦ Quot.exists_rep c

/-- One vertex from each component is an independent set, so there are at most `α(G)` components. -/
theorem numComponents_le_indepNum (G : CGraph) : G.numComponents ≤ G.indepNum := by
  classical
  choose f hout using G.surjective_connectedComponentMk
  have hinj : Function.Injective f := fun c d h ↦ by rw [← hout c, ← hout d, h]
  set s : Finset G.V := Finset.univ.image f with hs
  have hcard : s.card = G.numComponents := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  have hindep : G.toSimple.IsIndepSet s := by
    intro x hx y hy hxy hadj
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    refine hxy ?_
    have : c = d := by
      rw [← hout c, ← hout d]
      exact SimpleGraph.ConnectedComponent.sound hadj.reachable
    rw [this]
  calc G.numComponents = s.card := hcard.symm
    _ ≤ G.indepNum := hindep.card_le_indepNum

/-- A dominating set must meet every component, so there are at most `γ(G)` components. -/
theorem numComponents_le_domNum (G : CGraph) : G.numComponents ≤ G.domNum := by
  classical
  obtain ⟨s, hcard, hs⟩ := G.exists_isDominatingSet_domNum
  have hsurj : Function.Surjective
      (fun v : {x : G.V // x ∈ s} ↦ G.toSimple.connectedComponentMk v.1) := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      rcases hs v with hv | ⟨u, hu, hadj⟩
      · exact ⟨⟨v, hv⟩, rfl⟩
      · exact ⟨⟨u, hu⟩, SimpleGraph.ConnectedComponent.sound
          (SimpleGraph.Adj.reachable (G.toSimple_adj u v |>.2 hadj))⟩
  rw [numComponents]
  calc Nat.card G.toSimple.ConnectedComponent
      ≤ Nat.card {x : G.V // x ∈ s} := Nat.card_le_card_of_surjective _ hsurj
    _ = s.card := Nat.card_eq_finsetCard s
    _ = G.domNum := hcard

/-- The join of two nonempty graphs is connected, hence has one component. -/
theorem numComponents_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) :
    (join G H).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_join G H hG hH)

theorem E_pos_of_adj {G : CGraph} {a b : G.V} (h : G.toSimple.Adj a b) : 0 < G.E :=
  Finset.card_pos.2 ⟨s(a, b), SimpleGraph.mem_edgeFinset.2 h⟩

/-- A graph has as many components as vertices exactly when it has no edges. -/
theorem numComponents_eq_card_iff (G : CGraph) :
    G.numComponents = Fintype.card G.V ↔ G.E = 0 := by
  classical
  constructor
  · intro h
    by_contra hE
    obtain ⟨a, b, hab⟩ := exists_adj_of_E_pos (Nat.pos_of_ne_zero hE)
    have hadj : G.toSimple.Adj a b := hab
    have hnotinj : ¬ Function.Injective G.toSimple.connectedComponentMk := fun hinj ↦
      hadj.ne (hinj (SimpleGraph.ConnectedComponent.sound hadj.reachable))
    have hlt := Fintype.card_lt_of_surjective_not_injective _ G.surjective_connectedComponentMk
      hnotinj
    rw [Fintype.card_eq_nat_card] at hlt
    rw [numComponents] at h
    omega
  · intro h
    have hbot : G.toSimple = ⊥ := by
      ext a b
      simp only [SimpleGraph.bot_adj, iff_false]
      intro hadj
      have := E_pos_of_adj hadj
      omega
    have hinj : Function.Injective G.toSimple.connectedComponentMk := by
      intro u v huv
      have hr : G.toSimple.Reachable u v := SimpleGraph.ConnectedComponent.exact huv
      rw [hbot] at hr
      exact SimpleGraph.reachable_bot.1 hr
    rw [numComponents,
      ← Nat.card_eq_of_bijective _ ⟨hinj, G.surjective_connectedComponentMk⟩,
      Nat.card_eq_fintype_card]

theorem numComponents_lt_card_of_E_pos (G : CGraph) (h : 0 < G.E) :
    G.numComponents < Fintype.card G.V := by
  have hle := G.numComponents_le_card
  have := (G.numComponents_eq_card_iff).not.2 (by omega : ¬ G.E = 0)
  omega

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
theorem numComponents_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).numComponents = G.numComponents * H.numComponents := by
  rw [numComponents, numComponents, numComponents, toSimple_cartesianProduct]
  exact card_connectedComponent_boxProd _ _

/-! ### A minimum-degree condition for connectedness -/

/-- **A graph with `2δ(G) + 1 ≥ |V|` is connected**: two nonadjacent vertices have too many
neighbours between them to avoid sharing one. -/
theorem isConnected_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : Fintype.card G.V ≤ 2 * G.minDeg + 1) : G.IsConnected := by
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
  have hTcard : T.card = Fintype.card G.V - 2 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨fun h' ↦ huv h'.symm, Finset.mem_univ v⟩),
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    omega
  have hdu : G.minDeg ≤ (G.toSimple.neighborFinset u).card := G.minDeg_le_degree u
  have hdv : G.minDeg ≤ (G.toSimple.neighborFinset v).card := G.minDeg_le_degree v
  have hunion : (G.toSimple.neighborFinset u ∪ G.toSimple.neighborFinset v).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset hu hv)
  have hinter := Finset.card_union_add_card_inter
    (G.toSimple.neighborFinset u) (G.toSimple.neighborFinset v)
  have hcard2 : 2 ≤ Fintype.card G.V := by
    have hle : ({u, v} : Finset G.V).card ≤ Fintype.card G.V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rwa [Finset.card_pair huv] at hle
  have hpos : 0 < (G.toSimple.neighborFinset u ∩ G.toSimple.neighborFinset v).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
  exact hw.1.reachable.trans hw.2.reachable.symm

theorem numComponents_eq_one_of_card_le_two_mul_minDeg (G : CGraph) [Nonempty G.V]
    (h : Fintype.card G.V ≤ 2 * G.minDeg + 1) : G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 (G.isConnected_of_card_le_two_mul_minDeg h)

/-! ### Counting automorphisms -/

/-- Every permutation is an automorphism of the edgeless graph. -/
def _root_.SimpleGraph.autBotEquiv (α : Type*) :
    ((⊥ : SimpleGraph α) ≃g (⊥ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Every permutation is an automorphism of the complete graph. -/
def _root_.SimpleGraph.autTopEquiv (α : Type*) :
    ((⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp [e.injective.ne_iff]⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Complementation does not change the automorphism group. -/
def _root_.SimpleGraph.autComplEquiv {α : Type*} (S : SimpleGraph α) : (S ≃g S) ≃ (Sᶜ ≃g Sᶜ) where
  toFun a := ⟨a.toEquiv, by
    intro x y
    simp only [SimpleGraph.compl_adj, ne_eq, a.toEquiv.injective.ne_iff]
    exact and_congr_right fun _ ↦ not_congr a.map_rel_iff⟩
  invFun b := ⟨b.toEquiv, by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · have hne : ¬ (b x = b y) := fun hh ↦ hxy (b.toEquiv.injective hh)
      have h := b.map_rel_iff (a := x) (b := y)
      rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h
      constructor
      · intro hadj
        by_contra hc
        exact (h.2 ⟨hxy, hc⟩).2 hadj
      · intro hadj
        by_contra hc
        exact (h.1 ⟨hne, hc⟩).2 hadj⟩
  left_inv a := by ext v; rfl
  right_inv b := by ext v; rfl

theorem autCount_pos (G : CGraph) : 0 < G.autCount := Nat.card_pos

/-- An automorphism is in particular a permutation of the vertices. -/
theorem autCount_le_factorial (G : CGraph) : G.autCount ≤ Nat.factorial (Fintype.card G.V) := by
  classical
  calc G.autCount ≤ Nat.card (G.V ≃ G.V) :=
        Nat.card_le_card_of_injective (fun a : G.toSimple ≃g G.toSimple ↦ a.toEquiv)
          (fun _ _ h ↦ by ext v; exact congrArg (fun e : G.V ≃ G.V ↦ e v) h)
    _ = Nat.factorial (Fintype.card G.V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- **A graph and its complement have the same automorphisms.** -/
@[simp] theorem autCount_compl (G : CGraph) [DecidableEq G.V] :
    (compl G).autCount = G.autCount := by
  rw [autCount, autCount, compl_toSimple]
  exact (Nat.card_congr (SimpleGraph.autComplEquiv G.toSimple)).symm

@[simp] theorem autCount_empty (n : ℕ) : (empty n).autCount = Nat.factorial n := by
  classical
  rw [autCount, empty_toSimple, Nat.card_congr (SimpleGraph.autBotEquiv (Fin n)),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

@[simp] theorem autCount_complete (n : ℕ) : (complete n).autCount = Nat.factorial n := by
  classical
  rw [autCount, complete_toSimple, Nat.card_congr (SimpleGraph.autTopEquiv (Fin n)),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The automorphism count is `1` exactly for an asymmetric graph. -/
theorem autCount_eq_one_iff (G : CGraph) :
    G.autCount = 1 ↔ ∀ a : G.toSimple ≃g G.toSimple, a = RelIso.refl _ := by
  rw [autCount, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, -⟩ a
    exact hsub.elim a _
  · intro h
    exact ⟨⟨fun a b ↦ (h a).trans (h b).symm⟩, ⟨RelIso.refl _⟩⟩

/-! ### Automorphisms versus degrees and symmetry -/

/-- Automorphisms preserve degrees, so a graph whose vertices all have distinct degrees is
asymmetric. -/
theorem autCount_eq_one_of_degree_injective (G : CGraph)
    (h : Function.Injective fun v : G.V ↦ G.toSimple.degree v) : G.autCount = 1 := by
  rw [autCount_eq_one_iff]
  intro a
  ext v
  exact h (SimpleGraph.Iso.degree_eq a v)

/-- A vertex-transitive graph has at least `|V|` automorphisms: the automorphisms carrying a fixed
base vertex to each vertex in turn are already pairwise distinct. -/
theorem card_le_autCount_of_isVertexTransitive (G : CGraph) [Nonempty G.V]
    (h : G.IsVertexTransitive) : Fintype.card G.V ≤ G.autCount := by
  obtain ⟨v₀⟩ := ‹Nonempty G.V›
  choose f hf using h v₀
  haveI : Finite (G ≃cg G) := G.instFiniteAut
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (f u) v₀ = (f v) v₀ := by rw [huv]
    rw [hf u, hf v] at h1
    exact h1
  calc Fintype.card G.V = Nat.card G.V := Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (G ≃cg G) := Nat.card_le_card_of_injective f hinj
    _ = G.autCount := rfl

/-- An arc-transitive graph has at least `2|E|` automorphisms, one for each arc. -/
theorem two_mul_E_le_autCount_of_isArcTransitive (G : CGraph) (h : G.IsArcTransitive) :
    2 * G.E ≤ G.autCount := by
  classical
  rcases Nat.eq_zero_or_pos G.E with hE | hE
  · simp [hE]
  obtain ⟨u₀, v₀, h₀⟩ := exists_adj_of_E_pos hE
  haveI : Finite (G ≃cg G) := G.instFiniteAut
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

/-- Too few automorphisms to move a base vertex everywhere. -/
theorem not_isVertexTransitive_of_autCount_lt (G : CGraph) [Nonempty G.V]
    (h : G.autCount < Fintype.card G.V) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.card_le_autCount_of_isVertexTransitive hvt) (by omega)

/-- Too few automorphisms to move a base arc everywhere. -/
theorem not_isArcTransitive_of_autCount_lt (G : CGraph) (h : G.autCount < 2 * G.E) :
    ¬ G.IsArcTransitive := fun hat ↦
  absurd (G.two_mul_E_le_autCount_of_isArcTransitive hat) (by omega)

/-! ### The handshaking lemma -/

/-- **Handshaking lemma.**  A graph has evenly many vertices of odd degree. -/
theorem even_card_odd_degree (G : CGraph) :
    Even (Finset.univ.filter fun v : G.V ↦ Odd (G.toSimple.degree v)).card :=
  SimpleGraph.even_card_odd_degree_vertices G.toSimple

/-- The handshaking lemma, read off the degree multiset. -/
theorem even_countP_odd_degMultiset (G : CGraph) :
    Even (G.degMultiset.countP fun d ↦ Odd d) := by
  have h : (G.degMultiset.countP fun d ↦ Odd d)
      = (Finset.univ.filter fun v : G.V ↦ Odd (G.toSimple.degree v)).card := by
    rw [degMultiset, Multiset.countP_map]
    rfl
  rw [h]
  exact G.even_card_odd_degree

/-- The handshaking lemma, read off the degree sequence. -/
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
    Even (Fintype.card G.V) := by
  have hc := G.even_card_odd_degree
  rwa [Finset.filter_true_of_mem fun v _ ↦ h v, Finset.card_univ] at hc

/-- **An odd-regular graph has evenly many vertices.**  There is no cubic graph on five
vertices. -/
theorem even_card_of_isRegularOfDegree_odd (G : CGraph) {k : ℕ} (hk : Odd k)
    (h : G.toSimple.IsRegularOfDegree k) : Even (Fintype.card G.V) :=
  G.even_card_of_forall_odd_degree fun v ↦ by rw [h v]; exact hk

/-- On an odd number of vertices, some vertex has even degree. -/
theorem exists_even_degree_of_odd_card (G : CGraph) (h : Odd (Fintype.card G.V)) :
    ∃ v, Even (G.toSimple.degree v) := by
  by_contra hc
  push_neg at hc
  exact Nat.not_even_iff_odd.2 h
    (G.even_card_of_forall_odd_degree fun v ↦ Nat.not_even_iff_odd.1 (hc v))

/-! ### Automorphisms of the constructions

An automorphism of each factor gives an automorphism of a disjoint union, a join, or any of the
four products, and different pairs give different automorphisms.  So the automorphism count of a
construction is at least the product of the counts of its factors. -/

/-- The counting step shared by all the constructions below: an injective way of building an
automorphism of `K` out of one automorphism of `G` and one of `H`. -/
private theorem mul_autCount_le_autCount {K : CGraph}
    (f : (G ≃cg G) → (H ≃cg H) → (K ≃cg K))
    (hf : ∀ a a' b b', f a b = f a' b' → a = a' ∧ b = b') :
    G.autCount * H.autCount ≤ K.autCount := by
  haveI : Finite (K ≃cg K) := K.instFiniteAut
  have hinj : Function.Injective fun p : (G ≃cg G) × (H ≃cg H) ↦ f p.1 p.2 := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := hf a a' b b' h
    rw [h1, h2]
  calc G.autCount * H.autCount = Nat.card ((G ≃cg G) × (H ≃cg H)) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (K ≃cg K) := Nat.card_le_card_of_injective _ hinj
    _ = K.autCount := rfl

/-- An automorphism of each side, acting on the disjoint union. -/
def disjUnionAuto (a : G ≃cg G) (b : H ≃cg H) : disjUnion G H ≃cg disjUnion G H :=
  autoOfPerm (G := disjUnion G H) (Equiv.sumCongr a.toEquiv b.toEquiv) (by
    rintro (x | x) (y | y)
    · exact a.adj_eq x y
    · rfl
    · rfl
    · exact b.adj_eq x y)

@[simp] theorem disjUnionAuto_inl (a : G ≃cg G) (b : H ≃cg H) (x : G.V) :
    disjUnionAuto a b (.inl x) = .inl (a x) := rfl

@[simp] theorem disjUnionAuto_inr (a : G ≃cg G) (b : H ≃cg H) (y : H.V) :
    disjUnionAuto a b (.inr y) = .inr (b y) := rfl

theorem autCount_mul_le_autCount_disjUnion (G H : CGraph) :
    G.autCount * H.autCount ≤ (disjUnion G H).autCount :=
  mul_autCount_le_autCount disjUnionAuto fun a a' b b' h ↦ by
    refine ⟨?_, ?_⟩
    · ext x
      exact Sum.inl_injective
        (congrArg (fun σ : disjUnion G H ≃cg disjUnion G H ↦ σ (.inl x)) h)
    · ext y
      exact Sum.inr_injective
        (congrArg (fun σ : disjUnion G H ≃cg disjUnion G H ↦ σ (.inr y)) h)

theorem autCount_mul_le_autCount_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    G.autCount * H.autCount ≤ (join G H).autCount := by
  have h := autCount_mul_le_autCount_disjUnion (compl G) (compl H)
  rwa [autCount_compl, autCount_compl, ← autCount_compl (disjUnion (compl G) (compl H))] at h

/-- Swapping the two copies of a graph in a disjoint union with itself. -/
def disjUnionSwapAuto (G : CGraph) : disjUnion G G ≃cg disjUnion G G :=
  autoOfPerm (G := disjUnion G G) (Equiv.sumComm G.V G.V) (by
    rintro (x | x) (y | y) <;> rfl)

@[simp] theorem disjUnionSwapAuto_inl (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inl x) = .inr x := rfl

@[simp] theorem disjUnionSwapAuto_inr (G : CGraph) (x : G.V) :
    disjUnionSwapAuto G (.inr x) = .inl x := rfl

/-- Two copies of the same graph can also be exchanged, which doubles the bound. -/
theorem two_mul_autCount_mul_le_autCount_disjUnion_self (G : CGraph) [Nonempty G.V] :
    2 * (G.autCount * G.autCount) ≤ (disjUnion G G).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  haveI : Finite (disjUnion G G ≃cg disjUnion G G) := (disjUnion G G).instFiniteAut
  set f : Bool × (G ≃cg G) × (G ≃cg G) → (disjUnion G G ≃cg disjUnion G G) :=
    fun p ↦ if p.1 then (disjUnionAuto p.2.1 p.2.2).trans (disjUnionSwapAuto G)
      else disjUnionAuto p.2.1 p.2.2 with hfdef
  -- The two copies are told apart by which side `inl x₀` lands in, and each factor is read back
  -- off by forgetting the side.
  have hside : ∀ (c : Bool) (a b : G ≃cg G), (f (c, a, b) (Sum.inl x₀)).isRight = c := by
    rintro (_ | _) a b <;> simp [hfdef]
  have hfst : ∀ (c : Bool) (a b : G ≃cg G) (x : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inl x)) = a x := by
    rintro (_ | _) a b x <;> simp [hfdef]
  have hsnd : ∀ (c : Bool) (a b : G ≃cg G) (y : G.V),
      Sum.elim id id (f (c, a, b) (Sum.inr y)) = b y := by
    rintro (_ | _) a b y <;> simp [hfdef]
  have hinj : Function.Injective f := by
    rintro ⟨c, a, b⟩ ⟨c', a', b'⟩ h
    have hc : c = c' := by rw [← hside c a b, ← hside c' a' b', h]
    subst hc
    have ha : a = a' := by
      ext x
      rw [← hfst c a b x, ← hfst c a' b' x, h]
    have hb : b = b' := by
      ext y
      rw [← hsnd c a b y, ← hsnd c a' b' y, h]
    rw [ha, hb]
  calc 2 * (G.autCount * G.autCount) = Nat.card (Bool × (G ≃cg G) × (G ≃cg G)) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
        rfl
    _ ≤ Nat.card (disjUnion G G ≃cg disjUnion G G) := Nat.card_le_card_of_injective f hinj
    _ = (disjUnion G G).autCount := rfl

/-- An automorphism of each factor, acting coordinatewise on the Cartesian product. -/
def cartesianProductAuto [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G) (b : H ≃cg H) :
    cartesianProduct G H ≃cg cartesianProduct G H :=
  autoOfPerm (G := cartesianProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (cartesianProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [cartesianProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff]

@[simp] theorem cartesianProductAuto_apply [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : cartesianProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the tensor product. -/
def tensorProductAuto [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G) (b : H ≃cg H) :
    tensorProduct G H ≃cg tensorProduct G H :=
  autoOfPerm (G := tensorProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (tensorProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [tensorProduct_adj, a.adj_eq, b.adj_eq]

@[simp] theorem tensorProductAuto_apply [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : tensorProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the strong product. -/
def strongProductAuto [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G) (b : H ≃cg H) :
    strongProduct G H ≃cg strongProduct G H :=
  autoOfPerm (G := strongProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (strongProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [strongProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff, ne_eq, Prod.ext_iff]

@[simp] theorem strongProductAuto_apply [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : strongProductAuto a b x = (a x.1, b x.2) := rfl

/-- An automorphism of each factor, acting coordinatewise on the lexicographic product. -/
def lexProductAuto [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G) (b : H ≃cg H) :
    lexProduct G H ≃cg lexProduct G H :=
  autoOfPerm (G := lexProduct G H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (lexProduct G H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [lexProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff]

@[simp] theorem lexProductAuto_apply [DecidableEq G.V] [DecidableEq H.V] (a : G ≃cg G)
    (b : H ≃cg H) (x : G.V × H.V) : lexProductAuto a b x = (a x.1, b x.2) := rfl

theorem autCount_mul_le_autCount_cartesianProduct (G H : CGraph) [DecidableEq G.V]
    [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (cartesianProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount cartesianProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg
      (fun σ : cartesianProduct G H ≃cg cartesianProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg
      (fun σ : cartesianProduct G H ≃cg cartesianProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

theorem autCount_mul_le_autCount_tensorProduct (G H : CGraph) [DecidableEq G.V]
    [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (tensorProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount tensorProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : tensorProduct G H ≃cg tensorProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : tensorProduct G H ≃cg tensorProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

theorem autCount_mul_le_autCount_strongProduct (G H : CGraph) [DecidableEq G.V]
    [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (strongProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount strongProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : strongProduct G H ≃cg strongProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : strongProduct G H ≃cg strongProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

theorem autCount_mul_le_autCount_lexProduct (G H : CGraph) [DecidableEq G.V]
    [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    G.autCount * H.autCount ≤ (lexProduct G H).autCount := by
  obtain ⟨x₀⟩ := ‹Nonempty G.V›
  obtain ⟨y₀⟩ := ‹Nonempty H.V›
  refine mul_autCount_le_autCount lexProductAuto fun a a' b b' h ↦ ⟨?_, ?_⟩
  · ext x
    have := congrArg (fun σ : lexProduct G H ≃cg lexProduct G H ↦ (σ (x, y₀)).1) h
    simpa using this
  · ext y
    have := congrArg (fun σ : lexProduct G H ≃cg lexProduct G H ↦ (σ (x₀, y)).2) h
    simpa using this

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

/-- Choosing, in every component, one vertex to be the root, and sending every other vertex to the
edge joining it to a neighbour closer to that root, embeds `V` minus the roots into `E`:
`|V| ≤ |E| + c(G)`. -/
theorem card_le_E_add_numComponents (G : CGraph) :
    Fintype.card G.V ≤ G.E + G.numComponents := by
  classical
  rcases isEmpty_or_nonempty G.V with hV | hV
  · simp [Fintype.card_eq_zero]
  choose r hr using G.surjective_connectedComponentMk
  set root : G.V → G.V := fun v ↦ r (G.toSimple.connectedComponentMk v) with hroot
  have hreach : ∀ v, G.toSimple.Reachable v (root v) := by
    intro v
    apply SimpleGraph.ConnectedComponent.exact
    rw [hroot]
    exact (hr _).symm
  have hrootroot : ∀ c, root (r c) = r c := fun c ↦ by rw [hroot]; simp only [hr]
  -- the roots form a set of size `c(G)`
  have hinj : Function.Injective r := fun c d h ↦ by rw [← hr c, ← hr d, h]
  have himg : Finset.univ.filter (fun v ↦ v = root v) = Finset.univ.image r := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact fun h ↦ ⟨G.toSimple.connectedComponentMk v, h.symm⟩
    · rintro ⟨c, rfl⟩
      exact (hrootroot c).symm
  have hroots : (Finset.univ.filter (fun v ↦ v = root v)).card = G.numComponents := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, numComponents,
      Fintype.card_eq_nat_card]
  -- and every other vertex picks out an edge, injectively
  choose! u hu1 hu2 using fun v (hv : v ≠ root v) ↦ G.exists_adj_dist_lt (hreach v) hv
  have hne : ∀ {v w : G.V}, G.toSimple.Adj v w → root v = root w := fun {v w} h ↦ by
    rw [hroot]
    simp only
    rw [SimpleGraph.ConnectedComponent.sound h.reachable]
  have hmaps : ∀ v ∈ Finset.univ.filter (fun v ↦ ¬ v = root v),
      s(v, u v) ∈ G.toSimple.edgeFinset := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simpa using hu1 v hv
  have hinjOn : Set.InjOn (fun v ↦ s(v, u v))
      (Finset.univ.filter (fun v ↦ ¬ v = root v) : Finset G.V) := by
    intro v hv w hw h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have hrw : root v = root w := hne (h2 ▸ hu1 v hv)
      have d1 := hu2 v hv
      have d2 := hu2 w hw
      rw [← h1] at d2
      rw [h2, hrw] at d1
      omega
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G.V)) (p := fun v ↦ v = root v)
  have hle : (Finset.univ.filter (fun v ↦ ¬ v = root v)).card ≤ G.E :=
    Finset.card_le_card_of_injOn _ hmaps hinjOn
  rw [Finset.card_univ] at hcards
  omega

/-- A connected graph has at least `|V| - 1` edges. -/
theorem card_le_E_add_one_of_isConnected (G : CGraph) (h : G.IsConnected) :
    Fintype.card G.V ≤ G.E + 1 := by
  have := G.card_le_E_add_numComponents
  rw [(numComponents_eq_one_iff G).2 h] at this
  exact this

/-- Each edge can merge at most two components, so a graph with few edges has many components. -/
theorem card_sub_E_le_numComponents (G : CGraph) :
    Fintype.card G.V - G.E ≤ G.numComponents := by
  have := G.card_le_E_add_numComponents
  omega

/-- More components than vertices is impossible, so a graph with fewer components than vertices
has an edge. -/
theorem E_pos_of_numComponents_lt_card (G : CGraph) (h : G.numComponents < Fintype.card G.V) :
    0 < G.E := by
  have := G.card_le_E_add_numComponents
  omega

/-! ### The clique number of the Mycielskian -/

/-- The Mycielskian creates no new cliques: apart from the edges at the apex, every clique is a
clique of `G` in disguise. -/
theorem cliqueNum_mycielskian (G : CGraph) [DecidableEq G.V] [Nonempty G.V] :
    (mycielskian G).cliqueNum = max G.cliqueNum 2 := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty G.V›
  apply le_antisymm
  · obtain ⟨t, ht, hcard⟩ := (mycielskian G).toSimple.exists_isNClique_cliqueNum
    show (mycielskian G).toSimple.cliqueNum ≤ _
    rw [← hcard]
    by_cases hnone : (none : (mycielskian G).V) ∈ t
    · -- the apex is adjacent only to the copies, which are pairwise non-adjacent
      refine le_trans ?_ (le_max_right _ _)
      by_contra hc
      push_neg at hc
      have hcard' : 1 < (t.erase none).card := by
        rw [Finset.card_erase_of_mem hnone]
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard'
      have hinr : ∀ z ∈ t.erase none, ∃ b, z = some (.inr b) := by
        intro z hz
        have hzn : z ≠ none := Finset.ne_of_mem_erase hz
        have hadj := ht (by simpa using hnone) (by simpa using Finset.mem_of_mem_erase hz)
          (Ne.symm hzn)
        match z, hzn with
        | some (.inl b), _ => simp [CGraph.toSimple_adj] at hadj
        | some (.inr b), _ => exact ⟨b, rfl⟩
      obtain ⟨b, rfl⟩ := hinr x hx
      obtain ⟨c, rfl⟩ := hinr y hy
      have := ht (by simpa using Finset.mem_of_mem_erase hx)
        (by simpa using Finset.mem_of_mem_erase hy) hxy
      simp [CGraph.toSimple_adj] at this
    · -- no apex: forgetting which copy a vertex is in gives a clique of `G` of the same size
      refine le_trans ?_ (le_max_left _ _)
      set f : (mycielskian G).V → G.V := fun x ↦ x.elim a₀ (Sum.elim id id) with hf
      have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj (f x) (f y) = true := by
        intro x hx y hy hxy
        have h := ht (by simpa using hx) (by simpa using hy) hxy
        match x, (by rintro rfl; exact hnone hx : x ≠ none),
            y, (by rintro rfl; exact hnone hy : y ≠ none) with
        | some (.inl b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inl b), _, some (.inr c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inl c), _ => simpa [hf, CGraph.toSimple_adj] using h
        | some (.inr b), _, some (.inr c), _ => simp [CGraph.toSimple_adj] at h
      have hinj : Set.InjOn f t := by
        intro x hx y hy hfxy
        by_contra hxy
        have := hadj x hx y hy hxy
        rw [hfxy] at this
        exact absurd this (by simp [G.loopless])
      have hclique : G.toSimple.IsClique ((t.image f : Finset G.V) : Set G.V) := by
        intro u hu v hv huv
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        rw [CGraph.toSimple_adj]
        exact hadj x hx y hy fun h ↦ huv (by rw [h])
      calc t.card = (t.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ G.cliqueNum := hclique.card_le_cliqueNum
  · refine max_le ?_ ?_
    · -- `G` embeds as the `inl` copy
      obtain ⟨t, ht, hcard⟩ := G.toSimple.exists_isNClique_cliqueNum
      have hemb : Function.Injective (fun a : G.V ↦ (some (.inl a) : (mycielskian G).V)) := by
        intro a b h
        simpa using h
      have hclique : (mycielskian G).toSimple.IsClique
          ((t.map ⟨_, hemb⟩ : Finset (mycielskian G).V) : Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
          Function.Embedding.coeFn_mk] at hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨y, hy, rfl⟩ := hv
        have := ht hx hy fun h ↦ huv (by rw [h])
        rw [CGraph.toSimple_adj] at this ⊢
        simpa using this
      calc G.cliqueNum = (t.map ⟨_, hemb⟩).card := by
            rw [Finset.card_map]; exact hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum
    · -- the apex together with any copy is an edge
      have hclique : (mycielskian G).toSimple.IsClique
          (({none, some (.inr a₀)} : Finset (mycielskian G).V) :
            Set (mycielskian G).V) := by
        intro u hu v hv huv
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
          simp_all [CGraph.toSimple_adj]
      have hcard : ({none, some (.inr a₀)} : Finset (mycielskian G).V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      calc (2 : ℕ) = ({none, some (.inr a₀)} : Finset (mycielskian G).V).card := hcard.symm
        _ ≤ (mycielskian G).cliqueNum := hclique.card_le_cliqueNum

/-- Mycielski's construction preserves triangle-freeness. -/
theorem cliqueNum_mycielskian_eq_two (G : CGraph) [DecidableEq G.V] [Nonempty G.V]
    (h : G.cliqueNum ≤ 2) : (mycielskian G).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian]
  omega

/-! ### Edge counts of the strong and lexicographic products -/

private theorem sum_degree_add_one (K : CGraph) :
    ∑ v : K.V, (K.toSimple.degree v + 1) = 2 * K.E + Fintype.card K.V := by
  rw [Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]
  rfl

theorem E_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).E
      = Fintype.card G.V * H.E + Fintype.card H.V * G.E + 2 * G.E * H.E := by
  have hdeg : ∀ p : G.V × H.V, (strongProduct G H).toSimple.degree p + 1
      = (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) := by
    intro p
    have h := degree_strongProduct G H p
    have hpos : 1 ≤ (G.toSimple.degree p.1 + 1) * (H.toSimple.degree p.2 + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hdegsum : ∑ p : G.V × H.V, (strongProduct G H).toSimple.degree p
      = 2 * (strongProduct G H).E := SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hstrong : ∑ p : G.V × H.V, ((strongProduct G H).toSimple.degree p + 1)
      = 2 * (strongProduct G H).E + Fintype.card G.V * Fintype.card H.V := by
    rw [Finset.sum_add_distrib, hdegsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod]
  have key : 2 * (strongProduct G H).E + Fintype.card G.V * Fintype.card H.V
      = (2 * G.E + Fintype.card G.V) * (2 * H.E + Fintype.card H.V) := by
    rw [← hstrong, ← sum_degree_add_one G, ← sum_degree_add_one H, Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b)
  have expand : (2 * G.E + Fintype.card G.V) * (2 * H.E + Fintype.card H.V)
      = 2 * (Fintype.card G.V * H.E + Fintype.card H.V * G.E + 2 * G.E * H.E)
        + Fintype.card G.V * Fintype.card H.V := by ring
  rw [expand] at key
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel key)

theorem E_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).E
      = Fintype.card H.V * Fintype.card H.V * G.E + Fintype.card G.V * H.E := by
  have hdeg : ∀ p : G.V × H.V, (lexProduct G H).toSimple.degree p
      = G.toSimple.degree p.1 * Fintype.card H.V + H.toSimple.degree p.2 :=
    fun p ↦ degree_lexProduct G H p
  have hG : ∑ a : G.V, G.toSimple.degree a = 2 * G.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hH : ∑ b : H.V, H.toSimple.degree b = 2 * H.E :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hlex : ∑ p : G.V × H.V, (lexProduct G H).toSimple.degree p
      = 2 * (lexProduct G H).E := SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hfibre : ∀ a : G.V,
      ∑ b : H.V, (G.toSimple.degree a * Fintype.card H.V + H.toSimple.degree b)
        = G.toSimple.degree a * (Fintype.card H.V * Fintype.card H.V) + 2 * H.E := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, hH]
    ring
  have key : 2 * (lexProduct G H).E
      = 2 * (Fintype.card H.V * Fintype.card H.V * G.E + Fintype.card G.V * H.E) := by
    rw [← hlex, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hdeg (a, b),
      Finset.sum_congr rfl fun a _ ↦ hfibre a, Finset.sum_add_distrib, ← Finset.sum_mul, hG,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-! ### Domination in disjoint unions, joins and cartesian products -/

theorem isDominatingSet_disjSum {G H : CGraph} {s : Finset G.V} {t : Finset H.V}
    (hs : G.IsDominatingSet s) (ht : H.IsDominatingSet t) :
    (disjUnion G H).IsDominatingSet (s.disjSum t) := by
  intro v
  rcases v with a | b
  · rcases hs a with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inl_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inl u, Finset.inl_mem_disjSum.2 hu, by simpa using hadj⟩
  · rcases ht b with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.inr_mem_disjSum.2 h)
    · exact Or.inr ⟨Sum.inr u, Finset.inr_mem_disjSum.2 hu, by simpa using hadj⟩

/-- **Domination is additive over components**: the two sides of a disjoint union have to be
dominated separately, and any two dominating sets can be put side by side. -/
theorem domNum_disjUnion (G H : CGraph) :
    (disjUnion G H).domNum = G.domNum + H.domNum := by
  apply le_antisymm
  · obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
    obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
    have h := domNum_le_card_of_isDominatingSet (isDominatingSet_disjSum hsdom htdom)
    rwa [Finset.card_disjSum, hs, ht] at h
  · obtain ⟨u, hu, hudom⟩ := (disjUnion G H).exists_isDominatingSet_domNum
    have hG : G.IsDominatingSet u.toLeft := by
      intro v
      rcases hudom (Sum.inl v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toLeft.2 h)
      · rcases w with a | b
        · exact Or.inr ⟨a, Finset.mem_toLeft.2 hw, by simpa using hadj⟩
        · simp at hadj
    have hH : H.IsDominatingSet u.toRight := by
      intro v
      rcases hudom (Sum.inr v) with h | ⟨w, hw, hadj⟩
      · exact Or.inl (Finset.mem_toRight.2 h)
      · rcases w with a | b
        · simp at hadj
        · exact Or.inr ⟨b, Finset.mem_toRight.2 hw, by simpa using hadj⟩
    have h1 := domNum_le_card_of_isDominatingSet hG
    have h2 := domNum_le_card_of_isDominatingSet hH
    have h3 : u.toLeft.card + u.toRight.card = u.card :=
      Finset.card_toLeft_add_card_toRight
    omega

/-- One vertex from each side dominates a join. -/
theorem domNum_join_le_two (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] : (join G H).domNum ≤ 2 := by
  obtain ⟨a⟩ := ‹Nonempty G.V›
  obtain ⟨b⟩ := ‹Nonempty H.V›
  have hdom : (join G H).IsDominatingSet {Sum.inl a, Sum.inr b} := by
    intro v
    rcases v with x | y
    · by_cases h : x = a
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inr b, by simp, join_adj_inr_inl G H b x⟩
    · by_cases h : y = b
      · exact Or.inl (by simp [h])
      · exact Or.inr ⟨Sum.inl a, by simp, join_adj_inl_inr G H a y⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  have hcard : ({Sum.inl a, Sum.inr b} : Finset (join G H).V).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- A single vertex dominates a join exactly when it is universal on its own side: the other side
is seen for free. -/
theorem domNum_join_eq_one_iff (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  rw [domNum_eq_one_iff, domNum_eq_one_iff, domNum_eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    rcases v with a | b
    · refine Or.inl ⟨a, fun u hu ↦ ?_⟩
      have := hv (Sum.inl u) fun h ↦ hu (Sum.inl_injective h)
      simpa using this
    · refine Or.inr ⟨b, fun u hu ↦ ?_⟩
      have := hv (Sum.inr u) fun h ↦ hu (Sum.inr_injective h)
      simpa using this
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Sum.inl a, fun u hu ↦ ?_⟩
      rcases u with c | d
      · rw [join_adj_inl_inl]
        exact ha c fun h ↦ hu (congrArg Sum.inl h)
      · exact join_adj_inl_inr G H a d
    · refine ⟨Sum.inr b, fun u hu ↦ ?_⟩
      rcases u with c | d
      · exact join_adj_inr_inl G H b c
      · rw [join_adj_inr_inr]
        exact hb d fun h ↦ hu (congrArg Sum.inr h)

/-- Without a universal vertex on either side, a join needs exactly two dominating vertices. -/
theorem domNum_join_eq_two (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty G.V] [Nonempty H.V] (hG : G.domNum ≠ 1) (hH : H.domNum ≠ 1) :
    (join G H).domNum = 2 := by
  haveI : Nonempty (join G H).V := ⟨Sum.inl (Classical.arbitrary G.V)⟩
  have h1 := domNum_join_le_two G H
  have h2 := (join G H).domNum_pos (Fintype.card_pos_iff.2 ‹Nonempty (join G H).V›)
  have h3 : (join G H).domNum ≠ 1 := fun h ↦ by
    rcases (domNum_join_eq_one_iff G H).1 h with h | h
    · exact hG h
    · exact hH h
  omega

/-- A dominating set of `G`, spread over every fibre, dominates `G □ H`. -/
theorem domNum_cartesianProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).domNum ≤ G.domNum * Fintype.card H.V := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (cartesianProduct G H).IsDominatingSet (s ×ˢ Finset.univ) := by
    rintro ⟨x, y⟩
    rcases hsdom x with h | ⟨u, hu, hadj⟩
    · exact Or.inl (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
    · refine Or.inr ⟨(u, y), Finset.mem_product.2 ⟨hu, Finset.mem_univ _⟩, ?_⟩
      rw [cartesianProduct_adj]
      simp [hadj]
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, Finset.card_univ, hs] at h

/-! ### The radius of a cartesian product -/

/-- The eccentricity of a vertex of a box product is the sum of the eccentricities of its
coordinates: a farthest vertex can be chosen coordinatewise. -/
theorem eccent_boxProd {α β : Type} [Fintype α] [Fintype β]
    (S : SimpleGraph α) (T : SimpleGraph β) (p : α × β) :
    (S.boxProd T).eccent p = S.eccent p.1 + T.eccent p.2 := by
  refine le_antisymm ((SimpleGraph.eccent_le_iff _ _).2 fun q ↦ ?_) ?_
  · rw [SimpleGraph.edist_boxProd]
    exact add_le_add SimpleGraph.edist_le_eccent SimpleGraph.edist_le_eccent
  · obtain ⟨x, hx⟩ := S.exists_edist_eq_eccent_of_finite p.1
    obtain ⟨y, hy⟩ := T.exists_edist_eq_eccent_of_finite p.2
    rw [← hx, ← hy, ← SimpleGraph.edist_boxProd (x := p) (y := (x, y))]
    exact SimpleGraph.edist_le_eccent

/-- **The radius of a box product is the sum of the radii**: a central vertex can be chosen
coordinatewise. -/
theorem radius_boxProd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : SimpleGraph α) (T : SimpleGraph β) :
    (S.boxProd T).radius = S.radius + T.radius := by
  refine le_antisymm ?_ ?_
  · obtain ⟨a, ha⟩ := S.exists_eccent_eq_radius
    obtain ⟨b, hb⟩ := T.exists_eccent_eq_radius
    rw [← ha, ← hb, ← eccent_boxProd S T (a, b)]
    exact SimpleGraph.radius_le_eccent
  · obtain ⟨p, hp⟩ := (S.boxProd T).exists_eccent_eq_radius
    rw [← hp, eccent_boxProd]
    exact add_le_add SimpleGraph.radius_le_eccent SimpleGraph.radius_le_eccent

/-- **The radius of a cartesian product is the sum of the radii.**  Both factors have to be
connected: the radius of a disconnected graph is the junk value `0`. -/
theorem radius_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (cartesianProduct G H).radius = G.radius + H.radius := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hGtop : G.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hG
  have hHtop : H.toSimple.radius ≠ ⊤ := SimpleGraph.radius_ne_top_iff.2 hH
  have h : (cartesianProduct G H).toSimple.radius = G.toSimple.radius + H.toSimple.radius := by
    rw [toSimple_cartesianProduct]
    exact radius_boxProd _ _
  show (cartesianProduct G H).toSimple.radius.toNat = _
  rw [h, ENat.toNat_add hGtop hHtop]
  rfl

/-- Adding edges cannot increase the diameter: the strong product is at most as wide as the
cartesian product living inside it. -/
theorem diameter_strongProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (strongProduct G H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (cartesianProduct G H).IsConnected :=
    (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (cartesianProduct G H).V := hcp.nonempty
  have hne : (cartesianProduct G H).toSimple.ediam ≠ ⊤ :=
    SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_strongProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-- The same bound for the lexicographic product. -/
theorem diameter_lexProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsConnected) (hH : H.IsConnected) :
    (lexProduct G H).diameter ≤ G.diameter + H.diameter := by
  haveI : Nonempty G.V := hG.nonempty
  haveI : Nonempty H.V := hH.nonempty
  have hcp : (cartesianProduct G H).IsConnected :=
    (isConnected_cartesianProduct_iff G H).2 ⟨hG, hH⟩
  haveI : Nonempty (cartesianProduct G H).V := hcp.nonempty
  have hne : (cartesianProduct G H).toSimple.ediam ≠ ⊤ :=
    SimpleGraph.connected_iff_ediam_ne_top.1 hcp
  have h := SimpleGraph.diam_anti_of_ediam_ne_top (cartesianProduct_le_lexProduct G H) hne
  rw [← diameter_cartesianProduct G H hG hH]
  exact h

/-! ### Domination in the graph products -/

/-- **Vizing's bound for the strong product**: a product of dominating sets dominates, because a
vertex of `G ⊠ H` is either equal or adjacent to a dominator in each coordinate. -/
theorem domNum_strongProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).domNum ≤ G.domNum * H.domNum := by
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  obtain ⟨t, ht, htdom⟩ := H.exists_isDominatingSet_domNum
  have hdom : (strongProduct G H).IsDominatingSet (s ×ˢ t) := by
    rintro ⟨x, y⟩
    have hx : ∃ u ∈ s, u = x ∨ G.Adj u x = true := by
      rcases hsdom x with h | ⟨u, hu, hadj⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨u, hu, Or.inr hadj⟩
    have hy : ∃ v ∈ t, v = y ∨ H.Adj v y = true := by
      rcases htdom y with h | ⟨v, hv, hadj⟩
      · exact ⟨y, h, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr hadj⟩
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    by_cases hpq : ((u, v) : (strongProduct G H).V) = (x, y)
    · exact Or.inl (hpq ▸ Finset.mem_product.2 ⟨hu, hv⟩)
    · refine Or.inr ⟨(u, v), Finset.mem_product.2 ⟨hu, hv⟩, ?_⟩
      rw [strongProduct_adj]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
      exact ⟨hpq, hux, hvy⟩
  have h := domNum_le_card_of_isDominatingSet hdom
  rwa [Finset.card_product, hs, ht] at h

/-- Forgetting the second coordinate turns a dominating set of `G[H]` into one of `G`. -/
theorem domNum_le_domNum_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty H.V] : G.domNum ≤ (lexProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (lexProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (lexProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [lexProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with h1 | ⟨h1, -⟩
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- **A blow-up by a dominated graph does not change the domination number**: if some vertex of `H`
sees all of `H`, then a dominating set of `G` lifted into that vertex's fibre dominates `G[H]`. -/
theorem domNum_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hH : H.domNum = 1) : (lexProduct G H).domNum = G.domNum := by
  obtain ⟨x, hx⟩ := (domNum_eq_one_iff H).1 hH
  haveI : Nonempty H.V := ⟨x⟩
  refine le_antisymm ?_ (domNum_le_domNum_lexProduct G H)
  obtain ⟨s, hs, hsdom⟩ := G.exists_isDominatingSet_domNum
  have hdom : (lexProduct G H).IsDominatingSet (s.image fun v ↦ (v, x)) := by
    rintro ⟨u, y⟩
    rcases hsdom u with h | ⟨v, hv, hadj⟩
    · by_cases hy : y = x
      · exact Or.inl (Finset.mem_image.2 ⟨u, h, by rw [hy]⟩)
      · refine Or.inr ⟨(u, x), Finset.mem_image.2 ⟨u, h, rfl⟩, ?_⟩
        rw [lexProduct_adj]
        simp [hx y hy]
    · refine Or.inr ⟨(v, x), Finset.mem_image.2 ⟨v, hv, rfl⟩, ?_⟩
      rw [lexProduct_adj]
      simp [hadj]
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  rw [Finset.card_image_of_injective _ fun a b hab ↦ congrArg Prod.fst hab, hs]

/-- Forgetting the second coordinate turns a dominating set of `G □ H` into one of `G`. -/
theorem domNum_le_domNum_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty H.V] : G.domNum ≤ (cartesianProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (cartesianProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (cartesianProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [cartesianProduct_adj] at hadj
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-- Forgetting the second coordinate turns a dominating set of `G ⊠ H` into one of `G`. -/
theorem domNum_le_domNum_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    [Nonempty H.V] : G.domNum ≤ (strongProduct G H).domNum := by
  obtain ⟨s, hs, hsdom⟩ := (strongProduct G H).exists_isDominatingSet_domNum
  obtain ⟨y⟩ := ‹Nonempty H.V›
  have hdom : G.IsDominatingSet (s.image Prod.fst) := by
    intro u
    rcases hsdom ((u, y) : (strongProduct G H).V) with h | ⟨w, hw, hadj⟩
    · exact Or.inl (Finset.mem_image.2 ⟨(u, y), h, rfl⟩)
    · rw [strongProduct_adj] at hadj
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hadj
      rcases hadj.2.1 with h1 | h1
      · exact Or.inl (Finset.mem_image.2 ⟨w, hw, h1⟩)
      · exact Or.inr ⟨w.1, Finset.mem_image.2 ⟨w, hw, rfl⟩, h1⟩
  exact le_trans (domNum_le_card_of_isDominatingSet hdom) (hs ▸ Finset.card_image_le)

/-! ### Independence numbers of the graph products -/

/-- Independence number is antitone in the graph: adding edges can only shrink it. -/
private theorem indepNum_anti {α : Type} [Fintype α] {S T : SimpleGraph α} (h : S ≤ T) :
    T.indepNum ≤ S.indepNum := by
  obtain ⟨s, hs, hcard⟩ := T.exists_isNIndepSet_indepNum
  have hind : S.IsIndepSet (s : Set α) := by
    intro x hx y hy hxy hadj
    exact hs hx hy hxy (h hadj)
  exact hcard ▸ hind.card_le_indepNum

/-- The strong product is a subgraph of the lexicographic product. -/
theorem strongProduct_le_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).toSimple ≤ (lexProduct G H).toSimple := by
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

/-- **A product of independent sets is independent in the strong product**, so
`α(G) · α(H) ≤ α(G ⊠ H)`.  This is the inequality behind the Shannon capacity of a graph. -/
theorem indepNum_mul_indepNum_le_indepNum_strongProduct (G H : CGraph)
    [DecidableEq G.V] [DecidableEq H.V] :
    G.indepNum * H.indepNum ≤ (strongProduct G H).indepNum := by
  have h := indepNum_anti (strongProduct_le_lexProduct G H)
  rwa [show (lexProduct G H).toSimple.indepNum = G.indepNum * H.indepNum from
    indepNum_lexProduct G H] at h

/-- The same product set is independent in the (sparser) cartesian product. -/
theorem indepNum_mul_indepNum_le_indepNum_cartesianProduct (G H : CGraph)
    [DecidableEq G.V] [DecidableEq H.V] :
    G.indepNum * H.indepNum ≤ (cartesianProduct G H).indepNum :=
  le_trans (indepNum_mul_indepNum_le_indepNum_strongProduct G H)
    (indepNum_anti (cartesianProduct_le_strongProduct G H))

/-- In the tensor product a whole slab `S ×ˢ univ` over an independent set `S` is independent,
because every tensor edge moves in *both* coordinates: `α(G) · |V(H)| ≤ α(G × H)`. -/
theorem indepNum_mul_card_le_indepNum_tensorProduct (G H : CGraph)
    [DecidableEq G.V] [DecidableEq H.V] :
    G.indepNum * Fintype.card H.V ≤ (tensorProduct G H).indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  have hind : (tensorProduct G H).toSimple.IsIndepSet
      ((s ×ˢ (Finset.univ : Finset H.V) : Finset (G.V × H.V)) : Set (G.V × H.V)) := by
    intro p hp q hq hpq hadj
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    rw [CGraph.toSimple_adj, tensorProduct_adj, Bool.and_eq_true] at hadj
    have hne : p.1 ≠ q.1 := fun h ↦ G.loopless q.1 (h ▸ hadj.1)
    exact hs hp.1 hq.1 hne hadj.1
  calc G.indepNum * Fintype.card H.V
      = (s ×ˢ (Finset.univ : Finset H.V)).card := by
        rw [Finset.card_product, hcard, Finset.card_univ]
        rfl
    _ ≤ _ := hind.card_le_indepNum

/-- Fibrewise counting: an independent set of `G □ H` meets each fibre `{a} × V(H)` in an
independent set of `H`, so `α(G □ H) ≤ |V(G)| · α(H)`. -/
theorem indepNum_cartesianProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).indepNum ≤ Fintype.card G.V * H.indepNum := by
  classical
  obtain ⟨s, hs, hcard⟩ := (cartesianProduct G H).toSimple.exists_isNIndepSet_indepNum
  have hfib : ∀ a : G.V, (s.filter fun p ↦ p.1 = a).card ≤ H.indepNum := by
    intro a
    have hindH : H.toSimple.IsIndepSet
        (((s.filter fun p ↦ p.1 = a).image Prod.snd : Finset H.V) : Set H.V) := by
      intro y hy z hz hyz hadj
      rw [Finset.mem_coe, Finset.mem_image] at hy hz
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨q, hq, rfl⟩ := hz
      rw [Finset.mem_filter] at hp hq
      refine hs hp.1 hq.1 (fun h ↦ hyz (congrArg Prod.snd h)) ?_
      rw [CGraph.toSimple_adj, cartesianProduct_adj]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨hp.2.trans hq.2.symm, hadj⟩
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd
      (fun p hp ↦ Finset.mem_image_of_mem _ hp) ?_) hindH.card_le_indepNum
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq
  have hsum : s.card = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ ↦ Finset.mem_univ p.1
  calc (cartesianProduct G H).indepNum = s.card := hcard.symm
    _ = ∑ a : G.V, (s.filter fun p ↦ p.1 = a).card := hsum
    _ ≤ ∑ _a : G.V, H.indepNum := Finset.sum_le_sum fun a _ ↦ hfib a
    _ = Fintype.card G.V * H.indepNum := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The strong product has at least as many edges as the cartesian one, so the same bound holds. -/
theorem indepNum_strongProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).indepNum ≤ Fintype.card G.V * H.indepNum :=
  le_trans (indepNum_anti (cartesianProduct_le_strongProduct G H))
    (indepNum_cartesianProduct_le G H)

/-! ### Colouring the strong product -/

/-- **The strong product multiplies chromatic numbers, at worst**: it sits inside the
lexicographic product, which is already known to satisfy `χ ≤ χ(G)·χ(H)`, and colourings pull
back along subgraph inclusions. -/
theorem chromNum_strongProduct_le (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).chromNum ≤ G.chromNum * H.chromNum :=
  chromNum_le_iff_colorable.2
    ((chromNum_le_iff_colorable.1 (chromNum_lexProduct_le G H)).mono_left
      (strongProduct_le_lexProduct G H))

/-- Both factors appear as fibres of the cartesian product, which the strong product contains,
so `max χ(G) χ(H) ≤ χ(G ⊠ H)`. -/
theorem max_chromNum_le_chromNum_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a : G.V) (b : H.V) : max G.chromNum H.chromNum ≤ (strongProduct G H).chromNum := by
  rw [← chromNum_cartesianProduct G H a b]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_strongProduct G H))

/-- The same sandwich for the lexicographic product. -/
theorem max_chromNum_le_chromNum_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a : G.V) (b : H.V) : max G.chromNum H.chromNum ≤ (lexProduct G H).chromNum := by
  rw [← chromNum_cartesianProduct G H a b]
  exact chromNum_le_iff_colorable.2
    (colorable_chromNum.mono_left (cartesianProduct_le_lexProduct G H))

/-- Cliques multiply in the strong product, so `ω(G)·ω(H) ≤ χ(G ⊠ H)`: the lower bound coming
from cliques is itself multiplicative. -/
theorem cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (G H : CGraph)
    [DecidableEq G.V] [DecidableEq H.V] :
    G.cliqueNum * H.cliqueNum ≤ (strongProduct G H).chromNum := by
  have h := (strongProduct G H).cliqueNum_le_chromNum
  rwa [cliqueNum_strongProduct] at h

/-- The tensor product of two graphs with an edge has an edge, hence needs two colours.  Together
with `chromNum_tensorProduct_le` this pins `χ(G × H) = 2` as soon as one factor is bipartite and
both have an edge.  In general the lower bound is the hard direction: Hedetniemi's conjecture that
`χ(G × H) = min χ(G) χ(H)` is false. -/
theorem two_le_chromNum_tensorProduct {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : 0 < G.E) (hH : 0 < H.E) : 2 ≤ (tensorProduct G H).chromNum := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  refine two_le_chromNum_of_adj (a := ((a, b) : (tensorProduct G H).V)) (b := (a', b')) ?_
  rw [tensorProduct_adj]
  simp [ha, hb]

/-- One bipartite factor is enough: if `G` is bipartite and both factors have an edge then
`χ(G × H) = 2`. -/
theorem chromNum_tensorProduct_eq_two {G H : CGraph} [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsBipartite) (hGE : 0 < G.E) (hHE : 0 < H.E) :
    (tensorProduct G H).chromNum = 2 :=
  le_antisymm
    (le_trans (chromNum_tensorProduct_le G H)
      (le_trans (min_le_left _ _) (isBipartite_iff_chromNum_le_two.1 hG)))
    (two_le_chromNum_tensorProduct hGE hHE)


/-! ### Nordhaus–Gaddum for the domination number -/

/-- **`γ(G) + γ(Gᶜ) ≤ |V| + 1`.**  Each graph satisfies `γ + Δ ≤ |V|`, and complementation turns
the maximum degree into `|V| - 1 - δ`, so the two bounds add up with `δ ≤ Δ` to spare. -/
theorem domNum_add_domNum_compl_le_card_add_one (G : CGraph) [DecidableEq G.V] :
    G.domNum + (compl G).domNum ≤ Fintype.card G.V + 1 := by
  rcases isEmpty_or_nonempty G.V with hemp | hne
  · have h1 : Fintype.card G.V = 0 := Fintype.card_eq_zero
    have h2 := G.domNum_le_card
    have h3 := (compl G).domNum_le_card
    have h4 : Fintype.card (compl G).V = Fintype.card G.V := rfl
    omega
  obtain ⟨v₀⟩ := hne
  have h1 := G.domNum_add_maxDeg_le_card
  have h2 := (compl G).domNum_add_maxDeg_le_card
  rw [maxDeg_compl G v₀, show Fintype.card (compl G).V = Fintype.card G.V from rfl] at h2
  have h3 := G.minDeg_le_maxDeg
  have h4 := G.maxDeg_lt_card v₀
  omega

/-- Two vertices in different components dominate the complement: whatever `x` is, it is
unreachable from one of them, hence adjacent to it in `Gᶜ`. -/
theorem domNum_compl_le_two_of_not_reachable (G : CGraph) [DecidableEq G.V] {a b : G.V}
    (h : ¬ G.toSimple.Reachable a b) : (compl G).domNum ≤ 2 := by
  classical
  have hdom : (compl G).IsDominatingSet ({a, b} : Finset G.V) := by
    intro x
    by_cases hxa : x = a
    · exact Or.inl (by simp [hxa])
    by_cases hxb : x = b
    · exact Or.inl (by simp [hxb])
    by_cases hr : G.toSimple.Reachable a x
    · refine Or.inr ⟨b, by simp, ?_⟩
      have hbx : ¬ G.toSimple.Reachable b x := fun hbx ↦ h (hr.trans hbx.symm)
      simpa using compl_adj_of_not_reachable G hbx
    · exact Or.inr ⟨a, by simp, by simpa using compl_adj_of_not_reachable G hr⟩
  refine le_trans (domNum_le_card_of_isDominatingSet hdom) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- A disconnected graph has a complement that two vertices dominate. -/
theorem domNum_compl_le_two_of_not_isConnected (G : CGraph) [DecidableEq G.V] [Nonempty G.V]
    (h : ¬ G.IsConnected) : (compl G).domNum ≤ 2 := by
  rw [IsConnected, SimpleGraph.connected_iff] at h
  push_neg at h
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ G.toSimple.Reachable a b := by
    by_contra hc
    push_neg at hc
    exact absurd (h fun a b ↦ hc a b) (not_isEmpty_iff.2 ‹Nonempty G.V›)
  exact domNum_compl_le_two_of_not_reachable G hab

/-- A graph and its complement cannot both have a universal vertex once there are two vertices,
so `3 ≤ γ(G) + γ(Gᶜ)`. -/
theorem three_le_domNum_add_domNum_compl (G : CGraph) [DecidableEq G.V]
    (hV : 2 ≤ Fintype.card G.V) : 3 ≤ G.domNum + (compl G).domNum := by
  have hG : 0 < G.domNum := G.domNum_pos (by omega)
  have hGc : 0 < (compl G).domNum :=
    (compl G).domNum_pos (by rw [show Fintype.card (compl G).V = Fintype.card G.V from rfl]; omega)
  by_contra hc
  have h1 : G.domNum = 1 := by omega
  have h2 : (compl G).domNum = 1 := by omega
  obtain ⟨v, hv⟩ := (domNum_eq_one_iff G).1 h1
  obtain ⟨w, hw⟩ := (domNum_eq_one_iff (compl G)).1 h2
  by_cases hvw : w = v
  · subst hvw
    obtain ⟨u, hu⟩ : ∃ u : G.V, u ≠ w := by
      by_contra hc'
      push_neg at hc'
      have : Fintype.card G.V ≤ 1 := Fintype.card_le_one_iff.2 fun a b ↦ (hc' a).trans (hc' b).symm
      omega
    have h3 := hv u hu
    have h4 := hw u hu
    rw [compl_adj] at h4
    simp [h3] at h4
  · have h3 := hv w hvw
    have h4 := hw v (fun h ↦ hvw h.symm)
    rw [compl_adj] at h4
    rw [G.symm v w] at h3
    simp [h3] at h4

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

/-! ### Clique numbers of the cartesian, tensor and lexicographic products -/

theorem cliqueNum_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (cartesianProduct G H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, cliqueNum_mk, cliqueNum_mk, cliqueNum_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.cliqueNum_cartesianProduct _ _ a b

@[simp] theorem cliqueNum_tensorProduct (G H : IsoGraph) :
    (tensorProduct G H).cliqueNum = min G.cliqueNum H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_tensorProduct _ _

@[simp] theorem cliqueNum_lexProduct (G H : IsoGraph) :
    (lexProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, cliqueNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_lexProduct _ _

/-- A maximum clique of a rook graph is a full row or a full column. -/
@[simp] theorem cliqueNum_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (rook m n).cliqueNum = max m n := by
  rw [show rook m n = cartesianProduct (complete m) (complete n) from rfl,
    cliqueNum_cartesianProduct (by simpa using hm) (by simpa using hn), cliqueNum_complete,
    cliqueNum_complete]

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

/-! ### Vertex- and arc-transitivity -/

@[simp] theorem isVertexTransitive_empty (n : ℕ) : IsVertexTransitive (empty n) :=
  CGraph.isVertexTransitive_empty n

@[simp] theorem isArcTransitive_empty (n : ℕ) : IsArcTransitive (empty n) :=
  CGraph.isArcTransitive_empty n

@[simp] theorem isVertexTransitive_complete (n : ℕ) : IsVertexTransitive (complete n) :=
  CGraph.isVertexTransitive_complete n

@[simp] theorem isArcTransitive_complete (n : ℕ) : IsArcTransitive (complete n) :=
  CGraph.isArcTransitive_complete n

@[simp] theorem isVertexTransitive_cycle (n : ℕ) : IsVertexTransitive (cycle n) :=
  CGraph.isVertexTransitive_cycle n

@[simp] theorem isArcTransitive_cycle (n : ℕ) : IsArcTransitive (cycle n) :=
  CGraph.isArcTransitive_cycle n

@[simp] theorem isVertexTransitive_hypercube (n : ℕ) : IsVertexTransitive (hypercube n) :=
  CGraph.isVertexTransitive_hypercube n

@[simp] theorem isArcTransitive_hypercube (n : ℕ) : IsArcTransitive (hypercube n) :=
  CGraph.isArcTransitive_hypercube n

@[simp] theorem isVertexTransitive_foldedCube (n : ℕ) : IsVertexTransitive (foldedCube n) :=
  CGraph.isVertexTransitive_foldedCube n

@[simp] theorem isArcTransitive_bipartite_self (n : ℕ) : IsArcTransitive (bipartite n n) :=
  CGraph.isArcTransitive_bipartite_self n

@[simp] theorem isVertexTransitive_bipartite_self (n : ℕ) : IsVertexTransitive (bipartite n n) :=
  CGraph.isVertexTransitive_bipartite_self n

@[simp] theorem isArcTransitive_kneser (n k : ℕ) : IsArcTransitive (kneser n k) :=
  CGraph.isArcTransitive_kneser n k

@[simp] theorem isVertexTransitive_kneser (n k : ℕ) : IsVertexTransitive (kneser n k) :=
  CGraph.isVertexTransitive_kneser n k

/-- The complement has the same automorphisms. -/
theorem IsVertexTransitive.compl {G : IsoGraph} (h : IsVertexTransitive G) :
    IsVertexTransitive (IsoGraph.compl G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at h
  exact CGraph.isVertexTransitive_compl _ h

@[simp] theorem isVertexTransitive_compl (G : IsoGraph) :
    IsVertexTransitive (IsoGraph.compl G) ↔ IsVertexTransitive G :=
  ⟨fun h ↦ by simpa using h.compl, IsVertexTransitive.compl⟩

theorem IsVertexTransitive.cartesianProduct {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : IsVertexTransitive H) : IsVertexTransitive (IsoGraph.cartesianProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at hG hH
  exact CGraph.isVertexTransitive_cartesianProduct _ _ hG hH

theorem IsVertexTransitive.tensorProduct {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : IsVertexTransitive H) : IsVertexTransitive (IsoGraph.tensorProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at hG hH
  exact CGraph.isVertexTransitive_tensorProduct _ _ hG hH

theorem IsVertexTransitive.strongProduct {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : IsVertexTransitive H) : IsVertexTransitive (IsoGraph.strongProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at hG hH
  exact CGraph.isVertexTransitive_strongProduct _ _ hG hH

theorem IsVertexTransitive.lexProduct {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : IsVertexTransitive H) : IsVertexTransitive (IsoGraph.lexProduct G H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, isVertexTransitive_mk]
  rw [isVertexTransitive_mk] at hG hH
  exact CGraph.isVertexTransitive_lexProduct _ _ hG hH

/-- Arcs of `G` are vertices of its line graph, so arc-transitivity becomes vertex-transitivity. -/
theorem IsArcTransitive.lineGraph {G : IsoGraph} (h : IsArcTransitive G) :
    IsVertexTransitive (IsoGraph.lineGraph G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [lineGraph_mk, isVertexTransitive_mk]
  rw [isArcTransitive_mk] at h
  exact CGraph.isVertexTransitive_lineGraph _ h

/-! Derived transitivity. -/

@[simp] theorem isVertexTransitive_petersen : IsVertexTransitive petersen :=
  isVertexTransitive_kneser 5 2

@[simp] theorem isArcTransitive_petersen : IsArcTransitive petersen := isArcTransitive_kneser 5 2

@[simp] theorem isVertexTransitive_triangular (n : ℕ) : IsVertexTransitive (triangular n) := by
  rw [triangular_eq_compl_kneser, isVertexTransitive_compl]
  exact isVertexTransitive_kneser n 2

@[simp] theorem isVertexTransitive_rook (m n : ℕ) : IsVertexTransitive (rook m n) :=
  (isVertexTransitive_complete m).cartesianProduct (isVertexTransitive_complete n)

@[simp] theorem isVertexTransitive_prism (n : ℕ) : IsVertexTransitive (prism n) :=
  (isVertexTransitive_cycle n).cartesianProduct (isVertexTransitive_complete 2)

@[simp] theorem isVertexTransitive_cocktailParty (n : ℕ) :
    IsVertexTransitive (cocktailParty n) := by
  rw [cocktailParty_eq_lexProduct]
  exact (isVertexTransitive_complete n).lexProduct (isVertexTransitive_empty 2)

@[simp] theorem isVertexTransitive_lineGraph_complete (n : ℕ) :
    IsVertexTransitive (lineGraph (complete n)) := (isArcTransitive_complete n).lineGraph

@[simp] theorem isVertexTransitive_lineGraph_cycle (n : ℕ) :
    IsVertexTransitive (lineGraph (cycle n)) := (isArcTransitive_cycle n).lineGraph

/-! ### Strong regularity -/

/-- The complement of a strongly regular graph is strongly regular. -/
theorem IsSRGWith.compl {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    IsSRGWith (IsoGraph.compl G) n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, isSRGWith_mk]
  rw [isSRGWith_mk] at h
  exact CGraph.isSRGWith_compl _ h

theorem isSRGWith_rook (k : ℕ) : IsSRGWith (rook k k) (k * k) (2 * (k - 1)) (k - 2) 2 := by
  show IsSRGWith (cartesianProduct (complete k) (complete k)) _ _ _ _
  rw [complete_def, cartesianProduct_mk, isSRGWith_mk]
  exact CGraph.isSRGWith_rook k

theorem isSRGWith_kneser_two (n : ℕ) :
    IsSRGWith (kneser n 2) (n.choose 2) ((n - 2).choose 2) ((n - 4).choose 2)
      ((n - 3).choose 2) := by
  rw [kneser_def, isSRGWith_mk]
  exact CGraph.isSRGWith_kneser_two n

theorem isSRGWith_johnson_two (n : ℕ) (hn : 4 ≤ n) :
    IsSRGWith (johnson n 2) (n.choose 2) (2 * (n - 2)) (n - 2) 4 := by
  rw [johnson_def, isSRGWith_mk]
  exact CGraph.isSRGWith_johnson_two n hn

theorem isSRGWith_triangular (n : ℕ) (hn : 4 ≤ n) :
    IsSRGWith (triangular n) (n.choose 2) (2 * (n - 2)) (n - 2) 4 :=
  isSRGWith_johnson_two n hn

theorem isSRGWith_bipartite (n : ℕ) : IsSRGWith (bipartite n n) (2 * n) n 0 n := by
  rw [bipartite_def, isSRGWith_mk]
  exact CGraph.isSRGWith_bipartite n

theorem isSRGWith_cocktailParty (n : ℕ) :
    IsSRGWith (cocktailParty n) (2 * n) (2 * n - 2) (2 * n - 4) (2 * n - 2) := by
  show IsSRGWith (completeMultipartite (List.replicate n 2)) _ _ _ _
  rw [completeMultipartite_def, isSRGWith_mk]
  exact CGraph.isSRGWith_cocktailParty n

theorem isSRGWith_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    IsSRGWith (paley q) q ((q - 1) / 2) ((q - 5) / 4) ((q - 1) / 4) := by
  rw [paley_def, isSRGWith_mk]
  exact CGraph.isSRGWith_paley q hq

theorem isSRGWith_petersen : IsSRGWith petersen 10 3 0 1 := isSRGWith_kneser_two 5

/-! ### The diameter of a Cartesian product -/

/-- **The diameter of a Cartesian product is the sum of the diameters.** -/
theorem diameter_cartesianProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (cartesianProduct G H).diameter = G.diameter + H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, diameter_mk, diameter_mk, diameter_mk]
  rw [isConnected_mk] at hG hH
  exact CGraph.diameter_cartesianProduct _ _ hG hH

@[simp] theorem diameter_empty (n : ℕ) : (empty n).diameter = 0 := CGraph.diameter_empty n

@[simp] theorem diameter_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (disjUnion G H).diameter = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, diameter_mk]
  rw [V_mk] at hG hH
  exact CGraph.diameter_disjUnion _ _ hG hH

/-- **The hypercube `Q_n` has diameter `n`**: flipping the bits one at a time is optimal. -/
@[simp] theorem diameter_hypercube (n : ℕ) : (hypercube n).diameter = n := by
  induction n with
  | zero => rw [hypercube_zero, diameter_empty]
  | succ n ih =>
    rw [hypercube_succ, diameter_cartesianProduct (isConnected_hypercube n)
      (isConnected_complete 1), ih, diameter_complete 0]

@[simp] theorem diameter_ladder (n : ℕ) : (ladder (n + 1)).diameter = n + 1 := by
  show (cartesianProduct (path (n + 1)) (complete 2)).diameter = n + 1
  rw [diameter_cartesianProduct (isConnected_path n) (isConnected_complete 1), diameter_path n,
    diameter_complete 0]

@[simp] theorem diameter_prism (n : ℕ) : (prism (n + 1)).diameter = (n + 1) / 2 + 1 := by
  show (cartesianProduct (cycle (n + 1)) (complete 2)).diameter = (n + 1) / 2 + 1
  rw [diameter_cartesianProduct (isConnected_cycle n) (isConnected_complete 1), diameter_cycle n,
    diameter_complete 0]

@[simp] theorem diameter_rook (m n : ℕ) : (rook (m + 2) (n + 2)).diameter = 2 := by
  show (cartesianProduct (complete (m + 2)) (complete (n + 2))).diameter = 2
  rw [diameter_cartesianProduct (isConnected_complete (m + 1)) (isConnected_complete (n + 1)),
    diameter_complete m, diameter_complete n]

/-- The `m × n` torus, a Cartesian product of two cycles. -/
theorem diameter_cartesianProduct_cycle (m n : ℕ) :
    (cartesianProduct (cycle (m + 1)) (cycle (n + 1))).diameter = (m + 1) / 2 + (n + 1) / 2 := by
  rw [diameter_cartesianProduct (isConnected_cycle m) (isConnected_cycle n), diameter_cycle m,
    diameter_cycle n]

/-! ### Degree sequences -/

@[simp] theorem length_degSequence (G : IsoGraph) : (degSequence G).length = G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.length_degSequence g

/-- The handshake lemma: the degrees add up to twice the edge count. -/
theorem sum_degSequence (G : IsoGraph) : (degSequence G).sum = 2 * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.sum_degSequence g

@[simp] theorem degSequence_empty (n : ℕ) : degSequence (empty n) = List.replicate n 0 :=
  CGraph.degSequence_empty n

@[simp] theorem degSequence_complete (n : ℕ) :
    degSequence (complete n) = List.replicate n (n - 1) := CGraph.degSequence_complete n

/-- A strongly regular graph has a constant degree sequence. -/
theorem IsSRGWith.degSequence {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    IsoGraph.degSequence G = List.replicate n k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.IsSRGWith.degSequence h

@[simp] theorem degSequence_petersen : degSequence petersen = List.replicate 10 3 :=
  isSRGWith_petersen.degSequence

@[simp] theorem degSequence_kneser_two (n : ℕ) :
    degSequence (kneser n 2) = List.replicate (n.choose 2) ((n - 2).choose 2) :=
  (isSRGWith_kneser_two n).degSequence

@[simp] theorem degSequence_cocktailParty (n : ℕ) :
    degSequence (cocktailParty n) = List.replicate (2 * n) (2 * n - 2) :=
  (isSRGWith_cocktailParty n).degSequence

@[simp] theorem degSequence_bipartite_self (n : ℕ) :
    degSequence (bipartite n n) = List.replicate (2 * n) n :=
  (isSRGWith_bipartite n).degSequence

/-- The handshake lemma for a strongly regular graph: `n` vertices of degree `k` give `n * k / 2`
edges. -/
theorem IsSRGWith.two_mul_E {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    2 * G.E = n * k := by
  rw [← sum_degSequence, h.degSequence, List.sum_replicate, smul_eq_mul]

theorem degSequence_triangular (n : ℕ) (hn : 4 ≤ n) :
    degSequence (triangular n) = List.replicate (n.choose 2) (2 * (n - 2)) :=
  (isSRGWith_triangular n hn).degSequence

/-! ### Edge counts of the complement and the line graph -/

theorem E_compl (G : IsoGraph) : (compl G).E + G.E = G.V.choose 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, E_mk, E_mk, V_mk]
  exact CGraph.E_compl _

theorem E_compl_eq (G : IsoGraph) : (compl G).E = G.V.choose 2 - G.E := by
  have := G.E_compl
  omega

theorem E_le_choose_two (G : IsoGraph) : G.E ≤ G.V.choose 2 := by
  have := G.E_compl
  omega

/-- The line graph has one vertex per edge, and one edge per pair of edges meeting at a vertex:
`∑ v, C(deg v, 2)`, written over the degree sequence so as not to name a vertex. -/
theorem E_lineGraph (G : IsoGraph) :
    (lineGraph G).E = ((degSequence G).map fun d ↦ d.choose 2).sum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, lineGraph_mk, E_mk, degSequence_mk]
  exact CGraph.E_lineGraph_eq_sum_degSequence _

/-- A regular graph's line graph has `n * C(k, 2)` edges. -/
theorem IsSRGWith.E_lineGraph {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) :
    (lineGraph G).E = n * k.choose 2 := by
  rw [IsoGraph.E_lineGraph, h.degSequence, List.map_replicate, List.sum_replicate, smul_eq_mul]

@[simp] theorem E_lineGraph_complete (n : ℕ) :
    (lineGraph (complete n)).E = n * (n - 1).choose 2 := by
  rw [E_lineGraph, degSequence_complete, List.map_replicate, List.sum_replicate, smul_eq_mul]

@[simp] theorem E_lineGraph_empty (n : ℕ) : (lineGraph (empty n)).E = 0 := by
  rw [E_lineGraph, degSequence_empty, List.map_replicate, List.sum_replicate, smul_eq_mul]
  rfl

@[simp] theorem E_triangular (n : ℕ) : (triangular n).E = n * (n - 1).choose 2 := by
  rw [← lineGraph_complete_eq_triangular, E_lineGraph_complete]

/-! ### More vertex counts -/

@[simp] theorem V_rook (m n : ℕ) : (rook m n).V = m * n := by
  show (cartesianProduct (complete m) (complete n)).V = _
  rw [V_cartesianProduct, V_complete, V_complete]

@[simp] theorem V_triangular (n : ℕ) : (triangular n).V = n.choose 2 := V_johnson n 2

@[simp] theorem V_ladder (n : ℕ) : (ladder n).V = n * 2 := by
  show (cartesianProduct (path n) (complete 2)).V = _
  rw [V_cartesianProduct, V_path, V_complete]

@[simp] theorem V_prism (n : ℕ) : (prism n).V = n * 2 := by
  show (cartesianProduct (cycle n) (complete 2)).V = _
  rw [V_cartesianProduct, V_cycle, V_complete]

@[simp] theorem V_fan (n : ℕ) : (fan n).V = 1 + n := by
  show (join (complete 1) (path n)).V = _
  rw [V_join, V_complete, V_path]

@[simp] theorem V_book (n : ℕ) : (book n).V = 2 + n := by
  show (completeMultipartite [1, 1, n]).V = _
  rw [V_completeMultipartite]
  simp
  omega

@[simp] theorem V_cocktailParty (n : ℕ) : (cocktailParty n).V = 2 * n := by
  show (completeMultipartite (List.replicate n 2)).V = _
  rw [V_completeMultipartite, List.sum_replicate, smul_eq_mul]
  omega

/-! ### Regular families beyond the strongly regular ones -/

/-- The handshake lemma for any graph whose degree sequence is constant. -/
theorem two_mul_E_of_degSequence_replicate {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : 2 * G.E = n * k := by
  rw [← sum_degSequence, h, List.sum_replicate, smul_eq_mul]

@[simp] theorem degSequence_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    degSequence (kneser n k) = List.replicate (n.choose k) ((n - k).choose k) := by
  rw [kneser_def, degSequence_mk]
  exact CGraph.degSequence_kneser hk

@[simp] theorem degSequence_rook (m n : ℕ) :
    degSequence (rook m n) = List.replicate (m * n) ((n - 1) + (m - 1)) := by
  show degSequence (cartesianProduct (complete m) (complete n)) = _
  rw [complete_def m, complete_def n, cartesianProduct_mk, degSequence_mk]
  exact CGraph.degSequence_rook m n

theorem two_mul_E_kneser (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    2 * (kneser n k).E = n.choose k * (n - k).choose k :=
  two_mul_E_of_degSequence_replicate (degSequence_kneser n hk)

theorem degSequence_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    degSequence (paley q) = List.replicate q ((q - 1) / 2) :=
  (isSRGWith_paley q hq).degSequence

/-! ### Degree sequences of the products

A product of regular graphs is regular, and on the quotient "regular of degree `k`" is exactly
"the degree sequence is `List.replicate _ k`". -/

private theorem card_eq_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : n = G.V := by
  rw [← length_degSequence, h, List.length_replicate]

theorem degSequence_cartesianProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (cartesianProduct G H) = List.replicate (m * n) (k + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_cartesianProduct hG hH

theorem degSequence_tensorProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (tensorProduct G H) = List.replicate (m * n) (k * l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_tensorProduct hG hH

theorem degSequence_lexProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (lexProduct G H) = List.replicate (m * n) (k * n + l) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_lexProduct hG hH

theorem degSequence_strongProduct {G H : IsoGraph} {m k n l : ℕ}
    (hG : degSequence G = List.replicate m k) (hH : degSequence H = List.replicate n l) :
    degSequence (strongProduct G H) = List.replicate (m * n) ((k + 1) * (l + 1) - 1) := by
  rw [card_eq_of_degSequence hG, card_eq_of_degSequence hH]
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, degSequence_mk, V_mk, V_mk]
  rw [degSequence_mk] at hG hH
  exact CGraph.degSequence_strongProduct hG hH

@[simp] theorem degSequence_hypercube (n : ℕ) :
    degSequence (hypercube n) = List.replicate (2 ^ n) n := by
  induction n with
  | zero => rw [hypercube_zero, degSequence_empty]; rfl
  | succ n ih =>
    rw [hypercube_succ, degSequence_cartesianProduct ih (degSequence_complete 2)]
    congr 1

theorem two_mul_E_hypercube (n : ℕ) : 2 * (hypercube n).E = 2 ^ n * n :=
  two_mul_E_of_degSequence_replicate (degSequence_hypercube n)

/-! ### Vertex-transitive graphs are regular -/

theorem exists_degSequence_replicate_of_isVertexTransitive {G : IsoGraph}
    (h : IsVertexTransitive G) : ∃ k, degSequence G = List.replicate G.V k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.exists_degSequence_replicate_of_isVertexTransitive h

/-- A vertex-transitive graph is regular, so the vertex and edge counts already pin down its
degree sequence. -/
theorem degSequence_of_isVertexTransitive {G : IsoGraph} {k : ℕ} (h : IsVertexTransitive G)
    (hV : 0 < G.V) (hk : G.V * k = 2 * G.E) : degSequence G = List.replicate G.V k := by
  obtain ⟨k', hk'⟩ := exists_degSequence_replicate_of_isVertexTransitive h
  have h2 := two_mul_E_of_degSequence_replicate hk'
  have : k = k' := Nat.eq_of_mul_eq_mul_left hV (hk.trans h2)
  rwa [this]

@[simp] theorem degSequence_cycle (n : ℕ) :
    degSequence (cycle (n + 3)) = List.replicate (n + 3) 2 := by
  have h := degSequence_of_isVertexTransitive (k := 2) (isVertexTransitive_cycle (n + 3))
    (by rw [V_cycle]; omega) (by rw [V_cycle, E_cycle]; omega)
  rwa [V_cycle] at h

@[simp] theorem degSequence_prism (n : ℕ) :
    degSequence (prism (n + 3)) = List.replicate ((n + 3) * 2) 3 := by
  show degSequence (cartesianProduct (cycle (n + 3)) (complete 2)) = _
  rw [degSequence_cartesianProduct (degSequence_cycle n) (degSequence_complete 2)]

@[simp] theorem E_lineGraph_cycle (n : ℕ) : (lineGraph (cycle (n + 3))).E = n + 3 := by
  rw [E_lineGraph, degSequence_cycle, List.map_replicate, List.sum_replicate, smul_eq_mul,
    show (2 : ℕ).choose 2 = 1 from rfl, mul_one]

theorem two_mul_E_prism (n : ℕ) : 2 * (prism (n + 3)).E = (n + 3) * 2 * 3 :=
  two_mul_E_of_degSequence_replicate (degSequence_prism n)

/-! ### Distinguishing graphs

Because `IsoGraph` is the quotient of `CGraph` by isomorphism, `G ≠ H` *is* the assertion that
`G` and `H` are non-isomorphic. Every invariant therefore doubles as a tool for proving
non-isomorphism: if it takes different values on the two graphs, they are different. -/

theorem ne_of_V_ne {G H : IsoGraph} (h : G.V ≠ H.V) : G ≠ H := ne_of_apply_ne V h

theorem ne_of_E_ne {G H : IsoGraph} (h : G.E ≠ H.E) : G ≠ H := ne_of_apply_ne E h

theorem ne_of_degSequence_ne {G H : IsoGraph} (h : degSequence G ≠ degSequence H) : G ≠ H :=
  ne_of_apply_ne degSequence h

theorem ne_of_diameter_ne {G H : IsoGraph} (h : G.diameter ≠ H.diameter) : G ≠ H :=
  ne_of_apply_ne diameter h

theorem ne_of_indepNum_ne {G H : IsoGraph} (h : G.indepNum ≠ H.indepNum) : G ≠ H :=
  ne_of_apply_ne indepNum h

theorem ne_of_cliqueNum_ne {G H : IsoGraph} (h : G.cliqueNum ≠ H.cliqueNum) : G ≠ H :=
  ne_of_apply_ne cliqueNum h

/-- The same principle for predicates: any property of `IsoGraph`s that holds of `G` but fails
for `H` separates them. -/
theorem ne_of_pred {p : IsoGraph → Prop} {G H : IsoGraph} (hG : p G) (hH : ¬ p H) : G ≠ H :=
  fun he ↦ hH (he ▸ hG)

theorem ne_of_isConnected {G H : IsoGraph} (hG : IsConnected G) (hH : ¬ IsConnected H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isAcyclic {G H : IsoGraph} (hG : IsAcyclic G) (hH : ¬ IsAcyclic H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isTree {G H : IsoGraph} (hG : IsTree G) (hH : ¬ IsTree H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isBipartite {G H : IsoGraph} (hG : IsBipartite G) (hH : ¬ IsBipartite H) : G ≠ H :=
  ne_of_pred hG hH

theorem ne_of_isVertexTransitive {G H : IsoGraph} (hG : IsVertexTransitive G)
    (hH : ¬ IsVertexTransitive H) : G ≠ H := ne_of_pred hG hH

theorem ne_of_isArcTransitive {G H : IsoGraph} (hG : IsArcTransitive G)
    (hH : ¬ IsArcTransitive H) : G ≠ H := ne_of_pred hG hH

private theorem replicate_ne {k a b : ℕ} (hk : 0 < k) (hab : a ≠ b) :
    List.replicate k a ≠ List.replicate k b := fun h ↦
  hab (List.eq_of_mem_replicate (h ▸ List.mem_replicate.2 ⟨hk.ne', rfl⟩))

/-- Two regular graphs on the same (positive) number of vertices but of different degree are
non-isomorphic. -/
theorem ne_of_degree_ne {G H : IsoGraph} {n k l : ℕ} (hG : degSequence G = List.replicate n k)
    (hH : degSequence H = List.replicate n l) (hn : 0 < n) (hkl : k ≠ l) : G ≠ H :=
  ne_of_degSequence_ne (by rw [hG, hH]; exact replicate_ne hn hkl)

/-! Each of the standard families is determined by its parameter. -/

@[simp] theorem empty_inj {m n : ℕ} : empty m = empty n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem complete_inj {m n : ℕ} : complete m = complete n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem path_inj {m n : ℕ} : path m = path n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem cycle_inj {m n : ℕ} : cycle m = cycle n ↔ m = n :=
  ⟨fun h ↦ by simpa using congrArg V h, fun h ↦ by rw [h]⟩

@[simp] theorem star_inj {m n : ℕ} : star m = star n ↔ m = n :=
  ⟨fun h ↦ by have h2 := congrArg V h; simp only [V_star] at h2; omega, fun h ↦ by rw [h]⟩

/-! Some non-isomorphisms between the families. -/

theorem empty_ne_complete (n : ℕ) : empty (n + 2) ≠ complete (n + 2) :=
  ne_of_E_ne (by rw [E_empty]; exact (E_complete_pos n).ne)

theorem path_ne_cycle (m n : ℕ) : path (m + 1) ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_path m) (not_isTree_cycle n)

theorem star_ne_cycle (m n : ℕ) : star m ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_star m) (not_isTree_cycle n)

theorem complete_ne_cycle (n : ℕ) : complete (n + 4) ≠ cycle (n + 4) :=
  ne_of_degree_ne (degSequence_complete (n + 4)) (degSequence_cycle (n + 1)) (by omega) (by omega)

theorem bipartite_ne_complete (m n k : ℕ) : bipartite m n ≠ complete (k + 3) :=
  ne_of_isBipartite (isBipartite_bipartite m n) (not_isBipartite_complete k)

theorem hypercube_ne_complete (n k : ℕ) : hypercube (n + 2) ≠ complete (k + 3) :=
  ne_of_isBipartite (isBipartite_hypercube (n + 2)) (not_isBipartite_complete k)

/-! ### Diameter two, connectivity and strong regularity -/

theorem isConnected_of_diameter_ne_zero {G : IsoGraph} (h : G.diameter ≠ 0) : IsConnected G := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.isConnected_of_diameter_ne_zero g h

/-- **A strongly regular graph with `μ > 0` that is not complete has diameter two.** -/
theorem IsSRGWith.diameter_eq_two {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ)
    (hμ : 0 < μ) (hk : k + 1 < n) : G.diameter = 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.IsSRGWith.diameter_eq_two h hμ hk

/-- **A strongly regular graph with `μ > 0` is connected.** -/
theorem IsSRGWith.isConnected {G : IsoGraph} {n k ℓ μ : ℕ} (h : IsSRGWith G n k ℓ μ) (hμ : 0 < μ)
    (hn : 0 < n) : IsConnected G := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.IsSRGWith.isConnected h hμ hn

private theorem lt_choose_two_aux (m : ℕ) : 2 * (m + 2) + 1 < (m + 4).choose 2 := by
  induction m with
  | zero => decide
  | succ p ih =>
    have hc : (p + 1 + 4).choose 2 = (p + 4) + (p + 4).choose 2 := by
      rw [show p + 1 + 4 = (p + 4) + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    omega

private theorem lt_choose_two {n : ℕ} (hn : 4 ≤ n) : 2 * (n - 2) + 1 < n.choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h2 : m + 4 - 2 = m + 2 := by omega
  rw [h2]
  exact lt_choose_two_aux m

@[simp] theorem diameter_petersen : petersen.diameter = 2 :=
  isSRGWith_petersen.diameter_eq_two (by norm_num) (by norm_num)

@[simp] theorem isConnected_petersen : IsConnected petersen :=
  isSRGWith_petersen.isConnected (by norm_num) (by norm_num)

@[simp] theorem diameter_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).diameter = 2 :=
  (isSRGWith_cocktailParty (n + 2)).diameter_eq_two (by omega) (by omega)

theorem diameter_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).diameter = 2 :=
  (isSRGWith_triangular n hn).diameter_eq_two (by norm_num) (lt_choose_two hn)

theorem isConnected_triangular {n : ℕ} (hn : 4 ≤ n) : IsConnected (triangular n) :=
  (isSRGWith_triangular n hn).isConnected (by norm_num) (Nat.choose_pos (by omega))

theorem diameter_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).diameter = 2 :=
  (isSRGWith_paley q hq).diameter_eq_two (by omega) (by omega)

theorem isConnected_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    IsConnected (paley q) :=
  (isSRGWith_paley q hq).isConnected (by omega) (by omega)

theorem diameter_bipartite_self (n : ℕ) : (bipartite (n + 2) (n + 2)).diameter = 2 :=
  (isSRGWith_bipartite (n + 2)).diameter_eq_two (by omega) (by omega)

theorem isConnected_bipartite_self (n : ℕ) : IsConnected (bipartite (n + 1) (n + 1)) :=
  (isSRGWith_bipartite (n + 1)).isConnected (by omega) (by omega)

/-! ### The diameter of a join -/

theorem diameter_join_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (join G H).diameter ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [V_mk] at hG hH
  haveI := Fintype.card_pos_iff.1 hG
  haveI := Fintype.card_pos_iff.1 hH
  rw [join_mk, diameter_mk]
  exact CGraph.diameter_join_le_two _ _

/-- A join whose left factor is not complete has diameter two. -/
theorem diameter_join_left {G H : IsoGraph} (hH : 0 < H.V) (h : G.E < G.V.choose 2) :
    (join G H).diameter = 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h' =>
  rw [← mk_canonicalize g, ← mk_canonicalize h'] at *
  rw [V_mk] at hH
  rw [E_mk, V_mk] at h
  haveI := Fintype.card_pos_iff.1 hH
  rw [join_mk, diameter_mk]
  obtain ⟨a, c, hne, hadj⟩ := CGraph.exists_not_adj_of_E_lt _ h
  exact CGraph.diameter_join_of_not_adj _ _ hne hadj

/-- A join whose right factor is not complete has diameter two. -/
theorem diameter_join_right {G H : IsoGraph} (hG : 0 < G.V) (h : H.E < H.V.choose 2) :
    (join G H).diameter = 2 := by
  rw [join_comm]
  exact diameter_join_left hG h

@[simp] theorem diameter_star (n : ℕ) : (star (n + 2)).diameter = 2 := by
  rw [star_eq_bipartite, bipartite_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [E_empty, V_empty]
  exact Nat.choose_pos (by omega)

@[simp] theorem diameter_book (n : ℕ) : (book (n + 2)).diameter = 2 := by
  rw [book_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [E_empty, V_empty]
  exact Nat.choose_pos (by omega)

@[simp] theorem diameter_wheel (n : ℕ) : (wheel (n + 4)).diameter = 2 := by
  rw [wheel_eq_join]
  refine diameter_join_right (by simp) ?_
  rw [show n + 4 = n + 1 + 3 from rfl, E_cycle, V_cycle]
  have := lt_choose_two (n := n + 1 + 3) (by omega)
  omega

@[simp] theorem diameter_fan (n : ℕ) : (fan (n + 4)).diameter = 2 := by
  refine diameter_join_right (by simp) ?_
  rw [show n + 4 = n + 3 + 1 from rfl, E_path, V_path]
  have := lt_choose_two (n := n + 3 + 1) (by omega)
  omega

/-! ### Complements of disconnected graphs -/

/-- **The complement of a disconnected graph is connected.** -/
theorem isConnected_compl_of_not_isConnected {G : IsoGraph} (hV : 0 < G.V)
    (h : ¬ IsConnected G) : IsConnected (compl G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [isConnected_mk] at h
  rw [compl_mk, isConnected_mk]
  haveI := Fintype.card_pos_iff.1 hV
  exact CGraph.isConnected_compl_of_not_preconnected _ fun hp ↦ h ⟨hp⟩

/-- At least one of a graph and its complement is connected. -/
theorem isConnected_or_isConnected_compl {G : IsoGraph} (hV : 0 < G.V) :
    IsConnected G ∨ IsConnected (compl G) := by
  by_cases h : IsConnected G
  · exact Or.inl h
  · exact Or.inr (isConnected_compl_of_not_isConnected hV h)

theorem diameter_compl_le_two {G : IsoGraph} (hV : 0 < G.V) (h : ¬ IsConnected G) :
    (compl G).diameter ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [isConnected_mk] at h
  rw [compl_mk, diameter_mk]
  haveI := Fintype.card_pos_iff.1 hV
  exact CGraph.diameter_compl_le_two _ fun hp ↦ h ⟨hp⟩

/-- A disconnected graph with an edge has a complement of diameter exactly two. -/
theorem diameter_compl {G : IsoGraph} (h : ¬ IsConnected G) (hE : 0 < G.E) :
    (compl G).diameter = 2 := by
  have hV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h0 | hp
    · have hle := E_le_choose_two G
      rw [h0] at hle
      simp at hle
      omega
    · exact hp
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at hV
  rw [E_mk] at hE
  rw [isConnected_mk] at h
  rw [compl_mk, diameter_mk]
  haveI := Fintype.card_pos_iff.1 hV
  exact CGraph.diameter_compl_eq_two _ (fun hp ↦ h ⟨hp⟩) hE

@[simp] theorem isConnected_compl_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    IsConnected (compl (disjUnion G H)) :=
  isConnected_compl_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

theorem diameter_compl_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V)
    (hE : 0 < G.E + H.E) : (compl (disjUnion G H)).diameter = 2 :=
  diameter_compl (not_isConnected_disjUnion hG hH) (by rw [E_disjUnion]; omega)

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

/-! ### Degree multisets

`degSequence` is a sorted list, which makes it awkward to combine: the degree sequence of a
disjoint union is a *merge* of the two sequences, not a concatenation.  The underlying multiset
`degMultiset` has no such problem, and since `degSequence` is literally its `sort`
(`coe_degSequence`) nothing is lost by working with it. -/

@[simp] theorem card_degMultiset (G : IsoGraph) : Multiset.card (degMultiset G) = G.V := by
  rw [← coe_degSequence, Multiset.coe_card, length_degSequence]

/-- The handshake lemma, for the degree multiset. -/
theorem sum_degMultiset (G : IsoGraph) : (degMultiset G).sum = 2 * G.E := by
  rw [← coe_degSequence, Multiset.sum_coe, sum_degSequence]

theorem ne_of_degMultiset_ne {G H : IsoGraph} (h : degMultiset G ≠ degMultiset H) : G ≠ H :=
  ne_of_apply_ne degMultiset h

/-- Reading a degree multiset off a constant degree sequence. -/
theorem degMultiset_of_degSequence {G : IsoGraph} {n k : ℕ}
    (h : degSequence G = List.replicate n k) : degMultiset G = Multiset.replicate n k := by
  rw [← coe_degSequence, h, Multiset.coe_replicate]

@[simp] theorem degMultiset_disjUnion (G H : IsoGraph) :
    degMultiset (disjUnion G H) = degMultiset G + degMultiset H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, disjUnion_mk, degMultiset_mk, degMultiset_mk,
    degMultiset_mk]
  exact CGraph.degMultiset_disjUnion _ _

@[simp] theorem degMultiset_join (G H : IsoGraph) :
    degMultiset (join G H) = (degMultiset G).map (· + H.V) + (degMultiset H).map (· + G.V) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, degMultiset_mk, degMultiset_mk,
    degMultiset_mk, V_mk, V_mk]
  exact CGraph.degMultiset_join _ _

@[simp] theorem degMultiset_compl (G : IsoGraph) :
    degMultiset (compl G) = (degMultiset G).map (fun d ↦ G.V - 1 - d) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_compl _

/-! ### Degree multisets of the named graphs -/

@[simp] theorem degMultiset_empty (n : ℕ) : degMultiset (empty n) = Multiset.replicate n 0 :=
  degMultiset_of_degSequence (degSequence_empty n)

@[simp] theorem degMultiset_complete (n : ℕ) :
    degMultiset (complete n) = Multiset.replicate n (n - 1) :=
  degMultiset_of_degSequence (degSequence_complete n)

@[simp] theorem degMultiset_cycle (n : ℕ) :
    degMultiset (cycle (n + 3)) = Multiset.replicate (n + 3) 2 :=
  degMultiset_of_degSequence (degSequence_cycle n)

@[simp] theorem degMultiset_petersen : degMultiset petersen = Multiset.replicate 10 3 :=
  degMultiset_of_degSequence degSequence_petersen

@[simp] theorem degMultiset_bipartite (m n : ℕ) :
    degMultiset (bipartite m n) = Multiset.replicate m n + Multiset.replicate n m := by
  rw [bipartite_eq_join, degMultiset_join, degMultiset_empty, degMultiset_empty, V_empty, V_empty,
    Multiset.map_replicate, Multiset.map_replicate]
  simp

@[simp] theorem degMultiset_star (n : ℕ) :
    degMultiset (star n) = n ::ₘ Multiset.replicate n 1 := by
  rw [star_eq_bipartite, degMultiset_bipartite, Multiset.replicate_one, Multiset.singleton_add]

@[simp] theorem degMultiset_wheel (n : ℕ) :
    degMultiset (wheel (n + 3)) = (n + 3) ::ₘ Multiset.replicate (n + 3) 3 := by
  rw [wheel_eq_join, degMultiset_join, degMultiset_complete, degMultiset_cycle, V_complete,
    V_cycle, Multiset.map_replicate, Multiset.map_replicate,
    show 1 - 1 + (n + 3) = n + 3 from by omega, show 2 + 1 = 3 from rfl,
    Multiset.replicate_one, Multiset.singleton_add]

@[simp] theorem degMultiset_book (n : ℕ) :
    degMultiset (book n) = Multiset.replicate 2 (n + 1) + Multiset.replicate n 2 := by
  rw [book_eq_join, degMultiset_join, degMultiset_complete, degMultiset_empty, V_complete,
    V_empty, Multiset.map_replicate, Multiset.map_replicate,
    show 2 - 1 + n = n + 1 from by omega, Nat.zero_add]

/-! ### The degrees of a path

The path is the first named graph whose degrees are not all equal, so it is the first whose degree
multiset needs `degMultiset_path` rather than the strong-regularity machinery.  Sorting the
resulting multiset is easy enough that the degree *sequence* comes out too. -/

theorem degMultiset_path_eq (n : ℕ) :
    degMultiset (path n)
      = (Multiset.range n).map fun k ↦ (if k + 1 < n then 1 else 0) + (if 0 < k then 1 else 0) :=
  CGraph.degMultiset_path n

@[simp] theorem degMultiset_path (n : ℕ) :
    degMultiset (path (n + 2)) = 1 ::ₘ 1 ::ₘ Multiset.replicate n 2 := by
  rw [degMultiset_path_eq]
  set g : ℕ → ℕ := fun k ↦ (if k + 1 < n + 2 then 1 else 0) + (if 0 < k then 1 else 0) with hg
  have hmid : ∀ m, m ≤ n → (Multiset.range (m + 1)).map g = 1 ::ₘ Multiset.replicate m 2 := by
    intro m
    induction m with
    | zero => intro _; simp [hg]
    | succ p ih =>
      intro hp
      have hgp : g (p + 1) = 2 := by simp only [hg]; split_ifs <;> omega
      rw [Multiset.range_succ, Multiset.map_cons, ih (by omega), hgp, Multiset.cons_swap,
        ← Multiset.replicate_succ]
  have hgn : g (n + 1) = 1 := by simp only [hg]; split_ifs <;> omega
  rw [Multiset.range_succ, Multiset.map_cons, hmid n le_rfl, hgn]

/-- Sorting a multiset whose sorted form we can guess. -/
private theorem sort_eq_of_pairwise {s : Multiset ℕ} {l : List ℕ} (hl : l.Pairwise (· ≤ ·))
    (h : (l : Multiset ℕ) = s) : s.sort (· ≤ ·) = l :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba ↦ le_antisymm hab hba)
    (Multiset.pairwise_sort s (· ≤ ·)) hl
    (Multiset.coe_eq_coe.mp (by rw [Multiset.sort_eq, h]))

@[simp] theorem degSequence_path (n : ℕ) :
    degSequence (path (n + 2)) = 1 :: 1 :: List.replicate n 2 := by
  rw [degSequence_eq_sort]
  refine sort_eq_of_pairwise ?_ ?_
  · simp [List.pairwise_cons, List.mem_replicate]
  · rw [degMultiset_path]
    rfl

/-- The sorted form of a multiset made of `m` copies of a small value `a` and a list `l` of larger
ones.  This is exactly the shape of the degree multisets of the join-built families: a large hub
and a lot of small vertices. -/
private theorem sort_replicate_append {m a : ℕ} {l : List ℕ} (hl : l.Pairwise (· ≤ ·))
    (hab : ∀ x ∈ List.replicate m a, ∀ b ∈ l, x ≤ b) :
    ((l : Multiset ℕ) + Multiset.replicate m a).sort (· ≤ ·) = List.replicate m a ++ l := by
  refine sort_eq_of_pairwise ?_ ?_
  · exact List.pairwise_append.2 ⟨List.pairwise_replicate.2 (Or.inr le_rfl), hl, hab⟩
  · rw [← Multiset.coe_add, Multiset.coe_replicate, add_comm]

@[simp] theorem degSequence_star (n : ℕ) :
    degSequence (star n) = List.replicate n 1 ++ [n] := by
  rw [degSequence_eq_sort, degMultiset_star, ← Multiset.singleton_add,
    show ({n} : Multiset ℕ) = (([n] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (List.pairwise_singleton _ _) fun x hx b hb ↦ ?_
  have hx' := List.eq_of_mem_replicate hx
  have hn := List.ne_nil_of_mem hx
  rw [List.mem_singleton] at hb
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0] at hn
  · omega

@[simp] theorem degSequence_wheel (n : ℕ) :
    degSequence (wheel (n + 3)) = List.replicate (n + 3) 3 ++ [n + 3] := by
  rw [degSequence_eq_sort, degMultiset_wheel, ← Multiset.singleton_add,
    show ({n + 3} : Multiset ℕ) = (([n + 3] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (List.pairwise_singleton _ _) fun x hx b hb ↦ ?_
  rw [List.eq_of_mem_replicate hx, List.mem_singleton] at *
  omega

@[simp] theorem degSequence_book (n : ℕ) :
    degSequence (book n) = List.replicate n 2 ++ [n + 1, n + 1] := by
  rw [degSequence_eq_sort, degMultiset_book,
    show Multiset.replicate 2 (n + 1) = (([n + 1, n + 1] : List ℕ) : Multiset ℕ) from rfl]
  refine sort_replicate_append (by simp [List.pairwise_cons]) fun x hx b hb ↦ ?_
  have hx' := List.eq_of_mem_replicate hx
  have hn := List.ne_nil_of_mem hx
  have hb' : b = n + 1 := by simpa using hb
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · simp [hn0] at hn
  · omega

/-! ### Degree multisets of the four products

The vertex set of a product is a product, so its degree multiset is a `Multiset.bind`: run over
the degrees of the left factor, and for each of them map the degrees of the right factor through
whatever the product does to a pair of degrees. -/

@[simp] theorem degMultiset_cartesianProduct (G H : IsoGraph) :
    degMultiset (cartesianProduct G H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_cartesianProduct _ _

@[simp] theorem degMultiset_tensorProduct (G H : IsoGraph) :
    degMultiset (tensorProduct G H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_tensorProduct _ _

@[simp] theorem degMultiset_lexProduct (G H : IsoGraph) :
    degMultiset (lexProduct G H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ d * H.V + e := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk, V_mk]
  exact CGraph.degMultiset_lexProduct _ _

@[simp] theorem degMultiset_strongProduct (G H : IsoGraph) :
    degMultiset (strongProduct G H)
      = (degMultiset G).bind fun d ↦ (degMultiset H).map fun e ↦ (d + 1) * (e + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, degMultiset_mk,
    degMultiset_mk, degMultiset_mk]
  exact CGraph.degMultiset_strongProduct _ _

/-! ### The chromatic number of an `IsoGraph` -/

theorem chromNum_le_V (G : IsoGraph) : G.chromNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, V_mk]
  exact CGraph.chromNum_le_card _

/-- **`ω(G) ≤ χ(G)`.** -/
theorem cliqueNum_le_chromNum (G : IsoGraph) : G.cliqueNum ≤ G.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_le_chromNum _

theorem isBipartite_iff_chromNum_le_two {G : IsoGraph} : IsBipartite G ↔ G.chromNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, isBipartite_mk]
  exact CGraph.isBipartite_iff_chromNum_le_two

/-- **A graph is 2-chromatic exactly when it is bipartite and has an edge.**  With the tables of
`IsBipartite` and of `E` above, this settles the chromatic number of every bipartite graph in
the file. -/
theorem chromNum_eq_two_iff {G : IsoGraph} : G.chromNum = 2 ↔ IsBipartite G ∧ 0 < G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, isBipartite_mk, E_mk]
  exact CGraph.chromNum_eq_two_iff

@[simp] theorem chromNum_eq_zero_iff {G : IsoGraph} : G.chromNum = 0 ↔ G.V = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, V_mk]
  exact CGraph.chromNum_eq_zero_iff

theorem three_le_chromNum {G : IsoGraph} (h : ¬ IsBipartite G) : 3 ≤ G.chromNum := by
  rw [isBipartite_iff_chromNum_le_two] at h; omega

/-- Two graphs with different chromatic numbers are different graphs. -/
theorem ne_of_chromNum_ne {G H : IsoGraph} (h : G.chromNum ≠ H.chromNum) : G ≠ H :=
  ne_of_apply_ne chromNum h

/-! Values. -/

@[simp] theorem chromNum_empty_zero : (empty 0).chromNum = 0 := CGraph.chromNum_empty_zero

@[simp] theorem chromNum_empty (n : ℕ) : (empty (n + 1)).chromNum = 1 := CGraph.chromNum_empty n

@[simp] theorem chromNum_complete (n : ℕ) : (complete n).chromNum = n := CGraph.chromNum_complete n

@[simp] theorem chromNum_path (n : ℕ) : (path (n + 2)).chromNum = 2 := CGraph.chromNum_path n

@[simp] theorem chromNum_cycle_even (m : ℕ) : (cycle (2 * m + 2)).chromNum = 2 :=
  CGraph.chromNum_cycle_even m

@[simp] theorem chromNum_cycle_odd (m : ℕ) : (cycle (2 * m + 3)).chromNum = 3 :=
  CGraph.chromNum_cycle_odd m

@[simp] theorem chromNum_disjUnion (G H : IsoGraph) :
    (disjUnion G H).chromNum = max G.chromNum H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  exact CGraph.chromNum_disjUnion g h

theorem chromNum_tensorProduct_le (G H : IsoGraph) :
    (tensorProduct G H).chromNum ≤ min G.chromNum H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.chromNum_tensorProduct_le _ _

/-! Derived chromatic numbers: everything bipartite with an edge. -/

@[simp] theorem chromNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_bipartite _ _, by rw [E_bipartite]; positivity⟩

@[simp] theorem chromNum_star (n : ℕ) : (star (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_star _, by rw [E_star]; omega⟩

/-- **The hypercube `Q_{n+1}` is 2-chromatic.** -/
@[simp] theorem chromNum_hypercube (n : ℕ) : (hypercube (n + 1)).chromNum = 2 := by
  refine chromNum_eq_two_iff.2 ⟨isBipartite_hypercube _, ?_⟩
  have h := E_hypercube (n + 1)
  have hp : 0 < (n + 1) * 2 ^ (n + 1) := Nat.mul_pos n.succ_pos (Nat.two_pow_pos _)
  omega

@[simp] theorem chromNum_ladder (n : ℕ) : (ladder (n + 1)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_ladder _, by rw [E_ladder]; omega⟩

@[simp] theorem chromNum_prism_even (m : ℕ) : (prism (2 * m + 4)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨by rw [show 2 * m + 4 = 2 * (m + 2) by ring]; exact isBipartite_prism_even _,
    by rw [show 2 * m + 4 = (2 * m + 1) + 3 by ring, E_prism]; omega⟩

/-- **A grid is 2-chromatic.** -/
@[simp] theorem chromNum_grid (m n : ℕ) :
    (cartesianProduct (path (m + 2)) (path (n + 2))).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_cartesianProduct (isBipartite_path _) (isBipartite_path _),
    by rw [E_cartesianProduct, E_path, E_path, V_path, V_path]; positivity⟩

/-! ### The chromatic number of a join and of the products -/

/-- **The chromatic numbers of a join add.** -/
@[simp] theorem chromNum_join (G H : IsoGraph) :
    (join G H).chromNum = G.chromNum + H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, chromNum_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_join _ _

/-- **Sabidussi's theorem** for the cartesian product. -/
theorem chromNum_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (cartesianProduct G H).chromNum = max G.chromNum H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, chromNum_mk, chromNum_mk, chromNum_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.chromNum_cartesianProduct _ _ a b

/-- **The lexicographic product multiplies chromatic numbers, at worst.** -/
theorem chromNum_lexProduct_le (G H : IsoGraph) :
    (lexProduct G H).chromNum ≤ G.chromNum * H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.chromNum_lexProduct_le _ _

/-- **`|V| ≤ χ·α`**: the colour classes are independent sets and they cover the graph. -/
theorem V_le_chromNum_mul_indepNum (G : IsoGraph) : G.V ≤ G.chromNum * G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, indepNum_mk, V_mk]
  exact CGraph.card_le_chromNum_mul_indepNum _

/-- One colour is enough exactly when there is a vertex but no edge. -/
theorem chromNum_eq_one_iff {G : IsoGraph} : G.chromNum = 1 ↔ G.E = 0 ∧ 0 < G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, E_mk, V_mk]
  exact CGraph.chromNum_eq_one_iff

/-! ### Complete multipartite graphs -/

/-- **A complete multipartite graph needs one colour per nonempty part.** -/
@[simp] theorem chromNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).chromNum = (ds.map fun d ↦ min d 1).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [completeMultipartite_cons, chromNum_join, ih, List.map_cons, List.sum_cons]
    cases d with
    | zero => simp
    | succ k => rw [chromNum_empty, Nat.min_eq_right (by omega)]

@[simp] theorem chromNum_cocktailParty (n : ℕ) : (cocktailParty n).chromNum = n := by
  show (completeMultipartite (List.replicate n 2)).chromNum = n
  rw [chromNum_completeMultipartite, List.map_replicate]
  simp

@[simp] theorem chromNum_book (n : ℕ) : (book (n + 1)).chromNum = 3 := by
  show (completeMultipartite [1, 1, n + 1]).chromNum = 3
  rw [chromNum_completeMultipartite]
  simp

@[simp] theorem chromNum_wheel_even (m : ℕ) : (wheel (2 * m + 4)).chromNum = 3 := by
  rw [wheel_eq_join, chromNum_join, chromNum_complete,
    show 2 * m + 4 = 2 * (m + 1) + 2 by ring, chromNum_cycle_even]

@[simp] theorem chromNum_wheel_odd (m : ℕ) : (wheel (2 * m + 3)).chromNum = 4 := by
  rw [wheel_eq_join, chromNum_join, chromNum_complete, chromNum_cycle_odd]

/-! ### The Mycielskian and the Kneser bound -/

/-- **Mycielski's construction raises the chromatic number by exactly one.** -/
@[simp] theorem chromNum_mycielskian (G : IsoGraph) :
    (mycielskian G).chromNum = G.chromNum + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, mycielskian_mk, chromNum_mk, chromNum_mk]
  exact CGraph.chromNum_mycielskian _

/-- **`χ(K(n, k)) ≤ n - 2k + 2`.** -/
theorem chromNum_kneser_le (n k : ℕ) (hk : 0 < k) :
    (kneser n k).chromNum ≤ n - 2 * k + 2 := CGraph.chromNum_kneser_le n k hk

/-- **The Petersen graph is 3-chromatic**: the Kneser bound gives three colours, and it is not
bipartite. -/
@[simp] theorem chromNum_petersen : petersen.chromNum = 3 :=
  le_antisymm (chromNum_kneser_le 5 2 (by norm_num)) (three_le_chromNum not_isBipartite_petersen)

/-- **Nordhaus–Gaddum, product form**: `|V| ≤ χ(G)·χ(Gᶜ)`, since an independent set of `G` is a
clique of `Gᶜ`. -/
theorem V_le_chromNum_mul_chromNum_compl (G : IsoGraph) :
    G.V ≤ G.chromNum * (compl G).chromNum :=
  le_trans (V_le_chromNum_mul_indepNum G)
    (Nat.mul_le_mul_left _ (by rw [← cliqueNum_compl]; exact cliqueNum_le_chromNum _))

/- The Grötzsch graph: triangle-free and 4-chromatic. -/
example : (mycielskian (cycle 5)).chromNum = 4 := by
  rw [chromNum_mycielskian, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (mycielskian (mycielskian (cycle 5))).chromNum = 5 := by
  rw [chromNum_mycielskian, chromNum_mycielskian,
    show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (kneser 7 3).chromNum ≤ 3 := by
  have h := chromNum_kneser_le 7 3 (by norm_num)
  omega

/- The complement of the Petersen graph is the triangular graph `T(5)`, which needs five colours;
the product bound is tight here. -/
example : 10 ≤ 3 * (compl petersen).chromNum := by
  have h := V_le_chromNum_mul_chromNum_compl petersen
  rwa [V_petersen, chromNum_petersen] at h

/-! ### Girth -/

theorem girth_eq_zero_iff {G : IsoGraph} : G.girth = 0 ↔ IsAcyclic G := by
  induction G using Quotient.inductionOn with | _ G => exact CGraph.girth_eq_zero_iff G

theorem three_le_girth {G : IsoGraph} (h : ¬ IsAcyclic G) : 3 ≤ G.girth := by
  induction G using Quotient.inductionOn with | _ G => exact CGraph.three_le_girth h

theorem girth_eq_three_iff {G : IsoGraph} : G.girth = 3 ↔ 3 ≤ G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ G => exact CGraph.girth_eq_three_iff

theorem girth_eq_three_of_cliqueNum {G : IsoGraph} (h : 3 ≤ G.cliqueNum) : G.girth = 3 :=
  girth_eq_three_iff.2 h

theorem four_le_girth_of_cliqueNum {G : IsoGraph} (hcl : G.cliqueNum ≤ 2) (h : ¬ IsAcyclic G) :
    4 ≤ G.girth := by
  have h3 := three_le_girth h
  have hne : G.girth ≠ 3 := fun hg ↦ by have := girth_eq_three_iff.1 hg; omega
  omega

theorem four_le_girth_of_isBipartite {G : IsoGraph} (hb : IsBipartite G) (h : ¬ IsAcyclic G) :
    4 ≤ G.girth := by
  induction G using Quotient.inductionOn with | _ G =>
  exact CGraph.four_le_girth_of_isBipartite hb h

theorem two_le_cliqueNum_of_E_pos {G : IsoGraph} (h : 0 < G.E) : 2 ≤ G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ G => exact CGraph.two_le_cliqueNum_of_E_pos h

theorem one_le_cliqueNum {G : IsoGraph} (h : 0 < G.V) : 1 ≤ G.cliqueNum := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [V_mk] at h
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 h
  exact CGraph.one_le_cliqueNum_of_vertex a

theorem ne_of_girth_ne {G H : IsoGraph} (h : G.girth ≠ H.girth) : G ≠ H := fun hgh ↦ h (hgh ▸ rfl)

/-! ### Girth of the named graphs -/

@[simp] theorem girth_empty (n : ℕ) : (empty n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_empty n)

@[simp] theorem girth_path (n : ℕ) : (path n).girth = 0 := girth_eq_zero_iff.2 (isAcyclic_path n)

@[simp] theorem girth_star (n : ℕ) : (star n).girth = 0 :=
  girth_eq_zero_iff.2 ((isTree_iff_isConnected_and_isAcyclic _).1 (isTree_star n)).2

@[simp] theorem girth_complete (n : ℕ) : (complete (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_cocktailParty (n : ℕ) : (cocktailParty (n + 3)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_book (n : ℕ) : (book (n + 1)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by simp)

@[simp] theorem girth_wheel (n : ℕ) : (wheel (n + 3)).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [wheel_eq_join, cliqueNum_join]
  have : 2 ≤ (cycle (n + 3)).cliqueNum := two_le_cliqueNum_of_E_pos (by simp)
  simp only [cliqueNum_complete]
  omega

@[simp] theorem girth_cycle_three : (cycle 3).girth = 3 := by
  rw [cycle_three]; exact girth_complete 0

theorem girth_join_left {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.V) :
    (join G H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_join]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 1 ≤ H.cliqueNum := one_le_cliqueNum hH
  omega

theorem girth_join_right {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.E) :
    (join G H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_join]
  have h1 : 1 ≤ G.cliqueNum := one_le_cliqueNum hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  omega

/-- **A Cartesian product of two bipartite graphs with an edge each has girth four.** -/
theorem girth_cartesianProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E)
    (hbG : IsBipartite G) (hbH : IsBipartite H) : (cartesianProduct G H).girth = 4 := by
  induction G using Quotient.inductionOn with | _ G =>
  induction H using Quotient.inductionOn with | _ H =>
  rw [← mk_canonicalize G, ← mk_canonicalize H] at *
  rw [cartesianProduct_mk, girth_mk]
  rw [E_mk] at hG hH
  rw [isBipartite_mk] at hbG hbH
  exact CGraph.girth_cartesianProduct hG hH hbG hbH

@[simp] theorem girth_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).girth = 4 := by
  rw [bipartite_def, girth_mk]
  exact CGraph.girth_bipartite m n

@[simp] theorem girth_hypercube (n : ℕ) : (hypercube (n + 2)).girth = 4 := by
  rw [hypercube_succ]
  refine girth_cartesianProduct ?_ (by simp) (isBipartite_hypercube (n + 1)) isBipartite_complete_two
  have h := E_hypercube (n + 1)
  have : 0 < (n + 1) * 2 ^ (n + 1) := by positivity
  omega

@[simp] theorem girth_cycle_four : (cycle 4).girth = 4 := by
  rw [← hypercube_two]; exact girth_hypercube 0

@[simp] theorem girth_ladder (n : ℕ) : (ladder (n + 2)).girth = 4 :=
  girth_cartesianProduct (by simp) (by simp) (isBipartite_path (n + 2)) isBipartite_complete_two

@[simp] theorem girth_cycle_five : (cycle 5).girth = 5 := by
  rw [cycle_def, girth_mk]; exact CGraph.girth_cycle_five

theorem girth_rook {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : 3 ≤ max m n) :
    (rook m n).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_rook hm hn]; exact h)

theorem girth_strongProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    (strongProduct G H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_strongProduct]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  calc 3 ≤ 2 * 2 := by norm_num
    _ ≤ G.cliqueNum * H.cliqueNum := Nat.mul_le_mul h1 h2

theorem girth_lexProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    (lexProduct G H).girth = 3 := by
  refine girth_eq_three_of_cliqueNum ?_
  rw [cliqueNum_lexProduct]
  have h1 : 2 ≤ G.cliqueNum := two_le_cliqueNum_of_E_pos hG
  have h2 : 2 ≤ H.cliqueNum := two_le_cliqueNum_of_E_pos hH
  calc 3 ≤ 2 * 2 := by norm_num
    _ ≤ G.cliqueNum * H.cliqueNum := Nat.mul_le_mul h1 h2

theorem girth_prism_even (m : ℕ) : (prism (2 * m + 4)).girth = 4 := by
  have hb : IsBipartite (cycle (2 * m + 4)) := by
    have h := isBipartite_cycle_even (m + 2)
    rwa [show 2 * (m + 2) = 2 * m + 4 by ring] at h
  refine girth_cartesianProduct ?_ (by simp) hb isBipartite_complete_two
  rw [show 2 * m + 4 = (2 * m + 1) + 3 by ring, E_cycle]
  omega

@[simp] theorem girth_petersen : petersen.girth = 5 := by
  show (kneser 5 2).girth = 5
  rw [kneser_def, girth_mk]
  exact CGraph.girth_kneser_five_two

example : (rook 3 4).girth = 3 := girth_rook (by norm_num) (by norm_num) (by norm_num)

example : (wheel 7).girth = 3 := girth_wheel 4

example : (hypercube 4).girth = 4 := girth_hypercube 2

example : cycle 5 ≠ cycle 4 := ne_of_girth_ne (by simp)

example : petersen ≠ hypercube 4 := ne_of_girth_ne (by simp)

example : ¬ IsAcyclic (cycle 5) := by
  intro h
  have := girth_eq_zero_iff.2 h
  simp at this

/-! ### Maximum and minimum degree -/

/-! ### Basic API -/

theorem minDeg_le_maxDeg (G : IsoGraph) : minDeg G ≤ maxDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.minDeg_le_maxDeg _

theorem maxDeg_lt_V {G : IsoGraph} (h : 0 < G.V) : maxDeg G < G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [V_mk] at h ⊢
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 h
  exact CGraph.maxDeg_lt_card _ v

theorem maxDeg_le_of_degMultiset {G : IsoGraph} {k : ℕ} (h : ∀ d ∈ degMultiset G, d ≤ k) :
    maxDeg G ≤ k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.maxDeg_le_of_forall fun v ↦ h _ (CGraph.mem_degMultiset.2 ⟨v, rfl⟩)

theorem maxDeg_eq_of_degMultiset {G : IsoGraph} {k : ℕ} (hmem : k ∈ degMultiset G)
    (hle : ∀ d ∈ degMultiset G, d ≤ k) : maxDeg G = k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.maxDeg_eq_of_degMultiset hmem hle

theorem minDeg_eq_of_degMultiset {G : IsoGraph} {k : ℕ} (hmem : k ∈ degMultiset G)
    (hle : ∀ d ∈ degMultiset G, k ≤ d) : minDeg G = k := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.minDeg_eq_of_degMultiset hmem hle

/-- A regular graph, read off its degree multiset: both extremes are the common degree. -/
theorem maxDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : maxDeg G = k :=
  maxDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ le_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

theorem minDeg_of_degMultiset_replicate {G : IsoGraph} {n k : ℕ} (hn : 0 < n)
    (h : degMultiset G = Multiset.replicate n k) : minDeg G = k :=
  minDeg_eq_of_degMultiset (h ▸ Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)
    fun _ hd ↦ ge_of_eq (Multiset.eq_of_mem_replicate (h ▸ hd))

/-- The maximum degree is the largest entry of the degree multiset. -/
theorem maxDeg_eq_sup (G : IsoGraph) : maxDeg G = (degMultiset G).sup := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.maxDeg_eq_sup _

/-- **The handshake bounds**: `|V|·δ ≤ 2|E| ≤ |V|·Δ`. -/
theorem V_mul_minDeg_le (G : IsoGraph) : G.V * minDeg G ≤ 2 * G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, minDeg_mk, E_mk]
  exact CGraph.card_mul_minDeg_le _

theorem two_mul_E_le_V_mul_maxDeg (G : IsoGraph) : 2 * G.E ≤ G.V * maxDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, maxDeg_mk, E_mk]
  exact CGraph.two_mul_E_le_card_mul_maxDeg _

theorem ne_of_maxDeg_ne {G H : IsoGraph} (h : maxDeg G ≠ maxDeg H) : G ≠ H :=
  ne_of_apply_ne maxDeg h

theorem ne_of_minDeg_ne {G H : IsoGraph} (h : minDeg G ≠ minDeg H) : G ≠ H :=
  ne_of_apply_ne minDeg h

/-! ### The disjoint union, the join and the complement -/

@[simp] theorem maxDeg_disjUnion (G H : IsoGraph) :
    maxDeg (disjUnion G H) = max (maxDeg G) (maxDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, disjUnion_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  exact CGraph.maxDeg_disjUnion _ _

theorem minDeg_disjUnion {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (disjUnion G H) = min (minDeg G) (minDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [disjUnion_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_disjUnion _ _ a b

theorem maxDeg_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (join G H) = max (maxDeg G + H.V) (G.V + maxDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk, V_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_join _ _ a b

theorem minDeg_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (join G H) = min (minDeg G + H.V) (G.V + minDeg H) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [join_mk, minDeg_mk, minDeg_mk, minDeg_mk, V_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_join _ _ a b

/-- **Complementation swaps the two extreme degrees.** -/
theorem maxDeg_compl {G : IsoGraph} (hG : 0 < G.V) :
    maxDeg (compl G) = G.V - 1 - minDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, maxDeg_mk, minDeg_mk, V_mk]
  rw [V_mk] at hG
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hG
  exact CGraph.maxDeg_compl _ v

theorem minDeg_compl {G : IsoGraph} (hG : 0 < G.V) :
    minDeg (compl G) = G.V - 1 - maxDeg G := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at *
  rw [compl_mk, minDeg_mk, maxDeg_mk, V_mk]
  rw [V_mk] at hG
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hG
  exact CGraph.minDeg_compl _ v

/-! ### The four products -/

theorem maxDeg_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (cartesianProduct G H) = maxDeg G + maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_cartesianProduct _ _ a b

theorem minDeg_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (cartesianProduct G H) = minDeg G + minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [cartesianProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_cartesianProduct _ _ a b

theorem maxDeg_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (tensorProduct G H) = maxDeg G * maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_tensorProduct _ _ a b

theorem minDeg_tensorProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (tensorProduct G H) = minDeg G * minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [tensorProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_tensorProduct _ _ a b

theorem maxDeg_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (lexProduct G H) = maxDeg G * H.V + maxDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_lexProduct _ _ a b

theorem minDeg_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (lexProduct G H) = minDeg G * H.V + minDeg H := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [lexProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk, V_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_lexProduct _ _ a b

theorem maxDeg_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    maxDeg (strongProduct G H) = (maxDeg G + 1) * (maxDeg H + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, maxDeg_mk, maxDeg_mk, maxDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.maxDeg_strongProduct _ _ a b

theorem minDeg_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    minDeg (strongProduct G H) = (minDeg G + 1) * (minDeg H + 1) - 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h] at *
  rw [strongProduct_mk, minDeg_mk, minDeg_mk, minDeg_mk]
  rw [V_mk] at hG hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  exact CGraph.minDeg_strongProduct _ _ a b

/-! ### The named graphs -/

@[simp] theorem maxDeg_empty (n : ℕ) : maxDeg (empty n) = 0 :=
  Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ by
    rw [degMultiset_empty] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd))

@[simp] theorem minDeg_empty (n : ℕ) : minDeg (empty n) = 0 :=
  Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (le_of_eq (maxDeg_empty n)))

@[simp] theorem maxDeg_complete (n : ℕ) : maxDeg (complete n) = n - 1 := by
  cases n with
  | zero =>
    refine Nat.le_zero.1 (maxDeg_le_of_degMultiset fun d hd ↦ ?_)
    rw [degMultiset_complete] at hd
    exact le_of_eq (Multiset.eq_of_mem_replicate hd)
  | succ m => exact maxDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem minDeg_complete (n : ℕ) : minDeg (complete n) = n - 1 := by
  cases n with
  | zero => exact Nat.le_zero.1 (le_trans (minDeg_le_maxDeg _) (by simp))
  | succ m => exact minDeg_of_degMultiset_replicate (n := m + 1) (Nat.succ_pos m) (by simp)

@[simp] theorem maxDeg_cycle (n : ℕ) : maxDeg (cycle (n + 3)) = 2 :=
  maxDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

@[simp] theorem minDeg_cycle (n : ℕ) : minDeg (cycle (n + 3)) = 2 :=
  minDeg_of_degMultiset_replicate (n := n + 3) (by omega) (by simp)

@[simp] theorem maxDeg_petersen : maxDeg petersen = 3 :=
  maxDeg_of_degMultiset_replicate (n := 10) (by omega) (by simp)

@[simp] theorem minDeg_petersen : minDeg petersen = 3 :=
  minDeg_of_degMultiset_replicate (n := 10) (by omega) (by simp)

@[simp] theorem maxDeg_star (n : ℕ) : maxDeg (star (n + 1)) = n + 1 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_star] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

@[simp] theorem minDeg_star (n : ℕ) : minDeg (star (n + 1)) = 1 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_star] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem maxDeg_wheel (n : ℕ) : maxDeg (wheel (n + 3)) = n + 3 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_wheel] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

@[simp] theorem minDeg_wheel (n : ℕ) : minDeg (wheel (n + 3)) = 3 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_wheel] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem maxDeg_path (n : ℕ) : maxDeg (path (n + 3)) = 2 := by
  refine maxDeg_eq_of_degMultiset ?_ fun d hd ↦ ?_
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path]
    simp
  · rw [show n + 3 = (n + 1) + 2 from rfl, degMultiset_path] at hd
    rcases Multiset.mem_cons.1 hd with h | h
    · omega
    rcases Multiset.mem_cons.1 h with h | h
    · omega
    · rw [Multiset.eq_of_mem_replicate h]

@[simp] theorem minDeg_path (n : ℕ) : minDeg (path (n + 2)) = 1 := by
  refine minDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_path] at hd
  rcases Multiset.mem_cons.1 hd with h | h
  · omega
  rcases Multiset.mem_cons.1 h with h | h
  · omega
  · rw [Multiset.eq_of_mem_replicate h]; omega

@[simp] theorem maxDeg_hypercube (n : ℕ) : maxDeg (hypercube n) = n := by
  induction n with
  | zero => rw [hypercube_zero, maxDeg_empty]
  | succ m ih =>
    rw [hypercube_succ, maxDeg_cartesianProduct (by simp) (by simp), ih, maxDeg_complete]

@[simp] theorem minDeg_hypercube (n : ℕ) : minDeg (hypercube n) = n := by
  induction n with
  | zero => rw [hypercube_zero, minDeg_empty]
  | succ m ih =>
    rw [hypercube_succ, minDeg_cartesianProduct (by simp) (by simp), ih, minDeg_complete]

example : maxDeg (bipartite 3 5) = 5 := by
  refine maxDeg_eq_of_degMultiset (by simp) fun d hd ↦ ?_
  rw [degMultiset_bipartite] at hd
  rcases Multiset.mem_add.1 hd with h | h
  · rw [Multiset.eq_of_mem_replicate h]
  · rw [Multiset.eq_of_mem_replicate h]; omega

example : maxDeg (rook 3 4) = 5 := by
  rw [show rook 3 4 = cartesianProduct (complete 3) (complete 4) from rfl,
    maxDeg_cartesianProduct (by simp) (by simp), maxDeg_complete, maxDeg_complete]

/- A graph with `Δ = δ` is regular, and the handshake bounds then pin down the edge count. -/
example : 2 * (petersen.E) = 30 := by
  have h1 := V_mul_minDeg_le petersen
  have h2 := two_mul_E_le_V_mul_maxDeg petersen
  rw [V_petersen, minDeg_petersen] at h1
  rw [V_petersen, maxDeg_petersen] at h2
  omega

/- The complement of the `5`-cycle is the `5`-cycle, so both extremes are `2`. -/
example : maxDeg (compl (cycle 5)) = 2 := by
  rw [maxDeg_compl (by simp)]
  simp

/-! ### Greedy colouring and Nordhaus–Gaddum -/

/-! ### Greedy colouring -/

/-- **The greedy bound** `χ ≤ Δ + 1`. -/
theorem chromNum_le_maxDeg_add_one (G : IsoGraph) : G.chromNum ≤ G.maxDeg + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, chromNum_mk, maxDeg_mk]
  exact CGraph.chromNum_le_maxDeg_add_one _

/-- A `k`-chromatic graph has a vertex of degree at least `k - 1`. -/
theorem chromNum_sub_one_le_maxDeg (G : IsoGraph) : G.chromNum - 1 ≤ G.maxDeg := by
  have := G.chromNum_le_maxDeg_add_one
  omega

/-- `|V| ≤ (Δ + 1)·α`: the independence number of a graph of bounded degree cannot be small. -/
theorem V_le_maxDeg_add_one_mul_indepNum (G : IsoGraph) :
    G.V ≤ (G.maxDeg + 1) * G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, maxDeg_mk, indepNum_mk]
  exact CGraph.card_le_maxDeg_add_one_mul_indepNum _

/-- `χ ≤ |V| - α + 1`. -/
theorem chromNum_le_V_sub_indepNum_add_one (G : IsoGraph) :
    G.chromNum ≤ G.V - G.indepNum + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, chromNum_mk, indepNum_mk]
  exact CGraph.chromNum_le_card_sub_indepNum_add_one _

theorem chromNum_add_indepNum_le_V_add_one (G : IsoGraph) :
    G.chromNum + G.indepNum ≤ G.V + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, chromNum_mk, indepNum_mk]
  exact CGraph.chromNum_add_indepNum_le_card_add_one _

/-- **Nordhaus–Gaddum, sum form**: `4·|V| ≤ (χ(G) + χ(Gᶜ))²`, i.e. `χ(G) + χ(Gᶜ) ≥ 2√|V|`.
This is the product form together with `4ab ≤ (a + b)²`. -/
theorem four_mul_V_le_chromNum_add_chromNum_compl_sq (G : IsoGraph) :
    4 * G.V ≤ (G.chromNum + (compl G).chromNum) ^ 2 := by
  have h := V_le_chromNum_mul_chromNum_compl G
  nlinarith [sq_nonneg (G.chromNum - (compl G).chromNum : ℤ)]

/-- **Nordhaus–Gaddum, sum form**: `χ(G) + χ(Gᶜ) ≤ |V| + 1`. -/
theorem chromNum_add_chromNum_compl_le_V_add_one (G : IsoGraph) :
    G.chromNum + (compl G).chromNum ≤ G.V + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, chromNum_mk, chromNum_mk, V_mk]
  exact CGraph.chromNum_add_chromNum_compl_le_card_add_one _

/-- The product counterpart of the sum bound, by AM–GM: `4·χ(G)·χ(Gᶜ) ≤ (|V| + 1)²`. -/
theorem four_mul_chromNum_mul_chromNum_compl_le (G : IsoGraph) :
    4 * (G.chromNum * (compl G).chromNum) ≤ (G.V + 1) ^ 2 := by
  have h := G.chromNum_add_chromNum_compl_le_V_add_one
  nlinarith [sq_nonneg (G.chromNum - (compl G).chromNum : ℤ)]

/-! ### The bounds at work -/

/-- The greedy bound is tight on complete graphs. -/
example (n : ℕ) : (complete (n + 1)).chromNum = (complete (n + 1)).maxDeg + 1 := by
  rw [chromNum_complete, maxDeg_complete]
  omega

/-- And on odd cycles, where two colours are not enough. -/
example : (cycle 5).chromNum = (cycle 5).maxDeg + 1 := by
  rw [show (5 : ℕ) = 2 * 1 + 3 from rfl, chromNum_cycle_odd, maxDeg_cycle]

/-- Nordhaus–Gaddum is tight on complete graphs: `n + 1 = |V| + 1`. -/
example (n : ℕ) : (complete (n + 1)).chromNum + (compl (complete (n + 1))).chromNum
    = (complete (n + 1)).V + 1 := by
  rw [compl_complete, chromNum_complete, chromNum_empty, V_complete]

/-- The complement of the Petersen graph needs at least four colours. -/
example : 4 ≤ (compl petersen).chromNum := by
  have h := V_le_chromNum_mul_chromNum_compl petersen
  rw [V_petersen, chromNum_petersen] at h
  omega

/-- Petersen has an independent set of size at least three, because it is `3`-regular. -/
example : 3 ≤ petersen.indepNum := by
  have h := V_le_maxDeg_add_one_mul_indepNum petersen
  rw [V_petersen, maxDeg_petersen] at h
  omega

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

example : IsVertexTransitive (compl petersen) := by simp
example : IsVertexTransitive (cartesianProduct (hypercube 3) (cycle 5)) :=
  (isVertexTransitive_hypercube 3).cartesianProduct (isVertexTransitive_cycle 5)
example : IsVertexTransitive (triangular 5) := by simp

example : IsSRGWith (rook 3 3) 9 4 1 2 := isSRGWith_rook 3
example : IsSRGWith (triangular 5) 10 6 3 4 := isSRGWith_triangular 5 (by norm_num)
example : IsSRGWith (cocktailParty 4) 8 6 4 6 := isSRGWith_cocktailParty 4
example : IsSRGWith (bipartite 3 3) 6 3 0 3 := isSRGWith_bipartite 3
example : IsSRGWith (compl petersen) 10 6 3 4 := isSRGWith_petersen.compl

example : (degSequence (complete 5)).sum = 20 := by
  rw [sum_degSequence, E_complete]
  rfl

example : (degSequence petersen).length = 10 := by rw [degSequence_petersen]; rfl

example : petersen.E = 15 := by have := isSRGWith_petersen.two_mul_E; omega

example : (rook 3 3).E = 18 := by have := (isSRGWith_rook 3).two_mul_E; omega

example : degSequence (cocktailParty 3) = [4, 4, 4, 4, 4, 4] := by
  rw [degSequence_cocktailParty]
  rfl

example : (compl petersen).E = 30 := by
  rw [E_compl_eq, V_petersen]
  have h : (10 : ℕ).choose 2 = 45 := rfl
  have := isSRGWith_petersen.two_mul_E
  omega

example : (lineGraph petersen).E = 30 := by
  rw [isSRGWith_petersen.E_lineGraph]
  rfl

example : (lineGraph (complete 5)).E = 30 := by simp [Nat.choose]

example : (triangular 5).E = 30 := by simp [Nat.choose]

example (G : IsoGraph) (h : G.V = 5) (h2 : G.E = 4) : (compl G).E = 6 := by
  rw [E_compl_eq, h, h2]
  rfl

example : degSequence (rook 3 3) = List.replicate 9 4 := by simp

example : 2 * (kneser 5 2).E = 30 := by
  rw [two_mul_E_kneser 5 (k := 2) (by norm_num)]
  rfl

example : (fan 4).V = 5 := by simp

example : (cocktailParty 4).V = 8 := by simp

example : (triangular 5).V = 10 := by simp [Nat.choose]

example : degSequence (hypercube 3) = List.replicate 8 3 := by simp

example : degSequence (tensorProduct (complete 3) (complete 4)) = List.replicate 12 6 := by
  rw [degSequence_tensorProduct (degSequence_complete 3) (degSequence_complete 4)]

example : degSequence (strongProduct (complete 2) (complete 2)) = List.replicate 4 3 := by
  rw [degSequence_strongProduct (degSequence_complete 2) (degSequence_complete 2)]

example : 2 * (hypercube 4).E = 64 := by rw [two_mul_E_hypercube]; rfl

example : degSequence (cycle 5) = List.replicate 5 2 := by simp

example : degSequence (prism 3) = List.replicate 6 3 := by simp

example : (lineGraph (cycle 6)).E = 6 := by simp

example (G : IsoGraph) (h : IsVertexTransitive G) (hV : G.V = 7) (hE : G.E = 14) :
    degSequence G = List.replicate 7 4 := by
  have := degSequence_of_isVertexTransitive (k := 4) h (by omega) (by omega)
  rwa [hV] at this

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

example : complete 3 ≠ complete 4 := by simp

example : cycle 4 ≠ complete 4 :=
  ne_of_E_ne (by rw [show (4 : ℕ) = 1 + 3 from rfl, E_cycle, E_complete]; decide)

example : complete 5 ≠ cycle 5 :=
  ne_of_degSequence_ne (by
    rw [degSequence_complete, show (5 : ℕ) = 2 + 3 from rfl, degSequence_cycle]
    decide)

/-- The six-cycle and two triangles share their order, size and degree sequence; connectivity
tells them apart. -/
example : cycle 6 ≠ disjUnion (cycle 3) (cycle 3) :=
  ne_of_isConnected (isConnected_cycle 5) (not_isConnected_disjUnion (by simp) (by simp))

example : cycle 6 ≠ disjUnion (complete 3) (complete 3) :=
  ne_of_indepNum_ne (by
    rw [show (6 : ℕ) = 3 + 3 from rfl, indepNum_cycle, indepNum_disjUnion, indepNum_complete]
    decide)

/-- The triangular prism and `K₃,₃` are both cubic on six vertices; bipartiteness separates
them. -/
example : prism 3 ≠ bipartite 3 3 :=
  (ne_of_isBipartite (isBipartite_bipartite 3 3) (not_isBipartite_prism_odd 0)).symm

example : path 5 ≠ cycle 5 := path_ne_cycle 4 2

example : petersen ≠ cycle 10 :=
  ne_of_degSequence_ne (by
    rw [degSequence_petersen, show (10 : ℕ) = 7 + 3 from rfl, degSequence_cycle]
    decide)

example : disjUnion (complete 3) (empty 1) ≠ star 3 :=
  ne_of_cliqueNum_ne (by
    rw [cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_empty,
      show (3 : ℕ) = 2 + 1 from rfl, cliqueNum_star]
    decide)

/-- The cube and two disjoint copies of `K₄` are both cubic on eight vertices with twelve
edges. -/
example : hypercube 3 ≠ disjUnion (complete 4) (complete 4) :=
  ne_of_isConnected (isConnected_hypercube 3) (not_isConnected_disjUnion (by simp) (by simp))

example : complete 4 ≠ path 4 :=
  ne_of_diameter_ne (by
    rw [show (4 : ℕ) = 2 + 2 from rfl, diameter_complete, show (2 + 2 : ℕ) = 3 + 1 from rfl,
      diameter_path]
    decide)

example (G : IsoGraph) (h : G.V = 5) : G ≠ petersen := ne_of_V_ne (by rw [h, V_petersen]; decide)

example : petersen.diameter = 2 := by simp

example : (rook 3 3).diameter = 2 := diameter_rook 1 1

example : (cocktailParty 5).diameter = 2 := diameter_cocktailParty 3

example : (triangular 5).diameter = 2 := diameter_triangular (by norm_num)

/-- The Petersen graph is not the 10-cycle: their diameters (and degree sequences) differ. -/
example : petersen ≠ cycle 10 :=
  ne_of_diameter_ne (by
    rw [diameter_petersen, show (10 : ℕ) = 9 + 1 from rfl, diameter_cycle]
    decide)

example : (star 5).diameter = 2 := by simp

example : (wheel 6).diameter = 2 := by simp

example : (fan 5).diameter = 2 := diameter_fan 1

example : (book 4).diameter = 2 := by simp

/-- The star and the path on four vertices have the same order, size and edge count, and both are
trees; the diameter is what tells them apart. -/
example : star 3 ≠ path 4 :=
  ne_of_diameter_ne (by
    rw [show (3 : ℕ) = 1 + 2 from rfl, diameter_star, show (4 : ℕ) = 3 + 1 from rfl, diameter_path]
    decide)

example : IsConnected (compl (disjUnion (complete 3) (complete 3))) := by simp

example : (compl (disjUnion (complete 3) (complete 3))).diameter = 2 :=
  diameter_compl_disjUnion (by simp) (by simp) (by simp [Nat.choose])

example : IsConnected (compl (empty 5)) := by
  rw [compl_empty]
  exact isConnected_complete 4

/- A disconnected graph and a connected one of the same order and size: the six-cycle against
two triangles, once more. -/
example : ¬ IsConnected (disjUnion (cycle 3) (cycle 3)) :=
  not_isConnected_disjUnion (by simp) (by simp)

example : degMultiset (star 4) = {4, 1, 1, 1, 1} := by
  rw [degMultiset_star]
  rfl

example : degMultiset (wheel 4) = {4, 3, 3, 3, 3} := by
  rw [show (4 : ℕ) = 1 + 3 from rfl, degMultiset_wheel]
  rfl

/- The complement of the five-cycle is a five-cycle, degree by degree. -/
example : degMultiset (compl (cycle 5)) = Multiset.replicate 5 2 := by
  rw [compl_cycle_five, show (5 : ℕ) = 2 + 3 from rfl, degMultiset_cycle]

example : star 4 ≠ cycle 4 :=
  ne_of_degMultiset_ne (by
    rw [degMultiset_star, show (4 : ℕ) = 1 + 3 from rfl, degMultiset_cycle]
    decide)

/- The degree multiset does not separate everything: a triangle plus a square has the same
degrees as the seven-cycle, and only connectivity tells them apart. -/
example : degMultiset (disjUnion (cycle 3) (cycle 4)) = degMultiset (cycle 7) := by
  rw [show (3 : ℕ) = 0 + 3 from rfl, show (4 : ℕ) = 1 + 3 from rfl, degMultiset_disjUnion,
    degMultiset_cycle, degMultiset_cycle, show (7 : ℕ) = 4 + 3 from rfl, degMultiset_cycle]
  rfl

example : disjUnion (cycle 3) (cycle 4) ≠ cycle 7 :=
  Ne.symm (ne_of_isConnected (isConnected_cycle 6)
    (not_isConnected_disjUnion (G := cycle 3) (H := cycle 4) (by simp) (by simp)))

example : degSequence (path 5) = [1, 1, 2, 2, 2] := degSequence_path 3

example : degMultiset (path 2) = {1, 1} := degMultiset_path 0

/- The star and the path on four vertices: same order, same size, both trees, and now separated
by the degree multiset as well as by the diameter. -/
example : star 3 ≠ path 4 :=
  ne_of_degMultiset_ne (by
    have h1 : degMultiset (star 3) = 3 ::ₘ Multiset.replicate 3 1 := degMultiset_star 3
    have h2 : degMultiset (path 4) = 1 ::ₘ 1 ::ₘ Multiset.replicate 2 2 := degMultiset_path 2
    rw [h1, h2]
    decide)

example : degSequence (star 4) = [1, 1, 1, 1, 4] := degSequence_star 4

example : degSequence (wheel 5) = [3, 3, 3, 3, 3, 5] := degSequence_wheel 2

example : degSequence (book 3) = [2, 2, 2, 4, 4] := degSequence_book 3

/- The three-rung ladder: the four corners have degree two and the two middle vertices degree
three. -/
example : degMultiset (ladder 3) = {2, 2, 3, 3, 2, 2} := by
  have h1 : degMultiset (path 3) = 1 ::ₘ 1 ::ₘ Multiset.replicate 1 2 := degMultiset_path 1
  have h2 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  rw [show ladder 3 = cartesianProduct (path 3) (complete 2) from rfl,
    degMultiset_cartesianProduct, h1, h2]
  decide

/- A star times an edge, in the lexicographic product: the hub sees everything. -/
example : degMultiset (lexProduct (complete 2) (empty 3)) = Multiset.replicate 6 3 := by
  have h1 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  have h2 : degMultiset (empty 3) = Multiset.replicate 3 0 := degMultiset_empty 3
  rw [degMultiset_lexProduct, h1, h2, V_empty]
  decide

/- The tensor product multiplies degrees, so each row of `K₃ × P₃` repeats the path's degrees
scaled by two. -/
example : degMultiset (tensorProduct (complete 3) (path 3)) = {2, 4, 2, 2, 4, 2, 2, 4, 2} := by
  have h1 : degMultiset (complete 3) = Multiset.replicate 3 2 := degMultiset_complete 3
  have h2 : degMultiset (path 3) = 1 ::ₘ 1 ::ₘ Multiset.replicate 1 2 := degMultiset_path 1
  rw [degMultiset_tensorProduct, h1, h2]
  decide

/- `K₂ ⊠ K₂` is `K₄`, and the degrees agree: `(1 + 1) * (1 + 1) - 1 = 3`. -/
example : degMultiset (strongProduct (complete 2) (complete 2)) = Multiset.replicate 4 3 := by
  have h1 : degMultiset (complete 2) = Multiset.replicate 2 1 := degMultiset_complete 2
  rw [degMultiset_strongProduct, h1]
  decide

example : path 6 ≠ cycle 6 :=
  ne_of_degMultiset_ne (by
    have h1 : degMultiset (path 6) = 1 ::ₘ 1 ::ₘ Multiset.replicate 4 2 := degMultiset_path 4
    have h2 : degMultiset (cycle 6) = Multiset.replicate 6 2 := degMultiset_cycle 3
    rw [h1, h2]
    decide)

example : (cartesianProduct (bipartite 2 3) (complete 4)).cliqueNum = 4 := by
  rw [cliqueNum_cartesianProduct (by simp) (by simp), cliqueNum_complete,
    show bipartite 2 3 = bipartite (1 + 1) (2 + 1) from rfl, cliqueNum_bipartite]
  decide

example : (rook 3 3).cliqueNum = 3 := by simp

example : (tensorProduct (complete 3) (complete 5)).cliqueNum = 3 := by simp

example : (lexProduct (complete 3) (complete 5)).cliqueNum = 15 := by simp

example : (lexProduct (empty 4) (complete 5)).cliqueNum = 5 := by simp

example : rook 3 3 ≠ lexProduct (complete 3) (complete 3) :=
  ne_of_cliqueNum_ne (by simp)

example : tensorProduct (complete 4) (complete 4) ≠ rook 3 3 :=
  ne_of_cliqueNum_ne (by simp)

example : (hypercube 4).diameter = 4 := diameter_hypercube 4

example : (ladder 5).diameter = 5 := diameter_ladder 4

example : (prism 6).diameter = 4 := diameter_prism 5

example : (rook 4 4).diameter = 2 := diameter_rook 2 2

/- `Q₄` and the `4 × 4` rook graph both have sixteen vertices and are both `4`-regular, but the
hypercube is far bigger across. -/
example : hypercube 4 ≠ rook 4 4 :=
  ne_of_diameter_ne (by rw [diameter_hypercube, diameter_rook]; decide)

example : (disjUnion (complete 3) (complete 3)).diameter = 0 :=
  diameter_disjUnion (by simp) (by simp)

example : (complete 5).chromNum = 5 := by simp
example : (cycle 8).chromNum = 2 := chromNum_cycle_even 3
example : (cycle 7).chromNum = 3 := chromNum_cycle_odd 2
example : (path 9).chromNum = 2 := by simp
example : (hypercube 4).chromNum = 2 := by simp
example : (bipartite 3 4).chromNum = 2 := by simp
example : (cartesianProduct (path 3) (path 4)).chromNum = 2 := by simp
example : (empty 7).chromNum = 1 := by simp
example : (disjUnion (complete 4) (cycle 5)).chromNum = 4 := by
  rw [chromNum_disjUnion, chromNum_complete, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]
  decide
example : (tensorProduct (cycle 3) (complete 5)).chromNum ≤ 3 := by
  refine le_trans (chromNum_tensorProduct_le _ _) ?_
  rw [show (cycle 3).chromNum = 3 from chromNum_cycle_odd 0]
  exact min_le_left _ _
/- The Petersen graph contains a 5-cycle, so two colours are not enough. -/
example : 3 ≤ petersen.chromNum := three_le_chromNum (by simp)
/- A `3 × 3` rook graph contains a triangle. -/
example : 3 ≤ (rook 3 3).chromNum := le_trans (by simp) (cliqueNum_le_chromNum _)
/- `C₃ ⊔ C₃` and `C₆` are both 2-regular on six vertices with six edges; the chromatic number
tells them apart. -/
example : disjUnion (cycle 3) (cycle 3) ≠ cycle 6 :=
  ne_of_chromNum_ne (by
    rw [chromNum_disjUnion, show (cycle 3).chromNum = 3 from chromNum_cycle_odd 0,
      show (cycle 6).chromNum = 2 from chromNum_cycle_even 2]
    decide)

example : (join (complete 3) (cycle 5)).chromNum = 6 := by
  rw [chromNum_join, chromNum_complete, show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]

example : (join (cycle 4) (cycle 4)).chromNum = 4 := by
  rw [chromNum_join, show (cycle 4).chromNum = 2 from chromNum_cycle_even 1]

example : (cartesianProduct (complete 4) (cycle 5)).chromNum = 4 := by
  rw [chromNum_cartesianProduct (by simp) (by simp), chromNum_complete,
    show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1]
  decide

example : (lexProduct (cycle 5) (complete 2)).chromNum ≤ 6 := by
  have h := chromNum_lexProduct_le (cycle 5) (complete 2)
  rw [show (cycle 5).chromNum = 3 from chromNum_cycle_odd 1, chromNum_complete] at h
  omega

/- The independence number bounds the chromatic number from below. -/
example (n : ℕ) : n + 1 ≤ (cocktailParty (n + 1)).chromNum := by
  have h := V_le_chromNum_mul_indepNum (cocktailParty (n + 1))
  rw [V_cocktailParty, indepNum_cocktailParty] at h
  omega

example : (wheel 7).chromNum = 4 := chromNum_wheel_odd 2
example : (cocktailParty 4).chromNum = 4 := by simp

/-! ### Turán's theorem -/

/-- **Turán's theorem**: `ω(G) ≤ r` forces `2r·|E| ≤ (r - 1)·|V|²`. -/
theorem two_mul_mul_E_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.cliqueNum ≤ r) :
    2 * r * G.E ≤ (r - 1) * G.V ^ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, E_mk, V_mk] at *
  rw [cliqueNum_mk] at h
  exact CGraph.two_mul_mul_E_le _ hr h

/-- **Mantel's theorem**: `4·|E| ≤ |V|²` for a triangle-free graph. -/
theorem four_mul_E_le_V_sq (G : IsoGraph) (h : G.cliqueNum ≤ 2) : 4 * G.E ≤ G.V ^ 2 := by
  have := G.two_mul_mul_E_le (r := 2) (by omega) h
  omega

/-- A graph with more than `|V|²/4` edges contains a triangle, so its girth is `3`. -/
theorem three_le_cliqueNum_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) :
    3 ≤ G.cliqueNum := by
  by_contra hcon
  exact absurd (G.four_mul_E_le_V_sq (by omega)) (by omega)

theorem girth_eq_three_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) : G.girth = 3 :=
  girth_eq_three_iff.2 (G.three_le_cliqueNum_of_V_sq_lt h)

/-- The general contrapositive of Turán: beating the Turán density forces a bigger clique. -/
theorem lt_cliqueNum_of_lt (G : IsoGraph) {r : ℕ} (hr : 0 < r)
    (h : (r - 1) * G.V ^ 2 < 2 * r * G.E) : r < G.cliqueNum := by
  by_contra hcon
  exact absurd (G.two_mul_mul_E_le hr (Nat.not_lt.1 hcon)) (by omega)

/-- Mantel's bound applies to every graph of girth at least four, and to every bipartite graph. -/
theorem four_mul_E_le_V_sq_of_girth_ne_three (G : IsoGraph) (h : G.girth ≠ 3) :
    4 * G.E ≤ G.V ^ 2 := by
  refine G.four_mul_E_le_V_sq ?_
  by_contra hcon
  exact h (girth_eq_three_iff.2 (by omega))

theorem cliqueNum_le_two_of_isBipartite {G : IsoGraph} (h : IsBipartite G) : G.cliqueNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.cliqueNum_le_two_of_isBipartite h

theorem four_mul_E_le_V_sq_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    4 * G.E ≤ G.V ^ 2 :=
  G.four_mul_E_le_V_sq (cliqueNum_le_two_of_isBipartite h)

/-! ### Turán in the complement: few independent vertices means many edges -/

/-- Turán applied to `Gᶜ`: a graph with independence number at most `r` has few *non*-edges. -/
theorem two_mul_mul_E_compl_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * (compl G).E ≤ (r - 1) * G.V ^ 2 := by
  have hV : (compl G).V = G.V := V_compl G
  have := (compl G).two_mul_mul_E_le hr (by rwa [cliqueNum_compl])
  rwa [hV] at this

/-- Consequently a graph with independence number at most `r` has *many* edges: the `Gᶜ` bound
turns into a lower bound on `G.E` through `|E(G)| + |E(Gᶜ)| = C(|V|, 2)`. -/
theorem two_mul_mul_choose_le (G : IsoGraph) {r : ℕ} (hr : 0 < r) (h : G.indepNum ≤ r) :
    2 * r * G.V.choose 2 ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := by
  have hsum := G.E_compl_add
  have hb := G.two_mul_mul_E_compl_le hr h
  calc 2 * r * G.V.choose 2 = 2 * r * (compl G).E + 2 * r * G.E := by
        rw [← Nat.mul_add, hsum]
    _ ≤ (r - 1) * G.V ^ 2 + 2 * r * G.E := Nat.add_le_add_right hb _

/-- **Mantel in the complement**: a graph with no three pairwise non-adjacent vertices has at
least `C(n, 2) - n²/4` edges. -/
theorem four_mul_choose_le (G : IsoGraph) (h : G.indepNum ≤ 2) :
    4 * G.V.choose 2 ≤ G.V ^ 2 + 4 * G.E := by
  have := G.two_mul_mul_choose_le (r := 2) (by omega) h
  omega

/-! ### Turán at work -/

/-- Mantel's bound is attained by the balanced complete bipartite graph. -/
example (m : ℕ) : 4 * (bipartite m m).E = (bipartite m m).V ^ 2 := by
  rw [E_bipartite, V_bipartite]
  ring

/-- Turán's bound is attained by the complete graph `K_r`, whose clique number is exactly `r`. -/
example (n : ℕ) :
    2 * (n + 1) * (complete (n + 1)).E = ((n + 1) - 1) * (complete (n + 1)).V ^ 2 := by
  have key : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self n
    have hc : (n + 1) * n = n * (n + 1) := Nat.mul_comm _ _
    omega
  rw [E_complete, V_complete, Nat.add_sub_cancel]
  calc 2 * (n + 1) * (n + 1).choose 2 = (n + 1) * (2 * (n + 1).choose 2) := by ring
    _ = (n + 1) * ((n + 1) * n) := by rw [key]
    _ = n * (n + 1) ^ 2 := by ring

/-- The Petersen graph is well under the Mantel threshold, as it must be: it has no triangle. -/
example : 4 * petersen.E ≤ petersen.V ^ 2 :=
  petersen.four_mul_E_le_V_sq_of_girth_ne_three (by rw [girth_petersen]; omega)

/-- Edge counting alone certifies a triangle in `K₃`. -/
example : (complete 3).girth = 3 := girth_eq_three_of_V_sq_lt _ (by simp)

/-- ... and in the triangular graph `T(5)`, which has `10` vertices and `30` edges. -/
example : (triangular 5).girth = 3 := girth_eq_three_of_V_sq_lt _ (by simp [Nat.choose])

/-- The complement bound at work on `C₅`, whose independence number is two: `40 ≤ 25 + 20`. -/
example : 4 * (cycle 5).V.choose 2 ≤ (cycle 5).V ^ 2 + 4 * (cycle 5).E :=
  four_mul_choose_le _ (by rw [show (5 : ℕ) = 2 + 3 from rfl, indepNum_cycle])

/-- Turán with `r = 2` detects that `K₄` has a clique on more than two vertices. -/
example : 2 < (complete 4).cliqueNum := lt_cliqueNum_of_lt _ (by omega) (by simp; decide)

/-! ### The Ramsey number `R(3, 3)` -/

/-- **`R(3, 3) ≤ 6`**: among any six people, three are mutual friends or three are mutual
strangers. -/
theorem three_le_cliqueNum_or_three_le_indepNum (G : IsoGraph) (h : 6 ≤ G.V) :
    3 ≤ G.cliqueNum ∨ 3 ≤ G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at h
  rw [← mk_canonicalize g, cliqueNum_mk, indepNum_mk]
  exact CGraph.three_le_cliqueNum_or_three_le_indepNum _ h

/-- A triangle-free graph on six or more vertices has independence number at least three. -/
theorem three_le_indepNum_of_cliqueNum_le_two (G : IsoGraph) (h : 6 ≤ G.V)
    (hcl : G.cliqueNum ≤ 2) : 3 ≤ G.indepNum := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · omega
  · exact h'

/-- The same for a graph of girth other than three, in particular any bipartite graph. -/
theorem three_le_indepNum_of_girth_ne_three (G : IsoGraph) (h : 6 ≤ G.V) (hg : G.girth ≠ 3) :
    3 ≤ G.indepNum := by
  refine G.three_le_indepNum_of_cliqueNum_le_two h ?_
  by_contra hcon
  exact hg (girth_eq_three_iff.2 (by omega))

theorem three_le_indepNum_of_isBipartite (G : IsoGraph) (h : 6 ≤ G.V) (hb : IsBipartite G) :
    3 ≤ G.indepNum :=
  G.three_le_indepNum_of_cliqueNum_le_two h (cliqueNum_le_two_of_isBipartite hb)

/-- Either way round: on six vertices a graph or its complement has girth three. -/
theorem girth_eq_three_or_girth_compl_eq_three (G : IsoGraph) (h : 6 ≤ G.V) :
    G.girth = 3 ∨ (compl G).girth = 3 := by
  rcases G.three_le_cliqueNum_or_three_le_indepNum h with h' | h'
  · exact Or.inl (girth_eq_three_iff.2 h')
  · exact Or.inr (girth_eq_three_iff.2 (by rwa [cliqueNum_compl]))

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

example : (cycle 5).V = 5 ∧ (cycle 5).cliqueNum < 3 ∧ (cycle 5).indepNum < 3 := by
  refine ⟨by simp, by rw [cliqueNum_cycle_five]; omega, ?_⟩
  rw [show (5 : ℕ) = 2 + 3 from rfl, indepNum_cycle]
  omega

/-- The Petersen graph, being triangle-free on ten vertices, must contain three pairwise
non-adjacent vertices. -/
example : 3 ≤ petersen.indepNum :=
  petersen.three_le_indepNum_of_girth_ne_three (by rw [V_petersen]; omega)
    (by rw [girth_petersen]; omega)

/-- So must the cube graph, which is bipartite on eight vertices. -/
example : 3 ≤ (hypercube 3).indepNum :=
  (hypercube 3).three_le_indepNum_of_isBipartite (by simp) (isBipartite_hypercube 3)

/-! ### Ramsey numbers in general -/

/-- **Ramsey's theorem**, `R(s, t) ≤ C(s + t, s)`. -/
theorem le_cliqueNum_or_le_indepNum (G : IsoGraph) {s t : ℕ} (h : (s + t).choose s ≤ G.V) :
    s ≤ G.cliqueNum ∨ t ≤ G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at h
  rw [← mk_canonicalize g, cliqueNum_mk, indepNum_mk]
  exact CGraph.le_cliqueNum_or_le_indepNum _ h

/-- The diagonal case, in the crude but memorable form `4^s` — since `C(2s, s) ≤ 2^(2s)`. -/
theorem le_cliqueNum_or_le_indepNum_of_pow (G : IsoGraph) {s : ℕ} (h : 4 ^ s ≤ G.V) :
    s ≤ G.cliqueNum ∨ s ≤ G.indepNum := by
  refine G.le_cliqueNum_or_le_indepNum (le_trans ?_ h)
  calc (s + s).choose s ≤ 2 ^ (s + s) := Nat.choose_le_two_pow _ _
    _ = 4 ^ s := by rw [← two_mul, pow_mul]; norm_num

/-- A graph on `70` vertices has four mutually adjacent or four mutually non-adjacent vertices. -/
example (G : IsoGraph) (h : 70 ≤ G.V) : 4 ≤ G.cliqueNum ∨ 4 ≤ G.indepNum :=
  G.le_cliqueNum_or_le_indepNum (by rw [show (4 : ℕ) + 4 = 8 from rfl]; simpa using h)

/-! ### The vertex cover number -/

/-- **Gallai's identity**, `τ + α = |V|`. -/
@[simp] theorem coverNum_add_indepNum (G : IsoGraph) : G.coverNum + G.indepNum = G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, coverNum_mk, indepNum_mk, V_mk]
  exact CGraph.coverNum_add_indepNum _

theorem coverNum_eq (G : IsoGraph) : G.coverNum = G.V - G.indepNum := by
  have := G.coverNum_add_indepNum
  omega

theorem indepNum_eq_V_sub_coverNum (G : IsoGraph) : G.indepNum = G.V - G.coverNum := by
  have := G.coverNum_add_indepNum
  omega

theorem coverNum_le_V (G : IsoGraph) : G.coverNum ≤ G.V := by
  have := G.coverNum_add_indepNum
  omega

/-- In the complement, Gallai reads `τ(Gᶜ) + ω(G) = |V|`. -/
theorem coverNum_compl_add_cliqueNum (G : IsoGraph) :
    (compl G).coverNum + G.cliqueNum = G.V := by
  have := (compl G).coverNum_add_indepNum
  rwa [indepNum_compl, V_compl] at this

/-! ### The vertex cover table -/

@[simp] theorem coverNum_empty (n : ℕ) : (empty n).coverNum = 0 := by
  rw [coverNum_eq, V_empty, indepNum_empty]
  omega

@[simp] theorem coverNum_complete (n : ℕ) : (complete n).coverNum = n - 1 := by
  rw [coverNum_eq, V_complete, indepNum_complete]
  omega

@[simp] theorem coverNum_cycle (n : ℕ) : (cycle (n + 3)).coverNum = (n + 3) - (n + 3) / 2 := by
  rw [coverNum_eq, V_cycle, indepNum_cycle]

@[simp] theorem coverNum_bipartite (m n : ℕ) : (bipartite m n).coverNum = min m n := by
  rw [coverNum_eq, V_bipartite, indepNum_bipartite]
  omega

@[simp] theorem coverNum_star (n : ℕ) : (star n).coverNum = min 1 n := by
  rw [star_eq_bipartite, coverNum_bipartite]

@[simp] theorem coverNum_disjUnion (G H : IsoGraph) :
    (disjUnion G H).coverNum = G.coverNum + H.coverNum := by
  rw [coverNum_eq, coverNum_eq, coverNum_eq, V_disjUnion, indepNum_disjUnion]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

@[simp] theorem coverNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).coverNum = ds.sum - (ds.max?).getD 0 := by
  rw [coverNum_eq, V_completeMultipartite, indepNum_completeMultipartite]

/-! ### Where the cover number sits among the other invariants -/

/-- **`|E| ≤ τ·Δ`**, so a graph with many edges and small degrees needs a big cover. -/
theorem E_le_coverNum_mul_maxDeg (G : IsoGraph) : G.E ≤ G.coverNum * G.maxDeg := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, E_mk, coverNum_mk, maxDeg_mk]
  exact CGraph.E_le_coverNum_mul_maxDeg _

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

/-- A vertex cover needs at most one vertex per edge. -/
@[simp] theorem coverNum_le_E (G : IsoGraph) : G.coverNum ≤ G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, E_mk, coverNum_mk]
  exact CGraph.coverNum_le_E _

/-- A graph with an edge has an independent set smaller than its whole vertex set. -/
theorem indepNum_lt_V_of_E_pos (G : IsoGraph) (h : 0 < G.E) : G.indepNum < G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, E_mk] at h
  rw [← mk_canonicalize g, indepNum_mk, V_mk]
  exact CGraph.indepNum_lt_card_of_E_pos _ h

/-- A vertex cover meets every edge, so a graph with an edge needs one, and conversely a graph
with no edges needs none. -/
theorem coverNum_pos (G : IsoGraph) (h : 0 < G.E) : 0 < G.coverNum := by
  have h1 := G.coverNum_add_indepNum
  have h2 := G.indepNum_lt_V_of_E_pos h
  omega

@[simp] theorem coverNum_eq_zero_iff (G : IsoGraph) : G.coverNum = 0 ↔ G.E = 0 := by
  constructor
  · intro h
    by_contra hcon
    exact absurd (G.coverNum_pos (by omega)) (by omega)
  · intro h
    have := G.coverNum_le_E
    omega

/-! ### The cover number at work -/

example : (cycle 6).coverNum = 3 := by rw [show (6 : ℕ) = 3 + 3 from rfl, coverNum_cycle]

example : (complete 5).coverNum = 4 := by simp

example : (bipartite 3 4).coverNum = 3 := by simp

/-- `|E| ≤ τ·Δ` is an equality on stars, where a single vertex covers everything. -/
example (n : ℕ) :
    (star (n + 1)).E = (star (n + 1)).coverNum * (star (n + 1)).maxDeg := by
  rw [E_star, maxDeg_star, coverNum_star, Nat.min_eq_left (by omega), one_mul]

/-! ### The clique–coclique bound -/

/-- **The clique–coclique bound**: `α · ω ≤ |V|` for a vertex-transitive graph.  Both factors are
maximised by the same graph only in very rigid cases; see the examples below. -/
theorem indepNum_mul_cliqueNum_le_V {G : IsoGraph} (h : IsVertexTransitive G) :
    G.indepNum * G.cliqueNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, indepNum_mk, cliqueNum_mk]
  rw [← mk_canonicalize g, isVertexTransitive_mk] at h
  exact CGraph.indepNum_mul_cliqueNum_le_card _ h

/-- Contrapositive: `α · ω > |V|` is a certificate of *non*-vertex-transitivity, and one that is
independent of the usual degree-sequence obstruction. -/
theorem not_isVertexTransitive_of_V_lt {G : IsoGraph} (h : G.V < G.indepNum * G.cliqueNum) :
    ¬ IsVertexTransitive G := fun hvt ↦ absurd (indepNum_mul_cliqueNum_le_V hvt) (by omega)

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

/-! ### Consequences for the named families -/

/-- The independence number of a rook's graph is at most `min m n`: a set of squares no two of
which share a row or a column is a partial permutation matrix.  This is the hard direction of
`α(K_m □ K_n) = min m n`, and it comes out of the clique–coclique bound because the rook's graph
is vertex-transitive with `ω = max m n`. -/
theorem indepNum_rook_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (rook m n).indepNum ≤ min m n := by
  have h := indepNum_mul_cliqueNum_le_V (isVertexTransitive_rook m n)
  rw [cliqueNum_rook hm hn, V_rook] at h
  have hmax : 0 < max m n := lt_of_lt_of_le hm (le_max_left m n)
  refine Nat.le_of_mul_le_mul_right ?_ hmax
  calc (rook m n).indepNum * max m n ≤ m * n := h
    _ = min m n * max m n := (min_mul_max m n).symm

/-- Hypercubes: an independent set in `Q_n` has at most `2^(n-1)` vertices (and the even-weight
vertices show this is sharp). -/
theorem two_mul_indepNum_hypercube_le (n : ℕ) :
    2 * (hypercube (n + 1)).indepNum ≤ 2 ^ (n + 1) := by
  have hE : 0 < (hypercube (n + 1)).E := by
    have h := E_hypercube (n + 1)
    have hpos : 0 < (n + 1) * 2 ^ (n + 1) :=
      Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
    omega
  have := two_mul_indepNum_le_V (isVertexTransitive_hypercube (n + 1)) hE
  rwa [V_hypercube] at this

/-- Kneser graphs: `α(K(n, k)) · ω(K(n, k)) ≤ C(n, k)`. -/
theorem indepNum_mul_cliqueNum_kneser_le (n k : ℕ) :
    (kneser n k).indepNum * (kneser n k).cliqueNum ≤ n.choose k := by
  have := indepNum_mul_cliqueNum_le_V (isVertexTransitive_kneser n k)
  rwa [V_kneser] at this

/-- The Petersen graph is triangle-free, so its independence number is at most `5`.
(The true value is `4`; the clique–coclique bound is off by one here.) -/
theorem indepNum_petersen_le : petersen.indepNum ≤ 5 := by
  have hE : 0 < petersen.E := by
    have h : 2 * petersen.E = 30 := by
      rw [two_mul_E_kneser 5 (k := 2) (by norm_num)]; rfl
    omega
  have := two_mul_indepNum_le_V isVertexTransitive_petersen hE
  rw [V_petersen] at this
  omega

/-- Cycles: the clique–coclique bound recovers `α(C_n) ≤ ⌊n/2⌋`. -/
theorem two_mul_indepNum_cycle_le (n : ℕ) : 2 * (cycle (n + 3)).indepNum ≤ n + 3 := by
  have hE : 0 < (cycle (n + 3)).E := by simp
  have := two_mul_indepNum_le_V (isVertexTransitive_cycle (n + 3)) hE
  rwa [V_cycle] at this

/-! Tightness: the complete graph, the cocktail-party graph and the rook's graph all meet the
bound with equality. -/

example (n : ℕ) : (complete (n + 1)).indepNum * (complete (n + 1)).cliqueNum = (complete (n + 1)).V := by
  simp

example (n : ℕ) :
    (cocktailParty (n + 1)).indepNum * (cocktailParty (n + 1)).cliqueNum
      = (cocktailParty (n + 1)).V := by
  rw [indepNum_cocktailParty, cliqueNum_cocktailParty, V_cocktailParty]

/-- The star `K_{1,3}` has `α · ω = 3 · 2 > 4 = |V|`, so it is not vertex-transitive. -/
example : ¬ IsVertexTransitive (star 3) := by
  refine not_isVertexTransitive_of_V_lt ?_
  rw [indepNum_star, cliqueNum_star, V_star]
  norm_num

/-- Unbalanced complete bipartite graphs are not vertex-transitive. -/
example (m n : ℕ) (h : m + 2 ≤ n) : ¬ IsVertexTransitive (bipartite (m + 1) (n + 1)) := by
  refine not_isVertexTransitive_of_V_lt ?_
  rw [indepNum_bipartite, cliqueNum_bipartite, V_bipartite]
  have hmax : max (m + 1) (n + 1) = n + 1 := Nat.max_eq_right (by omega)
  rw [hmax]
  omega

/-- Paley graphs are Cayley graphs of the additive group of the field, so they are
vertex-transitive. -/
@[simp] theorem isVertexTransitive_paley (q : ℕ) [NeZero q] [Fact q.Prime] :
    IsVertexTransitive (paley q) :=
  CGraph.isVertexTransitive_paley q

/-! ### Self-complementary graphs -/

/-- A self-complementary graph has as many vertices in its largest independent set as in its
largest clique. -/
theorem indepNum_eq_cliqueNum_of_compl_eq {G : IsoGraph} (h : compl G = G) :
    G.indepNum = G.cliqueNum := by
  conv_lhs => rw [← h]
  rw [indepNum_compl]

/-- A self-complementary graph owns exactly half of the possible edges. -/
theorem two_mul_E_of_compl_eq {G : IsoGraph} (h : compl G = G) : 2 * G.E = G.V.choose 2 := by
  have h1 := G.E_compl
  rw [h] at h1
  omega

private theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [Nat.choose_two_right, Nat.succ_sub_one]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    have h : (m + 1) * m = 2 * k := by rw [Nat.mul_comm]; omega
    rw [h]
    omega

/-- **A self-complementary graph has `|V| ≡ 0` or `1 (mod 4)`**: it owns half of the `C(|V|, 2)`
possible edges, so `4` divides `|V| · (|V| - 1)`. -/
theorem V_mod_four_of_compl_eq {G : IsoGraph} (h : compl G = G) :
    G.V % 4 = 0 ∨ G.V % 4 = 1 := by
  have h1 := two_mul_E_of_compl_eq h
  have h2 := two_mul_choose_two G.V
  have h3 : 4 * G.E = G.V * (G.V - 1) := by omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨k, hk⟩ : ∃ k, G.V = 4 * k + G.V % 4 := ⟨G.V / 4, by omega⟩
  have hr : G.V % 4 = 2 ∨ G.V % 4 = 3 := by omega
  rcases hr with hr | hr <;> rw [hr] at hk
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 12 * k + 2 := by
      rw [hk, show 4 * k + 2 - 1 = 4 * k + 1 from by omega]; ring
    omega
  · have hexp : G.V * (G.V - 1) = 16 * (k * k) + 20 * k + 6 := by
      rw [hk, show 4 * k + 3 - 1 = 4 * k + 2 from by omega]; ring
    omega

/-- A self-complementary *vertex-transitive* graph has `ω² ≤ |V|`, since `α = ω` there. -/
theorem cliqueNum_sq_le_V_of_compl_eq {G : IsoGraph} (h : IsVertexTransitive G)
    (hc : compl G = G) : G.cliqueNum ^ 2 ≤ G.V := by
  have hα := indepNum_eq_cliqueNum_of_compl_eq hc
  have hle := indepNum_mul_cliqueNum_le_V h
  rw [hα, ← pow_two] at hle
  exact hle

/-- `ω(Paley 13) ≤ 3` (the true value is `3`), from `ω² ≤ 13`.  Since `Paley 13` is
self-complementary this bounds its independence number too. -/
theorem cliqueNum_paley_thirteen_le : (paley 13).cliqueNum ≤ 3 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h := cliqueNum_sq_le_V_of_compl_eq (isVertexTransitive_paley 13) compl_paley_thirteen
  rw [V_paley] at h
  by_contra hcon
  push_neg at hcon
  have : 4 * 4 ≤ (paley 13).cliqueNum ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul hcon hcon
  omega

theorem indepNum_paley_thirteen_le : (paley 13).indepNum ≤ 3 := by
  rw [indepNum_eq_cliqueNum_of_compl_eq compl_paley_thirteen]
  exact cliqueNum_paley_thirteen_le

/-- `ω(Paley 17) ≤ 4`, from `ω² ≤ 17`. -/
theorem cliqueNum_paley_seventeen_le : (paley 17).cliqueNum ≤ 4 := by
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have h := cliqueNum_sq_le_V_of_compl_eq (isVertexTransitive_paley 17) compl_paley_seventeen
  rw [V_paley] at h
  by_contra hcon
  push_neg at hcon
  have : 5 * 5 ≤ (paley 17).cliqueNum ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul hcon hcon
  omega

/-- No graph on `6` vertices is self-complementary. -/
example (G : IsoGraph) (h : G.V = 6) : compl G ≠ G := fun hc ↦ by
  have := V_mod_four_of_compl_eq hc
  rw [h] at this
  omega

/-! ### The domination number -/

theorem domNum_le_V (G : IsoGraph) : G.domNum ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk]
  exact CGraph.domNum_le_card _

@[simp] theorem domNum_eq_zero_iff (G : IsoGraph) : G.domNum = 0 ↔ G.V = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk]
  exact CGraph.domNum_eq_zero_iff _

theorem domNum_pos {G : IsoGraph} (h : 0 < G.V) : 0 < G.domNum := by
  have := (G.domNum_eq_zero_iff).not.2 (by omega : ¬ G.V = 0)
  omega

/-- **The degree bound** `|V| ≤ γ·(Δ + 1)`. -/
theorem V_le_domNum_mul_maxDeg_add_one (G : IsoGraph) : G.V ≤ G.domNum * (G.maxDeg + 1) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk, maxDeg_mk]
  exact CGraph.card_le_domNum_mul_maxDeg_add_one _

/-- **`γ ≤ α`**. -/
theorem domNum_le_indepNum (G : IsoGraph) : G.domNum ≤ G.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, domNum_mk, indepNum_mk]
  exact CGraph.domNum_le_indepNum _

/-- **`γ + Δ ≤ |V|`**. -/
theorem domNum_add_maxDeg_le_V (G : IsoGraph) : G.domNum + G.maxDeg ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk, domNum_mk, maxDeg_mk]
  exact CGraph.domNum_add_maxDeg_le_card _

/-- **`γ ≤ τ`** for a graph with no isolated vertex. -/
theorem domNum_le_coverNum {G : IsoGraph} (h : 1 ≤ G.minDeg) : G.domNum ≤ G.coverNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, domNum_mk, coverNum_mk]
  rw [← mk_canonicalize g, minDeg_mk] at h
  exact CGraph.domNum_le_coverNum _ h

/-- With Gallai's identity, the degree bound reads `τ ≥ |V|·Δ/(Δ+1) - ...`; more usefully it
bounds the independence number from below, since `γ ≤ α`. -/
theorem V_le_indepNum_mul_maxDeg_add_one (G : IsoGraph) : G.V ≤ G.indepNum * (G.maxDeg + 1) :=
  le_trans G.V_le_domNum_mul_maxDeg_add_one
    (Nat.mul_le_mul_right _ G.domNum_le_indepNum)

/-! ### The table -/

@[simp] theorem domNum_empty (n : ℕ) : (empty n).domNum = n := CGraph.domNum_empty n

@[simp] theorem domNum_complete (n : ℕ) : (complete (n + 1)).domNum = 1 :=
  CGraph.domNum_complete n

@[simp] theorem domNum_star (n : ℕ) : (star n).domNum = 1 := CGraph.domNum_star n

/-- A `k`-regular graph needs at least `|V|/(k + 1)` vertices to dominate it. -/
theorem le_domNum_of_regular {G : IsoGraph} {k : ℕ} (h : G.maxDeg = k) :
    G.V ≤ G.domNum * (k + 1) := by
  rw [← h]; exact G.V_le_domNum_mul_maxDeg_add_one

/-- `γ(Petersen) ≥ 3` (the true value is `3`). -/
theorem three_le_domNum_petersen : 3 ≤ petersen.domNum := by
  have h := le_domNum_of_regular (G := petersen) (k := 3) maxDeg_petersen
  rw [V_petersen] at h
  omega

/-- `γ(Cₙ) ≥ n/3`. -/
theorem le_domNum_cycle (n : ℕ) : n + 3 ≤ (cycle (n + 3)).domNum * 3 := by
  have h := le_domNum_of_regular (G := cycle (n + 3)) (k := 2) (maxDeg_cycle n)
  rwa [V_cycle] at h

example : (star 5).domNum = 1 := by simp

example : (empty 4).domNum = 4 := by simp

example : (complete 7).domNum = 1 := by simp

/-! ### The radius -/

theorem radius_le_diameter (G : IsoGraph) : G.radius ≤ G.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, diameter_mk]
  exact CGraph.radius_le_diameter _

theorem diameter_le_two_mul_radius (G : IsoGraph) : G.diameter ≤ 2 * G.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, diameter_mk]
  exact CGraph.diameter_le_two_mul_radius _

theorem radius_pos {G : IsoGraph} (hc : IsConnected G) (hV : 1 < G.V) : 0 < G.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk]
  rw [← mk_canonicalize g, isConnected_mk] at hc
  rw [← mk_canonicalize g, V_mk] at hV
  exact CGraph.radius_pos _ hc hV

/-- **`r = 1 ↔ γ = 1`** on a graph with at least two vertices. -/
theorem radius_eq_one_iff_domNum_eq_one {G : IsoGraph} (hV : 1 < G.V) :
    G.radius = 1 ↔ G.domNum = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, domNum_mk]
  rw [← mk_canonicalize g, V_mk] at hV
  exact CGraph.radius_eq_one_iff_domNum_eq_one _ hV

/-- **A vertex-transitive graph has `r = d`.** -/
theorem radius_eq_diameter_of_isVertexTransitive {G : IsoGraph} (h : IsVertexTransitive G) :
    G.radius = G.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, radius_mk, diameter_mk]
  rw [← mk_canonicalize g, isVertexTransitive_mk] at h
  exact CGraph.radius_eq_diameter_of_isVertexTransitive _ h

/-! ### The radius table -/

@[simp] theorem domNum_wheel (n : ℕ) : (wheel n).domNum = 1 := CGraph.domNum_wheel n


@[simp] theorem radius_empty (n : ℕ) : (empty n).radius = 0 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_empty n), diameter_empty]

@[simp] theorem radius_complete (n : ℕ) : (complete (n + 2)).radius = 1 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_complete _),
    diameter_complete]

@[simp] theorem radius_cycle (n : ℕ) : (cycle (n + 1)).radius = (n + 1) / 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_cycle _), diameter_cycle]

@[simp] theorem radius_hypercube (n : ℕ) : (hypercube n).radius = n := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_hypercube n),
    diameter_hypercube]

@[simp] theorem radius_petersen : petersen.radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive isVertexTransitive_petersen, diameter_petersen]

@[simp] theorem radius_rook (m n : ℕ) : (rook (m + 2) (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_rook _ _), diameter_rook]

@[simp] theorem radius_cocktailParty (n : ℕ) : (cocktailParty (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (by simp), diameter_cocktailParty]

theorem radius_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_triangular n),
    diameter_triangular hn]

theorem radius_bipartite_self (n : ℕ) : (bipartite (n + 2) (n + 2)).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_bipartite_self _),
    diameter_bipartite_self]

@[simp] theorem radius_star (n : ℕ) : (star (n + 1)).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one (by rw [V_star]; omega)]
  exact domNum_star (n + 1)

/-- The hub of a wheel dominates it, so the wheel has radius one. -/
@[simp] theorem radius_wheel (n : ℕ) : (wheel (n + 1)).radius = 1 := by
  rw [radius_eq_one_iff_domNum_eq_one (by rw [V_wheel]; omega)]
  exact domNum_wheel (n + 1)

@[simp] theorem radius_prism (n : ℕ) : (prism (n + 1)).radius = (n + 1) / 2 + 1 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_prism _), diameter_prism]

theorem radius_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).radius = 2 := by
  rw [radius_eq_diameter_of_isVertexTransitive (isVertexTransitive_paley q),
    diameter_paley q hq hq5]

/-! ### Consequences -/

/-- A graph of radius `r` needs at least `2r` steps to be crossed in the worst case, so a graph
with a large diameter has a large radius. -/
example (G : IsoGraph) (h : 5 ≤ G.diameter) : 3 ≤ G.radius := by
  have := G.diameter_le_two_mul_radius
  omega

example : (complete 5).radius = 1 := by simp

example : (star 4).radius = 1 := by simp

example (n : ℕ) : (cycle (2 * n + 1)).radius = n := by
  rw [show 2 * n + 1 = n + n + 1 from by omega, radius_cycle]
  omega

/-! ### Counting cliques -/

theorem cliqueCount_le_choose (G : IsoGraph) (n : ℕ) : G.cliqueCount n ≤ G.V.choose n := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, V_mk]
  exact CGraph.cliqueCount_le_choose _ n

@[simp] theorem cliqueCount_zero (G : IsoGraph) : G.cliqueCount 0 = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk]
  exact CGraph.cliqueCount_zero _

@[simp] theorem cliqueCount_one (G : IsoGraph) : G.cliqueCount 1 = G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, V_mk]
  exact CGraph.cliqueCount_one _

@[simp] theorem cliqueCount_two (G : IsoGraph) : G.cliqueCount 2 = G.E := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, E_mk]
  classical
  exact CGraph.cliqueCount_two _

theorem cliqueCount_eq_zero_iff (G : IsoGraph) (n : ℕ) :
    G.cliqueCount n = 0 ↔ G.cliqueNum < n := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, cliqueNum_mk]
  exact CGraph.cliqueCount_eq_zero_iff _ n

theorem cliqueCount_pos_iff (G : IsoGraph) (n : ℕ) : 0 < G.cliqueCount n ↔ n ≤ G.cliqueNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, cliqueCount_eq_zero_iff]
  omega

theorem cliqueCount_three_eq_zero_iff (G : IsoGraph) : G.cliqueCount 3 = 0 ↔ G.girth ≠ 3 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, cliqueCount_mk, girth_mk]
  exact CGraph.cliqueCount_three_eq_zero_iff _

theorem cliqueCount_three_eq_zero_of_isBipartite {G : IsoGraph} (h : G.IsBipartite) :
    G.cliqueCount 3 = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [cliqueCount_mk]
  rw [isBipartite_mk] at h
  exact CGraph.cliqueCount_three_eq_zero_of_isBipartite h

/-! ### The clique-count table -/

@[simp] theorem cliqueCount_complete (m n : ℕ) : (complete m).cliqueCount n = m.choose n :=
  CGraph.cliqueCount_complete m n

@[simp] theorem cliqueCount_empty (m n : ℕ) : (empty m).cliqueCount (n + 2) = 0 :=
  CGraph.cliqueCount_empty m n

@[simp] theorem cliqueCount_cycle_even (m : ℕ) : (cycle (2 * m)).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_cycle_even m)

@[simp] theorem cliqueCount_cycle_four : (cycle 4).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_four]
  omega

@[simp] theorem cliqueCount_cycle_five : (cycle 5).cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_cycle_five]
  omega

@[simp] theorem cliqueCount_prism_even (m : ℕ) : (prism (2 * m)).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_prism_even m)

@[simp] theorem cliqueCount_star (n : ℕ) : (star n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_star n)

@[simp] theorem cliqueCount_petersen : petersen.cliqueCount 3 = 0 := by
  rw [cliqueCount_three_eq_zero_iff, girth_petersen]
  omega

@[simp] theorem cliqueCount_bipartite (m n : ℕ) : (bipartite m n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_bipartite m n)

@[simp] theorem cliqueCount_hypercube (n : ℕ) : (hypercube n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_hypercube n)

example : (complete 5).cliqueCount 3 = 10 := by rw [cliqueCount_complete]; decide

example : (cycle 6).cliqueCount 3 = 0 := cliqueCount_cycle_even 3

/-! ### Counting independent sets -/

@[simp] theorem cliqueCount_compl (G : IsoGraph) (n : ℕ) :
    (compl G).cliqueCount n = G.indepCount n := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, cliqueCount_mk, indepCount_mk]
  exact CGraph.cliqueCount_compl _ n

@[simp] theorem indepCount_compl (G : IsoGraph) (n : ℕ) :
    (compl G).indepCount n = G.cliqueCount n := by
  rw [← cliqueCount_compl (compl G), compl_compl]

@[simp] theorem indepCount_zero (G : IsoGraph) : G.indepCount 0 = 1 := by
  rw [← cliqueCount_compl, cliqueCount_zero]

@[simp] theorem indepCount_one (G : IsoGraph) : G.indepCount 1 = G.V := by
  rw [← cliqueCount_compl, cliqueCount_one, V_compl]

theorem indepCount_eq_zero_iff (G : IsoGraph) (n : ℕ) :
    G.indepCount n = 0 ↔ G.indepNum < n := by
  rw [← cliqueCount_compl, cliqueCount_eq_zero_iff, cliqueNum_compl]

theorem indepCount_pos_iff (G : IsoGraph) (n : ℕ) : 0 < G.indepCount n ↔ n ≤ G.indepNum := by
  rw [Nat.pos_iff_ne_zero, ne_eq, indepCount_eq_zero_iff]
  omega

theorem indepCount_le_choose (G : IsoGraph) (n : ℕ) : G.indepCount n ≤ G.V.choose n := by
  rw [← cliqueCount_compl, ← V_compl]
  exact cliqueCount_le_choose _ n

theorem indepCount_two_add_E (G : IsoGraph) : G.indepCount 2 + G.E = G.V.choose 2 := by
  rw [← cliqueCount_compl, cliqueCount_two]
  exact E_compl_add G

@[simp] theorem indepCount_empty (m n : ℕ) : (empty m).indepCount n = m.choose n := by
  rw [← cliqueCount_compl, compl_empty, cliqueCount_complete]

@[simp] theorem indepCount_complete (m n : ℕ) : (complete m).indepCount (n + 2) = 0 := by
  rw [← cliqueCount_compl, compl_complete, cliqueCount_empty]

example : (empty 6).indepCount 3 = 20 := by rw [indepCount_empty]; decide

example : (complete 4).indepCount 2 = 0 := by
  show (complete 4).indepCount (0 + 2) = 0
  simp

/-! ### Counting cliques in a disjoint union -/

theorem cliqueCount_disjUnion (G H : IsoGraph) (n : ℕ) :
    (disjUnion G H).cliqueCount (n + 1)
      = G.cliqueCount (n + 1) + H.cliqueCount (n + 1) := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, cliqueCount_mk, cliqueCount_mk, cliqueCount_mk]
  exact CGraph.cliqueCount_disjUnion g h n

theorem indepCount_join (G H : IsoGraph) (n : ℕ) :
    (join G H).indepCount (n + 1) = G.indepCount (n + 1) + H.indepCount (n + 1) := by
  rw [join, indepCount_compl, cliqueCount_disjUnion, cliqueCount_compl, cliqueCount_compl]

@[simp] theorem indepCount_bipartite (m n k : ℕ) :
    (bipartite m n).indepCount (k + 1) = m.choose (k + 1) + n.choose (k + 1) := by
  rw [bipartite_def, indepCount_mk]
  exact CGraph.indepCount_bipartite m n k

@[simp] theorem indepCount_star (n k : ℕ) :
    (star n).indepCount (k + 2) = n.choose (k + 2) := by
  rw [star_def, CGraph.star, ← bipartite_def, indepCount_bipartite]
  simp [Nat.choose_eq_zero_of_lt]

example : (bipartite 4 6).indepCount 3 = 24 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, indepCount_bipartite]; decide

example : (disjUnion (complete 4) (complete 5)).cliqueCount 3 = 14 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cliqueCount_disjUnion, cliqueCount_complete,
    cliqueCount_complete]
  decide

/-! ### Counting connected components -/

theorem numComponents_eq_zero_iff (G : IsoGraph) : G.numComponents = 0 ↔ G.V = 0 := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.numComponents_eq_zero_iff g

theorem numComponents_pos_iff (G : IsoGraph) : 0 < G.numComponents ↔ 0 < G.V := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, ne_eq, ne_eq, numComponents_eq_zero_iff]

/-- A graph is connected exactly when it has one component. -/
theorem numComponents_eq_one_iff (G : IsoGraph) : G.numComponents = 1 ↔ G.IsConnected := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.numComponents_eq_one_iff g

theorem numComponents_eq_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) :
    G.numComponents = 1 :=
  (numComponents_eq_one_iff G).2 h

theorem numComponents_le_V (G : IsoGraph) : G.numComponents ≤ G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.numComponents_le_card g

@[simp] theorem numComponents_disjUnion (G H : IsoGraph) :
    (disjUnion G H).numComponents = G.numComponents + H.numComponents := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [disjUnion_mk, numComponents_mk, numComponents_mk, numComponents_mk]
  exact CGraph.numComponents_disjUnion g h

/-- **At most one of a graph and its complement is disconnected.** -/
theorem numComponents_compl_eq_one {G : IsoGraph} (h : 2 ≤ G.numComponents) :
    (compl G).numComponents = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, numComponents_mk]
  rw [← mk_canonicalize g, numComponents_mk] at h
  exact CGraph.numComponents_compl_eq_one _ h

/-! ### The component-count table -/

@[simp] theorem numComponents_empty (n : ℕ) : (empty n).numComponents = n := by
  rw [empty_def, numComponents_mk]
  exact CGraph.numComponents_empty n

@[simp] theorem numComponents_complete (n : ℕ) : (complete (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_complete n)

@[simp] theorem numComponents_path (n : ℕ) : (path (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_path n)

@[simp] theorem numComponents_cycle (n : ℕ) : (cycle (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_cycle n)

@[simp] theorem numComponents_star (n : ℕ) : (star n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_star n)

@[simp] theorem numComponents_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_bipartite m n)

@[simp] theorem numComponents_hypercube (n : ℕ) : (hypercube n).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_hypercube n)

@[simp] theorem numComponents_wheel (n : ℕ) : (wheel (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_wheel n)

@[simp] theorem numComponents_prism (n : ℕ) : (prism (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_prism n)

@[simp] theorem numComponents_ladder (n : ℕ) : (ladder (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_ladder n)

@[simp] theorem numComponents_rook (m n : ℕ) : (rook (m + 1) (n + 1)).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_rook m n)

example : (disjUnion (cycle 5) (path 4)).numComponents = 2 := by simp

example : (empty 7).numComponents = 7 := by simp

/-! ### Components versus the other invariants -/

theorem numComponents_le_indepNum (G : IsoGraph) : G.numComponents ≤ G.indepNum := by
  induction G using Quotient.inductionOn with | _ g
  exact CGraph.numComponents_le_indepNum g

theorem numComponents_le_domNum (G : IsoGraph) : G.numComponents ≤ G.domNum := by
  induction G using Quotient.inductionOn with | _ g
  exact CGraph.numComponents_le_domNum g

@[simp] theorem numComponents_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (join G H).numComponents = 1 :=
  numComponents_eq_one_of_isConnected (isConnected_join hG hH)

/-- A graph has as many components as vertices exactly when it has no edges. -/
theorem numComponents_eq_V_iff (G : IsoGraph) : G.numComponents = G.V ↔ G.E = 0 := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk, E_mk, numComponents_mk]
  exact CGraph.numComponents_eq_card_iff _

theorem numComponents_lt_V_of_E_pos {G : IsoGraph} (h : 0 < G.E) : G.numComponents < G.V := by
  have hle := G.numComponents_le_V
  have := (G.numComponents_eq_V_iff).not.2 (by omega : ¬ G.E = 0)
  omega

example : (join (cycle 5) (empty 3)).numComponents = 1 := by
  refine numComponents_join ?_ ?_ <;> simp

example : (cycle 5).numComponents < (cycle 5).V := numComponents_lt_V_of_E_pos (by simp)

/-! ### Components of a Cartesian product -/

/-- **The components of a Cartesian product are the pairs of components.** -/
@[simp] theorem numComponents_cartesianProduct (G H : IsoGraph) :
    (cartesianProduct G H).numComponents = G.numComponents * H.numComponents := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, numComponents_mk,
    numComponents_mk, numComponents_mk]
  exact CGraph.numComponents_cartesianProduct _ _

/-! ### A minimum-degree condition for connectedness -/

/-- **A graph with `2δ(G) + 1 ≥ |V|` is connected.** -/
theorem isConnected_of_V_le_two_mul_minDeg (G : IsoGraph) (hV : 0 < G.V)
    (h : G.V ≤ 2 * minDeg G + 1) : IsConnected G := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, V_mk, minDeg_mk] at h
  rw [← mk_canonicalize g, isConnected_mk]
  have : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  exact CGraph.isConnected_of_card_le_two_mul_minDeg _ h

theorem numComponents_eq_one_of_V_le_two_mul_minDeg (G : IsoGraph) (hV : 0 < G.V)
    (h : G.V ≤ 2 * minDeg G + 1) : G.numComponents = 1 :=
  numComponents_eq_one_of_isConnected (G.isConnected_of_V_le_two_mul_minDeg hV h)

example : (cartesianProduct (empty 3) (empty 4)).numComponents = 12 := by simp

example : IsConnected (hypercube 2) := by
  refine (hypercube 2).isConnected_of_V_le_two_mul_minDeg (by simp) ?_
  simp

/-! ### Counting automorphisms -/

theorem autCount_pos (G : IsoGraph) : 0 < G.autCount := by
  induction G using Quotient.inductionOn with | _ g
  exact CGraph.autCount_pos g

theorem autCount_le_factorial (G : IsoGraph) : G.autCount ≤ Nat.factorial G.V := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk, autCount_mk]
  exact CGraph.autCount_le_factorial _

/-- **A graph and its complement have the same automorphisms.** -/
@[simp] theorem autCount_compl (G : IsoGraph) : (compl G).autCount = G.autCount := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, compl_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_compl _

@[simp] theorem autCount_empty (n : ℕ) : (empty n).autCount = Nat.factorial n := by
  rw [empty_def, autCount_mk, CGraph.autCount_empty]

@[simp] theorem autCount_complete (n : ℕ) : (complete n).autCount = Nat.factorial n := by
  rw [complete_def, autCount_mk, CGraph.autCount_complete]

/-- Two graphs with different automorphism counts are different. -/
theorem ne_of_autCount_ne {G H : IsoGraph} (h : G.autCount ≠ H.autCount) : G ≠ H :=
  fun hGH ↦ h (hGH ▸ rfl)

example : (complete 4).autCount = 24 := by simp [Nat.factorial]

example : (empty 3).autCount = 6 := by simp [Nat.factorial]

/-! ### Automorphisms versus symmetry -/

theorem V_le_autCount_of_isVertexTransitive (G : IsoGraph) (hV : 0 < G.V)
    (h : G.IsVertexTransitive) : G.V ≤ G.autCount := by
  induction G using Quotient.inductionOn with | _ g =>
  haveI : Nonempty g.V := Fintype.card_pos_iff.1 hV
  exact CGraph.card_le_autCount_of_isVertexTransitive g h

theorem two_mul_E_le_autCount_of_isArcTransitive (G : IsoGraph) (h : G.IsArcTransitive) :
    2 * G.E ≤ G.autCount := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.two_mul_E_le_autCount_of_isArcTransitive g h

theorem not_isVertexTransitive_of_autCount_lt (G : IsoGraph) (hV : 0 < G.V)
    (h : G.autCount < G.V) : ¬ G.IsVertexTransitive := fun hvt ↦
  absurd (G.V_le_autCount_of_isVertexTransitive hV hvt) (by omega)

theorem not_isArcTransitive_of_autCount_lt (G : IsoGraph) (h : G.autCount < 2 * G.E) :
    ¬ G.IsArcTransitive := fun hat ↦
  absurd (G.two_mul_E_le_autCount_of_isArcTransitive hat) (by omega)

example : 5 ≤ (cycle 5).autCount := by
  have := V_le_autCount_of_isVertexTransitive (cycle 5) (by simp) (by simp)
  simpa using this

example : 10 ≤ (cycle 5).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (cycle 5) (by simp)
  simpa using this

example : 24 ≤ (hypercube 3).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (hypercube 3) (by simp)
  simpa using this

example : 30 ≤ (kneser 5 2).autCount := by
  have := two_mul_E_le_autCount_of_isArcTransitive (kneser 5 2) (by simp)
  simpa using this

/-! ### The handshaking lemma -/

theorem even_countP_odd_degMultiset (G : IsoGraph) :
    Even ((degMultiset G).countP fun d ↦ Odd d) := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.even_countP_odd_degMultiset g

theorem even_countP_odd_degSequence (G : IsoGraph) :
    Even ((degSequence G).countP fun d ↦ decide (Odd d)) := by
  induction G using Quotient.inductionOn with | _ g =>
  exact CGraph.even_countP_odd_degSequence g

/-- A graph all of whose degrees are odd has evenly many vertices. -/
theorem even_V_of_forall_odd_mem_degSequence (G : IsoGraph)
    (h : ∀ d ∈ degSequence G, Odd d) : Even G.V := by
  have hc := G.even_countP_odd_degSequence
  rwa [List.countP_eq_length.2 (fun d hd ↦ by simpa using h d hd), length_degSequence] at hc

/-- **An odd-regular graph has evenly many vertices.** -/
theorem even_V_of_degSequence_replicate {G : IsoGraph} {n k : ℕ} (hk : Odd k)
    (h : degSequence G = List.replicate n k) : Even G.V :=
  G.even_V_of_forall_odd_mem_degSequence fun d hd ↦ by
    rw [h, List.mem_replicate] at hd
    exact hd.2 ▸ hk

/-- On an odd number of vertices, some degree is even. -/
theorem exists_even_mem_degSequence_of_odd_V (G : IsoGraph) (h : Odd G.V) :
    ∃ d ∈ degSequence G, Even d := by
  by_contra hc
  push_neg at hc
  exact Nat.not_even_iff_odd.2 h (G.even_V_of_forall_odd_mem_degSequence
    fun d hd ↦ Nat.not_even_iff_odd.1 (hc d hd))

/-- There is no cubic graph on seven vertices. -/
example (G : IsoGraph) (h : degSequence G = List.replicate 7 3) : False := by
  have hV : G.V = 7 := by rw [← length_degSequence, h, List.length_replicate]
  have := even_V_of_degSequence_replicate (by decide) h
  rw [hV] at this
  exact (by decide : ¬ Even 7) this

/-! ### Automorphisms of the constructions -/

theorem autCount_mul_le_autCount_disjUnion (G H : IsoGraph) :
    G.autCount * H.autCount ≤ (disjUnion G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [disjUnion_mk, autCount_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_mul_le_autCount_disjUnion g h

theorem autCount_mul_le_autCount_join (G H : IsoGraph) :
    G.autCount * H.autCount ≤ (join G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, autCount_mk, autCount_mk, autCount_mk]
  exact CGraph.autCount_mul_le_autCount_join _ _

theorem autCount_mul_le_autCount_cartesianProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (cartesianProduct G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_cartesianProduct _ _

theorem autCount_mul_le_autCount_tensorProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (tensorProduct G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_tensorProduct _ _

theorem autCount_mul_le_autCount_strongProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (strongProduct G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_strongProduct _ _

theorem autCount_mul_le_autCount_lexProduct (G H : IsoGraph) (hG : 0 < G.V)
    (hH : 0 < H.V) : G.autCount * H.autCount ≤ (lexProduct G H).autCount := by
  induction G using Quotient.inductionOn with | _ g
  induction H using Quotient.inductionOn with | _ h
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, autCount_mk, autCount_mk,
    autCount_mk]
  exact CGraph.autCount_mul_le_autCount_lexProduct _ _

theorem two_mul_autCount_mul_le_autCount_disjUnion_self (G : IsoGraph) (hV : 0 < G.V) :
    2 * (G.autCount * G.autCount) ≤ (disjUnion G G).autCount := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, disjUnion_mk, autCount_mk, autCount_mk]
  exact CGraph.two_mul_autCount_mul_le_autCount_disjUnion_self _

example : 12 ≤ (disjUnion (complete 3) (complete 4)).autCount := by
  have := autCount_mul_le_autCount_disjUnion (complete 3) (complete 4)
  simp [Nat.factorial] at this
  omega

/-! ### Vertices, edges and components -/

/-- `|V| ≤ |E| + c(G)`: a spanning forest has `|V| - c(G)` edges. -/
theorem V_le_E_add_numComponents (G : IsoGraph) : G.V ≤ G.E + G.numComponents := by
  induction G using Quotient.inductionOn with | _ g
  exact CGraph.card_le_E_add_numComponents g

theorem V_le_E_add_one_of_isConnected {G : IsoGraph} (h : G.IsConnected) : G.V ≤ G.E + 1 := by
  have := G.V_le_E_add_numComponents
  rw [numComponents_eq_one_of_isConnected h] at this
  exact this

theorem V_sub_E_le_numComponents (G : IsoGraph) : G.V - G.E ≤ G.numComponents := by
  have := G.V_le_E_add_numComponents
  omega

theorem E_pos_of_numComponents_lt_V {G : IsoGraph} (h : G.numComponents < G.V) : 0 < G.E := by
  have := G.V_le_E_add_numComponents
  omega

theorem not_isConnected_of_E_add_one_lt_V {G : IsoGraph} (h : G.E + 1 < G.V) :
    ¬ G.IsConnected := fun hc ↦ by
  have := V_le_E_add_one_of_isConnected hc
  omega

/-- `c(G) = |V|` forces `E = 0`, and this recovers it quantitatively: each edge kills at most one
component. -/
theorem V_sub_numComponents_le_E (G : IsoGraph) : G.V - G.numComponents ≤ G.E := by
  have := G.V_le_E_add_numComponents
  omega

example : (empty 5).V - (empty 5).E ≤ (empty 5).numComponents := by simp

example : ¬ (disjUnion (complete 1) (complete 1)).IsConnected := by
  apply not_isConnected_of_E_add_one_lt_V
  simp

/-! ### The clique number of the Mycielskian -/

theorem cliqueNum_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    (mycielskian G).cliqueNum = max G.cliqueNum 2 := by
  induction G using Quotient.inductionOn with | _ g
  rw [← mk_canonicalize g, V_mk] at hV
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, mycielskian_mk, cliqueNum_mk, cliqueNum_mk]
  exact CGraph.cliqueNum_mycielskian _

theorem cliqueNum_mycielskian_eq_two {G : IsoGraph} (hV : 0 < G.V) (h : G.cliqueNum ≤ 2) :
    (mycielskian G).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian G hV]
  omega

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

example : (mycielskian (cycle 5)).cliqueNum = 2 := by
  rw [cliqueNum_mycielskian _ (by simp), cliqueNum_cycle_five, max_self]

/-! ### Edge counts of the strong and lexicographic products -/

@[simp] theorem E_strongProduct (G H : IsoGraph) :
    (strongProduct G H).E = G.V * H.E + H.V * G.E + 2 * G.E * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_strongProduct _ _

@[simp] theorem E_lexProduct (G H : IsoGraph) :
    (lexProduct G H).E = H.V * H.V * G.E + G.V * H.E := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, E_mk, E_mk, E_mk, V_mk, V_mk]
  exact CGraph.E_lexProduct _ _

theorem E_strongProduct_eq_add (G H : IsoGraph) :
    (strongProduct G H).E = (cartesianProduct G H).E + (tensorProduct G H).E := by
  rw [E_strongProduct, E_cartesianProduct, E_tensorProduct]

example : (strongProduct (complete 3) (complete 3)).E = 36 := by
  rw [E_strongProduct]
  simp

example : (lexProduct (complete 2) (empty 3)).E = 9 := by
  rw [E_lexProduct]
  simp

example : (strongProduct (path 2) (path 2)).E = 6 := by
  rw [E_strongProduct]
  simp

example : (paley 9).E = 27 := by
  rw [paley_nine_eq_lexProduct, E_lexProduct]
  simp

/-! ### Domination in disjoint unions, joins and cartesian products -/

@[simp] theorem domNum_disjUnion (G H : IsoGraph) :
    (disjUnion G H).domNum = G.domNum + H.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, disjUnion_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_disjUnion _ _

theorem domNum_join_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (join G H).domNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hG
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, domNum_mk]
  exact CGraph.domNum_join_le_two _ _

@[simp] theorem domNum_join_eq_one_iff (G H : IsoGraph) :
    (join G H).domNum = 1 ↔ G.domNum = 1 ∨ H.domNum = 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, join_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_join_eq_one_iff _ _

theorem domNum_join_eq_two {G H : IsoGraph} (hGV : 0 < G.V) (hHV : 0 < H.V)
    (hG : G.domNum ≠ 1) (hH : H.domNum ≠ 1) : (join G H).domNum = 2 := by
  have h1 := domNum_join_le_two hGV hHV
  have h2 : 0 < (join G H).domNum := domNum_pos (by rw [V_join]; omega)
  have h3 : (join G H).domNum ≠ 1 := fun h ↦ by
    rcases (domNum_join_eq_one_iff G H).1 h with h | h
    · exact hG h
    · exact hH h
  omega

theorem domNum_cartesianProduct_le (G H : IsoGraph) :
    (cartesianProduct G H).domNum ≤ G.domNum * H.V := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, domNum_mk, domNum_mk, V_mk]
  exact CGraph.domNum_cartesianProduct_le _ _

theorem domNum_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).domNum = 2 := by
  rw [bipartite_eq_join]
  exact domNum_join_eq_two (by simp) (by simp) (by simp) (by simp)

example : (disjUnion (complete 3) (complete 4)).domNum = 2 := by simp

example : (disjUnion (empty 5) (complete 3)).domNum = 6 := by simp

example : (bipartite 3 3).domNum = 2 := domNum_bipartite 1 1

example : (cartesianProduct (complete 4) (complete 4)).domNum ≤ 4 := by
  have := domNum_cartesianProduct_le (complete 4) (complete 4)
  simpa using this

/-! ### The radius of a cartesian product -/

theorem radius_cartesianProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (cartesianProduct G H).radius = G.radius + H.radius := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, radius_mk, radius_mk,
    radius_mk]
  exact CGraph.radius_cartesianProduct _ _ hG hH

example : (cartesianProduct (cycle 5) (cycle 5)).radius = 4 := by
  rw [radius_cartesianProduct (by simp) (by simp)]
  simp

example : (rook 4 4).radius = 2 := by
  rw [rook, radius_cartesianProduct (by simp) (by simp)]
  simp

theorem diameter_strongProduct_le {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (strongProduct G H).diameter ≤ G.diameter + H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, diameter_mk, diameter_mk,
    diameter_mk]
  exact CGraph.diameter_strongProduct_le _ _ hG hH

theorem diameter_lexProduct_le {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (lexProduct G H).diameter ≤ G.diameter + H.diameter := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isConnected_mk] at hG
  rw [← mk_canonicalize h, isConnected_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, diameter_mk, diameter_mk,
    diameter_mk]
  exact CGraph.diameter_lexProduct_le _ _ hG hH

theorem radius_cartesianProduct_self {G : IsoGraph} (hG : IsConnected G) :
    (cartesianProduct G G).radius = 2 * G.radius := by
  rw [radius_cartesianProduct hG hG, two_mul]

example : (strongProduct (cycle 5) (cycle 5)).diameter ≤ 4 := by
  have := diameter_strongProduct_le (G := cycle 5) (H := cycle 5) (by simp) (by simp)
  simpa using this

/-! ### Domination in the graph products -/

theorem domNum_strongProduct_le (G H : IsoGraph) :
    (strongProduct G H).domNum ≤ G.domNum * H.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, domNum_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_strongProduct_le _ _

theorem domNum_le_domNum_lexProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (lexProduct G H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_lexProduct _ _

theorem domNum_lexProduct (G : IsoGraph) {H : IsoGraph} (hH : H.domNum = 1) :
    (lexProduct G H).domNum = G.domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, domNum_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_lexProduct _ _ hH

/-- Two universal vertices give a universal vertex of the strong product. -/
theorem domNum_strongProduct_eq_one {G H : IsoGraph} (hG : G.domNum = 1) (hH : H.domNum = 1) :
    (strongProduct G H).domNum = 1 := by
  have hGV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have hHV : 0 < H.V := by
    rcases Nat.eq_zero_or_pos H.V with h | h
    · rw [← domNum_eq_zero_iff] at h; omega
    · exact h
  have h1 := domNum_strongProduct_le G H
  have h2 : 0 < (strongProduct G H).domNum :=
    domNum_pos (by rw [V_strongProduct]; exact Nat.mul_pos hGV hHV)
  rw [hG, hH] at h1
  omega

example : (lexProduct (empty 3) (complete 2)).domNum = 3 := by
  rw [domNum_lexProduct _ (by simp), domNum_empty]

example : (strongProduct (star 3) (star 4)).domNum = 1 :=
  domNum_strongProduct_eq_one (by simp) (by simp)

example : (lexProduct (cycle 5) (complete 4)).domNum = (cycle 5).domNum :=
  domNum_lexProduct _ (by simp)

theorem domNum_le_domNum_cartesianProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (cartesianProduct G H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_cartesianProduct _ _

theorem domNum_le_domNum_strongProduct (G : IsoGraph) {H : IsoGraph} (hH : 0 < H.V) :
    G.domNum ≤ (strongProduct G H).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize h, V_mk] at hH
  haveI : Nonempty h.canonicalize.V := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, domNum_mk, domNum_mk]
  exact CGraph.domNum_le_domNum_strongProduct _ _

/-- The domination number of a strong product sits between the larger factor value and the
product of the two. -/
theorem max_domNum_le_domNum_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.domNum H.domNum ≤ (strongProduct G H).domNum := by
  refine max_le (domNum_le_domNum_strongProduct G hH) ?_
  rw [strongProduct_comm]
  exact domNum_le_domNum_strongProduct H hG

/-! ### Independence numbers of the graph products -/

/-- `α(G) · α(H) ≤ α(G ⊠ H)`: the Shannon-capacity lower bound. -/
theorem indepNum_mul_indepNum_le_indepNum_strongProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (strongProduct G H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_mul_indepNum_le_indepNum_strongProduct _ _

/-- `α(G) · α(H) ≤ α(G □ H)`. -/
theorem indepNum_mul_indepNum_le_indepNum_cartesianProduct (G H : IsoGraph) :
    G.indepNum * H.indepNum ≤ (cartesianProduct G H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, indepNum_mk, indepNum_mk,
    indepNum_mk]
  exact CGraph.indepNum_mul_indepNum_le_indepNum_cartesianProduct _ _

/-- `α(G) · |V(H)| ≤ α(G × H)`, since no tensor edge stays inside a slab. -/
theorem indepNum_mul_V_le_indepNum_tensorProduct (G H : IsoGraph) :
    G.indepNum * H.V ≤ (tensorProduct G H).indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_mul_card_le_indepNum_tensorProduct _ _

/-- `α(G × H)` is also at least `|V(G)| · α(H)`, by symmetry. -/
theorem V_mul_indepNum_le_indepNum_tensorProduct (G H : IsoGraph) :
    G.V * H.indepNum ≤ (tensorProduct G H).indepNum := by
  rw [tensorProduct_comm, mul_comm]
  exact indepNum_mul_V_le_indepNum_tensorProduct H G

/-- `α(G □ H) ≤ |V(G)| · α(H)`, by counting fibrewise. -/
theorem indepNum_cartesianProduct_le (G H : IsoGraph) :
    (cartesianProduct G H).indepNum ≤ G.V * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, cartesianProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_cartesianProduct_le _ _

/-- The mirror bound `α(G □ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_cartesianProduct_le' (G H : IsoGraph) :
    (cartesianProduct G H).indepNum ≤ G.indepNum * H.V := by
  rw [cartesianProduct_comm, mul_comm]
  exact indepNum_cartesianProduct_le H G

/-- `α(G ⊠ H) ≤ |V(G)| · α(H)`. -/
theorem indepNum_strongProduct_le (G H : IsoGraph) :
    (strongProduct G H).indepNum ≤ G.V * H.indepNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, indepNum_mk, indepNum_mk,
    V_mk]
  exact CGraph.indepNum_strongProduct_le _ _

/-- The mirror bound `α(G ⊠ H) ≤ α(G) · |V(H)|`. -/
theorem indepNum_strongProduct_le' (G H : IsoGraph) :
    (strongProduct G H).indepNum ≤ G.indepNum * H.V := by
  rw [strongProduct_comm, mul_comm]
  exact indepNum_strongProduct_le H G

/-- Squeezing the two bounds: a product with a complete graph has independence number exactly
`α(G)`, because `α(K_n) = 1` for `n ≠ 0`. -/
theorem indepNum_cartesianProduct_complete_le (G : IsoGraph) (n : ℕ) :
    (cartesianProduct G (complete n)).indepNum ≤ G.indepNum * n := by
  have h := indepNum_cartesianProduct_le' G (complete n)
  rwa [V_complete] at h

example : 4 ≤ (strongProduct (cycle 5) (cycle 5)).indepNum := by
  have h5 : (cycle 5).indepNum = 2 := by simp
  have h := indepNum_mul_indepNum_le_indepNum_strongProduct (cycle 5) (cycle 5)
  rw [h5] at h
  omega

example : 3 ≤ (tensorProduct (complete 3) (complete 3)).indepNum := by
  have h := V_mul_indepNum_le_indepNum_tensorProduct (complete 3) (complete 3)
  rw [V_complete, indepNum_complete] at h
  omega

/-! ### Colouring the strong product -/

/-- **`χ(G ⊠ H) ≤ χ(G)·χ(H)`.** -/
theorem chromNum_strongProduct_le (G H : IsoGraph) :
    (strongProduct G H).chromNum ≤ G.chromNum * H.chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.chromNum_strongProduct_le _ _

/-- `max χ(G) χ(H) ≤ χ(G ⊠ H)`, once both factors have a vertex. -/
theorem max_chromNum_le_chromNum_strongProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.chromNum H.chromNum ≤ (strongProduct G H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.max_chromNum_le_chromNum_strongProduct _ _ a b

/-- `max χ(G) χ(H) ≤ χ(G[H])`, once both factors have a vertex. -/
theorem max_chromNum_le_chromNum_lexProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    max G.chromNum H.chromNum ≤ (lexProduct G H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, V_mk] at hG
  rw [← mk_canonicalize h, V_mk] at hH
  obtain ⟨a⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨b⟩ := Fintype.card_pos_iff.1 hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, lexProduct_mk, chromNum_mk, chromNum_mk,
    chromNum_mk]
  exact CGraph.max_chromNum_le_chromNum_lexProduct _ _ a b

/-- `ω(G)·ω(H) ≤ χ(G ⊠ H)`. -/
theorem cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (G H : IsoGraph) :
    G.cliqueNum * H.cliqueNum ≤ (strongProduct G H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, ← mk_canonicalize h, strongProduct_mk, chromNum_mk, cliqueNum_mk,
    cliqueNum_mk]
  exact CGraph.cliqueNum_mul_cliqueNum_le_chromNum_strongProduct _ _

/-- Two edges make a tensor edge: `2 ≤ χ(G × H)`. -/
theorem two_le_chromNum_tensorProduct {G H : IsoGraph} (hG : 0 < G.E) (hH : 0 < H.E) :
    2 ≤ (tensorProduct G H).chromNum := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, E_mk] at hG
  rw [← mk_canonicalize h, E_mk] at hH
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, chromNum_mk]
  exact CGraph.two_le_chromNum_tensorProduct hG hH

/-- A bipartite factor and edges on both sides force `χ(G × H) = 2`. -/
theorem chromNum_tensorProduct_eq_two {G H : IsoGraph} (hG : IsBipartite G)
    (hGE : 0 < G.E) (hHE : 0 < H.E) : (tensorProduct G H).chromNum = 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  induction H using Quotient.inductionOn with | _ h =>
  rw [← mk_canonicalize g, isBipartite_mk] at hG
  rw [← mk_canonicalize g, E_mk] at hGE
  rw [← mk_canonicalize h, E_mk] at hHE
  rw [← mk_canonicalize g, ← mk_canonicalize h, tensorProduct_mk, chromNum_mk]
  exact CGraph.chromNum_tensorProduct_eq_two hG hGE hHE

/-- The strong product of complete graphs shows the upper bound is attained. -/
example : (strongProduct (complete 3) (complete 4)).chromNum = 12 := by
  rw [strongProduct_complete, chromNum_complete]

example : 4 ≤ (strongProduct (cycle 5) (cycle 5)).chromNum := by
  have h := cliqueNum_mul_cliqueNum_le_chromNum_strongProduct (cycle 5) (cycle 5)
  have h5 : (cycle 5).cliqueNum = 2 := cliqueNum_cycle_five
  rw [h5] at h
  omega

example : (strongProduct (cycle 5) (cycle 5)).chromNum ≤ 9 := by
  have h := chromNum_strongProduct_le (cycle 5) (cycle 5)
  have h5 : (cycle 5).chromNum = 3 := by
    have := chromNum_cycle_odd 1
    norm_num at this
    exact this
  rw [h5] at h
  omega

example : (tensorProduct (cycle 4) (path 3)).chromNum = 2 := by
  refine chromNum_tensorProduct_eq_two ?_ ?_ ?_
  · simpa using isBipartite_cycle_even 2
  · simp
  · simp

/-! ### Vertex covers of the products -/

/-- Gallai turns the exact independence number of a lexicographic product into an exact cover
number: `τ(G[H]) = |V(G)|·|V(H)| - α(G)·α(H)`. -/
@[simp] theorem coverNum_lexProduct (G H : IsoGraph) :
    (lexProduct G H).coverNum = G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_lexProduct, indepNum_lexProduct]

/-- A cover of a join must contain one whole side. -/
@[simp] theorem coverNum_join (G H : IsoGraph) :
    (join G H).coverNum = min (G.coverNum + H.V) (G.V + H.coverNum) := by
  rw [coverNum_eq, V_join, indepNum_join]
  have := G.coverNum_add_indepNum
  have := H.coverNum_add_indepNum
  omega

/-- The independent set bound `α(G)·α(H) ≤ α(G □ H)` becomes an upper bound on `τ`. -/
theorem coverNum_cartesianProduct_le (G H : IsoGraph) :
    (cartesianProduct G H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_cartesianProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_cartesianProduct G H) _

/-- The same bound for the strong product. -/
theorem coverNum_strongProduct_le (G H : IsoGraph) :
    (strongProduct G H).coverNum ≤ G.V * H.V - G.indepNum * H.indepNum := by
  rw [coverNum_eq, V_strongProduct]
  exact Nat.sub_le_sub_left (indepNum_mul_indepNum_le_indepNum_strongProduct G H) _

/-- Fibrewise counting from below: `|V(G)|·τ(H) ≤ τ(G □ H)`. -/
theorem V_mul_coverNum_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (cartesianProduct G H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_cartesianProduct_le G H
  have h3 := (cartesianProduct G H).coverNum_add_indepNum
  rw [V_cartesianProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- The mirror bound `τ(G) · |V(H)| ≤ τ(G □ H)`. -/
theorem coverNum_mul_V_le_coverNum_cartesianProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (cartesianProduct G H).coverNum := by
  rw [cartesianProduct_comm]
  have h := V_mul_coverNum_le_coverNum_cartesianProduct H G
  rwa [mul_comm] at h

/-- The strong product contains the cartesian one, and both have the same vertex set, so the
lower bound survives: `|V(G)|·τ(H) ≤ τ(G ⊠ H)`. -/
theorem V_mul_coverNum_le_coverNum_strongProduct (G H : IsoGraph) :
    G.V * H.coverNum ≤ (strongProduct G H).coverNum := by
  have h1 : G.V * H.coverNum = G.V * H.V - G.V * H.indepNum := by
    rw [coverNum_eq, Nat.mul_sub]
  have h2 := indepNum_strongProduct_le G H
  have h3 := (strongProduct G H).coverNum_add_indepNum
  rw [V_strongProduct] at h3
  have h4 : G.V * H.indepNum ≤ G.V * H.V :=
    Nat.mul_le_mul_left _ (by have := H.coverNum_add_indepNum; omega)
  omega

/-- The mirror bound for the strong product. -/
theorem coverNum_mul_V_le_coverNum_strongProduct (G H : IsoGraph) :
    G.coverNum * H.V ≤ (strongProduct G H).coverNum := by
  rw [strongProduct_comm]
  have h := V_mul_coverNum_le_coverNum_strongProduct H G
  rwa [mul_comm] at h

/-- A slab `S × V(H)` is independent in the tensor product, so covering it is cheap:
`τ(G × H) ≤ τ(G)·|V(H)|`. -/
theorem coverNum_tensorProduct_le (G H : IsoGraph) :
    (tensorProduct G H).coverNum ≤ G.coverNum * H.V := by
  have h1 : G.coverNum * H.V = G.V * H.V - G.indepNum * H.V := by
    rw [coverNum_eq, Nat.sub_mul]
  have h2 := indepNum_mul_V_le_indepNum_tensorProduct G H
  have h3 := (tensorProduct G H).coverNum_add_indepNum
  rw [V_tensorProduct] at h3
  omega

/-- The mirror bound `τ(G × H) ≤ |V(G)|·τ(H)`. -/
theorem coverNum_tensorProduct_le' (G H : IsoGraph) :
    (tensorProduct G H).coverNum ≤ G.V * H.coverNum := by
  rw [tensorProduct_comm]
  have h := coverNum_tensorProduct_le H G
  rwa [mul_comm] at h

example : (lexProduct (cycle 5) (complete 3)).coverNum = 13 := by
  rw [coverNum_lexProduct, V_cycle, V_complete, indepNum_complete]
  norm_num [show ((cycle 5).indepNum) = 2 from by simp]

example : (cartesianProduct (complete 3) (complete 3)).coverNum ≤ 8 := by
  have h := coverNum_cartesianProduct_le (complete 3) (complete 3)
  simpa using h

example : 6 ≤ (cartesianProduct (complete 3) (complete 3)).coverNum := by
  have h := V_mul_coverNum_le_coverNum_cartesianProduct (complete 3) (complete 3)
  simpa using h


/-! ### Nordhaus–Gaddum for the domination number -/

/-- **`γ(G) + γ(Gᶜ) ≤ |V| + 1`.** -/
theorem domNum_add_domNum_compl_le_V_add_one (G : IsoGraph) :
    G.domNum + (compl G).domNum ≤ G.V + 1 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, compl_mk, domNum_mk, domNum_mk, V_mk]
  exact CGraph.domNum_add_domNum_compl_le_card_add_one _

/-- Two vertices dominate the complement of a disconnected graph. -/
theorem domNum_compl_le_two_of_not_isConnected {G : IsoGraph} (hV : 0 < G.V)
    (h : ¬ IsConnected G) : (compl G).domNum ≤ 2 := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, isConnected_mk] at h
  haveI : Nonempty g.canonicalize.V := Fintype.card_pos_iff.1 hV
  rw [← mk_canonicalize g, compl_mk, domNum_mk]
  exact CGraph.domNum_compl_le_two_of_not_isConnected _ h

/-- `3 ≤ γ(G) + γ(Gᶜ)` on at least two vertices. -/
theorem three_le_domNum_add_domNum_compl {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.domNum + (compl G).domNum := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g, V_mk] at hV
  rw [← mk_canonicalize g, compl_mk, domNum_mk, domNum_mk]
  exact CGraph.three_le_domNum_add_domNum_compl _ hV

/-- The two Nordhaus–Gaddum bounds together. -/
theorem domNum_add_domNum_compl_mem_Icc {G : IsoGraph} (hV : 2 ≤ G.V) :
    3 ≤ G.domNum + (compl G).domNum ∧ G.domNum + (compl G).domNum ≤ G.V + 1 :=
  ⟨three_le_domNum_add_domNum_compl hV, G.domNum_add_domNum_compl_le_V_add_one⟩

/-- An edgeless graph attains the upper bound: `γ(E_n) = n` and `γ(K_n) = 1`. -/
example (n : ℕ) : (empty (n + 1)).domNum + (compl (empty (n + 1))).domNum = (n + 1) + 1 := by
  rw [compl_empty, domNum_empty, domNum_complete]

/-- The complement of a disconnected graph — in particular of any disjoint union of two
nonempty graphs — is dominated by two vertices. -/
theorem domNum_compl_disjUnion_le_two {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (compl (disjUnion G H)).domNum ≤ 2 :=
  domNum_compl_le_two_of_not_isConnected (by rw [V_disjUnion]; omega)
    (not_isConnected_disjUnion hG hH)

/-- The complement of `2 K₃` is `K₃,₃`, which two vertices dominate. -/
example : (compl (disjUnion (complete 3) (complete 3))).domNum ≤ 2 :=
  domNum_compl_disjUnion_le_two (by simp) (by simp)

end IsoGraph
