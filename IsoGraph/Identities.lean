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

end Iso

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

/-- `K_{2,2}` is the square. -/
theorem bipartite_two_two : bipartite 2 2 = cycle 4 := by
  rw [bipartite_def, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.bipartite 2 2) (H := CGraph.cycle 4)
    (⟨Sum.elim ![0, 2] ![1, 3], ![.inl 0, .inr 0, .inl 1, .inr 1], by decide, by decide⟩ :
      (Fin 2 ⊕ Fin 2) ≃ Fin 4)
    (by decide)⟩

@[simp] theorem wheel_zero : wheel 0 = empty 1 := by
  rw [wheel_eq_join, cycle_zero, join_empty_zero, complete_one]

theorem wheel_one : wheel 1 = complete 2 := by
  rw [wheel_eq_join, cycle_one, ← complete_one, join_complete]

theorem wheel_two : wheel 2 = complete 3 := by
  rw [wheel_eq_join, cycle_two, join_complete]

theorem wheel_three : wheel 3 = complete 4 := by
  rw [wheel_eq_join, cycle_three, join_complete]

/-! ## Complete multipartite graphs

A single part is an independent set, and `cocktailParty 1` is that case; two singleton parts and
one part of size `n` is the book `B_n`, whose first two members are complete. -/

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

/-! ## Paley graphs -/

/-- The nonzero squares mod `5` are `{1, 4} = {±1}`, so `Paley(5)` is the pentagon — and the
identity map on `Fin 5` is already the isomorphism. -/
theorem paley_five : paley 5 = cycle 5 := by
  rw [paley_def, cycle_def]
  exact Quotient.sound ⟨CGraph.isoOfAdj
    (G := CGraph.paley 5) (H := CGraph.cycle 5) (Equiv.refl (Fin 5)) (by decide)⟩

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

/-- The triangular graph is the complement of the Petersen-style Kneser graph on 2-sets. -/
theorem triangular_eq_compl_kneser (n : ℕ) : triangular n = compl (kneser n 2) := by
  rw [kneser_def, compl_mk]
  exact Quotient.sound ⟨CGraph.johnsonTwoIso n⟩

/-- Any two of the three 2-subsets of `Fin 3` meet, so `T(3) = K₃`. -/
theorem triangular_three : triangular 3 = complete 3 := by
  show johnson 3 2 = complete 3
  rw [johnson_def, mk_eq_complete (G := CGraph.johnson 3 2) (by decide)]
  simp

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

/-- The cube graph is the four-rung prism. -/
theorem hypercube_three : hypercube 3 = prism 4 := by
  show hypercube 3 = cartesianProduct (cycle 4) (complete 2)
  rw [hypercube_succ, hypercube_two]

end IsoGraph
