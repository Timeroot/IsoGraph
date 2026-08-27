import IsoGraph.ForMathlib.Decide
import IsoGraph.ForMathlib.Nat
import IsoGraph.ForMathlib.Perm
import IsoGraph.ForMathlib.QuadraticChar
import IsoGraph.ForMathlib.ZMod
import IsoGraph.Invariants.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The graphs and the operations on them

The graphs everything else is built from: the empty graph, the complete graph, the path and the
cycle, together with the operations that combine them — complementation, the disjoint union, the
join, the four products, the line graph, the Mycielskian, blow-ups and the exponential.  Only the
definitions and the notation live here; the facts are in the topical files that follow.
-/

namespace CGraph

section
open Fintype

/-! ## Isomorphisms

Every construction below that takes a graph has to be shown to respect isomorphism before it
descends to `IsoGraph`; all of those congruences are the same shape — a bijection of vertices that
carries adjacency to adjacency — and they are all built from `isoOfAdj`.  They live in
`IsoGraph/Core/Quotient.lean`, next to the lifts they justify; only the tool is here. -/

/-- Build an isomorphism out of a bijection of vertices that carries adjacency to adjacency on
the nose.  For two concrete small graphs the hypothesis is a `decide`. -/
def isoOfAdj {G H : CGraph} (e : G.V ≃ H.V) (h : ∀ x y, H.Adj (e x) (e y) = G.Adj x y) :
    G ≃cg H := ⟨e, fun {a b} ↦ by rw [h]⟩

@[simp] theorem isoOfAdj_apply {G H : CGraph} (e : G.V ≃ H.V)
    (h : ∀ x y, H.Adj (e x) (e y) = G.Adj x y) (x : G.V) : isoOfAdj e h x = e x := rfl

/-- `Equiv.ofBijective`, computably: between finite types the inverse of a bijection can be found
by search, so an isomorphism built from one is data rather than a classical choice.  Vertex types
are finite with decidable equality, so this is the version to use on graphs. -/
def equivOfBijective {α β : Type} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun := Fintype.bijInv hf
  left_inv := Fintype.leftInverse_bijInv hf
  right_inv := Fintype.rightInverse_bijInv hf

@[simp] theorem equivOfBijective_apply {α β : Type} [Fintype α] [DecidableEq β] {f : α → β}
    (hf : Function.Bijective f) (x : α) : equivOfBijective hf x = f x := rfl

/-! ## The primitives -/

/-- A `CGraph` from an arbitrary relation: symmetrise it, and delete the diagonal.

This is the only place in the file where symmetry and irreflexivity are checked; nearly every
construction goes through it, and may pass a relation that is already symmetric and irreflexive
(in which case `ofRel` changes nothing). -/
def ofRel (V : Type) [FinEnum V] (r : V → V → Bool) : CGraph where
  V := V
  Adj x y := decide (x ≠ y) && (r x y || r y x)
  symm x y := by
    by_cases h : x = y
    · subst h; simp
    · cases r x y <;> cases r y x <;> simp [h, Ne.symm h]
  loopless x := by simp

@[simp] theorem ofRel_adj {V : Type} [FinEnum V] (r : V → V → Bool) (x y : V) :
    (ofRel V r).Adj x y = (decide (x ≠ y) && (r x y || r y x)) := rfl

@[simp] theorem card_ofRel (V : Type) [FinEnum V] (r : V → V → Bool) :
    FinEnum.card (ofRel V r).V = FinEnum.card V := rfl

/-- **How to recognise an `ofRel`.**  A graph *is* `ofRel V r` as soon as its adjacency agrees
with the symmetrisation of `r` off the diagonal.

Most constructions below are defined directly rather than through `ofRel`, because `ofRel` calls
`r` twice on every query and that factor of two compounds through nested constructions.  This
lemma is what lets each of them still be *described* by an `ofRel`, so that proofs may reason
with the symmetrised relation even though the compiled code never evaluates it. -/
theorem eq_ofRel (G : CGraph) (r : G.V → G.V → Bool)
    (h : ∀ x y, x ≠ y → G.Adj x y = (r x y || r y x)) : G = ofRel G.V r := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  show G.Adj x y = (decide (x ≠ y) && (r x y || r y x))
  by_cases hxy : x = y
  · subst hxy
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    exact Bool.eq_false_iff.2 (G.loopless x)
  · rw [h x y hxy]; simp [hxy]

/-- A `CGraph` on `Fin n` from a list of edges, given as pairs of numbers. -/
def ofEdges (n : ℕ) (es : List (ℕ × ℕ)) : CGraph :=
  ofRel (Fin n) fun i j ↦ es.contains (i.1, j.1)

@[simp] theorem card_ofEdges (n : ℕ) (es : List (ℕ × ℕ)) :
    FinEnum.card (ofEdges n es).V = n := rfl

/-- The edgeless graph on `n` vertices. -/
@[toIsoGraph]
def empty (n : ℕ) : CGraph where
  V := Fin n
  Adj _ _ := false
  symm _ _ := rfl
  loopless _ := by simp

instance (n : ℕ) : Nonempty (empty (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem empty_adj (n : ℕ) (i j : (empty n).V) : (empty n).Adj i j = false := rfl

@[simp] theorem card_empty (n : ℕ) : FinEnum.card (empty n).V = n := rfl

/-- The vertices of `empty n` are enumerated by themselves.  Tactics that take a vertex apart —
`fin_cases`, `decide` through `Finset.univ` — hand back `equiv.symm i` rather than `i`, and the
`Fin n` lemma cannot fire because the vertex type is not syntactically `Fin n`. -/
@[simp] theorem equiv_empty (n : ℕ) (i : (empty n).V) : FinEnum.equiv i = i := rfl

@[simp] theorem equiv_empty_symm (n : ℕ) (i : Fin n) :
    (FinEnum.equiv (α := (empty n).V)).symm i = i := rfl

/-- The complement: same vertices, edges exactly where there were none.

Written directly rather than as `ofRel G.V (!G.Adj · ·)`, which would query `G.Adj` twice per
edge; `compl_eq_ofRel` says the two agree. -/
def compl (G : CGraph) : CGraph where
  V := G.V
  Adj x y := decide (x ≠ y) && !G.Adj x y
  symm x y := by
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h, G.symm x y]
  loopless x := by simp

/-- Complementation is written `Gᶜ`, on graphs as on isomorphism classes. -/
instance : Compl CGraph := ⟨compl⟩

theorem compl_eq (G : CGraph) : Gᶜ = compl G := rfl

instance (G : CGraph) [Nonempty G.V] : Nonempty Gᶜ.V :=
  inferInstanceAs (Nonempty G.V)

theorem compl_eq_ofRel (G : CGraph) :
    Gᶜ = ofRel G.V fun x y ↦ !G.Adj x y :=
  eq_ofRel _ _ fun x y hxy => by simp [compl_eq, compl, hxy, G.symm x y]

@[simp] theorem compl_adj (G : CGraph) (x y : G.V) :
    Gᶜ.Adj x y = (decide (x ≠ y) && !G.Adj x y) := rfl

@[simp] theorem card_compl (G : CGraph) :
    FinEnum.card Gᶜ.V = FinEnum.card G.V := rfl

/-- Complementation respects isomorphism. -/
def Iso.compl {G G' : CGraph} (i : G ≃cg G') : Gᶜ ≃cg G'ᶜ :=
  isoOfAdj (G := Gᶜ) (H := G'ᶜ) i.toEquiv fun x y ↦ by
    show (decide (i x ≠ i y) && !G'.Adj (i x) (i y)) = (decide (x ≠ y) && !G.Adj x y)
    rw [i.adj_eq, show decide (i x ≠ i y) = decide (x ≠ y) from by simp]

end

end CGraph

namespace IsoGraph

section
open Fintype

/-- The complement of an isomorphism class: the complement of any representative. -/
def compl (G : IsoGraph) : IsoGraph :=
  Quotient.map (sa := CGraph.isoSetoid) (sb := CGraph.isoSetoid) CGraph.compl
    (fun _ _ ⟨i⟩ ↦ ⟨CGraph.Iso.compl i⟩) G

/-- Complementation is written `Gᶜ`, matching `Compl CGraph` on representatives.

Note that `⟦g⟧ᶜ` does not elaborate — instance search sees the type `Quotient CGraph.isoSetoid`
and will not unfold `IsoGraph` to reach it.  Write `(show IsoGraph from ⟦g⟧)ᶜ`; a type ascription
is *not* enough, since it leaves the inferred type unchanged. -/
instance : Compl IsoGraph := ⟨compl⟩

theorem compl_eq (G : IsoGraph) : Gᶜ = compl G := rfl

@[simp, isoTransfer] theorem compl_mk (G : CGraph) :
    (show IsoGraph from ⟦G⟧)ᶜ = ⟦Gᶜ⟧ := rfl

isograph_bridge CGraph.compl ↦ IsoGraph.compl via IsoGraph.compl_mk

end

end IsoGraph

namespace CGraph

section
open Fintype

/-- The disjoint union, on `G.V ⊕ H.V`.

This is the one construction that tests no vertex equality at all: the two sides are kept apart
by the `Sum` constructors, so it is built directly rather than through `ofRel`. -/
def disjUnion (G H : CGraph) : CGraph where
  V := G.V ⊕ H.V
  Adj x y :=
    match x, y with
    | .inl a, .inl c => G.Adj a c
    | .inr b, .inr d => H.Adj b d
    | _, _ => false
  symm x y := by
    cases x <;> cases y
    · exact G.symm _ _
    · rfl
    · rfl
    · exact H.symm _ _
  loopless x := by
    cases x with
    | inl a => exact G.loopless a
    | inr b => exact H.loopless b

/-! Each of the six binary operations gets one token, declared here beside the operation itself.
The tokens are the ones `IsoGraph/Core/Quotient.lean` already gives the operations on classes:
they are overloaded, and which of the two is meant is settled by the types of the arguments.  The
four products bind more tightly than the two sums, so `G ⊕g H □g K` is `G ⊕g (H □g K)`. -/

@[inherit_doc] infixl:60 " ⊕g " => CGraph.disjUnion

instance (G H : CGraph) [Nonempty G.V] : Nonempty (G ⊕g H).V :=
  inferInstanceAs (Nonempty (G.V ⊕ H.V))

@[simp] theorem disjUnion_adj_inl_inl (G H : CGraph) (a c : G.V) :
    (G ⊕g H).Adj (.inl a) (.inl c) = G.Adj a c := rfl

@[simp] theorem disjUnion_adj_inr_inr (G H : CGraph) (b d : H.V) :
    (G ⊕g H).Adj (.inr b) (.inr d) = H.Adj b d := rfl

@[simp] theorem disjUnion_adj_inl_inr (G H : CGraph) (a : G.V) (d : H.V) :
    (G ⊕g H).Adj (.inl a) (.inr d) = false := rfl

@[simp] theorem disjUnion_adj_inr_inl (G H : CGraph) (b : H.V) (c : G.V) :
    (G ⊕g H).Adj (.inr b) (.inl c) = false := rfl

@[simp] theorem card_disjUnion (G H : CGraph) :
    FinEnum.card (G ⊕g H).V = FinEnum.card G.V + FinEnum.card H.V := rfl

/-- The disjoint union of a finite family of graphs, on the sigma type.

The relation is already symmetric and loopless — two vertices in the same fibre are adjacent
exactly when they are adjacent in that fibre's graph — so it is used as-is rather than run
through `ofRel`; see `sigmaUnion_eq_ofRel`. -/
def sigmaUnion {ι : Type} [FinEnum ι] (F : ι → CGraph)
 : CGraph where
  V := Σ i, (F i).V
  Adj x y := if h : x.1 = y.1 then (F y.1).Adj (h ▸ x.2) y.2 else false
  symm x y := by
    obtain ⟨i, a⟩ := x
    obtain ⟨j, b⟩ := y
    by_cases h : i = j
    · subst h
      rw [dif_pos (rfl : i = i), dif_pos (rfl : i = i)]
      exact (F i).symm a b
    · rw [dif_neg h, dif_neg (Ne.symm h)]
  loopless x := by
    obtain ⟨i, a⟩ := x
    rw [dif_pos (rfl : i = i)]
    exact (F i).loopless a

@[simp] theorem sigmaUnion_adj_mk {ι : Type} [FinEnum ι] (F : ι → CGraph)
 (i : ι) (a b : (F i).V) :
    (sigmaUnion F).Adj ⟨i, a⟩ ⟨i, b⟩ = (F i).Adj a b := by
  show (if h : i = i then (F i).Adj (h ▸ a) b else false) = _
  rw [dif_pos (rfl : i = i)]

theorem sigmaUnion_adj_of_fst_ne {ι : Type} [FinEnum ι] (F : ι → CGraph)
 (x y : (sigmaUnion F).V) (h : x.1 ≠ y.1) :
    (sigmaUnion F).Adj x y = false := by
  show (if h : x.1 = y.1 then (F y.1).Adj (h ▸ x.2) y.2 else false) = _
  rw [dif_neg h]

@[simp] theorem sigmaUnion_adj_ne {ι : Type} [FinEnum ι] (F : ι → CGraph)
 (i j : ι) (a : (F i).V) (b : (F j).V) (h : i ≠ j) :
    (sigmaUnion F).Adj ⟨i, a⟩ ⟨j, b⟩ = false :=
  sigmaUnion_adj_of_fst_ne F ⟨i, a⟩ ⟨j, b⟩ h

theorem sigmaUnion_eq_ofRel {ι : Type} [FinEnum ι] (F : ι → CGraph)
 :
    sigmaUnion F = ofRel (Σ i, (F i).V) fun x y ↦
      if h : x.1 = y.1 then (F y.1).Adj (h ▸ x.2) y.2 else false := by
  refine eq_ofRel _ _ fun x y _ => ?_
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  by_cases h : i = j
  · subst h
    simp only [sigmaUnion_adj_mk]
    show (F i).Adj a b = ((F i).Adj a b || (F i).Adj b a)
    rw [(F i).symm b a, Bool.or_self]
  · simp only [sigmaUnion_adj_ne F i j a b h, dif_neg h, dif_neg (Ne.symm h), Bool.or_self]

@[simp] theorem card_sigmaUnion {ι : Type} [FinEnum ι] (F : ι → CGraph)
 :
    FinEnum.card (sigmaUnion F).V = ∑ i, FinEnum.card (F i).V := FinEnum.card_sigma _

/-! ## Built out of the primitives -/

/-- The complete graph on `n` vertices. -/
@[toIsoGraph]
def complete (n : ℕ) : CGraph := (empty n)ᶜ

instance (n : ℕ) : Nonempty (complete (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_complete (n : ℕ) : FinEnum.card (complete n).V = n := rfl

/-- As `equiv_empty`: complementation keeps the enumeration, so this is the identity too. -/
@[simp] theorem equiv_complete (n : ℕ) (i : (complete n).V) : FinEnum.equiv i = i := rfl

@[simp] theorem equiv_complete_symm (n : ℕ) (i : Fin n) :
    (FinEnum.equiv (α := (complete n).V)).symm i = i := rfl

/-- The join: a disjoint union together with every edge between the two parts. -/
def join (G H : CGraph) : CGraph :=
  (Gᶜ ⊕g Hᶜ)ᶜ

@[inherit_doc] infixl:60 " ∇g " => CGraph.join

@[simp] theorem card_join (G H : CGraph) :
    FinEnum.card (G ∇g H).V = FinEnum.card G.V + FinEnum.card H.V := rfl

@[simp] theorem join_adj_inl_inl (G H : CGraph) (a c : G.V) :
    (G ∇g H).Adj (.inl a) (.inl c) = G.Adj a c := by
  by_cases h : a = c
  · subst h
    simp [join, G.loopless a]
  · have hne : (Sum.inl a : G.V ⊕ H.V) ≠ Sum.inl c := fun h' ↦ h (Sum.inl.inj h')
    simp [join, h, hne]

@[simp] theorem join_adj_inr_inr (G H : CGraph) (b d : H.V) :
    (G ∇g H).Adj (.inr b) (.inr d) = H.Adj b d := by
  by_cases h : b = d
  · subst h
    simp [join, H.loopless b]
  · have hne : (Sum.inr b : G.V ⊕ H.V) ≠ Sum.inr d := fun h' ↦ h (Sum.inr.inj h')
    simp [join, h, hne]

@[simp] theorem join_adj_inl_inr (G H : CGraph)
    (a : G.V) (d : H.V) : (G ∇g H).Adj (.inl a) (.inr d) = true := by
  simp [join]

@[simp] theorem join_adj_inr_inl (G H : CGraph)
    (b : H.V) (c : G.V) : (G ∇g H).Adj (.inr b) (.inl c) = true := by
  simp [join]

/-! ## Paths, cycles and theta graphs -/

/-- The path on `n` vertices. -/
@[toIsoGraph]
def path (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ i.1 + 1 == j.1

instance (n : ℕ) : Nonempty (path (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_path (n : ℕ) : FinEnum.card (path n).V = n := rfl

/-- The cycle on `n` vertices.  For `n ≤ 2` this degenerates: `cycle 0` and `cycle 1` are
edgeless, and `cycle 2` is a single edge. -/
@[toIsoGraph]
def cycle (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ (i.1 + 1) % n == j.1

instance (n : ℕ) : Nonempty (cycle (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_cycle (n : ℕ) : FinEnum.card (cycle n).V = n := rfl

/-- The edges of the theta graph: vertex `0` and vertex `1` are the poles, and the `i`-th path
uses `xs[i]` fresh internal vertices starting at `off`. -/
def thetaEdges : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | off, 0 :: rest => (0, 1) :: thetaEdges off rest
  | off, (k + 1) :: rest =>
      ((0, off) :: (off + k, 1) :: (List.range k).map fun i ↦ (off + i, off + i + 1)) ++
        thetaEdges (off + k + 1) rest

/-! ## Trees, tadpoles and other decorated cycles

Everything here is an `ofEdges` over `Fin n`: these graphs are small and are meant to be *named*
and then evaluated, so the vertex type is kept flat rather than assembled out of `disjUnion`s. -/

/-- The edges of the path that visits the given vertices in order. -/
def pathEdges : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pathEdges (b :: rest)
  | _ => []

/-- The edges of the cycle `0, 1, …, m-1`. -/
def cycleEdges (m : ℕ) : List (ℕ × ℕ) := pathEdges (List.range m ++ [0])

/-- The edges of the complete graph on `0, 1, …, m-1`. -/
def cliqueEdges (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun i ↦ ((List.range m).filter (i < ·)).map (i, ·)

/-- The edges of a path of `k` fresh vertices `off, off+1, …` hanging off vertex `v`. -/
def legEdges (v off k : ℕ) : List (ℕ × ℕ) := pathEdges (v :: (List.range k).map (· + off))

/-- The legs of a spider: paths of the given lengths, all hanging off vertex `0`, using fresh
vertices from `off` on. -/
def spiderEdges : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | off, k :: rest => legEdges 0 off k ++ spiderEdges (off + k) rest

/-- Pendant vertices: `ks[i]` fresh vertices attached to vertex `v + i`, taken from `off` on. -/
def pendantEdges : ℕ → ℕ → List ℕ → List (ℕ × ℕ)
  | _, _, [] => []
  | v, off, k :: rest =>
      ((List.range k).map fun i ↦ (v, off + i)) ++ pendantEdges (v + 1) (off + k) rest

/-! ## Products

All four products live on `G.V × H.V` and differ only in the adjacency.  Three of the four
relations are loopless on the nose — the diagonal test they already carry sees to that — and all
four are symmetric, so none of them goes through `ofRel`; only the strong product, which *does*
put a loop at every vertex, has to delete the diagonal explicitly.

Writing them directly matters here more than anywhere else in the file: an `ofRel` calls its
relation twice, so an `n`-fold product built through `ofRel` would query the innermost factor
`2ⁿ` times — an overhead linear in the size of the graph.  The `*_eq_ofRel` lemmas recover the
`ofRel` description for proofs. -/

/-- The cartesian product `G □ H`: move in one coordinate, stay put in the other. -/
def cartesianProduct (G H : CGraph) : CGraph where
  V := G.V × H.V
  Adj p q := (decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2))
  symm p q := by
    rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1, decide_eq_comm p.2 q.2]
  loopless p := by simp [G.loopless p.1, H.loopless p.2]

/-- The tensor (categorical) product `G × H`: move in both coordinates. -/
def tensorProduct (G H : CGraph) : CGraph where
  V := G.V × H.V
  Adj p q := G.Adj p.1 q.1 && H.Adj p.2 q.2
  symm p q := by rw [G.symm p.1 q.1, H.symm p.2 q.2]
  loopless p := by simp [G.loopless p.1]

/-- The strong product `G ⊠ H`: the union of the cartesian and tensor products.

This is the one product whose relation holds on the diagonal, so the definition tests `p ≠ q`.
That test is on the vertex type, not the graphs: neither `G.Adj` nor `H.Adj` is queried twice. -/
def strongProduct (G H : CGraph) : CGraph where
  V := G.V × H.V
  Adj p q :=
    decide (p ≠ q) && ((decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2))
  symm p q := by
    rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1, decide_eq_comm p.2 q.2,
      decide_ne_comm p q]
  loopless p := by simp

/-- The lexicographic product `G[H]`: `G` on the first coordinate, and a copy of `H` inside each
fibre. -/
def lexProduct (G H : CGraph) : CGraph where
  V := G.V × H.V
  Adj p q := G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2)
  symm p q := by rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1]
  loopless p := by simp [G.loopless p.1, H.loopless p.2]

@[inherit_doc] infixl:70 " □g " => CGraph.cartesianProduct
@[inherit_doc] infixl:70 " ⊗g " => CGraph.tensorProduct
@[inherit_doc] infixl:70 " ⊠g " => CGraph.strongProduct
@[inherit_doc] infixl:70 " ·g " => CGraph.lexProduct

instance (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    Nonempty (G □g H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    Nonempty (G ⊗g H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    Nonempty (G ⊠g H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [Nonempty G.V] [Nonempty H.V] :
    Nonempty (G ·g H).V := inferInstanceAs (Nonempty (G.V × H.V))

@[simp] theorem card_cartesianProduct (G H : CGraph) :
    FinEnum.card (G □g H).V = FinEnum.card G.V * FinEnum.card H.V :=
  rfl

@[simp] theorem card_tensorProduct (G H : CGraph) :
    FinEnum.card (G ⊗g H).V = FinEnum.card G.V * FinEnum.card H.V :=
  rfl

@[simp] theorem card_strongProduct (G H : CGraph) :
    FinEnum.card (G ⊠g H).V = FinEnum.card G.V * FinEnum.card H.V :=
  rfl

@[simp] theorem card_lexProduct (G H : CGraph) :
    FinEnum.card (G ·g H).V = FinEnum.card G.V * FinEnum.card H.V :=
  rfl

@[simp] theorem cartesianProduct_adj (G H : CGraph)
    (p q : G.V × H.V) :
    (G □g H).Adj p q
      = ((decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2))) := rfl

@[simp] theorem tensorProduct_adj (G H : CGraph)
    (p q : G.V × H.V) :
    (G ⊗g H).Adj p q = (G.Adj p.1 q.1 && H.Adj p.2 q.2) := rfl

@[simp] theorem strongProduct_adj (G H : CGraph)
    (p q : G.V × H.V) :
    (G ⊠g H).Adj p q
      = (decide (p ≠ q) &&
          ((decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2))) := rfl

@[simp] theorem lexProduct_adj (G H : CGraph)
    (p q : G.V × H.V) :
    (G ·g H).Adj p q = (G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2)) := rfl

theorem cartesianProduct_eq_ofRel (G H : CGraph) :
    G □g H = ofRel (G.V × H.V) fun p q ↦
      (decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2)) :=
  eq_ofRel _ _ fun p q _ => by
    simp only [cartesianProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, decide_eq_comm q.2 p.2,
      Bool.or_self]

theorem tensorProduct_eq_ofRel (G H : CGraph) :
    G ⊗g H = ofRel (G.V × H.V) fun p q ↦ G.Adj p.1 q.1 && H.Adj p.2 q.2 :=
  eq_ofRel _ _ fun p q _ => by
    simp only [tensorProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, Bool.or_self]

theorem strongProduct_eq_ofRel (G H : CGraph) :
    G ⊠g H = ofRel (G.V × H.V) fun p q ↦
      (decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2) :=
  eq_ofRel _ _ fun p q hpq => by
    have h : decide (p ≠ q) = true := by simp [hpq]
    simp only [strongProduct_adj, h, Bool.true_and]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, decide_eq_comm q.2 p.2,
      Bool.or_self]

theorem lexProduct_eq_ofRel (G H : CGraph) :
    G ·g H = ofRel (G.V × H.V) fun p q ↦
      G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2) :=
  eq_ofRel _ _ fun p q _ => by
    simp only [lexProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, Bool.or_self]

/-! ## The exponential

The exponential is the internal hom of the tensor product in the category of graphs *with* loops,
where `Gᴴ` has the maps `H.V → G.V` for vertices and a loop at every homomorphism.  A `CGraph` is
loopless, so `G ^g H` is that graph with its diagonal deleted, and the deletion is what breaks the
laws: none of `(Gᴴ)ᴷ = G ^ (H ⊗ K)`, `G ^ (H ⊕ K) = Gᴴ ⊗ Gᴷ` or `(G ⊗ H)ᴷ = Gᴷ ⊗ Hᴷ` survives it —
see `IsoGraph/Algebra/Exponential.lean`, where the degenerate cases that do survive are
proved and the failures are witnessed.  The section after this one puts the loops back and gets
all three laws, over the strong product. -/

/-- The exponential graph `G ^g H`: the vertices are the maps `H.V → G.V`, and two distinct maps
`f`, `f'` are adjacent when every edge `u ~ v` of `H` is carried to an edge `f u ~ f' v` of `G`. -/
def exponential (G H : CGraph) : CGraph where
  V := H.V → G.V
  Adj f f' := decide (f ≠ f') && decide (∀ u v, H.Adj u v → G.Adj (f u) (f' v))
  symm f f' := by
    have h1 : decide (f ≠ f') = decide (f' ≠ f) := decide_eq_decide.2 ne_comm
    have h2 : decide (∀ u v, H.Adj u v → G.Adj (f u) (f' v))
        = decide (∀ u v, H.Adj u v → G.Adj (f' u) (f v)) := by
      refine decide_eq_decide.2 ⟨fun h u v huv ↦ ?_, fun h u v huv ↦ ?_⟩
      · rw [G.symm]; exact h v u (by rw [H.symm]; exact huv)
      · rw [G.symm]; exact h v u (by rw [H.symm]; exact huv)
    rw [h1, h2]
  loopless f := by simp

@[inherit_doc] infixr:75 " ^g " => CGraph.exponential

instance (G H : CGraph) [Nonempty G.V] : Nonempty (G ^g H).V :=
  inferInstanceAs (Nonempty (H.V → G.V))

@[simp] theorem card_exponential (G H : CGraph) :
    FinEnum.card (G ^g H).V = FinEnum.card G.V ^ FinEnum.card H.V := FinEnum.card_fun

@[simp] theorem exponential_adj (G H : CGraph) (f f' : H.V → G.V) :
    (G ^g H).Adj f f'
      = (decide (f ≠ f') && decide (∀ u v, H.Adj u v → G.Adj (f u) (f' v))) := rfl

/-! ## The reflexive exponential

What breaks the exponent laws is that a `CGraph` has no loops.  The repair is to put them back:
work with `adjR`, the adjacency of the graph with a loop added at every vertex, and take for
vertices not all the maps but the *homomorphisms* for that relation — the maps that send an edge
of the exponent to an edge or a fixed point of the base.  Every such map is `adjR`-adjacent to
itself, which is exactly the loop the plain exponential is missing, and deleting the diagonal then
costs nothing: `adjR_homExponential` says reflexive adjacency in `G ^hg H` is the defining
condition, on and off the diagonal alike.

This is the exponential of the category of *reflexive* graphs (Hell–Nešetřil, *Graphs and
Homomorphisms*, §2.6), where the categorical product of two reflexive graphs is the strong product
of their loopless shadows.  So the right adjoint here is the strong product, not the tensor
product, and the laws that fail for `^g` hold for `^hg` with `⊠g` throughout — see
`IsoGraph/Algebra/Exponential.lean`. -/

/-- `G.adjR x y`: `x` and `y` are equal or adjacent.  This is the adjacency of `G` with a loop
added at every vertex, and it is what the reflexive exponential `^hg` is built from. -/
def adjR (G : CGraph) (x y : G.V) : Bool := decide (x = y) || G.Adj x y

@[simp] theorem adjR_self (G : CGraph) (x : G.V) : G.adjR x x = true := by simp [adjR]

theorem adjR_comm (G : CGraph) (x y : G.V) : G.adjR x y = G.adjR y x := by
  rw [adjR, adjR, G.symm, decide_eq_comm]

theorem adjR_of_adj {G : CGraph} {x y : G.V} (h : G.Adj x y) : G.adjR x y := by simp [adjR, h]

/-- Adjacency is reflexive adjacency off the diagonal: the two determine each other. -/
theorem adj_eq_adjR (G : CGraph) (x y : G.V) : G.Adj x y = (decide (x ≠ y) && G.adjR x y) := by
  by_cases h : x = y
  · subst h; simp [(Bool.not_eq_true _).mp (G.loopless x)]
  · simp [adjR, h]

/-- `isoOfAdj` for reflexive adjacency: a bijection that carries `adjR` to `adjR` is an
isomorphism, since `adj_eq_adjR` recovers `Adj` from `adjR` and injectivity. -/
def isoOfAdjR {G H : CGraph} (e : G.V ≃ H.V) (h : ∀ x y, H.adjR (e x) (e y) = G.adjR x y) :
    G ≃cg H :=
  isoOfAdj e fun x y ↦ by
    rw [adj_eq_adjR, adj_eq_adjR, h]
    congr 1
    exact decide_eq_decide.2 (not_congr e.apply_eq_iff_eq)

theorem Iso.adjR_eq {G H : CGraph} (i : G ≃cg H) (x y : G.V) :
    H.adjR (i x) (i y) = G.adjR x y := by
  rw [adjR, adjR, i.adj_eq]
  congr 1
  exact decide_eq_decide.2 (RelIso.injective i).eq_iff

theorem Iso.adjR_symm_eq {G H : CGraph} (i : G ≃cg H) (x y : H.V) :
    G.adjR (i.symm x) (i.symm y) = H.adjR x y := by
  rw [← i.adjR_eq, i.apply_symm_apply, i.apply_symm_apply]

@[simp] theorem adjR_empty (n : ℕ) (x y : (empty n).V) : (empty n).adjR x y = decide (x = y) := by
  simp [adjR]

theorem adjR_disjUnion_inl (G H : CGraph) (x y : G.V) :
    (G ⊕g H).adjR (Sum.inl x) (Sum.inl y) = G.adjR x y := by simp [adjR, disjUnion]

theorem adjR_disjUnion_inr (G H : CGraph) (x y : H.V) :
    (G ⊕g H).adjR (Sum.inr x) (Sum.inr y) = H.adjR x y := by simp [adjR, disjUnion]

@[simp] theorem adjR_disjUnion_inl_inr (G H : CGraph) (x : G.V) (y : H.V) :
    (G ⊕g H).adjR (Sum.inl x) (Sum.inr y) = false := by simp [adjR, disjUnion]

@[simp] theorem adjR_disjUnion_inr_inl (G H : CGraph) (x : H.V) (y : G.V) :
    (G ⊕g H).adjR (Sum.inr x) (Sum.inl y) = false := by simp [adjR, disjUnion]

/-- **The strong product is the product of the reflexive adjacencies.**  This is the whole reason
the strong product is the one the reflexive exponential is adjoint to. -/
@[simp] theorem adjR_strongProduct (G H : CGraph) (p q : (G ⊠g H).V) :
    (G ⊠g H).adjR p q = (G.adjR p.1 q.1 && H.adjR p.2 q.2) := by
  by_cases h : p = q
  · subst h; simp
  · simp [adjR, h, strongProduct_adj]

/-- The reflexive exponential `G ^hg H`: the vertices are the homomorphisms `H → G` for the
reflexive adjacencies, and two distinct ones `f`, `f'` are adjacent when `f u` and `f' v` are
equal or adjacent for every `u`, `v` equal or adjacent in `H`. -/
def homExponential (G H : CGraph) : CGraph where
  V := {f : H.V → G.V // ∀ u v, H.adjR u v → G.adjR (f u) (f v)}
  Adj f f' := decide (f ≠ f') && decide (∀ u v, H.adjR u v → G.adjR (f.1 u) (f'.1 v))
  symm f f' := by
    have h1 : decide (f ≠ f') = decide (f' ≠ f) := decide_eq_decide.2 ne_comm
    have h2 : decide (∀ u v, H.adjR u v → G.adjR (f.1 u) (f'.1 v))
        = decide (∀ u v, H.adjR u v → G.adjR (f'.1 u) (f.1 v)) :=
      decide_eq_decide.2
        ⟨fun h u v huv ↦ by rw [G.adjR_comm]; exact h v u (by rw [H.adjR_comm]; exact huv),
          fun h u v huv ↦ by rw [G.adjR_comm]; exact h v u (by rw [H.adjR_comm]; exact huv)⟩
    rw [h1, h2]
  loopless f := by simp

@[inherit_doc] infixr:75 " ^hg " => CGraph.homExponential

@[simp] theorem homExponential_adj (G H : CGraph) (f f' : (G ^hg H).V) :
    (G ^hg H).Adj f f'
      = (decide (f ≠ f') && decide (∀ u v, H.adjR u v → G.adjR (f.1 u) (f'.1 v))) := rfl

/-- **Reflexive adjacency in `G ^hg H` is the defining condition**, with no diagonal test left
over: on the diagonal it is the property that makes a map a vertex in the first place.  Every
identity about `^hg` is this lemma plus a reindexing. -/
@[simp] theorem adjR_homExponential (G H : CGraph) (f f' : (G ^hg H).V) :
    (G ^hg H).adjR f f' = decide (∀ u v, H.adjR u v → G.adjR (f.1 u) (f'.1 v)) := by
  by_cases h : f = f'
  · subst h
    simp only [adjR, decide_true, Bool.true_or]
    exact (decide_eq_true f.2).symm
  · simp [adjR, h]

/-- The line graph: one vertex per edge of `G`, two of them adjacent when the edges meet.

Every edge meets itself, so the diagonal has to go; the meeting relation is symmetric as it
stands. -/
def lineGraph (G : CGraph) : CGraph where
  V := {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}
  Adj e f := decide (e ≠ f) && decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V))
  symm e f := by
    rw [decide_ne_comm e f]
    congr 1
    exact decide_eq_decide.2 ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩
  loopless e := by simp

@[simp] theorem lineGraph_adj (G : CGraph)
    (e f : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) :
    (lineGraph G).Adj e f
      = (decide (e ≠ f) && decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V))) := rfl

theorem lineGraph_eq_ofRel (G : CGraph) :
    lineGraph G = ofRel {e : Sym2 G.V // e ∈ G.toSimple.edgeSet} fun e f ↦
      decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V)) :=
  eq_ofRel _ _ fun e f hef => by
    have hcomm : decide (∃ v, v ∈ (f.1 : Sym2 G.V) ∧ v ∈ (e.1 : Sym2 G.V))
        = decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V)) :=
      decide_eq_decide.2 ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩
    rw [lineGraph_adj, decide_eq_true (by simpa using hef : e ≠ f), Bool.true_and, hcomm,
      Bool.or_self]

/-- The Mycielskian of `G`: a copy of `G`, a *shadow* `v'` of each vertex `v` joined to the
neighbours of `v`, and one apex joined to every shadow.  It raises the chromatic number by one
without creating a triangle. -/
def mycielskian (G : CGraph) : CGraph where
  V := Option (G.V ⊕ G.V)
  Adj x y :=
    match x, y with
    | some (.inl a), some (.inl b) => G.Adj a b
    | some (.inl a), some (.inr b) => G.Adj a b
    | some (.inr a), some (.inl b) => G.Adj a b
    | none, some (.inr _) => true
    | some (.inr _), none => true
    | _, _ => false
  symm x y := by
    rcases x with _ | (a | a) <;> rcases y with _ | (b | b) <;>
      first
        | rfl
        | exact G.symm _ _
  loopless x := by
    rcases x with _ | (a | a)
    · simp
    · exact G.loopless a
    · simp

@[simp] theorem mycielskian_adj_inl_inl (G : CGraph) (a b : G.V) :
    (mycielskian G).Adj (some (.inl a)) (some (.inl b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inl_inr (G : CGraph) (a b : G.V) :
    (mycielskian G).Adj (some (.inl a)) (some (.inr b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inr_inl (G : CGraph) (a b : G.V) :
    (mycielskian G).Adj (some (.inr a)) (some (.inl b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inr_inr (G : CGraph) (a b : G.V) :
    (mycielskian G).Adj (some (.inr a)) (some (.inr b)) = false := rfl

@[simp] theorem mycielskian_adj_none_inl (G : CGraph) (b : G.V) :
    (mycielskian G).Adj none (some (.inl b)) = false := rfl

@[simp] theorem mycielskian_adj_none_inr (G : CGraph) (b : G.V) :
    (mycielskian G).Adj none (some (.inr b)) = true := rfl

@[simp] theorem mycielskian_adj_inl_none (G : CGraph) (a : G.V) :
    (mycielskian G).Adj (some (.inl a)) none = false := rfl

@[simp] theorem mycielskian_adj_inr_none (G : CGraph) (a : G.V) :
    (mycielskian G).Adj (some (.inr a)) none = true := rfl

@[simp] theorem mycielskian_adj_none_none (G : CGraph) :
    (mycielskian G).Adj none none = false := rfl

theorem mycielskian_eq_ofRel (G : CGraph) :
    mycielskian G = ofRel (Option (G.V ⊕ G.V)) fun x y ↦
      match x, y with
      | some (.inl a), some (.inl b) => G.Adj a b
      | some (.inl a), some (.inr b) => G.Adj a b
      | some (.inr a), some (.inl b) => G.Adj a b
      | none, some (.inr _) => true
      | some (.inr _), none => true
      | _, _ => false :=
  eq_ofRel _ _ fun x y _ => by
    rcases x with _ | (a | a) <;> rcases y with _ | (b | b) <;>
      simp only [mycielskian_adj_inl_inl, mycielskian_adj_inl_inr, mycielskian_adj_inr_inl,
        mycielskian_adj_inr_inr, mycielskian_adj_none_inl, mycielskian_adj_none_inr,
        mycielskian_adj_inl_none, mycielskian_adj_inr_none, mycielskian_adj_none_none,
        Bool.or_self] <;>
      first
        | rfl
        | rw [G.symm b a, Bool.or_self]

/-- **Seidel switching** with respect to a set `S` of vertices: complement every edge between `S`
and its complement, leaving the edges inside `S` and inside its complement alone.

Switching does not change the vertex type, and it preserves neither the degree sequence nor the
isomorphism class in general — but it does act on *Seidel switching classes*, and applying it to
the triangular graph `T(8)` produces the three Chang graphs. -/
def seidelSwitch (G : CGraph) (S : G.V → Bool) : CGraph where
  V := G.V
  Adj x y := G.Adj x y ^^ (S x ^^ S y)
  symm x y := by rw [G.symm x y, Bool.xor_comm (S x) (S y)]
  loopless x := by simp [G.loopless x]

@[simp] theorem seidelSwitch_adj (G : CGraph) (S : G.V → Bool) (x y : G.V) :
    (seidelSwitch G S).Adj x y = (G.Adj x y ^^ (S x ^^ S y)) := rfl

@[simp] theorem card_seidelSwitch (G : CGraph) (S : G.V → Bool) :
    FinEnum.card (seidelSwitch G S).V = FinEnum.card G.V := rfl

/-- Switching twice with the same set is the identity. -/
@[simp] theorem seidelSwitch_seidelSwitch (G : CGraph) (S : G.V → Bool) :
    seidelSwitch (seidelSwitch G S) S = G := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  show ((G.Adj x y ^^ (S x ^^ S y)) ^^ (S x ^^ S y)) = G.Adj x y
  cases G.Adj x y <;> cases S x <;> cases S y <;> rfl

/-! ## Graph codes

Two families given by a code rather than by a formula: an LCF code, and the pair `(n, k)` of a
generalized Petersen graph.  Both produce a graph on `Fin n`, numbered so that the back-edge
certificate for connectivity of `IsoGraph/Invariants/Certificates.lean` holds on the nose. -/

/-- Vertex number `i` of a graph on `Fin n`, for naming the corners of a triangle, square or
pentagon.  The bound is `Nat.mod_lt`. -/
abbrev vtx (n : ℕ) [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- The edges of the LCF code `[ss]^r`: the Hamiltonian cycle `0 - 1 - ⋯ - (n-1) - 0` on
`n = ss.length * r` vertices, together with the chord from `i` to `i + ss[i mod ss.length]`. -/
def lcfEdges (ss : List ℤ) (r : ℕ) : List (ℕ × ℕ) :=
  (List.range (ss.length * r)).flatMap fun i ↦
    [(i, (i + 1) % (ss.length * r)),
      (i, ((((i : ℤ) + ss.getD (i % ss.length) 0) % (ss.length * r : ℕ)
              + (ss.length * r : ℕ)) % (ss.length * r : ℕ)).toNat)]

/-- The edges of the generalized Petersen graph `GP(n, k)`: an outer `n`-cycle on `0 … n-1`, an
inner circulant `n + i ~ n + (i + k)` on `n … 2n-1`, and the spokes `i ~ n + i`. -/
def gpEdges (n k : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ [(i, (i + 1) % n), (i, n + i), (n + i, n + (i + k) % n)]

end

end CGraph
