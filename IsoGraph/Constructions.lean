import IsoGraph.Invariants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Constructions

Ways of building a `CGraph`.  Everything here is a plain definition — no `Classical.choice` — so
every graph in this file can be handed to `CGraph.canonicalize` and actually run.

The guiding principle is the one from `isograph_draft.txt`: build the zoo out of a very small
number of primitives.  `ofRel` symmetrises an arbitrary `Bool`-valued relation and deletes the
diagonal, so it is the only place where symmetry and irreflexivity have to be arranged by hand;
`empty`, `disjUnion` and `compl` then generate most of the rest —

```
complete n           = compl (empty n)
join G H             = compl (disjUnion (compl G) (compl H))
bipartite m n        = compl (disjUnion (complete m) (complete n))
completeMultipartite = compl (sigmaUnion of completes)
star n               = bipartite 1 n
wheel n              = join (complete 1) (cycle n)
```

## `DecidableEq`

A `CGraph` carries a `Fintype` instance but no `DecidableEq`, and the latter does *not* follow
from the former.  Any construction that has to ask "is this the same vertex?" — the complement,
the cartesian/strong/lexicographic products, the line graph — therefore takes `[DecidableEq G.V]`
as an instance argument.  Each construction then exports the instance for *its* vertex type, so
the derived definitions above compose without the caller ever seeing it.

Putting `DecidableEq` into the `CGraph` structure itself would avoid the boilerplate, at the cost
of making the type no longer a bare `Fintype`-bundled graph (and of breaking `simpleEquiv`); the
instance arguments seemed the smaller price.

## Layout

The definitions come first; the section after them, `## Invariants of the constructions`, records
what the invariants of `IsoGraph/Invariants.lean` evaluate to.
-/

open Fintype

namespace CGraph

/-! ## The primitives -/

/-- A `CGraph` from an arbitrary relation: symmetrise it, and delete the diagonal.

This is the only place in the file where symmetry and irreflexivity are checked; every construction
whose vertex type has a `DecidableEq` goes through it, and may pass a relation that is already
symmetric and irreflexive (in which case `ofRel` changes nothing). -/
def ofRel (V : Type) [Fintype V] [DecidableEq V] (r : V → V → Bool) : CGraph where
  V := V
  Adj x y := decide (x ≠ y) && (r x y || r y x)
  symm x y := by
    by_cases h : x = y
    · subst h; simp
    · cases r x y <;> cases r y x <;> simp [h, Ne.symm h]
  loopless x := by simp

instance instDecidableEqOfRel (V : Type) [Fintype V] [DecidableEq V] (r : V → V → Bool) :
    DecidableEq (ofRel V r).V := inferInstanceAs (DecidableEq V)

@[simp] theorem ofRel_adj {V : Type} [Fintype V] [DecidableEq V] (r : V → V → Bool) (x y : V) :
    (ofRel V r).Adj x y = (decide (x ≠ y) && (r x y || r y x)) := rfl

@[simp] theorem card_ofRel (V : Type) [Fintype V] [DecidableEq V] (r : V → V → Bool) :
    Fintype.card (ofRel V r).V = Fintype.card V := rfl

/-- `decide` of an equality is symmetric.  Stated as a `Bool` equation rather than reached
through `eq_comm`, so that `rw` can use it inside a `decide` without a motive problem. -/
theorem decide_eq_comm {α : Type} [DecidableEq α] (a b : α) :
    decide (a = b) = decide (b = a) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- `decide` of a disequality is symmetric; the companion of `decide_eq_comm`. -/
theorem decide_ne_comm {α : Type} [DecidableEq α] (a b : α) :
    decide (a ≠ b) = decide (b ≠ a) := by
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- **How to recognise an `ofRel`.**  A graph *is* `ofRel V r` as soon as its adjacency agrees
with the symmetrisation of `r` off the diagonal.

Most constructions below are defined directly rather than through `ofRel`, because `ofRel` calls
`r` twice on every query and that factor of two compounds through nested constructions.  This
lemma is what lets each of them still be *described* by an `ofRel`, so that proofs may reason
with the symmetrised relation even though the compiled code never evaluates it. -/
theorem eq_ofRel (G : CGraph) [DecidableEq G.V] (r : G.V → G.V → Bool)
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

instance (n : ℕ) (es : List (ℕ × ℕ)) : DecidableEq (ofEdges n es).V :=
  inferInstanceAs (DecidableEq (Fin n))

@[simp] theorem card_ofEdges (n : ℕ) (es : List (ℕ × ℕ)) :
    Fintype.card (ofEdges n es).V = n := Fintype.card_fin n

/-- The edgeless graph on `n` vertices. -/
def empty (n : ℕ) : CGraph where
  V := Fin n
  Adj _ _ := false
  symm _ _ := rfl
  loopless _ := by simp

instance (n : ℕ) : DecidableEq (empty n).V := inferInstanceAs (DecidableEq (Fin n))

instance (n : ℕ) : Nonempty (empty (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem empty_adj (n : ℕ) (i j : (empty n).V) : (empty n).Adj i j = false := rfl

@[simp] theorem card_empty (n : ℕ) : Fintype.card (empty n).V = n := Fintype.card_fin n

/-- The complement: same vertices, edges exactly where there were none.

Written directly rather than as `ofRel G.V (!G.Adj · ·)`, which would query `G.Adj` twice per
edge; `compl_eq_ofRel` says the two agree. -/
def compl (G : CGraph) [DecidableEq G.V] : CGraph where
  V := G.V
  Adj x y := decide (x ≠ y) && !G.Adj x y
  symm x y := by
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h, G.symm x y]
  loopless x := by simp

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (compl G).V :=
  inferInstanceAs (DecidableEq G.V)

instance (G : CGraph) [DecidableEq G.V] [Nonempty G.V] : Nonempty (compl G).V :=
  inferInstanceAs (Nonempty G.V)

theorem compl_eq_ofRel (G : CGraph) [DecidableEq G.V] :
    compl G = ofRel G.V fun x y ↦ !G.Adj x y :=
  eq_ofRel _ _ fun x y hxy => by simp [compl, hxy, G.symm x y]

@[simp] theorem compl_adj (G : CGraph) [DecidableEq G.V] (x y : G.V) :
    (compl G).Adj x y = (decide (x ≠ y) && !G.Adj x y) := rfl

@[simp] theorem card_compl (G : CGraph) [DecidableEq G.V] :
    Fintype.card (compl G).V = Fintype.card G.V := rfl

/-- The disjoint union, on `G.V ⊕ H.V`.

This is the one construction that needs no `DecidableEq`: the two sides are kept apart by the
`Sum` constructors rather than by an equality test. -/
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

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : DecidableEq (disjUnion G H).V :=
  inferInstanceAs (DecidableEq (G.V ⊕ H.V))

instance (G H : CGraph) [Nonempty G.V] : Nonempty (disjUnion G H).V :=
  inferInstanceAs (Nonempty (G.V ⊕ H.V))

@[simp] theorem disjUnion_adj_inl_inl (G H : CGraph) (a c : G.V) :
    (disjUnion G H).Adj (.inl a) (.inl c) = G.Adj a c := rfl

@[simp] theorem disjUnion_adj_inr_inr (G H : CGraph) (b d : H.V) :
    (disjUnion G H).Adj (.inr b) (.inr d) = H.Adj b d := rfl

@[simp] theorem disjUnion_adj_inl_inr (G H : CGraph) (a : G.V) (d : H.V) :
    (disjUnion G H).Adj (.inl a) (.inr d) = false := rfl

@[simp] theorem disjUnion_adj_inr_inl (G H : CGraph) (b : H.V) (c : G.V) :
    (disjUnion G H).Adj (.inr b) (.inl c) = false := rfl

@[simp] theorem card_disjUnion (G H : CGraph) :
    Fintype.card (disjUnion G H).V = Fintype.card G.V + Fintype.card H.V := Fintype.card_sum

/-- The disjoint union of a finite family of graphs, on the sigma type.

The relation is already symmetric and loopless — two vertices in the same fibre are adjacent
exactly when they are adjacent in that fibre's graph — so it is used as-is rather than run
through `ofRel`; see `sigmaUnion_eq_ofRel`. -/
def sigmaUnion {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] : CGraph where
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

instance {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph) [∀ i, DecidableEq (F i).V] :
    DecidableEq (sigmaUnion F).V := inferInstanceAs (DecidableEq (Σ i, (F i).V))

@[simp] theorem sigmaUnion_adj_mk {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] (i : ι) (a b : (F i).V) :
    (sigmaUnion F).Adj ⟨i, a⟩ ⟨i, b⟩ = (F i).Adj a b := by
  show (if h : i = i then (F i).Adj (h ▸ a) b else false) = _
  rw [dif_pos (rfl : i = i)]

theorem sigmaUnion_adj_of_fst_ne {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] (x y : (sigmaUnion F).V) (h : x.1 ≠ y.1) :
    (sigmaUnion F).Adj x y = false := by
  show (if h : x.1 = y.1 then (F y.1).Adj (h ▸ x.2) y.2 else false) = _
  rw [dif_neg h]

@[simp] theorem sigmaUnion_adj_ne {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] (i j : ι) (a : (F i).V) (b : (F j).V) (h : i ≠ j) :
    (sigmaUnion F).Adj ⟨i, a⟩ ⟨j, b⟩ = false :=
  sigmaUnion_adj_of_fst_ne F ⟨i, a⟩ ⟨j, b⟩ h

theorem sigmaUnion_eq_ofRel {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] :
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

@[simp] theorem card_sigmaUnion {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] :
    Fintype.card (sigmaUnion F).V = ∑ i, Fintype.card (F i).V := Fintype.card_sigma

/-! ## Built out of the primitives -/

/-- The complete graph on `n` vertices. -/
def complete (n : ℕ) : CGraph := compl (empty n)

instance (n : ℕ) : DecidableEq (complete n).V := inferInstanceAs (DecidableEq (Fin n))

instance (n : ℕ) : Nonempty (complete (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_complete (n : ℕ) : Fintype.card (complete n).V = n := Fintype.card_fin n

/-- The join: a disjoint union together with every edge between the two parts. -/
def join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  compl (disjUnion (compl G) (compl H))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : DecidableEq (join G H).V :=
  inferInstanceAs (DecidableEq (G.V ⊕ H.V))

@[simp] theorem card_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (join G H).V = Fintype.card G.V + Fintype.card H.V := Fintype.card_sum

@[simp] theorem join_adj_inl_inl (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (a c : G.V) :
    (join G H).Adj (.inl a) (.inl c) = G.Adj a c := by
  by_cases h : a = c
  · subst h
    simp [join, G.loopless a]
  · have hne : (Sum.inl a : G.V ⊕ H.V) ≠ Sum.inl c := fun h' ↦ h (Sum.inl.inj h')
    simp [join, h, hne]

@[simp] theorem join_adj_inr_inr (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] (b d : H.V) :
    (join G H).Adj (.inr b) (.inr d) = H.Adj b d := by
  by_cases h : b = d
  · subst h
    simp [join, H.loopless b]
  · have hne : (Sum.inr b : G.V ⊕ H.V) ≠ Sum.inr d := fun h' ↦ h (Sum.inr.inj h')
    simp [join, h, hne]

@[simp] theorem join_adj_inl_inr (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (a : G.V) (d : H.V) : (join G H).Adj (.inl a) (.inr d) = true := by
  simp [join]

@[simp] theorem join_adj_inr_inl (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (b : H.V) (c : G.V) : (join G H).Adj (.inr b) (.inl c) = true := by
  simp [join]

/-- The complete bipartite graph `K_{m,n}`. -/
def bipartite (m n : ℕ) : CGraph := compl (disjUnion (complete m) (complete n))

instance (m n : ℕ) : DecidableEq (bipartite m n).V :=
  inferInstanceAs (DecidableEq (Fin m ⊕ Fin n))

instance (m n : ℕ) : Nonempty (bipartite (m + 1) n).V :=
  inferInstanceAs (Nonempty (Fin (m + 1) ⊕ Fin n))

@[simp] theorem card_bipartite (m n : ℕ) : Fintype.card (bipartite m n).V = m + n := by
  simp [bipartite]

@[simp] theorem bipartite_adj_inl_inl (m n : ℕ) (a c : Fin m) :
    (bipartite m n).Adj (.inl a) (.inl c) = false := by
  by_cases h : a = c <;> simp [bipartite, complete, compl, h]

@[simp] theorem bipartite_adj_inr_inr (m n : ℕ) (b d : Fin n) :
    (bipartite m n).Adj (.inr b) (.inr d) = false := by
  by_cases h : b = d <;> simp [bipartite, complete, compl, h]

@[simp] theorem bipartite_adj_inl_inr (m n : ℕ) (a : Fin m) (d : Fin n) :
    (bipartite m n).Adj (.inl a) (.inr d) = true := by
  simp [bipartite, compl]

@[simp] theorem bipartite_adj_inr_inl (m n : ℕ) (b : Fin n) (c : Fin m) :
    (bipartite m n).Adj (.inr b) (.inl c) = true := by
  simp [bipartite, compl]

/-- The complete multipartite graph with parts of sizes `ds`. -/
def completeMultipartite (ds : List ℕ) : CGraph :=
  compl (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))

instance (ds : List ℕ) : DecidableEq (completeMultipartite ds).V :=
  inferInstanceAs (DecidableEq (Σ i : Fin ds.length, (complete (ds.get i)).V))

/-- The star with `n` leaves. -/
def star (n : ℕ) : CGraph := bipartite 1 n

instance (n : ℕ) : DecidableEq (star n).V := inferInstanceAs (DecidableEq (bipartite 1 n).V)

instance (n : ℕ) : Nonempty (star n).V := inferInstanceAs (Nonempty (bipartite (0 + 1) n).V)

/-! ## Paths, cycles and theta graphs -/

/-- The path on `n` vertices. -/
def path (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ i.1 + 1 == j.1

instance (n : ℕ) : DecidableEq (path n).V := inferInstanceAs (DecidableEq (Fin n))

instance (n : ℕ) : Nonempty (path (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_path (n : ℕ) : Fintype.card (path n).V = n := Fintype.card_fin n

/-- The cycle on `n` vertices.  For `n ≤ 2` this degenerates: `cycle 0` and `cycle 1` are
edgeless, and `cycle 2` is a single edge. -/
def cycle (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ (i.1 + 1) % n == j.1

instance (n : ℕ) : DecidableEq (cycle n).V := inferInstanceAs (DecidableEq (Fin n))

instance (n : ℕ) : Nonempty (cycle (n + 1)).V := inferInstanceAs (Nonempty (Fin (n + 1)))

@[simp] theorem card_cycle (n : ℕ) : Fintype.card (cycle n).V = n := Fintype.card_fin n

/-- The wheel: a cycle plus a hub joined to all of it. -/
def wheel (n : ℕ) : CGraph := join (complete 1) (cycle n)

instance (n : ℕ) : DecidableEq (wheel n).V :=
  inferInstanceAs (DecidableEq (join (complete 1) (cycle n)).V)

/-- The edges of the theta graph: vertex `0` and vertex `1` are the poles, and the `i`-th path
uses `xs[i]` fresh internal vertices starting at `off`. -/
def thetaEdges : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | off, 0 :: rest => (0, 1) :: thetaEdges off rest
  | off, (k + 1) :: rest =>
      ((0, off) :: (off + k, 1) :: (List.range k).map fun i ↦ (off + i, off + i + 1)) ++
        thetaEdges (off + k + 1) rest

/-- The theta graph: two poles joined by `xs.length` internally disjoint paths, the `i`-th of
which has `xs[i]` internal vertices (so `Θ(a,b,c)` in the usual notation is
`thetaGraph [a-1, b-1, c-1]`).  A `0` in the list contributes the single edge between the two
poles, so at most one `0` is meaningful. -/
def thetaGraph (xs : List ℕ) : CGraph := ofEdges (2 + xs.sum) (thetaEdges 2 xs)

instance (xs : List ℕ) : DecidableEq (thetaGraph xs).V :=
  inferInstanceAs (DecidableEq (Fin (2 + xs.sum)))

@[simp] theorem card_thetaGraph (xs : List ℕ) :
    Fintype.card (thetaGraph xs).V = 2 + xs.sum := Fintype.card_fin _

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

/-- The tadpole (or pan) graph `T(m,k)`: the cycle on `m` vertices with a path of `k` further
vertices attached to it.  `tadpole m 0` is `cycle m` and `tadpole 4 1` is the banner. -/
def tadpole (m k : ℕ) : CGraph := ofEdges (m + k) (cycleEdges m ++ legEdges 0 m k)

instance (m k : ℕ) : DecidableEq (tadpole m k).V := inferInstanceAs (DecidableEq (Fin (m + k)))

@[simp] theorem card_tadpole (m k : ℕ) : Fintype.card (tadpole m k).V = m + k := Fintype.card_fin _

/-- The lollipop graph `L(m,k)`: `Kₘ` with a path of `k` further vertices attached to it. -/
def lollipop (m k : ℕ) : CGraph := ofEdges (m + k) (cliqueEdges m ++ legEdges 0 m k)

instance (m k : ℕ) : DecidableEq (lollipop m k).V := inferInstanceAs (DecidableEq (Fin (m + k)))

@[simp] theorem card_lollipop (m k : ℕ) :
    Fintype.card (lollipop m k).V = m + k := Fintype.card_fin _

/-- The legs of a spider: paths of the given lengths, all hanging off vertex `0`, using fresh
vertices from `off` on. -/
def spiderEdges : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | off, k :: rest => legEdges 0 off k ++ spiderEdges (off + k) rest

/-- The spider (or generalised star) `S(legs)`: a centre with paths of the given lengths hanging
off it.  `spider [1, 1, …, 1]` is a star and `spider [a, b]` is a path. -/
def spider (legs : List ℕ) : CGraph := ofEdges (1 + legs.sum) (spiderEdges 1 legs)

instance (legs : List ℕ) : DecidableEq (spider legs).V :=
  inferInstanceAs (DecidableEq (Fin (1 + legs.sum)))

@[simp] theorem card_spider (legs : List ℕ) :
    Fintype.card (spider legs).V = 1 + legs.sum := Fintype.card_fin _

/-- The double star `S(m,n)`: an edge with `m` pendant vertices on one end and `n` on the
other. -/
def doubleStar (m n : ℕ) : CGraph :=
  ofEdges (2 + m + n) ((0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
    ((List.range n).map fun i ↦ (1, 2 + m + i))))

instance (m n : ℕ) : DecidableEq (doubleStar m n).V :=
  inferInstanceAs (DecidableEq (Fin (2 + m + n)))

@[simp] theorem card_doubleStar (m n : ℕ) :
    Fintype.card (doubleStar m n).V = 2 + m + n := Fintype.card_fin _

/-- Pendant vertices: `ks[i]` fresh vertices attached to vertex `v + i`, taken from `off` on. -/
def pendantEdges : ℕ → ℕ → List ℕ → List (ℕ × ℕ)
  | _, _, [] => []
  | v, off, k :: rest =>
      ((List.range k).map fun i ↦ (v, off + i)) ++ pendantEdges (v + 1) (off + k) rest

/-- The cycle on `m` vertices with `ks[i]` pendant vertices attached to vertex `i`.  The paw is
`cyclePendant 3 [1]`, the bull is `cyclePendant 3 [1, 1]` and the net is
`cyclePendant 3 [1, 1, 1]`. -/
def cyclePendant (m : ℕ) (ks : List ℕ) : CGraph :=
  ofEdges (m + ks.sum) (cycleEdges m ++ pendantEdges 0 m ks)

instance (m : ℕ) (ks : List ℕ) : DecidableEq (cyclePendant m ks).V :=
  inferInstanceAs (DecidableEq (Fin (m + ks.sum)))

@[simp] theorem card_cyclePendant (m : ℕ) (ks : List ℕ) :
    Fintype.card (cyclePendant m ks).V = m + ks.sum := Fintype.card_fin _

/-! ## Cayley graphs

A group and a connection set.  `ofRel` symmetrises, so the connection set does *not* have to be
closed under negation — passing `S` and passing `S ∪ -S` give the same graph — and a `0 ∈ S` does
no harm either, since `ofRel` deletes the diagonal. -/

/-- The Cayley graph of a finite additive group `A` with connection set `S`: `x ~ y` when
`y - x ∈ S`.  Left translation is an automorphism, so this is always vertex-transitive. -/
def cayleyAdd (A : Type) [Fintype A] [DecidableEq A] [AddGroup A] (S : A → Bool) : CGraph :=
  ofRel A fun x y ↦ S (y - x)

instance (A : Type) [Fintype A] [DecidableEq A] [AddGroup A] (S : A → Bool) :
    DecidableEq (cayleyAdd A S).V := inferInstanceAs (DecidableEq A)

@[simp] theorem cayleyAdd_adj (A : Type) [Fintype A] [DecidableEq A] [AddGroup A] (S : A → Bool)
    (x y : A) : (cayleyAdd A S).Adj x y = (decide (x ≠ y) && (S (y - x) || S (x - y))) := rfl

@[simp] theorem card_cayleyAdd (A : Type) [Fintype A] [DecidableEq A] [AddGroup A] (S : A → Bool) :
    Fintype.card (cayleyAdd A S).V = Fintype.card A := rfl

/-- The circulant on `Fin n` with connection set `S`, taken mod `n`: the Cayley graph of `ℤ/n`,
written on `Fin n` so that no `NeZero` instance is needed.  `cycle n = circulant n [1]`. -/
def circulant (n : ℕ) (S : List ℕ) : CGraph :=
  ofRel (Fin n) fun x y ↦ S.contains ((y.1 + n - x.1) % n)

instance (n : ℕ) (S : List ℕ) : DecidableEq (circulant n S).V :=
  inferInstanceAs (DecidableEq (Fin n))

@[simp] theorem card_circulant (n : ℕ) (S : List ℕ) :
    Fintype.card (circulant n S).V = n := Fintype.card_fin n

@[simp] theorem circulant_nil (n : ℕ) : circulant n [] = empty n :=
  (eq_ofRel (empty n) (fun _ _ ↦ false) fun _ _ _ ↦ rfl).symm

/-- The arithmetic behind `circulant_one_eq_cycle`: for distinct `a, b < n`, the difference
`b - a` is `1` mod `n` exactly when `b` is the successor of `a` mod `n`.  Distinctness is needed
only for `n = 1`, where `a = b = 0` is its own successor but has difference `0`. -/
private theorem mod_add_sub_eq_one_iff {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (b + n - a) % n = 1 ↔ (a + 1) % n = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [show b + n - a = b - a + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : b - a < n)]
    rcases Nat.lt_or_ge (a + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show a + 1 = n by omega, Nat.mod_self]; omega
  · exact absurd h hab
  · rw [show b + n - a = n - (a - b) by omega,
      Nat.mod_eq_of_lt (by omega : n - (a - b) < n)]
    rcases Nat.lt_or_ge (a + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show a + 1 = n by omega, Nat.mod_self]; omega

/-- **The cycle is the circulant with connection set `{1}`** — an equality of `CGraph`s, not just
of isomorphism classes, since both are `ofRel` on `Fin n`. -/
theorem circulant_one_eq_cycle (n : ℕ) : circulant n [1] = cycle n := by
  refine (eq_ofRel (circulant n [1]) (fun i j ↦ (i.1 + 1) % n == j.1) fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  have key : ∀ a b : Fin n, a.1 ≠ b.1 →
      ([1].contains ((b.1 + n - a.1) % n)) = ((a.1 + 1) % n == b.1) := fun a b hab ↦ by
    have h := mod_add_sub_eq_one_iff a.2 b.2 hab
    rw [show ([1].contains ((b.1 + n - a.1) % n)) = decide ((b.1 + n - a.1) % n = 1) by simp,
      Bool.beq_eq_decide_eq]
    exact decide_eq_decide.2 h
  show (decide (x ≠ y) && ([1].contains ((y.1 + n - x.1) % n) ||
    [1].contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and, key x y hne, key y x (Ne.symm hne)]

/-- The nonzero quadratic residues mod `q`, as a lookup table — computed once, so that the Paley
graph answers an adjacency query with one array read.

Written as an `Array.ofFn` over the *defining* predicate rather than by scattering `i * i % q`
into a mutable array: building the table then costs `O(q²)` instead of `O(q)`, which is nothing
next to the `O(q²)` adjacency matrix it feeds, and in exchange `qrTable_getElem` reads off an
entry with no reasoning about `Array.set!` at all. -/
private def qrTable (q : ℕ) : Array Bool :=
  Array.ofFn (n := q) fun d ↦ decide (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = d.1)

private theorem qrTable_getElem (q d : ℕ) (h : d < q) :
    (qrTable q)[d]! = decide (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = d) := by
  have hs : d < (qrTable q).size := by simpa [qrTable] using h
  rw [getElem!_pos (qrTable q) d hs]
  simp [qrTable]

/-- The Paley graph of order `q`: `x ~ y` when `y - x` is a nonzero square mod `q`.

This is the intended graph only for a *prime* `q ≡ 1 mod 4` — for a prime power one would need the
field `GF(q)`, and for `q ≡ 3 mod 4` the residues are not closed under negation, so `ofRel`
symmetrises the Paley *tournament* into the complete graph.  For a prime `q ≡ 1 mod 4` it is
strongly regular with parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)`; see `IsoGraph/SRG.lean`. -/
def paley (q : ℕ) : CGraph :=
  let t := qrTable q
  ofRel (Fin q) fun x y ↦ t[(y.1 + q - x.1) % q]!

instance (q : ℕ) : DecidableEq (paley q).V := inferInstanceAs (DecidableEq (Fin q))

instance (q : ℕ) : Nonempty (paley (q + 1)).V := inferInstanceAs (Nonempty (Fin (q + 1)))

@[simp] theorem card_paley (q : ℕ) : Fintype.card (paley q).V = q := Fintype.card_fin q

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
def cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph where
  V := G.V × H.V
  Adj p q := (decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2))
  symm p q := by
    rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1, decide_eq_comm p.2 q.2]
  loopless p := by simp [G.loopless p.1, H.loopless p.2]

/-- The tensor (categorical) product `G × H`: move in both coordinates. -/
def tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph where
  V := G.V × H.V
  Adj p q := G.Adj p.1 q.1 && H.Adj p.2 q.2
  symm p q := by rw [G.symm p.1 q.1, H.symm p.2 q.2]
  loopless p := by simp [G.loopless p.1]

/-- The strong product `G ⊠ H`: the union of the cartesian and tensor products.

This is the one product whose relation holds on the diagonal, so the definition tests `p ≠ q`.
That test is on the vertex type, not the graphs: neither `G.Adj` nor `H.Adj` is queried twice. -/
def strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph where
  V := G.V × H.V
  Adj p q :=
    decide (p ≠ q) && ((decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2))
  symm p q := by
    rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1, decide_eq_comm p.2 q.2,
      decide_ne_comm p q]
  loopless p := by simp

/-- The lexicographic product `G[H]`: `G` on the first coordinate, and a copy of `H` inside each
fibre. -/
def lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph where
  V := G.V × H.V
  Adj p q := G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2)
  symm p q := by rw [G.symm p.1 q.1, H.symm p.2 q.2, decide_eq_comm p.1 q.1]
  loopless p := by simp [G.loopless p.1, H.loopless p.2]

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (cartesianProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (tensorProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (strongProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (lexProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    Nonempty (cartesianProduct G H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    Nonempty (tensorProduct G H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    Nonempty (strongProduct G H).V := inferInstanceAs (Nonempty (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] [Nonempty G.V] [Nonempty H.V] :
    Nonempty (lexProduct G H).V := inferInstanceAs (Nonempty (G.V × H.V))

@[simp] theorem card_cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (cartesianProduct G H).V = Fintype.card G.V * Fintype.card H.V :=
  Fintype.card_prod _ _

@[simp] theorem card_tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (tensorProduct G H).V = Fintype.card G.V * Fintype.card H.V :=
  Fintype.card_prod _ _

@[simp] theorem card_strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (strongProduct G H).V = Fintype.card G.V * Fintype.card H.V :=
  Fintype.card_prod _ _

@[simp] theorem card_lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (lexProduct G H).V = Fintype.card G.V * Fintype.card H.V :=
  Fintype.card_prod _ _

@[simp] theorem cartesianProduct_adj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p q : G.V × H.V) :
    (cartesianProduct G H).Adj p q
      = ((decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2))) := rfl

@[simp] theorem tensorProduct_adj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p q : G.V × H.V) :
    (tensorProduct G H).Adj p q = (G.Adj p.1 q.1 && H.Adj p.2 q.2) := rfl

@[simp] theorem strongProduct_adj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p q : G.V × H.V) :
    (strongProduct G H).Adj p q
      = (decide (p ≠ q) &&
          ((decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2))) := rfl

@[simp] theorem lexProduct_adj (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (p q : G.V × H.V) :
    (lexProduct G H).Adj p q = (G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2)) := rfl

theorem cartesianProduct_eq_ofRel (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    cartesianProduct G H = ofRel (G.V × H.V) fun p q ↦
      (decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2)) :=
  eq_ofRel _ _ fun p q _ => by
    simp only [cartesianProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, decide_eq_comm q.2 p.2,
      Bool.or_self]

theorem tensorProduct_eq_ofRel (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    tensorProduct G H = ofRel (G.V × H.V) fun p q ↦ G.Adj p.1 q.1 && H.Adj p.2 q.2 :=
  eq_ofRel _ _ fun p q _ => by
    simp only [tensorProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, Bool.or_self]

theorem strongProduct_eq_ofRel (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    strongProduct G H = ofRel (G.V × H.V) fun p q ↦
      (decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2) :=
  eq_ofRel _ _ fun p q hpq => by
    have h : decide (p ≠ q) = true := by simp [hpq]
    simp only [strongProduct_adj, h, Bool.true_and]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, decide_eq_comm q.2 p.2,
      Bool.or_self]

theorem lexProduct_eq_ofRel (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    lexProduct G H = ofRel (G.V × H.V) fun p q ↦
      G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2) :=
  eq_ofRel _ _ fun p q _ => by
    simp only [lexProduct_adj]
    rw [G.symm q.1 p.1, H.symm q.2 p.2, decide_eq_comm q.1 p.1, Bool.or_self]

/-- The hypercube `Q_n`: bit-strings of length `n`, adjacent when they differ in exactly one
place.  This is the `n`-fold cartesian product of `complete 2`, but written directly: threading a
`DecidableEq` instance through that recursion costs more than it saves, since
`cartesianProduct` needs the instance for the graph it is about to build. -/
def hypercube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1
  symm x y := by
    congr 1
    exact congrArg Finset.card (Finset.filter_congr fun i _ => by exact ne_comm)
  loopless x := by simp

instance (n : ℕ) : DecidableEq (hypercube n).V :=
  inferInstanceAs (DecidableEq (Fin n → Bool))

instance (n : ℕ) : Nonempty (hypercube n).V := inferInstanceAs (Nonempty (Fin n → Bool))

@[simp] theorem hypercube_adj (n : ℕ) (x y : Fin n → Bool) :
    (hypercube n).Adj x y = ((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) := rfl

theorem hypercube_eq_ofRel (n : ℕ) :
    hypercube n = ofRel (Fin n → Bool) fun x y ↦
      (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1 :=
  eq_ofRel _ _ fun x y _ => by
    have h := (hypercube n).symm x y
    simp only [hypercube_adj] at h
    simp only [hypercube_adj, ← h, Bool.or_self]

/-! ## The funnier ones -/

/-- The Kneser graph `K(n, k)`: the `k`-element subsets of `Fin n`, adjacent when disjoint.
`kneser 5 2` is the Petersen graph.

The disjointness test is reflexive when `k = 0` (the empty set is disjoint from itself), so the
diagonal is deleted explicitly; it is symmetric already. -/
def kneser (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := decide (s ≠ t) && decide (s.1 ∩ t.1 = ∅)
  symm s t := by rw [decide_ne_comm s t, Finset.inter_comm]
  loopless s := by simp

instance (n k : ℕ) : DecidableEq (kneser n k).V :=
  inferInstanceAs (DecidableEq {s : Finset (Fin n) // s.card = k})

@[simp] theorem kneser_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (kneser n k).Adj s t = (decide (s ≠ t) && decide (s.1 ∩ t.1 = ∅)) := rfl

theorem kneser_eq_ofRel (n k : ℕ) :
    kneser n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ decide (s.1 ∩ t.1 = ∅) :=
  eq_ofRel _ _ fun s t hst => by
    rw [kneser_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

/-- The line graph: one vertex per edge of `G`, two of them adjacent when the edges meet.

Every edge meets itself, so the diagonal has to go; the meeting relation is symmetric as it
stands. -/
def lineGraph (G : CGraph) [DecidableEq G.V] : CGraph where
  V := {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}
  Adj e f := decide (e ≠ f) && decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V))
  symm e f := by
    rw [decide_ne_comm e f]
    congr 1
    exact decide_eq_decide.2 ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩
  loopless e := by simp

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (lineGraph G).V :=
  inferInstanceAs (DecidableEq {e : Sym2 G.V // e ∈ G.toSimple.edgeSet})

@[simp] theorem lineGraph_adj (G : CGraph) [DecidableEq G.V]
    (e f : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) :
    (lineGraph G).Adj e f
      = (decide (e ≠ f) && decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V))) := rfl

theorem lineGraph_eq_ofRel (G : CGraph) [DecidableEq G.V] :
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
def mycielskian (G : CGraph) [DecidableEq G.V] : CGraph where
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

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (mycielskian G).V :=
  inferInstanceAs (DecidableEq (Option (G.V ⊕ G.V)))

@[simp] theorem mycielskian_adj_inl_inl (G : CGraph) [DecidableEq G.V] (a b : G.V) :
    (mycielskian G).Adj (some (.inl a)) (some (.inl b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inl_inr (G : CGraph) [DecidableEq G.V] (a b : G.V) :
    (mycielskian G).Adj (some (.inl a)) (some (.inr b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inr_inl (G : CGraph) [DecidableEq G.V] (a b : G.V) :
    (mycielskian G).Adj (some (.inr a)) (some (.inl b)) = G.Adj a b := rfl

@[simp] theorem mycielskian_adj_inr_inr (G : CGraph) [DecidableEq G.V] (a b : G.V) :
    (mycielskian G).Adj (some (.inr a)) (some (.inr b)) = false := rfl

@[simp] theorem mycielskian_adj_none_inl (G : CGraph) [DecidableEq G.V] (b : G.V) :
    (mycielskian G).Adj none (some (.inl b)) = false := rfl

@[simp] theorem mycielskian_adj_none_inr (G : CGraph) [DecidableEq G.V] (b : G.V) :
    (mycielskian G).Adj none (some (.inr b)) = true := rfl

@[simp] theorem mycielskian_adj_inl_none (G : CGraph) [DecidableEq G.V] (a : G.V) :
    (mycielskian G).Adj (some (.inl a)) none = false := rfl

@[simp] theorem mycielskian_adj_inr_none (G : CGraph) [DecidableEq G.V] (a : G.V) :
    (mycielskian G).Adj (some (.inr a)) none = true := rfl

@[simp] theorem mycielskian_adj_none_none (G : CGraph) [DecidableEq G.V] :
    (mycielskian G).Adj none none = false := rfl

theorem mycielskian_eq_ofRel (G : CGraph) [DecidableEq G.V] :
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

/-- The Johnson graph `J(n, k)`: the `k`-element subsets of `Fin n`, adjacent when they meet in
`k - 1` points.  `johnson n 2` is the triangular graph `T(n)`, i.e. the line graph of `Kₙ`, and
the complement of `kneser n 2`.

Every set meets itself in `k` points, so for `k ≥ 1` the diagonal is already excluded; it is
deleted explicitly anyway, since at `k = 0` the condition `|s ∩ t| = k - 1` degenerates to `0 = 0`
and would put a loop at the one vertex. -/
def johnson (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := decide (s ≠ t) && ((s.1 ∩ t.1).card == k - 1)
  symm s t := by rw [decide_ne_comm s t, Finset.inter_comm]
  loopless s := by simp

instance (n k : ℕ) : DecidableEq (johnson n k).V :=
  inferInstanceAs (DecidableEq {s : Finset (Fin n) // s.card = k})

@[simp] theorem johnson_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (johnson n k).Adj s t = (decide (s ≠ t) && ((s.1 ∩ t.1).card == k - 1)) := rfl

theorem johnson_eq_ofRel (n k : ℕ) :
    johnson n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ (s.1 ∩ t.1).card == k - 1 :=
  eq_ofRel _ _ fun s t hst => by
    rw [johnson_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

@[simp] theorem card_johnson (n k : ℕ) : Fintype.card (johnson n k).V = n.choose k := by
  simp [johnson, Fintype.card_finset_len]

/-- The folded cube: `Qₙ` with each pair of antipodal vertices joined, i.e. bit-strings of length
`n` adjacent when they differ in exactly one place *or* in all `n` of them.  Identifying antipodes
instead would halve the vertex count; this is the double cover of that, and is the folded
`(n+1)`-cube.  `foldedCube 4` is the Clebsch graph. -/
def foldedCube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := decide (x ≠ y) && (((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) ||
    ((Finset.univ.filter fun i ↦ x i ≠ y i).card == n))
  symm x y := by
    have h : (Finset.univ.filter fun i ↦ x i ≠ y i) = (Finset.univ.filter fun i ↦ y i ≠ x i) :=
      Finset.filter_congr fun i _ => by exact ne_comm
    rw [decide_ne_comm x y, h]
  loopless x := by simp

instance (n : ℕ) : DecidableEq (foldedCube n).V := inferInstanceAs (DecidableEq (Fin n → Bool))

@[simp] theorem foldedCube_adj (n : ℕ) (x y : Fin n → Bool) :
    (foldedCube n).Adj x y = (decide (x ≠ y) &&
      (((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) ||
        ((Finset.univ.filter fun i ↦ x i ≠ y i).card == n))) := rfl

@[simp] theorem card_foldedCube (n : ℕ) : Fintype.card (foldedCube n).V = 2 ^ n := by
  simp [foldedCube]

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

instance (G : CGraph) [DecidableEq G.V] (S : G.V → Bool) : DecidableEq (seidelSwitch G S).V :=
  inferInstanceAs (DecidableEq G.V)

@[simp] theorem seidelSwitch_adj (G : CGraph) (S : G.V → Bool) (x y : G.V) :
    (seidelSwitch G S).Adj x y = (G.Adj x y ^^ (S x ^^ S y)) := rfl

@[simp] theorem card_seidelSwitch (G : CGraph) (S : G.V → Bool) :
    Fintype.card (seidelSwitch G S).V = Fintype.card G.V := rfl

/-- Switching twice with the same set is the identity. -/
@[simp] theorem seidelSwitch_seidelSwitch (G : CGraph) (S : G.V → Bool) :
    seidelSwitch (seidelSwitch G S) S = G := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  show ((G.Adj x y ^^ (S x ^^ S y)) ^^ (S x ^^ S y)) = G.Adj x y
  cases G.Adj x y <;> cases S x <;> cases S y <;> rfl

/-! ## A few named families

One call to one constructor each, so they are `abbrev`s: instance search and `decide` see straight
through them. -/

/-- The book `Bₙ = K_{1,1,n}`: `n` triangles glued along a common edge. -/
abbrev book (n : ℕ) : CGraph := completeMultipartite [1, 1, n]

/-- The fan `Fₙ`: a path on `n` vertices plus a hub joined to all of it. -/
abbrev fan (n : ℕ) : CGraph := join (complete 1) (path n)

/-- The ladder `Lₙ = Pₙ □ K₂`: two paths joined rung by rung. -/
abbrev ladder (n : ℕ) : CGraph := cartesianProduct (path n) (complete 2)

/-- The prism `Yₙ = Cₙ □ K₂`, also called the circular ladder. -/
abbrev prism (n : ℕ) : CGraph := cartesianProduct (cycle n) (complete 2)

/-- The triangular graph `T(n) = J(n, 2) = L(Kₙ)`: the pairs from an `n`-set, adjacent when they
overlap. -/
abbrev triangular (n : ℕ) : CGraph := johnson n 2

/-- The rook's graph `Kₘ □ Kₙ`: the squares of an `m × n` board, adjacent along rows and
columns. -/
abbrev rook (m n : ℕ) : CGraph := cartesianProduct (complete m) (complete n)

/-- The cocktail party graph `K_{n×2}`: `K_{2n}` minus a perfect matching. -/
abbrev cocktailParty (n : ℕ) : CGraph := completeMultipartite (List.replicate n 2)

/-! ## Invariants of the constructions

What the invariants of `IsoGraph/Invariants.lean` come to on the graphs above.
-/

section Invariants

variable (G H : CGraph)

/-! ### The empty graph -/

@[simp] theorem empty_toSimple (n : ℕ) : (empty n).toSimple = ⊥ := by
  ext i j
  simp

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := by
  simp [E]

@[simp] theorem isAcyclic_empty (n : ℕ) : (empty n).IsAcyclic := by
  simp [IsAcyclic]

@[simp] theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := by
  rw [indepNum, empty_toSimple]
  simp [SimpleGraph.indepNum]
  let hIndep : ∀ (s : Finset (Fin n)), (⊥ : SimpleGraph (Fin n)).IsIndepSet s := by
    intro s u _ v _ huv hadj
    exact hadj
  have hset : {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} = Set.Iic n := by
    ext m
    rw [Set.mem_setOf_eq, Set.mem_Iic]
    change (∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) m s) ↔ m ≤ n
    constructor
    · rintro ⟨s, hs_indep, hs_card⟩
      exact hs_card ▸ (Finset.card_le_univ s).trans (by simp [Fintype.card_fin])
    · intro hm
      if h : m < n then
        exact ⟨Finset.image (fun i : Fin m => ⟨i, by omega⟩ : Fin m → Fin n) Finset.univ, hIndep _, by
          rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congr_arg Fin.val h)), Finset.card_fin]⟩
      else
        push_neg at h
        have heq : m = n := le_antisymm hm h
        subst heq
        exact ⟨Finset.univ, hIndep _, by simp [Fintype.card_fin]⟩
  have mem_0 : 0 ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} := by
    exact ⟨∅, hIndep ∅, by simp⟩
  have mem_n : n ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} := by
    exact ⟨Finset.univ, hIndep Finset.univ, by simp [Fintype.card_fin]⟩
  have bound : ∀ x, x ∈ {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} → x ≤ n := by
    intro x hx; rw [hset] at hx; exact hx
  have h_bdd : BddAbove {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} :=
    ⟨n, bound⟩
  change sSup {n_1 | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊥ : SimpleGraph (Fin n))) n_1 s} = n
  exact le_antisymm (csSup_le ⟨0, mem_0⟩ fun x hx => bound x hx)
    (le_csSup h_bdd mem_n)

@[simp] theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 := by
  simp [cliqueNum, empty_toSimple]
  unfold SimpleGraph.cliqueNum
  apply le_antisymm
  · -- Every clique has size ≤ min n 1
    apply csSup_le'
    rintro k ⟨s, hs⟩
    have hk := hs.1
    have hpadj := hs.2
    have hkn : s.card ≤ n := by
      calc s.card ≤ Fintype.card (empty n).V := s.card_le_univ
        _ = n := card_empty n
    have hk1 : s.card ≤ 1 := by
      rw [Finset.card_le_one]
      exact fun x hx y hy => Classical.not_not.1 fun hne => by
        have := hk hx hy hne
        simp at this
    omega
  · -- min n 1 ≤ sSup
    apply le_csSup
    · -- bounded above
      exact ⟨n, fun k ⟨s, hs⟩ => by
        have := hs.2
        rw [← this]
        calc s.card ≤ Fintype.card (empty n).V := s.card_le_univ
          _ = n := card_empty n⟩
    · -- min n 1 is in the set
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · push_cast [min_eq_right (Nat.succ_le_of_lt hn)]
        exact ⟨{⟨0, hn⟩}, by simp⟩

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
  exact hgoal.trans (goal 0 n)

@[simp] theorem isConnected_empty_one : (empty 1).IsConnected := by
  simp only [IsConnected]
  decide

/-! ### The complement -/

@[simp] theorem compl_toSimple [DecidableEq G.V] : (compl G).toSimple = G.toSimpleᶜ := by
  ext x y
  simp [compl, G.symm x y, SimpleGraph.compl_adj]

@[simp] theorem compl_compl [DecidableEq G.V] : compl (compl G) = G := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  rcases eq_or_ne x y with rfl | h
  · simp [compl, G.loopless x]
  · simp [compl, h, G.symm x y]

@[simp] theorem indepNum_compl [DecidableEq G.V] : (compl G).indepNum = G.cliqueNum := by
  simp [indepNum, cliqueNum, compl_toSimple, SimpleGraph.indepNum_compl]

@[simp] theorem cliqueNum_compl [DecidableEq G.V] : (compl G).cliqueNum = G.indepNum := by
  rw [← indepNum_compl (compl G), compl_compl]

/-- The complement of a strongly regular graph is strongly regular, with the parameters Mathlib
computes for `SimpleGraph`s. -/
theorem isSRGWith_compl [DecidableEq G.V] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) :
    (compl G).IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) :=
  SimpleGraph.Iso.isSRGWith_of_iso (G := G.toSimpleᶜ) (G' := (compl G).toSimple)
    ⟨Equiv.refl G.V, by simp; intro a b _; rfl⟩ (SimpleGraph.IsSRGWith.compl h)

theorem E_compl [DecidableEq G.V] :
    (compl G).E + G.E = (Fintype.card G.V).choose 2 := by
  simp only [CGraph.E]
  have h1 : G.compl.toSimple.edgeFinset = (G.toSimpleᶜ).edgeFinset := by
    simp [compl_toSimple]
  rw [h1]
  have h_disj : Disjoint G.toSimple.edgeFinset (G.toSimpleᶜ).edgeFinset := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    rw [SimpleGraph.mem_edgeFinset] at hx hxc
    induction x using Sym2.ind with
    | h v w =>
      rw [SimpleGraph.mem_edgeSet] at hx hxc
      rw [SimpleGraph.compl_adj] at hxc
      exact absurd hx hxc.2
  have h_union : G.toSimple.edgeFinset ∪ (G.toSimpleᶜ).edgeFinset = (⊤ : SimpleGraph G.V).edgeFinset := by
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
  have h_card : (G.toSimpleᶜ).edgeFinset.card + G.toSimple.edgeFinset.card =
    (⊤ : SimpleGraph G.V).edgeFinset.card := by
    have := Finset.card_union_of_disjoint (h_disj.symm)
    rw [Finset.union_comm] at this
    rw [← this, h_union]
  rw [h_card, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-! ### The complete graph -/

@[simp] theorem complete_adj (n : ℕ) (i j : Fin n) : (complete n).Adj i j = decide (i ≠ j) := by
  simp [complete, compl]

/-- **The complement of the rook's graph is the tensor product of complete graphs**: two squares
of the board are non-adjacent in `Kₘ □ Kₙ` exactly when they agree in neither coordinate.  Both
sides are literally on `Fin m × Fin n`, so this is an equality of `CGraph`s. -/
theorem compl_rook (m n : ℕ) :
    compl (rook m n) = tensorProduct (complete m) (complete n) := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun p ↦ funext fun q ↦ ?_))
  rw [compl_adj, cartesianProduct_adj, tensorProduct_adj, complete_adj, complete_adj]
  have hpq : (p = q) ↔ (p.1 = q.1 ∧ p.2 = q.2) := Prod.ext_iff
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, hpq]

@[simp] theorem complete_toSimple (n : ℕ) : (complete n).toSimple = ⊤ := by
  simp [complete]

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := by
  have h : (complete n).E = Fintype.card ↥(⊤ : SimpleGraph (Fin n)).edgeSet := by
    simp [E, SimpleGraph.edgeFinset_card]
  rw [h, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

@[simp] theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n := by
  simp [cliqueNum, complete_toSimple]
  rw [SimpleGraph.cliqueNum]
  have hmem : n ∈ {m | ∃ s : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique m s} := by
    refine ⟨Finset.univ, ?_⟩
    show SimpleGraph.IsNClique (⊤ : SimpleGraph (Fin n)) n Finset.univ
    letI : DecidableEq (Fin n) := inferInstance
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    have hcl : (⊤ : SimpleGraph (Fin n)).IsClique (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
      simp [SimpleGraph.IsClique, Set.Pairwise]
    exact ⟨hcl, hc⟩
  have hle : ∀ m ∈ {m | ∃ s : Finset (Fin n), (⊤ : SimpleGraph (Fin n)).IsNClique m s}, m ≤ n := by
    rintro m ⟨s, hs⟩
    show m ≤ n
    obtain ⟨hcl, hcard⟩ := hs
    rw [← hcard]
    exact le_trans (Finset.card_le_univ s) (le_of_eq (Fintype.card_fin n))
  exact csSup_eq_of_forall_le_of_forall_lt_exists_gt (by exact ⟨n, hmem⟩) hle fun m hm => ⟨n, hmem, hm⟩

@[simp] theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 := by
  simp [complete_toSimple, CGraph.indepNum]
  unfold SimpleGraph.indepNum
  -- ⊤ : SimpleGraph (Fin n), indepNum = sSup {k | ∃ s, ⊤.IsNIndepSet k s}
  -- Key: in ⊤, IsNIndepSet k s ↔ s.card = k ∧ s.card ≤ 1
  have h_adj_top : ∀ (x y : Fin n), (⊤ : SimpleGraph (Fin n)).Adj x y ↔ x ≠ y := by
    intro x y; simp [SimpleGraph.top_adj]
  have h_isIndep_top : ∀ (s : Finset (Fin n)), (⊤ : SimpleGraph (Fin n)).IsIndepSet s ↔ s.card ≤ 1 := by
    intro s
    constructor
    · -- IsIndepSet ⊤ s → s.card ≤ 1
      intro h
      by_contra hlt
      push_neg at hlt
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
      have hna := h hx hy hxy
      exact hna (h_adj_top x y |>.mpr hxy)
    · -- s.card ≤ 1 → IsIndepSet ⊤ s
      intro h x hx y hy hne
      exfalso
      have : ∀ z ∈ s, z = x := by
        intro z hz
        by_contra hne'
        have : s.card ≥ 2 := by
          have h1 : ({x, z} : Finset (Fin n)).card = 2 := by
            rw [Finset.card_pair (fun hzx => hne' hzx.symm)]
          exact h1 ▸ Finset.card_le_card (by exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hz))
        omega
      exact hne (this y hy).symm
  have h_indep : ∀ (s : Finset (Fin n)) (k : ℕ), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) k s ↔ s.card = k ∧ s.card ≤ 1 := by
    intro s k
    constructor
    · intro h
      cases h with
      | mk hi hc => exact ⟨hc, h_isIndep_top s |>.mp hi⟩
    · intro ⟨hcard, hiset⟩
      exact SimpleGraph.IsNIndepSet.mk (h_isIndep_top s |>.mpr hiset) hcard
  -- sSup = min n 1
  apply le_antisymm
  · -- sSup ≤ min n 1
    apply csSup_le'
    rintro k ⟨s, hs⟩
    have hinfo := h_indep s k |>.mp hs
    have hk1 : k ≤ 1 := hinfo.1 ▸ hinfo.2
    have hkn : k ≤ n := hinfo.1 ▸ (show s.card ≤ n from by
      calc s.card ≤ Fintype.card (Fin n) := Finset.card_le_univ s
        _ = n := Fintype.card_fin n)
    exact le_min hkn hk1
  · -- min n 1 ≤ sSup
    have hbdd : BddAbove {n_1 : ℕ | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) n_1 s} := by
      exact ⟨n, fun k ⟨s, hs⟩ => by
        have := h_indep s k |>.mp hs
        have h1 := this.1
        have h2 : s.card ≤ n := by
          calc s.card ≤ Fintype.card (Fin n) := Finset.card_le_univ s
            _ = n := Fintype.card_fin n
        rw [h1] at h2
        exact h2⟩
    -- Show min n 1 is in the set
    have hmem : min n 1 ∈ {n_1 : ℕ | ∃ s : Finset (Fin n), SimpleGraph.IsNIndepSet (G := (⊤ : SimpleGraph (Fin n))) n_1 s} := by
      by_cases hn : n = 0
      · subst hn
        simp
        exact ⟨∅, SimpleGraph.IsNIndepSet.mk (by trivial) rfl⟩
      · -- n ≥ 1, so min n 1 = 1
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hmin : min n 1 = 1 := min_eq_right hn1
        rw [hmin]
        exact ⟨{⟨0, hn1⟩}, SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) (by simp)⟩
    exact le_csSup hbdd hmem

@[simp] theorem isConnected_complete (n : ℕ) : (complete (n + 1)).IsConnected := by
  have : Nonempty (complete (n + 1)).V := ⟨(0 : Fin (n + 1))⟩
  simp [IsConnected]

@[simp] theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 := by
  simp [CGraph.diameter]
  have : Nontrivial (Fin (n + 2)) := inferInstance
  exact SimpleGraph.diam_top (α := Fin (n + 2))

@[simp] theorem degSequence_complete (n : ℕ) :
    (complete n).degSequence = List.replicate n (n - 1) := by
  have htosimple : (complete n).toSimple = SimpleGraph.completeGraph (Fin n) := by
    ext x y
    simp [CGraph.toSimple, complete, compl, empty_adj]
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
    have h1 : (Finset.univ : Finset (complete n).V).card = Fintype.card (complete n).V := Finset.card_univ
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

@[simp] theorem isConnected_path (n : ℕ) : (path (n + 1)).IsConnected := by
  simpa [IsConnected] using SimpleGraph.pathGraph_connected n

@[simp] theorem isAcyclic_path (n : ℕ) : (path n).IsAcyclic := by
  simp [IsAcyclic, path_toSimple]
  intro v c hc
  have hne : c ≠ SimpleGraph.Walk.nil := hc.isCircuit.ne_nil
  have htrail := hc.isCircuit.isTrail
  -- No edges in pathGraph n when n ≤ 1
  by_cases hn : n ≤ 1
  · -- pathGraph n has no edges
    have no_edges : ∀ (a b : Fin n), ¬(SimpleGraph.pathGraph n).Adj a b := by
      intro a b hab
      rw [SimpleGraph.pathGraph_adj] at hab
      omega
    -- In a graph with no edges, every walk is nil. Contradiction with hne.
    have all_walks_nil : ∀ ⦃x y : Fin n⦄ (w : (SimpleGraph.pathGraph n).Walk x y), w.length = 0 := by
      intro x y w
      induction w with
      | nil => simp
      | cons hab w' ih =>
        exact absurd hab (no_edges _ _)
    exact hne (by
      have h0 : c.length = 0 := all_walks_nil c
      rw [SimpleGraph.Walk.length_eq_zero_iff] at h0
      exact h0)
  · -- n ≥ 2: use cut lemma
    -- Helper: In pathGraph n, adjacent vertices have indices differing by exactly 1.
    have adj_idx : ∀ (a b : Fin n), (SimpleGraph.pathGraph n).Adj a b → (a.val = b.val + 1 ∨ b.val = a.val + 1) := by
      intro a b hab
      rw [SimpleGraph.pathGraph_adj] at hab
      omega
    -- Helper: The only edge between {0..k} and {k+1..n-1} is {⟨k,...⟩, ⟨k+1,...⟩}.
    -- Specifically, if Adj x y, x.val ≤ k, and y.val ≥ k+1, then {x,y} = {⟨k,...⟩, ⟨k+1,...⟩}.
    have crossing_edge_unique : ∀ (k : ℕ) (hk : k + 1 < n) (x y : Fin n)
      (hadj : (SimpleGraph.pathGraph n).Adj x y) (hx : x.val ≤ k) (hy : k + 1 ≤ y.val),
      Sym2.mk (x, y) = Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) := by
      intro k hk x y hadj hx hy
      have hadj' := adj_idx x y hadj
      obtain hx1 | hy1 := hadj'
      · -- x.val = y.val + 1, but x ≤ k < y, impossible
        omega
      · -- y.val = x.val + 1, and x ≤ k < y, so x = k, y = k+1
        have hxval : x.val = k := by omega
        have hyval : y.val = k + 1 := by omega
        have hxFin : x = ⟨k, by omega⟩ := Fin.ext hxval
        have hyFin' : y = ⟨k + 1, hk⟩ := Fin.ext hyval
        exact congr_arg Sym2.mk (Prod.ext hxFin hyFin')
    -- Cut lemma: any walk from index ≥ k+1 to index ≤ k uses the crossing edge.
    have cut_lemma : ∀ (k : ℕ) (hk : k + 1 < n) (x y : Fin n) (hx : k + 1 ≤ x.val) (hy : y.val ≤ k)
      (w : (SimpleGraph.pathGraph n).Walk x y),
      Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) ∈ w.edges := by
      intro k hk x y hx hy w
      induction w with
      | nil =>
        simp at hx hy
        omega
      | @cons u v w huv rest ih =>
        -- huv : Adj u v, rest : Walk v w, ih : for walk v → w
        -- hx : k+1 ≤ u.val, hy : w.val ≤ k
        by_cases hv : v.val ≤ k
        · -- Edge huv crosses: u.val ≥ k+1, v.val ≤ k. Use crossing_edge_unique with (v, u).
          have hcross : Sym2.mk (v, u) = Sym2.mk (Prod.mk (⟨k, by omega⟩ : Fin n) (⟨k + 1, by omega⟩ : Fin n)) :=
            crossing_edge_unique k hk v u (huv.symm) (by omega) (by omega)
          have : Sym2.mk (v, u) = Sym2.mk (u, v) := by
            symm
            show Sym2.mk (u, v) = Sym2.mk (v, u)
            dsimp only [Sym2.mk]
            exact Quot.sound (Sym2.Rel.swap u v)
          rw [SimpleGraph.Walk.edges_cons, ← hcross, this]
          exact List.Mem.head _
        · -- v.val ≥ k+1, recurse on rest
          push_neg at hv
          have := ih hv hy
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ this
    -- Sym2 symmetry helper
    have symm_edge : ∀ (a b : (path n).V), Sym2.mk (b, a) = Sym2.mk (a, b) := by
      intro a b
      dsimp only [Sym2.mk]
      exact Quot.sound (Sym2.Rel.swap b a)
    -- Now handle c. Decompose.
    cases c
    · exact absurd rfl hne
    · rename_i v_star huv rest
      have edge_in_cons : Sym2.mk (v, v_star) ∈ (SimpleGraph.Walk.cons huv rest).edges := by
        simp [SimpleGraph.Walk.edges_cons]
      obtain hvw | hvw := adj_idx v v_star huv
      · -- v.val = v_star.val + 1, so v_star < v. rest goes low→high.
        set k := v_star.val
        have hk : k + 1 < n := by omega
        have hvk : (v : (path n).V).val = k + 1 := hvw
        let vki : (path n).V := ⟨k, by omega⟩
        let VKI : (path n).V := ⟨k + 1, by omega⟩
        have hv_eq : v = VKI := Fin.ext hvk
        let crossing : Sym2 ((path n).V) := Sym2.mk (vki, VKI)
        have hedge_eq : Sym2.mk (v, v_star) = crossing := by
          subst hv_eq; exact symm_edge vki VKI
        -- reverse rest : Walk v v_star, high→low
        have hmem_rev : crossing ∈ (SimpleGraph.Walk.reverse rest).edges := by
          have h1 : k + 1 ≤ (v : Fin n).val := hvk.ge
          have h2 : (v_star : Fin n).val ≤ k := le_rfl
          convert cut_lemma k hk v v_star h1 h2 (SimpleGraph.Walk.reverse rest) using 1
        rw [SimpleGraph.Walk.edges_reverse] at hmem_rev
        have hmem : crossing ∈ rest.edges := by
          rw [List.mem_reverse] at hmem_rev; exact hmem_rev
        have hnodu := htrail.edges_nodup
        rw [SimpleGraph.Walk.edges_cons] at hnodu edge_in_cons
        rw [hedge_eq] at edge_in_cons
        have hnotin : crossing ∉ rest.edges := by
          intro h
          rw [hedge_eq.symm] at h
          exact (List.nodup_cons.mp hnodu).1 h
        exact hnotin hmem
      · -- v_star.val = v.val + 1, so v_star > v. rest goes high→low.
        set k := (v : (path n).V).val
        have hk : k + 1 < n := by omega
        let vki : (path n).V := ⟨k, by omega⟩
        let VKI : (path n).V := ⟨k + 1, by omega⟩
        have hvstar_eq : v_star = VKI := Fin.ext hvw
        let crossing : Sym2 ((path n).V) := Sym2.mk (vki, VKI)
        have hedge_eq : Sym2.mk (v, v_star) = crossing := by
          subst hvstar_eq; rfl
        have hmem : crossing ∈ rest.edges :=
          cut_lemma k hk v_star v (by omega) (by omega) rest
        have hnodu := htrail.edges_nodup
        rw [SimpleGraph.Walk.edges_cons] at hnodu edge_in_cons
        rw [hedge_eq] at edge_in_cons
        have hnotin : crossing ∉ rest.edges := by
          intro h
          rw [hedge_eq.symm] at h
          exact (List.nodup_cons.mp hnodu).1 h
        exact hnotin hmem

@[simp] theorem isTree_path (n : ℕ) : (path (n + 1)).IsTree :=
  ⟨isConnected_path n, isAcyclic_path (n + 1)⟩

@[simp] theorem E_path (n : ℕ) : (path (n + 1)).E = n := by
  unfold CGraph.E
  have h1 : (path (n + 1)).toSimple.edgeFinset.card = ((path (n + 1)).toSimple.edgeSet).ncard := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
  rw [h1, path_toSimple]
  -- Goal: (pathGraph (n+1)).edgeSet.ncard = n
  -- Use: edgeSet.ncard = edgeFinset.card, and compute edgeFinset.card for pathGraph
  haveI : DecidableRel (SimpleGraph.pathGraph (n + 1)).Adj :=
    fun i j => decidable_of_iff _ (SimpleGraph.pathGraph_adj).symm
  have h2 : (SimpleGraph.pathGraph (n + 1)).edgeSet.ncard =
    (SimpleGraph.pathGraph (n + 1)).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
  have htree : (SimpleGraph.pathGraph (n + 1)).IsTree := by
    exact {
      isConnected := SimpleGraph.pathGraph_connected n
      IsAcyclic := by
        have := isAcyclic_path (n + 1)
        simpa [CGraph.IsAcyclic, path_toSimple] using this
    }
  have h3 := SimpleGraph.IsTree.card_edgeFinset htree
  have h4 : (SimpleGraph.pathGraph (n + 1)).edgeFinset.card = n := by
    simp [Fintype.card_fin] at h3; omega
  exact h2.trans h4

@[simp] theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := by
  simp [diameter, path_toSimple]
  rw [SimpleGraph.diam]
  -- Build walks from 0 to i of length i for all i : Fin (n+1)
  have walk0to : ∀ i : Fin (n + 1), ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk 0 i, p.length = i.val := by
    intro i
    induction i using Fin.induction with
    | zero =>
      let p : (SimpleGraph.pathGraph (n + 1)).Walk 0 0 := .nil
      exact ⟨p, rfl⟩
    | succ i ih =>
      obtain ⟨p, hp⟩ := ih
      have hadj : (SimpleGraph.pathGraph (n + 1)).Adj (i.castSucc) (i.succ) := by
        simp [SimpleGraph.pathGraph_adj]
      let single : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ :=
        SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ)
      have hsingle : single.length = 1 := by simp [single]
      exact ⟨p.append single, by simp [hp, hsingle]⟩
  -- From this, edist 0 i ≤ ↑i.val
  have edist0_le : ∀ i : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).edist 0 i ≤ ↑(i.val : ℕ) := by
    intro i
    obtain ⟨p, hp⟩ := walk0to i
    rw [SimpleGraph.edist]
    exact le_trans (iInf_le (f := fun w : (SimpleGraph.pathGraph (n + 1)).Walk 0 i => (w.length : ℕ∞)) p) (by simp [hp])
  -- upWalk i : walk from castSucc i to succ i of length 1, for i : Fin n
  have upWalk : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ, p.length = 1 := by
    intro i
    exact ⟨SimpleGraph.Walk.cons (by simp [SimpleGraph.pathGraph_adj])
      (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ), by simp⟩
  -- downWalk i : walk from succ i to castSucc i, by reversing upWalk
  have downWalk : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.castSucc, p.length = 1 := by
    intro i
    obtain ⟨q, hq⟩ := upWalk i
    exact ⟨q.reverse, by simp [hq]⟩
  -- Monotone up walk: for u v with u.val ≤ v.val, walk from u to v of length v - u
  -- By induction on the difference. This is complex; let me use a simpler approach.
  -- For any i : Fin (n+1) and k : ℕ with i.val + k ≤ n, walk from i to ⟨i+k, ...⟩ of length k.
  -- Adjacency between any i and i+1 in pathGraph (n+1)
  have adj_succ : ∀ i : Fin n, (SimpleGraph.pathGraph (n + 1)).Adj i.castSucc i.succ := by
    intro i; simp [SimpleGraph.pathGraph_adj]
  -- Walk from i to i.succ of length 1
  have walk_succ : ∀ i : Fin n, ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i.castSucc i.succ, p.length = 1 := by
    intro i
    exact ⟨SimpleGraph.Walk.cons (adj_succ i)
      (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph (n + 1)).Walk i.succ i.succ), by simp⟩
  -- Build walk from i to j (where j = i + k) by iterating walk_succ k times
  -- Target vertex: i + k in Fin (n+1), when i.val + k < n + 1
  let addK (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1) : Fin (n + 1) := ⟨i.val + k, hk⟩
  have upWalkAny : ∀ (i : Fin (n + 1)) (k : ℕ) (hk : (i : ℕ) + k < n + 1),
      ∃ p : (SimpleGraph.pathGraph (n + 1)).Walk i (addK i k hk), p.length = k := by
    intro i k hk
    induction k with
    | zero =>
      exact ⟨.nil, rfl⟩
    | succ m ih =>
      obtain ⟨p, hp⟩ := ih (by omega)
      have hm : (i : ℕ) + m < n := by omega
      obtain ⟨q, hq⟩ := walk_succ ⟨i.val + m, hm⟩
      exact ⟨p.append q, by simp [hp, hq]⟩
  -- hupper: edist u v ≤ ↑n for all u, v
  have hinner : ∀ {u v : Fin (n + 1)}, (u : ℕ) ≤ v → (SimpleGraph.pathGraph (n + 1)).edist u v ≤ ↑n := by
    intro u v huv
    have hvk : (u : ℕ) + (v - u) < n + 1 := by omega
    have hkep : addK u (v - u) hvk = v := by
      ext; simp [addK, Nat.add_sub_of_le huv]
    obtain ⟨p, hp⟩ := upWalkAny u (v - u) hvk
    have hedist_le : (SimpleGraph.pathGraph (n + 1)).edist u (addK u (v - u) hvk) ≤ ↑(v - u : ℕ) := by
      exact SimpleGraph.edist_le p |>.trans (by rw [hp])
    rw [hkep] at hedist_le
    exact hedist_le.trans (Nat.cast_le.mpr (by omega))
  have hupper : ∀ u v : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).edist u v ≤ ↑n := by
    intro u v
    by_cases huv : (u : ℕ) ≤ v
    · exact hinner huv
    · rw [SimpleGraph.edist_comm]
      exact hinner (le_of_lt (not_le.mp huv))
  -- hexist_upper
  have hexist_upper : (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ ≤ ↑n := hupper 0 ⟨n, Nat.lt_succ_self n⟩
  -- Key: for any walk, b.val ≤ a.val + walk.length
  have walk_pot : ∀ {a b : Fin (n + 1)} (p : (SimpleGraph.pathGraph (n + 1)).Walk a b),
      (b : ℕ) ≤ (a : ℕ) + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | @cons u v w hadj p ih =>
      have hadj' : (SimpleGraph.pathGraph (n + 1)).Adj u v := hadj
      rw [SimpleGraph.pathGraph_adj] at hadj'
      have : (v : ℕ) ≤ (u : ℕ) + 1 := by
        rcases hadj' with h | h <;> omega
      simp [SimpleGraph.Walk.length_cons]
      omega
  -- hexist_lower: edist 0 last ≥ ↑n
  have hexist_lower : ↑(n : ℕ∞) ≤ (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ := by
    rw [SimpleGraph.edist]
    by_cases hne : Nonempty ((SimpleGraph.pathGraph (n + 1)).Walk 0 ⟨n, Nat.lt_succ_self n⟩)
    · apply le_ciInf
      intro p
      have := walk_pot p
      simp at this ⊢
      exact_mod_cast this
    · push_neg at hne
      simp
  -- hexist
  have hexist : (SimpleGraph.pathGraph (n + 1)).edist 0 ⟨n, Nat.lt_succ_self n⟩ = ↑n :=
    le_antisymm hexist_upper hexist_lower
  -- iSup bounds
  have hiSup_ge : ↑(n : ℕ∞) ≤ ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 := by
    rw [← hexist]
    exact le_iSup (f := fun p : (Fin (n + 1)) × (Fin (n + 1)) => (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2) ⟨0, ⟨n, Nat.lt_succ_self n⟩⟩
  have hiSup_le : ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 ≤ ↑(n : ℕ∞) :=
    ciSup_le fun p => hupper p.1 p.2
  have hisup : ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 = ↑(n : ℕ∞) :=
    le_antisymm hiSup_le hiSup_ge
  have : ⨆ u : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).eccent u = ⨆ p : (Fin (n + 1)) × (Fin (n + 1)), (SimpleGraph.pathGraph (n + 1)).edist p.1 p.2 := by
    simp only [SimpleGraph.eccent]
    have : ∀ {f : Fin (n + 1) → Fin (n + 1) → ℕ∞}, (⨆ u, ⨆ v, f u v) = ⨆ p : Fin (n + 1) × Fin (n + 1), f p.1 p.2 := by
      intro f
      exact iSup_prod' f
    exact this
  have hediam : (SimpleGraph.pathGraph (n + 1)).ediam = ⨆ u : Fin (n + 1), (SimpleGraph.pathGraph (n + 1)).eccent u := by
    simp [SimpleGraph.ediam]
  rw [hediam, this, hisup]
  simp

@[simp] theorem isConnected_cycle (n : ℕ) : (cycle (n + 1)).IsConnected := by
  rcases n with _ | n
  · -- n = 0: cycle 1, single vertex, trivially connected
    show (cycle 1).toSimple.Connected
    let _ : Nonempty (cycle 1).V := ⟨⟨0, by omega⟩⟩
    have huv : ∀ (u v : (cycle 1).V), u = v := by
      intro u v
      have hu : u.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ u.is_lt)
      have hv : v.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ v.is_lt)
      exact Fin.ext (hu.trans hv.symm)
    exact { preconnected := fun u v => by rw [huv u v] }
  · -- n ≥ 1: m ≥ 2
    set m := n + 1 + 1
    -- step_adj: from i can go to (i+1)%m
    have step_adj : ∀ i : Fin m, (cycle m).toSimple.Adj i ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
      intro i
      simp only [cycle, toSimple_adj, ofRel_adj]
      have hi_lt : (i : ℕ) < m := i.is_lt
      have hne : (i : ℕ) ≠ (i.val + 1) % m := by
        intro h
        have him1 : (i : ℕ) + 1 ≤ m := by omega
        by_cases hlt : (i : ℕ) + 1 < m
        · have hmod : ((i : ℕ) + 1) % m = (i : ℕ) + 1 := Nat.mod_eq_of_lt hlt
          rw [hmod] at h; omega
        · have hneq : (i : ℕ) + 1 = m := by omega
          have hmod2 : ((i : ℕ) + 1) % m = 0 := by rw [hneq]; simp
          rw [hmod2] at h; omega
      set j : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩
      have hne' : i ≠ j := by
        intro h; have := congr_arg Fin.val h; simp [j] at this; exact hne this
      simp [hne', j]
    -- Walk step: reachability from i to (i+k)%m for any k
    have walk_step : ∀ (i : Fin m) (k : ℕ), (cycle m).toSimple.Reachable i ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ := by
      intro i k
      induction k with
      | zero =>
        show (cycle m).toSimple.Reachable i ⟨(i.val + 0) % m, Nat.mod_lt _ (by omega)⟩
        simp [Nat.mod_eq_of_lt (by omega : (i : ℕ) < m)]
      | succ k ih =>
        show (cycle m).toSimple.Reachable i ⟨(i.val + (k + 1)) % m, Nat.mod_lt _ (by omega)⟩
        have hstep : (cycle m).toSimple.Adj ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ ⟨((i.val + k) + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
          convert step_adj ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ using 2
          simp
        obtain ⟨w⟩ := ih
        exact ⟨w.concat hstep⟩
    -- Reachability between any two vertices
    have reach_all : ∀ (i j : Fin m), (cycle m).toSimple.Reachable i j := by
      intro i j
      let k := j.val + m - i.val
      have hk : (i.val + k) % m = j.val := by
        simp [k]
        have : (i.val + (j.val + m - i.val)) = j.val + m := by omega
        have h1 : (↑i + (↑j + m - ↑i)) = ↑j + m := ‹_›
        rw [h1]
        have h2 : ((↑j + m) % m : ℕ) = ↑j := by
          simp [Nat.mod_eq_of_lt (by omega : (j : ℕ) < m)]
        exact h2
      have h_eq : j = ⟨(i.val + k) % m, Nat.mod_lt _ (by omega)⟩ := by
        exact Fin.ext hk.symm
      rw [h_eq]
      exact walk_step i k
    exact { preconnected := reach_all, nonempty := ⟨⟨0, by omega⟩⟩ }

@[simp] theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := by
  rw [show (cycle (n + 3)).E = (cycle (n + 3)).toSimple.edgeFinset.card from rfl]
  have hadj : ∀ v u : Fin (n + 3), (cycle (n + 3)).toSimple.Adj v u ↔
      u = (v + 1) % (n + 3) ∨ u = (v + (n + 2)) % (n + 3) := by
    intro v u
    simp only [cycle, ofRel, CGraph.toSimple_adj]
    -- Key: relate Nat.mod stuff to Fin equality via Fin.ext_iff
    have hv1 : ∀ (x : Fin (n + 3)), (x + 1 : Fin (n + 3)).val = (x.val + 1) % (n + 3) := by
      simp [Fin.val_add]
    have hv2 : ∀ (x : Fin (n + 3)), (x + Fin.mk (n + 2) (by omega) : Fin (n + 3)).val = (x.val + (n + 2)) % (n + 3) := by
      simp [Fin.val_add]
    -- u = v+1 (Fin) ↔ (v+1).val = u.val ↔ (v.val+1)%(n+3) = u.val
    -- (u+1 = v) ↔ (u+1).val = v.val ↔ (u.val+1)%(n+3) = v.val
    -- Inverse direction for key2: u+1 = v ↔ ...
    have key_uv1 : (v + 1 = u) ↔ (v.val + 1) % (n + 3) = u.val := by
      rw [← hv1, Fin.ext_iff]
    have key_u1v : (u + 1 = v) ↔ (u.val + 1) % (n + 3) = v.val := by
      rw [← hv1, Fin.ext_iff]
    have key_uv1_rev : (u = v + 1) ↔ u.val = (v.val + 1) % (n + 3) := by
      rw [← hv1]; exact Fin.ext_iff
    have key_venv : (u = v + Fin.mk (n + 2) (by omega)) ↔
        u.val = (v.val + (n + 2)) % (n + 3) := by
      rw [← hv2]; exact Fin.ext_iff
    -- Now: adj ↔ (¬v=u ∧ ((v+1)%m = u ∨ (u+1)%m = v)) ↔ u = v+1 ∨ u = v+(n+2) (in Fin, expressed as Nat mod)
    -- The RHS of the theorem goal is about Nat mod, not Fin eq. But it's equivalent to Fin eq.
    -- LHS: ¬v = u ∧ ((v.val+1)%(n+3) == u.val ∨ (u.val+1)%(n+3) == v.val) = true
    -- After simp with Bool.eq... let me just use the keys.
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [key_uv1.symm, key_u1v.symm]
    -- Now: v ≠ u ∧ (v + 1 = u ∨ u + 1 = v) ↔ u = v + 1 ∨ u = v + ⟨n+2,...⟩
    have h_add_one_mk : (1 : Fin (n + 3)) + Fin.mk (n + 2) (by omega) = 0 := by
      ext; simp [Fin.val_add]
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n + 3), Nat.mod_eq_of_lt (by omega : n + 2 < n + 3)]
      rw [show 1 + (n + 2) = n + 3 by omega]
      exact Nat.mod_self _
    have h_mk_one_add : Fin.mk (n + 2) (by omega) + (1 : Fin (n + 3)) = 0 := by
      show (⟨n + 2, by omega⟩ : Fin (n + 3)) + 1 = 0
      ext; simp [Fin.val_add]
    have hadd_cancel : ∀ x : Fin (n + 3), ∀ v : Fin (n + 3), v + x = v → x = 0 := by
      intro x v h
      have h1 : (v.val + x.val) % (n + 3) = v.val := by
        have := congr_arg Fin.val h; simp [Fin.val_add] at this; exact this
      have hvb := v.2
      have hxvb := x.2
      have hdiv := Nat.mod_add_div (v.val + x.val) (n + 3)
      rw [h1] at hdiv
      have hdiv2 : x.val = (n + 3) * ((v.val + x.val) / (n + 3)) := by omega
      have : x.val = 0 := by
        by_contra hx_ne
        have : (n + 3) ≤ x.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hx_ne) ⟨(v.val + x.val) / (n + 3), by linarith⟩
        omega
      exact Fin.ext this
    have hne_from_left : v + 1 ≠ v := by
      intro h; exact absurd (hadd_cancel 1 v h) (by simp)
    have hne_from_right : v + Fin.mk (n + 2) (by omega) ≠ v := by
      intro h
      have : (Fin.mk (n + 2) (by omega) : Fin (n + 3)) = 0 → False := by
        intro heq; exact absurd (congr_arg Fin.val heq) (by simp)
      exact this (hadd_cancel _ _ h)
    have hinv : ∀ x y : Fin (n + 3), x + 1 = y ↔ x = y + Fin.mk (n + 2) (by omega) := by
      intro x y
      constructor
      · intro h
        have : y + Fin.mk (n + 2) (by omega) = x + 1 + Fin.mk (n + 2) (by omega) := by rw [h]
        rw [this, add_assoc, h_add_one_mk, add_zero]
      · intro h; rw [h, add_assoc, h_mk_one_add, add_zero]
    have hinv_right : (u + 1 = v) ↔ (u = v + Fin.mk (n + 2) (by omega)) := hinv u v
    rw [hinv_right]
    constructor
    · rintro ⟨hne, h | h⟩
      · left; exact (key_uv1.mp h).symm
      · right; exact key_venv.mp h
    · rintro (h | h)
      · exact ⟨fun heq => hne_from_left (heq ▸ key_uv1.mpr h.symm), Or.inl (key_uv1.mpr h.symm)⟩
      · exact ⟨fun heq => hne_from_right (heq.symm ▸ (key_venv.mpr h).symm), Or.inr (key_venv.mpr h)⟩
  have hne_one_mk : (1 : Fin (n + 3)) ≠ Fin.mk (n + 2) (by omega) := by
    intro h; have := congr_arg Fin.val h; simp at this
  have hdeg : ∀ v : (cycle (n + 3)).V, (cycle (n + 3)).toSimple.degree v = 2 := by
    intro v
    change Fin (n + 3) at v
    have hne2 : v + 1 ≠ v + Fin.mk (n + 2) (by omega) := by
      intro h; exact hne_one_mk (add_left_cancel h)
    rw [SimpleGraph.degree]
    have hneighborFinset : (cycle (n + 3)).toSimple.neighborFinset v =
      {v + 1, v + Fin.mk (n + 2) (by omega)} := by
      ext u
      change Fin (n + 3) at u
      simp only [SimpleGraph.mem_neighborFinset]
      have hu := hadj v u
      have hv1' : ∀ (x : Fin (n + 3)), (x + 1 : Fin (n + 3)).val = (x.val + 1) % (n + 3) := by
        intro x; simp [Fin.val_add]
      have hv2' : ∀ (x : Fin (n + 3)), (x + Fin.mk (n + 2) (by omega) : Fin (n + 3)).val = (x.val + (n + 2)) % (n + 3) := by
        intro x; simp [Fin.val_add]
      have key1 : u = v + 1 ↔ u.val = (v.val + 1) % (n + 3) := by
        rw [← hv1']; exact Fin.ext_iff
      have key2 : u = v + Fin.mk (n + 2) (by omega) ↔ u.val = (v.val + (n + 2)) % (n + 3) := by
        rw [← hv2']; exact Fin.ext_iff
      rw [hu, Finset.mem_insert, Finset.mem_singleton]
      rw [key1, key2]
    rw [hneighborFinset]
    rw [Finset.card_eq_two]
    exact ⟨v + 1, v + Fin.mk (n + 2) (by omega), hne2, rfl⟩
  have hsum : ∑ v : (cycle (n + 3)).V, (cycle (n + 3)).toSimple.degree v = 2 * (n + 3) := by
    simp [hdeg]
    omega
  have h2 := SimpleGraph.sum_degrees_eq_twice_card_edges (cycle (n + 3)).toSimple
  linarith

@[simp] theorem not_isAcyclic_cycle (n : ℕ) : ¬(cycle (n + 3)).IsAcyclic := by
  by_contra h_ac
  simp only [IsAcyclic, CGraph.IsAcyclic] at h_ac
  have hconn : (cycle (n + 3)).IsConnected := isConnected_cycle (n + 2)
  have hE : (cycle (n + 3)).E = n + 3 := E_cycle n
  have htree_simple : (cycle (n + 3)).toSimple.IsTree := ⟨hconn, h_ac⟩
  -- Need: for a tree, edgeFinset.card = card V - 1
  have h1 : (cycle (n + 3)).toSimple.IsTree := htree_simple
  -- A tree on V vertices has |V|-1 edges. We know |V| = n+3 and |E| = n+3, contradiction.
  have hV : Fintype.card (cycle (n + 3)).V = n + 3 := card_cycle (n + 3)
  -- A tree is a minimal connected graph: removing any edge disconnects it.
  -- Also, a tree on V vertices has |V|-1 edges. Let me find/search for this.
  -- Alternative: use that G.toSimple is a tree, so it has a unique path between any two vertices,
  -- and use rank of graphic matroid... too complex.
  -- Let me try to prove |E| = |V|-1 for a tree by using SimpleGraph's tree lemmas.
  have h_edges := SimpleGraph.IsTree.card_edgeFinset h1
  rw [hV] at h_edges
  -- h_edges : edgeFinset.card + 1 = n + 3
  -- hE : edgeFinset.card = n + 3 (via CGraph.E)
  have : (cycle (n + 3)).toSimple.edgeFinset.card = (cycle (n + 3)).E := by
    simp [CGraph.E]
  rw [hE] at this
  omega

@[simp] theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 := by
  show (cycle (n + 1)).toSimple.diam = (n + 1) / 2
  simp only [SimpleGraph.diam]
  set m : ℕ := (n + 1) / 2
  show ((cycle (n + 1)).toSimple.ediam).toNat = m
  by_cases hn : n = 0
  · subst hn
    simp [m]
    exact Or.inl (by show Subsingleton (Fin 1); exact inferInstance)
  have h_edge : ∀ i : Fin (n + 1), (cycle (n + 1)).toSimple.Adj i (i + 1) := by
    intro i
    simp [cycle, ofRel_adj, toSimple_adj]
    exact ⟨hn, Or.inl (by rw [Fin.val_add]; simp)⟩
  -- Clockwise walk of length t from u to (u + t)
  let finAdd : ℕ → Fin (n + 1) := fun t => ⟨t % (n + 1), Nat.mod_lt t (Nat.succ_pos n)⟩
  have h_edist_walk : ∀ (u : Fin (n + 1)) (t : ℕ), t ≤ n → (cycle (n + 1)).toSimple.edist u (u + finAdd t) ≤ (t : ℕ∞) := by
    intro u t
    induction t with
    | zero =>
      intro ht
      simp [finAdd, SimpleGraph.edist_self]
    | succ t ih =>
      intro ht
      have hstep : (u + finAdd t) + 1 = u + finAdd (t + 1) := by
        simp [finAdd, Fin.add_def, Nat.add_assoc]
      have hedge : (cycle (n + 1)).toSimple.Adj (u + finAdd t) (u + finAdd (t + 1)) := by
        rw [← hstep]
        exact h_edge (u + finAdd t)
      have h_edist_succ : (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) ≤ 1 := by
        have : (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) ≤ ↑(SimpleGraph.Walk.nil.cons hedge).length := SimpleGraph.Walk.edist_le (SimpleGraph.Walk.nil.cons hedge)
        simp at this
        exact this
      calc (cycle (n + 1)).toSimple.edist u (u + finAdd (t + 1))
          ≤ (cycle (n + 1)).toSimple.edist u (u + finAdd t) +
              (cycle (n + 1)).toSimple.edist (u + finAdd t) (u + finAdd (t + 1)) :=
            SimpleGraph.edist_triangle
        _ ≤ ↑t + 1 := by
            exact add_le_add (ih (by omega)) h_edist_succ
        _ = ↑(t + 1) := by push_cast; rfl
  have h_edist_le : ∀ u v : Fin (n + 1), (cycle (n + 1)).toSimple.edist u v ≤ (m : ℕ∞) := by
    intro u v
    let t : ℕ := (v.val + (n + 1) - u.val) % (n + 1)  -- clockwise distance, 0 ≤ t ≤ n
    -- min(t, (n+1)-t) ≤ m
    have hmin : t ≤ m ∨ (n + 1 - t) ≤ m := by
      have ht : t < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
      have ht_le : t ≤ n := Nat.le_of_lt_succ ht
      have : t + (n + 1 - t) = n + 1 := by omega
      by_contra h
      push_neg at h
      omega
    -- Helper: u + (v - u) = v in Fin (n+1)
    have hfin_add_sub : ∀ (u v : Fin (n + 1)), u + (v - u) = v := by
      intro u v
      ext
      simp
    -- Helper: Fin.val of subtraction
    have ht_def : t = (v - u).val := by
      simp [t, Fin.sub_def]
      have : (v : ℕ) + (n + 1) - u = (n + 1 - u + v : ℕ) := by omega
      rw [this]
    let t' : ℕ := (u.val + (n + 1) - v.val) % (n + 1)
    have ht'_def : t' = (u - v).val := by
      simp [t', Fin.sub_def]
      have : (u : ℕ) + (n + 1) - v = (n + 1 - v + u : ℕ) := by omega
      rw [this]
    rcases hmin with htle | hbtle
    · -- clockwise walk from u to v has edist ≤ t ≤ m
      have huv : v = u + finAdd t := by
        have : finAdd t = (v - u : Fin (n + 1)) := by
          ext; simp [finAdd, ht_def]
          omega
        rw [this]
        exact (hfin_add_sub u v).symm
      rw [huv]
      exact (h_edist_walk u t (by omega)).trans (WithBot.coe_le_coe.mpr htle)
    · -- counterclockwise: use symmetry and walk from v to u clockwise
      rw [SimpleGraph.edist_comm]
      -- clockwise distance from v to u
      have ht'_le_n : t' ≤ n := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos n))
      -- t' ≤ m (since t' = (n+1-t) % (n+1) and hbtle says n+1-t ≤ m)
      have ht'_le_m : t' ≤ m := by
        by_cases ht0 : t = 0
        · simp [t']
          omega
        · -- t > 0 case: t' + t = n + 1
          have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
          have ht_lt : t < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
          have ht'_lt : t' < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
          have htsum : t' + t = n + 1 := by
            have hsum_zero : (u - v : Fin (n + 1)) + (v - u) = 0 := by
              ext; simp
            have hval : ((u - v).val + (v - u).val) % (n + 1) = 0 := by
              have h1 : ((u - v : Fin (n + 1)) + (v - u)).val = (0 : Fin (n + 1)).val := by rw [hsum_zero]
              rw [Fin.val_add] at h1
              simp at h1
              exact h1
            have hvu_val : (v - u).val = t := ht_def.symm
            have hu_val : (u - v).val = t' := ht'_def.symm
            have hpos : 0 < (v - u).val := hvu_val ▸ ht_pos
            have hlt : (v - u).val < n + 1 := (v - u).isLt
            have hlt' : (u - v).val < n + 1 := (u - v).isLt
            have hdvd : (n + 1 : ℕ) ∣ ((u - v).val + (v - u).val) := Nat.dvd_of_mod_eq_zero hval
            obtain ⟨k, hk⟩ := hdvd
            rcases k with (_ | _ | k) <;> simp at hk
            · exfalso
              have h1 : (v - u : Fin (n + 1)) = 0 := hk.2
              have h2 : (v - u).val = 0 := by simpa using h1
              omega
            · rw [← hvu_val, ← hu_val]; exact hk
            · exfalso
              have hge : (n + 1) * (k + 1 + 1) ≥ 2 * (n + 1) := by nlinarith
              omega
          omega
      have huv' : u = v + finAdd t' := by
        have : finAdd t' = (u - v : Fin (n + 1)) := by
          ext; simp [finAdd, ht'_def]
          omega
        rw [this]
        exact (hfin_add_sub v u).symm
      rw [huv']
      exact (h_edist_walk v t' ht'_le_n).trans (WithBot.coe_le_coe.mpr ht'_le_m)
  have h_ediam_le : (cycle (n + 1)).toSimple.ediam ≤ (m : ℕ∞) :=
    SimpleGraph.ediam_le_of_edist_le h_edist_le
  -- Potential function for lower bounds
  let f : Fin (n + 1) → ℤ := fun i => min ((i : ℤ)) ((n + 1) - (i : ℤ))
  have hf_adj : ∀ {i j : Fin (n + 1)}, (cycle (n + 1)).toSimple.Adj i j → |(f j : ℤ) - (f i : ℤ)| ≤ 1 := by
    intro i j hij
    -- Characterize edges: Adj i j ↔ j = i + 1 ∨ i = j + 1 in Fin (n+1)
    simp [cycle, ofRel_adj, toSimple_adj] at hij
    rcases hij with ⟨hne, hj|hi⟩
    · -- j = i + 1
      have hij1 : j = i + 1 := by
        ext; simp [Fin.val_add] at hj ⊢; omega
      rw [hij1]
      simp only [f]
      rw [abs_sub_le_iff]
      by_cases hmax : (i : ℕ) = n
      · -- i is the last element, i+1 wraps to 0
        have : (i + 1 : Fin (n + 1)) = 0 := by
          ext; simp [Fin.val_add, hmax]
        rw [this]
        simp only [Fin.val_zero]
        simp
        constructor <;> omega
      · -- i.val < n, so (i+1).val = i.val + 1
        have hi_lt_n : (i : ℕ) < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hmax
        have hmod : ((i : ℕ) + 1) % (n + 1) = (i : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
        have hval_i1 : ((i + 1 : Fin (n + 1)) : ℤ) = (i : ℤ) + 1 := by
          simp [Fin.val_add, hmod]
        rw [hval_i1]
        set a := (i : ℤ) with ha_def
        simp only [Int.min_def]
        split <;> split <;> omega
    · -- i = j + 1
      have hij2 : i = j + 1 := by
        ext; simp [Fin.val_add] at hi ⊢; omega
      rw [hij2]
      simp only [f]
      rw [abs_sub_le_iff]
      by_cases hmax : (j : ℕ) = n
      · have : (j + 1 : Fin (n + 1)) = 0 := by
          ext; simp [Fin.val_add, hmax]
        rw [this]
        simp only [Fin.val_zero]
        simp
        constructor <;> omega
      · have hj_lt_n : (j : ℕ) < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hmax
        have hmod : ((j : ℕ) + 1) % (n + 1) = (j : ℕ) + 1 := Nat.mod_eq_of_lt (by omega)
        have hval_j1 : ((j + 1 : Fin (n + 1)) : ℤ) = (j : ℤ) + 1 := by
          simp [Fin.val_add, hmod]
        rw [hval_j1]
        set a := (j : ℤ) with ha_def
        simp only [Int.min_def]
        split <;> split <;> omega
  have hf_walk : ∀ {u v : Fin (n + 1)} (w : (cycle (n + 1)).toSimple.Walk u v),
      |(f v : ℤ) - (f u : ℤ)| ≤ (w.length : ℤ) := by
    intro u v w
    induction w with
    | nil => simp [SimpleGraph.Walk.length]
    | @cons u' w' hstep ih pw ihw =>
      calc |(f hstep : ℤ) - (f u' : ℤ)|
          = |((f hstep : ℤ) - (f w' : ℤ)) + ((f w' : ℤ) - (f u' : ℤ))| := by
            congr 1; ring
        _ ≤ |(f hstep : ℤ) - (f w' : ℤ)| + |(f w' : ℤ) - (f u' : ℤ)| := abs_add_le _ _
        _ ≤ (pw.length : ℤ) + 1 := by
            exact add_le_add ihw (hf_adj ih)
        _ = (SimpleGraph.Walk.cons ih pw).length := by simp [SimpleGraph.Walk.length]
  have hf0 : f (0 : Fin (n + 1)) = 0 := by
    show min ((0 : ℤ)) ((n : ℤ) + 1 - (0 : ℤ)) = 0
    simp; omega
  have hfm : f ⟨m, by omega⟩ = (m : ℤ) := by
    show min ((m : ℤ)) ((n : ℤ) + 1 - (m : ℤ)) = (m : ℤ)
    exact min_eq_left (by omega)
  have h_lb : ∀ {w : (cycle (n + 1)).toSimple.Walk (0 : Fin (n + 1)) ⟨m, by omega⟩}, (m : ℤ) ≤ (w.length : ℤ) := by
    intro w
    have := hf_walk w
    rw [hfm, hf0] at this
    simpa using this
  have h_edist_ge : ∃ u v : Fin (n + 1), (m : ℕ∞) ≤ (cycle (n + 1)).toSimple.edist u v := by
    refine ⟨(0 : Fin (n + 1)), (⟨m, by omega⟩ : Fin (n + 1)), ?_⟩
    let base : Fin (n + 1) := ⟨0, by omega⟩
    have hfinAdd : base + finAdd m = ⟨m, by omega⟩ := by
      ext; simp [finAdd, base]; omega
    have hreach : (cycle (n + 1)).toSimple.Reachable base ⟨m, by omega⟩ := by
      rw [← hfinAdd]
      have hne : (cycle (n + 1)).toSimple.edist base (base + finAdd m) ≠ ⊤ := by
        have : (m : ℕ∞) ≠ ⊤ := by simp
        exact ne_top_of_le_ne_top this (h_edist_walk base m (by omega))
      exact (SimpleGraph.edist_ne_top_iff_reachable).mp hne
    -- Reachable: use le_csInf
    rw [SimpleGraph.edist]
    apply le_csInf
    · exact ⟨_, ⟨hreach.some, rfl⟩⟩
    · rintro _ ⟨w, rfl⟩
      show (m : ℕ∞) ≤ ↑w.length
      exact_mod_cast @h_lb w
  obtain ⟨u, v, huv⟩ := h_edist_ge
  have h_m_le_ediam : (m : ℕ∞) ≤ (cycle (n + 1)).toSimple.ediam :=
    huv.trans (SimpleGraph.edist_le_ediam)
  have h_ediam_eq : (cycle (n + 1)).toSimple.ediam = (m : ℕ∞) := le_antisymm h_ediam_le h_m_le_ediam
  rw [h_ediam_eq]
  simp

@[simp] theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 := by
  unfold CGraph.indepNum SimpleGraph.indepNum
  set m := n + 3
  -- Adjacency in cycle m: toSimple.Adj i j ↔ i ≠ j ∧ ((i+1)%m == j ∨ (j+1)%m == i)
  have habj : ∀ (i j : Fin m), (cycle m).toSimple.Adj i j ↔ i ≠ j ∧ (((i.val + 1) % m == j.val) ∨ ((j.val + 1) % m == i.val)) := by
    intro i j
    simp [cycle, ofRel_adj, CGraph.toSimple_adj]
  -- The shift map i ↦ (i+1) % m is a bijection on Fin m
  let shift : Fin m → Fin m := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩
  have hshift_eq : ∀ i : Fin m, shift i = i + 1 := by
    intro i; exact Fin.ext (by simp [shift, Fin.val_add])
  have hshift_bijective : Function.Bijective shift := by
    refine ⟨?_, ?_⟩
    · -- injective
      intro i j hij
      rw [hshift_eq] at hij
      exact add_right_cancel hij
    · -- surjective
      intro j
      refine ⟨j + ⟨m - 1, by omega⟩, ?_⟩
      rw [hshift_eq]
      have hlast : (⟨m - 1, by omega⟩ : Fin m) + 1 = 0 := by
        ext; simp [Fin.val_add]
        have : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        simp [this]
      rw [add_assoc, hlast, add_zero]
  have hshift_inj := hshift_bijective.1
  have hshift_surj := hshift_bijective.2
  -- For any i : Fin m, i ≠ shift i (since m ≥ 3)
  have hne_shift : ∀ i : Fin m, i ≠ shift i := by
    intro i hi
    have hshift_eq_i : shift i = i + 1 := hshift_eq i
    rw [hshift_eq_i] at hi
    have h1 : (i + 1 : Fin m) = i := hi.symm
    have h2 : (1 : Fin m) = 0 := by
      have := congr_arg (· + (-i : Fin m)) h1
      simp [add_assoc] at this
    exact absurd (Fin.ext_iff.mp h2) (by simp; omega)
  -- For any i : Fin m, Adj i (shift i)
  have hadj_shift : ∀ i : Fin m, (cycle m).toSimple.Adj i (shift i) := by
    intro i
    rw [habj]
    exact ⟨hne_shift i, Or.inl (by simp [shift])⟩
  -- For any independent set s, shift(s) is disjoint from s
  have hdisjoint : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      Disjoint s (s.map ⟨shift, hshift_inj⟩) := by
    intro s hs
    rw [Finset.disjoint_left]
    intro z hz hzm
    obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hzm
    have hyz' : shift y = z := hyz
    have hadyz : (cycle m).toSimple.Adj y z := by
      subst hyz'
      exact hadj_shift y
    have hyz_ne : y ≠ z := by
      intro heq; rw [heq.symm] at hyz'; exact hne_shift y hyz'.symm
    exact hs hy hz hyz_ne hadyz
  -- So |s| + |shift(s)| ≤ m, i.e., 2|s| ≤ m
  have hupper : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      2 * s.card ≤ m := by
    intro s hs
    have hd := hdisjoint s hs
    have hcard_map : (s.map ⟨shift, hshift_inj⟩).card = s.card := by
      exact Finset.card_map (⟨shift, hshift_inj⟩ : Fin m ↪ Fin m)
    have hcard_union : (s ∪ s.map ⟨shift, hshift_inj⟩).card = 2 * s.card := by
      rw [Finset.card_union_of_disjoint hd, hcard_map, two_mul]
    exact hcard_union ▸ le_trans (Finset.card_le_univ _) (by simp)
  have hupper' : ∀ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) →
      s.card ≤ m / 2 := by
    intro s hindep
    rw [Nat.le_div_iff_mul_le zero_lt_two]
    linarith [hupper s hindep]
  -- Flower: there exists an independent set of size m/2
  have flower : ∃ s : Finset (Fin m), (cycle m).toSimple.IsIndepSet (s : Set (Fin m)) ∧ s.card = m / 2 := by
    -- Use the set of odd-valued vertices
    let s := Finset.image (fun (a : Fin (m / 2)) => ⟨2 * a.val + 1, by omega⟩ : Fin (m / 2) → Fin m) Finset.univ
    refine ⟨s, ?_, ?_⟩
    · -- s is independent
      intro x hx y hy hxy hadj
      rw [Finset.mem_coe, Finset.mem_image] at hx
      rw [Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      rw [habj] at hadj
      obtain ⟨hne, hcase⟩ := hadj
      have ha_lt : a.val < m / 2 := a.isLt
      have hb_lt : b.val < m / 2 := b.isLt
      have h2a1_lt_m : 2 * a.val + 1 < m := by omega
      have h2b1_lt_m : 2 * b.val + 1 < m := by omega
      -- Fin.val of our constructed elements
      have hval_a : ((⟨2 * a.val + 1, by omega⟩ : Fin m).val) = 2 * a.val + 1 := by
        simp
      have hval_b : ((⟨2 * b.val + 1, by omega⟩ : Fin m).val) = 2 * b.val + 1 := by
        simp
      -- (v+1) as Fin m: (2*k+1)+1 = 2*k+2. Two cases: 2*k+2 < m or 2*k+2 = m.
      -- In either case ((v+1).val) is even.
      have h2a2_le_m : 2 * a.val + 2 ≤ m := by omega
      have h2b2_le_m : 2 * b.val + 2 ≤ m := by omega
      -- (v1+1).val = (2*a+2) % m, which is even
      have hv1p1_val : ((⟨2 * a.val + 1, by omega⟩ : Fin m) + 1).val = (2 * a.val + 2) % m := by
        simp [Fin.val_add]
      have hv2p1_val : ((⟨2 * b.val + 1, by omega⟩ : Fin m) + 1).val = (2 * b.val + 2) % m := by
        simp [Fin.val_add]
      -- (2*k+2) % m is even since 2*k+2 ≤ m
      have heven_mod : ∀ k : ℕ, 2 * k + 2 ≤ m → ((2 * k + 2) % m) % 2 = 0 := by
        intro k hk
        by_cases hlt : 2 * k + 2 < m
        · rw [Nat.mod_eq_of_lt hlt]
          omega
        · have heq : 2 * k + 2 = m := by omega
          rw [heq, Nat.mod_self]
      have heven_v1 : ((⟨2 * a.val + 1, by omega⟩ : Fin m) + 1).val % 2 = 0 := by rw [hv1p1_val]; exact heven_mod a h2a2_le_m
      have heven_v2 : ((⟨2 * b.val + 1, by omega⟩ : Fin m) + 1).val % 2 = 0 := by rw [hv2p1_val]; exact heven_mod b h2b2_le_m
      -- adjacency requires even == odd, impossible
      rcases hcase with h | h
      · simp at h
        have h1 := heven_mod a h2a2_le_m
        rw [h] at h1
        omega
      · simp at h
        have h1 := heven_mod b h2b2_le_m
        rw [h] at h1
        omega
    · -- s has size m/2
      rw [Finset.card_image_of_injective _ (fun i j hij => by
        have := Fin.ext_iff.mp hij
        simp at this
        omega), Finset.card_fin]
  -- Now combine to get sSup = m/2
  have hindep_empty : (cycle m).toSimple.IsIndepSet (∅ : Set (Fin m)) := by
    simp [SimpleGraph.IsIndepSet]
  have hmem : m / 2 ∈ {n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s} := by
    obtain ⟨s, hind, hcard⟩ := flower
    exact ⟨s, SimpleGraph.IsNIndepSet.mk hind hcard⟩
  have hbdd : BddAbove {n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s} := by
    exact ⟨m, fun k ⟨s, hs⟩ => by
      rcases hs with ⟨hs_indep, hs_card⟩
      rw [hs_card.symm]
      show s.card ≤ m
      exact le_trans (Finset.card_le_univ s) (card_cycle m |> le_of_eq)⟩
  have hnonempty : ({n | ∃ s : Finset (Fin m), (cycle m).toSimple.IsNIndepSet n s}).Nonempty := by
    exact ⟨0, (∅ : Finset (Fin m)), SimpleGraph.IsNIndepSet.mk (by simp [SimpleGraph.IsIndepSet]) rfl⟩
  apply le_antisymm
  · apply csSup_le hnonempty
    intro b hb
    obtain ⟨s, hs⟩ := hb
    rcases hs with ⟨hs_indep, hs_card⟩
    rw [← hs_card]
    exact hupper' s hs_indep
  · apply le_csSup hbdd hmem

/-! ### Disjoint unions and joins -/

@[simp] theorem E_disjUnion : (disjUnion G H).E = G.E + H.E := by
  simp [CGraph.E]
  haveI : DecidableEq (G.V ⊕ H.V) := Classical.decEq _
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  -- Goal: Fintype.card ↑edgeSet ...
  -- Build injection from G.edgeSet to (G.disjUnion H).edgeSet via Sym2.map Sum.inl
  -- Build injection from H.edgeSet similarly. Show images disjoint and covering.
  -- Then use Fintype.card_congr.
  -- Step 1: Sym2.map Sum.inl and Sum.inr are injective
  have hinj_l : Function.Injective (Sym2.map (Sum.inl : G.V → G.V ⊕ H.V)) := by
    intro a b hab
    obtain ⟨x, y, rfl⟩ := Sym2.mk_surjective a
    obtain ⟨u, v, rfl⟩ := Sym2.mk_surjective b
    simp [Sym2.map, Quot.map] at hab
    apply Quot.sound
    rw [Sym2.rel_iff]
    rcases hab with h | h
    · exact Or.inl ⟨Sum.inl_injective (congr_arg Prod.fst h), Sum.inl_injective (congr_arg Prod.snd h)⟩
    · exact Or.inr ⟨Sum.inl_injective (congr_arg Prod.fst h), Sum.inl_injective (congr_arg Prod.snd h)⟩
  have hinj_r : Function.Injective (Sym2.map (Sum.inr : H.V → G.V ⊕ H.V)) := by
    intro a b hab
    obtain ⟨x, y, rfl⟩ := Sym2.mk_surjective a
    obtain ⟨u, v, rfl⟩ := Sym2.mk_surjective b
    simp [Sym2.map, Quot.map] at hab
    apply Quot.sound
    rw [Sym2.rel_iff]
    rcases hab with h | h
    · exact Or.inl ⟨Sum.inr_injective (congr_arg Prod.fst h), Sum.inr_injective (congr_arg Prod.snd h)⟩
    · exact Or.inr ⟨Sum.inr_injective (congr_arg Prod.fst h), Sum.inr_injective (congr_arg Prod.snd h)⟩
  -- Show forward direction: every edge of disjUnion is inl-image of G-edge or inr-image of H-edge
  -- Membership: inl-image of G-edges are disjUnion-edges
  have hmem_inl : ∀ e ∈ G.toSimple.edgeSet, Sym2.map Sum.inl e ∈ (G.disjUnion H).toSimple.edgeSet := by
    intro e he
    obtain ⟨a, b, hab, rfl⟩ := Sym2.mk_surjective e
    simp [Sym2.map, Quot.map]
    show Sym2.map (Sum.inl : G.V → G.V ⊕ H.V) (Sym2.mk a) ∈ (G.disjUnion H).toSimple.edgeSet
    simp only [Sym2.map, Quot.map]
    show Sym2.mk (Sum.inl a.1, Sum.inl a.2) ∈ (G.disjUnion H).toSimple.edgeSet
    rw [SimpleGraph.mem_edgeSet] at he ⊢
    rw [CGraph.toSimple_adj] at he
    simp [CGraph.toSimple_adj, disjUnion_adj_inl_inl, he]
  -- hmem_inr: inr-image of H-edges are disjUnion-edges
  have hmem_inr : ∀ e ∈ H.toSimple.edgeSet, Sym2.map (Sum.inr : H.V → G.V ⊕ H.V) e ∈ (G.disjUnion H).toSimple.edgeSet := by
    intro e he
    obtain ⟨a, b, hab, rfl⟩ := Sym2.mk_surjective e
    show Sym2.map (Sum.inr : H.V → G.V ⊕ H.V) (Sym2.mk a) ∈ (G.disjUnion H).toSimple.edgeSet
    simp only [Sym2.map, Quot.map]
    show Sym2.mk (Sum.inr a.1, Sum.inr a.2) ∈ (G.disjUnion H).toSimple.edgeSet
    rw [SimpleGraph.mem_edgeSet] at he ⊢
    rw [CGraph.toSimple_adj] at he
    simp [CGraph.toSimple_adj, disjUnion_adj_inr_inr, he]
  -- Cover: every disjUnion edge is inl-image of G-edge or inr-image of H-edge
  have hcover : ∀ s ∈ (G.disjUnion H).toSimple.edgeSet,
      (∃ e ∈ G.toSimple.edgeSet, Sym2.map (Sum.inl : G.V → G.V ⊕ H.V) e = s) ∨
      (∃ e ∈ H.toSimple.edgeSet, Sym2.map (Sum.inr : H.V → G.V ⊕ H.V) e = s) := by
    intro s hs
    obtain ⟨p, rfl⟩ := Quot.exists_rep s
    rw [SimpleGraph.mem_edgeSet] at hs
    rcases p with ⟨a | b, c | d⟩ <;> simp at hs
    · -- inl/inl
      left
      refine ⟨Sym2.mk (a, c), hs, ?_⟩
      simp [Sym2.map, Quot.map]
      rfl
    · -- inr/inr
      right
      refine ⟨Sym2.mk (b, d), hs, ?_⟩
      simp [Sym2.map, Quot.map]
      rfl
  -- inl-image and inr-image edges are disjoint
  have hnd : ∀ e ∈ G.toSimple.edgeSet, ∀ e' ∈ H.toSimple.edgeSet,
      Sym2.map (Sum.inl : G.V → G.V ⊕ H.V) e ≠ Sym2.map (Sum.inr : H.V → G.V ⊕ H.V) e' := by
    intro e he e' he' h_eq
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
    obtain ⟨⟨c, d⟩, rfl⟩ := Sym2.mk_surjective e'
    simp [Sym2.map, Quot.map] at h_eq
  -- The edge set is exactly the disjoint union of the two images
  have himage_in : Set.image (Sym2.map (Sum.inl : G.V → G.V ⊕ H.V)) ↑G.toSimple.edgeSet ⊆ ↑(G.disjUnion H).toSimple.edgeSet := by
    rintro _ ⟨e, he, rfl⟩; exact hmem_inl e he
  have himage_in' : Set.image (Sym2.map (Sum.inr : H.V → G.V ⊕ H.V)) ↑H.toSimple.edgeSet ⊆ ↑(G.disjUnion H).toSimple.edgeSet := by
    rintro _ ⟨e, he, rfl⟩; exact hmem_inr e he
  have himage_union : ↑(G.disjUnion H).toSimple.edgeSet ⊆
      Set.image (Sym2.map (Sum.inl : G.V → G.V ⊕ H.V)) ↑G.toSimple.edgeSet ∪
      Set.image (Sym2.map (Sum.inr : H.V → G.V ⊕ H.V)) ↑H.toSimple.edgeSet := by
    intro s hs; exact hcover s hs
  have heqv_set : ↑(G.disjUnion H).toSimple.edgeSet =
      Set.image (Sym2.map (Sum.inl : G.V → G.V ⊕ H.V)) ↑G.toSimple.edgeSet ∪
      Set.image (Sym2.map (Sum.inr : H.V → G.V ⊕ H.V)) ↑H.toSimple.edgeSet := by
    exact Set.Subset.antisymm himage_union (Set.union_subset himage_in himage_in')
  -- Build the equiv between edge sets
  let f : ↑G.toSimple.edgeSet ⊕ ↑H.toSimple.edgeSet → ↑(G.disjUnion H).toSimple.edgeSet :=
    Sum.elim (fun ⟨e, he⟩ => ⟨Sym2.map (Sum.inl : G.V → G.V ⊕ H.V) e, hmem_inl e he⟩)
             (fun ⟨e, he⟩ => ⟨Sym2.map (Sum.inr : H.V → G.V ⊕ H.V) e, hmem_inr e he⟩)
  -- f is injective
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rcases x with (⟨e₁, he₁⟩ | ⟨e₁, he₁⟩) <;> rcases y with (⟨e₂, he₂⟩ | ⟨e₂, he₂⟩)
    · simp [f] at hxy
      cases hinj_l hxy with rfl
    · simp [f] at hxy; exact False.elim (hnd e₁ he₁ e₂ he₂ hxy)
    · simp [f] at hxy; exact False.elim (hnd e₂ he₂ e₁ he₁ hxy.symm)
    · simp [f] at hxy
      cases hinj_r hxy with rfl
  -- f is surjective
  have hf_surj : Function.Surjective f := by
    intro ⟨s, hs⟩
    rcases hcover s hs with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact ⟨Sum.inl ⟨e, he⟩, rfl⟩
    · exact ⟨Sum.inr ⟨e, he⟩, rfl⟩
  let hequiv := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  rw [Fintype.card_congr hequiv.symm]
  exact Fintype.card_sum

@[simp] theorem indepNum_disjUnion : (disjUnion G H).indepNum = G.indepNum + H.indepNum := by
  simp only [CGraph.indepNum]
  -- The LHS graph is isomorphic to G.toSimple.sum H.toSimple
  have heq : (G.disjUnion H).toSimple = G.toSimple.sum H.toSimple := by
    ext x y
    simp [SimpleGraph.sum_adj, CGraph.toSimple_adj]
    cases x <;> cases y <;> simp [disjUnion_adj_inl_inl, disjUnion_adj_inr_inr, disjUnion_adj_inl_inr, disjUnion_adj_inr_inl]
  rw [heq]
  unfold SimpleGraph.indepNum
  set G' := G.toSimple
  set H' := H.toSimple
  classical
  set SG := {n : ℕ | ∃ s : Finset G.V, G'.IsNIndepSet n s} with SG_def
  set SH := {n : ℕ | ∃ s : Finset H.V, H'.IsNIndepSet n s} with SH_def
  set SL := {n : ℕ | ∃ s : Finset (G.V ⊕ H.V), (G' ⊕g H').IsNIndepSet n s} with SL_def
  --SG, SH bounded above
  have hSG_bdd : BddAbove SG := ⟨Fintype.card G.V, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ⟩
  have hSH_bdd : BddAbove SH := ⟨Fintype.card H.V, fun n ⟨s, hs⟩ => hs.card_eq ▸ s.card_le_univ⟩
  have hSL_bdd : BddAbove SL := ⟨Fintype.card G.V + Fintype.card H.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]
    exact s.card_le_univ.trans (by simp [Fintype.card_sum])⟩
  -- Step: SG + SH ⊆ SL (construct indep set in sum from indep sets in each side)
  have h_add_mem : ∀ a ∈ SG, ∀ b ∈ SH, a + b ∈ SL := by
    rintro a ha b hb
    obtain ⟨sG, hsG⟩ := ha
    obtain ⟨sH, hsH⟩ := hb
    let embL : G.V ↪ G.V ⊕ H.V := ⟨Sum.inl, Sum.inl_injective⟩
    let embR : H.V ↪ G.V ⊕ H.V := ⟨Sum.inr, Sum.inr_injective⟩
    have hdisjoint : Disjoint (Finset.map embL sG) (Finset.map embR sH) := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      simp [Finset.mem_map] at hxL hxR
      obtain ⟨a, ha, rfl⟩ := hxL
      obtain ⟨b, hb, hb'⟩ := hxR
      cases hb'
    have hasmp : (Finset.map embL sG ⊔ Finset.map embR sH) = Finset.map embL sG ∪ Finset.map embR sH := rfl
    have hc : (Finset.map embL sG ⊔ Finset.map embR sH).card = a + b := by
      rw [hasmp, Finset.card_union_of_disjoint hdisjoint]
      simp [Finset.card_map, embL, embR, hsG.card_eq, hsH.card_eq]
    refine ⟨sG.map embL ⊔ sH.map embR, ?_, hc⟩
    show (G' ⊕g H').IsIndepSet (↑(sG.map embL ⊔ sH.map embR))
    unfold SimpleGraph.IsIndepSet
    simp
    intro v hv w hw hvw
    simp only [Set.mem_union, Set.mem_image] at hv hw
    rcases hv with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> rcases hw with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
      simp at hvw ⊢
    · intro hadj; exact hsG.1 hx hy hvw (by simpa using hadj)
    · intro hadj; exact hsH.1 hx hy hvw (by simpa using hadj)
  -- 0 ∈ SG and 0 ∈ SH (empty independent set)
  have h0_SG : 0 ∈ SG := ⟨∅, by simp [SimpleGraph.IsNIndepSet.mk, SimpleGraph.IsIndepSet]⟩
  have h0_SH : 0 ∈ SH := ⟨∅, by simp [SimpleGraph.IsNIndepSet.mk, SimpleGraph.IsIndepSet]⟩
  -- Every element of SL is ≤ sSup SG + sSup SH
  have h_le_each : ∀ n ∈ SL, n ≤ sSup SG + sSup SH := by
    intro n hn
    obtain ⟨s, hs⟩ := hn
    -- Define sL and sR as finsets of vertices in G.V and H.V whose inl/inr is in s
    let sL := Finset.filter (fun a => (Sum.inl a : G.V ⊕ H.V) ∈ s) Finset.univ
    let sR := Finset.filter (fun b => (Sum.inr b : G.V ⊕ H.V) ∈ s) Finset.univ
    -- sL is indep in G', sR is indep in H'
    have hsL_ind : G'.IsIndepSet (sL : Set G.V) := by
      unfold SimpleGraph.IsIndepSet
      intro a ha c hc hac
      simp [sL] at ha hc
      have hsum_adj : ¬(G' ⊕g H').Adj (Sum.inl a) (Sum.inl c) := by
        have := hs.1 ha hc (Sum.inl_injective.ne hac)
        simpa [SimpleGraph.sum_adj] using this
      simpa [SimpleGraph.sum_adj] using hsum_adj
    have hsR_ind : H'.IsIndepSet (sR : Set H.V) := by
      unfold SimpleGraph.IsIndepSet
      intro b hb d hd hbd
      simp [sR] at hb hd
      have hsum_adj : ¬(G' ⊕g H').Adj (Sum.inr b) (Sum.inr d) := by
        have := hs.1 hb hd (Sum.inr_injective.ne hbd)
        simpa [SimpleGraph.sum_adj] using this
      simpa [SimpleGraph.sum_adj] using hsum_adj
    -- card s = card sL + card sR
    have hcard : s.card = sL.card + sR.card := by
      let embL : G.V ↪ G.V ⊕ H.V := ⟨Sum.inl, Sum.inl_injective⟩
      let embR : H.V ↪ G.V ⊕ H.V := ⟨Sum.inr, Sum.inr_injective⟩
      have hsum_eq : s = sL.map embL ∪ sR.map embR := by
        ext v
        simp [sL, sR, embL, embR, Finset.mem_map, Finset.mem_union, Finset.mem_filter, Finset.mem_univ]
        cases v <;> simp
      have hdisjoint : Disjoint (sL.map embL) (sR.map embR) := by
        rw [Finset.disjoint_left]
        intro x hxL hxR
        simp [embL, embR, Finset.mem_map] at hxL hxR
        obtain ⟨a, ha, rfl⟩ := hxL
        obtain ⟨b, hb, hb'⟩ := hxR
        cases hb'
      rw [hsum_eq, Finset.card_union_of_disjoint hdisjoint,
          Finset.card_map embL,
          Finset.card_map embR]
    -- sL.card ≤ sSup SG, sR.card ≤ sSup SH
    have hcard_L : sL.card ≤ sSup SG := by
      apply le_csSup hSG_bdd
      exact ⟨sL, ⟨hsL_ind, rfl⟩⟩
    have hcard_R : sR.card ≤ sSup SH := by
      apply le_csSup hSH_bdd
      exact ⟨sR, ⟨hsR_ind, rfl⟩⟩
    rw [← hs.card_eq, hcard]
    exact add_le_add hcard_L hcard_R
  -- RHS ≤ LHS: sSup SG + sSup SH ≤ sSup SL
  have h_sum_subset : {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} ⊆ SL := by
    rintro n ⟨a, ha, b, hb, rfl⟩; exact h_add_mem a ha b hb
  have h_nonempty_sum : (∃ n, n ∈ {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n}) := ⟨0 + 0, 0, h0_SG, 0, h0_SH, rfl⟩
  have h_bdd_sum : BddAbove {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} := by
    exact ⟨sSup SG + sSup SH, fun n ⟨a, ha, b, hb, hn⟩ => hn ▸ add_le_add (le_csSup hSG_bdd ha) (le_csSup hSH_bdd hb)⟩
  have h_sSup_sum_le : sSup {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} ≤ sSup SL :=
    csSup_le h_nonempty_sum (fun n hn => le_csSup hSL_bdd (h_sum_subset hn))
  have h_sSup_mem (S : Set ℕ) (hSne : S.Nonempty) (hSbb : BddAbove S) : sSup S ∈ S := by
    have hfin : S.Finite := Set.Finite.subset (Set.finite_Iic hSbb.choose) (fun x hx => hSbb.choose_spec hx)
    have hmem_aux : hfin.toFinset.max' (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx)) ∈ S := by
      have := Finset.max'_mem (hfin.toFinset) (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx))
      exact hfin.mem_toFinset.mp this
    have hsSup_eq_max' : sSup S = hfin.toFinset.max' (hSne.imp (fun x hx => hfin.mem_toFinset.mpr hx)) := by
      apply le_antisymm
      · exact csSup_le hSne (fun x hx => Finset.le_max' _ _ (hfin.mem_toFinset.mpr hx))
      · apply le_csSup hSbb hmem_aux
    rw [hsSup_eq_max']
    exact hmem_aux
  have h_sSup_add : sSup SG + sSup SH ≤ sSup {n | ∃ a ∈ SG, ∃ b ∈ SH, a + b = n} := by
    exact le_csSup h_bdd_sum ⟨sSup SG, h_sSup_mem SG ⟨0, h0_SG⟩ hSG_bdd, sSup SH, h_sSup_mem SH ⟨0, h0_SH⟩ hSH_bdd, rfl⟩
  have h_rtl : sSup SG + sSup SH ≤ sSup SL := le_trans h_sSup_add h_sSup_sum_le
  -- LHS ≤ RHS: sSup SL ≤ sSup SG + sSup SH
  have h_ltr : sSup SL ≤ sSup SG + sSup SH := by
    apply csSup_le'
    intro n hn
    exact h_le_each n hn
  exact le_antisymm h_ltr h_rtl

@[simp] theorem cliqueNum_disjUnion :
    (disjUnion G H).cliqueNum = max G.cliqueNum H.cliqueNum := by
  simp only [CGraph.cliqueNum]
  letI := Classical.decEq G.V
  letI := Classical.decEq H.V
  let SG := G.toSimple
  let SH := H.toSimple
  let SD := (G.disjUnion H).toSimple
  show SD.cliqueNum = max SG.cliqueNum SH.cliqueNum
  unfold SimpleGraph.cliqueNum
  -- Define the sets of achievable clique sizes
  set SC := {n : ℕ | ∃ s : Finset (G.V ⊕ H.V), SD.IsNClique n s}
  set SSG := {n : ℕ | ∃ s : Finset G.V, SG.IsNClique n s}
  set SSH := {n : ℕ | ∃ s : Finset H.V, SH.IsNClique n s}
  -- Helper: Fintype.card of G.V ⊕ H.V bounds all clique sizes in SD
  have hbound : ∀ n ∈ SC, n ≤ Fintype.card (G.V ⊕ H.V) := by
    rintro n ⟨s, hs⟩
    have hcard := hs.card_eq
    rw [← hcard]
    exact s.card_le_univ
  -- SC is bounded above
  have hSC_bdd : BddAbove SC := ⟨Fintype.card (G.V ⊕ H.V), hbound⟩
  -- Lower bounds: embedding cliques from G and H into disjUnion
  have hSSG : ∀ n ∈ SSG, n ≤ sSup SC := by
    rintro n ⟨s, hs⟩
    apply le_csSup hSC_bdd
    use s.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V)
    constructor
    · -- IsClique / pairwise adj
      intro a ha b hb hab
      simp [Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxy : x ≠ y := fun heq => hab (by rw [heq])
      show SD.Adj (Sum.inl x) (Sum.inl y)
      simp only [SD, CGraph.toSimple]
      rw [disjUnion_adj_inl_inl]
      rcases hs with ⟨hadj, hcard⟩
      exact hadj hx hy hxy
    · -- card
      rw [Finset.card_map]; exact hs.card_eq
  have hSSH : ∀ n ∈ SSH, n ≤ sSup SC := by
    rintro n ⟨s, hs⟩
    apply le_csSup hSC_bdd
    use s.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V)
    constructor
    · -- IsClique / pairwise adj
      intro a ha b hb hab
      simp [Set.mem_image] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxy : x ≠ y := fun heq => hab (by rw [heq])
      show SD.Adj (Sum.inr x) (Sum.inr y)
      simp only [SD, CGraph.toSimple]
      rw [disjUnion_adj_inr_inr]
      rcases hs with ⟨hadj, hcard⟩
      exact hadj hx hy hxy
    · rw [Finset.card_map]
      exact hs.card_eq
  -- SSG is bounded above
  have hSSG_bdd : BddAbove SSG := ⟨Fintype.card G.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]; exact s.card_le_univ⟩
  -- SSH is bounded above
  have hSSH_bdd : BddAbove SSH := ⟨Fintype.card H.V, fun n ⟨s, hs⟩ => by
    rw [← hs.card_eq]; exact s.card_le_univ⟩
  -- Lower bound from G: SG.cliqueNum ≤ SD.cliqueNum
  have hle_G : sSup SSG ≤ sSup SC := by
    apply csSup_le _ hSSG
    exact ⟨0, ∅, by simp⟩
  -- Lower bound from H
  have hle_H : sSup SSH ≤ sSup SC := by
    apply csSup_le _ hSSH
    exact ⟨0, ∅, by simp⟩
  -- Lower bound: max ≤ SD
  have hlower : max (sSup SSG) (sSup SSH) ≤ sSup SC := max_le hle_G hle_H
  -- Upper bound: SD ≤ max
  -- Key: every SD-clique comes from G or H
  -- If s is a clique in SD containing an inl vertex, then all vertices of s are inl.
  have hclique_inl : ∀ (s : Finset (G.V ⊕ H.V)) (n : ℕ) (x₀ : G.V),
      Sum.inl x₀ ∈ s → SD.IsNClique n s →
      ∃ t : Finset G.V, SG.IsNClique n t ∧ s = t.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V) := by
    intro s n x₀ hinx₀ hnc
    have hall_inl : ∀ y ∈ s, ∃ a : G.V, y = Sum.inl a := by
      intro y hy
      cases y with
      | inl a => exact ⟨a, rfl⟩
      | inr b =>
        exfalso
        rcases hnc with ⟨hclique, _⟩
        have hineq : (Sum.inl x₀ : G.V ⊕ H.V) ≠ Sum.inr b := by intro h; cases h
        have hadj : SD.Adj (Sum.inl x₀) (Sum.inr b) := hclique hinx₀ hy hineq
        simp [SD, CGraph.toSimple, disjUnion_adj_inl_inr] at hadj
    let decoder : G.V ⊕ H.V → G.V := Sum.elim id (fun _ => x₀)
    have hinl_decoder : ∀ y ∈ s, Sum.inl (decoder y) = y := by
      intro y hy; obtain ⟨a, rfl⟩ := hall_inl y hy; simp [decoder]
    let t := s.image decoder
    have ht_card : t.card = s.card := by
      rw [Finset.card_image_of_injOn]
      intro y hy z hz h_eq
      have hy' := hinl_decoder y hy
      have hz' := hinl_decoder z hz
      exact hy'.symm.trans (congr_arg Sum.inl h_eq ▸ hz')
    have hs_card : s.card = n := hnc.card_eq
    refine ⟨t, ?_, ?_⟩
    · have ht_n : t.card = n := ht_card.symm ▸ hs_card
      exact ⟨fun a ha b hb hab => by
        rw [Finset.mem_coe, Finset.mem_image] at ha hb
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨z, hz, rfl⟩ := hb
        show SG.Adj (decoder y) (decoder z)
        rcases hnc with ⟨hclique, _⟩
        have hadj := hclique hy hz (by intro heq; apply hab; rw [heq])
        show SG.Adj (decoder y) (decoder z)
        rw [CGraph.toSimple_adj]
        show G.Adj (decoder y) (decoder z) = true
        rw [← disjUnion_adj_inl_inl G H (decoder y) (decoder z)]
        rw [hinl_decoder y hy, hinl_decoder z hz]
        rw [CGraph.toSimple_adj] at hadj
        exact hadj, ht_n⟩
    · show s = t.map (⟨Sum.inl, Sum.inl_injective⟩ : G.V ↪ G.V ⊕ H.V)
      ext y
      simp [Finset.mem_map]
      exact ⟨fun hy => ⟨decoder y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hinl_decoder y hy⟩,
             fun ⟨a, ha, hxy⟩ => by
               obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
               have heq : Sum.inl a = z := Eq.trans (congr_arg Sum.inl hza.symm) (hinl_decoder z hz)
               exact hxy.symm ▸ heq ▸ hz⟩
  -- Similarly for inr.
  have hclique_inr : ∀ (s : Finset (G.V ⊕ H.V)) (x₀ : H.V),
      Sum.inr x₀ ∈ s → SD.IsNClique s.card s →
      ∃ t : Finset H.V, SH.IsNClique t.card t ∧ s = t.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V) := by
    intro s x₀ hinx₀ hnc
    have hall_inr : ∀ y ∈ s, ∃ b : H.V, y = Sum.inr b := by
      intro y hy
      cases y with
      | inl a =>
        exfalso
        rcases hnc with ⟨hclique, _⟩
        have hineq : (Sum.inr x₀ : G.V ⊕ H.V) ≠ Sum.inl a := by intro h; cases h
        have hadj : SD.Adj (Sum.inr x₀) (Sum.inl a) := hclique hinx₀ hy hineq
        simp [SD, CGraph.toSimple, disjUnion_adj_inr_inl] at hadj
      | inr b => exact ⟨b, rfl⟩
    let encoder : G.V ⊕ H.V → H.V := Sum.elim (fun _ => x₀) id
    have hinr_encoder : ∀ y ∈ s, Sum.inr (encoder y) = y := by
      intro y hy; obtain ⟨b, rfl⟩ := hall_inr y hy; simp [encoder]
    let t := s.image encoder
    have ht_card : t.card = s.card := by
      rw [Finset.card_image_of_injOn]
      intro y hy z hz h_eq
      have hy' := hinr_encoder y hy
      have hz' := hinr_encoder z hz
      exact hy'.symm.trans (congr_arg Sum.inr h_eq ▸ hz')
    refine ⟨t, ?_, ?_⟩
    · exact ⟨fun a ha b hb hab => by
        rw [Finset.mem_coe, Finset.mem_image] at ha hb
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨z, hz, rfl⟩ := hb
        show SH.Adj (encoder y) (encoder z)
        rcases hnc with ⟨hclique, _⟩
        have hadj := hclique hy hz (by intro heq; apply hab; exact (congr_arg encoder heq))
        show SH.Adj (encoder y) (encoder z)
        rw [CGraph.toSimple_adj]
        show H.Adj (encoder y) (encoder z) = true
        rw [← disjUnion_adj_inr_inr G H (encoder y) (encoder z)]
        rw [hinr_encoder y hy, hinr_encoder z hz]
        rw [CGraph.toSimple_adj] at hadj
        exact hadj, rfl⟩
    · show s = t.map (⟨Sum.inr, Sum.inr_injective⟩ : H.V ↪ G.V ⊕ H.V)
      ext y
      simp [Finset.mem_map]
      exact ⟨fun hy => ⟨encoder y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hinr_encoder y hy⟩,
             fun ⟨a, ha, hxy⟩ => by
               obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
               have heq : Sum.inr a = z := Eq.trans (congr_arg Sum.inr hza.symm) (hinr_encoder z hz)
               exact hxy.symm ▸ heq ▸ hz⟩
  have hmem : ∀ n ∈ SC, n ∈ SSG ∨ n ∈ SSH := by
    rintro n ⟨s, hs⟩
    by_cases hempty : s = ∅
    · subst hempty
      have hn0 : n = 0 := hs.card_eq.symm
      subst hn0
      left; exact ⟨∅, by simp⟩
    · obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hempty
      cases v with
      | inl x =>
        left
        obtain ⟨t, ht1, ht2⟩ := hclique_inl s n x hv hs
        exact ⟨t, ht1⟩
      | inr x =>
        right
        have hs_card_eq : s.card = n := hs.card_eq
        have hs' : SD.IsNClique s.card s := ⟨by rcases hs with ⟨hc, _⟩; exact hc, rfl⟩
        obtain ⟨t, ht1, ht2⟩ := hclique_inr s x hv hs'
        have : t.card = n := by
          have := congr_arg Finset.card ht2
          simp [Finset.card_map] at this
          exact this.symm ▸ hs_card_eq
        exact ⟨t, this ▸ ht1⟩
  have hupper : sSup SC ≤ max (sSup SSG) (sSup SSH) := by
    apply csSup_le
    · exact ⟨0, ⟨∅, by simp⟩⟩
    · intro n hn
      rcases hmem n hn with h | h
      · exact le_max_of_le_left (le_csSup hSSG_bdd h)
      · exact le_max_of_le_right (le_csSup hSSH_bdd h)
  exact le_antisymm hupper hlower

/-- The disjoint union is commutative up to isomorphism — which is exactly what equality in
`IsoGraph` means. -/
theorem disjUnion_comm : Nonempty (disjUnion G H ≃cg disjUnion H G) :=
  let e : (G.disjUnion H).V ≃ (H.disjUnion G).V := Equiv.sumComm G.V H.V
  have he1 : ∀ a : G.V, e (Sum.inl a) = Sum.inr a := fun a => Equiv.sumComm_apply (α := G.V) (β := H.V) ▸ rfl
  have he2 : ∀ b : H.V, e (Sum.inr b) = Sum.inl b := fun b => Equiv.sumComm_apply (α := G.V) (β := H.V) ▸ rfl
  ⟨RelIso.mk e (by
        intro x y
        rcases x with _ | _ <;> rcases y with _ | _ <;>
          simp [he1, he2, disjUnion_adj_inl_inl, disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, disjUnion_adj_inr_inr] )⟩

theorem disjUnion_assoc (K : CGraph) :
    Nonempty (disjUnion (disjUnion G H) K ≃cg disjUnion G (disjUnion H K)) :=
  by exact ⟨RelIso.mk (Equiv.sumAssoc G.V H.V K.V) (by
  intro a b
  simp only [disjUnion]
  dsimp [Equiv.sumAssoc]
  cases a with
  | inl x =>
    cases x with
    | inl a =>
      cases b with
      | inl y =>
        cases y with
        | inl c => simp
        | inr d => simp
      | inr y => simp
    | inr hb =>
      cases b with
      | inl y => cases y with | inl c => simp | inr d => simp
      | inr y => simp
  | inr hc =>
    cases b with
    | inl y => cases y with | inl c => simp | inr d => simp
    | inr y => simp)⟩

theorem not_isConnected_disjUnion (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) :
    ¬(disjUnion G H).IsConnected := by
  simp only [CGraph.IsConnected]
  intro h
  have hGne : Nonempty G.V := Fintype.card_pos_iff.mp hG
  have hHne : Nonempty H.V := Fintype.card_pos_iff.mp hH
  let a := hGne.some
  let b := hHne.some
  have hr : (disjUnion G H).toSimple.Reachable (.inl a) (.inr b) := h (Sum.inl a) (.inr b)
  -- Key lemma: adjacency preserves "side" (inl vs inr)
  let side : (G.V ⊕ H.V) → Bool := fun | Sum.inl _ => true | Sum.inr _ => false
  have side_eq_of_adj : ∀ (x y : G.V ⊕ H.V), (disjUnion G H).Adj x y → side x = side y := by
    intro x y h_adj
    cases x with
    | inl a =>
      cases y with
      | inl c => simp [side]
      | inr d => simp [disjUnion_adj_inl_inr] at h_adj
    | inr b =>
      cases y with
      | inl c => simp [disjUnion_adj_inr_inl] at h_adj
      | inr d => simp [side]
  -- Adjacency preserves side, so Reachability preserves side
  have keep_side : ∀ {u v : G.V ⊕ H.V}, (disjUnion G H).toSimple.Reachable u v → side u = side v := by
    intro u v huv
    show side u = side v
    induction huv
    rename_i w
    induction w with
    | nil => rfl
    | @cons w' x y hp e ih => rw [side_eq_of_adj _ _ hp, ih]
  -- inl a and inr b have different sides, contradiction
  have hside : side (.inl a) = true := rfl
  have hside2 : side (.inr b) = false := rfl
  have := keep_side hr
  simp [hside, hside2] at this

@[simp] theorem E_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).E = G.E + H.E + Fintype.card G.V * Fintype.card H.V := by
  have h1 : (join G H).E + (disjUnion (compl G) (compl H)).E = (Fintype.card (join G H).V).choose 2 := by
    rw [join]
    exact E_compl _
  have h2 : (disjUnion (compl G) (compl H)).E = (compl G).E + (compl H).E := E_disjUnion _ _
  have h3 : (compl G).E + G.E = (Fintype.card G.V).choose 2 := E_compl G
  have h4 : (compl H).E + H.E = (Fintype.card H.V).choose 2 := E_compl H
  have h5 : Fintype.card (join G H).V = Fintype.card G.V + Fintype.card H.V := card_join G H
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

theorem isConnected_join [DecidableEq G.V] [DecidableEq H.V]
    (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) : (join G H).IsConnected := by
  simp only [IsConnected, join, compl, CGraph.toSimple]
  have hcross : ∀ (a : G.V) (b : H.V),
      ((join G H).toSimple.Adj (Sum.inl a) (Sum.inr b) = true) := by
    simp [join, compl, CGraph.toSimple, disjUnion_adj_inl_inr]
  have hcross' : ∀ (a : G.V) (b : H.V),
      ((join G H).toSimple.Adj (Sum.inr b) (Sum.inl a) = true) := by
    simp [join, compl, CGraph.toSimple, disjUnion_adj_inr_inl]
  set J := (join G H).toSimple
  obtain ⟨a0⟩ := Fintype.card_pos_iff.mp hG
  obtain ⟨b0⟩ := Fintype.card_pos_iff.mp hH
  let walk_inl_inr (a : G.V) (b : H.V) : J.Walk (Sum.inl a) (Sum.inr b) :=
    SimpleGraph.Walk.cons (by rw [hcross a b]) SimpleGraph.Walk.nil
  let walk_inr_inl (b : H.V) (a : G.V) : J.Walk (Sum.inr b) (Sum.inl a) :=
    SimpleGraph.Walk.cons (by rw [hcross' a b]) SimpleGraph.Walk.nil
  have hreach : ∀ v : (join G H).V, J.Reachable (Sum.inl a0) v := by
    intro v
    match v with
    | Sum.inl a => exact ⟨(walk_inl_inr a0 b0).append (walk_inr_inl b0 a)⟩
    | Sum.inr b => exact ⟨walk_inl_inr a0 b⟩
  show J.Connected
  have hne : Nonempty (G.join H).V := ⟨Sum.inl a0⟩
  exact ⟨fun u v => ⟨(SimpleGraph.Reachable.symm (hreach u)).some.append ((hreach v).some)⟩⟩

@[simp] theorem cliqueNum_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).cliqueNum = G.cliqueNum + H.cliqueNum := by
  simp only [join, cliqueNum_compl, indepNum_disjUnion, indepNum_compl]

@[simp] theorem indepNum_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).indepNum = max G.indepNum H.indepNum := by
  -- The goal: (join G H).toSimple.indepNum = max G.toSimple.indepNum H.toSimple.indepNum
  -- Join has all cross edges, so indep sets don't span both sides.
  -- I'll prove it by showing both ≤ and ≥.
  rw [join, indepNum_compl]
  -- Helper: cliqueNum monotone under embedding
  have cliqueNum_le_of_emb {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      {G : SimpleGraph X} {H : SimpleGraph Y} (f : G ↪g H) : G.cliqueNum ≤ H.cliqueNum := by
    unfold SimpleGraph.cliqueNum
    apply csSup_le_csSup
    · exact ⟨Fintype.card Y, fun n ⟨t, ht⟩ => ht.card_eq ▸ Finset.card_le_univ t⟩
    · exact ⟨0, ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    · rintro n ⟨s, hs⟩
      have hcard : (s.map f.toEmbedding).card = n := by simp [hs.card_eq]
      have hclique : H.IsClique ((fun a => f a) '' ↑s) := by
        intro a ha b hb hab
        simp at ha hb hab
        obtain ⟨xa, hxa, rfl⟩ := ha
        obtain ⟨xb, hxb, rfl⟩ := hb
        have hne : xa ≠ xb := by
          intro heq; exact hab (by rw [heq])
        exact f.map_rel_iff.mpr (hs.isClique hxa hxb hne)
      have heq : ((fun a => f a) '' (s : Set X)) = ↑(s.map f.toEmbedding) := by
        ext y; simp
      rw [heq] at hclique
      exact ⟨_, SimpleGraph.IsNClique.mk hclique hcard⟩
  -- Embed compl G and compl H into disjUnion (compl G) (compl H)
  have hge_left : cliqueNum (compl G) ≤ cliqueNum (disjUnion (compl G) (compl H)) := by
    apply cliqueNum_le_of_emb
    exact { toFun := Sum.inl, inj' := Sum.inl_injective,
            map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion, compl] }
  have hge_right : cliqueNum (compl H) ≤ cliqueNum (disjUnion (compl G) (compl H)) := by
    apply cliqueNum_le_of_emb
    exact { toFun := Sum.inr, inj' := Sum.inr_injective,
            map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion, compl] }
  have hge : max (cliqueNum (compl G)) (cliqueNum (compl H)) ≤ cliqueNum (disjUnion (compl G) (compl H)) :=
    max_le hge_left hge_right
  -- Cross pairs are not adjacent in disjUnion
  have hno_cross : ∀ (a : G.compl.V) (b : H.compl.V),
      ¬(disjUnion G.compl H.compl).toSimple.Adj (Sum.inl a) (Sum.inr b) := by
    simp [CGraph.toSimple, disjUnion, compl]
  -- Any clique in disjUnion is in one side
  have clique_one_side : ∀ (C : Finset (G.compl.V ⊕ H.compl.V))
      (hC : (disjUnion G.compl H.compl).toSimple.IsNClique C.card C),
      (∀ x ∈ C, x.isLeft = true) ∨ (∀ x ∈ C, x.isRight = true) := by
    intro C hC
    by_contra h
    push_neg at h
    obtain ⟨hx, hy⟩ := h
    obtain ⟨px, hpx, hx'⟩ := hx
    obtain ⟨py, hpy, hy'⟩ := hy
    obtain ⟨b, rfl⟩ : ∃ b, px = Sum.inr b := by
      match px with
      | Sum.inl a => simp at hx'
      | Sum.inr b => exact ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, py = Sum.inl c := by
      match py with
      | Sum.inl c => exact ⟨c, rfl⟩
      | Sum.inr d => simp at hy'
    exact hno_cross c b (hC.isClique hpx hpy (by intro h; cases h))
  have hle : cliqueNum (disjUnion (compl G) (compl H)) ≤
      max (cliqueNum (compl G)) (cliqueNum (compl H)) := by
    let embL : (compl G).toSimple ↪g (disjUnion (compl G) (compl H)).toSimple :=
      { toFun := Sum.inl, inj' := Sum.inl_injective,
        map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion, compl] }
    let embR : (compl H).toSimple ↪g (disjUnion (compl G) (compl H)).toSimple :=
      { toFun := Sum.inr, inj' := Sum.inr_injective,
        map_rel_iff' := @fun a b => by simp [CGraph.toSimple, disjUnion, compl] }
    simp only [CGraph.cliqueNum, SimpleGraph.cliqueNum]
    apply csSup_le
    · exact ⟨0, ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    · intro n hn
      obtain ⟨C, hC⟩ := hn
      have hside : (∀ x ∈ C, ∃ a : G.compl.V, x = Sum.inl a) ∨ (∀ x ∈ C, ∃ b : H.compl.V, x = Sum.inr b) := by
        by_contra h
        push_neg at h
        obtain ⟨hx, hy⟩ := h
        obtain ⟨px, hpx, hx'⟩ := hx
        obtain ⟨py, hpy, hy'⟩ := hy
        obtain ⟨b, rfl⟩ : ∃ b, px = Sum.inr b := by
          match px with
          | Sum.inl a => exfalso; exact hx' a rfl
          | Sum.inr b => exact ⟨b, rfl⟩
        obtain ⟨c, rfl⟩ : ∃ c, py = Sum.inl c := by
          match py with
          | Sum.inl c => exact ⟨c, rfl⟩
          | Sum.inr d => exfalso; exact hy' d rfl
        exact hno_cross c b (hC.isClique hpx hpy (by intro h; cases h))
      rcases hside with hleft | hright
      · -- All inl: Dav = {a | inl a ∈ C} is an n-clique in compl G
        let Dav : Finset (compl G).V := Finset.univ.filter (fun a => Sum.inl a ∈ C)
        have hinl_mem : ∀ x ∈ C, ∃ a, x = Sum.inl a := hleft
        have hDav_eq : Dav.map ⟨Sum.inl, Sum.inl_injective⟩ = C := by
          ext x; simp [Dav, Finset.mem_map]
          refine ⟨fun ⟨a, ha, hx⟩ => hx ▸ ha, fun hx => ?_⟩
          obtain ⟨a, ha'⟩ := hinl_mem x hx
          have ha_Dav : a ∈ Dav := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha'.symm ▸ hx⟩
          exact ⟨a, ha'.symm ▸ hx, ha'.symm⟩
        have hdav_card : Dav.card = n := by
          have h1 := congr_arg Finset.card hDav_eq
          simp [Finset.card_map] at h1
          exact h1.trans hC.card_eq
        have hdav_clique : (compl G).toSimple.IsClique (Dav : Set (compl G).V) := by
          intro a1 ha1 a2 ha2 ha12
          have ha1C : Sum.inl a1 ∈ C := Finset.mem_filter.mp ha1 |>.2
          have ha2C : Sum.inl a2 ∈ C := Finset.mem_filter.mp ha2 |>.2
          have hadj' : (disjUnion G.compl H.compl).toSimple.Adj (Sum.inl a1) (Sum.inl a2) :=
            hC.isClique (by exact ha1C) (by exact ha2C) (by intro h; exact ha12 (embL.injective h))
          exact embL.map_adj_iff.mp hadj'
        have hbddG : BddAbove {m | ∃ s : Finset (compl G).V, (compl G).toSimple.IsNClique m s} :=
          ⟨Fintype.card (compl G).V, fun m ⟨s, hs⟩ => hs.card_eq ▸ Finset.card_le_univ s⟩
        have hnG : n ∈ {m | ∃ s : Finset (compl G).V, (compl G).toSimple.IsNClique m s} :=
          ⟨Dav, SimpleGraph.IsNClique.mk hdav_clique hdav_card⟩
        exact le_max_of_le_left (le_csSup hbddG hnG)
      · let Dav : Finset (compl H).V := Finset.univ.filter (fun b => Sum.inr b ∈ C)
        have hinr_mem : ∀ x ∈ C, ∃ b, x = Sum.inr b := hright
        have hDav_eq : Dav.map ⟨Sum.inr, Sum.inr_injective⟩ = C := by
          ext x; simp [Dav, Finset.mem_map]
          refine ⟨fun ⟨b, hb, hx⟩ => hx ▸ hb, fun hx => ?_⟩
          obtain ⟨b, hb'⟩ := hinr_mem x hx
          have hb_Dav : b ∈ Dav := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb'.symm ▸ hx⟩
          exact ⟨b, hb'.symm ▸ hx, hb'.symm⟩
        have hdav_card : Dav.card = n := by
          have h1 := congr_arg Finset.card hDav_eq
          simp [Finset.card_map] at h1
          exact h1.trans hC.card_eq
        have hdav_clique : (compl H).toSimple.IsClique (Dav : Set (compl H).V) := by
          intro b1 hb1 b2 hb2 hb12
          have h1 : Sum.inr b1 ∈ C := Finset.mem_filter.mp hb1 |>.2
          have h2 : Sum.inr b2 ∈ C := Finset.mem_filter.mp hb2 |>.2
          have hadj' : (disjUnion G.compl H.compl).toSimple.Adj (Sum.inr b1) (Sum.inr b2) :=
            hC.isClique h1 h2 (by intro h; exact hb12 (embR.injective h))
          exact embR.map_adj_iff.mp hadj'
        have hbddH : BddAbove {m | ∃ s : Finset (compl H).V, (compl H).toSimple.IsNClique m s} :=
          ⟨Fintype.card (compl H).V, fun m ⟨s, hs⟩ => hs.card_eq ▸ Finset.card_le_univ s⟩
        have hnH : n ∈ {m | ∃ s : Finset (compl H).V, (compl H).toSimple.IsNClique m s} :=
          ⟨Dav, SimpleGraph.IsNClique.mk hdav_clique hdav_card⟩
        exact le_max_of_le_right (le_csSup hbddH hnH)
  have hle' : (G.compl.disjUnion H.compl).cliqueNum ≤ max G.indepNum H.indepNum := by
    rw [cliqueNum_compl, cliqueNum_compl] at hle; exact hle
  have hge' : max G.indepNum H.indepNum ≤ (G.compl.disjUnion H.compl).cliqueNum := by
    rw [cliqueNum_compl, cliqueNum_compl] at hge; exact hge
  exact le_antisymm hle' hge'

/-! ### Bipartite and multipartite graphs -/

@[simp] theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := by
  let G := disjUnion (complete m) (complete n)
  have h1 := E_compl (G := G)
  have h2 := E_disjUnion (G := complete m) (H := complete n)
  have h3 := E_complete m
  have h4 := E_complete n
  rw [h3, h4] at h2
  rw [h2] at h1
  rw [card_disjUnion, card_complete, card_complete] at h1
  -- bipartite m n = compl G
  have hbip : bipartite m n = compl G := rfl
  rw [hbip]
  have hdiv (k : ℕ) : 2 ∣ k * (k - 1) := by
    rcases k with _ | _ | k <;> simp [Nat.mul_succ, parity_simps]
    exact even_iff_two_dvd.mp (by simp [parity_simps])
  have h2' : 2 * (Nat.choose (m + n) 2) = (m + n) * (m + n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h3' : 2 * (Nat.choose m 2) = m * (m - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h4' : 2 * (Nat.choose n 2) = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (hdiv _)]
  have h1' : 2 * G.compl.E + 2 * m.choose 2 + 2 * n.choose 2 = 2 * (m + n).choose 2 := by
    linarith
  rw [h2', h3', h4'] at h1'
  generalize G.compl.E = e at h1'
  clear h1 h2 h3 h4 h2' h3' h4' hbip hdiv G
  have hgoal : e = m * n := by
    rcases m with _ | m <;> rcases n with _ | n
    · simp at h1'; omega
    · simp at h1'; omega
    · simp at h1'; omega
    · simp [Nat.succ_mul] at h1'
      have h1'' : e + e + (m * m + m) + (n * n + n) = (m + 1 + (n + 1)) * (m + 1 + n) := h1'
      have : 2 * e = 2 * ((m + 1) * (n + 1)) := by
        ring_nf at h1''
        clear h1'
        have he : e = m * n + m + n + 1 := by omega
        rw [he]; ring
      omega
  exact hgoal

@[simp] theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n := by
  simp only [bipartite]
  rw [indepNum_compl, cliqueNum_disjUnion, cliqueNum_complete, cliqueNum_complete]

@[simp] theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 := by
  simp only [bipartite, cliqueNum_compl, indepNum_disjUnion, indepNum_complete]
  omega

@[simp] theorem isConnected_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).IsConnected := by
  simp only [bipartite, CGraph.IsConnected, compl_toSimple]
  show SimpleGraph.Connected ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ
  haveI : Nonempty ((complete (m + 1)).disjUnion (complete (n + 1))).V := ⟨Sum.inl ⟨0, Nat.zero_lt_succ _⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  -- Pick a "hub" vertex on the right side
  let w : ((complete (m + 1)).disjUnion (complete (n + 1))).V := Sum.inr ⟨0, Nat.zero_lt_succ n⟩
  -- In the complement, every vertex is adjacent to w (since w is in right, and for any x,
  -- if x is in left, they're across partitions so adjacent in complement;
  -- if x is in right and x ≠ w, wait, they're in the same partition... hmm)
  -- Actually in the complement, inl-* is NOT adjacent to inr-* ... wait yes it is.
  -- complement of disjUnion: adj iff NOT (same side and adj in that side).
  -- For inl a and inr b: same side? No. So NOT false = true. Adjacent! ✓
  -- For inl a and inl c (a ≠ c): same side yes, adj in complete yes, so NOT true = false. Not adjacent.
  -- For inr b and inr d (b ≠ d): same道理.
  -- For inr b and w = inr ⟨0,...⟩ when b = 0 (and b ≠ w is impossible since w is inr 0):
  --   They're the same vertex when b = ⟨0,...⟩, or same-side adjacent in G so not adjacent in complement.
  -- So NOT every vertex is adjacent to w. Only vertices on the left side are adjacent to w in the complement.
  -- Vertices on the right side (different from w) are NOT adjacent to w in the complement.
  -- But they ARE adjacent to vertices on the left side.
  -- So for reachability u → v:
  --   Case u=inl, v=inl: u → w → v (via left vertices adjacent to w)
  --   Case u=inl, v=inr: u → v directly (adjacent)
  --   Case u=inr, v=inl: u → v directly
  --   Case u=inr, v=inr: u → (some inl) → v
  -- We need a "hub" on the LEFT side for right-side vertices to use. Let's pick hub on left.
  let w' : ((complete (m + 1)).disjUnion (complete (n + 1))).V := Sum.inl ⟨0, Nat.zero_lt_succ m⟩
  -- In the complement, every RIGHT vertex is adjacent to w' (across partition).
  -- Left vertices ≠ w' are NOT adjacent to w' (same side, complete).
  -- Strategy: route EVERYTHING through both hubs. u → (if u on right, go to w'; if u on left, already on left)
  -- Actually, simplest: u → w' (if u on right, adj directly; if u on left and u ≠ w', not adj directly...)
  --Hmm. Let me think of a 2-hop strategy for everything.
  -- u=(inl a), v=(inl c): use any right vertex r. u→r (across, adj) and r→v (across, adj). So u→r→v.
  -- u=(inr b), v=(inr d): use any left vertex l. u→l→v.
  -- u=(inl a), v=(inr d): u→v directly.
  -- u=(inr b), v=(inl c): u→v directly.
  -- So I need: for any left vertex l0 and right vertex r0, use them as intermediaries.
  let r0 : ((complete (m + 1)).disjUnion (complete (n + 1))).V := Sum.inr ⟨0, Nat.zero_lt_succ n⟩
  -- Key adjacency facts in the complement:
  -- Cross-partition edges exist (complete bipartite structure)
  -- In the complement, cross-partition edges exist.
  have h_cross_adj : ∀ (a : Fin (m + 1)) (b : Fin (n + 1)),
      ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ.Adj (Sum.inl a) (Sum.inr b) := by
    intro a b
    simp [SimpleGraph.compl_adj, CGraph.toSimple_adj, disjUnion_adj_inl_inr]
  have h_cross_adj2 : ∀ (a : Fin (m + 1)) (b : Fin (n + 1)),
      ((complete (m + 1)).disjUnion (complete (n + 1))).toSimpleᶜ.Adj (Sum.inr b) (Sum.inl a) := by
    intro a b
    simp [SimpleGraph.compl_adj, CGraph.toSimple_adj, disjUnion_adj_inr_inl]
  -- Strategy for Reachable u v:
  -- • inl → inr: direct edge
  -- • inr → inl: direct edge  
  -- • inl → inl: go via any inr (2 hops)
  -- • inr → inr: go via any inl (2 hops)
  rcases u with ⟨a, ha⟩ | ⟨b, hb⟩ <;> rcases v with ⟨c, hc⟩ | ⟨d, hd⟩
  · -- inl → inl: via r0
    exact (h_cross_adj ⟨a, ha⟩ ⟨0, Nat.zero_lt_succ n⟩).reachable.trans
      (h_cross_adj2 ⟨c, hc⟩ ⟨0, Nat.zero_lt_succ n⟩).reachable
  · -- inl → inr: direct
    exact (h_cross_adj ⟨a, ha⟩ ⟨d, hd⟩).reachable
  · -- inr → inl: direct
    exact (h_cross_adj2 ⟨c, hc⟩ ⟨b, hb⟩).reachable
  · -- inr → inr: via w' (inl ⟨0,...⟩)
    exact (h_cross_adj2 ⟨0, Nat.zero_lt_succ m⟩ ⟨b, hb⟩).reachable.trans
      (h_cross_adj ⟨0, Nat.zero_lt_succ m⟩ ⟨d, hd⟩).reachable

@[simp] theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 := by
  set V₁ := Fin (m + 2)
  set V₂ := Fin (n + 2)
  set G : SimpleGraph (V₁ ⊕ V₂) := (bipartite (m + 2) (n + 2)).toSimple
  -- All pairs in different parts are adjacent
  have h_adj_cross : ∀ a : V₁, ∀ d : V₂, G.Adj (.inl a) (.inr d) := by
    intro a d
    simp only [G, bipartite, CGraph.toSimple_adj, compl]
    rw [disjUnion_adj_inl_inr]
    simp
  have h_adj_cross' : ∀ b : V₂, ∀ c : V₁, G.Adj (.inr b) (.inl c) := by
    intro b c; exact (h_adj_cross c b).symm
  -- No edges within part 1 (inl-inl), handled by... we don't need this explicitly
  -- All pairs in different parts have dist 1
  -- Pairs in the same part have dist 2 (via any vertex in the other part)
  -- No edges within each part
  have h_no_edge_inl_inl : ∀ a c : V₁, ¬G.Adj (.inl a) (.inl c) := by
    intro a c
    by_cases h : a = c <;> simp [G, bipartite, complete, disjUnion, h]
  have h_no_edge_inr_inr : ∀ b d : V₂, ¬G.Adj (.inr b) (.inr d) := by
    intro b d
    by_cases h : b = d <;> simp [G, bipartite, complete, disjUnion, h]
  -- The graph is connected
  have h_connected : G.Connected := by
    show SimpleGraph.Connected G
    exact ⟨fun u v => by
      cases u with
      | inl a =>
        cases v with
        | inl c =>
          exact ⟨SimpleGraph.Walk.append
            (SimpleGraph.Walk.cons (h_adj_cross a ⟨0, by omega⟩) (SimpleGraph.Walk.nil : G.Walk _ _))
            (SimpleGraph.Walk.cons (h_adj_cross' ⟨0, by omega⟩ c) (SimpleGraph.Walk.nil : G.Walk _ _))⟩
        | inr d =>
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross a d) (SimpleGraph.Walk.nil : G.Walk _ _)⟩
      | inr b =>
        cases v with
        | inl c =>
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross' b c) (SimpleGraph.Walk.nil : G.Walk _ _)⟩
        | inr d =>
          exact ⟨SimpleGraph.Walk.append
            (SimpleGraph.Walk.cons (h_adj_cross' b ⟨0, by omega⟩) (SimpleGraph.Walk.nil : G.Walk _ _))
            (SimpleGraph.Walk.cons (h_adj_cross ⟨0, by omega⟩ d) (SimpleGraph.Walk.nil : G.Walk _ _))⟩⟩
  -- Distance ≤ 2 for all pairs
  have h_edist_le_two : ∀ u v : V₁ ⊕ V₂, G.edist u v ≤ 2 := by
    intro u v
    cases u with
    | inl a =>
      cases v with
      | inl c =>
        -- Walk inl a → inr ⟨0,...⟩ → inl c, length 2
        have hw : ∃ w : G.Walk (.inl a) (.inl c), w.length = 2 := by
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross a ⟨0, by omega⟩)
            (SimpleGraph.Walk.cons (h_adj_cross' ⟨0, by omega⟩ c)
              (SimpleGraph.Walk.nil : G.Walk _ _)), by simp⟩
        obtain ⟨w, hw⟩ := hw
        exact le_trans (SimpleGraph.edist_le w) (by rw [hw]; decide)
      | inr d =>
        -- Adj, so edist ≤ 1
        have hw : ∃ w : G.Walk (.inl a) (.inr d), w.length = 1 := by
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross a d) (SimpleGraph.Walk.nil : G.Walk _ _), by simp⟩
        obtain ⟨w, hw⟩ := hw
        exact le_trans (SimpleGraph.edist_le w) (by rw [hw]; decide)
    | inr b =>
      cases v with
      | inl c =>
        have hw : ∃ w : G.Walk (.inr b) (.inl c), w.length = 1 := by
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross' b c) (SimpleGraph.Walk.nil : G.Walk _ _), by simp⟩
        obtain ⟨w, hw⟩ := hw
        exact le_trans (SimpleGraph.edist_le w) (by rw [hw]; decide)
      | inr d =>
        have hw : ∃ w : G.Walk (.inr b) (.inr d), w.length = 2 := by
          exact ⟨SimpleGraph.Walk.cons (h_adj_cross' b ⟨0, by omega⟩)
            (SimpleGraph.Walk.cons (h_adj_cross ⟨0, by omega⟩ d)
              (SimpleGraph.Walk.nil : G.Walk _ _)), by simp⟩
        obtain ⟨w, hw⟩ := hw
        exact le_trans (SimpleGraph.edist_le w) (by rw [hw]; decide)
  -- There exist u, v with distance ≥ 2 (in fact = 2): pick two distinct vertices in V₁
  have h_exists_dist_ge_two : ∃ u v : V₁ ⊕ V₂, 2 ≤ G.edist u v := by
    -- Pick two distinct vertices in V₁, say ⟨0,by omega⟩ and ⟨1,by omega⟩
    refine ⟨.inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, ?_⟩
    -- They're not adjacent, so edist is not 1. Since they're reachable and distinct, edist ≥ 2.
    have hreach : G.Reachable (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) :=
       h_connected _ _
    have hne : (.inl ⟨0, by omega⟩ : V₁ ⊕ V₂) ≠ .inl ⟨1, by omega⟩ := by simp
    have hnotadj := h_no_edge_inl_inl ⟨0, by omega⟩ ⟨1, by omega⟩
    -- Any walk from inl ⟨0⟩ to inl ⟨1⟩ has length ≥ 2 (since not adjacent, can't be length 1; and ne, can't be 0)
    -- So edist ≥ 2.
    have h_ge : 2 ≤ G.edist (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) := by
      by_contra hlt
      push_neg at hlt
      have h_ne0 : G.edist (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) ≠ 0 := by
        intro heq
        rw [SimpleGraph.edist_eq_zero_iff] at heq
        exact hne heq
      have h_ne_top : G.edist (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) ≠ ⊤ := by
        intro h
        obtain ⟨w⟩ := hreach
        have := SimpleGraph.edist_le w
        rw [h] at this
        exact absurd this (by simp)
      have h_ne1 : G.edist (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) ≠ 1 := by
        intro heq; exact hnotadj (SimpleGraph.edist_eq_one_iff_adj.mp heq)
      -- In ENat, < 2, ≠ ⊤, ≠ 0, ≠ 1 is impossible
      have : ∀ (x : ℕ∞), x < 2 → x ≠ ⊤ → x ≠ 0 → x ≠ 1 → False := by
        intro x hx hx_top hx0 hx1
        cases x with
        | top => exact hx_top rfl
        | coe n =>
          simp at hx hx0 hx1
          omega
      exact absurd (this _ hlt h_ne_top h_ne0 h_ne1) (by trivial)
    exact h_ge
  -- Conclude diam = 2 from edist bounds
  -- G.ediam = 2 (as ℕ∞) since all edist ≤ 2 and some edist ≥ 2
  have h_ediam_le : G.ediam ≤ 2 := SimpleGraph.ediam_le_of_edist_le h_edist_le_two
  obtain ⟨u, v, huv⟩ := h_exists_dist_ge_two
  have h_ediam_ge : 2 ≤ G.ediam := by
    exact le_trans huv (SimpleGraph.edist_le_ediam)
  have h_ediam_eq : G.ediam = 2 := le_antisymm h_ediam_le h_ediam_ge
  simp only [CGraph.diameter]
  change G.diam = 2
  rw [SimpleGraph.diam, h_ediam_eq]
  rfl

@[simp] theorem card_completeMultipartite (ds : List ℕ) :
    Fintype.card (completeMultipartite ds).V = ds.sum := by
  simp only [completeMultipartite, card_compl, card_sigmaUnion, card_complete]
  rw [← Fin.sum_ofFn, List.ofFn_get]

@[simp] theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 := by
  simp only [completeMultipartite, indepNum_compl]
  -- Need: (sigmaUnion (fun i : Fin ds.length => complete (ds.get i))).cliqueNum = (ds.max?).getD 0
  induction ds with
  | nil =>
    simp [List.max?]
    -- vertex type of sigmaUnion over Fin 0 is empty
    have : IsEmpty (sigmaUnion (fun i : Fin 0 => complete [][↑i])).V := by
      exact ⟨fun x => Fin.elim0 x.1⟩
    simp only [CGraph.cliqueNum, CGraph.toSimple]
    unfold SimpleGraph.cliqueNum
    have : {n : ℕ | ∃ s : Finset (sigmaUnion (fun i : Fin 0 => complete [][↑i])).V,
        (sigmaUnion (fun i : Fin 0 => complete [][↑i])).toSimple.IsNClique n s} ⊆ {0} := by
      rintro n ⟨s, hs⟩
      have : s = ∅ := by
        by_contra hns
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hns
        exact this.elim (Fin.elim0 (by exact x.1))
      rw [this] at hs
      have : n = 0 := by
        have := SimpleGraph.IsNClique.card_eq hs
        simp at this
        exact this.symm
      exact this
    rw [csSup_eq_of_forall_le_of_forall_lt_exists_gt]
    · exact ⟨0, ∅, by simp⟩
    · intro n hn; have := this hn; simp at this; exact this.le
    · intro w hw; exact ⟨0, by simp, hw⟩
  | cons h tl ih =>
    let Fi : Fin (tl.length + 1) → CGraph := fun i => complete ((h :: tl).get i)
    have hcliqueNum_Fi : ∀ i, (Fi i).cliqueNum = (h :: tl).get i := fun i => cliqueNum_complete _
    -- Helper: adjacent in sigmaUnion implies same fiber
    have hsame_fiber : ∀ x y : (sigmaUnion Fi).V, (sigmaUnion Fi).Adj x y → x.1 = y.1 := by
      intro x y hadj
      by_contra heq
      rw [sigmaUnion_adj_of_fst_ne _ x y heq] at hadj
      simp at hadj
    -- Helper: embedding from Fi i into sigmaUnion Fi
    let embed : ∀ i, (Fi i).V ↪ (sigmaUnion Fi).V := fun i =>
      ⟨fun v => ⟨i, v⟩, fun a b h => by
        exact heq_iff_eq.mp (Sigma.mk.inj_iff.mp h |>.2)⟩
    have hembed_inj : ∀ i, Function.Injective (embed i) := fun i => (embed i).injective
    -- Adjacency within a fiber (all pairs adjacent in Fi = complete)
    have hcomplete_adj : ∀ i (a b : (Fi i).V), a ≠ b → (Fi i).Adj a b := by
      intro i a b hab
      show (complete ((h :: tl).get i)).Adj a b
      show (complete ((h :: tl).get i)).Adj a b
      show (complete ((h :: tl).get i)).Adj a b
      show (CGraph.compl (empty ((h :: tl).get i))).Adj a b
      dsimp [CGraph.compl]
      simp [empty]
      exact hab
    have hfiber_adj : ∀ i (a b : (Fi i).V), a ≠ b → (sigmaUnion Fi).Adj (embed i a) (embed i b) := by
      intro i a b hab
      show (sigmaUnion Fi).Adj ⟨i, a⟩ ⟨i, b⟩ = true
      rw [sigmaUnion_adj_mk]
      exact hcomplete_adj i a b hab
    -- Fiber cardinality via equiv
    let fiberEquiv : ∀ i, (Fi i).V ≃ {v : (sigmaUnion Fi).V // v.1 = i} := fun i =>
      ⟨fun v => ⟨⟨i, v⟩, rfl⟩,
       fun p => (show (Fi p.val.1).V = (Fi i).V from by rw [p.property]) ▸ p.val.2,
       fun _ => rfl,
       fun ⟨⟨j, v⟩, hj⟩ => by subst hj; rfl⟩
    have hfiber_card_equiv : ∀ i, Fintype.card {v : (sigmaUnion Fi).V // v.1 = i} = Fintype.card (Fi i).V :=
      fun i => Fintype.card_congr (fiberEquiv i).symm
    -- Step 1: cliqueNum (sigmaUnion Fi) = Finset.sup Finset.univ (fun i => (Fi i).cliqueNum)
    have hsigma : (sigmaUnion Fi).cliqueNum = Finset.sup Finset.univ (fun i => (Fi i).cliqueNum) := by
      apply le_antisymm
      · -- Upper bound
        unfold CGraph.cliqueNum SimpleGraph.cliqueNum
        apply csSup_le
        · exact ⟨0, ∅, by simp⟩
        · intro n ⟨s, hs⟩
          by_cases hs0 : s = ∅
          · rw [hs0] at hs; have hcard := SimpleGraph.IsNClique.card_eq hs; simp at hcard; rw [← hcard]; exact Nat.zero_le _
          · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hs0
            set i := x.1
            have hall : ∀ y ∈ s, y.1 = i := by
              intro y hy
              by_cases hyx : y = x
              · rw [hyx]
              · have hadj : (sigmaUnion Fi).toSimple.Adj y x := SimpleGraph.IsNClique.isClique hs hy hx hyx
                exact hsame_fiber y x hadj
            have hcard_eq_n : s.card = n := SimpleGraph.IsNClique.card_eq hs
            have hsub : s ⊆ Finset.univ.filter (fun v : (sigmaUnion Fi).V => v.1 = i) := by
              intro v hv; simp [hall v hv]
            have hfilter_card : (Finset.univ.filter (fun v : (sigmaUnion Fi).V => v.1 = i)).card = Fintype.card (Fi i).V := by
              rw [← Fintype.card_subtype, hfiber_card_equiv]
            have hcard_eq_clique : Fintype.card (Fi i).V = (Fi i).cliqueNum := by
              rw [card_complete, hcliqueNum_Fi i]
            rw [hcard_eq_clique] at hfilter_card
            have hcard_le : n ≤ (Fi i).cliqueNum := by
              rw [← hcard_eq_n, ← hfilter_card]
              exact Finset.card_le_card hsub
            exact hcard_le.trans (Finset.le_sup (f := fun i => sSup {n | ∃ s, (Fi i).toSimple.IsNClique n s}) (Finset.mem_univ i))
      · -- Lower bound
        apply Finset.sup_le
        intro i _
        apply le_csSup
        · exact ⟨Fintype.card (sigmaUnion Fi).V, fun m ⟨t, ht⟩ => by
            rw [← ht.card_eq]
            exact Finset.card_le_univ t⟩
        · let s_i := Finset.univ.image (embed i)
          have hc : (Fi i).cliqueNum = Fintype.card (Fi i).V := by
            rw [hcliqueNum_Fi i, card_complete]
          have hs_i_clique : (sigmaUnion Fi).toSimple.IsNClique (Fi i).cliqueNum s_i := by
            rw [hc] at *
            constructor
            · intro a' ha' b' hb' hab'
              simp only [s_i, Finset.coe_image, Set.mem_image] at ha' hb'
              obtain ⟨a, _, rfl⟩ := ha'
              obtain ⟨b, _, rfl⟩ := hb'
              exact hfiber_adj i a b (hembed_inj i |>.ne_iff.mp hab')
            · rw [Finset.card_image_of_injective _ (hembed_inj i)]
              simp
          exact ⟨s_i, hs_i_clique⟩
    -- Step 2: hsup lemma
    have hsup : ∀ (l : List ℕ), Finset.sup Finset.univ (fun i : Fin l.length => l.get i) = l.max?.getD 0 := by
      intro l
      induction l with
      | nil => simp [List.max?]
      | cons a tl ih =>
        simp only [List.length_cons]
        -- Step 1: sup over Fin (n+2) splits as max of f(0) and sup over the rest
        have hsplit : ∀ (f : Fin (tl.length + 1) → ℕ),
            Finset.sup Finset.univ f = max (f 0) (Finset.sup Finset.univ (fun i : Fin tl.length => f i.succ)) := by
          intro f
          have : (Finset.univ : Finset (Fin (tl.length + 1))) =
              {(0 : Fin (tl.length + 1))} ∪ Finset.image Fin.succ (Finset.univ : Finset (Fin tl.length)) := by
            ext i; simp [Finset.mem_univ]
          rw [this, Finset.sup_union, Finset.sup_singleton]
          rw [Finset.sup_image]
          rfl
        -- Step 2: Apply split to (a :: tl).get
        have hget : ∀ (i : Fin tl.length), (a :: tl).get i.succ = tl.get i := by
          intro i; simp
        have hget0 : (a :: tl).get 0 = a := by simp
        rw [hsplit, hget0]
        rw [Finset.sup_congr rfl (fun i _ => hget i)]
        rw [ih]
        -- Step 3: max a (tl.max?.getD 0) = (a :: tl).max?.getD 0
        have foldl_max : ∀ (x : ℕ) (l : List ℕ), ∀ y, max x (List.foldl max y l) = List.foldl max (max x y) l := by
          intro x l
          induction l with
          | nil => simp
          | cons hd tl ih' =>
            intro y
            simp only [List.foldl]
            rw [ih' (max y hd)]
            rw [(max_assoc x y hd).symm]
        simp [List.max?]
        cases tl with
        | nil => simp
        | cons b tl => simp [List.foldl, foldl_max]
    have hsup' := hsup (h :: tl)
    show (sigmaUnion (fun i : Fin (tl.length + 1) => complete ((h :: tl).get i))).cliqueNum = (h :: tl).max?.getD 0
    dsimp only [Fi] at hsigma ⊢
    rw [hsigma, Finset.sup_congr rfl (fun i _ => hcliqueNum_Fi i), hsup']

@[simp] theorem card_star (n : ℕ) : Fintype.card (star n).V = 1 + n := by
  simp [star]

@[simp] theorem E_star (n : ℕ) : (star n).E = n := by
  simp [star, E_bipartite]

/-! ### Products -/

@[simp] theorem E_cartesianProduct [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).E = Fintype.card G.V * H.E + Fintype.card H.V * G.E := by
  dsimp only [CGraph.E]
  -- Step 1: Show that toSimple of cartesianProduct equals SimpleGraph.prodCartesian
  have huv : ∀ p q : G.V × H.V, (cartesianProduct G H).toSimple.Adj p q ↔
      (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2) ∨ (G.toSimple.Adj p.1 q.1 ∧ p.2 = q.2) := by
    intro p q
    simp only [cartesianProduct_adj, CGraph.toSimple_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  -- Handshaking lemma for cartesianProduct
  have hhand_CP : ∑ v : G.V × H.V, (cartesianProduct G H).toSimple.degree v =
      Fintype.card H.V * ∑ g : G.V, G.toSimple.degree g + Fintype.card G.V * ∑ h : H.V, H.toSimple.degree h := by
    have hdeg : ∀ g : G.V, ∀ h : H.V,
        (cartesianProduct G H).toSimple.degree (g, h) = G.toSimple.degree g + H.toSimple.degree h := by
      intro g h
      have hns_finset : (cartesianProduct G H).toSimple.neighborFinset (g, h) =
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
    simp only [hdeg, Fintype.sum_prod_type]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  -- Use handshaking lemma
  have hhand : 2 * (cartesianProduct G H).toSimple.edgeFinset.card =
      ∑ v : G.V × H.V, (cartesianProduct G H).toSimple.degree v :=
    (SimpleGraph.sum_degrees_eq_twice_card_edges (G := (cartesianProduct G H).toSimple)).symm
  have hhand_G : ∑ g : G.V, G.toSimple.degree g = 2 * G.toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G.toSimple
  have hhand_H : ∑ h : H.V, H.toSimple.degree h = 2 * H.toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H.toSimple
  rw [hhand_CP] at hhand
  rw [hhand_G, hhand_H] at hhand
  linarith

@[simp] theorem E_tensorProduct [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).E = 2 * G.E * H.E := by
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
  have hsum_tensor : ∑ p : (tensorProduct G H).V, (tensorProduct G H).toSimple.degree p = 2 * (tensorProduct G H).toSimple.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  -- Rewrite sum over tensorProduct vertices as sum over G.V × H.V
  have hsum_reindex : ∑ p : (tensorProduct G H).V, (tensorProduct G H).toSimple.degree p =
    ∑ p : G.V × H.V, G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
    have : ∀ p : (tensorProduct G H).V, (tensorProduct G H).toSimple.degree p =
      G.toSimple.degree p.1 * H.toSimple.degree p.2 := by
      rintro ⟨g, h⟩
      exact hdeg g h
    rw [Finset.sum_congr rfl (fun p _ => this p)]
    rfl
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

@[simp] theorem indepNum_lexProduct [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).indepNum = G.indepNum * H.indepNum := by
  simp only [CGraph.indepNum]
  unfold SimpleGraph.indepNum
  have hlex : ∀ (p q : G.V × H.V),
      (lexProduct G H).toSimple.Adj p q ↔
        (G.toSimple.Adj p.1 q.1 ∧ p.1 ≠ q.1) ∨ (p.1 = q.1 ∧ H.toSimple.Adj p.2 q.2 ∧ p.2 ≠ q.2) := by
    intro p q
    obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
    simp only [CGraph.toSimple_adj, lexProduct_adj]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ne_eq]
    constructor
    · rintro (h | ⟨hac, hbd⟩)
      · exact Or.inl ⟨h, fun hac => G.loopless c (hac ▸ h)⟩
      · exact Or.inr ⟨hac, hbd, fun hbd' => H.loopless d (hbd' ▸ hbd)⟩
    · rintro (⟨h, -⟩ | ⟨hac, hbd, -⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hac, hbd⟩
  -- Key lemma: independence number of lex product
  -- α(G[H]) = α(G) * α(H)
  -- We prove by showing both ≤ and ≥ directions for sSup
  unfold SimpleGraph.indepNum at *
  -- Let's obtain witnesses for αG and αH
  -- indepNum is sSup of {n | ∃ s, IsNIndepSet n s}
  -- We need:
  -- (1) ∀ S indep in lexProduct, #S ≤ αG * αH  (so sSup ≤ αG * αH)
  -- (2) ∃ S indep in lexProduct with #S = αG * αH (so αG * αH ≤ sSup)
  -- All sets of indep-set sizes are nonempty and bounded above
  set SG := {n : ℕ | ∃ s : Finset G.V, G.toSimple.IsNIndepSet n s}
  set SH := {n : ℕ | ∃ s : Finset H.V, H.toSimple.IsNIndepSet n s}
  set SGH := {n : ℕ | ∃ s : Finset (G.V × H.V), (lexProduct G H).toSimple.IsNIndepSet n s}
  have hSG_ne : SG.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSH_ne : SH.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSGH_ne : SGH.Nonempty := ⟨0, ⟨∅, by intro x; simp, rfl⟩⟩
  have hSG_bdd : BddAbove SG := ⟨Fintype.card G.V, fun n ⟨s, hs⟩ ↦ hs.card_eq.symm ▸ s.card_le_univ⟩
  have hSH_bdd : BddAbove SH := ⟨Fintype.card H.V, fun n ⟨s, hs⟩ ↦ hs.card_eq.symm ▸ s.card_le_univ⟩
  have hSGH_bdd : BddAbove SGH :=
    ⟨Fintype.card G.V * Fintype.card H.V, fun n ⟨s, hs⟩ ↦
      hs.card_eq.symm ▸ le_trans s.card_le_univ (by simp [Fintype.card_prod])⟩
  -- Key: indepNum is attained. Use that {n | ...} is a set of naturals that is nonempty and
  -- bounded above, and for ℕ, sSup is attained when the set is "compact" (finite). 
  -- We use `Nat.exists_max_image` on the finite type `Finset G.V`.
  -- indepNum G = sSup {n | ∃ s, IsNIndepSet n s} = max {|s| : s is indep in G}
  -- So there exists an indep set of size indepNum G.
  -- SG is finite (image of a subset of Finset G.V under card)
  have hSG_finite : SG.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset G.V => s.card) (Finset.univ : Finset (Finset G.V))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  have hSH_finite : SH.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset H.V => s.card) (Finset.univ : Finset (Finset H.V))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  have hSGH_finite : SGH.Finite := by
    exact Set.Finite.subset (Set.toFinite (Finset.image (fun s : Finset (G.V × H.V) => s.card) (Finset.univ : Finset (Finset (G.V × H.V)))))
      (fun n hn => by rcases hn with ⟨s, hs⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.card_eq⟩))
  -- For finite nonempty sets of ℕ, sSup is attained
  have attained_G : ∃ s : Finset G.V, G.toSimple.IsIndepSet (s : Set G.V) ∧ s.card = G.toSimple.indepNum := by
    have hmem : G.toSimple.indepNum ∈ SG := by
      exact Nat.sSup_mem hSG_ne hSG_bdd
    rcases hmem with ⟨s, hs⟩
    exact ⟨s, hs.isIndepSet, hs.card_eq⟩
  have attained_H : ∃ s : Finset H.V, H.toSimple.IsIndepSet (s : Set H.V) ∧ s.card = H.toSimple.indepNum := by
    have hmem : H.toSimple.indepNum ∈ SH := by
      exact Nat.sSup_mem hSH_ne hSH_bdd
    rcases hmem with ⟨s, hs⟩
    exact ⟨s, hs.isIndepSet, hs.card_eq⟩
  -- Lower bound: product of max indep sets is indep in lexProduct
  obtain ⟨sG, hsG_ind, hsG_card⟩ := attained_G
  obtain ⟨sH, hsH_ind, hsH_card⟩ := attained_H
  let sGH := sG ×ˢ sH
  have hprod_indep : (lexProduct G H).toSimple.IsIndepSet (sGH : Set (G.V × H.V)) := by
    intro p hp q hq hadj
    change p ∈ (sG ×ˢ sH : Finset (G.V × H.V)) at hp
    change q ∈ (sG ×ˢ sH : Finset (G.V × H.V)) at hq
    rw [Finset.mem_product] at hp hq
    rcases hp with ⟨hap, hbp⟩; rcases hq with ⟨haq, hbq⟩
    rw [hlex]
    intro h
    rcases h with ⟨hadj1, hne1⟩ | ⟨heq, hadj2, hne2⟩
    · exact absurd hadj1 (hsG_ind hap haq hne1)
    · exact absurd hadj2 (hsH_ind hbp hbq hne2)
  have hprod_card : sGH.card = G.toSimple.indepNum * H.toSimple.indepNum := by
    rw [Finset.card_product, hsG_card, hsH_card]
  have hmem_GH : G.toSimple.indepNum * H.toSimple.indepNum ∈ SGH :=
    ⟨sGH, hprod_indep, hprod_card⟩
  -- sSup ≤ ... : upper bound
  have hupper : ∀ n ∈ SGH, n ≤ G.toSimple.indepNum * H.toSimple.indepNum := by
    intro n ⟨s, hs_ind, hs_card⟩
    rw [← hs_card]
    -- projG is indep in G
    let projG := s.image Prod.fst
    have hprojG_ind : G.toSimple.IsIndepSet (projG : Set G.V) := by
      intro a ha a' ha' hadj haa'
      rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.mp ha' with ⟨q, hq, rfl⟩
      have hpq : p ≠ q := by intro heq; exact hadj (congr_arg Prod.fst heq)
      exfalso; apply hs_ind hp hq hpq; exact (hlex p q).mpr (Or.inl ⟨haa', hadj⟩)
    --projG.card ≤ indepNum G
    have hproj_card_le : projG.card ≤ G.toSimple.indepNum := by
      apply le_csSup hSG_bdd
      exact ⟨projG, ⟨hprojG_ind, rfl⟩⟩
    -- Each fiber has size ≤ indepNum H
    let fiber (a : G.V) : Finset (G.V × H.V) := s.filter (fun x => x.1 = a)
    have hfiber_card : ∀ a, (fiber a).card ≤ H.toSimple.indepNum := by
      intro a
      -- fiber a is in bijection with a subset of H.V that's indep
      let fibersnd : Finset H.V := (fiber a).image Prod.snd
      have hfib_ind : H.toSimple.IsIndepSet (fibersnd : Set H.V) := by
        intro b hb b' hb' hab hadj
        rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hb' with ⟨q, hq, rfl⟩
        simp [fiber, Finset.mem_filter] at hp hq
        have hpq : p ≠ q := by intro heq; exact hab (Prod.ext_iff.mp heq |>.2)
        exact absurd ((hlex p q).mpr (Or.inr ⟨hp.2.trans hq.2.symm, hadj, hab⟩)) (hs_ind hp.1 hq.1 hpq)
      have hfib_card : (fiber a).card = fibersnd.card := by
        rw [Finset.card_image_of_injOn (f := Prod.snd) (fun p hp q hq h => by
          simp [fiber] at hp hq
          exact Prod.ext (hp.2.trans hq.2.symm) h)]
      have hfib_le : fibersnd.card ≤ H.toSimple.indepNum := by
        apply le_csSup hSH_bdd; exact ⟨fibersnd, hfib_ind, rfl⟩
      exact hfib_card.symm ▸ hfib_le
    have hcard_fiberwise : s.card = ∑ a ∈ projG, (fiber a).card := by
      have h_union : s = projG.biUnion fiber := by
        ext ⟨x1, x2⟩
        simp [projG, fiber]
        exact fun h => ⟨x2, h⟩
      rw [h_union, Finset.card_biUnion]
      intro a ha b hb hab
      exact Finset.disjoint_left.mpr (fun x hx hx' => hab (by simp [fiber] at hx hx'; exact hx.2.symm.trans hx'.2))
    calc s.card = ∑ a ∈ projG, (fiber a).card := hcard_fiberwise
      _ ≤ ∑ _ ∈ projG, H.toSimple.indepNum := Finset.sum_le_sum fun a ha => hfiber_card a
      _ = projG.card * H.toSimple.indepNum := by simp
      _ ≤ G.toSimple.indepNum * H.toSimple.indepNum := Nat.mul_le_mul_right _ hproj_card_le
  have hlower : G.toSimple.indepNum * H.toSimple.indepNum ≤ sSup SGH := by
    apply le_csSup hSGH_bdd hmem_GH
  exact le_antisymm (csSup_le hSGH_ne hupper) hlower

@[simp] theorem cliqueNum_strongProduct [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum := by
  unfold CGraph.cliqueNum
  -- cliqueNum G = G.toSimple.cliqueNum = sSup {n | ∃ s, G.toSimple.IsNClique n s}
  set sG := G.toSimple
  set sH := H.toSimple
  set sGH := (G.strongProduct H).toSimple
  -- The adjacency in sGH: for p q : G.V × H.V,
  -- sGH.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ sG.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ sH.Adj p.2 q.2))
  have hasAdj : ∀ p q : G.V × H.V,
    sGH.Adj p q ↔ p ≠ q ∧ ((p.1 = q.1 ∨ sG.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ sH.Adj p.2 q.2)) := by
    intro p q
    simp [sGH, strongProduct_adj, CGraph.toSimple]
    simp [sG, sH]
  -- cliqueNum unfolds to sSup of clique sizes
  -- We prove both directions.
  -- Get witnesses of max cliques in G and H
  have h0G : ∃ s : Finset G.V, sG.IsNClique 0 s := ⟨∅, by simp⟩
  have h0H : ∃ s : Finset H.V, sH.IsNClique 0 s := ⟨∅, by simp⟩
  have hωG_nonempty : {n | ∃ s : Finset G.V, sG.IsNClique n s}.Nonempty := ⟨0, h0G⟩
  have hωG_bdd : BddAbove {n | ∃ s : Finset G.V, sG.IsNClique n s} := by
    exact ⟨Fintype.card G.V, fun n ⟨s, hs⟩ ↦ by rw [← hs.2]; exact Finset.card_le_univ s⟩
  have hωH_nonempty : {n | ∃ s : Finset H.V, sH.IsNClique n s}.Nonempty := ⟨0, h0H⟩
  have hωH_bdd : BddAbove {n | ∃ s : Finset H.V, sH.IsNClique n s} := by
    exact ⟨Fintype.card H.V, fun n ⟨s, hs⟩ ↦ by rw [← hs.2]; exact Finset.card_le_univ s⟩
  -- cliqueNum = sSup of clique sizes (already unfolded)
  -- Helper: clique sizes are ≤ cliqueNum
  have card_le_cliqueNum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      {n : ℕ} {s : Finset V} (hs : G.IsNClique n s) : n ≤ G.cliqueNum := by
    rw [SimpleGraph.cliqueNum]
    exact le_csSup
      ⟨Fintype.card V, fun m ⟨t, ht⟩ ↦ ht.2 ▸ Finset.card_le_univ t⟩
      ⟨s, hs⟩
  -- Upper bound on clique size in strong product
  have upper : ∀ u : Finset (G.V × H.V), sGH.IsNClique u.card u → u.card ≤ sG.cliqueNum * sH.cliqueNum := by
    intro u hu
    -- Let πG be the image of u under first projection
    let projG := Finset.image (fun p : G.V × H.V => p.1) u
    -- For each g, fiber size
    let fiber := fun g => Finset.filter (fun p => p.1 = g) u
    -- Project to H for a fixed g
    let projHfiber := fun g => Finset.image (fun p : G.V × H.V => p.2) (fiber g)
    -- Step 1: projG is a clique in sG
    have projG_clique : sG.IsClique projG := by
      intro g1 hg1 g2 hg2 hne
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hg1
      obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hg2
      have hne2 : p1 ≠ p2 := by intro h; exact hne (by simp [h])
      have hadj := hu.1 hp1 hp2 hne2
      rw [hasAdj] at hadj
      exact hadj.2.1.resolve_left (fun h => hne (h ▸ rfl))
    -- Step 2: Each fiber's image in H is a clique
    have fiber_clique : ∀ g ∈ projG, sH.IsClique (projHfiber g) := by
      intro g hg h1 hh1 h2 hh2 hne
      obtain ⟨p1, hp1, rfl⟩ := Finset.mem_image.mp hh1
      obtain ⟨p2, hp2, rfl⟩ := Finset.mem_image.mp hh2
      have hne2 : p1 ≠ p2 := fun h => hne (by simp [h])
      have hp1uv : p1 ∈ u ∧ p1.1 = g := by simpa [fiber] using hp1
      have hp2uv : p2 ∈ u ∧ p2.1 = g := by simpa [fiber] using hp2
      have hadj := hu.1 hp1uv.1 hp2uv.1 hne2
      rw [hasAdj] at hadj
      have hp1p2 : p1.1 = p2.1 := hp1uv.2 ▸ hp2uv.2.symm
      rw [hp1p2] at hadj
      exact hadj.2.2.resolve_left hne
    -- Step 3: Each fiber has size ≤ sH.cliqueNum
    have fiber_size_bound : ∀ g ∈ projG, (fiber g).card ≤ sH.cliqueNum := by
      intro g hg
      have hclique_H := fiber_clique g hg
      have hcard_eq : (fiber g).card = (projHfiber g).card := by
        dsimp only [projHfiber, fiber]
        exact (Finset.card_image_of_injOn (fun p1 hp1 p2 hp2 h => by
          have h1 : p1.1 = g := (Finset.mem_filter.mp hp1).2
          have h2 : p2.1 = g := (Finset.mem_filter.mp hp2).2
          exact Prod.ext (h1 ▸ h2.symm) h)).symm
      rw [hcard_eq]
      exact card_le_cliqueNum sH ⟨hclique_H, rfl⟩
    -- Step 4: u.card ≤ projG.card * sH.cliqueNum
    have u_card_bound : u.card ≤ projG.card * sH.cliqueNum := by
      have hsum : u.card = ∑ g ∈ projG, (fiber g).card := by
        have h_decomp : ∀ p, p ∈ u ↔ ∃ g ∈ projG, p ∈ fiber g := by
          intro p
          constructor
          · intro hp
            exact ⟨p.1, Finset.mem_image_of_mem _ hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
          · rintro ⟨g, hg, hp⟩
            exact (Finset.mem_filter.mp hp).1
        have h_union : u = projG.biUnion fiber := by ext p; simp [h_decomp, Finset.mem_biUnion]
        rw [h_union]
        apply Finset.card_biUnion
        intro g hg g' hg' hne
        show Disjoint (fiber g) (fiber g')
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hne ((Finset.mem_filter.mp hp1).2 ▸ (Finset.mem_filter.mp hp2).2)
      exact hsum ▸ Finset.sum_le_card_nsmul _ _ _ fiber_size_bound
    -- Step 5: projG.card ≤ sG.cliqueNum
    have projG_card_bound : projG.card ≤ sG.cliqueNum := by
      exact card_le_cliqueNum sG ⟨projG_clique, rfl⟩
    exact le_trans u_card_bound (Nat.mul_le_mul_right _ projG_card_bound)
  -- So cliqueNumGH ≤ cliqueNumG * cliqueNumH
  have upper_sSup : sGH.cliqueNum ≤ sG.cliqueNum * sH.cliqueNum := by
    rw [SimpleGraph.cliqueNum]
    have hωGH_nonempty : {n | ∃ s : Finset (G.V × H.V), sGH.IsNClique n s}.Nonempty := ⟨0, ⟨∅, by simp⟩⟩
    apply csSup_le hωGH_nonempty
    rintro n ⟨s, hs⟩
    obtain ⟨hclique, hcard⟩ := hs
    have hncard : sGH.IsNClique s.card s := ⟨hclique, rfl⟩
    have := upper s hncard
    exact hcard ▸ this
  -- Lower bound: ωG * ωH ≤ ωGH
  -- Build sizes_G and sizes_H finsets of clique sizes
  let cliques_G := Finset.univ.powerset.filter (fun (s : Finset G.V) => sG.IsClique s)
  let sizes_G := cliques_G.image (fun s => s.card)
  have hsizes_G_ne : sizes_G.Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [SimpleGraph.IsClique]⟩, rfl⟩⟩
  let cliques_H := Finset.univ.powerset.filter (fun (s : Finset H.V) => sH.IsClique s)
  let sizes_H := cliques_H.image (fun s => s.card)
  have hsizes_H_ne : sizes_H.Nonempty := ⟨0, Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [SimpleGraph.IsClique]⟩, rfl⟩⟩
  -- cliqueNum = sup' of the sizes finset
  have hset_eq_G : {n | ∃ s : Finset G.V, sG.IsNClique n s} = (sizes_G : Set ℕ) := by
    ext n
    simp [sizes_G, cliques_G]
    exact ⟨fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩, fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩⟩
  have hset_eq_H : {n | ∃ s : Finset H.V, sH.IsNClique n s} = (sizes_H : Set ℕ) := by
    ext n
    simp [sizes_H, cliques_H]
    exact ⟨fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩, fun ⟨s, hclique, hcard⟩ ↦ ⟨s, hclique, hcard⟩⟩
  have hcliqueNum_eq_G : sG.cliqueNum = sizes_G.max' hsizes_G_ne := by
    rw [SimpleGraph.cliqueNum, hset_eq_G]
    have hωG_ne' : ((sizes_G : Set ℕ)).Nonempty := by rw [← hset_eq_G]; exact hωG_nonempty
    have hωG_bd' : BddAbove (sizes_G : Set ℕ) := by rw [← hset_eq_G]; exact hωG_bdd
    have hmem : (sizes_G.max' hsizes_G_ne : ℕ) ∈ (sizes_G : Set ℕ) := Finset.max'_mem sizes_G hsizes_G_ne
    exact le_antisymm
      (csSup_le hωG_ne' (fun n hn => Finset.le_max' _ _ hn))
      (le_csSup hωG_bd' hmem)
  have hcliqueNum_eq_H : sH.cliqueNum = sizes_H.max' hsizes_H_ne := by
    rw [SimpleGraph.cliqueNum, hset_eq_H]
    have hωH_ne' : ((sizes_H : Set ℕ)).Nonempty := by rw [← hset_eq_H]; exact hωH_nonempty
    have hωH_bd' : BddAbove (sizes_H : Set ℕ) := by rw [← hset_eq_H]; exact hωH_bdd
    have hmem : (sizes_H.max' hsizes_H_ne : ℕ) ∈ (sizes_H : Set ℕ) := Finset.max'_mem sizes_H hsizes_H_ne
    exact le_antisymm
      (csSup_le hωH_ne' (fun n hn => Finset.le_max' _ _ hn))
      (le_csSup hωH_bd' hmem)
  -- Get attained max cliques in G and H
  have hsGmax_mem : sizes_G.max' hsizes_G_ne ∈ sizes_G := Finset.max'_mem sizes_G hsizes_G_ne
  have hsHmax_mem : sizes_H.max' hsizes_H_ne ∈ sizes_H := Finset.max'_mem sizes_H hsizes_H_ne
  obtain ⟨sGmax, hsGmax_mem', hsGmax_card⟩ := Finset.mem_image.mp hsGmax_mem
  obtain ⟨sHmax, hsHmax_mem', hsHmax_card⟩ := Finset.mem_image.mp hsHmax_mem
  have hsGmax_clique : sG.IsClique sGmax := (Finset.mem_filter.mp hsGmax_mem').2
  have hsHmax_clique : sH.IsClique sHmax := (Finset.mem_filter.mp hsHmax_mem').2
  -- sGmax is a clique in G, sHmax is a clique in H
  -- Their product is a clique in sGH
  let u := sGmax.product sHmax
  have hu_clique_carrier : sGH.IsClique (↑(sGmax.product sHmax) : Set (G.V × H.V)) := by
    intro p hp q hq hpq
    simp at hp hq
    obtain ⟨hpG, hpH⟩ := hp
    obtain ⟨hqG, hqH⟩ := hq
    rw [hasAdj]
    refine ⟨hpq, ?_, ?_⟩
    · by_cases h1 : p.1 = q.1
      · exact Or.inl h1
      · exact Or.inr (hsGmax_clique hpG hqG h1)
    · by_cases h2 : p.2 = q.2
      · exact Or.inl h2
      · exact Or.inr (hsHmax_clique hpH hqH h2)
  have hu_clique : sGH.IsNClique (sGmax.card * sHmax.card) (sGmax.product sHmax) := by
    exact ⟨hu_clique_carrier, Finset.card_product sGmax sHmax⟩
  have hu_clique' : sGH.IsNClique (sizes_G.max' hsizes_G_ne * sizes_H.max' hsizes_H_ne) (sGmax.product sHmax) := by
    rwa [hsGmax_card, hsHmax_card] at hu_clique
  have hlower : sG.cliqueNum * sH.cliqueNum ≤ sGH.cliqueNum := by
    rw [hcliqueNum_eq_G, hcliqueNum_eq_H]
    exact card_le_cliqueNum sGH hu_clique'
  exact le_antisymm upper_sSup hlower

@[simp] theorem card_hypercube (n : ℕ) : Fintype.card (hypercube n).V = 2 ^ n := by
  simp [hypercube]

/-! ### Kneser, line and Mycielskian -/

@[simp] theorem card_kneser (n k : ℕ) : Fintype.card (kneser n k).V = n.choose k := by
  simp [kneser, Fintype.card_finset_len]

@[simp] theorem card_lineGraph [DecidableEq G.V] : Fintype.card (lineGraph G).V = G.E := by
  rw [E, SimpleGraph.edgeFinset_card]
  exact Fintype.card_congr' rfl

/-- The degree of an edge `e` in `lineGraph G`: each endpoint `v` of `e` contributes the
`G.degree v - 1` other edges incident to `v`, and no edge is counted twice because two
distinct endpoints cannot both lie on a third edge. -/
theorem degree_lineGraph [DecidableEq G.V] (e : (lineGraph G).V) :
    (lineGraph G).toSimple.degree e = ∑ v ∈ e.1.toFinset, (G.toSimple.degree v - 1) := by
  set S := G.toSimple
  have hhadj : ∀ x y : (lineGraph G).V,
      (lineGraph G).toSimple.Adj x y ↔ x ≠ y ∧ ∃ v : G.V, Sym2.Mem v (Subtype.val x) ∧ Sym2.Mem v (Subtype.val y) := by
    intro x y
    simp only [CGraph.toSimple, lineGraph_adj]
    simp [Bool.and_eq_true, decide_eq_true_eq]
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
      have hadj' : e ≠ a ∧ ∃ v, v ∈ ee ∧ v ∈ a.1 := (hhadj e a).mp (by simpa using hadj)
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
    have : (Finset.image (fun f : (lineGraph G).V => f.1) (G.lineGraph.toSimple.neighborFinset e)).card =
        (G.lineGraph.toSimple.neighborFinset e).card := by
      apply Finset.card_image_of_injective _ Subtype.coe_injective
    rw [this]
  rw [hcard_eq]
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
  rw [hdecomp]
  have hEE_inc_sym2 : ∀ v ∈ ee.toFinset, v ∈ ee := by
    intro v hv
    exact Sym2.mem_toFinset.mp hv
  have hEE_inc : ∀ v ∈ ee.toFinset, ee ∈ S.incidenceFinset v := by
    intro v hv
    rw [S.mem_incidenceFinset]
    exact ⟨(heqmem ee).mpr hee_mem, hEE_inc_sym2 v hv⟩
  have hEE_inc_set : ∀ v ∈ ee.toFinset, ee ∈ S.incidenceSet v := by
    intro v hv
    show ee ∈ {e ∈ S.edgeSet | v ∈ e}
    exact ⟨(heqmem ee).mpr hee_mem, hEE_inc_sym2 v hv⟩
  have hpiece : ∀ v ∈ ee.toFinset, (S.incidenceFinset v \ {ee}).card = S.degree v - 1 := by
    intro v hv
    have hsubset : {ee} ⊆ S.incidenceFinset v := Finset.singleton_subset_iff.mpr (hEE_inc v hv)
    have hcard_v : (S.incidenceFinset v).card = S.degree v := by
      rw [SimpleGraph.degree, SimpleGraph.incidenceFinset]; simp
    rw [Finset.card_sdiff_of_subset hsubset, Finset.card_singleton, hcard_v]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl hpiece
  · intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro f hfv hfw
    simp [Finset.mem_sdiff, Finset.mem_singleton] at hfv hfw
    obtain ⟨hfv_inc, hfv_ne⟩ := hfv
    obtain ⟨hfw_inc, hfw_ne⟩ := hfw
    have hfv_inc' : f ∈ S.incidenceFinset v := by
      rw [S.mem_incidenceFinset]; exact ⟨hfv_inc.1, hfv_inc.2⟩
    have hfw_inc' : f ∈ S.incidenceFinset w := by
      rw [S.mem_incidenceFinset]; exact ⟨hfw_inc.1, hfw_inc.2⟩
    simp [SimpleGraph.mem_incidenceFinset] at hfv_inc' hfw_inc'
    have hf_edge' : f ∈ S.edgeSet := hfv_inc.1
    have hee_edge' : ee ∈ S.edgeSet := (heqmem ee).mpr hee_mem
    have hvf_mem : Sym2.Mem v f := hfv_inc.2
    have hwf_mem : Sym2.Mem w f := hfw_inc.2
    have hvf : v ∈ f.toFinset := Sym2.mem_toFinset.mpr hvf_mem
    have hwf : w ∈ f.toFinset := Sym2.mem_toFinset.mpr hwf_mem
    -- Both f and ee have v, w as members (distinct). Since Sym2 elements have exactly 2 members,
    -- every member of f is v or w, and same for ee. Hence f = ee by Sym2 extensionality.
    -- f and ee both contain v and w (v ≠ w) as members. Since they're Sym2 (unordered pairs),
    -- each must equal Sym2.mk (v, w), so they're equal.
    -- We prove this by showing both are equal via Sym2.mk (v, w).
    -- First, we show membership in Sym2.mk (v, w) characterizes when x ∈ f.
    -- Key lemma: for any Sym2 e with v, w ∈ e and v ≠ w, e = Sym2.mk (v, w).
    have hsyeq : ∀ (e : Sym2 G.V), Sym2.Mem v e → Sym2.Mem w e → v ≠ w → e = Sym2.mk (v, w) := by
      intro e hve hwe hvw
      obtain ⟨a, ha⟩ := Sym2.mk_surjective e
      subst ha
      -- For any x, x ∈ Sym2.mk a → x = a.1 ∨ x = a.2 (from cases on Sym2.Mem)
      have hx_mem : ∀ x, Sym2.Mem x (Sym2.mk a) → x = a.1 ∨ x = a.2 := by
        intro x hx'
        show x = a.1 ∨ x = a.2
        simp [Sym2.Mem] at hx'
        rcases hx' with ⟨y, rfl | rfl⟩ <;> simp
      obtain rfl | rfl := hx_mem v hve
      · obtain rfl | rfl := hx_mem w hwe
        · exact absurd rfl hvw
        · rfl
      · obtain rfl | rfl := hx_mem w hwe
        · exact Quot.sound (Sym2.Rel.swap (a.1) (a.2))
        · exact absurd rfl hvw
    exact hfv_ne (hsyeq f hvf_mem hwf_mem hvw ▸ hsyeq ee (Sym2.mem_toFinset.mp hv) (Sym2.mem_toFinset.mp hw) hvw ▸ rfl)

@[simp] theorem E_lineGraph [DecidableEq G.V] :
    (lineGraph G).E = (∑ v : G.V, (G.toSimple.degree v).choose 2) := by
  set S := G.toSimple
  show (lineGraph G).toSimple.edgeFinset.card = ∑ v, (S.degree v).choose 2
  -- Key fact: (lineGraph G).toSimple.Adj x y ↔ x ≠ y ∧ ∃ v, v ∈ ↑x ∧ v ∈ ↑y
  have hhadj : ∀ x y : (lineGraph G).V,
      (lineGraph G).toSimple.Adj x y ↔ x ≠ y ∧ ∃ v : G.V, Sym2.Mem v (Subtype.val x) ∧ Sym2.Mem v (Subtype.val y) := by
    intro x y
    simp only [CGraph.toSimple, lineGraph_adj]
    simp [Bool.and_eq_true, decide_eq_true_eq]
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
    have hcard : (S.incidenceFinset v).card = S.degree v := by
      rw [SimpleGraph.degree, SimpleGraph.incidenceFinset]
      simp
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

@[simp] theorem card_mycielskian [DecidableEq G.V] :
    Fintype.card (mycielskian G).V = 2 * Fintype.card G.V + 1 := by
  simp [mycielskian, Fintype.card_option, Fintype.card_sum, two_mul]

@[simp] theorem E_mycielskian [DecidableEq G.V] :
    (mycielskian G).E = 3 * G.E + Fintype.card G.V := by
  unfold CGraph.E
  let H := (mycielskian G).toSimple
  have hhand_myc := H.sum_degrees_eq_twice_card_edges
  have hhand_G := G.toSimple.sum_degrees_eq_twice_card_edges
  -- Goal: H.edgeFinset.card = 3 * G.toSimple.edgeFinset.card + Fintype.card G.V
  -- From handshaking: 2 * H.edgeFinset.card = ∑ v, H.degree v
  -- and 2 * G.toSimple.edgeFinset.card = ∑ v, G.toSimple.degree v
  -- So it suffices to show ∑ v, H.degree v = 3 * ∑ v, G.toSimple.degree v + 2 * Fintype.card G.V
  -- Helper: describe neighbors of each vertex type in H
  have h_neighborFinset_inl : ∀ a : G.V,
      H.neighborFinset (some (Sum.inl a)) =
        (Finset.image (fun b : G.V => some (Sum.inl b)) (G.toSimple.neighborFinset a) ∪
          Finset.image (fun b : G.V => some (Sum.inr b)) (G.toSimple.neighborFinset a)) := by
    intro a
    ext y
    simp [H, mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  have h_neighborFinset_inr : ∀ a : G.V,
      H.neighborFinset (some (Sum.inr a)) =
        Finset.image (fun b : G.V => some (Sum.inl b)) (G.toSimple.neighborFinset a) ∪ {none} := by
    intro a
    ext y
    simp [H, mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  have h_neighborFinset_none :
      H.neighborFinset none = Finset.image (fun b : G.V => some (Sum.inr b)) Finset.univ := by
    ext y
    simp [H, mycielskian, CGraph.toSimple, SimpleGraph.mem_neighborFinset]
    rcases y with _ | y | y <;> simp
  have target : ∑ v : Option (G.V ⊕ G.V), H.degree v = 3 * ∑ v : G.V, G.toSimple.degree v + 2 * Fintype.card G.V := by
    have hinjl : Function.Injective (fun b : G.V => some (Sum.inl b) : G.V → Option (G.V ⊕ G.V)) :=
      fun x y h => Sum.inl_injective (Option.some_injective (G.V ⊕ G.V) h)
    have hinjr : Function.Injective (fun b : G.V => some (Sum.inr b) : G.V → Option (G.V ⊕ G.V)) :=
      fun x y h => Sum.inr_injective (Option.some_injective (G.V ⊕ G.V) h)
    -- Compute degrees from neighborFinset lemmas
    have hdeg_inl : ∀ a : G.V, H.degree (some (Sum.inl a)) = 2 * G.toSimple.degree a := by
      intro a
      rw [SimpleGraph.degree, h_neighborFinset_inl, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ hinjl, Finset.card_image_of_injective _ hinjr]
        rw [SimpleGraph.degree]
        ring
      · rw [Finset.disjoint_left]; simp [Finset.mem_image]
    have hdeg_inr : ∀ a : G.V, H.degree (some (Sum.inr a)) = G.toSimple.degree a + 1 := by
      intro a
      rw [SimpleGraph.degree, h_neighborFinset_inr, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ hinjl]
        · rfl
      · simp [Finset.disjoint_singleton_right]
    have hdeg_none : H.degree none = Fintype.card G.V := by
      rw [SimpleGraph.degree, h_neighborFinset_none]
      rw [Finset.card_image_of_injective _ hinjr]
      simp
    -- Split the sum over Option
    have hsum_split : ∑ v : Option (G.V ⊕ G.V), H.degree v =
        H.degree none + ∑ x : G.V ⊕ G.V, H.degree (some x) := by
      rw [Fintype.sum_option]
    rw [hsum_split, hdeg_none]
    -- Split the sum over Sum
    have hsum_split2 : ∑ x : G.V ⊕ G.V, H.degree (some x) =
        ∑ a : G.V, H.degree (some (Sum.inl a)) + ∑ a : G.V, H.degree (some (Sum.inr a)) := by
      have h_disj : Disjoint (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ : Finset (G.V ⊕ G.V))
          (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ : Finset (G.V ⊕ G.V)) := by
        rw [Finset.disjoint_left]
        simp
      have h_univ : (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ : Finset (G.V ⊕ G.V)) ∪
          Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ = Finset.univ := by
        ext x; cases x <;> simp
      rw [← h_univ, Finset.sum_union h_disj, Finset.sum_map, Finset.sum_map]
      simp
    rw [hsum_split2]
    simp only [hdeg_inl, hdeg_inr]
    have h1 : ∑ x : G.V, 2 * G.toSimple.degree x = 2 * ∑ x : G.V, G.toSimple.degree x := by
      rw [Finset.mul_sum]
    have h2 : ∑ x : G.V, (G.toSimple.degree x + 1) = ∑ x : G.V, G.toSimple.degree x + Fintype.card G.V := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      simp
    rw [h1, h2]
    ring
  rw [show (∑ v : Option (G.V ⊕ G.V), H.degree v) = 2 * H.edgeFinset.card from hhand_myc] at target
  rw [show (∑ v : G.V, G.toSimple.degree v) = 2 * G.toSimple.edgeFinset.card from hhand_G] at target
  have h2 : 2 * H.edgeFinset.card = 6 * G.toSimple.edgeFinset.card + 2 * Fintype.card G.V := by linarith
  have h3 : H.edgeFinset.card = 3 * G.toSimple.edgeFinset.card + Fintype.card G.V := by omega
  exact h3

/-- The Petersen graph, as `K(5,2)`. -/
theorem card_petersen : Fintype.card (kneser 5 2).V = 10 := by
  rw [card_kneser]; rfl

end Invariants

/-! ## Strongly regular families

`isSRGWith_compl` above already turns one strongly regular graph into another.  Here are three
infinite families proved from scratch, via `isSRGWith_of`: the square rook's graphs, the Kneser
graphs on pairs (`kneser 5 2` is the Petersen graph) and — as the complement of the latter — the
triangular graphs.  `IsoGraph/SRG.lean` reads the concrete entries of its table off these. -/

section SRGFamilies

variable {m n : ℕ}

/-! ### Rook's graphs -/

theorem rook_adj (p q : (rook m n).V) :
    (rook m n).Adj p q
      = ((decide (p.1 = q.1) && decide (p.2 ≠ q.2)) ||
          (decide (p.1 ≠ q.1) && decide (p.2 = q.2))) := by
  simp [rook, cartesianProduct_adj]

theorem mem_nbrs_rook (p q : (rook m n).V) :
    q ∈ (rook m n).nbrs p ↔ (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.1 ≠ q.1 ∧ p.2 = q.2) := by
  rw [mem_nbrs, rook_adj]
  simp

/-- The neighbours of a square are the rest of its row together with the rest of its column. -/
theorem nbrs_rook (p : (rook m n).V) :
    (rook m n).nbrs p
      = (({p.1} : Finset (complete m).V) ×ˢ ({p.2} : Finset (complete n).V)ᶜ) ∪
          (({p.1} : Finset (complete m).V)ᶜ ×ˢ ({p.2} : Finset (complete n).V)) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun q ↦ ?_
  obtain ⟨x, y⟩ := q
  rw [mem_nbrs_rook p (x, y)]
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_compl, Finset.mem_singleton]
  tauto

theorem card_nbrs_rook (p : (rook m n).V) :
    ((rook m n).nbrs p).card = (n - 1) + (m - 1) := by
  rw [nbrs_rook, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product]
  · simp [Finset.card_compl]
  · rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton] at h1 h2
    exact h2.1 h1.1

/-- Neighbours common to two squares in the same row: the rest of that row. -/
theorem nbrs_inter_rook_row (a : (complete m).V) (b d : (complete n).V) (h : b ≠ d) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (a, d)
      = ({a} : Finset (complete m).V) ×ˢ ({b, d} : Finset (complete n).V)ᶜ := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (a, d) (x, y)]
  simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert,
    not_or]
  grind

/-- Neighbours common to two squares in the same column: the rest of that column. -/
theorem nbrs_inter_rook_col (a c : (complete m).V) (b : (complete n).V) (h : a ≠ c) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, b)
      = ({a, c} : Finset (complete m).V)ᶜ ×ˢ ({b} : Finset (complete n).V) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (c, b) (x, y)]
  simp only [Finset.mem_product, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert,
    not_or]
  grind

/-- Neighbours common to two squares in different rows *and* different columns: the two remaining
corners of the rectangle they span. -/
theorem nbrs_inter_rook_diag (a c : (complete m).V) (b d : (complete n).V) (h1 : a ≠ c)
    (h2 : b ≠ d) :
    (rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, d)
      = ({(a, d), (c, b)} : Finset ((complete m).V × (complete n).V)) := by
  refine Finset.ext (α := (complete m).V × (complete n).V) fun r ↦ ?_
  obtain ⟨x, y⟩ := r
  rw [Finset.mem_inter, mem_nbrs_rook (a, b) (x, y), mem_nbrs_rook (c, d) (x, y)]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  grind

theorem card_nbrs_inter_rook_row (a : (complete m).V) (b d : (complete n).V) (h : b ≠ d) :
    ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (a, d)).card = n - 2 := by
  rw [nbrs_inter_rook_row a b d h, Finset.card_product, Finset.card_compl,
    Finset.card_singleton, Finset.card_pair h, card_complete, one_mul]

theorem card_nbrs_inter_rook_col (a c : (complete m).V) (b : (complete n).V) (h : a ≠ c) :
    ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, b)).card = m - 2 := by
  rw [nbrs_inter_rook_col a c b h, Finset.card_product, Finset.card_compl,
    Finset.card_singleton, Finset.card_pair h, card_complete, mul_one]

theorem card_nbrs_inter_rook_diag (a c : (complete m).V) (b d : (complete n).V) (h1 : a ≠ c)
    (h2 : b ≠ d) : ((rook m n).nbrs (a, b) ∩ (rook m n).nbrs (c, d)).card = 2 := by
  rw [nbrs_inter_rook_diag a c b d h1 h2, Finset.card_pair fun hc ↦ h1 (congrArg Prod.fst hc)]

/-- **The `k × k` rook's graph is strongly regular**, with parameters `(k², 2(k-1), k-2, 2)`.

Only the *square* rook's graphs qualify: in `rook m n` two squares in a row have `n - 2` common
neighbours and two in a column have `m - 2`, so `ℓ` is well defined exactly when `m = n`. -/
theorem isSRGWith_rook (k : ℕ) : (rook k k).IsSRGWith (k * k) (2 * (k - 1)) (k - 2) 2 := by
  refine isSRGWith_of _ ?_ ?_ ?_ ?_
  · show Fintype.card ((complete k).V × (complete k).V) = k * k
    rw [Fintype.card_prod, card_complete]
  · rintro ⟨a, b⟩
    rw [card_nbrs_rook]
    omega
  · rintro ⟨a, b⟩ ⟨c, d⟩ hadj
    rw [rook_adj] at hadj
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hadj
    obtain ⟨rfl, h⟩ | ⟨h, rfl⟩ := hadj
    · exact card_nbrs_inter_rook_row a b d h
    · exact card_nbrs_inter_rook_col a c b h
  · rintro ⟨a, b⟩ ⟨c, d⟩ hne hadj
    rw [rook_adj] at hadj
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      not_not] at hadj
    refine card_nbrs_inter_rook_diag a c b d ?_ ?_ <;> grind [Prod.ext_iff]

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

/-- For `k ≥ 1` the neighbours of `s` in `kneser n k` are exactly the vertices disjoint from `s`:
the `s ≠ t` conjunct in the definition is redundant, since a nonempty set meets itself. -/
theorem nbrs_kneser {k : ℕ} (hk : 1 ≤ k) (s : (kneser n k).V) :
    (kneser n k).nbrs s
      = Finset.univ.filter fun u : {u : Finset (Fin n) // u.card = k} ↦ u.1 ∩ s.1 = ∅ := by
  refine Finset.ext (α := {u : Finset (Fin n) // u.card = k}) fun u ↦ ?_
  rw [mem_nbrs]
  simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Finset.inter_comm]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun hst ↦ ?_, h⟩⟩
  rw [← hst, Finset.inter_self] at h
  have hs := s.2
  rw [h, Finset.card_empty] at hs
  omega

/-- **Kneser graphs are regular of degree `(n - k).choose k`.** -/
theorem card_nbrs_kneser {k : ℕ} (hk : 1 ≤ k) (s : (kneser n k).V) :
    ((kneser n k).nbrs s).card = (n - k).choose k := by
  rw [nbrs_kneser hk, card_filter_kneser_disjoint, s.2]

theorem nbrs_inter_kneser {k : ℕ} (hk : 1 ≤ k) (s t : (kneser n k).V) :
    (kneser n k).nbrs s ∩ (kneser n k).nbrs t
      = Finset.univ.filter fun u : {u : Finset (Fin n) // u.card = k} ↦
          u.1 ∩ (s.1 ∪ t.1) = ∅ := by
  rw [nbrs_kneser hk, nbrs_kneser hk]
  refine Finset.ext (α := {u : Finset (Fin n) // u.card = k}) fun u ↦ ?_
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.inter_union_distrib_left, Finset.union_eq_empty]

/-- Two `k`-sets meeting in `i` points have `(n - (2k - i)).choose k` common neighbours: the
`k`-sets avoiding their union.  In particular adjacent — i.e. disjoint — vertices have
`(n - 2k).choose k`. -/
theorem card_nbrs_inter_kneser {k : ℕ} (hk : 1 ≤ k) (s t : (kneser n k).V) :
    ((kneser n k).nbrs s ∩ (kneser n k).nbrs t).card
      = (n - (2 * k - (s.1 ∩ t.1).card)).choose k := by
  rw [nbrs_inter_kneser hk, card_filter_kneser_disjoint]
  congr 2
  have := Finset.card_union_add_card_inter s.1 t.1
  rw [s.2, t.2] at this
  omega

/-- Two distinct `2`-subsets that are not disjoint meet in exactly one point. -/
theorem card_inter_eq_one_of_ne (s t : (kneser n 2).V) (hne : s ≠ t) (hd : s.1 ∩ t.1 ≠ ∅) :
    (s.1 ∩ t.1).card = 1 := by
  have hle : (s.1 ∩ t.1).card ≤ 2 := by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := s.1) (s₂ := t.1))
    rwa [s.2] at this
  have hpos : 0 < (s.1 ∩ t.1).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hd)
  rcases Nat.lt_or_ge (s.1 ∩ t.1).card 2 with h | h
  · omega
  · refine absurd (Subtype.ext ?_) hne
    have h1 : s.1 ∩ t.1 = s.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [s.2]; exact h)
    have h2 : s.1 ∩ t.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [t.2]; exact h)
    rw [← h1, h2]

/-- **Kneser graphs on pairs are strongly regular**, with parameters
`(C(n,2), C(n-2,2), C(n-4,2), C(n-3,2))`.  For `n = 5` this is the Petersen graph, `(10,3,0,1)`.
-/
theorem isSRGWith_kneser_two (n : ℕ) :
    (kneser n 2).IsSRGWith (n.choose 2) ((n - 2).choose 2) ((n - 4).choose 2)
      ((n - 3).choose 2) := by
  refine isSRGWith_of _ (card_kneser n 2) (fun s ↦ card_nbrs_kneser one_le_two s) ?_ ?_
  · intro s t hadj
    simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq] at hadj
    rw [card_nbrs_inter_kneser one_le_two, hadj.2, Finset.card_empty]
    norm_num
  · intro s t hne hadj
    simp only [kneser_adj, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not] at hadj
    rw [card_nbrs_inter_kneser one_le_two,
      card_inter_eq_one_of_ne s t hne (hadj.resolve_left (by simpa using hne))]
    norm_num

/-! ### Triangular graphs -/

/-- `johnson n 2` — the triangular graph `T(n)` — is the complement of `kneser n 2`: two distinct
pairs either meet in a point or are disjoint, and never both. -/
def johnsonTwoIso (n : ℕ) : johnson n 2 ≃cg compl (kneser n 2) :=
  ⟨Equiv.refl {s : Finset (Fin n) // s.card = 2}, by
    intro s t
    show (compl (kneser n 2)).Adj s t = true ↔ (johnson n 2).Adj s t = true
    simp only [compl_adj, kneser_adj, johnson_adj, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, not_not, beq_iff_eq,
      ne_eq]
    constructor
    · rintro ⟨hne, hd⟩
      exact ⟨hne, card_inter_eq_one_of_ne s t hne (hd.resolve_left (by simpa using hne))⟩
    · rintro ⟨hne, hc⟩
      refine ⟨hne, Or.inr fun he ↦ ?_⟩
      rw [he, Finset.card_empty] at hc
      exact absurd hc (by norm_num)⟩

theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- **Triangular graphs are strongly regular**: `T(n) = J(n, 2)` has parameters
`(C(n,2), 2(n-2), n-2, 4)`.

The bound `4 ≤ n` is only needed for `μ`, which is vacuous below it: `T(3) = K₃` and
`T(n)` is empty for `n < 3`, so those graphs have no non-adjacent pair to constrain. -/
theorem isSRGWith_johnson_two (n : ℕ) (hn : 4 ≤ n) :
    (johnson n 2).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 from rfl]
  have h := isSRGWith_compl _ (isSRGWith_kneser_two (m + 4))
  rw [show m + 4 - 2 = m + 2 from rfl, show m + 4 - 3 = m + 1 from rfl,
    show m + 4 - 4 = m from rfl] at h
  have h1 : (m + 1).choose 2 = m.choose 2 + m := choose_two_succ m
  have h2 : (m + 2).choose 2 = (m + 1).choose 2 + (m + 1) := choose_two_succ (m + 1)
  have h3 : (m + 3).choose 2 = (m + 2).choose 2 + (m + 2) := choose_two_succ (m + 2)
  have h4 : (m + 4).choose 2 = (m + 3).choose 2 + (m + 3) := choose_two_succ (m + 3)
  rw [show (m + 4).choose 2 - (m + 2).choose 2 - 1 = 2 * (m + 2) from by omega,
    show (m + 4).choose 2 - (2 * (m + 2).choose 2 - (m + 1).choose 2) - 2 = m + 2 from by omega,
    show (m + 4).choose 2 - (2 * (m + 2).choose 2 - m.choose 2) = 4 from by omega] at h
  exact SimpleGraph.Iso.isSRGWith_of_iso (CGraph.Iso.toSimpleIso (johnsonTwoIso (m + 4)).symm) h

@[inherit_doc isSRGWith_johnson_two]
theorem isSRGWith_triangular (n : ℕ) (hn : 4 ≤ n) :
    (triangular n).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4 :=
  isSRGWith_johnson_two n hn

/-! ### Complete bipartite graphs -/

theorem nbrs_bipartite_inl (m n : ℕ) (a : (complete m).V) :
    (bipartite m n).nbrs (Sum.inl a) = Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  refine Finset.ext (α := (complete m).V ⊕ (complete n).V) fun x ↦ ?_
  cases x with
  | inl b => rw [mem_nbrs]; simp
  | inr b => rw [mem_nbrs]; simp

theorem nbrs_bipartite_inr (m n : ℕ) (b : (complete n).V) :
    (bipartite m n).nbrs (Sum.inr b) = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  refine Finset.ext (α := (complete m).V ⊕ (complete n).V) fun x ↦ ?_
  cases x with
  | inl c => rw [mem_nbrs]; simp
  | inr d => rw [mem_nbrs]; simp

/-- **The complete bipartite graph `K_{n,n}` is strongly regular** with parameters
`(2n, n, 0, n)`.

`bipartite m n` is the complement of `Kₘ ⊔ Kₙ`, so this could go through `isSRGWith_compl`, but
the counts are more direct read off the graph itself: a vertex on one side sees all of the other
side, two vertices on the same side see all of the other side in common, and two adjacent
vertices see nothing in common.  Doing it directly also avoids the `2 ≤ n` side condition that
the truncated subtraction in `isSRGWith_compl`'s parameters would force. -/
theorem isSRGWith_bipartite (n : ℕ) : (bipartite n n).IsSRGWith (2 * n) n 0 n := by
  have hnbrs : ∀ x : (complete n).V ⊕ (complete n).V, ((bipartite n n).nbrs x).card = n := by
    rintro (a | b)
    · rw [nbrs_bipartite_inl]; simp
    · rw [nbrs_bipartite_inr]; simp
  refine isSRGWith_of _ ?_ hnbrs (fun (x y : (complete n).V ⊕ (complete n).V) hadj ↦ ?_)
    (fun (x y : (complete n).V ⊕ (complete n).V) hne _ ↦ ?_)
  · show Fintype.card ((complete n).V ⊕ (complete n).V) = 2 * n
    simp [two_mul]
  · -- adjacent: one vertex on each side, and the two neighbourhoods are the two sides
    rcases x with a | b <;> rcases y with c | d <;> simp_all [nbrs_bipartite_inl,
      nbrs_bipartite_inr, Finset.eq_empty_iff_forall_notMem]
  · -- non-adjacent and distinct: both on the same side, with the same neighbourhood
    rcases x with a | b <;> rcases y with c | d <;>
      simp_all [nbrs_bipartite_inl, nbrs_bipartite_inr]

/-! ### Complete multipartite graphs

`completeMultipartite ds` is the complement of a disjoint union of complete graphs, so two
vertices are adjacent exactly when they lie in different parts.  Once that is said, every count
the strong-regularity definition asks for is a sum of part sizes over a complement, and for equal
parts those sums are products. -/

/-- Two vertices of a complete multipartite graph are adjacent exactly when they lie in different
parts. -/
theorem completeMultipartite_adj (ds : List ℕ)
    (x y : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).Adj x y = decide (x.1 ≠ y.1) := by
  show (compl (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))).Adj x y = _
  rw [compl_adj]
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  by_cases h : i = j
  · subst h
    rw [sigmaUnion_adj_mk, complete_adj]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  · rw [sigmaUnion_adj_ne _ _ _ _ _ h]
    have hne : (⟨i, a⟩ : Σ i : Fin ds.length, (complete (ds.get i)).V) ≠ ⟨j, b⟩ :=
      fun hh ↦ h (congrArg Sigma.fst hh)
    simp [hne, h]


/-- The neighbourhood of `x` is everything outside `x`'s own part. -/
theorem nbrs_completeMultipartite (ds : List ℕ)
    (x : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).nbrs x
      = Finset.univ.filter (fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦
          z.1 ∉ ({x.1} : Finset (Fin ds.length))) := by
  refine Finset.ext (α := Σ i : Fin ds.length, (complete (ds.get i)).V) fun z ↦ ?_
  rw [mem_nbrs, completeMultipartite_adj]
  simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ne_comm

/-- Two vertices see in common everything outside both of their parts. -/
theorem nbrs_inter_completeMultipartite (ds : List ℕ)
    (x y : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).nbrs x ∩ (completeMultipartite ds).nbrs y
      = Finset.univ.filter (fun z : Σ i : Fin ds.length, (complete (ds.get i)).V ↦
          z.1 ∉ ({x.1, y.1} : Finset (Fin ds.length))) := by
  rw [nbrs_completeMultipartite, nbrs_completeMultipartite]
  refine Finset.ext (α := Σ i : Fin ds.length, (complete (ds.get i)).V) fun z ↦ ?_
  simp

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

/-- With all parts of size `a`, the sums of `card_filter_fst_notMem` are products.  The length is
left as `(List.replicate n a).length` rather than `n` so that the statement does not have to
transport `S` along `List.length_replicate`. -/
theorem sum_compl_replicate (n a : ℕ) (S : Finset (Fin (List.replicate n a).length)) :
    ∑ j ∈ Sᶜ, (List.replicate n a).get j = ((List.replicate n a).length - S.card) * a := by
  have h : ∀ j ∈ Sᶜ, (List.replicate n a).get j = a := fun j _ ↦ by simp
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, Finset.card_compl, Fintype.card_fin]

/-- **The complete multipartite graph with `n` parts of size `a` is strongly regular** with
parameters `(na, (n-1)a, (n-2)a, (n-1)a)`.

A vertex misses only its own part; two vertices in different parts miss both of theirs; two
distinct vertices in the same part have the same neighbourhood.  The truncated subtractions are
correct in the degenerate cases too: for `n ≤ 1` there are no edges and `(n-1)a = 0`, and for
`n = 2` no two adjacent vertices have a common neighbour and `(n-2)a = 0`. -/
theorem isSRGWith_completeMultipartite_replicate (n a : ℕ) :
    (completeMultipartite (List.replicate n a)).IsSRGWith (n * a) ((n - 1) * a) ((n - 2) * a)
      ((n - 1) * a) := by
  refine isSRGWith_of _ ?_
    (fun (x : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) ↦ ?_)
    (fun (x y : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) hadj ↦ ?_)
    (fun (x y : Σ i : Fin (List.replicate n a).length,
      (complete ((List.replicate n a).get i)).V) hne hadj ↦ ?_)
  · rw [card_completeMultipartite, List.sum_replicate, smul_eq_mul]
  · rw [nbrs_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate,
      Finset.card_singleton]
    simp
  · rw [nbrs_inter_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate]
    rw [completeMultipartite_adj] at hadj
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hadj
    rw [Finset.card_insert_of_notMem (by simpa using hadj), Finset.card_singleton]
    simp
  · rw [nbrs_inter_completeMultipartite, card_filter_fst_notMem, sum_compl_replicate]
    rw [completeMultipartite_adj] at hadj
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq] at hadj
    rw [hadj, Finset.pair_eq_singleton, Finset.card_singleton]
    simp

/-- **The cocktail party graph `K_{n×2}` is strongly regular** with parameters
`(2n, 2n-2, 2n-4, 2n-2)`: it is `n` parts of size two. -/
theorem isSRGWith_cocktailParty (n : ℕ) :
    (cocktailParty n).IsSRGWith (2 * n) (2 * n - 2) (2 * n - 4) (2 * n - 2) := by
  have h := isSRGWith_completeMultipartite_replicate n 2
  rwa [show n * 2 = 2 * n from by ring, show (n - 1) * 2 = 2 * n - 2 from by omega,
    show (n - 2) * 2 = 2 * n - 4 from by omega] at h

/-! ### Paley graphs

`paley q` is a Cayley graph on `ZMod q` with the nonzero squares as connection set, so the whole
question is a character sum.  Write `χ = quadraticChar F` for the quadratic character of a finite
field `F` with `q ≡ 1 mod 4` elements; then `χ (-1) = 1`, so `χ (y - x) = 1` is a symmetric
relation and

* `#{u | χ u = 1} = (q - 1) / 2`, from `∑ u, χ u = 0`;
* `#{u | χ u = 1 ∧ χ (u - a) = 1} = (q - 3 - 2 * χ a) / 4` for `a ≠ 0`, from the same plus
  `∑ u, χ (u * (u - a)) = -1`.

Translating by `x` turns those two counts into the degree and the common-neighbour count, which
is exactly `isSRGWith_of`.  The last step, `paleyIso`, identifies `paley q` — which is written on
`Fin q` and reads its adjacency out of `qrTable` — with the field version over `ZMod q`. -/

section Paley

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For `a ≠ 0`, the quadratic character sum `∑ u, χ (u * (u - a))` is `-1`.

`u ↦ 1 - a * u⁻¹` is a bijection from the nonzero elements to the elements other than `1`, and
`χ (u * (u - a)) = χ (u²) * χ (1 - a * u⁻¹) = χ (1 - a * u⁻¹)`, so the sum is `∑_{w ≠ 1} χ w`. -/
theorem quadraticChar_sum_mul_sub (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ u : F, quadraticChar F (u * (u - a)) = -1 := by
  have h0 : ∑ u : F, quadraticChar F (u * (u - a))
      = ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (u * (u - a)) := by
    rw [Finset.sum_erase]
    simp
  have key : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (u * (u - a))
      = ∑ w ∈ Finset.univ.erase (1 : F), quadraticChar F w := by
    refine Finset.sum_nbij' (i := fun u ↦ 1 - a * u⁻¹) (j := fun w ↦ a * (1 - w)⁻¹)
      ?_ ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu ⊢
      intro h
      rcases mul_eq_zero.mp (sub_eq_self.mp h) with h3 | h3
      · exact ha h3
      · exact hu (inv_eq_zero.mp h3)
    · intro w hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw ⊢
      exact mul_ne_zero ha (inv_ne_zero (sub_ne_zero.2 (Ne.symm hw)))
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
      show a * (1 - (1 - a * u⁻¹))⁻¹ = u
      rw [sub_sub_cancel, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · intro w hw
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
      have h1 : (1 : F) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
      show 1 - a * (a * (1 - w)⁻¹)⁻¹ = w
      rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_sub_cancel]
    · intro u hu
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
      have : u * (u - a) = u ^ 2 * (1 - a * u⁻¹) := by field_simp
      rw [this, map_mul, quadraticChar_sq_one' hu, one_mul]
  rw [h0, key, Finset.sum_erase_eq_sub (Finset.mem_univ _), quadraticChar_sum_zero hF]
  simp

variable (hq : Fintype.card F % 4 = 1)
include hq

omit [DecidableEq F] in
theorem ringChar_ne_two_of_card_mod_four : ringChar F ≠ 2 := fun h ↦ by
  have := FiniteField.even_card_iff_char_two.1 h
  omega

theorem quadraticChar_neg_one_eq_one : quadraticChar F (-1) = 1 :=
  (quadraticChar_one_iff_isSquare (by simp)).2 (FiniteField.isSquare_neg_one_iff.2 (by omega))

/-- Over a field with `q ≡ 1 mod 4` elements the quadratic character is even, which is why the
Paley graph is a graph and not a tournament. -/
theorem quadraticChar_neg' (a : F) : quadraticChar F (-a) = quadraticChar F a := by
  rw [show -a = -1 * a by ring, map_mul, quadraticChar_neg_one_eq_one hq, one_mul]

omit hq in
theorem quadraticChar_sum_sub_zero (hF : ringChar F ≠ 2) (a : F) :
    ∑ u : F, quadraticChar F (u - a) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun u ↦ quadraticChar F (u - a))
    (fun w ↦ quadraticChar F w) (fun u ↦ rfl)]
  exact quadraticChar_sum_zero hF

/-- **The degree count**: exactly half of the nonzero elements are squares. -/
theorem card_quadraticChar_eq_one :
    2 * ((Finset.univ.filter fun u : F ↦ quadraticChar F u = 1).card : ℤ)
      = Fintype.card F - 1 := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have hsplit : ∑ u ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F u)
      = 2 * (((Finset.univ.erase (0 : F)).filter fun u ↦ quadraticChar F u = 1).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (0 : F))
      (fun u ↦ quadraticChar F u = 1)]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (2 : ℤ)) fun u hu ↦ by
        simp only [Finset.mem_filter] at hu; rw [hu.2]; norm_num,
      Finset.sum_eq_zero
        (s := (Finset.univ.erase (0 : F)).filter fun u ↦ ¬ quadraticChar F u = 1) fun u hu ↦ by
          simp only [Finset.mem_filter, Finset.mem_erase] at hu
          rcases quadraticChar_dichotomy hu.1.1 with h | h
          · exact absurd h hu.2
          · rw [h]; ring]
    simp [mul_comm]
  have hfe : ((Finset.univ.erase (0 : F)).filter fun u ↦ quadraticChar F u = 1)
      = Finset.univ.filter fun u : F ↦ quadraticChar F u = 1 := by
    refine Finset.ext fun u ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun h0 ↦ by rw [h0] at h; simp at h, h⟩⟩
  rw [hfe] at hsplit
  rw [← hsplit, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_erase_eq_sub (Finset.mem_univ _), quadraticChar_sum_zero hF,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
  have h2 : 1 ≤ Fintype.card F := Fintype.card_pos
  simp only [nsmul_eq_mul, mul_one, quadraticChar_zero, sub_zero]
  omega

/-- **The common-neighbour count**: for `a ≠ 0` the number of `u` with both `u` and `u - a`
nonzero squares is `(q - 3 - 2 * χ a) / 4`. -/
theorem card_common_quadraticChar {a : F} (ha : a ≠ 0) :
    4 * ((Finset.univ.filter fun u : F ↦
          quadraticChar F u = 1 ∧ quadraticChar F (u - a) = 1).card : ℤ)
      = Fintype.card F - 3 - 2 * quadraticChar F a := by
  have hF := ringChar_ne_two_of_card_mod_four hq
  have ha' : a ∈ Finset.univ.erase (0 : F) := Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩
  set S : Finset F := (Finset.univ.erase (0 : F)).erase a with hS
  set P : F → Prop := fun u ↦ quadraticChar F u = 1 ∧ quadraticChar F (u - a) = 1 with hP
  have hfe : S.filter P = Finset.univ.filter P := by
    refine Finset.ext fun u ↦ ?_
    simp only [hS, hP, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩, h⟩⟩
    · rw [h0, sub_self] at h; simp at h
    · rw [h0] at h; simp at h
  have hsplit : ∑ u ∈ S, (1 + quadraticChar F u) * (1 + quadraticChar F (u - a))
      = 4 * ((S.filter P).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S P]
    rw [Finset.sum_congr rfl (g := fun _ ↦ (4 : ℤ)) fun u hu ↦ by
        simp only [Finset.mem_filter, hP] at hu; rw [hu.2.1, hu.2.2]; norm_num,
      Finset.sum_eq_zero (s := S.filter fun u ↦ ¬ P u) fun u hu ↦ by
        simp only [Finset.mem_filter, hS, Finset.mem_erase, hP, not_and] at hu
        rcases quadraticChar_dichotomy hu.1.2.1 with h | h
        · rcases quadraticChar_dichotomy (sub_ne_zero.2 hu.1.1) with h' | h'
          · exact absurd h' (hu.2 h)
          · rw [h']; ring
        · rw [h]; ring]
    simp [mul_comm]
  have hexp : ∑ u ∈ S, (1 + quadraticChar F u) * (1 + quadraticChar F (u - a))
      = (∑ _u ∈ S, (1 : ℤ)) + (∑ u ∈ S, quadraticChar F u)
        + (∑ u ∈ S, quadraticChar F (u - a)) + ∑ u ∈ S, quadraticChar F (u * (u - a)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [map_mul]
    ring
  have e1 : (∑ _u ∈ S, (1 : ℤ)) = (Fintype.card F : ℤ) - 2 := by
    rw [Finset.sum_const, hS, Finset.card_erase_of_mem ha',
      Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    simp only [nsmul_eq_mul, mul_one]
    omega
  have e2 : (∑ u ∈ S, quadraticChar F u) = -quadraticChar F a := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_zero hF]
    simp
  have e3 : (∑ u ∈ S, quadraticChar F (u - a)) = -quadraticChar F a := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_sub_zero hF]
    simp [quadraticChar_neg' hq]
  have e4 : (∑ u ∈ S, quadraticChar F (u * (u - a))) = -1 := by
    rw [hS, Finset.sum_erase_eq_sub ha', Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)),
      quadraticChar_sum_mul_sub hF ha]
    simp
  rw [← hfe, ← hsplit, hexp, e1, e2, e3, e4]
  ring

end Paley

/-! ### The Paley graph of a finite field -/

/-- The **Paley graph** of a finite field: `x ~ y` when `y - x` is a nonzero square.  For
`Fintype.card F % 4 = 1` this is `paley (Fintype.card F)` up to isomorphism; see `paleyIso`. -/
def paleyField (F : Type) [Field F] [Fintype F] [DecidableEq F] : CGraph :=
  cayleyAdd F fun z ↦ decide (quadraticChar F z = 1)

section PaleyField

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

instance : DecidableEq (paleyField F).V := inferInstanceAs (DecidableEq F)

@[simp] theorem card_paleyField : Fintype.card (paleyField F).V = Fintype.card F := rfl

theorem paleyField_adj (hq : Fintype.card F % 4 = 1) (x y : F) :
    (paleyField F).Adj x y = decide (quadraticChar F (y - x) = 1) := by
  show (cayleyAdd F fun z ↦ decide (quadraticChar F z = 1)).Adj x y = _
  rw [cayleyAdd_adj, show x - y = -(y - x) by ring, quadraticChar_neg' hq]
  by_cases h : x = y
  · subst h
    simp
  · simp [h]

theorem nbrs_paleyField (hq : Fintype.card F % 4 = 1) (x : F) :
    (paleyField F).nbrs x = Finset.univ.filter fun y : F ↦ quadraticChar F (y - x) = 1 := by
  refine Finset.ext (α := F) fun y ↦ ?_
  rw [mem_nbrs, paleyField_adj hq]
  simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]

theorem nbrs_inter_paleyField (hq : Fintype.card F % 4 = 1) (x y : F) :
    (paleyField F).nbrs x ∩ (paleyField F).nbrs y
      = Finset.univ.filter fun z : F ↦
          quadraticChar F (z - x) = 1 ∧ quadraticChar F (z - y) = 1 := by
  refine Finset.ext (α := F) fun z ↦ ?_
  rw [Finset.mem_inter, mem_nbrs, mem_nbrs, paleyField_adj hq, paleyField_adj hq]
  simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Translation by `x` matches the neighbours of `x` with the nonzero squares. -/
theorem card_nbrs_paleyField (hq : Fintype.card F % 4 = 1) (x : F) :
    ((paleyField F).nbrs x).card = (Fintype.card F - 1) / 2 := by
  have hb : (Finset.univ.filter fun y : F ↦ quadraticChar F (y - x) = 1).card
      = (Finset.univ.filter fun u : F ↦ quadraticChar F u = 1).card := by
    refine Finset.card_bij (fun y _ ↦ y - x) ?_ (fun a _ b _ h ↦ sub_left_inj.mp h) ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact ⟨u + x, by simpa using hu, by ring⟩
  have := card_quadraticChar_eq_one hq
  rw [nbrs_paleyField hq, hb]
  omega

theorem card_nbrs_inter_paleyField (hq : Fintype.card F % 4 = 1) {x y : F} (hxy : x ≠ y) :
    (((paleyField F).nbrs x ∩ (paleyField F).nbrs y).card : ℤ) * 4
      = Fintype.card F - 3 - 2 * quadraticChar F (y - x) := by
  have hb : (Finset.univ.filter fun z : F ↦
        quadraticChar F (z - x) = 1 ∧ quadraticChar F (z - y) = 1).card
      = (Finset.univ.filter fun u : F ↦
          quadraticChar F u = 1 ∧ quadraticChar F (u - (y - x)) = 1).card := by
    refine Finset.card_bij (fun z _ ↦ z - x) ?_ (fun a _ b _ h ↦ sub_left_inj.mp h) ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact ⟨hz.1, by rw [show z - x - (y - x) = z - y by ring]; exact hz.2⟩
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨u + x, ⟨by simpa using hu.1, ?_⟩, by ring⟩
      rw [show u + x - y = u - (y - x) by ring]
      exact hu.2
  have ha : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  rw [nbrs_inter_paleyField hq, hb, mul_comm]
  exact card_common_quadraticChar hq ha

/-- **Paley graphs are strongly regular.**  For a finite field with `q ≡ 1 mod 4` elements the
Paley graph has parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)`. -/
theorem isSRGWith_paleyField (hq : Fintype.card F % 4 = 1) :
    (paleyField F).IsSRGWith (Fintype.card F) ((Fintype.card F - 1) / 2)
      ((Fintype.card F - 5) / 4) ((Fintype.card F - 1) / 4) := by
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  refine isSRGWith_of _ rfl (fun (x : F) ↦ card_nbrs_paleyField hq x)
    (fun (x y : F) hadj ↦ ?_) (fun (x y : F) hxy hadj ↦ ?_)
  · -- adjacent: `χ (y - x) = 1`
    rw [paleyField_adj hq] at hadj
    simp only [decide_eq_true_eq] at hadj
    have hxy : x ≠ y := by
      rintro rfl
      rw [sub_self, quadraticChar_zero] at hadj
      exact absurd hadj (by norm_num)
    have := card_nbrs_inter_paleyField hq hxy
    rw [hadj] at this
    omega
  · -- distinct and non-adjacent: `χ (y - x) = -1`
    have ha : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    rw [paleyField_adj hq] at hadj
    simp only [decide_eq_false_iff_not] at hadj
    have hneg : quadraticChar F (y - x) = -1 := (quadraticChar_dichotomy ha).resolve_left hadj
    have := card_nbrs_inter_paleyField hq hxy
    rw [hneg] at this
    omega

theorem quadraticChar_eq_one_iff (a : F) :
    quadraticChar F a = 1 ↔ ∃ r : F, r ≠ 0 ∧ r * r = a := by
  constructor
  · intro h
    have ha : a ≠ 0 := by rintro rfl; rw [quadraticChar_zero] at h; norm_num at h
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare ha).1 h
    exact ⟨r, fun h0 ↦ ha (by rw [hr, h0, mul_zero]), hr.symm⟩
  · rintro ⟨r, hr0, rfl⟩
    exact (quadraticChar_one_iff_isSquare (mul_ne_zero hr0 hr0)).2 ⟨r, rfl⟩

end PaleyField

/-! ### `paley q` is the field version over `ZMod q` -/

/-- `ZMod q` and `Fin q`, matched up by `ZMod.val`. -/
def zmodEquivFin (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun a := ⟨a.val, ZMod.val_lt a⟩
  invFun i := (i.1 : ZMod q)
  left_inv a := ZMod.natCast_rightInverse a
  right_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)

/-- The `Fin q` arithmetic `paley` does to find the offset of `y` from `x` is subtraction in
`ZMod q`. -/
theorem zmod_val_sub {q : ℕ} [NeZero q] (x y : ZMod q) :
    (y.val + q - x.val) % q = (y - x).val := by
  rw [show y.val + q - x.val = y.val + (q - x.val) from by
    have := ZMod.val_lt x; omega, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_sub (le_of_lt (ZMod.val_lt x)), ZMod.natCast_self,
    ZMod.natCast_rightInverse x, ZMod.natCast_rightInverse y, zero_sub, ← sub_eq_add_neg]

/-- The lookup table records exactly the nonzero squares of `ZMod q`. -/
theorem exists_sq_iff_val {q : ℕ} [NeZero q] (a : ZMod q) :
    (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = a.val) ↔ ∃ r : ZMod q, r ≠ 0 ∧ r * r = a := by
  constructor
  · rintro ⟨i, hi, hia⟩
    have hr : ((i.1 : ℕ) : ZMod q).val = i.1 := ZMod.val_cast_of_lt i.2
    refine ⟨(i.1 : ℕ), fun h0 ↦ hi (by rw [← hr, h0, ZMod.val_zero]), ZMod.val_injective q ?_⟩
    rw [ZMod.val_mul, hr, hia]
  · rintro ⟨r, hr0, rfl⟩
    refine ⟨⟨r.val, ZMod.val_lt r⟩, ?_, ?_⟩
    · simpa using fun h ↦ hr0 ((ZMod.val_eq_zero r).1 h)
    · rw [ZMod.val_mul]

theorem paley_adj_eq (q : ℕ) [NeZero q] [Fact q.Prime] (a b : ZMod q) :
    (paley q).Adj (zmodEquivFin q a) (zmodEquivFin q b) = (paleyField (ZMod q)).Adj a b := by
  have key : ∀ u v : ZMod q,
      (qrTable q)[((zmodEquivFin q v).1 + q - (zmodEquivFin q u).1) % q]!
        = decide (quadraticChar (ZMod q) (v - u) = 1) := by
    intro u v
    show (qrTable q)[(v.val + q - u.val) % q]! = _
    rw [zmod_val_sub u v, qrTable_getElem q _ (ZMod.val_lt (v - u))]
    simp only [exists_sq_iff_val, quadraticChar_eq_one_iff]
  show (ofRel (Fin q) _).Adj _ _ = (cayleyAdd (ZMod q) _).Adj a b
  rw [ofRel_adj, cayleyAdd_adj]
  show (decide ((zmodEquivFin q a) ≠ (zmodEquivFin q b)) &&
      ((qrTable q)[((zmodEquivFin q b).1 + q - (zmodEquivFin q a).1) % q]! ||
       (qrTable q)[((zmodEquivFin q a).1 + q - (zmodEquivFin q b).1) % q]!)) = _
  rw [key a b, key b a]
  congr 1
  simp [EmbeddingLike.apply_eq_iff_eq]

/-- For a prime `q`, `paley q` is the Paley graph of the field `ZMod q`. -/
def paleyIso (q : ℕ) [NeZero q] [Fact q.Prime] : paleyField (ZMod q) ≃cg paley q :=
  ⟨zmodEquivFin q, fun {a b} ↦
    iff_of_eq (congrArg (fun x : Bool ↦ x = true) (paley_adj_eq q a b))⟩

/-- **`paley q` is strongly regular** for every prime `q ≡ 1 mod 4`. -/
theorem isSRGWith_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (paley q).IsSRGWith q ((q - 1) / 2) ((q - 5) / 4) ((q - 1) / 4) := by
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have h := isSRGWith_paleyField (F := ZMod q) (by rw [hcard]; exact hq)
  rw [hcard] at h
  exact SimpleGraph.Iso.isSRGWith_of_iso (CGraph.Iso.toSimpleIso (paleyIso q)) h

end SRGFamilies

/-! ## Transitivity of the constructions

`CGraph.IsVertexTransitive` and `CGraph.IsArcTransitive` are decidable, but only by enumerating
the `n!` permutations of the vertex type, which is hopeless past a handful of vertices.  The
lemmas here settle whole families at once by exhibiting the automorphisms directly.

Everything factors through `ofRel`: an automorphism of `ofRel V r` is a permutation of `V`
preserving the *symmetrised* relation `r x y || r y x`, which is a weaker — and so easier to
supply — obligation than preserving `r` itself.  That weakening is what lets the reflections of a
cycle count as automorphisms even though they reverse the successor relation. -/

section Transitivity

variable (G : CGraph)

/-- To see that `ofRel V r` is vertex-transitive it is enough to move `u` to `v` by a permutation
preserving the symmetrisation of `r`. -/
theorem isVertexTransitive_ofRel (V : Type) [Fintype V] [DecidableEq V] (r : V → V → Bool)
    (h : ∀ u v : V, ∃ σ : Equiv.Perm V,
      (∀ x y, (r (σ x) (σ y) || r (σ y) (σ x)) = (r x y || r y x)) ∧ σ u = v) :
    (ofRel V r).IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ, huv⟩ := h u v
  refine ⟨autoOfPerm (G := ofRel V r) σ fun x y ↦ ?_, huv⟩
  show (decide (σ x ≠ σ y) && (r (σ x) (σ y) || r (σ y) (σ x))) =
    (decide (x ≠ y) && (r x y || r y x))
  rw [hσ x y]
  simp

/-- To see that `ofRel V r` is arc-transitive it is enough to match up any two pairs of distinct,
symmetrically-related points. -/
theorem isArcTransitive_ofRel (V : Type) [Fintype V] [DecidableEq V] (r : V → V → Bool)
    (h : ∀ u v u' v' : V, u ≠ v → u' ≠ v' → (r u v || r v u) → (r u' v' || r v' u') →
      ∃ σ : Equiv.Perm V, (∀ x y, (r (σ x) (σ y) || r (σ y) (σ x)) = (r x y || r y x)) ∧
        σ u = u' ∧ σ v = v') :
    (ofRel V r).IsArcTransitive := by
  intro u v u' v' huv hu'v'
  simp only [ofRel_adj, Bool.and_eq_true, decide_eq_true_eq] at huv hu'v'
  obtain ⟨σ, hσ, h₁, h₂⟩ := h u v u' v' huv.1 hu'v'.1 huv.2 hu'v'.2
  refine ⟨autoOfPerm (G := ofRel V r) σ fun x y ↦ ?_, h₁, h₂⟩
  show (decide (σ x ≠ σ y) && (r (σ x) (σ y) || r (σ y) (σ x))) =
    (decide (x ≠ y) && (r x y || r y x))
  rw [hσ x y]
  simp

/-- Arc-transitivity is the stronger property: it implies vertex-transitivity as soon as there
are no isolated vertices.  (The hypothesis is needed: `empty n` is arc-transitive for want of any
arcs at all, but not vertex-transitive for `n ≥ 2`.) -/
theorem isVertexTransitive_of_isArcTransitive
    (hne : ∀ u : G.V, ∃ v, G.Adj u v) (h : G.IsArcTransitive) : G.IsVertexTransitive := by
  intro u v
  obtain ⟨u', hu⟩ := hne u
  obtain ⟨v', hv⟩ := hne v
  obtain ⟨σ, h₁, -⟩ := h u u' v v' hu hv
  exact ⟨σ, h₁⟩

/-- The complement has the same automorphisms, so it is vertex-transitive whenever `G` is. -/
theorem isVertexTransitive_compl [DecidableEq G.V] (h : G.IsVertexTransitive) :
    (compl G).IsVertexTransitive := by
  intro u v
  obtain ⟨σ, hσ⟩ := h u v
  refine ⟨autoOfPerm (G := compl G) σ.toEquiv fun x y ↦ ?_, hσ⟩
  show (decide (σ x ≠ σ y) && !G.Adj (σ x) (σ y)) = (decide (x ≠ y) && !G.Adj x y)
  rw [σ.adj_eq]
  simp [(RelIso.injective σ).eq_iff]

/-- Any two ordered pairs of distinct points are matched by some permutation: swap `u` with `u'`,
then swap the image of `v` with `v'`.  (On a *complete* graph every such permutation is an
automorphism, which is why this gives arc-transitivity there.) -/
theorem exists_perm_apply_apply {α : Type} [DecidableEq α] {u v u' v' : α} (h : u ≠ v)
    (h' : u' ≠ v') : ∃ σ : Equiv.Perm α, σ u = u' ∧ σ v = v' := by
  have key : Equiv.swap u u' v ≠ u' := by
    intro e
    exact h ((Equiv.swap u u').injective (by rw [e, Equiv.swap_apply_left])).symm
  refine ⟨(Equiv.swap u u').trans (Equiv.swap (Equiv.swap u u' v) v'), ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm key) h'
  · simp

theorem empty_eq_ofRel (n : ℕ) : empty n = ofRel (Fin n) fun _ _ ↦ false :=
  eq_ofRel _ _ fun _ _ _ ↦ rfl

theorem complete_eq_ofRel (n : ℕ) : complete n = ofRel (Fin n) fun _ _ ↦ true := by
  rw [complete, compl_eq_ofRel]
  rfl

theorem isVertexTransitive_empty (n : ℕ) : (empty n).IsVertexTransitive := by
  rw [empty_eq_ofRel]
  exact isVertexTransitive_ofRel _ _ fun u v ↦ ⟨Equiv.swap u v, fun _ _ ↦ rfl, by simp⟩

/-- Vacuously: `empty n` has no arcs to move around. -/
theorem isArcTransitive_empty (n : ℕ) : (empty n).IsArcTransitive := by
  intro u v u' v' huv _
  simp at huv

theorem isVertexTransitive_complete (n : ℕ) : (complete n).IsVertexTransitive := by
  rw [complete_eq_ofRel]
  exact isVertexTransitive_ofRel _ _ fun u v ↦ ⟨Equiv.swap u v, fun _ _ ↦ rfl, by simp⟩

theorem isArcTransitive_complete (n : ℕ) : (complete n).IsArcTransitive := by
  rw [complete_eq_ofRel]
  refine isArcTransitive_ofRel _ _ fun u v u' v' huv hu'v' _ _ ↦ ?_
  obtain ⟨σ, h₁, h₂⟩ := exists_perm_apply_apply huv hu'v'
  exact ⟨σ, fun _ _ ↦ rfl, h₁, h₂⟩

/-- Right translation is an automorphism of a Cayley graph. -/
theorem isVertexTransitive_cayleyAdd (A : Type) [Fintype A] [DecidableEq A] [AddGroup A]
    (S : A → Bool) : (cayleyAdd A S).IsVertexTransitive :=
  isVertexTransitive_ofRel A _ fun u v ↦
    ⟨Equiv.addRight (-u + v), fun x y ↦ by simp [add_sub_add_right_eq_sub], by simp⟩

/-- The Paley graph of a finite field is a Cayley graph, hence vertex-transitive. -/
theorem isVertexTransitive_paleyField (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (paleyField F).IsVertexTransitive :=
  isVertexTransitive_cayleyAdd F _

theorem isVertexTransitive_paley (q : ℕ) [NeZero q] [Fact q.Prime] :
    (paley q).IsVertexTransitive :=
  isVertexTransitive_of_iso (paleyIso q) (isVertexTransitive_paleyField (ZMod q))

/-! ### Cycles

The successor relation `(i + 1) % n = j` defining `cycle n` is the group-theoretic successor on
`Fin n`, so the rotations `x ↦ x + d` preserve it and the reflections `x ↦ c - x` reverse it —
and reversing it is enough, since `ofRel` symmetrises.  Together they act transitively on arcs:
rotations match up two arcs that run the same way round, reflections two that run oppositely. -/

private theorem cycle_rel (n : ℕ) [NeZero n] (x y : Fin n) :
    ((x.1 + 1) % n == y.1) = decide (x + 1 = y) := by
  rw [show ((x + 1 : Fin n)) = ⟨(x.1 + 1) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩ from ?_]
  · simp [Fin.ext_iff]
    rfl
  · apply Fin.ext
    simp [Fin.add_def, Nat.add_mod_mod]

private theorem cycle_trans_iff {n : ℕ} [NeZero n] (d x y : Fin n) :
    (x + d + 1 = y + d) ↔ (x + 1 = y) := by
  rw [add_right_comm, add_left_inj]

private theorem cycle_refl_iff {n : ℕ} [NeZero n] (c a b : Fin n) :
    (c - a + 1 = c - b) ↔ (b + 1 = a) := by
  constructor
  · intro h
    have h2 : c - a = c - (b + 1) := by rw [sub_add_eq_sub_sub, ← h]; simp
    exact (sub_right_injective h2).symm
  · rintro rfl
    rw [sub_add_eq_sub_sub, sub_add_cancel]

theorem isVertexTransitive_cycle (n : ℕ) : (cycle n).IsVertexTransitive := by
  match n with
  | 0 => intro u _; exact (u : Fin 0).elim0
  | (m + 1) =>
    rw [cycle]
    refine isVertexTransitive_ofRel _ _ fun u v ↦
      ⟨Equiv.addRight (v - u), fun x y ↦ ?_, by simp⟩
    simp only [Equiv.coe_addRight, cycle_rel, cycle_trans_iff]

theorem isArcTransitive_cycle (n : ℕ) : (cycle n).IsArcTransitive := by
  match n with
  | 0 => intro u _ _ _ _ _; exact (u : Fin 0).elim0
  | (m + 1) =>
    rw [cycle]
    refine isArcTransitive_ofRel _ _ fun u v u' v' _ _ h h' ↦ ?_
    have htrans (d : Fin (m + 1)) (x y : Fin (m + 1)) :
        ((((x + d).1 + 1) % (m + 1) == (y + d).1) || (((y + d).1 + 1) % (m + 1) == (x + d).1)) =
          ((((x.1 + 1) % (m + 1)) == y.1) || (((y.1 + 1) % (m + 1)) == x.1)) := by
      simp only [cycle_rel, cycle_trans_iff]
    have hrefl (c : Fin (m + 1)) (x y : Fin (m + 1)) :
        ((((c - x).1 + 1) % (m + 1) == (c - y).1) || (((c - y).1 + 1) % (m + 1) == (c - x).1)) =
          ((((x.1 + 1) % (m + 1)) == y.1) || (((y.1 + 1) % (m + 1)) == x.1)) := by
      simp only [cycle_rel, cycle_refl_iff, Bool.or_comm]
    simp only [cycle_rel, Bool.or_eq_true, decide_eq_true_eq] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · refine ⟨Equiv.addRight (u' - u), fun x y ↦ by
        simpa only [Equiv.coe_addRight] using htrans (u' - u) x y, by simp, ?_⟩
      simp only [Equiv.coe_addRight, ← h]
      rw [add_right_comm, add_comm u (u' - u), sub_add_cancel]
      exact h'
    · refine ⟨Equiv.subLeft (u' + u), fun x y ↦ by
        simpa only [Equiv.subLeft_apply] using hrefl (u' + u) x y, ?_, ?_⟩
      · rw [Equiv.subLeft_apply, add_sub_cancel_right]
      · rw [Equiv.subLeft_apply, ← h, sub_add_eq_sub_sub, add_sub_cancel_right, ← h',
          add_sub_cancel_right]
    · refine ⟨Equiv.subLeft (u' + u), fun x y ↦ by
        simpa only [Equiv.subLeft_apply] using hrefl (u' + u) x y, ?_, ?_⟩
      · rw [Equiv.subLeft_apply, add_sub_cancel_right]
      · rw [Equiv.subLeft_apply, ← h, add_comm v 1, ← add_assoc, add_sub_cancel_right, h']
    · refine ⟨Equiv.addRight (u' - u), fun x y ↦ by
        simpa only [Equiv.coe_addRight] using htrans (u' - u) x y, by simp, ?_⟩
      subst h
      subst h'
      rw [Equiv.coe_addRight, add_sub_add_right_eq_sub]
      simp

/-! ### Hypercubes

Adding a fixed bit-string is an automorphism of both the hypercube and the folded cube: it does
not change *which* coordinates two strings differ in. -/

private theorem xorPerm_involutive (n : ℕ) (d : Fin n → Bool) :
    Function.Involutive (fun x : Fin n → Bool ↦ fun i ↦ x i ^^ d i) := fun x ↦ by
  funext i
  simp

private theorem filter_xor_eq (n : ℕ) (d x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ (x i ^^ d i) ≠ (y i ^^ d i)) =
      (Finset.univ.filter fun i ↦ x i ≠ y i) :=
  Finset.filter_congr fun i _ ↦ by
    simp only [ne_eq]
    constructor
    · intro h he; exact h (by rw [he])
    · intro h he; exact h (Bool.xor_left_inj.1 he)

theorem isVertexTransitive_hypercube (n : ℕ) : (hypercube n).IsVertexTransitive := by
  rw [hypercube_eq_ofRel]
  refine isVertexTransitive_ofRel _ _ fun u v ↦
    ⟨(xorPerm_involutive n fun i ↦ u i ^^ v i).toPerm _, fun x y ↦ ?_, ?_⟩
  · show ((Finset.univ.filter fun i ↦ (x i ^^ _) ≠ (y i ^^ _)).card == 1 ||
      (Finset.univ.filter fun i ↦ (y i ^^ _) ≠ (x i ^^ _)).card == 1) = _
    rw [filter_xor_eq, filter_xor_eq]
  · funext i
    show (u i ^^ (u i ^^ v i)) = v i
    simp

private theorem xor_eq_decide_of_filter_eq {n : ℕ} {x y : Fin n → Bool} {i₀ : Fin n}
    (h : (Finset.univ.filter fun i ↦ x i ≠ y i) = {i₀}) (k : Fin n) :
    (x k ^^ y k) = decide (k = i₀) := by
  have hiff : (x k ≠ y k) ↔ k = i₀ := by
    constructor
    · intro hk
      have : k ∈ ({i₀} : Finset (Fin n)) := h ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      simpa using this
    · rintro rfl
      have : k ∈ (Finset.univ.filter fun i ↦ x i ≠ y i) := h ▸ Finset.mem_singleton_self k
      exact (Finset.mem_filter.1 this).2
  have hxor : (x k ^^ y k) = decide (x k ≠ y k) := by cases x k <;> cases y k <;> simp
  rw [hxor, decide_eq_decide.2 hiff]

/-- Adding a fixed bit-string is an automorphism of the hypercube. -/
def cubeXor (n : ℕ) (d : Fin n → Bool) : hypercube n ≃cg hypercube n :=
  autoOfPerm (G := hypercube n) ((xorPerm_involutive n d).toPerm _) fun x y ↦ by
    show ((Finset.univ.filter fun i ↦ (x i ^^ d i) ≠ (y i ^^ d i)).card == 1) = _
    rw [filter_xor_eq]
    rfl

/-- Permuting the coordinates is an automorphism of the hypercube: it does not change *how many*
coordinates two strings differ in. -/
def cubeCoord (n : ℕ) (τ : Equiv.Perm (Fin n)) : hypercube n ≃cg hypercube n :=
  autoOfPerm (G := hypercube n) (Equiv.arrowCongr τ (Equiv.refl Bool)) fun x y ↦ by
    show ((Finset.univ.filter fun i ↦ x (τ.symm i) ≠ y (τ.symm i)).card == 1) = _
    congr 1
    exact Finset.card_equiv τ.symm (by simp)

/-- The hypercube is arc-transitive: translate the first endpoint to the origin, swap the
coordinate in which the arc moves for the one the target arc moves in, then translate to the
second endpoint. -/
theorem isArcTransitive_hypercube (n : ℕ) : (hypercube n).IsArcTransitive := by
  intro u v u' v' huv hu'v'
  rw [hypercube_adj, beq_iff_eq] at huv hu'v'
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 huv
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.1 hu'v'
  have hswap : ∀ i : Fin n, decide (Equiv.swap i₀ j₀ i = i₀) = decide (i = j₀) := fun i ↦ by
    rw [decide_eq_decide, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  refine ⟨((cubeXor n u).trans (cubeCoord n (Equiv.swap i₀ j₀))).trans (cubeXor n u'), ?_, ?_⟩
  · funext i
    show ((u (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) ^^ u' i) = u' i
    simp
  · funext i
    show ((v (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) ^^ u' i) = v' i
    have h1 : (u (Equiv.swap i₀ j₀ i) ^^ v (Equiv.swap i₀ j₀ i))
        = decide (Equiv.swap i₀ j₀ i = i₀) := xor_eq_decide_of_filter_eq hi₀ _
    have h2 : (u' i ^^ v' i) = decide (i = j₀) := xor_eq_decide_of_filter_eq hj₀ i
    have h3 : (v (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) = (u' i ^^ v' i) := by
      rw [Bool.xor_comm (v _) (u _), h1, hswap, ← h2]
    rw [h3]
    cases u' i <;> cases v' i <;> simp

theorem isVertexTransitive_foldedCube (n : ℕ) : (foldedCube n).IsVertexTransitive := by
  intro u v
  refine ⟨autoOfPerm (G := foldedCube n)
    ((xorPerm_involutive n fun i ↦ u i ^^ v i).toPerm _) fun x y ↦ ?_, ?_⟩
  · show (decide ((fun i ↦ x i ^^ _) ≠ (fun i ↦ y i ^^ _)) &&
      (((Finset.univ.filter fun i ↦ (x i ^^ _) ≠ (y i ^^ _)).card == 1) ||
        ((Finset.univ.filter fun i ↦ (x i ^^ _) ≠ (y i ^^ _)).card == n))) = _
    rw [filter_xor_eq]
    congr 1
    exact decide_eq_decide.2 ((xorPerm_involutive n fun i ↦ u i ^^ v i).toPerm _).injective.ne_iff
  · funext i
    show (u i ^^ (u i ^^ v i)) = v i
    simp

/-! ### Products

An automorphism of each factor gives an automorphism of any of the four products, acting
coordinatewise. -/

theorem isVertexTransitive_cartesianProduct (H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (cartesianProduct G H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := cartesianProduct G H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (cartesianProduct G H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [cartesianProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff,
    (RelIso.injective τ).eq_iff]

theorem isVertexTransitive_tensorProduct (H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (tensorProduct G H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := tensorProduct G H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (tensorProduct G H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [tensorProduct_adj, σ.adj_eq, τ.adj_eq]

theorem isVertexTransitive_strongProduct (H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (strongProduct G H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := strongProduct G H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (strongProduct G H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [strongProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff,
    (RelIso.injective τ).eq_iff, ne_eq, Prod.ext_iff]

theorem isVertexTransitive_lexProduct (H : CGraph) [DecidableEq G.V] [DecidableEq H.V]
    (hG : G.IsVertexTransitive) (hH : H.IsVertexTransitive) :
    (lexProduct G H).IsVertexTransitive := by
  rintro ⟨u₁, u₂⟩ ⟨v₁, v₂⟩
  obtain ⟨σ, hσ⟩ := hG u₁ v₁
  obtain ⟨τ, hτ⟩ := hH u₂ v₂
  refine ⟨autoOfPerm (G := lexProduct G H) (Equiv.prodCongr σ.toEquiv τ.toEquiv)
    fun x y ↦ ?_, by show (σ u₁, τ u₂) = (v₁, v₂); rw [hσ, hτ]⟩
  show (lexProduct G H).Adj (σ x.1, τ x.2) (σ y.1, τ y.2) = _
  simp only [lexProduct_adj, σ.adj_eq, τ.adj_eq, (RelIso.injective σ).eq_iff]

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

@[simp] theorem bipartiteCongr_inl (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (a : Fin n) :
    bipartiteCongr n σ τ (.inl a) = .inl (σ a) := rfl

@[simp] theorem bipartiteCongr_inr (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (b : Fin n) :
    bipartiteCongr n σ τ (.inr b) = .inr (τ b) := rfl

@[simp] theorem bipartiteSwap_inl (n : ℕ) (a : Fin n) : bipartiteSwap n (.inl a) = .inr a := rfl

@[simp] theorem bipartiteSwap_inr (n : ℕ) (b : Fin n) : bipartiteSwap n (.inr b) = .inl b := rfl

/-- Permuting the rays of the star `K_{1,n}` and fixing its centre. -/
def starAut (n : ℕ) (σ : Equiv.Perm (Fin n)) : bipartite 1 n ≃cg bipartite 1 n :=
  autoOfPerm (G := bipartite 1 n) (Equiv.sumCongr (Equiv.refl (Fin 1)) σ) fun x y ↦ by
    show (bipartite 1 n).Adj (Sum.map id σ x) (Sum.map id σ y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

@[simp] theorem starAut_inl (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : Fin 1) :
    starAut n σ (.inl a) = .inl a := rfl

@[simp] theorem starAut_inr (n : ℕ) (σ : Equiv.Perm (Fin n)) (b : Fin n) :
    starAut n σ (.inr b) = .inr (σ b) := rfl

/-- Every arc of `K_{m,n}` crosses between the two sides. -/
theorem bipartite_arc (m n : ℕ) (x y : (bipartite m n).V) (h : (bipartite m n).Adj x y) :
    (∃ a b, x = .inl a ∧ y = .inr b) ∨ (∃ a b, x = .inr b ∧ y = .inl a) := by
  rcases x with a | b <;> rcases y with c | d
  · simp at h
  · exact Or.inl ⟨a, d, rfl, rfl⟩
  · exact Or.inr ⟨c, b, rfl, rfl⟩
  · simp at h

theorem isArcTransitive_bipartite_self (n : ℕ) : (bipartite n n).IsArcTransitive := by
  rintro u v u' v' huv hu'v'
  rcases bipartite_arc n n u v huv with ⟨a, b, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ <;>
    rcases bipartite_arc n n u' v' hu'v' with ⟨a', b', rfl, rfl⟩ | ⟨a', b', rfl, rfl⟩
  · exact ⟨bipartiteCongr n (Equiv.swap a a') (Equiv.swap b b'), by simp, by simp⟩
  · exact ⟨(bipartiteCongr n (Equiv.swap a b') (Equiv.swap b a')).trans (bipartiteSwap n),
      by simp, by simp⟩
  · exact ⟨(bipartiteSwap n).trans (bipartiteCongr n (Equiv.swap b a') (Equiv.swap a b')),
      by simp, by simp⟩
  · exact ⟨bipartiteCongr n (Equiv.swap a a') (Equiv.swap b b'), by simp, by simp⟩

theorem isVertexTransitive_bipartite_self (n : ℕ) : (bipartite n n).IsVertexTransitive := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rintro (u | u) <;> exact (u : Fin 0).elim0
  · refine isVertexTransitive_of_isArcTransitive _ (fun u ↦ ?_) (isArcTransitive_bipartite_self n)
    rcases u with a | b
    · exact ⟨.inr ⟨0, hn⟩, by simp⟩
    · exact ⟨.inl ⟨0, hn⟩, by simp⟩

/-! ### Line graphs

Vertices of `lineGraph G` are edges of `G`, so an automorphism of `G` acts on them, and an
automorphism carrying one arc to another carries one edge to the other. -/

section LineGraph

variable [DecidableEq G.V]

/-- An automorphism of `G` maps edges to edges, bijectively. -/
def edgePerm (σ : G ≃cg G) : Equiv.Perm {e : Sym2 G.V // e ∈ G.toSimple.edgeSet} where
  toFun e := ⟨Sym2.map σ e.1, σ.toSimpleIso.toHom.map_mem_edgeSet e.2⟩
  invFun e := ⟨Sym2.map σ.symm e.1, (Iso.toSimpleIso σ.symm).toHom.map_mem_edgeSet e.2⟩
  left_inv e := by ext : 1; simp [Sym2.map_map]
  right_inv e := by ext : 1; simp [Sym2.map_map]

omit [DecidableEq G.V] in
@[simp] theorem edgePerm_coe (σ : G ≃cg G) (x : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) :
    ((G.edgePerm σ x : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) : Sym2 G.V)
      = Sym2.map σ (x : Sym2 G.V) := rfl

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

/-- An arc-transitive graph has a vertex-transitive line graph. -/
theorem isVertexTransitive_lineGraph (h : G.IsArcTransitive) :
    (lineGraph G).IsVertexTransitive := by
  have key : ∀ (u v u' v' : G.V) (huv : s(u, v) ∈ G.toSimple.edgeSet)
      (hu'v' : s(u', v') ∈ G.toSimple.edgeSet),
      ∃ σ : lineGraph G ≃cg lineGraph G,
        σ (⟨s(u, v), huv⟩ : {e : Sym2 G.V // e ∈ G.toSimple.edgeSet}) = ⟨s(u', v'), hu'v'⟩ := by
    intro u v u' v' huv hu'v'
    obtain ⟨σ, h₁, h₂⟩ := h u v u' v' (by simpa using huv) (by simpa using hu'v')
    refine ⟨G.lineGraphAuto σ, ?_⟩
    show G.edgePerm σ ⟨s(u, v), huv⟩ = _
    exact Subtype.ext (by simp [edgePerm_coe, h₁, h₂])
  rintro ⟨e, he⟩ ⟨f, hf⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ u' v' => exact key u v u' v' he hf

end LineGraph

/-! ### Kneser graphs

Permutations of the ground set act on the `k`-subsets, and any two *disjoint pairs* of `k`-subsets
are matched by one of them — which is precisely arc-transitivity, an arc of `kneser n k` being a
pair of disjoint `k`-sets. -/

/-- Two disjoint pairs of finsets of matching sizes are related by a permutation of the whole
(finite) type: match up the two parts, and the two complements with each other. -/
theorem exists_perm_image₂ {α : Type} [Fintype α] [DecidableEq α] {A B A' B' : Finset α}
    (hAB : Disjoint A B) (hA'B' : Disjoint A' B') (hA : A.card = A'.card)
    (hB : B.card = B'.card) : ∃ π : Equiv.Perm α, A.image π = A' ∧ B.image π = B' := by
  classical
  set C : Finset α := (A ∪ B)ᶜ with hC
  set C' : Finset α := (A' ∪ B')ᶜ with hC'
  have hCcard : C.card = C'.card := by
    rw [hC, hC', Finset.card_compl, Finset.card_compl, Finset.card_union_of_disjoint hAB,
      Finset.card_union_of_disjoint hA'B', hA, hB]
  let eA := Finset.equivOfCardEq hA
  let eB := Finset.equivOfCardEq hB
  let eC := Finset.equivOfCardEq hCcard
  set f : α → α := fun x ↦
      if h : x ∈ A then (eA ⟨x, h⟩ : α)
      else if h' : x ∈ B then (eB ⟨x, h'⟩ : α)
      else (eC ⟨x, by simp [hC, h, h']⟩ : α) with hf
  have hfA : ∀ x (h : x ∈ A), f x = eA ⟨x, h⟩ := fun x h ↦ by simp [hf, h]
  have hfB : ∀ x (h : x ∉ A) (h' : x ∈ B), f x = eB ⟨x, h'⟩ := fun x h h' ↦ by simp [hf, h, h']
  have hfC : ∀ x (h : x ∉ A) (h' : x ∉ B), f x ∈ C' := fun x h h' ↦ by
    rw [hf]; simp only [h, h', dite_false]
    exact (eC ⟨x, by simp [hC, h, h']⟩).2
  have hmemA : ∀ x, x ∈ A → f x ∈ A' := fun x h ↦ by rw [hfA x h]; exact (eA ⟨x, h⟩).2
  have hmemB : ∀ x, x ∈ B → f x ∈ B' := fun x h ↦ by
    have hxA : x ∉ A := Finset.disjoint_right.1 hAB h
    rw [hfB x hxA h]; exact (eB ⟨x, h⟩).2
  have hC'mem : ∀ x, x ∈ C' → x ∉ A' ∧ x ∉ B' := by
    intro x hx
    rw [hC', Finset.mem_compl, Finset.mem_union] at hx
    exact ⟨fun h ↦ hx (Or.inl h), fun h ↦ hx (Or.inr h)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · have : (eA ⟨x, hxA⟩ : α) = eA ⟨y, hyA⟩ := by rw [← hfA x hxA, ← hfA y hyA, hxy]
      simpa using congrArg Subtype.val (eA.injective (Subtype.ext this))
    · by_cases hyB : y ∈ B
      · have h1 : f y ∈ A' := by rw [← hxy]; exact hmemA x hxA
        exact absurd (hmemB y hyB) (Finset.disjoint_left.1 hA'B' h1)
      · have h1 : f y ∈ A' := by rw [← hxy]; exact hmemA x hxA
        exact absurd h1 (hC'mem _ (hfC y hyA hyB)).1
    · by_cases hxB : x ∈ B
      · have h1 : f x ∈ A' := by rw [hxy]; exact hmemA y hyA
        exact absurd (hmemB x hxB) (Finset.disjoint_left.1 hA'B' h1)
      · have h1 : f x ∈ A' := by rw [hxy]; exact hmemA y hyA
        exact absurd h1 (hC'mem _ (hfC x hxA hxB)).1
    · by_cases hxB : x ∈ B <;> by_cases hyB : y ∈ B
      · have : (eB ⟨x, hxB⟩ : α) = eB ⟨y, hyB⟩ := by
          rw [← hfB x hxA hxB, ← hfB y hyA hyB, hxy]
        simpa using congrArg Subtype.val (eB.injective (Subtype.ext this))
      · have h1 : f y ∈ B' := by rw [← hxy]; exact hmemB x hxB
        exact absurd h1 (hC'mem _ (hfC y hyA hyB)).2
      · have h1 : f x ∈ B' := by rw [hxy]; exact hmemB y hyB
        exact absurd h1 (hC'mem _ (hfC x hxA hxB)).2
      · have hx : f x = eC ⟨x, by simp [hC, hxA, hxB]⟩ := by
          rw [hf]; simp only [hxA, hxB, dite_false]
        have hy : f y = eC ⟨y, by simp [hC, hyA, hyB]⟩ := by
          rw [hf]; simp only [hyA, hyB, dite_false]
        have : (eC ⟨x, by simp [hC, hxA, hxB]⟩ : α) = eC ⟨y, by simp [hC, hyA, hyB]⟩ := by
          rw [← hx, ← hy, hxy]
        simpa using congrArg Subtype.val (eC.injective (Subtype.ext this))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_, ?_⟩
  · show A.image f = A'
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmemA x hx
    · rw [Finset.card_image_of_injective _ hinj, hA]
  · show B.image f = B'
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hmemB x hx
    · rw [Finset.card_image_of_injective _ hinj, hB]

/-- A permutation of `Fin n` permutes the `k`-subsets. -/
def kneserPerm (n k : ℕ) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm {s : Finset (Fin n) // s.card = k} where
  toFun s := ⟨s.1.image π, by rw [Finset.card_image_of_injective _ π.injective]; exact s.2⟩
  invFun s := ⟨s.1.image π.symm, by
    rw [Finset.card_image_of_injective _ π.symm.injective]; exact s.2⟩
  left_inv s := by ext : 1; simp [Finset.image_image]
  right_inv s := by ext : 1; simp [Finset.image_image]

@[simp] theorem kneserPerm_coe (n k : ℕ) (π : Equiv.Perm (Fin n))
    (s : {s : Finset (Fin n) // s.card = k}) :
    ((kneserPerm n k π s : {s : Finset (Fin n) // s.card = k}) : Finset (Fin n))
      = (s : Finset (Fin n)).image π := rfl

/-- A permutation of the ground set is an automorphism of the Kneser graph. -/
def kneserAuto (n k : ℕ) (π : Equiv.Perm (Fin n)) : kneser n k ≃cg kneser n k :=
  autoOfPerm (G := kneser n k) (kneserPerm n k π) fun s t ↦ by
    obtain ⟨s, hs⟩ := s
    obtain ⟨t, ht⟩ := t
    show (kneser n k).Adj (kneserPerm n k π ⟨s, hs⟩) (kneserPerm n k π ⟨t, ht⟩) = _
    simp only [kneser_adj, ne_eq, Subtype.ext_iff, kneserPerm_coe,
      (Finset.image_injective π.injective).eq_iff, ← Finset.image_inter _ _ π.injective,
      Finset.image_eq_empty]

theorem isArcTransitive_kneser (n k : ℕ) : (kneser n k).IsArcTransitive := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨A', hA'⟩ ⟨B', hB'⟩ h h'
  simp only [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at h h'
  obtain ⟨π, hπA, hπB⟩ := exists_perm_image₂
    (Finset.disjoint_iff_inter_eq_empty.2 h.2) (Finset.disjoint_iff_inter_eq_empty.2 h'.2)
    (hA.trans hA'.symm) (hB.trans hB'.symm)
  exact ⟨kneserAuto n k π, Subtype.ext hπA, Subtype.ext hπB⟩

/-- Kneser graphs are vertex-transitive.  This does not go through
`isVertexTransitive_of_isArcTransitive`, which would need `kneser n k` to have an arc at all:
`exists_perm_image₂` with both second components empty does it directly. -/
theorem isVertexTransitive_kneser (n k : ℕ) : (kneser n k).IsVertexTransitive := by
  rintro ⟨A, hA⟩ ⟨A', hA'⟩
  obtain ⟨π, hπ, -⟩ := exists_perm_image₂ (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right A') (hA.trans hA'.symm) rfl
  exact ⟨kneserAuto n k π, Subtype.ext hπ⟩

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

/-- Johnson graphs are vertex-transitive.  As for `isVertexTransitive_kneser`, this does not go
through `isVertexTransitive_of_isArcTransitive`: `exists_perm_image₂` with both second
components empty produces the permutation directly. -/
theorem isVertexTransitive_johnson (n k : ℕ) : (johnson n k).IsVertexTransitive := by
  rintro ⟨A, hA⟩ ⟨A', hA'⟩
  obtain ⟨π, hπ, -⟩ := exists_perm_image₂ (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right A') (hA.trans hA'.symm) rfl
  exact ⟨johnsonAuto n k π, Subtype.ext hπ⟩

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
example : (cartesianProduct (cycle 4) (complete 2)).IsVertexTransitive :=
  isVertexTransitive_cartesianProduct _ _ (isVertexTransitive_cycle 4)
    (isVertexTransitive_complete 2)
example : (compl (kneser 4 2)).IsVertexTransitive :=
  isVertexTransitive_compl _ (isVertexTransitive_kneser 4 2)

end Transitivity

end CGraph
