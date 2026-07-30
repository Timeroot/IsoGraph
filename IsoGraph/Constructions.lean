import IsoGraph.Invariants
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Constructions

Ways of building a `CGraph`.  Everything here is a plain definition — no `Classical.choice` — so
every graph in this file can be handed to `CGraph.canonicalize` and actually run.

The guiding principle is the one from `isograph_draft.txt`: build the zoo out of a very small
number of primitives.  `ofRel` symmetrises an arbitrary `Bool`-valued relation and deletes the
diagonal, which is the only "graph axioms" work anybody has to do; `empty`, `disjUnion` and
`compl` then generate most of the rest —

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
what the invariants of `IsoGraph/Invariants.lean` evaluate to.  Proofs that run longer than a few
lines are left as `sorry` for now — the statements are the point.
-/

open Fintype

namespace CGraph

/-! ## The primitives -/

/-- A `CGraph` from an arbitrary relation: symmetrise it, and delete the diagonal.

This is the only place in the file where the graph axioms have to be checked; every construction
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

@[simp] theorem empty_adj (n : ℕ) (i j : (empty n).V) : (empty n).Adj i j = false := rfl

@[simp] theorem card_empty (n : ℕ) : Fintype.card (empty n).V = n := Fintype.card_fin n

/-- The complement: same vertices, edges exactly where there were none. -/
def compl (G : CGraph) [DecidableEq G.V] : CGraph :=
  ofRel G.V fun x y ↦ !G.Adj x y

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (compl G).V :=
  inferInstanceAs (DecidableEq G.V)

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

/-- The disjoint union of a finite family of graphs, on the sigma type. -/
def sigmaUnion {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] : CGraph :=
  ofRel (Σ i, (F i).V) fun x y ↦ if h : x.1 = y.1 then (F y.1).Adj (h ▸ x.2) y.2 else false

instance {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph) [∀ i, DecidableEq (F i).V] :
    DecidableEq (sigmaUnion F).V := inferInstanceAs (DecidableEq (Σ i, (F i).V))

@[simp] theorem card_sigmaUnion {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CGraph)
    [∀ i, DecidableEq (F i).V] :
    Fintype.card (sigmaUnion F).V = ∑ i, Fintype.card (F i).V := Fintype.card_sigma

/-! ## Built out of the primitives -/

/-- The complete graph on `n` vertices. -/
def complete (n : ℕ) : CGraph := compl (empty n)

instance (n : ℕ) : DecidableEq (complete n).V := inferInstanceAs (DecidableEq (Fin n))

@[simp] theorem card_complete (n : ℕ) : Fintype.card (complete n).V = n := Fintype.card_fin n

/-- The join: a disjoint union together with every edge between the two parts. -/
def join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  compl (disjUnion (compl G) (compl H))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : DecidableEq (join G H).V :=
  inferInstanceAs (DecidableEq (G.V ⊕ H.V))

@[simp] theorem card_join (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    Fintype.card (join G H).V = Fintype.card G.V + Fintype.card H.V := Fintype.card_sum

/-- The complete bipartite graph `K_{m,n}`. -/
def bipartite (m n : ℕ) : CGraph := compl (disjUnion (complete m) (complete n))

instance (m n : ℕ) : DecidableEq (bipartite m n).V :=
  inferInstanceAs (DecidableEq (Fin m ⊕ Fin n))

@[simp] theorem card_bipartite (m n : ℕ) : Fintype.card (bipartite m n).V = m + n := by
  simp [bipartite]

/-- The complete multipartite graph with parts of sizes `ds`. -/
def completeMultipartite (ds : List ℕ) : CGraph :=
  compl (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))

instance (ds : List ℕ) : DecidableEq (completeMultipartite ds).V :=
  inferInstanceAs (DecidableEq (Σ i : Fin ds.length, (complete (ds.get i)).V))

/-- The star with `n` leaves. -/
def star (n : ℕ) : CGraph := bipartite 1 n

/-! ## Paths, cycles and theta graphs -/

/-- The path on `n` vertices. -/
def path (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ i.1 + 1 == j.1

instance (n : ℕ) : DecidableEq (path n).V := inferInstanceAs (DecidableEq (Fin n))

@[simp] theorem card_path (n : ℕ) : Fintype.card (path n).V = n := Fintype.card_fin n

/-- The cycle on `n` vertices.  For `n ≤ 2` this degenerates: `cycle 0` and `cycle 1` are
edgeless, and `cycle 2` is a single edge. -/
def cycle (n : ℕ) : CGraph := ofRel (Fin n) fun i j ↦ (i.1 + 1) % n == j.1

instance (n : ℕ) : DecidableEq (cycle n).V := inferInstanceAs (DecidableEq (Fin n))

@[simp] theorem card_cycle (n : ℕ) : Fintype.card (cycle n).V = n := Fintype.card_fin n

/-- The wheel: a cycle plus a hub joined to all of it. -/
def wheel (n : ℕ) : CGraph := join (complete 1) (cycle n)

/-- The edges of the theta graph: vertex `0` and vertex `1` are the poles, and the `i`-th path
uses `xs[i]` fresh internal vertices starting at `off`. -/
private def thetaEdges : ℕ → List ℕ → List (ℕ × ℕ)
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

/-! ## Products

All four products live on `G.V × H.V` and differ only in the adjacency; `ofRel` deletes the
diagonal, so none of them has to special-case `p = q`. -/

/-- The cartesian product `G □ H`: move in one coordinate, stay put in the other. -/
def cartesianProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  ofRel (G.V × H.V) fun p q ↦
    (decide (p.1 = q.1) && H.Adj p.2 q.2) || (G.Adj p.1 q.1 && decide (p.2 = q.2))

/-- The tensor (categorical) product `G × H`: move in both coordinates. -/
def tensorProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  ofRel (G.V × H.V) fun p q ↦ G.Adj p.1 q.1 && H.Adj p.2 q.2

/-- The strong product `G ⊠ H`: the union of the cartesian and tensor products. -/
def strongProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  ofRel (G.V × H.V) fun p q ↦
    (decide (p.1 = q.1) || G.Adj p.1 q.1) && (decide (p.2 = q.2) || H.Adj p.2 q.2)

/-- The lexicographic product `G[H]`: `G` on the first coordinate, and a copy of `H` inside each
fibre. -/
def lexProduct (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] : CGraph :=
  ofRel (G.V × H.V) fun p q ↦ G.Adj p.1 q.1 || (decide (p.1 = q.1) && H.Adj p.2 q.2)

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (cartesianProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (tensorProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (strongProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

instance (G H : CGraph) [DecidableEq G.V] [DecidableEq H.V] :
    DecidableEq (lexProduct G H).V := inferInstanceAs (DecidableEq (G.V × H.V))

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

/-- The hypercube `Q_n`: bit-strings of length `n`, adjacent when they differ in exactly one
place.  This is the `n`-fold cartesian product of `complete 2`, but written directly: threading a
`DecidableEq` instance through that recursion costs more than it saves, since
`cartesianProduct` needs the instance for the graph it is about to build. -/
def hypercube (n : ℕ) : CGraph :=
  ofRel (Fin n → Bool) fun x y ↦ (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1

instance (n : ℕ) : DecidableEq (hypercube n).V :=
  inferInstanceAs (DecidableEq (Fin n → Bool))

/-! ## The funnier ones -/

/-- The Kneser graph `K(n, k)`: the `k`-element subsets of `Fin n`, adjacent when disjoint.
`kneser 5 2` is the Petersen graph. -/
def kneser (n k : ℕ) : CGraph :=
  ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ decide (s.1 ∩ t.1 = ∅)

instance (n k : ℕ) : DecidableEq (kneser n k).V :=
  inferInstanceAs (DecidableEq {s : Finset (Fin n) // s.card = k})

/-- The line graph: one vertex per edge of `G`, two of them adjacent when the edges meet. -/
def lineGraph (G : CGraph) [DecidableEq G.V] : CGraph :=
  ofRel {e : Sym2 G.V // e ∈ G.toSimple.edgeSet} fun e f ↦
    decide (∃ v, v ∈ (e.1 : Sym2 G.V) ∧ v ∈ (f.1 : Sym2 G.V))

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (lineGraph G).V :=
  inferInstanceAs (DecidableEq {e : Sym2 G.V // e ∈ G.toSimple.edgeSet})

/-- The Mycielskian of `G`: a copy of `G`, a *shadow* `v'` of each vertex `v` joined to the
neighbours of `v`, and one apex joined to every shadow.  It raises the chromatic number by one
without creating a triangle. -/
def mycielskian (G : CGraph) [DecidableEq G.V] : CGraph :=
  ofRel (Option (G.V ⊕ G.V)) fun x y ↦
    match x, y with
    | some (.inl a), some (.inl b) => G.Adj a b
    | some (.inl a), some (.inr b) => G.Adj a b
    | some (.inr a), some (.inl b) => G.Adj a b
    | none, some (.inr _) => true
    | some (.inr _), none => true
    | _, _ => false

instance (G : CGraph) [DecidableEq G.V] : DecidableEq (mycielskian G).V :=
  inferInstanceAs (DecidableEq (Option (G.V ⊕ G.V)))

/-! ## Invariants of the constructions

What the invariants of `IsoGraph/Invariants.lean` come to on the graphs above.  Anything whose
proof runs past a handful of lines is left as `sorry`: the statements are what is wanted here, and
the proofs can be filled in as the `SimpleGraph` bridge gets more API.
-/

section Invariants

variable (G H : CGraph)

/-! ### The empty graph -/

@[simp] theorem empty_toSimple (n : ℕ) : (empty n).toSimple = ⊥ := by
  ext i j
  simp

@[simp] theorem E_empty (n : ℕ) : (empty n).E = 0 := by
  simp [E]

theorem isAcyclic_empty (n : ℕ) : (empty n).IsAcyclic := by
  simp [IsAcyclic]

theorem indepNum_empty (n : ℕ) : (empty n).indepNum = n := sorry

theorem cliqueNum_empty (n : ℕ) : (empty n).cliqueNum = min n 1 := sorry

theorem degSequence_empty (n : ℕ) : (empty n).degSequence = List.replicate n 0 := sorry

theorem isConnected_empty_one : (empty 1).IsConnected := sorry

/-! ### The complement -/

@[simp] theorem compl_toSimple [DecidableEq G.V] : (compl G).toSimple = G.toSimpleᶜ := by
  ext x y
  simp [compl, G.symm x y, SimpleGraph.compl_adj]

theorem compl_compl [DecidableEq G.V] : compl (compl G) = G := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  rcases eq_or_ne x y with rfl | h
  · simp [compl, G.loopless x]
  · simp [compl, h, Ne.symm h, G.symm x y]

theorem indepNum_compl [DecidableEq G.V] : (compl G).indepNum = G.cliqueNum := sorry

theorem cliqueNum_compl [DecidableEq G.V] : (compl G).cliqueNum = G.indepNum := sorry

theorem E_compl [DecidableEq G.V] :
    (compl G).E + G.E = (Fintype.card G.V).choose 2 := sorry

/-! ### The complete graph -/

@[simp] theorem complete_toSimple (n : ℕ) : (complete n).toSimple = ⊤ := by
  simp [complete]

@[simp] theorem E_complete (n : ℕ) : (complete n).E = n.choose 2 := by
  have h : (complete n).E = Fintype.card ↥(⊤ : SimpleGraph (Fin n)).edgeSet := by
    simp [E, SimpleGraph.edgeFinset_card]
  rw [h, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem cliqueNum_complete (n : ℕ) : (complete n).cliqueNum = n := sorry

theorem indepNum_complete (n : ℕ) : (complete n).indepNum = min n 1 := sorry

theorem isConnected_complete (n : ℕ) : (complete (n + 1)).IsConnected := by
  have : Nonempty (complete (n + 1)).V := ⟨(0 : Fin (n + 1))⟩
  simp [IsConnected]

theorem diameter_complete (n : ℕ) : (complete (n + 2)).diameter = 1 := sorry

theorem degSequence_complete (n : ℕ) :
    (complete n).degSequence = List.replicate n (n - 1) := sorry

/-! ### Paths and cycles -/

@[simp] theorem path_toSimple (n : ℕ) : (path n).toSimple = SimpleGraph.pathGraph n := by
  ext i j
  simp only [toSimple_adj, path, ofRel_adj, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq, SimpleGraph.pathGraph_adj, ne_eq, Fin.ext_iff]
  omega

theorem isConnected_path (n : ℕ) : (path (n + 1)).IsConnected := by
  simpa [IsConnected] using SimpleGraph.pathGraph_connected n

theorem isAcyclic_path (n : ℕ) : (path n).IsAcyclic := sorry

theorem isTree_path (n : ℕ) : (path (n + 1)).IsTree :=
  ⟨isConnected_path n, isAcyclic_path (n + 1)⟩

theorem E_path (n : ℕ) : (path (n + 1)).E = n := sorry

theorem diameter_path (n : ℕ) : (path (n + 1)).diameter = n := sorry

theorem isConnected_cycle (n : ℕ) : (cycle (n + 1)).IsConnected := sorry

theorem E_cycle (n : ℕ) : (cycle (n + 3)).E = n + 3 := sorry

theorem not_isAcyclic_cycle (n : ℕ) : ¬(cycle (n + 3)).IsAcyclic := sorry

theorem diameter_cycle (n : ℕ) : (cycle (n + 1)).diameter = (n + 1) / 2 := sorry

theorem indepNum_cycle (n : ℕ) : (cycle (n + 3)).indepNum = (n + 3) / 2 := sorry

/-! ### Disjoint unions and joins -/

theorem E_disjUnion : (disjUnion G H).E = G.E + H.E := sorry

theorem indepNum_disjUnion : (disjUnion G H).indepNum = G.indepNum + H.indepNum := sorry

theorem cliqueNum_disjUnion :
    (disjUnion G H).cliqueNum = max G.cliqueNum H.cliqueNum := sorry

/-- The disjoint union is commutative up to isomorphism — which is exactly what equality in
`IsoGraph` means. -/
theorem disjUnion_comm : Nonempty (disjUnion G H ≃cg disjUnion H G) := sorry

theorem disjUnion_assoc (K : CGraph) :
    Nonempty (disjUnion (disjUnion G H) K ≃cg disjUnion G (disjUnion H K)) := sorry

theorem not_isConnected_disjUnion (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) :
    ¬(disjUnion G H).IsConnected := sorry

theorem E_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).E = G.E + H.E + Fintype.card G.V * Fintype.card H.V := sorry

theorem isConnected_join [DecidableEq G.V] [DecidableEq H.V]
    (hG : 0 < Fintype.card G.V) (hH : 0 < Fintype.card H.V) : (join G H).IsConnected := sorry

theorem cliqueNum_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).cliqueNum = G.cliqueNum + H.cliqueNum := sorry

theorem indepNum_join [DecidableEq G.V] [DecidableEq H.V] :
    (join G H).indepNum = max G.indepNum H.indepNum := sorry

/-! ### Bipartite and multipartite graphs -/

theorem E_bipartite (m n : ℕ) : (bipartite m n).E = m * n := sorry

theorem indepNum_bipartite (m n : ℕ) : (bipartite m n).indepNum = max m n := sorry

theorem cliqueNum_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).cliqueNum = 2 := sorry

theorem isConnected_bipartite (m n : ℕ) : (bipartite (m + 1) (n + 1)).IsConnected := sorry

theorem diameter_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).diameter = 2 := sorry

theorem card_completeMultipartite (ds : List ℕ) :
    Fintype.card (completeMultipartite ds).V = ds.sum := by
  simp only [completeMultipartite, card_compl, card_sigmaUnion, card_complete]
  rw [← Fin.sum_ofFn, List.ofFn_get]

theorem indepNum_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).indepNum = (ds.max?).getD 0 := sorry

theorem card_star (n : ℕ) : Fintype.card (star n).V = 1 + n := by
  simp [star]

theorem E_star (n : ℕ) : (star n).E = n := by
  simp [star, E_bipartite]

/-! ### Products -/

theorem E_cartesianProduct [DecidableEq G.V] [DecidableEq H.V] :
    (cartesianProduct G H).E = Fintype.card G.V * H.E + Fintype.card H.V * G.E := sorry

theorem E_tensorProduct [DecidableEq G.V] [DecidableEq H.V] :
    (tensorProduct G H).E = 2 * G.E * H.E := sorry

theorem indepNum_lexProduct [DecidableEq G.V] [DecidableEq H.V] :
    (lexProduct G H).indepNum = G.indepNum * H.indepNum := sorry

theorem cliqueNum_strongProduct [DecidableEq G.V] [DecidableEq H.V] :
    (strongProduct G H).cliqueNum = G.cliqueNum * H.cliqueNum := sorry

theorem card_hypercube (n : ℕ) : Fintype.card (hypercube n).V = 2 ^ n := by
  simp [hypercube]

/-! ### Kneser, line and Mycielskian -/

theorem card_kneser (n k : ℕ) : Fintype.card (kneser n k).V = n.choose k := by
  simp [kneser, Fintype.card_finset_len]

theorem card_lineGraph [DecidableEq G.V] : Fintype.card (lineGraph G).V = G.E := by
  rw [E, SimpleGraph.edgeFinset_card]
  exact Fintype.card_congr' rfl

theorem E_lineGraph [DecidableEq G.V] :
    (lineGraph G).E = (∑ v : G.V, (G.toSimple.degree v).choose 2) := sorry

@[simp] theorem card_mycielskian [DecidableEq G.V] :
    Fintype.card (mycielskian G).V = 2 * Fintype.card G.V + 1 := by
  simp [mycielskian, Fintype.card_option, Fintype.card_sum, two_mul]

theorem E_mycielskian [DecidableEq G.V] :
    (mycielskian G).E = 3 * G.E + Fintype.card G.V := sorry

/-- The Petersen graph, as `K(5,2)`. -/
theorem card_petersen : Fintype.card (kneser 5 2).V = 10 := by
  simpa using card_kneser 5 2

end Invariants

end CGraph
