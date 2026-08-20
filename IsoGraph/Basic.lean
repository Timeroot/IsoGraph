import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import IsoGraph.Canon.Spec
import IsoGraph.ForMathlib.FinEnum
import IsoGraph.ForMathlib.List

/-!
# Graphs up to isomorphism

This file follows `isograph_draft.txt`: a bundled, computable graph type `CGraph`, its
isomorphisms, and the quotient `IsoGraph` of graphs up to isomorphism.

Everything that has to be lifted through the quotient — in particular the canonical
representative `IsoGraph.toCGraph` — rests on the invariance of the canonical labelling
algorithm under renaming vertices (`IsoGraph.Canon.canonAdj_relabel`, in
`IsoGraph.Canon.Spec`).
-/

/-- Computable graphs with bundled vertex type.

The vertex type comes with a `FinEnum` instance rather than a `Fintype` one: not just "there are
finitely many vertices" but "here is the list of them, in order, and here is the bijection with
`Fin n`".  That is what every algorithm here actually needs — an index for each vertex, chosen
without appealing to `Classical.choice` — and it subsumes the `DecidableEq V` that the
complement, the products and the line graph all ask for, since `FinEnum` bundles one.

The price is that `FinEnum` is not a subsingleton: two graphs with the same vertices and the same
edges but different enumerations of those vertices are different `CGraph`s.  They are of course
isomorphic, and `IsoGraph` — the quotient — does not see the difference. -/
structure CGraph where
  /-- The vertex type. -/
  V : Type
  /-- The vertices, enumerated.  Bundled rather than asked for as an instance argument: every
  construction that has to ask "is this the same vertex?" — the complement, the products, the
  line graph — needs a `DecidableEq`, and every algorithm needs an indexing. -/
  [enum : FinEnum V]
  /-- The adjacency relation, as a decidable predicate. -/
  Adj : V → V → Bool
  /-- Adjacency is symmetric. -/
  symm x y : Adj x y = Adj y x
  /-- There are no loops. -/
  loopless x : ¬Adj x x

attribute [instance] CGraph.enum

/-- The number of vertices.  `FinEnum.card` rather than `FinEnum.card`: the enumeration knows the
number, so for a graph on `Fin n` this is `n` by `rfl`, where the `Fintype` route computes the
length of a mapped `Finset`. -/
abbrev CGraph.card (G : CGraph) : ℕ := FinEnum.card G.V

@[simp] theorem CGraph.fintypeCard (G : CGraph) : Fintype.card G.V = FinEnum.card G.V :=
  FinEnum.card_eq_fintypeCard.symm

/-- Two `CGraph`s with the same vertex type, the same enumeration of it and the same adjacency
function are equal; the remaining fields are propositions.  The enumeration is an `autoParam`
because at almost every call site the two graphs are built from the same one. -/
theorem CGraph.ext' {G H : CGraph} (hV : G.V = H.V) (hA : HEq G.Adj H.Adj)
    (he : HEq G.enum H.enum := by rfl) : G = H := by
  obtain ⟨V₁, A₁, s₁, l₁⟩ := G
  obtain ⟨V₂, A₂, s₂, l₂⟩ := H
  simp only at hV hA he
  subst hV
  cases he
  cases hA
  rfl

/-- The enumerations of `Fin m` and `Fin n` agree as soon as `m = n`; this is the side condition
of `CGraph.ext'` for two graphs that have both been relabelled onto an initial segment. -/
theorem CGraph.heq_enum_fin {m n : ℕ} (h : m = n) :
    HEq (FinEnum.instFin m) (FinEnum.instFin n) := by subst h; rfl

/-! ## `CGraph` is equivalent to `SimpleGraph` -/

/-- The `SimpleGraph` underlying a `CGraph`. -/
def CGraph.toSimple (G : CGraph) : SimpleGraph G.V where
  Adj x y := G.Adj x y
  symm := by intro x y h; show G.Adj y x = true; rw [← G.symm x y]; exact h
  loopless := ⟨fun x h => G.loopless x h⟩

@[simp] theorem CGraph.toSimple_adj (G : CGraph) (x y : G.V) :
    G.toSimple.Adj x y ↔ G.Adj x y = true := Iff.rfl

instance (G : CGraph) : DecidableRel G.toSimple.Adj :=
  fun x y => decidable_of_iff (G.Adj x y = true) Iff.rfl

/-- A decidable `SimpleGraph` as a `CGraph`. -/
def SimpleGraph.toCGraph {V : Type} [FinEnum V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    CGraph where
  V := V
  Adj x y := decide (G.Adj x y)
  symm x y := by simp [G.adj_comm]
  loopless x := by simp

/-- A `CGraph` is an enumerated type together with a `SimpleGraph` on it.  Unlike the `Fintype`
version this is an honest bijection with nothing to quotient by: both sides carry the
enumeration as data. -/
noncomputable def CGraph.simpleEquiv : CGraph ≃ Σ V, FinEnum V × SimpleGraph V where
  toFun G := ⟨G.V, G.enum, G.toSimple⟩
  invFun := fun ⟨_, e, G⟩ ↦ open Classical in @SimpleGraph.toCGraph _ e G (Classical.decRel _)
  left_inv G := by
    refine CGraph.ext' rfl (heq_of_eq ?_)
    funext x y
    simp [SimpleGraph.toCGraph, CGraph.toSimple]
  right_inv := by
    rintro ⟨V, e, G⟩
    have hG : (open Classical in @SimpleGraph.toCGraph _ e G (Classical.decRel _)).toSimple = G := by
      ext x y
      simp [SimpleGraph.toCGraph, CGraph.toSimple]
    simp only [hG]
    rfl

namespace CGraph

variable (G H I : CGraph)

/-- A graph homomorphism. -/
abbrev Hom (G H : CGraph) :=
  RelHom (G.Adj · ·) (H.Adj · ·)

/-- A graph embedding. -/
abbrev Embedding (G H : CGraph) :=
  RelEmbedding (G.Adj · ·) (H.Adj · ·)

/-- A graph isomorphism. -/
abbrev Iso (G H : CGraph) :=
  RelIso (G.Adj · ·) (H.Adj · ·)

@[inherit_doc] infixl:50 " →cg " => Hom
@[inherit_doc] infixl:50 " ↪cg " => Embedding
@[inherit_doc] infixl:50 " ≃cg " => Iso

theorem hom_eq : (G →cg H) = (G.toSimple →g H.toSimple) := by
  rfl

theorem embedding_eq : (G ↪cg H) = (G.toSimple ↪g H.toSimple) := by
  rfl

theorem iso_eq : (G ≃cg H) = (G.toSimple ≃g H.toSimple) := by
  rfl

/-- A `CGraph` isomorphism *is* an isomorphism of the underlying `SimpleGraph`s (`iso_eq` is
`rfl`); this is the coercion that lets Mathlib's graph API be used directly. -/
def Iso.toSimpleIso {G H : CGraph} (i : G ≃cg H) : G.toSimple ≃g H.toSimple := i

theorem Iso.card_eq (i : G ≃cg H) : FinEnum.card G.V = FinEnum.card H.V := by
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact Fintype.card_congr i.toEquiv

/-- An isomorphism transports adjacency, as `Bool`s. -/
theorem Iso.adj_eq {G H : CGraph} (i : G ≃cg H) (x y : G.V) : H.Adj (i x) (i y) = G.Adj x y :=
  Bool.eq_iff_iff.2 i.map_rel_iff

example (f : G ≃cg H) (g : H ≃cg I) : G ≃cg I := f.trans g

instance isoSetoid : Setoid CGraph where
  r G H := Nonempty (G ≃cg H)
  iseqv := by
    refine ⟨fun _ ↦ ⟨RelIso.refl _⟩, ?_, ?_⟩
    · rintro _ _ ⟨i⟩
      exact ⟨i.symm⟩
    · rintro _ _ _ ⟨i⟩ ⟨j⟩
      exact ⟨i.trans j⟩

end CGraph

/-- A graph, up to isomorphism. -/
def IsoGraph :=
  Quotient CGraph.isoSetoid

/-- Number of vertices of an `IsoGraph`. -/
def IsoGraph.V (G : IsoGraph) : ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) (fun g ↦ FinEnum.card g.V) (fun _ _ ⟨i⟩ ↦ CGraph.Iso.card_eq _ _ i) G

/-! ## The canonical labelling

The algorithm of `IsoGraph.Canon.Algorithm` works on `{0, …, n-1}`, so running it on a `CGraph` needs a
listing of the vertices.  A `Fintype` instance is exactly that: underneath, it is a `Multiset`,
i.e. a `List` up to permutation.  So the canonical form is computed from a `List G.V` and then
lifted through `Quot`; the side condition of the lift is that a different listing of the same
vertices gives the same answer, which is precisely invariance of the algorithm under renaming.

Nothing here chooses an equivalence `G.V ≃ Fin n` by choice, so `CGraph.canonicalize` is
**computable**. -/

namespace CGraph

/-- The adjacency of `G` read along an *array* of its vertices.

The array is a parameter rather than something this definition builds, because the compiler
η-expands every function-typed definition: a `let a := l.toArray` in the body of a
`… → Fin _ → Fin _ → Bool` would be re-run on every single adjacency query. -/
def adjOfArray (G : CGraph) (a : Array G.V) (i j : Fin a.size) : Bool :=
  G.Adj a[i] a[j]

/-- The adjacency of `G` read along a listing `l` of its vertices.  This is the specification;
what actually runs is `adjOfArray` on `l.toArray`, and the two are definitionally equal. -/
def adjOfList (G : CGraph) (l : List G.V) (i j : Fin l.length) : Bool :=
  G.Adj (l.get i) (l.get j)

@[simp] theorem adjOfList_apply (G : CGraph) (l : List G.V) (i j : Fin l.length) :
    G.adjOfList l i j = G.Adj (l.get i) (l.get j) := rfl

/-- The canonical form of `G` computed along an array of its vertices, on `Fin (card G.V)`. -/
def canonOfArray (G : CGraph) (a : Array G.V) :
    IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  (IsoGraph.Canon.canonMatrix a.size (G.adjOfArray a)).reindex (FinEnum.card G.V)

/-- The same, off a tabulated adjacency: the `n × n` array is filled once, and every query the
search makes is then an array read rather than a call to `G.Adj`.

This is what runs — `canonOfArray_eq_tab` below is a `@[csimp]` lemma — while `canonOfArray`
stays the definition everything is proved about.  Measured by `CacheBench.lean` (`canon-tab`,
`canon-mass`), best of five interleaved rounds, in milliseconds:

| job                                   | raw  | tabulated |
| ------------------------------------- | ---- | --------- |
| canonical form of the Balaban 10-cage | 24   | 9         |
| canonical form of the Tutte graph     | 9    | 6         |
| canonical form of the Kneser graph `K(7,3)` | 5 | 3      |
| canonical form of `K₄₀`               | 21   | 22        |
| 20000 labelled graphs on six vertices | 968  | 933       |

The win is the whole of what a query costs, because the search asks far more than `n²` times.
Nothing gets slower: a host whose adjacency is already a formula is a wash, and so is a sweep of
graphs small enough that the fill is a real fraction of the work. -/
def canonOfArrayTab (G : CGraph) (a : Array G.V) :
    IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  (IsoGraph.Canon.canonMatrix a.size
    (IsoGraph.Canon.matLookup a.size
      (IsoGraph.Canon.adjArray a.size (G.adjOfArray a)))).reindex (FinEnum.card G.V)

@[csimp] theorem canonOfArray_eq_tab : @canonOfArray = @canonOfArrayTab := by
  funext G a
  rw [canonOfArrayTab, IsoGraph.Canon.matLookup_adjArray_eq, canonOfArray]

/-- **The canonical form of `G` relative to the listing `l`**: the canonical adjacency matrix,
on `Fin (FinEnum.card G.V)`.

The size of the index set is `FinEnum.card G.V` rather than `l.length` for a reason: the type of
the result must not mention `l`, or the quotient lift below would not typecheck.  For a listing
that really does enumerate `G.V` the two agree, and `reindex` is then a no-op; for any other list
the matrix is padded or truncated with `false`, which the lift never sees. -/
def canonOfList (G : CGraph) (l : List G.V) : IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  G.canonOfArray l.toArray

theorem canonOfList_eq (G : CGraph) (l : List G.V) :
    G.canonOfList l =
      (IsoGraph.Canon.canonMatrix l.length (G.adjOfList l)).reindex (FinEnum.card G.V) := rfl

/-- The canonical labelling of `G` relative to the listing `l`: canonical position `i` is occupied
by the vertex `G.labellingOfList l i`.

Specification only — being function-typed, every query re-runs the search. -/
def labellingOfList (G : CGraph) (l : List G.V) (i : Fin l.length) : G.V :=
  l.get (IsoGraph.Canon.canonPerm l.length (G.adjOfList l) i)

theorem canonOfList_adj_apply (G : CGraph) (l : List G.V) (x y : Fin (FinEnum.card G.V))
    (hx : x.1 < l.length) (hy : y.1 < l.length) :
    (G.canonOfList l).adj x y =
      G.Adj (G.labellingOfList l ⟨x.1, hx⟩) (G.labellingOfList l ⟨y.1, hy⟩) :=
  IsoGraph.Canon.oracleOfFin_apply
    (IsoGraph.Canon.canonAdj l.length (G.adjOfList l)) hx hy

/-- **The listing does not matter.**  This is the side condition of the quotient lift below, and
the only place where invariance of the algorithm under renaming is used. -/
theorem canonOfList_perm (G : CGraph) {l₁ l₂ : List G.V} (h : List.Perm l₁ l₂) :
    G.canonOfList l₁ = G.canonOfList l₂ := by
  obtain ⟨σ, hσ⟩ := h.exists_finEquiv
  rw [canonOfList_eq, canonOfList_eq]
  refine IsoGraph.Canon.canonMatrix_reindex_congr h.length_eq σ (fun a b ↦ ?_) _
  rw [adjOfList_apply, adjOfList_apply, hσ, hσ]

/-- **The canonical form of `G`**: `G.canon.adj i j` is the entry at canonical positions `i`, `j`
of the canonical adjacency matrix.

The listing of the vertices is the one the `FinEnum` instance carries — no choice is involved, so
this computes.  Forcing it runs the search once; each `adj` query afterwards is `O(1)`. -/
def canon (G : CGraph) : IsoGraph.Canon.AdjMatrix (FinEnum.card G.V) :=
  G.canonOfList (FinEnum.toList G.V)

/-- The listing of `G.V` that comes out of the enumeration. -/
theorem toList_nodup (G : CGraph) : (FinEnum.toList G.V).Nodup := FinEnum.nodup_toList

theorem mem_toList (G : CGraph) (v : G.V) : v ∈ FinEnum.toList G.V := FinEnum.mem_toList v

@[simp] theorem length_toList (G : CGraph) :
    (FinEnum.toList G.V).length = FinEnum.card G.V := by
  simp [FinEnum.toList]

/-- Any other listing of the same vertices gives the same canonical form. -/
theorem canon_eq_ofList (G : CGraph) {l : List G.V} (hl : l.Perm (FinEnum.toList G.V)) :
    G.canon = G.canonOfList l := (G.canonOfList_perm hl).symm

theorem canonOfList_adj_symm (G : CGraph) (l : List G.V) (x y : Fin (FinEnum.card G.V)) :
    (G.canonOfList l).adj x y = (G.canonOfList l).adj y x :=
  IsoGraph.Canon.oracleOfFin_comm (f := IsoGraph.Canon.canonAdj l.length (G.adjOfList l))
    (fun i j ↦ IsoGraph.Canon.canonAdj_comm (adj := G.adjOfList l) (fun _ _ ↦ G.symm _ _) i j)
    x.1 y.1

theorem canonOfList_adj_self (G : CGraph) (l : List G.V) (x : Fin (FinEnum.card G.V)) :
    (G.canonOfList l).adj x x = false :=
  IsoGraph.Canon.oracleOfFin_irrefl (f := IsoGraph.Canon.canonAdj l.length (G.adjOfList l))
    (fun i ↦ by
      simpa using
        IsoGraph.Canon.canonAdj_irrefl (adj := G.adjOfList l) (fun k ↦ G.loopless (l.get k)) i)
    x.1

theorem canon_adj_symm (G : CGraph) (x y : Fin (FinEnum.card G.V)) :
    G.canon.adj x y = G.canon.adj y x :=
  G.canonOfList_adj_symm _ x y

@[simp] theorem canon_adj_self (G : CGraph) (x : Fin (FinEnum.card G.V)) :
    G.canon.adj x x = false :=
  G.canonOfList_adj_self _ x

theorem canon_loopless (G : CGraph) (x : Fin (FinEnum.card G.V)) : ¬G.canon.adj x x := by
  simp

/-! ### Invariance under isomorphism -/

/-- A listing of *all* the vertices, without repeats, is an enumeration of the vertex type. -/
noncomputable def equivOfList (G : CGraph) {l : List G.V} (hn : l.Nodup) (hc : ∀ v, v ∈ l) :
    Fin l.length ≃ G.V :=
  Equiv.ofBijective _ (List.Nodup.getBijectionOfForallMemList l hn hc).2

@[simp] theorem equivOfList_apply (G : CGraph) {l : List G.V} (hn : l.Nodup) (hc : ∀ v, v ∈ l)
    (i : Fin l.length) : G.equivOfList hn hc i = l.get i := rfl

/-- Isomorphic graphs, listed however you like, have the same canonical form — entrywise, since
the two matrices live over index sets of provably but not definitionally equal size. -/
theorem canonOfList_adj_eq_of_iso {G H : CGraph} (i : G ≃cg H) {l : List G.V} {m : List H.V}
    (hnl : l.Nodup) (hcl : ∀ v, v ∈ l) (hnm : m.Nodup) (hcm : ∀ w, w ∈ m)
    (x y : Fin (FinEnum.card G.V)) (x' y' : Fin (FinEnum.card H.V)) (hx : x'.1 = x.1)
    (hy : y'.1 = y.1) :
    (G.canonOfList l).adj x y = (H.canonOfList m).adj x' y' := by
  set σ : Fin l.length ≃ Fin m.length :=
    (G.equivOfList hnl hcl).trans (i.toEquiv.trans (H.equivOfList hnm hcm).symm) with hσdef
  have hlen : l.length = m.length := by simpa using Fintype.card_congr σ
  have key : ∀ a : Fin l.length, m.get (σ a) = i (l.get a) := fun a ↦
    (H.equivOfList hnm hcm).apply_symm_apply _
  show (IsoGraph.Canon.canonMatrix l.length (G.adjOfList l)).get x.1 y.1 =
    (IsoGraph.Canon.canonMatrix m.length (H.adjOfList m)).get x'.1 y'.1
  rw [hx, hy]
  refine IsoGraph.Canon.canonMatrix_get_congr hlen σ (fun a b ↦ ?_) x.1 y.1
  rw [adjOfList_apply, adjOfList_apply, key, key]
  exact CGraph.Iso.adj_eq i _ _

/-- **Isomorphism invariance of the canonical form.**  This is the statement that makes the
quotient work: the two matrices agree entry by entry, once their index sets are identified along
`FinEnum.card G.V = FinEnum.card H.V`. -/
theorem canon_adj_eq_of_iso {G H : CGraph} (i : G ≃cg H) (x y : Fin (FinEnum.card G.V)) :
    G.canon.adj x y =
      H.canon.adj (IsoGraph.Canon.finEq (CGraph.Iso.card_eq G H i) x)
        (IsoGraph.Canon.finEq (CGraph.Iso.card_eq G H i) y) := by
  exact canonOfList_adj_eq_of_iso i G.toList_nodup G.mem_toList H.toList_nodup
    H.mem_toList x y _ _ rfl rfl

/-- The same statement, as a heterogeneous equality of matrices. -/
theorem canon_heq_of_iso {G H : CGraph} (i : G ≃cg H) : HEq G.canon H.canon :=
  IsoGraph.Canon.AdjMatrix.heq_of_adj (CGraph.Iso.card_eq G H i) (canon_adj_eq_of_iso i)

/-- The canonical labelling is appropriately invariant under isomorphism: reading either graph
through its own canonical labelling gives the *same* adjacency matrix. -/
theorem Iso.canonicalLabelling_eq {G H : CGraph} (i : G ≃cg H) : HEq G.canon H.canon :=
  canon_heq_of_iso i

end CGraph

/-- `HEq` of two adjacency functions on `Fin m` and `Fin n`, from `m = n` and pointwise
agreement. -/
theorem IsoGraph.Canon.heq_adj {m n : ℕ} (h : m = n) {f : Fin m → Fin m → Bool}
    {g : Fin n → Fin n → Bool} (hfg : ∀ x y, f x y = g (finEq h x) (finEq h y)) : HEq f g := by
  subst h
  exact heq_of_eq (funext fun x ↦ funext fun y ↦ hfg x y)

/-! ## A canonical representative, and the quotient -/

namespace CGraph

/-- The graph on `Fin n` given by an adjacency matrix.

`M` is a parameter, so it is evaluated once by the caller and then captured; this is what keeps
`canonicalize` from re-running the search on every adjacency query. -/
def ofMatrix (n : ℕ) (M : IsoGraph.Canon.AdjMatrix n)
    (hsymm : ∀ i j, M.adj i j = M.adj j i) (hloop : ∀ i, ¬M.adj i i) : CGraph where
  V := Fin n
  Adj := M.adj
  symm := hsymm
  loopless := hloop

/-- The canonical representative of the isomorphism class of `G`: the same graph, relabelled onto
`Fin (FinEnum.card G.V)` so that its adjacency matrix is the canonical one.

Computable, and the search runs exactly once per `canonicalize`. -/
def canonicalize (G : CGraph) : CGraph :=
  ofMatrix (FinEnum.card G.V) G.canon G.canon_adj_symm G.canon_loopless

@[simp] theorem canonicalize_V (G : CGraph) : G.canonicalize.V = Fin (FinEnum.card G.V) := rfl

@[simp] theorem canonicalize_adj (G : CGraph) (i j : Fin (FinEnum.card G.V)) :
    G.canonicalize.Adj i j = G.canon.adj i j := rfl

/-- Isomorphic graphs have *equal* canonical representatives.  This is what makes `IsoGraph`
usable: it turns the isomorphism relation into equality. -/
theorem canonicalize_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.canonicalize = H.canonicalize := by
  have hc : FinEnum.card G.V = FinEnum.card H.V := CGraph.Iso.card_eq G H i
  refine CGraph.ext' (show Fin (FinEnum.card G.V) = Fin (FinEnum.card H.V) by rw [hc])
    (IsoGraph.Canon.heq_adj hc (canon_adj_eq_of_iso i)) (CGraph.heq_enum_fin hc)

/-- The canonical representative really is isomorphic to the original graph. -/
theorem nonempty_iso_canonicalize (G : CGraph) : Nonempty (G ≃cg G.canonicalize) := by
  set l : List G.V := FinEnum.toList G.V with hldef
  have hlen : l.length = FinEnum.card G.V := G.length_toList
  let σ := IsoGraph.Canon.canonPerm l.length (G.adjOfList l)
  let φ : Fin (FinEnum.card G.V) ≃ G.V :=
    (IsoGraph.Canon.finEq hlen.symm).trans
      (σ.trans (G.equivOfList G.toList_nodup G.mem_toList))
  have key : ∀ x y : Fin (FinEnum.card G.V), G.canonicalize.Adj x y = G.Adj (φ x) (φ y) := by
    intro x y
    rw [canonicalize_adj, show G.canon = G.canonOfList l from rfl,
      G.canonOfList_adj_apply l x y (by omega) (by omega)]
    rfl
  refine ⟨⟨φ.symm, fun {a b} ↦ ?_⟩⟩
  show (G.canonicalize.Adj (φ.symm a) (φ.symm b) = true) ↔ (G.Adj a b = true)
  rw [key, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A choice of isomorphism onto the canonical representative.  Only the *graph* has to be
computable; picking one of the (possibly many) isomorphisms onto it does not. -/
noncomputable def isoCanonicalize (G : CGraph) : G ≃cg G.canonicalize :=
  Classical.choice G.nonempty_iso_canonicalize

/-- **Equal canonical representatives, and isomorphism, are the same thing.**  One direction is
`canonicalize_eq_of_iso`; the other is immediate from the fact that a graph is isomorphic to its
representative.  This is what lets isomorphism be tested by comparing canonical forms. -/
theorem canonicalize_eq_iff {G H : CGraph} :
    G.canonicalize = H.canonicalize ↔ Nonempty (G ≃cg H) := by
  refine ⟨fun h ↦ ?_, fun ⟨i⟩ ↦ canonicalize_eq_of_iso i⟩
  obtain ⟨iG⟩ := G.nonempty_iso_canonicalize
  obtain ⟨iH⟩ := H.nonempty_iso_canonicalize
  refine ⟨iG.trans ?_⟩
  rw [h]
  exact iH.symm

end CGraph

/-- A canonical path out of the quotient type. -/
def IsoGraph.toCGraph (G : IsoGraph) : CGraph :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.canonicalize (fun _ _ ⟨i⟩ ↦ CGraph.canonicalize_eq_of_iso i) G

@[simp] theorem IsoGraph.toCGraph_mk (G : CGraph) :
    IsoGraph.toCGraph (Quotient.mk _ G) = G.canonicalize := rfl

/-- `IsoGraph.toCGraph` is a section of the quotient map: it picks a representative of the class.
Together with `Quotient.sound` this gives an *efficient* `DecidableEq` for `IsoGraph`, by
comparing canonical forms. -/
theorem IsoGraph.mk_toCGraph (G : IsoGraph) : Quotient.mk _ G.toCGraph = G := by
  induction G using Quotient.inductionOn with
  | h g => exact Quotient.sound ⟨g.isoCanonicalize.symm⟩

-- The invariants of a `CGraph` / `IsoGraph` (`indepNum`, `cliqueNum`, `E`, `degSequence`,
-- `IsConnected`, `IsAcyclic`, `diameter`, …) live in `IsoGraph/Invariants/Basic.lean`, and the ways
-- of building graphs (`empty`, `complete`, `path`, products, …) in
-- `IsoGraph/Core/Defs.lean`.
