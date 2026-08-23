import IsoGraph.Core.Defs

/-!
# Isomorphism certificates

An isomorphism between two concrete graphs is a bijection of their vertex sets that carries
adjacency to adjacency.  Finding one is a search; *checking* one is not, and this file is the
checker: a pair of lists of natural numbers `p`, `q` describing the bijection and its inverse at
the level of the enumerations, a `Bool`-valued predicate `isoListOK` saying that they do describe
one, and `isoOfList`, which turns a proof that the predicate holds into the isomorphism itself.

The point of the indirection is that `isoListOK G H p q = true` is a closed computation, so the
whole certificate is discharged by `decide` — no `native_decide`, no trusted compiler.  What
produces the lists is the `generate_graph_iso` tactic, which runs a canonical labelling of both
graphs in the elaborator, where the search costs nothing to the kernel.

## The shape of a certificate

Vertices are identified with their positions in `FinEnum.toList`, so a map `G.V → H.V` is a
function `{0, …, |V(G)|-1} → {0, …, |V(H)|-1}`, and a list of naturals is exactly that.  `permOK`
checks that `p` and `q` are mutually inverse maps between the two ranges — pure arithmetic, no
vertices involved — and `adjOK` checks that `p` preserves adjacency, which is the only part that
touches the graphs.
-/

set_option autoImplicit false

namespace CGraph
namespace Decompose

/-! ## Vertices and their indices -/

/-- The index of a vertex: its position in the enumeration of its graph's vertex type. -/
def idxOf {G : CGraph} (v : G.V) : ℕ := (FinEnum.equiv v : Fin (FinEnum.card G.V)).val

theorem idxOf_lt {G : CGraph} (v : G.V) : idxOf v < FinEnum.card G.V := (FinEnum.equiv v).isLt

/-- The vertex of `H` at index `k`, when there is one. -/
def vtxAt (H : CGraph) (k : ℕ) : Option H.V :=
  if h : k < FinEnum.card H.V then some (FinEnum.equiv.symm ⟨k, h⟩) else none

/-! ## The checks -/

/-- `p` and `q` are mutually inverse maps `{0, …, m-1} → {0, …, n-1}`.

Out-of-range lookups are given a default that fails the range test — `n` for `p`, `m` for `q` —
so a list that is too short is rejected rather than silently padded. -/
def permOK (m n : ℕ) (p q : List ℕ) : Bool :=
  (List.range m).all (fun i ↦ p.getD i n < n && q.getD (p.getD i n) m == i) &&
    (List.range n).all (fun j ↦ q.getD j m < m && p.getD (q.getD j m) n == j)

/-- The vertices of `G` paired with their images in `H`.

A parameter of `adjOKAux` rather than something it recomputes: the adjacency check is a double
loop, and the kernel would otherwise redo the whole pairing once per row. -/
def pairing (G H : CGraph) (p : List ℕ) : List (G.V × Option H.V) :=
  (FinEnum.toList G.V).map fun v ↦ (v, vtxAt H (p.getD (idxOf v) (FinEnum.card H.V)))

/-- Adjacency is carried across the pairing, in both directions at once: the two `Bool`s agree. -/
def adjOKAux (G H : CGraph) (l : List (G.V × Option H.V)) : Bool :=
  l.all fun uo ↦ l.all fun vo ↦
    match uo.2, vo.2 with
    | some a, some b => H.Adj a b == G.Adj uo.1 vo.1
    | _, _ => false

/-- `p` carries the adjacency of `G` to that of `H`. -/
def adjOK (G H : CGraph) (p : List ℕ) : Bool := adjOKAux G H (pairing G H p)

/-- **The certificate.**  `p` and `q` are mutually inverse index maps and `p` preserves adjacency;
that is, `p` describes an isomorphism `G ≃cg H` with inverse `q`. -/
def isoListOK (G H : CGraph) (p q : List ℕ) : Bool :=
  permOK (FinEnum.card G.V) (FinEnum.card H.V) p q && adjOK G H p

/-! ## Reading a certificate -/

section Perm

variable {m n : ℕ} {p q : List ℕ}

theorem permOK_fwd (h : permOK m n p q = true) {i : ℕ} (hi : i < m) :
    p.getD i n < n ∧ q.getD (p.getD i n) m = i := by
  rw [permOK, Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.1 i (List.mem_range.2 hi)
  simpa using this

theorem permOK_bwd (h : permOK m n p q = true) {j : ℕ} (hj : j < n) :
    q.getD j m < m ∧ p.getD (q.getD j m) n = j := by
  rw [permOK, Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.2 j (List.mem_range.2 hj)
  simpa using this

/-- The bijection `{0, …, m-1} ≃ {0, …, n-1}` described by a valid pair of lists. -/
def permEquiv (h : permOK m n p q = true) : Fin m ≃ Fin n where
  toFun i := ⟨p.getD i.1 n, (permOK_fwd h i.2).1⟩
  invFun j := ⟨q.getD j.1 m, (permOK_bwd h j.2).1⟩
  left_inv i := Fin.ext (permOK_fwd h i.2).2
  right_inv j := Fin.ext (permOK_bwd h j.2).2

@[simp] theorem permEquiv_apply (h : permOK m n p q = true) (i : Fin m) :
    (permEquiv h i : ℕ) = p.getD i.1 n := rfl

end Perm

variable {G H : CGraph} {p q : List ℕ}

/-- The bijection of vertex sets described by a valid pair of lists. -/
def vEquiv (h : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true) : G.V ≃ H.V :=
  FinEnum.equiv.trans ((permEquiv h).trans FinEnum.equiv.symm)

theorem vtxAt_vEquiv (h : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true) (v : G.V) :
    vtxAt H (p.getD (idxOf v) (FinEnum.card H.V)) = some (vEquiv h v) := by
  rw [vtxAt, dif_pos (permOK_fwd h (idxOf_lt v)).1]
  rfl

theorem adj_vEquiv (hp : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true)
    (ha : adjOK G H p = true) (u v : G.V) : H.Adj (vEquiv hp u) (vEquiv hp v) = G.Adj u v := by
  have hmem : ∀ w : G.V, (w, vtxAt H (p.getD (idxOf w) (FinEnum.card H.V))) ∈ pairing G H p :=
    fun w ↦ List.mem_map_of_mem (FinEnum.mem_toList w)
  rw [adjOK, adjOKAux] at ha
  have hrow := List.all_eq_true.1 ha _ (hmem u)
  have hcell := List.all_eq_true.1 hrow _ (hmem v)
  rw [vtxAt_vEquiv hp u, vtxAt_vEquiv hp v] at hcell
  simpa using hcell

/-- **An isomorphism from a checked certificate.** -/
def isoOfList (G H : CGraph) (p q : List ℕ) (h : isoListOK G H p q = true) : G ≃cg H :=
  have hp : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true := by
    rw [isoListOK, Bool.and_eq_true] at h; exact h.1
  have ha : adjOK G H p = true := by
    rw [isoListOK, Bool.and_eq_true] at h; exact h.2
  isoOfAdj (vEquiv hp) (adj_vEquiv hp ha)

/-- The same certificate, read on the quotient: two graphs with a certificate between them are
*equal* as `IsoGraph`s. -/
theorem mk_eq_mk_of_isoListOK {G H : CGraph} {p q : List ℕ} (h : isoListOK G H p q = true) :
    (Quotient.mk CGraph.isoSetoid G : IsoGraph) = Quotient.mk CGraph.isoSetoid H :=
  Quotient.sound ⟨isoOfList G H p q h⟩

end Decompose
end CGraph
