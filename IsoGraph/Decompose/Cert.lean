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

theorem vtxAt_eq_some (H : CGraph) {k : ℕ} (h : k < FinEnum.card H.V) :
    vtxAt H k = some (FinEnum.equiv.symm ⟨k, h⟩) := dite_eq_left h

/-! ## The checks -/

/-- `p` and `q` are mutually inverse maps `{0, …, m-1} → {0, …, n-1}`.

Out-of-range lookups are given a default that fails the range test — `n` for `p`, `m` for `q` —
so a list that is too short is rejected rather than silently padded. -/
def permOK (m n : ℕ) (p q : List ℕ) : Bool :=
  (List.range m).all (fun i ↦ p.getD i n < n && q.getD (p.getD i n) m == i) &&
    (List.range n).all (fun j ↦ q.getD j m < m && p.getD (q.getD j m) n == j)

/-- The vertices of `G` paired with their images in `H`, or `none` if an index is out of range.

Built once and handed to `adjOKAux` rather than recomputed there: the adjacency check is a double
loop, and the kernel would otherwise redo the whole pairing once per row.  The range check is
done here too, once per vertex, so that the quadratic loop below sees a pair of vertices and not
a pair of `Option`s.

The recursion is over the *indices* and not over `FinEnum.toList G.V`, because a vertex does not
know its own index: `idxOf` is `List.idxOf` for every enumeration built from a list, so pairing a
list of vertices with their images would search the enumeration once per vertex — and the search
compares vertices, which for the vertex type of a line graph is itself two comparisons in the
vertex type below.  Counting instead of searching turns that into one traversal. -/
def pairing (G H : CGraph) (p : List ℕ) : List ℕ → Option (List (G.V × H.V))
  | [] => some []
  | i :: is =>
    match vtxAt G i, vtxAt H (p.getD i (FinEnum.card H.V)), pairing G H p is with
    | some v, some w, some l => some ((v, w) :: l)
    | _, _, _ => none

/-- Adjacency is carried across the pairing, in both directions at once: the two `Bool`s agree.

Each unordered pair is visited once.  Adjacency is symmetric and irreflexive on both sides, so
the lower half of the matrix and its diagonal say nothing the upper half does not, and it is the
kernel that pays for them. -/
def adjOKAux (G H : CGraph) : List (G.V × H.V) → Bool
  | [] => true
  | (u, a) :: l => l.all (fun vb ↦ H.Adj a vb.2 == G.Adj u vb.1) && adjOKAux G H l

/-- `p` carries the adjacency of `G` to that of `H`. -/
def adjOK (G H : CGraph) (p : List ℕ) : Bool :=
  match pairing G H p (List.range (FinEnum.card G.V)) with
  | none => false
  | some l => adjOKAux G H l

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
  rw [vtxAt, dite_eq_left (permOK_fwd h (idxOf_lt v)).1]
  rfl

/-- The same, read off an index rather than a vertex — the form `pairing` meets it in. -/
theorem vtxAt_vEquiv_idx (h : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true) {i : ℕ}
    (hi : i < FinEnum.card G.V) :
    vtxAt H (p.getD i (FinEnum.card H.V))
      = some (vEquiv h (FinEnum.equiv.symm ⟨i, hi⟩ : G.V)) := by
  have h' := vtxAt_vEquiv h (FinEnum.equiv.symm ⟨i, hi⟩ : G.V)
  simpa only [idxOf, Equiv.apply_symm_apply] using h'

/-- A valid `p` pairs the vertex at every index listed with its image, and nothing is out of
range. -/
theorem pairing_isSome (hp : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true) {is : List ℕ}
    (his : ∀ i ∈ is, i < FinEnum.card G.V) :
    ∃ l, pairing G H p is = some l ∧ ∀ v : G.V, idxOf v ∈ is → (v, vEquiv hp v) ∈ l := by
  induction is with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons i is ih =>
    obtain ⟨l, hl, hmem⟩ := ih fun j hj ↦ his j (List.mem_cons_of_mem _ hj)
    have hi : i < FinEnum.card G.V := his i (List.mem_cons_self ..)
    refine ⟨(FinEnum.equiv.symm ⟨i, hi⟩, vEquiv hp (FinEnum.equiv.symm ⟨i, hi⟩)) :: l, ?_, ?_⟩
    · simp only [pairing, vtxAt_eq_some G hi, vtxAt_vEquiv_idx hp hi, hl]
    · intro v hv
      rcases List.mem_cons.1 hv with h | h
      · have hveq : (FinEnum.equiv.symm ⟨i, hi⟩ : G.V) = v := by
          subst h; exact FinEnum.equiv.symm_apply_apply v
        rw [hveq]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hmem v h)

/-- What the triangular loop leaves behind: any two distinct entries of the list agree, in
either order.  The loop sees each pair once; symmetry of adjacency supplies the other order. -/
theorem adjOKAux_apply {l : List (G.V × H.V)} (h : adjOKAux G H l = true) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → H.Adj x.2 y.2 = G.Adj x.1 y.1 := by
  induction l with
  | nil => simp
  | cons z l ih =>
    obtain ⟨u, a⟩ := z
    rw [adjOKAux, Bool.and_eq_true] at h
    have hhead : ∀ y ∈ l, H.Adj a y.2 = G.Adj u y.1 :=
      fun y hy ↦ by simpa using List.all_eq_true.1 h.1 y hy
    intro x hx y hy hxy
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hhead y hy
    · show H.Adj x.2 a = G.Adj x.1 u
      rw [H.symm x.2 a, G.symm x.1 u]; exact hhead x hx
    · exact ih h.2 x hx y hy hxy

theorem adj_vEquiv (hp : permOK (FinEnum.card G.V) (FinEnum.card H.V) p q = true)
    (ha : adjOK G H p = true) (u v : G.V) : H.Adj (vEquiv hp u) (vEquiv hp v) = G.Adj u v := by
  rcases eq_or_ne u v with rfl | huv
  · rw [Bool.eq_false_iff.2 (H.loopless (vEquiv hp u)), Bool.eq_false_iff.2 (G.loopless u)]
  · obtain ⟨l, hl, hmem⟩ :=
      pairing_isSome hp (is := List.range (FinEnum.card G.V)) fun i hi ↦ List.mem_range.1 hi
    simp only [adjOK, hl] at ha
    exact adjOKAux_apply ha _ (hmem u (List.mem_range.2 (idxOf_lt u))) _
      (hmem v (List.mem_range.2 (idxOf_lt v))) fun h ↦ huv (congrArg Prod.fst h)

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
