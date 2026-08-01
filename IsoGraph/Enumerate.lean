import IsoGraph.Constructions

/-!
# Enumerating graphs up to isomorphism

This file produces, for each `n`, a list containing **exactly one** graph from every isomorphism
class of graphs on `n` vertices.

The plan is the obvious one: a graph on `Fin n` is `n.choose 2` bits — the strict upper triangle of
its adjacency matrix — so it can be packed into a single natural number, and the whole search space
is `List.range (2 ^ n.choose 2)`.  What makes this cheap to *deduplicate* is an observation about
canonicalisation:

`canonAdj n adj` is by definition `relabel (canonPerm n adj) adj`, and `canonAdj` is invariant under
relabelling, so canonicalisation is **idempotent** (`canonAdj_idem`).  Consequently the canonical
codes are precisely the *fixed points* of `canonCode`, and the deduplication step degenerates into a
`List.filter` — no sorting, no hash set, no `List.dedup` with its quadratic behaviour, and constant
memory.

The main results are

* `enumerate n : List CGraph`, all of whose members have `n` vertices;
* `exists_mem_enumerate` — **completeness**: every `n`-vertex graph is isomorphic to a member;
* `enumerate_pairwise_not_iso` — **soundness**: the members are pairwise non-isomorphic.

The final section uses the same encoding to give every graph a numeric `key` that classifies it up
to isomorphism, hence a `Decidable` instance for `Nonempty (G ≃cg H)`.
-/

namespace CGraph.Enum

open IsoGraph.Canon

set_option autoImplicit false

/-! ## Indexing the upper triangle -/

/-- The position of the unordered pair `{i, j}` (`i ≠ j`) in the upper triangle, listed column by
column: `{0,1} ↦ 0`, `{0,2} ↦ 1`, `{1,2} ↦ 2`, `{0,3} ↦ 3`, … -/
def pairIdx (i j : ℕ) : ℕ := if i < j then j.choose 2 + i else i.choose 2 + j

theorem pairIdx_comm (i j : ℕ) : pairIdx i j = pairIdx j i := by
  unfold pairIdx
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, if_neg (by omega)]
  · subst h; rfl
  · rw [if_neg (by omega), if_pos h]

theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ]
  show j.choose 1 + j.choose 2 = j.choose 2 + j
  rw [Nat.choose_one_right, Nat.add_comm]

theorem pairIdx_lt {i j n : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    pairIdx i j < n.choose 2 := by
  rcases Nat.lt_or_ge i j with h | h
  · rw [pairIdx, if_pos h]
    have h1 : (j + 1).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
    rw [choose_two_succ] at h1; omega
  · have h' : j < i := by omega
    rw [pairIdx, if_neg (by omega)]
    have h1 : (i + 1).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
    rw [choose_two_succ] at h1; omega

theorem pairIdx_inj {i j i' j' : ℕ} (h : i < j) (h' : i' < j')
    (e : pairIdx i j = pairIdx i' j') : i = i' ∧ j = j' := by
  rw [pairIdx, if_pos h] at e
  rw [pairIdx, if_pos h'] at e
  have hj : j = j' := by
    by_contra hne
    rcases Nat.lt_or_ge j j' with hlt | hge
    · have h1 : (j + 1).choose 2 ≤ j'.choose 2 := Nat.choose_le_choose 2 (by omega)
      rw [choose_two_succ] at h1; omega
    · have hlt' : j' < j := by omega
      have h1 : (j' + 1).choose 2 ≤ j.choose 2 := Nat.choose_le_choose 2 (by omega)
      rw [choose_two_succ] at h1; omega
  subst hj
  exact ⟨by omega, rfl⟩

/-! ## Encoding a graph as a natural number -/

/-- The pairs `(i, j)` with `i < j < n`, in increasing order of `pairIdx`. -/
def pairsBelow (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j ↦ (List.range j).map fun i ↦ (i, j)

@[simp] theorem mem_pairsBelow {n : ℕ} {p : ℕ × ℕ} :
    p ∈ pairsBelow n ↔ p.1 < p.2 ∧ p.2 < n := by
  obtain ⟨i, j⟩ := p
  simp only [pairsBelow, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', i', hi', rfl, rfl⟩; exact ⟨hi', hj'⟩
  · rintro ⟨hij, hj⟩; exact ⟨j, hj, i, hij, rfl, rfl⟩

theorem testBit_foldl_or {α : Type} (f : α → ℕ) (p : α → Bool) (k : ℕ) (l : List α) (c : ℕ) :
    (l.foldl (fun c a ↦ if p a then c ||| 2 ^ f a else c) c).testBit k
      = (c.testBit k || l.any fun a ↦ p a && decide (f a = k)) := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      by_cases hp : p a
      · simp [hp, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc]
      · simp [hp]

theorem foldl_or_lt {α : Type} (f : α → ℕ) (p : α → Bool) (m : ℕ) (l : List α)
    (hf : ∀ a ∈ l, f a < m) (c : ℕ) (hc : c < 2 ^ m) :
    l.foldl (fun c a ↦ if p a then c ||| 2 ^ f a else c) c < 2 ^ m := by
  induction l generalizing c with
  | nil => simpa using hc
  | cons a t ih =>
      simp only [List.foldl_cons]
      refine ih (fun b hb ↦ hf b (List.mem_cons_of_mem _ hb)) _ ?_
      by_cases hp : p a
      · simp only [hp, if_true]
        exact Nat.or_lt_two_pow hc
          (Nat.pow_lt_pow_right Nat.one_lt_two (hf a List.mem_cons_self))
      · simpa [hp] using hc

/-- The code of an adjacency oracle: bit `pairIdx i j` is set exactly when `i` and `j` are
adjacent, for `i < j < n`. -/
def codeOfAdj (n : ℕ) (adj : ℕ → ℕ → Bool) : ℕ :=
  (pairsBelow n).foldl (fun c p ↦ if adj p.1 p.2 then c ||| 2 ^ pairIdx p.1 p.2 else c) 0

theorem codeOfAdj_lt (n : ℕ) (adj : ℕ → ℕ → Bool) : codeOfAdj n adj < 2 ^ n.choose 2 :=
  foldl_or_lt _ _ _ _
    (fun p hp ↦ by
      obtain ⟨h1, h2⟩ := mem_pairsBelow.1 hp
      exact pairIdx_lt (by omega) h2 (by omega))
    0 (Nat.two_pow_pos _)

theorem testBit_codeOfAdj (n : ℕ) (adj : ℕ → ℕ → Bool) (k : ℕ) :
    (codeOfAdj n adj).testBit k
      = (pairsBelow n).any fun p ↦ adj p.1 p.2 && decide (pairIdx p.1 p.2 = k) := by
  rw [codeOfAdj, testBit_foldl_or]; simp

theorem testBit_codeOfAdj_pair (n : ℕ) (adj : ℕ → ℕ → Bool) {i j : ℕ} (hij : i < j) (hj : j < n) :
    (codeOfAdj n adj).testBit (pairIdx i j) = adj i j := by
  rw [testBit_codeOfAdj]
  refine Bool.eq_iff_iff.2 ⟨?_, ?_⟩
  · rw [List.any_eq_true]
    rintro ⟨⟨i', j'⟩, hmem, hq⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨hi'j', -⟩ := mem_pairsBelow.1 hmem
    obtain ⟨rfl, rfl⟩ := pairIdx_inj hi'j' hij hq.2
    exact hq.1
  · intro hadj
    rw [List.any_eq_true]
    exact ⟨(i, j), mem_pairsBelow.2 ⟨hij, hj⟩, by simp [hadj]⟩

theorem testBit_codeOfAdj_ne (n : ℕ) {adj : ℕ → ℕ → Bool} (hs : ∀ a b, adj a b = adj b a)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    (codeOfAdj n adj).testBit (pairIdx i j) = adj i j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact testBit_codeOfAdj_pair n adj h hj
  · rw [pairIdx_comm, testBit_codeOfAdj_pair n adj (by omega) hi, hs]

/-- The code of a graph on `Fin n`. -/
def codeOf (n : ℕ) (adj : Fin n → Fin n → Bool) : ℕ := codeOfAdj n (oracleOfFin n adj)

theorem codeOf_lt (n : ℕ) (adj : Fin n → Fin n → Bool) : codeOf n adj < 2 ^ n.choose 2 :=
  codeOfAdj_lt n _

/-! ## Decoding -/

/-- The graph on `Fin n` whose upper-triangle adjacency bits are those of `c`. -/
def graphOfCode (n c : ℕ) : CGraph where
  V := Fin n
  Adj i j := decide (i ≠ j) && c.testBit (pairIdx i.1 j.1)
  symm i j := by rw [pairIdx_comm i.1 j.1, decide_ne_comm i j]
  loopless i := by simp

@[simp] theorem graphOfCode_V (n c : ℕ) : (graphOfCode n c).V = Fin n := rfl

@[simp] theorem graphOfCode_adj (n c : ℕ) (i j : Fin n) :
    (graphOfCode n c).Adj i j = (decide (i ≠ j) && c.testBit (pairIdx i.1 j.1)) := rfl

instance (n c : ℕ) : DecidableEq (graphOfCode n c).V := inferInstanceAs (DecidableEq (Fin n))

/-- **Decoding undoes encoding.**  For a genuine adjacency function — symmetric and loopless —
the graph read off its code is the graph itself. -/
theorem adj_graphOfCode_codeOf {n : ℕ} {adj : Fin n → Fin n → Bool}
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) (i j : Fin n) :
    (graphOfCode n (codeOf n adj)).Adj i j = adj i j := by
  rw [graphOfCode_adj]
  by_cases h : i = j
  · subst h; simp [hl i]
  · have hne : i.1 ≠ j.1 := fun he ↦ h (Fin.ext he)
    rw [decide_eq_true h, Bool.true_and, codeOf,
      testBit_codeOfAdj_ne n (oracleOfFin_comm hs) i.2 j.2 hne, oracleOfFin_apply adj i.2 j.2]

/-! ## The canonical code -/

/-- The canonical code of a graph on `Fin n`: the code of its canonical form.

Written through `canonMatrix` rather than `canonAdj` so that the search runs once per graph
instead of once per adjacency query; the two are definitionally equal (`canonCode_eq`). -/
def canonCode (n : ℕ) (adj : Fin n → Fin n → Bool) : ℕ := codeOfAdj n (canonMatrix n adj).get

theorem canonCode_eq (n : ℕ) (adj : Fin n → Fin n → Bool) :
    canonCode n adj = codeOf n (canonAdj n adj) := rfl

/-- **Canonicalisation is idempotent.**  Immediate from invariance: the canonical form is a
relabelling of the original, and relabelling does not change the canonical form. -/
theorem canonAdj_idem (n : ℕ) (adj : Fin n → Fin n → Bool) :
    canonAdj n (canonAdj n adj) = canonAdj n adj :=
  canonAdj_relabel (canonPerm n adj) adj

theorem canonAdj_symm' {n : ℕ} {adj : Fin n → Fin n → Bool} (hs : ∀ i j, adj i j = adj j i)
    (i j : Fin n) : canonAdj n adj i j = canonAdj n adj j i := canonAdj_comm hs i j

theorem canonAdj_loopless {n : ℕ} {adj : Fin n → Fin n → Bool} (hl : ∀ i, adj i i = false)
    (i : Fin n) : canonAdj n adj i i = false :=
  Bool.eq_false_iff.2 (canonAdj_irrefl (fun k ↦ by simp [hl k]) i)

/-- Decoding a canonical code returns the canonical form. -/
theorem adj_graphOfCode_canonCode {n : ℕ} {adj : Fin n → Fin n → Bool}
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) (i j : Fin n) :
    (graphOfCode n (canonCode n adj)).Adj i j = canonAdj n adj i j := by
  rw [canonCode_eq]
  exact adj_graphOfCode_codeOf (canonAdj_symm' hs) (canonAdj_loopless hl) i j

/-- **Canonical codes are exactly the fixed points of `canonCode`.**  This is what makes the
duplicate removal a `filter` rather than a sort or a hash set. -/
theorem canonCode_graphOfCode_canonCode {n : ℕ} {adj : Fin n → Fin n → Bool}
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) :
    canonCode n (graphOfCode n (canonCode n adj)).Adj = canonCode n adj := by
  have h : (graphOfCode n (canonCode n adj)).Adj = canonAdj n adj :=
    funext fun i ↦ funext fun j ↦ adj_graphOfCode_canonCode hs hl i j
  rw [h, canonCode_eq, canonCode_eq, canonAdj_idem]

/-! ## The enumerator -/

/-- The codes surviving the sweep: those that are their own canonical code. -/
def enumCodes (n : ℕ) : List ℕ :=
  (List.range (2 ^ n.choose 2)).filter fun c ↦ canonCode n (graphOfCode n c).Adj == c

/-- **All graphs on `n` vertices, one per isomorphism class.** -/
def enumerate (n : ℕ) : List CGraph := (enumCodes n).map (graphOfCode n)

@[simp] theorem card_of_mem_enumerate {n : ℕ} {H : CGraph} (h : H ∈ enumerate n) :
    Fintype.card H.V = n := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
  exact Fintype.card_fin n

/-- The codes come out strictly increasing, so the enumeration is canonically *ordered* as well as
canonically chosen: the code is the promised sort key. -/
theorem enumCodes_pairwise_lt (n : ℕ) : (enumCodes n).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- An adjacency-preserving bijection of vertex sets is an isomorphism. -/
def isoOfEquiv {G H : CGraph} (e : G.V ≃ H.V) (h : ∀ x y, H.Adj (e x) (e y) = G.Adj x y) :
    G ≃cg H := ⟨e, fun {a b} ↦ by rw [h]⟩

theorem mem_enumCodes {n : ℕ} {adj : Fin n → Fin n → Bool} (hs : ∀ i j, adj i j = adj j i)
    (hl : ∀ i, adj i i = false) : canonCode n adj ∈ enumCodes n := by
  rw [enumCodes, List.mem_filter]
  refine ⟨List.mem_range.2 ?_, ?_⟩
  · rw [canonCode_eq]; exact codeOf_lt _ _
  · simp [canonCode_graphOfCode_canonCode hs hl]

/-- **Completeness.**  Every graph on `n` vertices is isomorphic to one in `enumerate n`. -/
theorem exists_mem_enumerate (G : CGraph) {n : ℕ} (hn : Fintype.card G.V = n) :
    ∃ H ∈ enumerate n, Nonempty (G ≃cg H) := by
  set e : G.V ≃ Fin n := Fintype.equivFinOfCardEq hn with he
  set adj : Fin n → Fin n → Bool := fun i j ↦ G.Adj (e.symm i) (e.symm j) with hadj
  have hs : ∀ i j, adj i j = adj j i := fun i j ↦ G.symm _ _
  have hl : ∀ i, adj i i = false := fun i ↦ Bool.eq_false_iff.2 (G.loopless _)
  refine ⟨graphOfCode n (canonCode n adj),
    List.mem_map_of_mem (mem_enumCodes hs hl), ⟨?_⟩⟩
  refine (isoOfEquiv (G := graphOfCode n (canonCode n adj)) (H := G)
    ((canonPerm n adj).trans e.symm) fun x y ↦ ?_).symm
  rw [adj_graphOfCode_canonCode hs hl, canonAdj_apply]
  rfl

/-! ## Soundness: no duplicates -/

theorem canonCode_eq_of_iso {n c₁ c₂ : ℕ} (i : graphOfCode n c₁ ≃cg graphOfCode n c₂) :
    canonCode n (graphOfCode n c₁).Adj = canonCode n (graphOfCode n c₂).Adj := by
  rw [canonCode_eq, canonCode_eq, codeOf,
    canonAdj_eq_of_equiv (A := (graphOfCode n c₁).Adj) (B := (graphOfCode n c₂).Adj)
      (i.toEquiv : Equiv.Perm (Fin n)) (fun a b ↦ CGraph.Iso.adj_eq i a b), codeOf]

theorem canonCode_of_mem {n c : ℕ} (h : c ∈ enumCodes n) :
    canonCode n (graphOfCode n c).Adj = c := by
  have := (List.mem_filter.1 h).2
  simpa using this

theorem not_iso_of_mem_of_ne {n c₁ c₂ : ℕ} (h₁ : c₁ ∈ enumCodes n) (h₂ : c₂ ∈ enumCodes n)
    (hne : c₁ ≠ c₂) : ¬Nonempty (graphOfCode n c₁ ≃cg graphOfCode n c₂) := by
  rintro ⟨i⟩
  exact hne (by rw [← canonCode_of_mem h₁, ← canonCode_of_mem h₂, canonCode_eq_of_iso i])

/-- **Soundness.**  The graphs listed are pairwise non-isomorphic: the list has exactly one
representative of each isomorphism class. -/
theorem enumerate_pairwise_not_iso (n : ℕ) :
    (enumerate n).Pairwise fun G H ↦ ¬Nonempty (G ≃cg H) := by
  rw [enumerate, List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun h₁ h₂ hne ↦ not_iso_of_mem_of_ne h₁ h₂ hne)
    (List.nodup_range.filter _)

theorem enumerate_nodup (n : ℕ) : (enumerate n).Nodup := by
  refine (enumerate_pairwise_not_iso n).imp ?_
  intro G H h heq
  subst heq
  exact h ⟨RelIso.refl _⟩

/-! ## Enumerating the quotient

The same list, read in `IsoGraph`, is a list of *all* isomorphism classes of size `n`, without
repetition.
-/

/-- The isomorphism classes of graphs on `n` vertices. -/
def enumerateIso (n : ℕ) : List IsoGraph := (enumerate n).map (Quotient.mk CGraph.isoSetoid)

/-- **Completeness in the quotient.**  Every isomorphism class of size `n` occurs. -/
theorem mem_enumerateIso {n : ℕ} {G : IsoGraph} (hn : G.V = n) : G ∈ enumerateIso n := by
  induction G using Quotient.inductionOn with
  | h G =>
      obtain ⟨H, hH, hi⟩ := exists_mem_enumerate G hn
      exact List.mem_map.2 ⟨H, hH, (Quotient.sound (s := CGraph.isoSetoid) hi).symm⟩

/-- **No repetitions in the quotient**: the list is exactly the set of isomorphism classes. -/
theorem enumerateIso_nodup (n : ℕ) : (enumerateIso n).Nodup := by
  rw [enumerateIso, List.Nodup, List.pairwise_map]
  exact (enumerate_pairwise_not_iso n).imp fun h he ↦ h (Quotient.exact he)

/-! ## A numeric key classifying graphs up to isomorphism -/

/-- The **key** of a graph: its vertex count together with the code of its canonical form.  Two
graphs have the same key exactly when they are isomorphic (`key_eq_iff`), so this is the promised
total ordering on graphs up to isomorphism. -/
def key (G : CGraph) : ℕ × ℕ := (Fintype.card G.V, codeOfAdj (Fintype.card G.V) G.canon.get)

/-- The canonical representative, read off the key. -/
theorem canonicalize_eq_graphOfCode (G : CGraph) :
    G.canonicalize
      = graphOfCode (Fintype.card G.V) (codeOfAdj (Fintype.card G.V) G.canon.get) := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun (i : Fin (Fintype.card G.V)) ↦
    funext fun (j : Fin (Fintype.card G.V)) ↦ ?_))
  rw [CGraph.canonicalize_adj, graphOfCode_adj]
  by_cases h : i = j
  · subst h; simp [Bool.eq_false_iff.2 (G.canon_loopless i)]
  · rw [decide_eq_true h, Bool.true_and,
      testBit_codeOfAdj_ne _ (AdjMatrix.get_comm G.canon_adj_symm) i.2 j.2
        (fun he ↦ h (Fin.ext he)),
      AdjMatrix.get_eq _ i.2 j.2]

theorem canon_get_eq_of_iso {G H : CGraph} (i : G ≃cg H) : G.canon.get = H.canon.get := by
  have aux : ∀ (m k : ℕ) (M : AdjMatrix m) (N : AdjMatrix k), m = k → HEq M N → M.get = N.get := by
    rintro m k M N rfl h
    cases h
    rfl
  exact aux _ _ _ _ (CGraph.Iso.card_eq G H i) (CGraph.canon_heq_of_iso i)

theorem key_eq_of_iso {G H : CGraph} (i : G ≃cg H) : key G = key H := by
  have aux : ∀ (a a' : ℕ) (f g : ℕ → ℕ → Bool), a = a' → f = g → codeOfAdj a f = codeOfAdj a' g := by
    rintro a a' f g rfl rfl; rfl
  have hc : Fintype.card G.V = Fintype.card H.V := CGraph.Iso.card_eq G H i
  simp only [key, Prod.mk.injEq]
  exact ⟨hc, aux _ _ _ _ hc (canon_get_eq_of_iso i)⟩

/-- **The key is a complete isomorphism invariant.** -/
theorem key_eq_iff {G H : CGraph} : key G = key H ↔ Nonempty (G ≃cg H) := by
  refine ⟨fun h ↦ ?_, fun ⟨i⟩ ↦ key_eq_of_iso i⟩
  have aux : ∀ a a' b b' : ℕ, a = a' → b = b' → graphOfCode a b = graphOfCode a' b' := by
    rintro a a' b b' rfl rfl; rfl
  rw [← CGraph.canonicalize_eq_iff, canonicalize_eq_graphOfCode, canonicalize_eq_graphOfCode]
  exact aux _ _ _ _ (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **Isomorphism of two arbitrary graphs is decidable**, by comparing keys — one canonical
labelling each, rather than a search over bijections. -/
instance decidableNonemptyIso (G H : CGraph) : Decidable (Nonempty (G ≃cg H)) :=
  decidable_of_iff (key G = key H) key_eq_iff

/-! ## Sanity check

The counts are OEIS A000088, the number of graphs on `n` unlabelled vertices.  Larger `n` is
checked by `lake exe enumbench`, which reaches `n = 7`: 1044 classes out of `2 ^ 21` codes.
-/

#guard ((List.range 5).map fun n ↦ (enumCodes n).length) == [1, 1, 2, 4, 11]

end CGraph.Enum
