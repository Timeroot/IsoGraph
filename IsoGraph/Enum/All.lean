import IsoGraph.Graphs.Constructions
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Perm
import IsoGraph.ForMathlib.Bits
import IsoGraph.ForMathlib.Nat

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

## Faster enumerators

Sweeping all `2 ^ n.choose 2` codes is quadratic in the exponent, so it runs out of steam at
`n = 7`.  The rest of the file builds graphs one vertex at a time instead: extend each of the
graphs already found on `n` vertices by a new *last* vertex, canonicalise, and deduplicate.
Because the new vertex is last, its incidences occupy the top `n` bits of the code and the
extension is a plain shift-and-or (`extendCode`).

Which of the `2 ^ n` neighbourhoods to try is left as a parameter: `enumCodesOf masks` is the
enumerator built from a mask selector `masks : ℕ → ℕ → List ℕ`, and the *only* obligation on
`masks` is `MasksComplete` — every `(n+1)`-vertex graph must arise from *some* `n`-vertex graph
and *some* offered mask.  No soundness side is needed: whatever `masks` produces, the output of
`enumCodesOf` consists of `canonCode` values, hence of canonical codes, so `enumCodesOf_eq` gives
`enumCodesOf masks n = enumCodes n` on the nose and every enumerator below inherits completeness
and soundness from `enumerate`.  Three selectors are provided, each pruning more:

* `allMasks` — all `2 ^ n` neighbourhoods (`enumCodesExt`);
* `symMasks` — keep only orbit minima under the automorphism group of the parent (`enumCodesSym`).
  The generators come out of the canonical-labelling search, but are re-checked at runtime with
  `decide` (`autoPerms`), so no proof depends on the search being correct;
* `redMasks` — additionally require the new vertex to have least degree (`enumCodesFast`), which
  is legitimate because every graph has such a vertex and the test is `Aut`-invariant.

Measured with `lake exe enumbench --all` (counts all matching OEIS A000088):

| `n` | `enumCodes` | `enumCodesExt` | `enumCodesSym` | `enumCodesFast` |
|-----|------------:|---------------:|---------------:|----------------:|
| 7   |    108389ms |          502ms |          308ms |           161ms |
| 8   |           — |         7509ms |         4879ms |          2196ms |
| 9   |           — |              — |              — |        219158ms |

At `n = 9` the pruning leaves little on the table: 18329 candidates were canonicalised to produce
the 12346 graphs on 8 vertices, so all but a factor of 1.5 of the work is one canonical labelling
per graph, and further symmetry reduction cannot buy much.

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
  · subst h; simp
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

/-- An isomorphism, from a computation that the two keys agree.  Deciding *whether* two graphs are
isomorphic is a comparison of two canonical labellings; picking one of the maps that witnesses it
is not part of that answer, so this is noncomputable. -/
noncomputable def isoOfKeyEq {G H : CGraph} (h : key G = key H) : G ≃cg H :=
  Classical.choice (key_eq_iff.1 h)

/-- The key of an isomorphism class: `key` is an isomorphism invariant, so it descends to the
quotient. -/
def _root_.IsoGraph.key : IsoGraph → ℕ × ℕ :=
  Quotient.lift (s := CGraph.isoSetoid) CGraph.Enum.key fun _ _ ⟨i⟩ ↦ CGraph.Enum.key_eq_of_iso i

@[simp] theorem _root_.IsoGraph.key_mk (G : CGraph) :
    IsoGraph.key (Quotient.mk _ G) = CGraph.Enum.key G := rfl

/-- **The key determines the isomorphism class.** -/
theorem _root_.IsoGraph.key_injective : Function.Injective IsoGraph.key := by
  intro G H h
  induction G using Quotient.inductionOn with
  | h G =>
      induction H using Quotient.inductionOn with
      | h H => exact Quotient.sound (CGraph.Enum.key_eq_iff.1 h)

@[simp] theorem _root_.IsoGraph.key_eq_key_iff {G H : IsoGraph} :
    IsoGraph.key G = IsoGraph.key H ↔ G = H :=
  ⟨fun h ↦ IsoGraph.key_injective h, fun h ↦ h ▸ rfl⟩

/-- **Equality of isomorphism classes is decidable**, by comparing keys: one canonical labelling
each. -/
instance _root_.IsoGraph.instDecidableEq : DecidableEq IsoGraph := fun _ _ ↦
  decidable_of_iff _ IsoGraph.key_eq_key_iff

/-! ## Sorted deduplication -/

/-- Remove adjacent duplicates.  On a sorted list this removes *all* duplicates. -/
def dedupSorted : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: t => if a = b then dedupSorted (b :: t) else a :: dedupSorted (b :: t)

/-- Tail-recursive implementation of `dedupSorted`.  The naive equation compiler output recurses
once per element, which blows the stack on the hundreds of thousands of candidates that appear from
`n = 9` on; this version is installed as the compiled code by the `@[csimp]` lemma below, so nothing
downstream has to mention it. -/
def dedupSortedFast (l : List ℕ) : List ℕ := go l []
where
  go : List ℕ → List ℕ → List ℕ
    | [], acc => acc.reverse
    | [a], acc => (a :: acc).reverse
    | a :: b :: t, acc => if a = b then go (b :: t) acc else go (b :: t) (a :: acc)

theorem dedupSortedFast.go_eq (l acc : List ℕ) :
    dedupSortedFast.go l acc = acc.reverse ++ dedupSorted l := by
  fun_induction dedupSortedFast.go l acc <;> simp_all [dedupSorted]

@[csimp] theorem dedupSorted_eq_dedupSortedFast : @dedupSorted = @dedupSortedFast := by
  funext l
  simpa using (dedupSortedFast.go_eq l []).symm

/-- Deduplicate a list of naturals in `O(k log k)`: sort, then drop adjacent duplicates. -/
def dedupNat (l : List ℕ) : List ℕ := dedupSorted (l.mergeSort (· ≤ ·))

@[simp] theorem mem_dedupSorted {a : ℕ} {l : List ℕ} : a ∈ dedupSorted l ↔ a ∈ l := by
  fun_induction dedupSorted l with
  | case1 => simp
  | case2 b => simp
  | case3 x t ih => simp only [List.mem_cons, ih, or_self_left]
  | case4 x y t h ih => simp only [List.mem_cons, ih]

theorem pairwise_lt_dedupSorted : ∀ {l : List ℕ}, l.Pairwise (· ≤ ·) →
    (dedupSorted l).Pairwise (· < ·) := by
  intro l
  fun_induction dedupSorted l with
  | case1 => simp
  | case2 b => simp
  | case3 x t ih => exact fun h ↦ ih h.tail
  | case4 x y t hxy ih =>
      intro h
      have hcons := List.pairwise_cons.1 h
      have hxy' : x < y := lt_of_le_of_ne (hcons.1 y (by simp)) hxy
      refine List.pairwise_cons.2 ⟨?_, ih hcons.2⟩
      intro z hz
      rcases List.mem_cons.1 (mem_dedupSorted.1 hz) with rfl | hz'
      · exact hxy'
      · exact lt_of_lt_of_le hxy' ((List.pairwise_cons.1 hcons.2).1 z hz')

@[simp] theorem mem_dedupNat {a : ℕ} {l : List ℕ} : a ∈ dedupNat l ↔ a ∈ l := by
  rw [dedupNat, mem_dedupSorted]
  exact (List.mergeSort_perm l _).mem_iff

theorem pairwise_lt_dedupNat (l : List ℕ) : (dedupNat l).Pairwise (· < ·) :=
  pairwise_lt_dedupSorted
    ((List.pairwise_mergeSort (fun a b c ↦ by simp; omega) (fun a b ↦ by simp; omega) l).imp
      (fun {a b} h ↦ by simpa using h))

theorem nodup_dedupNat (l : List ℕ) : (dedupNat l).Nodup :=
  (pairwise_lt_dedupNat l).imp Nat.ne_of_lt

/-! ## Adding a vertex -/

/-- The bit mask of a row: bit `i` is set exactly when `f i`, for `i < n`. -/
def rowMask (n : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range n).foldl (fun m i ↦ if f i then m ||| 2 ^ i else m) 0

theorem rowMask_lt (n : ℕ) (f : ℕ → Bool) : rowMask n f < 2 ^ n :=
  foldl_or_lt (fun a ↦ a) f n _ (fun _ ha ↦ List.mem_range.1 ha) 0 (Nat.two_pow_pos _)

theorem testBit_rowMask {n : ℕ} (f : ℕ → Bool) {k : ℕ} (hk : k < n) :
    (rowMask n f).testBit k = f k := by
  rw [rowMask, testBit_foldl_or (fun a ↦ a)]
  simp only [Nat.zero_testBit, Bool.false_or]
  refine Bool.eq_iff_iff.2 ⟨?_, ?_⟩
  · rw [List.any_eq_true]
    rintro ⟨a, -, ha⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨h1, rfl⟩ := ha
    exact h1
  · intro h
    rw [List.any_eq_true]
    exact ⟨k, List.mem_range.2 hk, by simp [h]⟩

/-- Extend the code `c` of an `n`-vertex graph by a new last vertex whose neighbourhood is the
bit mask `s`.  The pair indices `pairIdx i n` for `i < n` are exactly the positions
`n.choose 2, …, (n+1).choose 2 - 1`, so this is a plain shift-and-or. -/
def extendCode (n c s : ℕ) : ℕ := c ||| (s <<< n.choose 2)

theorem testBit_extendCode_low {n c s k : ℕ} (hk : k < n.choose 2) :
    (extendCode n c s).testBit k = c.testBit k := by
  rw [extendCode, Nat.testBit_or, Nat.testBit_shiftLeft]
  simp [Nat.not_le.2 hk]

theorem testBit_extendCode_high {n c s i : ℕ} (hc : c < 2 ^ n.choose 2) :
    (extendCode n c s).testBit (n.choose 2 + i) = s.testBit i := by
  have h0 : c.testBit (n.choose 2 + i) = false :=
    Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [extendCode, Nat.testBit_or, Nat.testBit_shiftLeft, h0]
  simp

theorem adj_extendCode_lt {n c s : ℕ} {i j : Fin (n + 1)} (hi : i.1 < n) (hj : j.1 < n) :
    (graphOfCode (n + 1) (extendCode n c s)).Adj i j
      = (graphOfCode n c).Adj ⟨i.1, hi⟩ ⟨j.1, hj⟩ := by
  rw [graphOfCode_adj, graphOfCode_adj]
  by_cases h : i.1 = j.1
  · simp [Fin.ext_iff, h]
  · rw [testBit_extendCode_low (pairIdx_lt hi hj h)]
    simp [Fin.ext_iff, h]

theorem adj_extendCode_last {n c s : ℕ} (hc : c < 2 ^ n.choose 2) {i : Fin (n + 1)}
    (hi : i.1 < n) :
    (graphOfCode (n + 1) (extendCode n c s)).Adj i (Fin.last n) = s.testBit i.1 := by
  rw [graphOfCode_adj]
  have hne : i ≠ Fin.last n := fun h ↦ by rw [h] at hi; simp at hi
  have hp : pairIdx i.1 (Fin.last n).1 = n.choose 2 + i.1 := by
    rw [Fin.val_last, pairIdx, if_pos hi]
  rw [decide_eq_true hne, Bool.true_and, hp, testBit_extendCode_high hc]

/-! ## Extending a permutation by a fixed last vertex -/

/-- A permutation of `Fin n`, extended to `Fin (n+1)` by fixing the last element. -/
def permLast {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquivLast.trans σ.optionCongr).trans finSuccEquivLast.symm

@[simp] theorem permLast_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permLast σ i.castSucc = (σ i).castSucc := by
  simp [permLast]

@[simp] theorem permLast_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLast σ (Fin.last n) = Fin.last n := by
  simp [permLast]

/-! ## The fast enumerator

The recursion is parameterised by a **mask selector** `masks n c`, the list of neighbourhoods to
try for the new vertex when extending the graph with code `c`.  Offering every mask
(`allMasks`) is complete for trivial reasons; the point of the parameter is that pruning the list
is then a self-contained obligation (`MasksComplete`), and every theorem below is proved once and
for all.
-/

theorem canonCode_lt (n : ℕ) (adj : Fin n → Fin n → Bool) :
    canonCode n adj < 2 ^ n.choose 2 := by
  rw [canonCode_eq]; exact codeOf_lt _ _

theorem canonCode_zero (adj : Fin 0 → Fin 0 → Bool) : canonCode 0 adj = 0 := rfl

/-- **One level of the recursion**: extend every code in `l` by a new last vertex in each offered
way, canonicalise, and deduplicate. -/
def extendLevel (masks : ℕ → ℕ → List ℕ) (n : ℕ) (l : List ℕ) : List ℕ :=
  dedupNat ((l.flatMap fun c ↦ (masks n c).map (extendCode n c)).map
    fun C ↦ canonCode (n + 1) (graphOfCode (n + 1) C).Adj)

theorem mem_extendLevel {masks : ℕ → ℕ → List ℕ} {n : ℕ} {l : List ℕ} {d : ℕ} :
    d ∈ extendLevel masks n l ↔ ∃ c ∈ l, ∃ s ∈ masks n c,
      canonCode (n + 1) (graphOfCode (n + 1) (extendCode n c s)).Adj = d := by
  rw [extendLevel, mem_dedupNat, List.mem_map]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨c, hc, hC'⟩ := List.mem_flatMap.1 hC
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hC'
    exact ⟨c, hc, s, hs, rfl⟩
  · rintro ⟨c, hc, s, hs, rfl⟩
    exact ⟨extendCode n c s, List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨s, hs, rfl⟩⟩, rfl⟩

/-- Every entry of a level is a canonical code, and in range — whatever the masks were. -/
theorem isCanon_of_mem_extendLevel {masks : ℕ → ℕ → List ℕ} {n : ℕ} {l : List ℕ} {d : ℕ}
    (h : d ∈ extendLevel masks n l) :
    canonCode (n + 1) (graphOfCode (n + 1) d).Adj = d ∧ d < 2 ^ (n + 1).choose 2 := by
  obtain ⟨c, -, s, -, rfl⟩ := mem_extendLevel.1 h
  set C := extendCode n c s
  exact ⟨canonCode_graphOfCode_canonCode (fun i j ↦ (graphOfCode (n + 1) C).symm i j)
      (fun i ↦ Bool.eq_false_iff.2 ((graphOfCode (n + 1) C).loopless i)),
    canonCode_lt _ _⟩

theorem pairwise_lt_extendLevel (masks : ℕ → ℕ → List ℕ) (n : ℕ) (l : List ℕ) :
    (extendLevel masks n l).Pairwise (· < ·) := pairwise_lt_dedupNat _

/-- The recursion, over an arbitrary mask selector. -/
def enumCodesOf (masks : ℕ → ℕ → List ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => extendLevel masks n (enumCodesOf masks n)

/-- **What a mask selector must satisfy**: every graph on `n + 1` vertices must be obtainable, up
to isomorphism, by extending *some* graph on `n` vertices by one of the offered masks.

Nothing is required for soundness — whatever masks are offered, the entries of `enumCodesOf` are
canonical codes of graphs on `n` vertices, because they are outputs of `canonCode`. -/
def MasksComplete (masks : ℕ → ℕ → List ℕ) : Prop :=
  ∀ (n : ℕ) (adj : Fin (n + 1) → Fin (n + 1) → Bool), (∀ i j, adj i j = adj j i) →
    (∀ i, adj i i = false) →
    ∃ adj' : Fin n → Fin n → Bool, (∀ i j, adj' i j = adj' j i) ∧ (∀ i, adj' i i = false) ∧
      ∃ s ∈ masks n (canonCode n adj'),
        canonCode (n + 1) (graphOfCode (n + 1) (extendCode n (canonCode n adj') s)).Adj
          = canonCode (n + 1) adj

/-- Every entry of `enumCodesOf masks n` is a canonical code, and in range. -/
theorem isCanon_of_mem {masks : ℕ → ℕ → List ℕ} {n c : ℕ} (h : c ∈ enumCodesOf masks n) :
    canonCode n (graphOfCode n c).Adj = c ∧ c < 2 ^ n.choose 2 := by
  cases n with
  | zero =>
      rw [enumCodesOf, List.mem_singleton] at h
      subst h
      exact ⟨canonCode_zero _, by norm_num⟩
  | succ n => exact isCanon_of_mem_extendLevel h

/-! ### Deleting the last vertex

`lastMask n adj` is the neighbourhood the last vertex acquires once the *other* `n` vertices have
been canonically relabelled: reattaching it to the canonical form of `adj` restricted to the first
`n` vertices rebuilds `adj` up to isomorphism (`canonCode_extend`). -/

/-- `adj` with its last vertex deleted. -/
abbrev restrict {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool) : Fin n → Fin n → Bool :=
  fun i j ↦ adj i.castSucc j.castSucc

/-- The neighbourhood of the last vertex, read through the canonical labelling of the rest. -/
def lastMask (n : ℕ) (adj : Fin (n + 1) → Fin (n + 1) → Bool) : ℕ :=
  rowMask n fun k ↦
    if h : k < n then adj ((canonPerm n (restrict adj)) ⟨k, h⟩).castSucc (Fin.last n) else false

theorem lastMask_lt (n : ℕ) (adj : Fin (n + 1) → Fin (n + 1) → Bool) : lastMask n adj < 2 ^ n :=
  rowMask_lt _ _

theorem testBit_lastMask {n : ℕ} {adj : Fin (n + 1) → Fin (n + 1) → Bool} {k : ℕ} (hk : k < n) :
    (lastMask n adj).testBit k
      = adj ((canonPerm n (restrict adj)) ⟨k, hk⟩).castSucc (Fin.last n) := by
  rw [lastMask, testBit_rowMask _ hk, dif_pos hk]

/-- **The key step**, as an explicit isomorphism: relabelling by `permLast (canonPerm …)` carries
`adj` to the graph built by canonicalising the first `n` vertices and putting the last vertex's
neighbourhood back on top. -/
theorem adj_extendCode_lastMask {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) (a b : Fin (n + 1)) :
    adj (permLast (canonPerm n (restrict adj)) a) (permLast (canonPerm n (restrict adj)) b)
      = (graphOfCode (n + 1)
          (extendCode n (canonCode n (restrict adj)) (lastMask n adj))).Adj a b := by
  have hs' : ∀ i j, restrict adj i j = restrict adj j i := fun i j ↦ hs _ _
  have hl' : ∀ i, restrict adj i i = false := fun i ↦ hl _
  set σ : Equiv.Perm (Fin n) := canonPerm n (restrict adj) with hσ
  set c : ℕ := canonCode n (restrict adj) with hc
  have hclt : c < 2 ^ n.choose 2 := canonCode_lt _ _
  set s : ℕ := lastMask n adj with hsdef
  have hlast : ∀ x : Fin n,
      (graphOfCode (n + 1) (extendCode n c s)).Adj x.castSucc (Fin.last n)
        = adj (σ x).castSucc (Fin.last n) := by
    intro x
    rw [adj_extendCode_last hclt (by simp), hsdef, testBit_lastMask (show (x.castSucc).1 < n by
      simp)]
    rfl
  revert a b
  refine Fin.lastCases ?_ ?_
  · refine Fin.lastCases ?_ ?_
    · simp [hl]
    · intro y
      rw [permLast_last, permLast_castSucc, hs,
        (graphOfCode (n + 1) (extendCode n c s)).symm, hlast y]
  · intro x
    refine Fin.lastCases ?_ ?_
    · rw [permLast_last, permLast_castSucc, hlast x]
    · intro y
      rw [permLast_castSucc, permLast_castSucc,
        adj_extendCode_lt (show (x.castSucc).1 < n by simp)
          (show (y.castSucc).1 < n by simp)]
      show adj _ _ = (graphOfCode n c).Adj x y
      rw [hc, adj_graphOfCode_canonCode hs' hl', canonAdj_apply]

/-- **The key step.**  Canonicalise the graph on the first `n` vertices, put the last vertex's
neighbourhood back on top, and the result is isomorphic to the graph we started with. -/
theorem canonCode_extend {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool)
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) :
    canonCode (n + 1)
        (graphOfCode (n + 1) (extendCode n (canonCode n (restrict adj)) (lastMask n adj))).Adj
      = canonCode (n + 1) adj := by
  exact congrArg (codeOf (n + 1)) (canonAdj_eq_of_equiv (permLast (canonPerm n (restrict adj)))
    (adj_extendCode_lastMask adj hs hl))

/-! ### Completeness and soundness, for any complete mask selector -/

/-- **Completeness.** -/
theorem mem_enumCodesOf {masks : ℕ → ℕ → List ℕ} (hm : MasksComplete masks) :
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ i j, adj i j = adj j i) → (∀ i, adj i i = false) →
      canonCode n adj ∈ enumCodesOf masks n := by
  intro n
  induction n with
  | zero => intro adj _ _; rw [canonCode_zero, enumCodesOf]; simp
  | succ n ih =>
      intro adj hs hl
      obtain ⟨adj', hs', hl', t, ht, heq⟩ := hm n adj hs hl
      exact mem_extendLevel.2 ⟨_, ih adj' hs' hl', t, ht, heq⟩

/-- **The pruned enumerator agrees with the brute-force sweep**, as sets of codes. -/
theorem mem_enumCodesOf_iff {masks : ℕ → ℕ → List ℕ} (hm : MasksComplete masks) {n c : ℕ} :
    c ∈ enumCodesOf masks n ↔ c ∈ enumCodes n := by
  constructor
  · intro h
    obtain ⟨hcan, hlt⟩ := isCanon_of_mem h
    rw [enumCodes, List.mem_filter]
    exact ⟨List.mem_range.2 hlt, by simp [hcan]⟩
  · intro h
    have := mem_enumCodesOf hm n (graphOfCode n c).Adj (fun i j ↦ (graphOfCode n c).symm i j)
      (fun i ↦ Bool.eq_false_iff.2 ((graphOfCode n c).loopless i))
    rwa [canonCode_of_mem h] at this

theorem pairwise_lt_enumCodesOf (masks : ℕ → ℕ → List ℕ) (n : ℕ) :
    (enumCodesOf masks n).Pairwise (· < ·) := by
  cases n with
  | zero => simp [enumCodesOf]
  | succ n => exact pairwise_lt_extendLevel _ _ _

theorem nodup_enumCodesOf (masks : ℕ → ℕ → List ℕ) (n : ℕ) : (enumCodesOf masks n).Nodup :=
  (pairwise_lt_enumCodesOf masks n).imp Nat.ne_of_lt

/-- **The pruned enumerator computes the same list as the brute-force sweep** — not merely the
same set: both are strictly increasing lists of codes with the same members. -/
theorem enumCodesOf_eq {masks : ℕ → ℕ → List ℕ} (hm : MasksComplete masks) (n : ℕ) :
    enumCodesOf masks n = enumCodes n :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h₁ h₂ ↦ le_antisymm h₁ h₂)
    ((pairwise_lt_enumCodesOf masks n).imp le_of_lt) ((enumCodes_pairwise_lt n).imp le_of_lt)
    ((List.perm_ext_iff_of_nodup (nodup_enumCodesOf masks n) (List.nodup_range.filter _)).2
      fun _ ↦ mem_enumCodesOf_iff hm)

/-! ### Offering every mask -/

/-- Every neighbourhood for the new vertex. -/
def allMasks (n : ℕ) (_c : ℕ) : List ℕ := List.range (2 ^ n)

theorem allMasks_complete : MasksComplete allMasks := fun n adj hs hl ↦
  ⟨restrict adj, fun _ _ ↦ hs _ _, fun _ ↦ hl _, lastMask n adj,
    List.mem_range.2 (lastMask_lt n adj), canonCode_extend adj hs hl⟩

/-- **The canonical codes of all graphs on `n` vertices**, built one vertex at a time: extend each
graph on `n-1` vertices in all `2 ^ (n-1)` ways, canonicalise, and remove duplicates. -/
def enumCodesExt : ℕ → List ℕ := enumCodesOf allMasks

theorem enumCodesExt_eq (n : ℕ) : enumCodesExt n = enumCodes n :=
  enumCodesOf_eq allMasks_complete n

/-! ## Masks are determined by their low bits -/

theorem rowMask_testBit {n s : ℕ} (hs : s < 2 ^ n) : rowMask n s.testBit = s :=
  eq_of_testBit_lt (rowMask_lt _ _) hs fun _ hk ↦ testBit_rowMask _ hk

/-! ## Permuting a neighbourhood mask -/

/-- The mask `s` read through `σ`: bit `k` of `permMask n σ s` is bit `σ k` of `s`. -/
def permMask (n : ℕ) (σ : Equiv.Perm (Fin n)) (s : ℕ) : ℕ :=
  rowMask n fun k ↦ if h : k < n then s.testBit (σ ⟨k, h⟩).1 else false

theorem permMask_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) (s : ℕ) : permMask n σ s < 2 ^ n :=
  rowMask_lt _ _

theorem testBit_permMask {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : ℕ) {k : ℕ} (hk : k < n) :
    (permMask n σ s).testBit k = s.testBit (σ ⟨k, hk⟩).1 := by
  rw [permMask, testBit_rowMask _ hk, dif_pos hk]

theorem permMask_one {n s : ℕ} (hs : s < 2 ^ n) : permMask n 1 s = s :=
  eq_of_testBit_lt (permMask_lt _ _ _) hs fun _ hk ↦ by rw [testBit_permMask _ _ hk]; rfl

theorem permMask_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (s : ℕ) :
    permMask n σ (permMask n τ s) = permMask n (τ * σ) s :=
  eq_of_testBit_lt (permMask_lt _ _ _) (permMask_lt _ _ _) fun k hk ↦ by
    rw [testBit_permMask _ _ hk, testBit_permMask _ _ (σ ⟨k, hk⟩).2, testBit_permMask _ _ hk]
    rfl

/-! ## The automorphism group -/

/-- The automorphisms of a graph on `Fin n`, as a `Finset`. -/
def autGroup (n : ℕ) (adj : Fin n → Fin n → Bool) : Finset (Equiv.Perm (Fin n)) :=
  {σ | ∀ i j, adj (σ i) (σ j) = adj i j}

theorem mem_autGroup {n : ℕ} {adj : Fin n → Fin n → Bool} {σ : Equiv.Perm (Fin n)} :
    σ ∈ autGroup n adj ↔ ∀ i j, adj (σ i) (σ j) = adj i j := by
  simp [autGroup]

theorem one_mem_autGroup {n : ℕ} (adj : Fin n → Fin n → Bool) :
    (1 : Equiv.Perm (Fin n)) ∈ autGroup n adj := mem_autGroup.2 fun _ _ ↦ rfl

theorem mul_mem_autGroup {n : ℕ} {adj : Fin n → Fin n → Bool} {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ autGroup n adj) (hτ : τ ∈ autGroup n adj) : σ * τ ∈ autGroup n adj :=
  mem_autGroup.2 fun i j ↦ by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, mem_autGroup.1 hσ, mem_autGroup.1 hτ]

/-- Permuting the mask by an automorphism `σ` of the parent is the same as relabelling the
extension by `permLast σ`. -/
theorem adj_extendCode_permMask {n c s : ℕ} (hc : c < 2 ^ n.choose 2)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ autGroup n (graphOfCode n c).Adj) :
    ∀ a b : Fin (n + 1),
      (graphOfCode (n + 1) (extendCode n c s)).Adj (permLast σ a) (permLast σ b)
        = (graphOfCode (n + 1) (extendCode n c (permMask n σ s))).Adj a b := by
  have hσ' := mem_autGroup.1 hσ
  have hlast : ∀ x : Fin n,
      (graphOfCode (n + 1) (extendCode n c s)).Adj (σ x).castSucc (Fin.last n)
        = (graphOfCode (n + 1) (extendCode n c (permMask n σ s))).Adj x.castSucc
            (Fin.last n) := by
    intro x
    rw [adj_extendCode_last hc (by simp), adj_extendCode_last hc (by simp),
      testBit_permMask _ _ (show (x.castSucc).1 < n by simp)]
    rfl
  refine Fin.lastCases ?_ ?_
  · refine Fin.lastCases ?_ ?_
    · simp [permLast_last]
    · intro y
      rw [permLast_last, permLast_castSucc, (graphOfCode (n + 1) _).symm,
        (graphOfCode (n + 1) (extendCode n c (permMask n σ s))).symm]
      exact hlast y
  · intro x
    refine Fin.lastCases ?_ ?_
    · rw [permLast_last, permLast_castSucc]; exact hlast x
    · intro y
      rw [permLast_castSucc, permLast_castSucc,
        adj_extendCode_lt (show ((σ x).castSucc).1 < n by simp)
          (show ((σ y).castSucc).1 < n by simp),
        adj_extendCode_lt (show (x.castSucc).1 < n by simp)
          (show (y.castSucc).1 < n by simp)]
      exact hσ' x y

/-- Masks in the same orbit of `Aut` give isomorphic extensions, hence the same canonical code. -/
theorem canonCode_extendCode_permMask {n c s : ℕ} (hc : c < 2 ^ n.choose 2)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ autGroup n (graphOfCode n c).Adj) :
    canonCode (n + 1) (graphOfCode (n + 1) (extendCode n c (permMask n σ s))).Adj
      = canonCode (n + 1) (graphOfCode (n + 1) (extendCode n c s)).Adj := by
  exact congrArg (codeOf (n + 1))
    (canonAdj_eq_of_equiv (permLast σ) (adj_extendCode_permMask hc σ hσ))

/-! ## Harvesting automorphisms -/

/-- Candidate automorphisms, as found by the canonical-labelling search, together with their
inverses — and each one *checked*, so nothing here depends on the search being right. -/
def autoPerms (n : ℕ) (adj : Fin n → Fin n → Bool) : List (Equiv.Perm (Fin n)) :=
  let gens := ((canonical (Graph.ofOracle n (oracleOfFin n adj))).autos.toList.map
    fun a ↦ permOfArrays n a (invArray n a))
  (gens ++ gens.map (·⁻¹)).filter fun σ ↦ decide (∀ i j, adj (σ i) (σ j) = adj i j)

theorem autoPerms_mem {n : ℕ} {adj : Fin n → Fin n → Bool} {σ : Equiv.Perm (Fin n)}
    (h : σ ∈ autoPerms n adj) : σ ∈ autGroup n adj := by
  simp only [autoPerms, List.mem_filter, decide_eq_true_eq] at h
  exact mem_autGroup.2 h.2

/-! ## Orbit-reduced masks -/

/-- The neighbourhoods to try for the new vertex: those that no discovered automorphism makes
smaller.  Every orbit's least element passes, so nothing is lost. -/
def symMasks (n c : ℕ) : List ℕ :=
  let ps := autoPerms n (graphOfCode n c).Adj
  (List.range (2 ^ n)).filter fun s ↦ ps.all fun σ ↦ decide (s ≤ permMask n σ s)

/-- **Nothing is lost by orbit reduction**: every mask has an automorphic image in the list. -/
theorem exists_mem_symMasks {n c s : ℕ} (hs : s < 2 ^ n) :
    ∃ σ ∈ autGroup n (graphOfCode n c).Adj, permMask n σ s ∈ symMasks n c := by
  classical
  set A := autGroup n (graphOfCode n c).Adj with hA
  set O : Finset ℕ := A.image fun σ ↦ permMask n σ s with hO
  have hOmem : ∀ x : ℕ, x ∈ O ↔ ∃ σ ∈ A, permMask n σ s = x := fun _ ↦ Finset.mem_image
  have hne : O.Nonempty := ⟨s, (hOmem s).2 ⟨1, one_mem_autGroup _, permMask_one hs⟩⟩
  obtain ⟨σ₀, hσ₀, ht⟩ := (hOmem _).1 (O.min'_mem hne)
  refine ⟨σ₀, hσ₀, ?_⟩
  rw [symMasks, List.mem_filter, ht]
  refine ⟨List.mem_range.2 (ht ▸ permMask_lt _ _ _), ?_⟩
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro σ hσ
  refine O.min'_le _ ((hOmem _).2 ⟨σ₀ * σ, mul_mem_autGroup hσ₀ (autoPerms_mem hσ), ?_⟩)
  rw [← permMask_mul, ht]

/-! ## Degrees -/

/-- The degree of `i`. -/
def deg {n : ℕ} (adj : Fin n → Fin n → Bool) (i : Fin n) : ℕ := ∑ j, if adj i j then 1 else 0

/-- The number of set bits of `s` below `n`. -/
def maskCard (n s : ℕ) : ℕ := ∑ i : Fin n, if s.testBit i.1 then 1 else 0

theorem deg_perm {n : ℕ} (adj : Fin n → Fin n → Bool) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    deg (fun a b ↦ adj (σ a) (σ b)) i = deg adj (σ i) :=
  Fintype.sum_equiv σ _ _ fun _ ↦ rfl

theorem deg_of_mem_autGroup {n : ℕ} {adj : Fin n → Fin n → Bool} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ autGroup n adj) (i : Fin n) : deg adj (σ i) = deg adj i := by
  have h : (fun a b ↦ adj (σ a) (σ b)) = adj := funext fun a ↦ funext fun b ↦ mem_autGroup.1 hσ a b
  rw [← deg_perm adj σ i, h]

theorem deg_castSucc_split {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    deg adj i = (∑ j : Fin n, if adj i j.castSucc then 1 else 0)
      + (if adj i (Fin.last n) then 1 else 0) := Fin.sum_univ_castSucc _

theorem maskCard_permMask {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    maskCard n (permMask n σ s) = maskCard n s :=
  Fintype.sum_equiv σ _ _ fun i ↦ by rw [testBit_permMask _ _ i.2]

/-! ## Only adding a vertex of least degree -/

/-- Would the new vertex have least degree in the extension?  Every graph has a vertex of least
degree, so insisting on this loses nothing — and it throws away most of the masks. -/
def minDegOk (n c s : ℕ) : Bool :=
  decide (∀ i : Fin n,
    maskCard n s ≤ deg (graphOfCode n c).Adj i + (if s.testBit i.1 then 1 else 0))

theorem minDegOk_permMask {n c s : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ autGroup n (graphOfCode n c).Adj) (h : minDegOk n c s = true) :
    minDegOk n c (permMask n σ s) = true := by
  simp only [minDegOk, decide_eq_true_eq] at h ⊢
  intro i
  rw [maskCard_permMask, testBit_permMask _ _ i.2, ← deg_of_mem_autGroup hσ i]
  exact h (σ i)

/-- The masks actually tried: orbit representatives that keep the new vertex of least degree. -/
def redMasks (n c : ℕ) : List ℕ := (symMasks n c).filter (minDegOk n c)

/-- **Nothing is lost by insisting on least degree either.**  Delete a vertex of least degree
from a graph on `n+1` vertices: what is left is a graph on `n` vertices, and the mask that puts
the deleted vertex back passes both tests. -/
theorem redMasks_complete : MasksComplete redMasks := by
  intro n adj hs hl
  obtain ⟨v, -, hv⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1))) (deg adj) ⟨0, Finset.mem_univ _⟩
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.swap v (Fin.last n) with hπ
  set adjπ : Fin (n + 1) → Fin (n + 1) → Bool := fun a b ↦ adj (π a) (π b) with hadjπ
  have hsπ : ∀ i j, adjπ i j = adjπ j i := fun i j ↦ hs _ _
  have hlπ : ∀ i, adjπ i i = false := fun i ↦ hl _
  set adj' : Fin n → Fin n → Bool := restrict adjπ with hadj'
  have hs' : ∀ i j, adj' i j = adj' j i := fun i j ↦ hsπ _ _
  have hl' : ∀ i, adj' i i = false := fun i ↦ hlπ _
  set c : ℕ := canonCode n adj' with hc
  set σ : Equiv.Perm (Fin n) := canonPerm n adj' with hσdef
  set s : ℕ := lastMask n adjπ with hsdef
  -- the bits of the mask, and the degrees they contribute to
  have hbit : ∀ u : Fin n, s.testBit u.1 = adjπ (σ u).castSucc (Fin.last n) :=
    fun u ↦ testBit_lastMask u.2
  have hdegπ : ∀ i : Fin (n + 1), deg adjπ i = deg adj (π i) := deg_perm adj π
  -- the new vertex's degree is the degree of `v`
  have hcard : maskCard n s = deg adj v := by
    rw [← Equiv.swap_apply_right v (Fin.last n), ← hπ, ← hdegπ, deg_castSucc_split,
      if_neg (by simp [hlπ]), Nat.add_zero, maskCard]
    refine (Fintype.sum_equiv σ _ _ fun i ↦ ?_).trans rfl
    rw [hbit i, hsπ]
  -- and the old vertices keep theirs
  have hdeg : ∀ u : Fin n,
      deg (graphOfCode n c).Adj u + (if s.testBit u.1 then 1 else 0) = deg adj (π (σ u).castSucc) := by
    intro u
    have hgc : (graphOfCode n c).Adj = fun a b ↦ adj' (σ a) (σ b) :=
      funext fun i ↦ funext fun j ↦ by
        rw [hc, adj_graphOfCode_canonCode hs' hl' i j, canonAdj_apply]
    rw [hgc, deg_perm, hbit u, ← hdegπ, deg_castSucc_split]
    rfl
  have hmin : minDegOk n c s = true := by
    simp only [minDegOk, decide_eq_true_eq]
    intro u
    rw [hcard, hdeg u]
    exact hv _ (Finset.mem_univ _)
  -- reduce the mask to its orbit representative
  obtain ⟨τ, hτ, hmem⟩ := exists_mem_symMasks (c := c) (lastMask_lt n adjπ)
  refine ⟨adj', hs', hl', permMask n τ s, ?_, ?_⟩
  · rw [redMasks, List.mem_filter]
    exact ⟨hmem, minDegOk_permMask hτ hmin⟩
  · rw [canonCode_extendCode_permMask (canonCode_lt n adj') τ hτ, canonCode_extend adjπ hsπ hlπ,
      canonCode_eq, canonCode_eq, canonAdj_eq_of_equiv (A := adjπ) (B := adj) π fun _ _ ↦ rfl]

theorem symMasks_complete : MasksComplete symMasks := fun n adj hs hl ↦ by
  obtain ⟨τ, hτ, hmem⟩ := exists_mem_symMasks (c := canonCode n (restrict adj)) (lastMask_lt n adj)
  exact ⟨restrict adj, fun _ _ ↦ hs _ _, fun _ ↦ hl _, permMask n τ (lastMask n adj), hmem, by
    rw [canonCode_extendCode_permMask (canonCode_lt _ _) τ hτ, canonCode_extend adj hs hl]⟩

/-! ## The fast enumerator

`allMasks` offers every neighbourhood; `symMasks` keeps one per orbit of the automorphism group of
the graph being extended; `redMasks` additionally insists that the new vertex be one of least
degree.  All three enumerate the same list — they differ only in how many candidates they
canonicalise, which is where all the time goes:

| candidates at `n = 8` | `allMasks` | `symMasks` | `redMasks` |
| :-- | --: | --: | --: |
| | 133632 | 79454 | 18329 |
-/

/-- All graphs on `n` vertices, one vertex at a time, with orbit reduction. -/
def enumCodesSym : ℕ → List ℕ := enumCodesOf symMasks

theorem enumCodesSym_eq (n : ℕ) : enumCodesSym n = enumCodes n :=
  enumCodesOf_eq symMasks_complete n

/-- **The canonical codes of all graphs on `n` vertices** — the recommended enumerator: extend one
vertex at a time, offering only the least-degree orbit representatives. -/
def enumCodesFast : ℕ → List ℕ := enumCodesOf redMasks

/-- **The fast enumerator computes the same list as the brute-force sweep** — not merely the same
set: both are strictly increasing lists of codes with the same members. -/
theorem enumCodesFast_eq (n : ℕ) : enumCodesFast n = enumCodes n :=
  enumCodesOf_eq redMasks_complete n

/-- **All graphs on `n` vertices, one per isomorphism class** — the fast version.

Everything proved about `enumerate` holds of it verbatim, by `enumerateFast_eq`. -/
def enumerateFast (n : ℕ) : List CGraph := (enumCodesFast n).map (graphOfCode n)

theorem enumerateFast_eq (n : ℕ) : enumerateFast n = enumerate n := by
  rw [enumerateFast, enumerate, enumCodesFast_eq]

theorem exists_mem_enumerateFast (G : CGraph) {n : ℕ} (hn : Fintype.card G.V = n) :
    ∃ H ∈ enumerateFast n, Nonempty (G ≃cg H) := by
  rw [enumerateFast_eq]; exact exists_mem_enumerate G hn

theorem enumerateFast_pairwise_not_iso (n : ℕ) :
    (enumerateFast n).Pairwise fun G H ↦ ¬Nonempty (G ≃cg H) := by
  rw [enumerateFast_eq]; exact enumerate_pairwise_not_iso n

/-! ## Sanity check

The counts are OEIS A000088, the number of graphs on `n` unlabelled vertices.  Larger `n` is
checked by `lake exe enumbench`, which reaches `n = 7`: 1044 classes out of `2 ^ 21` codes.
-/

#guard ((List.range 5).map fun n ↦ (enumCodes n).length) == [1, 1, 2, 4, 11]
#guard ((List.range 7).map fun n ↦ (enumCodesExt n).length) == [1, 1, 2, 4, 11, 34, 156]
#guard ((List.range 8).map fun n ↦ (enumCodesFast n).length) == [1, 1, 2, 4, 11, 34, 156, 1044]

end CGraph.Enum
