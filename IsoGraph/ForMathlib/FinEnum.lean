import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Sym
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Equiv.Fin.Basic
import Std.Data.HashMap

/-!
# Faster enumerations

`FinEnum α` is `Mathlib`'s "α is finite *and* comes with a chosen bijection `α ≃ Fin (card α)`".
It is exactly the structure a graph algorithm wants — an index for every vertex, with no appeal to
choice — but the instances Mathlib ships are written for convenience, not for speed: nearly all of
them go through `FinEnum.ofList`, which materialises the whole type as a `List` and then
`dedup`s it, so building the instance is quadratic and every `equiv` query afterwards is a linear
`List.idxOf` scan.  For `FinEnum (Fin n)` — the case that matters most, since it is where every
other instance bottoms out — that is a list of `n` elements built and searched to compute a
function that ought to be the identity.

This file replaces the instances on the way to `Fin n` with direct ones.  They are all at priority
2000, so they win instance search against Mathlib's; nothing is removed, and the two agree up to
`FinEnum.card_unique`, but a term elaborated here will consistently use the fast ones.

| instance          | Mathlib                            | here                                |
| ----------------- | ---------------------------------- | ----------------------------------- |
| `Fin n`           | `ofList (List.finRange n)`         | `Equiv.refl`                        |
| `α × β`           | `ofList (toList α ×ˢ toList β)`    | `finProdFinEquiv`                   |
| `α ⊕ β`           | `ofList (map inl ++ map inr)`      | `finSumFinEquiv`                    |
| `{x // p x}`      | `ofList (filterMap …)`, with dedup | `ofNodupList`, no dedup             |
| `{s : Finset α // s.card = k}` | the above over `FinEnum (Finset α)` | `List.sublistsLen`     |

The last of these is the one that changes an asymptotic.  Mathlib reaches the `k`-element subsets
of `α` by way of `FinEnum (Finset α)`, which lists all `2 ^ card α` subsets and deduplicates them
against each other, and only then filters; `kSubsetList` generates the `C(card α, k)` that survive
and nothing else.  For the Kneser graph `K(10,5)` that is 252 vertices built directly against 1024
subsets deduplicated in ~500 000 comparisons, and the gap widens with `n`.

`Sym2` gets an instance too — not a fast one, there is nothing to exploit, but Mathlib has none
and the line graph cannot be built without it.
-/

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v}

namespace FinEnum

/-! ## The base case -/

/-- `Fin n` is its own enumeration.  Mathlib's instance builds `List.finRange n` and answers
`equiv i` by searching it; this one answers `i`. -/
instance (priority := 2000) instFin (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _

@[simp] theorem card_fin' (n : ℕ) : card (Fin n) = n := rfl

@[simp] theorem equiv_fin (n : ℕ) (i : Fin n) : equiv i = i := rfl

@[simp] theorem equiv_fin_symm (n : ℕ) (i : Fin n) : (equiv (α := Fin n)).symm i = i := rfl

/-! ## Sums and products

Both of these are `O(1)` to build and `O(1)` to query, against Mathlib's `O(card²)` and
`O(card)`. -/

instance (priority := 2000) instProd [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  card := card α * card β
  equiv := (Equiv.prodCongr equiv equiv).trans finProdFinEquiv

@[simp] theorem card_prod' [FinEnum α] [FinEnum β] : card (α × β) = card α * card β := rfl

instance (priority := 2000) instSum [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  card := card α + card β
  equiv := (Equiv.sumCongr equiv equiv).trans finSumFinEquiv

@[simp] theorem card_sum' [FinEnum α] [FinEnum β] : card (α ⊕ β) = card α + card β := rfl

/-! ## Subtypes

The list of elements satisfying `p` is already duplicate-free, being a `filterMap` of the
duplicate-free `toList α` along a partial function that only ever forgets a proof.  Mathlib's
instance throws that away and calls `dedup`, which compares every pair. -/

theorem nodup_subtypeList (p : α → Prop) [FinEnum α] [DecidablePred p] :
    ((toList α).filterMap fun x ↦ if h : p x then some (⟨x, h⟩ : {x // p x}) else none).Nodup := by
  refine List.Nodup.filterMap (fun a a' b hb hb' ↦ ?_) (nodup_toList (α := α))
  simp only [Option.mem_def] at hb hb'
  by_cases ha : p a
  · by_cases ha' : p a'
    · rw [dif_pos ha] at hb
      rw [dif_pos ha'] at hb'
      exact congrArg Subtype.val (Option.some.inj (hb.trans hb'.symm))
    · rw [dif_neg ha'] at hb'; exact absurd hb' (by simp)
  · rw [dif_neg ha] at hb; exact absurd hb (by simp)

instance (priority := 2000) instSubtype [FinEnum α] (p : α → Prop) [DecidablePred p] :
    FinEnum {x // p x} :=
  ofNodupList ((toList α).filterMap fun x ↦ if h : p x then some ⟨x, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa) (nodup_subtypeList p)

/-! ## Subsets of a fixed size

The vertex type of a Kneser graph.  Going through `FinEnum (Finset α)` costs `2 ^ card α` — it is
the powerset that gets listed, and then deduplicated against itself — where the `k`-element
subsets can be generated directly, as the sublists of `toList α` of length `k`.  What has to be
checked is that this loses nothing and repeats nothing: distinct sublists of a duplicate-free list
have distinct element sets, which is the lemma below. -/

/-- A sublist of a duplicate-free list is determined by the set of its elements: two sublists of
the same nodup list that are permutations of each other are equal.  Order is inherited from the
ambient list, so there is only one way to lay out a given set of its elements. -/
theorem _root_.List.eq_of_sublist_of_perm {l l₁ l₂ : List α} (hn : l.Nodup)
    (h₁ : l₁.Sublist l) (h₂ : l₂.Sublist l) (hp : l₁.Perm l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => rw [List.sublist_nil.1 h₁, List.sublist_nil.1 h₂]
  | cons a t ih =>
    rw [List.nodup_cons] at hn
    rcases List.sublist_cons_iff.1 h₁ with h₁' | ⟨r₁, rfl, hr₁⟩
    · rcases List.sublist_cons_iff.1 h₂ with h₂' | ⟨r₂, rfl, hr₂⟩
      · exact ih hn.2 h₁' h₂' hp
      · exact absurd (h₁'.subset (hp.mem_iff.2 (by simp))) hn.1
    · rcases List.sublist_cons_iff.1 h₂ with h₂' | ⟨r₂, rfl, hr₂⟩
      · exact absurd (h₂'.subset (hp.mem_iff.1 (by simp))) hn.1
      · exact congrArg (a :: ·) (ih hn.2 hr₁ hr₂ hp.cons_inv)

/-- The `k`-element subsets of an enumerated type, each listed once. -/
def kSubsetList (α : Type u) [FinEnum α] (k : ℕ) : List {s : Finset α // s.card = k} :=
  ((toList α).sublistsLen k).pmap (fun l h ↦ ⟨l.toFinset, h⟩) fun _ hl ↦ by
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.1 hl
    rw [List.toFinset_card_of_nodup (List.Nodup.sublist hsub nodup_toList), hlen]

theorem length_kSubsetList (α : Type u) [FinEnum α] (k : ℕ) :
    (kSubsetList α k).length = (card α).choose k := by
  rw [kSubsetList, List.length_pmap, List.length_sublistsLen]
  congr 1
  simp [toList]

theorem mem_kSubsetList (α : Type u) [FinEnum α] {k : ℕ} (s : {s : Finset α // s.card = k}) :
    s ∈ kSubsetList α k := by
  obtain ⟨s, hs⟩ := s
  have hsub : ((toList α).filter (fun a ↦ decide (a ∈ s))).Sublist (toList α) :=
    List.filter_sublist
  have hnd : ((toList α).filter (fun a ↦ decide (a ∈ s))).Nodup :=
    List.Nodup.sublist hsub nodup_toList
  have hfin : ((toList α).filter (fun a ↦ decide (a ∈ s))).toFinset = s := by
    ext a; simp [mem_toList]
  have hlen : ((toList α).filter (fun a ↦ decide (a ∈ s))).length = k := by
    rw [← List.toFinset_card_of_nodup hnd, hfin, hs]
  rw [kSubsetList, List.mem_pmap]
  exact ⟨_, List.mem_sublistsLen.2 ⟨hsub, hlen⟩, Subtype.ext hfin⟩

theorem nodup_kSubsetList (α : Type u) [FinEnum α] (k : ℕ) : (kSubsetList α k).Nodup := by
  rw [kSubsetList, List.pmap_eq_map_attach]
  refine List.Nodup.map_on ?_
    (List.nodup_attach.2 (List.nodup_sublistsLen k (nodup_toList (α := α))))
  rintro ⟨l₁, hm₁⟩ - ⟨l₂, hm₂⟩ - heq
  obtain ⟨hs₁, -⟩ := List.mem_sublistsLen.1 hm₁
  obtain ⟨hs₂, -⟩ := List.mem_sublistsLen.1 hm₂
  have hfin : l₁.toFinset = l₂.toFinset := congrArg Subtype.val heq
  exact Subtype.ext (List.eq_of_sublist_of_perm nodup_toList hs₁ hs₂
    (List.perm_of_nodup_nodup_toFinset_eq (List.Nodup.sublist hs₁ nodup_toList)
      (List.Nodup.sublist hs₂ nodup_toList) hfin))

/-! ### Answering a query without a scan

`ofNodupList` — the constructor every list-based enumeration goes through, this one included —
answers `equiv x` with `List.idxOf`, a scan of the whole list.  For the `k`-element subsets that
is `C(card α, k)` `Finset` comparisons on *every* query, and it is what makes `CGraph.cache`
slower than no cache at all on a Kneser graph: the two `equiv` calls a cached query pays cost far
more than the adjacency function they replace.

`subsetMask` gives a subset a numeric key, and the key determines the subset, so a table from keys
to positions answers a query with one lookup.  The table is built once, when the enumeration is
built, because it is captured by the closure stored in the structure's field; an implementation
taking the subset and the list as two arguments would rebuild it on every query.

The fast version is attached with `@[implemented_by]`, so it is what runs, while the list scan
stays what the kernel sees and what every proof is about.  The two agree: `equiv.symm` is the same
list lookup in both, and the table sends a subset's mask to its position in that same list.  The
`native_decide` checks below run the compiled `equiv` against the kernel's `equiv.symm`. -/

/-- The bitmask of a subset of an enumerated type: the sum of `2 ^ i` over the indices of its
elements.  Distinct subsets have distinct masks, so this is a key a hash table can take where the
subsets themselves cannot be hashed. -/
def subsetMask [FinEnum α] (s : Finset α) : ℕ := ∑ x ∈ s, 2 ^ (equiv x).1

section KSubset

/-! `@[implemented_by]` compares the two declarations' types as terms, down to the names of their
binders — and a binder written out twice is *not* the same binder, since each carries the macro
scope of the declaration it was written in.  Taking both signatures from one `variable` line is
what makes them equal. -/

variable (α : Type u) [inst : FinEnum α] (k : ℕ)

-- Both of these are deliberately semireducible: `kSubsetEnum` has to stay an opaque constant
-- for the `@[implemented_by]` redirection below to survive into compiled code, and making it
-- unfold at instance-synthesis transparency costs an order of magnitude at run time.
set_option warn.classDefReducibility false

/-- `kSubsetEnum`, with the position table built once and hashed. -/
private unsafe def kSubsetEnumImpl :
    FinEnum.{u + 1} {s : Finset α // s.card = k} :=
  let l := kSubsetList α k
  let base : FinEnum {s : Finset α // s.card = k} :=
    ofNodupList l (mem_kSubsetList α) (nodup_kSubsetList α k)
  let table : Std.HashMap ℕ ℕ :=
    l.zipIdx.foldl (fun m p ↦ m.insert (subsetMask p.1.1) p.2)
      (Std.HashMap.emptyWithCapacity l.length)
  { base with
    equiv :=
      { toFun := fun s ↦ ⟨table.getD (subsetMask s.1) 0, lcProof⟩
        invFun := fun i ↦ base.equiv.symm i
        left_inv := lcProof
        right_inv := lcProof } }

/-- The subsets of a fixed size, enumerated without going through the powerset. -/
@[implemented_by kSubsetEnumImpl]
def kSubsetEnum :
    FinEnum.{u + 1} {s : Finset α // s.card = k} :=
  ofNodupList (kSubsetList α k) (mem_kSubsetList α) (nodup_kSubsetList α k)

/-- The enumeration of the `k`-element subsets, as an instance.  The work is in `kSubsetEnum`,
which is where the fast implementation is attached: an `instance` and a `def` do not elaborate
their (identical) signatures to quite the same term, and `@[implemented_by]` compares terms. -/
instance (priority := 3000) instFinsetCard :
    FinEnum {s : Finset α // s.card = k} :=
  kSubsetEnum α k

end KSubset

/-- The compiled `equiv` against the kernel's `equiv.symm`.  Both paths share `equiv.symm` — it is
the same lookup in the same list — so this says that the table sends a subset to the position the
scan would have found, which is the whole of what `@[implemented_by]` is taking on trust.
`native_decide` is the point: `decide` would run the scan and check nothing. -/
example : ∀ i : Fin (FinEnum.card {s : Finset (Fin 6) // s.card = 3}),
    FinEnum.equiv (FinEnum.equiv.symm i) = i := by native_decide

example : ∀ i : Fin (FinEnum.card {s : Finset (Fin 8) // s.card = 5}),
    FinEnum.equiv (FinEnum.equiv.symm i) = i := by native_decide

@[simp] theorem card_finsetCard (α : Type u) [FinEnum α] (k : ℕ) :
    card {s : Finset α // s.card = k} = (card α).choose k :=
  length_kSubsetList α k

/-! ## Everything else -/

instance (priority := 2000) instBool : FinEnum Bool where
  card := 2
  equiv := finTwoEquiv.symm

@[simp] theorem card_bool : card Bool = 2 := rfl

/-- Unordered pairs.  No structure to exploit — the list of pairs has to be deduplicated — but
without this instance a graph cannot name its own edges, which is what the line graph needs. -/
instance instSym2 [FinEnum α] : FinEnum (Sym2 α) :=
  ofList ((toList α ×ˢ toList α).map fun p ↦ s(p.1, p.2)) <| by
    intro e
    induction e with
    | _ x y => exact List.mem_map.2 ⟨(x, y), List.mem_product.2 ⟨mem_toList x, mem_toList y⟩, rfl⟩

/-! ## Cardinalities

`card_eq_fintypeCard` turns any of Mathlib's `Fintype.card` computations into one about `card`;
these are the ones this development uses often enough to want by name. -/

theorem card_sigma {ι : Type u} [FinEnum ι] (F : ι → Type v) [∀ i, FinEnum (F i)] :
    card (Σ i, F i) = ∑ i, card (F i) := by
  rw [card_eq_fintypeCard, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ ↦ (card_eq_fintypeCard (α := F i)).symm

theorem card_subtype' [FinEnum α] (p : α → Prop) [DecidablePred p] :
    card {x // p x} = ((toList α).filterMap fun x ↦
      if h : p x then some (⟨x, h⟩ : {x // p x}) else none).length := rfl

theorem card_fun [FinEnum α] [FinEnum β] : card (α → β) = card β ^ card α := by
  rw [card_eq_fintypeCard, Fintype.card_fun, ← card_eq_fintypeCard (α := α),
    ← card_eq_fintypeCard (α := β)]

theorem card_subtype [FinEnum α] (p : α → Prop) [DecidablePred p] :
    card {x // p x} = (Finset.univ.filter p).card := by
  rw [card_eq_fintypeCard, Fintype.card_subtype]

@[simp] theorem card_option [FinEnum α] : card (Option α) = card α + 1 := by
  rw [card_eq_fintypeCard, Fintype.card_option, ← card_eq_fintypeCard (α := α)]

/-- The counterpart of `Finset.card_univ`.  A `FinEnum` gives a `Fintype`, so Mathlib's counting
lemmas all apply, but they are stated with `Fintype.card`; these two are the ones that come up
often enough that translating them by hand every time is a nuisance. -/
@[simp] theorem card_univ [FinEnum α] : (Finset.univ : Finset α).card = card α := by
  rw [Finset.card_univ, card_eq_fintypeCard]

theorem card_le [FinEnum α] (s : Finset α) : s.card ≤ card α :=
  (Finset.card_le_univ s).trans_eq card_univ

/-! ### Counting a map

The four `Fintype` lemmas this development reaches for, restated for `card`.  Each is the Mathlib
one with `card_eq_fintypeCard` on both sides; they are here because a `CGraph` states its vertex
count with `card`, so a homomorphism argument that ends in "and the cardinalities agree" would
otherwise have to change units in the middle. -/

theorem card_le_of_injective [FinEnum α] [FinEnum β] (f : α → β) (h : Function.Injective f) :
    card α ≤ card β := by
  rw [card_eq_fintypeCard, card_eq_fintypeCard]; exact Fintype.card_le_of_injective f h

theorem card_le_of_surjective [FinEnum α] [FinEnum β] (f : α → β) (h : Function.Surjective f) :
    card β ≤ card α := by
  rw [card_eq_fintypeCard, card_eq_fintypeCard]; exact Fintype.card_le_of_surjective f h

theorem bijective_iff_injective_and_card [FinEnum α] [FinEnum β] (f : α → β) :
    Function.Bijective f ↔ Function.Injective f ∧ card α = card β := by
  rw [card_eq_fintypeCard, card_eq_fintypeCard]
  exact Fintype.bijective_iff_injective_and_card f

theorem bijective_iff_surjective_and_card [FinEnum α] [FinEnum β] (f : α → β) :
    Function.Bijective f ↔ Function.Surjective f ∧ card α = card β := by
  rw [card_eq_fintypeCard, card_eq_fintypeCard]
  exact Fintype.bijective_iff_surjective_and_card f

/-- `card_eq_fintypeCard` against *any* `Fintype` instance, not just the one the `FinEnum`
induces.  `Fintype.card` does not depend on the instance, but the two are only propositionally
equal, and a Mathlib counting lemma will have been stated with the canonical instance. -/
theorem card_eq_fintypeCard' [FinEnum α] [Fintype α] : card α = Fintype.card α :=
  card_eq_fintypeCard.trans (Fintype.card_congr' rfl)

end FinEnum

/-- Two `Fintype` instances on the same type give the same `Finset.univ`.  Instances that are
propositionally but not definitionally equal are the price of a structure that carries its own
enumeration: a `CGraph` on `G.V × H.V` counts with the `Fintype` its `FinEnum` induces, where a
Mathlib lemma about products counts with `instFintypeProd`. -/
theorem Finset.univ_inst_eq {α : Type u} (i j : Fintype α) :
    @Finset.univ α i = @Finset.univ α j :=
  congrArg (fun k ↦ @Finset.univ α k) (Subsingleton.elim i j)

/-- The underlying multiset of `Finset.univ`, again independent of the instance.  Mathlib's
degree-sum lemmas are stated about `Finset.univ.val`, and a `CGraph`'s degree multiset is built
from the `Finset.univ` of its own instance. -/
theorem Finset.univ_val_inst_eq {α : Type u} (i j : Fintype α) :
    (@Finset.univ α i).val = (@Finset.univ α j).val :=
  congrArg Finset.val (Finset.univ_inst_eq i j)

/-- A sum over the whole type does not depend on which `Fintype` instance names it.  The
handshake lemmas of `SimpleGraph` sum over Mathlib's instance and a `CGraph` sums over its own,
so this gets used wherever the two meet. -/
theorem Finset.sum_univ_inst_eq {α : Type u} {β : Type v} [AddCommMonoid β] (i j : Fintype α)
    (f : α → β) : ∑ x ∈ @Finset.univ α i, f x = ∑ x ∈ @Finset.univ α j, f x :=
  Finset.sum_congr (Finset.univ_inst_eq i j) fun _ _ ↦ rfl
