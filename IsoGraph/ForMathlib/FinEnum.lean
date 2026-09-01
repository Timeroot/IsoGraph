import Mathlib.Algebra.BigOperators.Fin
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
| `α → β`           | `ofList (Pi.enum …)`, with dedup   | `hornerSum`, in base `card β`       |
| `{x // p x}`      | `ofList (filterMap …)`, with dedup | `ofNodupBlocks`, no dedup           |
| `{s : Finset α // s.card = k}` | the above over `FinEnum (Finset α)` | `List.sublistsLen`     |
| `Sym2 α`          | none                               | `sym2List`, no dedup                |

The Kneser one changes an asymptotic.  Mathlib reaches the `k`-element subsets of `α` by way of
`FinEnum (Finset α)`, which lists all `2 ^ card α` subsets and deduplicates them against each
other, and only then filters; `kSubsetList` generates the `C(card α, k)` that survive and nothing
else.  For the Kneser graph `K(10,5)` that is 252 vertices built directly against 1024 subsets
deduplicated in ~500 000 comparisons, and the gap widens with `n`.

`Sym2 α` Mathlib has no instance for at all, and the line graph cannot be built without one.

The last three have no arithmetic to be written in — there is no formula for "the `i`-th element
satisfying `p`" — so they still enumerate by listing, and pay for the list in the way `## Indexed
access` below describes.
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

/-- Decide `a = b` by comparing indices.  See `instDecidableEqArrow` below for when this is
worth doing. -/
def decEqOfEquiv {n : ℕ} (e : α ≃ Fin n) : DecidableEq α :=
  fun _ _ ↦ decidable_of_iff _ e.apply_eq_iff_eq

/-! ## Sums and products

Both of these are `O(1)` to build and `O(1)` to query, against Mathlib's `O(card²)` and
`O(card)`.

The obvious way to write them is `(Equiv.prodCongr equiv equiv).trans finProdFinEquiv`, and the
index it computes is the one below — but a composite `Equiv` is a composite at *run* time too.
Asking it for one index calls the `trans` closure, which calls the `prodCongr` closure, which
allocates a pair of `Fin`s for `finProdFinEquiv` to take apart again: six closures and two
allocations to multiply and add. Writing the arithmetic out takes a table lookup on a
`Fin 4 × Fin 4` from 90 ns to 58, against 24 for the array read underneath it, and that lookup is
what the searches spend their time on.

Nothing changes but the speed: the index is `finProdFinEquiv`'s, so the enumeration order, the
`toList`, and every `decide` that ever ran against these instances are the same. -/

private theorem prod_lt [FinEnum α] [FinEnum β] (a : Fin (card α)) (b : Fin (card β)) :
    b.val + card β * a.val < card α * card β :=
  calc b.val + card β * a.val
      < card β + card β * a.val := by omega
    _ = card β * (a.val + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ card β * card α := Nat.mul_le_mul le_rfl a.isLt
    _ = card α * card β := Nat.mul_comm _ _

private theorem card_snd_pos [FinEnum α] [FinEnum β] (i : Fin (card α * card β)) : 0 < card β :=
  Nat.pos_of_ne_zero fun h ↦ absurd i.isLt (by simp [h])

private theorem prod_div_lt [FinEnum α] [FinEnum β] (i : Fin (card α * card β)) :
    i.val / card β < card α :=
  (Nat.div_lt_iff_lt_mul (card_snd_pos i)).mpr i.isLt

instance (priority := 2000) instProd [FinEnum α] [FinEnum β] : FinEnum (α × β) where
  card := card α * card β
  equiv :=
    { toFun := fun p ↦ ⟨(equiv p.2).val + card β * (equiv p.1).val, prod_lt _ _⟩
      invFun := fun i ↦
        (equiv.symm ⟨i.val / card β, prod_div_lt i⟩,
          equiv.symm ⟨i.val % card β, Nat.mod_lt _ (card_snd_pos i)⟩)
      left_inv := fun p ↦ by
        dsimp only
        have hb := (equiv p.2).isLt
        have hpos : 0 < card β := Nat.lt_of_le_of_lt (Nat.zero_le _) hb
        refine Prod.ext ?_ ?_ <;>
          simp only [Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left,
            Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb, Nat.zero_add]
        · exact congrArg _ (Fin.ext rfl) |>.trans (Equiv.symm_apply_apply _ _)
        · exact congrArg _ (Fin.ext rfl) |>.trans (Equiv.symm_apply_apply _ _)
      right_inv := fun i ↦ by
        dsimp only
        simp only [Equiv.apply_symm_apply]
        exact Fin.ext (Nat.mod_add_div _ _) }

@[simp] theorem card_prod' [FinEnum α] [FinEnum β] : card (α × β) = card α * card β := rfl

instance (priority := 2000) instSum [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) where
  card := card α + card β
  equiv :=
    { toFun := fun s ↦ s.elim
        (fun a ↦ ⟨(equiv a).val, Nat.lt_add_right _ (equiv a).isLt⟩)
        (fun b ↦ ⟨card α + (equiv b).val, Nat.add_lt_add_left (equiv b).isLt _⟩)
      invFun := fun i ↦
        if h : i.val < card α then .inl (equiv.symm ⟨i.val, h⟩)
        else .inr (equiv.symm ⟨i.val - card α, by omega⟩)
      left_inv := fun s ↦ by
        dsimp only
        cases s with
        | inl a =>
          rw [Sum.elim_inl, dif_pos (equiv a).isLt]
          exact congrArg _ (congrArg _ (Fin.ext rfl) |>.trans (Equiv.symm_apply_apply _ _))
        | inr b =>
          rw [Sum.elim_inr, dif_neg (by simp)]
          exact congrArg _ (congrArg _ (Fin.ext (by simp)) |>.trans (Equiv.symm_apply_apply _ _))
      right_inv := fun i ↦ by
        dsimp only
        by_cases h : i.val < card α
        · rw [dif_pos h]; exact Fin.ext (by simp)
        · rw [dif_neg h]; exact Fin.ext (by simp; omega) }

@[simp] theorem card_sum' [FinEnum α] [FinEnum β] : card (α ⊕ β) = card α + card β := rfl

/-! ## Functions

A hypercube's vertices are the functions `Fin n → Bool`, and Mathlib enumerates a function type
the way it enumerates everything else: list all `card β ^ card α` of them and deduplicate.  A
single comparison there is a loop over the domain, so the list costs `card β ^ (2 * card α)`
comparisons of coordinates to build and `card β ^ card α` of them to search on every `equiv`
query — for `Fin 4 → Bool` that is more work than scanning the adjacency of the graph the
enumeration is indexing.

A function into `Fin (card β)` is a numeral written in base `card β`, and `finFunctionFinEquiv`
is that reading.  Nothing is listed and nothing is searched.

Its `toFun` is `∑ i, f i * card β ^ i`, though, and that sum is expensive out of proportion to
what it says: `Finset.univ` on the domain is `List.finRange (card α)` built afresh on every
query, `card β ^ i` is recomputed from scratch at each digit rather than carried along, and the
composition with `arrowCongr` wraps the whole thing in two more closures.  `hornerSum` below is
the same numeral read by Horner's rule — one multiplication and one addition per digit, no list,
no powers — and `arrowIdx_eq` is the proof that it is the same number, so the enumeration is
again unchanged.  A table lookup on `Fin 4 → Bool` costs 1190 ns instead of 2450.

The `invFun` is the other half of that, and it matters more.  `finFunctionFinEquiv.symm` reads
digit `a` as `i / card β ^ a % card β`, and `arrowCongr` wraps it in two further `Equiv`s; where
the encoding runs once per vertex, this runs on *every application of one* — a hypercube's
adjacency query applies two vertices `n` times each.  `arrowDecode` below reaches the digit with
`digit`, which divides rather than raising to the power and shifts when the base is two, and
`arrowDecode_eq` is the proof that it is the same digit.  Over the 256 vertices of `Q₈`, a million
applications cost 505 ms through the composite and 48 through this, and a full sweep of the
hypercube's adjacency drops from 365 ms to 68.

Equality is the same story told about `Fintype.decidablePiFintype`, which decides `f = g` by
folding a pointwise check over `Finset.univ` of the domain — structural, and started again from
the top for every pair, where the adjacency scans here compare the same `card α ^ 2` pairs of
vertices over and over.  Comparing indices is cheaper in a way that compounds: `equiv f` is a
single term, so the kernel evaluates it once for `f` and answers every later comparison that
mentions `f` out of its cache, which turns a quadratic number of structural comparisons into a
linear number of `equiv` queries and a quadratic number of comparisons of numbers.  On the sixteen
vertices of `Q₄`, 184 ms of kernel time against 74.

It is a global instance and not the `decEq` field of `instArrow`, because the two have to agree:
`homExponential` decides `f ≠ f'` where the type is spelled `H.V → G.V`, `homExponential_adj`
states the same thing where it is spelled `(G ^hg H).V`, and that lemma is `rfl` only if the two
spellings find the same instance.  Overriding the field alone leaves search finding Mathlib's at
the first site and this one at the second.

The listed enumerations at the end of the file could not do this in any case: their `equiv` is
`List.idxOf`, a search that uses `DecidableEq α`, so it would call itself. -/

/-- `∑ i < k, g (j + i) * b ^ i`, read by Horner's rule from the most significant digit down. -/
private def hornerSum (b : ℕ) (g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, j => g j + b * hornerSum b g k (j + 1)

private theorem hornerSum_eq (b : ℕ) (g : ℕ → ℕ) :
    ∀ k j, hornerSum b g k j = ∑ i ∈ Finset.range k, g (j + i) * b ^ i
  | 0, _ => rfl
  | k + 1, j => by
    rw [hornerSum, hornerSum_eq b g k (j + 1), Finset.mul_sum,
      Finset.sum_range_succ' (fun i ↦ g (j + i) * b ^ i) k]
    refine (Nat.add_comm _ _).trans (congrArg₂ _ (Finset.sum_congr rfl fun i _ ↦ ?_) (by simp))
    rw [show j + 1 + i = j + (i + 1) by omega, Nat.pow_succ']
    exact Nat.mul_left_comm _ _ _

/-- The index of `f` in the enumeration of `α → β`: the digits `equiv (f a)`, written in base
`card β` with the `a` of index `0` least significant. -/
private def arrowIdx [FinEnum α] [FinEnum β] (f : α → β) : ℕ :=
  hornerSum (card β)
    (fun j ↦ if h : j < card α then (equiv (f (equiv.symm ⟨j, h⟩))).val else 0) (card α) 0

private theorem arrowIdx_eq [FinEnum α] [FinEnum β] (f : α → β) :
    arrowIdx f = ∑ i : Fin (card α), (equiv (f (equiv.symm i))).val * card β ^ (i : ℕ) := by
  rw [Finset.sum_fin_eq_sum_range, arrowIdx, hornerSum_eq]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  simp [hi]

private theorem arrowIdx_lt [FinEnum α] [FinEnum β] (f : α → β) :
    arrowIdx f < card β ^ card α := by
  rw [arrowIdx_eq]
  exact (finFunctionFinEquiv fun i ↦ equiv (f (equiv.symm i))).isLt

/-- The `j`-th digit of `i` in base `b`, reached by dividing `j` times. -/
private def digitAux (b : ℕ) : ℕ → ℕ → ℕ
  | i, 0 => i % b
  | i, j + 1 => digitAux b (i / b) j

private theorem digitAux_eq (b : ℕ) : ∀ i j, digitAux b i j = i / b ^ j % b
  | i, 0 => by simp [digitAux]
  | i, j + 1 => by
    rw [digitAux, digitAux_eq b (i / b) j, Nat.div_div_eq_div_mul, ← pow_succ']

/-- **The `j`-th digit of `i` in base `b`.**

`i / b ^ j % b` is the same number and the obvious way to write it, but `Nat.pow` is a call into
GMP whatever it is handed, and one of those costs more than reaching the digit by dividing: on a
byte, 171 ns by the power against 52 by the descent.  Base two is the case that matters — the
vertices of a hypercube are `Fin n → Bool` — and there the digit is a shift, which is 15 ns and
does not depend on `j` at all.  Every query of a function-typed vertex reads one digit, so this is
the innermost loop of anything built on `instArrow`, and it is worth the branch. -/
private def digit (b i j : ℕ) : ℕ := if b = 2 then (i >>> j) % 2 else digitAux b i j

private theorem digit_eq (b i j : ℕ) : digit b i j = i / b ^ j % b := by
  rw [digit]
  split
  · next h => subst h; rw [Nat.shiftRight_eq_div_pow]
  · exact digitAux_eq b i j

/-- **The `a`-th coordinate of the function numbered `i`.**

This is `((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv).symm` — `arrowDecode_eq` —
written out, so that neither the four `Equiv`s nor the power stands between a vertex and its
digit.  The note above says what that is worth. -/
private def arrowDecode [FinEnum α] [FinEnum β] (i : Fin (card β ^ card α)) (a : α) : β :=
  equiv.symm ⟨digit (card β) i.1 (equiv a).1, by
    have hb : 0 < card β := by
      rcases Nat.eq_zero_or_pos (card β) with hb0 | hb
      · exfalso
        have hpos : 0 < card β ^ card α := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
        rw [hb0] at hpos
        have hα : card α = 0 := by
          by_contra hne
          rw [Nat.zero_pow (Nat.pos_of_ne_zero hne)] at hpos
          exact absurd hpos (Nat.lt_irrefl 0)
        exact absurd (equiv a).isLt (by omega)
      · exact hb
    rw [digit_eq]
    exact Nat.mod_lt _ hb⟩

private theorem arrowDecode_eq [FinEnum α] [FinEnum β] (i : Fin (card β ^ card α)) :
    arrowDecode i = ((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv).symm i := by
  funext a
  refine congrArg equiv.symm (Fin.ext ?_)
  show digit (card β) i.1 (equiv a).1 = _
  rw [digit_eq]
  exact (finFunctionFinEquiv_symm_apply_val i (equiv a)).symm

/-- The equivalence `finFunctionFinEquiv` computes, with `hornerSum` in place of its sum and
`arrowDecode` in place of its inverse. -/
private def arrowEquiv [FinEnum α] [FinEnum β] : (α → β) ≃ Fin (card β ^ card α) where
  toFun f := ⟨arrowIdx f, arrowIdx_lt f⟩
  invFun := arrowDecode
  left_inv f := (arrowDecode_eq _).trans <|
    calc ((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv).symm
            ⟨arrowIdx f, arrowIdx_lt f⟩
        = ((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv).symm
            (((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv) f) :=
          congrArg _ (Fin.ext (arrowIdx_eq f))
      _ = f := Equiv.symm_apply_apply _ _
  right_inv i := by
    rw [arrowDecode_eq]
    exact Fin.ext <| (arrowIdx_eq _).trans <| congrArg Fin.val <|
      Equiv.apply_symm_apply ((Equiv.arrowCongr equiv equiv).trans finFunctionFinEquiv) i

instance (priority := 2000) instDecidableEqArrow [FinEnum α] [FinEnum β] :
    DecidableEq (α → β) :=
  decEqOfEquiv arrowEquiv

instance (priority := 2000) instArrow [FinEnum α] [FinEnum β] : FinEnum (α → β) where
  card := card β ^ card α
  equiv := arrowEquiv

@[simp] theorem card_fun [FinEnum α] [FinEnum β] : card (α → β) = card β ^ card α := rfl

/-! ## Indexed access

The three instances below cannot be an equivalence written out in arithmetic; they enumerate by
listing, holding a duplicate-free list of the whole type and answering `equiv.symm i` with its
`i`-th entry.  A list is a linear structure, so that entry takes `i` steps to reach — and
`FinEnum.toList`, where every algorithm here starts, asks for all `card α` of them one after
another.  Nothing is shared between two different indices, so enumerating the type costs
`card α ^ 2 / 2` steps.  Compiled, that is invisible.  In the kernel, where a reduction step is
tens of microseconds, it is the dominant cost of any proof about a line graph: of the four seconds
it took to check that the line graph of the dodecahedron is the icosidodecahedron, 2.7 went on
producing its thirty vertices.

Cutting the list into blocks of sixteen replaces the one walk of length `i` by two — `i / 16`
blocks and then `i % 16` entries — and both indices are arithmetic the kernel does natively.  The
enumeration then costs about `card α * (card α / 32 + 8)`, and on the line graph of the
dodecahedron the 2.7 seconds become 310 milliseconds.

That is on the understanding that the blocked list is built once.  In the kernel it is, for free:
it mentions no index, so it is the same subterm in every query and one reduction answers for all
of them.  Compiled, nothing of the sort is automatic — `List.blocks xs.length xs` written inside
the lambda is a fresh call on every query, walking and reallocating the whole list to answer for
one entry of it, and on the 252 vertices of `K(10, 5)` that made `equiv.symm` cost 8.6 µs rather
than 0.13.  So it is `let`-bound outside the `Equiv` below, and `kSubsetEnumImpl` stores that
`Equiv`'s `invFun` field rather than the eta-expansion `fun i ↦ base.equiv.symm i`, which would
have put the whole of `base` — blocked list included — back inside a lambda.  Neither shape is one
the kernel can tell from the other. -/

/-- The `i`-th element of `l`, or `d` if there is none.  This is `List.getD`, but `List.getD` is
stated through `getElem?`, so unfolding it costs an `Option` and a bounds check at every element,
where this costs one step. -/
def _root_.List.nthD : List α → ℕ → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: l, i + 1, d => List.nthD l i d

@[simp] theorem _root_.List.nthD_nil (i : ℕ) (d : α) : List.nthD ([] : List α) i d = d := rfl

theorem _root_.List.nthD_eq_getElem :
    ∀ (l : List α) (i : ℕ) (h : i < l.length) (d : α), l.nthD i d = l[i]
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, h, d => List.nthD_eq_getElem l i (by simpa using h) d

theorem _root_.List.nthD_drop (d : α) : ∀ (n : ℕ) (l : List α) (i : ℕ),
    (l.drop n).nthD i d = l.nthD (n + i) d
  | 0, l, i => by rw [List.drop_zero, Nat.zero_add]
  | n + 1, [], i => by rw [List.drop_nil, List.nthD_nil, List.nthD_nil]
  | n + 1, a :: l, i => by
    rw [List.drop_succ_cons, List.nthD_drop d n l i, show n + 1 + i = (n + i) + 1 from by omega]
    rfl

theorem _root_.List.nthD_take (d : α) : ∀ (n : ℕ) (l : List α) (i : ℕ), i < n →
    (l.take n).nthD i d = l.nthD i d
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => by rw [List.take_nil]
  | _ + 1, _ :: _, 0, _ => by rw [List.take_succ_cons]; rfl
  | n + 1, _ :: l, i + 1, h => by
    rw [List.take_succ_cons]
    show (l.take n).nthD i d = l.nthD i d
    exact List.nthD_take d n l i (by omega)

/-- `l` cut into blocks of sixteen.  The first argument is fuel, and `l.length` is always enough
of it. -/
def _root_.List.blocks : ℕ → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, a :: l => (a :: l).take 16 :: List.blocks f ((a :: l).drop 16)

/-- Indexed access to a blocked list: find the block, then the element. -/
def _root_.List.blockNthD (bs : List (List α)) (i : ℕ) (d : α) : α :=
  (bs.nthD (i / 16) []).nthD (i % 16) d

theorem _root_.List.blockNthD_blocks (d : α) : ∀ (f : ℕ) (l : List α), l.length ≤ 16 * f →
    ∀ i : ℕ, (List.blocks f l).blockNthD i d = l.nthD i d := by
  intro f
  induction f with
  | zero =>
    intro l hl i
    rw [Nat.mul_zero, Nat.le_zero, List.length_eq_zero_iff] at hl
    subst hl
    rfl
  | succ f ih =>
    rintro (_ | ⟨a, l⟩) hl i
    · rfl
    rw [List.blocks]
    rcases Nat.lt_or_ge i 16 with h | h
    · rw [List.blockNthD, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      exact List.nthD_take d 16 (a :: l) i h
    · have hd : ((a :: l).drop 16).length ≤ 16 * f := by
        rw [List.length_drop]
        simp only [List.length_cons] at hl ⊢
        omega
      rw [List.blockNthD, show i / 16 = (i - 16) / 16 + 1 from by omega,
        show i % 16 = (i - 16) % 16 from by omega]
      show (List.blocks f ((a :: l).drop 16)).blockNthD (i - 16) d = _
      rw [ih _ hd, List.nthD_drop, show 16 + (i - 16) = i from by omega]

/-- The point of the blocking: it is the same lookup. -/
theorem _root_.List.blockNthD_blocks_self (l : List α) (i : ℕ) (hi : i < l.length) (d : α) :
    (List.blocks l.length l).blockNthD i d = l[i] := by
  rw [List.blockNthD_blocks d l.length l (by omega) i, List.nthD_eq_getElem l i hi]

/-- `FinEnum.ofNodupList`, with the list blocked.  `equiv` is unchanged — it is still the position
of an element in `xs` — and so is the enumeration order; only the walk to the `i`-th entry is. -/
@[instance_reducible]
def ofNodupBlocks [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : xs.Nodup) :
    FinEnum α :=
  let bs := List.blocks xs.length xs
  { card := xs.length
    equiv :=
      { toFun := fun x ↦ ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩
        invFun := fun i ↦ bs.blockNthD i.1
          (xs.head (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt i.2)))
        left_inv := fun x ↦ by
          show (List.blocks xs.length xs).blockNthD (xs.idxOf x) _ = x
          rw [List.blockNthD_blocks_self _ _ (by rw [List.idxOf_lt_length_iff]; exact h x)]
          simp
        right_inv := fun i ↦ by
          ext
          show xs.idxOf ((List.blocks xs.length xs).blockNthD i.1 _) = i.1
          rw [List.blockNthD_blocks_self _ _ i.2]
          simp [h'.idxOf_getElem] } }

theorem toList_ofNodupBlocks [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs)
    (h' : xs.Nodup) : @toList α (ofNodupBlocks xs h h') = xs := by
  have hEq : @toList α (ofNodupBlocks xs h h')
      = (List.finRange xs.length).map (@equiv α (ofNodupBlocks xs h h')).symm := rfl
  rw [hEq]
  refine List.ext_getElem (by simp) fun i _ hi ↦ ?_
  rw [List.getElem_map, List.getElem_finRange]
  exact List.blockNthD_blocks_self xs i hi _

/-! ### The list an enumeration was built from

An enumeration built by listing knows its elements twice over: once as the list, and once as the
`card α` separate lookups into it that `FinEnum.toList` performs.  The second reading is the one
every algorithm here gets, and it is not free — even blocked, a lookup is a walk of average
length `√(card α)`, so naming all of `α` costs `card α ^ 1.5` steps where the list itself costs
`card α`.  On the two hundred and ten unordered pairs a twenty-vertex line graph filters, that is
0.20 s of kernel time against 0.04.

`Elems` hands the list back.  It is not a stronger assumption than `FinEnum`: the default
instance is `toList` itself, so `Elems α` is always available and never changes *what* is
enumerated — `elems_eq` says so — only what reaching it costs. -/

/-- The elements of `α`, in the order `FinEnum.toList` puts them, but named directly rather than
looked up one index at a time. -/
class Elems (α : Type u) [FinEnum α] where
  /-- The elements of `α`. -/
  elems : List α
  /-- They are the enumeration. -/
  elems_eq : elems = toList α

/-- Every enumeration has its `toList`; an instance below only ever replaces this with a cheaper
spelling of the same list. -/
instance (priority := 100) instElemsToList [FinEnum α] : Elems α := ⟨toList α, rfl⟩

/-- The elements of `α`, naming the type: `Elems.elems` with `α` where a reader can see it. -/
abbrev elems (α : Type u) [FinEnum α] [Elems α] : List α := Elems.elems

theorem elems_eq (α : Type u) [FinEnum α] [Elems α] : elems α = toList α := Elems.elems_eq

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

instance (priority := 2000) instSubtype [FinEnum α] [Elems α] (p : α → Prop) [DecidablePred p] :
    FinEnum {x // p x} :=
  ofNodupBlocks ((elems α).filterMap fun x ↦ if h : p x then some ⟨x, h⟩ else none)
    (by rw [elems_eq]; rintro ⟨x, h⟩; simpa)
    (by rw [elems_eq]; exact nodup_subtypeList p)

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

/-- **Every `k`-element subset is laid out by a sublist.**  A `Finset` of size `k` is the elements
of one of the length-`k` sublists of `toList α`, namely the one that keeps its members in the order
the enumeration puts them in.  Together with the lemma above — which says there is only the one —
this is what makes `sublistsLen` an enumeration of the `k`-element subsets. -/
theorem exists_mem_sublistsLen (α : Type u) [FinEnum α] {k : ℕ} {s : Finset α} (hs : s.card = k) :
    ∃ l ∈ (toList α).sublistsLen k, l.toFinset = s := by
  have hsub : ((toList α).filter (fun a ↦ decide (a ∈ s))).Sublist (toList α) :=
    List.filter_sublist
  have hnd : ((toList α).filter (fun a ↦ decide (a ∈ s))).Nodup :=
    List.Nodup.sublist hsub nodup_toList
  have hfin : ((toList α).filter (fun a ↦ decide (a ∈ s))).toFinset = s := by
    ext a; simp [mem_toList]
  exact ⟨_, List.mem_sublistsLen.2 ⟨hsub, by rw [← List.toFinset_card_of_nodup hnd, hfin, hs]⟩,
    hfin⟩

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
  obtain ⟨l, hl, hlf⟩ := exists_mem_sublistsLen α hs
  rw [kSubsetList, List.mem_pmap]
  exact ⟨l, hl, Subtype.ext hlf⟩

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
    ofNodupBlocks l (mem_kSubsetList α) (nodup_kSubsetList α k)
  let table : Std.HashMap ℕ ℕ :=
    l.zipIdx.foldl (fun m p ↦ m.insert (subsetMask p.1.1) p.2)
      (Std.HashMap.emptyWithCapacity l.length)
  { base with
    equiv :=
      { toFun := fun s ↦ ⟨table.getD (subsetMask s.1) 0, lcProof⟩
        invFun := base.equiv.invFun
        left_inv := lcProof
        right_inv := lcProof } }

/-- The subsets of a fixed size, enumerated without going through the powerset. -/
@[implemented_by kSubsetEnumImpl]
def kSubsetEnum :
    FinEnum.{u + 1} {s : Finset α // s.card = k} :=
  ofNodupBlocks (kSubsetList α k) (mem_kSubsetList α) (nodup_kSubsetList α k)

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

/-! ## Unordered pairs

Without this instance a graph cannot name its own edges, which is what the line graph needs.
Listing all `card α ^ 2` ordered pairs and deduplicating them is the obvious way to build it and
the wrong one: `dedup` compares every surviving pair against every earlier one, and the elements
being compared are `Sym2`s, whose equality test is itself two comparisons in `α` — for the line
graph of the cube, whose vertices are functions `Fin 3 → Bool`, that is the dominant cost of the
whole enumeration.  Taking `y` only from `x` onwards produces each pair once, so the list is
duplicate-free by construction and half the length.

The block for `x` is written as a recursion and not as `l.map (fun y ↦ s(x, y)) ++ acc`, which is
what it computes.  A `Quot.mk` the kernel meets under a `List.map` costs it far more than one it
meets directly — on the twenty vertices of the dodecahedron, whose two hundred and ten pairs the
line graph's enumeration scans, 0.25 s against 0.04 — and `sym2Cons_eq` hands the proofs below the
spelling they want. -/

/-- `s(x, y)` for every `y` in the list, in front of `acc`. -/
def sym2Cons (x : α) : List α → List (Sym2 α) → List (Sym2 α)
  | [], acc => acc
  | y :: ys, acc => s(x, y) :: sym2Cons x ys acc

theorem sym2Cons_eq (x : α) (l : List α) (acc : List (Sym2 α)) :
    sym2Cons x l acc = (l.map fun y ↦ s(x, y)) ++ acc := by
  induction l with
  | nil => rfl
  | cons y ys ih => rw [sym2Cons, ih, List.map_cons, List.cons_append]

/-- The unordered pairs drawn from a list: `s(x, y)` for every `y` at or after `x`. -/
def sym2List : List α → List (Sym2 α)
  | [] => []
  | x :: xs => sym2Cons x (x :: xs) (sym2List xs)

theorem sym2List_cons (x : α) (xs : List α) :
    sym2List (x :: xs) = ((x :: xs).map fun y ↦ s(x, y)) ++ sym2List xs :=
  sym2Cons_eq ..

theorem mem_of_mem_sym2List {l : List α} {e : Sym2 α} (he : e ∈ sym2List l) {z : α} (hz : z ∈ e) :
    z ∈ l := by
  induction l with
  | nil => cases he
  | cons x xs ih =>
    rw [sym2List_cons, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact List.mem_cons_self ..
      · exact hy
    · exact List.mem_cons_of_mem _ (ih he)

theorem mem_sym2List {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) : s(a, b) ∈ sym2List l := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [sym2List_cons, List.mem_append]
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact Or.inl (List.mem_map.2 ⟨b, hb, rfl⟩)
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact Or.inl (List.mem_map.2 ⟨a, List.mem_cons_of_mem _ ha', Sym2.eq_swap⟩)
      · exact Or.inr (ih ha' hb')

/-- The point of `sym2List`: the pair `s(x, y)` is listed under the earlier of `x` and `y` and
nowhere else, so there is nothing to deduplicate. -/
theorem nodup_sym2List {l : List α} (h : l.Nodup) : (sym2List l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [sym2List_cons]
    refine List.Nodup.append (List.Nodup.map ?_ (List.nodup_cons.2 h)) (ih h.2) ?_
    · exact fun a b hab ↦ Sym2.congr_right.1 hab
    · intro e he he'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
      exact h.1 (mem_of_mem_sym2List he' (Sym2.mem_mk_left x y))

theorem length_sym2List (l : List α) : (sym2List l).length * 2 = l.length * (l.length + 1) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [sym2List_cons, List.length_append, List.length_map, List.length_cons, Nat.add_mul, ih]
    simp only [Nat.mul_succ, Nat.succ_mul]
    omega

instance instSym2 [FinEnum α] : FinEnum (Sym2 α) :=
  ofNodupBlocks (sym2List (toList α))
    (Sym2.ind fun x y ↦ mem_sym2List (mem_toList x) (mem_toList y))
    (nodup_sym2List nodup_toList)

/-- The pairs are already in a list; `toList` would fetch each of them out of it by index.  This
is what makes the vertices of a line graph cheap to enumerate — the subtype instance filters
`elems`, not `toList`. -/
instance instElemsSym2 [FinEnum α] : Elems (Sym2 α) where
  elems := sym2List (toList α)
  elems_eq := (toList_ofNodupBlocks _ _ _).symm

/-- The triangular number, stated without division. -/
@[simp] theorem card_sym2 [FinEnum α] : card (Sym2 α) * 2 = card α * (card α + 1) := by
  have h : (toList α).length = card α := by simp [toList]
  show (sym2List (toList α)).length * 2 = _
  rw [length_sym2List, h]

/-! ## Cardinalities

`card_eq_fintypeCard` turns any of Mathlib's `Fintype.card` computations into one about `card`;
these are the ones this development uses often enough to want by name. -/

theorem card_sigma {ι : Type u} [FinEnum ι] (F : ι → Type v) [∀ i, FinEnum (F i)] :
    card (Σ i, F i) = ∑ i, card (F i) := by
  rw [card_eq_fintypeCard, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun i _ ↦ (card_eq_fintypeCard (α := F i)).symm

theorem card_subtype' [FinEnum α] [Elems α] (p : α → Prop) [DecidablePred p] :
    card {x // p x} = ((toList α).filterMap fun x ↦
      if h : p x then some (⟨x, h⟩ : {x // p x}) else none).length := by
  show ((elems α).filterMap _).length = _
  rw [elems_eq]

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
