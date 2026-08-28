import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Equiv.Fin.Basic
import IsoGraph.ForMathlib.FinEnum

/-!
# A verified backtracking search

Deciding whether one graph sits inside another is NP-hard, so any algorithm for it is a
backtracking search: extend a partial assignment one element at a time, and abandon a branch as
soon as it cannot be completed.  What makes such a search *fast* is the pruning, and what makes it
*correct* is that the pruning throws nothing away.  This file separates the two.

`Backtrack.dfs` assigns a value to each element of a list `todo` in turn, in the order given.  It
takes two callbacks:

* `goal` decides whether a *complete* assignment is a solution;
* `cand a pre` lists the values worth trying for `a`, given the assignments `pre` already made
  (most recent first).

`dfs` returns the first complete assignment `goal` accepts, and `dfs_eq_none` says that when it
returns `none` there is none to be found — under the single hypothesis that `cand` is *sound*:
whenever `l ++ (a, b) :: pre` is a solution, `b` is among the candidates `cand` offers for `a`
after `pre`.  Every pruning rule is therefore discharged by one implication, from a global
property of a solution to a locally computable test, and a caller is free to make `cand` as clever
as it likes: dropping a candidate is only ever a *speed* question, never a correctness one, as
long as that implication still goes through.

The idiom this suggests, and the one both callers use, is to put every necessary condition into
`goal` and then to have `cand` re-check the ones it can see, so that the soundness of the pruning
becomes a projection out of `goal`.  A condition that is a *consequence* of the others need not go
in: `dfs_eq_none_keys` hands the pruning the keys the solution assigns, which is enough to recover
a global fact like "no vertex of the pattern has more neighbours than its image" from the local
ones, and a test that would only ever have succeeded is one the leaf does not have to run.

`Backtrack.Roster` is here too: the list of candidates has to come from somewhere, and a `Fintype`
instance cannot computably produce one.
-/

set_option autoImplicit false

namespace Backtrack

universe u v

variable {α : Type u} {β : Type v}

/-- A computable list of all the elements of a type.

A `Fintype` instance is not enough for a search: it gives a `Finset`, whose underlying `Multiset`
is a quotient of lists by permutation, and there is no well-defined — hence no computable — way to
pick a list out of it again.  `Finset.toList` exists but is noncomputable.  A search has to try
the candidates in *some* order, so it has to be handed one. -/
structure Roster (α : Type u) where
  /-- The elements, in the order a search should try them. -/
  toList : List α
  /-- Every element occurs. -/
  mem_toList : ∀ a, a ∈ toList

/-- The roster of `Fin n`.  This covers essentially every graph in practice: a `CGraph` built by
one of the constructions has `Fin n`, or something equivalent to it, for its vertex type. -/
def Roster.fin (n : ℕ) : Roster (Fin n) := ⟨List.finRange n, by simp⟩

/-- The roster a `FinEnum` already carries.  Every `CGraph` bundles one, so no vertex type in this
development is without a roster; the hand-written combinators below survive because they can be
cheaper — `FinEnum.toList` runs every index through `equiv.symm`, which for a vertex type whose
enumeration is a list is a list index per element. -/
def Roster.enum (α : Type u) [FinEnum α] : Roster α := ⟨FinEnum.toList α, FinEnum.mem_toList⟩

/-- A roster transported along an equivalence. -/
def Roster.ofEquiv {α : Type u} {β : Type v} (r : Roster β) (e : α ≃ β) : Roster α :=
  ⟨r.toList.map e.symm, fun a ↦ List.mem_map.mpr ⟨e a, r.mem_toList (e a), e.symm_apply_apply a⟩⟩

/-- The roster of a product. -/
def Roster.prod (r : Roster α) (s : Roster β) : Roster (α × β) :=
  ⟨r.toList.flatMap fun a ↦ s.toList.map fun b ↦ (a, b), fun p ↦ by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨p.1, r.mem_toList p.1, p.2, s.mem_toList p.2, rfl⟩⟩

/-- The roster of a sum. -/
def Roster.sum (r : Roster α) (s : Roster β) : Roster (α ⊕ β) :=
  ⟨r.toList.map Sum.inl ++ s.toList.map Sum.inr, fun x ↦ by
    cases x <;> simp [r.mem_toList, s.mem_toList]⟩

/-- The roster of `Bool`. -/
def Roster.bool : Roster Bool := ⟨[false, true], by decide⟩

/-- The roster of the functions out of `Fin n`, in lexicographic order. -/
def Roster.finArrow : (n : ℕ) → Roster β → Roster (Fin n → β)
  | 0, _ => ⟨[Fin.elim0], fun _ ↦ List.mem_singleton.mpr (funext fun i ↦ i.elim0)⟩
  | n + 1, r => (r.prod (Roster.finArrow n r)).ofEquiv (Fin.consEquiv fun _ ↦ β).symm

/-- The roster of a subtype. -/
def Roster.subtype (r : Roster α) (p : α → Prop) [DecidablePred p] : Roster {x // p x} :=
  ⟨r.toList.filterMap fun a ↦ if h : p a then some ⟨a, h⟩ else none, fun x ↦
    List.mem_filterMap.mpr ⟨x.1, r.mem_toList x.1, by rw [dif_pos x.2]⟩⟩

/-- The roster of the finite subsets of a rostered type. -/
def Roster.finset [DecidableEq α] (r : Roster α) : Roster (Finset α) :=
  ⟨r.toList.sublists.map List.toFinset, fun s ↦
    List.mem_map.mpr ⟨r.toList.filter fun a ↦ decide (a ∈ s),
      List.mem_sublists.mpr (List.filter_sublist ..), by
        ext a; simp [r.mem_toList a]⟩⟩

/-! ### Tabulated functions

A search asks the same numeric question about the same element over and over: where the roster
lists a vertex, how many neighbours it has, how many of its class are still to come.  None of
those depends on the partial assignment, and all of them are a scan of something, so a search
computes each once per element before it starts and reads them back out of an array afterwards.

`tabulate` and `tabAt` are that array and that read, indexed by `FinEnum.equiv`.  Whether the
lookup is faster than the question is a matter for the type: for `Fin n`, and for the products and
sums the graph constructions build, `FinEnum.equiv` is arithmetic; for a vertex type whose
enumeration is a list it is another scan, and the table only pays from the second query onwards.
Neither is ever reasoned about — `tabAt_tabulate` puts the function back. -/

/-- A `ℕ`-valued function on a `FinEnum`, as a table indexed by `FinEnum.equiv`. -/
def tabulate {α : Type u} [FinEnum α] (f : α → ℕ) : Array ℕ :=
  ((List.finRange (FinEnum.card α)).map fun i ↦ f (FinEnum.equiv.symm i)).toArray

/-- Read a value out of a `Backtrack.tabulate` table.

Top-level, and applied to the table alone rather than defined as `fun f v ↦ ⋯`: the compiler
maximises the arity of a definition, so one that returns a function type takes the second argument
too and rebuilds the table on every lookup.  A caller shares the table by naming
`tabAt (tabulate f)` in a `let`. -/
def tabAt {α : Type u} [FinEnum α] (t : Array ℕ) (v : α) : ℕ := t[(FinEnum.equiv v).val]!

/-- **The table says what the function says.** -/
theorem tabAt_tabulate {α : Type u} [FinEnum α] (f : α → ℕ) : tabAt (tabulate f) = f := by
  funext v
  rw [tabAt, tabulate, getElem!_pos _ _ (by simp [(FinEnum.equiv v).isLt])]
  simp

/-- Where `l` lists each element, tabulated: the rank symmetry breaking orders images by. -/
def rankTable {α : Type u} [FinEnum α] (l : List α) : Array ℕ := tabulate fun v ↦ l.idxOf v

theorem tabAt_rankTable {α : Type u} [FinEnum α] (l : List α) :
    tabAt (rankTable l) = fun v ↦ l.idxOf v :=
  tabAt_tabulate _

/-- Depth-first search over assignments of values in `β` to the elements of `todo`, taken in
order.  `pre` is the assignment made so far, most recent first; `cand a pre` are the values to try
for `a`; `goal` decides a complete assignment. -/
def dfs (cand : α → List (α × β) → List β) (goal : List (α × β) → Bool) :
    List α → List (α × β) → Option (List (α × β))
  | [], pre => if goal pre then some pre else none
  | a :: todo, pre => (cand a pre).findSome? fun b ↦ dfs cand goal todo ((a, b) :: pre)

variable {cand : α → List (α × β) → List β} {goal : List (α × β) → Bool}

/-- **Soundness**: what the search returns satisfies `goal`. -/
theorem goal_of_dfs_eq_some {todo : List α} {pre r : List (α × β)}
    (h : dfs cand goal todo pre = some r) : goal r = true := by
  induction todo generalizing pre r with
  | nil =>
    rw [dfs] at h
    split at h
    · rename_i hg; rw [Option.some_inj] at h; exact h ▸ hg
    · exact absurd h (by simp)
  | cons a todo ih =>
    rw [dfs] at h
    obtain ⟨_, _, hb⟩ := List.exists_of_findSome?_eq_some h
    exact ih hb

/-- What the search returns assigns a value to every element of `todo`, and to nothing else. -/
theorem keys_of_dfs_eq_some {todo : List α} {pre r : List (α × β)}
    (h : dfs cand goal todo pre = some r) :
    r.map Prod.fst = todo.reverse ++ pre.map Prod.fst := by
  induction todo generalizing pre r with
  | nil =>
    rw [dfs] at h
    split at h
    · rw [Option.some_inj] at h; subst h; simp
    · exact absurd h (by simp)
  | cons a todo ih =>
    rw [dfs] at h
    obtain ⟨_, _, hb⟩ := List.exists_of_findSome?_eq_some h
    rw [ih hb]; simp

/-- **Completeness**, with the keys of the solution in hand: if the search comes back empty then
nothing satisfies `goal`.  The one thing asked of the pruning is `hcand`, and it may assume that
the solution it is shown assigns exactly `keys` — which is what lets a condition like "no vertex
of the pattern has more neighbours than its image" be available to the pruning without `goal`
having to test it.  What is left to do and what has been done together make up `keys` at every
step, and that is the invariant `hkeys` carries down the recursion. -/
theorem dfs_eq_none_keys {keys : List α}
    (hcand : ∀ (a : α) (pre : List (α × β)) (b : β) (l : List (α × β)),
      (l ++ (a, b) :: pre).map Prod.fst = keys →
        goal (l ++ (a, b) :: pre) = true → b ∈ cand a pre)
    {todo : List α} {pre sol : List (α × β)} (h : dfs cand goal todo pre = none)
    (hsol : sol.map Prod.fst = todo) (hkeys : todo.reverse ++ pre.map Prod.fst = keys) :
    goal (sol.reverse ++ pre) = false := by
  induction todo generalizing pre sol with
  | nil =>
    obtain rfl : sol = [] := List.map_eq_nil_iff.mp hsol
    rw [dfs] at h
    simp only [List.reverse_nil, List.nil_append]
    split at h
    · exact absurd h (by simp)
    · rename_i hg; simpa using hg
  | cons a todo ih =>
    rw [dfs] at h
    cases sol with
    | nil => simp at hsol
    | cons p sol =>
      obtain ⟨a', b⟩ := p
      simp only [List.map_cons, List.cons.injEq] at hsol
      obtain ⟨rfl, hsol⟩ := hsol
      have hrw : ((a', b) :: sol).reverse ++ pre = sol.reverse ++ (a', b) :: pre := by simp
      have hkeys' : todo.reverse ++ ((a', b) :: pre).map Prod.fst = keys := by
        rw [← hkeys]; simp
      have hk : (sol.reverse ++ (a', b) :: pre).map Prod.fst = keys := by
        rw [← hkeys', List.map_append, List.map_reverse, hsol]
      rw [hrw]
      by_contra hg
      rw [Bool.not_eq_false] at hg
      have hb : b ∈ cand a' pre := hcand a' pre b sol.reverse hk hg
      have hno := ih (List.findSome?_eq_none_iff.mp h b hb) hsol hkeys'
      rw [hg] at hno
      exact absurd hno (by simp)

/-- **Completeness** for a pruning rule that has no use for what the rest of the solution
assigns. -/
theorem dfs_eq_none
    (hcand : ∀ (a : α) (pre : List (α × β)) (b : β) (l : List (α × β)),
      goal (l ++ (a, b) :: pre) = true → b ∈ cand a pre)
    {todo : List α} {pre sol : List (α × β)} (h : dfs cand goal todo pre = none)
    (hsol : sol.map Prod.fst = todo) : goal (sol.reverse ++ pre) = false :=
  dfs_eq_none_keys (fun a pre b l _ hg ↦ hcand a pre b l hg) h hsol rfl

end Backtrack
