import IsoGraph.Containment.Minors
import IsoGraph.Containment.Algorithms.Backtrack

/-!
# Searching for a minor

`CGraph.findMinor H G rH rG` looks for `H` as a minor of `G`: a family of disjoint connected
*branch sets* in `G`, one for each vertex of `H`, with an edge of `G` between two of them whenever
there is an edge of `H`.  Like the induced subgraph search it does not return a `Bool`: when it
succeeds it returns the witness itself, an `H.MinorOf G`, and when it fails,
`isEmpty_minorOf_of_findMinor_eq_none` says there was nothing to find.  `rH` and `rG` are
`Backtrack.Roster`s; for a graph on `Fin n`, `Backtrack.Roster.fin n` is the one to use.

## What is searched over

A minor is a partial map `G.V → Option H.V` with connected fibres, so the naive search would be
over `(card H.V + 1) ^ card G.V` maps, with connectivity only testable at the very end.  Instead
the search builds the branch sets *one vertex at a time, in chain order*: `CGraph.ChainConn` says
that every vertex of a list is adjacent to one occurring later in it, which by
`CGraph.connectedOn_of_chainConn` makes the list connected, and by `CGraph.exists_pickChain` every
connected set can be listed that way.  Connectivity therefore holds by construction, and the
search never visits a partial assignment that is not extendable to connected sets.

The state (`MinorSearch.State`) is: the vertices of `H` still to be given a set, the set currently
being built, the sets already finished, and the vertices of `G` still unused.  There are two moves
(`MinorSearch.step`):

* `pick v` — add an unused `v` to the current set, which must be adjacent to something already in
  it and must come in the canonical order described below, or start the next set with `v`;
* `stop` — declare the current set finished.

`stop` is where the pruning lives, because a finished set is the last chance to reject it:

* every finished set that `H` requires to be adjacent to this one must actually have an edge to
  it — the sets are complete, so this test is final;
* if the vertex just finished still has `H`-neighbours waiting for sets, the set must have an edge
  to *some* still-unused vertex, since that is where those sets have to come from;
* there must be at least as many unused vertices left as there are vertices of `H` left, since the
  branch sets are disjoint and nonempty.

Two counting tests, `card H.V ≤ card G.V` and `H.E ≤ G.E`, reject hopeless pairs before the search
starts.

The whole thing runs on `Backtrack.dfs` with `α = Unit` and the state itself for the value, over a
`todo` of fixed length `card G.V + card H.V` — the largest number of moves a successful run can
take, padded out with `stop`s once everything is placed.  A leaf of the search is therefore always
a complete model, so `goal` — which re-checks the chain of states and then everything a minor
needs, from scratch — is evaluated rarely and can afford to be expensive.  That is what makes the
correctness proof cheap: soundness (`MinorSearch.ofFinal`) reads only the final state, and the
pruning is discharged by `Backtrack.dfs_eq_none`'s single obligation, which here is the
observation that a state in a chain is by definition a candidate of its predecessor.

## One order per set

A set of size `k` has `k!` orders, so enumerating orders rather than sets would cost a factor of
`k!` per branch set.  `CGraph.PickChain` cuts that down to one order per set, using the position
`rank v` of a vertex in the roster as a tie-break: a vertex may be added to `u :: T` only when

* it is adjacent to something already there — the connectivity requirement;
* it does not come before the vertex `T.getLastD u` the set was seeded at, which forces the seed
  to be the least vertex of the finished set;
* it does not come before the previous pick `u`, unless `u` is the only reason it is adjacent to
  the set at all — the exception is what lets the order follow a growing frontier.

`CGraph.exists_pickChain` proves nothing is lost: greedily taking the least vertex on the frontier,
starting from the least vertex of the set, always produces a legal order.  This needs no
assumption on `rank` whatsoever, so the search is free to choose it; it uses the roster order.

## What it costs

The search is still exponential — the problem is NP-hard — but the two cases it is meant for stay
cheap.  Both `K5` and `K3,3` in a graph of a dozen-odd vertices, and a `C3` in a tree, are found or
ruled out at once.  What can be slow is a *negative* answer on a dense host, where every family of
disjoint connected sets has to be looked at.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable {G : CGraph}

/-- A list is chain-connected when every vertex after the first is adjacent to one of the later
ones — that is, when reading it from the right builds a connected set one vertex at a time. -/
def ChainConn (G : CGraph) : List G.V → Bool
  | [] => false
  | v :: rest => rest.isEmpty || (rest.any (G.Adj v) && ChainConn G rest)

theorem chainConn_ne_nil {l : List G.V} (h : ChainConn G l = true) : l ≠ [] := by
  rintro rfl; simp [ChainConn] at h

theorem connectedOn_of_chainConn : ∀ {l : List G.V}, ChainConn G l = true →
    G.ConnectedOn {v | v ∈ l}
  | [], h => by simp [ChainConn] at h
  | v :: rest, h => by
    rw [ChainConn, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain rfl : rest = [] := List.isEmpty_iff.mp h
      have : {u : G.V | u ∈ [v]} = {v} := by ext u; simp
      rw [this]
      exact connectedOn_singleton G v
    · rw [Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨⟨u, hu, hvu⟩, hrest⟩ := h
      have hset : {u : G.V | u ∈ v :: rest} = insert v {u : G.V | u ∈ rest} := by
        ext u; simp [List.mem_cons, Set.mem_insert_iff]
      rw [hset]
      exact (connectedOn_of_chainConn hrest).insert hu hvu

/-- A list is a *legal* pick order for the search when it is a record of building the set one
vertex at a time: each vertex is adjacent to the ones after it, and — this is the part that keeps
the same set from being built in all `k!` of its orders — it comes no earlier in the search order
`rank` than the vertex added just before it, unless that vertex is what made it adjacent to the
set at all. -/
def PickChain (G : CGraph) (rank : G.V → ℕ) : List G.V → Bool
  | [] => false
  | [_] => true
  | v :: u :: T =>
    (u :: T).any (G.Adj v) && decide (rank (T.getLastD u) ≤ rank v) &&
      (decide (rank u ≤ rank v) || !T.any (G.Adj v)) && PickChain G rank (u :: T)

theorem pickChain_ne_nil {rank : G.V → ℕ} {l : List G.V} (h : PickChain G rank l = true) :
    l ≠ [] := by
  rintro rfl; simp [PickChain] at h

theorem chainConn_of_pickChain {rank : G.V → ℕ} :
    ∀ {l : List G.V}, PickChain G rank l = true → ChainConn G l = true
  | [], h => by simp [PickChain] at h
  | [_], _ => by simp [ChainConn]
  | _ :: u :: T, h => by
    rw [PickChain, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    rw [ChainConn]
    simp only [List.isEmpty_cons, Bool.false_or, Bool.and_eq_true]
    exact ⟨h.1.1.1, chainConn_of_pickChain h.2⟩

/-- The greedy step: taking always the frontier vertex of least `rank` keeps the order legal.
`u :: T` is what has been picked so far, `R` what is left of the graph. -/
theorem exists_pickChain_aux {s : Set G.V} (hs : G.ConnectedOn s) [DecidablePred (· ∈ s)]
    (rank : G.V → ℕ) :
    ∀ (n : ℕ) (u : G.V) (T R : List G.V), (u :: T).Nodup → (∀ v ∈ u :: T, v ∈ s) →
      PickChain G rank (u :: T) = true → (∀ v ∈ s, v ∈ u :: T ∨ v ∈ R) →
      (∀ v ∈ R, v ∉ u :: T) → R.length ≤ n → (∀ w ∈ s, rank (T.getLastD u) ≤ rank w) →
      (∀ w ∈ s, w ∉ u :: T → T.any (G.Adj w) = true → rank u ≤ rank w) →
      ∃ l : List G.V, l.Nodup ∧ (∀ v, v ∈ l ↔ v ∈ s) ∧ PickChain G rank l = true := by
  intro n
  induction n with
  | zero =>
    intro u T R hnd hsub hpc hcov _ hlen _ _
    obtain rfl : R = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    exact ⟨u :: T, hnd, fun v ↦ ⟨hsub v, fun hv ↦ (hcov v hv).resolve_right (by simp)⟩, hpc⟩
  | succ n ih =>
    intro u T R hnd hsub hpc hcov hdisj hlen hseed hmin
    by_cases hdone : ∀ v ∈ s, v ∈ u :: T
    · exact ⟨u :: T, hnd, fun v ↦ ⟨hsub v, fun hv ↦ hdone v hv⟩, hpc⟩
    push_neg at hdone
    obtain ⟨w, hws, hwl⟩ := hdone
    have hmemF : ∀ v, v ∈ R.filter (fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)) ↔
        (v ∈ R ∧ v ∈ s ∧ (u :: T).any (G.Adj v) = true) := by
      intro v; rw [List.mem_filter]; simp
    have hFne : R.filter (fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)) ≠ [] := by
      obtain ⟨a, ha, b, hbs, hbl, hab⟩ :=
        hs.exists_adj_of_ssubset (t := {v | v ∈ u :: T}) hsub (List.mem_cons_self ..) hws hwl
      intro hnil
      have hb := (hmemF b).mpr ⟨(hcov b hbs).resolve_left hbl, hbs,
        List.any_eq_true.mpr ⟨a, ha, by rw [G.symm b a]; exact hab⟩⟩
      rw [hnil] at hb
      simp at hb
    obtain ⟨b, hb⟩ : ∃ b, (R.filter fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)).argmin
        rank = some b := by
      cases hA : (R.filter fun z ↦ decide (z ∈ s) && (u :: T).any (G.Adj z)).argmin rank with
      | none => exact absurd (List.argmin_eq_none.mp hA) hFne
      | some b => exact ⟨b, rfl⟩
    obtain ⟨hbR, hbs, hbadj⟩ := (hmemF b).mp (List.argmin_mem hb)
    have hbl : b ∉ u :: T := hdisj b hbR
    refine ih b (u :: T) (R.filter fun v ↦ decide (v ≠ b))
      (List.nodup_cons.mpr ⟨hbl, hnd⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hbs
      · exact hsub v hv
    · rw [PickChain, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨⟨hbadj, by simpa using hseed b hbs⟩, ?_⟩, hpc⟩
      cases hT : T.any (G.Adj b)
      · simp
      · simp [hmin b hbs hbl hT]
    · intro v hv
      rcases hcov v hv with hvl | hvR
      · exact Or.inl (List.mem_cons_of_mem _ hvl)
      · by_cases hvb : v = b
        · exact Or.inl (hvb ▸ List.mem_cons_self ..)
        · exact Or.inr (List.mem_filter.mpr ⟨hvR, by simpa using hvb⟩)
    · intro v hv
      obtain ⟨hvR, hvb⟩ := List.mem_filter.mp hv
      simp only [decide_eq_true_eq] at hvb
      rw [List.mem_cons, not_or]
      exact ⟨hvb, hdisj v hvR⟩
    · have : (R.filter fun v ↦ decide (v ≠ b)).length < R.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨b, hbR, by simp⟩
      omega
    · rw [List.getLastD_cons]; exact hseed
    · intro z hzs hzl hzadj
      simp only [List.mem_cons, not_or] at hzl
      exact List.le_of_mem_argmin
        ((hmemF z).mpr ⟨(hcov z hzs).resolve_left (by simp [hzl.2.1, hzl.2.2]), hzs, hzadj⟩) hb

/-- **A connected set can be enumerated in a legal pick order.**  This is what makes the search's
canonicalisation of the order lose nothing: whatever the branch sets of a minor are, there is a
run of the search that builds them. -/
theorem exists_pickChain {s : Set G.V} [DecidablePred (· ∈ s)] (hs : G.ConnectedOn s)
    (rank : G.V → ℕ) (gs : List G.V) (hgs : ∀ v, v ∈ gs) :
    ∃ l : List G.V, l.Nodup ∧ (∀ v, v ∈ l ↔ v ∈ s) ∧ PickChain G rank l = true := by
  obtain ⟨u₀, hu₀⟩ := hs.nonempty
  have hne : gs.filter (fun z ↦ decide (z ∈ s)) ≠ [] := by
    intro hnil
    have : u₀ ∈ gs.filter fun z ↦ decide (z ∈ s) :=
      List.mem_filter.mpr ⟨hgs u₀, by simpa using hu₀⟩
    rw [hnil] at this
    simp at this
  obtain ⟨u, hu⟩ : ∃ u, (gs.filter fun z ↦ decide (z ∈ s)).argmin rank = some u := by
    cases hA : (gs.filter fun z ↦ decide (z ∈ s)).argmin rank with
    | none => exact absurd (List.argmin_eq_none.mp hA) hne
    | some u => exact ⟨u, rfl⟩
  have hus : u ∈ s := by simpa using (List.mem_filter.mp (List.argmin_mem hu)).2
  have hmin : ∀ w ∈ s, rank u ≤ rank w := fun w hw ↦
    List.le_of_mem_argmin (List.mem_filter.mpr ⟨hgs w, by simpa using hw⟩) hu
  refine exists_pickChain_aux hs rank (gs.filter fun v ↦ decide (v ≠ u)).length u []
    (gs.filter fun v ↦ decide (v ≠ u)) (by simp) ?_ rfl ?_ ?_ le_rfl hmin (by simp)
  · intro v hv; rw [List.mem_singleton] at hv; exact hv ▸ hus
  · intro v _
    by_cases hvu : v = u
    · exact Or.inl (by simp [hvu])
    · exact Or.inr (List.mem_filter.mpr ⟨hgs v, by simpa using hvu⟩)
  · intro v hv
    have := (List.mem_filter.mp hv).2
    simp only [decide_eq_true_eq] at this
    simpa using this

namespace MinorSearch

variable (H G : CGraph) (rank : G.V → ℕ)

/-- A step of the search. -/
inductive Move (G : CGraph) where
  /-- Add a vertex to the branch set under construction, starting one if there is none. -/
  | pick (v : G.V)
  /-- Finish the branch set under construction; when there is none and every vertex of `H` has
  one, do nothing. -/
  | stop

/-- The state of the search. -/
structure State (H G : CGraph) where
  /-- The vertices of `H` that have no branch set yet, in the order they will get one. -/
  todo : List H.V
  /-- The branch set under construction, newest vertex first. -/
  cur : Option (H.V × List G.V)
  /-- The finished branch sets, most recent first. -/
  done : List (H.V × List G.V)
  /-- The vertices of `G` that no branch set uses. -/
  avail : List G.V
  deriving DecidableEq

/-- Is there an edge of `G` between these two sets of vertices? -/
def linked (S T : List G.V) : Bool := S.any fun u ↦ T.any fun w ↦ G.Adj u w

theorem linked_iff {S T : List G.V} : linked G S T = true ↔ ∃ u ∈ S, ∃ w ∈ T, G.Adj u w := by
  simp [linked]

/-- Make a move, or report that it is illegal. -/
def step (m : Move G) (st : State H G) : Option (State H G) :=
  match m with
  | .pick v =>
    if st.avail.contains v then
      match st.cur with
      | some (_, []) => none
      | some (x, u :: T) =>
        if (u :: T).any (G.Adj v) && decide (rank (T.getLastD u) ≤ rank v) &&
            (decide (rank u ≤ rank v) || !T.any (G.Adj v)) then
          some ⟨st.todo, some (x, v :: u :: T), st.done, st.avail.erase v⟩
        else none
      | none =>
        match st.todo with
        | [] => none
        | x :: rest => some ⟨rest, some (x, [v]), st.done, st.avail.erase v⟩
    else none
  | .stop =>
    match st.cur with
    | some (x, S) =>
      if st.done.all (fun p ↦ !H.Adj x p.1 || linked G S p.2) &&
          (!st.todo.any (H.Adj x) || linked G S st.avail) &&
          decide (st.todo.length ≤ st.avail.length) then
        some ⟨st.todo, none, (x, S) :: st.done, st.avail⟩
      else none
    | none => if st.todo.isEmpty then some st else none

/-- The states one legal move away. -/
def candList (st : State H G) : List (State H G) :=
  (step H G rank .stop st).toList ++ st.avail.filterMap fun v ↦ step H G rank (.pick v) st

theorem mem_candList {m : Move G} {st st' : State H G} (h : step H G rank m st = some st') :
    st' ∈ candList H G rank st := by
  cases m with
  | stop => exact List.mem_append_left _ (by rw [h]; exact List.mem_singleton_self _)
  | pick v =>
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨v, ?_, h⟩)
    rw [step] at h
    split at h
    · rename_i hv; exact List.contains_iff_mem.mp hv
    · exact absurd h (by simp)

/-- The state a search has reached: the most recent one, or the initial one. -/
def headSt (init : State H G) : List (Unit × State H G) → State H G
  | [] => init
  | (_, st) :: _ => st

/-- Every state in the list follows from the one before by a legal move. -/
def chainOk (init : State H G) : List (Unit × State H G) → Bool
  | [] => true
  | (_, st) :: rest => (candList H G rank (headSt H G init rest)).contains st && chainOk init rest

theorem chainOk_of_append {init : State H G} {l r : List (Unit × State H G)}
    (h : chainOk H G rank init (l ++ r) = true) : chainOk H G rank init r = true := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    obtain ⟨_, st⟩ := p
    rw [List.cons_append, chainOk, Bool.and_eq_true] at h
    exact ih h.2

/-- The branch set of `x`. -/
def getSet : List (H.V × List G.V) → H.V → List G.V
  | [], _ => []
  | (y, S) :: rest, x => if y = x then S else getSet rest x

/-- The vertex of `H` whose branch set contains `v`, if any. -/
def branchOf : List (H.V × List G.V) → G.V → Option H.V
  | [], _ => none
  | (y, S) :: rest, v => if S.contains v then some y else branchOf rest v

/-- Does the state describe a minor?  Everything the answer needs is checked here, so the search
itself is free to prune as it likes. -/
def finalOk (hs : List H.V) (st : State H G) : Bool :=
  st.cur.isNone && st.todo.isEmpty &&
    decide (st.done.map Prod.fst).Nodup && decide (st.done.flatMap Prod.snd).Nodup &&
    hs.all (fun x ↦ (st.done.map Prod.fst).contains x) &&
    st.done.all (fun p ↦ ChainConn G p.2) &&
    hs.all fun x ↦ hs.all fun y ↦
      !H.Adj x y || linked G (getSet H G st.done x) (getSet H G st.done y)

/-- A complete run of the search is a solution when every move was legal and the state it ends in
describes a minor. -/
def goal (hs : List H.V) (init : State H G) (r : List (Unit × State H G)) : Bool :=
  chainOk H G rank init r && finalOk H G hs (headSt H G init r)

/-! ## Soundness -/

theorem getSet_eq_nil {bs : List (H.V × List G.V)} {x : H.V} (h : x ∉ bs.map Prod.fst) :
    getSet H G bs x = [] := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [getSet, if_neg fun hy ↦ h.1 hy.symm]
    exact ih h.2

theorem mem_flatMap_of_mem_getSet {bs : List (H.V × List G.V)} {x : H.V} {v : G.V}
    (h : v ∈ getSet H G bs x) : v ∈ bs.flatMap Prod.snd := by
  induction bs with
  | nil => exact absurd h (by simp [getSet])
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [List.flatMap_cons, List.mem_append]
    rw [getSet] at h
    split at h
    · exact Or.inl h
    · exact Or.inr (ih h)

theorem mem_getSet {bs : List (H.V × List G.V)} {x : H.V} (h : x ∈ bs.map Prod.fst) :
    (x, getSet H G bs x) ∈ bs := by
  induction bs with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [getSet]
    split
    · rename_i hy; subst hy; exact List.mem_cons_self ..
    · rename_i hy
      simp only [List.map_cons, List.mem_cons] at h
      exact List.mem_cons_of_mem _ (ih (h.resolve_left (Ne.symm hy)))

/-- With distinct keys and disjoint branch sets, the two ways of reading the table agree. -/
theorem branchOf_eq_some_iff {bs : List (H.V × List G.V)} (hk : (bs.map Prod.fst).Nodup)
    (hf : (bs.flatMap Prod.snd).Nodup) {v : G.V} {x : H.V} :
    branchOf H G bs v = some x ↔ v ∈ getSet H G bs x := by
  induction bs with
  | nil => simp [branchOf, getSet]
  | cons p rest ih =>
    obtain ⟨y, S⟩ := p
    rw [List.map_cons, List.nodup_cons] at hk
    rw [List.flatMap_cons, List.nodup_append] at hf
    rw [branchOf, getSet]
    by_cases hyx : y = x
    · subst hyx
      rw [if_pos rfl]
      by_cases hvS : S.contains v
      · rw [if_pos hvS]
        exact ⟨fun _ ↦ List.contains_iff_mem.mp hvS, fun _ ↦ rfl⟩
      · rw [if_neg hvS, ih hk.2 hf.2.1, getSet_eq_nil H G hk.1]
        simp only [List.not_mem_nil, false_iff]
        exact fun hv ↦ hvS (List.contains_iff_mem.mpr hv)
    · rw [if_neg hyx]
      by_cases hvS : S.contains v
      · rw [if_pos hvS]
        simp only [Option.some_inj]
        refine ⟨fun hxy ↦ absurd hxy hyx, fun hv ↦ ?_⟩
        exact absurd rfl (hf.2.2 v (List.contains_iff_mem.mp hvS) v
          (mem_flatMap_of_mem_getSet H G hv))
      · rw [if_neg hvS]
        exact ih hk.2 hf.2.1

/-- The minor that a successful search describes. -/
def ofFinal (hs : List H.V) (st : State H G) (hcov : ∀ x : H.V, x ∈ hs)
    (h : finalOk H G hs st = true) : H.MinorOf G := by
  rw [finalOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hkey⟩, hflat⟩, hmem⟩, hconn⟩, hedge⟩ := h
  have hiff : ∀ (v : G.V) (x : H.V), branchOf H G st.done v = some x ↔ v ∈ getSet H G st.done x :=
    fun _ _ ↦ branchOf_eq_some_iff H G hkey hflat
  refine ⟨branchOf H G st.done, fun x ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [show {v : G.V | branchOf H G st.done v = some x} = {v | v ∈ getSet H G st.done x} from
      Set.ext fun v ↦ hiff v x]
    exact connectedOn_of_chainConn
      (hconn _ (mem_getSet H G (List.contains_iff_mem.mp (hmem x (hcov x)))))
  · have := (hedge x (hcov x) y (hcov y)).resolve_left (by simp [hxy])
    rw [linked, List.any_eq_true] at this
    obtain ⟨u, hu, hw⟩ := this
    rw [List.any_eq_true] at hw
    obtain ⟨w, hw, huw⟩ := hw
    exact ⟨u, w, (hiff u x).mpr hu, (hiff w y).mpr hw, huw⟩

/-! ## The search -/

/-- The state a search starts from. -/
def initState (hs : List H.V) (gs : List G.V) : State H G := ⟨hs, none, [], gs⟩

/-- Search for a model of `H` in `G`, given the vertices of each.  A run is `gs.length +
hs.length` moves long: at most one `pick` per vertex of `G` and one `stop` per vertex of `H`,
padded out with idle moves once everything is placed. -/
def searchFrom (hs : List H.V) (gs : List G.V) : Option (State H G) :=
  let init := initState H G hs gs
  (Backtrack.dfs (fun _ pre ↦ candList H G rank (headSt H G init pre)) (goal H G rank hs init)
    (List.replicate (gs.length + hs.length) ()) []).map (headSt H G init)

theorem finalOk_of_searchFrom {hs : List H.V} {gs : List G.V} {st : State H G}
    (h : searchFrom H G rank hs gs = some st) : finalOk H G hs st = true := by
  simp only [searchFrom, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact (Bool.and_eq_true .. |>.mp (Backtrack.goal_of_dfs_eq_some hr)).2

/-! ## Completeness -/

/-- Erase each of `L` from `avail`. -/
def eraseAll (avail : List G.V) : List G.V → List G.V
  | [] => avail
  | v :: L => (eraseAll avail L).erase v

theorem nodup_eraseAll {avail : List G.V} (h : avail.Nodup) : ∀ L, (eraseAll G avail L).Nodup
  | [] => h
  | _ :: L => (nodup_eraseAll h L).erase _

theorem mem_eraseAll {avail : List G.V} (h : avail.Nodup) : ∀ (L : List G.V) (v : G.V),
    v ∈ eraseAll G avail L ↔ v ∈ avail ∧ v ∉ L
  | [], v => by simp [eraseAll]
  | w :: L, v => by
    rw [eraseAll, (nodup_eraseAll G h L).mem_erase_iff, mem_eraseAll h L]
    simp only [List.mem_cons, not_or]
    tauto

/-- Run a list of moves, most recent first, recording the state after each. -/
def trace (init : State H G) : List (Move G) → Option (List (Unit × State H G))
  | [] => some []
  | m :: ms => (trace init ms).bind fun r ↦
      (step H G rank m (headSt H G init r)).map fun st ↦ ((), st) :: r

theorem headSt_append (init : State H G) (r₁ r₂ : List (Unit × State H G)) :
    headSt H G init (r₁ ++ r₂) = headSt H G (headSt H G init r₂) r₁ := by
  cases r₁ with
  | nil => rfl
  | cons p r₁ => obtain ⟨_, st⟩ := p; rfl

theorem trace_append {init : State H G} {ms₁ ms₂ : List (Move G)} {r₂ : List (Unit × State H G)}
    (h₂ : trace H G rank init ms₂ = some r₂) :
    trace H G rank init (ms₁ ++ ms₂) = (trace H G rank (headSt H G init r₂) ms₁).map (· ++ r₂) := by
  induction ms₁ with
  | nil => simp [trace, h₂]
  | cons m ms ih =>
    rw [List.cons_append, trace, ih, trace]
    cases htr : trace H G rank (headSt H G init r₂) ms with
    | none => simp
    | some r₁ =>
      simp only [Option.map_some, Option.bind_some, headSt_append]
      cases step H G rank m (headSt H G (headSt H G init r₂) r₁) <;> simp

/-- A traced run is a legal one. -/
theorem trace_chainOk {init : State H G} {ms : List (Move G)} {r : List (Unit × State H G)}
    (h : trace H G rank init ms = some r) :
    chainOk H G rank init r = true ∧ r.length = ms.length := by
  induction ms generalizing r with
  | nil => rw [trace, Option.some_inj] at h; subst h; exact ⟨rfl, rfl⟩
  | cons m ms ih =>
    rw [trace, Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨st, hst, rfl⟩ := h
    obtain ⟨hchain, hlen⟩ := ih hr'
    refine ⟨?_, by simp [hlen]⟩
    rw [chainOk, Bool.and_eq_true]
    exact ⟨List.contains_iff_mem.mpr (mem_candList H G rank hst), hchain⟩

/-- Idling once everything is placed changes nothing. -/
theorem trace_pad {st : State H G} (hcur : st.cur = none) (htodo : st.todo = []) :
    ∀ k, ∃ r, trace H G rank st (List.replicate k Move.stop) = some r ∧ r.length = k ∧
      headSt H G st r = st
  | 0 => ⟨[], rfl, rfl, rfl⟩
  | k + 1 => by
    obtain ⟨r, hr, hlen, hhead⟩ := trace_pad hcur htodo k
    refine ⟨((), st) :: r, ?_, by simp [hlen], rfl⟩
    rw [List.replicate_succ, trace, hr, Option.bind_some, hhead, step]
    simp [hcur, htodo]

section Complete

variable {H G} (l : H.V → List G.V)

/-- The moves that give `x` its branch set: pick its vertices, then close the set. -/
def blockOf (x : H.V) : List (Move G) := Move.stop :: (l x).map Move.pick

/-- The moves that give every vertex of `xs` a branch set, most recent first. -/
def blocks : List H.V → List (Move G)
  | [] => []
  | x :: xs => blocks xs ++ blockOf l x

/-- The search state records the branch sets of `p`, and has `xs` left to place. -/
structure Ok (st : State H G) (xs p : List H.V) : Prop where
  /-- Nothing is under construction. -/
  cur : st.cur = none
  /-- The vertices left to place. -/
  todo : st.todo = xs
  /-- The branch sets built so far are the intended ones. -/
  done : st.done = p.map fun y ↦ (y, l y)
  /-- The branch sets still to come are still available. -/
  sub : ∀ y ∈ xs, ∀ v ∈ l y, v ∈ st.avail
  /-- No vertex is available twice. -/
  nodup : st.avail.Nodup

/-- Picking the vertices of a chain-connected list, from the right, builds it as a branch set. -/
theorem trace_picks {x : H.V} {rest : List H.V} :
    ∀ (L : List G.V) (st : State H G), st.cur = none → st.todo = x :: rest →
      PickChain G rank L = true → L.Nodup → (∀ v ∈ L, v ∈ st.avail) → st.avail.Nodup →
      ∃ r, trace H G rank st (L.map Move.pick) = some r ∧ r.length = L.length ∧
        headSt H G st r = ⟨rest, some (x, L), st.done, eraseAll G st.avail L⟩ := by
  intro L
  induction L with
  | nil => intro st _ _ hL _ _ _; simp [PickChain] at hL
  | cons v L ih =>
    intro st hcur htodo hL hnd hsub hav
    have hvL : v ∉ L := (List.nodup_cons.mp hnd).1
    have hvav : v ∈ st.avail := hsub v (List.mem_cons_self ..)
    rcases L with _ | ⟨w, L⟩
    · refine ⟨[((), ⟨rest, some (x, [v]), st.done, st.avail.erase v⟩)], ?_, rfl, rfl⟩
      rw [List.map_cons, List.map_nil, trace, trace, Option.bind_some]
      simp only [headSt, step, List.contains_iff_mem, hvav, if_pos, hcur, htodo]
      rfl
    · rw [PickChain] at hL
      simp only [Bool.and_eq_true] at hL
      obtain ⟨⟨⟨hadj, hseed⟩, hrank⟩, hLc⟩ := hL
      obtain ⟨r, hr, hlen, hhead⟩ := ih st hcur htodo hLc (List.Nodup.of_cons hnd)
        (fun u hu ↦ hsub u (List.mem_cons_of_mem _ hu)) hav
      refine ⟨((), ⟨rest, some (x, v :: w :: L), st.done, eraseAll G st.avail (v :: w :: L)⟩) :: r,
        ?_, by simp [hlen], rfl⟩
      have hmem : v ∈ eraseAll G st.avail (w :: L) := (mem_eraseAll G hav _ v).mpr ⟨hvav, hvL⟩
      rw [List.map_cons, trace, hr, Option.bind_some, hhead, step]
      simp only [List.contains_iff_mem, hmem, if_pos, hadj, hseed, hrank, Bool.and_self]
      rfl

variable (f : H.MinorOf G) (hl : ∀ (x : H.V) (v : G.V), v ∈ l x ↔ f.branch v = some x)
  (hnd : ∀ x, (l x).Nodup) (hch : ∀ x, PickChain G rank (l x) = true)

include hl in
/-- Distinct vertices of `H` have disjoint branch sets. -/
theorem not_mem_l {x y : H.V} (hxy : x ≠ y) {v : G.V} (hv : v ∈ l x) : v ∉ l y := fun hw ↦
  hxy (Option.some_inj.mp (((hl x v).mp hv).symm.trans ((hl y v).mp hw)))

include f hl in
/-- Adjacent vertices of `H` have branch sets joined by an edge. -/
theorem linked_l {x y : H.V} (hxy : H.Adj x y = true) : linked G (l x) (l y) = true := by
  obtain ⟨u, w, hu, hw, huw⟩ := f.map_adj hxy
  exact (linked_iff G).mpr ⟨u, (hl x u).mpr hu, w, (hl y w).mpr hw, huw⟩

include hl hnd in
theorem nodup_flatMap : ∀ {xs : List H.V}, xs.Nodup → (xs.flatMap l).Nodup
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hnd x, nodup_flatMap h.2, fun a ha b hb hab ↦ ?_⟩
    obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
    exact not_mem_l l f hl (fun e ↦ h.1 (by rw [e]; exact hy)) ha (hab ▸ hb)

theorem length_flatMap_add (xs : List H.V) :
    (xs.map fun y ↦ (l y).length + 1).sum = (xs.flatMap l).length + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append,
      List.length_cons]; omega

include hch in
theorem length_le_flatMap : ∀ xs : List H.V, xs.length ≤ (xs.flatMap l).length
  | [] => le_rfl
  | x :: xs => by
    have h1 := length_le_flatMap xs
    have h2 : 0 < (l x).length := List.length_pos_of_ne_nil (pickChain_ne_nil (hch x))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    omega

include f hl hnd hch in
/-- One block of moves gives `x` its branch set. -/
theorem trace_block (x : H.V) (xs p : List H.V) (st : State H G) (hok : Ok l st (x :: xs) p)
    (hxs : (x :: xs).Nodup) :
    ∃ r, trace H G rank st (blockOf l x) = some r ∧ r.length = (l x).length + 1 ∧
      Ok l (headSt H G st r) xs (x :: p) := by
  obtain ⟨hcur, htodo, hdone, hsub, hav⟩ := hok
  obtain ⟨r, hr, hlen, hhead⟩ := trace_picks rank (l x) st hcur htodo (hch x) (hnd x)
    (hsub x (List.mem_cons_self ..)) hav
  have havail : ∀ y ∈ xs, ∀ v ∈ l y, v ∈ eraseAll G st.avail (l x) := by
    intro y hy v hv
    refine (mem_eraseAll G hav _ v).mpr ⟨hsub y (List.mem_cons_of_mem _ hy) v hv, ?_⟩
    exact not_mem_l l f hl (by rintro rfl; exact (List.nodup_cons.mp hxs).1 hy) hv
  have hc1 : st.done.all (fun q ↦ !H.Adj x q.1 || linked G (l x) q.2) = true := by
    rw [hdone, List.all_eq_true]
    intro q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
    cases hadj : H.Adj x y
    · simp
    · simp [linked_l l f hl hadj]
  have hc2 : (!xs.any (H.Adj x) || linked G (l x) (eraseAll G st.avail (l x))) = true := by
    cases hany : xs.any (H.Adj x)
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      obtain ⟨y, hy, hadj⟩ := List.any_eq_true.mp hany
      obtain ⟨u, hu, w, hw, huw⟩ := (linked_iff G).mp (linked_l l f hl hadj)
      exact (linked_iff G).mpr ⟨u, hu, w, havail y hy w hw, huw⟩
  have hc3 : xs.length ≤ (eraseAll G st.avail (l x)).length := by
    refine le_trans (length_le_flatMap rank l hch xs) ?_
    refine ((nodup_flatMap l f hl hnd (List.Nodup.of_cons hxs)).subperm ?_).length_le
    intro v hv
    obtain ⟨y, hy, hv⟩ := List.mem_flatMap.mp hv
    exact havail y hy v hv
  refine ⟨((), ⟨xs, none, (x, l x) :: st.done, eraseAll G st.avail (l x)⟩) :: r, ?_,
    by simp [hlen], ⟨rfl, rfl, by rw [hdone]; rfl, havail, nodup_eraseAll G hav _⟩⟩
  rw [blockOf, trace, hr, Option.bind_some, hhead, step]
  simp only [hc1, hc2, hc3, decide_true, Bool.and_true, if_pos]
  rfl

include f hl hnd hch in
/-- The whole run: every vertex of `xs` gets its branch set. -/
theorem trace_blocks : ∀ (xs p : List H.V) (st : State H G), Ok l st xs p → xs.Nodup →
    ∃ r, trace H G rank st (blocks l xs) = some r ∧
      r.length = (xs.map fun y ↦ (l y).length + 1).sum ∧
      Ok l (headSt H G st r) [] (xs.reverse ++ p)
  | [], p, st, hok, _ => ⟨[], rfl, rfl, by simpa using hok⟩
  | x :: xs, p, st, hok, hxs => by
    obtain ⟨r₁, hr₁, hlen₁, hok₁⟩ := trace_block rank l f hl hnd hch x xs p st hok hxs
    obtain ⟨r₂, hr₂, hlen₂, hok₂⟩ := trace_blocks xs (x :: p) _ hok₁ (List.Nodup.of_cons hxs)
    refine ⟨r₂ ++ r₁, ?_, ?_, ?_⟩
    · rw [blocks, trace_append H G rank hr₁, hr₂]; rfl
    · rw [List.length_append, hlen₁, hlen₂, List.map_cons, List.sum_cons]; omega
    · rw [headSt_append]; simpa using hok₂

theorem getSet_map {ys : List H.V} {x : H.V} (h : x ∈ ys) :
    getSet H G (ys.map fun y ↦ (y, l y)) x = l x := by
  induction ys with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.map_cons, getSet]
    split
    · rename_i hy; rw [hy]
    · rename_i hy; exact ih ((List.mem_cons.mp h).resolve_left fun e ↦ hy e.symm)

include f hl hnd hch in
/-- A finished run passes every test. -/
theorem finalOk_of_ok {st : State H G} {hs : List H.V} (hhsnd : hs.Nodup)
    (hok : Ok l st [] hs.reverse) : finalOk H G hs st = true := by
  obtain ⟨hcur, htodo, hdone, -, -⟩ := hok
  have e1 : ((hs.reverse.map fun y ↦ (y, l y)).map Prod.fst) = hs.reverse := by
    simp [Function.comp_def]
  have e2 : ((hs.reverse.map fun y ↦ (y, l y)).flatMap Prod.snd) = hs.reverse.flatMap l := by
    rw [List.flatMap_map]
  rw [finalOk, hcur, htodo, hdone, e1, e2]
  have h1 : hs.reverse.Nodup := List.nodup_reverse.mpr hhsnd
  have h2 : (hs.reverse.flatMap l).Nodup := nodup_flatMap l f hl hnd h1
  have h3 : ∀ x ∈ hs, hs.reverse.contains x :=
    fun x hx ↦ List.contains_iff_mem.mpr (List.mem_reverse.mpr hx)
  have h4 : ∀ q ∈ hs.reverse.map fun y ↦ (y, l y), ChainConn G q.2 = true := by
    intro q hq
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
    exact chainConn_of_pickChain (hch y)
  have h5 : ∀ x ∈ hs, ∀ y ∈ hs, (!H.Adj x y ||
      linked G (getSet H G (hs.reverse.map fun z ↦ (z, l z)) x)
        (getSet H G (hs.reverse.map fun z ↦ (z, l z)) y)) = true := by
    intro x hx y hy
    rw [getSet_map l (List.mem_reverse.mpr hx), getSet_map l (List.mem_reverse.mpr hy)]
    cases hadj : H.Adj x y
    · simp
    · simp [linked_l l f hl hadj]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

/-- **Every minor is described by a chain-ordered model**, which is what the search looks for. -/
theorem exists_chain_model (f : H.MinorOf G) (rank : G.V → ℕ) {gs : List G.V}
    (hgs : ∀ v, v ∈ gs) :
    ∃ L : H.V → List G.V, (∀ (x : H.V) (v : G.V), v ∈ L x ↔ f.branch v = some x) ∧
      (∀ x, (L x).Nodup) ∧ (∀ x, PickChain G rank (L x) = true) := by
  haveI : ∀ x : H.V, DecidablePred (· ∈ {v : G.V | f.branch v = some x}) :=
    fun x v ↦ inferInstanceAs (Decidable (f.branch v = some x))
  choose L h1 h2 h3 using fun x ↦ exists_pickChain (f.connectedOn x) rank gs hgs
  exact ⟨L, fun x v ↦ h2 x v, h1, h3⟩

end Complete

variable {H G}

/-- **Completeness**: a search that comes back empty has ruled out every minor. -/
theorem isEmpty_minorOf_of_searchFrom {hs : List H.V} {gs : List G.V} (hgs : ∀ v, v ∈ gs)
    (hhsnd : hs.Nodup) (hgsnd : gs.Nodup) (h : searchFrom H G rank hs gs = none) :
    IsEmpty (H.MinorOf G) := by
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨l, hl, hnd, hch⟩ := exists_chain_model f rank hgs
  have hok : Ok l (initState H G hs gs) hs [] := ⟨rfl, rfl, rfl, fun _ _ v _ ↦ hgs v, hgsnd⟩
  obtain ⟨r₁, hr₁, hlen₁, hok₁⟩ := trace_blocks rank l f hl hnd hch hs [] _ hok hhsnd
  have hbound : r₁.length ≤ gs.length + hs.length := by
    have : (hs.flatMap l).length ≤ gs.length :=
      ((nodup_flatMap l f hl hnd hhsnd).subperm fun v _ ↦ hgs v).length_le
    rw [hlen₁, length_flatMap_add l hs]
    omega
  obtain ⟨r₂, hr₂, hlen₂, hhead₂⟩ :=
    trace_pad H G rank hok₁.cur hok₁.todo (gs.length + hs.length - r₁.length)
  have htr : trace H G rank (initState H G hs gs)
      (List.replicate (gs.length + hs.length - r₁.length) Move.stop ++ blocks l hs)
      = some (r₂ ++ r₁) := by rw [trace_append H G rank hr₁, hr₂]; rfl
  obtain ⟨hchain, -⟩ := trace_chainOk H G rank htr
  have hgoal : goal H G rank hs (initState H G hs gs) (r₂ ++ r₁) = true := by
    rw [goal, Bool.and_eq_true, headSt_append, hhead₂]
    exact ⟨hchain, finalOk_of_ok rank l f hl hnd hch hhsnd (by simpa using hok₁)⟩
  have hcand : ∀ (a : Unit) (pre : List (Unit × State H G)) (b : State H G)
      (u : List (Unit × State H G)),
      goal H G rank hs (initState H G hs gs) (u ++ (a, b) :: pre) = true →
      b ∈ candList H G rank (headSt H G (initState H G hs gs) pre) := by
    intro _ pre b u hg
    rw [goal, Bool.and_eq_true] at hg
    have hc := chainOk_of_append H G rank hg.1
    rw [chainOk, Bool.and_eq_true] at hc
    exact List.contains_iff_mem.mp hc.1
  have hsol : ((r₂ ++ r₁).reverse).map Prod.fst = List.replicate (gs.length + hs.length) () := by
    rw [List.eq_replicate_iff]
    refine ⟨?_, fun b _ ↦ rfl⟩
    rw [List.length_map, List.length_reverse, List.length_append, hlen₂]
    omega
  rw [searchFrom, Option.map_eq_none_iff] at h
  have := Backtrack.dfs_eq_none hcand h hsol
  rw [List.reverse_reverse, List.append_nil, hgoal] at this
  exact absurd this (by simp)

end MinorSearch

/-! ## The search -/

section Search

open MinorSearch

variable (H G : CGraph)

/-- The finished state the search finds, before it is turned into a `MinorOf`.

The guard in front is the cheap necessary condition: a minor has no more vertices and no more
edges than its host, so a search that cannot possibly succeed is not started. -/
def searchMinor (rH : Roster H.V) (rG : Roster G.V) : Option (State H G) :=
  if Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E then
    searchFrom H G (fun v ↦ rG.toList.idxOf v) rH.toList.dedup rG.toList.dedup
  else none

theorem finalOk_of_searchMinor {rH : Roster H.V} {rG : Roster G.V} {st : State H G}
    (h : searchMinor H G rH rG = some st) : finalOk H G rH.toList.dedup st = true := by
  rw [searchMinor] at h
  split at h
  · exact finalOk_of_searchFrom H G _ h
  · exact absurd h (by simp)

/-- **Is `H` a minor of `G`?**  Returns a witness if so.  See
`isEmpty_minorOf_of_findMinor_eq_none` for the other half of the answer. -/
def findMinor (rH : Roster H.V) (rG : Roster G.V) : Option (H.MinorOf G) :=
  Option.pmap (p := fun st ↦ finalOk H G rH.toList.dedup st = true)
    (fun st hst ↦ ofFinal H G rH.toList.dedup st
      (fun x ↦ List.mem_dedup.mpr (rH.mem_toList x)) hst)
    (searchMinor H G rH rG) (fun _ hst ↦ finalOk_of_searchMinor H G hst)

theorem findMinor_eq_none_iff (rH : Roster H.V) (rG : Roster G.V) :
    findMinor H G rH rG = none ↔ searchMinor H G rH rG = none :=
  Option.pmap_eq_none_iff

variable {H G}

/-- **Completeness**: when the search comes back empty, `H` is not a minor of `G`. -/
theorem isEmpty_minorOf_of_findMinor_eq_none {rH : Roster H.V} {rG : Roster G.V}
    (h : findMinor H G rH rG = none) : IsEmpty (H.MinorOf G) := by
  rw [findMinor_eq_none_iff, searchMinor] at h
  split at h
  · exact isEmpty_minorOf_of_searchFrom _ (fun v ↦ List.mem_dedup.mpr (rG.mem_toList v))
      (List.nodup_dedup _) (List.nodup_dedup _) h
  · exact ⟨fun f ↦ absurd (show Fintype.card H.V ≤ Fintype.card G.V ∧ H.E ≤ G.E from
      ⟨f.card_le, f.E_le⟩) ‹_›⟩

/-- `H` is a minor of `G` exactly when the search finds one. -/
theorem isEmpty_minorOf_iff (rH : Roster H.V) (rG : Roster G.V) :
    IsEmpty (H.MinorOf G) ↔ findMinor H G rH rG = none := by
  refine ⟨fun h ↦ ?_, isEmpty_minorOf_of_findMinor_eq_none⟩
  rcases hm : findMinor H G rH rG with _ | f
  · rfl
  · exact (h.false f).elim

end Search

end CGraph
