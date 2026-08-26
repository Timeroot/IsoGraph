import IsoGraph.Containment.Defs

/-!
# The plumbing a routing search runs on

The topological minor and immersion searches have the same shape — place the branch vertices of
`H` in `G`, then join each edge of `H` by a walk of `G` — and differ only in what a walk is
allowed to be and in what two walks may share.  Everything they have in common is here.

Two things, really.  A `SimpleGraph.Walk` is indexed by its own endpoints, which is not something
a search can build up one step at a time, so a walk under construction is a *list* of vertices:
`CGraph.isWalkList` says consecutive ones are adjacent, `CGraph.chainEnd` says where the list ends
up, and `CGraph.walkOfList` turns the list back into a `Walk` once it is finished.  And a step of
the search is a `CGraph.Task` — place a vertex, or route an edge whose two ends are already placed
— with `CGraph.tasks` interleaving them so that a run is chosen as soon as both of its ends are
known.  `CGraph.branches` and `CGraph.runs` read the two kinds of entry back off an assignment,
and `CGraph.findB`, `CGraph.findR` look one up.

Everything a search built on this checks is stated over the *entries* of an assignment rather than
over what a lookup finds in it, because the pruning obligation of `Algorithms/Backtrack.lean` is
quantified over every way of splitting the assignment in two, and a duplicated key would otherwise
let a test pass on one occurrence and fail on another.
-/

set_option autoImplicit false

namespace CGraph

variable {G H : CGraph}

/-! ## Walks as lists -/

/-- Where the walk that starts at `u` and runs along `l` ends up. -/
def chainEnd : G.V → List G.V → G.V
  | u, [] => u
  | _, w :: l => chainEnd w l

/-- Is `u :: l` a walk of `G`? -/
def isWalkList (G : CGraph) : G.V → List G.V → Bool
  | _, [] => true
  | u, w :: l => G.Adj u w && isWalkList G w l

/-- The walk of `G` whose vertices are `u :: l`. -/
def walkOfList (G : CGraph) : (u : G.V) → (l : List G.V) → isWalkList G u l = true →
    G.toSimple.Walk u (chainEnd u l)
  | _, [], _ => .nil
  | u, w :: l, h =>
    .cons ((G.toSimple_adj u w).mpr (by rw [isWalkList, Bool.and_eq_true] at h; exact h.1))
      (walkOfList G w l (by rw [isWalkList, Bool.and_eq_true] at h; exact h.2))

@[simp] theorem support_walkOfList (u : G.V) (l : List G.V) (h : isWalkList G u l = true) :
    (walkOfList G u l h).support = u :: l := by
  induction l generalizing u with
  | nil => rfl
  | cons w l ih => rw [walkOfList, SimpleGraph.Walk.support_cons, ih]

theorem chainEnd_eq_getLast (u : G.V) (l : List G.V) :
    chainEnd u l = (u :: l).getLast (by simp) := by
  induction l generalizing u with
  | nil => rfl
  | cons w l ih => rw [chainEnd, ih, List.getLast_cons_cons]

/-- The vertices a walk runs through, after its first. -/
theorem isWalkList_support_tail {u v : G.V} (p : G.toSimple.Walk u v) :
    isWalkList G u p.support.tail = true := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, ← p.cons_tail_support, isWalkList]
    simpa using ⟨h, ih⟩

theorem chainEnd_support_tail {u v : G.V} (p : G.toSimple.Walk u v) :
    chainEnd u p.support.tail = v := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, ← p.cons_tail_support, chainEnd]
    exact ih

/-- The vertices a walk between distinct ends visits after its first, split at the last one. -/
theorem tail_support_eq {u v : G.V} (p : G.toSimple.Walk u v) (h : u ≠ v) :
    p.support.tail = p.support.tail.dropLast ++ [v] := by
  have hend := chainEnd_support_tail p
  have hne : p.support.tail ≠ [] := by
    intro he
    rw [he, chainEnd] at hend
    exact h hend
  have hl : p.support.tail.getLast hne = v := by
    rw [chainEnd_eq_getLast, List.getLast_cons hne] at hend
    exact hend
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]

/-! ## The search -/

/-- A step of the search. -/
inductive Task (H : CGraph) where
  /-- Choose the branch vertex of `x`. -/
  | place : H.V → Task H
  /-- Choose the run of the edge joining `x` to the earlier vertex `y`. -/
  | route : H.V → H.V → Task H

/-- What the search assigns: a list of vertices of `G` to each step — a one-element list for a
branch vertex, the run itself for an edge. -/
abbrev Asg (H G : CGraph) := List (Task H × List G.V)

/-- Is `x`–`y` an edge of `H` taken in the orientation the search routes it in, from the later of
its endpoints to the earlier?  Position is position in `hs`, the order the vertices are placed
in. -/
def oriented (H : CGraph) (hs : List H.V) (x y : H.V) : Bool :=
  H.Adj x y && decide (hs.idxOf y < hs.idxOf x)

theorem adj_of_oriented {hs : List H.V} {x y : H.V} (h : oriented H hs x y = true) :
    H.Adj x y = true := (Bool.and_eq_true .. ▸ h).1

theorem idxOf_lt_of_oriented {hs : List H.V} {x y : H.V} (h : oriented H hs x y = true) :
    hs.idxOf y < hs.idxOf x := of_decide_eq_true (Bool.and_eq_true .. ▸ h).2

theorem oriented_eq_true {hs : List H.V} {x y : H.V} (h : H.Adj x y = true)
    (hlt : hs.idxOf y < hs.idxOf x) : oriented H hs x y = true := by
  rw [oriented, Bool.and_eq_true]; exact ⟨h, by simpa using hlt⟩

theorem ne_of_oriented {hs : List H.V} {x y : H.V} (h : oriented H hs x y = true) : x ≠ y := by
  rintro rfl; exact absurd (idxOf_lt_of_oriented h) (by omega)

/-- The steps, in order: each vertex in turn, and after it the edges joining it to the vertices
already placed.  A run is therefore chosen as soon as both of its ends are known, which is what
keeps the search from placing a whole model before discovering that two of its vertices cannot be
joined. -/
def tasks (H : CGraph) (hs : List H.V) : List (Task H) :=
  hs.flatMap fun x ↦ Task.place x :: (hs.filter fun y ↦ oriented H hs x y).map (Task.route x)

theorem place_mem_tasks {hs : List H.V} {x : H.V} (hx : x ∈ hs) : Task.place x ∈ tasks H hs :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_cons_self ..⟩

theorem route_mem_tasks {hs : List H.V} {x y : H.V} (hx : x ∈ hs) (hy : y ∈ hs)
    (h : oriented H hs x y = true) : Task.route x y ∈ tasks H hs :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hy, h⟩, rfl⟩)⟩

/-! ## Reading an assignment

Everything the search checks is stated over the *entries* of the assignment rather than over what
a lookup finds in it.  That is what makes the pruning easy to justify: a candidate is filtered
against the entries made so far, and those entries are entries of the finished assignment too, so
the test the leaf applies is exactly the test the filter needs. -/

/-- The branch vertices an assignment names. -/
def branches (asg : Asg H G) : List (H.V × G.V) :=
  asg.filterMap fun p ↦ match p with
    | (.place x, [u]) => some (x, u)
    | _ => none

/-- The runs an assignment names. -/
def runs (asg : Asg H G) : List (H.V × H.V × List G.V) :=
  asg.filterMap fun p ↦ match p with
    | (.route x y, s) => some (x, y, s)
    | _ => none

theorem mem_branches {asg : Asg H G} {x : H.V} {u : G.V} (h : (Task.place x, [u]) ∈ asg) :
    (x, u) ∈ branches asg := List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_runs {asg : Asg H G} {x y : H.V} {s : List G.V} (h : (Task.route x y, s) ∈ asg) :
    (x, y, s) ∈ runs asg := List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem branches_append (l m : Asg H G) : branches (l ++ m) = branches l ++ branches m :=
  List.filterMap_append ..

theorem runs_append (l m : Asg H G) : runs (l ++ m) = runs l ++ runs m := List.filterMap_append ..

/-- The branch vertex an assignment gives `x`, if it gives it one. -/
def findB (x : H.V) : List (H.V × G.V) → Option G.V
  | [] => none
  | (z, u) :: rest => if x = z then some u else findB x rest

/-- The run an assignment gives the edge from `x` to `y`, if it gives it one. -/
def findR (x y : H.V) : List (H.V × H.V × List G.V) → Option (List G.V)
  | [] => none
  | (z, w, s) :: rest => if x = z ∧ y = w then some s else findR x y rest

theorem findB_mem {x : H.V} {u : G.V} : ∀ {l : List (H.V × G.V)}, findB x l = some u → (x, u) ∈ l
  | [], h => by rw [findB] at h; exact absurd h (by simp)
  | (z, v) :: rest, h => by
    rw [findB] at h
    split at h
    · rename_i he; subst he; rw [Option.some_inj] at h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (findB_mem h)

theorem findB_isSome {x : H.V} {u : G.V} : ∀ {l : List (H.V × G.V)}, (x, u) ∈ l →
    (findB x l).isSome
  | [], h => absurd h (by simp)
  | (z, v) :: rest, h => by
    rw [findB]
    split
    · simp
    · rename_i hne
      rcases List.mem_cons.mp h with he | hm
      · exact absurd (Prod.mk.injEq .. ▸ he).1 hne
      · exact findB_isSome hm

theorem findR_mem {x y : H.V} {s : List G.V} :
    ∀ {l : List (H.V × H.V × List G.V)}, findR x y l = some s → (x, y, s) ∈ l
  | [], h => by rw [findR] at h; exact absurd h (by simp)
  | (z, w, t) :: rest, h => by
    rw [findR] at h
    split at h
    · rename_i he; obtain ⟨rfl, rfl⟩ := he; rw [Option.some_inj] at h; subst h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (findR_mem h)

theorem findR_isSome {x y : H.V} {s : List G.V} :
    ∀ {l : List (H.V × H.V × List G.V)}, (x, y, s) ∈ l → (findR x y l).isSome
  | [], h => absurd h (by simp)
  | (z, w, t) :: rest, h => by
    rw [findR]
    split
    · simp
    · rename_i hne
      rcases List.mem_cons.mp h with he | hm
      · simp only [Prod.mk.injEq] at he
        exact absurd ⟨he.1, he.2.1⟩ hne
      · exact findR_isSome hm

/-- The run an assignment gives the edge from `x` to `y`, as a list. -/
def runOf (asg : Asg H G) (x y : H.V) : List G.V := (findR x y (runs asg)).getD []

/-- A route task is only ever generated for an edge in its canonical orientation. -/
theorem oriented_of_route_mem_tasks {hs : List H.V} {x y : H.V}
    (h : Task.route x y ∈ tasks H hs) : oriented H hs x y = true := by
  rw [tasks, List.mem_flatMap] at h
  obtain ⟨z, _, hmem⟩ := h
  rcases List.mem_cons.mp hmem with he | hmap
  · exact absurd he (by simp)
  · obtain ⟨w, hw, he⟩ := List.mem_map.mp hmap
    simp only [Task.route.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact (List.mem_filter.mp hw).2

/-- A branch vertex is one vertex. -/
def placeShape (p : Task H × List G.V) : Bool :=
  match p with
  | (.place _, l) => l.length == 1
  | (.route _ _, _) => true

theorem mem_branches_of_subset {asg asg' : Asg H G} (h : asg ⊆ asg') {p : H.V × G.V}
    (hp : p ∈ branches asg) : p ∈ branches asg' := by
  obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
  exact List.mem_filterMap.mpr ⟨q, h hq, hqp⟩

theorem mem_runs_of_subset {asg asg' : Asg H G} (h : asg ⊆ asg') {r : H.V × H.V × List G.V}
    (hr : r ∈ runs asg) : r ∈ runs asg' := by
  obtain ⟨q, hq, hqr⟩ := List.mem_filterMap.mp hr
  exact List.mem_filterMap.mpr ⟨q, h hq, hqr⟩

end CGraph
