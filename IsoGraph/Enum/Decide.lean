import IsoGraph.Enum.All
import IsoGraph.Enum.Conn
import IsoGraph.Invariants.Symmetry
import IsoGraph.Invariants.Derived

/-!
# `small_graphs`: proving a statement by checking every graph of a given order

`Enum/All.lean` and `Enum/Conn.lean` list one representative of every isomorphism class of a
given order, and — read in `IsoGraph` — that list is the *set* of isomorphism classes of that
order.  So a statement of the form

    ∀ G : IsoGraph, G.V = n → P G

is a statement about a finite list, and if `P` is decidable it is a computation.  That is what the
`small_graphs` tactic does: it rewrites the goal into `∀ G ∈ …, P G` with one of the three lemmas
below and hands the result to `native_decide`.

    theorem foo : ∀ G : IsoGraph, G.V = 5 → G.IsConnected → 2 ≤ G.minDeg →
        (G.IsVertexTransitive ↔ 5 ∣ G.E) := by
      small_graphs

The three goal shapes it recognises, in the order it tries them:

| shape | list | lemma |
| --- | --- | --- |
| `∀ G, G.V = n → G.IsConnected → P G` | `enumerateConnIso n` | `forall_conn_of_forall_mem` |
| `∀ G, G.V = n → P G` | `enumerateIso n` | `forall_eq_V_of_forall_mem` |
| `∀ G, G.V ≤ n → P G` | `enumerateIsoUpTo n` | `forall_le_V_of_forall_mem` |

The connected shape is tried first because its list is the shorter one and the hypothesis is then
discharged by the enumeration rather than checked on every graph.  Hypotheses other than those two
stay inside `P`, where the decision procedure evaluates them.

## What is decidable

Everything the tactic touches has to *run*, which rules out the invariants defined by an infimum
over an unbounded set — the chromatic number, the girth, the independence and clique numbers, the
domination number — and the two derived from them.  What is left is still most of the library:

* the counts `V`, `E`, `maxDeg`, `minDeg`, `degSequence`, and anything built from them;
* equality of isomorphism classes, through `IsoGraph.instDecidableEq` of `Enum/All.lean`, so also
  `IsSelfComplementary` and any statement naming a particular graph;
* `IsConnected`, `IsAcyclic`, `IsTree`, `IsBipartite`, `IsRegularWith` and `IsSRGWith`, decided on
  the canonical representative by the instances below;
* `IsVertexTransitive` and `IsArcTransitive`, through the automorphism-group computation of
  `Invariants/Symmetry.lean` rather than by a search over all `n!` permutations;
* the containment relations `≤ₛ`, `≤ᵢₛ`, `≤ₘ`, … of `IsoGraph/Containment/`, whose instances are
  with their decision procedures in `Containment/Algorithms/Cached.lean`.

## The cost

Both lists are grown one vertex at a time, so what they cost tracks their lengths — 1, 1, 2, 4,
11, 34, 156, 1044, 12346, 274668 classes, and 1, 1, 2, 6, 21, 112, 853, 11117, 261080 connected
ones — at roughly one canonical labelling per graph.  Neither ever sweeps the `2 ^ (n choose 2)`
codes: `enumerateIso` reads as if it did, but `Enum/All.lean` redirects it onto the extension
enumerator with `@[csimp]`.  So adding `G.IsConnected` to a statement buys what the ratio 112/156
of the two lengths suggests on `P`, and nothing on the enumeration itself: the connected list is
shorter but costs slightly *more* to produce, because it also looks for a cut vertex.

Timings from `lake exe enumbench`, which runs exactly the code a `native_decide` runs:

| `n` | `enumerateIso n` | `enumerateConnIso n` |
| --- | --- | --- |
| 6 | 0.008 s | 0.007 s |
| 7 | 0.057 s | 0.066 s |
| 8 | 0.69 s | 1.1 s |
| 9 | 16 s | 31 s |

On top of that a proof pays for `P` on each graph, which need not be small — a containment search
is not free, and for `ramsey_three_three` in `Exhaustion.lean` the two of them are about a third
of the 12 ms the tactic takes — plus the few seconds of loading the library, which at `n ≤ 7`
dominates everything else.

So: both shapes are comfortable to `n = 8` and possible at `n = 9`.  All of this assumes the
library is built with `precompileModules` (see `lakefile.toml`), so that a `native_decide` runs
the enumerator as compiled code; through the interpreter every one of these is about two orders of
magnitude worse, which is what the flag is there for.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## Reducing a universally quantified statement to a list -/

/-- **Every isomorphism class of order `n` is in `enumerateIso n`**, so a property of everything
on that list is a property of every graph of that order. -/
theorem forall_eq_V_of_forall_mem {n : ℕ} {P : IsoGraph → Prop}
    (h : ∀ G ∈ CGraph.Enum.enumerateIso n, P G) (G : IsoGraph) (hG : G.V = n) : P G :=
  h G (CGraph.Enum.mem_enumerateIso hG)

/-- The same for the connected classes, whose list is the shorter one. -/
theorem forall_conn_of_forall_mem {n : ℕ} {P : IsoGraph → Prop}
    (h : ∀ G ∈ CGraph.Enum.enumerateConnIso n, P G) (G : IsoGraph) (hG : G.V = n)
    (hc : G.IsConnected) : P G :=
  h G (CGraph.Enum.mem_enumerateConnIso hG hc)

/-- One representative of every isomorphism class of order **at most** `n`. -/
def enumerateIsoUpTo (n : ℕ) : List IsoGraph :=
  (List.range (n + 1)).flatMap CGraph.Enum.enumerateIso

theorem mem_enumerateIsoUpTo {n : ℕ} {G : IsoGraph} (h : G.V ≤ n) : G ∈ enumerateIsoUpTo n :=
  List.mem_flatMap.2 ⟨G.V, List.mem_range.2 (by omega), CGraph.Enum.mem_enumerateIso rfl⟩

@[simp] theorem V_of_mem_enumerateIsoUpTo {n : ℕ} {G : IsoGraph} (h : G ∈ enumerateIsoUpTo n) :
    G.V ≤ n := by
  obtain ⟨m, hm, hG⟩ := List.mem_flatMap.1 h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hG
  rw [V_mk, CGraph.Enum.card_of_mem_enumerate hg]
  exact Nat.lt_succ_iff.1 (List.mem_range.1 hm)

/-- **Every isomorphism class of order at most `n` is in `enumerateIsoUpTo n`.** -/
theorem forall_le_V_of_forall_mem {n : ℕ} {P : IsoGraph → Prop}
    (h : ∀ G ∈ enumerateIsoUpTo n, P G) (G : IsoGraph) (hG : G.V ≤ n) : P G :=
  h G (mem_enumerateIsoUpTo hG)

/-! ## Deciding the predicates on the quotient

Each of these decides the property on the canonical representative `G.toCGraph`, whose class is
`G` again (`mk_toCGraph`).  The `CGraph`-level instances are in `Invariants/Basic.lean`; the two
transitivity ones go through the automorphism-group computation instead, which is what makes them
usable past four or five vertices. -/

instance : DecidablePred IsConnected := fun G ↦
  decidable_of_iff G.toCGraph.IsConnected (by rw [← isConnected_mk, mk_toCGraph])

instance : DecidablePred IsAcyclic := fun G ↦
  decidable_of_iff G.toCGraph.IsAcyclic (by rw [← isAcyclic_mk, mk_toCGraph])

instance : DecidablePred IsTree := fun G ↦
  decidable_of_iff G.toCGraph.IsTree (by rw [← isTree_mk, mk_toCGraph])

instance : DecidablePred IsBipartite := fun G ↦
  decidable_of_iff G.toCGraph.IsBipartite (by rw [← isBipartite_mk, mk_toCGraph])

instance (k : ℕ) : DecidablePred (IsRegularWith · k) := fun G ↦
  decidable_of_iff (G.toCGraph.IsRegularWith k) (by rw [← isRegularWith_mk, mk_toCGraph])

instance (n k ℓ μ : ℕ) : DecidablePred (IsSRGWith · n k ℓ μ) := fun G ↦
  decidable_of_iff (G.toCGraph.IsSRGWith n k ℓ μ) (by rw [← isSRGWith_mk, mk_toCGraph])

instance : DecidablePred IsVertexTransitive := fun G ↦
  decidable_of_iff (G.vertexTransitiveB = true) G.vertexTransitiveB_iff

instance : DecidablePred IsArcTransitive := fun G ↦
  decidable_of_iff (G.arcTransitiveB = true) G.arcTransitiveB_iff

instance : DecidablePred IsSelfComplementary := fun G ↦
  decidable_of_iff (Gᶜ = G) isSelfComplementary_iff.symm

/-! ## The tactic -/

/-- **Prove a statement about every graph of a given order by checking all of them.**

The goal must be one of

    ∀ G : IsoGraph, G.V = n → G.IsConnected → P G
    ∀ G : IsoGraph, G.V = n → P G
    ∀ G : IsoGraph, G.V ≤ n → P G

with `n` a literal and `P` decidable; the tactic replaces it by the corresponding statement about
`CGraph.Enum.enumerateConnIso n`, `CGraph.Enum.enumerateIso n` or `enumerateIsoUpTo n` and runs
`native_decide`.  A goal with the graph already introduced needs `revert` first.

The shape is chosen first and the check runs once, so a `native_decide` that fails — because the
statement is false, or because something in it does not reduce — says so itself rather than being
retried against the other two shapes. -/
syntax (name := smallGraphs) "small_graphs" : tactic

macro_rules
  | `(tactic| small_graphs) =>
    `(tactic|
        (first
          | refine IsoGraph.forall_conn_of_forall_mem ?_
          | refine IsoGraph.forall_eq_V_of_forall_mem ?_
          | refine IsoGraph.forall_le_V_of_forall_mem ?_
          | fail "small_graphs: the goal should be `∀ G : IsoGraph, G.V = n → …`, \
                  `∀ G : IsoGraph, G.V = n → G.IsConnected → …` or \
                  `∀ G : IsoGraph, G.V ≤ n → …`") <;> native_decide)

end IsoGraph
