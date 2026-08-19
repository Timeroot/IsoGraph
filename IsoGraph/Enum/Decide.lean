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

`enumerateIso n` has 1, 2, 4, 11, 34, 156, 1044, 12346, … entries, but what it costs is not the
length: the list is the fixed points of `canonCode` among all `2 ^ (n choose 2)` codes, which is
1024 canonicalisations at `n = 5`, 32768 at `n = 6` and two million at `n = 7`.

On top of that, the library is not built with `precompileModules`, so a `native_decide` runs the
enumerator through the interpreter rather than as compiled code — a factor of a hundred or so
against the numbers in `EnumBench.lean`.  In practice `enumerateIso 5` is a second or two,
`enumerateIso 6` about forty-five, and `n = 7` is out of reach until that flag changes.  So this
is a tactic for `n ≤ 6`.

Adding `G.IsConnected` to the statement is worth it twice over, and the second time is the larger:
`enumConnCodes` grows the connected codes level by level instead of sweeping all `2 ^ (n choose 2)`
of them, so `enumerateConnIso 6` costs a fraction of `enumerateIso 6` and not merely the ratio
112/156 of their lengths.

What `P` costs on each graph is on top of that, and need not be small — a containment search is
not free — but at these orders it rarely is what dominates.
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
