import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Graphs.Cache

/-!
# The containment searches, on tabulated copies of both graphs

`Algorithms/Subgraph.lean` and its three siblings take the two graphs as they are, and each asks
`H.Adj` and `G.Adj` a few million times.  For a graph out of the gallery that is a few million
scans of an edge list.  This file wraps each of the four searches so that it runs on `cacheFin`
copies of the pattern *and* the host — adjacency matrices on `Fin n`, filled once — and transports
the answer back along `CGraph.isoCacheFin`.

Both sides are worth caching, and the effect multiplies: caching the pattern alone or the host
alone each recovers about half of the following, and the numbers below are the two together.
`CacheBench.lean`, cases `api-sub`, `api-minor`, `api-con`, `api-con-self`, `api-sub-kneser`; best
of three interleaved rounds, in milliseconds; the cost of filling both arrays is included in the
right-hand column:

| job                        | `find…` | `…Of?` |
| -------------------------- | ------- | ------ |
| `C₄ ⋏ tutte` (contraction) | 5957    | 478    |
| `mcgee ⋏ mcgee`            | 353     | 63     |
| `C₆ ⊆ K(10,5)`             | 403     | 120    |
| `K₄ ≼ tutte` (minor)       | 31      | 7      |
| `C₈ ⊆ tutte`               | 7       | 3      |

The `…Of?` entry points here are the ones to reach for; the underlying `find…` take a `Roster` and
run on whatever vertex type they are given, which is what to use when the graphs are already
tabulated or the search is short enough that the `n²` fill would dominate.

Each comes with `…?_eq_none_iff`, which says that `none` means the containment type is empty — so
a `none` is a complete answer and not a failure to search hard enough — and a `Bool` version with
the same guarantee, for `native_decide`.
-/

set_option autoImplicit false

open Backtrack

namespace CGraph

variable (H G : CGraph)

/-! ## Transporting an answer

The searches run on `H.cacheFin` and `G.cacheFin`, which are isomorphic to `H` and `G` but not
equal to them, so both the witness and the emptiness statement have to come back across
`CGraph.isoCacheFin`.  The witness moves by the `congr` of each containment structure; emptiness
moves by contraposition, one `congr` in each direction. -/

theorem isEmpty_subgraphOf_cacheFin :
    IsEmpty (H.cacheFin.SubgraphOf G.cacheFin) ↔ IsEmpty (H.SubgraphOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_inducedSubgraphOf_cacheFin :
    IsEmpty (H.cacheFin.InducedSubgraphOf G.cacheFin) ↔ IsEmpty (H.InducedSubgraphOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_minorOf_cacheFin :
    IsEmpty (H.cacheFin.MinorOf G.cacheFin) ↔ IsEmpty (H.MinorOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_contractionOf_cacheFin :
    IsEmpty (H.cacheFin.ContractionOf G.cacheFin) ↔ IsEmpty (H.ContractionOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

/-! ## The entry points -/

/-- **Is `H` a subgraph of `G`?**  Returns a witness if so — not necessarily an induced one.

Runs on tabulated copies of both graphs; `CGraph.findSubgraph` is the version that takes the
graphs as they are. -/
def subgraphOf? : Option (H.SubgraphOf G) :=
  (findSubgraph H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` an induced subgraph of `G`?**  Returns a witness if so. -/
def inducedSubgraphOf? : Option (H.InducedSubgraphOf G) :=
  (findInducedSubgraph H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` a minor of `G`?**  Returns the branch sets if so. -/
def minorOf? : Option (H.MinorOf G) :=
  (findMinor H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` a contraction of `G`?**  Returns the partition of `G` into blocks if so. -/
def contractionOf? : Option (H.ContractionOf G) :=
  (findContraction H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-! ## Completeness

`none` is not "the search gave up": it is a proof that there is no such containment at all. -/

theorem subgraphOf?_eq_none_iff : H.subgraphOf? G = none ↔ IsEmpty (H.SubgraphOf G) := by
  rw [subgraphOf?, Option.map_eq_none_iff, ← isEmpty_subgraphOf_iff,
    isEmpty_subgraphOf_cacheFin]

theorem inducedSubgraphOf?_eq_none_iff :
    H.inducedSubgraphOf? G = none ↔ IsEmpty (H.InducedSubgraphOf G) := by
  rw [inducedSubgraphOf?, Option.map_eq_none_iff, ← isEmpty_inducedSubgraphOf_iff,
    isEmpty_inducedSubgraphOf_cacheFin]

theorem minorOf?_eq_none_iff : H.minorOf? G = none ↔ IsEmpty (H.MinorOf G) := by
  rw [minorOf?, Option.map_eq_none_iff, ← isEmpty_minorOf_iff, isEmpty_minorOf_cacheFin]

theorem contractionOf?_eq_none_iff : H.contractionOf? G = none ↔ IsEmpty (H.ContractionOf G) := by
  rw [contractionOf?, Option.map_eq_none_iff, ← isEmpty_contractionOf_iff,
    isEmpty_contractionOf_cacheFin]

/-! ## The `Bool` versions

`Option.isSome` of the above.  These are what `native_decide` wants: the statement to prove is a
`Prop`, and the witness — which is what the `…Of?` return — cannot cross a `native_decide` since
the kernel never sees it. -/

/-- **Is `H` a subgraph of `G`?**, as a `Bool`. -/
def subgraphB : Bool := (H.subgraphOf? G).isSome

/-- **Is `H` an induced subgraph of `G`?**, as a `Bool`. -/
def inducedSubgraphB : Bool := (H.inducedSubgraphOf? G).isSome

/-- **Is `H` a minor of `G`?**, as a `Bool`. -/
def minorB : Bool := (H.minorOf? G).isSome

/-- **Is `H` a contraction of `G`?**, as a `Bool`. -/
def contractionB : Bool := (H.contractionOf? G).isSome

theorem subgraphB_iff : H.subgraphB G = true ↔ Nonempty (H.SubgraphOf G) := by
  rw [subgraphB, ← not_isEmpty_iff, ← subgraphOf?_eq_none_iff]
  cases H.subgraphOf? G <;> simp

theorem inducedSubgraphB_iff : H.inducedSubgraphB G = true ↔ Nonempty (H.InducedSubgraphOf G) := by
  rw [inducedSubgraphB, ← not_isEmpty_iff, ← inducedSubgraphOf?_eq_none_iff]
  cases H.inducedSubgraphOf? G <;> simp

theorem minorB_iff : H.minorB G = true ↔ Nonempty (H.MinorOf G) := by
  rw [minorB, ← not_isEmpty_iff, ← minorOf?_eq_none_iff]
  cases H.minorOf? G <;> simp

theorem contractionB_iff : H.contractionB G = true ↔ Nonempty (H.ContractionOf G) := by
  rw [contractionB, ← not_isEmpty_iff, ← contractionOf?_eq_none_iff]
  cases H.contractionOf? G <;> simp

end CGraph
