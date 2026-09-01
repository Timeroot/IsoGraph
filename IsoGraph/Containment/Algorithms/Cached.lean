import IsoGraph.Containment.Algorithms.Contraction
import IsoGraph.Containment.Algorithms.Hom
import IsoGraph.Containment.Algorithms.Immersion
import IsoGraph.Containment.Algorithms.InducedSubgraph
import IsoGraph.Containment.Algorithms.Minor
import IsoGraph.Containment.Algorithms.Subgraph
import IsoGraph.Containment.Algorithms.TopMinor
import IsoGraph.Cache
import IsoGraph.Invariants.Symmetry

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The containment searches, on tabulated copies of both graphs

`Algorithms/Subgraph.lean` and its siblings take the two graphs as they are, and each asks
`H.Adj` and `G.Adj` a few million times.  For a graph out of the gallery that is a few million
scans of an edge list.  This file wraps each of the nine searches so that it runs on `cacheFin`
copies of the pattern *and* the host — adjacency matrices on `Fin n`, filled once — and transports
the answer back along `CGraph.isoCacheFin`.

Both sides are cached because the wrapper cannot know which one needs it.  The win is not split
between them: it sits entirely on whichever side has the expensive `Adj`, which for the jobs below
is the one built by `CGraph.ofEdges`, and caching the other side buys nothing over its own `n²`
fill.  Caching the host alone gets 87 of the quotient's 902 ms and the pattern alone gets 888;
for `tutte → K₃` it is the other way round.  `testing/CacheBench.lean`, cases `api-sub`,
`api-minor`, `api-con`, `api-con-self`, `api-sub-kneser`, `api-hom`, `api-quot`, `api-indminor`;
best of five interleaved rounds, in milliseconds, both fills included on the right:

| job                           | `find…` | `…Of?` |
| ----------------------------- | ------- | ------ |
| `C₄` a quotient of `tutte`    | 894     | 19     |
| `C₆ ⊆ K(10,5)`                | 163     | 46     |
| `tutte → K₃` (3-colouring)    | 39      | 2      |
| `C₄ ⋏ tutte` (contraction)    | 38      | 4      |
| `mcgee ⋏ mcgee`               | 20      | 9      |
| `K₄ ≼ tutte` (minor)          | 18      | 2      |
| `K₄` induced minor of `tutte` | 12      | 2      |
| `C₈ ⊆ tutte`                  | 5       | 1      |
| `mcgee → K₂`                  | 4       | <1     |

The quotient row carries one thing besides the fill: `CGraph.quotientOf?` and `CGraph.homOf?` also
hand the search the automorphisms of its host, which take that row from 72 ms to 19 and the
colouring row nowhere at all.  `### The symmetry the two homomorphism searches break`, below, is
where they come from and why the other seven searches have no such clause.

The `…Of?` entry points here are the ones to reach for; the underlying `find…` take a `Roster` and
run on whatever vertex type they are given, which is what to use when the graphs are already
tabulated or the search is short enough that the `n²` fill would dominate.

Each comes with `…?_eq_none_iff`, which says that `none` means the containment type is empty — so
a `none` is a complete answer and not a failure to search hard enough — and a `Bool` version with
the same guarantee, for `native_decide`.

Those `Bool` versions are what makes the nine relations of `Containment/Defs.lean` decidable *on
the quotient*, which is the last section of this file: `H ≤ₛ G` for `H G : IsoGraph` is settled by
running the search on the canonical representatives.  So a containment may be `decide`d, or put
inside a `native_decide` over a whole enumeration.
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

theorem isEmpty_inducedMinorOf_cacheFin :
    IsEmpty (H.cacheFin.InducedMinorOf G.cacheFin) ↔ IsEmpty (H.InducedMinorOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_contractionOf_cacheFin :
    IsEmpty (H.cacheFin.ContractionOf G.cacheFin) ↔ IsEmpty (H.ContractionOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_hom_cacheFin :
    IsEmpty (H.cacheFin →cg G.cacheFin) ↔ IsEmpty (H →cg G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (homCongr f H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (homCongr f H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_topMinorOf_cacheFin :
    IsEmpty (H.cacheFin.TopMinorOf G.cacheFin) ↔ IsEmpty (H.TopMinorOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_immersionOf_cacheFin :
    IsEmpty (H.cacheFin.ImmersionOf G.cacheFin) ↔ IsEmpty (H.ImmersionOf G) :=
  ⟨fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin G.isoCacheFin)⟩,
    fun h ↦ ⟨fun f ↦ h.false (f.congr H.isoCacheFin.symm G.isoCacheFin.symm)⟩⟩

theorem isEmpty_quotientOf_cacheFin :
    IsEmpty (H.cacheFin.QuotientOf G.cacheFin) ↔ IsEmpty (H.QuotientOf G) :=
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

/-- **Is `H` an induced minor of `G`?**  Returns the branch sets if so — a set of them with no
edge of `G` between two of them that `H` does not have. -/
def inducedMinorOf? : Option (H.InducedMinorOf G) :=
  (findInducedMinor H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` a topological minor of `G`?**  Returns a subdivision of `H` inside `G` if so: the
branch vertices, and the path each edge of `H` runs along. -/
def topMinorOf? : Option (H.TopMinorOf G) :=
  (findTopMinor H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` immersed in `G`?**  Returns the branch vertices, and the trail each edge of `H` runs
along, if so — trails that share no edge, though they may share vertices. -/
def immersionOf? : Option (H.ImmersionOf G) :=
  (findImmersion H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` a contraction of `G`?**  Returns the partition of `G` into blocks if so. -/
def contractionOf? : Option (H.ContractionOf G) :=
  (findContraction H.cacheFin G.cacheFin (Roster.fin _) (Roster.fin _)).map
    (·.congr H.isoCacheFin.symm G.isoCacheFin.symm)

/-! ### The symmetry the two homomorphism searches break

`Algorithms/Hom.lean` prunes a node by the automorphisms of the *host* of the search, and takes
them as an argument because it cannot know what they cost to come by.  Here they are computed, by
the canonical labelling search of `Invariants/Symmetry.lean` — but only when the host is small,
which is exactly when they pay:

* the host of `CGraph.homOf? H G` is `G`, and the case this is for is a colouring, where `G` is
  `complete k` and the `k!` relabellings of a colouring collapse to one;
* the host of `CGraph.quotientOf? H G` is `H`, which is small whenever the question is interesting
  — a quotient onto something as big as `G` is an isomorphism.

Against a large host a run of the canonical labelling search costs more than the whole of some of
the searches above (about 2 ms on `tutte`, which is the entire `tutte → K₃` job), so `autThreshold`
turns it off there.  Nothing about correctness turns on either constant: the search is right for
any list of automorphisms of its host, including none, so both may be tuned freely. -/

/-- How big a host is worth computing the automorphisms of. -/
private def autThreshold : ℕ := 20

/-- How many of them to carry.  Every element costs a machine word at each node and about 15 µs to
have, so a group as big as `S₅` is not worth taking whole; any subset of it prunes soundly. -/
private def autCap : ℕ := 32

/-- **The symmetry a search hosted by `X` may break**, for a graph already indexed by `e`.  Taking
the indexed copy as an argument rather than making one is what keeps `CGraph.homOf?` below to a
single `cacheFin` fill of each side. -/
def searchAutData (X : CGraph) {n : ℕ} (e : X.V ≃ Fin n) (rX : Roster X.V) :
    AutData X rX.toList :=
  autData X rX <|
    if n ≤ autThreshold then autClosure X rX (X.autGens e).toList autCap else []

/-- **Is there a homomorphism `H → G`?**  Returns one if so.  Against `complete k` this is
`k`-colourability of `H`, with the colouring. -/
def homOf? : Option (H →cg G) :=
  let Gc := G.cacheFin
  let rG : Roster Gc.V := Roster.fin _
  (findHom H.cacheFin Gc (Roster.fin _) rG (searchAutData Gc G.cacheFinEquiv rG)).map
    (homCongr · H.isoCacheFin.symm G.isoCacheFin.symm)

/-- **Is `H` a quotient of `G`?**  Returns the surjection if so. -/
def quotientOf? : Option (H.QuotientOf G) :=
  let Hc := H.cacheFin
  let rH : Roster Hc.V := Roster.fin _
  (findQuotient Hc G.cacheFin rH (Roster.fin _) (searchAutData Hc H.cacheFinEquiv rH)).map
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

theorem inducedMinorOf?_eq_none_iff :
    H.inducedMinorOf? G = none ↔ IsEmpty (H.InducedMinorOf G) := by
  rw [inducedMinorOf?, Option.map_eq_none_iff, ← isEmpty_inducedMinorOf_iff,
    isEmpty_inducedMinorOf_cacheFin]

theorem topMinorOf?_eq_none_iff : H.topMinorOf? G = none ↔ IsEmpty (H.TopMinorOf G) := by
  rw [topMinorOf?, Option.map_eq_none_iff, ← isEmpty_topMinorOf_iff, isEmpty_topMinorOf_cacheFin]

theorem immersionOf?_eq_none_iff : H.immersionOf? G = none ↔ IsEmpty (H.ImmersionOf G) := by
  rw [immersionOf?, Option.map_eq_none_iff, ← isEmpty_immersionOf_iff,
    isEmpty_immersionOf_cacheFin]

theorem contractionOf?_eq_none_iff : H.contractionOf? G = none ↔ IsEmpty (H.ContractionOf G) := by
  rw [contractionOf?, Option.map_eq_none_iff, ← isEmpty_contractionOf_iff,
    isEmpty_contractionOf_cacheFin]

theorem homOf?_eq_none_iff : H.homOf? G = none ↔ IsEmpty (H →cg G) := by
  rw [homOf?, Option.map_eq_none_iff, ← isEmpty_hom_iff, isEmpty_hom_cacheFin]

theorem quotientOf?_eq_none_iff : H.quotientOf? G = none ↔ IsEmpty (H.QuotientOf G) := by
  rw [quotientOf?, Option.map_eq_none_iff, ← isEmpty_quotientOf_iff, isEmpty_quotientOf_cacheFin]

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

/-- **Is `H` an induced minor of `G`?**, as a `Bool`. -/
def inducedMinorB : Bool := (H.inducedMinorOf? G).isSome

/-- **Is `H` a topological minor of `G`?**, as a `Bool`. -/
def topMinorB : Bool := (H.topMinorOf? G).isSome

/-- **Is `H` immersed in `G`?**, as a `Bool`. -/
def immersionB : Bool := (H.immersionOf? G).isSome

/-- **Is `H` a contraction of `G`?**, as a `Bool`. -/
def contractionB : Bool := (H.contractionOf? G).isSome

/-- **Is there a homomorphism `H → G`?**, as a `Bool`. -/
def homB : Bool := (H.homOf? G).isSome

/-- **Is `H` a quotient of `G`?**, as a `Bool`. -/
def quotientB : Bool := (H.quotientOf? G).isSome

theorem subgraphB_iff : H.subgraphB G = true ↔ Nonempty (H.SubgraphOf G) := by
  rw [subgraphB, ← not_isEmpty_iff, ← subgraphOf?_eq_none_iff]
  cases H.subgraphOf? G <;> simp

theorem inducedSubgraphB_iff : H.inducedSubgraphB G = true ↔ Nonempty (H.InducedSubgraphOf G) := by
  rw [inducedSubgraphB, ← not_isEmpty_iff, ← inducedSubgraphOf?_eq_none_iff]
  cases H.inducedSubgraphOf? G <;> simp

theorem minorB_iff : H.minorB G = true ↔ Nonempty (H.MinorOf G) := by
  rw [minorB, ← not_isEmpty_iff, ← minorOf?_eq_none_iff]
  cases H.minorOf? G <;> simp

theorem inducedMinorB_iff : H.inducedMinorB G = true ↔ Nonempty (H.InducedMinorOf G) := by
  rw [inducedMinorB, ← not_isEmpty_iff, ← inducedMinorOf?_eq_none_iff]
  cases H.inducedMinorOf? G <;> simp

theorem topMinorB_iff : H.topMinorB G = true ↔ Nonempty (H.TopMinorOf G) := by
  rw [topMinorB, ← not_isEmpty_iff, ← topMinorOf?_eq_none_iff]
  cases H.topMinorOf? G <;> simp

theorem immersionB_iff : H.immersionB G = true ↔ Nonempty (H.ImmersionOf G) := by
  rw [immersionB, ← not_isEmpty_iff, ← immersionOf?_eq_none_iff]
  cases H.immersionOf? G <;> simp

theorem contractionB_iff : H.contractionB G = true ↔ Nonempty (H.ContractionOf G) := by
  rw [contractionB, ← not_isEmpty_iff, ← contractionOf?_eq_none_iff]
  cases H.contractionOf? G <;> simp

theorem homB_iff : H.homB G = true ↔ Nonempty (H →cg G) := by
  rw [homB, ← not_isEmpty_iff, ← homOf?_eq_none_iff]
  cases H.homOf? G <;> simp

theorem quotientB_iff : H.quotientB G = true ↔ Nonempty (H.QuotientOf G) := by
  rw [quotientB, ← not_isEmpty_iff, ← quotientOf?_eq_none_iff]
  cases H.quotientOf? G <;> simp

end CGraph

/-! ## The relations on `IsoGraph`, decided

Each of `Containment/Defs.lean`'s nine relations is `Quotient.lift₂` of a `Nonempty`, so it says
nothing that can be evaluated as it stands.  What decides it is the search above, run on *any*
representative of the two classes — which is exactly what `Quotient.recOnSubsingleton₂` offers,
since two `Decidable` instances for the same proposition are equal whatever they decide by.  The
`_mk` lemma then closes the gap between the relation on the class and the `Nonempty` on the
representative.

Deciding on the representative that is already to hand rather than on `H.toCGraph` is worth
roughly a factor of two on a short search: `toCGraph` runs the canonical labelling, which for a
graph on six vertices costs more than the subgraph search it would be preparing for.  Nothing is
lost by skipping it — each search tabulates its two graphs with `cacheFin` regardless, so the
adjacency it ends up reading is an array either way.

The searches are exponential in the pattern, so these are for small graphs — but "small" here is
the whole gallery, and it is exactly what an exhaustive check over `Enum/Decide.lean`'s
enumerations wants. -/

namespace IsoGraph

instance instDecidableHasHomInto : ∀ H G : IsoGraph, Decidable (H ≤ₕ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₕ G)) H G fun H G ↦
    decidable_of_iff (H.homB G = true) <| by rw [CGraph.homB_iff, hasHomInto_mk]

instance instDecidableIsSubgraphOf : ∀ H G : IsoGraph, Decidable (H ≤ₛ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₛ G)) H G fun H G ↦
    decidable_of_iff (H.subgraphB G = true) <| by rw [CGraph.subgraphB_iff, isSubgraphOf_mk]

instance instDecidableIsInducedSubgraphOf : ∀ H G : IsoGraph, Decidable (H ≤ᵢₛ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ᵢₛ G)) H G fun H G ↦
    decidable_of_iff (H.inducedSubgraphB G = true) <| by
      rw [CGraph.inducedSubgraphB_iff, isInducedSubgraphOf_mk]

instance instDecidableHasQuotient : ∀ G H : IsoGraph, Decidable (H ≤/ G) := fun G H ↦
  Quotient.recOnSubsingleton₂ (motive := fun G H ↦ Decidable (H ≤/ G)) G H fun G H ↦
    decidable_of_iff (H.quotientB G = true) <| by rw [CGraph.quotientB_iff, hasQuotient_mk]

instance instDecidableIsMinorOf : ∀ H G : IsoGraph, Decidable (H ≤ₘ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₘ G)) H G fun H G ↦
    decidable_of_iff (H.minorB G = true) <| by rw [CGraph.minorB_iff, isMinorOf_mk]

instance instDecidableIsInducedMinorOf : ∀ H G : IsoGraph, Decidable (H ≤ᵢₘ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ᵢₘ G)) H G fun H G ↦
    decidable_of_iff (H.inducedMinorB G = true) <| by
      rw [CGraph.inducedMinorB_iff, isInducedMinorOf_mk]

instance instDecidableIsContractionOf : ∀ H G : IsoGraph, Decidable (H ≤ₚ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₚ G)) H G fun H G ↦
    decidable_of_iff (H.contractionB G = true) <| by
      rw [CGraph.contractionB_iff, isContractionOf_mk]

instance instDecidableIsTopMinorOf : ∀ H G : IsoGraph, Decidable (H ≤ₜₘ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₜₘ G)) H G fun H G ↦
    decidable_of_iff (H.topMinorB G = true) <| by rw [CGraph.topMinorB_iff, isTopMinorOf_mk]

instance instDecidableIsImmersionMinorOf : ∀ H G : IsoGraph, Decidable (H ≤ₑ G) := fun H G ↦
  Quotient.recOnSubsingleton₂ (motive := fun H G ↦ Decidable (H ≤ₑ G)) H G fun H G ↦
    decidable_of_iff (H.immersionB G = true) <| by
      rw [CGraph.immersionB_iff, isImmersionMinorOf_mk]

end IsoGraph
