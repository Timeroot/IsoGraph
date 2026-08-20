import IsoGraph.Core.Quotient

/-!
# The invariants that are read off another graph

`Invariants/Basic.lean` defines the invariants that are computed from a graph directly.  Three
more are computed from a graph *built* out of it, so they have to wait until the constructions of
`Core/Defs.lean` are in hand — but they are invariants, not identities, and this is
where they belong.

| invariant | is | notation |
| --- | --- | --- |
| `CGraph.edgeChromNum` | the chromatic number of the line graph | `χ'(G)` |
| `CGraph.matchNum` | the independence number of the line graph | `ν(G)` |
| `CGraph.cliqueCoverNum` | the chromatic number of the complement | `θ(G)` |

Each is `@[toIsoGraph]`-lifted the same way as the invariants of `Invariants/Basic.lean`: the
`CGraph`-level definition, the proof that an isomorphism preserves it, and — because the
definition goes through a construction rather than through `G.toSimple` — a `…_eq` lemma
rewriting the quotient-level invariant as the invariant of the quotient-level construction.  That
lemma is what every statement about these three actually uses; none of them descends to a
representative again.

`IsoGraph.IsSelfComplementary` is here for the same reason, though it is a property rather than a
number.  On the quotient it is an equation, `Gᶜ = G`, which is why it needs no isomorphism at all.

The bounds relating all four to the rest of the invariants — `Δ ≤ χ'`, `χ' ≤ 2Δ - 1`, Gallai in
the line graph, `α ≤ θ`, the vertex counts forced on a self-complementary graph — are in
`SmallGraphs/Bounds.lean`, with the other bounds.
-/

set_option autoImplicit false

namespace IsoGraph

/-! ## The edge chromatic number

An edge colouring of `G` is a vertex colouring of `L(G)`, so the chromatic index is the
chromatic number of the line graph and needs no separate well-definedness argument. -/

/-- The *edge chromatic number* (chromatic index) `χ'(G)`: the least number of colours needed
to colour the edges of `G` so that edges meeting at a vertex get different colours. -/
noncomputable def _root_.CGraph.edgeChromNum (G : CGraph) : ℕ := G.lineGraph.chromNum

@[toIsoGraph]
theorem _root_.CGraph.edgeChromNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.edgeChromNum = H.edgeChromNum :=
  CGraph.chromNum_eq_of_iso (CGraph.Iso.lineGraph i)

theorem edgeChromNum_eq (G : IsoGraph) : G.edgeChromNum = chromNum (lineGraph G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [edgeChromNum_mk, lineGraph_mk, chromNum_mk]
  rfl

/-! ## The matching number

A matching is a set of pairwise disjoint edges, that is, an independent set in the line
graph, so like the chromatic index the matching number needs no separate construction. -/

/-- The *matching number* `ν(G)`: the largest number of pairwise disjoint edges. -/
noncomputable def _root_.CGraph.matchNum (G : CGraph) : ℕ := G.lineGraph.indepNum

@[toIsoGraph]
theorem _root_.CGraph.matchNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.matchNum = H.matchNum :=
  CGraph.indepNum_eq_of_iso (CGraph.Iso.lineGraph i)

theorem matchNum_eq (G : IsoGraph) : G.matchNum = indepNum (lineGraph G) := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [matchNum_mk, lineGraph_mk, indepNum_mk]
  rfl

/-! ## The clique cover number

A partition of the vertices into cliques of `G` is a proper colouring of the complement, so
`θ(G) = χ(Ḡ)`, and every statement about it is a statement about `chromNum` in disguise. -/

/-- The *clique cover number* `θ(G)`: the least number of cliques needed to cover the
vertices. -/
noncomputable def _root_.CGraph.cliqueCoverNum (G : CGraph) : ℕ := G.compl.chromNum

@[toIsoGraph]
theorem _root_.CGraph.cliqueCoverNum_eq_of_iso {G H : CGraph} (i : G ≃cg H) :
    G.cliqueCoverNum = H.cliqueCoverNum :=
  CGraph.chromNum_eq_of_iso (CGraph.Iso.compl i)

theorem cliqueCoverNum_eq (G : IsoGraph) : G.cliqueCoverNum = chromNum Gᶜ := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [cliqueCoverNum_mk, compl_mk, chromNum_mk]
  rfl

/-! ## Self-complementary graphs -/

/-- A graph is *self-complementary* when it is isomorphic to its own complement.  Because
`IsoGraph` is the quotient of graphs by isomorphism, this is literally the equation
`Gᶜ = G`. -/
def IsSelfComplementary (G : IsoGraph) : Prop := Gᶜ = G

theorem isSelfComplementary_iff {G : IsoGraph} :
    IsSelfComplementary G ↔ Gᶜ = G := Iff.rfl

theorem IsSelfComplementary.compl_eq {G : IsoGraph} (h : IsSelfComplementary G) :
    Gᶜ = G := h

theorem isSelfComplementary_compl {G : IsoGraph} (h : IsSelfComplementary G) :
    IsSelfComplementary Gᶜ := by
  show Gᶜᶜ = Gᶜ
  rw [compl_compl, h.compl_eq]

end IsoGraph
