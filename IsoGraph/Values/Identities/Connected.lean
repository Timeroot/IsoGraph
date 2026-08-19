import IsoGraph.Values.Identities.Semiring

/-!
# The connected graphs as a submonoid

The three products that a connected graph survives — the cartesian, the strong and the
lexicographic — each make the connected graphs a `Submonoid` of the graphs, since the one-vertex
graph is connected and is the unit of all three.  Those are `CartesianProduct.connectedSubmonoid`
and its two companions, and they are where unique factorisation lives: Sabidussi and Vizing for the
cartesian product, Dörfler and Imrich and McKenzie for the strong one, prove that a connected graph
factors uniquely into connected graphs that are prime for the product in question, whereas
`Identities/Factorization.lean` shows that over *all* graphs factorisation is not unique.  Neither
theorem is formalised here.

There is no corresponding subsemiring, and not for want of trying: a disjoint union of two nonempty
graphs is never connected, so the connected graphs are not closed under the addition of either
semiring.  That is `Semiring.not_isConnected_add`, and it is the reason the sub*monoid* is the most
that can be asked for.  The join does preserve connectivity — indeed it creates it — but its
identity `empty 0` is not connected, so the connected graphs are not an `AddSubmonoid` of the join
either; what they are there is a subsemigroup, recorded as `Join.isConnected_add`.

The tensor product is left out.  It preserves connectivity only when one factor is non-bipartite
(`isConnected_tensorProduct`), and it has no unit at all, so there is no submonoid to form.

All the closure lemmas this file uses are proved much earlier, with the products themselves and
without any algebraic scope open; the only thing added here is the packaging.
-/

set_option autoImplicit false

namespace IsoGraph

namespace CartesianProduct

/-- **The connected graphs are a submonoid under the cartesian product**: `K₁` is connected, and a
cartesian product is connected exactly when both factors are. -/
def connectedSubmonoid : Submonoid IsoGraph where
  carrier := {G : IsoGraph | G.IsConnected}
  one_mem' := isConnected_empty_one
  mul_mem' ha hb := isConnected_cartesianProduct.2 ⟨ha, hb⟩

@[simp] theorem mem_connectedSubmonoid {G : IsoGraph} :
    G ∈ connectedSubmonoid ↔ G.IsConnected := Iff.rfl

/-- A power of a connected graph is connected. -/
theorem isConnected_pow {G : IsoGraph} (h : G.IsConnected) (n : ℕ) : (G ^ n).IsConnected :=
  connectedSubmonoid.pow_mem h n

end CartesianProduct

namespace StrongProduct

/-- **The connected graphs are a submonoid under the strong product**, which contains the cartesian
product and so is connected whenever that is. -/
def connectedSubmonoid : Submonoid IsoGraph where
  carrier := {G : IsoGraph | G.IsConnected}
  one_mem' := isConnected_empty_one
  mul_mem' ha hb := isConnected_strongProduct ha hb

@[simp] theorem mem_connectedSubmonoid {G : IsoGraph} :
    G ∈ connectedSubmonoid ↔ G.IsConnected := Iff.rfl

/-- A power of a connected graph is connected. -/
theorem isConnected_pow {G : IsoGraph} (h : G.IsConnected) (n : ℕ) : (G ^ n).IsConnected :=
  connectedSubmonoid.pow_mem h n

end StrongProduct

namespace LexProduct

/-- **The connected graphs are a submonoid under the lexicographic product**, which also contains
the cartesian product.  Unique factorisation fails here even for connected graphs. -/
def connectedSubmonoid : Submonoid IsoGraph where
  carrier := {G : IsoGraph | G.IsConnected}
  one_mem' := isConnected_empty_one
  mul_mem' ha hb := isConnected_lexProduct ha hb

@[simp] theorem mem_connectedSubmonoid {G : IsoGraph} :
    G ∈ connectedSubmonoid ↔ G.IsConnected := Iff.rfl

/-- A power of a connected graph is connected. -/
theorem isConnected_pow {G : IsoGraph} (h : G.IsConnected) (n : ℕ) : (G ^ n).IsConnected :=
  connectedSubmonoid.pow_mem h n

end LexProduct

namespace Join

/-- **The connected graphs are closed under the join**, and then some: a join of two nonempty
graphs is connected however disconnected the two are.  They are not an `AddSubmonoid`, the
identity `empty 0` of the join having no vertex to connect. -/
theorem isConnected_add {G H : IsoGraph} (hG : G.IsConnected) (hH : H.IsConnected) :
    (G + H).IsConnected :=
  isConnected_join hG.V_pos hH.V_pos

end Join

namespace Semiring

/-- **The connected graphs are not closed under addition**, so they are no subsemiring: the sum is
the disjoint union, which falls apart into the two summands. -/
theorem not_isConnected_add {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ (G + H).IsConnected :=
  not_isConnected_disjUnion hG hH

end Semiring

namespace StrongSemiring

/-- **The connected graphs are not closed under addition**, so they are no subsemiring. -/
theorem not_isConnected_add {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ (G + H).IsConnected :=
  not_isConnected_disjUnion hG hH

end StrongSemiring

end IsoGraph
