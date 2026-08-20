import IsoGraph.Algebra.Factorization

/-!
# The connected graphs as a submonoid

The connected graphs form a submonoid under each of the products.
-/

namespace IsoGraph.CartesianProduct

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

end IsoGraph.CartesianProduct

namespace IsoGraph.StrongProduct

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

end IsoGraph.StrongProduct

namespace IsoGraph.LexProduct

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

end IsoGraph.LexProduct

namespace IsoGraph.Join

/-- **The connected graphs are closed under the join**, and then some: a join of two nonempty
graphs is connected however disconnected the two are.  They are not an `AddSubmonoid`, the
identity `empty 0` of the join having no vertex to connect. -/
theorem isConnected_add {G H : IsoGraph} (hG : G.IsConnected) (hH : H.IsConnected) :
    (G + H).IsConnected :=
  isConnected_join hG.V_pos hH.V_pos

end IsoGraph.Join

namespace IsoGraph.Semiring

/-- **The connected graphs are not closed under addition**, so they are no subsemiring: the sum is
the disjoint union, which falls apart into the two summands. -/
theorem not_isConnected_add {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ (G + H).IsConnected :=
  not_isConnected_disjUnion hG hH

end IsoGraph.Semiring

namespace IsoGraph.StrongSemiring

/-- **The connected graphs are not closed under addition**, so they are no subsemiring. -/
theorem not_isConnected_add {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ¬ (G + H).IsConnected :=
  not_isConnected_disjUnion hG hH

end IsoGraph.StrongSemiring
