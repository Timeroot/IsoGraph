import IsoGraph.Identities

/-!
# ATP batch targets, round fourteen

Every statement that earlier rounds left open, gathered into one file.  Each `sorry` here is a
target for the automated prover; anything that comes back proved gets moved into
`IsoGraph/Identities.lean` and this file shrinks.
-/

namespace IsoGraph

/-- The girth of a cycle is its length. -/
theorem girth_cycle (n : ℕ) : (cycle (n + 3)).girth = n + 3 := sorry

/-- The girth of a disjoint union, when both sides have a cycle. -/
theorem girth_disjUnion_of_pos {G H : IsoGraph} (hG : 0 < G.girth) (hH : 0 < H.girth) :
    (disjUnion G H).girth = min G.girth H.girth := sorry

/-- The girth of a disjoint union with an acyclic summand. -/
theorem girth_disjUnion_of_isAcyclic {G H : IsoGraph} (hG : IsAcyclic G) :
    (disjUnion G H).girth = H.girth := sorry

/-- **Kneser's conjecture for `k = 2`**: the chromatic number of `K(n, 2)` is `n - 2`. -/
theorem chromNum_kneser_two (n : ℕ) : (kneser (n + 4) 2).chromNum = n + 2 := sorry

/-- **A Kneser graph is `(n - 2k + 2)`-chromatic** in the first open case beyond `k = 2`: the
triples in `n ≥ 7` points need `n - 4` colours. -/
theorem chromNum_kneser_three (n : ℕ) : (kneser (n + 7) 3).chromNum = n + 3 := sorry

/-- A ladder needs about half of its rungs dominated: `γ(P_m □ K₂) = ⌈(m + 1) / 2⌉`. -/
theorem domNum_ladder (n : ℕ) : (ladder (n + 1)).domNum = (n + 3) / 2 := sorry

/-- The triangular graph is connected and vertex transitive, so it has a near-perfect
matching. -/
theorem matchNum_triangular (n : ℕ) :
    (triangular (n + 4)).matchNum = (n + 4).choose 2 / 2 := sorry

/-- The Kneser graph `K(n, 2)` is connected and vertex transitive, so it has a near-perfect
matching. -/
theorem matchNum_kneser_two (n : ℕ) :
    (kneser (n + 5) 2).matchNum = (n + 5).choose 2 / 2 := sorry

end IsoGraph
