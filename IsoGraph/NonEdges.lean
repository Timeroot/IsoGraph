import IsoGraph.SmallGraphs

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Counting the non-edges

Two distinct vertices are either joined or independent, so the edges and the independent pairs
between them account for all `V choose 2` pairs: `indepCount_two_add_E`.  That turns the number of
independent pairs into a table lookup rather than a search — any family whose order and size are
both known has its independent pairs known too — and this file spends the identity on the families
where the library had the two halves but not the difference.

Subtraction on `ℕ` truncates, so none of the proofs below states the answer as `V choose 2 - E`
and rewrites; each one puts the addition and the two table entries in front of `omega` and lets it
find the normal form.  What that costs is an occasional side condition — a hypercube has to be
told that `n + 2 ≤ 2 ^ (n + 1)` before the subtraction in its answer is the honest one.
-/

namespace IsoGraph

/-- The independent pairs are exactly the pairs that are not edges. -/
theorem indepCount_two (G : IsoGraph) : G.indepCount 2 = G.V.choose 2 - G.E := by
  have h := indepCount_two_add_E G
  omega

/-- A crown is a complete bipartite graph minus a perfect matching, so a pair of its `2 n` vertices
is independent exactly when the two lie on the same side or are matched to each other: `n ^ 2`
pairs in all. -/
theorem indepCount_crown (n : ℕ) : (crown n).indepCount 2 = n ^ 2 := by
  have h := indepCount_two_add_E (crown n)
  rw [V_crown, E_crown, choose_two_two_mul] at h
  have h2 := two_mul_choose_two n
  rcases n with _ | m
  · simp
  · rw [show m + 1 - 1 = m from rfl] at h2
    have e : (m + 1) * (2 * (m + 1) - 1) = (m + 1) * m + (m + 1) ^ 2 := by
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]; ring
    omega

/-- The ladder on `2 (n + 1)` vertices has `3 n + 1` edges, so `2 n ^ 2` independent pairs. -/
theorem indepCount_ladder (n : ℕ) : (ladder (n + 1)).indepCount 2 = 2 * n ^ 2 := by
  have h := indepCount_two_add_E (ladder (n + 1))
  rw [V_ladder, E_ladder, show (n + 1) * 2 = 2 * (n + 1) from by ring, choose_two_two_mul] at h
  have e : (n + 1) * (2 * (n + 1) - 1) = (3 * n + 1) + 2 * n ^ 2 := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega]; ring
  omega

/-- Closing the ladder into a prism adds two edges and removes two independent pairs. -/
theorem indepCount_prism (n : ℕ) : (prism (n + 3)).indepCount 2 = 2 * (n + 1) * (n + 3) := by
  have h := indepCount_two_add_E (prism (n + 3))
  rw [V_prism, E_prism, show (n + 3) * 2 = 2 * (n + 3) from by ring, choose_two_two_mul] at h
  have e : (n + 3) * (2 * (n + 3) - 1) = 3 * (n + 3) + 2 * (n + 1) * (n + 3) := by
    rw [show 2 * (n + 3) - 1 = 2 * n + 5 from by omega]; ring
  omega

/-- Every generalised Petersen graph is cubic on `2 n` vertices, so the count does not depend on
the step size. -/
theorem indepCount_gp {n k : ℕ} (h3 : 3 ≤ n) (hk : 0 < k) (hkn : k < n) (h2k : 2 * k ≠ n) :
    (gp n k).indepCount 2 = 2 * n * (n - 2) := by
  have h := indepCount_two_add_E (gp n k)
  rw [V_gp, E_gp h3 hk hkn h2k, choose_two_two_mul] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e : (m + 3) * (2 * (m + 3) - 1) = 3 * (m + 3) + 2 * (m + 3) * (m + 3 - 2) := by
    rw [show 2 * (m + 3) - 1 = 2 * m + 5 from by omega, show m + 3 - 2 = m + 1 from by omega]
    ring
  omega

/-- A vertex of the hypercube is non-adjacent to all but `n + 1` of the `2 ^ (n + 1)` vertices. -/
theorem indepCount_hypercube (n : ℕ) :
    (hypercube (n + 1)).indepCount 2 = 2 ^ n * (2 ^ (n + 1) - n - 2) := by
  have h := indepCount_two_add_E (hypercube (n + 1))
  rw [V_hypercube, pow_succ, Nat.mul_comm (2 ^ n) 2, choose_two_two_mul, E_hypercube_succ] at h
  have hn : n + 2 ≤ 2 * 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    omega
  have e : 2 ^ n * (2 * 2 ^ n - 1) = 2 ^ n * (2 * 2 ^ n - n - 2) + (n + 1) * 2 ^ n := by
    rw [show 2 * 2 ^ n - 1 = (2 * 2 ^ n - n - 2) + (n + 1) from by omega]; ring
  rw [pow_succ, Nat.mul_comm (2 ^ n) 2]
  omega

/-- The Mycielskian doubles the vertices and adds an apex, and each of its `3 E + V` edges kills
one of the `(2 V + 1) choose 2` pairs. -/
theorem indepCount_mycielskian (G : IsoGraph) :
    (mycielskian G).indepCount 2 = 2 * G.V ^ 2 - 3 * G.E := by
  have h := indepCount_two_add_E (mycielskian G)
  rw [V_mycielskian, E_mycielskian, choose_two_two_mul_add_one] at h
  have e : G.V * (2 * G.V + 1) = 2 * G.V ^ 2 + G.V := by ring
  omega

/-- The cube in LCF notation: `28 - 12` independent pairs. -/
theorem indepCount_lcf_cube : (lcf [3, -3] 4).indepCount 2 = 16 := by
  rw [hypercube_three_lcf, show (3 : ℕ) = 2 + 1 from rfl, indepCount_hypercube]
  norm_num

end IsoGraph
