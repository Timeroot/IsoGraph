import IsoGraph.TwoRegular
import IsoGraph.Edgeless

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Spectra of the degenerate members of a family

A family that is interesting for large parameters is usually something else entirely for small
ones: a tadpole with no tail is a cycle, a spider with two legs is a path, a Kneser graph on
singletons is a complete graph.  The identities that say so are, with the two exceptions proved at
the top of this file, already in `IsoGraph/SmallGraphs/Identifications.lean`; what is missing is
the arithmetic that follows from them.  This file reads those identities from left to right and
carries the spectral invariants — characteristic polynomials, spectra, energies, algebraic
connectivities, spectral determination — back across, so that asking for the spectrum of
`spider [3, 4]` does not require first noticing that it is a path on eight vertices.

Two identifications are worth their own section.  The cube appears three times over — as
`hypercube 3`, as the generalised Petersen graph `GP(4, 1)` and as the cubic graph `[3, -3]⁴` —
so its eight eigenvalues are computed once and shared; and the Mycielskian of an edgeless graph
falls apart into a star and an independent set, which makes every spectral invariant of it a
two-line calculation.
-/

open Polynomial

namespace CGraph

/-! ### Two identities the gallery does not have

Both constructions below are built in two halves — an outer cycle and a set of chords — and both
degenerate by having the second half contribute nothing.  `GP(1, k)` has a single outer vertex, so
the outer cycle is a loop that is not there and only the spoke survives; and an LCF graph whose
shifts are all zero joins every vertex to itself and to nobody else, so what is left is the
Hamiltonian cycle it was drawn on. -/

/-- The generalised Petersen graph on a single spoke is an edge: one outer vertex, one inner
vertex, and nothing for either of them to be adjacent to but each other. -/
@[toIsoGraph] theorem gp_one (k : ℕ) : gp 1 k = complete 2 := by
  rw [gp, ← ofEdges_cliqueEdges 2]
  refine ofEdges_congr _ _ _ ?_
  intro p q hpq
  simp [gpEdges, cliqueEdges, Nat.mod_one, List.mem_flatMap]
  omega

/-- A chord of length zero leads back where it started. -/
theorem lcfChord_of_forall_eq_zero {ss : List ℤ} {r : ℕ} (h : ∀ s ∈ ss, s = 0) {i : ℕ}
    (hi : i < ss.length * r) : lcfChord ss r i = i := by
  have hz : ss.getD (i % ss.length) 0 = 0 := by
    rcases lt_or_ge (i % ss.length) ss.length with hlt | hge
    · rw [List.getD_eq_getElem _ _ hlt]
      exact h _ (List.getElem_mem hlt)
    · exact List.getD_eq_default _ _ hge
  have hN : (0 : ℤ) < ((ss.length * r : ℕ) : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hi' : ((i : ℤ)) < ((ss.length * r : ℕ) : ℤ) := by exact_mod_cast hi
  unfold lcfChord
  rw [hz, add_zero, Int.emod_eq_of_lt (by positivity) hi', Int.add_emod_right,
    Int.emod_eq_of_lt (by positivity) hi', Int.toNat_natCast]

/-- An LCF graph all of whose shifts are zero is the cycle it is drawn on: every chord is a loop,
and loops are not edges. -/
@[toIsoGraph] theorem lcf_of_forall_eq_zero {ss : List ℤ} {r : ℕ} (h : ∀ s ∈ ss, s = 0) :
    lcf ss r = cycle (ss.length * r) := by
  refine eq_ofRel (lcf ss r) (fun i j ↦ (i.1 + 1) % (ss.length * r) == j.1) ?_
  intro x y hxy
  have hx : x.1 < ss.length * r := x.2
  have hy : y.1 < ss.length * r := y.2
  have hne : x.1 ≠ y.1 := fun hh ↦ hxy (Fin.ext hh)
  rw [Bool.eq_iff_iff, lcf_adj_val]
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨-, hmem⟩
    rcases hmem with hm | hm <;> rw [mem_lcfEdges_iff] at hm <;>
      obtain ⟨i, hi, hcase | hcase⟩ := hm
    · exact Or.inl (by rw [hcase.1, hcase.2])
    · rw [lcfChord_of_forall_eq_zero h hi] at hcase
      exact absurd (hcase.1.trans hcase.2.symm) hne
    · exact Or.inr (by rw [hcase.1, hcase.2])
    · rw [lcfChord_of_forall_eq_zero h hi] at hcase
      exact absurd (hcase.2.trans hcase.1.symm) hne
  · rintro (hc | hc)
    · exact ⟨hne, Or.inl (by rw [← hc]; exact mem_lcfEdges ss r hx)⟩
    · exact ⟨hne, Or.inr (by rw [← hc]; exact mem_lcfEdges ss r hy)⟩

end CGraph

namespace IsoGraph

/-! ### The tadpole with no tail

A tadpole is a cycle with a path glued to one of its vertices.  Glue on a path with no edges and
nothing has been glued on at all, so the whole spectral table of the cycle survives verbatim. -/

theorem charpoly_tadpole_zero {m : ℕ} (hm : 3 ≤ m) :
    (tadpole m 0).charpoly = ∏ k : Fin m, (X - C (2 * Real.cos (2 * Real.pi * k.1 / m))) := by
  rw [tadpole_zero]; exact charpoly_cycle hm

theorem spectrum_tadpole_zero {m : ℕ} (hm : 3 ≤ m) :
    (tadpole m 0).spectrum
      = Multiset.map (fun k : Fin m ↦ 2 * Real.cos (2 * Real.pi * k.1 / m)) Finset.univ.val := by
  rw [tadpole_zero]; exact spectrum_cycle hm

theorem energy_tadpole_zero {m : ℕ} (hm : 3 ≤ m) :
    (tadpole m 0).energy = ∑ k : Fin m, |2 * Real.cos (2 * Real.pi * k.1 / m)| := by
  rw [tadpole_zero]; exact energy_cycle hm

theorem lapCharpoly_tadpole_zero {m : ℕ} (hm : 3 ≤ m) :
    (tadpole m 0).lapCharpoly
      = ∏ k : Fin m, (X - C (2 - 2 * Real.cos (2 * Real.pi * k.1 / m))) := by
  rw [tadpole_zero]; exact lapCharpoly_cycle hm

theorem lapSpectrum_tadpole_zero {m : ℕ} (hm : 3 ≤ m) :
    (tadpole m 0).lapSpectrum
      = Multiset.map (fun k : Fin m ↦ 2 - 2 * Real.cos (2 * Real.pi * k.1 / m))
        Finset.univ.val := by
  rw [tadpole_zero]; exact lapSpectrum_cycle hm

theorem algConn_tadpole_zero (m : ℕ) :
    (tadpole (m + 3) 0).algConn = 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)) := by
  rw [tadpole_zero]; exact algConn_cycle m

theorem lapLambdaMax_tadpole_zero_even {m : ℕ} (hm : 2 ≤ m) :
    (tadpole (2 * m) 0).lapLambdaMax = 4 := by
  rw [tadpole_zero]; exact lapLambdaMax_cycle_even hm

theorem lapLambdaMax_tadpole_zero_odd (m : ℕ) :
    (tadpole (2 * m + 3) 0).lapLambdaMax
      = 2 + 2 * Real.cos (Real.pi / ((2 * m + 3 : ℕ) : ℝ)) := by
  rw [tadpole_zero]; exact lapLambdaMax_cycle_odd m

theorem indepCount_tadpole_zero (m k : ℕ) :
    (tadpole (m + 3) 0).indepCount (k + 1)
      = (m + 2 - k).choose (k + 1) + (m + 1 - k).choose k := by
  rw [tadpole_zero]; exact indepCount_cycle m k

/-! ### The cycle with no pendants

`cyclePendant m xs` hangs a path of length `xs[i]` off vertex `i` of an `m`-cycle.  A list of
zeroes hangs nothing off any vertex, however long the list is. -/

theorem charpoly_cyclePendant_replicate_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    (cyclePendant m (List.replicate j 0)).charpoly
      = ∏ k : Fin m, (X - C (2 * Real.cos (2 * Real.pi * k.1 / m))) := by
  rw [cyclePendant_replicate_zero]; exact charpoly_cycle hm

theorem spectrum_cyclePendant_replicate_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    (cyclePendant m (List.replicate j 0)).spectrum
      = Multiset.map (fun k : Fin m ↦ 2 * Real.cos (2 * Real.pi * k.1 / m)) Finset.univ.val := by
  rw [cyclePendant_replicate_zero]; exact spectrum_cycle hm

theorem energy_cyclePendant_replicate_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    (cyclePendant m (List.replicate j 0)).energy
      = ∑ k : Fin m, |2 * Real.cos (2 * Real.pi * k.1 / m)| := by
  rw [cyclePendant_replicate_zero]; exact energy_cycle hm

theorem lapCharpoly_cyclePendant_replicate_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    (cyclePendant m (List.replicate j 0)).lapCharpoly
      = ∏ k : Fin m, (X - C (2 - 2 * Real.cos (2 * Real.pi * k.1 / m))) := by
  rw [cyclePendant_replicate_zero]; exact lapCharpoly_cycle hm

theorem lapSpectrum_cyclePendant_replicate_zero {m : ℕ} (hm : 3 ≤ m) (j : ℕ) :
    (cyclePendant m (List.replicate j 0)).lapSpectrum
      = Multiset.map (fun k : Fin m ↦ 2 - 2 * Real.cos (2 * Real.pi * k.1 / m))
        Finset.univ.val := by
  rw [cyclePendant_replicate_zero]; exact lapSpectrum_cycle hm

theorem algConn_cyclePendant_replicate_zero (m j : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).algConn
      = 2 - 2 * Real.cos (2 * Real.pi / ((m : ℝ) + 3)) := by
  rw [cyclePendant_replicate_zero]; exact algConn_cycle m

theorem lapLambdaMax_cyclePendant_replicate_zero_even {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    (cyclePendant (2 * m) (List.replicate j 0)).lapLambdaMax = 4 := by
  rw [cyclePendant_replicate_zero]; exact lapLambdaMax_cycle_even hm

theorem lapLambdaMax_cyclePendant_replicate_zero_odd (m j : ℕ) :
    (cyclePendant (2 * m + 3) (List.replicate j 0)).lapLambdaMax
      = 2 + 2 * Real.cos (Real.pi / ((2 * m + 3 : ℕ) : ℝ)) := by
  rw [cyclePendant_replicate_zero]; exact lapLambdaMax_cycle_odd m

theorem indepCount_cyclePendant_replicate_zero (m j k : ℕ) :
    (cyclePendant (m + 3) (List.replicate j 0)).indepCount (k + 1)
      = (m + 2 - k).choose (k + 1) + (m + 1 - k).choose k := by
  rw [cyclePendant_replicate_zero]; exact indepCount_cycle m k

/-! ### The theta graph on two paths

A theta graph is a pair of vertices joined by several internally disjoint paths.  Joined by only
two of them there is no branching: the two paths close up into a single cycle whose length is the
sum of theirs, plus the two endpoints. -/

theorem charpoly_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).charpoly
      = ∏ k : Fin (2 + a + b),
        (X - C (2 * Real.cos (2 * Real.pi * k.1 / ((2 + a + b : ℕ) : ℝ)))) := by
  rw [thetaGraph_pair]; exact charpoly_cycle (by omega)

theorem spectrum_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).spectrum
      = Multiset.map
        (fun k : Fin (2 + a + b) ↦ 2 * Real.cos (2 * Real.pi * k.1 / ((2 + a + b : ℕ) : ℝ)))
        Finset.univ.val := by
  rw [thetaGraph_pair]; exact spectrum_cycle (by omega)

theorem energy_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).energy
      = ∑ k : Fin (2 + a + b), |2 * Real.cos (2 * Real.pi * k.1 / ((2 + a + b : ℕ) : ℝ))| := by
  rw [thetaGraph_pair]; exact energy_cycle (by omega)

theorem lapCharpoly_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).lapCharpoly
      = ∏ k : Fin (2 + a + b),
        (X - C (2 - 2 * Real.cos (2 * Real.pi * k.1 / ((2 + a + b : ℕ) : ℝ)))) := by
  rw [thetaGraph_pair]; exact lapCharpoly_cycle (by omega)

theorem lapSpectrum_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).lapSpectrum
      = Multiset.map
        (fun k : Fin (2 + a + b) ↦ 2 - 2 * Real.cos (2 * Real.pi * k.1 / ((2 + a + b : ℕ) : ℝ)))
        Finset.univ.val := by
  rw [thetaGraph_pair]; exact lapSpectrum_cycle (by omega)

theorem algConn_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).algConn
      = 2 - 2 * Real.cos (2 * Real.pi / ((2 + a + b : ℕ) : ℝ)) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = m + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hm, algConn_cycle]
  push_cast
  ring

theorem lapLambdaMax_thetaGraph_pair_even {a b m : ℕ} (h : 2 + a + b = 2 * m) (hm : 2 ≤ m) :
    (thetaGraph [a, b]).lapLambdaMax = 4 := by
  rw [thetaGraph_pair, h]; exact lapLambdaMax_cycle_even hm

theorem lapLambdaMax_thetaGraph_pair_odd {a b m : ℕ} (h : 2 + a + b = 2 * m + 3) :
    (thetaGraph [a, b]).lapLambdaMax
      = 2 + 2 * Real.cos (Real.pi / ((2 * m + 3 : ℕ) : ℝ)) := by
  rw [thetaGraph_pair, h]; exact lapLambdaMax_cycle_odd m

theorem indepCount_thetaGraph_pair {a b m : ℕ} (h : 2 + a + b = m + 3) (k : ℕ) :
    (thetaGraph [a, b]).indepCount (k + 1)
      = (m + 2 - k).choose (k + 1) + (m + 1 - k).choose k := by
  rw [thetaGraph_pair, h]; exact indepCount_cycle m k

/-! ### The circulant on a single shift

The circulant with connection set `[1]` joins every residue to its successor, which is exactly how
the cycle is built. -/

theorem indepCount_circulant_one (m k : ℕ) :
    (circulant (m + 3) [1]).indepCount (k + 1)
      = (m + 2 - k).choose (k + 1) + (m + 1 - k).choose k := by
  rw [circulant_one]; exact indepCount_cycle m k

/-! ### The spider with two legs

A spider is a tree with at most one branch vertex.  Two legs give it nothing to branch between,
and the body plus the two legs lie in a line. -/

theorem charpoly_spider_pair {a b n : ℕ} (h : 1 + a + b = n) :
    (spider [a, b]).charpoly
      = ∏ k : Fin n, (X - C (2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1)))) := by
  rw [spider_pair, h]; exact charpoly_path n

theorem spectrum_spider_pair {a b n : ℕ} (h : 1 + a + b = n) :
    (spider [a, b]).spectrum
      = Multiset.map (fun k : Fin n ↦ 2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1)))
        Finset.univ.val := by
  rw [spider_pair, h]; exact spectrum_path n

theorem energy_spider_pair {a b n : ℕ} (h : 1 + a + b = n) :
    (spider [a, b]).energy = ∑ k : Fin n, |2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1))| := by
  rw [spider_pair, h]; exact energy_path n

theorem lapCharpoly_spider_pair {a b n : ℕ} (h : 1 + a + b = n) :
    (spider [a, b]).lapCharpoly
      = ∏ k : Fin n, (X - C (2 - 2 * Real.cos (Real.pi * k.1 / n))) := by
  rw [spider_pair, h]; exact lapCharpoly_path n

theorem lapSpectrum_spider_pair {a b n : ℕ} (h : 1 + a + b = n) :
    (spider [a, b]).lapSpectrum
      = Multiset.map (fun k : Fin n ↦ 2 - 2 * Real.cos (Real.pi * k.1 / n)) Finset.univ.val := by
  rw [spider_pair, h]; exact lapSpectrum_path n

theorem algConn_spider_pair {a b n : ℕ} (h : 1 + a + b = n + 2) :
    (spider [a, b]).algConn = 2 - 2 * Real.cos (Real.pi / (n + 2)) := by
  rw [spider_pair, h]; exact algConn_path n

theorem lapLambdaMax_spider_pair (a b : ℕ) :
    (spider [a, b]).lapLambdaMax
      = 2 - 2 * Real.cos (Real.pi * ((a + b : ℕ) : ℝ) / ((a + b : ℕ) + 1)) := by
  rw [spider_pair, show 1 + a + b = (a + b) + 1 from by omega]
  exact lapLambdaMax_path (a + b)

theorem indepCount_spider_pair {a b n : ℕ} (h : 1 + a + b = n) (k : ℕ) :
    (spider [a, b]).indepCount k = (n + 1 - k).choose k := by
  rw [spider_pair, h]; exact indepCount_path n k

/-! ### The lollipop on a single-vertex head

The lollipop is a complete graph with a path attached to one of its vertices.  A complete graph on
one vertex is just that vertex, so what is left is the path with one more vertex on the end. -/

theorem charpoly_lollipop_one {j n : ℕ} (h : 1 + j = n) :
    (lollipop 1 j).charpoly
      = ∏ k : Fin n, (X - C (2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1)))) := by
  rw [lollipop_one, h]; exact charpoly_path n

theorem spectrum_lollipop_one {j n : ℕ} (h : 1 + j = n) :
    (lollipop 1 j).spectrum
      = Multiset.map (fun k : Fin n ↦ 2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1)))
        Finset.univ.val := by
  rw [lollipop_one, h]; exact spectrum_path n

theorem energy_lollipop_one {j n : ℕ} (h : 1 + j = n) :
    (lollipop 1 j).energy = ∑ k : Fin n, |2 * Real.cos (Real.pi * (k.1 + 1) / (n + 1))| := by
  rw [lollipop_one, h]; exact energy_path n

theorem lapCharpoly_lollipop_one {j n : ℕ} (h : 1 + j = n) :
    (lollipop 1 j).lapCharpoly
      = ∏ k : Fin n, (X - C (2 - 2 * Real.cos (Real.pi * k.1 / n))) := by
  rw [lollipop_one, h]; exact lapCharpoly_path n

theorem lapSpectrum_lollipop_one {j n : ℕ} (h : 1 + j = n) :
    (lollipop 1 j).lapSpectrum
      = Multiset.map (fun k : Fin n ↦ 2 - 2 * Real.cos (Real.pi * k.1 / n)) Finset.univ.val := by
  rw [lollipop_one, h]; exact lapSpectrum_path n

theorem algConn_lollipop_one (j : ℕ) :
    (lollipop 1 (j + 1)).algConn = 2 - 2 * Real.cos (Real.pi / (j + 2)) := by
  rw [lollipop_one, show 1 + (j + 1) = j + 2 from by omega]; exact algConn_path j

theorem lapLambdaMax_lollipop_one (j : ℕ) :
    (lollipop 1 j).lapLambdaMax = 2 - 2 * Real.cos (Real.pi * j / (j + 1)) := by
  rw [lollipop_one, show 1 + j = j + 1 from by omega]; exact lapLambdaMax_path j

theorem indepCount_lollipop_one {j n : ℕ} (h : 1 + j = n) (k : ℕ) :
    (lollipop 1 j).indepCount k = (n + 1 - k).choose k := by
  rw [lollipop_one, h]; exact indepCount_path n k

theorem cliqueCount_lollipop_zero (m k : ℕ) : (lollipop m 0).cliqueCount k = m.choose k := by
  rw [lollipop_zero]; exact cliqueCount_complete m k

@[simp] theorem isSelfComplementary_lollipop_one_three : IsSelfComplementary (lollipop 1 3) := by
  rw [lollipop_one, show 1 + 3 = 4 from rfl]; exact isSelfComplementary_path_four

/-! ### The double star with all the leaves on one side

The two centres of a double star keep the edge between them whatever else happens, so stripping
the leaves off one side leaves the other centre with its own leaves and one more: a star. -/

theorem charpoly_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).charpoly = (X ^ 2 - C ((m : ℝ) + 1)) * X ^ m := by
  rw [doubleStar_right_zero]; exact charpoly_star m

theorem spectrum_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).spectrum
      = Real.sqrt ((m : ℝ) + 1) ::ₘ -Real.sqrt ((m : ℝ) + 1) ::ₘ Multiset.replicate m 0 := by
  rw [doubleStar_right_zero]; exact spectrum_star m

theorem energy_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).energy = 2 * Real.sqrt ((m : ℝ) + 1) := by
  rw [doubleStar_right_zero]; exact energy_star m

theorem lapCharpoly_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).lapCharpoly = X * (X - C ((m : ℝ) + 2)) * (X - 1) ^ m := by
  rw [doubleStar_right_zero]; exact lapCharpoly_star m

theorem lapSpectrum_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).lapSpectrum = 0 ::ₘ ((m : ℝ) + 2) ::ₘ Multiset.replicate m 1 := by
  rw [doubleStar_right_zero]; exact lapSpectrum_star m

theorem algConn_doubleStar_right_zero (m : ℕ) : (doubleStar (m + 1) 0).algConn = 1 := by
  rw [doubleStar_right_zero, show m + 1 + 1 = m + 2 from rfl]; exact algConn_star m

theorem lapLambdaMax_doubleStar_right_zero (m : ℕ) :
    (doubleStar m 0).lapLambdaMax = (m : ℝ) + 2 := by
  rw [doubleStar_right_zero]; exact lapLambdaMax_star m

theorem autCount_doubleStar_right_zero (m : ℕ) :
    (doubleStar (m + 1) 0).autCount = (m + 2).factorial := by
  rw [doubleStar_right_zero, show m + 1 + 1 = m + 2 from rfl]; exact autCount_star m

theorem indepCount_doubleStar_right_zero (m k : ℕ) :
    (doubleStar m 0).indepCount (k + 2) = (m + 1).choose (k + 2) := by
  rw [doubleStar_right_zero]; exact indepCount_star (m + 1) k

/-! ### The Kneser and Johnson graphs that are complete or edgeless

Two singletons of an `n`-set are disjoint unless they are equal, so `kneser n 1` is the complete
graph; and both `johnson n 0` and `johnson n n` have a single vertex to their name. -/

theorem charpoly_kneser_one (n : ℕ) :
    (kneser (n + 1) 1).charpoly = (X - C (n : ℝ)) * (X + 1) ^ n := by
  rw [kneser_one]; exact charpoly_complete n

theorem lapCharpoly_kneser_one (n : ℕ) :
    (kneser (n + 1) 1).lapCharpoly = X * (X - C ((n : ℝ) + 1)) ^ n := by
  rw [kneser_one]; exact lapCharpoly_complete n

theorem charpoly_johnson_zero (n : ℕ) : (johnson n 0).charpoly = X ^ 1 := by
  rw [johnson_zero]; exact charpoly_empty 1

theorem lapCharpoly_johnson_zero (n : ℕ) : (johnson n 0).lapCharpoly = X ^ 1 := by
  rw [johnson_zero]; exact lapCharpoly_empty 1

/-! ### The fans that are complete

The fan joins one vertex to a path.  A path on two or fewer vertices is already a clique, so the
join is complete — for longer paths the fan is genuinely its own graph. -/

theorem charpoly_fan_two : (fan 2).charpoly = (X - C (2 : ℝ)) * (X + 1) ^ 2 := by
  rw [fan_two]; exact charpoly_complete 2

theorem spectrum_fan_two : (fan 2).spectrum = (2 : ℝ) ::ₘ Multiset.replicate 2 (-1) := by
  rw [fan_two]; exact spectrum_complete 2

theorem energy_fan_two : (fan 2).energy = 4 := by
  rw [fan_two]
  have h := energy_complete 2
  norm_num at h
  exact h

/-! ### The cube

The three-dimensional cube has eigenvalues `3 - 2j` with multiplicity `C(3, j)`, that is
`3, 1, 1, 1, -1, -1, -1, -3`, and Laplacian eigenvalues `2j` with the same multiplicities.  Writing
the four factors out once here keeps the next two sections to a single line apiece. -/

theorem charpoly_hypercube_three :
    (hypercube 3).charpoly = (X - 3) * (X - 1) ^ 3 * (X + 1) ^ 3 * (X + 3) := by
  rw [charpoly_hypercube]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num [map_ofNat]

theorem spectrum_hypercube_three :
    (hypercube 3).spectrum = {3, 1, 1, 1, -1, -1, -1, -3} := by
  rw [spectrum_hypercube]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Multiset.replicate_succ,
    Multiset.replicate_zero, Multiset.cons_zero, Multiset.cons_add, Multiset.singleton_add,
    Multiset.insert_eq_cons, add_zero, Nat.choose]
  norm_num only

theorem energy_hypercube_three : (hypercube 3).energy = 12 := by
  rw [energy_hypercube]
  norm_num [Finset.sum_range_succ]

theorem lapCharpoly_hypercube_three :
    (hypercube 3).lapCharpoly = X * (X - 2) ^ 3 * (X - 4) ^ 3 * (X - 6) := by
  rw [lapCharpoly_hypercube]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num [map_ofNat]

theorem lapSpectrum_hypercube_three :
    (hypercube 3).lapSpectrum = {0, 2, 2, 2, 4, 4, 4, 6} := by
  rw [lapSpectrum_hypercube]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Multiset.replicate_succ,
    Multiset.replicate_zero, Multiset.cons_zero, Multiset.cons_add, Multiset.singleton_add,
    Multiset.insert_eq_cons, add_zero, Nat.choose]
  norm_num only

/-! ### The generalised Petersen graphs with a description

Nothing in the definition of `gp n k` pins down an eigenvalue in general — the outer cycle, the
inner circulant and the spokes interleave differently for every step size.  At two sets of
parameters the graph has an independent description, and reading it backwards carries the spectrum
across: `GP(4, 1)` is the cube and `GP(5, 2)` is the Petersen graph. -/

theorem charpoly_gp_four_one :
    (gp 4 1).charpoly = (X - 3) * (X - 1) ^ 3 * (X + 1) ^ 3 * (X + 3) := by
  rw [gp_four_one_iso_hypercube]; exact charpoly_hypercube_three

theorem spectrum_gp_four_one : (gp 4 1).spectrum = {3, 1, 1, 1, -1, -1, -1, -3} := by
  rw [gp_four_one_iso_hypercube]; exact spectrum_hypercube_three

theorem energy_gp_four_one : (gp 4 1).energy = 12 := by
  rw [gp_four_one_iso_hypercube]; exact energy_hypercube_three

theorem lapCharpoly_gp_four_one :
    (gp 4 1).lapCharpoly = X * (X - 2) ^ 3 * (X - 4) ^ 3 * (X - 6) := by
  rw [gp_four_one_iso_hypercube]; exact lapCharpoly_hypercube_three

theorem lapSpectrum_gp_four_one : (gp 4 1).lapSpectrum = {0, 2, 2, 2, 4, 4, 4, 6} := by
  rw [gp_four_one_iso_hypercube]; exact lapSpectrum_hypercube_three

theorem algConn_gp_four_one : (gp 4 1).algConn = 2 := by
  rw [gp_four_one_iso_hypercube]; exact algConn_hypercube (by norm_num)

theorem lapLambdaMax_gp_four_one : (gp 4 1).lapLambdaMax = 6 := by
  rw [gp_four_one_iso_hypercube, lapLambdaMax_hypercube]; norm_num

@[simp] theorem autCount_gp_four_one : (gp 4 1).autCount = 48 := by
  rw [gp_four_one_iso_hypercube, autCount_hypercube]; norm_num [Nat.factorial]

@[simp] theorem isVertexTransitive_gp_four_one : IsVertexTransitive (gp 4 1) := by
  rw [gp_four_one_iso_hypercube]; exact isVertexTransitive_hypercube 3

@[simp] theorem isArcTransitive_gp_four_one : IsArcTransitive (gp 4 1) := by
  rw [gp_four_one_iso_hypercube]; exact isArcTransitive_hypercube 3

@[simp] theorem cliqueCount_gp_four_one : (gp 4 1).cliqueCount 3 = 0 := by
  rw [gp_four_one_iso_hypercube]; exact cliqueCount_hypercube 3

theorem isSRGWith_gp_five_two : IsSRGWith (gp 5 2) 10 3 0 1 := by
  rw [gp_five_two_iso_petersen]; exact isSRGWith_petersen

/-! ### The generalised Petersen graph on one spoke

`Connectivities.lean` carries `κ` and `λ` across every identification that is available where it
sits in the import order; the two proved at the top of this file are not, so their two graphs are
settled here instead.  `GP(1, k)` is an edge, and an edge is cut by removing either half of it. -/

theorem vertexConn_gp_one (k : ℕ) : (gp 1 k).vertexConn = 1 := by
  rw [gp_one, vertexConn_complete]

theorem edgeConn_gp_one (k : ℕ) : (gp 1 k).edgeConn = 1 := by
  rw [gp_one, edgeConn_complete]

/-! ### The LCF cube

`[3, -3]⁴` is the cube in LCF notation: eight vertices on a Hamiltonian cycle, each joined to the
vertex three steps away.  The same eight eigenvalues, reached from the other direction. -/

theorem charpoly_lcf_cube :
    (lcf [3, -3] 4).charpoly = (X - 3) * (X - 1) ^ 3 * (X + 1) ^ 3 * (X + 3) := by
  rw [hypercube_three_lcf]; exact charpoly_hypercube_three

theorem spectrum_lcf_cube : (lcf [3, -3] 4).spectrum = {3, 1, 1, 1, -1, -1, -1, -3} := by
  rw [hypercube_three_lcf]; exact spectrum_hypercube_three

theorem energy_lcf_cube : (lcf [3, -3] 4).energy = 12 := by
  rw [hypercube_three_lcf]; exact energy_hypercube_three

theorem lapCharpoly_lcf_cube :
    (lcf [3, -3] 4).lapCharpoly = X * (X - 2) ^ 3 * (X - 4) ^ 3 * (X - 6) := by
  rw [hypercube_three_lcf]; exact lapCharpoly_hypercube_three

theorem lapSpectrum_lcf_cube : (lcf [3, -3] 4).lapSpectrum = {0, 2, 2, 2, 4, 4, 4, 6} := by
  rw [hypercube_three_lcf]; exact lapSpectrum_hypercube_three

theorem algConn_lcf_cube : (lcf [3, -3] 4).algConn = 2 := by
  rw [hypercube_three_lcf]; exact algConn_hypercube (by norm_num)

theorem lapLambdaMax_lcf_cube : (lcf [3, -3] 4).lapLambdaMax = 6 := by
  rw [hypercube_three_lcf, lapLambdaMax_hypercube]; norm_num

@[simp] theorem autCount_lcf_cube : (lcf [3, -3] 4).autCount = 48 := by
  rw [hypercube_three_lcf, autCount_hypercube]; norm_num [Nat.factorial]

@[simp] theorem isVertexTransitive_lcf_cube : IsVertexTransitive (lcf [3, -3] 4) := by
  rw [hypercube_three_lcf]; exact isVertexTransitive_hypercube 3

@[simp] theorem isArcTransitive_lcf_cube : IsArcTransitive (lcf [3, -3] 4) := by
  rw [hypercube_three_lcf]; exact isArcTransitive_hypercube 3

@[simp] theorem cliqueCount_lcf_cube : (lcf [3, -3] 4).cliqueCount 3 = 0 := by
  rw [hypercube_three_lcf]; exact cliqueCount_hypercube 3

@[simp] theorem isArcTransitive_prism_four : IsArcTransitive (prism 4) := by
  rw [← hypercube_three]; exact isArcTransitive_hypercube 3

@[simp] theorem isArcTransitive_foldedCube_two : IsArcTransitive (foldedCube 2) := by
  rw [foldedCube_two]; exact isArcTransitive_complete 4

/-! ### The LCF graph with no chords

An LCF description whose shifts are all zero describes nothing beyond the Hamiltonian cycle it is
drawn on, and the cycles are a family this library already knows in full.  Which cycle it is
depends on the length of the description, so the statements below carry `|ss| · r` along as a
hypothesis rather than case on it. -/

theorem isDS_lcf_of_forall_eq_zero {ss : List ℤ} {r m : ℕ} (h : ∀ s ∈ ss, s = 0)
    (hlen : ss.length * r = m + 3) : IsDS (lcf ss r) := by
  rw [lcf_of_forall_eq_zero h, hlen]; exact isDS_cycle m

theorem isSRGWith_lcf_zero_five : IsSRGWith (lcf [0] 5) 5 2 0 1 := by
  rw [lcf_of_forall_eq_zero (by simp), show (([0] : List ℤ).length * 5) = 5 from rfl]
  exact cycle_five_srg

theorem indepCount_lcf_of_forall_eq_zero {ss : List ℤ} {r m k : ℕ} (h : ∀ s ∈ ss, s = 0)
    (hlen : ss.length * r = m + 3) :
    (lcf ss r).indepCount (k + 1) = (m + 2 - k).choose (k + 1) + (m + 1 - k).choose k := by
  rw [lcf_of_forall_eq_zero h, hlen]; exact indepCount_cycle m k

theorem vertexConn_lcf_of_forall_eq_zero {ss : List ℤ} {r m : ℕ} (h : ∀ s ∈ ss, s = 0)
    (hlen : ss.length * r = m + 3) : (lcf ss r).vertexConn = 2 := by
  rw [lcf_of_forall_eq_zero h, hlen]; exact vertexConn_cycle m

theorem edgeConn_lcf_of_forall_eq_zero {ss : List ℤ} {r m : ℕ} (h : ∀ s ∈ ss, s = 0)
    (hlen : ss.length * r = m + 3) : (lcf ss r).edgeConn = 2 := by
  rw [lcf_of_forall_eq_zero h, hlen]; exact edgeConn_cycle m

/-! ### The Mycielskian of an edgeless graph

The Mycielskian doubles a graph and adds an apex, joining each shadow vertex to the neighbours of
its twin.  Over an edgeless graph there are no neighbours to join it to, so the shadows stay
isolated and only the apex has any edges: a star and an independent set, side by side.  That
decomposition settles the counting invariants as readily as the spectral ones. -/

theorem charpoly_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).charpoly = (X ^ 2 - C ((n : ℝ) + 1)) * X ^ (2 * n + 1) := by
  rw [mycielskian_empty, charpoly_disjUnion, charpoly_star, charpoly_empty]
  ring

theorem spectrum_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).spectrum
      = Real.sqrt ((n : ℝ) + 1) ::ₘ -Real.sqrt ((n : ℝ) + 1) ::ₘ Multiset.replicate (2 * n + 1) 0
      := by
  rw [mycielskian_empty, spectrum_disjUnion, spectrum_star, spectrum_empty,
    show 2 * n + 1 = n + (n + 1) from by ring, Multiset.replicate_add n (n + 1) (0 : ℝ),
    Multiset.cons_add, Multiset.cons_add]

theorem energy_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).energy = 2 * Real.sqrt ((n : ℝ) + 1) := by
  rw [mycielskian_empty, energy_disjUnion, energy_star, energy_empty, add_zero]

theorem lapCharpoly_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).lapCharpoly
      = X ^ (n + 2) * (X - C ((n : ℝ) + 2)) * (X - 1) ^ n := by
  rw [mycielskian_empty, lapCharpoly_disjUnion, lapCharpoly_star, lapCharpoly_empty]
  ring

theorem lapSpectrum_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).lapSpectrum
      = 0 ::ₘ ((n : ℝ) + 2) ::ₘ (Multiset.replicate n 1 + Multiset.replicate (n + 1) 0) := by
  rw [mycielskian_empty, lapSpectrum_disjUnion, lapSpectrum_star, lapSpectrum_empty,
    Multiset.cons_add, Multiset.cons_add]

theorem algConn_mycielskian_empty (n : ℕ) : (mycielskian (empty (n + 1))).algConn = 0 := by
  rw [mycielskian_empty]
  exact algConn_disjUnion _ _ (by simp) (by simp)

theorem lapLambdaMax_mycielskian_empty (n : ℕ) :
    (mycielskian (empty (n + 1))).lapLambdaMax = (n : ℝ) + 2 := by
  rw [mycielskian_empty, lapLambdaMax_disjUnion _ _ (by simp) (by simp), lapLambdaMax_star,
    lapLambdaMax_empty]
  exact max_eq_left (by positivity)

theorem coverNum_mycielskian_empty (n : ℕ) : (mycielskian (empty n)).coverNum = min 1 n := by
  rw [mycielskian_empty, coverNum_disjUnion, coverNum_star, coverNum_empty, Nat.add_zero]

theorem indepNum_mycielskian_empty (n : ℕ) : (mycielskian (empty n)).indepNum = max 1 n + n := by
  rw [mycielskian_empty, indepNum_disjUnion, indepNum_star, indepNum_empty]

theorem edgeChromNum_mycielskian_empty (n : ℕ) : (mycielskian (empty n)).edgeChromNum = n := by
  rw [mycielskian_empty, edgeChromNum_disjUnion, edgeChromNum_star, edgeChromNum_empty,
    Nat.max_zero]

theorem diameter_mycielskian_empty (n : ℕ) : (mycielskian (empty (n + 1))).diameter = 0 := by
  rw [mycielskian_empty]
  exact diameter_disjUnion (by simp) (by simp)

/-! ### Spectra determined by an identity

Being determined by its spectrum is a property of the graph, not of the description it arrives
under.  Every family member below is a complete or an edgeless graph in disguise — or, in the case
of the wheel on three spokes, a join of two complete graphs — and each of those is known to be
determined by its spectrum. -/

theorem isDS_path_two : IsDS (path 2) := by rw [path_two]; exact isDS_complete 2

theorem isDS_path_one : IsDS (path 1) := by rw [path_one]; exact isDS_empty 1

theorem isDS_path_zero : IsDS (path 0) := by rw [path_zero]; exact isDS_empty 0

theorem isDS_book_zero : IsDS (book 0) := by rw [book_zero]; exact isDS_complete 2

theorem isDS_book_one : IsDS (book 1) := by rw [book_one]; exact isDS_complete 3

theorem isDS_fan_one : IsDS (fan 1) := by rw [fan_one]; exact isDS_complete 2

theorem isDS_fan_two : IsDS (fan 2) := by rw [fan_two]; exact isDS_complete 3

theorem isDS_friendship_one : IsDS (friendship 1) := by
  rw [friendship_one]; exact isDS_complete 3

theorem isDS_lollipop_zero (m : ℕ) : IsDS (lollipop m 0) := by
  rw [lollipop_zero]; exact isDS_complete m

theorem isDS_spider_nil : IsDS (spider []) := by rw [spider_nil]; exact isDS_empty 1

theorem isDS_kneser_one (n : ℕ) : IsDS (kneser n 1) := by
  rw [kneser_one]; exact isDS_complete n

theorem isDS_gp_one (k : ℕ) : IsDS (gp 1 k) := by rw [gp_one]; exact isDS_complete 2

theorem isDS_johnson_zero (n : ℕ) : IsDS (johnson n 0) := by
  rw [johnson_zero]; exact isDS_empty 1

theorem isDS_johnson_self (n : ℕ) : IsDS (johnson n n) := by
  rw [johnson_self]; exact isDS_empty 1

theorem isDS_doubleStar_zero_zero : IsDS (doubleStar 0 0) := by
  rw [doubleStar_right_zero, star_one]; exact isDS_complete 2

theorem isDS_foldedCube_zero : IsDS (foldedCube 0) := by
  rw [foldedCube_zero]; exact isDS_empty 1

theorem isDS_foldedCube_one : IsDS (foldedCube 1) := by
  rw [foldedCube_one]; exact isDS_complete 2

theorem isDS_foldedCube_two : IsDS (foldedCube 2) := by
  rw [foldedCube_two]; exact isDS_complete 4

theorem isDS_wheel_three : IsDS (wheel 3) := by
  rw [wheel_eq_join, cycle_three]; exact isDS_join_complete 1 3

theorem isDS_mycielskian_empty_zero : IsDS (mycielskian (empty 0)) := by
  rw [mycielskian_empty_zero]; exact isDS_empty 1

/-! ### The line graphs with a second description

Two of the line graphs the gallery can be asked for are graphs it already had.  The edges of a
cycle meet in a cycle of the same length, so the operator fixes every cycle from the triangle up;
and the edges of a star all meet each other, so the line graph of a star is complete. -/

theorem cliqueCoverNum_lineGraph_cycle (n : ℕ) :
    ((cycle (n + 4)).lineGraph).cliqueCoverNum = (n + 5) / 2 := by
  rw [lineGraph_cycle (n + 1)]; exact cliqueCoverNum_cycle n

theorem diameter_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).diameter = (n + 3) / 2 := by
  rw [lineGraph_cycle]; exact diameter_cycle (n + 2)

theorem radius_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).radius = (n + 3) / 2 := by
  rw [lineGraph_cycle]; exact radius_cycle (n + 2)

theorem matchNum_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).matchNum = (n + 3) / 2 := by
  rw [lineGraph_cycle]; exact matchNum_cycle n

theorem domNum_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).domNum = (n + 5) / 3 := by
  rw [lineGraph_cycle]; exact domNum_cycle n

theorem edgeChromNum_lineGraph_star (n : ℕ) :
    ((star (n + 2)).lineGraph).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  rw [lineGraph_star]; exact edgeChromNum_complete n

/-! ### The products that are edgeless

A strong or a lexicographic product has an edge only where one of its factors does, and a tensor
product only where both of them do at once.  So the strong and the lexicographic product of two
edgeless graphs are edgeless, and a tensor product is edgeless as soon as either side is. -/

theorem cliqueCoverNum_strongProduct_empty (m n : ℕ) :
    (empty m ⊠g empty n).cliqueCoverNum = m * n := by
  rw [strongProduct_empty]; exact cliqueCoverNum_empty _

theorem edgeChromNum_strongProduct_empty (m n : ℕ) : (empty m ⊠g empty n).edgeChromNum = 0 := by
  rw [strongProduct_empty]; exact edgeChromNum_empty _

theorem cliqueCoverNum_tensorProduct_empty (G : IsoGraph) (n : ℕ) :
    (G ⊗g empty n).cliqueCoverNum = G.V * n := by
  rw [tensorProduct_empty]; exact cliqueCoverNum_empty _

theorem coverNum_tensorProduct_empty (G : IsoGraph) (n : ℕ) : (G ⊗g empty n).coverNum = 0 := by
  rw [tensorProduct_empty]; exact coverNum_empty _

theorem edgeChromNum_tensorProduct_empty (G : IsoGraph) (n : ℕ) :
    (G ⊗g empty n).edgeChromNum = 0 := by
  rw [tensorProduct_empty]; exact edgeChromNum_empty _

theorem indepNum_tensorProduct_empty (G : IsoGraph) (n : ℕ) :
    (G ⊗g empty n).indepNum = G.V * n := by
  rw [tensorProduct_empty]; exact indepNum_empty _

theorem diameter_lexProduct_empty (m n : ℕ) : (empty m ·g empty n).diameter = 0 := by
  rw [lexProduct_empty]; exact diameter_empty _

theorem edgeChromNum_lexProduct_empty (m n : ℕ) : (empty m ·g empty n).edgeChromNum = 0 := by
  rw [lexProduct_empty]; exact edgeChromNum_empty _

/-! ### The Cartesian products with another name

Two Cartesian products are stocked under a name of their own: a product of two complete graphs is a
rook's graph, and a product of a hypercube with an edge is the next hypercube up. -/

theorem domNum_cartesianProduct_complete (m n : ℕ) :
    (complete (m + 1) □g complete (n + 1)).domNum = min (m + 1) (n + 1) :=
  domNum_rook m n

theorem cliqueCoverNum_cartesianProduct_hypercube (n : ℕ) :
    (hypercube n □g complete 2).cliqueCoverNum = 2 ^ n := by
  rw [← hypercube_succ]; exact cliqueCoverNum_hypercube n

/-! ### The complement of an edgeless graph

Complementation swaps the two extremes of the gallery, so every value known for a complete graph is
a value known for the complement operator. -/

theorem domNum_compl_empty (n : ℕ) : ((empty (n + 1))ᶜ).domNum = 1 := by
  rw [compl_empty]; exact domNum_complete n

theorem radius_compl_empty (n : ℕ) : ((empty (n + 2))ᶜ).radius = 1 := by
  rw [compl_empty]; exact radius_complete n

theorem edgeChromNum_compl_empty (n : ℕ) :
    ((empty (n + 2))ᶜ).edgeChromNum = if n % 2 = 0 then n + 1 else n + 2 := by
  rw [compl_empty]; exact edgeChromNum_complete n

/-! ### More invariants determined by an identity

The last of the identities to read from left to right.  The circulant this library calls `paley 9`
is the complete tripartite graph `K₃,₃,₃`, whose colouring invariants can be read off its parts; the
book on one page, the fan on two and the folded cube on one dimension are all complete graphs; the
Turán graph and the complete multipartite graph on a single part are both edgeless; and `T(4)` is
the octahedron, which has a perfect matching. -/

theorem chromNum_paley_nine : (paley 9).chromNum = 3 := by
  rw [paley_nine, chromNum_completeMultipartite]
  rfl

theorem cliqueNum_paley_nine : (paley 9).cliqueNum = 3 := by
  rw [paley_nine, cliqueNum_completeMultipartite]
  rfl

theorem indepNum_paley_nine : (paley 9).indepNum = 3 := by
  rw [paley_nine, indepNum_completeMultipartite]
  rfl

theorem coverNum_paley_nine : (paley 9).coverNum = 6 := by
  rw [paley_nine, coverNum_completeMultipartite]
  rfl

theorem cliqueCoverNum_paley_nine : (paley 9).cliqueCoverNum = 3 := by
  rw [paley_nine, cliqueCoverNum_completeMultipartite]
  rfl

theorem edgeChromNum_book_one : (book 1).edgeChromNum = 3 := by
  rw [book_one]; exact edgeChromNum_complete 1

theorem edgeChromNum_fan_two : (fan 2).edgeChromNum = 3 := by
  rw [fan_two]; exact edgeChromNum_complete 1

theorem edgeChromNum_foldedCube_one : (foldedCube 1).edgeChromNum = 1 := by
  rw [foldedCube_one]; exact edgeChromNum_complete 0

theorem edgeChromNum_turan_one (n : ℕ) : (turan n 1).edgeChromNum = 0 := by
  rw [turan_one]; exact edgeChromNum_empty n

theorem edgeChromNum_completeMultipartite_singleton (n : ℕ) :
    (completeMultipartite [n]).edgeChromNum = 0 := by
  rw [completeMultipartite_singleton]; exact edgeChromNum_empty n

theorem matchNum_triangular_four : (triangular 4).matchNum = 3 := by
  rw [triangular_four]; exact matchNum_cocktailParty 1

end IsoGraph
