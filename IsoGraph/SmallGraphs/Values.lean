import IsoGraph.SmallGraphs.Colouring
import IsoGraph.ForMathlib.Hamming

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Values that need more than one of the topical files

Values whose proofs need more than one of the topical files above — the strongly regular parameters,
the separations between the families, and the concrete tables the later files consume.
-/

namespace CGraph

section
open Fintype
variable {m n : ℕ}

/-! ### Triangular graphs -/

/-- `johnson n 2` — the triangular graph `T(n)` — is the complement of `kneser n 2`: two distinct
pairs either meet in a point or are disjoint, and never both. -/
@[toIsoGraph johnson_two_eq_compl_kneser]
def johnsonTwoIso (n : ℕ) : johnson n 2 ≃cg (kneser n 2)ᶜ :=
  ⟨Equiv.refl {s : Finset (Fin n) // s.card = 2}, by
    intro s t
    show ((kneser n 2)ᶜ).Adj s t = true ↔ (johnson n 2).Adj s t = true
    simp only [compl_adj, kneser_adj, johnson_adj, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, not_not, beq_iff_eq,
      ne_eq]
    constructor
    · rintro ⟨hne, hd⟩
      exact ⟨hne, card_inter_eq_one_of_ne s t hne (hd.resolve_left (by simpa using hne))⟩
    · rintro ⟨hne, hc⟩
      refine ⟨hne, Or.inr fun he ↦ ?_⟩
      rw [he, Finset.card_empty] at hc
      exact absurd hc (by norm_num)⟩

/-- **Triangular graphs are strongly regular**: `T(n) = J(n, 2)` has parameters
`(C(n,2), 2(n-2), n-2, 4)`.

The bound `4 ≤ n` is only needed for `μ`, which is vacuous below it: `T(3) = K₃` and
`T(n)` is empty for `n < 3`, so those graphs have no non-adjacent pair to constrain. -/
@[toIsoGraph]
theorem isSRGWith_johnson_two (n : ℕ) (hn : 4 ≤ n) :
    (johnson n 2).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 2 = m + 2 from rfl]
  have h := isSRGWith_compl _ (isSRGWith_kneser_two (m + 4))
  rw [show m + 4 - 2 = m + 2 from rfl, show m + 4 - 3 = m + 1 from rfl,
    show m + 4 - 4 = m from rfl] at h
  have h1 : (m + 1).choose 2 = m.choose 2 + m := choose_two_succ m
  have h2 : (m + 2).choose 2 = (m + 1).choose 2 + (m + 1) := choose_two_succ (m + 1)
  have h3 : (m + 3).choose 2 = (m + 2).choose 2 + (m + 2) := choose_two_succ (m + 2)
  have h4 : (m + 4).choose 2 = (m + 3).choose 2 + (m + 3) := choose_two_succ (m + 3)
  rw [show (m + 4).choose 2 - (m + 2).choose 2 - 1 = 2 * (m + 2) from by omega,
    show (m + 4).choose 2 - (2 * (m + 2).choose 2 - (m + 1).choose 2) - 2 = m + 2 from by omega,
    show (m + 4).choose 2 - (2 * (m + 2).choose 2 - m.choose 2) = 4 from by omega] at h
  exact SimpleGraph.Iso.isSRGWith_of_iso (CGraph.Iso.toSimpleIso (johnsonTwoIso (m + 4)).symm) h

@[inherit_doc isSRGWith_johnson_two]
theorem isSRGWith_triangular (n : ℕ) (hn : 4 ≤ n) :
    (triangular n).IsSRGWith (n.choose 2) (2 * (n - 2)) (n - 2) 4 :=
  isSRGWith_johnson_two n hn

/-- A triangle of the triangular graph `T(n)` is either three pairs through one common point or
the three pairs on three points. -/
@[toIsoGraph]
theorem cliqueCount_johnson_two (n : ℕ) (hn : 4 ≤ n) :
    (johnson n 2).cliqueCount 3 = n * (n - 1).choose 3 + n.choose 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := (isSRGWith_johnson_two (m + 4) hn).six_mul_cliqueCount_three
  rw [show m + 4 - 2 = m + 2 from rfl] at h
  have hC := two_mul_choose_two (m + 4)
  rw [show m + 4 - 1 = m + 3 from rfl] at hC
  have hA := six_mul_choose_three (m + 3)
  rw [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl] at hA
  have hB := six_mul_choose_three (m + 4)
  rw [show m + 4 - 1 = m + 3 from rfl, show m + 4 - 2 = m + 2 from rfl] at hB
  rw [show m + 4 - 1 = m + 3 from rfl]
  refine (Nat.eq_of_mul_eq_mul_left (show 0 < 6 by norm_num) ?_).symm
  calc 6 * ((m + 4) * (m + 3).choose 3 + (m + 4).choose 3)
      = (m + 4) * (6 * (m + 3).choose 3) + 6 * (m + 4).choose 3 := by ring
    _ = (m + 4) * ((m + 3) * (m + 2) * (m + 1)) + (m + 4) * (m + 3) * (m + 2) := by rw [hA, hB]
    _ = 2 * (m + 4).choose 2 * (m + 2) * (m + 2) := by rw [hC]; ring
    _ = (m + 4).choose 2 * (2 * (m + 2)) * (m + 2) := by ring
    _ = 6 * (johnson (m + 4) 2).cliqueCount 3 := h.symm

@[inherit_doc cliqueCount_johnson_two, toIsoGraph]
theorem cliqueCount_triangular (n : ℕ) (hn : 4 ≤ n) :
    (triangular n).cliqueCount 3 = n * (n - 1).choose 3 + n.choose 3 :=
  cliqueCount_johnson_two n hn

/-- Reading `johnsonTwoIso` the other way: an independent triple of `T(n)` is a triangle of the
Kneser graph, that is a perfect matching on six of the `n` points. -/
@[toIsoGraph]
theorem indepCount_johnson_two (n : ℕ) : (johnson n 2).indepCount 3 = 15 * n.choose 6 := by
  rw [indepCount_eq_of_iso (johnsonTwoIso n), indepCount_compl, cliqueCount_kneser_two]

@[inherit_doc indepCount_johnson_two, toIsoGraph]
theorem indepCount_triangular (n : ℕ) : (triangular n).indepCount 3 = 15 * n.choose 6 :=
  indepCount_johnson_two n

/-- Dually, an independent triple of the Kneser graph is a triangle of `T(n)`. -/
@[toIsoGraph]
theorem indepCount_kneser_two (n : ℕ) (hn : 4 ≤ n) :
    (kneser n 2).indepCount 3 = n * (n - 1).choose 3 + n.choose 3 := by
  rw [← cliqueCount_compl, ← cliqueCount_eq_of_iso (johnsonTwoIso n)]
  exact cliqueCount_johnson_two n hn

end

section
open Fintype
variable (G : CGraph)

private theorem xor_eq_decide_of_filter_eq {n : ℕ} {x y : Fin n → Bool} {i₀ : Fin n}
    (h : (Finset.univ.filter fun i ↦ x i ≠ y i) = {i₀}) (k : Fin n) :
    (x k ^^ y k) = decide (k = i₀) := by
  have hiff : (x k ≠ y k) ↔ k = i₀ := by
    constructor
    · intro hk
      have : k ∈ ({i₀} : Finset (Fin n)) := h ▸ Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      simpa using this
    · rintro rfl
      have : k ∈ (Finset.univ.filter fun i ↦ x i ≠ y i) := h ▸ Finset.mem_singleton_self k
      exact (Finset.mem_filter.1 this).2
  have hxor : (x k ^^ y k) = decide (x k ≠ y k) := by cases x k <;> cases y k <;> simp
  rw [hxor, decide_eq_decide.2 hiff]

/-- Adding a fixed bit-string is an automorphism of the hypercube. -/
def cubeXor (n : ℕ) (d : Fin n → Bool) : hypercube n ≃cg hypercube n :=
  autoOfPerm (G := hypercube n) ((xorPerm_involutive n d).toPerm _) fun x y ↦ by
    show (hammingCapped (fun i ↦ x i ^^ d i) (fun i ↦ y i ^^ d i) 0 n == 1) = _
    rw [hammingCapped_self, hammingBelow_xor]
    exact (hammingCapped_self x y).symm

/-- Permuting the coordinates is an automorphism of the hypercube: it does not change *how many*
coordinates two strings differ in. -/
def cubeCoord (n : ℕ) (τ : Equiv.Perm (Fin n)) : hypercube n ≃cg hypercube n :=
  autoOfPerm (G := hypercube n) (Equiv.arrowCongr τ (Equiv.refl Bool)) fun x y ↦ by
    show (hammingCapped (fun i ↦ x (τ.symm i)) (fun i ↦ y (τ.symm i)) 0 n == 1) = _
    rw [hammingCapped_self, hammingBelow_self, ← card_filter_ne_eq_countP, hypercube_adj]
    congr 1
    exact Finset.card_equiv τ.symm (by simp)

/-- The hypercube is arc-transitive: translate the first endpoint to the origin, swap the
coordinate in which the arc moves for the one the target arc moves in, then translate to the
second endpoint. -/
theorem isArcTransitive_hypercube (n : ℕ) : (hypercube n).IsArcTransitive := by
  intro u v u' v' huv hu'v'
  rw [hypercube_adj, beq_iff_eq] at huv hu'v'
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 huv
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.1 hu'v'
  have hswap : ∀ i : Fin n, decide (Equiv.swap i₀ j₀ i = i₀) = decide (i = j₀) := fun i ↦ by
    rw [decide_eq_decide, ← Equiv.eq_symm_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  refine ⟨((cubeXor n u).trans (cubeCoord n (Equiv.swap i₀ j₀))).trans (cubeXor n u'), ?_, ?_⟩
  · funext i
    show ((u (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) ^^ u' i) = u' i
    simp
  · funext i
    show ((v (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) ^^ u' i) = v' i
    have h1 : (u (Equiv.swap i₀ j₀ i) ^^ v (Equiv.swap i₀ j₀ i))
        = decide (Equiv.swap i₀ j₀ i = i₀) := xor_eq_decide_of_filter_eq hi₀ _
    have h2 : (u' i ^^ v' i) = decide (i = j₀) := xor_eq_decide_of_filter_eq hj₀ i
    have h3 : (v (Equiv.swap i₀ j₀ i) ^^ u (Equiv.swap i₀ j₀ i)) = (u' i ^^ v' i) := by
      rw [Bool.xor_comm (v _) (u _), h1, hswap, ← h2]
    rw [h3]
    cases u' i <;> cases v' i <;> simp

theorem isVertexTransitive_foldedCube (n : ℕ) : (foldedCube n).IsVertexTransitive := by
  intro u v
  refine ⟨autoOfPerm (G := foldedCube n)
    ((xorPerm_involutive n fun i ↦ u i ^^ v i).toPerm _) fun x y ↦ ?_, ?_⟩
  · show ((n != 0) && foldedNear (fun i ↦ x i ^^ (u i ^^ v i)) (fun i ↦ y i ^^ (u i ^^ v i)))
        = ((n != 0) && foldedNear x y)
    rw [foldedNear_eq, foldedNear_eq, hammingBelow_xor]
  · funext i
    show (u i ^^ (u i ^^ v i)) = v i
    simp

end

/-! ### The cube families through the Hamming distance

Both cube families are defined by counting the coordinates at which two bit-strings differ, which
is exactly `hammingDist`.  Restating adjacency that way gives access to the triangle inequality
and to the lemmas of `IsoGraph.ForMathlib.Hamming`, and turns the two elementary moves — flipping
one coordinate, and flipping them all — into named edges. -/

section Cubes

/-- Adjacency in the hypercube is Hamming distance one. -/
theorem hypercube_adj_hamming (n : ℕ) (x y : Fin n → Bool) :
    (hypercube n).Adj x y = true ↔ hammingDist x y = 1 := by
  simp [hypercube_adj, hammingDist]

/-- The edges of the hypercube are exactly the single coordinate flips. -/
theorem hypercube_adj_update_iff (n : ℕ) (x y : Fin n → Bool) :
    (hypercube n).Adj x y = true ↔ ∃ i, y = Function.update x i (!x i) := by
  rw [hypercube_adj_hamming, hammingDist_eq_one_iff]

/-- Adjacency in the folded cube is Hamming distance one or `n`. -/
theorem foldedCube_adj_hamming (n : ℕ) (x y : Fin n → Bool) :
    (foldedCube n).Adj x y = true ↔ x ≠ y ∧ (hammingDist x y = 1 ∨ hammingDist x y = n) := by
  simp [foldedCube_adj, hammingDist]

/-- Flipping one coordinate is an edge of the folded cube. -/
theorem foldedCube_adj_update (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (foldedCube n).Adj x (Function.update x i (!x i)) = true :=
  (foldedCube_adj_hamming n _ _).2
    ⟨fun h ↦ by simpa using congrArg (· i) h, Or.inl (hammingDist_update_not_self x i)⟩

/-- The antipodal map is an edge of the folded cube. -/
theorem foldedCube_adj_not (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (foldedCube n).Adj x (fun i ↦ !x i) = true := by
  refine (foldedCube_adj_hamming n _ _).2 ⟨fun h ↦ ?_, Or.inr ?_⟩
  · simpa using congrArg (· (⟨0, hn⟩ : Fin n)) h
  · simpa [Fintype.card_fin] using
      (hammingDist_eq_card_iff (x := x) (y := fun i ↦ !x i)).2 fun i ↦ by simp

/-- …and those are the only edges: every edge of the folded cube is either a single coordinate
flip or the antipodal map. -/
theorem foldedCube_adj_cases {n : ℕ} {u v : Fin n → Bool} (h : (foldedCube n).Adj u v = true) :
    (∃ i, v = Function.update u i (!u i)) ∨ v = fun i ↦ !u i := by
  obtain ⟨-, hd⟩ := (foldedCube_adj_hamming n u v).1 h
  rcases hd with h1 | hm
  · exact Or.inl (hammingDist_eq_one_iff.1 h1)
  · exact Or.inr (funext fun i ↦ by
      have := hammingDist_eq_card_iff.1 (by rw [hm, Fintype.card_fin]) i
      revert this; cases u i <;> cases v i <;> simp)

end Cubes

end CGraph

namespace SRG

section
open CGraph CGraph.Enum

/-! ## The parameters

Whatever can be, is proved: the rook, Kneser, triangular, Paley, complete bipartite and cocktail
party entries come from the infinite families of `IsoGraph/Core/Defs.lean`, and three
more from `isSRGWith_compl`.  What is left is `cycle 5`, `clebsch` and `shrikhande` by kernel
`decide`, and five large sporadic graphs by `native_decide`. -/

set_option maxRecDepth 4000 in
@[toIsoGraph cycle_five_srg]
theorem cycle_five_srg : (cycle 5).IsSRGWith 5 2 0 1 := by decide +kernel

@[toIsoGraph bipartite_srg]
theorem bipartite_srg : (bipartite 3 3).IsSRGWith 6 3 0 3 := isSRGWith_bipartite 3

@[toIsoGraph cocktailParty_srg]
theorem cocktailParty_srg : (cocktailParty 4).IsSRGWith 8 6 4 6 := isSRGWith_cocktailParty 4

@[toIsoGraph rook_three_srg]
theorem rook_three_srg : (rook 3 3).IsSRGWith 9 4 1 2 := isSRGWith_rook 3

@[toIsoGraph petersen_srg]
theorem petersen_srg : petersen.IsSRGWith 10 3 0 1 := isSRGWith_kneser_two 5

@[toIsoGraph triangular_five_srg]
theorem triangular_five_srg : (triangular 5).IsSRGWith 10 6 3 4 :=
  isSRGWith_triangular 5 (by norm_num)

@[toIsoGraph paley_thirteen_srg]
theorem paley_thirteen_srg : (paley 13).IsSRGWith 13 6 2 3 :=
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  isSRGWith_paley 13 (by norm_num)

@[toIsoGraph kneser_six_srg]
theorem kneser_six_srg : (kneser 6 2).IsSRGWith 15 6 1 3 := isSRGWith_kneser_two 6

@[toIsoGraph triangular_six_srg]
theorem triangular_six_srg : (triangular 6).IsSRGWith 15 8 4 4 :=
  isSRGWith_triangular 6 (by norm_num)

set_option maxRecDepth 100000 in
@[toIsoGraph clebsch_srg]
theorem clebsch_srg : clebsch.IsSRGWith 16 5 0 2 := by decide +kernel

@[toIsoGraph rook_four_srg]
theorem rook_four_srg : (rook 4 4).IsSRGWith 16 6 2 2 := isSRGWith_rook 4

set_option maxRecDepth 100000 in
@[toIsoGraph shrikhande_srg]
theorem shrikhande_srg : shrikhande.IsSRGWith 16 6 2 2 := by decide +kernel

@[toIsoGraph compl_clebsch_srg]
theorem compl_clebsch_srg : clebschᶜ.IsSRGWith 16 10 6 6 := isSRGWith_compl _ clebsch_srg

/-- The Clebsch graph is triangle-free, and its independent triples are the triangles of the
`(16, 10, 6, 6)` graph above: `16·10·6/6 = 160` of them. -/
@[toIsoGraph indepCount_clebsch]
theorem indepCount_clebsch : clebsch.indepCount 3 = 160 := by
  have h := clebsch_srg.six_mul_indepCount_three
  omega

@[toIsoGraph paley_seventeen_srg]
theorem paley_seventeen_srg : (paley 17).IsSRGWith 17 8 3 4 :=
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  isSRGWith_paley 17 (by norm_num)

@[toIsoGraph linesOnCubic_srg]
theorem linesOnCubic_srg : linesOnCubic.IsSRGWith 27 10 1 5 := by native_decide

@[toIsoGraph schlafli_srg]
theorem schlafli_srg : schlafli.IsSRGWith 27 16 10 8 := isSRGWith_compl _ linesOnCubic_srg

@[toIsoGraph triangular_eight_srg]
theorem triangular_eight_srg : (triangular 8).IsSRGWith 28 12 6 4 :=
  isSRGWith_triangular 8 (by norm_num)

@[toIsoGraph chang₁_srg]
theorem chang₁_srg : chang₁.IsSRGWith 28 12 6 4 := by native_decide

@[toIsoGraph chang₂_srg]
theorem chang₂_srg : chang₂.IsSRGWith 28 12 6 4 := by native_decide

@[toIsoGraph chang₃_srg]
theorem chang₃_srg : chang₃.IsSRGWith 28 12 6 4 := by native_decide

@[toIsoGraph paley_twentynine_srg]
theorem paley_twentynine_srg : (paley 29).IsSRGWith 29 14 6 7 :=
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  isSRGWith_paley 29 (by norm_num)

@[toIsoGraph hoffmanSingleton_srg]
theorem hoffmanSingleton_srg : hoffmanSingleton.IsSRGWith 50 7 0 1 := by native_decide

@[toIsoGraph compl_hoffmanSingleton_srg]
theorem compl_hoffmanSingleton_srg : hoffmanSingletonᶜ.IsSRGWith 50 42 35 36 :=
  isSRGWith_compl _ hoffmanSingleton_srg

@[toIsoGraph gewirtz_srg]
theorem gewirtz_srg : gewirtz.IsSRGWith 56 10 0 2 := by native_decide

@[toIsoGraph m22_srg]
theorem m22_srg : m22.IsSRGWith 77 16 0 4 := by native_decide

@[toIsoGraph higmanSims_srg]
theorem higmanSims_srg : higmanSims.IsSRGWith 100 22 0 6 := by native_decide

@[toIsoGraph compl_higmanSims_srg]
theorem compl_higmanSims_srg : higmanSimsᶜ.IsSRGWith 100 77 60 56 :=
  isSRGWith_compl _ higmanSims_srg

@[toIsoGraph paley_hundredone_srg]
theorem paley_hundredone_srg : (paley 101).IsSRGWith 101 50 24 25 :=
  haveI : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  isSRGWith_paley 101 (by norm_num)

/-! ## Identifications and separations

Same parameters need not mean isomorphic, and different descriptions often do.  Where the two
graphs are already the same construction in disguise the isomorphism is written down; otherwise
the question is decided by the canonical key. -/

/-- `Paley(5)` is the 5-cycle.  Both are circulants on `Fin 5` — the nonzero squares mod `5` are
`{1, 4}`, which is `{±1}` — so the identity is already an isomorphism and the twenty-five
adjacency comparisons fit inside kernel `decide`. -/
@[toIsoGraph paley_five]
def paleyFiveIso : paley 5 ≃cg cycle 5 :=
  ⟨Equiv.refl (Fin 5), fun {a b} ↦ by revert a b; decide⟩

/-- `T(5)` is the complement of the Petersen graph — a special case of `johnsonTwoIso`, which
identifies `johnson n 2` with `(kneser n 2)ᶜ` for every `n`. -/
@[toIsoGraph triangular_five_eq_compl_petersen]
def triangularFiveIso : triangular 5 ≃cg petersenᶜ := johnsonTwoIso 5

/-- `T(4)` is the octahedron `K_{2,2,2}`.  Nothing identifies the two vertex sets by hand here;
the canonical keys agree, and `isoOfKeyEq` extracts a witness from that. -/
@[toIsoGraph triangular_four_eq_octahedron]
noncomputable def triangularFourIso : triangular 4 ≃cg cocktailParty 3 :=
  isoOfKeyEq (by native_decide)

/-- The Shrikhande graph is *not* the `4 × 4` rook's graph, though the two share the parameters
`(16, 6, 2, 2)`.  Together they are all the strongly regular graphs with those parameters. -/
theorem shrikhande_not_iso_rook : ¬Nonempty (shrikhande ≃cg rook 4 4) := by
  rw [← key_eq_iff]; native_decide

/-- `T(8)` and the three Chang graphs are pairwise non-isomorphic — a complete list of the
strongly regular graphs with parameters `(28, 12, 6, 4)`. -/
theorem changs_pairwise_not_iso :
    ([triangular 8, chang₁, chang₂, chang₃] : List CGraph).Pairwise
      fun G H ↦ ¬Nonempty (G ≃cg H) := by
  have h : (([triangular 8, chang₁, chang₂, chang₃] : List CGraph).map key).Pairwise (· ≠ ·) := by
    native_decide
  rw [List.pairwise_map] at h
  exact h.imp fun hne he ↦ hne (key_eq_iff.2 he)

/-! ## The table as data -/

/-- One row of the table: a graph, its parameters, and the proof that they are its parameters. -/
structure Entry where
  /-- What the graph is usually called. -/
  name : String
  /-- The graph. -/
  graph : CGraph
  /-- Number of vertices. -/
  n : ℕ
  /-- Degree of every vertex. -/
  k : ℕ
  /-- Common neighbours of an adjacent pair. -/
  ℓ : ℕ
  /-- Common neighbours of a distinct non-adjacent pair. -/
  μ : ℕ
  /-- The parameters are right. -/
  isSRG : graph.IsSRGWith n k ℓ μ

/-- Every strongly regular graph in this development, with its parameters. -/
def table : List Entry :=
  [ ⟨"C₅ = Paley(5)", cycle 5, 5, 2, 0, 1, cycle_five_srg⟩,
    ⟨"K₃,₃", bipartite 3 3, 6, 3, 0, 3, bipartite_srg⟩,
    ⟨"K₄ₓ₂ (cocktail party)", cocktailParty 4, 8, 6, 4, 6, cocktailParty_srg⟩,
    ⟨"3×3 rook = Paley(9)", rook 3 3, 9, 4, 1, 2, rook_three_srg⟩,
    ⟨"Petersen", petersen, 10, 3, 0, 1, petersen_srg⟩,
    ⟨"T(5)", triangular 5, 10, 6, 3, 4, triangular_five_srg⟩,
    ⟨"Paley(13)", paley 13, 13, 6, 2, 3, paley_thirteen_srg⟩,
    ⟨"Kneser K(6,2)", kneser 6 2, 15, 6, 1, 3, kneser_six_srg⟩,
    ⟨"T(6)", triangular 6, 15, 8, 4, 4, triangular_six_srg⟩,
    ⟨"Clebsch", clebsch, 16, 5, 0, 2, clebsch_srg⟩,
    ⟨"4×4 rook", rook 4 4, 16, 6, 2, 2, rook_four_srg⟩,
    ⟨"Shrikhande", shrikhande, 16, 6, 2, 2, shrikhande_srg⟩,
    ⟨"complement of Clebsch", clebschᶜ, 16, 10, 6, 6, compl_clebsch_srg⟩,
    ⟨"Paley(17)", paley 17, 17, 8, 3, 4, paley_seventeen_srg⟩,
    ⟨"27 lines on a cubic", linesOnCubic, 27, 10, 1, 5, linesOnCubic_srg⟩,
    ⟨"Schläfli", schlafli, 27, 16, 10, 8, schlafli_srg⟩,
    ⟨"T(8)", triangular 8, 28, 12, 6, 4, triangular_eight_srg⟩,
    ⟨"Chang 1 (4K₂)", chang₁, 28, 12, 6, 4, chang₁_srg⟩,
    ⟨"Chang 2 (C₈)", chang₂, 28, 12, 6, 4, chang₂_srg⟩,
    ⟨"Chang 3 (C₃ ∪ C₅)", chang₃, 28, 12, 6, 4, chang₃_srg⟩,
    ⟨"Paley(29)", paley 29, 29, 14, 6, 7, paley_twentynine_srg⟩,
    ⟨"Hoffman–Singleton", hoffmanSingleton, 50, 7, 0, 1, hoffmanSingleton_srg⟩,
    ⟨"complement of Hoffman–Singleton", hoffmanSingletonᶜ, 50, 42, 35, 36,
      compl_hoffmanSingleton_srg⟩,
    ⟨"Gewirtz", gewirtz, 56, 10, 0, 2, gewirtz_srg⟩,
    ⟨"M₂₂", m22, 77, 16, 0, 4, m22_srg⟩,
    ⟨"Higman–Sims", higmanSims, 100, 22, 0, 6, higmanSims_srg⟩,
    ⟨"complement of Higman–Sims", higmanSimsᶜ, 100, 77, 60, 56, compl_higmanSims_srg⟩,
    ⟨"Paley(101)", paley 101, 101, 50, 24, 25, paley_hundredone_srg⟩ ]

#guard table.length = 28

#guard table.map (fun e ↦ e.n) =
  [5, 6, 8, 9, 10, 10, 13, 15, 15, 16, 16, 16, 16, 17, 27, 27, 28, 28, 28, 28, 29, 50, 50, 56, 77,
    100, 100, 101]

/-- The parameters of any row satisfy the standard feasibility identity
`k (k - ℓ - 1) = (n - k - 1) μ` — counting, in two ways, the edges between the neighbours and the
non-neighbours of a vertex. -/
theorem param_eq (e : Entry) (hn : 0 < e.n) : e.k * (e.k - e.ℓ - 1) = (e.n - e.k - 1) * e.μ :=
  SimpleGraph.IsSRGWith.param_eq _ e.isSRG hn

end

end SRG

namespace CGraph

/-! ## Circulants

`circulant_congr` says that only the differences in `(0, n)` matter, and the three corollaries
normalise a connection set: drop a `0`, drop a repeat, and replace `k` by `n - k`. -/

/-- **Only the differences in `(0, n)` matter.**  A circulant only ever asks whether its
connection set contains a difference of two distinct vertices, so two connection sets agreeing
there give the same graph — on the nose, not just up to isomorphism. -/
@[toIsoGraph]
theorem circulant_congr (n : ℕ) (S T : List ℕ)
    (h : ∀ d, 0 < d → d < n → S.contains d = T.contains d) :
    circulant n S = circulant n T := by
  refine (eq_ofRel (circulant n S) (fun x y ↦ T.contains ((y.1 + n - x.1) % n))
    fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  obtain ⟨-, hp, hq⟩ := circulant_diff_facts n x y hne
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  show (decide (x ≠ y) && (S.contains ((y.1 + n - x.1) % n) ||
    S.contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and, h _ hp (Nat.mod_lt _ hn), h _ hq (Nat.mod_lt _ hn)]

/-- A `0` in the connection set contributes nothing: `x` and `y` differ by `0` only when they are
equal, and a circulant has no loops. -/
@[toIsoGraph]
theorem circulant_zero_cons (n : ℕ) (S : List ℕ) :
    circulant n (0 :: S) = circulant n S :=
  circulant_congr n _ _ fun d hd _ ↦ by
    have h0 : (d == 0) = false := by simp; omega
    simp only [List.contains_cons, h0, Bool.false_or]

/-- A repeated entry in the connection set contributes nothing. -/
@[toIsoGraph]
theorem circulant_dup_cons (n k : ℕ) (S : List ℕ) :
    circulant n (k :: k :: S) = circulant n (k :: S) :=
  circulant_congr n _ _ fun d _ _ ↦ by
    simp only [List.contains_cons]
    cases (d == k) <;> simp

/-- **The connection set is symmetric.**  A circulant joins `x` to `y` when either difference is
listed, so replacing an entry `k` by `n - k` does not change the graph. -/
@[toIsoGraph]
theorem circulant_neg_cons (n k : ℕ) (hk : k ≤ n) (S : List ℕ) :
    circulant n (k :: S) = circulant n ((n - k) :: S) := by
  refine (eq_ofRel (circulant n (k :: S))
    (fun x y ↦ ((n - k) :: S).contains ((y.1 + n - x.1) % n)) fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  obtain ⟨hsum, hp, hq⟩ := circulant_diff_facts n x y hne
  have key : ((y.1 + n - x.1) % n = k ∨ (x.1 + n - y.1) % n = k) ↔
      ((y.1 + n - x.1) % n = n - k ∨ (x.1 + n - y.1) % n = n - k) := by omega
  show (decide (x ≠ y) && ((k :: S).contains ((y.1 + n - x.1) % n) ||
    (k :: S).contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and]
  refine Bool.eq_iff_iff.2 ?_
  simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq]
  tauto

/-- The connection set of `Paley(13)` is `{±1, ±3, ±4}`. -/
@[toIsoGraph]
theorem paley_thirteen_eq_circulant : paley 13 = circulant 13 [1, 3, 4] :=
  eq_ofRel _ _ (by decide +kernel)

/-- The connection set of `Paley(17)` is `{±1, ±2, ±4, ±8}`. -/
@[toIsoGraph]
theorem paley_seventeen_eq_circulant : paley 17 = circulant 17 [1, 2, 4, 8] :=
  eq_ofRel _ _ (by decide +kernel)

/-- A tadpole with no tail is a cycle. -/
@[simp, toIsoGraph] theorem tadpole_zero (m : ℕ) : tadpole m 0 = cycle m := by
  rw [tadpole, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cycleEdges]

/-- A tadpole with no cycle is a path. -/
@[simp, toIsoGraph] theorem tadpole_zero_left (k : ℕ) : tadpole 0 k = path k := by
  rw [tadpole, cycleEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A tadpole whose cycle is a single vertex is a path: the "cycle" is a loop, which `ofEdges`
discards. -/
@[simp, toIsoGraph] theorem tadpole_one (k : ℕ) : tadpole 1 k = path (1 + k) := by
  rw [tadpole, ofEdges_cycleEdges_one_append, ofEdges_legEdges_one]

/-- A lollipop with no stick is a complete graph. -/
@[simp, toIsoGraph] theorem lollipop_zero (m : ℕ) : lollipop m 0 = complete m := by
  rw [lollipop, legEdges_zero, List.append_nil, Nat.add_zero, ofEdges_cliqueEdges]

/-- A lollipop with no clique is a path. -/
@[simp, toIsoGraph] theorem lollipop_zero_left (k : ℕ) : lollipop 0 k = path k := by
  rw [lollipop, cliqueEdges_zero, List.nil_append, Nat.zero_add, ofEdges_legEdges_zero]

/-- A lollipop whose clique is a single vertex is a path. -/
@[simp, toIsoGraph] theorem lollipop_one (k : ℕ) : lollipop 1 k = path (1 + k) := by
  rw [lollipop, cliqueEdges_one, List.nil_append, ofEdges_legEdges_one]

/-- `K₂` and `C₂` have the same edges, so a lollipop on two vertices is a tadpole. -/
@[toIsoGraph lollipop_two_eq_tadpole]
theorem lollipop_two (k : ℕ) : lollipop 2 k = tadpole 2 k := by
  rw [lollipop, tadpole]
  refine ofEdges_append_congr _ _ _ _ fun p q _ ↦ ?_
  simp only [mem_cliqueEdges, mem_cycleEdges]
  omega

/-- `K₃` and `C₃` have the same edges, so a lollipop on three vertices is a tadpole. -/
@[toIsoGraph lollipop_three_eq_tadpole]
theorem lollipop_three (k : ℕ) : lollipop 3 k = tadpole 3 k := by
  rw [lollipop, tadpole]
  refine ofEdges_append_congr _ _ _ _ fun p q _ ↦ ?_
  simp only [mem_cliqueEdges, mem_cycleEdges]
  omega

/-- A spider with an empty leg is the spider without it. -/
@[toIsoGraph]
theorem spider_zero_cons (ks : List ℕ) : spider (0 :: ks) = spider ks := by
  rw [spider, spider, List.sum_cons, Nat.zero_add,
    show spiderEdges 1 (0 :: ks) = spiderEdges 1 ks from by
      rw [spiderEdges, legEdges_zero, List.nil_append, Nat.add_zero]]

/-- A spider ignores its empty legs wherever they sit in the list, not just at the front. -/
@[toIsoGraph]
theorem spider_append_zero_cons (pre post : List ℕ) :
    spider (pre ++ 0 :: post) = spider (pre ++ post) := by
  have hsum : (pre ++ 0 :: post).sum = (pre ++ post).sum := by
    simp only [List.sum_append, List.sum_cons, Nat.zero_add]
  rw [spider, spider, hsum, spiderEdges_append, spiderEdges_append, spiderEdges, legEdges_zero,
    List.nil_append, Nat.add_zero]

/-- A spider with a single leg is a path. -/
@[simp, toIsoGraph] theorem spider_singleton (k : ℕ) : spider [k] = path (1 + k) := by
  rw [spider, show spiderEdges 1 [k] = legEdges 0 1 k from by simp [spiderEdges],
    show (1 : ℕ) + [k].sum = 1 + k from by simp, ofEdges_legEdges_one]

/-- A spider all of whose legs are empty is a single vertex. -/
@[simp, toIsoGraph]
theorem spider_replicate_zero (j : ℕ) :
    spider (List.replicate j 0) = empty 1 := by
  rw [spider, spiderEdges_replicate_zero,
    show (1 : ℕ) + (List.replicate j 0).sum = 1 from by simp, ofEdges_nil]

@[simp, toIsoGraph] theorem spider_nil : spider [] = empty 1 := spider_replicate_zero 0

/-- A cycle carrying no pendant vertices is a cycle. -/
@[simp, toIsoGraph] theorem cyclePendant_replicate_zero (m j : ℕ) :
    cyclePendant m (List.replicate j 0) = cycle m := by
  rw [cyclePendant, pendantEdges_replicate_zero, List.append_nil,
    show m + (List.replicate j 0).sum = m from by simp, ofEdges_cycleEdges]

@[simp, toIsoGraph] theorem cyclePendant_nil (m : ℕ) : cyclePendant m [] = cycle m :=
  cyclePendant_replicate_zero m 0

/-- A cycle with a trailing empty block of pendant vertices is the cycle without that block. -/
@[toIsoGraph]
theorem cyclePendant_append_zero (m : ℕ) (ks : List ℕ) :
    cyclePendant m (ks ++ [0]) = cyclePendant m ks := by
  have hsum : (ks ++ [0]).sum = ks.sum := by simp
  rw [cyclePendant, cyclePendant, pendantEdges_append_zero, hsum]

/-- Two paths of length one between the poles of a theta graph are the same single edge, so one of
them can be dropped. -/
@[toIsoGraph]
theorem thetaGraph_zero_zero_cons (ks : List ℕ) :
    thetaGraph (0 :: 0 :: ks) = thetaGraph (0 :: ks) := by
  rw [thetaGraph, thetaGraph]
  simp only [List.sum_cons, Nat.zero_add]
  refine ofEdges_congr _ _ _ fun p q _ ↦ ?_
  simp only [thetaEdges, List.mem_cons]
  tauto

/-- Adjacency in `spider ks`, phrased entirely in terms of the underlying naturals. -/
theorem spider_adj_val (ks : List ℕ) (u v : (spider ks).V) :
    (spider ks).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ spiderEdges 1 ks ∨ (v.1, u.1) ∈ spiderEdges 1 ks)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `tadpole m k`, phrased entirely in terms of the underlying naturals. -/
theorem tadpole_adj_val (m k : ℕ) (u v : (tadpole m k).V) :
    (tadpole m k).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ cycleEdges m ++ legEdges 0 m k ∨
        (v.1, u.1) ∈ cycleEdges m ++ legEdges 0 m k)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `lollipop m k`, phrased entirely in terms of the underlying naturals. -/
theorem lollipop_adj_val (m k : ℕ) (u v : (lollipop m k).V) :
    (lollipop m k).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ cliqueEdges m ++ legEdges 0 m k ∨
        (v.1, u.1) ∈ cliqueEdges m ++ legEdges 0 m k)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `cyclePendant m ks`, phrased entirely in terms of the underlying naturals. -/
theorem cyclePendant_adj_val (m : ℕ) (ks : List ℕ) (u v : (cyclePendant m ks).V) :
    (cyclePendant m ks).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ cycleEdges m ++ pendantEdges 0 m ks ∨
        (v.1, u.1) ∈ cycleEdges m ++ pendantEdges 0 m ks)) :=
  ofEdges_adj_val _ _ u v

/-- Adjacency in `thetaGraph xs`, phrased entirely in terms of the underlying naturals. -/
theorem thetaGraph_adj_val (xs : List ℕ) (u v : (thetaGraph xs).V) :
    (thetaGraph xs).Adj u v = true ↔
      (u.1 ≠ v.1 ∧ ((u.1, v.1) ∈ thetaEdges 2 xs ∨ (v.1, u.1) ∈ thetaEdges 2 xs)) :=
  ofEdges_adj_val _ _ u v

@[toIsoGraph]
theorem thetaGraph_nil : thetaGraph [] = empty 2 := ofEdges_nil 2

/-- A theta graph all of whose paths are single edges is just that edge. -/
@[toIsoGraph]
theorem thetaGraph_replicate_zero (j : ℕ) :
    thetaGraph (List.replicate (j + 1) 0) = complete 2 := by
  have hs : (List.replicate (j + 1) (0 : ℕ)).sum = 0 := by simp
  rw [thetaGraph, hs]
  refine (eq_ofRel (ofEdges (2 + 0) (thetaEdges 2 (List.replicate (j + 1) 0)))
    (fun _ _ ↦ true) ?_).trans (complete_eq_ofRel 2).symm
  intro x y hxy
  have hx : x.1 < 2 := x.isLt
  have hy : y.1 < 2 := y.isLt
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  simp only [ofEdges_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_thetaEdges_replicate_zero, or_self, iff_true]
  omega

/-- A one-vertex "cycle" carrying `k` pendant vertices is the `k`-legged spider whose legs all
have length one: the loop is discarded, and the pendant edges are the legs. -/
theorem cyclePendant_one_eq_spider (k : ℕ) :
    cyclePendant 1 [k] = spider (List.replicate k 1) := by
  have hsum : (1 : ℕ) + ([k] : List ℕ).sum = 1 + (List.replicate k 1).sum := by simp
  have hes : pendantEdges 0 1 [k] = spiderEdges 1 (List.replicate k 1) := by
    rw [spiderEdges_replicate_one]
    simp only [pendantEdges, List.append_nil]
  rw [cyclePendant, spider, hsum, hes, ofEdges_cycleEdges_one_append]

/-! ### A cycle with a single pendant vertex -/

/-- A cycle carrying a single pendant vertex is a tadpole with a leg of length one. -/
@[toIsoGraph]
theorem cyclePendant_singleton_one (m : ℕ) : cyclePendant m [1] = tadpole m 1 := by
  rw [cyclePendant, tadpole, show ([1] : List ℕ).sum = 1 from rfl,
    show pendantEdges 0 m [1] = legEdges 0 m 1 from by
      simp [pendantEdges, legEdges, pathEdges]]

/-- Adjacency in `doubleStar m n`, phrased entirely in terms of the underlying naturals. -/
theorem doubleStar_adj_val (m n : ℕ) (u v : (doubleStar m n).V) :
    (doubleStar m n).Adj u v = true ↔
      (u.1 ≠ v.1 ∧
        (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
            (u.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + n)) ∨
          ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + m) ∨
            (v.1 = 1 ∧ 2 + m ≤ u.1 ∧ u.1 < 2 + m + n)))) := by
  simp only [doubleStar]
  rw [ofEdges_adj_val]
  simp only [mem_doubleStarEdges]

/-! ### Triangles and odd cycles in graphs on sets -/

/-- The block `[a, a + k)` as a `k`-element subset of `Fin n`. -/
private def kneserBlock (n k a : ℕ) (h : a + k ≤ n) : {s : Finset (Fin n) // s.card = k} :=
  ⟨(Finset.Ico a (a + k)).attachFin (fun x hx ↦ by
      simp only [Finset.mem_Ico] at hx; omega),
   by rw [Finset.card_attachFin, Nat.card_Ico]; omega⟩

private theorem mem_kneserBlock {n k a : ℕ} {h : a + k ≤ n} (i : Fin n) :
    i ∈ (kneserBlock n k a h).1 ↔ a ≤ i.1 ∧ i.1 < a + k := by
  simp [kneserBlock, Finset.mem_attachFin]

private theorem mk_mem_kneserBlock {n k a : ℕ} {h : a + k ≤ n} (i : ℕ) (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∈ (kneserBlock n k a h).1 ↔ a ≤ i ∧ i < a + k := by
  simp [kneserBlock, Finset.mem_attachFin]

private theorem kneserBlock_ne {n k a b : ℕ} {ha : a + k ≤ n} {hb : b + k ≤ n} (hk : 0 < k)
    (hab : a ≠ b) : kneserBlock n k a ha ≠ kneserBlock n k b hb := by
  intro hEq
  have h1 : (⟨a, by omega⟩ : Fin n) ∈ (kneserBlock n k a ha).1 :=
    (mk_mem_kneserBlock _ _).2 (by omega)
  have h2 : (⟨b, by omega⟩ : Fin n) ∈ (kneserBlock n k b hb).1 :=
    (mk_mem_kneserBlock _ _).2 (by omega)
  rw [hEq, mk_mem_kneserBlock] at h1
  rw [← hEq, mk_mem_kneserBlock] at h2
  omega

/-- **Kneser graphs with room for three disjoint blocks are not bipartite.** -/
@[toIsoGraph]
theorem not_isBipartite_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) :
    ¬ (CGraph.kneser n k).IsBipartite := by
  refine not_isBipartite_of_triangle
    (a := kneserBlock n k 0 (by omega)) (b := kneserBlock n k k (by omega))
    (d := kneserBlock n k (2 * k) (by omega)) ?_ ?_ ?_ <;>
  · rw [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨kneserBlock_ne hk (by omega), ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_kneserBlock, mem_kneserBlock] at hx
    omega

/-- The `(k+1)`-element subset `{0, …, k-1} ∪ {k + j}` of `Fin n`. -/
private def johnsonTri (n k j : ℕ) (h : k + j < n) : {s : Finset (Fin n) // s.card = k + 1} :=
  ⟨(insert (k + j) (Finset.range k)).attachFin (fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_range] at hx; omega),
   by rw [Finset.card_attachFin, Finset.card_insert_of_notMem (by simp), Finset.card_range]⟩

private theorem mem_johnsonTri {n k j : ℕ} {h : k + j < n} (i : Fin n) :
    i ∈ (johnsonTri n k j h).1 ↔ i.1 = k + j ∨ i.1 < k := by
  simp [johnsonTri, Finset.mem_attachFin]

private theorem mk_mem_johnsonTri {n k j : ℕ} {h : k + j < n} (i : ℕ) (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∈ (johnsonTri n k j h).1 ↔ i = k + j ∨ i < k := by
  simp [johnsonTri, Finset.mem_attachFin]

private theorem johnsonTri_ne {n k j j' : ℕ} {h : k + j < n} {h' : k + j' < n} (hjj : j ≠ j') :
    johnsonTri n k j h ≠ johnsonTri n k j' h' := by
  intro hEq
  have h1 : (⟨k + j, h⟩ : Fin n) ∈ (johnsonTri n k j h).1 :=
    (mk_mem_johnsonTri _ _).2 (Or.inl rfl)
  rw [hEq, mk_mem_johnsonTri] at h1
  omega

private theorem johnsonTri_inter {n k j j' : ℕ} {h : k + j < n} {h' : k + j' < n} (hjj : j ≠ j') :
    ((johnsonTri n k j h).1 ∩ (johnsonTri n k j' h').1).card = k := by
  have key : (johnsonTri n k j h).1 ∩ (johnsonTri n k j' h').1
      = (Finset.range k).attachFin (n := n) (fun x hx ↦ by
          simp only [Finset.mem_range] at hx; omega) := by
    ext i
    simp only [Finset.mem_inter, mem_johnsonTri, Finset.mem_attachFin, Finset.mem_range]
    omega
  rw [key, Finset.card_attachFin, Finset.card_range]

/-- **Johnson graphs on at least `k + 2` points are not bipartite.** -/
@[toIsoGraph]
theorem not_isBipartite_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) :
    ¬ (CGraph.johnson n k).IsBipartite := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine not_isBipartite_of_triangle
    (a := johnsonTri n k 0 (by omega)) (b := johnsonTri n k 1 (by omega))
    (d := johnsonTri n k 2 (by omega)) ?_ ?_ ?_ <;>
  · rw [johnson_adj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.add_sub_cancel]
    exact ⟨johnsonTri_ne (by omega), johnsonTri_inter (by omega)⟩

/-- The outer five-cycle of the Petersen graph, as a walk in `kneser 5 2`. -/
private def petersenWalk (k : ℕ) : (CGraph.kneser 5 2).V :=
  if k % 5 = 0 then ⟨{0, 1}, by decide +kernel⟩
  else if k % 5 = 1 then ⟨{2, 3}, by decide +kernel⟩
  else if k % 5 = 2 then ⟨{4, 0}, by decide +kernel⟩
  else if k % 5 = 3 then ⟨{1, 2}, by decide +kernel⟩
  else ⟨{3, 4}, by decide +kernel⟩

/-- **The Petersen graph is not bipartite**: it has no triangle, but it does have a five-cycle. -/
theorem not_isBipartite_kneser_five_two : ¬ (CGraph.kneser 5 2).IsBipartite :=
  not_isBipartite_of_odd_walk petersenWalk 5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

@[simp, toIsoGraph] theorem degSequence_kneser {n k : ℕ} (hk : 1 ≤ k) :
    (kneser n k).degSequence = List.replicate (n.choose k) ((n - k).choose k) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_kneser hk), card_kneser]

@[simp] theorem degSequence_rook (m n : ℕ) :
    (rook m n).degSequence = List.replicate (m * n) ((n - 1) + (m - 1)) := by
  rw [degSequence_of_card_nbrs _ (card_nbrs_rook)]
  congr 1

section
variable {G H : CGraph}

/-! ### The greedy colouring of a Kneser graph -/

/-- The heart of the Kneser bound: two disjoint `k`-sets cannot have the same capped minimum.
Below the cap they would share their smallest element; at the cap both sets live in the top
`n - (n - 2k + 1)` elements, which is fewer than the `2k` they need between them. -/
private theorem kneser_color_ne {n k : ℕ} (hk : 0 < k) {s t : Finset (Fin n)}
    (hs : s.card = k) (ht : t.card = k) (hinter : s ∩ t = ∅)
    {ms mt : Fin n} (hms : ms ∈ s) (hmsle : ∀ x ∈ s, ms ≤ x)
    (hmt : mt ∈ t) (hmtle : ∀ x ∈ t, mt ≤ x) :
    min (ms : ℕ) (n - 2 * k + 1) ≠ min (mt : ℕ) (n - 2 * k + 1) := by
  classical
  intro heq
  set c := n - 2 * k + 1 with hc
  rcases lt_or_ge (ms : ℕ) c with hlt | hge
  · -- the two smallest elements agree, so the sets meet
    rw [min_eq_left hlt.le] at heq
    have hmt' : (mt : ℕ) = (ms : ℕ) := by
      rcases lt_or_ge (mt : ℕ) c with h | h
      · rw [min_eq_left h.le] at heq; omega
      · rw [min_eq_right h] at heq; omega
    have hmem : ms ∈ s ∩ t := Finset.mem_inter.2 ⟨hms, Fin.ext hmt' ▸ hmt⟩
    rw [hinter] at hmem
    simp at hmem
  · -- both sets live above the cap, and there is no room for `2k` vertices there
    rw [min_eq_right hge] at heq
    have hget : c ≤ (mt : ℕ) := by
      rcases lt_or_ge (mt : ℕ) c with h | h
      · rw [min_eq_left h.le] at heq; omega
      · exact h
    have hsub : s ∪ t ⊆ Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ) := by
      intro x hx
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.1 hx with h | h
      · exact le_trans hge (hmsle x h)
      · exact le_trans hget (hmtle x h)
    have hdisj : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.2 hinter
    have hcard : (s ∪ t).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, hs, ht]; ring
    have hfil : (Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ)).card ≤ n - c := by
      have h := Finset.card_le_card_of_injOn (f := fun x : Fin n ↦ (x : ℕ))
        (s := Finset.univ.filter fun x : Fin n ↦ c ≤ (x : ℕ)) (t := Finset.Ico c n)
        (fun x hx ↦ Finset.mem_Ico.2 ⟨(Finset.mem_filter.1 hx).2, x.isLt⟩)
        (fun x _ y _ h ↦ Fin.ext h)
      rwa [Nat.card_Ico] at h
    have hle := le_trans (Finset.card_le_card hsub) hfil
    omega

/-- **`χ(K(n, k)) ≤ n - 2k + 2`.**  Colour a `k`-set by its smallest element, capped at
`n - 2k + 1`. -/
@[toIsoGraph]
theorem chromNum_kneser_le (n k : ℕ) (hk : 0 < k) :
    (kneser n k).chromNum ≤ n - 2 * k + 2 := by
  classical
  rw [chromNum_le_iff_colorable, SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  have hnonempty : ∀ s : {s : Finset (Fin n) // s.card = k}, (s : Finset (Fin n)).Nonempty := by
    intro s
    rw [← Finset.card_pos, s.2]
    exact hk
  refine ⟨SimpleGraph.Coloring.mk
    (fun s : {s : Finset (Fin n) // s.card = k} ↦
      min ((s : Finset (Fin n)).min' (hnonempty s)) (n - 2 * k + 1)) ?_, fun s ↦ ?_⟩
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ hadj
    rw [CGraph.toSimple_adj, kneser_adj] at hadj
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Subtype.mk.injEq] at hadj
    exact kneser_color_ne hk hs ht hadj.2 (s.min'_mem _) (fun x hx ↦ s.min'_le x hx)
      (t.min'_mem _) fun x hx ↦ t.min'_le x hx
  · exact lt_of_le_of_lt (min_le_right _ _) (by omega)

/-! ### Girth four -/

/-- A bipartite graph with a square has girth exactly four. -/
theorem girth_eq_four_of_square_of_isBipartite {G : CGraph} (hb : G.IsBipartite) {a b c d : G.V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c)
    (hbd : b ≠ d) : G.girth = 4 :=
  le_antisymm (girth_le_four_of_square hab hbc hcd hda hac hbd)
    (four_le_girth_of_isBipartite hb (not_isAcyclic_of_square hab hbc hcd hda hac hbd))

/-- **A Cartesian product of two bipartite graphs with an edge each has girth four**: the two
edges span a square, and the product is bipartite so there is no triangle. -/
@[toIsoGraph]
theorem girth_cartesianProduct {G H : CGraph}
    (hG : 0 < G.E) (hH : 0 < H.E) (hbG : G.IsBipartite) (hbH : H.IsBipartite) :
    (G □g H).girth = 4 := by
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  refine girth_eq_four_of_square_of_isBipartite (hbG.cartesianProduct hbH)
    (a := ((a, b) : (G □g H).V)) (b := (a', b)) (c := (a', b')) (d := (a, b'))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-- **A triangle in a Cartesian product projects to a triangle in a factor.**  Each product edge
moves exactly one coordinate; a triangle whose edges do not all move the same coordinate would
need an edge moving both. -/
theorem triangle_cartesianProduct {G H : CGraph}
    (hG : ∀ x y z : G.V, G.Adj x y → G.Adj y z → G.Adj z x → False)
    (hH : ∀ x y z : H.V, H.Adj x y → H.Adj y z → H.Adj z x → False)
    (x y z : (G □g H).V) (h1 : (G □g H).Adj x y)
    (h2 : (G □g H).Adj y z) (h3 : (G □g H).Adj z x) : False := by
  have hne : ∀ a b : (G □g H).V, (G □g H).Adj a b →
      (G.Adj a.1 b.1 ∧ a.2 = b.2 ∧ a.1 ≠ b.1) ∨ (H.Adj a.2 b.2 ∧ a.1 = b.1 ∧ a.2 ≠ b.2) := by
    intro a b hab
    rw [cartesianProduct_adj, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, decide_eq_true_eq] at hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha, fun h ↦ H.loopless b.2 (h ▸ hb)⟩
    · exact Or.inl ⟨ha, hb, fun h ↦ G.loopless b.1 (h ▸ ha)⟩
  rcases hne _ _ h1 with ⟨g1, e1, n1⟩ | ⟨g1, e1, n1⟩ <;>
    rcases hne _ _ h2 with ⟨g2, e2, n2⟩ | ⟨g2, e2, n2⟩ <;>
      rcases hne _ _ h3 with ⟨g3, e3, n3⟩ | ⟨g3, e3, n3⟩
  all_goals first
    | exact hG _ _ _ g1 g2 g3
    | exact hH _ _ _ g1 g2 g3
    | simp_all

/-- **A Cartesian product of two triangle-free graphs with an edge each has girth four.** -/
@[toIsoGraph]
theorem girth_cartesianProduct_of_cliqueNum_le_two {G H : CGraph}
 (hG : 0 < G.E) (hH : 0 < H.E) (hcG : G.cliqueNum ≤ 2)
    (hcH : H.cliqueNum ≤ 2) : (G □g H).girth = 4 := by
  have tri : ∀ (K : CGraph), K.cliqueNum ≤ 2 →
      ∀ x y z : K.V, K.Adj x y → K.Adj y z → K.Adj z x → False := by
    intro K hK x y z h1 h2 h3
    have := girth_eq_three_iff.1 (girth_eq_three_of_triangle h1 h2 h3)
    omega
  obtain ⟨a, a', ha⟩ := exists_adj_of_E_pos hG
  obtain ⟨b, b', hb⟩ := exists_adj_of_E_pos hH
  have hane : a ≠ a' := by rintro rfl; exact absurd ha (by simp [G.loopless])
  have hbne : b ≠ b' := by rintro rfl; exact absurd hb (by simp [H.loopless])
  refine le_antisymm (girth_cartesianProduct_le_four hG hH)
    (four_le_girth (triangle_cartesianProduct (tri G hcG) (tri H hcH)) ?_)
  refine not_isAcyclic_of_square (a := ((a, b) : (G □g H).V)) (b := (a', b))
    (c := (a', b')) (d := (a, b')) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [cartesianProduct_adj]; simp [ha]
  · rw [cartesianProduct_adj]; simp [hb]
  · rw [cartesianProduct_adj]; simp [G.symm a' a, ha]
  · rw [cartesianProduct_adj]; simp [H.symm b' b, hb]
  · exact fun h ↦ hane (congrArg Prod.fst h)
  · exact fun h ↦ hane (congrArg Prod.fst h).symm

/-- **A Kneser graph with room for three disjoint blocks has girth three.** -/
@[toIsoGraph]
theorem girth_kneser {n k : ℕ} (hk : 0 < k) (h : 3 * k ≤ n) : (kneser n k).girth = 3 := by
  refine girth_eq_three_of_triangle
    (a := kneserBlock n k 0 (by omega)) (b := kneserBlock n k k (by omega))
    (c := kneserBlock n k (2 * k) (by omega)) ?_ ?_ ?_ <;>
  · rw [kneser_adj, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨kneserBlock_ne hk (by omega), ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_kneserBlock, mem_kneserBlock] at hx
    omega

/-- **A Johnson graph on at least `k + 2` points has girth three**: three `k`-sets sharing a
common `(k-1)`-set are pairwise adjacent. -/
@[toIsoGraph]
theorem girth_johnson {n k : ℕ} (hk : 0 < k) (h : k + 2 ≤ n) : (johnson n k).girth = 3 := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine girth_eq_three_of_triangle
    (a := johnsonTri n k 0 (by omega)) (b := johnsonTri n k 1 (by omega))
    (c := johnsonTri n k 2 (by omega)) ?_ ?_ ?_ <;>
  · rw [johnson_adj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.add_sub_cancel]
    exact ⟨johnsonTri_ne (by omega), johnsonTri_inter (by omega)⟩

/-- **The complete bipartite graph `K_{m+2,n+2}` has girth four.** -/
@[toIsoGraph]
theorem girth_bipartite (m n : ℕ) : (bipartite (m + 2) (n + 2)).girth = 4 := by
  have hb : (bipartite (m + 2) (n + 2)).IsBipartite :=
    ⟨Sum.elim (fun _ ↦ false) (fun _ ↦ true), by rintro (a | b) (c | d) hadj <;> simp at hadj ⊢⟩
  refine girth_eq_four_of_square_of_isBipartite hb
    (a := (Sum.inl ⟨0, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (b := (Sum.inr ⟨0, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (c := (Sum.inl ⟨1, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (d := (Sum.inr ⟨1, by omega⟩ : Fin (m + 2) ⊕ Fin (n + 2)))
    (by rw [bipartite_adj_inl_inr]) (by rw [bipartite_adj_inr_inl])
    (by rw [bipartite_adj_inl_inr]) (by rw [bipartite_adj_inr_inl]) ?_ ?_
  · intro h
    have h2 : (⟨0, by omega⟩ : Fin (m + 2)) = ⟨1, by omega⟩ := Sum.inl.inj h
    simp at h2
  · intro h
    have h2 : (⟨0, by omega⟩ : Fin (n + 2)) = ⟨1, by omega⟩ := Sum.inr.inj h
    simp at h2

/-- Independence version of the greedy bound: `|V| ≤ (Δ + 1)·α`. -/
@[toIsoGraph V_le_maxDeg_add_one_mul_indepNum]
theorem card_le_maxDeg_add_one_mul_indepNum (G : CGraph) :
    FinEnum.card G.V ≤ (G.maxDeg + 1) * G.indepNum :=
  le_trans G.card_le_chromNum_mul_indepNum
    (Nat.mul_le_mul_right _ G.chromNum_le_maxDeg_add_one)

end

end CGraph

namespace IsoGraph

/-- **The double cover of a bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    complete 2 ⊗g G = G ⊕g G := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [← mk_canonicalize G] at *
  obtain ⟨c, hc⟩ := h
  exact tensorProduct_complete_two_of_colouring _ c hc

/-! Some non-isomorphisms between the families. -/

theorem empty_ne_complete (n : ℕ) : empty (n + 2) ≠ complete (n + 2) :=
  ne_of_E_ne (by rw [E_empty]; exact (E_complete_pos n).ne)

theorem path_ne_cycle (m n : ℕ) : path (m + 1) ≠ cycle (n + 3) :=
  ne_of_isTree (isTree_path m) (not_isTree_cycle n)

theorem complete_ne_cycle (n : ℕ) : complete (n + 4) ≠ cycle (n + 4) :=
  ne_of_degree_ne (degSequence_complete (n + 4)) (degSequence_cycle (n + 1)) (by omega) (by omega)

end IsoGraph

namespace CGraph

/-! The line graphs of the cycle, the path and the complete bipartite graph are all read off an
explicit bijection between the edges of the one graph and the vertices of the other, so they are
`def`s here and `@[toIsoGraph]` states them on the quotient. -/

/-- Successor mod `n + 3`, the "next vertex" map along the cycle. -/
private def cyc (n : ℕ) (i : Fin (n + 3)) : Fin (n + 3) :=
  ⟨(i.1 + 1) % (n + 3), Nat.mod_lt _ (by omega)⟩

private theorem cyc_val (n : ℕ) (i : Fin (n + 3)) : (cyc n i).1 = (i.1 + 1) % (n + 3) := rfl

private theorem cyc_ne (n : ℕ) (i : Fin (n + 3)) : cyc n i ≠ i := by
  intro h
  have h1 : (i.1 + 1) % (n + 3) = i.1 := congrArg Fin.val h
  have hi := i.2
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · rw [show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega

private theorem cyc_inj (n : ℕ) : Function.Injective (cyc n) := by
  intro i j h
  have h1 : (i.1 + 1) % (n + 3) = (j.1 + 1) % (n + 3) := congrArg Fin.val h
  have hi := i.2
  have hj := j.2
  refine Fin.ext ?_
  rcases Nat.lt_or_ge (i.1 + 1) (n + 3) with h2 | h2 <;>
    rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · rw [Nat.mod_eq_of_lt h2, show j.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [Nat.mod_eq_of_lt h3, show i.1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · omega

/-- Two steps along the cycle never return to where they started — this is the only place
`n ≥ 3` is used, and it is what rules out `L(C₂) = C₂`. -/
private theorem cyc_cyc_ne (n : ℕ) (j : Fin (n + 3)) : cyc n (cyc n j) ≠ j := by
  intro h
  have h1 : ((j.1 + 1) % (n + 3) + 1) % (n + 3) = j.1 := congrArg Fin.val h
  have hj := j.2
  rcases Nat.lt_or_ge (j.1 + 1) (n + 3) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h1
    rcases Nat.lt_or_ge (j.1 + 1 + 1) (n + 3) with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h1; omega
    · rw [show j.1 + 1 + 1 = n + 3 by omega, Nat.mod_self] at h1; omega
  · rw [show j.1 + 1 = n + 3 by omega, Nat.mod_self,
      Nat.mod_eq_of_lt (by omega : 0 + 1 < n + 3)] at h1
    omega

/-- Cycle adjacency in terms of `cyc`. -/
private theorem cycle_adj_cyc (n : ℕ) (i j : Fin (n + 3)) :
    (CGraph.cycle (n + 3)).Adj i j = decide (i ≠ j ∧ (cyc n i = j ∨ cyc n j = i)) := by
  have key : ∀ a b : Fin (n + 3), ((a.1 + 1) % (n + 3) == b.1) = decide (cyc n a = b) := by
    intro a b
    rw [Bool.beq_eq_decide_eq]
    exact decide_eq_decide.2 (by rw [Fin.ext_iff, cyc_val])
  show (decide (i ≠ j) && (((i.1 + 1) % (n + 3) == j.1) || ((j.1 + 1) % (n + 3) == i.1))) = _
  rw [key i j, key j i, Bool.decide_and, Bool.decide_or]

private theorem cyc_adj (n : ℕ) (i : Fin (n + 3)) :
    s(i, cyc n i) ∈ (CGraph.cycle (n + 3)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, cycle_adj_cyc]
  exact decide_eq_true ⟨Ne.symm (cyc_ne n i), Or.inl rfl⟩

/-- The edge of `Cₙ` running from `i` to its successor.  Every edge is of this form, so this is
the bijection `Fin n ≃ E(Cₙ)` witnessing `L(Cₙ) = Cₙ`. -/
private def cycEdge (n : ℕ) (i : Fin (n + 3)) : (CGraph.lineGraph (CGraph.cycle (n + 3))).V :=
  ⟨s(i, cyc n i), cyc_adj n i⟩

private theorem mem_cycEdge (n : ℕ) (v i : Fin (n + 3)) :
    v ∈ ((cycEdge n i).1 : Sym2 (Fin (n + 3))) ↔ v = i ∨ v = cyc n i := Sym2.mem_iff

private theorem cycEdge_inj (n : ℕ) : Function.Injective (cycEdge n) := by
  intro i j h
  have h1 : s(i, cyc n i) = s(j, cyc n j) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact h2
  · exact absurd (h2 ▸ h3) (cyc_cyc_ne n j)

/-- **The cycle is its own line graph**, for `n ≥ 3`.  The edges of `Cₙ` are the consecutive pairs
`{i, i+1}`, and two of them share a vertex exactly when their indices are consecutive.  Injectivity
is where `n ≥ 3` enters: for `n = 2` the two "edges" `{0, 1}` and `{1, 0}` coincide. -/
@[toIsoGraph simp lineGraph_cycle]
def lineGraphCycle (n : ℕ) : lineGraph (cycle (n + 3)) ≃cg cycle (n + 3) := by
  have hcard : FinEnum.card (Fin (n + 3))
      = FinEnum.card (CGraph.lineGraph (CGraph.cycle (n + 3))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_cycle, FinEnum.card_fin']
  have hbij : Function.Bijective (cycEdge n) :=
    FinEnum.bijective_iff_injective_and_card _ |>.2 ⟨cycEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin (n + 3),
      (CGraph.lineGraph (CGraph.cycle (n + 3))).Adj (cycEdge n i) (cycEdge n j)
        = (CGraph.cycle (n + 3)).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, cycle_adj_cyc]
    by_cases hij : i = j
    · subst hij; simp
    · rw [decide_eq_true (show cycEdge n i ≠ cycEdge n j from fun h ↦ hij (cycEdge_inj n h)),
        Bool.true_and, Bool.decide_and, decide_eq_true hij, Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_cycEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
        · exact absurd (h1.symm.trans h2) hij
        · exact Or.inr (h2.symm.trans h1)
        · exact Or.inl (h1.symm.trans h2)
        · exact absurd (cyc_inj n (h1.symm.trans h2)) hij
      · rintro (h | h)
        · exact ⟨j, (mem_cycEdge n j i).2 (Or.inr h.symm), (mem_cycEdge n j j).2 (Or.inl rfl)⟩
        · exact ⟨i, (mem_cycEdge n i i).2 (Or.inl rfl), (mem_cycEdge n i j).2 (Or.inr h.symm)⟩
  exact (isoOfAdj (equivOfBijective hbij) hadj).symm

/-- Path adjacency at the level of the underlying naturals.  Note that `i ≠ j` is implied by
either disjunct, so it drops out. -/
private theorem path_adj_nat (n : ℕ) (i j : Fin n) :
    (CGraph.path n).Adj i j = decide (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  show (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) = _
  by_cases h : i = j
  · subst h; simp
  · rw [decide_eq_true h, Bool.true_and, Bool.beq_eq_decide_eq, Bool.beq_eq_decide_eq,
      ← Bool.decide_or]

private theorem pathEdge_adj (n : ℕ) (i : Fin n) :
    s(i.castSucc, i.succ) ∈ (CGraph.path (n + 1)).toSimple.edgeSet := by
  rw [SimpleGraph.mem_edgeSet, CGraph.toSimple_adj, path_adj_nat]
  exact decide_eq_true (Or.inl (by simp))

/-- The `i`-th edge of the path `0 — 1 — ⋯ — n`. -/
private def pathEdge (n : ℕ) (i : Fin n) : (CGraph.lineGraph (CGraph.path (n + 1))).V :=
  ⟨s(i.castSucc, i.succ), pathEdge_adj n i⟩

private theorem mem_pathEdge (n : ℕ) (v : Fin (n + 1)) (i : Fin n) :
    v ∈ ((pathEdge n i).1 : Sym2 (Fin (n + 1))) ↔ v = i.castSucc ∨ v = i.succ := Sym2.mem_iff

private theorem pathEdge_inj (n : ℕ) : Function.Injective (pathEdge n) := by
  intro i j h
  have h1 : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h1 with ⟨h2, _⟩ | ⟨h2, h3⟩
  · exact Fin.ext (by simpa using congrArg Fin.val h2)
  · have hv2 := congrArg Fin.val h2
    have hv3 := congrArg Fin.val h3
    simp only [Fin.val_castSucc, Fin.val_succ] at hv2 hv3
    omega

/-- **The line graph of a path is the shorter path**: `L(Pₙ₊₁) = Pₙ`.  Unlike the cycle this needs
no size hypothesis — `L(P₁) = P₀` is the empty graph. -/
@[toIsoGraph simp lineGraph_path]
def lineGraphPath (n : ℕ) : lineGraph (path (n + 1)) ≃cg path n := by
  have hcard : FinEnum.card (Fin n)
      = FinEnum.card (CGraph.lineGraph (CGraph.path (n + 1))).V := by
    rw [CGraph.card_lineGraph, CGraph.E_path, FinEnum.card_fin']
  have hbij : Function.Bijective (pathEdge n) :=
    FinEnum.bijective_iff_injective_and_card _ |>.2 ⟨pathEdge_inj n, hcard⟩
  have hadj : ∀ i j : Fin n,
      (CGraph.lineGraph (CGraph.path (n + 1))).Adj (pathEdge n i) (pathEdge n j)
        = (CGraph.path n).Adj i j := by
    intro i j
    rw [CGraph.lineGraph_adj, path_adj_nat]
    by_cases hij : i = j
    · subst hij; simp
    · have hval : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
      rw [decide_eq_true (show pathEdge n i ≠ pathEdge n j from fun h ↦ hij (pathEdge_inj n h)),
        Bool.true_and]
      refine decide_eq_decide.2 ⟨?_, ?_⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [mem_pathEdge] at hv1 hv2
        rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2 <;>
          · have h3 := congrArg Fin.val (h1.symm.trans h2)
            simp only [Fin.val_castSucc, Fin.val_succ] at h3
            omega
      · rintro (h | h)
        · exact ⟨i.succ, (mem_pathEdge n _ i).2 (Or.inr rfl),
            (mem_pathEdge n _ j).2 (Or.inl (Fin.ext (by simpa using h)))⟩
        · exact ⟨i.castSucc, (mem_pathEdge n _ i).2 (Or.inl rfl),
            (mem_pathEdge n _ j).2 (Or.inr (Fin.ext (by simpa using h.symm)))⟩
  exact (isoOfAdj (equivOfBijective hbij) hadj).symm

end CGraph

namespace IsoGraph

/-- **Nordhaus–Gaddum, product form**: `|V| ≤ χ(G)·χ(Gᶜ)`, since an independent set of `G` is a
clique of `Gᶜ`. -/
theorem V_le_chromNum_mul_chromNum_compl (G : IsoGraph) :
    G.V ≤ G.chromNum * Gᶜ.chromNum :=
  le_trans (V_le_chromNum_mul_indepNum G)
    (Nat.mul_le_mul_left _ (by rw [← cliqueNum_compl]; exact cliqueNum_le_chromNum _))

/-- **Nordhaus–Gaddum, sum form**: `4·|V| ≤ (χ(G) + χ(Gᶜ))²`, i.e. `χ(G) + χ(Gᶜ) ≥ 2√|V|`.
This is the product form together with `4ab ≤ (a + b)²`. -/
theorem four_mul_V_le_chromNum_add_chromNum_compl_sq (G : IsoGraph) :
    4 * G.V ≤ (G.chromNum + Gᶜ.chromNum) ^ 2 := by
  have h := V_le_chromNum_mul_chromNum_compl G
  nlinarith [sq_nonneg (G.chromNum - Gᶜ.chromNum : ℤ)]

theorem girth_eq_three_of_V_sq_lt (G : IsoGraph) (h : G.V ^ 2 < 4 * G.E) : G.girth = 3 :=
  girth_eq_three_iff.2 (G.three_le_cliqueNum_of_V_sq_lt h)

/-- Mantel's bound applies to every graph of girth at least four, and to every bipartite graph. -/
theorem four_mul_E_le_V_sq_of_girth_ne_three (G : IsoGraph) (h : G.girth ≠ 3) :
    4 * G.E ≤ G.V ^ 2 := by
  refine G.four_mul_E_le_V_sq ?_
  by_contra hcon
  exact h (girth_eq_three_iff.2 (by omega))

theorem four_mul_E_le_V_sq_of_isBipartite (G : IsoGraph) (h : IsBipartite G) :
    4 * G.E ≤ G.V ^ 2 :=
  G.four_mul_E_le_V_sq (cliqueNum_le_two_of_isBipartite h)

/-! ### Consequences of regularity -/

/-- A `k`-regular graph on a nonempty vertex set has more than `k` vertices. -/
theorem IsRegularWith.lt_V {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hV : 0 < G.V) :
    k < G.V := by
  rw [← h.maxDeg_eq hV]
  exact maxDeg_lt_V hV

/-- The degree of a regular graph is determined by the graph. -/
theorem IsRegularWith.unique {G : IsoGraph} {k l : ℕ} (hk : G.IsRegularWith k)
    (hl : G.IsRegularWith l) (hV : 0 < G.V) : k = l := by
  rw [← hk.maxDeg_eq hV, ← hl.maxDeg_eq hV]

/-- The handshake parity constraint: an odd-degree regular graph has an even number of
vertices.  There is no `3`-regular graph on five vertices. -/
theorem IsRegularWith.two_dvd_V {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) (hk : ¬ 2 ∣ k) :
    2 ∣ G.V := by
  have h2 : 2 ∣ G.V * k := ⟨G.E, h.two_mul_E.symm⟩
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 hk

/-- Greedy colouring on a regular graph. -/
theorem IsRegularWith.chromNum_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    G.chromNum ≤ k + 1 := by
  rcases Nat.eq_zero_or_pos G.V with hV | hV
  · have := G.chromNum_le_V
    omega
  · rw [← h.maxDeg_eq hV]
    exact G.chromNum_le_maxDeg_add_one

/-- A dominating set of a `k`-regular graph covers at most `k + 1` vertices per element. -/
theorem IsRegularWith.V_le_domNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.V ≤ G.domNum * (k + 1) :=
  le_domNum_of_regular (h.maxDeg_eq hV)

/-- The greedy bound `α ≥ n / (k + 1)` for a `k`-regular graph. -/
theorem IsRegularWith.V_le_indepNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.V ≤ G.indepNum * (k + 1) := by
  rw [← h.maxDeg_eq hV]
  exact G.V_le_indepNum_mul_maxDeg_add_one

theorem IsRegularWith.domNum_add_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.domNum + k ≤ G.V := by
  rw [← h.maxDeg_eq hV]
  exact G.domNum_add_maxDeg_le_V

/-- Each vertex of a cover of a `k`-regular graph is on `k` edges. -/
theorem IsRegularWith.E_le_coverNum_mul {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.E ≤ G.coverNum * k := by
  rw [← h.maxDeg_eq hV]
  exact G.E_le_coverNum_mul_maxDeg

theorem IsRegularWith.E_add_indepNum_mul_le {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k)
    (hV : 0 < G.V) : G.E + G.indepNum * k ≤ G.V * k := by
  rw [← h.maxDeg_eq hV]
  exact G.indepNum_mul_maxDeg_le

/-- The complement of a `k`-regular graph is `(n - 1 - k)`-regular, so its edge count is
also forced. -/
theorem IsRegularWith.two_mul_E_compl {G : IsoGraph} {k : ℕ} (h : G.IsRegularWith k) :
    2 * Gᶜ.E = G.V * (G.V - 1 - k) := by
  have h2 := h.compl.two_mul_E
  rwa [V_compl] at h2

/-- A `0`-regular graph has no edges at all. -/
theorem IsRegularWith.eq_empty {G : IsoGraph} (h : G.IsRegularWith 0) : G = empty G.V := by
  induction G using Quotient.inductionOn with | _ g =>
  rw [← mk_canonicalize g] at h ⊢
  rw [isRegularWith_mk] at h
  rw [V_mk]
  exact mk_eq_empty (CGraph.adj_eq_false_of_isRegularWith_zero h)

/-- Every colour class of an edge colouring is a matching, so `|E| ≤ χ' ν`. -/
theorem E_le_edgeChromNum_mul_matchNum (G : IsoGraph) :
    G.E ≤ G.edgeChromNum * G.matchNum := by
  have h := V_le_chromNum_mul_indepNum (lineGraph G)
  rw [edgeChromNum_eq, matchNum_eq]
  rwa [V_lineGraph] at h

/-- Combining `|E| ≤ χ' ν` with `χ' ≤ 2Δ - 1`. -/
theorem E_le_two_mul_maxDeg_sub_one_mul_matchNum (G : IsoGraph) :
    G.E ≤ (2 * G.maxDeg - 1) * G.matchNum := by
  refine le_trans G.E_le_edgeChromNum_mul_matchNum ?_
  exact Nat.mul_le_mul_right _ G.edgeChromNum_le_two_mul_maxDeg_sub_one

/-- `n ≤ θ ω`, the complement of `n ≤ χ α`: each of the `θ` cliques has at most `ω` vertices. -/
theorem V_le_cliqueCoverNum_mul_cliqueNum (G : IsoGraph) :
    G.V ≤ G.cliqueCoverNum * G.cliqueNum := by
  have h := V_le_chromNum_mul_indepNum Gᶜ
  rw [cliqueCoverNum_eq]
  rwa [V_compl, indepNum_compl] at h

/-! ### Nordhaus–Gaddum for the clique cover number

Every bound relating a graph to its complement can be read as a bound relating the chromatic
number to the clique cover number. -/

/-- `n ≤ χ θ`: the `χ` colour classes are independent sets, so `θ` of them cover `G`. -/
theorem V_le_chromNum_mul_cliqueCoverNum (G : IsoGraph) :
    G.V ≤ G.chromNum * G.cliqueCoverNum := by
  rw [cliqueCoverNum_eq]; exact G.V_le_chromNum_mul_chromNum_compl

theorem four_mul_V_le_chromNum_add_cliqueCoverNum_sq (G : IsoGraph) :
    4 * G.V ≤ (G.chromNum + G.cliqueCoverNum) ^ 2 := by
  rw [cliqueCoverNum_eq]; exact G.four_mul_V_le_chromNum_add_chromNum_compl_sq

theorem V_le_two_mul_coverNum_of_two_mul_matchNum_eq {G : IsoGraph} (h : 2 * G.matchNum = G.V) :
    G.V ≤ 2 * G.coverNum := by
  have h1 := G.matchNum_le_coverNum
  omega

/-- Consequently a long cycle has girth at least four. -/
theorem four_le_girth_cycle (n : ℕ) : 4 ≤ (cycle (n + 4)).girth :=
  four_le_girth_of_cliqueNum (by rw [cliqueNum_cycle]) (not_isAcyclic_cycle (n + 1))

/-! ### The matching number of a complete graph -/

/-- **The matching number of a complete graph**: `ν(Kₙ) = ⌊n/2⌋`.  The upper bound is
`2ν ≤ |V|`; for the lower bound, the vertices missed by a maximum matching are independent,
so `|V| ≤ α + 2ν = 1 + 2ν`. -/
@[simp] theorem matchNum_complete (n : ℕ) : (complete n).matchNum = n / 2 := by
  have h1 := matchNum_complete_le n
  have h2 := V_le_indepNum_add_two_mul_matchNum (complete n)
  rw [V_complete, indepNum_complete] at h2
  omega

/-- A complete graph of even order has a perfect matching. -/
theorem two_mul_matchNum_complete_two_mul (m : ℕ) :
    2 * (complete (2 * m)).matchNum = (complete (2 * m)).V := by
  rw [matchNum_complete, V_complete]
  omega

/-- **`K_{2m+3}` is a class-two graph**: `χ'(K_{2m+3}) ≥ 2m + 3 = Δ + 1`, because each of the
`(m+1)(2m+3)` edges lies in a colour class of size at most `ν = m + 1`.  (Vizing's theorem says
`Δ + 1` colours always suffice, so this is exactly the edge chromatic number.) -/
theorem le_edgeChromNum_complete_odd (m : ℕ) :
    2 * m + 3 ≤ (complete (2 * m + 3)).edgeChromNum := by
  have hch : (2 * m + 3).choose 2 = (m + 1) * (2 * m + 3) := by
    rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring, choose_two_two_mul_add_one]
  have h := E_le_edgeChromNum_mul_matchNum (complete (2 * m + 3))
  rw [E_complete, matchNum_complete, hch, show (2 * m + 3) / 2 = m + 1 from by omega,
    Nat.mul_comm (m + 1) (2 * m + 3)] at h
  exact Nat.le_of_mul_le_mul_right h m.succ_pos

/-- Complete graphs of odd order `≥ 3` need more than `Δ` colours on their edges. -/
theorem maxDeg_lt_edgeChromNum_complete_odd (m : ℕ) :
    maxDeg (complete (2 * m + 3)) < (complete (2 * m + 3)).edgeChromNum := by
  have h := le_edgeChromNum_complete_odd m
  rw [maxDeg_complete]
  omega

@[simp] theorem minDeg_eq_maxDeg_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : G.minDeg = G.maxDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).maxDeg_eq hV |>.symm

/-- **The handshake lemma for a vertex-transitive graph**: `2|E| = |V| · δ`. -/
theorem two_mul_E_of_isVertexTransitive {G : IsoGraph} (hV : 0 < G.V) (h : IsVertexTransitive G) :
    2 * G.E = G.V * G.minDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).two_mul_E

theorem degSequence_of_isVertexTransitive_minDeg {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) : degSequence G = List.replicate G.V G.minDeg :=
  (isRegularWith_minDeg_of_isVertexTransitive hV h).degSequence

/-- A vertex-transitive graph on an odd number of vertices has even degree: `|V| · δ` is even. -/
theorem even_minDeg_of_isVertexTransitive_of_odd {G : IsoGraph} (hV : 0 < G.V)
    (h : IsVertexTransitive G) (hodd : G.V % 2 = 1) : G.minDeg % 2 = 0 := by
  have h2 := two_mul_E_of_isVertexTransitive hV h
  rcases Nat.even_mul.1 (⟨G.E, by omega⟩ : Even (G.V * G.minDeg)) with he | he
  · exact absurd (Nat.even_iff.1 he) (by omega)
  · exact Nat.even_iff.1 he

/-- **A regular graph of odd order is class two**: each colour class misses a vertex, so `Δ`
colours cover fewer than `E` edges. -/
theorem maxDeg_lt_edgeChromNum_of_isRegularWith_odd {G : IsoGraph} {k : ℕ}
    (h : G.IsRegularWith k) (hk : 0 < k) (hodd : G.V % 2 = 1) : maxDeg G < G.edgeChromNum := by
  have hV : 0 < G.V := by omega
  rw [h.maxDeg_eq hV]
  -- Key facts:
  -- 2 * E = V * k
  -- E ≤ edgeChromNum * matchNum
  -- 2 * matchNum ≤ V
  -- V % 2 = 1
  -- From these: V * k ≤ 2 * edgeChromNum * matchNum, and matchNum ≤ (V-1)/2
  -- So V * k ≤ edgeChromNum * (V-1), so edgeChromNum > k when k > 0 and V odd.
  have h2E := h.two_mul_E
  have hE_le := G.E_le_edgeChromNum_mul_matchNum
  have hmatch_bound := G.two_mul_matchNum_le_V
  -- matchNum ≤ (V - 1) / 2
  have hm_le : G.matchNum ≤ (G.V - 1) / 2 := by
    omega
  -- V * k ≤ edgeChromNum * (V - 1)
  have hm_le2 : 2 * G.matchNum ≤ G.V - 1 := by omega
  have hV1 : G.V - 1 ≥ 0 := Nat.zero_le _
  -- From 2*E = V*k and E ≤ edgeChromNum * matchNum:
  -- V * k ≤ 2 * (edgeChromNum * matchNum)
  -- With 2*matchNum ≤ V-1:
  -- V * k ≤ edgeChromNum * (V - 1)
  have hVk : G.V * k ≤ G.edgeChromNum * (G.V - 1) := by nlinarith
  -- If edgeChromNum ≤ k, contradiction (for k > 0, G.V ≥ 1, V odd so V-1 < V)
  by_contra hle
  push Not at hle
  have : G.V * k ≤ k * (G.V - 1) := by nlinarith
  nlinarith [Nat.sub_add_cancel hV]

/-! ### Vertex-transitive graphs of odd order are class two -/

/-- **A vertex-transitive graph of odd order with an edge is class two.**  Vertex-transitivity
gives regularity, and a regular graph of odd order needs more than `Δ` edge colours because each
colour class is a matching and so misses a vertex. -/
theorem maxDeg_lt_edgeChromNum_of_isVertexTransitive_odd {G : IsoGraph}
    (h : IsVertexTransitive G) (hodd : G.V % 2 = 1) (hE : 0 < G.E) :
    maxDeg G < G.edgeChromNum := by
  have hV : 0 < G.V := by omega
  refine maxDeg_lt_edgeChromNum_of_isRegularWith_odd
    (isRegularWith_minDeg_of_isVertexTransitive hV h) ?_ hodd
  by_contra hk
  have hk0 : G.minDeg = 0 := by omega
  have h2 := two_mul_E_of_isVertexTransitive hV h
  rw [hk0, Nat.mul_zero] at h2
  omega

@[simp] theorem girth_join_cycle (m n : ℕ) :
    (cycle (m + 4) ∇g cycle (n + 4)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_cycle]; omega)

theorem diameter_join_cycle (m n : ℕ) :
    (cycle (m + 4) ∇g cycle (n + 4)).diameter = 2 := by
  have h : (m + 4).choose 2 = (m + 4) * (m + 3) / 2 := by
    rw [Nat.choose_two_right, show m + 4 - 1 = m + 3 by omega]
  have h2 : m + 5 ≤ (m + 4) * (m + 3) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 4) * (m + 3) = m * m + 7 * m + 12 := by ring
    omega
  refine diameter_join_left (by rw [V_cycle]; omega) ?_
  rw [E_cycle, V_cycle, h]
  omega

end IsoGraph
