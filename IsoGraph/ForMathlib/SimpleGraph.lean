import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Common

/-!
# Lemmas about `SimpleGraph`

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

open Fintype

/-! ## Isomorphism-invariance lemmas for `SimpleGraph` -/

namespace SimpleGraph.Iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- The image of an `n`-clique under an isomorphism is an `n`-clique. -/
theorem isNClique_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNClique n s) :
    G'.IsNClique n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact f.map_adj_iff.2 (h.1 hx hy fun e ↦ hab (by rw [e]))

/-- The image of an independent `n`-set under an isomorphism is an independent `n`-set. -/
theorem isNIndepSet_map (f : G ≃g G') {n : ℕ} {s : Finset V} (h : G.IsNIndepSet n s) :
    G'.IsNIndepSet n (s.map ⟨f, f.injective⟩) := by
  refine ⟨?_, by simpa using h.2⟩
  rintro a ha b hb hab
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at ha hb
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact fun hadj ↦ h.1 hx hy (fun e ↦ hab (by rw [e])) (f.map_adj_iff.1 hadj)

/-- The `n`-cliques of two isomorphic graphs are in bijection, so there are equally many. -/
theorem cliqueSet_ncard_eq (f : G ≃g G') (n : ℕ) :
    (G.cliqueSet n).ncard = (G'.cliqueSet n).ncard := by
  have himg : G'.cliqueSet n
      = (fun s : Finset V ↦ s.map ⟨f, f.injective⟩) '' G.cliqueSet n := by
    ext t
    simp only [Set.mem_image, mem_cliqueSet_iff]
    constructor
    · intro ht
      refine ⟨t.map ⟨f.symm, f.symm.injective⟩, isNClique_map f.symm ht, ?_⟩
      rw [Finset.map_map]
      ext x
      simp
    · rintro ⟨s, hs, rfl⟩
      exact isNClique_map f hs
  rw [himg, Set.ncard_image_of_injective _ (Finset.map_injective _)]

/-- The independent `n`-sets of two isomorphic graphs are in bijection, so there are equally
many. -/
theorem indepSetSet_ncard_eq (f : G ≃g G') (n : ℕ) :
    (G.indepSetSet n).ncard = (G'.indepSetSet n).ncard := by
  have himg : G'.indepSetSet n
      = (fun s : Finset V ↦ s.map ⟨f, f.injective⟩) '' G.indepSetSet n := by
    ext t
    simp only [Set.mem_image, mem_indepSetSet_iff]
    constructor
    · intro ht
      refine ⟨t.map ⟨f.symm, f.symm.injective⟩, isNIndepSet_map f.symm ht, ?_⟩
      rw [Finset.map_map]
      ext x
      simp
    · rintro ⟨s, hs, rfl⟩
      exact isNIndepSet_map f hs
  rw [himg, Set.ncard_image_of_injective _ (Finset.map_injective _)]

/-- Isomorphic graphs have equally many connected components. -/
theorem numComponents_eq (f : G ≃g G') :
    Nat.card G.ConnectedComponent = Nat.card G'.ConnectedComponent :=
  Nat.card_congr f.connectedComponentEquiv

/-- Conjugating by an isomorphism is a bijection between the automorphism groups. -/
def autEquiv (f : G ≃g G') : (G ≃g G) ≃ (G' ≃g G') where
  toFun a := (f.symm.trans a).trans f
  invFun b := (f.trans b).trans f.symm
  left_inv a := by ext v; simp
  right_inv b := by ext v; simp

/-- Isomorphic graphs have equally many automorphisms. -/
theorem autCount_eq (f : G ≃g G') : Nat.card (G ≃g G) = Nat.card (G' ≃g G') :=
  Nat.card_congr (autEquiv f)

theorem cliqueNum_eq (f : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNClique_map f.symm hs⟩⟩

theorem indepNum_eq (f : G ≃g G') : G.indepNum = G'.indepNum := by
  unfold SimpleGraph.indepNum
  congr 1
  ext n
  exact ⟨fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f hs⟩, fun ⟨_, hs⟩ ↦ ⟨_, isNIndepSet_map f.symm hs⟩⟩

/-- Isomorphic graphs have the same multiset of degrees. -/
theorem degrees_eq [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]
    (f : G ≃g G') :
    (Finset.univ.val.map fun v ↦ G.degree v) = Finset.univ.val.map fun w ↦ G'.degree w := by
  conv_rhs => rw [← Finset.map_univ_equiv f.toEquiv]
  rw [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun v _ ↦ ?_
  exact (f.degree_eq v).symm

/-- Pushing a walk forward along an isomorphism can only shorten the extended distance; applying
this to `f` and to `f.symm` gives `edist_eq`. -/
private theorem edist_le_of_iso (f : G ≃g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  rw [SimpleGraph.edist_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨w, rfl⟩
  simpa using SimpleGraph.edist_le (w.map f.toHom)

/-- Isomorphisms preserve the extended distance. -/
theorem edist_eq (f : G ≃g G') (u v : V) : G.edist u v = G'.edist (f u) (f v) :=
  le_antisymm (by simpa using edist_le_of_iso f.symm (f u) (f v)) (edist_le_of_iso f u v)

/-- Isomorphic graphs have the same extended diameter. -/
theorem ediam_eq (f : G ≃g G') : G.ediam = G'.ediam := by
  refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
    (SimpleGraph.ediam_le_of_edist_le fun u v ↦ ?_)
  · rw [edist_eq f]; exact SimpleGraph.edist_le_ediam
  · rw [edist_eq f.symm]; exact SimpleGraph.edist_le_ediam

/-- Isomorphic graphs have the same diameter. -/
theorem diam_eq (f : G ≃g G') : G.diam = G'.diam :=
  congrArg ENat.toNat (ediam_eq f)

/-- Isomorphisms preserve eccentricity. -/
theorem eccent_eq (f : G ≃g G') (u : V) : G.eccent u = G'.eccent (f u) := by
  unfold SimpleGraph.eccent
  refine le_antisymm (iSup_le fun v ↦ ?_) (iSup_le fun w ↦ ?_)
  · rw [edist_eq f]
    exact le_iSup (G'.edist (f u)) (f v)
  · have hw : G'.edist (f u) w = G.edist u (f.symm w) := by
      rw [edist_eq f u (f.symm w), f.apply_symm_apply]
    rw [hw]
    exact le_iSup (G.edist u) (f.symm w)

/-- Isomorphic graphs have the same radius. -/
theorem radius_eq (f : G ≃g G') : G.radius = G'.radius := by
  unfold SimpleGraph.radius
  refine le_antisymm (le_iInf fun w ↦ ?_) (le_iInf fun u ↦ ?_)
  · have hw : G'.eccent w = G.eccent (f.symm w) := by
      rw [eccent_eq f, f.apply_symm_apply]
    rw [hw]
    exact iInf_le _ (f.symm w)
  · rw [eccent_eq f]
    exact iInf_le _ (f u)

/-- An isomorphism restricts to a bijection between common neighbourhoods. -/
def commonNeighborsEquiv (f : G ≃g G') (v w : V) :
    G.commonNeighbors v w ≃ G'.commonNeighbors (f v) (f w) :=
  Equiv.subtypeEquiv f.toEquiv fun x ↦ by
    simp [SimpleGraph.mem_commonNeighbors, f.map_adj_iff]

theorem card_commonNeighbors_eq [Fintype V] [Fintype W] [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (f : G ≃g G') (v w : V) :
    Fintype.card (G.commonNeighbors v w) = Fintype.card (G'.commonNeighbors (f v) (f w)) :=
  Fintype.card_congr (commonNeighborsEquiv f v w)

/-- Isomorphic graphs have the same chromatic number. -/
theorem chromaticNumber_eq (f : G ≃g G') : G.chromaticNumber = G'.chromaticNumber :=
  le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

section StronglyRegular

variable [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj] {n k ℓ μ : ℕ}

/-- Strong regularity transfers along an isomorphism. -/
theorem isSRGWith_of_iso (f : G ≃g G') (h : G.IsSRGWith n k ℓ μ) : G'.IsSRGWith n k ℓ μ where
  card := by rw [← Fintype.card_congr f.toEquiv]; exact h.card
  regular v := by
    obtain ⟨u, rfl⟩ := f.surjective v
    rw [f.degree_eq u]
    exact h.regular u
  of_adj v w hvw := by
    obtain ⟨u, rfl⟩ := f.surjective v
    obtain ⟨t, rfl⟩ := f.surjective w
    rw [← card_commonNeighbors_eq f]
    exact h.of_adj u t (f.map_adj_iff.1 hvw)
  of_not_adj := by
    intro v w hne hvw
    obtain ⟨u, rfl⟩ := f.surjective v
    obtain ⟨t, rfl⟩ := f.surjective w
    rw [← card_commonNeighbors_eq f]
    exact h.of_not_adj (fun e ↦ hne (congrArg f e)) fun hut ↦ hvw (f.map_adj_iff.2 hut)

/-- Isomorphic graphs are strongly regular with the same parameters. -/
theorem isSRGWith_iff (f : G ≃g G') : G.IsSRGWith n k ℓ μ ↔ G'.IsSRGWith n k ℓ μ :=
  ⟨isSRGWith_of_iso f, isSRGWith_of_iso f.symm⟩

/-- Regularity transfers along an isomorphism: it preserves degrees and is surjective. -/
theorem isRegularOfDegree_of_iso (f : G ≃g G') (h : G.IsRegularOfDegree k) :
    G'.IsRegularOfDegree k := fun v ↦ by
  obtain ⟨u, rfl⟩ := f.surjective v
  rw [f.degree_eq u]
  exact h u

/-- Isomorphic graphs are regular of the same degree. -/
theorem isRegularOfDegree_iff (f : G ≃g G') : G.IsRegularOfDegree k ↔ G'.IsRegularOfDegree k :=
  ⟨isRegularOfDegree_of_iso f, isRegularOfDegree_of_iso f.symm⟩

end StronglyRegular

/-- **Girth is an isomorphism invariant**: an isomorphism carries cycles to cycles of the same
length, in both directions, so the infimum of cycle lengths is the same on both sides. -/
theorem egirth_eq (f : G ≃g G') : G.egirth = G'.egirth := by
  refine le_antisymm (le_egirth.2 fun a w hw ↦ ?_) (le_egirth.2 fun a w hw ↦ ?_)
  · have h := egirth_le_length (hw.map (f := f.symm.toHom) f.symm.injective)
    rwa [Walk.length_map] at h
  · have h := egirth_le_length (hw.map (f := f.toHom) f.injective)
    rwa [Walk.length_map] at h

theorem girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  rw [girth, girth, f.egirth_eq]

end SimpleGraph.Iso

theorem getLastD_support {V : Type} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (x : V) :
    p.support.getLastD x = v := by
  induction p generalizing x with
  | nil => rfl
  | cons h q ih => rw [SimpleGraph.Walk.support_cons, List.getLastD_cons]; exact ih _

/-- In a path of length at least two, the two endpoints are not joined by an edge of the path. -/
theorem not_mem_edges_of_isPath {V : Type} {G : SimpleGraph V} {u v : V} :
    ∀ (p : G.Walk u v), p.IsPath → 2 ≤ p.length → s(u, v) ∉ p.edges := by
  intro p
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    intro hp hlen hmem
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · have hbc : b = c := by
        rcases Sym2.eq_iff.1 heq with ⟨_, hbc⟩ | ⟨hac, _⟩
        · exact hbc.symm
        · exact absurd hac h.ne
      subst hbc
      rw [SimpleGraph.Walk.isPath_iff_eq_nil] at hp
      simp [hp.1] at hlen
    · exact hp.2 (q.fst_mem_support_of_mem_edges hmem)

/-- The eccentricity of a vertex of a box product is the sum of the eccentricities of its
coordinates: a farthest vertex can be chosen coordinatewise. -/
theorem eccent_boxProd {α β : Type} [Fintype α] [Fintype β]
    (S : SimpleGraph α) (T : SimpleGraph β) (p : α × β) :
    (S.boxProd T).eccent p = S.eccent p.1 + T.eccent p.2 := by
  refine le_antisymm ((SimpleGraph.eccent_le_iff _ _).2 fun q ↦ ?_) ?_
  · rw [SimpleGraph.edist_boxProd]
    exact add_le_add SimpleGraph.edist_le_eccent SimpleGraph.edist_le_eccent
  · obtain ⟨x, hx⟩ := S.exists_edist_eq_eccent_of_finite p.1
    obtain ⟨y, hy⟩ := T.exists_edist_eq_eccent_of_finite p.2
    rw [← hx, ← hy, ← SimpleGraph.edist_boxProd (x := p) (y := (x, y))]
    exact SimpleGraph.edist_le_eccent

/-- **The radius of a box product is the sum of the radii**: a central vertex can be chosen
coordinatewise. -/
theorem radius_boxProd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : SimpleGraph α) (T : SimpleGraph β) :
    (S.boxProd T).radius = S.radius + T.radius := by
  refine le_antisymm ?_ ?_
  · obtain ⟨a, ha⟩ := S.exists_eccent_eq_radius
    obtain ⟨b, hb⟩ := T.exists_eccent_eq_radius
    rw [← ha, ← hb, ← eccent_boxProd S T (a, b)]
    exact SimpleGraph.radius_le_eccent
  · obtain ⟨p, hp⟩ := (S.boxProd T).exists_eccent_eq_radius
    rw [← hp, eccent_boxProd]
    exact add_le_add SimpleGraph.radius_le_eccent SimpleGraph.radius_le_eccent

/-- Distances in a box product add, so extremal distances do too: the box product of two nonempty
finite graphs has the sum of the two extended diameters. -/
theorem ediam_boxProd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (S : SimpleGraph α) (T : SimpleGraph β) :
    (S.boxProd T).ediam = S.ediam + T.ediam := by
  refine le_antisymm (SimpleGraph.ediam_le_of_edist_le fun p q ↦ ?_) ?_
  · rw [SimpleGraph.edist_boxProd]
    exact add_le_add SimpleGraph.edist_le_ediam SimpleGraph.edist_le_ediam
  · obtain ⟨a, a', ha⟩ := SimpleGraph.exists_edist_eq_ediam_of_finite (G := S)
    obtain ⟨b, b', hb⟩ := SimpleGraph.exists_edist_eq_ediam_of_finite (G := T)
    rw [← ha, ← hb, ← SimpleGraph.edist_boxProd (x := (a, b)) (y := (a', b'))]
    exact SimpleGraph.edist_le_ediam
