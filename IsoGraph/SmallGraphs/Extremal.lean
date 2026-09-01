import IsoGraph.SmallGraphs.Values

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Extremal graphs, and the automorphisms of the bipartite families

The extremal bounds — maximum and minimum degree, greedy colouring, Nordhaus–Gaddum — applied to the
named families, and the automorphism counts of the complete bipartite graphs and the wheel.
-/

namespace CGraph

section
variable {G H : CGraph}

/-- **The Petersen graph has girth five**: it is strongly regular with `ℓ = 0` and `μ = 1`, so it
has neither a triangle nor a square, and its outer five-cycle realises the bound. -/
theorem girth_kneser_five_two : (kneser 5 2).girth = 5 := by
  have hpent := girth_le_five_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide))
  have hnac := not_isAcyclic_of_pentagon (G := kneser 5 2)
    (a := (⟨{0, 1}, by decide⟩ : {s : Finset (Fin 5) // s.card = 2}))
    (b := ⟨{2, 3}, by decide⟩) (c := ⟨{4, 0}, by decide⟩)
    (d := ⟨{1, 2}, by decide⟩) (e := ⟨{3, 4}, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide)) (Subtype.coe_ne_coe.mp (by decide))
    (Subtype.coe_ne_coe.mp (by decide))
  exact le_antisymm hpent ((isSRGWith_kneser_two 5).five_le_girth hnac)

@[toIsoGraph]
theorem domNum_star (n : ℕ) : (star n).domNum = 1 := by
  refine domNum_eq_one_of_universal (v := (Sum.inl 0 : Fin 1 ⊕ Fin n)) fun u hu ↦ ?_
  match u with
  | Sum.inl a => exact absurd (congrArg Sum.inl (Subsingleton.elim a (0 : Fin 1))) hu
  | Sum.inr b => exact bipartite_adj_inl_inr 1 n 0 b

@[toIsoGraph]
theorem domNum_wheel (n : ℕ) : (wheel n).domNum = 1 := domNum_join_complete_one (cycle n)

/-- An independent set of `K_{m,n}` is a set of vertices on one side. -/
@[simp, toIsoGraph] theorem indepCount_bipartite (m n k : ℕ) :
    (bipartite m n).indepCount (k + 1) = m.choose (k + 1) + n.choose (k + 1) := by
  classical
  rw [bipartite_eq_compl, indepCount_compl, cliqueCount_disjUnion, cliqueCount_complete,
    cliqueCount_complete]

/-- A ray of a star has only one neighbour, so a vertex of `K_{1,n}` with two distinct neighbours
is the centre. -/
theorem exists_eq_inl_of_two_neighbours {n : ℕ} {x u v : (bipartite 1 n).V} (huv : u ≠ v)
    (hu : (bipartite 1 n).Adj x u = true) (hv : (bipartite 1 n).Adj x v = true) :
    ∃ a, x = Sum.inl a := by
  rcases x with a | b
  · exact ⟨a, rfl⟩
  · exfalso
    apply huv
    rcases u with c | d
    · rcases v with c' | d'
      · rw [Subsingleton.elim c c']
      · simp at hv
    · simp at hu

/-- **Every automorphism of a star with at least two rays fixes the centre**, since the centre is
the only vertex with two distinct neighbours. -/
theorem aut_apply_inl {n : ℕ} (f : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2))
    (a : Fin 1) : f (.inl a) = .inl a := by
  obtain ⟨u, v, huv⟩ :=
    Fintype.exists_pair_of_one_lt_card (α := Fin (n + 2)) (by simp)
  have hne : (Sum.inr u : (bipartite 1 (n + 2)).V) ≠ Sum.inr v := fun h ↦ huv (Sum.inr.inj h)
  obtain ⟨a', ha'⟩ := exists_eq_inl_of_two_neighbours
    (x := f (.inl a)) (u := f (Sum.inr u)) (v := f (Sum.inr v))
    (fun h ↦ hne (f.injective h)) (by rw [f.adj_eq]; simp) (by rw [f.adj_eq]; simp)
  rw [ha', Subsingleton.elim a' a]

/-- With the centre fixed, an automorphism of a star with at least two rays is nothing but a
permutation of the rays. -/
theorem exists_perm_of_aut {n : ℕ} (f : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), f = starAut (n + 2) σ := by
  have hex : ∀ b : Fin (n + 2), ∃ r, f (.inr b) = Sum.inr r := by
    intro b
    rcases hb : f (.inr b) with a | r
    · exact absurd (f.injective (hb.trans (aut_apply_inl f a).symm)) (by simp)
    · exact ⟨r, rfl⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro b c h
    have hbc : f (.inr b) = f (.inr c) := by rw [hg b, hg c, h]
    exact Sum.inr.inj (f.injective hbc)
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj), ?_⟩
  ext x
  rcases x with a | b
  · rw [aut_apply_inl f a, starAut_inl]
  · rw [hg b, starAut_inr]
    rfl

/-- **The star `K_{1,n}` has exactly `n!` automorphisms** once it has at least two rays: every
automorphism fixes the centre, and what is left is an arbitrary permutation of the rays.  This is
the upper bound matching `IsoGraph.factorial_le_autCount_star`; the two smaller stars are
exceptions, `star 0 = K₁` has one automorphism and `star 1 = K₂` has two. -/
@[toIsoGraph]
theorem autCount_star (n : ℕ) : (star (n + 2)).autCount = (n + 2).factorial := by
  have hb : Function.Bijective (starAut (n + 2)) := by
    constructor
    · intro σ τ h
      refine Equiv.ext fun b ↦ ?_
      have h1 : (Sum.inr (σ b) : (bipartite 1 (n + 2)).V) = Sum.inr (τ b) :=
        congrArg (fun e : bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2) ↦ e (.inr b)) h
      exact Sum.inr.inj h1
    · intro f
      obtain ⟨σ, hσ⟩ := exists_perm_of_aut f
      exact ⟨σ, hσ.symm⟩
  have hcard : Nat.card (Equiv.Perm (Fin (n + 2)))
      = Nat.card (bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) :=
    Nat.card_eq_of_bijective _ hb
  have hperm : Nat.card (Equiv.Perm (Fin (n + 2))) = (n + 2).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  show Nat.card (bipartite 1 (n + 2) ≃cg bipartite 1 (n + 2)) = (n + 2).factorial
  rw [← hcard, hperm]

/-! ### The automorphism count of a complete bipartite graph

`K_{m,n}` with `m ≠ n` is the star argument with the asymmetry moved from one vertex to one side.
A vertex of the `m`-side has `n` neighbours and a vertex of the `n`-side has `m`, so as soon as the
two sides have different sizes no automorphism can exchange them, and the group is `Sₘ × Sₙ`.  When
`m = n` the swap is available and the count doubles, which is why the hypothesis cannot be dropped.
-/

/-- Permuting the two sides of `K_{m,n}` separately.  This is `bipartiteCongr` without the
requirement that the two sides have the same size. -/
def bipartiteAut (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    bipartite m n ≃cg bipartite m n :=
  autoOfPerm (G := bipartite m n) (Equiv.sumCongr σ τ) fun x y ↦ by
    show (bipartite m n).Adj (Sum.map σ τ x) (Sum.map σ τ y) = _
    rcases x with a | b <;> rcases y with c | d <;> simp

@[simp] theorem bipartiteAut_inl (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (a : Fin m) : bipartiteAut m n σ τ (.inl a) = .inl (σ a) := rfl

@[simp] theorem bipartiteAut_inr (m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (b : Fin n) : bipartiteAut m n σ τ (.inr b) = .inr (τ b) := rfl

theorem card_nbrs_bipartite_inl (m n : ℕ) (a : Fin m) :
    ((bipartite m n).nbrs (Sum.inl a)).card = n := by
  rw [nbrs_bipartite_inl, Finset.card_map, Finset.card_fin]

theorem card_nbrs_bipartite_inr (m n : ℕ) (b : Fin n) :
    ((bipartite m n).nbrs (Sum.inr b)).card = m := by
  rw [nbrs_bipartite_inr, Finset.card_map, Finset.card_fin]

/-- **The two sides of `K_{m,n}` cannot be exchanged when `m ≠ n`**, since they are told apart by
the degree of their vertices. -/
theorem bipartite_aut_inl {m n : ℕ} (hmn : m ≠ n) (f : bipartite m n ≃cg bipartite m n)
    (a : Fin m) : ∃ a', f (Sum.inl a) = Sum.inl a' := by
  rcases h : f (Sum.inl a) with a' | b'
  · exact ⟨a', rfl⟩
  · exfalso
    have h1 := card_nbrs_aut f (Sum.inl a)
    rw [h, card_nbrs_bipartite_inr, card_nbrs_bipartite_inl] at h1
    exact hmn h1

theorem bipartite_aut_inr {m n : ℕ} (hmn : m ≠ n) (f : bipartite m n ≃cg bipartite m n)
    (b : Fin n) : ∃ b', f (Sum.inr b) = Sum.inr b' := by
  rcases h : f (Sum.inr b) with a' | b'
  · exfalso
    have h1 := card_nbrs_aut f (Sum.inr b)
    rw [h, card_nbrs_bipartite_inl, card_nbrs_bipartite_inr] at h1
    exact hmn h1.symm
  · exact ⟨b', rfl⟩

/-- With the sides preserved, an automorphism of `K_{m,n}` is a pair of permutations. -/
theorem exists_perm_of_aut_bipartite {m n : ℕ} (hmn : m ≠ n)
    (f : bipartite m n ≃cg bipartite m n) :
    ∃ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)), f = bipartiteAut m n σ τ := by
  choose g hg using bipartite_aut_inl hmn f
  choose h hh using bipartite_aut_inr hmn f
  have hginj : Function.Injective g := by
    intro a b hab
    have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
    exact Sum.inl.inj (f.injective hab')
  have hhinj : Function.Injective h := by
    intro a b hab
    have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hh a, hh b, hab]
    exact Sum.inr.inj (f.injective hab')
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
    Equiv.ofBijective h (Finite.injective_iff_bijective.1 hhinj), ?_⟩
  ext x
  rcases x with a | b
  · rw [hg a, bipartiteAut_inl]
    rfl
  · rw [hh b, bipartiteAut_inr]
    rfl

/-- **The complete bipartite graph `K_{m,n}` has exactly `m! · n!` automorphisms when `m ≠ n`**:
the sides are told apart by degree, so each is permuted within itself.  This is the upper bound
matching `IsoGraph.factorial_mul_factorial_le_autCount_bipartite`, and it generalises
`autCount_star`, whose `n ≥ 2` hypothesis becomes `1 ≠ n`.  For `m = n` the true count is
`2 · (n!)²`, by `bipartiteSwap`. -/
@[toIsoGraph]
theorem autCount_bipartite {m n : ℕ} (hmn : m ≠ n) :
    (bipartite m n).autCount = m.factorial * n.factorial := by
  have hb : Function.Bijective
      (fun p : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) ↦ bipartiteAut m n p.1 p.2) := by
    constructor
    · rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ hst
      have h1 : ∀ a, (Sum.inl (σ a) : (bipartite m n).V) = Sum.inl (σ' a) := fun a ↦
        congrArg (fun e : bipartite m n ≃cg bipartite m n ↦ e (.inl a)) hst
      have h2 : ∀ b, (Sum.inr (τ b) : (bipartite m n).V) = Sum.inr (τ' b) := fun b ↦
        congrArg (fun e : bipartite m n ≃cg bipartite m n ↦ e (.inr b)) hst
      have e1 : σ = σ' := Equiv.ext fun a ↦ Sum.inl.inj (h1 a)
      have e2 : τ = τ' := Equiv.ext fun b ↦ Sum.inr.inj (h2 b)
      rw [e1, e2]
    · intro f
      obtain ⟨σ, τ, hσ⟩ := exists_perm_of_aut_bipartite hmn f
      exact ⟨(σ, τ), hσ.symm⟩
  have hcard := Nat.card_eq_of_bijective _ hb
  have hperm : Nat.card (Equiv.Perm (Fin m) × Equiv.Perm (Fin n))
      = m.factorial * n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  show Nat.card (bipartite m n ≃cg bipartite m n) = m.factorial * n.factorial
  rw [← hcard, hperm]

/-! ### The automorphism count of `K_{n,n}`

When the two sides have the same size the degree argument no longer separates them, but being on
the same side is still first-order: two distinct vertices are on the same side exactly when they
are non-adjacent.  So an automorphism either preserves both sides or exchanges them, and the count
doubles.
-/

/-- Permuting the two sides of `K_{n,n}` and then exchanging them. -/
def bipartiteSwapAut (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : bipartite n n ≃cg bipartite n n :=
  (bipartiteAut n n σ τ).trans (bipartiteSwap n)

@[simp] theorem bipartiteSwapAut_inl (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (a : Fin n) :
    bipartiteSwapAut n σ τ (.inl a) = .inr (σ a) := rfl

@[simp] theorem bipartiteSwapAut_inr (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (b : Fin n) :
    bipartiteSwapAut n σ τ (.inr b) = .inl (τ b) := rfl

/-- If one left vertex of `K_{n,n}` goes left then they all do: two left vertices are
non-adjacent, and a left and a right vertex are adjacent. -/
theorem bipartite_self_inl_inl {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a a' c : Fin n} (h : f (Sum.inl a) = Sum.inl c) :
    ∃ c', f (Sum.inl a') = Sum.inl c' := by
  rcases ha : f (Sum.inl a') with c' | d'
  · exact ⟨c', rfl⟩
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inl a')) = true := by
      rw [h, ha]; simp
    rw [f.adj_eq] at hadj
    simp at hadj

/-- If one left vertex of `K_{n,n}` goes right then they all do. -/
theorem bipartite_self_inl_inr {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a a' d : Fin n} (h : f (Sum.inl a) = Sum.inr d) :
    ∃ d', f (Sum.inl a') = Sum.inr d' := by
  rcases ha : f (Sum.inl a') with c' | d'
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inl a')) = true := by
      rw [h, ha]; simp
    rw [f.adj_eq] at hadj
    simp at hadj
  · exact ⟨d', rfl⟩

theorem bipartite_self_inr_of_inl {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a c : Fin n} (h : f (Sum.inl a) = Sum.inl c) (b : Fin n) :
    ∃ d, f (Sum.inr b) = Sum.inr d := by
  rcases hb : f (Sum.inr b) with c' | d'
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inr b)) = true := by
      rw [f.adj_eq]; simp
    rw [h, hb] at hadj
    simp at hadj
  · exact ⟨d', rfl⟩

theorem bipartite_self_inl_of_inr {n : ℕ} (f : bipartite n n ≃cg bipartite n n)
    {a d : Fin n} (h : f (Sum.inl a) = Sum.inr d) (b : Fin n) :
    ∃ c, f (Sum.inr b) = Sum.inl c := by
  rcases hb : f (Sum.inr b) with c' | d'
  · exact ⟨c', rfl⟩
  · exfalso
    have hadj : (bipartite n n).Adj (f (Sum.inl a)) (f (Sum.inr b)) = true := by
      rw [f.adj_eq]; simp
    rw [h, hb] at hadj
    simp at hadj

/-- **Every automorphism of `K_{n,n}` is a pair of permutations of the two sides, possibly
followed by exchanging them.** -/
theorem exists_perm_of_aut_bipartite_self {n : ℕ}
    (f : bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1)) :
    ∃ σ τ : Equiv.Perm (Fin (n + 1)),
      f = bipartiteAut (n + 1) (n + 1) σ τ ∨ f = bipartiteSwapAut (n + 1) σ τ := by
  rcases h0 : f (Sum.inl ⟨0, Nat.succ_pos n⟩) with c | d
  · have hl : ∀ a, ∃ c', f (Sum.inl a) = Sum.inl c' := fun a ↦ bipartite_self_inl_inl f h0
    have hr : ∀ b, ∃ d', f (Sum.inr b) = Sum.inr d' := bipartite_self_inr_of_inl f h0
    choose g hg using hl
    choose k hk using hr
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
      exact Sum.inl.inj (f.injective hab')
    have hkinj : Function.Injective k := by
      intro a b hab
      have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hk a, hk b, hab]
      exact Sum.inr.inj (f.injective hab')
    refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
      Equiv.ofBijective k (Finite.injective_iff_bijective.1 hkinj), Or.inl ?_⟩
    ext x
    rcases x with a | b
    · rw [hg a, bipartiteAut_inl]
      rfl
    · rw [hk b, bipartiteAut_inr]
      rfl
  · have hl : ∀ a, ∃ d', f (Sum.inl a) = Sum.inr d' := fun a ↦ bipartite_self_inl_inr f h0
    have hr : ∀ b, ∃ c', f (Sum.inr b) = Sum.inl c' := bipartite_self_inl_of_inr f h0
    choose g hg using hl
    choose k hk using hr
    have hginj : Function.Injective g := by
      intro a b hab
      have hab' : f (Sum.inl a) = f (Sum.inl b) := by rw [hg a, hg b, hab]
      exact Sum.inl.inj (f.injective hab')
    have hkinj : Function.Injective k := by
      intro a b hab
      have hab' : f (Sum.inr a) = f (Sum.inr b) := by rw [hk a, hk b, hab]
      exact Sum.inr.inj (f.injective hab')
    refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj),
      Equiv.ofBijective k (Finite.injective_iff_bijective.1 hkinj), Or.inr ?_⟩
    ext x
    rcases x with a | b
    · rw [hg a, bipartiteSwapAut_inl]
      rfl
    · rw [hk b, bipartiteSwapAut_inr]
      rfl

/-- An automorphism of `K_{n,n}` packaged as a `Bool` — whether the sides are exchanged — together
with a permutation of each side. -/
def bipartiteSelfAut (n : ℕ) (p : Bool × Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
    bipartite n n ≃cg bipartite n n :=
  if p.1 then bipartiteSwapAut n p.2.1 p.2.2 else bipartiteAut n n p.2.1 p.2.2

theorem bipartiteSelfAut_injective (n : ℕ) : Function.Injective (bipartiteSelfAut (n + 1)) := by
  rintro ⟨s, σ, τ⟩ ⟨s', σ', τ'⟩ h
  have key : ∀ x : (bipartite (n + 1) (n + 1)).V,
      bipartiteSelfAut (n + 1) (s, σ, τ) x = bipartiteSelfAut (n + 1) (s', σ', τ') x := fun x ↦
    congrArg (fun e : bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1) ↦ e x) h
  have hs : s = s' := by
    cases s <;> cases s' <;>
      first
        | rfl
        | exact absurd (key (Sum.inl ⟨0, Nat.succ_pos n⟩)) (by simp [bipartiteSelfAut])
  subst hs
  have hσ : σ = σ' := by
    refine Equiv.ext fun a ↦ ?_
    have hx := key (Sum.inl a)
    cases s with
    | false =>
      have h2 : (Sum.inl (σ a) : (bipartite (n + 1) (n + 1)).V) = Sum.inl (σ' a) := hx
      exact Sum.inl.inj h2
    | true =>
      have h2 : (Sum.inr (σ a) : (bipartite (n + 1) (n + 1)).V) = Sum.inr (σ' a) := hx
      exact Sum.inr.inj h2
  have hτ : τ = τ' := by
    refine Equiv.ext fun b ↦ ?_
    have hx := key (Sum.inr b)
    cases s with
    | false =>
      have h2 : (Sum.inr (τ b) : (bipartite (n + 1) (n + 1)).V) = Sum.inr (τ' b) := hx
      exact Sum.inr.inj h2
    | true =>
      have h2 : (Sum.inl (τ b) : (bipartite (n + 1) (n + 1)).V) = Sum.inl (τ' b) := hx
      exact Sum.inl.inj h2
  rw [hσ, hτ]

theorem bipartiteSelfAut_surjective (n : ℕ) : Function.Surjective (bipartiteSelfAut (n + 1)) := by
  intro f
  obtain ⟨σ, τ, hf | hf⟩ := exists_perm_of_aut_bipartite_self f
  · exact ⟨(false, σ, τ), hf.symm⟩
  · exact ⟨(true, σ, τ), hf.symm⟩

/-- **`K_{n,n}` has exactly `2 · (n!)²` automorphisms**: each side may be permuted freely, and the
two sides may be exchanged.  This is the case `autCount_bipartite` has to exclude. -/
@[toIsoGraph]
theorem autCount_bipartite_self (n : ℕ) :
    (bipartite (n + 1) (n + 1)).autCount = 2 * ((n + 1).factorial * (n + 1).factorial) := by
  have hb : Function.Bijective (bipartiteSelfAut (n + 1)) :=
    ⟨bipartiteSelfAut_injective n, bipartiteSelfAut_surjective n⟩
  have hcard := Nat.card_eq_of_bijective _ hb
  have hprod : Nat.card (Bool × Equiv.Perm (Fin (n + 1)) × Equiv.Perm (Fin (n + 1)))
      = 2 * ((n + 1).factorial * (n + 1).factorial) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_perm, Fintype.card_fin]
  show Nat.card (bipartite (n + 1) (n + 1) ≃cg bipartite (n + 1) (n + 1))
    = 2 * ((n + 1).factorial * (n + 1).factorial)
  rw [← hcard, hprod]

/-! ### The automorphism count of a wheel

A wheel is a cone over a cycle, and once the rim is long enough the hub is recognisable: it is the
only vertex adjacent to every other one, since a rim vertex misses the rim vertex two steps along.
Every automorphism therefore fixes the hub and permutes the rim, and what it does to the rim is an
automorphism of the cycle.  That restriction map is injective, so the wheel has no more symmetry
than its rim, and the join bound `le_autCount_wheel` says it has no less.
-/

private theorem cyc_mod_two (N i : ℕ) (hN : 2 ≤ N) (hi : i < N) :
    (i + 2) % N = if i + 2 = N then 0 else if i + 2 = N + 1 then 1 else i + 2 := by
  rcases lt_trichotomy (i + 2) N with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), Nat.mod_eq_of_lt h]
  · rw [if_pos h, ← h, Nat.mod_self]
  · have h1 : i + 2 = N + 1 := by omega
    rw [if_neg (by omega), if_pos h1, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem wheel_adj_inr_inr {N : ℕ} (u v : (cycle N).V) :
    (wheel N).Adj (Sum.inr u) (Sum.inr v) = (cycle N).Adj u v := by
  simp [wheel]

theorem wheel_adj_inl_inr {N : ℕ} (a : (complete 1).V) (v : (cycle N).V) :
    (wheel N).Adj (Sum.inl a) (Sum.inr v) = true := by
  simp [wheel]

/-- The hub of a wheel is unique: `complete 1` has just one vertex.  Stated as a plain equation
rather than obtained from a `Subsingleton` instance because typeclass search does not unfold
`(complete 1).V`. -/
theorem complete_one_elim {a b : (complete 1).V} : a = b := Subsingleton.elim (α := Fin 1) a b

/-- In a cycle of length at least four, every vertex misses some other vertex: the vertex two
steps along is neither the vertex itself nor one of its two neighbours. -/
theorem exists_cycle_non_adj {N : ℕ} (hN : 4 ≤ N) (b : (cycle N).V) :
    ∃ c : (cycle N).V, c ≠ b ∧ (cycle N).Adj b c = false := by
  have hb := b.isLt
  have hlt : (b.1 + 2) % N < N := Nat.mod_lt _ (by omega)
  have key : (b.1 + 2) % N ≠ b.1 ∧ (b.1 + 2) % N ≠ (b.1 + 1) % N ∧
      (b.1 + 2) % N ≠ (b.1 + N - 1) % N := by
    rw [cyc_mod_two N b.1 (by omega) hb, cyc_mod_succ N b.1 hb, cyc_mod_pred N b.1 hb]
    refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
  refine ⟨⟨(b.1 + 2) % N, hlt⟩, Fin.ne_of_val_ne key.1, ?_⟩
  rw [Bool.eq_false_iff, ne_eq, cycle_adj_eq_iff (by omega)]
  rintro (h | h)
  · exact key.2.1 h
  · exact key.2.2 h

/-- The hub is the only vertex of a wheel adjacent to every other one, once the rim has length at
least four. -/
theorem eq_inl_of_adj_all {N : ℕ} (hN : 4 ≤ N) {x : (wheel N).V}
    (hx : ∀ y : (wheel N).V, y ≠ x → (wheel N).Adj x y = true) :
    ∃ a : (complete 1).V, x = Sum.inl a := by
  rcases x with a | b
  · exact ⟨a, rfl⟩
  · obtain ⟨c, hcb, hadj⟩ := exists_cycle_non_adj hN b
    have h := hx (Sum.inr c) fun hi ↦ hcb (Sum.inr.inj hi)
    rw [wheel_adj_inr_inr, hadj] at h
    exact absurd h (by simp)

/-- **Every automorphism of a wheel fixes the hub** once the rim has length at least four. -/
theorem wheel_hub {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (a : (complete 1).V) :
    f (Sum.inl a) = Sum.inl a := by
  have hall : ∀ y : (wheel N).V, y ≠ f (Sum.inl a) → (wheel N).Adj (f (Sum.inl a)) y = true := by
    intro y hy
    obtain ⟨z, rfl⟩ : ∃ z, f z = y := ⟨f.symm y, f.apply_symm_apply y⟩
    rw [f.adj_eq]
    rcases z with a' | c
    · exact absurd (complete_one_elim (a := a') (b := a)) fun h ↦ hy (by rw [h])
    · exact wheel_adj_inl_inr a c
  obtain ⟨a', ha'⟩ := eq_inl_of_adj_all hN hall
  rw [ha', complete_one_elim (a := a') (b := a)]

/-- The rim component of the image of a rim vertex.  The fallback branch is never taken. -/
def wheelRim {N : ℕ} (f : wheel N ≃cg wheel N) (b : (cycle N).V) : (cycle N).V :=
  Sum.elim (fun _ : (complete 1).V ↦ b) (id : (cycle N).V → (cycle N).V) (f (Sum.inr b))

theorem wheel_rim_exists {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b : (cycle N).V) :
    ∃ c, f (Sum.inr b) = Sum.inr c := by
  rcases hb : f (Sum.inr b) with a | c
  · exact absurd (f.injective (hb.trans (wheel_hub hN f a).symm)) (by simp)
  · exact ⟨c, rfl⟩

theorem wheelRim_spec {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b : (cycle N).V) :
    f (Sum.inr b) = Sum.inr (wheelRim f b) := by
  obtain ⟨c, hc⟩ := wheel_rim_exists hN f b
  simp only [wheelRim, hc, Sum.elim_inr, id_eq]

theorem wheelRim_injective {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) :
    Function.Injective (wheelRim f) := by
  intro b c h
  have hbc : f (Sum.inr b) = f (Sum.inr c) := by
    rw [wheelRim_spec hN, wheelRim_spec hN, h]
  exact Sum.inr.inj (f.injective hbc)

theorem wheelRim_adj {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) (b c : (cycle N).V) :
    (cycle N).Adj (wheelRim f b) (wheelRim f c) = (cycle N).Adj b c := by
  have h1 : (wheel N).Adj (f (Sum.inr b)) (f (Sum.inr c))
      = (wheel N).Adj (Sum.inr b) (Sum.inr c) := f.adj_eq _ _
  rw [wheelRim_spec hN, wheelRim_spec hN, wheel_adj_inr_inr, wheel_adj_inr_inr] at h1
  exact h1

/-- **Restricting an automorphism of a wheel to its rim** gives an automorphism of the cycle. -/
noncomputable def wheelToCycle {N : ℕ} (hN : 4 ≤ N) (f : wheel N ≃cg wheel N) :
    cycle N ≃cg cycle N :=
  autoOfPerm (G := cycle N)
    (Equiv.ofBijective (wheelRim f) (Finite.injective_iff_bijective.1 (wheelRim_injective hN f)))
    fun x y ↦ wheelRim_adj hN f x y

theorem wheelToCycle_injective {N : ℕ} (hN : 4 ≤ N) :
    Function.Injective (wheelToCycle hN) := by
  intro f g h
  refine RelIso.ext fun x ↦ ?_
  rcases x with a | b
  · rw [wheel_hub hN f a, wheel_hub hN g a]
  · have hb : wheelRim f b = wheelRim g b :=
      congrArg (fun e : cycle N ≃cg cycle N ↦ e b) h
    rw [wheelRim_spec hN f b, wheelRim_spec hN g b, hb]

/-- **A wheel has at most `2n` automorphisms** once its rim has length at least four: the hub is
fixed, and what is left is an automorphism of the rim. -/
theorem autCount_wheel_le {N : ℕ} (hN : 4 ≤ N) : (wheel N).autCount ≤ 2 * N := by
  have : Finite (cycle N ≃cg cycle N) := (cycle N).instFiniteAut
  have h := Nat.card_le_card_of_injective (wheelToCycle hN) (wheelToCycle_injective hN)
  have h2 : (wheel N).autCount ≤ (cycle N).autCount := h
  exact h2.trans (autCount_cycle_le (by omega))

end

end CGraph
