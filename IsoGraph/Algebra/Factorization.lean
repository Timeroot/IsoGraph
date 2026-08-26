import IsoGraph.Algebra.Cancellation

/-!
# Factorization

Factorization: irreducibility, primality, and what the abstract ring-theoretic classes come to for
the graph semiring.
-/

namespace IsoGraph

/-- A graph has no components exactly when it has no vertices. -/
theorem numComponents_eq_zero_iff_eq_empty {a : IsoGraph} :
    a.numComponents = 0 ↔ a = empty 0 := by
  rw [numComponents_eq_zero_iff, V_eq_zero_iff]

/-! ## The arguments, over an abstract structure

None of the six scopes of `Identities/Semiring.lean` is open here, so `*` below is whichever
product the caller supplies, and the properties of that product enter as hypotheses: `hV` says it
multiplies vertex counts, `hone` and `hzero` identify its unit and its zero, and `hadd` says the
addition is the disjoint union.  All four are `rfl` in every scope.  The two global `0` and `1`
instances have to be switched off for the section, or they would shadow those of the structure
being quantified over and no `Mathlib` lemma about `1` would apply. -/

attribute [-instance] IsoGraph.instZero IsoGraph.instOne

section
variable [MonoidWithZero IsoGraph]
  (hzero : (0 : IsoGraph) = empty 0)
  (hone : (1 : IsoGraph) = empty 1)
  (hV : ∀ G H : IsoGraph, (G * H).V = G.V * H.V)

include hV in
/-- A factor has at most as many vertices as the product, and divides it. -/
theorem V_dvd_of_dvd {a b : IsoGraph} (h : a ∣ b) : a.V ∣ b.V := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c.V, hV a c⟩

include hone hV in
/-- **The one-vertex graph is the only unit.** -/
theorem isUnit_iff_V (G : IsoGraph) : IsUnit G ↔ G.V = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := h
    have hu := congrArg IsoGraph.V u.mul_inv
    rw [hV, hone, V_empty] at hu
    exact Nat.eq_one_of_dvd_one ⟨_, hu.symm⟩
  · have hG : G = 1 := by rw [hone]; exact V_eq_one_iff.1 h
    exact hG ▸ isUnit_one

include hone hV in
/-- **Associated graphs are equal.**  Associates differ by a unit, and the only unit is the graph
on one vertex, so the "up to associates" that factorisation theory usually has to carry around is
here plain equality of isomorphism classes. -/
theorem associated_iff_eq {a b : IsoGraph} : Associated a b ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Associated.refl a⟩
  obtain ⟨u, hu⟩ := h
  have h1 : (u : IsoGraph) = 1 := by
    rw [hone]
    exact V_eq_one_iff.1 ((isUnit_iff_V hone hV _).1 u.isUnit)
  rw [← hu, h1, mul_one]

include hone hV in
/-- **A graph on a prime number of vertices is irreducible**, there being nowhere for the vertices
of a factorisation to go. -/
theorem irreducible_of_prime_V {G : IsoGraph} (hp : Nat.Prime G.V) : Irreducible G := by
  refine ⟨fun h ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [isUnit_iff_V hone hV] at h
    rw [h] at hp
    exact Nat.not_prime_one hp
  · have hVab := congrArg IsoGraph.V hab
    rw [hV] at hVab
    rw [isUnit_iff_V hone hV, isUnit_iff_V hone hV]
    rcases hp.eq_one_or_self_of_dvd a.V ⟨b.V, hVab⟩ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h] at hVab
      exact (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hVab)).symm

end

section
variable [CommMonoidWithZero IsoGraph]
  (hzero : (0 : IsoGraph) = empty 0)
  (hone : (1 : IsoGraph) = empty 1)
  (hV : ∀ G H : IsoGraph, (G * H).V = G.V * H.V)

include hzero hone hV in
/-- **Divisibility is well-founded**: dividing by a non-unit loses a vertex.  Only the graph on no
vertices needs an argument of its own, since everything divides it. -/
theorem wfDvdMonoid_of_V : WfDvdMonoid IsoGraph := by
  have hVz : ∀ a : IsoGraph, a.V = 0 ↔ a = 0 := by
    intro a; rw [hzero]; exact V_eq_zero_iff
  have key : ∀ n (a : IsoGraph), a.V ≤ n → a ≠ 0 → Acc DvdNotUnit a := by
    intro n
    induction n with
    | zero => exact fun a ha h0 ↦ absurd ((hVz a).1 (Nat.le_zero.1 ha)) h0
    | succ n ih =>
      refine fun a ha h0 ↦ Acc.intro _ (fun b hb ↦ ih b ?_ hb.1)
      obtain ⟨c, hc, rfl⟩ := hb.2
      rw [isUnit_iff_V hone hV] at hc
      have hb0 : b.V ≠ 0 := fun h ↦ hb.1 ((hVz b).1 h)
      have hc0 : c.V ≠ 0 := fun h ↦ h0 ((hVz _).1 (by rw [hV, h, mul_zero]))
      rw [hV] at ha
      have h2 : 2 ≤ c.V := by omega
      nlinarith [Nat.one_le_iff_ne_zero.2 hb0]
  refine ⟨⟨fun a ↦ ?_⟩⟩
  by_cases h : a = 0
  · exact h ▸ Acc.intro _ (fun b hb ↦ key b.V b le_rfl hb.1)
  · exact key a.V a le_rfl h

include hzero hone hV in
/-- **Every graph with a vertex is a product of irreducibles.**  Well-founded divisibility gives a
factorisation up to associates, and associates are equal here, so the product is the graph on the
nose.  The empty multiset covers the one-vertex graph; anything larger gets a genuine factor. -/
theorem exists_multiset_prod_eq {a : IsoGraph} (ha : a ≠ 0) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a := by
  have := wfDvdMonoid_of_V hzero hone hV
  obtain ⟨f, hf, hassoc⟩ := WfDvdMonoid.exists_factors a ha
  exact ⟨f, hf, (associated_iff_eq hone hV).1 hassoc⟩

end

section
variable [CommSemiring IsoGraph]
  (hadd : ∀ G H : IsoGraph, G + H = G ⊕g H)
  (hzero : (0 : IsoGraph) = empty 0)
  (hone : (1 : IsoGraph) = empty 1)
  (hV : ∀ G H : IsoGraph, (G * H).V = G.V * H.V)

include hadd hone hV in
/-- **The graph semiring is local**: a disjoint union is one vertex only if a summand is. -/
theorem isLocalRing_of_V : IsLocalRing IsoGraph := by
  refine IsLocalRing.of_is_unit_or_is_unit_of_add_one (fun {a b} hab ↦ ?_)
  have h := congrArg IsoGraph.V hab
  rw [hadd, V_disjUnion, hone, V_empty] at h
  rw [isUnit_iff_V hone hV, isUnit_iff_V hone hV]
  omega

include hadd hone hV in
/-- **The graph semiring is not Bézout**: the ideal generated by `K₂` and `K₃` is not principal,
because a generator would have to have one vertex, and no combination of `K₂` and `K₃` is a single
vertex. -/
theorem not_isBezout_of_V : ¬ IsBezout IsoGraph := by
  intro hb
  have hfg : (Ideal.span {complete 2, complete 3} : Ideal IsoGraph).FG :=
    Submodule.fg_span (Set.toFinite _)
  obtain ⟨g, hg⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  have hmem : ∀ n : ℕ, complete n ∈ ({complete 2, complete 3} : Set IsoGraph) →
      g.V ∣ (complete n).V := by
    intro n hn
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hg ▸ Ideal.subset_span hn)
    exact V_dvd_of_dvd hV (Dvd.intro_left c hc)
  have h2 : g.V ∣ 2 := by simpa using hmem 2 (by simp)
  have h3 : g.V ∣ 3 := by simpa using hmem 3 (by simp)
  have htop : Ideal.span ({complete 2, complete 3} : Set IsoGraph) = ⊤ := by
    rw [hg]
    exact Ideal.span_singleton_eq_top.2
      ((isUnit_iff_V hone hV g).2 (Nat.eq_one_of_dvd_one (by simpa using Nat.dvd_gcd h2 h3)))
  have h1 : (1 : IsoGraph) ∈ Ideal.span ({complete 2, complete 3} : Set IsoGraph) := by
    rw [htop]; trivial
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 h1
  have h := congrArg IsoGraph.V hcd
  rw [hadd, V_disjUnion, hV, hV, hone, V_empty] at h
  simp only [V_complete] at h
  omega

include hadd hone hV in
/-- **The graph semiring is not a principal ideal ring**, a principal ideal ring being Bézout. -/
theorem not_isPrincipalIdealRing_of_V : ¬ IsPrincipalIdealRing IsoGraph :=
  fun _ ↦ not_isBezout_of_V hadd hone hV inferInstance

include hadd hzero hV in
/-- The graphs that are not a single vertex: the non-units, which form an ideal because a disjoint
union has one vertex only if a summand does. -/
private def nonunitIdeal : Ideal IsoGraph where
  carrier := {G : IsoGraph | G.V ≠ 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, hadd, V_disjUnion] at *
    omega
  zero_mem' := by simp [hzero]
  smul_mem' := by
    intro c a ha h
    simp only [Set.mem_ofPred_eq, smul_eq_mul, hV] at *
    exact ha (Nat.eq_one_of_dvd_one ⟨c.V, by rw [mul_comm]; exact h.symm⟩)

include hadd hzero hV in
/-- **The graph semiring is not Noetherian.**  Its maximal ideal is not finitely generated: pick a
prime larger than every generator's order, and expand the complete graph on that many vertices
over the generators.  The number of components is additive and the complete graph is connected, so
exactly one term of that expansion is nonzero and equals the complete graph itself; its generator
then has a number of vertices that divides the prime and is not one. -/
theorem not_isNoetherianRing_of_V : ¬ IsNoetherianRing IsoGraph := by
  classical
  intro hn
  obtain ⟨S, hS⟩ := (isNoetherianRing_iff_ideal_fg IsoGraph).1 hn (nonunitIdeal hadd hzero hV)
  obtain ⟨q, hqle, hq⟩ := Nat.exists_infinite_primes (S.sup IsoGraph.V + 2)
  have hncq : (complete q : IsoGraph).numComponents = 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
    exact numComponents_complete m
  have hmem : (complete q : IsoGraph) ∈ Ideal.span (S : Set IsoGraph) := by
    rw [hS]
    show (complete q : IsoGraph).V ≠ 1
    rw [V_complete]
    omega
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hmem
  simp only [smul_eq_mul] at hf
  have hnc : ∀ a b : IsoGraph, (a + b).numComponents = a.numComponents + b.numComponents :=
    fun a b ↦ by rw [hadd, numComponents_disjUnion]
  let φ : IsoGraph →+ ℕ :=
    { toFun := IsoGraph.numComponents
      map_zero' := by rw [hzero]; simp
      map_add' := hnc }
  have hsum : ∑ a ∈ S, (f a * a).numComponents = 1 := by
    have hh := congrArg φ hf
    rwa [map_sum, show φ (complete q) = 1 from hncq] at hh
  obtain ⟨a₀, ha₀S, ha₀⟩ : ∃ a ∈ S, (f a * a).numComponents ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have hrest : ∀ a ∈ S.erase a₀, f a * a = 0 := by
    intro a ha
    have hle : (f a * a).numComponents ≤ ∑ x ∈ S.erase a₀, (f x * x).numComponents :=
      Finset.single_le_sum (f := fun x ↦ (f x * x).numComponents) (fun _ _ ↦ Nat.zero_le _) ha
    have hsplit : (f a₀ * a₀).numComponents + ∑ x ∈ S.erase a₀, (f x * x).numComponents
        = ∑ x ∈ S, (f x * x).numComponents :=
      Finset.add_sum_erase S (fun x ↦ (f x * x).numComponents) ha₀S
    rw [hsum] at hsplit
    rw [hzero]
    exact numComponents_eq_zero_iff_eq_empty.1 (by omega)
  have heq : (complete q : IsoGraph) = f a₀ * a₀ := by
    have hsplit : f a₀ * a₀ + ∑ x ∈ S.erase a₀, f x * x = ∑ x ∈ S, f x * x :=
      Finset.add_sum_erase S (fun x ↦ f x * x) ha₀S
    rw [← hf, ← hsplit, Finset.sum_congr rfl hrest, Finset.sum_const_zero, add_zero]
  have hdvd : a₀.V ∣ q := by
    have hh := V_dvd_of_dvd hV (Dvd.intro_left (f a₀) heq.symm)
    rwa [V_complete] at hh
  have hne1 : a₀.V ≠ 1 := by
    have hmem' : a₀ ∈ Ideal.span (S : Set IsoGraph) := Ideal.subset_span ha₀S
    rw [hS] at hmem'
    exact hmem'
  have hle : a₀.V ≤ S.sup IsoGraph.V := Finset.le_sup ha₀S
  have : a₀.V = q := (hq.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  omega

include hadd hone hV in
/-- With `x` on two vertices, `1 + x` has three vertices and `1 + x + x²` has seven, so the one
cannot divide the other. -/
private theorem not_dvd_one_add_add_sq (x : IsoGraph) (hx : x.V = 2) :
    ¬ (1 + x) ∣ (1 + x + x * x) := by
  intro h
  have h7 := V_dvd_of_dvd hV h
  simp only [hadd, V_disjUnion, hone, V_empty, hV, hx] at h7
  omega

include hadd hone hV in
/-- With `x` connected on two vertices, `1 + x` does not divide `1 + x³`: a cofactor would be a
component of `1 + x³` and so have one or eight vertices rather than three. -/
private theorem not_dvd_one_add_cube (x : IsoGraph) (hx : x.V = 2)
    (hx3 : (x * x * x).numComponents = 1) : ¬ (1 + x) ∣ (1 + x * x * x) := by
  rintro ⟨c, hc⟩
  have hc' : (1 : IsoGraph) + x * x * x = c + x * c := by rw [hc]; ring
  have hVc : c.V = 3 := by
    have hh := congrArg IsoGraph.V hc
    simp only [hadd, hV, V_disjUnion, hone, V_empty, hx] at hh
    omega
  have hVxc : (x * c).V = 6 := by rw [hV, hx, hVc]
  have hnc : ∀ a b : IsoGraph, (a + b).numComponents = a.numComponents + b.numComponents :=
    fun a b ↦ by rw [hadd, numComponents_disjUnion]
  have hnc1 : (1 : IsoGraph).numComponents = 1 := by rw [hone, numComponents_empty]
  have hncc : c.numComponents = 1 := by
    have hh := congrArg IsoGraph.numComponents hc'
    rw [hnc, hnc, hnc1, hx3] at hh
    have h1 : c.numComponents ≠ 0 := fun hzz ↦ by
      rw [numComponents_eq_zero_iff_eq_empty.1 hzz, V_empty] at hVc; omega
    have h2 : (x * c).numComponents ≠ 0 := fun hzz ↦ by
      rw [numComponents_eq_zero_iff_eq_empty.1 hzz, V_empty] at hVxc; omega
    omega
  have hcomps := congrArg IsoGraph.comps hc'
  rw [hadd, hadd, comps_disjUnion, comps_disjUnion, comps_eq_singleton hnc1,
    comps_eq_singleton hx3, comps_eq_singleton hncc] at hcomps
  have hmem : c ∈ ({(1 : IsoGraph)} + {x * x * x} : Multiset IsoGraph) := by
    rw [hcomps]; exact Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self c))
  rw [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · rw [hone, V_empty] at hVc; omega
  · rw [hV, hV, hx] at hVc; omega

/-- **The two factorisations.**  Writing `x` for `K₂`, so that `xᵏ` is the `k`-cube, both sides are
`1 + x + x² + x³ + x⁴ + x⁵`; the identity holds in any commutative semiring and so needs nothing
about graphs at all. -/
theorem one_add_mul_eq (x : IsoGraph) :
    (1 + x) * (1 + x * x + x * x * x * x) = (1 + x + x * x) * (1 + x * x * x) := by ring

include hadd hone hV in
/-- **An irreducible graph that is not prime.**  With `x` connected on two vertices, `1 + x` has
three vertices, and `(1 + x) * (1 + x² + x⁴) = (1 + x + x²) * (1 + x³)`.  It does not divide
`1 + x + x²`, which has seven vertices; and it does not divide `1 + x³` either, since a cofactor
would be a component of `1 + x³` and so have one or eight vertices rather than three. -/
theorem not_prime_one_add (x : IsoGraph) (hx : x.V = 2) (hx3 : (x * x * x).numComponents = 1) :
    ¬ Prime (1 + x) := by
  intro hp
  have hdvd : (1 + x) ∣ (1 + x + x * x) * (1 + x * x * x) :=
    ⟨1 + x * x + x * x * x * x, (one_add_mul_eq x).symm⟩
  rcases hp.2.2 _ _ hdvd with h | h
  · exact not_dvd_one_add_add_sq hadd hone hV x hx h
  · exact not_dvd_one_add_cube hadd hone hV x hx hx3 h

include hadd hone hV in
/-- **Irreducible does not imply prime** in the graph semiring. -/
theorem exists_irreducible_not_prime (x : IsoGraph) (hx : x.V = 2)
    (hx3 : (x * x * x).numComponents = 1) : ∃ p : IsoGraph, Irreducible p ∧ ¬ Prime p := by
  refine ⟨1 + x, irreducible_of_prime_V hone hV ?_, not_prime_one_add hadd hone hV x hx hx3⟩
  rw [hadd, V_disjUnion, hone, V_empty, hx]
  exact Nat.prime_three

include hadd hone hV in
/-- **Graphs do not factor uniquely.** -/
theorem not_uniqueFactorizationMonoid_of_V (x : IsoGraph) (hx : x.V = 2)
    (hx3 : (x * x * x).numComponents = 1) : ¬ UniqueFactorizationMonoid IsoGraph := by
  intro _
  obtain ⟨p, hirr, hnp⟩ := exists_irreducible_not_prime hadd hone hV x hx hx3
  exact hnp (UniqueFactorizationMonoid.irreducible_iff_prime.1 hirr)

include hadd hzero hone hV in
/-- **Two genuinely different factorisations of one graph into irreducibles.**  Writing `x` for
`K₂`, the commutative-semiring axioms alone give

    (1 + x) * (1 + x² + x⁴) = 1 + x + x² + x³ + x⁴ + x⁵ = (1 + x + x²) * (1 + x³),

so the two sides are the same graph.  Split `1 + x + x²` and `1 + x³` into irreducibles and one
gets a factorisation none of whose members is `1 + x`, since `1 + x` divides neither; split
`1 + x² + x⁴` and put `1 + x` in front, which is irreducible because it has three vertices, and one
gets a factorisation that does contain `1 + x`.  The two multisets therefore differ, and since
associates are equal here there is no wriggle room left: the factorisation really is not unique.
The graph in question is disconnected, and that is no accident — Sabidussi and Vizing proved that
connected graphs do factor uniquely under the cartesian product. -/
theorem exists_factorisations_ne (x : IsoGraph) (hx : x.V = 2)
    (hx3 : (x * x * x).numComponents = 1) :
    ∃ f g : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ (∀ b ∈ g, Irreducible b) ∧
      f.prod = g.prod ∧ f ≠ g := by
  have hVone : (1 : IsoGraph).V = 1 := by rw [hone, V_empty]
  have hVadd : ∀ a b : IsoGraph, (a + b).V = a.V + b.V := fun a b ↦ by rw [hadd, V_disjUnion]
  have hne : ∀ a : IsoGraph, a.V ≠ 0 → a ≠ 0 := fun a h hz ↦ h (by rw [hz, hzero, V_empty])
  have hV7 : (1 + x + x * x : IsoGraph).V = 7 := by simp only [hVadd, hV, hVone, hx]
  have hV9 : (1 + x * x * x : IsoGraph).V = 9 := by simp only [hVadd, hV, hVone, hx]
  have hV21 : (1 + x * x + x * x * x * x : IsoGraph).V = 21 := by
    simp only [hVadd, hV, hVone, hx]
  obtain ⟨f₁, hf₁, hf₁p⟩ :=
    exists_multiset_prod_eq hzero hone hV (a := 1 + x + x * x) (hne _ (by omega))
  obtain ⟨f₂, hf₂, hf₂p⟩ :=
    exists_multiset_prod_eq hzero hone hV (a := 1 + x * x * x) (hne _ (by omega))
  obtain ⟨g₀, hg₀, hg₀p⟩ :=
    exists_multiset_prod_eq hzero hone hV (a := 1 + x * x + x * x * x * x) (hne _ (by omega))
  have hirr : Irreducible (1 + x : IsoGraph) := by
    refine irreducible_of_prime_V hone hV ?_
    have hV3 : (1 + x : IsoGraph).V = 3 := by simp only [hVadd, hVone, hx]
    rw [hV3]
    exact Nat.prime_three
  refine ⟨f₁ + f₂, (1 + x) ::ₘ g₀, ?_, ?_, ?_, ?_⟩
  · exact fun b hb ↦ (Multiset.mem_add.1 hb).elim (hf₁ b) (hf₂ b)
  · intro b hb
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · exact hirr
    · exact hg₀ b hb
  · rw [Multiset.prod_add, Multiset.prod_cons, hf₁p, hf₂p, hg₀p, one_add_mul_eq]
  · intro heq
    have hmem : (1 + x : IsoGraph) ∈ f₁ + f₂ := by
      rw [heq]; exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.1 hmem with hb | hb
    · exact not_dvd_one_add_add_sq hadd hone hV x hx (hf₁p ▸ Multiset.dvd_prod hb)
    · exact not_dvd_one_add_cube hadd hone hV x hx hx3 (hf₂p ▸ Multiset.dvd_prod hb)

end

/-! ## The scopes

Each scope of `Identities/Semiring.lean` that has a unit gets the results above, with the four
hypotheses discharged by `rfl`.  The three multiplicative scopes get what needs only a product;
the two semiring scopes get everything. -/

end IsoGraph

namespace IsoGraph.CartesianProduct

/-- **The one-vertex graph is the only unit** of the cartesian product. -/
theorem isUnit_iff (G : IsoGraph) : IsUnit G ↔ G.V = 1 := isUnit_iff_V rfl V_cartesianProduct G

/-- A graph on a prime number of vertices is irreducible for the cartesian product. -/
theorem irreducible_of_prime_V {G : IsoGraph} (hp : Nat.Prime G.V) : Irreducible G :=
  IsoGraph.irreducible_of_prime_V rfl V_cartesianProduct hp

/-- **Associated graphs are equal** for the cartesian product. -/
theorem associated_iff_eq {a b : IsoGraph} : Associated a b ↔ a = b :=
  IsoGraph.associated_iff_eq rfl V_cartesianProduct

/-- **Divisibility for the cartesian product is well-founded.** -/
scoped instance instWfDvdMonoid : WfDvdMonoid IsoGraph :=
  wfDvdMonoid_of_V rfl rfl V_cartesianProduct

/-- **Every graph with a vertex is a cartesian product of irreducibles.** -/
theorem exists_multiset_prod_eq {a : IsoGraph} (ha : a ≠ 0) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a :=
  IsoGraph.exists_multiset_prod_eq rfl rfl V_cartesianProduct ha

end IsoGraph.CartesianProduct

namespace IsoGraph.StrongProduct

/-- **The one-vertex graph is the only unit** of the strong product. -/
theorem isUnit_iff (G : IsoGraph) : IsUnit G ↔ G.V = 1 := isUnit_iff_V rfl V_strongProduct G

/-- A graph on a prime number of vertices is irreducible for the strong product. -/
theorem irreducible_of_prime_V {G : IsoGraph} (hp : Nat.Prime G.V) : Irreducible G :=
  IsoGraph.irreducible_of_prime_V rfl V_strongProduct hp

/-- **Associated graphs are equal** for the strong product. -/
theorem associated_iff_eq {a b : IsoGraph} : Associated a b ↔ a = b :=
  IsoGraph.associated_iff_eq rfl V_strongProduct

/-- **Divisibility for the strong product is well-founded.** -/
scoped instance instWfDvdMonoid : WfDvdMonoid IsoGraph :=
  wfDvdMonoid_of_V rfl rfl V_strongProduct

/-- **Every graph with a vertex is a strong product of irreducibles.** -/
theorem exists_multiset_prod_eq {a : IsoGraph} (ha : a ≠ 0) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a :=
  IsoGraph.exists_multiset_prod_eq rfl rfl V_strongProduct ha

end IsoGraph.StrongProduct

namespace IsoGraph.LexProduct

/-- **The one-vertex graph is the only unit** of the lexicographic product. -/
theorem isUnit_iff (G : IsoGraph) : IsUnit G ↔ G.V = 1 := isUnit_iff_V rfl V_lexProduct G

/-- A graph on a prime number of vertices is irreducible for the lexicographic product. -/
theorem irreducible_of_prime_V {G : IsoGraph} (hp : Nat.Prime G.V) : Irreducible G :=
  IsoGraph.irreducible_of_prime_V rfl V_lexProduct hp

/-- **Associated graphs are equal** for the lexicographic product. -/
theorem associated_iff_eq {a b : IsoGraph} : Associated a b ↔ a = b :=
  IsoGraph.associated_iff_eq rfl V_lexProduct

end IsoGraph.LexProduct

namespace IsoGraph.Semiring

/-- **The one-vertex graph is the only unit.** -/
theorem isUnit_iff (G : IsoGraph) : IsUnit G ↔ G.V = 1 := isUnit_iff_V rfl V_cartesianProduct G

/-- **Divisibility is well-founded**, so every graph on at least two vertices is a product of
irreducibles. -/
scoped instance instWfDvdMonoid : WfDvdMonoid IsoGraph :=
  wfDvdMonoid_of_V rfl rfl V_cartesianProduct

/-- **The graph semiring is local**, the one-vertex graph being its only unit. -/
scoped instance instIsLocalRing : IsLocalRing IsoGraph :=
  isLocalRing_of_V (fun _ _ ↦ rfl) rfl V_cartesianProduct

/-- **The graph semiring is not Bézout.** -/
theorem not_isBezout : ¬ IsBezout IsoGraph :=
  not_isBezout_of_V (fun _ _ ↦ rfl) rfl V_cartesianProduct

/-- **The graph semiring is not a principal ideal ring.** -/
theorem not_isPrincipalIdealRing : ¬ IsPrincipalIdealRing IsoGraph :=
  not_isPrincipalIdealRing_of_V (fun _ _ ↦ rfl) rfl V_cartesianProduct

/-- **The graph semiring is not Noetherian.** -/
theorem not_isNoetherianRing : ¬ IsNoetherianRing IsoGraph :=
  not_isNoetherianRing_of_V (fun _ _ ↦ rfl) rfl V_cartesianProduct

/-- The three-cube is connected. -/
private theorem cube_connected :
    ((complete 2 : IsoGraph) * complete 2 * complete 2).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_cartesianProduct.2
    ⟨isConnected_cartesianProduct.2 ⟨isConnected_complete 1, isConnected_complete 1⟩,
      isConnected_complete 1⟩)

/-- **`K₁ ⊕g K₂` is irreducible but not prime.** -/
theorem exists_irreducible_not_prime : ∃ p : IsoGraph, Irreducible p ∧ ¬ Prime p :=
  IsoGraph.exists_irreducible_not_prime (fun _ _ ↦ rfl) rfl V_cartesianProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Graphs do not factor uniquely** into irreducibles for the cartesian product. -/
theorem not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid IsoGraph :=
  not_uniqueFactorizationMonoid_of_V (fun _ _ ↦ rfl) rfl V_cartesianProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Two different factorisations of `K₁ ⊕g Q₁ ⊕g Q₂ ⊕g Q₃ ⊕g Q₄ ⊕g Q₅` into irreducibles**, the
`Qₖ` being the hypercubes.  The graph is disconnected; Sabidussi and Vizing proved that connected
graphs do factor uniquely. -/
theorem exists_factorisations_ne :
    ∃ f g : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ (∀ b ∈ g, Irreducible b) ∧
      f.prod = g.prod ∧ f ≠ g :=
  IsoGraph.exists_factorisations_ne (fun _ _ ↦ rfl) rfl rfl V_cartesianProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Every graph with a vertex is a product of irreducibles.** -/
theorem exists_multiset_prod_eq {a : IsoGraph} (ha : a ≠ 0) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a :=
  IsoGraph.exists_multiset_prod_eq rfl rfl V_cartesianProduct ha

end IsoGraph.Semiring

namespace IsoGraph.StrongSemiring

/-- **The one-vertex graph is the only unit.** -/
theorem isUnit_iff (G : IsoGraph) : IsUnit G ↔ G.V = 1 := isUnit_iff_V rfl V_strongProduct G

/-- **Divisibility is well-founded**, so every graph on at least two vertices is a product of
irreducibles. -/
scoped instance instWfDvdMonoid : WfDvdMonoid IsoGraph :=
  wfDvdMonoid_of_V rfl rfl V_strongProduct

/-- **The graph semiring is local**, the one-vertex graph being its only unit. -/
scoped instance instIsLocalRing : IsLocalRing IsoGraph :=
  isLocalRing_of_V (fun _ _ ↦ rfl) rfl V_strongProduct

/-- **The graph semiring is not Bézout.** -/
theorem not_isBezout : ¬ IsBezout IsoGraph :=
  not_isBezout_of_V (fun _ _ ↦ rfl) rfl V_strongProduct

/-- **The graph semiring is not a principal ideal ring.** -/
theorem not_isPrincipalIdealRing : ¬ IsPrincipalIdealRing IsoGraph :=
  not_isPrincipalIdealRing_of_V (fun _ _ ↦ rfl) rfl V_strongProduct

/-- **The graph semiring is not Noetherian.** -/
theorem not_isNoetherianRing : ¬ IsNoetherianRing IsoGraph :=
  not_isNoetherianRing_of_V (fun _ _ ↦ rfl) rfl V_strongProduct

/-- The strong cube of `K₂`, which is `K₈`, is connected. -/
private theorem cube_connected :
    ((complete 2 : IsoGraph) * complete 2 * complete 2).numComponents = 1 :=
  (numComponents_eq_one_iff _).2 (isConnected_strongProduct
    (isConnected_strongProduct (isConnected_complete 1) (isConnected_complete 1))
    (isConnected_complete 1))

/-- **`K₁ ⊕g K₂` is irreducible but not prime.** -/
theorem exists_irreducible_not_prime : ∃ p : IsoGraph, Irreducible p ∧ ¬ Prime p :=
  IsoGraph.exists_irreducible_not_prime (fun _ _ ↦ rfl) rfl V_strongProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Graphs do not factor uniquely** into irreducibles for the strong product. -/
theorem not_uniqueFactorizationMonoid : ¬ UniqueFactorizationMonoid IsoGraph :=
  not_uniqueFactorizationMonoid_of_V (fun _ _ ↦ rfl) rfl V_strongProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Two different factorisations of `K₁ ⊕g Q₁ ⊕g Q₂ ⊕g Q₃ ⊕g Q₄ ⊕g Q₅` into irreducibles**, the
`Qₖ` being the hypercubes.  The graph is disconnected; Sabidussi and Vizing proved that connected
graphs do factor uniquely. -/
theorem exists_factorisations_ne :
    ∃ f g : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ (∀ b ∈ g, Irreducible b) ∧
      f.prod = g.prod ∧ f ≠ g :=
  IsoGraph.exists_factorisations_ne (fun _ _ ↦ rfl) rfl rfl V_strongProduct (complete 2)
    (V_complete 2) cube_connected

/-- **Every graph with a vertex is a product of irreducibles.** -/
theorem exists_multiset_prod_eq {a : IsoGraph} (ha : a ≠ 0) :
    ∃ f : Multiset IsoGraph, (∀ b ∈ f, Irreducible b) ∧ f.prod = a :=
  IsoGraph.exists_multiset_prod_eq rfl rfl V_strongProduct ha

end IsoGraph.StrongSemiring
