import IsoGraph.Invariants.Fractional

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The fractional chromatic number of a product

`IsoGraph/Invariants/Fractional.lean` settles `α_f` on the disjoint union, the join and the
strong, lexicographic and cartesian products, and `χ_f` on those of them whose complement is
again a product.  What it leaves untouched is the tensor (categorical) product `G ⊗ H`, whose
complement is nothing recognisable, and which is where the interesting question lives:
Hedetniemi's conjecture asks whether `χ(G ⊗ H) = min (χ G) (χ H)`.  For `χ` the answer is no
(Shitov, 2019); for `χ_f` the answer is yes (Zhu, 2011), and that theorem is the point of this
file.

Everything here has to be produced by exhibiting *weightings*.  `χ_f` is defined in this library
as the value of the packing program on the complement — the fractional *clique* number — and no
general strong duality is available, so a lower bound on `χ_f` comes from a feasible weighting and
an upper bound from a bound on every clique of the complement.  Nowhere below is a fractional
*colouring* used.

The tool the easy half is built from is homomorphism monotonicity.  A homomorphism `f : G → H`
acts on the packing program by pushing a weighting `w` of `G` forward to `w' b = ∑_{f a = b} w a`:
totals are preserved, and the preimage of an independent set of `H` is an independent set of `G`,
so feasibility is preserved too.  That is `CGraph.fracChromNum_le_of_hom`, a strict strengthening
of `CGraph.fracChromNum_le_of_injective`, which asks the map to be injective as well.  Its
`α_f`-level form, `CGraph.fracIndepNum_le_of_cliquePreimage`, is stated for any map whose
preimages of cliques are cliques.

What is proved here:

| statement | name |
| --- | --- |
| `G → H` implies `χ_f(G) ≤ χ_f(H)` | `CGraph.fracChromNum_le_of_hom` |
| `χ_f(G ⊗ H) ≤ min (χ_f G) (χ_f H)` | `CGraph.fracChromNum_tensorProduct_le_min` |
| `min (χ_f G) (χ_f H) ≤ χ_f(G ⊗ H)` | `CGraph.min_fracChromNum_le_fracChromNum_tensorProduct` |
| `χ_f(G ⊗ H) = min (χ_f G) (χ_f H)` | `CGraph.fracChromNum_tensorProduct` |
| `G → H` implies `χ_f(G ⊗ H) = χ_f(G)` | `CGraph.fracChromNum_tensorProduct_of_hom` |
| `max (χ_f G) (χ_f H) ≤ χ_f(G □ H)` | `CGraph.max_fracChromNum_le_fracChromNum_cartesianProduct` |

## Zhu's theorem

The easy half is the pair of projections `G ⊗ H → G` and `G ⊗ H → H`, which are homomorphisms by
the very definition of the tensor product.  The hard half is Zhu, *The fractional version of
Hedetniemi's conjecture is true*, European J. Combin. 32 (2011) 1168–1175.  The argument
formalised below follows his, in a form that never needs an induced subgraph:

* the closed-neighbourhood lemma (`CGraph.sum_mul_fracChromNum_le`, private) says that for a
  feasible weighting `f` of `Gᶜ` and an independent set `X` of `G`,
  `f(X)·χ_f(G) ≤ f(N[X]) + (χ_f(G) − f(V))`.  Zhu states it for a *maximum* fractional clique, so
  that the last bracket vanishes; keeping the error term costs nothing and avoids having to know
  that the supremum is attained.  It is proved by feeding the weighting "`f` off `N[X]`, zero on
  it" to `CGraph.sum_le_mul_fracIndepNum_rat`, the point being that `X ∪ (K \ N[X])` is again an
  independent set whenever `K` is;
* the partition lemma (`CGraph.key_tensor`, private) splits an independent set `U` of `G ⊗ H` into
  the part `A` no other vertex of `U` in the same row is `G`-adjacent to, and the rest `B`.  Every
  row fibre of `A` is independent in `G`, every column fibre of `B` is independent in `H`, and —
  the combinatorial heart — the two "inflated" sets `{(x,y) : x ∈ N_G[A(y)]}` and
  `{(x,y) : y ∈ N_H[B(x)]}` are disjoint.  Applying the closed-neighbourhood lemma fibre by fibre
  and adding up bounds the weight of `U` under `(x,y) ↦ g x · h y`;
* the bound on cliques of `(G ⊗ H)ᶜ` that comes out is then fed to
  `CGraph.sum_le_mul_fracIndepNum`, which turns it into an inequality relating `∑ g`, `∑ h` and
  `χ_f(G ⊗ H)` (`CGraph.tensor_ineq`, private);
* that inequality is affine in `∑ g` for fixed `h`, so a single `csSup` step (through
  `CGraph.fracIndepNum_le`) replaces `∑ g` by `χ_f(G)`, and a second one replaces `∑ h` by
  `χ_f(H)`.  No `ε` is needed, and no supremum has to be attained.

## The cartesian product

Only one inequality is here.  Each embedding `u ↦ (u, v₀)` is a homomorphism, so
`max (χ_f G) (χ_f H) ≤ χ_f(G □ H)`; the reverse inequality is the fractional form of Sabidussi's
`χ(G □ H) = max (χ G) (χ H)`, whose proof is a *colouring* of the product and so lives on the
covering side of the linear program, which this library does not have.  It is therefore missing,
and `χ_f(G □ H) = max (χ_f G) (χ_f H)` is *not* proved here.
-/

set_option autoImplicit false

open Finset

namespace CGraph

/-! ## Pushing a weighting forward

A map `f : G.V → H.V` carries a weighting of `G` to a weighting of `H` by summing over the
fibres.  The total is unchanged, and the weight `f` puts on a set `K` of vertices of `H` is the
weight the original puts on `f ⁻¹' K`; so the pushforward is feasible as soon as the preimage of
every clique of `H` is a clique of `G`. -/

/-- The pushforward of the weighting `x` of `G` along `f`: the weight of a vertex of `H` is the
total weight of its fibre. -/
private def pushforward {G H : CGraph} (f : G.V → H.V) (x : G.V → ℚ) (b : H.V) : ℚ :=
  ∑ a ∈ Finset.univ.filter (fun a ↦ f a = b), x a

/-- Summing the pushforward over all of `H` recovers the total weight, since the fibres of `f`
partition the vertices of `G`. -/
private theorem sum_pushforward {G H : CGraph} (f : G.V → H.V) (x : G.V → ℚ) :
    ∑ b, pushforward f x b = ∑ a, x a :=
  Finset.sum_fiberwise _ _ _

/-- The pushforward weight of a set `K` of vertices of `H` is the original weight of its
preimage. -/
private theorem sum_pushforward_mem {G H : CGraph} (f : G.V → H.V) (x : G.V → ℚ)
    (K : Finset H.V) :
    ∑ b ∈ K, pushforward f x b = ∑ a ∈ Finset.univ.filter (fun a ↦ f a ∈ K), x a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := f)
    (s := Finset.univ.filter (fun a ↦ f a ∈ K)) (t := K)
    (fun a ha ↦ (Finset.mem_filter.1 ha).2) x]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  unfold pushforward
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h ↦ ⟨h ▸ hb, h⟩, fun h ↦ h.2⟩

/-- **A map whose preimages of cliques are cliques cannot lower `α_f`.**  Push a feasible
weighting of `G` forward along `f`: the total is unchanged, and the weight landing on a clique
`K` of `H` is the weight of the clique `f ⁻¹' K` of `G`, hence at most one.

No injectivity is asked for, which is what separates this from
`CGraph.fracIndepNum_le_of_injective`; read on the complements it becomes homomorphism
monotonicity of `χ_f`. -/
theorem fracIndepNum_le_of_cliquePreimage {G H : CGraph} (f : G.V → H.V)
    (hf : ∀ K : Finset H.V, H.IsCliqueOn K →
      G.IsCliqueOn (Finset.univ.filter fun a ↦ f a ∈ K)) :
    G.fracIndepNum ≤ H.fracIndepNum := by
  classical
  refine fracIndepNum_le fun x hx ↦ ?_
  have hfeas : H.IsFracIndep (pushforward f x) := by
    refine ⟨fun b ↦ Finset.sum_nonneg fun a _ ↦ hx.nonneg a, fun K hK ↦ ?_⟩
    rw [sum_pushforward_mem f x K]
    exact hx.sum_le (hf K hK)
  have := le_fracIndepNum hfeas
  rwa [sum_pushforward f x] at this

/-- **A graph homomorphism cannot lower `χ_f`.**  If `f : G.V → H.V` carries edges to edges then
`χ_f(G) ≤ χ_f(H)`.

In the packing formulation this is the previous lemma read on the complements: the preimage of an
independent set `I` of `H` is independent in `G`, because two adjacent vertices of `G` are carried
to two adjacent — in particular distinct — vertices of `H`, which cannot both lie in `I`. -/
theorem fracChromNum_le_of_hom {G H : CGraph} (f : G.V → H.V)
    (hadj : ∀ u v : G.V, G.Adj u v = true → H.Adj (f u) (f v) = true) :
    G.fracChromNum ≤ H.fracChromNum := by
  classical
  refine fracIndepNum_le_of_cliquePreimage (G := Gᶜ) (H := Hᶜ) f fun K hK ↦ ?_
  intro a ha b hb hab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [compl_adj]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true']
  refine ⟨hab, ?_⟩
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  have hHadj := hadj a b hcon
  rcases eq_or_ne (f a) (f b) with he | hne
  · rw [he, adj_self] at hHadj
    exact Bool.noConfusion hHadj
  · have := hK _ ha _ hb hne
    rw [compl_adj] at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    rw [hHadj] at this
    exact Bool.noConfusion this.2

/-! ## The tensor product: the easy half of Hedetniemi

An edge of `G ⊗ H` is an edge in each coordinate, so both projections are homomorphisms and
`χ_f(G ⊗ H)` is at most each of `χ_f(G)` and `χ_f(H)`.  This is the direction that holds for `χ`
too, and for the same reason. -/

/-- The first projection `G ⊗ H → G` is a homomorphism. -/
theorem fracChromNum_tensorProduct_le_left (G H : CGraph) :
    (G ⊗g H).fracChromNum ≤ G.fracChromNum :=
  fracChromNum_le_of_hom (G := G ⊗g H) (H := G) Prod.fst fun p q h ↦ by
    rw [tensorProduct_adj, Bool.and_eq_true] at h
    exact h.1

/-- The second projection `G ⊗ H → H` is a homomorphism. -/
theorem fracChromNum_tensorProduct_le_right (G H : CGraph) :
    (G ⊗g H).fracChromNum ≤ H.fracChromNum :=
  fracChromNum_le_of_hom (G := G ⊗g H) (H := H) Prod.snd fun p q h ↦ by
    rw [tensorProduct_adj, Bool.and_eq_true] at h
    exact h.2

/-- **`χ_f(G ⊗ H) ≤ min (χ_f G) (χ_f H)`**, the easy half of the fractional Hedetniemi conjecture:
the two projections out of a tensor product are homomorphisms.

The other half is Zhu's theorem, `CGraph.min_fracChromNum_le_fracChromNum_tensorProduct`; the two
together are `CGraph.fracChromNum_tensorProduct`. -/
theorem fracChromNum_tensorProduct_le_min (G H : CGraph) :
    (G ⊗g H).fracChromNum ≤ min G.fracChromNum H.fracChromNum :=
  le_min (fracChromNum_tensorProduct_le_left G H) (fracChromNum_tensorProduct_le_right G H)

/-! ## The tensor product: Zhu's theorem

The hard half.  The two private lemmas below are Zhu's Lemma 3 and Lemma 4; the module docstring
describes the shape of the argument.  Everything is phrased in the packing program, so the only
facts about `χ_f` used are `CGraph.sum_le_mul_fracIndepNum_rat`,
`CGraph.sum_le_mul_fracIndepNum` and `CGraph.fracIndepNum_le`. -/

/-- The closed neighbourhood of a set of vertices: the set itself together with everything
adjacent to a member of it. -/
private def closedNbhd (G : CGraph) (X : Finset G.V) : Finset G.V :=
  Finset.univ.filter (fun v ↦ v ∈ X ∨ ∃ x ∈ X, G.Adj x v = true)

/-- Membership in a closed neighbourhood, unfolded. -/
private theorem mem_closedNbhd {G : CGraph} {X : Finset G.V} {v : G.V} :
    v ∈ G.closedNbhd X ↔ v ∈ X ∨ ∃ x ∈ X, G.Adj x v = true := by
  simp [closedNbhd]

/-- A set is contained in its closed neighbourhood. -/
private theorem subset_closedNbhd {G : CGraph} (X : Finset G.V) : X ⊆ G.closedNbhd X :=
  fun _ hv ↦ mem_closedNbhd.2 (Or.inl hv)

/-- **Zhu's closed-neighbourhood lemma.**  For a feasible weighting `f` of `Gᶜ` — that is, a
fractional clique of `G` — and an independent set `X` of `G`,
`f(X) · χ_f(G) ≤ f(N[X]) + (χ_f(G) − f(V))`.

Zhu states this for a maximum fractional clique, where the error term `χ_f(G) − f(V)` vanishes;
carrying it along costs nothing and means the supremum never has to be attained.  The proof
deletes `N[X]` from `f`: whatever is left weighs at most `1 − f(X)` on any independent set `K`,
because `X ∪ (K \ N[X])` is itself independent — no vertex of `K` outside `N[X]` is adjacent to a
vertex of `X` — and so `CGraph.sum_le_mul_fracIndepNum_rat` bounds the leftover total by
`(1 − f(X)) · χ_f(G)`. -/
private theorem sum_mul_fracChromNum_le {G : CGraph} {f : G.V → ℚ} (hf : Gᶜ.IsFracIndep f)
    {X : Finset G.V} (hX : Gᶜ.IsCliqueOn X) :
    ((∑ v ∈ X, f v : ℚ) : ℝ) * G.fracChromNum ≤
      ((∑ v ∈ G.closedNbhd X, f v : ℚ) : ℝ) +
        (G.fracChromNum - ((∑ v, f v : ℚ) : ℝ)) := by
  classical
  set p : ℚ := 1 - ∑ v ∈ X, f v with hp
  set z : G.V → ℚ := fun v ↦ if v ∈ G.closedNbhd X then 0 else f v with hz
  have hznn : ∀ v, 0 ≤ z v := by
    intro v; rw [hz]; dsimp only; split_ifs with hv
    · exact le_rfl
    · exact hf.nonneg v
  have hzc : ∀ K : Finset G.V, Gᶜ.IsCliqueOn K → ∑ v ∈ K, z v ≤ p := by
    intro K hK
    set K' : Finset G.V := K.filter (fun v ↦ v ∉ G.closedNbhd X) with hK'
    have hsum : ∑ v ∈ K, z v = ∑ v ∈ K', f v := by
      rw [hK', Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      by_cases h : v ∈ G.closedNbhd X <;> simp [hz, h]
    have hdisj : Disjoint X K' := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      exact (Finset.mem_filter.1 hv').2 (subset_closedNbhd X hv)
    have hcl : Gᶜ.IsCliqueOn (X ∪ K') := by
      intro a ha b hb hab
      rcases Finset.mem_union.1 ha with ha' | ha' <;>
        rcases Finset.mem_union.1 hb with hb' | hb'
      · exact hX a ha' b hb' hab
      · -- a ∈ X, b ∉ N[X]
        rw [Finset.mem_filter] at hb'
        rw [compl_adj]
        simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true']
        refine ⟨hab, ?_⟩
        by_contra hcon
        rw [Bool.not_eq_false] at hcon
        exact hb'.2 (mem_closedNbhd.2 (Or.inr ⟨a, ha', hcon⟩))
      · rw [Finset.mem_filter] at ha'
        rw [compl_adj]
        simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true']
        refine ⟨hab, ?_⟩
        by_contra hcon
        rw [Bool.not_eq_false] at hcon
        exact ha'.2 (mem_closedNbhd.2 (Or.inr ⟨b, hb', G.symm b a ▸ hcon⟩))
      · exact hK a (Finset.mem_filter.1 ha').1 b (Finset.mem_filter.1 hb').1 hab
    have hle := hf.sum_le hcl
    have hsplit : ∑ v ∈ X ∪ K', f v = (∑ v ∈ X, f v) + ∑ v ∈ K', f v :=
      Finset.sum_union hdisj
    have hle2 := hsplit.symm.trans_le hle
    rw [hsum, hp]
    linarith
  have hmain : ((∑ v : G.V, z v : ℚ) : ℝ) ≤ (p : ℝ) * G.fracChromNum :=
    sum_le_mul_fracIndepNum_rat (G := Gᶜ) (x := z) hznn hzc
  have hzsum : ∑ v, z v = (∑ v, f v) - ∑ v ∈ G.closedNbhd X, f v := by
    rw [eq_sub_iff_add_eq, hz]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v ↦ v ∈ G.closedNbhd X) f]
    have h1 : ∑ v ∈ Finset.univ.filter (fun v ↦ v ∈ G.closedNbhd X), f v
        = ∑ v ∈ G.closedNbhd X, f v := by
      congr 1
      ext v
      simp
    have h2 : ∑ v : G.V, (if v ∈ G.closedNbhd X then (0 : ℚ) else f v)
        = ∑ v ∈ Finset.univ.filter (fun v ↦ ¬ v ∈ G.closedNbhd X), f v := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      split_ifs with h <;> rfl
    rw [h1, h2]
    ring
  rw [hzsum, hp] at hmain
  have hc : ((1 - ∑ v ∈ X, f v : ℚ) : ℝ) = 1 - ((∑ v ∈ X, f v : ℚ) : ℝ) := by push_cast; ring
  rw [Rat.cast_sub, hc, sub_mul, one_mul] at hmain
  linarith
/-- Sums over the vertices of a tensor product, fibre by fibre.  Restated here rather than
imported: the corresponding helper in `IsoGraph/Invariants/Fractional.lean` is private. -/
private theorem sum_univ_tensor {G H : CGraph} (z : (G ⊗g H).V → ℚ) :
    ∑ p, z p = ∑ x, ∑ y, z (x, y) :=
  (Finset.sum_univ_inst_eq _ (instFintypeProd G.V H.V) z).trans (Fintype.sum_prod_type z)

/-- **Zhu's partition lemma.**  Let `g` and `h` be fractional cliques of `G` and `H`, write
`r_g = ∑ g` and `r_h = ∑ h`, and let `U` be an independent set of `G ⊗ H`.  If
`χ_f(H) ≤ χ_f(G)` then the weight of `U` under `(x, y) ↦ g x · h y` satisfies

`weight(U) · χ_f(H) ≤ χ_f(G) · r_h + χ_f(H) · r_g − r_g · r_h`.

Split `U` into `A`, the vertices `(x, y)` such that no `(x', y) ∈ U` has `x` adjacent to `x'`,
and `B`, the rest.  Each row fibre `A(y)` is independent in `G` by construction.  Each column
fibre `B(x)` is independent in `H`: if `(x, y)` and `(x, y')` both lay in `B` with `y` adjacent to
`y'`, the witness `(x', y) ∈ U` for `(x, y) ∈ B` would be adjacent to `(x, y')` in `G ⊗ H`.

The combinatorial heart is that `{(x, y) : x ∈ N_G[A(y)]}` and `{(x, y) : y ∈ N_H[B(x)]}` are
disjoint; each of the four ways a vertex could lie in both produces two adjacent vertices of `U`.
The closed-neighbourhood lemma applied to every row fibre and every column fibre, weighted by `h`
and by `g` respectively and added up, then gives the claim, because the two inflated sets weigh at
most `r_g · r_h` together. -/
private theorem key_tensor {G H : CGraph} {g : G.V → ℚ} {h : H.V → ℚ}
    (hg : Gᶜ.IsFracIndep g) (hh : Hᶜ.IsFracIndep h)
    (hWle : H.fracChromNum ≤ G.fracChromNum)
    {U : Finset (G.V × H.V)} (hU : (G ⊗g H)ᶜ.IsCliqueOn U) :
    ((∑ p ∈ U, g p.1 * h p.2 : ℚ) : ℝ) * H.fracChromNum ≤
      G.fracChromNum * ((∑ v, h v : ℚ) : ℝ)
        + H.fracChromNum * ((∑ u, g u : ℚ) : ℝ)
        - ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ) := by
  classical
  -- `U` is an independent set of the tensor product.
  have hUind : ∀ p ∈ U, ∀ q ∈ U, G.Adj p.1 q.1 = true → H.Adj p.2 q.2 = true → False := by
    intro p hp q hq h1 h2
    by_cases hpq : p = q
    · subst hpq; exact G.loopless p.1 h1
    · have hc := hU p hp q hq hpq
      rw [compl_adj] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true'] at hc
      have h3 : (G ⊗g H).Adj p q = true := by rw [tensorProduct_adj, h1, h2]; rfl
      rw [h3] at hc
      exact Bool.noConfusion hc.2
  obtain ⟨R, hRspec⟩ : ∃ R : G.V → H.V → Prop,
      ∀ x y, R x y ↔ ∀ q ∈ U, q.2 = y → G.Adj x q.1 = false :=
    ⟨_, fun _ _ ↦ Iff.rfl⟩
  obtain ⟨Ay, hAyMem⟩ : ∃ Ay : H.V → Finset G.V, ∀ x y, x ∈ Ay y ↔ ((x, y) ∈ U ∧ R x y) :=
    ⟨fun y ↦ Finset.univ.filter (fun x ↦ (x, y) ∈ U ∧ R x y), by intro x y; simp⟩
  obtain ⟨Bx, hBxMem⟩ : ∃ Bx : G.V → Finset H.V, ∀ y x, y ∈ Bx x ↔ ((x, y) ∈ U ∧ ¬ R x y) :=
    ⟨fun x ↦ Finset.univ.filter (fun y ↦ (x, y) ∈ U ∧ ¬ R x y), by intro y x; simp⟩
  -- Every row fibre of `A` is independent in `G`.
  have hAyClique : ∀ y, Gᶜ.IsCliqueOn (Ay y) := by
    intro y x hx x' hx' hne
    rw [compl_adj]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true']
    refine ⟨hne, ?_⟩
    obtain ⟨_, hxR⟩ := (hAyMem x y).1 hx
    obtain ⟨hx'U, _⟩ := (hAyMem x' y).1 hx'
    exact (hRspec x y).1 hxR (x', y) hx'U rfl
  -- Every column fibre of `B` is independent in `H`.
  have hBxClique : ∀ x, Hᶜ.IsCliqueOn (Bx x) := by
    intro x y hy y' hy' hne
    rw [compl_adj]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Bool.not_eq_true']
    refine ⟨hne, ?_⟩
    obtain ⟨_, hyR⟩ := (hBxMem y x).1 hy
    obtain ⟨hy'U, _⟩ := (hBxMem y' x).1 hy'
    rw [hRspec] at hyR
    push Not at hyR
    obtain ⟨q, hqU, hq2, hq3⟩ := hyR
    by_contra hcon
    refine hUind q hqU (x, y') hy'U ?_ ?_
    · rw [G.symm]
      simpa using hq3
    · show H.Adj q.2 y' = true
      rw [hq2]
      simpa using hcon
  -- The closed neighbourhoods of the two families never meet.
  have hdisj : ∀ (x : G.V) (y : H.V),
      ¬ (x ∈ G.closedNbhd (Ay y) ∧ y ∈ H.closedNbhd (Bx x)) := by
    rintro x y ⟨h1, h2⟩
    rcases mem_closedNbhd.1 h1 with hA1 | ⟨x₀, hx₀A, hx₀adj⟩ <;>
      rcases mem_closedNbhd.1 h2 with hB1 | ⟨y₀, hy₀B, hy₀adj⟩
    · exact ((hBxMem y x).1 hB1).2 ((hAyMem x y).1 hA1).2
    · obtain ⟨hxU, _⟩ := (hAyMem x y).1 hA1
      obtain ⟨_, hy₀R⟩ := (hBxMem y₀ x).1 hy₀B
      rw [hRspec] at hy₀R
      push Not at hy₀R
      obtain ⟨q, hqU, hq2, hq3⟩ := hy₀R
      refine hUind (x, y) hxU q hqU (by simpa using hq3) ?_
      show H.Adj y q.2 = true
      rw [hq2, H.symm]
      exact hy₀adj
    · obtain ⟨_, hx₀R⟩ := (hAyMem x₀ y).1 hx₀A
      obtain ⟨hxU, _⟩ := (hBxMem y x).1 hB1
      rw [(hRspec x₀ y).1 hx₀R (x, y) hxU rfl] at hx₀adj
      exact Bool.noConfusion hx₀adj
    · obtain ⟨hx₀U, _⟩ := (hAyMem x₀ y).1 hx₀A
      obtain ⟨hxU, _⟩ := (hBxMem y₀ x).1 hy₀B
      refine hUind (x₀, y) hx₀U (x, y₀) hxU hx₀adj ?_
      show H.Adj y y₀ = true
      rw [H.symm]
      exact hy₀adj
  -- Indicator expansions of the fibre sums.
  have hExpG : ∀ K : Finset G.V, ∑ x ∈ K, g x = ∑ x : G.V, (if x ∈ K then g x else 0) := by
    intro K; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hExpH : ∀ K : Finset H.V, ∑ y ∈ K, h y = ∑ y : H.V, (if y ∈ K then h y else 0) := by
    intro K; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hAyExp : ∀ y : H.V, ∑ x ∈ Ay y, g x
      = ∑ x : G.V, (if (x, y) ∈ U ∧ R x y then g x else 0) := fun y ↦
    (hExpG (Ay y)).trans (Finset.sum_congr rfl fun x _ ↦ if_congr (hAyMem x y) rfl rfl)
  have hBxExp : ∀ x : G.V, ∑ y ∈ Bx x, h y
      = ∑ y : H.V, (if (x, y) ∈ U ∧ ¬ R x y then h y else 0) := fun x ↦
    (hExpH (Bx x)).trans (Finset.sum_congr rfl fun y _ ↦ if_congr (hBxMem y x) rfl rfl)
  -- The two families split the weight of `U`.
  have hsplitQ : (∑ y, h y * ∑ x ∈ Ay y, g x) + (∑ x, g x * ∑ y ∈ Bx x, h y)
      = ∑ p ∈ U, g p.1 * h p.2 := by
    have e0 : ∑ p ∈ U, g p.1 * h p.2
        = ∑ x : G.V, ∑ y : H.V, (if (x, y) ∈ U then g x * h y else 0) := by
      have e := sum_univ_tensor (G := G) (H := H) (fun p ↦ if p ∈ U then g p.1 * h p.2 else 0)
      rw [← e, Finset.sum_ite_mem, Finset.univ_inter]
      rfl
    have e1 : (∑ y, h y * ∑ x ∈ Ay y, g x)
        = ∑ y : H.V, ∑ x : G.V, (if (x, y) ∈ U ∧ R x y then g x * h y else 0) := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hAyExp y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by split_ifs <;> ring
    have e2 : (∑ x, g x * ∑ y ∈ Bx x, h y)
        = ∑ x : G.V, ∑ y : H.V, (if (x, y) ∈ U ∧ ¬ R x y then g x * h y else 0) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hBxExp x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> ring
    have ecomm : ∑ y : H.V, ∑ x : G.V, (if (x, y) ∈ U ∧ R x y then g x * h y else 0)
        = ∑ x : G.V, ∑ y : H.V, (if (x, y) ∈ U ∧ R x y then g x * h y else 0) :=
      Finset.sum_comm
    rw [e0, e1, e2, ecomm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    by_cases h1 : (x, y) ∈ U <;> by_cases h2 : R x y <;> simp [h1, h2]
  -- The two closed neighbourhoods are disjoint, so their weights add to at most the total.
  have hboundQ : (∑ y, h y * ∑ x ∈ G.closedNbhd (Ay y), g x)
      + (∑ x, g x * ∑ y ∈ H.closedNbhd (Bx x), h y)
      ≤ (∑ u, g u) * (∑ v, h v) := by
    have e1 : (∑ y, h y * ∑ x ∈ G.closedNbhd (Ay y), g x)
        = ∑ y : H.V, ∑ x : G.V, (if x ∈ G.closedNbhd (Ay y) then g x * h y else 0) := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hExpG (G.closedNbhd (Ay y)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by split_ifs <;> ring
    have e2' : (∑ x, g x * ∑ y ∈ H.closedNbhd (Bx x), h y)
        = ∑ x : G.V, ∑ y : H.V, (if y ∈ H.closedNbhd (Bx x) then g x * h y else 0) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hExpH (H.closedNbhd (Bx x)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> ring
    have e2 : (∑ x, g x * ∑ y ∈ H.closedNbhd (Bx x), h y)
        = ∑ y : H.V, ∑ x : G.V, (if y ∈ H.closedNbhd (Bx x) then g x * h y else 0) :=
      e2'.trans Finset.sum_comm
    have e3 : (∑ u : G.V, g u) * (∑ v : H.V, h v) = ∑ y : H.V, ∑ x : G.V, g x * h y := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_comm
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    have hnn : (0 : ℚ) ≤ g x * h y := mul_nonneg (hg.nonneg x) (hh.nonneg y)
    by_cases h1 : x ∈ G.closedNbhd (Ay y)
    · have h2 : y ∉ H.closedNbhd (Bx x) := fun hy ↦ hdisj x y ⟨h1, hy⟩
      simp [h1, h2]
    · by_cases h2 : y ∈ H.closedNbhd (Bx x) <;> simp [h1, h2, hnn]
  -- Zhu's closed-neighbourhood lemma, fibre by fibre.
  have hhsum : (∑ y : H.V, (h y : ℝ)) = ((∑ v, h v : ℚ) : ℝ) := by push_cast; ring
  have hgsum : (∑ x : G.V, (g x : ℝ)) = ((∑ u, g u : ℚ) : ℝ) := by push_cast; ring
  have hSA : (∑ y, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ)) * G.fracChromNum
      ≤ (∑ y, (h y : ℝ) * ((∑ x ∈ G.closedNbhd (Ay y), g x : ℚ) : ℝ))
        + ((∑ v, h v : ℚ) : ℝ) * (G.fracChromNum - ((∑ u, g u : ℚ) : ℝ)) := by
    have hs := Finset.sum_le_sum (fun (y : H.V) (_ : y ∈ (Finset.univ : Finset H.V)) ↦
      mul_le_mul_of_nonneg_left (sum_mul_fracChromNum_le hg (hAyClique y))
        (show (0:ℝ) ≤ (h y : ℝ) by exact_mod_cast hh.nonneg y))
    have hL : (∑ y : H.V, (h y : ℝ) * (((∑ x ∈ Ay y, g x : ℚ) : ℝ) * G.fracChromNum))
        = (∑ y : H.V, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ)) * G.fracChromNum := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ ↦ (mul_assoc _ _ _).symm
    have hR : (∑ y : H.V, (h y : ℝ) * (((∑ x ∈ G.closedNbhd (Ay y), g x : ℚ) : ℝ)
          + (G.fracChromNum - ((∑ u, g u : ℚ) : ℝ))))
        = (∑ y : H.V, (h y : ℝ) * ((∑ x ∈ G.closedNbhd (Ay y), g x : ℚ) : ℝ))
          + ((∑ v, h v : ℚ) : ℝ) * (G.fracChromNum - ((∑ u, g u : ℚ) : ℝ)) := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hhsum]
    rw [hL, hR] at hs
    exact hs
  have hSB : (∑ x, (g x : ℝ) * ((∑ y ∈ Bx x, h y : ℚ) : ℝ)) * H.fracChromNum
      ≤ (∑ x, (g x : ℝ) * ((∑ y ∈ H.closedNbhd (Bx x), h y : ℚ) : ℝ))
        + ((∑ u, g u : ℚ) : ℝ) * (H.fracChromNum - ((∑ v, h v : ℚ) : ℝ)) := by
    have hs := Finset.sum_le_sum (fun (x : G.V) (_ : x ∈ (Finset.univ : Finset G.V)) ↦
      mul_le_mul_of_nonneg_left (sum_mul_fracChromNum_le hh (hBxClique x))
        (show (0:ℝ) ≤ (g x : ℝ) by exact_mod_cast hg.nonneg x))
    have hL : (∑ x : G.V, (g x : ℝ) * (((∑ y ∈ Bx x, h y : ℚ) : ℝ) * H.fracChromNum))
        = (∑ x : G.V, (g x : ℝ) * ((∑ y ∈ Bx x, h y : ℚ) : ℝ)) * H.fracChromNum := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ ↦ (mul_assoc _ _ _).symm
    have hR : (∑ x : G.V, (g x : ℝ) * (((∑ y ∈ H.closedNbhd (Bx x), h y : ℚ) : ℝ)
          + (H.fracChromNum - ((∑ v, h v : ℚ) : ℝ))))
        = (∑ x : G.V, (g x : ℝ) * ((∑ y ∈ H.closedNbhd (Bx x), h y : ℚ) : ℝ))
          + ((∑ u, g u : ℚ) : ℝ) * (H.fracChromNum - ((∑ v, h v : ℚ) : ℝ)) := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hgsum]
    rw [hL, hR] at hs
    exact hs
  -- Casting the two rational facts to the reals.
  have hsum : (∑ y, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ))
      + (∑ x, (g x : ℝ) * ((∑ y ∈ Bx x, h y : ℚ) : ℝ))
      = ((∑ p ∈ U, g p.1 * h p.2 : ℚ) : ℝ) := by
    rw [← hsplitQ]; push_cast; ring
  have hAB : (∑ y, (h y : ℝ) * ((∑ x ∈ G.closedNbhd (Ay y), g x : ℚ) : ℝ))
      + (∑ x, (g x : ℝ) * ((∑ y ∈ H.closedNbhd (Bx x), h y : ℚ) : ℝ))
      ≤ ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ) := by
    have hc : (((∑ y, h y * ∑ x ∈ G.closedNbhd (Ay y), g x)
          + (∑ x, g x * ∑ y ∈ H.closedNbhd (Bx x), h y) : ℚ) : ℝ)
        ≤ (((∑ u, g u) * (∑ v, h v) : ℚ) : ℝ) := by exact_mod_cast hboundQ
    push_cast at hc ⊢
    linarith
  have hSAnn : (0 : ℝ) ≤ ∑ y, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ) :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (by exact_mod_cast hh.nonneg y)
      (by exact_mod_cast Finset.sum_nonneg fun x _ ↦ hg.nonneg x)
  have hkey : (∑ y, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ)) * H.fracChromNum
      ≤ (∑ y, (h y : ℝ) * ((∑ x ∈ Ay y, g x : ℚ) : ℝ)) * G.fracChromNum :=
    mul_le_mul_of_nonneg_left hWle hSAnn
  rw [← hsum, add_mul]
  nlinarith [hSA, hSB, hAB, hkey]

/-- The bilinear inequality the partition lemma yields.  Feeding the bound on cliques of
`(G ⊗ H)ᶜ` to `CGraph.sum_le_mul_fracIndepNum` — the weighting `(x, y) ↦ g x · h y` has total
`r_g · r_h` — turns it into

`r_g · r_h · χ_f(H) ≤ (χ_f(G) · r_h + χ_f(H) · r_g − r_g · r_h) · χ_f(G ⊗ H)`,

which no longer mentions the independent set. -/
private theorem tensor_ineq {G H : CGraph} (hWle : H.fracChromNum ≤ G.fracChromNum)
    (hpos : 0 < H.fracChromNum) {g : G.V → ℚ} {h : H.V → ℚ}
    (hg : Gᶜ.IsFracIndep g) (hh : Hᶜ.IsFracIndep h) :
    ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ) * H.fracChromNum
      ≤ (G.fracChromNum * ((∑ v, h v : ℚ) : ℝ) + H.fracChromNum * ((∑ u, g u : ℚ) : ℝ)
          - ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ)) * (G ⊗g H).fracChromNum := by
  have hz : ∀ K : Finset (G ⊗g H)ᶜ.V, (G ⊗g H)ᶜ.IsCliqueOn K →
      ((∑ p ∈ K, g p.1 * h p.2 : ℚ) : ℝ)
        ≤ (G.fracChromNum * ((∑ v, h v : ℚ) : ℝ) + H.fracChromNum * ((∑ u, g u : ℚ) : ℝ)
            - ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ)) / H.fracChromNum := by
    intro K hK
    rw [le_div_iff₀ hpos]
    exact key_tensor hg hh hWle hK
  have hmain : ((∑ p : (G ⊗g H).V, g p.1 * h p.2 : ℚ) : ℝ)
      ≤ ((G.fracChromNum * ((∑ v, h v : ℚ) : ℝ) + H.fracChromNum * ((∑ u, g u : ℚ) : ℝ)
            - ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ)) / H.fracChromNum)
        * (G ⊗g H).fracChromNum :=
    sum_le_mul_fracIndepNum (G := (G ⊗g H)ᶜ) (x := fun p ↦ g p.1 * h p.2)
      (fun p ↦ mul_nonneg (hg.nonneg _) (hh.nonneg _)) hz
  have htot : (∑ p : (G ⊗g H).V, g p.1 * h p.2) = (∑ u, g u) * (∑ v, h v) := by
    rw [sum_univ_tensor, Finset.sum_mul_sum]
  rw [htot] at hmain
  have hcast : (((∑ u, g u) * (∑ v, h v) : ℚ) : ℝ)
      = ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ) := by push_cast; ring
  rw [hcast] at hmain
  calc ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ) * H.fracChromNum
      ≤ (((G.fracChromNum * ((∑ v, h v : ℚ) : ℝ) + H.fracChromNum * ((∑ u, g u : ℚ) : ℝ)
            - ((∑ u, g u : ℚ) : ℝ) * ((∑ v, h v : ℚ) : ℝ)) / H.fracChromNum)
          * (G ⊗g H).fracChromNum) * H.fracChromNum :=
        mul_le_mul_of_nonneg_right hmain hpos.le
    _ = _ := by field_simp

/-- Zhu's theorem under the normalisation `0 < χ_f(H) ≤ χ_f(G)`.

The previous inequality is affine in `r_g` once `h` is fixed: it reads `r_g · a ≤ χ_f(G) · r_h · T`
with `a = r_h · χ_f(H) + r_h · T − χ_f(H) · T` and `T = χ_f(G ⊗ H)`.  If `a ≤ 0` the conclusion
`χ_f(G) · a ≤ χ_f(G) · r_h · T` is immediate from the signs; if `a > 0` it is what
`CGraph.fracIndepNum_le` gives after dividing by `a`.  Either way `r_g` may be replaced by
`χ_f(G)`, and the inequality collapses to `χ_f(G) · χ_f(H) · r_h ≤ χ_f(G) · χ_f(H) · T`.  A second
`CGraph.fracIndepNum_le`, this time over `h`, replaces `r_h` by `χ_f(H)`. -/
private theorem le_tensor_aux {G H : CGraph} (hWle : H.fracChromNum ≤ G.fracChromNum)
    (hpos : 0 < H.fracChromNum) : H.fracChromNum ≤ (G ⊗g H).fracChromNum := by
  have hT : (0 : ℝ) ≤ (G ⊗g H).fracChromNum := (G ⊗g H).zero_le_fracChromNum
  have hWG : 0 < G.fracChromNum := lt_of_lt_of_le hpos hWle
  refine fracIndepNum_le (G := Hᶜ) fun k hk ↦ ?_
  show ((∑ v : H.V, k v : ℚ) : ℝ) ≤ (G ⊗g H).fracChromNum
  have hv0 : (0 : ℝ) ≤ ((∑ v : H.V, k v : ℚ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun v _ ↦ hk.nonneg v
  have hall : ∀ g : G.V → ℚ, Gᶜ.IsFracIndep g →
      ((∑ u, g u : ℚ) : ℝ) * (((∑ v : H.V, k v : ℚ) : ℝ) * H.fracChromNum
          + ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum
          - H.fracChromNum * (G ⊗g H).fracChromNum)
        ≤ G.fracChromNum * ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum := by
    intro g hgf
    nlinarith [tensor_ineq hWle hpos hgf hk]
  have hga : G.fracChromNum * (((∑ v : H.V, k v : ℚ) : ℝ) * H.fracChromNum
        + ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum
        - H.fracChromNum * (G ⊗g H).fracChromNum)
      ≤ G.fracChromNum * ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum := by
    by_cases hsign : ((∑ v : H.V, k v : ℚ) : ℝ) * H.fracChromNum
        + ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum
        - H.fracChromNum * (G ⊗g H).fracChromNum ≤ 0
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hWG.le hsign)
        (mul_nonneg (mul_nonneg hWG.le hv0) hT)
    · push Not at hsign
      have hle : G.fracChromNum
          ≤ (G.fracChromNum * ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum)
            / (((∑ v : H.V, k v : ℚ) : ℝ) * H.fracChromNum
              + ((∑ v : H.V, k v : ℚ) : ℝ) * (G ⊗g H).fracChromNum
              - H.fracChromNum * (G ⊗g H).fracChromNum) := by
        refine fracIndepNum_le (G := Gᶜ) fun g hgf ↦ ?_
        rw [le_div_iff₀ hsign]
        exact hall g hgf
      rwa [le_div_iff₀ hsign] at hle
  have hfin : G.fracChromNum * H.fracChromNum * ((∑ v : H.V, k v : ℚ) : ℝ)
      ≤ G.fracChromNum * H.fracChromNum * (G ⊗g H).fracChromNum := by nlinarith [hga]
  exact le_of_mul_le_mul_left hfin (mul_pos hWG hpos)

/-- **Zhu's theorem: `min (χ_f G) (χ_f H) ≤ χ_f(G ⊗ H)`**, the hard half of the fractional
Hedetniemi conjecture (Zhu, *The fractional version of Hedetniemi's conjecture is true*, European
J. Combin. 32 (2011) 1168–1175).

The two degenerate cases are trivial — if the smaller of the two is zero there is nothing to prove
— and the two orderings of `χ_f(G)` and `χ_f(H)` are exchanged by
`CGraph.Iso.tensorProductComm`. -/
theorem min_fracChromNum_le_fracChromNum_tensorProduct (G H : CGraph) :
    min G.fracChromNum H.fracChromNum ≤ (G ⊗g H).fracChromNum := by
  rcases le_total H.fracChromNum G.fracChromNum with hle | hle
  · rw [min_eq_right hle]
    rcases eq_or_lt_of_le H.zero_le_fracChromNum with h0 | h0
    · rw [← h0]; exact (G ⊗g H).zero_le_fracChromNum
    · exact le_tensor_aux hle h0
  · rw [min_eq_left hle]
    rcases eq_or_lt_of_le G.zero_le_fracChromNum with h0 | h0
    · rw [← h0]; exact (G ⊗g H).zero_le_fracChromNum
    · calc G.fracChromNum ≤ (H ⊗g G).fracChromNum := le_tensor_aux hle h0
        _ = (G ⊗g H).fracChromNum := Iso.fracChromNum_eq (Iso.tensorProductComm H G)

/-! ## The tensor product: consequences

With the equality in hand the only thing left to say about a particular pair of factors is which
of the two fractional chromatic numbers the minimum is. -/

/-- **The fractional Hedetniemi equality, `χ_f(G ⊗ H) = min (χ_f G) (χ_f H)`.**  The easy half is
the two projections, the hard half is Zhu's theorem. -/
@[simp] theorem fracChromNum_tensorProduct (G H : CGraph) :
    (G ⊗g H).fracChromNum = min G.fracChromNum H.fracChromNum :=
  le_antisymm (fracChromNum_tensorProduct_le_min G H)
    (min_fracChromNum_le_fracChromNum_tensorProduct G H)

/-- **A homomorphism `G → H` pins the minimum down**: `χ_f(G ⊗ H) = χ_f(G)`, with no `min` left,
because a homomorphism forces `χ_f(G) ≤ χ_f(H)`. -/
theorem fracChromNum_tensorProduct_of_hom {G H : CGraph} (f : G.V → H.V)
    (hf : ∀ u v : G.V, G.Adj u v = true → H.Adj (f u) (f v) = true) :
    (G ⊗g H).fracChromNum = G.fracChromNum := by
  rw [fracChromNum_tensorProduct, min_eq_left (fracChromNum_le_of_hom f hf)]

/-- **`χ_f(G ⊗ G) = χ_f(G)`**: the diagonal of `G ⊗ G` is a copy of `G`, and the identity is a
homomorphism the other way. -/
theorem fracChromNum_tensorProduct_self (G : CGraph) :
    (G ⊗g G).fracChromNum = G.fracChromNum :=
  fracChromNum_tensorProduct_of_hom (G := G) (H := G) id fun _ _ h ↦ h

/-! ## The cartesian product

Sabidussi's `χ(G □ H) = max (χ G) (χ H)` has a fractional counterpart, but only one of its two
inequalities is available here.  Each embedding of a factor as a row or a column of the product
is a homomorphism, which gives `max ≤ χ_f(G □ H)`.  The reverse inequality is proved by
*colouring* `(u, v)` with the sum of the colours of `u` and `v`, and a fractional colouring is a
solution of the covering program, which this library does not relate to the packing program that
defines `χ_f`; so it is missing, and the equality is not stated. -/

/-- **A row of a cartesian product is a copy of `G`**, so `χ_f(G) ≤ χ_f(G □ H)`.  The embedding
`u ↦ (u, v₀)` is a homomorphism: it moves in the first coordinate and stands still in the
second. -/
theorem fracChromNum_le_fracChromNum_cartesianProduct (G H : CGraph) (v₀ : H.V) :
    G.fracChromNum ≤ (G □g H).fracChromNum :=
  fracChromNum_le_of_hom (G := G) (H := G □g H) (fun u ↦ (u, v₀)) fun u v h ↦ by
    rw [cartesianProduct_adj]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨h, trivial⟩

/-- **`max (χ_f G) (χ_f H) ≤ χ_f(G □ H)`**, the half of the fractional Sabidussi equality that
the packing program can see.  Both factors must be inhabited, or the product is empty and its
`χ_f` is zero. -/
theorem max_fracChromNum_le_fracChromNum_cartesianProduct (G H : CGraph) (u₀ : G.V) (v₀ : H.V) :
    max G.fracChromNum H.fracChromNum ≤ (G □g H).fracChromNum := by
  refine max_le (fracChromNum_le_fracChromNum_cartesianProduct G H v₀) ?_
  rw [← Iso.fracChromNum_eq (Iso.cartesianProductComm H G)]
  exact fracChromNum_le_fracChromNum_cartesianProduct H G u₀

end CGraph
