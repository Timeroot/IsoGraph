import IsoGraph.Algebra.Semiring

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Cancellation

Cancellation in the graph semiring: when `A + C = B + C` or `A * C = B * C` forces `A = B`.
-/

namespace CGraph

section
variable {X Y G H : CGraph}

/-- `f` is a homomorphism of reflexive closures. -/
def IsRHom (X G : CGraph) (f : X.V → G.V) : Prop :=
  ∀ a b, X.Adj a b → f a = f b ∨ G.Adj (f a) (f b)

instance (X G : CGraph) : DecidablePred (IsRHom X G) := fun _ ↦ by
  unfold IsRHom; infer_instance

/-- The reflexive homomorphisms from `X` to `G`. -/
def rhoms (X G : CGraph) : Finset (X.V → G.V) := Finset.univ.filter (IsRHom X G)

/-- How many reflexive homomorphisms there are from `X` to `G`. -/
def rhomCount (X G : CGraph) : ℕ := (rhoms X G).card

/-- the enumeration index of a vertex -/
def vIdx {X : CGraph} (v : X.V) : ℕ := (FinEnum.equiv v : Fin (FinEnum.card X.V)).1

theorem vIdx_injective {X : CGraph} : Function.Injective (vIdx (X := X)) := by
  intro a b h
  have : (FinEnum.equiv a : Fin (FinEnum.card X.V)) = FinEnum.equiv b := Fin.ext h
  simpa using congrArg (FinEnum.equiv (α := X.V)).symm this

/-- The order the enumeration puts on the vertices. -/
local instance vOrder (X : CGraph) : LinearOrder X.V := LinearOrder.lift' vIdx vIdx_injective

/-- The fibre of `f` through `x`. -/
def fibre (f : X.V → G.V) (x : X.V) : Finset X.V := Finset.univ.filter (fun y ↦ f y = f x)

@[simp] theorem mem_fibre {f : X.V → G.V} {x y : X.V} : y ∈ fibre f x ↔ f y = f x := by
  simp [fibre]

theorem fibre_nonempty (f : X.V → G.V) (x : X.V) : (fibre f x).Nonempty := ⟨x, by simp⟩

theorem fibre_congr {f : X.V → G.V} {x y : X.V} (h : f x = f y) : fibre f x = fibre f y := by
  ext z; simp [h]

/-- The least vertex, in the enumeration order, sent by `f` to the same place as `x`. -/
def blockMap (f : X.V → G.V) (x : X.V) : X.V := (fibre f x).min' (fibre_nonempty f x)

theorem blockMap_mem (f : X.V → G.V) (x : X.V) : blockMap f x ∈ fibre f x :=
  Finset.min'_mem _ _

-- The head symbol of the left-hand side is the variable `f`, so `simp` will try this at every
-- step; that is unavoidable, since the point of the lemma is that `blockMap f` is a section of an
-- arbitrary `f`.  It is `local` and the cost is confined to the proofs just below, which need it.
set_option warning.simp.varHead false in
@[local simp] theorem apply_blockMap (f : X.V → G.V) (x : X.V) : f (blockMap f x) = f x :=
  mem_fibre.1 (blockMap_mem f x)

theorem blockMap_le (f : X.V → G.V) (x : X.V) : blockMap f x ≤ x :=
  Finset.min'_le _ _ (by simp)

theorem blockMap_eq_of {f : X.V → G.V} {x m : X.V} (hm : f m = f x)
    (h : ∀ y, f y = f x → m ≤ y) : blockMap f x = m :=
  le_antisymm (Finset.min'_le _ _ (by simp [hm]))
    (Finset.le_min' _ _ _ (fun y hy ↦ h y (by simpa using hy)))

theorem blockMap_eq_iff {f : X.V → G.V} {x y : X.V} : blockMap f x = blockMap f y ↔ f x = f y := by
  constructor
  · intro h
    have := congrArg f h
    simpa using this
  · intro h
    refine blockMap_eq_of (by simp [h]) (fun z hz ↦ ?_)
    exact Finset.min'_le _ _ (by simp [hz, h])

@[simp] theorem blockMap_idem (f : X.V → G.V) (x : X.V) :
    blockMap f (blockMap f x) = blockMap f x :=
  blockMap_eq_iff.2 (apply_blockMap f x)

/-- The block maps of `X`. -/
def IsBlockMap (X : CGraph) (q : X.V → X.V) : Prop := (∀ x, q (q x) = q x) ∧ ∀ x, q x ≤ x

instance (X : CGraph) : DecidablePred (IsBlockMap X) := fun _ ↦ by
  unfold IsBlockMap; infer_instance

theorem isBlockMap_blockMap (f : X.V → G.V) : IsBlockMap X (blockMap f) :=
  ⟨blockMap_idem f, blockMap_le f⟩

theorem isBlockMap_id (X : CGraph) : IsBlockMap X id := ⟨fun _ ↦ rfl, fun _ ↦ le_refl _⟩

/-- The quotient of `X` by a block map: the vertices are the block representatives, and two of
them are adjacent when some vertex of the one block is adjacent to some vertex of the other. -/
def quot (X : CGraph) (q : X.V → X.V) : CGraph where
  V := {v : X.V // q v = v}
  Adj a b := decide (a ≠ b) && decide (∃ x y : X.V, q x = a.1 ∧ q y = b.1 ∧ X.Adj x y)
  symm a b := by
    have hex : decide (∃ x y : X.V, q x = a.1 ∧ q y = b.1 ∧ X.Adj x y)
        = decide (∃ x y : X.V, q x = b.1 ∧ q y = a.1 ∧ X.Adj x y) := by
      refine decide_eq_decide.2 ⟨?_, ?_⟩ <;>
        · rintro ⟨x, y, hx, hy, hxy⟩
          exact ⟨y, x, hy, hx, by rw [X.symm]; exact hxy⟩
    rw [decide_ne_comm, hex]
  loopless a := by simp

@[simp] theorem quot_adj_iff (X : CGraph) (q : X.V → X.V) (a b : (quot X q).V) :
    (quot X q).Adj a b ↔ a ≠ b ∧ ∃ x y : X.V, q x = a.1 ∧ q y = b.1 ∧ X.Adj x y := by
  simp [quot]

theorem card_quot_lt {q : X.V → X.V} (h : q ≠ id) :
    FinEnum.card (quot X q).V < FinEnum.card X.V := by
  obtain ⟨x, hx⟩ : ∃ x, q x ≠ x := by
    by_contra hc
    exact h (funext fun x ↦ not_not.1 (fun hne ↦ hc ⟨x, hne⟩))
  have hcard : FinEnum.card (quot X q).V = (Finset.univ.filter (fun v : X.V ↦ q v = v)).card :=
    FinEnum.card_subtype _
  rw [hcard, ← FinEnum.card_univ (α := X.V)]
  refine Finset.card_lt_card (Finset.ssubset_univ_iff.2 fun hc ↦ ?_)
  have hxm : x ∈ Finset.univ.filter (fun v : X.V ↦ q v = v) := by rw [hc]; exact Finset.mem_univ x
  simp [hx] at hxm

/-- `f` is a graph homomorphism. -/
def IsGHom (X G : CGraph) (f : X.V → G.V) : Prop := ∀ a b, X.Adj a b → G.Adj (f a) (f b)

instance (X G : CGraph) : DecidablePred (IsGHom X G) := fun _ ↦ by
  unfold IsGHom; infer_instance

/-- The injective homomorphisms from `X` to `G`. -/
def injHoms (X G : CGraph) : Finset (X.V → G.V) :=
  Finset.univ.filter (fun f ↦ Function.Injective f ∧ IsGHom X G f)

/-- How many injective homomorphisms there are from `X` to `G`. -/
def injHomCount (X G : CGraph) : ℕ := (injHoms X G).card

/-- The block maps of `X`, one for each partition of its vertices. -/
def blockMaps (X : CGraph) : Finset (X.V → X.V) := Finset.univ.filter (IsBlockMap X)

@[simp] theorem mem_blockMaps {q : X.V → X.V} : q ∈ blockMaps X ↔ IsBlockMap X q := by
  simp [blockMaps]

@[simp] theorem mem_rhoms {f : X.V → G.V} : f ∈ rhoms X G ↔ IsRHom X G f := by simp [rhoms]

@[simp] theorem mem_injHoms {f : X.V → G.V} :
    f ∈ injHoms X G ↔ Function.Injective f ∧ IsGHom X G f := by simp [injHoms]

/-- **The reflexive homomorphisms inducing a given partition are the injections out of the
quotient by it.**  One direction restricts `f` to the block representatives, the other precomposes
with `q`. -/
theorem card_fibre_blockMap (X G : CGraph) {q : X.V → X.V} (hq : IsBlockMap X q) :
    ((rhoms X G).filter (fun f ↦ blockMap f = q)).card = injHomCount (quot X q) G := by
  refine Finset.card_bij' (fun f _ ↦ fun v : (quot X q).V ↦ f v.1)
    (fun g _ ↦ fun x ↦ g ⟨q x, hq.1 x⟩) ?_ ?_ ?_ ?_
  · rintro f hf
    simp only [Finset.mem_filter, mem_rhoms] at hf
    obtain ⟨hr, hb⟩ := hf
    have hinj : Function.Injective (fun v : (quot X q).V ↦ f v.1) := by
      intro v w h
      have : blockMap f v.1 = blockMap f w.1 := blockMap_eq_iff.2 h
      rw [hb] at this
      exact Subtype.ext (by rw [← v.2, ← w.2, this])
    refine mem_injHoms.2 ⟨hinj, ?_⟩
    intro a b hab
    obtain ⟨hne, x, y, hx, hy, hxy⟩ := (quot_adj_iff X q a b).1 hab
    have hfx : f a.1 = f x := by rw [← hx, ← hb]; exact apply_blockMap f x
    have hfy : f b.1 = f y := by rw [← hy, ← hb]; exact apply_blockMap f y
    rcases hr x y hxy with h | h
    · exact absurd (hinj (show f a.1 = f b.1 by rw [hfx, hfy, h])) hne
    · simpa [hfx, hfy] using h
  · rintro g hg
    simp only [mem_injHoms] at hg
    obtain ⟨hinj, hhom⟩ := hg
    have hbm : blockMap (fun x ↦ g ⟨q x, hq.1 x⟩) = q := by
      funext x
      refine blockMap_eq_of ?_ ?_
      · exact congrArg g (Subtype.ext (hq.1 x))
      · intro y hy
        have : (⟨q y, hq.1 y⟩ : (quot X q).V) = ⟨q x, hq.1 x⟩ := hinj hy
        have hqy : q y = q x := congrArg Subtype.val this
        exact hqy ▸ hq.2 y
    refine Finset.mem_filter.2 ⟨mem_rhoms.2 ?_, hbm⟩
    intro a b hab
    by_cases h : (⟨q a, hq.1 a⟩ : (quot X q).V) = ⟨q b, hq.1 b⟩
    · exact Or.inl (congrArg g h)
    · exact Or.inr (hhom _ _ ((quot_adj_iff X q _ _).2 ⟨h, a, b, rfl, rfl, hab⟩))
  · rintro f hf
    simp only [Finset.mem_filter] at hf
    funext x
    simp only
    rw [← hf.2]
    exact apply_blockMap f x
  · rintro g hg
    funext v
    simp only
    exact congrArg g (Subtype.ext v.2)

/-- **Lovász's decomposition**: every reflexive homomorphism out of `X` is an injective
homomorphism out of one of the quotients of `X`, and by exactly one of them. -/
theorem rhomCount_eq_sum (X G : CGraph) :
    rhomCount X G = ∑ q ∈ blockMaps X, injHomCount (quot X q) G := by
  rw [rhomCount, Finset.card_eq_sum_card_fiberwise
    (f := fun f : X.V → G.V ↦ blockMap f) (t := blockMaps X)
    (fun f _ ↦ mem_blockMaps.2 (isBlockMap_blockMap f))]
  exact Finset.sum_congr rfl fun q hq ↦ card_fibre_blockMap X G (mem_blockMaps.1 hq)

/-- Isomorphic targets have the same reflexive-hom count. -/
theorem rhomCount_congr_right (X : CGraph) (i : G ≃cg H) : rhomCount X G = rhomCount X H := by
  refine Finset.card_bij' (fun f _ ↦ fun a ↦ i (f a)) (fun g _ ↦ fun a ↦ i.symm (g a))
    ?_ ?_ ?_ ?_
  · intro f hf
    refine mem_rhoms.2 fun a b hab ↦ ?_
    rcases mem_rhoms.1 hf a b hab with h | h
    · exact Or.inl (congrArg i h)
    · exact Or.inr (i.map_rel_iff.2 h)
  · intro g hg
    refine mem_rhoms.2 fun a b hab ↦ ?_
    rcases mem_rhoms.1 hg a b hab with h | h
    · exact Or.inl (congrArg i.symm h)
    · exact Or.inr (i.symm.map_rel_iff.2 h)
  · intro f _; funext a; simp
  · intro g _; funext a; simp

/-- Isomorphic sources have the same injective-hom count. -/
theorem injHomCount_congr_left (i : X ≃cg Y) (G : CGraph) :
    injHomCount X G = injHomCount Y G := by
  refine Finset.card_bij' (fun f _ ↦ fun a ↦ f (i.symm a)) (fun g _ ↦ fun a ↦ g (i a)) ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨hinj, hhom⟩ := mem_injHoms.1 hf
    refine mem_injHoms.2 ⟨fun a b h ↦ i.symm.injective (hinj h), fun a b hab ↦ ?_⟩
    exact hhom _ _ (i.symm.map_rel_iff.2 hab)
  · intro g hg
    obtain ⟨hinj, hhom⟩ := mem_injHoms.1 hg
    refine mem_injHoms.2 ⟨fun a b h ↦ i.injective (hinj h), fun a b hab ↦ ?_⟩
    exact hhom _ _ (i.map_rel_iff.2 hab)
  · intro f _; funext a; simp
  · intro g _; funext a; simp

/-- Quotienting by the identity block map changes nothing. -/
def quotIdIso (X : CGraph) : quot X id ≃cg X where
  toEquiv := Equiv.subtypeUnivEquiv (fun _ ↦ rfl)
  map_rel_iff' := by
    intro a b
    show X.Adj a.1 b.1 ↔ ((quot X id).Adj a b = true)
    rw [quot_adj_iff]
    constructor
    · refine fun h ↦ ⟨fun hab ↦ X.loopless a.1 ?_, a.1, b.1, rfl, rfl, h⟩
      rw [congrArg Subtype.val hab] at h ⊢
      exact h
    · rintro ⟨-, x, y, hx, hy, hxy⟩
      simp only [id] at hx hy
      rw [← hx, ← hy]
      exact hxy

/-- **Reflexive-hom counts determine injective-hom counts.**  Strong induction on the number of
vertices of `X`: the trivial partition contributes `injHomCount X` to `rhomCount X`, and every
other quotient of `X` is smaller, so the induction hypothesis cancels the rest of the sum. -/
theorem injHomCount_eq_of_rhomCount_eq {B C : CGraph}
    (h : ∀ Y : CGraph, rhomCount Y B = rhomCount Y C) :
    ∀ (n : ℕ) (X : CGraph), FinEnum.card X.V = n → injHomCount X B = injHomCount X C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hX
    have key : ∀ G : CGraph, rhomCount X G
        = injHomCount X G + ∑ q ∈ (blockMaps X).erase id, injHomCount (quot X q) G := by
      intro G
      rw [rhomCount_eq_sum X G,
        ← Finset.add_sum_erase _ _ (mem_blockMaps.2 (isBlockMap_id X))]
      congr 1
      exact injHomCount_congr_left (quotIdIso X) G
    have hsum : ∑ q ∈ (blockMaps X).erase id, injHomCount (quot X q) B
        = ∑ q ∈ (blockMaps X).erase id, injHomCount (quot X q) C :=
      Finset.sum_congr rfl fun q hq ↦
        ih _ (hX ▸ card_quot_lt (Finset.ne_of_mem_erase hq)) _ rfl
    have hXG := h X
    rw [key B, key C, hsum] at hXG
    omega

/-- The identity is an injective homomorphism. -/
theorem one_le_injHomCount_self (B : CGraph) : 1 ≤ injHomCount B B :=
  Finset.card_pos.2 ⟨id, mem_injHoms.2 ⟨Function.injective_id, fun _ _ h ↦ h⟩⟩

/-- Iterates of an endomorphism are endomorphisms. -/
theorem isGHom_iterate {σ : X.V → X.V} (h : IsGHom X X σ) (m : ℕ) : IsGHom X X (σ^[m]) := by
  induction m with
  | zero => intro a b hab; simpa using hab
  | succ m ih =>
    intro a b hab
    simpa [Function.iterate_succ_apply] using ih _ _ (h a b hab)

/-- A pair of injective homomorphisms in both directions between finite graphs is a pair of
isomorphisms. -/
theorem nonempty_iso_of_injHoms {B C : CGraph} {f : B.V → C.V} {g : C.V → B.V}
    (hf : Function.Injective f) (hfh : IsGHom B C f)
    (hg : Function.Injective g) (hgh : IsGHom C B g) : Nonempty (B ≃cg C) := by
  have hcard : FinEnum.card B.V = FinEnum.card C.V :=
    le_antisymm (FinEnum.card_le_of_injective f hf) (FinEnum.card_le_of_injective g hg)
  have hfbij : Function.Bijective f :=
    (FinEnum.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
  set σ : B.V → B.V := g ∘ f with hσ
  have hσh : IsGHom B B σ := fun a b hab ↦ hgh _ _ (hfh a b hab)
  have hσbij : Function.Bijective σ := ⟨hg.comp hf, by
    refine (FinEnum.bijective_iff_injective_and_card σ).2 ⟨hg.comp hf, rfl⟩ |>.2⟩
  set e : Equiv.Perm B.V := Equiv.ofBijective σ hσbij with he
  have hk : 0 < orderOf e := orderOf_pos e
  have hiter : σ^[orderOf e] = id := by
    have : ⇑(e ^ orderOf e) = σ^[orderOf e] := by
      rw [Equiv.Perm.coe_pow]; rfl
    rw [← this, pow_orderOf_eq_one e]; rfl
  have hrefl : ∀ a b : B.V, B.Adj (σ a) (σ b) → B.Adj a b := by
    intro a b hab
    obtain ⟨m, hm⟩ : ∃ m, orderOf e = m + 1 := ⟨orderOf e - 1, by omega⟩
    have h2 := isGHom_iterate hσh m _ _ hab
    have e1 : ∀ x : B.V, σ^[m] (σ x) = x := by
      intro x
      have hx : σ^[orderOf e] x = x := by rw [hiter]; rfl
      rwa [hm, Function.iterate_succ_apply] at hx
    rwa [e1 a, e1 b] at h2
  refine ⟨⟨Equiv.ofBijective f hfbij, fun {a b} ↦ ⟨fun hab ↦ ?_, fun hab ↦ hfh a b hab⟩⟩⟩
  exact hrefl a b (hgh _ _ hab)

theorem nonempty_iso_of_rhomCount_eq {B C : CGraph}
    (h : ∀ X : CGraph, rhomCount X B = rhomCount X C) : Nonempty (B ≃cg C) := by
  have hBC : injHomCount B B = injHomCount B C :=
    injHomCount_eq_of_rhomCount_eq h _ B rfl
  have hCB : injHomCount C B = injHomCount C C :=
    injHomCount_eq_of_rhomCount_eq h _ C rfl
  obtain ⟨f, hf⟩ : (injHoms B C).Nonempty := by
    refine Finset.card_pos.1 ?_
    have h1 := one_le_injHomCount_self B
    rw [hBC] at h1
    exact h1
  obtain ⟨g, hg⟩ : (injHoms C B).Nonempty := by
    refine Finset.card_pos.1 ?_
    have h1 := one_le_injHomCount_self C
    rw [← hCB] at h1
    exact h1
  obtain ⟨hfi, hfh⟩ := mem_injHoms.1 hf
  obtain ⟨hgi, hgh⟩ := mem_injHoms.1 hg
  exact nonempty_iso_of_injHoms hfi hfh hgi hgh

/-- Two vertices of a strong product are equal or adjacent exactly when both of their coordinate
pairs are.  This is the reflexive closure of `strongProduct_adj`, and the reason the strong
product is the categorical product for reflexive homomorphisms. -/
theorem strongProduct_rstep {G H : CGraph} (p q : (G ⊠g H).V) :
    (p = q ∨ (G ⊠g H).Adj p q) ↔
      ((p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2)) := by
  by_cases h : p = q
  · subst h; simp
  · rw [or_iff_right h, strongProduct_adj]
    simp [h]

/-- A map into a strong product is a reflexive homomorphism exactly when both of its coordinates
are. -/
theorem isRHom_strongProduct_iff {X G H : CGraph} {f : X.V → (G ⊠g H).V} :
    IsRHom X (G ⊠g H) f ↔
      IsRHom X G (fun a ↦ (f a).1) ∧ IsRHom X H (fun a ↦ (f a).2) := by
  constructor
  · intro hf
    exact ⟨fun a b hab ↦ ((strongProduct_rstep _ _).1 (hf a b hab)).1,
      fun a b hab ↦ ((strongProduct_rstep _ _).1 (hf a b hab)).2⟩
  · rintro ⟨h1, h2⟩ a b hab
    exact (strongProduct_rstep _ _).2 ⟨h1 a b hab, h2 a b hab⟩

/-- **Reflexive homomorphism counts are multiplicative over the strong product.**  This is what
makes the strong product cancellative and the tensor product not: the same argument for ordinary
homomorphisms and the tensor product breaks down because a hom count there can be zero. -/
theorem rhomCount_strongProduct (X G H : CGraph) :
    rhomCount X (G ⊠g H) = rhomCount X G * rhomCount X H := by
  rw [rhomCount, rhomCount, rhomCount, ← Finset.card_product]
  refine Finset.card_bij' (fun f _ ↦ ((fun a ↦ (f a).1), (fun a ↦ (f a).2)))
    (fun p _ ↦ (fun a ↦ (p.1 a, p.2 a))) ?_ ?_ ?_ ?_
  · intro f hf
    exact Finset.mem_product.2 (by
      obtain ⟨h1, h2⟩ := isRHom_strongProduct_iff.1 (mem_rhoms.1 hf)
      exact ⟨mem_rhoms.2 h1, mem_rhoms.2 h2⟩)
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact mem_rhoms.2 (isRHom_strongProduct_iff.2 ⟨mem_rhoms.1 h1, mem_rhoms.1 h2⟩)
  · intro f _; funext a; rfl
  · intro p _; rfl

/-- **There is always a reflexive homomorphism into a nonempty graph**: a constant map.  The
ordinary hom count has no such lower bound, which is why the tensor product does not cancel. -/
theorem one_le_rhomCount (X : CGraph) {G : CGraph} (v : G.V) : 1 ≤ rhomCount X G :=
  Finset.card_pos.2 ⟨fun _ ↦ v, mem_rhoms.2 fun _ _ _ ↦ Or.inl rfl⟩

/-- **The strong product is cancellative.** -/
theorem strongProduct_cancel {A B C : CGraph} (v : A.V) (i : A ⊠g B ≃cg A ⊠g C) :
    Nonempty (B ≃cg C) := by
  refine nonempty_iso_of_rhomCount_eq fun X ↦ ?_
  have h1 : rhomCount X A * rhomCount X B = rhomCount X A * rhomCount X C := by
    rw [← rhomCount_strongProduct, ← rhomCount_strongProduct]
    exact rhomCount_congr_right X i
  exact Nat.eq_of_mul_eq_mul_left (one_le_rhomCount X v) h1

end

end CGraph

namespace IsoGraph

/-- **The strong product cancels a nonempty factor on the left.** -/
theorem strongProduct_left_cancel {a b c : IsoGraph} (ha : a ≠ 0) (h : a ⊠g b = a ⊠g c) :
    b = c := by
  induction a using Quotient.ind with | _ A =>
  induction b using Quotient.ind with | _ B =>
  induction c using Quotient.ind with | _ C =>
  rw [strongProduct_mk, strongProduct_mk] at h
  obtain ⟨i⟩ := Quotient.exact h
  have hcard : FinEnum.card A.V ≠ 0 := fun hc ↦
    ha (V_eq_zero_iff.1 (by rw [V_mk]; exact hc))
  obtain ⟨v⟩ : Nonempty A.V := by
    rw [← Fintype.card_pos_iff, ← FinEnum.card_eq_fintypeCard]
    omega
  exact Quotient.sound (CGraph.strongProduct_cancel v i)

/-- **The strong product cancels a nonempty factor on the right.** -/
theorem strongProduct_right_cancel {a b c : IsoGraph} (hc : c ≠ 0) (h : a ⊠g c = b ⊠g c) :
    a = b :=
  strongProduct_left_cancel hc (by rw [strongProduct_comm c a, strongProduct_comm c b]; exact h)

section
attribute [local instance] instMulStrongProduct commMonoidWithZeroStrongProduct

/-- **Both cancellation laws for the strong product.** -/
theorem isCancelMulZeroStrongProduct : IsCancelMulZero IsoGraph where
  mul_left_cancel_of_ne_zero ha _ _ h := strongProduct_left_cancel ha h
  mul_right_cancel_of_ne_zero hb _ _ h := strongProduct_right_cancel hb h

end

end IsoGraph

namespace IsoGraph.StrongProduct

attribute [scoped instance] isCancelMulZeroStrongProduct

end IsoGraph.StrongProduct

namespace IsoGraph.StrongSemiring

/-- **The graphs are an integral domain** under the disjoint union and the strong product. -/
scoped instance instIsDomain : IsDomain IsoGraph where
  mul_left_cancel_of_ne_zero ha _ _ h := strongProduct_left_cancel ha h
  mul_right_cancel_of_ne_zero hb _ _ h := strongProduct_right_cancel hb h

end IsoGraph.StrongSemiring
