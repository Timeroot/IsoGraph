import IsoGraph.Core.CliqueSum
import IsoGraph.ForMathlib.List
import IsoGraph.ForMathlib.SimpleGraph
import IsoGraph.Invariants.Certificates
import IsoGraph.Invariants.Derived
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Equations between the core constructions

Equations between the core constructions: when two ways of writing a graph give the same graph.
Most of these are `simp` lemmas that rewrite a compound expression into a simpler one, or into a
member of a named family — a path with no internal vertices is an edge, a theta graph with two
paths is a cycle, the complement of a complete multipartite graph is a disjoint union of complete
graphs.  The explicit isomorphisms and the edge-list normalisations they need are here too.
-/

namespace CGraph

section
open Fintype
variable (G H : CGraph)

/-! ### The complete graph -/

@[simp] theorem complete_adj (n : ℕ) (i j : Fin n) : (complete n).Adj i j = decide (i ≠ j) := by
  simp [complete]

/-- The disjoint union is commutative up to isomorphism — which is exactly what equality in
`IsoGraph` means. -/
theorem disjUnion_comm : Nonempty (G ⊕g H ≃cg H ⊕g G) :=
  let e : (G.disjUnion H).V ≃ (H.disjUnion G).V := Equiv.sumComm G.V H.V
  have he1 : ∀ a : G.V, e (Sum.inl a) = Sum.inr a := fun a => Equiv.sumComm_apply (α := G.V) (β := H.V) ▸ rfl
  have he2 : ∀ b : H.V, e (Sum.inr b) = Sum.inl b := fun b => Equiv.sumComm_apply (α := G.V) (β := H.V) ▸ rfl
  ⟨RelIso.mk e (by
        intro x y
        rcases x with _ | _ <;> rcases y with _ | _ <;>
          simp [he1, he2, disjUnion_adj_inl_inl, disjUnion_adj_inl_inr, disjUnion_adj_inr_inl, disjUnion_adj_inr_inr] )⟩

theorem disjUnion_assoc (K : CGraph) :
    Nonempty (G ⊕g H ⊕g K ≃cg G ⊕g (H ⊕g K)) :=
  by exact ⟨RelIso.mk (Equiv.sumAssoc G.V H.V K.V) (by
  intro a b
  simp only [disjUnion]
  dsimp [Equiv.sumAssoc]
  cases a with
  | inl x =>
    cases x with
    | inl a =>
      cases b with
      | inl y =>
        cases y with
        | inl c => simp
        | inr d => simp
      | inr y => simp
    | inr hb =>
      cases b with
      | inl y => cases y with | inl c => simp | inr d => simp
      | inr y => simp
  | inr hc =>
    cases b with
    | inl y => cases y with | inl c => simp | inr d => simp
    | inr y => simp)⟩

end

section
open Fintype
variable {m n : ℕ}

/-- With all parts of size `a`, the sums of `card_filter_fst_notMem` are products.  The length is
left as `(List.replicate n a).length` rather than `n` so that the statement does not have to
transport `S` along `List.length_replicate`. -/
theorem sum_compl_replicate (n a : ℕ) (S : Finset (Fin (List.replicate n a).length)) :
    ∑ j ∈ Sᶜ, (List.replicate n a).get j = ((List.replicate n a).length - S.card) * a := by
  have h : ∀ j ∈ Sᶜ, (List.replicate n a).get j = a := fun j _ ↦ by simp
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, Finset.card_compl, Fintype.card_fin]

end

section
open Fintype
variable {m n : ℕ}
variable {F : Type} [Field F] [FinEnum F]

theorem quadraticChar_eq_one_iff (a : F) :
    quadraticChar F a = 1 ↔ ∃ r : F, r ≠ 0 ∧ r * r = a := by
  constructor
  · intro h
    have ha : a ≠ 0 := by rintro rfl; rw [quadraticChar_zero] at h; norm_num at h
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare ha).1 h
    exact ⟨r, fun h0 ↦ ha (by rw [hr, h0, mul_zero]), hr.symm⟩
  · rintro ⟨r, hr0, rfl⟩
    exact (quadraticChar_one_iff_isSquare (mul_ne_zero hr0 hr0)).2 ⟨r, rfl⟩

/-! #### Self-complementarity

Zero is a square, so a non-square is nonzero, and multiplying by it is a bijection of `F` that
exchanges the squares with the non-squares — that is, edges of `paleyField F` with non-edges. -/

omit [FinEnum F] in
theorem ne_zero_of_not_isSquare {g : F} (hg : ¬ IsSquare g) : g ≠ 0 := by
  rintro rfl; exact hg ⟨0, by simp⟩

end

section
open Fintype
variable (G : CGraph)

theorem empty_eq_ofRel (n : ℕ) : empty n = ofRel (Fin n) fun _ _ ↦ false :=
  eq_ofRel _ _ fun _ _ _ ↦ rfl

theorem complete_eq_ofRel (n : ℕ) : complete n = ofRel (Fin n) fun _ _ ↦ true := by
  rw [complete, compl_eq_ofRel]
  rfl

/-! ### Kneser graphs

Permutations of the ground set act on the `k`-subsets, and any two *disjoint pairs* of `k`-subsets
are matched by one of them — which is precisely arc-transitivity, an arc of `kneser n k` being a
pair of disjoint `k`-sets. -/

/-- A permutation of `Fin n` permutes the `k`-subsets. -/
def kneserPerm (n k : ℕ) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm {s : Finset (Fin n) // s.card = k} where
  toFun s := ⟨s.1.image π, by rw [Finset.card_image_of_injective _ π.injective]; exact s.2⟩
  invFun s := ⟨s.1.image π.symm, by
    rw [Finset.card_image_of_injective _ π.symm.injective]; exact s.2⟩
  left_inv s := by ext : 1; simp [Finset.image_image]
  right_inv s := by ext : 1; simp [Finset.image_image]

@[simp] theorem kneserPerm_coe (n k : ℕ) (π : Equiv.Perm (Fin n))
    (s : {s : Finset (Fin n) // s.card = k}) :
    ((kneserPerm n k π s : {s : Finset (Fin n) // s.card = k}) : Finset (Fin n))
      = (s : Finset (Fin n)).image π := rfl

end

end CGraph

namespace CGraph.Iso

section
variable {G G' H H' : CGraph}

/-- The disjoint union is commutative. -/
@[toIsoGraph disjUnion_comm]
def disjUnionComm (G H : CGraph) :
    G ⊕g H ≃cg H ⊕g G :=
  isoOfAdj (G := G ⊕g H) (H := H ⊕g G)
    (Equiv.sumComm G.V H.V) (by rintro (a | a) (b | b) <;> rfl)

/-- The join is commutative.  Unlike the disjoint union this needs a case analysis rather than
`rfl`: the vertex type of `join G H` is `Gᶜ.V ⊕ Hᶜ.V`, which is only definitionally `G.V ⊕ H.V`,
so `simp` cannot see through `Equiv.sumComm` and each case has to name its image. -/
@[toIsoGraph join_comm]
def joinComm (G H : CGraph) :
    G ∇g H ≃cg H ∇g G :=
  isoOfAdj (G := G ∇g H) (H := H ∇g G)
    (Equiv.sumComm G.V H.V) (by
      rintro (a | a) (b | b)
      · show (H ∇g G).Adj (.inr a) (.inr b) = _
        simp
      · show (H ∇g G).Adj (.inr a) (.inl b) = _
        simp
      · show (H ∇g G).Adj (.inl a) (.inr b) = _
        simp
      · show (H ∇g G).Adj (.inl a) (.inl b) = _
        simp)

/-- The cartesian product is commutative. -/
@[toIsoGraph cartesianProduct_comm]
def cartesianProductComm (G H : CGraph) :
    G □g H ≃cg H □g G :=
  isoOfAdj (G := G □g H) (H := H □g G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show ((decide (x.2 = y.2) && G.Adj x.1 y.1) || (H.Adj x.2 y.2 && decide (x.1 = y.1))) = _
      rw [CGraph.cartesianProduct_adj]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      generalize decide (x.1 = y.1) = c
      generalize decide (x.2 = y.2) = d
      revert a b c d
      decide

/-- The tensor product is commutative. -/
@[toIsoGraph tensorProduct_comm]
def tensorProductComm (G H : CGraph) :
    G ⊗g H ≃cg H ⊗g G :=
  isoOfAdj (G := G ⊗g H) (H := H ⊗g G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show (H.Adj x.2 y.2 && G.Adj x.1 y.1) = _
      rw [CGraph.tensorProduct_adj]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      revert a b
      decide

/-- The strong product is commutative. -/
@[toIsoGraph strongProduct_comm]
def strongProductComm (G H : CGraph) :
    G ⊠g H ≃cg H ⊠g G :=
  isoOfAdj (G := G ⊠g H) (H := H ⊠g G)
    (Equiv.prodComm G.V H.V) fun x y ↦ by
      show (decide ((x.2, x.1) ≠ (y.2, y.1)) &&
        ((decide (x.2 = y.2) || H.Adj x.2 y.2) && (decide (x.1 = y.1) || G.Adj x.1 y.1))) = _
      rw [CGraph.strongProduct_adj,
        show decide ((x.2, x.1) ≠ (y.2, y.1)) = decide (x ≠ y) from
          decide_eq_decide.2 (not_congr (by
            simp only [Prod.ext_iff]
            exact and_comm.trans (Prod.ext_iff (x := (x : G.V × H.V)) (y := y)).symm))]
      generalize G.Adj x.1 y.1 = a
      generalize H.Adj x.2 y.2 = b
      generalize decide (x.1 = y.1) = c
      generalize decide (x.2 = y.2) = d
      generalize decide (x ≠ y) = e
      revert a b c d e
      decide

/-! ### Associativity

All four products are associative, and all four proofs are the same: `Equiv.prodAssoc` on the
vertices, `decide_prod_eq` to break the equality tests on pairs apart, and `decide` on the
resulting identity between two Boolean expressions in six variables. -/

/-- The disjoint union is associative. -/
@[toIsoGraph disjUnion_assoc]
def disjUnionAssoc (G H K : CGraph) :
    G ⊕g H ⊕g K ≃cg
      G ⊕g (H ⊕g K) :=
  isoOfAdj (G := G ⊕g H ⊕g K)
    (H := G ⊕g (H ⊕g K))
    (Equiv.sumAssoc G.V H.V K.V) (by rintro ((a | a) | a) ((b | b) | b) <;> rfl)

/-- The join is associative. -/
@[toIsoGraph join_assoc]
def joinAssoc (G H K : CGraph) :
    G ∇g H ∇g K ≃cg
      G ∇g (H ∇g K) :=
  isoOfAdj (G := G ∇g H ∇g K)
    (H := G ∇g (H ∇g K))
    (Equiv.sumAssoc G.V H.V K.V) (by
      rintro ((a | a) | a) ((b | b) | b)
      · show (G ∇g (H ∇g K)).Adj (.inl a) (.inl b) = _
        simp
      · show (G ∇g (H ∇g K)).Adj (.inl a) (.inr (.inl b)) = _
        simp
      · show (G ∇g (H ∇g K)).Adj (.inl a) (.inr (.inr b)) = _
        simp
      · show (G ∇g (H ∇g K)).Adj (.inr (.inl a)) (.inl b) = _
        simp
      · show (G ∇g (H ∇g K)).Adj
          (.inr (.inl a)) (.inr (.inl b)) = _
        simp
      · show (G ∇g (H ∇g K)).Adj
          (.inr (.inl a)) (.inr (.inr b)) = _
        simp
      · show (G ∇g (H ∇g K)).Adj (.inr (.inr a)) (.inl b) = _
        simp
      · show (G ∇g (H ∇g K)).Adj
          (.inr (.inr a)) (.inr (.inl b)) = _
        simp
      · show (G ∇g (H ∇g K)).Adj
          (.inr (.inr a)) (.inr (.inr b)) = _
        simp)

/-- The cartesian product is associative. -/
@[toIsoGraph cartesianProduct_assoc]
def cartesianProductAssoc (G H K : CGraph)
 :
    G □g H □g K ≃cg
      G □g (H □g K) :=
  isoOfAdj (G := G □g H □g K)
    (H := G □g (H □g K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show ((decide (x.1.1 = y.1.1) &&
          (H □g K).Adj (x.1.2, x.2) (y.1.2, y.2)) ||
        (G.Adj x.1.1 y.1.1 && decide (((x.1.2, x.2) : H.V × K.V) = (y.1.2, y.2)))) = _
      rw [CGraph.cartesianProduct_adj, CGraph.cartesianProduct_adj, CGraph.cartesianProduct_adj,
        decide_prod_eq ((x.1.2, x.2) : H.V × K.V), decide_prod_eq x.1 y.1]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      generalize decide (x.2 = y.2) = c
      revert p q r a b c
      decide

/-- The tensor product is associative. -/
@[toIsoGraph tensorProduct_assoc]
def tensorProductAssoc (G H K : CGraph) :
    G ⊗g H ⊗g K ≃cg
      G ⊗g (H ⊗g K) :=
  isoOfAdj (G := G ⊗g H ⊗g K)
    (H := G ⊗g (H ⊗g K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (G.Adj x.1.1 y.1.1 && (H ⊗g K).Adj (x.1.2, x.2) (y.1.2, y.2)) = _
      rw [CGraph.tensorProduct_adj, CGraph.tensorProduct_adj, CGraph.tensorProduct_adj]
      exact (Bool.and_assoc _ _ _).symm

/-- The lexicographic product is associative. -/
@[toIsoGraph lexProduct_assoc]
def lexProductAssoc (G H K : CGraph) :
    G ·g H ·g K ≃cg
      G ·g (H ·g K) :=
  isoOfAdj (G := G ·g H ·g K)
    (H := G ·g (H ·g K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (G.Adj x.1.1 y.1.1 || (decide (x.1.1 = y.1.1) &&
        (H ·g K).Adj (x.1.2, x.2) (y.1.2, y.2))) = _
      rw [CGraph.lexProduct_adj, CGraph.lexProduct_adj, CGraph.lexProduct_adj,
        decide_prod_eq x.1 y.1]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      revert p q r a b
      decide

/-- The strong product is associative. -/
@[toIsoGraph strongProduct_assoc]
def strongProductAssoc (G H K : CGraph) :
    G ⊠g H ⊠g K ≃cg
      G ⊠g (H ⊠g K) :=
  isoOfAdj (G := G ⊠g H ⊠g K)
    (H := G ⊠g (H ⊠g K))
    (Equiv.prodAssoc G.V H.V K.V) fun x y ↦ by
      show (decide (((x.1.1, x.1.2, x.2) : G.V × H.V × K.V) ≠ (y.1.1, y.1.2, y.2)) &&
        ((decide (x.1.1 = y.1.1) || G.Adj x.1.1 y.1.1) &&
          (decide (((x.1.2, x.2) : H.V × K.V) = (y.1.2, y.2)) ||
            (H ⊠g K).Adj (x.1.2, x.2) (y.1.2, y.2)))) = _
      simp only [CGraph.strongProduct_adj, decide_not, decide_prod_eq]
      rw [show decide (x.1 = y.1)
          = (decide (x.1.1 = y.1.1) && decide (x.1.2 = y.1.2)) from decide_prod_eq _ _]
      generalize G.Adj x.1.1 y.1.1 = p
      generalize H.Adj x.1.2 y.1.2 = q
      generalize K.Adj x.2 y.2 = r
      generalize decide (x.1.1 = y.1.1) = a
      generalize decide (x.1.2 = y.1.2) = b
      generalize decide (x.2 = y.2) = c
      revert p q r a b c
      decide

/-! ### Bipartite double covers

`K₂ × G` is the bipartite double cover of `G`.  It splits into two copies of `G` exactly when `G`
is bipartite, and for an odd cycle it is the cycle of twice the length. -/

/-- Twisting the `K₂` coordinate by a 2-colouring of the other coordinate.  This is the bijection
that turns a bipartite double cover into two disjoint copies. -/
def colourTwist (G : CGraph) (c : G.V → Bool) : (Fin 2 × G.V) ≃ (Fin 2 × G.V) where
  toFun p := (⟨(p.1.1 + (if c p.2 then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩, p.2)
  invFun p := (⟨(p.1.1 + (if c p.2 then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩, p.2)
  left_inv p := by
    have h := p.1.isLt
    refine Prod.ext (Fin.ext ?_) rfl
    simp only
    rcases c p.2 <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega
  right_inv p := by
    have h := p.1.isLt
    refine Prod.ext (Fin.ext ?_) rfl
    simp only
    rcases c p.2 <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

/-- **A double cover splits whenever the graph is 2-coloured.**  If `c` is a proper 2-colouring of
`G` — that is, if `G` is bipartite — then twisting the `K₂` coordinate by the colour carries the
tensor product onto the Cartesian one, which is two disjoint copies. -/
def tensorTwoOfColouring (G : CGraph) (c : G.V → Bool)
    (h : ∀ x y, G.Adj x y = true → c x ≠ c y) :
    CGraph.complete 2 ⊗g G ≃cg CGraph.empty 2 □g G :=
  isoOfAdj (G := CGraph.complete 2 ⊗g G)
    (H := CGraph.empty 2 □g G) (colourTwist G c) (by
      rintro ⟨a, x⟩ ⟨b, y⟩
      show (CGraph.empty 2 □g G).Adj
          (⟨(a.1 + (if c x then 1 else 0)) % 2, _⟩, x)
          (⟨(b.1 + (if c y then 1 else 0)) % 2, _⟩, y)
        = (CGraph.complete 2 ⊗g G).Adj (a, x) (b, y)
      rw [CGraph.cartesianProduct_adj, CGraph.tensorProduct_adj]
      simp only [CGraph.empty_adj, CGraph.complete_adj, Bool.false_and, Bool.or_false]
      rcases hxy : G.Adj x y with _ | _
      · simp
      · have hne := h x y hxy
        have ha := a.isLt
        have hb := b.isLt
        simp only [Bool.and_true]
        rw [show (decide ((⟨(a.1 + (if c x then 1 else 0)) % 2,
              Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
            = ⟨(b.1 + (if c y then 1 else 0)) % 2, Nat.mod_lt _ (by norm_num)⟩))
          = decide ((a.1 + (if c x then 1 else 0)) % 2
            = (b.1 + (if c y then 1 else 0)) % 2) from by simp [Fin.ext_iff]]
        rw [show (decide (a ≠ b)) = decide (a.1 ≠ b.1) from by
          simp only [decide_eq_decide, ne_eq, not_iff_not]
          exact ⟨fun hh ↦ congrArg Fin.val hh, fun hh ↦ Fin.ext hh⟩]
        congr 1
        simp only [eq_iff_iff, ne_eq]
        rcases hcx : c x <;> rcases hcy : c y <;>
          simp only [if_true, if_false, Bool.false_eq_true] <;>
          first
            | omega
            | exact absurd (hcx.trans hcy.symm) hne)

/-- The Chinese remainder bijection `Fin (2n) ≃ Fin 2 × Fin n` for odd `n`, as the reduction
`k ↦ (k % 2, k % n)`.  Injectivity is elementary rather than a coprimality argument: `k` and
`k % n` differ by `0` or `n`, and `n` is odd, so the two residues pin `k` down. -/
noncomputable def crtEquiv (m : ℕ) : Fin (2 * (2 * m + 3)) ≃ (Fin 2 × Fin (2 * m + 3)) :=
  Equiv.ofBijective
    (fun k ↦ (⟨k.1 % 2, Nat.mod_lt _ (by omega)⟩, ⟨k.1 % (2 * m + 3), Nat.mod_lt _ (by omega)⟩))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro k l hkl
      have hk := mod_of_lt_two_mul (d := 2 * m + 3) k.isLt
      have hl := mod_of_lt_two_mul (d := 2 * m + 3) l.isLt
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hkl
      exact Fin.ext (by omega), by simp⟩)

/-- **The double cover of an odd cycle is the cycle of twice the length.**  Under the Chinese
remainder bijection, stepping once around `C_{2n}` changes the parity *and* steps once around
`C_n` — which is exactly an edge of `K₂ × C_n`. -/
noncomputable def cycleTensorTwo (m : ℕ) :
    CGraph.cycle (2 * (2 * m + 3)) ≃cg
      CGraph.complete 2 ⊗g CGraph.cycle (2 * m + 3) :=
  isoOfAdj (G := CGraph.cycle (2 * (2 * m + 3)))
    (H := CGraph.complete 2 ⊗g CGraph.cycle (2 * m + 3)) (crtEquiv m) (by
      intro k l
      show (CGraph.complete 2 ⊗g CGraph.cycle (2 * m + 3)).Adj
          (⟨k.1 % 2, _⟩, ⟨k.1 % (2 * m + 3), _⟩) (⟨l.1 % 2, _⟩, ⟨l.1 % (2 * m + 3), _⟩)
        = (CGraph.cycle (2 * (2 * m + 3))).Adj k l
      have hn : 0 < 2 * m + 3 := by omega
      have e1 := succ_mod_eq_iff (d := 2 * m + 3) (x := k.1 % (2 * m + 3))
        (y := l.1 % (2 * m + 3)) (Nat.mod_lt _ hn)
      have e2 := succ_mod_eq_iff (d := 2 * m + 3) (x := l.1 % (2 * m + 3))
        (y := k.1 % (2 * m + 3)) (Nat.mod_lt _ hn)
      have e3 := succ_mod_eq_iff (d := 2 * (2 * m + 3)) (x := k.1) (y := l.1) k.isLt
      have e4 := succ_mod_eq_iff (d := 2 * (2 * m + 3)) (x := l.1) (y := k.1) l.isLt
      have hk := mod_of_lt_two_mul (d := 2 * m + 3) k.isLt
      have hl := mod_of_lt_two_mul (d := 2 * m + 3) l.isLt
      refine Bool.eq_iff_iff.2 ?_
      simp only [CGraph.tensorProduct_adj, CGraph.complete_adj, CGraph.cycle, CGraph.ofRel_adj,
        Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq, Fin.ext_iff]
      rw [e1, e2, e3, e4]
      omega)

/-! ### Matchings as circulants -/

/-- Splitting `Fin (2m)` into `Fin m × Fin 2` by `k ↦ (k % m, k / m)`, written in the direction
`(i, a) ↦ i + m * a` so that the adjacency computation never has to divide. -/
noncomputable def finTwoMul (m : ℕ) : (Fin (m + 1) × Fin 2) ≃ Fin (2 * (m + 1)) :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1.1 + (m + 1) * p.2.1, by
      have hp := p.1.isLt
      have h2 : p.2.1 = 0 ∨ p.2.1 = 1 := by omega
      rcases h2 with h | h <;> rw [h] <;> omega⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.1 + (m + 1) * a.1 = j.1 + (m + 1) * b.1 := congrArg Fin.val hij
      have ha2 : a.1 = 0 ∨ a.1 = 1 := by omega
      have hb2 : b.1 = 0 ∨ b.1 = 1 := by omega
      have hab : i = j ∧ a = b := by
        rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;> rw [ha, hb] at hij' <;>
          exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      rw [hab.1, hab.2], by simp [Nat.mul_comm]⟩)

/-- **A perfect matching, as a circulant.**  `circulant (2m) {m}` joins `i` to `i + m`, so it is
`m` disjoint edges. -/
noncomputable def circulantMatching (m : ℕ) :
    CGraph.empty (m + 1) □g CGraph.complete 2 ≃cg
      CGraph.circulant (2 * (m + 1)) [m + 1] :=
  isoOfAdj (G := CGraph.empty (m + 1) □g CGraph.complete 2)
    (H := CGraph.circulant (2 * (m + 1)) [m + 1]) (finTwoMul m) (by
      rintro ⟨i, a⟩ ⟨j, b⟩
      have hi := i.isLt
      have hj := j.isLt
      have ha2 : a.1 = 0 ∨ a.1 = 1 := by omega
      have hb2 : b.1 = 0 ∨ b.1 = 1 := by omega
      have hx : i.1 + (m + 1) * a.1 < 2 * (m + 1) := by
        rcases ha2 with h | h <;> rw [h] <;> omega
      have hy : j.1 + (m + 1) * b.1 < 2 * (m + 1) := by
        rcases hb2 with h | h <;> rw [h] <;> omega
      have hIJ : (i = j) ↔ (i.1 = j.1) := ⟨fun h ↦ by rw [h], fun h ↦ Fin.ext h⟩
      show (CGraph.circulant (2 * (m + 1)) [m + 1]).Adj
          (⟨i.1 + (m + 1) * a.1, hx⟩ : Fin (2 * (m + 1)))
          (⟨j.1 + (m + 1) * b.1, hy⟩ : Fin (2 * (m + 1)))
        = (CGraph.empty (m + 1) □g CGraph.complete 2).Adj (i, a) (j, b)
      rw [CGraph.cartesianProduct_adj]
      simp only [CGraph.circulant, CGraph.ofRel_adj, CGraph.empty_adj, CGraph.complete_adj,
        Bool.false_and, Bool.or_false, List.contains_cons, List.contains_nil]
      refine Bool.eq_iff_iff.2 ?_
      rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;>
        · have h1 := sub_mod_cases hx hy
          have h2 := sub_mod_cases hy hx
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ne_eq,
            Fin.ext_iff, hIJ]
          rw [ha, hb] at h1 h2 ⊢
          omega)

end

end CGraph.Iso

namespace CGraph

/-! ## Edge lists

The `ofEdges`-based families are all built from `pathEdges`, `cycleEdges`, `cliqueEdges` and
`legEdges`; the lemmas here put each of those lists in closed form and read off its membership,
which is what turns a degenerate case of one of those families into a named graph. -/

theorem pathEdges_cons_cons (a b : ℕ) (l : List ℕ) :
    pathEdges (a :: b :: l) = (a, b) :: pathEdges (b :: l) := rfl

theorem pathEdges_map_succ : ∀ l : List ℕ,
    pathEdges (l.map (· + 1)) = (pathEdges l).map (fun p ↦ (p.1 + 1, p.2 + 1))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      have ih := pathEdges_map_succ (b :: rest)
      simp only [List.map_cons] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, List.map_cons, ih]

theorem pathEdges_concat : ∀ (l : List ℕ) (b x : ℕ),
    pathEdges (l ++ [b, x]) = pathEdges (l ++ [b]) ++ [(b, x)]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: c :: rest, b, x => by
      have ih := pathEdges_concat (c :: rest) b x
      simp only [List.cons_append] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, ih, List.cons_append]

/-- The edges of the path `0, 1, …, m`, in closed form. -/
theorem pathEdges_range : ∀ m : ℕ,
    pathEdges (List.range (m + 1)) = (List.range m).map (fun i ↦ (i, i + 1))
  | 0 => rfl
  | m + 1 => by
      have h : (List.range (m + 1)).map (· + 1) = 1 :: ((List.range m).map (· + 1)).map (· + 1) := by
        conv_lhs => rw [List.range_succ_eq_map]
        simp
      conv_lhs => rw [List.range_succ_eq_map]
      rw [h, pathEdges_cons_cons, ← h, pathEdges_map_succ, pathEdges_range m]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.map_map]
      rfl

@[simp] theorem mem_pathEdges_range (m a b : ℕ) :
    ((a, b) ∈ pathEdges (List.range (m + 1))) ↔ (b = a + 1 ∧ a < m) := by
  rw [pathEdges_range]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨rfl, hi⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl, rfl⟩

@[simp] theorem cycleEdges_zero : cycleEdges 0 = [] := rfl

/-- The edges of a cycle: the path `0, 1, …, m` together with the wrap-around edge. -/
theorem cycleEdges_succ (k : ℕ) :
    cycleEdges (k + 1) = (List.range k).map (fun i ↦ (i, i + 1)) ++ [(k, 0)] := by
  rw [cycleEdges, List.range_succ, List.append_assoc,
    show ([k] ++ [0] : List ℕ) = [k, 0] from rfl, pathEdges_concat, ← List.range_succ,
    pathEdges_range]

@[simp] theorem mem_cycleEdges_succ (k a b : ℕ) :
    ((a, b) ∈ cycleEdges (k + 1)) ↔ ((b = a + 1 ∧ a < k) ∨ (a = k ∧ b = 0)) := by
  rw [cycleEdges_succ]
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hi⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, ha⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Membership in `cycleEdges` without splitting the length into a successor.  This is the form to
use when the length is a numeral, where `mem_cycleEdges_succ` does not fire. -/
theorem mem_cycleEdges (m a b : ℕ) :
    ((a, b) ∈ cycleEdges m) ↔ ((b = a + 1 ∧ a + 1 < m) ∨ (a + 1 = m ∧ b = 0)) := by
  cases m with
  | zero => simp only [cycleEdges_zero, List.not_mem_nil, false_iff]; omega
  | succ k => rw [mem_cycleEdges_succ]; omega

/-- The cycle on `m` vertices has `m` edges. -/
@[simp] theorem length_cycleEdges (m : ℕ) : (cycleEdges m).length = m := by
  cases m with
  | zero => simp
  | succ k => rw [cycleEdges_succ]; simp

/-- The edge list of a cycle repeats nothing: the wrap-around edge `(k, 0)` runs backwards, so it
cannot coincide with any of the forward steps `(i, i + 1)`. -/
theorem cycleEdges_nodup (m : ℕ) : (cycleEdges m).Nodup := by
  cases m with
  | zero => simp
  | succ k =>
    rw [cycleEdges_succ]
    refine List.Nodup.append (List.Nodup.map (fun a b h ↦ by injection h) List.nodup_range)
      (List.nodup_singleton _) ?_
    intro p hp hq
    simp only [List.mem_map, List.mem_range] at hp
    simp only [List.mem_singleton] at hq
    obtain ⟨i, -, rfl⟩ := hp
    exact absurd (congrArg Prod.snd hq) (by simp)


@[simp] theorem cliqueEdges_zero : cliqueEdges 0 = [] := rfl

@[simp] theorem cliqueEdges_one : cliqueEdges 1 = [] := rfl

@[simp] theorem mem_cliqueEdges (m a b : ℕ) : ((a, b) ∈ cliqueEdges m) ↔ (a < b ∧ b < m) := by
  simp only [cliqueEdges, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, -, x, ⟨hx, hix⟩, rfl, rfl⟩
    exact ⟨hix, hx⟩
  · rintro ⟨hab, hb⟩
    exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl, rfl⟩

/-- **The edge list of a clique repeats nothing**: it lists the pairs `(i, x)` with `i < x < m`
grouped by their first entry, and within a group the second entries are distinct. -/
theorem cliqueEdges_nodup (m : ℕ) : (cliqueEdges m).Nodup := by
  rw [cliqueEdges]
  refine List.nodup_flatMap.2 ⟨fun i _ ↦ (List.nodup_range.filter _).map fun a b h ↦ by
    injection h, List.nodup_range.imp fun {i j} hij ↦ ?_⟩
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro p ⟨a, -, rfl⟩ ⟨b, -, hb⟩
  exact hij (congrArg Prod.fst hb).symm

@[simp] theorem legEdges_zero (v off : ℕ) : legEdges v off 0 = [] := rfl

/-- A leg of `k` fresh vertices hung off vertex `0`, when the fresh vertices start at `1`, is just
the path `0, 1, …, k`. -/
theorem legEdges_zero_one (k : ℕ) : legEdges 0 1 k = pathEdges (List.range (k + 1)) := by
  rw [List.range_succ_eq_map]
  simp only [legEdges]

/-- A leg hung off vertex `0` whose fresh vertices also start at `0`: the same path, with a loop
at `0` in front of it (which `ofEdges` discards). -/
theorem legEdges_zero_zero (k : ℕ) : legEdges 0 0 k = pathEdges (0 :: List.range k) := by
  simp only [legEdges, Nat.add_zero, List.map_id_fun', id_eq]

@[simp] theorem mem_pathEdges_zero_cons_range (k a b : ℕ) :
    ((a, b) ∈ pathEdges (0 :: List.range k)) ↔
      ((a = 0 ∧ b = 0 ∧ 0 < k) ∨ (b = a + 1 ∧ a + 1 < k)) := by
  rcases k with _ | j
  · simp [pathEdges]
  · have h : (0 :: List.range (j + 1)) = 0 :: 0 :: (List.range j).map (· + 1) := by
      conv_lhs => rw [List.range_succ_eq_map]
    rw [h, pathEdges_cons_cons, ← List.range_succ_eq_map]
    simp only [List.mem_cons, Prod.mk.injEq, mem_pathEdges_range]
    omega

/-! ## Degenerate cases of the decorated cycles and trees

Each family below is an `ofEdges` over `Fin n`, so its degenerate cases are equalities of graphs
on the nose, not merely isomorphisms: the edge list literally becomes the edge list of a cycle, a
clique or a path. -/

theorem ofEdges_nil (n : ℕ) : ofEdges n [] = empty n := by
  rw [empty_eq_ofRel]
  rfl

/-- Two edge lists that meet the same unordered pairs of *distinct* vertices describe the same
graph: `ofEdges` ignores the orientation of each pair, and discards the diagonal. -/
theorem ofEdges_congr (n : ℕ) (es fs : List (ℕ × ℕ))
    (h : ∀ p q : ℕ, p ≠ q → (((p, q) ∈ es ∨ (q, p) ∈ es) ↔ ((p, q) ∈ fs ∨ (q, p) ∈ fs))) :
    ofEdges n es = ofEdges n fs := by
  refine eq_ofRel (ofEdges n es) (fun i j ↦ fs.contains (i.1, j.1)) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact h x.1 y.1 fun hv ↦ hxy (Fin.ext hv)

/-- Replacing a prefix of the edge list by an equivalent one does not change the graph.  This is
the shape the decorated families come in: a cycle or clique part, followed by the legs. -/
theorem ofEdges_append_congr (n : ℕ) (es fs gs : List (ℕ × ℕ))
    (h : ∀ p q : ℕ, p ≠ q → (((p, q) ∈ es ∨ (q, p) ∈ es) ↔ ((p, q) ∈ fs ∨ (q, p) ∈ fs))) :
    ofEdges n (es ++ gs) = ofEdges n (fs ++ gs) := by
  refine ofEdges_congr _ _ _ fun p q hpq ↦ ?_
  simp only [List.mem_append]
  obtain ⟨h1, h2⟩ := h p q hpq
  constructor
  · rintro ((he | hg) | (he | hg))
    · exact (h1 (Or.inl he)).imp Or.inl Or.inl
    · exact Or.inl (Or.inr hg)
    · exact (h1 (Or.inr he)).imp Or.inl Or.inl
    · exact Or.inr (Or.inr hg)
  · rintro ((he | hg) | (he | hg))
    · exact (h2 (Or.inl he)).imp Or.inl Or.inl
    · exact Or.inl (Or.inr hg)
    · exact (h2 (Or.inr he)).imp Or.inl Or.inl
    · exact Or.inr (Or.inr hg)

theorem ofEdges_cycleEdges (m : ℕ) : ofEdges m (cycleEdges m) = cycle m := by
  refine eq_ofRel (ofEdges m (cycleEdges m)) (fun i j ↦ (i.1 + 1) % m == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rcases m with _ | k
  · exact absurd x.isLt (by omega)
  · have hx : x.1 < k + 1 := x.isLt
    have hy : y.1 < k + 1 := y.isLt
    have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
    have e1 := succ_mod_eq_iff (d := k + 1) (x := x.1) (y := y.1) hx
    have e2 := succ_mod_eq_iff (d := k + 1) (x := y.1) (y := x.1) hy
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_cycleEdges_succ]
    omega

/-- The one-vertex "cycle" is a single loop, which `ofEdges` discards. -/
theorem ofEdges_cycleEdges_one_append (n : ℕ) (es : List (ℕ × ℕ)) :
    ofEdges n (cycleEdges 1 ++ es) = ofEdges n es := by
  have hcyc : ∀ a b : ℕ, ((a, b) ∈ cycleEdges 1) ↔ (a = 0 ∧ b = 0) := by
    intro a b; rw [mem_cycleEdges]; omega
  refine ofEdges_congr _ _ _ fun p q hpq ↦ ?_
  simp only [List.mem_append, hcyc]
  constructor
  · rintro ((⟨rfl, rfl⟩ | he) | (⟨rfl, rfl⟩ | he))
    · exact absurd rfl hpq
    · exact Or.inl he
    · exact absurd rfl hpq
    · exact Or.inr he
  · exact fun he ↦ he.imp Or.inr Or.inr

theorem ofEdges_cliqueEdges (m : ℕ) : ofEdges m (cliqueEdges m) = complete m := by
  rw [complete_eq_ofRel]
  refine eq_ofRel (ofEdges m (cliqueEdges m)) _ ?_
  intro x y hxy
  have hne : (x : Fin m).1 ≠ (y : Fin m).1 := fun h ↦ hxy (Fin.ext h)
  have hx : (x : Fin m).1 < m := x.isLt
  have hy : (y : Fin m).1 < m := y.isLt
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    List.contains_eq_mem]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_cliqueEdges, or_self, iff_true]
  omega

theorem ofEdges_legEdges_one (k : ℕ) : ofEdges (1 + k) (legEdges 0 1 k) = path (1 + k) := by
  refine eq_ofRel (ofEdges (1 + k) (legEdges 0 1 k)) (fun i j ↦ i.1 + 1 == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    legEdges_zero_one, List.contains_eq_mem]
  have hx : (x : Fin (1 + k)).1 < 1 + k := x.isLt
  have hy : (y : Fin (1 + k)).1 < 1 + k := y.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_pathEdges_range]
  omega

theorem ofEdges_legEdges_zero (k : ℕ) : ofEdges k (legEdges 0 0 k) = path k := by
  refine eq_ofRel (ofEdges k (legEdges 0 0 k)) (fun i j ↦ i.1 + 1 == j.1) ?_
  intro x y hxy
  simp only [ofEdges, ofRel_adj, hxy, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
    legEdges_zero_zero, List.contains_eq_mem]
  have hx : (x : Fin k).1 < k := x.isLt
  have hy : (y : Fin k).1 < k := y.isLt
  have hne : (x : Fin k).1 ≠ (y : Fin k).1 := fun h ↦ hxy (Fin.ext h)
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, mem_pathEdges_zero_cons_range]
  omega

/-- The legs of a spider split along a split of the list of leg lengths, the second block starting
where the first one left off. -/
theorem spiderEdges_append : ∀ (pre post : List ℕ) (off : ℕ),
    spiderEdges off (pre ++ post) = spiderEdges off pre ++ spiderEdges (off + pre.sum) post
  | [], _, off => by rw [List.nil_append, spiderEdges, List.nil_append, List.sum_nil, Nat.add_zero]
  | k :: pre, post, off => by
      rw [List.cons_append, spiderEdges, spiderEdges, spiderEdges_append pre post (off + k),
        List.append_assoc, List.sum_cons,
        show off + k + pre.sum = off + (k + pre.sum) from by omega]

theorem spiderEdges_replicate_zero : ∀ (off j : ℕ), spiderEdges off (List.replicate j 0) = []
  | _, 0 => rfl
  | off, j + 1 => by
      rw [List.replicate_succ, spiderEdges, legEdges_zero, List.nil_append,
        spiderEdges_replicate_zero (off + 0) j]

theorem pendantEdges_replicate_zero : ∀ (v off j : ℕ), pendantEdges v off (List.replicate j 0) = []
  | _, _, 0 => rfl
  | v, off, j + 1 => by
      rw [List.replicate_succ, pendantEdges, List.range_zero, List.map_nil, List.nil_append,
        pendantEdges_replicate_zero (v + 1) (off + 0) j]

/-- Pendant vertices attached beyond the end of the cycle are no vertices at all. -/
theorem pendantEdges_append_zero : ∀ (v off : ℕ) (ks : List ℕ),
    pendantEdges v off (ks ++ [0]) = pendantEdges v off ks
  | _, _, [] => by simp [pendantEdges]
  | v, off, k :: ks => by
      rw [List.cons_append, pendantEdges, pendantEdges, pendantEdges_append_zero (v + 1) (off + k)]

/-! ## Relabellings for the `ofEdges` families

The `IsoGraph` identities at the end of this file that are *not* on-the-nose equalities of
`CGraph`s — a two-legged spider is a path, a one-path theta graph is a path, a double star with
leaves on one side only is a star — all need an explicit relabelling of `Fin n`.  This block
collects those relabellings together with the membership lemmas for the edge lists they act on,
and, in each case, the piece of pure arithmetic that says the relabelling matches the edges up.
Keeping the arithmetic separate is not just tidiness: stated as one goal, the disjunction over
all the edge shapes is large enough that `omega` spends minutes on it. -/

@[simp] theorem pathEdges_nil : pathEdges [] = [] := rfl

@[simp] theorem pathEdges_singleton (a : ℕ) : pathEdges [a] = [] := rfl

theorem pathEdges_map_add (c : ℕ) : ∀ l : List ℕ,
    pathEdges (l.map (· + c)) = (pathEdges l).map (fun p ↦ (p.1 + c, p.2 + c))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      have ih := pathEdges_map_add c (b :: rest)
      simp only [List.map_cons] at ih ⊢
      rw [pathEdges_cons_cons, pathEdges_cons_cons, List.map_cons, ih]

theorem legEdges_succ (v off j : ℕ) :
    legEdges v off (j + 1) = (v, off) :: (List.range j).map (fun i ↦ (i + off, i + 1 + off)) := by
  have h : (List.range (j + 1)).map (· + off)
      = off :: ((List.range j).map (· + 1)).map (· + off) := by
    conv_lhs => rw [List.range_succ_eq_map]
    simp [Nat.add_assoc]
  rw [legEdges, h, pathEdges_cons_cons, ← h, pathEdges_map_add, pathEdges_range, List.map_map]
  rfl

@[simp] theorem mem_legEdges (v off k p q : ℕ) :
    ((p, q) ∈ legEdges v off k) ↔
      ((p = v ∧ q = off ∧ 0 < k) ∨ (off ≤ p ∧ q = p + 1 ∧ p + 1 < off + k)) := by
  rcases k with _ | j
  · simp only [legEdges, List.range_zero, List.map_nil, pathEdges_singleton, List.not_mem_nil,
      Nat.lt_irrefl, Nat.add_zero, false_iff, not_or, not_and]
    exact ⟨fun _ _ ↦ not_false, fun _ _ ↦ by omega⟩
  · rw [legEdges_succ]
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hp, hq⟩)
      · exact Or.inl ⟨rfl, rfl, Nat.succ_pos j⟩
      · exact Or.inr (by omega)
    · rintro (⟨rfl, rfl, -⟩ | ⟨h1, rfl, h3⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨p - off, by omega, by omega, by omega⟩

/-- A leg of `k` fresh vertices contributes `k` edges. -/
@[simp] theorem length_legEdges (v off k : ℕ) : (legEdges v off k).length = k := by
  cases k with
  | zero => simp [legEdges]
  | succ j => rw [legEdges_succ]; simp

/-- The edge list of a leg repeats nothing: the steps `(i + off, i + 1 + off)` are distinct, and
none of them can be the attaching edge `(v, off)`. -/
theorem legEdges_nodup (v off k : ℕ) : (legEdges v off k).Nodup := by
  cases k with
  | zero => simp [legEdges]
  | succ j =>
    rw [legEdges_succ]
    refine List.nodup_cons.mpr ⟨?_, List.Nodup.map (fun a b h ↦ by injection h; omega)
      List.nodup_range⟩
    intro hmem
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
    obtain ⟨i, -, -, h⟩ := hmem
    omega


/-- Folding the interval `[0, a]` of `Fin N` back on itself, fixing everything above `a`.  This
is the relabelling that straightens a two-legged spider into a path: the two legs, which run
outwards from the centre, become one run from `a` down to `0` and one from `0` up. -/
def foldAt (a N : ℕ) (h : a < N) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 ≤ a then a - p.1 else p.1, by have := p.isLt; split <;> omega⟩
  invFun p := ⟨if p.1 ≤ a then a - p.1 else p.1, by have := p.isLt; split <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 ≤ a then a - p.1 else p.1) ≤ a then a - (if p.1 ≤ a then a - p.1 else p.1)
      else (if p.1 ≤ a then a - p.1 else p.1)) = p.1
    by_cases h1 : p.1 ≤ a
    · rw [if_pos h1, if_pos (by omega : a - p.1 ≤ a)]
      omega
    · rw [if_neg h1, if_neg h1]
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 ≤ a then a - p.1 else p.1) ≤ a then a - (if p.1 ≤ a then a - p.1 else p.1)
      else (if p.1 ≤ a then a - p.1 else p.1)) = p.1
    by_cases h1 : p.1 ≤ a
    · rw [if_pos h1, if_pos (by omega : a - p.1 ≤ a)]
      omega
    · rw [if_neg h1, if_neg h1]

@[simp] theorem foldAt_apply (a N : ℕ) (h : a < N) (p : Fin N) :
    (foldAt a N h p).1 = if p.1 ≤ a then a - p.1 else p.1 := rfl

/-- The arithmetic heart of `spider_pair`: after folding `[0, a]` back on itself, the two legs
of the spider `[a, b]` become a single run of consecutive naturals.  Both sides are spelled out
in the shape produced by `mem_legEdges`. -/
theorem foldAt_pair_iff (a b p q : ℕ) (hp : p < 1 + a + b) (hq : q < 1 + a + b) :
    ((if p ≤ a then a - p else p) ≠ (if q ≤ a then a - q else q) ∧
        ((if p ≤ a then a - p else p) + 1 = (if q ≤ a then a - q else q) ∨
          (if q ≤ a then a - q else q) + 1 = (if p ≤ a then a - p else p))) ↔
      (p ≠ q ∧
        ((((p = 0 ∧ q = 1 ∧ 0 < a) ∨ (1 ≤ p ∧ q = p + 1 ∧ p + 1 < 1 + a)) ∨
            ((p = 0 ∧ q = 1 + a ∧ 0 < b) ∨ (1 + a ≤ p ∧ q = p + 1 ∧ p + 1 < 1 + a + b))) ∨
          (((q = 0 ∧ p = 1 ∧ 0 < a) ∨ (1 ≤ q ∧ p = q + 1 ∧ q + 1 < 1 + a)) ∨
            ((q = 0 ∧ p = 1 + a ∧ 0 < b) ∨ (1 + a ≤ q ∧ p = q + 1 ∧ q + 1 < 1 + a + b))))) := by
  constructor
  · rintro ⟨hne, h⟩
    by_cases h1 : p ≤ a <;> by_cases h2 : q ≤ a
    · rw [if_pos h1, if_pos h2] at hne h
      rcases h with h | h
      · -- `q + 1 = p`, an edge of the first leg traversed towards the centre
        by_cases hq0 : q = 0
        · exact ⟨by omega, Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))⟩
        · exact ⟨by omega, Or.inr (Or.inl (Or.inr ⟨by omega, by omega, by omega⟩))⟩
      · by_cases hp0 : p = 0
        · exact ⟨by omega, Or.inl (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))⟩
        · exact ⟨by omega, Or.inl (Or.inl (Or.inr ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_pos h1, if_neg h2] at hne h
      -- only `a - p + 1 = q` is possible, forcing `p = 0` and `q = 1 + a`
      exact ⟨by omega, Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_neg h1, if_pos h2] at hne h
      exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
    · rw [if_neg h1, if_neg h2] at hne h
      rcases h with h | h
      · exact ⟨by omega, Or.inl (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩
      · exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩
  · rintro ⟨-, (((h | h) | (h | h)) | ((h | h) | (h | h)))⟩ <;> split_ifs <;> omega

/-! ### Theta graphs with no internal vertices -/

theorem thetaEdges_replicate_zero : ∀ (off j : ℕ),
    thetaEdges off (List.replicate j 0) = List.replicate j (0, 1)
  | _, 0 => rfl
  | off, j + 1 => by
      rw [List.replicate_succ, thetaEdges, thetaEdges_replicate_zero off j, List.replicate_succ]

@[simp] theorem mem_thetaEdges_replicate_zero (off j p q : ℕ) :
    ((p, q) ∈ thetaEdges off (List.replicate j 0)) ↔ (0 < j ∧ p = 0 ∧ q = 1) := by
  rw [thetaEdges_replicate_zero]
  simp only [List.mem_replicate, Prod.mk.injEq, ne_eq]
  constructor
  · rintro ⟨hj, rfl, rfl⟩
    exact ⟨Nat.pos_of_ne_zero hj, rfl, rfl⟩
  · rintro ⟨hj, rfl, rfl⟩
    exact ⟨by omega, rfl, rfl⟩

/-! ### Theta graphs with a single path: rotating the tail -/

theorem mem_thetaEdges_singleton (k p q : ℕ) :
    ((p, q) ∈ thetaEdges 2 [k + 1]) ↔
      ((p = 0 ∧ q = 2) ∨ (p = 2 + k ∧ q = 1) ∨ (2 ≤ p ∧ q = p + 1 ∧ p < 2 + k)) := by
  simp only [thetaEdges, List.append_nil, List.mem_cons, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, rfl, h3⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨p - 2, by omega, by omega, by omega⟩)

/-- Rotating the interval `[1, N-1]` of `Fin N` one step down, fixing `0`.  This is the
relabelling that straightens a one-path theta graph into a path: the second pole, which sits at
`1`, gets moved to the far end. -/
def rotTail (N : ℕ) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1, by
    have := p.isLt; split_ifs <;> omega⟩
  invFun p := ⟨if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1, by
    have := p.isLt; split_ifs <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) = 0 then 0
      else if (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) = N - 1 then 1
      else (if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1) + 1) = p.1
    split_ifs <;> omega
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) = 0 then 0
      else if (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) = 1 then N - 1
      else (if p.1 = 0 then 0 else if p.1 = N - 1 then 1 else p.1 + 1) - 1) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim

@[simp] theorem rotTail_apply (N : ℕ) (p : Fin N) :
    (rotTail N p).1 = if p.1 = 0 then 0 else if p.1 = 1 then N - 1 else p.1 - 1 := rfl

/-- The arithmetic heart of `thetaGraph_singleton`: after rotating the tail, the two poles and the
one internal path of the theta graph become a single run of consecutive naturals.  Both sides are
spelled out in the exact shape produced by `mem_thetaEdges_singleton`. -/
theorem rotTail_pair_iff (k p q : ℕ) (hp : p < k + 3) (hq : q < k + 3) :
    ((if p = 0 then 0 else if p = 1 then k + 2 else p - 1) ≠
        (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) ∧
      ((if p = 0 then 0 else if p = 1 then k + 2 else p - 1) + 1 =
          (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) ∨
        (if q = 0 then 0 else if q = 1 then k + 2 else q - 1) + 1 =
          (if p = 0 then 0 else if p = 1 then k + 2 else p - 1))) ↔
      (p ≠ q ∧
        (((p = 0 ∧ q = 2) ∨ (p = 2 + k ∧ q = 1) ∨ (2 ≤ p ∧ q = p + 1 ∧ p < 2 + k)) ∨
          ((q = 0 ∧ p = 2) ∨ (q = 2 + k ∧ p = 1) ∨ (2 ≤ q ∧ p = q + 1 ∧ q < 2 + k)))) := by
  have dir : ∀ a b : ℕ, a < k + 3 → b < k + 3 →
      (((if a = 0 then 0 else if a = 1 then k + 2 else a - 1) + 1 =
          (if b = 0 then 0 else if b = 1 then k + 2 else b - 1)) ↔
        ((a = 0 ∧ b = 2) ∨ (a = 2 + k ∧ b = 1) ∨ (2 ≤ a ∧ b = a + 1 ∧ a < 2 + k))) := by
    intro a b ha hb
    split_ifs <;> first
      | omega
      | (rw [false_iff]; omega)
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨fun hpq ↦ hne (by rw [hpq]), Or.inl ((dir p q hp hq).1 h)⟩
    · exact ⟨fun hpq ↦ hne (by rw [hpq]), Or.inr ((dir q p hq hp).1 h)⟩
  · rintro ⟨-, h | h⟩
    · have h' := (dir p q hp hq).2 h
      refine ⟨?_, Or.inl h'⟩
      rw [← h']
      exact (Nat.lt_succ_self _).ne
    · have h' := (dir q p hq hp).2 h
      refine ⟨?_, Or.inr h'⟩
      rw [← h']
      exact ((Nat.lt_succ_self _).ne).symm

/-! ### Double stars -/

@[simp] theorem mem_doubleStarEdges (m n p q : ℕ) :
    ((p, q) ∈ ((0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
        ((List.range n).map fun i ↦ (1, 2 + m + i))))) ↔
      ((p = 0 ∧ q = 1) ∨ (p = 0 ∧ 2 ≤ q ∧ q < 2 + m) ∨
        (p = 1 ∧ 2 + m ≤ q ∧ q < 2 + m + n)) := by
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨q - 2, by omega, rfl, by omega⟩)
    · exact Or.inr (Or.inr ⟨q - (2 + m), by omega, rfl, by omega⟩)

/-- Swapping the vertices `0` and `1` of `Fin N`. -/
def swapZeroOne (N : ℕ) (h : 1 < N) : Equiv.Perm (Fin N) where
  toFun p := ⟨if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1, by
    have := p.isLt; split_ifs <;> omega⟩
  invFun p := ⟨if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1, by
    have := p.isLt; split_ifs <;> omega⟩
  left_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 0 then 1
      else if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 1 then 0
      else (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1)) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim
  right_inv p := by
    have hp := p.isLt
    refine Fin.ext ?_
    show (if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 0 then 1
      else if (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1) = 1 then 0
      else (if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1)) = p.1
    split_ifs <;> first | omega | exact (‹False›).elim

@[simp] theorem swapZeroOne_apply (N : ℕ) (h : 1 < N) (p : Fin N) :
    (swapZeroOne N h p).1 = if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1 := rfl

/-! ### The one-legged spider, as an edge list -/

theorem spiderEdges_replicate_one : ∀ (off n : ℕ),
    spiderEdges off (List.replicate n 1) = (List.range n).map (fun i ↦ (0, off + i))
  | _, 0 => rfl
  | off, n + 1 => by
      have ih := spiderEdges_replicate_one (off + 1) n
      rw [List.replicate_succ, spiderEdges, ih, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      simp only [legEdges, List.range_one, List.map_cons, List.map_nil, pathEdges_cons_cons,
        pathEdges_singleton, List.cons_append, List.nil_append, Nat.add_zero, Function.comp_def]
      congr 1
      · rw [Nat.zero_add]
      · exact List.map_congr_left fun i _ ↦ Prod.ext rfl (by omega)

@[simp] theorem mem_spiderEdges_replicate_one (off n p q : ℕ) :
    ((p, q) ∈ spiderEdges off (List.replicate n 1)) ↔ (p = 0 ∧ off ≤ q ∧ q < off + n) := by
  rw [spiderEdges_replicate_one]
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨q - off, by omega, rfl, by omega⟩

/-! ### Swapping the two centres of a double star -/

/-- The relabelling that exchanges the two centres of a double star, carrying the leaves of each
along with it. -/
def doubleStarSwapFwd (m n v : ℕ) : ℕ :=
  if v = 0 then 1 else if v = 1 then 0 else if v < 2 + m then v + n else v - m

theorem doubleStarSwapFwd_lt (m n v : ℕ) (h : v < 2 + m + n) :
    doubleStarSwapFwd m n v < 2 + n + m := by
  unfold doubleStarSwapFwd; split_ifs <;> omega

theorem doubleStarSwapFwd_fwd (m n v : ℕ) (h : v < 2 + m + n) :
    doubleStarSwapFwd n m (doubleStarSwapFwd m n v) = v := by
  unfold doubleStarSwapFwd
  split_ifs <;> first | omega | exact (‹False›).elim

/-- The relabelling that exchanges the two centres of a double star. -/
def doubleStarSwap (m n : ℕ) : Fin (2 + m + n) ≃ Fin (2 + n + m) where
  toFun p := ⟨doubleStarSwapFwd m n p.1, doubleStarSwapFwd_lt m n p.1 p.isLt⟩
  invFun p := ⟨doubleStarSwapFwd n m p.1, doubleStarSwapFwd_lt n m p.1 p.isLt⟩
  left_inv p := Fin.ext (doubleStarSwapFwd_fwd m n p.1 p.isLt)
  right_inv p := Fin.ext (doubleStarSwapFwd_fwd n m p.1 p.isLt)

@[simp] theorem doubleStarSwap_apply (m n : ℕ) (p : Fin (2 + m + n)) :
    (doubleStarSwap m n p).1 = doubleStarSwapFwd m n p.1 := rfl

/-- One path of a theta graph splits off the front of the edge list. -/
theorem thetaEdges_cons (off k : ℕ) (rest : List ℕ) :
    thetaEdges off (k :: rest) = thetaEdges off [k] ++ thetaEdges (off + k) rest := by
  cases k with
  | zero => rfl
  | succ j => simp only [thetaEdges, List.append_nil, Nat.add_assoc]

theorem mem_thetaEdges_single (off k p q : ℕ) :
    ((p, q) ∈ thetaEdges off [k]) ↔
      ((k = 0 ∧ p = 0 ∧ q = 1) ∨ (0 < k ∧ p = 0 ∧ q = off) ∨
        (0 < k ∧ p = off + k - 1 ∧ q = 1) ∨ (off ≤ p ∧ q = p + 1 ∧ p + 1 < off + k)) := by
  rcases k with _ | j
  · simp only [thetaEdges, List.mem_singleton, Prod.mk.injEq, true_and]
    omega
  · simp only [thetaEdges, List.append_nil, List.mem_cons, List.mem_map, List.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))
    · rintro (⟨h, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨h1, rfl, h3⟩)
      · exact absurd h (by omega)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨p - off, by omega, by omega, by omega⟩)

/-- Each of the `ks.length` paths of a theta graph contributes `ks[i] + 1` edges. -/
theorem length_thetaEdges : ∀ (off : ℕ) (ks : List ℕ), (∀ k ∈ ks, 0 < k) →
    (thetaEdges off ks).length = ks.sum + ks.length := by
  intro off ks
  induction ks generalizing off with
  | nil => intro _; rfl
  | cons k rest ih =>
    intro h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h k (by simp); omega⟩
    rw [thetaEdges_cons, List.length_append,
      ih (off + (j + 1)) fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]
    simp only [thetaEdges, List.append_nil, List.length_cons, List.length_map,
      List.length_range, List.sum_cons]
    omega

/-- Every theta edge has one of three shapes: out of the pole `0`, into the pole `1`, or a step
along the interior of a path. -/
theorem mem_thetaEdges_shape : ∀ (off : ℕ) (ks : List ℕ), 2 ≤ off → (∀ k ∈ ks, 0 < k) →
    ∀ p ∈ thetaEdges off ks,
      (p.1 = 0 ∧ off ≤ p.2 ∧ p.2 < off + ks.sum) ∨
      (p.2 = 1 ∧ off ≤ p.1 ∧ p.1 < off + ks.sum) ∨
      (off ≤ p.1 ∧ p.2 = p.1 + 1 ∧ p.2 < off + ks.sum) := by
  intro off ks
  induction ks generalizing off with
  | nil => simp [thetaEdges]
  | cons k rest ih =>
    intro hoff h p hp
    have hk : 0 < k := h k (by simp)
    rw [thetaEdges_cons, List.mem_append] at hp
    simp only [List.sum_cons]
    rcases hp with hp | hp
    · rw [mem_thetaEdges_single] at hp
      omega
    · have := ih (off + k) (by omega) (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) p hp
      omega

/-- No theta edge is a loop. -/
theorem thetaEdges_ne (off : ℕ) (ks : List ℕ) (hoff : 2 ≤ off) (h : ∀ k ∈ ks, 0 < k) :
    ∀ p ∈ thetaEdges off ks, p.1 ≠ p.2 := fun p hp ↦ by
  have := mem_thetaEdges_shape off ks hoff h p hp
  omega

/-- Both endpoints of a theta edge are vertices of `thetaGraph`. -/
theorem thetaEdges_lt (off : ℕ) (ks : List ℕ) (hoff : 2 ≤ off) (h : ∀ k ∈ ks, 0 < k) :
    ∀ p ∈ thetaEdges off ks, p.1 < off + ks.sum ∧ p.2 < off + ks.sum := fun p hp ↦ by
  have := mem_thetaEdges_shape off ks hoff h p hp
  omega

/-- The edge list of a theta graph lists no edge in both orientations. -/
theorem thetaEdges_no_rev (off : ℕ) (ks : List ℕ) (hoff : 2 ≤ off) (h : ∀ k ∈ ks, 0 < k) :
    ∀ p ∈ thetaEdges off ks, (p.2, p.1) ∉ thetaEdges off ks := fun p hp hrev ↦ by
  have h1 := mem_thetaEdges_shape off ks hoff h p hp
  have h2 := mem_thetaEdges_shape off ks hoff h _ hrev
  simp only at h2
  omega

/-- The edge list of a theta graph has no repeats. -/
theorem thetaEdges_nodup : ∀ (off : ℕ) (ks : List ℕ), 2 ≤ off → (∀ k ∈ ks, 0 < k) →
    (thetaEdges off ks).Nodup := by
  intro off ks
  induction ks generalizing off with
  | nil => simp [thetaEdges]
  | cons k rest ih =>
    intro hoff h
    have hk : 0 < k := h k (by simp)
    have hrest : ∀ x ∈ rest, 0 < x := fun x hx ↦ h x (List.mem_cons_of_mem _ hx)
    rw [thetaEdges_cons]
    refine List.Nodup.append ?_ (ih (off + k) (by omega) hrest) ?_
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [thetaEdges, List.append_nil, List.nodup_cons, List.mem_cons, List.mem_map,
        List.mem_range, Prod.mk.injEq, not_or]
      refine ⟨⟨by omega, ?_⟩, ?_, List.Nodup.map (fun a b hab ↦ by
        injection hab with h1 _; omega) List.nodup_range⟩
      · rintro ⟨i, -, hi, -⟩
        omega
      · rintro ⟨i, -, -, hi⟩
        omega
    · intro p hp hq
      have h1 := mem_thetaEdges_shape off [k] hoff (by simpa using hk) p hp
      have h2 := mem_thetaEdges_shape (off + k) rest (by omega) hrest p hq
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h1
      omega

/-- The relabelling that reads a theta graph with two paths off as a cycle: the first path is
traversed away from the pole `0`, the second one back towards it. -/
def thetaCycleFwd (a b v : ℕ) : ℕ :=
  if v = 0 then 0 else if v = 1 then a + 1 else if v < 2 + a then v - 1 else 2 * a + b + 3 - v

/-- The inverse of `thetaCycleFwd`. -/
def thetaCycleBwd (a b u : ℕ) : ℕ :=
  if u = 0 then 0 else if u ≤ a then u + 1 else if u = a + 1 then 1 else 2 * a + b + 3 - u

theorem thetaCycleFwd_lt (a b v : ℕ) (h : v < 2 + a + b) : thetaCycleFwd a b v < 2 + a + b := by
  unfold thetaCycleFwd
  split_ifs <;> omega

theorem thetaCycleBwd_lt (a b u : ℕ) (h : u < 2 + a + b) : thetaCycleBwd a b u < 2 + a + b := by
  unfold thetaCycleBwd
  split_ifs <;> omega

theorem thetaCycleBwd_fwd (a b v : ℕ) (h : v < 2 + a + b) :
    thetaCycleBwd a b (thetaCycleFwd a b v) = v := by
  unfold thetaCycleFwd thetaCycleBwd
  split_ifs <;> first | omega | exact (‹False›).elim

theorem thetaCycleFwd_bwd (a b u : ℕ) (h : u < 2 + a + b) :
    thetaCycleFwd a b (thetaCycleBwd a b u) = u := by
  unfold thetaCycleFwd thetaCycleBwd
  split_ifs <;> first | omega | exact (‹False›).elim

/-- The relabelling of `thetaGraph [a, b]` as `cycle (2 + a + b)`. -/
def thetaCyclePerm (a b : ℕ) : Equiv.Perm (Fin (2 + a + b)) where
  toFun p := ⟨thetaCycleFwd a b p.1, thetaCycleFwd_lt a b p.1 p.isLt⟩
  invFun p := ⟨thetaCycleBwd a b p.1, thetaCycleBwd_lt a b p.1 p.isLt⟩
  left_inv p := Fin.ext (thetaCycleBwd_fwd a b p.1 p.isLt)
  right_inv p := Fin.ext (thetaCycleFwd_bwd a b p.1 p.isLt)

@[simp] theorem thetaCyclePerm_apply (a b : ℕ) (p : Fin (2 + a + b)) :
    (thetaCyclePerm a b p).1 = thetaCycleFwd a b p.1 := rfl

/-- The arithmetic heart of `thetaGraph_pair`: one step forward around the cycle is one edge of
the first path, or one edge of the second path taken backwards. -/
theorem thetaCycle_step (a b p q : ℕ) (hp : p < 2 + a + b) (hq : q < 2 + a + b) :
    ((thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q) ↔
      ((p, q) ∈ thetaEdges 2 [a] ∨ (q, p) ∈ thetaEdges (2 + a) [b]) := by
  rw [mem_thetaEdges_single, mem_thetaEdges_single, succ_mod_eq_iff (thetaCycleFwd_lt a b p hp)]
  constructor
  · intro h
    unfold thetaCycleFwd at h
    split_ifs at h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first
      | (exfalso; omega)
      | (refine Or.inl (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inl (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inl (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> omega)
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))) <;> omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))) <;> omega)
  · intro h
    unfold thetaCycleFwd
    rcases h with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) |
      (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
      subst h2 <;>
      split_ifs <;>
      (try simp only [and_true, and_false, false_or, or_false]) <;>
      first | omega | exact (‹False›).elim

/-- One step forward around the cycle already forces the two endpoints apart. -/
theorem thetaCycle_step_ne (a b p q : ℕ) (hp : p < 2 + a + b)
    (h : (thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q) :
    thetaCycleFwd a b p ≠ thetaCycleFwd a b q := by
  intro he
  rw [← he] at h
  exact succ_mod_ne (by omega) (thetaCycleFwd_lt a b p hp) h

/-- Adjacency in `thetaGraph [a, b]` matches adjacency in `cycle (2 + a + b)` under
`thetaCycleFwd`. -/
theorem thetaCycle_adj_iff (a b p q : ℕ) (hp : p < 2 + a + b) (hq : q < 2 + a + b) :
    (thetaCycleFwd a b p ≠ thetaCycleFwd a b q ∧
        ((thetaCycleFwd a b p + 1) % (2 + a + b) = thetaCycleFwd a b q ∨
          (thetaCycleFwd a b q + 1) % (2 + a + b) = thetaCycleFwd a b p)) ↔
      (p ≠ q ∧
        (((p, q) ∈ thetaEdges 2 [a] ∨ (p, q) ∈ thetaEdges (2 + a) [b]) ∨
          ((q, p) ∈ thetaEdges 2 [a] ∨ (q, p) ∈ thetaEdges (2 + a) [b]))) := by
  constructor
  · rintro ⟨hne, hs | hs⟩
    · refine ⟨fun he ↦ hne (by rw [he]), ?_⟩
      rcases (thetaCycle_step a b p q hp hq).1 hs with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr h)
    · refine ⟨fun he ↦ hne (by rw [he]), ?_⟩
      rcases (thetaCycle_step a b q p hq hp).1 hs with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
  · rintro ⟨-, (h | h) | (h | h)⟩
    · have hs := (thetaCycle_step a b p q hp hq).2 (Or.inl h)
      exact ⟨thetaCycle_step_ne a b p q hp hs, Or.inl hs⟩
    · have hs := (thetaCycle_step a b q p hq hp).2 (Or.inr h)
      exact ⟨fun he ↦ thetaCycle_step_ne a b q p hq hs he.symm, Or.inr hs⟩
    · have hs := (thetaCycle_step a b q p hq hp).2 (Or.inl h)
      exact ⟨fun he ↦ thetaCycle_step_ne a b q p hq hs he.symm, Or.inr hs⟩
    · have hs := (thetaCycle_step a b p q hp hq).2 (Or.inr h)
      exact ⟨thetaCycle_step_ne a b p q hp hs, Or.inl hs⟩

/-! ### Theta graphs whose paths all carry one internal vertex -/

/-- The edges of such a theta graph: each of the `j` midpoints is joined to both poles. -/
theorem mem_thetaEdges_replicate_one : ∀ (j off p q : ℕ),
    ((p, q) ∈ thetaEdges off (List.replicate j 1)) ↔
      ((p = 0 ∧ off ≤ q ∧ q < off + j) ∨ (off ≤ p ∧ p < off + j ∧ q = 1))
  | 0, off, p, q => by
      simp only [List.replicate_zero, thetaEdges, List.not_mem_nil, false_iff]
      omega
  | j + 1, off, p, q => by
      rw [List.replicate_succ, thetaEdges_cons, List.mem_append, mem_thetaEdges_single,
        mem_thetaEdges_replicate_one j (off + 1) p q]
      omega

/-! ## Two-colourings of the decorated families

A spider, a cycle with pendant vertices, and a tadpole are all two-colourable, but the colour of a
vertex is not a function of its number alone: it depends on which leg or which pendant block the
vertex sits in.  The two functions here recover that information from the list of block lengths,
by the same recursion the edge lists themselves are built by. -/

/-! ### The owner of a pendant vertex -/

/-- For a vertex `x` of `cyclePendant m ks`: `x` itself if it lies on the cycle, and one more than
the cycle vertex it hangs off if it is a pendant.  Its parity is a proper two-colouring when the
cycle is even. -/
def pendantOwner (m : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ
  | _, _, [], x => x
  | v, off, k :: ks, x =>
      if x < m then x else if x < off + k then v + 1 else pendantOwner m (v + 1) (off + k) ks x

theorem pendantOwner_of_lt : ∀ (m v off : ℕ) (ks : List ℕ) (x : ℕ), x < m →
    pendantOwner m v off ks x = x
  | _, _, _, [], _, _ => rfl
  | m, v, off, _ :: _, x, h => by rw [pendantOwner, if_pos h]

/-- Every pendant edge runs from one of the cycle vertices `v, …, v + ks.length - 1` to a fresh
vertex in `[off, off + ks.sum)`. -/
theorem mem_pendantEdges_bound : ∀ (v off : ℕ) (ks : List ℕ) (p q : ℕ),
    (p, q) ∈ pendantEdges v off ks →
      (v ≤ p ∧ p < v + ks.length) ∧ (off ≤ q ∧ q < off + ks.sum)
  | _, _, [], _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, q => by
      intro h
      rw [pendantEdges, List.mem_append] at h
      simp only [List.length_cons, List.sum_cons]
      rcases h with h | h
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨i, hi, rfl, rfl⟩ := h
        omega
      · have := mem_pendantEdges_bound (v + 1) (off + k) ks p q h
        omega

/-- Every fresh vertex of `pendantEdges v off ks` hangs off some cycle vertex. -/
theorem exists_mem_pendantEdges : ∀ (v off : ℕ) (ks : List ℕ) (q : ℕ), off ≤ q →
    q < off + ks.sum → ∃ p, (p, q) ∈ pendantEdges v off ks := by
  intro v off ks
  induction ks generalizing v off with
  | nil => intro q h1 h2; simp only [List.sum_nil, Nat.add_zero] at h2; omega
  | cons k rest ih =>
    intro q h1 h2
    simp only [List.sum_cons] at h2
    by_cases hq : q < off + k
    · refine ⟨v, ?_⟩
      rw [pendantEdges, List.mem_append]
      exact Or.inl (List.mem_map.2 ⟨q - off, List.mem_range.2 (by omega), by
        simp only [Prod.mk.injEq, true_and]; omega⟩)
    · obtain ⟨p, hp⟩ := ih (v + 1) (off + k) q (by omega) (by omega)
      exact ⟨p, by rw [pendantEdges, List.mem_append]; exact Or.inr hp⟩

/-- A pendant vertex hangs off exactly one cycle vertex. -/
theorem pendantEdges_snd_unique : ∀ (v off : ℕ) (ks : List ℕ) (p p' q : ℕ),
    (p, q) ∈ pendantEdges v off ks → (p', q) ∈ pendantEdges v off ks → p = p' := by
  intro v off ks
  induction ks generalizing v off with
  | nil => intro p p' q h; simp [pendantEdges] at h
  | cons k rest ih =>
    intro p p' q h h'
    rw [pendantEdges, List.mem_append] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h h'
      obtain ⟨i, -, rfl, -⟩ := h
      obtain ⟨j, -, rfl, -⟩ := h'
      rfl
    · exfalso
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
      obtain ⟨i, hi, -, hqi⟩ := h
      have := mem_pendantEdges_bound (v + 1) (off + k) rest p' q h'
      omega
    · exfalso
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h'
      obtain ⟨i, hi, -, hqi⟩ := h'
      have := mem_pendantEdges_bound (v + 1) (off + k) rest p q h
      omega
    · exact ih (v + 1) (off + k) p p' q h h'

/-- Hanging `ks` pendants contributes `ks.sum` edges. -/
@[simp] theorem length_pendantEdges : ∀ (v off : ℕ) (ks : List ℕ),
    (pendantEdges v off ks).length = ks.sum
  | _, _, [] => rfl
  | v, off, k :: ks => by
      rw [pendantEdges, List.length_append, List.length_map, List.length_range,
        length_pendantEdges (v + 1) (off + k) ks, List.sum_cons]

/-- The edge list of a family of pendants repeats nothing: the `k` edges hung on `v` all end at
distinct fresh vertices, and the later blocks live above `off + k`. -/
theorem pendantEdges_nodup : ∀ (v off : ℕ) (ks : List ℕ), (pendantEdges v off ks).Nodup
  | _, _, [] => by simp [pendantEdges]
  | v, off, k :: ks => by
      rw [pendantEdges]
      refine List.Nodup.append (List.Nodup.map (fun a b h ↦ by injection h with h1 h2; omega)
        List.nodup_range) (pendantEdges_nodup (v + 1) (off + k) ks) ?_
      intro p hp hq
      simp only [List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      have := mem_pendantEdges_bound (v + 1) (off + k) ks v (off + i) hq
      omega


/-- Along every pendant edge the parity of `pendantOwner` changes. -/
theorem pendantOwner_parity (m : ℕ) : ∀ (v off : ℕ) (ks : List ℕ) (p q : ℕ),
    v + ks.length ≤ m → m ≤ off → (p, q) ∈ pendantEdges v off ks →
      (pendantOwner m v off ks p + pendantOwner m v off ks q) % 2 = 1
  | _, _, [], _, _, _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, q, hv, hoff => by
      intro h
      rw [pendantEdges, List.mem_append] at h
      rcases h with h | h
      · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at h
        obtain ⟨i, hi, rfl, rfl⟩ := h
        rw [pendantOwner, if_pos (by simp only [List.length_cons] at hv; omega), pendantOwner,
          if_neg (by omega), if_pos (by omega)]
        omega
      · have hb := mem_pendantEdges_bound (v + 1) (off + k) ks p q h
        simp only [List.length_cons] at hv
        have hrec := pendantOwner_parity m (v + 1) (off + k) ks p q (by omega) (by omega) h
        rw [pendantOwner_of_lt m (v + 1) (off + k) ks p (by omega)] at hrec
        rwa [pendantOwner, if_pos (by omega), pendantOwner, if_neg (by omega), if_neg (by omega)]

/-! ### Parity in the folded cube -/

/-- Positions where `x` and `y` are both `true` are counted twice on the right, so the number of
positions where they differ has the same parity as the total number of `true`s. -/
theorem card_ne_add_two_mul (n : ℕ) (x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ x i ≠ y i).card
        + 2 * (Finset.univ.filter fun i ↦ x i = true ∧ y i = true).card
      = (Finset.univ.filter fun i ↦ x i = true).card
        + (Finset.univ.filter fun i ↦ y i = true).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases x i <;> cases y i <;> simp

theorem card_ne_parity (n : ℕ) (x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ x i ≠ y i).card % 2
      = ((Finset.univ.filter fun i ↦ x i = true).card
          + (Finset.univ.filter fun i ↦ y i = true).card) % 2 := by
  have := card_ne_add_two_mul n x y
  omega

/-- The bit-string whose first `k` coordinates are `true`.  Running `k` from `0` to `n` walks from
one antipode of the cube to the other, one coordinate at a time. -/
def prefixVec (n k : ℕ) : Fin n → Bool := fun i ↦ decide (i.1 < k)

theorem card_prefixVec_step (n k : ℕ) (hk : k < n) :
    (Finset.univ.filter fun i ↦ prefixVec n k i ≠ prefixVec n (k + 1) i).card = 1 := by
  rw [show (Finset.univ.filter fun i ↦ prefixVec n k i ≠ prefixVec n (k + 1) i)
      = {(⟨k, hk⟩ : Fin n)} from ?_]
  · simp
  · ext i
    simp only [prefixVec, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, decide_eq_decide,
      Finset.mem_singleton, Fin.ext_iff]
    omega

theorem card_prefixVec_full (n : ℕ) :
    (Finset.univ.filter fun i ↦ prefixVec n 0 i ≠ prefixVec n n i).card = n := by
  rw [show (Finset.univ.filter fun i ↦ prefixVec n 0 i ≠ prefixVec n n i) = Finset.univ from ?_]
  · simp
  · ext i
    simp only [prefixVec, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, decide_eq_decide,
      iff_true]
    omega

/-- Splitting the Hamming distance of two bit-strings of length `n + 1` off its first coordinate:
what `hypercube_succ` runs on. -/
theorem card_ne_succ (n : ℕ) (x y : Fin (n + 1) → Bool) :
    (Finset.univ.filter fun i : Fin (n + 1) ↦ x i ≠ y i).card
      = (if x 0 ≠ y 0 then 1 else 0)
        + (Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]

section
variable {G H : CGraph}

/-! ### Degree multisets of the binary constructions -/

theorem univ_val_sum' (α β : Type*) [Fintype α] [Fintype β] :
    (Finset.univ : Finset (α ⊕ β)).val
      = (Finset.univ : Finset α).val.map Sum.inl + (Finset.univ : Finset β).val.map Sum.inr :=
  rfl

/-! ### The degrees of a path -/

theorem path_adj {n : ℕ} (i j : Fin n) :
    (path n).Adj i j = (decide (i ≠ j) && ((i.1 + 1 == j.1) || (j.1 + 1 == i.1))) :=
  rfl

/-! ### Degree multisets of the four products -/

theorem univ_val_map_prod' {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℕ) :
    (Finset.univ : Finset (α × β)).val.map (fun p ↦ f p.1 p.2)
      = (Finset.univ : Finset α).val.bind fun a ↦ (Finset.univ : Finset β).val.map (f a) := by
  rw [← Finset.univ_product_univ, Finset.product_val]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind]
  exact Multiset.bind_congr fun a _ ↦ Multiset.map_map _ _ _

/-! ### Clique numbers of the cartesian, tensor and lexicographic products -/

end

section
variable {G H : CGraph}
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
private theorem clique_card_le {S : SimpleGraph X} {t : Finset X} (h : S.IsClique (t : Set X)) :
    t.card ≤ S.cliqueNum :=
  h.card_le_cliqueNum

omit [Fintype X] [DecidableEq X] in
private theorem cliqueNum_le_of_forall {S : SimpleGraph X} {n : ℕ}
    (h : ∀ t : Finset X, S.IsClique (t : Set X) → t.card ≤ n) : S.cliqueNum ≤ n := by
  obtain ⟨t, ht, hcard⟩ := S.exists_isNClique_cliqueNum
  exact hcard ▸ h t ht

omit [Fintype X] [DecidableEq X] in
private theorem exists_isClique_card {S : SimpleGraph X} {n : ℕ} (h : n ≤ S.cliqueNum) :
    ∃ t : Finset X, S.IsClique (t : Set X) ∧ t.card = n := by
  obtain ⟨t, ht, hcard⟩ := S.exists_isNClique_cliqueNum
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq (s := t) (n := n) (by omega)
  exact ⟨u, ht.subset (by exact_mod_cast hu), hucard⟩

omit [DecidableEq X] in
private theorem one_le_cliqueNum_simple {S : SimpleGraph X} (a : X) : 1 ≤ S.cliqueNum := by
  have h : S.IsClique (({a} : Finset X) : Set X) := by simp
  simpa using clique_card_le h

/-- The fibre bound: a finset whose first-coordinate projection is a clique and whose fibres
project to cliques has at most `ω(S) * ω(T)` elements. -/
private theorem card_le_mul_of_fibers {S : SimpleGraph X} {T : SimpleGraph Y}
    (s : Finset (X × Y)) (h1 : S.IsClique ((s.image Prod.fst : Finset X) : Set X))
    (h2 : ∀ a : X, T.IsClique (((s.filter fun p ↦ p.1 = a).image Prod.snd : Finset Y) : Set Y)) :
    s.card ≤ S.cliqueNum * T.cliqueNum := by
  have hfib : ∀ a : X, (s.filter fun p ↦ p.1 = a).card ≤ T.cliqueNum := by
    intro a
    have hinj : Set.InjOn Prod.snd
        (((s.filter fun p ↦ p.1 = a) : Finset (X × Y)) : Set (X × Y)) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact Prod.ext (hx.2.trans hy.2.symm) hxy
    rw [← Finset.card_image_of_injOn hinj]
    exact clique_card_le (h2 a)
  calc s.card = ∑ a ∈ s.image Prod.fst, (s.filter fun p ↦ p.1 = a).card :=
        Finset.card_eq_sum_card_fiberwise fun x hx ↦ Finset.mem_image_of_mem _ hx
    _ ≤ ∑ _a ∈ s.image Prod.fst, T.cliqueNum := Finset.sum_le_sum fun a _ ↦ hfib a
    _ = (s.image Prod.fst).card * T.cliqueNum := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ S.cliqueNum * T.cliqueNum := Nat.mul_le_mul_right _ (clique_card_le h1)

/-- A clique of a graph with cartesian-product adjacency lies in a single row or a single column,
so its clique number is the larger of the two.  The two vertices `a₀` and `b₀` are what rules out
the empty product, whose clique number is `0`. -/
theorem cliqueNum_of_cartesian_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} (a₀ : X) (b₀ : Y)
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ (p.1 = q.1 ∧ T.Adj p.2 q.2) ∨ (S.Adj p.1 q.1 ∧ p.2 = q.2)) :
    P.cliqueNum = max S.cliqueNum T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ ?_) (max_le ?_ ?_)
  · by_cases hcard : s.card ≤ 1
    · exact hcard.trans (le_max_of_le_left (one_le_cliqueNum_simple a₀))
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
      rcases (hadj p q).1 (hs (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq) hpq) with
        ⟨h1, -⟩ | ⟨-, h1⟩
      · -- every vertex of `s` lies in the row `p.1`
        have hall : ∀ r ∈ s, r.1 = p.1 := by
          intro r hr
          by_contra hne
          have hrp : r.2 = p.2 := by
            rcases (hadj r p).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hp)
              fun h ↦ hne (congrArg Prod.fst h)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd h hne
            · exact h
          have hrq : r.2 = q.2 := by
            rcases (hadj r q).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hq)
              fun h ↦ hne ((congrArg Prod.fst h).trans h1.symm)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd (h.trans h1.symm) hne
            · exact h
          exact hpq (Prod.ext h1 (hrp.symm.trans hrq))
        have hinj : Set.InjOn Prod.snd (s : Set (X × Y)) := fun x hx y hy hxy ↦
          Prod.ext ((hall x (Finset.mem_coe.1 hx)).trans (hall y (Finset.mem_coe.1 hy)).symm) hxy
        have hclique : T.IsClique ((s.image Prod.snd : Finset Y) : Set Y) := by
          intro b hb b' hb' hne
          rw [Finset.coe_image, Set.mem_image] at hb hb'
          obtain ⟨x, hx, rfl⟩ := hb
          obtain ⟨y, hy, rfl⟩ := hb'
          have hxy : x ≠ y := fun h ↦ hne (congrArg Prod.snd h)
          rcases (hadj x y).1 (hs hx hy hxy) with ⟨-, h⟩ | ⟨-, h⟩
          · exact h
          · exact absurd (Prod.ext ((hall x (Finset.mem_coe.1 hx)).trans
              (hall y (Finset.mem_coe.1 hy)).symm) h) hxy
        exact le_max_of_le_right (Finset.card_image_of_injOn hinj ▸ clique_card_le hclique)
      · -- every vertex of `s` lies in the column `p.2`
        have hall : ∀ r ∈ s, r.2 = p.2 := by
          intro r hr
          by_contra hne
          have hrp : r.1 = p.1 := by
            rcases (hadj r p).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hp)
              fun h ↦ hne (congrArg Prod.snd h)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd h hne
          have hrq : r.1 = q.1 := by
            rcases (hadj r q).1 (hs (Finset.mem_coe.2 hr) (Finset.mem_coe.2 hq)
              fun h ↦ hne ((congrArg Prod.snd h).trans h1.symm)) with ⟨h, -⟩ | ⟨-, h⟩
            · exact h
            · exact absurd (h.trans h1.symm) hne
          exact hpq (Prod.ext (hrp.symm.trans hrq) h1)
        have hinj : Set.InjOn Prod.fst (s : Set (X × Y)) := fun x hx y hy hxy ↦
          Prod.ext hxy ((hall x (Finset.mem_coe.1 hx)).trans (hall y (Finset.mem_coe.1 hy)).symm)
        have hclique : S.IsClique ((s.image Prod.fst : Finset X) : Set X) := by
          intro a ha a' ha' hne
          rw [Finset.coe_image, Set.mem_image] at ha ha'
          obtain ⟨x, hx, rfl⟩ := ha
          obtain ⟨y, hy, rfl⟩ := ha'
          have hxy : x ≠ y := fun h ↦ hne (congrArg Prod.fst h)
          rcases (hadj x y).1 (hs hx hy hxy) with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd (Prod.ext h ((hall x (Finset.mem_coe.1 hx)).trans
              (hall y (Finset.mem_coe.1 hy)).symm)) hxy
          · exact h
        exact le_max_of_le_left (Finset.card_image_of_injOn hinj ▸ clique_card_le hclique)
  · -- a maximum clique of `S`, times the single vertex `b₀`
    obtain ⟨t, ht, htcard⟩ := exists_isClique_card (le_refl S.cliqueNum)
    have hcard : (t ×ˢ ({b₀} : Finset Y)).card = S.cliqueNum := by
      rw [Finset.card_product, Finset.card_singleton, mul_one, htcard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hx hy
    have hne : x.1 ≠ y.1 := fun h ↦ hxy (Prod.ext h (hx.2.trans hy.2.symm))
    exact (hadj x y).2 (Or.inr ⟨ht (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) hne,
      hx.2.trans hy.2.symm⟩)
  · -- the single vertex `a₀`, times a maximum clique of `T`
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (le_refl T.cliqueNum)
    have hcard : (({a₀} : Finset X) ×ˢ u).card = T.cliqueNum := by
      rw [Finset.card_product, Finset.card_singleton, one_mul, hucard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hx hy
    have hne : x.2 ≠ y.2 := fun h ↦ hxy (Prod.ext (hx.1.trans hy.1.symm) h)
    exact (hadj x y).2 (Or.inl ⟨hx.1.trans hy.1.symm,
      hu (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2) hne⟩)

/-- Both projections of a clique of a graph with tensor-product adjacency are injective cliques,
and conversely any pairing of two cliques of the same size is one, so its clique number is the
smaller of the two. -/
theorem cliqueNum_of_tensor_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ S.Adj p.1 q.1 ∧ T.Adj p.2 q.2) :
    P.cliqueNum = min S.cliqueNum T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ le_min ?_ ?_) ?_
  · have hinj : Set.InjOn Prod.fst (s : Set (X × Y)) := by
      intro x hx y hy hxy
      by_contra hne
      exact ((hadj x y).1 (hs hx hy hne)).1.ne hxy
    have hclique : S.IsClique ((s.image Prod.fst : Finset X) : Set X) := by
      intro a ha a' ha' hne
      rw [Finset.coe_image, Set.mem_image] at ha ha'
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := ha'
      exact ((hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.fst h))).1
    exact Finset.card_image_of_injOn hinj ▸ clique_card_le hclique
  · have hinj : Set.InjOn Prod.snd (s : Set (X × Y)) := by
      intro x hx y hy hxy
      by_contra hne
      exact ((hadj x y).1 (hs hx hy hne)).2.ne hxy
    have hclique : T.IsClique ((s.image Prod.snd : Finset Y) : Set Y) := by
      intro b hb b' hb' hne
      rw [Finset.coe_image, Set.mem_image] at hb hb'
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨y, hy, rfl⟩ := hb'
      exact ((hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.snd h))).2
    exact Finset.card_image_of_injOn hinj ▸ clique_card_le hclique
  · obtain ⟨t, ht, htcard⟩ := exists_isClique_card (min_le_left S.cliqueNum T.cliqueNum)
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (min_le_right S.cliqueNum T.cliqueNum)
    have hcards : Fintype.card {a // a ∈ t} = Fintype.card {b // b ∈ u} := by
      rw [Fintype.card_coe, Fintype.card_coe, htcard, hucard]
    obtain ⟨e⟩ : Nonempty ({a // a ∈ t} ≃ {b // b ∈ u}) := ⟨Fintype.equivOfCardEq hcards⟩
    have hfinj : Function.Injective fun z : {a // a ∈ t} ↦ (z.1, (e z).1) :=
      fun z z' hzz' ↦ Subtype.ext (congrArg Prod.fst hzz')
    have hcard : (t.attach.image fun z ↦ (z.1, (e z).1)).card = min S.cliqueNum T.cliqueNum := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_attach, htcard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro p hp q hq hpq
    rw [Finset.coe_image, Set.mem_image] at hp hq
    obtain ⟨z, -, rfl⟩ := hp
    obtain ⟨z', -, rfl⟩ := hq
    have hzz' : z ≠ z' := fun h ↦ hpq (by rw [h])
    exact (hadj _ _).2
      ⟨ht (Finset.mem_coe.2 z.2) (Finset.mem_coe.2 z'.2) fun h ↦ hzz' (Subtype.ext h),
        hu (Finset.mem_coe.2 (e z).2) (Finset.mem_coe.2 (e z').2)
          fun h ↦ hzz' (e.injective (Subtype.ext h))⟩

/-- A graph with lexicographic-product adjacency multiplies the two clique numbers. -/
theorem cliqueNum_of_lex_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, P.Adj p q ↔ S.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ T.Adj p.2 q.2)) :
    P.cliqueNum = S.cliqueNum * T.cliqueNum := by
  refine le_antisymm (cliqueNum_le_of_forall fun s hs ↦ card_le_mul_of_fibers s ?_ ?_) ?_
  · intro a ha a' ha' hne
    rw [Finset.coe_image, Set.mem_image] at ha ha'
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    rcases (hadj x y).1 (hs hx hy fun h ↦ hne (congrArg Prod.fst h)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  · intro a b hb b' hb' hne
    rw [Finset.coe_image, Set.mem_image] at hb hb'
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨y, hy, rfl⟩ := hb'
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    rcases (hadj x y).1 (hs (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1)
      fun h ↦ hne (congrArg Prod.snd h)) with h | ⟨-, h⟩
    · exact absurd (hx.2.trans hy.2.symm) h.ne
    · exact h
  · obtain ⟨t, ht, htcard⟩ := exists_isClique_card (le_refl S.cliqueNum)
    obtain ⟨u, hu, hucard⟩ := exists_isClique_card (le_refl T.cliqueNum)
    have hcard : (t ×ˢ u).card = S.cliqueNum * T.cliqueNum := by
      rw [Finset.card_product, htcard, hucard]
    refine hcard ▸ clique_card_le (S := P) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    by_cases h : x.1 = y.1
    · exact (hadj x y).2 (Or.inr ⟨h, hu (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hy.2)
        fun h2 ↦ hxy (Prod.ext h h2)⟩)
    · exact (hadj x y).2 (Or.inl (ht (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) h))

end

section
variable {G H : CGraph}
variable {X Y : Type} [Fintype X] [Fintype Y]

/-! ### The join -/

omit [Fintype X] [Fintype Y] in
/-- Two colourings with disjoint palettes colour a join. -/
theorem colorable_of_join_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {J : SimpleGraph (X ⊕ Y)} {a b : ℕ}
    (hll : ∀ x y, J.Adj (.inl x) (.inl y) → S.Adj x y)
    (hrr : ∀ x y, J.Adj (.inr x) (.inr y) → T.Adj x y)
    (hS : S.Colorable a) (hT : T.Colorable b) : J.Colorable (a + b) := by
  obtain ⟨cS⟩ := hS
  obtain ⟨cT⟩ := hT
  refine ⟨SimpleGraph.Coloring.mk
    (Sum.elim (fun x ↦ (cS x).castAdd b) (fun y ↦ (cT y).natAdd a)) ?_⟩
  intro v w hadj
  cases v with
  | inl x =>
    cases w with
    | inl y =>
      refine fun h ↦ cS.valid (hll x y hadj) (Fin.ext ?_)
      simpa using congrArg Fin.val h
    | inr y =>
      refine Fin.ne_of_val_ne ?_
      have := (cS x).isLt
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd]
      omega
  | inr x =>
    cases w with
    | inl y =>
      refine Fin.ne_of_val_ne ?_
      have := (cS y).isLt
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd]
      omega
    | inr y =>
      refine fun h ↦ cT.valid (hrr x y hadj) (Fin.ext ?_)
      simpa using congrArg Fin.val h

/-- In a join every colour is used on one side only, so the two palettes are disjoint and the
chromatic numbers add. -/
theorem chromaticNumber_add_le_of_join_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {J : SimpleGraph (X ⊕ Y)} {n : ℕ}
    (hll : ∀ x y, S.Adj x y → J.Adj (.inl x) (.inl y))
    (hrr : ∀ x y, T.Adj x y → J.Adj (.inr x) (.inr y))
    (hlr : ∀ x y, J.Adj (.inl x) (.inr y))
    (hc : J.Colorable n) : S.chromaticNumber + T.chromaticNumber ≤ n := by
  classical
  obtain ⟨c⟩ := hc
  set A : Finset (Fin n) := Finset.univ.image fun x : X ↦ c (.inl x) with hA
  set B : Finset (Fin n) := Finset.univ.image fun y : Y ↦ c (.inr y) with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hA, Finset.mem_image] at hz
    rw [hB, Finset.mem_image] at hz'
    obtain ⟨x, -, hx⟩ := hz
    obtain ⟨y, -, hy⟩ := hz'
    exact c.valid (hlr x y) (hx.trans hy.symm)
  have hcard : A.card + B.card ≤ n := by
    have h := Finset.card_le_univ (A ∪ B)
    rwa [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at h
  have hSA : S.Colorable A.card := by
    have C : S.Coloring {z // z ∈ A} :=
      SimpleGraph.Coloring.mk (fun x ↦ ⟨c (.inl x), by rw [hA, Finset.mem_image]; exact ⟨x, by simp⟩⟩)
        fun {v w} h he ↦ c.valid (hll v w h) (congrArg Subtype.val he)
    simpa using C.colorable
  have hTB : T.Colorable B.card := by
    have C : T.Coloring {z // z ∈ B} :=
      SimpleGraph.Coloring.mk (fun y ↦ ⟨c (.inr y), by rw [hB, Finset.mem_image]; exact ⟨y, by simp⟩⟩)
        fun {v w} h he ↦ c.valid (hrr v w h) (congrArg Subtype.val he)
    simpa using C.colorable
  calc S.chromaticNumber + T.chromaticNumber
      ≤ (A.card : ℕ∞) + (B.card : ℕ∞) :=
        add_le_add hSA.chromaticNumber_le hTB.chromaticNumber_le
    _ = ((A.card + B.card : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ (n : ℕ∞) := Nat.cast_le.2 hcard

/-! ### The cartesian product -/

omit [Fintype X] [Fintype Y] in
/-- Colouring `G □ H` by the *sum* of the two coordinate colours, in `ZMod n`: an edge changes
exactly one coordinate, so the sums differ by cancellation. -/
theorem colorable_of_cartesian_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} {n : ℕ}
    (hadj : ∀ p q : X × Y, P.Adj p q → (p.1 = q.1 ∧ T.Adj p.2 q.2) ∨ (S.Adj p.1 q.1 ∧ p.2 = q.2))
    (hS : S.Colorable n) (hT : T.Colorable n) : P.Colorable n := by
  cases n with
  | zero =>
    haveI : IsEmpty X := SimpleGraph.isEmpty_of_colorable_zero hS
    haveI : IsEmpty (X × Y) := inferInstance
    exact SimpleGraph.Colorable.of_isEmpty 0
  | succ m =>
    obtain ⟨cS⟩ := hS
    obtain ⟨cT⟩ := hT
    refine ⟨SimpleGraph.Coloring.mk (fun p ↦ cS p.1 + cT p.2) ?_⟩
    intro v w hvw
    show cS v.1 + cT v.2 ≠ cS w.1 + cT w.2
    rcases hadj v w hvw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      exact fun h ↦ cT.valid h2 (add_left_cancel h)
    · rw [h2]
      exact fun h ↦ cS.valid h1 (add_right_cancel h)

omit [Fintype X] [Fintype Y] in
/-- A copy of `G` sits inside `G □ H` as a row. -/
theorem chromaticNumber_le_of_cartesian_left {S : SimpleGraph X}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, (S.Adj p.1 q.1 ∧ p.2 = q.2) → P.Adj p q) (y : Y) :
    S.chromaticNumber ≤ P.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom
    ⟨fun x ↦ (x, y), fun {a b} h ↦ hadj (a, y) (b, y) ⟨h, rfl⟩⟩

omit [Fintype X] [Fintype Y] in
/-- A copy of `H` sits inside `G □ H` as a column. -/
theorem chromaticNumber_le_of_cartesian_right {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)}
    (hadj : ∀ p q : X × Y, (p.1 = q.1 ∧ T.Adj p.2 q.2) → P.Adj p q) (x : X) :
    T.chromaticNumber ≤ P.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom
    ⟨fun y ↦ (x, y), fun {a b} h ↦ hadj (x, a) (x, b) ⟨rfl, h⟩⟩

/-! ### The lexicographic product -/

omit [Fintype X] [Fintype Y] in
/-- Colouring `G[H]` by the pair of coordinate colours. -/
theorem colorable_of_lex_adj {S : SimpleGraph X} {T : SimpleGraph Y}
    {P : SimpleGraph (X × Y)} {a b : ℕ}
    (hadj : ∀ p q : X × Y, P.Adj p q → S.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ T.Adj p.2 q.2))
    (hS : S.Colorable a) (hT : T.Colorable b) : P.Colorable (a * b) := by
  obtain ⟨cS⟩ := hS
  obtain ⟨cT⟩ := hT
  have C : P.Coloring (Fin a × Fin b) :=
    SimpleGraph.Coloring.mk (fun p ↦ (cS p.1, cT p.2)) fun {v w} h he ↦ by
      rcases hadj v w h with h' | ⟨h1, h2⟩
      · exact cS.valid h' (congrArg Prod.fst he)
      · exact cT.valid h2 (congrArg Prod.snd he)
  simpa using C.colorable

end

section
variable {G H : CGraph}

/-! ### Counting automorphisms -/

/-- Every permutation is an automorphism of the edgeless graph. -/
def _root_.SimpleGraph.autBotEquiv (α : Type*) :
    ((⊥ : SimpleGraph α) ≃g (⊥ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Every permutation is an automorphism of the complete graph. -/
def _root_.SimpleGraph.autTopEquiv (α : Type*) :
    ((⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph α)) ≃ Equiv.Perm α where
  toFun a := a.toEquiv
  invFun e := ⟨e, by simp [e.injective.ne_iff]⟩
  left_inv a := by ext v; rfl
  right_inv e := by ext v; rfl

/-- Complementation does not change the automorphism group. -/
def _root_.SimpleGraph.autComplEquiv {α : Type*} (S : SimpleGraph α) : (S ≃g S) ≃ (Sᶜ ≃g Sᶜ) where
  toFun a := ⟨a.toEquiv, by
    intro x y
    simp only [SimpleGraph.compl_adj, ne_eq, a.toEquiv.injective.ne_iff]
    exact and_congr_right fun _ ↦ not_congr a.map_rel_iff⟩
  invFun b := ⟨b.toEquiv, by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · have hne : ¬ (b x = b y) := fun hh ↦ hxy (b.toEquiv.injective hh)
      have h := b.map_rel_iff (a := x) (b := y)
      rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h
      constructor
      · intro hadj
        by_contra hc
        exact (h.2 ⟨hxy, hc⟩).2 hadj
      · intro hadj
        by_contra hc
        exact (h.1 ⟨hne, hc⟩).2 hadj⟩
  left_inv a := by ext v; rfl
  right_inv b := by ext v; rfl

/-! ### Automorphisms of the constructions

An automorphism of each factor gives an automorphism of a disjoint union, a join, or any of the
four products, and different pairs give different automorphisms.  So the automorphism count of a
construction is at least the product of the counts of its factors. -/

/-- The counting step shared by all the constructions below: an injective way of building an
automorphism of `K` out of one automorphism of `G` and one of `H`. -/
theorem mul_autCount_le_autCount {K : CGraph}
    (f : (G ≃cg G) → (H ≃cg H) → (K ≃cg K))
    (hf : ∀ a a' b b', f a b = f a' b' → a = a' ∧ b = b') :
    G.autCount * H.autCount ≤ K.autCount := by
  haveI : Finite (K ≃cg K) := K.instFiniteAut
  have hinj : Function.Injective fun p : (G ≃cg G) × (H ≃cg H) ↦ f p.1 p.2 := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h1, h2⟩ := hf a a' b b' h
    rw [h1, h2]
  calc G.autCount * H.autCount = Nat.card ((G ≃cg G) × (H ≃cg H)) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (K ≃cg K) := Nat.card_le_card_of_injective _ hinj
    _ = K.autCount := rfl

/-- An automorphism of each side, acting on the disjoint union. -/
def disjUnionAuto (a : G ≃cg G) (b : H ≃cg H) : G ⊕g H ≃cg G ⊕g H :=
  autoOfPerm (G := G ⊕g H) (Equiv.sumCongr a.toEquiv b.toEquiv) (by
    rintro (x | x) (y | y)
    · exact a.adj_eq x y
    · rfl
    · rfl
    · exact b.adj_eq x y)

/-- Swapping the two copies of a graph in a disjoint union with itself. -/
def disjUnionSwapAuto (G : CGraph) : G ⊕g G ≃cg G ⊕g G :=
  autoOfPerm (G := G ⊕g G) (Equiv.sumComm G.V G.V) (by
    rintro (x | x) (y | y) <;> rfl)

/-- An automorphism of each factor, acting coordinatewise on the Cartesian product. -/
def cartesianProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    G □g H ≃cg G □g H :=
  autoOfPerm (G := G □g H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (G □g H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [cartesianProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff]

/-- An automorphism of each factor, acting coordinatewise on the tensor product. -/
def tensorProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    G ⊗g H ≃cg G ⊗g H :=
  autoOfPerm (G := G ⊗g H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (G ⊗g H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [tensorProduct_adj, a.adj_eq, b.adj_eq]

/-- An automorphism of each factor, acting coordinatewise on the strong product. -/
def strongProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    G ⊠g H ≃cg G ⊠g H :=
  autoOfPerm (G := G ⊠g H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (G ⊠g H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [strongProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff,
      (RelIso.injective b).eq_iff, ne_eq, Prod.ext_iff]

/-- An automorphism of each factor, acting coordinatewise on the lexicographic product. -/
def lexProductAuto (a : G ≃cg G) (b : H ≃cg H) :
    G ·g H ≃cg G ·g H :=
  autoOfPerm (G := G ·g H) (Equiv.prodCongr a.toEquiv b.toEquiv) fun x y ↦ by
    show (G ·g H).Adj (a x.1, b x.2) (a y.1, b y.2) = _
    simp only [lexProduct_adj, a.adj_eq, b.adj_eq, (RelIso.injective a).eq_iff]

/-! ### A three-edge-colouring of the ladder

The ladder `P_N □ K₂` is cubic in the middle, so three colours are the least it can hope for, and
three suffice: give every rung the third colour and alternate the other two along both rails.  A
rail edge is determined by the smaller of its two endpoints' indices, and that index's parity is
the colour. -/

/-- Three colours for the ladder: the rungs take colour `2`, and a rail edge takes the parity of
the lower of the two rungs it joins. -/
def ladderCol (N : ℕ) (p q : Fin N × Fin 2) : Fin 3 :=
  if p.1 = q.1 then 2 else if min p.1.1 q.1.1 % 2 = 0 then 0 else 1

theorem ladderCol_symm (N : ℕ) (p q : Fin N × Fin 2) : ladderCol N p q = ladderCol N q p := by
  unfold ladderCol
  rw [Nat.min_comm]
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-! ### An `n`-edge-colouring of the crown

The crown `S_{n+2}^0 = K_{n+2} ⊗ K₂` is the complete bipartite graph `K_{n+2,n+2}` with a perfect
matching deleted, so it is `(n+1)`-regular and needs at least `n+1` colours.  It is also a Cayley
graph of `ℤ/(n+2)`, and the standard colouring of `K_{m,m}` by the difference of the two indices
restricts to it: the deleted matching is exactly the pairs of difference `0`, so the differences
that occur are the `n+1` nonzero ones. -/

/-- The cyclic distance from `c` up to `a`, as a natural number in `[0, N)`. -/
def crownIdx (N : ℕ) (a c : Fin N) : ℕ := if c.1 ≤ a.1 then a.1 - c.1 else a.1 + N - c.1

theorem crownIdx_lt (N : ℕ) (a c : Fin N) : crownIdx N a c < N := by
  have ha := a.isLt
  have hc := c.isLt
  unfold crownIdx
  split_ifs <;> omega

theorem crownIdx_pos (N : ℕ) {a c : Fin N} (h : a ≠ c) : 0 < crownIdx N a c := by
  have ha := a.isLt
  have hc := c.isLt
  have h' : (a : ℕ) ≠ (c : ℕ) := fun hh ↦ h (Fin.ext hh)
  unfold crownIdx
  split_ifs <;> omega

theorem crownIdx_inj (N : ℕ) (a c c' : Fin N) (h : crownIdx N a c = crownIdx N a c') : c = c' := by
  have ha := a.isLt
  have hc := c.isLt
  have hc' := c'.isLt
  refine Fin.ext ?_
  unfold crownIdx at h
  split_ifs at h <;> omega

theorem crownIdx_inj_left (N : ℕ) (a a' c : Fin N) (h : crownIdx N a c = crownIdx N a' c) :
    a = a' := by
  have ha := a.isLt
  have ha' := a'.isLt
  have hc := c.isLt
  refine Fin.ext ?_
  unfold crownIdx at h
  split_ifs at h <;> omega

/-- `n + 1` colours for the crown: the edge from `(a, 0)` to `(c, 1)` takes the cyclic difference
`a - c`, which is never zero because the difference-zero pairs are the deleted matching. -/
def crownCol (n : ℕ) (p q : Fin (n + 2) × Fin 2) : Fin (n + 1) :=
  if p.2 = q.2 then 0
  else if (p.2 : ℕ) = 0 then ⟨crownIdx (n + 2) p.1 q.1 - 1, by
      have := crownIdx_lt (n + 2) p.1 q.1; omega⟩
  else ⟨crownIdx (n + 2) q.1 p.1 - 1, by have := crownIdx_lt (n + 2) q.1 p.1; omega⟩

theorem crownCol_symm (n : ℕ) (p q : Fin (n + 2) × Fin 2) : crownCol n p q = crownCol n q p := by
  unfold crownCol
  by_cases h : p.2 = q.2
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hp := p.2.isLt
    have hq := q.2.isLt
    have h' : (p.2 : ℕ) ≠ (q.2 : ℕ) := fun hh ↦ h (Fin.ext hh)
    by_cases h0 : (p.2 : ℕ) = 0
    · rw [if_pos h0, if_neg (by omega)]
    · rw [if_neg h0, if_pos (by omega)]

/-! ### A three-edge-colouring of the prism

`Cₙ □ K₂` is cubic, so three colours is the best possible, and the graph is Hamiltonian: run along
the top rim, drop down the last rung, come back along the bottom rim and close up through the first
rung.  Alternating two colours along that cycle leaves the remaining rungs as a perfect matching for
the third colour.  The formula below does exactly that, in a shape `omega` can reason about. -/

/-- Three colours for the prism `Cₙ □ K₂`, read off a Hamiltonian cycle: go around the top rim,
drop down, come back along the bottom rim and close up.  Alternating two colours along that cycle
leaves the remaining perfect matching for the third. -/
def prismCol (N : ℕ) (p q : Fin N × Fin 2) : Fin 3 :=
  if p.1.1 = q.1.1 then
    (if p.1.1 = 0 then 1 else if p.1.1 + 1 = N then (if N % 2 = 0 then 1 else 0) else 2)
  else if (p.1.1 = 0 ∧ q.1.1 + 1 = N) ∨ (q.1.1 = 0 ∧ p.1.1 + 1 = N) then 2
  else if min p.1.1 q.1.1 % 2 = 0 then 0 else 1

theorem prismCol_symm (N : ℕ) (p q : Fin N × Fin 2) : prismCol N p q = prismCol N q p := by
  unfold prismCol
  rw [Nat.min_comm p.1.1 q.1.1]
  by_cases h : p.1.1 = q.1.1
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : (p.1.1 = 0 ∧ q.1.1 + 1 = N) ∨ (q.1.1 = 0 ∧ p.1.1 + 1 = N)
    · have h2' : (q.1.1 = 0 ∧ p.1.1 + 1 = N) ∨ (p.1.1 = 0 ∧ q.1.1 + 1 = N) := h2.symm
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬((q.1.1 = 0 ∧ p.1.1 + 1 = N) ∨ (p.1.1 = 0 ∧ q.1.1 + 1 = N)) :=
        fun hh ↦ h2 hh.symm
      rw [if_neg h2, if_neg h2']

/-! ### The double star and the Grötzsch graph

Two more class-one graphs, by two more explicit colourings.  The double star is a tree, so nothing
but the pendant edges at each hub can clash; the Grötzsch graph is small enough to hand the
properness check to the kernel. -/

/-- The colour of the edge between vertices `a` and `b` of `doubleStar m n`, as a natural: the
central edge gets `0`, the `i`-th pendant of the left hub gets `i + 1`, and the `j`-th pendant of
the right hub gets `j + 1`.  Off the edge set the value is junk. -/
def doubleStarIdx (m a b : ℕ) : ℕ :=
  if a = 0 then b - 1
  else if b = 0 then a - 1
  else if a = 1 then b - 1 - m
  else if b = 1 then a - 1 - m
  else 0

theorem doubleStarIdx_symm (m a b : ℕ) : doubleStarIdx m a b = doubleStarIdx m b a := by
  unfold doubleStarIdx
  split_ifs <;> omega

/-- A proper five-edge-colouring of the Grötzsch graph, as a symmetric table indexed by
`0–4` (the pentagon), `5–9` (their Mycielski copies) and `10` (the apex).  Off the edge set the
entries are junk zeroes. -/
def grotzschColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 1, 0, 2, 0, 0, 3, 0],
   [0, 0, 1, 0, 0, 2, 0, 3, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 3, 0, 2, 0, 0],
   [0, 0, 0, 0, 2, 0, 0, 4, 0, 1, 0],
   [1, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0],
   [2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 3, 0, 4, 0, 0, 0, 0, 0, 0, 2],
   [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3],
   [3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4],
   [0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 0]]

/-! ## The cocktail party graph is class one

`K_{(n+2)×2}` is `K_{2n+4}` minus a perfect matching.  Label the vertices of `K_{2n+4}` by
`ZMod (2n+3) ∪ {∞}` and colour the edge `{a, b}` by `a + b` and the edge `{a, ∞}` by `2a`; that
is the round-robin `1`-factorisation, whose colour class `0` is the matching
`{∞, 0}, {1, -1}, …, {n+1, -(n+1)}`.  Choosing the parts of the cocktail party graph to be exactly
that matching deletes colour `0`, leaving `2n+2` colours. -/

/-- The label of the cocktail party vertex `(i, j)` as a natural number below `2 * n + 3`.  The
vertex `(0, 0)` is the point at infinity and its label is not used. -/
def cpCode (n i j : ℕ) : ℕ := if i = 0 then 0 else if j = 0 then i else 2 * n + 3 - i

theorem cpCode_lt (n i j : ℕ) (hi : i < n + 2) : cpCode n i j < 2 * n + 3 := by
  unfold cpCode; split_ifs <;> omega

theorem cpCode_eq_zero_iff (n i j : ℕ) (hi : i < n + 2) : cpCode n i j = 0 ↔ i = 0 := by
  unfold cpCode; constructor <;> intro h <;> split_ifs at * <;> omega

theorem cpCode_inj (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2) (hj' : j' < 2)
    (h0 : ¬(i = 0 ∧ j = 0)) (h0' : ¬(i' = 0 ∧ j' = 0)) (h : cpCode n i j = cpCode n i' j') :
    i = i' ∧ j = j' := by
  unfold cpCode at h; split_ifs at h <;> omega

/-- The label of `(i, j)` in `ZMod (2 * n + 3)`. -/
def cpVal (n i j : ℕ) : ZMod (2 * n + 3) := ((cpCode n i j : ℕ) : ZMod (2 * n + 3))

/-- The colour of the ordered pair `(i, j), (i', j')` in `ZMod (2 * n + 3)`. -/
def cpRaw (n i j i' j' : ℕ) : ZMod (2 * n + 3) :=
  if i = 0 ∧ j = 0 then 2 * cpVal n i' j'
  else if i' = 0 ∧ j' = 0 then 2 * cpVal n i j
  else cpVal n i j + cpVal n i' j'

instance cpNeZero (n : ℕ) : NeZero (2 * n + 3) := ⟨by omega⟩

theorem cp_natCast_inj (n a b : ℕ) (ha : a < 2 * n + 3) (hb : b < 2 * n + 3)
    (h : (a : ZMod (2 * n + 3)) = (b : ZMod (2 * n + 3))) : a = b := by
  have h2 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at h2

/-- Two is invertible modulo the odd number `2 * n + 3`. -/
theorem cp_two_mul_inj (n : ℕ) {a b : ZMod (2 * n + 3)} (h : 2 * a = 2 * b) : a = b := by
  have hz : ((2 * n + 3 : ℕ) : ZMod (2 * n + 3)) = 0 := ZMod.natCast_self _
  push_cast at hz
  have key : ((n : ZMod (2 * n + 3)) + 2) * 2 = 1 := by linear_combination hz
  calc a = ((n : ZMod (2 * n + 3)) + 2) * 2 * a := by rw [key, one_mul]
    _ = ((n : ZMod (2 * n + 3)) + 2) * (2 * a) := by ring
    _ = ((n : ZMod (2 * n + 3)) + 2) * (2 * b) := by rw [h]
    _ = ((n : ZMod (2 * n + 3)) + 2) * 2 * b := by ring
    _ = b := by rw [key, one_mul]

theorem cpVal_inj (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2) (hj' : j' < 2)
    (h0 : ¬(i = 0 ∧ j = 0)) (h0' : ¬(i' = 0 ∧ j' = 0)) (h : cpVal n i j = cpVal n i' j') :
    i = i' ∧ j = j' :=
  cpCode_inj n i j i' j' hi hi' hj hj' h0 h0'
    (cp_natCast_inj n _ _ (cpCode_lt n i j hi) (cpCode_lt n i' j' hi') h)

theorem cpVal_eq_zero_iff (n i j : ℕ) (hi : i < n + 2) : cpVal n i j = 0 ↔ i = 0 := by
  rw [← cpCode_eq_zero_iff n i j hi]
  constructor
  · intro h
    have h2 : ((cpCode n i j : ℕ) : ZMod (2 * n + 3)) = ((0 : ℕ) : ZMod (2 * n + 3)) := by
      simpa [cpVal] using h
    exact cp_natCast_inj n _ _ (cpCode_lt n i j hi) (by omega) h2
  · intro h; unfold cpVal; rw [h]; simp

theorem cpRaw_comm (n i j i' j' : ℕ) : cpRaw n i j i' j' = cpRaw n i' j' i j := by
  unfold cpRaw
  by_cases h : i = 0 ∧ j = 0 <;> by_cases h' : i' = 0 ∧ j' = 0
  · rw [if_pos h, if_pos h']
    rw [show cpVal n i' j' = 0 from by unfold cpVal cpCode; rw [if_pos h'.1]; simp,
      show cpVal n i j = 0 from by unfold cpVal cpCode; rw [if_pos h.1]; simp]
  · rw [if_pos h, if_neg h', if_pos h]
  · rw [if_neg h, if_pos h', if_pos h']
  · rw [if_neg h, if_neg h', if_neg h', if_neg h]
    exact add_comm _ _

/-- The colour of an edge is never `0`: colour `0` is exactly the deleted perfect matching. -/
theorem cpRaw_ne_zero (n i j i' j' : ℕ) (hi : i < n + 2) (hi' : i' < n + 2) (hj : j < 2)
    (hj' : j' < 2) (hne : i ≠ i') : cpRaw n i j i' j' ≠ 0 := by
  unfold cpRaw
  split_ifs with h h'
  · intro hc
    have h2 : cpVal n i' j' = 0 := cp_two_mul_inj n (by rw [hc]; ring)
    rw [cpVal_eq_zero_iff n i' j' hi'] at h2
    omega
  · intro hc
    have h2 : cpVal n i j = 0 := cp_two_mul_inj n (by rw [hc]; ring)
    rw [cpVal_eq_zero_iff n i j hi] at h2
    omega
  · intro hc
    unfold cpVal at hc
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hb := cpCode_lt n i j hi
    have hb' := cpCode_lt n i' j' hi'
    have hk2 : k < 2 := by nlinarith
    interval_cases k
    · unfold cpCode at hk; split_ifs at hk <;> omega
    · unfold cpCode at hk; split_ifs at hk <;> omega

/-! ## Explicit edge colourings for the odd-order regular graphs

Each of these graphs is `k`-regular on an odd number of vertices, hence class two, so its
chromatic index is `k + 1` by Vizing; the tables below are the witnessing colourings, checked by
`native_decide` on the pairs (symmetry) and on the triples (properness). -/

def tri6Masks : List ℕ :=
  [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48]

def tri6ColTable : List (List ℕ) :=
  [[0, 0, 3, 4, 6, 0, 8, 1, 0, 0, 5, 2, 0, 0, 0], [0, 0, 7, 6, 0, 1, 3, 0, 8, 0, 4, 0, 2, 0, 0],
   [3, 7, 0, 0, 1, 4, 0, 8, 2, 0, 0, 6, 0, 0, 0], [4, 6, 0, 0, 3, 2, 7, 0, 0, 8, 1, 0, 0, 5, 0],
   [6, 0, 1, 3, 0, 8, 0, 5, 0, 4, 0, 0, 0, 7, 0], [0, 1, 4, 2, 8, 0, 0, 0, 5, 7, 0, 0, 3, 0, 0],
   [8, 3, 0, 7, 0, 0, 0, 4, 0, 1, 6, 0, 0, 0, 5], [1, 0, 8, 0, 5, 0, 4, 0, 7, 0, 0, 3, 0, 0, 6],
   [0, 8, 2, 0, 0, 5, 0, 7, 0, 6, 0, 0, 1, 0, 3], [0, 0, 0, 8, 4, 7, 1, 0, 6, 0, 0, 0, 0, 3, 2],
   [5, 4, 0, 1, 0, 0, 6, 0, 0, 0, 0, 8, 7, 2, 0], [2, 0, 6, 0, 0, 0, 0, 3, 0, 0, 8, 0, 5, 4, 7],
   [0, 2, 0, 0, 0, 3, 0, 0, 1, 0, 7, 5, 0, 6, 4], [0, 0, 0, 5, 7, 0, 0, 0, 0, 3, 2, 4, 6, 0, 8],
   [0, 0, 0, 0, 0, 0, 5, 6, 3, 2, 0, 7, 4, 8, 0]]

def tri7Masks : List ℕ :=
  [3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96]

def tri7ColTable : List (List ℕ) :=
  [[0, 10, 3, 0, 2, 0, 8, 7, 0, 0, 9, 6, 0, 0, 0, 1, 5, 0, 0, 0, 0], [10, 0, 5, 9, 0, 8, 2, 0, 4,
   0, 0, 0, 1, 0, 0, 3, 0, 7, 0, 0, 0], [3, 5, 0, 0, 8, 9, 0, 6, 0, 0, 0, 1, 7, 0, 0, 0, 4, 2, 0,
   0, 0], [0, 9, 0, 0, 3, 4, 1, 0, 0, 8, 10, 0, 0, 5, 0, 7, 0, 0, 2, 0, 0], [2, 0, 8, 3, 0, 10, 0,
   1, 0, 5, 0, 7, 0, 9, 0, 0, 6, 0, 0, 0, 0], [0, 8, 9, 4, 10, 0, 0, 0, 1, 0, 0, 0, 3, 6, 0, 0, 0,
   5, 7, 0, 0], [8, 2, 0, 1, 0, 0, 0, 0, 9, 7, 5, 0, 0, 0, 3, 6, 0, 0, 0, 4, 0], [7, 0, 6, 0, 1, 0,
   0, 0, 3, 9, 0, 10, 0, 0, 4, 0, 2, 0, 0, 8, 0], [0, 4, 0, 0, 0, 1, 9, 3, 0, 2, 0, 0, 10, 0, 7, 0,
   0, 8, 0, 6, 0], [0, 0, 0, 8, 5, 0, 7, 9, 2, 0, 0, 0, 0, 4, 10, 0, 0, 0, 6, 1, 0], [9, 0, 0, 10,
   0, 0, 5, 0, 0, 0, 0, 4, 6, 7, 8, 2, 0, 0, 0, 0, 3], [6, 0, 1, 0, 7, 0, 0, 10, 0, 0, 4, 0, 2, 8,
   5, 0, 3, 0, 0, 0, 0], [0, 1, 7, 0, 0, 3, 0, 0, 10, 0, 6, 2, 0, 0, 9, 0, 0, 4, 0, 0, 5], [0, 0,
   0, 5, 9, 6, 0, 0, 0, 4, 7, 8, 0, 0, 1, 0, 0, 0, 3, 0, 2], [0, 0, 0, 0, 0, 0, 3, 4, 7, 10, 8, 5,
   9, 1, 0, 0, 0, 0, 0, 2, 6], [1, 3, 0, 7, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8, 0, 9, 10, 4],
   [5, 0, 4, 0, 6, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 8, 0, 9, 1, 0, 10], [0, 7, 2, 0, 0, 5, 0, 0, 8, 0,
   0, 0, 4, 0, 0, 0, 9, 0, 10, 3, 1], [0, 0, 0, 2, 0, 7, 0, 0, 0, 6, 0, 0, 0, 3, 0, 9, 1, 10, 0, 5,
   8], [0, 0, 0, 0, 0, 0, 4, 8, 6, 1, 0, 0, 0, 0, 2, 10, 0, 3, 5, 0, 9], [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 3, 0, 5, 2, 6, 4, 10, 1, 8, 9, 0]]

def triples7Masks : List ℕ :=
  [7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56, 67, 69, 70, 73,
   74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 112]

def kneser73ColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
   0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 0, 0, 0, 3, 0, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 4, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0,
   0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1,
   0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
   0, 0, 3, 0, 0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 4,
   0, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0,
   0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2,
   4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 3, 0,
   4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0,
   0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0], [2, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0], [0, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def johnson73ColTable : List (List ℕ) :=
  [[0, 0, 12, 6, 7, 2, 10, 0, 0, 0, 5, 3, 11, 0, 0, 0, 0, 0, 0, 0, 4, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0], [0, 0, 8, 3, 1, 0, 0, 5, 7, 0, 10, 0, 0, 12, 4, 0, 0, 0, 0, 0, 6, 0, 0, 11, 2, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0], [12, 8, 0, 2, 0, 3, 0, 0, 0, 7, 0, 10, 0, 4, 0, 1, 0, 0, 0, 0, 0,
   11, 0, 6, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0], [6, 3, 2, 0, 0, 0, 12, 0, 10, 4, 0, 0, 1, 0, 5, 8,
   0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0], [7, 1, 0, 0, 0, 5, 2, 11, 12, 0, 4,
   0, 0, 0, 0, 0, 9, 6, 0, 0, 3, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0], [2, 0, 3, 0, 5, 0, 1,
   4, 0, 8, 0, 6, 0, 0, 0, 0, 7, 0, 0, 0, 0, 10, 0, 0, 0, 0, 11, 0, 9, 0, 0, 0, 0, 0, 0], [10, 0,
   0, 12, 2, 1, 0, 0, 6, 9, 0, 0, 5, 0, 0, 0, 0, 4, 11, 0, 0, 0, 3, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0,
   0, 0], [0, 5, 0, 0, 11, 4, 0, 0, 8, 10, 0, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 0, 12, 0, 0, 9, 0,
   0, 2, 0, 0, 0, 0, 0], [0, 7, 0, 10, 12, 0, 6, 8, 0, 0, 0, 0, 0, 0, 9, 0, 0, 2, 0, 5, 0, 0, 0, 0,
   3, 0, 0, 1, 0, 11, 0, 0, 0, 0, 0], [0, 0, 7, 4, 0, 8, 9, 10, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 3,
   11, 0, 0, 0, 0, 0, 1, 0, 0, 2, 6, 0, 0, 0, 0, 0], [5, 10, 0, 0, 4, 0, 0, 0, 0, 0, 0, 12, 3, 1,
   2, 0, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 6, 0, 0, 0], [3, 0, 10, 0, 0, 6, 0, 0, 0, 0,
   12, 0, 8, 9, 0, 11, 5, 0, 7, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0], [11, 0, 0, 1, 0,
   0, 5, 0, 0, 0, 3, 8, 0, 0, 6, 2, 0, 0, 9, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 4, 7, 0, 0], [0,
   12, 4, 0, 0, 0, 0, 3, 0, 0, 1, 9, 0, 0, 10, 7, 11, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 5, 0,
   0, 0, 0], [0, 4, 0, 5, 0, 0, 0, 0, 9, 0, 2, 0, 6, 10, 0, 0, 0, 12, 0, 8, 0, 0, 0, 0, 7, 0, 0, 0,
   0, 0, 0, 3, 0, 11, 0], [0, 0, 1, 8, 0, 0, 0, 0, 0, 5, 0, 11, 2, 7, 0, 0, 0, 0, 6, 4, 0, 0, 0, 0,
   0, 9, 0, 0, 0, 0, 0, 0, 3, 12, 0], [0, 0, 0, 0, 9, 7, 0, 6, 0, 0, 8, 5, 0, 11, 0, 0, 0, 3, 4, 0,
   0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 1], [0, 0, 0, 0, 6, 0, 4, 0, 2, 0, 9, 0, 0, 0, 12, 0,
   3, 0, 8, 10, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 5, 0, 0, 11], [0, 0, 0, 0, 0, 0, 11, 0, 0, 3, 0,
   7, 9, 0, 0, 6, 4, 8, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 12, 0, 5], [0, 0, 0, 0, 0, 0, 0,
   1, 5, 11, 0, 0, 0, 6, 8, 4, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 3, 12], [4, 6,
   0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 8, 5, 1, 0, 10, 12, 0, 0, 11, 2, 0,
   0, 0], [8, 0, 11, 0, 0, 10, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 12, 0, 0, 3, 5, 0,
   7, 0, 6, 0, 4, 0, 0], [9, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 8, 12, 0, 0,
   6, 2, 0, 4, 5, 0, 0, 7, 11, 0, 0], [0, 11, 6, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
   0, 5, 0, 0, 0, 4, 7, 1, 0, 0, 10, 8, 0, 0, 9, 0], [0, 2, 0, 9, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 7,
   0, 0, 0, 0, 0, 1, 0, 6, 4, 0, 10, 0, 5, 0, 0, 0, 11, 0, 8, 0], [0, 0, 5, 11, 0, 0, 0, 0, 0, 1,
   0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 3, 2, 7, 10, 0, 0, 0, 8, 12, 0, 0, 6, 4, 0], [0, 0, 0, 0, 0,
   11, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 5, 0, 1, 0, 0, 0, 6, 12, 7, 3, 0, 0, 0, 4],
   [0, 0, 0, 0, 10, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 12, 0, 4, 0, 5, 0, 6, 0, 11, 3, 0,
   9, 0, 0, 2], [0, 0, 0, 0, 0, 9, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 7, 5, 0, 0, 8, 12,
   11, 0, 4, 0, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0, 0, 2, 11, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0,
   10, 0, 12, 7, 3, 4, 0, 0, 0, 0, 1, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 4, 0, 5, 0, 0, 10, 0,
   0, 0, 11, 6, 0, 8, 0, 0, 3, 0, 0, 0, 0, 12, 0, 2, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 4, 0,
   3, 0, 0, 5, 0, 0, 2, 0, 7, 0, 11, 0, 0, 9, 0, 0, 12, 0, 8, 10, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 2, 7, 0, 0, 3, 0, 0, 12, 0, 0, 4, 11, 0, 0, 6, 0, 0, 1, 0, 0, 8, 0, 5, 10], [0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 12, 0, 0, 0, 3, 0, 0, 0, 9, 8, 4, 0, 0, 0, 1, 2, 10, 5, 0, 7],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 11, 5, 12, 0, 0, 0, 0, 0, 0, 4, 2, 3, 8, 9,
   0, 10, 7, 0]]

def rook33ColTable : List (List ℕ) :=
  [[0, 1, 3, 0, 0, 0, 2, 0, 0], [1, 0, 4, 0, 3, 0, 0, 0, 0], [3, 4, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
   0, 2, 3, 4, 0, 0], [0, 3, 0, 2, 0, 4, 0, 1, 0], [0, 0, 0, 3, 4, 0, 0, 0, 2], [2, 0, 0, 4, 0, 0,
   0, 3, 0], [0, 0, 0, 0, 1, 0, 3, 0, 4], [0, 0, 1, 0, 0, 2, 0, 4, 0]]

def paley13ColTable : List (List ℕ) :=
  [[0, 2, 0, 3, 6, 0, 0, 0, 0, 1, 0, 0, 5], [2, 0, 4, 0, 0, 5, 0, 0, 0, 0, 1, 6, 0], [0, 4, 0, 5,
   0, 2, 3, 0, 0, 0, 0, 0, 1], [3, 0, 5, 0, 4, 0, 1, 6, 0, 0, 0, 0, 0], [6, 0, 0, 4, 0, 1, 0, 3, 2,
   0, 0, 0, 0], [0, 5, 2, 0, 1, 0, 6, 0, 0, 4, 0, 0, 0], [0, 0, 3, 1, 0, 6, 0, 5, 0, 0, 4, 0, 0],
   [0, 0, 0, 6, 3, 0, 5, 0, 4, 0, 2, 1, 0], [0, 0, 0, 0, 2, 0, 0, 4, 0, 5, 0, 3, 6], [1, 0, 0, 0,
   0, 4, 0, 0, 5, 0, 6, 0, 2], [0, 1, 0, 0, 0, 0, 4, 2, 0, 6, 0, 5, 0], [0, 6, 0, 0, 0, 0, 0, 1, 3,
   0, 5, 0, 4], [5, 0, 1, 0, 0, 0, 0, 0, 6, 2, 0, 4, 0]]

def petPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 13), (0, 14), (1, 2), (1, 10), (1, 12), (2, 5), (2, 8), (3, 4), (3, 5),
   (3, 11), (3, 12), (4, 5), (4, 9), (4, 14), (5, 8), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8),
   (7, 11), (7, 13), (9, 10), (9, 14), (10, 12), (11, 12), (11, 13), (13, 14)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- No assignment of three colours to the fifteen edges of the Petersen graph avoids all thirty
conflicts: an exhaustive `3 ^ 15` case split. -/
theorem petSearch : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Fin 3,
    ¬ (c0 ≠ c1 ∧ c0 ≠ c2 ∧ c0 ≠ c13 ∧ c0 ≠ c14 ∧ c1 ≠ c2 ∧ c1 ≠ c10 ∧ c1 ≠ c12 ∧ c2 ≠ c5 ∧ c2 ≠ c8 ∧
      c3 ≠ c4 ∧ c3 ≠ c5 ∧ c3 ≠ c11 ∧ c3 ≠ c12 ∧ c4 ≠ c5 ∧ c4 ≠ c9 ∧ c4 ≠ c14 ∧ c5 ≠ c8 ∧ c6 ≠ c7 ∧
      c6 ≠ c8 ∧ c6 ≠ c9 ∧ c6 ≠ c10 ∧ c7 ≠ c8 ∧ c7 ≠ c11 ∧ c7 ≠ c13 ∧ c9 ≠ c10 ∧ c9 ≠ c14 ∧
      c10 ≠ c12 ∧ c11 ≠ c12 ∧ c11 ≠ c13 ∧ c13 ≠ c14) := by
  native_decide

/-! ### A four-edge-colouring of the Petersen graph -/

def pet10Masks : List ℕ := [3, 5, 6, 9, 10, 12, 17, 18, 20, 24]

def pet10ColTable : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 0, 0, 0, 1, 0, 3], [0, 0, 0, 0, 0, 0, 2, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 2, 3, 0], [0, 0, 0, 0, 0, 0, 3, 0, 2, 0], [0, 0, 0, 0, 0, 0, 1, 3, 0, 0],
   [0, 0, 2, 0, 3, 1, 0, 0, 0, 0], [0, 1, 0, 2, 0, 3, 0, 0, 0, 0], [1, 0, 0, 3, 2, 0, 0, 0, 0, 0],
   [2, 3, 1, 0, 0, 0, 0, 0, 0, 0]]

/-- Rewriting the index of a list lookup.  Mathlib's `getElem_congr_idx` is stated for a general
`GetElem` with the index implicit; this specialisation to lists, with the list explicit, is what
the cycle-list manipulations below can apply directly. -/
theorem getElem_congr_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i]'hi = l[j]'(h ▸ hi) := by subst h; rfl

/-! ### The cycle with pendant vertices -/

/-- A pendant vertex hangs off exactly one vertex of the cycle. -/
theorem pendantEdges_unique_owner : ∀ (v off : ℕ) (ks : List ℕ) (p p' q : ℕ),
    (p, q) ∈ pendantEdges v off ks → (p', q) ∈ pendantEdges v off ks → p = p'
  | _, _, [], _, _, _ => by simp [pendantEdges]
  | v, off, k :: ks, p, p', q => by
      intro h h'
      have hb : ∀ r s : ℕ, (r, s) ∈ (List.range k).map (fun i ↦ (v, off + i)) →
          r = v ∧ s < off + k := by
        intro r s hr
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hr
        obtain ⟨i, hi, h1, h2⟩ := hr
        omega
      rw [pendantEdges, List.mem_append] at h h'
      rcases h with h | h <;> rcases h' with h' | h'
      · exact ((hb p q h).1).trans ((hb p' q h').1).symm
      · have hq := (hb p q h).2
        have := (mem_pendantEdges_bound (v + 1) (off + k) ks p' q h').2.1
        omega
      · have hq := (hb p' q h').2
        have := (mem_pendantEdges_bound (v + 1) (off + k) ks p q h).2.1
        omega
      · exact pendantEdges_unique_owner (v + 1) (off + k) ks p p' q h h'

/-! ### The boustrophedon numbering of a board -/

/-- **Consecutive squares of the boustrophedon numbering are adjacent.**  Numbering an `m × n`
board row by row, left to right along the even rows and right to left along the odd ones, two
squares whose numbers differ by one share a row and are neighbouring columns, or share a column
and are neighbouring rows. -/
theorem snake_step {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + (if x % 2 = 0 then y else n - 1 - y) + 1
      = x' * n + (if x' % 2 = 0 then y' else n - 1 - y')) :
    (x = x' ∧ (y + 1 = y' ∨ y' + 1 = y)) ∨ (y = y' ∧ x + 1 = x') := by
  have hs : (if x % 2 = 0 then y else n - 1 - y) < n := by split; omega; omega
  have hs' : (if x' % 2 = 0 then y' else n - 1 - y') < n := by split; omega; omega
  rcases row_col_step hs hs' h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · subst h1
    exact Or.inl ⟨rfl, by split_ifs at h2 <;> omega⟩
  · exact Or.inr ⟨by split_ifs at h2 h3 <;> omega, h1⟩

/-- The boustrophedon numbering is injective. -/
theorem snake_inj {n x y x' y' : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + (if x % 2 = 0 then y else n - 1 - y)
      = x' * n + (if x' % 2 = 0 then y' else n - 1 - y')) : x = x' ∧ y = y' := by
  have hs : (if x % 2 = 0 then y else n - 1 - y) < n := by split; omega; omega
  have hs' : (if x' % 2 = 0 then y' else n - 1 - y') < n := by split; omega; omega
  obtain ⟨h1, h2⟩ := row_col_eq hs hs' h
  subst h1
  exact ⟨rfl, by split_ifs at h2 <;> omega⟩

/-! ### The independence number of a torus with two odd sides -/

/-- Two entries of one column of the staircase are never cyclically adjacent. -/
theorem staircase_same (a c i i' : ℕ) (hi : i ≤ a) (hi' : i' ≤ a) :
    (c + 2 * i + 1) % (2 * a + 3) ≠ (c + 2 * i') % (2 * a + 3) := by
  intro he
  have h1 : c + (2 * i + 1) ≡ c + 2 * i' [MOD 2 * a + 3] := by
    show (c + (2 * i + 1)) % (2 * a + 3) = (c + 2 * i') % (2 * a + 3)
    simpa [Nat.add_assoc] using he
  exact two_mul_succ_not_modEq a i i' hi hi' (Nat.ModEq.add_left_cancel' _ h1)

/-- Entries of two neighbouring columns never coincide. -/
theorem staircase_clash (a s t i i' : ℕ) (hi : i ≤ a) (hi' : i' ≤ a)
    (hst : (s + 1) % (2 * a + 3) = t % (2 * a + 3)) :
    (s + 2 * i) % (2 * a + 3) ≠ (t + 2 * i') % (2 * a + 3) := by
  intro he
  have h1 : s + 2 * i ≡ t + 2 * i' [MOD 2 * a + 3] := he
  have h2 : t + 2 * i' ≡ s + 1 + 2 * i' [MOD 2 * a + 3] :=
    Nat.ModEq.add_right _ (Nat.ModEq.symm hst)
  have h3 : s + 2 * i ≡ s + (1 + 2 * i') [MOD 2 * a + 3] := by
    simpa [Nat.add_assoc] using h1.trans h2
  have h4 : 2 * i ≡ 1 + 2 * i' [MOD 2 * a + 3] := Nat.ModEq.add_left_cancel' _ h3
  exact two_mul_succ_not_modEq a i' i hi' hi (by simpa [Nat.add_comm] using h4.symm)

end

end CGraph

namespace IsoGraph

/-! ## The join, and the constructions built from it

The `IsoGraph`-level `join`, defined as `(disjUnion Gᶜ Hᶜ)ᶜ` with no lift of its own, agrees
with `CGraph.join`; that is `join_mk`, in `IsoGraph/Core/Quotient.lean`. -/

theorem join_def (G H : IsoGraph) : G ∇g H = (Gᶜ ⊕g Hᶜ)ᶜ := rfl

end IsoGraph

namespace CGraph

@[toIsoGraph simp]
theorem compl_empty (n : ℕ) : (empty n)ᶜ = complete n := rfl

@[toIsoGraph simp]
theorem compl_complete (n : ℕ) : (complete n)ᶜ = empty n := by
  rw [← compl_empty, compl_compl]

@[toIsoGraph simp]
theorem compl_join (G H : CGraph) : (G ∇g H)ᶜ = Gᶜ ⊕g Hᶜ := by
  rw [join, compl_compl]

@[toIsoGraph simp]
theorem compl_disjUnion (G H : CGraph) : (G ⊕g H)ᶜ = Gᶜ ∇g Hᶜ := by
  rw [join, compl_compl, compl_compl]

@[toIsoGraph simp empty_zero_disjUnion]
def emptyZeroDisjUnion (G : CGraph) : empty 0 ⊕g G ≃cg G :=
  (Iso.disjUnionComm _ _).trans (Iso.disjUnionEmptyZero G)

@[toIsoGraph simp disjUnion_empty]
def disjUnionEmpty (m n : ℕ) : empty m ⊕g empty n ≃cg empty (m + n) :=
  isoOfAdj finSumFinEquiv fun x y ↦ by cases x <;> cases y <;> rfl

@[toIsoGraph simp]
theorem complete_zero : complete 0 = empty 0 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem complete_one : complete 1 = empty 1 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem path_zero : path 0 = empty 0 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem path_one : path 1 = empty 1 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem path_two : path 2 = complete 2 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem cycle_zero : cycle 0 = empty 0 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem cycle_one : cycle 1 = empty 1 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp]
theorem cycle_two : cycle 2 = complete 2 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph]
theorem cycle_three : cycle 3 = complete 3 := ext' rfl (heq_of_eq (by decide))

@[toIsoGraph simp compl_cycle_five]
def complCycleFive : (cycle 5)ᶜ ≃cg cycle 5 :=
  isoOfAdj (⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩ : Equiv.Perm (Fin 5))
    (by decide)

@[toIsoGraph simp compl_path_four]
def complPathFour : (path 4)ᶜ ≃cg path 4 :=
  isoOfAdj (⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩ : Equiv.Perm (Fin 4))
    (by decide)

@[toIsoGraph simp empty_zero_join]
def emptyZeroJoin (G : CGraph) : empty 0 ∇g G ≃cg G :=
  (Iso.joinComm _ _).trans (Iso.joinEmptyZero G)

theorem join_complete_eq_compl (m n : ℕ) :
    complete m ∇g complete n = (empty m ⊕g empty n)ᶜ := by
  rw [join, compl_complete, compl_complete]

@[toIsoGraph simp join_complete]
def joinComplete (m n : ℕ) : complete m ∇g complete n ≃cg complete (m + n) := by
  rw [join_complete_eq_compl]
  exact Iso.compl (disjUnionEmpty m n)

/-! ### Paley graphs

**Paley graphs are self-complementary**, because multiplication by a non-residue exchanges the
squares with the non-squares: that is `Iso.complPaleyOfNotIsSquare`, and all it needs is the
non-residue, here `2` mod `13` and `3` mod `17`.  Nine is not prime, and the degenerate `paley 9`
is handled separately. -/

theorem not_isSquare_two_zmod_thirteen : ¬ IsSquare (2 : ZMod 13) := by decide

theorem not_isSquare_three_zmod_seventeen : ¬ IsSquare (3 : ZMod 17) := by decide

end CGraph

namespace IsoGraph

/-- **The double cover of an odd cycle is one cycle of twice the length.**  The bound starts at
`C₃`: `cycle 1` is edgeless, so its double cover is too, while `cycle 2` is an edge. -/
theorem tensorProduct_complete_two_cycle_odd (m : ℕ) :
    complete 2 ⊗g cycle (2 * m + 3) = cycle (2 * (2 * m + 3)) := by
  rw [complete_def, cycle_def, tensorProduct_mk, cycle_def]
  exact Quotient.sound ⟨(CGraph.Iso.cycleTensorTwo m).symm⟩

theorem tensorProduct_complete_two_cycle_three :
    complete 2 ⊗g cycle 3 = cycle 6 :=
  tensorProduct_complete_two_cycle_odd 0

theorem tensorProduct_complete_two_cycle_five :
    complete 2 ⊗g cycle 5 = cycle 10 :=
  tensorProduct_complete_two_cycle_odd 1

/-- The same principle for predicates: any property of `IsoGraph`s that holds of `G` but fails
for `H` separates them. -/
theorem ne_of_pred {p : IsoGraph → Prop} {G H : IsoGraph} (hG : p G) (hH : ¬ p H) : G ≠ H :=
  fun he ↦ hH (he ▸ hG)

end IsoGraph

namespace CGraph

/-- **The Mycielskian of `K₂` is the 5-cycle**: two vertices, their two shadows and the apex,
strung together as `u₀ — u₁ — w₀ — z — w₁ — u₀`. -/
@[toIsoGraph mycielskian_complete_two]
def mycielskianCompleteTwo : mycielskian (complete 2) ≃cg cycle 5 :=
  isoOfAdj
    (⟨fun x ↦ match x with
        | none => 3
        | some (.inl a) => if a = 0 then 0 else 1
        | some (.inr a) => if a = 0 then 2 else 4,
      ![some (.inl 0), some (.inl 1), some (.inr 0), none, some (.inr 1)],
      by decide, by decide⟩ : Option (Fin 2 ⊕ Fin 2) ≃ Fin 5)
    (by decide)

end CGraph
