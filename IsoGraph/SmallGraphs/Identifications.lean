import IsoGraph.SmallGraphs.EdgeColourings

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# Named graphs recognised as other named graphs

Named graphs recognised as members of another family, up to isomorphism: which circulants are
Kneser graphs, which decorated cycles are theta graphs, which products are grids, and so on.
-/

namespace IsoGraph

@[simp] theorem V_bipartite (m n : ℕ) : (bipartite m n).V = m + n := CGraph.card_bipartite m n

@[simp] theorem V_star (n : ℕ) : (star n).V = 1 + n := CGraph.card_star n

@[simp] theorem V_kneser (n k : ℕ) : (kneser n k).V = n.choose k := CGraph.card_kneser n k

@[simp] theorem V_johnson (n k : ℕ) : (johnson n k).V = n.choose k := CGraph.card_johnson n k

@[simp] theorem V_hypercube (n : ℕ) : (hypercube n).V = 2 ^ n := CGraph.card_hypercube n

@[simp] theorem V_paley (q : ℕ) : (paley q).V = q := CGraph.card_paley q

@[simp] theorem V_circulant (n : ℕ) (S : List ℕ) : (circulant n S).V = n :=
  CGraph.card_circulant n S

@[simp] theorem V_foldedCube (n : ℕ) : (foldedCube n).V = 2 ^ n := CGraph.card_foldedCube n

@[simp] theorem V_wheel (n : ℕ) : (wheel n).V = 1 + n := by
  show FinEnum.card (CGraph.wheel n).V = _
  simp [CGraph.wheel]

@[simp] theorem V_thetaGraph (xs : List ℕ) : (thetaGraph xs).V = 2 + xs.sum :=
  CGraph.card_thetaGraph xs

@[simp] theorem V_tadpole (m k : ℕ) : (tadpole m k).V = m + k := CGraph.card_tadpole m k

@[simp] theorem V_lollipop (m k : ℕ) : (lollipop m k).V = m + k := CGraph.card_lollipop m k

@[simp] theorem V_spider (legs : List ℕ) : (spider legs).V = 1 + legs.sum :=
  CGraph.card_spider legs

@[simp] theorem V_doubleStar (m n : ℕ) : (doubleStar m n).V = 2 + m + n :=
  CGraph.card_doubleStar m n

@[simp] theorem V_cyclePendant (m : ℕ) (ks : List ℕ) : (cyclePendant m ks).V = m + ks.sum :=
  CGraph.card_cyclePendant m ks

end IsoGraph

/-! ## The identities themselves, at the level of `CGraph`

Everything from here to the products is proved downstairs and carried up by `@[toIsoGraph]`, which
is also where the `simp` attribute lands: where the two sides have the same vertex type the
identity is an equality of `CGraph`s, and where they do not it is an explicit — and computable —
isomorphism, whose lift is the equality of `IsoGraph`s. -/

namespace CGraph

attribute [toIsoGraph] bipartite_eq_compl

@[toIsoGraph]
theorem star_eq_bipartite (n : ℕ) : star n = bipartite 1 n := rfl

@[toIsoGraph]
theorem wheel_eq_join (n : ℕ) : wheel n = complete 1 ∇g cycle n := rfl

@[toIsoGraph simp]
theorem compl_bipartite (m n : ℕ) :
    (bipartite m n)ᶜ = complete m ⊕g complete n := by
  rw [bipartite_eq_compl, compl_compl]

attribute [toIsoGraph] bipartite_eq_join

@[toIsoGraph simp bipartite_zero_right]
def bipartiteZeroRight (m : ℕ) : bipartite m 0 ≃cg empty m := by
  rw [show bipartite m 0 = (complete m ⊕g empty 0)ᶜ from by
        rw [bipartite_eq_compl, complete_zero],
    show empty m = (complete m)ᶜ from (compl_complete m).symm]
  exact Iso.compl (Iso.disjUnionEmptyZero (complete m))

@[toIsoGraph simp bipartite_zero_left]
def bipartiteZeroLeft (n : ℕ) : bipartite 0 n ≃cg empty n := by
  rw [bipartite_eq_join]
  exact emptyZeroJoin (empty n)

@[toIsoGraph bipartite_one_one]
def bipartiteOneOne : bipartite 1 1 ≃cg complete 2 := by
  rw [bipartite_eq_join, ← complete_one]
  exact joinComplete 1 1

@[toIsoGraph simp star_zero]
def starZero : star 0 ≃cg empty 1 := by
  rw [star_eq_bipartite]
  exact bipartiteZeroRight 1

@[toIsoGraph star_one]
def starOne : star 1 ≃cg complete 2 := by
  rw [star_eq_bipartite]
  exact bipartiteOneOne

/-- The complement of a star is its centre, isolated, next to a clique on the leaves. -/
@[toIsoGraph]
theorem compl_star (n : ℕ) : (star n)ᶜ = empty 1 ⊕g complete n := by
  rw [star_eq_bipartite, compl_bipartite, complete_one]

/-- `K_{2,2}` is the square. -/
@[toIsoGraph bipartite_two_two]
def bipartiteTwoTwo : bipartite 2 2 ≃cg cycle 4 :=
  isoOfAdj (G := bipartite 2 2) (H := cycle 4)
    (⟨Sum.elim ![0, 2] ![1, 3], ![.inl 0, .inr 0, .inl 1, .inr 1], by decide, by decide⟩ :
      (Fin 2 ⊕ Fin 2) ≃ Fin 4)
    (by decide)

/-- The complement of the square is a perfect matching. -/
@[toIsoGraph simp compl_cycle_four]
def complCycleFour : (cycle 4)ᶜ ≃cg complete 2 ⊕g complete 2 := by
  rw [← compl_bipartite]
  exact (Iso.compl bipartiteTwoTwo).symm

@[toIsoGraph simp wheel_zero]
def wheelZero : wheel 0 ≃cg empty 1 := by
  rw [wheel_eq_join, cycle_zero, ← complete_one]
  exact Iso.joinEmptyZero (complete 1)

@[toIsoGraph wheel_one]
def wheelOne : wheel 1 ≃cg complete 2 := by
  rw [wheel_eq_join, cycle_one, ← complete_one]
  exact joinComplete 1 1

@[toIsoGraph wheel_two]
def wheelTwo : wheel 2 ≃cg complete 3 := by
  rw [wheel_eq_join, cycle_two]
  exact joinComplete 1 2

@[toIsoGraph wheel_three]
def wheelThree : wheel 3 ≃cg complete 4 := by
  rw [wheel_eq_join, cycle_three]
  exact joinComplete 1 3

/-- The hub of a wheel is joined to everything, so it is isolated in the complement. -/
@[toIsoGraph]
theorem compl_wheel (n : ℕ) : (wheel n)ᶜ = empty 1 ⊕g (cycle n)ᶜ := by
  rw [wheel_eq_join, compl_join, compl_complete]

/-! ### Complete multipartite graphs

A single part is an independent set, and `cocktailParty 1` is that case; two singleton parts and
one part of size `n` is the book `B_n`, whose first two members are complete.

The workhorse is `completeMultipartite_cons`: peeling the first part off turns the dependent
`Σ i : Fin ds.length, _` vertex type into a `Sum`, so the whole family becomes reachable by
`join`-level rewriting.  Everything after it — the append rule, `[a, b] = bipartite a b`,
`cocktailParty 2 = cycle 4`, the vertex count — is a consequence. -/

@[toIsoGraph simp completeMultipartite_nil]
noncomputable def completeMultipartiteNil : completeMultipartite [] ≃cg empty 0 :=
  isoEmptyOfCard (by decide) (by simp)

/-- One part: no edges at all. -/
@[toIsoGraph simp completeMultipartite_singleton]
noncomputable def completeMultipartiteSingleton (n : ℕ) :
    completeMultipartite [n] ≃cg empty n := by
  refine isoEmptyOfCard ?_ (by simp)
  have : Subsingleton (Fin [n].length) := inferInstanceAs (Subsingleton (Fin 1))
  rintro ⟨i, a⟩ ⟨j, b⟩
  obtain rfl : i = j := Subsingleton.elim i j
  rw [completeMultipartite_adj]
  simp

noncomputable def cocktailPartyOne : cocktailParty 1 ≃cg empty 2 :=
  completeMultipartiteSingleton 2

noncomputable def bookZero : book 0 ≃cg complete 2 :=
  isoCompleteOfCard (G := completeMultipartite [1, 1, 0]) (by decide) (by simp)

noncomputable def bookOne : book 1 ≃cg complete 3 :=
  isoCompleteOfCard (G := completeMultipartite [1, 1, 1]) (by decide) (by simp)

theorem join_empty_completeMultipartite (d : ℕ) (ds : List ℕ) :
    empty d ∇g completeMultipartite ds
      = (complete d ⊕g (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i)))ᶜ := by
  rw [join_eq_compl_disjUnion, compl_empty, completeMultipartite_eq_compl, compl_compl]

/-- Peeling off the first part: the rest of the multipartite graph, joined to an independent
set of the first part's size. -/
@[toIsoGraph completeMultipartite_cons]
def completeMultipartiteCons (d : ℕ) (ds : List ℕ) :
    completeMultipartite (d :: ds) ≃cg empty d ∇g completeMultipartite ds := by
  rw [join_empty_completeMultipartite, completeMultipartite_eq_compl (d :: ds)]
  exact Iso.compl (Iso.sigmaUnionSucc fun i : Fin (d :: ds).length ↦ complete ((d :: ds).get i))

@[toIsoGraph simp completeMultipartite_zero_cons]
def completeMultipartiteZeroCons (ds : List ℕ) :
    completeMultipartite (0 :: ds) ≃cg completeMultipartite ds :=
  (completeMultipartiteCons 0 ds).trans (emptyZeroJoin _)

@[toIsoGraph completeMultipartite_append]
noncomputable def completeMultipartiteAppend (ds es : List ℕ) :
    completeMultipartite (ds ++ es)
      ≃cg completeMultipartite ds ∇g completeMultipartite es := by
  induction ds with
  | nil =>
    exact ((Iso.join completeMultipartiteNil (RelIso.refl _)).trans
      (emptyZeroJoin (completeMultipartite es))).symm
  | cons d ds ih =>
    exact (completeMultipartiteCons d (ds ++ es)).trans
      (((Iso.join (RelIso.refl _) ih).trans (Iso.joinAssoc _ _ _).symm).trans
        (Iso.join (completeMultipartiteCons d ds).symm (RelIso.refl _)))

@[toIsoGraph compl_completeMultipartite_cons]
def complCompleteMultipartiteCons (d : ℕ) (ds : List ℕ) :
    (completeMultipartite (d :: ds))ᶜ ≃cg complete d ⊕g (completeMultipartite ds)ᶜ := by
  rw [show complete d ⊕g (completeMultipartite ds)ᶜ
      = (empty d ∇g completeMultipartite ds)ᶜ from by rw [compl_join, compl_empty]]
  exact Iso.compl (completeMultipartiteCons d ds)

@[toIsoGraph completeMultipartite_pair]
noncomputable def completeMultipartitePair (a b : ℕ) :
    completeMultipartite [a, b] ≃cg bipartite a b := by
  rw [bipartite_eq_join]
  exact (completeMultipartiteCons a [b]).trans
    (Iso.join (RelIso.refl _) (completeMultipartiteSingleton b))

@[toIsoGraph star_eq_completeMultipartite]
noncomputable def starEqCompleteMultipartite (n : ℕ) : star n ≃cg completeMultipartite [1, n] := by
  rw [star_eq_bipartite]
  exact (completeMultipartitePair 1 n).symm

@[toIsoGraph completeMultipartite_replicate_one]
noncomputable def completeMultipartiteReplicateOne (n : ℕ) :
    completeMultipartite (List.replicate n 1) ≃cg complete n := by
  induction n with
  | zero =>
    rw [complete_zero]
    exact completeMultipartiteNil
  | succ n ih =>
    rw [List.replicate_succ, show n + 1 = 1 + n from Nat.add_comm n 1]
    exact ((completeMultipartiteCons 1 (List.replicate n 1)).trans
      (Iso.join (RelIso.refl _) ih)).trans (by rw [← complete_one]; exact joinComplete 1 n)

noncomputable def cocktailPartyTwo : cocktailParty 2 ≃cg cycle 4 :=
  (completeMultipartitePair 2 2).trans bipartiteTwoTwo

noncomputable def bookEqJoin (n : ℕ) : book n ≃cg complete 2 ∇g empty n :=
  ((completeMultipartiteCons 1 [1, n]).trans
    (Iso.join (RelIso.refl _) ((completeMultipartitePair 1 n).trans
      (by rw [bipartite_eq_join])))).trans
    ((Iso.joinAssoc (empty 1) (empty 1) (empty n)).symm.trans
      (Iso.join (by rw [← bipartite_eq_join]; exact bipartiteOneOne) (RelIso.refl _)))

/-- The complement of the book `B_n` is its spine, edgeless, next to a clique on the pages. -/
noncomputable def complBook (n : ℕ) : (book n)ᶜ ≃cg empty 2 ⊕g complete n := by
  rw [show empty 2 ⊕g complete n = (complete 2 ∇g empty n)ᶜ from by
    rw [compl_join, compl_complete, compl_empty]]
  exact Iso.compl (bookEqJoin n)

/-! ### Circulants

`circulant_one_eq_cycle` and the normalisation lemmas of `IsoGraph/Core/Identities.lean`
are equalities of `CGraph`s already, so these are one-liners. -/

/-- The step `n - 1` runs around the cycle backwards. -/
@[toIsoGraph]
theorem circulant_pred (n : ℕ) (hn : 1 ≤ n) : circulant n [n - 1] = cycle n := by
  rw [← circulant_neg_cons n 1 hn [], circulant_one_eq_cycle]

/-- The cycle written with the symmetric connection set `{±1}`. -/
@[toIsoGraph]
theorem circulant_one_pred (n : ℕ) (hn : 1 ≤ n) : circulant n [1, n - 1] = cycle n := by
  rw [circulant_neg_cons n 1 hn [n - 1], circulant_dup_cons, circulant_pred n hn]

/-- **A perfect matching, as a circulant.** -/
@[toIsoGraph circulant_matching]
noncomputable def circulantMatching (m : ℕ) :
    circulant (2 * (m + 1)) [m + 1] ≃cg empty (m + 1) □g complete 2 :=
  (Iso.circulantMatching m).symm

/-- The `m = 0` case of both readings: one edge. -/
@[toIsoGraph]
theorem circulant_two_one : circulant 2 [1] = complete 2 := by
  rw [circulant_one_eq_cycle, cycle_two]

@[toIsoGraph simp compl_paley_thirteen]
def complPaleyThirteen : (paley 13)ᶜ ≃cg paley 13 :=
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  Iso.complPaleyOfNotIsSquare 13 rfl not_isSquare_two_zmod_thirteen

@[toIsoGraph simp compl_paley_seventeen]
def complPaleySeventeen : (paley 17)ᶜ ≃cg paley 17 :=
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  Iso.complPaleyOfNotIsSquare 17 rfl not_isSquare_three_zmod_seventeen

@[toIsoGraph compl_paley_nine]
def complPaleyNine :
    (paley 9)ᶜ ≃cg complete 3 ⊕g (complete 3 ⊕g complete 3) :=
  Iso.complPaleyNine

/-- The complement of a three-part complete multipartite graph is three cliques. -/
noncomputable def complCompleteMultipartiteTriple (a b c : ℕ) :
    (completeMultipartite [a, b, c])ᶜ ≃cg
      complete a ⊕g (complete b ⊕g complete c) :=
  (complCompleteMultipartiteCons a [b, c]).trans
    (Iso.disjUnion (RelIso.refl _)
      ((complCompleteMultipartiteCons b [c]).trans
        (Iso.disjUnion (RelIso.refl _) (Iso.compl (completeMultipartiteSingleton c)))))

@[toIsoGraph paley_nine]
noncomputable def paleyNine : paley 9 ≃cg completeMultipartite [3, 3, 3] := by
  rw [show paley 9 = ((paley 9)ᶜ)ᶜ from (compl_compl _).symm,
    show completeMultipartite [3, 3, 3] = ((completeMultipartite [3, 3, 3])ᶜ)ᶜ from
      (compl_compl _).symm]
  exact Iso.compl (complPaleyNine.trans (complCompleteMultipartiteTriple 3 3 3).symm)

/-! ### Kneser and Johnson graphs

The degenerate parameters.  `kneser n k` and `johnson n k` both have
`{s : Finset (Fin n) // s.card = k}` for a vertex type, of size `n.choose k`; for `k = 0` there is
one vertex, for `k = 1` the vertices are the points of `Fin n` and both graphs are complete, and
once `n < 2 * k` no two `k`-sets are disjoint so the Kneser graph has no edges at all. -/

@[toIsoGraph simp kneser_zero]
noncomputable def kneserZero (n : ℕ) : kneser n 0 ≃cg empty 1 := by
  refine isoEmptyOfCard ?_ (by simp)
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  have hst : s = t := by rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht]
  cases hst
  simp

@[toIsoGraph simp kneser_one]
noncomputable def kneserOne (n : ℕ) : kneser n 1 ≃cg complete n := by
  refine isoCompleteOfCard ?_ (by simp)
  rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ht
  have hab : a ≠ b := by rintro rfl; exact hne rfl
  simp [hne, Finset.singleton_inter_of_notMem, hab]

/-- Once `n < 2 * k` there are no two disjoint `k`-subsets of `Fin n`, so the Kneser graph is
edgeless. -/
@[toIsoGraph kneser_eq_empty]
noncomputable def kneserEqEmpty (n k : ℕ) (hn : n < 2 * k) : kneser n k ≃cg empty (n.choose k) := by
  refine isoEmptyOfCard ?_ (by simp)
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  rw [kneser_adj]
  rcases Bool.eq_false_or_eq_true (decide (s ∩ t = ∅)) with hd | hd
  · exfalso
    have hdisj : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.2 (of_decide_eq_true hd)
    have hcard : (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint hdisj
    have hle : (s ∪ t).card ≤ n := by simpa using Finset.card_le_univ (s ∪ t)
    omega
  · simp [hd]

@[toIsoGraph simp johnson_zero]
noncomputable def johnsonZero (n : ℕ) : johnson n 0 ≃cg empty 1 := by
  refine isoEmptyOfCard ?_ (by simp)
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  have hst : s = t := by rw [Finset.card_eq_zero.mp hs, Finset.card_eq_zero.mp ht]
  cases hst
  simp

@[toIsoGraph simp johnson_one]
noncomputable def johnsonOne (n : ℕ) : johnson n 1 ≃cg complete n := by
  refine isoCompleteOfCard ?_ (by simp)
  rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ht
  have hab : a ≠ b := by rintro rfl; exact hne rfl
  simp [hne, Finset.singleton_inter_of_notMem, hab]

/-- There is only one `n`-subset of `Fin n`. -/
@[toIsoGraph simp kneser_self]
noncomputable def kneserSelf : ∀ n : ℕ, kneser n n ≃cg empty 1
  | 0 => kneserZero 0
  | n + 1 => (kneserEqEmpty (n + 1) (n + 1) (by omega)).trans (by rw [Nat.choose_self])

@[toIsoGraph simp johnson_self]
noncomputable def johnsonSelf (n : ℕ) : johnson n n ≃cg empty 1 := by
  refine (isoEmptyOfCard ?_ (by simp : FinEnum.card (johnson n n).V = n.choose n)).trans
    (by rw [Nat.choose_self])
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  have hst : s = t := by
    rw [Finset.eq_univ_of_card s (by simpa using hs), Finset.eq_univ_of_card t (by simpa using ht)]
  cases hst
  simp

/-- The other end of `johnson_one`: the `n`-subsets of an `(n+1)`-set also form a clique. -/
@[toIsoGraph simp johnson_pred]
noncomputable def johnsonPred (n : ℕ) : johnson (n + 1) n ≃cg complete (n + 1) :=
  (Iso.johnsonCompl (n + 1) n (by omega)).trans
    (by rw [show n + 1 - n = 1 from by omega]; exact johnsonOne (n + 1))

/-- One step further down: the `n`-subsets of an `(n+2)`-set form a triangular graph. -/
def johnsonSubTwo (n : ℕ) : johnson (n + 2) n ≃cg triangular (n + 2) :=
  (Iso.johnsonCompl (n + 2) n (by omega)).trans (by rw [show n + 2 - n = 2 from by omega])

/-- The triangular graph is the complement of the Petersen-style Kneser graph on 2-sets. -/
def triangularEqComplKneser (n : ℕ) : triangular n ≃cg (kneser n 2)ᶜ := johnsonTwoIso n

/-- Any two of the three 2-subsets of `Fin 3` meet, so `T(3) = K₃`. -/
noncomputable def triangularThree : triangular 3 ≃cg complete 3 :=
  isoCompleteOfCard (G := johnson 3 2) (by decide) (by simp)

/-- The three ways to split `{0, 1, 2, 3}` into two pairs. -/
private def kneserFourTwoMap : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → (kneser 4 2).V
  | .inl 0 => ⟨{0, 1}, by decide⟩
  | .inl 1 => ⟨{2, 3}, by decide⟩
  | .inr (.inl 0) => ⟨{0, 2}, by decide⟩
  | .inr (.inl 1) => ⟨{1, 3}, by decide⟩
  | .inr (.inr 0) => ⟨{0, 3}, by decide⟩
  | .inr (.inr 1) => ⟨{1, 2}, by decide⟩

@[toIsoGraph kneser_four_two]
noncomputable def kneserFourTwo :
    kneser 4 2 ≃cg complete 2 ⊕g (complete 2 ⊕g complete 2) :=
  (isoOfAdj (G := complete 2 ⊕g (complete 2 ⊕g complete 2))
    (H := kneser 4 2) (Equiv.ofBijective kneserFourTwoMap (by decide)) (by decide)).symm

noncomputable def triangularFour : triangular 4 ≃cg cocktailParty 3 := by
  refine ((triangularEqComplKneser 4).trans (Iso.compl kneserFourTwo)).trans ?_
  rw [show cocktailParty 3 = ((completeMultipartite [2, 2, 2])ᶜ)ᶜ from (compl_compl _).symm]
  exact Iso.compl (complCompleteMultipartiteTriple 2 2 2).symm

/-! ### Hypercubes -/

@[toIsoGraph simp hypercube_zero]
noncomputable def hypercubeZero : hypercube 0 ≃cg empty 1 :=
  isoEmptyOfCard (by decide) (by simp)

@[toIsoGraph simp hypercube_one]
noncomputable def hypercubeOne : hypercube 1 ≃cg complete 2 :=
  isoCompleteOfCard (by decide) (by simp)

/-- The square is the two-dimensional cube. -/
@[toIsoGraph simp hypercube_two]
def hypercubeTwo : hypercube 2 ≃cg cycle 4 :=
  isoOfAdj (G := hypercube 2) (H := cycle 4)
    (⟨fun x ↦ if x 0 then (if x 1 then 2 else 1) else (if x 1 then 3 else 0),
      ![![false, false], ![true, false], ![true, true], ![false, true]],
      by decide, by decide⟩ : (Fin 2 → Bool) ≃ Fin 4)
    (by decide)

/-- **`Q_{n+1} = Q_n □ K₂`**: splitting a bit-string of length `n + 1` into its first bit and the
rest turns "differ in exactly one place" into the cartesian product's "agree on one side and
differ on the other". -/
@[toIsoGraph hypercube_succ]
def hypercubeSucc (n : ℕ) :
    hypercube (n + 1) ≃cg hypercube n □g complete 2 := by
  refine isoOfAdj (G := hypercube (n + 1)) (H := hypercube n □g complete 2)
    (⟨fun x ↦ (fun i ↦ x i.succ, if x 0 then 1 else 0),
      fun p ↦ Fin.cons (decide (p.2 = 1)) p.1,
      fun x ↦ by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · cases hx : x 0 <;> simp [hx]
        · simp,
      fun p ↦ by
        obtain ⟨f, k⟩ := p
        refine Prod.ext ?_ ?_
        · funext i; simp
        · fin_cases k <;> simp⟩ : (Fin (n + 1) → Bool) ≃ ((Fin n → Bool) × Fin 2))
    fun x y ↦ ?_
  -- only `β`-reduction here: the two `decide`s below are the product graph's own, taken from the
  -- factors' `FinEnum`s, so they must come out of `cartesianProduct_adj` rather than be written
  show (hypercube n □g complete 2).Adj
      ((fun i : Fin n ↦ x i.succ), (if x 0 then 1 else 0 : Fin 2))
      ((fun i : Fin n ↦ y i.succ), (if y 0 then 1 else 0 : Fin 2))
    = (hypercube (n + 1)).Adj x y
  rw [cartesianProduct_adj, hypercube_adj, hypercube_adj, complete_adj, card_ne_succ,
    Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ne_eq]
  rw [show ((fun i : Fin n ↦ x i.succ) = fun i : Fin n ↦ y i.succ)
        ↔ (Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card = 0 from by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
      simp]
  generalize (Finset.univ.filter fun i : Fin n ↦ x i.succ ≠ y i.succ).card = s
  cases hx0 : x 0 <;> cases hy0 : y 0 <;> cases s <;> simp <;> intro _ <;> decide

/-! ### Folded cubes

`foldedCube n` joins each pair of antipodal vertices of `Q_n`.  For `n ≤ 2` every pair of distinct
bit-strings differs in one place or in all of them, so the graph is complete; at `n = 3` the four
new edges make each vertex adjacent to the whole opposite parity class. -/

@[toIsoGraph simp foldedCube_zero]
noncomputable def foldedCubeZero : foldedCube 0 ≃cg empty 1 :=
  isoEmptyOfCard (by decide) (by simp)

@[toIsoGraph simp foldedCube_one]
noncomputable def foldedCubeOne : foldedCube 1 ≃cg complete 2 :=
  isoCompleteOfCard (by decide) (by simp)

@[toIsoGraph foldedCube_two]
noncomputable def foldedCubeTwo : foldedCube 2 ≃cg complete 4 :=
  isoCompleteOfCard (by decide) (by simp)

/-- Antipodal bit-strings of odd length have opposite parity, so every edge of `foldedCube 3`
crosses the parity classes. -/
@[toIsoGraph foldedCube_three]
def foldedCubeThree : foldedCube 3 ≃cg bipartite 4 4 :=
  isoOfAdj (G := foldedCube 3) (H := bipartite 4 4)
    (⟨fun x ↦ if xor (xor (x 0) (x 1)) (x 2) then
          .inr (if x 1 then (if x 2 then 3 else 2) else (if x 2 then 1 else 0))
        else .inl (if x 1 then (if x 2 then 3 else 2) else (if x 2 then 1 else 0)),
      Sum.elim
        ![![false, false, false], ![true, false, true], ![true, true, false], ![false, true, true]]
        ![![true, false, false], ![false, false, true], ![false, true, false], ![true, true, true]],
      by decide, by decide⟩ : (Fin 3 → Bool) ≃ (Fin 4 ⊕ Fin 4))
    (by decide)

end CGraph

namespace IsoGraph

@[simp] theorem V_completeMultipartite (ds : List ℕ) : (completeMultipartite ds).V = ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => rw [completeMultipartite_cons, V_join, V_empty, ih, List.sum_cons]

attribute [simp] IsoGraph.circulant_zero_cons IsoGraph.circulant_dup_cons

/-! ### The abbreviated families

`book`, `triangular` and `cocktailParty` are `abbrev`s on both levels, so `@[toIsoGraph]` sees
straight through them and would state these facts about `completeMultipartite` and `johnson`
instead.  They are therefore restated by hand, each from the isomorphism above: `simp only
[isoTransfer]` puts the goal in terms of classes, and `Quotient.sound` supplies the class. -/

@[simp] theorem cocktailParty_one : cocktailParty 1 = empty 2 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.cocktailPartyOne⟩

theorem book_zero : book 0 = complete 2 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.bookZero⟩

theorem book_one : book 1 = complete 3 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.bookOne⟩

@[simp] theorem cocktailParty_two : cocktailParty 2 = cycle 4 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.cocktailPartyTwo⟩

/-- The book `Bₙ` is an edge joined to `n` independent vertices. -/
theorem book_eq_join (n : ℕ) : book n = complete 2 ∇g empty n := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.bookEqJoin n⟩

/-- The complement of the book `B_n` is its spine, edgeless, next to a clique on the pages. -/
theorem compl_book (n : ℕ) : (book n)ᶜ = empty 2 ⊕g complete n := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.complBook n⟩

/-- One step further down: the `n`-subsets of an `(n+2)`-set form a triangular graph. -/
theorem johnson_sub_two (n : ℕ) : johnson (n + 2) n = triangular (n + 2) := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.johnsonSubTwo n⟩

/-- The triangular graph is the complement of the Kneser graph on 2-sets. -/
theorem triangular_eq_compl_kneser (n : ℕ) : triangular n = (kneser n 2)ᶜ := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.triangularEqComplKneser n⟩

/-- `T(3) = K₃`. -/
theorem triangular_three : triangular 3 = complete 3 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.triangularThree⟩

/-- `T(4)` is the octahedron. -/
theorem triangular_four : triangular 4 = cocktailParty 3 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.triangularFour⟩

/-! ## Decorated cycles and trees

The `ofEdges`-based families — tadpoles, lollipops, spiders and cycles with pendant vertices —
degenerate into the named families when one of their parameters vanishes.  Those degeneracies are
equalities of `CGraph`s and are generated from them; what is left here is the invariance of a
spider under permuting its legs, which renumbers the vertices and so is only an isomorphism. -/

attribute [simp] IsoGraph.spider_zero_cons

/-- Two adjacent legs of a spider may be exchanged. -/
theorem spider_swap (pre post : List ℕ) (a b : ℕ) :
    spider (pre ++ a :: b :: post) = spider (pre ++ b :: a :: post) := by
  have hsum : (pre ++ b :: a :: post).sum = (pre ++ a :: b :: post).sum := by
    simp only [List.sum_append, List.sum_cons]; omega
  have hL : CGraph.spiderEdges 1 (pre ++ a :: b :: post)
      = CGraph.spiderEdges 1 pre ++ (CGraph.legEdges 0 (1 + pre.sum) a ++
          (CGraph.legEdges 0 (1 + pre.sum + a) b ++
            CGraph.spiderEdges (1 + pre.sum + a + b) post)) := by
    rw [CGraph.spiderEdges_append, CGraph.spiderEdges, CGraph.spiderEdges]
  have hR : CGraph.spiderEdges 1 (pre ++ b :: a :: post)
      = CGraph.spiderEdges 1 pre ++ (CGraph.legEdges 0 (1 + pre.sum) b ++
          (CGraph.legEdges 0 (1 + pre.sum + b) a ++
            CGraph.spiderEdges (1 + pre.sum + a + b) post)) := by
    rw [CGraph.spiderEdges_append, CGraph.spiderEdges, CGraph.spiderEdges,
      show 1 + pre.sum + b + a = 1 + pre.sum + a + b from by omega]
  rw [spider_def, spider_def, CGraph.spider, CGraph.spider, hsum, hL, hR]
  refine Quotient.sound (CGraph.nonempty_iso_ofEdges_swap_legs _ (1 + pre.sum) a b _ _
    (by omega) ?_ ?_ ?_)
  · simp only [List.sum_append, List.sum_cons]
    omega
  · intro p q h
    have := CGraph.mem_spiderEdges_bound 1 pre p q h
    omega
  · intro p q h
    have := CGraph.mem_spiderEdges_bound (1 + pre.sum + a + b) post p q h
    omega

/-- The spider depends only on the multiset of its leg lengths. -/
theorem spider_perm_append {ks ls : List ℕ} (h : ks.Perm ls) :
    ∀ pre : List ℕ, spider (pre ++ ks) = spider (pre ++ ls) := by
  induction h with
  | nil => intro pre; rfl
  | cons x _ ih =>
      intro pre
      simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [x])
  | swap x y l => intro pre; exact spider_swap pre l y x
  | trans _ _ ih1 ih2 => intro pre; exact (ih1 pre).trans (ih2 pre)

theorem spider_perm {ks ls : List ℕ} (h : ks.Perm ls) : spider ks = spider ls := by
  simpa using spider_perm_append h []

attribute [simp] IsoGraph.cyclePendant_append_zero IsoGraph.thetaGraph_zero_zero_cons

/-! ## Decorated cycles and trees, up to isomorphism

Unlike the identities just above, these are not equalities of `CGraph`s: both sides are the same
graph drawn with a different numbering of the vertices, so each one carries an explicit
relabelling (`CGraph.foldAt`, `CGraph.rotTail`, `CGraph.swapZeroOne`, `finSumFinEquiv`).  The
relabelling is a `def` on `CGraph`, so that it can be computed with, and `@[toIsoGraph]` turns each
one into the equation of isomorphism classes. -/

end IsoGraph

namespace CGraph

/-- A spider with two legs is a path: fold the graph at the centre, so that one leg is numbered
backwards from the far end. -/
@[toIsoGraph simp spider_pair]
def spiderPair (a b : ℕ) : spider [a, b] ≃cg path (1 + a + b) := by
  have hN : (1 : ℕ) + ([a, b] : List ℕ).sum = 1 + a + b := by simp [Nat.add_assoc]
  have hes : CGraph.spiderEdges 1 [a, b]
      = CGraph.legEdges 0 1 a ++ CGraph.legEdges 0 (1 + a) b := by
    simp [CGraph.spiderEdges]
  set E : (CGraph.spider [a, b]).V ≃ (CGraph.path (1 + a + b)).V :=
    (finCongr hN).trans (CGraph.foldAt a (1 + a + b) (by omega)) with hE
  refine CGraph.isoOfAdj E ?_
  intro x y
  have hEz : ∀ z : (CGraph.spider [a, b]).V, (E z).1 = if z.1 ≤ a then a - z.1 else z.1 := by
    intro z; rw [hE]; rfl
  have hx : x.1 < 1 + a + b := hN ▸ x.isLt
  have hy : y.1 < 1 + a + b := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hEz x, hEz y]
  simp only [CGraph.spider]
  rw [CGraph.ofEdges_adj_val, hes]
  simp only [List.mem_append, CGraph.mem_legEdges]
  exact CGraph.foldAt_pair_iff a b x.1 y.1 hx hy

attribute [simp] IsoGraph.thetaGraph_nil IsoGraph.thetaGraph_replicate_zero

/-- A theta graph with a single path is a path: rotate the second pole to the far end. -/
@[toIsoGraph simp thetaGraph_singleton]
def thetaGraphSingleton (k : ℕ) : thetaGraph [k] ≃cg path (k + 2) := by
  rcases k with _ | k
  · show thetaGraph (List.replicate (0 + 1) 0) ≃cg path 2
    rw [thetaGraph_replicate_zero, path_two]
  have hN : 2 + ([k + 1] : List ℕ).sum = k + 3 := by simp; omega
  set E : (CGraph.thetaGraph [k + 1]).V ≃ (CGraph.path (k + 1 + 2)).V :=
    (finCongr hN).trans (CGraph.rotTail (k + 3)) with hE
  refine CGraph.isoOfAdj E ?_
  intro x y
  have hEz : ∀ z : (CGraph.thetaGraph [k + 1]).V,
      (E z).1 = if z.1 = 0 then 0 else if z.1 = 1 then k + 2 else z.1 - 1 := fun _ ↦ rfl
  have hx : x.1 < k + 3 := hN ▸ x.isLt
  have hy : y.1 < k + 3 := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hEz x, hEz y]
  simp only [CGraph.thetaGraph]
  rw [CGraph.ofEdges_adj_val]
  simp only [CGraph.mem_thetaEdges_singleton]
  exact CGraph.rotTail_pair_iff k x.1 y.1 hx hy

/-- A spider all of whose legs have length one is a star: the centre keeps its number and the
leaves follow it. -/
@[toIsoGraph simp spider_replicate_one]
def spiderReplicateOne (n : ℕ) : spider (List.replicate n 1) ≃cg star n := by
  have hN : (1 : ℕ) + (List.replicate n 1).sum = 1 + n := by simp
  refine RelIso.symm ?_
  · set E : (CGraph.star n).V ≃ (CGraph.spider (List.replicate n 1)).V :=
      (finSumFinEquiv (m := 1) (n := n)).trans (finCongr hN.symm) with hE
    refine CGraph.isoOfAdj E ?_
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete n).V, (E (Sum.inr b)).1 = 1 + b.1 := fun _ ↦ rfl
    have hsp : ∀ u v : (CGraph.spider (List.replicate n 1)).V,
        ((CGraph.spider (List.replicate n 1)).Adj u v = true ↔
          (u.1 ≠ v.1 ∧ ((u.1 = 0 ∧ 1 ≤ v.1 ∧ v.1 < 1 + n) ∨
            (v.1 = 0 ∧ 1 ≤ u.1 ∧ u.1 < 1 + n)))) := by
      intro u v
      simp only [CGraph.spider]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_spiderEdges_replicate_one]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hsp]
    · -- both are the centre, and `Fin 1` is a subsingleton
      rw [hl a, hl b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega

end CGraph

namespace IsoGraph

/-- Every spider all of whose legs have length one is a star. -/
theorem spider_of_all_one {ks : List ℕ} (h : ∀ k ∈ ks, k = 1) : spider ks = star ks.length := by
  obtain ⟨n, rfl⟩ : ∃ n, ks = List.replicate n 1 := ⟨ks.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
  rw [spider_replicate_one, List.length_replicate]

/-- A single vertex carrying `k` pendant vertices is the star `K_{1,k}`. -/
@[simp] theorem cyclePendant_one (k : ℕ) : cyclePendant 1 [k] = star k := by
  rw [cyclePendant_def, CGraph.cyclePendant_one_eq_spider, ← spider_def, spider_replicate_one]

/-- The star with two leaves is the path on three vertices. -/
theorem star_two : star 2 = path 3 := by
  rw [← spider_replicate_one 2, show List.replicate 2 1 = [1, 1] from rfl, spider_pair]

end IsoGraph

namespace CGraph

/-- A double star with no leaves on the second centre is a star. -/
@[toIsoGraph simp doubleStar_right_zero]
def doubleStarRightZero (m : ℕ) : doubleStar m 0 ≃cg star (m + 1) := by
  have hN : 1 + (m + 1) = 2 + m + 0 := by omega
  refine RelIso.symm ?_
  · set E : (CGraph.star (m + 1)).V ≃ (CGraph.doubleStar m 0).V :=
      (finSumFinEquiv (m := 1) (n := m + 1)).trans (finCongr hN) with hE
    refine CGraph.isoOfAdj E ?_
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete (m + 1)).V, (E (Sum.inr b)).1 = 1 + b.1 := fun _ ↦ rfl
    have hds : ∀ u v : (CGraph.doubleStar m 0).V,
        ((CGraph.doubleStar m 0).Adj u v = true ↔
          (u.1 ≠ v.1 ∧
            (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + m) ∨
                (u.1 = 1 ∧ 2 + m ≤ v.1 ∧ v.1 < 2 + m + 0)) ∨
              ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + m) ∨
                (v.1 = 1 ∧ 2 + m ≤ u.1 ∧ u.1 < 2 + m + 0))))) := by
      intro u v
      simp only [CGraph.doubleStar]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_doubleStarEdges]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hds]
    · rw [hl a, hl b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 1 := a.isLt
      have hb : b.1 < m + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < m + 1 := a.isLt
      have hb : b.1 < 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < m + 1 := a.isLt
      have hb : b.1 < m + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega

/-- A double star with no leaves on the first centre is a star: the two centres change places, so
that the one carrying the leaves is numbered first. -/
@[toIsoGraph simp doubleStar_left_zero]
def doubleStarLeftZero (n : ℕ) : doubleStar 0 n ≃cg star (n + 1) := by
  have hN : 1 + (n + 1) = 2 + 0 + n := by omega
  refine RelIso.symm ?_
  · set E : (CGraph.star (n + 1)).V ≃ (CGraph.doubleStar 0 n).V :=
      ((finSumFinEquiv (m := 1) (n := n + 1)).trans (finCongr hN)).trans
        (CGraph.swapZeroOne (2 + 0 + n) (by omega)) with hE
    refine CGraph.isoOfAdj E ?_
    have hl : ∀ a : (CGraph.complete 1).V, (E (Sum.inl a)).1 = 1 := by
      intro a
      have ha : a.1 = 0 := Nat.lt_one_iff.mp a.isLt
      show (if a.1 = 0 then 1 else if a.1 = 1 then 0 else a.1) = 1
      rw [if_pos ha]
    have hr : ∀ b : (CGraph.complete (n + 1)).V,
        (E (Sum.inr b)).1 = if b.1 = 0 then 0 else 1 + b.1 := by
      intro b
      show (if 1 + b.1 = 0 then 1 else if 1 + b.1 = 1 then 0 else 1 + b.1)
        = if b.1 = 0 then 0 else 1 + b.1
      split_ifs <;> omega
    have hds : ∀ u v : (CGraph.doubleStar 0 n).V,
        ((CGraph.doubleStar 0 n).Adj u v = true ↔
          (u.1 ≠ v.1 ∧
            (((u.1 = 0 ∧ v.1 = 1) ∨ (u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + 0) ∨
                (u.1 = 1 ∧ 2 + 0 ≤ v.1 ∧ v.1 < 2 + 0 + n)) ∨
              ((v.1 = 0 ∧ u.1 = 1) ∨ (v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + 0) ∨
                (v.1 = 1 ∧ 2 + 0 ≤ u.1 ∧ u.1 < 2 + 0 + n))))) := by
      intro u v
      simp only [CGraph.doubleStar]
      rw [CGraph.ofEdges_adj_val]
      simp only [CGraph.mem_doubleStarEdges]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hds]
    · rw [hl a, hl b]
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have hb : b.1 < n + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inl_inr, iff_true]
      rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · rw [if_pos hb0]
        simp
      · rw [if_neg (by omega : ¬ b.1 = 0)]
        simp only [true_and, and_true]
        omega
    · rw [hr a, hl b]
      have ha : a.1 < n + 1 := a.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inl, iff_true]
      rcases Nat.eq_zero_or_pos a.1 with ha0 | ha0
      · rw [if_pos ha0]
        simp
      · rw [if_neg (by omega : ¬ a.1 = 0)]
        simp only [true_and, and_true]
        omega
    · rw [hr a, hr b]
      have ha : a.1 < n + 1 := a.isLt
      have hb : b.1 < n + 1 := b.isLt
      simp only [CGraph.star, CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      rcases Nat.eq_zero_or_pos a.1 with ha0 | ha0 <;>
        rcases Nat.eq_zero_or_pos b.1 with hb0 | hb0
      · rw [if_pos ha0, if_pos hb0]
        simp only [true_and]
        omega
      · rw [if_pos ha0, if_neg (by omega : ¬ b.1 = 0)]
        simp only [true_and]
        omega
      · rw [if_neg (by omega : ¬ a.1 = 0), if_pos hb0]
        simp only [true_and]
        omega
      · rw [if_neg (by omega : ¬ a.1 = 0), if_neg (by omega : ¬ b.1 = 0)]
        omega

attribute [simp] IsoGraph.cyclePendant_singleton_one

/-- A theta graph with two paths is a cycle: the two paths are laid end to end. -/
@[toIsoGraph simp thetaGraph_pair]
def thetaGraphPair (a b : ℕ) : thetaGraph [a, b] ≃cg cycle (2 + a + b) := by
  have hN : 2 + ([a, b] : List ℕ).sum = 2 + a + b := by simp; omega
  set E : (CGraph.thetaGraph [a, b]).V ≃ (CGraph.cycle (2 + a + b)).V :=
    (finCongr hN).trans (CGraph.thetaCyclePerm a b) with hE
  refine CGraph.isoOfAdj E ?_
  intro x y
  have hEz : ∀ z : (CGraph.thetaGraph [a, b]).V,
      (E z).1 = CGraph.thetaCycleFwd a b z.1 := fun _ ↦ rfl
  have hx : x.1 < 2 + a + b := hN ▸ x.isLt
  have hy : y.1 < 2 + a + b := hN ▸ y.isLt
  rw [Bool.eq_iff_iff, CGraph.cycle_adj_val, hEz x, hEz y]
  simp only [CGraph.thetaGraph]
  rw [CGraph.ofEdges_adj_val,
    show CGraph.thetaEdges 2 [a, b] = CGraph.thetaEdges 2 [a] ++ CGraph.thetaEdges (2 + a) [b] from
      CGraph.thetaEdges_cons 2 a [b]]
  simp only [List.mem_append]
  exact CGraph.thetaCycle_adj_iff a b x.1 y.1 hx hy

/-- The two ends of a double star can be exchanged. -/
@[toIsoGraph doubleStar_comm]
def doubleStarComm (m n : ℕ) : doubleStar m n ≃cg doubleStar n m := by
  set E : (CGraph.doubleStar m n).V ≃ (CGraph.doubleStar n m).V :=
    CGraph.doubleStarSwap m n with hE
  refine CGraph.isoOfAdj E ?_
  intro x y
  have hx : x.1 < 2 + m + n := x.isLt
  have hy : y.1 < 2 + m + n := y.isLt
  have hval : ∀ p : (CGraph.doubleStar m n).V,
      (E p).1 = CGraph.doubleStarSwapFwd m n p.1 := fun _ ↦ rfl
  rw [Bool.eq_iff_iff, CGraph.doubleStar_adj_val, CGraph.doubleStar_adj_val, hval x, hval y]
  unfold CGraph.doubleStarSwapFwd
  split_ifs <;>
    (try simp only [false_and, false_or, true_and, and_true, or_false, true_or, or_true,
      or_self]) <;> omega

end CGraph

namespace IsoGraph

/-- Two adjacent paths of a theta graph may be exchanged. -/
theorem thetaGraph_swap (pre post : List ℕ) (a b : ℕ) :
    thetaGraph (pre ++ a :: b :: post) = thetaGraph (pre ++ b :: a :: post) := by
  have hsum : (pre ++ b :: a :: post).sum = (pre ++ a :: b :: post).sum := by
    simp only [List.sum_append, List.sum_cons]; omega
  have hL : CGraph.thetaEdges 2 (pre ++ a :: b :: post)
      = CGraph.thetaEdges 2 pre ++ ((CGraph.thetaEdges (2 + pre.sum) [a] ++
          CGraph.thetaEdges (2 + pre.sum + a) [b]) ++
            CGraph.thetaEdges (2 + pre.sum + a + b) post) := by
    rw [CGraph.thetaEdges_append, CGraph.thetaEdges_cons (2 + pre.sum) a (b :: post),
      CGraph.thetaEdges_cons (2 + pre.sum + a) b post, List.append_assoc]
  have hR : CGraph.thetaEdges 2 (pre ++ b :: a :: post)
      = CGraph.thetaEdges 2 pre ++ ((CGraph.thetaEdges (2 + pre.sum) [b] ++
          CGraph.thetaEdges (2 + pre.sum + b) [a]) ++
            CGraph.thetaEdges (2 + pre.sum + a + b) post) := by
    rw [CGraph.thetaEdges_append, CGraph.thetaEdges_cons (2 + pre.sum) b (a :: post),
      CGraph.thetaEdges_cons (2 + pre.sum + b) a post,
      show 2 + pre.sum + b + a = 2 + pre.sum + a + b from by omega, List.append_assoc]
  rw [thetaGraph_def, thetaGraph_def, CGraph.thetaGraph, CGraph.thetaGraph, hsum, hL, hR]
  refine Quotient.sound (CGraph.nonempty_iso_ofEdges_swap_theta _ (2 + pre.sum) a b _ _
    (by omega) ?_ ?_ ?_)
  · simp only [List.sum_append, List.sum_cons]
    omega
  · intro p q h
    have := CGraph.mem_thetaEdges_bound 2 pre p q h
    omega
  · intro p q h
    have := CGraph.mem_thetaEdges_bound (2 + pre.sum + a + b) post p q h
    omega

/-- The theta graph depends only on the multiset of its path lengths. -/
theorem thetaGraph_perm_append {xs ys : List ℕ} (h : xs.Perm ys) :
    ∀ pre : List ℕ, thetaGraph (pre ++ xs) = thetaGraph (pre ++ ys) := by
  induction h with
  | nil => intro pre; rfl
  | cons x _ ih =>
      intro pre
      simpa only [List.append_assoc, List.singleton_append] using ih (pre ++ [x])
  | swap x y l => intro pre; exact thetaGraph_swap pre l y x
  | trans _ _ ih1 ih2 => intro pre; exact (ih1 pre).trans (ih2 pre)

theorem thetaGraph_perm {xs ys : List ℕ} (h : xs.Perm ys) : thetaGraph xs = thetaGraph ys := by
  simpa using thetaGraph_perm_append h []

/-- Swapping the two paths of a two-path theta graph. -/
theorem thetaGraph_pair_comm (a b : ℕ) : thetaGraph [a, b] = thetaGraph [b, a] :=
  thetaGraph_perm (List.Perm.swap b a [])

end IsoGraph

namespace CGraph

/-- A theta graph all of whose paths have a single internal vertex is the complete bipartite
graph `K_{2,n}`: the two poles on one side, the `n` midpoints on the other. -/
@[toIsoGraph simp thetaGraph_replicate_one]
def thetaGraphReplicateOne (n : ℕ) :
    thetaGraph (List.replicate n 1) ≃cg bipartite 2 n := by
  have hN : (2 : ℕ) + (List.replicate n 1).sum = 2 + n := by simp
  refine RelIso.symm ?_
  · set E : (CGraph.bipartite 2 n).V ≃ (CGraph.thetaGraph (List.replicate n 1)).V :=
      (finSumFinEquiv (m := 2) (n := n)).trans (finCongr hN.symm) with hE
    refine CGraph.isoOfAdj E ?_
    have hl : ∀ a : (CGraph.complete 2).V, (E (Sum.inl a)).1 = a.1 := fun _ ↦ rfl
    have hr : ∀ b : (CGraph.complete n).V, (E (Sum.inr b)).1 = 2 + b.1 := fun _ ↦ rfl
    have hth : ∀ u v : (CGraph.thetaGraph (List.replicate n 1)).V,
        ((CGraph.thetaGraph (List.replicate n 1)).Adj u v = true ↔
          (u.1 ≠ v.1 ∧ (((u.1 = 0 ∧ 2 ≤ v.1 ∧ v.1 < 2 + n) ∨
              (2 ≤ u.1 ∧ u.1 < 2 + n ∧ v.1 = 1)) ∨
            ((v.1 = 0 ∧ 2 ≤ u.1 ∧ u.1 < 2 + n) ∨ (2 ≤ v.1 ∧ v.1 < 2 + n ∧ u.1 = 1))))) := by
      intro u v
      rw [CGraph.thetaGraph_adj_val]
      simp only [CGraph.mem_thetaEdges_replicate_one]
    rintro (a | a) (b | b) <;> rw [Bool.eq_iff_iff, hth]
    · rw [hl a, hl b]
      have ha : a.1 < 2 := a.isLt
      have hb : b.1 < 2 := b.isLt
      simp only [CGraph.bipartite_adj_inl_inl, Bool.false_eq_true, iff_false]
      omega
    · rw [hl a, hr b]
      have ha : a.1 < 2 := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.bipartite_adj_inl_inr, iff_true]
      omega
    · rw [hr a, hl b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < 2 := b.isLt
      simp only [CGraph.bipartite_adj_inr_inl, iff_true]
      omega
    · rw [hr a, hr b]
      have ha : a.1 < n := a.isLt
      have hb : b.1 < n := b.isLt
      simp only [CGraph.bipartite_adj_inr_inr, Bool.false_eq_true, iff_false]
      omega

end CGraph

namespace IsoGraph

/-- Every theta graph whose paths all have a single internal vertex is complete bipartite. -/
theorem thetaGraph_of_all_one {xs : List ℕ} (h : ∀ k ∈ xs, k = 1) :
    thetaGraph xs = bipartite 2 xs.length := by
  obtain ⟨n, rfl⟩ : ∃ n, xs = List.replicate n 1 := ⟨xs.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
  rw [thetaGraph_replicate_one, List.length_replicate]

end IsoGraph

namespace CGraph

/-- A tadpole whose cycle is `C₂` — a single edge — is a path.  The relabelling swaps the two
vertices of the cycle, so that the tail leaves from the far end. -/
@[toIsoGraph simp tadpole_two]
def tadpoleTwo (k : ℕ) : tadpole 2 k ≃cg path (2 + k) := by
  set E : (CGraph.tadpole 2 k).V ≃ (CGraph.path (2 + k)).V :=
    CGraph.swapZeroOne (2 + k) (by omega) with hE
  refine CGraph.isoOfAdj E ?_
  intro x y
  have hx : x.1 < 2 + k := x.isLt
  have hy : y.1 < 2 + k := y.isLt
  have hval : ∀ p : (CGraph.tadpole 2 k).V,
      (E p).1 = if p.1 = 0 then 1 else if p.1 = 1 then 0 else p.1 := fun _ ↦ rfl
  rw [Bool.eq_iff_iff, CGraph.path_adj_val, hval x, hval y]
  simp only [CGraph.tadpole]
  rw [CGraph.ofEdges_adj_val]
  simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges]
  -- `simp_all` substitutes the branch hypotheses `x.1 = 0`, `x.1 = 1`, … into the membership
  -- disjunctions, which prunes most of them before `omega` has to case on them.
  split_ifs <;> (try simp_all) <;> omega

end CGraph

namespace IsoGraph

/-- A lollipop whose clique is `K₂` is a path. -/
@[simp] theorem lollipop_two (k : ℕ) : lollipop 2 k = path (2 + k) := by
  rw [lollipop_two_eq_tadpole, tadpole_two]

end IsoGraph

/-! ## Products

Commutativity, associativity, the units and distributivity over `disjUnion` are generated from the
isomorphisms in `IsoGraph/Core/Quotient.lean`.  What is proved here is the rest: the mirror image
of each one-sided law, and what the products do to `empty` and `complete`. -/

namespace CGraph

/-- The complement of a complete multipartite graph with `m` equal parts is `m` disjoint cliques. -/
@[toIsoGraph compl_completeMultipartite_replicate]
noncomputable def complCompleteMultipartiteReplicate (m d : ℕ) :
    (completeMultipartite (List.replicate m d))ᶜ ≃cg empty m □g complete d := by
  induction m with
  | zero =>
    rw [List.replicate_zero]
    refine (Iso.compl completeMultipartiteNil).trans ?_
    rw [compl_empty, complete_zero]
    exact (emptyZeroCartesianProduct (complete d)).symm
  | succ m ih =>
    rw [List.replicate_succ]
    exact ((complCompleteMultipartiteCons d (List.replicate m d)).trans
      (Iso.disjUnion (RelIso.refl _) ih)).trans (emptySuccCartesianProduct m (complete d)).symm

/-- **Equal parts make a blow-up**: `K_{m×d}` is `K_m` with each vertex blown up to `d`
independent ones. -/
@[toIsoGraph completeMultipartite_replicate]
noncomputable def completeMultipartiteReplicate (m d : ℕ) :
    completeMultipartite (List.replicate m d) ≃cg complete m ·g empty d := by
  rw [show completeMultipartite (List.replicate m d)
      = ((completeMultipartite (List.replicate m d))ᶜ)ᶜ from (compl_compl _).symm]
  exact (Iso.compl (complCompleteMultipartiteReplicate m d)).trans
    (by rw [← compl_empty d]; exact (completeLexProduct m (empty d)).symm)

/-- `paley 9` is `K₃` with every vertex blown up to three. -/
@[toIsoGraph paley_nine_eq_lexProduct]
noncomputable def paleyNineEqLexProduct : paley 9 ≃cg complete 3 ·g empty 3 :=
  paleyNine.trans (completeMultipartiteReplicate 3 3)

/-- The complement of the cocktail-party graph is a perfect matching. -/
noncomputable def complCocktailParty (n : ℕ) :
    (cocktailParty n)ᶜ ≃cg empty n □g complete 2 :=
  complCompleteMultipartiteReplicate n 2

/-- The cocktail party graph is the complement of a perfect matching, and the matching is a
circulant. -/
noncomputable def complCocktailPartyEqCirculant (m : ℕ) :
    (cocktailParty (m + 1))ᶜ ≃cg circulant (2 * (m + 1)) [m + 1] :=
  (complCocktailParty (m + 1)).trans (circulantMatching m).symm

noncomputable def cocktailPartyEqLexProduct (m : ℕ) :
    cocktailParty m ≃cg complete m ·g empty 2 :=
  completeMultipartiteReplicate m 2

/-- The balanced complete bipartite graph is the two-part blow-up. -/
@[toIsoGraph bipartite_self_eq_lexProduct]
noncomputable def bipartiteSelfEqLexProduct (n : ℕ) :
    bipartite n n ≃cg complete 2 ·g empty n :=
  (completeMultipartitePair n n).symm.trans (completeMultipartiteReplicate 2 n)

/-- **Blowing up a complete multipartite graph multiplies its parts.**  Replacing every vertex by
`d` independent ones keeps the graph complete multipartite, with each part `d` times as large. -/
@[toIsoGraph lexProduct_completeMultipartite_empty]
noncomputable def lexProductCompleteMultipartiteEmpty (ds : List ℕ) (d : ℕ) :
    completeMultipartite ds ·g empty d ≃cg completeMultipartite (ds.map (· * d)) := by
  induction ds with
  | nil =>
    rw [List.map_nil]
    exact ((Iso.lexProduct completeMultipartiteNil (RelIso.refl _)).trans
      (emptyZeroLexProduct (empty d))).trans completeMultipartiteNil.symm
  | cons a ds ih =>
    rw [List.map_cons]
    exact (((Iso.lexProduct (completeMultipartiteCons a ds) (RelIso.refl _)).trans
      (joinLexProduct (empty a) (completeMultipartite ds) (empty d))).trans
      (Iso.join (lexProductEmpty a d) ih)).trans
      (completeMultipartiteCons (a * d) (ds.map (· * d))).symm

/-- The two-part case: blowing up `K_{a,b}` gives `K_{ad,bd}`. -/
@[toIsoGraph bipartite_mul]
noncomputable def bipartiteMul (a b d : ℕ) :
    bipartite (a * d) (b * d) ≃cg bipartite a b ·g empty d :=
  (completeMultipartitePair (a * d) (b * d)).symm.trans
    ((lexProductCompleteMultipartiteEmpty [a, b] d).symm.trans
      (Iso.lexProduct (completeMultipartitePair a b) (RelIso.refl _)))

end CGraph

namespace IsoGraph

/-! ### The cocktail party graph

`cocktailParty` is an `abbrev` on both levels, so — as with the abbreviated families above — these
three are restated by hand from the isomorphisms just proved. -/

/-- The complement of the cocktail-party graph is a perfect matching. -/
theorem compl_cocktailParty (n : ℕ) : (cocktailParty n)ᶜ = empty n □g complete 2 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.complCocktailParty n⟩

/-- The cocktail party graph is the complement of a matching, and the matching is a circulant. -/
theorem compl_cocktailParty_eq_circulant (m : ℕ) :
    (cocktailParty (m + 1))ᶜ = circulant (2 * (m + 1)) [m + 1] := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.complCocktailPartyEqCirculant m⟩

/-- `K_{m×2}` is `K_m` with each vertex blown up to two. -/
theorem cocktailParty_eq_lexProduct (m : ℕ) : cocktailParty m = complete m ·g empty 2 := by
  simp only [isoTransfer]; exact Quotient.sound ⟨CGraph.cocktailPartyEqLexProduct m⟩

/-- **`Q_{m+n} = Q_m □ Q_n`**: splitting a bit-string of length `m + n` into its first `m` and
last `n` bits.  Iterating `hypercube_succ` is all it takes. -/
theorem hypercube_add (m n : ℕ) :
    hypercube (m + n) = hypercube m □g hypercube n := by
  induction n with
  | zero => rw [Nat.add_zero, hypercube_zero, cartesianProduct_empty_one]
  | succ n ih =>
    rw [← Nat.add_assoc, hypercube_succ, ih, cartesianProduct_assoc, ← hypercube_succ]

/-- `Q₄` is the `4 × 4` torus. -/
theorem hypercube_four : hypercube 4 = cycle 4 □g cycle 4 := by
  rw [show hypercube 4 = hypercube (2 + 2) from rfl, hypercube_add, hypercube_two]

/-! ### Rooks and ladders -/

theorem rook_one_left (n : ℕ) : rook 1 n = complete n := by
  show complete 1 □g complete n = complete n
  rw [complete_one, empty_one_cartesianProduct]

theorem rook_one_right (m : ℕ) : rook m 1 = complete m := by
  show complete m □g complete 1 = complete m
  rw [complete_one, cartesianProduct_empty_one]

theorem rook_comm (m n : ℕ) : rook m n = rook n m := cartesianProduct_comm _ _

end IsoGraph

namespace CGraph

/-- The `2 × 2` rook's graph is the square: read the four squares of the board off in cyclic
order. -/
def rookTwoTwo : rook 2 2 ≃cg cycle 4 :=
  isoOfAdj
    (⟨fun p ↦ if p.1 = 0 then (if p.2 = 0 then 0 else 1) else (if p.2 = 0 then 3 else 2),
      ![(0, 0), (0, 1), (1, 1), (1, 0)], by decide, by decide⟩ : (Fin 2 × Fin 2) ≃ Fin 4)
    (by decide)

end CGraph

namespace IsoGraph

/-- The `2 × 2` rook's graph is the square. -/
theorem rook_two_two : rook 2 2 = cycle 4 := by
  show complete 2 □g complete 2 = cycle 4
  simp only [isoTransfer]
  exact Quotient.sound ⟨CGraph.rookTwoTwo⟩

/-- The complement of the rook's graph is the tensor product of the two complete graphs.  This one
is written out rather than generated: `rook` is an abbreviation for a cartesian product, and
`@[toIsoGraph]` would state it for the product and leave the later rewrites with no `rook` to
find. -/
theorem compl_rook (m n : ℕ) :
    (rook m n)ᶜ = complete m ⊗g complete n := by
  have hrook : (rook m n : IsoGraph) = ⟦CGraph.rook m n⟧ := by
    rw [show (rook m n : IsoGraph) = complete m □g complete n from rfl,
      complete_def, complete_def, cartesianProduct_mk]
  rw [hrook, compl_mk, CGraph.compl_rook, complete_def, complete_def, tensorProduct_mk]

/-- `K₂ × K₂` is a perfect matching: the tensor product keeps only the two "diagonal" moves. -/
theorem tensorProduct_complete_two_two :
    complete 2 ⊗g complete 2 = complete 2 ⊕g complete 2 := by
  rw [← compl_rook, rook_two_two, compl_cycle_four]

@[simp] theorem rook_zero_left (n : ℕ) : rook 0 n = empty 0 := by
  show complete 0 □g complete n = empty 0
  rw [complete_zero, empty_zero_cartesianProduct]

@[simp] theorem rook_zero_right (m : ℕ) : rook m 0 = empty 0 := by
  show complete m □g complete 0 = empty 0
  rw [complete_zero, cartesianProduct_empty_zero]

/-- The two-rung ladder is the square. -/
theorem ladder_two : ladder 2 = cycle 4 := by
  show path 2 □g complete 2 = cycle 4
  rw [path_two]
  exact rook_two_two

theorem ladder_one : ladder 1 = complete 2 := by
  show path 1 □g complete 2 = complete 2
  rw [path_one, empty_one_cartesianProduct]

/-- The two-rung prism is the square. -/
theorem prism_two : prism 2 = cycle 4 := by
  show cycle 2 □g complete 2 = cycle 4
  rw [cycle_two]
  exact rook_two_two

/-- `K₂ □ K₃` is the triangular prism. -/
theorem rook_two_three : rook 2 3 = prism 3 := by
  show complete 2 □g complete 3 = cycle 3 □g complete 2
  rw [cycle_three, cartesianProduct_comm]

end IsoGraph

namespace CGraph

/-- The complement of the hexagon is the triangular prism: `i ~ i + 2` gives the two triangles and
`i ~ i + 3` the matching between them. -/
def complCycleSix : (cycle 6)ᶜ ≃cg prism 3 :=
  isoOfAdj
    (⟨![(0, 0), (2, 1), (1, 0), (0, 1), (2, 0), (1, 1)],
      fun p ↦ ![![0, 3], ![2, 5], ![4, 1]] p.1 p.2, by decide, by decide⟩ :
        Fin 6 ≃ (Fin 3 × Fin 2))
    (by decide)

end CGraph

namespace IsoGraph

/-- The complement of the hexagon is the triangular prism. -/
theorem compl_cycle_six : (cycle 6)ᶜ = prism 3 := by
  show (cycle 6)ᶜ = cycle 3 □g complete 2
  simp only [isoTransfer]
  exact Quotient.sound ⟨CGraph.complCycleSix⟩

theorem compl_prism_three : (prism 3)ᶜ = cycle 6 := by
  rw [← compl_cycle_six, compl_compl]

/-- The cube graph is the four-rung prism. -/
theorem hypercube_three : hypercube 3 = prism 4 := by
  show hypercube 3 = cycle 4 □g complete 2
  rw [hypercube_succ, hypercube_two]

@[simp] theorem isBipartite_bipartite (m n : ℕ) : IsBipartite (bipartite m n) := by
  rw [bipartite_def, isBipartite_mk]
  exact ⟨Sum.elim (fun _ ↦ false) (fun _ ↦ true), by
    rintro (a | b) (c | d) hadj <;> simp at hadj ⊢⟩

@[simp] theorem isBipartite_star (n : ℕ) : IsBipartite (star n) := by
  rw [star_eq_bipartite]; exact isBipartite_bipartite 1 n

@[simp] theorem isBipartite_complete_two : IsBipartite (complete 2) := by
  rw [← bipartite_one_one]; exact isBipartite_bipartite 1 1

@[simp] theorem isBipartite_path (n : ℕ) : IsBipartite (path n) := by
  rw [path_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin n).1 % 2 = 1), fun i j hij ↦ ?_⟩
  simp only [CGraph.path, CGraph.ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, ne_eq] at hij
  simp only [ne_eq, decide_eq_decide]
  omega

@[simp] theorem isBipartite_cycle_even (m : ℕ) : IsBipartite (cycle (2 * m)) := by
  rw [cycle_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin (2 * m)).1 % 2 = 1), fun i j hij ↦ ?_⟩
  have hi := i.isLt
  have hj := j.isLt
  have key : ∀ x y : Fin (2 * m), (x.1 + 1) % (2 * m) = y.1 → (x.1 + y.1) % 2 = 1 := by
    intro x y hxy
    have hx := x.isLt
    have hy := y.isLt
    rcases Nat.lt_or_ge (x.1 + 1) (2 * m) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hxy
      omega
    · have : x.1 + 1 = 2 * m := by omega
      rw [this, Nat.mod_self] at hxy
      omega
  simp only [CGraph.cycle, CGraph.ofRel_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, ne_eq] at hij
  have := hij.2
  simp only [ne_eq, decide_eq_decide]
  rcases this with h | h
  · have := key i j h
    omega
  · have := key j i h
    omega

@[simp] theorem isBipartite_hypercube (n : ℕ) : IsBipartite (hypercube n) := by
  induction n with
  | zero => rw [hypercube_zero]; exact isBipartite_empty 1
  | succ n ih =>
    rw [hypercube_succ]
    exact isBipartite_cartesianProduct ih isBipartite_complete_two

@[simp] theorem isBipartite_ladder (n : ℕ) : IsBipartite (ladder n) :=
  isBipartite_cartesianProduct (isBipartite_path n) isBipartite_complete_two

@[simp] theorem isBipartite_prism_even (m : ℕ) : IsBipartite (prism (2 * m)) :=
  isBipartite_cartesianProduct (isBipartite_cycle_even m) isBipartite_complete_two

/-- **A spider is a tree, hence bipartite**: colour a vertex by the parity of its distance from
the centre. -/
@[simp] theorem isBipartite_spider (ks : List ℕ) : IsBipartite (spider ks) := by
  rw [spider_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.spiderDepth 1 ks (i : Fin (1 + ks.sum)).1 % 2 = 1),
    fun x y hxy ↦ ?_⟩
  rw [CGraph.spider_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with h | h
  · have := CGraph.spiderDepth_parity 1 ks x.1 y.1 Nat.one_pos h
    omega
  · have := CGraph.spiderDepth_parity 1 ks y.1 x.1 Nat.one_pos h
    omega

/-- **A double star is a tree, hence bipartite**: one centre goes with the leaves of the other. -/
@[simp] theorem isBipartite_doubleStar (m n : ℕ) : IsBipartite (doubleStar m n) := by
  rw [doubleStar_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((i : Fin (2 + m + n)).1 = 1 ∨
    (2 ≤ (i : Fin (2 + m + n)).1 ∧ (i : Fin (2 + m + n)).1 < 2 + m)), fun x y hxy ↦ ?_⟩
  rw [CGraph.doubleStar_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  omega

/-- **A tadpole with an even cycle is bipartite**: the tail continues the alternation around the
cycle, which closes up because the cycle has even length. -/
@[simp] theorem isBipartite_tadpole_even (m k : ℕ) : IsBipartite (tadpole (2 * m) k) := by
  rw [tadpole_def, isBipartite_mk]
  refine ⟨fun i ↦ decide ((if (i : Fin (2 * m + k)).1 < 2 * m then (i : Fin (2 * m + k)).1
    else (i : Fin (2 * m + k)).1 + 1) % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.tadpole_adj_val] at hxy
  simp only [List.mem_append, CGraph.mem_cycleEdges, CGraph.mem_legEdges] at hxy
  simp only [ne_eq, decide_eq_decide]
  obtain ⟨hne, h⟩ := hxy
  split_ifs <;> omega

/-- **A cycle of even length with pendant vertices is bipartite**: a pendant takes the colour
opposite to the cycle vertex it hangs off. -/
@[simp] theorem isBipartite_cyclePendant_even (t : ℕ) (ks : List ℕ) (h : ks.length ≤ 2 * t) :
    IsBipartite (cyclePendant (2 * t) ks) := by
  rw [cyclePendant_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.pendantOwner (2 * t) 0 (2 * t) ks
    (i : Fin (2 * t + ks.sum)).1 % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.cyclePendant_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  have key : ∀ p q : ℕ, (p, q) ∈ CGraph.cycleEdges (2 * t) ++ CGraph.pendantEdges 0 (2 * t) ks →
      (CGraph.pendantOwner (2 * t) 0 (2 * t) ks p
        + CGraph.pendantOwner (2 * t) 0 (2 * t) ks q) % 2 = 1 := by
    intro p q hpq
    rw [List.mem_append] at hpq
    rcases hpq with hpq | hpq
    · rw [CGraph.mem_cycleEdges] at hpq
      rw [CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega),
        CGraph.pendantOwner_of_lt _ _ _ _ _ (by omega)]
      omega
    · exact CGraph.pendantOwner_parity (2 * t) 0 (2 * t) ks p q (by omega) (by omega) hpq
  rcases hxy.2 with hm | hm
  · have := key x.1 y.1 hm
    omega
  · have := key y.1 x.1 hm
    omega

/-- **A theta graph is bipartite as soon as its paths all have the same parity of length.**  The
colouring is `thetaDepth b`, with `b` recording which class the far pole falls into. -/
theorem isBipartite_thetaGraph_of_parity {xs : List ℕ} (b : ℕ)
    (h : ∀ k ∈ xs, (k + b) % 2 = 1) : IsBipartite (thetaGraph xs) := by
  rw [thetaGraph_def, isBipartite_mk]
  refine ⟨fun i ↦ decide (CGraph.thetaDepth b 2 xs (i : Fin (2 + xs.sum)).1 % 2 = 1),
    fun x y hxy ↦ ?_⟩
  rw [CGraph.thetaGraph_adj_val] at hxy
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with hm | hm
  · have := CGraph.thetaDepth_parity b 2 xs x.1 y.1 (by omega) h hm
    omega
  · have := CGraph.thetaDepth_parity b 2 xs y.1 x.1 (by omega) h hm
    omega

/-- Every path of odd length: the two poles get opposite colours. -/
@[simp] theorem isBipartite_thetaGraph_even {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 0) :
    IsBipartite (thetaGraph xs) :=
  isBipartite_thetaGraph_of_parity 1 fun k hk ↦ by have := h k hk; omega

/-- Every path of even length: the two poles get the same colour. -/
@[simp] theorem isBipartite_thetaGraph_odd {xs : List ℕ} (h : ∀ k ∈ xs, k % 2 = 1) :
    IsBipartite (thetaGraph xs) :=
  isBipartite_thetaGraph_of_parity 0 fun k hk ↦ by have := h k hk; omega

/-- Two paths of different parity close up into an odd cycle, and then the graph is not
bipartite. -/
@[simp] theorem not_isBipartite_thetaGraph_pair {a b : ℕ} (h : (a + b) % 2 = 1) :
    ¬ IsBipartite (thetaGraph [a, b]) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = 2 * m + 3 := ⟨(a + b) / 2, by omega⟩
  rw [thetaGraph_pair, hm]
  exact not_isBipartite_cycle_odd m

/-- A tadpole whose cycle is odd is not bipartite. -/
theorem not_isBipartite_tadpole_odd (m k : ℕ) : ¬ IsBipartite (tadpole (2 * m + 3) k) := by
  rw [tadpole_def, isBipartite_mk]
  exact CGraph.not_isBipartite_ofEdges_of_odd_cycle _ (2 * m + 3) _ (by omega) (by omega)
    (by omega) fun _ _ h ↦ Or.inl (List.mem_append_left _ h)

/-- A cycle with pendant vertices is not bipartite when the cycle is odd. -/
theorem not_isBipartite_cyclePendant_odd (m : ℕ) (ks : List ℕ) :
    ¬ IsBipartite (cyclePendant (2 * m + 3) ks) := by
  rw [cyclePendant_def, isBipartite_mk]
  exact CGraph.not_isBipartite_ofEdges_of_odd_cycle _ (2 * m + 3) _ (by omega) (by omega)
    (by omega) fun _ _ h ↦ Or.inl (List.mem_append_left _ h)

/-- A lollipop is never bipartite: its head is a complete graph on at least three vertices, and
the triangle `0, 1, 2` sits inside it. -/
theorem not_isBipartite_lollipop (m k : ℕ) : ¬ IsBipartite (lollipop (m + 3) k) := by
  rw [lollipop_def, isBipartite_mk]
  refine CGraph.not_isBipartite_ofEdges_of_odd_cycle _ 3 _ (by omega) (by omega) (by omega) ?_
  intro p q h
  rw [CGraph.mem_cycleEdges] at h
  rcases h with ⟨rfl, h⟩ | ⟨h, rfl⟩
  · exact Or.inl (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨by omega, by omega⟩))
  · exact Or.inr (List.mem_append_left _ ((CGraph.mem_cliqueEdges _ _ _).2 ⟨by omega, by omega⟩))

/-- A wheel is not bipartite: the hub and any edge of the rim form a triangle. -/
theorem not_isBipartite_wheel (n : ℕ) : ¬ IsBipartite (wheel (n + 3)) := by
  rw [wheel_def, isBipartite_mk]
  refine CGraph.not_isBipartite_of_triangle (a := Sum.inl (0 : Fin 1))
    (b := Sum.inr ⟨0, by omega⟩) (d := Sum.inr ⟨1, by omega⟩)
    (by simp [CGraph.wheel]) (by simp [CGraph.wheel]) ?_
  show (CGraph.complete 1 ∇g CGraph.cycle (n + 3)).Adj _ _ = true
  rw [CGraph.join_adj_inr_inr, CGraph.cycle_adj_val]
  show (0 : ℕ) ≠ 1 ∧ ((0 + 1) % (n + 3) = 1 ∨ (1 + 1) % (n + 3) = 0)
  exact ⟨by omega, Or.inl (Nat.mod_eq_of_lt (by omega))⟩

/-- Each edge of `foldedCube n` flips either one coordinate or all `n` of them, so for odd `n`
every edge changes the parity of the number of `true`s. -/
@[simp] theorem isBipartite_foldedCube_odd {n : ℕ} (hn : n % 2 = 1) :
    IsBipartite (foldedCube n) := by
  rw [foldedCube_def, isBipartite_mk]
  refine ⟨fun x ↦ decide ((Finset.univ.filter fun i ↦ x i = true).card % 2 = 1), fun x y hxy ↦ ?_⟩
  rw [CGraph.foldedCube_adj, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hxy
  have hpar := CGraph.card_ne_parity n x y
  simp only [ne_eq, decide_eq_decide]
  rcases hxy.2 with h | h <;> rw [h] at hpar <;> omega

/-- For even `n` the antipodal edges close an odd cycle: flip the coordinates one at a time from
`0…0` to `1…1`, which takes `n` steps, and come back in one. -/
theorem not_isBipartite_foldedCube_of_even {n : ℕ} (h2 : n % 2 = 0) (hn : 0 < n) :
    ¬ IsBipartite (foldedCube n) := by
  rw [foldedCube_def, isBipartite_mk]
  refine CGraph.not_isBipartite_of_odd_walk
    (fun k ↦ (if k ≤ n then CGraph.prefixVec n k else CGraph.prefixVec n 0 :
      (CGraph.foldedCube n).V)) (n + 1) (by omega) ?_ ?_
  · intro k hk
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have hcard := CGraph.card_prefixVec_step n k hkn
      have hne : CGraph.prefixVec n k ≠ CGraph.prefixVec n (k + 1) := by
        intro he
        rw [he] at hcard
        simp at hcard
      rw [if_pos (by omega), if_pos (by omega), CGraph.foldedCube_adj, hcard]
      simp [hne]
    · have hkn' : k = n := by omega
      subst hkn'
      have hcard := CGraph.card_prefixVec_full k
      have hne : CGraph.prefixVec k 0 ≠ CGraph.prefixVec k k := by
        intro he
        have := congrFun he ⟨0, by omega⟩
        simp [CGraph.prefixVec] at this
        omega
      rw [if_pos (by omega), if_neg (by omega), CGraph.foldedCube_adj,
        show (Finset.univ.filter fun i ↦ CGraph.prefixVec k k i ≠ CGraph.prefixVec k 0 i)
          = (Finset.univ.filter fun i ↦ CGraph.prefixVec k 0 i ≠ CGraph.prefixVec k k i) from
          Finset.filter_congr fun i _ ↦ by exact ne_comm, hcard]
      simp [Ne.symm hne]
  · rw [if_neg (by omega), if_pos (by omega)]

theorem not_isBipartite_foldedCube_even (m : ℕ) : ¬ IsBipartite (foldedCube (2 * m + 2)) :=
  not_isBipartite_foldedCube_of_even (by omega) (by omega)

/-- **A circulant on an even number of vertices whose connection set is all odd is bipartite.**
Colour a vertex by the parity of its index: a step of odd length always crosses, because reducing
mod an even `n` does not change parity. -/
theorem isBipartite_circulant {n : ℕ} {S : List ℕ} (hn : n % 2 = 0) (hS : ∀ d ∈ S, d % 2 = 1) :
    IsBipartite (circulant n S) := by
  rw [circulant_def, isBipartite_mk]
  refine ⟨fun x ↦ decide (x.1 % 2 = 1), fun x y hxy ↦ ?_⟩
  have hadj : (decide (x ≠ y) && (S.contains ((y.1 + n - x.1) % n) ||
      S.contains ((x.1 + n - y.1) % n))) = true := hxy
  rw [Bool.and_eq_true, Bool.or_eq_true] at hadj
  have h1 := sub_mod_cases x.isLt y.isLt
  have h2 := sub_mod_cases y.isLt x.isLt
  simp only [ne_eq, decide_eq_decide]
  rcases hadj.2 with h | h
  · have := hS _ (List.mem_of_elem_eq_true h)
    omega
  · have := hS _ (List.mem_of_elem_eq_true h)
    omega

/-- **A circulant on an odd number of vertices is not bipartite** as soon as its connection set
contains a difference that does something.  Stepping by `d` returns to the start after `n` steps,
and `n` is odd. -/
theorem not_isBipartite_circulant_of_odd {n : ℕ} {S : List ℕ} (hn : n % 2 = 1) (d : ℕ)
    (hd : d ∈ S) (h0 : 0 < d) (hdn : d < n) : ¬ IsBipartite (circulant n S) := by
  rw [circulant_def, isBipartite_mk]
  have hpos : 0 < n := by omega
  refine CGraph.not_isBipartite_of_odd_walk
    (fun k ↦ (⟨k * d % n, Nat.mod_lt _ hpos⟩ : Fin n)) n hn ?_
    (Fin.ext (by simp [Nat.mul_mod_right]))
  intro k _
  have ha : k * d % n < n := Nat.mod_lt _ hpos
  have hb : (k + 1) * d % n = (k * d % n + d) % n := by
    rw [show (k + 1) * d = k * d + d by ring, Nat.add_mod, Nat.mod_eq_of_lt hdn]
  have key : ((k + 1) * d % n + n - k * d % n) % n = d ∧ k * d % n ≠ (k + 1) * d % n := by
    rcases Nat.lt_or_ge (k * d % n + d) n with h | h
    · rw [hb, Nat.mod_eq_of_lt h]
      refine ⟨?_, by omega⟩
      rw [show k * d % n + d + n - k * d % n = d + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hdn
    · have he : (k * d % n + d) % n = k * d % n + d - n := by
        conv_lhs => rw [show k * d % n + d = (k * d % n + d - n) + n by omega]
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hb, he]
      refine ⟨?_, by omega⟩
      rw [show k * d % n + d - n + n - k * d % n = d by omega]
      exact Nat.mod_eq_of_lt hdn
  show (decide _ && (S.contains _ || S.contains _)) = true
  rw [key.1]
  simp only [Bool.and_eq_true, Bool.or_eq_true, ne_eq, decide_eq_true_eq, Fin.mk.injEq]
  exact ⟨key.2, Or.inl (List.elem_eq_true_of_mem hd)⟩

/-- The rook's graph has a triangle in each row. -/
@[simp] theorem not_isBipartite_rook (m n : ℕ) : ¬ IsBipartite (rook (m + 3) (n + 1)) := by
  show ¬ IsBipartite (complete (m + 3) □g complete (n + 1))
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_complete m h.1

/-- A prism over an odd cycle is not bipartite. -/
@[simp] theorem not_isBipartite_prism_odd (m : ℕ) : ¬ IsBipartite (prism (2 * m + 3)) := by
  show ¬ IsBipartite (cycle (2 * m + 3) □g complete 2)
  rw [isBipartite_cartesianProduct_iff (by simp) (by simp)]
  exact fun h ↦ not_isBipartite_cycle_odd m h.1

attribute [simp] IsoGraph.not_isBipartite_kneser IsoGraph.not_isBipartite_johnson

/-- Triangular graphs on at least four points contain a triangle. -/
theorem not_isBipartite_triangular {n : ℕ} (h : 4 ≤ n) : ¬ IsBipartite (triangular n) :=
  not_isBipartite_johnson (by omega) (by omega)

/-- **The Petersen graph is not bipartite**: it is triangle-free, but it has a five-cycle. -/
@[simp] theorem not_isBipartite_petersen : ¬ IsBipartite petersen := by
  show ¬ IsBipartite (kneser 5 2)
  rw [kneser_def, isBipartite_mk]
  exact CGraph.not_isBipartite_kneser_five_two

/-- **Complete multipartite graphs with three nonempty parts are not bipartite.** -/
@[simp] theorem not_isBipartite_completeMultipartite (a b c : ℕ) (ds : List ℕ) :
    ¬ IsBipartite (completeMultipartite ((a + 1) :: (b + 1) :: (c + 1) :: ds)) := by
  rw [completeMultipartite_cons, completeMultipartite_cons, completeMultipartite_cons]
  exact not_isBipartite_join_join (by simp) (by simp) (by simp)

/-- Every page of a book meets the spine in a triangle. -/
@[simp] theorem not_isBipartite_book (n : ℕ) : ¬ IsBipartite (book (n + 1)) :=
  not_isBipartite_completeMultipartite 0 0 n []

/-- The cocktail party graph on three or more pairs is not bipartite. -/
@[simp] theorem not_isBipartite_cocktailParty (n : ℕ) : ¬ IsBipartite (cocktailParty (n + 3)) := by
  show ¬ IsBipartite (completeMultipartite (List.replicate (n + 3) 2))
  rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
  exact not_isBipartite_completeMultipartite 1 1 1 _

/-- The hub of a fan sees an edge of the path. -/
@[simp] theorem not_isBipartite_fan (n : ℕ) : ¬ IsBipartite (fan (n + 2)) := by
  show ¬ IsBipartite (complete 1 ∇g path (n + 2))
  rw [complete_def, path_def, join_mk, isBipartite_mk]
  refine CGraph.not_isBipartite_join_of_adj_right
    (a := (⟨0, by omega⟩ : (CGraph.path (n + 2)).V)) (b := ⟨1, by omega⟩) ?_ ⟨0, by omega⟩
  rw [CGraph.path_adj_val]
  exact ⟨by simp, Or.inl rfl⟩

theorem tensorProduct_complete_two_hypercube (n : ℕ) :
    complete 2 ⊗g hypercube n = hypercube n ⊕g hypercube n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_hypercube n)

theorem tensorProduct_complete_two_prism (m : ℕ) :
    complete 2 ⊗g prism (2 * m) = prism (2 * m) ⊕g prism (2 * m) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_prism_even m)

/-- **The double cover of a path is two paths.** -/
theorem tensorProduct_complete_two_path (n : ℕ) :
    complete 2 ⊗g path n = path n ⊕g path n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_path n)

/-- **The double cover of an even cycle is two cycles.** -/
theorem tensorProduct_complete_two_cycle (m : ℕ) :
    complete 2 ⊗g cycle (2 * m) = cycle (2 * m) ⊕g cycle (2 * m) :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_cycle_even m)

/-- **The double cover of a complete bipartite graph is two copies of it.** -/
theorem tensorProduct_complete_two_bipartite (m n : ℕ) :
    complete 2 ⊗g bipartite m n = bipartite m n ⊕g bipartite m n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_bipartite m n)

/-- The double cover of a star is two stars. -/
theorem tensorProduct_complete_two_star (n : ℕ) :
    complete 2 ⊗g star n = star n ⊕g star n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_star n)

/-- **The double cover of a ladder is two ladders.** -/
theorem tensorProduct_complete_two_ladder (n : ℕ) :
    complete 2 ⊗g ladder n = ladder n ⊕g ladder n :=
  tensorProduct_complete_two_of_isBipartite _ (isBipartite_ladder n)

/-! ### Independent sets and matchings in a path

A maximum matching leaves at least one endpoint of each of its edges out of any independent set,
so `α + ν ≤ τ + α = |V|`; in the other direction `|V| ≤ χ · α`.  For a path both bounds are
`⌈n/2⌉`, because the line graph of `P_{n+1}` is `P_n`, which turns the matching number into the
independence number one step down and makes the two estimates close a single induction. -/

/-- **The independence number of a path**: `α(Pₙ) = ⌈n/2⌉`. -/
@[simp] theorem indepNum_path (n : ℕ) : (path n).indepNum = (n + 1) / 2 := by
  induction n with
  | zero => rw [path_zero, indepNum_empty]
  | succ m ih =>
    cases m with
    | zero => rw [path_one, indepNum_empty]
    | succ k =>
      have hlow : k + 1 + 1 ≤ 2 * (path (k + 1 + 1)).indepNum := by
        have h := V_le_chromNum_mul_indepNum (path (k + 2))
        rw [V_path, chromNum_path] at h
        exact h
      have hnu : (path (k + 1 + 1)).matchNum = (k + 1 + 1) / 2 := by
        rw [matchNum_eq, lineGraph_path, ih]
      have hup := (path (k + 1 + 1)).matchNum_add_indepNum_le_V
      rw [V_path, hnu] at hup
      omega

/-- **The vertex cover number of a path**: `τ(Pₙ) = ⌊n/2⌋`, by Gallai. -/
@[simp] theorem coverNum_path (n : ℕ) : (path n).coverNum = n / 2 := by
  have h := (path n).coverNum_add_indepNum
  rw [V_path, indepNum_path] at h
  omega

/-- **The matching number of a path**: `ν(Pₙ) = ⌊n/2⌋`, since `L(P_{n+1}) = Pₙ`. -/
@[simp] theorem matchNum_path (n : ℕ) : (path n).matchNum = n / 2 := by
  cases n with
  | zero => rw [path_zero, matchNum_empty]
  | succ m => rw [matchNum_eq, lineGraph_path, indepNum_path]

/-- A path with an edge is bipartite, so its largest clique is an edge. -/
@[simp] theorem cliqueNum_path (n : ℕ) : (path (n + 2)).cliqueNum = 2 := by
  have h := chromNum_eq_cliqueNum_of_isBipartite (isBipartite_path (n + 2))
    (by rw [E_path]; omega)
  rw [chromNum_path] at h
  omega

/-- König's theorem for a path: the matching number and the cover number agree. -/
theorem matchNum_eq_coverNum_path (n : ℕ) : (path n).matchNum = (path n).coverNum := by
  rw [matchNum_path, coverNum_path]

/-- A path is covered by `⌈n/2⌉` cliques: take alternate edges. -/
@[simp] theorem cliqueCoverNum_path (n : ℕ) : (path n).cliqueCoverNum = (n + 1) / 2 := by
  apply le_antisymm
  · -- Upper bound: cliqueCoverNum (path n) ≤ (n+1)/2
    rw [cliqueCoverNum_eq]
    show chromNum (show IsoGraph from ⟦CGraph.path n⟧)ᶜ ≤ _
    rw [IsoGraph.compl_mk]
    rw [chromNum_mk]
    rw [CGraph.chromNum_le_iff_colorable]
    -- Coloring: vertex i gets color i/2
    -- In (path n)ᶜ, i and j are adjacent iff i ≠ j and not (path n).Adj i j
    -- i.e., i ≠ j and |i-j| ≠ 1. We need color i ≠ color j, i.e., i/2 ≠ j/2.
    -- If i/2 = j/2, then i and j are in {2k, 2k+1}, so |i-j| ≤ 1, contradiction.
    let k := (n + 1) / 2
    have hcoloring : ∀ i : Fin n, (i : ℕ) / 2 < k := by
      intro i
      have : (i : ℕ) < n := i.is_lt
      omega
    let color : (CGraph.path n).V → Fin k := fun i => ⟨i.val / 2, hcoloring i⟩
    have hvalid : ∀ i j, (CGraph.path n)ᶜ.toSimple.Adj i j → color i ≠ color j := by
      intro i j hij
      simp [CGraph.compl_toSimple] at hij
      -- hij : ¬i = j ∧ ¬(SimpleGraph.pathGraph n).Adj i j
      by_contra hne
      rw [SimpleGraph.pathGraph_adj] at hij
      -- hij.2 : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)
      -- hne : color i = color j, i.e., i.val / 2 = j.val / 2
      have hne' : (i.val : ℕ) ≠ (j.val : ℕ) := by
        intro h; exact hij.1 (Fin.ext h)
      have hquot : (i.val : ℕ) / 2 = (j.val : ℕ) / 2 := Fin.ext_iff.mp hne
      have hi2 := Nat.div_add_mod (i.val : ℕ) 2
      have hj2 := Nat.div_add_mod (j.val : ℕ) 2
      have himod := Nat.mod_lt (i.val : ℕ) (by omega : 0 < (2 : ℕ))
      have hjmod := Nat.mod_lt (j.val : ℕ) (by omega : 0 < (2 : ℕ))
      exact hij.2 (by omega)
    refine ⟨color, fun hij => ?_⟩
    simp [SimpleGraph.completeGraph]
    exact hvalid _ _ hij
  · -- Lower bound
    calc (n + 1) / 2 = (path n).indepNum := (indepNum_path n).symm
      _ ≤ (path n).cliqueCoverNum := indepNum_le_cliqueCoverNum _

/-- **A torus is a product of two cycles**, and has girth four once both are long enough. -/
@[simp] theorem girth_cartesianProduct_cycle (m n : ℕ) :
    (cycle (m + 4) □g cycle (n + 4)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ ?_ (by rw [cliqueNum_cycle])
    (by rw [cliqueNum_cycle]) <;>
  · rw [show _ + 4 = _ + 1 + 3 from rfl, E_cycle]
    omega

/-- A cycle crossed with a path: the girth is four whichever parity the cycle has. -/
@[simp] theorem girth_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 4) □g path (n + 2)).girth = 4 := by
  refine girth_cartesianProduct_of_cliqueNum_le_two ?_ (by simp) (by rw [cliqueNum_cycle])
    (by rw [cliqueNum_path])
  rw [show m + 4 = m + 1 + 3 by ring, E_cycle]
  omega

/-! ### Counting triangles in the triangle-free families

`cliqueCount G 3` is the number of triangles.  It vanishes exactly when the girth is not three,
and in particular whenever the graph is bipartite or its clique number is at most two — two
conditions the library already knows for most of its families.
-/

@[simp] theorem cliqueCount_path (n : ℕ) : (path n).cliqueCount 3 = 0 :=
  cliqueCount_three_eq_zero_of_isBipartite (isBipartite_path n)

theorem chromNum_compl_path (n : ℕ) : ((path n)ᶜ).chromNum = (n + 1) / 2 := by
  rw [chromNum_compl, cliqueCoverNum_path]

/-! ### The cylinder and the king graph -/

theorem cliqueNum_cartesianProduct_cycle_path (m n : ℕ) :
    (cycle (m + 4) □g path (n + 2)).cliqueNum = 2 := by
  have h := cliqueNum_cartesianProduct (G := cycle (m + 4)) (H := path (n + 2))
    (by rw [V_cycle]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_cycle, cliqueNum_path] at h
  omega

@[simp] theorem isBipartite_tensorProduct_path (m n : ℕ) :
    IsBipartite (path m ⊗g path n) :=
  isBipartite_tensorProduct_left (isBipartite_path m)

@[simp] theorem chromNum_tensorProduct_path (m n : ℕ) :
    (path (m + 2) ⊗g path (n + 2)).chromNum = 2 :=
  chromNum_eq_two_iff.2 ⟨isBipartite_tensorProduct_path _ _,
    by rw [E_tensorProduct, E_path, E_path]; positivity⟩

theorem chromNum_lexProduct_path (m n : ℕ) :
    (path (m + 2) ·g path (n + 2)).chromNum = 4 := by
  have h1 := chromNum_lexProduct_le (path (m + 2)) (path (n + 2))
  have h2 := cliqueNum_le_chromNum (path (m + 2) ·g path (n + 2))
  rw [chromNum_path, chromNum_path] at h1
  rw [cliqueNum_lexProduct, cliqueNum_path, cliqueNum_path] at h2
  omega

@[simp] theorem girth_join_path (m n : ℕ) :
    (path (m + 2) ∇g path (n + 2)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_path, cliqueNum_path]; omega)

theorem diameter_join_path (m n : ℕ) :
    (path (m + 3) ∇g path (n + 3)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_path]; omega) ?_
  rw [E_path, V_path, h]
  omega

theorem indepNum_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 4) □g path (n + 2))ᶜ).indepNum = 2 := by
  rw [indepNum_compl, cliqueNum_cartesianProduct_cycle_path]

theorem cliqueCoverNum_compl_disjUnion_cycle_even_odd (m n : ℕ) :
    ((cycle (2 * m + 2) ⊕g cycle (2 * n + 3))ᶜ).cliqueCoverNum = 3 := by
  rw [cliqueCoverNum_compl, chromNum_disjUnion_cycle_even_odd]

theorem cliqueCoverNum_compl_lexProduct_path (m n : ℕ) :
    ((path (m + 2) ·g path (n + 2))ᶜ).cliqueCoverNum = 4 := by
  rw [cliqueCoverNum_compl, chromNum_lexProduct_path]

/-! ### Girth and connectivity of complements -/

theorem girth_compl_cycle (n : ℕ) : ((cycle (n + 6))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_cycle]; omega)

theorem girth_compl_path (n : ℕ) : ((path (n + 5))ᶜ).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_compl, indepNum_path]; omega)

/-! ### Vertex cover numbers of complements -/

@[simp] theorem coverNum_compl_eq (G : IsoGraph) : Gᶜ.coverNum = G.V - G.cliqueNum := by
  have h := coverNum_compl_add_cliqueNum G
  omega

theorem coverNum_compl_disjUnion (G H : IsoGraph) :
    ((G ⊕g H)ᶜ).coverNum = G.V + H.V - max G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_disjUnion, cliqueNum_disjUnion]

theorem coverNum_compl_join (G H : IsoGraph) :
    ((G ∇g H)ᶜ).coverNum = G.V + H.V - (G.cliqueNum + H.cliqueNum) := by
  rw [coverNum_compl_eq, V_join, cliqueNum_join]

theorem coverNum_compl_strongProduct (G H : IsoGraph) :
    ((G ⊠g H)ᶜ).coverNum = G.V * H.V - G.cliqueNum * H.cliqueNum := by
  rw [coverNum_compl_eq, V_strongProduct, cliqueNum_strongProduct]

theorem coverNum_compl_tensorProduct (G H : IsoGraph) :
    ((G ⊗g H)ᶜ).coverNum = G.V * H.V - min G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_tensorProduct, cliqueNum_tensorProduct]

theorem coverNum_compl_cartesianProduct {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    ((G □g H)ᶜ).coverNum = G.V * H.V - max G.cliqueNum H.cliqueNum := by
  rw [coverNum_compl_eq, V_cartesianProduct, cliqueNum_cartesianProduct hG hH]

theorem coverNum_compl_mycielskian (G : IsoGraph) (hV : 0 < G.V) :
    ((mycielskian G)ᶜ).coverNum = 2 * G.V + 1 - max G.cliqueNum 2 := by
  rw [coverNum_compl_eq, V_mycielskian, cliqueNum_mycielskian G hV]

theorem coverNum_compl_lineGraph (G : IsoGraph) (h : 3 ≤ maxDeg G) :
    ((lineGraph G)ᶜ).coverNum = G.E - maxDeg G := by
  rw [coverNum_compl_eq, V_lineGraph, cliqueNum_lineGraph_of_three_le_maxDeg h]

theorem coverNum_compl_empty (n : ℕ) : ((empty n)ᶜ).coverNum = n - min n 1 := by
  have h := coverNum_compl_add_cliqueNum (empty n)
  rw [cliqueNum_empty, V_empty] at h
  omega

theorem coverNum_compl_cycle (n : ℕ) : ((cycle (n + 4))ᶜ).coverNum = n + 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (n + 4))
  rw [cliqueNum_cycle, V_cycle] at h
  omega

theorem coverNum_compl_cycle_three : ((cycle 3)ᶜ).coverNum = 0 := by
  have h := coverNum_compl_add_cliqueNum (cycle 3)
  rw [cliqueNum_cycle_three, V_cycle] at h
  omega

theorem coverNum_compl_path (n : ℕ) : ((path (n + 2))ᶜ).coverNum = n := by
  have h := coverNum_compl_add_cliqueNum (path (n + 2))
  rw [cliqueNum_path, V_path] at h
  omega

theorem coverNum_compl_cartesianProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) □g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) □g cycle (n + 4))
  rw [cliqueNum_cartesianProduct_cycle, V_cartesianProduct, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_cartesianProduct_cycle_path (m n : ℕ) :
    ((cycle (m + 4) □g path (n + 2))ᶜ).coverNum = (m + 4) * (n + 2) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) □g path (n + 2))
  rw [cliqueNum_cartesianProduct_cycle_path, V_cartesianProduct, V_cycle, V_path] at h
  omega

theorem coverNum_compl_tensorProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊗g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 2 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊗g cycle (n + 4))
  rw [cliqueNum_tensorProduct, cliqueNum_cycle, cliqueNum_cycle, V_tensorProduct, V_cycle,
      V_cycle] at h
  omega

theorem coverNum_compl_tensorProduct_path (m n : ℕ) :
    ((path (m + 2) ⊗g path (n + 2))ᶜ).coverNum = (m + 2) * (n + 2) - 2 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ⊗g path (n + 2))
  rw [cliqueNum_tensorProduct, cliqueNum_path, cliqueNum_path, V_tensorProduct, V_path, V_path] at h
  omega

theorem coverNum_compl_strongProduct_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊠g cycle (n + 4))ᶜ).coverNum = (m + 4) * (n + 4) - 4 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊠g cycle (n + 4))
  rw [cliqueNum_strongProduct, cliqueNum_cycle, cliqueNum_cycle, V_strongProduct, V_cycle,
      V_cycle] at h
  omega

theorem coverNum_compl_disjUnion_cycle (m n : ℕ) :
    ((cycle (m + 4) ⊕g cycle (n + 4))ᶜ).coverNum = m + n + 6 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ⊕g cycle (n + 4))
  rw [cliqueNum_disjUnion, cliqueNum_cycle, cliqueNum_cycle, V_disjUnion, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_disjUnion_path (m n : ℕ) :
    ((path (m + 2) ⊕g path (n + 2))ᶜ).coverNum = m + n + 2 := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ⊕g path (n + 2))
  rw [cliqueNum_disjUnion, cliqueNum_path, cliqueNum_path, V_disjUnion, V_path, V_path] at h
  omega

theorem coverNum_compl_join_cycle (m n : ℕ) :
    ((cycle (m + 4) ∇g cycle (n + 4))ᶜ).coverNum = m + n + 4 := by
  have h := coverNum_compl_add_cliqueNum (cycle (m + 4) ∇g cycle (n + 4))
  rw [cliqueNum_join, cliqueNum_cycle, cliqueNum_cycle, V_join, V_cycle, V_cycle] at h
  omega

theorem coverNum_compl_join_path (m n : ℕ) :
    ((path (m + 2) ∇g path (n + 2))ᶜ).coverNum = m + n := by
  have h := coverNum_compl_add_cliqueNum (path (m + 2) ∇g path (n + 2))
  rw [cliqueNum_join, cliqueNum_path, cliqueNum_path, V_join, V_path, V_path] at h
  omega

/-! ### Perfect factors in the tensor and lexicographic products -/

/-- The tensor product projects onto either factor, so `χ(G ⊗ H) ≤ min χ(G) χ(H)`, while its
clique number is `min ω(G) ω(H)`; when both factors have `χ = ω` the two bounds meet. -/
theorem chromNum_tensorProduct_of_chromNum_eq_cliqueNum {G H : IsoGraph}
    (hG : G.chromNum = G.cliqueNum) (hH : H.chromNum = H.cliqueNum) :
    (G ⊗g H).chromNum = min G.cliqueNum H.cliqueNum := by
  have h1 := chromNum_tensorProduct_le G H
  have h2 := cliqueNum_le_chromNum (G ⊗g H)
  rw [cliqueNum_tensorProduct] at h2
  rw [hG, hH] at h1
  omega

theorem chromNum_eq_cliqueNum_path (n : ℕ) :
    (path (n + 2)).chromNum = (path (n + 2)).cliqueNum := by
  rw [chromNum_path, cliqueNum_path]

theorem chromNum_eq_cliqueNum_complete (n : ℕ) :
    (complete n).chromNum = (complete n).cliqueNum := by
  rw [chromNum_complete, cliqueNum_complete]

theorem chromNum_tensorProduct_complete (m n : ℕ) :
    (complete m ⊗g complete n).chromNum = min m n := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_complete n)
  rwa [cliqueNum_complete, cliqueNum_complete] at h

theorem chromNum_tensorProduct_cycle_even (m n : ℕ) :
    (cycle (2 * m + 4) ⊗g cycle (2 * n + 4)).chromNum = 2 := by
  have h := chromNum_tensorProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_cycle_even m) (chromNum_eq_cliqueNum_cycle_even n)
  rw [cliqueNum_cycle, cliqueNum_cycle] at h
  omega

/-! ### The cartesian product of a complete graph with a path -/

theorem cliqueNum_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 2)).cliqueNum = m + 2 := by
  have h := cliqueNum_cartesianProduct (G := complete (m + 2)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [cliqueNum_complete, cliqueNum_path] at h
  omega

theorem chromNum_cartesianProduct_complete_path (m n : ℕ) :
    (complete (m + 2) □g path (n + 2)).chromNum = m + 2 := by
  have h := chromNum_cartesianProduct (G := complete (m + 2)) (H := path (n + 2))
    (by rw [V_complete]; omega) (by rw [V_path]; omega)
  rw [chromNum_complete, chromNum_path] at h
  omega

/-! ### More colourings of the strong and lexicographic products -/

theorem chromNum_lexProduct_complete_cycle_even (m n : ℕ) :
    (complete m ·g cycle (2 * n + 4)).chromNum = m * 2 := by
  have h := chromNum_lexProduct_of_chromNum_eq_cliqueNum
    (chromNum_eq_cliqueNum_complete m) (chromNum_eq_cliqueNum_cycle_even n)
  rwa [cliqueNum_complete, cliqueNum_cycle] at h

@[simp] theorem girth_join_path_cycle (m n : ℕ) :
    (path (m + 2) ∇g cycle (n + 4)).girth = 3 :=
  girth_eq_three_of_cliqueNum (by rw [cliqueNum_join, cliqueNum_path, cliqueNum_cycle]; omega)

theorem diameter_join_path_cycle (m n : ℕ) :
    (path (m + 3) ∇g cycle (n + 1)).diameter = 2 := by
  have h : (m + 3).choose 2 = (m + 3) * (m + 2) / 2 := by
    rw [Nat.choose_two_right, show m + 3 - 1 = m + 2 by omega]
  have h2 : m + 3 ≤ (m + 3) * (m + 2) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have e : (m + 3) * (m + 2) = m * m + 5 * m + 6 := by ring
    omega
  refine diameter_join_left (by rw [V_cycle]; omega) ?_
  rw [E_path, V_path, h]
  omega

theorem cliqueNum_mycielskian_path (m : ℕ) :
    (mycielskian (path (m + 2))).cliqueNum = 2 := by
  have h := cliqueNum_mycielskian (path (m + 2)) (by rw [V_path]; omega)
  rw [cliqueNum_path] at h
  omega

/-! ### The join of a path and a complete graph -/

theorem cliqueCoverNum_join_path_complete (m n : ℕ) :
    (path (m + 1) ∇g complete (n + 1)).cliqueCoverNum = (m + 2) / 2 := by
  have h := cliqueCoverNum_join (path (m + 1)) (complete (n + 1))
  rw [cliqueCoverNum_path, cliqueCoverNum_complete] at h
  omega

end IsoGraph

/-! ### Counting the independent sets of a path and of a cycle

An independent set of `path n` is a set of labels below `n` with no two consecutive, and one of
`cycle n` is such a set that in addition does not use both ends at once.  Counting those subsets
is Pascal's rule with a shift — delete the largest label and what is left is a sparse subset of a
shorter interval — which gives `(n + 1 - k).choose k` independent `k`-sets in a path.  A cycle
splits according to whether the label `0` is used, and so counts two paths.
-/

namespace CGraph

/-- The `k`-element subsets of `{0, …, n-1}` that contain no two consecutive numbers. -/
private def sparseFinsets (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range n).powersetCard k).filter fun s ↦ ∀ i ∈ s, i + 1 ∉ s

private theorem mem_sparseFinsets {n k : ℕ} {s : Finset ℕ} :
    s ∈ sparseFinsets n k ↔ (s ⊆ Finset.range n ∧ s.card = k) ∧ ∀ i ∈ s, i + 1 ∉ s := by
  simp [sparseFinsets, Finset.mem_powersetCard]

private theorem sparseFinsets_eq_empty {n k : ℕ} (h : n < k) : sparseFinsets n k = ∅ := by
  rw [sparseFinsets, Finset.powersetCard_eq_empty.2 (by rwa [Finset.card_range]),
    Finset.filter_empty]

private theorem card_sparseFinsets_zero (n : ℕ) : (sparseFinsets n 0).card = 1 := by
  have h : sparseFinsets n 0 = {∅} := by
    ext s
    rw [mem_sparseFinsets, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hcard⟩, -⟩
      exact Finset.card_eq_zero.1 hcard
    · rintro rfl
      simp
  rw [h, Finset.card_singleton]

private theorem card_sparseFinsets_one (n : ℕ) : (sparseFinsets n 1).card = n := by
  have h : sparseFinsets n 1 = (Finset.range n).powersetCard 1 := by
    rw [sparseFinsets, Finset.filter_eq_self]
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs.2
    simp
  rw [h, Finset.card_powersetCard, Finset.card_range, Nat.choose_one_right]

/-- Pascal's rule for sparse subsets: split on whether the last available number is used. -/
private theorem card_sparseFinsets_succ (n k : ℕ) :
    (sparseFinsets (n + 2) (k + 1)).card
      = (sparseFinsets (n + 1) (k + 1)).card + (sparseFinsets n k).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := sparseFinsets (n + 2) (k + 1)) (p := fun s ↦ n + 1 ∈ s)
  have h1 : ((sparseFinsets (n + 2) (k + 1)).filter fun s ↦ n + 1 ∈ s).card
      = (sparseFinsets n k).card := by
    refine Finset.card_bij (fun s _ ↦ s.erase (n + 1)) ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_filter, mem_sparseFinsets] at hs
      obtain ⟨⟨⟨hsub, hcard⟩, hsp⟩, hmem⟩ := hs
      rw [mem_sparseFinsets]
      refine ⟨⟨fun i hi ↦ ?_, ?_⟩, fun i hi ↦ ?_⟩
      · rw [Finset.mem_erase] at hi
        have hlt := Finset.mem_range.1 (hsub hi.2)
        have hne : i ≠ n := by
          rintro rfl
          exact hsp i hi.2 hmem
        rw [Finset.mem_range]
        omega
      · rw [Finset.card_erase_of_mem hmem, hcard]
        omega
      · rw [Finset.mem_erase] at hi ⊢
        exact fun h ↦ hsp i hi.2 h.2
    · intro s hs t ht hst
      rw [Finset.mem_filter] at hs ht
      rw [← Finset.insert_erase hs.2, ← Finset.insert_erase ht.2, hst]
    · intro t ht
      rw [mem_sparseFinsets] at ht
      obtain ⟨⟨hsub, hcard⟩, hsp⟩ := ht
      have hnot : n + 1 ∉ t := fun h ↦ by
        have := Finset.mem_range.1 (hsub h)
        omega
      refine ⟨insert (n + 1) t, ?_, Finset.erase_insert hnot⟩
      rw [Finset.mem_filter, mem_sparseFinsets]
      refine ⟨⟨⟨fun i hi ↦ ?_, ?_⟩, fun i hi ↦ ?_⟩, Finset.mem_insert_self _ _⟩
      · rw [Finset.mem_insert] at hi
        rw [Finset.mem_range]
        rcases hi with rfl | hi
        · omega
        · have := Finset.mem_range.1 (hsub hi)
          omega
      · rw [Finset.card_insert_of_notMem hnot, hcard]
      · rw [Finset.mem_insert] at hi ⊢
        rcases hi with rfl | hi
        · rintro (h | h)
          · omega
          · have := Finset.mem_range.1 (hsub h)
            omega
        · have hlt := Finset.mem_range.1 (hsub hi)
          rintro (h | h)
          · omega
          · exact hsp i hi h
  have h2 : ((sparseFinsets (n + 2) (k + 1)).filter fun s ↦ ¬ (n + 1 ∈ s)).card
      = (sparseFinsets (n + 1) (k + 1)).card := by
    congr 1
    ext s
    rw [Finset.mem_filter, mem_sparseFinsets, mem_sparseFinsets]
    constructor
    · rintro ⟨⟨⟨hsub, hcard⟩, hsp⟩, hmem⟩
      refine ⟨⟨fun i hi ↦ ?_, hcard⟩, hsp⟩
      have hlt := Finset.mem_range.1 (hsub hi)
      have hne : i ≠ n + 1 := by rintro rfl; exact hmem hi
      rw [Finset.mem_range]
      omega
    · rintro ⟨⟨hsub, hcard⟩, hsp⟩
      refine ⟨⟨⟨fun i hi ↦ ?_, hcard⟩, hsp⟩, fun h ↦ ?_⟩
      · have := Finset.mem_range.1 (hsub hi)
        rw [Finset.mem_range]
        omega
      · have := Finset.mem_range.1 (hsub h)
        omega
  omega

private theorem card_sparseFinsets (n k : ℕ) :
    (sparseFinsets n k).card = (n + 1 - k).choose k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases k with _ | k
    · rw [card_sparseFinsets_zero]
      simp
    rcases n with _ | _ | n
    · rw [sparseFinsets_eq_empty (by omega), Finset.card_empty,
        show 0 + 1 - (k + 1) = 0 from by omega, Nat.choose_eq_zero_of_lt (by omega)]
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [card_sparseFinsets_one]
        simp
      · rw [sparseFinsets_eq_empty (by omega), Finset.card_empty,
          show 1 + 1 - (k + 1) = 0 from by omega, Nat.choose_eq_zero_of_lt (by omega)]
    · rw [card_sparseFinsets_succ, ih (n + 1) (by omega), ih n (by omega)]
      by_cases h : k ≤ n + 1
      · rw [show n + 1 + 1 + 1 - (k + 1) = (n + 1 - k) + 1 from by omega,
          show n + 1 + 1 - (k + 1) = n + 1 - k from by omega, Nat.choose_succ_succ']
        omega
      · rw [show n + 1 + 1 + 1 - (k + 1) = 0 from by omega,
          show n + 1 + 1 - (k + 1) = 0 from by omega, show n + 1 - k = 0 from by omega,
          Nat.choose_eq_zero_of_lt (show 0 < k from by omega)]
        omega

/-- **The independent sets of a path are the sparse subsets of an interval.**  Choosing `k`
vertices of `path n` with no two adjacent is the same as choosing `k` naturals below `n` with no
two consecutive, and there are `(n + 1 - k).choose k` of those. -/
@[simp, toIsoGraph]
theorem indepCount_path (n k : ℕ) : (path n).indepCount k = (n + 1 - k).choose k := by
  classical
  rw [indepCount_eq_card_indepSetFinset, ← card_sparseFinsets n k]
  refine Finset.card_bij (fun s _ ↦ Finset.image (Fin.val : Fin n → ℕ) s) ?_ ?_ ?_
  · intro s hs
    rw [SimpleGraph.mem_indepSetFinset_iff] at hs
    rw [mem_sparseFinsets]
    refine ⟨⟨fun i hi ↦ ?_, ?_⟩, fun i hi hi' ↦ ?_⟩
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 v.2
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hs.card_eq]
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨v, hv, huv⟩ := Finset.mem_image.1 hi'
      refine hs.isIndepSet (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) (fun h ↦ ?_) ?_
      · rw [h] at huv
        omega
      · rw [CGraph.toSimple_adj]
        exact (path_adj_val n u v).2 ⟨by omega, Or.inl huv.symm⟩
  · intro s _ t _ hst
    exact Finset.image_injective Fin.val_injective hst
  · intro t ht
    rw [mem_sparseFinsets] at ht
    obtain ⟨⟨hsub, hcard⟩, hsp⟩ := ht
    have hlt : ∀ m ∈ t, m < n := fun m hm ↦ Finset.mem_range.1 (hsub hm)
    refine ⟨t.attachFin hlt, ?_, Finset.image_val_attachFin hlt⟩
    rw [SimpleGraph.mem_indepSetFinset_iff]
    refine ⟨fun u hu v hv _ ↦ ?_, by rw [Finset.card_attachFin, hcard]⟩
    rw [Finset.mem_coe, Finset.mem_attachFin] at hu hv
    rw [CGraph.toSimple_adj, path_adj_val]
    rintro ⟨-, h | h⟩
    · exact hsp u.1 hu (by rw [h]; exact hv)
    · exact hsp v.1 hv (by rw [h]; exact hu)

/-- The `k`-element subsets of `{0, …, N-1}` with no two consecutive numbers and not both ends:
the independent sets of a cycle, read off the labels. -/
private def cyclicSparseFinsets (N k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range N).powersetCard k).filter
    fun s ↦ (∀ i ∈ s, i + 1 ∉ s) ∧ ¬ (0 ∈ s ∧ N - 1 ∈ s)

private theorem mem_cyclicSparseFinsets {N k : ℕ} {s : Finset ℕ} :
    s ∈ cyclicSparseFinsets N k ↔
      (s ⊆ Finset.range N ∧ s.card = k) ∧ (∀ i ∈ s, i + 1 ∉ s) ∧ ¬ (0 ∈ s ∧ N - 1 ∈ s) := by
  rw [cyclicSparseFinsets, Finset.mem_filter, Finset.mem_powersetCard]

/-- Splitting on the label `0`: an independent set of the cycle either misses it, and is a sparse
subset of the remaining path, or contains it, and is `0` beside a sparse subset of the path two
steps in from either end. -/
private theorem card_cyclicSparseFinsets (n k : ℕ) :
    (cyclicSparseFinsets (n + 3) (k + 1)).card
      = (sparseFinsets (n + 2) (k + 1)).card + (sparseFinsets n k).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := cyclicSparseFinsets (n + 3) (k + 1)) (p := fun s ↦ (0 : ℕ) ∈ s)
  have hpos : ∀ s ∈ (cyclicSparseFinsets (n + 3) (k + 1)).filter fun s ↦ ¬ (0 : ℕ) ∈ s,
      ∀ i ∈ s, 1 ≤ i := by
    intro s hs i hi
    rw [Finset.mem_filter] at hs
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd hi hs.2
    · exact h
  have hmid : ∀ s ∈ (cyclicSparseFinsets (n + 3) (k + 1)).filter fun s ↦ (0 : ℕ) ∈ s,
      ∀ i ∈ s.erase 0, 2 ≤ i ∧ i ≤ n + 1 := by
    intro s hs i hi
    rw [Finset.mem_filter, mem_cyclicSparseFinsets] at hs
    obtain ⟨⟨⟨hsub, -⟩, hsp, hwrap⟩, h0s⟩ := hs
    rw [show n + 3 - 1 = n + 2 from by omega] at hwrap
    rw [Finset.mem_erase] at hi
    have hlt := Finset.mem_range.1 (hsub hi.2)
    have hne1 : i ≠ 1 := fun h ↦ hsp 0 h0s (by rw [show (0 : ℕ) + 1 = i from by omega]; exact hi.2)
    have hne2 : i ≠ n + 2 := fun h ↦ hwrap ⟨h0s, by rw [← h]; exact hi.2⟩
    have hne0 := hi.1
    omega
  have h0 : ((cyclicSparseFinsets (n + 3) (k + 1)).filter fun s ↦ ¬ (0 : ℕ) ∈ s).card
      = (sparseFinsets (n + 2) (k + 1)).card := by
    refine Finset.card_bij' (fun s _ ↦ s.image (· - 1)) (fun t _ ↦ t.image (· + 1)) ?_ ?_ ?_ ?_
    · intro s hs
      have h1 := hpos s hs
      rw [Finset.mem_filter, mem_cyclicSparseFinsets] at hs
      obtain ⟨⟨⟨hsub, hcard⟩, hsp, -⟩, -⟩ := hs
      rw [mem_sparseFinsets]
      refine ⟨⟨fun x hx ↦ ?_, ?_⟩, fun x hx hx' ↦ ?_⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        have := Finset.mem_range.1 (hsub hy)
        rw [Finset.mem_range]
        omega
      · have hinj : Set.InjOn (fun x ↦ x - 1) (s : Set ℕ) := by
          intro a ha b hb hab
          simp only at hab
          have := h1 a (Finset.mem_coe.1 ha)
          have := h1 b (Finset.mem_coe.1 hb)
          omega
        rw [Finset.card_image_of_injOn hinj, hcard]
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨z, hz, hz'⟩ := Finset.mem_image.1 hx'
        have := h1 y hy
        have := h1 z hz
        exact hsp y hy (by rw [show y + 1 = z from by omega]; exact hz)
    · intro t ht
      rw [mem_sparseFinsets] at ht
      obtain ⟨⟨hsub, hcard⟩, hsp⟩ := ht
      rw [Finset.mem_filter, mem_cyclicSparseFinsets]
      refine ⟨⟨⟨fun x hx ↦ ?_, ?_⟩, fun x hx hx' ↦ ?_, fun hc ↦ ?_⟩, fun hc ↦ ?_⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        have := Finset.mem_range.1 (hsub hy)
        rw [Finset.mem_range]
        omega
      · rw [Finset.card_image_of_injective _ (add_left_injective 1), hcard]
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨z, hz, hz'⟩ := Finset.mem_image.1 hx'
        exact hsp y hy (by rw [show y + 1 = z from by omega]; exact hz)
      · obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hc.1
        omega
      · obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hc
        omega
    · intro s hs
      have h1 := hpos s hs
      ext x
      simp only [Finset.image_image, Finset.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have := h1 y hy
        rwa [show y - 1 + 1 = y from by omega]
      · intro hx
        exact ⟨x, hx, by have := h1 x hx; omega⟩
    · intro t ht
      ext x
      simp only [Finset.image_image, Finset.mem_image, Function.comp_apply, Nat.add_sub_cancel]
      exact ⟨fun ⟨y, hy, hxy⟩ ↦ hxy ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have h1 : ((cyclicSparseFinsets (n + 3) (k + 1)).filter fun s ↦ (0 : ℕ) ∈ s).card
      = (sparseFinsets n k).card := by
    refine Finset.card_bij' (fun s _ ↦ (s.erase 0).image (· - 2))
      (fun t _ ↦ insert 0 (t.image (· + 2))) ?_ ?_ ?_ ?_
    · intro s hs
      have hr := hmid s hs
      rw [Finset.mem_filter, mem_cyclicSparseFinsets] at hs
      obtain ⟨⟨⟨hsub, hcard⟩, hsp, -⟩, h0s⟩ := hs
      rw [mem_sparseFinsets]
      refine ⟨⟨fun x hx ↦ ?_, ?_⟩, fun x hx hx' ↦ ?_⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        have := hr y hy
        rw [Finset.mem_range]
        omega
      · have hinj : Set.InjOn (fun x ↦ x - 2) ((s.erase 0 : Finset ℕ) : Set ℕ) := by
          intro a ha b hb hab
          simp only at hab
          have := hr a (Finset.mem_coe.1 ha)
          have := hr b (Finset.mem_coe.1 hb)
          omega
        rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem h0s, hcard]
        omega
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨z, hz, hz'⟩ := Finset.mem_image.1 hx'
        have hy2 := hr y hy
        have hz2 := hr z hz
        rw [Finset.mem_erase] at hy hz
        exact hsp y hy.2 (by rw [show y + 1 = z from by omega]; exact hz.2)
    · intro t ht
      rw [mem_sparseFinsets] at ht
      obtain ⟨⟨hsub, hcard⟩, hsp⟩ := ht
      have hnot : (0 : ℕ) ∉ t.image (· + 2) := by
        intro h
        obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
        omega
      rw [Finset.mem_filter, mem_cyclicSparseFinsets]
      refine ⟨⟨⟨fun x hx ↦ ?_, ?_⟩, fun x hx hx' ↦ ?_, fun hc ↦ ?_⟩, Finset.mem_insert_self _ _⟩
      · rw [Finset.mem_range]
        rcases Finset.mem_insert.1 hx with rfl | hx
        · omega
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          have := Finset.mem_range.1 (hsub hy)
          omega
      · rw [Finset.card_insert_of_notMem hnot,
          Finset.card_image_of_injective _ (add_left_injective 2), hcard]
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · rcases Finset.mem_insert.1 hx' with h | h
          · omega
          · obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
            omega
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
          rcases Finset.mem_insert.1 hx' with h | h
          · omega
          · obtain ⟨z, hz, hz'⟩ := Finset.mem_image.1 h
            exact hsp y hy (by rw [show y + 1 = z from by omega]; exact hz)
      · obtain ⟨-, h⟩ := hc
        rcases Finset.mem_insert.1 h with h' | h'
        · omega
        · obtain ⟨y, hy, hy'⟩ := Finset.mem_image.1 h'
          have := Finset.mem_range.1 (hsub hy)
          omega
    · intro s hs
      have hr := hmid s hs
      have h0s : (0 : ℕ) ∈ s := (Finset.mem_filter.1 hs).2
      ext x
      simp only [Finset.image_image, Finset.mem_insert, Finset.mem_image, Function.comp_apply,
        Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · exact h0s
        · have := hr y (Finset.mem_erase.2 hy)
          rw [show y - 2 + 2 = y from by omega]
          exact hy.2
      · intro hx
        rcases Nat.eq_zero_or_pos x with rfl | hxpos
        · exact Or.inl rfl
        · refine Or.inr ⟨x, ⟨by omega, hx⟩, ?_⟩
          have := hr x (Finset.mem_erase.2 ⟨by omega, hx⟩)
          omega
    · intro t ht
      have hnot : (0 : ℕ) ∉ t.image (· + 2) := by
        intro h
        obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
        omega
      rw [Finset.erase_insert hnot]
      ext x
      simp only [Finset.image_image, Finset.mem_image, Function.comp_apply, Nat.add_sub_cancel]
      exact ⟨fun ⟨y, hy, hxy⟩ ↦ hxy ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩
  omega

private theorem card_indepSetFinset_cycle (n k : ℕ) :
    ((cycle (n + 3)).toSimple.indepSetFinset k).card
      = (cyclicSparseFinsets (n + 3) k).card := by
  classical
  refine Finset.card_bij (fun s _ ↦ Finset.image (Fin.val : Fin (n + 3) → ℕ) s) ?_ ?_ ?_
  · intro s hs
    rw [SimpleGraph.mem_indepSetFinset_iff] at hs
    rw [mem_cyclicSparseFinsets]
    refine ⟨⟨fun i hi ↦ ?_, ?_⟩, fun i hi hi' ↦ ?_, fun hc ↦ ?_⟩
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 v.2
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hs.card_eq]
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨v, hv, huv⟩ := Finset.mem_image.1 hi'
      have hv3 := v.2
      refine hs.isIndepSet (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) (fun h ↦ ?_) ?_
      · rw [h] at huv
        omega
      · rw [CGraph.toSimple_adj]
        refine (cycle_adj_val (n + 3) u v).2 ⟨by omega, Or.inl ?_⟩
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · obtain ⟨h0, hlast⟩ := hc
      obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h0
      obtain ⟨v, hv, hv'⟩ := Finset.mem_image.1 hlast
      refine hs.isIndepSet (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hu) (fun h ↦ ?_) ?_
      · rw [h] at hv'
        omega
      · rw [CGraph.toSimple_adj]
        refine (cycle_adj_val (n + 3) v u).2 ⟨by omega, Or.inl ?_⟩
        rw [show v.1 + 1 = n + 3 from by omega, Nat.mod_self]
        omega
  · intro s _ t _ hst
    exact Finset.image_injective Fin.val_injective hst
  · intro t ht
    rw [mem_cyclicSparseFinsets] at ht
    obtain ⟨⟨hsub, hcard⟩, hsp, hwrap⟩ := ht
    rw [show n + 3 - 1 = n + 2 from by omega] at hwrap
    have hlt : ∀ m ∈ t, m < n + 3 := fun m hm ↦ Finset.mem_range.1 (hsub hm)
    refine ⟨t.attachFin hlt, ?_, Finset.image_val_attachFin hlt⟩
    rw [SimpleGraph.mem_indepSetFinset_iff]
    refine ⟨fun u hu v hv _ ↦ ?_, by rw [Finset.card_attachFin, hcard]⟩
    rw [Finset.mem_coe, Finset.mem_attachFin] at hu hv
    have hu3 := u.2
    have hv3 := v.2
    rw [CGraph.toSimple_adj, cycle_adj_val]
    rintro ⟨-, h | h⟩
    · rcases Nat.lt_or_ge (u.1 + 1) (n + 3) with hlt' | hge
      · rw [Nat.mod_eq_of_lt hlt'] at h
        exact hsp u.1 hu (by rw [h]; exact hv)
      · rw [show u.1 + 1 = n + 3 from by omega, Nat.mod_self] at h
        exact hwrap ⟨by rw [h]; exact hv, by rw [show n + 2 = u.1 from by omega]; exact hu⟩
    · rcases Nat.lt_or_ge (v.1 + 1) (n + 3) with hlt' | hge
      · rw [Nat.mod_eq_of_lt hlt'] at h
        exact hsp v.1 hv (by rw [h]; exact hu)
      · rw [show v.1 + 1 = n + 3 from by omega, Nat.mod_self] at h
        exact hwrap ⟨by rw [h]; exact hu, by rw [show n + 2 = v.1 from by omega]; exact hv⟩

/-- **The independent sets of a cycle.**  Splitting on whether the set uses the label `0` counts
them as sparse subsets of two paths, one of `n + 2` labels and one of `n`. -/
@[simp, toIsoGraph]
theorem indepCount_cycle (n k : ℕ) :
    (cycle (n + 3)).indepCount (k + 1)
      = (n + 2 - k).choose (k + 1) + (n + 1 - k).choose k := by
  rw [indepCount_eq_card_indepSetFinset, card_indepSetFinset_cycle, card_cyclicSparseFinsets,
    card_sparseFinsets, card_sparseFinsets, show n + 2 + 1 - (k + 1) = n + 2 - k from by omega]

example : (path 5).indepCount 2 = 6 := by rw [indepCount_path]; decide
example : (cycle 5).indepCount 2 = 5 := by rw [indepCount_cycle]; decide

end CGraph
