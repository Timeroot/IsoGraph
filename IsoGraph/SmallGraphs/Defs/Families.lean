import IsoGraph.Core.Defs

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The parametrised families

Cayley graphs, and the parametrised families defined through them or through an explicit adjacency
relation: hypercubes and folded cubes, circulants, Kneser and Johnson graphs, Paley graphs, grids,
tori and king graphs, Turán, crown and cocktail party graphs.  Definitions only.

They sit between `Core.Defs` and `Core.Quotient` because the core constructions on isomorphism
classes are stated for them too.
-/

namespace CGraph

section
open Fintype

/-- The complete bipartite graph `K_{m,n}`: two independent sets with every edge across.

Written directly rather than as `(complete m ⊕g complete n)ᶜ`, which it also is —
`bipartite_eq_compl` — but which asks four vertex comparisons of an adjacency query where one
match settles it; see the note on `CGraph.join`, of which this is the edgeless case. -/
@[toIsoGraph]
def bipartite (m n : ℕ) : CGraph where
  V := Fin m ⊕ Fin n
  Adj x y :=
    match x, y with
    | .inl _, .inl _ => false
    | .inr _, .inr _ => false
    | _, _ => true
  symm x y := by cases x <;> cases y <;> rfl
  loopless x := by cases x <;> simp

instance (m n : ℕ) : Nonempty (bipartite (m + 1) n).V :=
  inferInstanceAs (Nonempty (Fin (m + 1) ⊕ Fin n))

theorem bipartite_eq_join (m n : ℕ) : bipartite m n = empty m ∇g empty n :=
  CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ by cases x <;> cases y <;> rfl))

theorem bipartite_eq_compl (m n : ℕ) : bipartite m n = (complete m ⊕g complete n)ᶜ :=
  (bipartite_eq_join m n).trans (join_eq_compl_disjUnion (empty m) (empty n))

@[simp] theorem card_bipartite (m n : ℕ) : FinEnum.card (bipartite m n).V = m + n := rfl

@[simp] theorem bipartite_adj_inl_inl (m n : ℕ) (a c : Fin m) :
    (bipartite m n).Adj (.inl a) (.inl c) = false := rfl

@[simp] theorem bipartite_adj_inr_inr (m n : ℕ) (b d : Fin n) :
    (bipartite m n).Adj (.inr b) (.inr d) = false := rfl

@[simp] theorem bipartite_adj_inl_inr (m n : ℕ) (a : Fin m) (d : Fin n) :
    (bipartite m n).Adj (.inl a) (.inr d) = true := rfl

@[simp] theorem bipartite_adj_inr_inl (m n : ℕ) (b : Fin n) (c : Fin m) :
    (bipartite m n).Adj (.inr b) (.inl c) = true := rfl

/-- The complete multipartite graph with parts of sizes `ds`: two vertices are adjacent exactly
when they lie in different parts.

Written directly rather than as the complement of the disjoint union of the parts —
`completeMultipartite_eq_compl` — because that form asks whether the two vertices are equal,
then whether they share a part, and then, if they do, whether they are equal again.  The part
indices answer on their own, and a Turán graph is queried a great many times. -/
@[toIsoGraph]
def completeMultipartite (ds : List ℕ) : CGraph where
  V := Σ i : Fin ds.length, (complete (ds.get i)).V
  Adj x y := decide (x.1 ≠ y.1)
  symm x y := by simp [ne_comm]
  loopless x := by simp

/-- Two vertices of a complete multipartite graph are adjacent exactly when they lie in
different parts. -/
theorem completeMultipartite_adj (ds : List ℕ)
    (x y : Σ i : Fin ds.length, (complete (ds.get i)).V) :
    (completeMultipartite ds).Adj x y = decide (x.1 ≠ y.1) := rfl

theorem completeMultipartite_eq_compl (ds : List ℕ) :
    completeMultipartite ds = (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))ᶜ := by
  refine CGraph.ext' rfl (heq_of_eq (funext fun x ↦ funext fun y ↦ ?_))
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  show decide (i ≠ j) = (decide (_ ≠ _) && !(sigmaUnion _).Adj _ _)
  by_cases h : i = j
  · subst h
    rw [sigmaUnion_adj_mk]
    by_cases hab : a = b <;> simp [complete, hab]
  · rw [sigmaUnion_adj_ne _ _ _ _ _ h]
    have hne : (⟨i, a⟩ : Σ i : Fin ds.length, (complete (ds.get i)).V) ≠ ⟨j, b⟩ :=
      fun hh ↦ h (congrArg Sigma.fst hh)
    simp [hne, h]

/-- The star with `n` leaves. -/
@[toIsoGraph]
def star (n : ℕ) : CGraph := bipartite 1 n

instance (n : ℕ) : Nonempty (star n).V := inferInstanceAs (Nonempty (bipartite (0 + 1) n).V)

/-- The wheel: a cycle plus a hub joined to all of it. -/
@[toIsoGraph]
def wheel (n : ℕ) : CGraph := complete 1 ∇g cycle n

/-- The theta graph: two poles joined by `xs.length` internally disjoint paths, the `i`-th of
which has `xs[i]` internal vertices (so `Θ(a,b,c)` in the usual notation is
`thetaGraph [a-1, b-1, c-1]`).  A `0` in the list contributes the single edge between the two
poles, so at most one `0` is meaningful. -/
@[toIsoGraph]
def thetaGraph (xs : List ℕ) : CGraph := ofEdges (2 + xs.sum) (thetaEdges 2 xs)

@[simp] theorem card_thetaGraph (xs : List ℕ) :
    FinEnum.card (thetaGraph xs).V = 2 + xs.sum := rfl

/-- The tadpole (or pan) graph `T(m,k)`: the cycle on `m` vertices with a path of `k` further
vertices attached to it.  `tadpole m 0` is `cycle m` and `tadpole 4 1` is the banner. -/
@[toIsoGraph]
def tadpole (m k : ℕ) : CGraph := ofEdges (m + k) (cycleEdges m ++ legEdges 0 m k)

@[simp] theorem card_tadpole (m k : ℕ) : FinEnum.card (tadpole m k).V = m + k := rfl

/-- The lollipop graph `L(m,k)`: `Kₘ` with a path of `k` further vertices attached to it. -/
@[toIsoGraph]
def lollipop (m k : ℕ) : CGraph := ofEdges (m + k) (cliqueEdges m ++ legEdges 0 m k)

@[simp] theorem card_lollipop (m k : ℕ) :
    FinEnum.card (lollipop m k).V = m + k := rfl

/-- The spider (or generalised star) `S(legs)`: a centre with paths of the given lengths hanging
off it.  `spider [1, 1, …, 1]` is a star and `spider [a, b]` is a path. -/
@[toIsoGraph]
def spider (legs : List ℕ) : CGraph := ofEdges (1 + legs.sum) (spiderEdges 1 legs)

@[simp] theorem card_spider (legs : List ℕ) :
    FinEnum.card (spider legs).V = 1 + legs.sum := rfl

/-- The double star `S(m,n)`: an edge with `m` pendant vertices on one end and `n` on the
other. -/
@[toIsoGraph]
def doubleStar (m n : ℕ) : CGraph :=
  ofEdges (2 + m + n) ((0, 1) :: (((List.range m).map fun i ↦ (0, 2 + i)) ++
    ((List.range n).map fun i ↦ (1, 2 + m + i))))

@[simp] theorem card_doubleStar (m n : ℕ) :
    FinEnum.card (doubleStar m n).V = 2 + m + n := rfl

/-- The cycle on `m` vertices with `ks[i]` pendant vertices attached to vertex `i`.  The paw is
`cyclePendant 3 [1]`, the bull is `cyclePendant 3 [1, 1]` and the net is
`cyclePendant 3 [1, 1, 1]`. -/
@[toIsoGraph]
def cyclePendant (m : ℕ) (ks : List ℕ) : CGraph :=
  ofEdges (m + ks.sum) (cycleEdges m ++ pendantEdges 0 m ks)

@[simp] theorem card_cyclePendant (m : ℕ) (ks : List ℕ) :
    FinEnum.card (cyclePendant m ks).V = m + ks.sum := rfl

/-! ## Cayley graphs

A group and a connection set.  `ofRel` symmetrises, so the connection set does *not* have to be
closed under negation — passing `S` and passing `S ∪ -S` give the same graph — and a `0 ∈ S` does
no harm either, since `ofRel` deletes the diagonal. -/

/-- The Cayley graph of a finite additive group `A` with connection set `S`: `x ~ y` when
`y - x ∈ S`.  Left translation is an automorphism, so this is always vertex-transitive. -/
def cayleyAdd (A : Type) [FinEnum A] [AddGroup A] (S : A → Bool) : CGraph :=
  ofRel A fun x y ↦ S (y - x)

@[simp] theorem cayleyAdd_adj (A : Type) [FinEnum A] [AddGroup A] (S : A → Bool)
    (x y : A) : (cayleyAdd A S).Adj x y = (decide (x ≠ y) && (S (y - x) || S (x - y))) := rfl

@[simp] theorem card_cayleyAdd (A : Type) [FinEnum A] [AddGroup A] (S : A → Bool) :
    FinEnum.card (cayleyAdd A S).V = FinEnum.card A := rfl

/-- The circulant on `Fin n` with connection set `S`, taken mod `n`: the Cayley graph of `ℤ/n`,
written on `Fin n` so that no `NeZero` instance is needed.  `cycle n = circulant n [1]`. -/
@[toIsoGraph]
def circulant (n : ℕ) (S : List ℕ) : CGraph :=
  ofRel (Fin n) fun x y ↦ S.contains ((y.1 + n - x.1) % n)

@[simp] theorem card_circulant (n : ℕ) (S : List ℕ) :
    FinEnum.card (circulant n S).V = n := rfl

@[toIsoGraph simp, simp] theorem circulant_nil (n : ℕ) : circulant n [] = empty n :=
  (eq_ofRel (empty n) (fun _ _ ↦ false) fun _ _ _ ↦ rfl).symm

/-- The arithmetic behind `circulant_one_eq_cycle`: for distinct `a, b < n`, the difference
`b - a` is `1` mod `n` exactly when `b` is the successor of `a` mod `n`.  Distinctness is needed
only for `n = 1`, where `a = b = 0` is its own successor but has difference `0`. -/
private theorem mod_add_sub_eq_one_iff {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (b + n - a) % n = 1 ↔ (a + 1) % n = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [show b + n - a = b - a + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : b - a < n)]
    rcases Nat.lt_or_ge (a + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show a + 1 = n by omega, Nat.mod_self]; omega
  · exact absurd h hab
  · rw [show b + n - a = n - (a - b) by omega,
      Nat.mod_eq_of_lt (by omega : n - (a - b) < n)]
    rcases Nat.lt_or_ge (a + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show a + 1 = n by omega, Nat.mod_self]; omega

/-- **The cycle is the circulant with connection set `{1}`** — an equality of `CGraph`s, not just
of isomorphism classes, since both are `ofRel` on `Fin n`. -/
@[toIsoGraph simp circulant_one]
theorem circulant_one_eq_cycle (n : ℕ) : circulant n [1] = cycle n := by
  refine (eq_ofRel (circulant n [1]) (fun i j ↦ (i.1 + 1) % n == j.1) fun x y hxy ↦ ?_).trans rfl
  have hne : x.1 ≠ y.1 := fun h ↦ hxy (Fin.ext h)
  have key : ∀ a b : Fin n, a.1 ≠ b.1 →
      ([1].contains ((b.1 + n - a.1) % n)) = ((a.1 + 1) % n == b.1) := fun a b hab ↦ by
    have h := mod_add_sub_eq_one_iff a.2 b.2 hab
    rw [show ([1].contains ((b.1 + n - a.1) % n)) = decide ((b.1 + n - a.1) % n = 1) by simp,
      Bool.beq_eq_decide_eq]
    exact decide_eq_decide.2 h
  show (decide (x ≠ y) && ([1].contains ((y.1 + n - x.1) % n) ||
    [1].contains ((x.1 + n - y.1) % n))) = _
  rw [decide_eq_true hxy, Bool.true_and, key x y hne, key y x (Ne.symm hne)]

/-- The nonzero quadratic residues mod `q`, as a bitmask — computed once, so that the Paley graph
answers an adjacency query with one `Nat.testBit`.

A `q`-element `Array Bool` would say the same thing, but the kernel reads one by walking the list
behind it, which is `O(q)` a query on a graph that asks `q²` of them; a bit of a number is read in
one step, the same trick and for the same reason as the adjacency mask of `CGraph.ofEdges`.  The
residues are scattered in by squaring, `O(q)` work rather than the `O(q²)` of testing each `d` for
being a square; `testBit_qrMask` recovers the defining predicate. -/
def qrMask (q : ℕ) : ℕ :=
  (List.range q).foldl (fun m i ↦ if i != 0 then m ||| 1 <<< (i * i % q) else m) 0

theorem testBit_qrMask (q d : ℕ) :
    (qrMask q).testBit d = decide (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = d) := by
  rw [qrMask]
  simp only [Nat.one_shiftLeft]
  rw [testBit_foldl_or (f := fun i ↦ i * i % q) (p := fun i ↦ i != 0), Nat.zero_testBit,
    Bool.false_or, Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h0, hsq⟩
    exact ⟨⟨i, hi⟩, h0, hsq⟩
  · rintro ⟨⟨i, hi⟩, h0, hsq⟩
    exact ⟨i, hi, h0, hsq⟩

/-- The Paley graph of order `q`: `x ~ y` when `y - x` is a nonzero square mod `q`.

This is the intended graph only for a *prime* `q ≡ 1 mod 4` — for a prime power one would need the
field `GF(q)`, and for `q ≡ 3 mod 4` the residues are not closed under negation, so `ofRel`
symmetrises the Paley *tournament* into the complete graph.  For a prime `q ≡ 1 mod 4` it is
strongly regular with parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)`; see
`IsoGraph/SmallGraphs/Defs/SRG.lean`. -/
@[toIsoGraph]
def paley (q : ℕ) : CGraph :=
  let t := qrMask q
  ofRel (Fin q) fun x y ↦ t.testBit ((y.1 + q - x.1) % q)

instance (q : ℕ) : Nonempty (paley (q + 1)).V := inferInstanceAs (Nonempty (Fin (q + 1)))

@[simp] theorem card_paley (q : ℕ) : FinEnum.card (paley q).V = q := rfl

/-- The number of coordinates at which two bit-strings differ, counted along `List.finRange n`
instead of by building the `Finset` of them.  The same number, and the cheaper one to ask for:
the two cube families below ask it on every adjacency query, and the `Finset` they would build
is thrown away as soon as its cardinality has been read off.  `hammingBelow` below is cheaper
still, and this lemma is the bridge the proofs cross to reach the `Finset` form. -/
theorem card_filter_ne_eq_countP {n : ℕ} (x y : Fin n → Bool) :
    (Finset.univ.filter fun i ↦ x i ≠ y i).card = (List.finRange n).countP fun i ↦ x i != y i := by
  rw [← List.toFinset_finRange n, (List.nodup_finRange n).card_eq_countP]
  exact List.countP_congr fun i _ ↦ by cases x i <;> cases y i <;> rfl

/-- The number of coordinates below `m` at which `x` and `y` differ, counted by descending on the
index.

`((List.finRange n).take m).countP` is the same number — `hammingBelow_eq` — and at `m = n` it is
the form everything below states the distance in, but it builds the list of indices in order to
walk it.  The list is not free: over the 256 vertices of `Q₈`, a full sweep of the hypercube's
adjacency function costs 30 ms counting along it and 25 ms counting down.  `hammingCapped` below
is cheaper still, and is what the two cube families actually ask. -/
def hammingBelow {n : ℕ} (x y : Fin n → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (if h : m < n then (if x ⟨m, h⟩ != y ⟨m, h⟩ then 1 else 0) else 0) + hammingBelow x y m

theorem hammingBelow_eq {n : ℕ} (x y : Fin n → Bool) :
    ∀ m, m ≤ n → hammingBelow x y m = ((List.finRange n).take m).countP fun i ↦ x i != y i
  | 0, _ => by simp [hammingBelow]
  | m + 1, h => by
    have hm : m < n := h
    rw [hammingBelow, hammingBelow_eq x y m (Nat.le_of_lt hm), List.take_add_one,
      List.countP_append, dif_pos hm]
    rw [show (List.finRange n)[m]? = some ⟨m, hm⟩ by
      rw [List.getElem?_eq_getElem (by simpa using hm)]; simp]
    simp [List.countP_cons, Nat.add_comm]

/-- The Hamming distance, as everything states it. -/
theorem hammingBelow_self {n : ℕ} (x y : Fin n → Bool) :
    hammingBelow x y n = (List.finRange n).countP fun i ↦ x i != y i := by
  rw [hammingBelow_eq x y n le_rfl, List.take_of_length_le (by simp)]

theorem hammingBelow_le {n : ℕ} (x y : Fin n → Bool) : ∀ m, hammingBelow x y m ≤ m
  | 0 => le_rfl
  | m + 1 => by
    have := hammingBelow_le x y m
    rw [hammingBelow]
    split_ifs <;> omega

/-- The distance again, this time abandoned as soon as it reaches two.

Neither cube ever asks what the distance *is*; both ask whether it is one, and one is a question
two bit-strings usually answer in the first few coordinates.  Counting the whole way is counting
past the answer: two strings drawn at random differ twice within four coordinates, whatever `n`
is, so the scan the cube pays for grows with the dimension and the scan it needs does not.  Over
the 256 vertices of `Q₈`, a full sweep of the hypercube's adjacency costs 25 ms counting down and
13 ms stopping at two.

`hammingCapped_eq` is `min 2` of the distance, which is all that survives the cap, and
`hammingCapped_self` is the only consequence of it anyone wants. -/
def hammingCapped {n : ℕ} (x y : Fin n → Bool) (c : ℕ) : ℕ → ℕ
  | 0 => c
  | m + 1 =>
    if 2 ≤ c then c
    else hammingCapped x y
      (c + (if h : m < n then (if x ⟨m, h⟩ != y ⟨m, h⟩ then 1 else 0) else 0)) m

theorem hammingCapped_eq {n : ℕ} (x y : Fin n → Bool) :
    ∀ (m c : ℕ), c ≤ 2 → hammingCapped x y c m = min 2 (c + hammingBelow x y m)
  | 0, c, hc => by simp [hammingCapped, hammingBelow, Nat.min_eq_right hc]
  | m + 1, c, hc => by
    rw [hammingCapped]
    split
    · next h => omega
    · next h =>
      rw [hammingCapped_eq x y m _ (by split_ifs <;> omega), hammingBelow]
      omega

/-- Stopping at two still tells one from everything else, which is what the hypercube asks. -/
theorem hammingCapped_self {n : ℕ} (x y : Fin n → Bool) :
    (hammingCapped x y 0 n == 1) = (hammingBelow x y n == 1) := by
  rw [hammingCapped_eq x y n 0 (by omega), Nat.zero_add]
  rcases Nat.lt_or_ge (hammingBelow x y n) 2 with h | h
  · rw [Nat.min_eq_right (le_of_lt h)]
  · rw [Nat.min_eq_left h]
    show false = _
    exact (beq_eq_false_iff_ne.2 (by omega)).symm

/-- Whether `x` and `y` differ at every coordinate below `m`, i.e. whether their distance is `m`
— `hammingFull_eq`.  The folded cube's second disjunct, and the cheap half of it: `&&`
short-circuits, so this abandons at the first coordinate the two strings share, and two strings
drawn at random share one within two coordinates. -/
def hammingFull {n : ℕ} (x y : Fin n → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => (if h : m < n then x ⟨m, h⟩ != y ⟨m, h⟩ else false) && hammingFull x y m

theorem hammingFull_eq {n : ℕ} (x y : Fin n → Bool) :
    ∀ m, hammingFull x y m = (hammingBelow x y m == m)
  | 0 => rfl
  | m + 1 => by
    have := hammingBelow_le x y m
    rw [hammingFull, hammingFull_eq x y m, hammingBelow]
    split_ifs <;> simp_all [bne_iff_ne, Nat.add_comm] <;> omega

/-- The hypercube `Q_n`: bit-strings of length `n`, adjacent when they differ in exactly one
place.  This is the `n`-fold cartesian product of `complete 2`, but written directly, so that a
vertex is a bit-string rather than the nested pair the recursion would give.

`hypercube_adj` states adjacency with the `Finset` of differing coordinates, which is what the
proofs want; the definition counts them with `hammingCapped`, which is what a query wants. -/
@[toIsoGraph]
def hypercube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := hammingCapped x y 0 n == 1
  symm x y := by
    rw [hammingCapped_self, hammingCapped_self, hammingBelow_self, hammingBelow_self]
    congr 1
    exact List.countP_congr fun i _ ↦ by cases x i <;> cases y i <;> rfl
  loopless x := by
    rw [hammingCapped_self, hammingBelow_self,
      show ((List.finRange n).countP fun i ↦ x i != x i) = 0 from
      List.countP_eq_zero.2 fun i _ ↦ by simp]
    simp

instance (n : ℕ) : Nonempty (hypercube n).V := inferInstanceAs (Nonempty (Fin n → Bool))

@[simp] theorem hypercube_adj (n : ℕ) (x y : Fin n → Bool) :
    (hypercube n).Adj x y = ((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) := by
  rw [card_filter_ne_eq_countP, ← hammingBelow_self]
  exact hammingCapped_self x y

theorem hypercube_eq_ofRel (n : ℕ) :
    hypercube n = ofRel (Fin n → Bool) fun x y ↦
      (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1 :=
  eq_ofRel _ _ fun x y _ => by
    have h := (hypercube n).symm x y
    simp only [hypercube_adj] at h
    simp only [hypercube_adj, ← h, Bool.or_self]

/-! ## The funnier ones -/

/-- How many elements of `s` also lie in `t`.

`(s ∩ t).card` is the same number — `interCard_eq` — and is the form the two subset families below
state their adjacency in, but building the intersection in order to read its size off and throw it
away is not what one wants on every query.  Deciding membership is the expensive half of it, and
`Multiset.count` decides it with a `BEq` scan and nothing else: over the 252 vertices of `K(10, 5)`,
a full sweep of the Kneser adjacency costs 25 ms through the intersection, 24 ms counting the
elements of `s` that satisfy `· ∈ t`, and 9 ms counting them this way. -/
def interCard {α : Type*} [DecidableEq α] (s t : Finset α) : ℕ :=
  Multiset.countP (fun x ↦ t.val.count x ≠ 0) s.val

@[simp] theorem interCard_eq {α : Type*} [DecidableEq α] (s t : Finset α) :
    interCard s t = (s ∩ t).card := by
  rw [interCard, Multiset.countP_congr (p' := (· ∈ t)) rfl fun x _ ↦ by simp,
    Multiset.countP_eq_card_filter, ← Finset.filter_mem_eq_inter]
  rfl

/-- The Kneser graph `K(n, k)`: the `k`-element subsets of `Fin n`, adjacent when disjoint.
`kneser 5 2` is the Petersen graph.

The disjointness test is reflexive when `k = 0` (the empty set is disjoint from itself), so the
diagonal has to be excluded; it is symmetric already.  `k ≠ 0` does that as well as `s ≠ t`
would — a nonempty set meets itself — and does not cost a comparison of two `Finset`s, which is
a comparison of two lists up to permutation, on every query.  `kneser_adj` states the relation
in the form one wants to reason with. -/
@[toIsoGraph]
def kneser (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := (k != 0) && (interCard s.1 t.1 == 0)
  symm s t := by rw [interCard_eq, interCard_eq, Finset.inter_comm]
  loopless s := by
    rw [interCard_eq, Finset.inter_self, s.2]
    simp

@[simp] theorem kneser_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (kneser n k).Adj s t = (decide (s ≠ t) && decide (s.1 ∩ t.1 = ∅)) := by
  show ((k != 0) && (interCard s.1 t.1 == 0)) = _
  rw [interCard_eq]
  by_cases hd : s.1 ∩ t.1 = ∅
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hst : s = t :=
        Subtype.ext ((Finset.card_eq_zero.1 s.2).trans (Finset.card_eq_zero.1 t.2).symm)
      simp [hst]
    · have hst : s ≠ t := fun h ↦ by
        rw [← h, Finset.inter_self, ← Finset.card_eq_zero, s.2] at hd
        omega
      simp [hd, hst, hk.ne']
  · simp [hd, Finset.card_eq_zero]

theorem kneser_eq_ofRel (n k : ℕ) :
    kneser n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ decide (s.1 ∩ t.1 = ∅) :=
  eq_ofRel _ _ fun s t hst => by
    rw [kneser_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

/-- The Johnson graph `J(n, k)`: the `k`-element subsets of `Fin n`, adjacent when they meet in
`k - 1` points.  `johnson n 2` is the triangular graph `T(n)`, i.e. the line graph of `Kₙ`, and
the complement of `kneser n 2`.

Every set meets itself in `k` points, so for `k ≥ 1` the diagonal is already excluded; only
`k = 0`, where the condition `|s ∩ t| = k - 1` degenerates to `0 = 0`, would put a loop at the one
vertex, and `k ≠ 0` rules that out without comparing two `Finset`s on every query.  `johnson_adj`
states the relation in the form one wants to reason with. -/
@[toIsoGraph]
def johnson (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := (k != 0) && (interCard s.1 t.1 == k - 1)
  symm s t := by rw [interCard_eq, interCard_eq, Finset.inter_comm]
  loopless s := by
    rw [interCard_eq, Finset.inter_self, s.2, Bool.and_eq_true]
    rintro ⟨hk, hkk⟩
    simp only [bne_iff_ne, ne_eq, beq_iff_eq] at hk hkk
    omega

@[simp] theorem johnson_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (johnson n k).Adj s t = (decide (s ≠ t) && ((s.1 ∩ t.1).card == k - 1)) := by
  show ((k != 0) && (interCard s.1 t.1 == k - 1)) = _
  rw [interCard_eq]
  by_cases hst : s = t
  · subst hst
    rw [Finset.inter_self, s.2]
    have h0 : ((k != 0) && (k == k - 1)) = false := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact Or.inr (by omega)
    rw [h0]
    simp
  · have hk : k ≠ 0 := by
      rintro rfl
      exact hst (Subtype.ext ((Finset.card_eq_zero.1 s.2).trans (Finset.card_eq_zero.1 t.2).symm))
    simp [hst, hk]

theorem johnson_eq_ofRel (n k : ℕ) :
    johnson n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ (s.1 ∩ t.1).card == k - 1 :=
  eq_ofRel _ _ fun s t hst => by
    rw [johnson_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

@[simp] theorem card_johnson (n k : ℕ) : FinEnum.card (johnson n k).V = n.choose k := by
  show FinEnum.card {s : Finset (Fin n) // s.card = k} = n.choose k
  rw [FinEnum.card_eq_fintypeCard']
  simp [Fintype.card_finset_len]

/-- Whether two bit-strings differ in exactly one coordinate or in all `n` of them, which is the
folded cube's adjacency once the empty case is out of the way.

The distance decides both disjuncts and the obvious thing to do is to compute it once and ask
twice, but neither disjunct needs the distance itself: the first needs it capped at two and the
second only needs to know whether some coordinate agrees.  Both give up early where counting
cannot, and the pair of them cost less than the one count — over the 256 vertices of `Q₈` a full
sweep of the folded cube's adjacency costs 26 ms counting and 19 ms this way. -/
def foldedNear {n : ℕ} (x y : Fin n → Bool) : Bool :=
  (hammingCapped x y 0 n == 1) || hammingFull x y n

theorem foldedNear_eq {n : ℕ} (x y : Fin n → Bool) :
    foldedNear x y = ((hammingBelow x y n == 1) || (hammingBelow x y n == n)) := by
  rw [foldedNear, hammingCapped_self, hammingFull_eq]

/-- The folded cube: `Qₙ` with each pair of antipodal vertices joined, i.e. bit-strings of length
`n` adjacent when they differ in exactly one place *or* in all `n` of them.  Identifying antipodes
instead would halve the vertex count; this is the double cover of that, and is the folded
`(n+1)`-cube.  `foldedCube 4` is the Clebsch graph. -/
@[toIsoGraph]
def foldedCube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := (n != 0) && foldedNear x y
  symm x y := by
    show ((n != 0) && _) = ((n != 0) && _)
    rw [foldedNear_eq, foldedNear_eq, hammingBelow_self, hammingBelow_self,
      show ((List.finRange n).countP fun i ↦ x i != y i)
          = (List.finRange n).countP fun i ↦ y i != x i from
        List.countP_congr fun i _ ↦ by cases x i <;> cases y i <;> rfl]
  loopless x := by
    show ((n != 0) && _) = true → False
    rw [foldedNear_eq, hammingBelow_self,
      show ((List.finRange n).countP fun i ↦ x i != x i) = 0 from
      List.countP_eq_zero.2 fun i _ ↦ by simp, Bool.and_eq_true]
    rintro ⟨hn, hc⟩
    simp only [bne_iff_ne, ne_eq] at hn
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    omega

@[simp] theorem foldedCube_adj (n : ℕ) (x y : Fin n → Bool) :
    (foldedCube n).Adj x y = (decide (x ≠ y) &&
      (((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) ||
        ((Finset.univ.filter fun i ↦ x i ≠ y i).card == n))) := by
  rw [card_filter_ne_eq_countP]
  show ((n != 0) && _) = _
  rw [foldedNear_eq, hammingBelow_self]
  by_cases hxy : x = y
  · subst hxy
    rw [show ((List.finRange n).countP fun i ↦ x i != x i) = 0 from
      List.countP_eq_zero.2 fun i _ ↦ by simp]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne', hn.ne]
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hxy (funext fun i ↦ i.elim0)
    simp [hxy, hn]

@[simp] theorem card_foldedCube (n : ℕ) : FinEnum.card (foldedCube n).V = 2 ^ n := by
  simp [foldedCube]

/-! ## A few named families

One call to one constructor each, so they are `abbrev`s: instance search and `decide` see straight
through them. -/

/-- The book `Bₙ = K_{1,1,n}`: `n` triangles glued along a common edge. -/
abbrev book (n : ℕ) : CGraph := completeMultipartite [1, 1, n]

/-- The fan `Fₙ`: a path on `n` vertices plus a hub joined to all of it. -/
abbrev fan (n : ℕ) : CGraph := complete 1 ∇g path n

/-- The ladder `Lₙ = Pₙ □ K₂`: two paths joined rung by rung. -/
abbrev ladder (n : ℕ) : CGraph := path n □g complete 2

/-- The prism `Yₙ = Cₙ □ K₂`, also called the circular ladder. -/
abbrev prism (n : ℕ) : CGraph := cycle n □g complete 2

/-- The triangular graph `T(n) = J(n, 2) = L(Kₙ)`: the pairs from an `n`-set, adjacent when they
overlap. -/
abbrev triangular (n : ℕ) : CGraph := johnson n 2

/-- The rook's graph `Kₘ □ Kₙ`: the squares of an `m × n` board, adjacent along rows and
columns. -/
abbrev rook (m n : ℕ) : CGraph := complete m □g complete n

/-- The cocktail party graph `K_{n×2}`: `K_{2n}` minus a perfect matching. -/
abbrev cocktailParty (n : ℕ) : CGraph := completeMultipartite (List.replicate n 2)

/-- The Petersen graph, as the Kneser graph on the 2-subsets of a 5-set. -/
abbrev petersen : CGraph := kneser 5 2

/-- The Turán graph `T(n, r)`: the complete multipartite graph whose `r` parts are as equal as
possible and hold `n` vertices in total. -/
abbrev turan (n r : ℕ) : CGraph :=
  completeMultipartite (List.replicate (n % r) (n / r + 1) ++ List.replicate (r - n % r) (n / r))

/-- The friendship (windmill) graph `Fₙ`: `n` triangles glued at a common vertex. -/
abbrev friendship (n : ℕ) : CGraph :=
  complete 1 ∇g empty n □g complete 2

/-- The crown graph `Sₙ`: the complete bipartite graph `K_{n,n}` with a perfect matching removed,
equivalently the bipartite double cover of `Kₙ`. -/
abbrev crown (n : ℕ) : CGraph := complete n ⊗g complete 2

/-- The cubic graph with LCF code `[ss]^r`, in Lederberg–Coxeter–Frucht notation: a Hamiltonian
cycle on `ss.length * r` vertices with the chords prescribed by `ss`, repeated `r` times. -/
@[toIsoGraph]
def lcf (ss : List ℤ) (r : ℕ) : CGraph := ofEdges (ss.length * r) (lcfEdges ss r)

@[simp] theorem card_lcf (ss : List ℤ) (r : ℕ) :
    FinEnum.card (lcf ss r).V = ss.length * r := card_ofEdges _ _

/-- The generalized Petersen graph `GP(n, k)`. -/
@[toIsoGraph]
def gp (n k : ℕ) : CGraph := ofEdges (2 * n) (gpEdges n k)

@[simp] theorem card_gp (n k : ℕ) : FinEnum.card (gp n k).V = 2 * n := card_ofEdges _ _

end

end CGraph
