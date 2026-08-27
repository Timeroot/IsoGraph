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

/-- The complete bipartite graph `K_{m,n}`. -/
@[toIsoGraph]
def bipartite (m n : ℕ) : CGraph := (complete m ⊕g complete n)ᶜ

instance (m n : ℕ) : Nonempty (bipartite (m + 1) n).V :=
  inferInstanceAs (Nonempty (Fin (m + 1) ⊕ Fin n))

@[simp] theorem card_bipartite (m n : ℕ) : FinEnum.card (bipartite m n).V = m + n := by
  simp [bipartite]

@[simp] theorem bipartite_adj_inl_inl (m n : ℕ) (a c : Fin m) :
    (bipartite m n).Adj (.inl a) (.inl c) = false := by
  by_cases h : a = c <;> simp [bipartite, complete, h]

@[simp] theorem bipartite_adj_inr_inr (m n : ℕ) (b d : Fin n) :
    (bipartite m n).Adj (.inr b) (.inr d) = false := by
  by_cases h : b = d <;> simp [bipartite, complete, h]

@[simp] theorem bipartite_adj_inl_inr (m n : ℕ) (a : Fin m) (d : Fin n) :
    (bipartite m n).Adj (.inl a) (.inr d) = true := by
  simp [bipartite]

@[simp] theorem bipartite_adj_inr_inl (m n : ℕ) (b : Fin n) (c : Fin m) :
    (bipartite m n).Adj (.inr b) (.inl c) = true := by
  simp [bipartite]

/-- The complete multipartite graph with parts of sizes `ds`. -/
@[toIsoGraph]
def completeMultipartite (ds : List ℕ) : CGraph :=
  (sigmaUnion fun i : Fin ds.length ↦ complete (ds.get i))ᶜ

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

/-- The nonzero quadratic residues mod `q`, as a lookup table — computed once, so that the Paley
graph answers an adjacency query with one array read.

Written as an `Array.ofFn` over the *defining* predicate rather than by scattering `i * i % q`
into a mutable array: building the table then costs `O(q²)` instead of `O(q)`, which is nothing
next to the `O(q²)` adjacency matrix it feeds, and in exchange `qrTable_getElem` reads off an
entry with no reasoning about `Array.set!` at all. -/
def qrTable (q : ℕ) : Array Bool :=
  Array.ofFn (n := q) fun d ↦ decide (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = d.1)

theorem qrTable_getElem (q d : ℕ) (h : d < q) :
    (qrTable q)[d]! = decide (∃ i : Fin q, i.1 ≠ 0 ∧ i.1 * i.1 % q = d) := by
  have hs : d < (qrTable q).size := by simpa [qrTable] using h
  rw [getElem!_pos (qrTable q) d hs]
  simp [qrTable]

/-- The Paley graph of order `q`: `x ~ y` when `y - x` is a nonzero square mod `q`.

This is the intended graph only for a *prime* `q ≡ 1 mod 4` — for a prime power one would need the
field `GF(q)`, and for `q ≡ 3 mod 4` the residues are not closed under negation, so `ofRel`
symmetrises the Paley *tournament* into the complete graph.  For a prime `q ≡ 1 mod 4` it is
strongly regular with parameters `(q, (q-1)/2, (q-5)/4, (q-1)/4)`; see
`IsoGraph/SmallGraphs/Defs/SRG.lean`. -/
@[toIsoGraph]
def paley (q : ℕ) : CGraph :=
  let t := qrTable q
  ofRel (Fin q) fun x y ↦ t[(y.1 + q - x.1) % q]!

instance (q : ℕ) : Nonempty (paley (q + 1)).V := inferInstanceAs (Nonempty (Fin (q + 1)))

@[simp] theorem card_paley (q : ℕ) : FinEnum.card (paley q).V = q := rfl

/-- The hypercube `Q_n`: bit-strings of length `n`, adjacent when they differ in exactly one
place.  This is the `n`-fold cartesian product of `complete 2`, but written directly, so that a
vertex is a bit-string rather than the nested pair the recursion would give. -/
@[toIsoGraph]
def hypercube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1
  symm x y := by
    congr 1
    exact congrArg Finset.card (Finset.filter_congr fun i _ => by exact ne_comm)
  loopless x := by simp

instance (n : ℕ) : Nonempty (hypercube n).V := inferInstanceAs (Nonempty (Fin n → Bool))

@[simp] theorem hypercube_adj (n : ℕ) (x y : Fin n → Bool) :
    (hypercube n).Adj x y = ((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) := rfl

theorem hypercube_eq_ofRel (n : ℕ) :
    hypercube n = ofRel (Fin n → Bool) fun x y ↦
      (Finset.univ.filter fun i ↦ x i ≠ y i).card == 1 :=
  eq_ofRel _ _ fun x y _ => by
    have h := (hypercube n).symm x y
    simp only [hypercube_adj] at h
    simp only [hypercube_adj, ← h, Bool.or_self]

/-! ## The funnier ones -/

/-- The Kneser graph `K(n, k)`: the `k`-element subsets of `Fin n`, adjacent when disjoint.
`kneser 5 2` is the Petersen graph.

The disjointness test is reflexive when `k = 0` (the empty set is disjoint from itself), so the
diagonal is deleted explicitly; it is symmetric already. -/
@[toIsoGraph]
def kneser (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := decide (s ≠ t) && decide (s.1 ∩ t.1 = ∅)
  symm s t := by rw [decide_ne_comm s t, Finset.inter_comm]
  loopless s := by simp

@[simp] theorem kneser_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (kneser n k).Adj s t = (decide (s ≠ t) && decide (s.1 ∩ t.1 = ∅)) := rfl

theorem kneser_eq_ofRel (n k : ℕ) :
    kneser n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ decide (s.1 ∩ t.1 = ∅) :=
  eq_ofRel _ _ fun s t hst => by
    rw [kneser_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

/-- The Johnson graph `J(n, k)`: the `k`-element subsets of `Fin n`, adjacent when they meet in
`k - 1` points.  `johnson n 2` is the triangular graph `T(n)`, i.e. the line graph of `Kₙ`, and
the complement of `kneser n 2`.

Every set meets itself in `k` points, so for `k ≥ 1` the diagonal is already excluded; it is
deleted explicitly anyway, since at `k = 0` the condition `|s ∩ t| = k - 1` degenerates to `0 = 0`
and would put a loop at the one vertex. -/
@[toIsoGraph]
def johnson (n k : ℕ) : CGraph where
  V := {s : Finset (Fin n) // s.card = k}
  Adj s t := decide (s ≠ t) && ((s.1 ∩ t.1).card == k - 1)
  symm s t := by rw [decide_ne_comm s t, Finset.inter_comm]
  loopless s := by simp

@[simp] theorem johnson_adj (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (johnson n k).Adj s t = (decide (s ≠ t) && ((s.1 ∩ t.1).card == k - 1)) := rfl

theorem johnson_eq_ofRel (n k : ℕ) :
    johnson n k = ofRel {s : Finset (Fin n) // s.card = k} fun s t ↦ (s.1 ∩ t.1).card == k - 1 :=
  eq_ofRel _ _ fun s t hst => by
    rw [johnson_adj, decide_eq_true (by simpa using hst : s ≠ t), Bool.true_and,
      Finset.inter_comm t.1 s.1, Bool.or_self]

@[simp] theorem card_johnson (n k : ℕ) : FinEnum.card (johnson n k).V = n.choose k := by
  rw [FinEnum.card_eq_fintypeCard']
  simp [johnson, Fintype.card_finset_len]

/-- The folded cube: `Qₙ` with each pair of antipodal vertices joined, i.e. bit-strings of length
`n` adjacent when they differ in exactly one place *or* in all `n` of them.  Identifying antipodes
instead would halve the vertex count; this is the double cover of that, and is the folded
`(n+1)`-cube.  `foldedCube 4` is the Clebsch graph. -/
@[toIsoGraph]
def foldedCube (n : ℕ) : CGraph where
  V := Fin n → Bool
  Adj x y := decide (x ≠ y) && (((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) ||
    ((Finset.univ.filter fun i ↦ x i ≠ y i).card == n))
  symm x y := by
    have h : (Finset.univ.filter fun i ↦ x i ≠ y i) = (Finset.univ.filter fun i ↦ y i ≠ x i) :=
      Finset.filter_congr fun i _ => by exact ne_comm
    rw [decide_ne_comm x y, h]
  loopless x := by simp

@[simp] theorem foldedCube_adj (n : ℕ) (x y : Fin n → Bool) :
    (foldedCube n).Adj x y = (decide (x ≠ y) &&
      (((Finset.univ.filter fun i ↦ x i ≠ y i).card == 1) ||
        ((Finset.univ.filter fun i ↦ x i ≠ y i).card == n))) := rfl

@[simp] theorem card_foldedCube (n : ℕ) : FinEnum.card (foldedCube n).V = 2 ^ n := by
  simp [foldedCube, FinEnum.card_fun]

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
