import IsoGraph.Core.Colouring
import Std.Tactic.BVDecide

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# `graph_sat`: the co-NP invariants by SAT

The independence number, the clique number and the chromatic number are the three invariants of
the library whose *hard* direction is a refutation: there is no independent set of size `n + 1`,
no clique of size `n + 1`, no proper colouring with `k` colours.  Each of those is a propositional
formula being unsatisfiable, which is exactly what a SAT solver is for, and Lean has one —
`bv_decide` bit-blasts a `BitVec` goal, calls CaDiCaL, and checks the LRAT refutation it comes
back with in the kernel.

This file is the bridge.  `graph_sat` recognises

    G.indepNum ≤ n        G.cliqueNum ≤ n        k < G.chromNum
    G.matchNum ≤ n        k < G.edgeChromNum     k < G.cliqueCoverNum

for a concrete graph — a `CGraph`, or an element of `IsoGraph` that reduces to the class of one —
encodes it into a `BitVec` goal and hands that to `bv_decide`.  The three on the second line are
the same three invariants of a derived graph, definitionally: `ν(G) = α(L(G))`,
`χ'(G) = χ(L(G))`, `θ(G) = χ(Ḡ)`, so all the tactic does with them is search the derived graph.

## The encodings

A subset of the vertices is a `BitVec` of width `|V|`, one bit per vertex in the order
`FinEnum.equiv` puts them in.  For `indepNum ≤ n` the constraints are one per edge — no two
adjacent bits are both set — and the conclusion is that the population count is at most `n`; the
population count is spelled out as a chain of `w`-bit additions, which is how a SAT solver counts.
`cliqueNum ≤ n` is the same with the constraints on the *non*-edges.

For `k < G.chromNum` a colouring is a `BitVec` of width `|V| * k` read as `|V|` chunks of `k` bits,
the chunk of a vertex being the set of colours it is allowed.  Every chunk is nonzero and adjacent
chunks are disjoint; from any solution one reads off a proper `k`-colouring by picking a bit from
each chunk, so the system being unsatisfiable is exactly `¬ G.toSimple.Colorable k`.  Note this is
smaller than the usual clause encoding: one constraint per vertex and one per edge, not one per
edge and colour.

## What it costs

`bv_decide` is called once and the whole run — bit-blasting, CaDiCaL, and the kernel replay of the
LRAT proof — is what shows up in the elaboration time.  Measured on the graphs below:

| goal | vertices | constraints | time |
| --- | --- | --- | --- |
| `3 < (mycielskian (cycle 5)).chromNum` | 11 | 31 | 0.4 s |
| `(kneser 5 2).indepNum ≤ 4` | 10 | 15 | 0.7 s |
| `4 < (mycielskian (mycielskian (cycle 5))).chromNum` | 23 | 94 | 1 s |
| `(kneser 7 3).indepNum ≤ 15` | 35 | 70 | 1.6 s with `native`, 5 s without |
| `(kneser 5 2).cliqueNum ≤ 2` | 10 | 30 | 2 s |
| `pentakisDodecahedron.cliqueNum ≤ 3` | 32 | 406 | 4 s |

Those are profiled elaboration times of the one declaration, so they include everything.  The
solver is not the expensive part of any of them: bit-blasting, CaDiCaL and the kernel replay of
the LRAT certificate together come to a fifth of a second even on the pentakis dodecahedron, and
what the table measures is mostly the side conditions below and the work of matching the bundled
constraints against the chain `bv_decide` was handed, both linear in the constraint count.

The comparison is not with `decide`, which cannot do any of these — `indepNum` is an infimum over
a set of naturals and does not reduce — but with the hand proofs the library gives elsewhere: the
clique–coclique bound gets `petersen.indepNum ≤ 5` and stops one short of the truth, and the
Erdős–Ko–Rado value `(kneser 7 3).indepNum = 15` is a theorem nobody would attempt by hand here.

The tactic is used downstream too: `NamedGraphs.edgeChromNum_flowerSnark`, in
`SmallGraphs/EdgeColourings.lean`, is the flower snark `J₅` shown to be class two on a line graph
of thirty vertices — the case split the Petersen proof runs, `3 ^ E`, is hopeless there.

## The side conditions

Two facts about the graph are settled outside the solver: its order, and its edge list read
through `FinEnum.equiv`.  Both are closed computations, and `graph_sat` proves them with `decide`
— so the whole proof is kernel-checked, `bv_decide` included.  On a vertex type that the kernel
evaluates badly (a subtype of `Finset`, say) that check can cost more than the SAT call; `graph_sat
native` proves those two with `native_decide` instead, which trades them for the compiler.

## What it does not do

The other direction of each bound — `n ≤ G.indepNum`, `G.chromNum ≤ k` — is a *witness*, not a
refutation, and a SAT solver is the wrong tool: give the independent set to
`SimpleGraph.IsIndepSet.card_le_indepNum` or the colouring to `chromNum_le_iff_colorable` and the
kernel checks it directly.  `graph_sat` on such a goal fails rather than looping.
-/

set_option autoImplicit false

namespace CGraph
namespace Sat

/-! ## Vertices as bit positions -/

/-- The position of a vertex in the enumeration of `G.V`: the bit that stands for it. -/
def vIdx {G : CGraph} (v : G.V) : ℕ := (FinEnum.equiv v : Fin (FinEnum.card G.V)).val

theorem vIdx_lt {G : CGraph} (v : G.V) : vIdx v < FinEnum.card G.V := (FinEnum.equiv v).isLt

theorem vIdx_injective {G : CGraph} : Function.Injective (vIdx (G := G)) := fun _ _ h ↦
  FinEnum.equiv.injective (Fin.ext h)

/-- The edges of `G` as pairs of bit positions, each edge once. -/
def edgeIdxList (G : CGraph) : List (ℕ × ℕ) :=
  (FinEnum.toList G.V).flatMap fun u ↦
    (FinEnum.toList G.V).filterMap fun v ↦
      if G.Adj u v = true ∧ vIdx u < vIdx v then some (vIdx u, vIdx v) else none

/-- The pairs of *distinct non-adjacent* vertices of `G`, as pairs of bit positions. -/
def nonEdgeIdxList (G : CGraph) : List (ℕ × ℕ) :=
  (FinEnum.toList G.V).flatMap fun u ↦
    (FinEnum.toList G.V).filterMap fun v ↦
      if G.Adj u v = false ∧ vIdx u < vIdx v then some (vIdx u, vIdx v) else none

theorem exists_adj_of_mem_edgeIdxList {G : CGraph} {p : ℕ × ℕ} (h : p ∈ edgeIdxList G) :
    ∃ u v : G.V, G.Adj u v = true ∧ p = (vIdx u, vIdx v) := by
  obtain ⟨u, -, hu⟩ := List.mem_flatMap.1 h
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 hu
  by_cases hc : G.Adj u v = true ∧ vIdx u < vIdx v
  · rw [if_pos hc] at hv
    exact ⟨u, v, hc.1, (Option.some_inj.1 hv).symm⟩
  · rw [if_neg hc] at hv; exact absurd hv (by simp)

theorem exists_not_adj_of_mem_nonEdgeIdxList {G : CGraph} {p : ℕ × ℕ} (h : p ∈ nonEdgeIdxList G) :
    ∃ u v : G.V, u ≠ v ∧ G.Adj u v = false ∧ p = (vIdx u, vIdx v) := by
  obtain ⟨u, -, hu⟩ := List.mem_flatMap.1 h
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.1 hu
  by_cases hc : G.Adj u v = false ∧ vIdx u < vIdx v
  · rw [if_pos hc] at hv
    exact ⟨u, v, fun he ↦ absurd hc.2 (by rw [he]; omega), hc.1, (Option.some_inj.1 hv).symm⟩
  · rw [if_neg hc] at hv; exact absurd hv (by simp)

/-! ## Subsets as bit vectors -/

/-- The `m`-bit vector whose bits below `k` are `f`. -/
def bvOfPred (m : ℕ) (f : ℕ → Bool) : ℕ → BitVec m
  | 0 => 0#m
  | k + 1 => (if f k then BitVec.twoPow m k else 0#m) ||| bvOfPred m f k

theorem getLsbD_bvOfPred_of_le (m : ℕ) (f : ℕ → Bool) {k i : ℕ} (h : k ≤ i) :
    (bvOfPred m f k).getLsbD i = false := by
  induction k with
  | zero => simp [bvOfPred]
  | succ k ih =>
    have hk : k ≠ i := by omega
    rw [bvOfPred, BitVec.getLsbD_or, ih (by omega)]
    split <;> simp [BitVec.getLsbD_twoPow, hk]

theorem getLsbD_bvOfPred (m : ℕ) (f : ℕ → Bool) {k i : ℕ} (hik : i < k) (him : i < m) :
    (bvOfPred m f k).getLsbD i = f i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [bvOfPred, BitVec.getLsbD_or]
    rcases Nat.lt_or_ge i k with h | h
    · rw [ih h]
      have hk : ¬ k = i := by omega
      split <;> simp [BitVec.getLsbD_twoPow, hk]
    · have hik' : i = k := by omega
      subst hik'
      rw [getLsbD_bvOfPred_of_le m f (le_refl i)]
      cases hf : f i <;> simp [him]

/-! ## Counting the bits

`bvCount w b m` is the number of set bits of `b` below `m`, as a `w`-bit vector — an addition
chain of `m` conditional ones, which is what the tactic hands to `bv_decide`.  It counts
correctly as long as `w` bits are enough to hold the answer. -/

/-- The population count of the bottom `k` bits of `b`, as a `w`-bit vector. -/
def bvCount (w : ℕ) {m : ℕ} (b : BitVec m) : ℕ → BitVec w
  | 0 => 0#w
  | k + 1 => cond (b.getLsbD k) 1#w 0#w + bvCount w b k

theorem toNat_bvCount {w m : ℕ} (b : BitVec m) {k : ℕ} (hk : k < 2 ^ w) :
    (bvCount w b k).toNat = ((Finset.range k).filter fun i ↦ b.getLsbD i).card := by
  induction k with
  | zero => simp [bvCount]
  | succ k ih =>
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h | h
      · rw [h] at hk; omega
      · exact h
    have hk' : k < 2 ^ w := by omega
    have hcard : ((Finset.range k).filter fun i ↦ b.getLsbD i).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have hone : (cond (b.getLsbD k) 1#w 0#w : BitVec w).toNat = if b.getLsbD k then 1 else 0 := by
      cases b.getLsbD k <;> simp [BitVec.toNat_one hw]
    rw [bvCount, BitVec.toNat_add, hone, ih hk', Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter fun i ↦ b.getLsbD i := by simp
    split
    · rw [Finset.card_insert_of_notMem hnot, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega

/-! ## The bridges

Each of the three takes the graph apart into data the tactic can compute — the order `m`, the
edge list `es` — and leaves a hypothesis about `BitVec`s and nothing else, which is the goal that
goes to `bv_decide`.

The constraints go in bundled — `pairsOK b es`, one proposition — rather than one hypothesis per
pair, and on a graph with a few hundred non-edges the difference is most of the elaboration time.
Spelled out, the tactic has to prove `(i, j) ∈ es` for every pair, each a linear scan of a list
literal as long as the whole encoding, and then apply a term with one argument per pair for the
kernel to recheck; bundled, it is one traversal and one argument.  `bv_decide` preprocesses every
hypothesis it is handed too, so it would rather be handed one than four hundred.  Each of the
three predicates below unfolds, on a literal list, to precisely the chain of conjunctions the
tactic writes out — the same proposition, so nothing has to be rewritten to pass one for the
other. -/

/-- The independence constraints as a single proposition: neither bit of a listed pair is set. -/
def pairsOK {m : ℕ} (b : BitVec m) (l : List (ℕ × ℕ)) : Prop :=
  l.foldr (fun p P ↦ (b.getLsbD p.1 && b.getLsbD p.2) = false ∧ P) True

theorem pairsOK_of_forall {m : ℕ} {b : BitVec m} {l : List (ℕ × ℕ)}
    (h : ∀ i j : ℕ, (i, j) ∈ l → (b.getLsbD i && b.getLsbD j) = false) : pairsOK b l := by
  induction l with
  | nil => trivial
  | cons p l ih =>
    exact ⟨h p.1 p.2 List.mem_cons_self, ih fun i j hij ↦ h i j (List.mem_cons_of_mem p hij)⟩

/-- The colouring constraints on the vertices: each of the first `m` chunks is a nonempty set of
colours. -/
def chunksOK {W : ℕ} (k : ℕ) (b : BitVec W) : ℕ → Prop
  | 0 => True
  | i + 1 => BitVec.extractLsb' (i * k) k b ≠ 0#k ∧ chunksOK k b i

theorem chunksOK_of_forall {W k m : ℕ} {b : BitVec W}
    (h : ∀ i : ℕ, i < m → BitVec.extractLsb' (i * k) k b ≠ 0#k) : chunksOK k b m := by
  induction m with
  | zero => trivial
  | succ i ih => exact ⟨h i (Nat.lt_succ_self i), ih fun j hj ↦ h j (Nat.lt_succ_of_lt hj)⟩

/-- The colouring constraints on the edges: adjacent vertices get disjoint sets of colours. -/
def disjointOK {W : ℕ} (k : ℕ) (b : BitVec W) (l : List (ℕ × ℕ)) : Prop :=
  l.foldr (fun p P ↦
    (BitVec.extractLsb' (p.1 * k) k b &&& BitVec.extractLsb' (p.2 * k) k b) = 0#k ∧ P) True

theorem disjointOK_of_forall {W k : ℕ} {b : BitVec W} {l : List (ℕ × ℕ)}
    (h : ∀ i j : ℕ, (i, j) ∈ l →
      (BitVec.extractLsb' (i * k) k b &&& BitVec.extractLsb' (j * k) k b) = 0#k) :
    disjointOK k b l := by
  induction l with
  | nil => trivial
  | cons p l ih =>
    exact ⟨h p.1 p.2 List.mem_cons_self, ih fun i j hij ↦ h i j (List.mem_cons_of_mem p hij)⟩

/-- **The independence number from a refutation.**  If no `m`-bit vector with no two adjacent bits
set has more than `n` bits set, then `α(G) ≤ n`. -/
theorem indepNum_le_of_bv {G : CGraph} {m n w : ℕ} {es : List (ℕ × ℕ)}
    (hm : FinEnum.card G.V = m) (hes : edgeIdxList G = es)
    (hmw : m < 2 ^ w) (hnw : n < 2 ^ w)
    (h : ∀ b : BitVec m, pairsOK b es → bvCount w b m ≤ BitVec.ofNat w n) :
    G.indepNum ≤ n := by
  subst hm; subst hes
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNIndepSet_indepNum
  set M := FinEnum.card G.V with hM
  set f : ℕ → Bool := fun i ↦ decide (i ∈ s.image vIdx) with hf
  set b : BitVec M := bvOfPred M f M with hb
  have hbit : ∀ v : G.V, b.getLsbD (vIdx v) = decide (v ∈ s) := by
    intro v
    rw [hb, getLsbD_bvOfPred M f (vIdx_lt v) (vIdx_lt v), hf]
    simp only [Finset.mem_image, decide_eq_decide]
    exact ⟨fun ⟨w, hw, hwv⟩ ↦ vIdx_injective hwv ▸ hw, fun hv ↦ ⟨v, hv, rfl⟩⟩
  have hcon : ∀ i j : ℕ, (i, j) ∈ edgeIdxList G → (b.getLsbD i && b.getLsbD j) = false := by
    intro i j hij
    obtain ⟨u, v, huv, hp⟩ := exists_adj_of_mem_edgeIdxList hij
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hp
    have hadj : G.toSimple.Adj u v := by rwa [toSimple_adj]
    rw [hbit u, hbit v]
    by_cases hu : u ∈ s
    · by_cases hv : v ∈ s
      · exact absurd hadj (hs (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hadj.ne)
      · simp [hv]
    · simp [hu]
  have hle := BitVec.le_def.1 (h b (pairsOK_of_forall hcon))
  rw [toNat_bvCount b hmw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw] at hle
  have hset : ((Finset.range M).filter fun i ↦ b.getLsbD i) = s.image vIdx := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hi, hbi⟩
      by_contra hc
      rw [hb, getLsbD_bvOfPred M f hi hi, hf] at hbi
      simp only [decide_eq_true_eq, Finset.mem_image] at hbi
      exact hc hbi
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vIdx_lt v, by rw [hbit v, decide_eq_true hv]⟩
  rw [hset, Finset.card_image_of_injective _ vIdx_injective] at hle
  show G.toSimple.indepNum ≤ n
  rw [← hcard]
  exact hle

/-- **The clique number from a refutation.**  The same statement with the constraints on the
non-edges: a clique is an independent set of the complement. -/
theorem cliqueNum_le_of_bv {G : CGraph} {m n w : ℕ} {es : List (ℕ × ℕ)}
    (hm : FinEnum.card G.V = m) (hes : nonEdgeIdxList G = es)
    (hmw : m < 2 ^ w) (hnw : n < 2 ^ w)
    (h : ∀ b : BitVec m, pairsOK b es → bvCount w b m ≤ BitVec.ofNat w n) :
    G.cliqueNum ≤ n := by
  subst hm; subst hes
  obtain ⟨s, hs, hcard⟩ := G.toSimple.exists_isNClique_cliqueNum
  set M := FinEnum.card G.V with hM
  set f : ℕ → Bool := fun i ↦ decide (i ∈ s.image vIdx) with hf
  set b : BitVec M := bvOfPred M f M with hb
  have hbit : ∀ v : G.V, b.getLsbD (vIdx v) = decide (v ∈ s) := by
    intro v
    rw [hb, getLsbD_bvOfPred M f (vIdx_lt v) (vIdx_lt v), hf]
    simp only [Finset.mem_image, decide_eq_decide]
    exact ⟨fun ⟨w, hw, hwv⟩ ↦ vIdx_injective hwv ▸ hw, fun hv ↦ ⟨v, hv, rfl⟩⟩
  have hcon : ∀ i j : ℕ, (i, j) ∈ nonEdgeIdxList G → (b.getLsbD i && b.getLsbD j) = false := by
    intro i j hij
    obtain ⟨u, v, hne, huv, hp⟩ := exists_not_adj_of_mem_nonEdgeIdxList hij
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hp
    rw [hbit u, hbit v]
    by_cases hu : u ∈ s
    · by_cases hv : v ∈ s
      · have hadj : G.toSimple.Adj u v := hs (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) hne
        rw [toSimple_adj] at hadj
        exact absurd hadj (by rw [huv]; simp)
      · simp [hv]
    · simp [hu]
  have hle := BitVec.le_def.1 (h b (pairsOK_of_forall hcon))
  rw [toNat_bvCount b hmw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnw] at hle
  have hset : ((Finset.range M).filter fun i ↦ b.getLsbD i) = s.image vIdx := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hi, hbi⟩
      by_contra hc
      rw [hb, getLsbD_bvOfPred M f hi hi, hf] at hbi
      simp only [decide_eq_true_eq, Finset.mem_image] at hbi
      exact hc hbi
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vIdx_lt v, by rw [hbit v, decide_eq_true hv]⟩
  rw [hset, Finset.card_image_of_injective _ vIdx_injective] at hle
  show G.toSimple.cliqueNum ≤ n
  rw [← hcard]
  exact hle

/-! ### The chromatic number

A `k`-colouring is `|V|` chunks of `k` bits, the chunk of a vertex being the colours it may take.
Asking each chunk to be nonzero and adjacent chunks to be disjoint is satisfiable exactly when `G`
is `k`-colourable, so a refutation is the lower bound `k < χ(G)`. -/

private theorem idx_lt {M k a r : ℕ} (ha : a < M) (hr : r < k) : a * k + r < M * k :=
  calc a * k + r < a * k + k := by omega
    _ = (a + 1) * k := by ring
    _ ≤ M * k := Nat.mul_le_mul_right k (by omega)

/-- Division with remainder, as the tactic needs it: a bit position determines the vertex whose
chunk it is in and the colour it stands for. -/
private theorem pair_eq {k a r a' r' : ℕ} (hr : r < k) (hr' : r' < k)
    (h : a * k + r = a' * k + r') : a = a' ∧ r = r' := by
  have hk : 0 < k := by omega
  have hd : ∀ x y : ℕ, y < k → (x * k + y) / k = x := fun x y hy ↦ by
    rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hy, Nat.add_zero]
  have ha : a = a' := by rw [← hd a r hr, h, hd a' r' hr']
  subst ha
  exact ⟨rfl, by omega⟩

/-- **The chromatic number from a refutation.**  If no assignment of a nonempty set of `k` colours
to each vertex keeps adjacent sets disjoint, then `k < χ(G)`. -/
theorem lt_chromNum_of_bv {G : CGraph} {m k W : ℕ} {es : List (ℕ × ℕ)}
    (hm : FinEnum.card G.V = m) (hes : edgeIdxList G = es) (hW : m * k = W)
    (h : ∀ b : BitVec W, chunksOK k b m → disjointOK k b es → False) :
    k < G.chromNum := by
  subst hm; subst hes; subst hW
  by_contra hcon
  obtain ⟨c⟩ := chromNum_le_iff_colorable.1 (Nat.le_of_not_lt hcon)
  set M := FinEnum.card G.V with hM
  set f : ℕ → Bool := fun t ↦ decide (∃ v : G.V, t = vIdx v * k + (c v).val) with hf
  set b : BitVec (M * k) := bvOfPred (M * k) f (M * k) with hb
  have hbit : ∀ (v : G.V) (t : ℕ) (ht : t < k),
      b.getLsbD (vIdx v * k + t) = decide (∃ x : G.V, vIdx v * k + t = vIdx x * k + (c x).val) := by
    intro v t ht
    have hlt := idx_lt (vIdx_lt v) ht
    rw [hb, getLsbD_bvOfPred (M * k) f hlt hlt]
  have hvert : ∀ i : ℕ, i < M → BitVec.extractLsb' (i * k) k b ≠ 0#k := by
    intro i hi hzero
    set v : G.V := FinEnum.equiv.symm ⟨i, hi⟩ with hv
    have hvi : vIdx v = i := by rw [hv, vIdx, Equiv.apply_symm_apply]
    have hset : (BitVec.extractLsb' (i * k) k b).getLsbD (c v).val = true := by
      rw [BitVec.getLsbD_extractLsb', decide_eq_true (c v).isLt, Bool.true_and, ← hvi,
        hbit v (c v).val (c v).isLt]
      exact decide_eq_true ⟨v, rfl⟩
    rw [hzero, BitVec.getLsbD_zero] at hset
    exact Bool.noConfusion hset
  have hedge : ∀ i j : ℕ, (i, j) ∈ edgeIdxList G →
      (BitVec.extractLsb' (i * k) k b &&& BitVec.extractLsb' (j * k) k b) = 0#k := by
    intro i j hij
    obtain ⟨u, v, huv, hp⟩ := exists_adj_of_mem_edgeIdxList hij
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hp
    refine BitVec.eq_of_getLsbD_eq fun t ht ↦ ?_
    rw [BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_zero, decide_eq_true ht, Bool.true_and, Bool.true_and,
      hbit u t ht, hbit v t ht]
    by_contra hc
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
    push Not at hc
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hc
    obtain ⟨hxu, hxt⟩ := pair_eq ht (c x).isLt hx
    obtain ⟨hyv, hyt⟩ := pair_eq ht (c y).isLt hy
    have hxu' : x = u := vIdx_injective hxu.symm
    have hyv' : y = v := vIdx_injective hyv.symm
    subst hxu'; subst hyv'
    exact c.valid (by rwa [toSimple_adj]) (Fin.ext (by omega))
  exact h b (chunksOK_of_forall hvert) (disjointOK_of_forall hedge)

/-! ## The tactic

`graph_sat` recognises the six refutation goals

    G.indepNum ≤ n        G.cliqueNum ≤ n        k < G.chromNum
    G.matchNum ≤ n        k < G.edgeChromNum     k < G.cliqueCoverNum

for a *closed* graph `G` — either a `CGraph` or an element of `IsoGraph` that reduces to the class
of one — evaluates the graph once in the elaborator to get its order and its edge list, emits the
propositional encoding above as a `BitVec` statement with everything a literal, and hands that to
`bv_decide`.  `graph_sat native` proves the two side conditions relating the graph to those literals
with `native_decide` instead of `decide`; it is worth reaching for when the vertex type is an
expensive `Finset` or `Sym2` subtype, where reduction in the kernel is the slow step rather than the
SAT call. -/

section Tactic
open Lean Elab Tactic Meta

/-- Compile and run a closed `ℕ`-valued expression. -/
private unsafe def evalNatImpl (e : Expr) : MetaM ℕ := Meta.evalExpr ℕ (.const ``Nat []) e

/-- Evaluate a closed `ℕ`-valued expression.  Only ever called through its `implemented_by`; the
answer is checked by the side conditions of the bridge lemmas, so a wrong one is not unsound. -/
@[implemented_by evalNatImpl]
private def evalNat (_e : Expr) : MetaM ℕ := pure 0

/-- Compile and run a closed expression of type `List (ℕ × ℕ)`. -/
private unsafe def evalPairsImpl (e : Expr) : MetaM (List (ℕ × ℕ)) :=
  Meta.evalExpr (List (ℕ × ℕ))
    (mkApp (.const ``List [0]) (mkApp2 (.const ``Prod [0, 0]) (.const ``Nat []) (.const ``Nat []))) e

/-- Evaluate a closed expression of type `List (ℕ × ℕ)`. -/
@[implemented_by evalPairsImpl]
private def evalPairs (_e : Expr) : MetaM (List (ℕ × ℕ)) := pure []

/-- The names the generated script shares between quotations, so they have to be raw. -/
private def bId : Ident := mkIdent (.mkSimple "b✝gs")
private def keyId : Ident := mkIdent (.mkSimple "key✝gs")

/-- Run the generated script with room to recurse.  Elaborating it descends the chain of
constraints, a handful of stack frames apiece, and past a hundred or so constraints that is more
than the default depth allows; nothing else in the script recurses, so the bound can be generous
and still catch a genuine runaway. -/
private def withDepthFor (n : ℕ) (k : TacticM Unit) : TacticM Unit :=
  withOptions (fun o ↦ o.set `maxRecDepth (Nat.max (maxRecDepth.get o) (512 + 16 * n))) k

/-- The least `w` with `2 ^ w > n`, and at least one: the width of the counter. -/
private def counterWidth (n : ℕ) : ℕ := Nat.max 1 (n + 1).size

/-- `es` as a list literal. -/
private def pairsTerm (es : List (ℕ × ℕ)) : MetaM Term := do
  let elems ← es.toArray.mapM fun (i, j) ↦ `(($(quote i), $(quote j)))
  `([$elems,*])

/-- The unfolding of `bvCount w b m` as a literal addition chain. -/
private def countTerm (w m : ℕ) : MetaM Term := do
  let mut chain ← `(BitVec.ofNat $(quote w) 0)
  for k in [0:m] do
    chain ← `(cond (BitVec.getLsbD $bId $(quote k)) (BitVec.ofNat $(quote w) 1)
      (BitVec.ofNat $(quote w) 0) + $chain)
  return chain

/-- The `bv_decide` goal for `indepNum`/`cliqueNum`: no `m` bits with at most `n` of them set can
avoid every listed pair. -/
private def countStmt (m n w : ℕ) (es : List (ℕ × ℕ)) : MetaM Term := do
  let mut hyp ← `(True)
  for (i, j) in es.reverse do
    hyp ← `((BitVec.getLsbD $bId $(quote i) && BitVec.getLsbD $bId $(quote j)) = false ∧ $hyp)
  `(∀ $bId : BitVec $(quote m), $hyp →
    $(← countTerm w m) ≤ BitVec.ofNat $(quote w) $(quote n))

/-- The `bv_decide` goal for `chromNum`: no assignment of a nonempty set of `k` colours to each of
the `m` vertices keeps the listed pairs disjoint. -/
private def colourStmt (m k W : ℕ) (es : List (ℕ × ℕ)) : MetaM Term := do
  let chunk (i : ℕ) : MetaM Term :=
    `(BitVec.extractLsb' $(quote (i * k)) $(quote k) $bId)
  let mut hedge ← `(True)
  for (i, j) in es.reverse do
    hedge ← `(($(← chunk i) &&& $(← chunk j)) = BitVec.ofNat $(quote k) 0 ∧ $hedge)
  let mut hvert ← `(True)
  for i in [0:m] do
    hvert ← `($(← chunk i) ≠ BitVec.ofNat $(quote k) 0 ∧ $hvert)
  `(∀ $bId : BitVec $(quote W), $hvert → $hedge → False)

/-- Read `FinEnum.card G.V` and the edge (or non-edge) list of `G` off the compiled code. -/
private def graphData (G : Expr) (nonEdges : Bool) : TermElabM (ℕ × List (ℕ × ℕ)) := do
  let g ← Term.exprToSyntax G
  let m ← evalNat (← Term.elabTerm (← `(FinEnum.card ($g : CGraph).V)) none)
  let lst ← if nonEdges then `(CGraph.Sat.nonEdgeIdxList $g) else `(CGraph.Sat.edgeIdxList $g)
  let es ← evalPairs (← Term.elabTerm lst none)
  return (m, es)

/-- If `e : IsoGraph` reduces to the class of a `CGraph`, that `CGraph`. -/
private def repOfIsoGraph (e : Expr) : MetaM (Option Expr) := do
  match (← whnf e).getAppFnArgs with
  | (``Quot.mk, #[_, _, G]) => return some G
  | _ => return none

/-- A natural-number literal, however it is written. -/
private def natOf (e : Expr) : MetaM (Option ℕ) := do
  if let some n := (← whnf e).rawNatLit? then return some n
  if let (``OfNat.ofNat, #[_, l, _]) := e.getAppFnArgs then return l.rawNatLit?
  return none

/-- The invariant a goal is about, together with its graph and the bound. -/
inductive Shape
  | indep (G : Expr) (n : ℕ)
  | clique (G : Expr) (n : ℕ)
  | chrom (G : Expr) (k : ℕ)

/-- Recognise a bound on one of the six invariants, on either level.  The three derived ones are
*definitionally* the invariant of another graph — `χ'` and `ν` of the line graph, `θ` of the
complement — so recognising them is a matter of handing the search that graph instead.  Shared
with the fractional fast path in `IsoGraph/Fractional.lean`, which recognises the same goals. -/
def shapeOf (tgt : Expr) : MetaM (Option Shape) := do
  let asCGraph (e : Expr) : MetaM (Option Expr) := do
    if (← inferType e).isAppOf ``CGraph then return some e else repOfIsoGraph e
  let lineGraphOf (G : Expr) : Expr := mkApp (.const ``CGraph.lineGraph []) G
  let complOf (G : Expr) : Expr := mkApp (.const ``CGraph.compl []) G
  match tgt.getAppFnArgs with
  | (``LE.le, #[_, _, lhs, rhs]) =>
    let some n ← natOf rhs | return none
    match lhs.getAppFnArgs with
    | (``CGraph.indepNum, #[G]) | (``IsoGraph.indepNum, #[G]) =>
      return (← asCGraph G).map (Shape.indep · n)
    | (``CGraph.cliqueNum, #[G]) | (``IsoGraph.cliqueNum, #[G]) =>
      return (← asCGraph G).map (Shape.clique · n)
    | (``CGraph.matchNum, #[G]) | (``IsoGraph.matchNum, #[G]) =>
      return (← asCGraph G).map (fun g ↦ Shape.indep (lineGraphOf g) n)
    | _ => return none
  | (``LT.lt, #[_, _, lhs, rhs]) =>
    let some k ← natOf lhs | return none
    match rhs.getAppFnArgs with
    | (``CGraph.chromNum, #[G]) | (``IsoGraph.chromNum, #[G]) =>
      return (← asCGraph G).map (Shape.chrom · k)
    | (``CGraph.edgeChromNum, #[G]) | (``IsoGraph.edgeChromNum, #[G]) =>
      return (← asCGraph G).map (fun g ↦ Shape.chrom (lineGraphOf g) k)
    | (``CGraph.cliqueCoverNum, #[G]) | (``IsoGraph.cliqueCoverNum, #[G]) =>
      return (← asCGraph G).map (fun g ↦ Shape.chrom (complOf g) k)
    | _ => return none
  | _ => return none

/-- **Prove a bound on the independence, clique or chromatic number with a SAT solver.**

The goal must be one of

    G.indepNum ≤ n        G.cliqueNum ≤ n        k < G.chromNum
    G.matchNum ≤ n        k < G.edgeChromNum     k < G.cliqueCoverNum

for a closed graph `G`; these are the directions that are *refutations*, which is what a SAT
solver decides.  The opposite direction of each — `n ≤ G.indepNum`, `G.chromNum ≤ k` and so on —
is witnessed by an independent set, a clique or a colouring, and is cheap to give explicitly.

`graph_sat native` replaces the `decide` that ties the graph to the emitted literals by
`native_decide`.

`graph_sat (timeout := 300)` raises the solver's own time limit, which `bv_decide` sets to ten
seconds.  Ten is plenty for the refutations that are easy and useless for the ones that are not,
but there is a band in between — a chromatic bound on twenty-odd vertices is a small problem that
the bitvector encoding makes just big enough to run over. -/
syntax (name := graphSat) "graph_sat" (ppSpace &"native")?
  (ppSpace "(" &"timeout" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| graph_sat $[native%$nat]? $[(timeout := $tmo?)]?) => withMainContext do
    let native := nat.isSome
    let some shape ← shapeOf (← whnfR (← (← getMainGoal).getType)) |
      throwError "graph_sat: the goal should be `G.indepNum ≤ n`, `G.cliqueNum ≤ n`, \
        `G.matchNum ≤ n`, `k < G.chromNum`, `k < G.edgeChromNum` or `k < G.cliqueCoverNum` \
        for a closed graph `G`"
    let sideTac : TSyntax `tactic ← if native then `(tactic| native_decide) else `(tactic| decide)
    -- `bv_decide`'s embedded-constraint substitution rewrites every hypothesis with every other
    -- one.  That is quadratic, and on this encoding it finds nothing: the constraints are one per
    -- pair and no two of them share a subterm.  Turning it off is the single largest saving here.
    let satTac : TSyntax `tactic ← match tmo? with
      | some t => `(tactic| bv_decide (config := { timeout := $t }) -embeddedConstraintSubst)
      | none => `(tactic| bv_decide -embeddedConstraintSubst)
    match shape with
    | .indep G n | .clique G n =>
      let isClique := match shape with | .clique .. => true | _ => false
      let (m, es) ← graphData G isClique
      let w := counterWidth (Nat.max m n)
      let stmt ← countStmt m n w es
      let esTerm ← pairsTerm es
      let bridge := mkIdent <|
        if isClique then ``CGraph.Sat.cliqueNum_le_of_bv else ``CGraph.Sat.indepNum_le_of_bv
      withDepthFor es.length <| evalTactic <| ← `(tactic|
        (have $keyId : $stmt := by intros; $satTac:tactic
         exact $bridge (m := $(quote m)) (w := $(quote w)) (es := $esTerm)
           (by $sideTac:tactic) (by $sideTac:tactic) (by decide) (by decide) $keyId))
    | .chrom G k =>
      let (m, es) ← graphData G false
      let stmt ← colourStmt m k (m * k) es
      let esTerm ← pairsTerm es
      withDepthFor (m + es.length) <| evalTactic <| ← `(tactic|
        (have $keyId : $stmt := by intros; $satTac:tactic
         exact CGraph.Sat.lt_chromNum_of_bv (m := $(quote m)) (W := $(quote (m * k)))
           (es := $esTerm) (by $sideTac:tactic) (by $sideTac:tactic) (by decide) $keyId))

end Tactic

end Sat
end CGraph

/-! ## Examples

The five below are the regression tests for the tactic — one per goal shape, on both levels — and
then the one theorem here that is worth stating for its own sake. -/

namespace CGraph

section Examples

example : (kneser 5 2).indepNum ≤ 4 := by graph_sat

example : (IsoGraph.kneser 5 2).indepNum ≤ 4 := by graph_sat

example : (kneser 5 2).cliqueNum ≤ 2 := by graph_sat

/-- The Grötzsch graph is triangle-free and needs four colours. -/
example : 3 < (mycielskian (cycle 5)).chromNum := by graph_sat native

/-- One Mycielskian further: 23 vertices, five colours, and no clique bigger than an edge. -/
example : 4 < (mycielskian (mycielskian (cycle 5))).chromNum := by graph_sat native

/-- **The Petersen graph is a snark**: cubic, and not `3`-edge-colourable.  `SmallGraphs/` proves
this as `four_le_edgeChromNum_petersen`, out of a hand analysis of its perfect matchings. -/
example : 3 < (kneser 5 2).edgeChromNum := by graph_sat native

/-- A matching of the Petersen graph has at most five edges — an independent set of `L(P)`, which
has fifteen vertices. -/
example : (kneser 5 2).matchNum ≤ 5 := by graph_sat native

/-- The Petersen graph is not covered by two cliques. -/
example : 2 < (kneser 5 2).cliqueCoverNum := by graph_sat native

/-- The derived invariants work on the quotient too, and through an `abbrev`. -/
example : 3 < IsoGraph.petersen.edgeChromNum := by graph_sat native

end Examples

/-! ### Erdős–Ko–Rado for `K(7, 3)`

An independent set of `K(n, k)` is a family of pairwise *intersecting* `k`-subsets, and
Erdős–Ko–Rado says that for `n ≥ 2k` the largest one is a star: all the sets through a fixed point,
`C(n - 1, k - 1)` of them.  Nothing here appeals to that: for `K(7, 3)` the upper bound is a
search over `2 ^ 35` subsets that no kernel evaluation will do, and the solver settles it in a few
seconds.  `SmallGraphs.Kneser`, downstream, proves the value for every `n` and `k` out of
`Finset.erdos_ko_rado`; this is the independent check. -/

/-- **Erdős–Ko–Rado for `K(7, 3)`, upper bound**, by SAT. -/
theorem indepNum_kneser_seven_three_le : (kneser 7 3).indepNum ≤ 15 := by graph_sat native

/-- **Erdős–Ko–Rado for `K(7, 3)`, lower bound**: the fifteen triples through `0` pairwise meet. -/
theorem le_indepNum_kneser_seven_three : 15 ≤ (kneser 7 3).indepNum := by
  classical
  set s : Finset (kneser 7 3).V := Finset.univ.filter (fun v ↦ (0 : Fin 7) ∈ v.val) with hs
  have hcard : s.card = 15 := by rw [hs]; decide
  have hind : (kneser 7 3).toSimple.IsIndepSet ↑s := by
    intro u hu v hv _ hadj
    simp only [hs, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hu hv
    rw [toSimple_adj, kneser_adj] at hadj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hadj
    have h0 : (0 : Fin 7) ∈ u.1 ∩ v.1 := Finset.mem_inter.2 ⟨hu, hv⟩
    rw [hadj.2] at h0
    exact absurd h0 (Finset.notMem_empty _)
  show 15 ≤ (kneser 7 3).toSimple.indepNum
  rw [← hcard]
  exact hind.card_le_indepNum

/-- **Erdős–Ko–Rado for `K(7, 3)`.** -/
theorem indepNum_kneser_seven_three : (kneser 7 3).indepNum = 15 :=
  le_antisymm indepNum_kneser_seven_three_le le_indepNum_kneser_seven_three

end CGraph

namespace IsoGraph

/-- **Erdős–Ko–Rado for `K(7, 3)`**, on the quotient. -/
@[simp] theorem indepNum_kneser_seven_three : (kneser 7 3).indepNum = 15 := by
  rw [kneser_def, indepNum_mk, CGraph.indepNum_kneser_seven_three]

end IsoGraph
