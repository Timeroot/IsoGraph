import IsoGraph.Sat
import IsoGraph.Invariants.Fractional

/-!
# Computing the fractional relaxations

`IsoGraph/Invariants/Fractional.lean` defines `α_f` and `χ_f` and proves the bounds; this file
computes them.  The value of the linear program is found outside the kernel, by a rational
simplex, and comes back as a pair of certificates that Lean checks:

* the optimal *dual* solution is a fractional clique cover, and
  `CGraph.Sat.fracIndepNum_le_of_idxCover` turns it into `α_f(G) ≤ q`;
* the optimal *primal* solution is a fractional independent set, and
  `CGraph.Sat.le_fracIndepNum_of_idxWeights` turns it into `q ≤ α_f(G)`.

Both are integer-scaled and both are stated about *indices*, not vertices: as in `graph_sat`, the
only thing said about `G` itself is `FinEnum.card G.V = m` and `edgeIdxList G = es`, and every
other side condition is a closed `Bool` computation over lists of numerals.  That is what keeps
the certificate the small, arithmetic object an LP certificate should be — the same shape
`linarith` and `omega` hand their kernels — instead of a search over `Finset G.V`.  `linarith`
then puts the two halves together into the equation.

    compute_fractional_indepNum (cycle 5)         -- h_fα : (cycle 5).fracIndepNum = 5 / 2
    compute_fractional_chromNum native petersen   -- h_fχ : petersen.fracChromNum = 5 / 2

`compute_fractional_chromNum` is the same computation run on the complement, since that is what
`CGraph.fracChromNum` is.  The primal half is the expensive one — a weighting is feasible when no
clique is overloaded, and there is no way round enumerating the cliques, which `cliqueWeightOK`
does depth-first — so when that enumeration is too large the tactic settles for the upper bound
and adds `h_fα : α_f(G) ≤ q` instead.  As in `graph_sat`, `native` proves the side conditions with
`native_decide`, which is worth an order of magnitude but is no longer the difference between
seconds and not finishing.

The linear program is over the *maximal* cliques, enumerated by Bron–Kerbosch: a constraint on a
clique that sits inside another is implied by it, so the smaller ones can be dropped.  The
simplex runs Bland's rule on the tableau of the packing program, whose slack basis is feasible to
start with, so no first phase is needed.  Everything here is metacode: a wrong answer cannot make
Lean accept a wrong theorem, it can only fail to produce one.

The last section puts the same bound in front of `graph_sat`, where integrality turns
`α_f(G) ≤ 5/2` into `α(G) ≤ 2` with no search at all, on any graph whose program the simplex
can solve and whose relaxation is tight enough to answer the question.
-/

set_option autoImplicit false

/-- Whether `graph_sat` tries the fractional relaxation before the SAT search.  Turning it off
restores the behaviour of `IsoGraph/Sat.lean` on its own. -/
register_option graph_sat.frac : Bool := {
  defValue := true
  descr := "in graph_sat, try the fractional relaxation and integrality before the SAT search"
}

namespace CGraph
namespace Sat

/-! ## The certificates, at the level of indices

`CGraph.fracIndepNum_le_of_natCover` and `CGraph.le_fracIndepNum_of_natWeights` are the bounds a
solved linear program gives, but their hypotheses quantify over `Finset G.V`, and a `Finset G.V`
is an expensive thing to ask a kernel about: the vertex type may be a subtype, a sum or a
`Finset`, and every membership test drags `FinEnum.equiv` and a `DecidableEq` instance behind it.

So the tactic never states its certificate that way.  It does what `graph_sat` does: prove
`FinEnum.card G.V = m` and `edgeIdxList G = es` once, and phrase everything else as a closed
`Bool` computation over `List ℕ` and `List (ℕ × ℕ)`, where the arithmetic is the kernel's own.
The two bridges below are what carries such a computation back to the real statement. -/

section Certificates
open Finset

/-! ### Adjacency at the level of indices -/

/-- Adjacency read off an edge-index list: the pair in one order or the other. -/
def AdjIdx (es : List (ℕ × ℕ)) (i j : ℕ) : Bool := es.contains (i, j) || es.contains (j, i)

theorem adj_of_adjIdx {G : CGraph} {u v : G.V}
    (h : AdjIdx (edgeIdxList G) (vIdx u) (vIdx v) = true) : G.Adj u v = true := by
  have hmem : (vIdx u, vIdx v) ∈ edgeIdxList G ∨ (vIdx v, vIdx u) ∈ edgeIdxList G := by
    rw [AdjIdx, Bool.or_eq_true] at h
    simpa using h
  rcases hmem with hm | hm
  · obtain ⟨u', v', hadj, hp⟩ := exists_adj_of_mem_edgeIdxList hm
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hp
    rw [vIdx_injective h1, vIdx_injective h2]
    exact hadj
  · obtain ⟨u', v', hadj, hp⟩ := exists_adj_of_mem_edgeIdxList hm
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hp
    rw [vIdx_injective h1, vIdx_injective h2, G.symm]
    exact hadj

theorem adjIdx_of_adj {G : CGraph} {u v : G.V} (huv : u ≠ v) (h : G.Adj u v = true) :
    AdjIdx (edgeIdxList G) (vIdx u) (vIdx v) = true := by
  have key : ∀ x y : G.V, G.Adj x y = true → vIdx x < vIdx y →
      (vIdx x, vIdx y) ∈ edgeIdxList G := by
    intro x y hxy hlt
    refine List.mem_flatMap.2 ⟨x, FinEnum.mem_toList x, List.mem_filterMap.2 ⟨y, ?_, ?_⟩⟩
    · exact FinEnum.mem_toList y
    · rw [if_pos ⟨hxy, hlt⟩]
  have hne : vIdx u ≠ vIdx v := fun he ↦ huv (vIdx_injective he)
  rw [AdjIdx, Bool.or_eq_true]
  rcases Nat.lt_or_ge (vIdx u) (vIdx v) with hlt | hge
  · exact Or.inl (by simpa using key u v h hlt)
  · have hlt : vIdx v < vIdx u := by omega
    exact Or.inr (by simpa using key v u ((G.symm u v) ▸ h) hlt)

/-! ### The cover certificate -/

/-- Whether the indices in `K` are pairwise adjacent in `es`. -/
def IsCliqueIdx (es : List (ℕ × ℕ)) (K : List ℕ) : Bool :=
  K.all fun i ↦ K.all fun j ↦ (i == j) || AdjIdx es i j

/-- The total weight the weighted family `Kas` puts on the index `i`. -/
def coverWeight (Kas : List (List ℕ × ℕ)) (i : ℕ) : ℕ :=
  (Kas.map fun p ↦ if p.1.contains i then p.2 else 0).sum

/-- Whether `Kas` is a fractional clique cover of scale `d` of the `m` indices: every set carrying
weight is a clique, and every index is covered to total weight at least `d`. -/
def IsIdxCover (m d : ℕ) (es : List (ℕ × ℕ)) (Kas : List (List ℕ × ℕ)) : Bool :=
  (Kas.all fun p ↦ (p.2 == 0) || IsCliqueIdx es p.1) &&
    (List.range m).all fun i ↦ d ≤ coverWeight Kas i

/-- A sum over `Fin l.length` of a function of the entries is the sum of `l.map f`. -/
private theorem sum_fin_get {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f l[(i : ℕ)] = (l.map f).sum := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]

/-- **The dual certificate, checked on indices.**  A weighted list of index sets that `IsIdxCover`
accepts is a fractional clique cover of `G`, so it bounds `α_f(G)` above by `(∑ weights) / d`. -/
theorem fracIndepNum_le_of_idxCover {G : CGraph} {m d s : ℕ} {es : List (ℕ × ℕ)}
    {Kas : List (List ℕ × ℕ)} (hm : FinEnum.card G.V = m) (hes : edgeIdxList G = es)
    (hd : 0 < d) (hchk : IsIdxCover m d es Kas = true)
    (hs : (Kas.map Prod.snd).sum = s) :
    G.fracIndepNum ≤ (s : ℝ) / (d : ℝ) := by
  subst hes; subst hm; subst hs
  rw [IsIdxCover, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hchk
  obtain ⟨hcl, hcov⟩ := hchk
  refine fracIndepNum_le_of_natCover (G := G) hd
    (K := fun i : Fin Kas.length ↦
      Finset.univ.filter fun v ↦ Kas[(i : ℕ)].1.contains (vIdx v) = true)
    (a := fun i ↦ Kas[(i : ℕ)].2) (sum_fin_get Kas Prod.snd) ?_ ?_
  · intro i hi
    have h := hcl Kas[(i : ℕ)] (List.getElem_mem i.isLt)
    rw [Bool.or_eq_true] at h
    have hcl' : IsCliqueIdx (edgeIdxList G) Kas[(i : ℕ)].1 = true := by
      rcases h with h0 | h1
      · exact absurd (by simpa using h0) hi
      · exact h1
    intro u hu w hw huw
    simp only [Finset.mem_filter] at hu hw
    rw [IsCliqueIdx, List.all_eq_true] at hcl'
    have hmu : vIdx u ∈ Kas[(i : ℕ)].1 := by simpa using hu.2
    have hmw : vIdx w ∈ Kas[(i : ℕ)].1 := by simpa using hw.2
    have h2 := List.all_eq_true.1 (hcl' _ hmu) _ hmw
    rw [Bool.or_eq_true] at h2
    rcases h2 with he | hadj
    · exact absurd (vIdx_injective (by simpa using he)) huw
    · exact adj_of_adjIdx hadj
  · intro v
    have hv : vIdx v ∈ List.range (FinEnum.card G.V) := List.mem_range.2 (vIdx_lt v)
    have h : d ≤ coverWeight Kas (vIdx v) := of_decide_eq_true (hcov _ hv)
    refine le_trans h (le_of_eq ?_)
    rw [coverWeight, ← sum_fin_get]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp

/-! ### The weighting certificate -/

/-- The members of `l` adjacent to `i`.  A definition of its own rather than the `List.filter` it
unfolds to, so that the recursion below sees an opaque argument. -/
def nbrsIn (es : List (ℕ × ℕ)) (i : ℕ) (l : List ℕ) : List ℕ := l.filter (AdjIdx es i)

theorem mem_nbrsIn {es : List (ℕ × ℕ)} {i j : ℕ} {l : List ℕ} (hj : j ∈ l)
    (hadj : AdjIdx es i j = true) : j ∈ nbrsIn es i l := List.mem_filter.2 ⟨hj, hadj⟩

/-- Whether every clique of `es` inside `cand` weighs at most `d` once the weight `acc` already
accumulated is added: a depth-first enumeration of the cliques extending the current one, which
is what makes the feasibility of a weighting a finite check.

The recursion is on a fuel rather than on `cand.length` because a well-founded definition is one
the kernel cannot unfold, and `decide` is half the point.  Any fuel at least `cand.length` gives
the same answer; running out returns `false`, so the check is never wrongly passed. -/
def cliqueWeightOK (es : List (ℕ × ℕ)) (b : List ℕ) (d : ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, cand, acc => cand.isEmpty && decide (acc ≤ d)
  | fuel + 1, cand, acc =>
      match cand with
      | [] => decide (acc ≤ d)
      | i :: rest =>
          cliqueWeightOK es b d fuel rest acc &&
            cliqueWeightOK es b d fuel (nbrsIn es i rest) (acc + b.getD i 0)

theorem cliqueWeightOK_spec {es : List (ℕ × ℕ)} {b : List ℕ} {d : ℕ} (fuel : ℕ) :
    ∀ (cand : List ℕ) (acc : ℕ), cliqueWeightOK es b d fuel cand acc = true →
      ∀ C : Finset ℕ, (∀ i ∈ C, i ∈ cand) →
        (∀ i ∈ C, ∀ j ∈ C, i ≠ j → AdjIdx es i j = true) →
        acc + ∑ i ∈ C, b.getD i 0 ≤ d := by
  induction fuel with
  | zero =>
    intro cand acc h C hC _
    rw [cliqueWeightOK, Bool.and_eq_true] at h
    obtain ⟨hnil, hle⟩ := h
    rw [List.isEmpty_iff] at hnil
    subst hnil
    have hC' : C = ∅ := Finset.eq_empty_of_forall_notMem fun i hi ↦ by simpa using hC i hi
    subst hC'
    simpa using of_decide_eq_true hle
  | succ fuel ih =>
    rintro (_ | ⟨i, rest⟩) acc h C hC hadj
    · simp only [cliqueWeightOK] at h
      have hC' : C = ∅ := Finset.eq_empty_of_forall_notMem fun i hi ↦ by simpa using hC i hi
      subst hC'
      simpa using of_decide_eq_true h
    · simp only [cliqueWeightOK, Bool.and_eq_true] at h
      by_cases hi : i ∈ C
      · have hsub : ∀ j ∈ C.erase i, j ∈ nbrsIn es i rest := by
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          have hjC : j ∈ C := Finset.mem_of_mem_erase hj
          refine mem_nbrsIn ?_ (hadj i hi j hjC (Ne.symm hji))
          rcases List.mem_cons.1 (hC j hjC) with rfl | hr
          · exact absurd rfl hji
          · exact hr
        have key := ih _ _ h.2 (C.erase i) hsub
          (fun x hx y hy hxy ↦
            hadj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
        have hsum : ∑ x ∈ C, b.getD x 0 = b.getD i 0 + ∑ x ∈ C.erase i, b.getD x 0 :=
          (Finset.add_sum_erase _ _ hi).symm
        omega
      · refine ih _ _ h.1 C (fun j hj ↦ ?_) hadj
        rcases List.mem_cons.1 (hC j hj) with rfl | hr
        · exact absurd hj hi
        · exact hr

private theorem sum_getD_fin {n : ℕ} (b : List ℕ) (h : b.length = n) :
    ∑ i : Fin n, b.getD (i : ℕ) 0 = b.sum := by
  subst h
  have hb : ∑ i : Fin b.length, b[(i : ℕ)] = b.sum := by simp
  rw [← hb]
  exact Finset.sum_congr rfl fun i _ ↦ by simp

/-- **The primal certificate, checked on indices.**  A list of natural weights, one per index,
that no clique of `es` overloads is a feasible fractional independent set of `G` at scale `d`, so
it bounds `α_f(G)` below by `(∑ b) / d`.  Unlike the cover, this one has to look at *every*
clique, which is what `cliqueWeightOK` enumerates. -/
theorem le_fracIndepNum_of_idxWeights {G : CGraph} {m d s : ℕ} {es : List (ℕ × ℕ)} {b : List ℕ}
    (hm : FinEnum.card G.V = m) (hes : edgeIdxList G = es) (hd : 0 < d) (hlen : b.length = m)
    (hchk : cliqueWeightOK es b d m (List.range m) 0 = true) (hs : b.sum = s) :
    (s : ℝ) / (d : ℝ) ≤ G.fracIndepNum := by
  subst hes; subst hs
  refine le_fracIndepNum_of_natWeights (G := G) hd (fun v ↦ b.getD (vIdx v) 0) ?_ ?_
  · rw [← sum_getD_fin b (hlen.trans hm.symm)]
    exact Fintype.sum_equiv (FinEnum.equiv (α := G.V)) _ _ (fun v ↦ rfl)
  · intro K hK
    have hmem : ∀ i ∈ K.image vIdx, i ∈ List.range m := by
      intro i hi
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hi
      exact List.mem_range.2 (hm ▸ vIdx_lt v)
    have hpair : ∀ i ∈ K.image vIdx, ∀ j ∈ K.image vIdx, i ≠ j →
        AdjIdx (edgeIdxList G) i j = true := by
      intro i hi j hj hij
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hj
      have hne : u ≠ w := fun he ↦ hij (by rw [he])
      exact adjIdx_of_adj hne (hK u hu w hw hne)
    have key := cliqueWeightOK_spec m (List.range m) 0 hchk (K.image vIdx) hmem hpair
    rw [Finset.sum_image (fun x _ y _ h ↦ vIdx_injective h)] at key
    simpa using key

end Certificates

end Sat

namespace FracLP

/-! ## Maximal cliques -/

/-- The adjacency matrix of a graph given by its edge list of indices. -/
def adjMatrix (n : ℕ) (es : List (ℕ × ℕ)) : Array (Array Bool) := Id.run do
  let mut a : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for (i, j) in es do
    if i < n && j < n then
      a := a.modify i (·.set! j true)
      a := a.modify j (·.set! i true)
  return a

private def nbr (adj : Array (Array Bool)) (u v : ℕ) : Bool :=
  (adj.getD u #[]).getD v false

/-- Bron–Kerbosch with pivoting: every maximal clique of `adj`, as a sorted array of indices. -/
private partial def bkAux (adj : Array (Array Bool)) (R : List ℕ) (P X : List ℕ)
    (limit : ℕ) (acc : Array (Array ℕ)) : Array (Array ℕ) :=
  if acc.size > limit then acc
  else if P.isEmpty && X.isEmpty then acc.push (R.toArray.qsort (· < ·))
  else Id.run do
    let pivot : Option ℕ := (P ++ X).foldl (fun best u ↦
      let d := (P.filter (fun v ↦ nbr adj u v)).length
      match best with
      | none => some (u, d)
      | some (bu, bd) => if d > bd then some (u, d) else some (bu, bd)) none
      |>.map Prod.fst
    let ext := match pivot with
      | none => P
      | some u => P.filter (fun v ↦ !nbr adj u v)
    let mut P := P
    let mut X := X
    let mut acc := acc
    for v in ext do
      if acc.size > limit then break
      acc := bkAux adj (v :: R) (P.filter (nbr adj v)) (X.filter (nbr adj v)) limit acc
      P := P.erase v
      X := v :: X
    return acc

/-- The maximal cliques of a graph on `n` vertices, abandoned once there are more than `limit` of
them: the caller has a cap anyway, and a dense complement can have exponentially many. -/
def maximalCliques (n : ℕ) (adj : Array (Array Bool)) (limit : ℕ) : Array (Array ℕ) :=
  bkAux adj [] (List.range n) [] limit #[]

/-! ## An exact rational simplex

The packing program `max ∑ x` subject to `x ≥ 0` and `∑_{v ∈ K} x v ≤ 1` for every maximal
clique `K`.  Its right-hand side is positive, so the slack basis is feasible and one phase
suffices; Bland's rule keeps it from cycling. -/

/-- An optimal pair for the packing program: the vertex weights, the clique weights and their
common value. -/
structure Solution where
  /-- The optimal primal solution: a weight for each vertex. -/
  x : Array Rat
  /-- The optimal dual solution: a weight for each maximal clique. -/
  y : Array Rat
  /-- The common optimal value. -/
  val : Rat

private def pivotAt (T : Array (Array Rat)) (rows i e : ℕ) : Array (Array Rat) := Id.run do
  let piv := (T.getD i #[]).getD e 0
  let mut T := T.modify i (·.map (· / piv))
  let rowI := T.getD i #[]
  for k in [0:rows] do
    if k != i then
      let f := (T.getD k #[]).getD e 0
      if f != 0 then
        T := T.modify k (fun row ↦ row.mapIdx (fun j v ↦ v - f * rowI.getD j 0))
  return T

private partial def pivotLoop (n m cols : ℕ) (T : Array (Array Rat)) (basis : Array ℕ)
    (fuel : ℕ) : Option (Array (Array Rat) × Array ℕ) :=
  if fuel = 0 then none else
  let obj := T.getD m #[]
  let entering := (List.range (n + m)).find? (fun j ↦ obj.getD j 0 < 0)
  match entering with
  | none => some (T, basis)
  | some e =>
    let best : Option (ℕ × Rat) := (List.range m).foldl (fun best i ↦
      let a := (T.getD i #[]).getD e 0
      if a ≤ 0 then best
      else
        let r := (T.getD i #[]).getD (cols - 1) 0 / a
        match best with
        | none => some (i, r)
        | some (bi, br) =>
          if r < br || (r == br && basis.getD i 0 < basis.getD bi 0) then some (i, r)
          else best) none
    match best with
    | none => none
    | some (i, _) => pivotLoop n m cols (pivotAt T (m + 1) i e) (basis.set! i e) (fuel - 1)

/-- Solve the packing program on `n` vertices with one constraint per clique. -/
def solve (n : ℕ) (cliques : Array (Array ℕ)) : Option Solution := Id.run do
  let m := cliques.size
  let cols := n + m + 1
  let mut T : Array (Array Rat) := #[]
  for i in [0:m] do
    let mut row : Array Rat := Array.replicate cols 0
    for j in cliques.getD i #[] do
      row := row.set! j 1
    row := row.set! (n + i) 1
    row := row.set! (cols - 1) 1
    T := T.push row
  let mut obj : Array Rat := Array.replicate cols 0
  for j in [0:n] do
    obj := obj.set! j (-1)
  T := T.push obj
  let basis : Array ℕ := (Array.range m).map (n + ·)
  match pivotLoop n m cols T basis (200 + 40 * (n + m)) with
  | none => return none
  | some (fin, fbasis) =>
    let mut x : Array Rat := Array.replicate n 0
    for i in [0:m] do
      let bi := fbasis.getD i 0
      if bi < n then
        x := x.set! bi ((fin.getD i #[]).getD (cols - 1) 0)
    let mut y : Array Rat := Array.replicate m 0
    for i in [0:m] do
      y := y.set! i ((fin.getD m #[]).getD (n + i) 0)
    return some ⟨x, y, (fin.getD m #[]).getD (cols - 1) 0⟩

/-- Check an answer of `FracLP.solve` before building a proof out of it: both solutions
nonnegative and feasible, with equal objective values. -/
def Solution.valid (s : Solution) (n : ℕ) (cliques : Array (Array ℕ)) : Bool := Id.run do
  if s.x.size != n || s.y.size != cliques.size then return false
  if s.x.any (· < 0) || s.y.any (· < 0) then return false
  for i in [0:cliques.size] do
    let K := cliques.getD i #[]
    if K.foldl (fun acc j ↦ acc + s.x.getD j 0) 0 > 1 then return false
  for j in [0:n] do
    let mut tot : Rat := 0
    for i in [0:cliques.size] do
      if (cliques.getD i #[]).contains j then tot := tot + s.y.getD i 0
    if tot < 1 then return false
  if s.x.foldl (· + ·) 0 != s.val || s.y.foldl (· + ·) 0 != s.val then return false
  return true

/-- Clear the denominators of a list of nonnegative rationals: the common denominator and the
scaled numerators. -/
def clearDenom (q : Array Rat) : ℕ × Array ℕ :=
  let d := q.foldl (fun acc r ↦ Nat.lcm acc r.den) 1
  (d, q.map (fun r ↦ (r.num * (d : Int) / (r.den : Int)).toNat))

/-! ## The tactics -/

section Tactic
open Lean Elab Tactic Meta

/-- `set_option trace.graph_sat.frac true` reports the size of each program, how long it took to
read the graph and to solve it, and which way the fast path below went. -/
initialize registerTraceClass `graph_sat.frac

/-- Compile and run a closed `ℕ`-valued expression. -/
private unsafe def evalNatImpl (e : Expr) : MetaM ℕ := Meta.evalExpr ℕ (.const ``Nat []) e

/-- Evaluate a closed `ℕ`-valued expression.  As in `IsoGraph/Sat.lean`, only ever called through
its `implemented_by`; a wrong answer cannot make the certificate check out. -/
@[implemented_by evalNatImpl]
private def evalNat (_e : Expr) : MetaM ℕ := pure 0

/-- Compile and run a closed expression of type `List (ℕ × ℕ)`. -/
private unsafe def evalPairsImpl (e : Expr) : MetaM (List (ℕ × ℕ)) :=
  Meta.evalExpr (List (ℕ × ℕ))
    (mkApp (.const ``List [0])
      (mkApp2 (.const ``Prod [0, 0]) (.const ``Nat []) (.const ``Nat []))) e

/-- Evaluate a closed expression of type `List (ℕ × ℕ)`. -/
@[implemented_by evalPairsImpl]
private def evalPairs (_e : Expr) : MetaM (List (ℕ × ℕ)) := pure []

/-- The order and the edge list of a graph written as a term. -/
private def graphData (g : Term) : TermElabM (ℕ × List (ℕ × ℕ)) := do
  let n ← evalNat (← Term.elabTerm (← `(FinEnum.card ($g : CGraph).V)) none)
  let es ← evalPairs (← Term.elabTerm (← `(CGraph.Sat.edgeIdxList ($g : CGraph))) none)
  return (n, es)

/-- A list of natural number literals. -/
private def natListTerm (a : Array ℕ) : MetaM Term := do
  let elems ← a.mapM fun v ↦ `($(quote v))
  `([$elems,*])

/-- A list of pairs of natural number literals. -/
private def pairsTerm (es : List (ℕ × ℕ)) : MetaM Term := do
  let elems ← es.toArray.mapM fun (i, j) ↦ `(($(quote i), $(quote j)))
  `([$elems,*])

/-- A weighted family of index sets, as the literal `[([0, 1], 2), …]` the cover bridge takes. -/
private def coverTerm (Kas : Array (Array ℕ × ℕ)) : MetaM Term := do
  let elems ← Kas.mapM fun (K, a) ↦ do `(($(← natListTerm K), $(quote a)))
  `([$elems,*])

/-- A nonnegative rational as a real literal. -/
private def ratTerm (q : Rat) : MetaM Term :=
  if q.den == 1 then `(($(quote q.num.toNat) : ℝ))
  else `((($(quote q.num.toNat) : ℝ)) / (($(quote q.den) : ℝ)))

/-- How many nodes the kernel's depth-first clique enumeration would visit, abandoned once that
passes `limit`.  This is exactly the recursion `CGraph.Sat.cliqueWeightOK` runs, counted outside
the kernel first: it is the cost of the primal half of the certificate, and it is the one thing
here that can be exponential. -/
private partial def dfsNodes (adj : Array (Array Bool)) (limit : ℕ) (cand : List ℕ)
    (acc : ℕ) : ℕ :=
  if acc > limit then acc
  else match cand with
    | [] => acc + 1
    | i :: rest => dfsNodes adj limit (rest.filter (nbr adj i)) (dfsNodes adj limit rest (acc + 1))

/-- Everything the elaborator learned about a graph: its order, its edges, its maximal cliques,
and the optimal pair of the packing program over them. -/
private structure Data where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges, as pairs of vertex indices; the certificates are stated against this list. -/
  es : List (ℕ × ℕ)
  /-- The maximal cliques, as sorted arrays of vertex indices. -/
  cliques : Array (Array ℕ)
  /-- A verified optimal pair for the packing program. -/
  sol : Solution

/-- Run the linear program for `α_f(g)`, giving up rather than failing: `none` if the graph has no
vertices, if it has more than `maxCliques` maximal cliques, if the tableau those would make is too
big, or if the simplex does not come back with a pair that checks out. -/
private def lpData (g : Term) (maxCliques : ℕ) : TermElabM (Option Data) := do
  let t0 ← IO.monoMsNow
  let (n, es) ← graphData g
  let t1 ← IO.monoMsNow
  if n == 0 || n > 200 then return none
  let cliques := maximalCliques n (adjMatrix n es) maxCliques
  if cliques.size > maxCliques || n * cliques.size > 60000 then return none
  let some sol := solve n cliques | return none
  let t2 ← IO.monoMsNow
  trace[graph_sat.frac] "{n} vertices, {cliques.size} cliques: {t1 - t0} ms reading, \
    {t2 - t1} ms solving"
  return if sol.valid n cliques then some ⟨n, es, cliques, sol⟩ else none

/-- The tactic that ties the emitted literals to the graph: `decide`, or `native_decide` when the
vertex type is one the kernel is slow on.  A complement or a `Finset` subtype is usually the
point at which it becomes worth it. -/
private def sideTac (native : Bool) : MetaM (TSyntax `tactic) :=
  if native then `(tactic| native_decide) else `(tactic| decide)

/-- The dual half of the certificate: a term proving `α_f(g) ≤ q`, built from the cliques the
optimal cover actually uses, with their weights cleared of denominators.  Two `decide`s tie the
literals to the graph and one checks the cover; the rest is numerals. -/
private def upperTerm (g : Term) (D : Data) (native : Bool) : TermElabM Term := do
  let used := (Array.range D.cliques.size).filter (fun i ↦ D.sol.y.getD i 0 != 0)
  let (d, ay) := clearDenom (used.map (D.sol.y.getD · 0))
  let cover ← coverTerm <| (Array.range used.size).map fun k ↦
    (D.cliques.getD (used.getD k 0) #[], ay.getD k 0)
  let esT ← pairsTerm D.es
  let s := ay.foldl (· + ·) 0
  let tac ← sideTac native
  `(CGraph.Sat.fracIndepNum_le_of_idxCover (G := $g) (m := $(quote D.n)) (d := $(quote d))
    (s := $(quote s)) (es := $esT) (Kas := $cover)
    (by $tac:tactic) (by $tac:tactic) (by norm_num) (by $tac:tactic) (by decide))

/-- The primal half of the certificate: a term proving `q ≤ α_f(g)` from the optimal vertex
weights.  Feasibility means no clique of `g` is overloaded, and there is no way round looking at
all of them, so this is only offered when the depth-first enumeration is small — see
`dfsNodes`. -/
private def lowerTerm (g : Term) (D : Data) (native : Bool) : TermElabM (Option Term) := do
  let nodes := dfsNodes (adjMatrix D.n D.es) 20000 (List.range D.n) 0
  if nodes > 20000 then
    trace[graph_sat.frac] "the clique enumeration has more than {nodes} nodes; no lower bound"
    return none
  let (bd, bx) := clearDenom D.sol.x
  let bTerm ← natListTerm bx
  let esT ← pairsTerm D.es
  let sb := bx.foldl (· + ·) 0
  let tac ← sideTac native
  trace[graph_sat.frac] "the clique enumeration has {nodes} nodes"
  some <$> `(CGraph.Sat.le_fracIndepNum_of_idxWeights (G := $g) (m := $(quote D.n))
    (d := $(quote bd)) (s := $(quote sb)) (es := $esT) (b := $bTerm)
    (by $tac:tactic) (by $tac:tactic) (by norm_num) (by decide) (by $tac:tactic) (by decide))

/-- The two halves of the certificate for `g`: a term proving `α_f(g) ≤ q`, optionally a term
proving `q ≤ α_f(g)`, and `q` itself. -/
private def certificates (g : Term) (native : Bool) : TermElabM (Term × Option Term × Rat) := do
  let some D ← lpData g 800 |
    throwError "compute_fractional_indepNum: could not solve the linear program for {g}"
  return (← upperTerm g D native, ← lowerTerm g D native, D.sol.val)

/-- **Compute the fractional independence number.**  `compute_fractional_indepNum G` runs the
linear program for `α_f(G)` and adds the value to the context as `h_fα`, with the two halves of
the proof supplied by the optimal primal and dual solutions.  If the primal half is too large to
check, the hypothesis is the upper bound `α_f(G) ≤ q` instead of the equation.
`compute_fractional_indepNum native G` proves the side conditions with `native_decide`. -/
syntax (name := computeFracIndepNum) "compute_fractional_indepNum" (ppSpace &"native")?
  ppSpace term : tactic

/-- **Compute the fractional chromatic number.**  `compute_fractional_chromNum G` is
`compute_fractional_indepNum` on the complement, since `χ_f(G)` is `α_f(Gᶜ)`; the value lands in
the context as `h_fχ`.  The complement is often where `native` becomes necessary: its adjacency is
a conjunction with a disequality, and the kernel is slow on those. -/
syntax (name := computeFracChromNum) "compute_fractional_chromNum" (ppSpace &"native")?
  ppSpace term : tactic

/-- The shared body of the two tactics: `stmt` is the left-hand side of the hypothesis to add,
`g` the graph the program runs on, and `pre` the rewrite that turns the one into the other. -/
private def addValue (g : Term) (stmt : Term) (hname : Ident) (pre : Option (TSyntax `tactic))
    (native : Bool) : TacticM Unit := withMainContext do
  let (upper, lower, val) ← certificates g native
  let q ← ratTerm val
  let preTac : TSyntax `tactic ← match pre with
    | some t => pure t
    | none => `(tactic| skip)
  match lower with
  | some lower =>
    evalTactic <| ← `(tactic|
      have $hname : $stmt = $q := by
        set_option maxRecDepth 100000 in
        (have hub := $upper
         have hlb := $lower
         $preTac:tactic
         norm_num at hub hlb ⊢
         linarith))
  | none =>
    evalTactic <| ← `(tactic|
      have $hname : $stmt ≤ $q := by
        set_option maxRecDepth 100000 in
        (have hub := $upper
         $preTac:tactic
         norm_num at hub ⊢
         linarith))

elab_rules : tactic
  | `(tactic| compute_fractional_indepNum $[native%$nat]? $g:term) => do
    addValue g (← `(($g : CGraph).fracIndepNum)) (mkIdent (.mkSimple "h_fα")) none nat.isSome

elab_rules : tactic
  | `(tactic| compute_fractional_chromNum $[native%$nat]? $g:term) => do
    addValue (← `(($g : CGraph)ᶜ)) (← `(($g : CGraph).fracChromNum))
      (mkIdent (.mkSimple "h_fχ")) (some (← `(tactic| rw [CGraph.fracChromNum_eq_compl])))
      nat.isSome

/-! ### The fast path for `graph_sat`

An upper bound on `α_f` is an upper bound on `α`, and being an integer it can be rounded down: if
the linear program says `α_f(G) ≤ 5/2` then `α(G) ≤ 2` with no search at all.  The same goes for
`ω` through `χ_f`, and hence for `ν` through the line graph.  This is a second elaborator for the
`graph_sat` syntax, tried before the SAT one; when the relaxation is too weak, too big to solve,
or too big to be worth certifying, it stands aside and the SAT search runs as before.

`set_option graph_sat.frac false` turns it off entirely; `worthACertificate` is where the size
limits and the measurements behind them are. -/

/-- Whether the fast path should go on and build a certificate for a program this size.

The limits are empirical, and with the index-level certificates they are no longer tight: the
check is a `decide` over lists of numerals, one pass over the cover and one over the vertices, so
it costs about what reading the graph costs.  The 54-vertex Gray graph is two seconds where the
`Finset`-level certificate had not finished in five minutes.  What is left is the linear program
and the literal it turns into, both linear in `n * |cliques|`, and being wrong here is only ever
slow, never unsound. -/
private def worthACertificate (D : Data) : Bool :=
  D.n ≤ 120 && D.cliques.size ≤ 300

/-- Close a goal `G.indepNum ≤ n`, or `G.cliqueNum ≤ n` when `dual` is set, by rounding down the
fractional bound.  Fails if the program is out of reach or its value is at least `n + 1`. -/
private def roundDown (g : Term) (n : ℕ) (dual native : Bool) : TacticM Unit := do
  let lp ← if dual then `(($g)ᶜ) else pure g
  let some D ← lpData lp 300 | throwUnsupportedSyntax
  unless worthACertificate D do
    trace[graph_sat.frac] "the program is larger than the fast path takes on; leaving it to SAT"
    throwUnsupportedSyntax
  if D.sol.val ≥ (n : Rat) + 1 then
    trace[graph_sat.frac] "the relaxation gives only {D.sol.val}; leaving it to the SAT search"
    throwUnsupportedSyntax
  trace[graph_sat.frac] "closing the goal with the fractional bound {D.sol.val}"
  let upper ← upperTerm lp D native
  let q ← ratTerm D.sol.val
  if dual then
    evalTactic <| ← `(tactic|
      set_option maxRecDepth 100000 in
      (refine CGraph.cliqueNum_le_of_fracChromNum_le (G := $g) (c := $q) ?_ (by norm_num)
       rw [CGraph.fracChromNum_eq_compl]
       have hub := $upper
       norm_num at hub ⊢
       linarith))
  else
    evalTactic <| ← `(tactic|
      set_option maxRecDepth 100000 in
      (refine CGraph.indepNum_le_of_fracIndepNum_le (G := $g) (c := $q) ?_ (by norm_num)
       have hub := $upper
       norm_num at hub ⊢
       linarith))

/-- Close a goal `k < G.chromNum` by rounding *up* the fractional chromatic number, which is the
independence program on the complement.  This one needs the primal half of the certificate, so it
only fires on graphs whose feasibility check is small; it is worth trying because `χ_f` sees
things `ω` does not — `χ_f(C₅) = 5/2` proves `χ(C₅) > 2`, and `χ_f(K(n,k)) = n/k` proves the
Kneser bounds — and because when it fires there is no search at all. -/
private def roundUp (g : Term) (k : ℕ) (native : Bool) : TacticM Unit := do
  let lp ← `(($g)ᶜ)
  let some D ← lpData lp 300 | throwUnsupportedSyntax
  unless worthACertificate D do
    trace[graph_sat.frac] "the program is larger than the fast path takes on; leaving it to SAT"
    throwUnsupportedSyntax
  if D.sol.val ≤ (k : Rat) then
    trace[graph_sat.frac] "the relaxation gives only {D.sol.val}; leaving it to the SAT search"
    throwUnsupportedSyntax
  let some lower ← lowerTerm lp D native | throwUnsupportedSyntax
  trace[graph_sat.frac] "closing the goal with the fractional bound {D.sol.val}"
  let q ← ratTerm D.sol.val
  evalTactic <| ← `(tactic|
    set_option maxRecDepth 100000 in
    (refine CGraph.lt_chromNum_of_lt_fracChromNum (G := $g) (c := $q) (by norm_num) ?_
     rw [CGraph.fracChromNum_eq_compl]
     have hlb := $lower
     norm_num at hlb ⊢
     linarith))

elab_rules : tactic
  | `(tactic| graph_sat $[native%$nat]?) => withMainContext do
    unless (← getOptions).getBool `graph_sat.frac true do throwUnsupportedSyntax
    let native := nat.isSome
    let some shape ← CGraph.Sat.shapeOf (← whnfR (← (← getMainGoal).getType)) |
      throwUnsupportedSyntax
    let st ← saveState
    try
      match shape with
      | .indep G n => roundDown (← Term.exprToSyntax G) n false native
      | .clique G n => roundDown (← Term.exprToSyntax G) n true native
      | .chrom G k => roundUp (← Term.exprToSyntax G) k native
    catch _ =>
      st.restore
      throwUnsupportedSyntax

end Tactic

end FracLP

/-! ## Examples

The regression tests: both entry points on a graph whose value is not an integer, the upper bound
alone on one where the two invariants come apart, and the fast path on each of the three goal
shapes it handles. -/

section Examples

set_option maxHeartbeats 1000000

example : (cycle 5).fracIndepNum = 5 / 2 := by
  compute_fractional_indepNum (cycle 5)
  exact h_fα

example : (cycle 5).fracChromNum = 5 / 2 := by
  compute_fractional_chromNum (cycle 5)
  exact h_fχ

-- The Petersen graph is triangle free and has a perfect matching, so `α_f` is `n / 2` — a whole
-- unit above `α = 4`, which is why the fast path below leaves that one to the SAT search.  Its
-- vertices are two-element `Finset`s, so this is one for `native`.
example : petersen.fracIndepNum = 5 := by
  compute_fractional_indepNum native petersen
  exact h_fα

-- `χ_f(K(n, k)) = n / k`, the theorem that gives the chromatic number of a Kneser graph; the
-- Petersen graph is `K(5, 2)`.
example : petersen.fracChromNum = 5 / 2 := by
  compute_fractional_chromNum native petersen
  exact h_fχ

-- `α(C₅) ≤ 2`, `ω(C₅) ≤ 2` and `χ(C₅) > 2`, none of them with a SAT call, on either level of
-- `decide`.
example : (cycle 5).indepNum ≤ 2 := by graph_sat
example : (cycle 5).cliqueNum ≤ 2 := by graph_sat
example : 2 < (cycle 5).chromNum := by graph_sat
example : (cycle 5).indepNum ≤ 2 := by graph_sat native
example : (cycle 5).cliqueNum ≤ 2 := by graph_sat native
example : 2 < (cycle 5).chromNum := by graph_sat native

end Examples

end CGraph
