import IsoGraph.Enum.All

/-!
# Enumerating connected graphs up to isomorphism

`enumConnCodes n` lists the canonical codes of the connected graphs on `n` vertices, one per
isomorphism class.  It is the same recursion as `enumCodesFast` — extend a graph on `n` vertices by
a new last vertex, canonicalise, deduplicate — with a stronger mask selector:

* the new vertex must have at least one neighbour, so that the extension stays connected
  (`conn_extendCode`);
* the new vertex must have least degree **among the non-cut vertices**.  A connected graph always
  has a non-cut vertex (`exists_nonCut`) and deleting one leaves a connected graph
  (`conn_delAdj`), so the vertex deleted can always be taken to be a non-cut one of least degree,
  and nothing is lost (`connMasks_complete`).

Deciding which vertices are cut vertices needs a connectivity search, done here as a bitmask
breadth-first search (`reachSet`) that is proved both sound and complete: completeness is what
makes "is `u` a cut vertex?" a function of the isomorphism class, which is in turn what lets the
test be combined with the orbit reduction of `symMasks` (`nonCutTest_permMask`).

The result is `enumConnCodes n = (enumCodes n).filter (connTest n)` — the connected part of the
full enumeration, computed without ever looking at a disconnected graph.
-/

namespace CGraph.Enum

open IsoGraph.Canon

set_option autoImplicit false

/-! ## Reachability -/

/-- Reachability in a graph on `Fin n`. -/
abbrev Reach {n : ℕ} (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen fun a b ↦ adj a b = true

/-- Connectivity of an adjacency function.  Vacuously true when `n = 0`. -/
def Conn {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop := ∀ i j, Reach adj i j

theorem reach_symm {n : ℕ} {adj : Fin n → Fin n → Bool} (hs : ∀ i j, adj i j = adj j i)
    {i j : Fin n} (h : Reach adj i j) : Reach adj j i :=
  Relation.ReflTransGen.symmetric (fun _ _ h ↦ by rwa [hs]) h

/-- Reachability transports along a relabelling. -/
theorem reach_map {n : ℕ} {adj adj' : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (h : ∀ a b, adj (σ a) (σ b) = adj' a b) {i j : Fin n} (hr : Reach adj' i j) :
    Reach adj (σ i) (σ j) := by
  induction hr with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail (by rw [h]; exact hab)

theorem conn_map {n : ℕ} {adj adj' : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (h : ∀ a b, adj (σ a) (σ b) = adj' a b) (hc : Conn adj') : Conn adj := fun i j ↦ by
  simpa using reach_map σ h (hc (σ.symm i) (σ.symm j))

/-- Connectivity only depends on the isomorphism class, so it can be read off the canonical
form. -/
theorem conn_canonAdj_iff {n : ℕ} (adj : Fin n → Fin n → Bool) :
    Conn (canonAdj n adj) ↔ Conn adj := by
  constructor
  · exact conn_map (canonPerm n adj) fun _ _ ↦ rfl
  · exact conn_map (canonPerm n adj).symm fun a b ↦ by simp

/-! ## Walks of bounded length -/

/-- `reachIn adj k i j`: there is a walk from `i` to `j` of length at most `k`. -/
def reachIn {n : ℕ} (adj : Fin n → Fin n → Bool) : ℕ → Fin n → Fin n → Prop
  | 0, i, j => i = j
  | k + 1, i, j => reachIn adj k i j ∨ ∃ w, reachIn adj k i w ∧ adj w j = true

theorem reachIn_of_reachIn {n : ℕ} {adj : Fin n → Fin n → Bool} {k : ℕ} {i j : Fin n}
    (h : reachIn adj k i j) : reachIn adj (k + 1) i j := Or.inl h

theorem reach_of_reachIn {n : ℕ} {adj : Fin n → Fin n → Bool} {k : ℕ} {i j : Fin n}
    (h : reachIn adj k i j) : Reach adj i j := by
  induction k generalizing j with
  | zero => exact h ▸ .refl
  | succ k ih =>
      rcases h with h | ⟨w, hw, hwj⟩
      · exact ih h
      · exact (ih hw).tail hwj

theorem exists_reachIn {n : ℕ} {adj : Fin n → Fin n → Bool} {i j : Fin n} (h : Reach adj i j) :
    ∃ k, reachIn adj k i j := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hab ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, Or.inr ⟨_, hk, hab⟩⟩

/-! ## Cut vertices -/

/-- `adj` with every edge at `v` removed. -/
def avoid {n : ℕ} (adj : Fin n → Fin n → Bool) (v : Fin n) (a b : Fin n) : Bool :=
  adj a b && decide (a ≠ v) && decide (b ≠ v)

/-- `v` is **not a cut vertex**: deleting it leaves the rest connected. -/
def NonCut {n : ℕ} (adj : Fin n → Fin n → Bool) (v : Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ v → j ≠ v → Reach (avoid adj v) i j

theorem avoid_symm {n : ℕ} {adj : Fin n → Fin n → Bool} (hs : ∀ i j, adj i j = adj j i)
    (v a b : Fin n) : avoid adj v a b = avoid adj v b a := by
  simp only [avoid, hs a b]
  exact Bool.and_right_comm _ _ _

/-- **Every connected graph has a non-cut vertex**: a vertex farthest from any fixed root will
do, since no shortest path to the root can run through it. -/
theorem exists_nonCut {n : ℕ} {adj : Fin (n + 1) → Fin (n + 1) → Bool}
    (hs : ∀ i j, adj i j = adj j i) (hc : Conn adj) : ∃ v : Fin (n + 1), NonCut adj v := by
  classical
  set r : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩ with hr
  have hex : ∀ j, ∃ k, reachIn adj k r j := fun j ↦ exists_reachIn (hc r j)
  set d : Fin (n + 1) → ℕ := fun j ↦ Nat.find (hex j) with hd
  have hdspec : ∀ j, reachIn adj (d j) r j := fun j ↦ Nat.find_spec (hex j)
  have hdle : ∀ {j : Fin (n + 1)} {k : ℕ}, reachIn adj k r j → d j ≤ k :=
    fun {j k} h ↦ Nat.find_le h
  obtain ⟨v, -, hv⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1))) d ⟨r, Finset.mem_univ _⟩
  refine ⟨v, ?_⟩
  -- everything other than `v` is reachable from `r` without passing through `v`
  have main : ∀ m : ℕ, ∀ u : Fin (n + 1), d u = m → u ≠ v → Reach (avoid adj v) r u := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro u hdu hne
        match m, hdu with
        | 0, hdu =>
            have h : reachIn adj 0 r u := hdu ▸ hdspec u
            exact (h : r = u) ▸ .refl
        | (k + 1), hdu =>
            have h1 : reachIn adj (k + 1) r u := hdu ▸ hdspec u
            have h2 : ¬reachIn adj k r u := fun hk ↦ by have := hdle hk; omega
            rcases h1 with h | ⟨w, hw, hwu⟩
            · exact absurd h h2
            · have hdw : d w ≤ k := hdle hw
              have hwv : w ≠ v := by
                rintro rfl
                have := hv u (Finset.mem_univ _)
                omega
              refine (ih (d w) (by omega) w rfl hwv).tail ?_
              simp [avoid, hwu, hwv, hne]
  intro i j hi hj
  exact (reach_symm (avoid_symm hs v) (main (d i) i rfl hi)).trans (main (d j) j rfl hj)

/-! ## Deleting a vertex -/

/-- The transposition that moves `v` out of the way, to the last position. -/
abbrev swapLast {n : ℕ} (v : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) := Equiv.swap v (Fin.last n)

/-- `adj` with the vertex `v` deleted, as a graph on `Fin n`. -/
def delAdj {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool) (v : Fin (n + 1)) :
    Fin n → Fin n → Bool :=
  restrict fun a b ↦ adj (swapLast v a) (swapLast v b)

/-- The `i`-th surviving vertex, as a vertex of the original graph. -/
abbrev emb {n : ℕ} (v : Fin (n + 1)) (i : Fin n) : Fin (n + 1) := swapLast v i.castSucc

theorem delAdj_apply {n : ℕ} (adj : Fin (n + 1) → Fin (n + 1) → Bool) (v : Fin (n + 1))
    (i j : Fin n) : delAdj adj v i j = adj (emb v i) (emb v j) := rfl

theorem emb_ne {n : ℕ} (v : Fin (n + 1)) (i : Fin n) : emb v i ≠ v := by
  rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  exact (Fin.castSucc_lt_last i).ne

theorem emb_inj {n : ℕ} {v : Fin (n + 1)} {i j : Fin n} (h : emb v i = emb v j) : i = j :=
  Fin.castSucc_injective n ((swapLast v).injective h)

theorem exists_emb {n : ℕ} {v x : Fin (n + 1)} (h : x ≠ v) : ∃ i : Fin n, emb v i = x := by
  have hne : swapLast v x ≠ Fin.last n := by
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact h
  have hlt : (swapLast v x).1 < n := by
    have h1 := (swapLast v x).2
    have h2 : (swapLast v x).1 ≠ n := fun he ↦ hne (Fin.ext he)
    omega
  refine ⟨⟨(swapLast v x).1, hlt⟩, ?_⟩
  show swapLast v (Fin.castSucc ⟨_, hlt⟩) = x
  have hcs : (⟨(swapLast v x).1, hlt⟩ : Fin n).castSucc = swapLast v x := rfl
  rw [hcs, Equiv.swap_apply_self]

/-- Deleting a non-cut vertex leaves a connected graph. -/
theorem conn_delAdj {n : ℕ} {adj : Fin (n + 1) → Fin (n + 1) → Bool} {v : Fin (n + 1)}
    (h : NonCut adj v) : Conn (delAdj adj v) := by
  intro i j
  have aux : ∀ (x : Fin (n + 1)), Reach (avoid adj v) (emb v i) x →
      ∀ j : Fin n, emb v j = x → Reach (delAdj adj v) i j := by
    intro x hx
    induction hx with
    | refl => intro j hj; exact (emb_inj hj.symm : i = j) ▸ .refl
    | @tail b c _ hbc ih =>
        intro j hj
        have hbv : b ≠ v := by
          simp only [avoid, Bool.and_eq_true, decide_eq_true_eq] at hbc
          exact hbc.1.2
        obtain ⟨j', hj'⟩ := exists_emb hbv
        refine (ih j' hj').tail ?_
        simp only [avoid, Bool.and_eq_true] at hbc
        rw [delAdj_apply, hj', hj]
        exact hbc.1.1
  exact aux _ (h _ _ (emb_ne v i) (emb_ne v j)) j rfl

/-! ## Extending a connected graph keeps it connected -/

theorem reach_castSucc {n c s : ℕ} {i j : Fin n} (h : Reach (graphOfCode n c).Adj i j) :
    Reach (graphOfCode (n + 1) (extendCode n c s)).Adj i.castSucc j.castSucc := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
      refine ih.tail ?_
      rwa [adj_extendCode_lt (by simp) (by simp)]

/-- Attaching a new vertex to a nonempty set of vertices of a connected graph gives a connected
graph. -/
theorem conn_extendCode {n c s : ℕ} (hc : Conn (graphOfCode n c).Adj) (hclt : c < 2 ^ n.choose 2)
    {i₀ : Fin n} (hi₀ : s.testBit i₀.1 = true) :
    Conn (graphOfCode (n + 1) (extendCode n c s)).Adj := by
  have hedge : (graphOfCode (n + 1) (extendCode n c s)).Adj i₀.castSucc (Fin.last n) = true := by
    rw [adj_extendCode_last hclt (by simp)]
    exact hi₀
  have hall : ∀ x : Fin (n + 1),
      Reach (graphOfCode (n + 1) (extendCode n c s)).Adj x (Fin.last n) :=
    Fin.lastCases .refl fun i ↦ (reach_castSucc (hc i i₀)).tail hedge
  exact fun a b ↦ (hall a).trans
    (reach_symm (fun i j ↦ (graphOfCode (n + 1) (extendCode n c s)).symm i j) (hall b))

/-! ## Bitmask breadth-first search

Connectivity is tested with a bitmask search: a set of vertices is a natural number, one round of
the search adds the neighbours of everything in it, and the search stops at a fixed point.  Both
directions matter here.  Soundness — everything found really is reachable — keeps the enumerator
from listing a disconnected graph.  Completeness — everything reachable is found — is what makes
the test a *function of the graph up to isomorphism*, which is what lets it be combined with orbit
reduction.  Completeness is why the rounds run to a genuine fixed point rather than a fixed number
of times.
-/

/-- The mask of all `n` vertices. -/
def fullMask (n : ℕ) : ℕ := 2 ^ n - 1

theorem fullMask_lt (n : ℕ) : fullMask n < 2 ^ n :=
  Nat.sub_lt (Nat.two_pow_pos n) one_pos

@[simp] theorem testBit_fullMask (n k : ℕ) : (fullMask n).testBit k = decide (k < n) :=
  Nat.testBit_two_pow_sub_one n k

theorem le_of_testBit_imp {a b : ℕ} (h : ∀ k, a.testBit k = true → b.testBit k = true) : a ≤ b := by
  have hab : a &&& b = a := Nat.eq_of_testBit_eq fun k ↦ by
    rw [Nat.testBit_and]
    cases ha : a.testBit k with
    | false => rw [Bool.false_and]
    | true => rw [h k ha, Bool.and_self]
  exact hab ▸ Nat.and_le_right

theorem testBit_foldl_lor {α : Type} (f : α → ℕ) (p : α → Bool) (k : ℕ) (l : List α) (c : ℕ) :
    (l.foldl (fun c a ↦ if p a then c ||| f a else c) c).testBit k
      = (c.testBit k || l.any fun a ↦ p a && (f a).testBit k) := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.any_cons, ih]
      by_cases hp : p a
      · simp [hp, Nat.testBit_or, Bool.or_assoc]
      · simp [hp]

/-- One round of the search: add the neighbours of everything reached so far.  The result is
masked down to `n` bits, so nothing has to be assumed about `nbr`. -/
def reachStep (n : ℕ) (nbr : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((List.range n).foldl (fun acc i ↦ if m.testBit i then acc ||| nbr i else acc) m) &&& fullMask n

theorem testBit_reachStep (n : ℕ) (nbr : ℕ → ℕ) (m k : ℕ) :
    (reachStep n nbr m).testBit k
      = ((m.testBit k || (List.range n).any fun i ↦ m.testBit i && (nbr i).testBit k)
          && decide (k < n)) := by
  rw [reachStep, Nat.testBit_and, testBit_fullMask, testBit_foldl_lor]

theorem reachStep_lt (n : ℕ) (nbr : ℕ → ℕ) (m : ℕ) : reachStep n nbr m < 2 ^ n :=
  lt_of_le_of_lt Nat.and_le_right (fullMask_lt n)

theorem le_reachStep {n : ℕ} {nbr : ℕ → ℕ} {m : ℕ} (hm : m < 2 ^ n) : m ≤ reachStep n nbr m := by
  refine le_of_testBit_imp fun k hk ↦ ?_
  have hkn : k < n := by
    by_contra hc
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
      (not_lt.1 hc)))] at hk
    exact Bool.noConfusion hk
  rw [testBit_reachStep, hk, Bool.true_or, decide_eq_true hkn, Bool.and_self]

set_option linter.unusedVariables false in
/-- The rounds of the search.  `m'` is always one round on from `m`, so no round is run twice;
the search stops when a round changes nothing.  It terminates because each round that changes
something adds a vertex, and the masks stay below `2 ^ n`. -/
def reachCloseAux (n : ℕ) (nbr : ℕ → ℕ) (m m' : ℕ) (hm' : m' = reachStep n nbr m)
    (hb : m < 2 ^ n) : ℕ :=
  if h : m' = m then m
  else reachCloseAux n nbr m' (reachStep n nbr m') rfl (hm' ▸ reachStep_lt n nbr m)
termination_by 2 ^ n - m
decreasing_by
  have h1 : m ≤ m' := hm' ▸ le_reachStep hb
  have h2 : m' < 2 ^ n := hm' ▸ reachStep_lt n nbr m
  omega

/-- The set of vertices reachable from `m`: run the search to a fixed point. -/
def reachSet (n : ℕ) (nbr : ℕ → ℕ) (m : ℕ) (hb : m < 2 ^ n) : ℕ :=
  reachCloseAux n nbr m (reachStep n nbr m) rfl hb

/-- The search stops at a set closed under taking neighbours. -/
theorem reachCloseAux_fix (n : ℕ) (nbr : ℕ → ℕ) (m m' : ℕ) (hm' : m' = reachStep n nbr m)
    (hb : m < 2 ^ n) :
    reachStep n nbr (reachCloseAux n nbr m m' hm' hb) = reachCloseAux n nbr m m' hm' hb := by
  induction m, m', hm', hb using reachCloseAux.induct with
  | case1 m₁ hm₁ hb₁ => rw [reachCloseAux, dif_pos rfl]; exact hm₁.symm
  | case2 m₁ hb₁ hne ih => rw [reachCloseAux, dif_neg hne]; exact ih

theorem reachStep_reachSet (n : ℕ) (nbr : ℕ → ℕ) (m : ℕ) (hb : m < 2 ^ n) :
    reachStep n nbr (reachSet n nbr m hb) = reachSet n nbr m hb :=
  reachCloseAux_fix n nbr m _ rfl hb

theorem reachCloseAux_lt (n : ℕ) (nbr : ℕ → ℕ) (m m' : ℕ) (hm' : m' = reachStep n nbr m)
    (hb : m < 2 ^ n) : reachCloseAux n nbr m m' hm' hb < 2 ^ n := by
  induction m, m', hm', hb using reachCloseAux.induct with
  | case1 m₁ hm₁ hb₁ => rw [reachCloseAux, dif_pos rfl]; exact hb₁
  | case2 m₁ hb₁ hne ih => rw [reachCloseAux, dif_neg hne]; exact ih

theorem reachSet_lt (n : ℕ) (nbr : ℕ → ℕ) (m : ℕ) (hb : m < 2 ^ n) :
    reachSet n nbr m hb < 2 ^ n := reachCloseAux_lt n nbr m _ rfl hb

/-- Anything preserved by a round of the search holds of its result. -/
theorem reachCloseAux_ind {n : ℕ} {nbr : ℕ → ℕ} (P : ℕ → Prop)
    (hstep : ∀ m, P m → P (reachStep n nbr m)) (m m' : ℕ) (hm' : m' = reachStep n nbr m)
    (hb : m < 2 ^ n) (h : P m) : P (reachCloseAux n nbr m m' hm' hb) := by
  induction m, m', hm', hb using reachCloseAux.induct with
  | case1 m₁ hm₁ hb₁ => rw [reachCloseAux, dif_pos rfl]; exact h
  | case2 m₁ hb₁ hne ih => rw [reachCloseAux, dif_neg hne]; exact ih (hstep m₁ h)

theorem reachSet_ind {n : ℕ} {nbr : ℕ → ℕ} (P : ℕ → Prop)
    (hstep : ∀ m, P m → P (reachStep n nbr m)) (m : ℕ) (hb : m < 2 ^ n) (h : P m) :
    P (reachSet n nbr m hb) := reachCloseAux_ind P hstep m _ rfl hb h

/-- **Soundness**: everything the search reaches really is reachable. -/
theorem reachSet_sound {n : ℕ} {adj : Fin n → Fin n → Bool} {nbr : ℕ → ℕ}
    (hnbr : ∀ a b : Fin n, (nbr a.1).testBit b.1 = true → adj a b = true) {i : Fin n}
    {start : ℕ} {hb : start < 2 ^ n}
    (hstart : ∀ j : Fin n, start.testBit j.1 = true → Reach adj i j) :
    ∀ j : Fin n, (reachSet n nbr start hb).testBit j.1 = true → Reach adj i j := by
  refine reachSet_ind (fun m ↦ ∀ j : Fin n, m.testBit j.1 = true → Reach adj i j) ?_ start hb hstart
  intro m hm j hj
  rw [testBit_reachStep, Bool.and_eq_true] at hj
  rcases Bool.or_eq_true_iff.1 hj.1 with h1 | h1
  · exact hm j h1
  · obtain ⟨a, ha, hab⟩ := List.any_eq_true.1 h1
    rw [Bool.and_eq_true] at hab
    have han : a < n := List.mem_range.1 ha
    exact (hm ⟨a, han⟩ hab.1).tail (hnbr ⟨a, han⟩ j hab.2)

/-- **Completeness**: the search reaches everything reachable — because it stopped at a set closed
under taking neighbours. -/
theorem reachSet_complete {n : ℕ} {adj : Fin n → Fin n → Bool} {nbr : ℕ → ℕ}
    (hnbr : ∀ a b : Fin n, adj a b = true → (nbr a.1).testBit b.1 = true) {i : Fin n}
    {start : ℕ} {hb : start < 2 ^ n} (hstart : start.testBit i.1 = true)
    {j : Fin n} (hr : Reach adj i j) : (reachSet n nbr start hb).testBit j.1 = true := by
  have hfix := reachStep_reachSet n nbr start hb
  have hbase : (reachSet n nbr start hb).testBit i.1 = true := by
    have key : ∀ m : ℕ, m.testBit i.1 = true → (reachStep n nbr m).testBit i.1 = true := by
      intro m hm
      rw [testBit_reachStep, hm, Bool.true_or, decide_eq_true i.2, Bool.and_self]
    exact reachSet_ind (fun m ↦ m.testBit i.1 = true) key start hb hstart
  induction hr with
  | refl => exact hbase
  | tail _ hbc ih =>
      rename_i b c _
      rw [← hfix, testBit_reachStep, Bool.and_eq_true]
      refine ⟨Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨b.1, List.mem_range.2 b.2, ?_⟩)),
        decide_eq_true c.2⟩
      rw [Bool.and_eq_true]
      exact ⟨ih, hnbr b c hbc⟩

/-! ## Connectivity of a coded graph -/

/-- Row `i` of the adjacency matrix of the graph with code `c`, as a bit mask. -/
def rowOfCode (n c i : ℕ) : ℕ := rowMask n fun j ↦ decide (i ≠ j) && c.testBit (pairIdx i j)

theorem rowOfCode_lt (n c i : ℕ) : rowOfCode n c i < 2 ^ n := rowMask_lt _ _

theorem testBit_rowOfCode {n c : ℕ} (i j : Fin n) :
    (rowOfCode n c i.1).testBit j.1 = (graphOfCode n c).Adj i j := by
  rw [rowOfCode, testBit_rowMask _ j.2, graphOfCode_adj]
  simp [Fin.val_inj]

/-- All the rows at once — computed once per graph, then shared by every mask tried on it. -/
def rowsOfCode (n c : ℕ) : Array ℕ := (Array.range n).map (rowOfCode n c)

theorem getD_rowsOfCode {n c i : ℕ} (hi : i < n) :
    (rowsOfCode n c).getD i 0 = rowOfCode n c i := by
  rw [rowsOfCode, Array.getD_eq_getD_getElem?]
  simp [hi]

/-- The vertices of the graph with code `c` reachable from vertex `0`. -/
def compOfCode (n c : ℕ) : ℕ :=
  let rows := rowsOfCode n c
  reachSet n (fun i ↦ rows.getD i 0) (1 &&& fullMask n)
    (lt_of_le_of_lt Nat.and_le_right (fullMask_lt n))

/-- **Is the graph with code `c` connected?**  As for `SimpleGraph.Connected`, the graph with no
vertices is not. -/
def connTest (n c : ℕ) : Bool := decide (0 < n) && (compOfCode n c == fullMask n)

theorem testBit_one_and_fullMask {n k : ℕ} (hn : 0 < n) :
    (1 &&& fullMask n).testBit k = decide (k = 0) := by
  rw [Nat.testBit_and, testBit_fullMask]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hn]
  · have h1 : Nat.testBit 1 k = false := by
      rw [Bool.eq_false_iff, Ne, Nat.testBit_one_eq_true_iff_self_eq_zero]
      omega
    simp [h1, Nat.ne_of_gt hk]

/-- **The test is exactly connectivity** — sound, so the enumerator never lists a disconnected
graph, and complete, so it never drops one. -/
theorem connTest_iff {n c : ℕ} : connTest n c = true ↔ 0 < n ∧ Conn (graphOfCode n c).Adj := by
  have hrow : ∀ i j : Fin n, ((rowsOfCode n c).getD i.1 0).testBit j.1
      = (graphOfCode n c).Adj i j := fun i j ↦ by
    rw [getD_rowsOfCode i.2, testBit_rowOfCode]
  rw [connTest, Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
  constructor
  · rintro ⟨hn, heq⟩
    refine ⟨hn, ?_⟩
    set i₀ : Fin n := ⟨0, hn⟩ with hi₀
    have hall : ∀ j : Fin n, Reach (graphOfCode n c).Adj i₀ j := by
      intro j
      refine reachSet_sound (nbr := fun i ↦ (rowsOfCode n c).getD i 0)
        (start := 1 &&& fullMask n) (hb := lt_of_le_of_lt Nat.and_le_right (fullMask_lt n))
        (fun a b h ↦ (hrow a b) ▸ h) ?_ j ?_
      · intro j hj
        rw [testBit_one_and_fullMask hn, decide_eq_true_iff] at hj
        exact (Fin.ext hj.symm : i₀ = j) ▸ .refl
      · rw [show reachSet n _ _ _ = compOfCode n c from rfl, heq, testBit_fullMask]
        exact decide_eq_true j.2
    exact fun a b ↦ (reach_symm (fun i j ↦ (graphOfCode n c).symm i j) (hall a)).trans (hall b)
  · rintro ⟨hn, hc⟩
    refine ⟨hn, eq_of_testBit_lt (reachSet_lt _ _ _ _) (fullMask_lt n) fun k hk ↦ ?_⟩
    rw [testBit_fullMask, decide_eq_true hk]
    exact reachSet_complete (i := ⟨0, hn⟩) (j := ⟨k, hk⟩)
      (start := 1 &&& fullMask n) (hb := lt_of_le_of_lt Nat.and_le_right (fullMask_lt n))
      (fun a b h ↦ (hrow a b).symm ▸ h)
      (by rw [testBit_one_and_fullMask hn]; rfl) (hc _ _)


/-! ## Testing for a cut vertex in the extension

The extension of the code `c` by a new vertex with neighbourhood `s` is searched directly from
the rows of `c`, which are computed once per graph and shared by every mask tried on it.
-/

/-- The mask of every vertex but `u`. -/
def coMask (n u : ℕ) : ℕ := fullMask n ^^^ 2 ^ u

theorem coMask_lt {n u : ℕ} (hu : u < n) : coMask n u < 2 ^ n :=
  Nat.xor_lt_two_pow (fullMask_lt n) (Nat.pow_lt_pow_right one_lt_two hu)

theorem testBit_coMask {n u k : ℕ} (hk : k < n) : (coMask n u).testBit k = decide (k ≠ u) := by
  rw [coMask, Nat.testBit_xor, testBit_fullMask, Nat.testBit_two_pow, decide_eq_true hk]
  by_cases h : k = u
  · subst h; simp
  · simp [h, (Ne.symm h : u ≠ k)]

/-- Row `i` of the extension of `c` by a new vertex with neighbourhood `s`, with the vertex `u`
deleted.  `rows` are the rows of `c` itself. -/
def delNbr (n : ℕ) (rows : Array ℕ) (s u i : ℕ) : ℕ :=
  if i = u then 0
  else (if i = n then s else rows.getD i 0 ||| (if s.testBit i then 2 ^ n else 0))
        &&& coMask (n + 1) u

/-- What the rows of a graph on `Fin n` are. -/
def RowsSpec (n c : ℕ) (rows : Array ℕ) : Prop :=
  (∀ i j : Fin n, (rows.getD i.1 0).testBit j.1 = (graphOfCode n c).Adj i j) ∧
    ∀ i, rows.getD i 0 < 2 ^ n

theorem rowsSpec_rowsOfCode (n c : ℕ) : RowsSpec n c (rowsOfCode n c) := by
  refine ⟨fun i j ↦ by rw [getD_rowsOfCode i.2, testBit_rowOfCode], fun i ↦ ?_⟩
  by_cases hi : i < n
  · rw [getD_rowsOfCode hi]; exact rowOfCode_lt n c i
  · rw [rowsOfCode, Array.getD_eq_getD_getElem?]
    simp only [Array.getElem?_map, Array.getElem?_range]
    rw [if_neg hi]
    exact Nat.two_pow_pos n

theorem testBit_delNbr {n c s u : ℕ} {rows : Array ℕ} (hrows : RowsSpec n c rows)
    (hc : c < 2 ^ n.choose 2) (hs : s < 2 ^ n) (hu : u < n) (a b : Fin (n + 1)) :
    (delNbr n rows s u a.1).testBit b.1
      = avoid (graphOfCode (n + 1) (extendCode n c s)).Adj ⟨u, by omega⟩ a b := by
  set v : Fin (n + 1) := ⟨u, by omega⟩ with hv
  set B := (graphOfCode (n + 1) (extendCode n c s)).Adj with hB
  have hav : a ≠ v → a.1 ≠ u := fun h hc ↦ h (Fin.ext hc)
  have hbv : decide (b ≠ v) = decide (b.1 ≠ u) := by rw [hv]; simp [Fin.ext_iff]
  by_cases hau : a.1 = u
  · rw [delNbr, if_pos hau, Nat.zero_testBit, avoid]
    have : a = v := Fin.ext hau
    simp [this]
  -- the row itself, before deleting `u`
  have hrow : ∀ x y : Fin (n + 1),
      (if x.1 = n then s else rows.getD x.1 0 ||| (if s.testBit x.1 then 2 ^ n else 0)).testBit y.1
        = B x y := by
    refine Fin.lastCases ?_ ?_
    · refine Fin.lastCases ?_ ?_
      · rw [if_pos (by simp), Fin.val_last, Nat.testBit_lt_two_pow (lt_of_lt_of_le hs
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        simp [hB]
      · intro y
        rw [if_pos (by simp), hB, (graphOfCode (n + 1) (extendCode n c s)).symm,
          adj_extendCode_last hc (show (y.castSucc).1 < n by simp)]
    · intro x
      have hxn : (x.castSucc).1 ≠ n := by rw [Fin.val_castSucc]; exact Nat.ne_of_lt x.2
      refine Fin.lastCases ?_ ?_
      · rw [if_neg hxn, Nat.testBit_or, Fin.val_last, Nat.testBit_lt_two_pow (hrows.2 _),
          Bool.false_or, hB, adj_extendCode_last hc (show (x.castSucc).1 < n by simp)]
        by_cases h : s.testBit x.1 <;> simp [h]
      · intro y
        have hhigh : ((if s.testBit (x.castSucc).1 then 2 ^ n else 0)).testBit
            (y.castSucc).1 = false := by
          by_cases h : s.testBit x.1 <;> simp [h, y.isLt.ne']
        rw [if_neg hxn, Nat.testBit_or, hhigh, Bool.or_false, hB,
          adj_extendCode_lt (show (x.castSucc).1 < n by simp)
            (show (y.castSucc).1 < n by simp)]
        exact hrows.1 x y
  rw [delNbr, if_neg hau, Nat.testBit_and, testBit_coMask b.2, hrow a b, avoid, hbv]
  have hane : a ≠ v := fun h ↦ hau (Fin.ext_iff.1 h)
  simp [hane]

/-- Does deleting the vertex `u` from the extension leave the rest connected? -/
def nonCutTest (n : ℕ) (rows : Array ℕ) (s u : ℕ) : Bool :=
  reachSet (n + 1) (delNbr n rows s u) (2 ^ n)
      (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n))
    == coMask (n + 1) u

theorem not_reach_avoid {n : ℕ} {adj : Fin n → Fin n → Bool} {v i : Fin n}
    (h : Reach (avoid adj v) i v) : i = v := by
  cases h with
  | refl => rfl
  | tail _ hbv => simp [avoid] at hbv

/-- **The cut-vertex test is exact.**  Soundness is what keeps a disconnected graph out of the
list; completeness is what makes the test depend only on the isomorphism class, which is what lets
it be combined with orbit reduction. -/
theorem nonCutTest_iff {n c s u : ℕ} {rows : Array ℕ} (hrows : RowsSpec n c rows)
    (hc : c < 2 ^ n.choose 2) (hs : s < 2 ^ n) (hu : u < n) :
    nonCutTest n rows s u = true
      ↔ NonCut (graphOfCode (n + 1) (extendCode n c s)).Adj ⟨u, by omega⟩ := by
  set v : Fin (n + 1) := ⟨u, by omega⟩ with hv
  set B := (graphOfCode (n + 1) (extendCode n c s)).Adj with hB
  have hsymm : ∀ i j, B i j = B j i := fun i j ↦ (graphOfCode (n + 1) _).symm i j
  have hstart : ∀ j : Fin (n + 1), (2 ^ n).testBit j.1 = true → Reach (avoid B v) (Fin.last n) j :=
    fun j hj ↦ by
      rw [Nat.testBit_two_pow, decide_eq_true_iff] at hj
      exact (Fin.ext (show (Fin.last n).1 = j.1 from hj) : Fin.last n = j) ▸ .refl
  have hlast : Fin.last n ≠ v := by rw [Ne, hv, Fin.ext_iff]; simp; omega
  rw [nonCutTest, beq_iff_eq]
  constructor
  · intro heq
    have hreach : ∀ j : Fin (n + 1), j ≠ v → Reach (avoid B v) (Fin.last n) j := by
      intro j hj
      refine reachSet_sound (adj := avoid B v) (nbr := delNbr n rows s u) (start := 2 ^ n)
        (hb := Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n))
        (fun a b h ↦ ?_) hstart j ?_
      · rw [← testBit_delNbr hrows hc hs hu a b]; exact h
      · rw [heq, testBit_coMask j.2]
        exact decide_eq_true fun h ↦ hj (Fin.ext h)
    exact fun i j hi hj ↦
      (reach_symm (avoid_symm hsymm v) (hreach i hi)).trans (hreach j hj)
  · intro hnc
    refine eq_of_testBit_lt (reachSet_lt _ _ _ _) (coMask_lt (by omega)) fun k hk ↦ ?_
    rw [testBit_coMask hk]
    by_cases hku : k = u
    · subst hku
      rw [decide_eq_false (by simp)]
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      have := reachSet_sound (adj := avoid B v) (i := Fin.last n) (j := v)
        (nbr := delNbr n rows s k) (start := 2 ^ n)
        (hb := Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n))
        (fun a b h ↦ by rw [← testBit_delNbr hrows hc hs hu a b]; exact h) hstart
      exact hlast (not_reach_avoid (this hcon))
    · rw [decide_eq_true hku]
      refine reachSet_complete (adj := avoid B v) (i := Fin.last n) (j := ⟨k, hk⟩)
        (nbr := delNbr n rows s u) (start := 2 ^ n)
        (hb := Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n))
        (fun a b h ↦ by rw [testBit_delNbr hrows hc hs hu a b]; exact h) ?_
        (hnc _ _ hlast fun h ↦ hku (Fin.ext_iff.1 h))
      rw [Nat.testBit_two_pow]
      simp


/-! ## Transporting non-cutness along a relabelling -/

theorem avoid_map {n : ℕ} {adj adj' : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (h : ∀ a b, adj (σ a) (σ b) = adj' a b) (v a b : Fin n) :
    avoid adj (σ v) (σ a) (σ b) = avoid adj' v a b := by
  simp only [avoid, h a b, ne_eq, EmbeddingLike.apply_eq_iff_eq]

theorem nonCut_map {n : ℕ} {adj adj' : Fin n → Fin n → Bool} (σ : Equiv.Perm (Fin n))
    (h : ∀ a b, adj (σ a) (σ b) = adj' a b) {v : Fin n} (hv : NonCut adj' v) :
    NonCut adj (σ v) := by
  intro i j hi hj
  have hi' : σ.symm i ≠ v := fun he ↦ hi (by rw [← he, Equiv.apply_symm_apply])
  have hj' : σ.symm j ≠ v := fun he ↦ hj (by rw [← he, Equiv.apply_symm_apply])
  simpa using reach_map (adj := avoid adj (σ v)) σ (avoid_map σ h v) (hv _ _ hi' hj')

/-- Connectivity survives canonicalisation, so it can be read off the canonical code. -/
theorem conn_graphOfCode_canonCode {n : ℕ} {adj : Fin n → Fin n → Bool}
    (hs : ∀ i j, adj i j = adj j i) (hl : ∀ i, adj i i = false) :
    Conn (graphOfCode n (canonCode n adj)).Adj ↔ Conn adj := by
  have h : (graphOfCode n (canonCode n adj)).Adj = canonAdj n adj :=
    funext fun i ↦ funext fun j ↦ adj_graphOfCode_canonCode hs hl i j
  rw [h, conn_canonAdj_iff]

/-! ## Small arithmetic helpers -/

theorem exists_testBit {n s : ℕ} (hs : s < 2 ^ n) (h0 : s ≠ 0) :
    ∃ i : Fin n, s.testBit i.1 = true := by
  by_contra h
  simp only [not_exists, Bool.not_eq_true] at h
  exact h0 (eq_of_testBit_lt hs (Nat.two_pow_pos n) fun k hk ↦ by
    rw [Nat.zero_testBit]; exact h ⟨k, hk⟩)

theorem maskCard_zero (n : ℕ) : maskCard n 0 = 0 := by simp [maskCard]

theorem deg_ne_zero {n : ℕ} {adj : Fin n → Fin n → Bool} {v w : Fin n} (h : adj v w = true) :
    deg adj v ≠ 0 := by
  intro h0
  rw [deg, Finset.sum_eq_zero_iff] at h0
  simpa [h] using h0 w (Finset.mem_univ w)

/-! ## The connected mask selector

A connected graph on `n + 1` vertices stays connected when a **non-cut** vertex is deleted, and it
always has one.  So, exactly as for `redMasks`, we may insist that the vertex being added back is
one of least degree — but only among the non-cut vertices, since those are the only ones that could
have been deleted.  Deciding which vertices are non-cut needs a connectivity search per vertex
(`nonCutTest`), so the cheap degree comparison is tried first and the search runs only for the
vertices that could beat the new one. -/

/-- Would the new vertex have least degree **among the non-cut vertices** of the extension? -/
def nonCutMinDegOk (n : ℕ) (rows : Array ℕ) (c s : ℕ) : Bool :=
  decide (∀ u : Fin n,
    maskCard n s ≤ deg (graphOfCode n c).Adj u + (if s.testBit u.1 then 1 else 0) ∨
      nonCutTest n rows s u.1 = false)

/-- The masks tried when enumerating connected graphs: nonempty orbit representatives that make
the new vertex one of least degree among the non-cut vertices. -/
def connMasks (n c : ℕ) : List ℕ :=
  let rows := rowsOfCode n c
  (symMasks n c).filter fun s ↦ decide (s ≠ 0) && nonCutMinDegOk n rows c s

theorem connMasks_subset {n c s : ℕ} (h : s ∈ connMasks n c) : s ≠ 0 ∧ s < 2 ^ n := by
  rw [connMasks, List.mem_filter] at h
  obtain ⟨hmem, hok⟩ := h
  rw [symMasks, List.mem_filter, List.mem_range] at hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact ⟨hok.1, hmem.1⟩

/-- The non-cut test only depends on the isomorphism class, so it commutes with the action of the
automorphism group on masks. -/
theorem nonCutTest_permMask {n c s u : ℕ} (hc : c < 2 ^ n.choose 2) (hs : s < 2 ^ n) (hu : u < n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ autGroup n (graphOfCode n c).Adj)
    (h : nonCutTest n (rowsOfCode n c) (permMask n σ s) u = true) :
    nonCutTest n (rowsOfCode n c) s (σ ⟨u, hu⟩).1 = true := by
  rw [nonCutTest_iff (rowsSpec_rowsOfCode n c) hc (permMask_lt n σ s) hu] at h
  rw [nonCutTest_iff (rowsSpec_rowsOfCode n c) hc hs (σ ⟨u, hu⟩).2]
  have h' : NonCut (graphOfCode (n + 1) (extendCode n c s)).Adj
      (permLast σ (⟨u, hu⟩ : Fin n).castSucc) :=
    nonCut_map (permLast σ) (adj_extendCode_permMask hc σ hσ) h
  rwa [permLast_castSucc] at h'

theorem nonCutMinDegOk_permMask {n c s : ℕ} (hc : c < 2 ^ n.choose 2) (hs : s < 2 ^ n)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ autGroup n (graphOfCode n c).Adj)
    (h : nonCutMinDegOk n (rowsOfCode n c) c s = true) :
    nonCutMinDegOk n (rowsOfCode n c) c (permMask n σ s) = true := by
  simp only [nonCutMinDegOk, decide_eq_true_eq] at h ⊢
  intro u
  rcases h (σ u) with hd | hnc
  · left
    rw [maskCard_permMask, testBit_permMask _ _ u.2, ← deg_of_mem_autGroup hσ u]
    exact hd
  · right
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    have := nonCutTest_permMask hc hs u.2 hσ hcon
    simp [this] at hnc

/-! ## Completeness of the connected mask selector -/

/-- **What a mask selector must satisfy to enumerate the connected graphs**: every connected graph
on `n + 2` vertices must be obtainable, up to isomorphism, by extending some *connected* graph on
`n + 1` vertices by one of the offered masks. -/
def ConnMasksComplete (masks : ℕ → ℕ → List ℕ) : Prop :=
  ∀ (n : ℕ) (adj : Fin (n + 2) → Fin (n + 2) → Bool), (∀ i j, adj i j = adj j i) →
    (∀ i, adj i i = false) → Conn adj →
      ∃ adj' : Fin (n + 1) → Fin (n + 1) → Bool, (∀ i j, adj' i j = adj' j i) ∧
        (∀ i, adj' i i = false) ∧ Conn adj' ∧
        ∃ s ∈ masks (n + 1) (canonCode (n + 1) adj'),
          canonCode (n + 2)
              (graphOfCode (n + 2) (extendCode (n + 1) (canonCode (n + 1) adj') s)).Adj
            = canonCode (n + 2) adj

/-- **What a mask selector must satisfy for the extensions to stay connected**: never offer the
empty neighbourhood. -/
def MasksNonzero (masks : ℕ → ℕ → List ℕ) : Prop := ∀ n c, ∀ s ∈ masks n c, s ≠ 0 ∧ s < 2 ^ n

theorem connMasks_nonzero : MasksNonzero connMasks := fun _ _ _ h ↦ connMasks_subset h

/-- **Nothing is lost by only adding a least-degree non-cut vertex.**  Delete, from a connected
graph, a non-cut vertex of least degree among the non-cut vertices: what is left is a smaller
*connected* graph, and the mask that puts the deleted vertex back passes every test. -/
theorem connMasks_complete : ConnMasksComplete connMasks := by
  intro n adj hs hl hconn
  classical
  obtain ⟨v₀, hv₀⟩ := exists_nonCut hs hconn
  obtain ⟨v, hvmem, hvmin'⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Fin (n + 2))).filter fun x ↦ NonCut adj x) (deg adj)
    ⟨v₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₀⟩⟩
  have hnc : NonCut adj v := (Finset.mem_filter.1 hvmem).2
  have hvmin : ∀ u : Fin (n + 2), NonCut adj u → deg adj v ≤ deg adj u := fun u hu ↦
    hvmin' u (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩)
  set π : Equiv.Perm (Fin (n + 2)) := Equiv.swap v (Fin.last (n + 1)) with hπ
  set adjπ : Fin (n + 2) → Fin (n + 2) → Bool := fun a b ↦ adj (π a) (π b) with hadjπ
  have hsπ : ∀ i j, adjπ i j = adjπ j i := fun i j ↦ hs _ _
  have hlπ : ∀ i, adjπ i i = false := fun i ↦ hl _
  set adj' : Fin (n + 1) → Fin (n + 1) → Bool := restrict adjπ with hadj'
  have hs' : ∀ i j, adj' i j = adj' j i := fun i j ↦ hsπ _ _
  have hl' : ∀ i, adj' i i = false := fun i ↦ hlπ _
  have hconn' : Conn adj' := conn_delAdj hnc
  set c : ℕ := canonCode (n + 1) adj' with hc
  set σ : Equiv.Perm (Fin (n + 1)) := canonPerm (n + 1) adj' with hσdef
  set s : ℕ := lastMask (n + 1) adjπ with hsdef
  have hbit : ∀ u : Fin (n + 1), s.testBit u.1 = adjπ (σ u).castSucc (Fin.last (n + 1)) :=
    fun u ↦ testBit_lastMask u.2
  have hdegπ : ∀ i : Fin (n + 2), deg adjπ i = deg adj (π i) := deg_perm adj π
  have hcard : maskCard (n + 1) s = deg adj v := by
    have h1 : deg adj v = deg adjπ (Fin.last (n + 1)) := by
      rw [hdegπ, hπ, Equiv.swap_apply_right]
    rw [h1, deg_castSucc_split adjπ (Fin.last (n + 1)), if_neg (by simp [hlπ])]
    simp only [Nat.add_zero, maskCard]
    exact Fintype.sum_equiv σ _ _ fun i ↦ by rw [hbit i, hsπ]
  have hdeg : ∀ u : Fin (n + 1),
      deg (graphOfCode (n + 1) c).Adj u + (if s.testBit u.1 then 1 else 0)
        = deg adj (π (σ u).castSucc) := by
    intro u
    have hgc : (graphOfCode (n + 1) c).Adj = fun a b ↦ adj' (σ a) (σ b) :=
      funext fun i ↦ funext fun j ↦ by
        rw [hc, adj_graphOfCode_canonCode hs' hl' i j, canonAdj_apply]
    rw [hgc, deg_perm, hbit u, ← hdegπ, deg_castSucc_split adjπ (σ u).castSucc]
    rfl
  -- the new vertex has at least one neighbour, since the graph is connected and has ≥ 2 vertices
  obtain ⟨x, hx⟩ : ∃ x : Fin (n + 2), x ≠ v := exists_ne v
  obtain ⟨w, hvw, -⟩ := (Relation.ReflTransGen.cases_head (hconn v x)).resolve_left
    fun he ↦ hx he.symm
  have hdegv : deg adj v ≠ 0 := deg_ne_zero hvw
  -- and it has least degree among the non-cut vertices
  have hclt : c < 2 ^ (n + 1).choose 2 := hc ▸ canonCode_lt (n + 1) adj'
  have hslt : s < 2 ^ (n + 1) := hsdef ▸ lastMask_lt (n + 1) adjπ
  have hchild := adj_extendCode_lastMask adjπ hsπ hlπ
  -- a vertex of the extension that the test finds non-cut really is a non-cut vertex of `adj`
  have hnonCut : ∀ u : Fin (n + 1), nonCutTest (n + 1) (rowsOfCode (n + 1) c) s u.1 = true →
      NonCut adj (π (σ u).castSucc) := by
    intro u hnct
    rw [nonCutTest_iff (rowsSpec_rowsOfCode (n + 1) c) hclt hslt u.2] at hnct
    have h1 : NonCut adjπ (permLast σ u.castSucc) := nonCut_map (permLast σ) hchild hnct
    rw [permLast_castSucc] at h1
    exact nonCut_map π (fun _ _ ↦ rfl) h1
  have hmin : nonCutMinDegOk (n + 1) (rowsOfCode (n + 1) c) c s = true := by
    simp only [nonCutMinDegOk, decide_eq_true_eq]
    intro u
    by_cases hnct : nonCutTest (n + 1) (rowsOfCode (n + 1) c) s u.1 = true
    · rw [hcard, hdeg u]
      exact Or.inl (hvmin _ (hnonCut u hnct))
    · exact Or.inr (Bool.eq_false_iff.2 hnct)
  -- reduce the mask to its orbit representative
  obtain ⟨τ, hτ, hmem⟩ := exists_mem_symMasks (c := c) hslt
  refine ⟨adj', hs', hl', hconn', permMask (n + 1) τ s, ?_, ?_⟩
  · rw [connMasks, List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun h0 ↦ hdegv ?_, nonCutMinDegOk_permMask hclt hslt hτ hmin⟩
    have hpc : maskCard (n + 1) (permMask (n + 1) τ s) = deg adj v := by
      rw [maskCard_permMask, hcard]
    rw [h0, maskCard_zero] at hpc
    exact hpc.symm
  · rw [canonCode_extendCode_permMask (canonCode_lt (n + 1) adj') τ hτ,
      canonCode_extend adjπ hsπ hlπ, canonCode_eq, canonCode_eq,
      canonAdj_eq_of_equiv (A := adjπ) (B := adj) π fun _ _ ↦ rfl]

/-! ## The recursion over connected graphs

The empty graph is not connected, and there is nothing to extend it by, so the recursion starts at
one vertex instead of zero. -/

/-- Connected graphs, one vertex at a time, over an arbitrary mask selector. -/
def enumConnCodesOf (masks : ℕ → ℕ → List ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => [0]
  | n + 2 => extendLevel masks (n + 1) (enumConnCodesOf masks (n + 1))

theorem isCanon_of_mem_enumConn {masks : ℕ → ℕ → List ℕ} {n c : ℕ}
    (h : c ∈ enumConnCodesOf masks n) :
    canonCode n (graphOfCode n c).Adj = c ∧ c < 2 ^ n.choose 2 := by
  match n, h with
  | 0, h => simp [enumConnCodesOf] at h
  | 1, h =>
      rw [enumConnCodesOf, List.mem_singleton] at h
      subst h
      have hlt := canonCode_lt 1 (graphOfCode 1 0).Adj
      rw [show (1 : ℕ).choose 2 = 0 from rfl, pow_zero, Nat.lt_one_iff] at hlt
      exact ⟨hlt, by norm_num⟩
  | (n + 2), h => exact isCanon_of_mem_extendLevel h

theorem pairwise_lt_enumConnCodesOf (masks : ℕ → ℕ → List ℕ) (n : ℕ) :
    (enumConnCodesOf masks n).Pairwise (· < ·) := by
  match n with
  | 0 => simp [enumConnCodesOf]
  | 1 => simp [enumConnCodesOf]
  | (n + 2) => exact pairwise_lt_extendLevel _ _ _

theorem connTest_one_zero : connTest 1 0 = true :=
  connTest_iff.2 ⟨one_pos, fun i j ↦ (Subsingleton.elim i j : i = j) ▸ .refl⟩

/-- **Soundness**: whatever the masks, as long as none of them is empty, every code produced is
the canonical code of a connected graph. -/
theorem connTest_of_mem_enumConn {masks : ℕ → ℕ → List ℕ} (hz : MasksNonzero masks) (n : ℕ) :
    ∀ c ∈ enumConnCodesOf masks n, connTest n c = true := by
  induction n with
  | zero => simp [enumConnCodesOf]
  | succ m ih =>
      match m, ih with
      | 0, _ =>
          intro c h
          rw [enumConnCodesOf, List.mem_singleton] at h
          subst h
          exact connTest_one_zero
      | (k + 1), ih =>
          intro d h
          rw [enumConnCodesOf] at h
          obtain ⟨c, hc, s, hsmem, rfl⟩ := mem_extendLevel.1 h
          obtain ⟨hs0, hslt⟩ := hz _ _ _ hsmem
          obtain ⟨i₀, hi₀⟩ := exists_testBit hslt hs0
          have hchild : Conn (graphOfCode (k + 2) (extendCode (k + 1) c s)).Adj :=
            conn_extendCode (connTest_iff.1 (ih c hc)).2 (isCanon_of_mem_enumConn hc).2 hi₀
          refine connTest_iff.2 ⟨by omega, (conn_graphOfCode_canonCode
            (fun i j ↦ (graphOfCode (k + 2) _).symm i j)
            (fun i ↦ Bool.eq_false_iff.2 ((graphOfCode (k + 2) _).loopless i))).2 hchild⟩

/-- **Completeness**: every connected graph appears. -/
theorem mem_enumConnCodesOf {masks : ℕ → ℕ → List ℕ} (hm : ConnMasksComplete masks) (n : ℕ) :
    ∀ (adj : Fin (n + 1) → Fin (n + 1) → Bool), (∀ i j, adj i j = adj j i) →
      (∀ i, adj i i = false) → Conn adj →
        canonCode (n + 1) adj ∈ enumConnCodesOf masks (n + 1) := by
  induction n with
  | zero =>
      intro adj _ _ _
      have hlt := canonCode_lt 1 adj
      rw [show (1 : ℕ).choose 2 = 0 from rfl, pow_zero, Nat.lt_one_iff] at hlt
      rw [hlt, enumConnCodesOf]
      exact List.mem_singleton_self 0
  | succ m ih =>
      intro adj hs hl hc
      obtain ⟨adj', hs', hl', hc', t, ht, heq⟩ := hm m adj hs hl hc
      rw [enumConnCodesOf]
      exact mem_extendLevel.2 ⟨_, ih adj' hs' hl' hc', t, ht, heq⟩

/-! ## The connected enumerator -/

/-- **The canonical codes of all connected graphs on `n` vertices.** -/
def enumConnCodes : ℕ → List ℕ := enumConnCodesOf connMasks

theorem mem_enumConnCodes_iff {n c : ℕ} :
    c ∈ enumConnCodes n ↔ c ∈ enumCodes n ∧ connTest n c = true := by
  constructor
  · intro h
    obtain ⟨hcan, hlt⟩ := isCanon_of_mem_enumConn h
    exact ⟨List.mem_filter.2 ⟨List.mem_range.2 hlt, by simp [hcan]⟩,
      connTest_of_mem_enumConn connMasks_nonzero n c h⟩
  · rintro ⟨hmem, htest⟩
    obtain ⟨hn, hconn⟩ := connTest_iff.1 htest
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := mem_enumConnCodesOf connMasks_complete m (graphOfCode (m + 1) c).Adj
      (fun i j ↦ (graphOfCode (m + 1) c).symm i j)
      (fun i ↦ Bool.eq_false_iff.2 ((graphOfCode (m + 1) c).loopless i)) hconn
    rwa [canonCode_of_mem hmem] at this

/-- **The connected enumerator is exactly the connected part of the full enumeration** — not merely
the same set: both are strictly increasing lists of codes with the same members. -/
theorem enumConnCodes_eq (n : ℕ) : enumConnCodes n = (enumCodes n).filter (connTest n) :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h₁ h₂ ↦ le_antisymm h₁ h₂)
    ((pairwise_lt_enumConnCodesOf connMasks n).imp le_of_lt)
    ((List.Pairwise.filter _ (enumCodes_pairwise_lt n)).imp le_of_lt)
    ((List.perm_ext_iff_of_nodup ((pairwise_lt_enumConnCodesOf connMasks n).imp Nat.ne_of_lt)
        ((List.nodup_range.filter _).filter _)).2
      fun _ ↦ by rw [List.mem_filter]; exact mem_enumConnCodes_iff)

/-! ## Connectivity of a `CGraph`

`Conn` is stated for a raw adjacency function; `CGraph.IsConnected` is Mathlib's
`SimpleGraph.Connected`.  They agree on nonempty graphs — `Conn` is vacuously true when `n = 0`,
whereas `Connected` demands a vertex.
-/

theorem conn_of_isConnected {n c : ℕ} (h : (graphOfCode n c).IsConnected) :
    Conn (graphOfCode n c).Adj := fun i j ↦
  (SimpleGraph.reachable_iff_reflTransGen ..).1 (h.preconnected i j)

theorem isConnected_graphOfCode {n c : ℕ} (hn : 0 < n) (h : Conn (graphOfCode n c).Adj) :
    (graphOfCode n c).IsConnected := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [CGraph.IsConnected, SimpleGraph.connected_iff]
  exact ⟨fun i j ↦ (SimpleGraph.reachable_iff_reflTransGen ..).2 (h i j), hne⟩

theorem isConnected_graphOfCode_iff {n c : ℕ} (hn : 0 < n) :
    (graphOfCode n c).IsConnected ↔ Conn (graphOfCode n c).Adj :=
  ⟨conn_of_isConnected, isConnected_graphOfCode hn⟩

/-! ## The connected graphs themselves -/

/-- **All connected graphs on `n` vertices, one per isomorphism class.** -/
def enumerateConn (n : ℕ) : List CGraph := (enumConnCodes n).map (graphOfCode n)

@[simp] theorem card_of_mem_enumerateConn {n : ℕ} {H : CGraph} (h : H ∈ enumerateConn n) :
    Fintype.card H.V = n := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
  exact Fintype.card_fin n

/-- **Soundness, part one.**  Everything listed really is connected. -/
theorem isConnected_of_mem_enumerateConn {n : ℕ} {H : CGraph} (h : H ∈ enumerateConn n) :
    H.IsConnected := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
  obtain ⟨hn, hconn⟩ := connTest_iff.1 (mem_enumConnCodes_iff.1 hc).2
  exact isConnected_graphOfCode hn hconn

/-- **Completeness.**  Every connected graph on `n` vertices is isomorphic to one in
`enumerateConn n`. -/
theorem exists_mem_enumerateConn (G : CGraph) {n : ℕ} (hn : Fintype.card G.V = n)
    (hG : G.IsConnected) : ∃ H ∈ enumerateConn n, Nonempty (G ≃cg H) := by
  obtain ⟨H, hH, ⟨i⟩⟩ := exists_mem_enumerate G hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hH
  have hn0 : 0 < n := hn ▸ Fintype.card_pos_iff.2 hG.nonempty
  have hconn : Conn (graphOfCode n c).Adj :=
    conn_of_isConnected ((SimpleGraph.Iso.connected_iff (CGraph.Iso.toSimpleIso i)).1 hG)
  exact ⟨_, List.mem_map_of_mem
    (mem_enumConnCodes_iff.2 ⟨hc, connTest_iff.2 ⟨hn0, hconn⟩⟩), ⟨i⟩⟩

/-- **Soundness, part two.**  The graphs listed are pairwise non-isomorphic. -/
theorem enumerateConn_pairwise_not_iso (n : ℕ) :
    (enumerateConn n).Pairwise fun G H ↦ ¬Nonempty (G ≃cg H) := by
  rw [enumerateConn, List.pairwise_map]
  exact List.Pairwise.imp_of_mem
    (fun h₁ h₂ hne ↦ not_iso_of_mem_of_ne (mem_enumConnCodes_iff.1 h₁).1
      (mem_enumConnCodes_iff.1 h₂).1 hne)
    ((pairwise_lt_enumConnCodesOf connMasks n).imp Nat.ne_of_lt)

theorem enumerateConn_nodup (n : ℕ) : (enumerateConn n).Nodup := by
  refine (enumerateConn_pairwise_not_iso n).imp ?_
  rintro G H h rfl
  exact h ⟨RelIso.refl _⟩

/-! ## The connected isomorphism classes -/

/-- The isomorphism classes of connected graphs on `n` vertices. -/
def enumerateConnIso (n : ℕ) : List IsoGraph :=
  (enumerateConn n).map (Quotient.mk CGraph.isoSetoid)

/-- **Completeness in the quotient.**  Every connected isomorphism class of size `n` occurs. -/
theorem mem_enumerateConnIso {n : ℕ} {G : IsoGraph} (hn : G.V = n) (hc : G.IsConnected) :
    G ∈ enumerateConnIso n := by
  induction G using Quotient.inductionOn with
  | h G =>
      obtain ⟨H, hH, hi⟩ := exists_mem_enumerateConn G hn hc
      exact List.mem_map.2 ⟨H, hH, (Quotient.sound (s := CGraph.isoSetoid) hi).symm⟩

/-- Everything in the list is a connected class. -/
theorem isConnected_of_mem_enumerateConnIso {n : ℕ} {G : IsoGraph} (h : G ∈ enumerateConnIso n) :
    G.IsConnected := by
  obtain ⟨H, hH, rfl⟩ := List.mem_map.1 h
  exact isConnected_of_mem_enumerateConn hH

/-- **No repetitions in the quotient**: the list is exactly the set of connected classes. -/
theorem enumerateConnIso_nodup (n : ℕ) : (enumerateConnIso n).Nodup := by
  rw [enumerateConnIso, List.Nodup, List.pairwise_map]
  exact (enumerateConn_pairwise_not_iso n).imp fun h he ↦ h (Quotient.exact he)

/-! ## Sanity check

The counts are OEIS A001349, the number of connected graphs on `n` unlabelled vertices.  Larger
`n` is checked by `lake exe enumbench`. -/

#guard ((List.range 8).map fun n ↦ (enumConnCodes n).length) = [0, 1, 1, 2, 6, 21, 112, 853]

end CGraph.Enum
