import IsoGraph.Canon.Correct

/-!
# Searching the subtree below a node, and the orbit test

The canonical labelling search of `IsoGraph.Canon.Algorithm` explores the whole
individualisation–refinement tree from the root.  This file runs the *same* search starting from
an arbitrary node of that tree, and uses it to decide when two nodes are in the same orbit of the
automorphism group.

## What is here

* `subStAt n f path invPath p` — the search restricted to the subtree below the node
  `Node n f path invPath p`, and the usual package of facts about its answer: it succeeds
  (`subStAt_best_isSome`), it lands on a genuine leaf below that node (`subStAt_leafNode`,
  `subStAt_pathPre`, `subStAt_reach`) and that leaf is the best one there (`subStAt_subBest`).
* `Node.map_equiv` — an automorphism carrying one path to another carries the whole node
  structure with it: the same invariant path, equivalent partitions, and the same target cells
  all the way down.  This is what makes the subtree search *equivariant*.
* `subStAt_orbitMap` — the payoff.  If two nodes are related by an automorphism at all, then the
  canonical labellings of their two subtrees differ by one, and `autoOf` reconstructs it
  explicitly — without ever seeing the automorphism that related them.
* `sameOrbit n f P Q` — the resulting **decision procedure**: two paths are in the same orbit iff
  this `Bool` is `true`.  It is sound (`sameOrbit_spec` hands back an automorphism mapping `P` to
  `Q` pointwise) and complete (`sameOrbit_of_auto`), which is what `Canon/Chain.lean` needs to
  turn orbit–stabiliser recursion into a proof.

The cost is that the subtree below every candidate is searched from scratch, so nothing here is
meant to be run on a large graph; it is the *proof* that the automorphism computation can be
completed, and a reference implementation of it.
-/

set_option autoImplicit false
namespace IsoGraph
namespace Canon

open Std

/-! ## Leaves below an ancestor -/

/-- A leaf below a node is a leaf below every ancestor of that node. -/
theorem Node.ancReach_mono {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) :
    ∀ j, j ≤ path.size → ∀ k, ancReach n f path path.size k → ancReach n f path j k := by
  induction h with
  | root => intro j hj k hk; simp only [Array.size_empty, Nat.le_zero] at hj; subst hj; exact hk
  | @step path invPath p c v hnode hc hv hcell ih =>
    intro j hj k hk
    rw [Array.size_push] at hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · simpa using hk
    · have hj' : j ≤ path.size := by omega
      have h1 : SubR n f invPath p v k := (ancReach_child hnode v k).1 (by simpa using hk)
      have h2 : Reach n f invPath p k := Reach.step hc hv hcell h1
      exact (ancReach_push path v j hj' k).2 (ih j hj' k ((ancReach_full hnode k).2 h2))

theorem stopDepth_le (d : Nat) (ab : Option Nat) : stopDepth d ab ≤ d := by
  cases ab with
  | none => exact Nat.le_refl d
  | some j => exact Nat.min_le_right _ _

/-! ## The search, run at an arbitrary node -/

/-- The state a fresh search of the subtree below the node `(invPath, p)` at `path` ends in. -/
def subStAt (n : Nat) (f : Nat → Nat → Bool) (path : Array Nat) (invPath : Array UInt64)
    (p : Part) : St :=
  dfsNode (Graph.ofOracle n f) (n + 1) path invPath p
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }

theorem subStAt_best_isSome {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p) :
    (subStAt n f path invPath p).best.isSome = true :=
  dfsNode_best n f (n + 1) path invPath p _ hnode.wf
    (by have := numCells_le (n := n) p; omega) (by simp)

theorem subStAt_leafNode {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p) {b : Leaf}
    (hb : (subStAt n f path invPath p).best = some b) : LeafNode n f b :=
  (dfsNode_good n f (n + 1) path invPath p _ hnode ⟨by simp, by simp, by simp⟩).1 b hb

theorem subStAt_pathPre {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} {b : Leaf}
    (hb : (subStAt n f path invPath p).best = some b) : PathPre path b.path :=
  (dfsNode_paths n f (PathPre path) (n + 1) path invPath p _ (fun _ hQ => hQ)
    ⟨by simp, by simp⟩).1 b hb

theorem subStAt_reach {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p) {b : Leaf}
    (hb : (subStAt n f path invPath p).best = some b) :
    Reach n f invPath p (leafKey b.invPath b.cert) :=
  dfsNode_reach n f (Reach n f invPath p) (n + 1) path invPath p _ hnode.wf (fun _ h => h)
    (by intro l hl; simp at hl) b hb

/-- **The subtree search finds the best leaf below its node.** -/
theorem subStAt_dom {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p)
    {k : List (List UInt64)} (hk : Reach n f invPath p k) :
    Dom (subStAt n f path invPath p) k := by
  have h := dfsNode_dom n f (n + 1) path invPath p
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }
    (fun _ => False) hnode (by have := numCells_le (n := n) p; omega) rfl
    ⟨by simp, by simp, by simp⟩ (by intro l hl; rcases hl with hl | hl <;> simp at hl)
    (by intro l hl; rcases hl with hl | hl <;> simp at hl)
  refine (h.2.1 k ?_).elim id False.elim
  exact hnode.ancReach_mono _ (stopDepth_le _ _) k ((ancReach_full hnode k).2 hk)

/-! ## Two nodes related by an automorphism -/

theorem Node.pinPos_eq {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {ip : Array UInt64}
    {p : Part} (h : Node n f path ip p) :
    pinPos n f path.toList = (p.targetCell n).getD 0 := by
  rw [pinPos, congrArg Prod.snd h.nodePath_eq]

/-- **Transporting a node along an automorphism.**  If the automorphism `g` carries the path `Q`
to the path `P` entry by entry, then the two nodes have the same invariant path, their partitions
correspond under `g`, and every ancestor pair individualises at the same position. -/
theorem Node.map_equiv {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {Q : Array Nat} {iq : Array UInt64} {q : Part} (hQ : Node n f Q iq q) :
    ∀ {P : Array Nat} {ip : Array UInt64} {p : Part}, Node n f P ip p → P.size = Q.size →
      (∀ i, i < Q.size → P[i]! = g[Q[i]!]!) →
      ip = iq ∧ PartEquiv n (fun x => g[x]!) p q ∧
        ∀ j, j ≤ Q.size → pinPos n f (P.toList.take j) = pinPos n f (Q.toList.take j) := by
  induction hQ with
  | root =>
    intro P ip p hP hsize _
    cases hP with
    | root =>
      refine ⟨rfl, Node.root.auto_partEquiv hg (by intro i hi; simp at hi), ?_⟩
      intro j hj
      simp only [Array.size_empty, Nat.le_zero] at hj
      subst hj; rfl
    | step => simp at hsize
  | @step Q0 iq0 q0 c w hQ0 hc hw hcell ih =>
    intro P ip p hP hsize hmap
    cases hP with
    | root => simp at hsize
    | @step P0 ip0 p0 c' v hP0 hc' hv hcell' =>
      have hs0 : P0.size = Q0.size := by simpa using hsize
      have hmap0 : ∀ i, i < Q0.size → P0[i]! = g[Q0[i]!]! := by
        intro i hi
        have h1 := hmap i (by rw [Array.size_push]; omega)
        rwa [push_getElem!_lt P0 v (by omega), push_getElem!_lt Q0 w hi] at h1
      have hvw : v = g[w]! := by
        have h1 := hmap Q0.size (by rw [Array.size_push]; omega)
        rwa [← hs0, push_getElem!_eq, hs0, push_getElem!_eq] at h1
      subst hvw
      obtain ⟨hip0, he0, hpin0⟩ := ih hP0 hs0 hmap0
      have hce := child_equiv (f := f) hg.perm.isPerm hP0.wf hQ0.wf he0 hw
      have hci := childInv_equiv (f := f) hg.perm.isPerm hP0.wf hQ0.wf he0 ip0 hw
      rw [hg.graph] at hce hci
      refine ⟨by rw [hci, hip0], hce.1, ?_⟩
      intro j hj
      rw [Array.size_push] at hj
      rcases Nat.lt_or_ge j (Q0.size + 1) with h1 | h1
      · have hjQ : j ≤ Q0.size := by omega
        rw [Array.toList_push, Array.toList_push,
          List.take_append_of_le_length (by simp [hs0]; omega),
          List.take_append_of_le_length (by simpa using hjQ)]
        exact hpin0 j hjQ
      · have hje : j = Q0.size + 1 := by omega
        subst hje
        rw [Array.toList_push, Array.toList_push,
          show (P0.toList ++ [g[w]!]).take (Q0.size + 1) = P0.toList ++ [g[w]!] by
            simp [hs0],
          show (Q0.toList ++ [w]).take (Q0.size + 1) = Q0.toList ++ [w] by simp,
          ← Array.toList_push, ← Array.toList_push,
          (hP0.step hc' hv hcell').pinPos_eq, (hQ0.step hc hw hcell).pinPos_eq,
          hce.1.targetCell]

/-! ## The best leaf below a node -/

theorem cmp_le_antisymm {a b : List (List UInt64)} (h1 : compare a b ≠ .gt)
    (h2 : compare b a ≠ .gt) : a = b := by
  cases hc : compare a b with
  | eq => exact LawfulEqCmp.eq_of_compare hc
  | lt => exact absurd (OrientedCmp.gt_of_lt hc) h2
  | gt => exact absurd hc h1

/-- `k` is the largest key of a leaf below the node `(invPath, p)`. -/
def SubBest (n : Nat) (f : Nat → Nat → Bool) (invPath : Array UInt64) (p : Part)
    (k : List (List UInt64)) : Prop :=
  Reach n f invPath p k ∧ ∀ k', Reach n f invPath p k' → compare k' k ≠ .gt

theorem subBest_unique {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    {k k' : List (List UInt64)} (h : SubBest n f invPath p k) (h' : SubBest n f invPath p k') :
    k = k' :=
  cmp_le_antisymm (h'.2 k h.1) (h.2 k' h'.1)

theorem subStAt_subBest {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p) {b : Leaf}
    (hb : (subStAt n f path invPath p).best = some b) :
    SubBest n f invPath p (leafKey b.invPath b.cert) := by
  refine ⟨subStAt_reach hnode hb, fun k hk => ?_⟩
  obtain ⟨l, hl, hcmp⟩ := subStAt_dom hnode hk
  rw [hb] at hl
  cases hl
  exact hcmp

/-- The inverse renaming relates the same two partitions the other way round. -/
theorem PartEquiv.inv {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {p q : Part} (he : PartEquiv n (fun x => g[x]!) p q) :
    PartEquiv n (fun x => (invAuto n g)[x]!) q p := by
  refine ⟨fun i hi => (he.cst i hi).symm, fun i hi => (he.cen i hi).symm, fun v hv => ?_⟩
  obtain ⟨a, ha, hav⟩ := hg.perm.surj hv
  rw [← hav, invAuto_get hg.perm ha]
  exact (he.cell a ha).symm

/-! ## The orbit test -/

/-- **Two nodes in the same orbit have the same canonical leaf key.** -/
theorem subBest_map {n : Nat} {f : Nat → Nat → Bool} {P Q : Array Nat} {ip iq : Array UInt64}
    {p q : Part} (hP : Node n f P ip p) (hQ : Node n f Q iq q) {g : Array Nat}
    (hg : IsAutoArr n f g) (hsize : P.size = Q.size) (hmap : ∀ i, i < Q.size → P[i]! = g[Q[i]!]!)
    {kP kQ : List (List UInt64)} (hkP : SubBest n f ip p kP) (hkQ : SubBest n f iq q kQ) :
    kP = kQ := by
  obtain ⟨hipq, he, _⟩ := hQ.map_equiv hg hP hsize hmap
  subst hipq
  refine cmp_le_antisymm (hkQ.2 kP ?_) (hkP.2 kQ ?_)
  · exact reach_auto (invAuto_isAuto hg) hQ.wf hP.wf (he.inv hg) hkP.1
  · exact reach_auto hg hP.wf hQ.wf he hkQ.1

theorem PathPre.take {a b : Array Nat} (h : PathPre a b) {j : Nat} (hj : j ≤ a.size) :
    b.toList.take j = a.toList.take j := by
  have hjb : j ≤ b.size := hj.trans h.1
  refine List.ext_getElem (by simp; omega) (fun i h1 h2 => ?_)
  have hij : i < j := by simp at h1; omega
  have h3 := h.2 i (by omega)
  rw [getElem!_pos a i (by omega), getElem!_pos b i (by omega)] at h3
  simpa using h3.symm

/-- **The canonical leaves of two nodes in the same orbit exhibit an automorphism carrying one
node to the other.**  This is the completeness half of the orbit test: the map read off from the
two canonical labellings is an automorphism and it really does carry `P` to `Q`, whenever *some*
automorphism does. -/
theorem subStAt_orbitMap {n : Nat} {f : Nat → Nat → Bool} {P Q : Array Nat}
    {ip iq : Array UInt64} {p q : Part} (hP : Node n f P ip p) (hQ : Node n f Q iq q)
    {g : Array Nat} (hg : IsAutoArr n f g) (hsize : P.size = Q.size)
    (hmap : ∀ i, i < Q.size → P[i]! = g[Q[i]!]!) {bP bQ : Leaf}
    (hbP : (subStAt n f P ip p).best = some bP) (hbQ : (subStAt n f Q iq q).best = some bQ) :
    IsAutoArr n f (autoOf n bP.lab bQ.lab) ∧
      ∀ j, j < P.size → (autoOf n bP.lab bQ.lab)[P[j]!]! = Q[j]! := by
  obtain ⟨-, -, hpp⟩ := hQ.map_equiv hg hP hsize hmap
  have hkey : leafKey bP.invPath bP.cert = leafKey bQ.invPath bQ.cert :=
    subBest_map hP hQ hg hsize hmap (subStAt_subBest hP hbP) (subStAt_subBest hQ hbQ)
  have hlP := subStAt_leafNode hP hbP
  have hlQ := subStAt_leafNode hQ hbQ
  have hpermP : PermArr n bP.lab := hlP.permArr
  have hpermQ : PermArr n bQ.lab := hlQ.permArr
  obtain ⟨pb, hpbNode, -, hpbLab, hpbCert⟩ := hlP
  obtain ⟨qb, hqbNode, -, hqbLab, hqbCert⟩ := hlQ
  have hcert : certOf (Graph.ofOracle n f) bP.lab = certOf (Graph.ofOracle n f) bQ.lab := by
    rw [← hpbLab] at hpbCert
    rw [← hqbLab] at hqbCert
    rw [← hpbCert, ← hqbCert]
    exact (leafKey_inj hkey).2
  refine ⟨autoOf_isAuto hpermP hpermQ hcert, fun j hj => ?_⟩
  have hpreP : PathPre P bP.path := subStAt_pathPre hbP
  have hpreQ : PathPre Q bQ.path := subStAt_pathPre hbQ
  have hpinP := hpbNode.pin j (by have := hpreP.1; omega)
  have hpinQ := hqbNode.pin j (by have := hpreQ.1; omega)
  rw [hpreP.take (Nat.le_of_lt hj)] at hpinP
  rw [hpreQ.take (Nat.le_of_lt (hsize ▸ hj)), ← hpp j (Nat.le_of_lt (hsize ▸ hj))] at hpinQ
  have hgetP : bP.lab[pinPos n f (P.toList.take j)]! = P[j]! := by
    rw [hpbLab, hpinP.lab, ← hpreP.2 j hj]
  have hgetQ : bQ.lab[pinPos n f (P.toList.take j)]! = Q[j]! := by
    rw [hqbLab, hpinQ.lab, ← hpreQ.2 j (hsize ▸ hj)]
  rw [← hgetP, ← hgetQ]
  exact autoOf_get hpermP hpinP.lt

/-! ## Deciding that an array is an automorphism -/

/-- The `O(n²)` check that `g` is an automorphism of `Graph.ofOracle n f`. -/
def isAutoArrB (n : Nat) (f : Nat → Nat → Bool) (g : Array Nat) : Bool :=
  g.size == n &&
    (List.range n).all fun u =>
      g[u]! < n && (List.range n).all fun v => (u == v || g[u]! != g[v]!) && (f g[u]! g[v]! == f u v)

theorem isAutoArrB_iff {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} :
    isAutoArrB n f g = true ↔ IsAutoArr n f g := by
  simp only [isAutoArrB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨hsize, hall⟩
    refine ⟨⟨hsize, fun i hi => (hall i hi).1, fun i hi j hj hij => ?_⟩, fun u hu v hv => ?_⟩
    · rcases ((hall i hi).2 j hj).1 with h | h
      · exact h
      · exact absurd hij h
    · exact ((hall u hu).2 v hv).2
  · intro hg
    refine ⟨hg.perm.size, fun u hu => ⟨hg.perm.lt u hu, fun v hv => ⟨?_, hg.adj u hu v hv⟩⟩⟩
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr fun h => huv (hg.perm.inj u hu v hv h)

/-- The check that `d` is an automorphism carrying the path `P` to the path `Q`. -/
def mapsPath (n : Nat) (f : Nat → Nat → Bool) (d : Array Nat) (P Q : Array Nat) : Bool :=
  isAutoArrB n f d && (P.size == Q.size) && (List.range P.size).all fun i => d[P[i]!]! == Q[i]!

theorem mapsPath_iff {n : Nat} {f : Nat → Nat → Bool} {d P Q : Array Nat} :
    mapsPath n f d P Q = true ↔
      IsAutoArr n f d ∧ P.size = Q.size ∧ ∀ i, i < P.size → d[P[i]!]! = Q[i]! := by
  simp only [mapsPath, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    isAutoArrB_iff]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-! ## The orbit test -/

/-- The search of the subtree at `path`, with the node recomputed from the path. -/
def subSt (n : Nat) (f : Nat → Nat → Bool) (path : Array Nat) : St :=
  subStAt n f path (nodePath n f path.toList).1 (nodePath n f path.toList).2

theorem subSt_eq {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {ip : Array UInt64}
    {p : Part} (h : Node n f path ip p) : subSt n f path = subStAt n f path ip p := by
  rw [subSt, h.nodePath_eq]

/-- The canonical labelling of the subtree at `path`. -/
def subLab (n : Nat) (f : Nat → Nat → Bool) (path : Array Nat) : Array Nat :=
  match (subSt n f path).best with
  | some b => b.lab
  | none => Array.range n

/-- The permutation carrying the canonical leaf of the subtree at `P` to that of the subtree at
`Q`: the only candidate for an automorphism carrying `P` to `Q`. -/
def orbitMap (n : Nat) (f : Nat → Nat → Bool) (P Q : Array Nat) : Array Nat :=
  autoOf n (subLab n f P) (subLab n f Q)

/-- **The orbit test**: is there an automorphism carrying the path `P` to the path `Q`? -/
def sameOrbit (n : Nat) (f : Nat → Nat → Bool) (P Q : Array Nat) : Bool :=
  mapsPath n f (orbitMap n f P Q) P Q

theorem subLab_eq {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {ip : Array UInt64}
    {p : Part} (h : Node n f path ip p) {b : Leaf} (hb : (subStAt n f path ip p).best = some b) :
    subLab n f path = b.lab := by
  rw [subLab, subSt_eq h, hb]

/-- **The orbit test is complete.**  If any automorphism carries `Q` to `P`, the test succeeds. -/
theorem sameOrbit_of_auto {n : Nat} {f : Nat → Nat → Bool} {P Q : Array Nat}
    {ip iq : Array UInt64} {p q : Part} (hP : Node n f P ip p) (hQ : Node n f Q iq q)
    {g : Array Nat} (hg : IsAutoArr n f g) (hsize : P.size = Q.size)
    (hmap : ∀ i, i < Q.size → P[i]! = g[Q[i]!]!) : sameOrbit n f P Q = true := by
  obtain ⟨bP, hbP⟩ := Option.isSome_iff_exists.1 (subStAt_best_isSome hP)
  obtain ⟨bQ, hbQ⟩ := Option.isSome_iff_exists.1 (subStAt_best_isSome hQ)
  obtain ⟨hauto, hmaps⟩ := subStAt_orbitMap hP hQ hg hsize hmap hbP hbQ
  rw [sameOrbit, orbitMap, subLab_eq hP hbP, subLab_eq hQ hbQ]
  exact mapsPath_iff.2 ⟨hauto, hsize, hmaps⟩

/-- **The orbit test is sound**, and hands back the automorphism it found. -/
theorem sameOrbit_spec {n : Nat} {f : Nat → Nat → Bool} {P Q : Array Nat}
    (h : sameOrbit n f P Q = true) :
    IsAutoArr n f (orbitMap n f P Q) ∧ P.size = Q.size ∧
      ∀ i, i < P.size → (orbitMap n f P Q)[P[i]!]! = Q[i]! :=
  mapsPath_iff.1 h

end Canon
end IsoGraph
