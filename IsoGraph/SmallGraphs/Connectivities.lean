import IsoGraph.SmallGraphs.TreesAndCycles

/-!
# The connectivities of the families

`CGraph.vertexConn_join` says what a join does to `κ`, and Whitney's chain `κ ≤ λ ≤ δ` collapses
whenever its two ends meet.  Between them those two facts settle both connectivities for most of
the two-parameter families: everything built as a join — the complete multipartite graphs and so
the bipartite graphs, the books, the cocktail party graphs, the Turán graphs, the stars, the
wheels, the fans — and, from the other end, everything with a pendant vertex.

The families that are not joins get their lower bound on `κ` from a spanning cycle instead: a
Hamiltonian graph has no cut vertex.  That is exact for the ladders, whose minimum degree is two,
and a bound for the prisms, the crowns, the circulants and the LCF graphs.
-/

namespace IsoGraph

/-! ### Three list helpers

The complete multipartite graph on parts `ds` loses one part to a separator, so the answers below
are all `ds.sum - ds.max?`, and the induction over `ds` needs to know how that behaves under
`cons`. -/

private theorem max?_getD_cons (d : ℕ) (ds : List ℕ) :
    ((d :: ds).max?).getD 0 = max d ((ds.max?).getD 0) := by
  cases ds with
  | nil => simp
  | cons e es => simp [List.max?_cons]

private theorem max?_getD_le_sum (ds : List ℕ) : (ds.max?).getD 0 ≤ ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => rw [max?_getD_cons, List.sum_cons]; omega

private theorem sum_eq_zero_or_max?_getD_pos (ds : List ℕ) :
    ds.sum = 0 ∨ 0 < (ds.max?).getD 0 := by
  induction ds with
  | nil => exact Or.inl rfl
  | cons d ds ih => rw [max?_getD_cons, List.sum_cons]; omega

private theorem max?_getD_eq_sum_of_sum_le_one {ds : List ℕ} (h : ds.sum ≤ 1) :
    (ds.max?).getD 0 = ds.sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [List.sum_cons] at h
    rw [max?_getD_cons, List.sum_cons, ih (by omega)]
    omega

private theorem completeMultipartite_eq_empty_of_sum_eq_zero {ds : List ℕ} (h : ds.sum = 0) :
    completeMultipartite ds = empty 0 := by
  induction ds with
  | nil => rw [completeMultipartite_nil]
  | cons d ds ih =>
    rw [List.sum_cons] at h
    obtain rfl : d = 0 := by omega
    rw [completeMultipartite_zero_cons, ih (by omega)]

/-! ### The families that are joins

A join is as connected as its parts allow: to separate `G ∇g H` one must delete a whole side, so
`κ (G ∇g H)` is the least of `|G| + κ H`, `|H| + κ G` and `|G| + |H| - 1`.  In each of these
families that least term also equals the minimum degree, and then `λ = δ` too. -/

/-- **The edge connectivity of a join.**  Plesník settles `λ = δ` for anything of diameter two, and
a join always is; `minDeg_join` then reads off the answer. -/
@[simp] theorem edgeConn_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).edgeConn = min (G.minDeg + H.V) (G.V + H.minDeg) := by
  rw [edgeConn_join_eq_minDeg G H hG hH, minDeg_join hG hH]

@[simp] theorem vertexConn_bipartite (m n : ℕ) : (bipartite m n).vertexConn = min m n := by
  rw [bipartite_eq_join, vertexConn_join]
  simp only [V_empty, vertexConn_empty]
  omega

@[simp] theorem edgeConn_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).edgeConn = min (m + 1) (n + 1) := by
  rw [edgeConn_eq_minDeg _ (by rw [V_bipartite]; omega)
    (by rw [minDeg_bipartite, vertexConn_bipartite]), minDeg_bipartite]

@[simp] theorem vertexConn_star (n : ℕ) : (star n).vertexConn = min 1 n := by
  rw [star_eq_bipartite, vertexConn_bipartite]

@[simp] theorem edgeConn_star (n : ℕ) : (star n).edgeConn = min 1 n := by
  match n with
  | 0 => simp
  | (k + 1) => rw [star_eq_bipartite]; exact edgeConn_bipartite 0 k

@[simp] theorem vertexConn_wheel (n : ℕ) : (wheel (n + 3)).vertexConn = 3 := by
  rw [wheel_eq_join, vertexConn_join]
  simp only [V_complete, V_cycle, vertexConn_complete, vertexConn_cycle]
  omega

@[simp] theorem edgeConn_wheel (n : ℕ) : (wheel (n + 3)).edgeConn = 3 := by
  rw [edgeConn_eq_minDeg _ (by rw [V_wheel]; omega) (by rw [minDeg_wheel, vertexConn_wheel]),
    minDeg_wheel]

@[simp] theorem vertexConn_fan (n : ℕ) : (fan (n + 2)).vertexConn = 2 := by
  rw [fan_eq_join, vertexConn_join]
  simp only [V_complete, V_path, vertexConn_complete, vertexConn_path]
  omega

@[simp] theorem edgeConn_fan (n : ℕ) : (fan (n + 2)).edgeConn = 2 := by
  rw [edgeConn_eq_minDeg _ (by rw [V_fan]; omega) (by rw [minDeg_fan, vertexConn_fan]), minDeg_fan]

/-! ### Complete multipartite graphs

Peeling one part off the front turns `completeMultipartite (d :: ds)` into a join, and the
recursion closes: a separator must keep one part intact, so it is everything outside a largest
part. -/

/-- **The connectivity of a complete multipartite graph**: delete everything outside one largest
part. -/
theorem vertexConn_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).vertexConn = ds.sum - (ds.max?).getD 0 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have h1 := max?_getD_le_sum ds
    have h2 := sum_eq_zero_or_max?_getD_pos ds
    rw [completeMultipartite_cons, vertexConn_join, V_empty, V_completeMultipartite,
      vertexConn_empty, ih, max?_getD_cons, List.sum_cons]
    omega

/-- **The minimum degree of a complete multipartite graph**: a vertex of a largest part misses
exactly its own part. -/
theorem minDeg_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).minDeg = ds.sum - (ds.max?).getD 0 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have h1 := max?_getD_le_sum ds
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [completeMultipartite_zero_cons, ih, max?_getD_cons, List.sum_cons]
      omega
    rcases Nat.eq_zero_or_pos ds.sum with hs | hs
    · rw [completeMultipartite_cons, completeMultipartite_eq_empty_of_sum_eq_zero hs,
        join_empty_zero, minDeg_empty, max?_getD_cons, List.sum_cons]
      omega
    · rw [completeMultipartite_cons, minDeg_join (by rw [V_empty]; omega)
        (by rw [V_completeMultipartite]; omega), minDeg_empty, V_empty,
        V_completeMultipartite, ih, max?_getD_cons, List.sum_cons]
      omega

/-- **Whitney's chain collapses at both ends for a complete multipartite graph**: separator, cut
and minimum degree all cost `ds.sum - ds.max?`. -/
theorem edgeConn_completeMultipartite (ds : List ℕ) :
    (completeMultipartite ds).edgeConn = ds.sum - (ds.max?).getD 0 := by
  rcases Nat.lt_or_ge ds.sum 2 with hs | hs
  · rw [max?_getD_eq_sum_of_sum_le_one (by omega), Nat.sub_self]
    exact (edgeConn_eq_zero_iff _).2 (Or.inl (by rw [V_completeMultipartite]; omega))
  · have hV : 2 ≤ (completeMultipartite ds).V := by rw [V_completeMultipartite]; omega
    have hmv : (completeMultipartite ds).minDeg ≤ (completeMultipartite ds).vertexConn := by
      rw [minDeg_completeMultipartite, vertexConn_completeMultipartite]
    rw [edgeConn_eq_minDeg _ hV hmv, minDeg_completeMultipartite]

/-- In a complete multipartite graph the smallest separators are exactly the smallest vertex
covers: both are what is left after keeping one largest part whole. -/
theorem vertexConn_completeMultipartite_eq_coverNum (ds : List ℕ) :
    (completeMultipartite ds).vertexConn = (completeMultipartite ds).coverNum := by
  rw [vertexConn_completeMultipartite, coverNum_completeMultipartite]

@[simp] theorem vertexConn_book (n : ℕ) : (book (n + 1)).vertexConn = 2 := by
  rw [show (book (n + 1)).vertexConn = (book (n + 1)).coverNum from
    vertexConn_completeMultipartite_eq_coverNum _, coverNum_book]
  omega

@[simp] theorem edgeConn_book (n : ℕ) : (book (n + 1)).edgeConn = 2 := by
  rw [edgeConn_eq_minDeg _ (by rw [V_book]; omega) (by rw [minDeg_book, vertexConn_book]),
    minDeg_book]

@[simp] theorem vertexConn_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).vertexConn = 2 * n := by
  rw [show (cocktailParty (n + 1)).vertexConn = (cocktailParty (n + 1)).coverNum from
    vertexConn_completeMultipartite_eq_coverNum _, coverNum_cocktailParty]

@[simp] theorem edgeConn_cocktailParty (n : ℕ) : (cocktailParty (n + 1)).edgeConn = 2 * n := by
  rw [edgeConn_eq_minDeg _ (by rw [V_cocktailParty]; omega)
    (by rw [minDeg_cocktailParty, vertexConn_cocktailParty]), minDeg_cocktailParty]

@[simp] theorem vertexConn_turan {n r : ℕ} (hr : 0 < r) (h : r ≤ n) :
    (turan n r).vertexConn = n - (n + r - 1) / r := by
  rw [show (turan n r).vertexConn = (turan n r).coverNum from
    vertexConn_completeMultipartite_eq_coverNum _, coverNum_turan hr h]

@[simp] theorem edgeConn_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) :
    (turan n r).edgeConn = n - (n + r - 1) / r := by
  rw [edgeConn_eq_minDeg _ (by rw [V_turan]; omega)
    (by rw [minDeg_turan (by omega) h, vertexConn_turan (by omega) h]), minDeg_turan (by omega) h]

/-! ### The friendship graphs

`friendship n` is a join too, but with a disconnected right factor — `n` disjoint edges — so the
hub is a cut vertex and the join formula returns `1`. -/

/-- The complement of a cocktail party graph is a perfect matching, and a perfect matching on four
or more vertices is disconnected: it has too few edges to span. -/
theorem not_isConnected_compl_cocktailParty (n : ℕ) :
    ¬ ((cocktailParty (n + 2))ᶜ).IsConnected := by
  intro h
  have hV := h.V_le_E_add_one
  rw [V_compl, V_cocktailParty] at hV
  have hE := E_compl (cocktailParty (n + 2))
  rw [E_cocktailParty, V_cocktailParty, Nat.choose_two_right] at hE
  have hchoose : 2 * (n + 2) * (2 * (n + 2) - 1) / 2 = (n + 2) * (2 * n + 3) := by
    rw [show 2 * (n + 2) - 1 = 2 * n + 3 by omega, mul_assoc,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hmul : (n + 2) * (2 * n + 3) = (n + 2) * (2 * (n + 2) - 2) + (n + 2) := by
    rw [show 2 * (n + 2) - 2 = 2 * n + 2 by omega]; ring
  omega

/-- **The hub of a friendship graph is a cut vertex**, and the only one. -/
@[simp] theorem vertexConn_friendship (n : ℕ) : (friendship (n + 2)).vertexConn = 1 := by
  have hj : friendship (n + 2) = complete 1 ∇g (cocktailParty (n + 2))ᶜ := by
    rw [compl_cocktailParty]
  rw [hj, vertexConn_join,
    (vertexConn_eq_zero_iff _).2 (Or.inr (not_isConnected_compl_cocktailParty n))]
  simp only [V_complete, V_compl, V_cocktailParty, vertexConn_complete]
  omega

/-- **A friendship graph is held together by two edges**, even though one vertex separates it: the
graph has diameter two, so `λ = δ = 2` while `κ = 1`.  This is the standard witness that Whitney's
chain is strict in the middle. -/
@[simp] theorem edgeConn_friendship (n : ℕ) : (friendship (n + 2)).edgeConn = 2 := by
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (diameter_friendship n)]
  simp

/-- **No friendship graph with two or more triangles is Hamiltonian**: a spanning cycle would have
to pass through the hub twice.  `friendship 1` is the triangle and is the only Hamiltonian one. -/
theorem not_isHamiltonian_friendship (n : ℕ) : ¬ (friendship (n + 2)).IsHamiltonian := fun h ↦ by
  have h2 := h.two_le_vertexConn (by rw [V_friendship]; omega)
  rw [vertexConn_friendship] at h2
  omega

/-! ### The families of diameter two

Plesník's theorem — `edgeConn_eq_minDeg_of_diameter_eq_two` — turns every diameter the gallery has
already recorded as `2` into an edge connectivity.  That covers the strongly regular families and
the complement of anything disconnected, and it says nothing at all about `κ`, which the friendship
graphs above show may be as small as `1`. -/

theorem edgeConn_grotzsch : grotzsch.edgeConn = 3 := by
  rw [edgeConn_eq_minDeg_of_diameter_eq_two diameter_grotzsch, minDeg_grotzsch]

/-- **The Grötzsch graph is `3`-connected.**  The upper bound is `κ ≤ λ`; for the lower bound, no
pair of vertices separates it. -/
theorem vertexConn_grotzsch : grotzsch.vertexConn = 3 := by
  refine le_antisymm ?_ ?_
  · rw [← edgeConn_grotzsch]
    exact vertexConn_le_edgeConn grotzsch
  · rw [show (grotzsch : IsoGraph) = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk,
      vertexConn_mk]
    have hcard : (CGraph.mycielskian (CGraph.cycle 5)).card = 11 := NamedGraphs.card_grotzsch
    exact (CGraph.mycielskian (CGraph.cycle 5)).le_vertexConn_of_forall_card_lt (by omega)
      (by native_decide)

@[simp] theorem edgeConn_rook (m n : ℕ) : (rook (m + 2) (n + 2)).edgeConn = m + n + 2 := by
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (diameter_rook m n)]
  simp
  omega

theorem edgeConn_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).edgeConn = 2 * (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (diameter_triangular hn), minDeg_triangular]
  simp

theorem edgeConn_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).edgeConn = (q - 1) / 2 :=
  (isSRGWith_paley q hq).edgeConn_eq (by omega) (by omega)

theorem edgeConn_kneser_two (m : ℕ) : (kneser (m + 5) 2).edgeConn = (m + 3).choose 2 := by
  have h : m + 5 - 2 = m + 3 := by omega
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (diameter_kneser_two m),
    minDeg_kneser (m + 5) 2 (by omega) (by omega), h]

theorem edgeConn_johnson {n k : ℕ} (hk : k ≤ n) (h2 : min k (n - k) = 2) :
    (johnson n k).edgeConn = k * (n - k) := by
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (by rw [diameter_johnson hk]; exact h2),
    minDeg_johnson hk]

/-! ### The strongly regular families, from below

Plesník says nothing about `κ`, and the theorem that does — that a strongly regular graph is
`k`-connected — is spectral.  What is left over is `IsSRGWith.mu_le_vertexConn`: a separator has
to hold all `μ` of the common neighbours of the pair it separates. -/

theorem mu_le_vertexConn_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) :
    (q - 1) / 4 ≤ (paley q).vertexConn :=
  (isSRGWith_paley q hq).mu_le_vertexConn (Nat.div_le_self _ _)

/-- Two non-adjacent vertices of `J(n, 2)` are disjoint pairs `{a, b}` and `{c, d}`, and the four
pairs `{a, c}`, `{a, d}`, `{b, c}`, `{b, d}` meet both — so `μ = 4`, and a separator needs four
vertices. -/
theorem four_le_vertexConn_johnson_two {n : ℕ} (hn : 4 ≤ n) : 4 ≤ (johnson n 2).vertexConn :=
  (isSRGWith_johnson_two n hn).mu_le_vertexConn (by
    have h := Nat.choose_le_choose 2 hn
    rw [show Nat.choose 4 2 = 6 from rfl] at h
    omega)

@[inherit_doc four_le_vertexConn_johnson_two]
theorem four_le_vertexConn_triangular {n : ℕ} (hn : 4 ≤ n) : 4 ≤ (triangular n).vertexConn :=
  four_le_vertexConn_johnson_two hn

/-- Two non-adjacent vertices of `K(n, 2)` are two pairs sharing a point, so they use three points
between them and have `C(n-3, 2)` common neighbours: the pairs on the points they leave alone. -/
theorem mu_le_vertexConn_kneser_two (n : ℕ) : (n - 3).choose 2 ≤ (kneser n 2).vertexConn := by
  refine (isSRGWith_kneser_two n).mu_le_vertexConn ?_
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h1 : (m + 2).choose 2 ≤ (m + 4).choose 2 := Nat.choose_le_choose 2 (by omega)
    have h2 : (m + 5).choose 2 = (m + 4).choose 2 + (m + 4) := choose_two_succ (m + 4)
    rw [show m + 5 - 3 = m + 2 from rfl]
    omega

/-- **The complement of a disconnected graph with an edge has `λ = δ`**, and its minimum degree is
what the largest degree of the original leaves behind. -/
theorem edgeConn_compl {G : IsoGraph} (h : ¬ IsConnected G) (hE : 0 < G.E) :
    Gᶜ.edgeConn = G.V - 1 - G.maxDeg := by
  have hV : 0 < G.V := by
    rcases Nat.eq_zero_or_pos G.V with h0 | hp
    · have hle := E_le_choose_two G
      rw [h0] at hle
      simp at hle
      omega
    · exact hp
  rw [edgeConn_eq_minDeg_of_diameter_eq_two (diameter_compl h hE), minDeg_compl hV]

/-- **The complement of a disjoint union is a join**, and a join is as connected as its two halves
allow: either you delete one side entirely, or you leave a cut of the other side in place. -/
theorem vertexConn_compl_disjUnion (G H : IsoGraph) :
    ((G ⊕g H)ᶜ).vertexConn
      = min (G.V + Hᶜ.vertexConn) (min (H.V + Gᶜ.vertexConn) (G.V + H.V - 1)) := by
  rw [compl_disjUnion, vertexConn_join, V_compl, V_compl]

/-! ### The families with a pendant vertex

At the other end of Whitney's chain: a connected graph with a vertex of degree one is cut in two
by deleting that vertex's neighbour, or by deleting its one edge. -/

@[simp] theorem vertexConn_doubleStar (m n : ℕ) : (doubleStar m n).vertexConn = 1 :=
  vertexConn_eq_one _ (by rw [V_doubleStar]; omega) (isConnected_doubleStar m n)
    (minDeg_doubleStar m n).le

@[simp] theorem edgeConn_doubleStar (m n : ℕ) : (doubleStar m n).edgeConn = 1 :=
  edgeConn_eq_one _ (by rw [V_doubleStar]; omega) (isConnected_doubleStar m n)
    (minDeg_doubleStar m n).le

@[simp] theorem vertexConn_spider (legs : List ℕ) (h : 0 < legs.sum) :
    (spider legs).vertexConn = 1 :=
  vertexConn_eq_one _ (by rw [V_spider]; omega) (isConnected_spider legs) (minDeg_spider legs h).le

@[simp] theorem edgeConn_spider (legs : List ℕ) (h : 0 < legs.sum) : (spider legs).edgeConn = 1 :=
  edgeConn_eq_one _ (by rw [V_spider]; omega) (isConnected_spider legs) (minDeg_spider legs h).le

@[simp] theorem vertexConn_tadpole (m k : ℕ) : (tadpole (m + 3) (k + 1)).vertexConn = 1 :=
  vertexConn_eq_one _ (by rw [V_tadpole]; omega) (isConnected_tadpole m (k + 1))
    (minDeg_tadpole m k).le

@[simp] theorem edgeConn_tadpole (m k : ℕ) : (tadpole (m + 3) (k + 1)).edgeConn = 1 :=
  edgeConn_eq_one _ (by rw [V_tadpole]; omega) (isConnected_tadpole m (k + 1))
    (minDeg_tadpole m k).le

@[simp] theorem vertexConn_lollipop (m k : ℕ) : (lollipop (m + 2) (k + 1)).vertexConn = 1 :=
  vertexConn_eq_one _ (by rw [V_lollipop]; omega) (isConnected_lollipop (m + 1) (k + 1))
    (minDeg_lollipop m k).le

@[simp] theorem edgeConn_lollipop (m k : ℕ) : (lollipop (m + 2) (k + 1)).edgeConn = 1 :=
  edgeConn_eq_one _ (by rw [V_lollipop]; omega) (isConnected_lollipop (m + 1) (k + 1))
    (minDeg_lollipop m k).le

@[simp] theorem vertexConn_cyclePendant (m : ℕ) (ks : List ℕ) (hl : ks.length ≤ m + 3)
    (hs : 0 < ks.sum) : (cyclePendant (m + 3) ks).vertexConn = 1 :=
  vertexConn_eq_one _ (by rw [V_cyclePendant]; omega) (isConnected_cyclePendant m ks hl)
    (minDeg_cyclePendant m ks hl hs).le

@[simp] theorem edgeConn_cyclePendant (m : ℕ) (ks : List ℕ) (hl : ks.length ≤ m + 3)
    (hs : 0 < ks.sum) : (cyclePendant (m + 3) ks).edgeConn = 1 :=
  edgeConn_eq_one _ (by rw [V_cyclePendant]; omega) (isConnected_cyclePendant m ks hl)
    (minDeg_cyclePendant m ks hl hs).le

/-! ### The Hamiltonian families

`IsHamiltonian.two_le_vertexConn` is the other cheap lower bound on `κ`: a spanning cycle leaves
no cut vertex behind.  For the ladders that meets Whitney's chain from above, since `δ = 2`, and
the two connectivities are pinned exactly.  For the rest it is a bound and no more — a cubic graph
given by an LCF notation is 3-connected as often as not, but which one it is depends on the
notation. -/

@[simp] theorem vertexConn_ladder (n : ℕ) : (ladder (n + 2)).vertexConn = 2 :=
  le_antisymm (by
      have := vertexConn_le_minDeg (ladder (n + 2)) (by rw [V_ladder]; omega)
      rwa [minDeg_ladder] at this)
    ((isHamiltonian_ladder (by omega)).two_le_vertexConn (by rw [V_ladder]; omega))

@[simp] theorem edgeConn_ladder (n : ℕ) : (ladder (n + 2)).edgeConn = 2 := by
  rw [edgeConn_eq_minDeg _ (by rw [V_ladder]; omega)
    (by rw [minDeg_ladder, vertexConn_ladder]), minDeg_ladder]

theorem two_le_vertexConn_prism (n : ℕ) : 2 ≤ (prism (n + 3)).vertexConn :=
  (isHamiltonian_prism (by omega)).two_le_vertexConn (by rw [V_prism]; omega)

theorem two_le_edgeConn_prism (n : ℕ) : 2 ≤ (prism (n + 3)).edgeConn :=
  (isHamiltonian_prism (by omega)).two_le_edgeConn (by rw [V_prism]; omega)

theorem two_le_vertexConn_crown (n : ℕ) : 2 ≤ (crown (n + 3)).vertexConn :=
  (isHamiltonian_crown (by omega)).two_le_vertexConn (by rw [V_crown]; omega)

theorem two_le_edgeConn_crown (n : ℕ) : 2 ≤ (crown (n + 3)).edgeConn :=
  (isHamiltonian_crown (by omega)).two_le_edgeConn (by rw [V_crown]; omega)

theorem two_le_vertexConn_circulant {n : ℕ} {S : List ℕ} (h3 : 3 ≤ n) (h1 : 1 ∈ S) :
    2 ≤ (circulant n S).vertexConn :=
  (isHamiltonian_circulant h3 h1).two_le_vertexConn (by rw [V_circulant]; omega)

theorem two_le_edgeConn_circulant {n : ℕ} {S : List ℕ} (h3 : 3 ≤ n) (h1 : 1 ∈ S) :
    2 ≤ (circulant n S).edgeConn :=
  (isHamiltonian_circulant h3 h1).two_le_edgeConn (by rw [V_circulant]; omega)

theorem two_le_vertexConn_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    2 ≤ (lcf ss r).vertexConn :=
  (isHamiltonian_lcf ss r h3).two_le_vertexConn (by rw [V_lcf]; omega)

theorem two_le_edgeConn_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    2 ≤ (lcf ss r).edgeConn :=
  (isHamiltonian_lcf ss r h3).two_le_edgeConn (by rw [V_lcf]; omega)

/-! ### The generalised Petersen graphs

`gp n k` is connected for every `n` and `k` — the spokes tie the inner vertices to the outer cycle
— so both its connectivities are at least one.  How much more they are depends on `k`, which is
what decides whether the inner vertices are joined to each other at all. -/

theorem one_le_vertexConn_gp {n k : ℕ} (hn : 0 < n) : 1 ≤ (gp n k).vertexConn :=
  ((gp n k).one_le_vertexConn_iff (by rw [V_gp]; omega)).2 (isConnected_gp hn)

theorem one_le_edgeConn_gp {n k : ℕ} (hn : 0 < n) : 1 ≤ (gp n k).edgeConn :=
  ((gp n k).one_le_edgeConn_iff (by rw [V_gp]; omega)).2 (isConnected_gp hn)

/-! ### Mycielskians

The Mycielskian of a graph with no isolated vertex is connected, and `edgeConn_mycielskian` pins
its edge connectivity at `δ(G) + 1`; Whitney's `κ ≤ λ` turns that into an upper bound on `κ`. -/

/-- The Mycielskian of a graph with no isolated vertex is connected, so `κ ≥ 1`. -/
theorem one_le_vertexConn_mycielskian {G : IsoGraph} (hV : 0 < G.V) (h : 0 < G.minDeg) :
    1 ≤ (mycielskian G).vertexConn :=
  ((mycielskian G).one_le_vertexConn_iff (by rw [V_mycielskian]; omega)).2
    (isConnected_mycielskian G h)

/-- `κ(μ G) ≤ δ(G) + 1`, from `λ(μ G) = δ(G) + 1`. -/
theorem vertexConn_mycielskian_le {G : IsoGraph} (hG : G.IsConnected) (hdG : G.diameter ≤ 2)
    (h2 : 2 ≤ G.V) : (mycielskian G).vertexConn ≤ G.minDeg + 1 :=
  le_of_le_of_eq (vertexConn_le_edgeConn (mycielskian G)) (edgeConn_mycielskian hG hdG h2)

/-! ### Theta graphs

A theta graph on one arc is a path and on two arcs a cycle, which settles both connectivities in
those two cases.  (Three arcs or more and `κ = λ = 2` again — the two branch vertices are the only
thing worth cutting — but that needs a separator argument rather than an identification.) -/

/-- A theta graph on one arc is a path: `λ = 1`. -/
theorem edgeConn_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).edgeConn = 1 := by
  rw [thetaGraph_singleton, edgeConn_path]

/-- A theta graph on one arc is a path: `κ = 1`. -/
theorem vertexConn_thetaGraph_singleton (k : ℕ) : (thetaGraph [k]).vertexConn = 1 := by
  rw [thetaGraph_singleton, vertexConn_path]

/-- A theta graph on two arcs is a cycle, so `λ = 2` unless both arcs are empty (when the graph is
`K₂`). -/
theorem edgeConn_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).edgeConn = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = m + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hm, edgeConn_cycle]

/-- A theta graph on two arcs is a cycle, so `κ = 2` unless both arcs are empty. -/
theorem vertexConn_thetaGraph_pair {a b : ℕ} (h : 0 < a + b) :
    (thetaGraph [a, b]).vertexConn = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 + a + b = m + 3 := ⟨a + b - 1, by omega⟩
  rw [thetaGraph_pair, hm, vertexConn_cycle]

/-! ### The prism

Whitney's chain `κ ≤ λ ≤ δ` collapses whenever its two ends meet, and for the prism they already
have: `minDeg_prism` and `vertexConn_prism` are both `3`. -/

@[simp] theorem edgeConn_prism (n : ℕ) : (prism (n + 3)).edgeConn = 3 := by
  rw [edgeConn_eq_minDeg _ (by rw [V_prism]; omega) (by rw [minDeg_prism, vertexConn_prism]),
    minDeg_prism]

/-! ### The families with a second description

A family member that the gallery already holds under another name arrives with that name's
connectivities, so the identifications settle a row of cases that no general argument reaches.
The circulant on a single shift is a cycle; `GP(4, 1)`, `[3, -3]⁴` and the four-point crown are
all the cube; `GP(5, 2)` is the Petersen graph and the three-point crown the hexagon; the Kneser
and Johnson graphs on singletons are complete, as is `T(3)`, while `T(4)` is the octahedron; the
folded cubes on two and three dimensions are `K₄` and `K₄,₄`; and the Paley graphs on five and
nine points are the pentagon and `K₃,₃,₃`. -/

theorem vertexConn_circulant_one (n : ℕ) : (circulant (n + 3) [1]).vertexConn = 2 := by
  rw [circulant_one]; exact vertexConn_cycle n

theorem edgeConn_circulant_one (n : ℕ) : (circulant (n + 3) [1]).edgeConn = 2 := by
  rw [circulant_one]; exact edgeConn_cycle n

theorem vertexConn_gp_four_one : (gp 4 1).vertexConn = 3 := by
  rw [gp_four_one_iso_hypercube]; exact vertexConn_hypercube 2

theorem edgeConn_gp_four_one : (gp 4 1).edgeConn = 3 := by
  rw [gp_four_one_iso_hypercube]; exact edgeConn_hypercube 2

theorem vertexConn_gp_five_two : (gp 5 2).vertexConn = 3 := by
  rw [gp_five_two_iso_petersen]; exact vertexConn_petersen

theorem edgeConn_gp_five_two : (gp 5 2).edgeConn = 3 := by
  rw [gp_five_two_iso_petersen]; exact edgeConn_petersen

theorem vertexConn_lcf_cube : (lcf [3, -3] 4).vertexConn = 3 := by
  rw [hypercube_three_lcf]; exact vertexConn_hypercube 2

theorem edgeConn_lcf_cube : (lcf [3, -3] 4).edgeConn = 3 := by
  rw [hypercube_three_lcf]; exact edgeConn_hypercube 2

theorem vertexConn_crown_three : (crown 3).vertexConn = 2 := by
  rw [crown_three]; exact vertexConn_cycle 3

theorem edgeConn_crown_three : (crown 3).edgeConn = 2 := by
  rw [crown_three]; exact edgeConn_cycle 3

theorem vertexConn_crown_four : (crown 4).vertexConn = 3 := by
  rw [crown_four]; exact vertexConn_hypercube 2

theorem edgeConn_crown_four : (crown 4).edgeConn = 3 := by
  rw [crown_four]; exact edgeConn_hypercube 2

theorem vertexConn_kneser_one (n : ℕ) : (kneser (n + 1) 1).vertexConn = n := by
  rw [kneser_one, vertexConn_complete, Nat.add_sub_cancel]

theorem edgeConn_kneser_one (n : ℕ) : (kneser (n + 1) 1).edgeConn = n := by
  rw [kneser_one, edgeConn_complete, Nat.add_sub_cancel]

theorem vertexConn_johnson_one (n : ℕ) : (johnson (n + 1) 1).vertexConn = n := by
  rw [johnson_one, vertexConn_complete, Nat.add_sub_cancel]

theorem edgeConn_johnson_one (n : ℕ) : (johnson (n + 1) 1).edgeConn = n := by
  rw [johnson_one, edgeConn_complete, Nat.add_sub_cancel]

theorem vertexConn_triangular_three : (triangular 3).vertexConn = 2 := by
  rw [triangular_three, vertexConn_complete]

/-- `T(4)` is the octahedron, so `four_le_vertexConn_triangular` is sharp at `n = 4`. -/
theorem vertexConn_triangular_four : (triangular 4).vertexConn = 4 := by
  rw [triangular_four]; exact vertexConn_cocktailParty 2

theorem vertexConn_foldedCube_two : (foldedCube 2).vertexConn = 3 := by
  rw [foldedCube_two, vertexConn_complete]

theorem vertexConn_foldedCube_three : (foldedCube 3).vertexConn = 4 := by
  rw [foldedCube_three, vertexConn_bipartite, min_self]

theorem vertexConn_paley_five : (paley 5).vertexConn = 2 := by
  rw [paley_five]; exact vertexConn_cycle 2

theorem vertexConn_paley_nine : (paley 9).vertexConn = 6 := by
  rw [paley_nine, vertexConn_completeMultipartite]
  rfl

/-! ### The operators with a second description

Three of the operators hand back a graph the gallery already has.  The line graph of a cycle is
that cycle again and the line graph of a star is complete; a strong product of edgeless graphs is
edgeless; and the Mycielskian of an edgeless graph is a star beside an independent set, so both
its connectivities are the zero that any disconnected graph has. -/

theorem vertexConn_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).vertexConn = 2 := by
  rw [lineGraph_cycle]; exact vertexConn_cycle n

theorem edgeConn_lineGraph_cycle (n : ℕ) : ((cycle (n + 3)).lineGraph).edgeConn = 2 := by
  rw [lineGraph_cycle]; exact edgeConn_cycle n

theorem vertexConn_lineGraph_star (n : ℕ) : ((star (n + 1)).lineGraph).vertexConn = n := by
  rw [lineGraph_star, vertexConn_complete, Nat.add_sub_cancel]

theorem edgeConn_lineGraph_star (n : ℕ) : ((star (n + 1)).lineGraph).edgeConn = n := by
  rw [lineGraph_star, edgeConn_complete, Nat.add_sub_cancel]

theorem vertexConn_strongProduct_empty (m n : ℕ) : (empty m ⊠g empty n).vertexConn = 0 := by
  rw [strongProduct_empty]; exact vertexConn_empty _

theorem edgeConn_strongProduct_empty (m n : ℕ) : (empty m ⊠g empty n).edgeConn = 0 := by
  rw [strongProduct_empty]; exact edgeConn_empty _

theorem vertexConn_mycielskian_empty (n : ℕ) : (mycielskian (empty (n + 1))).vertexConn = 0 := by
  rw [mycielskian_empty]
  exact vertexConn_disjUnion (by simp) (by simp)

theorem edgeConn_mycielskian_empty (n : ℕ) : (mycielskian (empty (n + 1))).edgeConn = 0 := by
  rw [mycielskian_empty]
  exact edgeConn_disjUnion (by simp) (by simp)

end IsoGraph
