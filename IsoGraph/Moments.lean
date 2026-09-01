import IsoGraph.Spectrum
import IsoGraph.SmallGraphs

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# A spectrum from one polynomial identity and four traces

Every spectral formula in `IsoGraph/Spectrum.lean` needs some structure to hold on to: a product,
a regular graph, a strongly regular one.  The Grötzsch graph — the Mycielskian of the pentagon —
has none of it.  Its eleven eigenvalues are `1` five times over and two conjugate pairs,
`(-3 ± √5) / 2` twice each and `(1 ± √41) / 2` once each, and nothing in the library reaches them.

They are still only two matrix computations away.  The first is a polynomial identity: the
adjacency matrix satisfies its minimal polynomial, which here is a quintic, and checking that is a
question about a `11 × 11` integer matrix.  Multiplying the identity into an eigenvector turns it
into a statement about numbers — every eigenvalue is a root of the quintic — and the quintic
factors into a linear term and the two quadratics `x ^ 2 + 3 x + 1` and `x ^ 2 - x - 10`.

That leaves the five multiplicities, and five unknowns want five equations.  The order of the
graph is one; the traces of `A`, `A ^ 2`, `A ^ 3` and `A ^ 4` are the other four, each again an
integer matrix computation, and `sum_pow_spectrum` reads each one as a power sum of the
eigenvalues.  Using `√5 ^ 2 = 5` and `√41 ^ 2 = 41` to flatten the powers leaves a linear system
with rational coefficients — and with the two members of a conjugate pair appearing only through
their sum and through the difference of their multiplicities, which the system forces to zero.

Only the numbers are special to the Grötzsch graph.  The three lemmas the argument runs on —
`Multiset.eq_sum_replicate`, `CGraph.adjMat_pow_mulVec` and `CGraph.trace_adjMat_pow_eq_int` — are
stated for anything, and any graph whose minimal polynomial is short enough to check can be done
the same way.
-/

open Polynomial

/-- A multiset all of whose elements lie in `s` is the sum of its constant blocks, one for each
element of `s`. -/
theorem Multiset.eq_sum_replicate {α : Type*} [DecidableEq α] {m : Multiset α} {s : Finset α}
    (h : ∀ x ∈ m, x ∈ s) : m = ∑ x ∈ s, Multiset.replicate (m.count x) x := by
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq m]
  rw [Finset.sum_subset (fun x hx ↦ h x (Multiset.mem_toFinset.1 hx))
    (fun x _ hx ↦ by rw [Multiset.count_eq_zero_of_notMem (by simpa using hx), zero_nsmul])]
  exact Finset.sum_congr rfl fun x _ ↦ Multiset.nsmul_singleton _ _

namespace CGraph

/-! ## The general lemmas -/

/-- An eigenvector of `G` is an eigenvector of every power of the adjacency matrix, for the
corresponding power of the eigenvalue. -/
theorem adjMat_pow_mulVec {G : CGraph} {x : ℝ} {v : G.V → ℝ}
    (h : G.adjMat.mulVec v = x • v) (k : ℕ) : (G.adjMat ^ k).mulVec v = (x ^ k) • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- **The moments of the spectrum are integers**: the trace of a power of the adjacency matrix can
be computed over `ℤ`, where `decide` can reach it. -/
theorem trace_adjMat_pow_eq_int (G : CGraph) (n : ℕ) :
    (G.adjMat ^ n).trace = ((G.adjMatInt ^ n).trace : ℝ) := by
  have h : G.adjMat ^ n = (G.adjMatInt ^ n).map (Int.castRingHom ℝ) := by
    rw [adjMat_eq_map_adjMatInt, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  rw [h, Matrix.trace, Matrix.trace]
  push_cast
  rfl

/-- A conjugate pair of eigenvalues contributes a factor with integer coefficients: the pair is
recovered from its sum and its product. -/
private theorem quad_eq {a b : ℝ} {s t : ℤ} (hs : a + b = s) (ht : a * b = t) :
    (X - C a) * (X - C b) = X ^ 2 - (s : ℝ[X]) * X + (t : ℝ[X]) := by
  have h : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    rw [map_add, map_mul]; ring
  rw [h, hs, ht, map_intCast, map_intCast]

/-! ## The Grötzsch graph -/

open NamedGraphs

/-- **The minimal polynomial of the Grötzsch graph**, over `ℤ`: the quintic
`x ^ 5 + x ^ 4 - 14 x ^ 3 - 19 x ^ 2 + 21 x + 10`, written with both sides positive so that the
check never leaves `ℕ`-shaped arithmetic. -/
theorem grotzsch_poly_int :
    grotzsch.adjMatInt ^ 5 + grotzsch.adjMatInt ^ 4 + 21 * grotzsch.adjMatInt + 10
      = 14 * grotzsch.adjMatInt ^ 3 + 19 * grotzsch.adjMatInt ^ 2 := by
  native_decide

private theorem trace_grotzsch_one : (grotzsch.adjMatInt ^ 1).trace = 0 := by native_decide

private theorem trace_grotzsch_two : (grotzsch.adjMatInt ^ 2).trace = 40 := by native_decide

private theorem trace_grotzsch_three : (grotzsch.adjMatInt ^ 3).trace = 0 := by native_decide

private theorem trace_grotzsch_four : (grotzsch.adjMatInt ^ 4).trace = 340 := by native_decide

/-- The same identity over `ℝ`, where the eigenvectors live. -/
theorem grotzsch_poly :
    grotzsch.adjMat ^ 5 + grotzsch.adjMat ^ 4 + 21 * grotzsch.adjMat + 10
      = 14 * grotzsch.adjMat ^ 3 + 19 * grotzsch.adjMat ^ 2 := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix grotzsch_poly_int
  simp only [map_add, map_mul, map_pow, map_ofNat] at h
  rwa [RingHom.mapMatrix_apply, ← adjMat_eq_map_adjMatInt] at h

/-- Every eigenvalue of the Grötzsch graph is a root of the quintic, hence one of five reals. -/
private theorem eq_of_mem_spectrum_grotzsch {x : ℝ} (hx : x ∈ grotzsch.spectrum) :
    x = 1 ∨ x = (-3 + Real.sqrt 5) / 2 ∨ x = (-3 - Real.sqrt 5) / 2
      ∨ x = (1 + Real.sqrt 41) / 2 ∨ x = (1 - Real.sqrt 41) / 2 := by
  have hp2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq2 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  set p := Real.sqrt 5
  set q := Real.sqrt 41
  obtain ⟨v, hv0, hv⟩ := (mem_spectrum_iff grotzsch x).1 hx
  have hpx : x ^ 5 + x ^ 4 - 14 * x ^ 3 - 19 * x ^ 2 + 21 * x + 10 = 0 := by
    have h := congrArg (fun M : Matrix grotzsch.V grotzsch.V ℝ ↦ M.mulVec v) grotzsch_poly
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, adjMat_pow_mulVec hv, hv,
      Matrix.ofNat_mulVec] at h
    have h2 : (x ^ 5 + x ^ 4 - 14 * x ^ 3 - 19 * x ^ 2 + 21 * x + 10) • v = 0 := by
      linear_combination (norm := module) h
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 hv0
  have hfac : (x - 1) * ((x - (1 + q) / 2) * (x - (1 - q) / 2))
      * ((x - (-3 + p) / 2) * (x - (-3 - p) / 2)) = 0 := by
    linear_combination hpx - ((x - 1) * (2 * x - 1 - q) * (2 * x - 1 + q) / 16) * hp2
      - ((x - 1) * (x ^ 2 + 3 * x + 1) / 4) * hq2
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact Or.inl (by linarith only [h'])
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith only [h'']))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith only [h'']))))
  · rcases mul_eq_zero.1 h with h' | h'
    · exact Or.inr (Or.inl (by linarith only [h']))
    · exact Or.inr (Or.inr (Or.inl (by linarith only [h'])))

/-- **The spectrum of the Grötzsch graph**: `1` five times, `(-3 ± √5) / 2` twice each, and
`(1 ± √41) / 2` once each. -/
theorem spectrum_grotzsch :
    grotzsch.spectrum = (1 + Real.sqrt 41) / 2 ::ₘ (1 - Real.sqrt 41) / 2 ::ₘ
      (Multiset.replicate 5 1 + Multiset.replicate 2 ((-3 + Real.sqrt 5) / 2)
        + Multiset.replicate 2 ((-3 - Real.sqrt 5) / 2)) := by
  classical
  have hp2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq2 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have hp0 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hq0 : (0 : ℝ) < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
  set p := Real.sqrt 5
  set q := Real.sqrt 41
  have hp3 : p < 9 / 4 := by nlinarith only [hp2, hp0]
  have hq1 : 32 / 5 < q := by nlinarith only [hq2, hq0]
  -- the five candidates, in increasing order
  have ho1 : (1 - q) / 2 < (-3 - p) / 2 := by linarith only [hp3, hq1]
  have ho2 : (-3 - p) / 2 < (-3 + p) / 2 := by linarith only [hp0]
  have ho3 : (-3 + p) / 2 < 1 := by linarith only [hp3]
  have ho4 : (1 : ℝ) < (1 + q) / 2 := by linarith only [hq1]
  have hmem : ∀ x ∈ grotzsch.spectrum,
      x ∈ ({1, (-3 + p) / 2, (-3 - p) / 2, (1 + q) / 2, (1 - q) / 2} : Finset ℝ) := by
    intro x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using eq_of_mem_spectrum_grotzsch hx
  -- so the spectrum is five blocks, of sizes yet to be found
  have hn1 : (1 : ℝ) ∉ ({(-3 + p) / 2, (-3 - p) / 2, (1 + q) / 2, (1 - q) / 2} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h) <;> linarith only [h, ho1, ho2, ho3, ho4]
  have hn2 : (-3 + p) / 2 ∉ ({(-3 - p) / 2, (1 + q) / 2, (1 - q) / 2} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h) <;> linarith only [h, ho1, ho2, ho3, ho4]
  have hn3 : (-3 - p) / 2 ∉ ({(1 + q) / 2, (1 - q) / 2} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h) <;> linarith only [h, ho1, ho2, ho3, ho4]
  have hn4 : (1 + q) / 2 ∉ ({(1 - q) / 2} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    intro h
    linarith only [h, ho1, ho2, ho3, ho4]
  have hdecomp := Multiset.eq_sum_replicate hmem
  rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3, Finset.sum_insert hn4,
    Finset.sum_singleton] at hdecomp
  obtain ⟨a, ha⟩ : ∃ k, grotzsch.spectrum.count 1 = k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ k, grotzsch.spectrum.count ((-3 + p) / 2) = k := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ k, grotzsch.spectrum.count ((-3 - p) / 2) = k := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ k, grotzsch.spectrum.count ((1 + q) / 2) = k := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ k, grotzsch.spectrum.count ((1 - q) / 2) = k := ⟨_, rfl⟩
  rw [ha, hb, hc, hd, he] at hdecomp
  -- the five blocks account for eleven vertices
  have hcard : a + b + c + d + e = 11 := by
    have h := card_spectrum grotzsch
    rw [hdecomp, show FinEnum.card grotzsch.V = 11 from by
      rw [card_mycielskian, card_cycle]] at h
    simp only [Multiset.card_add, Multiset.card_replicate] at h
    omega
  -- and reproduce the first four moments
  have hmoment : ∀ k : ℕ, (a : ℝ) * 1 ^ k + b * ((-3 + p) / 2) ^ k + c * ((-3 - p) / 2) ^ k
      + d * ((1 + q) / 2) ^ k + e * ((1 - q) / 2) ^ k = ((grotzsch.adjMatInt ^ k).trace : ℝ) := by
    intro k
    rw [← trace_adjMat_pow_eq_int, ← sum_pow_spectrum, hdecomp]
    simp only [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add, Multiset.sum_replicate,
      nsmul_eq_mul]
    ring
  have h1 := hmoment 1
  have h2 := hmoment 2
  have h3 := hmoment 3
  have h4 := hmoment 4
  rw [trace_grotzsch_one] at h1
  rw [trace_grotzsch_two] at h2
  rw [trace_grotzsch_three] at h3
  rw [trace_grotzsch_four] at h4
  push_cast at h1 h2 h3 h4
  -- reduce the powers of the two conjugate pairs to their linear parts
  have m0 : (a : ℝ) + b + c + d + e = 11 := by exact_mod_cast hcard
  have m1 : (a : ℝ) - 3 / 2 * ((b : ℝ) + c) + ((b : ℝ) * p - c * p) / 2 + ((d : ℝ) + e) / 2
      + ((d : ℝ) * q - e * q) / 2 = 0 := by linear_combination h1
  have m2 : (a : ℝ) + 7 / 2 * ((b : ℝ) + c) - 3 / 2 * ((b : ℝ) * p - c * p)
      + 21 / 2 * ((d : ℝ) + e) + ((d : ℝ) * q - e * q) / 2 = 40 := by
    linear_combination h2 - (((b : ℝ) + c) / 4) * hp2 - (((d : ℝ) + e) / 4) * hq2
  have m3 : (a : ℝ) - 9 * ((b : ℝ) + c) + 4 * ((b : ℝ) * p - c * p) + 31 / 2 * ((d : ℝ) + e)
      + 11 / 2 * ((d : ℝ) * q - e * q) = 0 := by
    linear_combination h3 - (((b : ℝ) * p - 9 * b - c * p - 9 * c) / 8) * hp2
      - (((d : ℝ) * q + 3 * d - e * q + 3 * e) / 8) * hq2
  have m4 : (a : ℝ) + 47 / 2 * ((b : ℝ) + c) - 21 / 2 * ((b : ℝ) * p - c * p)
      + 241 / 2 * ((d : ℝ) + e) + 21 / 2 * ((d : ℝ) * q - e * q) = 340 := by
    linear_combination h4
      - (((b : ℝ) * p ^ 2 - 12 * b * p + 59 * b + c * p ^ 2 + 12 * c * p + 59 * c) / 16) * hp2
      - (((d : ℝ) * q ^ 2 + 4 * d * q + 47 * d + e * q ^ 2 - 4 * e * q + 47 * e) / 16) * hq2
  -- five linear equations with rational coefficients
  have hA : (a : ℝ) = 5 := by linarith only [m0, m1, m2, m3, m4]
  have hBC : (b : ℝ) + c = 4 := by linarith only [m0, m1, m2, m3, m4]
  have hBCp : (b : ℝ) * p - c * p = 0 := by linarith only [m0, m1, m2, m3, m4]
  have hDE : (d : ℝ) + e = 2 := by linarith only [m0, m1, m2, m3, m4]
  have hDEq : (d : ℝ) * q - e * q = 0 := by linarith only [m0, m1, m2, m3, m4]
  -- the two eigenvalues of a conjugate pair have the same multiplicity
  have hbc : (b : ℝ) = c := by
    rcases mul_eq_zero.1 (show ((b : ℝ) - c) * p = 0 by linear_combination hBCp) with h | h
    · linarith only [h]
    · exact absurd h hp0.ne'
  have hde : (d : ℝ) = e := by
    rcases mul_eq_zero.1 (show ((d : ℝ) - e) * q = 0 by linear_combination hDEq) with h | h
    · linarith only [h]
    · exact absurd h hq0.ne'
  have ha5 : a = 5 := by exact_mod_cast hA
  have hb2 : b = 2 := by
    have h : (b : ℝ) = 2 := by linarith only [hBC, hbc]
    exact_mod_cast h
  have hc2 : c = 2 := by
    have h : (c : ℝ) = 2 := by linarith only [hBC, hbc]
    exact_mod_cast h
  have hd1 : d = 1 := by
    have h : (d : ℝ) = 1 := by linarith only [hDE, hde]
    exact_mod_cast h
  have he1 : e = 1 := by
    have h : (e : ℝ) = 1 := by linarith only [hDE, hde]
    exact_mod_cast h
  rw [hdecomp, ha5, hb2, hc2, hd1, he1]
  simp only [Multiset.replicate_one, ← Multiset.singleton_add]
  abel

/-- **The characteristic polynomial of the Grötzsch graph**: the two conjugate pairs pair up into
quadratics, so the answer is an integer polynomial even though three of its roots are not. -/
theorem charpoly_grotzsch :
    grotzsch.charpoly = (X - 1) ^ 5 * (X ^ 2 + 3 * X + 1) ^ 2 * (X ^ 2 - X - 10) := by
  have hp2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq2 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  rw [charpoly_eq_prod_spectrum, spectrum_grotzsch]
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add, Multiset.prod_add,
    Multiset.map_replicate, Multiset.prod_replicate, map_one]
  set p := Real.sqrt 5
  set q := Real.sqrt 41
  have h1 : (X - C ((-3 + p) / 2)) * (X - C ((-3 - p) / 2)) = X ^ 2 + 3 * X + 1 := by
    have h := quad_eq (a := (-3 + p) / 2) (b := (-3 - p) / 2) (s := -3) (t := 1)
      (by push_cast; ring) (by push_cast; linear_combination -hp2 / 4)
    rw [h]; push_cast; ring
  have h2 : (X - C ((1 + q) / 2)) * (X - C ((1 - q) / 2)) = X ^ 2 - X - 10 := by
    have h := quad_eq (a := (1 + q) / 2) (b := (1 - q) / 2) (s := 1) (t := -10)
      (by push_cast; ring) (by push_cast; linear_combination -hq2 / 4)
    rw [h]; push_cast; ring
  linear_combination ((X - 1) ^ 5 * ((X - C ((1 + q) / 2)) * (X - C ((1 - q) / 2)))
      * ((X - C ((-3 + p) / 2)) * (X - C ((-3 - p) / 2)) + (X ^ 2 + 3 * X + 1))) * h1
    + ((X - 1) ^ 5 * (X ^ 2 + 3 * X + 1) ^ 2) * h2

/-- **The energy of the Grötzsch graph** is `11 + √41`: the `√5` in the middle pair cancels
between the two conjugates, and only the outer pair leaves a surd behind. -/
theorem energy_grotzsch : grotzsch.energy = 11 + Real.sqrt 41 := by
  have hp0 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hq0 : (0 : ℝ) < Real.sqrt 41 := Real.sqrt_pos.2 (by norm_num)
  have hp2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq2 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  rw [energy, spectrum_grotzsch]
  set p := Real.sqrt 5
  set q := Real.sqrt 41
  have hp3 : p < 3 := by nlinarith only [hp2, hp0]
  have hq1 : 1 < q := by nlinarith only [hq2, hq0]
  have e1 : |(1 + q) / 2| = (1 + q) / 2 := abs_of_pos (by linarith only [hq0])
  have e2 : |(1 - q) / 2| = -((1 - q) / 2) := abs_of_neg (by linarith only [hq1])
  have e3 : |(-3 + p) / 2| = -((-3 + p) / 2) := abs_of_neg (by linarith only [hp3])
  have e4 : |(-3 - p) / 2| = -((-3 - p) / 2) := abs_of_neg (by linarith only [hp0])
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul, e1, e2, e3, e4, abs_one]
  ring

end CGraph

namespace IsoGraph

/-! ## The Grötzsch graph, as an isomorphism class -/

/-- **The spectrum of the Grötzsch graph**: `1` five times, `(-3 ± √5) / 2` twice each, and
`(1 ± √41) / 2` once each. -/
theorem spectrum_grotzsch :
    grotzsch.spectrum = (1 + Real.sqrt 41) / 2 ::ₘ (1 - Real.sqrt 41) / 2 ::ₘ
      (Multiset.replicate 5 1 + Multiset.replicate 2 ((-3 + Real.sqrt 5) / 2)
        + Multiset.replicate 2 ((-3 - Real.sqrt 5) / 2)) := by
  rw [show (grotzsch : IsoGraph) = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk,
    spectrum_mk]
  exact CGraph.spectrum_grotzsch

/-- **The characteristic polynomial of the Grötzsch graph.** -/
theorem charpoly_grotzsch :
    grotzsch.charpoly = (X - 1) ^ 5 * (X ^ 2 + 3 * X + 1) ^ 2 * (X ^ 2 - X - 10) := by
  rw [show (grotzsch : IsoGraph) = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk,
    charpoly_mk]
  exact CGraph.charpoly_grotzsch

/-- **The energy of the Grötzsch graph** is `11 + √41`. -/
theorem energy_grotzsch : grotzsch.energy = 11 + Real.sqrt 41 := by
  rw [show (grotzsch : IsoGraph) = mycielskian (cycle 5) from rfl, cycle_def, mycielskian_mk,
    energy_mk]
  exact CGraph.energy_grotzsch

end IsoGraph
