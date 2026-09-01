import IsoGraph.SmallGraphs
import IsoGraph.Algebra.Semiring

-- A `CGraph` carries its vertex type as a field, so unification only sees `Gᶜ.V` as `G.V`
-- by unfolding the operation; see the note after `CGraph.enum` in `IsoGraph/Basic.lean`.
set_option backward.isDefEq.respectTransparency false

/-!
# The components of a construction

`comps a` is the multiset of connected components of `a`, taken as isomorphism classes, and
`sum_comps` says that they add back up to `a`.  A connected graph is therefore its own only
component, and `comps a = {a}` is exactly the statement that `a` is an atom of the additive monoid:
it is not a disjoint union of two nonempty graphs.  That is the answer at almost every construction
in the library, so each entry below is `comps_eq_singleton` applied to a component count proved
elsewhere, and what varies from line to line is only the hypothesis that makes the construction
connected.

The interesting entries are the ones that do split.  `empty n` is `n` copies of the one-vertex
graph; `circulant n []` and `kneser n k` for `n < 2k` are `empty` under another name; and a
disjoint union adds the two multisets, which is `comps_disjUnion` and the reason the multiset is
the right object to record.
-/

namespace IsoGraph

/-! ### Components of an operation -/

@[simp] theorem comps_cartesianProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G □g H).comps = {G □g H} :=
  comps_eq_singleton
    (numComponents_eq_one_of_isConnected (isConnected_cartesianProduct.2 ⟨hG, hH⟩))

@[simp] theorem comps_join {G H : IsoGraph} (hG : 0 < G.V) (hH : 0 < H.V) :
    (G ∇g H).comps = {G ∇g H} :=
  comps_eq_singleton (numComponents_join hG hH)

@[simp] theorem comps_lexProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ·g H).comps = {G ·g H} :=
  comps_eq_singleton (numComponents_lexProduct hG hH)

@[simp] theorem comps_strongProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H) :
    (G ⊠g H).comps = {G ⊠g H} :=
  comps_eq_singleton (numComponents_strongProduct hG hH)

/-- Weichsel's condition: a tensor product is connected when both factors are and one of them
carries an odd cycle. -/
@[simp] theorem comps_tensorProduct {G H : IsoGraph} (hG : IsConnected G) (hH : IsConnected H)
    (hb : ¬ IsBipartite G) (hE : 0 < H.E) : (G ⊗g H).comps = {G ⊗g H} :=
  comps_eq_singleton (numComponents_tensorProduct hG hH hb hE)

/-- A complement is connected as soon as the graph is not: the two components see each other
across every non-edge. -/
@[simp] theorem comps_compl {G : IsoGraph} (h : 2 ≤ G.numComponents) : Gᶜ.comps = {Gᶜ} :=
  comps_eq_singleton (numComponents_compl_eq_one h)

@[simp] theorem comps_lineGraph {G : IsoGraph} (hc : IsConnected G) (he : 0 < G.E) :
    (lineGraph G).comps = {lineGraph G} :=
  comps_eq_singleton (numComponents_lineGraph hc he)

@[simp] theorem comps_mycielskian {G : IsoGraph} (h : 0 < G.minDeg) :
    (mycielskian G).comps = {mycielskian G} :=
  comps_eq_singleton (numComponents_mycielskian G h)

/-! ### Components of a family

Every family in the gallery is connected at the parameters where it is interesting, and the
hypotheses here are the ones under which that was proved. -/

@[simp] theorem comps_bipartite (m n : ℕ) :
    (bipartite (m + 1) (n + 1)).comps = {bipartite (m + 1) (n + 1)} :=
  comps_eq_singleton (numComponents_bipartite m n)

@[simp] theorem comps_book (n : ℕ) : (book n).comps = {book n} :=
  comps_eq_singleton (numComponents_book n)

@[simp] theorem comps_chang₁ : chang₁.comps = {chang₁} := comps_eq_singleton numComponents_chang₁

@[simp] theorem comps_chang₂ : chang₂.comps = {chang₂} := comps_eq_singleton numComponents_chang₂

@[simp] theorem comps_chang₃ : chang₃.comps = {chang₃} := comps_eq_singleton numComponents_chang₃

@[simp] theorem comps_circulant_one (n : ℕ) :
    (circulant (n + 1) [1]).comps = {circulant (n + 1) [1]} :=
  comps_eq_singleton (numComponents_circulant_one n)

@[simp] theorem comps_cocktailParty (n : ℕ) :
    (cocktailParty (n + 2)).comps = {cocktailParty (n + 2)} :=
  comps_eq_singleton (numComponents_cocktailParty n)

@[simp] theorem comps_complete (n : ℕ) : (complete (n + 1)).comps = {complete (n + 1)} :=
  comps_eq_singleton (numComponents_complete n)

@[simp] theorem comps_completeMultipartite_replicate (m d : ℕ) :
    (completeMultipartite (List.replicate (m + 2) (d + 1))).comps
      = {completeMultipartite (List.replicate (m + 2) (d + 1))} :=
  comps_eq_singleton (numComponents_completeMultipartite_replicate m d)

@[simp] theorem comps_crown (n : ℕ) : (crown (n + 3)).comps = {crown (n + 3)} :=
  comps_eq_singleton (numComponents_crown n)

@[simp] theorem comps_cycle (n : ℕ) : (cycle (n + 1)).comps = {cycle (n + 1)} :=
  comps_eq_singleton (numComponents_cycle n)

@[simp] theorem comps_cyclePendant (m : ℕ) (ks : List ℕ) (h : ks.length ≤ m + 3) :
    (cyclePendant (m + 3) ks).comps = {cyclePendant (m + 3) ks} :=
  comps_eq_singleton (numComponents_cyclePendant m ks h)

@[simp] theorem comps_doubleStar (m n : ℕ) : (doubleStar m n).comps = {doubleStar m n} :=
  comps_eq_singleton (numComponents_doubleStar m n)

@[simp] theorem comps_fan (n : ℕ) : (fan (n + 1)).comps = {fan (n + 1)} :=
  comps_eq_singleton (numComponents_fan n)

@[simp] theorem comps_foldedCube (n : ℕ) : (foldedCube (n + 1)).comps = {foldedCube (n + 1)} :=
  comps_eq_singleton (numComponents_foldedCube n)

@[simp] theorem comps_friendship (n : ℕ) : (friendship (n + 1)).comps = {friendship (n + 1)} :=
  comps_eq_singleton (numComponents_friendship n)

@[simp] theorem comps_gewirtz : gewirtz.comps = {gewirtz} :=
  comps_eq_singleton numComponents_gewirtz

@[simp] theorem comps_gp {n k : ℕ} (hn : 0 < n) : (gp n k).comps = {gp n k} :=
  comps_eq_singleton (numComponents_gp hn)

@[simp] theorem comps_grotzsch : grotzsch.comps = {grotzsch} :=
  comps_eq_singleton numComponents_grotzsch

@[simp] theorem comps_higmanSims : higmanSims.comps = {higmanSims} :=
  comps_eq_singleton numComponents_higmanSims

@[simp] theorem comps_hoffmanSingleton : hoffmanSingleton.comps = {hoffmanSingleton} :=
  comps_eq_singleton numComponents_hoffmanSingleton

@[simp] theorem comps_hypercube (n : ℕ) : (hypercube n).comps = {hypercube n} :=
  comps_eq_singleton (numComponents_hypercube n)

@[simp] theorem comps_johnson {n k : ℕ} (hk : k ≤ n) : (johnson n k).comps = {johnson n k} :=
  comps_eq_singleton (numComponents_johnson hk)

@[simp] theorem comps_kneser_two (m : ℕ) : (kneser (m + 5) 2).comps = {kneser (m + 5) 2} :=
  comps_eq_singleton (numComponents_kneser_two m)

@[simp] theorem comps_ladder (n : ℕ) : (ladder (n + 1)).comps = {ladder (n + 1)} :=
  comps_eq_singleton (numComponents_ladder n)

@[simp] theorem comps_lcf (ss : List ℤ) (r : ℕ) (h3 : 3 ≤ ss.length * r) :
    (lcf ss r).comps = {lcf ss r} :=
  comps_eq_singleton (numComponents_lcf ss r h3)

@[simp] theorem comps_linesOnCubic : linesOnCubic.comps = {linesOnCubic} :=
  comps_eq_singleton numComponents_linesOnCubic

@[simp] theorem comps_lollipop (m k : ℕ) : (lollipop (m + 1) k).comps = {lollipop (m + 1) k} :=
  comps_eq_singleton (numComponents_lollipop m k)

@[simp] theorem comps_m22 : m22.comps = {m22} := comps_eq_singleton numComponents_m22

@[simp] theorem comps_paley (q : ℕ) [NeZero q] [Fact q.Prime] (hq : q % 4 = 1) (hq5 : 5 ≤ q) :
    (paley q).comps = {paley q} :=
  comps_eq_singleton (numComponents_paley q hq hq5)

@[simp] theorem comps_path (n : ℕ) : (path (n + 1)).comps = {path (n + 1)} :=
  comps_eq_singleton (numComponents_path n)

@[simp] theorem comps_petersen : petersen.comps = {petersen} :=
  comps_eq_singleton numComponents_petersen

@[simp] theorem comps_prism (n : ℕ) : (prism (n + 1)).comps = {prism (n + 1)} :=
  comps_eq_singleton (numComponents_prism n)

@[simp] theorem comps_rook (m n : ℕ) : (rook (m + 1) (n + 1)).comps = {rook (m + 1) (n + 1)} :=
  comps_eq_singleton (numComponents_rook m n)

@[simp] theorem comps_schlafli : schlafli.comps = {schlafli} :=
  comps_eq_singleton numComponents_schlafli

@[simp] theorem comps_shrikhande : shrikhande.comps = {shrikhande} :=
  comps_eq_singleton numComponents_shrikhande

@[simp] theorem comps_spider (legs : List ℕ) : (spider legs).comps = {spider legs} :=
  comps_eq_singleton (numComponents_spider legs)

@[simp] theorem comps_star (n : ℕ) : (star n).comps = {star n} :=
  comps_eq_singleton (numComponents_star n)

@[simp] theorem comps_tadpole (m k : ℕ) : (tadpole (m + 3) k).comps = {tadpole (m + 3) k} :=
  comps_eq_singleton (numComponents_tadpole m k)

@[simp] theorem comps_thetaGraph_pair (a b : ℕ) :
    (thetaGraph [a, b]).comps = {thetaGraph [a, b]} :=
  comps_eq_singleton (numComponents_thetaGraph_pair a b)

@[simp] theorem comps_triangular {n : ℕ} (hn : 4 ≤ n) : (triangular n).comps = {triangular n} :=
  comps_eq_singleton (numComponents_triangular hn)

@[simp] theorem comps_turan {n r : ℕ} (hr : 2 ≤ r) (h : r ≤ n) : (turan n r).comps = {turan n r} :=
  comps_eq_singleton (numComponents_turan hr h)

@[simp] theorem comps_wheel (n : ℕ) : (wheel (n + 1)).comps = {wheel (n + 1)} :=
  comps_eq_singleton (numComponents_wheel n)

section
variable {F : Type} [Field F] [FinEnum F]

@[simp] theorem comps_paleyField (hq : Fintype.card F % 4 = 1) (hq5 : 5 ≤ Fintype.card F) :
    (paleyField F).comps = {paleyField F} :=
  comps_eq_singleton (numComponents_paleyField hq hq5)

end

/-! ### The constructions that really do split -/

/-- **The one-vertex graph is the only atom that repeats.**  `empty n` is `n` copies of it, which
with `sum_comps` says that `empty n` is `n · 1` in the semiring. -/
@[simp] theorem comps_empty (n : ℕ) : (empty n).comps = Multiset.replicate n (empty 1) := by
  induction n with
  | zero => simpa using Multiset.card_eq_zero.1 (by simp)
  | succ k ih =>
      rw [show (empty (k + 1) : IsoGraph) = empty k ⊕g empty 1 from (disjUnion_empty k 1).symm,
        comps_disjUnion, ih, comps_eq_singleton (by simp), Multiset.replicate_succ,
        ← Multiset.singleton_add]
      exact add_comm _ _

theorem comps_circulant_nil (n : ℕ) :
    (circulant n []).comps = Multiset.replicate n (empty 1) := by
  rw [circulant_nil, comps_empty]

/-- Below the threshold a Kneser graph has no edges at all, so every `k`-set is its own
component. -/
theorem comps_kneser_of_lt (n k : ℕ) (h : n < 2 * k) :
    (kneser n k).comps = Multiset.replicate (n.choose k) (empty 1) := by
  rw [kneser_eq_empty n k h, comps_empty]

end IsoGraph
