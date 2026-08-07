import IsoGraph.Identities
import IsoGraph.SRG

/-!
# A gallery of named graphs

The graphs that have proper names but are too big for `IsoGraph/NamedSmallGraphs.lean` and are not
strongly regular, so miss `IsoGraph/SRG.lean` as well: the cubic cages, the generalized Petersen
graphs, two Platonic solids, and a handful of sporadic graphs.  For each one the file records the
order, the number of edges, the degree, connectivity, whether the graph is bipartite, and the
girth.

| graph                 |  n |  E | degree | girth | bipartite |
|-----------------------|----|----|--------|-------|-----------|
| `heawood`             | 14 | 21 |      3 |     6 | yes       |
| `mcgee`               | 24 | 36 |      3 |     7 | no        |
| `tutteCoxeter`        | 30 | 45 |      3 |     8 | yes       |
| `franklin`            | 12 | 18 |      3 |     4 | yes       |
| `pappus`              | 18 | 27 |      3 |     6 | yes       |
| `folkman`             | 20 | 40 |      4 |     4 | yes       |
| `frucht`              | 12 | 18 |      3 |     3 | no        |
| `durer`               | 12 | 18 |      3 |     3 | no        |
| `mobiusKantor`        | 16 | 24 |      3 |     6 | yes       |
| `dodecahedron`        | 20 | 30 |      3 |     5 | no        |
| `desargues`           | 20 | 30 |      3 |     6 | yes       |
| `nauru`               | 24 | 36 |      3 |     6 | yes       |
| `coxeter`             | 28 | 42 |      3 |     7 | no        |
| `wagner`              |  8 | 12 |      3 |     4 | no        |
| `chvatal`             | 12 | 24 |      4 |     4 | no        |
| `icosahedron`         | 12 | 30 |      5 |     3 | no        |
| `tutte`               | 46 | 69 |      3 |     4 | no        |
| `moserSpindle`        |  7 | 11 |    3–4 |     3 | no        |
| `grotzsch`            | 11 | 20 |    3–5 |     4 | no        |

Two remarks on what is and is not here.

* A *`(k, g)`-cage* is a smallest `k`-regular graph of girth `g`.  The cubic cages up to girth
  eight are `complete 4`, `bipartite 3 3`, `SRG.petersen`, `heawood`, `mcgee` and `tutteCoxeter`;
  the first three are already defined elsewhere.  `coxeter` is not a cage — `mcgee` is smaller —
  but it is the other famous cubic graph of girth seven.  Minimality is a statement about *all*
  graphs of a given order and so is out of reach here; what the file proves is that each of these
  graphs is regular of the right degree and of the right girth.
* Of the five Platonic solids, `complete 4` is the tetrahedron, `hypercube 3` the cube,
  `cocktailParty 3` the octahedron, and `dodecahedron` and `icosahedron` are defined here.
  `gp_four_one_iso_hypercube` identifies the cube as a generalized Petersen graph too.

## Proof style

Two certificates replace the `Decidable` instances that would otherwise be needed.

* `isConnected_of_backEdge`: numbering the vertices so that every vertex other than the first has
  a neighbour with a smaller number is enough for connectivity.  This is checked by a single
  `native_decide` over `n²` adjacency queries — Mathlib's `Decidable Connected` instance, by
  contrast, is unusable at this size.
* `walkOn`, feeding `not_isBipartite_of_odd_walk`: an odd closed walk written as a cyclic list of
  vertex numbers.  For the graphs of girth three a triangle is cheaper, and
  `not_isBipartite_of_triangle` is used instead.

Bipartiteness itself is always witnessed by an explicit two-colouring, never searched for: the
parity of the vertex number works for every graph here given by an LCF code, and
`(i + i / n) % 2` for the bipartite generalized Petersen graphs.

One wrinkle in the girth proofs: the distinctness side conditions of `exists_cycle_of_square` and
`exists_cycle_of_pentagon` are stated at the vertex type `G.V`, where `decide` does not always
find the `DecidableEq` instance, so they go through `Fin.ne_of_val_ne` instead.

Above girth five those per-length lemmas run out, and the cages go through the cycle lists of
`IsoGraph/Identities.lean` instead; see "The girth of the cages" at the end of the file.  The one
thing that needs care there is *how* the search for a short cycle is phrased.  Written as a
nested `∀` over vertices, the decision procedure enumerates the whole vertex type at every level
— `30⁷` for `tutteCoxeter`, which never finishes.  Written as `∀ b ∈ nb a`, it walks only along
edges, which is `30 · 3⁶` — but recomputing `nb` from the adjacency function costs a millisecond
a call.  Precomputing the neighbour lists once, in a top-level `def`, is what brings the deepest
search down to about two seconds.
-/

set_option maxRecDepth 4000

namespace NamedGraphs

open CGraph CGraph.Enum

/-! ## Two constructions

Both produce a graph on `Fin n`, numbered so that the back-edge certificate for connectivity
holds on the nose. -/

/-- The edges of the LCF code `[ss]^r`: the Hamiltonian cycle `0 - 1 - ⋯ - (n-1) - 0` on
`n = ss.length * r` vertices, together with the chord from `i` to `i + ss[i mod ss.length]`. -/
def lcfEdges (ss : List ℤ) (r : ℕ) : List (ℕ × ℕ) :=
  (List.range (ss.length * r)).flatMap fun i ↦
    [(i, (i + 1) % (ss.length * r)),
      (i, ((((i : ℤ) + ss.getD (i % ss.length) 0) % (ss.length * r : ℕ)
              + (ss.length * r : ℕ)) % (ss.length * r : ℕ)).toNat)]

/-- The cubic graph with LCF code `[ss]^r`, in Lederberg–Coxeter–Frucht notation: a Hamiltonian
cycle on `ss.length * r` vertices with the chords prescribed by `ss`, repeated `r` times. -/
def lcf (ss : List ℤ) (r : ℕ) : CGraph := ofEdges (ss.length * r) (lcfEdges ss r)

instance (ss : List ℤ) (r : ℕ) : DecidableEq (lcf ss r).V :=
  inferInstanceAs (DecidableEq (Fin (ss.length * r)))

@[simp] theorem card_lcf (ss : List ℤ) (r : ℕ) :
    Fintype.card (lcf ss r).V = ss.length * r := card_ofEdges _ _

/-- The edges of the generalized Petersen graph `GP(n, k)`: an outer `n`-cycle on `0 … n-1`, an
inner circulant `n + i ~ n + (i + k)` on `n … 2n-1`, and the spokes `i ~ n + i`. -/
def gpEdges (n k : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ [(i, (i + 1) % n), (i, n + i), (n + i, n + (i + k) % n)]

/-- The generalized Petersen graph `GP(n, k)`. -/
def gp (n k : ℕ) : CGraph := ofEdges (2 * n) (gpEdges n k)

instance (n k : ℕ) : DecidableEq (gp n k).V := inferInstanceAs (DecidableEq (Fin (2 * n)))

@[simp] theorem card_gp (n k : ℕ) : Fintype.card (gp n k).V = 2 * n := card_ofEdges _ _

/-! ## Two certificates -/

/-- **A back edge from every vertex but the first gives connectivity.**  If the vertices are
numbered by `e` so that each vertex other than number zero has a neighbour with a strictly smaller
number, then the graph is connected: induction on the number walks any vertex down to the first.

The hypothesis is decidable and cheap — `n²` adjacency queries — whereas deciding
`SimpleGraph.Connected` directly is not usable at these sizes. -/
theorem isConnected_of_backEdge {n : ℕ} {G : CGraph} (e : G.V ≃ Fin n) (hn : 0 < n)
    (h : ∀ v : G.V, 0 < (e v).1 → ∃ w : G.V, (e w).1 < (e v).1 ∧ G.Adj v w) : G.IsConnected := by
  have key : ∀ m : ℕ, ∀ x : G.V, (e x).1 = m → G.toSimple.Reachable x (e.symm ⟨0, hn⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hxe : x = e.symm ⟨0, hn⟩ := by
          rw [← e.symm_apply_apply x]; congr 1; exact Fin.ext hx
        exact hxe ▸ SimpleGraph.Reachable.refl _
      · obtain ⟨w, hlt, hadj⟩ := h x (by omega)
        exact (SimpleGraph.Adj.reachable ((toSimple_adj _ _ _).2 hadj)).trans
          (ih (e w).1 (by omega) w rfl)
  have : Nonempty G.V := ⟨e.symm ⟨0, hn⟩⟩
  exact ⟨fun u v ↦ (key _ u rfl).trans (key _ v rfl).symm⟩

/-- **The Mycielskian of a graph without isolated vertices is connected.**  The apex sees every
shadow, and every shadow sees the neighbours of the vertex it shadows. -/
theorem isConnected_mycielskian {G : CGraph} [DecidableEq G.V] (h : ∀ v : G.V, ∃ w, G.Adj v w) :
    (mycielskian G).IsConnected := by
  have hapex : ∀ a : G.V, (mycielskian G).toSimple.Adj none (some (Sum.inr a)) := fun a ↦
    (toSimple_adj (mycielskian G) none (some (Sum.inr a))).2 rfl
  have hnone : ∀ x : (mycielskian G).V, (mycielskian G).toSimple.Reachable none x := by
    rintro (_ | (a | a))
    · exact .refl _
    · obtain ⟨w, hw⟩ := h a
      have hwa : (mycielskian G).toSimple.Adj (some (Sum.inr w)) (some (Sum.inl a)) :=
        (toSimple_adj (mycielskian G) (some (Sum.inr w)) (some (Sum.inl a))).2
          ((G.symm w a).trans hw)
      exact (hapex w).reachable.trans hwa.reachable
    · exact (hapex a).reachable
  have : Nonempty (mycielskian G).V := ⟨none⟩
  exact ⟨fun u v ↦ (hnone u).symm.trans (hnone v)⟩

/-- The closed walk on `Fin N` that runs round the list `vs` of vertex numbers.  Paired with
`not_isBipartite_of_odd_walk`, an odd `vs` witnesses that a graph is not bipartite. -/
def walkOn (N : ℕ) (hN : 0 < N) (vs : List ℕ) (k : ℕ) : Fin N :=
  ⟨vs.getD (k % vs.length) 0 % N, Nat.mod_lt _ hN⟩

/-- Vertex number `i` of a graph on `Fin n`, for naming the corners of a triangle, square or
pentagon.  The bound is discharged by `omega`. -/
abbrev vtx (n : ℕ) [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-! ## The cubic cages

`heawood` is the `(3,6)`-cage — the incidence graph of the Fano plane — `mcgee` the `(3,7)`-cage,
and `tutteCoxeter` the `(3,8)`-cage, also known as the Levi graph of the generalized quadrangle
`GQ(2,2)`.  The `(3,5)`-cage is the Petersen graph, in `IsoGraph/SRG.lean`. -/

/-- The Heawood graph: the point–line incidence graph of the Fano plane, and the `(3,6)`-cage. -/
abbrev heawood : CGraph := lcf [5, -5] 7

/-- The McGee graph, the `(3,7)`-cage. -/
abbrev mcgee : CGraph := lcf [12, 7, -7] 8

/-- The Tutte–Coxeter graph, or Levi graph of `GQ(2,2)`: the `(3,8)`-cage. -/
abbrev tutteCoxeter : CGraph := lcf [-13, -9, 7, -7, 9, 13] 5

@[simp] theorem card_heawood : Fintype.card heawood.V = 14 := card_ofEdges _ _

@[simp] theorem E_heawood : heawood.E = 21 := by native_decide

theorem isRegularWith_heawood : heawood.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 14) (by native_decide)

@[simp] theorem isConnected_heawood : heawood.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 14)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_heawood : heawood.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem card_mcgee : Fintype.card mcgee.V = 24 := card_ofEdges _ _

@[simp] theorem E_mcgee : mcgee.E = 36 := by native_decide

theorem isRegularWith_mcgee : mcgee.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_mcgee : mcgee.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

/-- The McGee graph has odd girth: `0 - 12 - 11 - 4 - 3 - 2 - 1 - 0` is a seven-cycle. -/
@[simp] theorem not_isBipartite_mcgee : ¬ mcgee.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 24 (by norm_num) [0, 12, 11, 4, 3, 2, 1]) 7 rfl
    (by decide) rfl

@[simp] theorem card_tutteCoxeter : Fintype.card tutteCoxeter.V = 30 := card_ofEdges _ _

@[simp] theorem E_tutteCoxeter : tutteCoxeter.E = 45 := by native_decide

theorem isRegularWith_tutteCoxeter : tutteCoxeter.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 30) (by native_decide)

@[simp] theorem isConnected_tutteCoxeter : tutteCoxeter.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 30)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_tutteCoxeter : tutteCoxeter.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

/-! ## More graphs from LCF codes -/

/-- The Franklin graph: the `Möbius–Kantor`-like cubic graph on twelve vertices, an embedding of
the Klein bottle with six hexagonal faces. -/
abbrev franklin : CGraph := lcf [5, -5] 6

/-- The Pappus graph: the incidence graph of the Pappus configuration `9₃`. -/
abbrev pappus : CGraph := lcf [5, 7, -7, 7, -7, -5] 3

/-- The Folkman graph: the smallest semi-symmetric graph, that is, the smallest graph which is
edge-transitive and regular but not vertex-transitive. -/
abbrev folkman : CGraph := lcf [5, -7, -7, 5] 5

/-- The Frucht graph: a cubic graph whose only automorphism is the identity. -/
abbrev frucht : CGraph := lcf [-5, -2, -4, 2, 5, -2, 2, 5, -2, -5, 4, 2] 1

@[simp] theorem card_franklin : Fintype.card franklin.V = 12 := card_ofEdges _ _

@[simp] theorem E_franklin : franklin.E = 18 := by native_decide

theorem isRegularWith_franklin : franklin.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_franklin : franklin.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_franklin : franklin.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem girth_franklin : franklin.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := franklin) (a := vtx 12 0)
    (b := vtx 12 5) (c := vtx 12 6) (d := vtx 12 11) (by decide) (by decide) (by decide)
    (by decide) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_pappus : Fintype.card pappus.V = 18 := card_ofEdges _ _

@[simp] theorem E_pappus : pappus.E = 27 := by native_decide

theorem isRegularWith_pappus : pappus.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 18) (by native_decide)

@[simp] theorem isConnected_pappus : pappus.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 18)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_pappus : pappus.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem card_folkman : Fintype.card folkman.V = 20 := card_ofEdges _ _

@[simp] theorem E_folkman : folkman.E = 40 := by native_decide

theorem isRegularWith_folkman : folkman.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_folkman : folkman.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_folkman : folkman.IsBipartite :=
  ⟨fun v ↦ decide (v.1 % 2 = 1), by native_decide⟩

@[simp] theorem girth_folkman : folkman.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := folkman) (a := vtx 20 0)
    (b := vtx 20 5) (c := vtx 20 4) (d := vtx 20 19) (by decide) (by decide) (by decide)
    (by decide) (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_frucht : Fintype.card frucht.V = 12 := card_ofEdges _ _

@[simp] theorem E_frucht : frucht.E = 18 := by native_decide

theorem isRegularWith_frucht : frucht.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_frucht : frucht.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_frucht : ¬ frucht.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 1) (d := vtx 12 11)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_frucht : frucht.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 1) (c := vtx 12 11)
    (by decide) (by decide) (by decide)

/-! ## Generalized Petersen graphs

`GP(n, k)` is the outer `n`-cycle, the inner circulant of step `k`, and the spokes between them.
The Petersen graph itself is `GP(5, 2)`, the `n`-prism is `GP(n, 1)`. -/

/-- The Dürer graph `GP(6, 2)`, from Dürer's *Melencolia I*. -/
abbrev durer : CGraph := gp 6 2

/-- The Möbius–Kantor graph `GP(8, 3)`, the generalized Petersen graph on sixteen vertices. -/
abbrev mobiusKantor : CGraph := gp 8 3

/-- The dodecahedron `GP(10, 2)`, the skeleton of the Platonic solid. -/
abbrev dodecahedron : CGraph := gp 10 2

/-- The Desargues graph `GP(10, 3)`: the bipartite double cover of the Petersen graph, and the
incidence graph of the Desargues configuration `10₃`. -/
abbrev desargues : CGraph := gp 10 3

/-- The Nauru graph `GP(12, 5)`, the Levi graph of the Möbius–Kantor configuration `12₃`. -/
abbrev nauru : CGraph := gp 12 5

theorem gp_five_two_iso_petersen : Nonempty (gp 5 2 ≃cg SRG.petersen) := by
  rw [← key_eq_iff]; native_decide

theorem gp_six_one_iso_prism : Nonempty (gp 6 1 ≃cg prism 6) := by
  rw [← key_eq_iff]; native_decide

theorem gp_four_one_iso_hypercube : Nonempty (gp 4 1 ≃cg hypercube 3) := by
  rw [← key_eq_iff]; native_decide

@[simp] theorem card_durer : Fintype.card durer.V = 12 := card_ofEdges _ _

@[simp] theorem E_durer : durer.E = 18 := by native_decide

theorem isRegularWith_durer : durer.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_durer : durer.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_durer : ¬ durer.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 6) (b := vtx 12 8) (d := vtx 12 10)
    (by decide) (by decide) (by decide)

/-- The inner triangle `6 - 8 - 10` of the Dürer graph. -/
@[simp] theorem girth_durer : durer.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 6) (b := vtx 12 8) (c := vtx 12 10)
    (by decide) (by decide) (by decide)

@[simp] theorem card_mobiusKantor : Fintype.card mobiusKantor.V = 16 := card_ofEdges _ _

@[simp] theorem E_mobiusKantor : mobiusKantor.E = 24 := by native_decide

theorem isRegularWith_mobiusKantor : mobiusKantor.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 16) (by native_decide)

@[simp] theorem isConnected_mobiusKantor : mobiusKantor.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 16)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_mobiusKantor : mobiusKantor.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 8) % 2 = 1), by native_decide⟩

@[simp] theorem card_dodecahedron : Fintype.card dodecahedron.V = 20 := card_ofEdges _ _

@[simp] theorem E_dodecahedron : dodecahedron.E = 30 := by native_decide

theorem isRegularWith_dodecahedron : dodecahedron.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_dodecahedron : dodecahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_dodecahedron : ¬ dodecahedron.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 20 (by norm_num) [0, 10, 18, 8, 9]) 5 rfl (by decide) rfl

/-- The dodecahedron has girth five: its faces are pentagons. -/
@[simp] theorem girth_dodecahedron : dodecahedron.girth = 5 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_pentagon (G := dodecahedron) (a := vtx 20 0)
    (b := vtx 20 10) (c := vtx 20 18) (d := vtx 20 8) (e := vtx 20 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (five_le_girth (by native_decide) (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_desargues : Fintype.card desargues.V = 20 := card_ofEdges _ _

@[simp] theorem E_desargues : desargues.E = 30 := by native_decide

theorem isRegularWith_desargues : desargues.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 20) (by native_decide)

@[simp] theorem isConnected_desargues : desargues.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 20)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_desargues : desargues.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 10) % 2 = 1), by native_decide⟩

@[simp] theorem card_nauru : Fintype.card nauru.V = 24 := card_ofEdges _ _

@[simp] theorem E_nauru : nauru.E = 36 := by native_decide

theorem isRegularWith_nauru : nauru.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 24) (by native_decide)

@[simp] theorem isConnected_nauru : nauru.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 24)) (by norm_num) (by native_decide)

@[simp] theorem isBipartite_nauru : nauru.IsBipartite :=
  ⟨fun v ↦ decide ((v.1 + v.1 / 12) % 2 = 1), by native_decide⟩

/-! ## Sporadic graphs -/

/-- The edges of the Coxeter graph: a seven-cycle `0 … 6` of step one, a hub `7 … 13` joined to
it, and two more heptagons `14 … 20` and `21 … 27` of steps two and three, each joined to the hub
in the same way.  Numbered so that the back-edge certificate holds. -/
def coxeterEdges : List (ℕ × ℕ) :=
  (List.range 7).flatMap fun i ↦
    [(i, (i + 1) % 7), (i, 7 + i), (7 + i, 14 + i), (7 + i, 21 + i),
      (14 + i, 14 + (i + 2) % 7), (21 + i, 21 + (i + 3) % 7)]

/-- The Coxeter graph: a cubic distance-regular graph of girth seven on 28 vertices, one of the
thirteen known cubic symmetric graphs that are not Hamiltonian. -/
abbrev coxeter : CGraph := ofEdges 28 coxeterEdges

/-- The Wagner graph, or Möbius–Kantor ladder `V₈`: the circulant on eight vertices joining each
vertex to its neighbours and its antipode. -/
abbrev wagner : CGraph := circulant 8 [1, 4]

/-- The edges of the Chvátal graph. -/
def chvatalEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 4), (0, 6), (0, 9), (1, 2), (1, 5), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4),
    (3, 7), (3, 9), (4, 5), (4, 8), (5, 10), (5, 11), (6, 10), (6, 11), (7, 8), (7, 11),
    (8, 10), (9, 10), (9, 11)]

/-- The Chvátal graph: the smallest triangle-free four-regular graph with chromatic number four. -/
abbrev chvatal : CGraph := ofEdges 12 chvatalEdges

/-- The edges of the icosahedron. -/
def icosahedronEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 5), (0, 7), (0, 8), (0, 11), (1, 2), (1, 5), (1, 6), (1, 8), (2, 3), (2, 6),
    (2, 8), (2, 9), (3, 4), (3, 6), (3, 9), (3, 10), (4, 5), (4, 6), (4, 10), (4, 11), (5, 6),
    (5, 11), (7, 8), (7, 9), (7, 10), (7, 11), (8, 9), (9, 10), (10, 11)]

/-- The icosahedron, the skeleton of the Platonic solid: five-regular on twelve vertices. -/
abbrev icosahedron : CGraph := ofEdges 12 icosahedronEdges

/-- The edges of the Tutte graph. -/
def tutteEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 26), (2, 10), (2, 11), (3, 18), (3, 19), (4, 5), (4, 33),
    (5, 6), (5, 29), (6, 7), (6, 27), (7, 8), (7, 14), (8, 9), (8, 38), (9, 10), (9, 37),
    (10, 39), (11, 12), (11, 39), (12, 13), (12, 35), (13, 14), (13, 15), (14, 34), (15, 16),
    (15, 22), (16, 17), (16, 44), (17, 18), (17, 43), (18, 45), (19, 20), (19, 45), (20, 21),
    (20, 41), (21, 22), (21, 23), (22, 40), (23, 24), (23, 27), (24, 25), (24, 32), (25, 26),
    (25, 31), (26, 33), (27, 28), (28, 29), (28, 32), (29, 30), (30, 31), (30, 33), (31, 32),
    (34, 35), (34, 38), (35, 36), (36, 37), (36, 39), (37, 38), (40, 41), (40, 44), (41, 42),
    (42, 43), (42, 45), (43, 44)]

/-- The Tutte graph: a cubic planar three-connected graph with no Hamiltonian cycle, Tutte's 1946
counterexample to Tait's conjecture. -/
abbrev tutte : CGraph := ofEdges 46 tutteEdges

/-- The edges of the Moser spindle: two rhombi `0-1-3-2` and `0-4-6-5` sharing the vertex `0`,
with the far vertices `3` and `6` joined. -/
def moserSpindleEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (0, 4), (0, 5), (4, 5), (4, 6), (5, 6), (3, 6)]

/-- The Moser spindle: a unit-distance graph in the plane with chromatic number four, the classic
lower bound for the Hadwiger–Nelson problem. -/
abbrev moserSpindle : CGraph := ofEdges 7 moserSpindleEdges

/-- The Grötzsch graph, the Mycielskian of the pentagon: triangle-free with chromatic number
four, and the smallest such graph. -/
abbrev grotzsch : CGraph := mycielskian (cycle 5)

@[simp] theorem card_coxeter : Fintype.card coxeter.V = 28 := card_ofEdges _ _

@[simp] theorem E_coxeter : coxeter.E = 42 := by native_decide

theorem isRegularWith_coxeter : coxeter.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 28) (by native_decide)

@[simp] theorem isConnected_coxeter : coxeter.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 28)) (by norm_num) (by native_decide)

/-- The first heptagon of the Coxeter graph is an odd cycle. -/
@[simp] theorem not_isBipartite_coxeter : ¬ coxeter.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 28 (by norm_num) [0, 1, 2, 3, 4, 5, 6]) 7 rfl
    (by decide) rfl

@[simp] theorem card_wagner : Fintype.card wagner.V = 8 := card_circulant _ _

@[simp] theorem E_wagner : wagner.E = 12 := by native_decide

theorem isRegularWith_wagner : wagner.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 8) (by native_decide)

@[simp] theorem isConnected_wagner : wagner.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 8)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_wagner : ¬ wagner.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 8 (by norm_num) [0, 1, 2, 3, 7]) 5 rfl (by decide) rfl

@[simp] theorem girth_wagner : wagner.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := wagner) (a := vtx 8 0) (b := vtx 8 1)
    (c := vtx 8 5) (d := vtx 8 4) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_chvatal : Fintype.card chvatal.V = 12 := card_ofEdges _ _

@[simp] theorem E_chvatal : chvatal.E = 24 := by native_decide

theorem isRegularWith_chvatal : chvatal.IsRegularWith 4 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_chvatal : chvatal.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_chvatal : ¬ chvatal.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 12 (by norm_num) [0, 1, 2, 3, 4]) 5 rfl (by decide) rfl

/-- The Chvátal graph is triangle-free, and `0 - 1 - 2 - 6 - 0` is a square. -/
@[simp] theorem girth_chvatal : chvatal.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := chvatal) (a := vtx 12 0) (b := vtx 12 1)
    (c := vtx 12 2) (d := vtx 12 6) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_icosahedron : Fintype.card icosahedron.V = 12 := card_ofEdges _ _

@[simp] theorem E_icosahedron : icosahedron.E = 30 := by native_decide

theorem isRegularWith_icosahedron : icosahedron.IsRegularWith 5 :=
  isRegularWith_of_degSequence (n := 12) (by native_decide)

@[simp] theorem isConnected_icosahedron : icosahedron.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 12)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_icosahedron : ¬ icosahedron.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 12 0) (b := vtx 12 1) (d := vtx 12 5)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_icosahedron : icosahedron.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 12 0) (b := vtx 12 1) (c := vtx 12 5)
    (by decide) (by decide) (by decide)

@[simp] theorem card_tutte : Fintype.card tutte.V = 46 := card_ofEdges _ _

@[simp] theorem E_tutte : tutte.E = 69 := by native_decide

theorem isRegularWith_tutte : tutte.IsRegularWith 3 :=
  isRegularWith_of_degSequence (n := 46) (by native_decide)

@[simp] theorem isConnected_tutte : tutte.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 46)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_tutte : ¬ tutte.IsBipartite :=
  not_isBipartite_of_odd_walk (walkOn 46 (by norm_num) [4, 5, 29, 30, 33]) 5 rfl (by decide) rfl

@[simp] theorem girth_tutte : tutte.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := tutte) (a := vtx 46 1) (b := vtx 46 4)
    (c := vtx 46 33) (d := vtx 46 26) (by decide) (by decide) (by decide) (by decide)
    (Fin.ne_of_val_ne (by decide)) (Fin.ne_of_val_ne (by decide))
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

@[simp] theorem card_moserSpindle : Fintype.card moserSpindle.V = 7 := card_ofEdges _ _

@[simp] theorem E_moserSpindle : moserSpindle.E = 11 := by native_decide

@[simp] theorem degSequence_moserSpindle :
    moserSpindle.degSequence = [3, 3, 3, 3, 3, 3, 4] := by native_decide

@[simp] theorem isConnected_moserSpindle : moserSpindle.IsConnected :=
  isConnected_of_backEdge (Equiv.refl (Fin 7)) (by norm_num) (by native_decide)

@[simp] theorem not_isBipartite_moserSpindle : ¬ moserSpindle.IsBipartite :=
  not_isBipartite_of_triangle (a := vtx 7 0) (b := vtx 7 1) (d := vtx 7 2)
    (by decide) (by decide) (by decide)

@[simp] theorem girth_moserSpindle : moserSpindle.girth = 3 :=
  girth_eq_three_of_triangle (a := vtx 7 0) (b := vtx 7 1) (c := vtx 7 2)
    (by decide) (by decide) (by decide)

@[simp] theorem card_grotzsch : Fintype.card grotzsch.V = 11 := by native_decide

@[simp] theorem E_grotzsch : grotzsch.E = 20 := by native_decide

/-- The Grötzsch graph is not regular: the pentagon has degree four, its shadows degree three,
and the apex degree five. -/
@[simp] theorem degSequence_grotzsch :
    grotzsch.degSequence = [3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5] := by native_decide

@[simp] theorem isConnected_grotzsch : grotzsch.IsConnected :=
  isConnected_mycielskian (by decide)

@[simp] theorem not_isBipartite_grotzsch : ¬ grotzsch.IsBipartite :=
  not_isBipartite_mycielskian (a := vtx 5 0) (b := vtx 5 1) (by decide)

/-- The Grötzsch graph is triangle-free — that is the point of the Mycielskian — and
`apex - 0' - 1 - 2' - apex` is a square. -/
@[simp] theorem girth_grotzsch : grotzsch.girth = 4 := by
  obtain ⟨_, w, hw, hl⟩ := exists_cycle_of_square (G := grotzsch) (a := none)
    (b := some (Sum.inr (vtx 5 0))) (c := some (Sum.inl (vtx 5 1)))
    (d := some (Sum.inr (vtx 5 2)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact le_antisymm (hl ▸ girth_le_length hw)
    (four_le_girth (by native_decide) (not_isAcyclic_of_isCycle hw))

/-! ## Coincidences

Several of the graphs above have a second standard description; the canonical keys of
`IsoGraph/Enum` decide the isomorphisms. -/

theorem mobiusKantor_lcf : Nonempty (lcf [5, -5] 8 ≃cg mobiusKantor) := by
  rw [← key_eq_iff]; native_decide

theorem desargues_lcf : Nonempty (lcf [5, -5, 9, -9] 5 ≃cg desargues) := by
  rw [← key_eq_iff]; native_decide

theorem dodecahedron_lcf :
    Nonempty (lcf [10, 7, 4, -4, -7, 10, -4, 7, -7, 4] 2 ≃cg dodecahedron) := by
  rw [← key_eq_iff]; native_decide

theorem nauru_lcf : Nonempty (lcf [5, -9, 7, -7, 9, -5] 4 ≃cg nauru) := by
  rw [← key_eq_iff]; native_decide

/-! ## The girth of the cages

Every graph above of girth at most five got it from the hand-written ladder of
`IsoGraph/Identities.lean`.  The cages of girth six, seven and eight go through the cycle-list
machinery instead: `girth_le_of_cycleList` turns an explicit list of vertices into an upper
bound, and `six_le_girth_of_nbrList`, `seven_le_girth_of_nbrList` and
`eight_le_girth_of_nbrList` turn an exhaustive search along a neighbour table into a lower
bound. -/

/-- The neighbour table of the heawood graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def heawoodTbl : List (List heawood.V) := heawood.nbrTable (List.finRange 14)

/-- The neighbours of `a` in the heawood graph. -/
def heawoodNb (a : heawood.V) : List heawood.V := heawoodTbl.getD a.1 []

theorem heawood_nb : ∀ a b : heawood.V, b ∈ heawoodNb a ↔ heawood.Adj a b := by
  native_decide

/-- The Heawood graph, the `(3, 6)`-cage, has girth six: `0 - 1 - 2 - 3 - 4 - 5 - 0` is a
six-cycle, and a search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_heawood : heawood.girth = 6 := by
  have hcyc : heawood.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 14 0) [vtx 14 1, vtx 14 2, vtx 14 3, vtx 14 4, vtx 14 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ heawood.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 14 0) [vtx 14 1, vtx 14 2, vtx 14 3, vtx 14 4, vtx 14 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList heawood_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the pappus graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def pappusTbl : List (List pappus.V) := pappus.nbrTable (List.finRange 18)

/-- The neighbours of `a` in the pappus graph. -/
def pappusNb (a : pappus.V) : List pappus.V := pappusTbl.getD a.1 []

theorem pappus_nb : ∀ a b : pappus.V, b ∈ pappusNb a ↔ pappus.Adj a b := by
  native_decide

/-- The Pappus graph has girth six: `0 - 1 - 2 - 3 - 4 - 5 - 0` is a six-cycle, and a search along
the
neighbour table finds no shorter one. -/
@[simp] theorem girth_pappus : pappus.girth = 6 := by
  have hcyc : pappus.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 18 0) [vtx 18 1, vtx 18 2, vtx 18 3, vtx 18 4, vtx 18 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ pappus.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 18 0) [vtx 18 1, vtx 18 2, vtx 18 3, vtx 18 4, vtx 18 5]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList pappus_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the mobiusKantor graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def mobiusKantorTbl : List (List mobiusKantor.V) := mobiusKantor.nbrTable (List.finRange 16)

/-- The neighbours of `a` in the mobiusKantor graph. -/
def mobiusKantorNb (a : mobiusKantor.V) : List mobiusKantor.V := mobiusKantorTbl.getD a.1 []

theorem mobiusKantor_nb : ∀ a b : mobiusKantor.V, b ∈ mobiusKantorNb a ↔ mobiusKantor.Adj a b := by
  native_decide

/-- The Möbius–Kantor graph has girth six: `0 - 1 - 2 - 3 - 11 - 8 - 0` is a six-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_mobiusKantor : mobiusKantor.girth = 6 := by
  have hcyc : mobiusKantor.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 16 0) [vtx 16 1, vtx 16 2, vtx 16 3, vtx 16 11, vtx 16 8]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ mobiusKantor.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 16 0) [vtx 16 1, vtx 16 2, vtx 16 3, vtx 16 11, vtx 16 8]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList mobiusKantor_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the desargues graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def desarguesTbl : List (List desargues.V) := desargues.nbrTable (List.finRange 20)

/-- The neighbours of `a` in the desargues graph. -/
def desarguesNb (a : desargues.V) : List desargues.V := desarguesTbl.getD a.1 []

theorem desargues_nb : ∀ a b : desargues.V, b ∈ desarguesNb a ↔ desargues.Adj a b := by
  native_decide

/-- The Desargues graph has girth six: `0 - 1 - 2 - 3 - 13 - 10 - 0` is a six-cycle, and a search
along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_desargues : desargues.girth = 6 := by
  have hcyc : desargues.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 13, vtx 20 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ desargues.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 20 0) [vtx 20 1, vtx 20 2, vtx 20 3, vtx 20 13, vtx 20 10]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList desargues_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the nauru graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def nauruTbl : List (List nauru.V) := nauru.nbrTable (List.finRange 24)

/-- The neighbours of `a` in the nauru graph. -/
def nauruNb (a : nauru.V) : List nauru.V := nauruTbl.getD a.1 []

theorem nauru_nb : ∀ a b : nauru.V, b ∈ nauruNb a ↔ nauru.Adj a b := by
  native_decide

/-- The Nauru graph has girth six: `0 - 1 - 2 - 14 - 19 - 12 - 0` is a six-cycle, and a search
along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_nauru : nauru.girth = 6 := by
  have hcyc : nauru.girth ≤ 6 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 14, vtx 24 19, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ nauru.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 14, vtx 24 19, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (six_le_girth_of_nbrList nauru_nb
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the mcgee graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def mcgeeTbl : List (List mcgee.V) := mcgee.nbrTable (List.finRange 24)

/-- The neighbours of `a` in the mcgee graph. -/
def mcgeeNb (a : mcgee.V) : List mcgee.V := mcgeeTbl.getD a.1 []

theorem mcgee_nb : ∀ a b : mcgee.V, b ∈ mcgeeNb a ↔ mcgee.Adj a b := by
  native_decide

/-- The McGee graph has girth seven: `0 - 1 - 2 - 3 - 4 - 11 - 12 - 0` is a seven-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_mcgee : mcgee.girth = 7 := by
  have hcyc : mcgee.girth ≤ 7 :=
    girth_le_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 3, vtx 24 4, vtx 24 11, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ mcgee.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 24 0) [vtx 24 1, vtx 24 2, vtx 24 3, vtx 24 4, vtx 24 11, vtx 24 12]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (seven_le_girth_of_nbrList mcgee_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the coxeter graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def coxeterTbl : List (List coxeter.V) := coxeter.nbrTable (List.finRange 28)

/-- The neighbours of `a` in the coxeter graph. -/
def coxeterNb (a : coxeter.V) : List coxeter.V := coxeterTbl.getD a.1 []

theorem coxeter_nb : ∀ a b : coxeter.V, b ∈ coxeterNb a ↔ coxeter.Adj a b := by
  native_decide

/-- The Coxeter graph has girth seven: `0 - 1 - 2 - 3 - 4 - 5 - 6 - 0` is a seven-cycle, and a
search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_coxeter : coxeter.girth = 7 := by
  have hcyc : coxeter.girth ≤ 7 :=
    girth_le_of_cycleList
      (vtx 28 0) [vtx 28 1, vtx 28 2, vtx 28 3, vtx 28 4, vtx 28 5, vtx 28 6]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ coxeter.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 28 0) [vtx 28 1, vtx 28 2, vtx 28 3, vtx 28 4, vtx 28 5, vtx 28 6]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (seven_le_girth_of_nbrList coxeter_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

/-- The neighbour table of the tutteCoxeter graph.  Looking a neighbour up in a table is what makes
the girth search below tractable: the decision procedure would otherwise recompute the
neighbours of every vertex at every level of the search. -/
def tutteCoxeterTbl : List (List tutteCoxeter.V) := tutteCoxeter.nbrTable (List.finRange 30)

/-- The neighbours of `a` in the tutteCoxeter graph. -/
def tutteCoxeterNb (a : tutteCoxeter.V) : List tutteCoxeter.V := tutteCoxeterTbl.getD a.1 []

theorem tutteCoxeter_nb : ∀ a b : tutteCoxeter.V, b ∈ tutteCoxeterNb a ↔ tutteCoxeter.Adj a b := by
  native_decide

/-- The Tutte–Coxeter graph, the `(3, 8)`-cage, has girth eight: `0 - 1 - 2 - 3 - 4 - 5 - 18 - 17 -
0` is an eight-cycle, and a search along the
neighbour table finds no shorter one. -/
@[simp] theorem girth_tutteCoxeter : tutteCoxeter.girth = 8 := by
  have hcyc : tutteCoxeter.girth ≤ 8 :=
    girth_le_of_cycleList
      (vtx 30 0) [vtx 30 1, vtx 30 2, vtx 30 3, vtx 30 4, vtx 30 5, vtx 30 18, vtx 30 17]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  have hnac : ¬ tutteCoxeter.IsAcyclic :=
    not_isAcyclic_of_cycleList
      (vtx 30 0) [vtx 30 1, vtx 30 2, vtx 30 3, vtx 30 4, vtx 30 5, vtx 30 18, vtx 30 17]
      (by norm_num) (by native_decide) (by native_decide) (by native_decide)
  exact le_antisymm hcyc (eight_le_girth_of_nbrList tutteCoxeter_nb
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide) hnac)

end NamedGraphs
