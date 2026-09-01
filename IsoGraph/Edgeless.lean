import IsoGraph.Algebra.Components
import IsoGraph.Spectrum
import IsoGraph.SmallGraphs

/-!
# Constructions on edgeless input

A graph with no edges is the edgeless graph on its own vertices — that is `eq_empty_of_E_eq_zero`,
and this file spends it.  Several constructions collapse completely once one of their arguments has
no edges, and where they do, every invariant of the result is known.  Those are exactly the cells
the rest of the library cannot reach, because the constructions in question have no unconditional
formulas to state.

The two exponentials are the extreme case: neither has invariant formulas at all.  `G ^g H` exists
to turn questions about `Hom(K ⊗g H, G)` into questions about `Hom(K, G ^g H)`, which is why it
turns up in Hedetniemi-style arguments about the chromatic number of a tensor product — and those
are open questions, not rewrites.  `G ^hg H` is worse off still: its vertex count is `|Hom(H, G)|`,
which is not a function of the usual invariants of `G` and `H` at all.  But an edgeless exponent
makes the adjacency condition on `G ^g H` vacuous, so every two distinct functions are joined and
the exponential is a complete graph on `|G| ^ |H|` vertices; and an edgeless base over a connected
exponent leaves only the constant homomorphisms, no two of them joined, so `G ^hg H` is edgeless on
`|G|` vertices.  Both are read off below, invariant by invariant.

The four products get the same treatment further down, but only along the rows still open: the
rest of those columns have honest formulas already.  The complement, the line graph and the join
close the file off in the same way — and for the join, where an edgeless argument does *not*
settle everything, both extremes are recorded and the gap between them left visible.
-/

set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace IsoGraph

/-! ### The collapse of the exponentials

Three identifications, each generalising an existing one from a literal `empty n` to any graph
without edges. -/

/-- A graph with no edges is the edgeless graph on its own vertices. -/
theorem eq_empty_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) : G = empty G.V := by
  induction G using Quotient.inductionOn with | _ G =>
  rw [E_mk] at h
  rw [V_mk]
  exact mk_eq_empty (CGraph.adj_eq_false_of_E_eq_zero h)

/-- **An edgeless exponent makes the exponential complete.**  The adjacency condition on `G ^g H`
quantifies over the edges of `H`, so with none it is vacuous and only `f ≠ f'` survives. -/
theorem exponential_eq_complete {G H : IsoGraph} (h : H.E = 0) :
    G ^g H = complete (G.V ^ H.V) := by
  conv_lhs => rw [eq_empty_of_E_eq_zero h]
  rw [exponential_empty]

/-- An edgeless base makes the exponential edgeless too, as soon as the exponent has an edge to
witness. -/
theorem exponential_eq_empty {G H : IsoGraph} (hG : G.E = 0) (hH : 0 < H.E) :
    G ^g H = empty (G.V ^ H.V) := by
  conv_lhs => rw [eq_empty_of_E_eq_zero hG]
  exact empty_exponential G.V (fun hc ↦ by rw [hc, E_empty] at hH; omega)

/-- **An edgeless base makes the hom exponential edgeless.**  A homomorphism into an edgeless graph
is constant on each component, so over a connected exponent there are exactly `|G|` of them, and no
two are joined. -/
theorem homExponential_eq_empty {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    G ^hg H = empty G.V := by
  conv_lhs => rw [eq_empty_of_E_eq_zero hG]
  exact empty_homExponential_of_isConnected G.V hH

/-! ### The exponential over an edgeless exponent

`V_exponential` already gives the vertex count; what follows is the rest of the complete graph on
`|G| ^ |H|` vertices, read off through `exponential_eq_complete`.  The invariants that only make
sense above a certain size take the size as a hypothesis on `|G| ^ |H|` rather than on `|G|` and
`|H|` separately, which is both shorter and more general. -/

theorem E_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).E = (G.V ^ H.V).choose 2 := by
  rw [exponential_eq_complete h, E_complete]

theorem isArcTransitive_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).IsArcTransitive := by
  rw [exponential_eq_complete h]
  exact isArcTransitive_complete _

theorem isVertexTransitive_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).IsVertexTransitive := by
  rw [exponential_eq_complete h]
  exact isVertexTransitive_complete _

theorem isDS_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) : IsDS (G ^g H) := by
  rw [exponential_eq_complete h]
  exact isDS_complete _

theorem isRegularWith_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).IsRegularWith (G.V ^ H.V - 1) := by
  rw [exponential_eq_complete h]
  exact isRegularWith_complete _

theorem isSRGWith_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).IsSRGWith (G.V ^ H.V) (G.V ^ H.V - 1) (G.V ^ H.V - 2) (G.V ^ H.V - 1) := by
  rw [exponential_eq_complete h]
  exact isSRGWith_complete _

theorem chromNum_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).chromNum = G.V ^ H.V := by
  rw [exponential_eq_complete h, chromNum_complete]

theorem cliqueNum_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).cliqueNum = G.V ^ H.V := by
  rw [exponential_eq_complete h, cliqueNum_complete]

theorem cliqueCount_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) (k : ℕ) :
    (G ^g H).cliqueCount k = (G.V ^ H.V).choose k := by
  rw [exponential_eq_complete h, cliqueCount_complete]

theorem coverNum_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).coverNum = G.V ^ H.V - 1 := by
  rw [exponential_eq_complete h, coverNum_complete]

theorem degMultiset_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    degMultiset (G ^g H) = Multiset.replicate (G.V ^ H.V) (G.V ^ H.V - 1) := by
  rw [exponential_eq_complete h, degMultiset_complete]

theorem degSequence_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    degSequence (G ^g H) = List.replicate (G.V ^ H.V) (G.V ^ H.V - 1) := by
  rw [exponential_eq_complete h, degSequence_complete]

theorem edgeConn_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).edgeConn = G.V ^ H.V - 1 := by
  rw [exponential_eq_complete h, edgeConn_complete]

theorem vertexConn_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).vertexConn = G.V ^ H.V - 1 := by
  rw [exponential_eq_complete h, vertexConn_complete]

theorem indepNum_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).indepNum = min (G.V ^ H.V) 1 := by
  rw [exponential_eq_complete h, indepNum_complete]

theorem indepCount_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) (k : ℕ) :
    (G ^g H).indepCount (k + 2) = 0 := by
  rw [exponential_eq_complete h, indepCount_complete]

theorem matchNum_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).matchNum = G.V ^ H.V / 2 := by
  rw [exponential_eq_complete h, matchNum_complete]

theorem maxDeg_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    maxDeg (G ^g H) = G.V ^ H.V - 1 := by
  rw [exponential_eq_complete h, maxDeg_complete]

theorem minDeg_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    minDeg (G ^g H) = G.V ^ H.V - 1 := by
  rw [exponential_eq_complete h, minDeg_complete]

theorem autCount_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0) :
    (G ^g H).autCount = Nat.factorial (G.V ^ H.V) := by
  rw [exponential_eq_complete h, autCount_complete]

/-! With one vertex to spare the exponential is connected, and its spectrum appears. -/

theorem isConnected_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).IsConnected := by
  rw [exponential_eq_complete h, hm]
  exact isConnected_complete m

theorem numComponents_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).numComponents = 1 := by
  rw [exponential_eq_complete h, hm, numComponents_complete]

theorem comps_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).comps = {complete (m + 1)} := by
  rw [exponential_eq_complete h, hm, comps_complete]

theorem domNum_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).domNum = 1 := by
  rw [exponential_eq_complete h, hm, domNum_complete]

theorem cliqueCoverNum_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).cliqueCoverNum = 1 := by
  rw [exponential_eq_complete h, hm, cliqueCoverNum_complete]

theorem energy_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).energy = 2 * m := by
  rw [exponential_eq_complete h, hm, energy_complete]

theorem spectrum_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).spectrum = (m : ℝ) ::ₘ Multiset.replicate m (-1) := by
  rw [exponential_eq_complete h, hm, spectrum_complete]

theorem charpoly_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).charpoly = (X - C (m : ℝ)) * (X + 1) ^ m := by
  rw [exponential_eq_complete h, hm, charpoly_complete]

theorem lapSpectrum_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) :
    (G ^g H).lapSpectrum = (0 : ℝ) ::ₘ Multiset.replicate m ((m : ℝ) + 1) := by
  rw [exponential_eq_complete h, hm, lapSpectrum_complete]

theorem lapCharpoly_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 1) : (G ^g H).lapCharpoly = X * (X - C ((m : ℝ) + 1)) ^ m := by
  rw [exponential_eq_complete h, hm, lapCharpoly_complete]

/-! With two, the distances and the edge colourings. -/

theorem diameter_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) : (G ^g H).diameter = 1 := by
  rw [exponential_eq_complete h, hm, diameter_complete]

theorem radius_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) : (G ^g H).radius = 1 := by
  rw [exponential_eq_complete h, hm, radius_complete]

theorem algConn_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) : (G ^g H).algConn = (m : ℝ) + 2 := by
  rw [exponential_eq_complete h, hm, algConn_complete]

theorem lapLambdaMax_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) : (G ^g H).lapLambdaMax = (m : ℝ) + 2 := by
  rw [exponential_eq_complete h, hm, lapLambdaMax_complete]

theorem edgeChromNum_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) :
    (G ^g H).edgeChromNum = if m % 2 = 0 then m + 1 else m + 2 := by
  rw [exponential_eq_complete h, hm, edgeChromNum_complete]

theorem not_isSelfComplementary_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 2) : ¬ IsSelfComplementary (G ^g H) := by
  rw [exponential_eq_complete h, hm]
  exact not_isSelfComplementary_complete m

/-! With three, the triangles. -/

theorem girth_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 3) : (G ^g H).girth = 3 := by
  rw [exponential_eq_complete h, hm, girth_complete]

theorem not_isAcyclic_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 3) : ¬ IsAcyclic (G ^g H) := by
  rw [exponential_eq_complete h, hm]
  exact not_isAcyclic_complete m

theorem not_isBipartite_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 3) : ¬ IsBipartite (G ^g H) := by
  rw [exponential_eq_complete h, hm]
  exact not_isBipartite_complete m

theorem not_isTree_exponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : H.E = 0)
    (hm : G.V ^ H.V = m + 3) : ¬ IsTree (G ^g H) := by
  rw [exponential_eq_complete h, hm]
  exact not_isTree_complete m

theorem isHamiltonian_exponential_of_E_eq_zero {G H : IsoGraph} (h : H.E = 0)
    (h3 : 3 ≤ G.V ^ H.V) : (G ^g H).IsHamiltonian := by
  rw [exponential_eq_complete h]
  exact isHamiltonian_complete h3

/-! ### The hom exponential over an edgeless base

Here the collapse goes the other way: `G ^hg H` is the edgeless graph on `|G|` vertices, one for
each constant homomorphism.  Note that the vertex count is part of the conclusion — unlike `^g`,
the hom exponential has no unconditional formula for it. -/

theorem V_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).V = G.V := by
  rw [homExponential_eq_empty hG hH, V_empty]

theorem E_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).E = 0 := by
  rw [homExponential_eq_empty hG hH, E_empty]

theorem isAcyclic_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : IsAcyclic (G ^hg H) := by
  rw [homExponential_eq_empty hG hH]
  exact isAcyclic_empty _

theorem isBipartite_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : IsBipartite (G ^hg H) := by
  rw [homExponential_eq_empty hG hH]
  exact isBipartite_empty _

theorem isArcTransitive_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).IsArcTransitive := by
  rw [homExponential_eq_empty hG hH]
  exact isArcTransitive_empty _

theorem isVertexTransitive_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).IsVertexTransitive := by
  rw [homExponential_eq_empty hG hH]
  exact isVertexTransitive_empty _

theorem isDS_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    IsDS (G ^hg H) := by
  rw [homExponential_eq_empty hG hH]
  exact isDS_empty _

theorem isRegularWith_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).IsRegularWith 0 := by
  rw [homExponential_eq_empty hG hH]
  exact isRegularWith_empty _

theorem isSRGWith_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).IsSRGWith G.V 0 0 0 := by
  rw [homExponential_eq_empty hG hH]
  exact isSRGWith_empty _

theorem autCount_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).autCount = Nat.factorial G.V := by
  rw [homExponential_eq_empty hG hH, autCount_empty]

theorem charpoly_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).charpoly = X ^ G.V := by
  rw [homExponential_eq_empty hG hH, charpoly_empty]

theorem spectrum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).spectrum = Multiset.replicate G.V 0 := by
  rw [homExponential_eq_empty hG hH, spectrum_empty]

theorem lapCharpoly_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).lapCharpoly = X ^ G.V := by
  rw [homExponential_eq_empty hG hH, lapCharpoly_empty]

theorem lapSpectrum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).lapSpectrum = Multiset.replicate G.V 0 := by
  rw [homExponential_eq_empty hG hH, lapSpectrum_empty]

theorem energy_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).energy = 0 := by
  rw [homExponential_eq_empty hG hH, energy_empty]

theorem cliqueNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).cliqueNum = min G.V 1 := by
  rw [homExponential_eq_empty hG hH, cliqueNum_empty]

theorem cliqueCount_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) (k : ℕ) : (G ^hg H).cliqueCount (k + 2) = 0 := by
  rw [homExponential_eq_empty hG hH, cliqueCount_empty]

theorem cliqueCoverNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).cliqueCoverNum = G.V := by
  rw [homExponential_eq_empty hG hH, cliqueCoverNum_empty]

theorem comps_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).comps = Multiset.replicate G.V (empty 1) := by
  rw [homExponential_eq_empty hG hH, comps_empty]

theorem coverNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).coverNum = 0 := by
  rw [homExponential_eq_empty hG hH, coverNum_empty]

theorem degMultiset_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : degMultiset (G ^hg H) = Multiset.replicate G.V 0 := by
  rw [homExponential_eq_empty hG hH, degMultiset_empty]

theorem degSequence_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : degSequence (G ^hg H) = List.replicate G.V 0 := by
  rw [homExponential_eq_empty hG hH, degSequence_empty]

theorem diameter_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).diameter = 0 := by
  rw [homExponential_eq_empty hG hH, diameter_empty]

theorem radius_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).radius = 0 := by
  rw [homExponential_eq_empty hG hH, radius_empty]

theorem girth_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).girth = 0 := by
  rw [homExponential_eq_empty hG hH, girth_empty]

theorem domNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    (G ^hg H).domNum = G.V := by
  rw [homExponential_eq_empty hG hH, domNum_empty]

theorem edgeChromNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).edgeChromNum = 0 := by
  rw [homExponential_eq_empty hG hH, edgeChromNum_empty]

theorem edgeConn_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).edgeConn = 0 := by
  rw [homExponential_eq_empty hG hH, edgeConn_empty]

theorem vertexConn_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).vertexConn = 0 := by
  rw [homExponential_eq_empty hG hH, vertexConn_empty]

theorem indepNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).indepNum = G.V := by
  rw [homExponential_eq_empty hG hH, indepNum_empty]

theorem indepCount_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) (k : ℕ) : (G ^hg H).indepCount k = G.V.choose k := by
  rw [homExponential_eq_empty hG hH, indepCount_empty]

theorem matchNum_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).matchNum = 0 := by
  rw [homExponential_eq_empty hG hH, matchNum_empty]

theorem maxDeg_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    maxDeg (G ^hg H) = 0 := by
  rw [homExponential_eq_empty hG hH, maxDeg_empty]

theorem minDeg_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.IsConnected) :
    minDeg (G ^hg H) = 0 := by
  rw [homExponential_eq_empty hG hH, minDeg_empty]

theorem numComponents_homExponential_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0)
    (hH : H.IsConnected) : (G ^hg H).numComponents = G.V := by
  rw [homExponential_eq_empty hG hH, numComponents_empty]

/-! One vertex is enough to make the chromatic number visible. -/

theorem chromNum_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 1) : (G ^hg H).chromNum = 1 := by
  rw [homExponential_eq_empty hG hH, hm, chromNum_empty]

theorem lapLambdaMax_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 1) : (G ^hg H).lapLambdaMax = 0 := by
  rw [homExponential_eq_empty hG hH, hm, lapLambdaMax_empty]

/-! Two vertices and the graph is visibly disconnected. -/

theorem algConn_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 2) : (G ^hg H).algConn = 0 := by
  rw [homExponential_eq_empty hG hH, hm, algConn_empty]

theorem not_isConnected_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 2) : ¬ IsConnected (G ^hg H) := by
  rw [homExponential_eq_empty hG hH, hm]
  exact not_isConnected_empty m

theorem not_isHamiltonian_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 2) : ¬ IsHamiltonian (G ^hg H) := by
  rw [homExponential_eq_empty hG hH, hm]
  exact not_isHamiltonian_empty m

theorem not_isTree_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.IsConnected) (hm : G.V = m + 2) : ¬ IsTree (G ^hg H) := by
  rw [homExponential_eq_empty hG hH, hm]
  exact not_isTree_empty m

theorem not_isSelfComplementary_homExponential_of_E_eq_zero {G H : IsoGraph} {m : ℕ}
    (hG : G.E = 0) (hH : H.IsConnected) (hm : G.V = m + 2) :
    ¬ IsSelfComplementary (G ^hg H) := by
  rw [homExponential_eq_empty hG hH, hm]
  exact not_isSelfComplementary_empty m

/-! ### The four products

Only the rows still open in the product columns appear here; the rest of those columns already have
formulas that say something.  The tensor product is the interesting one — it annihilates on a
single edgeless factor, since an edge of the product is an edge of each factor at once — while the
other three need both. -/

/-- **The tensor product annihilates.**  An edge of `G ⊗g H` is an edge of `G` and an edge of `H`
at once, so one edgeless factor empties the product. -/
theorem tensorProduct_eq_empty {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    G ⊗g H = empty (G.V * H.V) := by
  have hE : (G ⊗g H).E = 0 := by
    rw [E_tensorProduct]; rcases h with h | h <;> simp [h]
  rw [eq_empty_of_E_eq_zero hE, V_tensorProduct]

/-- The cartesian product of two edgeless graphs is edgeless. -/
theorem cartesianProduct_eq_empty {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    G □g H = empty (G.V * H.V) := by
  have hE : (G □g H).E = 0 := by simp [E_cartesianProduct, hG, hH]
  rw [eq_empty_of_E_eq_zero hE, V_cartesianProduct]

/-- The strong product of two edgeless graphs is edgeless. -/
theorem strongProduct_eq_empty {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    G ⊠g H = empty (G.V * H.V) := by
  have hE : (G ⊠g H).E = 0 := by simp [E_strongProduct, hG, hH]
  rw [eq_empty_of_E_eq_zero hE, V_strongProduct]

/-- The lexicographic product of two edgeless graphs is edgeless. -/
theorem lexProduct_eq_empty {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    G ·g H = empty (G.V * H.V) := by
  have hE : (G ·g H).E = 0 := by simp [E_lexProduct, hG, hH]
  rw [eq_empty_of_E_eq_zero hE, V_lexProduct]

/-! The tensor product then settles seven rows at once. -/

theorem isDS_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    IsDS (G ⊗g H) := by
  rw [tensorProduct_eq_empty h]
  exact isDS_empty _

theorem diameter_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    (G ⊗g H).diameter = 0 := by
  rw [tensorProduct_eq_empty h, diameter_empty]

theorem radius_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    (G ⊗g H).radius = 0 := by
  rw [tensorProduct_eq_empty h, radius_empty]

theorem domNum_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    (G ⊗g H).domNum = G.V * H.V := by
  rw [tensorProduct_eq_empty h, domNum_empty]

theorem matchNum_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) :
    (G ⊗g H).matchNum = 0 := by
  rw [tensorProduct_eq_empty h, matchNum_empty]

theorem indepCount_tensorProduct_of_E_eq_zero {G H : IsoGraph} (h : G.E = 0 ∨ H.E = 0) (k : ℕ) :
    (G ⊗g H).indepCount k = (G.V * H.V).choose k := by
  rw [tensorProduct_eq_empty h, indepCount_empty]

theorem algConn_tensorProduct_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (h : G.E = 0 ∨ H.E = 0)
    (hm : G.V * H.V = m + 2) : (G ⊗g H).algConn = 0 := by
  rw [tensorProduct_eq_empty h, hm, algConn_empty]

/-! And the other three settle what is left of theirs. -/

theorem isDS_cartesianProduct_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    IsDS (G □g H) := by
  rw [cartesianProduct_eq_empty hG hH]
  exact isDS_empty _

theorem isDS_strongProduct_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    IsDS (G ⊠g H) := by
  rw [strongProduct_eq_empty hG hH]
  exact isDS_empty _

theorem indepCount_strongProduct_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0)
    (k : ℕ) : (G ⊠g H).indepCount k = (G.V * H.V).choose k := by
  rw [strongProduct_eq_empty hG hH, indepCount_empty]

theorem algConn_strongProduct_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0) (hH : H.E = 0)
    (hm : G.V * H.V = m + 2) : (G ⊠g H).algConn = 0 := by
  rw [strongProduct_eq_empty hG hH, hm, algConn_empty]

theorem isDS_lexProduct_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    IsDS (G ·g H) := by
  rw [lexProduct_eq_empty hG hH]
  exact isDS_empty _

theorem matchNum_lexProduct_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    (G ·g H).matchNum = 0 := by
  rw [lexProduct_eq_empty hG hH, matchNum_empty]

theorem algConn_lexProduct_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0) (hH : H.E = 0)
    (hm : G.V * H.V = m + 2) : (G ·g H).algConn = 0 := by
  rw [lexProduct_eq_empty hG hH, hm, algConn_empty]

theorem lapLambdaMax_lexProduct_of_E_eq_zero {G H : IsoGraph} {m : ℕ} (hG : G.E = 0)
    (hH : H.E = 0) (hm : G.V * H.V = m + 1) : (G ·g H).lapLambdaMax = 0 := by
  rw [lexProduct_eq_empty hG hH, hm, lapLambdaMax_empty]

/-! ### The complement, the line graph and the join

Three unary-ish leftovers.  The complement of an edgeless graph is complete and its line graph has
no vertices at all, so both collapse as before.  The join is the one place where the collapse is
not the end of the story: it lands on a complete bipartite graph rather than on `empty` or
`complete`, which settles the size of a maximum matching but not much else. -/

/-- The complement of an edgeless graph is complete. -/
theorem compl_eq_complete_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) : Gᶜ = complete G.V := by
  conv_lhs => rw [eq_empty_of_E_eq_zero h]
  exact compl_empty G.V

theorem matchNum_compl_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) : Gᶜ.matchNum = G.V / 2 := by
  rw [compl_eq_complete_of_E_eq_zero h, matchNum_complete]

/-- The line graph of an edgeless graph has no vertices at all: there are no edges to be its
vertices. -/
theorem lineGraph_eq_empty_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) : lineGraph G = empty 0 := by
  conv_lhs => rw [eq_empty_of_E_eq_zero h]
  exact lineGraph_empty G.V

theorem isArcTransitive_lineGraph_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) :
    IsArcTransitive (lineGraph G) := by
  rw [lineGraph_eq_empty_of_E_eq_zero h]
  exact isArcTransitive_empty 0

theorem isDS_lineGraph_of_E_eq_zero {G : IsoGraph} (h : G.E = 0) : IsDS (lineGraph G) := by
  rw [lineGraph_eq_empty_of_E_eq_zero h]
  exact isDS_empty 0

/-- The join of two edgeless graphs is the complete bipartite graph between them. -/
theorem join_eq_bipartite_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    G ∇g H = bipartite G.V H.V := by
  conv_lhs => rw [eq_empty_of_E_eq_zero hG, eq_empty_of_E_eq_zero hH]
  exact (bipartite_eq_join G.V H.V).symm

/-- `matchNum_bipartite` without its nonemptiness side conditions. -/
theorem matchNum_bipartite_eq_min (m n : ℕ) : (bipartite m n).matchNum = min m n := by
  match m, n with
  | 0, n => simp
  | m + 1, 0 => simp
  | m + 1, n + 1 => rw [matchNum_bipartite]

theorem matchNum_join_of_E_eq_zero {G H : IsoGraph} (hG : G.E = 0) (hH : H.E = 0) :
    (G ∇g H).matchNum = min G.V H.V := by
  rw [join_eq_bipartite_of_E_eq_zero hG hH, matchNum_bipartite_eq_min]

/-- Whether a join is determined by its spectrum depends on more than the two arguments' edge
counts.  At one end, a join of complete graphs is complete, and complete graphs are determined. -/
theorem isDS_join_complete (m n : ℕ) : IsDS (complete m ∇g complete n) := by
  rw [join_complete]
  exact isDS_complete (m + n)

/-- At the other end, a join of edgeless graphs need not be: `empty 1 ∇g empty 4` is the star
`K₁,₄`, and `not_isDS_star_four` exhibits the disconnected `K₂,₂ ⊔ K₁` cospectral with it. -/
theorem not_isDS_join_empty : ¬ IsDS (empty 1 ∇g empty 4) := by
  rw [← bipartite_eq_join, ← star_eq_bipartite]
  exact not_isDS_star_four

end IsoGraph
