import IsoGraph.Enum.Conn
import IsoGraph.Graphs.CliqueSum

/-!
# Named small graphs

A name for every connected graph on at most six vertices: 1, 1, 2, 6, 21 and 112 of them, 143 in
all.  Where a graph has a customary name (claw, paw, bull, cricket, net, house, gem, dart, kite,
domino, fish, prism, octahedron, 3-sun, …) that is the name it gets here; the rest are named after
the way they are built (`tadpole33`, `spider122`, `diamondPendantsTips`, `coP6`, `K6MinusGem`, …).
Two conventions run through the dense end of the list:

* `coX` is the complement of `X`, used when `X` is connected;
* `K6MinusX` is `K₆` with the edges of `X` deleted, used when the complement is `X` together with
  some isolated vertices — equivalently, when the graph has a universal vertex.

A definition that is precisely one call to one constructor is an `abbrev`, so that instance search
and `decide` see through it; anything compound is a `def`.

The point of the file is the completeness statement at the end: for each `n ≤ 6`,
`enumerateConnIso n` — the list of *all* connected isomorphism classes on `n` vertices, as produced
and verified in `IsoGraph/Enum/Conn.lean` — is exactly the list of names given here.  So the
names are known to cover every graph, and (because the enumeration has no repeats) to be pairwise
non-isomorphic.  `connOfCard_complete` and `connOfCard_pairwise` package that up.
-/

namespace SmallGraphs

open CGraph CGraph.Enum

/-! ## Edge lists used by more than one graph

Written out once, so that the decorated versions below agree on which vertex is which. -/

/-- The triangle `0-1-2`. -/
private def triangleEdges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0)]

/-- The diamond with hubs `0`, `1` and tips `2`, `3`. -/
private def diamondEdges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]

/-- The house with apex `0`, roof corners `1`, `4` and base corners `2`, `3`. -/
private def houseEdges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 4)]

/-- `K₂,₃` with sides `{0, 1}` and `{2, 3, 4}`. -/
private def k23Edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

/-- The butterfly with hub `0` and wings `{1, 2}`, `{3, 4}`. -/
private def butterflyEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]


/-! ## One vertex -/

/-- The one-vertex graph. -/
abbrev K1 : CGraph := complete 1

/-! ## Two vertices -/

/-- The single edge. -/
abbrev K2 : CGraph := complete 2

/-! ## Three vertices -/

/-- The path on three vertices, also called the cherry. -/
abbrev P3 : CGraph := path 3

/-- The triangle. -/
abbrev K3 : CGraph := complete 3

/-! ## Four vertices -/

/-- The four-cycle, also called the square. -/
abbrev C4 : CGraph := cycle 4

/-- The path on four vertices. -/
abbrev P4 : CGraph := path 4

/-- The star `K₁,₃`, better known as the claw. -/
abbrev K1_3 : CGraph := star 3

/-- The claw, another name for `K₁,₃`. -/
abbrev claw : CGraph := K1_3

/-- The paw: a triangle with a pendant vertex, i.e. a triangle and an edge glued at a vertex. -/
abbrev paw : CGraph := oneCliqueSum K3 K2

/-- The diamond `K₄ - e`: two triangles glued along an edge.  Its two degree-3 vertices are
called the *hubs* and its two degree-2 vertices the *tips*. -/
abbrev diamond : CGraph := twoCliqueSum K3 K3

/-- The complete graph on four vertices. -/
abbrev K4 : CGraph := complete 4

/-! ## Five vertices -/

/-- The five-cycle. -/
abbrev C5 : CGraph := cycle 5

/-- The path on five vertices. -/
abbrev P5 : CGraph := path 5

/-- The complete bipartite graph `K₂,₃`. -/
abbrev K2_3 : CGraph := bipartite 2 3

/-- The graph `K₂,₃` with an edge added inside its two-element side; equivalently the five-cycle
with two disjoint chords, or `K₅` minus a path and a disjoint edge. -/
def k23PlusEdge : CGraph := (P3 ⊕g K2)ᶜ

/-- The fork, also called the chair: the claw with one edge subdivided. -/
abbrev fork : CGraph := spider [1, 1, 2]

/-- The banner: a four-cycle with a pendant vertex. -/
abbrev banner : CGraph := tadpole 4 1

/-- The bull: a triangle with a pendant vertex at each of two corners.  It is self-complementary. -/
abbrev bull : CGraph := cyclePendant 3 [1, 1]

/-- The house: a triangle sitting on top of a square, i.e. `C₅` with one chord.  Its three vertex
orbits are the apex, the two roof corners of degree 3 and the two base corners. -/
abbrev house : CGraph := twoCliqueSum K3 C4

/-- The kite: the diamond with a pendant vertex at a tip. -/
abbrev kite : CGraph := ofEdges 5 ((2, 4) :: diamondEdges)

/-- The (3,2)-tadpole: a triangle with a path of two attached. -/
abbrev tadpole32 : CGraph := tadpole 3 2

/-- The star `K₁,₄`. -/
abbrev K1_4 : CGraph := star 4

/-- The butterfly, also called the bowtie: two triangles sharing a vertex. -/
abbrev butterfly : CGraph := oneCliqueSum K3 K3

/-- The wheel `W₄`: a four-cycle plus a hub. -/
abbrev W4 : CGraph := wheel 4

/-- The cricket: a triangle with two pendant vertices at one corner. -/
abbrev cricket : CGraph := cyclePendant 3 [2]

/-- The gem: a path on four vertices plus a hub. -/
abbrev gem : CGraph := fan 4

/-- The dart: the diamond with a pendant vertex at a hub. -/
abbrev dart : CGraph := ofEdges 5 ((0, 4) :: diamondEdges)

/-- The 4-lollipop: `K₄` with a pendant vertex. -/
abbrev lollipop41 : CGraph := lollipop 4 1

/-- The book `B₃ = K₁,₁,₃`: three triangles glued along an edge. -/
abbrev book3 : CGraph := book 3

/-- `K₅` with the two edges of a path removed. -/
def K5MinusP3 : CGraph := (P3 ⊕g empty 2)ᶜ

/-- `K₅` with one edge removed. -/
def K5MinusEdge : CGraph := (K2 ⊕g empty 3)ᶜ

/-- The complete graph on five vertices. -/
abbrev K5 : CGraph := complete 5

/-! ## Six vertices: trees -/

/-- The path on six vertices. -/
abbrev P6 : CGraph := path 6

/-- The spider `S(1,1,3)`: a centre with two leaves and a path of three hanging off it. -/
abbrev spider113 : CGraph := spider [1, 1, 3]

/-- The spider `S(1,2,2)`: a centre with one leaf and two paths of two. -/
abbrev spider122 : CGraph := spider [1, 2, 2]

/-- The cross: a centre with three leaves and a path of two, i.e. the claw with one edge
subdivided and one extra leaf. -/
abbrev cross : CGraph := spider [1, 1, 1, 2]

/-- The H graph: an edge with two pendant vertices at each end (the double star `S(2,2)`). -/
abbrev H : CGraph := doubleStar 2 2

/-- The star `K₁,₅`. -/
abbrev K1_5 : CGraph := star 5

/-! ## Six vertices: one cycle -/

/-- The six-cycle. -/
abbrev C6 : CGraph := cycle 6

/-- The (3,3)-tadpole: a triangle with a path of three attached. -/
abbrev tadpole33 : CGraph := tadpole 3 3

/-- The (4,2)-tadpole: a four-cycle with a path of two attached. -/
abbrev tadpole42 : CGraph := tadpole 4 2

/-- The (5,1)-tadpole: a five-cycle with a pendant vertex. -/
abbrev tadpole51 : CGraph := tadpole 5 1

/-- The net: a triangle with a pendant vertex at each corner. -/
abbrev net : CGraph := cyclePendant 3 [1, 1, 1]

/-- A triangle with two pendant vertices at one corner and one at another. -/
abbrev c3Pendants210 : CGraph := cyclePendant 3 [2, 1]

/-- A triangle with three pendant vertices at one corner. -/
abbrev c3Pendants300 : CGraph := cyclePendant 3 [3]

/-- A triangle with a pendant vertex at one corner and a path of two at another. -/
abbrev c3Legs12 : CGraph := ofEdges 6 ((0, 3) :: (1, 4) :: (4, 5) :: triangleEdges)

/-- A triangle with a pendant vertex and a path of two at the same corner. -/
abbrev c3Legs12Same : CGraph := ofEdges 6 ((0, 3) :: (0, 4) :: (4, 5) :: triangleEdges)

/-- A triangle with a fork attached: one corner carries a vertex that carries two leaves. -/
abbrev c3Fork : CGraph := ofEdges 6 ((0, 3) :: (3, 4) :: (3, 5) :: triangleEdges)

/-- A four-cycle with a pendant vertex at each of two opposite corners. -/
abbrev c4Pendants1010 : CGraph := cyclePendant 4 [1, 0, 1]

/-- A four-cycle with a pendant vertex at each of two adjacent corners. -/
abbrev c4Pendants1100 : CGraph := cyclePendant 4 [1, 1]

/-- A four-cycle with two pendant vertices at one corner. -/
abbrev c4Pendants2000 : CGraph := cyclePendant 4 [2]

/-! ## Six vertices: two or more cycles, at most seven edges -/

/-- The theta graph `Θ(2,2,3)`: two poles joined by three internally disjoint paths, of lengths
2, 2 and 3. -/
abbrev theta223 : CGraph := thetaGraph [1, 1, 2]

/-- The theta graph `Θ(1,2,4)`: a triangle and a pentagon sharing an edge. -/
abbrev theta124 : CGraph := thetaGraph [0, 1, 3]

/-- The domino: the 2×3 grid `P₃ □ K₂`, also the theta graph `Θ(1,3,3)`, and two squares glued
along an edge. -/
abbrev domino : CGraph := twoCliqueSum C4 C4

/-- The barbell: two triangles joined by an edge. -/
abbrev barbell : CGraph := ofEdges 6 ((0, 3) :: (3, 4) :: (4, 5) :: (5, 3) :: triangleEdges)

/-- The fish: a triangle and a four-cycle sharing a vertex. -/
abbrev fish : CGraph := oneCliqueSum K3 C4

/-- The house with a pendant vertex at its apex. -/
abbrev housePendantApex : CGraph := ofEdges 6 ((0, 5) :: houseEdges)

/-- The house with a pendant vertex at a roof corner (a degree-3 vertex). -/
abbrev housePendantRoof : CGraph := ofEdges 6 ((1, 5) :: houseEdges)

/-- The house with a pendant vertex at a base corner. -/
abbrev housePendantBase : CGraph := ofEdges 6 ((2, 5) :: houseEdges)

/-- The diamond with a pendant vertex at each tip. -/
abbrev diamondPendantsTips : CGraph := ofEdges 6 ((2, 4) :: (3, 5) :: diamondEdges)

/-- The diamond with a pendant vertex at each hub. -/
abbrev diamondPendantsHubs : CGraph := ofEdges 6 ((0, 4) :: (1, 5) :: diamondEdges)

/-- The diamond with a pendant vertex at a tip and another at a hub. -/
abbrev diamondPendantsTipHub : CGraph := ofEdges 6 ((2, 4) :: (0, 5) :: diamondEdges)

/-- The diamond with two pendant vertices at the same tip. -/
abbrev diamondPendantsSameTip : CGraph := ofEdges 6 ((2, 4) :: (2, 5) :: diamondEdges)

/-- The diamond with two pendant vertices at the same hub. -/
abbrev diamondPendantsSameHub : CGraph := ofEdges 6 ((0, 4) :: (0, 5) :: diamondEdges)

/-- The diamond with a path of two attached at a tip. -/
abbrev diamondTailTip : CGraph := ofEdges 6 ((2, 4) :: (4, 5) :: diamondEdges)

/-- The diamond with a path of two attached at a hub. -/
abbrev diamondTailHub : CGraph := ofEdges 6 ((0, 4) :: (4, 5) :: diamondEdges)

/-- `K₂,₃` with a pendant vertex on its two-element side. -/
abbrev k23PendantDeg3 : CGraph := ofEdges 6 ((0, 5) :: k23Edges)

/-- `K₂,₃` with a pendant vertex on its three-element side. -/
abbrev k23PendantDeg2 : CGraph := ofEdges 6 ((2, 5) :: k23Edges)

/-- The butterfly with a pendant vertex on a wing. -/
abbrev butterflyPendant : CGraph := ofEdges 6 ((1, 5) :: butterflyEdges)

/-- The butterfly with a pendant vertex at its hub. -/
abbrev butterflyPendantHub : CGraph := ofEdges 6 ((0, 5) :: butterflyEdges)

/-! ## Six vertices: complements of the graphs above -/

/-- The triangular prism `C₃ □ K₂`, the complement of the six-cycle; also the line graph of
`K₂,₃`. -/
abbrev prism3 : CGraph := prism 3

/-- The 3-sun: a triangle whose three edges each carry a further vertex, i.e. the complement of
the net. -/
def sun3 : CGraph := netᶜ

/-- The (4,2)-lollipop: `K₄` with a path of two attached; the complement of `k23PendantDeg3`. -/
abbrev lollipop42 : CGraph := lollipop 4 2

/-- The complement of the path on six vertices. -/
def coP6 : CGraph := P6ᶜ

/-- The complement of the spider `S(1,1,3)`. -/
def coSpider113 : CGraph := spider113ᶜ

/-- The complement of the spider `S(1,2,2)`. -/
def coSpider122 : CGraph := spider122ᶜ

/-- The complement of the cross. -/
def coCross : CGraph := crossᶜ

/-- The complement of the H graph; also the line graph of the butterfly. -/
def coH : CGraph := Hᶜ

/-- The complement of the (3,3)-tadpole. -/
def coTadpole33 : CGraph := tadpole33ᶜ

/-- The complement of the (4,2)-tadpole. -/
def coTadpole42 : CGraph := tadpole42ᶜ

/-- The complement of the (5,1)-tadpole. -/
def coTadpole51 : CGraph := tadpole51ᶜ

/-- The complement of `c3Pendants210`. -/
def coC3Pendants210 : CGraph := c3Pendants210ᶜ

/-- The complement of `c3Legs12`. -/
def coC3Legs12 : CGraph := c3Legs12ᶜ

/-- The complement of `c3Legs12Same`. -/
def coC3Legs12Same : CGraph := c3Legs12Sameᶜ

/-- The complement of `c3Fork`. -/
def coC3Fork : CGraph := c3Forkᶜ

/-- The complement of `c4Pendants1010`. -/
def coC4Pendants1010 : CGraph := c4Pendants1010ᶜ

/-- The complement of `c4Pendants1100`. -/
def coC4Pendants1100 : CGraph := c4Pendants1100ᶜ

/-- The complement of `c4Pendants2000`. -/
def coC4Pendants2000 : CGraph := c4Pendants2000ᶜ

/-- The complement of `Θ(2,2,3)`. -/
def coTheta223 : CGraph := theta223ᶜ

/-- The complement of `Θ(1,2,4)`. -/
def coTheta124 : CGraph := theta124ᶜ

/-- The co-domino: the complement of the domino. -/
def coDomino : CGraph := dominoᶜ

/-- The complement of the barbell. -/
def coBarbell : CGraph := barbellᶜ

/-- The co-fish: the complement of the fish. -/
def coFish : CGraph := fishᶜ

/-- The complement of `housePendantApex`. -/
def coHousePendantApex : CGraph := housePendantApexᶜ

/-- The complement of `housePendantRoof`. -/
def coHousePendantRoof : CGraph := housePendantRoofᶜ

/-- The complement of `housePendantBase`. -/
def coHousePendantBase : CGraph := housePendantBaseᶜ

/-- The complement of `diamondPendantsTips`. -/
def coDiamondPendantsTips : CGraph := diamondPendantsTipsᶜ

/-- The complement of `diamondPendantsHubs`. -/
def coDiamondPendantsHubs : CGraph := diamondPendantsHubsᶜ

/-- The complement of `diamondPendantsTipHub`. -/
def coDiamondPendantsTipHub : CGraph := diamondPendantsTipHubᶜ

/-- The complement of `diamondPendantsSameTip`. -/
def coDiamondPendantsSameTip : CGraph := diamondPendantsSameTipᶜ

/-- The complement of `diamondTailTip`. -/
def coDiamondTailTip : CGraph := diamondTailTipᶜ

/-- The complement of `diamondTailHub`. -/
def coDiamondTailHub : CGraph := diamondTailHubᶜ

/-- The complement of `k23PendantDeg2`. -/
def coK23PendantDeg2 : CGraph := k23PendantDeg2ᶜ

/-- The complement of `butterflyPendant`. -/
def coButterflyPendant : CGraph := butterflyPendantᶜ

/-! ## Six vertices: a universal vertex, i.e. `K₆` minus a graph on five vertices -/

/-- The complete graph on six vertices. -/
abbrev K6 : CGraph := complete 6

/-- The wheel `W₅`: a five-cycle plus a hub. -/
abbrev W5 : CGraph := wheel 5

/-- The fan `F₅`: a path on five vertices plus a hub. -/
abbrev fan5 : CGraph := fan 5

/-- The 5-lollipop: `K₅` with a pendant vertex. -/
abbrev lollipop51 : CGraph := lollipop 5 1

/-- The book `B₄ = K₁,₁,₄`: four triangles glued along an edge. -/
abbrev book4 : CGraph := book 4

/-- The complete multipartite graph `K₁,₁,₁,₃`. -/
abbrev K1_1_1_3 : CGraph := completeMultipartite [1, 1, 1, 3]

/-- The complete multipartite graph `K₁,₂,₃`. -/
abbrev K1_2_3 : CGraph := completeMultipartite [1, 2, 3]

/-- The complete multipartite graph `K₁,₁,₂,₂`. -/
abbrev K1_1_2_2 : CGraph := completeMultipartite [1, 1, 2, 2]

/-- `K₆` with one edge removed. -/
def K6MinusEdge : CGraph := (K2 ⊕g empty 4)ᶜ

/-- `K₆` with the edges of a path of three removed. -/
def K6MinusP3 : CGraph := (P3 ⊕g empty 3)ᶜ

/-- `K₆` with the edges of a path of four removed. -/
def K6MinusP4 : CGraph := (P4 ⊕g empty 2)ᶜ

/-- `K₆` with the edges of a four-cycle removed. -/
def K6MinusC4 : CGraph := (C4 ⊕g empty 2)ᶜ

/-- `K₆` with the edges of a claw removed. -/
def K6MinusClaw : CGraph := (claw ⊕g empty 2)ᶜ

/-- `K₆` with the edges of a paw removed. -/
def K6MinusPaw : CGraph := (paw ⊕g empty 2)ᶜ

/-- `K₆` with the edges of a diamond removed. -/
def K6MinusDiamond : CGraph := (diamond ⊕g empty 2)ᶜ

/-- `K₆` with the edges of an edge and a disjoint path of three removed. -/
def K6MinusK2P3 : CGraph := (K2 ⊕g (P3 ⊕g empty 1))ᶜ

/-- `K₆` with the edges of a path of five removed. -/
def K6MinusP5 : CGraph := (P5 ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a fork removed. -/
def K6MinusFork : CGraph := (fork ⊕g empty 1)ᶜ

/-- `K₆` with the edges of `K₂,₃` removed. -/
def K6MinusK23 : CGraph := (K2_3 ⊕g empty 1)ᶜ

/-- `K₆` with the edges of `k23PlusEdge` removed. -/
def K6MinusK23PlusEdge : CGraph := (k23PlusEdge ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a banner removed. -/
def K6MinusBanner : CGraph := (banner ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a bull removed. -/
def K6MinusBull : CGraph := (bull ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a kite removed. -/
def K6MinusKite : CGraph := (kite ⊕g empty 1)ᶜ

/-- `K₆` with the edges of the (3,2)-tadpole removed. -/
def K6MinusTadpole32 : CGraph := (tadpole32 ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a butterfly removed. -/
def K6MinusButterfly : CGraph := (butterfly ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a cricket removed. -/
def K6MinusCricket : CGraph := (cricket ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a gem removed. -/
def K6MinusGem : CGraph := (gem ⊕g empty 1)ᶜ

/-- `K₆` with the edges of a dart removed. -/
def K6MinusDart : CGraph := (dart ⊕g empty 1)ᶜ

/-- `K₆` with the edges of the 4-lollipop removed. -/
def K6MinusLollipop41 : CGraph := (lollipop41 ⊕g empty 1)ᶜ

/-- `K₆` with the edges of the book `B₃` removed. -/
def K6MinusBook3 : CGraph := (book3 ⊕g empty 1)ᶜ

/-! ## Six vertices: the remaining joins -/

/-- The complete bipartite graph `K₃,₃`, the complement of `2K₃`. -/
abbrev K3_3 : CGraph := bipartite 3 3

/-- The complete bipartite graph `K₂,₄`. -/
abbrev K2_4 : CGraph := bipartite 2 4

/-- The octahedron `K₂,₂,₂`, the complement of `3K₂`; also the line graph of `K₄`. -/
abbrev octahedron : CGraph := completeMultipartite [2, 2, 2]

/-- The complement of `K₂` and a disjoint four-cycle. -/
def coK2C4 : CGraph := (K2 ⊕g C4)ᶜ

/-- The complement of `K₂` and a disjoint path of four. -/
def coK2P4 : CGraph := (K2 ⊕g P4)ᶜ

/-- The complement of `K₂` and a disjoint claw. -/
def coK2Claw : CGraph := (K2 ⊕g claw)ᶜ

/-- The complement of `K₂` and a disjoint paw. -/
def coK2Paw : CGraph := (K2 ⊕g paw)ᶜ

/-- The complement of `K₂` and a disjoint diamond. -/
def coK2Diamond : CGraph := (K2 ⊕g diamond)ᶜ

/-- The complement of two disjoint paths of three. -/
def coP3P3 : CGraph := (P3 ⊕g P3)ᶜ

/-- The complement of a path of three and a disjoint triangle. -/
def coP3K3 : CGraph := (P3 ⊕g K3)ᶜ

/-! ## The clique sums are unambiguous

Six of the graphs above are defined by gluing two graphs at a vertex or along an edge.  Complete
graphs and cycles are vertex- and arc-transitive, so it makes no difference *where* the gluing
happens: each of these graphs is what you get from any choice of vertices, resp. edges. -/

theorem paw_iso_vertexSum (u : K3.V) (w : K2.V) :
    Nonempty (paw ≃cg vertexSum K3 u K2 w) :=
  oneCliqueSum_iso _ _ (isVertexTransitive_complete 3) (isVertexTransitive_complete 2) u w

theorem butterfly_iso_vertexSum (u w : K3.V) :
    Nonempty (butterfly ≃cg vertexSum K3 u K3 w) :=
  oneCliqueSum_iso _ _ (isVertexTransitive_complete 3) (isVertexTransitive_complete 3) u w

theorem fish_iso_vertexSum (u : K3.V) (w : C4.V) :
    Nonempty (fish ≃cg vertexSum K3 u C4 w) :=
  oneCliqueSum_iso _ _ (isVertexTransitive_complete 3) (isVertexTransitive_cycle 4) u w

theorem diamond_iso_edgeSum {u₁ u₂ w₁ w₂ : K3.V} (hu : K3.Adj u₁ u₂) (hw : K3.Adj w₁ w₂) :
    Nonempty (diamond ≃cg edgeSum K3 u₁ u₂ K3 w₁ w₂) :=
  twoCliqueSum_iso _ _ (isArcTransitive_complete 3) (isArcTransitive_complete 3) hu hw

theorem house_iso_edgeSum {u₁ u₂ : K3.V} {w₁ w₂ : C4.V} (hu : K3.Adj u₁ u₂) (hw : C4.Adj w₁ w₂) :
    Nonempty (house ≃cg edgeSum K3 u₁ u₂ C4 w₁ w₂) :=
  twoCliqueSum_iso _ _ (isArcTransitive_complete 3) (isArcTransitive_cycle 4) hu hw

theorem domino_iso_edgeSum {u₁ u₂ w₁ w₂ : C4.V} (hu : C4.Adj u₁ u₂) (hw : C4.Adj w₁ w₂) :
    Nonempty (domino ≃cg edgeSum C4 u₁ u₂ C4 w₁ w₂) :=
  twoCliqueSum_iso _ _ (isArcTransitive_cycle 4) (isArcTransitive_cycle 4) hu hw

/-! ## Completeness

For each `n ≤ 6` the list of names above is *exactly* `enumerateConnIso n`, the enumeration of all
connected isomorphism classes on `n` vertices verified in `IsoGraph/Enum/Conn.lean`.  Both
sides are compared as lists of `IsoGraph`s, i.e. by canonical labelling, in the canonical-code
order of the enumerator.  The checks are `native_decide` throughout: the canonical labelling is
defined by well-founded recursion and lifted through a `Quotient`, so the kernel does not reduce
it even for one vertex and the compiled evaluator has to do the work. -/

/-- There is no connected graph on no vertices. -/
theorem enumerateConnIso_zero :
    enumerateConnIso 0 = ([] : List CGraph).map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on one vertex. -/
def conn1 : List CGraph :=
  [K1]

theorem enumerateConnIso_one :
    enumerateConnIso 1 = conn1.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on two vertices. -/
def conn2 : List CGraph :=
  [K2]

theorem enumerateConnIso_two :
    enumerateConnIso 2 = conn2.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on three vertices. -/
def conn3 : List CGraph :=
  [P3, K3]

theorem enumerateConnIso_three :
    enumerateConnIso 3 = conn3.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on four vertices. -/
def conn4 : List CGraph :=
  [C4, P4, K1_3, paw, diamond, K4]

theorem enumerateConnIso_four :
    enumerateConnIso 4 = conn4.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on five vertices. -/
def conn5 : List CGraph :=
  [C5, P5, K2_3, k23PlusEdge, fork, banner, bull, house, kite, tadpole32, K1_4, butterfly, W4,
   cricket, gem, dart, lollipop41, book3, K5MinusP3, K5MinusEdge, K5]

theorem enumerateConnIso_five :
    enumerateConnIso 5 = conn5.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide

/-- The connected graphs on six vertices. -/
def conn6 : List CGraph :=
  [C6, K3_3, prism3, coTheta124, P6, spider113, coBarbell, c4Pendants1010, theta223,
   housePendantBase, diamondPendantsTips, coTheta223, tadpole33, coTadpole33, k23PendantDeg3,
   coDiamondTailHub, K2_4, coK2C4, octahedron, coK2Diamond, coK2P4, coK2Paw, coK2Claw, coDomino,
   domino, cross, coTadpole42, housePendantRoof, coDiamondTailTip, spider122, tadpole51, H,
   barbell, c4Pendants1100, k23PendantDeg2, coFish, net, housePendantApex, diamondTailTip,
   theta124, c4Pendants2000, coHousePendantApex, c3Pendants210, coHousePendantBase,
   diamondPendantsSameTip, coK23PendantDeg2, sun3, coSpider122, coDiamondPendantsTipHub,
   coSpider113, tadpole42, c3Fork, c3Legs12, c3Legs12Same, coButterflyPendant, coC3Legs12,
   diamondPendantsTipHub, coC3Fork, coH, coP3P3, diamondPendantsHubs, coDiamondPendantsTips,
   coC4Pendants1100, coP6, coC3Legs12Same, coDiamondPendantsHubs, coC4Pendants1010,
   coC3Pendants210, coCross, fish, coTadpole51, coHousePendantRoof, diamondTailHub,
   butterflyPendant, lollipop42, coDiamondPendantsSameTip, coP3K3, coC4Pendants2000, K1_5,
   butterflyPendantHub, W5, fan5, K6MinusButterfly, K1_2_3, K6MinusK2P3, c3Pendants300,
   K6MinusGem, K6MinusKite, diamondPendantsSameHub, K6MinusK23PlusEdge, K6MinusBook3, K6MinusK23,
   K6MinusTadpole32, K6MinusBull, K6MinusP5, K6MinusFork, K6MinusLollipop41, K6MinusBanner,
   K6MinusDart, K6MinusCricket, lollipop51, book4, K6MinusC4, K1_1_2_2, K6MinusDiamond, K6MinusP4,
   K6MinusPaw, K6MinusClaw, K1_1_1_3, K6MinusP3, K6MinusEdge, K6]

theorem enumerateConnIso_six :
    enumerateConnIso 6 = conn6.map (Quotient.mk CGraph.isoSetoid) := by
  native_decide


/-- The named connected graphs on `n` vertices, for `n ≤ 6`. -/
def connOfCard : ℕ → List CGraph
  | 1 => conn1
  | 2 => conn2
  | 3 => conn3
  | 4 => conn4
  | 5 => conn5
  | 6 => conn6
  | _ => []

#guard ((List.range 8).map fun n ↦ (connOfCard n).length) = [0, 1, 1, 2, 6, 21, 112, 0]

/-- **The names are complete**: for `n ≤ 6`, the graphs named in this file are precisely the
connected isomorphism classes on `n` vertices. -/
theorem enumerateConnIso_eq {n : ℕ} (hn : n ≤ 6) :
    enumerateConnIso n = (connOfCard n).map (Quotient.mk CGraph.isoSetoid) := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · exact enumerateConnIso_zero
  · exact enumerateConnIso_one
  · exact enumerateConnIso_two
  · exact enumerateConnIso_three
  · exact enumerateConnIso_four
  · exact enumerateConnIso_five
  · exact enumerateConnIso_six
  · exact absurd hn (by omega)

/-- Unpacking `enumerateConnIso_eq`: every connected graph on at most six vertices is isomorphic
to one of the graphs named here… -/
theorem connOfCard_complete {n : ℕ} (hn : n ≤ 6) (G : CGraph) (hcard : Fintype.card G.V = n)
    (hG : G.IsConnected) : ∃ H ∈ connOfCard n, Nonempty (G ≃cg H) := by
  have hmem : (Quotient.mk CGraph.isoSetoid G) ∈ enumerateConnIso n :=
    mem_enumerateConnIso (G := Quotient.mk CGraph.isoSetoid G) hcard hG
  rw [enumerateConnIso_eq hn] at hmem
  obtain ⟨H, hH, he⟩ := List.mem_map.1 hmem
  exact ⟨H, hH, Quotient.exact he.symm⟩

/-- …and no two of them are isomorphic. -/
theorem connOfCard_pairwise {n : ℕ} (hn : n ≤ 6) :
    (connOfCard n).Pairwise fun G H ↦ ¬Nonempty (G ≃cg H) := by
  have := enumerateConnIso_nodup n
  rw [enumerateConnIso_eq hn, List.Nodup, List.pairwise_map] at this
  exact this.imp fun h he ↦ h (Quotient.sound he)

end SmallGraphs
