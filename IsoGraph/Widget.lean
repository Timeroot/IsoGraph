import IsoGraph.Basic
import ProofWidgets.Component.ForceGraphDisplay
import ProofWidgets.Component.HtmlDisplay

/-!
# Graph visualisation

`#html` displays a `CGraph` or `IsoGraph` as an interactive, undirected force-directed graph in
VS Code's infoview. Vertices are numbered according to the graph's `FinEnum`; an `IsoGraph` is
shown through its canonical representative.
-/

public meta section

open ProofWidgets Jsx

namespace IsoGraph.Widget

/-- Settings for the interactive graph visualiser. The vertex cap avoids accidentally rendering a
large graph (or its quadratic edge set) in the infoview. -/
structure Config where
  maxVertices : Nat := 75
  linkDistance : Float := 70
  deriving Inhabited

private def vertexLabel (id : String) : Html :=
  <g>
    <circle r="13" fill="var(--vscode-editor-background)"
      stroke="var(--vscode-editor-foreground)" strokeWidth={.num 1.5} />
    <text textAnchor="middle" dominantBaseline="middle" className="font-code">{.text id}</text>
  </g>

private def vertices (G : CGraph) : Array ForceGraphDisplay.Vertex :=
  (List.finRange G.card).toArray.map fun i =>
    let id := toString i.val
    { id, label := vertexLabel id, boundingShape := .circle 13
      details? := some <span>Vertex {Html.text id}</span> }

private def edges (G : CGraph) : Array ForceGraphDisplay.Edge := Id.run do
  let mut result := #[]
  for i in List.finRange G.card do
    for j in List.finRange i.val do
      let v := FinEnum.equiv.symm i
      let w := FinEnum.equiv.symm ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
      if G.Adj v w then
        result := result.push {
          source := toString i.val
          target := toString j.val
          details? := some <span>{Html.text s!"Edge {i.val} — {j.val}"}</span>
        }
  return result

/-- Render a concrete graph with the ProofWidgets interactive force-directed graph component. -/
def cgraph (G : CGraph) (config : Config := {}) : Html :=
  if _ : config.maxVertices < G.card then
    <div>{Html.text s!"Graph has {G.card} vertices, exceeding this visualiser's limit of {config.maxVertices}. Use IsoGraph.Widget.cgraph G with a larger maxVertices setting to raise the limit."}</div>
  else
    <ForceGraphDisplay
      vertices={vertices G}
      edges={edges G}
      defaultEdgeAttrs={#[
        ("stroke", "var(--vscode-editor-foreground)"),
        ("strokeWidth", .num 1.5)
      ]}
      forces={#[
        .link { distance? := some config.linkDistance },
        .manyBody { strength? := some (-180) },
        .collide { radius? := some 18 },
        .x { strength? := some 0.05 },
        .y { strength? := some 0.05 }
      ]}
      showDetails={true}
    />

/-- Render an isomorphism class via its canonical `CGraph` representative. -/
def isograph (G : IsoGraph) (config : Config := {}) : Html :=
  cgraph G.toCGraph config

end IsoGraph.Widget

namespace CGraph

/-- Render this graph in VS Code's infoview with `#html G`. -/
def toHtml (G : CGraph) : Html := IsoGraph.Widget.cgraph G

instance : HtmlEval CGraph where
  eval G := pure G.toHtml

end CGraph

namespace IsoGraph

/-- Render this isomorphism class in VS Code's infoview with `#html G`. -/
def toHtml (G : IsoGraph) : Html := Widget.isograph G

instance : HtmlEval IsoGraph where
  eval G := pure G.toHtml

/-- `IsoGraph` is a definition rather than an abbreviation, so this second instance also covers
terms whose elaborated type is its underlying quotient. -/
instance : HtmlEval (Quotient CGraph.isoSetoid) where
  eval G := pure (Widget.isograph G)

end IsoGraph
