import IsoGraph.Enum.All
import IsoGraph.Enum.Conn

/-!
# The enumeration engine

For each `n`, a list holding exactly one graph from every isomorphism class on `n` vertices
(`Enum/All.lean`) and from every *connected* class (`Enum/Conn.lean`), together with completeness,
pairwise non-isomorphy, and the quotient-level statement that the list *is* the set of classes.
Both rest on the canonical labelling: canonical codes are the fixed points of `canonCode`, so
deduplication is a filter.
-/
