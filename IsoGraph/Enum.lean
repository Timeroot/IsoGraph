import IsoGraph.Enum.All
import IsoGraph.Enum.Conn
import IsoGraph.Enum.Decide

/-!
# The enumeration engine

For each `n`, a list holding exactly one graph from every isomorphism class on `n` vertices
(`Enum/All.lean`) and from every *connected* class (`Enum/Conn.lean`), together with completeness,
pairwise non-isomorphy, and the quotient-level statement that the list *is* the set of classes.
Both rest on the canonical labelling: canonical codes are the fixed points of `canonCode`, so
deduplication is a filter.

`Enum/Decide.lean` puts those lists to work: the `small_graphs` tactic turns a statement about
every graph of a given order into a `native_decide` over the corresponding list.
-/
