import IsoGraph.Values.Identities
import IsoGraph.Values.Spectrum

/-!
# The values of the invariants

The invariants of `IsoGraph/Invariants/` evaluated on the graphs of `IsoGraph/Graphs/`.
`Values/Identities.lean` is the bulk of it: the equations between the constructions — the
complement of the 5-cycle is the 5-cycle, `K_{m,n}` is the join of two empty graphs — and then,
family by family, the order, size, degree sequence, connectivity, girth, diameter, clique and
independence numbers, and chromatic number of every construction, all as `simp` lemmas on
`IsoGraph`.  `Values/Spectrum.lean` does the same for the adjacency spectrum, which needs enough
machinery of its own — characteristic polynomials, circulants, the discrete Fourier transform —
to be worth a module.
-/
