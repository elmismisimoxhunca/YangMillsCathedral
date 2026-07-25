# Standalone checker source audit

## Scope

This audit covers the requirement shapes used by the bounded 3D SU(2) checker. It does not assert
that the sources construct the accepted theory. The checker specializes general source-backed
interfaces to an intentionally uninhabited project contract in dimension three.

Every retained artifact is checked by `scripts/verify_sources.py` against the nearest
`SHA256SUMS.txt`. The local `SOURCE.md` files record retrieval, edition, page, correction, and scope
information.

## Requirement-to-source map

| Checker requirement | Primary retained sources | Formal status |
|---|---|---|
| Literal matrix SU(2), unitary matrices of determinant one | Hall 2000, §2.4, retained extraction around lines 582--609 | Algebraic/topological identification target; the future carrier separately supplies compact-simple Lie geometry |
| Principal bundles, connections, curvature, invariant pairing, and Euclidean Yang--Mills action | Yang--Mills 1954; Atiyah--Hitchin--Singer 1978; Atiyah--Bott 1983; Freed 1992, especially p. 8 §1 (1.13); Husemoller 1994; Singer 1978; Jost 2017 | General geometric definitions and project interface requirements, not a 3D quantum construction |
| Wightman field, common domain, covariance, locality, vacuum, correlators, and spectrum | Wightman 1956; Hall--Wightman 1957; Streater--Wightman 2000; Bargmann 1947 and Ambrose 1944 for representation/spectral background | General axiomatic requirement surfaces |
| Euclidean Schwinger requirements and reconstruction condition | Osterwalder--Schrader I, CMP 31 (1973), 83--112; Osterwalder--Schrader II, CMP 42 (1975), 281--305 | Conditional requirement shape. OS-II corrects OS-I Lemma 8.8 and strengthens the growth hypothesis. The checker stores a current strict-domain candidate and an explicit same-correlator Wick witness; it does not claim a universal OS reconstruction theorem |
| Local observable products and nontrivial curvature-squared identification | Wilson 1969, pp. 1499--1500 §II (2.2), together with the classical curvature sources above | Project strengthening used to prevent a generic scalar theory from passing as Yang--Mills |
| Positive physical mass gap on the same reconstructed spectrum | Jaffe--Witten/Clay, `Quantum Yang--Mills Theory`, p. 6 §4 | Threshold and physical-spectrum requirement shape. Its 3D specialization is a project analogue, not the official 4D Clay endpoint |

## Explicit negative source conclusion

None of these retained sources supplies an end-to-end theorem constructing infinite-volume
continuum pure SU(2) Yang--Mills on `ℝ³`, verifying the corrected OS hypotheses for its exact
observables, reconstructing the same nontrivial Minkowski theory, and proving a positive physical
joint-spectrum gap. Consequently the standalone package contains no acceptance inhabitant.

## Retained source families

The package retains only source families relevant to its transitive checker interfaces:

- `Sources/AxiomaticQFT/`;
- `Sources/Clay/`;
- `Sources/GaugeGeometry/`;
- `Sources/LieGroups/`;
- `Sources/Observables/Wilson1969/`.

Frozen two-dimensional, unrestricted Fourier, lattice, renormalization, and stress-tensor source
tracks are not part of this package.
