# Declaration-level source map

This ledger maps source obligations to Lean declarations. A blank declaration means the
requirement has not yet been formalized; it must not be inferred from roadmap prose.

## Clay/Jaffe–Witten source of record

Artifact: `Sources/Clay/yangmills_official.pdf`
Searchable extraction: `Sources/Clay/yangmills_official.txt`

| Source locator | Requirement | Classification | Lean declaration | Status / decision |
|---|---|---|---|---|
| p. 5 §3; text 222–240 | Hilbert space, Poincaré representation, self-adjoint translation generators, invariant unique vacuum, positive energy, covariance and locality | Model requirement | — | Pending Wightman/Poincaré sources and definitions |
| p. 5 §3; text 241–253 | Relation between Euclidean and Lorentzian axiom schemes through reflection positivity/reconstruction | Bridge | — | Pending corrected OS source pin; no definitional identification allowed |
| p. 6 §4; text 263–266 | 4D QFT with local operators corresponding to gauge-invariant local curvature polynomials and covariant derivatives | Model requirement | — | Pending geometry and renormalized observable semantics |
| p. 6 §4; footnote 1; text 298–304 | Renormalization prevents a natural one-to-one classical-polynomial/quantum-field correspondence | Formalization constraint | — | Raw syntactic injectivity is forbidden as canonical semantics |
| p. 6 §4; text 267–271 | Short-distance agreement with asymptotic freedom and perturbative renormalization | Model requirement | — | Pending primary renormalization sources and precise distributional formulation |
| p. 6 §4; text 269–271 | Stress tensor | Model requirement | — | Pending source and semantics |
| p. 6 §4; text 269–271 | Operator-product expansion with prescribed local singularities | Model requirement | — | Pending source and semantics |
| p. 6 §4; text 272–276 | Poincaré-invariant zero-energy vacuum, nonnegative Hamiltonian spectrum and no spectrum in `(0, Δ)` | Model requirement / definition | — | Pending physical translation/PVM semantics |
| p. 6 §4; text 275–276 | Supremum of admissible gaps is finite mass | Model requirement / definition | — | Pending non-vacuous supremum definition |
| p. 6 §4; text 277–280 | For every compact simple gauge group, a nontrivial QFT on `ℝ⁴` exists and has positive gap | Final acceptance proposition | — | Pending all lower layers; no inhabitant asserted |
| p. 6 §4; text 279–280 | Axiomatic properties at least as strong as references [45, 35] | Comparative requirement | — | Pending verified Wightman and corrected OS source maps |

## Gauge-group convention evidence

| Source locator | Evidence | Formalization consequence | Status |
|---|---|---|---|
| Clay p. 6 §4; text 277–280 | Universal quantifier over “any compact simple gauge group G” | Preserve `G` as a quantified group; do not restrict the final target to one example family | Pinned; exact phrase does not define connectedness/global form |
| Hall 2000, printed p. 115 §7; extracted 6092–6095 | Simple Lie algebra has no ideals except zero/whole and has dimension at least two | Use Mathlib `LieAlgebra.IsSimple`, which also explicitly requires non-abelianness; do not use abstract group simplicity | Pinned mathematical context; Hall passage is in complex semisimple section |
| Aharony–Seiberg–Tachikawa 2013, printed pp. 1–2; extracted 44–65 and 84–119 | Lie algebra and global gauge group are distinct; connected groups are quotients of the universal cover by a subgroup of its center; global form changes physical data | Keep group/global form explicit; do not silently replace by the simply connected cover or `SU(N)` | Pinned; connectedness is an explicit project convention, not claimed as verbatim Clay wording |

The reusable Lie-algebra layer now exposes the selected Mathlib semantics:

| Lean declaration | Meaning | Classification | Hostile evidence |
|---|---|---|---|
| `YangMills.Mathematics.lieAlgebra_isSimple_iff_ideals_and_nonabelian` | `LieAlgebra.IsSimple` is exactly ideal-triviality plus non-abelianness | Derived interface theorem over Mathlib | exact bidirectional proof |
| `YangMills.Mathematics.isSimple_not_isLieAbelian` | simplicity excludes abelian brackets | Derived theorem | `abelian_simpleLieAlgebra_blocked` |
| `YangMills.Mathematics.isSimple_ideal_eq_bot_or_eq_top` | every Lie ideal is zero or whole | Derived theorem | `proper_nonzero_ideal_blocked` |
| `YangMills.Mathematics.isSimple_to_nontrivial` | a simple Lie algebra has nontrivial carrier | Derived theorem | `subsingleton_simpleLieAlgebra_blocked` |

No compact-simple gauge-group Lean certificate is canonical yet. It requires the reviewed Mathlib
Lie-group/tangent-Lie-algebra bridge, compactness, connectedness, global-form preservation, and
positive consistency evidence.

## Dimension-foundation decisions

| Lean declaration | Meaning | Source / decision | Classification | Hostile evidence |
|---|---|---|---|---|
| `YangMills.EuclideanDimension` | Euclidean spacetime dimension restricted to `1 ≤ d ≤ 4` | Project scope decision; Clay p. 6 §4 fixes the four-dimensional endpoint but does not require lower-dimensional contracts | Definition | `zero_dimension_blocked`, `dimension_above_four_blocked` |
| `EuclideanDimension.one` through `.four` | The four supported named dimensions | Project bookkeeping | Definition | exhaustive `eq_one_or_eq_two_or_eq_three_or_eq_four` |
| `EuclideanDimension.spatialDimension` | Arithmetic `d - 1`, used only after selecting one coordinate as time | Formalization decision; does not assert OS reconstruction | Definition | `one_has_no_spatial_coordinate` |
| `EuclideanDimension.Spacetime` | Mathlib real Euclidean coordinate space indexed by `d` | Mathlib primitive; Clay p. 6 fixes `d = 4` for the final target | Definition | `finrank_spacetime`, `no_linearEquiv_two_four` |

Dimensions one through three remain consistency regimes requested by this project, not claims in the
Clay problem statement. Their physical contracts require separate sources before introduction.

## Signature-foundation decisions

| Lean declaration | Meaning | Source / decision | Classification | Hostile evidence |
|---|---|---|---|---|
| `EuclideanDimension.CoordinateVector` | Algebraic real coordinate vectors with no selected topology or form | Project definition over the dimension index | Definition | Forms are added separately rather than hidden in the carrier |
| `EuclideanDimension.euclideanQuadraticForm` | All-positive sum-of-squares form | Standard mathematical convention; Clay p. 5 distinguishes Euclidean spacetime but does not state this formula | Formalization definition | `negative_euclidean_value_blocked` |
| `EuclideanDimension.minkowskiQuadraticForm` | Mostly-minus form with coordinate zero positive | Clay p. 5 §3, text 227–232 requires Minkowski signature and translation generators; `(+,-,…,-)` is an explicit project convention | Formalization definition | `nonpositive_minkowski_time_basis_blocked`, `nonnegative_minkowski_spatial_basis_blocked` |
| `EuclideanDimension.spatialIndexSucc` | Places spatial indices after coordinate zero | Project coordinate convention; no reconstruction asserted | Definition | spatial-basis negative-value theorem |
| `euclideanQuadraticForm_nondegenerate`, `minkowskiQuadraticForm_nondegenerate` | Both selected forms have zero radical | Derived from Mathlib's radical theorem for weighted sums of squares and the nonzero weights | Derived theorem | `degenerate_euclideanQuadraticForm_blocked`, `degenerate_minkowskiQuadraticForm_blocked` |
| `one_euclideanQuadraticForm_eq_minkowskiQuadraticForm` | In `d = 1`, no spatial weight distinguishes the two algebraic forms | Derived from the definitions; does not identify theories | Derived theorem | exact proof |
| `euclideanQuadraticForm_ne_minkowskiQuadraticForm` | From `d = 2` onward, a spatial basis vector separates the forms | Derived from the definitions | Derived theorem | 2D and 4D identification-blocking probes |

No Lorentz group, Euclidean group, analytic continuation, or OS bridge is claimed by these
quadratic-form declarations.

## Non-source project declarations

| Lean declaration | Purpose | Authority | Axiom status |
|---|---|---|---|
| `YangMills.Audit.audit_yang_mills_axioms` command | Kernel-level rejection of `sorryAx` and project-defined axioms | Project validation infrastructure; uses `Lean.collectAxioms` | Checked by the root build and mutation fixtures |

Every future canonical physical declaration must be added here in the same commit that introduces
it. “Pending” rows are obligations, not accepted placeholder fields.
