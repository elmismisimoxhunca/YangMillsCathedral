# Verified status

This file records evidence for the current checkout. It is not a roadmap and does not infer
physical adequacy from compilation.

## 2026-07-15 — standalone initialization

Verified:

- Repository initialized independently on branch `cathedral`.
- Lean toolchain pinned to `leanprover/lean4:v4.31.0`.
- Mathlib input pinned to `v4.31.0`; `lake-manifest.json` resolves it to
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `lake build` completed successfully for the root library.
- The Clay PDF was independently downloaded from its canonical URL and matched the pinned bytes;
  Poppler 25.03.0 reproduced the searchable extraction byte-for-byte.
- Clay source manifest verified the PDF and text extraction. A legacy 404 HTML response was
  deliberately excluded.
- Conservative source audit found no proof placeholder or axiom-like project declaration.
- The root build ran `Lean.collectAxioms` over every loaded `YangMills` declaration and found no
  transitive `sorryAx` or project-defined axiom.
- Mutation checks confirmed rejection of source corruption, unmanifested artifacts, unsafe/control
  manifest paths, symlinks, proof placeholders, elaborated `sorryAx` dependencies and project
  axioms.
- The retired `LeanMillenniumPrizeProblems` clone is absent and is not a dependency.

## 2026-07-15 — first mathematical stone: dimensions

Verified:

- `EuclideanDimension` admits exactly natural dimensions one through four.
- The four named dimensions have spatial arithmetic `0`, `1`, `2`, and `3` respectively, without
  asserting reconstruction.
- Mathlib Euclidean spacetime carriers have the declared real finrank.
- Hostile probes reject zero, values above four, equality of dimensions two and four, and a linear
  equivalence between their spacetime carriers.
- The complete build imports the production module and probes before running the kernel axiom
  audit.

## 2026-07-17 — second mathematical stone: signatures

Verified:

- A coordinate-vector carrier is introduced without silently selecting a metric or topology.
- The positive Euclidean sum-of-squares form and mostly-minus Minkowski form are separate
  dimension-indexed declarations.
- Coordinate zero has positive Minkowski weight; every available spatial basis direction has
  negative weight.
- The Euclidean form is nonnegative.
- In dimension one the algebraic forms agree because no spatial coordinate exists; this is not
  presented as equivalence of Euclidean and Minkowski theories.
- From dimension two onward the forms are proved unequal, with dedicated 2D and 4D hostile probes.
- No group action, analytic continuation, or reconstruction claim is introduced.

## 2026-07-17 — third mathematical stone: Lie-algebra simplicity

Verified:

- The project adopts Mathlib's existing `LieAlgebra.IsSimple` rather than inventing a competing
  meaning of “simple.”
- A proved source-facing equivalence exposes its two requirements: every Lie ideal is zero or whole,
  and the bracket is non-abelian.
- Derived theorems and hostile probes reject abelian and subsingleton carriers and proper nonzero
  ideals.
- This reusable layer makes no claim that a group is compact, connected, smooth, or physically
  admissible.

## 2026-07-17 — fourth mathematical stone: compact-simple gauge-group semantics

Verified:

- `CompactSimpleGaugeGroupData G E` preserves the actual carrier `G` and requires a
  finite-dimensional real smooth Lie-group model without replacing `G` by a universal cover.
- Hausdorff and second-countable manifold conventions, topological compactness, connectedness,
  carrier nontriviality, and tangent-Lie-algebra simplicity are explicit.
- The `C∞`-to-`GroupLieAlgebra` regularity/completeness bridge is implemented from Mathlib rather
  than hidden as an axiom.
- Hostile probes independently reject noncompact, disconnected, subsingleton, abelian-tangent, and
  proper-nonzero-ideal mutations.
- Connectedness is labelled as a project strengthening of the terse Clay wording; abstract-group
  simplicity and simple connectedness are not imposed.

## 2026-07-17 — gauge-geometry provenance stone

Verified:

- Daniel Freed's versioned `hep-th/9206021v1` PDF and reproducible Poppler text extraction are
  pinned and hashed.
- Printed pp. 6–9, §1 supply exact locators for principal bundles, gauge transformations,
  connection forms, curvature, Bianchi identity, and gauge covariance.
- The ledger confines this Chern–Simons paper to its general connection-geometry review and does
  not use it as evidence for Yang–Mills existence, action semantics, or a mass gap.
- No geometry declaration was added merely because the source is now available.

## 2026-07-17 — fifth mathematical stone: fiberwise principal torsors

Verified:

- `PrincipalBundleTorsorData G B P` stores one projection and one right action, avoiding unrelated
  action/projection witnesses.
- Every base point has a fiber, fibers are exactly right-action orbits, and the solving group
  element between two points in one fiber is unique.
- Surjectivity, transitivity, freeness, and the set-level orbit/fiber equivalence are derived.
- The product family `B × G → B` supplies a concrete trivial-torsor constructor.
- Hostile probes reject empty total carriers over nonempty bases, missing fibers, base-moving and
  law-breaking actions, nonidentity stabilizers, and nontransitive fibers.
- The module and ledger explicitly deny that this algebraic core supplies topology or smooth local
  triviality.

## 2026-07-17 — sixth mathematical stone: algebraic bundle maps and gauge automorphisms

Verified:

- `PrincipalBundleTorsorMap` couples one base map to one total map and requires projection
  compatibility and right-action equivariance.
- Identity and composition are defined with named evaluation laws and positive probes; same-fiber
  points map to same-fiber points.
- `TorsorGaugeTransformation` is an actual total-space equivalence over the identity base map, not
  an arbitrary endomorphism.
- Gauge transformations carry a proved group structure with identity, composition, inverse, and
  pointwise evaluation laws; an explicit forgetful bridge produces their underlying bundle map.
- Hostile probes reject projection mismatch, failed equivariance, base movement, and noninjective
  gauge candidates; identity and inverse probes give positive consistency evidence.
- Every name and ledger row labels this as algebraic: no smooth gauge transformation is claimed.

## 2026-07-17 — seventh mathematical stone: topological principal bundles

Verified:

- `PrincipalBundleLocalTrivialization` is an open partial homeomorphism to `baseSet × G` whose
  source is exactly the projection preimage and whose coordinates preserve projection and right
  multiplication.
- `TopologicalPrincipalBundleData` requires continuous projection/action and a designated atlas
  with a selected chart covering every base point.
- Selected chart sources are proved to cover the entire total carrier, and right action preserves
  each applicable chart source.
- The global product `B × G → B` gives a concrete topological principal-bundle constructor for any
  topological group.
- Hostile probes independently reject discontinuity, selected charts outside the designated atlas,
  missing coverage, malformed source/target sets, and failed local equivariance.
- No smooth chart compatibility, smooth gauge map, connection, or curvature is inferred.

Not yet achieved:

- No concrete inhabitant of the gauge-group certificate has been constructed. Mathlib's algebraic
  `SU(n)` API does not supply the complete manifold/compactness/connectedness/tangent-simplicity
  chain, so positive consistency infrastructure remains open.
- No smooth principal-bundle compatibility layer, smooth gauge transformation, connection,
  curvature, symmetry-group, quantum-theory, acceptance, existence, or mass-gap declaration exists.
- No Yang–Mills acceptance declaration exists.
- No standalone Git remote exists or has been pushed. The tested candidate
  `git@github.com:elmismisimoxhunca/lean-yangmills-adaly.git` does not exist, and the available SSH
  credential was scoped to the retired repository. Local commits can proceed; remote publication
  remains an explicit infrastructure blocker.
- Clay, Hall, Aharony–Seiberg–Tachikawa, and Freed artifacts are pinned. Yang–Mills action,
  OS/Wightman, spectral, observable, and lattice sources remain to be independently acquired and
  verified before their corresponding declarations become canonical.

The absence of an acceptance declaration is intentional: no placeholder theorem or arbitrary
structure is introduced merely to make the project appear advanced.
