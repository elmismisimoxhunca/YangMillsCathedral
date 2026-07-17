# Yang–Mills Definition in Lean

This repository builds a source-traceable, machine-checked definition of **what a Yang–Mills theory
must satisfy**. It does not construct Yang–Mills theory, prove its existence, prove a mass gap, or
claim a solution to the Clay problem.

## Governing decision

The formalization is built from the ground up. The former `LeanMillenniumPrizeProblems`
implementation is not a dependency and its API is not preserved. The legacy Adaly
`ClayStatement` and hostile probes are archaeological input: useful ideas may be integrated only
after independent validation against primary literature.

**Papers are authoritative. Legacy is the quarry, not the cathedral.**

## Acceptance target

The pinned Clay/Jaffe–Witten source states on PDF p. 6, §4:

> Prove that for any compact simple gauge group G, a non-trivial quantum Yang–Mills theory exists
> on R4 and has a mass gap Δ > 0.

This headline is not the complete contract. The same section also requires gauge-invariant local
curvature fields, short-distance agreement with asymptotic freedom and perturbative
renormalization, a stress tensor, an operator-product expansion with prescribed singularities,
finite supremal mass, and axiomatic strength at least matching the cited Wightman and
Osterwalder–Schrader sources. This project formalizes the full contract a future construction would
have to inhabit. The final target will be a proposition, not a falsely inhabited theorem.

## Construction order

1. Euclidean dimensions and signatures;
2. compact-simple Lie-group semantics;
3. manifolds, principal bundles, gauge transformations, connections and curvature;
4. classical action and interpreted gauge-invariant observables;
5. Euclidean continuum and Osterwalder–Schrader data;
6. Minkowski/Wightman data and physical Poincaré symmetry;
7. joint translation spectral/PVM and mass-gap semantics;
8. explicit reconstruction and coherence bridges;
9. optional lattice-regulator and continuum-limit interfaces;
10. distinct contracts and consistency probes for Euclidean dimensions 1–4;
11. the four-dimensional Clay acceptance proposition.

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md), the goal sequence in
[`docs/ROADMAP.md`](docs/ROADMAP.md), the declaration-level
[`docs/SOURCE_MAP.md`](docs/SOURCE_MAP.md), and the evidence-only current state in
[`docs/STATUS.md`](docs/STATUS.md).

## Formalization laws

- New Lean source contains no `sorry` and introduces no project axioms.
- Every physical requirement has declaration-level provenance.
- Definitions, witness requirements, derived results, bridges and open specification debt remain
  visibly distinct.
- Euclidean dimension `d` means spacetime dimension; under OS reconstruction it corresponds to
  `(d - 1) + 1` Minkowski spacetime.
- Lower-dimensional theories test shared interfaces but never imply the 4D contract without an
  explicit theorem carrying every required hypothesis.
- Lattice models are regulators/construction interfaces, not silently continuum theories.
- Lean type correctness is necessary but does not establish physical adequacy.
- Every major interface receives positive consistency evidence where available and hostile probes
  against vacuous witnesses.

## Reproducible setup

Requirements: Git, `curl`, and `elan`. The project pins its Lean and Mathlib revisions.

```bash
lake build
python3 scripts/verify_sources.py
```

Source verification is independent of Lean compilation. Both gates are required.

## Repository layout

```text
YangMills/            Lean source
Sources/              pinned primary/authoritative source artifacts
scripts/              provenance and audit tools
docs/                 architecture, decisions and source maps
YangMills.lean        library root
lean-toolchain        pinned Lean release
lakefile.toml         pinned dependencies
```

## Current status

The standalone foundation, Euclidean dimension index, separate Euclidean/Minkowski quadratic
forms, source-facing Lie-algebra simplicity layer, and compact-connected-simple Lie-group
certificate type and semantics, the fiberwise torsor core, algebraic bundle maps/gauge
automorphisms, topological and smooth equivariant local trivializations, derived open-quotient
projection and smooth overlap-transition theorems, smooth gauge automorphisms, the Lie-group adjoint
action, a typed pointwise manifold differential-form carrier, local-model exterior derivative and
an arbitrary-manifold one-form Cartan certificate, a smoothly closed Lie-bracket wedge,
finite-dimensional tangent-bracket continuity/smoothness bridges, smooth differential-form
regularity, pointwise and smooth principal connection-form definitions, the derived principal
curvature formula, intrinsic curvature horizontality/right-adjoint-equivariance certificate semantics,
the adjoint associated-bundle orbit quotient with its quotient topology, base projection, and
representative-independent set-level local coordinates, and an explicit positive adjoint-invariant
Lie-algebra inner-product certificate are implemented. No
concrete gauge-group, connection, invariant-inner-product, curvature, or structure-certificate witness,
symmetry group, reconstruction bridge, quantum-theory witness, Yang–Mills existence claim, or
mass-gap claim is present.
