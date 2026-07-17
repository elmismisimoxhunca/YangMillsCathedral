# Construction roadmap

This roadmap is a goal sequence, not a claim of current completion. Every stone is reviewed and
committed before higher layers depend on it.

## Phase 0 — independent foundation

- [x] Initialize a standalone Lean/Mathlib project.
- [x] Pin and verify the Clay/Jaffe–Witten source artifact.
- [x] Record the no-solution mission, provenance law and dependency architecture.
- [ ] Establish a writable standalone remote.
- [x] Add declaration-level source and legacy-integration ledgers.

## Phase 1 — dimensions and signatures

- [x] Define Euclidean spacetime dimensions `1 ≤ d ≤ 4`.
- [x] Define spatial dimension as `d - 1` only in reconstruction contexts.
- [x] Define Euclidean and Minkowski quadratic forms without identifying them or asserting reconstruction.
- [x] Add hostile probes for out-of-range and dimension-confused witnesses.

## Phase 2 — gauge geometry

- [x] Pin authoritative Lie-algebra simplicity and gauge-global-form sources.
- [x] Pin authoritative principal-bundle, connection and curvature sources.
- [x] Define compact-simple Lie-group semantics and global-form policy.
- [x] Adopt and source-map Mathlib's ideal/non-abelian Lie-algebra simplicity interface.
- [x] Define and probe the reusable fiberwise torsor core (not a full principal bundle).
- [x] Define algebraic bundle maps and gauge automorphisms (smoothness still pending).
- [x] Define and probe topological equivariant local trivializations.
- [x] Define and probe smooth principal-bundle compatibility.
- [x] Package quotient-map and smooth overlap-transition theorems.
- [x] Define and probe smooth gauge transformations.
- [x] Define and probe the Lie-group adjoint action needed by connection equivariance.
- [x] Define and probe typed pointwise manifold differential forms and pullback.
- [x] Define and probe pointwise principal connection normalization/equivariance.
- [x] Add and probe local smooth-section regularity for differential forms.
- [x] Promote the pointwise form to a smooth principal connection definition.
- [x] Add continuous and smooth wedge/bracket infrastructure.
- [ ] Add arbitrary-manifold exterior-derivative certification and define curvature.
- [ ] Prove structural curvature and gauge-covariance results.

## Phase 3 — classical Yang–Mills semantics

- [ ] Define the invariant inner product and Euclidean action from curvature.
- [ ] Interpret gauge-invariant local curvature polynomials and covariant derivatives.
- [ ] Separate local observables from nonlocal Wilson observables.
- [ ] Add nontrivial positive examples and hostile disconnected-curvature probes.

## Phase 4 — Euclidean and Minkowski quantum surfaces

- [ ] Pin OS-I, OS-II, Wightman and correcting sources with verified locators.
- [ ] Define OS-II-strength Euclidean/Schwinger data.
- [ ] Define proper-orthochronous Poincaré and Wightman data independently.
- [ ] Define common invariant domains and operator-valued tempered distributions.
- [ ] Add explicit OS reconstruction and correlator coherence.

## Phase 5 — translations and mass gap

- [ ] Build or package a genuine joint projection-valued-measure interface.
- [ ] Tie energy and momentum to one strongly continuous translation representation.
- [ ] Define forward-cone support, vacuum sector and invariant mass.
- [ ] Derive Hamiltonian-only gap views under explicit bridge hypotheses.
- [ ] Reject bounded, empty, full and unrelated spectral witnesses.

## Phase 6 — optional lattice route

- [ ] Pin Wilson and Osterwalder–Seiler primary sources.
- [ ] Define dimension-indexed lattice regulators and Wilson action semantics.
- [ ] Define scaling, renormalization, observable and continuum-limit bridges.
- [ ] Keep finite-cutoff reflection positivity distinct from continuum OS data.

## Phase 7 — dimension contracts and final checker

- [ ] Add the degenerate/topological `d = 1` boundary contract.
- [ ] Add rigorous `d = 2` consistency models.
- [ ] Add a nontrivial but uninhabited `d = 3` continuum acceptance contract.
- [ ] Add the full `d = 4` Clay acceptance contract.
- [ ] Prove that no lower-dimensional witness is silently accepted as 4D.
- [ ] Publish the final acceptance proposition without asserting an inhabitant.

## Per-commit gates

```bash
lake env lean <changed-module>
lake build
python3 scripts/verify_sources.py
python3 scripts/audit_lean.py
git diff --check
git status --short
```

A phase is complete only when its source map, definitions, derived theorems, bridges, hostile
probes, build evidence and axiom audit are all present.
