# Architecture

## Mission boundary

The repository defines a type-checked acceptance surface for proposed Yang–Mills theories. An
inhabitant of the final four-dimensional contract would still require the open mathematics. This
repository neither provides nor assumes such an inhabitant.

## Dependency direction

```text
Foundation.Dimensions
Foundation.Signatures
        ↓
Geometry.LieGroup
Geometry.PrincipalBundle
Geometry.Connection
Geometry.Curvature
        ↓
Classical.Action
Observables.GaugeInvariant
        ↓
Euclidean.OSData ───────────────────────┐
Lattice.Regulator -optional→ Continuum ─┤
                                ├→ Reconstruction.Coherence
Minkowski.Poincare ─────────────┤
Minkowski.WightmanData ─────────┘
        ↓
Spectral.Translations
Spectral.MassGap
        ↓
Dimension.One / Two / Three / Four
        ↓
Clay.Acceptance
```

Imports must follow this direction. In particular, foundational geometry must not import a quantum
acceptance record, and the canonical continuum contract must not require a lattice witness.

## Layer law

Every layer distinguishes:

1. **definitions**—mathematical meanings built from earlier layers;
2. **requirements**—fields a proposed model must prove;
3. **derived theorems**—Lean proofs following from definitions and requirements;
4. **bridges**—explicit compatibility between independently meaningful surfaces;
5. **specification debt**—named missing infrastructure that is not hidden in an arbitrary
   proposition.

## Dimension law

The following is a provisional architectural decision, not yet a canonical Lean interface. Its
source rows must be completed before the corresponding declarations are introduced.

The common core is indexed by Euclidean spacetime dimension. Supported public dimensions are
`1 ≤ d ≤ 4`. OS reconstruction, when available, selects one Euclidean coordinate as time and
produces `(d - 1) + 1` Minkowski spacetime.

- `d = 1`: local curvature vanishes for degree reasons; global holonomy may remain.
- `d = 2`: exact/constructive models provide consistency evidence.
- `d = 3`: genuine lower-dimensional continuum contract, not a solved proxy for 4D.
- `d = 4`: candidate acceptance surface that must retain every pinned Clay §4 obligation.

There is no coercion from a lower-dimensional model to the four-dimensional contract.

## Replacement policy

Legacy `ClayStatement` declarations may be integrated only declaration by declaration. The import
record must state the original legacy locator, primary source, discovered defect, repair, and new
hostile probe. No legacy solution module is an allowed dependency.

The removed `LeanMillenniumPrizeProblems` clone is not an implementation dependency. Its audit is
historical evidence only.

## Validation gates

Every commit must pass, as applicable:

```bash
lake env lean <changed module>
lake build
python3 scripts/verify_sources.py
python3 scripts/verify_audit_bibliography.py
python3 scripts/audit_lean.py
git diff --check
```

`YangMills.lean` invokes the kernel-level namespace audit after all production imports. The Python
scan is deliberately conservative defense in depth; the `Lean.collectAxioms` audit is the semantic
gate for generated or indirect `sorryAx` dependencies and project-defined axioms.

A green build proves elaboration and kernel checking only. Source fidelity and adversarial probes
are separate acceptance gates.
