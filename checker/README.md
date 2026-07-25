# Standalone 3D SU(2) Yang--Mills plug-in checker

This directory is the bounded, independently buildable acceptance checker extracted from the larger
`YangMillsDefinition` research repository. It contains only the transitive project-module closure
needed by the exact three-dimensional SU(2) gate and its hostile probes.

It does **not** construct a Yang--Mills theory, prove continuum existence, perform a universal
Osterwalder--Schrader reconstruction, or prove a mass gap. The authoritative proposition remains
uninhabited unless a future candidate supplies every dependent witness.

## Authoritative API

- `ThreeDimensionalSU2GaugeGroupData`: exact continuously and multiplicatively identified matrix
  `SU(2)` gauge geometry.
- `ThreeDimensionalSU2ContinuumExistenceData`: classical `ℝ³` Yang--Mills data, nontrivial Wightman
  data, coherent gauge-invariant local observables, and nontrivial scalar `F²` identification.
- `ThreeDimensionalSU2SameTheoryData`: explicit strict Euclidean family and ordered Wick coherence
  with those same Minkowski correlators.
- `ThreeDimensionalSU2ExistenceMassGapAcceptanceData`: a positive physical gap with a nonzero
  excitation sector on that unchanged theory's joint translation PVM.
- `ThreeDimensionalSU2ExistenceMassGapAcceptance`: `Nonempty` of the strongest data.
- `ThreeDimensionalSU2PluginReport`: proof-carrying `PASS`, diagnostic `INCOMPLETE`, or certified
  `DIMENSION MISMATCH`.

See [`docs/THREE_DIMENSIONAL_SU2_PLUGIN_GUIDE.md`](docs/THREE_DIMENSIONAL_SU2_PLUGIN_GUIDE.md) for
the future-candidate adapter procedure.

## Independent build and audits

From this directory:

```bash
python3 scripts/verify_checker.py
python3 scripts/verify_sources.py
lake build YangMillsChecker
```

`verify_checker.py` checks that:

- every project import resolves inside this directory;
- `CHECKER_FILES.txt` is the exact source closure;
- no 2D, 4D, lattice, or renormalization research module entered the closure;
- the root imports the exact SU(2), strongest-gate, and plug-in probe surfaces;
- there are no `sorry`, `admit`, `sorryAx`, source symlinks, or project axiom declarations.

Mathlib is the only external Lean dependency and is pinned to `v4.31.0`.

## Scope boundary

A successful build establishes elaboration and audit coverage only. It is not evidence that the
acceptance proposition is inhabited. A failed candidate is **not established by that candidate**;
it is not thereby mathematically false.

The frozen 2D, unrestricted Peter--Weyl, broad multidimensional, lattice, and renormalization tracks
are intentionally absent from this standalone package.
