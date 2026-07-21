/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalRepresentationInducedPairing

/-!
# Probes for Driver's representation-induced pairing
-/

namespace YangMills.Dimensions.TwoDimensionalRepresentationInducedPairing.Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Driver's `p_*` is the exact manifold derivative of the stored representation at identity. -/
theorem exact_representation_differential
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    representation.differential =
      mfderiv (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ
          (Fin representation.dimension → Fin representation.dimension → ℂ))
        (fun g i j => representation.representation g i j) (1 : G) :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Injectivity is attached to that exact differential, not an unrelated linear map. -/
theorem exact_differential_injective
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    Function.Injective representation.differential :=
  representation.differential_injective_exact

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The continuum inner product is exactly `-Re tr(p_*X p_*Y)` for the same representation. -/
theorem exact_trace_pairing
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (coherence : TwoDimensionalRepresentationInducedPairingCoherenceData representation inner)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    inner.pairing first second =
      -(Matrix.trace
        (representation.differential first * representation.differential second)).re :=
  coherence.pairing_eq_trace first second

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- A nonzero Lie-algebra direction cannot collapse under `p_*`. -/
theorem collapsed_nonzero_direction_blocked
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (direction : GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
    (nonzero : direction ≠ 0)
    (collapsed : representation.differential direction = 0) : False := by
  apply nonzero
  apply representation.differential_injective_exact
  simpa using collapsed

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- An unrelated inner product value is hostilely rejected by exact trace coherence. -/
theorem unrelated_pairing_blocked
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (coherence : TwoDimensionalRepresentationInducedPairingCoherenceData representation inner)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
    (claimed : inner.pairing first second ≠
      twoDimensionalRepresentationTracePairing representation first second) : False :=
  claimed (coherence.pairing_eq_trace first second)

end

end YangMills.Dimensions.TwoDimensionalRepresentationInducedPairing.Probes
