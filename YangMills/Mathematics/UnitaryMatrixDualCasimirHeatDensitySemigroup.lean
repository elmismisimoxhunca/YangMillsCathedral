/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.NormalizedCompactHaarDensitySemigroup
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatPositiveSemigroup

/-!
# Conditional normalized density semigroup from the Casimir spectral family

The preceding Fourier modules separately prove measurability, centrality, inversion symmetry,
normalization, convolution addition, and weak convergence to the identity for the candidate Casimir
spectral density. This file assembles those results into the reusable source-neutral
`NormalizedCompactHaarDensitySemigroupData` interface.

The construction remains conditional on the explicit heat-trace summability, Casimir/Laplacian
bridge, strict positivity, and weak initial-identity witnesses. It constructs no one of those inputs
and does not identify the resulting semigroup with a geometric heat kernel unless an additional
Laplacian/heat-equation witness is retained.
-/

namespace YangMills.Mathematics

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uG uE

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
  {inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)}
  {laplacianData : RightInvariantPairingComplexLaplacianData inner}
  {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- Assemble the conditional positive Casimir spectral family into the generic normalized compact
Haar density-semigroup interface. Every field is derived from a separately named prior theorem. -/
noncomputable def unitaryMatrixDualCasimirHeatDensitySemigroupData
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    (initial : UnitaryMatrixDualCasimirHeatInitialIdentityData heatTraceData) :
    NormalizedCompactHaarDensitySemigroupData
      (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData) where
  density_measurable := fun t _ht =>
    measurable_unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t
  density_central := by
    intro t ht h g
    unfold unitaryMatrixDualCasimirHeatDensityENNReal
    rw [unitaryMatrixDualCasimirHeatDensityReal_central heatTraceData ht g h]
  density_inv := fun t ht g =>
    unitaryMatrixDualCasimirHeatDensityENNReal_inv heatTraceData ht g
  density_lintegral_normalized := fun t ht =>
    normalizedCompactHaar_lintegral_casimirHeatDensityENNReal bridge positivity ht
  density_add := fun s t hs ht g =>
    unitaryMatrixDualCasimirHeatDensityENNReal_add heatTraceData positivity hs ht g
  weak_tendsto_identity := fun f => by
    simpa [unitaryMatrixDualCasimirHeatProbabilityMeasure] using
      tendsto_integral_casimirHeatProbabilityMeasure_nhdsWithin_zero
        heatTraceData positivity initial f

end

end YangMills.Mathematics
