/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Measure.WithDensity
import YangMills.Mathematics.UnitaryMatrixDualTrivialHeatNormalization

/-!
# Explicit positivity debt for the candidate Casimir spectral series

The spectral construction and geometric bridge now conditionally provide convergence, the
convolution law, a heat equation, and normalized-Haar mass one, but none of those statements proves
that the character sum is real or positive pointwise. This file records exactly that remaining gap
as uninhabited `UnitaryMatrixDualCasimirHeatPositivityData`:

* the imaginary part of every positive-time value is zero;
* the real part is strictly positive.

From these fields it constructs a continuous strictly positive real density and its `ENNReal`
version. Combined with the still-uninhabited geometric bridge, normalized-Haar mass one promotes the
`ENNReal` density to a probability measure via `Measure.withDensity`.

No positivity datum is constructed. No time-zero identity, Brownian identification, or heat-kernel
status is claimed.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]

/-- Exact remaining real-valuedness and strict pointwise positivity obligations for the candidate
spectral family. This is caller-supplied uninhabited data. -/
structure UnitaryMatrixDualCasimirHeatPositivityData
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) where
  value_im_zero : ∀ (t : ℝ), 0 < t → ∀ g : G,
    (unitaryMatrixDualCasimirHeatCharacterSeries data t g).im = 0
  value_re_pos : ∀ (t : ℝ), 0 < t → ∀ g : G,
    0 < (unitaryMatrixDualCasimirHeatCharacterSeries data t g).re

/-- Real part of the candidate spectral family. -/
noncomputable def unitaryMatrixDualCasimirHeatDensityReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (g : G) : ℝ :=
  (unitaryMatrixDualCasimirHeatCharacterSeries data t g).re

/-- `ENNReal` density obtained from the real part of the candidate spectral family. -/
noncomputable def unitaryMatrixDualCasimirHeatDensityENNReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (g : G) : ENNReal :=
  ENNReal.ofReal (unitaryMatrixDualCasimirHeatDensityReal data t g)

omit [CompactSpace G] in
/-- The real-part density is continuous. -/
theorem continuous_unitaryMatrixDualCasimirHeatDensityReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) (t : ℝ) :
    Continuous (unitaryMatrixDualCasimirHeatDensityReal data t) := by
  unfold unitaryMatrixDualCasimirHeatDensityReal
  fun_prop

omit [CompactSpace G] in
/-- Under the explicit real-valuedness field, the complex spectral value is exactly the coercion of
its real-part density. -/
theorem unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t g =
      (unitaryMatrixDualCasimirHeatDensityReal data t g : ℂ) := by
  apply Complex.ext
  · rfl
  · simp [unitaryMatrixDualCasimirHeatDensityReal, positivity.value_im_zero t ht g]

omit [CompactSpace G] in
/-- The real density is strictly positive at every positive time and point. -/
theorem unitaryMatrixDualCasimirHeatDensityReal_pos
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t) (g : G) :
    0 < unitaryMatrixDualCasimirHeatDensityReal data t g :=
  positivity.value_re_pos t ht g

omit [CompactSpace G] in
/-- The associated `ENNReal` density is measurable. -/
theorem measurable_unitaryMatrixDualCasimirHeatDensityENNReal
    [MeasurableSpace G] [BorelSpace G]
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G)) (t : ℝ) :
    Measurable (unitaryMatrixDualCasimirHeatDensityENNReal data t) := by
  unfold unitaryMatrixDualCasimirHeatDensityENNReal
  exact (continuous_unitaryMatrixDualCasimirHeatDensityReal data t).measurable.ennreal_ofReal

omit [CompactSpace G] in
/-- The `ENNReal` density is strictly positive. -/
theorem unitaryMatrixDualCasimirHeatDensityENNReal_pos
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {t : ℝ} (ht : 0 < t) (g : G) :
    0 < unitaryMatrixDualCasimirHeatDensityENNReal data t g := by
  rw [unitaryMatrixDualCasimirHeatDensityENNReal, ENNReal.ofReal_pos]
  exact positivity.value_re_pos t ht g

variable [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The real density inherits conjugation centrality from the uniformly summed character series. -/
theorem unitaryMatrixDualCasimirHeatDensityReal_central
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g k : G) :
    unitaryMatrixDualCasimirHeatDensityReal data t (k * g * k⁻¹) =
      unitaryMatrixDualCasimirHeatDensityReal data t g := by
  exact congrArg Complex.re
    ((unitaryMatrixDualCasimirHeatCentralCharacterSeries data t ht).property g k)

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}

/-- The real-part density has normalized Haar integral one under the geometric bridge. Positivity is
not needed for this real integral identity. -/
theorem normalizedCompactHaar_integral_casimirHeatDensityReal
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    (∫ g, unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = 1 := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have hi : Integrable
      (fun g => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g) μ := by
    have hc : Continuous
        (fun g => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g) := by
      fun_prop
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  rw [show (∫ g, unitaryMatrixDualCasimirHeatDensityReal heatTraceData t g ∂μ) =
      Complex.re (∫ g, unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t g ∂μ) by
    exact integral_re hi]
  rw [normalizedCompactHaar_integral_casimirHeatCharacterSeries bridge ht]
  norm_num

/-- Under explicit strict positivity, the `ENNReal` density also has normalized Haar lintegral one. -/
theorem normalizedCompactHaar_lintegral_casimirHeatDensityENNReal
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ g, unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t g
      ∂normalizedCompactHaarMeasure G) = 1 := by
  unfold unitaryMatrixDualCasimirHeatDensityENNReal
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [normalizedCompactHaar_integral_casimirHeatDensityReal bridge ht]
    norm_num
  · let μ := normalizedCompactHaarMeasure G
    letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
    have hc := continuous_unitaryMatrixDualCasimirHeatDensityReal heatTraceData t
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  · filter_upwards [] with g
    exact (positivity.value_re_pos t ht g).le

/-- Positive-time probability measure defined by the conditional positive spectral density relative
to normalized Haar measure. -/
noncomputable def unitaryMatrixDualCasimirHeatProbabilityMeasure
    (heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) : Measure G :=
  (normalizedCompactHaarMeasure G).withDensity
    (unitaryMatrixDualCasimirHeatDensityENNReal heatTraceData t)

/-- The conditional positive spectral measure has total mass one. -/
theorem unitaryMatrixDualCasimirHeatProbabilityMeasure_univ
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData)
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData heatTraceData)
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatProbabilityMeasure heatTraceData t Set.univ = 1 := by
  rw [unitaryMatrixDualCasimirHeatProbabilityMeasure,
    withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using
    normalizedCompactHaar_lintegral_casimirHeatDensityENNReal bridge positivity ht

end

end Mathematics
end YangMills
