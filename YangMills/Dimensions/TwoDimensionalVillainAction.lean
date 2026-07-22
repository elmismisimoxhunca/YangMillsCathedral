/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence
import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator

/-!
# Driver Villain plaquette action

Driver Definition 8.3 defines the Villain action at lattice spacing `ε` as the convolution heat
kernel `Q_{ε²}` for `exp(t Δ / 2)`, with Driver's Definition 4.7 invariant Laplacian. This module
requires the project's unchanged normalized convolution-semigroup density, its weak identity limit,
its smooth strictly-positive real representative, its exact `∂ₜQ = 1/2 ΔQ` equation for that same
Definition 4.7 operator, and an initial-identity generated operator semigroup satisfying Driver's
displayed convolution-kernel identity. The action is the real representative at `ε²`; its `ENNReal`
bridge is
used only to construct the normalized single-plaquette Haar-density measure.

No lattice Gibbs field, infinite-volume measure, approximating sequence inhabitant, convergence,
Yang--Mills theory, or mass gap is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}

/-- Driver's positive plaquette-area parameter `ε²`. -/
def twoDimensionalVillainTime (spacing : PositiveLatticeSpacing) : ℝ :=
  spacing.1 ^ 2

/-- Driver Definition 8.3: the real Villain action is the unchanged heat density `Q_{ε²}`. -/
def twoDimensionalVillainAction
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) : G → ℝ :=
  heat.densityReal (twoDimensionalVillainTime spacing)

/-- The normalized single-plaquette Villain measure relative to canonical Haar probability. -/
def twoDimensionalVillainPlaquetteMeasure
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) : Measure G :=
  (normalizedCompactHaarMeasure G).withDensity
    (fun g => ENNReal.ofReal (twoDimensionalVillainAction heat _kernel spacing g))

namespace TwoDimensionalVillainAction

/-- Positive spacing gives strictly positive Villain time. -/
theorem time_pos (spacing : PositiveLatticeSpacing) :
    0 < twoDimensionalVillainTime spacing := by
  exact sq_pos_of_pos spacing.2

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The real action and the unchanged semigroup density agree through the exact `ENNReal` bridge. -/
theorem action_toENNReal
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) (g : G) :
    ENNReal.ofReal (twoDimensionalVillainAction heat _kernel spacing g) =
      law.selectedAreaDensity (twoDimensionalVillainTime spacing) g :=
  heat.densityReal_toENNReal _ (time_pos spacing) g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Driver's action is smooth, hence continuous. -/
theorem action_continuous
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) :
    Continuous (twoDimensionalVillainAction heat _kernel spacing) :=
  (heat.densityReal_spatialSmooth _ (time_pos spacing)).continuous

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Driver's action is strictly positive. -/
theorem action_pos
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) (g : G) :
    0 < twoDimensionalVillainAction heat _kernel spacing g :=
  heat.densityReal_pos _ (time_pos spacing) g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The Villain action is a conjugation-class function. -/
theorem action_central
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) (h g : G) :
    twoDimensionalVillainAction heat _kernel spacing (h * g * h⁻¹) =
      twoDimensionalVillainAction heat _kernel spacing g :=
  heat.densityReal_central _ (time_pos spacing) h g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The Villain action is invariant under orientation reversal. -/
theorem action_inv
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalVillainAction heat _kernel spacing g⁻¹ =
      twoDimensionalVillainAction heat _kernel spacing g :=
  heat.densityReal_inv _ (time_pos spacing) g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Continuity on the compact gauge group makes the real action integrable against Haar. -/
theorem action_integrable
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) :
    Integrable (twoDimensionalVillainAction heat _kernel spacing)
      (normalizedCompactHaarMeasure G) := by
  constructor
  · exact (action_continuous heat _kernel spacing).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun g => (action_pos heat _kernel spacing g).le)]
    have hdensity :
        (fun g => ENNReal.ofReal (twoDimensionalVillainAction heat _kernel spacing g)) =
          law.selectedAreaDensity (twoDimensionalVillainTime spacing) := by
      funext g
      exact action_toENNReal heat _kernel spacing g
    rw [hdensity, semigroup.density_lintegral_normalized _ (time_pos spacing)]
    exact ENNReal.one_lt_top

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Semigroup normalization makes every single-plaquette Villain measure a probability measure. -/
theorem plaquetteMeasure_univ
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalVillainPlaquetteMeasure heat _kernel spacing univ = 1 := by
  change ((normalizedCompactHaarMeasure G).withDensity
    (fun g => ENNReal.ofReal (heat.densityReal (twoDimensionalVillainTime spacing) g))) univ = 1
  have hdensity :
      (fun g => ENNReal.ofReal
        (heat.densityReal (twoDimensionalVillainTime spacing) g)) =
        law.selectedAreaDensity (twoDimensionalVillainTime spacing) := by
    funext g
    exact heat.densityReal_toENNReal _ (time_pos spacing) g
  rw [hdensity]
  exact semigroup.densityMeasure_univ_of_pos
    (twoDimensionalVillainTime spacing) (time_pos spacing)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Driver Definition 7.1's normalization is stated on the real action itself. -/
theorem action_integral_normalized
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) :
    ∫ g, twoDimensionalVillainAction heat _kernel spacing g
      ∂normalizedCompactHaarMeasure G = 1 := by
  have hlintegral :
      ∫⁻ g, ENNReal.ofReal (twoDimensionalVillainAction heat _kernel spacing g)
        ∂normalizedCompactHaarMeasure G = 1 := by
    have hdensity :
        (fun g => ENNReal.ofReal (twoDimensionalVillainAction heat _kernel spacing g)) =
          law.selectedAreaDensity (twoDimensionalVillainTime spacing) := by
      funext g
      exact action_toENNReal heat _kernel spacing g
    rw [hdensity]
    exact semigroup.density_lintegral_normalized _ (time_pos spacing)
  have hofReal : ENNReal.ofReal
      (∫ g, twoDimensionalVillainAction heat _kernel spacing g
        ∂normalizedCompactHaarMeasure G) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (action_integrable heat _kernel spacing)
      (Filter.Eventually.of_forall fun g => (action_pos heat _kernel spacing g).le)]
    exact hlintegral
  have hintegral_nonneg : 0 ≤
      ∫ g, twoDimensionalVillainAction heat _kernel spacing g
        ∂normalizedCompactHaarMeasure G :=
    integral_nonneg fun g => (action_pos heat _kernel spacing g).le
  have := congrArg ENNReal.toReal hofReal
  simpa [ENNReal.toReal_ofReal hintegral_nonneg] using this

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Every normalized Villain plaquette measure is nonzero. -/
theorem plaquetteMeasure_ne_zero
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (_kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)
    (spacing : PositiveLatticeSpacing) :
    twoDimensionalVillainPlaquetteMeasure heat _kernel spacing ≠ 0 := by
  intro hzero
  have h := plaquetteMeasure_univ heat _kernel spacing
  rw [hzero] at h
  simp at h

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The action's time derivative is exactly Driver's `1/2 Δ` at every positive time, exposing the
source-critical Definition 4.7 heat-kernel chain rather than merely a central density. -/
theorem hasDerivAt_heatDensity
    (heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => heat.densityReal s g)
      ((1 / 2 : ℝ) * laplacian.laplacian (heat.smoothDensityAt t ht) g) t :=
  heat.hasDerivAt_densityReal t ht g

end TwoDimensionalVillainAction

end

end YangMills.Dimensions
