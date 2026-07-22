/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopBrownianRealization

/-!
# Hostile probes for the selected-loop Brownian realization

The probes expose probability normalization, identity start, continuous paths, exact stationary
right-increment laws, mutual finite increment independence, derived marginals, and exact selected-
area coherence with the sampled loop holonomy. No process or theory is constructed.
-/

namespace YangMills.Dimensions.TwoDimensionalSelectedLoopBrownianRealization.Probes

open MeasureTheory ProbabilityTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

variable
    {E G Gauge Sample Connection Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    [Group Gauge] [MeasurableSpace Sample] [MeasurableSpace Ω]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian}

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The exact process law is probability normalized, not merely nonzero. -/
theorem exact_process_probability_normalization
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    brownian.probabilityMeasure Set.univ = 1 :=
  brownian.probability_normalized

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Probability normalization blocks a zero process law. -/
theorem zero_process_measure_blocked
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (claimed : brownian.probabilityMeasure = 0) : False :=
  brownian.probabilityMeasure_ne_zero claimed

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every fixed-time coordinate is measurable under the exact process carrier. -/
theorem exact_fixed_time_measurability
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (t : NNReal) : Measurable (brownian.process t) :=
  brownian.process_measurable t

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The process starts at the exact group identity almost surely. -/
theorem exact_identity_start
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    {samplePoint | brownian.process 0 samplePoint = 1} ∈
      ae brownian.probabilityMeasure :=
  brownian.process_zero

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Path continuity concerns the same process and probability law. -/
theorem exact_continuous_paths
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    {samplePoint | Continuous (fun t => brownian.process t samplePoint)} ∈
      ae brownian.probabilityMeasure :=
  brownian.continuous_paths

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- A measurable null hull supports an everywhere-continuous, jointly measurable modification
that agrees with the original process at every time simultaneously almost surely. -/
theorem exact_jointly_measurable_continuous_modification
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    MeasurableSet brownian.pathDiscontinuityHull ∧
      brownian.probabilityMeasure brownian.pathDiscontinuityHull = 0 ∧
      (∀ samplePoint, Continuous
        (fun t => brownian.jointlyMeasurableProcess t samplePoint)) ∧
      Measurable (Function.uncurry brownian.jointlyMeasurableProcess) ∧
      ∀ᵐ samplePoint ∂brownian.probabilityMeasure,
        ∀ t, brownian.jointlyMeasurableProcess t samplePoint = brownian.process t samplePoint :=
  ⟨measurableSet_toMeasurable _ _, brownian.pathDiscontinuityHull_null,
    brownian.jointlyMeasurableProcess_continuous,
    brownian.jointlyMeasurableProcess_measurable,
    brownian.jointlyMeasurableProcess_ae_eq⟩

omit [FiniteDimensional ℝ E] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Joint nonmeasurability of the derived continuous modification is hostilely rejected. -/
theorem joint_nonmeasurability_blocked
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (wrong : ¬Measurable (Function.uncurry brownian.jointlyMeasurableProcess)) : False :=
  wrong brownian.jointlyMeasurableProcess_measurable

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The modification preserves every fixed-time law exactly. -/
theorem exact_modified_fixed_time_law
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) (t : NNReal) :
    Measure.map (brownian.jointlyMeasurableProcess t) brownian.probabilityMeasure =
      Measure.map (brownian.process t) brownian.probabilityMeasure :=
  brownian.jointlyMeasurableProcess_map_eq t

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- The modified process retains the exact positive stationary right-increment law. -/
theorem exact_modified_stationary_increment_law
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (s t : NNReal) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (brownian.jointlyMeasurableProcess s samplePoint)⁻¹ *
        brownian.jointlyMeasurableProcess (s + t) samplePoint) brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)) :=
  brownian.jointlyMeasurableProcess_stationary_increment_law s t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every positive stationary right increment has the unchanged density law. -/
theorem exact_stationary_increment_law
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (s t : NNReal) (ht : 0 < t) :
    Measure.map (fun samplePoint =>
      (brownian.process s samplePoint)⁻¹ * brownian.process (s + t) samplePoint)
      brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)) :=
  brownian.stationary_increment_law s t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- Mutual independence retains every finite monotone family and the exact right-increment order. -/
theorem exact_independent_increments
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (n : ℕ) (t : Fin (n + 1) → NNReal) (ht : Monotone t) :
    iIndepFun
      (fun (i : Fin n) samplePoint =>
        (brownian.process (t i.castSucc) samplePoint)⁻¹ *
          brownian.process (t i.succ) samplePoint)
      brownian.probabilityMeasure :=
  brownian.independent_increments n t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- One-time marginals are derived from identity start and stationary increments. -/
theorem exact_derived_marginal
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (t : NNReal) (ht : 0 < t) :
    Measure.map (brownian.process t) brownian.probabilityMeasure =
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)) :=
  brownian.marginal_law t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- At the selected area, the process and exact sampled loop holonomy have one law. -/
theorem exact_selected_area_coherence
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω) :
    Measure.map
        (brownian.process
          (TwoDimensionalSelectedLoopBrownianRealizationData.selectedAreaTime (law := law)))
        brownian.probabilityMeasure =
      Measure.map
        (fun samplePoint =>
          base.holonomy law.selectedLoop (base.sampleConnection samplePoint))
        base.probabilityMeasure :=
  brownian.selectedArea_marginal_eq_sampledLoopLaw

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [MeasurableMul₂ G] [MeasurableInv G] in
/-- A changed positive-time marginal is rejected. -/
theorem changed_marginal_blocked
    (brownian : TwoDimensionalSelectedLoopBrownianRealizationData
      inner law semigroup laplacian heat Ω)
    (t : NNReal) (ht : 0 < t) (wrong : Measure G)
    (different : wrong ≠
      (normalizedCompactHaarMeasure G).withDensity
        (law.selectedAreaDensity (t : ℝ)))
    (claimed : Measure.map (brownian.process t) brownian.probabilityMeasure = wrong) : False := by
  apply different
  rw [← claimed]
  exact brownian.marginal_law t ht

/-- This lower-dimensional process cannot change the Clay endpoint index. -/
theorem brownian_realization_cannot_be_four :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSelectedLoopBrownianRealization.Probes
