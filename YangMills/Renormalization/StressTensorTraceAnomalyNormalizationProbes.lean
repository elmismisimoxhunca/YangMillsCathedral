/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Renormalization.StressTensorTraceAnomalyNormalization

namespace YangMills.Renormalization.StressTensorTraceAnomalyNormalizationProbes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    {normalizedBeta : GroupNormalizedOneLoopBetaData inner freedom}
    {classicalCoupling : ℝ}
    {reference : ClassicalRunningCouplingReferenceData freedom classicalCoupling}
    (normalization : StressTensorTraceAnomalyNormalizationData normalizedBeta reference)

/-- The explicitly supplied project coefficient cannot collapse to zero. -/
theorem zero_coefficient_blocked
    (zero : normalization.coefficient = 0) : False :=
  normalization.coefficient_ne_zero zero

/-- A changed coefficient that violates the derived outer-coupling formula is rejected. -/
theorem changed_coefficient_normalization_blocked
    (changed : normalization.coefficient ≠
      freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) /
        (2 * freedom.runningCoupling reference.referenceLogScale ^ 3)) : False :=
  changed normalization.coefficient_eq_beta_div_two_mul_cube

/-- A changed source-to-project curvature-squared scale is rejected. -/
theorem changed_curvatureSquared_scale_blocked
    (changed : normalization.sourceToOuterCurvatureSquaredScale ≠
      1 / freedom.runningCoupling reference.referenceLogScale ^ 2) : False :=
  changed normalization.scale_eq_outerCoupling

/-- The exact normalized one-loop beta and exact classical reference remain in one chain. -/
theorem exact_normalizedBeta_reference_chain :
    freedom.leadingCoefficient =
        (11 * normalizedBeta.casimirNormalization.adjointCasimir) /
          (3 * (16 * Real.pi ^ 2)) ∧
      classicalCoupling = freedom.runningCoupling reference.referenceLogScale :=
  ⟨normalizedBeta.leadingCoefficient_eq, reference.coupling_eq_runningCoupling⟩

/-- At the positive reference coupling the project coefficient has exactly the beta-function sign. -/
theorem coefficient_sign_probe :
    normalization.coefficient < 0 ↔
      freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) < 0 :=
  normalization.coefficient_neg_iff_betaFunction_neg

end

end YangMills.Renormalization.StressTensorTraceAnomalyNormalizationProbes
