/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/


import YangMills.Renormalization.AdjointCasimirNormalization

/-!
# Trace-anomaly normalization bridge

Collins–Duncan–Joglekar 1977, §III, equations (3.19)–(3.21), use a convention with
coupling inside the field strength. This uninhabited bridge makes explicit the additional
renormalized-operator rescaling needed for the project's geometric curvature and outer
`(4g²)⁻¹` action convention. The `β(g)/(2g³)` expression is derived from supplied source and
rescaling equalities; it is not installed as a verbatim source formula or constructed theorem.
-/

namespace YangMills.Renormalization

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
    (normalizedBeta : GroupNormalizedOneLoopBetaData inner freedom)
    {classicalCoupling : ℝ}
    (reference : ClassicalRunningCouplingReferenceData freedom classicalCoupling)

/-- Supplied bridge from the CDJ source normalization to the project's outer-coupling
curvature-squared normalization. The exact group-normalized one-loop datum and exact classical
reference are parameters, so neither can be replaced by a disconnected beta function or scale. -/
structure StressTensorTraceAnomalyNormalizationData where
  /-- Exact coherence with the already supplied group/pairing-normalized one-loop datum. This is
  discharged by `normalizedBeta.leadingCoefficient_eq`; retaining it in the type prevents the
  normalization bridge from erasing or replacing that exact index. -/
  normalizedBeta_coherence : freedom.leadingCoefficient =
    (11 * normalizedBeta.casimirNormalization.adjointCasimir) /
      (3 * (16 * Real.pi ^ 2)) := normalizedBeta.leadingCoefficient_eq
  /-- Project coefficient after the supplied source-to-outer-curvature-squared rescaling. -/
  coefficient : ℝ
  /-- Anti-collapse is explicit acceptance data at the selected exact reference. -/
  coefficient_ne_zero : coefficient ≠ 0
  /-- Multiplicative conversion of the source-renormalized curvature-squared insertion into the
  project's exact outer-coupling curvature-squared operator convention. -/
  sourceToOuterCurvatureSquaredScale : ℝ
  /-- A collapsed conversion is forbidden. -/
  scale_ne_zero : sourceToOuterCurvatureSquaredScale ≠ 0
  /-- Source reduced-matrix-element convention before applying the project rescaling. -/
  coefficient_eq_sourceConvention :
    coefficient =
      freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) /
          (2 * freedom.runningCoupling reference.referenceLogScale) *
        sourceToOuterCurvatureSquaredScale
  /-- Explicit project bridge for an outer classical action coupling: the curvature-squared
  insertion is rescaled by `g⁻²` at the exact reference. -/
  scale_eq_outerCoupling :
    sourceToOuterCurvatureSquaredScale =
      1 / freedom.runningCoupling reference.referenceLogScale ^ 2

namespace StressTensorTraceAnomalyNormalizationData

/-- The selected running coupling is nonzero because the exact reference lies in the positive
ultraviolet tail. -/
theorem referenceRunningCoupling_ne_zero
    (_data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    freedom.runningCoupling reference.referenceLogScale ≠ 0 :=
  freedom.runningCoupling_ne_zero reference.referenceLogScale
    reference.reference_mem_ultraviolet

/-- The project's `beta(g)/(2*g^3)` expression is a theorem derived from the separately supplied
source convention and outer-coupling curvature-squared rescaling. -/
theorem coefficient_eq_beta_div_two_mul_cube
    (data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    data.coefficient =
      freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) /
        (2 * freedom.runningCoupling reference.referenceLogScale ^ 3) := by
  rw [data.coefficient_eq_sourceConvention, data.scale_eq_outerCoupling]
  field_simp [data.referenceRunningCoupling_ne_zero]

/-- The same derived coefficient written using the exact classical outer coupling connected by
`ClassicalRunningCouplingReferenceData`. -/
theorem coefficient_eq_classicalOuterCoupling
    (data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    data.coefficient = freedom.betaFunction classicalCoupling /
      (2 * classicalCoupling ^ 3) := by
  rw [data.coefficient_eq_beta_div_two_mul_cube]
  exact congrArg
    (fun g : ℝ => freedom.betaFunction g / (2 * g ^ 3))
    reference.coupling_eq_runningCoupling.symm

/-- Nonzero project coefficient forces beta itself to be nonzero at the exact selected reference. -/
theorem betaFunction_at_reference_ne_zero
    (data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) ≠ 0 := by
  intro betaZero
  apply data.coefficient_ne_zero
  rw [data.coefficient_eq_beta_div_two_mul_cube, betaZero]
  simp

/-- The derived project coefficient has exactly the sign of beta at the positive reference
coupling; a sign-flipped normalization is therefore rejected. -/
theorem coefficient_neg_iff_betaFunction_neg
    (data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    data.coefficient < 0 ↔
      freedom.betaFunction (freedom.runningCoupling reference.referenceLogScale) < 0 := by
  rw [data.coefficient_eq_beta_div_two_mul_cube]
  have couplingPos : 0 < freedom.runningCoupling reference.referenceLogScale :=
    freedom.runningCoupling_pos reference.referenceLogScale
      reference.reference_mem_ultraviolet
  have denominatorPos :
      0 < 2 * freedom.runningCoupling reference.referenceLogScale ^ 3 :=
    mul_pos (by norm_num) (pow_pos couplingPos 3)
  constructor
  · intro quotientNeg
    rcases div_neg_iff.mp quotientNeg with impossible | correct
    · exact (not_lt_of_ge (le_of_lt denominatorPos) impossible.2).elim
    · exact correct.1
  · intro betaNeg
    exact div_neg_iff.mpr (Or.inr ⟨betaNeg, denominatorPos⟩)

/-- The normalized one-loop datum in the index is exactly the supplied group/pairing normalization,
not an existentially selected replacement. -/
theorem exact_groupNormalizedOneLoopBeta_chain
    (_data : StressTensorTraceAnomalyNormalizationData normalizedBeta reference) :
    Nonempty (GroupNormalizedOneLoopBetaData inner freedom) :=
  ⟨normalizedBeta⟩

end StressTensorTraceAnomalyNormalizationData

end

end YangMills.Renormalization
