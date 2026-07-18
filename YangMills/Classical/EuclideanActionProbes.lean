/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanAction

/-!
# Hostile probes for the Euclidean action relative to a designated measure
-/

namespace YangMills.Classical.Probes

open Bundle MeasureTheory
open scoped Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [MeasurableSpace B] [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : YangMills.Geometry.PrincipalBundleTorsorData G B P}
    {bundle : YangMills.Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : YangMills.Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]

open YangMills.Geometry

variable
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate)

include analytic in
/-- A non-Borel measurable structure cannot enter the analytic action data. -/
theorem nonBorel_actionMeasurableStructure_blocked
    (notBorel : ¬ BorelSpace B) : False :=
  notBorel analytic.1

/-- The action data cannot carry a zero or negative coupling. -/
theorem nonpositive_actionCoupling_blocked
    (nonpositive : analytic.coupling ≤ 0) : False :=
  (not_lt_of_ge nonpositive) analytic.coupling_pos

/-- A nonintegrable exact curvature scalar cannot enter the real-valued action domain. -/
theorem nonintegrable_exactCurvatureDensity_blocked
    (notIntegrable : ¬ Integrable
      (geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate)
      analytic.measure) : False :=
  notIntegrable analytic.density_integrable

/-- The relative-to-measure action cannot be negative. -/
theorem negative_euclideanAction_blocked
    (negative : euclideanYangMillsActionRelativeToMeasure
      geometry inner connection exterior certificate analytic < 0) : False :=
  (not_lt_of_ge
    (euclideanYangMillsActionRelativeToMeasure_nonnegative
      geometry inner connection exterior certificate analytic)) negative

/-- An unrelated pointwise scalar cannot replace the exact curvature scalar if it changes the
weighted action value. -/
theorem unrelated_actionIntegrand_substitution_blocked
    (candidate : B → ℝ)
    (changesAction :
      analytic.actionCoefficient * ∫ b, candidate b ∂analytic.measure ≠
        analytic.actionCoefficient *
          ∫ b, geometry.chosenOrthonormalCurvatureDensity
            inner connection exterior certificate b ∂analytic.measure)
    (claimsSubstitution :
      euclideanYangMillsActionRelativeToMeasure
          geometry inner connection exterior certificate analytic =
        analytic.actionCoefficient * ∫ b, candidate b ∂analytic.measure) : False := by
  apply changesAction
  rw [← claimsSubstitution]
  exact euclideanYangMillsActionRelativeToMeasure_eq
    geometry inner connection exterior certificate analytic

/-- An unrelated measure cannot replace the designated measure if it changes the action value. -/
theorem unrelated_actionMeasure_substitution_blocked
    (alternative : Measure B)
    (changesAction :
      analytic.actionCoefficient *
          ∫ b, geometry.chosenOrthonormalCurvatureDensity
            inner connection exterior certificate b ∂alternative ≠
        analytic.actionCoefficient *
          ∫ b, geometry.chosenOrthonormalCurvatureDensity
            inner connection exterior certificate b ∂analytic.measure)
    (claimsSubstitution :
      euclideanYangMillsActionRelativeToMeasure
          geometry inner connection exterior certificate analytic =
        analytic.actionCoefficient *
          ∫ b, geometry.chosenOrthonormalCurvatureDensity
            inner connection exterior certificate b ∂alternative) : False := by
  apply changesAction
  rw [← claimsSubstitution]
  exact euclideanYangMillsActionRelativeToMeasure_eq
    geometry inner connection exterior certificate analytic

/-- A disconnected caller-supplied real cannot replace the action computed from the exact data. -/
theorem disconnected_actionValue_blocked
    (candidate : ℝ)
    (different : candidate ≠ euclideanYangMillsActionRelativeToMeasure
      geometry inner connection exterior certificate analytic)
    (claimsExactFormula :
      candidate = analytic.actionCoefficient *
        ∫ b, geometry.chosenOrthonormalCurvatureDensity
          inner connection exterior certificate b ∂analytic.measure) : False := by
  apply different
  rw [claimsExactFormula]
  exact (euclideanYangMillsActionRelativeToMeasure_eq
    geometry inner connection exterior certificate analytic).symm

end

end YangMills.Classical.Probes
