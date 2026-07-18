/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalAction

/-!
# Hostile probes for the canonical-curvature action presentation
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

/-- The canonical exact curvature scalar cannot become nonintegrable while the action data is
admissible. -/
theorem nonintegrable_canonicalCurvatureDensity_blocked
    (notIntegrable : ¬ Integrable
      (geometry.canonicalCurvatureDensity inner connection exterior certificate)
      analytic.measure) : False :=
  notIntegrable (analytic.canonicalCurvatureDensity_integrable
    geometry inner connection exterior certificate)

/-- The existing action cannot disagree with its canonical-curvature integral presentation. -/
theorem canonical_actionFormula_mismatch_blocked
    (mismatch :
      euclideanYangMillsActionRelativeToMeasure
          geometry inner connection exterior certificate analytic ≠
        analytic.actionCoefficient *
          ∫ b, geometry.canonicalCurvatureDensity
            inner connection exterior certificate b ∂analytic.measure) : False :=
  mismatch (euclideanYangMillsActionRelativeToMeasure_eq_canonical
    geometry inner connection exterior certificate analytic)

/-- An unrelated scalar integrand cannot replace the canonical curvature scalar when it changes the
weighted action value. -/
theorem unrelated_canonicalActionIntegrand_substitution_blocked
    (candidate : B → ℝ)
    (changesAction :
      analytic.actionCoefficient * ∫ b, candidate b ∂analytic.measure ≠
        analytic.actionCoefficient *
          ∫ b, geometry.canonicalCurvatureDensity
            inner connection exterior certificate b ∂analytic.measure)
    (claimsSubstitution :
      euclideanYangMillsActionRelativeToMeasure
          geometry inner connection exterior certificate analytic =
        analytic.actionCoefficient * ∫ b, candidate b ∂analytic.measure) : False := by
  apply changesAction
  rw [← claimsSubstitution]
  exact euclideanYangMillsActionRelativeToMeasure_eq_canonical
    geometry inner connection exterior certificate analytic

end

end YangMills.Classical.Probes
