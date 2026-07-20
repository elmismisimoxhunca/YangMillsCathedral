/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalAction
import YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance

/-!
# Gauge invariance of the Euclidean action

Pointwise equality of the exact gauge-pulled curvature density transports the analytic action datum
to the pulled connection/exterior/certificate chain without changing the base measure or coupling.
Consequently the canonical integral, and hence the existing relative-to-measure Euclidean action,
is unchanged.

Gauge transformations here cover the identity on the base. No measure pushforward or Jacobian is
introduced. This theorem is not invariance under a base diffeomorphism, does not identify the
measure with metric volume, and does not prove observable invariance.
-/

namespace YangMills.Classical

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

namespace EuclideanActionAnalyticData

/-- Transport the analytic datum to the exact gauge-pulled chain. The measure and coupling are
unchanged; only integrability is transported across the proved pointwise density equality. -/
def gaugePullback
    [CompleteSpace EP]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    EuclideanActionAnalyticData geometry inner
      (gaugePullbackConnection gauge connection)
      (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
      (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate) where
  measurable_is_borel := analytic.measurable_is_borel
  measure := analytic.measure
  coupling := analytic.coupling
  coupling_pos := analytic.coupling_pos
  density_integrable := by
    apply analytic.density_integrable.congr
    filter_upwards [] with b
    exact (geometry.chosenOrthonormalCurvatureDensity_gaugePullback
      inner gauge connection exterior certificate b).symm

@[simp]
theorem gaugePullback_measure
    [CompleteSpace EP]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).measure =
      analytic.measure :=
  rfl

@[simp]
theorem gaugePullback_coupling
    [CompleteSpace EP]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).coupling =
      analytic.coupling :=
  rfl

@[simp]
theorem gaugePullback_actionCoefficient
    [CompleteSpace EP]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).actionCoefficient =
      analytic.actionCoefficient :=
  rfl

end EuclideanActionAnalyticData

/-- The exact relative-to-measure Euclidean action is invariant under gauge pullback, with the same
base measure and coupling. -/
theorem euclideanYangMillsActionRelativeToMeasure_gaugePullback
    [CompleteSpace EP]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    euclideanYangMillsActionRelativeToMeasure geometry inner
        (gaugePullbackConnection gauge connection)
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate)
        (analytic.gaugePullback geometry inner gauge connection exterior certificate) =
      euclideanYangMillsActionRelativeToMeasure
        geometry inner connection exterior certificate analytic := by
  rw [euclideanYangMillsActionRelativeToMeasure_eq_canonical,
    euclideanYangMillsActionRelativeToMeasure_eq_canonical]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with b
  exact geometry.canonicalCurvatureDensity_gaugePullback
    inner gauge connection exterior certificate b

end

end YangMills.Classical
