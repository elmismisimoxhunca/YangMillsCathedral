/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanActionGaugeInvariance

/-!
# Hostile probes for Euclidean action gauge invariance
-/

namespace YangMills.Classical.EuclideanActionGaugeInvariance.Probes

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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [CompleteSpace EP]

open YangMills.Geometry

variable
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate)

/-- Gauge pullback retains the exact designated measure. -/
theorem exact_measure :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).measure =
      analytic.measure :=
  analytic.gaugePullback_measure geometry inner gauge connection exterior certificate

/-- Gauge pullback retains the exact positive coupling. -/
theorem exact_coupling :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).coupling =
      analytic.coupling :=
  analytic.gaugePullback_coupling geometry inner gauge connection exterior certificate

/-- Gauge pullback retains the exact Clay outer coefficient. -/
theorem exact_actionCoefficient :
    (analytic.gaugePullback geometry inner gauge connection exterior certificate).actionCoefficient =
      analytic.actionCoefficient :=
  analytic.gaugePullback_actionCoefficient geometry inner gauge connection exterior certificate

/-- The transported datum really certifies integrability of the exact pulled chosen density. -/
theorem exact_pulled_density_integrable :
    Integrable
      (geometry.chosenOrthonormalCurvatureDensity inner
        (gaugePullbackConnection gauge connection)
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate))
      analytic.measure :=
  (analytic.gaugePullback geometry inner gauge connection exterior certificate).density_integrable

/-- The full integrated action is invariant under the exact pulled chain. -/
theorem exact_integrated_action_invariance :
    euclideanYangMillsActionRelativeToMeasure geometry inner
        (gaugePullbackConnection gauge connection)
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate)
        (analytic.gaugePullback geometry inner gauge connection exterior certificate) =
      euclideanYangMillsActionRelativeToMeasure
        geometry inner connection exterior certificate analytic :=
  euclideanYangMillsActionRelativeToMeasure_gaugePullback
    geometry inner gauge connection exterior certificate analytic

/-- A changed integrated action contradicts exact gauge invariance. -/
theorem changed_integrated_action_blocked
    (wrong :
      euclideanYangMillsActionRelativeToMeasure geometry inner
          (gaugePullbackConnection gauge connection)
          (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
          (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate)
          (analytic.gaugePullback geometry inner gauge connection exterior certificate) ≠
        euclideanYangMillsActionRelativeToMeasure
          geometry inner connection exterior certificate analytic) : False :=
  wrong (euclideanYangMillsActionRelativeToMeasure_gaugePullback
    geometry inner gauge connection exterior certificate analytic)

/-- The canonical transport cannot secretly replace the designated measure. -/
theorem changed_transported_measure_blocked
    (wrong :
      (analytic.gaugePullback geometry inner gauge connection exterior certificate).measure ≠
        analytic.measure) : False :=
  wrong (analytic.gaugePullback_measure geometry inner gauge connection exterior certificate)

/-- The canonical transport cannot secretly replace the designated coupling. -/
theorem changed_transported_coupling_blocked
    (wrong :
      (analytic.gaugePullback geometry inner gauge connection exterior certificate).coupling ≠
        analytic.coupling) : False :=
  wrong (analytic.gaugePullback_coupling geometry inner gauge connection exterior certificate)

end

end YangMills.Classical.EuclideanActionGaugeInvariance.Probes
