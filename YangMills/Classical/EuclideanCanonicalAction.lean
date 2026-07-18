/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanAction
import YangMills.Classical.EuclideanCanonicalCurvatureContraction

/-!
# Canonical-curvature presentation of the Euclidean action

The existing real-valued Euclidean action was deliberately defined through the earlier chosen
orthonormal contraction. That contraction is now proved equal pointwise to the canonical tensor
contraction. This module transports integrability across the exact equality and proves that the same
action integrates the canonical curvature scalar.

No action value or analytic witness is replaced. The designated Borel measure remains explicit and
is not called Riemannian volume; no general Hodge-star theorem is asserted.
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

/-- Integrability of the committed chosen contraction is exactly integrability of the canonical
curvature scalar against the same designated measure. -/
theorem EuclideanActionAnalyticData.canonicalCurvatureDensity_integrable
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    Integrable (geometry.canonicalCurvatureDensity inner connection exterior certificate)
      analytic.measure := by
  apply analytic.density_integrable.congr
  filter_upwards [] with b
  exact (geometry.canonicalCurvatureDensity_eq_chosen
    inner connection exterior certificate b).symm

/-- The existing relative-to-measure action is exactly the integral of the basis-free canonical
curvature scalar with the same designated measure and Clay outer coefficient. -/
theorem euclideanYangMillsActionRelativeToMeasure_eq_canonical
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (analytic : EuclideanActionAnalyticData geometry inner connection exterior certificate) :
    euclideanYangMillsActionRelativeToMeasure
        geometry inner connection exterior certificate analytic =
      analytic.actionCoefficient *
        ∫ b, geometry.canonicalCurvatureDensity
          inner connection exterior certificate b ∂analytic.measure := by
  rw [euclideanYangMillsActionRelativeToMeasure]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with b
  exact (geometry.canonicalCurvatureDensity_eq_chosen
    inner connection exterior certificate b).symm

end

end YangMills.Classical
