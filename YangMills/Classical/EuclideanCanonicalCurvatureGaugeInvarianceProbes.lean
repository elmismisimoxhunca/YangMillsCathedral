/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance

/-!
# Hostile probes for gauge invariance of canonical curvature density
-/

namespace YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance.Probes

open Bundle
open scoped BigOperators Bundle ContDiff Manifold Topology

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
    [IsTopologicalGroup G]
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
open EuclideanMetricData

omit [FiniteDimensional ℝ EG] [CompleteSpace EP] in
/-- Arbitrary exact fiber-action transforms preserve the canonical two-form contraction. -/
theorem exact_transformedTwoForm_contraction
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (form transformed : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B)
    (htransform : ∀ v,
      transformed b v = gauge.inducedAdjointFiberAction b (form b v)) :
    geometry.canonicalTwoFormContraction inner transformed b =
      geometry.canonicalTwoFormContraction inner form b :=
  geometry.canonicalTwoFormContraction_inducedAdjointFiberAction
    inner gauge form transformed b htransform

/-- The exact chosen density is unchanged by the full derived gauge-pullback chain. -/
theorem exact_chosen_density_invariance
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    geometry.chosenOrthonormalCurvatureDensity inner
        (gaugePullbackConnection gauge connection)
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate) b =
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b :=
  geometry.chosenOrthonormalCurvatureDensity_gaugePullback
    inner gauge connection exterior certificate b

/-- The exact canonical density is unchanged by the full derived gauge-pullback chain. -/
theorem exact_canonical_density_invariance
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    geometry.canonicalCurvatureDensity inner
        (gaugePullbackConnection gauge connection)
        (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate) b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b :=
  geometry.canonicalCurvatureDensity_gaugePullback
    inner gauge connection exterior certificate b

/-- A claimed change of the exact canonical density is inconsistent. -/
theorem changed_canonical_density_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (wrong :
      geometry.canonicalCurvatureDensity inner
          (gaugePullbackConnection gauge connection)
          (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
          (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate) b ≠
        geometry.canonicalCurvatureDensity inner connection exterior certificate b) : False :=
  wrong (geometry.canonicalCurvatureDensity_gaugePullback
    inner gauge connection exterior certificate b)

/-- A claimed change of the chosen contraction is likewise inconsistent. -/
theorem changed_chosen_density_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (wrong :
      geometry.chosenOrthonormalCurvatureDensity inner
          (gaugePullbackConnection gauge connection)
          (gaugePullbackConnectionExteriorDerivative gauge connection exterior)
          (gaugePullbackCurvatureStructureCertificate gauge connection exterior certificate) b ≠
        geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b) : False :=
  wrong (geometry.chosenOrthonormalCurvatureDensity_gaugePullback
    inner gauge connection exterior certificate b)

end

end YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance.Probes
