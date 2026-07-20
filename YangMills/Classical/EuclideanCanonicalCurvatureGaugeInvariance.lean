/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalCurvatureContraction
import YangMills.Geometry.AdjointBundleGaugeInvariantPairing

/-!
# Gauge invariance of canonical Euclidean curvature contraction

A fiberwise transformation of an adjoint-valued two-form by one exact induced gauge action leaves
the canonical quadratic contraction unchanged. Exact smooth curvature covariance applies this
reusable result to the gauge-pulled connection, its derived exterior datum, and its derived
same-index structure certificate. The pulled curvature uses the inverse induced action, as required
by the contravariant connection pullback convention.

These are pointwise scalar-density theorems. Integration, action invariance, and observable
invariance remain downstream.
-/

namespace YangMills.Classical

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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]

open YangMills.Geometry

namespace EuclideanMetricData

omit [FiniteDimensional ℝ EG] in
/-- The canonical contraction is unchanged when every value of a two-form is transformed by the
same exact induced adjoint-fiber action. -/
theorem canonicalTwoFormContraction_inducedAdjointFiberAction
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (gauge : SmoothGaugeTransformation smoothBundle)
    (form transformed : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B)
    (htransform : ∀ v,
      transformed b v = gauge.inducedAdjointFiberAction b (form b v)) :
    geometry.canonicalTwoFormContraction inner transformed b =
      geometry.canonicalTwoFormContraction inner form b := by
  rw [geometry.canonicalTwoFormContraction_eq_chosen inner transformed b,
    geometry.canonicalTwoFormContraction_eq_chosen inner form b]
  rw [chosenOrthonormalTwoFormContraction, chosenOrthonormalTwoFormContraction]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [htransform]
  exact AdjointBundle.fiberPairing_self_inducedAdjointFiberAction inner gauge b _

/-- The chosen orthonormal curvature density is invariant under the exact gauge-pulled chain. -/
theorem chosenOrthonormalCurvatureDensity_gaugePullback
    [CompleteSpace EP]
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
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b := by
  unfold chosenOrthonormalCurvatureDensity chosenOrthonormalTwoFormContraction
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gaugePullbackSmoothBaseCurvature_eq_inverseInducedAction
    gauge connection exterior certificate]
  exact AdjointBundle.fiberPairing_self_inducedAdjointFiberAction inner gauge⁻¹ b _

/-- The basis-independent canonical curvature density is invariant under the exact gauge-pulled
connection/exterior/certificate chain. -/
theorem canonicalCurvatureDensity_gaugePullback
    [CompleteSpace EP]
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
      geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  apply geometry.canonicalTwoFormContraction_inducedAdjointFiberAction inner gauge⁻¹
  intro v
  exact gaugePullbackSmoothBaseCurvature_eq_inverseInducedAction
    gauge connection exterior certificate b v

end EuclideanMetricData

end

end YangMills.Classical
