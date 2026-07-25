/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCurvatureDensity
import YangMills.Geometry.AdjointBundleInvariantPairingLinear
import YangMills.Mathematics.AlternatingMapDegreeTwoBilinear
import YangMills.Mathematics.OrthonormalBilinearContraction

/-!
# Canonical Euclidean contraction of adjoint-valued two-forms

This module applies the reusable canonical-tensor contraction to the exact bilinear packaging of an
adjoint-fiber pairing and the exact bilinear packaging of a degree-two continuous alternating map.
The resulting scalar is proved equal both to the previously committed chosen-basis contraction and
to the corresponding sum in every orthonormal basis.

This closes basis dependence of the pointwise scalar contraction. It does not construct or identify
a general manifold Hodge star, a volume form, or a metric-induced measure.
-/

namespace YangMills.Classical

open Bundle
open scoped BigOperators Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP uι

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

open YangMills.Geometry YangMills.Mathematics

namespace EuclideanMetricData

/-- The basis-free canonical tensor contraction of an adjoint-bundle-valued two-form at one base
point, with the conventional inner factor `1/2`. -/
def canonicalTwoFormContraction
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) : ℝ := by
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace IB b) := tangentSpaceFiniteDimensional b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact (2 : ℝ)⁻¹ * canonicalBilinearQuadraticContraction
    (AdjointBundle.fiberPairingLinearMap bundle inner b)
    (continuousAlternatingMapFinTwoToBilinear (form b))

omit [FiniteDimensional ℝ EG] in
/-- Positive rescaling of the named invariant pairing scales the canonical two-form contraction by
the same scalar. -/
theorem canonicalTwoFormContraction_positiveScale
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (scalar : ℝ) (scalar_pos : 0 < scalar)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) :
    geometry.canonicalTwoFormContraction
        (inner.positiveScale scalar scalar_pos) form b =
      scalar * geometry.canonicalTwoFormContraction inner form b := by
  rw [canonicalTwoFormContraction, canonicalTwoFormContraction]
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace IB b) := tangentSpaceFiniteDimensional b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  rw [AdjointBundle.fiberPairingLinearMap_positiveScale
    bundle inner scalar scalar_pos b]
  rw [canonicalBilinearQuadraticContraction_smul_pairing]
  ring

omit [FiniteDimensional ℝ EG] in
/-- Every orthonormal basis computes the canonical contraction as the conventional double sum. -/
theorem canonicalTwoFormContraction_eq_orthonormalSum
    {ι : Type uι} [Fintype ι]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) :
    letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
      ⟨geometry.metric.toRiemannianMetric⟩
    ∀ basis : OrthonormalBasis ι ℝ (TangentSpace IB b),
      geometry.canonicalTwoFormContraction inner form b =
        (2 : ℝ)⁻¹ * ∑ i, ∑ j,
          AdjointBundle.fiberPairing bundle inner b
            ((form b) ![basis i, basis j]) ((form b) ![basis i, basis j]) := by
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  intro basis
  rw [canonicalTwoFormContraction]
  letI : FiniteDimensional ℝ (TangentSpace IB b) := tangentSpaceFiniteDimensional b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  congr 1
  rw [canonicalBilinearQuadraticContraction_eq_sum
    (AdjointBundle.fiberPairingLinearMap bundle inner b)
    (continuousAlternatingMapFinTwoToBilinear (form b)) basis]
  simp

omit [FiniteDimensional ℝ EG] in
/-- The earlier chosen-standard-basis contraction is exactly the canonical tensor contraction. -/
theorem canonicalTwoFormContraction_eq_chosen
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) :
    geometry.canonicalTwoFormContraction inner form b =
      geometry.chosenOrthonormalTwoFormContraction inner form b := by
  rw [canonicalTwoFormContraction, chosenOrthonormalTwoFormContraction]
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace IB b) := tangentSpaceFiniteDimensional b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  congr 1
  rw [canonicalBilinearQuadraticContraction_eq_sum
    (AdjointBundle.fiberPairingLinearMap bundle inner b)
    (continuousAlternatingMapFinTwoToBilinear (form b))
    (stdOrthonormalBasis ℝ (TangentSpace IB b))]
  simp

/-- The canonical pointwise Euclidean scalar of the exact smoothly descended curvature. -/
def canonicalCurvatureDensity
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) : ℝ :=
  geometry.canonicalTwoFormContraction inner
    (connection.smoothBaseCurvature exterior certificate).toForm b

/-- Positive rescaling of the named invariant pairing scales the exact canonical curvature scalar
by the same factor. -/
theorem canonicalCurvatureDensity_positiveScale
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (scalar : ℝ) (scalar_pos : 0 < scalar)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    geometry.canonicalCurvatureDensity (inner.positiveScale scalar scalar_pos)
        connection exterior certificate b =
      scalar * geometry.canonicalCurvatureDensity
        inner connection exterior certificate b :=
  geometry.canonicalTwoFormContraction_positiveScale
    inner scalar scalar_pos _ b

/-- The canonical curvature scalar is exactly the previously chosen contraction of the same exact
curvature. -/
theorem canonicalCurvatureDensity_eq_chosen
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    geometry.canonicalCurvatureDensity inner connection exterior certificate b =
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b :=
  geometry.canonicalTwoFormContraction_eq_chosen inner _ b

/-- The exact canonical curvature scalar is pointwise nonnegative. -/
theorem canonicalCurvatureDensity_nonnegative
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    0 ≤ geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  rw [geometry.canonicalCurvatureDensity_eq_chosen inner connection exterior certificate b]
  exact geometry.chosenOrthonormalCurvatureDensity_nonnegative
    inner connection exterior certificate b

end EuclideanMetricData

end

end YangMills.Classical
