/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleInvariantPairing
import YangMills.Geometry.PrincipalCurvatureSmoothDescent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# A chosen orthonormal contraction of Euclidean Yang--Mills curvature

This module supplies the pointwise positive scalar needed before integration in the classical
Euclidean action. Its inputs are the exact smoothly descended curvature, the exact invariant
pairing on the actual adjoint quotient fiber, and a named smooth Riemannian metric.

Mathlib does not currently provide the required general manifold Hodge-star interface. We therefore
use `stdOrthonormalBasis` in each tangent fiber and expose the construction honestly as a *chosen
orthonormal contraction*. No basis-independence theorem or general Hodge-star theorem is asserted
here. Integration measure, coupling, integrability, and the action remain separate downstream data.
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

/-- A named smooth positive-definite metric on the Euclidean base tangent bundle.

This structure deliberately contains neither a measure nor a purported Hodge-star operation. -/
structure EuclideanMetricData where
  metric : ContMDiffRiemannianMetric IB ∞ EB (fun b : B => TangentSpace IB b)

namespace EuclideanMetricData

/-- Reusable finite-dimensionality transport from the base model to a tangent fiber. -/
@[reducible]
noncomputable def tangentSpaceFiniteDimensional (b : B) :
    FiniteDimensional ℝ (TangentSpace IB b) :=
  FiniteDimensional.of_injective
    ((trivializationAt EB (TangentSpace IB) b).linearEquivAt ℝ b
      (mem_baseSet_trivializationAt EB (TangentSpace IB) b)).toLinearMap
    ((trivializationAt EB (TangentSpace IB) b).linearEquivAt ℝ b
      (mem_baseSet_trivializationAt EB (TangentSpace IB) b)).injective

/-- The conventional `1/2 * sum_ij` contraction of an adjoint-valued two-form in Mathlib's chosen
standard orthonormal basis for the metric tangent fiber.

The name records the remaining basis-independence debt: this is not advertised as a general
manifold Hodge-star construction. -/
def chosenOrthonormalTwoFormContraction
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) : ℝ := by
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace IB b) := tangentSpaceFiniteDimensional b
  let basis := stdOrthonormalBasis ℝ (TangentSpace IB b)
  exact (2 : ℝ)⁻¹ * ∑ i, ∑ j,
    AdjointBundle.fiberPairing bundle inner b
      ((form b) ![basis i, basis j])
      ((form b) ![basis i, basis j])

/-- The chosen pointwise Euclidean density of the exact curvature derived from the same connection
and exterior-derivative datum and certified by the same-index structure certificate. -/
def chosenOrthonormalCurvatureDensity
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) : ℝ :=
  geometry.chosenOrthonormalTwoFormContraction inner
    (connection.smoothBaseCurvature exterior certificate).toForm b

/-- Unfolding the chosen density exposes the exact pointwise base curvature derived from the same
connection and exterior-derivative datum. -/
@[simp]
theorem chosenOrthonormalCurvatureDensity_eq_pointwiseBaseCurvature
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b =
      geometry.chosenOrthonormalTwoFormContraction inner
        (connection.pointwiseBaseCurvature exterior) b :=
  rfl

omit [FiniteDimensional ℝ EG] in
/-- The chosen orthonormal contraction is pointwise nonnegative. -/
theorem chosenOrthonormalTwoFormContraction_nonnegative
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) :
    0 ≤ geometry.chosenOrthonormalTwoFormContraction inner form b := by
  rw [chosenOrthonormalTwoFormContraction]
  apply mul_nonneg (inv_nonneg.mpr (by norm_num))
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    AdjointBundle.fiberPairing_self_nonnegative bundle inner b _

/-- The exact chosen curvature density is pointwise nonnegative. -/
theorem chosenOrthonormalCurvatureDensity_nonnegative
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B) :
    0 ≤ geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b :=
  geometry.chosenOrthonormalTwoFormContraction_nonnegative inner _ b

end EuclideanMetricData

end

end YangMills.Classical
