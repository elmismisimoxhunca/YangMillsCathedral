/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCurvatureDensity

/-!
# Hostile probes for the chosen Euclidean curvature contraction
-/

namespace YangMills.Classical.Probes

open Bundle
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

/-- The exact chosen density cannot be negative. -/
theorem negative_chosenCurvatureDensity_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (negative : geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b < 0) :
    False :=
  (not_lt_of_ge
    (geometry.chosenOrthonormalCurvatureDensity_nonnegative
      inner connection exterior certificate b)) negative

/-- An unrelated adjoint-valued two-form cannot replace the exact certified curvature when that
replacement changes the chosen scalar contraction. -/
theorem unrelated_curvature_substitution_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (candidate : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B)
    (changesDensity :
      geometry.chosenOrthonormalTwoFormContraction inner candidate b ≠
        geometry.chosenOrthonormalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b)
    (claimsSubstitution :
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b =
        geometry.chosenOrthonormalTwoFormContraction inner candidate b) : False := by
  apply changesDensity
  rw [← claimsSubstitution]
  exact geometry.chosenOrthonormalCurvatureDensity_eq_pointwiseBaseCurvature
    inner connection exterior certificate b

/-- A different invariant pairing cannot replace the supplied exact pairing when it changes the
chosen scalar contraction. -/
theorem unrelated_innerProduct_substitution_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner alternative : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (changesDensity :
      geometry.chosenOrthonormalTwoFormContraction alternative
          (connection.pointwiseBaseCurvature exterior) b ≠
        geometry.chosenOrthonormalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b)
    (claimsSubstitution :
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b =
        geometry.chosenOrthonormalTwoFormContraction alternative
          (connection.pointwiseBaseCurvature exterior) b) : False := by
  apply changesDensity
  rw [← claimsSubstitution]
  exact geometry.chosenOrthonormalCurvatureDensity_eq_pointwiseBaseCurvature
    inner connection exterior certificate b

/-- A different metric cannot replace the supplied metric when it changes the chosen scalar
contraction. -/
theorem unrelated_metric_substitution_blocked
    (geometry alternative : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (changesDensity :
      alternative.chosenOrthonormalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b ≠
        geometry.chosenOrthonormalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b)
    (claimsSubstitution :
      geometry.chosenOrthonormalCurvatureDensity inner connection exterior certificate b =
        alternative.chosenOrthonormalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b) : False := by
  apply changesDensity
  rw [← claimsSubstitution]
  exact geometry.chosenOrthonormalCurvatureDensity_eq_pointwiseBaseCurvature
    inner connection exterior certificate b

omit [FiniteDimensional ℝ EG] in
/-- Every designated chart computes the canonical pairing used by each contraction term. -/
theorem chart_dependent_contractionPairing_blocked
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (X Y : AdjointBundle.Fiber (I := IG) (torsor := torsor) b)
    (mismatch :
      AdjointBundle.fiberPairingInChart bundle inner chart hb X Y ≠
        AdjointBundle.fiberPairing bundle inner b X Y) : False :=
  mismatch (AdjointBundle.fiberPairingInChart_eq bundle inner chart hb X Y)

end

end YangMills.Classical.Probes
