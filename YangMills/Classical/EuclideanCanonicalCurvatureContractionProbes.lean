/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalCurvatureContraction

/-!
# Hostile probes for canonical Euclidean curvature contraction
-/

namespace YangMills.Classical.Probes

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

open YangMills.Geometry

omit [FiniteDimensional ℝ EG] in
/-- The canonical tensor contraction cannot differ from the earlier chosen-basis contraction. -/
theorem canonical_chosenTwoFormContraction_mismatch_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B)
    (mismatch :
      geometry.canonicalTwoFormContraction inner form b ≠
        geometry.chosenOrthonormalTwoFormContraction inner form b) : False :=
  mismatch (geometry.canonicalTwoFormContraction_eq_chosen inner form b)

omit [FiniteDimensional ℝ EG] in
/-- No orthonormal basis can compute a different contraction sum. -/
theorem orthonormalBasis_curvatureContraction_mismatch_blocked
    {ι : Type uι} [Fintype ι]
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) :
    letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
      ⟨geometry.metric.toRiemannianMetric⟩
    ∀ (basis : OrthonormalBasis ι ℝ (TangentSpace IB b)),
      (geometry.canonicalTwoFormContraction inner form b ≠
        (2 : ℝ)⁻¹ * ∑ i, ∑ j,
          AdjointBundle.fiberPairing bundle inner b
            ((form b) ![basis i, basis j]) ((form b) ![basis i, basis j])) → False := by
  letI : RiemannianBundle (fun b : B => TangentSpace IB b) :=
    ⟨geometry.metric.toRiemannianMetric⟩
  intro basis mismatch
  exact mismatch (geometry.canonicalTwoFormContraction_eq_orthonormalSum inner form b basis)

/-- Positive pairing rescaling cannot change the exact canonical curvature scalar by a different
factor. -/
theorem malformed_canonicalCurvatureScale_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (scalar : ℝ) (scalar_pos : 0 < scalar)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (mismatch :
      geometry.canonicalCurvatureDensity (inner.positiveScale scalar scalar_pos)
          connection exterior certificate b ≠
        scalar * geometry.canonicalCurvatureDensity
          inner connection exterior certificate b) : False :=
  mismatch (geometry.canonicalCurvatureDensity_positiveScale
    inner scalar scalar_pos connection exterior certificate b)

/-- The exact canonical curvature scalar cannot be negative. -/
theorem negative_canonicalCurvatureDensity_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (b : B)
    (negative : geometry.canonicalCurvatureDensity
      inner connection exterior certificate b < 0) : False :=
  (not_lt_of_ge
    (geometry.canonicalCurvatureDensity_nonnegative
      inner connection exterior certificate b)) negative

/-- An unrelated two-form cannot replace the exact certified curvature when it changes the
canonical contraction. -/
theorem unrelated_canonicalCurvature_substitution_blocked
    (geometry : EuclideanMetricData (IB := IB) (B := B))
    (inner : InvariantInnerProductData (I := IG) (G := G))
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (certificate : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (candidate : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B)
    (changesDensity :
      geometry.canonicalTwoFormContraction inner candidate b ≠
        geometry.canonicalTwoFormContraction inner
          (connection.pointwiseBaseCurvature exterior) b)
    (claimsSubstitution :
      geometry.canonicalCurvatureDensity inner connection exterior certificate b =
        geometry.canonicalTwoFormContraction inner candidate b) : False := by
  apply changesDensity
  rw [← claimsSubstitution]
  rfl

end

end YangMills.Classical.Probes
