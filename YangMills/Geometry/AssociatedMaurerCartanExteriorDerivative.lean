/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AssociatedMaurerCartanDerivativePullback
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates

/-!
# Certified associated Maurer--Cartan equation

Arbitrary-smooth-map exterior naturality is applied to the associated gauge function. This certifies
the existing smooth derivative candidate as the exterior derivative of the exact associated
Maurer--Cartan pullback and derives its structure equation with the established `1/2` normalization.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Checked application of the arbitrary-smooth-map constructor to the associated gauge map. -/
noncomputable def associatedMaurerCartanExteriorDerivativeCertificate
    (gauge : SmoothGaugeTransformation smoothBundle) :
    SmoothManifoldOneFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) gauge.associatedMaurerCartanPullbackSmoothForm :=
  SmoothManifoldOneFormExteriorDerivativeCertificate.pullbackSmoothMapOfForms
    gauge.associatedGaugeFunction gauge.associatedGaugeFunction_contMDiff
    (groupLieAlgebraModelEquiv IG)
    (leftMaurerCartanSmoothForm (IG := IG) (G := G))
    (leftMaurerCartanExteriorDerivativeCertificate (IG := IG) (G := G))
    gauge.associatedMaurerCartanPullbackSmoothForm
    (by
      rw [gauge.associatedMaurerCartanPullbackSmoothForm_toForm]
      exact associated_eq_pullback gauge)
    (associatedMaurerCartanDerivativeCandidate gauge)
    (associatedMaurerCartanDerivativeCandidate_eq_universal_pullback gauge)

@[simp] theorem associatedMaurerCartanExteriorDerivativeCertificate_derivative
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanExteriorDerivativeCertificate gauge).derivative =
      associatedMaurerCartanDerivativeCandidate gauge := rfl

/-- The associated Maurer--Cartan equation now follows from the certified derivative carrier. -/
theorem associatedMaurerCartan_structureEquation
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanExteriorDerivativeCertificate gauge).derivative.toForm +
      (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback gauge.associatedMaurerCartanPullback = 0 := by
  rw [associatedMaurerCartanExteriorDerivativeCertificate_derivative]
  exact associatedMaurerCartanDerivativeCandidate_add_half_selfWedge gauge

end
end YangMills.Geometry
