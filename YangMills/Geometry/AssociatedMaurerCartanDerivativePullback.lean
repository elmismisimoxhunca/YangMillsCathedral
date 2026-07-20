/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.UniversalMaurerCartanExteriorDerivative

/-!
# Associated Maurer--Cartan derivative as universal pullback

The smooth associated derivative candidate `-1/2[α∧α]` is exactly the raw pullback of the certified
universal Maurer--Cartan derivative. The proof uses pointwise naturality of the exact bracket wedge
and preserves the existing associated one-form carrier.

This is the required derivative-carrier identity, but not yet an associated exterior-derivative
certificate; arbitrary-smooth-map Cartan naturality remains separate.
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
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
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

private theorem pullback_lieBracketWedgeOneMany
    (gauge : SmoothGaugeTransformation smoothBundle)
    (first second : ManifoldDifferentialForm IG G (GroupLieAlgebra IG G) 1) :
    ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1 first second) =
      ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        (ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
          gauge.associatedGaugeFunction_contMDiff first)
        (ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
          gauge.associatedGaugeFunction_contMDiff second) := by
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ManifoldDifferentialForm.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ManifoldDifferentialForm.lieBracketWedgeOneMany_apply]
  rfl

/-- The already-smooth associated derivative candidate is exactly the pointwise pullback of the
certified universal derivative carrier. This is algebraic; certification still needs exterior
naturality for an arbitrary smooth map. -/
theorem associatedMaurerCartanDerivativeCandidate_eq_universal_pullback
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm =
      ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm := by
  rw [associatedMaurerCartanDerivativeCandidate_toForm,
    leftMaurerCartanExteriorDerivative_toForm]
  rw [show gauge.associatedMaurerCartanPullback =
      ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (leftMaurerCartanForm (IG := IG) (G := G)) from associated_eq_pullback gauge]
  rw [show ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
      gauge.associatedGaugeFunction_contMDiff
      ((-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm) =
      (-1 / 2 : ℝ) • ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
          leftMaurerCartanForm leftMaurerCartanForm) by
    funext p
    apply ContinuousAlternatingMap.ext
    intro v
    rfl]
  rw [pullback_lieBracketWedgeOneMany gauge]

end
end YangMills.Geometry
