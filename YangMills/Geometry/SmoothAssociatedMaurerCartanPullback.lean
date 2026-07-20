/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation
import YangMills.Mathematics.LieGroupAdjointRegularity
import YangMills.Mathematics.SmoothManifoldDifferentialFormOperations

/-!
# Smooth associated Maurer--Cartan pullback

For a supplied smooth principal connection, the affine gauge formula identifies the exact associated
Maurer--Cartan pullback with the difference between two derived smooth forms: the gauge-pulled
connection and the original connection transformed pointwise by `Ad(g_ϕ⁻¹)`. This proves smoothness
without changing the raw carrier already used by the affine theorem.

The connection parameter is a proof device tied to the same affine identity, not an additional field
of the Maurer--Cartan form. A connection-independent direct smoothness theorem and the
Maurer--Cartan structure equation remain separate reusable-mathematics goals.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

set_option backward.isDefEq.respectTransparency false

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Original connection form transformed pointwise by the exact inverse adjoint factor. -/
noncomputable def adjointTransformedConnectionForm
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 1 := fun p =>
  (lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹).compContinuousAlternatingMap
    (connection.pointwise.form p)

@[simp] theorem adjointTransformedConnectionForm_apply
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : Fin 1 → TangentSpace IP p) :
    adjointTransformedConnectionForm gauge connection p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        (connection.pointwise.form p v) := rfl

/-- Joint adjoint regularity and connection smoothness derive smoothness of the transformed term. -/
theorem adjointTransformedConnectionForm_isSmooth
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    (adjointTransformedConnectionForm gauge connection).IsSmooth
      (groupLieAlgebraModelEquiv IG) := by
  intro s fields fields_smooth
  have hg : ContMDiffOn IP IG ∞ gauge.associatedGaugeFunction s :=
    gauge.associatedGaugeFunction_contMDiff.contMDiffOn
  have hA := connection.form_smooth s fields fields_smooth
  have hpair : ContMDiffOn IP (IG.prod 𝓘(ℝ, EG)) ∞
      (fun p => (gauge.associatedGaugeFunction p,
        groupLieAlgebraModelEquiv IG
          (connection.pointwise.form p (fun i => fields i p)))) s :=
    hg.prodMk hA
  have hresult :=
    (lieGroupAdjointCoordinates_inverseAction_contMDiff (I := IG) (G := G)).comp_contMDiffOn hpair
  exact hresult.congr fun p hp => by
    rfl

/-- The exact affine formula identifies the Maurer--Cartan pullback with a smooth difference. -/
theorem associatedMaurerCartanPullback_eq_gaugePullback_sub_adjoint
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gauge.associatedMaurerCartanPullback =
      gaugePullbackForm gauge connection -
        adjointTransformedConnectionForm gauge connection := by
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  rw [show v = fun _ => v 0 by funext i; fin_cases i; rfl]
  change gauge.associatedMaurerCartanPullback.evalOne p (v 0) =
    (gaugePullbackForm gauge connection).evalOne p (v 0) -
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        (connection.pointwise.form.evalOne p (v 0))
  rw [gaugePullbackForm_evalOne_affine]
  abel

/-- A supplied smooth connection derives smoothness of the unchanged associated Maurer--Cartan
pullback through the exact affine identity. -/
theorem SmoothGaugeTransformation.associatedMaurerCartanPullback_isSmooth_of_connection
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gauge.associatedMaurerCartanPullback.IsSmooth (groupLieAlgebraModelEquiv IG) := by
  rw [associatedMaurerCartanPullback_eq_gaugePullback_sub_adjoint gauge connection]
  intro s fields fields_smooth
  have hpull := gaugePullbackForm_isSmooth gauge connection s fields fields_smooth
  have hadjoint := adjointTransformedConnectionForm_isSmooth gauge connection
    s fields fields_smooth
  convert hpull.sub hadjoint using 1
  funext p
  simp [adjointTransformedConnectionForm]

/-- Bundle the exact existing associated Maurer--Cartan carrier as a smooth form, using the supplied
connection only to derive regularity. -/
noncomputable def SmoothGaugeTransformation.associatedMaurerCartanPullbackSmoothFormUsingConnection
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1 where
  toForm := gauge.associatedMaurerCartanPullback
  smooth := gauge.associatedMaurerCartanPullback_isSmooth_of_connection connection

/-- Smooth bundling preserves the exact pointwise Maurer--Cartan carrier definitionally. -/
@[simp] theorem SmoothGaugeTransformation.associatedMaurerCartanPullbackSmoothFormUsingConnection_toForm
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    (gauge.associatedMaurerCartanPullbackSmoothFormUsingConnection connection).toForm =
      gauge.associatedMaurerCartanPullback := rfl

end
end YangMills.Geometry
