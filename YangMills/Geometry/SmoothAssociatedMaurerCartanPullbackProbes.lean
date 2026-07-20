/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothAssociatedMaurerCartanPullback

/-!
# Hostile probes for smooth associated Maurer--Cartan pullbacks
-/

namespace YangMills.Geometry.SmoothAssociatedMaurerCartanPullback.Probes

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

/-- The adjoint-transformed term uses the same connection and exact inverse adjoint factor. -/
theorem exact_adjoint_transformed_evaluation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : Fin 1 → TangentSpace IP p) :
    adjointTransformedConnectionForm gauge connection p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        (connection.pointwise.form p v) :=
  adjointTransformedConnectionForm_apply gauge connection p v

/-- Joint adjoint and connection regularity derive smoothness rather than storing it. -/
theorem exact_adjoint_transformed_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    (adjointTransformedConnectionForm gauge connection).IsSmooth
      (groupLieAlgebraModelEquiv IG) :=
  adjointTransformedConnectionForm_isSmooth gauge connection

/-- The associated Maurer--Cartan pullback is exactly the affine difference of two smooth terms. -/
theorem exact_affine_difference
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gauge.associatedMaurerCartanPullback =
      gaugePullbackForm gauge connection -
        adjointTransformedConnectionForm gauge connection :=
  associatedMaurerCartanPullback_eq_gaugePullback_sub_adjoint gauge connection

/-- A supplied exact smooth connection derives smoothness of the unchanged Maurer--Cartan carrier. -/
theorem exact_maurerCartan_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gauge.associatedMaurerCartanPullback.IsSmooth (groupLieAlgebraModelEquiv IG) :=
  gauge.associatedMaurerCartanPullback_isSmooth_of_connection connection

/-- Smooth bundling retains exactly the original pointwise form. -/
theorem exact_smooth_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    (gauge.associatedMaurerCartanPullbackSmoothFormUsingConnection connection).toForm =
      gauge.associatedMaurerCartanPullback :=
  gauge.associatedMaurerCartanPullbackSmoothFormUsingConnection_toForm connection

/-- A disconnected adjoint term cannot replace the exact same-connection affine difference. -/
theorem unrelated_adjoint_difference_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection other : PrincipalConnectionData smoothBundle)
    (differences_differ :
      gaugePullbackForm gauge connection -
          adjointTransformedConnectionForm gauge connection ≠
        gaugePullbackForm gauge connection -
          adjointTransformedConnectionForm gauge other)
    (wrong : gauge.associatedMaurerCartanPullback =
      gaugePullbackForm gauge connection -
        adjointTransformedConnectionForm gauge other) : False :=
  differences_differ
    ((associatedMaurerCartanPullback_eq_gaugePullback_sub_adjoint
      gauge connection).symm.trans wrong)

/-- A smooth wrapper with a different raw carrier is rejected definitionally. -/
theorem mismatched_smooth_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (wrong :
      (gauge.associatedMaurerCartanPullbackSmoothFormUsingConnection connection).toForm ≠
        gauge.associatedMaurerCartanPullback) : False :=
  wrong (gauge.associatedMaurerCartanPullbackSmoothFormUsingConnection_toForm connection)

end

end YangMills.Geometry.SmoothAssociatedMaurerCartanPullback.Probes
