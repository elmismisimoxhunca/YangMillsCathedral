/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionGaugePullback

/-!
# Hostile probes for gauge pullback of principal connections

These probes lock the transformed form to the exact gauge tangent map, preserve both principal
connection laws, and reject reversal of the contravariant composition order. Curvature covariance
and action invariance are intentionally outside this surface.
-/

namespace YangMills.Geometry.PrincipalConnectionGaugePullback.Probes

open scoped Manifold ContDiff

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The transformed form evaluates the original form on the exact gauge tangent map. -/
theorem exact_gauge_tangent_pullback
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p) :
    (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      connection.pointwise.form.evalOne (gauge p) (mfderiv IP IP gauge p v) := by
  rfl

/-- Fundamental vertical vectors retain their exact Lie-algebra generator. -/
theorem exact_fundamental_vector_transport
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (X : GroupLieAlgebra IG G) :
    mfderiv IP IP gauge p (principalFundamentalVector smoothBundle p X) =
      principalFundamentalVector smoothBundle (gauge p) X :=
  gauge_mfderiv_principalFundamentalVector gauge p X

/-- Gauge pullback is genuinely another principal connection, retaining vertical normalization. -/
theorem exact_transformed_vertical_normalization
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (X : GroupLieAlgebra IG G) :
    (gaugePullbackConnection gauge connection).pointwise.form.evalOne p
        (principalFundamentalVector smoothBundle p X) = X :=
  (gaugePullbackConnection gauge connection).vertical_normalization p X

/-- Gauge pullback retains exact right-adjoint equivariance. -/
theorem exact_transformed_right_equivariance
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (g : G) (v : TangentSpace IP p) :
    (gaugePullbackConnection gauge connection).pointwise.form.evalOne
        (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g v) =
      YangMills.Mathematics.lieGroupAdjoint IG g⁻¹
        ((gaugePullbackConnection gauge connection).pointwise.form.evalOne p v) :=
  (gaugePullbackConnection gauge connection).right_equivariant p g v

/-- Pullback by the identity is definitionally coherent with the original connection. -/
theorem exact_identity_pullback
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackConnection (1 : SmoothGaugeTransformation smoothBundle) connection = connection :=
  gaugePullbackConnection_one connection

/-- Composition is locked to contravariant pullback order. -/
theorem exact_contravariant_composition
    (first second : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackConnection (first * second) connection =
      gaugePullbackConnection second (gaugePullbackConnection first connection) :=
  gaugePullbackConnection_mul first second connection

/-- The covariant/reversed order is rejected whenever the two iterated pullbacks differ. -/
theorem reversed_composition_blocked_when_distinct
    (first second : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (orders_differ :
      gaugePullbackConnection first (gaugePullbackConnection second connection) ≠
        gaugePullbackConnection second (gaugePullbackConnection first connection))
    (wrong : gaugePullbackConnection (first * second) connection =
      gaugePullbackConnection first (gaugePullbackConnection second connection)) : False :=
  orders_differ (wrong.symm.trans (gaugePullbackConnection_mul first second connection))

/-- A tangent transport that changes the vertical generator cannot define this gauge pullback. -/
theorem changed_vertical_generator_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (X : GroupLieAlgebra IG G)
    (wrong : mfderiv IP IP gauge p (principalFundamentalVector smoothBundle p X) ≠
      principalFundamentalVector smoothBundle (gauge p) X) : False :=
  wrong (gauge_mfderiv_principalFundamentalVector gauge p X)

end

end YangMills.Geometry.PrincipalConnectionGaugePullback.Probes
