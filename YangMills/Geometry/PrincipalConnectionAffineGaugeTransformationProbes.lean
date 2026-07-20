/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation

/-!
# Hostile probes for the affine gauge transformation formula
-/

namespace YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation.Probes

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

/-- The associated one-form is exactly the left-trivialized derivative `g_ϕ⁻¹ dg_ϕ`. -/
theorem exact_associated_maurerCartan_evaluation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (p : P) (v : TangentSpace IP p) :
    gauge.associatedMaurerCartanPullback.evalOne p v =
      leftMaurerCartanApply (gauge.associatedGaugeFunction p)
        (mfderiv IP IG gauge.associatedGaugeFunction p v) :=
  gauge.associatedMaurerCartanPullback_evalOne p v

/-- The two-variable principal action derivative has the exact fixed-translation-plus-vertical split. -/
theorem exact_principalRightAction_derivative_split
    (p : P) (g : G) (v : TangentSpace IP p) (w : TangentSpace IG g) :
    mfderiv (IP.prod IG) IP (fun z : P × G => torsor.rightAction z.1 z.2) (p, g) (v, w) =
      principalRightTranslationDifferential smoothBundle p g v +
        principalFundamentalVector smoothBundle (torsor.rightAction p g)
          (leftMaurerCartanApply g w) :=
  principalRightAction_mfderiv_apply p g v w

/-- The exact gauge tangent decomposition retains both its translated and fundamental summands. -/
theorem exact_gauge_tangent_decomposition
    (gauge : SmoothGaugeTransformation smoothBundle)
    (p : P) (v : TangentSpace IP p) :
    tangentMap IP IP gauge ⟨p, v⟩ =
      (⟨torsor.rightAction p (gauge.associatedGaugeFunction p),
        principalRightTranslationDifferential smoothBundle p
            (gauge.associatedGaugeFunction p) v +
          principalFundamentalVector smoothBundle
            (torsor.rightAction p (gauge.associatedGaugeFunction p))
            (gauge.associatedMaurerCartanApply p v)⟩ : TangentBundle IP P) :=
  gauge.tangentMap_eq_rightTranslation_add_fundamental p v

/-- Freed's affine formula holds for the exact transformed principal connection carrier. -/
theorem exact_affine_connection_formula
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p) :
    (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) +
        gauge.associatedMaurerCartanPullback.evalOne p v :=
  gaugePullbackConnection_form_evalOne_affine gauge connection p v

/-- Omitting a distinguishable Maurer--Cartan term contradicts the exact affine law. -/
theorem omitted_maurerCartan_term_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (term_changes_value :
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v ≠
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v))
    (wrong : (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
        (connection.pointwise.form.evalOne p v)) : False :=
  term_changes_value
    ((gaugePullbackConnection_form_evalOne_affine gauge connection p v).symm.trans wrong)

/-- Replacing the sourced plus sign by a distinguishable minus sign is rejected. -/
theorem wrong_maurerCartan_sign_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (signs_differ :
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v ≠
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) -
          gauge.associatedMaurerCartanPullback.evalOne p v)
    (wrong : (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) -
        gauge.associatedMaurerCartanPullback.evalOne p v) : False :=
  signs_differ
    ((gaugePullbackConnection_form_evalOne_affine gauge connection p v).symm.trans wrong)

/-- An unrelated original connection cannot replace the exact connection on the affine right side
when the resulting values differ. -/
theorem unrelated_connection_affine_formula_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection other : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (values_differ :
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v ≠
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (other.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v)
    (wrong : (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (other.pointwise.form.evalOne p v) +
        gauge.associatedMaurerCartanPullback.evalOne p v) : False :=
  values_differ
    ((gaugePullbackConnection_form_evalOne_affine gauge connection p v).symm.trans wrong)

/-- The non-inverted adjoint factor is rejected whenever it gives a different affine value. -/
theorem wrong_affine_adjoint_inverse_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (factors_differ :
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)⁻¹
          (connection.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v ≠
        lieGroupAdjoint IG (gauge.associatedGaugeFunction p)
          (connection.pointwise.form.evalOne p v) +
          gauge.associatedMaurerCartanPullback.evalOne p v)
    (wrong : (gaugePullbackConnection gauge connection).pointwise.form.evalOne p v =
      lieGroupAdjoint IG (gauge.associatedGaugeFunction p)
          (connection.pointwise.form.evalOne p v) +
        gauge.associatedMaurerCartanPullback.evalOne p v) : False :=
  factors_differ
    ((gaugePullbackConnection_form_evalOne_affine gauge connection p v).symm.trans wrong)

end

end YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation.Probes
