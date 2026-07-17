/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothGaugeTransformation

/-!
# Hostile probes for smooth gauge transformations

The smooth and inverse-smooth requirements are isolated from the inherited algebraic projection and
equivariance laws.
-/

namespace YangMills.Geometry.Probes

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

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

/-- A nonsmooth algebraic gauge automorphism cannot pass the smooth layer. -/
theorem nonsmooth_gaugeTransformation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (nonsmooth : ¬ContMDiff IP IP ∞ gauge.toGauge) : False :=
  nonsmooth gauge.smooth

/-- Smoothness of the forward map cannot substitute for smoothness of the inverse. -/
theorem nonsmooth_inverse_gaugeTransformation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (nonsmooth : ¬ContMDiff IP IP ∞ gauge.toGauge.toEquiv.symm) : False :=
  nonsmooth gauge.inverse_smooth

/-- The smooth wrapper cannot disconnect an automorphism from the bundle projection. -/
theorem base_moving_smoothGaugeTransformation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (movesBase : torsor.projection (gauge p) ≠ torsor.projection p) : False :=
  movesBase (gauge.preserves_projection p)

/-- The smooth wrapper retains right-action equivariance. -/
theorem nonequivariant_smoothGaugeTransformation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (g : G)
    (mismatch : gauge (torsor.rightAction p g) ≠ torsor.rightAction (gauge p) g) : False :=
  mismatch (gauge.rightAction_equivariant p g)

/-- The smooth gauge identity is a concrete inhabitant for every smooth principal bundle. -/
theorem identity_smoothGaugeTransformation_exists :
    Nonempty (SmoothGaugeTransformation smoothBundle) :=
  ⟨1⟩

/-- Smooth gauge inversion undoes the original transformation pointwise. -/
theorem inverse_smoothGaugeTransformation_undoes
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) :
    gauge⁻¹ (gauge p) = p :=
  gauge.toGauge.toEquiv.symm_apply_apply p

end YangMills.Geometry.Probes
