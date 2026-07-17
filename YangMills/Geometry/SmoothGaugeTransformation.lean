/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleMap
import YangMills.Geometry.SmoothPrincipalBundle

/-!
# Smooth gauge transformations

A smooth gauge transformation is an algebraic bundle automorphism over the identity whose total
map and inverse are smooth. It is tied to one fixed smooth principal bundle.
-/

namespace YangMills.Geometry

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

/-- A smooth gauge automorphism of one fixed smooth principal bundle. -/
@[ext]
structure SmoothGaugeTransformation
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) where
  /-- Underlying algebraic automorphism over the identity base map. -/
  toGauge : TorsorGaugeTransformation torsor
  /-- Smoothness of the total-space automorphism. -/
  smooth : ContMDiff IP IP ∞ toGauge
  /-- Smoothness of its inverse. -/
  inverse_smooth : ContMDiff IP IP ∞ toGauge.toEquiv.symm

namespace SmoothGaugeTransformation

variable {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

instance : CoeFun (SmoothGaugeTransformation smoothBundle) fun _ => P → P :=
  ⟨fun gauge => gauge.toGauge⟩

/-- Identity smooth gauge transformation. -/
def identity (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) :
    SmoothGaugeTransformation smoothBundle where
  toGauge := 1
  smooth := contMDiff_id
  inverse_smooth := contMDiff_id

/-- Composition, with `second` applied first. -/
def comp (first second : SmoothGaugeTransformation smoothBundle) :
    SmoothGaugeTransformation smoothBundle where
  toGauge := first.toGauge * second.toGauge
  smooth := first.smooth.comp second.smooth
  inverse_smooth := second.inverse_smooth.comp first.inverse_smooth

/-- Inverse smooth gauge transformation. -/
def inverse (gauge : SmoothGaugeTransformation smoothBundle) :
    SmoothGaugeTransformation smoothBundle where
  toGauge := TorsorGaugeTransformation.inverse gauge.toGauge
  smooth := gauge.inverse_smooth
  inverse_smooth := by
    change ContMDiff IP IP ∞ gauge.toGauge.toEquiv.symm.symm
    simpa using gauge.smooth

instance : Group (SmoothGaugeTransformation smoothBundle) where
  one := identity smoothBundle
  mul := comp
  inv := inverse
  mul_assoc a b c := by
    apply SmoothGaugeTransformation.ext
    exact mul_assoc a.toGauge b.toGauge c.toGauge
  one_mul a := by
    apply SmoothGaugeTransformation.ext
    exact one_mul a.toGauge
  mul_one a := by
    apply SmoothGaugeTransformation.ext
    exact mul_one a.toGauge
  inv_mul_cancel a := by
    apply SmoothGaugeTransformation.ext
    exact inv_mul_cancel a.toGauge

/-- A smooth gauge transformation preserves the bundle projection. -/
theorem preserves_projection (gauge : SmoothGaugeTransformation smoothBundle) (p : P) :
    torsor.projection (gauge p) = torsor.projection p :=
  gauge.toGauge.projection_preserving p

/-- A smooth gauge transformation remains equivariant for the right structure-group action. -/
theorem rightAction_equivariant (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (g : G) :
    gauge (torsor.rightAction p g) = torsor.rightAction (gauge p) g :=
  gauge.toGauge.equivariant p g

/-- Evaluation of the smooth gauge identity. -/
@[simp]
theorem identity_apply (p : P) : (1 : SmoothGaugeTransformation smoothBundle) p = p :=
  rfl

/-- Smooth gauge multiplication evaluates as composition. -/
@[simp]
theorem mul_apply (first second : SmoothGaugeTransformation smoothBundle) (p : P) :
    (first * second) p = first (second p) :=
  rfl

/-- Smooth gauge inversion evaluates through the inverse algebraic gauge equivalence. -/
@[simp]
theorem inv_apply (gauge : SmoothGaugeTransformation smoothBundle) (p : P) :
    gauge⁻¹ p = gauge.toGauge.toEquiv.symm p :=
  rfl

end SmoothGaugeTransformation

end YangMills.Geometry
