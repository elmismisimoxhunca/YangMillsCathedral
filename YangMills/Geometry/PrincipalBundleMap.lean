/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleTorsor
import Mathlib.Logic.Equiv.Basic

/-!
# Maps and gauge automorphisms of fiberwise principal torsors

This module formalizes the algebraic part of Freed's bundle-map and gauge-transformation
definitions. Smoothness belongs to the later smooth principal-bundle layer and is not claimed here.
-/

namespace YangMills.Geometry

universe uG uB uP uB' uP' uB'' uP''

variable {G : Type uG} [Group G]

/-- A base map and an equivariant total-space map between two fiberwise principal torsors. -/
structure PrincipalBundleTorsorMap
    {B : Type uB} {P : Type uP} {B' : Type uB'} {P' : Type uP'}
    (source : PrincipalBundleTorsorData G B P)
    (target : PrincipalBundleTorsorData G B' P') where
  /-- Map induced on base points. -/
  baseMap : B → B'
  /-- Map on total carriers. -/
  totalMap : P → P'
  /-- The total map covers the declared base map. -/
  projection_commutes : ∀ p, target.projection (totalMap p) = baseMap (source.projection p)
  /-- The total map commutes with the right `G`-actions. -/
  equivariant : ∀ p g, totalMap (source.rightAction p g) = target.rightAction (totalMap p) g

namespace PrincipalBundleTorsorMap

variable
    {B : Type uB} {P : Type uP} {B' : Type uB'} {P' : Type uP'}
    {B'' : Type uB''} {P'' : Type uP''}
    {source : PrincipalBundleTorsorData G B P}
    {middle : PrincipalBundleTorsorData G B' P'}
    {target : PrincipalBundleTorsorData G B'' P''}

/-- Identity map of a fiberwise principal torsor. -/
def id (source : PrincipalBundleTorsorData G B P) : PrincipalBundleTorsorMap source source where
  baseMap := fun b => b
  totalMap := fun p => p
  projection_commutes _ := rfl
  equivariant _ _ := rfl

/-- Composition of torsor maps, with the second argument applied first. -/
def comp (after : PrincipalBundleTorsorMap middle target)
    (before : PrincipalBundleTorsorMap source middle) : PrincipalBundleTorsorMap source target where
  baseMap := after.baseMap ∘ before.baseMap
  totalMap := after.totalMap ∘ before.totalMap
  projection_commutes p := by
    change target.projection (after.totalMap (before.totalMap p)) =
      after.baseMap (before.baseMap (source.projection p))
    rw [after.projection_commutes, before.projection_commutes]
  equivariant p g := by
    change after.totalMap (before.totalMap (source.rightAction p g)) =
      target.rightAction (after.totalMap (before.totalMap p)) g
    rw [before.equivariant, after.equivariant]

/-- Identity bundle maps act identically on the base. -/
@[simp]
theorem id_baseMap_apply (source : PrincipalBundleTorsorData G B P) (b : B) :
    (id source).baseMap b = b :=
  rfl

/-- Identity bundle maps act identically on the total carrier. -/
@[simp]
theorem id_totalMap_apply (source : PrincipalBundleTorsorData G B P) (p : P) :
    (id source).totalMap p = p :=
  rfl

/-- Composition evaluates in the declared after-before order on total carriers. -/
@[simp]
theorem comp_totalMap_apply (after : PrincipalBundleTorsorMap middle target)
    (before : PrincipalBundleTorsorMap source middle) (p : P) :
    (comp after before).totalMap p = after.totalMap (before.totalMap p) :=
  rfl

/-- Composition evaluates in the declared after-before order on bases. -/
@[simp]
theorem comp_baseMap_apply (after : PrincipalBundleTorsorMap middle target)
    (before : PrincipalBundleTorsorMap source middle) (b : B) :
    (comp after before).baseMap b = after.baseMap (before.baseMap b) :=
  rfl

/-- A torsor map sends equal-base points to equal-base points according to its declared base map. -/
theorem maps_sameFiber (map : PrincipalBundleTorsorMap source middle)
    {p q : P} (sameFiber : source.projection p = source.projection q) :
    middle.projection (map.totalMap p) = middle.projection (map.totalMap q) := by
  rw [map.projection_commutes, map.projection_commutes, sameFiber]

end PrincipalBundleTorsorMap

/-- An algebraic gauge transformation is an equivariant automorphism of one fiberwise principal
torsor covering the identity on its base. It is not yet required to be smooth. -/
@[ext]
structure TorsorGaugeTransformation
    {B : Type uB} {P : Type uP} (bundle : PrincipalBundleTorsorData G B P) where
  /-- Invertible map of the total carrier. -/
  toEquiv : P ≃ P
  /-- The automorphism lies over the identity of the base. -/
  projection_preserving : ∀ p, bundle.projection (toEquiv p) = bundle.projection p
  /-- The automorphism commutes with the right group action. -/
  equivariant : ∀ p g, toEquiv (bundle.rightAction p g) = bundle.rightAction (toEquiv p) g

namespace TorsorGaugeTransformation

variable {B : Type uB} {P : Type uP} {bundle : PrincipalBundleTorsorData G B P}

instance : CoeFun (TorsorGaugeTransformation bundle) fun _ => P → P :=
  ⟨fun gauge => gauge.toEquiv⟩

/-- Forget invertibility and view a gauge transformation as a torsor map over the identity base map. -/
def toTorsorMap (gauge : TorsorGaugeTransformation bundle) :
    PrincipalBundleTorsorMap bundle bundle where
  baseMap := fun b => b
  totalMap := gauge
  projection_commutes := gauge.projection_preserving
  equivariant := gauge.equivariant

/-- The forgotten torsor map covers the identity on the base. -/
@[simp]
theorem toTorsorMap_baseMap_apply (gauge : TorsorGaugeTransformation bundle) (b : B) :
    gauge.toTorsorMap.baseMap b = b :=
  rfl

/-- Forgetting to a torsor map preserves pointwise evaluation. -/
@[simp]
theorem toTorsorMap_totalMap_apply (gauge : TorsorGaugeTransformation bundle) (p : P) :
    gauge.toTorsorMap.totalMap p = gauge p :=
  rfl

/-- Identity gauge transformation. -/
def identity (bundle : PrincipalBundleTorsorData G B P) : TorsorGaugeTransformation bundle where
  toEquiv := Equiv.refl P
  projection_preserving _ := rfl
  equivariant _ _ := rfl

/-- Composition, with `second` applied first. -/
def comp (first second : TorsorGaugeTransformation bundle) :
    TorsorGaugeTransformation bundle where
  toEquiv := second.toEquiv.trans first.toEquiv
  projection_preserving p := by
    rw [Equiv.trans_apply, first.projection_preserving, second.projection_preserving]
  equivariant p g := by
    change first.toEquiv (second.toEquiv (bundle.rightAction p g)) =
      bundle.rightAction (first.toEquiv (second.toEquiv p)) g
    rw [second.equivariant, first.equivariant]

/-- Inverse gauge transformation. -/
def inverse (gauge : TorsorGaugeTransformation bundle) : TorsorGaugeTransformation bundle where
  toEquiv := gauge.toEquiv.symm
  projection_preserving p := by
    simpa using (gauge.projection_preserving (gauge.toEquiv.symm p)).symm
  equivariant p g := by
    apply gauge.toEquiv.injective
    rw [gauge.toEquiv.apply_symm_apply, gauge.equivariant, gauge.toEquiv.apply_symm_apply]

instance : Group (TorsorGaugeTransformation bundle) where
  one := identity bundle
  mul := comp
  inv := inverse
  mul_assoc a b c := by
    apply TorsorGaugeTransformation.ext
    apply Equiv.ext
    intro p
    rfl
  one_mul a := by
    apply TorsorGaugeTransformation.ext
    apply Equiv.ext
    intro p
    rfl
  mul_one a := by
    apply TorsorGaugeTransformation.ext
    apply Equiv.ext
    intro p
    rfl
  inv_mul_cancel a := by
    change comp (inverse a) a = identity bundle
    apply TorsorGaugeTransformation.ext
    apply Equiv.ext
    intro p
    exact a.toEquiv.symm_apply_apply p

/-- Evaluation of the identity gauge transformation. -/
@[simp]
theorem identity_apply (p : P) : (1 : TorsorGaugeTransformation bundle) p = p :=
  rfl

/-- Multiplication evaluates as composition. -/
@[simp]
theorem mul_apply (first second : TorsorGaugeTransformation bundle) (p : P) :
    (first * second) p = first (second p) :=
  rfl

/-- Inversion evaluates through the inverse total-space equivalence. -/
@[simp]
theorem inv_apply (gauge : TorsorGaugeTransformation bundle) (p : P) :
    gauge⁻¹ p = gauge.toEquiv.symm p :=
  rfl

end TorsorGaugeTransformation

end YangMills.Geometry
