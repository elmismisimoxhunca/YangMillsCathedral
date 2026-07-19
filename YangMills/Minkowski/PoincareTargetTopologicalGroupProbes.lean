/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTargetTopologicalGroup

/-!
# Hostile probes for the named affine Poincaré topological-group law

These probes lock the exact identity, affine action composition, uniqueness from action, and
continuity. They do not construct the group law.
-/

namespace YangMills.Minkowski.PoincareTargetTopologicalGroup.Probes

open YangMills
open YangMills.Minkowski

variable (d : EuclideanDimension)
    (data : ProperOrthochronousPoincareTargetGroupData d)

/-- The named identity cannot differ from the exact affine identity. -/
example :
    @One.one (ProperOrthochronousPoincareTransformation d) data.group.toOne =
      ProperOrthochronousPoincareTransformation.identity d :=
  data.one_eq_identity

/-- Named multiplication acts by exact affine composition in source order. -/
example (first second : ProperOrthochronousPoincareTransformation d) (x : Spacetime d) :
    (@Mul.mul _ data.group.toMul first second).act x =
      first.act (second.act x) :=
  data.mul_act first second x

/-- No disconnected candidate with a different action can replace multiplication. -/
example (first second candidate : ProperOrthochronousPoincareTransformation d)
    (candidate_act : ∀ x, candidate.act x = first.act (second.act x)) :
    candidate = @Mul.mul _ data.group.toMul first second :=
  data.mul_eq_of_same_action first second candidate candidate_act

/-- Multiplication is continuous for the exact canonical target topology. -/
example :
    @Continuous
      ((ProperOrthochronousPoincareTransformation d) ×
        ProperOrthochronousPoincareTransformation d)
      (ProperOrthochronousPoincareTransformation d)
      inferInstance inferInstance
      (fun pair => @Mul.mul _ data.group.toMul pair.1 pair.2) :=
  data.continuous_mul

/-- For every exact double cover, the projection is a bundled homomorphism into this named target
law. -/
noncomputable example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) (first second : G) :
    letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
    data.projectionMonoidHom cover (first * second) =
      data.projectionMonoidHom cover first * data.projectionMonoidHom cover second := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
  exact (data.projectionMonoidHom cover).map_mul first second

/-- Equality of affine actions forces equality of transformations, blocking proof-field surrogates. -/
example (first second : ProperOrthochronousPoincareTransformation d)
    (action_eq : ∀ x, first.act x = second.act x) :
    first = second :=
  ProperOrthochronousPoincareTargetGroupData.transformation_ext_action action_eq

end YangMills.Minkowski.PoincareTargetTopologicalGroup.Probes
