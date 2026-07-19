/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTopologicalDoubleCover

/-!
# Exact topological-group laws on affine Poincaré kinematics

Streater–Wightman printed p. 14, equation `(1-22)`, gives the affine semidirect-product law and its
action `x ↦ Λx+a`. Closure of the proof-carrying proper-orthochronous carrier requires future-cone
mathematics not yet derived in this project. This module therefore isolates an uninhabited acceptance
interface for the group law.

The supplied law is not arbitrary: its identity is the exact affine identity, multiplication must
act by exact composition, and it must form a topological group for the canonical target topology.
No concrete group-law inhabitant or `SL(2,ℂ)` construction is provided.
-/

namespace YangMills.Minkowski

/-- Exact action-compatible topological-group structure on proper-orthochronous affine kinematics. -/
structure ProperOrthochronousPoincareTargetGroupData (d : EuclideanDimension) where
  /-- Named group law; it is not installed globally. -/
  group : Group (ProperOrthochronousPoincareTransformation d)
  /-- Its identity is the exact previously defined affine identity. -/
  one_eq_identity :
    @One.one (ProperOrthochronousPoincareTransformation d) group.toOne =
      ProperOrthochronousPoincareTransformation.identity d
  /-- Multiplication is exact affine-action composition in source order. -/
  mul_act : ∀ first second x,
    (@Mul.mul (ProperOrthochronousPoincareTransformation d) group.toMul first second).act x =
      first.act (second.act x)
  /-- The named group law is continuous for the canonical coordinate topology. -/
  topologicalGroup :
    @IsTopologicalGroup (ProperOrthochronousPoincareTransformation d)
      (properOrthochronousPoincareTopologicalSpace d) group

namespace ProperOrthochronousPoincareTargetGroupData

/-- Exact affine transformations are determined by their action on every spacetime point. -/
theorem transformation_ext_action
    {d : EuclideanDimension}
    {first second : ProperOrthochronousPoincareTransformation d}
    (action_eq : ∀ x, first.act x = second.act x) :
    first = second := by
  have translation_eq : first.translation = second.translation := by
    simpa [ProperOrthochronousPoincareTransformation.act] using action_eq 0
  have linear_eq : first.lorentz.linear = second.lorentz.linear := by
    apply LinearEquiv.ext
    intro x
    have at_x := action_eq x
    simp only [ProperOrthochronousPoincareTransformation.act, translation_eq] at at_x
    exact add_right_cancel at_x
  apply properOrthochronousPoincareCoordinate_injective d
  apply Prod.ext
  · exact congrArg (fun linear : Spacetime d ≃ₗ[ℝ] Spacetime d =>
      (linear : Spacetime d → Spacetime d)) linear_eq
  · exact translation_eq

/-- The named multiplication is uniquely determined by exact affine action composition. -/
theorem mul_eq_of_same_action
    {d : EuclideanDimension}
    (data : ProperOrthochronousPoincareTargetGroupData d)
    (first second candidate : ProperOrthochronousPoincareTransformation d)
    (candidate_act : ∀ x, candidate.act x = first.act (second.act x)) :
    candidate = @Mul.mul _ data.group.toMul first second := by
  apply transformation_ext_action
  intro x
  rw [data.mul_act]
  exact candidate_act x

/-- Multiplication is continuous for the exact named group law. -/
theorem continuous_mul
    {d : EuclideanDimension}
    (data : ProperOrthochronousPoincareTargetGroupData d) :
    @Continuous
      ((ProperOrthochronousPoincareTransformation d) ×
        ProperOrthochronousPoincareTransformation d)
      (ProperOrthochronousPoincareTransformation d)
      inferInstance inferInstance
      (fun pair => @Mul.mul _ data.group.toMul pair.1 pair.2) := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
  letI : IsTopologicalGroup (ProperOrthochronousPoincareTransformation d) :=
    data.topologicalGroup
  exact data.topologicalGroup.continuous_mul

/-- The exact two-sheet cover projection becomes a bundled group homomorphism for the named target
law. Multiplicativity is derived from the two independently exact action-composition laws. -/
noncomputable def projectionMonoidHom
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (data : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
    G →* ProperOrthochronousPoincareTransformation d := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
  exact
    { toFun := cover.projection
      map_one' := by
        calc
          cover.projection 1 = ProperOrthochronousPoincareTransformation.identity d :=
            cover.projection_one
          _ = @One.one _ data.group.toOne := data.one_eq_identity.symm
      map_mul' := by
        intro first second
        apply transformation_ext_action
        intro x
        change (cover.projection (first * second)).act x =
          (@Mul.mul _ data.group.toMul (cover.projection first) (cover.projection second)).act x
        calc
          (cover.projection (first * second)).act x =
              (cover.projection first).act ((cover.projection second).act x) :=
            cover.projection_mul_action first second x
          _ = (@Mul.mul _ data.group.toMul
              (cover.projection first) (cover.projection second)).act x :=
            (data.mul_act (cover.projection first) (cover.projection second) x).symm }

@[simp] theorem projectionMonoidHom_apply
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (data : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)
    (g : G) :
    letI : Group (ProperOrthochronousPoincareTransformation d) := data.group
    data.projectionMonoidHom cover g = cover.projection g := by
  rfl

end ProperOrthochronousPoincareTargetGroupData

end YangMills.Minkowski
