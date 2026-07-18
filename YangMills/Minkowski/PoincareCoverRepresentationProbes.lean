/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareCoverRepresentation

/-!
# Hostile probes for Poincaré covers and unitary representations

All probes are conditional on supplied lift/pre-cover and representation data. They force projection laws,
nontrivial translations, one unitary homomorphism, and strong continuity of its derived translation
subgroup. No cover or representation is constructed.
-/

namespace YangMills.Minkowski.PoincareCoverRepresentation.Probes

/-- Cover identity projects to exact affine identity. -/
theorem exact_projection_identity
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareLiftData d G) :
    cover.projection 1 = ProperOrthochronousPoincareTransformation.identity d :=
  cover.projection_one

/-- Projected multiplication acts by exact affine composition. -/
theorem exact_projection_multiplication_action
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareLiftData d G) (g h : G)
    (x : Spacetime d) :
    (cover.projection (g * h)).act x =
      (cover.projection g).act ((cover.projection h).act x) :=
  cover.projection_mul_action g h x

/-- Every exact affine transformation has a cover lift. -/
theorem every_affine_transformation_has_lift
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareLiftData d G)
    (p : ProperOrthochronousPoincareTransformation d) :
    ∃ g : G, cover.projection g = p :=
  cover.projection_surjective p

/-- Every additive spacetime translation has a distinct lift-group image. -/
theorem translation_map_is_injective
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (lift : ProperOrthochronousPoincareLiftData d G) :
    Function.Injective
      (fun a : Spacetime d => lift.translation (Multiplicative.ofAdd a)) :=
  lift.translation_ofAdd_injective

/-- The lift of the nonzero time translation cannot collapse to lift-group identity. -/
theorem time_translation_lift_ne_identity
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareLiftData d G) :
    cover.translation (Multiplicative.ofAdd (d.basisVector d.timeIndex)) ≠ 1 := by
  intro hcollapse
  have hprojection := congrArg cover.projection hcollapse
  rw [cover.projection_translation, cover.projection_one] at hprojection
  have haction := congrArg
    (fun p : ProperOrthochronousPoincareTransformation d => p.act 0) hprojection
  simp at haction
  have hquadratic := congrArg d.minkowskiQuadraticForm haction
  rw [d.minkowskiQuadraticForm_time_basisVector] at hquadratic
  simp [EuclideanDimension.minkowskiQuadraticForm] at hquadratic

/-- The unitary homomorphism sends cover identity to Hilbert-space identity. -/
theorem exact_unitary_identity
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) :
    U.unitary 1 = LinearIsometryEquiv.refl ℂ H :=
  U.unitary_one

/-- Cover multiplication is represented by multiplication in the same unitary homomorphism. -/
theorem exact_unitary_multiplication
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) (g h : G) :
    U.unitary (g * h) = U.unitary g * U.unitary h :=
  U.unitary_mul g h

/-- Physical translations obey addition through that same Poincaré representation. -/
theorem exact_translation_unitary_addition
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H)
    (a b : Spacetime d) :
    U.translationUnitary (a + b) = U.translationUnitary a * U.translationUnitary b :=
  U.translationUnitary_add a b

/-- The derived translation subgroup is strongly continuous on every physical vector. -/
theorem exact_translation_strong_continuity
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) (ψ : H) :
    Continuous (fun a : Spacetime d => U.translationUnitary a ψ) :=
  U.translation_stronglyContinuous ψ

end YangMills.Minkowski.PoincareCoverRepresentation.Probes
