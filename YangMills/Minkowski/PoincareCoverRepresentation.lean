/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareKinematics
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Bases

/-!
# Poincaré lift/pre-cover and strongly continuous unitary representation interfaces

Streater–Wightman, printed p. 14, equation `(1-23)`, describes the inhomogeneous `SL(2,ℂ)` cover;
printed p. 97, axiom `0`, requires one continuous unitary representation on the physical Hilbert
space. This module packages a weaker lift/pre-cover interface and the representation requirements
without constructing either. The lift interface does not claim a topological covering projection:
the affine target has no topology here, and no local-homeomorphism, discrete-kernel, or covering-map
law is asserted. Constructing the actual `SL(2,ℂ)` cover remains explicit debt.

The lift projection is connected to the exact affine kinematics, including all translations. The
unitary representation is a single group homomorphism and is strongly continuous on every Hilbert
vector. Its physical translation subgroup is derived from that same homomorphism; no disconnected
surrogate translation representation is accepted.

No vacuum, generator, spectral measure, field, Wightman theory, existence theorem, or mass gap is
introduced here.
-/

namespace YangMills.Minkowski

/-- A topological-group lift/pre-cover interface over proper-orthochronous affine kinematics.

This is intentionally weaker than a topological covering projection. -/
structure ProperOrthochronousPoincareLiftData
    (d : EuclideanDimension) (G : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- Projection from the lift group to exact affine Poincaré kinematics. -/
  projection : G → ProperOrthochronousPoincareTransformation d
  /-- Lift-group identity projects to affine identity. -/
  projection_one : projection 1 = ProperOrthochronousPoincareTransformation.identity d
  /-- Projected multiplication composes the exact affine actions in the same order. -/
  projection_mul_action : ∀ g h x,
    (projection (g * h)).act x = (projection g).act ((projection h).act x)
  /-- Every exact proper-orthochronous affine transformation has a lift. -/
  projection_surjective : Function.Surjective projection
  /-- The additive Minkowski translation group mapped into the lift group. -/
  translation : Multiplicative (Spacetime d) →* G
  /-- Translation lifts project to the exact pure affine translations. -/
  projection_translation : ∀ a,
    projection (translation (Multiplicative.ofAdd a)) =
      ProperOrthochronousPoincareTransformation.pureTranslation d a
  /-- The translation subgroup embedding is continuous. -/
  translation_continuous : Continuous translation

/-- One strongly continuous unitary representation of the same lift group on one separable,
complete complex inner-product space. -/
structure StronglyContinuousUnitaryPoincareRepresentation
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (cover : ProperOrthochronousPoincareLiftData d G)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] where
  /-- The single physical unitary group homomorphism. -/
  unitary : G →* (H ≃ₗᵢ[ℂ] H)
  /-- Strong continuity on every physical Hilbert vector. -/
  strongly_continuous : ∀ ψ : H, Continuous (fun g => unitary g ψ)

/-- Physical translations are restrictions of the same lift-group representation. -/
def StronglyContinuousUnitaryPoincareRepresentation.translationUnitary
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H)
    (a : Spacetime d) : H ≃ₗᵢ[ℂ] H :=
  U.unitary (cover.translation (Multiplicative.ofAdd a))

@[simp] theorem StronglyContinuousUnitaryPoincareRepresentation.unitary_one
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) :
    U.unitary 1 = LinearIsometryEquiv.refl ℂ H := by
  exact U.unitary.map_one

@[simp] theorem StronglyContinuousUnitaryPoincareRepresentation.unitary_mul
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) (g h : G) :
    U.unitary (g * h) = U.unitary g * U.unitary h :=
  U.unitary.map_mul g h

/-- Additive spacetime translations map injectively into the lift group. -/
theorem ProperOrthochronousPoincareLiftData.translation_ofAdd_injective
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (lift : ProperOrthochronousPoincareLiftData d G) :
    Function.Injective (fun a : Spacetime d => lift.translation (Multiplicative.ofAdd a)) := by
  intro a b h
  have hprojection := congrArg lift.projection h
  rw [lift.projection_translation, lift.projection_translation] at hprojection
  exact congrArg ProperOrthochronousPoincareTransformation.translation hprojection

/-- Physical translation unitaries obey the additive spacetime group law through the same
Poincaré representation. -/
theorem StronglyContinuousUnitaryPoincareRepresentation.translationUnitary_add
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H)
    (a b : Spacetime d) :
    U.translationUnitary (a + b) = U.translationUnitary a * U.translationUnitary b := by
  change U.unitary (cover.translation (Multiplicative.ofAdd (a + b))) =
    U.unitary (cover.translation (Multiplicative.ofAdd a)) *
      U.unitary (cover.translation (Multiplicative.ofAdd b))
  rw [show Multiplicative.ofAdd (a + b) =
    Multiplicative.ofAdd a * Multiplicative.ofAdd b by rfl]
  rw [cover.translation.map_mul, U.unitary.map_mul]

/-- The derived physical translation representation is strongly continuous. -/
theorem StronglyContinuousUnitaryPoincareRepresentation.translation_stronglyContinuous
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {cover : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation cover H) (ψ : H) :
    Continuous (fun a : Spacetime d => U.translationUnitary a ψ) := by
  exact (U.strongly_continuous ψ).comp
    (cover.translation_continuous.comp continuous_ofAdd)

end YangMills.Minkowski
