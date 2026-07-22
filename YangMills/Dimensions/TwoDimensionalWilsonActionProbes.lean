/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalWilsonAction
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for Driver's Wilson action
-/

namespace YangMills.Dimensions.TwoDimensionalWilsonAction.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (representation : FiniteDimensionalUnitaryRepresentationCharacterData G)
    (normalization : TwoDimensionalWilsonNormalizerData representation)

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The character is the trace of an actual nonzero-dimensional matrix representation. -/
theorem exact_representation_character (g : G) :
    representation.character g = Matrix.trace (representation.representation g) ∧
      0 < representation.dimension :=
  ⟨rfl, representation.dimension_pos⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The same matrix homomorphism is exposed through Mathlib's representation-theory carrier. -/
theorem exact_mathlib_character_bridge (g : G) :
    representation.toRepresentation.character g =
      Matrix.trace (representation.representation g) :=
  representation.toRepresentation_character g

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Character continuity and conjugacy invariance are now independently derived from the matrix
representation rather than relying only on stored fields. -/
theorem exact_derived_character_laws :
    Continuous (fun g => Matrix.trace (representation.representation g)) ∧
      ∀ h g,
        Matrix.trace (representation.representation (h * g * h⁻¹)) =
          Matrix.trace (representation.representation g) :=
  ⟨representation.character_continuous_derived,
    representation.character_central_derived⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Unitarity derives the exact inverse/conjugate-transpose matrix law and full complex character
conjugation, strengthening the stored real-part law. -/
theorem exact_derived_inverse_laws (g : G) :
    representation.representation g⁻¹ =
        Matrix.conjTranspose (representation.representation g) ∧
      Matrix.trace (representation.representation g⁻¹) =
        star (Matrix.trace (representation.representation g)) ∧
      (Matrix.trace (representation.representation g⁻¹)).re =
        (Matrix.trace (representation.representation g)).re :=
  ⟨representation.representation_inv_eq_conjTranspose_derived g,
    representation.character_inv_derived g,
    representation.character_inv_re_derived g⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The supplied representation is genuinely unitary. -/
theorem exact_unitarity (g : G) :
    star (representation.representation g) * representation.representation g = 1 :=
  representation.representation_unitary g

/-- Driver Definition 8.4's formula is retained literally. -/
theorem exact_wilson_formula (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalWilsonAction normalization spacing g =
      (normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (representation.representation g)).re) :=
  action_formula normalization spacing g

/-- The inherited action contract includes continuity, strict positivity, class symmetry,
orientation symmetry, and exact real Haar normalization. -/
theorem exact_action_contract (spacing : PositiveLatticeSpacing) :
    Continuous (twoDimensionalWilsonAction normalization spacing) ∧
      (∀ g : G, 0 < twoDimensionalWilsonAction normalization spacing g) ∧
      (∀ h g : G, twoDimensionalWilsonAction normalization spacing (h * g * h⁻¹) =
        twoDimensionalWilsonAction normalization spacing g) ∧
      (∀ g : G, twoDimensionalWilsonAction normalization spacing g⁻¹ =
        twoDimensionalWilsonAction normalization spacing g) ∧
      (∫ g, twoDimensionalWilsonAction normalization spacing g
        ∂normalizedCompactHaarMeasure G) = 1 :=
  ⟨action_continuous normalization spacing, action_pos normalization spacing,
    action_central normalization spacing, action_inv normalization spacing,
    action_integral_normalized normalization spacing⟩

/-- For a fixed representation, every source-indexed normalizer is forced to the same exact
character-weight integral. -/
theorem exact_normalizer_choice
    (spacing₁ spacing₂ : PositiveLatticeSpacing) :
    normalization.normalizer spacing₁ = normalization.normalizer spacing₂ := by
  rw [normalization.normalizer_eq_integral, normalization.normalizer_eq_integral]

/-- A zero normalizer is rejected by the exact positive source normalization. -/
theorem zero_normalizer_blocked
    (spacing : PositiveLatticeSpacing)
    (claimed : normalization.normalizer spacing = 0) : False :=
  (ne_of_gt (normalization.normalizer_pos spacing)) claimed

/-- The source formula cannot use an arbitrary unrelated character: the action unfolds to the trace
of the stored unitary representation. -/
theorem unrelated_character_requires_equality
    (spacing : PositiveLatticeSpacing) (fakeCharacter : G → ℂ)
    (claimed : twoDimensionalWilsonAction normalization spacing =
      fun g => (normalization.normalizer spacing)⁻¹ * Real.exp ((fakeCharacter g).re)) :
    (fun g => (normalization.normalizer spacing)⁻¹ *
      Real.exp ((Matrix.trace (representation.representation g)).re)) =
      fun g => (normalization.normalizer spacing)⁻¹ * Real.exp ((fakeCharacter g).re) := by
  change twoDimensionalWilsonAction normalization spacing =
    fun g => (normalization.normalizer spacing)⁻¹ * Real.exp ((fakeCharacter g).re)
  exact claimed

/-- A two-dimensional Wilson plaquette action is not a four-dimensional continuum endpoint. -/
theorem wilson_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalWilsonAction.Probes
