/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence
import YangMills.Mathematics.NormalizedCompactHaarMeasure
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Driver Wilson plaquette action

Driver Definition 8.4 defines `Aᵋχ(g) = Zᵋ⁻¹ exp(Re χ(g))`, where `χ` is the character of a
finite-dimensional unitary representation and `Zᵋ` is chosen to normalize the real Haar integral.
This module retains an actual matrix representation and defines its character as its matrix trace.
The supplied normalizer is tied exactly to the integral of the unnormalized character weight, so
normalization is derived rather than stored independently.

No representation, action datum, lattice field, convergence theorem, Yang--Mills theory, or mass
gap is constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uG

/-- A nonzero finite-dimensional unitary matrix representation and its exact trace character. -/
structure FiniteDimensionalUnitaryRepresentationCharacterData
    (G : Type uG) [Group G] [TopologicalSpace G] where
  dimension : ℕ
  dimension_pos : 0 < dimension
  representation : G →* Matrix (Fin dimension) (Fin dimension) ℂ
  representation_continuous : Continuous representation
  representation_unitary : ∀ g,
    star (representation g) * representation g = 1
  /-- Continuity of the actual trace character. -/
  character_continuous : Continuous (fun g => Matrix.trace (representation g))
  /-- Cyclic trace invariance, exposed on the actual trace character. -/
  character_central : ∀ h g,
    Matrix.trace (representation (h * g * h⁻¹)) = Matrix.trace (representation g)
  /-- Unitarity makes the real part of the character invariant under inversion. -/
  character_inv_re : ∀ g,
    (Matrix.trace (representation g⁻¹)).re = (Matrix.trace (representation g)).re

namespace FiniteDimensionalUnitaryRepresentationCharacterData

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The character is definitionally the trace of the same representation. -/
def character (data : FiniteDimensionalUnitaryRepresentationCharacterData G) : G → ℂ :=
  fun g => Matrix.trace (data.representation g)

/-- The unnormalized positive Wilson character weight. -/
def weight (data : FiniteDimensionalUnitaryRepresentationCharacterData G) : G → ℝ :=
  fun g => Real.exp ((data.character g).re)

/-- The Wilson character weight is continuous. -/
theorem weight_continuous
    (data : FiniteDimensionalUnitaryRepresentationCharacterData G) :
    Continuous data.weight :=
  Real.continuous_exp.comp (Complex.continuous_re.comp data.character_continuous)

/-- The Wilson character weight is strictly positive. -/
theorem weight_pos
    (data : FiniteDimensionalUnitaryRepresentationCharacterData G) (g : G) :
    0 < data.weight g :=
  Real.exp_pos _

/-- The Wilson character weight is central. -/
theorem weight_central
    (data : FiniteDimensionalUnitaryRepresentationCharacterData G) (h g : G) :
    data.weight (h * g * h⁻¹) = data.weight g := by
  simp only [weight, character]
  rw [data.character_central h g]

/-- The Wilson character weight is inversion symmetric. -/
theorem weight_inv
    (data : FiniteDimensionalUnitaryRepresentationCharacterData G) (g : G) :
    data.weight g⁻¹ = data.weight g := by
  simp only [weight, character]
  rw [data.character_inv_re g]

end FiniteDimensionalUnitaryRepresentationCharacterData

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Driver's `Zᵋ`, required to be the exact Haar integral of the character weight. The source
notation retains `ε`; exactness forces equal values when the representation is fixed. -/
structure TwoDimensionalWilsonNormalizerData
    (representation : FiniteDimensionalUnitaryRepresentationCharacterData G) where
  normalizer : PositiveLatticeSpacing → ℝ
  normalizer_eq_integral : ∀ spacing,
    normalizer spacing =
      ∫ g, representation.weight g ∂normalizedCompactHaarMeasure G
  normalizer_pos : ∀ spacing, 0 < normalizer spacing

/-- Driver Definition 8.4's exact normalizer. -/
def twoDimensionalWilsonNormalizer
    {representation : FiniteDimensionalUnitaryRepresentationCharacterData G}
    (normalization : TwoDimensionalWilsonNormalizerData representation)
    (spacing : PositiveLatticeSpacing) : ℝ :=
  normalization.normalizer spacing

/-- Driver Definition 8.4: `Zᵋ⁻¹ exp(Re χ(g))`. -/
def twoDimensionalWilsonAction
    {representation : FiniteDimensionalUnitaryRepresentationCharacterData G}
    (normalization : TwoDimensionalWilsonNormalizerData representation)
    (spacing : PositiveLatticeSpacing) : G → ℝ :=
  fun g => (twoDimensionalWilsonNormalizer normalization spacing)⁻¹ * representation.weight g

namespace TwoDimensionalWilsonAction

variable
    {representation : FiniteDimensionalUnitaryRepresentationCharacterData G}
    (normalization : TwoDimensionalWilsonNormalizerData representation)

/-- The action has the exact source formula with the actual trace character. -/
theorem action_formula (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalWilsonAction normalization spacing g =
      (normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (representation.representation g)).re) :=
  rfl

/-- The Wilson action is continuous. -/
theorem action_continuous (spacing : PositiveLatticeSpacing) :
    Continuous (twoDimensionalWilsonAction normalization spacing) :=
  continuous_const.mul representation.weight_continuous

/-- The Wilson action is strictly positive. -/
theorem action_pos (spacing : PositiveLatticeSpacing) (g : G) :
    0 < twoDimensionalWilsonAction normalization spacing g := by
  exact mul_pos (inv_pos.mpr (normalization.normalizer_pos spacing))
    (representation.weight_pos g)

/-- The Wilson action is central. -/
theorem action_central (spacing : PositiveLatticeSpacing) (h g : G) :
    twoDimensionalWilsonAction normalization spacing (h * g * h⁻¹) =
      twoDimensionalWilsonAction normalization spacing g := by
  simp only [twoDimensionalWilsonAction]
  rw [representation.weight_central h g]

/-- The Wilson action is inversion symmetric. -/
theorem action_inv (spacing : PositiveLatticeSpacing) (g : G) :
    twoDimensionalWilsonAction normalization spacing g⁻¹ =
      twoDimensionalWilsonAction normalization spacing g := by
  simp only [twoDimensionalWilsonAction]
  rw [representation.weight_inv g]

/-- The Wilson action is integrable on compact Haar probability. -/
theorem action_integrable (spacing : PositiveLatticeSpacing) :
    Integrable (twoDimensionalWilsonAction normalization spacing)
      (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  have hweight : Integrable representation.weight (normalizedCompactHaarMeasure G) := by
    rcases isCompact_univ.bddAbove_image
      representation.weight_continuous.continuousOn with ⟨bound, hbound⟩
    apply Integrable.of_bound representation.weight_continuous.aestronglyMeasurable bound
    filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_pos (representation.weight_pos g)]
    exact hbound ⟨g, Set.mem_univ g, rfl⟩
  exact hweight.const_mul _

/-- Exact choice of `Zᵋ` derives Driver Definition 7.1's real Haar normalization. -/
theorem action_integral_normalized (spacing : PositiveLatticeSpacing) :
    ∫ g, twoDimensionalWilsonAction normalization spacing g
      ∂normalizedCompactHaarMeasure G = 1 := by
  rw [show twoDimensionalWilsonAction normalization spacing =
      fun g => (normalization.normalizer spacing)⁻¹ * representation.weight g by rfl]
  rw [integral_const_mul, ← normalization.normalizer_eq_integral spacing]
  exact inv_mul_cancel₀ (ne_of_gt (normalization.normalizer_pos spacing))

end TwoDimensionalWilsonAction

end

end YangMills.Dimensions
