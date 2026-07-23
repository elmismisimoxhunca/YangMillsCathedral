/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationExplicitUnitarization
import YangMills.Mathematics.UnitaryMatrixDualCharacterTransport

/-!
# Hostile probes for explicit compact-representation unitarization
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationExplicitUnitarization
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)

/-- The conjugated matrix retains the exact `U ρ(g) U⁻¹` order. -/
theorem exact_conjugation_order (g : G) :
    compactRepresentationUnitarizedRepresentation ρ hρ g =
      LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).toLinearMap *
        ρ g * LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm.toLinearMap :=
  compactRepresentationUnitarizedRepresentation_eq_conjugation ρ hρ g

/-- Hostile orientation probe: changing the exact conjugated matrix is contradictory. -/
theorem changed_conjugation_order_blocked
    (g : G)
    (changed : compactRepresentationUnitarizedRepresentation ρ hρ g ≠
      LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).toLinearMap *
        ρ g * LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm.toLinearMap) : False :=
  changed (compactRepresentationUnitarizedRepresentation_eq_conjugation ρ hρ g)

/-- The unitarized representation is genuinely continuous. -/
theorem exact_unitarized_continuity :
    Continuous (compactRepresentationUnitarizedRepresentation ρ hρ) :=
  continuous_compactRepresentationUnitarizedRepresentation ρ hρ

/-- Exact action probe: the target action is the selected coordinate transport of the original
action on the inverse-transported vector. -/
theorem exact_unitarized_action (g : G) (vector : Fin n → ℂ) :
    Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) vector =
      compactRepresentationUnitarizingLinearEquiv ρ hρ
        (Matrix.mulVec (ρ g)
          ((compactRepresentationUnitarizingLinearEquiv ρ hρ).symm vector)) :=
  compactRepresentationUnitarizedRepresentation_action ρ hρ g vector

/-- Exact pairing probe: the conjugated matrix preserves the standard coordinate Hermitian
pairing. -/
theorem exact_standard_pairing_invariance
    (g : G) (first second : Fin n → ℂ) :
    coordinateHermitianPairing
        (Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) first)
        (Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) second) =
      coordinateHermitianPairing first second :=
  compactRepresentationUnitarizedRepresentation_pairing ρ hρ g first second

/-- The resulting representation satisfies the literal standard-coordinate unitary equation. -/
theorem exact_unitary_equation (g : G) :
    star (compactRepresentationUnitarizedRepresentation ρ hρ g) *
      compactRepresentationUnitarizedRepresentation ρ hρ g = 1 :=
  compactRepresentationUnitarizedRepresentation_unitary ρ hρ g

/-- Hostile unitary probe: a changed one-sided unitary equation is impossible. -/
theorem changed_unitary_equation_blocked
    (g : G)
    (changed : star (compactRepresentationUnitarizedRepresentation ρ hρ g) *
      compactRepresentationUnitarizedRepresentation ρ hρ g ≠ 1) : False :=
  changed (compactRepresentationUnitarizedRepresentation_unitary ρ hρ g)

/-- Equivalence coherence probe: the selected coordinate map is exactly the underlying map of the
representation equivalence. -/
theorem exact_representation_equivalence_carrier (vector : Fin n → ℂ) :
    compactRepresentationUnitarizingRepresentationEquiv ρ hρ vector =
      compactRepresentationUnitarizingLinearEquiv ρ hρ vector := by
  rfl

/-- Trace characters are unchanged by the explicit unitarization equivalence. -/
theorem exact_unitarized_character (g : G) :
    Matrix.trace (ρ g) =
      Matrix.trace (compactRepresentationUnitarizedRepresentation ρ hρ g) :=
  matrixRepresentation_trace_eq_of_equiv ρ
    (compactRepresentationUnitarizedRepresentation ρ hρ)
    (compactRepresentationUnitarizingRepresentationEquiv ρ hρ) g

/-- Dimension-zero probe: explicit unitarization and its unitary equation require no positive
matrix-dimension premise. -/
theorem zero_dimension_unitary
    (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀) (g : G) :
    star (compactRepresentationUnitarizedRepresentation ρ₀ hρ₀ g) *
      compactRepresentationUnitarizedRepresentation ρ₀ hρ₀ g = 1 :=
  compactRepresentationUnitarizedRepresentation_unitary ρ₀ hρ₀ g

end

end Probes
end CompactRepresentationExplicitUnitarization
end Mathematics
end YangMills
