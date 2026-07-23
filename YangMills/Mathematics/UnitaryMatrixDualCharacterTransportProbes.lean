/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterTransport

/-!
# Hostile probes for character transport
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterTransport
namespace Probes

noncomputable section

universe uG

/-- Exact transport probe: a representation equivalence preserves the trace character despite
possibly different coordinate dimensions. -/
theorem exact_equivalent_character
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G) :
    Matrix.trace (ρ g) = Matrix.trace (σ g) :=
  matrixRepresentation_trace_eq_of_equiv ρ σ equivalence g

/-- Hostile transport probe: an explicitly changed character value is incompatible with the same
supplied representation equivalence. -/
theorem changed_equivalent_character_blocked
    {G : Type uG} [Monoid G] {m n : ℕ}
    (ρ : G →* Matrix (Fin m) (Fin m) ℂ)
    (σ : G →* Matrix (Fin n) (Fin n) ℂ)
    (equivalence : Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation σ)) (g : G)
    (changed : Matrix.trace (ρ g) ≠ Matrix.trace (σ g)) : False :=
  changed (matrixRepresentation_trace_eq_of_equiv ρ σ equivalence g)

/-- Quotient coherence probe: selecting a noncomputable representative cannot change the trace
character of the bundled presentation that defines the class. -/
theorem selected_representative_character_coherent
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) (g : G) :
    unitaryMatrixDualCharacter (unitaryMatrixDualClass ρ) g =
      Matrix.trace (ρ.representation g) :=
  unitaryMatrixDualCharacter_class_eq ρ g

/-- Hostile quotient probe: a changed selected character contradicts exact class coherence. -/
theorem changed_selected_character_blocked
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) (g : G)
    (changed : unitaryMatrixDualCharacter (unitaryMatrixDualClass ρ) g ≠
      Matrix.trace (ρ.representation g)) : False :=
  changed (unitaryMatrixDualCharacter_class_eq ρ g)

end

end Probes
end UnitaryMatrixDualCharacterTransport
end Mathematics
end YangMills
