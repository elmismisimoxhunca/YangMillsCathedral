/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationUnitaryCoordinateRealization
import YangMills.Mathematics.UnitaryMatrixDualCharacterTransport

/-!
# Hostile probes for unitary-coordinate realization
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationUnitaryCoordinateRealization
namespace Probes

open scoped MonoidAlgebra

noncomputable section

universe uG

/-- The group-algebra module equivalence has exactly the original intertwining-map carrier. -/
theorem exact_module_equivalence_carrier
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (equivalence : Representation.Equiv ρ σ) (vector : ρ.asModule) :
    representationEquivAsModuleLinearEquiv equivalence vector = equivalence vector := by
  rfl

/-- Irreducibility transports in both directions across the exact supplied equivalence. -/
theorem exact_irreducibility_transport
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (equivalence : Representation.Equiv ρ σ) :
    Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ :=
  representation_isIrreducible_iff_of_equiv equivalence

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The constructed representation retains the original positive matrix dimension exactly. -/
theorem exact_unitary_dimension
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    ρ.toUnitary.dimension = ρ.dimension :=
  rfl

/-- The constructed matrix representation is continuous. -/
theorem exact_unitary_continuity
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    Continuous ρ.toUnitary.representation :=
  ρ.toUnitary.continuous_representation

/-- The constructed representative satisfies the exact coordinate unitary equation. -/
theorem exact_unitary_law
    (ρ : ContinuousIrreducibleMatrixRepresentation G) (g : G) :
    star (ρ.toUnitary.representation g) * ρ.toUnitary.representation g = 1 :=
  ρ.toUnitary.unitary_representation g

/-- The constructed representative retains irreducibility through the same exact equivalence. -/
theorem exact_unitary_irreducibility
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    Representation.IsIrreducible (matrixRepresentation ρ.toUnitary.representation) :=
  ρ.toUnitary.irreducible_representation

/-- The original and constructed unitary-coordinate representations are explicitly equivalent. -/
theorem exact_unitary_equivalence
    (ρ : ContinuousIrreducibleMatrixRepresentation G) :
    Nonempty (Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation ρ.toUnitary.representation)) :=
  ρ.equivalent_toUnitary

/-- The explicit equivalence preserves the trace character pointwise. -/
theorem exact_unitary_character
    (ρ : ContinuousIrreducibleMatrixRepresentation G) (g : G) :
    Matrix.trace (ρ.representation g) = Matrix.trace (ρ.toUnitary.representation g) :=
  matrixRepresentation_trace_eq_of_equiv ρ.representation ρ.toUnitary.representation
    (compactRepresentationUnitarizingRepresentationEquiv
      ρ.representation ρ.continuous_representation) g

/-- Hostile law probe: failure of the unitary equation contradicts the constructed realization. -/
theorem failed_unitary_law_blocked
    (ρ : ContinuousIrreducibleMatrixRepresentation G) (g : G)
    (failed : star (ρ.toUnitary.representation g) * ρ.toUnitary.representation g ≠ 1) : False :=
  failed (ρ.toUnitary.unitary_representation g)

/-- Re-unitarizing an already unitary bundle cannot change its coordinate-dual class. -/
theorem exact_already_unitary_class
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    ρ.toContinuousIrreducible.unitaryDualClass = unitaryMatrixDualClass ρ :=
  ρ.unitaryDualClass_toContinuousIrreducible

/-- Hostile quotient probe: a changed class for an already-unitary input is contradictory. -/
theorem changed_already_unitary_class_blocked
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (changed : ρ.toContinuousIrreducible.unitaryDualClass ≠ unitaryMatrixDualClass ρ) : False :=
  changed ρ.unitaryDualClass_toContinuousIrreducible

end

end Probes
end CompactRepresentationUnitaryCoordinateRealization
end Mathematics
end YangMills
