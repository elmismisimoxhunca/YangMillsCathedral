/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixRepresentationInverse

/-!
# Hostile probes for unitary representation inverses
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixRepresentationInverse
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitary : ∀ g, star (ρ g) * ρ g = 1)

include unitary in
/-- The inverse is the exact conjugate transpose of the same representation matrix. -/
theorem exact_inverse_matrix (g : G) :
    ρ (g⁻¹) = Matrix.conjTranspose (ρ g) :=
  unitaryMatrixRepresentation_inv_eq_conjTranspose ρ unitary g

include unitary in
/-- Row and column are necessarily exchanged under inversion. -/
theorem exact_inverse_entry (g : G) (row column : Fin n) :
    ρ (g⁻¹) row column = star (ρ g column row) :=
  unitaryMatrixRepresentation_inv_apply ρ unitary g row column

include unitary in
/-- The full complex character, not merely its real part, has the exact conjugation law. -/
theorem exact_inverse_character (g : G) :
    Matrix.trace (ρ (g⁻¹)) = star (Matrix.trace (ρ g)) :=
  unitaryMatrixRepresentation_trace_inv ρ unitary g

include unitary in
/-- Hostile probe: omitting the transpose forces the corresponding entries to agree. -/
theorem untransposed_inverse_requires_entry_equality
    (g : G) (row column : Fin n)
    (wrong : ρ (g⁻¹) row column = star (ρ g row column)) :
    star (ρ g column row) = star (ρ g row column) := by
  rw [← wrong]
  exact (unitaryMatrixRepresentation_inv_apply
    ρ unitary g row column).symm

end

end Probes
end UnitaryMatrixRepresentationInverse
end Mathematics
end YangMills
