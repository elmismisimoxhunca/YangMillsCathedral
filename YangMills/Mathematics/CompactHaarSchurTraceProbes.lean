/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactHaarSchurTrace

/-!
# Hostile probes for compact Haar–Schur trace normalization
-/

namespace YangMills
namespace Mathematics
namespace CompactHaarSchurTrace
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)

include hρ in
/-- Conjugation averaging preserves the exact original matrix trace. -/
theorem exact_trace_preservation :
    Matrix.trace (compactHaarIntertwinerAverage ρ ρ A) = Matrix.trace A :=
  compactHaarIntertwinerAverage_trace_self ρ hρ A

include hρ in
/-- Under irreducibility, no unrelated scalar can replace the exact dimension-normalized one. -/
theorem exact_undivided_scalar_normalization
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    (n : ℂ) * compactHaarSchurScalar ρ hρ A = Matrix.trace A :=
  natCast_mul_compactHaarSchurScalar_eq_trace ρ hρ A

include hρ in
/-- Positive dimension permits exact division by the representation dimension. -/
theorem exact_positive_dimension_scalar
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    compactHaarSchurScalar ρ hρ A =
      (n : ℂ)⁻¹ * Matrix.trace A :=
  compactHaarSchurScalar_eq_inv_natCast_mul_trace ρ hρ A dimension_pos

include hρ in
/-- Hostile probe: a changed Schur scalar contradicts the exact trace normalization. -/
theorem changed_scalar_blocked
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (candidate : ℂ)
    (candidate_eq : compactHaarIntertwinerAverage ρ ρ A =
      candidate • (1 : Matrix (Fin n) (Fin n) ℂ))
    (changed : (n : ℂ) * candidate ≠ Matrix.trace A) : False := by
  apply changed
  have traceEquality := congrArg Matrix.trace candidate_eq
  rw [compactHaarIntertwinerAverage_trace_self ρ hρ A] at traceEquality
  simpa [Matrix.trace, mul_comm] using traceEquality.symm

end

end Probes
end CompactHaarSchurTrace
end Mathematics
end YangMills
