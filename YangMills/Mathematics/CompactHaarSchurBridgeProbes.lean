/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactHaarSchurBridge

/-!
# Hostile probes for the compact Haar–Schur bridge
-/

namespace YangMills
namespace Mathematics
namespace CompactHaarSchurBridge
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ)

/-- The bundled map uses the exact Haar-averaged matrix as its underlying linear map. -/
theorem exact_underlying_linear_map :
    (compactHaarIntertwiningMap σ ρ hσ hρ A).toLinearMap =
      Matrix.toLin' (compactHaarIntertwinerAverage σ ρ A) :=
  rfl

include hσ hρ in
/-- The bundled map has the exact source-to-target intertwining orientation. -/
theorem exact_intertwining_orientation (h : G) :
    (compactHaarIntertwiningMap σ ρ hσ hρ A).toLinearMap ∘ₗ
        matrixRepresentation ρ h =
      matrixRepresentation σ h ∘ₗ
        (compactHaarIntertwiningMap σ ρ hσ hρ A).toLinearMap :=
  (compactHaarIntertwiningMap σ ρ hσ hρ A).isIntertwining' h

include hσ hρ in
/-- Inequivalent irreducible representations force every averaged rectangular matrix to zero. -/
theorem exact_inequivalent_zero
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))] :
    compactHaarIntertwinerAverage σ ρ A = 0 :=
  compactHaarIntertwinerAverage_eq_zero_of_irreducible_inequivalent
    σ ρ hσ hρ A

include hσ hρ in
/-- Hostile probe: a claimed nonzero inequivalent irreducible average contradicts Schur. -/
theorem nonzero_inequivalent_average_blocked
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))]
    (claimedNonzero : compactHaarIntertwinerAverage σ ρ A ≠ 0) : False :=
  claimedNonzero
    (compactHaarIntertwinerAverage_eq_zero_of_irreducible_inequivalent
      σ ρ hσ hρ A)

end

end Probes
end CompactHaarSchurBridge
end Mathematics
end YangMills
