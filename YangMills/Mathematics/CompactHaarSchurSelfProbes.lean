/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactHaarSchurSelf

/-!
# Hostile probes for irreducible self Haar–Schur averaging
-/

namespace YangMills
namespace Mathematics
namespace CompactHaarSchurSelf
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]

/-- The named Schur scalar controls the exact same Haar average. -/
theorem exact_selected_scalar :
    compactHaarIntertwinerAverage ρ ρ A =
      compactHaarSchurScalar ρ hρ A •
        (1 : Matrix (Fin n) (Fin n) ℂ) :=
  compactHaarIntertwinerAverage_eq_schurScalar_smul_one ρ hρ A

include hρ in
/-- No irreducible self-average can avoid being every scalar multiple of identity. -/
theorem nonscalar_self_average_blocked
    (claimedNonscalar : ∀ scalar : ℂ,
      compactHaarIntertwinerAverage ρ ρ A ≠
        scalar • (1 : Matrix (Fin n) (Fin n) ℂ)) : False :=
  claimedNonscalar (compactHaarSchurScalar ρ hρ A)
    (compactHaarIntertwinerAverage_eq_schurScalar_smul_one ρ hρ A)

include hρ in
/-- The theorem supplies only a scalar identity form; no unproved trace/dimension value is inserted. -/
theorem exact_uncomputed_scalar_surface :
    ∃ scalar : ℂ,
      compactHaarIntertwinerAverage ρ ρ A =
        scalar • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  exists_compactHaarIntertwinerAverage_eq_smul_one ρ hρ A

end

end Probes
end CompactHaarSchurSelf
end Mathematics
end YangMills
