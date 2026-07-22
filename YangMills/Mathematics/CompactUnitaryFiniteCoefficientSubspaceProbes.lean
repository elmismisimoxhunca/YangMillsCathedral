/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientSubspace

/-!
# Hostile probes for finite compact matrix-coefficient subspaces
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryFiniteCoefficientSubspace
namespace Probes

noncomputable section

universe uG

/-- The finite-block transform retains the exact transpose and inverse-dimension normalization. -/
theorem exact_synthesis_transform
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    normalizedCompactMatrixFourierCoefficient G ρ
        (matrixCoefficientSynthesis ρ A) =
      (n : ℂ)⁻¹ • A.transpose :=
  normalizedCompactMatrixFourierCoefficient_synthesis
    ρ hρ unitaryρ dimension_pos A

/-- Hostile noncollapse probe: a synthesized coefficient combination is the zero function only when
its entire coefficient matrix is zero. -/
theorem zero_synthesis_forces_zero_matrix
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ)
    (collapsed : matrixCoefficientSynthesis ρ A = 0) : A = 0 := by
  apply matrixCoefficientSynthesis_injective
    ρ hρ unitaryρ dimension_pos
  simpa using collapsed

/-- The exact coefficient block has dimension `n²`, not merely some unspecified finite bound. -/
theorem exact_coefficient_subspace_finrank
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    Module.finrank ℂ (matrixCoefficientSubspace ρ) = n * n :=
  finrank_matrixCoefficientSubspace
    ρ hρ unitaryρ dimension_pos

/-- Hostile dimension probe: a claimed different coefficient-block dimension is impossible. -/
theorem wrong_coefficient_subspace_finrank_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n)
    (wrong : Module.finrank ℂ (matrixCoefficientSubspace ρ) ≠ n * n) : False :=
  wrong (finrank_matrixCoefficientSubspace
    ρ hρ unitaryρ dimension_pos)

end

end Probes
end CompactUnitaryFiniteCoefficientSubspace
end Mathematics
end YangMills
