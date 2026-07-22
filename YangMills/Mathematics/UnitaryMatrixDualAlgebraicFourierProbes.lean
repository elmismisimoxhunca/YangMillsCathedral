/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualAlgebraicFourier

/-!
# Hostile probes for algebraic Fourier synthesis over the unitary dual
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualAlgebraicFourier
namespace Probes

noncomputable section

universe uG

/-- A single direct-sum block synthesizes to exactly its own matrix-coefficient combination. -/
theorem exact_single_block_synthesis
    {G : Type uG} [Group G] [TopologicalSpace G]
    (q : UnitaryMatrixDual G)
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    unitaryMatrixDualCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle q A) =
      matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A :=
  unitaryMatrixDualCoefficientSynthesis_single q A

/-- Analysis over the all-class coordinate direct sum retains the exact inverse dimension and
transpose at every class. -/
theorem exact_all_class_analysis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCoefficientSpace G)
    (q : UnitaryMatrixDual G) :
    normalizedCompactMatrixFourierCoefficient G
        (unitaryMatrixDualRepresentation q)
        (unitaryMatrixDualCoefficientSynthesis G coefficients) =
      (unitaryMatrixDualDimension q : ℂ)⁻¹ •
        (unitaryMatrixDualCoefficientAt q coefficients).transpose :=
  unitaryMatrixDualCoefficientSynthesis_analysis coefficients q

/-- Exact finite-support inversion recovers every coefficient matrix. -/
theorem exact_algebraic_inversion
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCoefficientSpace G)
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCoefficientAt q coefficients =
      (unitaryMatrixDualDimension q : ℂ) •
        (normalizedCompactMatrixFourierCoefficient G
          (unitaryMatrixDualRepresentation q)
          (unitaryMatrixDualCoefficientSynthesis G coefficients)).transpose :=
  unitaryMatrixDualCoefficientSynthesis_inversion coefficients q

/-- Hostile noncollapse probe: no nonzero finitely supported coefficient family synthesizes to the
zero function. -/
theorem zero_synthesis_forces_zero_coefficients
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCoefficientSpace G)
    (collapsed : unitaryMatrixDualCoefficientSynthesis G coefficients = 0) :
    coefficients = 0 := by
  apply unitaryMatrixDualCoefficientSynthesis_injective
  simpa using collapsed

/-- Hostile inversion probe: claiming a recovered coefficient differs from the exact
Fourier-transpose formula is contradictory. -/
theorem changed_algebraic_inversion_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (coefficients : UnitaryMatrixDualCoefficientSpace G)
    (q : UnitaryMatrixDual G)
    (changed : unitaryMatrixDualCoefficientAt q coefficients ≠
      (unitaryMatrixDualDimension q : ℂ) •
        (normalizedCompactMatrixFourierCoefficient G
          (unitaryMatrixDualRepresentation q)
          (unitaryMatrixDualCoefficientSynthesis G coefficients)).transpose) : False :=
  changed (unitaryMatrixDualCoefficientSynthesis_inversion coefficients q)

/-- The range equivalence is only with the finite-support algebraic coefficient subspace, retaining
the boundary against unjustified inversion for arbitrary continuous or `L²` functions. -/
theorem exact_algebraic_range_equivalence
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Nonempty (UnitaryMatrixDualCoefficientSpace G ≃ₗ[ℂ]
      unitaryMatrixDualAlgebraicCoefficientSubspace G) :=
  ⟨unitaryMatrixDualCoefficientSynthesisEquiv⟩

end

end Probes
end UnitaryMatrixDualAlgebraicFourier
end Mathematics
end YangMills
