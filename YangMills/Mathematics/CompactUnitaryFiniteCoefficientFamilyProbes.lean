/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientFamily

/-!
# Hostile probes for finite compact coefficient-block families
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryFiniteCoefficientFamily
namespace Probes

noncomputable section

universe uG uι

/-- An entire synthesized block, not merely one coefficient, vanishes under Fourier analysis at an
explicitly inequivalent irreducible representation. -/
theorem exact_inequivalent_block_zero
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation σ) (matrixRepresentation ρ))]
    (A : Matrix (Fin m) (Fin m) ℂ) :
    normalizedCompactMatrixFourierCoefficient G ρ
      (matrixCoefficientSynthesis σ A) = 0 :=
  normalizedCompactMatrixFourierCoefficient_synthesis_inequivalent
    σ ρ hσ hρ unitaryρ A

/-- Fourier analysis of a finite pairwise-inequivalent family recovers exactly one transposed,
inverse-dimension-scaled coefficient block. -/
theorem exact_family_block_analysis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (hρ : ∀ i, Continuous (ρ i))
    (unitaryρ : ∀ i g, star (ρ i g) * ρ i g = 1)
    [∀ i, Representation.IsIrreducible (matrixRepresentation (ρ i))]
    (dimension_pos : ∀ i, 0 < dimension i)
    (pairwiseInequivalent : ∀ i j, i ≠ j →
      IsEmpty (Representation.Equiv
        (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
    (coefficients : ∀ i,
      Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (index : ι) :
    normalizedCompactMatrixFourierCoefficient G (ρ index)
      (finiteCoefficientBlockSynthesis dimension ρ coefficients) =
        (dimension index : ℂ)⁻¹ • (coefficients index).transpose :=
  finiteCoefficientBlockSynthesis_analysis
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent
    coefficients index

/-- Hostile noncollapse probe: a zero finite coefficient-family synthesis forces every dependent
coefficient matrix to vanish. -/
theorem zero_family_synthesis_forces_zero_coefficients
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (hρ : ∀ i, Continuous (ρ i))
    (unitaryρ : ∀ i g, star (ρ i g) * ρ i g = 1)
    [∀ i, Representation.IsIrreducible (matrixRepresentation (ρ i))]
    (dimension_pos : ∀ i, 0 < dimension i)
    (pairwiseInequivalent : ∀ i j, i ≠ j →
      IsEmpty (Representation.Equiv
        (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
    (coefficients : ∀ i,
      Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (collapsed :
      finiteCoefficientBlockSynthesis dimension ρ coefficients = 0) :
    coefficients = 0 := by
  apply finiteCoefficientBlockSynthesis_injective
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent
  simpa using collapsed

/-- The full finite coefficient-family range remembers the sum of all squared representation
dimensions. -/
theorem exact_family_coefficient_subspace_finrank
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (hρ : ∀ i, Continuous (ρ i))
    (unitaryρ : ∀ i g, star (ρ i g) * ρ i g = 1)
    [∀ i, Representation.IsIrreducible (matrixRepresentation (ρ i))]
    (dimension_pos : ∀ i, 0 < dimension i)
    (pairwiseInequivalent : ∀ i j, i ≠ j →
      IsEmpty (Representation.Equiv
        (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i)))) :
    Module.finrank ℂ (finiteCoefficientBlockSubspace dimension ρ) =
      ∑ i, dimension i * dimension i :=
  finrank_finiteCoefficientBlockSubspace
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent

/-- Hostile dimension probe: replacing the sum of squared dimensions by any different value is
impossible. -/
theorem wrong_family_coefficient_subspace_finrank_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (hρ : ∀ i, Continuous (ρ i))
    (unitaryρ : ∀ i g, star (ρ i g) * ρ i g = 1)
    [∀ i, Representation.IsIrreducible (matrixRepresentation (ρ i))]
    (dimension_pos : ∀ i, 0 < dimension i)
    (pairwiseInequivalent : ∀ i j, i ≠ j →
      IsEmpty (Representation.Equiv
        (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
    (wrong : Module.finrank ℂ
      (finiteCoefficientBlockSubspace dimension ρ) ≠
        ∑ i, dimension i * dimension i) : False :=
  wrong (finrank_finiteCoefficientBlockSubspace
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent)

/-- Hostile family probe: two distinct family members cannot simultaneously carry an explicit
representation equivalence and the pairwise-inequivalence certificate. -/
theorem equivalent_distinct_blocks_blocked
    {G : Type uG} [Group G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (pairwiseInequivalent : ∀ i j, i ≠ j →
      IsEmpty (Representation.Equiv
        (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
    (i j : ι) (distinct : i ≠ j)
    (equivalence : Representation.Equiv
      (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))) : False :=
  (pairwiseInequivalent i j distinct).false equivalence

end

end Probes
end CompactUnitaryFiniteCoefficientFamily
end Mathematics
end YangMills
