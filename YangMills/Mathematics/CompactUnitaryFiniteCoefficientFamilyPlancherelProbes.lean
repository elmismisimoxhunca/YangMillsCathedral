/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientFamilyPlancherel

/-!
# Hostile probes for finite-family coefficient Plancherel
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryFiniteCoefficientFamilyPlancherel
namespace Probes

open MeasureTheory

noncomputable section

universe uG uι

/-- The generic analysis identity retains the transpose of the representation-valued Fourier
coefficient. -/
theorem exact_generic_synthesis_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (f : G → ℂ) (hf : Continuous f) :
    (∫ g, star (matrixCoefficientSynthesis ρ A g) * f g
      ∂normalizedCompactHaarMeasure G) =
      matrixHilbertSchmidtPairing A
        (normalizedCompactMatrixFourierCoefficient G ρ f).transpose :=
  coefficientSynthesis_pairing_fourier ρ hρ unitaryρ A f hf

/-- The coefficient-side family pairing retains every inverse representation-dimension weight. -/
theorem exact_family_coefficient_pairing
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
    (A B : ∀ i, Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ) :
    (∫ g, star (finiteCoefficientBlockSynthesis dimension ρ A g) *
        finiteCoefficientBlockSynthesis dimension ρ B g
      ∂normalizedCompactHaarMeasure G) =
      ∑ i, (dimension i : ℂ)⁻¹ *
        matrixHilbertSchmidtPairing (A i) (B i) :=
  finiteCoefficientBlockSynthesis_pairing
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent A B

/-- The Fourier-side family formula retains each positive representation-dimension weight. -/
theorem exact_family_fourier_plancherel
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
    (A B : ∀ i, Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ) :
    (∫ g, star (finiteCoefficientBlockSynthesis dimension ρ A g) *
        finiteCoefficientBlockSynthesis dimension ρ B g
      ∂normalizedCompactHaarMeasure G) =
      ∑ i, (dimension i : ℂ) * matrixHilbertSchmidtPairing
        (normalizedCompactMatrixFourierCoefficient G (ρ i)
          (finiteCoefficientBlockSynthesis dimension ρ A))
        (normalizedCompactMatrixFourierCoefficient G (ρ i)
          (finiteCoefficientBlockSynthesis dimension ρ B)) :=
  finiteCoefficientBlockSynthesis_fourier_plancherel
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent A B

/-- Hostile exactness probe: a claim that the family pairing differs from the dimension-weighted
Fourier sum is contradictory. The imported single-block probe further shows that dropping the
weight forces that block's dimension to be one. -/
theorem changed_family_fourier_plancherel_blocked
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
    (A B : ∀ i, Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (changed :
      (∫ g, star (finiteCoefficientBlockSynthesis dimension ρ A g) *
          finiteCoefficientBlockSynthesis dimension ρ B g
        ∂normalizedCompactHaarMeasure G) ≠
        ∑ i, (dimension i : ℂ) * matrixHilbertSchmidtPairing
          (normalizedCompactMatrixFourierCoefficient G (ρ i)
            (finiteCoefficientBlockSynthesis dimension ρ A))
          (normalizedCompactMatrixFourierCoefficient G (ρ i)
            (finiteCoefficientBlockSynthesis dimension ρ B))) : False :=
  changed (finiteCoefficientBlockSynthesis_fourier_plancherel
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent A B)

end

end Probes
end CompactUnitaryFiniteCoefficientFamilyPlancherel
end Mathematics
end YangMills
