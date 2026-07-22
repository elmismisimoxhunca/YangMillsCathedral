/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCharacterSubspace

/-!
# Hostile probes for finite compact central-character subspaces
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryFiniteCharacterSubspace
namespace Probes

open MeasureTheory

noncomputable section

universe uG uι

/-- Synthesized character combinations retain exact conjugacy invariance. -/
theorem exact_centrality
    {G : Type uG} [Group G]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (dimension : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dimension i)) (Fin (dimension i)) ℂ)
    (coefficients : ι → ℂ) (g h : G) :
    finiteCharacterSynthesis dimension ρ coefficients (h * g * h⁻¹) =
      finiteCharacterSynthesis dimension ρ coefficients g :=
  finiteCharacterSynthesis_conj dimension ρ coefficients g h

/-- Analysis by one represented character recovers exactly its own coefficient. -/
theorem exact_character_analysis
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
    (coefficients : ι → ℂ) (index : ι) :
    (∫ g, star (Matrix.trace (ρ index g)) *
        finiteCharacterSynthesis dimension ρ coefficients g
      ∂normalizedCompactHaarMeasure G) = coefficients index :=
  normalizedCompactHaar_character_analysis_synthesis
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent
    coefficients index

/-- The finite central-character pairing is the exact coordinate pairing. -/
theorem exact_finite_character_pairing
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
    (first second : ι → ℂ) :
    (∫ g, star (finiteCharacterSynthesis dimension ρ first g) *
        finiteCharacterSynthesis dimension ρ second g
      ∂normalizedCompactHaarMeasure G) =
      ∑ i, star (first i) * second i :=
  normalizedCompactHaar_finiteCharacterSynthesis_pairing
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent
    first second

/-- Hostile noncollapse probe: a zero synthesized central function has every coefficient zero. -/
theorem zero_character_synthesis_forces_zero_coefficients
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
    (coefficients : ι → ℂ)
    (collapsed : finiteCharacterSynthesis dimension ρ coefficients = 0) :
    coefficients = 0 := by
  apply finiteCharacterSynthesis_injective
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent
  simpa using collapsed

/-- The exact central-character subspace dimension remembers every indexed inequivalent
character. -/
theorem exact_finite_character_subspace_finrank
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
    Module.finrank ℂ (finiteCharacterSubspace dimension ρ) =
      Fintype.card ι :=
  finrank_finiteCharacterSubspace
    dimension ρ hρ unitaryρ dimension_pos pairwiseInequivalent

/-- Hostile family probe: an explicit equivalence between two distinct indexed members contradicts
the pairwise-inequivalence certificate. -/
theorem equivalent_distinct_members_blocked
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
end CompactUnitaryFiniteCharacterSubspace
end Mathematics
end YangMills
