/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupConjugationCentralization
import YangMills.Mathematics.CompactHaarSchurTrace

/-!
# The conjugation-average Schur-to-character formula

This file completes Hall's centralization argument. For a continuous irreducible finite matrix
representation `ρ` and a coefficient matrix `A`, finite coordinate calculation identifies

`matrixCoefficientSynthesis ρ A g = tr(ρ(g) Aᵀ)`.

Conjugation averaging moves `ρ(x)` outside the average and leaves the existing Schur average
`∫ρ(h⁻¹)Aᵀρ(h)`. The normalized Schur trace theorem evaluates that matrix as
`dim(ρ)⁻¹ tr(A) I`, giving the exact finite character coefficient.

The formula is first proved for one selected unitary-dual block and then extended by direct-sum
induction to every finite-support coefficient synthesis. Consequently the actual Haar operator now
constructs `CompactGroupCharacterCentralizationData`. Under second countability:

* full continuous Peter–Weyl density implies uniform central character density;
* faithful finite matrix coordinates imply both central uniform and central `L²` completeness.

The theorem remains conditional on full density (or a faithful finite matrix representation). It
does not prove the general compact-group Peter–Weyl theorem, dual countability, or an infinite
character expansion.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Finite matrix-coefficient synthesis is exactly a trace against the transposed coefficient
matrix. -/
theorem matrixCoefficientSynthesis_eq_trace_mul_transpose
    {G : Type uG} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    matrixCoefficientSynthesis ρ A g = Matrix.trace (ρ g * A.transpose) := by
  simp [matrixCoefficientSynthesis_apply, Matrix.trace, Matrix.mul_apply]
  simp_rw [mul_comm]

/-- The conjugation average of a coefficient synthesis is the trace of `ρ(x)` against the existing
normalized-Haar Schur average of `Aᵀ`. -/
theorem compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_trace_average
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (A : Matrix (Fin n) (Fin n) ℂ) (x : G) :
    compactGroupConjugationAverage (continuousMatrixCoefficientSynthesis ρ hρ A) x =
      Matrix.trace (ρ x * compactHaarIntertwinerAverage ρ ρ A.transpose) := by
  let μ := normalizedCompactHaarMeasure G
  let B := fun h => ρ (h⁻¹) * A.transpose * ρ h
  change (∫ h, matrixCoefficientSynthesis ρ A (h * x * h⁻¹) ∂μ) = _
  simp_rw [matrixCoefficientSynthesis_eq_trace_mul_transpose]
  have pointwise : ∀ h : G,
      Matrix.trace (ρ (h * x * h⁻¹) * A.transpose) =
        Matrix.trace (ρ x * B h) := by
    intro h
    simp only [map_mul, B]
    rw [show Matrix.trace ((ρ h * ρ x * ρ (h⁻¹)) * A.transpose) =
        Matrix.trace (ρ h * (ρ x * ρ (h⁻¹) * A.transpose)) by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp_rw [pointwise]
  change (∫ h, ∑ i, ∑ j, ρ x i j * B h j i ∂μ) =
    ∑ i, ∑ j, ρ x i j * compactHaarIntertwinerAverage ρ ρ A.transpose j i
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      rfl
    · intro j _
      exact (integrable_compactHaarIntertwinerAverage_integrand
        ρ ρ hρ hρ A.transpose j i).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ =>
      (integrable_compactHaarIntertwinerAverage_integrand
        ρ ρ hρ hρ A.transpose j i).const_mul _

/-- For a positive-dimensional irreducible representation, conjugation averaging a coefficient
synthesis gives the exact inverse-dimension trace weight times the irreducible character. -/
theorem compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_character
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) (x : G) :
    compactGroupConjugationAverage (continuousMatrixCoefficientSynthesis ρ hρ A) x =
      ((n : ℂ)⁻¹ * Matrix.trace A) * Matrix.trace (ρ x) := by
  rw [compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_trace_average ρ hρ A x]
  rw [compactHaarIntertwinerAverage_eq_schurScalar_smul_one ρ hρ A.transpose]
  rw [compactHaarSchurScalar_eq_inv_natCast_mul_trace
    ρ hρ A.transpose dimension_pos]
  simp only [Matrix.trace_transpose]
  rw [Matrix.mul_smul, Matrix.mul_one]
  change (∑ i, ((n : ℂ)⁻¹ * ∑ j, A j j) * ρ x i i) =
    ((n : ℂ)⁻¹ * ∑ j, A j j) * ∑ i, ρ x i i
  simpa using (Finset.mul_sum Finset.univ (fun i => ρ x i i)
    ((n : ℂ)⁻¹ * ∑ j, A j j)).symm

/-- Exact selected-block Schur-to-character formula for the actual conjugation centralization
operator. -/
theorem compactGroupConjugationCentralization_coefficientSingle
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (q : UnitaryMatrixDual G)
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    compactGroupConjugationCentralization
      (unitaryMatrixDualContinuousCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle q A)) =
    unitaryMatrixDualCentralCharacterSynthesis G
      (Finsupp.single q
        ((unitaryMatrixDualDimension q : ℂ)⁻¹ * Matrix.trace A)) := by
  apply Subtype.ext
  ext x
  change compactGroupConjugationAverage
    (unitaryMatrixDualContinuousCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle q A)) x = _
  have coefficient_eq : unitaryMatrixDualContinuousCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle q A) =
      continuousMatrixCoefficientSynthesis (unitaryMatrixDualRepresentation q)
        (continuous_unitaryMatrixDualRepresentation q) A := by
    ext g
    exact congrFun (unitaryMatrixDualCoefficientSynthesis_single q A) g
  rw [coefficient_eq]
  rw [compactGroupConjugationAverage_matrixCoefficientSynthesis_eq_character
    (unitaryMatrixDualRepresentation q)
    (continuous_unitaryMatrixDualRepresentation q)
    (unitaryMatrixDualDimension_pos q) A x]
  rw [unitaryMatrixDualCentralCharacterSynthesis_apply,
    unitaryMatrixDualCharacterSynthesis_single]
  rfl

/-- Every finite-support selected-dual coefficient synthesis centralizes to an exact finite-support
selected-character synthesis. -/
theorem compactGroupConjugationCentralization_maps_coefficientSynthesis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      compactGroupConjugationCentralization
        (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
      unitaryMatrixDualCentralCharacterSynthesis G c := by
  classical
  induction A using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of q A =>
      exact ⟨Finsupp.single q
        ((unitaryMatrixDualDimension q : ℂ)⁻¹ * Matrix.trace A),
        compactGroupConjugationCentralization_coefficientSingle q A⟩
  | add A B hA hB =>
      rcases hA with ⟨c, hc⟩
      rcases hB with ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      rw [map_add (unitaryMatrixDualContinuousCoefficientSynthesis G) A B]
      rw [map_add (compactGroupConjugationCentralization (G := G))]
      rw [hc, hd, map_add (unitaryMatrixDualCentralCharacterSynthesis G)]

/-- The actual conjugation-Haar operator now supplies the full character-centralization bridge
data. -/
noncomputable def compactGroupCharacterCentralizationData
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] :
    CompactGroupCharacterCentralizationData G :=
  compactGroupCharacterCentralizationDataOfMapsCoefficientSynthesis
    compactGroupConjugationCentralization_maps_coefficientSynthesis

/-- Under second countability, full selected-dual continuous density implies uniform central
character density with no additional centralization hypothesis. -/
theorem UnitaryMatrixDual.HasContinuousPeterWeylDensity.hasCentralContinuousPeterWeylDensity_of_secondCountable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  density.hasCentralContinuousPeterWeylDensity (compactGroupCharacterCentralizationData G)

/-- Under second countability, full selected-dual continuous density implies the exact central
normalized-Haar `L²` closed-span target. -/
theorem UnitaryMatrixDual.HasContinuousPeterWeylDensity.hasCentralL2PeterWeylCompleteness_of_secondCountable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  density.hasCentralContinuousPeterWeylDensity_of_secondCountable
    |>.hasCentralL2PeterWeylCompleteness

/-- Faithful finite matrix coordinates and second countability imply uniform central character
density. -/
theorem unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  (unitaryMatrixDual_hasContinuousPeterWeylDensity_of_faithful faithful)
    |>.hasCentralContinuousPeterWeylDensity_of_secondCountable

/-- Faithful finite matrix coordinates and second countability imply the exact central normalized-
Haar `L²` closed-span target. -/
theorem unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  (unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful faithful)
    |>.hasCentralL2PeterWeylCompleteness

end

end Mathematics
end YangMills
