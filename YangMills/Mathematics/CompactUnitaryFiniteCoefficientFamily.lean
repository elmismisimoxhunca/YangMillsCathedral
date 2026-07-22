/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteBlockPlancherel

/-!
# Finite families of inequivalent irreducible coefficient blocks

This file packages a finite dependently typed family of full matrix-coefficient blocks, allowing the
representation dimension to vary with the family index. It first extends Fourier extraction from one
coefficient to an arbitrary synthesized block at an inequivalent representation. It then constructs
finite block synthesis

`A ↦ (g ↦ ∑ᵢ ∑ₐᵦ Aᵢₐᵦ ρᵢ(g)ₐᵦ)`.

For pairwise inequivalent positive-dimensional irreducible unitary representations, Fourier analysis
at `ρᵢ` recovers exactly `(dim ρᵢ)⁻¹ Aᵢᵀ`. Hence synthesis is injective, its range is linearly
equivalent to the dependent product of matrix spaces, and its exact dimension is
`∑ᵢ (dim ρᵢ)²`.

This remains a selected finite family. It does not enumerate all irreducibles or assert density,
Fourier inversion, or `L²` completeness.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG uι

/-- A synthesized coefficient block has zero Fourier transform at an explicitly inequivalent
irreducible unitary representation. -/
theorem normalizedCompactMatrixFourierCoefficient_synthesis_inequivalent
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
      (matrixCoefficientSynthesis σ A) = 0 := by
  classical
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  ext outputRow outputColumn
  rw [normalizedCompactMatrixFourierCoefficient_apply, Matrix.zero_apply]
  have hInt (row column : Fin m) : Integrable (fun g =>
      A row column * (σ g row column * ρ (g⁻¹) outputRow outputColumn)) μ := by
    have hc : Continuous (fun g =>
      A row column * (σ g row column * ρ (g⁻¹) outputRow outputColumn)) := by fun_prop
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
  calc
   (∫g, matrixCoefficientSynthesis σ A g * ρ (g⁻¹) outputRow outputColumn ∂μ) =
    ∫g, ∑row, ∑column, A row column *
      (σ g row column * ρ (g⁻¹) outputRow outputColumn) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [matrixCoefficientSynthesis_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro col _
      ring
   _ = ∑row, ∑column, ∫g, A row column *
      (σ g row column * ρ (g⁻¹) outputRow outputColumn) ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro row _
        rw [integral_finsetSum Finset.univ]
        intro col _
        exact hInt row col
      · intro row _
        exact integrable_finsetSum _ fun col _ => hInt row col
   _ = 0 := by
      apply Finset.sum_eq_zero
      intro row _
      apply Finset.sum_eq_zero
      intro col _
      rw [integral_const_mul]
      have hzero := congrFun (congrFun
        (normalizedCompactMatrixFourierCoefficient_matrixCoefficient_inequivalent
          σ ρ hσ hρ unitaryρ row col) outputRow) outputColumn
      change (∫g, σ g row col * ρ (g⁻¹) outputRow outputColumn ∂μ) = 0 at hzero
      rw [hzero, mul_zero]

/-- Linear synthesis of a finite dependent family of full matrix-coefficient blocks. -/
def finiteCoefficientBlockSynthesis
 {G:Type uG} [Group G] {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 (∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] (G→ℂ) where
 toFun A g := ∑i,matrixCoefficientSynthesis (ρ i) (A i) g
 map_add' A B := by
  funext g
  change (∑i,matrixCoefficientSynthesis (ρ i) (A i+B i) g) =
    (∑i,matrixCoefficientSynthesis (ρ i) (A i) g)+
      ∑i,matrixCoefficientSynthesis (ρ i) (B i) g
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (map_add (matrixCoefficientSynthesis (ρ i)) (A i) (B i)) g
 map_smul' c A := by
  funext g
  change (∑i,matrixCoefficientSynthesis (ρ i) (c • A i) g) =
    c * ∑i,matrixCoefficientSynthesis (ρ i) (A i) g
  simp_rw [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

@[simp] theorem finiteCoefficientBlockSynthesis_apply
 {G:Type uG} [Group G] {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (A:∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) (g:G) :
 finiteCoefficientBlockSynthesis d ρ A g =
   ∑i,matrixCoefficientSynthesis (ρ i) (A i) g := rfl

/-- Finite block synthesis is continuous when every represented matrix family is continuous. -/
theorem continuous_finiteCoefficientBlockSynthesis
 {G:Type uG} [Group G] [TopologicalSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i))
 (A:∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 Continuous (finiteCoefficientBlockSynthesis d ρ A) := by
 change Continuous (fun g => ∑i,matrixCoefficientSynthesis (ρ i) (A i) g)
 exact continuous_finsetSum _ fun i _ =>
  continuous_matrixCoefficientSynthesis (ρ i) (hρ i) (A i)

/-- Fourier analysis at one family member recovers exactly its own inverse-dimension-scaled
transposed coefficient matrix; every inequivalent block contributes zero. -/
theorem finiteCoefficientBlockSynthesis_analysis
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
 (A:∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) (i:ι) :
 normalizedCompactMatrixFourierCoefficient G (ρ i)
   (finiteCoefficientBlockSynthesis d ρ A) =
 (d i:ℂ)⁻¹ • (A i).transpose := by
  classical
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  ext outputRow outputCol
  rw [normalizedCompactMatrixFourierCoefficient_apply]
  have hInt (j:ι) : Integrable (fun g =>
    matrixCoefficientSynthesis (ρ j) (A j) g * ρ i (g⁻¹) outputRow outputCol) μ := by
    have hc : Continuous (fun g =>
      matrixCoefficientSynthesis (ρ j) (A j) g * ρ i (g⁻¹) outputRow outputCol) := by
      apply Continuous.mul
      · exact continuous_matrixCoefficientSynthesis (ρ j) (hρ j) (A j)
      · fun_prop
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
  calc
   (∫g, finiteCoefficientBlockSynthesis d ρ A g * ρ i (g⁻¹) outputRow outputCol ∂μ) =
    ∫g, ∑j,matrixCoefficientSynthesis (ρ j) (A j) g *
      ρ i (g⁻¹) outputRow outputCol ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [finiteCoefficientBlockSynthesis_apply, Finset.sum_mul]
   _ = ∑j,∫g,matrixCoefficientSynthesis (ρ j) (A j) g *
      ρ i (g⁻¹) outputRow outputCol ∂μ := by
      rw [integral_finsetSum Finset.univ]
      intro j _
      exact hInt j
   _ = ((d i:ℂ)⁻¹ • (A i).transpose) outputRow outputCol := by
      rw [Finset.sum_eq_single i]
      · have hself := congrFun (congrFun
          (normalizedCompactMatrixFourierCoefficient_synthesis
            (ρ i) (hρ i) (hu i) (hd i) (A i)) outputRow) outputCol
        exact hself
      · intro j _ hji
        letI := hineq i j (Ne.symm hji)
        have hzero := congrFun (congrFun
          (normalizedCompactMatrixFourierCoefficient_synthesis_inequivalent
            (ρ j) (ρ i) (hρ j) (hρ i) (hu i) (A j)) outputRow) outputCol
        simpa using hzero
      · simp

/-- Pairwise-inequivalent finite block synthesis is injective. -/
theorem finiteCoefficientBlockSynthesis_injective
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i)))) :
 Function.Injective (finiteCoefficientBlockSynthesis d ρ) := by
  intro A B hAB
  funext i
  have hFourier := congrArg
    (normalizedCompactMatrixFourierCoefficient G (ρ i)) hAB
  rw [finiteCoefficientBlockSynthesis_analysis d ρ hρ hu hd hineq A i,
    finiteCoefficientBlockSynthesis_analysis d ρ hρ hu hd hineq B i] at hFourier
  ext row col
  have hentry := congrFun (congrFun hFourier col) row
  change (d i:ℂ)⁻¹ * A i row col = (d i:ℂ)⁻¹ * B i row col at hentry
  have hd0 : (d i:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd i))
  exact mul_left_cancel₀ (inv_ne_zero hd0) hentry

/-- The finite full-coefficient-family subspace is the exact range of block synthesis. -/
def finiteCoefficientBlockSubspace
 {G:Type uG} [Group G] {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 Submodule ℂ (G→ℂ) := LinearMap.range (finiteCoefficientBlockSynthesis d ρ)

/-- Fourier analysis identifies the dependent coefficient matrices with their synthesized range. -/
noncomputable def finiteCoefficientBlockSynthesisEquiv
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i)))) :
 (∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
   finiteCoefficientBlockSubspace d ρ :=
 LinearEquiv.ofInjective (finiteCoefficientBlockSynthesis d ρ)
  (finiteCoefficientBlockSynthesis_injective d ρ hρ hu hd hineq)

/-- Every finite synthesized block family has finite-dimensional range. -/
noncomputable instance finiteCoefficientBlockSubspace_finiteDimensional
 {G:Type uG} [Group G] {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 FiniteDimensional ℂ (finiteCoefficientBlockSubspace d ρ) :=
 Module.Finite.range (finiteCoefficientBlockSynthesis d ρ)

/-- The exact dimension of a pairwise-inequivalent finite coefficient family is the sum of the
squared representation dimensions. -/
theorem finrank_finiteCoefficientBlockSubspace
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i)))) :
 Module.finrank ℂ (finiteCoefficientBlockSubspace d ρ) =
   ∑i,d i*d i := by
 rw [← (finiteCoefficientBlockSynthesisEquiv d ρ hρ hu hd hineq).finrank_eq]
 rw [Module.finrank_pi_fintype]
 apply Finset.sum_congr rfl
 intro i _
 simp [Module.finrank_matrix]

end

end Mathematics
end YangMills
