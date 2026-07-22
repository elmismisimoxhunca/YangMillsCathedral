/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientFamily

/-!
# Algebraic Plancherel for finite families of irreducible coefficient blocks

First, this file proves a useful finite-block analysis identity valid for an arbitrary continuous
function `f`:

`∫ conj(synthesisρ(A)) f dμ_H = ⟨A, f̂(ρ)ᵀ⟩ₕₛ`.

For a finite family of pairwise inequivalent positive-dimensional irreducible unitary
representations, this yields

`⟨f_A,f_B⟩ = ∑ᵢ dᵢ⁻¹ ⟨Aᵢ,Bᵢ⟩ₕₛ`

and the exact Fourier-side Plancherel formula

`⟨f_A,f_B⟩ = ∑ᵢ dᵢ ⟨f̂_A(ρᵢ),f̂_B(ρᵢ)⟩ₕₛ`.

The sums are over one explicitly supplied finite family. No all-irreducible enumeration, infinite
sum convergence, density, or `L²` completeness is asserted.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG uι

/-- Pairing a synthesized coefficient block against an arbitrary continuous function is the
Hilbert–Schmidt pairing with the transpose of that function's representation-valued Fourier
coefficient. -/
theorem coefficientSynthesis_pairing_fourier
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {n:ℕ} (ρ:G→*Matrix (Fin n) (Fin n) ℂ) (hρ:Continuous ρ)
 (hu:∀ g, star (ρ g)*ρ g=1) (A:Matrix (Fin n) (Fin n) ℂ)
 (f:G→ℂ) (hf:Continuous f) :
 (∫g,star (matrixCoefficientSynthesis ρ A g)*f g ∂normalizedCompactHaarMeasure G) =
 matrixHilbertSchmidtPairing A
  (normalizedCompactMatrixFourierCoefficient G ρ f).transpose := by
  classical
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have hInt (row col:Fin n) : Integrable (fun g =>
    star (A row col*ρ g row col)*f g) μ := by
    have hc : Continuous (fun g => star (A row col*ρ g row col)*f g) := by
      apply Continuous.mul
      · exact (Continuous.const_mul (hρ.matrix_elem row col) (A row col)).star
      · exact hf
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
  calc
   (∫g,star (matrixCoefficientSynthesis ρ A g)*f g ∂μ) =
    ∫g,∑row,∑col,star (A row col*ρ g row col)*f g ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [matrixCoefficientSynthesis_apply]
      change (starRingEnd ℂ) (∑row,∑col,A row col*ρ g row col)*_ = _
      rw [map_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      rw [map_sum,Finset.sum_mul]
      simp only [starRingEnd_apply]
   _ = ∑row,∑col,∫g,star (A row col*ρ g row col)*f g ∂μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro row _
        rw [integral_finsetSum Finset.univ]
        intro col _
        exact hInt row col
      · intro row _
        exact integrable_finsetSum _ fun col _ => hInt row col
   _ = ∑row,∑col,star (A row col)*
      normalizedCompactMatrixFourierCoefficient G ρ f col row := by
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro col _
      have hFourier : normalizedCompactMatrixFourierCoefficient G ρ f col row =
        ∫g,star (ρ g row col)*f g ∂μ := by
        rw [normalizedCompactMatrixFourierCoefficient_apply]
        apply integral_congr_ae
        filter_upwards [] with g
        rw [unitaryMatrixRepresentation_inv_apply ρ hu g col row]
        ring
      have hfactor : (fun g => star (A row col*ρ g row col)*f g) =
        fun g => star (A row col)*(star (ρ g row col)*f g) := by
        funext g
        change (starRingEnd ℂ) (A row col*ρ g row col)*f g =
          (starRingEnd ℂ) (A row col)*((starRingEnd ℂ) (ρ g row col)*f g)
        rw [map_mul]
        ring
      rw [hfactor,integral_const_mul,←hFourier]
   _ = matrixHilbertSchmidtPairing A
      (normalizedCompactMatrixFourierCoefficient G ρ f).transpose := by
      rfl

/-- Exact coefficient-side Plancherel pairing for a finite pairwise-inequivalent family. -/
theorem finiteCoefficientBlockSynthesis_pairing
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
 (A B:∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 (∫g,star (finiteCoefficientBlockSynthesis d ρ A g)*
   finiteCoefficientBlockSynthesis d ρ B g ∂normalizedCompactHaarMeasure G) =
 ∑i,(d i:ℂ)⁻¹*matrixHilbertSchmidtPairing (A i) (B i) := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have hInt (i:ι) : Integrable (fun g =>
    star (matrixCoefficientSynthesis (ρ i) (A i) g)*
      finiteCoefficientBlockSynthesis d ρ B g) μ := by
    have hc : Continuous (fun g =>
      star (matrixCoefficientSynthesis (ρ i) (A i) g)*
        finiteCoefficientBlockSynthesis d ρ B g) := by
      apply Continuous.mul
      · exact (continuous_matrixCoefficientSynthesis (ρ i) (hρ i) (A i)).star
      · exact continuous_finiteCoefficientBlockSynthesis d ρ hρ B
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
  calc
   (∫g,star (finiteCoefficientBlockSynthesis d ρ A g)*
      finiteCoefficientBlockSynthesis d ρ B g ∂μ) =
    ∫g,∑i,star (matrixCoefficientSynthesis (ρ i) (A i) g)*
      finiteCoefficientBlockSynthesis d ρ B g ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [finiteCoefficientBlockSynthesis_apply]
      change (starRingEnd ℂ) (∑i,matrixCoefficientSynthesis (ρ i) (A i) g)*_ = _
      rw [map_sum,Finset.sum_mul]
      simp only [starRingEnd_apply]
   _ = ∑i,∫g,star (matrixCoefficientSynthesis (ρ i) (A i) g)*
      finiteCoefficientBlockSynthesis d ρ B g ∂μ := by
      rw [integral_finsetSum Finset.univ]
      intro i _
      exact hInt i
   _ = ∑i,(d i:ℂ)⁻¹*matrixHilbertSchmidtPairing (A i) (B i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coefficientSynthesis_pairing_fourier (ρ i) (hρ i) (hu i)
        (A i) (finiteCoefficientBlockSynthesis d ρ B)
        (continuous_finiteCoefficientBlockSynthesis d ρ hρ B),
        finiteCoefficientBlockSynthesis_analysis d ρ hρ hu hd hineq B i]
      have htranspose :
          (((d i : ℂ)⁻¹ • (B i).transpose).transpose) =
            (d i : ℂ)⁻¹ • B i := by
        ext row col
        simp
      rw [htranspose]
      have hsmul := matrixHilbertSchmidtPairing_smul
        (1 : ℂ) ((d i : ℂ)⁻¹) (A i) (B i)
      simpa using hsmul

/-- Exact dimension-weighted Fourier-side Plancherel pairing for a finite
pairwise-inequivalent family. -/
theorem finiteCoefficientBlockSynthesis_fourier_plancherel
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 {ι:Type uι} [Fintype ι] [DecidableEq ι]
 (d:ι→ℕ) (ρ:∀i,G→*Matrix (Fin (d i)) (Fin (d i)) ℂ)
 (hρ:∀i,Continuous (ρ i)) (hu:∀i g,star (ρ i g)*ρ i g=1)
 [∀i,Representation.IsIrreducible (matrixRepresentation (ρ i))]
 (hd:∀i,0<d i)
 (hineq:∀ i j,i≠j→IsEmpty (Representation.Equiv
  (matrixRepresentation (ρ j)) (matrixRepresentation (ρ i))))
 (A B:∀i,Matrix (Fin (d i)) (Fin (d i)) ℂ) :
 (∫g,star (finiteCoefficientBlockSynthesis d ρ A g)*
   finiteCoefficientBlockSynthesis d ρ B g ∂normalizedCompactHaarMeasure G) =
 ∑i,(d i:ℂ)*matrixHilbertSchmidtPairing
   (normalizedCompactMatrixFourierCoefficient G (ρ i)
     (finiteCoefficientBlockSynthesis d ρ A))
   (normalizedCompactMatrixFourierCoefficient G (ρ i)
     (finiteCoefficientBlockSynthesis d ρ B)) := by
  rw [finiteCoefficientBlockSynthesis_pairing d ρ hρ hu hd hineq A B]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteCoefficientBlockSynthesis_analysis d ρ hρ hu hd hineq A i,
    finiteCoefficientBlockSynthesis_analysis d ρ hρ hu hd hineq B i,
    matrixHilbertSchmidtPairing_smul,
    matrixHilbertSchmidtPairing_transpose]
  have hd0 : (d i:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hd i))
  have hstar : star ((d i:ℂ)⁻¹) = (d i:ℂ)⁻¹ := by
    change (starRingEnd ℂ) ((d i:ℂ)⁻¹) = (d i:ℂ)⁻¹
    rw [map_inv₀]
    simp
  rw [hstar]
  field_simp

end

end Mathematics
end YangMills
