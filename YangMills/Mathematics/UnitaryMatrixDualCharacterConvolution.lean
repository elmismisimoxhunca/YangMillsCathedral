/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierConvolution
import YangMills.Mathematics.UnitaryMatrixDualCharacters

/-!
# Convolution of selected irreducible characters

For the project's normalized-Haar convolution

`(f ⋆ g)(z) = ∫ f(x) g(x⁻¹z) dμ_H(x)`,

this file proves the exact selected-character law

`χ_q ⋆ χ_r = if q = r then dim(q)⁻¹ χ_q else 0`.

The proof expands both traces into matrix coordinates, uses the unitary inverse/conjugate-transpose
formula, exchanges only finite sums with the normalized-Haar integral, and applies the already proved
self and inequivalent matrix-coefficient orthogonality formulas. The inverse dimension and
convolution order are therefore kernel-checked rather than postulated.

No Peter–Weyl completeness, infinite character series, or heat-kernel semigroup is used.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Self-convolution of one selected irreducible character is exactly inverse-dimension times that
character. -/
theorem normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_self (q:UnitaryMatrixDual G) (z:G) :
 normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
  (unitaryMatrixDualCharacter q) z =
 (unitaryMatrixDualDimension q:ℂ)⁻¹*unitaryMatrixDualCharacter q z := by
 let ρ:=unitaryMatrixDualRepresentation q
 let n:=unitaryMatrixDualDimension q
 rw [normalizedCompactHaarComplexConvolution_apply]
 change (∫x, Matrix.trace (ρ x)*Matrix.trace (ρ (x⁻¹*z))
  ∂normalizedCompactHaarMeasure G)=_
 simp_rw [map_mul]
 simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
 simp_rw [unitaryMatrixRepresentation_inv_eq_conjTranspose ρ
  (unitaryMatrixDualRepresentative q).unitary_representation]
 simp only [Matrix.conjTranspose_apply]
 simp_rw [Finset.sum_mul,Finset.mul_sum]
 let μ:=normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
 have hρc:Continuous ρ:=continuous_unitaryMatrixDualRepresentation q
 have hint (k i j:Fin (unitaryMatrixDualDimension q)) : Integrable
  (fun x:G=>ρ x k k*(star (ρ x j i)*ρ z j i)) μ := by
  have hc:Continuous (fun x:G=>ρ x k k*(star (ρ x j i)*ρ z j i)) := by
   fun_prop
  simpa only [integrableOn_univ] using
   hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
 calc
  (∫x,∑k,∑i,∑j,ρ x k k*(star (ρ x j i)*ρ z j i) ∂μ) =
   ∑k,∑i,∑j,∫x,ρ x k k*(star (ρ x j i)*ρ z j i) ∂μ := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hint k i j
      · intro j hj
        exact MeasureTheory.integrable_finsetSum _ (fun i hi=>hint k j i)
    · intro i hi
      exact MeasureTheory.integrable_finsetSum _ (fun j hj=>
       MeasureTheory.integrable_finsetSum _ (fun k hk=>hint i j k))
  _ = ∑k,∑i,∑j, ρ z j i * ((unitaryMatrixDualDimension q:ℂ)⁻¹ *
          (if j=k then 1 else 0)*(if i=k then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
     (∫x,ρ x k k*(star (ρ x j i)*ρ z j i) ∂μ) =
      ρ z j i * (∫x,star (ρ x j i)*ρ x k k ∂μ) := by
       rw [←integral_const_mul]
       apply integral_congr_ae
       filter_upwards [] with x
       ring
     _ = _ := by
       rw [normalizedCompactHaar_matrixCoefficient_orthogonality_self ρ
        (continuous_unitaryMatrixDualRepresentation q)
        (unitaryMatrixDualRepresentative q).unitary_representation
        (unitaryMatrixDualRepresentative q).dimension_pos]
  _ = _ := by
   dsimp only [ρ]
   unfold unitaryMatrixDualCharacter Matrix.trace
   simp [Matrix.diag_apply, mul_comm]
   rw [Finset.mul_sum]

/-- Convolution of characters from distinct selected irreducible classes vanishes exactly. -/
theorem normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne {q r:UnitaryMatrixDual G} (hqr:q≠r) (z:G) :
 normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
  (unitaryMatrixDualCharacter r) z = 0 := by
 let ρ:=unitaryMatrixDualRepresentation q
 let σ:=unitaryMatrixDualRepresentation r
 letI := unitaryMatrixDual_representative_inequivalent (q:=r) (r:=q) (Ne.symm hqr)
 rw [normalizedCompactHaarComplexConvolution_apply]
 change (∫x, Matrix.trace (ρ x)*Matrix.trace (σ (x⁻¹*z))
  ∂normalizedCompactHaarMeasure G)=0
 simp_rw [map_mul]
 simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
 simp_rw [unitaryMatrixRepresentation_inv_eq_conjTranspose σ
  (unitaryMatrixDualRepresentative r).unitary_representation]
 simp only [Matrix.conjTranspose_apply]
 simp_rw [Finset.sum_mul,Finset.mul_sum]
 let μ:=normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
 have hρc:Continuous ρ:=continuous_unitaryMatrixDualRepresentation q
 have hσc:Continuous σ:=continuous_unitaryMatrixDualRepresentation r
 have hint (k:Fin (unitaryMatrixDualDimension q))
  (i j:Fin (unitaryMatrixDualDimension r)) : Integrable
  (fun x:G=>ρ x k k*(star (σ x j i)*σ z j i)) μ := by
  have hc:Continuous (fun x:G=>ρ x k k*(star (σ x j i)*σ z j i)) := by
   fun_prop
  simpa only [integrableOn_univ] using
   hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
 calc
  (∫x,∑k,∑i,∑j,ρ x k k*(star (σ x j i)*σ z j i) ∂μ) =
   ∑k,∑i,∑j,∫x,ρ x k k*(star (σ x j i)*σ z j i) ∂μ := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hint k i j
      · intro j hj
        exact MeasureTheory.integrable_finsetSum _ (fun i hi=>hint k j i)
    · intro i hi
      exact MeasureTheory.integrable_finsetSum _ (fun j hj=>
       MeasureTheory.integrable_finsetSum _ (fun k hk=>hint i j k))
  _ = 0 := by
   apply Finset.sum_eq_zero
   intro k hk
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   calc
    (∫x,ρ x k k*(star (σ x j i)*σ z j i) ∂μ) =
     σ z j i * (∫x,star (σ x j i)*ρ x k k ∂μ) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = 0 := by
      rw [normalizedCompactHaar_matrixCoefficient_orthogonality_inequivalent
       σ ρ (continuous_unitaryMatrixDualRepresentation r)
       (continuous_unitaryMatrixDualRepresentation q)
       (unitaryMatrixDualRepresentative r).unitary_representation]
      simp

/-- Unified selected-character convolution law with exact Kronecker branching. -/
theorem normalizedCompactHaar_unitaryMatrixDualCharacter_convolution
    (q r : UnitaryMatrixDual G) (z : G) :
    normalizedCompactHaarComplexConvolution G (unitaryMatrixDualCharacter q)
      (unitaryMatrixDualCharacter r) z =
      if q = r then
        (unitaryMatrixDualDimension q : ℂ)⁻¹ * unitaryMatrixDualCharacter q z
      else 0 := by
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl]
    exact normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_self q z
  · rw [if_neg hqr]
    exact normalizedCompactHaar_unitaryMatrixDualCharacter_convolution_ne hqr z

end

end Mathematics
end YangMills
