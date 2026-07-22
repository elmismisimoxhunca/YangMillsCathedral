/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Algebra.DirectSum.Module
import YangMills.Mathematics.UnitaryMatrixDual

/-!
# Algebraic Fourier synthesis over the coordinate unitary dual

This file forms the dependent algebraic direct sum of coefficient matrices over every class in the
coordinate `UnitaryMatrixDual G`. Elements therefore have finite support by construction. The
associated linear synthesis map adds the corresponding finite collection of matrix-coefficient
functions.

For each dual class `q`, Fourier analysis recovers

`f̂_A(q) = (dim q)⁻¹ A(q)ᵀ`.

Consequently algebraic synthesis is injective and has the exact finite-support inversion formula

`A(q) = (dim q) f̂_A(q)ᵀ`.

This is algebraic Fourier inversion on the finite-support coefficient span. It is not inversion for
arbitrary continuous or `L²` functions and uses no Peter–Weyl density or completeness theorem.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Classical decidable equality for the quotient index, used only to realize dependent finite
support. -/
noncomputable instance unitaryMatrixDualDecidableEq
 (G:Type uG) [Group G] [TopologicalSpace G] :
 DecidableEq (UnitaryMatrixDual G) := Classical.decEq _

/-- The algebraic dependent direct sum of one full coefficient matrix for each coordinate dual
class. -/
abbrev UnitaryMatrixDualCoefficientSpace
 (G:Type uG) [Group G] [TopologicalSpace G] :=
 DirectSum (UnitaryMatrixDual G) (fun q =>
  Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ)

/-- Finite-support synthesis of coefficient matrices over the entire coordinate unitary dual. -/
noncomputable def unitaryMatrixDualCoefficientSynthesis
 (G:Type uG) [Group G] [TopologicalSpace G] :
 UnitaryMatrixDualCoefficientSpace G →ₗ[ℂ] (G→ℂ) := by
 letI := Classical.decEq (UnitaryMatrixDual G)
 exact DirectSum.toModule ℂ (UnitaryMatrixDual G) (G→ℂ)
  (fun q => matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q))

/-- Inclusion of one coefficient matrix into its single dual block. -/
noncomputable def unitaryMatrixDualCoefficientSingle
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ →ₗ[ℂ]
   UnitaryMatrixDualCoefficientSpace G := by
 letI := Classical.decEq (UnitaryMatrixDual G)
 exact DirectSum.lof ℂ (UnitaryMatrixDual G) (fun r =>
  Matrix (Fin (unitaryMatrixDualDimension r))
   (Fin (unitaryMatrixDualDimension r)) ℂ) q

/-- Linear extraction of one dual-class coefficient matrix. -/
noncomputable def unitaryMatrixDualCoefficientAt
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 UnitaryMatrixDualCoefficientSpace G →ₗ[ℂ]
 Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ := by
 letI := Classical.decEq (UnitaryMatrixDual G)
 exact DFinsupp.lapply q

@[simp] theorem unitaryMatrixDualCoefficientAt_single_self
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G)
 (A:Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ) :
 unitaryMatrixDualCoefficientAt q
   (unitaryMatrixDualCoefficientSingle q A) = A := by
 classical
 change (DFinsupp.single
  (β := fun r : UnitaryMatrixDual G =>
    Matrix (Fin (unitaryMatrixDualDimension r))
      (Fin (unitaryMatrixDualDimension r)) ℂ) q A) q = A
 simp

@[simp] theorem unitaryMatrixDualCoefficientAt_single_of_ne
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q r:UnitaryMatrixDual G) (hrq:r≠q)
 (A:Matrix (Fin (unitaryMatrixDualDimension r))
   (Fin (unitaryMatrixDualDimension r)) ℂ) :
 unitaryMatrixDualCoefficientAt q
   (unitaryMatrixDualCoefficientSingle r A) = 0 := by
 classical
 change (DFinsupp.single
  (β := fun s : UnitaryMatrixDual G =>
    Matrix (Fin (unitaryMatrixDualDimension s))
      (Fin (unitaryMatrixDualDimension s)) ℂ) r A) q = 0
 simp [hrq]

@[simp] theorem unitaryMatrixDualCoefficientSynthesis_single
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G)
 (A:Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ) :
 unitaryMatrixDualCoefficientSynthesis G
   (unitaryMatrixDualCoefficientSingle q A) =
 matrixCoefficientSynthesis (unitaryMatrixDualRepresentation q) A := by
 classical
 simp [unitaryMatrixDualCoefficientSynthesis,
   unitaryMatrixDualCoefficientSingle]

/-- Every algebraically synthesized finite-support coefficient function is continuous. -/
theorem continuous_unitaryMatrixDualCoefficientSynthesis
 {G:Type uG} [Group G] [TopologicalSpace G]
 (A:UnitaryMatrixDualCoefficientSpace G) :
 Continuous (unitaryMatrixDualCoefficientSynthesis G A) := by
 classical
 induction A using DirectSum.induction_on with
 | zero =>
   rw [map_zero]
   fun_prop
 | of q A =>
   change Continuous (unitaryMatrixDualCoefficientSynthesis G
     (unitaryMatrixDualCoefficientSingle q A))
   rw [unitaryMatrixDualCoefficientSynthesis_single]
   exact continuous_matrixCoefficientSynthesis
    (unitaryMatrixDualRepresentation q)
    (continuous_unitaryMatrixDualRepresentation q) A
 | add A B hA hB =>
   rw [map_add]
   exact hA.add hB

/-- Fourier analysis at any coordinate dual class recovers its exact inverse-dimension-scaled
transposed coefficient matrix. -/
theorem unitaryMatrixDualCoefficientSynthesis_analysis
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A:UnitaryMatrixDualCoefficientSpace G) (q:UnitaryMatrixDual G) :
 normalizedCompactMatrixFourierCoefficient G
   (unitaryMatrixDualRepresentation q)
   (unitaryMatrixDualCoefficientSynthesis G A) =
 (unitaryMatrixDualDimension q:ℂ)⁻¹ •
   (unitaryMatrixDualCoefficientAt q A).transpose := by
 classical
 letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
   normalizedCompactHaarMeasure_isProbability G
 induction A using DirectSum.induction_on with
 | zero =>
   rw [map_zero, map_zero, Matrix.transpose_zero, smul_zero]
   unfold normalizedCompactMatrixFourierCoefficient
   exact matrixFourierCoefficient_zero
     (normalizedCompactHaarMeasure G)
     (unitaryMatrixDualRepresentation q)
 | of r B =>
   change normalizedCompactMatrixFourierCoefficient G
      (unitaryMatrixDualRepresentation q)
      (unitaryMatrixDualCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle r B)) = _
   rw [unitaryMatrixDualCoefficientSynthesis_single]
   by_cases hrq:r=q
   · subst r
     rw [normalizedCompactMatrixFourierCoefficient_synthesis
       (unitaryMatrixDualRepresentation q)
       (continuous_unitaryMatrixDualRepresentation q)
       (unitary_unitaryMatrixDualRepresentation q)
       (unitaryMatrixDualDimension_pos q) B]
     change (unitaryMatrixDualDimension q : ℂ)⁻¹ • B.transpose =
       (unitaryMatrixDualDimension q : ℂ)⁻¹ •
         (DFinsupp.single
           (β := fun r : UnitaryMatrixDual G =>
             Matrix (Fin (unitaryMatrixDualDimension r))
               (Fin (unitaryMatrixDualDimension r)) ℂ) q B q).transpose
     simp
   · letI := unitaryMatrixDual_representative_inequivalent (Ne.symm hrq)
     rw [normalizedCompactMatrixFourierCoefficient_synthesis_inequivalent
       (unitaryMatrixDualRepresentation r)
       (unitaryMatrixDualRepresentation q)
       (continuous_unitaryMatrixDualRepresentation r)
       (continuous_unitaryMatrixDualRepresentation q)
       (unitary_unitaryMatrixDualRepresentation q) B]
     change 0 = (unitaryMatrixDualDimension q : ℂ)⁻¹ •
       (DFinsupp.single
         (β := fun s : UnitaryMatrixDual G =>
           Matrix (Fin (unitaryMatrixDualDimension s))
             (Fin (unitaryMatrixDualDimension s)) ℂ) r B q).transpose
     simp [hrq]
 | add A B hA hB =>
   rw [map_add]
   have hTransformAdd := matrixFourierCoefficient_add
    (normalizedCompactHaarMeasure G)
    (unitaryMatrixDualRepresentation q)
    (continuous_unitaryMatrixDualRepresentation q)
    (unitaryMatrixDualCoefficientSynthesis G A)
    (unitaryMatrixDualCoefficientSynthesis G B)
    (continuous_unitaryMatrixDualCoefficientSynthesis A)
    (continuous_unitaryMatrixDualCoefficientSynthesis B)
   change matrixFourierCoefficient (normalizedCompactHaarMeasure G)
      (unitaryMatrixDualRepresentation q)
      (fun g => unitaryMatrixDualCoefficientSynthesis G A g +
        unitaryMatrixDualCoefficientSynthesis G B g) = _
   rw [hTransformAdd]
   change normalizedCompactMatrixFourierCoefficient G
        (unitaryMatrixDualRepresentation q)
        (unitaryMatrixDualCoefficientSynthesis G A) +
      normalizedCompactMatrixFourierCoefficient G
        (unitaryMatrixDualRepresentation q)
        (unitaryMatrixDualCoefficientSynthesis G B) = _
   rw [hA, hB, map_add]
   ext row col
   simp [Matrix.transpose_apply, mul_add]

/-- Algebraic Fourier synthesis over the full coordinate dual is injective. -/
theorem unitaryMatrixDualCoefficientSynthesis_injective
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
 Function.Injective (unitaryMatrixDualCoefficientSynthesis G) := by
  intro A B hAB
  ext q row col
  have hFourier := congrArg
    (normalizedCompactMatrixFourierCoefficient G
      (unitaryMatrixDualRepresentation q)) hAB
  rw [unitaryMatrixDualCoefficientSynthesis_analysis A q,
    unitaryMatrixDualCoefficientSynthesis_analysis B q] at hFourier
  have hentry := congrFun (congrFun hFourier col) row
  change (unitaryMatrixDualDimension q:ℂ)⁻¹ *
      unitaryMatrixDualCoefficientAt q A row col =
    (unitaryMatrixDualDimension q:ℂ)⁻¹ *
      unitaryMatrixDualCoefficientAt q B row col at hentry
  have hd0 : (unitaryMatrixDualDimension q:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (unitaryMatrixDualDimension_pos q))
  exact mul_left_cancel₀ (inv_ne_zero hd0) hentry

/-- Exact Fourier inversion for every finitely supported coordinate-dual coefficient family. -/
theorem unitaryMatrixDualCoefficientSynthesis_inversion
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A:UnitaryMatrixDualCoefficientSpace G) (q:UnitaryMatrixDual G) :
 unitaryMatrixDualCoefficientAt q A =
   (unitaryMatrixDualDimension q:ℂ) •
    (normalizedCompactMatrixFourierCoefficient G
      (unitaryMatrixDualRepresentation q)
      (unitaryMatrixDualCoefficientSynthesis G A)).transpose := by
  rw [unitaryMatrixDualCoefficientSynthesis_analysis A q]
  ext row col
  have hd0 : (unitaryMatrixDualDimension q:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (unitaryMatrixDualDimension_pos q))
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp

/-- The algebraic finite-support coefficient subspace in the full function carrier. -/
def unitaryMatrixDualAlgebraicCoefficientSubspace
 (G:Type uG) [Group G] [TopologicalSpace G] : Submodule ℂ (G→ℂ) :=
 LinearMap.range (unitaryMatrixDualCoefficientSynthesis G)

/-- The dependent direct sum is linearly equivalent to its exact synthesized function range. -/
noncomputable def unitaryMatrixDualCoefficientSynthesisEquiv
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
 UnitaryMatrixDualCoefficientSpace G ≃ₗ[ℂ]
   unitaryMatrixDualAlgebraicCoefficientSubspace G :=
 LinearEquiv.ofInjective (unitaryMatrixDualCoefficientSynthesis G)
  unitaryMatrixDualCoefficientSynthesis_injective

end

end Mathematics
end YangMills
