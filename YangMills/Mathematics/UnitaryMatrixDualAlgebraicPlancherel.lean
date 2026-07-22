/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Data.DFinsupp.BigOperators
import YangMills.Mathematics.UnitaryMatrixDualAlgebraicFourier

/-!
# Algebraic Plancherel over the coordinate unitary dual

On the dependent finite-support direct sum over `UnitaryMatrixDual G`, this file defines the exact
coefficient-side pairing

`∑q (dim q)⁻¹ ⟨A(q),B(q)⟩ₕₛ`

as an additive homomorphism in the conjugated first coordinate. It proves that this is the normalized
Haar pairing of the synthesized functions. It also defines the finite-support Fourier-side pairing
and proves the all-coordinate-class algebraic Plancherel identity

`⟨f_A,f_B⟩ = ∑q (dim q) ⟨f̂_A(q),f̂_B(q)⟩ₕₛ`.

Every sum is finite because its first coefficient family lies in `DirectSum`. This is not an infinite
series theorem and does not establish `L²` completeness or Peter–Weyl density.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Zero in the first matrix slot has zero Hilbert–Schmidt pairing. -/
theorem matrixHilbertSchmidtPairing_zero_left {n:ℕ}
 (B:Matrix (Fin n) (Fin n) ℂ) : matrixHilbertSchmidtPairing 0 B=0 := by
 unfold matrixHilbertSchmidtPairing
 simp

/-- The Hilbert–Schmidt pairing is additive in its conjugated first matrix slot. -/
theorem matrixHilbertSchmidtPairing_add_left {n:ℕ}
 (A B C:Matrix (Fin n) (Fin n) ℂ) :
 matrixHilbertSchmidtPairing (A+B) C =
 matrixHilbertSchmidtPairing A C + matrixHilbertSchmidtPairing B C := by
 unfold matrixHilbertSchmidtPairing
 simp only [Matrix.add_apply]
 rw [←Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro row _
 rw [←Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro col _
 change (starRingEnd ℂ) (A row col + B row col) * C row col =
   (starRingEnd ℂ) (A row col) * C row col +
     (starRingEnd ℂ) (B row col) * C row col
 rw [map_add]
 ring

/-- The finite-support inverse-dimension-weighted coefficient pairing, bundled additively in its
first slot. -/
noncomputable def unitaryMatrixDualAlgebraicCoefficientPairingAddHom
 {G:Type uG} [Group G] [TopologicalSpace G]
 (B:UnitaryMatrixDualCoefficientSpace G) :
 UnitaryMatrixDualCoefficientSpace G →+ ℂ := by
 letI := Classical.decEq (UnitaryMatrixDual G)
 apply DirectSum.toAddMonoid
 intro q
 exact
  { toFun := fun Aq => (unitaryMatrixDualDimension q:ℂ)⁻¹ *
      matrixHilbertSchmidtPairing Aq (unitaryMatrixDualCoefficientAt q B)
    map_zero' := by simp [matrixHilbertSchmidtPairing_zero_left]
    map_add' := by
      intro X Y
      rw [matrixHilbertSchmidtPairing_add_left]
      ring }

def unitaryMatrixDualAlgebraicCoefficientPairing
 {G:Type uG} [Group G] [TopologicalSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) : ℂ :=
 unitaryMatrixDualAlgebraicCoefficientPairingAddHom B A

@[simp] theorem unitaryMatrixDualAlgebraicCoefficientPairing_zero_left
 {G:Type uG} [Group G] [TopologicalSpace G]
 (B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicCoefficientPairing 0 B=0 := by
 exact map_zero (unitaryMatrixDualAlgebraicCoefficientPairingAddHom B)

@[simp] theorem unitaryMatrixDualAlgebraicCoefficientPairing_single_left
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G)
 (Aq:Matrix (Fin (unitaryMatrixDualDimension q))
   (Fin (unitaryMatrixDualDimension q)) ℂ)
 (B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicCoefficientPairing
   (unitaryMatrixDualCoefficientSingle q Aq) B =
 (unitaryMatrixDualDimension q:ℂ)⁻¹ *
   matrixHilbertSchmidtPairing Aq (unitaryMatrixDualCoefficientAt q B) := by
 classical
 unfold unitaryMatrixDualAlgebraicCoefficientPairing
 unfold unitaryMatrixDualAlgebraicCoefficientPairingAddHom
 unfold unitaryMatrixDualCoefficientSingle
 rw [DirectSum.lof_eq_of, DirectSum.toAddMonoid_of]
 rfl

theorem unitaryMatrixDualAlgebraicCoefficientPairing_add_left
 {G:Type uG} [Group G] [TopologicalSpace G]
 (A C B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicCoefficientPairing (A+C) B =
 unitaryMatrixDualAlgebraicCoefficientPairing A B +
 unitaryMatrixDualAlgebraicCoefficientPairing C B := by
 exact map_add (unitaryMatrixDualAlgebraicCoefficientPairingAddHom B) A C

/-- The coefficient-side algebraic pairing equals normalized Haar pairing after synthesis. -/
theorem unitaryMatrixDualAlgebraicCoefficientSynthesis_pairing
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) :
 (∫g,star (unitaryMatrixDualCoefficientSynthesis G A g)*
   unitaryMatrixDualCoefficientSynthesis G B g
   ∂normalizedCompactHaarMeasure G) =
 unitaryMatrixDualAlgebraicCoefficientPairing A B := by
 classical
 let μ := normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
 induction A using DirectSum.induction_on with
 | zero =>
   rw [map_zero]
   simp [unitaryMatrixDualAlgebraicCoefficientPairing]
 | of q Aq =>
   change (∫g,star (unitaryMatrixDualCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle q Aq) g)*
      unitaryMatrixDualCoefficientSynthesis G B g ∂μ) =
    unitaryMatrixDualAlgebraicCoefficientPairing
      (unitaryMatrixDualCoefficientSingle q Aq) B
   rw [unitaryMatrixDualCoefficientSynthesis_single,
     coefficientSynthesis_pairing_fourier
       (unitaryMatrixDualRepresentation q)
       (continuous_unitaryMatrixDualRepresentation q)
       (unitary_unitaryMatrixDualRepresentation q) Aq
       (unitaryMatrixDualCoefficientSynthesis G B)
       (continuous_unitaryMatrixDualCoefficientSynthesis B),
     unitaryMatrixDualCoefficientSynthesis_analysis B q]
   have htranspose :
      (((unitaryMatrixDualDimension q:ℂ)⁻¹ •
        (unitaryMatrixDualCoefficientAt q B).transpose).transpose) =
       (unitaryMatrixDualDimension q:ℂ)⁻¹ •
        unitaryMatrixDualCoefficientAt q B := by
     ext row col
     simp
   rw [htranspose]
   have hsmul := matrixHilbertSchmidtPairing_smul
     (1:ℂ) ((unitaryMatrixDualDimension q:ℂ)⁻¹)
     Aq (unitaryMatrixDualCoefficientAt q B)
   have hvalue : matrixHilbertSchmidtPairing Aq
      ((unitaryMatrixDualDimension q:ℂ)⁻¹ •
        unitaryMatrixDualCoefficientAt q B) =
      (unitaryMatrixDualDimension q:ℂ)⁻¹ *
        matrixHilbertSchmidtPairing Aq
          (unitaryMatrixDualCoefficientAt q B) := by
     simpa using hsmul
   rw [hvalue]
   rw [unitaryMatrixDualAlgebraicCoefficientPairing_single_left]
 | add A C hA hC =>
   rw [map_add]
   have hIntA : Integrable (fun g =>
      star (unitaryMatrixDualCoefficientSynthesis G A g)*
        unitaryMatrixDualCoefficientSynthesis G B g) μ := by
     have hc : Continuous (fun g =>
      star (unitaryMatrixDualCoefficientSynthesis G A g)*
        unitaryMatrixDualCoefficientSynthesis G B g) :=
       (continuous_unitaryMatrixDualCoefficientSynthesis A).star.mul
        (continuous_unitaryMatrixDualCoefficientSynthesis B)
     simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hIntC : Integrable (fun g =>
      star (unitaryMatrixDualCoefficientSynthesis G C g)*
        unitaryMatrixDualCoefficientSynthesis G B g) μ := by
     have hc : Continuous (fun g =>
      star (unitaryMatrixDualCoefficientSynthesis G C g)*
        unitaryMatrixDualCoefficientSynthesis G B g) :=
       (continuous_unitaryMatrixDualCoefficientSynthesis C).star.mul
        (continuous_unitaryMatrixDualCoefficientSynthesis B)
     simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hpoint : (fun g =>
      star ((unitaryMatrixDualCoefficientSynthesis G A+
        unitaryMatrixDualCoefficientSynthesis G C) g)*
          unitaryMatrixDualCoefficientSynthesis G B g) =
      fun g =>
       star (unitaryMatrixDualCoefficientSynthesis G A g)*
          unitaryMatrixDualCoefficientSynthesis G B g +
       star (unitaryMatrixDualCoefficientSynthesis G C g)*
          unitaryMatrixDualCoefficientSynthesis G B g := by
     funext g
     change (starRingEnd ℂ)
       (unitaryMatrixDualCoefficientSynthesis G A g+
        unitaryMatrixDualCoefficientSynthesis G C g)*
         unitaryMatrixDualCoefficientSynthesis G B g =
       (starRingEnd ℂ) (unitaryMatrixDualCoefficientSynthesis G A g) *
         unitaryMatrixDualCoefficientSynthesis G B g +
       (starRingEnd ℂ) (unitaryMatrixDualCoefficientSynthesis G C g) *
         unitaryMatrixDualCoefficientSynthesis G B g
     rw [map_add]
     ring
   rw [hpoint,integral_add hIntA hIntC,hA,hC]
   rw [unitaryMatrixDualAlgebraicCoefficientPairing_add_left]

/-- The finite-support dimension-weighted Fourier pairing, bundled additively in its first slot. -/
noncomputable def unitaryMatrixDualAlgebraicFourierPairingAddHom
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (B:UnitaryMatrixDualCoefficientSpace G) :
 UnitaryMatrixDualCoefficientSpace G →+ ℂ := by
 letI := Classical.decEq (UnitaryMatrixDual G)
 apply DirectSum.toAddMonoid
 intro q
 exact
  { toFun := fun Aq => (unitaryMatrixDualDimension q:ℂ) *
      matrixHilbertSchmidtPairing
       ((unitaryMatrixDualDimension q:ℂ)⁻¹ • Aq.transpose)
       (normalizedCompactMatrixFourierCoefficient G
        (unitaryMatrixDualRepresentation q)
        (unitaryMatrixDualCoefficientSynthesis G B))
    map_zero' := by simp [matrixHilbertSchmidtPairing_zero_left]
    map_add' := by
      intro X Y
      have htranspose : (X+Y).transpose=X.transpose+Y.transpose := by
       ext row col
       simp
      rw [htranspose,smul_add,matrixHilbertSchmidtPairing_add_left]
      ring }

def unitaryMatrixDualAlgebraicFourierPairing
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) : ℂ :=
 unitaryMatrixDualAlgebraicFourierPairingAddHom B A

@[simp] theorem unitaryMatrixDualAlgebraicFourierPairing_single_left
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (q:UnitaryMatrixDual G)
 (Aq:Matrix (Fin (unitaryMatrixDualDimension q))
  (Fin (unitaryMatrixDualDimension q)) ℂ)
 (B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicFourierPairing
   (unitaryMatrixDualCoefficientSingle q Aq) B =
 (unitaryMatrixDualDimension q:ℂ) *
  matrixHilbertSchmidtPairing
   ((unitaryMatrixDualDimension q:ℂ)⁻¹ • Aq.transpose)
   (normalizedCompactMatrixFourierCoefficient G
    (unitaryMatrixDualRepresentation q)
    (unitaryMatrixDualCoefficientSynthesis G B)) := by
 classical
 unfold unitaryMatrixDualAlgebraicFourierPairing
 unfold unitaryMatrixDualAlgebraicFourierPairingAddHom
 unfold unitaryMatrixDualCoefficientSingle
 rw [DirectSum.lof_eq_of,DirectSum.toAddMonoid_of]
 rfl

theorem unitaryMatrixDualAlgebraicFourierPairing_add_left
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A C B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicFourierPairing (A+C) B =
 unitaryMatrixDualAlgebraicFourierPairing A B+
 unitaryMatrixDualAlgebraicFourierPairing C B := by
 exact map_add (unitaryMatrixDualAlgebraicFourierPairingAddHom B) A C

/-- Coefficient-side and Fourier-side algebraic pairings agree over all coordinate dual classes. -/
theorem unitaryMatrixDualAlgebraicCoefficientPairing_eq_fourierPairing
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) :
 unitaryMatrixDualAlgebraicCoefficientPairing A B =
 unitaryMatrixDualAlgebraicFourierPairing A B := by
 classical
 induction A using DirectSum.induction_on with
 | zero =>
   simp [unitaryMatrixDualAlgebraicCoefficientPairing,
    unitaryMatrixDualAlgebraicFourierPairing]
 | of q Aq =>
   change unitaryMatrixDualAlgebraicCoefficientPairing
      (unitaryMatrixDualCoefficientSingle q Aq) B =
    unitaryMatrixDualAlgebraicFourierPairing
      (unitaryMatrixDualCoefficientSingle q Aq) B
   rw [unitaryMatrixDualAlgebraicCoefficientPairing_single_left,
    unitaryMatrixDualAlgebraicFourierPairing_single_left,
    unitaryMatrixDualCoefficientSynthesis_analysis B q,
    matrixHilbertSchmidtPairing_smul,
    matrixHilbertSchmidtPairing_transpose]
   have hd0 : (unitaryMatrixDualDimension q:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (unitaryMatrixDualDimension_pos q))
   have hstar : star ((unitaryMatrixDualDimension q:ℂ)⁻¹) =
      (unitaryMatrixDualDimension q:ℂ)⁻¹ := by
    change (starRingEnd ℂ) ((unitaryMatrixDualDimension q:ℂ)⁻¹) = _
    rw [map_inv₀]
    simp
   rw [hstar]
   field_simp
 | add A C hA hC =>
   rw [unitaryMatrixDualAlgebraicCoefficientPairing_add_left,
    unitaryMatrixDualAlgebraicFourierPairing_add_left,hA,hC]

/-- Exact all-coordinate-class algebraic Plancherel for finitely supported coefficient families. -/
theorem unitaryMatrixDualAlgebraicCoefficientSynthesis_fourier_plancherel
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) :
 (∫g,star (unitaryMatrixDualCoefficientSynthesis G A g)*
   unitaryMatrixDualCoefficientSynthesis G B g
   ∂normalizedCompactHaarMeasure G) =
 unitaryMatrixDualAlgebraicFourierPairing A B := by
 rw [unitaryMatrixDualAlgebraicCoefficientSynthesis_pairing,
  unitaryMatrixDualAlgebraicCoefficientPairing_eq_fourierPairing]

end

end Mathematics
end YangMills
