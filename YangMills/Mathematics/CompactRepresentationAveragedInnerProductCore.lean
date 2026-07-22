/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import YangMills.Mathematics.CompactRepresentationHaarAverage

/-!
# The inner-product core obtained by compact-group Haar averaging

This file completes the algebraic packaging of Hall's compact-representation averaging argument.
The previously constructed averaged coordinate pairing is proved conjugate symmetric,
conjugate-linear/additive in its first argument, nonnegative on the diagonal, and definite. It is
then packaged as Mathlib's `InnerProductSpace.Core` on the finite coordinate vector space.

The core is not installed as a global `InnerProductSpace` instance: the ordinary function carrier
already has topology/norm infrastructure whose compatibility with the averaged norm requires a
separate finite-dimensional comparison. No unitarizing coordinate equivalence or Peter–Weyl theorem
is claimed here.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

universe uG

/-- Conjugate symmetry of the standard coordinate Hermitian pairing. -/
theorem coordinateHermitianPairing_conj_symm
    {n : ℕ} (first second : Fin n → ℂ) :
    star (coordinateHermitianPairing second first) =
      coordinateHermitianPairing first second := by
  unfold coordinateHermitianPairing
  change (starRingEnd ℂ) (∑ i, star (second i) * first i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, starRingEnd_apply]
  rw [star_star]
  ring

/-- Additivity of the coordinate Hermitian pairing in its first argument. -/
theorem coordinateHermitianPairing_add_left
    {n : ℕ} (first second third : Fin n → ℂ) :
    coordinateHermitianPairing (first + second) third =
      coordinateHermitianPairing first third +
        coordinateHermitianPairing second third := by
  unfold coordinateHermitianPairing
  simp only [Pi.add_apply, star_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Conjugate homogeneity of the coordinate Hermitian pairing in its first argument. -/
theorem coordinateHermitianPairing_smul_left
    {n : ℕ} (scalar : ℂ) (first second : Fin n → ℂ) :
    coordinateHermitianPairing (scalar • first) second =
      star scalar * coordinateHermitianPairing first second := by
  unfold coordinateHermitianPairing
  simp only [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul]
  rw [star_mul]
  ring

/-- The real part of averaged self-pairing is exactly the previously constructed real averaged norm
square. -/
theorem compactRepresentationAveragedPairing_self_re
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (vector : Fin n → ℂ) :
    (compactRepresentationAveragedPairing ρ vector vector).re =
      compactRepresentationAveragedNormSq ρ vector := by
  have integrablePairing :=
    integrable_compactRepresentationAveragedPairing_integrand
      ρ hρ vector vector
  unfold compactRepresentationAveragedPairing
    compactRepresentationAveragedNormSq
  change RCLike.re (∫ g, coordinateHermitianPairing
    (Matrix.mulVec (ρ g) vector) (Matrix.mulVec (ρ g) vector)
    ∂normalizedCompactHaarMeasure G) = _
  rw [← integral_re integrablePairing]
  apply integral_congr_ae
  filter_upwards [] with g
  unfold coordinateHermitianPairing
  change Complex.reCLM (∑ i,
    star (Matrix.mulVec (ρ g) vector i) *
      Matrix.mulVec (ρ g) vector i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star (Matrix.mulVec (ρ g) vector i) *
    Matrix.mulVec (ρ g) vector i).re = _
  simp [Complex.normSq_apply]

/-- Conjugate symmetry of the normalized-Haar averaged pairing. -/
theorem compactRepresentationAveragedPairing_conj_symm
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (first second : Fin n → ℂ) :
    star (compactRepresentationAveragedPairing ρ second first) =
      compactRepresentationAveragedPairing ρ first second := by
  unfold compactRepresentationAveragedPairing
  change (starRingEnd ℂ) (∫ g, coordinateHermitianPairing
    (Matrix.mulVec (ρ g) second) (Matrix.mulVec (ρ g) first)
    ∂normalizedCompactHaarMeasure G) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with g
  exact coordinateHermitianPairing_conj_symm _ _

/-- Additivity of the normalized-Haar averaged pairing in its first argument. -/
theorem compactRepresentationAveragedPairing_add_left
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (first second third : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ (first + second) third =
      compactRepresentationAveragedPairing ρ first third +
        compactRepresentationAveragedPairing ρ second third := by
  unfold compactRepresentationAveragedPairing
  simp_rw [Matrix.mulVec_add, coordinateHermitianPairing_add_left]
  rw [integral_add]
  · exact integrable_compactRepresentationAveragedPairing_integrand
      ρ hρ first third
  · exact integrable_compactRepresentationAveragedPairing_integrand
      ρ hρ second third

/-- Conjugate homogeneity of the normalized-Haar averaged pairing in its first argument. -/
theorem compactRepresentationAveragedPairing_smul_left
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (scalar : ℂ) (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ (scalar • first) second =
      star scalar * compactRepresentationAveragedPairing ρ first second := by
  unfold compactRepresentationAveragedPairing
  simp_rw [Matrix.mulVec_smul, coordinateHermitianPairing_smul_left]
  exact integral_const_mul _ _

/-- The positive definite inner-product core obtained from normalized-Haar averaging. It is a named
value, not a global instance, so no unrelated pre-existing norm is silently replaced. -/
@[reducible]
noncomputable def compactRepresentationAveragedInnerProductCore
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) : InnerProductSpace.Core ℂ (Fin n → ℂ) where
  inner := compactRepresentationAveragedPairing ρ
  conj_inner_symm := compactRepresentationAveragedPairing_conj_symm ρ
  re_inner_nonneg := by
    intro vector
    change 0 ≤ (compactRepresentationAveragedPairing ρ vector vector).re
    rw [compactRepresentationAveragedPairing_self_re ρ hρ]
    apply integral_nonneg
    intro g
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  add_left := compactRepresentationAveragedPairing_add_left ρ hρ
  smul_left := by
    intro first second scalar
    simpa only [starRingEnd_apply] using
      compactRepresentationAveragedPairing_smul_left ρ scalar first second
  definite := by
    intro vector selfPairingZero
    by_contra vectorNonzero
    have positive := compactRepresentationAveragedNormSq_pos
      ρ hρ vector vectorNonzero
    have realPart := compactRepresentationAveragedPairing_self_re ρ hρ vector
    rw [selfPairingZero] at realPart
    norm_num at realPart
    linarith

/-- The core's pairing is definitionally the exact normalized-Haar averaged pairing. -/
@[simp]
theorem compactRepresentationAveragedInnerProductCore_inner
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (first second : Fin n → ℂ) :
    @inner ℂ (Fin n → ℂ)
      (compactRepresentationAveragedInnerProductCore ρ hρ).toCore.toInner
      first second = compactRepresentationAveragedPairing ρ first second :=
  rfl

end

end Mathematics
end YangMills
