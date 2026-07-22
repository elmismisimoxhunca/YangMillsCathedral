/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierConvolution

/-!
# Haar averaging for finite-dimensional compact-group representations

Hall, Proposition 5.17, averages a finite-dimensional inner product over a compact group to obtain
an invariant positive inner product. This file formalizes the analytic core for continuous complex
matrix representations. It defines the standard coordinate Hermitian pairing and its normalized-Haar
average, proves genuine compact-domain integrability and exact representation invariance, and proves
strict positivity of the averaged norm square away from zero.

The positivity proof does not infer positivity merely from pointwise nonnegativity: continuity gives
an open nonzero support at the identity, and the Haar measure's positive-open-set property gives that
support positive measure.

This layer has not yet packaged the averaged pairing as an `InnerProductSpace` instance or proved
Schur orthogonality, Plancherel, or Peter–Weyl completeness.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory
open scoped BigOperators

noncomputable section

universe uG

/-- The standard coordinate Hermitian pairing, conjugate-linear in the first argument. -/
def coordinateHermitianPairing
    {n : ℕ} (first second : Fin n → ℂ) : ℂ :=
  ∑ i, star (first i) * second i

/-- Haar average of the standard coordinate Hermitian pairing along a matrix representation. -/
def compactRepresentationAveragedPairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (first second : Fin n → ℂ) : ℂ :=
  ∫ g, coordinateHermitianPairing
      (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second)
    ∂normalizedCompactHaarMeasure G

/-- The integrand defining the averaged Hermitian pairing is continuous. -/
theorem continuous_compactRepresentationAveragedPairing_integrand
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (first second : Fin n → ℂ) :
    Continuous (fun g => coordinateHermitianPairing
      (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second)) := by
  unfold coordinateHermitianPairing Matrix.mulVec dotProduct
  fun_prop

/-- The averaged Hermitian pairing has a genuinely integrable defining function. -/
theorem integrable_compactRepresentationAveragedPairing_integrand
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (first second : Fin n → ℂ) :
    Integrable (fun g => coordinateHermitianPairing
      (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second))
      (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  have continuousIntegrand :=
    continuous_compactRepresentationAveragedPairing_integrand
      ρ hρ first second
  simpa only [integrableOn_univ] using
    continuousIntegrand.continuousOn.integrableOn_compact
      (μ := normalizedCompactHaarMeasure G) isCompact_univ

/-- The averaged pairing is invariant under simultaneous action by the same representation
matrix. The proof uses exact right Haar invariance and the homomorphism multiplication order. -/
theorem compactRepresentationAveragedPairing_invariant
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h : G) (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ
        (Matrix.mulVec (ρ h) first) (Matrix.mulVec (ρ h) second) =
      compactRepresentationAveragedPairing ρ first second := by
  let μ := normalizedCompactHaarMeasure G
  letI : Measure.IsMulRightInvariant μ :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  change (∫ g, coordinateHermitianPairing
      (Matrix.mulVec (ρ g) (Matrix.mulVec (ρ h) first))
      (Matrix.mulVec (ρ g) (Matrix.mulVec (ρ h) second)) ∂μ) =
    ∫ g, coordinateHermitianPairing
      (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second) ∂μ
  simp_rw [Matrix.mulVec_mulVec, ← map_mul]
  exact integral_mul_right_eq_self
    (fun g => coordinateHermitianPairing
      (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second)) h

/-- The real averaged coordinate norm square. -/
def compactRepresentationAveragedNormSq
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (vector : Fin n → ℂ) : ℝ :=
  ∫ g, ∑ i, Complex.normSq (Matrix.mulVec (ρ g) vector i)
    ∂normalizedCompactHaarMeasure G

/-- The averaged norm square is invariant under the representation. -/
theorem compactRepresentationAveragedNormSq_invariant
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h : G) (vector : Fin n → ℂ) :
    compactRepresentationAveragedNormSq ρ (Matrix.mulVec (ρ h) vector) =
      compactRepresentationAveragedNormSq ρ vector := by
  let μ := normalizedCompactHaarMeasure G
  letI : Measure.IsMulRightInvariant μ :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  change (∫ g, ∑ i, Complex.normSq
      (Matrix.mulVec (ρ g) (Matrix.mulVec (ρ h) vector) i) ∂μ) =
    ∫ g, ∑ i, Complex.normSq (Matrix.mulVec (ρ g) vector i) ∂μ
  simp_rw [Matrix.mulVec_mulVec, ← map_mul]
  exact integral_mul_right_eq_self
    (fun g => ∑ i, Complex.normSq (Matrix.mulVec (ρ g) vector i)) h

/-- Haar averaging is strictly positive away from the zero vector. -/
theorem compactRepresentationAveragedNormSq_pos
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (vector : Fin n → ℂ) (hvector : vector ≠ 0) :
    0 < compactRepresentationAveragedNormSq ρ vector := by
  let μ := normalizedCompactHaarMeasure G
  letI : Measure.IsHaarMeasure μ := normalizedCompactHaarMeasure_isHaar G
  let normIntegrand : G → ℝ := fun g =>
    ∑ i, Complex.normSq (Matrix.mulVec (ρ g) vector i)
  have integrandContinuous : Continuous normIntegrand := by
    unfold normIntegrand Matrix.mulVec dotProduct
    fun_prop
  have integrandIntegrable : Integrable normIntegrand μ := by
    simpa only [integrableOn_univ] using
      integrandContinuous.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  have integrandNonnegative : 0 ≤ normIntegrand := by
    intro g
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have nonzeroCoordinate : ∃ i, vector i ≠ 0 := by
    by_contra noCoordinate
    apply hvector
    funext i
    exact not_ne_iff.mp (not_exists.mp noCoordinate i)
  have positiveAtIdentity : 0 < normIntegrand 1 := by
    simp only [normIntegrand, map_one, Matrix.one_mulVec]
    apply Finset.sum_pos'
    · intro i _
      exact Complex.normSq_nonneg _
    · obtain ⟨i, hi⟩ := nonzeroCoordinate
      exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  have supportPositive : 0 < μ (Function.support normIntegrand) :=
    IsOpen.measure_pos μ integrandContinuous.isOpen_support
      ⟨1, ne_of_gt positiveAtIdentity⟩
  change 0 < ∫ g, normIntegrand g ∂μ
  exact (integral_pos_iff_support_of_nonneg
    integrandNonnegative integrandIntegrable).2 supportPositive

end

end Mathematics
end YangMills
