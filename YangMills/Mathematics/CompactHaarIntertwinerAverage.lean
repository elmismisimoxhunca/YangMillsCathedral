/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import YangMills.Mathematics.CompactRepresentationAveragedInnerProductCore

/-!
# Haar averaging produces intertwiners

For continuous finite matrix representations `ρ` and `σ`, this file averages an arbitrary
rectangular matrix `A` by

`P(A) = ∫ g, σ(g⁻¹) A ρ(g) dμ_H(g)`

coordinatewise. It proves genuine coefficient integrability and the exact intertwining identity

`σ(h) P(A) = P(A) ρ(h)`.

The proof uses finite sum/integral interchange and the exact right-Haar substitution `g ↦ g*h`.
This is the analytic averaging operator needed before applying algebraic Schur lemmas. No
irreducibility, scalar-multiple conclusion, or matrix-coefficient orthogonality is assumed here.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Coordinatewise normalized-Haar average of an arbitrary map between two matrix
representations. -/
def compactHaarIntertwinerAverage
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  fun row column =>
    ∫ g, (σ (g⁻¹) * A * ρ g) row column
      ∂normalizedCompactHaarMeasure G

@[simp]
theorem compactHaarIntertwinerAverage_apply
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) (row : Fin m) (column : Fin n) :
    compactHaarIntertwinerAverage σ ρ A row column =
      ∫ g, (σ (g⁻¹) * A * ρ g) row column
        ∂normalizedCompactHaarMeasure G :=
  rfl

/-- Every coordinate of the conjugated rectangular matrix family is genuinely integrable. -/
theorem integrable_compactHaarIntertwinerAverage_integrand
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ) (row : Fin m) (column : Fin n) :
    Integrable (fun g => (σ (g⁻¹) * A * ρ g) row column)
      (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  have continuousIntegrand : Continuous
      (fun g => (σ (g⁻¹) * A * ρ g) row column) := by
    fun_prop
  simpa only [integrableOn_univ] using
    continuousIntegrand.continuousOn.integrableOn_compact
      (μ := normalizedCompactHaarMeasure G) isCompact_univ

/-- Haar averaging an arbitrary rectangular matrix produces an exact intertwiner from `ρ` to `σ`. -/
theorem compactHaarIntertwinerAverage_intertwines
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ) (h : G) :
    σ h * compactHaarIntertwinerAverage σ ρ A =
      compactHaarIntertwinerAverage σ ρ A * ρ h := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  letI : Measure.IsMulRightInvariant μ :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  ext row column
  have leftIntegral :
      (σ h * compactHaarIntertwinerAverage σ ρ A) row column =
        ∫ g, (σ h * (σ (g⁻¹) * A * ρ g)) row column ∂μ := by
    rw [Matrix.mul_apply]
    change (∑ middle, σ h row middle *
      ∫ g, (σ (g⁻¹) * A * ρ g) middle column ∂μ) = _
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum Finset.univ]
    · apply integral_congr_ae
      filter_upwards [] with g
      rw [Matrix.mul_apply]
    · intro middle _
      exact (integrable_compactHaarIntertwinerAverage_integrand
        σ ρ hσ hρ A middle column).const_mul (σ h row middle)
  have rightIntegral :
      (compactHaarIntertwinerAverage σ ρ A * ρ h) row column =
        ∫ g, ((σ (g⁻¹) * A * ρ g) * ρ h) row column ∂μ := by
    rw [Matrix.mul_apply]
    change (∑ middle,
      (∫ g, (σ (g⁻¹) * A * ρ g) row middle ∂μ) *
        ρ h middle column) = _
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum Finset.univ]
    · apply integral_congr_ae
      filter_upwards [] with g
      rw [Matrix.mul_apply]
    · intro middle _
      exact (integrable_compactHaarIntertwinerAverage_integrand
        σ ρ hσ hρ A row middle).mul_const (ρ h middle column)
  rw [leftIntegral, rightIntegral]
  calc
    (∫ g, (σ h * (σ (g⁻¹) * A * ρ g)) row column ∂μ) =
        ∫ g, (σ h * (σ ((g * h)⁻¹) * A * ρ (g * h)))
          row column ∂μ :=
      (integral_mul_right_eq_self
        (fun g => (σ h * (σ (g⁻¹) * A * ρ g)) row column) h).symm
    _ = ∫ g, ((σ (g⁻¹) * A * ρ g) * ρ h) row column ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [mul_inv_rev, map_mul]
      apply congrArg (fun matrix : Matrix (Fin m) (Fin n) ℂ =>
        matrix row column)
      calc
        σ h * (σ h⁻¹ * σ g⁻¹ * A * (ρ g * ρ h)) =
            (σ h * σ h⁻¹) * σ g⁻¹ * A * (ρ g * ρ h) := by
          simp only [Matrix.mul_assoc]
        _ = σ g⁻¹ * A * ρ g * ρ h := by
          rw [← map_mul]
          simp only [mul_inv_cancel, map_one, Matrix.one_mul, Matrix.mul_assoc]

end

end Mathematics
end YangMills
