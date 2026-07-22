/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import YangMills.Mathematics.MatrixRepresentationCharacter
import YangMills.Mathematics.NormalizedCompactHaarMeasure

/-!
# Matrix-valued Fourier coefficients of compact-group functions

For a matrix representation `ρ`, a measure `μ`, and a complex function `f`, this file defines the
representation-valued Fourier coefficient coordinatewise by

`f̂(ρ)ᵢⱼ = ∫ g, f(g) ρ(g⁻¹)ᵢⱼ ∂μ`.

Coordinatewise integration avoids imposing an artificial choice of matrix norm. On compact groups,
continuity of `f` and `ρ` derives genuine integrability of every coefficient against any measure
finite on compact sets, in particular probability-normalized Haar measure. Addition, scalar
multiplication, and the zero transform are derived with the exact inverse convention retained.

This is initial nonabelian Fourier infrastructure. It assumes no irreducibility, Schur orthogonality,
Plancherel theorem, Fourier inversion, or Peter–Weyl completeness.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG un

/-- The coordinatewise representation-valued Fourier coefficient with convention
`f̂(ρ) = ∫ f(g)ρ(g⁻¹)dμ(g)`. -/
def matrixFourierCoefficient
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) (f : G → ℂ) : Matrix n n ℂ :=
  fun row column => ∫ g, f g * ρ (g⁻¹) row column ∂μ

@[simp]
theorem matrixFourierCoefficient_apply
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) (f : G → ℂ)
    (row column : n) :
    matrixFourierCoefficient μ ρ f row column =
      ∫ g, f g * ρ (g⁻¹) row column ∂μ :=
  rfl

/-- On a compact domain, every coordinate integrand is genuinely integrable when the function and
matrix representation are continuous and the measure is finite on compact sets. -/
theorem integrable_matrixFourierCoefficient_integrand
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f : G → ℂ) (hf : Continuous f) (row column : n) :
    Integrable (fun g => f g * ρ (g⁻¹) row column) μ := by
  have continuousIntegrand : Continuous (fun g => f g * ρ (g⁻¹) row column) := by
    fun_prop
  simpa only [integrableOn_univ] using
    continuousIntegrand.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- Taking the matrix trace of the Fourier coefficient gives the scalar coefficient against the
inverse trace character. This is the exact bridge from representation-valued Fourier coefficients
to central character analysis. -/
theorem matrixFourierCoefficient_trace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f : G → ℂ) (hf : Continuous f) :
    Matrix.trace (matrixFourierCoefficient μ ρ f) =
      ∫ g, f g * Matrix.trace (ρ (g⁻¹)) ∂μ := by
  rw [Matrix.trace]
  change (∑ i, ∫ g, f g * ρ (g⁻¹) i i ∂μ) = _
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_matrixFourierCoefficient_integrand μ ρ hρ f hf i i)]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [Matrix.trace]
  simp [Finset.mul_sum]

/-- Fourier coefficients preserve addition for continuous functions on a compact group. -/
theorem matrixFourierCoefficient_add
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f h : G → ℂ) (hf : Continuous f) (hh : Continuous h) :
    matrixFourierCoefficient μ ρ (fun g => f g + h g) =
      matrixFourierCoefficient μ ρ f + matrixFourierCoefficient μ ρ h := by
  ext row column
  rw [matrixFourierCoefficient_apply, Matrix.add_apply,
    matrixFourierCoefficient_apply, matrixFourierCoefficient_apply,
    ← integral_add
      (integrable_matrixFourierCoefficient_integrand μ ρ hρ f hf row column)
      (integrable_matrixFourierCoefficient_integrand μ ρ hρ h hh row column)]
  apply integral_congr_ae
  filter_upwards [] with g
  ring

/-- Fourier coefficients commute with complex scalar multiplication. -/
theorem matrixFourierCoefficient_smul
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) (c : ℂ) (f : G → ℂ) :
    matrixFourierCoefficient μ ρ (fun g => c * f g) =
      c • matrixFourierCoefficient μ ρ f := by
  ext row column
  rw [matrixFourierCoefficient_apply]
  change (∫ g, (c * f g) * ρ (g⁻¹) row column ∂μ) =
    c * matrixFourierCoefficient μ ρ f row column
  rw [matrixFourierCoefficient_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  ring

/-- The zero function has the zero matrix Fourier coefficient. -/
@[simp]
theorem matrixFourierCoefficient_zero
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) :
    matrixFourierCoefficient μ ρ (fun _ => 0) = 0 := by
  ext row column
  simp

/-- The exact probability-Haar specialization used by compact nonabelian harmonic analysis. -/
def normalizedCompactMatrixFourierCoefficient
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (f : G → ℂ) : Matrix n n ℂ :=
  matrixFourierCoefficient (normalizedCompactHaarMeasure G) ρ f

@[simp]
theorem normalizedCompactMatrixFourierCoefficient_apply
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (f : G → ℂ) (row column : n) :
    normalizedCompactMatrixFourierCoefficient G ρ f row column =
      ∫ g, f g * ρ (g⁻¹) row column ∂normalizedCompactHaarMeasure G :=
  rfl

end

end Mathematics
end YangMills
