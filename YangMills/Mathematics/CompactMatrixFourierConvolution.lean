/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.Mathematics.CompactMatrixFourierCoefficient

/-!
# Compact-group convolution under the matrix Fourier transform

This file fixes the complex compact-group convolution convention

`(f ⋆ g)(z) = ∫ x, f(x) g(x⁻¹z) dμ_H(x)`

against the project's probability-normalized Haar measure. For the Fourier convention
`f̂(ρ)=∫f(z)ρ(z⁻¹)dμ_H(z)`, it proves

`(f ⋆ g)̂(ρ) = ĝ(ρ) f̂(ρ)`.

The reversed matrix order is forced by `(xy)⁻¹=y⁻¹x⁻¹`; it is not simplified using commutativity.
The proof derives joint product integrability from continuity and compactness, uses genuine Fubini,
performs the exact left-Haar substitution `z=x*y`, and then separates the finite matrix-coordinate
sum. No orthogonality, inversion, or Peter–Weyl theorem is assumed.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG un

/-- Complex convolution with the exact Driver/Sengupta source order. -/
def normalizedCompactHaarComplexConvolution
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f g : G → ℂ) (z : G) : ℂ :=
  ∫ x, f x * g (x⁻¹ * z) ∂normalizedCompactHaarMeasure G

@[simp]
theorem normalizedCompactHaarComplexConvolution_apply
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f g : G → ℂ) (z : G) :
    normalizedCompactHaarComplexConvolution G f g z =
      ∫ x, f x * g (x⁻¹ * z) ∂normalizedCompactHaarMeasure G :=
  rfl

/-- With the exact inverse Fourier convention, convolution transforms to matrix multiplication in
reversed function order. -/
theorem normalizedCompactMatrixFourierCoefficient_convolution
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f g : G → ℂ) (hf : Continuous f) (hg : Continuous g) :
    normalizedCompactMatrixFourierCoefficient G ρ
        (normalizedCompactHaarComplexConvolution G f g) =
      normalizedCompactMatrixFourierCoefficient G ρ g *
        normalizedCompactMatrixFourierCoefficient G ρ f := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  letI : Measure.IsHaarMeasure μ := normalizedCompactHaarMeasure_isHaar G
  letI : Measure.IsMulLeftInvariant μ :=
    (normalizedCompactHaarMeasure_isHaar G).toIsMulLeftInvariant
  ext row column
  change (∫ z, (∫ x, f x * g (x⁻¹ * z) ∂μ) * ρ (z⁻¹) row column ∂μ) =
    ∑ middle,
      (∫ y, g y * ρ (y⁻¹) row middle ∂μ) *
        (∫ x, f x * ρ (x⁻¹) middle column ∂μ)
  have jointIntegrable : Integrable (fun pair : G × G =>
      (f pair.2 * g (pair.2⁻¹ * pair.1)) *
        ρ (pair.1⁻¹) row column) (μ.prod μ) := by
    have jointContinuous : Continuous (fun pair : G × G =>
        (f pair.2 * g (pair.2⁻¹ * pair.1)) *
          ρ (pair.1⁻¹) row column) := by
      fun_prop
    simpa only [integrableOn_univ] using
      jointContinuous.continuousOn.integrableOn_compact
        (μ := μ.prod μ) isCompact_univ
  calc
    (∫ z, (∫ x, f x * g (x⁻¹ * z) ∂μ) *
          ρ (z⁻¹) row column ∂μ) =
        ∫ z, ∫ x, (f x * g (x⁻¹ * z)) *
          ρ (z⁻¹) row column ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [integral_mul_const]
    _ = ∫ x, ∫ z, (f x * g (x⁻¹ * z)) *
          ρ (z⁻¹) row column ∂μ ∂μ := by
      exact integral_integral_swap jointIntegrable
    _ = _ := by
      have innerFormula (x : G) :
          (∫ z, (f x * g (x⁻¹ * z)) * ρ (z⁻¹) row column ∂μ) =
            ∑ middle,
              (∫ y, g y * ρ (y⁻¹) row middle ∂μ) *
                (f x * ρ (x⁻¹) middle column) := by
        rw [← integral_mul_left_eq_self
          (fun z => (f x * g (x⁻¹ * z)) *
            ρ (z⁻¹) row column) x]
        simp only [inv_mul_cancel_left, mul_inv_rev, map_mul, Matrix.mul_apply]
        simp_rw [Finset.mul_sum]
        rw [integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro middle _
          have integrandEq :
              (fun y => f x * g y *
                (ρ (y⁻¹) row middle * ρ (x⁻¹) middle column)) =
              (fun y => (g y * ρ (y⁻¹) row middle) *
                (f x * ρ (x⁻¹) middle column)) := by
            funext y
            ring
          rw [integrandEq, integral_mul_const]
        · intro middle _
          have baseIntegrable := integrable_matrixFourierCoefficient_integrand
            μ ρ hρ g hg row middle
          have integrandEq :
              (fun y => f x * g y *
                (ρ (y⁻¹) row middle * ρ (x⁻¹) middle column)) =
              (fun y => (g y * ρ (y⁻¹) row middle) *
                (f x * ρ (x⁻¹) middle column)) := by
            funext y
            ring
          rw [integrandEq]
          exact baseIntegrable.mul_const
            (f x * ρ (x⁻¹) middle column)
      simp_rw [innerFormula]
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro middle _
        rw [integral_const_mul]
      · intro middle _
        exact (integrable_matrixFourierCoefficient_integrand
          μ ρ hρ f hf middle column).const_mul
            (∫ y, g y * ρ (y⁻¹) row middle ∂μ)

end

end Mathematics
end YangMills
