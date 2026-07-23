/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierConvolution

/-!
# Continuous convolution on a compact group

This file packages the project's normalized-Haar convolution

`(f ⋆ g)(z) = ∫ x, f(x) g(x⁻¹z) dμ_H(x)`

as a continuous function whenever both inputs are continuous. Under the explicit
`SecondCountableTopology` hypothesis needed by Mathlib's parametric Bochner-integral theorem, it
proves the sharp Banach-algebra estimate `‖f⋆g‖∞ ≤ ‖f‖∞ ‖g‖∞` and packages convolution by either
fixed input as a continuous linear map on `C(G, ℂ)`.

The convention and noncommutative input order are inherited unchanged from
`CompactMatrixFourierConvolution`. No associativity, commutativity, Fourier inversion, or
Peter–Weyl completeness is used here.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Normalized-Haar convolution of two continuous complex functions, packaged as a continuous
function. -/
noncomputable def normalizedCompactHaarContinuousConvolution (f g:C(G,ℂ)):C(G,ℂ):=
 ⟨normalizedCompactHaarComplexConvolution G f g, by
  let μ:=normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ:=normalizedCompactHaarMeasure_isProbability G
  have hc:Continuous (Function.uncurry (fun z x:G=>f x*g (x⁻¹*z))):=by fun_prop
  change Continuous (fun z=>∫x,f x*g (x⁻¹*z) ∂μ)
  simpa only [Measure.restrict_univ] using
   (continuous_parametric_integral_of_continuous hc (μ:=μ) (s:=Set.univ) isCompact_univ)⟩

@[simp] theorem normalizedCompactHaarContinuousConvolution_apply (f g : C(G, ℂ)) (z : G) :
    normalizedCompactHaarContinuousConvolution f g z =
 normalizedCompactHaarComplexConvolution G f g z:=rfl

/-- Sharp probability-Haar sup-norm estimate for continuous convolution. -/
theorem norm_normalizedCompactHaarContinuousConvolution_le (f g : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolution f g‖ ≤ ‖f‖ * ‖g‖ := by
 rw [ContinuousMap.norm_le]
 · intro z
   change ‖∫x,f x*g (x⁻¹*z) ∂normalizedCompactHaarMeasure G‖≤_
   let μ:=normalizedCompactHaarMeasure G
   letI : IsProbabilityMeasure μ:=normalizedCompactHaarMeasure_isProbability G
   calc
    ‖∫x,f x*g (x⁻¹*z) ∂μ‖ ≤ (‖f‖*‖g‖)*μ.real Set.univ := by
     apply norm_integral_le_of_norm_le_const
     filter_upwards [] with x
     rw [norm_mul]
     exact mul_le_mul
      (ContinuousMap.norm_coe_le_norm f x)
      (ContinuousMap.norm_coe_le_norm g (x⁻¹*z))
      (norm_nonneg _) (norm_nonneg _)
    _ = _ :=by simp
 · positivity

theorem normalizedCompactHaarContinuousConvolution_add_left (f₁ f₂ g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolution (f₁ + f₂) g =
      normalizedCompactHaarContinuousConvolution f₁ g +
        normalizedCompactHaarContinuousConvolution f₂ g := by
 let μ:=normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ:=normalizedCompactHaarMeasure_isProbability G
 ext z
 change (∫x,(f₁ x+f₂ x)*g (x⁻¹*z) ∂μ)=_
 simp_rw [add_mul]
 have h1:Integrable (fun x=>f₁ x*g (x⁻¹*z)) μ:=by
  have hc:Continuous (fun x=>f₁ x*g (x⁻¹*z)):=by fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
   (μ:=μ) isCompact_univ
 have h2:Integrable (fun x=>f₂ x*g (x⁻¹*z)) μ:=by
  have hc:Continuous (fun x=>f₂ x*g (x⁻¹*z)):=by fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
   (μ:=μ) isCompact_univ
 rw [integral_add h1 h2]
 rfl

theorem normalizedCompactHaarContinuousConvolution_smul_left
    (c : ℂ) (f g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolution (c • f) g =
      c • normalizedCompactHaarContinuousConvolution f g := by
 ext z
 change (∫x,(c*f x)*g (x⁻¹*z) ∂normalizedCompactHaarMeasure G)=c*∫x,f x*g (x⁻¹*z) ∂normalizedCompactHaarMeasure G
 rw [←integral_const_mul]
 apply integral_congr_ae
 filter_upwards [] with x
 ring

theorem normalizedCompactHaarContinuousConvolution_add_right (f g₁ g₂ : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolution f (g₁ + g₂) =
      normalizedCompactHaarContinuousConvolution f g₁ +
        normalizedCompactHaarContinuousConvolution f g₂ := by
 let μ:=normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ:=normalizedCompactHaarMeasure_isProbability G
 ext z
 change (∫x,f x*(g₁ (x⁻¹*z)+g₂ (x⁻¹*z)) ∂μ)=_
 simp_rw [mul_add]
 have h1:Integrable (fun x=>f x*g₁ (x⁻¹*z)) μ:=by
  have hc:Continuous (fun x=>f x*g₁ (x⁻¹*z)):=by fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
   (μ:=μ) isCompact_univ
 have h2:Integrable (fun x=>f x*g₂ (x⁻¹*z)) μ:=by
  have hc:Continuous (fun x=>f x*g₂ (x⁻¹*z)):=by fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
   (μ:=μ) isCompact_univ
 rw [integral_add h1 h2]
 rfl

theorem normalizedCompactHaarContinuousConvolution_smul_right
    (c : ℂ) (f g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolution f (c • g) =
      c • normalizedCompactHaarContinuousConvolution f g := by
 ext z
 change (∫x,f x*(c*g (x⁻¹*z)) ∂normalizedCompactHaarMeasure G)=c*∫x,f x*g (x⁻¹*z) ∂normalizedCompactHaarMeasure G
 rw [←integral_const_mul]
 apply integral_congr_ae
 filter_upwards [] with x
 ring

/-- Convolution by a fixed right input as a bounded linear operator on continuous functions. -/
noncomputable def normalizedCompactHaarContinuousConvolutionRight
    (g : C(G, ℂ)) : C(G, ℂ) →L[ℂ] C(G, ℂ) :=
  ({
    toFun := fun f => normalizedCompactHaarContinuousConvolution f g
    map_add' := fun f h => normalizedCompactHaarContinuousConvolution_add_left f h g
    map_smul' := fun c f => normalizedCompactHaarContinuousConvolution_smul_left c f g
  } : C(G, ℂ) →ₗ[ℂ] C(G, ℂ)).mkContinuous ‖g‖ (by
    intro f
    simpa [mul_comm] using norm_normalizedCompactHaarContinuousConvolution_le f g)

/-- Operator norm of convolution by a fixed right input is bounded by that input's uniform norm. -/
theorem norm_normalizedCompactHaarContinuousConvolutionRight_le
    (g : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolutionRight g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  change ‖normalizedCompactHaarContinuousConvolution f g‖ ≤ ‖g‖ * ‖f‖
  simpa [mul_comm] using norm_normalizedCompactHaarContinuousConvolution_le f g

@[simp]
theorem normalizedCompactHaarContinuousConvolutionRight_apply
    (g f : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolutionRight g f =
      normalizedCompactHaarContinuousConvolution f g :=
  rfl

/-- Convolution by a fixed left input as a bounded linear operator on continuous functions. -/
noncomputable def normalizedCompactHaarContinuousConvolutionLeft
    (f : C(G, ℂ)) : C(G, ℂ) →L[ℂ] C(G, ℂ) :=
  ({
    toFun := fun g => normalizedCompactHaarContinuousConvolution f g
    map_add' := fun g h => normalizedCompactHaarContinuousConvolution_add_right f g h
    map_smul' := fun c g => normalizedCompactHaarContinuousConvolution_smul_right c f g
  } : C(G, ℂ) →ₗ[ℂ] C(G, ℂ)).mkContinuous ‖f‖ (by
    intro g
    exact norm_normalizedCompactHaarContinuousConvolution_le f g)

/-- Operator norm of convolution by a fixed left input is bounded by that input's uniform norm. -/
theorem norm_normalizedCompactHaarContinuousConvolutionLeft_le
    (f : C(G, ℂ)) :
    ‖normalizedCompactHaarContinuousConvolutionLeft f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro g
  change ‖normalizedCompactHaarContinuousConvolution f g‖ ≤ ‖f‖ * ‖g‖
  exact norm_normalizedCompactHaarContinuousConvolution_le f g

@[simp]
theorem normalizedCompactHaarContinuousConvolutionLeft_apply
    (f g : C(G, ℂ)) :
    normalizedCompactHaarContinuousConvolutionLeft f g =
      normalizedCompactHaarContinuousConvolution f g :=
  rfl

end

end Mathematics
end YangMills
