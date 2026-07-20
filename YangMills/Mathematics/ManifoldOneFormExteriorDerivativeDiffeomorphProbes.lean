/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph

/-!
# Hostile probes for diffeomorphism pullback of Cartan certificates
-/

namespace YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph.Probes

open Set Function
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM' uV uW

noncomputable section

variable
    {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    [IsManifold I ∞ M] [IsManifold I' ∞ M']
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- Every smooth diffeomorphism tangent map is invertible without an accepted inverse witness. -/
theorem exact_tangent_invertibility
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (x : M) :
    (mfderiv I I' e x).IsInvertible :=
  Diffeomorph.isInvertible_mfderiv e x

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- Pulling the exact pushed field back recovers the original dependent tangent field. -/
theorem exact_push_pull_field
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (X : (x : M) → TangentSpace I x) :
    VectorField.mpullback I I' e (Diffeomorph.pushforwardField e X) = X :=
  Diffeomorph.mpullback_pushforwardField e X

/-- Lie-bracket transport uses the exact image set and preserves the ordered bracket. -/
theorem exact_lieBracket_image_transport [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (s : Set M) (x : M)
    (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ManifoldTangentField.IsSmoothOn I s X)
    (hY : ManifoldTangentField.IsSmoothOn I s Y) :
    mfderiv I I' e x (VectorField.mlieBracketWithin I X Y s x) =
      VectorField.mlieBracketWithin I'
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y) (e '' s) (e x) :=
  Diffeomorph.mfderiv_mlieBracketWithin e s x hx hs X Y hX hY

/-- A reversed or wrong-set bracket transport contradicts the exact ordered image theorem. -/
theorem mismatched_lieBracket_transport_blocked [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (s : Set M) (x : M)
    (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ManifoldTangentField.IsSmoothOn I s X)
    (hY : ManifoldTangentField.IsSmoothOn I s Y)
    (wrong : mfderiv I I' e x (VectorField.mlieBracketWithin I X Y s x) ≠
      VectorField.mlieBracketWithin I'
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y) (e '' s) (e x)) : False :=
  wrong (Diffeomorph.mfderiv_mlieBracketWithin e s x hx hs X Y hX hY)

/-- The complete within-set Cartan expression is natural under diffeomorphism pullback. -/
theorem exact_cartan_expression_pullback [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (hpull : pulledForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ManifoldTangentField.IsSmoothOn I s X)
    (hY : ManifoldTangentField.IsSmoothOn I s Y) :
    pulledForm.toForm.oneFormCartanExpressionCoordinates coordinates s x X Y =
      form.toForm.oneFormCartanExpressionCoordinates coordinates (e '' s) (e x)
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y) :=
  oneFormCartanExpressionCoordinates_pullback_diffeomorph
    e coordinates form pulledForm hpull s x hx hs X Y hX hY

/-- A mismatched Cartan transport is inconsistent with exact diffeomorphism naturality. -/
theorem mismatched_cartan_expression_blocked [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (hpull : pulledForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ManifoldTangentField.IsSmoothOn I s X)
    (hY : ManifoldTangentField.IsSmoothOn I s Y)
    (wrong : pulledForm.toForm.oneFormCartanExpressionCoordinates coordinates s x X Y ≠
      form.toForm.oneFormCartanExpressionCoordinates coordinates (e '' s) (e x)
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y)) : False :=
  wrong (oneFormCartanExpressionCoordinates_pullback_diffeomorph
    e coordinates form pulledForm hpull s x hx hs X Y hX hY)

/-- The constructed pullback certificate retains exactly the selected pulled derivative carrier. -/
theorem exact_certificate_derivative [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (hpullForm : pulledForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates 2)
    (hpullDerivative : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff certificate.derivative.toForm) :
    (certificate.pullbackDiffeomorph e coordinates form pulledForm hpullForm
      pulledDerivative hpullDerivative).derivative = pulledDerivative := by
  rfl

end

end YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph.Probes
