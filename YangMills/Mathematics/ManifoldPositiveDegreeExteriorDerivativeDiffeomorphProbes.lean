/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeDiffeomorph

/-!
# Hostile probes for positive-degree diffeomorphism naturality
-/

namespace YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeDiffeomorph.Probes

open Set Function
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM' uV uW

variable
    {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M'] [IsManifold I ∞ M] [IsManifold I' ∞ M']
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable section

/-- The complete arbitrary-degree Cartan expression transports to the exact image set. -/
theorem exact_positive_degree_expression_transport
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpull : pulledForm.toForm = ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (x : M) → TangentSpace I x)
    (hfields : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    pulledForm.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n (e '' s) (e x)
        (fun i => Diffeomorph.pushforwardField e (fields i)) :=
  positiveDegreeCartanExpressionCoordinates_pullback_diffeomorph
    e coordinates n form pulledForm hpull s x hx hs fields hfields

/-- Exact pulled carriers construct the pulled positive-degree certificate. -/
noncomputable def exact_pulled_certificate
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpullForm : pulledForm.toForm = ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates (n + 2))
    (hpullDerivative : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff certificate.derivative.toForm) :
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n pulledForm :=
  certificate.pullbackDiffeomorph e coordinates n form pulledForm hpullForm
    pulledDerivative hpullDerivative

/-- The constructed certificate retains the exact supplied pulled derivative carrier. -/
theorem exact_pulled_certificate_derivative
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpullForm : pulledForm.toForm = ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates (n + 2))
    (hpullDerivative : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff certificate.derivative.toForm) :
    (certificate.pullbackDiffeomorph e coordinates n form pulledForm hpullForm
      pulledDerivative hpullDerivative).derivative = pulledDerivative :=
  rfl

/-- The `2 → 3` endpoint uses the same arbitrary-degree transport theorem. -/
theorem exact_two_to_three_expression_transport
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 2)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 2)
    (hpull : pulledForm.toForm = ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (fields : Fin 3 → (x : M) → TangentSpace I x)
    (hfields : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    pulledForm.toForm.positiveDegreeCartanExpressionCoordinates coordinates 1 s x fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates 1 (e '' s) (e x)
        (fun i => Diffeomorph.pushforwardField e (fields i)) :=
  positiveDegreeCartanExpressionCoordinates_pullback_diffeomorph
    e coordinates 1 form pulledForm hpull s x hx hs fields hfields

/-- A changed transported Cartan expression contradicts exact naturality. -/
theorem mismatched_positive_degree_transport_blocked
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpull : pulledForm.toForm = ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (x : M) → TangentSpace I x)
    (hfields : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (wrong : pulledForm.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields ≠
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n (e '' s) (e x)
        (fun i => Diffeomorph.pushforwardField e (fields i))) : False :=
  wrong (positiveDegreeCartanExpressionCoordinates_pullback_diffeomorph
    e coordinates n form pulledForm hpull s x hx hs fields hfields)

end

end YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeDiffeomorph.Probes
