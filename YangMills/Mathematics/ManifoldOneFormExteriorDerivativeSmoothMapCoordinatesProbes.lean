/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates

/-!
# Hostile probes for centered smooth-map exterior calculus
-/

namespace YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates.Probes

open Set Function
open scoped Manifold ContDiff

universe uE uH uM uV uW uE' uH' uM'

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

/-- A manifold certificate is exactly Mathlib's centered-chart `extDerivWithin`. -/
theorem exact_certificate_centered_extDeriv
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (p : M) :
    certificate.derivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates 1 p)
        (extChartAt I p).target ((extChartAt I p) p) :=
  certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates form p

variable
    {E' : Type uE'} {H' : Type uH'}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {M' : Type uM'} [TopologicalSpace M']
    {I' : ModelWithCorners ℝ E' H'} [ChartedSpace H' M'] [IsManifold I' ∞ M']

omit [FiniteDimensional ℝ E] in
/-- Mathlib pullback naturality applies to the written representative of every smooth manifold map
on the exact chart-safe set. -/
theorem exact_centered_smoothMap_pullback
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (p : M) :
    let g : E → E' := writtenInExtChartAt I I' p f
    let s : Set E := (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
    let t : Set E' := (extChartAt I' (f p)).target
    extDerivWithin
        (fun x => ((form.toForm.inExtChartAt coordinates 1 (f p)) (g x)).compContinuousLinearMap
          (fderivWithin ℝ g s x)) s ((extChartAt I p) p) =
      (extDerivWithin (form.toForm.inExtChartAt coordinates 1 (f p)) t
          (g ((extChartAt I p) p))).compContinuousLinearMap
        (fderivWithin ℝ g s ((extChartAt I p) p)) :=
  centeredChart_extDerivWithin_pullback f hf coordinates form p

omit [FiniteDimensional ℝ E] in
/-- A changed arbitrary-map centered pullback expression contradicts exact Mathlib naturality. -/
theorem mismatched_centered_smoothMap_pullback_blocked
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (p : M)
    (wrong :
      let g : E → E' := writtenInExtChartAt I I' p f
      let s : Set E := (extChartAt I p).target ∩
        (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source
      let t : Set E' := (extChartAt I' (f p)).target
      extDerivWithin
          (fun x => ((form.toForm.inExtChartAt coordinates 1 (f p)) (g x)).compContinuousLinearMap
            (fderivWithin ℝ g s x)) s ((extChartAt I p) p) ≠
        (extDerivWithin (form.toForm.inExtChartAt coordinates 1 (f p)) t
            (g ((extChartAt I p) p))).compContinuousLinearMap
          (fderivWithin ℝ g s ((extChartAt I p) p))) : False :=
  wrong (centeredChart_extDerivWithin_pullback f hf coordinates form p)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- A changed raw-pullback carrier on the exact chart-safe set is rejected. -/
theorem mismatched_raw_pullback_carrier_blocked
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I' M' V k) (p : M)
    (x : E)
    (hx : x ∈ (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source)
    (wrong :
      (ManifoldDifferentialForm.pullback f hf form).inExtChartAt coordinates k p x ≠
        ((form.inExtChartAt coordinates k (f p)) (writtenInExtChartAt I I' p f x)).compContinuousLinearMap
            (fderivWithin ℝ (writtenInExtChartAt I I' p f)
              ((extChartAt I p).target ∩
                (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source) x)) : False :=
  wrong (pullback_inExtChartAt_eqOn f hf coordinates k form p hx)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The arbitrary Cartan-calculus set cannot fail to agree locally with the chart-safe set. -/
theorem mismatched_chartSafe_locality_blocked
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (s : Set M) (p : M) (open_s : IsOpen s) (mem_s : p ∈ s)
    (wrong : ¬ ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I : Set E) =ᶠ[
        nhds ((extChartAt I p) p)]
      ((extChartAt I p).target ∩
        (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt I' (f p)).source : Set E)) : False :=
  wrong (centered_calculusSet_eventuallyEq_chartSafe f hf s p open_s mem_s)

/-- Exact smooth pullback carriers determine a genuine all-fields Cartan certificate; no
naturality proposition is accepted from the caller. -/
noncomputable def exact_smoothMap_certificate_constructor
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates 1)
    (pulledForm_eq : pulledForm.toForm =
      ManifoldDifferentialForm.pullback f hf form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates 2)
    (pulledDerivative_eq : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm) :
    SmoothManifoldOneFormExteriorDerivativeCertificate coordinates pulledForm :=
  certificate.pullbackSmoothMapOfForms f hf coordinates form pulledForm pulledForm_eq
    pulledDerivative pulledDerivative_eq

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- A derivative carrier different from the exact raw pullback cannot enter the constructor. -/
theorem mismatched_pulledDerivative_blocked
    (f : M → M') (hf : ContMDiff I I' ∞ f)
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates 2)
    (pulledDerivative_eq : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm)
    (wrong : pulledDerivative.toForm ≠
      ManifoldDifferentialForm.pullback f hf certificate.derivative.toForm) : False :=
  wrong pulledDerivative_eq

/-- A substituted centered derivative contradicts the supplied certificate. -/
theorem mismatched_certificate_centered_extDeriv_blocked
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (p : M)
    (wrong :
      certificate.derivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p) ≠
        extDerivWithin (form.toForm.inExtChartAt coordinates 1 p)
          (extChartAt I p).target ((extChartAt I p) p)) : False :=
  wrong (certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates form p)

end YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates.Probes
