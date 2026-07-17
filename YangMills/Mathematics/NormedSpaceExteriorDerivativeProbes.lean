/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedSpaceExteriorDerivative

/-!
# Probes for the normed-space exterior derivative

These probes enforce degree shift, the derivative of a zero-form, vanishing on the zero form,
nilpotence, pullback naturality, and coherence with the pointwise manifold carrier.
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uV

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exterior differentiation raises degree by exactly one. -/
theorem exteriorDerivative_has_next_degree {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) :
    Nonempty (NormedSpaceDifferentialForm E V (k + 1)) :=
  ⟨form.exteriorDerivative⟩

/-- The derivative of a zero-form is its Fréchet derivative in the canonical one-form encoding. -/
theorem zeroForm_exteriorDerivative_eq_fderiv (f : E → V) (x : E) :
    let form : NormedSpaceDifferentialForm E V 0 := fun y =>
      ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y)
    form.exteriorDerivative x =
      (ContinuousAlternatingMap.ofSubsingleton ℝ E V (0 : Fin 1)) (fderiv ℝ f x) := by
  simpa only [NormedSpaceDifferentialForm.exteriorDerivative] using
    extDeriv_constOfIsEmpty f x

/-- Exterior differentiation sends the zero form to zero. -/
theorem exteriorDerivative_zero (k : ℕ) :
    (0 : NormedSpaceDifferentialForm E V k).exteriorDerivative = 0 := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [NormedSpaceDifferentialForm.exteriorDerivative_apply]
  change extDeriv (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] V)) x v = 0
  rw [extDeriv_apply (differentiableAt_const (c := (0 : E [⋀^Fin k]→L[ℝ] V))) v]
  simp

/-- A smooth form cannot have a nonzero second exterior derivative. -/
theorem nonzero_second_exteriorDerivative_blocked {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) (smooth : ContDiff ℝ ∞ form)
    (nonzero : form.exteriorDerivative.exteriorDerivative ≠ 0) : False :=
  nonzero (form.exteriorDerivative_exteriorDerivative smooth)

/-- The bridge to pointwise manifold forms preserves every evaluation. -/
theorem normedSpace_toManifoldForm_coherent {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) (x : E)
    (v : Fin k → TangentSpace 𝓘(ℝ, E) x)
    (mismatch : form.toManifoldForm x v ≠ form x v) : False :=
  mismatch (form.toManifoldForm_apply x v)

/-- The local-model pullback cannot disagree with the pointwise manifold pullback bridge. -/
theorem malformed_normedSpace_manifold_pullback_bridge_blocked
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (form : NormedSpaceDifferentialForm F W k) (f : E → F)
    (smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (mismatch : (form.pullback f).toManifoldForm ≠
      ManifoldDifferentialForm.pullback f smooth form.toManifoldForm) : False :=
  mismatch (form.toManifoldForm_pullback f smooth)

/-- A violation of exterior-derivative pullback naturality is rejected under the stated regularity. -/
theorem malformed_exteriorDerivative_pullback_blocked
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (form : NormedSpaceDifferentialForm F W k) (f : E → F) (x : E)
    (form_smooth : ContDiffAt ℝ ∞ form (f x))
    (f_smooth : ContDiffAt ℝ ∞ f x)
    (mismatch : extDeriv
        (fun y => (form (f y)).compContinuousLinearMap (fderiv ℝ f y)) x ≠
      (form.exteriorDerivative (f x)).compContinuousLinearMap (fderiv ℝ f x)) : False :=
  mismatch (form.exteriorDerivative_pullback f x form_smooth f_smooth)

end YangMills.Mathematics.Probes
