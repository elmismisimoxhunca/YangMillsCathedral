/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialForms
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Exterior derivative on normed vector spaces

This module packages Mathlib's Fréchet-derivative construction as the local-model exterior
derivative needed for later manifold work. It also gives the definitionally coherent bridge from a
normed-space differential form to this project's pointwise manifold form carrier.

This is deliberately not yet a global exterior derivative on arbitrary manifolds.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff

universe uE uV

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A differential `k`-form on a real normed vector space, in Mathlib's native representation. -/
abbrev NormedSpaceDifferentialForm (E : Type uE)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :=
  E → E [⋀^Fin k]→L[ℝ] V

/-- View a normed-space form as the same evaluation family in the pointwise manifold carrier. -/
def NormedSpaceDifferentialForm.toManifoldForm {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) :
    ManifoldDifferentialForm 𝓘(ℝ, E) E V k :=
  form

/-- Pull back a normed-space differential form using the Fréchet derivative. -/
noncomputable def NormedSpaceDifferentialForm.pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (form : NormedSpaceDifferentialForm F W k) (f : E → F) :
    NormedSpaceDifferentialForm E W k :=
  fun x => (form (f x)).compContinuousLinearMap (fderiv ℝ f x)

/-- The normed-space and pointwise-manifold pullback constructions agree exactly. -/
theorem NormedSpaceDifferentialForm.toManifoldForm_pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (f : E → F) (smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (form : NormedSpaceDifferentialForm F W k) :
    (form.pullback f).toManifoldForm =
      ManifoldDifferentialForm.pullback f smooth form.toManifoldForm := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [NormedSpaceDifferentialForm.pullback,
    NormedSpaceDifferentialForm.toManifoldForm,
    ManifoldDifferentialForm.pullback, mfderiv_eq_fderiv]
  rfl

/-- Exterior derivative on a normed vector space, delegated to Mathlib's `extDeriv`. -/
noncomputable def NormedSpaceDifferentialForm.exteriorDerivative {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) :
    NormedSpaceDifferentialForm E V (k + 1) :=
  extDeriv form

@[simp]
theorem NormedSpaceDifferentialForm.exteriorDerivative_apply {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) (x : E) :
    form.exteriorDerivative x = extDeriv form x :=
  rfl

/-- The manifold bridge does not alter any pointwise coefficient or tangent input. -/
@[simp]
theorem NormedSpaceDifferentialForm.toManifoldForm_apply {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) (x : E) (v : Fin k → TangentSpace 𝓘(ℝ, E) x) :
    form.toManifoldForm x v = form x v :=
  rfl

/-- The exterior derivative squares to zero for a sufficiently smooth normed-space form. -/
theorem NormedSpaceDifferentialForm.exteriorDerivative_exteriorDerivative {k : ℕ}
    (form : NormedSpaceDifferentialForm E V k) (smooth : ContDiff ℝ ∞ form) :
    form.exteriorDerivative.exteriorDerivative = 0 := by
  apply extDeriv_extDeriv smooth
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

/-- Exterior differentiation is natural under a sufficiently smooth pullback between normed spaces. -/
theorem NormedSpaceDifferentialForm.exteriorDerivative_pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} (form : NormedSpaceDifferentialForm F W k) (f : E → F) (x : E)
    (form_smooth : ContDiffAt ℝ ∞ form (f x))
    (f_smooth : ContDiffAt ℝ ∞ f x) :
    extDeriv (fun y => (form (f y)).compContinuousLinearMap (fderiv ℝ f y)) x =
      (form.exteriorDerivative (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  apply extDeriv_pullback (r := ∞) (form_smooth.differentiableAt (by simp)) f_smooth
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

end YangMills.Mathematics
