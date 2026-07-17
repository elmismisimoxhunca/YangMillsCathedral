/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialForms
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Hostile probes for smooth manifold differential forms

These probes ensure that smoothness is tested locally against smooth tangent-vector fields and that
zero forms provide positive consistency evidence.
-/

namespace YangMills.Mathematics.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW uW₂

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {W₂ : Type uW₂} [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {valueCoordinates : V ≃L[ℝ] W} {k : ℕ}

/-- A claimed smooth form cannot fail smoothness on one locally smooth tuple of fields. -/
theorem nonsmooth_form_evaluation_blocked
    (form : SmoothManifoldDifferentialForm I M V valueCoordinates k)
    (s : Set M) (fields : Fin k → (x : M) → TangentSpace I x)
    (fields_smooth : ∀ i, ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun x => (⟨x, fields i x⟩ : TangentBundle I M)) s)
    (nonsmooth : ¬ContMDiffOn I (modelWithCornersSelf ℝ W) ∞
      (fun x => valueCoordinates (form.toForm x (fun i => fields i x))) s) : False :=
  nonsmooth (form.eval_smooth s fields fields_smooth)

/-- Changing continuously linearly equivalent value coordinates cannot change smoothness. -/
theorem coordinate_choice_cannot_change_smoothness
    (firstCoordinates : V ≃L[ℝ] W) (secondCoordinates : V ≃L[ℝ] W₂)
    (form : ManifoldDifferentialForm I M V k) :
    form.IsSmooth firstCoordinates ↔ form.IsSmooth secondCoordinates :=
  form.isSmooth_iff_valueCoordinates firstCoordinates secondCoordinates

/-- The absolute-value function, encoded as a degree-zero pointwise form on `ℝ`. -/
noncomputable def absoluteValueZeroForm :
    ManifoldDifferentialForm 𝓘(ℝ, ℝ) ℝ ℝ 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ ℝ (Fin 0) |x|

/-- The smoothness criterion concretely rejects the nonsmooth absolute-value zero-form. -/
theorem absoluteValueZeroForm_not_smooth :
    ¬absoluteValueZeroForm.IsSmooth (ContinuousLinearEquiv.refl ℝ ℝ) := by
  intro smooth
  let fields : Fin 0 → (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun i => Fin.elim0 i
  have fields_smooth : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod (modelWithCornersSelf ℝ ℝ)) ∞
      (fun x => (⟨x, fields i x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) Set.univ :=
    fun i => Fin.elim0 i
  have evaluated := smooth Set.univ fields fields_smooth
  have evaluation_eq : (fun x => (ContinuousLinearEquiv.refl ℝ ℝ)
      (absoluteValueZeroForm x (fun i => fields i x))) = (abs : ℝ → ℝ) := by
    funext x
    rfl
  have smooth_abs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (abs : ℝ → ℝ) := by
    rw [← contMDiffOn_univ, ← evaluation_eq]
    exact evaluated
  exact not_differentiableAt_abs_zero (smooth_abs.contDiff.differentiable (by simp) 0)

/-- Every degree has a concrete smooth zero form. -/
theorem zero_smoothDifferentialForm_exists
    (valueCoordinates : V ≃L[ℝ] W) (k : ℕ) :
    Nonempty (SmoothManifoldDifferentialForm I M V valueCoordinates k) :=
  ⟨SmoothManifoldDifferentialForm.zero valueCoordinates k⟩

/-- The bundled zero smooth form has the pointwise zero form underneath. -/
theorem zero_smoothDifferentialForm_toForm
    (valueCoordinates : V ≃L[ℝ] W) (k : ℕ) :
    (SmoothManifoldDifferentialForm.zero
      (I := I) (M := M) (V := V) valueCoordinates k).toForm = 0 :=
  rfl

end YangMills.Mathematics.Probes
