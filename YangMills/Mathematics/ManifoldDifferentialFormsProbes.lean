/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldDifferentialForms

/-!
# Hostile probes for pointwise manifold differential forms

These probes enforce degree typing, alternating two-form behavior, and degree-preserving pullback.
They do not claim a smooth-section or exterior-derivative API.
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uM uE' uH' uM' uV

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {E' : Type uE'} {H' : Type uH'}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M' : Type uM'} [TopologicalSpace M']
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Every degree has a concrete zero pointwise form. -/
theorem zero_differentialForm_exists
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] (k : ℕ) :
    Nonempty (ManifoldDifferentialForm I M V k) :=
  ⟨0⟩

/-- One-form evaluation is additive in its tangent-vector argument. -/
theorem oneForm_eval_add
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    (form : ManifoldDifferentialForm I M V 1) (x : M)
    (v w : TangentSpace I x) :
    form.evalOne x (v + w) = form.evalOne x v + form.evalOne x w := by
  unfold ManifoldDifferentialForm.evalOne
  have hsum : (fun _ : Fin 1 => v + w) =
      Function.update (fun _ : Fin 1 => 0) 0 (v + w) := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  have hv : (fun _ : Fin 1 => v) = Function.update (fun _ : Fin 1 => 0) 0 v := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  have hw : (fun _ : Fin 1 => w) = Function.update (fun _ : Fin 1 => 0) 0 w := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  rw [hsum, hv, hw]
  exact (form x).map_update_add (fun _ : Fin 1 => 0) 0 v w

/-- A purported alternating two-form cannot be nonzero on two identical arguments. -/
theorem nonalternating_twoForm_blocked
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    (form : ManifoldDifferentialForm I M V 2) (x : M) (v : TangentSpace I x)
    (nonzero : form x (fun _ => v) ≠ 0) : False :=
  nonzero (form.evalTwo_same x v)

/-- Pullback preserves form degree in its result type. -/
noncomputable def pullback_preserves_degree
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    (f : M → M') (smooth : ContMDiff I I' ∞ f) (k : ℕ)
    (form : ManifoldDifferentialForm I' M' V k) :
    ManifoldDifferentialForm I M V k :=
  form.pullback f smooth

/-- A zero form cannot acquire a nonzero pullback merely by changing manifolds. -/
theorem nonzero_pullback_of_zero_blocked
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    (f : M → M') (smooth : ContMDiff I I' ∞ f) (k : ℕ)
    (nonzero : ManifoldDifferentialForm.pullback f smooth
      (0 : ManifoldDifferentialForm I' M' V k) ≠ 0) : False :=
  nonzero (ManifoldDifferentialForm.pullback_zero f smooth k)

end YangMills.Mathematics.Probes
