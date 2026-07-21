/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeDiffeomorph

namespace YangMills.Mathematics
open Set Function
open scoped Manifold ContDiff Bundle
universe uE uE' uH uH' uM uM' uV uW
noncomputable section
variable {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
 [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
 {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
 {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
 [ChartedSpace H M] [IsManifold I ∞ M] [ChartedSpace H' M'] [IsManifold I' ∞ M']
 {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
 [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
 {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def SmoothManifoldDifferentialForm.pullbackDiffeomorph
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates k) :
    SmoothManifoldDifferentialForm I M V coordinates k where
  toForm := form.toForm.pullback e e.contMDiff
  smooth := by
    intro s fields hfields
    let targetFields : Fin k → (y : M') → TangentSpace I' y := fun i =>
      Diffeomorph.pushforwardField e (fields i)
    have htarget : ∀ i, ManifoldTangentField.IsSmoothOn I' (e '' s) (targetFields i) :=
      fun i => Diffeomorph.pushforwardField_isSmoothOn e (fields i) (hfields i)
    have heval := form.eval_smooth (e '' s) targetFields htarget
    have hresult := heval.comp e.contMDiff.contMDiffOn (Set.mapsTo_image e s)
    apply hresult.congr
    intro x hx
    change coordinates (form.toForm (e x)
      (fun i => mfderiv I I' e x (fields i x))) =
      coordinates (form.toForm (e x) (fun i => targetFields i (e x)))
    congr 2
    funext i
    unfold targetFields Diffeomorph.pushforwardField
    rw [e.symm_apply_apply x]

@[simp] theorem SmoothManifoldDifferentialForm.pullbackDiffeomorph_toForm
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates k) :
    (form.pullbackDiffeomorph e coordinates k).toForm =
      form.toForm.pullback e e.contMDiff := rfl

end
end YangMills.Mathematics
