/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeDiffeomorph

/-!
# Positive-degree exterior certificates under diffeomorphisms

The full positive-degree Cartan expression is transported through a smooth diffeomorphism in every
arity, on the exact image of the source calculus set. Consequently an exact pulled form and exact
pulled derivative package into a derived pulled exterior certificate without accepting another
naturality witness.
-/

namespace YangMills.Mathematics

open Set Function
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM' uV uW

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

noncomputable section

lemma positiveDegreeCartanExpressionCoordinates_pullback_diffeomorph
    [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpull : pulledForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (fields : Fin (n + 2) → (x : M) → TangentSpace I x)
    (hfields : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    pulledForm.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s x fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n (e '' s) (e x)
        (fun i => Diffeomorph.pushforwardField e (fields i)) := by
  let pushed : Fin (n + 2) → (y : M') → TangentSpace I' y :=
    fun i => Diffeomorph.pushforwardField e (fields i)
  have hpushed : ∀ i, ManifoldTangentField.IsSmoothOn I' (e '' s) (pushed i) :=
    fun i => Diffeomorph.pushforwardField_isSmoothOn e (fields i) (hfields i)
  let g : Fin (n + 2) → M' → W := fun i y =>
    coordinates (form.toForm y (i.removeNth (fun k => pushed k y)))
  have hg_smooth (i : Fin (n + 2)) :
      ContMDiffOn I' (modelWithCornersSelf ℝ W) ∞ (g i) (e '' s) := by
    apply form.eval_smooth (e '' s) (fun k => pushed (i.succAbove k))
    intro k
    exact hpushed (i.succAbove k)
  have hmem : e x ∈ e '' s := ⟨x, hx, rfl⟩
  have hg (i : Fin (n + 2)) :
      MDifferentiableWithinAt I' (modelWithCornersSelf ℝ W)
        (g i) (e '' s) (e x) :=
    ((hg_smooth i) (e x) hmem).mdifferentiableWithinAt (by simp)
  have eval (i : Fin (n + 2)) (z : M) :
      coordinates (pulledForm.toForm z (i.removeNth (fun k => fields k z))) =
        g i (e z) := by
    rw [hpull]
    unfold ManifoldDifferentialForm.pullback g
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have tuplePush :
        (mfderiv I I' e z ∘ i.removeNth (fun k => fields k z)) =
          i.removeNth (fun k => pushed k (e z)) := by
      funext k
      unfold pushed Diffeomorph.pushforwardField
      rw [e.symm_apply_apply z]
      rfl
    rw [tuplePush]
  have eval_fun (i : Fin (n + 2)) :
      (fun z => coordinates (pulledForm.toForm z
        (i.removeNth (fun k => fields k z)))) = g i ∘ e := by
    funext z
    exact eval i z
  have derivative_transport (i : Fin (n + 2)) :
      (NormedSpace.fromTangentSpace (g i (e x)))
          (mfderivWithin I (modelWithCornersSelf ℝ W) (g i ∘ e) s x (fields i x)) =
        (NormedSpace.fromTangentSpace (g i (e x)))
          (mfderivWithin I' (modelWithCornersSelf ℝ W) (g i) (e '' s) (e x)
            (pushed i (e x))) := by
    exact congrArg (NormedSpace.fromTangentSpace (g i (e x)))
      (Diffeomorph.mfderivWithin_comp_apply_pushforward
        e (g i) s x hx hs (hg i) (fields i))
  have first_term (i : Fin (n + 2)) :
      (-1 : ℤ) ^ (i : ℕ) •
          (NormedSpace.fromTangentSpace
            (coordinates (pulledForm.toForm x (i.removeNth (fun k => fields k x)))))
            (mfderivWithin I (modelWithCornersSelf ℝ W)
              (fun y => coordinates (pulledForm.toForm y
                (i.removeNth (fun k => fields k y)))) s x (fields i x)) =
        (-1 : ℤ) ^ (i : ℕ) •
          (NormedSpace.fromTangentSpace
            (coordinates (form.toForm (e x) (i.removeNth (fun k => pushed k (e x))))))
            (mfderivWithin I' (modelWithCornersSelf ℝ W)
              (fun y => coordinates (form.toForm y
                (i.removeNth (fun k => pushed k y))))
              (e '' s) (e x) (pushed i (e x))) := by
    rw [eval i x, eval_fun i]
    exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (derivative_transport i)
  have bracket_term (i : Fin (n + 1)) (j : Fin (n + 1)) :
      coordinates (pulledForm.toForm x (Matrix.vecCons
          (VectorField.mlieBracketWithin I
            (fields i.castSucc) (fields j.succ) s x)
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k x)))) =
        coordinates (form.toForm (e x) (Matrix.vecCons
          (VectorField.mlieBracketWithin I'
            (pushed i.castSucc) (pushed j.succ) (e '' s) (e x))
          (j.removeNth <| i.castSucc.removeNth (fun k => pushed k (e x))))) := by
    have bracket := Diffeomorph.mfderiv_mlieBracketWithin e s x hx hs
      (fields i.castSucc) (fields j.succ) (hfields i.castSucc) (hfields j.succ)
    rw [hpull]
    simp only [ManifoldDifferentialForm.pullback,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 2
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · exact bracket
    · unfold pushed Diffeomorph.pushforwardField
      rw [e.symm_apply_apply x]
      rfl
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
  change
    (∑ i : Fin (n + 2), _) - ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, _ =
      (∑ i : Fin (n + 2), _) - ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact first_term i
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg ((-1 : ℤ) ^ (i + j : ℕ) • ·) (bracket_term i j)

noncomputable def SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.pullbackDiffeomorph
    [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I' M' V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      coordinates n form)
    (pulledForm : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hpullForm : pulledForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (pulledDerivative : SmoothManifoldDifferentialForm I M V coordinates (n + 2))
    (hpullDerivative : pulledDerivative.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff certificate.derivative.toForm) :
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n pulledForm where
  derivative := pulledDerivative
  cartan_formula := by
    intro s x open_s mem_s unique_s fields fields_smooth
    let pushed : Fin (n + 2) → (y : M') → TangentSpace I' y :=
      fun i => Diffeomorph.pushforwardField e (fields i)
    have pushed_smooth : ∀ i,
        ManifoldTangentField.IsSmoothOn I' (e '' s) (pushed i) :=
      fun i => Diffeomorph.pushforwardField_isSmoothOn e (fields i) (fields_smooth i)
    have open_image : IsOpen (e '' s) := e.toHomeomorph.isOpen_image.mpr open_s
    have mem_image : e x ∈ e '' s := ⟨x, mem_s, rfl⟩
    have unique_image : UniqueMDiffOn I' (e '' s) :=
      (e.uniqueMDiffOn_image (by simp)).mpr unique_s
    have tuplePush :
        (mfderiv I I' e x ∘ fun i => fields i x) = fun i => pushed i (e x) := by
      funext i
      unfold pushed Diffeomorph.pushforwardField
      rw [e.symm_apply_apply x]
      rfl
    calc
      coordinates (pulledDerivative.toForm x (fun i => fields i x)) =
          coordinates (certificate.derivative.toForm (e x) (fun i => pushed i (e x))) := by
        rw [hpullDerivative]
        change coordinates (certificate.derivative.toForm (e x)
          (mfderiv I I' e x ∘ fun i => fields i x)) = _
        rw [tuplePush]
      _ = form.toForm.positiveDegreeCartanExpressionCoordinates
          coordinates n (e '' s) (e x) pushed :=
        certificate.cartan_formula (e '' s) (e x) open_image mem_image unique_image
          pushed pushed_smooth
      _ = pulledForm.toForm.positiveDegreeCartanExpressionCoordinates
          coordinates n s x fields :=
        (positiveDegreeCartanExpressionCoordinates_pullback_diffeomorph
          e coordinates n form pulledForm hpullForm s x mem_s unique_s
          fields fields_smooth).symm

end

end YangMills.Mathematics
