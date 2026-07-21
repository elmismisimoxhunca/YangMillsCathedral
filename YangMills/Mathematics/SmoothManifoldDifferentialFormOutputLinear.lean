/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative

namespace YangMills.Mathematics
open Set Function
open scoped Manifold ContDiff

universe uE uH uM uV uW
noncomputable section

variable {E : Type uE} {H : Type uH}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
 {M : Type uM} [TopologicalSpace M]
 {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
 {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
 [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
 {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Output postcomposition of an alternating map. -/
def ContinuousAlternatingMap.postcompContinuousLinearMap
    {A : Type*} [AddCommMonoid A] [Module ℝ A] [TopologicalSpace A] {k : ℕ}
    (L : V →L[ℝ] V) (a : A [⋀^Fin k]→L[ℝ] V) : A [⋀^Fin k]→L[ℝ] V where
  toContinuousMultilinearMap := L.compContinuousMultilinearMap a.toContinuousMultilinearMap
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    simp [a.map_eq_zero_of_eq v hij hne]

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
@[simp] theorem ContinuousAlternatingMap.postcompContinuousLinearMap_apply
    {A : Type*} [AddCommMonoid A] [Module ℝ A] [TopologicalSpace A] {k : ℕ}
    (L : V →L[ℝ] V) (a : A [⋀^Fin k]→L[ℝ] V) (v : Fin k → A) :
    ContinuousAlternatingMap.postcompContinuousLinearMap L a v = L (a v) := rfl

/-- Output postcomposition of a manifold form. -/
def ManifoldDifferentialForm.postcompContinuousLinearMap (L : V →L[ℝ] V) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) : ManifoldDifferentialForm I M V k :=
  fun x => ContinuousAlternatingMap.postcompContinuousLinearMap L (form x)

omit [IsManifold I ∞ M] in
@[simp] theorem ManifoldDifferentialForm.postcompContinuousLinearMap_apply
    (L : V →L[ℝ] V) (k : ℕ) (form : ManifoldDifferentialForm I M V k)
    (x : M) (v : Fin k → TangentSpace I x) :
    form.postcompContinuousLinearMap L k x v = L (form x v) := rfl

/-- Smooth output postcomposition. -/
def SmoothManifoldDifferentialForm.postcompContinuousLinearMap
    (coordinates : V ≃L[ℝ] W) (L : V →L[ℝ] V) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k) :
    SmoothManifoldDifferentialForm I M V coordinates k where
  toForm := form.toForm.postcompContinuousLinearMap L k
  smooth := by
    intro s fields hfields
    let Lc : W →L[ℝ] W := coordinates.toContinuousLinearMap.comp
      (L.comp coordinates.symm.toContinuousLinearMap)
    have h := Lc.contMDiff.comp_contMDiffOn (form.eval_smooth s fields hfields)
    simpa [Lc, Function.comp_def] using h

end
end YangMills.Mathematics

namespace YangMills.Mathematics
open Set Function
open scoped Manifold ContDiff

universe uE uH uM uV uW
noncomputable section
variable {E : Type uE} {H : Type uH}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
 {M : Type uM} [TopologicalSpace M]
 {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
 {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
 [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
 {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.postcompContinuousLinearMap
    (coordinates : V ≃L[ℝ] W) (L : V →L[ℝ] V) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form) :
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n
      (form.postcompContinuousLinearMap coordinates L (n + 1)) where
  derivative := certificate.derivative.postcompContinuousLinearMap coordinates L (n + 2)
  cartan_formula := by
    intro s x hs hx hu fields hfields
    let Lc : W →L[ℝ] W := coordinates.toContinuousLinearMap.comp
      (L.comp coordinates.symm.toContinuousLinearMap)
    have hcartan := certificate.cartan_formula s x hs hx hu fields hfields
    have hcoeff (i : Fin (n + 2)) :
        (fun y => coordinates
          ((form.postcompContinuousLinearMap coordinates L (n + 1)).toForm y
            (i.removeNth (fun k => fields k y)))) =
        Lc ∘ (fun y => coordinates (form.toForm y
          (i.removeNth (fun k => fields k y)))) := by
      funext y
      simp [SmoothManifoldDifferentialForm.postcompContinuousLinearMap,
        ManifoldDifferentialForm.postcompContinuousLinearMap, Lc]
    have hdiff (i : Fin (n + 2)) :
        (NormedSpace.fromTangentSpace
          (coordinates ((form.postcompContinuousLinearMap coordinates L (n + 1)).toForm x
            (i.removeNth (fun k => fields k x)))))
          (mfderivWithin I (modelWithCornersSelf ℝ W)
            (fun y => coordinates
              ((form.postcompContinuousLinearMap coordinates L (n + 1)).toForm y
                (i.removeNth (fun k => fields k y)))) s x (fields i x)) =
        Lc ((NormedSpace.fromTangentSpace
          (coordinates (form.toForm x (i.removeNth (fun k => fields k x)))))
          (mfderivWithin I (modelWithCornersSelf ℝ W)
            (fun y => coordinates (form.toForm y
              (i.removeNth (fun k => fields k y)))) s x (fields i x))) := by
      rw [hcoeff]
      let f : M → W := fun y => coordinates (form.toForm y
        (i.removeNth (fun k => fields k y)))
      have hf : MDifferentiableWithinAt I (modelWithCornersSelf ℝ W) f s x :=
        ((form.eval_smooth s (fun k => fields (i.succAbove k))
          (fun k => hfields (i.succAbove k))) x hx).mdifferentiableWithinAt (by simp)
      have chain := mfderivWithin_comp (I := I) (I' := modelWithCornersSelf ℝ W)
        (I'' := modelWithCornersSelf ℝ W) (f := f) (g := Lc) x
        (Lc.contMDiff.mdifferentiableAt (n := ∞) (by simp)) hf (by simp) (hu x hx)
      rw [mfderivWithin_eq_fderivWithin, Lc.fderivWithin uniqueDiffWithinAt_univ] at chain
      change (NormedSpace.fromTangentSpace (Lc (f x)))
          (mfderivWithin I (modelWithCornersSelf ℝ W) (Lc ∘ f) s x (fields i x)) = _
      rw [chain]
      simp only [mfld_simps]
      rfl
    dsimp [SmoothManifoldDifferentialForm.postcompContinuousLinearMap,
      ManifoldDifferentialForm.postcompContinuousLinearMap,
      ContinuousAlternatingMap.postcompContinuousLinearMap]
    change coordinates (L (certificate.derivative.toForm x (fun i => fields i x))) = _
    rw [show coordinates (L (certificate.derivative.toForm x (fun i => fields i x))) =
      Lc (coordinates (certificate.derivative.toForm x (fun i => fields i x))) by simp [Lc]]
    rw [hcartan]
    unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
    rw [map_sub, map_sum, map_sum]
    simp only [map_zsmul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (hdiff i).symm
    · apply Finset.sum_congr rfl
      intro i hi
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [ManifoldDifferentialForm.postcompContinuousLinearMap, Lc]

end
end YangMills.Mathematics
