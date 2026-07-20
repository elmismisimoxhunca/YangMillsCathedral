/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvature
import YangMills.Geometry.PrincipalConnectionGaugePullback

/-!
# Gauge pullback of the principal curvature formula

A gauge diffeomorphism pulls smooth fixed-value forms back in every degree and preserves the
Lie-bracket wedge. Pulling back the existing certified derivative carrier and combining it with the
already constructed pulled connection therefore yields a curvature-formula carrier equal to the
pullback of the original curvature.

This is algebraic and smooth pullback naturality of the exact formula. It does not yet construct the
Cartan certificate required for `PrincipalConnectionExteriorDerivativeData` of the transformed
connection. Consequently it is not yet the canonical transformed `curvatureForm`, a local adjoint
transformation law, descended curvature covariance, or gauge invariance of a scalar/action.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Pullback of any smooth fixed-value form by the gauge diffeomorphism. -/
noncomputable def gaugePullbackSmoothForm (k : ℕ)
    (gauge : SmoothGaugeTransformation smoothBundle)
    (form : YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) k) :
    YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) k where
  toForm := form.toForm.pullback gauge gauge.smooth
  smooth := by
    intro s fields hfields
    let invGauge : P → P := gauge.toGauge.toEquiv.symm
    let targetFields : Fin k → (y : P) → TangentSpace IP y := fun i y =>
      mfderiv IP IP gauge (invGauge y) (fields i (invGauge y))
    have hinvSmooth : ContMDiff IP IP ∞ invGauge := gauge.inverse_smooth
    have hinvMaps : Set.MapsTo invGauge (gauge '' s) s := by
      rintro y ⟨x, hx, rfl⟩
      simpa [invGauge] using hx
    have htarget : ∀ i, ContMDiffOn IP (IP.prod (modelWithCornersSelf ℝ EP)) ∞
        (fun y => (⟨y, targetFields i y⟩ : TangentBundle IP P)) (gauge '' s) := by
      intro i
      have hsource : ContMDiffOn IP (IP.prod (modelWithCornersSelf ℝ EP)) ∞
          (fun y => (⟨invGauge y, fields i (invGauge y)⟩ : TangentBundle IP P))
          (gauge '' s) :=
        (hfields i).comp hinvSmooth.contMDiffOn hinvMaps
      have htangent : ContMDiff IP.tangent IP.tangent ∞ (tangentMap IP IP gauge) :=
        gauge.smooth.contMDiff_tangentMap (m := ∞) (by simp)
      have hcomposed := htangent.comp_contMDiffOn hsource
      apply hcomposed.congr
      intro y hy
      apply Bundle.TotalSpace.ext
      · exact (gauge.toGauge.toEquiv.apply_symm_apply y).symm
      · rfl
    have heval := form.eval_smooth (gauge '' s) targetFields htarget
    have hresult := heval.comp gauge.smooth.contMDiffOn (Set.mapsTo_image gauge s)
    apply hresult.congr
    intro x hx
    change (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
        (form.toForm (gauge x)
          (fun i => mfderiv IP IP gauge x (fields i x))) =
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
        (form.toForm (gauge x)
          (fun i => mfderiv IP IP gauge (invGauge (gauge x))
            (fields i (invGauge (gauge x)))))
    rw [show invGauge (gauge x) = x by
      exact gauge.toGauge.toEquiv.symm_apply_apply x]

@[simp] theorem gaugePullbackSmoothForm_toForm (k : ℕ)
    (gauge : SmoothGaugeTransformation smoothBundle)
    (form : YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) k) :
    (gaugePullbackSmoothForm k gauge form).toForm =
      form.toForm.pullback gauge gauge.smooth := rfl

/-- Pullback commutes exactly with the one-form Lie-bracket wedge. -/
theorem gaugePullback_lieBracketWedgeOne [FiniteDimensional ℝ EG]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (first second : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 1) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    YangMills.Mathematics.ManifoldDifferentialForm.pullback
        (V := GroupLieAlgebra IG G) gauge gauge.smooth
        (first.lieBracketWedgeOne second) =
      (YangMills.Mathematics.ManifoldDifferentialForm.pullback
        (V := GroupLieAlgebra IG G) gauge gauge.smooth first).lieBracketWedgeOne
        (YangMills.Mathematics.ManifoldDifferentialForm.pullback
          (V := GroupLieAlgebra IG G) gauge gauge.smooth second) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [YangMills.Mathematics.ManifoldDifferentialForm.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    YangMills.Mathematics.ManifoldDifferentialForm.lieBracketWedgeOne_apply]
  rfl

/-- The exact transformed smooth derivative carrier is the pullback of the supplied derivative. -/
noncomputable def gaugePullbackExteriorDerivativeForm
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) 2 :=
  gaugePullbackSmoothForm 2 gauge exterior.certificate.derivative

/-- Curvature formula assembled from the exact pulled-back derivative and transformed connection. -/
noncomputable def gaugePulledCurvatureForm [FiniteDimensional ℝ EG]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) 2 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact YangMills.Mathematics.SmoothManifoldDifferentialForm.add
    (gaugePullbackExteriorDerivativeForm gauge connection exterior)
    (YangMills.Mathematics.SmoothManifoldDifferentialForm.smul (1 / 2 : ℝ)
      (YangMills.Mathematics.SmoothManifoldDifferentialForm.lieBracketWedgeOne
        (I := IP) (M := P) (V := GroupLieAlgebra IG G)
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
        (gaugePullbackConnection gauge connection).toSmoothForm
        (gaugePullbackConnection gauge connection).toSmoothForm))

/-- The curvature formula assembled from the exact pulled derivative carrier equals the pullback
of the original exact curvature form. This does not supply a transformed Cartan certificate. -/
theorem gaugePulledCurvatureForm_toForm [FiniteDimensional ℝ EG]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (gaugePulledCurvatureForm gauge connection exterior).toForm =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth
        (connection.curvatureForm exterior).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [PrincipalConnectionData.curvatureForm_toForm]
  change YangMills.Mathematics.ManifoldDifferentialForm.pullback
        (V := GroupLieAlgebra IG G) gauge gauge.smooth
      exterior.certificate.derivative.toForm +
      (1 / 2 : ℝ) •
        (gaugePullbackForm gauge connection).lieBracketWedgeOne
          (gaugePullbackForm gauge connection) =
    YangMills.Mathematics.ManifoldDifferentialForm.pullback
      (V := GroupLieAlgebra IG G) gauge gauge.smooth
      (exterior.certificate.derivative.toForm +
        (1 / 2 : ℝ) • connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form)
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [YangMills.Mathematics.ManifoldDifferentialForm.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    YangMills.Mathematics.ManifoldDifferentialForm.lieBracketWedgeOne_apply,
    Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply]
  rfl

/-- Evaluated pullback formula on the exact gauge tangent transports. -/
theorem gaugePulledCurvatureForm_apply [FiniteDimensional ℝ EG]
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (gaugePulledCurvatureForm gauge connection exterior).toForm p v =
      (connection.curvatureForm exterior).toForm (gauge p)
        (fun i => mfderiv IP IP gauge p (v i)) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [gaugePulledCurvatureForm_toForm]
  rfl

end
end YangMills.Geometry
