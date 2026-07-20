/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureGaugePullbackFormula

/-!
# Hostile probes for gauge pullback of the curvature formula

The probes pin the smooth derivative carrier and bracket-wedge term to exact pullbacks, and reject
an unrelated or malformed formula. They do not produce transformed exterior-derivative data.
-/

namespace YangMills.Geometry.PrincipalCurvatureGaugePullbackFormula.Probes

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
    [FiniteDimensional ℝ EG]

omit [FiniteDimensional ℝ EG] in
/-- Smooth pullback retains exactly the raw manifold-form carrier in every degree. -/
theorem exact_smooth_pullback_carrier (k : ℕ)
    (gauge : SmoothGaugeTransformation smoothBundle)
    (form : YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) k) :
    (gaugePullbackSmoothForm k gauge form).toForm =
      form.toForm.pullback gauge gauge.smooth :=
  gaugePullbackSmoothForm_toForm k gauge form

/-- Gauge pullback preserves the exact orientation of a general one-form bracket wedge. -/
theorem exact_bracket_wedge_pullback
    (gauge : SmoothGaugeTransformation smoothBundle)
    (first second : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 1) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth
        (first.lieBracketWedgeOne second) =
      (YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth first
        ).lieBracketWedgeOne
          (YangMills.Mathematics.ManifoldDifferentialForm.pullback
            gauge gauge.smooth second) :=
  gaugePullback_lieBracketWedgeOne gauge first second

/-- A mismatched or reversed pulled wedge is rejected against the generic exact theorem. -/
theorem mismatched_bracket_wedge_pullback_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (first second : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 1)
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth
          (first.lieBracketWedgeOne second) ≠
        (YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth first
          ).lieBracketWedgeOne
            (YangMills.Mathematics.ManifoldDifferentialForm.pullback
              gauge gauge.smooth second)) : False :=
  wrong (gaugePullback_lieBracketWedgeOne gauge first second)

omit [FiniteDimensional ℝ EG] in
/-- The pulled derivative is tied to the exact derivative of the original certificate. -/
theorem exact_pulled_derivative_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    (gaugePullbackExteriorDerivativeForm gauge connection exterior).toForm =
      exterior.certificate.derivative.toForm.pullback gauge gauge.smooth :=
  gaugePullbackSmoothForm_toForm 2 gauge exterior.certificate.derivative

/-- The assembled formula is exactly the gauge pullback of the same indexed curvature. -/
theorem exact_curvature_formula_pullback
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (gaugePulledCurvatureForm gauge connection exterior).toForm =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth
        (connection.curvatureForm exterior).toForm :=
  gaugePulledCurvatureForm_toForm gauge connection exterior

/-- Evaluation uses both exact tangent vectors transported by the same gauge differential. -/
theorem exact_curvature_formula_evaluation
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
        (fun i => mfderiv IP IP gauge p (v i)) :=
  gaugePulledCurvatureForm_apply gauge connection exterior p v

omit [FiniteDimensional ℝ EG] in
/-- An unrelated transformed derivative carrier contradicts the exact smooth pullback. -/
theorem unrelated_pulled_derivative_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (wrong : (gaugePullbackExteriorDerivativeForm gauge connection exterior).toForm ≠
      exterior.certificate.derivative.toForm.pullback gauge gauge.smooth) : False :=
  wrong (gaugePullbackSmoothForm_toForm 2 gauge exterior.certificate.derivative)

/-- A non-pullback curvature formula is rejected without manufacturing transformed certificate data. -/
theorem malformed_curvature_formula_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (wrong :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      (gaugePulledCurvatureForm gauge connection exterior).toForm ≠
        YangMills.Mathematics.ManifoldDifferentialForm.pullback gauge gauge.smooth
          (connection.curvatureForm exterior).toForm) : False :=
  wrong (gaugePulledCurvatureForm_toForm gauge connection exterior)

end

end YangMills.Geometry.PrincipalCurvatureGaugePullbackFormula.Probes
