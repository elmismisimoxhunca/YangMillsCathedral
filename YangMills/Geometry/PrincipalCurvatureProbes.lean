/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvature

/-!
# Hostile probes for principal curvature

These probes ensure that curvature is smooth, remains tied to the same principal connection and its
certified exterior derivative, uses the exact factor one-half, and is genuinely alternating.
-/

namespace YangMills.Geometry.Probes

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)] [TopologicalSpace HG]
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
    {connection : PrincipalConnectionData smoothBundle}

omit [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Exterior-derivative data cannot be disconnected from this connection's exact smooth form. -/
theorem exteriorDerivativeData_derivative_smooth
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    exterior.certificate.derivative.toForm.IsSmooth
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) :=
  exterior.certificate.derivative.smooth

omit [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- A derived principal curvature cannot fail smoothness. -/
theorem nonsmooth_principalCurvature_blocked
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (nonsmooth : ¬(connection.curvatureForm exterior).toForm.IsSmooth
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)) : False :=
  nonsmooth (connection.curvatureForm exterior).smooth

/-- The curvature form cannot differ from Freed's exact `dΘ + 1/2 [Θ ∧ Θ]` equation. -/
theorem malformed_principalCurvature_formula_blocked
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (mismatch : (connection.curvatureForm exterior).toForm ≠
      exterior.certificate.derivative.toForm +
        (1 / 2 : ℝ) •
          connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form) : False :=
  mismatch (connection.curvatureForm_toForm exterior)

omit [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Pointwise evaluation cannot lose the bracket term or retain an erroneous factor two. -/
theorem malformed_principalCurvature_evaluation_blocked
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (v : Fin 2 → TangentSpace IP p)
    (mismatch : (connection.curvatureForm exterior).toForm p v ≠
      exterior.certificate.derivative.toForm p v +
        ⁅connection.pointwise.form p (fun _ => v 0),
          connection.pointwise.form p (fun _ => v 1)⁆) : False :=
  mismatch (connection.curvatureForm_apply exterior p v)

omit [CompleteSpace EG] [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The derived curvature is a genuine alternating two-form. -/
theorem nonalternating_principalCurvature_blocked
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (v : TangentSpace IP p)
    (nonzero : (connection.curvatureForm exterior).toForm p (fun _ => v) ≠ 0) : False :=
  nonzero ((connection.curvatureForm exterior).toForm.evalTwo_same p v)

end

end YangMills.Geometry.Probes
