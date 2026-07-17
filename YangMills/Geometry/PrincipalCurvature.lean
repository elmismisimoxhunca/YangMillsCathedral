/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PointwisePrincipalConnection
import YangMills.Mathematics.LieGroupSmoothBracket
import YangMills.Mathematics.ManifoldOneFormExteriorDerivative
import YangMills.Mathematics.SmoothLieBracketWedge
import YangMills.Mathematics.SmoothManifoldDifferentialFormOperations

/-!
# Principal-connection curvature

Given a smooth principal connection whose one-form has a certified manifold exterior derivative,
this module derives its smooth curvature form using Freed's equation (1.13):

`Ω = dΘ + 1/2 [Θ ∧ Θ]`.

The curvature is a definition from the same connection and certificate, never an unrelated witness.
No principal connection or curvature is constructed here.
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

/-- Exterior-derivative data tied to the exact smooth one-form of one principal connection. -/
structure PrincipalConnectionExteriorDerivativeData
    (connection : PrincipalConnectionData smoothBundle) where
  /-- Certified `dΘ` for this connection's unchanged smooth form. -/
  certificate :
    YangMills.Mathematics.SmoothManifoldOneFormExteriorDerivativeCertificate
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) connection.toSmoothForm

namespace PrincipalConnectionData

variable [FiniteDimensional ℝ EG]

/-- Curvature of a principal connection, derived as `dΘ + 1/2 [Θ ∧ Θ]`. -/
noncomputable def curvatureForm
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    YangMills.Mathematics.SmoothManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G)
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) 2 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact YangMills.Mathematics.SmoothManifoldDifferentialForm.add
    exterior.certificate.derivative
    (YangMills.Mathematics.SmoothManifoldDifferentialForm.smul (1 / 2 : ℝ)
      (YangMills.Mathematics.SmoothManifoldDifferentialForm.lieBracketWedgeOne
        (I := IP) (M := P) (V := GroupLieAlgebra IG G)
        (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
        connection.toSmoothForm connection.toSmoothForm))

/-- The bundled curvature retains Freed's exact form-level equation (1.13). -/
theorem curvatureForm_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (connection.curvatureForm exterior).toForm =
      exterior.certificate.derivative.toForm +
        (1 / 2 : ℝ) •
          connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rfl

/-- Evaluated on two tangent vectors, the factor `1/2` cancels the factor two in the self-wedge. -/
theorem curvatureForm_apply
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (connection.curvatureForm exterior).toForm p v =
      exterior.certificate.derivative.toForm p v +
        ⁅connection.pointwise.form p (fun _ => v 0),
          connection.pointwise.form p (fun _ => v 1)⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [curvatureForm_toForm]
  change exterior.certificate.derivative.toForm p v +
      (1 / 2 : ℝ) •
        (connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form) p v = _
  change exterior.certificate.derivative.toForm p v +
      (1 / 2 : ℝ) •
        ((connection.pointwise.form p).lieBracketWedgeOne
          (connection.pointwise.form p)) v = _
  rw [ContinuousAlternatingMap.lieBracketWedgeOne_self_apply]
  module

end PrincipalConnectionData

end

end YangMills.Geometry
