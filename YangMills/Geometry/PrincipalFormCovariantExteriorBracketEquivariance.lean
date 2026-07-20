/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorCandidate
import YangMills.Mathematics.LieGroupAdjointBracket

/-!
# Right-adjoint equivariance of the covariant bracket correction

For every positive degree, the exact same-connection bracket term `[Θ ∧ ω]` preserves
right-adjoint equivariance. The proof combines connection and input equivariance termwise with the
proved preservation of the intrinsic Lie bracket by the derivative-defined adjoint action.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff
open YangMills.Mathematics

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

namespace PrincipalForm

/-- The same-connection bracket term preserves right adjoint equivariance in every positive
input degree. -/
theorem covariantExteriorBracket_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    IsRightAdEquivariant smoothBundle
      (covariantExteriorBracket connection n form).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  intro g p v
  rw [covariantExteriorBracket_toForm]
  simp only [ManifoldDifferentialForm.lieBracketWedgeOneMany_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  have hconnection :
      connection.pointwise.form (torsor.rightAction p g)
          (fun _ => principalRightTranslationDifferential smoothBundle p g (v i)) =
        lieGroupAdjoint IG g⁻¹
          (connection.pointwise.form p (fun _ => v i)) :=
    connection.right_equivariant p g (v i)
  rw [hconnection]
  have hremove :
      i.removeNth (fun j => principalRightTranslationDifferential smoothBundle p g (v j)) =
        fun j => principalRightTranslationDifferential smoothBundle p g ((i.removeNth v) j) := rfl
  rw [hremove, equivariant g p (i.removeNth v)]
  congr 1
  exact (lieGroupAdjoint_lieBracket IG g⁻¹
    (connection.pointwise.form p (fun _ => v i))
    (form.toForm p (i.removeNth v))).symm

end PrincipalForm

end
end YangMills.Geometry
