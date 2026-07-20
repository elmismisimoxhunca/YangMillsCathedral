/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorVertical

/-!
# Hostile probes for vertical-slot covariant-exterior formulas
-/

namespace YangMills.Geometry.PrincipalFormCovariantExteriorVertical.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
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

omit [FiniteDimensional ℝ EG] in
/-- Every fundamental vector is vertical for the exact bundle projection. -/
theorem exact_fundamental_vertical
    (p : P) (X : GroupLieAlgebra IG G) :
    mfderiv IP IB torsor.projection p (principalFundamentalVector smoothBundle p X) = 0 :=
  principalFundamentalVector_projection_eq_zero p X

/-- One fundamental slot gives the exact signed intrinsic bracket correction. -/
theorem exact_fundamental_slot
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (PrincipalForm.covariantExteriorBracket connection n form).toForm p vectors =
      (-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆ :=
  PrincipalForm.covariantExteriorBracket_apply_fundamentalSlot
    connection n form horizontal p vectors r X fundamentalSlot

/-- The exact negative derivative formula implies horizontality of the full candidate. -/
theorem exact_conditional_candidate_horizontality
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (derivative_vertical : ∀ (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
      (r : Fin (n + 2)), mfderiv IP IB torsor.projection p (vectors r) = 0 →
      exterior.derivative.toForm p vectors =
        -((-1 : ℤ) ^ (r : ℕ) •
          ⁅connection.pointwise.form.evalOne p (vectors r),
            form.toForm p (r.removeNth vectors)⁆)) :
    PrincipalForm.IsHorizontal smoothBundle
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm :=
  PrincipalForm.covariantExteriorCandidate_isHorizontal_of_derivative_vertical
    connection n form exterior horizontal derivative_vertical

/-- Without the required derivative cancellation, the bracket correction is not silently erased. -/
theorem omitted_fundamental_correction_blocked
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X)
    (nonzero : (-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆ ≠ 0)
    (omitted : (PrincipalForm.covariantExteriorBracket connection n form).toForm p vectors = 0) :
    False := by
  apply nonzero
  rw [← PrincipalForm.covariantExteriorBracket_apply_fundamentalSlot
    connection n form horizontal p vectors r X fundamentalSlot]
  exact omitted

end

end YangMills.Geometry.PrincipalFormCovariantExteriorVertical.Probes
