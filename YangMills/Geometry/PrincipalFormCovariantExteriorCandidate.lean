/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormSmoothDescent
import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivative
import YangMills.Mathematics.SmoothGradedLieBracketWedge
import YangMills.Mathematics.SmoothManifoldDifferentialFormOperations

/-!
# Positive-degree principal covariant-exterior candidate

For a smooth Lie-algebra-valued principal `(n+1)`-form with a supplied ordinary exterior-derivative
certificate, this module constructs the exact smooth total-space expression

`dω + [Θ ∧ ω]`.

The expression is tied to one unchanged principal connection, input form, and positive-degree
certificate. It is deliberately called a candidate: the current positive-degree certificate gives
the Cartan formula, but the project does not yet derive that this output is horizontal and
right-adjoint-equivariant. Consequently this module does not descend the candidate or claim an
intrinsic adjoint-bundle operator.
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

/-- The exact smooth same-connection bracket term `[Θ ∧ ω]` in positive degree. -/
noncomputable def covariantExteriorBracket
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1)) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 2) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact SmoothManifoldDifferentialForm.lieBracketWedgeOneMany
    (I := IP) (M := P) (V := GroupLieAlgebra IG G)
    (groupLieAlgebraModelEquiv IG) (n + 1) connection.toSmoothForm form

/-- Forgetting smoothness recovers the exact same-connection graded bracket wedge. -/
@[simp] theorem covariantExteriorBracket_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1)) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorBracket connection n form).toForm =
      connection.pointwise.form.lieBracketWedgeOneMany (n + 1) form.toForm := by
  rfl

/-- The exact smooth total-space candidate `dω + [Θ ∧ ω]` for positive form degree.

This construction does not assert that its output is tensorial. -/
noncomputable def covariantExteriorCandidate
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 2) :=
  SmoothManifoldDifferentialForm.add exterior.derivative
    (covariantExteriorBracket connection n form)

/-- Forgetting smoothness exposes exactly the same certified derivative and connection bracket. -/
@[simp] theorem covariantExteriorCandidate_toForm
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorCandidate connection n form exterior).toForm =
      exterior.derivative.toForm +
        connection.pointwise.form.lieBracketWedgeOneMany (n + 1) form.toForm := by
  change exterior.derivative.toForm + (covariantExteriorBracket connection n form).toForm = _
  rw [covariantExteriorBracket_toForm]

/-- Pointwise evaluation retains the exact certified derivative and same-connection bracket
carrier. -/
theorem covariantExteriorCandidate_apply
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorCandidate connection n form exterior).toForm p vectors =
      exterior.derivative.toForm p vectors +
        (connection.pointwise.form.lieBracketWedgeOneMany (n + 1) form.toForm) p vectors := by
  rw [covariantExteriorCandidate_toForm]
  rfl

end PrincipalForm

end
end YangMills.Geometry
