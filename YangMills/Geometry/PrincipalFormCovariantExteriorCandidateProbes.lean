/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorCandidate

/-!
# Hostile probes for the positive-degree principal covariant-exterior candidate
-/

namespace YangMills.Geometry.PrincipalFormCovariantExteriorCandidate.Probes

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

/-- The first positive-degree specialization is an exact smooth `2 → 3` expression. -/
noncomputable def exact_two_to_three_candidate
    (connection : PrincipalConnectionData smoothBundle)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 2)
    (exterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) form) :
    SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 3 :=
  PrincipalForm.covariantExteriorCandidate connection 1 form exterior

/-- The candidate cannot silently replace the supplied ordinary derivative. -/
theorem unrelated_derivative_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (other : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) (n + 2))
    (candidate_eq :
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm =
        other + (PrincipalForm.covariantExteriorBracket connection n form).toForm) :
    other = exterior.derivative.toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [PrincipalForm.covariantExteriorCandidate_toForm] at candidate_eq
  exact add_right_cancel candidate_eq.symm

/-- Omitting the connection bracket contradicts any witnessed nonzero bracket term. -/
theorem omitted_connection_bracket_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (nonzeroBracket :
      (PrincipalForm.covariantExteriorBracket connection n form).toForm p vectors ≠ 0)
    (omitted :
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm p vectors =
        exterior.derivative.toForm p vectors) : False := by
  rw [PrincipalForm.covariantExteriorCandidate_apply] at omitted
  apply nonzeroBracket
  apply add_left_cancel (a := exterior.derivative.toForm p vectors)
  simpa using omitted

end

end YangMills.Geometry.PrincipalFormCovariantExteriorCandidate.Probes
