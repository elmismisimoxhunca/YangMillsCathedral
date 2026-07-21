/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance

namespace YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 1000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

omit [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The fixed right-translation equivalence has the exact inverse action by `g⁻¹`. -/
theorem exact_right_translation_inverse (g : G) (p : P) :
    (principalRightTranslationEquiv (torsor := torsor) g).symm p =
      torsor.rightAction p g⁻¹ := rfl

/-- The ordinary exterior derivative retains the exact right-adjoint action. -/
theorem exact_exterior_derivative_equivariance
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm) :
    PrincipalForm.IsRightAdEquivariant smoothBundle exterior.derivative.toForm :=
  PrincipalForm.exteriorDerivative_isRightAdEquivariant IG IB IP smoothBundle n form exterior
    equivariant

/-- The full same-connection candidate is right-adjoint-equivariant. -/
theorem exact_candidate_equivariance
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm) :
    PrincipalForm.IsRightAdEquivariant smoothBundle
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm :=
  PrincipalForm.covariantExteriorCandidate_isRightAdEquivariant
    IG IB IP smoothBundle connection n form exterior equivariant

/-- A nonequivariant full candidate contradicts exact pullback/certificate uniqueness. -/
theorem nonequivariant_candidate_blocked
    (connection : PrincipalConnectionData smoothBundle) (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (hostile : ¬ PrincipalForm.IsRightAdEquivariant smoothBundle
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm) : False :=
  hostile (PrincipalForm.covariantExteriorCandidate_isRightAdEquivariant
    IG IB IP smoothBundle connection n form exterior equivariant)

end

end YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance.Probes
