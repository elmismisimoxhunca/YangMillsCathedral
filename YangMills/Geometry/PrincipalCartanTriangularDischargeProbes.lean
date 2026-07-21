/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCartanTriangularDischarge

namespace YangMills.Geometry.PrincipalCartanTriangularDischarge.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 1000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
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

/-- The ordinary vertical derivative formula requires no supplied triangular cancellation premise. -/
theorem exact_unconditional_vertical_derivative
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    exterior.derivative.toForm p vectors =
      -((-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆) :=
  PrincipalForm.exteriorDerivative_apply_fundamental_unconditional IG IB IP smoothBundle
    n form exterior horizontal equivariant p vectors r X fundamentalSlot

/-- A changed signed vertical derivative contradicts the derived common-source Cartan calculation. -/
theorem changed_unconditional_vertical_derivative_blocked
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X)
    (changed : exterior.derivative.toForm p vectors ≠
      -((-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆)) : False :=
  changed (PrincipalForm.exteriorDerivative_apply_fundamental_unconditional
    IG IB IP smoothBundle n form exterior horizontal equivariant p vectors r X fundamentalSlot)

/-- Full candidate horizontality is derived rather than supplied as candidate data. -/
theorem exact_unconditional_candidate_horizontality
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm) :
    PrincipalForm.IsHorizontal smoothBundle
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm :=
  PrincipalForm.covariantExteriorCandidate_isHorizontal_unconditional
    IG IB IP smoothBundle connection n form exterior horizontal equivariant

/-- A hostile nonhorizontal candidate contradicts vertical tangent generation and Cartan
cancellation. -/
theorem nonhorizontal_candidate_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (hostile : ¬ PrincipalForm.IsHorizontal smoothBundle
      (PrincipalForm.covariantExteriorCandidate connection n form exterior).toForm) : False :=
  hostile (PrincipalForm.covariantExteriorCandidate_isHorizontal_unconditional
    IG IB IP smoothBundle connection n form exterior horizontal equivariant)

end

end YangMills.Geometry.PrincipalCartanTriangularDischarge.Probes
