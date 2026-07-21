/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureStructureFiniteDimensional

namespace YangMills.Geometry.PrincipalCurvatureStructureFiniteDimensional.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section
set_option maxHeartbeats 1000000

variable
    {EG : Type uEG} {HG : Type uHG}
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

/-- Vertical normalization replaces the generic horizontal-input premise in the fundamental-slot
Cartan calculation for a connection. -/
theorem exact_connection_fundamental_derivative
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (vectors : Fin 2 → TangentSpace IP p)
    (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors 0 = principalFundamentalVector smoothBundle p X) :
    exterior.certificate.derivative.toForm p vectors =
      -⁅X, connection.pointwise.form.evalOne p (vectors 1)⁆ :=
  connection.exteriorDerivative_apply_fundamental_first IG IB IP smoothBundle exterior p vectors X
    fundamentalSlot

/-- Curvature horizontality and right-adjoint equivariance are both derived from the same connection
and exterior datum. -/
theorem exact_automatic_curvature_structure
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalTwoForm.IsHorizontal smoothBundle (connection.curvatureForm exterior).toForm ∧
      PrincipalTwoForm.IsRightAdEquivariant smoothBundle
        (connection.curvatureForm exterior).toForm :=
  ⟨connection.curvatureForm_isHorizontal IG IB IP smoothBundle exterior,
    connection.curvatureForm_isRightAdEquivariant IG IB IP smoothBundle exterior⟩

/-- The packaged certificate is indexed by the exact derived curvature chain. -/
theorem exact_finiteDimensional_certificate
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalCurvatureStructureCertificate smoothBundle connection exterior :=
  connection.curvatureStructureCertificate_finiteDimensional IG IB IP smoothBundle exterior

/-- A hostile nonhorizontal curvature contradicts vertical generation and Cartan cancellation. -/
theorem nonhorizontal_curvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (hostile : ¬ PrincipalTwoForm.IsHorizontal smoothBundle
      (connection.curvatureForm exterior).toForm) : False :=
  hostile (connection.curvatureForm_isHorizontal IG IB IP smoothBundle exterior)

/-- A hostile nonequivariant curvature contradicts exact exterior and bracket transport. -/
theorem nonequivariant_curvature_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (hostile : ¬ PrincipalTwoForm.IsRightAdEquivariant smoothBundle
      (connection.curvatureForm exterior).toForm) : False :=
  hostile (connection.curvatureForm_isRightAdEquivariant IG IB IP smoothBundle exterior)

end

end YangMills.Geometry.PrincipalCurvatureStructureFiniteDimensional.Probes
