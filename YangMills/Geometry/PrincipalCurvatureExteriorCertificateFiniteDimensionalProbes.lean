/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureExteriorCertificateFiniteDimensional

namespace YangMills.Geometry.PrincipalCurvatureExteriorCertificateFiniteDimensional.Probes

open Set Function Filter
open scoped Manifold ContDiff Topology
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G] [LieGroup IG (minSmoothness ℝ 3) G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

omit [FiniteDimensional ℝ EB] in
/-- The constructed ordinary derivative is exactly `-[A∧F]` from the same connection and first
exterior data. -/
theorem exact_curvature_exterior_derivative
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    (connection.curvatureExteriorCertificate_finiteDimensional exterior).derivative =
      SmoothManifoldDifferentialForm.smul (-1 : ℝ)
        (PrincipalForm.covariantExteriorBracket connection 1
          (connection.curvatureForm exterior)) := rfl

omit [FiniteDimensional ℝ EB] in
/-- A hostile replacement of the constructed derivative is rejected. -/
theorem changed_curvature_exterior_derivative_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (changed : (connection.curvatureExteriorCertificate_finiteDimensional exterior).derivative ≠
      SmoothManifoldDifferentialForm.smul (-1 : ℝ)
        (PrincipalForm.covariantExteriorBracket connection 1
          (connection.curvatureForm exterior))) : False :=
  changed rfl

omit [FiniteDimensional ℝ EB] in
/-- The constructed certificate satisfies the full arbitrary-open-set Cartan interface. -/
theorem exact_curvature_exterior_cartan_formula
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (s : Set P) (p : P) (open_s : IsOpen s) (mem_s : p ∈ s)
    (unique_s : UniqueMDiffOn IP s)
    (fields : Fin 3 → (y : P) → TangentSpace IP y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP s (fields i)) :
    (groupLieAlgebraModelEquiv IG)
        ((connection.curvatureExteriorCertificate_finiteDimensional exterior).derivative.toForm p
          (fun i => fields i p)) =
      (connection.curvatureForm exterior).toForm.positiveDegreeCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) 1 s p fields :=
  (connection.curvatureExteriorCertificate_finiteDimensional exterior).cartan_formula
    s p open_s mem_s unique_s fields fields_smooth

/-- The derived carrier is exactly the existing finite-dimensional intrinsic carrier instantiated
with the constructed same-chain curvature exterior certificate, not a disconnected zero form. -/
theorem exact_derived_carrier
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    connection.curvatureCovariantExteriorDerivative_derived exterior =
      connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior
        (connection.curvatureExteriorCertificate_finiteDimensional exterior) := rfl

/-- A hostile disconnected replacement of the derived carrier is rejected. -/
theorem disconnected_derived_carrier_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (changed : connection.curvatureCovariantExteriorDerivative_derived exterior ≠
      connection.curvatureCovariantExteriorDerivative_finiteDimensional exterior
        (connection.curvatureExteriorCertificate_finiteDimensional exterior)) : False :=
  changed rfl

/-- With only the connection and its exact first exterior data supplied, the derived intrinsic
covariant curvature derivative vanishes. -/
theorem exact_derived_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    connection.curvatureCovariantExteriorDerivative_derived exterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 :=
  connection.curvatureCovariantExteriorDerivative_derived_eq_zero exterior

/-- A hostile nonzero derived intrinsic Bianchi output is rejected. -/
theorem nonzero_derived_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (nonzero : connection.curvatureCovariantExteriorDerivative_derived exterior ≠
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3) : False :=
  nonzero (connection.curvatureCovariantExteriorDerivative_derived_eq_zero exterior)

end

end YangMills.Geometry.PrincipalCurvatureExteriorCertificateFiniteDimensional.Probes
