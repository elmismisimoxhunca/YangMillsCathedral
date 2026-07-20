/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionCoordinateExteriorNaturality

/-!
# Hostile probes for inverse-chart exterior naturality reduction

The probes expose the exact remaining Cartan-transport equality, both independently derived sides,
and its sufficiency for full inverse-chart naturality. No naturality or Cartan-transport witness is
constructed.
-/

namespace YangMills.Geometry.PrincipalConnectionCoordinateExteriorNaturality.Probes

open Set Function
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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EP]

/-- The remaining obligation is exactly equality of intrinsic and coordinate Cartan expressions on
chart-pulled constant fields. -/
theorem exact_cartan_naturality_shape
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p ↔
      ∀ (x : EP), x ∈ (extChartAt IP p).target → ∀ v w : EP,
        connection.toSmoothForm.toForm.oneFormCartanExpressionCoordinates
            (groupLieAlgebraModelEquiv IG) (extChartAt IP p).source
            ((extChartAt IP p).symm x)
            (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
              (extChartAt IP p) (fun _ => v))
            (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
              (extChartAt IP p) (fun _ => w)) =
          ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
            (I := modelWithCornersSelf ℝ EP) (ContinuousLinearEquiv.refl ℝ EG)
            (connection.connectionCoordinatesInExtChartAt p).toManifoldForm
            (extChartAt IP p).target x (fun _ => v) (fun _ => w) :=
  Iff.rfl

/-- The certified derivative side is derived from the existing manifold Cartan certificate. -/
theorem exact_certified_derivative_cartan
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x v w : EP) (hx : x ∈ (extChartAt IP p).target) :
    exterior.coordinatesInExtChartAt p x (fun i => Fin.cases v (fun _ => w) i) =
      connection.toSmoothForm.toForm.oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) (extChartAt IP p).source
        ((extChartAt IP p).symm x)
        (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
          (extChartAt IP p) (fun _ => v))
        (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
          (extChartAt IP p) (fun _ => w)) :=
  exterior.exterior_coordinatesInExtChartAt_eq_cartan_constantFields p x v w hx

/-- The coordinate side is derived from Mathlib's `extDerivWithin` Cartan formula. -/
theorem exact_coordinate_extDeriv_cartan
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (x v w : EP) (hx : x ∈ (extChartAt IP p).target) :
    extDerivWithin (connection.connectionCoordinatesInExtChartAt p)
        (extChartAt IP p).target x (fun i => Fin.cases v (fun _ => w) i) =
      ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ EP) (ContinuousLinearEquiv.refl ℝ EG)
        (connection.connectionCoordinatesInExtChartAt p).toManifoldForm
        (extChartAt IP p).target x (fun _ => v) (fun _ => w) :=
  connection.extDerivWithin_connectionCoordinates_eq_coordinateCartan_constantFields p x v w hx

/-- The explicit Cartan equality, rather than an unrelated derivative equality, implies the full
inverse-chart naturality proposition. -/
theorem exact_naturality_reduction
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P)
    (cartan : PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p) :
    exterior.IsNaturalInExtChartAt p :=
  exterior.isNaturalInExtChartAt_of_cartanNaturality p cartan

/-- The residual Cartan equality is exactly equivalent to full inverse-chart naturality. -/
theorem exact_naturality_iff_cartan_transport
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    exterior.IsNaturalInExtChartAt p ↔
      PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p :=
  exterior.isNaturalInExtChartAt_iff_cartanNaturality p

/-- Generic Cartan transport and intrinsic connection smoothness derive the formerly residual
principal Cartan equality. -/
theorem exact_derived_cartan_transport
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p :=
  connection.coordinateCartanNaturalityInExtChartAt p

/-- The exact connection-indexed certificate now has derived inverse-chart exterior naturality. -/
theorem exact_derived_exterior_naturality
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    exterior.IsNaturalInExtChartAt p :=
  exterior.isNaturalInExtChartAt p

/-- A mismatched intrinsic/coordinate Cartan value contradicts the exact remaining obligation. -/
theorem mismatched_cartan_transport_blocked
    (connection : PrincipalConnectionData smoothBundle) (p : P)
    (cartan : PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p)
    (x : EP) (hx : x ∈ (extChartAt IP p).target) (v w : EP)
    (different :
      connection.toSmoothForm.toForm.oneFormCartanExpressionCoordinates
          (groupLieAlgebraModelEquiv IG) (extChartAt IP p).source
          ((extChartAt IP p).symm x)
          (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
            (extChartAt IP p) (fun _ => v))
          (VectorField.mpullback IP (modelWithCornersSelf ℝ EP)
            (extChartAt IP p) (fun _ => w)) ≠
        ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ EP) (ContinuousLinearEquiv.refl ℝ EG)
          (connection.connectionCoordinatesInExtChartAt p).toManifoldForm
          (extChartAt IP p).target x (fun _ => v) (fun _ => w)) : False :=
  different (cartan x hx v w)

end

end YangMills.Geometry.PrincipalConnectionCoordinateExteriorNaturality.Probes
