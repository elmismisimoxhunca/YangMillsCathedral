/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureCoordinateBianchiBridge
import YangMills.Mathematics.ManifoldOneFormExtChartNaturality

/-!
# Derived inverse-chart exterior naturality through Cartan transport

This module first isolates the exact equality controlling inverse-chart naturality of the
connection-indexed exterior derivative. The supplied manifold certificate identifies the certified
derivative with its intrinsic Cartan expression on chart-pulled constant fields, while Mathlib's
normed-space theorem identifies `extDerivWithin` with the coordinate Cartan expression. Degree-two
extensionality proves that equality is exactly equivalent to full naturality.

Reusable inverse-chart Cartan mathematics now proves the isolated equality from the within-chain
rule, inverse tangent cancellation, and Lie-bracket pullback. Intrinsic connection smoothness then
derives full naturality without adding a witness.
-/

namespace YangMills.Geometry

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

/-- Exact remaining inverse-chart Cartan-transport equality. The left side uses intrinsic manifold
Cartan calculus on pullbacks of constant coordinate fields; the right side uses the coordinate
one-form and the actual chart target. -/
def PrincipalConnectionCoordinateCartanNaturalityInExtChartAt
    [FiniteDimensional ℝ EP]
    (connection : PrincipalConnectionData smoothBundle) (p : P) : Prop :=
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
        (extChartAt IP p).target x (fun _ => v) (fun _ => w)

namespace PrincipalConnectionData

/-- Reusable inverse-chart Cartan transport and intrinsic connection smoothness discharge the exact
remaining principal-connection Cartan naturality condition. -/
theorem coordinateCartanNaturalityInExtChartAt
    [FiniteDimensional ℝ EP]
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p := by
  intro x hx v w
  have hcoord : DifferentiableWithinAt ℝ
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target x :=
    (connection.connectionCoordinatesInExtChartAt_contDiffWithinAt p x hx).differentiableWithinAt
      (by simp)
  simpa [PrincipalConnectionData.toSmoothForm,
    PrincipalConnectionData.connectionCoordinatesInExtChartAt] using
    (connection.pointwise.form.oneFormCartanExpressionCoordinates_inExtChartAt
      (groupLieAlgebraModelEquiv IG) p x hx v w (by
        simpa [PrincipalConnectionData.connectionCoordinatesInExtChartAt] using hcoord))

end PrincipalConnectionData

namespace PrincipalConnectionExteriorDerivativeData

/-- The coordinate pullback of the certified derivative is exactly its intrinsic Cartan expression
on inverse-chart pullbacks of constant coordinate fields. -/
theorem exterior_coordinatesInExtChartAt_eq_cartan_constantFields
    [FiniteDimensional ℝ EP]
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
          (extChartAt IP p) (fun _ => w)) := by
  let chart : PartialEquiv P EP := extChartAt IP p
  let firstCoordinate : EP → EP := fun _ => v
  let secondCoordinate : EP → EP := fun _ => w
  let first : (q : P) → TangentSpace IP q :=
    VectorField.mpullback IP (modelWithCornersSelf ℝ EP) chart firstCoordinate
  let second : (q : P) → TangentSpace IP q :=
    VectorField.mpullback IP (modelWithCornersSelf ℝ EP) chart secondCoordinate
  have firstCoordinate_smooth : ContMDiff (modelWithCornersSelf ℝ EP)
      ((modelWithCornersSelf ℝ EP).prod (modelWithCornersSelf ℝ EP)) ∞
      (fun y => (⟨y, firstCoordinate y⟩ : TangentBundle (modelWithCornersSelf ℝ EP) EP)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    simpa [firstCoordinate] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => v))
  have secondCoordinate_smooth : ContMDiff (modelWithCornersSelf ℝ EP)
      ((modelWithCornersSelf ℝ EP).prod (modelWithCornersSelf ℝ EP)) ∞
      (fun y => (⟨y, secondCoordinate y⟩ : TangentBundle (modelWithCornersSelf ℝ EP) EP)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    simpa [secondCoordinate] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : EP => w))
  have first_smooth : ManifoldTangentField.IsSmoothOn IP chart.source first := by
    intro q hq
    simpa [ManifoldTangentField.IsSmoothOn, first, firstCoordinate, chart] using
      (ContMDiffAt.mpullback_vectorField_preimage
        firstCoordinate_smooth.contMDiffAt
        (contMDiffAt_extChartAt' (I := IP) (x := p) (n := ∞) (by simpa [chart] using hq))
        (isInvertible_mfderiv_extChartAt (I := IP) (x := p) (by simpa [chart] using hq))
        (by simp)).contMDiffWithinAt
  have second_smooth : ManifoldTangentField.IsSmoothOn IP chart.source second := by
    intro q hq
    simpa [ManifoldTangentField.IsSmoothOn, second, secondCoordinate, chart] using
      (ContMDiffAt.mpullback_vectorField_preimage
        secondCoordinate_smooth.contMDiffAt
        (contMDiffAt_extChartAt' (I := IP) (x := p) (n := ∞) (by simpa [chart] using hq))
        (isInvertible_mfderiv_extChartAt (I := IP) (x := p) (by simpa [chart] using hq))
        (by simp)).contMDiffWithinAt
  have hq : chart.symm x ∈ chart.source := chart.map_target hx
  have tangent_inverse :
      (mfderiv IP (modelWithCornersSelf ℝ EP) chart (chart.symm x)).inverse =
        mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm (Set.range ⇑IP) x :=
    ContinuousLinearMap.inverse_eq
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx)
  have cartan := exterior.certificate.cartan_formula chart.source (chart.symm x)
    (isOpen_extChartAt_source p) hq (isOpen_extChartAt_source p).uniqueMDiffOn
    first second first_smooth second_smooth
  rw [PrincipalConnectionExteriorDerivativeData.coordinatesInExtChartAt,
    ManifoldDifferentialForm.inExtChartAt_apply]
  calc
    (groupLieAlgebraModelEquiv IG)
        (exterior.certificate.derivative.toForm ((extChartAt IP p).symm x)
          (fun i => mfderivWithin (modelWithCornersSelf ℝ EP) IP
            (extChartAt IP p).symm (Set.range ⇑IP) x
            (Fin.cases v (fun _ => w) i))) =
      (groupLieAlgebraModelEquiv IG)
        (exterior.certificate.derivative.toForm (chart.symm x)
          (ManifoldDifferentialForm.twoVectorArguments first second (chart.symm x))) := by
            congr 2
            funext i
            fin_cases i
            · change mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm
                (Set.range ⇑IP) x v =
                (mfderiv IP (modelWithCornersSelf ℝ EP) chart (chart.symm x)).inverse v
              exact congrArg (fun L : EP →L[ℝ] TangentSpace IP (chart.symm x) => L v)
                tangent_inverse.symm
            · change mfderivWithin (modelWithCornersSelf ℝ EP) IP chart.symm
                (Set.range ⇑IP) x w =
                (mfderiv IP (modelWithCornersSelf ℝ EP) chart (chart.symm x)).inverse w
              exact congrArg (fun L : EP →L[ℝ] TangentSpace IP (chart.symm x) => L w)
                tangent_inverse.symm
    _ = _ := cartan

end PrincipalConnectionExteriorDerivativeData

namespace PrincipalConnectionData

/-- Mathlib's coordinate side: `extDerivWithin` of the exact smooth coordinate connection is its
normed-space Cartan expression on constant fields. -/
theorem extDerivWithin_connectionCoordinates_eq_coordinateCartan_constantFields
    [FiniteDimensional ℝ EP]
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (x v w : EP) (hx : x ∈ (extChartAt IP p).target) :
    extDerivWithin (connection.connectionCoordinatesInExtChartAt p)
        (extChartAt IP p).target x (fun i => Fin.cases v (fun _ => w) i) =
      ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ EP) (ContinuousLinearEquiv.refl ℝ EG)
        (connection.connectionCoordinatesInExtChartAt p).toManifoldForm
        (extChartAt IP p).target x (fun _ => v) (fun _ => w) := by
  have regular := connection.connectionCoordinatesInExtChartAt_contDiffWithinAt p x hx
  have formula :=
    NormedSpaceDifferentialForm.extDerivWithin_eq_oneFormCartanExpression
      (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target x (fun _ => v) (fun _ => w)
      (regular.differentiableWithinAt (by simp))
      (differentiableWithinAt_const v) (differentiableWithinAt_const w)
      (uniqueDiffOn_extChartAt_target p x hx)
  have tuple_eq :
      ManifoldDifferentialForm.twoVectorArguments
          (I := modelWithCornersSelf ℝ EP) (fun _ => v) (fun _ => w) x =
        (fun i => Fin.cases v (fun _ => w) i) := by
    funext i
    fin_cases i <;> rfl
  exact (congrArg
    (fun args => extDerivWithin (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target x args) tuple_eq).symm.trans formula

end PrincipalConnectionData

namespace PrincipalConnectionExteriorDerivativeData

/-- Equality of the two explicit Cartan expressions is sufficient for full inverse-chart exterior
naturality of the exact certificate. -/
theorem isNaturalInExtChartAt_of_cartanNaturality
    [FiniteDimensional ℝ EP]
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P)
    (cartan_naturality : PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p) :
    exterior.IsNaturalInExtChartAt p := by
  unfold PrincipalConnectionExteriorDerivativeData.IsNaturalInExtChartAt
    PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
  intro x hx
  change exterior.coordinatesInExtChartAt p x =
    extDerivWithin (connection.connectionCoordinatesInExtChartAt p)
      (extChartAt IP p).target x
  ext vectors
  let v := vectors 0
  let w := vectors 1
  have vectors_eq : vectors = fun i => Fin.cases v (fun _ => w) i := by
    funext i
    fin_cases i <;> rfl
  rw [vectors_eq,
    exterior.exterior_coordinatesInExtChartAt_eq_cartan_constantFields p x v w hx,
    cartan_naturality x hx v w,
    ← connection.extDerivWithin_connectionCoordinates_eq_coordinateCartan_constantFields
      p x v w hx]

/-- Full inverse-chart naturality conversely forces the exact Cartan-transport equality. -/
theorem cartanNaturality_of_isNaturalInExtChartAt
    [FiniteDimensional ℝ EP]
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (naturality : exterior.IsNaturalInExtChartAt p) :
    PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p := by
  intro x hx v w
  have hform : exterior.coordinatesInExtChartAt p x =
      extDerivWithin (connection.connectionCoordinatesInExtChartAt p)
        (extChartAt IP p).target x := by
    exact naturality hx
  have heval := congrArg
    (fun form : ContinuousAlternatingMap ℝ EP EG (Fin 2) =>
      form (fun i => Fin.cases v (fun _ => w) i)) hform
  rw [exterior.exterior_coordinatesInExtChartAt_eq_cartan_constantFields p x v w hx,
    connection.extDerivWithin_connectionCoordinates_eq_coordinateCartan_constantFields
      p x v w hx] at heval
  exact heval

/-- The named Cartan-transport equality is exactly equivalent to inverse-chart exterior naturality,
not a weaker proxy or a stronger unrelated condition. -/
theorem isNaturalInExtChartAt_iff_cartanNaturality
    [FiniteDimensional ℝ EP]
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    exterior.IsNaturalInExtChartAt p ↔
      PrincipalConnectionCoordinateCartanNaturalityInExtChartAt connection p :=
  ⟨exterior.cartanNaturality_of_isNaturalInExtChartAt p,
    exterior.isNaturalInExtChartAt_of_cartanNaturality p⟩

/-- In a finite-dimensional principal total-space model, inverse-chart exterior naturality is
derived from the exact connection, certificate, and generic Cartan transport; it is no longer an
acceptance premise. -/
theorem isNaturalInExtChartAt
    [FiniteDimensional ℝ EP]
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    exterior.IsNaturalInExtChartAt p :=
  exterior.isNaturalInExtChartAt_of_cartanNaturality p
    (connection.coordinateCartanNaturalityInExtChartAt p)

end PrincipalConnectionExteriorDerivativeData

end

end YangMills.Geometry
