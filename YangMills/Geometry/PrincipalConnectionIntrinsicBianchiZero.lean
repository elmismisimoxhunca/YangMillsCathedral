/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundlePositiveCovariantExteriorDerivative
import YangMills.Geometry.PrincipalCurvatureCoordinateBianchi
import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeExtChart

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology
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

namespace PrincipalForm

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [LieGroup IG (minSmoothness ℝ 3) G] [IsManifold IB ∞ B] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Selected descent preserves the zero principal form exactly. -/
theorem selectedBaseForm_zero (k : ℕ) :
    selectedBaseForm (IB := IB) (bundle := bundle)
        (0 : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) k) =
      AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k := by
  funext b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  ext vectors
  let chart := bundle.trivializationAt b
  let hb := bundle.mem_baseSet_trivializationAt b
  apply (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb).injective
  rw [selectedBaseForm_coordinate]
  rw [AdjointBundle.DifferentialForm.zero_apply, map_zero]
  rfl

end PrincipalForm

namespace PrincipalConnectionData

omit [FiniteDimensional ℝ EB] [ENat.LEInfty (minSmoothness ℝ 3)] in
set_option backward.isDefEq.respectTransparency false in
lemma curvatureCovariantExteriorCandidate_inExtChartAt_center_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (p : P) :
    (PrincipalForm.covariantExteriorCandidate connection 1
      (connection.curvatureForm exterior) curvatureExterior).toForm.inExtChartAt
        (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have derivative_eq :=
    curvatureExterior.inExtChartAt_derivative_eq_extDerivWithin
      (groupLieAlgebraModelEquiv IG) 1 (connection.curvatureForm exterior) p
  have bracket_eq :=
    connection.pointwise.form.inExtChartAt_lieBracketWedgeOneMany
      (IG := IG) (G := G) 2 (connection.curvatureForm exterior).toForm p
  have derivative_eq' :
      curvatureExterior.derivative.toForm.inExtChartAt
          (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) =
        extDerivWithin (connection.curvatureCoordinatesInExtChartAt exterior p)
          (extChartAt IP p).target ((extChartAt IP p) p) := by
    simpa only [Nat.reduceAdd, PrincipalConnectionData.curvatureCoordinatesInExtChartAt] using
      derivative_eq
  have bracket_eq' :
      (connection.pointwise.form.lieBracketWedgeOneMany 2
        (connection.curvatureForm exterior).toForm).inExtChartAt
          (groupLieAlgebraModelEquiv IG) 3 p =
        fun x => ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
          (connection.connectionCoordinatesInExtChartAt p x)
          (connection.curvatureCoordinatesInExtChartAt exterior p x) := by
    simpa only [Nat.reduceAdd, PrincipalConnectionData.connectionCoordinatesInExtChartAt,
      PrincipalConnectionData.curvatureCoordinatesInExtChartAt] using bracket_eq
  have bianchi := connection.curvatureCoordinatesInExtChartAt_coordinateBianchi_finiteDimensional
    exterior p ((extChartAt IP p) p) (mem_extChartAt_target p)
  rw [PrincipalForm.covariantExteriorCandidate_toForm]
  change (curvatureExterior.derivative.toForm +
      connection.pointwise.form.lieBracketWedgeOneMany 2
        (connection.curvatureForm exterior).toForm).inExtChartAt
      (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) = 0
  rw [show (curvatureExterior.derivative.toForm +
      connection.pointwise.form.lieBracketWedgeOneMany 2
        (connection.curvatureForm exterior).toForm).inExtChartAt
      (groupLieAlgebraModelEquiv IG) 3 p =
      curvatureExterior.derivative.toForm.inExtChartAt
        (groupLieAlgebraModelEquiv IG) 3 p +
      (connection.pointwise.form.lieBracketWedgeOneMany 2
        (connection.curvatureForm exterior).toForm).inExtChartAt
          (groupLieAlgebraModelEquiv IG) 3 p by
    exact ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_add
      (groupLieAlgebraModelEquiv IG) 3 curvatureExterior.derivative.toForm
      (connection.pointwise.form.lieBracketWedgeOneMany 2
        (connection.curvatureForm exterior).toForm)
      (extChartAt IP p).symm (Set.range ⇑IP)]
  change curvatureExterior.derivative.toForm.inExtChartAt
      (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) +
    (connection.pointwise.form.lieBracketWedgeOneMany 2
      (connection.curvatureForm exterior).toForm).inExtChartAt
        (groupLieAlgebraModelEquiv IG) 3 p ((extChartAt IP p) p) = 0
  rw [derivative_eq', bracket_eq']
  exact bianchi

omit [FiniteDimensional ℝ EB] in
/-- The same principal-total-space covariant exterior candidate vanishes intrinsically. -/
theorem curvatureCovariantExteriorCandidate_toForm_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    (PrincipalForm.covariantExteriorCandidate connection 1
      (connection.curvatureForm exterior) curvatureExterior).toForm = 0 := by
  funext p
  ext vectors
  let coordinateVectors : Fin 3 → EP := fun i =>
    mfderiv IP (modelWithCornersSelf ℝ EP) (extChartAt IP p) p (vectors i)
  have center_zero := connection.curvatureCovariantExteriorCandidate_inExtChartAt_center_eq_zero
    exterior curvatureExterior p
  have evaluated := congrArg
    (fun A : EP [⋀^Fin 3]→L[ℝ] EG => A coordinateVectors) center_zero
  have cancel (i : Fin 3) :
      mfderivWithin (modelWithCornersSelf ℝ EP) IP (extChartAt IP p).symm
          (Set.range ⇑IP) ((extChartAt IP p) p) (coordinateVectors i) = vectors i := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := IP) (x := p) (mem_extChartAt_target p)
    rw [extChartAt_to_inv] at hcomp
    exact congrArg (fun L : TangentSpace IP p →L[ℝ] TangentSpace IP p => L (vectors i)) hcomp
  change groupLieAlgebraModelEquiv IG
      ((PrincipalForm.covariantExteriorCandidate connection 1
        (connection.curvatureForm exterior) curvatureExterior).toForm
          ((extChartAt IP p).symm ((extChartAt IP p) p))
          (fun i => mfderivWithin (modelWithCornersSelf ℝ EP) IP
            (extChartAt IP p).symm (Set.range ⇑IP) ((extChartAt IP p) p)
              (coordinateVectors i))) = 0 at evaluated
  rw [extChartAt_to_inv] at evaluated
  have evaluated' : groupLieAlgebraModelEquiv IG
      ((PrincipalForm.covariantExteriorCandidate connection 1
        (connection.curvatureForm exterior) curvatureExterior).toForm p vectors) = 0 := by
    convert evaluated using 1
    congr 3
    funext i
    exact (cancel i).symm
  exact (groupLieAlgebraModelEquiv IG).injective (by simpa using evaluated')

/-- Intrinsic descended Bianchi: the constructed same-chain `D_A F` is the smooth zero
adjoint-bundle-valued three-form, without an assumed naturality or zero bridge. -/
theorem curvatureCovariantExteriorDerivative_toForm_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
      curvatureStructure curvatureExterior).toForm =
      (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [connection.curvatureCovariantExteriorDerivative_toForm IG IB IP smoothBundle exterior
    curvatureStructure curvatureExterior]
  rw [connection.curvatureCovariantExteriorCandidate_toForm_eq_zero exterior curvatureExterior]
  exact PrincipalForm.selectedBaseForm_zero (IG := IG) (IB := IB) (IP := IP) 3

/-- Bundled intrinsic Bianchi identity: the smooth same-chain `D_A F` object itself is the
canonical smooth zero adjoint-bundle-valued three-form. -/
theorem curvatureCovariantExteriorDerivative_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior)) :
    connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
        curvatureStructure curvatureExterior =
      AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 := by
  cases hleft : connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
      curvatureStructure curvatureExterior with
  | mk leftForm leftSmooth =>
    cases hright : AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3 with
    | mk rightForm rightSmooth =>
      simp only [AdjointBundle.DifferentialForm.Smooth.mk.injEq]
      have hl := congrArg AdjointBundle.DifferentialForm.Smooth.toForm hleft
      have hr := congrArg AdjointBundle.DifferentialForm.Smooth.toForm hright
      calc
        leftForm = (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
          curvatureStructure curvatureExterior).toForm := hl.symm
        _ = (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm :=
          connection.curvatureCovariantExteriorDerivative_toForm_eq_zero exterior
            curvatureStructure curvatureExterior
        _ = rightForm := hr

/-- Pointwise form evaluation of the descended Bianchi carrier is the canonical dependent-fiber
zero evaluation. -/
theorem curvatureCovariantExteriorDerivative_apply_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (curvatureStructure : PrincipalCurvatureStructureCertificate smoothBundle connection exterior)
    (curvatureExterior : SmoothManifoldTwoFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) (connection.curvatureForm exterior))
    (b : B) (vectors : Fin 3 → TangentSpace IB b) :
    (connection.curvatureCovariantExteriorDerivative IG IB IP smoothBundle exterior
      curvatureStructure curvatureExterior).toForm b vectors =
      (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle 3).toForm b vectors := by
  rw [connection.curvatureCovariantExteriorDerivative_toForm_eq_zero exterior
    curvatureStructure curvatureExterior]


end PrincipalConnectionData

end
end YangMills.Geometry
