/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptance

/-!
# Plug-in surface for the bounded three-dimensional SU(2) checker

A future construction submits the strongest dependent data to `ThreeDimensionalSU2PluginReport.pass`.
That constructor cannot be used without all continuum, same-theory, observable, and same-PVM gap
witnesses. `incomplete` and `dimensionMismatch` are honest diagnostic outcomes, not negative
mathematical theorems. In particular, failure to provide the strongest data means only that the
candidate has not established the target.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff

noncomputable section

/-- Named obligations shown by the plug-in diagnostic surface. These names do not weaken the
dependent Lean records that define the authoritative gate. -/
inductive ThreeDimensionalSU2PluginObligation where
  | exactSU2GaugeGeometry
  | classicalThreeDimensionalYangMills
  | continuumWightmanExistence
  | gaugeInvariantObservableIdentification
  | euclideanMinkowskiSameTheory
  | sameJointPVMMassGap
  | nonvacuumSpectralSector
  deriving DecidableEq, Repr

universe uEG uEP uHP uGauge uP uLift uH uLabel

variable
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [FiniteDimensional ℝ EG]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    {P : Type uP} [TopologicalSpace P]
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData GaugeGroup
      ThreeDimensionalEuclideanBase P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData threeDimensionalEuclideanModel
      (modelWithCornersSelf ℝ EG) IP torsor bundle}
    {PoincareLiftGroup : Type uLift} [Group PoincareLiftGroup]
    [TopologicalSpace PoincareLiftGroup] [IsTopologicalGroup PoincareLiftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData
      EuclideanDimension.three PoincareLiftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}

/-- Proof-carrying result of checking a future construction. `pass` stores the exact strongest data;
there is no evidence-free successful constructor. An incomplete result is diagnostic rather than a
proof of mathematical impossibility. -/
inductive ThreeDimensionalSU2PluginReport where
  | pass (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData.{uEG, uEP, uHP,
      uGauge, uP, uLift, uH, uLabel}
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate))
  | incomplete (missing : List ThreeDimensionalSU2PluginObligation) (nonempty : missing ≠ [])
  | dimensionMismatch (candidateDimension : EuclideanDimension)
      (mismatch : candidateDimension ≠ EuclideanDimension.three)

namespace ThreeDimensionalSU2PluginReport

/-- Stable human-facing status labels. -/
def status
    (report : ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) : String :=
  match report with
  | .pass _ => "PASS"
  | .incomplete _ _ => "INCOMPLETE"
  | .dimensionMismatch _ _ => "DIMENSION MISMATCH"

/-- Only a proof-carrying `pass` report yields the strongest data. Wrapping the returned datum in
`Nonempty` gives the authoritative acceptance proposition. -/
def acceptanceData?
    (report : ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    Option (ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :=
  match report with
  | .pass data => some data
  | .incomplete _ _ => none
  | .dimensionMismatch _ _ => none

/-- A future candidate with every strongest-tier witness obtains a proof-carrying pass report. -/
def ofData
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .pass data

end ThreeDimensionalSU2PluginReport

end

end YangMills.Dimensions
