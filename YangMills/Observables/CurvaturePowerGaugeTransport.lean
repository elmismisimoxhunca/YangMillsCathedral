/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvaturePowerInterpretation
import YangMills.Classical.EuclideanCanonicalCurvatureGaugeInvariance

/-!
# Gauge transport of the finite interpreted curvature fragment

The classical meanings of `1`, `F²`, and `(F²)²` are unchanged by the exact derived gauge-pullback
chain. The existing basic and finite-power interpretation records therefore transport to that chain
while retaining the same quantum family, labels, operator actions, nontriviality witnesses, and
quartic anti-collapse data.

This is exact same-family transport, not the construction of a quantum gauge action on the local
observable family. It does not extend the finite observable grammar.
-/

namespace YangMills.Observables

open Bundle
open scoped Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP uH

noncomputable section

variable
    {d : EuclideanDimension}
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
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}

/-- The exact basic classical carrier is unchanged by gauge pullback. -/
theorem basicClassicalCurvatureObservable_gaugePullback
    [CompleteSpace EP]
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    basicClassicalCurvatureObservable geometry inner
        (Geometry.gaugePullbackConnection gauge connection)
        (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (Geometry.gaugePullbackCurvatureStructureCertificate
          gauge connection exterior certificate) =
      basicClassicalCurvatureObservable geometry inner connection exterior certificate := by
  funext tag b
  cases tag with
  | unit => rfl
  | curvatureSquared =>
      exact geometry.canonicalCurvatureDensity_gaugePullback
        inner gauge connection exterior certificate b

/-- Gauge transport of the basic interpretation keeps the exact quantum labels and witnesses. -/
def CurvatureSquaredLocalObservableInterpretationData.gaugePullback
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    CurvatureSquaredLocalObservableInterpretationData geometry inner
      (Geometry.gaugePullbackConnection gauge connection)
      (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
      (Geometry.gaugePullbackCurvatureStructureCertificate
        gauge connection exterior certificate) family where
  basePoint := interpretation.basePoint
  baseDimension_eq := interpretation.baseDimension_eq
  quantumLabel := interpretation.quantumLabel
  quantumLabel_unit := interpretation.quantumLabel_unit
  curvatureSquaredLabel_ne_unit := interpretation.curvatureSquaredLabel_ne_unit
  curvatureSquared_nontrivial := interpretation.curvatureSquared_nontrivial

omit [FiniteDimensional ℝ EB] in
@[simp] theorem CurvatureSquaredLocalObservableInterpretationData.gaugePullback_basePoint
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    (interpretation.gaugePullback gauge).basePoint = interpretation.basePoint :=
  rfl

omit [FiniteDimensional ℝ EB] in
@[simp] theorem CurvatureSquaredLocalObservableInterpretationData.gaugePullback_baseDimension_eq
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)
    (b : B) :
    (interpretation.gaugePullback gauge).baseDimension_eq b =
      interpretation.baseDimension_eq b :=
  rfl

omit [FiniteDimensional ℝ EB] in
@[simp] theorem CurvatureSquaredLocalObservableInterpretationData.gaugePullback_quantumLabel
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)
    (tag : BasicCurvatureObservableTag) :
    (interpretation.gaugePullback gauge).quantumLabel tag = interpretation.quantumLabel tag :=
  rfl

omit [FiniteDimensional ℝ EB] in
@[simp] theorem CurvatureSquaredLocalObservableInterpretationData.gaugePullback_nontrivial
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    (interpretation.gaugePullback gauge).curvatureSquared_nontrivial =
      interpretation.curvatureSquared_nontrivial :=
  rfl

/-- Every member of the finite scalar fragment is unchanged by gauge pullback. -/
theorem classicalScalarCurvaturePowerObservable_gaugePullback
    [CompleteSpace EP]
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    classicalScalarCurvaturePowerObservable geometry inner
        (Geometry.gaugePullbackConnection gauge connection)
        (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (Geometry.gaugePullbackCurvatureStructureCertificate
          gauge connection exterior certificate) =
      classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate := by
  funext tag b
  cases tag with
  | unit => rfl
  | curvatureSquared =>
      exact geometry.canonicalCurvatureDensity_gaugePullback
        inner gauge connection exterior certificate b
  | curvatureQuartic =>
      rw [classicalScalarCurvaturePowerObservable_curvatureQuartic,
        classicalScalarCurvaturePowerObservable_curvatureQuartic,
        geometry.canonicalCurvatureDensity_gaugePullback
          inner gauge connection exterior certificate b]

/-- Gauge transport of a finite-power interpretation preserves its classical carrier and every
quantum label, while changing only the exact connection-indexed parameters. -/
def ScalarCurvaturePowerLocalObservableInterpretationData.gaugePullback
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic) :
    ScalarCurvaturePowerLocalObservableInterpretationData geometry inner
      (Geometry.gaugePullbackConnection gauge connection)
      (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
      (Geometry.gaugePullbackCurvatureStructureCertificate
        gauge connection exterior certificate) family (basic.gaugePullback gauge) where
  classicalObservable := powers.classicalObservable
  classicalObservable_eq := by
    rw [powers.classicalObservable_eq]
    exact (classicalScalarCurvaturePowerObservable_gaugePullback
      geometry inner gauge connection exterior certificate).symm
  quantumLabel := powers.quantumLabel
  quantumLabel_unit := powers.quantumLabel_unit
  quantumLabel_curvatureSquared := powers.quantumLabel_curvatureSquared

@[simp] theorem ScalarCurvaturePowerLocalObservableInterpretationData.gaugePullback_classicalObservable
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (tag : ScalarCurvaturePowerTag) :
    (powers.gaugePullback gauge).classicalObservable tag = powers.classicalObservable tag :=
  rfl

@[simp] theorem ScalarCurvaturePowerLocalObservableInterpretationData.gaugePullback_quantumLabel
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)
    (tag : ScalarCurvaturePowerTag) :
    (powers.gaugePullback gauge).quantumLabel tag = powers.quantumLabel tag :=
  rfl

/-- Quartic anti-collapse transports without weakening: it is about the preserved family labels and
operator actions, so the same exact witnesses work after gauge pullback. -/
def CurvatureQuarticAntiCollapseData.gaugePullback
    [CompleteSpace EP]
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    {powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic}
    (antiCollapse : CurvatureQuarticAntiCollapseData powers) :
    CurvatureQuarticAntiCollapseData (powers.gaugePullback gauge) where
  curvatureQuarticLabel_ne_unit := antiCollapse.curvatureQuarticLabel_ne_unit
  curvatureQuarticLabel_ne_curvatureSquared :=
    antiCollapse.curvatureQuarticLabel_ne_curvatureSquared
  curvatureQuartic_nontrivial := antiCollapse.curvatureQuartic_nontrivial

end

end YangMills.Observables
