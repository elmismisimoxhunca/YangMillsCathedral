/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCanonicalCurvatureContraction
import YangMills.Minkowski.TemperedLocalObservableProducts

/-!
# Classical-to-quantum interpretation of the curvature-squared observable

Clay/Jaffe–Witten §4 requires local gauge-invariant observables, while the classical action uses the
invariant quadratic curvature density. This module provides a deliberately small interpretation
bridge: the quantum unit and curvature-squared labels are tied to the exact same classical metric,
invariant pairing, connection, certified exterior derivative, and descended curvature chain.

This is not yet a grammar of arbitrary curvature polynomials or covariant derivatives. No
quantization map, observable family, field, theory, or mass gap is constructed.
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

/-- The two basic curvature-observable tags available at this stage. The name does not assert a
separate theorem about gauge transformations of connections; the `F²` branch uses the already
descended curvature and invariant fiber pairing. -/
inductive BasicCurvatureObservableTag where
  | unit
  | curvatureSquared
  deriving DecidableEq

/-- Exact classical meaning of the basic observable tags. The curvature-squared branch is the
basis-free canonical density of the same certified curvature chain. -/
def basicClassicalCurvatureObservable
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    BasicCurvatureObservableTag → B → ℝ
  | .unit => fun _ => 1
  | .curvatureSquared =>
      geometry.canonicalCurvatureDensity inner connection exterior certificate

/-- Interpretation of the exact basic classical observables as labels in one exact quantum local
observable family and common-domain/Poincaré chain. -/
structure CurvatureSquaredLocalObservableInterpretationData
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (family : Minkowski.TemperedLocalObservableFamilyData D) where
  /-- A designated classical base point prevents a vacuous empty-base interpretation. -/
  basePoint : B
  /-- The classical base tangent dimension agrees with the exact quantum spacetime index. -/
  baseDimension_eq : ∀ b : B,
    Module.finrank ℝ (TangentSpace IB b) = d.value
  /-- Quantum label assigned to each exact basic classical tag. -/
  quantumLabel : BasicCurvatureObservableTag → family.Label
  /-- The classical unit is the already normalized unit label of the same family. -/
  quantumLabel_unit : quantumLabel .unit = family.unitLabel
  /-- Curvature squared is not silently identified with the unit. -/
  curvatureSquaredLabel_ne_unit :
    quantumLabel .curvatureSquared ≠ family.unitLabel
  /-- Curvature squared acts nontrivially and differently from the unit on one exact test/vector. -/
  curvatureSquared_nontrivial :
    ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
      family.operator (quantumLabel .curvatureSquared) f ψ ≠ 0 ∧
      family.operator (quantumLabel .curvatureSquared) f ψ ≠
        family.operator family.unitLabel f ψ

/-- The classical curvature-squared tag is definitionally the canonical density of the exact
connection/exterior/certificate chain. -/
theorem basicClassicalCurvatureObservable_curvatureSquared
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    basicClassicalCurvatureObservable geometry inner connection exterior certificate
        .curvatureSquared =
      geometry.canonicalCurvatureDensity inner connection exterior certificate :=
  rfl

end

end YangMills.Observables
