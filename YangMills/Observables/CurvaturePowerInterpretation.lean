/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvatureSquaredInterpretation

/-!
# A finite scalar curvature-power fragment

Clay/Jaffe–Witten §4 asks for local observables corresponding to gauge-invariant curvature
polynomials. This module adds only the finite intrinsic scalar fragment `1`, `F²`, and `(F²)²`, where
`F²` is the already descended, representative-independent canonical curvature density.

Descent is not promoted to a theorem about active gauge transformations of connections. A separate,
explicit project strengthening can require the quartic label to be a new nontrivial operator. This
is not a full curvature-polynomial grammar, an all-power interpretation, or a canonical quantization
map. No interpretation, theory, or mass gap is constructed.
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

/-- The finite intrinsic scalar fragment currently interpreted by the checker. -/
inductive ScalarCurvaturePowerTag where
  | unit
  | curvatureSquared
  | curvatureQuartic
  deriving DecidableEq

/-- Exact classical meaning of the finite fragment on the same descended curvature chain. -/
def classicalScalarCurvaturePowerObservable
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) : ScalarCurvaturePowerTag → B → ℝ
  | .unit => fun _ => 1
  | .curvatureSquared =>
      geometry.canonicalCurvatureDensity inner connection exterior certificate
  | .curvatureQuartic => fun b =>
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ 2

/-- Interpretation of the finite scalar fragment. Its classical carrier is explicitly required to
be the exact function above; the unit and `F²` labels reuse the existing basic interpretation. -/
structure ScalarCurvaturePowerLocalObservableInterpretationData
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (family : Minkowski.TemperedLocalObservableFamilyData D)
    (basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) where
  /-- Supplied classical meaning, exposed so disconnected substitutions can be rejected. -/
  classicalObservable : ScalarCurvaturePowerTag → B → ℝ
  /-- Exact coherence with the same descended canonical curvature density. -/
  classicalObservable_eq : classicalObservable =
    classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate
  /-- Quantum label for every member of this finite fragment. -/
  quantumLabel : ScalarCurvaturePowerTag → family.Label
  /-- The unit is the exact unit label of the same family. -/
  quantumLabel_unit : quantumLabel .unit = family.unitLabel
  /-- `F²` is the exact previously interpreted label, not a second copy. -/
  quantumLabel_curvatureSquared :
    quantumLabel .curvatureSquared = basic.quantumLabel .curvatureSquared

/-- Explicit project anti-collapse strengthening for the first new composite `(F²)²`. Clay's
footnote does not itself imply this separation; it is kept outside the base interpretation record. -/
structure CurvatureQuarticAntiCollapseData
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic) where
  curvatureQuarticLabel_ne_unit : powers.quantumLabel .curvatureQuartic ≠ family.unitLabel
  curvatureQuarticLabel_ne_curvatureSquared :
    powers.quantumLabel .curvatureQuartic ≠ basic.quantumLabel .curvatureSquared
  curvatureQuartic_nontrivial :
    ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
      family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠ 0 ∧
      family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠
        family.operator family.unitLabel f ψ ∧
      family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠
        family.operator (basic.quantumLabel .curvatureSquared) f ψ

@[simp] theorem classicalScalarCurvaturePowerObservable_unit
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate
        .unit = fun _ => 1 :=
  rfl

@[simp] theorem classicalScalarCurvaturePowerObservable_curvatureSquared
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) :
    classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate
        .curvatureSquared =
      geometry.canonicalCurvatureDensity inner connection exterior certificate :=
  rfl

@[simp] theorem classicalScalarCurvaturePowerObservable_curvatureQuartic
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (b : B) :
    classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate
        .curvatureQuartic b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ 2 :=
  rfl

end

end YangMills.Observables
