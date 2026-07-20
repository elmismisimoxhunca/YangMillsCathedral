/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvaturePowerInterpretation

/-!
# All natural powers of the canonical curvature density

Clay/Jaffe--Witten §4 asks for local fields corresponding to gauge-invariant curvature
polynomials. This module strengthens the existing finite intrinsic fragment by assigning a label to
every natural power `(F²)ⁿ` of the same exact canonical curvature density. Indices `0`, `1`, and `2`
are required to reuse the existing labels `1`, `F²`, and `(F²)²` exactly.

This remains a narrow scalar subgrammar. It does not provide independent contractions, mixed
polynomials, covariant derivatives, injectivity, pairwise label separation, or a quantization map.
No interpretation, theory, or mass gap is constructed.
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

/-- Exact classical scalar `(F²)ⁿ` on the same descended curvature chain. -/
def classicalScalarCurvatureAllPowersObservable
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) (n : ℕ) (b : B) : ℝ :=
  geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ n

/-- Natural exponent represented by each tag of the existing finite fragment. -/
def ScalarCurvaturePowerTag.exponent : ScalarCurvaturePowerTag → ℕ
  | .unit => 0
  | .curvatureSquared => 1
  | .curvatureQuartic => 2

/-- Interpretation of every natural power, retaining exact reuse of the existing finite labels. -/
structure ScalarCurvatureAllPowersLocalObservableInterpretationData
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (family : Minkowski.TemperedLocalObservableFamilyData D)
    (basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)
    (finitePowers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic) where
  /-- Supplied classical family, exposed so unrelated substitutions can be rejected. -/
  classicalObservable : ℕ → B → ℝ
  /-- Exact coherence with every natural power of the same canonical density. -/
  classicalObservable_eq : classicalObservable =
    classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate
  /-- Quantum label in the same exact local-observable family for every natural power. -/
  quantumLabel : ℕ → family.Label
  /-- Power zero reuses the finite unit label. -/
  quantumLabel_zero : quantumLabel 0 = finitePowers.quantumLabel .unit
  /-- Power one reuses the finite `F²` label. -/
  quantumLabel_one : quantumLabel 1 = finitePowers.quantumLabel .curvatureSquared
  /-- Power two reuses the finite `(F²)²` label. -/
  quantumLabel_two : quantumLabel 2 = finitePowers.quantumLabel .curvatureQuartic

namespace ScalarCurvatureAllPowersLocalObservableInterpretationData

variable
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family}
    {finitePowers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic}

@[simp] theorem classicalObservable_apply
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (n : ℕ) (b : B) :
    allPowers.classicalObservable n b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ n := by
  rw [allPowers.classicalObservable_eq]
  rfl

@[simp] theorem classicalObservable_zero
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (b : B) : allPowers.classicalObservable 0 b = 1 := by
  simp

@[simp] theorem classicalObservable_one
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (b : B) :
    allPowers.classicalObservable 1 b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  simp

@[simp] theorem classicalObservable_two
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (b : B) :
    allPowers.classicalObservable 2 b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ 2 := by
  simp

@[simp] theorem classicalObservable_succ
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (n : ℕ) (b : B) :
    allPowers.classicalObservable (n + 1) b =
      allPowers.classicalObservable n b *
        geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  simp [pow_succ]

/-- Restriction along the finite tag exponents, definitionally using the all-power carriers. -/
def finiteRestriction
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers) :
    ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic where
  classicalObservable tag := allPowers.classicalObservable tag.exponent
  classicalObservable_eq := by
    funext tag b
    cases tag <;> simp [ScalarCurvaturePowerTag.exponent,
      classicalScalarCurvaturePowerObservable]
  quantumLabel tag := allPowers.quantumLabel tag.exponent
  quantumLabel_unit := allPowers.quantumLabel_zero.trans finitePowers.quantumLabel_unit
  quantumLabel_curvatureSquared :=
    allPowers.quantumLabel_one.trans finitePowers.quantumLabel_curvatureSquared

@[simp] theorem finiteRestriction_classicalObservable
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (tag : ScalarCurvaturePowerTag) :
    (allPowers.finiteRestriction).classicalObservable tag =
      finitePowers.classicalObservable tag := by
  funext b
  cases tag <;> simp [finiteRestriction, ScalarCurvaturePowerTag.exponent,
    finitePowers.classicalObservable_eq, classicalScalarCurvaturePowerObservable]

@[simp] theorem finiteRestriction_quantumLabel
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)
    (tag : ScalarCurvaturePowerTag) :
    (allPowers.finiteRestriction).quantumLabel tag = finitePowers.quantumLabel tag := by
  cases tag
  · exact allPowers.quantumLabel_zero
  · exact allPowers.quantumLabel_one
  · exact allPowers.quantumLabel_two

/-- Restricting back to the three old exponents recovers the exact original finite record. -/
theorem finiteRestriction_eq
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers) :
    allPowers.finiteRestriction = finitePowers := by
  rw [ScalarCurvaturePowerLocalObservableInterpretationData.mk.injEq]
  constructor
  · funext tag
    exact allPowers.finiteRestriction_classicalObservable tag
  · funext tag
    exact allPowers.finiteRestriction_quantumLabel tag

@[simp] theorem quantumLabel_zero_eq_unit
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers) :
    allPowers.quantumLabel 0 = family.unitLabel :=
  allPowers.quantumLabel_zero.trans finitePowers.quantumLabel_unit

@[simp] theorem quantumLabel_one_eq_curvatureSquared
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers) :
    allPowers.quantumLabel 1 = basic.quantumLabel .curvatureSquared :=
  allPowers.quantumLabel_one.trans finitePowers.quantumLabel_curvatureSquared

end ScalarCurvatureAllPowersLocalObservableInterpretationData

@[simp] theorem classicalScalarCurvatureAllPowersObservable_zero
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) (b : B) :
    classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate 0 b =
      1 := by
  simp [classicalScalarCurvatureAllPowersObservable]

@[simp] theorem classicalScalarCurvatureAllPowersObservable_one
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) (b : B) :
    classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate 1 b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  simp [classicalScalarCurvatureAllPowersObservable]

@[simp] theorem classicalScalarCurvatureAllPowersObservable_two
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) (b : B) :
    classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate 2 b =
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ 2 := by
  rfl

@[simp] theorem classicalScalarCurvatureAllPowersObservable_succ
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior) (n : ℕ) (b : B) :
    classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate
        (n + 1) b =
      classicalScalarCurvatureAllPowersObservable geometry inner connection exterior certificate n b *
        geometry.canonicalCurvatureDensity inner connection exterior certificate b := by
  simp [classicalScalarCurvatureAllPowersObservable, pow_succ]

end

end YangMills.Observables
