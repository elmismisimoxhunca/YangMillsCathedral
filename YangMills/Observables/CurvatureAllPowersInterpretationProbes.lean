/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvatureAllPowersInterpretation

/-!
# Hostile probes for all natural curvature-density powers

The probes lock every classical power to the exact same descended curvature chain and lock indices
`0`, `1`, and `2` to the existing finite labels. No injectivity or all-power anti-collapse is
assumed.
-/

namespace YangMills.Observables.CurvatureAllPowersInterpretation.Probes

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
    (allPowers : ScalarCurvatureAllPowersLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic finitePowers)

/-- The exposed classical carrier is the exact natural-power family. -/
theorem exact_classical_all_powers :
    allPowers.classicalObservable =
      classicalScalarCurvatureAllPowersObservable
        geometry inner connection exterior certificate :=
  allPowers.classicalObservable_eq

/-- Indices zero, one, and two are the exact existing finite labels. -/
theorem exact_zero_one_two_labels :
    allPowers.quantumLabel 0 = finitePowers.quantumLabel .unit ∧
      allPowers.quantumLabel 1 = finitePowers.quantumLabel .curvatureSquared ∧
      allPowers.quantumLabel 2 = finitePowers.quantumLabel .curvatureQuartic :=
  ⟨allPowers.quantumLabel_zero, allPowers.quantumLabel_one,
    allPowers.quantumLabel_two⟩

/-- A substituted classical value at any power is forced back to the exact canonical density. -/
theorem unrelated_higher_power_blocked
    (n : ℕ) (b : B) (wrong : ℝ)
    (claimed : allPowers.classicalObservable n b = wrong) :
    wrong = geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ n := by
  rw [← claimed]
  exact allPowers.classicalObservable_apply n b

/-- Restriction to exponents zero, one, and two recovers the original finite interpretation. -/
theorem finite_restriction_exact :
    allPowers.finiteRestriction = finitePowers :=
  allPowers.finiteRestriction_eq

/-- The existing quartic anti-collapse witness transfers exactly to all-power index two. -/
theorem quartic_antiCollapse_transfers
    (antiCollapse : CurvatureQuarticAntiCollapseData finitePowers) :
    allPowers.quantumLabel 2 ≠ family.unitLabel ∧
      allPowers.quantumLabel 2 ≠ basic.quantumLabel .curvatureSquared ∧
      ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
        family.operator (allPowers.quantumLabel 2) f ψ ≠ 0 ∧
        family.operator (allPowers.quantumLabel 2) f ψ ≠
          family.operator family.unitLabel f ψ ∧
        family.operator (allPowers.quantumLabel 2) f ψ ≠
          family.operator (basic.quantumLabel .curvatureSquared) f ψ := by
  rw [allPowers.quantumLabel_two]
  exact ⟨antiCollapse.curvatureQuarticLabel_ne_unit,
    antiCollapse.curvatureQuarticLabel_ne_curvatureSquared,
    antiCollapse.curvatureQuartic_nontrivial⟩

/-- The zero and one labels also reduce to the original basic unit and `F²` labels. -/
theorem exact_basic_labels :
    allPowers.quantumLabel 0 = family.unitLabel ∧
      allPowers.quantumLabel 1 = basic.quantumLabel .curvatureSquared :=
  ⟨allPowers.quantumLabel_zero_eq_unit,
    allPowers.quantumLabel_one_eq_curvatureSquared⟩

end

end YangMills.Observables.CurvatureAllPowersInterpretation.Probes
