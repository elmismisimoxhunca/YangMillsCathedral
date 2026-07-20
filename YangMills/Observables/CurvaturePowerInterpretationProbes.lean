/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvaturePowerInterpretation

/-!
# Hostile probes for the finite scalar curvature-power fragment

The probes force all three tags to use the exact same classical curvature chain and local family.
Quartic anti-collapse is tested separately as an explicit strengthening. No interpretation is
constructed.
-/

namespace YangMills.Observables.CurvaturePowerInterpretation.Probes

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
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)

/-- The exposed classical carrier is exactly the finite canonical fragment, not unrelated data. -/
theorem exact_classical_fragment :
    powers.classicalObservable =
      classicalScalarCurvaturePowerObservable
        geometry inner connection exterior certificate :=
  powers.classicalObservable_eq

/-- Unit and curvature-squared labels reuse the exact existing labels. -/
theorem exact_old_labels :
    powers.quantumLabel .unit = family.unitLabel ∧
      powers.quantumLabel .curvatureSquared = basic.quantumLabel .curvatureSquared :=
  ⟨powers.quantumLabel_unit, powers.quantumLabel_curvatureSquared⟩

/-- A substituted classical quartic function is rejected by exact carrier coherence. -/
theorem unrelated_quartic_classicalMeaning_blocked
    (wrong : B → ℝ)
    (claimed : powers.classicalObservable .curvatureQuartic = wrong) :
    wrong = fun b =>
      geometry.canonicalCurvatureDensity inner connection exterior certificate b ^ 2 := by
  funext b
  rw [← claimed, powers.classicalObservable_eq]
  rfl

/-- Optional quartic anti-collapse rejects unit/`F²` collapse and zero operator action. -/
theorem exact_quartic_antiCollapse
    (antiCollapse : CurvatureQuarticAntiCollapseData powers) :
    powers.quantumLabel .curvatureQuartic ≠ family.unitLabel ∧
      powers.quantumLabel .curvatureQuartic ≠ basic.quantumLabel .curvatureSquared ∧
      ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
        family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠ 0 ∧
        family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠
          family.operator family.unitLabel f ψ ∧
        family.operator (powers.quantumLabel .curvatureQuartic) f ψ ≠
          family.operator (basic.quantumLabel .curvatureSquared) f ψ :=
  ⟨antiCollapse.curvatureQuarticLabel_ne_unit,
    antiCollapse.curvatureQuarticLabel_ne_curvatureSquared,
    antiCollapse.curvatureQuartic_nontrivial⟩

end

end YangMills.Observables.CurvaturePowerInterpretation.Probes
