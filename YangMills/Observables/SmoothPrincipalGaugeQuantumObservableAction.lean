/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothGaugeTransformation
import YangMills.Observables.QuantumGaugeObservableAction

/-!
# Quantum observable action of the canonical smooth principal gauge group

This module specializes the independent algebraic quantum gauge-action interface to the exact group
of smooth automorphisms of one fixed principal bundle. It constructs neither a representation nor
an invariance certificate and asserts no classical/quantum transformation-law theorem.
-/

namespace YangMills.Observables

open YangMills.Minkowski
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

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
    {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    (smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle)
    {d : EuclideanDimension} {PoincareGroup : Type*}
    [Group PoincareGroup] [TopologicalSpace PoincareGroup] [IsTopologicalGroup PoincareGroup]
    {lift : ProperOrthochronousPoincareLiftData d PoincareGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D)

/-- The independent action interface with gauge group fixed to smooth automorphisms of one exact
principal bundle. -/
abbrev SmoothPrincipalGaugeQuantumObservableActionData :=
  QuantumGaugeObservableActionData (Geometry.SmoothGaugeTransformation smoothBundle) family

/-- All-label invariance under one exact designated action of the canonical smooth gauge group. -/
abbrev SmoothPrincipalGaugeInvariantQuantumObservableFamilyData
    (action : SmoothPrincipalGaugeQuantumObservableActionData smoothBundle family) :=
  GaugeInvariantQuantumObservableFamilyData action

end YangMills.Observables
