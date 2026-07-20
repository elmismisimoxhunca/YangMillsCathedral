/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.FiniteCovariantObservableMultiplet

/-!
# Adjoint partners of finite covariant observable multiplets

Streater–Wightman axioms I–II require exact field adjoints on the common domain and one
finite-dimensional transformation law. Taking an adjoint conjugates the finite mixing
coefficients. This module records the exact partner relation between two already supplied
lift-covariant multiplets in the same observable family.

The relation reuses the family's involutive adjoint label, gives an exact equivalence of component
indices, and requires coefficientwise complex-conjugate mixing. It constructs no field,
representation, multiplet, or theory.
-/

namespace YangMills.Minkowski

/-- Exact adjoint/conjugate-representation partner relation between two finite multiplets in the
same local-observable family. -/
structure FiniteLiftCovariantObservableMultipletAdjointPartnerData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (covariance : CovariantLocalObservableFamilyData family)
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (first : FiniteLiftCovariantObservableMultipletData family ι)
    (second : FiniteLiftCovariantObservableMultipletData family κ) where
  /-- Exact correspondence between the two finite component carriers. -/
  indexEquiv : ι ≃ κ
  /-- The corresponding second component is the existing family adjoint of the first. -/
  componentLabel_adjoint : ∀ i,
    second.componentLabel (indexEquiv i) = covariance.adjointLabel (first.componentLabel i)
  /-- The partner's matrix coefficient is the complex conjugate of the original coefficient. -/
  mixing_coefficient_conj : ∀ g i j,
    second.mixingRepresentation g (Pi.single (indexEquiv i) 1) (indexEquiv j) =
      starRingEnd ℂ (first.mixingRepresentation g (Pi.single i 1) j)

/-- Involutivity of the existing family adjoint recovers the original component label from its
partner; no reverse relation is stored independently. -/
theorem FiniteLiftCovariantObservableMultipletAdjointPartnerData.componentLabel_adjoint_back
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    {covariance : CovariantLocalObservableFamilyData family}
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {first : FiniteLiftCovariantObservableMultipletData family ι}
    {second : FiniteLiftCovariantObservableMultipletData family κ}
    (partner : FiniteLiftCovariantObservableMultipletAdjointPartnerData
      covariance first second)
    (i : ι) :
    covariance.adjointLabel (second.componentLabel (partner.indexEquiv i)) =
      first.componentLabel i := by
  rw [partner.componentLabel_adjoint, covariance.adjointLabel_adjointLabel]

end YangMills.Minkowski
