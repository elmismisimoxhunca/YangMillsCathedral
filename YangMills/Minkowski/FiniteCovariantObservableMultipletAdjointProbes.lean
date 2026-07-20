/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.FiniteCovariantObservableMultipletAdjoint

/-!
# Hostile probes for finite-multiplet adjoint partners

The probes expose exact family-label reuse, derived reverse adjoint coherence, and coefficientwise
conjugate mixing. No partner datum is constructed.
-/

namespace YangMills.Minkowski.FiniteCovariantObservableMultipletAdjoint.Probes

variable
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

/-- Partner components are exact existing family adjoint labels, not copied fields. -/
theorem exact_adjoint_partner_label
    (partner : FiniteLiftCovariantObservableMultipletAdjointPartnerData
      covariance first second)
    (i : ι) :
    second.componentLabel (partner.indexEquiv i) =
      covariance.adjointLabel (first.componentLabel i) :=
  partner.componentLabel_adjoint i

/-- The reverse label relation follows from the same involutive family adjoint. -/
theorem exact_adjoint_partner_back
    (partner : FiniteLiftCovariantObservableMultipletAdjointPartnerData
      covariance first second)
    (i : ι) :
    covariance.adjointLabel (second.componentLabel (partner.indexEquiv i)) =
      first.componentLabel i :=
  partner.componentLabel_adjoint_back i

/-- An unrelated partner representation cannot replace coefficientwise complex conjugation. -/
theorem exact_conjugate_mixing_coefficient
    (partner : FiniteLiftCovariantObservableMultipletAdjointPartnerData
      covariance first second)
    (g : G) (i j : ι) :
    second.mixingRepresentation g (Pi.single (partner.indexEquiv i) 1)
        (partner.indexEquiv j) =
      starRingEnd ℂ (first.mixingRepresentation g (Pi.single i 1) j) :=
  partner.mixing_coefficient_conj g i j

end YangMills.Minkowski.FiniteCovariantObservableMultipletAdjoint.Probes
