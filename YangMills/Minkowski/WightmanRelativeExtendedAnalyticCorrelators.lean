/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanExtendedTubeContinuation
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators

/-!
# Relative Wightman correlators on extended tubes

This module attaches extended-tube continuation at every arity to the exact relative tempered
distributions, ordinary tube boundaries, full correlators, field, common domain, vacuum, and
physical representation already selected by `ScalarWightmanRelativeAnalyticCorrelatorData`.

No continuation or correlator datum is constructed.
-/

namespace YangMills.Minkowski

/-- All-arity scalar extended-tube continuations on one exact relative Wightman correlator chain. -/
structure ScalarWightmanRelativeExtendedAnalyticCorrelatorData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    (relative : ScalarWightmanRelativeAnalyticCorrelatorData full) where
  /-- At every arity, continue exactly the ordinary analytic boundary already indexed by the exact
  relative tempered distribution. -/
  extendedContinuation : ∀ n : ℕ,
    PolynomiallyBoundedWightmanExtendedTubeContinuationData d n
      (relative.analyticBoundary n)

/-- Restriction at every arity is the same tube function whose boundary is the exact relative
correlator distribution. -/
theorem ScalarWightmanRelativeExtendedAnalyticCorrelatorData.restricts_to_relativeBoundary
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    {relative : ScalarWightmanRelativeAnalyticCorrelatorData full}
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) (z : Fin n → ComplexifiedSpacetime d)
    (hz : z ∈ wightmanBackwardTube d n) :
    (data.extendedContinuation n).extendedFunction z =
      (relative.analyticBoundary n).tubeFunction z :=
  (data.extendedContinuation n).restricts_to_ordinary z hz

end YangMills.Minkowski
