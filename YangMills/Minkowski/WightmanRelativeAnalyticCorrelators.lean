/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubePolynomialGrowth
import YangMills.Mathematics.ConsecutiveDifferenceCoordinates

/-!
# Relative-coordinate analytic Wightman correlators

Streater–Wightman printed pp. 108 and 114 first factors translation-invariant full correlators
through consecutive differences, then identifies the relative tempered distribution as the boundary
value of a polynomially bounded tube-holomorphic function.

This interface makes that chain explicit. A normalized anchor Schwartz test integrates out the
common translation coordinate; coherence is required for every normalized anchor, not merely one
selected witness. The anchor integral uses coordinate Lebesgue/Haar volume and is not called a
Riemannian volume. No correlator, anchor, analytic function, or theory is constructed.
-/

namespace YangMills.Minkowski

open MeasureTheory
open scoped SchwartzMap

/-- Full-product correlators, relative-coordinate tempered distributions, and their exact analytic
boundary data on one connected chain. -/
structure ScalarWightmanRelativeAnalyticCorrelatorData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (full : ScalarWightmanJointTemperedCorrelatorData fieldData) where
  /-- A concrete anchor test prevents the normalization domain from being empty. -/
  normalizationAnchor : ScalarMinkowskiSchwartzTestFunction d
  /-- Exact coordinate-Lebesgue normalization of the selected anchor. -/
  normalizationAnchor_integral_one : ∫ x, normalizationAnchor x = 1
  /-- One relative-coordinate tempered distribution at every difference arity. -/
  relativeDistribution : ∀ n : ℕ,
    TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ
  /-- Full and relative distributions agree after lifting with every normalized anchor test. -/
  full_relative_coherent : ∀ (n : ℕ)
    (relative : ScalarMinkowskiNPointSchwartzTestFunction d n)
    (anchor : ScalarMinkowskiSchwartzTestFunction d),
    (∫ x, anchor x) = 1 →
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor) =
      relativeDistribution n relative
  /-- The exact relative distribution is the polynomially bounded tube boundary at every arity. -/
  analyticBoundary : ∀ n : ℕ,
    PolynomiallyBoundedWightmanTubeBoundaryValueData d n (relativeDistribution n)

/-- Coherence for the selected nonvacuous normalization anchor. -/
theorem ScalarWightmanRelativeAnalyticCorrelatorData.selectedAnchor_coherent
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
    (data : ScalarWightmanRelativeAnalyticCorrelatorData full)
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n) :
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d)
        relative data.normalizationAnchor) =
      data.relativeDistribution n relative :=
  data.full_relative_coherent n relative data.normalizationAnchor
    data.normalizationAnchor_integral_one

/-- Any two normalized anchors give the same full-distribution value because both equal the exact
relative distribution. -/
theorem ScalarWightmanRelativeAnalyticCorrelatorData.normalizedAnchor_independent
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
    (data : ScalarWightmanRelativeAnalyticCorrelatorData full)
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n)
    (anchor₁ anchor₂ : ScalarMinkowskiSchwartzTestFunction d)
    (h₁ : (∫ x, anchor₁ x) = 1) (h₂ : (∫ x, anchor₂ x) = 1) :
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor₁) =
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor₂) := by
  rw [data.full_relative_coherent n relative anchor₁ h₁,
    data.full_relative_coherent n relative anchor₂ h₂]

end YangMills.Minkowski
