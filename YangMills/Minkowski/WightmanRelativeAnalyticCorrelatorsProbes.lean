/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators

/-!
# Hostile probes for relative analytic Wightman correlators

The probes expose nonvacuous anchor normalization, exact full/relative coherence, anchor
independence, and use of the exact relative distribution as the analytic boundary. No datum is
constructed.
-/

namespace YangMills.Minkowski.WightmanRelativeAnalyticCorrelators.Probes

variable
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

/-- The selected anchor has exact coordinate-Lebesgue integral one. -/
theorem exact_anchor_normalization :
    (∫ x, data.normalizationAnchor x) = 1 :=
  data.normalizationAnchor_integral_one

/-- Anchor normalization blocks the zero test. -/
theorem normalization_anchor_ne_zero : data.normalizationAnchor ≠ 0 := by
  intro hzero
  have hone := data.normalizationAnchor_integral_one
  rw [hzero] at hone
  simp at hone

/-- Every relative arity is an actual tempered distribution. -/
def exact_relative_distribution (n : ℕ) :
    TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ :=
  data.relativeDistribution n

/-- The selected nonzero normalized anchor gives exact full/relative coherence. -/
theorem exact_selected_anchor_coherence
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n) :
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d)
        relative data.normalizationAnchor) =
      data.relativeDistribution n relative :=
  data.selectedAnchor_coherent n relative

/-- Coherence is required for every normalized anchor, not just the selected witness. -/
theorem exact_all_normalized_anchor_coherence
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n)
    (anchor : ScalarMinkowskiSchwartzTestFunction d)
    (hanchor : (∫ x, anchor x) = 1) :
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor) =
      data.relativeDistribution n relative :=
  data.full_relative_coherent n relative anchor hanchor

/-- Two normalized anchors cannot produce different full-correlator values. -/
theorem exact_normalized_anchor_independence
    (S : ScalarWightmanRelativeAnalyticCorrelatorData full)
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n)
    (anchor₁ anchor₂ : ScalarMinkowskiSchwartzTestFunction d)
    (h₁ : (∫ x, anchor₁ x) = 1) (h₂ : (∫ x, anchor₂ x) = 1) :
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor₁) =
    full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d) relative anchor₂) :=
  ScalarWightmanRelativeAnalyticCorrelatorData.normalizedAnchor_independent
    S n relative anchor₁ anchor₂ h₁ h₂

/-- The analytic boundary is indexed by the exact relative distribution, not a surrogate. -/
def exact_relative_analytic_boundary (n : ℕ) :
    PolynomiallyBoundedWightmanTubeBoundaryValueData d n
      (data.relativeDistribution n) :=
  data.analyticBoundary n

/-- The exact relative distribution is the all-direction weak boundary limit. -/
theorem exact_relative_boundary_limit (n : ℕ) :
    Filter.Tendsto (data.analyticBoundary n).boundaryApproximation
      (nhdsWithin 0 (wightmanForwardDirectionSet d n))
      (nhds (data.relativeDistribution n)) :=
  (data.analyticBoundary n).boundary_tendsto

/-- A disconnected proposed relative value is rejected by exact full/relative coherence. -/
theorem disconnected_relative_value_blocked
    (n : ℕ) (relative : ScalarMinkowskiNPointSchwartzTestFunction d n) (z : ℂ)
    (hmismatch : z ≠ full.nPointDistribution (n + 1)
      (Mathematics.relativeAnchorSchwartzLift (Spacetime d)
        relative data.normalizationAnchor)) :
    data.relativeDistribution n relative ≠ z := by
  rw [← data.selectedAnchor_coherent n relative]
  exact fun h => hmismatch h.symm

end YangMills.Minkowski.WightmanRelativeAnalyticCorrelators.Probes
