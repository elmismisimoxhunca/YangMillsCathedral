/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PhysicalMassGapSupremum

/-!
# Hostile probes for physical mass-gap supremum semantics

The probes lock set membership to the exact same-PVM gap predicate and expose nonemptiness,
uniform boundedness, positivity, and rejection of an unrelated proposed supremum. They assume an
admissible gap; none is constructed.
-/

namespace YangMills.Minkowski.PhysicalMassGapSupremum.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}

/-- Membership in the threshold set is definitionally the exact physical same-PVM predicate. -/
theorem exact_threshold_membership (Δ : ℝ) :
    Δ ∈ physicalGapThresholdSet vacuumData spectrum ↔
      IsClayHamiltonianGapThreshold vacuumData spectrum Δ :=
  Iff.rfl

/-- One selected gap makes the exact threshold set nonempty. -/
theorem exact_threshold_set_nonempty
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    (physicalGapThresholdSet vacuumData spectrum).Nonempty :=
  physicalGapThresholdSet_nonempty hgap

/-- Its bounded excitation band uniformly bounds every exact admissible threshold. -/
theorem exact_threshold_set_bddAbove
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    BddAbove (physicalGapThresholdSet vacuumData spectrum) :=
  physicalGapThresholdSet_bddAbove hgap

/-- Every exact admissible threshold lies below the exact supremum mass. -/
theorem exact_threshold_le_mass
    {Δ Δ₀ : ℝ}
    (hthreshold : IsClayHamiltonianGapThreshold vacuumData spectrum Δ)
    (hgap₀ : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ₀) :
    Δ ≤ physicalMassGapValue vacuumData spectrum :=
  le_physicalMassGapValue hthreshold hgap₀

/-- One exact gap forces the exact supremum mass to be positive. -/
theorem exact_mass_positive
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    0 < physicalMassGapValue vacuumData spectrum :=
  physicalMassGapValue_pos hgap

/-- One exact gap yields the complete nonempty, bounded-above, positive-supremum semantics. -/
theorem exact_finite_positive_mass_semantics
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    HasFinitePositivePhysicalMassGap vacuumData spectrum :=
  hasFinitePositivePhysicalMassGap_of_hasPhysicalJointSpectralMassGap hgap

/-- The mass value is locked to the supremum of the exact source-facing threshold set. -/
theorem exact_mass_is_sSup :
    physicalMassGapValue vacuumData spectrum =
      sSup (physicalGapThresholdSet vacuumData spectrum) :=
  rfl

/-- A vacuum-only spectrum with the correct vacuum line admits every positive Hamiltonian interval,
so its source-facing threshold set is unbounded rather than artificially empty. -/
theorem vacuum_only_threshold_set_not_bddAbove
    (hZeroLine : ∀ ψ : H,
      spectrum.joint.pvm.projection ({0} : Set (Spacetime d)) ψ =
        inner ℂ vacuumData.vacuum ψ • vacuumData.vacuum)
    (hVacuumOnly : spectrum.joint.pvm.projection
      (({0} : Set (Spacetime d))ᶜ) = 0) :
    ¬ BddAbove (physicalGapThresholdSet vacuumData spectrum) := by
  intro hb
  rcases hb with ⟨B, hB⟩
  let Δ : ℝ := max 1 (B + 1)
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one (le_max_left 1 (B + 1))
  have hHamiltonianZero :
      physicalHamiltonianSpectralProjection spectrum (Set.Ioo 0 Δ) = 0 := by
    rw [physicalHamiltonianSpectralProjection]
    apply spectrum.joint.pvm.projection_eq_zero_of_subset
      ((isClosed_closedForwardMomentumCone d).measurableSet.inter
        ((measurableSet_Ioo.preimage (measurable_pi_apply d.timeIndex))))
      (measurableSet_singleton (0 : Spacetime d)).compl
    · intro p hp hpZero
      subst p
      simpa using hp.2.1
    · exact hVacuumOnly
  have hmem : Δ ∈ physicalGapThresholdSet vacuumData spectrum :=
    ⟨hΔpos, hZeroLine, hHamiltonianZero⟩
  have hle := hB hmem
  have hBlt : B < Δ := lt_of_lt_of_le (lt_add_one B) (le_max_right 1 (B + 1))
  exact (not_lt_of_ge hle) hBlt

end YangMills.Minkowski.PhysicalMassGapSupremum.Probes
