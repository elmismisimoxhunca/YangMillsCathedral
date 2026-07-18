/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.JointTranslationSpectrum

/-!
# Supremum semantics for the physical mass gap

Clay/Jaffe–Witten p. 6 defines the mass `m` as the supremum of positive Hamiltonian intervals
without spectrum and requires `m < ∞`. This module forms that supremum from the exact source-facing
same-PVM Hamiltonian condition. Any one stronger physical joint gap separately supplies a nonzero
bounded-energy excitation band; that fixed band bounds every source-facing threshold, so the
supremum is a positive finite real rather than the vacuum-only value `+∞`.

No admissible threshold, spectral datum, Yang–Mills theory, or mass gap is constructed.
-/

namespace YangMills.Minkowski

/-- Clay's source-facing Hamiltonian gap condition for one positive threshold.

The exact zero-momentum projection remains the selected vacuum line, while admissibility itself is
absence of Hamiltonian spectrum in `(0, Δ)`. The bounded-excitation guard is deliberately not part
of membership; it is used separately to prove the supremum finite. -/
def IsClayHamiltonianGapThreshold
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U)
    (Δ : ℝ) : Prop :=
  0 < Δ ∧
  (∀ ψ : H, spectrum.joint.pvm.projection ({0} : Set (Spacetime d)) ψ =
    inner ℂ vacuumData.vacuum ψ • vacuumData.vacuum) ∧
  physicalHamiltonianSpectralProjection spectrum (Set.Ioo 0 Δ) = 0

/-- The stronger invariant-mass predicate implies Clay's exact Hamiltonian threshold condition. -/
theorem isClayHamiltonianGapThreshold_of_hasPhysicalJointSpectralMassGap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    IsClayHamiltonianGapThreshold vacuumData spectrum Δ :=
  ⟨hgap.1, hgap.2.1, hgap.hamiltonian_Ioo_projection_zero⟩

/-- All source-facing admissible Hamiltonian gap thresholds for one exact vacuum and physical joint
PVM. -/
def physicalGapThresholdSet
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U) : Set ℝ :=
  {Δ | IsClayHamiltonianGapThreshold vacuumData spectrum Δ}

/-- Clay's mass value as the supremum of all admissible thresholds. -/
noncomputable def physicalMassGapValue
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U) : ℝ :=
  sSup (physicalGapThresholdSet vacuumData spectrum)

/-- One admissible threshold makes the threshold set nonempty. -/
theorem physicalGapThresholdSet_nonempty
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    (physicalGapThresholdSet vacuumData spectrum).Nonempty :=
  ⟨Δ, isClayHamiltonianGapThreshold_of_hasPhysicalJointSpectralMassGap hgap⟩

/-- The bounded positive-energy band from one gap bounds every admissible threshold. -/
theorem physicalGapThresholdSet_bddAbove
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ₀ : ℝ} (hgap₀ : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ₀) :
    BddAbove (physicalGapThresholdSet vacuumData spectrum) := by
  rcases hgap₀.2.2.2 with ⟨E, hE, _, hExcitation⟩
  refine ⟨E, ?_⟩
  intro Δ hΔ
  change IsClayHamiltonianGapThreshold vacuumData spectrum Δ at hΔ
  by_contra hnot
  have hEΔ : E < Δ := lt_of_not_ge hnot
  apply hExcitation
  apply spectrum.joint.pvm.projection_eq_zero_of_subset
    (measurableSet_boundedPositiveEnergyExcitationRegion d E)
    (measurableSet_positiveEnergySubgapRegion d Δ)
  · intro p hp
    exact ⟨hp.1, hp.2.1, lt_of_le_of_lt hp.2.2 hEΔ⟩
  · have hset : positiveEnergySubgapRegion d Δ =
        closedForwardMomentumCone d ∩
          (fun p : Spacetime d => p d.timeIndex) ⁻¹' Set.Ioo 0 Δ := by
      ext p
      rfl
    rw [hset]
    exact hΔ.2.2

/-- Every admissible threshold is at most the Clay supremum. -/
theorem le_physicalMassGapValue
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ Δ₀ : ℝ}
    (hthreshold : IsClayHamiltonianGapThreshold vacuumData spectrum Δ)
    (hgap₀ : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ₀) :
    Δ ≤ physicalMassGapValue vacuumData spectrum := by
  apply le_csSup (physicalGapThresholdSet_bddAbove hgap₀)
  exact hthreshold

/-- One admissible gap proves that the supremum mass is a strictly positive finite real. -/
theorem physicalMassGapValue_pos
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    0 < physicalMassGapValue vacuumData spectrum := by
  have hthreshold :=
    isClayHamiltonianGapThreshold_of_hasPhysicalJointSpectralMassGap hgap
  have hle := le_physicalMassGapValue hthreshold hgap
  exact lt_of_lt_of_le hgap.1 hle

/-- Source-facing finite-positive supremum semantics, still without an existence assertion. -/
def HasFinitePositivePhysicalMassGap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U) : Prop :=
  (physicalGapThresholdSet vacuumData spectrum).Nonempty ∧
  BddAbove (physicalGapThresholdSet vacuumData spectrum) ∧
  0 < physicalMassGapValue vacuumData spectrum

/-- Any selected physical gap yields the full finite-positive supremum semantics. -/
theorem hasFinitePositivePhysicalMassGap_of_hasPhysicalJointSpectralMassGap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    HasFinitePositivePhysicalMassGap vacuumData spectrum :=
  ⟨physicalGapThresholdSet_nonempty hgap,
    physicalGapThresholdSet_bddAbove hgap,
    physicalMassGapValue_pos hgap⟩

end YangMills.Minkowski
