/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteGibbsMeasure

/-!
# Hostile probes for finite lattice Gibbs data

These probes reject zero reference/Gibbs measures, zero or infinite partition functions, vanishing
Boltzmann density, and nonintegrable-observable shortcuts. They construct no Haar or Gibbs datum.
-/

namespace YangMills.Lattice.FiniteGibbsMeasure.Probes

open MeasureTheory

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}

/-- The exact identity configuration has Boltzmann weight one, not zero. -/
@[simp] theorem identity_boltzmann_weight :
    latticeBoltzmannWeight potential coupling
      (fun _ : PositiveOrientedLink d Λ => (1 : G)) = 1 := by
  simp [latticeBoltzmannWeight]

/-- No finite gauge field can acquire zero Boltzmann density. -/
theorem zero_density_blocked (U : GaugeField d Λ G) :
    latticeBoltzmannWeight potential coupling U ≠ 0 :=
  ne_of_gt (latticeBoltzmannWeight_pos potential coupling U)

/-- The density itself is invariant because it uses the exact gauge-invariant action. -/
theorem exact_boltzmann_gauge_invariance
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G) :
    latticeBoltzmannWeight potential coupling (gaugeTransform g U) =
      latticeBoltzmannWeight potential coupling U :=
  latticeBoltzmannWeight_gaugeInvariant potential coupling g U

variable [MeasurableSpace G]

/-- Probability normalization rejects the zero reference measure. -/
theorem zero_reference_measure_blocked
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    gibbs.referenceMeasure ≠ 0 := by
  intro hzero
  have h := gibbs.reference_probability
  rw [hzero] at h
  simp at h

/-- The accepted reference gauge action is explicitly measurable. -/
theorem exact_gauge_action_measurability
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measurable (gaugeTransform g : GaugeField d Λ G → GaugeField d Λ G) :=
  gibbs.gaugeTransform_measurable g

/-- Boltzmann measurability is an exact acceptance obligation, not a default-zero convention. -/
theorem exact_boltzmann_measurability
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    Measurable (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling) :=
  gibbs.boltzmann_measurable

/-- The reference measure must be invariant under the same exact gauge action. -/
theorem exact_reference_gauge_invariance
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g) gibbs.referenceMeasure = gibbs.referenceMeasure :=
  gibbs.reference_gaugeInvariant g

/-- Strict positivity rejects a zero partition function. -/
theorem zero_partition_blocked
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    latticePartitionFunction potential coupling gibbs.referenceMeasure ≠ 0 :=
  ne_of_gt gibbs.partition_pos

/-- Finiteness separately rejects an infinite partition function. -/
theorem infinite_partition_blocked
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    latticePartitionFunction potential coupling gibbs.referenceMeasure ≠ ⊤ :=
  gibbs.partition_ne_top

/-- Probability normalization rejects the zero normalized Gibbs measure. -/
theorem zero_gibbs_measure_blocked
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure ≠ 0 := by
  intro hzero
  have h := gibbs.gibbs_probability
  rw [hzero] at h
  simp at h

/-- The normalized Gibbs measure must remain invariant on the same reference/action chain. -/
theorem exact_gibbs_gauge_invariance
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g)
      (normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure) =
      normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure :=
  gibbs.gibbs_gaugeInvariant g

/-- Every accepted observable carries enough evidence to avoid Bochner's nonintegrable-zero case. -/
theorem observable_integrability_is_required
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (observable : @FiniteLatticeObservable d Λ G _ _) :
    Integrable observable
      (normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure) :=
  observable.integrable gibbs

end YangMills.Lattice.FiniteGibbsMeasure.Probes
