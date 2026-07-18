/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FinitePeriodicGaugeField
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-cutoff lattice Gibbs measure interface

Osterwalder–Seiler 1978, pp. 442–443, defines the finite lattice Gibbs measure from product Haar
measure and the exponential of the lattice action. This module packages the exact normalized
measure semantics while leaving compact-group Haar construction as an explicit input obligation.

The partition function must be strictly positive and finite, and the normalized Gibbs measure must
have total mass one. Measurability and local gauge invariance are explicit; no nonmeasurable-zero or
infinite-normalization shortcut is accepted. No Haar measure, Gibbs datum, expectation value,
reflection positivity, continuum limit, or physical theory is constructed.
-/

namespace YangMills.Lattice

open MeasureTheory

/-- Positive Boltzmann density of the exact finite Wilson-type action. -/
noncomputable def latticeBoltzmannWeight
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField d Λ G) : ENNReal :=
  ENNReal.ofReal (Real.exp (-wilsonTypeLatticeAction Λ potential coupling U))

/-- The Boltzmann density is strictly positive at every finite gauge field. -/
theorem latticeBoltzmannWeight_pos
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField d Λ G) :
    0 < latticeBoltzmannWeight potential coupling U := by
  rw [latticeBoltzmannWeight, ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- The exact Boltzmann density inherits local gauge invariance from the same lattice action. -/
theorem latticeBoltzmannWeight_gaugeInvariant
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G) :
    latticeBoltzmannWeight potential coupling (gaugeTransform g U) =
      latticeBoltzmannWeight potential coupling U := by
  simp [latticeBoltzmannWeight, wilsonTypeLatticeAction_gaugeInvariant]

/-- Partition function relative to a supplied finite-cutoff reference measure. -/
noncomputable def latticePartitionFunction
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G)) : ENNReal :=
  ∫⁻ U, latticeBoltzmannWeight potential coupling U ∂reference

/-- Normalized Gibbs measure obtained from the exact partition function and Boltzmann density. -/
noncomputable def normalizedLatticeGibbsMeasure
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G)) : Measure (GaugeField d Λ G) :=
  (latticePartitionFunction potential coupling reference)⁻¹ •
    reference.withDensity (latticeBoltzmannWeight potential coupling)

/-- Exact finite-cutoff Gibbs data based on a normalized gauge-invariant reference measure.

For compact groups the intended reference is finite product Haar measure, but that construction is
not silently postulated here. -/
structure FiniteLatticeGibbsMeasureData
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) where
  /-- Intended finite product Haar reference measure. -/
  referenceMeasure : Measure (GaugeField d Λ G)
  /-- Exact reference probability normalization. -/
  reference_probability : referenceMeasure Set.univ = 1
  /-- Every local gauge action is measurable on configuration space. -/
  gaugeTransform_measurable : ∀ g : GaugeTransformation d Λ G,
    Measurable (gaugeTransform g : GaugeField d Λ G → GaugeField d Λ G)
  /-- The reference measure is exactly invariant under every local gauge transformation. -/
  reference_gaugeInvariant : ∀ g : GaugeTransformation d Λ G,
    Measure.map (gaugeTransform g) referenceMeasure = referenceMeasure
  /-- Exact action/Boltzmann measurability. -/
  boltzmann_measurable : Measurable
    (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling)
  /-- The partition function cannot vanish. -/
  partition_pos : 0 < latticePartitionFunction potential coupling referenceMeasure
  /-- The partition function cannot be infinite. -/
  partition_ne_top : latticePartitionFunction potential coupling referenceMeasure ≠ ⊤
  /-- Exact Gibbs probability normalization. -/
  gibbs_probability :
    normalizedLatticeGibbsMeasure potential coupling referenceMeasure Set.univ = 1
  /-- The normalized Gibbs measure retains local gauge invariance. -/
  gibbs_gaugeInvariant : ∀ g : GaugeTransformation d Λ G,
    Measure.map (gaugeTransform g)
      (normalizedLatticeGibbsMeasure potential coupling referenceMeasure) =
      normalizedLatticeGibbsMeasure potential coupling referenceMeasure

/-- Bounded measurable complex observable on one finite gauge-field configuration space. -/
structure FiniteLatticeObservable
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [MeasurableSpace G] where
  toFun : GaugeField d Λ G → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  norm_le : ∀ U, ‖toFun U‖ ≤ bound

instance
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] :
    CoeFun (@FiniteLatticeObservable d Λ G _ _) (fun _ => GaugeField d Λ G → ℂ) :=
  ⟨FiniteLatticeObservable.toFun⟩

/-- Every packaged observable is genuinely integrable under the normalized Gibbs probability. -/
theorem FiniteLatticeObservable.integrable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (observable : @FiniteLatticeObservable d Λ G _ _) :
    Integrable observable
      (normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure) := by
  letI : IsProbabilityMeasure
      (normalizedLatticeGibbsMeasure potential coupling gibbs.referenceMeasure) :=
    ⟨gibbs.gibbs_probability⟩
  apply Integrable.of_bound observable.measurable.aestronglyMeasurable observable.bound
  filter_upwards with U
  exact observable.norm_le U

/-- Expectation of a genuinely integrable bounded complex finite-cutoff observable. -/
noncomputable def finiteLatticeExpectation
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (gibbs : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (observable : @FiniteLatticeObservable d Λ G _ _) : ℂ :=
  ∫ U, observable U ∂(normalizedLatticeGibbsMeasure potential coupling
    gibbs.referenceMeasure)

end YangMills.Lattice
