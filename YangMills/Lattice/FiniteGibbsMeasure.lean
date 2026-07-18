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

/-- Nonnegative finite action bounds every Boltzmann density by one. -/
theorem latticeBoltzmannWeight_le_one
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField d Λ G) :
    latticeBoltzmannWeight potential coupling U ≤ 1 := by
  rw [latticeBoltzmannWeight, ENNReal.ofReal_le_one, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (wilsonTypeLatticeAction_nonnegative Λ potential coupling U)

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

/-- A measurable positive density over a probability reference has positive partition function. -/
theorem latticePartitionFunction_pos_of_probability
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G))
    (hprobability : reference Set.univ = 1)
    (hmeasurable : Measurable
      (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling)) :
    0 < latticePartitionFunction potential coupling reference := by
  rw [latticePartitionFunction, lintegral_pos_iff_support hmeasurable]
  have hsupport : Function.support
      (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling) = Set.univ := by
    ext U
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (latticeBoltzmannWeight_pos potential coupling U)
  rw [hsupport, hprobability]
  exact zero_lt_one

/-- The uniform bound by one makes the partition function finite over a probability reference. -/
theorem latticePartitionFunction_ne_top_of_probability
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G))
    (hprobability : reference Set.univ = 1) :
    latticePartitionFunction potential coupling reference ≠ ⊤ := by
  letI : IsProbabilityMeasure reference := ⟨hprobability⟩
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  exact lintegral_le_const (Filter.Eventually.of_forall
    (latticeBoltzmannWeight_le_one potential coupling))

/-- Positive finite partition function exactly normalizes the `withDensity` measure. -/
theorem normalizedLatticeGibbsMeasure_probability
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G))
    (hpos : 0 < latticePartitionFunction potential coupling reference)
    (hneTop : latticePartitionFunction potential coupling reference ≠ ⊤) :
    normalizedLatticeGibbsMeasure potential coupling reference Set.univ = 1 := by
  rw [normalizedLatticeGibbsMeasure, Measure.smul_apply, withDensity_apply _ .univ,
    Measure.restrict_univ, latticePartitionFunction]
  exact ENNReal.inv_mul_cancel hpos.ne' hneTop

/-- A measure-preserving symmetry of the reference and density preserves the normalized Gibbs
measure on the same exact chain. -/
theorem normalizedLatticeGibbsMeasure_map_eq_of_measurePreserving
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (reference : Measure (GaugeField d Λ G))
    (T : GaugeField d Λ G → GaugeField d Λ G)
    (hT : MeasurePreserving T reference reference)
    (hmeasurable : Measurable
      (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling))
    (hinvariant : ∀ U, latticeBoltzmannWeight potential coupling (T U) =
      latticeBoltzmannWeight potential coupling U) :
    Measure.map T (normalizedLatticeGibbsMeasure potential coupling reference) =
      normalizedLatticeGibbsMeasure potential coupling reference := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs]
  simp only [normalizedLatticeGibbsMeasure, Measure.smul_apply]
  congr 1
  rw [withDensity_apply _ (hs.preimage hT.measurable), withDensity_apply _ hs]
  calc
    ∫⁻ U in T ⁻¹' s, latticeBoltzmannWeight potential coupling U ∂reference =
        ∫⁻ U in T ⁻¹' s, latticeBoltzmannWeight potential coupling (T U) ∂reference := by
          apply setLIntegral_congr_fun (hs.preimage hT.measurable)
          intro U _
          exact (hinvariant U).symm
    _ = ∫⁻ U in s, latticeBoltzmannWeight potential coupling U ∂reference :=
      hT.setLIntegral_comp_preimage hs hmeasurable

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

/-- Strict positivity of the partition function is derived from the same measurable density and
probability reference, rather than accepted as a disconnected field. -/
theorem FiniteLatticeGibbsMeasureData.partition_pos
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    0 < latticePartitionFunction potential coupling data.referenceMeasure :=
  latticePartitionFunction_pos_of_probability potential coupling data.referenceMeasure
    data.reference_probability data.boltzmann_measurable

/-- Partition finiteness is derived from the exact action bound and probability reference. -/
theorem FiniteLatticeGibbsMeasureData.partition_ne_top
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    latticePartitionFunction potential coupling data.referenceMeasure ≠ ⊤ :=
  latticePartitionFunction_ne_top_of_probability potential coupling data.referenceMeasure
    data.reference_probability

/-- Gibbs probability normalization is derived from the same partition function and density. -/
theorem FiniteLatticeGibbsMeasureData.gibbs_probability
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling) :
    normalizedLatticeGibbsMeasure potential coupling data.referenceMeasure Set.univ = 1 :=
  normalizedLatticeGibbsMeasure_probability potential coupling data.referenceMeasure
    data.partition_pos data.partition_ne_top

/-- Gibbs gauge invariance is derived from the same reference transformation and exact invariant
density, rather than accepted as an unrelated final-measure field. -/
theorem FiniteLatticeGibbsMeasureData.gibbs_gaugeInvariant
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g)
      (normalizedLatticeGibbsMeasure potential coupling data.referenceMeasure) =
      normalizedLatticeGibbsMeasure potential coupling data.referenceMeasure :=
  normalizedLatticeGibbsMeasure_map_eq_of_measurePreserving potential coupling
    data.referenceMeasure (gaugeTransform g)
    ⟨data.gaugeTransform_measurable g, data.reference_gaugeInvariant g⟩
    data.boltzmann_measurable
    (latticeBoltzmannWeight_gaugeInvariant potential coupling g)

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
