/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteGibbsMeasure
import YangMills.Lattice.FiniteProductHaarMeasure

/-!
# Gibbs acceptance data on the exact finite product Haar reference

This module closes the reference-measure gap in the preliminary Gibbs interface: the reference is
now definitionally the finite product of normalized compact-group Haar probabilities. The only new
acceptance field is measurability of the already-fixed Wilson-type Boltzmann density. Reference
probability, local gauge-action measurability, reference invariance, positive finite partition
function, Gibbs normalization, and Gibbs gauge invariance are all derived on the same exact chain.

This constructs neither an inhabitant nor a Gibbs expectation. It does not identify finite-cutoff
data with continuum Osterwalder–Schrader or Clay data.
-/

namespace YangMills.Lattice

open MeasureTheory

/-- Finite-periodic Gibbs acceptance data with the exact compact product-Haar reference fixed.

Potential measurability is deliberately not inferred from algebraic class-function laws; a future
representation/character or continuous-potential layer must supply it. -/
structure FiniteProductHaarGibbsMeasureData
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) where
  /-- Exact measurability of the same Boltzmann density used in the partition function. -/
  boltzmann_measurable : Measurable
    (latticeBoltzmannWeight (d := d) (Λ := Λ) potential coupling)

/-- Forgetting the compact-Haar construction yields the generic Gibbs checker with no choices. -/
noncomputable def FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    @FiniteLatticeGibbsMeasureData d Λ G _ _ potential coupling where
  referenceMeasure := finiteGaugeFieldProductHaarMeasure Λ G
  reference_probability := finiteGaugeFieldProductHaarMeasure_probability Λ G
  gaugeTransform_measurable := fun g =>
    (gaugeTransform_measurePreserving_productHaar Λ G g).measurable
  reference_gaugeInvariant := fun g =>
    finiteGaugeFieldProductHaarMeasure_gaugeInvariant Λ G g
  boltzmann_measurable := data.boltzmann_measurable

/-- The specialized partition function uses the exact finite product Haar measure. -/
noncomputable def finiteProductHaarLatticePartitionFunction
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) : ENNReal :=
  latticePartitionFunction (d := d) (Λ := Λ) potential coupling
    (finiteGaugeFieldProductHaarMeasure (d := d) Λ G)

/-- The specialized normalized Gibbs measure cannot switch to an unrelated reference. -/
noncomputable def normalizedFiniteProductHaarLatticeGibbsMeasure
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) :
    Measure (GaugeField d Λ G) :=
  normalizedLatticeGibbsMeasure (d := d) (Λ := Λ) potential coupling
    (finiteGaugeFieldProductHaarMeasure (d := d) Λ G)

/-- Measurability plus exact product-Haar probability implies positive partition function. -/
theorem FiniteProductHaarGibbsMeasureData.partition_pos
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    0 < finiteProductHaarLatticePartitionFunction (d := d) (Λ := Λ) G potential coupling := by
  simpa [finiteProductHaarLatticePartitionFunction,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    data.toFiniteLatticeGibbsMeasureData.partition_pos

/-- The action bound by one and product-Haar probability imply finite partition function. -/
theorem FiniteProductHaarGibbsMeasureData.partition_ne_top
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    finiteProductHaarLatticePartitionFunction (d := d) (Λ := Λ) G potential coupling ≠ ⊤ := by
  simpa [finiteProductHaarLatticePartitionFunction,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    data.toFiniteLatticeGibbsMeasureData.partition_ne_top

/-- The exact product-Haar Gibbs measure is normalized, as a derived theorem. -/
theorem FiniteProductHaarGibbsMeasureData.gibbs_probability
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G potential coupling
      Set.univ = 1 := by
  simpa [normalizedFiniteProductHaarLatticeGibbsMeasure,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    data.toFiniteLatticeGibbsMeasureData.gibbs_probability

/-- The exact product-Haar Gibbs measure is locally gauge invariant, as a derived theorem. -/
theorem FiniteProductHaarGibbsMeasureData.gibbs_gaugeInvariant
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) =
      normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling := by
  simpa [normalizedFiniteProductHaarLatticeGibbsMeasure,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    data.toFiniteLatticeGibbsMeasureData.gibbs_gaugeInvariant g

end YangMills.Lattice
