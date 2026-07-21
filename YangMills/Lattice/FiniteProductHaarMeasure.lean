/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FinitePeriodicGaugeField
import YangMills.Mathematics.NormalizedCompactHaarMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Normalized compact Haar measure on finite lattice gauge fields

Osterwalder–Seiler 1978, pp. 442–443, integrates lattice bond variables against product Haar
measure. This module constructs the finite-periodic counterpart from Mathlib's Haar measure on a
compact topological group. Each link marginal is the probability normalization of the same Haar
measure; the gauge-field reference is the exact finite product, not an unrelated invariant measure.

For a compact group, normalized left Haar measure is proved right- and inversion-invariant by Haar
uniqueness. Coordinatewise left/right multiplication then proves exact local gauge invariance of
the finite product. No Gibbs datum, reflection positivity, continuum limit, or quantum theory is
constructed.
-/

namespace YangMills.Lattice

open MeasureTheory Set

open YangMills.Mathematics

/-- Exact finite product of the same normalized Haar probability over all positive links. -/
noncomputable def finiteGaugeFieldProductHaarMeasure
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure (GaugeField d Λ G) :=
  Measure.pi (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G)

/-- The finite product Haar reference is a probability measure. -/
theorem finiteGaugeFieldProductHaarMeasure_probability
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    finiteGaugeFieldProductHaarMeasure (d := d) Λ G Set.univ = 1 := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  simp [finiteGaugeFieldProductHaarMeasure]

/-- Every exact link-coordinate marginal is the same normalized Haar probability. -/
theorem finiteGaugeFieldProductHaarMeasure_map_eval
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (link : PositiveOrientedLink d Λ) :
    Measure.map (Function.eval link) (finiteGaugeFieldProductHaarMeasure Λ G) =
      normalizedCompactHaarMeasure G := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  exact (measurePreserving_eval
    (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G) link).map_eq

/-- One link's endpoint gauge multiplication preserves normalized Haar measure. -/
theorem linkGaugeMap_measurePreserving
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (g : GaugeTransformation d Λ G) (link : PositiveOrientedLink d Λ) :
    MeasurePreserving
      (fun u : G => g link.base * u * (g (shiftForward link.base link.direction))⁻¹)
      (normalizedCompactHaarMeasure G) (normalizedCompactHaarMeasure G) := by
  letI : Measure.IsMulLeftInvariant (normalizedCompactHaarMeasure G) :=
    (normalizedCompactHaarMeasure_isHaar G).toIsMulLeftInvariant
  letI : Measure.IsMulRightInvariant (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  simpa [Function.comp_def, mul_assoc] using
    (measurePreserving_mul_left (normalizedCompactHaarMeasure G) (g link.base)).comp
      (measurePreserving_mul_right (normalizedCompactHaarMeasure G)
        (g (shiftForward link.base link.direction))⁻¹)

/-- Every local gauge transformation preserves the exact finite product Haar reference. -/
theorem gaugeTransform_measurePreserving_productHaar
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (g : GaugeTransformation d Λ G) :
    MeasurePreserving (gaugeTransform g)
      (finiteGaugeFieldProductHaarMeasure Λ G)
      (finiteGaugeFieldProductHaarMeasure Λ G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  change MeasurePreserving
    (fun U link => g link.base * U link * (g (shiftForward link.base link.direction))⁻¹)
    (Measure.pi (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G))
    (Measure.pi (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G))
  exact measurePreserving_pi
    (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G)
    (fun _ : PositiveOrientedLink d Λ => normalizedCompactHaarMeasure G)
    (linkGaugeMap_measurePreserving G g)

/-- Declaration-level form of exact local gauge invariance of finite product Haar measure. -/
theorem finiteGaugeFieldProductHaarMeasure_gaugeInvariant
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g) (finiteGaugeFieldProductHaarMeasure Λ G) =
      finiteGaugeFieldProductHaarMeasure Λ G :=
  (gaugeTransform_measurePreserving_productHaar Λ G g).map_eq

end YangMills.Lattice
