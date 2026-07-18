/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FinitePeriodicGaugeField
import Mathlib.MeasureTheory.Measure.Haar.Unique
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

/-- Probability normalization of Mathlib's chosen Haar measure on a compact topological group. -/
noncomputable def normalizedCompactHaarMeasure
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : Measure G :=
  ((Measure.haar (G := G)) Set.univ)⁻¹ • Measure.haar

/-- The normalized compact Haar measure has total mass one. -/
theorem normalizedCompactHaarMeasure_isProbability
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (normalizedCompactHaarMeasure G) := by
  change IsProbabilityMeasure
    (((Measure.haar (G := G)) Set.univ)⁻¹ • Measure.haar)
  infer_instance

/-- Probability normalization retains the Haar property. -/
theorem normalizedCompactHaarMeasure_isHaar
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure.IsHaarMeasure (normalizedCompactHaarMeasure G) := by
  rw [normalizedCompactHaarMeasure]
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact ENNReal.inv_ne_top.mpr
      (Measure.measure_univ_eq_zero.not.mpr (NeZero.ne _))

/-- Left multiplication preserves normalized compact Haar measure. -/
theorem normalizedCompactHaarMeasure_map_mul_left
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (g : G) :
    Measure.map (g * ·) (normalizedCompactHaarMeasure G) =
      normalizedCompactHaarMeasure G := by
  letI : Measure.IsMulLeftInvariant (normalizedCompactHaarMeasure G) :=
    (normalizedCompactHaarMeasure_isHaar G).toIsMulLeftInvariant
  exact map_mul_left_eq_self _ _

private theorem map_normalizedCompactHaar_isProbability
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f : G → G) (hf : Measurable f) :
    IsProbabilityMeasure (Measure.map f (normalizedCompactHaarMeasure G)) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  constructor
  rw [Measure.map_apply hf .univ, preimage_univ, measure_univ]

/-- On a compact group, probability-normalized left Haar measure is also right-invariant. -/
theorem normalizedCompactHaarMeasure_isMulRightInvariant
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure.IsMulRightInvariant (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  letI : Measure.IsHaarMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isHaar G
  constructor
  intro g
  letI : IsProbabilityMeasure
      (Measure.map (· * g) (normalizedCompactHaarMeasure G)) :=
    map_normalizedCompactHaar_isProbability G _ (measurable_mul_const g)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Right multiplication preserves normalized compact Haar measure. -/
theorem normalizedCompactHaarMeasure_map_mul_right
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (g : G) :
    Measure.map (· * g) (normalizedCompactHaarMeasure G) =
      normalizedCompactHaarMeasure G :=
  (normalizedCompactHaarMeasure_isMulRightInvariant G).map_mul_right_eq_self g

/-- Normalized Haar measure on a compact group is inversion-invariant. -/
theorem normalizedCompactHaarMeasure_isInvInvariant
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure.IsInvInvariant (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  letI : Measure.IsHaarMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isHaar G
  letI : Measure.IsMulRightInvariant (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  constructor
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G).inv := by
    constructor
    rw [Measure.inv_apply, Set.inv_univ, measure_univ]
  letI : Measure.IsHaarMeasure (normalizedCompactHaarMeasure G).inv := by
    letI : Measure.IsMulLeftInvariant (normalizedCompactHaarMeasure G).inv := inferInstance
    letI : IsFiniteMeasureOnCompacts (normalizedCompactHaarMeasure G).inv := inferInstance
    letI : Measure.IsOpenPosMeasure (normalizedCompactHaarMeasure G).inv := inferInstance
    exact {}
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

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
