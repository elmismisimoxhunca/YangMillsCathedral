/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Probability-normalized Haar measure on a compact group

This neutral measure-theoretic module constructs probability-normalized Haar measure on a compact
topological group and derives left, right, and inversion invariance from Haar uniqueness. It is
independent of lattice gauge fields and is shared by finite-lattice and continuum interfaces.

No compact gauge group, heat kernel, Gibbs measure, or quantum theory is constructed here.
-/

namespace YangMills.Mathematics

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

end YangMills.Mathematics
