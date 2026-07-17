/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions

/-!
# Hostile probes for dimension bookkeeping

These are proved rejection properties, not examples of Yang–Mills theories. They ensure that zero,
out-of-range, and dimension-confused data cannot pass through the foundation layer silently.
-/

namespace YangMills.EuclideanDimension.Probes

/-- A purported supported zero-dimensional spacetime contradicts the lower bound. -/
theorem zero_dimension_blocked (d : EuclideanDimension) (h : d.value = 0) : False := by
  exact d.value_ne_zero h

/-- A purported supported dimension above four contradicts the upper bound. -/
theorem dimension_above_four_blocked (d : EuclideanDimension) (h : 5 ≤ d.value) : False := by
  have upper := d.le_four
  omega

/-- Dimension two cannot be silently identified with dimension four. -/
theorem two_equals_four_blocked (h : EuclideanDimension.two = EuclideanDimension.four) : False :=
  EuclideanDimension.two_ne_four h

/-- The two- and four-dimensional Euclidean spacetime carriers are not linearly equivalent.

This blocks an API from erasing the dimension index and reconnecting two-dimensional consistency
data to the four-dimensional contract through an arbitrary linear equivalence. -/
theorem no_linearEquiv_two_four :
    IsEmpty (EuclideanDimension.two.Spacetime ≃ₗ[ℝ] EuclideanDimension.four.Spacetime) := by
  constructor
  intro equivalence
  have ranks_equal := LinearEquiv.finrank_eq equivalence
  norm_num at ranks_equal

/-- Dimension one has no spatial coordinate after one coordinate is designated as Euclidean time.
This is arithmetic bookkeeping only; it does not assert reconstruction. -/
theorem one_has_no_spatial_coordinate :
    IsEmpty (Fin EuclideanDimension.one.spatialDimension) :=
  ⟨fun coordinate => Fin.elim0 coordinate⟩

end YangMills.EuclideanDimension.Probes
