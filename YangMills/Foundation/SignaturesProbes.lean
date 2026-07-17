/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Signatures

/-!
# Hostile probes for signature separation

These probes prevent later APIs from silently replacing the Euclidean form by the Minkowski form,
reversing the chosen time sign, or treating the Minkowski form as positive in a spatial direction.
-/

namespace YangMills.EuclideanDimension.Probes

/-- A negative value cannot be supplied for the positive-definite Euclidean quadratic form. -/
theorem negative_euclidean_value_blocked
    (d : EuclideanDimension) (p : d.CoordinateVector)
    (h : d.euclideanQuadraticForm p < 0) : False := by
  exact (not_lt_of_ge (d.euclideanQuadraticForm_nonneg p)) h

/-- The chosen Minkowski convention rejects a nonpositive time-basis value. -/
theorem nonpositive_minkowski_time_basis_blocked
    (d : EuclideanDimension)
    (h : d.minkowskiQuadraticForm (d.basisVector d.timeIndex) ≤ 0) : False := by
  norm_num at h

/-- A Minkowski spatial basis direction cannot be declared nonnegative. -/
theorem nonnegative_minkowski_spatial_basis_blocked
    (d : EuclideanDimension) (i : Fin d.spatialDimension)
    (h : 0 ≤ d.minkowskiQuadraticForm (d.basisVector (d.spatialIndexSucc i))) : False := by
  norm_num at h

/-- In dimension two the Euclidean and Minkowski forms cannot be silently identified. -/
theorem two_forms_identified_blocked
    (h : EuclideanDimension.two.euclideanQuadraticForm =
      EuclideanDimension.two.minkowskiQuadraticForm) : False := by
  exact (EuclideanDimension.two.euclideanQuadraticForm_ne_minkowskiQuadraticForm (by decide)) h

/-- In dimension four the Euclidean and Minkowski forms cannot be silently identified. -/
theorem four_forms_identified_blocked
    (h : EuclideanDimension.four.euclideanQuadraticForm =
      EuclideanDimension.four.minkowskiQuadraticForm) : False := by
  exact (EuclideanDimension.four.euclideanQuadraticForm_ne_minkowskiQuadraticForm (by decide)) h

end YangMills.EuclideanDimension.Probes
