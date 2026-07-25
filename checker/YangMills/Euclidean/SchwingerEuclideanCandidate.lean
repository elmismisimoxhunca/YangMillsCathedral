/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerRegularity
import YangMills.Euclidean.SchwingerCovariance
import YangMills.Euclidean.SchwingerSymmetry
import YangMills.Euclidean.SchwingerReflectionPositivityForm
import YangMills.Euclidean.SchwingerClusteringForm

/-!
# Composite strict-domain scalar Euclidean candidate

This module assembles the currently proved Mathlib-side scalar Schwinger requirements around one
normalized distribution family and one explicitly supplied unit spatial direction:

* fixed-order factorial growth on full Mathlib Schwartz spaces;
* proper-Euclidean covariance `(E1)`;
* permutation symmetry `(E3)`;
* the strict-domain reflection-positivity candidate;
* the strict-domain clustering candidate along the supplied direction.

The record is deliberately named `MathlibStrictScalarEuclideanCandidate`, not an OS theory or
reconstruction datum. It does not turn the preliminary growth estimate into OS-II `(E0′)`, does not
bridge strict support to OS-I's derivative-vanishing carrier, and does not assert `(E2)`, `(E4)`,
reconstruction, existence, or a mass gap. No inhabitant is constructed.
-/

namespace YangMills

/-- One internally coherent scalar Euclidean candidate on the current strict Mathlib test domain.
Every field is indexed by the same distribution family; clustering is indexed by the same explicit
unit spatial direction. -/
structure MathlibStrictScalarEuclideanCandidate
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (direction : EuclideanUnitSpatialDirection d) where
  /-- Preliminary OS-II-strength growth candidate on full Mathlib Schwartz spaces. -/
  fixedOrderGrowth : MathlibFixedOrderFactorialGrowthData family
  /-- Exact proper-Euclidean covariance candidate `(E1)`. -/
  covariance : ScalarSchwingerEuclideanCovariance family
  /-- Exact scalar permutation symmetry candidate `(E3)`. -/
  symmetry : ScalarSchwingerPermutationSymmetry family
  /-- Reflection positivity on the current strict Mathlib positive-time subdomain. -/
  reflectionPositivity : MathlibStrictScalarReflectionPositivity family
  /-- Clustering on that same strict domain along the supplied unit spatial direction. -/
  clustering : MathlibStrictScalarClusteringAlongDirection family direction

/-- The composite candidate exposes strict-domain reflection positivity for every exact strict test
sequence. -/
theorem MathlibStrictScalarEuclideanCandidate.reflectionPositivity_apply
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction)
    (f : MathlibStrictPositiveTimeTestSequence d) :
    IsNonnegativeComplexReal (mathlibStrictReflectionPositivityExpression family f) :=
  candidate.reflectionPositivity f

/-- The composite candidate exposes strict-domain clustering for every exact pair of strict test
sequences. -/
theorem MathlibStrictScalarEuclideanCandidate.clustering_apply
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction)
    (f g : MathlibStrictPositiveTimeTestSequence d) :
    Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family direction f g scale)
      Filter.atTop (nhds 0) :=
  candidate.clustering f g

/-- A direction-indexed composite candidate cannot be packaged or inhabited in dimension one,
because no unit spatial direction exists. This is a lower-dimensional consistency fact, not an
existence or nonexistence theorem for a physical one-dimensional theory. -/
theorem oneDimensional_no_directionIndexedScalarEuclideanCandidate
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.one) :
    IsEmpty (Σ direction : EuclideanUnitSpatialDirection EuclideanDimension.one,
      MathlibStrictScalarEuclideanCandidate family direction) := by
  constructor
  intro candidate
  exact oneDimensional_no_unitSpatialDirection.false candidate.1

end YangMills
