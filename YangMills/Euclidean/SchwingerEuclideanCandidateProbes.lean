/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerEuclideanCandidate

/-!
# Hostile probes for the composite strict Euclidean candidate

All probes take a candidate as a hypothesis. They force its fields to act on the same normalized
family and supplied direction, specialize positivity and clustering to the explicit nonzero bump,
and expose the dimension-one direction obstruction. No candidate is constructed.
-/

namespace YangMills.Euclidean.SchwingerEuclideanCandidate.Probes

/-- The composite retains the exact fixed-order growth bound on its same family. -/
theorem exact_growth_bound
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction)
    (n : PositiveArity) (f : ScalarSchwartzTestFunction d n.value) :
    ‖family.positivePoint n f‖ ≤
      candidate.fixedOrderGrowth.growth.coefficient n *
        mathlibSchwartzOrderControl d n.value candidate.fixedOrderGrowth.order f :=
  candidate.fixedOrderGrowth.bound n f

/-- Proper-Euclidean covariance is attached to the same normalized family. -/
theorem exact_covariance
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction)
    (n : PositiveArity) (motion : EuclideanProperRigidMotion d)
    (f : ScalarSchwartzTestFunction d n.value) :
    family.positivePoint n
        (pullbackScalarSchwartzTestFunctionByProperRigidMotion d motion f) =
      family.positivePoint n f :=
  candidate.covariance.invariant n motion f

/-- Permutation symmetry is attached to that same family. -/
theorem exact_permutation_symmetry
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction)
    (n : PositiveArity) (π : Equiv.Perm (Fin n.value))
    (f : ScalarSchwartzTestFunction d n.value) :
    family.positivePoint n (permuteScalarSchwartzTestFunction d π f) =
      family.positivePoint n f :=
  candidate.symmetry.invariant n π f

/-- Composite positivity reaches the explicit nonzero strict bump sequence. -/
theorem candidate_bump_reflection_nonnegative
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction) :
    IsNonnegativeComplexReal
      (mathlibStrictReflectionPositivityExpression family
        (singletonPositiveTimeBumpSequence d)) :=
  candidate.reflectionPositivity_apply (singletonPositiveTimeBumpSequence d)

/-- Composite clustering reaches the same bump pair along the candidate's exact direction. -/
theorem candidate_bump_pair_clusters
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (candidate : MathlibStrictScalarEuclideanCandidate family direction) :
    Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family direction
        (singletonPositiveTimeBumpSequence d)
        (singletonPositiveTimeBumpSequence d) scale)
      Filter.atTop (nhds 0) :=
  candidate.clustering_apply
    (singletonPositiveTimeBumpSequence d) (singletonPositiveTimeBumpSequence d)

/-- The clustering direction in every composite candidate is normalized and nonzero. -/
theorem candidate_direction_ne_zero
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {direction : EuclideanUnitSpatialDirection d}
    (_candidate : MathlibStrictScalarEuclideanCandidate family direction) :
    direction.vector ≠ 0 :=
  direction.vector_ne_zero

/-- No direction-indexed composite candidate can be packaged in dimension one. -/
theorem dimension_one_composite_candidate_blocked
    (family : ScalarSchwingerDistributionFamily EuclideanDimension.one) :
    IsEmpty (Σ direction : EuclideanUnitSpatialDirection EuclideanDimension.one,
      MathlibStrictScalarEuclideanCandidate family direction) :=
  oneDimensional_no_directionIndexedScalarEuclideanCandidate family

end YangMills.Euclidean.SchwingerEuclideanCandidate.Probes
