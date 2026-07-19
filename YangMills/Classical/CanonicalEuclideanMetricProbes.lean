/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.CanonicalEuclideanMetric

/-! Hostile probes for the canonical flat Euclidean spacetime metric. -/

namespace YangMills.Classical.CanonicalEuclideanMetric.Probes

open scoped Manifold ContDiff

/-- Every fiber pairing is the exact standard real inner product. -/
theorem exact_inner
    (d : EuclideanDimension) (x : d.Spacetime)
    (v w : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) :
    (canonicalEuclideanSpacetimeMetricData d).metric.inner x v w =
      @inner ℝ d.Spacetime _ v w :=
  canonicalEuclideanSpacetimeMetricData_inner d x v w

/-- Every self-pairing is the exact squared coordinate norm. -/
theorem exact_inner_self
    (d : EuclideanDimension) (x : d.Spacetime)
    (v : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) :
    (canonicalEuclideanSpacetimeMetricData d).metric.inner x v v =
      ‖(show d.Spacetime from v)‖ ^ 2 :=
  canonicalEuclideanSpacetimeMetricData_inner_self d x v

/-- A canonical coordinate basis vector has metric norm squared one at every base point. -/
theorem exact_basis_vector_self
    (d : EuclideanDimension) (x : d.Spacetime) (i : d.CoordinateIndex) :
    (canonicalEuclideanSpacetimeMetricData d).metric.inner x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 1 := by
  rw [canonicalEuclideanSpacetimeMetricData_inner_self]
  simp

/-- Nonzero tangent vectors have strictly positive canonical self-pairing. -/
theorem exact_positive
    (d : EuclideanDimension) (x : d.Spacetime)
    (v : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) (nonzero : v ≠ 0) :
    0 < (canonicalEuclideanSpacetimeMetricData d).metric.inner x v v :=
  canonicalEuclideanSpacetimeMetricData_pos d x v nonzero

/-- A different metric pairing cannot be silently substituted for the canonical flat metric. -/
theorem unrelated_metric_blocked
    (d : EuclideanDimension)
    (wrong : EuclideanMetricData
      (IB := modelWithCornersSelf ℝ d.Spacetime) (B := d.Spacetime))
    (x : d.Spacetime)
    (v w : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x)
    (different : wrong.metric.inner x v w ≠ @inner ℝ d.Spacetime _ v w)
    (claimed : wrong = canonicalEuclideanSpacetimeMetricData d) : False := by
  apply different
  have pairing := congrArg (fun geometry => geometry.metric.inner x v w) claimed
  rw [pairing]
  exact canonicalEuclideanSpacetimeMetricData_inner d x v w

/-- The three-dimensional specialization uses the same exact standard inner product on coordinate
`ℝ³`; no arbitrary Riemannian metric remains in this specialization. -/
theorem exact_three_dimensional_inner
    (x : EuclideanDimension.three.Spacetime)
    (v w : TangentSpace
      (modelWithCornersSelf ℝ EuclideanDimension.three.Spacetime) x) :
    (canonicalEuclideanSpacetimeMetricData EuclideanDimension.three).metric.inner x v w =
      @inner ℝ EuclideanDimension.three.Spacetime _ v w :=
  canonicalEuclideanSpacetimeMetricData_inner EuclideanDimension.three x v w

end YangMills.Classical.CanonicalEuclideanMetric.Probes
