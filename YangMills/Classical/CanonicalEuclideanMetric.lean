/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Classical.EuclideanCurvatureDensity
import YangMills.Foundation.Dimensions
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Canonical flat metric on Euclidean spacetime

Mathlib constructs the standard smooth Riemannian metric on every real inner-product vector space by
using its inner product in every tangent fiber. This module packages that exact metric in the
project's `EuclideanMetricData` interface for each supported spacetime dimension.

Mathlib's standard metric is `C^ω`; the project interface asks only for `C^∞`, obtained by monotonicity.
No second metric or inner product is selected. This module does not construct a principal bundle,
connection, action datum, or metric-induced volume-measure bridge.
-/

namespace YangMills.Classical

open scoped Manifold ContDiff

/-- Exact canonical flat Euclidean metric on the coordinate spacetime of dimension `d`. -/
noncomputable def canonicalEuclideanSpacetimeMetricData (d : EuclideanDimension) :
    EuclideanMetricData
      (IB := modelWithCornersSelf ℝ (EuclideanDimension.Spacetime d))
      (B := EuclideanDimension.Spacetime d) where
  metric := by
    let standard := riemannianMetricVectorSpace (EuclideanDimension.Spacetime d)
    exact {
      inner := standard.inner
      symm := standard.symm
      pos := standard.pos
      isVonNBounded := standard.isVonNBounded
      contMDiff := standard.contMDiff.of_le le_top
    }

/-- The metric pairing is definitionally the standard real inner product in every tangent fiber. -/
@[simp]
theorem canonicalEuclideanSpacetimeMetricData_inner
    (d : EuclideanDimension) (x : d.Spacetime)
    (v w : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) :
    (canonicalEuclideanSpacetimeMetricData d).metric.inner x v w =
      @inner ℝ d.Spacetime _ v w :=
  rfl

/-- The canonical metric evaluates a vector against itself as its squared norm. -/
@[simp]
theorem canonicalEuclideanSpacetimeMetricData_inner_self
    (d : EuclideanDimension) (x : d.Spacetime)
    (v : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) :
    (canonicalEuclideanSpacetimeMetricData d).metric.inner x v v =
      ‖(show d.Spacetime from v)‖ ^ 2 := by
  rw [canonicalEuclideanSpacetimeMetricData_inner, real_inner_self_eq_norm_sq]

/-- The canonical metric is strictly positive on every nonzero tangent vector. -/
theorem canonicalEuclideanSpacetimeMetricData_pos
    (d : EuclideanDimension) (x : d.Spacetime)
    (v : TangentSpace (modelWithCornersSelf ℝ d.Spacetime) x) (nonzero : v ≠ 0) :
    0 < (canonicalEuclideanSpacetimeMetricData d).metric.inner x v v :=
  (canonicalEuclideanSpacetimeMetricData d).metric.pos x v nonzero

end YangMills.Classical
