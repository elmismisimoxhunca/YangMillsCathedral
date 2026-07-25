/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Classical.CanonicalEuclideanMetric
import YangMills.Classical.EuclideanAction
import YangMills.Euclidean.SchwingerEuclideanCandidate
import YangMills.Geometry.LieGroup
import YangMills.Minkowski.ScalarWightmanAxiomSurface
import YangMills.Minkowski.WightmanJointTemperedCorrelators
import YangMills.Minkowski.WightmanLocalObservableCoherence
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Observables.CurvatureSquaredInterpretation
import YangMills.Reconstruction.StrictOrderedWickContinuation

/-!
# Minimal shared foundation for the bounded three-dimensional checker

This module names the exact coordinate carrier and imports only the general interfaces used by the
bounded SU(2) checker. Stronger stress-tensor, source-facing OS, and four-dimensional acceptance
surfaces are intentionally outside this foundation.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff

noncomputable section

/-- Exact classical coordinate base for the three-dimensional checker. -/
abbrev ThreeDimensionalEuclideanBase := EuclideanDimension.three.Spacetime

/-- Self model for the exact three-dimensional Euclidean coordinate base. -/
abbrev threeDimensionalEuclideanModel :=
  modelWithCornersSelf ℝ ThreeDimensionalEuclideanBase

end

end YangMills.Dimensions
