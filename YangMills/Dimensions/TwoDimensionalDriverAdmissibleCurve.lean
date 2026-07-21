/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.List.Chain

/-!
# Driver-admissible planar curves

Driver's Definition 3.1 calls `(x, a(x))` horizontal when `a` is continuous, while Definition 3.8
calls a planar curve admissible when it admits a finite decomposition into vertical line segments
and the `C¹` subclass of those horizontal curves. This module gives a concrete normalized
certificate strengthening that requirement.

A finite strictly increasing breakpoint list runs from parameter `0` to parameter `1`. On every
adjacent interval the coordinate curve is either an affinely parameterized vertical line segment or
an affinely reparameterized graph of a `C¹` height function. The horizontal x-endpoints must be
distinct; orientation reversal is allowed.

Affine speed on each piece is a project parameterization strengthening: Driver specifies geometric
vertical segments and `C¹` horizontal curves but does not require this chosen speed. This is
reusable source-specific geometry. It constructs no curve, path carrier, graph, holonomy,
measure, or Yang--Mills object.
-/

namespace YangMills.Dimensions

open Set
open scoped ContDiff

noncomputable section

/-- First coordinate of literal two-dimensional Euclidean spacetime. -/
def twoDimensionalFirstCoordinate
    (point : EuclideanDimension.two.Spacetime) : ℝ :=
  (EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ point) ⟨0, by decide⟩

/-- Second coordinate of literal two-dimensional Euclidean spacetime. -/
def twoDimensionalSecondCoordinate
    (point : EuclideanDimension.two.Spacetime) : ℝ :=
  (EuclideanSpace.equiv EuclideanDimension.two.CoordinateIndex ℝ point) ⟨1, by decide⟩

/-- Affine interpolation from `startValue` to `endValue` across a nondegenerate parameter interval.
The definition is total; callers retain the strict interval hypothesis separately. -/
def affineIntervalCoordinate
    (parameterStart parameterEnd startValue endValue t : ℝ) : ℝ :=
  startValue + ((t - parameterStart) / (parameterEnd - parameterStart)) *
    (endValue - startValue)

/-- One adjacent interval of a Driver-admissible coordinate curve: either a vertical affine segment
or an oriented affine reparameterization of a `C¹` horizontal graph. -/
def IsDriverAdmissibleCurvePiece
    (curve : ℝ → EuclideanDimension.two.Spacetime)
    (parameterStart parameterEnd : ℝ) : Prop :=
  parameterStart < parameterEnd ∧
    ((∃ x yStart yEnd : ℝ, ∀ t ∈ Set.Icc parameterStart parameterEnd,
        twoDimensionalFirstCoordinate (curve t) = x ∧
        twoDimensionalSecondCoordinate (curve t) =
          affineIntervalCoordinate parameterStart parameterEnd yStart yEnd t) ∨
      (∃ xStart xEnd : ℝ, ∃ height : ℝ → ℝ,
        xStart ≠ xEnd ∧
        ContDiffOn ℝ 1 height (Set.uIcc xStart xEnd) ∧
        ∀ t ∈ Set.Icc parameterStart parameterEnd,
          let x := affineIntervalCoordinate
            parameterStart parameterEnd xStart xEnd t
          twoDimensionalFirstCoordinate (curve t) = x ∧
            twoDimensionalSecondCoordinate (curve t) = height x))

/-- Concrete normalized finite decomposition certificate strengthening Driver admissibility on
parameter interval `[0,1]` by choosing affine speed on every piece. -/
structure DriverAdmissibleCurveCertificate
    (curve : ℝ → EuclideanDimension.two.Spacetime) where
  /-- Ordered finite subdivision points. -/
  breakpoints : List ℝ
  breakpoints_nonempty : breakpoints ≠ []
  breakpoints_head : breakpoints.head breakpoints_nonempty = 0
  breakpoints_last : breakpoints.getLast breakpoints_nonempty = 1
  /-- Strict ordering prevents zero-length and reordered pieces. -/
  breakpoints_strict : breakpoints.Pairwise (· < ·)
  /-- Every adjacent interval is one exact vertical or `C¹` horizontal piece. -/
  pieces : breakpoints.IsChain (IsDriverAdmissibleCurvePiece curve)

namespace DriverAdmissibleCurveCertificate

/-- A certificate cannot use a singleton breakpoint list: its exact first and last parameters are
`0` and `1`. -/
theorem breakpoints_ne_singleton
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    (certificate : DriverAdmissibleCurveCertificate curve) (value : ℝ) :
    certificate.breakpoints ≠ [value] := by
  intro equality
  have head : value = 0 := by
    simpa [equality] using certificate.breakpoints_head
  have last : value = 1 := by
    simpa [equality] using certificate.breakpoints_last
  linarith

/-- In particular, every certificate has at least two breakpoints and therefore at least one
source-admissible piece. -/
theorem two_le_breakpoints_length
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    (certificate : DriverAdmissibleCurveCertificate curve) :
    2 ≤ certificate.breakpoints.length := by
  by_contra not_two
  by_cases length_zero : certificate.breakpoints.length = 0
  · exact certificate.breakpoints_nonempty (List.length_eq_zero_iff.mp length_zero)
  · have length_one : certificate.breakpoints.length = 1 := by omega
    obtain ⟨value, equality⟩ := List.length_eq_one_iff.mp length_one
    exact certificate.breakpoints_ne_singleton value equality

end DriverAdmissibleCurveCertificate

end

end YangMills.Dimensions
