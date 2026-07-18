/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.TemperedLocalObservableProducts

/-!
# Normalized weak probes approaching the bilocal diagonal

Wilson 1969, §II, formulates the operator-product expansion weakly for `y` sufficiently close to
`x`, between fixed states. This module defines a nonvacuous Schwartz-test family for that regime.
Relative support is bounded by a fixed positive constant times the scale and shrinks to the
diagonal, anchors remain in one compact set, Schwartz seminorms obey a fixed dimension/order
polynomial envelope, and the full test has
Lebesgue integral one at all sufficiently small positive scales.

Normalization blocks zero or amplitude-vanishing probes. This is only test-family infrastructure:
no OPE coefficient, truncation, asymptotic remainder, curvature interpretation, field, or theory is
constructed.
-/

namespace YangMills.Minkowski

open Filter MeasureTheory Set Topology
open YangMills.Mathematics

/-- Anchor coordinate of a two-point Minkowski configuration. -/
def bilocalConfigurationAnchor
    {d : EuclideanDimension}
    (x : FiniteConfiguration (Spacetime d) 2) : Spacetime d :=
  x 0

/-- Relative displacement `y - x` in coordinate order `(x,y)`. -/
def bilocalRelativeDisplacement
    {d : EuclideanDimension}
    (x : FiniteConfiguration (Spacetime d) 2) : Spacetime d :=
  x 1 - x 0

/-- Euclidean control norm used only to measure approach to the configuration-space diagonal. -/
def bilocalDiagonalDistance
    {d : EuclideanDimension}
    (x : FiniteConfiguration (Spacetime d) 2) : ℝ :=
  ‖bilocalRelativeDisplacement x‖

/-- Zero diagonal distance is exactly equality of the two configuration coordinates. -/
theorem bilocalDiagonalDistance_eq_zero_iff
    {d : EuclideanDimension}
    (x : FiniteConfiguration (Spacetime d) 2) :
    bilocalDiagonalDistance x = 0 ↔ x 1 = x 0 := by
  rw [bilocalDiagonalDistance, norm_eq_zero, bilocalRelativeDisplacement, sub_eq_zero]

/-- Lebesgue integral of one full bilocal Schwartz test. -/
noncomputable def bilocalSchwartzIntegral
    {d : EuclideanDimension}
    (F : SchwartzMap (FiniteConfiguration (Spacetime d) 2) ℂ) : ℂ :=
  ∫ x, F x

/-- A normalized compact-anchor family of full Schwartz tests approaching the bilocal diagonal. -/
structure WeakBilocalDiagonalProbeData (d : EuclideanDimension) where
  /-- Scale-dependent full two-configuration test. Only `r → 0+` is constrained. -/
  test : ℝ → SchwartzMap (FiniteConfiguration (Spacetime d) 2) ℂ
  /-- One compact region containing all sufficiently small-scale anchor support. -/
  anchorCompact : Set (Spacetime d)
  anchorCompact_isCompact : IsCompact anchorCompact
  /-- Full-test normalization prevents an eventually zero or arbitrarily rescaled-away probe. -/
  normalized_eventually :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), bilocalSchwartzIntegral (test r) = 1
  /-- Anchors of the topological support remain in the same compact set. -/
  anchor_localized_eventually :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ x ∈ tsupport (test r), bilocalConfigurationAnchor x ∈ anchorCompact
  /-- Fixed positive comparison constant tying geometric support radius to the scale parameter. -/
  relativeScaleConstant : ℝ
  relativeScaleConstant_positive : 0 < relativeScaleConstant
  /-- Relative support is `O(r)`, making finite-order powers of the same `r` meaningful. -/
  relative_support_linear_bound :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ x ∈ tsupport (test r),
        bilocalDiagonalDistance x ≤ relativeScaleConstant * r
  /-- Relative support approaches the diagonal at every requested positive radius. -/
  relative_support_shrinks : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ x ∈ tsupport (test r), bilocalDiagonalDistance x < ε
  /-- Canonical polynomial seminorm-growth envelope for scaling only the `d` relative directions.
  This blocks arbitrarily amplified zero-integral additions to the normalized probe shape. -/
  seminorm_growth_control : ∀ k n : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (SchwartzMap.seminorm ℂ k n) (test r) ≤ C / r ^ (d.value + k + n)

/-- Normalization proves that a weak diagonal probe is eventually genuinely nonzero. -/
theorem WeakBilocalDiagonalProbeData.test_ne_zero_eventually
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), probe.test r ≠ 0 := by
  filter_upwards [probe.normalized_eventually] with r hr
  intro hzero
  rw [hzero] at hr
  simp [bilocalSchwartzIntegral] at hr

/-- The compact anchor region of a normalized probe is necessarily inhabited. -/
theorem WeakBilocalDiagonalProbeData.anchorCompact_nonempty
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    probe.anchorCompact.Nonempty := by
  have hev := probe.test_ne_zero_eventually.and probe.anchor_localized_eventually
  rcases Filter.Eventually.exists hev with ⟨r, hnonzero, hlocalized⟩
  have hsupp : (Function.support (probe.test r :
      FiniteConfiguration (Spacetime d) 2 → ℂ)).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty, Function.support_eq_empty_iff] at hempty
    exact hnonzero (SchwartzMap.ext fun x => congrFun hempty x)
  rcases hsupp with ⟨x, hx⟩
  exact ⟨bilocalConfigurationAnchor x,
    hlocalized x (subset_closure hx)⟩

end YangMills.Minkowski
