/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WeakBilocalDiagonalProbe

/-!
# Hostile probes for weak bilocal diagonal tests

The probes reject zero/amplitude-vanishing families, empty anchor regions, and support uniformly
separated from the diagonal. No OPE datum is constructed.
-/

namespace YangMills.Minkowski.WeakBilocalDiagonalProbe.Probes

open Filter Set Topology
open YangMills.Mathematics

/-- A constant two-point configuration lies exactly on the diagonal. -/
@[simp] theorem constant_configuration_distance_zero
    {d : EuclideanDimension} (x : Spacetime d) :
    bilocalDiagonalDistance (fun _ : Fin 2 => x) = 0 := by
  simp [bilocalDiagonalDistance, bilocalRelativeDisplacement]

/-- A normalized probe cannot become the zero Schwartz family near positive scale zero. -/
theorem eventually_zero_probe_blocked
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    ¬ (∀ᶠ r in 𝓝[>] (0 : ℝ), probe.test r = 0) := by
  intro hzero
  have hev := probe.test_ne_zero_eventually.and hzero
  rcases Filter.Eventually.exists hev with ⟨r, hne, heq⟩
  exact hne heq

/-- Integral-one normalization is retained explicitly at sufficiently small positive scales. -/
theorem exact_probe_normalization
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), bilocalSchwartzIntegral (probe.test r) = 1 :=
  probe.normalized_eventually

/-- Compact localization cannot use the empty set. -/
theorem empty_anchor_compact_blocked
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    probe.anchorCompact ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp probe.anchorCompact_nonempty

/-- A nonzero Schwartz test has a point in its topological support. -/
private theorem exists_mem_tsupport_of_ne_zero
    {d : EuclideanDimension}
    (F : SchwartzMap (FiniteConfiguration (Spacetime d) 2) ℂ) (hF : F ≠ 0) :
    ∃ x, x ∈ tsupport F := by
  have hsupp : (Function.support (F :
      FiniteConfiguration (Spacetime d) 2 → ℂ)).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty, Function.support_eq_empty_iff] at hempty
    exact hF (SchwartzMap.ext fun x => congrFun hempty x)
  rcases hsupp with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩

/-- Support cannot remain uniformly a positive distance away from the diagonal. -/
theorem fixed_diagonal_separation_blocked
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    ¬ ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ x ∈ tsupport (probe.test r), δ ≤ bilocalDiagonalDistance x := by
  rintro ⟨δ, hδ, hseparated⟩
  have hev := (probe.test_ne_zero_eventually.and
    (probe.relative_support_shrinks δ hδ)).and hseparated
  rcases Filter.Eventually.exists hev with ⟨r, ⟨hne, hclose⟩, hfar⟩
  rcases exists_mem_tsupport_of_ne_zero (probe.test r) hne with ⟨x, hx⟩
  exact (not_lt_of_ge (hfar x hx)) (hclose x hx)

/-- The same scale parameter used by OPE powers linearly controls supported separation. -/
theorem exact_linear_scale_control
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d) :
    0 < probe.relativeScaleConstant ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∀ x ∈ tsupport (probe.test r),
          bilocalDiagonalDistance x ≤ probe.relativeScaleConstant * r :=
  ⟨probe.relativeScaleConstant_positive, probe.relative_support_linear_bound⟩

/-- Every Schwartz seminorm obeys the fixed canonical polynomial scaling envelope. -/
theorem arbitrary_amplification_blocked
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (SchwartzMap.seminorm ℂ k n) (probe.test r) ≤
          C / r ^ (d.value + k + n) :=
  probe.seminorm_growth_control k n

/-- Every positive radius eventually controls every supported relative displacement. -/
theorem exact_all_radius_shrinking
    {d : EuclideanDimension} (probe : WeakBilocalDiagonalProbeData d)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ x ∈ tsupport (probe.test r), bilocalDiagonalDistance x < ε :=
  probe.relative_support_shrinks ε hε

end YangMills.Minkowski.WeakBilocalDiagonalProbe.Probes
