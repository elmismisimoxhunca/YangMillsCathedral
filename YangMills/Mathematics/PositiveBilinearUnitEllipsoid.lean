/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact

/-!
# Bounded unit ellipsoids of positive bilinear forms

A continuous bilinear form that is strictly positive on every nonzero vector is coercive in finite
dimensions. Consequently its open quadratic unit sublevel set is norm bounded and therefore von
Neumann bounded. This is the exact bornological field needed by Mathlib's
`ContMDiffRiemannianMetric` constructor.

The proof minimizes the quadratic form on the compact unit sphere. Symmetry is not required for
this boundedness statement; only the diagonal positivity and bilinearity are used.
-/

namespace YangMills.Mathematics

open Set Metric Bornology

universe uE

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The quadratic unit ellipsoid of a continuous strictly positive bilinear form is von Neumann
bounded in every finite-dimensional real normed space. -/
theorem positiveBilinear_unitEllipsoid_isVonNBounded
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (positive : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v | B v v < 1} := by
  by_cases nontrivial : Nontrivial E
  · letI : Nontrivial E := nontrivial
    let quadratic : E → ℝ := fun v => B v v
    have quadratic_continuous : Continuous quadratic :=
      (B.continuous.comp continuous_id).clm_apply continuous_id
    have sphere_nonempty : (sphere (0 : E) 1).Nonempty := by
      obtain ⟨e, he⟩ := exists_ne (0 : E)
      exact ⟨‖e‖⁻¹ • e, by
        rw [mem_sphere, dist_zero_right, norm_smul]
        simp [he]⟩
    obtain ⟨u, hu, hu_min⟩ :=
      (isCompact_sphere (0 : E) 1).exists_isMinOn sphere_nonempty
        quadratic_continuous.continuousOn
    have u_ne_zero : u ≠ 0 := by
      intro h
      subst u
      norm_num [mem_sphere] at hu
    have quadratic_u_pos : 0 < quadratic u := positive u u_ne_zero
    refine (NormedSpace.isVonNBounded_iff' ℝ).2
      ⟨(quadratic u)⁻¹ + 1, ?_⟩
    intro v hv
    by_cases v_zero : v = 0
    · subst v
      simp
      positivity
    let w : E := ‖v‖⁻¹ • v
    have w_mem_sphere : w ∈ sphere (0 : E) 1 := by
      rw [mem_sphere, dist_zero_right, norm_smul]
      simp [v_zero]
    have min_le : quadratic u ≤ quadratic w := hu_min w_mem_sphere
    have v_eq : v = ‖v‖ • w := by
      simp [w, v_zero]
    have quadratic_scale : quadratic v = ‖v‖ ^ 2 * quadratic w := by
      calc
        quadratic v = quadratic (‖v‖ • w) := congrArg quadratic v_eq
        _ = ‖v‖ ^ 2 * quadratic w := by
          simp [quadratic, pow_two]
          ring
    have norm_v_pos : 0 < ‖v‖ := norm_pos_iff.mpr v_zero
    have norm_bound : ‖v‖ < (quadratic u)⁻¹ + 1 := by
      by_contra not_lt
      have inv_add_one_le : (quadratic u)⁻¹ + 1 ≤ ‖v‖ := le_of_not_gt not_lt
      have inv_pos : 0 < (quadratic u)⁻¹ := inv_pos.mpr quadratic_u_pos
      have one_le_norm : 1 ≤ ‖v‖ := by nlinarith
      have one_le_norm_mul : 1 ≤ ‖v‖ * quadratic u := by
        nlinarith [inv_mul_cancel₀ (ne_of_gt quadratic_u_pos)]
      have norm_le_sq : ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith
      have product_le : ‖v‖ * quadratic u ≤ ‖v‖ ^ 2 * quadratic w :=
        mul_le_mul norm_le_sq min_le (le_of_lt quadratic_u_pos) (by positivity)
      have one_le_quadratic : 1 ≤ quadratic v := by
        rw [quadratic_scale]
        exact one_le_norm_mul.trans product_le
      exact (not_lt_of_ge one_le_quadratic) hv
    exact le_of_lt norm_bound
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp nontrivial
    exact IsVonNBounded.of_subsingleton

end

end YangMills.Mathematics
