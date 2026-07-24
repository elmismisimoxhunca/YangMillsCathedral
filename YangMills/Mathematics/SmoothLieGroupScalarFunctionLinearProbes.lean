/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothLieGroupScalarFunctionLinear

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact pointwise linearity probe on the smooth carrier. -/
theorem exact_smoothScalar_pointwise_linearity
    (c : ℝ) (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (c • (f + h)) g = c * (f g + h g) := by
  simp
  ring

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact pointwise probes for negation, subtraction, and natural/integer scaling. -/
theorem exact_smoothScalar_pointwise_group_operations
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G))
    (n : ℕ) (z : ℤ) (g : G) :
    (-f) g = -f g ∧ (f - h) g = f g - h g ∧
      (n • f) g = n • f g ∧ (z • f) g = z • f g := by
  simp

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact probe for the smooth-domain map into the continuous ambient carrier. -/
theorem exact_smoothScalar_continuousLinearMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    smoothLieGroupScalarToContinuousLinearMap f g = f g :=
  smoothLieGroupScalarToContinuousLinearMap_apply f g

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact density-target probe: the named proposition is precisely density of the smooth image. -/
theorem exact_smoothLieGroupScalarFunctionsDenseInContinuous
    (dense : SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G)) :
    Dense (Set.range
      (smoothLieGroupScalarToContinuousLinearMap (E := E) (G := G))) :=
  dense

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile probe: two distinct smooth functions cannot have the same ambient continuous image. -/
theorem changed_smoothScalar_continuousImage_blocked
    (f changed : SmoothLieGroupScalarFunction (E := E) (G := G))
    (changed_ne : changed ≠ f)
    (claimed : smoothLieGroupScalarToContinuousLinearMap changed =
      smoothLieGroupScalarToContinuousLinearMap f) : False :=
  changed_ne (smoothLieGroupScalarToContinuousLinearMap_injective claimed)

end

end Mathematics
end YangMills
