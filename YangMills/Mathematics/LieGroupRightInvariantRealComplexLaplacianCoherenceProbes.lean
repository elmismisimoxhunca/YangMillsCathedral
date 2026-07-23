/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantRealComplexLaplacianCoherence

/-!
# Hostile probes for real/complex Laplacian coherence
-/

namespace YangMills
namespace Mathematics
namespace LieGroupRightInvariantRealComplexLaplacianCoherence
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {realLaplacian : RightInvariantPairingLaplacianData inner}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The smooth real part retains the exact underlying pointwise real part. -/
theorem exact_smooth_real_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    f.realPart g = (f g).re :=
  rfl

/-- Coherence uses the same invariant pairing and exact real part of the complex Laplacian. -/
theorem exact_laplacian_real_part
    (coherence : RightInvariantPairingRealComplexLaplacianCoherenceData
      inner realLaplacian complexLaplacian)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    realLaplacian.laplacian f.realPart g =
      (complexLaplacian.laplacian f g).re :=
  coherence.laplacian_realPart f g

/-- Hostile coherence probe: a changed real Laplacian value is contradictory. -/
theorem changed_laplacian_real_part_blocked
    (coherence : RightInvariantPairingRealComplexLaplacianCoherenceData
      inner realLaplacian complexLaplacian)
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G)
    (changed : ℝ) (hchanged : changed ≠ (complexLaplacian.laplacian f g).re)
    (changedReal : realLaplacian.laplacian f.realPart g = changed) : False := by
  apply hchanged
  rw [← changedReal]
  exact coherence.laplacian_realPart f g

end

end Probes
end LieGroupRightInvariantRealComplexLaplacianCoherence
end Mathematics
end YangMills
