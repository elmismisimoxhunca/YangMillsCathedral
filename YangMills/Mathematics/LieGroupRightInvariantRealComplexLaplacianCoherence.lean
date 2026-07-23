/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantComplexLaplacian

/-!
# Coherence between real and complex pairing Laplacians

The Driver two-dimensional heat interface is real-valued, while the character spectral development
uses a complex-valued Laplacian. Both operators are indexed by the same invariant pairing, but the
current basis-independence packages do not themselves prove that taking real parts commutes with
the two manifold derivatives and finite basis sum.

This file exposes that remaining compatibility as explicit uninhabited
`RightInvariantPairingRealComplexLaplacianCoherenceData`. No equality is assumed between unrelated
pairings or Laplacians.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Exact real/complex compatibility for Laplacians normalized by one unchanged invariant pairing. -/
structure RightInvariantPairingRealComplexLaplacianCoherenceData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (realLaplacian : RightInvariantPairingLaplacianData inner)
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner) where
  laplacian_realPart : ∀
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G),
    realLaplacian.laplacian f.realPart g =
      (complexLaplacian.laplacian f g).re

end

end Mathematics
end YangMills
