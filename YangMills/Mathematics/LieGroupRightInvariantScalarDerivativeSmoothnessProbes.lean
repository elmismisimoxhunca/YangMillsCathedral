/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantScalarDerivativeSmoothness

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
  {inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)}
  (laplacianData : RightInvariantPairingLaplacianData inner)
  (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact probe: the supplied one-step regularity constructs a smooth iterated derivative. -/
theorem exact_smoothSecondDerivative
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    regularity.smoothSecondDerivative f X Y g =
      rightInvariantScalarSecondDerivative f X Y g :=
  regularity.smoothSecondDerivative_apply f X Y g

/-- Exact probe: the continuous ambient representative has the original pairing-Laplacian value. -/
theorem exact_pairingLaplacianContinuousMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.pairingLaplacianContinuousMap laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.pairingLaplacianContinuousMap_apply laplacianData f g

/-- Hostile probe: no changed continuous function can be identified with the constructed pairing
Laplacian representative. -/
theorem changed_pairingLaplacianContinuousMap_blocked
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      regularity.pairingLaplacianContinuousMap laplacianData f)
    (claimed : regularity.pairingLaplacianContinuousMap laplacianData f = changed) : False :=
  changed_ne_exact claimed.symm

end

end Mathematics
end YangMills
