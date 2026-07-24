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

/-- Exact probe: the one-step smoothness interface is canonically inhabited. -/
theorem exact_rightInvariantScalarDerivativeSmoothness_inhabited :
    Nonempty (RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G)) :=
  ⟨rightInvariantScalarDerivativeSmoothnessData⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact probe: the raw directional derivative is the vector-valued exterior derivative evaluated
on the right-invariant vector. -/
theorem exact_rightInvariantScalarDerivative_mvfderiv
    (f : G → ℝ) (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f Y g =
      mvfderiv (modelWithCornersSelf ℝ E) f g
        (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g) :=
  RightInvariantScalarDerivativeSmoothnessData.rightInvariantScalarDerivative_eq_mvfderiv
    f Y g

/-- Exact probe: the canonical one-step regularity constructs a smooth iterated derivative. -/
theorem exact_smoothSecondDerivative
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivativeSmoothnessData.smoothSecondDerivative f X Y g =
      rightInvariantScalarSecondDerivative f X Y g :=
  rightInvariantScalarDerivativeSmoothnessData.smoothSecondDerivative_apply f X Y g

/-- Exact probe: the continuous ambient representative has the original pairing-Laplacian value. -/
theorem exact_pairingLaplacianContinuousMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarDerivativeSmoothnessData.pairingLaplacianContinuousMap
      laplacianData f g = laplacianData.laplacian f g :=
  rightInvariantScalarDerivativeSmoothnessData.pairingLaplacianContinuousMap_apply
    laplacianData f g

/-- Exact probe: the pairing Laplacian is now a linear map from the smooth domain into the
continuous ambient carrier. -/
theorem exact_pairingLaplacianLinearMap
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    rightInvariantPairingLaplacianLinearMap laplacianData f g =
      laplacianData.laplacian f g :=
  rightInvariantPairingLaplacianLinearMap_apply laplacianData f g

/-- Exact probe: additivity and real homogeneity hold in the continuous ambient carrier. -/
theorem exact_pairingLaplacianLinearMap_linearity
    (c : ℝ) (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    rightInvariantPairingLaplacianLinearMap laplacianData (c • f + h) =
      c • rightInvariantPairingLaplacianLinearMap laplacianData f +
        rightInvariantPairingLaplacianLinearMap laplacianData h := by
  rw [map_add, map_smul]

/-- Hostile probe: no changed continuous function can replace the constructed linear pairing-
Laplacian value. -/
theorem changed_pairingLaplacianLinearMap_blocked
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (changed : C(G, ℝ))
    (changed_ne_exact : changed ≠
      rightInvariantPairingLaplacianLinearMap laplacianData f)
    (claimed : rightInvariantPairingLaplacianLinearMap laplacianData f = changed) : False :=
  changed_ne_exact claimed.symm

end

end Mathematics
end YangMills
