/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothLieGroupScalarFunctionLinear

/-!
# Smoothness reduction for right-invariant scalar Laplacians

This file isolates one regularity input: differentiating a smooth scalar function along a fixed
right-invariant vector field again gives a smooth scalar function. From that field it constructs
smooth first derivatives, smooth iterated derivatives, finite-basis smooth Laplacians, and a
continuous-function realization of the pairing Laplacian.

The regularity input is intentionally an explicit structure with no inhabitant constructed here.
The file does not prove linearity of the raw `mfderiv`-based Laplacian, graph density, a heat-quotient
bound, or comparison with the Laplace–Beltrami operator.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff BigOperators

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Explicit regularity obligation saying that every smooth scalar test remains smooth after one
right-invariant directional derivative. -/
structure RightInvariantScalarDerivativeSmoothnessData where
  derivative_contMDiff :
    ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G))
      (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G),
      ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞
        (fun g => rightInvariantScalarDerivative f Y g)

namespace RightInvariantScalarDerivativeSmoothnessData

/-- One right-invariant derivative packaged back into the smooth scalar carrier. -/
def smoothDerivative
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  ⟨fun g => rightInvariantScalarDerivative f Y g,
    regularity.derivative_contMDiff f Y⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothDerivative_apply
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    regularity.smoothDerivative f Y g = rightInvariantScalarDerivative f Y g :=
  rfl

/-- Two iterated right-invariant derivatives packaged as a smooth scalar function. -/
def smoothSecondDerivative
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  regularity.smoothDerivative (regularity.smoothDerivative f Y) X

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothSecondDerivative_apply
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    regularity.smoothSecondDerivative f X Y g =
      rightInvariantScalarSecondDerivative f X Y g :=
  rfl

/-- A finite basis sum of second derivatives, now carrying an actual smoothness proof. -/
def smoothLaplacianInBasis
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  ∑ a, regularity.smoothSecondDerivative f (basis a) (basis a)

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothLaplacianInBasis_apply
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.smoothLaplacianInBasis basis f g =
      rightInvariantScalarLaplacianInBasis basis f g := by
  unfold smoothLaplacianInBasis rightInvariantScalarLaplacianInBasis
  rw [SmoothLieGroupScalarFunction.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rfl

/-- The selected pairing Laplacian packaged as a smooth scalar function. -/
def smoothPairingLaplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  regularity.smoothLaplacianInBasis laplacianData.orthonormalBasis.basis f

@[simp]
theorem smoothPairingLaplacian_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.smoothPairingLaplacian laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.smoothLaplacianInBasis_apply laplacianData.orthonormalBasis.basis f g

/-- Continuous ambient realization of the pairing Laplacian, derived from the one-step smoothness
field. This is a function-valued map, not yet a bundled linear map. -/
noncomputable def pairingLaplacianContinuousMap
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) : C(G, ℝ) :=
  smoothLieGroupScalarToContinuousLinearMap
    (regularity.smoothPairingLaplacian laplacianData f)

@[simp]
theorem pairingLaplacianContinuousMap_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.pairingLaplacianContinuousMap laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.smoothPairingLaplacian_apply laplacianData f g

end RightInvariantScalarDerivativeSmoothnessData

end

end Mathematics
end YangMills
