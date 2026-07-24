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
current basis-independence packages do not themselves identify the two value types. This file proves
that taking real and imaginary parts commutes with each right-invariant derivative by the manifold
chain rule, constructs smooth complex directional derivatives using tangent-map calculus, propagates coherence
through second derivatives and finite basis sums, and canonically inhabits
`RightInvariantPairingRealComplexLaplacianCoherenceData` for Laplacians normalized by the same
pairing. No equality is asserted between unrelated pairings or Laplacians.
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
  laplacian_imaginaryPart : ∀
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G),
    realLaplacian.laplacian f.imaginaryPart g =
      (complexLaplacian.laplacian f g).im

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Taking real parts commutes with one right-invariant derivative. -/
theorem rightInvariantScalarDerivative_realPart
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f.realPart Y g =
      (rightInvariantComplexDerivative f Y g).re := by
  unfold rightInvariantScalarDerivative rightInvariantComplexDerivative
  have chain := mfderiv_comp (I := modelWithCornersSelf ℝ E)
    (I' := modelWithCornersSelf ℝ ℂ) (I'' := modelWithCornersSelf ℝ ℝ)
    (f := f.toFun) (g := Complex.reCLM) g Complex.reCLM.mdifferentiableAt
    (f.contMDiff.mdifferentiableAt (by simp))
  rw [Complex.reCLM.hasMFDerivAt.mfderiv] at chain
  exact congrArg
    (fun L => L (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g)) chain

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Taking imaginary parts commutes with one right-invariant derivative. -/
theorem rightInvariantScalarDerivative_imaginaryPart
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f.imaginaryPart Y g =
      (rightInvariantComplexDerivative f Y g).im := by
  unfold rightInvariantScalarDerivative rightInvariantComplexDerivative
  have chain := mfderiv_comp (I := modelWithCornersSelf ℝ E)
    (I' := modelWithCornersSelf ℝ ℂ) (I'' := modelWithCornersSelf ℝ ℝ)
    (f := f.toFun) (g := Complex.imCLM) g Complex.imCLM.mdifferentiableAt
    (f.contMDiff.mdifferentiableAt (by simp))
  rw [Complex.imCLM.hasMFDerivAt.mfderiv] at chain
  exact congrArg
    (fun L => L (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g)) chain

/-- A right-invariant derivative of a smooth complex test is again smooth. -/
theorem contMDiff_rightInvariantComplexDerivative
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (fun g => rightInvariantComplexDerivative f Y g) := by
  have hfield := contMDiff_mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y
  have htangent := f.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)
  have hsnd :=
    contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℂ (modelWithCornersSelf ℝ ℂ)
  exact hsnd.comp (htangent.comp hfield)

/-- One complex right-invariant derivative packaged in the smooth complex carrier. -/
noncomputable def smoothRightInvariantComplexDerivative
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    SmoothLieGroupComplexFunction (E := E) (G := G) :=
  ⟨fun g => rightInvariantComplexDerivative f Y g,
    contMDiff_rightInvariantComplexDerivative f Y⟩

@[simp]
theorem smoothRightInvariantComplexDerivative_apply
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    smoothRightInvariantComplexDerivative f Y g = rightInvariantComplexDerivative f Y g :=
  rfl

/-- Taking real parts commutes with the ordered second derivative (`X` after `Y`). -/
theorem rightInvariantScalarSecondDerivative_realPart
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative f.realPart X Y g =
      (rightInvariantComplexSecondDerivative f X Y g).re := by
  calc
    _ = rightInvariantScalarDerivative
        (smoothRightInvariantComplexDerivative f Y).realPart X g := by
      unfold rightInvariantScalarSecondDerivative
      congr 2
      funext q
      exact rightInvariantScalarDerivative_realPart f Y q
    _ = _ := rightInvariantScalarDerivative_realPart
      (smoothRightInvariantComplexDerivative f Y) X g

/-- Taking imaginary parts commutes with the ordered second derivative (`X` after `Y`). -/
theorem rightInvariantScalarSecondDerivative_imaginaryPart
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative f.imaginaryPart X Y g =
      (rightInvariantComplexSecondDerivative f X Y g).im := by
  calc
    _ = rightInvariantScalarDerivative
        (smoothRightInvariantComplexDerivative f Y).imaginaryPart X g := by
      unfold rightInvariantScalarSecondDerivative
      congr 2
      funext q
      exact rightInvariantScalarDerivative_imaginaryPart f Y q
    _ = _ := rightInvariantScalarDerivative_imaginaryPart
      (smoothRightInvariantComplexDerivative f Y) X g

/-- Taking real parts commutes with every finite-basis Laplacian. -/
theorem rightInvariantScalarLaplacianInBasis_realPart
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis f.realPart g =
      (rightInvariantComplexLaplacianInBasis basis f g).re := by
  unfold rightInvariantScalarLaplacianInBasis rightInvariantComplexLaplacianInBasis
  change (∑ a, rightInvariantScalarSecondDerivative f.realPart (basis a) (basis a) g) =
    Complex.reCLM (∑ a, rightInvariantComplexSecondDerivative f (basis a) (basis a) g)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact rightInvariantScalarSecondDerivative_realPart f (basis a) (basis a) g

/-- Taking imaginary parts commutes with every finite-basis Laplacian. -/
theorem rightInvariantScalarLaplacianInBasis_imaginaryPart
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis f.imaginaryPart g =
      (rightInvariantComplexLaplacianInBasis basis f g).im := by
  unfold rightInvariantScalarLaplacianInBasis rightInvariantComplexLaplacianInBasis
  change (∑ a, rightInvariantScalarSecondDerivative f.imaginaryPart (basis a) (basis a) g) =
    Complex.imCLM (∑ a, rightInvariantComplexSecondDerivative f (basis a) (basis a) g)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact rightInvariantScalarSecondDerivative_imaginaryPart f (basis a) (basis a) g

/-- Canonical real/complex coherence for pairing Laplacians normalized by the same invariant
pairing. Basis independence aligns the real basis with the selected complex basis. -/
noncomputable def rightInvariantPairingRealComplexLaplacianCoherenceData
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (realLaplacian : RightInvariantPairingLaplacianData inner)
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner) :
    RightInvariantPairingRealComplexLaplacianCoherenceData
      inner realLaplacian complexLaplacian where
  laplacian_realPart f g := by
    rw [realLaplacian.laplacian_eq_inBasis complexLaplacian.orthonormalBasis]
    change rightInvariantScalarLaplacianInBasis
      complexLaplacian.orthonormalBasis.basis f.realPart g =
        (rightInvariantComplexLaplacianInBasis
          complexLaplacian.orthonormalBasis.basis f g).re
    exact rightInvariantScalarLaplacianInBasis_realPart
      complexLaplacian.orthonormalBasis.basis f g
  laplacian_imaginaryPart f g := by
    rw [realLaplacian.laplacian_eq_inBasis complexLaplacian.orthonormalBasis]
    change rightInvariantScalarLaplacianInBasis
      complexLaplacian.orthonormalBasis.basis f.imaginaryPart g =
        (rightInvariantComplexLaplacianInBasis
          complexLaplacian.orthonormalBasis.basis f g).im
    exact rightInvariantScalarLaplacianInBasis_imaginaryPart
      complexLaplacian.orthonormalBasis.basis f g

end

end Mathematics
end YangMills
