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

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The smooth imaginary part retains the exact underlying pointwise imaginary part. -/
theorem exact_smooth_imaginary_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    f.imaginaryPart g = (f g).im :=
  rfl

/-- The same-pairing coherence interface is canonically inhabited. -/
theorem exact_realComplexLaplacianCoherence_inhabited :
    Nonempty (RightInvariantPairingRealComplexLaplacianCoherenceData
      inner realLaplacian complexLaplacian) :=
  ⟨rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact first-derivative real-part coherence. -/
theorem exact_derivative_real_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f.realPart Y g =
      (rightInvariantComplexDerivative f Y g).re :=
  rightInvariantScalarDerivative_realPart f Y g

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact first-derivative imaginary-part coherence. -/
theorem exact_derivative_imaginary_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f.imaginaryPart Y g =
      (rightInvariantComplexDerivative f Y g).im :=
  rightInvariantScalarDerivative_imaginaryPart f Y g

/-- Exact smoothness probe for the complex directional derivative. -/
theorem exact_complexDerivative_smooth
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (fun g => rightInvariantComplexDerivative f Y g) :=
  contMDiff_rightInvariantComplexDerivative f Y

/-- Exact ordered-second-derivative real-part coherence. -/
theorem exact_secondDerivative_real_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative f.realPart X Y g =
      (rightInvariantComplexSecondDerivative f X Y g).re :=
  rightInvariantScalarSecondDerivative_realPart f X Y g

/-- Exact ordered-second-derivative imaginary-part coherence. -/
theorem exact_secondDerivative_imaginary_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative f.imaginaryPart X Y g =
      (rightInvariantComplexSecondDerivative f X Y g).im :=
  rightInvariantScalarSecondDerivative_imaginaryPart f X Y g

/-- Exact finite-basis real-part coherence. -/
theorem exact_laplacianInBasis_real_part
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis f.realPart g =
      (rightInvariantComplexLaplacianInBasis basis f g).re :=
  rightInvariantScalarLaplacianInBasis_realPart basis f g

/-- Exact finite-basis imaginary-part coherence. -/
theorem exact_laplacianInBasis_imaginary_part
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis f.imaginaryPart g =
      (rightInvariantComplexLaplacianInBasis basis f g).im :=
  rightInvariantScalarLaplacianInBasis_imaginaryPart basis f g

/-- Coherence uses the same invariant pairing and exact real part of the complex Laplacian. -/
theorem exact_laplacian_real_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    realLaplacian.laplacian f.realPart g =
      (complexLaplacian.laplacian f g).re :=
  (rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian).laplacian_realPart f g

/-- Pairing coherence also uses the exact imaginary part of the complex Laplacian. -/
theorem exact_laplacian_imaginary_part
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G) :
    realLaplacian.laplacian f.imaginaryPart g =
      (complexLaplacian.laplacian f g).im :=
  (rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian).laplacian_imaginaryPart f g

/-- Hostile coherence probe: a changed real Laplacian value is contradictory. -/
theorem changed_laplacian_real_part_blocked
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G)
    (changed : ℝ) (hchanged : changed ≠ (complexLaplacian.laplacian f g).re)
    (changedReal : realLaplacian.laplacian f.realPart g = changed) : False := by
  apply hchanged
  rw [← changedReal]
  exact (rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian).laplacian_realPart f g

/-- Hostile imaginary-part coherence probe: a changed real Laplacian value is contradictory. -/
theorem changed_laplacian_imaginary_part_blocked
    (f : SmoothLieGroupComplexFunction (E := E) (G := G)) (g : G)
    (changed : ℝ) (hchanged : changed ≠ (complexLaplacian.laplacian f g).im)
    (changedReal : realLaplacian.laplacian f.imaginaryPart g = changed) : False := by
  apply hchanged
  rw [← changedReal]
  exact (rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian).laplacian_imaginaryPart f g

end

end Probes
end LieGroupRightInvariantRealComplexLaplacianCoherence
end Mathematics
end YangMills
