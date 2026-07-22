/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierConvolution

/-!
# Hostile probes for compact-group Fourier convolution
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixFourierConvolution
namespace Probes

noncomputable section

universe uG un

/-- Convolution retains the exact noncommutative source order `g(x⁻¹z)`. -/
theorem exact_convolution_order
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f g : G → ℂ) (z : G) :
    normalizedCompactHaarComplexConvolution G f g z =
      ∫ x, f x * g (x⁻¹ * z) ∂normalizedCompactHaarMeasure G :=
  rfl

/-- The Fourier transform reverses the two factors exactly; no matrix commutativity is used. -/
theorem exact_fourier_convolution_order
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f g : G → ℂ) (hf : Continuous f) (hg : Continuous g) :
    normalizedCompactMatrixFourierCoefficient G ρ
        (normalizedCompactHaarComplexConvolution G f g) =
      normalizedCompactMatrixFourierCoefficient G ρ g *
        normalizedCompactMatrixFourierCoefficient G ρ f :=
  normalizedCompactMatrixFourierCoefficient_convolution G ρ hρ f g hf hg

/-- Hostile order probe: a claim in the opposite order forces the two Fourier matrices to commute. -/
theorem opposite_order_requires_commutation
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f g : G → ℂ) (hf : Continuous f) (hg : Continuous g)
    (wrongOrder :
      normalizedCompactMatrixFourierCoefficient G ρ
          (normalizedCompactHaarComplexConvolution G f g) =
        normalizedCompactMatrixFourierCoefficient G ρ f *
          normalizedCompactMatrixFourierCoefficient G ρ g) :
    normalizedCompactMatrixFourierCoefficient G ρ g *
        normalizedCompactMatrixFourierCoefficient G ρ f =
      normalizedCompactMatrixFourierCoefficient G ρ f *
        normalizedCompactMatrixFourierCoefficient G ρ g := by
  rw [← wrongOrder]
  exact (normalizedCompactMatrixFourierCoefficient_convolution
    G ρ hρ f g hf hg).symm

end

end Probes
end CompactMatrixFourierConvolution
end Mathematics
end YangMills
