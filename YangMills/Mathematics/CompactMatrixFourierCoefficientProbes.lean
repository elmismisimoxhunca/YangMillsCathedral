/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixFourierCoefficient

/-!
# Hostile probes for compact matrix Fourier coefficients
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixFourierCoefficient
namespace Probes

open MeasureTheory

noncomputable section

universe uG un

/-- The convention retains the inverse representation matrix in every exact coefficient. -/
theorem exact_inverse_convention
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) (f : G → ℂ)
    (row column : n) :
    matrixFourierCoefficient μ ρ f row column =
      ∫ g, f g * ρ (g⁻¹) row column ∂μ :=
  rfl

/-- Continuity on a compact group supplies actual coefficient integrability. -/
theorem exact_integrability
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f : G → ℂ) (hf : Continuous f) (row column : n) :
    Integrable (fun g => f g * ρ (g⁻¹) row column) μ :=
  integrable_matrixFourierCoefficient_integrand μ ρ hρ f hf row column

/-- Matrix trace recovers the exact scalar inverse-character coefficient. -/
theorem exact_trace_character_bridge
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f : G → ℂ) (hf : Continuous f) :
    Matrix.trace (matrixFourierCoefficient μ ρ f) =
      ∫ g, f g * Matrix.trace (ρ (g⁻¹)) ∂μ :=
  matrixFourierCoefficient_trace μ ρ hρ f hf

/-- Addition is coefficientwise linear and uses the same representation. -/
theorem exact_additivity
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : G →* Matrix n n ℂ) (hρ : Continuous ρ)
    (f h : G → ℂ) (hf : Continuous f) (hh : Continuous h) :
    matrixFourierCoefficient μ ρ (fun g => f g + h g) =
      matrixFourierCoefficient μ ρ f + matrixFourierCoefficient μ ρ h :=
  matrixFourierCoefficient_add μ ρ hρ f h hf hh

/-- Hostile probe: the zero function cannot produce a nonzero Fourier matrix. -/
theorem zero_transform_exact
    {G : Type uG} [Group G] [MeasurableSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (μ : Measure G) (ρ : G →* Matrix n n ℂ) :
    matrixFourierCoefficient μ ρ (fun _ => 0) = 0 :=
  matrixFourierCoefficient_zero μ ρ

/-- Probability-normalized Haar measure is the exact compact-group specialization. -/
theorem exact_normalized_haar_specialization
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : Type un} [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n ℂ) (f : G → ℂ) :
    normalizedCompactMatrixFourierCoefficient G ρ f =
      matrixFourierCoefficient (normalizedCompactHaarMeasure G) ρ f :=
  rfl

end

end Probes
end CompactMatrixFourierCoefficient
end Mathematics
end YangMills
