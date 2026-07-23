/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCasimirLaplacianBridge

/-!
# Formal Laplacian series and explicit heat-equation interchange debt

The uniformly convergent coefficient-derivative series determines the formal Laplacian series with
coefficients

`-c_q dim(q) exp (-(t/2)c_q)`.

This file proves its weighted uniform convergence and the exact identity

`formalLaplacianSeries(t) = 2 • derivativeCandidateSeries(t)`.

It then isolates the two genuinely analytic interchanges still missing from the current development:
spatial smoothness plus passage of the geometric Laplacian through the infinite character series,
and pointwise differentiation of the original series with derivative equal to the already
constructed derivative-candidate series. These are fields of the uninhabited
`UnitaryMatrixDualCasimirHeatEquationInterchangeData`. From those exact fields the pointwise heat
equation `∂ₜK_t = 1/2 ΔK_t` is derived.

No interchange datum is constructed. Consequently this file does not prove an unconditional heat
equation, positivity, Haar normalization, a time-zero identity, or heat-kernel status.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Real formal Laplacian coefficient `-c_q` times the candidate heat coefficient. -/
noncomputable def unitaryMatrixDualCasimirHeatLaplacianCoefficientReal
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℝ :=
  -data.casimirWeight q * unitaryMatrixDualCasimirHeatCoefficientReal data t q

/-- Complex coercion of the formal Laplacian coefficient. -/
noncomputable def unitaryMatrixDualCasimirHeatLaplacianCoefficient
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) : ℂ :=
  (unitaryMatrixDualCasimirHeatLaplacianCoefficientReal data t q : ℂ)

/-- The formal Laplacian coefficient is exactly twice the coefficient derivative. -/
theorem unitaryMatrixDualCasimirHeatLaplacianCoefficient_eq_two_derivative
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q =
      2 * unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q := by
  unfold unitaryMatrixDualCasimirHeatLaplacianCoefficient
    unitaryMatrixDualCasimirHeatLaplacianCoefficientReal
    unitaryMatrixDualCasimirHeatDerivativeCoefficient
    unitaryMatrixDualCasimirHeatDerivativeCoefficientReal
  push_cast
  ring

/-- Exact weighted norm of the formal Laplacian coefficient in terms of the derivative weight. -/
theorem norm_unitaryMatrixDualCasimirHeatLaplacianCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ) =
      2 * (‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ)) := by
  rw [unitaryMatrixDualCasimirHeatLaplacianCoefficient_eq_two_derivative, norm_mul]
  norm_num
  ring

/-- Positive-time weighted uniform summability of the formal Laplacian coefficients. -/
theorem summable_norm_unitaryMatrixDualCasimirHeatLaplacianCoefficient_mul_dimension
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun q => ‖unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q‖ *
      (unitaryMatrixDualDimension q : ℝ)) := by
  have h : Summable (fun q => 2 *
      (‖unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q‖ *
        (unitaryMatrixDualDimension q : ℝ))) :=
    (summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht).mul_left 2
  simpa only [norm_unitaryMatrixDualCasimirHeatLaplacianCoefficient_mul_dimension] using h

variable [CompactSpace G]

/-- Uniformly convergent formal Laplacian character series. -/
noncomputable def unitaryMatrixDualCasimirHeatLaplacianCharacterSeries
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (t : ℝ) : C(G, ℂ) :=
  unitaryMatrixDualUniformCharacterSeries
    (unitaryMatrixDualCasimirHeatLaplacianCoefficient data t)

/-- The formal Laplacian series is exactly twice the uniformly convergent derivative-candidate
series. -/
theorem unitaryMatrixDualCasimirHeatLaplacianCharacterSeries_eq_two_derivative
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    unitaryMatrixDualCasimirHeatLaplacianCharacterSeries data t =
      (2 : ℂ) • unitaryMatrixDualCasimirHeatDerivativeCharacterSeries data t := by
  unfold unitaryMatrixDualCasimirHeatLaplacianCharacterSeries
    unitaryMatrixDualCasimirHeatDerivativeCharacterSeries
  have hs := summable_unitaryMatrixDualContinuousCharacter_smul _
    (summable_norm_unitaryMatrixDualCasimirHeatDerivativeCoefficient_mul_dimension data ht)
  have hh : HasSum
      (fun q => unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      ((2 : ℂ) • ∑' q, unitaryMatrixDualCasimirHeatDerivativeCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q) := by
    convert hs.hasSum.const_smul (2 : ℂ) using 1
    · funext q
      rw [unitaryMatrixDualCasimirHeatLaplacianCoefficient_eq_two_derivative]
      module
  exact hh.tsum_eq

/-- Exact unconditional finite-subset convergence of the formal Laplacian series. -/
theorem tendsto_finsetSum_unitaryMatrixDualCasimirHeatLaplacianCharacter
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, unitaryMatrixDualCasimirHeatLaplacianCoefficient data t q •
        unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualCasimirHeatLaplacianCharacterSeries data t)) :=
  tendsto_finsetSum_unitaryMatrixDualContinuousCharacter _
    (summable_norm_unitaryMatrixDualCasimirHeatLaplacianCoefficient_mul_dimension data ht)

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Explicit remaining interchanges needed to promote the formal spectral identities to the actual
pointwise heat equation for the infinite series. This structure is uninhabited caller-supplied data. -/
structure UnitaryMatrixDualCasimirHeatEquationInterchangeData
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData) where
  heatSeries_contMDiff : ∀ (t : ℝ), 0 < t →
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℂ) ∞
      (unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t)
  laplacian_interchange : ∀ (t : ℝ) (ht : 0 < t) (g : G),
    laplacianData.laplacian
      { toFun := unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t
        contMDiff := heatSeries_contMDiff t ht } g =
      unitaryMatrixDualCasimirHeatLaplacianCharacterSeries heatTraceData t g
  timeDerivative_interchange : ∀ (t : ℝ) (_ht : 0 < t) (g : G),
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData s g)
      (unitaryMatrixDualCasimirHeatDerivativeCharacterSeries heatTraceData t g) t

namespace UnitaryMatrixDualCasimirHeatEquationInterchangeData

/-- The positive-time spectral series packaged with the spatial smoothness supplied by the
interchange data. -/
def smoothHeatCharacterSeries
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData}
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) : SmoothLieGroupComplexFunction (E := E) (G := G) :=
  ⟨unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData t,
    interchange.heatSeries_contMDiff t ht⟩

/-- Under exactly the two supplied infinite-series interchanges, the candidate spectral family
satisfies Driver's pointwise positive-time heat equation `∂ₜK_t = 1/2 ΔK_t`. -/
theorem hasDerivAt_heatCharacterSeries_eq_half_laplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {laplacianData : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    {bridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner laplacianData heatTraceData}
    (interchange : UnitaryMatrixDualCasimirHeatEquationInterchangeData bridge)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => unitaryMatrixDualCasimirHeatCharacterSeries heatTraceData s g)
      ((1 / 2 : ℂ) * laplacianData.laplacian
        (interchange.smoothHeatCharacterSeries t ht) g) t := by
  apply (interchange.timeDerivative_interchange t ht g).congr_deriv
  have hlap := interchange.laplacian_interchange t ht g
  change laplacianData.laplacian (interchange.smoothHeatCharacterSeries t ht) g =
    unitaryMatrixDualCasimirHeatLaplacianCharacterSeries heatTraceData t g at hlap
  have hseries := congrArg (fun f : C(G, ℂ) => f g)
    (unitaryMatrixDualCasimirHeatLaplacianCharacterSeries_eq_two_derivative
      heatTraceData ht)
  rw [hlap]
  change unitaryMatrixDualCasimirHeatDerivativeCharacterSeries heatTraceData t g =
    (1 / 2 : ℂ) * unitaryMatrixDualCasimirHeatLaplacianCharacterSeries heatTraceData t g
  rw [hseries]
  simp

end UnitaryMatrixDualCasimirHeatEquationInterchangeData

end

end Mathematics
end YangMills
