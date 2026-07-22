/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopConvolutionSemigroup
import YangMills.Geometry.LieGroup
import YangMills.Mathematics.LieGroupRightInvariantScalarLaplacian
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Same-density heat equation for the selected two-dimensional loop law

Driver Remark 4.13 identifies `Q_t` as the convolution kernel of the contraction semigroup solving
`∂ₜu = 1/2 Δu`. Sengupta Notation 4.7 and Remark 6.5 use the Laplacian induced by the selected
Ad-invariant Lie-algebra pairing and the same factor `1/2`.

This module requires a smooth strictly positive real representative of the **unchanged** `ENNReal`
density family, tied pointwise by `ENNReal.ofReal`, and requires its time derivative to equal one
half of the already defined right-invariant pairing Laplacian. The analytic core has compact
Lie-group scope. Connectedness is imposed by Driver's common Theorem 8.5 chain, while compact
simplicity is absent from the core.

This is still uninhabited acceptance data. It constructs no density, metric, solution, Brownian
motion, Yang--Mills measure, or theory. Brownian/generator identification remains a separate bridge
before the family is called the source heat kernel without qualification.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff
open YangMills.Mathematics

noncomputable section

universe uE uG uGauge uSample uConnection

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {Gauge : Type uGauge} [Group Gauge]
    {Sample : Type uSample} [MeasurableSpace Sample]
    {Connection : Type uConnection}

/-- Exact positive-time heat-equation requirements for the unchanged selected-loop density family.
This core uses precisely the compact Lie analytic ambient types needed by Driver; compact simplicity
is not an index. -/
structure TwoDimensionalSelectedLoopHeatEquationCoreData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    (law : TwoDimensionalSelectedLoopHaarDensityLawData base)
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)
    (laplacian : RightInvariantPairingLaplacianData inner) where
  /-- Real representative of the same density family, defined on all times for ordinary calculus. -/
  densityReal : ℝ → G → ℝ
  /-- Positive-time spatial smoothness on the exact Lie-group manifold. -/
  densityReal_spatialSmooth : ∀ t, 0 < t →
    ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞ (densityReal t)
  /-- Strict source positivity at every positive time and group element. -/
  densityReal_pos : ∀ t, 0 < t → ∀ g, 0 < densityReal t g
  /-- Pointwise bridge to the unchanged `ENNReal` density used by the selected-loop law and
  convolution semigroup. -/
  densityReal_toENNReal : ∀ t, 0 < t → ∀ g,
    ENNReal.ofReal (densityReal t g) = law.selectedAreaDensity t g
  /-- Driver's exact sign and factor convention `∂ₜQ = 1/2 ΔQ`. -/
  heatEquation : ∀ t (ht : 0 < t) g,
    HasDerivAt (fun s => densityReal s g)
      ((1 / 2 : ℝ) * laplacian.laplacian
        ({ toFun := densityReal t,
           contMDiff := densityReal_spatialSmooth t ht } :
          SmoothLieGroupScalarFunction (E := E) (G := G)) g) t

namespace TwoDimensionalSelectedLoopHeatEquationCoreData

variable
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}

/-- Bundled smooth spatial density at one exact positive time. -/
noncomputable def smoothDensityAt
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) : SmoothLieGroupScalarFunction (E := E) (G := G) where
  toFun := data.densityReal t
  contMDiff := data.densityReal_spatialSmooth t ht

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
@[simp]
theorem smoothDensityAt_apply
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    data.smoothDensityAt t ht g = data.densityReal t g :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The stored heat equation is exposed through the exact bundled smooth spatial density. -/
theorem hasDerivAt_densityReal
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    HasDerivAt (fun s => data.densityReal s g)
      ((1 / 2 : ℝ) * laplacian.laplacian (data.smoothDensityAt t ht) g) t :=
  data.heatEquation t ht g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Strict positivity supplies the nonnegative premise needed by the exact `ENNReal` bridge. -/
theorem densityReal_nonnegative
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) : 0 ≤ data.densityReal t g :=
  (data.densityReal_pos t ht g).le

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The smooth real representative inherits conjugation centrality from the unchanged density law. -/
theorem densityReal_central
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (h g : G) :
    data.densityReal t (h * g * h⁻¹) = data.densityReal t g := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (data.densityReal_nonnegative t ht (h * g * h⁻¹))
    (data.densityReal_nonnegative t ht g)).mp
  rw [data.densityReal_toENNReal t ht, data.densityReal_toENNReal t ht]
  exact law.selectedAreaDensity_central t ht h g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The smooth real representative inherits inversion symmetry from the unchanged density law. -/
theorem densityReal_inv
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) :
    data.densityReal t g⁻¹ = data.densityReal t g := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (data.densityReal_nonnegative t ht g⁻¹)
    (data.densityReal_nonnegative t ht g)).mp
  rw [data.densityReal_toENNReal t ht, data.densityReal_toENNReal t ht]
  exact law.selectedAreaDensity_inv t ht g

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- A positive-time real density value cannot be zero. -/
theorem densityReal_ne_zero
    (data : TwoDimensionalSelectedLoopHeatEquationCoreData
      inner law semigroup laplacian)
    (t : ℝ) (ht : 0 < t) (g : G) : data.densityReal t g ≠ 0 :=
  ne_of_gt (data.densityReal_pos t ht g)

end TwoDimensionalSelectedLoopHeatEquationCoreData

end

end YangMills.Dimensions
