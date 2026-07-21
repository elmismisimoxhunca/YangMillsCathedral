/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator

/-!
# Probes for the selected-loop heat operator/kernel bridge
-/

namespace YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped Manifold ContDiff

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
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    {semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law}
    {laplacian : RightInvariantPairingLaplacianData inner}
    {heat : TwoDimensionalSelectedLoopHeatEquationData
      gaugeGroup inner law semigroup laplacian}
    (kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat)

/-- The designated semigroup starts at the identity operator. -/
theorem exact_operator_zero (f : C(G, ℝ)) : kernel.heatOperator 0 f = f :=
  kernel.heatOperator_zero f

/-- Nonnegative-time composition has the exact exponential-semigroup order. -/
theorem exact_operator_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : C(G, ℝ)) :
    kernel.heatOperator (s + t) f =
      kernel.heatOperator s (kernel.heatOperator t f) :=
  kernel.heatOperator_add s t hs ht f

/-- Its positive-time generator is exactly one half of the stored Definition 4.7 Laplacian. -/
theorem exact_operator_generator
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    HasDerivAt (fun s => kernel.heatOperator s f g)
      ((1 / 2 : ℝ) * laplacian.laplacian (kernel.positiveTimeSmooth t ht f) g) t :=
  kernel.heatOperator_hasDerivAt t ht f g

/-- Driver's operator-kernel identity uses the unchanged real density and canonical Haar measure. -/
theorem exact_kernel_integral
    (t : ℝ) (ht : 0 < t) (f : C(G, ℝ)) (g : G) :
    kernel.heatOperator t f g =
      ∫ h, heat.densityReal t (h⁻¹ * g) * f h ∂normalizedCompactHaarMeasure G :=
  kernel.heatOperator_eq_kernelIntegral t ht f g

/-- A zero designated semigroup is rejected by its identity initial value whenever the test function
is nonzero. -/
theorem zero_operator_blocked (f : C(G, ℝ)) (hf : f ≠ 0)
    (claimed : kernel.heatOperator 0 f = 0) : False :=
  hf (kernel.heatOperator_zero f ▸ claimed)

end

end YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator.Probes
