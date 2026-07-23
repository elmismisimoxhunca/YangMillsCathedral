/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalRepresentationInducedPairing
import YangMills.Dimensions.TwoDimensionalSelectedLoopHeatKernelOperator
import YangMills.Dimensions.TwoDimensionalVillainCommonHeatChain

/-!
# Common representation, Wilson action, pairing, Laplacian, and heat chain

This module closes the parameter-disconnection exposed by Driver Theorem 8.10: the faithful Wilson
matrix representation is the same smooth representation whose injective derivative defines the
invariant pairing, whose Laplacian generates the unchanged heat density attached to the continuum
holonomy nucleus. It still supplies no planar continuum expectation law or convergence theorem.
-/

namespace YangMills.Dimensions

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
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {law : TwoDimensionalSelectedLoopHaarDensityLawData base}
    (semigroup : TwoDimensionalSelectedLoopConvolutionSemigroupData law)

/-- One exact chain shared by Driver's continuum heat law and Wilson lattice actions. -/
structure TwoDimensionalWilsonCommonHeatChainData where
  group_connected : IsConnected (Set.univ : Set G)
  representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)
  representation_faithful : Function.Injective representation.representation
  normalization : TwoDimensionalWilsonNormalizerData
    representation.toFiniteDimensionalUnitaryRepresentationCharacterData
  inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ E) (G := G)
  pairing_coherence :
    TwoDimensionalRepresentationInducedPairingCoherenceData representation inner
  laplacian : RightInvariantPairingLaplacianData inner
  heat : TwoDimensionalSelectedLoopHeatEquationCoreData
    inner law semigroup laplacian
  kernel : TwoDimensionalSelectedLoopHeatKernelOperatorData heat

namespace TwoDimensionalWilsonCommonHeatChainData

/-- Forget only the genuinely stronger global representation faithfulness and Wilson normalization,
retaining the exact connected representation/differential-induced-pairing/Laplacian/heat/kernel
chain required by Driver's Villain Theorem 8.5. -/
noncomputable def toVillainCommonHeatChainCoreData
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup) :
    TwoDimensionalVillainCommonHeatChainCoreData (E := E) semigroup where
  group_connected := data.group_connected
  representation := data.representation
  inner := data.inner
  pairing_coherence := data.pairing_coherence
  laplacian := data.laplacian
  heat := data.heat
  kernel := data.kernel

/-- The Wilson family uses the exact same representation and normalization stored by the common
continuum heat chain. -/
def wilsonFamily
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup) :
    FaithfulWilsonActionFamilyData (G := G) where
  representationData :=
    data.representation.toFiniteDimensionalUnitaryRepresentationCharacterData
  normalization := data.normalization
  representation_faithful := data.representation_faithful

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Every Wilson action has the exact trace formula for the representation whose differential defines
`data.inner`. -/
theorem actionAt_formula
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (spacing : PositiveLatticeSpacing) (g : G) :
    (data.wilsonFamily semigroup |>.actionAt spacing).action g =
      (data.normalization.normalizer spacing)⁻¹ *
        Real.exp ((Matrix.trace (data.representation.representation g)).re) :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- The pairing driving the heat Laplacian is literally induced by the same Wilson representation. -/
theorem inner_pairing_eq_trace
    (data : TwoDimensionalWilsonCommonHeatChainData (E := E) semigroup)
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    data.inner.pairing first second =
      twoDimensionalRepresentationTracePairing data.representation first second :=
  data.pairing_coherence.pairing_eq_trace first second

end TwoDimensionalWilsonCommonHeatChainData

end

end YangMills.Dimensions
