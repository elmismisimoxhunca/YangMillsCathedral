/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLevyFurtherConditioning

/-!
# Hostile probes for Lévy sewing under further conditioning
-/

namespace YangMills.Dimensions.TwoDimensionalLevyFurtherConditioning.Probes

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uG uLB uRB uWB uLL uRL uWL uLS uRS uWS

/-- Zero blocks represent no extra condition without fabricating an empty joint conjugacy class. -/
def emptyFixedBaseBlockCollection {Base : Type uLB} (LoopAt : Base → Type uLL) :
    YangMills.Mathematics.FiniteFixedBaseBlockCollection LoopAt where
  blockCount := 0
  block := Fin.elim0
  base_injective := fun index => Fin.elim0 index

variable
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL] {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER] {HR : Type uHR} [TopologicalSpace HR]
    {SR : Type uSR} [TopologicalSpace SR] [MeasurableSpace SR] [BorelSpace SR]
    {IR : ModelWithCorners ℝ ER HR} [ChartedSpace HR SR] [IsManifold IR ∞ SR]
    [CompactSpace SR] [T2Space SR] [SecondCountableTopology SR]
    {leftSurface : YangMills.Geometry.CompactOrientedMeasuredSurfaceData IL SL}
    {leftPresentation : YangMills.Geometry.CompactSurfaceBoundaryCirclePresentationData leftSurface}
    {leftOrientation : YangMills.Geometry.CompactSurfaceBoundaryOrientationData
      leftSurface leftPresentation}
    {rightSurface : YangMills.Geometry.CompactOrientedMeasuredSurfaceData IR SR}
    {rightPresentation : YangMills.Geometry.CompactSurfaceBoundaryCirclePresentationData rightSurface}
    {rightOrientation : YangMills.Geometry.CompactSurfaceBoundaryOrientationData
      rightSurface rightPresentation}
    {identification : YangMills.Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation}
    {G : Type uG} [Group G] [MeasurableSpace G]
    {LeftBase : Type uLB} {RightBase : Type uRB} {WholeBase : Type uWB}
    {LeftLoop : LeftBase → Type uLL} {RightLoop : RightBase → Type uRL}
    {WholeLoop : WholeBase → Type uWL}
    {LeftSample : Type uLS} [MeasurableSpace LeftSample]
    {RightSample : Type uRS} [MeasurableSpace RightSample]
    {WholeSample : Type uWS} [MeasurableSpace WholeSample]
    {data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)}

/-- A collection may contain many bases, but distinct blocks cannot split one base into separately
conjugated pieces. -/
theorem exact_distinct_block_bases
    (blocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop)
    {first second : Fin blocks.blockCount}
    (sameBase : (blocks.block first).1 = (blocks.block second).1) : first = second :=
  blocks.base_injective sameBase

/-- Every coordinate of the collection is exactly the selected positive fixed-base joint class. -/
theorem exact_block_observation
    (blocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop)
    (sample : LeftSample) (index : Fin blocks.blockCount) :
    YangMills.Mathematics.finiteFixedBaseBlockObservation data.leftHolonomy blocks sample index =
      YangMills.Mathematics.partitionedFixedBaseConjugacyObservation
        data.leftHolonomy (blocks.block index) sample :=
  rfl

/-- The enlarged condition is literally seam value plus all left and right fixed-base blocks on the
same restricted sewn sample. -/
theorem exact_enlarged_boundary_value
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks) (whole : WholeSample) :
    further.disintegration.boundaryValue whole =
      (data.disintegration.boundaryValue whole,
        YangMills.Mathematics.finiteFixedBaseBlockObservation
          data.leftHolonomy leftBlocks (data.disintegration.restriction whole).1,
        YangMills.Mathematics.finiteFixedBaseBlockObservation
          data.rightHolonomy rightBlocks (data.disintegration.restriction whole).2) :=
  further.boundaryValue_eq whole

/-- Further conditioning reconstructs the exact same sewn law and restriction. -/
theorem exact_same_law_and_restriction
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks) :
    further.disintegration.wholeMeasure = data.disintegration.wholeMeasure ∧
      further.disintegration.restriction = data.disintegration.restriction :=
  ⟨further.wholeMeasure_eq, further.restriction_eq⟩

/-- The all-value product law remains true for arbitrary finite collections of distinct fixed-base
blocks; each side kernel receives only its own full block tuple. -/
theorem exact_further_conditioned_product
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks)
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G)
    (leftValue : YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) leftBlocks)
    (rightValue : YangMills.Mathematics.finiteFixedBaseBlockObservationValue (G := G) rightBlocks) :
    Measure.map data.disintegration.restriction
        (further.disintegration.conditionedWhole (boundary, leftValue, rightValue)) =
      (further.conditionedLeft (boundary, leftValue)).prod
        (further.conditionedRight (levyBoundaryConjugacyReverse boundary, rightValue)) :=
  further.conditioned_restriction_product boundary leftValue rightValue

/-- An unrelated unconditional law cannot replace the same sewn law. -/
theorem unrelated_whole_law_blocked
    {leftBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection LeftLoop}
    {rightBlocks : YangMills.Mathematics.FiniteFixedBaseBlockCollection RightLoop}
    (further : TwoDimensionalLevyFurtherConditioningData (data := data)
      leftBlocks rightBlocks) (wrong : Measure WholeSample)
    (different : wrong ≠ data.disintegration.wholeMeasure)
    (claimed : further.disintegration.wholeMeasure = wrong) : False := by
  apply different
  rw [← claimed]
  exact further.wholeMeasure_eq

end

end YangMills.Dimensions.TwoDimensionalLevyFurtherConditioning.Probes
