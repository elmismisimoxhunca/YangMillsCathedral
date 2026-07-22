/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient
import YangMills.Mathematics.BoundaryConditionedProductDisintegration
import YangMills.Mathematics.PartitionedFixedBaseConjugacyObservation
import YangMills.Mathematics.SimultaneousConjugacyQuotientInversion

/-!
# Lévy compact-surface conditional-independence sewing contract

This file gives a source-specific, uninhabited acceptance record for Lévy's Theorem 5.1.1. It ties
the committed compact-surface boundary identification and topological gluing carrier to:

* exact holonomy-generated sigma fields on both pieces and the sewn sample carrier;
* literal restriction of piece holonomies from sewn samples;
* the positive family of seam loops indexed by the same geometric gluing pairs;
* boundary values in `(G / Ad)^p`, represented as a product of singleton simultaneous-conjugacy
  quotients;
* genuine conditional-kernel disintegration with an all-boundary-value product restriction; and
* the exact componentwise inverse conjugacy class on the second piece.

The two side sigma fields are not asserted to generate the sewn field; this would contradict Lévy's
nonabelian warning. No sample carrier, probability measure, Yang--Mills law, or theorem instance is
constructed.
-/

namespace YangMills.Dimensions

open MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uG uLeftBase uRightBase uWholeBase
  uLeftLoop uRightLoop uWholeLoop uLeftSample uRightSample uWholeSample

/-- Exact `p`-tuple of individual boundary conjugacy classes. Every coordinate is a singleton
simultaneous-conjugacy quotient, i.e. the literal `G / Ad` semantics. -/
abbrev LevyBoundaryConjugacyValue (pairCount : ℕ) (G : Type uG) [Group G] :=
  Fin pairCount → YangMills.Mathematics.SimultaneousConjugacyQuotient (Fin 1) G

/-- Componentwise inversion induced from pointwise group inversion on the exact quotient. -/
def levyBoundaryConjugacyReverse {pairCount : ℕ} {G : Type uG} [Group G] :
    LevyBoundaryConjugacyValue pairCount G → LevyBoundaryConjugacyValue pairCount G :=
  fun boundary pair => YangMills.Mathematics.simultaneousConjugacyInverse (boundary pair)

/-- The exact boundary reversal is involutive. -/
theorem levyBoundaryConjugacyReverse_involutive
    {pairCount : ℕ} {G : Type uG} [Group G] :
    Function.Involutive (levyBoundaryConjugacyReverse :
      LevyBoundaryConjugacyValue pairCount G → LevyBoundaryConjugacyValue pairCount G) := by
  intro boundary
  funext pair
  exact YangMills.Mathematics.simultaneousConjugacyInverse_involutive (boundary pair)

/-- Componentwise boundary reversal is measurable for the product of exact final quotient sigma
fields. -/
theorem levyBoundaryConjugacyReverse_measurable
    {pairCount : ℕ} {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableInv G] :
    Measurable (levyBoundaryConjugacyReverse :
      LevyBoundaryConjugacyValue pairCount G → LevyBoundaryConjugacyValue pairCount G) := by
  apply measurable_pi_iff.mpr
  intro pair
  exact YangMills.Mathematics.simultaneousConjugacyInverse_measurable.comp
    (measurable_pi_apply pair)

variable
    {EL : Type uEL} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [FiniteDimensional ℝ EL]
    [MeasurableSpace EL] [BorelSpace EL]
    {HL : Type uHL} [TopologicalSpace HL]
    {SL : Type uSL} [TopologicalSpace SL] [MeasurableSpace SL] [BorelSpace SL]
    {IL : ModelWithCorners ℝ EL HL} [ChartedSpace HL SL] [IsManifold IL ∞ SL]
    [CompactSpace SL] [T2Space SL] [SecondCountableTopology SL]
    {ER : Type uER} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
    [MeasurableSpace ER] [BorelSpace ER]
    {HR : Type uHR} [TopologicalSpace HR]
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
    {LeftBase : Type uLeftBase} {RightBase : Type uRightBase} {WholeBase : Type uWholeBase}
    {LeftLoop : LeftBase → Type uLeftLoop} {RightLoop : RightBase → Type uRightLoop}
    {WholeLoop : WholeBase → Type uWholeLoop}
    {LeftSample : Type uLeftSample} [MeasurableSpace LeftSample]
    {RightSample : Type uRightSample} [MeasurableSpace RightSample]
    {WholeSample : Type uWholeSample} [MeasurableSpace WholeSample]

/-- Uninhabited source-facing contract for Lévy Theorem 5.1.1 over the exact geometric gluing data. -/
structure TwoDimensionalLevyCompactSurfaceSewingData where
  /-- Holonomy functions on the two pieces and on the sewn carrier. -/
  leftHolonomy : ∀ base, LeftLoop base → LeftSample → G
  rightHolonomy : ∀ base, RightLoop base → RightSample → G
  wholeHolonomy : ∀ base, WholeLoop base → WholeSample → G
  /-- Exact geometric traces. Raw `G`-valued holonomies are deliberately not required measurable:
  only their joint conjugacy classes are observables on Lévy's quotient sample spaces. -/
  leftBasePoint : LeftBase → SL
  rightBasePoint : RightBase → SR
  wholeBasePoint : WholeBase →
    YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient identification
  /-- Base labels represent geometric points exactly: distinct labels cannot split loops based at
  one actual point into source-false independently conjugated fibers. -/
  leftBasePoint_injective : Function.Injective leftBasePoint
  rightBasePoint_injective : Function.Injective rightBasePoint
  wholeBasePoint_injective : Function.Injective wholeBasePoint
  leftLoopTrace : ∀ base, LeftLoop base → Circle → SL
  rightLoopTrace : ∀ base, RightLoop base → Circle → SR
  wholeLoopTrace : ∀ base, WholeLoop base → Circle →
    YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient identification
  /-- Every dependent loop fiber is genuinely based at the geometric point named by its index. -/
  leftLoopTrace_based : ∀ base loop, leftLoopTrace base loop 1 = leftBasePoint base
  rightLoopTrace_based : ∀ base loop, rightLoopTrace base loop 1 = rightBasePoint base
  wholeLoopTrace_based : ∀ base loop, wholeLoopTrace base loop 1 = wholeBasePoint base
  /-- Exact source sigma fields generated by all positive-arity fixed-base joint holonomy classes. -/
  left_measurableSpace_eq_generated :
    (inferInstance : MeasurableSpace LeftSample) =
      YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace leftHolonomy
  right_measurableSpace_eq_generated :
    (inferInstance : MeasurableSpace RightSample) =
      YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace rightHolonomy
  whole_measurableSpace_eq_generated :
    (inferInstance : MeasurableSpace WholeSample) =
      YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace wholeHolonomy
  /-- Exact inclusions of piece loops into the sewn loop carrier. -/
  leftBaseInWhole : LeftBase → WholeBase
  rightBaseInWhole : RightBase → WholeBase
  leftBaseInWhole_point : ∀ base,
    wholeBasePoint (leftBaseInWhole base) =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (leftBasePoint base)
  rightBaseInWhole_point : ∀ base,
    wholeBasePoint (rightBaseInWhole base) =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.rightInclusion identification
        (rightBasePoint base)
  leftLoopInWhole : ∀ base, LeftLoop base → WholeLoop (leftBaseInWhole base)
  rightLoopInWhole : ∀ base, RightLoop base → WholeLoop (rightBaseInWhole base)
  leftLoopInWhole_trace : ∀ base loop circlePoint,
    wholeLoopTrace (leftBaseInWhole base) (leftLoopInWhole base loop) circlePoint =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (leftLoopTrace base loop circlePoint)
  rightLoopInWhole_trace : ∀ base loop circlePoint,
    wholeLoopTrace (rightBaseInWhole base) (rightLoopInWhole base loop) circlePoint =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.rightInclusion identification
        (rightLoopTrace base loop circlePoint)
  /-- Side seam loops and the sewn seam loop for every same exact geometric gluing pair. -/
  leftSeamBase : Fin identification.pairCount → LeftBase
  rightSeamBase : Fin identification.pairCount → RightBase
  leftSeamLoop : ∀ pair, LeftLoop (leftSeamBase pair)
  rightSeamLoop : ∀ pair, RightLoop (rightSeamBase pair)
  seamBase : Fin identification.pairCount → WholeBase
  seamLoop : ∀ pair, WholeLoop (seamBase pair)
  leftSeamLoop_trace : ∀ pair,
    leftLoopTrace (leftSeamBase pair) (leftSeamLoop pair) =
      leftPresentation.parameterization (identification.leftComponent pair)
  rightSeamLoop_trace : ∀ pair,
    rightLoopTrace (rightSeamBase pair) (rightSeamLoop pair) =
      rightPresentation.parameterization (identification.rightComponent pair)
  seamLoop_trace : ∀ pair circlePoint,
    wholeLoopTrace (seamBase pair) (seamLoop pair) circlePoint =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair circlePoint)
  /-- The right positive boundary loop is the opposite orientation of the sewn seam. -/
  rightSeamLoopInWhole_trace : ∀ pair circlePoint,
    wholeLoopTrace (rightBaseInWhole (rightSeamBase pair))
        (rightLoopInWhole (rightSeamBase pair) (rightSeamLoop pair))
        (identification.circleDiffeomorphism pair circlePoint) =
      wholeLoopTrace (seamBase pair) (seamLoop pair) circlePoint
  /-- Genuine disintegration and all-value product restriction law. -/
  disintegration : YangMills.Mathematics.BoundaryConditionedProductDisintegrationData
    (LevyBoundaryConjugacyValue identification.pairCount G)
    LeftSample RightSample WholeSample
  /-- Restricting a sewn sample preserves every exact piece holonomy. -/
  left_restriction_holonomy : ∀ base loop whole,
    leftHolonomy base loop (disintegration.restriction whole).1 =
      wholeHolonomy (leftBaseInWhole base) (leftLoopInWhole base loop) whole
  right_restriction_holonomy : ∀ base loop whole,
    rightHolonomy base loop (disintegration.restriction whole).2 =
      wholeHolonomy (rightBaseInWhole base) (rightLoopInWhole base loop) whole
  /-- The selected side seam holonomy **classes** are the left-oriented sewn class and its right-side
  inverse. Class equality, rather than false raw equality across different base points, is exact. -/
  leftSeamHolonomyClass_eq : ∀ pair whole,
    YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => leftHolonomy (leftSeamBase pair) (leftSeamLoop pair)
          (disintegration.restriction whole).1) =
      YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => wholeHolonomy (seamBase pair) (seamLoop pair) whole)
  rightSeamHolonomyClass_eq_inverse : ∀ pair whole,
    YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => rightHolonomy (rightSeamBase pair) (rightSeamLoop pair)
          (disintegration.restriction whole).2) =
      YangMills.Mathematics.simultaneousConjugacyInverse
        (YangMills.Mathematics.simultaneousConjugacyClass
          (fun _ : Fin 1 => wholeHolonomy (seamBase pair) (seamLoop pair) whole))
  /-- Boundary conditioning is literally the vector of the geometrically certified seam-loop
  conjugacy classes. -/
  boundaryValue_eq_seamHolonomy : ∀ whole pair,
    disintegration.boundaryValue whole pair =
      YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => wholeHolonomy (seamBase pair) (seamLoop pair) whole)
  /-- The abstract reversal in the reusable disintegration is exactly componentwise class inversion,
  giving `(t₁⁻¹, ..., tₚ⁻¹)` on the right side of equation (5.1). -/
  boundaryReverse_eq_inverse :
    disintegration.boundaryReverse = levyBoundaryConjugacyReverse

namespace TwoDimensionalLevyCompactSurfaceSewingData

/-- The same geometric positive pair count makes the boundary tuple genuinely positive-arity. -/
theorem boundary_pair_nonempty
    (_data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    Nonempty (Fin identification.pairCount) :=
  identification.pairIndex_nonempty

/-- The selected left seam base label is tied to an actual point of its selected boundary trace. -/
theorem leftSeamBasePoint_eq
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) :
    data.leftBasePoint (data.leftSeamBase pair) =
      leftPresentation.parameterization (identification.leftComponent pair) 1 := by
  rw [← data.leftLoopTrace_based (data.leftSeamBase pair) (data.leftSeamLoop pair)]
  exact congrFun (data.leftSeamLoop_trace pair) 1

/-- The selected right seam base label is tied to an actual point of its selected boundary trace. -/
theorem rightSeamBasePoint_eq
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) :
    data.rightBasePoint (data.rightSeamBase pair) =
      rightPresentation.parameterization (identification.rightComponent pair) 1 := by
  rw [← data.rightLoopTrace_based (data.rightSeamBase pair) (data.rightSeamLoop pair)]
  exact congrFun (data.rightSeamLoop_trace pair) 1

/-- The sewn seam base label is tied to the corresponding exact quotient boundary point. -/
theorem seamBasePoint_eq
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (pair : Fin identification.pairCount) :
    data.wholeBasePoint (data.seamBase pair) =
      YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
        (identification.leftBoundaryPoint pair 1) := by
  rw [← data.wholeLoopTrace_based (data.seamBase pair) (data.seamLoop pair)]
  exact data.seamLoop_trace pair 1

/-- The reusable product law specializes to literal inverse conjugacy classes on the right. -/
theorem conditioned_restriction_product_inverse
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map data.disintegration.restriction
        (data.disintegration.conditionedWhole boundary) =
      (data.disintegration.conditionedLeft boundary).prod
        (data.disintegration.conditionedRight (levyBoundaryConjugacyReverse boundary)) := by
  rw [← data.boundaryReverse_eq_inverse]
  exact data.disintegration.conditioned_restriction_product boundary

/-- Conditional left restriction marginal at every boundary value. -/
theorem conditioned_left_marginal
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map (fun whole => (data.disintegration.restriction whole).1)
        (data.disintegration.conditionedWhole boundary) =
      data.disintegration.conditionedLeft boundary :=
  data.disintegration.conditioned_left_marginal boundary

/-- Conditional right restriction marginal at the exact inverse boundary value. -/
theorem conditioned_right_marginal_inverse
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample))
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map (fun whole => (data.disintegration.restriction whole).2)
        (data.disintegration.conditionedWhole boundary) =
      data.disintegration.conditionedRight (levyBoundaryConjugacyReverse boundary) := by
  rw [← data.boundaryReverse_eq_inverse]
  exact data.disintegration.conditioned_right_marginal boundary

/-- The sewn whole law is probability normalized, derived from genuine disintegration. -/
theorem wholeMeasure_univ
    (data : TwoDimensionalLevyCompactSurfaceSewingData
      (identification := identification) (G := G) (LeftLoop := LeftLoop)
      (RightLoop := RightLoop) (WholeLoop := WholeLoop)
      (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)) :
    data.disintegration.wholeMeasure Set.univ = 1 :=
  data.disintegration.wholeMeasure_univ

end TwoDimensionalLevyCompactSurfaceSewingData

end

end YangMills.Dimensions
