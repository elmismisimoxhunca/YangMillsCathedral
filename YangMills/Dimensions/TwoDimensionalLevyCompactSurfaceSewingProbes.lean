/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing

/-!
# Hostile probes for Lévy compact-surface sewing
-/

namespace YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing.Probes

open MeasureTheory
open scoped Manifold ContDiff

noncomputable section

universe uEL uHL uSL uER uHR uSR uG uLB uRB uWB uLL uRL uWL uLS uRS uWS

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

abbrev SewingData
    (identification : YangMills.Geometry.CompactSurfaceBoundaryIdentification
      leftSurface leftPresentation leftOrientation rightSurface rightPresentation rightOrientation)
    (G : Type uG) [Group G] [MeasurableSpace G]
    (LeftBase : Type uLB) (RightBase : Type uRB) (WholeBase : Type uWB)
    (LeftLoop : LeftBase → Type uLL) (RightLoop : RightBase → Type uRL)
    (WholeLoop : WholeBase → Type uWL)
    (LeftSample : Type uLS) [MeasurableSpace LeftSample]
    (RightSample : Type uRS) [MeasurableSpace RightSample]
    (WholeSample : Type uWS) [MeasurableSpace WholeSample] :=
  TwoDimensionalLevyCompactSurfaceSewingData
    (identification := identification) (G := G) (LeftBase := LeftBase)
    (RightBase := RightBase) (WholeBase := WholeBase) (LeftLoop := LeftLoop)
    (RightLoop := RightLoop) (WholeLoop := WholeLoop)
    (LeftSample := LeftSample) (RightSample := RightSample) (WholeSample := WholeSample)

omit [MeasurableSpace G] in
/-- The boundary target is literally one individual conjugacy class for each exact geometric pair. -/
theorem exact_boundary_target :
    LevyBoundaryConjugacyValue identification.pairCount G =
      (Fin identification.pairCount →
        YangMills.Mathematics.SimultaneousConjugacyQuotient (Fin 1) G) :=
  rfl

/-- Geometry constructor-blocks an empty conditioning tuple. -/
theorem exact_positive_boundary_arity
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample) :
    Nonempty (Fin identification.pairCount) :=
  data.boundary_pair_nonempty

/-- Every sample sigma field is exactly its own full positive-arity fixed-base joint-holonomy field.
No equality between the join of the two side fields and the sewn field occurs here. -/
theorem exact_three_generated_fields
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample) :
    (inferInstance : MeasurableSpace LeftSample) =
        YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace data.leftHolonomy ∧
    (inferInstance : MeasurableSpace RightSample) =
        YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace data.rightHolonomy ∧
    (inferInstance : MeasurableSpace WholeSample) =
        YangMills.Mathematics.partitionedFixedBaseConjugacyGeneratedMeasurableSpace data.wholeHolonomy :=
  ⟨data.left_measurableSpace_eq_generated,
    data.right_measurableSpace_eq_generated,
    data.whole_measurableSpace_eq_generated⟩

/-- Restriction preserves exact group-valued holonomy on both pieces. -/
theorem exact_restriction_holonomy
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (leftBase : LeftBase) (leftLoop : LeftLoop leftBase)
    (rightBase : RightBase) (rightLoop : RightLoop rightBase) (whole : WholeSample) :
    data.leftHolonomy leftBase leftLoop (data.disintegration.restriction whole).1 =
        data.wholeHolonomy (data.leftBaseInWhole leftBase)
          (data.leftLoopInWhole leftBase leftLoop) whole ∧
      data.rightHolonomy rightBase rightLoop (data.disintegration.restriction whole).2 =
        data.wholeHolonomy (data.rightBaseInWhole rightBase)
          (data.rightLoopInWhole rightBase rightLoop) whole :=
  ⟨data.left_restriction_holonomy leftBase leftLoop whole,
    data.right_restriction_holonomy rightBase rightLoop whole⟩

/-- Base labels are exact: labels are equal precisely when their represented geometric points are
equal, so one actual basepoint cannot be split across independently conjugated fibers. -/
theorem exact_basepoint_label_recognition
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample) :
    (∀ first second : LeftBase,
      data.leftBasePoint first = data.leftBasePoint second ↔ first = second) ∧
    (∀ first second : RightBase,
      data.rightBasePoint first = data.rightBasePoint second ↔ first = second) ∧
    (∀ first second : WholeBase,
      data.wholeBasePoint first = data.wholeBasePoint second ↔ first = second) := by
  exact ⟨fun first second =>
      ⟨fun equality => data.leftBasePoint_injective equality, congrArg data.leftBasePoint⟩,
    fun first second =>
      ⟨fun equality => data.rightBasePoint_injective equality, congrArg data.rightBasePoint⟩,
    fun first second =>
      ⟨fun equality => data.wholeBasePoint_injective equality, congrArg data.wholeBasePoint⟩⟩

/-- Every loop fiber is genuinely based at the geometric point named by its dependent index; in
particular all selected seam base labels recover points on their exact boundary traces. -/
theorem exact_geometric_basepoint_semantics
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (leftBase : LeftBase) (leftLoop : LeftLoop leftBase)
    (rightBase : RightBase) (rightLoop : RightLoop rightBase)
    (wholeBase : WholeBase) (wholeLoop : WholeLoop wholeBase)
    (pair : Fin identification.pairCount) :
    data.leftLoopTrace leftBase leftLoop 1 = data.leftBasePoint leftBase ∧
      data.rightLoopTrace rightBase rightLoop 1 = data.rightBasePoint rightBase ∧
      data.wholeLoopTrace wholeBase wholeLoop 1 = data.wholeBasePoint wholeBase ∧
      data.leftBasePoint (data.leftSeamBase pair) =
        leftPresentation.parameterization (identification.leftComponent pair) 1 ∧
      data.rightBasePoint (data.rightSeamBase pair) =
        rightPresentation.parameterization (identification.rightComponent pair) 1 ∧
      data.wholeBasePoint (data.seamBase pair) =
        YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
          (identification.leftBoundaryPoint pair 1) :=
  ⟨data.leftLoopTrace_based leftBase leftLoop,
    data.rightLoopTrace_based rightBase rightLoop,
    data.wholeLoopTrace_based wholeBase wholeLoop,
    data.leftSeamBasePoint_eq pair,
    data.rightSeamBasePoint_eq pair,
    data.seamBasePoint_eq pair⟩

/-- Exact basepoint injectivity forces the included left seam base to be the designated sewn seam
base, and the included left loop has the same pointwise trace without reparameterization. -/
theorem derived_left_seam_inclusion_coherence
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    data.leftBaseInWhole (data.leftSeamBase pair) = data.seamBase pair ∧
      data.wholeLoopTrace (data.leftBaseInWhole (data.leftSeamBase pair))
          (data.leftLoopInWhole (data.leftSeamBase pair) (data.leftSeamLoop pair)) circlePoint =
        data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint :=
  ⟨data.leftSeamBaseInWhole_eq_seamBase pair,
    data.leftSeamLoopInWhole_trace pair circlePoint⟩

/-- A duplicate left included-seam base label is rejected by exact geometric base injectivity. -/
theorem duplicate_left_seam_base_blocked
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount)
    (wrong : data.leftBaseInWhole (data.leftSeamBase pair) ≠ data.seamBase pair) : False :=
  wrong (data.leftSeamBaseInWhole_eq_seamBase pair)

/-- The selected side and sewn seam traces are tied to the exact geometric components and quotient
identifications, not merely indexed by the same cardinality. -/
theorem exact_geometric_seam_incidence
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    data.leftLoopTrace (data.leftSeamBase pair) (data.leftSeamLoop pair) circlePoint =
        leftPresentation.parameterization (identification.leftComponent pair) circlePoint ∧
      data.rightLoopTrace (data.rightSeamBase pair) (data.rightSeamLoop pair) circlePoint =
        rightPresentation.parameterization (identification.rightComponent pair) circlePoint ∧
      data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint =
        YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.leftInclusion identification
          (identification.leftBoundaryPoint pair circlePoint) ∧
      data.wholeLoopTrace (data.rightBaseInWhole (data.rightSeamBase pair))
          (data.rightLoopInWhole (data.rightSeamBase pair) (data.rightSeamLoop pair))
          (identification.circleDiffeomorphism pair circlePoint) =
        data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint := by
  exact ⟨congrFun (data.leftSeamLoop_trace pair) circlePoint,
    congrFun (data.rightSeamLoop_trace pair) circlePoint,
    data.seamLoop_trace pair circlePoint,
    data.rightSeamLoopInWhole_trace pair circlePoint⟩

/-- The sewn seam trace lands in the exact pre-descent seam set, not in the retained boundary
candidate; its dependent base label has the same exact incidence. -/
theorem exact_seam_set_incidence
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) (circlePoint : Circle) :
    data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint ∈
        YangMills.Geometry.compactSurfaceBoundaryGluingSeam
          (identification := identification) ∧
      data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint ∉
        YangMills.Geometry.compactSurfaceBoundaryGluingRemainingBoundary
          (identification := identification) ∧
      data.wholeBasePoint (data.seamBase pair) ∈
        YangMills.Geometry.compactSurfaceBoundaryGluingSeam
          (identification := identification) :=
  ⟨data.seamLoopTrace_mem_gluingSeam pair circlePoint,
    data.seamLoopTrace_not_mem_remainingBoundary pair circlePoint,
    data.seamBasePoint_mem_gluingSeam pair⟩

/-- Both included side seam traces lie in the exact seam. The right statement covers an arbitrary
right parameter through the inverse designated circle diffeomorphism, while retaining its separate
dependent base label. -/
theorem exact_included_side_seam_set_incidence
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount)
    (leftCirclePoint rightCirclePoint : Circle) :
    data.wholeLoopTrace (data.leftBaseInWhole (data.leftSeamBase pair))
          (data.leftLoopInWhole (data.leftSeamBase pair) (data.leftSeamLoop pair))
          leftCirclePoint ∈
        YangMills.Geometry.compactSurfaceBoundaryGluingSeam
          (identification := identification) ∧
      data.wholeLoopTrace (data.rightBaseInWhole (data.rightSeamBase pair))
          (data.rightLoopInWhole (data.rightSeamBase pair) (data.rightSeamLoop pair))
          rightCirclePoint ∈
        YangMills.Geometry.compactSurfaceBoundaryGluingSeam
          (identification := identification) ∧
      data.wholeBasePoint (data.rightBaseInWhole (data.rightSeamBase pair)) ∈
        YangMills.Geometry.compactSurfaceBoundaryGluingSeam
          (identification := identification) :=
  ⟨data.leftSeamLoopInWholeTrace_mem_gluingSeam pair leftCirclePoint,
    data.rightSeamLoopInWholeTrace_mem_gluingSeam pair rightCirclePoint,
    data.rightSeamIncludedBasePoint_mem_gluingSeam pair⟩

/-- The right included base has two exact geometric descriptions, while its dependent label remains
separate from the left-oriented seam base. -/
theorem exact_right_included_seam_base_geometry
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) :
    data.wholeBasePoint (data.rightBaseInWhole (data.rightSeamBase pair)) =
        YangMills.Geometry.CompactSurfaceBoundaryGluingQuotient.rightInclusion identification
          (rightPresentation.parameterization (identification.rightComponent pair) 1) ∧
      data.wholeBasePoint (data.rightBaseInWhole (data.rightSeamBase pair)) =
        data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair)
          ((identification.circleDiffeomorphism pair).symm 1) :=
  ⟨data.rightSeamIncludedBasePoint_eq pair,
    data.rightSeamIncludedBasePoint_eq_reparameterizedSeamTrace pair⟩

/-- A source-false claim that a sewn seam trace point lies on retained boundary is rejected. -/
theorem sewn_seam_trace_retained_boundary_blocked
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) (circlePoint : Circle)
    (wrong : data.wholeLoopTrace (data.seamBase pair) (data.seamLoop pair) circlePoint ∈
      YangMills.Geometry.compactSurfaceBoundaryGluingRemainingBoundary
        (identification := identification)) : False :=
  data.seamLoopTrace_not_mem_remainingBoundary pair circlePoint wrong

/-- Side restrictions see the geometrically selected seam as the left-oriented conjugacy class and
its right-side inverse class; false raw equality across different base points is not required. -/
theorem exact_side_seam_holonomy_inverse
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (pair : Fin identification.pairCount) (whole : WholeSample) :
    YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => data.leftHolonomy (data.leftSeamBase pair) (data.leftSeamLoop pair)
          (data.disintegration.restriction whole).1) =
        YangMills.Mathematics.simultaneousConjugacyClass
          (fun _ : Fin 1 => data.wholeHolonomy (data.seamBase pair) (data.seamLoop pair) whole) ∧
      YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => data.rightHolonomy (data.rightSeamBase pair) (data.rightSeamLoop pair)
          (data.disintegration.restriction whole).2) =
        YangMills.Mathematics.simultaneousConjugacyInverse
          (YangMills.Mathematics.simultaneousConjugacyClass
            (fun _ : Fin 1 => data.wholeHolonomy (data.seamBase pair) (data.seamLoop pair) whole)) :=
  ⟨data.leftSeamHolonomyClass_eq pair whole,
    data.rightSeamHolonomyClass_eq_inverse pair whole⟩

/-- Conditioning is exactly by the conjugacy classes of the same geometrically certified positive
family of seam loops. -/
theorem exact_seam_boundary_value
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (whole : WholeSample) (pair : Fin identification.pairCount) :
    data.disintegration.boundaryValue whole pair =
      YangMills.Mathematics.simultaneousConjugacyClass
        (fun _ : Fin 1 => data.wholeHolonomy (data.seamBase pair)
          (data.seamLoop pair) whole) :=
  data.boundaryValue_eq_seamHolonomy whole pair

/-- The right factor receives literal componentwise class inversion, not an unrelated involution. -/
theorem exact_inverse_product_law
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map data.disintegration.restriction
        (data.disintegration.conditionedWhole boundary) =
      (data.disintegration.conditionedLeft boundary).prod
        (data.disintegration.conditionedRight (levyBoundaryConjugacyReverse boundary)) :=
  data.conditioned_restriction_product_inverse boundary

/-- Both source-facing conditional marginals derive at every boundary value. -/
theorem exact_inverse_marginals
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (boundary : LevyBoundaryConjugacyValue identification.pairCount G) :
    Measure.map (fun whole => (data.disintegration.restriction whole).1)
        (data.disintegration.conditionedWhole boundary) =
        data.disintegration.conditionedLeft boundary ∧
      Measure.map (fun whole => (data.disintegration.restriction whole).2)
        (data.disintegration.conditionedWhole boundary) =
        data.disintegration.conditionedRight (levyBoundaryConjugacyReverse boundary) :=
  ⟨data.conditioned_left_marginal boundary,
    data.conditioned_right_marginal_inverse boundary⟩

/-- An unrelated boundary involution cannot replace exact class inversion. -/
theorem unrelated_boundary_reverse_blocked
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample)
    (wrong : LevyBoundaryConjugacyValue identification.pairCount G →
      LevyBoundaryConjugacyValue identification.pairCount G)
    (different : wrong ≠ levyBoundaryConjugacyReverse)
    (claimed : data.disintegration.boundaryReverse = wrong) : False := by
  apply different
  rw [← claimed]
  exact data.boundaryReverse_eq_inverse

/-- No zero whole law can satisfy the genuine disintegration contract. -/
theorem zero_whole_law_blocked
    (data : SewingData identification G LeftBase RightBase WholeBase
      LeftLoop RightLoop WholeLoop LeftSample RightSample WholeSample) :
    data.disintegration.wholeMeasure ≠ 0 :=
  data.disintegration.wholeMeasure_ne_zero

end

end YangMills.Dimensions.TwoDimensionalLevyCompactSurfaceSewing.Probes
