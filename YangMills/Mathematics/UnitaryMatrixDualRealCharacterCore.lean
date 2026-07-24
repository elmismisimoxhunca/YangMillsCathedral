/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantRealComplexLaplacianCoherence
import YangMills.Mathematics.SmoothLieGroupScalarFunctionLinear
import YangMills.Mathematics.UnitaryMatrixDualCasimirLaplacianBridge

/-!
# Real smooth selected-character core

A complex irreducible character supplies two real smooth tests: its real and imaginary parts. This
file packages both components, proves their exact pairing-Laplacian/Casimir eigenvalue equation, and
constructs their canonical finite-support real synthesis in the smooth scalar domain.

The resulting range is an explicit real smooth **central** character-core candidate. Every member is
proved conjugation-invariant, so this range is not proposed as a graph-dense core in the full smooth
function domain of a nonabelian group. No graph density, Peter–Weyl completeness, heat-quotient
bound, or closure theorem is asserted.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff BigOperators

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- The two real components of a complex selected character. -/
inductive UnitaryMatrixDualCharacterRealComponent
  | real
  | imaginary
  deriving DecidableEq

/-- Smooth real or imaginary part of one selected irreducible character. -/
def unitaryMatrixDualSmoothRealCharacterComponent
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  match component with
  | .real => (casimirBridge.smoothCharacter q).realPart
  | .imaginary => (casimirBridge.smoothCharacter q).imaginaryPart

@[simp]
theorem unitaryMatrixDualSmoothRealCharacterComponent_real_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .real g =
      (unitaryMatrixDualCharacter q g).re :=
  rfl

@[simp]
theorem unitaryMatrixDualSmoothRealCharacterComponent_imaginary_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .imaginary g =
      (unitaryMatrixDualCharacter q g).im :=
  rfl

/-- Both real character components have the exact Casimir eigenvalue for the real pairing
Laplacian. -/
theorem laplacian_unitaryMatrixDualSmoothRealCharacterComponent
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (realLaplacian : RightInvariantPairingLaplacianData inner)
    (complexLaplacian : RightInvariantPairingComplexLaplacianData inner)
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent)
    (g : G) :
    realLaplacian.laplacian
      (unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component) g =
      -(heatTraceData.casimirWeight q) *
        unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component g := by
  let coherence := rightInvariantPairingRealComplexLaplacianCoherenceData
    realLaplacian complexLaplacian
  cases component with
  | real =>
      rw [show realLaplacian.laplacian
        (unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .real) g =
          (complexLaplacian.laplacian (casimirBridge.smoothCharacter q) g).re from
        coherence.laplacian_realPart (casimirBridge.smoothCharacter q) g]
      rw [casimirBridge.laplacian_smoothCharacter]
      simp only [unitaryMatrixDualSmoothRealCharacterComponent_real_apply]
      simp [Complex.mul_re]
  | imaginary =>
      rw [show realLaplacian.laplacian
        (unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q .imaginary) g =
          (complexLaplacian.laplacian (casimirBridge.smoothCharacter q) g).im from
        coherence.laplacian_imaginaryPart (casimirBridge.smoothCharacter q) g]
      rw [casimirBridge.laplacian_smoothCharacter]
      simp only [unitaryMatrixDualSmoothRealCharacterComponent_imaginary_apply]
      simp [Complex.mul_im]

/-- Both real character components are conjugation-invariant. -/
theorem unitaryMatrixDualSmoothRealCharacterComponent_conj
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent)
    (g h : G) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component
        (h * g * h⁻¹) =
      unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component g := by
  cases component <;>
    simp [unitaryMatrixDualSmoothRealCharacterComponent,
      unitaryMatrixDualCharacter_conj]

/-- Finite real coefficient carrier for both components of every selected character. -/
abbrev UnitaryMatrixDualRealCharacterCoefficients (G : Type uG)
    [Group G] [TopologicalSpace G] :=
  (UnitaryMatrixDual G × UnitaryMatrixDualCharacterRealComponent) →₀ ℝ

/-- Canonical finite real selected-character synthesis in the smooth scalar domain. -/
noncomputable def unitaryMatrixDualSmoothRealCharacterSynthesis
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData) :
    UnitaryMatrixDualRealCharacterCoefficients G →ₗ[ℝ]
      SmoothLieGroupScalarFunction (E := E) (G := G) :=
  Finsupp.linearCombination ℝ (fun qc =>
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge qc.1 qc.2)

/-- Every finite real character synthesis is conjugation-invariant. -/
theorem unitaryMatrixDualSmoothRealCharacterSynthesis_conj
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (c : UnitaryMatrixDualRealCharacterCoefficients G) (g h : G) :
    unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge c (h * g * h⁻¹) =
      unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge c g := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add qc a c hqc ha induction =>
      simp only [map_add]
      change
        (unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge
            (Finsupp.single qc a)) (h * g * h⁻¹) +
            unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge c
              (h * g * h⁻¹) =
          (unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge
            (Finsupp.single qc a)) g +
            unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge c g
      rw [induction]
      congr 1
      simp only [unitaryMatrixDualSmoothRealCharacterSynthesis,
        Finsupp.linearCombination_single]
      exact congrArg (a * ·)
        (unitaryMatrixDualSmoothRealCharacterComponent_conj
          casimirBridge qc.1 qc.2 g h)

/-- The explicit real smooth central character core candidate is the range of finite synthesis. -/
def unitaryMatrixDualSmoothRealCharacterCore
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData) :
    Set (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  Set.range (unitaryMatrixDualSmoothRealCharacterSynthesis casimirBridge)

/-- Every individual real character component lies in the finite real smooth character core. -/
theorem unitaryMatrixDualSmoothRealCharacterComponent_mem_core
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (q : UnitaryMatrixDual G) (component : UnitaryMatrixDualCharacterRealComponent) :
    unitaryMatrixDualSmoothRealCharacterComponent casimirBridge q component ∈
      unitaryMatrixDualSmoothRealCharacterCore casimirBridge := by
  refine ⟨Finsupp.single (q, component) 1, ?_⟩
  simp [unitaryMatrixDualSmoothRealCharacterSynthesis]

/-- Every member of the real smooth character core candidate is central. -/
theorem unitaryMatrixDualSmoothRealCharacterCore_conj
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    {f : SmoothLieGroupScalarFunction (E := E) (G := G)}
    (hf : f ∈ unitaryMatrixDualSmoothRealCharacterCore casimirBridge)
    (g h : G) : f (h * g * h⁻¹) = f g := by
  obtain ⟨c, rfl⟩ := hf
  exact unitaryMatrixDualSmoothRealCharacterSynthesis_conj casimirBridge c g h

/-- A noncentral smooth function cannot belong to the central character synthesis range. -/
theorem not_mem_unitaryMatrixDualSmoothRealCharacterCore_of_not_central
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {complexLaplacian : RightInvariantPairingComplexLaplacianData inner}
    {heatTraceData : UnitaryMatrixDualHeatTraceSummabilityData (G := G)}
    (casimirBridge : UnitaryMatrixDualCasimirLaplacianBridgeData
      inner complexLaplacian heatTraceData)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hnot : ∃ g h : G, f (h * g * h⁻¹) ≠ f g) :
    f ∉ unitaryMatrixDualSmoothRealCharacterCore casimirBridge := by
  rintro hf
  obtain ⟨g, h, hne⟩ := hnot
  exact hne (unitaryMatrixDualSmoothRealCharacterCore_conj casimirBridge hf g h)

end

end Mathematics
end YangMills
