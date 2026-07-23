/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCentralContinuousFunctions

/-!
# The normalized-Haar central L² character span

This file maps continuous central functions and finite-support selected character syntheses into
normalized-Haar `L²`. The closed span of continuous-central images is a project-level surrogate for
Lévy's literal space of central square-integrable functions: it avoids imposing pointwise equations
on almost-everywhere classes, and no equality with a separately defined AE-central carrier is
claimed. It defines:

* the closed `L²` span of finite character syntheses;
* the closed `L²` span of continuous central functions;
* `UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G`, asserting equality of those two exact
  subspaces.

Uniform central character density implies this `L²` target. Conversely, an inhabitant of the `L²`
target gives arbitrarily accurate finite-support character approximants to every vector in the
closed continuous-central subspace.

No general density inhabitant, countable character enumeration, infinite expansion, or pointwise
inversion is constructed.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Continuous map from the exact continuous-central carrier into normalized-Haar `L²`. -/
noncomputable def normalizedCompactHaarCentralContinuousToL2
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    continuousCentralFunctionStarSubalgebra G →L[ℂ] NormalizedCompactHaarL2 G :=
  (normalizedCompactHaarContinuousToL2 G).comp
    (Submodule.subtypeL (continuousCentralFunctionStarSubalgebra G).toSubmodule)

/-- Finite-support selected character synthesis in normalized-Haar `L²`. -/
noncomputable def unitaryMatrixDualL2CharacterSynthesis
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    UnitaryMatrixDualCharacterCoefficients G →ₗ[ℂ] NormalizedCompactHaarL2 G :=
  (normalizedCompactHaarCentralContinuousToL2 G).toLinearMap.comp
    (unitaryMatrixDualCentralCharacterSynthesis G)

/-- Algebraic finite-support selected-character range in normalized-Haar `L²`. -/
def unitaryMatrixDualL2CharacterAlgebraicRange
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Submodule ℂ (NormalizedCompactHaarL2 G) :=
  LinearMap.range (unitaryMatrixDualL2CharacterSynthesis G)

/-- Closed normalized-Haar `L²` span of finite-support selected-character synthesis. -/
def unitaryMatrixDualL2CharacterClosedSpan
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Submodule ℂ (NormalizedCompactHaarL2 G) :=
  (unitaryMatrixDualL2CharacterAlgebraicRange G).topologicalClosure

/-- `L²` range of all continuous central functions. -/
def normalizedCompactHaarContinuousCentralL2Range
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Submodule ℂ (NormalizedCompactHaarL2 G) :=
  LinearMap.range (normalizedCompactHaarCentralContinuousToL2 G).toLinearMap

/-- Closed normalized-Haar `L²` span of the continuous central functions. This avoids pretending
that pointwise conjugation invariance is directly defined on arbitrary almost-everywhere classes. -/
def normalizedCompactHaarContinuousCentralL2ClosedSpan
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Submodule ℂ (NormalizedCompactHaarL2 G) :=
  (normalizedCompactHaarContinuousCentralL2Range G).topologicalClosure

/-- Exact central normalized-Haar `L²` Peter–Weyl target: finite selected characters have the same
closed span as all continuous central functions. -/
def UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : Prop :=
  unitaryMatrixDualL2CharacterClosedSpan G =
    normalizedCompactHaarContinuousCentralL2ClosedSpan G

/-- Every finite character synthesis comes from a continuous central function. -/
theorem unitaryMatrixDualL2CharacterAlgebraicRange_le_continuousCentralRange
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    unitaryMatrixDualL2CharacterAlgebraicRange G ≤
      normalizedCompactHaarContinuousCentralL2Range G := by
  rintro f ⟨c, rfl⟩
  exact ⟨unitaryMatrixDualCentralCharacterSynthesis G c, rfl⟩

/-- Consequently, the closed character span is always contained in the closed
continuous-central span. -/
theorem unitaryMatrixDualL2CharacterClosedSpan_le_continuousCentralClosedSpan
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    unitaryMatrixDualL2CharacterClosedSpan G ≤
      normalizedCompactHaarContinuousCentralL2ClosedSpan G :=
  Submodule.topologicalClosure_mono
    unitaryMatrixDualL2CharacterAlgebraicRange_le_continuousCentralRange

/-- Compact-group uniform central character density implies central normalized-Haar `L²`
Peter–Weyl completeness. -/
theorem UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity.hasCentralL2PeterWeylCompleteness
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G := by
  apply le_antisymm
  · exact unitaryMatrixDualL2CharacterClosedSpan_le_continuousCentralClosedSpan
  · apply Submodule.topologicalClosure_minimal
      (normalizedCompactHaarContinuousCentralL2Range G)
    · rintro f ⟨centralFunction, rfl⟩
      have centralFunction_mem : centralFunction ∈ closure
          (LinearMap.range (unitaryMatrixDualCentralCharacterSynthesis G) :
            Set (continuousCentralFunctionStarSubalgebra G)) := by
        have closure_eq := (show Dense (LinearMap.range
          (unitaryMatrixDualCentralCharacterSynthesis G) :
          Set (continuousCentralFunctionStarSubalgebra G)) from density).closure_eq
        rw [closure_eq]
        trivial
      exact map_mem_closure (normalizedCompactHaarCentralContinuousToL2 G).continuous
        centralFunction_mem (by
          rintro y ⟨c, rfl⟩
          exact ⟨c, rfl⟩)
    · exact Submodule.isClosed_topologicalClosure _

/-- Central `L²` completeness gives one finite-support character approximant at every positive
tolerance for every vector in the closed continuous-central subspace. -/
theorem UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness.exists_character_approximation
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖unitaryMatrixDualL2CharacterSynthesis G c - f‖ < ε := by
  have hfclosure : f ∈ closure
      (unitaryMatrixDualL2CharacterAlgebraicRange G : Set (NormalizedCompactHaarL2 G)) := by
    change f ∈ unitaryMatrixDualL2CharacterClosedSpan G
    rw [complete]
    exact hf
  rw [Metric.mem_closure_iff] at hfclosure
  rcases hfclosure ε hε with ⟨y, hy, hd⟩
  rcases hy with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  rwa [← dist_eq_norm, dist_comm]

end

end Mathematics
end YangMills
