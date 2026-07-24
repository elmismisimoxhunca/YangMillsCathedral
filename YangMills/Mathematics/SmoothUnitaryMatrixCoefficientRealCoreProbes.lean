/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientRealCore

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact coordinate probe: no trace or transpose is inserted. -/
theorem exact_smoothMatrixCoefficient
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    smoothUnitaryMatrixCoefficient ρ row column g =
      ρ.representation g row column :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact component probe for both real scalar projections. -/
theorem exact_smoothMatrixCoefficient_components
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, column, .real⟩ g =
        (ρ.representation g row column).re ∧
      smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, column, .imaginary⟩ g =
        (ρ.representation g row column).im := by
  simp

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Conjugation mixes matrix rows and columns rather than being silently collapsed to a class
function law. -/
theorem exact_smoothMatrixCoefficient_conjugation
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g h : G) :
    smoothUnitaryMatrixCoefficient ρ row column (h * g * h⁻¹) =
      ∑ middle,
        (∑ left, ρ.representation h row left *
          ρ.representation g left middle) *
            ρ.representation h⁻¹ middle column :=
  smoothUnitaryMatrixCoefficient_conj ρ row column g h

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact range probe: every dependent coordinate component is in the finite synthesis range. -/
theorem exact_smoothMatrixCoefficient_mem_coreCandidate
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    smoothUnitaryMatrixCoefficientRealFunction index ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  smoothUnitaryMatrixCoefficientRealFunction_mem_coreCandidate index

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact carrier probe: the set candidate is the bundled algebraic submodule carrier. -/
theorem exact_smoothMatrixCoefficient_coreSubmodule_carrier :
    (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G) :
      Set (SmoothLieGroupScalarFunction (E := E) (G := G))) =
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  smoothUnitaryMatrixCoefficientRealCoreSubmodule_carrier

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The matrix-coefficient core candidate is closed under real linear combinations. -/
theorem exact_smoothMatrixCoefficient_coreCandidate_linear
    (c : ℝ) (f h : SmoothLieGroupScalarFunction (E := E) (G := G))
    (hf : f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G))
    (hh : h ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G)) :
    c • f + h ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) := by
  change c • f + h ∈ smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)
  exact (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).add_mem
    ((smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)).smul_mem c hf) hh

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact realification probe for a finite complex matrix-weighted smooth coefficient sum. -/
theorem exact_smoothMatrixCoefficient_matrixRealification
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (A : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) (g : G) :
    smoothUnitaryMatrixCoefficientMatrixRealification ρ A g =
      (smoothUnitaryMatrixCoefficientMatrixWeightedSum ρ A g).re ∧
    smoothUnitaryMatrixCoefficientRealSynthesis
        (smoothUnitaryMatrixCoefficientMatrixRealificationCoefficients ρ A) =
      smoothUnitaryMatrixCoefficientMatrixRealification ρ A ∧
    smoothLieGroupScalarToContinuousLinearMap
        (smoothUnitaryMatrixCoefficientMatrixRealification ρ A) ∈
      smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  ⟨smoothUnitaryMatrixCoefficientMatrixRealification_apply ρ A g,
    smoothUnitaryMatrixCoefficientRealSynthesis_realificationCoefficients ρ A,
    smoothUnitaryMatrixCoefficientMatrixRealification_mem_continuousCoreImage ρ A⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile realification probe: changing the exact real part is contradictory. -/
theorem changed_smoothMatrixCoefficient_matrixRealification_blocked
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (A : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      (smoothUnitaryMatrixCoefficientMatrixWeightedSum ρ A g).re)
    (claimed : smoothUnitaryMatrixCoefficientMatrixRealification ρ A g = changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (smoothUnitaryMatrixCoefficientMatrixRealification_apply ρ A g))

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- A supplied smooth representation makes the coefficient range genuinely nonzero. -/
theorem exact_smoothMatrixCoefficient_coreCandidate_nontrivial
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G), f ≠ 0 :=
  smoothUnitaryMatrixCoefficientRealCoreCandidate_nontrivial ρ

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact finite-synthesis linearity probe. -/
theorem exact_smoothMatrixCoefficient_synthesis_linearity
    (c : ℝ) (a b : SmoothUnitaryMatrixCoefficientRealCoefficients E G) :
    smoothUnitaryMatrixCoefficientRealSynthesis (c • a + b) =
      c • smoothUnitaryMatrixCoefficientRealSynthesis a +
        smoothUnitaryMatrixCoefficientRealSynthesis b := by
  rw [map_add, map_smul]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile coordinate probe: a genuinely changed row/column value cannot be accepted as the exact
coefficient. -/
theorem changed_smoothMatrixCoefficient_blocked
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) (changed : ℂ)
    (changed_ne_exact : changed ≠ ρ.representation g row column)
    (claimed : smoothUnitaryMatrixCoefficient ρ row column g = changed) : False := by
  apply changed_ne_exact
  rw [← claimed]
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile conjugation probe: replacing the exact mixed-coordinate value is contradictory. -/
theorem changed_smoothMatrixCoefficient_conjugation_blocked
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g h : G) (changed : ℂ)
    (changed_ne_exact : changed ≠
      ∑ middle,
        (∑ left, ρ.representation h row left *
          ρ.representation g left middle) *
            ρ.representation h⁻¹ middle column)
    (claimed : smoothUnitaryMatrixCoefficient ρ row column (h * g * h⁻¹) = changed) :
    False := by
  apply changed_ne_exact
  rw [← claimed]
  exact smoothUnitaryMatrixCoefficient_conj ρ row column g h

end

end Mathematics
end YangMills
