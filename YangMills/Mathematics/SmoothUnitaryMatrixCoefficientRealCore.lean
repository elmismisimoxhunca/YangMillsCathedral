/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantComplexLaplacian
import YangMills.Mathematics.SmoothLieGroupScalarFunctionLinear
import YangMills.Mathematics.SmoothUnitaryMatrixDual

/-!
# Real smooth matrix-coefficient core candidate

A bundled smooth irreducible unitary matrix representation supplies smooth complex matrix
coefficients and hence smooth real and imaginary parts. This file packages their dependent indices
and finite real synthesis in the full smooth scalar-function domain.

Unlike a character span, this coefficient range is not forced to be central. It is therefore the
appropriate algebraic shape for a future all-smooth graph core. This file does not quotient
coordinate presentations, assert coverage of the continuous unitary dual, prove uniform or graph
Peter--Weyl density, identify a Casimir eigenvalue, or prove heat-generator convergence.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- A smooth complex matrix coefficient of one explicitly bundled smooth irreducible unitary
representation. -/
def smoothUnitaryMatrixCoefficient
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) :
    SmoothLieGroupComplexFunction (E := E) (G := G) where
  toFun g := ρ.representation g row column
  contMDiff := by
    let evalRow : (Fin ρ.dimension → Fin ρ.dimension → ℂ) →L[ℝ]
        (Fin ρ.dimension → ℂ) := ContinuousLinearMap.proj row
    let evalEntry : (Fin ρ.dimension → ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.proj column
    exact evalEntry.contDiff.contMDiff.comp
      (evalRow.contDiff.contMDiff.comp ρ.representation_contMDiff)

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothUnitaryMatrixCoefficient_apply
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    smoothUnitaryMatrixCoefficient ρ row column g =
      ρ.representation g row column :=
  rfl

/-- The two real scalar components of a complex matrix coefficient. -/
inductive SmoothUnitaryMatrixCoefficientRealComponent
  | real
  | imaginary
  deriving DecidableEq

/-- A dependent index retaining the representation dimension, row, column, and real component. -/
structure SmoothUnitaryMatrixCoefficientRealIndex
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace E G] where
  representation : SmoothUnitaryIrreducibleMatrixRepresentation E G
  row : Fin representation.dimension
  column : Fin representation.dimension
  component : SmoothUnitaryMatrixCoefficientRealComponent

/-- Smooth real or imaginary part of an explicitly indexed smooth matrix coefficient. -/
def smoothUnitaryMatrixCoefficientRealFunction
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  match index.component with
  | .real =>
      (smoothUnitaryMatrixCoefficient index.representation index.row index.column).realPart
  | .imaginary =>
      (smoothUnitaryMatrixCoefficient index.representation index.row index.column).imaginaryPart

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothUnitaryMatrixCoefficientRealFunction_real_apply
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    smoothUnitaryMatrixCoefficientRealFunction
        ⟨ρ, row, column, .real⟩ g =
      (ρ.representation g row column).re :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothUnitaryMatrixCoefficientRealFunction_imaginary_apply
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g : G) :
    smoothUnitaryMatrixCoefficientRealFunction
        ⟨ρ, row, column, .imaginary⟩ g =
      (ρ.representation g row column).im :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact conjugation formula for the underlying complex coefficient. It deliberately retains the
full row/column mixing rather than asserting character-like centrality. -/
theorem smoothUnitaryMatrixCoefficient_conj
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row column : Fin ρ.dimension) (g h : G) :
    smoothUnitaryMatrixCoefficient ρ row column (h * g * h⁻¹) =
      ∑ middle,
        (∑ left, ρ.representation h row left *
          ρ.representation g left middle) *
            ρ.representation h⁻¹ middle column := by
  simp only [smoothUnitaryMatrixCoefficient_apply, map_mul, Matrix.mul_apply]

/-- Finite real coefficient carrier over the exact dependent smooth matrix-coordinate indices. -/
abbrev SmoothUnitaryMatrixCoefficientRealCoefficients
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace E G] :=
  SmoothUnitaryMatrixCoefficientRealIndex E G →₀ ℝ

/-- Canonical finite real matrix-coefficient synthesis in the smooth scalar domain. -/
noncomputable def smoothUnitaryMatrixCoefficientRealSynthesis :
    SmoothUnitaryMatrixCoefficientRealCoefficients E G →ₗ[ℝ]
      SmoothLieGroupScalarFunction (E := E) (G := G) :=
  Finsupp.linearCombination ℝ smoothUnitaryMatrixCoefficientRealFunction

/-- The explicit finite real smooth matrix-coefficient range. No density assertion is included. -/
def smoothUnitaryMatrixCoefficientRealCoreCandidate :
    Set (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  Set.range (smoothUnitaryMatrixCoefficientRealSynthesis (E := E) (G := G))

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The same finite real smooth matrix-coefficient range, bundled as an algebraic real
submodule. No topology or closure is installed on the smooth domain. -/
noncomputable def smoothUnitaryMatrixCoefficientRealCoreSubmodule :
    Submodule ℝ (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  LinearMap.range (smoothUnitaryMatrixCoefficientRealSynthesis (E := E) (G := G))

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The set-valued candidate and bundled algebraic submodule have exactly the same carrier. -/
@[simp]
theorem smoothUnitaryMatrixCoefficientRealCoreSubmodule_carrier :
    (smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G) :
      Set (SmoothLieGroupScalarFunction (E := E) (G := G))) =
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Membership in the bundled core is exactly finite real coefficient synthesis. -/
theorem mem_smoothUnitaryMatrixCoefficientRealCoreSubmodule_iff
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    f ∈ smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G) ↔
      ∃ coefficients : SmoothUnitaryMatrixCoefficientRealCoefficients E G,
        smoothUnitaryMatrixCoefficientRealSynthesis coefficients = f :=
  Iff.rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every individual real or imaginary matrix coefficient lies in the finite synthesis range. -/
theorem smoothUnitaryMatrixCoefficientRealFunction_mem_coreCandidate
    (index : SmoothUnitaryMatrixCoefficientRealIndex E G) :
    smoothUnitaryMatrixCoefficientRealFunction index ∈
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) := by
  classical
  refine ⟨Finsupp.single index 1, ?_⟩
  simp [smoothUnitaryMatrixCoefficientRealSynthesis]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every bundled smooth representation contributes a nonzero diagonal real coefficient. This
prevents the candidate range from collapsing once such a representation is supplied. -/
theorem smoothUnitaryMatrixCoefficientRealFunction_diagonal_real_ne_zero
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G)
    (row : Fin ρ.dimension) :
    smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, row, .real⟩ ≠ 0 := by
  intro equality
  have atIdentity := congrArg
    (fun f : SmoothLieGroupScalarFunction (E := E) (G := G) => f (1 : G)) equality
  simp at atIdentity

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The finite smooth matrix-coefficient range is nontrivial whenever one bundled smooth
representation is supplied. -/
theorem smoothUnitaryMatrixCoefficientRealCoreCandidate_nontrivial
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G), f ≠ 0 := by
  let row : Fin ρ.dimension := ⟨0, ρ.dimension_pos⟩
  exact ⟨smoothUnitaryMatrixCoefficientRealFunction ⟨ρ, row, row, .real⟩,
    smoothUnitaryMatrixCoefficientRealFunction_mem_coreCandidate _,
    smoothUnitaryMatrixCoefficientRealFunction_diagonal_real_ne_zero ρ row⟩

end

end Mathematics
end YangMills
