/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupSelectedDualDensity
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientRealCore

/-!
# Realification of selected-dual coefficients through smooth representatives

A selected continuous unitary-dual class with an explicitly retained smooth representative can be
transported, with both change-of-basis matrices, to a finite coefficient synthesis in that smooth
presentation. Taking its real part then lands in the existing smooth real matrix-coefficient core.

This file does not assert that every continuous-dual class has a smooth representative, does not
identify raw coefficients across presentations, and proves no density or Peter--Weyl theorem.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- One selected-dual coefficient block whose class has a smooth representative has a real part in
the exact smooth real coefficient core. The witness retains the chosen smooth presentation and the
basis-aware pulled-back coefficient matrix. -/
theorem unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re := by
  obtain ⟨ρ, hρ⟩ := q.hasSmoothRepresentative_iff_exists_representation.mp hq
  subst q
  let equivalence := unitaryMatrixDualSelectedRepresentativeEquiv
    ρ.toContinuousUnitaryIrreducibleMatrixRepresentation
  let pulledBack := representationEquivPullbackCoefficientMatrix equivalence A
  refine ⟨smoothUnitaryMatrixCoefficientMatrixRealification ρ pulledBack,
    smoothUnitaryMatrixCoefficientMatrixRealification_mem_coreCandidate ρ pulledBack, ?_⟩
  intro g
  rw [smoothUnitaryMatrixCoefficientMatrixRealification_apply,
    unitaryMatrixDualCoefficientSynthesis_single]
  congr 1
  exact (representationEquiv_weightedMatrixCoefficientSum
    ρ.representation
    (unitaryMatrixDualRepresentation
      (unitaryMatrixDualClass ρ.toContinuousUnitaryIrreducibleMatrixRepresentation))
    equivalence A g).symm

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Continuous-image form of selected-block realification. -/
theorem unitaryMatrixDualCoefficientSingle_realPart_mem_continuousSmoothRealCoreImage
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re := by
  obtain ⟨smoothFunction, hsmoothFunction, hpointwise⟩ :=
    unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore q hq A
  exact ⟨smoothLieGroupScalarToContinuousLinearMap smoothFunction,
    ⟨smoothFunction, hsmoothFunction, rfl⟩, hpointwise⟩

end

end Mathematics
end YangMills
