/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupL2CoefficientCompleteness

/-!
# Hostile probes for conditional L² coefficient completeness
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixGroupL2CoefficientCompleteness
namespace Probes

noncomputable section

open MeasureTheory

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The actual finite-support selected-dual synthesis map has dense range. -/
theorem exact_dense_synthesis_range
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    DenseRange (unitaryMatrixDualL2CoefficientSynthesis G) :=
  unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful faithful

/-- Approximation uses one genuine finite-support dual coefficient datum at every positive scale. -/
theorem exact_finite_support_approximation
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : UnitaryMatrixDualCoefficientSpace G,
      ‖unitaryMatrixDualL2CoefficientSynthesis G A - f‖ < ε :=
  exists_unitaryMatrixDualL2CoefficientSynthesis_norm_sub_lt_of_faithful faithful f hε

/-- Hostile approximation probe: denying every finite-support approximant is contradictory. -/
theorem missing_finite_support_approximation_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G) {ε : ℝ} (hε : 0 < ε)
    (missing : ∀ A : UnitaryMatrixDualCoefficientSpace G,
      ε ≤ ‖unitaryMatrixDualL2CoefficientSynthesis G A - f‖) : False := by
  rcases exists_unitaryMatrixDualL2CoefficientSynthesis_norm_sub_lt_of_faithful
    faithful f hε with ⟨A, hA⟩
  exact (not_lt_of_ge (missing A)) hA

/-- Orthogonality to every finite-support synthesis forces exact zero. -/
theorem exact_zero_from_all_coefficient_tests
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G)
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f = 0) :
    f = 0 :=
  normalizedCompactHaarL2_eq_zero_of_inner_synthesis_eq_zero_of_faithful faithful f h

/-- Hostile zero probe: a nonzero vector cannot pass every zero coefficient test. -/
theorem nonzero_all_zero_coefficient_tests_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G) (hf : f ≠ 0)
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f = 0) : False :=
  hf (normalizedCompactHaarL2_eq_zero_of_inner_synthesis_eq_zero_of_faithful faithful f h)

/-- Equal coefficient tests force equality of the tested `L²` vectors. -/
theorem exact_equality_from_all_coefficient_tests
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {f g : NormalizedCompactHaarL2 G}
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f =
      inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) g) :
    f = g :=
  normalizedCompactHaarL2_eq_of_inner_synthesis_eq_of_faithful faithful h

/-- Hostile equality probe: distinct vectors cannot have all identical finite-support coefficient
tests. -/
theorem distinct_equal_coefficient_tests_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {f g : NormalizedCompactHaarL2 G} (hfg : f ≠ g)
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f =
      inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) g) : False :=
  hfg (normalizedCompactHaarL2_eq_of_inner_synthesis_eq_of_faithful faithful h)

end

end Probes
end CompactMatrixGroupL2CoefficientCompleteness
end Mathematics
end YangMills
