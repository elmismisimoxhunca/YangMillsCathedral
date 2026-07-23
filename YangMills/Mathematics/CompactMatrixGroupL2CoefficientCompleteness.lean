/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupSelectedDualDensity

/-!
# Finite-support L² approximation and coefficient-test uniqueness

In the faithful compact matrix-group setting, the selected coordinate unitary dual has dense
finite-support coefficient synthesis in normalized-Haar `L²`. This file exposes three direct
consequences:

* the synthesis linear map has dense range;
* every `L²` vector admits arbitrarily close finite-support coefficient approximants;
* equality of inner products against every finite-support synthesized coefficient determines an
  `L²` vector uniquely.

These are exact Hilbert-space completeness consequences of the preceding conditional density
theorem. They do not construct an infinite Fourier series, a countable enumeration of the dual, or
pointwise inversion.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Under an explicit faithful finite matrix representation, finite-support selected-dual
coefficient synthesis has dense range in normalized-Haar `L²`. -/
theorem unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    DenseRange (unitaryMatrixDualL2CoefficientSynthesis G) := by
  change Dense (unitaryMatrixDualL2AlgebraicRange G : Set (NormalizedCompactHaarL2 G))
  rw [← unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense]
  exact unitaryMatrixDual_hasL2PeterWeylCompleteness_of_faithful faithful

/-- Every normalized-Haar `L²` vector is approximated within every positive tolerance by one
finite-support selected-dual coefficient synthesis. -/
theorem exists_unitaryMatrixDualL2CoefficientSynthesis_norm_sub_lt_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A, ‖unitaryMatrixDualL2CoefficientSynthesis G A - f‖ < ε := by
  rcases (unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful faithful).exists_dist_lt
      f hε with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rwa [← dist_eq_norm, dist_comm]

/-- If an `L²` vector pairs to zero with every finite-support selected-dual coefficient synthesis,
then the vector is zero. -/
theorem normalizedCompactHaarL2_eq_zero_of_inner_synthesis_eq_zero_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : NormalizedCompactHaarL2 G)
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f = 0) :
    f = 0 := by
  have functions_eq : (fun u : NormalizedCompactHaarL2 G => inner ℂ u f) =
      (fun _ => 0) := by
    apply (unitaryMatrixDualL2CoefficientSynthesis_denseRange_of_faithful faithful).equalizer
    · fun_prop
    · fun_prop
    · funext A
      exact h A
  have self_zero : inner ℂ f f = 0 := congrFun functions_eq f
  exact inner_self_eq_zero.mp self_zero

/-- Inner products against all finite-support selected-dual coefficient syntheses separate
normalized-Haar `L²` vectors. -/
theorem normalizedCompactHaarL2_eq_of_inner_synthesis_eq_of_faithful
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {f g : NormalizedCompactHaarL2 G}
    (h : ∀ A, inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) f =
      inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A) g) :
    f = g := by
  apply sub_eq_zero.mp
  apply normalizedCompactHaarL2_eq_zero_of_inner_synthesis_eq_zero_of_faithful faithful
  intro A
  rw [inner_sub_right, h, sub_self]

end

end Mathematics
end YangMills
