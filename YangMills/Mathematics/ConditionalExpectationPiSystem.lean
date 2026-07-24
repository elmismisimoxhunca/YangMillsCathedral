/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.PiSystem

/-!
# Conditional expectation from a generating pi-system

A reusable monotone-class bridge: equality of set integrals on a generating pi-system, together
with the total integral, determines a conditional expectation. This separates the generic analytic
closure argument from application-specific work identifying finite-cylinder generators.
-/

namespace YangMills.Mathematics

open MeasureTheory

noncomputable section

universe uα uE

variable {α : Type uα} {E : Type uE}
  {m m₀ : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Equality of integrals on a generating pi-system and on the whole space determines the
conditional expectation. The explicit whole-space hypothesis handles the complement step without
silently requiring the pi-system to contain `univ`. -/
theorem ae_eq_condExp_of_piSystem_setIntegral_eq
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : AEStronglyMeasurable[m] g μ)
    (generator : Set (Set α)) (generator_pi : IsPiSystem generator)
    (generator_eq : m = MeasurableSpace.generateFrom generator)
    (total_eq : ∫ x, g x ∂μ = ∫ x, f x ∂μ)
    (basic_eq : ∀ set, set ∈ generator → ∫ x in set, g x ∂μ = ∫ x in set, f x ∂μ) :
    g =ᵐ[μ] MeasureTheory.condExp m μ f := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro set _ _
    exact hg.integrableOn
  · intro set set_measurable _
    let C : ∀ set : Set α, @MeasurableSet α m set → Prop := fun set _ =>
      ∫ x in set, g x ∂μ = ∫ x in set, f x ∂μ
    refine MeasurableSpace.induction_on_inter (C := C) generator_eq generator_pi
      ?_ ?_ ?_ ?_ set set_measurable
    · simp [C]
    · intro basic basic_mem
      exact basic_eq basic basic_mem
    · intro set set_measurable set_eq
      have g_add := integral_add_compl (hm set set_measurable) hg
      have f_add := integral_add_compl (hm set set_measurable) hf
      dsimp only [C] at set_eq ⊢
      calc
        ∫ x in setᶜ, g x ∂μ = (∫ x, g x ∂μ) - ∫ x in set, g x ∂μ :=
          eq_sub_of_add_eq' g_add
        _ = (∫ x, f x ∂μ) - ∫ x in set, f x ∂μ := by rw [total_eq, set_eq]
        _ = ∫ x in setᶜ, f x ∂μ := (eq_sub_of_add_eq' f_add).symm
    · intro sets pairwise_disjoint sets_measurable sets_eq
      dsimp only [C] at sets_eq ⊢
      calc
        ∫ x in ⋃ i, sets i, g x ∂μ = ∑' i, ∫ x in sets i, g x ∂μ :=
          integral_iUnion (fun i => hm (sets i) (sets_measurable i))
            pairwise_disjoint hg.integrableOn
        _ = ∑' i, ∫ x in sets i, f x ∂μ := tsum_congr sets_eq
        _ = ∫ x in ⋃ i, sets i, f x ∂μ :=
          (integral_iUnion (fun i => hm (sets i) (sets_measurable i))
            pairwise_disjoint hf.integrableOn).symm
  · exact hgm

end

end YangMills.Mathematics
