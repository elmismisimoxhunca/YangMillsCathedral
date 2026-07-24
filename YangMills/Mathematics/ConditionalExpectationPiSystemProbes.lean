/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.ConditionalExpectationPiSystem

/-!
# Hostile probes for conditional expectation from a pi-system
-/

namespace YangMills.Mathematics

open MeasureTheory

noncomputable section

universe uα uE

variable {α : Type uα} {E : Type uE}
  {m m₀ : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
  {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
  (hgm : AEStronglyMeasurable[m] g μ)
  (generator : Set (Set α)) (generator_pi : IsPiSystem generator)
  (generator_eq : m = MeasurableSpace.generateFrom generator)
  (total_eq : ∫ x, g x ∂μ = ∫ x, f x ∂μ)
  (basic_eq : ∀ set, set ∈ generator → ∫ x in set, g x ∂μ = ∫ x in set, f x ∂μ)

include hm hf hg hgm generator generator_pi generator_eq total_eq basic_eq in
/-- Exact positive probe: a generating pi-system determines the conditional expectation. -/
theorem exact_piSystem_conditionalExpectation :
    g =ᵐ[μ] MeasureTheory.condExp m μ f :=
  ae_eq_condExp_of_piSystem_setIntegral_eq hm hf hg hgm generator generator_pi generator_eq
    total_eq basic_eq

include hm hf hg hgm generator generator_pi generator_eq total_eq basic_eq in
/-- Hostile probe: an a.e.-different replacement cannot satisfy the conclusion forced by the same
pi-system data. -/
theorem changed_piSystem_conditionalExpectation_blocked
    (changed : α → E)
    (changed_ne_exact : ¬ changed =ᵐ[μ] MeasureTheory.condExp m μ f)
    (claimed : g =ᵐ[μ] changed) : False :=
  changed_ne_exact (claimed.symm.trans
    (ae_eq_condExp_of_piSystem_setIntegral_eq hm hf hg hgm generator generator_pi generator_eq
      total_eq basic_eq))

end

end YangMills.Mathematics
