/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterProjectionConvergence

/-!
# Hostile probes for unconditional finite-character projection convergence
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterProjectionConvergence
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- Closed-span membership supplies a finite synthesis approximant at every positive tolerance. -/
theorem exact_closedSpan_approximation
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖unitaryMatrixDualL2CharacterSynthesis G c - f‖ < ε :=
  exists_unitaryMatrixDualL2CharacterSynthesis_norm_sub_lt_of_mem_closedSpan f hf hε

/-- The unconditional finite-subset projection net converges on the exact closed character span. -/
theorem exact_closedSpan_projection_net_convergence
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) :=
  tendsto_unitaryMatrixDualFiniteCharacterProjection_of_mem_closedSpan f hf

omit [T2Space G] in
/-- Hostile converse probe: convergence cannot place the limit outside the closed character span. -/
theorem convergent_projection_net_outside_closedSpan_blocked
    (f : NormalizedCompactHaarL2 G)
    (h : Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f))
    (outside : f ∉ unitaryMatrixDualL2CharacterClosedSpan G) : False :=
  outside (mem_unitaryMatrixDualL2CharacterClosedSpan_of_tendsto_projection f h)

/-- Exact closed-span criterion for unconditional projection-net convergence. -/
theorem exact_projection_net_convergence_iff_closedSpan
    (f : NormalizedCompactHaarL2 G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) ↔
      f ∈ unitaryMatrixDualL2CharacterClosedSpan G :=
  tendsto_unitaryMatrixDualFiniteCharacterProjection_iff_mem_closedSpan f

/-- Exact unconditional Parseval equality on the closed character span. -/
theorem exact_closedSpan_character_Parseval
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 = ‖f‖ ^ 2 :=
  tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_eq_of_mem_closedSpan f hf

/-- Hostile Parseval probe: changing the closed-span equality is contradictory. -/
theorem changed_closedSpan_character_Parseval_blocked
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G) {changed : ℝ}
    (hchanged : changed ≠ ‖f‖ ^ 2)
    (changedParseval : ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 = changed) : False := by
  apply hchanged
  rw [← changedParseval]
  exact tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_eq_of_mem_closedSpan f hf

/-- Central completeness is exactly projection-net convergence throughout the project's central
`L²` surrogate. -/
theorem exact_centralCompleteness_iff_projection_convergence :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G ↔
      ∀ f : NormalizedCompactHaarL2 G,
        f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G →
        Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
          unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) :=
  unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_iff_projection_tendsto

/-- A central-completeness inhabitant gives the exact continuous-central projection limit. -/
theorem exact_complete_continuousCentral_projection_limit
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s
        (normalizedCompactHaarCentralContinuousToL2 G f))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  complete.tendsto_continuousCentral f

/-- A central-completeness inhabitant gives exact Parseval for source-facing character integrals. -/
theorem exact_complete_continuousCentral_integral_Parseval
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 =
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 :=
  complete.continuousCentral_character_parseval f

variable [SecondCountableTopology G]

/-- Faithful finite matrix coordinates conditionally give the exact unconditional projection net. -/
theorem exact_faithful_continuousCentral_projection_limit
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s
        (normalizedCompactHaarCentralContinuousToL2 G f))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  tendsto_unitaryMatrixDualFiniteCharacterProjection_continuousCentral_of_faithful faithful f

/-- Faithful finite matrix coordinates conditionally give exact source-facing character Parseval. -/
theorem exact_faithful_continuousCentral_integral_Parseval
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 =
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 :=
  normalizedCompactHaar_continuousCentral_character_parseval_of_faithful faithful f

end

end Probes
end UnitaryMatrixDualCharacterProjectionConvergence
end Mathematics
end YangMills
