/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupConjugationCharacterFormula
import YangMills.Mathematics.UnitaryMatrixDualFiniteCharacterProjection

/-!
# Unconditional finite-character projection convergence

The finite selected-character projections form a net indexed by all finite subsets of the selected
dual, ordered by inclusion. This file proves that the net converges in normalized-Haar `L²` exactly
for vectors in the closed finite-character span. On that closed span, the unconditional character
coefficient `tsum` satisfies Parseval.

If the explicit central `L²` Peter–Weyl completeness target is inhabited, these results apply to the
project's closed continuous-central surrogate. In particular, for continuous central functions the
finite projection net converges and the exact integrals `∫ conj(χ_q)f` satisfy Parseval. The existing
faithful second-countable compact matrix-group theorem gives a conditional source-facing instance.

This is an unconditional finite-subset **net**, not a countably ordered series. It does not establish
global dual countability, pointwise or uniform inversion, an AE-central carrier identification, or
heat-kernel series convergence.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- Membership in the closed finite-character span gives a finite synthesis approximant at every
positive `L²` tolerance. -/
theorem exists_unitaryMatrixDualL2CharacterSynthesis_norm_sub_lt_of_mem_closedSpan
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖unitaryMatrixDualL2CharacterSynthesis G c - f‖ < ε := by
  have hf' : f ∈ closure
      (unitaryMatrixDualL2CharacterAlgebraicRange G : Set (NormalizedCompactHaarL2 G)) := hf
  rw [Metric.mem_closure_iff] at hf'
  rcases hf' ε hε with ⟨y, hy, hd⟩
  rcases hy with ⟨c, rfl⟩
  rw [dist_eq_norm] at hd
  exact ⟨c, by simpa [norm_sub_rev] using hd⟩

/-- The unconditional finite-character projection net converges to every vector in the closed
finite-character span. -/
theorem tendsto_unitaryMatrixDualFiniteCharacterProjection_of_mem_closedSpan
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨c, hc⟩ :=
    exists_unitaryMatrixDualL2CharacterSynthesis_norm_sub_lt_of_mem_closedSpan
      f hf (half_pos hε)
  refine ⟨c.support, ?_⟩
  intro s hs
  rw [dist_eq_norm]
  let y := unitaryMatrixDualL2CharacterSynthesis G c
  have hfix : unitaryMatrixDualFiniteCharacterProjection s y = y :=
    unitaryMatrixDualFiniteCharacterProjection_synthesis_of_support_subset s c hs
  calc
    ‖unitaryMatrixDualFiniteCharacterProjection s f - f‖ =
        ‖unitaryMatrixDualFiniteCharacterProjection s (f - y) + (y - f)‖ := by
          congr 1
          rw [map_sub, hfix]
          module
    _ ≤ ‖unitaryMatrixDualFiniteCharacterProjection s (f - y)‖ + ‖y - f‖ :=
      norm_add_le _ _
    _ ≤ ‖f - y‖ + ‖y - f‖ := add_le_add
      (norm_unitaryMatrixDualFiniteCharacterProjection_le s (f - y)) le_rfl
    _ = 2 * ‖y - f‖ := by
      rw [norm_sub_rev]
      ring
    _ < ε := by
      linarith

omit [T2Space G] in
/-- Conversely, convergence of the unconditional finite projection net forces membership in the
closed finite-character span. -/
theorem mem_unitaryMatrixDualL2CharacterClosedSpan_of_tendsto_projection
    (f : NormalizedCompactHaarL2 G)
    (h : Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f)) :
    f ∈ unitaryMatrixDualL2CharacterClosedSpan G := by
  apply (Submodule.isClosed_topologicalClosure
    (unitaryMatrixDualL2CharacterAlgebraicRange G)).mem_of_tendsto h
  filter_upwards [] with s
  apply Submodule.le_topologicalClosure (unitaryMatrixDualL2CharacterAlgebraicRange G)
  exact ⟨unitaryMatrixDualFiniteCharacterProjectionCoefficients s f,
    (unitaryMatrixDualFiniteCharacterProjection_eq_synthesis s f).symm⟩

/-- Exact criterion: the unconditional finite projection net converges to `f` iff `f` belongs to the
closed finite-character span. -/
theorem tendsto_unitaryMatrixDualFiniteCharacterProjection_iff_mem_closedSpan
    (f : NormalizedCompactHaarL2 G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) ↔
      f ∈ unitaryMatrixDualL2CharacterClosedSpan G :=
  ⟨mem_unitaryMatrixDualL2CharacterClosedSpan_of_tendsto_projection f,
    tendsto_unitaryMatrixDualFiniteCharacterProjection_of_mem_closedSpan f⟩

/-- Exact unconditional Parseval equality on the whole closed finite-character span. -/
theorem tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_eq_of_mem_closedSpan
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ unitaryMatrixDualL2CharacterClosedSpan G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 = ‖f‖ ^ 2 := by
  have projectionTendsto :=
    tendsto_unitaryMatrixDualFiniteCharacterProjection_of_mem_closedSpan f hf
  have normTendsto := projectionTendsto.norm.pow 2
  have sumTendsto : Filter.Tendsto
      (fun s : Finset (UnitaryMatrixDual G) =>
        ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2)
      Filter.atTop
      (nhds (∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2)) :=
    (summable_norm_unitaryMatrixDualL2CharacterAnalysis_sq f).hasSum
  have projectionNormEq :
      (fun s : Finset (UnitaryMatrixDual G) =>
        ‖unitaryMatrixDualFiniteCharacterProjection s f‖ ^ 2) =
      fun s => ∑ q ∈ s, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 := by
    funext s
    exact norm_unitaryMatrixDualFiniteCharacterProjection_sq s f
  rw [projectionNormEq] at normTendsto
  exact tendsto_nhds_unique sumTendsto normTendsto

/-- Central `L²` completeness makes the finite projection net converge on the whole closed
continuous-central surrogate. -/
theorem UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness.tendsto_finiteCharacterProjection
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) := by
  apply tendsto_unitaryMatrixDualFiniteCharacterProjection_of_mem_closedSpan f
  rw [complete]
  exact hf

/-- Central `L²` completeness is equivalent to convergence of the unconditional finite projection
net on every vector in the closed continuous-central surrogate. -/
theorem unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_iff_projection_tendsto :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G ↔
      ∀ f : NormalizedCompactHaarL2 G,
        f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G →
        Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
          unitaryMatrixDualFiniteCharacterProjection s f) Filter.atTop (nhds f) := by
  constructor
  · intro complete f hf
    exact complete.tendsto_finiteCharacterProjection f hf
  · intro h
    apply le_antisymm
    · exact unitaryMatrixDualL2CharacterClosedSpan_le_continuousCentralClosedSpan
    · intro f hf
      exact mem_unitaryMatrixDualL2CharacterClosedSpan_of_tendsto_projection f (h f hf)

/-- Central `L²` completeness gives exact character Parseval on the closed continuous-central
surrogate. -/
theorem UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness.character_parseval
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G) :
    ∑' q, ‖unitaryMatrixDualL2CharacterAnalysis q f‖ ^ 2 = ‖f‖ ^ 2 := by
  apply tsum_norm_unitaryMatrixDualL2CharacterAnalysis_sq_eq_of_mem_closedSpan f
  rw [complete]
  exact hf

/-- Under central `L²` completeness, the finite projection net converges to every continuous central
function in normalized-Haar `L²`. -/
theorem UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness.tendsto_continuousCentral
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s
        (normalizedCompactHaarCentralContinuousToL2 G f))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) := by
  apply complete.tendsto_finiteCharacterProjection
  apply Submodule.le_topologicalClosure (normalizedCompactHaarContinuousCentralL2Range G)
  exact ⟨f, rfl⟩

/-- Source-facing conditional Parseval identity for a continuous central function. -/
theorem UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness.continuousCentral_character_parseval
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 =
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 := by
  have hf : normalizedCompactHaarCentralContinuousToL2 G f ∈
      normalizedCompactHaarContinuousCentralL2ClosedSpan G := by
    apply Submodule.le_topologicalClosure (normalizedCompactHaarContinuousCentralL2Range G)
    exact ⟨f, rfl⟩
  simpa only [unitaryMatrixDualL2CharacterAnalysis_continuousCentral_eq_integral] using
    complete.character_parseval (normalizedCompactHaarCentralContinuousToL2 G f) hf

/-- Faithful finite matrix coordinates plus second countability give unconditional finite-character
projection convergence for every continuous central function. -/
theorem tendsto_unitaryMatrixDualFiniteCharacterProjection_continuousCentral_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      unitaryMatrixDualFiniteCharacterProjection s
        (normalizedCompactHaarCentralContinuousToL2 G f))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  (unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful faithful).tendsto_continuousCentral f

/-- Faithful finite matrix coordinates plus second countability give exact unconditional character
Parseval for every continuous central function. -/
theorem normalizedCompactHaar_continuousCentral_character_parseval_of_faithful
    [SecondCountableTopology G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∑' q : UnitaryMatrixDual G,
      ‖∫ g, star (unitaryMatrixDualCharacter q g) * (f : C(G, ℂ)) g
        ∂normalizedCompactHaarMeasure G‖ ^ 2 =
      ‖normalizedCompactHaarCentralContinuousToL2 G f‖ ^ 2 :=
  (unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful faithful).continuousCentral_character_parseval f

end

end Mathematics
end YangMills
