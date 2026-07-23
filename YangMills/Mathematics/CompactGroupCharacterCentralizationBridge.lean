/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCentralL2Span

/-!
# Exact bridge from full coefficient density to central character density

Hall's proof of character completeness centralizes a coefficient approximant by conjugation-Haar
averaging. The average fixes central functions, while Schur's lemma turns each averaged matrix block
into a finite character combination.

This file isolates exactly that remaining analytic bridge as
`CompactGroupCharacterCentralizationData`. Given such data, full selected-dual continuous density
implies compact-group uniform central character density, and hence the central normalized-Haar `L²`
completeness target. A faithful finite matrix representation supplies the full-density premise.

No centralization datum is constructed here. In particular, continuity of the function-valued Haar
average and its exact finite-character formula remain explicit obligations rather than hidden
assumptions.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- Exact data required from conjugation-Haar centralization: a continuous linear map onto central
functions, identity on that carrier, whose value on every finite selected-dual coefficient synthesis
is a finite selected-character synthesis. -/
structure CompactGroupCharacterCentralizationData
    (G : Type uG) [Group G] [TopologicalSpace G] [CompactSpace G] where
  centralization : C(G, ℂ) →L[ℂ] continuousCentralFunctionStarSubalgebra G
  fixes_central : ∀ f : continuousCentralFunctionStarSubalgebra G,
    centralization (f : C(G, ℂ)) = f
  maps_coefficient_synthesis : ∀ A : UnitaryMatrixDualCoefficientSpace G,
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      centralization (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
        unitaryMatrixDualCentralCharacterSynthesis G c

/-- The supplied centralization map is surjective because it fixes every central function. -/
theorem CompactGroupCharacterCentralizationData.centralization_surjective
    {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
    (data : CompactGroupCharacterCentralizationData G) :
    Function.Surjective data.centralization := by
  intro f
  exact ⟨(f : C(G, ℂ)), data.fixes_central f⟩

/-- Centralization fixes the constant function one exactly. -/
theorem CompactGroupCharacterCentralizationData.centralization_one
    {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
    (data : CompactGroupCharacterCentralizationData G) :
    data.centralization (1 : C(G, ℂ)) =
      (1 : continuousCentralFunctionStarSubalgebra G) :=
  data.fixes_central 1

/-- Exact abstract Hall bridge: full selected-dual continuous coefficient density plus a genuine
centralization map implies uniform finite-character density in the compact central carrier. -/
theorem UnitaryMatrixDual.HasContinuousPeterWeylDensity.hasCentralContinuousPeterWeylDensity
    {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G := by
  change DenseRange (unitaryMatrixDualCentralCharacterSynthesis G)
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  rw [← data.fixes_central f]
  have hf : (f : C(G, ℂ)) ∈ closure
      (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) := by
    have closure_eq := (show Dense (LinearMap.range
      (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) from density).closure_eq
    rw [closure_eq]
    trivial
  exact map_mem_closure data.centralization.continuous hf (by
    rintro y ⟨A, rfl⟩
    rcases data.maps_coefficient_synthesis A with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩)

/-- With a faithful finite matrix representation and explicit centralization data, finite selected
characters are uniformly dense among continuous central functions. -/
theorem unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful_of_centralization
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  (unitaryMatrixDual_hasContinuousPeterWeylDensity_of_faithful faithful)
    |>.hasCentralContinuousPeterWeylDensity data

/-- The same faithful-plus-centralization hypotheses imply the exact central normalized-Haar `L²`
closed-span target. -/
theorem unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful_of_centralization
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  (unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful_of_centralization
    faithful data).hasCentralL2PeterWeylCompleteness

end

end Mathematics
end YangMills
