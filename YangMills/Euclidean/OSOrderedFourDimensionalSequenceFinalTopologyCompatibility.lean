/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Topology.CompactOpen
import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageContinuousLinear
import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceTopologicalAlgebra

/-!
# Algebraic compatibility of the exact-source final topology

The disjoint union of all exact finite stages maps surjectively to the exact OS source-sequence
carrier. This module proves that map is a quotient map for the named finite-stage final topology.
Because `ℂ` is locally compact, the quotient-product lifting theorem then proves joint continuity
of complex scalar multiplication. Negation follows. Addition of any two fixed finite stages factors
continuously through their union, which proves continuity in each sequence variable separately.

We deliberately do **not** package `ContinuousAdd` or `IsTopologicalAddGroup`: products of arbitrary
quotient maps need not be quotient maps, and the present proof does not establish that special
product property. A conditional theorem isolates exactly that remaining obstruction. Joint
addition, a topological-vector-space structure, local convexity, identification with OS-I's locally
convex direct sum, `(E2)`, and reconstruction remain open.
-/

namespace YangMills

noncomputable section

noncomputable local instance osSourceSpaceAddCommGroupForFinalCompatibility
    (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance osSourceSpaceModuleForFinalCompatibility
    (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance osSourceSpaceContinuousAddForFinalCompatibility
    (arity : PositiveArity) :
    ContinuousAdd (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousAdd arity

noncomputable local instance osSourceSpaceContinuousSMulForFinalCompatibility
    (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance osSourceSequenceTopologyForFinalCompatibility :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology

noncomputable local instance osSourceSequenceAddCommGroupForFinalCompatibility :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance osSourceSequenceModuleForFinalCompatibility :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- Disjoint union of all finite exact positive-arity source stages. -/
abbrev OSPositiveTimeOrderedFourDimensionalTotalStage :=
  Σ s : Finset PositiveArity, OSPositiveTimeOrderedFourDimensionalStage s

/-- Canonical map from the disjoint union of exact finite stages to source sequences. -/
def osPositiveTimeOrderedFourDimensionalTotalStageToSequence :
    OSPositiveTimeOrderedFourDimensionalTotalStage →
      OSPositiveTimeOrderedFourDimensionalTestSequence
  | ⟨s, x⟩ => osPositiveTimeOrderedFourDimensionalStageToSequence s x

/-- The total-stage map is continuous for the named final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalTotalStageToSequence :
    Continuous osPositiveTimeOrderedFourDimensionalTotalStageToSequence := by
  apply continuous_sigma
  intro s
  exact continuous_osPositiveTimeOrderedFourDimensionalStageToSequence s

/-- Every exact source sequence is represented by its actual-support stage. -/
theorem osPositiveTimeOrderedFourDimensionalTotalStageToSequence_surjective :
    Function.Surjective osPositiveTimeOrderedFourDimensionalTotalStageToSequence := by
  intro f
  exact ⟨⟨f.support, osPositiveTimeOrderedFourDimensionalSequenceToSupportStage f⟩,
    osPositiveTimeOrderedFourDimensionalStage_recover f⟩

/-- The named finite-stage final topology is exactly the quotient topology of the total-stage map. -/
theorem osPositiveTimeOrderedFourDimensionalTotalStageToSequence_isQuotientMap :
    Topology.IsQuotientMap osPositiveTimeOrderedFourDimensionalTotalStageToSequence := by
  refine ⟨⟨?_⟩, osPositiveTimeOrderedFourDimensionalTotalStageToSequence_surjective⟩
  apply le_antisymm
  · change osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology ≤ _
    unfold osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology
    apply iSup_le
    intro s
    change TopologicalSpace.coinduced
      (osPositiveTimeOrderedFourDimensionalTotalStageToSequence ∘ Sigma.mk s)
        inferInstance ≤ _
    rw [← coinduced_compose]
    apply coinduced_mono
    exact continuous_iff_coinduced_le.mp continuous_sigmaMk
  · exact continuous_iff_coinduced_le.mp
      continuous_osPositiveTimeOrderedFourDimensionalTotalStageToSequence

/-- Before descent through the quotient, scalar multiplication is continuous on total stages. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalTotalStage_scalarAction :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalTotalStage × ℂ =>
      p.2 • osPositiveTimeOrderedFourDimensionalTotalStageToSequence p.1) := by
  let actionOnSigma :
      (Σ s : Finset PositiveArity,
        OSPositiveTimeOrderedFourDimensionalStage s × ℂ) →
        OSPositiveTimeOrderedFourDimensionalTestSequence := fun z =>
      z.2.2 • osPositiveTimeOrderedFourDimensionalStageToSequence z.1 z.2.1
  have haction : Continuous actionOnSigma := by
    apply continuous_sigma
    intro s
    change Continuous (fun p : OSPositiveTimeOrderedFourDimensionalStage s × ℂ =>
      p.2 • osPositiveTimeOrderedFourDimensionalStageToSequence s p.1)
    rw [show (fun p : OSPositiveTimeOrderedFourDimensionalStage s × ℂ =>
        p.2 • osPositiveTimeOrderedFourDimensionalStageToSequence s p.1) =
      osPositiveTimeOrderedFourDimensionalStageToSequence s ∘
        (fun p => p.2 • p.1) by
      funext p
      exact (map_smul
        (osPositiveTimeOrderedFourDimensionalStageToSequenceLinearMap s) p.2 p.1).symm]
    exact (continuous_osPositiveTimeOrderedFourDimensionalStageToSequence s).comp
      (continuous_smul.comp continuous_swap)
  exact haction.comp
    (Homeomorph.sigmaProdDistrib :
      OSPositiveTimeOrderedFourDimensionalTotalStage × ℂ ≃ₜ
        (Σ s : Finset PositiveArity,
          OSPositiveTimeOrderedFourDimensionalStage s × ℂ)).continuous

/-- Joint complex scalar multiplication is continuous for the exact-source final topology. The
proof uses local compactness of `ℂ` and quotient-map lifting in the sequence variable. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequence_smul :
    Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalTestSequence =>
      p.1 • p.2) := by
  have swapped : Continuous
      (fun p : OSPositiveTimeOrderedFourDimensionalTestSequence × ℂ => p.2 • p.1) :=
    osPositiveTimeOrderedFourDimensionalTotalStageToSequence_isQuotientMap.continuous_lift_prod_left
      continuous_osPositiveTimeOrderedFourDimensionalTotalStage_scalarAction
  exact swapped.comp continuous_swap

/-- Named continuous complex scalar action on exact source sequences. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalSequenceContinuousSMul :
    ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence where
  continuous_smul := continuous_osPositiveTimeOrderedFourDimensionalSequence_smul

/-- Negation is continuous as scalar multiplication by `-1`. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequence_neg :
    Continuous (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence => -f) := by
  have h := continuous_osPositiveTimeOrderedFourDimensionalSequence_smul.comp
    ((continuous_const : Continuous
      (fun _ : OSPositiveTimeOrderedFourDimensionalTestSequence => (-1 : ℂ))).prodMk
        continuous_id)
  change Continuous (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence =>
    (-1 : ℂ) • f) at h
  simpa only [neg_one_smul] using h

/-- Named continuous negation on exact source sequences. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalSequenceContinuousNeg :
    ContinuousNeg OSPositiveTimeOrderedFourDimensionalTestSequence where
  continuous_neg := continuous_osPositiveTimeOrderedFourDimensionalSequence_neg

/-- Evaluation of a stage component is continuous, including the exact zero branch outside the
finite stage. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStageComponent
    (s : Finset PositiveArity) (arity : PositiveArity) :
    Continuous (fun x : OSPositiveTimeOrderedFourDimensionalStage s =>
      osPositiveTimeOrderedFourDimensionalStageComponent s x arity) := by
  classical
  unfold osPositiveTimeOrderedFourDimensionalStageComponent
  split_ifs with h
  · exact (continuous_apply (⟨arity, h⟩ : {a // a ∈ s})).comp continuous_snd
  · exact continuous_const

/-- Add two finite stages inside the finite union of their arity sets. -/
def osPositiveTimeOrderedFourDimensionalStagePairAdd
    (s t : Finset PositiveArity)
    (p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage t) :
    OSPositiveTimeOrderedFourDimensionalStage (s ∪ t) :=
  ⟨p.1.1 + p.2.1, fun arity =>
    osPositiveTimeOrderedFourDimensionalStageComponent s p.1 arity.val +
      osPositiveTimeOrderedFourDimensionalStageComponent t p.2 arity.val⟩

/-- Finite-stage pair addition is continuous into the union stage. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStagePairAdd
    (s t : Finset PositiveArity) :
    Continuous (osPositiveTimeOrderedFourDimensionalStagePairAdd s t) := by
  apply Continuous.prodMk
  · fun_prop
  · apply continuous_pi
    intro arity
    exact ((continuous_osPositiveTimeOrderedFourDimensionalStageComponent s arity.val).comp
      continuous_fst).add
      ((continuous_osPositiveTimeOrderedFourDimensionalStageComponent t arity.val).comp
        continuous_snd)

/-- Union-stage addition agrees exactly with named source-sequence addition. -/
theorem osPositiveTimeOrderedFourDimensionalStagePairAdd_factor
    (s t : Finset PositiveArity)
    (p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage t) :
    osPositiveTimeOrderedFourDimensionalStageToSequence (s ∪ t)
        (osPositiveTimeOrderedFourDimensionalStagePairAdd s t p) =
      osPositiveTimeOrderedFourDimensionalStageToSequence s p.1 +
        osPositiveTimeOrderedFourDimensionalStageToSequence t p.2 := by
  apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
  · rfl
  · intro arity
    change (osPositiveTimeOrderedFourDimensionalStageComponent (s ∪ t)
      (osPositiveTimeOrderedFourDimensionalStagePairAdd s t p) arity).toSchwartz =
      (osPositiveTimeOrderedFourDimensionalStageComponent s p.1 arity).toSchwartz +
        (osPositiveTimeOrderedFourDimensionalStageComponent t p.2 arity).toSchwartz
    classical
    by_cases hu : arity ∈ s ∪ t
    · simp only [osPositiveTimeOrderedFourDimensionalStageComponent, dif_pos hu,
        osPositiveTimeOrderedFourDimensionalStagePairAdd]
      exact OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_add_toSchwartz arity _ _
    · have hs : arity ∉ s := fun h => hu (Finset.mem_union_left t h)
      have ht : arity ∉ t := fun h => hu (Finset.mem_union_right s h)
      simp [osPositiveTimeOrderedFourDimensionalStageComponent, hu, hs, ht,
        zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
        OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- The sum of two selected finite-stage maps is jointly continuous. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStagePair_addition
    (s t : Finset PositiveArity) :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage t =>
      osPositiveTimeOrderedFourDimensionalStageToSequence s p.1 +
        osPositiveTimeOrderedFourDimensionalStageToSequence t p.2) := by
  rw [show (fun p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage t =>
      osPositiveTimeOrderedFourDimensionalStageToSequence s p.1 +
        osPositiveTimeOrderedFourDimensionalStageToSequence t p.2) =
    osPositiveTimeOrderedFourDimensionalStageToSequence (s ∪ t) ∘
      osPositiveTimeOrderedFourDimensionalStagePairAdd s t by
    funext p
    exact (osPositiveTimeOrderedFourDimensionalStagePairAdd_factor s t p).symm]
  exact (continuous_osPositiveTimeOrderedFourDimensionalStageToSequence (s ∪ t)).comp
    (continuous_osPositiveTimeOrderedFourDimensionalStagePairAdd s t)

/-- Addition by a fixed exact source sequence on the right is continuous. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequence_add_right
    (g : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Continuous (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence => f + g) := by
  rw [osPositiveTimeOrderedFourDimensionalTotalStageToSequence_isQuotientMap.continuous_iff]
  apply continuous_sigma
  intro s
  have pairWithSupportStage : Continuous
      (fun x : OSPositiveTimeOrderedFourDimensionalStage s =>
        (x, osPositiveTimeOrderedFourDimensionalSequenceToSupportStage g)) :=
    continuous_id.prodMk continuous_const
  have h :=
    (continuous_osPositiveTimeOrderedFourDimensionalStagePair_addition s g.support).comp
      pairWithSupportStage
  convert h using 1
  funext x
  change osPositiveTimeOrderedFourDimensionalStageToSequence s x + g =
    osPositiveTimeOrderedFourDimensionalStageToSequence s x +
      osPositiveTimeOrderedFourDimensionalStageToSequence g.support
        (osPositiveTimeOrderedFourDimensionalSequenceToSupportStage g)
  rw [osPositiveTimeOrderedFourDimensionalStage_recover g]

/-- Addition by a fixed exact source sequence on the left is continuous. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequence_add_left
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Continuous (fun g : OSPositiveTimeOrderedFourDimensionalTestSequence => f + g) := by
  simpa only [add_comm] using
    continuous_osPositiveTimeOrderedFourDimensionalSequence_add_right f

/-- Joint addition would follow from the precise remaining product-quotient property. This theorem
records the obstruction rather than assuming products of arbitrary quotient maps are quotient. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequence_add_of_product_isQuotientMap
    (hproduct : Topology.IsQuotientMap
      (Prod.map osPositiveTimeOrderedFourDimensionalTotalStageToSequence
        osPositiveTimeOrderedFourDimensionalTotalStageToSequence)) :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalTestSequence ×
      OSPositiveTimeOrderedFourDimensionalTestSequence => p.1 + p.2) := by
  rw [hproduct.continuous_iff]
  let additionOnSigma :
      (Σ s : Finset PositiveArity,
        OSPositiveTimeOrderedFourDimensionalStage s ×
          OSPositiveTimeOrderedFourDimensionalTotalStage) →
        OSPositiveTimeOrderedFourDimensionalTestSequence := fun z =>
      osPositiveTimeOrderedFourDimensionalStageToSequence z.1 z.2.1 +
        osPositiveTimeOrderedFourDimensionalTotalStageToSequence z.2.2
  have haddition : Continuous additionOnSigma := by
    apply continuous_sigma
    intro s
    let reversedStages :
        (Σ t : Finset PositiveArity,
          OSPositiveTimeOrderedFourDimensionalStage t ×
            OSPositiveTimeOrderedFourDimensionalStage s) →
          OSPositiveTimeOrderedFourDimensionalTestSequence := fun z =>
      osPositiveTimeOrderedFourDimensionalStageToSequence s z.2.2 +
        osPositiveTimeOrderedFourDimensionalStageToSequence z.1 z.2.1
    have hreversed : Continuous reversedStages := by
      apply continuous_sigma
      intro t
      exact (continuous_osPositiveTimeOrderedFourDimensionalStagePair_addition s t).comp
        continuous_swap
    exact hreversed.comp
      ((Homeomorph.sigmaProdDistrib :
        OSPositiveTimeOrderedFourDimensionalTotalStage ×
            OSPositiveTimeOrderedFourDimensionalStage s ≃ₜ
          (Σ t : Finset PositiveArity,
            OSPositiveTimeOrderedFourDimensionalStage t ×
              OSPositiveTimeOrderedFourDimensionalStage s)).continuous.comp continuous_swap)
  exact haddition.comp
    (Homeomorph.sigmaProdDistrib :
      OSPositiveTimeOrderedFourDimensionalTotalStage ×
          OSPositiveTimeOrderedFourDimensionalTotalStage ≃ₜ
        (Σ s : Finset PositiveArity,
          OSPositiveTimeOrderedFourDimensionalStage s ×
            OSPositiveTimeOrderedFourDimensionalTotalStage)).continuous

end

end YangMills
