/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Finite graph refinement maps

If a finer graph represents every coarse edge by an oriented fine-edge word, its configuration map
sends a fine configuration to the holonomies of those words. This is Lévy's map
`f_{Γ₁Γ₂} : G^{Γ₂} → G^{Γ₁}`. Reverse coarse traversal substitutes the reversed/flipped fine word.
Word substitution proves the exact composition law underlying Lévy Lemma 1.6.3.

`FiniteGraphRefinementData` additionally records endpoint coherence. Theorem 1.6.1's surjectivity
is deliberately required later at the selected gauge group by the source-facing measure law;
arbitrary word families do not imply it. This module supplies no embedding, face law, probability measure, or
Yang--Mills theory.
-/

namespace YangMills.Mathematics

open MeasureTheory

noncomputable section

universe uCoarseVertex uFineVertex uCoarseEdge uFineEdge uG

/-- Replace one oriented coarse edge by its exact fine-edge word. -/
def refineOrientedEdge
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge)) :
    OrientedEdge CoarseEdge → List (OrientedEdge FineEdge)
  | .forward edge => edgeWord edge
  | .reverse edge => reverseFiniteOrientedWord (edgeWord edge)

/-- Substitute fine-edge words throughout a coarse oriented word, preserving traversal order. -/
def refineOrientedWord
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (word : List (OrientedEdge CoarseEdge)) : List (OrientedEdge FineEdge) :=
  word.flatMap (refineOrientedEdge edgeWord)

/-- Refining a reversed traversal is exactly reversal of the refined traversal. -/
theorem refineOrientedWord_reverseFiniteOrientedWord
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (word : List (OrientedEdge CoarseEdge)) :
    refineOrientedWord edgeWord (reverseFiniteOrientedWord word) =
      reverseFiniteOrientedWord (refineOrientedWord edgeWord word) := by
  induction word with
  | nil => rfl
  | cons oriented tail ih =>
      rw [show reverseFiniteOrientedWord (oriented :: tail) =
        reverseFiniteOrientedWord tail ++ [OrientedEdge.flip oriented] by
          simp [reverseFiniteOrientedWord, List.map_reverse]]
      simp only [refineOrientedWord, List.flatMap_append, List.flatMap_singleton]
      simp only [refineOrientedWord] at ih
      rw [ih]
      cases oriented <;>
        simp [refineOrientedEdge, reverseFiniteOrientedWord, List.map_reverse,
          Function.comp_def, OrientedEdge.flip_flip]

/-- Two successive oriented-word substitutions equal one substitution by the composed edge words. -/
theorem refineOrientedWord_comp
    {CoarseEdge : Type uCoarseEdge} {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    (coarseToMiddle : CoarseEdge → List (OrientedEdge MiddleEdge))
    (middleToFine : MiddleEdge → List (OrientedEdge FineEdge))
    (word : List (OrientedEdge CoarseEdge)) :
    refineOrientedWord middleToFine (refineOrientedWord coarseToMiddle word) =
      refineOrientedWord
        (fun edge => refineOrientedWord middleToFine (coarseToMiddle edge)) word := by
  induction word with
  | nil => rfl
  | cons oriented tail ih =>
      simp only [refineOrientedWord, List.flatMap_cons, List.flatMap_append]
      simp only [refineOrientedWord] at ih
      rw [ih]
      congr 1
      cases oriented with
      | forward edge => rfl
      | reverse edge =>
          exact refineOrientedWord_reverseFiniteOrientedWord middleToFine (coarseToMiddle edge)

/-- Reversing and flipping a composable oriented word preserves composability. -/
theorem isChain_reverseFiniteOrientedWord
    {Vertex Edge : Type*} (edgeSource edgeTarget : Edge → Vertex)
    (word : List (OrientedEdge Edge))
    (chain : List.IsChain (OrientedEdgeComposable edgeSource edgeTarget) word) :
    List.IsChain (OrientedEdgeComposable edgeSource edgeTarget)
      (reverseFiniteOrientedWord word) := by
  simp only [reverseFiniteOrientedWord, List.isChain_map, List.isChain_reverse]
  apply chain.imp
  intro first second composable
  simpa [OrientedEdgeComposable, OrientedEdge.source_flip, OrientedEdge.target_flip]
    using composable.symm

/-- Fine configurations induce coarse configurations by exact word holonomy. -/
def finiteEdgeRefinementConfigurationMap
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    {G : Type uG} [Group G]
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (configuration : FineEdge → G) (edge : CoarseEdge) : G :=
  finiteOrientedWordHolonomy configuration (edgeWord edge)

/-- Holonomy commutes exactly with oriented-word substitution. -/
theorem finiteOrientedWordHolonomy_refineOrientedWord
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    {G : Type uG} [Group G]
    (edgeWord : CoarseEdge → List (OrientedEdge FineEdge))
    (configuration : FineEdge → G) (word : List (OrientedEdge CoarseEdge)) :
    finiteOrientedWordHolonomy configuration (refineOrientedWord edgeWord word) =
      finiteOrientedWordHolonomy
        (finiteEdgeRefinementConfigurationMap edgeWord configuration) word := by
  induction word with
  | nil => rfl
  | cons oriented tail ih =>
      rw [show refineOrientedWord edgeWord (oriented :: tail) =
        refineOrientedEdge edgeWord oriented ++ refineOrientedWord edgeWord tail by
          rfl]
      rw [finiteOrientedWordHolonomy_append, ih]
      cases oriented with
      | forward edge => rfl
      | reverse edge =>
          simp [refineOrientedEdge, finiteEdgeRefinementConfigurationMap]

/-- Simultaneous holonomies of an indexed finite-word family. -/
def finiteOrientedWordHolonomyFamily
    {Index : Type*} {Edge : Type uFineEdge} {G : Type uG} [Group G]
    (words : Index → List (OrientedEdge Edge)) (configuration : Edge → G) (index : Index) : G :=
  finiteOrientedWordHolonomy configuration (words index)

/-- A finite family of word holonomies is jointly measurable. -/
theorem finiteOrientedWordHolonomyFamily_measurable
    {Index : Type*} [Fintype Index] {Edge : Type uFineEdge}
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (words : Index → List (OrientedEdge Edge)) :
    Measurable (finiteOrientedWordHolonomyFamily (G := G) words) := by
  apply measurable_pi_iff.mpr
  intro index
  exact finiteOrientedWordHolonomy_measurable (words index)

/-- Lévy Lemma 1.6.3 at the exact finite-word level. -/
theorem finiteEdgeRefinementConfigurationMap_comp
    {CoarseEdge : Type uCoarseEdge} {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    {G : Type uG} [Group G]
    (coarseToMiddle : CoarseEdge → List (OrientedEdge MiddleEdge))
    (middleToFine : MiddleEdge → List (OrientedEdge FineEdge))
    (configuration : FineEdge → G) :
    finiteEdgeRefinementConfigurationMap coarseToMiddle
        (finiteEdgeRefinementConfigurationMap middleToFine configuration) =
      finiteEdgeRefinementConfigurationMap
        (fun edge => refineOrientedWord middleToFine (coarseToMiddle edge)) configuration := by
  funext edge
  exact (finiteOrientedWordHolonomy_refineOrientedWord
    middleToFine configuration (coarseToMiddle edge)).symm

/-- Finite graph refinement combinatorics: every coarse edge is a nonempty composable fine path with
coherent endpoints. Source-facing geometry and Theorem 1.6.1 surjectivity are imposed later. -/
structure FiniteGraphRefinementData
    (CoarseVertex : Type uCoarseVertex) (FineVertex : Type uFineVertex)
    (CoarseEdge : Type uCoarseEdge) (FineEdge : Type uFineEdge)
    [Fintype CoarseEdge] [Fintype FineEdge]
    (coarseSource coarseTarget : CoarseEdge → CoarseVertex)
    (fineSource fineTarget : FineEdge → FineVertex) where
  vertexMap : CoarseVertex → FineVertex
  edgeWord : CoarseEdge → List (OrientedEdge FineEdge)
  edgeWord_nonempty : ∀ edge, edgeWord edge ≠ []
  edgeWord_chain : ∀ edge,
    List.IsChain (OrientedEdgeComposable fineSource fineTarget) (edgeWord edge)
  edgeWord_source : ∀ edge,
    OrientedEdge.source fineSource fineTarget
      ((edgeWord edge).head (edgeWord_nonempty edge)) = vertexMap (coarseSource edge)
  edgeWord_target : ∀ edge,
    OrientedEdge.target fineSource fineTarget
      ((edgeWord edge).getLast (edgeWord_nonempty edge)) = vertexMap (coarseTarget edge)

/-- Identity refinement, providing positive consistency evidence for the interface. -/
noncomputable def finiteGraphIdentityRefinementData
    (Vertex : Type uCoarseVertex) (Edge : Type uCoarseEdge) [Fintype Edge]
    (edgeSource edgeTarget : Edge → Vertex) :
    FiniteGraphRefinementData Vertex Vertex Edge Edge
      edgeSource edgeTarget edgeSource edgeTarget where
  vertexMap := id
  edgeWord edge := [.forward edge]
  edgeWord_nonempty edge := by simp
  edgeWord_chain edge := by simp
  edgeWord_source edge := rfl
  edgeWord_target edge := rfl

namespace FiniteGraphRefinementData

/-- A finite graph refinement is determined by its vertex map and oriented edge words; endpoint and
chain certificates are proof-irrelevant. -/
theorem eq_of_vertexMap_edgeWord_eq
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (first second : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (vertexMap_eq : first.vertexMap = second.vertexMap)
    (edgeWord_eq : first.edgeWord = second.edgeWord) : first = second := by
  cases first
  cases second
  simp_all

/-- The fine word replacing any oriented coarse edge is nonempty. -/
theorem refineOrientedEdge_nonempty
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (edge : OrientedEdge CoarseEdge) :
    refineOrientedEdge refinement.edgeWord edge ≠ [] := by
  cases edge with
  | forward edge => exact refinement.edgeWord_nonempty edge
  | reverse edge =>
      simpa [refineOrientedEdge, reverseFiniteOrientedWord] using
        refinement.edgeWord_nonempty edge

/-- The fine word replacing any oriented coarse edge is composable. -/
theorem refineOrientedEdge_chain
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (edge : OrientedEdge CoarseEdge) :
    List.IsChain (OrientedEdgeComposable fineSource fineTarget)
      (refineOrientedEdge refinement.edgeWord edge) := by
  cases edge with
  | forward edge => exact refinement.edgeWord_chain edge
  | reverse edge =>
      exact isChain_reverseFiniteOrientedWord fineSource fineTarget
        (refinement.edgeWord edge) (refinement.edgeWord_chain edge)

/-- The source of an oriented refined edge word is the mapped coarse oriented source. -/
theorem refineOrientedEdge_source
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (edge : OrientedEdge CoarseEdge) :
    OrientedEdge.source fineSource fineTarget
        ((refineOrientedEdge refinement.edgeWord edge).head
          (refinement.refineOrientedEdge_nonempty edge)) =
      refinement.vertexMap (OrientedEdge.source coarseSource coarseTarget edge) := by
  cases edge with
  | forward edge => exact refinement.edgeWord_source edge
  | reverse edge =>
      simp only [refineOrientedEdge]
      rw [show (reverseFiniteOrientedWord (refinement.edgeWord edge)).head
          (refinement.refineOrientedEdge_nonempty (.reverse edge)) =
        OrientedEdge.flip ((refinement.edgeWord edge).getLast
          (refinement.edgeWord_nonempty edge)) by
            simp [reverseFiniteOrientedWord]]
      rw [OrientedEdge.source_flip, refinement.edgeWord_target]
      rfl

/-- The target of an oriented refined edge word is the mapped coarse oriented target. -/
theorem refineOrientedEdge_target
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (edge : OrientedEdge CoarseEdge) :
    OrientedEdge.target fineSource fineTarget
        ((refineOrientedEdge refinement.edgeWord edge).getLast
          (refinement.refineOrientedEdge_nonempty edge)) =
      refinement.vertexMap (OrientedEdge.target coarseSource coarseTarget edge) := by
  cases edge with
  | forward edge => exact refinement.edgeWord_target edge
  | reverse edge =>
      simp only [refineOrientedEdge]
      rw [show (reverseFiniteOrientedWord (refinement.edgeWord edge)).getLast
          (refinement.refineOrientedEdge_nonempty (.reverse edge)) =
        OrientedEdge.flip ((refinement.edgeWord edge).head
          (refinement.edgeWord_nonempty edge)) by
            simp [reverseFiniteOrientedWord]]
      rw [OrientedEdge.target_flip, refinement.edgeWord_source]
      rfl

/-- Refining a nonempty oriented word remains nonempty. -/
theorem refineOrientedWord_nonempty
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (word : List (OrientedEdge CoarseEdge)) (word_nonempty : word ≠ []) :
    refineOrientedWord refinement.edgeWord word ≠ [] := by
  intro refinedEmpty
  rw [refineOrientedWord, List.flatMap_eq_nil_iff] at refinedEmpty
  obtain ⟨edge, member⟩ := List.exists_mem_of_ne_nil word word_nonempty
  exact refinement.refineOrientedEdge_nonempty edge (refinedEmpty edge member)

/-- Refinement preserves composability of an entire oriented word. -/
theorem refineOrientedWord_chain
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (word : List (OrientedEdge CoarseEdge))
    (chain : List.IsChain (OrientedEdgeComposable coarseSource coarseTarget) word) :
    List.IsChain (OrientedEdgeComposable fineSource fineTarget)
      (refineOrientedWord refinement.edgeWord word) := by
  induction word with
  | nil => simp [refineOrientedWord]
  | cons edge tail ih =>
      rw [show refineOrientedWord refinement.edgeWord (edge :: tail) =
        refineOrientedEdge refinement.edgeWord edge ++
          refineOrientedWord refinement.edgeWord tail by rfl]
      apply List.IsChain.append (refinement.refineOrientedEdge_chain edge)
        (ih (List.IsChain.tail chain))
      intro last last_mem first first_mem
      rw [List.getLast?_eq_some_getLast (refinement.refineOrientedEdge_nonempty edge)] at last_mem
      simp only [Option.mem_def, Option.some.injEq] at last_mem
      subst last
      cases tail with
      | nil => simp [refineOrientedWord] at first_mem
      | cons next rest =>
          have pair : OrientedEdgeComposable coarseSource coarseTarget edge next := chain.rel
          have tail_nonempty :
              refineOrientedWord refinement.edgeWord (next :: rest) ≠ [] :=
            refinement.refineOrientedWord_nonempty (next :: rest) (by simp)
          rw [List.head?_eq_some_head tail_nonempty] at first_mem
          simp only [Option.mem_def, Option.some.injEq] at first_mem
          have head_eq :
              (refineOrientedWord refinement.edgeWord (next :: rest)).head tail_nonempty =
                (refineOrientedEdge refinement.edgeWord next).head
                  (refinement.refineOrientedEdge_nonempty next) := by
            simp [refineOrientedWord, refinement.refineOrientedEdge_nonempty]
          rw [head_eq] at first_mem
          subst first
          rw [OrientedEdgeComposable, refinement.refineOrientedEdge_target,
            refinement.refineOrientedEdge_source]
          exact congrArg refinement.vertexMap pair

/-- The source of a refined nonempty word is the image of its coarse source. -/
theorem refineOrientedWord_source
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (word : List (OrientedEdge CoarseEdge)) (word_nonempty : word ≠ []) :
    OrientedEdge.source fineSource fineTarget
        ((refineOrientedWord refinement.edgeWord word).head
          (refinement.refineOrientedWord_nonempty word word_nonempty)) =
      refinement.vertexMap
        (OrientedEdge.source coarseSource coarseTarget (word.head word_nonempty)) := by
  obtain ⟨edge, tail, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
  simp [refineOrientedWord, refinement.refineOrientedEdge_nonempty,
    refinement.refineOrientedEdge_source]

/-- The target of a refined nonempty word is the image of its coarse target. -/
theorem refineOrientedWord_target
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)
    (word : List (OrientedEdge CoarseEdge)) (word_nonempty : word ≠ []) :
    OrientedEdge.target fineSource fineTarget
        ((refineOrientedWord refinement.edgeWord word).getLast
          (refinement.refineOrientedWord_nonempty word word_nonempty)) =
      refinement.vertexMap
        (OrientedEdge.target coarseSource coarseTarget (word.getLast word_nonempty)) := by
  induction word using List.reverseRecOn with
  | nil => contradiction
  | append_singleton init edge =>
      simp [refineOrientedWord, refinement.refineOrientedEdge_nonempty,
        refinement.refineOrientedEdge_target]

variable
    {CoarseVertex : Type uCoarseVertex} {FineVertex : Type uFineVertex}
    {CoarseEdge : Type uCoarseEdge} {FineEdge : Type uFineEdge}
    [Fintype CoarseEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (refinement : FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget)

/-- The exact fine-to-coarse configuration map. -/
def configurationMap {G : Type uG} [Group G] : (FineEdge → G) → CoarseEdge → G :=
  finiteEdgeRefinementConfigurationMap refinement.edgeWord

/-- The refinement configuration map is measurable under the finite product measurable structures. -/
theorem configurationMap_measurable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] :
    Measurable (refinement.configurationMap (G := G)) := by
  apply measurable_pi_iff.mpr
  intro edge
  exact finiteOrientedWordHolonomy_measurable (refinement.edgeWord edge)

/-- Endpoint gauge transport commutes exactly with refinement. -/
theorem configurationMap_gauge
    {G : Type uG} [Group G]
    (fineGauge : FineVertex → G) (configuration : FineEdge → G) :
    refinement.configurationMap
        (finiteEdgeGaugeAction fineSource fineTarget fineGauge configuration) =
      finiteEdgeGaugeAction coarseSource coarseTarget
        (fun vertex => fineGauge (refinement.vertexMap vertex))
        (refinement.configurationMap configuration) := by
  funext edge
  obtain ⟨first, tail, word_eq⟩ := List.exists_cons_of_ne_nil
    (refinement.edgeWord_nonempty edge)
  rw [configurationMap, finiteEdgeRefinementConfigurationMap, word_eq]
  rw [finiteOrientedWordHolonomy_gauge_of_chain
    fineSource fineTarget fineGauge configuration first tail]
  · simp only [finiteEdgeGaugeAction]
    rw [← refinement.edgeWord_target edge, ← refinement.edgeWord_source edge]
    simp [finiteEdgeRefinementConfigurationMap, word_eq]
  · simpa [word_eq] using refinement.edgeWord_chain edge

/-- Canonical composite of two finite graph refinements. -/
noncomputable def comp
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget)
    (middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget) :
    FiniteGraphRefinementData CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget where
  vertexMap := middleToFine.vertexMap ∘ coarseToMiddle.vertexMap
  edgeWord edge := refineOrientedWord middleToFine.edgeWord (coarseToMiddle.edgeWord edge)
  edgeWord_nonempty edge := middleToFine.refineOrientedWord_nonempty
    (coarseToMiddle.edgeWord edge) (coarseToMiddle.edgeWord_nonempty edge)
  edgeWord_chain edge := middleToFine.refineOrientedWord_chain
    (coarseToMiddle.edgeWord edge) (coarseToMiddle.edgeWord_chain edge)
  edgeWord_source edge := by
    rw [middleToFine.refineOrientedWord_source (coarseToMiddle.edgeWord edge)
      (coarseToMiddle.edgeWord_nonempty edge)]
    rw [coarseToMiddle.edgeWord_source]
    rfl
  edgeWord_target edge := by
    rw [middleToFine.refineOrientedWord_target (coarseToMiddle.edgeWord edge)
      (coarseToMiddle.edgeWord_nonempty edge)]
    rw [coarseToMiddle.edgeWord_target]
    rfl

end FiniteGraphRefinementData

/-- Exact pushforward laws compose along measurable refinement maps. -/
theorem finiteRefinementMeasurePushforward_comp
    {FineConfiguration MiddleConfiguration CoarseConfiguration : Type*}
    [MeasurableSpace FineConfiguration] [MeasurableSpace MiddleConfiguration]
    [MeasurableSpace CoarseConfiguration]
    (fineMeasure : Measure FineConfiguration) (middleMeasure : Measure MiddleConfiguration)
    (coarseMeasure : Measure CoarseConfiguration)
    (fineToMiddle : FineConfiguration → MiddleConfiguration)
    (middleToCoarse : MiddleConfiguration → CoarseConfiguration)
    (fineToMiddle_measurable : Measurable fineToMiddle)
    (middleToCoarse_measurable : Measurable middleToCoarse)
    (fine_pushforward : Measure.map fineToMiddle fineMeasure = middleMeasure)
    (middle_pushforward : Measure.map middleToCoarse middleMeasure = coarseMeasure) :
    Measure.map (middleToCoarse ∘ fineToMiddle) fineMeasure = coarseMeasure := by
  rw [← Measure.map_map middleToCoarse_measurable fineToMiddle_measurable,
    fine_pushforward, middle_pushforward]

/-- Exact coherence datum for a coarse-to-middle, middle-to-fine, and coarse-to-fine refinement
triple. The direct edge words must be literal oriented-word substitution. -/
structure FiniteGraphRefinementCompositionData
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget)
    (middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget)
    (coarseToFine : FiniteGraphRefinementData
      CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget) where
  vertexMap_eq : coarseToFine.vertexMap = middleToFine.vertexMap ∘ coarseToMiddle.vertexMap
  edgeWord_eq : ∀ edge, coarseToFine.edgeWord edge =
    refineOrientedWord middleToFine.edgeWord (coarseToMiddle.edgeWord edge)

/-- Every two-stage finite graph refinement has a canonical coherent direct refinement. -/
noncomputable def finiteGraphRefinementCompositionData
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    (coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget)
    (middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget) :
    FiniteGraphRefinementCompositionData coarseToMiddle middleToFine
      (coarseToMiddle.comp middleToFine) where
  vertexMap_eq := rfl
  edgeWord_eq _edge := rfl

/-- Identity refinements compose coherently, providing positive evidence for the composition API. -/
noncomputable def finiteGraphIdentityRefinementCompositionData
    (Vertex : Type uCoarseVertex) (Edge : Type uCoarseEdge) [Fintype Edge]
    (edgeSource edgeTarget : Edge → Vertex) :
    FiniteGraphRefinementCompositionData
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget)
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget)
      (finiteGraphIdentityRefinementData Vertex Edge edgeSource edgeTarget) where
  vertexMap_eq := by rfl
  edgeWord_eq edge := by
    simp [finiteGraphIdentityRefinementData, refineOrientedWord, refineOrientedEdge]

namespace FiniteGraphRefinementCompositionData

/-- Any two direct graph refinements coherent with the same two stages are equal. In particular,
every stored coherent direct graph equals the canonical composite constructed by `comp`. -/
theorem directGraph_unique
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget}
    {middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget}
    {firstDirect secondDirect : FiniteGraphRefinementData
      CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget}
    (first : FiniteGraphRefinementCompositionData
      coarseToMiddle middleToFine firstDirect)
    (second : FiniteGraphRefinementCompositionData
      coarseToMiddle middleToFine secondDirect) :
    firstDirect = secondDirect := by
  apply FiniteGraphRefinementData.eq_of_vertexMap_edgeWord_eq
  · rw [first.vertexMap_eq, second.vertexMap_eq]
  · funext edge
    rw [first.edgeWord_eq edge, second.edgeWord_eq edge]

variable
    {CoarseVertex : Type uCoarseVertex} {MiddleVertex : Type uFineVertex}
    {FineVertex : Type*} {CoarseEdge : Type uCoarseEdge}
    {MiddleEdge : Type uFineEdge} {FineEdge : Type*}
    [Fintype CoarseEdge] [Fintype MiddleEdge] [Fintype FineEdge]
    {coarseSource coarseTarget : CoarseEdge → CoarseVertex}
    {middleSource middleTarget : MiddleEdge → MiddleVertex}
    {fineSource fineTarget : FineEdge → FineVertex}
    {coarseToMiddle : FiniteGraphRefinementData
      CoarseVertex MiddleVertex CoarseEdge MiddleEdge
      coarseSource coarseTarget middleSource middleTarget}
    {middleToFine : FiniteGraphRefinementData
      MiddleVertex FineVertex MiddleEdge FineEdge
      middleSource middleTarget fineSource fineTarget}
    {coarseToFine : FiniteGraphRefinementData
      CoarseVertex FineVertex CoarseEdge FineEdge
      coarseSource coarseTarget fineSource fineTarget}

/-- The direct refinement map is exactly the composite, Lévy Lemma 1.6.3. -/
theorem configurationMap_eq_comp
    (data : FiniteGraphRefinementCompositionData
      coarseToMiddle middleToFine coarseToFine)
    {G : Type uG} [Group G] :
    coarseToFine.configurationMap (G := G) =
      coarseToMiddle.configurationMap ∘ middleToFine.configurationMap := by
  funext configuration edge
  rw [FiniteGraphRefinementData.configurationMap,
    finiteEdgeRefinementConfigurationMap, data.edgeWord_eq]
  exact finiteOrientedWordHolonomy_refineOrientedWord
    middleToFine.edgeWord configuration (coarseToMiddle.edgeWord edge)

end FiniteGraphRefinementCompositionData

end

end YangMills.Mathematics
