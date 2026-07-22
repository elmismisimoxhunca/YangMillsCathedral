/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginals of finite products along injections

Restricting a finite family along an injective index map sends a finite product of one probability
measure to the smaller product of the same measure. The proof splits selected and complementary
coordinates, discards the probability-normalized complement, and reindexes the selected subtype.
-/

namespace YangMills.Mathematics

open MeasureTheory Set

noncomputable section

universe uG uI uJ

/-- Restrict a larger finite product to coordinates selected by an injection. -/
def finiteProductRestriction {I : Type uI} {J : Type uJ} {G : Type uG}
    (inclusion : J → I) : (I → G) → (J → G) :=
  fun values j => values (inclusion j)

namespace finiteProductRestriction

variable {I : Type uI} {J : Type uJ} {G : Type uG}
  [Fintype I] [Fintype J] [MeasurableSpace G]
  (μ : Measure G) [SigmaFinite μ] [IsProbabilityMeasure μ]
  (inclusion : J → I) (hinj : Function.Injective inclusion)

private def selected (i : I) : Prop := i ∈ Set.range inclusion

local instance selectedDecidable : DecidablePred (selected inclusion) := Classical.decPred _

private def selectedEquiv : J ≃ {i : I // selected inclusion i} := by
  apply Equiv.ofBijective (fun j => ⟨inclusion j, ⟨j, rfl⟩⟩)
  constructor
  · intro first second equality
    exact hinj (congrArg Subtype.val equality)
  · rintro ⟨i, ⟨j, rfl⟩⟩
    exact ⟨j, rfl⟩

private def selectedReindex :
    ({i : I // selected inclusion i} → G) ≃ᵐ (J → G) :=
  MeasurableEquiv.piCongrLeft (fun _ : J => G) (selectedEquiv inclusion hinj).symm

omit [IsProbabilityMeasure μ] in
private theorem selectedReindex_measurePreserving :
    MeasurePreserving (selectedReindex (G := G) inclusion hinj)
      (Measure.pi fun _ : {i : I // selected inclusion i} => μ)
      (Measure.pi fun _ : J => μ) := by
  simpa [selectedReindex] using
    (measurePreserving_piCongrLeft (fun _ : J => μ)
      (selectedEquiv inclusion hinj).symm)

omit [Fintype I] [Fintype J] in
private theorem selectedReindex_apply
    (values : {i : I // selected inclusion i} → G) (j : J) :
    selectedReindex (G := G) inclusion hinj values j =
      values ⟨inclusion j, ⟨j, rfl⟩⟩ := by
  change (MeasurableEquiv.piCongrLeft (fun _ : J => G)
    (selectedEquiv inclusion hinj).symm) values j = _
  rw [MeasurableEquiv.coe_piCongrLeft]
  calc
    _ = values ((selectedEquiv inclusion hinj) j) := by
      simpa using Equiv.piCongrLeft_apply_apply (fun _ : J => G)
        (selectedEquiv inclusion hinj).symm values ((selectedEquiv inclusion hinj) j)
    _ = values ⟨inclusion j, ⟨j, rfl⟩⟩ := by
      congr 1

omit [Fintype I] [Fintype J] in
private theorem restriction_eq_composition :
    finiteProductRestriction (G := G) inclusion =
      selectedReindex (G := G) inclusion hinj ∘ Prod.fst ∘
        MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => G) (selected inclusion) := by
  funext values j
  simp only [Function.comp_apply, finiteProductRestriction]
  rw [selectedReindex_apply]
  rfl

/-- Restriction along any injection sends a finite product of one probability law to the smaller
product of the same law. -/
theorem measurePreserving (hinj : Function.Injective inclusion) :
    MeasurePreserving (finiteProductRestriction (G := G) inclusion)
      (Measure.pi fun _ : I => μ) (Measure.pi fun _ : J => μ) := by
  let complementMeasure : Measure ({i : I // ¬ selected inclusion i} → G) :=
    Measure.pi fun _ => μ
  letI : IsProbabilityMeasure complementMeasure := by
    dsimp [complementMeasure]
    infer_instance
  have splitMP := measurePreserving_piEquivPiSubtypeProd
    (fun _ : I => μ) (selected inclusion)
  have firstMP : MeasurePreserving Prod.fst
      ((Measure.pi fun _ : {i : I // selected inclusion i} => μ).prod complementMeasure)
      (Measure.pi fun _ : {i : I // selected inclusion i} => μ) :=
    measurePreserving_fst
  rw [restriction_eq_composition (G := G) inclusion hinj]
  exact (selectedReindex_measurePreserving μ inclusion hinj).comp
    (firstMP.comp splitMP)

/-- Exact marginal equality exposed as a map identity. -/
theorem map_eq (hinj : Function.Injective inclusion) :
    Measure.map (finiteProductRestriction (G := G) inclusion)
      (Measure.pi fun _ : I => μ) = Measure.pi fun _ : J => μ :=
  (finiteProductRestriction.measurePreserving μ inclusion hinj).map_eq

end finiteProductRestriction

end

end YangMills.Mathematics
