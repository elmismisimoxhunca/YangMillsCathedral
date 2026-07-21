/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxMeasure

/-!
# Probes for normalized exact square-box measures
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxMeasure.Probes

open MeasureTheory Set

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G)

omit [MeasurableMul₂ G] in
/-- The box weight is exactly the generic finite weight on the concrete box presentation. -/
theorem exact_weight_formula :
    twoDimensionalSquareLatticeBoxWeight spacing radius action =
      twoDimensionalFiniteAxialPlaquetteWeight action
        (twoDimensionalSquareLatticeBoxPresentation spacing radius) :=
  rfl

omit [MeasurableMul₂ G] in
/-- The box partition function is exactly the product-Haar integral of that same weight. -/
theorem exact_normalizer_formula :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action =
      twoDimensionalFiniteAxialNormalizer action
        (twoDimensionalSquareLatticeBoxPresentation spacing radius) :=
  rfl

/-- Every exact box partition function is simultaneously nonzero and finite. -/
theorem exact_normalizer_contract :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action ≠ 0 ∧
      twoDimensionalSquareLatticeBoxNormalizer spacing radius action ≠ ⊤ :=
  ⟨twoDimensionalSquareLatticeBoxNormalizer.ne_zero spacing radius action,
    twoDimensionalSquareLatticeBoxNormalizer.ne_top spacing radius action⟩

/-- The constructed finite-coordinate box measure is normalized and nonzero. -/
theorem exact_box_measure_contract :
    twoDimensionalSquareLatticeBoxMeasure spacing radius action univ = 1 ∧
      twoDimensionalSquareLatticeBoxMeasure spacing radius action ≠ 0 :=
  ⟨twoDimensionalSquareLatticeBoxMeasure.apply_univ spacing radius action,
    twoDimensionalSquareLatticeBoxMeasure.ne_zero spacing radius action⟩

/-- Its same-extension pushforward is normalized and nonzero on the exact infinite axial carrier. -/
theorem exact_box_pushforward_contract :
    twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action univ = 1 ∧
      twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action ≠ 0 :=
  ⟨twoDimensionalSquareLatticeBoxPushforwardMeasure.apply_univ spacing radius action,
    twoDimensionalSquareLatticeBoxPushforwardMeasure.ne_zero spacing radius action⟩

/-- A zero box partition function is hostilely rejected. -/
theorem zero_normalizer_blocked
    (claimed : twoDimensionalSquareLatticeBoxNormalizer spacing radius action = 0) : False :=
  (twoDimensionalSquareLatticeBoxNormalizer.ne_zero spacing radius action) claimed

omit [MeasurableMul₂ G] in
/-- An infinite box partition function is hostilely rejected. -/
theorem infinite_normalizer_blocked
    (claimed : twoDimensionalSquareLatticeBoxNormalizer spacing radius action = ⊤) : False :=
  (twoDimensionalSquareLatticeBoxNormalizer.ne_top spacing radius action) claimed

/-- A zero exact box measure is hostilely rejected. -/
theorem zero_box_measure_blocked
    (claimed : twoDimensionalSquareLatticeBoxMeasure spacing radius action = 0) : False :=
  (twoDimensionalSquareLatticeBoxMeasure.ne_zero spacing radius action) claimed

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxMeasure.Probes
