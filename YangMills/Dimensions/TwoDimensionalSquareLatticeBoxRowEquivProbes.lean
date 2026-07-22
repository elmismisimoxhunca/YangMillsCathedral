/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxRowEquiv

/-!
# Probes for exact square-box row-chain equivalences
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxRowEquiv.Probes

noncomputable section

/-- Positive and negative coordinate chains retain their exact signed integer rows. -/
theorem exact_coordinate_chain_rows (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inl index)).1 = (index.1 : ℤ) + 1 ∧
      (boxOffAxisRowEquiv radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) := by
  simp

/-- Upper and lower plaquette chains retain the exact lower-left rows. -/
theorem exact_plaquette_chain_rows (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxPlaquetteRowEquiv radius (Sum.inl index)).1 = (index.1 : ℤ) ∧
      (boxPlaquetteRowEquiv radius (Sum.inr index)).1 = -((index.1 : ℤ) + 1) := by
  simp

/-- Both chain enumerations are surjective onto the actual finite row subtypes. -/
theorem exact_row_coverage (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxOffAxisRowEquiv radius) ∧
      Function.Surjective (boxPlaquetteRowEquiv radius) :=
  ⟨(boxOffAxisRowEquiv radius).surjective, (boxPlaquetteRowEquiv radius).surjective⟩

/-- The upper and lower row alignments are exact and orientation-sensitive. -/
theorem exact_row_alignment (radius : PositiveSquareLatticeBoxRadius)
    (index : Fin radius.1) :
    (boxOffAxisRowEquiv radius (Sum.inl index)).1 =
        (boxPlaquetteRowEquiv radius (Sum.inl index)).1 + 1 ∧
      (boxOffAxisRowEquiv radius (Sum.inr index)).1 =
        (boxPlaquetteRowEquiv radius (Sum.inr index)).1 :=
  ⟨box_upper_row_alignment radius index, box_lower_row_alignment radius index⟩

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxRowEquiv.Probes
