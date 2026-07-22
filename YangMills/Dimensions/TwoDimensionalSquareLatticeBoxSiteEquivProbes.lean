/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxSiteEquiv

/-!
# Probes for exact square-box site and chain equivalences
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxSiteEquiv.Probes

noncomputable section

/-- The coordinate-site equivalence retains the literal right-directed bond. -/
theorem exact_coordinate_site
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius)
    (row : SquareLatticeBoxOffAxisRow radius) :
    (boxCoordinateSiteEquiv spacing radius (horizontal, row)).1 =
      epsilonSquareLatticeRightBond spacing (horizontal.1, row.1) :=
  boxCoordinateSiteEquiv_val spacing radius (horizontal, row)

/-- The plaquette-site equivalence retains the literal lower-left site. -/
theorem exact_plaquette_site
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius)
    (row : SquareLatticeBoxPlaquetteRow radius) :
    (boxPlaquetteSiteEquiv spacing radius (horizontal, row)).1.lowerLeft =
      (horizontal.1, row.1) :=
  boxPlaquetteSiteEquiv_lowerLeft spacing radius (horizontal, row)

/-- Chain coordinates retain both exact signed source rows. -/
theorem exact_coordinate_chain_sources
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)).1.source =
        (horizontal.1, (index.1 : ℤ) + 1) ∧
      (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)).1.source =
        (horizontal.1, -((index.1 : ℤ) + 1)) :=
  ⟨boxCoordinateChainEquiv_source_inl spacing radius horizontal index,
    boxCoordinateChainEquiv_source_inr spacing radius horizontal index⟩

/-- Chain plaquettes retain both exact lower-left rows. -/
theorem exact_plaquette_chain_sites
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)).1.lowerLeft =
        (horizontal.1, (index.1 : ℤ)) ∧
      (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)).1.lowerLeft =
        (horizontal.1, -((index.1 : ℤ) + 1)) := by
  simp

/-- Both geometric chain maps cover the complete actual coordinate and plaquette subtypes. -/
theorem exact_chain_coverage
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxCoordinateChainEquiv spacing radius) ∧
      Function.Surjective (boxPlaquetteChainEquiv spacing radius) :=
  ⟨(boxCoordinateChainEquiv spacing radius).surjective,
    (boxPlaquetteChainEquiv spacing radius).surjective⟩

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxSiteEquiv.Probes
