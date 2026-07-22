/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPresentation

/-!
# Exact site and chain coordinates for square boxes

Every independent horizontal bond and every plaquette is identified with its literal integer site.
Composing those geometric bijections with the signed row-chain equivalences yields exact common
`horizontal × (upper ⊕ lower)` index types for coordinates and plaquettes. These are load-bearing
geometric equivalences, not arbitrary finite-cardinality relabelings.

No measure or projective limit is constructed here.
-/

namespace YangMills.Dimensions

noncomputable section

/-- Horizontal integer indices in one exact positive-radius box. -/
abbrev SquareLatticeBoxHorizontalIndex (radius : PositiveSquareLatticeBoxRadius) :=
  {horizontal : ℤ // horizontal ∈ squareLatticeBoxInterval radius}

/-- The exact right-directed box coordinate at one horizontal/off-axis-row site. -/
def boxCoordinateOfSite
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius →
      EpsilonSquareLatticeBoxCoordinate spacing radius :=
  fun site =>
    ⟨epsilonSquareLatticeRightBond spacing (site.1.1, site.2.1),
      epsilonSquareLatticeBoxAxialCoordinates.mem_of_site spacing radius
        (site.1.1, site.2.1) site.1.2 site.2.2⟩

@[simp]
theorem boxCoordinateOfSite_val
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) :
    (boxCoordinateOfSite spacing radius site).1 =
      epsilonSquareLatticeRightBond spacing (site.1.1, site.2.1) :=
  rfl

@[simp]
theorem boxCoordinateOfSite_source
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) :
    (boxCoordinateOfSite spacing radius site).1.source = (site.1.1, site.2.1) :=
  rfl

@[simp]
theorem boxCoordinateOfSite_target
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) :
    (boxCoordinateOfSite spacing radius site).1.target = (site.1.1 + 1, site.2.1) :=
  rfl

/-- Distinct exact sites give distinct box coordinates. -/
theorem boxCoordinateOfSite_injective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (boxCoordinateOfSite spacing radius) := by
  intro first second equality
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius =>
      coordinate.1.source.1) equality
  · apply Subtype.ext
    exact congrArg (fun coordinate : EpsilonSquareLatticeBoxCoordinate spacing radius =>
      coordinate.1.source.2) equality

/-- Every exact box coordinate comes from its unique horizontal/off-axis-row site. -/
theorem boxCoordinateOfSite_surjective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxCoordinateOfSite spacing radius) := by
  rintro ⟨bond, membership⟩
  simp only [epsilonSquareLatticeBoxAxialCoordinates, Finset.mem_image] at membership
  obtain ⟨site, siteMembership, equality⟩ := membership
  obtain ⟨horizontalMembership, rowMembership⟩ := Finset.mem_product.mp siteMembership
  refine ⟨(⟨site.1, horizontalMembership⟩, ⟨site.2, rowMembership⟩), ?_⟩
  apply Subtype.ext
  exact equality

/-- Exact site equivalence for independent box coordinates. -/
def boxCoordinateSiteEquiv
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) ≃
      EpsilonSquareLatticeBoxCoordinate spacing radius :=
  Equiv.ofBijective (boxCoordinateOfSite spacing radius)
    ⟨boxCoordinateOfSite_injective spacing radius,
      boxCoordinateOfSite_surjective spacing radius⟩

@[simp]
theorem boxCoordinateSiteEquiv_apply
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) :
    boxCoordinateSiteEquiv spacing radius site = boxCoordinateOfSite spacing radius site :=
  rfl

@[simp]
theorem boxCoordinateSiteEquiv_val
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxOffAxisRow radius) :
    (boxCoordinateSiteEquiv spacing radius site).1 =
      epsilonSquareLatticeRightBond spacing (site.1.1, site.2.1) :=
  rfl

/-- The exact elementary plaquette at one horizontal/lower-left-row site. -/
def boxPlaquetteOfSite
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius →
      EpsilonSquareLatticeBoxPlaquette spacing radius :=
  fun site =>
    ⟨⟨(site.1.1, site.2.1)⟩,
      Finset.mem_image.mpr
        ⟨(site.1.1, site.2.1), Finset.mem_product.mpr ⟨site.1.2, site.2.2⟩, rfl⟩⟩

@[simp]
theorem boxPlaquetteOfSite_val
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius) :
    (boxPlaquetteOfSite spacing radius site).1 =
      (⟨(site.1.1, site.2.1)⟩ : EpsilonSquareLatticePlaquette spacing) :=
  rfl

@[simp]
theorem boxPlaquetteOfSite_lowerLeft
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius) :
    (boxPlaquetteOfSite spacing radius site).1.lowerLeft = (site.1.1, site.2.1) :=
  rfl

/-- Distinct exact lower-left sites give distinct box plaquettes. -/
theorem boxPlaquetteOfSite_injective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Injective (boxPlaquetteOfSite spacing radius) := by
  intro first second equality
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius =>
      plaquette.1.lowerLeft.1) equality
  · apply Subtype.ext
    exact congrArg (fun plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius =>
      plaquette.1.lowerLeft.2) equality

/-- Every exact box plaquette comes from its unique lower-left site. -/
theorem boxPlaquetteOfSite_surjective
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    Function.Surjective (boxPlaquetteOfSite spacing radius) := by
  rintro ⟨plaquette, membership⟩
  simp only [epsilonSquareLatticeBoxPlaquettes, Finset.mem_image] at membership
  obtain ⟨site, siteMembership, equality⟩ := membership
  obtain ⟨horizontalMembership, rowMembership⟩ := Finset.mem_product.mp siteMembership
  refine ⟨(⟨site.1, horizontalMembership⟩, ⟨site.2, rowMembership⟩), ?_⟩
  apply Subtype.ext
  exact equality

/-- Exact site equivalence for box plaquettes. -/
def boxPlaquetteSiteEquiv
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius) ≃
      EpsilonSquareLatticeBoxPlaquette spacing radius :=
  Equiv.ofBijective (boxPlaquetteOfSite spacing radius)
    ⟨boxPlaquetteOfSite_injective spacing radius,
      boxPlaquetteOfSite_surjective spacing radius⟩

@[simp]
theorem boxPlaquetteSiteEquiv_apply
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius) :
    boxPlaquetteSiteEquiv spacing radius site = boxPlaquetteOfSite spacing radius site :=
  rfl

@[simp]
theorem boxPlaquetteSiteEquiv_lowerLeft
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × SquareLatticeBoxPlaquetteRow radius) :
    (boxPlaquetteSiteEquiv spacing radius site).1.lowerLeft = (site.1.1, site.2.1) :=
  rfl

/-- Exact positive/negative-chain equivalence for independent box coordinates. -/
def boxCoordinateChainEquiv
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) ≃
      EpsilonSquareLatticeBoxCoordinate spacing radius :=
  (Equiv.prodCongr (Equiv.refl _) (boxOffAxisRowEquiv radius)).trans
    (boxCoordinateSiteEquiv spacing radius)

@[simp]
theorem boxCoordinateChainEquiv_apply
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) :
    boxCoordinateChainEquiv spacing radius site =
      boxCoordinateOfSite spacing radius (site.1, boxOffAxisRowEquiv radius site.2) :=
  rfl

@[simp]
theorem boxCoordinateChainEquiv_source
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) :
    (boxCoordinateChainEquiv spacing radius site).1.source =
      (site.1.1, (boxOffAxisRowEquiv radius site.2).1) :=
  rfl

@[simp]
theorem boxCoordinateChainEquiv_source_inl
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inl index)).1.source =
      (horizontal.1, (index.1 : ℤ) + 1) := by
  simp [epsilonSquareLatticeRightBond]

@[simp]
theorem boxCoordinateChainEquiv_source_inr
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxCoordinateChainEquiv spacing radius (horizontal, Sum.inr index)).1.source =
      (horizontal.1, -((index.1 : ℤ) + 1)) := by
  simp [epsilonSquareLatticeRightBond]

/-- Exact positive/negative-chain equivalence for box plaquettes. -/
def boxPlaquetteChainEquiv
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius) :
    (SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) ≃
      EpsilonSquareLatticeBoxPlaquette spacing radius :=
  (Equiv.prodCongr (Equiv.refl _) (boxPlaquetteRowEquiv radius)).trans
    (boxPlaquetteSiteEquiv spacing radius)

@[simp]
theorem boxPlaquetteChainEquiv_apply
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) :
    boxPlaquetteChainEquiv spacing radius site =
      boxPlaquetteOfSite spacing radius (site.1, boxPlaquetteRowEquiv radius site.2) :=
  rfl

@[simp]
theorem boxPlaquetteChainEquiv_lowerLeft
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (site : SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) :
    (boxPlaquetteChainEquiv spacing radius site).1.lowerLeft =
      (site.1.1, (boxPlaquetteRowEquiv radius site.2).1) :=
  rfl

@[simp]
theorem boxPlaquetteChainEquiv_lowerLeft_inl
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)).1.lowerLeft =
      (horizontal.1, (index.1 : ℤ)) := by
  simp

@[simp]
theorem boxPlaquetteChainEquiv_lowerLeft_inr
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)).1.lowerLeft =
      (horizontal.1, -((index.1 : ℤ) + 1)) := by
  simp

end

end YangMills.Dimensions
