/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteLatticeTimeReflection

/-!
# Hostile probes for finite lattice time reflection

The probes expose a genuinely moved periodic coordinate, orientation reversal of time links,
unchanged spatial orientation, gauge covariance, and inhabited strict positive-time link regions.
They do not assert reflection positivity.
-/

namespace YangMills.Lattice.FiniteLatticeTimeReflection.Probes

/-- Six-site periodic time geometry in dimension one. -/
def sixSiteOneDimensionalGeometry :
    FiniteLatticeTimeReflectionGeometry EuclideanDimension.one ⟨5⟩ where
  timeDirection := ⟨0, by decide⟩
  extent_even := ⟨3, by norm_num [FinitePeriodicLattice.extent]⟩
  four_le_extent := by norm_num [FinitePeriodicLattice.extent]

/-- Reflection is not merely the identity: time `1` maps to time `5` on six sites. -/
theorem six_site_coordinate_reflection_nontrivial :
    periodicTimeReflectionCoordinate (⟨5⟩ : FinitePeriodicLattice)
      (⟨1, by norm_num [FinitePeriodicLattice.extent]⟩ :
        Fin (⟨5⟩ : FinitePeriodicLattice).extent) =
      (⟨5, by norm_num [FinitePeriodicLattice.extent]⟩ :
        Fin (⟨5⟩ : FinitePeriodicLattice).extent) := by
  decide

/-- A time-oriented link is read as the inverse link based at the reflected endpoint. -/
theorem exact_time_link_reflection
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (U : GaugeField d Λ G) (x : Vertex d Λ) :
    timeReflectGaugeField τ U ⟨x, τ⟩ =
      (U ⟨timeReflectVertex τ (shiftForward x τ), τ⟩)⁻¹ := by
  simp [timeReflectGaugeField, timeReflectedPositiveLink]

/-- A non-time link keeps its positive orientation at the reflected base. -/
theorem exact_spatial_link_reflection
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ μ : d.CoordinateIndex) (hμ : μ ≠ τ)
    (U : GaugeField d Λ G) (x : Vertex d Λ) :
    timeReflectGaugeField τ U ⟨x, μ⟩ = U ⟨timeReflectVertex τ x, μ⟩ := by
  simp [timeReflectGaugeField, timeReflectedPositiveLink, hμ]

/-- Double field reflection returns the exact original field. -/
theorem exact_field_reflection_involution
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (U : GaugeField d Λ G) :
    timeReflectGaugeField τ (timeReflectGaugeField τ U) = U :=
  timeReflectGaugeField_involutive τ U

/-- Reflected fields remain tied to the reflected transformation on exact link endpoints. -/
theorem exact_reflection_gauge_covariance
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (g : GaugeTransformation d Λ G)
    (U : GaugeField d Λ G) :
    timeReflectGaugeField τ (gaugeTransform g U) =
      gaugeTransform (timeReflectGaugeTransformation τ g) (timeReflectGaugeField τ U) :=
  timeReflectGaugeField_gaugeTransform τ g U

/-- The six-site one-dimensional positive half contains an actual positive time link `1 → 2`. -/
theorem six_site_one_dimensional_positive_link_nonempty :
    ∃ link : PositiveOrientedLink EuclideanDimension.one (⟨5⟩ : FinitePeriodicLattice),
      IsStrictPositiveTimeLink sixSiteOneDimensionalGeometry link := by
  let τ : EuclideanDimension.one.CoordinateIndex := ⟨0, by decide⟩
  let x : Vertex EuclideanDimension.one (⟨5⟩ : FinitePeriodicLattice) :=
    fun _ => (1 : Fin 6)
  refine ⟨⟨x, τ⟩, ?_⟩
  constructor
  · norm_num [IsStrictPositiveTimeVertex, sixSiteOneDimensionalGeometry, x, τ,
      FinitePeriodicLattice.extent]
  · change 0 < ((shiftForward x τ) τ).val ∧ ((shiftForward x τ) τ).val < 3
    norm_num [shiftForward, x, τ, cyclicSucc, FinitePeriodicLattice.extent, Fin.val_add]

/-- In dimension two the positive half also contains a spatial link at time `1`. -/
theorem six_site_two_dimensional_spatial_positive_link_nonempty :
    ∃ (geometry : FiniteLatticeTimeReflectionGeometry EuclideanDimension.two ⟨5⟩)
      (link : PositiveOrientedLink EuclideanDimension.two (⟨5⟩ : FinitePeriodicLattice)),
      link.direction ≠ geometry.timeDirection ∧ IsStrictPositiveTimeLink geometry link := by
  let τ : EuclideanDimension.two.CoordinateIndex := ⟨0, by decide⟩
  let μ : EuclideanDimension.two.CoordinateIndex := ⟨1, by decide⟩
  let geometry : FiniteLatticeTimeReflectionGeometry EuclideanDimension.two ⟨5⟩ :=
    ⟨τ, ⟨3, by norm_num [FinitePeriodicLattice.extent]⟩,
      by norm_num [FinitePeriodicLattice.extent]⟩
  let x : Vertex EuclideanDimension.two (⟨5⟩ : FinitePeriodicLattice) :=
    fun i => if i = τ then
      (⟨1, by norm_num [FinitePeriodicLattice.extent]⟩ :
        Fin (⟨5⟩ : FinitePeriodicLattice).extent)
      else ⟨0, by norm_num [FinitePeriodicLattice.extent]⟩
  refine ⟨geometry, ⟨x, μ⟩, ?_, ?_⟩
  · decide
  · constructor <;>
      norm_num [IsStrictPositiveTimeVertex, geometry, x, τ, μ,
        shiftForward, cyclicSucc, FinitePeriodicLattice.extent]

end YangMills.Lattice.FiniteLatticeTimeReflection.Probes
