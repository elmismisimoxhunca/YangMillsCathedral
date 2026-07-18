/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteProductHaarGibbsMeasure

/-!
# Explicit finite periodic lattice time reflection

Osterwalder–Seiler 1978, pp. 447–449, reflects the time coordinate, positive-time bond variables,
and gauge-invariant observables before stating finite-cutoff reflection positivity. This module
constructs only that reflection geometry. A time-oriented positive link reverses orientation under
reflection and is therefore represented by the inverse link based at the reflected endpoint;
spatial positive links retain orientation at the reflected base.

The even-extent geometry record identifies a time direction and two reflection planes. Reflection
is proved involutive, measurable, and exactly covariant with endpoint gauge transformations. No
reflection-positivity theorem, transfer matrix, Hamiltonian, continuum OS axiom, Gibbs datum,
theory, or mass gap is constructed.
-/

namespace YangMills.Lattice

/-- Periodic reflection geometry with an even time circle and at least four time sites. -/
structure FiniteLatticeTimeReflectionGeometry
    (d : EuclideanDimension) (Λ : FinitePeriodicLattice) where
  /-- Distinguished Euclidean lattice time direction. -/
  timeDirection : d.CoordinateIndex
  /-- Even extent gives reflection planes at time `0` and `extent / 2`. -/
  extent_even : Even Λ.extent
  /-- At least four sites separate the two reflection planes. -/
  four_le_extent : 4 ≤ Λ.extent

/-- Reflection `t ↦ -t` on one nonempty periodic coordinate circle. -/
def periodicTimeReflectionCoordinate
    (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) : Fin Λ.extent := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  exact -i

/-- Periodic coordinate reflection is an involution. -/
@[simp] theorem periodicTimeReflectionCoordinate_involutive
    (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) :
    periodicTimeReflectionCoordinate Λ (periodicTimeReflectionCoordinate Λ i) = i := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  simp [periodicTimeReflectionCoordinate]

/-- Reflect exactly one distinguished coordinate of a periodic vertex. -/
def timeReflectVertex
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (τ : d.CoordinateIndex) (x : Vertex d Λ) : Vertex d Λ :=
  fun i => if i = τ then periodicTimeReflectionCoordinate Λ (x i) else x i

/-- Vertex time reflection is an exact involution. -/
@[simp] theorem timeReflectVertex_involutive
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (τ : d.CoordinateIndex) (x : Vertex d Λ) :
    timeReflectVertex τ (timeReflectVertex τ x) = x := by
  funext i
  by_cases h : i = τ <;> simp [timeReflectVertex, h]

/-- Reflecting a positive time step gives a backward step from the reflected vertex. -/
theorem timeReflectVertex_shiftForward_time
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (τ : d.CoordinateIndex) (x : Vertex d Λ) :
    timeReflectVertex τ (shiftForward x τ) =
      shiftBackward (timeReflectVertex τ x) τ := by
  funext i
  by_cases h : i = τ
  · subst i
    simp [timeReflectVertex, shiftForward, shiftBackward, cyclicSucc, cyclicPred,
      periodicTimeReflectionCoordinate]
    letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
    abel
  · simp [timeReflectVertex, shiftForward, shiftBackward, h]

/-- Reflection commutes with shifts in every non-time direction. -/
theorem timeReflectVertex_shiftForward_of_ne
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (τ μ : d.CoordinateIndex) (hμ : μ ≠ τ) (x : Vertex d Λ) :
    timeReflectVertex τ (shiftForward x μ) =
      shiftForward (timeReflectVertex τ x) μ := by
  funext i
  by_cases hi : i = μ
  · subst i
    simp [timeReflectVertex, shiftForward, hμ]
  · simp [timeReflectVertex, shiftForward, hi]

/-- Positive link whose value is read after reflecting a given positive link. -/
def timeReflectedPositiveLink
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (τ : d.CoordinateIndex) (link : PositiveOrientedLink d Λ) :
    PositiveOrientedLink d Λ :=
  if link.direction = τ then
    ⟨timeReflectVertex τ (shiftForward link.base τ), τ⟩
  else
    ⟨timeReflectVertex τ link.base, link.direction⟩

/-- Time reflection of a gauge field, with inversion exactly in the reversed time direction. -/
def timeReflectGaugeField
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (U : GaugeField d Λ G) : GaugeField d Λ G :=
  fun link => if link.direction = τ then
    (U (timeReflectedPositiveLink τ link))⁻¹
  else
    U (timeReflectedPositiveLink τ link)

/-- Gauge-field time reflection is an exact involution. -/
@[simp] theorem timeReflectGaugeField_involutive
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (U : GaugeField d Λ G) :
    timeReflectGaugeField τ (timeReflectGaugeField τ U) = U := by
  funext link
  rcases link with ⟨base, direction⟩
  by_cases h : direction = τ
  · subst direction
    simp only [timeReflectGaugeField, timeReflectedPositiveLink, ↓reduceIte, inv_inv]
    rw [timeReflectVertex_shiftForward_time, timeReflectVertex_involutive,
      shiftBackward_shiftForward]
  · simp [timeReflectGaugeField, timeReflectedPositiveLink, h, timeReflectVertex_involutive]

/-- The exact field-reflection map is measurable on product configuration space. -/
theorem timeReflectGaugeField_measurable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (τ : d.CoordinateIndex) :
    Measurable (timeReflectGaugeField (Λ := Λ) (G := G) τ :
      GaugeField d Λ G → GaugeField d Λ G) := by
  apply measurable_pi_iff.mpr
  intro link
  by_cases h : link.direction = τ
  · simpa [timeReflectGaugeField, h] using
      (measurable_pi_apply (X := fun _ : PositiveOrientedLink d Λ => G)
        (timeReflectedPositiveLink τ link)).inv
  · simpa [timeReflectGaugeField, h] using
      (measurable_pi_apply (X := fun _ : PositiveOrientedLink d Λ => G)
        (timeReflectedPositiveLink τ link))

/-- Reflect a local gauge transformation by precomposition with vertex reflection. -/
def timeReflectGaugeTransformation
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*}
    (τ : d.CoordinateIndex) (g : GaugeTransformation d Λ G) :
    GaugeTransformation d Λ G :=
  fun x => g (timeReflectVertex τ x)

/-- Reflection remains on the same endpoint gauge-action chain. -/
theorem timeReflectGaugeField_gaugeTransform
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (τ : d.CoordinateIndex) (g : GaugeTransformation d Λ G)
    (U : GaugeField d Λ G) :
    timeReflectGaugeField τ (gaugeTransform g U) =
      gaugeTransform (timeReflectGaugeTransformation τ g) (timeReflectGaugeField τ U) := by
  funext link
  rcases link with ⟨base, direction⟩
  by_cases h : direction = τ
  · subst direction
    simp only [timeReflectGaugeField, timeReflectedPositiveLink, ↓reduceIte,
      gaugeTransform, timeReflectGaugeTransformation]
    rw [timeReflectVertex_shiftForward_time, shiftForward_shiftBackward]
    group
  · simp only [timeReflectGaugeField, timeReflectedPositiveLink, h, ↓reduceIte,
      gaugeTransform, timeReflectGaugeTransformation]
    rw [timeReflectVertex_shiftForward_of_ne τ direction h]

/-- Strict positive-time vertices lie between the two reflection planes. -/
def IsStrictPositiveTimeVertex
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (geometry : FiniteLatticeTimeReflectionGeometry d Λ) (x : Vertex d Λ) : Prop :=
  0 < (x geometry.timeDirection).val ∧
    (x geometry.timeDirection).val < Λ.extent / 2

/-- A strict positive-time positive link has both endpoints strictly inside the positive half. -/
def IsStrictPositiveTimeLink
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (geometry : FiniteLatticeTimeReflectionGeometry d Λ)
    (link : PositiveOrientedLink d Λ) : Prop :=
  IsStrictPositiveTimeVertex geometry link.base ∧
    IsStrictPositiveTimeVertex geometry
      (shiftForward link.base link.direction)

end YangMills.Lattice
