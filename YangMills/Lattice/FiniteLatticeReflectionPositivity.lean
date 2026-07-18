/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteLatticeTimeReflection
import YangMills.Lattice.FiniteWilsonLoopExpectation

/-!
# Finite-cutoff lattice reflection-positivity interface

Osterwalder–Seiler 1978, Theorem 2.1 on p. 448, proves positivity of
`⟨(θF)F⟩` for gauge-invariant positive-time lattice observables. This module packages that exact
finite-cutoff obligation over the previously fixed product-Haar Gibbs chain. It does not reuse or
claim continuum Osterwalder–Schrader `(E2)`.

The reflection pairing is an actual integrable Gibbs expectation. Accepted positivity data must use
the explicit time reflection, a designated sufficient strict positive-link support, and the same
specialized Gibbs datum.
A nonzero test with nonempty positive support blocks the zero-observable and empty-region shortcuts.
No positivity datum, transfer matrix, Hamiltonian, continuum bridge, theory, or mass gap is built.
-/

namespace YangMills.Lattice

open MeasureTheory

/-- Bounded measurable finite lattice observable with a designated sufficient link support and exact local
gauge invariance. -/
structure FiniteSupportedGaugeInvariantLatticeObservable
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    (G : Type*) [Group G] [MeasurableSpace G] where
  observable : @FiniteLatticeObservable d Λ G _ _
  linkSupport : Finset (PositiveOrientedLink d Λ)
  depends_only_on_support : ∀ U V : GaugeField d Λ G,
    (∀ link ∈ linkSupport, U link = V link) → observable U = observable V
  gauge_invariant : ∀ (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G),
    observable (gaugeTransform g U) = observable U

instance
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] :
    CoeFun (@FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _)
      (fun _ => GaugeField d Λ G → ℂ) :=
  ⟨fun F => F.observable⟩

/-- A closed bounded measurable Wilson loop supplies an exact supported gauge-invariant observable. -/
def finiteSupportedWilsonLoopObservable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (hclosed : IsClosedPath x path) :
    @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _ where
  observable := finiteWilsonLoopObservable χ x path
  linkSupport := pathLinkSupport x path
  depends_only_on_support := fun U V h =>
    finiteWilsonLoopObservable_eq_of_eq_on_pathLinkSupport χ U V x path h
  gauge_invariant := fun g U =>
    finiteWilsonLoopObservable_gaugeInvariant χ g U x path hclosed

/-- Reflection-square observable `conj(F(θU)) * F(U)` on the same finite configuration space. -/
def finiteLatticeReflectionSquareObservable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (τ : d.CoordinateIndex)
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _) :
    @FiniteLatticeObservable d Λ G _ _ where
  toFun := fun U => starRingEnd ℂ (F (timeReflectGaugeField τ U)) * F U
  measurable :=
    (Complex.continuous_conj.measurable.comp
      (F.observable.measurable.comp (timeReflectGaugeField_measurable τ))).mul
      F.observable.measurable
  bound := F.observable.bound ^ 2
  bound_nonnegative := sq_nonneg _
  norm_le := by
    intro U
    rw [norm_mul, pow_two]
    simpa using mul_le_mul (F.observable.norm_le _) (F.observable.norm_le _)
      (norm_nonneg _) F.observable.bound_nonnegative

/-- Actual finite-cutoff reflection pairing under the exact specialized Gibbs measure. -/
noncomputable def finiteLatticeReflectionPairing
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (geometry : FiniteLatticeTimeReflectionGeometry d Λ)
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _) : ℂ :=
  finiteLatticeExpectation data.toFiniteLatticeGibbsMeasureData
    (finiteLatticeReflectionSquareObservable geometry.timeDirection F)

/-- Every reflection-square integrand is genuinely integrable before its pairing is taken. -/
theorem finiteLatticeReflectionSquareObservable_integrable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (geometry : FiniteLatticeTimeReflectionGeometry d Λ)
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _) :
    Integrable (finiteLatticeReflectionSquareObservable geometry.timeDirection F)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) := by
  simpa [normalizedFiniteProductHaarLatticeGibbsMeasure,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    (finiteLatticeReflectionSquareObservable geometry.timeDirection F).integrable
      data.toFiniteLatticeGibbsMeasureData

/-- An observable genuinely depends on one designated link if changing only that link can change
its value. -/
def DependsNontriviallyOnLink
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G]
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _)
    (link : PositiveOrientedLink d Λ) : Prop :=
  ∃ U V : GaugeField d Λ G,
    (∀ other, other ≠ link → U other = V other) ∧ F U ≠ F V

/-- Exact finite-cutoff Osterwalder–Seiler reflection-positivity obligation.

This is intentionally a separate lattice record and is not continuum OS `(E2)`. -/
structure FiniteLatticeReflectionPositivityData
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (gibbs : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (geometry : FiniteLatticeTimeReflectionGeometry d Λ) where
  /-- The same normalized Gibbs measure is invariant under the explicit time reflection. -/
  gibbs_reflection_invariant :
    Measure.map (timeReflectGaugeField (G := G) geometry.timeDirection)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) =
      normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling
  /-- Reflection pairings are real and nonnegative for every gauge-invariant observable supported
  strictly in the positive half. -/
  reflection_positive : ∀ F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _,
    (∀ link ∈ F.linkSupport, IsStrictPositiveTimeLink geometry link) →
      (finiteLatticeReflectionPairing gibbs geometry F).im = 0 ∧
      0 ≤ (finiteLatticeReflectionPairing gibbs geometry F).re
  /-- The accepted positive domain contains an observable that genuinely depends on a strict
  positive-time link; merely assigning a fake nonempty support to a constant is insufficient. -/
  nontrivial_positive_test :
    ∃ (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _)
      (link : PositiveOrientedLink d Λ),
      link ∈ F.linkSupport ∧
      (∀ other ∈ F.linkSupport, IsStrictPositiveTimeLink geometry other) ∧
      DependsNontriviallyOnLink F link

/-- Reflection invariance plus explicit measurability gives a genuine measure-preserving symmetry. -/
theorem FiniteLatticeReflectionPositivityData.reflection_measurePreserving
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    {gibbs : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling}
    {geometry : FiniteLatticeTimeReflectionGeometry d Λ}
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    MeasurePreserving (timeReflectGaugeField geometry.timeDirection)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) :=
  ⟨timeReflectGaugeField_measurable geometry.timeDirection,
    data.gibbs_reflection_invariant⟩

end YangMills.Lattice
