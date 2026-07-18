/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteLatticeReflectionPositivity

/-!
# Hostile probes for finite lattice reflection positivity

These probes show that positivity uses the exact Gibbs measure, reflection, support predicate, and a
nonzero nonempty-support domain. They do not produce a positivity datum or continuum OS `(E2)`.
-/

namespace YangMills.Lattice.FiniteLatticeReflectionPositivity.Probes

open MeasureTheory

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}

/-- A closed Wilson loop enters the positivity domain with its exact path support. -/
theorem exact_supported_wilson_loop
    [MeasurableMul₂ G]
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (hclosed : IsClosedPath x path) :
    (finiteSupportedWilsonLoopObservable χ x path hclosed).linkSupport =
      pathLinkSupport x path :=
  rfl

variable
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    {gibbs : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling}
    {geometry : FiniteLatticeTimeReflectionGeometry d Λ}

/-- The reflection-square integrand is genuinely integrable under the exact specialized measure. -/
theorem exact_reflection_square_integrability
    (gibbs : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _) :
    Integrable (finiteLatticeReflectionSquareObservable geometry.timeDirection F)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) :=
  finiteLatticeReflectionSquareObservable_integrable gibbs geometry F

/-- Accepted data make the explicit field reflection measure preserving on the same Gibbs chain. -/
theorem exact_reflection_measure_preserving
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    MeasurePreserving (timeReflectGaugeField geometry.timeDirection)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) :=
  data.reflection_measurePreserving

/-- Positivity and reality apply only after exact strict-positive support is supplied. -/
theorem exact_finite_cutoff_reflection_positivity
    (data : FiniteLatticeReflectionPositivityData gibbs geometry)
    (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _)
    (hpositive : ∀ link ∈ F.linkSupport, IsStrictPositiveTimeLink geometry link) :
    (finiteLatticeReflectionPairing gibbs geometry F).im = 0 ∧
      0 ≤ (finiteLatticeReflectionPairing gibbs geometry F).re :=
  data.reflection_positive F hpositive

/-- The accepted domain contains actual one-link dependence, not a constant with fake support. -/
theorem fake_support_on_constant_blocked
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    ∃ (F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _)
      (link : PositiveOrientedLink d Λ),
      link ∈ F.linkSupport ∧ DependsNontriviallyOnLink F link := by
  rcases data.nontrivial_positive_test with ⟨F, link, hmem, _, hdepends⟩
  exact ⟨F, link, hmem, hdepends⟩

/-- Actual dependence rejects the zero-only-observable shortcut. -/
theorem zero_only_positive_domain_blocked
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    ∃ F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _,
      F.observable.toFun ≠ 0 := by
  rcases data.nontrivial_positive_test with
    ⟨F, link, _, _, U, V, _, hne⟩
  refine ⟨F, ?_⟩
  intro hzero
  apply hne
  rw [hzero]
  rfl

/-- The empty-support-only shortcut is separately rejected by the depended-on member. -/
theorem empty_support_only_domain_blocked
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    ∃ F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _,
      F.linkSupport.Nonempty := by
  rcases data.nontrivial_positive_test with ⟨F, link, hmem, _, _⟩
  exact ⟨F, ⟨link, hmem⟩⟩

/-- The nontrivial test is tied to this geometry's strict positive half, not an unrelated region. -/
theorem unrelated_positive_region_blocked
    (data : FiniteLatticeReflectionPositivityData gibbs geometry) :
    ∃ F : @FiniteSupportedGaugeInvariantLatticeObservable d Λ G _ _,
      F.linkSupport.Nonempty ∧
      ∀ link ∈ F.linkSupport, IsStrictPositiveTimeLink geometry link := by
  rcases data.nontrivial_positive_test with ⟨F, link, hmem, hpositive, _⟩
  exact ⟨F, ⟨link, hmem⟩, hpositive⟩

end YangMills.Lattice.FiniteLatticeReflectionPositivity.Probes
