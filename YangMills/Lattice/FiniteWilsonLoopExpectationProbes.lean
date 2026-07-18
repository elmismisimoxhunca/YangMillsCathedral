/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteWilsonLoopExpectation

/-!
# Hostile probes for finitely supported Wilson-loop expectations

The probes expose exact nonempty supports, invariance under changes outside support, genuine
measurability/integrability, and the closed-path gate on expectations. No Gibbs datum is built.
-/

namespace YangMills.Lattice.FiniteWilsonLoopExpectation.Probes

open MeasureTheory

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}

/-- Empty paths have empty support. -/
@[simp] theorem empty_path_support (x : Vertex d Λ) :
    pathLinkSupport x [] = ∅ :=
  rfl

/-- A forward singleton reads exactly its displayed positive link. -/
@[simp] theorem forward_singleton_support
    (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    pathLinkSupport x [.forward μ] = {⟨x, μ⟩} := by
  simp [pathLinkSupport, orientedStepPositiveLink]

/-- A backward singleton reads exactly the inverse link based one step backward. -/
@[simp] theorem backward_singleton_support
    (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    pathLinkSupport x [.backward μ] = {⟨shiftBackward x μ, μ⟩} := by
  simp [pathLinkSupport, orientedStepPositiveLink]

/-- The explicit four-step plaquette cannot hide behind empty support. -/
theorem plaquette_support_nonempty
    (x : Vertex d Λ) (μ ν : d.CoordinateIndex) :
    (pathLinkSupport x (plaquettePath μ ν)).Nonempty := by
  refine ⟨⟨x, μ⟩, ?_⟩
  simp [plaquettePath, pathLinkSupport, orientedStepPositiveLink]

/-- Altering arbitrarily many links outside the exact path support cannot change holonomy. -/
theorem outside_support_changes_do_not_change_holonomy
    (U V : GaugeField d Λ G) (x : Vertex d Λ)
    (path : List (SignedDirection d))
    (h : ∀ link ∈ pathLinkSupport x path, U link = V link) :
    pathHolonomy U x path = pathHolonomy V x path :=
  pathHolonomy_eq_of_eq_on_pathLinkSupport U V x path h

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The bounded Wilson-loop package remains finitely supported on the same links. -/
theorem outside_support_changes_do_not_change_observable
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (U V : GaugeField d Λ G) (x : Vertex d Λ)
    (path : List (SignedDirection d))
    (h : ∀ link ∈ pathLinkSupport x path, U link = V link) :
    finiteWilsonLoopObservable χ x path U = finiteWilsonLoopObservable χ x path V :=
  finiteWilsonLoopObservable_eq_of_eq_on_pathLinkSupport χ U V x path h

/-- Measurability is carried by the exact path holonomy, not postulated for an unrelated function. -/
theorem exact_wilson_loop_measurability
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    Measurable (finiteWilsonLoopObservable χ x path : GaugeField d Λ G → ℂ) :=
  (finiteWilsonLoopObservable χ x path).measurable

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]

/-- The packaged observable is actually integrable under the same specialized Gibbs measure. -/
theorem exact_wilson_loop_integrability
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    Integrable (finiteWilsonLoopObservable χ x path)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) := by
  simpa [normalizedFiniteProductHaarLatticeGibbsMeasure,
    FiniteProductHaarGibbsMeasureData.toFiniteLatticeGibbsMeasureData] using
    (finiteWilsonLoopObservable χ x path).integrable
      data.toFiniteLatticeGibbsMeasureData

/-- A two-site one-dimensional forward step is genuinely open, so closure is not automatic. -/
theorem two_site_forward_path_not_closed :
    ¬ IsClosedPath (Λ := (⟨1⟩ : FinitePeriodicLattice))
      (fun _ : EuclideanDimension.one.CoordinateIndex => (0 : Fin 2))
      [.forward (⟨0, by decide⟩ : EuclideanDimension.one.CoordinateIndex)] := by
  intro h
  change shiftForward (fun _ : EuclideanDimension.one.CoordinateIndex => (0 : Fin 2))
    (⟨0, by decide⟩ : EuclideanDimension.one.CoordinateIndex) =
      (fun _ : EuclideanDimension.one.CoordinateIndex => (0 : Fin 2)) at h
  have hcoord := congrFun h (⟨0, by decide⟩ : EuclideanDimension.one.CoordinateIndex)
  have hval := congrArg Fin.val hcoord
  norm_num [shiftForward, cyclicSucc, FinitePeriodicLattice.extent, Fin.val_add] at hval

/-- The expectation definition retains the supplied closure proof and exact specialized measure. -/
theorem exact_closed_loop_expectation
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (hclosed : IsClosedPath x path) :
    finiteProductHaarWilsonLoopExpectation data χ x path hclosed =
      finiteLatticeExpectation data.toFiniteLatticeGibbsMeasureData
        (finiteWilsonLoopObservable χ x path) :=
  rfl

end YangMills.Lattice.FiniteWilsonLoopExpectation.Probes
