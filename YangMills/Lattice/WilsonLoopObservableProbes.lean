/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.WilsonLoopObservable

/-!
# Hostile probes for finite lattice Wilson loops

The probes expose signed-link endpoint covariance, nonempty and plaquette paths, exact plaquette
closure/holonomy, class-function nontriviality, and closed-loop gauge invariance. No expectation,
area law, or continuum observable is constructed.
-/

namespace YangMills.Lattice.WilsonLoopObservable.Probes

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]

/-- Backward traversal uses the inverse positive link based one step backward. -/
theorem exact_backward_link_value
    (U : GaugeField d Λ G) (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    orientedLinkValue U x (.backward μ) =
      (U ⟨shiftBackward x μ, μ⟩)⁻¹ :=
  rfl

/-- Every signed link transforms at its exact traversal endpoints. -/
theorem exact_signed_link_covariance
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (step : SignedDirection d) :
    orientedLinkValue (gaugeTransform g U) x step =
      g x * orientedLinkValue U x step * (g (stepEndpoint x step))⁻¹ :=
  orientedLinkValue_gaugeTransform g U x step

/-- Empty path holonomy is the group identity. -/
@[simp] theorem empty_path_holonomy
    (U : GaugeField d Λ G) (x : Vertex d Λ) :
    pathHolonomy U x [] = 1 :=
  rfl

/-- Empty paths are closed, but plaquette probes below prevent using only this trivial loop. -/
@[simp] theorem empty_path_closed (x : Vertex d Λ) : IsClosedPath x [] :=
  rfl

/-- Arbitrary path holonomy transforms only at its exact initial/final endpoints. -/
theorem exact_path_endpoint_covariance
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    pathHolonomy (gaugeTransform g U) x path =
      g x * pathHolonomy U x path * (g (pathEndpoint x path))⁻¹ :=
  pathHolonomy_gaugeTransform g U x path

/-- The explicit four-step elementary plaquette path is closed. -/
theorem exact_plaquette_path_closed
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    IsClosedPath x (plaquettePath μ ν) :=
  plaquettePath_closed x hμν

/-- Its path holonomy is exactly the independently defined plaquette holonomy. -/
theorem exact_plaquette_path_holonomy
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    pathHolonomy U x (plaquettePath μ ν) = plaquetteHolonomy U x μ ν :=
  pathHolonomy_plaquettePath U x hμν

/-- The supplied loop interpretation cannot be a constant function. -/
theorem constant_class_observable_blocked
    (χ : GaugeInvariantClassObservable G) :
    χ.observable ≠ fun _ => χ.observable 1 := by
  rcases χ.nontrivial with ⟨u, hu⟩
  intro hconstant
  exact hu (congrFun hconstant u)

/-- Every exact closed-loop class observable is locally gauge invariant. -/
theorem exact_closed_loop_gauge_invariance
    (χ : GaugeInvariantClassObservable G)
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (hclosed : IsClosedPath x path) :
    wilsonLoopObservable χ (gaugeTransform g U) x path =
      wilsonLoopObservable χ U x path :=
  wilsonLoopObservable_gaugeInvariant χ g U x path hclosed

/-- The nontrivial four-step plaquette loop itself gives an exact gauge-invariant observable. -/
theorem exact_plaquette_loop_gauge_invariance
    (χ : GaugeInvariantClassObservable G)
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    wilsonLoopObservable χ (gaugeTransform g U) x (plaquettePath μ ν) =
      wilsonLoopObservable χ U x (plaquettePath μ ν) :=
  wilsonLoopObservable_gaugeInvariant χ g U x _ (plaquettePath_closed x hμν)

end YangMills.Lattice.WilsonLoopObservable.Probes
