/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedDerivativeCarrier

/-!
# Hostile probes for the OS ordered Fréchet candidate

These probes lock the candidate's all-order exterior vanishing law, induced topology, strict-carrier inclusion,
coincidence flatness, and nonzero arity-one test. The constructor surface deliberately has no
open-set topological-support field.
-/

namespace YangMills.OSOrderedDerivativeCarrier.Probes

open Set Topology

noncomputable section

/-- Constructor-surface probe: all-order derivative vanishing is sufficient; no strict topological-
support premise is accepted here. -/
def derivative_only_constructor_surface
    {d : EuclideanDimension} {n : ℕ}
    (f : ScalarSchwartzTestFunction d n)
    (h : IsOSPositiveTimeOrderedDerivativeVanishing f) :
    OSPositiveTimeOrderedDerivativeCarrier d n :=
  ⟨f, h⟩

/-- The derivative condition is an exact complex submodule, so sums and arbitrary complex
multiples remain in the same candidate condition. -/
theorem exact_complex_linear_closure
    {d : EuclideanDimension} {n : ℕ}
    (f g : ScalarSchwartzTestFunction d n)
    (hf : IsOSPositiveTimeOrderedDerivativeVanishing f)
    (hg : IsOSPositiveTimeOrderedDerivativeVanishing g)
    (scalar : ℂ) :
    f + g ∈ osPositiveTimeOrderedDerivativeSubmodule d n ∧
      scalar • f ∈ osPositiveTimeOrderedDerivativeSubmodule d n :=
  ⟨(osPositiveTimeOrderedDerivativeSubmodule d n).add_mem hf hg,
    (osPositiveTimeOrderedDerivativeSubmodule d n).smul_mem scalar hf⟩

/-- The candidate and named submodule presentations retain exactly the same Schwartz function. -/
theorem exact_submodule_identification
    {d : EuclideanDimension} {n : ℕ}
    (f : OSPositiveTimeOrderedDerivativeCarrier d n) :
    (OSPositiveTimeOrderedDerivativeCarrier.equivSubmodule f).1 = f.toSchwartz :=
  rfl

/-- The exact internal candidate law cannot be replaced by a disconnected value. -/
theorem exact_derivative_vanishing
    {d : EuclideanDimension} {n : ℕ}
    (f : OSPositiveTimeOrderedDerivativeCarrier d n)
    (k : ℕ) (x : EuclideanNPointSpace d n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet d n) :
    iteratedFDeriv ℝ k
      ((f.toSchwartz : ScalarSchwartzTestFunction d n) :
        EuclideanNPointSpace d n → ℂ) x = 0 :=
  f.derivative_vanishes_outside k x hx

/-- A Schwartz function with a nonzero jet outside the ordered region cannot masquerade as the
underlying test of this carrier. -/
theorem nonvanishing_outside_blocked
    {d : EuclideanDimension} {n : ℕ}
    (f : ScalarSchwartzTestFunction d n)
    (k : ℕ) (x : EuclideanNPointSpace d n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet d n)
    (hne : iteratedFDeriv ℝ k
      (f : EuclideanNPointSpace d n → ℂ) x ≠ 0) :
    ¬ ∃ accepted : OSPositiveTimeOrderedDerivativeCarrier d n,
      accepted.toSchwartz = f := by
  rintro ⟨accepted, equality⟩
  apply hne
  rw [← equality]
  exact accepted.derivative_vanishes_outside k x hx

/-- The strict-carrier inclusion preserves the underlying Schwartz test exactly. -/
theorem strict_inclusion_exact
    {d : EuclideanDimension} {n : ℕ}
    (f : MathlibPositiveTimeOrderedFlatTestFunction d n) :
    (OSPositiveTimeOrderedDerivativeCarrier.ofStrictOrderedFlat f).toSchwartz =
      f.toSchwartz :=
  rfl

/-- Source-ordered derivative vanishing implies all-order coincidence flatness because coincident
configurations cannot be strictly ordered. -/
theorem coincidence_flat
    {d : EuclideanDimension} {n : ℕ}
    (f : OSPositiveTimeOrderedDerivativeCarrier d n) :
    IsFlatAtPointCoincidences f.toSchwartz := by
  intro k x coincidence
  rcases coincidence with ⟨i, j, hne, heq⟩
  apply f.derivative_vanishes_outside k x
  intro ordered
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hlt := ordered.2 i j hij
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · have hlt := ordered.2 j i hji
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)

/-- The carrier topology is genuinely the ambient induced topology. -/
theorem exact_induced_topology
    {d : EuclideanDimension} {n : ℕ} :
    IsInducing
      (OSPositiveTimeOrderedDerivativeCarrier.toSchwartz :
        OSPositiveTimeOrderedDerivativeCarrier d n → ScalarSchwartzTestFunction d n) :=
  OSPositiveTimeOrderedDerivativeCarrier.inducing_toSchwartz

/-- The explicit positive-time element blocks an empty/zero-only carrier surrogate. -/
theorem nonzero_positive_time_test_exists (d : EuclideanDimension) :
    ∃ f : OSPositiveTimeOrderedDerivativeCarrier d 1, f.toSchwartz ≠ 0 :=
  ⟨OSPositiveTimeOrderedDerivativeCarrier.positiveTimeBump d,
    OSPositiveTimeOrderedDerivativeCarrier.positiveTimeBump_toSchwartz_ne_zero d⟩

end

end YangMills.OSOrderedDerivativeCarrier.Probes
