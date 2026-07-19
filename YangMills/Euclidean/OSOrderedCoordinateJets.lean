/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedDerivativeCarrier
import YangMills.Mathematics.ContinuousMultilinearMapBasis

/-!
# Coordinate-basis jets for the OS ordered Fréchet candidate

OS-I printed p. 86 formulates ordered-space flatness using all coordinate partial derivatives.
This module moves the project candidate one step toward that source formulation: it constructs the
exact coordinate basis of the `n`-point Euclidean configuration space and proves that vanishing of
each iterated Fréchet derivative as a multilinear map is equivalent to vanishing on every tuple of
coordinate basis directions.

This module itself stops before the printed multi-index theorem. Downstream modules identify
repeated basis directions and multiplicities, prove permutation independence, interpret OS-I's
`D^α` at positive arity, and transport this candidate's closedness to those exact source spaces.
Finite-sequence topology, `(E2)` and reconstruction remain separate debt.
-/

namespace YangMills

open Set

noncomputable section

/-- Coordinate basis indexed by a point label and a spacetime coordinate label. -/
def euclideanNPointCoordinateBasis (d : EuclideanDimension) (n : ℕ) :
    Module.Basis ((_point : Fin n) × d.CoordinateIndex) ℝ (EuclideanNPointSpace d n) :=
  Pi.basis fun _ => (EuclideanSpace.basisFun d.CoordinateIndex ℝ).toBasis

/-- Candidate coordinate-jet condition: every ordered iterated derivative vanishes on every tuple
of exact configuration-coordinate basis vectors outside strict positive time order. -/
def IsOSPositiveTimeOrderedCoordinateJetVanishing
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) : Prop :=
  ∀ k : ℕ, ∀ x : EuclideanNPointSpace d n,
    x ∉ strictPositiveTimeOrderedConfigurationSet d n →
      ∀ directions : Fin k → ((_point : Fin n) × d.CoordinateIndex),
        iteratedFDeriv ℝ k (f : EuclideanNPointSpace d n → ℂ) x
          (fun j => euclideanNPointCoordinateBasis d n (directions j)) = 0

/-- Full Fréchet vanishing is exactly equivalent to vanishing on all coordinate-basis tuples. This
is an internal finite-dimensional basis theorem, not yet the source's multi-index identification. -/
theorem osPositiveTimeOrderedFrechet_iff_coordinateJets
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedCoordinateJetVanishing f := by
  constructor
  · intro frechet k x hx directions
    rw [frechet k x hx]
    rfl
  · intro coordinate k x hx
    apply Mathematics.continuousMultilinearMap_eq_zero_of_basis_evaluation
      (euclideanNPointCoordinateBasis d n)
    intro directions
    exact coordinate k x hx directions

/-- Coordinate-jet presentation of the same project candidate. -/
def OSPositiveTimeOrderedCoordinateJetCarrier
    (d : EuclideanDimension) (n : ℕ) :=
  {f : ScalarSchwartzTestFunction d n // IsOSPositiveTimeOrderedCoordinateJetVanishing f}

namespace OSPositiveTimeOrderedCoordinateJetCarrier

variable {d : EuclideanDimension} {n : ℕ}

/-- Exact equivalence between the Fréchet and coordinate-basis-jet candidate presentations. -/
def equivFrechetCarrier :
    OSPositiveTimeOrderedCoordinateJetCarrier d n ≃
      OSPositiveTimeOrderedDerivativeCarrier d n where
  toFun f := ⟨f.1, (osPositiveTimeOrderedFrechet_iff_coordinateJets f.1).mpr f.2⟩
  invFun f := ⟨f.1, (osPositiveTimeOrderedFrechet_iff_coordinateJets f.1).mp f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Forgetful map to the same exact ambient Schwartz test. -/
def toSchwartz (f : OSPositiveTimeOrderedCoordinateJetCarrier d n) :
    ScalarSchwartzTestFunction d n :=
  f.1

/-- The equivalence preserves the exact underlying Schwartz function. -/
@[simp]
theorem equivFrechetCarrier_toSchwartz
    (f : OSPositiveTimeOrderedCoordinateJetCarrier d n) :
    (equivFrechetCarrier f).toSchwartz = f.toSchwartz :=
  rfl

/-- The existing explicit nonzero positive-time bump in coordinate-jet presentation. -/
def positiveTimeBump (d : EuclideanDimension) :
    OSPositiveTimeOrderedCoordinateJetCarrier d 1 :=
  (equivFrechetCarrier (d := d) (n := 1)).symm
    (OSPositiveTimeOrderedDerivativeCarrier.positiveTimeBump d)

/-- Coordinate-jet presentation remains nonzero. -/
theorem positiveTimeBump_toSchwartz_ne_zero (d : EuclideanDimension) :
    (positiveTimeBump d).toSchwartz ≠ 0 :=
  positiveTimeBumpSchwartz_ne_zero d

end OSPositiveTimeOrderedCoordinateJetCarrier

end

end YangMills
