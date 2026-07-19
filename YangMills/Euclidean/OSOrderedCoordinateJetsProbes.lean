/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedCoordinateJets

/-! Hostile probes for coordinate-basis jets of the OS ordered Fréchet candidate. -/

namespace YangMills.OSOrderedCoordinateJets.Probes

open Set

noncomputable section

/-- The configuration basis has the exact point/coordinate Kronecker values. -/
theorem exact_coordinate_basis_value
    (d : EuclideanDimension) (n : ℕ)
    (point otherPoint : Fin n) (coordinate otherCoordinate : d.CoordinateIndex) :
    euclideanNPointCoordinateBasis d n ⟨point, coordinate⟩ otherPoint otherCoordinate =
      if otherPoint = point then (if otherCoordinate = coordinate then 1 else 0) else 0 := by
  classical
  by_cases hp : otherPoint = point
  · subst otherPoint
    simp [euclideanNPointCoordinateBasis, Pi.basis_apply,
      EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · simp [euclideanNPointCoordinateBasis, Pi.basis_apply,
      EuclideanSpace.basisFun_apply, hp]

/-- Coordinate-jet vanishing and full Fréchet-map vanishing are exactly equivalent internally. -/
theorem exact_frechet_coordinate_equivalence
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) :
    IsOSPositiveTimeOrderedDerivativeVanishing f ↔
      IsOSPositiveTimeOrderedCoordinateJetVanishing f :=
  osPositiveTimeOrderedFrechet_iff_coordinateJets f

/-- A nonzero derivative map is detected by an actual tuple of configuration-coordinate basis
vectors, blocking a disconnected coordinate family. -/
theorem nonzero_derivative_detected
    {d : EuclideanDimension} {n k : ℕ}
    (f : ScalarSchwartzTestFunction d n) (x : EuclideanNPointSpace d n)
    (hne : iteratedFDeriv ℝ k (f : EuclideanNPointSpace d n → ℂ) x ≠ 0) :
    ∃ directions : Fin k → ((_point : Fin n) × d.CoordinateIndex),
      iteratedFDeriv ℝ k (f : EuclideanNPointSpace d n → ℂ) x
        (fun j => euclideanNPointCoordinateBasis d n (directions j)) ≠ 0 :=
  Mathematics.exists_basis_evaluation_ne_zero_of_ne_zero
    (euclideanNPointCoordinateBasis d n) hne

/-- The carrier equivalence preserves the exact same Schwartz test rather than a disconnected
replacement. -/
theorem exact_carrier_identification
    {d : EuclideanDimension} {n : ℕ}
    (f : OSPositiveTimeOrderedCoordinateJetCarrier d n) :
    (OSPositiveTimeOrderedCoordinateJetCarrier.equivFrechetCarrier f).toSchwartz =
      f.toSchwartz :=
  rfl

/-- The coordinate-jet presentation retains an explicit nonzero positive-time test. -/
theorem nonzero_coordinate_jet_test_exists (d : EuclideanDimension) :
    ∃ f : OSPositiveTimeOrderedCoordinateJetCarrier d 1, f.toSchwartz ≠ 0 :=
  ⟨OSPositiveTimeOrderedCoordinateJetCarrier.positiveTimeBump d,
    OSPositiveTimeOrderedCoordinateJetCarrier.positiveTimeBump_toSchwartz_ne_zero d⟩

end

end YangMills.OSOrderedCoordinateJets.Probes
