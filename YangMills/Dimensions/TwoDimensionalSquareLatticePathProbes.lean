/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticePath
import YangMills.Foundation.DimensionsProbes

/-!
# Probes for exact epsilon-square lattice paths
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticePath.Probes

open Set

noncomputable section

/-- Positive and negative horizontal nearest-neighbor bonds are admitted. -/
theorem horizontal_steps_are_nearest (m n : ℤ) :
    SquareLatticeNearestNeighbor (m, n) (m + 1, n) ∧
      SquareLatticeNearestNeighbor (m, n) (m - 1, n) := by
  constructor <;> simp [SquareLatticeNearestNeighbor]

/-- Positive and negative vertical nearest-neighbor bonds are admitted. -/
theorem vertical_steps_are_nearest (m n : ℤ) :
    SquareLatticeNearestNeighbor (m, n) (m, n + 1) ∧
      SquareLatticeNearestNeighbor (m, n) (m, n - 1) := by
  constructor <;> simp [SquareLatticeNearestNeighbor]

/-- A diagonal move is not a nearest-neighbor bond. -/
theorem diagonal_step_blocked (m n : ℤ) :
    ¬ SquareLatticeNearestNeighbor (m, n) (m + 1, n + 1) := by
  simp [SquareLatticeNearestNeighbor]

/-- A stationary node repetition is not a nearest-neighbor bond. -/
theorem zero_step_blocked (m n : ℤ) :
    ¬ SquareLatticeNearestNeighbor (m, n) (m, n) := by
  simp [SquareLatticeNearestNeighbor]
  omega

/-- Every certificate has positive spacing and at least one actual lattice bond. -/
theorem exact_nontrivial_lattice_path
    {curve : ℝ → EuclideanDimension.two.Spacetime} {ε : ℝ}
    (certificate : EpsilonSquareLatticePathCertificate curve ε) :
    0 < ε ∧ 2 ≤ certificate.nodes.length :=
  ⟨certificate.epsilon_pos, certificate.two_le_nodes_length⟩

/-- Every stored adjacent piece exposes the exact affine `εℤ²` coordinate formulas. -/
theorem exact_piece_geometry
    {curve : ℝ → EuclideanDimension.two.Spacetime} {ε : ℝ}
    (first second : ℝ × (ℤ × ℤ))
    (piece : EpsilonSquareLatticePathPiece curve ε first second) :
    first.1 < second.1 ∧ SquareLatticeNearestNeighbor first.2 second.2 ∧
      ∀ t ∈ Set.Icc first.1 second.1,
        twoDimensionalFirstCoordinate (curve t) =
          affineIntervalCoordinate first.1 second.1
            (ε * (first.2.1 : ℝ)) (ε * (second.2.1 : ℝ)) t ∧
        twoDimensionalSecondCoordinate (curve t) =
          affineIntervalCoordinate first.1 second.1
            (ε * (first.2.2 : ℝ)) (ε * (second.2.2 : ℝ)) t :=
  piece

/-- Zero lattice spacing cannot be substituted into a certificate. -/
theorem zero_spacing_blocked
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    (certificate : EpsilonSquareLatticePathCertificate curve 0) : False := by
  linarith [certificate.epsilon_pos]

/-- Exact square-lattice paths remain two-dimensional and cannot inhabit the Clay endpoint. -/
theorem square_lattice_path_not_four_dimensional :
    EuclideanDimension.two ≠ EuclideanDimension.four :=
  EuclideanDimension.two_ne_four

end

end YangMills.Dimensions.TwoDimensionalSquareLatticePath.Probes
