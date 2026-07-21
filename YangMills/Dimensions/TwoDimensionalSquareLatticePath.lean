/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAdmissibleCurve

/-!
# Exact paths in the epsilon-square lattice

Driver Definition 8.1 uses paths in the infinite directed nearest-neighbor graph on `εℤ²`. This
module gives that phrase an exact finite geometric certificate. Each node stores its parameter and
integer lattice coordinate; adjacent coordinates differ by exactly one horizontal or vertical unit,
and the curve is the affine nearest-neighbor segment on the corresponding parameter interval.

This is reusable two-dimensional lattice geometry. It constructs no approximating graph, action,
measure, continuum limit, or Yang--Mills theory.
-/

namespace YangMills.Dimensions

open Set

noncomputable section

/-- Two integer lattice sites are directed nearest neighbors exactly when one coordinate changes by
`±1` and the other is unchanged. -/
def SquareLatticeNearestNeighbor (first second : ℤ × ℤ) : Prop :=
  ((second.1 = first.1 + 1 ∨ second.1 = first.1 - 1) ∧ second.2 = first.2) ∨
  ((second.2 = first.2 + 1 ∨ second.2 = first.2 - 1) ∧ second.1 = first.1)

/-- One exact affinely parameterized nearest-neighbor bond in `εℤ²`. -/
def EpsilonSquareLatticePathPiece
    (curve : ℝ → EuclideanDimension.two.Spacetime) (ε : ℝ)
    (first second : ℝ × (ℤ × ℤ)) : Prop :=
  first.1 < second.1 ∧
    SquareLatticeNearestNeighbor first.2 second.2 ∧
    ∀ t ∈ Set.Icc first.1 second.1,
      twoDimensionalFirstCoordinate (curve t) =
        affineIntervalCoordinate first.1 second.1
          (ε * (first.2.1 : ℝ)) (ε * (second.2.1 : ℝ)) t ∧
      twoDimensionalSecondCoordinate (curve t) =
        affineIntervalCoordinate first.1 second.1
          (ε * (first.2.2 : ℝ)) (ε * (second.2.2 : ℝ)) t

/-- Exact finite path certificate in Driver's directed `ε`-square nearest-neighbor lattice. -/
structure EpsilonSquareLatticePathCertificate
    (curve : ℝ → EuclideanDimension.two.Spacetime) (ε : ℝ) where
  epsilon_pos : 0 < ε
  curve_continuous : Continuous curve
  nodes : List (ℝ × (ℤ × ℤ))
  nodes_nonempty : nodes ≠ []
  nodes_head_parameter : (nodes.head nodes_nonempty).1 = 0
  nodes_last_parameter : (nodes.getLast nodes_nonempty).1 = 1
  nodes_strict_parameter : nodes.Pairwise (fun first second => first.1 < second.1)
  pieces : nodes.IsChain (EpsilonSquareLatticePathPiece curve ε)

namespace EpsilonSquareLatticePathCertificate

/-- A path certificate cannot collapse to one node because its first and last parameters are
literally zero and one. -/
theorem nodes_ne_singleton
    {curve : ℝ → EuclideanDimension.two.Spacetime} {ε : ℝ}
    (certificate : EpsilonSquareLatticePathCertificate curve ε)
    (node : ℝ × (ℤ × ℤ)) : certificate.nodes ≠ [node] := by
  intro equality
  have head : node.1 = 0 := by
    simpa [equality] using certificate.nodes_head_parameter
  have last : node.1 = 1 := by
    simpa [equality] using certificate.nodes_last_parameter
  linarith

/-- Every certified lattice path contains at least one actual nearest-neighbor bond. -/
theorem two_le_nodes_length
    {curve : ℝ → EuclideanDimension.two.Spacetime} {ε : ℝ}
    (certificate : EpsilonSquareLatticePathCertificate curve ε) :
    2 ≤ certificate.nodes.length := by
  by_contra not_two
  by_cases length_zero : certificate.nodes.length = 0
  · exact certificate.nodes_nonempty (List.length_eq_zero_iff.mp length_zero)
  · have length_one : certificate.nodes.length = 1 := by omega
    obtain ⟨node, equality⟩ := List.length_eq_one_iff.mp length_one
    exact certificate.nodes_ne_singleton node equality

end EpsilonSquareLatticePathCertificate

end

end YangMills.Dimensions
