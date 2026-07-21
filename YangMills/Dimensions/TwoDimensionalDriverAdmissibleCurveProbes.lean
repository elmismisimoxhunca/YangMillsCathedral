/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalDriverAdmissibleCurve

/-!
# Probes for Driver-admissible curve certificates

The probes retain literal coordinates, strict finite subdivision, exact vertical-or-horizontal
piece shape, and the nonempty piece requirement.
-/

namespace YangMills.Dimensions.TwoDimensionalDriverAdmissibleCurve.Probes

open Set
open scoped ContDiff

noncomputable section

/-- Every certified adjacent piece has positive parameter length and exactly one of the source-facing
vertical or `C¹` horizontal presentations. -/
theorem exact_piece_shape
    (curve : ℝ → EuclideanDimension.two.Spacetime)
    (start finish : ℝ)
    (piece : IsDriverAdmissibleCurvePiece curve start finish) :
    start < finish ∧
      ((∃ x yStart yEnd : ℝ, ∀ t ∈ Set.Icc start finish,
          twoDimensionalFirstCoordinate (curve t) = x ∧
          twoDimensionalSecondCoordinate (curve t) =
            affineIntervalCoordinate start finish yStart yEnd t) ∨
        (∃ xStart xEnd : ℝ, ∃ height : ℝ → ℝ,
          xStart ≠ xEnd ∧ ContDiffOn ℝ 1 height (Set.uIcc xStart xEnd) ∧
          ∀ t ∈ Set.Icc start finish,
            let x := affineIntervalCoordinate start finish xStart xEnd t
            twoDimensionalFirstCoordinate (curve t) = x ∧
              twoDimensionalSecondCoordinate (curve t) = height x)) :=
  piece

/-- Every certificate starts at zero, ends at one, is strictly ordered, and certifies every adjacent
piece. -/
theorem exact_finite_subdivision
    (curve : ℝ → EuclideanDimension.two.Spacetime)
    (certificate : DriverAdmissibleCurveCertificate curve) :
    certificate.breakpoints.head certificate.breakpoints_nonempty = 0 ∧
      certificate.breakpoints.getLast certificate.breakpoints_nonempty = 1 ∧
      certificate.breakpoints.Pairwise (· < ·) ∧
      certificate.breakpoints.IsChain (IsDriverAdmissibleCurvePiece curve) :=
  ⟨certificate.breakpoints_head, certificate.breakpoints_last,
    certificate.breakpoints_strict, certificate.pieces⟩

/-- A source-admissible curve certificate has at least one piece. -/
theorem exact_nonempty_piece_count
    (curve : ℝ → EuclideanDimension.two.Spacetime)
    (certificate : DriverAdmissibleCurveCertificate curve) :
    2 ≤ certificate.breakpoints.length :=
  certificate.two_le_breakpoints_length

/-- A fake singleton subdivision cannot satisfy both exact endpoint parameters. -/
theorem singleton_subdivision_blocked
    (curve : ℝ → EuclideanDimension.two.Spacetime)
    (certificate : DriverAdmissibleCurveCertificate curve) (value : ℝ)
    (claimed : certificate.breakpoints = [value]) : False :=
  certificate.breakpoints_ne_singleton value claimed

end

end YangMills.Dimensions.TwoDimensionalDriverAdmissibleCurve.Probes
