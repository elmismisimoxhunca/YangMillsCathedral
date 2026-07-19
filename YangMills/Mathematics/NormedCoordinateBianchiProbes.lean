/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedCoordinateBianchi

/-!
# Hostile probes for normed-coordinate Bianchi

These probes lock the curvature normalization, the same-connection covariant exterior expression,
coordinate cubic Jacobi cancellation, the derived Bianchi identity, and rejection of unrelated
curvature or nonzero Bianchi outputs.
-/

namespace YangMills.Mathematics.NormedCoordinateBianchi.Probes

open scoped Manifold ContDiff

universe uT uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- Curvature uses exactly `dA + 1/2 [A ∧ A]` with the canonical bracket. -/
theorem exact_curvature_formula
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (x : T) :
    groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection x =
      extDeriv connection x + (1 / 2 : ℝ) •
        (connection x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1
          (connection x) :=
  rfl

/-- The degree-two covariant exterior expression uses the same connection and canonical bracket. -/
theorem exact_covariant_exterior_formula
    (connection : T → T [⋀^Fin 1]→L[ℝ] E)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) (x : T) :
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
        (I := I) (G := G) connection form x =
      extDeriv form x +
        (connection x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2 (form x) :=
  rfl

/-- Cubic cancellation is exact for the same canonical coordinate bracket. -/
theorem exact_cubic_jacobi
    (connection : T [⋀^Fin 1]→L[ℝ] E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let bracket := groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)
    connection.continuousBilinearWedgeOneMany bracket 2
      (connection.continuousBilinearWedgeOneMany bracket 1 connection) = 0 :=
  groupLieAlgebraCoordinateSelfWedge_cubic (I := I) (G := G) connection

/-- The Bianchi identity is derived from a twice continuously differentiable connection. -/
theorem exact_bianchi
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (x : T)
    (connection_regular : ContDiffAt ℝ 2 connection x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
      (I := I) (G := G) connection
      (groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection) x = 0 :=
  groupLieAlgebraCoordinate_bianchi (I := I) (G := G)
    connection x connection_regular

/-- An unrelated two-form cannot be substituted for the curvature definition. -/
theorem unrelated_curvature_blocked
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (x : T)
    (other : T [⋀^Fin 2]→L[ℝ] E)
    (different : other ≠ extDeriv connection x + (1 / 2 : ℝ) •
      (connection x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1 (connection x))
    (claimed : groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection x = other) :
    False := by
  apply different
  rw [← claimed]
  rfl

/-- A nonzero value for the exact same-connection Bianchi expression is impossible. -/
theorem nonzero_bianchi_blocked
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (x : T)
    (connection_regular : ContDiffAt ℝ 2 connection x)
    (claimed_nonzero :
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
        (I := I) (G := G) connection
        (groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection) x ≠ 0) : False :=
  claimed_nonzero
    (groupLieAlgebraCoordinate_bianchi (I := I) (G := G)
      connection x connection_regular)

end YangMills.Mathematics.NormedCoordinateBianchi.Probes
