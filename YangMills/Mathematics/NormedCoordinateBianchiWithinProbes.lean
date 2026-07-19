/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedCoordinateBianchiWithin

/-!
# Hostile probes for within-set normed-coordinate Bianchi
-/

namespace YangMills.Mathematics.NormedCoordinateBianchiWithin.Probes

open Set
open scoped Manifold ContDiff

universe uT uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- The within-set curvature retains the exact set and normalization. -/
theorem exact_curvatureWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) (x : T) :
    groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G) connection s x =
      extDerivWithin connection s x + (1 / 2 : ℝ) •
        (connection x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1
          (connection x) :=
  rfl

/-- The within-set covariant expression uses the same set, connection, and canonical bracket. -/
theorem exact_covariantWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) (x : T) :
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
        (I := I) (G := G) connection s form x =
      extDerivWithin form s x +
        (connection x).continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2 (form x) :=
  rfl

/-- Both within-set definitions recover the global definitions exactly on `univ`. -/
theorem exact_univ_recovery
    (connection : T → T [⋀^Fin 1]→L[ℝ] E)
    (form : T → T [⋀^Fin 2]→L[ℝ] E) :
    (groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G)
      connection Set.univ =
        groupLieAlgebraCoordinateCurvature (I := I) (G := G) connection) ∧
    (groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
      (I := I) (G := G) connection Set.univ form =
        groupLieAlgebraCoordinateCovariantExteriorDerivativeTwo
          (I := I) (G := G) connection form) :=
  ⟨groupLieAlgebraCoordinateCurvatureWithin_univ (I := I) (G := G) connection,
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin_univ
      (I := I) (G := G) connection form⟩

/-- The same-set Bianchi identity follows from the full explicit within-set hypotheses. -/
theorem exact_bianchiWithin
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) (x : T) {r : ℕ∞}
    (connection_regular : ContDiffWithinAt ℝ r connection s x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_s : UniqueDiffOn ℝ s)
    (mem_closure_interior : x ∈ closure (interior s))
    (mem_s : x ∈ s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
      (I := I) (G := G) connection s
      (groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G) connection s) x = 0 :=
  groupLieAlgebraCoordinate_bianchiWithin (I := I) (G := G)
    connection s x connection_regular regularity_order unique_s
    mem_closure_interior mem_s

/-- An unrelated curvature on the same set cannot replace the exact derived curvature. -/
theorem unrelated_curvatureWithin_blocked
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) (x : T)
    (other : T [⋀^Fin 2]→L[ℝ] E)
    (different : other ≠ extDerivWithin connection s x + (1 / 2 : ℝ) •
      (connection x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 1 (connection x))
    (claimed : groupLieAlgebraCoordinateCurvatureWithin
      (I := I) (G := G) connection s x = other) : False := by
  apply different
  rw [← claimed]
  rfl

/-- A nonzero same-set Bianchi expression contradicts the derived theorem. -/
theorem nonzero_bianchiWithin_blocked
    (connection : T → T [⋀^Fin 1]→L[ℝ] E) (s : Set T) (x : T) {r : ℕ∞}
    (connection_regular : ContDiffWithinAt ℝ r connection s x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_s : UniqueDiffOn ℝ s)
    (mem_closure_interior : x ∈ closure (interior s))
    (mem_s : x ∈ s)
    (claimed_nonzero :
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin
        (I := I) (G := G) connection s
        (groupLieAlgebraCoordinateCurvatureWithin (I := I) (G := G) connection s) x ≠ 0) :
    False :=
  claimed_nonzero
    (groupLieAlgebraCoordinate_bianchiWithin (I := I) (G := G)
      connection s x connection_regular regularity_order unique_s
      mem_closure_interior mem_s)

end YangMills.Mathematics.NormedCoordinateBianchiWithin.Probes
