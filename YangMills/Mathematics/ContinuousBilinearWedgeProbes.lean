/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearWedge

/-!
# Hostile probes for the continuous bilinear wedge

The probes lock the omitted-slot sum, degree-one ordering, linearity in both arguments, and exact
coherence with the actual transported finite-dimensional group Lie bracket.
-/

namespace YangMills.Mathematics.ContinuousBilinearWedge.Probes

open scoped Manifold ContDiff

universe uT uV uE uH uG

variable
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The construction has exactly the intended signed omitted-slot sum. -/
theorem exact_alternating_sum
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) :
    alpha.continuousBilinearWedgeOneMany bilinear n beta v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        bilinear (alpha (fun _ => v i)) (beta (i.removeNth v)) :=
  ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply bilinear n alpha beta v

/-- Degree one retains the exact first-minus-second ordering. -/
theorem exact_degree_one_order
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T) :
    alpha.continuousBilinearWedgeOneMany bilinear 1 beta v =
      bilinear (alpha (fun _ => v 0)) (beta (fun _ => v 1)) -
        bilinear (alpha (fun _ => v 1)) (beta (fun _ => v 0)) :=
  ContinuousAlternatingMap.continuousBilinearWedgeOneMany_one_apply
    bilinear alpha beta v

/-- The one-form/two-form coordinate wedge has exactly three signed omitted-slot terms. -/
theorem exact_degree_two_three_terms
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin 2]→L[ℝ] V)
    (v : Fin 3 → T) :
    alpha.continuousBilinearWedgeOneMany bilinear 2 beta v =
      (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) •
          bilinear (alpha (fun _ => v 0)) (beta (Fin.removeNth 0 v)) +
      (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) •
          bilinear (alpha (fun _ => v 1)) (beta (Fin.removeNth 1 v)) +
      (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) •
          bilinear (alpha (fun _ => v 2)) (beta (Fin.removeNth 2 v)) := by
  rw [ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply,
    Fin.sum_univ_three]

/-- Additivity and real scalar multiplication are exact in the first argument. -/
theorem exact_first_argument_linearity
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ) (r : ℝ)
    (alpha₁ alpha₂ : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    ((alpha₁ + alpha₂).continuousBilinearWedgeOneMany bilinear n beta =
      alpha₁.continuousBilinearWedgeOneMany bilinear n beta +
        alpha₂.continuousBilinearWedgeOneMany bilinear n beta) ∧
    ((r • alpha₁).continuousBilinearWedgeOneMany bilinear n beta =
      r • alpha₁.continuousBilinearWedgeOneMany bilinear n beta) :=
  ⟨ContinuousAlternatingMap.add_continuousBilinearWedgeOneMany
      bilinear n alpha₁ alpha₂ beta,
    ContinuousAlternatingMap.smul_continuousBilinearWedgeOneMany
      bilinear n r alpha₁ beta⟩

/-- Additivity and real scalar multiplication are exact in the second argument. -/
theorem exact_second_argument_linearity
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ) (r : ℝ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta₁ beta₂ : T [⋀^Fin n]→L[ℝ] V) :
    (alpha.continuousBilinearWedgeOneMany bilinear n (beta₁ + beta₂) =
      alpha.continuousBilinearWedgeOneMany bilinear n beta₁ +
        alpha.continuousBilinearWedgeOneMany bilinear n beta₂) ∧
    (alpha.continuousBilinearWedgeOneMany bilinear n (r • beta₁) =
      r • alpha.continuousBilinearWedgeOneMany bilinear n beta₁) :=
  ⟨ContinuousAlternatingMap.continuousBilinearWedgeOneMany_add
      bilinear n alpha beta₁ beta₂,
    ContinuousAlternatingMap.continuousBilinearWedgeOneMany_smul
      bilinear n r alpha beta₁⟩

/-- A malformed omitted-slot expression is rejected. -/
theorem malformed_sum_blocked
    (bilinear : V →L[ℝ] V →L[ℝ] V) (n : ℕ)
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) (wrong : V)
    (different : wrong ≠ ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      bilinear (alpha (fun _ => v i)) (beta (i.removeNth v)))
    (claimed : alpha.continuousBilinearWedgeOneMany bilinear n beta v = wrong) : False := by
  apply different
  rw [← claimed]
  exact ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply
    bilinear n alpha beta v

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- The coordinate wedge uses the same canonical bracket as the intrinsic group Lie-algebra wedge. -/
theorem exact_group_coordinate_coherence
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] GroupLieAlgebra I G)
    (beta : T [⋀^Fin n]→L[ℝ] GroupLieAlgebra I G) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let coordinates := groupLieAlgebraModelEquiv (G := G) I
    coordinates.toContinuousLinearMap.compContinuousAlternatingMap
        (alpha.lieBracketWedgeOneMany n beta) =
      ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) n
        (coordinates.toContinuousLinearMap.compContinuousAlternatingMap alpha)
        (coordinates.toContinuousLinearMap.compContinuousAlternatingMap beta) :=
  groupLieAlgebraCoordinateBracket_wedge_coherence n alpha beta

/-- Any claimed failure of exact intrinsic/coordinate coherence is contradictory. -/
theorem coordinate_coherence_mismatch_blocked
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] GroupLieAlgebra I G)
    (beta : T [⋀^Fin n]→L[ℝ] GroupLieAlgebra I G)
    (mismatch :
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      let coordinates := groupLieAlgebraModelEquiv (G := G) I
      coordinates.toContinuousLinearMap.compContinuousAlternatingMap
          (alpha.lieBracketWedgeOneMany n beta) ≠
        ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) n
          (coordinates.toContinuousLinearMap.compContinuousAlternatingMap alpha)
          (coordinates.toContinuousLinearMap.compContinuousAlternatingMap beta)) : False :=
  mismatch (groupLieAlgebraCoordinateBracket_wedge_coherence n alpha beta)

end YangMills.Mathematics.ContinuousBilinearWedge.Probes
