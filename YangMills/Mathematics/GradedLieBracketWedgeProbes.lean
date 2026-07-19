/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.GradedLieBracketWedge

/-!
# Hostile probes for the graded Lie-bracket wedge

These probes lock every alternating-sum term and sign, degree-one compatibility, the three-term
one-with-two formula needed before Bianchi, genuine alternation, zero laws, and pointwise manifold
coherence.
-/

namespace YangMills.Mathematics.GradedLieBracketWedge.Probes

universe uE uH uM uT uV

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]

/-- Every omitted-slot term and alternating sign is retained exactly. -/
theorem exact_alternating_sum
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) :
    alpha.lieBracketWedgeOneMany n beta v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ⁅alpha (fun _ => v i), beta (i.removeNth v)⁆ :=
  ContinuousAlternatingMap.lieBracketWedgeOneMany_apply n alpha beta v

/-- The generalized construction cannot alter the previously fixed degree-one convention. -/
theorem exact_degree_one_coherence
    (alpha beta : T [⋀^Fin 1]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany 1 beta = alpha.lieBracketWedgeOne beta :=
  ContinuousAlternatingMap.lieBracketWedgeOneMany_one alpha beta

/-- The one-form/two-form bracket has exactly three omitted-slot terms. -/
theorem exact_degree_two_three_terms
    (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin 2]→L[ℝ] V)
    (v : Fin 3 → T) :
    alpha.lieBracketWedgeOneMany 2 beta v =
      (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) •
          ⁅alpha (fun _ => v 0), beta (Fin.removeNth 0 v)⁆ +
      (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) •
          ⁅alpha (fun _ => v 1), beta (Fin.removeNth 1 v)⁆ +
      (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) •
          ⁅alpha (fun _ => v 2), beta (Fin.removeNth 2 v)⁆ := by
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply, Fin.sum_univ_three]

/-- The exact cubic self-bracket cancels by Lie Jacobi with the fixed normalization. -/
theorem exact_cubic_jacobi_cancellation
    (alpha : T [⋀^Fin 1]→L[ℝ] V) :
    alpha.lieBracketWedgeOneMany 2 (alpha.lieBracketWedgeOne alpha) = 0 :=
  ContinuousAlternatingMap.lieBracketWedgeOneMany_self_self alpha

/-- A purported nonzero cubic self-bracket is rejected. -/
theorem nonzero_cubic_self_bracket_blocked
    (alpha : T [⋀^Fin 1]→L[ℝ] V)
    (hne : alpha.lieBracketWedgeOneMany 2 (alpha.lieBracketWedgeOne alpha) ≠ 0) : False :=
  hne (ContinuousAlternatingMap.lieBracketWedgeOneMany_self_self alpha)

/-- Omitting any demanded alternating-sum term or changing a sign is rejected. -/
theorem malformed_sum_blocked
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T)
    (mismatch : alpha.lieBracketWedgeOneMany n beta v ≠
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ⁅alpha (fun _ => v i), beta (i.removeNth v)⁆) : False :=
  mismatch (ContinuousAlternatingMap.lieBracketWedgeOneMany_apply n alpha beta v)

/-- The resulting `(n+1)`-form vanishes whenever two distinct slots coincide. -/
theorem nonalternating_output_blocked
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V)
    (v : Fin (n + 1) → T) (i j : Fin (n + 1))
    (hij : i ≠ j) (heq : v i = v j)
    (hne : alpha.lieBracketWedgeOneMany n beta v ≠ 0) : False :=
  hne ((alpha.lieBracketWedgeOneMany n beta).map_eq_zero_of_eq v heq hij)

/-- Additivity in both arguments is part of the exact graded bracket operation. -/
theorem exact_additivity
    (n : ℕ) (alpha₁ alpha₂ : T [⋀^Fin 1]→L[ℝ] V)
    (beta₁ beta₂ : T [⋀^Fin n]→L[ℝ] V) :
    (alpha₁ + alpha₂).lieBracketWedgeOneMany n beta₁ =
        alpha₁.lieBracketWedgeOneMany n beta₁ +
          alpha₂.lieBracketWedgeOneMany n beta₁ ∧
      alpha₁.lieBracketWedgeOneMany n (beta₁ + beta₂) =
        alpha₁.lieBracketWedgeOneMany n beta₁ +
          alpha₁.lieBracketWedgeOneMany n beta₂ := by
  simp

/-- Real scalar factors can be extracted from either exact argument. -/
theorem exact_real_scalarity
    [ContinuousSMul ℝ V]
    (n : ℕ) (r : ℝ) (alpha : T [⋀^Fin 1]→L[ℝ] V)
    (beta : T [⋀^Fin n]→L[ℝ] V) :
    (r • alpha).lieBracketWedgeOneMany n beta =
        r • alpha.lieBracketWedgeOneMany n beta ∧
      alpha.lieBracketWedgeOneMany n (r • beta) =
        r • alpha.lieBracketWedgeOneMany n beta := by
  simp

/-- Zero in either factor gives exactly the zero output, not a disconnected supplied form. -/
theorem exact_zero_laws
    (n : ℕ) (alpha : T [⋀^Fin 1]→L[ℝ] V) (beta : T [⋀^Fin n]→L[ℝ] V) :
    (0 : T [⋀^Fin 1]→L[ℝ] V).lieBracketWedgeOneMany n beta = 0 ∧
      alpha.lieBracketWedgeOneMany n 0 = 0 := by
  simp

/-- The manifold lift carries the cubic Jacobi cancellation pointwise. -/
theorem exact_manifold_cubic_jacobi_cancellation
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (alpha : ManifoldDifferentialForm I M V 1) :
    alpha.lieBracketWedgeOneMany 2 (alpha.lieBracketWedgeOne alpha) = 0 :=
  ManifoldDifferentialForm.lieBracketWedgeOneMany_self_self alpha

/-- The manifold lift uses both forms at the same exact base point. -/
theorem exact_manifold_pointwise_formula
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (n : ℕ) (alpha : ManifoldDifferentialForm I M V 1)
    (beta : ManifoldDifferentialForm I M V n) (x : M)
    (v : Fin (n + 1) → TangentSpace I x) :
    alpha.lieBracketWedgeOneMany n beta x v =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ⁅alpha x (fun _ => v i), beta x (i.removeNth v)⁆ :=
  ManifoldDifferentialForm.lieBracketWedgeOneMany_apply n alpha beta x v

end YangMills.Mathematics.GradedLieBracketWedge.Probes
