/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorAlternation

/-!
# Hostile probes for self-wedge exterior alternation

The probes lock tuple recovery, the minus-two normalization, the canonical group-coordinate bracket,
and rejection of any conflicting alternation value. They do not identify the raw alternation with
`extDeriv` of the whole self-wedge function.
-/

namespace YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorAlternation.Probes

open scoped Manifold ContDiff

universe uT uV uE uH uG

variable
    {T : Type uT} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An arbitrary `Fin 2` tuple receives the exact four-term coefficient derivative. -/
theorem exact_tuple_derivative
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x direction : T) (pair : Fin 2 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    fderiv ℝ
      (fun y => (form y).continuousBilinearWedgeOneMany bilinear 1 (form y) pair)
      x direction =
      (bilinear (form x (fun _ => pair 0))
          (formDerivative direction (fun _ => pair 1)) +
        bilinear (formDerivative direction (fun _ => pair 0))
          (form x (fun _ => pair 1))) -
      (bilinear (form x (fun _ => pair 1))
          (formDerivative direction (fun _ => pair 0)) +
        bilinear (formDerivative direction (fun _ => pair 1))
          (form x (fun _ => pair 0))) :=
  ContinuousAlternatingMap.continuousBilinearSelfWedgeOne_fderiv_tuple
    bilinear form formDerivative x direction pair form_hasDerivative

/-- The exact skew-bilinear exterior alternation has coefficient `-2`. -/
theorem exact_neg_two_alternation
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x : T) (vectors : Fin 3 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    continuousBilinearSelfWedgeExteriorAlternationAt bilinear form x vectors =
      (-2 : ℝ) •
        (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x) vectors :=
  continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two
    bilinear skew form formDerivative x vectors form_hasDerivative

/-- Any conflicting sign, factor, or term arrangement is rejected when it differs from the exact
minus-two expression. -/
theorem malformed_alternation_blocked
    (bilinear : V →L[ℝ] V →L[ℝ] V)
    (skew : ∀ first second, bilinear first second = -bilinear second first)
    (form : T → T [⋀^Fin 1]→L[ℝ] V)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] V))
    (x : T) (vectors : Fin 3 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x)
    (wrong : V)
    (different : wrong ≠ (-2 : ℝ) •
      (form x).continuousBilinearWedgeOneMany bilinear 2 (extDeriv form x) vectors)
    (claimed : continuousBilinearSelfWedgeExteriorAlternationAt
      bilinear form x vectors = wrong) : False := by
  apply different
  exact claimed.symm.trans
    (continuousBilinearSelfWedgeExteriorAlternationAt_eq_neg_two
      bilinear skew form formDerivative x vectors form_hasDerivative)

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I (minSmoothness ℝ 3) G]

/-- The exact canonical group-coordinate bracket is skew. -/
theorem exact_group_coordinate_skew (first second : E) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) first second =
      -groupLieAlgebraCoordinateBracketCLM (I := I) (G := G) second first :=
  groupLieAlgebraCoordinateBracketCLM_skew (I := I) (G := G) first second

/-- The canonical group-coordinate alternation uses the same exact minus-two normalization. -/
theorem exact_group_coordinate_alternation
    (form : T → T [⋀^Fin 1]→L[ℝ] E)
    (formDerivative : T →L[ℝ] (T [⋀^Fin 1]→L[ℝ] E))
    (x : T) (vectors : Fin 3 → T)
    (form_hasDerivative : HasFDerivAt form formDerivative x) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    continuousBilinearSelfWedgeExteriorAlternationAt
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) form x vectors =
      (-2 : ℝ) • (form x).continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := I) (G := G)) 2
        (extDeriv form x) vectors :=
  groupLieAlgebraCoordinateSelfWedgeExteriorAlternationAt_eq_neg_two
    (I := I) (G := G) form formDerivative x vectors form_hasDerivative

end YangMills.Mathematics.ContinuousBilinearSelfWedgeExteriorAlternation.Probes
