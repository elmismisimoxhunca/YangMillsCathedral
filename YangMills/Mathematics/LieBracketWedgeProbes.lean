/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieBracketWedge

/-!
# Hostile probes for the continuous Lie-bracket wedge

These probes enforce joint bracket continuity, antisymmetrization order, degree, alternation, and
the factor-two self-wedge normalization used in the curvature convention.
-/

namespace YangMills.Mathematics.Probes

universe uE uH uM uT uV

variable
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousLieBracket V]
    {T : Type uT} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]

omit [LieAlgebra ℝ V] [IsTopologicalAddGroup V] in
/-- A discontinuous bracket cannot pass the topological Lie-algebra interface. -/
theorem discontinuous_lieBracket_blocked
    (discontinuous : ¬Continuous fun pair : V × V => ⁅pair.1, pair.2⁆) : False :=
  discontinuous ContinuousLieBracket.continuous_bracket

omit [IsTopologicalAddGroup V] [ContinuousLieBracket V] in
/-- The one-form/linear-map bridge evaluates the exact same single input. -/
theorem oneFormLinear_coherent
    (form : T [⋀^Fin 1]→L[ℝ] V) (v : T) :
    form.oneFormLinear v = form (fun _ => v) :=
  rfl

/-- The two bracket terms and their order are fixed by the wedge definition. -/
theorem malformed_lieBracketWedge_blocked
    (first second : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T)
    (mismatch : first.lieBracketWedgeOne second v ≠
      ⁅first (fun _ => v 0), second (fun _ => v 1)⁆ -
        ⁅first (fun _ => v 1), second (fun _ => v 0)⁆) : False :=
  mismatch (ContinuousAlternatingMap.lieBracketWedgeOne_apply first second v)

/-- The self bracket-wedge carries the factor two paired with curvature's factor one-half. -/
theorem wrong_self_lieBracketWedge_normalization_blocked
    (form : T [⋀^Fin 1]→L[ℝ] V) (v : Fin 2 → T)
    (mismatch : form.lieBracketWedgeOne form v ≠
      (2 : ℝ) • ⁅form (fun _ => v 0), form (fun _ => v 1)⁆) : False :=
  mismatch (ContinuousAlternatingMap.lieBracketWedgeOne_self_apply form v)

/-- The constructed bracket-wedge is genuinely alternating. -/
theorem nonalternating_lieBracketWedge_blocked
    (first second : T [⋀^Fin 1]→L[ℝ] V) (v : T)
    (nonzero : first.lieBracketWedgeOne second (fun _ => v) ≠ 0) : False :=
  nonzero ((first.lieBracketWedgeOne second).map_eq_zero_of_eq
    (fun _ => v) (i := 0) (j := 1) rfl (by decide))

/-- The manifold lift must use both one-forms at the same declared base point. -/
theorem malformed_manifold_lieBracketWedge_blocked
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]
    [ContinuousSMul ℝ V]
    (first second : ManifoldDifferentialForm I M V 1) (x : M)
    (v : Fin 2 → TangentSpace I x)
    (mismatch : first.lieBracketWedgeOne second x v ≠
      ⁅first x (fun _ => v 0), second x (fun _ => v 1)⁆ -
        ⁅first x (fun _ => v 1), second x (fun _ => v 0)⁆) : False :=
  mismatch (ManifoldDifferentialForm.lieBracketWedgeOne_apply first second x v)

/-- Zero one-forms give a concrete zero bracket-wedge in every compatible topological Lie algebra. -/
theorem zero_lieBracketWedge_eq_zero :
    (0 : T [⋀^Fin 1]→L[ℝ] V).lieBracketWedgeOne 0 = 0 := by
  ext v
  simp

end YangMills.Mathematics.Probes
