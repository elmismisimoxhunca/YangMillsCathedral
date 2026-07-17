/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTransition

/-!
# Hostile probes for adjoint-bundle transition maps
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)
    (first second : PrincipalBundleLocalTrivialization torsor)

omit [IsTopologicalGroup G] [LieGroup I ∞ G] in
/-- The associated overlap source cannot differ from the intersection of base chart domains times
the whole fiber. -/
theorem malformed_adjointBundle_overlapDomain_blocked
    (mismatch : adjointBundleOverlapDomain (I := I) first second ≠
      (first.baseSet ∩ second.baseSet) ×ˢ
        (Set.univ : Set (GroupLieAlgebra I G))) : False :=
  mismatch (adjointBundleOverlapDomain_eq (I := I) first second)

/-- An associated overlap transition cannot move the base coordinate. -/
theorem baseMoving_adjointBundle_transition_blocked
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second)
    (mismatch : (adjointBundleTransition (I := I) bundle first second z).1 ≠ z.1) : False :=
  mismatch (adjointBundleTransition_fst (I := I) bundle first second z hz)

/-- The fiber operator is tied to the actual principal transition coordinate. -/
theorem disconnected_adjointBundle_transition_operator_blocked
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second)
    (mismatch : adjointBundleTransition (I := I) bundle first second z ≠
      (z.1, YangMills.Mathematics.lieGroupAdjoint I
        (principalBundleTransition first second (z.1, (1 : G))).2 z.2)) : False :=
  mismatch (adjointBundleTransition_eq (I := I) bundle first second z hz)

/-- Reversing the ordered transition cannot fail to recover the original coordinate. -/
theorem broken_adjointBundle_reverse_transition_blocked
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second)
    (mismatch : adjointBundleTransition (I := I) bundle second first
      (adjointBundleTransition (I := I) bundle first second z) ≠ z) : False :=
  mismatch (adjointBundleTransition_reverse (I := I) bundle first second z hz)

/-- The transition cannot translate the zero fiber vector. -/
theorem nonzero_adjointBundle_zero_transition_blocked
    (b : B)
    (hb : (b, (0 : GroupLieAlgebra I G)) ∈
      adjointBundleOverlapDomain (I := I) first second)
    (mismatch : adjointBundleTransition (I := I) bundle first second (b, 0) ≠ (b, 0)) :
    False :=
  mismatch (adjointBundleTransition_zero (I := I) bundle first second b hb)

/-- A nonlinear additive mutation is rejected by the derived transition. -/
theorem nonadditive_adjointBundle_transition_blocked
    (b : B) (X Y : GroupLieAlgebra I G)
    (hX : (b, X) ∈ adjointBundleOverlapDomain (I := I) first second)
    (mismatch :
      (adjointBundleTransition (I := I) bundle first second (b, X + Y)).2 ≠
        (adjointBundleTransition (I := I) bundle first second (b, X)).2 +
          (adjointBundleTransition (I := I) bundle first second (b, Y)).2) : False :=
  mismatch (adjointBundleTransition_snd_add (I := I) bundle first second b X Y hX)

/-- A nonlinear scalar mutation is rejected by the derived transition. -/
theorem nonscalar_adjointBundle_transition_blocked
    (b : B) (c : ℝ) (X : GroupLieAlgebra I G)
    (hX : (b, X) ∈ adjointBundleOverlapDomain (I := I) first second)
    (mismatch :
      (adjointBundleTransition (I := I) bundle first second (b, c • X)).2 ≠
        c • (adjointBundleTransition (I := I) bundle first second (b, X)).2) : False :=
  mismatch (adjointBundleTransition_snd_smul (I := I) bundle first second b c X hX)

end

end YangMills.Geometry.Probes
