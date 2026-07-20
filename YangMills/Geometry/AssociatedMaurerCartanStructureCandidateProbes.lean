/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AssociatedMaurerCartanStructureCandidate

/-!
# Hostile probes for the Maurer--Cartan structure candidate
-/

namespace YangMills.Geometry.AssociatedMaurerCartanStructureCandidate.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)]

omit [IsTopologicalGroup G] [FiniteDimensional ℝ EG] in
/-- Left trivialization returns the generator of a left-invariant field. -/
theorem exact_invariant_generator
    (g : G) (v : GroupLieAlgebra IG G) :
    leftMaurerCartanApply g (mulInvariantVectorField v g) = v :=
  leftMaurerCartanApply_mulInvariantVectorField g v

omit [IsTopologicalGroup G] in
/-- The universal Cartan expression has the exact negative-bracket sign. -/
theorem exact_invariant_cartan
    (g : G) (v w : GroupLieAlgebra IG G) :
    (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) Set.univ g
        (mulInvariantVectorField v) (mulInvariantVectorField w) =
      -(groupLieAlgebraModelEquiv IG) ⁅v, w⁆ :=
  leftMaurerCartanForm_cartan_invariant g v w

omit [IsTopologicalGroup G] in
/-- The `-1/2` candidate matches the Cartan expression on invariant fields. -/
theorem exact_candidate_invariant_cartan
    (g : G) (v w : GroupLieAlgebra IG G) :
    (groupLieAlgebraModelEquiv IG)
        (((-1 / 2 : ℝ) •
          ManifoldDifferentialForm.lieBracketWedgeOneMany
            (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
            (leftMaurerCartanForm (IG := IG) (G := G))
            (leftMaurerCartanForm (IG := IG) (G := G))) g
          (ManifoldDifferentialForm.twoVectorArguments
            (mulInvariantVectorField v) (mulInvariantVectorField w) g)) =
      (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) Set.univ g
        (mulInvariantVectorField v) (mulInvariantVectorField w) :=
  leftMaurerCartan_candidate_cartan_invariant g v w

omit [FiniteDimensional ℝ EG] [CompleteSpace EG]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The associated gauge form is the exact pullback of the universal form. -/
theorem exact_associated_pullback
    (gauge : SmoothGaugeTransformation smoothBundle) :
    gauge.associatedMaurerCartanPullback =
      ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (leftMaurerCartanForm (IG := IG) (G := G)) :=
  associated_eq_pullback gauge

/-- The associated self-wedge has exactly the factor-two project normalization. -/
theorem exact_associated_selfWedge
    (gauge : SmoothGaugeTransformation smoothBundle)
    (p : P) (v : Fin 2 → TangentSpace IP p) :
    ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback
        gauge.associatedMaurerCartanPullback p v =
      (2 : ℝ) • ⁅gauge.associatedMaurerCartanPullback.evalOne p (v 0),
        gauge.associatedMaurerCartanPullback.evalOne p (v 1)⁆ :=
  associated_selfWedge_apply gauge p v

/-- The smooth derivative candidate has exactly the required same-form carrier. -/
theorem exact_candidate_carrier
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm =
      (-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback
        gauge.associatedMaurerCartanPullback :=
  associatedMaurerCartanDerivativeCandidate_toForm gauge

/-- The candidate cancels the normalized self-wedge as an exact carrier equality. -/
theorem exact_candidate_cancellation
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm + (1 / 2 : ℝ) •
      ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback
        gauge.associatedMaurerCartanPullback = 0 :=
  associatedMaurerCartanDerivativeCandidate_add_half_selfWedge gauge

omit [IsTopologicalGroup G] in
/-- Reversing the checked invariant-field Cartan sign is inconsistent when asserted as inequality
from the exact negative-bracket expression. -/
theorem wrong_invariant_cartan_sign_blocked
    (g : G) (v w : GroupLieAlgebra IG G)
    (wrong :
      (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
          (groupLieAlgebraModelEquiv IG) Set.univ g
          (mulInvariantVectorField v) (mulInvariantVectorField w) ≠
        -(groupLieAlgebraModelEquiv IG) ⁅v, w⁆) : False :=
  wrong (leftMaurerCartanForm_cartan_invariant g v w)

/-- An unrelated candidate carrier is rejected. -/
theorem mismatched_candidate_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong :
      (associatedMaurerCartanDerivativeCandidate gauge).toForm ≠
        (-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
          gauge.associatedMaurerCartanPullback
          gauge.associatedMaurerCartanPullback) : False :=
  wrong (associatedMaurerCartanDerivativeCandidate_toForm gauge)

end

end YangMills.Geometry.AssociatedMaurerCartanStructureCandidate.Probes
