/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormCovariantExteriorCandidate
import YangMills.Mathematics.LieBracketWedgeHorizontalVertical

/-!
# Vertical-slot formulas for the principal covariant-exterior candidate

The exact bracket correction is calculated on arbitrary vertical slots and fundamental vertical
vectors. It generally does not vanish with one vertical slot, but has the precise signed term that
must cancel the ordinary exterior derivative. A conditional algebraic theorem isolates this
remaining infinitesimal-geometric obligation without accepting it as candidate data.
-/

namespace YangMills.Geometry

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG]

omit [FiniteDimensional ℝ EG] in
/-- Fundamental vectors lie in the kernel of the bundle-projection differential. -/
theorem principalFundamentalVector_projection_eq_zero
    (p : P) (X : GroupLieAlgebra IG G) :
    mfderiv IP IB torsor.projection p (principalFundamentalVector smoothBundle p X) = 0 := by
  have orbitDifferentiable :=
    (principalOrbitMap_smooth smoothBundle p).mdifferentiableAt (x := (1 : G)) (by simp)
  have projectionDifferentiable :=
    smoothBundle.projection_smooth.mdifferentiableAt
      (x := principalOrbitMap torsor p 1) (by simp)
  have hchain := mfderiv_comp (I := IG) (I' := IP) (I'' := IB)
    (f := principalOrbitMap torsor p) (g := torsor.projection) 1
    projectionDifferentiable orbitDifferentiable
  have hfun : torsor.projection ∘ principalOrbitMap torsor p =
      fun _ : G => torsor.projection p := by
    funext g
    exact torsor.projection_rightAction p g
  rw [mfderiv_congr (I := IG) (I' := IB) (x := (1 : G)) hfun,
    mfderiv_const] at hchain
  rw [show principalOrbitMap torsor p 1 = p by exact torsor.right_one p] at hchain
  change mfderiv IP IB torsor.projection p
      (mfderiv IG IP (principalOrbitMap torsor p) 1 X) = 0
  exact congrArg (fun L => L X) hchain.symm

namespace PrincipalForm

/-- Exact bracket-correction value on a tuple with an arbitrary vertical vector in slot `r`.
The connection value of that vertical vector is retained explicitly. -/
theorem covariantExteriorBracket_apply_verticalSlot
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2))
    (vertical : mfderiv IP IB torsor.projection p (vectors r) = 0) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorBracket connection n form).toForm p vectors =
      (-1 : ℤ) ^ (r : ℕ) •
        ⁅connection.pointwise.form.evalOne p (vectors r),
          form.toForm p (r.removeNth vectors)⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [covariantExteriorBracket_toForm]
  change (connection.pointwise.form p).lieBracketWedgeOneMany (n + 1)
    (form.toForm p) vectors = _
  exact ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
    (n + 1) (connection.pointwise.form p) (form.toForm p)
    (mfderiv IP IB torsor.projection p).toLinearMap (horizontal p) vectors r vertical

/-- The bracket correction vanishes if two distinct slots are vertical. -/
theorem covariantExteriorBracket_apply_twoVerticalSlots
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r s : Fin (n + 2)) (hrs : r ≠ s)
    (vertical_r : mfderiv IP IB torsor.projection p (vectors r) = 0)
    (vertical_s : mfderiv IP IB torsor.projection p (vectors s) = 0) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorBracket connection n form).toForm p vectors = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [covariantExteriorBracket_toForm]
  change (connection.pointwise.form p).lieBracketWedgeOneMany (n + 1)
    (form.toForm p) vectors = 0
  exact ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_twoVerticalSlots
    (n + 1) (connection.pointwise.form p) (form.toForm p)
    (mfderiv IP IB torsor.projection p).toLinearMap (horizontal p) vectors r s hrs
      vertical_r vertical_s

/-- Exact bracket-correction value on a tuple with a fundamental vertical vector in slot `r`.
All other omitted-slot summands vanish by horizontality of `form`. -/
theorem covariantExteriorBracket_apply_fundamentalSlot
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorBracket connection n form).toForm p vectors =
      (-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [covariantExteriorBracket_toForm]
  change (connection.pointwise.form p).lieBracketWedgeOneMany (n + 1)
    (form.toForm p) vectors = _
  rw [ContinuousAlternatingMap.lieBracketWedgeOneMany_apply_of_horizontal_verticalSlot
      (n + 1) (connection.pointwise.form p) (form.toForm p)
      (projection := (mfderiv IP IB torsor.projection p).toLinearMap)
      (horizontal := horizontal p)
      (vertical := by
        rw [fundamentalSlot]
        exact principalFundamentalVector_projection_eq_zero p X)]
  change (-1 : ℤ) ^ (r : ℕ) •
      ⁅connection.pointwise.form.evalOne p (vectors r),
        form.toForm p (r.removeNth vectors)⁆ = _
  rw [fundamentalSlot, connection.vertical_normalization]


/-- On a tuple with a fundamental vertical slot, the full candidate is the ordinary derivative plus
exactly the signed infinitesimal adjoint correction. -/
theorem covariantExteriorCandidate_apply_fundamentalSlot
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorCandidate connection n form exterior).toForm p vectors =
      exterior.derivative.toForm p vectors +
        (-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [covariantExteriorCandidate_apply]
  change exterior.derivative.toForm p vectors +
    (covariantExteriorBracket connection n form).toForm p vectors = _
  rw [covariantExteriorBracket_apply_fundamentalSlot connection n form horizontal p vectors r X
    fundamentalSlot]

/-- Maximal algebraic horizontality theorem. Once the ordinary derivative is known to
have the exact negative vertical-slot value, the full same-connection candidate is horizontal.
This isolates the remaining geometric/infinitesimal calculus obligation from the finite-sum proof. -/
theorem covariantExteriorCandidate_isHorizontal_of_derivative_vertical
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (derivative_vertical : ∀ (p : P)
      (vectors : Fin (n + 2) → TangentSpace IP p) (r : Fin (n + 2)),
      mfderiv IP IB torsor.projection p (vectors r) = 0 →
      exterior.derivative.toForm p vectors =
        -((-1 : ℤ) ^ (r : ℕ) •
          ⁅connection.pointwise.form.evalOne p (vectors r),
            form.toForm p (r.removeNth vectors)⁆)) :
    IsHorizontal smoothBundle
      (covariantExteriorCandidate connection n form exterior).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  intro p vectors vertical
  obtain ⟨r, vertical_r⟩ := vertical
  rw [covariantExteriorCandidate_apply]
  change exterior.derivative.toForm p vectors +
    (covariantExteriorBracket connection n form).toForm p vectors = 0
  rw [covariantExteriorBracket_apply_verticalSlot connection n form horizontal p vectors r
    vertical_r, derivative_vertical p vectors r vertical_r, neg_add_cancel]

/-- The exact cancellation criterion: if the ordinary derivative on a fundamental vertical slot is
the negative infinitesimal adjoint term (as supplied by infinitesimal right-equivariance/Cartan
calculus), then `dω + [Θ ∧ ω]` vanishes on that tuple. -/
theorem covariantExteriorCandidate_apply_fundamentalSlot_eq_zero
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X)
    (derivative_vertical : exterior.derivative.toForm p vectors =
      -((-1 : ℤ) ^ (r : ℕ) • ⁅X, form.toForm p (r.removeNth vectors)⁆)) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    (covariantExteriorCandidate connection n form exterior).toForm p vectors = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [covariantExteriorCandidate_apply_fundamentalSlot connection n form exterior horizontal p
    vectors r X fundamentalSlot, derivative_vertical, neg_add_cancel]

end PrincipalForm

end

end YangMills.Geometry
