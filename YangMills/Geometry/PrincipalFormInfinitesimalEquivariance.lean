/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFundamentalVectorField
import YangMills.Geometry.PrincipalFormCovariantExteriorVertical
import YangMills.Mathematics.LieGroupInfinitesimalAdjoint

/-!
# Infinitesimal right-equivariance of principal forms

For omitted tangent fields transported exactly by principal right translations along one orbit,
right-adjoint equivariance and the proved infinitesimal inverse-adjoint formula determine the
coefficient derivative in a fundamental direction. Horizontality kills every nondistinguished
coefficient containing the globally fundamental field. The resulting arbitrary-degree Cartan
reduction retains only an explicit triangular bracket-term cancellation premise; constructing
chart-local orbit-adapted fields that derive that premise remains separate geometry debt.
-/

namespace YangMills.Geometry

open Set
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

namespace PrincipalForm

/-- The distinguished coefficient in Cartan's formula has the exact infinitesimal
inverse-adjoint derivative when the omitted fields are right-translation adapted along the orbit. -/
theorem distinguishedCoefficient_mfderiv_fundamental
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP Set.univ (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p)) :
    let Y := form.toForm p (fun i => (r.removeNth fields) i p)
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv IG Y)
      (mfderiv IP (modelWithCornersSelf ℝ EG)
        (fun q => groupLieAlgebraModelEquiv IG
          (form.toForm q (fun i => (r.removeNth fields) i q))) p
        (principalFundamentalVector smoothBundle p X))) =
      -groupLieAlgebraModelEquiv IG ⁅X, Y⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  dsimp only
  let coefficient : P → EG := fun q => groupLieAlgebraModelEquiv IG
    (form.toForm q (fun i => (r.removeNth fields) i q))
  let orbit : G → P := principalOrbitMap torsor p
  have omitted_smooth : ∀ i : Fin (n + 1),
      ManifoldTangentField.IsSmoothOn IP Set.univ ((r.removeNth fields) i) := by
    intro i
    exact fields_smooth (r.succAbove i)
  have coefficient_smooth : ContMDiff IP (modelWithCornersSelf ℝ EG) ∞ coefficient := by
    exact contMDiffOn_univ.mp
      (form.eval_smooth Set.univ (r.removeNth fields) omitted_smooth)
  have orbit_smooth : ContMDiff IG IP ∞ orbit :=
    principalOrbitMap_smooth smoothBundle p
  have chain := mfderiv_comp (I := IG) (I' := IP)
    (I'' := modelWithCornersSelf ℝ EG)
    (f := orbit) (g := coefficient) (1 : G)
    (coefficient_smooth.mdifferentiableAt (by simp))
    (orbit_smooth.mdifferentiableAt (by simp))
  have orbit_one : orbit 1 = p := torsor.right_one p
  have orbit_derivative : mfderiv IG IP orbit 1 X =
      principalFundamentalVector smoothBundle p X := rfl
  have coefficient_orbit : coefficient ∘ orbit =
      fun g => groupLieAlgebraModelEquiv IG
        (inverseAdjointOrbit IG
          (form.toForm p (fun i => (r.removeNth fields) i p)) g) := by
    funext g
    change groupLieAlgebraModelEquiv IG
        (form.toForm (torsor.rightAction p g)
          (fun i => (r.removeNth fields) i (torsor.rightAction p g))) = _
    calc
      _ = groupLieAlgebraModelEquiv IG
          (form.toForm (torsor.rightAction p g)
            (fun i => principalRightTranslationDifferential smoothBundle p g
              ((r.removeNth fields) i p))) := by
        congr 2
        funext i
        exact adapted g i
      _ = groupLieAlgebraModelEquiv IG
          (lieGroupAdjoint IG g⁻¹
            (form.toForm p (fun i => (r.removeNth fields) i p))) := by
        exact congrArg (groupLieAlgebraModelEquiv IG)
          (equivariant g p (fun i => (r.removeNth fields) i p))
      _ = _ := rfl
  have chain_apply := congrArg (fun L => L X) chain
  rw [coefficient_orbit, orbit_one] at chain_apply
  change mfderiv IG (modelWithCornersSelf ℝ EG)
      (fun g => groupLieAlgebraModelEquiv IG
        (inverseAdjointOrbit IG
          (form.toForm p (fun i => (r.removeNth fields) i p)) g)) 1 X =
    mfderiv IP (modelWithCornersSelf ℝ EG) coefficient p
      (mfderiv IG IP orbit 1 X) at chain_apply
  rw [orbit_derivative] at chain_apply
  rw [← chain_apply]
  exact mfderiv_inverseAdjointOrbit_identity IG X
    (form.toForm p (fun i => (r.removeNth fields) i p))

omit [FiniteDimensional ℝ EG] in
/-- Horizontality and a globally fundamental distinguished field make every other Cartan
coefficient identically zero, hence its directional derivative vanishes. -/
theorem otherCoefficient_mfderiv_zero_of_fundamentalField
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (p : P) (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamental_field : ∀ q,
      fields r q = principalFundamentalVectorField (smoothBundle := smoothBundle) X q)
    (i : Fin (n + 2)) (hir : i ≠ r) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv IG
        (form.toForm p (i.removeNth (fun k => fields k p))))
      (mfderiv IP (modelWithCornersSelf ℝ EG)
        (fun q => groupLieAlgebraModelEquiv IG
          (form.toForm q (i.removeNth (fun k => fields k q)))) p (fields i p))) = 0 := by
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hir.symm
  have form_zero (q : P) :
      form.toForm q (i.removeNth (fun k => fields k q)) = 0 := by
    apply horizontal q
    refine ⟨z, ?_⟩
    rw [Fin.removeNth_apply, hz, fundamental_field q]
    exact principalFundamentalVectorField_projection_eq_zero X q
  have coefficient_zero :
      (fun q => groupLieAlgebraModelEquiv IG
        (form.toForm q (i.removeNth (fun k => fields k q)))) =
      (fun _ : P => (0 : EG)) := by
    funext q
    rw [form_zero q, map_zero]
  rw [coefficient_zero, mfderiv_const]
  rfl

/-- Maximal compiled Cartan reduction currently available. Besides orbit adaptation, it retains
only the triangular bracket-evaluation cancellation obligation; horizontality now derives every
nondistinguished coefficient cancellation. -/
theorem exteriorDerivative_apply_fundamental_of_adaptedFields
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP Set.univ (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamental_field : ∀ q,
      fields r q = principalFundamentalVectorField (smoothBundle := smoothBundle) X q)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p))
    (bracketTerm_zero : ∀ (i j : Fin (n + 1)), j ∈ Finset.Ici i →
      groupLieAlgebraModelEquiv IG
        (form.toForm p (Matrix.vecCons
          (VectorField.mlieBracketWithin IP
            (fields i.castSucc) (fields j.succ) Set.univ p)
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0) :
    exterior.derivative.toForm p (fun i => fields i p) =
      -((-1 : ℤ) ^ (r : ℕ) •
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have distinguished := distinguishedCoefficient_mfderiv_fundamental
    (smoothBundle := smoothBundle) n form equivariant p fields fields_smooth r X adapted
  have cartan := exterior.cartan_formula Set.univ p isOpen_univ (Set.mem_univ p)
    uniqueMDiffOn_univ fields fields_smooth
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates at cartan
  simp only [mfderivWithin_univ] at cartan
  have first_sum :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (NormedSpace.fromTangentSpace
          (groupLieAlgebraModelEquiv IG
            (form.toForm p (i.removeNth (fun k => fields k p))))
          (mfderiv IP (modelWithCornersSelf ℝ EG)
            (fun q => groupLieAlgebraModelEquiv IG
              (form.toForm q (i.removeNth (fun k => fields k q)))) p (fields i p)))) =
        (-1 : ℤ) ^ (r : ℕ) •
          (-groupLieAlgebraModelEquiv IG
            ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) := by
    rw [Finset.sum_eq_single r]
    · rw [fundamental_field p]
      exact congrArg (fun z : EG => (-1 : ℤ) ^ (r : ℕ) • z) distinguished
    · intro i hi hir
      rw [otherCoefficient_mfderiv_zero_of_fundamentalField
        (smoothBundle := smoothBundle) n form horizontal p fields r X fundamental_field i hir,
        smul_zero]
    · simp
  have bracket_summand_zero (i j : Fin (n + 1)) (hj : j ∈ Finset.Ici i) :
      (-1 : ℤ) ^ (i + j : ℕ) •
        groupLieAlgebraModelEquiv IG
          (form.toForm p (Matrix.vecCons
            (VectorField.mlieBracketWithin IP
              (fields i.castSucc) (fields j.succ) Set.univ p)
            (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0 := by
    rw [bracketTerm_zero i j hj, smul_zero]
  have second_sum :
      (∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ (i + j : ℕ) •
        groupLieAlgebraModelEquiv IG
          (form.toForm p (Matrix.vecCons
            (VectorField.mlieBracketWithin IP
              (fields i.castSucc) (fields j.succ) Set.univ p)
            (j.removeNth <| i.castSucc.removeNth (fun k => fields k p))))) = (0 : EG) := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact bracket_summand_zero i j hj
  rw [first_sum, second_sum, sub_zero] at cartan
  apply (groupLieAlgebraModelEquiv IG).injective
  rw [cartan]
  simp only [map_neg, map_zsmul]
  module

end PrincipalForm
end
end YangMills.Geometry
