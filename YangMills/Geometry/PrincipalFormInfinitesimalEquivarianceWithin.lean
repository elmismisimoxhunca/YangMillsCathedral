/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormInfinitesimalEquivariance

/-!
# Local infinitesimal right-equivariance of principal forms

The distinguished, nondistinguished, and final Cartan reductions are localized to an arbitrary open
calculus set containing the evaluation point. Orbit adaptation remains quantified over the whole
structure group, which matches full-fiber principal trivialization domains. The termwise triangular
bracket-evaluation premise remains explicit.
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

/-- Localized distinguished-coefficient calculation. The fields need only be smooth on the open
calculus set, while orbit adaptation is retained for every group element. -/
theorem distinguishedCoefficient_mfderivWithin_fundamental
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (s : Set P) (p : P) (open_s : IsOpen s) (hp : p ∈ s)
    (_unique_s : UniqueMDiffOn IP s)
    (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP s (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p)) :
    let Y := form.toForm p (fun i => (r.removeNth fields) i p)
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv IG Y)
      (mfderivWithin IP (modelWithCornersSelf ℝ EG)
        (fun q => groupLieAlgebraModelEquiv IG
          (form.toForm q (fun i => (r.removeNth fields) i q))) s p
        (principalFundamentalVector smoothBundle p X))) =
      -groupLieAlgebraModelEquiv IG ⁅X, Y⁆ := by
  rw [mfderivWithin_of_isOpen open_s hp]
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  dsimp only
  let coefficient : P → EG := fun q => groupLieAlgebraModelEquiv IG
    (form.toForm q (fun i => (r.removeNth fields) i q))
  let orbit : G → P := principalOrbitMap torsor p
  have omitted_smooth : ∀ i : Fin (n + 1),
      ManifoldTangentField.IsSmoothOn IP s ((r.removeNth fields) i) := by
    intro i
    exact fields_smooth (r.succAbove i)
  have coefficient_smooth : ContMDiffAt IP (modelWithCornersSelf ℝ EG) ∞ coefficient p := by
    exact ((form.eval_smooth s (r.removeNth fields) omitted_smooth) p hp).contMDiffAt
      (open_s.mem_nhds hp)
  have orbit_smooth : ContMDiff IG IP ∞ orbit :=
    principalOrbitMap_smooth smoothBundle p
  have orbit_one : orbit 1 = p := torsor.right_one p
  have coefficient_smooth_orbit_one :
      ContMDiffAt IP (modelWithCornersSelf ℝ EG) ∞ coefficient (orbit 1) := by
    rw [orbit_one]
    exact coefficient_smooth
  have chain := mfderiv_comp (I := IG) (I' := IP)
    (I'' := modelWithCornersSelf ℝ EG)
    (f := orbit) (g := coefficient) (1 : G)
    (coefficient_smooth_orbit_one.mdifferentiableAt (by simp))
    (orbit_smooth.mdifferentiableAt (by simp))
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
/-- Localized nondistinguished-coefficient cancellation. Only equality to zero on the calculus set
is used. -/
theorem otherCoefficient_mfderivWithin_zero_of_fundamentalField
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (s : Set P) (p : P) (_open_s : IsOpen s) (hp : p ∈ s)
    (_unique_s : UniqueMDiffOn IP s)
    (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamental_field : ∀ q ∈ s,
      fields r q = principalFundamentalVectorField (smoothBundle := smoothBundle) X q)
    (i : Fin (n + 2)) (hir : i ≠ r) :
    (NormedSpace.fromTangentSpace
      (groupLieAlgebraModelEquiv IG
        (form.toForm p (i.removeNth (fun k => fields k p))))
      (mfderivWithin IP (modelWithCornersSelf ℝ EG)
        (fun q => groupLieAlgebraModelEquiv IG
          (form.toForm q (i.removeNth (fun k => fields k q)))) s p (fields i p))) = 0 := by
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hir.symm
  have form_zero (q : P) (hq : q ∈ s) :
      form.toForm q (i.removeNth (fun k => fields k q)) = 0 := by
    apply horizontal q
    refine ⟨z, ?_⟩
    rw [Fin.removeNth_apply, hz, fundamental_field q hq]
    exact principalFundamentalVectorField_projection_eq_zero X q
  have coefficient_zero (q : P) (hq : q ∈ s) :
      groupLieAlgebraModelEquiv IG
        (form.toForm q (i.removeNth (fun k => fields k q))) = (0 : EG) := by
    rw [form_zero q hq, map_zero]
  rw [mfderivWithin_congr coefficient_zero (coefficient_zero p hp), mfderivWithin_const]
  rfl

/-- Fully localized Cartan reduction. Smoothness and bracket calculus are restricted to the open
set `s`; orbit adaptation still ranges over every `g : G`. -/
theorem exteriorDerivative_apply_fundamental_of_adaptedFieldsWithin
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (s : Set P) (p : P) (open_s : IsOpen s) (hp : p ∈ s)
    (unique_s : UniqueMDiffOn IP s)
    (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP s (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamental_field : ∀ q ∈ s,
      fields r q = principalFundamentalVectorField (smoothBundle := smoothBundle) X q)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p))
    (bracketTerm_zero : ∀ (i j : Fin (n + 1)), j ∈ Finset.Ici i →
      groupLieAlgebraModelEquiv IG
        (form.toForm p (Matrix.vecCons
          (VectorField.mlieBracketWithin IP
            (fields i.castSucc) (fields j.succ) s p)
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0) :
    exterior.derivative.toForm p (fun i => fields i p) =
      -((-1 : ℤ) ^ (r : ℕ) •
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have distinguished := distinguishedCoefficient_mfderivWithin_fundamental
    (smoothBundle := smoothBundle) n form equivariant s p open_s hp unique_s fields
      fields_smooth r X adapted
  have cartan := exterior.cartan_formula s p open_s hp unique_s fields fields_smooth
  unfold ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates at cartan
  have first_sum :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (NormedSpace.fromTangentSpace
          (groupLieAlgebraModelEquiv IG
            (form.toForm p (i.removeNth (fun k => fields k p))))
          (mfderivWithin IP (modelWithCornersSelf ℝ EG)
            (fun q => groupLieAlgebraModelEquiv IG
              (form.toForm q (i.removeNth (fun k => fields k q)))) s p (fields i p)))) =
        (-1 : ℤ) ^ (r : ℕ) •
          (-groupLieAlgebraModelEquiv IG
            ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) := by
    rw [Finset.sum_eq_single r]
    · rw [fundamental_field p hp]
      exact congrArg (fun z : EG => (-1 : ℤ) ^ (r : ℕ) • z) distinguished
    · intro i hi hir
      rw [otherCoefficient_mfderivWithin_zero_of_fundamentalField
        (smoothBundle := smoothBundle) n form horizontal s p open_s hp unique_s fields r X
          fundamental_field i hir,
        smul_zero]
    · simp
  have bracket_summand_zero (i j : Fin (n + 1)) (hj : j ∈ Finset.Ici i) :
      (-1 : ℤ) ^ (i + j : ℕ) •
        groupLieAlgebraModelEquiv IG
          (form.toForm p (Matrix.vecCons
            (VectorField.mlieBracketWithin IP
              (fields i.castSucc) (fields j.succ) s p)
            (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0 := by
    rw [bracketTerm_zero i j hj, smul_zero]
  have second_sum :
      (∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℤ) ^ (i + j : ℕ) •
        groupLieAlgebraModelEquiv IG
          (form.toForm p (Matrix.vecCons
            (VectorField.mlieBracketWithin IP
              (fields i.castSucc) (fields j.succ) s p)
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
