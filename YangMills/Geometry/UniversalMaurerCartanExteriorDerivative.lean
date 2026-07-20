/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AssociatedMaurerCartanStructureCandidate
import YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport

/-!
# Universal Maurer--Cartan exterior derivative

The universal left Maurer--Cartan form is proved smooth and its exact exterior derivative is
certified as `-1/2[θ∧θ]`. Finite-dimensional intrinsic Cartan field-extension independence upgrades
the invariant-field calculation to every admissible local pair of smooth fields, producing a genuine
`SmoothManifoldOneFormExteriorDerivativeCertificate` and the universal structure equation.

This theorem is on the group itself. Transporting the certificate along the associated gauge
function still requires arbitrary-smooth-map certificate pullback.
-/

namespace YangMills.Geometry

open Set Function Filter ChartedSpace IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle
open YangMills.Mathematics

universe uEG uHG uG

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G] in
private theorem contMDiff_invariantField_top
    (v : GroupLieAlgebra IG G) :
    ContMDiff IG (IG.prod (modelWithCornersSelf ℝ EG)) ∞
      (fun g => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle IG G)) := by
  let fg : G → TangentBundle IG G := fun g => TotalSpace.mk' EG g 0
  have sfg : ContMDiff IG IG.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle IG G := fun _ => TotalSpace.mk' EG 1 v
  have sfv : ContMDiff IG IG.tangent ∞ fv := contMDiff_const
  let F₁ : G → (TangentBundle IG G × TangentBundle IG G) := fun g => (fg g, fv g)
  have S₁ : ContMDiff IG (IG.tangent.prod IG.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle IG G × TangentBundle IG G) →
      TangentBundle (IG.prod IG) (G × G) :=
    (equivTangentBundleProd IG G IG G).symm
  have S₂ : ContMDiff (IG.tangent.prod IG.tangent) (IG.prod IG).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (IG.prod IG) (G × G) → TangentBundle IG G :=
    tangentMap (IG.prod IG) IG (fun p : G × G => p.1 * p.2)
  have S₃ : ContMDiff (IG.prod IG).tangent IG.tangent ∞ F₃ := by
    have hmul : ContMDiff (IG.prod IG) IG ∞ (fun p : G × G => p.1 * p.2) :=
      contMDiff_fst.mul contMDiff_snd
    exact hmul.contMDiff_tangentMap (by simp)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    have hmul : ContMDiff (IG.prod IG) IG ∞ (fun p : G × G => p.1 * p.2) :=
      contMDiff_fst.mul contMDiff_snd
    rw [mfderiv_prod_eq_add_apply (hmul.mdifferentiableAt (by simp))]
    simp +instances [equivTangentBundleProd, mulInvariantVectorField]

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G] in
private theorem leftMaurerCartanForm_isSmooth :
    (leftMaurerCartanForm (IG := IG) (G := G)).IsSmooth
      (groupLieAlgebraModelEquiv IG) := by
  intro s fields fields_smooth
  let sourceField : G → TangentBundle IG G := fun g => ⟨g, fields 0 g⟩
  have hsourceField : ContMDiffOn IG IG.tangent ∞ sourceField s := fields_smooth 0
  let zeroAtG : G → TangentBundle IG G := fun g => ⟨g, 0⟩
  have hzeroAtG : ContMDiffOn IG IG.tangent ∞ zeroAtG s := by
    have hzero : ContMDiff IG IG.tangent ∞
        (Bundle.zeroSection EG (TangentSpace IG : G → Type _)) :=
      Bundle.contMDiff_zeroSection ℝ _
    exact hzero.contMDiffOn
  let pairField : G → (TangentBundle IG G × TangentBundle IG G) :=
    fun g => (zeroAtG g, sourceField g)
  have hpairField : ContMDiffOn IG (IG.tangent.prod IG.tangent) ∞ pairField s :=
    hzeroAtG.prodMk hsourceField
  let productField : G → TangentBundle (IG.prod IG) (G × G) := fun g =>
    (equivTangentBundleProd IG G IG G).symm (pairField g)
  have hproductField : ContMDiffOn IG (IG.prod IG).tangent ∞ productField s :=
    contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn hpairField
  let difference : G × G → G := fun z => z.1⁻¹ * z.2
  have hdifference : ContMDiff (IG.prod IG) IG ∞ difference :=
    contMDiff_fst.inv.mul contMDiff_snd
  let resultField : G → TangentBundle IG G := fun g =>
    tangentMap (IG.prod IG) IG difference (productField g)
  have hresultField : ContMDiffOn IG IG.tangent ∞ resultField s := by
    have htangent : ContMDiff (IG.prod IG).tangent IG.tangent ∞
        (tangentMap (IG.prod IG) IG difference) :=
      hdifference.contMDiff_tangentMap (by simp)
    exact htangent.comp_contMDiffOn hproductField
  intro g hg
  have htotal := hresultField g hg
  have hfiber := (Bundle.contMDiffWithinAt_totalSpace.mp htotal).2
  have hbase : (resultField g).proj = (1 : G) := by
    simp [resultField, productField, pairField, zeroAtG, sourceField,
      difference, tangentMap]
  rw [hbase] at hfiber
  apply hfiber.congr_of_eventuallyEq_of_mem _ hg
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hbaseq : (resultField q).proj = (1 : G) := by
    simp [resultField, productField, pairField, zeroAtG, sourceField,
      difference, tangentMap]
  rw [TangentBundle.trivializationAt_apply, hbaseq]
  change groupLieAlgebraModelEquiv IG
      ((leftMaurerCartanForm (IG := IG) (G := G)) q (fun i => fields i q)) =
    tangentCoordChange IG (1 : G) (1 : G) (1 : G) (resultField q).2
  rw [tangentCoordChange_self (mem_extChartAt_source (I := IG) (1 : G))]
  simp [resultField, productField, pairField, zeroAtG, sourceField,
    difference, tangentMap, leftMaurerCartanForm, groupLieAlgebraModelEquiv]
  symm
  let v : EG := fields 0 q
  change mfderiv (IG.prod IG) IG (fun z : G × G => z.1⁻¹ * z.2)
      (q, q) (0, v) = mfderiv IG IG (fun y : G => q⁻¹ * y) q v
  have hsplit := mfderiv_prod_eq_add_apply
    (f := fun z : G × G => z.1⁻¹ * z.2) (p := (q, q)) (v := ((0, v) : EG × EG))
    (hdifference.mdifferentiableAt (by simp))
  rw [hsplit]
  simp

noncomputable def leftMaurerCartanSmoothForm :
    SmoothManifoldDifferentialForm IG G (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1 where
  toForm := leftMaurerCartanForm
  smooth := leftMaurerCartanForm_isSmooth

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G] in
@[simp] theorem leftMaurerCartanSmoothForm_toForm :
    (leftMaurerCartanSmoothForm (IG := IG) (G := G)).toForm = leftMaurerCartanForm := rfl

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem mulInvariant_leftMaurerCartanApply
    (g : G) (v : TangentSpace IG g) :
    mulInvariantVectorField (leftMaurerCartanApply g v) g = v := by
  let forward : G → G := fun y => g * y
  let backward : G → G := fun y => g⁻¹ * y
  have hcomp := mfderiv_comp (I := IG) (I' := IG) (I'' := IG)
    (f := backward) (g := forward) g
    ((lieGroupLeftTranslation_smooth (IG := IG) g).mdifferentiableAt (by simp))
    ((lieGroupLeftTranslation_smooth (IG := IG) g⁻¹).mdifferentiableAt (by simp))
  have hfun : forward ∘ backward = id := by
    funext y
    simp [backward, forward]
  rw [hfun, mfderiv_id] at hcomp
  have happ := congrArg (fun L => L v) hcomp
  change v = mfderiv IG IG forward (backward g)
    (mfderiv IG IG backward g v) at happ
  change mfderiv IG IG forward 1 (mfderiv IG IG backward g v) = v
  rw [show backward g = 1 by simp [backward]] at happ
  exact happ.symm

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G] [LieGroup IG ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
private theorem cartan_open_eq_univ
    (s : Set G) (x : G) (open_s : IsOpen s) (mem_s : x ∈ s)
    (first second : (y : G) → TangentSpace IG y) :
    (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) s x first second =
      (leftMaurerCartanForm (IG := IG) (G := G)).oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) Set.univ x first second := by
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  rw [mfderivWithin_of_isOpen open_s mem_s, mfderivWithin_univ,
    mfderivWithin_of_isOpen open_s mem_s, mfderivWithin_univ,
    VectorField.mlieBracketWithin_of_isOpen open_s mem_s,
    VectorField.mlieBracketWithin_univ]

noncomputable def leftMaurerCartanExteriorDerivative :
    SmoothManifoldDifferentialForm IG G (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 2 :=
  SmoothManifoldDifferentialForm.smul (-1 / 2 : ℝ)
    (SmoothManifoldDifferentialForm.lieBracketWedgeOneMany
      (I := IG) (M := G) (V := GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1
      leftMaurerCartanSmoothForm leftMaurerCartanSmoothForm)

omit [IsTopologicalGroup G] in
@[simp] theorem leftMaurerCartanExteriorDerivative_toForm :
    (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm =
      (-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm := by
  unfold leftMaurerCartanExteriorDerivative
  rw [SmoothManifoldDifferentialForm.smul_toForm,
    SmoothManifoldDifferentialForm.lieBracketWedgeOneMany_toForm]
  rfl

noncomputable def leftMaurerCartanExteriorDerivativeCertificate :
    SmoothManifoldOneFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG)
      (leftMaurerCartanSmoothForm (IG := IG) (G := G)) where
  derivative := leftMaurerCartanExteriorDerivative (IG := IG) (G := G)
  cartan_formula := by
    intro s x open_s mem_s unique_s first second first_smooth second_smooth
    let v := leftMaurerCartanApply x (first x)
    let w := leftMaurerCartanApply x (second x)
    let first' := mulInvariantVectorField (I := IG) v
    let second' := mulInvariantVectorField (I := IG) w
    have first'_smooth : ManifoldTangentField.IsSmoothOn IG s first' :=
      (contMDiff_invariantField_top (IG := IG) (G := G) v).contMDiffOn
    have second'_smooth : ManifoldTangentField.IsSmoothOn IG s second' :=
      (contMDiff_invariantField_top (IG := IG) (G := G) w).contMDiffOn
    have hfirst : first x = first' x := by
      symm
      exact mulInvariant_leftMaurerCartanApply (IG := IG) x (first x)
    have hsecond : second x = second' x := by
      symm
      exact mulInvariant_leftMaurerCartanApply (IG := IG) x (second x)
    rw [leftMaurerCartanExteriorDerivative_toForm]
    change (groupLieAlgebraModelEquiv IG)
      (((-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm) x
          (ManifoldDifferentialForm.twoVectorArguments first second x)) = _
    have hargs : ManifoldDifferentialForm.twoVectorArguments first second x =
        ManifoldDifferentialForm.twoVectorArguments first' second' x := by
      funext i
      fin_cases i
      · exact hfirst
      · exact hsecond
    have wedge_congr :
        (((-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
          leftMaurerCartanForm leftMaurerCartanForm) x
            (ManifoldDifferentialForm.twoVectorArguments first second x)) =
        (((-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
          leftMaurerCartanForm leftMaurerCartanForm) x
            (ManifoldDifferentialForm.twoVectorArguments first' second' x)) := by
      rw [hargs]
    rw [wedge_congr]
    rw [leftMaurerCartan_candidate_cartan_invariant (IG := IG) x v w]
    rw [← cartan_open_eq_univ (IG := IG) s x open_s mem_s first' second']
    exact (SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
      (groupLieAlgebraModelEquiv IG) leftMaurerCartanSmoothForm s x mem_s unique_s
      first' second' first second first'_smooth second'_smooth first_smooth second_smooth
      hfirst.symm hsecond.symm)

omit [IsTopologicalGroup G] in
@[simp]
theorem leftMaurerCartanExteriorDerivativeCertificate_derivative :
    (leftMaurerCartanExteriorDerivativeCertificate (IG := IG) (G := G)).derivative =
      leftMaurerCartanExteriorDerivative :=
  rfl

omit [IsTopologicalGroup G] in
/-- Universal Maurer--Cartan structure equation. -/
theorem leftMaurerCartan_structureEquation :
    (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm +
      (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm = 0 := by
  rw [leftMaurerCartanExteriorDerivative_toForm]
  module

end
end YangMills.Geometry
