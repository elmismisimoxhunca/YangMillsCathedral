import YangMills.Mathematics.ManifoldOneFormExteriorDerivative
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

/-!
# Exterior derivative certificates under diffeomorphism pullback

This module proves pullback naturality of the Cartan formula for fixed-value smooth one-forms under
a smooth diffeomorphism. It transports arbitrary local tangent fields to the image set, proves the
within-set chain rules and Lie-bracket transport, and constructs the pulled exterior-derivative
certificate.

Mathlib's public `mpullback_mlieBracketWithin` theorem requires completeness of the source model.
The same explicit hypothesis is retained here; no arbitrary-manifold completeness is inferred.
-/

namespace YangMills.Mathematics

open Set Function
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM'

variable
    {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    [IsManifold I ∞ M] [IsManifold I' ∞ M']

noncomputable section

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
lemma Diffeomorph.isInvertible_mfderiv (e : M ≃ₘ^∞⟮I, I'⟯ M') (x : M) :
    (mfderiv I I' e x).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := mfderiv I' I e.symm (e x))
  · have hcomp := mfderiv_comp (I := I') (I' := I) (I'' := I')
      (f := (e.symm : M' → M)) (g := (e : M → M')) (e x)
      (e.contMDiff.mdifferentiable (by simp) (e.symm (e x)))
      (e.symm.contMDiff.mdifferentiable (by simp) (e x))
    have hfun : (e : M → M') ∘ e.symm = id := by
      funext y
      exact e.apply_symm_apply y
    rw [mfderiv_congr (x := e x) hfun, mfderiv_id] at hcomp
    rw [e.symm_apply_apply x] at hcomp
    exact hcomp.symm
  · have hcomp := mfderiv_comp (I := I) (I' := I') (I'' := I)
      (f := (e : M → M')) (g := (e.symm : M' → M)) x
      (e.symm.contMDiff.mdifferentiable (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x)
    have hfun : (e.symm : M' → M) ∘ e = id := by
      funext y
      exact e.symm_apply_apply y
    rw [mfderiv_congr (x := x) hfun, mfderiv_id] at hcomp
    rw [e.symm_apply_apply x] at hcomp
    exact hcomp.symm


/-- Push a vector field through a diffeomorphism. -/
def Diffeomorph.pushforwardField (e : M ≃ₘ^∞⟮I, I'⟯ M')
    (X : (x : M) → TangentSpace I x) (y : M') : TangentSpace I' y :=
  mfderiv I I' e (e.symm y) (X (e.symm y))

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
lemma Diffeomorph.mpullback_pushforwardField
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (X : (x : M) → TangentSpace I x) :
    VectorField.mpullback I I' e (Diffeomorph.pushforwardField e X) = X := by
  funext x
  rw [VectorField.mpullback_apply]
  unfold Diffeomorph.pushforwardField
  rw [e.symm_apply_apply x]
  exact (Diffeomorph.isInvertible_mfderiv e x).inverse_apply_eq.mpr rfl

lemma Diffeomorph.pushforwardField_isSmoothOn
    (e : M ≃ₘ^∞⟮I, I'⟯ M') {s : Set M}
    (X : (x : M) → TangentSpace I x)
    (hX : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I s X) :
    YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s)
      (Diffeomorph.pushforwardField e X) := by
  have hsource : ContMDiffOn I' (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y => (⟨e.symm y, X (e.symm y)⟩ : TangentBundle I M)) (e '' s) := by
    apply hX.comp e.symm.contMDiff.contMDiffOn
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using hx
  have htangent : ContMDiff I.tangent I'.tangent ∞ (tangentMap I I' e) :=
    e.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)
  have hcomposed := htangent.comp_contMDiffOn hsource
  apply hcomposed.congr
  intro y hy
  apply Bundle.TotalSpace.ext
  · exact (e.apply_symm_apply y).symm
  · rfl

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
lemma Diffeomorph.mfderivWithin_comp_apply_pushforward
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (g : M' → W) (s : Set M) (x : M)
    (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (hg : MDifferentiableWithinAt I' (modelWithCornersSelf ℝ W) g (e '' s) (e x))
    (X : (x : M) → TangentSpace I x) :
    mfderivWithin I (modelWithCornersSelf ℝ W) (g ∘ e) s x (X x) =
      mfderivWithin I' (modelWithCornersSelf ℝ W) g (e '' s) (e x)
        (Diffeomorph.pushforwardField e X (e x)) := by
  have he : MDifferentiableWithinAt I I' e s x :=
    (e.contMDiff.mdifferentiable (by simp) x).mdifferentiableWithinAt
  have hchain := mfderivWithin_comp (I' := I') (u := e '' s) x hg he
    (Set.mapsTo_image e s) (hs x hx)
  have heq : mfderivWithin I I' e s x = mfderiv I I' e x := by
    apply mfderivWithin_eq_mfderiv
    · exact hs x hx
    · exact e.contMDiff.mdifferentiable (by simp) x
  rw [hchain, heq]
  unfold Diffeomorph.pushforwardField
  rw [e.symm_apply_apply x]
  rfl

lemma Diffeomorph.mfderiv_mlieBracketWithin
    [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (s : Set M) (x : M)
    (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I s X)
    (hY : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I s Y) :
    mfderiv I I' e x (VectorField.mlieBracketWithin I X Y s x) =
      VectorField.mlieBracketWithin I'
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y) (e '' s) (e x) := by
  letI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))
  letI : IsManifold I' (minSmoothness ℝ 2) M' :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))
  let X' := Diffeomorph.pushforwardField e X
  let Y' := Diffeomorph.pushforwardField e Y
  have hX' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) X' :=
    Diffeomorph.pushforwardField_isSmoothOn e X hX
  have hY' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) Y' :=
    Diffeomorph.pushforwardField_isSmoothOn e Y hY
  have hpre : (e : M → M') ⁻¹' (e '' s) ∈ nhdsWithin x s := by
    have hset : (e : M → M') ⁻¹' (e '' s) = s := by
      ext z
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨y, hy, hye⟩
        exact e.injective hye ▸ hy
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hset]
    exact self_mem_nhdsWithin
  have hnat := VectorField.mpullback_mlieBracketWithin
    (f := (e : M → M')) (V := X') (W := Y') (x₀ := x)
    (s := s) (t := e '' s)
    ((hX' (e x) ⟨x, hx, rfl⟩).mdifferentiableWithinAt (by simp))
    ((hY' (e x) ⟨x, hx, rfl⟩).mdifferentiableWithinAt (by simp))
    hs e.contMDiff.contMDiffAt hx
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))
    hpre
  rw [Diffeomorph.mpullback_pushforwardField e X,
    Diffeomorph.mpullback_pushforwardField e Y] at hnat
  exact ((Diffeomorph.isInvertible_mfderiv e x).inverse_apply_eq.mp hnat).symm

universe uV uW

variable {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma oneFormCartanExpressionCoordinates_pullback_diffeomorph
    [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : YangMills.Mathematics.SmoothManifoldDifferentialForm
      I' M' V coordinates 1)
    (pulledForm : YangMills.Mathematics.SmoothManifoldDifferentialForm
      I M V coordinates 1)
    (hpull : pulledForm.toForm =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (s : Set M) (x : M) (hx : x ∈ s) (hs : UniqueMDiffOn I s)
    (X Y : (x : M) → TangentSpace I x)
    (hX : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I s X)
    (hY : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I s Y) :
    pulledForm.toForm.oneFormCartanExpressionCoordinates coordinates s x X Y =
      form.toForm.oneFormCartanExpressionCoordinates coordinates (e '' s) (e x)
        (Diffeomorph.pushforwardField e X)
        (Diffeomorph.pushforwardField e Y) := by
  let X' := Diffeomorph.pushforwardField e X
  let Y' := Diffeomorph.pushforwardField e Y
  have hX' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) X' :=
    Diffeomorph.pushforwardField_isSmoothOn e X hX
  have hY' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) Y' :=
    Diffeomorph.pushforwardField_isSmoothOn e Y hY
  let gY : M' → W := fun y => coordinates (form.toForm y (fun _ => Y' y))
  let gX : M' → W := fun y => coordinates (form.toForm y (fun _ => X' y))
  have hgY_smooth : ContMDiffOn I' (modelWithCornersSelf ℝ W) ∞ gY (e '' s) := by
    apply form.eval_smooth (e '' s) (fun _ => Y')
    intro i
    exact hY'
  have hgX_smooth : ContMDiffOn I' (modelWithCornersSelf ℝ W) ∞ gX (e '' s) := by
    apply form.eval_smooth (e '' s) (fun _ => X')
    intro i
    exact hX'
  have hmem : e x ∈ e '' s := ⟨x, hx, rfl⟩
  have hgY : MDifferentiableWithinAt I' (modelWithCornersSelf ℝ W)
      gY (e '' s) (e x) :=
    (hgY_smooth (e x) hmem).mdifferentiableWithinAt (by simp)
  have hgX : MDifferentiableWithinAt I' (modelWithCornersSelf ℝ W)
      gX (e '' s) (e x) :=
    (hgX_smooth (e x) hmem).mdifferentiableWithinAt (by simp)
  have evalY (z : M) :
      coordinates (pulledForm.toForm z (fun _ => Y z)) = gY (e z) := by
    rw [hpull]
    unfold YangMills.Mathematics.ManifoldDifferentialForm.pullback gY
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have pushY :
        (mfderiv I I' e z ∘ fun _ : Fin 1 => Y z) = (fun _ : Fin 1 => Y' (e z)) := by
      funext i
      unfold Y' Diffeomorph.pushforwardField
      rw [e.symm_apply_apply z]
      rfl
    rw [pushY]
  have evalX (z : M) :
      coordinates (pulledForm.toForm z (fun _ => X z)) = gX (e z) := by
    rw [hpull]
    unfold YangMills.Mathematics.ManifoldDifferentialForm.pullback gX
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have pushX :
        (mfderiv I I' e z ∘ fun _ : Fin 1 => X z) = (fun _ : Fin 1 => X' (e z)) := by
      funext i
      unfold X' Diffeomorph.pushforwardField
      rw [e.symm_apply_apply z]
      rfl
    rw [pushX]
  have dY := Diffeomorph.mfderivWithin_comp_apply_pushforward e gY s x hx hs hgY X
  have dX := Diffeomorph.mfderivWithin_comp_apply_pushforward e gX s x hx hs hgX Y
  have bracket := Diffeomorph.mfderiv_mlieBracketWithin e s x hx hs X Y hX hY
  unfold YangMills.Mathematics.ManifoldDifferentialForm.oneFormCartanExpressionCoordinates
  rw [evalY x, evalX x]
  rw [mfderivWithin_congr (fun z hz => evalY z) (evalY x),
    mfderivWithin_congr (fun z hz => evalX z) (evalX x)]
  have compY : (fun z => gY (e z)) = gY ∘ e := rfl
  have compX : (fun z => gX (e z)) = gX ∘ e := rfl
  rw [compY, compX]
  have dYW :
      (NormedSpace.fromTangentSpace (gY (e x)))
          (mfderivWithin I (modelWithCornersSelf ℝ W) (gY ∘ e) s x (X x)) =
        (NormedSpace.fromTangentSpace (gY (e x)))
          (mfderivWithin I' (modelWithCornersSelf ℝ W) gY (e '' s) (e x)
            (Diffeomorph.pushforwardField e X (e x))) := by
    exact congrArg (NormedSpace.fromTangentSpace (gY (e x))) dY
  have dXW :
      (NormedSpace.fromTangentSpace (gX (e x)))
          (mfderivWithin I (modelWithCornersSelf ℝ W) (gX ∘ e) s x (Y x)) =
        (NormedSpace.fromTangentSpace (gX (e x)))
          (mfderivWithin I' (modelWithCornersSelf ℝ W) gX (e '' s) (e x)
            (Diffeomorph.pushforwardField e Y (e x))) := by
    exact congrArg (NormedSpace.fromTangentSpace (gX (e x))) dX
  refine (congrArg₂ (fun a b : W => a - b -
    coordinates (pulledForm.toForm x
      (fun _ => VectorField.mlieBracketWithin I X Y s x))) dYW dXW).trans ?_
  rw [hpull]
  simp only [YangMills.Mathematics.ManifoldDifferentialForm.pullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have bracketTuple :
      (mfderiv I I' e x ∘ fun _ : Fin 1 => VectorField.mlieBracketWithin I X Y s x) =
        (fun _ : Fin 1 => VectorField.mlieBracketWithin I'
          (Diffeomorph.pushforwardField e X) (Diffeomorph.pushforwardField e Y)
          (e '' s) (e x)) := by
    funext i
    exact bracket
  rw [bracketTuple]

noncomputable def SmoothManifoldOneFormExteriorDerivativeCertificate.pullbackDiffeomorph
    [CompleteSpace E]
    (e : M ≃ₘ^∞⟮I, I'⟯ M') (coordinates : V ≃L[ℝ] W)
    (form : YangMills.Mathematics.SmoothManifoldDifferentialForm
      I' M' V coordinates 1)
    (certificate :
      YangMills.Mathematics.SmoothManifoldOneFormExteriorDerivativeCertificate
        coordinates form)
    (pulledForm : YangMills.Mathematics.SmoothManifoldDifferentialForm
      I M V coordinates 1)
    (hpullForm : pulledForm.toForm =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback e e.contMDiff form.toForm)
    (pulledDerivative : YangMills.Mathematics.SmoothManifoldDifferentialForm
      I M V coordinates 2)
    (hpullDerivative : pulledDerivative.toForm =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback e e.contMDiff
        certificate.derivative.toForm) :
    YangMills.Mathematics.SmoothManifoldOneFormExteriorDerivativeCertificate
      coordinates pulledForm where
  derivative := pulledDerivative
  cartan_formula := by
    intro s x open_s mem_s unique_s X Y hX hY
    let X' := Diffeomorph.pushforwardField e X
    let Y' := Diffeomorph.pushforwardField e Y
    have hX' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) X' :=
      Diffeomorph.pushforwardField_isSmoothOn e X hX
    have hY' : YangMills.Mathematics.ManifoldTangentField.IsSmoothOn I' (e '' s) Y' :=
      Diffeomorph.pushforwardField_isSmoothOn e Y hY
    have open_image : IsOpen (e '' s) := e.toHomeomorph.isOpen_image.mpr open_s
    have mem_image : e x ∈ e '' s := ⟨x, mem_s, rfl⟩
    have unique_image : UniqueMDiffOn I' (e '' s) :=
      (e.uniqueMDiffOn_image (by simp)).mpr unique_s
    have tuplePush :
        (mfderiv I I' e x ∘
          YangMills.Mathematics.ManifoldDifferentialForm.twoVectorArguments X Y x) =
        YangMills.Mathematics.ManifoldDifferentialForm.twoVectorArguments X' Y' (e x) := by
      funext i
      fin_cases i
      · change mfderiv I I' e x (X x) = X' (e x)
        unfold X' Diffeomorph.pushforwardField
        rw [e.symm_apply_apply x]
      · change mfderiv I I' e x (Y x) = Y' (e x)
        unfold Y' Diffeomorph.pushforwardField
        rw [e.symm_apply_apply x]
    calc
      coordinates (pulledDerivative.toForm x
          (YangMills.Mathematics.ManifoldDifferentialForm.twoVectorArguments X Y x)) =
        coordinates (certificate.derivative.toForm (e x)
          (YangMills.Mathematics.ManifoldDifferentialForm.twoVectorArguments X' Y' (e x))) := by
            rw [hpullDerivative]
            change coordinates (certificate.derivative.toForm (e x)
              (mfderiv I I' e x ∘
                YangMills.Mathematics.ManifoldDifferentialForm.twoVectorArguments X Y x)) = _
            rw [tuplePush]
      _ = form.toForm.oneFormCartanExpressionCoordinates coordinates (e '' s) (e x) X' Y' :=
        certificate.cartan_formula (e '' s) (e x) open_image mem_image unique_image
          X' Y' hX' hY'
      _ = pulledForm.toForm.oneFormCartanExpressionCoordinates coordinates s x X Y :=
        (oneFormCartanExpressionCoordinates_pullback_diffeomorph e coordinates form
          pulledForm hpullForm s x mem_s unique_s X Y hX hY).symm

end


end YangMills.Mathematics
