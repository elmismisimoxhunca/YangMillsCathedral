/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Regularity of the Lie-group adjoint representation

The adjoint map was defined as the manifold derivative of conjugation and its algebraic laws were
proved previously. Mathlib's parameter-dependent manifold-derivative theorem proves that this map
varies smoothly in the group parameter after transport to the declared normed model coordinates.

This is reusable manifold calculus. No gauge group, principal bundle, or Yang--Mills field is
constructed.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- The adjoint map transported to the declared normed model coordinates. -/
def lieGroupAdjointCoordinates (g : G) : E →L[ℝ] E :=
  ((groupLieAlgebraModelEquiv (G := G) I :
      GroupLieAlgebra I G →L[ℝ] E).comp
    ((lieGroupAdjoint I g).comp
      (groupLieAlgebraModelEquiv (G := G) I).symm.toContinuousLinearMap))

omit [IsTopologicalGroup G] in
/-- The model-coordinate adjoint map as a continuous linear equivalence. Its inverse is the same
coordinate construction at the inverse group element. -/
def lieGroupAdjointCoordinatesEquiv (g : G) : E ≃L[ℝ] E where
  toFun := lieGroupAdjointCoordinates (I := I) g
  invFun := lieGroupAdjointCoordinates (I := I) g⁻¹
  map_add' := (lieGroupAdjointCoordinates (I := I) g).map_add
  map_smul' := (lieGroupAdjointCoordinates (I := I) g).map_smul
  left_inv X := by
    let coordinates := groupLieAlgebraModelEquiv (G := G) I
    change coordinates
      (lieGroupAdjoint I g⁻¹ (lieGroupAdjoint I g (coordinates.symm X))) = X
    rw [lieGroupAdjoint_inv_apply]
    exact coordinates.apply_symm_apply X
  right_inv X := by
    let coordinates := groupLieAlgebraModelEquiv (G := G) I
    change coordinates
      (lieGroupAdjoint I g (lieGroupAdjoint I g⁻¹ (coordinates.symm X))) = X
    rw [lieGroupAdjoint_apply_inv]
    exact coordinates.apply_symm_apply X
  continuous_toFun := (lieGroupAdjointCoordinates (I := I) g).continuous
  continuous_invFun := (lieGroupAdjointCoordinates (I := I) g⁻¹).continuous

omit [IsTopologicalGroup G] in
/-- The forward continuous linear map of the coordinate equivalence is the existing coordinate
adjoint map. -/
@[simp]
theorem lieGroupAdjointCoordinatesEquiv_apply (g : G) (X : E) :
    lieGroupAdjointCoordinatesEquiv (I := I) g X =
      lieGroupAdjointCoordinates (I := I) g X :=
  rfl

omit [IsTopologicalGroup G] in
/-- The inverse coordinate equivalence is adjoint action by the inverse group element. -/
@[simp]
theorem lieGroupAdjointCoordinatesEquiv_symm_apply (g : G) (X : E) :
    (lieGroupAdjointCoordinatesEquiv (I := I) g).symm X =
      lieGroupAdjointCoordinates (I := I) g⁻¹ X :=
  rfl

omit [IsTopologicalGroup G] in
/-- When both tangent-space base maps are constantly the same point, Mathlib's coordinate transport
for a family of continuous linear maps reduces to that family itself. -/
theorem inTangentCoordinates_const_const (x₀ : G) (φ : G → E →L[ℝ] E) (g : G) :
    inTangentCoordinates I I (fun _ : G => x₀) (fun _ : G => x₀) φ g = φ := by
  funext x
  rw [inTangentCoordinates_eq]
  · ext X
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [(tangentBundleCore I G).coordChange_self,
      (tangentBundleCore I G).coordChange_self]
    all_goals
      rw [tangentBundleCore_baseSet]
      exact mem_chart_source H x₀
  · exact mem_chart_source H x₀
  · exact mem_chart_source H x₀

omit [IsTopologicalGroup G] in
set_option backward.isDefEq.respectTransparency false in
/-- The derivative-defined adjoint representation varies smoothly in model coordinates. This is a
specialization of Mathlib's parameter-dependent `ContMDiffAt.mfderiv` theorem to jointly smooth
conjugation and the constant identity evaluation point. -/
theorem lieGroupAdjointCoordinates_contMDiff :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G => lieGroupAdjointCoordinates (I := I) g) := by
  intro g
  let conjugationFamily : G → G → G := fun a b => a * b * a⁻¹
  have familySmooth : ContMDiff (I.prod I) I ∞ (Function.uncurry conjugationFamily) := by
    exact (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv
  have derivativeSmooth :=
    (familySmooth.contMDiffAt (x := (g, 1))).mfderiv conjugationFamily
      (fun _ : G => (1 : G)) (contMDiffAt_const (x := g))
      (m := (∞ : WithTop ℕ∞)) (by simp)
  dsimp [conjugationFamily] at derivativeSmooth
  simp only [mul_one, mul_inv_cancel] at derivativeSmooth
  rw [inTangentCoordinates_const_const (I := I) 1] at derivativeSmooth
  refine derivativeSmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro x
  ext X
  rfl

omit [IsTopologicalGroup G] in
/-- The forward operator family of coordinate adjoint equivalences is smooth. -/
theorem lieGroupAdjointCoordinatesEquiv_contMDiff :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G => (lieGroupAdjointCoordinatesEquiv (I := I) g).toContinuousLinearMap) := by
  have function_eq :
      (fun g : G => (lieGroupAdjointCoordinatesEquiv (I := I) g).toContinuousLinearMap) =
        (fun g : G => lieGroupAdjointCoordinates (I := I) g) := by
    funext g
    ext X
    rfl
  rw [function_eq]
  exact lieGroupAdjointCoordinates_contMDiff (I := I) (G := G)

omit [IsTopologicalGroup G] in
/-- The inverse operator family is smooth and is exactly the coordinate adjoint at `g⁻¹`. -/
theorem lieGroupAdjointCoordinatesEquiv_symm_contMDiff :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G => (lieGroupAdjointCoordinatesEquiv (I := I) g).symm.toContinuousLinearMap) := by
  have function_eq :
      (fun g : G =>
        (lieGroupAdjointCoordinatesEquiv (I := I) g).symm.toContinuousLinearMap) =
        (fun g : G => lieGroupAdjointCoordinates (I := I) g⁻¹) := by
    funext g
    ext X
    rfl
  rw [function_eq]
  exact (lieGroupAdjointCoordinates_contMDiff (I := I) (G := G)).comp contMDiff_id.inv

omit [IsTopologicalGroup G] in
/-- Joint smoothness of the model-coordinate adjoint evaluation. -/
theorem lieGroupAdjointCoordinates_action_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun z : G × E => lieGroupAdjointCoordinates (I := I) z.1 z.2) := by
  have operatorSmooth : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun z : G × E => lieGroupAdjointCoordinates (I := I) z.1) :=
    (lieGroupAdjointCoordinates_contMDiff (I := I) (G := G)).comp contMDiff_fst
  exact operatorSmooth.clm_apply contMDiff_snd

omit [IsTopologicalGroup G] in
/-- Joint smoothness also holds after inversion in the group parameter. -/
theorem lieGroupAdjointCoordinates_inverseAction_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun z : G × E => lieGroupAdjointCoordinates (I := I) z.1⁻¹ z.2) := by
  have inverseSmooth : ContMDiff (I.prod 𝓘(ℝ, E)) I ∞ (fun z : G × E => z.1⁻¹) :=
    contMDiff_fst.inv
  have operatorSmooth : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun z : G × E => lieGroupAdjointCoordinates (I := I) z.1⁻¹) :=
    (lieGroupAdjointCoordinates_contMDiff (I := I) (G := G)).comp inverseSmooth
  exact operatorSmooth.clm_apply contMDiff_snd

/-- Continuity certificate retained as a compact interface for the topological associated-bundle
layer. Its canonical inhabitant is derived below; it is not model data or an open assumption. -/
structure ContinuousLieGroupAdjointData : Prop where
  map_continuous : Continuous (fun g : G => lieGroupAdjointCoordinates (I := I) g)

/-- Every smooth Lie group has the adjoint-continuity certificate. -/
def continuousLieGroupAdjointData : ContinuousLieGroupAdjointData (I := I) (G := G) where
  map_continuous := (lieGroupAdjointCoordinates_contMDiff (I := I) (G := G)).continuous

namespace ContinuousLieGroupAdjointData

omit [IsTopologicalGroup G] in
/-- Joint continuity of `(g,X) ↦ Ad(g)X` follows from continuity into continuous linear maps. -/
theorem action_continuous (data : ContinuousLieGroupAdjointData (I := I) (G := G)) :
    Continuous (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1 z.2) := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) I
  have inputCoordinates : Continuous
      (fun z : G × GroupLieAlgebra I G => (z.1, coordinates z.2)) :=
    continuous_fst.prodMk (coordinates.continuous.comp continuous_snd)
  have evaluated : Continuous (fun z : G × E =>
      lieGroupAdjointCoordinates (I := I) z.1 z.2) :=
    (data.map_continuous.comp continuous_fst).clm_apply continuous_snd
  have transported := coordinates.symm.continuous.comp (evaluated.comp inputCoordinates)
  simpa [coordinates, lieGroupAdjointCoordinates, Function.comp_def] using transported

/-- Joint continuity also holds for the inverse-adjoint action used by associated bundles. -/
theorem inverseAction_continuous (data : ContinuousLieGroupAdjointData (I := I) (G := G)) :
    Continuous (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1⁻¹ z.2) := by
  have input : Continuous (fun z : G × GroupLieAlgebra I G => (z.1⁻¹, z.2)) :=
    (continuous_inv.comp continuous_fst).prodMk continuous_snd
  simpa [Function.comp_def] using data.action_continuous.comp input

end ContinuousLieGroupAdjointData

end

end YangMills.Mathematics
