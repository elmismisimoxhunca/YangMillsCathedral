/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCommonAdaptedTotalFields
import YangMills.Geometry.PrincipalFormCovariantExteriorBracketEquivariance
import YangMills.Mathematics.SmoothManifoldDifferentialFormOutputLinear
import YangMills.Mathematics.SmoothManifoldDifferentialFormDiffeomorphPullback

namespace YangMills.Geometry
open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics
open PrincipalOrbitAdapted

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 4000000

variable {EG : Type uEG} {HG : Type uHG}
 [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
 {EB : Type uEB} {HB : Type uHB}
 [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace HB]
 {EP : Type uEP} {HP : Type uHP}
 [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] [TopologicalSpace HP]
 {G : Type uG} {B : Type uB} {P : Type uP}
 [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
 [IsTopologicalGroup G]
 (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
 (IP : ModelWithCorners ℝ EP HP)
 [ChartedSpace HG G] [LieGroup IG ∞ G]
 [ChartedSpace HB B] [IsManifold IB ∞ B]
 [ChartedSpace HP P] [IsManifold IP ∞ P]
 [ENat.LEInfty (minSmoothness ℝ 3)]
 {torsor : PrincipalBundleTorsorData G B P}
 {bundle : TopologicalPrincipalBundleData torsor}
 (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- Fixed principal right translation as an equivalence. -/
def principalRightTranslationEquiv (g : G) : P ≃ P where
  toFun := principalRightTranslation torsor g
  invFun := principalRightTranslation torsor g⁻¹
  left_inv := by
    intro p
    simp [principalRightTranslation, torsor.right_mul, torsor.right_one]
  right_inv := by
    intro p
    simp [principalRightTranslation, torsor.right_mul, torsor.right_one]

/-- Fixed principal right translation as a smooth diffeomorphism. -/
def principalRightTranslationDiffeomorph (g : G) : P ≃ₘ^∞⟮IP, IP⟯ P where
  toEquiv := principalRightTranslationEquiv (torsor := torsor) g
  contMDiff_toFun := principalRightTranslation_smooth smoothBundle g
  contMDiff_invFun := principalRightTranslation_smooth smoothBundle g⁻¹

namespace PrincipalForm

/-- The ordinary positive-degree exterior derivative of a right-adjoint-equivariant principal form
is again right-adjoint-equivariant. -/
theorem exteriorDerivative_isRightAdEquivariant
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    IsRightAdEquivariant smoothBundle exterior.derivative.toForm := by
  letI : CompleteSpace EP := FiniteDimensional.complete ℝ EP
  intro g p v
  let e := principalRightTranslationDiffeomorph IG IB IP smoothBundle g
  let L := lieGroupAdjoint IG g⁻¹
  let mappedForm := form.postcompContinuousLinearMap (groupLieAlgebraModelEquiv IG) L (n + 1)
  let mappedDerivative := exterior.derivative.postcompContinuousLinearMap
    (groupLieAlgebraModelEquiv IG) L (n + 2)
  let mappedCertificate := exterior.postcompContinuousLinearMap
    (groupLieAlgebraModelEquiv IG) L n
  let pulledDerivative := exterior.derivative.pullbackDiffeomorph e
    (groupLieAlgebraModelEquiv IG) (n + 2)
  have hpullForm : mappedForm.toForm =
      ManifoldDifferentialForm.pullback e e.contMDiff form.toForm := by
    funext q
    ext w
    simp only [mappedForm, SmoothManifoldDifferentialForm.postcompContinuousLinearMap,
      ManifoldDifferentialForm.postcompContinuousLinearMap_apply,
      ManifoldDifferentialForm.pullback,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact (equivariant g q w).symm
  let pulledCertificate :=
    SmoothManifoldPositiveDegreeExteriorDerivativeCertificate.pullbackDiffeomorph
      e (groupLieAlgebraModelEquiv IG) n form exterior mappedForm hpullForm
        pulledDerivative (by rfl)
  obtain ⟨U, fields, hopen, hp, _horbit, hvalue, hsmooth, _hright, _hbracket⟩ :=
    exists_common_principalAdaptedTotalFields_arbitrary IG IB IP smoothBundle p 0 v
  have hagree := mappedCertificate.derivatives_agree_on_smoothFields pulledCertificate
    U p hopen hp hopen.uniqueMDiffOn fields hsmooth
  apply (groupLieAlgebraModelEquiv IG).injective
  rw [show (fun i => fields i p) = v by funext i; exact hvalue i] at hagree
  exact hagree.symm

/-- The full covariant-exterior candidate is right-adjoint-equivariant. -/
theorem covariantExteriorCandidate_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    IsRightAdEquivariant smoothBundle
      (covariantExteriorCandidate connection n form exterior).toForm := by
  intro g p v
  rw [covariantExteriorCandidate_apply]
  change exterior.derivative.toForm (torsor.rightAction p g)
      (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) +
      (covariantExteriorBracket connection n form).toForm (torsor.rightAction p g)
        (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) = _
  rw [exteriorDerivative_isRightAdEquivariant IG IB IP smoothBundle n form exterior equivariant g p v,
    covariantExteriorBracket_isRightAdEquivariant connection n form equivariant g p v]
  rw [covariantExteriorCandidate_apply, covariantExteriorBracket_toForm, map_add]

end PrincipalForm
end
end YangMills.Geometry
