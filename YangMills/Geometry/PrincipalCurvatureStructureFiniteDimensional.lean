/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureStructure
import YangMills.Geometry.PrincipalFormCovariantExteriorEquivariance
import YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin
import YangMills.Geometry.PrincipalCommonAdaptedTotalFields
import YangMills.Geometry.PrincipalVerticalTangentGeneration
import YangMills.Mathematics.ManifoldOneFormPositiveDegreeExteriorDerivativeBridge

namespace YangMills.Geometry

open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics
open PrincipalOrbitAdapted

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section
set_option maxHeartbeats 4000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
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

namespace PrincipalConnectionData

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- The generic right-adjoint-equivariance presentation of a connection one-form. -/
theorem toSmoothForm_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle) :
    PrincipalForm.IsRightAdEquivariant smoothBundle connection.toSmoothForm.toForm := by
  intro g p v
  have hv : v = fun _ : Fin 1 => v 0 := by
    funext i
    exact congrArg v (Subsingleton.elim i 0)
  rw [hv]
  exact connection.right_equivariant p g (v 0)

/-- The certified ordinary exterior derivative of a connection form remains right-adjoint
 equivariant. -/
theorem exteriorDerivative_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalForm.IsRightAdEquivariant smoothBundle exterior.certificate.derivative.toForm := by
  exact PrincipalForm.exteriorDerivative_isRightAdEquivariant IG IB IP smoothBundle 0
    connection.toSmoothForm exterior.certificate.toPositiveDegreeZero
      (connection.toSmoothForm_isRightAdEquivariant IG IB IP smoothBundle)

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
/-- The self-bracket wedge of the connection is right-adjoint-equivariant. -/
theorem selfBracketWedge_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle) :
    PrincipalForm.IsRightAdEquivariant smoothBundle
      (connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form) := by
  intro g p v
  rw [ManifoldDifferentialForm.lieBracketWedgeOne_apply,
    ManifoldDifferentialForm.lieBracketWedgeOne_apply]
  change ⁅connection.pointwise.form.evalOne (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g (v 0)),
      connection.pointwise.form.evalOne (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g (v 1))⁆ -
    ⁅connection.pointwise.form.evalOne (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g (v 1)),
      connection.pointwise.form.evalOne (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g (v 0))⁆ =
    lieGroupAdjoint IG g⁻¹
      (⁅connection.pointwise.form.evalOne p (v 0),
          connection.pointwise.form.evalOne p (v 1)⁆ -
        ⁅connection.pointwise.form.evalOne p (v 1),
          connection.pointwise.form.evalOne p (v 0)⁆)
  rw [connection.right_equivariant p g (v 0), connection.right_equivariant p g (v 1)]
  rw [map_sub]
  congr 1
  · exact (lieGroupAdjoint_lieBracket IG g⁻¹
      (connection.pointwise.form.evalOne p (v 0))
      (connection.pointwise.form.evalOne p (v 1))).symm
  · exact (lieGroupAdjoint_lieBracket IG g⁻¹
      (connection.pointwise.form.evalOne p (v 1))
      (connection.pointwise.form.evalOne p (v 0))).symm

/-- On a fundamental first slot, Cartan's formula for a connection has the exact infinitesimal
adjoint value. Unlike the generic principal-form theorem, this uses no horizontal-input premise:
vertical normalization makes the second coefficient `Theta(X#) = X` constant. -/
theorem exteriorDerivative_apply_fundamental_first
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (vectors : Fin 2 → TangentSpace IP p)
    (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors 0 = principalFundamentalVector smoothBundle p X) :
    exterior.certificate.derivative.toForm p vectors =
      -⁅X, connection.pointwise.form.evalOne p (vectors 1)⁆ := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  obtain ⟨U, adaptedFields, hopen, hp, _horbit, hvalue, hsmooth, hright, hbracket⟩ :=
    exists_common_principalAdaptedTotalFields_arbitrary IG IB IP smoothBundle p X
      (fun _ : Fin 1 => vectors 1)
  let fundamental : (q : P) → TangentSpace IP q :=
    principalFundamentalVectorField (smoothBundle := smoothBundle) X
  let adapted : (q : P) → TangentSpace IP q := adaptedFields 0
  let fields : Fin 2 → (q : P) → TangentSpace IP q :=
    ManifoldDifferentialForm.twoTangentFieldFamily fundamental adapted
  have hfundamental : ManifoldTangentField.IsSmoothOn IP U fundamental :=
    principalFundamentalVectorField_isSmoothOn X U
  have hadapted : ManifoldTangentField.IsSmoothOn IP U adapted := hsmooth 0
  have hadapted_value : adapted p = vectors 1 := hvalue 0
  have hadapted_right : ∀ g : G,
      adapted (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g (adapted p) := by
    intro g
    exact (hright 0 g).symm
  have hdist := PrincipalForm.distinguishedCoefficient_mfderivWithin_fundamental
    (smoothBundle := smoothBundle) 0 connection.toSmoothForm
      (connection.toSmoothForm_isRightAdEquivariant IG IB IP smoothBundle)
      U p hopen hp hopen.uniqueMDiffOn fields (by
        intro i
        fin_cases i
        · exact hfundamental
        · exact hadapted)
      0 X (by
        intro g i
        fin_cases i
        exact hadapted_right g)
  have hconstant (q : P) :
      groupLieAlgebraModelEquiv IG
        (connection.pointwise.form q (fun _ : Fin 1 => fundamental q)) =
      groupLieAlgebraModelEquiv IG X := by
    congr 1
    exact connection.vertical_normalization q X
  have hsecond :
      (NormedSpace.fromTangentSpace
        (groupLieAlgebraModelEquiv IG
          (connection.pointwise.form p (fun _ : Fin 1 => fundamental p)))
        (mfderivWithin IP (modelWithCornersSelf ℝ EG)
          (fun q => groupLieAlgebraModelEquiv IG
            (connection.pointwise.form q (fun _ : Fin 1 => fundamental q)))
          U p (adapted p))) = 0 := by
    rw [mfderivWithin_congr (fun q _ => hconstant q) (hconstant p), mfderivWithin_const]
    rfl
  have hbracket_zero :
      connection.pointwise.form p
        (fun _ : Fin 1 => VectorField.mlieBracketWithin IP fundamental adapted U p) = 0 := by
    rw [show VectorField.mlieBracketWithin IP fundamental adapted U p = 0 by
      exact hbracket 0]
    exact (connection.pointwise.form p).map_zero
  have hcartan := exterior.certificate.cartan_formula U p hopen hp hopen.uniqueMDiffOn
    fundamental adapted hfundamental hadapted
  simp only [toSmoothForm] at hcartan hdist
  unfold ManifoldDifferentialForm.oneFormCartanExpressionCoordinates at hcartan
  have hvector : ManifoldDifferentialForm.twoVectorArguments fundamental adapted p = vectors := by
    funext i
    fin_cases i
    · exact fundamentalSlot.symm
    · exact hadapted_value
  rw [hvector] at hcartan
  apply (groupLieAlgebraModelEquiv IG).injective
  rw [hcartan]
  rw [hsecond, hbracket_zero, map_zero, sub_zero]
  have hremove (q : P) :
      (fun i => Fin.removeNth 0 fields i q) = fun _ : Fin 1 => adapted q := by
    funext i
    fin_cases i
    rfl
  have hremove_p :
      connection.pointwise.form p (fun i => Fin.removeNth 0 fields i p) =
        connection.pointwise.form p (fun _ : Fin 1 => adapted p) := by
    rw [hremove p]
  have hremove_function :
      (fun q => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form q (fun i => Fin.removeNth 0 fields i q))) =
      fun q => groupLieAlgebraModelEquiv IG
        (connection.pointwise.form q (fun _ : Fin 1 => adapted q)) := by
    funext q
    rw [hremove q]
  rw [hremove_p, hremove_function] at hdist
  have hdist' :
      (NormedSpace.fromTangentSpace
        (groupLieAlgebraModelEquiv IG
          (connection.pointwise.form p (fun _ : Fin 1 => adapted p)))
        (mfderivWithin IP (modelWithCornersSelf ℝ EG)
          (fun q => groupLieAlgebraModelEquiv IG
            (connection.pointwise.form q (fun _ : Fin 1 => adapted q)))
          U p (fundamental p))) =
        -groupLieAlgebraModelEquiv IG
          ⁅X, connection.pointwise.form p (fun _ : Fin 1 => adapted p)⁆ := by
    rw [show fundamental p = principalFundamentalVector smoothBundle p X by rfl]
    exact hdist
  rw [hdist']
  simp only [map_neg]
  rw [hadapted_value]
  simp [ManifoldDifferentialForm.evalOne]

/-- The curvature is horizontal, derived from vertical generation and the exact half-self-wedge
normalization. -/
theorem curvatureForm_isHorizontal
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalTwoForm.IsHorizontal smoothBundle (connection.curvatureForm exterior).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  intro p vectors vertical
  obtain ⟨r, vertical_r⟩ := vertical
  fin_cases r
  · obtain ⟨X, fundamentalSlot⟩ := vertical_tangent_exists_fundamental
      (smoothBundle := smoothBundle) p (vectors 0) vertical_r
    rw [connection.curvatureForm_apply exterior]
    rw [connection.exteriorDerivative_apply_fundamental_first IG IB IP smoothBundle exterior
      p vectors X fundamentalSlot]
    rw [fundamentalSlot]
    change -⁅X, connection.pointwise.form.evalOne p (vectors 1)⁆ +
      ⁅connection.pointwise.form.evalOne p (principalFundamentalVector smoothBundle p X),
        connection.pointwise.form.evalOne p (vectors 1)⁆ = 0
    rw [connection.vertical_normalization]
    exact neg_add_cancel _
  · let swapped : Fin 2 → TangentSpace IP p := vectors ∘ Equiv.swap 0 1
    have swapped_zero : swapped 0 = vectors 1 := by rfl
    have swapped_vertical : mfderiv IP IB torsor.projection p (swapped 0) = 0 := by
      rw [swapped_zero]
      exact vertical_r
    obtain ⟨X, fundamentalSlot⟩ := vertical_tangent_exists_fundamental
      (smoothBundle := smoothBundle) p (swapped 0) swapped_vertical
    have hzero : (connection.curvatureForm exterior).toForm p swapped = 0 := by
      rw [connection.curvatureForm_apply exterior]
      rw [connection.exteriorDerivative_apply_fundamental_first IG IB IP smoothBundle exterior
        p swapped X fundamentalSlot]
      rw [fundamentalSlot]
      change -⁅X, connection.pointwise.form.evalOne p (swapped 1)⁆ +
        ⁅connection.pointwise.form.evalOne p (principalFundamentalVector smoothBundle p X),
          connection.pointwise.form.evalOne p (swapped 1)⁆ = 0
      rw [connection.vertical_normalization]
      exact neg_add_cancel _
    have hswap := ((connection.curvatureForm exterior).toForm p).map_swap vectors
      (show (0 : Fin 2) ≠ 1 by decide)
    change (connection.curvatureForm exterior).toForm p swapped =
      -(connection.curvatureForm exterior).toForm p vectors at hswap
    rw [hzero] at hswap
    simpa using hswap.symm

/-- The curvature is right-adjoint-equivariant with the unchanged factor `1/2`. -/
theorem curvatureForm_isRightAdEquivariant
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalTwoForm.IsRightAdEquivariant smoothBundle
      (connection.curvatureForm exterior).toForm := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  intro g p vectors
  rw [connection.curvatureForm_toForm exterior]
  change exterior.certificate.derivative.toForm (torsor.rightAction p g)
      (fun i => principalRightTranslationDifferential smoothBundle p g (vectors i)) +
      (1 / 2 : ℝ) •
        (connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form)
          (torsor.rightAction p g)
          (fun i => principalRightTranslationDifferential smoothBundle p g (vectors i)) = _
  rw [connection.exteriorDerivative_isRightAdEquivariant IG IB IP smoothBundle exterior g p vectors,
    connection.selfBracketWedge_isRightAdEquivariant IG IB IP smoothBundle g p vectors]
  change lieGroupAdjoint IG g⁻¹ (exterior.certificate.derivative.toForm p vectors) +
      (1 / 2 : ℝ) • lieGroupAdjoint IG g⁻¹
        ((connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form) p vectors) =
    lieGroupAdjoint IG g⁻¹
      (exterior.certificate.derivative.toForm p vectors + (1 / 2 : ℝ) •
        (connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form) p vectors)
  rw [map_add, map_smul]

/-- Automatic structural certificate for the exact curvature of every connection and same-index
exterior-derivative datum. -/
noncomputable def curvatureStructureCertificate_finiteDimensional
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) :
    PrincipalCurvatureStructureCertificate smoothBundle connection exterior where
  horizontal := connection.curvatureForm_isHorizontal IG IB IP smoothBundle exterior
  right_ad_equivariant :=
    connection.curvatureForm_isRightAdEquivariant IG IB IP smoothBundle exterior

end PrincipalConnectionData

end

end YangMills.Geometry
