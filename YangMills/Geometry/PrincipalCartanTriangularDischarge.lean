/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCommonAdaptedTotalFields
import YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin
import YangMills.Geometry.PrincipalFormCovariantExteriorVertical
import YangMills.Geometry.PrincipalVerticalTangentGeneration

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

namespace PrincipalForm

/-- The localized derivative formula with the triangular premise discharged by common-source
orbit-adapted fields and horizontality. -/
theorem exteriorDerivative_apply_fundamental_unconditional
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    exterior.derivative.toForm p vectors =
      -((-1 : ℤ) ^ (r : ℕ) •
        ⁅X, form.toForm p (r.removeNth vectors)⁆) := by
  obtain ⟨U, adaptedFields, hopen, hp, _horbit, hvalue, hsmooth, hright, hbracket⟩ :=
    exists_common_principalAdaptedTotalFields_arbitrary IG IB IP smoothBundle p X
      (r.removeNth vectors)
  let fundamental : (q : P) → TangentSpace IP q :=
    principalFundamentalVectorField (smoothBundle := smoothBundle) X
  let fields : Fin (n + 2) → (q : P) → TangentSpace IP q :=
    r.insertNth (fundamental) adaptedFields
  have fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP U (fields i) := by
    intro i
    by_cases hir : i = r
    · subst i
      simpa [fields, fundamental] using
        (principalFundamentalVectorField_isSmoothOn (smoothBundle := smoothBundle) X U)
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hir
      rw [← hz]
      simpa [fields] using hsmooth z
  have fundamental_field : ∀ q ∈ U,
      fields r q = principalFundamentalVectorField (smoothBundle := smoothBundle) X q := by
    intro q hq
    simp [fields, fundamental]
  have adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p) := by
    intro g i
    simpa [fields] using (hright i g).symm
  have bracketTerm_zero : ∀ (i j : Fin (n + 1)), j ∈ Finset.Ici i →
      groupLieAlgebraModelEquiv IG
        (form.toForm p (Matrix.vecCons
          (VectorField.mlieBracketWithin IP
            (fields i.castSucc) (fields j.succ) U p)
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0 := by
    intro i j hj
    have hij : i ≤ j := Finset.mem_Ici.mp hj
    have hab : i.castSucc < j.succ := Fin.castSucc_lt_succ_iff.mpr hij
    have hsucc : i.castSucc.succAbove j = j.succ :=
      Fin.succAbove_of_lt_succ i.castSucc j hab
    by_cases har : i.castSucc = r
    · have hfielda : fields i.castSucc = fundamental := by
        rw [har]
        simp [fields]
      have hfieldb : fields j.succ = adaptedFields j := by
        rw [← hsucc, har]
        simp [fields]
      have hbr : VectorField.mlieBracketWithin IP
          (fields i.castSucc) (fields j.succ) U p = 0 := by
        rw [hfielda, hfieldb]
        exact hbracket j
      rw [hbr]
      apply (form.toForm p).toContinuousMultilinearMap.map_coord_zero 0
      simp
    · by_cases hbr : j.succ = r
      · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq har
        have hzero : VectorField.mlieBracketWithin IP
            (fields i.castSucc) (fields j.succ) U p = 0 := by
          rw [hbr, ← hz]
          have hzfield : fields (r.succAbove z) = adaptedFields z := by simp [fields]
          rw [hzfield, VectorField.mlieBracketWithin_swap_apply]
          simp [fields, fundamental, hbracket z]
        rw [hzero]
        apply (form.toForm p).toContinuousMultilinearMap.map_coord_zero 0
        simp
      · have hform : form.toForm p (Matrix.vecCons
            (VectorField.mlieBracketWithin IP
              (fields i.castSucc) (fields j.succ) U p)
            (j.removeNth <| i.castSucc.removeNth (fun k => fields k p))) = 0 := by
          apply horizontal p
          obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq (Ne.symm har)
          have hyj : y ≠ j := by
            intro heq
            apply hbr
            rw [← hsucc, ← heq, hy]
          obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hyj
          refine ⟨z.succ, ?_⟩
          simp only [Matrix.cons_val_succ]
          rw [Fin.removeNth_apply, hz, Fin.removeNth_apply, hy,
            fundamental_field p hp]
          exact principalFundamentalVectorField_projection_eq_zero X p
        rw [hform, map_zero]
  have result := exteriorDerivative_apply_fundamental_of_adaptedFieldsWithin
    (smoothBundle := smoothBundle) n form exterior horizontal equivariant U p hopen hp
      hopen.uniqueMDiffOn fields fields_smooth r X fundamental_field adapted bracketTerm_zero
  have fields_at_p : (fun i => fields i p) = vectors := by
    funext i
    by_cases hir : i = r
    · subst i
      simp [fields, fundamental, principalFundamentalVectorField, fundamentalSlot]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hir
      rw [← hz]
      rw [show fields (r.succAbove z) = adaptedFields z by simp [fields]]
      rw [hvalue, Fin.removeNth_apply]
  rw [fields_at_p] at result
  simpa [fields_at_p] using result

/-- The covariant-exterior candidate vanishes whenever one designated slot is a principal
fundamental vector. The ordinary derivative and bracket correction cancel with the same sign. -/
theorem covariantExteriorCandidate_apply_fundamentalSlot_eq_zero_unconditional
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (vectors : Fin (n + 2) → TangentSpace IP p)
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (fundamentalSlot : vectors r = principalFundamentalVector smoothBundle p X) :
    (covariantExteriorCandidate connection n form exterior).toForm p vectors = 0 := by
  apply covariantExteriorCandidate_apply_fundamentalSlot_eq_zero connection n form exterior
    horizontal p vectors r X fundamentalSlot
  exact exteriorDerivative_apply_fundamental_unconditional IG IB IP smoothBundle n form exterior
    horizontal equivariant p vectors r X fundamentalSlot

/-- The positive-degree covariant-exterior candidate is horizontal, with no supplied vertical-slot
or triangular cancellation premise. Vertical tangent generation reduces an arbitrary vertical slot
to the unconditional principal-fundamental calculation above. -/
theorem covariantExteriorCandidate_isHorizontal_unconditional
    (connection : PrincipalConnectionData smoothBundle)
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : IsHorizontal smoothBundle form.toForm)
    (equivariant : IsRightAdEquivariant smoothBundle form.toForm) :
    IsHorizontal smoothBundle
      (covariantExteriorCandidate connection n form exterior).toForm := by
  intro p vectors vertical
  obtain ⟨r, vertical_r⟩ := vertical
  obtain ⟨X, fundamentalSlot⟩ := vertical_tangent_exists_fundamental
    (smoothBundle := smoothBundle) p (vectors r) vertical_r
  exact covariantExteriorCandidate_apply_fundamentalSlot_eq_zero_unconditional
    IG IB IP smoothBundle connection n form exterior horizontal equivariant p vectors r X
      fundamentalSlot

end PrincipalForm
end
end YangMills.Geometry
