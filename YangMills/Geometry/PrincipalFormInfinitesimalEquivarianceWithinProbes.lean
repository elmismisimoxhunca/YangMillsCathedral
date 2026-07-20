/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin

namespace YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin.Probes

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

/-- The exact local Cartan reduction retains the chosen open calculus set. -/
theorem exact_local_conditional_vertical_derivative
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
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
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) :=
  PrincipalForm.exteriorDerivative_apply_fundamental_of_adaptedFieldsWithin
    n form exterior horizontal equivariant s p open_s hp unique_s fields fields_smooth r X
    fundamental_field adapted bracketTerm_zero

/-- Changing the localized derivative conclusion contradicts the exact within-set reduction. -/
theorem changed_local_vertical_derivative_blocked
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
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
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0)
    (changed : exterior.derivative.toForm p (fun i => fields i p) ≠
      -((-1 : ℤ) ^ (r : ℕ) •
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆)) : False :=
  changed (PrincipalForm.exteriorDerivative_apply_fundamental_of_adaptedFieldsWithin
    n form exterior horizontal equivariant s p open_s hp unique_s fields fields_smooth r X
    fundamental_field adapted bracketTerm_zero)

end

end YangMills.Geometry.PrincipalFormInfinitesimalEquivarianceWithin.Probes
