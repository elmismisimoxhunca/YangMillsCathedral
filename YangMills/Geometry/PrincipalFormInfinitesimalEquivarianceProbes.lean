/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormInfinitesimalEquivariance

namespace YangMills.Geometry.PrincipalFormInfinitesimalEquivariance.Probes

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

/-- The distinguished coefficient has the exact negative infinitesimal-adjoint derivative. -/
theorem exact_distinguished_coefficient
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP Set.univ (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p)) :
    let Y := form.toForm p (fun i => (r.removeNth fields) i p)
    (NormedSpace.fromTangentSpace (groupLieAlgebraModelEquiv IG Y)
      (mfderiv IP (modelWithCornersSelf ℝ EG)
        (fun q => groupLieAlgebraModelEquiv IG
          (form.toForm q (fun i => (r.removeNth fields) i q))) p
        (principalFundamentalVector smoothBundle p X))) =
      -groupLieAlgebraModelEquiv IG ⁅X, Y⁆ :=
  PrincipalForm.distinguishedCoefficient_mfderiv_fundamental
    n form equivariant p fields fields_smooth r X adapted

/-- The exact remaining triangular bracket premise yields the required ordinary derivative value. -/
theorem exact_conditional_vertical_derivative
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
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
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆) :=
  PrincipalForm.exteriorDerivative_apply_fundamental_of_adaptedFields
    n form exterior horizontal equivariant p fields fields_smooth r X
    fundamental_field adapted bracketTerm_zero

/-- Changing the final derivative sign, parity, or carrier contradicts the exact Cartan reduction. -/
theorem changed_conditional_vertical_derivative_blocked
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (exterior : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG) n form)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form.toForm)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
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
          (j.removeNth <| i.castSucc.removeNth (fun k => fields k p)))) = 0)
    (changed : exterior.derivative.toForm p (fun i => fields i p) ≠
      -((-1 : ℤ) ^ (r : ℕ) •
        ⁅X, form.toForm p (r.removeNth (fun k => fields k p))⁆)) : False :=
  changed (PrincipalForm.exteriorDerivative_apply_fundamental_of_adaptedFields
    n form exterior horizontal equivariant p fields fields_smooth r X
    fundamental_field adapted bracketTerm_zero)

/-- Changing the distinguished coefficient sign contradicts infinitesimal equivariance. -/
theorem changed_distinguished_coefficient_blocked
    (n : ℕ)
    (form : SmoothManifoldDifferentialForm IP P (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) (n + 1))
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form.toForm)
    (p : P) (fields : Fin (n + 2) → (q : P) → TangentSpace IP q)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn IP Set.univ (fields i))
    (r : Fin (n + 2)) (X : GroupLieAlgebra IG G)
    (adapted : ∀ (g : G) (i : Fin (n + 1)),
      (r.removeNth fields) i (torsor.rightAction p g) =
        principalRightTranslationDifferential smoothBundle p g
          ((r.removeNth fields) i p))
    (changed : (let Y := form.toForm p (fun i => (r.removeNth fields) i p)
      (NormedSpace.fromTangentSpace (groupLieAlgebraModelEquiv IG Y)
        (mfderiv IP (modelWithCornersSelf ℝ EG)
          (fun q => groupLieAlgebraModelEquiv IG
            (form.toForm q (fun i => (r.removeNth fields) i q))) p
          (principalFundamentalVector smoothBundle p X))) ≠
        -groupLieAlgebraModelEquiv IG ⁅X, Y⁆)) : False :=
  changed (PrincipalForm.distinguishedCoefficient_mfderiv_fundamental
    n form equivariant p fields fields_smooth r X adapted)

end

end YangMills.Geometry.PrincipalFormInfinitesimalEquivariance.Probes
