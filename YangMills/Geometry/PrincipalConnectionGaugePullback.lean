/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PointwisePrincipalConnection
import YangMills.Geometry.SmoothGaugeTransformation

/-!
# Gauge pullback of principal connections

A smooth gauge automorphism pulls a principal connection form back by its exact manifold tangent
map. Vertical normalization, right equivariance, and smoothness are derived, producing another
connection on the same principal bundle. Identity and composition laws expose the contravariant
pullback order, equivalently a right action convention.

This module constructs the action on connections only. It does not yet transform an indexed
exterior-derivative certificate, prove curvature covariance, or infer active gauge invariance of the
Yang--Mills action or observables.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Pull a connection form back by the exact manifold derivative of a gauge automorphism. -/
def gaugePullbackForm
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    YangMills.Mathematics.ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 1 :=
  connection.pointwise.form.pullback gauge gauge.smooth

/-- Gauge pullback uses exactly `mfderiv` of the total-space automorphism. -/
theorem gaugePullbackForm_evalOne
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p) :
    (gaugePullbackForm gauge connection).evalOne p v =
      connection.pointwise.form.evalOne (gauge p) (mfderiv IP IP gauge p v) := by
  rfl

/-- Identity gauge transformation acts trivially on the pointwise connection form. -/
theorem gaugePullbackForm_one
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackForm (1 : SmoothGaugeTransformation smoothBundle) connection =
      connection.pointwise.form := by
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [gaugePullbackForm,
    YangMills.Mathematics.ManifoldDifferentialForm.pullback]
  have hfun : ((1 : SmoothGaugeTransformation smoothBundle) : P → P) = id := by
    funext x
    exact SmoothGaugeTransformation.identity_apply x
  rw [mfderiv_congr (I := IP) (I' := IP) (x := p) hfun,
    mfderiv_id]
  rfl

/-- Gauge multiplication acts by iterated pullback, in the action order induced by composition. -/
theorem gaugePullbackForm_mul
    (first second : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackForm (first * second) connection =
      YangMills.Mathematics.ManifoldDifferentialForm.pullback second second.smooth
        (gaugePullbackForm first connection) := by
  funext p
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [gaugePullbackForm,
    YangMills.Mathematics.ManifoldDifferentialForm.pullback]
  have hfun : ((first * second : SmoothGaugeTransformation smoothBundle) : P → P) =
      (first : P → P) ∘ (second : P → P) := by
    funext x
    exact SmoothGaugeTransformation.mul_apply first second x
  rw [mfderiv_congr (I := IP) (I' := IP) (x := p) hfun,
    mfderiv_comp p
      (first.smooth.mdifferentiableAt (by simp))
      (second.smooth.mdifferentiableAt (by simp))]
  rfl

/-- The exact gauge tangent map carries every fundamental vertical vector to the same
    infinitesimal generator at the transformed point. -/
theorem gauge_mfderiv_principalFundamentalVector
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P)
    (X : GroupLieAlgebra IG G) :
    mfderiv IP IP gauge p (principalFundamentalVector smoothBundle p X) =
      principalFundamentalVector smoothBundle (gauge p) X := by
  have hfun : (gauge : P → P) ∘ principalOrbitMap torsor p =
      principalOrbitMap torsor (gauge p) := by
    funext g
    exact gauge.rightAction_equivariant p g
  have hchain := mfderiv_comp (I := IG) (I' := IP) (I'' := IP)
    (f := principalOrbitMap torsor p) (g := gauge) 1
    (gauge.smooth.mdifferentiableAt (by simp))
    ((principalOrbitMap_smooth smoothBundle p).mdifferentiableAt (by simp))
  rw [mfderiv_congr (I := IG) (I' := IP) (x := (1 : G)) hfun] at hchain
  change mfderiv IG IP (principalOrbitMap torsor (gauge p)) 1 =
    (mfderiv IP IP gauge (torsor.rightAction p 1)).comp
      (mfderiv IG IP (principalOrbitMap torsor p) 1) at hchain
  rw [torsor.right_one p] at hchain
  change mfderiv IP IP gauge p (mfderiv IG IP (principalOrbitMap torsor p) 1 X) =
    mfderiv IG IP (principalOrbitMap torsor (gauge p)) 1 X
  exact (congrArg (fun L => L X) hchain).symm

/-- The gauge tangent map commutes exactly with every fixed right translation. -/
theorem gauge_mfderiv_principalRightTranslationDifferential
    (gauge : SmoothGaugeTransformation smoothBundle) (p : P) (g : G)
    (v : TangentSpace IP p) :
    mfderiv IP IP gauge (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g v) =
      principalRightTranslationDifferential smoothBundle (gauge p) g
        (mfderiv IP IP gauge p v) := by
  have hfun : (gauge : P → P) ∘ principalRightTranslation torsor g =
      principalRightTranslation torsor g ∘ (gauge : P → P) := by
    funext q
    exact gauge.rightAction_equivariant q g
  have hderiv := mfderiv_congr (I := IP) (I' := IP) (x := p) hfun
  rw [mfderiv_comp p
      (gauge.smooth.mdifferentiableAt (by simp))
      ((principalRightTranslation_smooth smoothBundle g).mdifferentiableAt (by simp)),
    mfderiv_comp p
      ((principalRightTranslation_smooth smoothBundle g).mdifferentiableAt (by simp))
      (gauge.smooth.mdifferentiableAt (by simp))] at hderiv
  exact congrArg (fun L => L v) hderiv

/-- Pointwise gauge pullback of a principal connection. Its two connection laws are consequences
rather than additional assumptions. -/
def gaugePullbackPointwiseConnection
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    PointwisePrincipalConnectionData smoothBundle where
  form := gaugePullbackForm gauge connection
  vertical_normalization := by
    intro p X
    rw [gaugePullbackForm_evalOne,
      gauge_mfderiv_principalFundamentalVector,
      connection.vertical_normalization]
  right_equivariant := by
    intro p g v
    rw [gaugePullbackForm_evalOne,
      gauge_mfderiv_principalRightTranslationDifferential,
      gauge.rightAction_equivariant,
      connection.right_equivariant,
      gaugePullbackForm_evalOne]

/-- Smoothness of the pulled-back form, proved by transporting test vector fields through the
    gauge diffeomorphism and its smooth inverse. -/
theorem gaugePullbackForm_isSmooth
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    (gaugePullbackForm gauge connection).IsSmooth
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG) := by
  intro s fields hfields
  let invGauge : P → P := gauge.toGauge.toEquiv.symm
  let targetFields : Fin 1 → (y : P) → TangentSpace IP y := fun i y =>
    mfderiv IP IP gauge (invGauge y) (fields i (invGauge y))
  have hinvSmooth : ContMDiff IP IP ∞ invGauge := gauge.inverse_smooth
  have hinvMaps : Set.MapsTo invGauge (gauge '' s) s := by
    rintro y ⟨x, hx, rfl⟩
    simpa [invGauge] using hx
  have htarget : ∀ i, ContMDiffOn IP (IP.prod (modelWithCornersSelf ℝ EP)) ∞
      (fun y => (⟨y, targetFields i y⟩ : TangentBundle IP P)) (gauge '' s) := by
    intro i
    have hsource : ContMDiffOn IP (IP.prod (modelWithCornersSelf ℝ EP)) ∞
        (fun y => (⟨invGauge y, fields i (invGauge y)⟩ : TangentBundle IP P))
        (gauge '' s) :=
      (hfields i).comp hinvSmooth.contMDiffOn hinvMaps
    have htangent : ContMDiff IP.tangent IP.tangent ∞ (tangentMap IP IP gauge) :=
      gauge.smooth.contMDiff_tangentMap (m := ∞) (by simp)
    have hcomposed := htangent.comp_contMDiffOn hsource
    apply hcomposed.congr
    intro y hy
    apply Bundle.TotalSpace.ext
    · exact (gauge.toGauge.toEquiv.apply_symm_apply y).symm
    · rfl
  have heval := connection.form_smooth (gauge '' s) targetFields htarget
  have hresult := heval.comp gauge.smooth.contMDiffOn (Set.mapsTo_image gauge s)
  apply hresult.congr
  intro x hx
  change (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
      (connection.pointwise.form (gauge x)
        (fun i => mfderiv IP IP gauge x (fields i x))) =
    (YangMills.Mathematics.groupLieAlgebraModelEquiv IG)
      (connection.pointwise.form (gauge x)
        (fun i => mfderiv IP IP gauge (invGauge (gauge x))
          (fields i (invGauge (gauge x)))))
  rw [show invGauge (gauge x) = x by
    exact gauge.toGauge.toEquiv.symm_apply_apply x]

/-- Gauge pullback of a smooth principal connection, with smoothness derived from the original. -/
def gaugePullbackConnection
    (gauge : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    PrincipalConnectionData smoothBundle where
  pointwise := gaugePullbackPointwiseConnection gauge connection
  form_smooth := gaugePullbackForm_isSmooth gauge connection

/-- Extensionality helper for the pointwise connection carrier. -/
theorem pointwisePrincipalConnection_ext_form
    {first second : PointwisePrincipalConnectionData smoothBundle}
    (h : first.form = second.form) : first = second := by
  cases first
  cases second
  cases h
  rfl

/-- Extensionality helper for the smooth connection carrier. -/
theorem principalConnection_ext_form
    {first second : PrincipalConnectionData smoothBundle}
    (h : first.pointwise.form = second.pointwise.form) : first = second := by
  have hp : first.pointwise = second.pointwise := pointwisePrincipalConnection_ext_form h
  cases first
  cases second
  cases hp
  rfl

/-- Pullback by the identity gauge transformation fixes every smooth connection. -/
theorem gaugePullbackConnection_one
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackConnection (1 : SmoothGaugeTransformation smoothBundle) connection =
      connection := by
  apply principalConnection_ext_form
  exact gaugePullbackForm_one connection

/-- Gauge pullback respects multiplication in contravariant pullback order.

Equivalently, taking the connection as the first argument would give a right gauge action. -/
theorem gaugePullbackConnection_mul
    (first second : SmoothGaugeTransformation smoothBundle)
    (connection : PrincipalConnectionData smoothBundle) :
    gaugePullbackConnection (first * second) connection =
      gaugePullbackConnection second (gaugePullbackConnection first connection) := by
  apply principalConnection_ext_form
  exact gaugePullbackForm_mul first second connection

end

end YangMills.Geometry
