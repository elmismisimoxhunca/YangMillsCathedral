/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionLocalAdjointCalculus
import YangMills.Geometry.PrincipalConnectionCoordinateExteriorNaturality
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates

/-!
# Exterior naturality for a designated local section

The exact certified principal exterior derivative pulled back by a designated local section is
proved equal to `extDerivWithin` of the exact local potential on `baseExtChartDomain`. The section is
only smooth on its principal-chart domain: the proof uses local `ContMDiffOn`, recenters at every
point, and preserves the fixed calculus set through a proved set-germ equality. It does not assert
global smoothness of the totalized section.
-/

namespace YangMills.Geometry

open Set Function Filter
open scoped Manifold ContDiff Bundle Topology
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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]

namespace PrincipalConnectionData

/-- Direct base-chart coordinate of the exact certified principal exterior derivative, using
exactly the local section and tangent transport used by `localPotentialInBaseExtChartAt`. -/
noncomputable def localExteriorDerivativeInBaseExtChartAt
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    NormedSpaceDifferentialForm EB EG 2 := fun x => by
  classical
  let q := (extChartAt IB b).symm x
  if hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b then
    exact (groupLieAlgebraModelEquiv IG).toContinuousLinearMap.compContinuousAlternatingMap
      ((exterior.certificate.derivative.toForm (principalBundleLocalSection chart q))
        |>.compContinuousLinearMap
          ((principalBundleLocalTangentLift (IB := IB) (IP := IP) chart q).comp
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x)))
  else exact 0

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
/-- On the exact overlap, the local derivative carrier is the certified principal derivative on the
same local section, tangent lifts, and corner-aware inverse-chart transport. -/
@[simp] theorem localExteriorDerivativeInBaseExtChartAt_apply
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin 2 → EB) :
    connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x vectors =
      groupLieAlgebraModelEquiv IG
        (exterior.certificate.derivative.toForm
          (principalBundleLocalSection chart ((extChartAt IB b).symm x))
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart
            ((extChartAt IB b).symm x)
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x (vectors i)))) := by
  simp only [localExteriorDerivativeInBaseExtChartAt, dif_pos hx]
  rfl

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
/-- Outside the exact overlap, the local derivative carrier is exactly zero. -/
@[simp] theorem localExteriorDerivativeInBaseExtChartAt_of_not_mem
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∉ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x = 0 := by
  simp [localExteriorDerivativeInBaseExtChartAt, hx]

omit [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP] in
set_option backward.isDefEq.respectTransparency false in
private lemma local_pullback_coordinate_eqOn
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : B → P) (u : Set B) (open_u : IsOpen u) (hf : ContMDiffOn IB IP ∞ f u)
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm IP P V k)
    (b : B) (p : P)
    (hp : ∀ q ∈ u, f q ∈ (extChartAt IP p).source) :
    let s : Set EB := (extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' u
    let g : EB → EP := extChartAt IP p ∘ f ∘ (extChartAt IB b).symm
    Set.EqOn
      (fun x => coordinates.toContinuousLinearMap.compContinuousAlternatingMap
        ((form (f ((extChartAt IB b).symm x))).compContinuousLinearMap
          ((mfderiv IB IP f ((extChartAt IB b).symm x)).comp
            (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
              (Set.range ⇑IB) x))))
      (fun x => ((form.inExtChartAt coordinates k p) (g x)).compContinuousLinearMap
        (fderivWithin ℝ g s x)) s := by
  dsimp only
  let s : Set EB := (extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' u
  let g : EB → EP := extChartAt IP p ∘ f ∘ (extChartAt IB b).symm
  intro x hx
  let q : B := (extChartAt IB b).symm x
  have hq_source : q ∈ (extChartAt IB b).source :=
    (extChartAt IB b).map_target hx.1
  have hq : (extChartAt IB b) q = x := (extChartAt IB b).right_inv hx.1
  have hq_u : q ∈ u := hx.2
  have hfq_source : f q ∈ (extChartAt IP p).source := hp q hq_u
  have hg : g x = (extChartAt IP p) (f q) := by rfl
  let sourceInv := mfderivWithin (modelWithCornersSelf ℝ EB) IB
    (extChartAt IB b).symm (Set.range ⇑IB) x
  let targetInv := mfderivWithin (modelWithCornersSelf ℝ EP) IP
    (extChartAt IP p).symm (Set.range ⇑IP) ((extChartAt IP p) (f q))
  let targetChartDeriv := mfderiv IP (modelWithCornersSelf ℝ EP)
    (extChartAt IP p) (f q)
  have unique_source_on : UniqueDiffOn ℝ s := by
    exact open_u.uniqueMDiffOn.uniqueDiffOn_target_inter (I := IB) b
  have unique_source : UniqueMDiffWithinAt (modelWithCornersSelf ℝ EB) s x :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt (unique_source_on x hx)
  have sourceInv_eq : mfderivWithin (modelWithCornersSelf ℝ EB) IB
      (extChartAt IB b).symm s x = sourceInv := by
    apply MDifferentiableWithinAt.mfderivWithin_mono
      (mdifferentiableWithinAt_extChartAt_symm hx.1) unique_source
    exact inter_subset_left.trans (extChartAt_target_subset_range b)
  have inner_deriv : mfderivWithin (modelWithCornersSelf ℝ EB) IP
      (f ∘ (extChartAt IB b).symm) s x =
      (mfderiv IB IP f q).comp sourceInv := by
    have h := mfderiv_comp_mfderivWithin_of_eq
      (I := modelWithCornersSelf ℝ EB) (I' := IB) (I'' := IP)
      (g := f) (f := (extChartAt IB b).symm) (s := s)
      (x := x) (y := q)
      ((hf q hq_u).contMDiffAt (open_u.mem_nhds hq_u) |>.mdifferentiableAt (by simp))
      ((mdifferentiableWithinAt_extChartAt_symm hx.1).mono
        (inter_subset_left.trans (extChartAt_target_subset_range b)))
      unique_source rfl
    rw [sourceInv_eq] at h
    exact h
  have inner_mdiff : MDifferentiableWithinAt (modelWithCornersSelf ℝ EB) IP
      (f ∘ (extChartAt IB b).symm) s x :=
    MDifferentiableWithinAt.comp_of_eq
      (I := modelWithCornersSelf ℝ EB) (I' := IB) (I'' := IP)
      (g := f) (f := (extChartAt IB b).symm) (u := Set.univ) (s := s)
      (x := x) (y := q)
      (((hf q hq_u).contMDiffAt (open_u.mem_nhds hq_u)).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      ((mdifferentiableWithinAt_extChartAt_symm hx.1).mono
        (inter_subset_left.trans (extChartAt_target_subset_range b)))
      (by simp) rfl
  have written_deriv : fderivWithin ℝ g s x =
      targetChartDeriv.comp ((mfderiv IB IP f q).comp sourceInv) := by
    rw [← mfderivWithin_eq_fderivWithin]
    have h := mfderiv_comp_mfderivWithin_of_eq
      (I := modelWithCornersSelf ℝ EB) (I' := IP)
      (I'' := modelWithCornersSelf ℝ EP)
      (g := extChartAt IP p) (f := f ∘ (extChartAt IB b).symm)
      (s := s) (x := x) (y := f q)
      (mdifferentiableAt_extChartAt (I := IP) (by simpa using hfq_source))
      inner_mdiff unique_source rfl
    rw [inner_deriv] at h
    exact h
  have cancel_target : targetInv.comp targetChartDeriv = ContinuousLinearMap.id ℝ EP := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := IP) (x := p) (y := (extChartAt IP p) (f q))
      ((extChartAt IP p).map_source hfq_source)
    rw [(extChartAt IP p).left_inv hfq_source] at hcomp
    exact hcomp
  apply ContinuousAlternatingMap.ext
  intro vectors
  simp only [ManifoldDifferentialForm.inExtChartAt_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [show (extChartAt IP p ∘ f ∘ (extChartAt IB b).symm) x =
    (extChartAt IP p) (f q) from rfl, (extChartAt IP p).left_inv hfq_source]
  change coordinates (form (f q) (fun i =>
      ((mfderiv IB IP f q).comp sourceInv) (vectors i))) =
    coordinates (form (f q) (fun i =>
      targetInv ((fderivWithin ℝ g s x) (vectors i))))
  congr 3
  funext i
  rw [written_deriv]
  change ((mfderiv IB IP f q).comp sourceInv) (vectors i) =
    (targetInv.comp targetChartDeriv) (((mfderiv IB IP f q).comp sourceInv) (vectors i))
  rw [cancel_target]
  rfl

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] in
/-- The certified principal exterior derivative pulled back by the designated local section is
exactly Mathlib's within-set exterior derivative of the local potential on the exact overlap. -/
theorem localExteriorDerivativeInBaseExtChartAt_eqOn_extDerivWithin
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) (b : B) :
    Set.EqOn
      (connection.localExteriorDerivativeInBaseExtChartAt exterior chart b)
      (extDerivWithin (connection.localPotentialInBaseExtChartAt chart b)
        (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b))
      (AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) := by
  intro x hx
  let q : B := (extChartAt IB b).symm x
  let p : P := principalBundleLocalSection chart q
  let u : Set B := chart.baseSet ∩
    (principalBundleLocalSection chart) ⁻¹' (extChartAt IP p).source
  let s : Set EB := (extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' u
  let g : EB → EP := extChartAt IP p ∘ principalBundleLocalSection chart ∘
    (extChartAt IB b).symm
  let target : Set EP := (extChartAt IP p).target
  have hq_chart : q ∈ chart.baseSet := hx.2
  have hp_source : p ∈ (extChartAt IP p).source := mem_extChartAt_source p
  have open_u : IsOpen u := by
    exact (principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem).continuousOn
      |>.isOpen_inter_preimage chart.isOpen_baseSet (isOpen_extChartAt_source p)
  have hq_u : q ∈ u := ⟨hq_chart, hp_source⟩
  have hx_s : x ∈ s := by
    exact ⟨hx.1, hq_u⟩
  have section_smooth_u : ContMDiffOn IB IP ∞ (principalBundleLocalSection chart) u :=
    (principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem).mono inter_subset_left
  have maps_section : ∀ y ∈ u,
      principalBundleLocalSection chart y ∈ (extChartAt IP p).source := fun y hy => hy.2
  have unique_s : UniqueDiffOn ℝ s := by
    exact open_u.uniqueMDiffOn.uniqueDiffOn_target_inter (I := IB) b
  have closure_s : x ∈ closure (interior s) := by
    have hqInterior : q ∈ interior u :=
      mem_interior_iff_mem_nhds.mpr (open_u.mem_nhds hq_u)
    have hqClosure : q ∈ closure (interior u) := subset_closure hqInterior
    have h := extChartAt_mem_closure_interior (I := IB) (x₀ := b)
      hqClosure ((extChartAt IB b).map_target hx.1)
    rw [(extChartAt IB b).right_inv hx.1] at h
    change x ∈ closure (interior
      ((extChartAt IB b).target ∩ (extChartAt IB b).symm ⁻¹' u))
    simpa only [inter_comm] using h
  have set_germ :
      AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b =ᶠ[𝓝 x] s := by
    let safeB : Set B := (principalBundleLocalSection chart) ⁻¹' (extChartAt IP p).source
    have safeB_mem : safeB ∈ 𝓝 q :=
      (principalBundleLocalSection_contMDiffAt smoothBundle chart chart_mem hq_chart).continuousAt
        |>.preimage_mem_nhds (extChartAt_source_mem_nhds p)
    have inverse_safe : (extChartAt IB b).symm ⁻¹' safeB ∈
        𝓝[(extChartAt IB b).target] x := by
      exact ((contMDiffOn_extChartAt_symm (n := ∞) b) x hx.1).continuousWithinAt
        |>.preimage_mem_nhdsWithin safeB_mem
    have domain_subset_target :
        AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b ⊆
          (extChartAt IB b).target := inter_subset_left
    have inverse_safe_domain : (extChartAt IB b).symm ⁻¹' safeB ∈
        𝓝[AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b] x := by
      apply Filter.Eventually.filter_mono (nhdsWithin_mono x domain_subset_target)
      exact inverse_safe
    let domain := AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b
    have ambient_event : (extChartAt IB b).symm ⁻¹' safeB ∪ domainᶜ ∈ 𝓝 x := by
      rw [← nhdsWithin_univ, ← union_compl_self domain, nhdsWithin_union]
      exact Filter.union_mem_sup inverse_safe_domain self_mem_nhdsWithin
    rw [eventuallyEq_set]
    filter_upwards [ambient_event] with y hy
    constructor
    · intro hyDomain
      have hySafe := hy.resolve_right (fun hnot => hnot hyDomain)
      exact ⟨hyDomain.1, hyDomain.2, hySafe⟩
    · intro hyS
      exact ⟨hyS.1, hyS.2.1⟩
  have base_inverse_smooth : ContMDiffOn (modelWithCornersSelf ℝ EB) IB ∞
      (extChartAt IB b).symm s :=
    (contMDiffOn_extChartAt_symm b).mono inter_subset_left
  have section_after_inverse_smooth : ContMDiffOn (modelWithCornersSelf ℝ EB) IP ∞
      (principalBundleLocalSection chart ∘ (extChartAt IB b).symm) s := by
    exact section_smooth_u.comp base_inverse_smooth (fun y hy => hy.2)
  have g_smooth : ContDiffWithinAt ℝ ∞ g s x := by
    have target_chart_smooth : ContMDiffOn IP (modelWithCornersSelf ℝ EP) ∞
        (extChartAt IP p) (extChartAt IP p).source := by
      simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := IP) (x := p))
    have hg : ContMDiffOn (modelWithCornersSelf ℝ EB) (modelWithCornersSelf ℝ EP) ∞ g s := by
      exact target_chart_smooth.comp section_after_inverse_smooth (fun y hy => hy.2.2)
    exact (hg x hx_s).contDiffWithinAt
  have maps_g : MapsTo g s target := by
    intro y hy
    exact (extChartAt IP p).map_source hy.2.2
  let omega := connection.pointwise.form.inExtChartAt (groupLieAlgebraModelEquiv IG) 1 p
  let writtenPotential : NormedSpaceDifferentialForm EB EG 1 := fun y =>
    (omega (g y)).compContinuousLinearMap (fderivWithin ℝ g s y)
  let writtenDerivative : NormedSpaceDifferentialForm EB EG 2 := fun y =>
    ((exterior.certificate.derivative.toForm.inExtChartAt
      (groupLieAlgebraModelEquiv IG) 2 p) (g y)).compContinuousLinearMap
        (fderivWithin ℝ g s y)
  have potential_coordinate := local_pullback_coordinate_eqOn
    (f := principalBundleLocalSection chart) u open_u section_smooth_u
    (groupLieAlgebraModelEquiv IG) 1 connection.pointwise.form b p maps_section
  have potential_eq : Set.EqOn
      (connection.localPotentialInBaseExtChartAt chart b) writtenPotential s := by
    intro y hy
    have hyDomain : y ∈ AdjointBundle.DifferentialForm.baseExtChartDomain
        (IB := IB) chart b := ⟨hy.1, hy.2.1⟩
    simpa [localPotentialInBaseExtChartAt, hyDomain, writtenPotential, omega, g, s, q, p, u,
      principalBundleLocalTangentLift] using (potential_coordinate hy)
  have derivative_coordinate := local_pullback_coordinate_eqOn
    (f := principalBundleLocalSection chart) u open_u section_smooth_u
    (groupLieAlgebraModelEquiv IG) 2 exterior.certificate.derivative.toForm b p maps_section
  have derivative_eq :
      connection.localExteriorDerivativeInBaseExtChartAt exterior chart b x =
        writtenDerivative x := by
    have evaluated := derivative_coordinate hx_s
    simpa [localExteriorDerivativeInBaseExtChartAt, hx, writtenDerivative, g, s, q, p, u,
      principalBundleLocalTangentLift, ContinuousLinearMap.comp_apply] using evaluated
  have target_form_diff : DifferentiableWithinAt ℝ omega target (g x) := by
    have h := SmoothManifoldDifferentialForm.inExtChartAt_contDiffWithinAt
      (groupLieAlgebraModelEquiv IG) connection.toSmoothForm p
    have gx : g x = (extChartAt IP p) p := by
      simp [g, p, q]
    rw [gx]
    exact h.differentiableWithinAt (by simp)
  have naturality : extDerivWithin writtenPotential s x =
      (extDerivWithin omega target (g x)).compContinuousLinearMap
        (fderivWithin ℝ g s x) := by
    exact extDerivWithin_pullback target_form_diff g_smooth
      (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
          WithTop.coe_le_coe.mpr le_top))
      unique_s closure_s hx_s maps_g
  have certified_target :
      exterior.certificate.derivative.toForm.inExtChartAt
          (groupLieAlgebraModelEquiv IG) 2 p ((extChartAt IP p) p) =
        extDerivWithin omega target ((extChartAt IP p) p) :=
    exterior.certificate.inExtChartAt_derivative_eq_extDerivWithin
      (groupLieAlgebraModelEquiv IG) connection.toSmoothForm p
  have gx : g x = (extChartAt IP p) p := by
    simp [g, p, q]
  rw [derivative_eq]
  rw [show writtenDerivative x =
      (extDerivWithin omega target (g x)).compContinuousLinearMap
        (fderivWithin ℝ g s x) by
    simp only [writtenDerivative]
    rw [gx, certified_target]]
  rw [← naturality]
  rw [← extDerivWithin_congr' potential_eq hx_s]
  exact extDerivWithin_congr_set_local
    (connection.localPotentialInBaseExtChartAt chart b) set_germ.symm

end PrincipalConnectionData
end
end YangMills.Geometry
