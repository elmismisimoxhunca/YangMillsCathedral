/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureLocalGaugeAdjoint
import YangMills.Geometry.PrincipalBundleLocalTangentLift

/-!
# Smoothness of the associated gauge function

The noncomputably selected torsor function `g_ϕ` is identified with explicit smooth principal-chart
coordinates. Its restriction to every canonical local section is the second coordinate of the
transformed section. Every chart point is reconstructed from that section and its second coordinate,
so the conjugation law yields smoothness on the whole chart source. Atlas coverage then proves
global `C∞` regularity.

This derives smoothness of the unique selected function; it does not yet construct its pulled
Maurer--Cartan form or prove the affine connection transformation formula.
-/

namespace YangMills.Geometry

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- On a designated principal chart, the associated gauge function at the canonical local section
is exactly the second chart coordinate of the transformed section. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_localSection_eq_secondCoordinate
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    gauge.associatedGaugeFunction (principalBundleLocalSection chart b) =
      (chart.toPartialHomeomorph
        (gauge (principalBundleLocalSection chart b))).2 := by
  apply gauge.associatedGaugeFunction_eq_of_rightAction
  let p := principalBundleLocalSection chart b
  let k := (chart.toPartialHomeomorph (gauge p)).2
  have hp : p ∈ chart.toPartialHomeomorph.source := by
    rw [chart.source_eq]
    change torsor.projection (principalBundleLocalSection chart b) ∈ chart.baseSet
    rw [principalBundleLocalSection_projection chart hb]
    exact hb
  have hgp : gauge p ∈ chart.toPartialHomeomorph.source := by
    rw [chart.source_eq]
    change torsor.projection (gauge p) ∈ chart.baseSet
    rw [gauge.preserves_projection, principalBundleLocalSection_projection chart hb]
    exact hb
  have hright := chart.rightAction_coordinate p hp k
  have hp_coordinate : chart.toPartialHomeomorph p = (b, (1 : G)) :=
    chart.toPartialHomeomorph.right_inv
      (principalBundleLocalSection_pair_mem_target chart hb)
  have hgp_coordinate : chart.toPartialHomeomorph (gauge p) = (b, k) := by
    apply Prod.ext
    · rw [chart.base_coordinate _ hgp, gauge.preserves_projection,
        principalBundleLocalSection_projection chart hb]
    · rfl
  apply chart.toPartialHomeomorph.injOn hgp (chart.rightAction_mem_source hp k)
  rw [hright, hp_coordinate, one_mul, hgp_coordinate]

/-- The associated gauge function restricted to a canonical local section is smooth on the exact
base domain of every designated atlas chart. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_localSection_contMDiffOn
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn IB IG ∞
      (fun b => gauge.associatedGaugeFunction (principalBundleLocalSection chart b))
      chart.baseSet := by
  have sectionSmooth :=
    principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem
  have gaugeSectionSmooth : ContMDiffOn IB IP ∞
      (fun b => gauge (principalBundleLocalSection chart b)) chart.baseSet := by
    simpa [Function.comp_def] using gauge.smooth.comp_contMDiffOn sectionSmooth
  have gaugeSectionMaps : Set.MapsTo
      (fun b => gauge (principalBundleLocalSection chart b)) chart.baseSet
      chart.toPartialHomeomorph.source := by
    intro b hb
    rw [chart.source_eq]
    change torsor.projection (gauge (principalBundleLocalSection chart b)) ∈ chart.baseSet
    rw [gauge.preserves_projection, principalBundleLocalSection_projection chart hb]
    exact hb
  have coordinateSmooth : ContMDiffOn IB IG ∞
      (fun b => (chart.toPartialHomeomorph
        (gauge (principalBundleLocalSection chart b))).2) chart.baseSet := by
    have chartGaugeSmooth :=
      (smoothBundle.trivialization_smooth chart chart_mem).comp
        gaugeSectionSmooth gaugeSectionMaps
    simpa [Function.comp_def] using contMDiff_snd.comp_contMDiffOn chartGaugeSmooth
  exact coordinateSmooth.congr fun b hb =>
    gauge.associatedGaugeFunction_localSection_eq_secondCoordinate chart hb


omit [IsTopologicalGroup G] in
/-- Every point in a principal chart is the canonical local section at its base point right-
translated by its exact second chart coordinate. -/
theorem principalBundleLocalSection_rightAction_chartSecond
    (chart : PrincipalBundleLocalTrivialization torsor)
    (p : P) (hp : p ∈ chart.toPartialHomeomorph.source) :
    torsor.rightAction
        (principalBundleLocalSection chart (torsor.projection p))
        (chart.toPartialHomeomorph p).2 = p := by
  have hb : torsor.projection p ∈ chart.baseSet := by
    simpa [chart.source_eq] using hp
  have hsection : principalBundleLocalSection chart (torsor.projection p) ∈
      chart.toPartialHomeomorph.source := by
    rw [chart.source_eq]
    change torsor.projection (principalBundleLocalSection chart (torsor.projection p)) ∈
      chart.baseSet
    rw [principalBundleLocalSection_projection chart hb]
    exact hb
  apply chart.toPartialHomeomorph.injOn (chart.rightAction_mem_source hsection _) hp
  rw [chart.rightAction_coordinate _ hsection]
  have sectionCoordinate :
      chart.toPartialHomeomorph (principalBundleLocalSection chart (torsor.projection p)) =
        (torsor.projection p, (1 : G)) :=
    chart.toPartialHomeomorph.right_inv
      (principalBundleLocalSection_pair_mem_target chart hb)
  rw [sectionCoordinate, one_mul]
  apply Prod.ext
  · exact (chart.base_coordinate p hp).symm
  · rfl

/-- In one designated source chart, the associated gauge function is conjugation of its local-
section restriction by the exact second principal coordinate. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_eq_chartConjugation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (p : P) (hp : p ∈ chart.toPartialHomeomorph.source) :
    gauge.associatedGaugeFunction p =
      (chart.toPartialHomeomorph p).2⁻¹ *
        gauge.associatedGaugeFunction
          (principalBundleLocalSection chart (torsor.projection p)) *
        (chart.toPartialHomeomorph p).2 := by
  let localSection := principalBundleLocalSection chart (torsor.projection p)
  let h := (chart.toPartialHomeomorph p).2
  have hpresentation : torsor.rightAction localSection h = p :=
    principalBundleLocalSection_rightAction_chartSecond chart p hp
  calc
    gauge.associatedGaugeFunction p =
        gauge.associatedGaugeFunction (torsor.rightAction localSection h) :=
      congrArg gauge.associatedGaugeFunction hpresentation.symm
    _ = h⁻¹ * gauge.associatedGaugeFunction localSection * h :=
      gauge.associatedGaugeFunction_rightAction localSection h
    _ = (chart.toPartialHomeomorph p).2⁻¹ *
        gauge.associatedGaugeFunction
          (principalBundleLocalSection chart (torsor.projection p)) *
        (chart.toPartialHomeomorph p).2 := rfl

/-- The canonical associated gauge function is smooth throughout every designated principal-chart
source. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_contMDiffOn_chartSource
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn IP IG ∞ gauge.associatedGaugeFunction
      chart.toPartialHomeomorph.source := by
  let coordinate := chart.toPartialHomeomorph
  let base : P → B := fun p => (coordinate p).1
  let fiber : P → G := fun p => (coordinate p).2
  let localGauge : B → G := fun b =>
    gauge.associatedGaugeFunction (principalBundleLocalSection chart b)
  have hcoordinate : ContMDiffOn IP (IB.prod IG) ∞ coordinate coordinate.source :=
    smoothBundle.trivialization_smooth chart chart_mem
  have hbase : ContMDiffOn IP IB ∞ base coordinate.source := by
    simpa [base, Function.comp_def] using contMDiff_fst.comp_contMDiffOn hcoordinate
  have hfiber : ContMDiffOn IP IG ∞ fiber coordinate.source := by
    simpa [fiber, Function.comp_def] using contMDiff_snd.comp_contMDiffOn hcoordinate
  have hbaseMaps : Set.MapsTo base coordinate.source chart.baseSet := by
    intro p hp
    change (coordinate p).1 ∈ chart.baseSet
    rw [chart.base_coordinate p hp]
    change p ∈ torsor.projection ⁻¹' chart.baseSet
    rw [← chart.source_eq]
    exact hp
  have hlocal : ContMDiffOn IB IG ∞ localGauge chart.baseSet := by
    simpa [localGauge] using
      gauge.associatedGaugeFunction_localSection_contMDiffOn chart chart_mem
  have hlocalComp : ContMDiffOn IP IG ∞ (fun p => localGauge (base p)) coordinate.source :=
    hlocal.comp hbase hbaseMaps
  have hcand : ContMDiffOn IP IG ∞
      (fun p => (fiber p)⁻¹ * localGauge (base p) * fiber p) coordinate.source :=
    (hfiber.inv.mul hlocalComp).mul hfiber
  apply hcand.congr
  intro p hp
  rw [gauge.associatedGaugeFunction_eq_chartConjugation chart p hp]
  congr 2
  unfold localGauge base
  rw [chart.base_coordinate p hp]

/-- The associated gauge function is globally smooth, derived from designated chart-source
smoothness and atlas coverage. -/
theorem SmoothGaugeTransformation.associatedGaugeFunction_contMDiff
    (gauge : SmoothGaugeTransformation smoothBundle) :
    ContMDiff IP IG ∞ gauge.associatedGaugeFunction := by
  intro p
  obtain ⟨chart, chart_mem, hp⟩ := bundle.exists_atlas_trivialization_mem_source p
  have hon := gauge.associatedGaugeFunction_contMDiffOn_chartSource chart chart_mem
  exact (hon p hp).contMDiffAt
    (chart.toPartialHomeomorph.open_source.mem_nhds hp)

end

end YangMills.Geometry
