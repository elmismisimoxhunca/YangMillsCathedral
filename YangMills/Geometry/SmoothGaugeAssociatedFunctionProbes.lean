/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.SmoothGaugeAssociatedFunction

/-!
# Hostile probes for smooth associated gauge functions
-/

namespace YangMills.Geometry.SmoothGaugeAssociatedFunction.Probes

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

/-- On the canonical local section the selected torsor value is the exact transformed second
coordinate. -/
theorem exact_localSection_secondCoordinate
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) :
    gauge.associatedGaugeFunction (principalBundleLocalSection chart b) =
      (chart.toPartialHomeomorph
        (gauge (principalBundleLocalSection chart b))).2 :=
  gauge.associatedGaugeFunction_localSection_eq_secondCoordinate chart hb

/-- The local-section restriction is smooth only on the exact designated base domain. -/
theorem exact_localSection_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn IB IG ∞
      (fun b => gauge.associatedGaugeFunction (principalBundleLocalSection chart b))
      chart.baseSet :=
  gauge.associatedGaugeFunction_localSection_contMDiffOn chart chart_mem

omit [IsTopologicalGroup G] in
/-- Every source point is reconstructed from the local section and exact second coordinate. -/
theorem exact_chart_reconstruction
    (chart : PrincipalBundleLocalTrivialization torsor)
    (p : P) (hp : p ∈ chart.toPartialHomeomorph.source) :
    torsor.rightAction
        (principalBundleLocalSection chart (torsor.projection p))
        (chart.toPartialHomeomorph p).2 = p :=
  principalBundleLocalSection_rightAction_chartSecond chart p hp

/-- The associated function has the exact chart conjugation formula. -/
theorem exact_chart_conjugation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (p : P) (hp : p ∈ chart.toPartialHomeomorph.source) :
    gauge.associatedGaugeFunction p =
      (chart.toPartialHomeomorph p).2⁻¹ *
        gauge.associatedGaugeFunction
          (principalBundleLocalSection chart (torsor.projection p)) *
        (chart.toPartialHomeomorph p).2 :=
  gauge.associatedGaugeFunction_eq_chartConjugation chart p hp

/-- Smoothness is first established on each exact chart source. -/
theorem exact_chartSource_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn IP IG ∞ gauge.associatedGaugeFunction
      chart.toPartialHomeomorph.source :=
  gauge.associatedGaugeFunction_contMDiffOn_chartSource chart chart_mem

/-- Atlas coverage derives global smoothness of the same uniquely selected function. -/
theorem exact_global_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle) :
    ContMDiff IP IG ∞ gauge.associatedGaugeFunction :=
  gauge.associatedGaugeFunction_contMDiff

/-- A mismatched local coordinate is incompatible with torsor uniqueness. -/
theorem mismatched_localSection_coordinate_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (wrong : gauge.associatedGaugeFunction (principalBundleLocalSection chart b) ≠
      (chart.toPartialHomeomorph
        (gauge (principalBundleLocalSection chart b))).2) : False :=
  wrong (gauge.associatedGaugeFunction_localSection_eq_secondCoordinate chart hb)

/-- The genuinely reversed chart conjugation is rejected whenever it differs from the exact
right-action orientation. -/
theorem reversed_chart_conjugation_blocked_when_distinct
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (orientations_differ :
      (chart.toPartialHomeomorph p).2⁻¹ *
          gauge.associatedGaugeFunction
            (principalBundleLocalSection chart (torsor.projection p)) *
          (chart.toPartialHomeomorph p).2 ≠
        (chart.toPartialHomeomorph p).2 *
          gauge.associatedGaugeFunction
            (principalBundleLocalSection chart (torsor.projection p)) *
          (chart.toPartialHomeomorph p).2⁻¹)
    (wrong : gauge.associatedGaugeFunction p =
      (chart.toPartialHomeomorph p).2 *
        gauge.associatedGaugeFunction
          (principalBundleLocalSection chart (torsor.projection p)) *
        (chart.toPartialHomeomorph p).2⁻¹) : False :=
  orientations_differ
    ((gauge.associatedGaugeFunction_eq_chartConjugation chart p hp).symm.trans wrong)

end

end YangMills.Geometry.SmoothGaugeAssociatedFunction.Probes
