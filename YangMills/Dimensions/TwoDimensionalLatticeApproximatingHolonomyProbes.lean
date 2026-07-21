/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingHolonomy

/-!
# Probes for exact approximating-edge holonomy words
-/

namespace YangMills.Dimensions.TwoDimensionalLatticeApproximatingHolonomy.Probes

open MeasureTheory

noncomputable section

universe uG uVertex uEdge uFace uXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell

/-- The word carrier cannot be empty and is tied to every certified node transition. -/
theorem exact_word_node_contract
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    {spacing : PositiveLatticeSpacing}
    {certificate : EpsilonSquareLatticePathCertificate curve spacing.1}
    (data : EpsilonSquareLatticePathBondWordData certificate) :
    data.bondWord ≠ [] ∧
      data.bondWord.length + 1 = certificate.nodes.length ∧
      data.bondWord.map EpsilonSquareLatticeDirectedBond.source =
        certificate.nodes.dropLast.map (fun node => node.2) ∧
      data.bondWord.map EpsilonSquareLatticeDirectedBond.target =
        certificate.nodes.tail.map (fun node => node.2) :=
  ⟨data.bondWord_nonempty, data.bondWord_length,
    data.bondWord_sources, data.bondWord_targets⟩

/-- Later traversal multiplies on the left after exact word concatenation. -/
theorem exact_append_order
    {G : Type uG} [Group G] {spacing : PositiveLatticeSpacing}
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (first second : List (EpsilonSquareLatticeDirectedBond spacing)) :
    epsilonSquareLatticeDirectedBondWordHolonomy configuration (first ++ second) =
      epsilonSquareLatticeDirectedBondWordHolonomy configuration second *
        epsilonSquareLatticeDirectedBondWordHolonomy configuration first :=
  epsilonSquareLatticeDirectedBondWordHolonomy.append configuration first second

/-- Every exact directed-bond word observable is measurable. -/
theorem exact_word_measurable
    {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {spacing : PositiveLatticeSpacing}
    (word : List (EpsilonSquareLatticeDirectedBond spacing)) :
    Measurable (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      epsilonSquareLatticeDirectedBondWordHolonomy configuration word) :=
  epsilonSquareLatticeDirectedBondWordHolonomy.measurable word

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq coarse.Edge]

omit [MeasurableMul₂ G] in
/-- Coarse restriction is literally fine word holonomy on the mapped edge. -/
theorem exact_coarse_restriction
    (data : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge, uFace, uXAxisCell,
      uFineVertex, uFineEdge, uFineFace, uFineXAxisCell} (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (edge : coarse.Edge) :
    data.coarseRestriction spacing configuration edge =
      epsilonSquareLatticeDirectedBondWordHolonomy configuration
        (data.fineEdgeBondWord spacing (data.edgeMap spacing edge)).bondWord :=
  rfl

/-- The complete coarse restriction map is measurable, preventing disconnected observable transport. -/
theorem exact_coarse_restriction_measurable
    (data : TwoDimensionalLatticeApproximatingHolonomyData.{uVertex, uEdge, uFace, uXAxisCell,
      uFineVertex, uFineEdge, uFineFace, uFineXAxisCell} (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing) :
    Measurable (data.coarseRestriction spacing) :=
  data.coarseRestriction_measurable spacing

/-- An empty proposed edge word is hostilely rejected. -/
theorem empty_edge_word_blocked
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    {spacing : PositiveLatticeSpacing}
    {certificate : EpsilonSquareLatticePathCertificate curve spacing.1}
    (data : EpsilonSquareLatticePathBondWordData certificate)
    (claimed : data.bondWord = []) : False :=
  data.bondWord_nonempty claimed

end

end YangMills.Dimensions.TwoDimensionalLatticeApproximatingHolonomy.Probes
