/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeApproximatingSequence
import YangMills.Dimensions.TwoDimensionalInfiniteSquareLatticeConfiguration

/-!
# Exact holonomy words for lattice-approximating edges

Definition 8.1 says every fine edge is a path in the directed square lattice. This module strengthens
the existing geometric path certificate with the exact ordered directed-bond word determined by its
nodes, then evaluates that word using Driver's later-on-the-left transport convention. This supplies
the non-disconnected observable transport needed by Theorems 8.5 and 8.10.
-/

namespace YangMills.Dimensions

open MeasureTheory

noncomputable section

universe uG uVertex uEdge uFace uXAxisCell
  uFineVertex uFineEdge uFineFace uFineXAxisCell

/-- Ordered directed square-lattice bonds matching every consecutive pair of certified path nodes. -/
structure EpsilonSquareLatticePathBondWordData
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    {spacing : PositiveLatticeSpacing}
    (certificate : EpsilonSquareLatticePathCertificate curve spacing.1) where
  bondWord : List (EpsilonSquareLatticeDirectedBond spacing)
  bondWord_length : bondWord.length + 1 = certificate.nodes.length
  bondWord_sources : bondWord.map EpsilonSquareLatticeDirectedBond.source =
    certificate.nodes.dropLast.map (fun node => node.2)
  bondWord_targets : bondWord.map EpsilonSquareLatticeDirectedBond.target =
    certificate.nodes.tail.map (fun node => node.2)

namespace EpsilonSquareLatticePathBondWordData

/-- Every certified edge word contains at least one actual directed bond. -/
theorem bondWord_nonempty
    {curve : ℝ → EuclideanDimension.two.Spacetime}
    {spacing : PositiveLatticeSpacing}
    {certificate : EpsilonSquareLatticePathCertificate curve spacing.1}
    (data : EpsilonSquareLatticePathBondWordData certificate) :
    data.bondWord ≠ [] := by
  intro empty
  have lengthOne : certificate.nodes.length = 1 := by
    simpa [empty] using data.bondWord_length.symm
  have two_le := certificate.two_le_nodes_length
  omega

end EpsilonSquareLatticePathBondWordData

/-- Holonomy of an ordered directed-bond word. Later traversed bonds multiply on the left. -/
def epsilonSquareLatticeDirectedBondWordHolonomy
    {G : Type uG} [Group G] {spacing : PositiveLatticeSpacing}
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    List (EpsilonSquareLatticeDirectedBond spacing) → G
  | [] => 1
  | bond :: remaining =>
      epsilonSquareLatticeDirectedBondWordHolonomy configuration remaining * configuration bond

namespace epsilonSquareLatticeDirectedBondWordHolonomy

variable {G : Type uG} [Group G] {spacing : PositiveLatticeSpacing}

@[simp]
theorem empty (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    epsilonSquareLatticeDirectedBondWordHolonomy configuration [] = 1 :=
  rfl

/-- Concatenating traversal words multiplies the later word holonomy on the left. -/
theorem append
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing)
    (first second : List (EpsilonSquareLatticeDirectedBond spacing)) :
    epsilonSquareLatticeDirectedBondWordHolonomy configuration (first ++ second) =
      epsilonSquareLatticeDirectedBondWordHolonomy configuration second *
        epsilonSquareLatticeDirectedBondWordHolonomy configuration first := by
  induction first with
  | nil => simp [epsilonSquareLatticeDirectedBondWordHolonomy]
  | cons bond remaining inductionHypothesis =>
      simp only [List.cons_append, epsilonSquareLatticeDirectedBondWordHolonomy]
      rw [inductionHypothesis]
      group

/-- Finite directed-bond word holonomy is measurable on the exact axial carrier. -/
theorem measurable
    [MeasurableSpace G] [MeasurableMul₂ G]
    (word : List (EpsilonSquareLatticeDirectedBond spacing)) :
    Measurable (fun configuration : EpsilonSquareLatticeAxialConfiguration G spacing =>
      epsilonSquareLatticeDirectedBondWordHolonomy configuration word) := by
  induction word with
  | nil => exact measurable_const
  | cons bond remaining inductionHypothesis =>
      exact inductionHypothesis.mul
        (EpsilonSquareLatticeAxialConfiguration.measurable_apply bond)

end epsilonSquareLatticeDirectedBondWordHolonomy

variable
    {G Gauge Sample Connection : Type*}
    [Group G] [MeasurableSpace G] [Group Gauge] [MeasurableSpace Sample]
    {base : TwoDimensionalGaugeFixedHolonomyMeasureData G Gauge Sample Connection}
    {coarse : TwoDimensionalEmbeddedPlanarGraphData.{uVertex, uEdge, uFace, uXAxisCell} base}
    [DecidableEq coarse.Edge]

/-- Definition 8.1 approximating sequence with exact ordered square-lattice bond words on every fine
edge. -/
structure TwoDimensionalLatticeApproximatingHolonomyData extends
    TwoDimensionalLatticeApproximatingSequenceData.{uVertex, uEdge, uFace, uXAxisCell,
      uFineVertex, uFineEdge, uFineFace, uFineXAxisCell} (base := base) (coarse := coarse) where
  fineEdgeBondWord : ∀ spacing edge,
    EpsilonSquareLatticePathBondWordData
      (toTwoDimensionalLatticeApproximatingSequenceData.fineEdge_latticePath spacing edge)

namespace TwoDimensionalLatticeApproximatingHolonomyData

variable [MeasurableMul₂ G]

/-- Evaluate every fine graph edge by its exact certified square-lattice bond word. -/
def fineConfiguration
    (data : TwoDimensionalLatticeApproximatingHolonomyData (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) :
    (data.fine spacing).Edge → G :=
  fun edge => epsilonSquareLatticeDirectedBondWordHolonomy configuration
    (data.fineEdgeBondWord spacing edge).bondWord

/-- Pull a lattice configuration back to the coarse edge carrier through Driver's exact edge map. -/
def coarseRestriction
    (data : TwoDimensionalLatticeApproximatingHolonomyData (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing)
    (configuration : EpsilonSquareLatticeAxialConfiguration G spacing) : coarse.Edge → G :=
  fun edge => data.fineConfiguration spacing configuration (data.edgeMap spacing edge)

/-- Fine edge configurations are measurable in every coordinate. -/
theorem fineConfiguration_measurable
    (data : TwoDimensionalLatticeApproximatingHolonomyData (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing) :
    Measurable (data.fineConfiguration spacing) := by
  apply measurable_pi_iff.mpr
  intro edge
  exact epsilonSquareLatticeDirectedBondWordHolonomy.measurable
    (data.fineEdgeBondWord spacing edge).bondWord

/-- The exact coarse restriction is measurable. -/
theorem coarseRestriction_measurable
    (data : TwoDimensionalLatticeApproximatingHolonomyData (base := base) (coarse := coarse))
    (spacing : PositiveLatticeSpacing) :
    Measurable (data.coarseRestriction spacing) := by
  apply measurable_pi_iff.mpr
  intro edge
  exact epsilonSquareLatticeDirectedBondWordHolonomy.measurable
    (data.fineEdgeBondWord spacing (data.edgeMap spacing edge)).bondWord

end TwoDimensionalLatticeApproximatingHolonomyData

end

end YangMills.Dimensions
