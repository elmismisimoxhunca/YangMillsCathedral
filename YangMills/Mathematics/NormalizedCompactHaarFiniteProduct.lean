/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeGaugeTransport
import YangMills.Mathematics.NormalizedCompactHaarMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite products of normalized compact Haar measure

For a finite edge index, this module constructs the exact product of one canonical normalized Haar
probability per stored edge coordinate. Coordinate evaluation has the original Haar marginal. The
target-left/source-right-inverse endpoint gauge action preserves each coordinate Haar law and hence
the full finite product.

Only one variable is integrated per underlying edge; reverse orientations remain derived by
inversion in `FiniteOrientedEdgeWord`. This is reusable finite measure theory and makes no planar,
face, Gibbs, continuum, or Yang--Mills claim.
-/

namespace YangMills.Mathematics

open MeasureTheory Set

universe uVertex uEdge uG

/-- Exact finite product of canonical normalized Haar probability, one factor per underlying edge. -/
noncomputable def normalizedCompactHaarFiniteProductMeasure
    (Edge : Type uEdge) [Fintype Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure (Edge → G) :=
  Measure.pi (fun _ : Edge => normalizedCompactHaarMeasure G)

/-- The finite product Haar reference is a probability measure. -/
theorem normalizedCompactHaarFiniteProductMeasure_univ
    (Edge : Type uEdge) [Fintype Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    normalizedCompactHaarFiniteProductMeasure Edge G Set.univ = 1 := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  simp [normalizedCompactHaarFiniteProductMeasure]

/-- Every stored edge coordinate has the unchanged canonical normalized Haar marginal. -/
theorem normalizedCompactHaarFiniteProductMeasure_map_eval
    (Edge : Type uEdge) [Fintype Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (edge : Edge) :
    Measure.map (Function.eval edge)
      (normalizedCompactHaarFiniteProductMeasure Edge G) =
        normalizedCompactHaarMeasure G := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  exact (measurePreserving_eval
    (fun _ : Edge => normalizedCompactHaarMeasure G) edge).map_eq

/-- One edge's exact endpoint gauge multiplication preserves normalized Haar probability. -/
theorem finiteEdgeGaugeCoordinate_measurePreserving
    {Vertex : Type uVertex} {Edge : Type uEdge}
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G) (edge : Edge) :
    MeasurePreserving
      (fun value : G =>
        gauge (edgeTarget edge) * value * (gauge (edgeSource edge))⁻¹)
      (normalizedCompactHaarMeasure G) (normalizedCompactHaarMeasure G) := by
  letI : Measure.IsMulLeftInvariant (normalizedCompactHaarMeasure G) :=
    (normalizedCompactHaarMeasure_isHaar G).toIsMulLeftInvariant
  letI : Measure.IsMulRightInvariant (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  simpa [Function.comp_def, mul_assoc] using
    (measurePreserving_mul_left
      (normalizedCompactHaarMeasure G) (gauge (edgeTarget edge))).comp
      (measurePreserving_mul_right
        (normalizedCompactHaarMeasure G) (gauge (edgeSource edge))⁻¹)

/-- Every finite vertex-gauge transformation preserves the exact product Haar reference. -/
theorem finiteEdgeGaugeAction_measurePreserving
    {Vertex : Type uVertex} (Edge : Type uEdge) [Fintype Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G) :
    MeasurePreserving
      (finiteEdgeGaugeAction edgeSource edgeTarget gauge)
      (normalizedCompactHaarFiniteProductMeasure Edge G)
      (normalizedCompactHaarFiniteProductMeasure Edge G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  change MeasurePreserving
    (fun configuration edge =>
      gauge (edgeTarget edge) * configuration edge * (gauge (edgeSource edge))⁻¹)
    (Measure.pi (fun _ : Edge => normalizedCompactHaarMeasure G))
    (Measure.pi (fun _ : Edge => normalizedCompactHaarMeasure G))
  exact measurePreserving_pi
    (fun _ : Edge => normalizedCompactHaarMeasure G)
    (fun _ : Edge => normalizedCompactHaarMeasure G)
    (finiteEdgeGaugeCoordinate_measurePreserving G edgeSource edgeTarget gauge)

/-- Declaration-level invariance of the exact finite product Haar reference. -/
theorem normalizedCompactHaarFiniteProductMeasure_gaugeInvariant
    {Vertex : Type uVertex} (Edge : Type uEdge) [Fintype Edge]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G) :
    Measure.map (finiteEdgeGaugeAction edgeSource edgeTarget gauge)
      (normalizedCompactHaarFiniteProductMeasure Edge G) =
        normalizedCompactHaarFiniteProductMeasure Edge G :=
  (finiteEdgeGaugeAction_measurePreserving
    Edge G edgeSource edgeTarget gauge).map_eq

end YangMills.Mathematics
