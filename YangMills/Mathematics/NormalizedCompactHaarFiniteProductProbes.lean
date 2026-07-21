/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct

/-!
# Probes for finite normalized-Haar products

The probes pin probability normalization, unchanged edge marginals, the exact endpoint action, and
full product-measure invariance. Reverse orientations do not receive independent factors.
-/

namespace YangMills.Mathematics.NormalizedCompactHaarFiniteProduct.Probes

open MeasureTheory

universe uVertex uEdge uG

variable
    {Vertex : Type uVertex} {Edge : Type uEdge} [Fintype Edge]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The exact finite product is normalized. -/
theorem exact_probability :
    normalizedCompactHaarFiniteProductMeasure Edge G Set.univ = 1 :=
  normalizedCompactHaarFiniteProductMeasure_univ Edge G

/-- Every underlying edge has exactly the canonical normalized Haar marginal. -/
theorem exact_edge_marginal (edge : Edge) :
    Measure.map (Function.eval edge)
      (normalizedCompactHaarFiniteProductMeasure Edge G) =
        normalizedCompactHaarMeasure G :=
  normalizedCompactHaarFiniteProductMeasure_map_eval Edge G edge

/-- The exact target-left/source-right-inverse action preserves the finite product. -/
theorem exact_gauge_invariance
    (edgeSource edgeTarget : Edge → Vertex) (gauge : Vertex → G) :
    Measure.map (finiteEdgeGaugeAction edgeSource edgeTarget gauge)
      (normalizedCompactHaarFiniteProductMeasure Edge G) =
        normalizedCompactHaarFiniteProductMeasure Edge G :=
  normalizedCompactHaarFiniteProductMeasure_gaugeInvariant
    Edge G edgeSource edgeTarget gauge

/-- A disconnected replacement measure is rejected by any differing exact edge marginal. -/
theorem unrelated_measure_blocked
    (wrong : Measure (Edge → G)) (edge : Edge)
    (different : Measure.map (Function.eval edge) wrong ≠ normalizedCompactHaarMeasure G)
    (claimed : wrong = normalizedCompactHaarFiniteProductMeasure Edge G) : False := by
  apply different
  rw [claimed]
  exact normalizedCompactHaarFiniteProductMeasure_map_eval Edge G edge

end YangMills.Mathematics.NormalizedCompactHaarFiniteProduct.Probes
