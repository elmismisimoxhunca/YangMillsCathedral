/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Minkowski.PoincareComplexSL2Topology

/-!
# Hostile probes for the homogeneous matrix `SL(2, ℂ)` topology
-/

namespace YangMills
namespace Minkowski
namespace PoincareComplexSL2Topology
namespace Probes

/-- The concrete homogeneous carrier has the required topological-group structure. -/
example : IsTopologicalGroup ComplexSpecialLinearTwo := inferInstance

/-- The concrete homogeneous carrier is Hausdorff, so distinct signs cannot be topologically
collapsed. -/
example : T2Space ComplexSpecialLinearTwo := inferInstance

/-- The topology is induced by the exact matrix inclusion, not by a disconnected auxiliary map. -/
theorem exact_matrix_embedding :
    Topology.IsEmbedding
      (fun A : ComplexSpecialLinearTwo => (A : Matrix (Fin 2) (Fin 2) ℂ)) :=
  complexSpecialLinearTwo_coe_isEmbedding

/-- Exact group multiplication is continuous. -/
theorem exact_multiplication_continuous :
    Continuous (fun pair : ComplexSpecialLinearTwo × ComplexSpecialLinearTwo => pair.1 * pair.2) :=
  continuous_mul

/-- Exact group inversion is continuous. -/
theorem exact_inversion_continuous :
    Continuous (fun A : ComplexSpecialLinearTwo => A⁻¹) :=
  continuous_inv

/-- The exact matrix-sign subgroup remains central after installing the topology. -/
theorem exact_matrix_sign_center
    (signMatrix : complexSignSL2Subgroup) (A : ComplexSpecialLinearTwo) :
    signMatrix.1 * A = A * signMatrix.1 :=
  complexSignSL2Subgroup_central signMatrix A

/-- Hostile probe: Hausdorff topological structure does not collapse the exact negative sign. -/
theorem negative_sign_topologically_distinct :
    complexSignToSL2 negativeComplexSign ≠ 1 :=
  complexSignToSL2_negative_ne_one

end Probes
end PoincareComplexSL2Topology
end Minkowski
end YangMills
