/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactHaarIntertwinerAverage

/-!
# Hostile probes for Haar intertwiner averaging
-/

namespace YangMills
namespace Mathematics
namespace CompactHaarIntertwinerAverage
namespace Probes

open MeasureTheory

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (A : Matrix (Fin m) (Fin n) ℂ)

omit [T2Space G] in
/-- The average retains both designated representations and the inverse on the target side. -/
theorem exact_average_coordinate (row : Fin m) (column : Fin n) :
    compactHaarIntertwinerAverage σ ρ A row column =
      ∫ g, (σ (g⁻¹) * A * ρ g) row column
        ∂normalizedCompactHaarMeasure G :=
  rfl

include hσ hρ in
/-- Every coordinate integral is genuine under the displayed continuity hypotheses. -/
theorem exact_coordinate_integrability (row : Fin m) (column : Fin n) :
    Integrable (fun g => (σ (g⁻¹) * A * ρ g) row column)
      (normalizedCompactHaarMeasure G) :=
  integrable_compactHaarIntertwinerAverage_integrand
    σ ρ hσ hρ A row column

include hσ hρ in
/-- The average satisfies the exact rectangular intertwining equation. -/
theorem exact_intertwiner (h : G) :
    σ h * compactHaarIntertwinerAverage σ ρ A =
      compactHaarIntertwinerAverage σ ρ A * ρ h :=
  compactHaarIntertwinerAverage_intertwines σ ρ hσ hρ A h

include hσ hρ in
/-- Any matrix definitionally identified with the average inherits the exact intertwining law. -/
theorem replacement_requires_intertwining
    (candidate : Matrix (Fin m) (Fin n) ℂ)
    (replacement : candidate = compactHaarIntertwinerAverage σ ρ A)
    (h : G) :
    σ h * candidate = candidate * ρ h := by
  rw [replacement]
  exact compactHaarIntertwinerAverage_intertwines σ ρ hσ hρ A h

omit [T2Space G] in
/-- Hostile probe: a replacement that changes even one exact averaged coordinate is impossible. -/
theorem changed_average_coordinate_blocked
    (candidate : Matrix (Fin m) (Fin n) ℂ)
    (replacement : candidate = compactHaarIntertwinerAverage σ ρ A)
    (row : Fin m) (column : Fin n)
    (changed : candidate row column ≠
      ∫ g, (σ (g⁻¹) * A * ρ g) row column
        ∂normalizedCompactHaarMeasure G) : False := by
  apply changed
  rw [replacement]
  rfl

end

end Probes
end CompactHaarIntertwinerAverage
end Mathematics
end YangMills
