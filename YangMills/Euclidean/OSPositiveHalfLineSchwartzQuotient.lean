/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzPointEvaluation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The OS positive-half-line Schwartz quotient

OS-I, printed p. 86, defines `𝒮(ℝ₊)` as the quotient of `𝒮(ℝ)` by the closed subspace
`𝒮(ℝ₋)` of functions supported in the nonpositive half-line. This module constructs the exact
complex Schwartz submodule by vanishing on every positive point, proves that condition equivalent
to topological-support containment in `(-∞,0]`, proves the submodule closed using continuous point
evaluations, and forms the algebraic quotient with its genuine quotient topology.

A compactly supported bump centered at `1` proves the quotient nonzero. The quotient is Hausdorff,
but completeness, the source's Fréchet seminorm presentation, the spatial factor, completed
projective tensor product, iterated positive-half-space tensor powers, `(E2)`, and reconstruction
remain open.
-/

namespace YangMills

noncomputable section

/-- One-dimensional complex Schwartz space used in OS-I's half-line quotient. -/
abbrev OneDimensionalComplexSchwartzSpace := SchwartzMap ℝ ℂ

/-- Exact negative-half-line Schwartz submodule: every value at positive `x` vanishes. -/
def osNegativeHalfLineSchwartzSubmodule :
    Submodule ℂ OneDimensionalComplexSchwartzSpace where
  carrier := {f | ∀ x : ℝ, 0 < x → f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]

/-- Membership is exact pointwise vanishing on the positive half-line. -/
theorem mem_osNegativeHalfLineSchwartzSubmodule_iff
    (f : OneDimensionalComplexSchwartzSpace) :
    f ∈ osNegativeHalfLineSchwartzSubmodule ↔ ∀ x : ℝ, 0 < x → f x = 0 :=
  Iff.rfl

/-- Pointwise positive-half-line vanishing is equivalent to topological support contained in the
closed nonpositive half-line. -/
theorem mem_osNegativeHalfLineSchwartzSubmodule_iff_tsupport
    (f : OneDimensionalComplexSchwartzSpace) :
    f ∈ osNegativeHalfLineSchwartzSubmodule ↔ tsupport f ⊆ Set.Iic 0 := by
  rw [mem_osNegativeHalfLineSchwartzSubmodule_iff]
  constructor
  · intro h
    apply closure_minimal
    · intro x hx
      by_contra hnot
      have hpos : 0 < x := lt_of_not_ge hnot
      exact hx (h x hpos)
    · exact isClosed_Iic
  · intro h x hx
    by_contra hfx
    have hsupp : x ∈ Function.support f := hfx
    have htsupport : x ∈ tsupport f := subset_tsupport f hsupp
    exact (not_le_of_gt hx) (h htsupport)

/-- The negative-half-line Schwartz submodule is closed, as an intersection of kernels of exact
continuous point evaluations at all positive points. -/
theorem isClosed_osNegativeHalfLineSchwartzSubmodule :
    IsClosed (osNegativeHalfLineSchwartzSubmodule :
      Set OneDimensionalComplexSchwartzSpace) := by
  rw [show (osNegativeHalfLineSchwartzSubmodule :
      Set OneDimensionalComplexSchwartzSpace) =
    ⋂ x : ℝ, ⋂ (_h : 0 < x),
      (LinearMap.ker (SchwartzMap.pointEvaluationCLM (F := ℂ) x :
        OneDimensionalComplexSchwartzSpace →ₗ[ℝ] ℂ) :
          Set OneDimensionalComplexSchwartzSpace) by
    ext f
    simp [osNegativeHalfLineSchwartzSubmodule]]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact SchwartzMap.isClosed_pointEvaluationCLM_ker (F := ℂ) x

/-- OS-I's algebraic positive-half-line Schwartz quotient `𝒮(ℝ)/𝒮(ℝ₋)`. Mathlib equips this
quotient with the genuine quotient topology. -/
abbrev OSPositiveHalfLineSchwartzSpace :=
  OneDimensionalComplexSchwartzSpace ⧸ osNegativeHalfLineSchwartzSubmodule

/-- Canonical complex-linear quotient map. -/
def osPositiveHalfLineSchwartzQuotientMap :
    OneDimensionalComplexSchwartzSpace →ₗ[ℂ] OSPositiveHalfLineSchwartzSpace :=
  Submodule.mkQ osNegativeHalfLineSchwartzSubmodule

/-- The quotient map vanishes exactly on tests supported in the nonpositive half-line. -/
theorem osPositiveHalfLineSchwartzQuotientMap_eq_zero_iff
    (f : OneDimensionalComplexSchwartzSpace) :
    osPositiveHalfLineSchwartzQuotientMap f = 0 ↔ tsupport f ⊆ Set.Iic 0 := by
  change Submodule.Quotient.mk f = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero,
    mem_osNegativeHalfLineSchwartzSubmodule_iff_tsupport]

/-- The canonical map is a genuine quotient map for Mathlib's quotient topology. -/
theorem osPositiveHalfLineSchwartzQuotientMap_isQuotientMap :
    Topology.IsQuotientMap osPositiveHalfLineSchwartzQuotientMap :=
  osNegativeHalfLineSchwartzSubmodule.isQuotientMap_mkQ

/-- The canonical quotient map is continuous. -/
theorem continuous_osPositiveHalfLineSchwartzQuotientMap :
    Continuous osPositiveHalfLineSchwartzQuotientMap :=
  osNegativeHalfLineSchwartzSubmodule.continuous_mkQ

/-- The quotient map bundled continuously linearly. -/
def osPositiveHalfLineSchwartzQuotientCLM :
    OneDimensionalComplexSchwartzSpace →L[ℂ] OSPositiveHalfLineSchwartzSpace :=
  { osPositiveHalfLineSchwartzQuotientMap with
    cont := continuous_osPositiveHalfLineSchwartzQuotientMap }

/-- The closed quotient is regular, hence Hausdorff. -/
@[reducible]
noncomputable def osPositiveHalfLineSchwartzT3Space :
    T3Space OSPositiveHalfLineSchwartzSpace := by
  letI : IsClosed (osNegativeHalfLineSchwartzSubmodule :
      Set OneDimensionalComplexSchwartzSpace) :=
    isClosed_osNegativeHalfLineSchwartzSubmodule
  infer_instance

/-- Named Hausdorff structure on the positive-half-line quotient. -/
@[reducible]
noncomputable def osPositiveHalfLineSchwartzT2Space :
    T2Space OSPositiveHalfLineSchwartzSpace := by
  letI : T3Space OSPositiveHalfLineSchwartzSpace := osPositiveHalfLineSchwartzT3Space
  infer_instance

/-- Smooth compactly supported bump centered at positive point `1`. -/
noncomputable def osPositiveHalfLineBump : ContDiffBump (1 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Complex Schwartz function induced by the positive-half-line bump. -/
noncomputable def osPositiveHalfLineBumpSchwartz : OneDimensionalComplexSchwartzSpace := by
  let bump := osPositiveHalfLineBump
  let complexBump : ℝ → ℂ := Complex.ofRealCLM ∘ bump
  exact (bump.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)

/-- The positive bump takes value one at its center. -/
theorem osPositiveHalfLineBumpSchwartz_one : osPositiveHalfLineBumpSchwartz 1 = 1 := by
  unfold osPositiveHalfLineBumpSchwartz
  change Complex.ofRealCLM (osPositiveHalfLineBump 1) = 1
  rw [osPositiveHalfLineBump.one_of_mem_closedBall]
  · norm_num
  · exact Metric.mem_closedBall_self (le_of_lt osPositiveHalfLineBump.rIn_pos)

/-- The positive bump's topological support lies entirely in the closed positive half-line. -/
theorem osPositiveHalfLineBumpSchwartz_tsupport_subset :
    tsupport osPositiveHalfLineBumpSchwartz ⊆ Set.Ici 0 := by
  intro x hx
  have hsubset := tsupport_comp_subset
    (show Complex.ofRealCLM 0 = 0 by simp) osPositiveHalfLineBump
  have hxbump : x ∈ tsupport osPositiveHalfLineBump := hsubset hx
  rw [osPositiveHalfLineBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hxbump
  change |x - 1| ≤ (1 / 2 : ℝ) at hxbump
  have hlower := (abs_le.mp hxbump).1
  change 0 ≤ x
  linarith

/-- The positive bump does not belong to the negative-half-line submodule. -/
theorem osPositiveHalfLineBumpSchwartz_not_mem_negative :
    osPositiveHalfLineBumpSchwartz ∉ osNegativeHalfLineSchwartzSubmodule := by
  intro h
  have hz := h (1 : ℝ) (by norm_num)
  rw [osPositiveHalfLineBumpSchwartz_one] at hz
  norm_num at hz

/-- The positive bump gives an explicit nonzero quotient class. -/
theorem osPositiveHalfLineBumpQuotient_ne_zero :
    osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz ≠ 0 := by
  rw [Ne, osPositiveHalfLineSchwartzQuotientMap_eq_zero_iff]
  intro hsupp
  exact osPositiveHalfLineBumpSchwartz_not_mem_negative
    ((mem_osNegativeHalfLineSchwartzSubmodule_iff_tsupport
      osPositiveHalfLineBumpSchwartz).mpr hsupp)

end

end YangMills
