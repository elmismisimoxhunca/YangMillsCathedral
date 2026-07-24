/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Extending generator convergence from a graph-dense core

This file proves a reusable functional-analytic closure lemma. Let `A` be a possibly unbounded
linear operator represented algebraically by a `LinearMap`, and let `Q i` be linear approximating
operators. If:

* a subset is dense for the graph norm `‖x‖ + ‖A x‖`;
* `Q i x → A x` on that subset; and
* the `Q i` are eventually bounded uniformly by the same graph norm,

then `Q i x → A x` everywhere.

The theorem deliberately keeps graph density, core convergence, and the eventual graph bound as
separate hypotheses. It does not assert that a particular differential operator is closable, that
finite characters form a graph core, or that heat difference quotients satisfy the required bound.
-/

namespace YangMills
namespace Mathematics

open Filter

noncomputable section

universe uK uD uX uI

variable {𝕜 : Type uK} [NormedField 𝕜]
  {D : Type uD} [AddCommGroup D] [Module 𝕜 D]
  {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {ι : Type uI} {l : Filter ι}

/-- Pointwise graph density for an operator `A : D → X` whose possibly unnormed algebraic domain is
represented in the ambient normed space by `J : D → X`. No injectivity is required. -/
def IsLinearMapDomainGraphDenseAt
    (J A : D →ₗ[𝕜] X) (core : Set D) (x : D) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ z ∈ core, ‖J x - J z‖ < δ ∧ ‖A x - A z‖ < δ

/-- Global graph density on a possibly proper algebraic operator domain. -/
def IsLinearMapDomainGraphDenseCore
    (J A : D →ₗ[𝕜] X) (core : Set D) : Prop :=
  ∀ x, IsLinearMapDomainGraphDenseAt J A core x

/-- Pointwise graph-density of `core` for an algebraic linear operator `A`. This epsilon form avoids
assuming that `A` is bounded or installing a separate graph-norm topology. -/
def IsLinearMapGraphDenseAt
    (A : X →ₗ[𝕜] X) (core : Set X) (x : X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ z ∈ core, ‖x - z‖ < δ ∧ ‖A x - A z‖ < δ

/-- A subset is a graph core for the present closure lemma when it is graph-dense at every point. -/
def IsLinearMapGraphDenseCore
    (A : X →ₗ[𝕜] X) (core : Set X) : Prop :=
  ∀ x, IsLinearMapGraphDenseAt A core x

/-- Convergence in a normed space gives an eventual pointwise norm bound. This elementary
lemma is useful for auditing the quantifier gap between convergence on each core vector and a single
operator bound uniform over the whole domain. -/
theorem eventually_norm_le_norm_add_one_of_tendsto
    {f : ι → X} {y : X} (hf : Tendsto f l (nhds y)) :
    ∀ᶠ i in l, ‖f i‖ ≤ ‖y‖ + 1 := by
  have hnorm : Tendsto (fun i => ‖f i‖) l (nhds ‖y‖) := tendsto_norm.comp hf
  have heventually := (Metric.tendsto_nhds.mp hnorm) 1 zero_lt_one
  filter_upwards [heventually] with i hi
  rw [Real.dist_eq] at hi
  linarith [le_abs_self (‖f i‖ - ‖y‖)]

/-- Generator convergence extends from a graph-dense subset of a possibly proper algebraic
domain. Neither the domain `D` nor its ambient map `J` is assumed complete, normed, or injective. -/
theorem tendsto_linearMapOnDomain_of_graphDenseAt_of_eventually_graphBound
    (J A : D →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set D)
    (C : ℝ) (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : D,
      ‖Q i (J z)‖ ≤ C * (‖J z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i (J z)) l (nhds (A z)))
    {x : D} (graphApprox : IsLinearMapDomainGraphDenseAt J A core x) :
    Tendsto (fun i => Q i (J x)) l (nhds (A x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (2 * C + 1))
  have hden : 0 < 4 * (2 * C + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨z, hzcore, hxz, hAxz⟩ := graphApprox δ hδ
  have coreEventually :=
    (Metric.tendsto_nhds.mp (coreGenerator z hzcore)) (ε / 2) (by positivity)
  filter_upwards [graphBound, coreEventually] with i hiBound hiCore
  rw [dist_eq_norm]
  have split : Q i (J x) - A x =
      Q i (J (x - z)) + (Q i (J z) - A z) + (A z - A x) := by
    simp only [map_sub]
    abel
  rw [split]
  calc
    ‖Q i (J (x - z)) + (Q i (J z) - A z) + (A z - A x)‖
        ≤ ‖Q i (J (x - z))‖ + ‖Q i (J z) - A z‖ + ‖A z - A x‖ :=
      norm_add₃_le
    _ < C * (2 * δ) + ε / 2 + δ := by
      have hQ := hiBound (x - z)
      have hJ : ‖J (x - z)‖ = ‖J x - J z‖ := by rw [map_sub]
      have hA : ‖A (x - z)‖ = ‖A x - A z‖ := by rw [map_sub]
      have hdiff : ‖J (x - z)‖ + ‖A (x - z)‖ < 2 * δ := by
        rw [hJ, hA]
        linarith
      have hQle : ‖Q i (J (x - z))‖ ≤ C * (2 * δ) :=
        hQ.trans (mul_le_mul_of_nonneg_left hdiff.le hC)
      have hrev : ‖A z - A x‖ = ‖A x - A z‖ := norm_sub_rev _ _
      rw [dist_eq_norm] at hiCore
      rw [hrev]
      linarith
    _ < ε := by
      have hquarter : C * (2 * δ) + δ = ε / 4 := by
        dsimp [δ]
        field_simp
      linarith [hquarter]

/-- Global proper-domain specialization of the graph-core closure theorem. -/
theorem tendsto_linearMapOnDomain_of_graphDenseCore_of_eventually_graphBound
    (J A : D →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set D)
    (C : ℝ) (hC : 0 ≤ C)
    (graphDense : IsLinearMapDomainGraphDenseCore J A core)
    (graphBound : ∀ᶠ i in l, ∀ z : D,
      ‖Q i (J z)‖ ≤ C * (‖J z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i (J z)) l (nhds (A z))) :
    ∀ x, Tendsto (fun i => Q i (J x)) l (nhds (A x)) := by
  intro x
  exact tendsto_linearMapOnDomain_of_graphDenseAt_of_eventually_graphBound
    J A Q core C hC graphBound coreGenerator (graphDense x)

/-- Generator convergence extends from a graph-dense core under an eventual uniform graph bound.
No continuity of `A` or of the algebraic maps `Q i` is assumed. -/
theorem tendsto_linearMap_of_graphDenseAt_of_eventually_graphBound
    (A : X →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set X)
    (C : ℝ) (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))
    {x : X} (graphApprox : IsLinearMapGraphDenseAt A core x) :
    Tendsto (fun i => Q i x) l (nhds (A x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / (4 * (2 * C + 1))
  have hden : 0 < 4 * (2 * C + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨z, hzcore, hxz, hAxz⟩ := graphApprox δ hδ
  have coreEventually :=
    (Metric.tendsto_nhds.mp (coreGenerator z hzcore)) (ε / 2) (by positivity)
  filter_upwards [graphBound, coreEventually] with i hiBound hiCore
  rw [dist_eq_norm]
  have split : Q i x - A x = Q i (x - z) + (Q i z - A z) + (A z - A x) := by
    simp only [map_sub]
    abel
  rw [split]
  calc
    ‖Q i (x - z) + (Q i z - A z) + (A z - A x)‖
        ≤ ‖Q i (x - z)‖ + ‖Q i z - A z‖ + ‖A z - A x‖ :=
      norm_add₃_le
    _ < C * (2 * δ) + ε / 2 + δ := by
      have hQ := hiBound (x - z)
      have hA : ‖A (x - z)‖ = ‖A x - A z‖ := by rw [map_sub]
      have hdiff : ‖x - z‖ + ‖A (x - z)‖ < 2 * δ := by
        rw [hA]
        linarith
      have hQle : ‖Q i (x - z)‖ ≤ C * (2 * δ) :=
        hQ.trans (mul_le_mul_of_nonneg_left hdiff.le hC)
      have hrev : ‖A z - A x‖ = ‖A x - A z‖ := norm_sub_rev _ _
      rw [dist_eq_norm] at hiCore
      rw [hrev]
      linarith
    _ < ε := by
      have hquarter : C * (2 * δ) + δ = ε / 4 := by
        dsimp [δ]
        field_simp
      linarith [hquarter]

/-- Global graph-core specialization of the pointwise closure theorem. -/
theorem tendsto_linearMap_of_graphDenseCore_of_eventually_graphBound
    (A : X →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set X)
    (C : ℝ) (hC : 0 ≤ C)
    (graphDense : IsLinearMapGraphDenseCore A core)
    (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z))) :
    ∀ x, Tendsto (fun i => Q i x) l (nhds (A x)) := by
  intro x
  exact tendsto_linearMap_of_graphDenseAt_of_eventually_graphBound A Q core C hC graphBound
    coreGenerator (graphDense x)

end

end Mathematics
end YangMills
