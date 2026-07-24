/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LieGroupRightInvariantScalarLaplacian
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Linear structure on smooth real Lie-group scalar functions

The existing `SmoothLieGroupScalarFunction` carrier stores an everywhere-smooth real-valued
function on a Lie group. This file equips that carrier with its pointwise real vector-space
structure and constructs the injective algebraic linear map into `C(G, ℝ)`.

This is domain infrastructure for later unbounded-generator arguments. It does not put a norm on the
smooth domain, prove continuity of a Laplacian, identify a graph core, or construct a heat generator.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

namespace SmoothLieGroupScalarFunction

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Smooth scalar functions are equal when their underlying functions are equal. -/
@[ext]
theorem ext {f h : SmoothLieGroupScalarFunction (E := E) (G := G)}
    (toFun_eq : f.toFun = h.toFun) : f = h := by
  cases f
  cases h
  cases toFun_eq
  rfl

end SmoothLieGroupScalarFunction

instance : Zero (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨SmoothLieGroupScalarFunction.const 0⟩

instance : Add (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun f h => ⟨fun g => f g + h g, f.contMDiff.add h.contMDiff⟩⟩

instance : Neg (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun f => ⟨fun g => -f g, f.contMDiff.neg⟩⟩

instance : Sub (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun f h => ⟨fun g => f g - h g, f.contMDiff.sub h.contMDiff⟩⟩

instance : SMul ℕ (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun n f => ⟨fun g => n • f g, by
    apply ((show ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞
      (fun _ : G => (n : ℝ)) from contMDiff_const).mul f.contMDiff).congr
    intro g
    simp only [Pi.mul_apply, nsmul_eq_mul]⟩⟩

instance : SMul ℤ (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun n f => ⟨fun g => n • f g, by
    apply ((show ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞
      (fun _ : G => (n : ℝ)) from contMDiff_const).mul f.contMDiff).congr
    intro g
    simp only [Pi.mul_apply, zsmul_eq_mul]⟩⟩

/-- Pointwise additive commutative group structure on smooth real scalar functions. -/
instance : AddCommGroup (SmoothLieGroupScalarFunction (E := E) (G := G)) := by
  apply Function.Injective.addCommGroup (fun f => f.toFun)
    (fun _ _ equality => SmoothLieGroupScalarFunction.ext equality)
  all_goals intros
  all_goals rfl

instance : SMul ℝ (SmoothLieGroupScalarFunction (E := E) (G := G)) :=
  ⟨fun c f => ⟨fun g => c * f g,
    (show ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞
      (fun _ : G => c) from contMDiff_const).mul f.contMDiff⟩⟩

/-- Underlying-function additive homomorphism. -/
def smoothLieGroupScalarToFunctionAddHom :
    SmoothLieGroupScalarFunction (E := E) (G := G) →+ (G → ℝ) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Pointwise real module structure on smooth real scalar functions. -/
instance : Module ℝ (SmoothLieGroupScalarFunction (E := E) (G := G)) := by
  apply Function.Injective.module ℝ smoothLieGroupScalarToFunctionAddHom
    (fun _ _ equality => SmoothLieGroupScalarFunction.ext equality)
  intro c f
  ext g
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.zero_apply (g : G) :
    (0 : SmoothLieGroupScalarFunction (E := E) (G := G)) g = 0 :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.add_apply
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (f + h) g = f g + h g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.neg_apply
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (-f) g = -f g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.sub_apply
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (f - h) g = f g - h g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.nsmul_apply
    (n : ℕ) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (n • f) g = n • f g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.zsmul_apply
    (n : ℤ) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (n • f) g = n • f g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem SmoothLieGroupScalarFunction.smul_apply
    (c : ℝ) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    (c • f) g = c * f g :=
  rfl

/-- Algebraic linear inclusion of smooth scalar functions into continuous scalar functions. -/
noncomputable def smoothLieGroupScalarToContinuousLinearMap :
    SmoothLieGroupScalarFunction (E := E) (G := G) →ₗ[ℝ] C(G, ℝ) where
  toFun f := ⟨f, f.contMDiff.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothLieGroupScalarToContinuousLinearMap_apply
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    smoothLieGroupScalarToContinuousLinearMap f g = f g :=
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The smooth-to-continuous linear map is faithful. -/
theorem smoothLieGroupScalarToContinuousLinearMap_injective :
    Function.Injective
      (smoothLieGroupScalarToContinuousLinearMap (E := E) (G := G)) := by
  intro f h equality
  apply SmoothLieGroupScalarFunction.ext
  funext g
  exact congrArg (fun k : C(G, ℝ) => k g) equality

end

end Mathematics
end YangMills
