/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Algebra.Module.Rat

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/

@[expose] public section


variable {E : Type*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [ContinuousSMul Real E]
  {F : Type*} [AddCommGroup F] [Module Real F] [TopologicalSpace F] [ContinuousSMul Real F] [T2Space F]

/--
theorem `map_real_smul` / 定理 `map_real_smul`

English:
theorem map_real_smul
  statement: {G} [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf : Continuous f)
  proof: suffices (fun c : Real => f (c • x)) = fun c : Real => c • f x from congr_fun this c
  Rat.isDenseEmbedding_coe_real.dense.equalizer (by fun_prop)
    (continuous_id.smul continuous_const) (funext fun r => map_ratCast_smul f Real Real r x)

中文:
定理 map_real_smul
  结论: {G} [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf : Continuous f)
  证明: suffices (fun c : Real => f (c • x)) = fun c : Real => c • f x from congr_fun this c
  Rat.isDenseEmbedding_coe_real.dense.equalizer (by fun_prop)
    (continuous_id.smul continuous_const) (funext fun r => map_ratCast_smul f Real Real r x)

Depends on / 依赖: Rat.isDenseEmbedding_coe_real.dense.equalizer, congr_fun, continuous_const, continuous_id, continuous_id.smul, equalizer, fun_prop, isDenseEmbedding_coe_real, map_ratCast_smul
-/
theorem map_real_smul {G} [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf : Continuous f)
    (c : Real) (x : E) :
    f (c • x) = c • f x :=
  suffices (fun c : Real => f (c • x)) = fun c : Real => c • f x from congr_fun this c
  Rat.isDenseEmbedding_coe_real.dense.equalizer (by fun_prop)
    (continuous_id.smul continuous_const) (funext fun r => map_ratCast_smul f Real Real r x)

namespace AddMonoidHom

/--
Definition of `toRealLinearMap` / `toRealLinearMap` 的定义

English:
definition toRealLinearMap
  signature: (f : E ->+ F) (hf : Continuous f)
  body: ⟨{ toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩

@[simp]

中文:
定义 toRealLinearMap
  签名: (f : E ->+ F) (hf : Continuous f)
  定义体: ⟨{ toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩

@[simp]

Depends on / 依赖: f.map_add, map_add, map_real_smul, map_smul
-/
def toRealLinearMap (f : E ->+ F) (hf : Continuous f) : E ->L[Real] F :=
  ⟨{ toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩

@[simp]
/--
theorem `coe_toRealLinearMap` / 定理 `coe_toRealLinearMap`

English:
theorem coe_toRealLinearMap
  given: (f : E ->+ F) (hf : Continuous f)
  statement: ⇑(f.toRealLinearMap hf) = f
  proof: rfl

中文:
定理 coe_toRealLinearMap
  条件: (f : E ->+ F) (hf : Continuous f)
  结论: ⇑(f.to实数LinearMap hf) = f
  证明: rfl
-/
theorem coe_toRealLinearMap (f : E ->+ F) (hf : Continuous f) : ⇑(f.toRealLinearMap hf) = f :=
  rfl

end AddMonoidHom

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `AddEquiv.toRealLinearEquiv` / `AddEquiv.toRealLinearEquiv` 的定义

English:
definition AddEquiv.toRealLinearEquiv
  signature: (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm)
  body: { e, e.toAddMonoidHom.toRealLinearMap h₁ with }

中文:
定义 AddEquiv.toRealLinearEquiv
  签名: (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm)
  定义体: { e, e.toAddMonoidHom.toRealLinearMap h₁ with }

Depends on / 依赖: e.toAddMonoidHom.toRealLinearMap, toAddMonoidHom, toRealLinearMap
-/
def AddEquiv.toRealLinearEquiv (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    E ≃L[Real] F :=
  { e, e.toAddMonoidHom.toRealLinearMap h₁ with }

/-- A topological group carries at most one structure of a topological `ℝ`-module, so for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is both a topological
`ℝ`-module and a topological `A`-module, these structures agree. -/
instance (priority := 900) Real.isScalarTower [T2Space E] {A : Type*} [TopologicalSpace A] [Ring A]
    [Algebra Real A] [Module A E] [ContinuousSMul Real A] [ContinuousSMul A E] : IsScalarTower Real A E :=
  ⟨fun r x y => map_real_smul ((smulAddHom A E).flip y) (continuous_id.smul continuous_const) r x⟩
