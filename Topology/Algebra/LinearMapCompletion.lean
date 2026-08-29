/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Completion of continuous (semi-)linear maps:

This file has a declaration that enables a continuous (semi-)linear map between modules to be
lifted to a continuous semilinear map between the completions of those modules.

## Main declarations:

* `ContinuousLinearMap.completion`: promotes a continuous semilinear map
  from `α` to `β` to a continuous semilinear map from `Completion α` to `Completion β`.
* `ContinuousLinearMap.fromCompletion`: promotes a continuous semilinear map
  from `α` to `β` to a continuous semilinear map from `Completion α` to `β`.
-/

@[expose] public section

namespace ContinuousLinearMap

open UniformSpace Completion

variable {α β : Type*} {R₁ R₂ : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring R₁] [Module R₁ α] [UniformContinuousConstSMul R₁ α] [Semiring R₂] [UniformSpace β]
  [AddCommGroup β] [IsUniformAddGroup β] [Module R₂ β] [UniformContinuousConstSMul R₂ β]
  {σ : R₁ ->+* R₂}

section completion

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `completion` / `completion` 的定义

English:
definition completion
  signature: (f : α ->SL[σ] β)
  body: f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.fun_const_smul _)
    | ih x => simp [← Completion.coe_smul]

@[simp]

中文:
定义 completion
  签名: (f : α ->SL[σ] β)
  定义体: f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.fun_const_smul _)
    | ih x => simp [← Completion.coe_smul]

@[simp]

Depends on / 依赖: completion, continuous, f.continuous, f.toAddMonoidHom.completion, toAddMonoidHom
-/
noncomputable def completion (f : α ->SL[σ] β) : Completion α ->SL[σ] Completion β where
  __ := f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.fun_const_smul _)
    | ih x => simp [← Completion.coe_smul]

@[simp]
/--
lemma `toAddMonoidHom_completion` / 引理 `toAddMonoidHom_completion`

English:
lemma toAddMonoidHom_completion
  given: (f : α ->SL[σ] β)
  proof: rfl

中文:
引理 toAddMonoidHom_completion
  条件: (f : α ->SL[σ] β)
  证明: rfl
-/
lemma toAddMonoidHom_completion (f : α ->SL[σ] β) :
    f.completion.toAddMonoidHom = f.toAddMonoidHom.completion f.continuous := rfl

/--
lemma `coe_completion` / 引理 `coe_completion`

English:
lemma coe_completion
  given: (f : α ->SL[σ] β)
  proof: rfl

@[simp]

中文:
引理 coe_completion
  条件: (f : α ->SL[σ] β)
  证明: rfl

@[simp]
-/
lemma coe_completion (f : α ->SL[σ] β) :
    f.completion = Completion.map f := rfl

@[simp]
/--
theorem `completion_apply_coe` / 定理 `completion_apply_coe`

English:
theorem completion_apply_coe
  given: (f : α ->SL[σ] β) (a : α)
  proof: by simp [coe_completion, map_coe]

中文:
定理 completion_apply_coe
  条件: (f : α ->SL[σ] β) (a : α)
  证明: by simp [coe_completion, map_coe]

Depends on / 依赖: coe_completion, map_coe
-/
theorem completion_apply_coe (f : α ->SL[σ] β) (a : α) :
    f.completion a = f a := by simp [coe_completion, map_coe]

end completion

section fromCompletion

variable [T0Space β] [CompleteSpace β]

/--
Definition of `fromCompletion` / `fromCompletion` 的定义

English:
definition fromCompletion
  signature: (f : α ->SL[σ] β)
  body: f.toAddMonoidHom.extension f.continuous
  map_smul' c a := induction_on a
(isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by dsimp; fun_prop)) by
    simp [← Completion.coe_smul, AddMonoidHom.extension_coe f.toAddMonoidHom f.continuous]

@[simp]

中文:
定义 fromCompletion
  签名: (f : α ->SL[σ] β)
  定义体: f.toAddMonoidHom.extension f.continuous
  map_smul' c a := induction_on a
(isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by dsimp; fun_prop)) by
    simp [← Completion.coe_smul, AddMonoidHom.extension_coe f.toAddMonoidHom f.continuous]

@[simp]

Depends on / 依赖: continuous, extension, f.continuous, f.toAddMonoidHom.extension, toAddMonoidHom
-/
noncomputable def fromCompletion (f : α ->SL[σ] β) :
    Completion α ->SL[σ] β where
  __ := f.toAddMonoidHom.extension f.continuous
  map_smul' c a := induction_on a
(isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by dsimp; fun_prop)) by
    simp [← Completion.coe_smul, AddMonoidHom.extension_coe f.toAddMonoidHom f.continuous]

@[simp]
/--
lemma `toAddMonoidHom_fromCompletion` / 引理 `toAddMonoidHom_fromCompletion`

English:
lemma toAddMonoidHom_fromCompletion
  given: (f : α ->SL[σ] β)
  proof: rfl

中文:
引理 toAddMonoidHom_fromCompletion
  条件: (f : α ->SL[σ] β)
  证明: rfl
-/
lemma toAddMonoidHom_fromCompletion (f : α ->SL[σ] β) :
    f.fromCompletion.toAddMonoidHom = f.toAddMonoidHom.extension f.continuous := rfl

/--
lemma `coe_fromCompletion` / 引理 `coe_fromCompletion`

English:
lemma coe_fromCompletion
  given: (f : α ->SL[σ] β)
  proof: rfl

@[simp]

中文:
引理 coe_fromCompletion
  条件: (f : α ->SL[σ] β)
  证明: rfl

@[simp]
-/
lemma coe_fromCompletion (f : α ->SL[σ] β) :
    f.fromCompletion = Completion.extension f := rfl

@[simp]
/--
lemma `fromCompletion_apply_coe` / 引理 `fromCompletion_apply_coe`

English:
lemma fromCompletion_apply_coe
  given: (f : α ->SL[σ] β) (e : α)
  proof: by simp [coe_fromCompletion, extension_coe]

中文:
引理 fromCompletion_apply_coe
  条件: (f : α ->SL[σ] β) (e : α)
  证明: by simp [coe_fromCompletion, extension_coe]

Depends on / 依赖: coe_fromCompletion, extension_coe
-/
lemma fromCompletion_apply_coe (f : α ->SL[σ] β) (e : α) :
    f.fromCompletion e = f e := by simp [coe_fromCompletion, extension_coe]

/--
lemma `fromCompletion_unique` / 引理 `fromCompletion_unique`

English:
lemma fromCompletion_unique
  statement: (f : α ->SL[σ] β) (g : Completion α ->SL[σ] β)
  proof: by
  ext; simp [coe_fromCompletion, extension_unique f.uniformContinuous g.uniformContinuous h]

中文:
引理 fromCompletion_unique
  结论: (f : α ->SL[σ] β) (g : Completion α ->SL[σ] β)
  证明: by
  ext; simp [coe_fromCompletion, extension_unique f.uniformContinuous g.uniformContinuous h]

Depends on / 依赖: coe_fromCompletion, extension_unique, f.uniformContinuous, g.uniformContinuous, uniformContinuous
-/
lemma fromCompletion_unique (f : α ->SL[σ] β) (g : Completion α ->SL[σ] β)
    (h : forall (e : α), f e = g e) : f.fromCompletion = g := by
  ext; simp [coe_fromCompletion, extension_unique f.uniformContinuous g.uniformContinuous h]

end fromCompletion

end ContinuousLinearMap
