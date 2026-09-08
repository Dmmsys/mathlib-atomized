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
  {σ : R₁ →+* R₂}

section completion

set_option backward.isDefEq.respectTransparency false in
/--
Lift a continuous semilinear map to a continuous semilinear map between the
`UniformSpace.Completion`s of the spaces. This is `UniformSpace.Completion.map` bundled as a
continuous linear map when the input is itself a continuous linear map.
-/
/-
**ContinuousLinearMap.completion** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：completion (f : α ->SL[σ] β) : Completion α ->SL[σ] Completion β where __
参数：f : α ->SL[σ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a continuous semilinear map to a continuous semilinear map between the
`UniformSpace.Completion`s of the spaces. This is `UniformSpace.Completion.map` 
bundled as a
continuous linear map when the input is itself a continuous linear map.
-/
noncomputable def completion (f : α →SL[σ] β) : Completion α →SL[σ] Completion β where
  __ := f.toAddMonoidHom.completion f.continuous
  map_smul' r x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_map.comp <| continuous_const_smul r)
        (continuous_map.fun_const_smul _)
    | ih x => simp [← Completion.coe_smul]

@[simp]
/-
**ContinuousLinearMap.toAddMonoidHom_completion** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：toAddMonoidHom_completion (f : α ->SL[σ] β) : f.completion.toAddMonoidHom 
= f.toAddMonoidHom.completion f.continuous
参数：f : α ->SL[σ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddMonoidHom_completion (f : α →SL[σ] β) :
    f.completion.toAddMonoidHom = f.toAddMonoidHom.completion f.continuous := rfl
/-
**ContinuousLinearMap.coe_completion** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：coe_completion (f : α ->SL[σ] β) : f.completion = Completion.map f
参数：f : α ->SL[σ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_completion (f : α →SL[σ] β) :
    f.completion = Completion.map f := rfl

@[simp]
/-
**ContinuousLinearMap.completion_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：completion_apply_coe (f : α ->SL[σ] β) (a : α) : f.completion a = f a
参数：f : α ->SL[σ] β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem completion_apply_coe (f : α →SL[σ] β) (a : α) :
    f.completion a = f a := by simp [coe_completion, map_coe]

end completion

section fromCompletion

variable [T0Space β] [CompleteSpace β]

/-- Extension of a linear function to a linear function over the completion. This is the continuous
linear version of `UniformSpace.Completion.extension`. -/
/-
**ContinuousLinearMap.fromCompletion** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：fromCompletion (f : α ->SL[σ] β) : Completion α ->SL[σ] β where __
参数：f : α ->SL[σ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension of a linear function to a linear function over the completion. This is
 the continuous
linear version of `UniformSpace.Completion.extension`.
-/
noncomputable def fromCompletion (f : α →SL[σ] β) :
    Completion α →SL[σ] β where
  __ := f.toAddMonoidHom.extension f.continuous
  map_smul' c a := induction_on a
      (isClosed_eq (continuous_extension.comp (continuous_const_smul c)) (by dsimp; fun_prop)) <| by
    simp [← Completion.coe_smul, AddMonoidHom.extension_coe f.toAddMonoidHom f.continuous]

@[simp]
/-
**ContinuousLinearMap.toAddMonoidHom_fromCompletion** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：toAddMonoidHom_fromCompletion (f : α ->SL[σ] β) : f.fromCompletion.toAddMo
noidHom = f.toAddMonoidHom.extension f.continuous
参数：f : α ->SL[σ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddMonoidHom_fromCompletion (f : α →SL[σ] β) :
    f.fromCompletion.toAddMonoidHom = f.toAddMonoidHom.extension f.continuous := rfl
/-
**ContinuousLinearMap.coe_fromCompletion** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：coe_fromCompletion (f : α ->SL[σ] β) : f.fromCompletion = Completion.exten
sion f
参数：f : α ->SL[σ] β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_fromCompletion (f : α →SL[σ] β) :
    f.fromCompletion = Completion.extension f := rfl

@[simp]
/-
**ContinuousLinearMap.fromCompletion_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：fromCompletion_apply_coe (f : α ->SL[σ] β) (e : α) : f.fromCompletion e = 
f e
参数：f : α ->SL[σ] β；e : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromCompletion_apply_coe (f : α →SL[σ] β) (e : α) :
    f.fromCompletion e = f e := by simp [coe_fromCompletion, extension_coe]
/-
**ContinuousLinearMap.fromCompletion_unique** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：fromCompletion_unique (f : α ->SL[σ] β) (g : Completion α ->SL[σ] β) (h : 
forall (e : α), f e = g e) : f.fromCompletion = g
参数：f : α ->SL[σ] β；g : Completion α ->SL[σ] β；h : forall (e : α), f e = g e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `UniformSpace.Completion.extension_unique`：extension_unique (hf : Uniform
Continuous f) {g : Completion α -> β} (hg : UniformContinuous g) (h : forall a :
 α, f a = g (a : Completion α)…
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromCompletion_unique (f : α →SL[σ] β) (g : Completion α →SL[σ] β)
    (h : ∀ (e : α), f e = g e) : f.fromCompletion = g := by
  ext; simp [coe_fromCompletion, extension_unique f.uniformContinuous g.uniformContinuous h]

end fromCompletion

end ContinuousLinearMap

