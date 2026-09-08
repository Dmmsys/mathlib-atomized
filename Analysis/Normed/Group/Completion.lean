/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/

public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type*)

/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace E] [Norm E] : Norm (Completion E) where
  norm := Completion.extension Norm.norm

@[simp]
/-
**UniformSpace.Completion.norm_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖
x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `uniformContinuous_norm`：∀ {E : Type u_2} [inst : SeminormedAddGroup E], 
UniformContinuous norm
-/
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) where
  dist_eq x y := by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension (continuous_neg.fst.add continuous_snd)
    · rw [← Completion.coe_neg, ← Completion.coe_add, norm_coe, Completion.dist_eq,
        dist_eq_norm_neg_add]

@[simp]
/-
**UniformSpace.Completion.nnnorm_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Com
pletion`。
形式化陈述：nnnorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖₊ 
= ‖x‖₊
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊ := by
  simp [nnnorm]

@[simp]
/-
**UniformSpace.Completion.enorm_coe** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace.Comp
letion`。
形式化陈述：enorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ₑ =
 ‖x‖ₑ
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.nnnorm_coe`：nnnorm_coe {E} [SeminormedAddCommGro
up E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ₑ = ‖x‖ₑ := by
  simp [enorm]

end Completion

end UniformSpace

