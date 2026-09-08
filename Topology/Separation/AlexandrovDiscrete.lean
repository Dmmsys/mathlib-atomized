/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.AlexandrovDiscrete

/-!
# T1 Alexandrov-discrete topology is discrete
-/

public section

open Filter

variable {X : Type*} [TopologicalSpace X]

@[simp]
/-
**nhdsKer_eq_of_t1Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsKer_eq_of_t1Space [T1Space X] (s : Set X) : nhdsKer s = s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `specializes_eq_eq`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space
 X], (fun x1 x2 => x1 ⤳ x2) = Eq
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsKer_eq_of_t1Space [T1Space X] (s : Set X) : nhdsKer s = s := by
  ext; simp [mem_nhdsKer_iff_specializes]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [AlexandrovDiscrete X] [T1Space X] : DiscreteTopology X := by
  simp [discreteTopology_iff_nhds, ← principal_nhdsKer_singleton]
