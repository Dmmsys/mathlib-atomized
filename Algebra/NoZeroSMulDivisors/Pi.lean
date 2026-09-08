/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yaël Dillies
-/
module

public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Pi instances for NoZeroSMulDivisors

This file defines instances for NoZeroSMulDivisors on Pi types.
-/

public section


universe u v

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

/-
**Pi.noZeroSMulDivisors** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.noZeroSMulDivisors (α) [Semiring α] [IsDomain α] [forall i, AddCommGrou
p <| f i] [forall i, Module α <| f i] [forall i, NoZeroSMulDivisors α <| f i] : 
NoZeroSMulDivisors α (forall i : I, f i)
参数：α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
instance Pi.noZeroSMulDivisors (α) [Semiring α] [IsDomain α] [∀ i, AddCommGroup <| f i]
    [∀ i, Module α <| f i] [∀ i, NoZeroSMulDivisors α <| f i] :
    NoZeroSMulDivisors α (∀ i : I, f i) :=
  ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

/-- A special case of `Pi.noZeroSMulDivisors` for non-dependent types. Lean struggles to
synthesize this instance by itself elsewhere in the library. -/
/-
**_root_.Function.noZeroSMulDivisors** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.Function.noZeroSMulDivisors {ι α β : Type*} [Semiring α] [IsDomain 
α] [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β] : NoZeroSMulDivisors α
 (ι -> β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `Pi.noZeroSMulDivisors` for non-dependent types. Lean struggle
s to
synthesize this instance by itself elsewhere in the library.
-/
instance _root_.Function.noZeroSMulDivisors {ι α β : Type*} [Semiring α] [IsDomain α]
    [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β] : NoZeroSMulDivisors α (ι → β) :=
  Pi.noZeroSMulDivisors _
