/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Additive and Multiplicative for group actions

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero MonoidHom

open Function (Injective Surjective)

variable {M α β γ : Type*}

section

open Additive Multiplicative

/-
**Additive.vadd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.vadd [SMul α β] : VAdd (Additive α) β where vadd a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.vadd [SMul α β] : VAdd (Additive α) β where vadd a := (a.toMul • ·)
/-
**Multiplicative.smul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a := (a.toAdd +ᵥ ·)
/-
**toMul_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] (a : Additive α) (b : β)
, Additive.toMul a • b = a +ᵥ b
参数：a : Additive α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMul_smul [SMul α β] (a : Additive α) (b : β) : (a.toMul : α) • b = a +ᵥ b := rfl
/-
**ofMul_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] (a : α) (b : β), Additiv
e.ofMul a +ᵥ b = a • b
参数：a : α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofMul_vadd [SMul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b := rfl
/-
**toAdd_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] (a : Multiplicative α) (
b : β), Multiplicative.toAdd a +ᵥ b = a • b
参数：a : Multiplicative α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAdd_vadd [VAdd α β] (a : Multiplicative α) (b : β) : (a.toAdd : α) +ᵥ b = a • b :=
  rfl
/-
**ofAdd_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] (a : α) (b : β), Multipl
icative.ofAdd a • b = a +ᵥ b
参数：a : α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b := rfl
/-
**Additive.addAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β w
here zero_vadd
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b
-/
instance Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β where
  zero_vadd := MulAction.one_smul
  add_vadd := mul_smul (α := α)
/-
**Multiplicative.mulAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.mulAction [AddMonoid α] [AddAction α β] : MulAction (Multip
licative α) β where one_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.zero_vadd`：∀ {G : Type u_9} {P : Type u_10} {inst : AddMonoid 
G} [self : AddAction G P] (p : P), 0 +ᵥ p = p
-/
instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] :
    MulAction (Multiplicative α) β where
  one_smul := AddAction.zero_vadd
  mul_smul := add_vadd (G := α)
/-
**Additive.vaddCommClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.vaddCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : VAddC
ommClass (Additive α) (Additive β) γ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance Additive.vaddCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    VAddCommClass (Additive α) (Additive β) γ :=
  ⟨@smul_comm α β _ _ _ _⟩
/-
**Multiplicative.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
 SMulCommClass (Multiplicative α) (Multiplicative β) γ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VAddCommClass.vadd_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : VAdd M α} {inst_1 : VAdd N α} [self : VAddCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
    SMulCommClass (Multiplicative α) (Multiplicative β) γ :=
  ⟨@vadd_comm α β _ _ _ _⟩

end

