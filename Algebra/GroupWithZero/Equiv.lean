/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.GroupWithZero.Hom

/-! # Isomorphisms of monoids with zero -/

@[expose] public section

assert_not_exists Ring

namespace MulEquivClass
variable {F α β : Type*} [EquivLike F α β]

-- See note [lower instance priority]
/-
**MulEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toZeroHomClass [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero f :=
    calc
      f 0 = f 0 * f (EquivLike.inv f 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
/-
**MulEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass with }

end MulEquivClass

namespace MulEquiv

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

/-- An isomorphism of monoids with zero can be treated as a homomorphism preserving zero.
This is a helper projection that utilizes the `MonoidWithZeroHomClass` instance. -/
/-
**MulEquiv.toMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidWithZeroHom (f : G ≃* H) : G ->*₀ H
参数：f : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of monoids with zero can be treated as a homomorphism preserving 
zero.
This is a helper projection that utilizes the `MonoidWithZeroHomClass` instance.
-/
def toMonoidWithZeroHom (f : G ≃* H) : G →*₀ H := .ofClass f
/-
**MulEquiv.toMonoidWithZeroHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : MulZeroOneClass G] [inst_1 : MulZe
roOneClass H] (f : G ≃* H) (x : G),   f.toMonoidWithZeroHom x = f x
参数：f : G ≃* H；x : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidWithZeroHom_apply (f : G ≃* H) (x : G) : f.toMonoidWithZeroHom x = f x := rfl
/-
**MulEquiv.toMonoidWithZeroHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidWithZeroHom_injective (f : G ≃* H) : Function.Injective f.toMonoid
WithZeroHom
参数：f : G ≃* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
lemma toMonoidWithZeroHom_injective (f : G ≃* H) :
    Function.Injective f.toMonoidWithZeroHom :=
  f.injective
/-
**MulEquiv.toMonoidWithZeroHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidWithZeroHom_surjective (f : G ≃* H) : Function.Surjective f.toMono
idWithZeroHom
参数：f : G ≃* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
lemma toMonoidWithZeroHom_surjective (f : G ≃* H) :
    Function.Surjective f.toMonoidWithZeroHom :=
  f.surjective
/-
**MulEquiv.toMonoidWithZeroHom_bijective** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidWithZeroHom_bijective (f : G ≃* H) : Function.Bijective f.toMonoid
WithZeroHom
参数：f : G ≃* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.bijective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Bijective ⇑e
-/
lemma toMonoidWithZeroHom_bijective (f : G ≃* H) :
    Function.Bijective f.toMonoidWithZeroHom :=
  f.bijective
/-
**MulEquiv.toMonoidWithZeroHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : MulZeroOneClass G] [inst_1 : MulZe
roOneClass H] {f g : G ≃* H},   f.toMonoidWithZeroHom = g.toMonoidWithZeroHom ↔ 
f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toMonoidWithZeroHom_inj {f g : G ≃* H} :
    f.toMonoidWithZeroHom = g.toMonoidWithZeroHom ↔ f = g := by
  simp [MonoidWithZeroHom.ext_iff, MulEquiv.ext_iff]

end MulEquiv

