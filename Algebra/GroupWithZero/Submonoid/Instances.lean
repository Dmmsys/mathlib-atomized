/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Instances for the range submonoid of a monoid with zero hom
-/

public section

assert_not_exists Ring

namespace MonoidWithZeroHom

variable {G H : Type*}

/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    MulZeroOneClass (MonoidHom.mrange f) where
  zero := ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
/-
**MonoidWithZeroHom.val_mrange_zero** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom
`。
形式化陈述：val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G ->*₀ H) : (
(0 : MonoidHom.mrange f) : H) = 0
参数：f : G ->*₀ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    ((0 : MonoidHom.mrange f) : H) = 0 :=
  rfl
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroOneClass G] [MonoidWithZero H] (f : G →*₀ H) :
    MonoidWithZero (MonoidHom.mrange f) where
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroOneClass G] [CommMonoidWithZero H] (f : G →*₀ H) :
    CommMonoidWithZero (MonoidHom.mrange f) where
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GroupWithZero G] [GroupWithZero H] (f : G →*₀ H) :
    GroupWithZero (MonoidHom.mrange f) where
  inv := fun x ↦ ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    use y⁻¹
    simp [← hy]⟩
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [-map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cancel₀ h
/-
**MonoidWithZeroHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GroupWithZero G] [CommGroupWithZero H] (f : G →*₀ H) :
    CommGroupWithZero (MonoidHom.mrange f) where
/-
**MonoidWithZeroHom.mker_inverse** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：mker_inverse [CommGroupWithZero H] : MonoidHom.mker (MonoidWithZero.invers
e (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mker_inverse [CommGroupWithZero H] :
    MonoidHom.mker (MonoidWithZero.inverse (M := H)) = ⊥ := by
  ext
  simp

end MonoidWithZeroHom

