/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Tactic.Abel

/-!
# Associator in a ring

If `R` is a non-associative ring, then  `(x * y) * z - x * (y * z)` is called the `associator` of
ring elements `x y z : R`.

The associator vanishes exactly when `R` is associative.

We prove variants of this statement also for the `AddMonoidHom` bundled version of the associator,
as well as the bundled version of `mulLeft₃` and `mulRight₃`, the multiplications `(x * y) * z` and
`x * (y * z)`.
-/

@[expose] public section

variable {R : Type*}

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R]

/-- The associator `(x * y) * z - x * (y * z)` -/
/-
**associator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：associator (x y z : R) : R
参数：x y z : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator `(x * y) * z - x * (y * z)`
-/
def associator (x y z : R) : R := (x * y) * z - x * (y * z)
/-
**associator_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associator_apply (x y z : R) : associator x y z = (x * y) * z - x * (y * z
)
参数：x y z : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_apply (x y z : R) : associator x y z = (x * y) * z - x * (y * z) := rfl
/-
**associator_eq_zero_iff_associative** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associator_eq_zero_iff_associative : associator (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congr_fun₃`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {f g : (a : α) → (b : β a)
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ sub_eq_zero.mp <| congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]
/-
**associator_cocycle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associator_cocycle (a b c d : R) : a * associator b c d - associator (a * 
b) c d + associator a (b * c) d - associator a b (c * d) + (associator a b c) * 
d = 0
参数：a b c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `_private.Mathlib.Algebra.Ring.Associator.0.associator_cocycle._abel_1_2`
：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (a b c d : R),   a * (b * c *
 d) - a * (b * (c * d)) - (a * b * c * d - a * b * (c * d)) +…
-/
theorem associator_cocycle (a b c d : R) :
    a * associator b c d - associator (a * b) c d + associator a (b * c) d - associator a b (c * d)
    + (associator a b c) * d = 0 := by
  simp only [associator, mul_sub, sub_mul]
  abel1

open MulOpposite in
@[simp]
/-
**associator_op** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：associator_op (x y z : Rᵐᵒᵖ) : associator x y z = -op (associator (unop z)
 (unop y) (unop x))
参数：x y z : Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_op (x y z : Rᵐᵒᵖ) :
    associator x y z = -op (associator (unop z) (unop y) (unop x)) := by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

@[simp]
/-
**associator_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associator_eq_zero : associator (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associator_eq_zero_iff_associative`：associator_eq_zero_iff_associative :
 associator (R
-/
theorem associator_eq_zero : associator (R := R) = 0 :=
  associator_eq_zero_iff_associative.mpr inferInstance

end NonUnitalRing

namespace AddMonoidHom

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-- The multiplication `(x * y) * z` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. See also `LinearMap.mulLeftRight` for a
related functions realized as a linear map. -/
/-
**AddMonoidHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulLeft (r : R) : R ->+ R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication `(x * y) * z` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. See also `LinearMap.mulLeftRi
ght` for a
related functions realized as a linear map.
-/
def mulLeft₃ : R →+ R →+ R →+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
/-
**AddMonoidHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulLeft (r : R) : R ->+ R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeft₃_apply (x y z : R) : mulLeft₃ x y z = (x * y) * z := rfl

/-- The multiplication `x * (y * z)` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. -/
/-
**AddMonoidHom.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulRight (r : R) : R ->+ R where toFun a
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication `x * (y * z)` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument.
-/
def mulRight₃ : R →+ R →+ R →+ R where
  toFun x := compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
/-
**AddMonoidHom.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulRight (r : R) : R ->+ R where toFun a
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRight₃_apply (x y z : R) : mulRight₃ x y z = x * (y * z) := rfl

/-- An a priori non-associative semiring is associative if the `AddMonoidHom` versions of
the multiplications `(x * y) * z` and `x * (y * z)` agree. -/
/-
**AddMonoidHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulLeft (r : R) : R ->+ R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An a priori non-associative semiring is associative if the `AddMonoidHom` versio
ns of
the multiplications `(x * y) * z` and `x * (y * z)` agree.
-/
theorem mulLeft₃_eq_mulRight₃_iff_associative :
    mulLeft₃ (R := R) = mulRight₃ ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R]

/-
**AddMonoidHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulLeft (r : R) : R ->+ R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeft₃_eq_mulRight₃ : mulLeft₃ (R := R) = mulRight₃ :=
  mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance

end NonUnitalSemiring

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] (a b c : R)

/-- The associator for a non-associative ring is `(x * y) * z - x * (y * z)`. It is an
`AddMonoidHom` in each argument. -/
/-
**AddMonoidHom.associator** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：associator : R ->+ R ->+ R ->+ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for a non-associative ring is `(x * y) * z - x * (y * z)`. It is 
an
`AddMonoidHom` in each argument.
-/
def associator : R →+ R →+ R →+ R := mulLeft₃ - mulRight₃

@[simp]
/-
**AddMonoidHom.associator_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：associator_apply : associator a b c = _root_.associator a b c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_apply : associator a b c = _root_.associator a b c := rfl

/-- An a priori non-associative ring is associative iff the `AddMonoidHom` version of the
associator vanishes. -/
/-
**AddMonoidHom.associator_eq_zero_iff_associative** 是 Mathlib 中的一个定理，位于命名空间 `Add
MonoidHom`。
形式化陈述：associator_eq_zero_iff_associative : associator (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An a priori non-associative ring is associative iff the `AddMonoidHom` version o
f the
associator vanishes.
-/
theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) ↦ x * y) := by
  simp [mulLeft₃_eq_mulRight₃_iff_associative, associator, sub_eq_zero]

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

@[simp]
/-
**AddMonoidHom.associator_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：associator_eq_zero : associator (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddMonoidHom.associator_eq_zero_iff_associative`：associator_eq_zero_iff_
associative : associator (R
-/
theorem associator_eq_zero : associator (R := R) = 0 :=
  associator_eq_zero_iff_associative.mpr inferInstance

end NonUnitalRing
end AddMonoidHom

