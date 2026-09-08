/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Extensionality lemmas for monoid and group structures

In this file we prove extensionality lemmas for `Monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `Algebra.Group.Defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `MonoidHom.map_div`, `MonoidHom.map_pow` etc.

To refer to the `*` operator of a particular instance `i`, we use
`(letI := i; HMul.hMul : M → M → M)` instead of `i.mul` (which elaborates to `Mul.mul`), as the
former uses `HMul.hMul` which is the canonical spelling.

## Tags
monoid, group, extensionality
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Function

universe u

@[to_additive (attr := ext)]
/-
**Monoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.ext`：MulOneClass.ext {M : Type u} : forall ⦃m₁ m₂ : MulOneCl
ass M⦄, m₁.mul = m₂.mul -> m₁ = m₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ := by
  have : m₁.toMulOneClass = m₂.toMulOneClass := MulOneClass.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) this
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.npow = m₂.npow := by
    ext n x
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  rcases m₁ with @⟨@⟨⟨_⟩⟩, ⟨_⟩, _, _, ⟨_⟩⟩
  congr

@[to_additive]
/-
**CommMonoid.toMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommMonoid.toMonoid_injective {M : Type u} : Function.Injective (@CommMono
id.toMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CommMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@CommMonoid.toMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
/-
**CommMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.toMonoid_injective`：CommMonoid.toMonoid_injective {M : Type u
} : Function.Injective (@CommMonoid.toMonoid M)
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
-/
theorem CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
/-
**LeftCancelMonoid.toMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LeftCancelMonoid.toMonoid_injective {M : Type u} : Function.Injective (@Le
ftCancelMonoid.toMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
/-
**LeftCancelMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : (l
etI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.toMonoid_injective`：LeftCancelMonoid.toMonoid_injective
 {M : Type u} : Function.Injective (@LeftCancelMonoid.toMonoid M)
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
-/
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
/-
**RightCancelMonoid.toMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightCancelMonoid.toMonoid_injective {M : Type u} : Function.Injective (@R
ightCancelMonoid.toMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) := by
  rintro @⟨@⟨⟩⟩ @⟨@⟨⟩⟩ h
  congr <;> injection h

@[to_additive (attr := ext)]
/-
**RightCancelMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : 
(letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightCancelMonoid.toMonoid_injective`：RightCancelMonoid.toMonoid_injecti
ve {M : Type u} : Function.Injective (@RightCancelMonoid.toMonoid M)
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
-/
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul

@[to_additive]
/-
**CancelMonoid.toLeftCancelMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CancelMonoid.toLeftCancelMonoid_injective {M : Type u} : Function.Injectiv
e (@CancelMonoid.toLeftCancelMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

@[to_additive (attr := ext)]
/-
**CancelMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CancelMonoid.toLeftCancelMonoid_injective`：CancelMonoid.toLeftCancelMono
id_injective {M : Type u} : Function.Injective (@CancelMonoid.toLeftCancelMonoid
 M)
· 使用定理 `LeftCancelMonoid.ext`：LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCan
celMonoid M⦄ (h_mul : (letI
-/
theorem CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul

@[to_additive]
/-
**CancelMonoid.toRightCancelMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CancelMonoid.toRightCancelMonoid_injective {M : Type u} : Function.Injecti
ve (@CancelMonoid.toRightCancelMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CancelMonoid.ext`：CancelMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelMonoid M⦄ 
(h_mul : (letI
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem CancelMonoid.toRightCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toRightCancelMonoid M) := by
  intro m₁ m₂ h
  apply CancelMonoid.ext
  exact congrArg (fun m : Monoid M => (letI := m; HMul.hMul : M → M → M)) <|
    congrArg (@RightCancelMonoid.toMonoid M) h

@[to_additive]
/-
**CancelCommMonoid.toCommMonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CancelCommMonoid.toCommMonoid_injective {M : Type u} : Function.Injective 
(@CancelCommMonoid.toCommMonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) := by
  rintro @⟨@⟨@⟨⟩⟩⟩ @⟨@⟨@⟨⟩⟩⟩ h
  grind

@[to_additive (attr := ext)]
/-
**CancelCommMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : (le
tI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CancelCommMonoid.toCommMonoid_injective`：CancelCommMonoid.toCommMonoid_i
njective {M : Type u} : Function.Injective (@CancelCommMonoid.toCommMonoid M)
· 使用定理 `CommMonoid.ext`：CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul
 : (letI
-/
theorem CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul

@[to_additive (attr := ext)]
/-
**DivInvMonoid.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHom.map_zpow'`：∀ {M : Type u_4} {N : Type u_5} [inst : DivInvMonoi
d M] [inst_1 : DivInvMonoid N] (f : M →* N),   (∀ (x : M), f x⁻¹ = (f x)⁻¹) → ∀ 
(a : M) (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M))
    (h_inv : (letI := m₁; Inv.inv : M → M) = (letI := m₂; Inv.inv : M → M)) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact (@div_eq_mul_inv _ m₁ a b).trans
      (((congr_fun (congr_fun h_mul a) _).trans
        (congr_arg _ (congr_fun h_inv b))).trans (@div_eq_mul_inv _ m₂ a b).symm)
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩, ⟨_⟩⟩
  congr

@[to_additive]
/-
**Group.toDivInvMonoid_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Group.toDivInvMonoid_injective {G : Type*} : Injective (@Group.toDivInvMon
oid G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Group.toDivInvMonoid_injective {G : Type*} : Injective (@Group.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
/-
**Group.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Monoid.ext`：Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : (letI
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `Group.toDivInvMonoid_injective`：Group.toDivInvMonoid_injective {G : Type
*} : Injective (@Group.toDivInvMonoid G)
· 使用定理 `DivInvMonoid.ext`：DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄ 
(h_mul : (letI
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) :
    g₁ = g₂ := by
  have h₁ : g₁.one = g₂.one := congr_arg (·.one) (Monoid.ext h_mul)
  let f : @MonoidHom G G g₁.toMulOne g₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ g₂.toDivisionMonoid f))

@[to_additive]
/-
**CommGroup.toGroup_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommGroup.toGroup_injective {G : Type*} : Injective (@CommGroup.toGroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma CommGroup.toGroup_injective {G : Type*} : Injective (@CommGroup.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

@[to_additive (attr := ext)]
/-
**CommGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : (letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommGroup.toGroup_injective`：CommGroup.toGroup_injective {G : Type*} : I
njective (@CommGroup.toGroup G)
· 使用定理 `Group.ext`：Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄ (h_mul : (letI
-/
theorem CommGroup.ext {G : Type*} ⦃g₁ g₂ : CommGroup G⦄
    (h_mul : (letI := g₁; HMul.hMul : G → G → G) = (letI := g₂; HMul.hMul : G → G → G)) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
