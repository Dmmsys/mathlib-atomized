/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Hom.Basic
/-!
# Ordered monoid and group homomorphisms

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `OrderAddMonoidHom`: Ordered additive monoid homomorphisms.
* `OrderMonoidHom`: Ordered monoid homomorphisms.
* `OrderAddMonoidIso`: Ordered additive monoid isomorphisms.
* `OrderMonoidIso`: Ordered monoid isomorphisms.

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive group homs.
* `→*o`: Bundled ordered monoid homs. Also use for group homs.
* `≃+o`: Bundled ordered additive monoid isos. Also use for additive group isos.
* `≃*o`: Bundled ordered monoid isos. Also use for group isos.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `OrderGroupHom` -- the idea is that `OrderMonoidHom` is used.
The constructor for `OrderMonoidHom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `OrderMonoidHom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `OrderMonoidHom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

### Removed typeclasses

This file used to define typeclasses for order-preserving (additive) monoid homomorphisms:
`OrderAddMonoidHomClass`, `OrderMonoidHomClass`, and `OrderMonoidWithZeroHomClass`.

In https://github.com/leanprover-community/mathlib4/pull/10544 we migrated from these typeclasses
to assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`,
making some definitions and lemmas irrelevant.

## Tags

ordered monoid, ordered group
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

variable {F α β γ δ : Type*}

section AddMonoid

/-- `α →+o β` is the type of monotone functions `α → β` that preserve the ordered additive monoid
structure.

`OrderAddMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N] (f : F)`. -/
/-
**OrderAddMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → [AddZeroCl
ass α] → [AddZeroClass β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α →+o β` is the type of monotone functions `α → β` that preserve the ordered ad
ditive monoid
structure.

`OrderAddMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N] (f : F
)`.
-/
structure OrderAddMonoidHom (α β : Type*) [Preorder α] [Preorder β] [AddZeroClass α]
  [AddZeroClass β] extends α →+ β where
  /-- An `OrderAddMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderAddMonoidHom`. -/
infixr:25 " →+o " => OrderAddMonoidHom

/-- `α ≃+o β` is the type of isomorphisms `α ≃ β` that preserve the ordered additive monoid
structure.

`OrderAddMonoidIso` is also used for ordered group isomorphisms.

When possible, instead of parametrizing results over `(f : α ≃+o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddEquivClass F M N] [OrderIsoClass F M N] (f : F)`. -/
/-
**OrderAddMonoidIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → [Add α] → 
[Add β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α ≃+o β` is the type of isomorphisms `α ≃ β` that preserve the ordered additive
 monoid
structure.

`OrderAddMonoidIso` is also used for ordered group isomorphisms.

When possible, instead of parametrizing results over `(f : α ≃+o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddEquivClass F M N] [OrderIsoClass F M N] (f : F)
`.
-/
structure OrderAddMonoidIso (α β : Type*) [Preorder α] [Preorder β] [Add α] [Add β]
  extends α ≃+ β where
  /-- An `OrderAddMonoidIso` respects `≤`. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b

/-- Infix notation for `OrderAddMonoidIso`. -/
infixr:25 " ≃+o " => OrderAddMonoidIso

-- Instances and lemmas are defined below through `@[to_additive]`.
end AddMonoid

section Monoid

/-- `α →*o β` is the type of functions `α → β` that preserve the ordered monoid structure.

`OrderMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N] (f : F)`. -/
@[to_additive]
/-
**OrderMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → [MulOneCla
ss α] → [MulOneClass β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α →*o β` is the type of functions `α → β` that preserve the ordered monoid stru
cture.

`OrderMonoidHom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N] (f : F
)`.
-/
structure OrderMonoidHom (α β : Type*) [Preorder α] [Preorder β] [MulOneClass α]
  [MulOneClass β] extends α →* β where
  /-- An `OrderMonoidHom` is a monotone function. -/
  monotone' : Monotone toFun

/-- Infix notation for `OrderMonoidHom`. -/
infixr:25 " →*o " => OrderMonoidHom

variable [Preorder α] [Preorder β] [MulOneClass α] [MulOneClass β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `MonoidHomClass F α β`
into an actual `OrderMonoidHom`. This is declared as the default coercion from `F` to `α →*o β`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `OrderHomClass F α β` and `AddMonoidHomClass F α β`
  into an actual `OrderAddMonoidHom`.
  This is declared as the default coercion from `F` to `α →+o β`. -/]
/-
**OrderMonoidHomClass.toOrderMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidHomClass.toOrderMonoidHom [OrderHomClass F α β] [MonoidHomClass
 F α β] (f : F) : α ->*o β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…
-/
def OrderMonoidHomClass.toOrderMonoidHom [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) :
    α →*o β :=
  { (f : α →* β) with monotone' := OrderHomClass.monotone f }

/-- Any type satisfying `OrderMonoidHomClass` can be cast into `OrderMonoidHom` via
  `OrderMonoidHomClass.toOrderMonoidHom`. -/
@[to_additive /-- Any type satisfying `OrderAddMonoidHomClass` can be cast into `OrderAddMonoidHom`
  via `OrderAddMonoidHomClass.toOrderAddMonoidHom`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderHomClass F α β] [MonoidHomClass F α β] : CoeTC F (α →*o β) :=
  ⟨OrderMonoidHomClass.toOrderMonoidHom⟩

/-- `α ≃*o β` is the type of isomorphisms `α ≃ β` that preserve the ordered monoid structure.

`OrderMonoidIso` is also used for ordered group isomorphisms.

When possible, instead of parametrizing results over `(f : α ≃*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulEquivClass F M N] [OrderIsoClass F M N] (f : F)`. -/
@[to_additive]
/-
**OrderMonoidIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → [Mul α] → 
[Mul β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α ≃*o β` is the type of isomorphisms `α ≃ β` that preserve the ordered monoid s
tructure.

`OrderMonoidIso` is also used for ordered group isomorphisms.

When possible, instead of parametrizing results over `(f : α ≃*o β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulEquivClass F M N] [OrderIsoClass F M N] (f : F)
`.
-/
structure OrderMonoidIso (α β : Type*) [Preorder α] [Preorder β] [Mul α] [Mul β]
  extends α ≃* β where
  /-- An `OrderMonoidIso` respects `≤`. -/
  map_le_map_iff' {a b : α} : toFun a ≤ toFun b ↔ a ≤ b

/-- Infix notation for `OrderMonoidIso`. -/
infixr:25 " ≃*o " => OrderMonoidIso

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `MulEquivClass F α β`
into an actual `OrderMonoidIso`. This is declared as the default coercion from `F` to `α ≃*o β`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` and `AddEquivClass F α β`
  into an actual `OrderAddMonoidIso`.
  This is declared as the default coercion from `F` to `α ≃+o β`. -/]
/-
**OrderMonoidIsoClass.toOrderMonoidIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIsoClass.toOrderMonoidIso [EquivLike F α β] [OrderIsoClass F α 
β] [MulEquivClass F α β] (f : F) : α ≃*o β
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OrderMonoidIsoClass.toOrderMonoidIso [EquivLike F α β] [OrderIsoClass F α β]
    [MulEquivClass F α β] (f : F) :
    α ≃*o β :=
  { (f : α ≃* β) with map_le_map_iff' := OrderIsoClass.map_le_map_iff f }

/-- Any type satisfying `OrderMonoidIsoClass` can be cast into `OrderMonoidIso` via
  `OrderMonoidIsoClass.toOrderMonoidIso`. -/
@[to_additive /-- Any type satisfying `OrderAddMonoidIsoClass` can be cast into `OrderAddMonoidIso`
  via `OrderAddMonoidIsoClass.toOrderAddMonoidIso`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EquivLike F α β] [OrderIsoClass F α β] [MulEquivClass F α β] : CoeTC F (α ≃*o β) :=
  ⟨OrderMonoidIsoClass.toOrderMonoidIso⟩

end Monoid

section MonoidHomClass

variable [Group α] [Monoid β]
variable {F : Type*} [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
/-
**map_inv_le_map_inv_iff_map_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_le_map_inv_iff_map_le_map [LE β] [MulRightMono β] [MulLeftMono β] 
{f g : F} {x : α} : f x⁻¹ <= g x⁻¹ ↔ g x <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem map_inv_le_map_inv_iff_map_le_map [LE β] [MulRightMono β] [MulLeftMono β]
    {f g : F} {x : α} : f x⁻¹ ≤ g x⁻¹ ↔ g x ≤ f x := by
  suffices h : ∀ (f g : F) (x), f x⁻¹ ≤ g x⁻¹ → g x ≤ f x from
    ⟨h f g x, by simpa using h g f x⁻¹⟩
  exact fun f g x hfg ↦ calc
    _ = f x * (f x⁻¹ * g x) := by simp [← mul_assoc, ← map_mul]
    _ ≤ f x * (g x⁻¹ * g x) := by gcongr
    _ = f x                 := by simp [← map_mul]

@[to_additive]
/-
**MonoidHomClass.ext_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHomClass.ext_iff_le [PartialOrder β] [MulRightMono β] [MulLeftMono β
] {f g : F} : f = g ↔ forall x, f x <= g x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_inv_le_map_inv_iff_map_le_map`：map_inv_le_map_inv_iff_map_le_map [LE
 β] [MulRightMono β] [MulLeftMono β] {f g : F} {x : α} : f x⁻¹ <= g x⁻¹ ↔ g x <=
 f x
-/
theorem MonoidHomClass.ext_iff_le [PartialOrder β] [MulRightMono β] [MulLeftMono β] {f g : F} :
    f = g ↔ ∀ x, f x ≤ g x where
  mp := by simp +contextual
  mpr h := DFunLike.ext f g
    fun x ↦ le_antisymm (h x) (map_inv_le_map_inv_iff_map_le_map.mp <| h x⁻¹)

end MonoidHomClass

section OrderedZero

variable [FunLike F α β]
variable [Preorder α] [Zero α] [Preorder β] [Zero β] [OrderHomClass F α β]
  [ZeroHomClass F α β] (f : F) {a : α}

/-- See also `NonnegHomClass.apply_nonneg`. -/
/-
**map_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nonneg (ha : 0 <= a) : 0 <= f a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…

--- 原说明 ---
See also `NonnegHomClass.apply_nonneg`.
-/
theorem map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha
/-
**map_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nonpos (ha : a <= 0) : f a <= 0
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
-/
theorem map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

end OrderedZero

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]
variable (f : F)

/-
**monotone_iff_map_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_iff_map_nonneg [iamhc : AddMonoidHomClass F α β] : Monotone (f : 
α -> β) ↔ forall a, 0 <= a -> 0 <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
-/
theorem monotone_iff_map_nonneg [iamhc : AddMonoidHomClass F α β] :
    Monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a :=
  ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a, map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

variable [iamhc : AddMonoidHomClass F α β]
/-
**antitone_iff_map_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_iff_map_nonpos : Antitone (f : α -> β) ↔ forall a, 0 <= a -> f a 
<= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monotone_toDual_comp_iff`：monotone_toDual_comp_iff : Monotone (toDual ∘ 
f) ↔ Antitone f
· 使用定理 `monotone_iff_map_nonneg`：monotone_iff_map_nonneg [iamhc : AddMonoidHomCl
ass F α β] : Monotone (f : α -> β) ↔ forall a, 0 <= a -> 0 <= f a
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
  monotone_toDual_comp_iff.symm.trans <| monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _
/-
**monotone_iff_map_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_iff_map_nonpos : Monotone (f : α -> β) ↔ forall a <= 0, f a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `antitone_comp_ofDual_iff`：antitone_comp_ofDual_iff : Antitone (f ∘ ofDua
l) ↔ Monotone f
· 使用定理 `antitone_iff_map_nonpos`：antitone_iff_map_nonpos : Antitone (f : α -> β)
 ↔ forall a, 0 <= a -> f a <= 0
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem monotone_iff_map_nonpos : Monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 :=
  antitone_comp_ofDual_iff.symm.trans <| antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _
/-
**antitone_iff_map_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_iff_map_nonneg : Antitone (f : α -> β) ↔ forall a <= 0, 0 <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monotone_comp_ofDual_iff`：monotone_comp_ofDual_iff : Monotone (f ∘ ofDua
l) ↔ Antitone f
· 使用定理 `monotone_iff_map_nonneg`：monotone_iff_map_nonneg [iamhc : AddMonoidHomCl
ass F α β] : Monotone (f : α -> β) ↔ forall a, 0 <= a -> 0 <= f a
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem antitone_iff_map_nonneg : Antitone (f : α → β) ↔ ∀ a ≤ 0, 0 ≤ f a :=
  monotone_comp_ofDual_iff.symm.trans <| monotone_iff_map_nonneg (α := αᵒᵈ) (iamhc := iamhc) _
/-
**strictMono_iff_map_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_iff_map_pos : StrictMono (f : α -> β) ↔ forall a, 0 < a -> 0 < 
f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddGroup.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : AddGroup N
] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   ContravariantClass N N (fun x
1 x2 =…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
-/
theorem strictMono_iff_map_pos :
    StrictMono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a := by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)
/-
**strictAnti_iff_map_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_iff_map_neg : StrictAnti (f : α -> β) ↔ forall a, 0 < a -> f a 
< 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `strictMono_toDual_comp_iff`：strictMono_toDual_comp_iff : StrictMono (toD
ual ∘ f : α -> βᵒᵈ) ↔ StrictAnti f
· 使用定理 `strictMono_iff_map_pos`：strictMono_iff_map_pos : StrictMono (f : α -> β)
 ↔ forall a, 0 < a -> 0 < f a
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem strictAnti_iff_map_neg : StrictAnti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 :=
  strictMono_toDual_comp_iff.symm.trans <| strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _
/-
**strictMono_iff_map_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_iff_map_neg : StrictMono (f : α -> β) ↔ forall a < 0, f a < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `strictAnti_comp_ofDual_iff`：strictAnti_comp_ofDual_iff : StrictAnti (f ∘
 ofDual) ↔ StrictMono f
· 使用定理 `strictAnti_iff_map_neg`：strictAnti_iff_map_neg : StrictAnti (f : α -> β)
 ↔ forall a, 0 < a -> f a < 0
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem strictMono_iff_map_neg : StrictMono (f : α → β) ↔ ∀ a < 0, f a < 0 :=
  strictAnti_comp_ofDual_iff.symm.trans <| strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _
/-
**strictAnti_iff_map_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_iff_map_pos : StrictAnti (f : α -> β) ↔ forall a < 0, 0 < f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `strictMono_comp_ofDual_iff`：strictMono_comp_ofDual_iff : StrictMono (f ∘
 ofDual) ↔ StrictAnti f
· 使用定理 `strictMono_iff_map_pos`：strictMono_iff_map_pos : StrictMono (f : α -> β)
 ↔ forall a, 0 < a -> 0 < f a
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem strictAnti_iff_map_pos : StrictAnti (f : α → β) ↔ ∀ a < 0, 0 < f a :=
  strictMono_comp_ofDual_iff.symm.trans <| strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _

end OrderedAddCommGroup

namespace OrderMonoidHom

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

@[to_additive]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →*o β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

initialize_simps_projections OrderAddMonoidHom (toFun → apply, -toAddMonoidHom)
initialize_simps_projections OrderMonoidHom (toFun → apply, -toMonoidHom)

@[to_additive]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (α →*o β) α β where
  map_rel f _ _ h := f.monotone' h

@[to_additive]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidHomClass (α →*o β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
/-
**OrderMonoidHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：ext (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/-
**OrderMonoidHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：toFun_eq_coe (f : α ->*o β) : f.toFun = (f : α -> β)
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α →*o β) : f.toFun = (f : α → β) :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_mk (f : α ->* β) (h) : (OrderMonoidHom.mk f h : α -> β) = f
参数：f : α ->* β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α →* β) (h) : (OrderMonoidHom.mk f h : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：mk_coe (f : α ->*o β) (h) : OrderMonoidHom.mk (f : α ->* β) h = f
参数：f : α ->*o β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
-/
theorem mk_coe (f : α →*o β) (h) : OrderMonoidHom.mk (f : α →* β) h = f := by
  ext
  rfl

/-- Reinterpret an ordered monoid homomorphism as an order homomorphism. -/
@[to_additive /-- Reinterpret an ordered additive monoid homomorphism as an order homomorphism. -/]
/-
**OrderMonoidHom.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：toOrderHom (f : α ->*o β) : α ->o β
参数：f : α ->*o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] 
(self : α →*o …

--- 原说明 ---
Reinterpret an ordered monoid homomorphism as an order homomorphism.
-/
def toOrderHom (f : α →*o β) : α →o β :=
  { f with }

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_monoidHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_monoidHom (f : α ->*o β) : ((f : α ->* β) : α -> β) = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
-/
theorem coe_monoidHom (f : α →*o β) : ((f : α →* β) : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_orderHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_orderHom (f : α ->*o β) : ((f : α ->o β) : α -> β) = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneC
lass β], OrderHomClass…
-/
theorem coe_orderHom (f : α →*o β) : ((f : α →o β) : α → β) = f :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.toMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom
`。
形式化陈述：toMonoidHom_injective : Injective (toMonoidHom : _ -> α ->* β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : _ → α →* β) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
/-
**OrderMonoidHom.toOrderHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`
。
形式化陈述：toOrderHom_injective : Injective (toOrderHom : _ -> α ->o β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toOrderHom_injective : Injective (toOrderHom : _ → α →o β) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h using 0

/-- Copy of an `OrderMonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive /-- Copy of an `OrderAddMonoidHom` with a new `toFun` equal to the old one. Useful to
fix definitional equalities. -/]
/-
**OrderMonoidHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Preorder α] →       [inst_
1 : Preorder β] →         [inst_2 : MulOneClass α] → [inst_3 : MulOneClass β] → 
(f : α →*o β) → (f' : α → β) → f' = ⇑f → α →*o β
参数：f : α →*o β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
  { f.toMonoidHom.copy f' h with toFun := f', monotone' := h.symm.subst f.monotone' }

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_copy (f : α ->*o β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->*o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →*o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：copy_eq (f : α ->*o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->*o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- The identity map as an ordered monoid homomorphism. -/
@[to_additive /-- The identity map as an ordered additive monoid homomorphism. -/]
/-
**OrderMonoidHom.id** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：(α : Type u_2) → [inst : Preorder α] → [inst_1 : MulOneClass α] → α →*o α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun

--- 原说明 ---
The identity map as an ordered monoid homomorphism.
-/
protected def id : α →*o α :=
  { MonoidHom.id α, OrderHom.id with }

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_id : ⇑(OrderMonoidHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(OrderMonoidHom.id α) = id :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →*o α) :=
  ⟨OrderMonoidHom.id α⟩

variable {α}

/-- Composition of `OrderMonoidHom`s as an `OrderMonoidHom`. -/
@[to_additive /-- Composition of `OrderAddMonoidHom`s as an `OrderAddMonoidHom` -/]
/-
**OrderMonoidHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp (f : β ->*o γ) (g : α ->*o β) : α ->*o γ
参数：f : β ->*o γ；g : α ->*o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
· 使用定理 `OrderMonoidHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneC
lass β], OrderHomClass…
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun

--- 原说明 ---
Composition of `OrderMonoidHom`s as an `OrderMonoidHom`.
-/
def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
  { f.toMonoidHom.comp (g : α →* β), f.toOrderHom.comp (g : α →o β) with }

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_comp (f : β ->*o γ) (g : α ->*o β) : (f.comp g : α -> γ) = f ∘ g
参数：f : β ->*o γ；g : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : β →*o γ) (g : α →*o β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp_apply (f : β ->*o γ) (g : α ->*o β) (a : α) : (f.comp g) a = f (g a)
参数：f : β ->*o γ；g : α ->*o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.coe_comp_monoidHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_comp_monoidHom (f : β ->*o γ) (g : α ->*o β) : (f.comp g : α ->* γ) = 
(f : β ->* γ).comp g
参数：f : β ->*o γ；g : α ->*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
-/
theorem coe_comp_monoidHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →* γ) = (f : β →* γ).comp g :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.coe_comp_orderHom** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_comp_orderHom (f : β ->*o γ) (g : α ->*o β) : (f.comp g : α ->o γ) = (
f : β ->o γ).comp g
参数：f : β ->*o γ；g : α ->*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneC
lass β], OrderHomClass…
-/
theorem coe_comp_orderHom (f : β →*o γ) (g : α →*o β) :
    (f.comp g : α →o γ) = (f : β →o γ).comp g :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp_assoc (f : γ ->*o δ) (g : β ->*o γ) (h : α ->*o β) : (f.comp g).comp 
h = f.comp (g.comp h)
参数：f : γ ->*o δ；g : β ->*o γ；h : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp_id (f : α ->*o β) : f.comp (OrderMonoidHom.id α) = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : α →*o β) : f.comp (OrderMonoidHom.id α) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：id_comp (f : α ->*o β) : (OrderMonoidHom.id β).comp f = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : α →*o β) : (OrderMonoidHom.id β).comp f = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：cancel_right {g₁ g₂ : β ->*o γ} {f : α ->*o β} (hf : Function.Surjective f
) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：cancel_left {g : β ->*o γ} {f₁ f₂ : α ->*o β} (hg : Function.Injective g) 
: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderMonoidHom.comp_apply`：comp_apply (f : β ->*o γ) (g : α ->*o β) (a :
 α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive /-- `0` is the homomorphism sending all elements to `0`. -/]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is the homomorphism sending all elements to `1`.
-/
instance : One (α →*o β) :=
  ⟨{ (1 : α →* β) with monotone' := monotone_const }⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_one : ⇑(1 : α ->*o β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : α →*o β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：one_apply (a : α) : (1 : α ->*o β) a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : α) : (1 : α →*o β) a = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.one_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：one_comp (f : α ->*o β) : (1 : β ->*o γ).comp f = 1
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_comp (f : α →*o β) : (1 : β →*o γ).comp f = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp_one (f : β ->*o γ) : f.comp (1 : α ->*o β) = 1
参数：f : β ->*o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
-/
theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 :=
  ext fun _ => map_one f

end Preorder

section Mul

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
@[to_additive /-- For two ordered additive monoid morphisms `f` and `g`, their product is the
ordered additive monoid morphism sending `a` to `f a + g a`. -/]
/-
**OrderMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOrderedMonoid β] : Mul (α →*o β) :=
  ⟨fun f g => { (f * g : α →* β) with monotone' := f.monotone'.mul' g.monotone' }⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：coe_mul [IsOrderedMonoid β] (f g : α ->*o β) : ⇑(f * g) = f * g
参数：f g : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [IsOrderedMonoid β] (f g : α →*o β) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：mul_apply [IsOrderedMonoid β] (f g : α ->*o β) (a : α) : (f * g) a = f a *
 g a
参数：f g : α ->*o β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [IsOrderedMonoid β] (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：mul_comp [IsOrderedMonoid γ] (g₁ g₂ : β ->*o γ) (f : α ->*o β) : (g₁ * g₂)
.comp f = g₁.comp f * g₂.comp f
参数：g₁ g₂ : β ->*o γ；f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp [IsOrderedMonoid γ] (g₁ g₂ : β →*o γ) (f : α →*o β) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：comp_mul [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β ->*o γ) (f₁ f₂ : α
 ->*o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂
参数：g : β ->*o γ；f₁ f₂ : α ->*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `OrderMonoidHom.instMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOne
Class β], MonoidHomClas…
-/
theorem comp_mul [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β →*o γ) (f₁ f₂ : α →*o β) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
  ext fun _ => map_mul g _ _

end Mul

section OrderedCommMonoid

variable {_ : Preorder α} {_ : Preorder β} {_ : MulOneClass α} {_ : MulOneClass β}

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.toMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：toMonoidHom_eq_coe (f : α ->*o β) : f.toMonoidHom = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidHom_eq_coe (f : α →*o β) : f.toMonoidHom = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.toOrderHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：toOrderHom_eq_coe (f : α ->*o β) : f.toOrderHom = f
参数：f : α ->*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderHom_eq_coe (f : α →*o β) : f.toOrderHom = f :=
  rfl

end OrderedCommMonoid

section OrderedCommGroup

variable {_ : CommGroup α} {_ : Preorder α} {_ : CommGroup β} {_ : PartialOrder β}

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      /-- Makes an ordered additive group homomorphism from a proof that the map preserves
      addition. -/]
/-
**OrderMonoidHom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：mk' (f : α -> β) (hf : Monotone f) (map_mul : forall a b : α, f (a * b) = 
f a * f b) : α ->*o β
参数：f : α -> β；hf : Monotone f；map_mul : forall a b : α, f (a * b) = f a * f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }

end OrderedCommGroup

end OrderMonoidHom

namespace OrderMonoidIso

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [Mul α] [Mul β]
  [Mul γ] [Mul δ] {f g : α ≃*o β}

@[to_additive]
/-
**OrderMonoidIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃*o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩⟩, _⟩ := g
    congr

@[to_additive]
/-
**OrderMonoidIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderIsoClass (α ≃*o β) α β where
  map_le_map_iff f := f.map_le_map_iff'

@[to_additive]
/-
**OrderMonoidIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulEquivClass (α ≃*o β) α β where
  map_mul f := map_mul f.toMulEquiv

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
/-
**OrderMonoidIso.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：ext (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/-
**OrderMonoidIso.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：toFun_eq_coe (f : α ≃*o β) : f.toFun = (f : α -> β)
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α ≃*o β) : f.toFun = (f : α → β) :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_mk (f : α ≃* β) (h) : (OrderMonoidIso.mk f h : α -> β) = f
参数：f : α ≃* β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α ≃* β) (h) : (OrderMonoidIso.mk f h : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：mk_coe (f : α ≃*o β) (h) : OrderMonoidIso.mk (f : α ≃* β) h = f
参数：f : α ≃*o β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
-/
theorem mk_coe (f : α ≃*o β) (h) : OrderMonoidIso.mk (f : α ≃* β) h = f := rfl

/-- Reinterpret an ordered monoid isomorphism as an order isomorphism. -/
@[to_additive
/-- Reinterpret an ordered additive monoid isomorphism as an order isomorphism. -/]
/-
**OrderMonoidIso.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso`。
形式化陈述：toOrderIso (f : α ≃*o β) : α ≃o β
参数：f : α ≃*o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toOrderIso (f : α ≃*o β) : α ≃o β :=
  { f with
    map_rel_iff' := map_le_map_iff f }

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_mulEquiv (f : α ≃*o β) : ((f : α ≃* β) : α -> β) = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
-/
theorem coe_mulEquiv (f : α ≃*o β) : ((f : α ≃* β) : α → β) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_orderIso** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_orderIso (f : α ≃*o β) : ((f : α ->o β) : α -> β) = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : LE α] [inst_1 : LE β] [inst_2 : EquivLike F α β]   [OrderIsoClass 
F α β], OrderHomCla…
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
-/
theorem coe_orderIso (f : α ≃*o β) : ((f : α →o β) : α → β) = f :=
  rfl

@[to_additive]
/-
**OrderMonoidIso.toMulEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`
。
形式化陈述：toMulEquiv_injective : Injective (toMulEquiv : _ -> α ≃* β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toMulEquiv_injective : Injective (toMulEquiv : _ → α ≃* β) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h using 0

@[to_additive]
/-
**OrderMonoidIso.toOrderIso_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`
。
形式化陈述：toOrderIso_injective : Injective (toOrderIso : _ -> α ≃o β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem toOrderIso_injective : Injective (toOrderIso : _ → α ≃o β) := fun f g h =>
  ext <| by convert! DFunLike.ext_iff.1 h using 0

variable (α)

/-- The identity map as an ordered monoid isomorphism. -/
@[to_additive /-- The identity map as an ordered additive monoid isomorphism. -/]
/-
**OrderMonoidIso.refl** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso`。
形式化陈述：(α : Type u_2) → [inst : Preorder α] → [inst_1 : Mul α] → α ≃*o α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as an ordered monoid isomorphism.
-/
protected def refl : α ≃*o α :=
  { MulEquiv.refl α with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_refl : ⇑(OrderMonoidIso.refl α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(OrderMonoidIso.refl α) = id :=
  rfl

@[to_additive]
/-
**OrderMonoidIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderMonoidIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α ≃*o α) :=
  ⟨OrderMonoidIso.refl α⟩

variable {α}

/-- Transitivity of multiplication-preserving order isomorphisms -/
@[to_additive (attr := trans) /-- Transitivity of addition-preserving order isomorphisms -/]
/-
**OrderMonoidIso.trans** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso`。
形式化陈述：trans (f : α ≃*o β) (g : β ≃*o γ) : α ≃*o γ
参数：f : α ≃*o β；g : β ≃*o γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β

--- 原说明 ---
Transitivity of multiplication-preserving order isomorphisms
-/
def trans (f : α ≃*o β) (g : β ≃*o γ) : α ≃*o γ :=
  { (f : α ≃* β).trans g with map_le_map_iff' := by simp }

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_trans (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α -> γ) = g ∘ f
参数：f : α ≃*o β；g : β ≃*o γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α → γ) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a : α) : (f.trans g) a = g (f a)
参数：f : α ≃*o β；g : β ≃*o γ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[to_additive]
/-
**OrderMonoidIso.coe_trans_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_trans_mulEquiv (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α ≃* γ) = (f
 : α ≃* β).trans g
参数：f : α ≃*o β；g : β ≃*o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
-/
theorem coe_trans_mulEquiv (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃* γ) = (f : α ≃* β).trans g :=
  rfl

@[to_additive]
/-
**OrderMonoidIso.coe_trans_orderIso** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_trans_orderIso (f : α ≃*o β) (g : β ≃*o γ) : (f.trans g : α ≃o γ) = (f
 : α ≃o β).trans g
参数：f : α ≃*o β；g : β ≃*o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
-/
theorem coe_trans_orderIso (f : α ≃*o β) (g : β ≃*o γ) :
    (f.trans g : α ≃o γ) = (f : α ≃o β).trans g :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：trans_assoc (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ) : (f.trans g).trans 
h = f.trans (g.trans h)
参数：f : α ≃*o β；g : β ≃*o γ；h : γ ≃*o δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc (f : α ≃*o β) (g : β ≃*o γ) (h : γ ≃*o δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：trans_refl (f : α ≃*o β) : f.trans (OrderMonoidIso.refl β) = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_refl (f : α ≃*o β) : f.trans (OrderMonoidIso.refl β) = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：refl_trans (f : α ≃*o β) : (OrderMonoidIso.refl α).trans f = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_trans (f : α ≃*o β) : (OrderMonoidIso.refl α).trans f = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：cancel_right {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f) :
 g₁.trans f = g₂.trans f ↔ g₁ = g₂
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderMonoidIso.trans_apply`：trans_apply (f : α ≃*o β) (g : β ≃*o γ) (a :
 α) : (f.trans g) a = g (f a)
-/
theorem cancel_right {g₁ g₂ : α ≃*o β} {f : β ≃*o γ} (hf : Function.Injective f) :
    g₁.trans f = g₂.trans f ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← trans_apply, h, trans_apply], by rintro rfl; rfl⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：cancel_left {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g) :
 g.trans f₁ = g.trans f₂ ↔ f₁ = f₂
参数：hg : Function.Surjective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem cancel_left {g : α ≃*o β} {f₁ f₂ : β ≃*o γ} (hg : Function.Surjective g) :
    g.trans f₁ = g.trans f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, fun _ => by congr⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.toMulEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：toMulEquiv_eq_coe (f : α ≃*o β) : f.toMulEquiv = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_eq_coe (f : α ≃*o β) : f.toMulEquiv = f :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.toOrderIso_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：toOrderIso_eq_coe (f : α ≃*o β) : f.toOrderIso = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderIso_eq_coe (f : α ≃*o β) : f.toOrderIso = f :=
  rfl

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) /-- The inverse of an order isomorphism is an order isomorphism. -/]
/-
**OrderMonoidIso.symm** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm (f : α ≃*o β) : β ≃*o α
参数：f : α ≃*o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an isomorphism is an isomorphism.
-/
def symm (f : α ≃*o β) : β ≃*o α :=
  ⟨f.toMulEquiv.symm, f.toOrderIso.symm.map_rel_iff⟩

/-- See Note [custom simps projection]. -/
@[to_additive /-- See Note [custom simps projection]. -/]
/-
**OrderMonoidIso.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso.Simps`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preord
er β] → [inst_2 : Mul α] → [inst_3 : Mul β] → (α ≃*o β) → α → β
参数：α ≃*o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.apply (h : α ≃*o β) : α → β :=
  h

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection]. -/]
/-
**OrderMonoidIso.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso.Simp
s`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preord
er β] → [inst_2 : Mul α] → [inst_3 : Mul β] → (α ≃*o β) → β → α
参数：α ≃*o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : α ≃*o β) : β → α :=
  h.symm

initialize_simps_projections OrderAddMonoidIso (toFun → apply, invFun → symm_apply)
initialize_simps_projections OrderMonoidIso (toFun → apply, invFun → symm_apply)

@[to_additive]
/-
**OrderMonoidIso.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：invFun_eq_symm {f : α ≃*o β} : f.invFun = f.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {f : α ≃*o β} : f.invFun = f.symm := rfl

/-- `simp`-normal form of `invFun_eq_symm`. -/
@[to_additive (attr := simp)]
/-
**OrderMonoidIso.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：coe_toEquiv_symm (f : α ≃*o β) : ((f : α ≃ β).symm : β -> α) = f.symm
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`simp`-normal form of `invFun_eq_symm`.
-/
theorem coe_toEquiv_symm (f : α ≃*o β) : ((f : α ≃ β).symm : β → α) = f.symm := rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.equivLike_inv_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso
`。
形式化陈述：equivLike_inv_eq_symm (f : α ≃*o β) : EquivLike.inv f = f.symm
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivLike_inv_eq_symm (f : α ≃*o β) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：toEquiv_symm (f : α ≃*o β) : (f.symm : β ≃ α) = (f : α ≃ β).symm
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm (f : α ≃*o β) : (f.symm : β ≃ α) = (f : α ≃ β).symm := rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_symm (f : α ≃*o β) : f.symm.symm = f
参数：f : α ≃*o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : α ≃*o β) : f.symm.symm = f := rfl

@[to_additive]
/-
**OrderMonoidIso.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_bijective : Function.Bijective (symm : (α ≃*o β) -> β ≃*o α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `OrderMonoidIso.symm_symm`：symm_symm (f : α ≃*o β) : f.symm.symm = f
-/
theorem symm_bijective : Function.Bijective (symm : (α ≃*o β) → β ≃*o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：refl_symm : (OrderMonoidIso.refl α).symm = .refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (OrderMonoidIso.refl α).symm = .refl α := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/-
**OrderMonoidIso.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：apply_symm_apply (e : α ≃*o β) (y : β) : e (e.symm y) = y
参数：e : α ≃*o β；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : α ≃*o β) (y : β) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/-
**OrderMonoidIso.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_apply_apply (e : α ≃*o β) (x : α) : e.symm (e x) = x
参数：e : α ≃*o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : α ≃*o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_comp_self (e : α ≃*o β) : e.symm ∘ e = id
参数：e : α ≃*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderMonoidIso.symm_apply_apply`：symm_apply_apply (e : α ≃*o β) (x : α) 
: e.symm (e x) = x
-/
theorem symm_comp_self (e : α ≃*o β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/-
**OrderMonoidIso.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：self_comp_symm (e : α ≃*o β) : e ∘ e.symm = id
参数：e : α ≃*o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderMonoidIso.apply_symm_apply`：apply_symm_apply (e : α ≃*o β) (y : β) 
: e (e.symm y) = y
-/
theorem self_comp_symm (e : α ≃*o β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/-
**OrderMonoidIso.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_apply_eq (e : α ≃*o β) {x y} : e.symm x = y ↔ x = e y
参数：e : α ≃*o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : α ≃*o β) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/-
**OrderMonoidIso.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：eq_symm_apply (e : α ≃*o β) {x y} : y = e.symm x ↔ e y = x
参数：e : α ≃*o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : α ≃*o β) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/-
**OrderMonoidIso.apply_eq_iff_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidI
so`。
形式化陈述：apply_eq_iff_symm_apply (e : α ≃*o β) {x : α} {y : β} : e x = y ↔ x = e.sy
mm y
参数：e : α ≃*o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderMonoidIso.eq_symm_apply`：eq_symm_apply (e : α ≃*o β) {x y} : y = e.
symm x ↔ e y = x
-/
theorem apply_eq_iff_symm_apply (e : α ≃*o β) {x : α} {y : β} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/-
**OrderMonoidIso.eq_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：eq_comp_symm (e : α ≃*o β) (f : β -> α) (g : α -> α) : f = g ∘ e.symm ↔ f 
∘ e = g
参数：e : α ≃*o β；f : β -> α；g : α -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_comp_symm`：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : f = g ∘ e.symm ↔ f ∘ e = g
-/
theorem eq_comp_symm (e : α ≃*o β) (f : β → α) (g : α → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/-
**OrderMonoidIso.comp_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：comp_symm_eq (e : α ≃*o β) (f : β -> α) (g : α -> α) : g ∘ e.symm = f ↔ g 
= f ∘ e
参数：e : α ≃*o β；f : β -> α；g : α -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.comp_symm_eq`：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : g ∘ e.symm = f ↔ g = f ∘ e
-/
theorem comp_symm_eq (e : α ≃*o β) (f : β → α) (g : α → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/-
**OrderMonoidIso.eq_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：eq_symm_comp (e : α ≃*o β) (f : α -> α) (g : α -> β) : f = e.symm ∘ g ↔ e 
∘ f = g
参数：e : α ≃*o β；f : α -> α；g : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
-/
theorem eq_symm_comp (e : α ≃*o β) (f : α → α) (g : α → β) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/-
**OrderMonoidIso.symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_comp_eq (e : α ≃*o β) (f : α -> α) (g : α -> β) : e.symm ∘ g = f ↔ g 
= e ∘ f
参数：e : α ≃*o β；f : α -> α；g : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_comp_eq`：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : e.symm ∘ g = f ↔ g = e ∘ f
-/
theorem symm_comp_eq (e : α ≃*o β) (f : α → α) (g : α → β) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive]
/-
**OrderMonoidIso.lt_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `OrderMonoidIso`。
形式化陈述：lt_symm_apply (e : α ≃*o β) {x : α} {y : β} : x < e.symm y ↔ e x < y
参数：e : α ≃*o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lt_symm_apply`：lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
 e.symm y ↔ e x < y
-/
lemma lt_symm_apply (e : α ≃*o β) {x : α} {y : β} : x < e.symm y ↔ e x < y :=
  e.toOrderIso.lt_symm_apply

@[to_additive]
/-
**OrderMonoidIso.symm_apply_lt** 是 Mathlib 中的一个引理，位于命名空间 `OrderMonoidIso`。
形式化陈述：symm_apply_lt (e : α ≃*o β) {x : α} {y : β} : e.symm y < x ↔ y < e x
参数：e : α ≃*o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_lt`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder
 α] [inst_1 : Preorder β] (e : α ≃o β) {x : α} {y : β},   e.symm y < x ↔ y < e x
-/
lemma symm_apply_lt (e : α ≃*o β) {x : α} {y : β} : e.symm y < x ↔ y < e x :=
  e.toOrderIso.symm_apply_lt

variable (f)

@[to_additive]
/-
**OrderMonoidIso.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : Mul α] [inst_3 : Mul β]   (f : α ≃*o β), StrictMono ⇑f
参数：f : α ≃*o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
-/
protected lemma strictMono : StrictMono f :=
  strictMono_of_le_iff_le fun _ _ ↦ (map_le_map_iff _).symm

@[to_additive]
/-
**OrderMonoidIso.strictMono_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : Mul α] [inst_3 : Mul β]   (f : α ≃*o β), StrictMono ⇑f.symm
参数：f : α ≃*o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma strictMono_symm : StrictMono f.symm :=
  strictMono_of_le_iff_le <| fun a b ↦ by
    rw [← map_le_map_iff f]
    convert! Iff.rfl <;>
    exact f.toEquiv.apply_symm_apply _

end Preorder

section OrderedCommGroup

variable {_ : CommGroup α} {_ : Preorder α} {_ : CommGroup β} {_ : PartialOrder β}

/-- Makes an ordered group isomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      /-- Makes an ordered additive group isomorphism from a proof that the map preserves
      addition. -/]
/-
**OrderMonoidIso.mk'** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidIso`。
形式化陈述：mk' (f : α ≃ β) (hf : forall {a b}, f a <= f b ↔ a <= b) (map_mul : forall
 a b : α, f (a * b) = f a * f b) : α ≃*o β
参数：f : α ≃ β；hf : forall {a b}, f a <= f b ↔ a <= b；map_mul : forall a b : α, f 
(a * b) = f a * f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk' (f : α ≃ β) (hf : ∀ {a b}, f a ≤ f b ↔ a ≤ b) (map_mul : ∀ a b : α, f (a * b) = f a * f b) :
    α ≃*o β :=
  { MulEquiv.mk' f map_mul with map_le_map_iff' := hf }

end OrderedCommGroup

end OrderMonoidIso

