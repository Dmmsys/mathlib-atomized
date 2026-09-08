/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Ring.Defs

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `NonnegHomClass`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `SubadditiveHomClass`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `SubmultiplicativeHomClass`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `MulLEAddHomClass`: `∀ f a b, f (a * b) ≤ f a + f b`
* `NonarchimedeanHomClass`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

Group norms
* `AddGroupSeminormClass`: Homs are nonnegative, subadditive, even and preserve zero.
* `GroupSeminormClass`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `AddGroupNormClass`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `GroupNormClass`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

Ring norms
* `RingSeminormClass`: Homs are submultiplicative group norms.
* `RingNormClass`: Homs are ring seminorms that are also additive group norms.
* `MulRingSeminormClass`: Homs are ring seminorms that are multiplicative.
* `MulRingNormClass`: Homs are ring norms that are multiplicative.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`Analysis.Normed.Group.Seminorm` and `Analysis.Normed.Ring.Seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

public section

assert_not_exists Field

library_note «out-param inheritance» /--
Diamond inheritance cannot depend on `outParam`s in the following circumstances:
* there are three classes `Top`, `Middle`, `Bottom`
* all of these classes have a parameter `(α : outParam _)`
* all of these classes have an instance parameter `[Root α]` that depends on this `outParam`
* the `Root` class has two child classes: `Left` and `Right`, these are siblings in the hierarchy
* the instance `Bottom.toMiddle` takes a `[Left α]` parameter
* the instance `Middle.toTop` takes a `[Right α]` parameter
* there is a `Leaf` class that inherits from both `Left` and `Right`.

In that case, given instances `Bottom α` and `Leaf α`, Lean cannot synthesize a `Top α` instance,
even though the hypotheses of the instances `Bottom.toMiddle` and `Middle.toTop` are satisfied.

There are two workarounds:
* You could replace the bundled inheritance implemented by the instance `Middle.toTop` with
  unbundled inheritance implemented by adding a `[Top α]` parameter to the `Middle` class. This is
  the preferred option since it is also more compatible with Lean 4, at the cost of being more work
  to implement and more verbose to use.
* You could weaken the `Bottom.toMiddle` instance by making it depend on a subclass of
  `Middle.toTop`'s parameter, in this example replacing `[Left α]` with `[Leaf α]`.
-/

open Function

variable {ι F α β γ δ : Type*}

/-! ### Basics -/

/-- `NonnegHomClass F α β` states that `F` is a type of nonnegative morphisms. -/
/-
**NonnegHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) → (α : outParam (Type u_8)) → (β : outParam (Type u_9)) → [
Zero β] → [LE β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonnegHomClass F α β` states that `F` is a type of nonnegative morphisms.
-/
class NonnegHomClass (F : Type*) (α β : outParam Type*) [Zero β] [LE β] [FunLike F α β] : Prop where
  /-- the image of any element is nonnegative. -/
  apply_nonneg (f : F) : ∀ a, 0 ≤ f a

/-- `SubadditiveHomClass F α β` states that `F` is a type of subadditive morphisms. -/
/-
**SubadditiveHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) → (β : outParam (Type u_9)) →
 [Add α] → [Add β] → [LE β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubadditiveHomClass F α β` states that `F` is a type of subadditive morphisms.
-/
class SubadditiveHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [Add β] [LE β] [FunLike F α β] : Prop where
  /-- the image of a sum is less or equal than the sum of the images. -/
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b

/-- `SubmultiplicativeHomClass F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubadditiveHomClass]
/-
**SubmultiplicativeHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) → (β : outParam (Type u_9)) →
 [Mul α] → [Mul β] → [LE β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubmultiplicativeHomClass F α β` states that `F` is a type of submultiplicative
 morphisms.
-/
class SubmultiplicativeHomClass (F : Type*) (α β : outParam (Type*)) [Mul α] [Mul β] [LE β]
    [FunLike F α β] : Prop where
  /-- the image of a product is less or equal than the product of the images. -/
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b

/-- `MulLEAddHomClass F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubadditiveHomClass]
/-
**MulLEAddHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) → (β : outParam (Type u_9)) →
 [Mul α] → [Add β] → [LE β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulLEAddHomClass F α β` states that `F` is a type of subadditive morphisms.
-/
class MulLEAddHomClass (F : Type*) (α β : outParam Type*) [Mul α] [Add β] [LE β] [FunLike F α β] :
    Prop where
  /-- the image of a product is less or equal than the sum of the images. -/
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b

/-- `NonarchimedeanHomClass F α β` states that `F` is a type of non-archimedean morphisms. -/
/-
**NonarchimedeanHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) → (β : outParam (Type u_9)) →
 [Add α] → [LinearOrder β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonarchimedeanHomClass F α β` states that `F` is a type of non-archimedean morp
hisms.
-/
class NonarchimedeanHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [LinearOrder β] [FunLike F α β] : Prop where
  /-- the image of a sum is less or equal than the maximum of the images. -/
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)

export NonnegHomClass (apply_nonneg)

export SubadditiveHomClass (map_add_le_add)

export SubmultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonarchimedeanHomClass (map_add_le_max)

attribute [simp] apply_nonneg

variable [FunLike F α β]

@[to_additive]
/-
**le_map_mul_map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_map_mul_map_div [Group α] [CommMagma β] [LE β] [SubmultiplicativeHomCla
ss F α β] (f : F) (a b : α) : f a <= f b * f (a / b)
参数：f : F；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…
-/
theorem le_map_mul_map_div [Group α] [CommMagma β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel] using map_mul_le_mul f (a / b) b

@[to_additive existing]
/-
**le_map_add_map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_map_add_map_div [Group α] [AddCommMagma β] [LE β] [MulLEAddHomClass F α
 β] (f : F) (a b : α) : f a <= f b + f (a / b)
参数：f : F；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MulLEAddHomClass.map_mul_le_add`：∀ {F : Type u_7} {α : outParam (Type u_
8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Add β} {inst_2 : LE β}   
{inst_3 : FunLike F α…
-/
theorem le_map_add_map_div [Group α] [AddCommMagma β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel] using map_mul_le_add f (a / b) b

@[to_additive]
/-
**le_map_div_mul_map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_map_div_mul_map_div [Group α] [Mul β] [LE β] [SubmultiplicativeHomClass
 F α β] (f : F) (a b c : α) : f (a / c) <= f (a / b) * f (b / c)
参数：f : F；a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `SubmultiplicativeHomClass.map_mul_le_mul`：∀ {F : Type u_7} {α : outParam
 (Type u_8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Mul β} {inst_2 :
 LE β}   {inst_3 : FunLike F α…
-/
theorem le_map_div_mul_map_div [Group α] [Mul β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel] using map_mul_le_mul f (a / b) (b / c)

@[to_additive existing]
/-
**le_map_div_add_map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_map_div_add_map_div [Group α] [Add β] [LE β] [MulLEAddHomClass F α β] (
f : F) (a b c : α) : f (a / c) <= f (a / b) + f (b / c)
参数：f : F；a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `MulLEAddHomClass.map_mul_le_add`：∀ {F : Type u_7} {α : outParam (Type u_
8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Add β} {inst_2 : LE β}   
{inst_3 : FunLike F α…
-/
theorem le_map_div_add_map_div [Group α] [Add β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel] using map_mul_le_add f (a / b) (b / c)

/-! ### Group (semi)norms -/


/-- `AddGroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the additive
group `α`.

You should extend this class when you extend `AddGroupSeminorm`. -/
/-
**AddGroupSeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [AddGroup α] → [AddCommMonoid β] → [PartialOrder β] → [FunLike F α β] → Pro
p
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddGroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on
 the additive
group `α`.

You should extend this class when you extend `AddGroupSeminorm`.
-/
class AddGroupSeminormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends SubadditiveHomClass F α β where
  /-- The image of zero is zero. -/
  map_zero (f : F) : f 0 = 0
  /-- The map is invariant under negation of its argument. -/
  map_neg_eq_map (f : F) (a : α) : f (-a) = f a

/-- `GroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the group `α`.

You should extend this class when you extend `GroupSeminorm`. -/
@[to_additive]
/-
**GroupSeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [Group α] → [AddCommMonoid β] → [PartialOrder β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on th
e group `α`.

You should extend this class when you extend `GroupSeminorm`.
-/
class GroupSeminormClass (F : Type*) (α β : outParam Type*)
    [Group α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends MulLEAddHomClass F α β where
  /-- The image of one is zero. -/
  map_one_eq_zero (f : F) : f 1 = 0
  /-- The map is invariant under inversion of its argument. -/
  map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a

/-- `AddGroupNormClass F α` states that `F` is a type of `β`-valued norms on the additive group
`α`.

You should extend this class when you extend `AddGroupNorm`. -/
/-
**AddGroupNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [AddGroup α] → [AddCommMonoid β] → [PartialOrder β] → [FunLike F α β] → Pro
p
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddGroupNormClass F α` states that `F` is a type of `β`-valued norms on the add
itive group
`α`.

You should extend this class when you extend `AddGroupNorm`.
-/
class AddGroupNormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β where
  /-- The argument is zero if its image under the map is zero. -/
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0

/-- `GroupNormClass F α` states that `F` is a type of `β`-valued norms on the group `α`.

You should extend this class when you extend `GroupNorm`. -/
@[to_additive]
/-
**GroupNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [Group α] → [AddCommMonoid β] → [PartialOrder β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GroupNormClass F α` states that `F` is a type of `β`-valued norms on the group 
`α`.

You should extend this class when you extend `GroupNorm`.
-/
class GroupNormClass (F : Type*) (α β : outParam Type*)
    [Group α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends GroupSeminormClass F α β where
  /-- The argument is one if its image under the map is zero. -/
  eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1

export AddGroupSeminormClass (map_neg_eq_map)

export GroupSeminormClass (map_one_eq_zero map_inv_eq_map)

export AddGroupNormClass (eq_zero_of_map_eq_zero)

export GroupNormClass (eq_one_of_map_eq_zero)

attribute [simp] map_one_eq_zero map_neg_eq_map map_inv_eq_map

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) AddGroupSeminormClass.toZeroHomClass [AddGroup α]
    [AddCommMonoid β] [PartialOrder β] [AddGroupSeminormClass F α β] : ZeroHomClass F α β :=
  { ‹AddGroupSeminormClass F α β› with }

section GroupSeminormClass

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

@[to_additive]
/-
**map_div_le_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_div_le_add : f (x / y) <= f x + f y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GroupSeminormClass.map_inv_eq_map`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   {i
nst_2 : PartialOrder β}…
· 使用定理 `MulLEAddHomClass.map_mul_le_add`：∀ {F : Type u_7} {α : outParam (Type u_
8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Add β} {inst_2 : LE β}   
{inst_3 : FunLike F α…
· 使用定理 `GroupSeminormClass.toMulLEAddHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β} 
  {inst_2 : PartialOrder β}…
-/
theorem map_div_le_add : f (x / y) ≤ f x + f y := by
  rw [div_eq_mul_inv, ← map_inv_eq_map f y]
  exact map_mul_le_add _ _ _

@[to_additive]
/-
**map_div_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_div_rev : f (x / y) = f (y / x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `GroupSeminormClass.map_inv_eq_map`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   {i
nst_2 : PartialOrder β}…
-/
theorem map_div_rev : f (x / y) = f (y / x) := by rw [← inv_div, map_inv_eq_map]

@[to_additive]
/-
**map_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_mul {α : Type*} [FunLike F α β] [CommGroup α] [GroupSeminormClass 
F α β] (x y : α) : f (x⁻¹ * y) = f (x * y⁻¹)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GroupSeminormClass.map_inv_eq_map`：∀ {F : Type u_7} {α : outParam (Type 
u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   {i
nst_2 : PartialOrder β}…
· 使用定理 `inv_mul'`：inv_mul' : (a * b)⁻¹ = a⁻¹ / b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem map_inv_mul {α : Type*} [FunLike F α β] [CommGroup α] [GroupSeminormClass F α β] (x y : α) :
    f (x⁻¹ * y) = f (x * y⁻¹) := by
  rw [← map_inv_eq_map, inv_mul', inv_inv, div_eq_mul_inv]

@[to_additive]
/-
**le_map_add_map_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_map_add_map_div' : f x <= f y + f (y / x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div_rev`：map_div_rev : f (x / y) = f (y / x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MulLEAddHomClass.map_mul_le_add`：∀ {F : Type u_7} {α : outParam (Type u_
8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Add β} {inst_2 : LE β}   
{inst_3 : FunLike F α…
· 使用定理 `GroupSeminormClass.toMulLEAddHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β} 
  {inst_2 : PartialOrder β}…
-/
theorem le_map_add_map_div' : f x ≤ f y + f (y / x) := by
  simpa only [add_comm, map_div_rev, div_mul_cancel] using map_mul_le_add f (x / y) y

end GroupSeminormClass

@[to_additive]
/-
**abs_sub_map_le_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_sub_map_le_div [Group α] [AddCommGroup β] [LinearOrder β] [IsOrderedAd
dMonoid β] [GroupSeminormClass F α β] (f : F) (x y : α) : |f x - f y| <= f (x / 
y)
参数：f : F；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_map_add_map_div`：le_map_add_map_div [Group α] [AddCommMagma β] [LE β]
 [MulLEAddHomClass F α β] (f : F) (a b : α) : f a <= f b + f (a / b)
· 使用定理 `GroupSeminormClass.toMulLEAddHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β} 
  {inst_2 : PartialOrder β}…
· 使用定理 `le_map_add_map_div'`：le_map_add_map_div' : f x <= f y + f (y / x)
-/
theorem abs_sub_map_le_div [Group α] [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupSeminormClass F α β]
    (f : F) (x y : α) : |f x - f y| ≤ f (x / y) := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GroupSeminormClass.toNonnegHomClass [Group α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [GroupSeminormClass F α β] :
    NonnegHomClass F α β :=
  { ‹GroupSeminormClass F α β› with
    apply_nonneg := fun f a =>
      (nsmul_nonneg_iff two_ne_zero).1 <| by
        rw [two_nsmul, ← map_one_eq_zero f, ← div_self' a]
        exact map_div_le_add _ _ _ }

section GroupNormClass

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupNormClass F α β] (f : F) {x : α}

@[to_additive]
/-
**map_eq_zero_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupNormClass.eq_one_of_map_eq_zero`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}  
 {inst_2 : PartialOrder β}…
· 使用定理 `GroupSeminormClass.map_one_eq_zero`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   {
inst_2 : PartialOrder β}…
· 使用定理 `GroupNormClass.toGroupSeminormClass`：∀ {F : Type u_7} {α : outParam (Typ
e u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   
{inst_2 : PartialOrder β}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
  ⟨eq_one_of_map_eq_zero _, by
    rintro rfl
    exact map_one_eq_zero _⟩

@[to_additive]
/-
**map_ne_zero_iff_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ne_zero_iff_ne_one : f x != 0 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `map_eq_zero_iff_eq_one`：map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1
-/
theorem map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 :=
  (map_eq_zero_iff_eq_one _).not

end GroupNormClass

@[to_additive]
/-
**map_pos_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_pos_of_ne_one [Group α] [AddCommMonoid β] [LinearOrder β] [IsOrderedAd
dMonoid β] [GroupNormClass F α β] (f : F) {x : α} (hx : x != 1) : 0 < f x
参数：f : F；hx : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `GroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β 
: Type u_4} [inst : FunLike F α β] [inst_1 : Group α] [inst_2 : AddCommMonoid β]
   [inst_3 : LinearOrder …
· 使用定理 `GroupNormClass.toGroupSeminormClass`：∀ {F : Type u_7} {α : outParam (Typ
e u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   
{inst_2 : PartialOrder β}…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff_ne_one`：map_ne_zero_iff_ne_one : f x != 0 ↔ x != 1
-/
theorem map_pos_of_ne_one [Group α] [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupNormClass F α β] (f : F)
    {x : α} (hx : x ≠ 1) : 0 < f x :=
  (apply_nonneg _ _).lt_of_ne <| ((map_ne_zero_iff_ne_one _).2 hx).symm

/-! ### Ring (semi)norms -/


/-- `RingSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the ring `α`.

You should extend this class when you extend `RingSeminorm`. -/
/-
**RingSeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [NonUnitalNonAssocRing α] → [Semiring β] → [PartialOrder β] → [FunLike F α 
β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the
 ring `α`.

You should extend this class when you extend `RingSeminorm`.
-/
class RingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β, SubmultiplicativeHomClass F α β

/-- `RingNormClass F α` states that `F` is a type of `β`-valued norms on the ring `α`.

You should extend this class when you extend `RingNorm`. -/
/-
**RingNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [NonUnitalNonAssocRing α] → [Semiring β] → [PartialOrder β] → [FunLike F α 
β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingNormClass F α` states that `F` is a type of `β`-valued norms on the ring `α
`.

You should extend this class when you extend `RingNorm`.
-/
class RingNormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends RingSeminormClass F α β, AddGroupNormClass F α β

/-- `MulRingSeminormClass F α` states that `F` is a type of `β`-valued multiplicative seminorms
on the ring `α`.

You should extend this class when you extend `MulRingSeminorm`. -/
/-
**MulRingSeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [NonAssocRing α] → [Semiring β] → [PartialOrder β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulRingSeminormClass F α` states that `F` is a type of `β`-valued multiplicativ
e seminorms
on the ring `α`.

You should extend this class when you extend `MulRingSeminorm`.
-/
class MulRingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β, MonoidWithZeroHomClass F α β

-- Lower the priority of these instances since they require synthesizing an order structure.
attribute [instance 50]
  MulRingSeminormClass.toMonoidHomClass MulRingSeminormClass.toMonoidWithZeroHomClass

/-- `MulRingNormClass F α` states that `F` is a type of `β`-valued multiplicative norms on the
ring `α`.

You should extend this class when you extend `MulRingNorm`. -/
/-
**MulRingNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (α : outParam (Type u_8)) →     (β : outParam (Type u_9
)) → [NonAssocRing α] → [Semiring β] → [PartialOrder β] → [FunLike F α β] → Prop
参数：Type u_8；Type u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulRingNormClass F α` states that `F` is a type of `β`-valued multiplicative no
rms on the
ring `α`.

You should extend this class when you extend `MulRingNorm`.
-/
class MulRingNormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends MulRingSeminormClass F α β, AddGroupNormClass F α β

-- See note [out-param inheritance]
-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) RingSeminormClass.toNonnegHomClass [NonUnitalNonAssocRing α]
    [Semiring β] [LinearOrder β] [IsOrderedAddMonoid β] [RingSeminormClass F α β] :
    NonnegHomClass F α β :=
  AddGroupSeminormClass.toNonnegHomClass

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRingSeminormClass.toRingSeminormClass [NonAssocRing α]
    [Semiring β] [PartialOrder β] [MulRingSeminormClass F α β] : RingSeminormClass F α β :=
  { ‹MulRingSeminormClass F α β› with map_mul_le_mul := fun _ _ _ => (map_mul _ _ _).le }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulRingNormClass.toRingNormClass [NonAssocRing α]
    [Semiring β] [PartialOrder β] [MulRingNormClass F α β] : RingNormClass F α β :=
  { ‹MulRingNormClass F α β›, MulRingSeminormClass.toRingSeminormClass with }
