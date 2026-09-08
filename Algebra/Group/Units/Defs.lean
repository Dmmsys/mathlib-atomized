/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
module

public import Mathlib.Algebra.Group.Commute.Defs

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `Units M`: the group of units (i.e., invertible elements) of a monoid.
* `IsUnit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `AddUnits` and `IsAddUnit`.
See also `Prime`, `Associated`, and `Irreducible` in
`Mathlib/Algebra/GroupWithZero/Associated.lean`.

## Notation

We provide `Mˣ` as notation for `Units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

@[expose] public section

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

/-- Units of a `Monoid`, bundled version. Notation: `αˣ`.

An element of a `Monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `IsUnit`. -/
/-
**Units** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [Monoid α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a `Monoid`, bundled version. Notation: `αˣ`.

An element of a `Monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `IsUnit`.
-/
structure Units (α : Type u) [Monoid α] where
  /-- The underlying value in the base `Monoid`. -/
  val : α
  /-- The inverse value of `val` in the base `Monoid`. -/
  inv : α
  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/
  val_inv : val * inv = 1
  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/
  inv_val : inv * val = 1

attribute [coe] Units.val

@[inherit_doc]
postfix:1024 "ˣ" => Units

-- We don't provide notation for the additive version, because its use is somewhat rare.
/-- Units of an `AddMonoid`, bundled version.

An element of an `AddMonoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `isAddUnit`. -/
/-
**AddUnits** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [AddMonoid α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of an `AddMonoid`, bundled version.

An element of an `AddMonoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `isAddUnit`.
-/
structure AddUnits (α : Type u) [AddMonoid α] where
  /-- The underlying value in the base `AddMonoid`. -/
  val : α
  /-- The additive inverse value of `val` in the base `AddMonoid`. -/
  neg : α
  /-- `neg` is the right additive inverse of `val` in the base `AddMonoid`. -/
  val_neg : val + neg = 0
  /-- `neg` is the left additive inverse of `val` in the base `AddMonoid`. -/
  neg_val : neg + val = 0

attribute [to_additive] Units
attribute [coe] AddUnits.val

namespace Units
section Monoid
variable [Monoid α]

/-- A unit can be interpreted as a term in the base `Monoid`. -/
@[to_additive /-- An additive unit can be interpreted as a term in the base `AddMonoid`. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unit can be interpreted as a term in the base `Monoid`.
-/
instance : CoeHead αˣ α :=
  ⟨val⟩

/-- The inverse of a unit in a `Monoid`. -/
@[to_additive /-- The additive inverse of an additive unit in an `AddMonoid`. -/]
/-
**Units.instInv** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instInv : Inv αˣ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1

--- 原说明 ---
The inverse of a unit in a `Monoid`.
-/
instance instInv : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩
attribute [instance] AddUnits.instNeg

/-- See Note [custom simps projection] -/
@[to_additive
/-- See Note [custom simps projection] -/]
/-
**Units.Simps.val_inv** 是 Mathlib 中的一个定义，位于命名空间 `Units.Simps`。
形式化陈述：{α : Type u} → [inst : Monoid α] → αˣ → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv → null, inv → val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg → null, neg → val_neg, as_prefix val_neg)

@[to_additive]
/-
**Units.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a
参数：a : α；b h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl

@[to_additive]
/-
**Units.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α], Function.Injective Units.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem val_injective : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[to_additive (attr := ext)]
/-
**Units.ext** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：ext {u v : αˣ} (huv : u.val = v.val) : u = v
参数：huv : u.val = v.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := val_injective huv

@[to_additive (attr := norm_cast)]
/-
**Units.val_inj** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
theorem val_inj {a b : αˣ} : (a : α) = b ↔ a = b :=
  val_injective.eq_iff

/-- Units have decidable equality if the base `Monoid` has decidable equality. -/
@[to_additive /-- Additive units have decidable equality
if the base `AddMonoid` has decidable equality. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]
/-
**Units.mk_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u
参数：u : αˣ；y h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive (attr := simps) /-- Copy an `AddUnit`, adjusting definitional equalities. -/]
/-
**Units.copy** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ
参数：u : αˣ；val : α；hv : val = u；inv : α；hi : inv = ↑u⁻¹。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy a unit, adjusting definition equalities.
-/
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
/-
**Units.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u
参数：u : αˣ；val hv inv hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv

/-- Units of a monoid have an induced multiplication. -/
@[to_additive /-- Additive units of an additive monoid have an induced addition. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a monoid have an induced multiplication.
-/
instance : Mul αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

/-- Units of a monoid have a unit -/
@[to_additive /-- Additive units of an additive monoid have a zero. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a monoid have a unit
-/
instance : One αˣ where
  one := ⟨1, 1, one_mul 1, one_mul 1⟩

/-- Units of a monoid have a multiplication and multiplicative identity. -/
@[to_additive
/-- Additive units of an additive monoid have an addition and an additive identity. -/]
/-
**Units.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instMulOneClass : MulOneClass αˣ where one_mul u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass : MulOneClass αˣ where
  one_mul u := ext <| one_mul (u : α)
  mul_one u := ext <| mul_one (u : α)

/-- Units of a monoid are inhabited because `1` is a unit. -/
@[to_additive
/-- Additive units of an additive monoid are inhabited because `0` is an additive unit. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited αˣ :=
  ⟨1⟩

/-- Units of a monoid have a representation of the base value in the `Monoid`. -/
@[to_additive /-- Additive units of an additive monoid have a representation of the base value in
the `AddMonoid`. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Repr α] : Repr αˣ :=
  ⟨reprPrec ∘ val⟩

variable (a b : αˣ) {u : αˣ}

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_mul : (↑(a * b) : α) = a * b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_one : ((1 : αˣ) : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, val_inj]

@[to_additive (attr := simp)]
/-
**Units.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁
参数：x y : α；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl

@[to_additive (attr := simp)]
/-
**Units.inv_eq_val_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl

@[to_additive (attr := simp)]
/-
**Units.inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul : (↑a⁻¹ * a : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
-/
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _

@[to_additive (attr := simp)]
/-
**Units.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv : (a * ↑a⁻¹ : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
-/
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _
/-
**Units.commute_coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] (a : αˣ), Commute ↑a ↑a⁻¹
参数：a : αˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
@[to_additive] lemma commute_coe_inv : Commute (a : α) ↑a⁻¹ := by
  rw [Commute, SemiconjBy, inv_mul, mul_inv]
/-
**Units.commute_inv_coe** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] (a : αˣ), Commute ↑a⁻¹ ↑a
参数：a : αˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Units.commute_coe_inv`：∀ {α : Type u} [inst : Monoid α] (a : αˣ), Commut
e ↑a ↑a⁻¹
-/
@[to_additive] lemma commute_inv_coe : Commute ↑a⁻¹ (a : α) := a.commute_coe_inv.symm

@[to_additive]
/-
**Units.inv_mul_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1
参数：h : ↑u = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]

@[to_additive]
/-
**Units.mul_inv_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1
参数：h : ↑u = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]

@[to_additive (attr := simp)]
/-
**Units.mul_inv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b
参数：a : αˣ；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]

@[to_additive (attr := simp)]
/-
**Units.inv_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b
参数：a : αˣ；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]

@[to_additive]
/-
**Units.inv_mul_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
/-
**Units.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instMonoid : Monoid αˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid αˣ :=
  { (inferInstance : MulOneClass αˣ) with
    mul_assoc := fun _ _ _ => ext <| mul_assoc _ _ _,
    npow := fun n a ↦
      { val := a ^ n
        inv := a⁻¹ ^ n
        val_inv := by rw [← a.commute_coe_inv.mul_pow]; simp
        inv_val := by rw [← a.commute_inv_coe.mul_pow]; simp }
    npow_zero := fun a ↦ by simp only [HPow.hPow, Pow.pow]; ext; simp
    npow_succ := fun n a ↦ by simp only [HPow.hPow, Pow.pow]; ext; simp [pow_succ] }

/-- Units of a monoid have division -/
@[to_additive /-- Additive units of an additive monoid have subtraction. -/]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a monoid have division
-/
instance : Div αˣ where
  div := fun a b ↦
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }

/-- Units of a monoid form a `DivInvMonoid`. -/
@[to_additive /-- Additive units of an additive monoid form a `SubNegMonoid`. -/]
/-
**Units.instDivInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instDivInvMonoid : DivInvMonoid αˣ where zpow
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a monoid form a `DivInvMonoid`.
-/
instance instDivInvMonoid : DivInvMonoid αˣ where
  zpow := fun n a ↦ match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a ↦ by simp only [HPow.hPow, Pow.pow]; simp
  zpow_succ' := fun n a ↦ by simp only [HPow.hPow, Pow.pow]; simp [pow_succ]
  zpow_neg' := fun n a ↦ rfl

/-- Units of a monoid form a group. -/
@[to_additive /-- Additive units of an additive monoid form an additive group. -/]
/-
**Units.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instGroup : Group αˣ where inv_mul_cancel
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Units of a monoid form a group.
-/
instance instGroup : Group αˣ where
  inv_mul_cancel := fun u => ext u.inv_val

/-- Units of a commutative monoid form a commutative group. -/
@[to_additive /-- Additive units of an additive commutative monoid form
an additive commutative group. -/]
/-
**Units.instCommGroupUnits** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ where
  mul_comm := fun _ _ => ext <| mul_comm _ _

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_pow_eq_pow_val** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^ n : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_pow_eq_pow_val (n : ℕ) : ↑(a ^ n) = (a ^ n : α) := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Units.inv_pow_eq_pow_inv** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：inv_pow_eq_pow_inv (n : Nat) : ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_pow_eq_pow_inv (n : ℕ) : ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α) := rfl

end Monoid

section DivisionMonoid
variable [DivisionMonoid α]

/-
**Units.val_inv_eq_inv_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] (u : αˣ), ↑u⁻¹ = (↑u)⁻¹
参数：u : αˣ；↑u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
@[to_additive (attr := simp, norm_cast)] lemma val_inv_eq_inv_val (u : αˣ) : ↑u⁻¹ = (u⁻¹ : α) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_div_eq_div_val** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：val_div_eq_div_val : forall u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma val_div_eq_div_val : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) := by simp [div_eq_mul_inv]

end DivisionMonoid
end Units

/-- For `a, b` in a Dedekind-finite monoid such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive /-- For `a, b` in a Dedekind-finite additive monoid such that `a + b = 0`,
makes an addUnit out of `a`. -/]
/-
**Units.mkOfMulEqOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] (a b : α) (hab : 
a * b = 1) : αˣ
参数：a b : α；hab : a * b = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Units.mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, mul_eq_one_symm hab⟩

@[to_additive (attr := simp)]
/-
**Units.val_mkOfMulEqOne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.val_mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] {a b : α} (h 
: a * b = 1) : (Units.mkOfMulEqOne a b h : α) = a
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Units.val_mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl

section Monoid

variable [Monoid α] {a : α}

/-- Partial division, denoted `a /ₚ u`. It is defined when the
  second argument is invertible, and unlike the division operator
  in `DivisionRing` it is not totalized at zero. -/
/-
**divp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：divp (a : α) (u : Units α) : α
参数：a : α；u : Units α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial division, denoted `a /ₚ u`. It is defined when the
  second argument is invertible, and unlike the division operator
  in `DivisionRing` it is not totalized at zero.
-/
def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]
/-
**divp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_self (u : αˣ) : (u : α) /ₚ u = 1
参数：u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _

@[simp]
/-
**divp_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_one (a : α) : a /ₚ 1 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _
/-
**divp_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u)
参数：a b : α；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _

@[simp]
/-
**divp_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u
参数：u : αˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl

@[simp]
/-
**divp_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a
参数：a : α；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]

@[simp]
/-
**mul_divp_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a
参数：a : α；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]
/-
**divp_divp_eq_divp_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁
)
参数：x : α；u₁ u₂ : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

@[simp]
/-
**one_divp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹
参数：u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _
/-
**inv_eq_one_divp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u
参数：u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_divp`：one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹
-/
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]
/-
**val_div_eq_divp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂
参数：u₁ u₂ : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp.eq_1`：∀ {α : Type u} [inst : Monoid α] (a : α) (u : αˣ), a /ₚ u = a
 * ↑u⁻¹
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
-/
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]

end Monoid

/-!
### `IsUnit` predicate
-/

section IsUnit

variable {M : Type*} {N : Type*}

/-- An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `IsUnit`. -/
@[to_additive /-- An element `a : M` of an `AddMonoid` is an `AddUnit` if it has a two-sided
additive inverse. The actual definition says that `a` is equal to some `u : AddUnits M`,
where `AddUnits M` is a bundled version of `IsAddUnit`. -/]
/-
**IsUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUnit [Monoid M] (a : M) : Prop
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a

/-- See `isUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/
@[to_additive
/-- See `isAddUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/]
/-
**isUnit_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exists b, x * b = 1 ∧ b 
* x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
-/
lemma isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ ∃ b, x * b = 1 ∧ b * x = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- See `isUnit_iff_exists` for a similar lemma with one existential. -/
@[to_additive /-- See `isAddUnit_iff_exists` for a similar lemma with one existential. -/]
/-
**isUnit_iff_exists_and_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_exists_and_exists [Monoid M] {a : M} : IsUnit a ↔ (exists b, a 
* b = 1) ∧ (exists c, c * a = 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c

--- 原说明 ---
See `isUnit_iff_exists` for a similar lemma with one existential.
-/
theorem isUnit_iff_exists_and_exists [Monoid M] {a : M} :
    IsUnit a ↔ (∃ b, a * b = 1) ∧ (∃ c, c * a = 1) :=
  isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := simp)]
/-
**Units.isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
参数：u : Mˣ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩

@[to_additive (attr := simp, grind ←)]
/-
**isUnit_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_one [Monoid M] : IsUnit (1 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩

@[to_additive]
/-
**IsUnit.of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteMonoid M] {a : M} (b : M)
 (h : a * b = 1) : IsUnit a
参数：b : M；h : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteMonoid M] {a : M} (b : M) (h : a * b = 1) :
    IsUnit a :=
  ⟨.mkOfMulEqOne a b h, rfl⟩

@[to_additive]
/-
**IsUnit.of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.of_mul_eq_one_right [Monoid M] [IsDedekindFiniteMonoid M] {b : M} (
a : M) (h : a * b = 1) : IsUnit b
参数：a : M；h : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `IsDedekindFiniteMonoid.mul_eq_one_symm`：∀ {M : Type u_2} {inst : MulOne 
M} [self : IsDedekindFiniteMonoid M] {a b : M}, a * b = 1 → b * a = 1
-/
theorem IsUnit.of_mul_eq_one_right [Monoid M] [IsDedekindFiniteMonoid M] {b : M} (a : M)
    (h : a * b = 1) : IsUnit b :=
  .of_mul_eq_one a <| mul_eq_one_symm h

section Monoid
variable [Monoid M] {a b : M}

@[to_additive IsAddUnit.exists_neg]
/-
**IsUnit.exists_right_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.exists_right_inv (h : IsUnit a) : exists b, a * b = 1
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsUnit.exists_right_inv (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']
/-
**IsUnit.exists_left_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : exists b, b * a = 1
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsUnit.exists_left_inv {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩
/-
**IsUnit.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsUnit b → IsUnit
 (a * b)
参数：a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma IsUnit.mul : IsUnit a → IsUnit b → IsUnit (a * b) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, rfl⟩
/-
**IsUnit.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a → IsUnit (a ^
 n)
参数：n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma IsUnit.pow (n : ℕ) : IsUnit a → IsUnit (a ^ n) := by
  rintro ⟨u, rfl⟩; exact ⟨u ^ n, rfl⟩
/-
**Subsingleton.units_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M], (∀ (a : M), IsUnit a → a = 1) → Subsin
gleton Mˣ
参数：∀ (a : M), IsUnit a → a = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
@[to_additive] lemma Subsingleton.units_of_isUnit (h : ∀ a : M, IsUnit a → a = 1) :
    Subsingleton Mˣ := subsingleton_of_forall_eq 1 fun u ↦ Units.ext <| h u u.isUnit

variable [Subsingleton Mˣ]
/-
**Units.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] [Subsingleton Mˣ] (u : Mˣ), u = 1
参数：u : Mˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
@[to_additive] lemma Units.eq_one (u : Mˣ) : u = 1 := Subsingleton.elim ..
/-
**IsUnit.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a : M} [Subsingleton Mˣ], IsUnit a → a
 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.eq_one`：∀ {M : Type u_1} [inst : Monoid M] [Subsingleton Mˣ] (u : 
Mˣ), u = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma IsUnit.eq_one : IsUnit a → a = 1 := by rintro ⟨u, rfl⟩; simp [u.eq_one]

@[to_additive (attr := simp)]
/-
**isUnit_iff_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_iff_eq_one : IsUnit a ↔ a = 1 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_one`：∀ {M : Type u_1} [inst : Monoid M] {a : M} [Subsingleton 
Mˣ], IsUnit a → a = 1
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isUnit_iff_eq_one : IsUnit a ↔ a = 1 where
  mp := IsUnit.eq_one
  mpr := by rintro rfl; exact isUnit_one

end Monoid

@[to_additive]
/-
**isUnit_iff_exists_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_exists_inv [Monoid M] [IsDedekindFiniteMonoid M] {a : M} : IsUn
it a ↔ exists b, a * b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
-/
theorem isUnit_iff_exists_inv [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨(·.exists_right_inv), fun ⟨b, hab⟩ ↦ .of_mul_eq_one b hab⟩

@[to_additive]
/-
**isUnit_iff_exists_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFiniteMonoid M] {a : M} : IsU
nit a ↔ exists b, b * a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `IsUnit.of_mul_eq_one_right`：IsUnit.of_mul_eq_one_right [Monoid M] [IsDed
ekindFiniteMonoid M] {b : M} (a : M) (h : a * b = 1) : IsUnit b
-/
theorem isUnit_iff_exists_inv' [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ ∃ b, b * a = 1 :=
  ⟨(·.exists_left_inv), fun ⟨b, hba⟩ ↦ .of_mul_eq_one_right b hba⟩

/-- Multiplication by a `u : Mˣ` on the right doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
/-- Addition of a `u : AddUnits M` on the right doesn't affect `IsAddUnit`. -/]
/-
**Units.isUnit_mul_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUn
it a
参数：a : M；u : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

/-- Multiplication by a `u : Mˣ` on the left doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
/-- Addition of a `u : AddUnits M` on the left doesn't affect `IsAddUnit`. -/]
/-
**Units.isUnit_units_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) : IsUnit (↑
u * a) ↔ IsUnit a
参数：u : Mˣ；a : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul

@[to_additive]
/-
**isUnit_of_mul_isUnit_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_mul_isUnit_left [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} 
(hu : IsUnit (x * y)) : IsUnit x
参数：hu : IsUnit (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isUnit_of_mul_isUnit_left [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

@[to_additive]
/-
**isUnit_of_mul_isUnit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_mul_isUnit_right [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
 (hu : IsUnit (x * y)) : IsUnit y
参数：hu : IsUnit (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv'`：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFin
iteMonoid M] {a : M} : IsUnit a ↔ exists b, b * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isUnit_of_mul_isUnit_right [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit y :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv'.1 hu
  isUnit_iff_exists_inv'.2 ⟨z * x, by rwa [mul_assoc]⟩

namespace IsUnit

@[to_additive (attr := simp, grind =)]
/-
**IsUnit.mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} : IsUnit (x * y) ↔
 IsUnit x ∧ IsUnit y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} :
    IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

section Monoid

variable [Monoid M] {a b : M}

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `DivisionMonoid`, use `IsUnit.unit'` instead. -/
@[to_additive /-- The element of the additive group of additive units, corresponding to an element
of an additive monoid which is an additive unit. When `α` is a `SubtractionMonoid`, use
`IsAddUnit.addUnit'` instead. -/]
/-
**IsUnit.unit** 是 Mathlib 中的一个定义，位于命名空间 `IsUnit`。
形式化陈述：{M : Type u_1} → [inst : Monoid M] → {a : M} → IsUnit a → Mˣ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

@[to_additive (attr := simp)]
/-
**IsUnit.unit_of_val_units** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a
参数：h : IsUnit (a : M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext rfl

@[to_additive (attr := simp)]
/-
**IsUnit.unit_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_spec (h : IsUnit a) : ↑h.unit = a
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl

@[to_additive (attr := simp)]
/-
**IsUnit.unit_one** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_one (h : IsUnit (1 : M)) : h.unit = 1
参数：h : IsUnit (1 : M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem unit_one (h : IsUnit (1 : M)) : h.unit = 1 :=
  Units.ext rfl

@[to_additive]
/-
**IsUnit.unit_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_mul (ha : IsUnit a) (hb : IsUnit b) : (ha.mul hb).unit = ha.unit * hb
.unit
参数：ha : IsUnit a；hb : IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
-/
theorem unit_mul (ha : IsUnit a) (hb : IsUnit b) : (ha.mul hb).unit = ha.unit * hb.unit :=
  Units.ext rfl

@[to_additive]
/-
**IsUnit.unit_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_pow (h : IsUnit a) (n : Nat) : (h.pow n).unit = h.unit ^ n
参数：h : IsUnit a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
theorem unit_pow (h : IsUnit a) (n : ℕ) : (h.pow n).unit = h.unit ^ n :=
  Units.ext rfl

@[to_additive (attr := simp)]
/-
**IsUnit.val_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _

@[to_additive (attr := simp)]
/-
**IsUnit.mul_val_inv** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← h.unit.mul_inv]; congr

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive /-- `IsAddUnit x` is decidable if we can decide if `x` comes from `AddUnits M`. -/]
/-
**IsUnit.** 是 Mathlib 中的一个实例，位于命名空间 `IsUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`.
-/
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h
/-
**IsUnit.mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_left_iff {a b : M} (ha : IsUnit a) : IsUnit (a * b) ↔ IsUnit b
参数：ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_left_iff {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b :=
  show IsUnit (ha.unit * b) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)
/-
**IsUnit.mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_right_iff {a b : M} (hb : IsUnit b) : IsUnit (a * b) ↔ IsUnit a
参数：hb : IsUnit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_right_iff {a b : M} (hb : IsUnit b) :
    IsUnit (a * b) ↔ IsUnit a :=
  show IsUnit (a * hb.unit) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
/-
**IsUnit.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → a⁻¹ * a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]

@[to_additive (attr := simp)]
/-
**IsUnit.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → a * a⁻¹ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `IsUnit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `Units α` to `α`. See also `toUnits`. -/
@[to_additive (attr := simps val)
/-- The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. As opposed to `IsAddUnit.addUnit`, the negation is
computable and comes from the negation on `α`. This is useful to transfer properties of negation
in `AddUnits α` to `α`. See also `toAddUnits`. -/]
/-
**IsUnit.unit'** 是 Mathlib 中的一个定义，位于命名空间 `IsUnit`。
形式化陈述：unit' (h : IsUnit a) : αˣ
参数：h : IsUnit a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
· 使用定理 `IsUnit.inv_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a⁻¹ * a = 1
-/
def unit' (h : IsUnit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩
/-
**IsUnit.val_inv_unit'** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α} (h : IsUnit a), ↑h.unit'⁻
¹ = a⁻¹
参数：h : IsUnit a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma val_inv_unit' (h : IsUnit a) : ↑(h.unit'⁻¹) = a⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**IsUnit.mul_inv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → ∀ (b : α), a 
* (a⁻¹ * b) = b
参数：b : α；a⁻¹ * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
-/
protected lemma mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
/-
**IsUnit.inv_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → ∀ (b : α), a⁻
¹ * (a * b) = b
参数：b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
protected lemma inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[to_additive]
/-
**IsUnit.div_self** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → a / a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
-/
protected lemma div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
/-
**IsUnit.inv** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：inv (h : IsUnit a) : IsUnit a⁻¹
参数：h : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]
/-
**IsUnit.unit_inv** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：unit_inv (h : IsUnit a) : h.inv.unit = h.unit⁻¹
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
-/
lemma unit_inv (h : IsUnit a) : h.inv.unit = h.unit⁻¹ :=
  Units.ext h.unit.val_inv_eq_inv_val.symm

@[to_additive]
/-
**IsUnit.div** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b)
参数：ha : IsUnit a；hb : IsUnit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
-/
lemma div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]
/-
**IsUnit.unit_div** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：unit_div (ha : IsUnit a) (hb : IsUnit b) : (ha.div hb).unit = ha.unit / hb
.unit
参数：ha : IsUnit a；hb : IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用引理 `IsUnit.div`：div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Units.val_div_eq_div_val`：val_div_eq_div_val : forall u₁ u₂ : αˣ, ↑(u₁ /
 u₂) = (u₁ / u₂ : α)
-/
lemma unit_div (ha : IsUnit a) (hb : IsUnit b) : (ha.div hb).unit = ha.unit / hb.unit :=
  Units.ext (ha.unit.val_div_eq_div_val hb.unit).symm

@[to_additive]
/-
**IsUnit.div_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α}, IsUnit b → ∀ (a : α), b 
/ (a * b) = a⁻¹
参数：a : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `IsUnit.mul_inv_cancel_left`：∀ {α : Type u} [inst : DivisionMonoid α] {a 
: α}, IsUnit a → ∀ (b : α), a * (a⁻¹ * b) = b
-/
protected lemma div_mul_cancel_right (h : IsUnit b) (a : α) : b / (a * b) = a⁻¹ := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left]

@[to_additive]
/-
**IsUnit.mul_div_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {c : α}, IsUnit c → ∀ (a b : α), 
a * c / (b * c) = a / b
参数：a b : α；b * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_inv_cancel_left`：∀ {α : Type u} [inst : DivisionMonoid α] {a 
: α}, IsUnit a → ∀ (b : α), a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a c : α}

@[to_additive]
/-
**IsUnit.div_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a : α}, IsUnit a → ∀ (b : α)
, a / (a * b) = b⁻¹
参数：b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.div_mul_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), b / (a * b) = a⁻¹
-/
protected lemma div_mul_cancel_left (h : IsUnit a) (b : α) : a / (a * b) = b⁻¹ := by
  rw [mul_comm, h.div_mul_cancel_right]

@[to_additive]
/-
**IsUnit.mul_div_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {c : α}, IsUnit c → ∀ (a b : 
α), c * a / (c * b) = a / b
参数：a b : α；c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.mul_div_mul_right`：∀ {α : Type u} [inst : DivisionMonoid α] {c : 
α}, IsUnit c → ∀ (a b : α), a * c / (b * c) = a / b
-/
protected lemma mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

end DivisionCommMonoid
end IsUnit

/-
**divp_eq_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u
参数：a : α；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `divp.eq_1`：∀ {α : Type u} [inst : Monoid α] (a : α) (u : αˣ), a /ₚ u = a
 * ↑u⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
-/
lemma divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv, divp, u.val_inv_eq_inv_val]

@[to_additive]
/-
**Group.isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Group.isUnit [Group α] (a : α) : IsUnit a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
lemma Group.isUnit [Group α] (a : α) : IsUnit a :=
  ⟨⟨a, a⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩, rfl⟩

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type*}

/-- Constructs an inv operation for a `Monoid` consisting only of units. -/
@[instance_reducible]
/-
**invOfIsUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invOfIsUnit [Monoid M] (h : forall a : M, IsUnit a) : Inv M where inv
参数：h : forall a : M, IsUnit a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an inv operation for a `Monoid` consisting only of units.
-/
noncomputable def invOfIsUnit [Monoid M] (h : ∀ a : M, IsUnit a) : Inv M where
  inv := fun a => ↑(h a).unit⁻¹

/-- Constructs a `Group` structure on a `Monoid` consisting only of units. -/
@[instance_reducible]
/-
**groupOfIsUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupOfIsUnit [hM : Monoid M] (h : forall a : M, IsUnit a) : Group M
参数：h : forall a : M, IsUnit a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `Group` structure on a `Monoid` consisting only of units.
-/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

/-- Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units. -/
@[instance_reducible]
/-
**commGroupOfIsUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGroupOfIsUnit [hM : CommMonoid M] (h : forall a : M, IsUnit a) : CommG
roup M
参数：h : forall a : M, IsUnit a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a

--- 原说明 ---
Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units.
-/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }

end NoncomputableDefs

