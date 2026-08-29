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

/--
Definition of `Units` / `Units` 的定义

English:
structure Units
  parameters: (α : Type u) [Monoid α]
  axioms and operations (4):
    - val : α
    - inv : α
    - val_inv : val * inv = 1
    - inv_val : inv * val = 1

中文:
结构 单位群
  参数: (α : 类型u) [幺半群 α]
  公理与运算 (4 个):
    - val : α
    - inv : α
    - val_inv : val * inv = 1
    - inv_val : inv * val = 1
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
/--
Definition of `AddUnits` / `AddUnits` 的定义

English:
structure AddUnits
  parameters: (α : Type u) [AddMonoid α]
  axioms and operations (4):
    - val : α
    - neg : α
    - val_neg : val + neg = 0
    - neg_val : neg + val = 0

中文:
结构 加法单位群
  参数: (α : 类型u) [加法幺半群 α]
  公理与运算 (4 个):
    - val : α
    - neg : α
    - val_neg : val + neg = 0
    - neg_val : neg + val = 0
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeHead αˣ α
  body: ⟨val⟩

中文:
实例 :
  签名: CoeHead αˣ α
  定义体: ⟨val⟩
-/
instance : CoeHead αˣ α :=
  ⟨val⟩

/-- The inverse of a unit in a `Monoid`. -/
@[to_additive /-- The additive inverse of an additive unit in an `AddMonoid`. -/]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv αˣ
  body: ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩

中文:
实例 instInv
  签名: : 取逆 αˣ
  定义体: ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩

Depends on / 依赖: AddUnits, AddUnits.instNeg, attribute, instNeg, instance
-/
instance instInv : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩
attribute [instance] AddUnits.instNeg

/-- See Note [custom simps projection] -/
@[to_additive
/-- See Note [custom simps projection] -/]
/--
Definition of `Simps.val_inv` / `Simps.val_inv` 的定义

English:
definition Simps.val_inv
  signature: (u : αˣ)
  body: ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv -> null, inv -> val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg -> null, neg -> val_neg, as_prefix val_neg)

@[to_additive]

中文:
定义 Simps.val_inv
  签名: (u : αˣ)
  定义体: ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv -> null, inv -> val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg -> null, neg -> val_neg, as_prefix val_neg)

@[to_additive]
-/
def Simps.val_inv (u : αˣ) : α := ↑(u⁻¹)

initialize_simps_projections Units (as_prefix val, val_inv -> null, inv -> val_inv, as_prefix val_inv)

initialize_simps_projections AddUnits
  (as_prefix val, val_neg -> null, neg -> val_neg, as_prefix val_neg)

@[to_additive]
/--
theorem `val_mk` / 定理 `val_mk`

English:
theorem val_mk
  given: (a : α) (b h₁ h₂)
  statement: ↑(Units.mk a b h₁ h₂) = a
  proof: rfl

@[to_additive]

中文:
定理 val_mk
  条件: (a : α) (b h₁ h₂)
  结论: ↑(单位群.mk a b h₁ h₂) = a
  证明: rfl

@[to_additive]
-/
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl

@[to_additive]
/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  statement: Function.Injective (val : αˣ -> α)

中文:
定理 val_injective
  结论: 函数.单射 (val : αˣ -> α)
-/
theorem val_injective : Function.Injective (val : αˣ -> α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {u v : αˣ} (huv : u.val = v.val)
  statement: u = v
  proof: val_injective huv

@[to_additive (attr := norm_cast)]

中文:
定理 ext
  条件: {u v : αˣ} (huv : u.val = v.val)
  结论: u = v
  证明: val_injective huv

@[to_additive (attr := norm_cast)]

Depends on / 依赖: val_injective
-/
theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := val_injective huv

@[to_additive (attr := norm_cast)]
/--
theorem `val_inj` / 定理 `val_inj`

English:
theorem val_inj
  given: {a b : αˣ}
  statement: (a : α) = b ↔ a = b
  proof: val_injective.eq_iff

中文:
定理 val_inj
  条件: {a b : αˣ}
  结论: (a : α) = b ↔ a = b
  证明: val_injective.eq_iff

Depends on / 依赖: eq_iff, val_injective, val_injective.eq_iff
-/
theorem val_inj {a b : αˣ} : (a : α) = b ↔ a = b :=
  val_injective.eq_iff

/-- Units have decidable equality if the base `Monoid` has decidable equality. -/
@[to_additive /-- Additive units have decidable equality
if the base `AddMonoid` has decidable equality. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq αˣ
  body: fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]

中文:
实例 [DecidableEq
  签名: α] : DecidableEq αˣ
  定义体: fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Units.ext_iff, decidable_of_iff, ext_iff
-/
instance [DecidableEq α] : DecidableEq αˣ := fun _ _ => decidable_of_iff' _ Units.ext_iff

@[to_additive (attr := simp)]
/--
theorem `mk_val` / 定理 `mk_val`

English:
theorem mk_val
  given: (u : αˣ) (y h₁ h₂)
  statement: mk (u : α) y h₁ h₂ = u
  proof: ext rfl

中文:
定理 mk_val
  条件: (u : αˣ) (y h₁ h₂)
  结论: mk (u : α) y h₁ h₂ = u
  证明: ext rfl
-/
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl

/-- Copy a unit, adjusting definition equalities. -/
@[to_additive (attr := simps) /-- Copy an `AddUnit`, adjusting definitional equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹)
  body: { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]

中文:
定义 copy
  签名: (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹)
  定义体: { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]

Depends on / 依赖: hi.symm, hv.symm, inv_val, u.inv_val, u.val_inv, val_inv
-/
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }

@[to_additive]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (u : αˣ) (val hv inv hi)
  statement: u.copy val hv inv hi = u
  proof: ext hv

中文:
定理 copy_eq
  条件: (u : αˣ) (val hv inv hi)
  结论: u.copy val hv inv hi = u
  证明: ext hv
-/
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv

/-- Units of a monoid have an induced multiplication. -/
@[to_additive /-- Additive units of an additive monoid have an induced addition. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul αˣ
  body: ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

中文:
实例 :
  签名: 乘法 αˣ
  定义体: ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

Depends on / 依赖: inv_val, mul_assoc, one_mul, val_inv
-/
instance : Mul αˣ where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv,
      by rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv],
      by rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩

/-- Units of a monoid have a unit -/
@[to_additive /-- Additive units of an additive monoid have a zero. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One αˣ
  body: ⟨1, 1, one_mul 1, one_mul 1⟩

中文:
实例 :
  签名: 幺 αˣ
  定义体: ⟨1, 1, one_mul 1, one_mul 1⟩

Depends on / 依赖: one_mul
-/
instance : One αˣ where
  one := ⟨1, 1, one_mul 1, one_mul 1⟩

/-- Units of a monoid have a multiplication and multiplicative identity. -/
@[to_additive
/-- Additive units of an additive monoid have an addition and an additive identity. -/]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: : MulOneClass αˣ where
  body: ext one_mul (u : α)
mul_one u := ext mul_one (u : α)

中文:
实例 instMulOneClass
  签名: : MulOne类 αˣ where
  定义体: ext one_mul (u : α)
mul_one u := ext mul_one (u : α)

Depends on / 依赖: one_mul
-/
instance instMulOneClass : MulOneClass αˣ where
one_mul u := ext one_mul (u : α)
mul_one u := ext mul_one (u : α)

/-- Units of a monoid are inhabited because `1` is a unit. -/
@[to_additive
/-- Additive units of an additive monoid are inhabited because `0` is an additive unit. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited αˣ
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 αˣ
  定义体: ⟨1⟩
-/
instance : Inhabited αˣ :=
  ⟨1⟩

/-- Units of a monoid have a representation of the base value in the `Monoid`. -/
@[to_additive /-- Additive units of an additive monoid have a representation of the base value in
the `AddMonoid`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: α] : Repr αˣ
  body: ⟨reprPrec ∘ val⟩

中文:
实例 [Repr
  签名: α] : Repr αˣ
  定义体: ⟨reprPrec ∘ val⟩

Depends on / 依赖: reprPrec
-/
instance [Repr α] : Repr αˣ :=
  ⟨reprPrec ∘ val⟩

variable (a b : αˣ) {u : αˣ}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  statement: (↑(a * b) : α) = a * b
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 val_mul
  结论: (↑(a * b) : α) = a * b
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  statement: ((1 : αˣ) : α) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 val_one
  结论: ((1 : αˣ) : α) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_eq_one` / 定理 `val_eq_one`

English:
theorem val_eq_one
  given: {a : αˣ}
  statement: (a : α) = 1 ↔ a = 1
  proof: by rw [← Units.val_one, val_inj]

@[to_additive (attr := simp)]

中文:
定理 val_eq_one
  条件: {a : αˣ}
  结论: (a : α) = 1 ↔ a = 1
  证明: by rw [← Units.val_one, val_inj]

@[to_additive (attr := simp)]

Depends on / 依赖: Units.val_one, val_inj, val_one
-/
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, val_inj]

@[to_additive (attr := simp)]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: (x y : α) (h₁ h₂)
  statement: (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_mk
  条件: (x y : α) (h₁ h₂)
  结论: (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_eq_val_inv` / 定理 `inv_eq_val_inv`

English:
theorem inv_eq_val_inv
  statement: a.inv = ((a⁻¹ : αˣ) : α)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_eq_val_inv
  结论: a.inv = ((a⁻¹ : αˣ) : α)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_mul` / 定理 `inv_mul`

English:
theorem inv_mul
  statement: (↑a⁻¹ * a : α) = 1
  proof: inv_val _

@[to_additive (attr := simp)]

中文:
定理 inv_mul
  结论: (↑a⁻¹ * a : α) = 1
  证明: inv_val _

@[to_additive (attr := simp)]

Depends on / 依赖: inv_val
-/
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _

@[to_additive (attr := simp)]
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  statement: (a * ↑a⁻¹ : α) = 1
  proof: val_inv _

中文:
定理 mul_inv
  结论: (a * ↑a⁻¹ : α) = 1
  证明: val_inv _

Depends on / 依赖: val_inv
-/
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _

/--
lemma `commute_coe_inv` / 引理 `commute_coe_inv`

English:
lemma commute_coe_inv
  statement: Commute (a : α) ↑a⁻¹
  proof: by
  rw [Commute]; rw [SemiconjBy]; rw [inv_mul]; rw [mul_inv]

中文:
引理 commute_coe_inv
  结论: Commute (a : α) ↑a⁻¹
  证明: by
  rw [Commute]; rw [SemiconjBy]; rw [inv_mul]; rw [mul_inv]
-/
@[to_additive] lemma commute_coe_inv : Commute (a : α) ↑a⁻¹ := by
  rw [Commute]; rw [SemiconjBy]; rw [inv_mul]; rw [mul_inv]

/--
lemma `commute_inv_coe` / 引理 `commute_inv_coe`

English:
lemma commute_inv_coe
  statement: Commute ↑a⁻¹ (a : α)
  proof: a.commute_coe_inv.symm

@[to_additive]

中文:
引理 commute_inv_coe
  结论: Commute ↑a⁻¹ (a : α)
  证明: a.commute_coe_inv.symm

@[to_additive]
-/
@[to_additive] lemma commute_inv_coe : Commute ↑a⁻¹ (a : α) := a.commute_coe_inv.symm

@[to_additive]
/--
theorem `inv_mul_of_eq` / 定理 `inv_mul_of_eq`

English:
theorem inv_mul_of_eq
  given: {a : α} (h : ↑u = a)
  statement: ↑u⁻¹ * a = 1
  proof: by rw [← h, u.inv_mul]

@[to_additive]

中文:
定理 inv_mul_of_eq
  条件: {a : α} (h : ↑u = a)
  结论: ↑u⁻¹ * a = 1
  证明: by rw [← h, u.inv_mul]

@[to_additive]

Depends on / 依赖: inv_mul, u.inv_mul
-/
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]

@[to_additive]
/--
theorem `mul_inv_of_eq` / 定理 `mul_inv_of_eq`

English:
theorem mul_inv_of_eq
  given: {a : α} (h : ↑u = a)
  statement: a * ↑u⁻¹ = 1
  proof: by rw [← h, u.mul_inv]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_of_eq
  条件: {a : α} (h : ↑u = a)
  结论: a * ↑u⁻¹ = 1
  证明: by rw [← h, u.mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_inv, u.mul_inv
-/
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel_left` / 定理 `mul_inv_cancel_left`

English:
theorem mul_inv_cancel_left
  given: (a : αˣ) (b : α)
  statement: (a : α) * (↑a⁻¹ * b) = b
  proof: by
  rw [← mul_assoc]; rw [mul_inv]; rw [one_mul]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_cancel_left
  条件: (a : αˣ) (b : α)
  结论: (a : α) * (↑a⁻¹ * b) = b
  证明: by
  rw [← mul_assoc]; rw [mul_inv]; rw [one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_inv, one_mul
-/
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc]; rw [mul_inv]; rw [one_mul]

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel_left` / 定理 `inv_mul_cancel_left`

English:
theorem inv_mul_cancel_left
  given: (a : αˣ) (b : α)
  statement: (↑a⁻¹ : α) * (a * b) = b
  proof: by
  rw [← mul_assoc]; rw [inv_mul]; rw [one_mul]

@[to_additive]

中文:
定理 inv_mul_cancel_left
  条件: (a : αˣ) (b : α)
  结论: (↑a⁻¹ : α) * (a * b) = b
  证明: by
  rw [← mul_assoc]; rw [inv_mul]; rw [one_mul]

@[to_additive]

Depends on / 依赖: inv_mul, mul_assoc, one_mul
-/
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc]; rw [inv_mul]; rw [one_mul]

@[to_additive]
/--
theorem `inv_mul_eq_iff_eq_mul` / 定理 `inv_mul_eq_iff_eq_mul`

English:
theorem inv_mul_eq_iff_eq_mul
  given: {b c : α}
  statement: ↑a⁻¹ * b = c ↔ b = a * c
  proof: ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]

中文:
定理 inv_mul_eq_iff_eq_mul
  条件: {b c : α}
  结论: ↑a⁻¹ * b = c ↔ b = a * c
  证明: ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left, mul_inv_cancel_left
-/
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid αˣ
  body: { (inferInstance : MulOneClass αˣ) with
mul_assoc := fun _ _ _ => ext mul_assoc _ _ _,
    npow := fun n a =>
      { val := a ^ n
        inv := a⁻¹ ^ n
        val_inv := by rw [← a.commute_coe_inv.mul_pow]; simp
        inv_val := by rw [← a.commute_inv_coe.mul_pow]; simp }
    npow_zero := fun a

中文:
实例 instMonoid
  签名: : 幺半群 αˣ
  定义体: { (inferInstance : MulOneClass αˣ) with
mul_assoc := fun _ _ _ => ext mul_assoc _ _ _,
    npow := fun n a =>
      { val := a ^ n
        inv := a⁻¹ ^ n
        val_inv := by rw [← a.commute_coe_inv.mul_pow]; simp
        inv_val := by rw [← a.commute_inv_coe.mul_pow]; simp }
    npow_zero := fun a

Depends on / 依赖: HPow.hPow, MulOneClass, Pow.pow, a.commute_coe_inv.mul_pow, a.commute_inv_coe.mul_pow, commute_coe_inv, commute_inv_coe, inv_val, mul_assoc, mul_pow, npow_succ, npow_zero, pow_succ, val_inv
-/
instance instMonoid : Monoid αˣ :=
  { (inferInstance : MulOneClass αˣ) with
mul_assoc := fun _ _ _ => ext mul_assoc _ _ _,
    npow := fun n a =>
      { val := a ^ n
        inv := a⁻¹ ^ n
        val_inv := by rw [← a.commute_coe_inv.mul_pow]; simp
        inv_val := by rw [← a.commute_inv_coe.mul_pow]; simp }
    npow_zero := fun a => by simp only [HPow.hPow, Pow.pow]; ext; simp
    npow_succ := fun n a => by simp only [HPow.hPow, Pow.pow]; ext; simp [pow_succ] }

/-- Units of a monoid have division -/
@[to_additive /-- Additive units of an additive monoid have subtraction. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div αˣ
  body: fun a b =>
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }

中文:
实例 :
  签名: 除法 αˣ
  定义体: fun a b =>
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }
-/
instance : Div αˣ where
  div := fun a b =>
    { val := a * b⁻¹
      inv := b * a⁻¹
      val_inv := by rw [mul_assoc, inv_mul_cancel_left, mul_inv]
      inv_val := by rw [mul_assoc, inv_mul_cancel_left, mul_inv] }

/-- Units of a monoid form a `DivInvMonoid`. -/
@[to_additive /-- Additive units of an additive monoid form a `SubNegMonoid`. -/]
/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: : DivInvMonoid αˣ where
  body: fun n a => match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a => by simp only [HPow.hPow, Pow.pow]; simp
  zpow_succ' := fun n a => by simp only [HPow.hPow, Pow.pow]; simp [pow_succ]
  zpow_neg' := fun n a => rfl

中文:
实例 instDivInvMonoid
  签名: : 除逆幺半群 αˣ where
  定义体: fun n a => match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a => by simp only [HPow.hPow, Pow.pow]; simp
  zpow_succ' := fun n a => by simp only [HPow.hPow, Pow.pow]; simp [pow_succ]
  zpow_neg' := fun n a => rfl
-/
instance instDivInvMonoid : DivInvMonoid αˣ where
  zpow := fun n a => match n, a with
    | Int.ofNat n, a => a ^ n
    | Int.negSucc n, a => (a ^ n.succ)⁻¹
  zpow_zero' := fun a => by simp only [HPow.hPow, Pow.pow]; simp
  zpow_succ' := fun n a => by simp only [HPow.hPow, Pow.pow]; simp [pow_succ]
  zpow_neg' := fun n a => rfl

/-- Units of a monoid form a group. -/
@[to_additive /-- Additive units of an additive monoid form an additive group. -/]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: : Group αˣ where
  body: fun u => ext u.inv_val

中文:
实例 instGroup
  签名: : 群 αˣ where
  定义体: fun u => ext u.inv_val

Depends on / 依赖: inv_val, u.inv_val
-/
instance instGroup : Group αˣ where
  inv_mul_cancel := fun u => ext u.inv_val

/-- Units of a commutative monoid form a commutative group. -/
@[to_additive /-- Additive units of an additive commutative monoid form
an additive commutative group. -/]
/--
Instance `instCommGroupUnits` / 实例 `instCommGroupUnits`

English:
instance instCommGroupUnits
  signature: {α} [CommMonoid α]
  body: fun _ _ => ext mul_comm _ _

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instCommGroupUnits
  签名: {α} [交换幺半群 α]
  定义体: fun _ _ => ext mul_comm _ _

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: mul_comm
-/
instance instCommGroupUnits {α} [CommMonoid α] : CommGroup αˣ where
mul_comm := fun _ _ => ext mul_comm _ _

@[to_additive (attr := simp, norm_cast)]
/--
lemma `val_pow_eq_pow_val` / 引理 `val_pow_eq_pow_val`

English:
lemma val_pow_eq_pow_val
  given: (n : Nat)
  statement: ↑(a ^ n) = (a ^ n : α)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
引理 val_pow_eq_pow_val
  条件: (n : 自然数)
  结论: ↑(a ^ n) = (a ^ n : α)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
lemma val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^ n : α) := rfl

@[to_additive (attr := simp, norm_cast)]
/--
lemma `inv_pow_eq_pow_inv` / 引理 `inv_pow_eq_pow_inv`

English:
lemma inv_pow_eq_pow_inv
  given: (n : Nat)
  statement: ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α)
  proof: rfl

中文:
引理 inv_pow_eq_pow_inv
  条件: (n : 自然数)
  结论: ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α)
  证明: rfl
-/
lemma inv_pow_eq_pow_inv (n : Nat) : ↑(a ^ n)⁻¹ = (a⁻¹ ^ n : α) := rfl

end Monoid

section DivisionMonoid
variable [DivisionMonoid α]

/--
lemma `val_inv_eq_inv_val` / 引理 `val_inv_eq_inv_val`

English:
lemma val_inv_eq_inv_val
  given: (u : αˣ)
  statement: ↑u⁻¹ = (u⁻¹ : α)
  proof: Eq.symm inv_eq_of_mul_eq_one_right u.mul_inv

@[to_additive (attr := simp, norm_cast)]

中文:
引理 val_inv_eq_inv_val
  条件: (u : αˣ)
  结论: ↑u⁻¹ = (u⁻¹ : α)
  证明: Eq.symm inv_eq_of_mul_eq_one_right u.mul_inv

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive (attr := simp, norm_cast)] lemma val_inv_eq_inv_val (u : αˣ) : ↑u⁻¹ = (u⁻¹ : α) :=
Eq.symm inv_eq_of_mul_eq_one_right u.mul_inv

@[to_additive (attr := simp, norm_cast)]
/--
lemma `val_div_eq_div_val` / 引理 `val_div_eq_div_val`

English:
lemma val_div_eq_div_val
  statement: forall u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α)
  proof: by simp [div_eq_mul_inv]

中文:
引理 val_div_eq_div_val
  结论: 对任意 u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α)
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
lemma val_div_eq_div_val : forall u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) := by simp [div_eq_mul_inv]

end DivisionMonoid
end Units

/-- For `a, b` in a Dedekind-finite monoid such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive /-- For `a, b` in a Dedekind-finite additive monoid such that `a + b = 0`,
makes an addUnit out of `a`. -/]
/--
Definition of `Units.mkOfMulEqOne` / `Units.mkOfMulEqOne` 的定义

English:
definition Units.mkOfMulEqOne
  signature: [Monoid α] [IsDedekindFiniteMonoid α] (a b : α) (hab : a * b = 1)
  body: ⟨a, b, hab, mul_eq_one_symm hab⟩

@[to_additive (attr := simp)]

中文:
定义 单位群.mkOfMulEqOne
  签名: [幺半群 α] [是DedekindFinite幺半群 α] (a b : α) (hab : a * b = 1)
  定义体: ⟨a, b, hab, mul_eq_one_symm hab⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mul_eq_one_symm
-/
def Units.mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, mul_eq_one_symm hab⟩

@[to_additive (attr := simp)]
/--
theorem `Units.val_mkOfMulEqOne` / 定理 `Units.val_mkOfMulEqOne`

English:
theorem Units.val_mkOfMulEqOne
  given: [Monoid α] [IsDedekindFiniteMonoid α] {a b : α} (h : a * b = 1)
  proof: rfl

中文:
定理 单位群.val_mkOfMulEqOne
  条件: [幺半群 α] [是DedekindFinite幺半群 α] {a b : α} (h : a * b = 1)
  证明: rfl
-/
theorem Units.val_mkOfMulEqOne [Monoid α] [IsDedekindFiniteMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl

section Monoid

variable [Monoid α] {a : α}

/--
Definition of `divp` / `divp` 的定义

English:
definition divp
  signature: (a : α) (u : Units α)
  body: a * (u⁻¹ : αˣ)

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]

中文:
定义 divp
  签名: (a : α) (u : 单位群 α)
  定义体: a * (u⁻¹ : αˣ)

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]
-/
def divp (a : α) (u : Units α) : α :=
  a * (u⁻¹ : αˣ)

@[inherit_doc]
infixl:70 " /ₚ " => divp

@[simp]
/--
theorem `divp_self` / 定理 `divp_self`

English:
theorem divp_self
  given: (u : αˣ)
  statement: (u : α) /ₚ u = 1
  proof: Units.mul_inv _

@[simp]

中文:
定理 divp_self
  条件: (u : αˣ)
  结论: (u : α) /ₚ u = 1
  证明: Units.mul_inv _

@[simp]

Depends on / 依赖: Units.mul_inv, antisymm, mem_smul, mul_inv, s.smul_zero_subset.antisymm, smul_zero_subset
-/
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _

@[simp]
/--
theorem `divp_one` / 定理 `divp_one`

English:
theorem divp_one
  given: (a : α)
  statement: a /ₚ 1 = a
  proof: mul_one _

中文:
定理 divp_one
  条件: (a : α)
  结论: a /ₚ 1 = a
  证明: mul_one _

Depends on / 依赖: mul_one
-/
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _

/--
theorem `divp_assoc` / 定理 `divp_assoc`

English:
theorem divp_assoc
  given: (a b : α) (u : αˣ)
  statement: a * b /ₚ u = a * (b /ₚ u)
  proof: mul_assoc _ _ _

@[simp]

中文:
定理 divp_assoc
  条件: (a b : α) (u : αˣ)
  结论: a * b /ₚ u = a * (b /ₚ u)
  证明: mul_assoc _ _ _

@[simp]

Depends on / 依赖: mul_assoc
-/
theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _

@[simp]
/--
theorem `divp_inv` / 定理 `divp_inv`

English:
theorem divp_inv
  given: (u : αˣ)
  statement: a /ₚ u⁻¹ = a * u
  proof: rfl

@[simp]

中文:
定理 divp_inv
  条件: (u : αˣ)
  结论: a /ₚ u⁻¹ = a * u
  证明: rfl

@[simp]

Depends on / 依赖: antisymm, mem_smul, t.zero_smul_subset.antisymm, zero_smul_subset
-/
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl

@[simp]
/--
theorem `divp_mul_cancel` / 定理 `divp_mul_cancel`

English:
theorem divp_mul_cancel
  given: (a : α) (u : αˣ)
  statement: a /ₚ u * u = a
  proof: (mul_assoc _ _ _).trans by rw [Units.inv_mul, mul_one]

@[simp]

中文:
定理 divp_mul_cancel
  条件: (a : α) (u : αˣ)
  结论: a /ₚ u * u = a
  证明: (mul_assoc _ _ _).trans by rw [Units.inv_mul, mul_one]

@[simp]

Depends on / 依赖: Units.inv_mul, inv_mul, mul_assoc, mul_one
-/
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
(mul_assoc _ _ _).trans by rw [Units.inv_mul, mul_one]

@[simp]
/--
theorem `mul_divp_cancel` / 定理 `mul_divp_cancel`

English:
theorem mul_divp_cancel
  given: (a : α) (u : αˣ)
  statement: a * u /ₚ u = a
  proof: (mul_assoc _ _ _).trans by rw [Units.mul_inv, mul_one]

中文:
定理 mul_divp_cancel
  条件: (a : α) (u : αˣ)
  结论: a * u /ₚ u = a
  证明: (mul_assoc _ _ _).trans by rw [Units.mul_inv, mul_one]

Depends on / 依赖: Units.mul_inv, mul_assoc, mul_inv, mul_one
-/
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
(mul_assoc _ _ _).trans by rw [Units.mul_inv, mul_one]

/--
theorem `divp_divp_eq_divp_mul` / 定理 `divp_divp_eq_divp_mul`

English:
theorem divp_divp_eq_divp_mul
  given: (x : α) (u₁ u₂ : αˣ)
  statement: x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁)
  proof: by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

@[simp]

中文:
定理 divp_divp_eq_divp_mul
  条件: (x : α) (u₁ u₂ : αˣ)
  结论: x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁)
  证明: by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

@[simp]

Depends on / 依赖: Units.val_mul, mul_assoc, mul_inv_rev, val_mul
-/
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]

@[simp]
/--
theorem `one_divp` / 定理 `one_divp`

English:
theorem one_divp
  given: (u : αˣ)
  statement: 1 /ₚ u = ↑u⁻¹
  proof: one_mul _

中文:
定理 one_divp
  条件: (u : αˣ)
  结论: 1 /ₚ u = ↑u⁻¹
  证明: one_mul _

Depends on / 依赖: one_mul
-/
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _

/--
theorem `inv_eq_one_divp` / 定理 `inv_eq_one_divp`

English:
theorem inv_eq_one_divp
  given: (u : αˣ)
  statement: ↑u⁻¹ = 1 /ₚ u
  proof: by rw [one_divp]

中文:
定理 inv_eq_one_divp
  条件: (u : αˣ)
  结论: ↑u⁻¹ = 1 /ₚ u
  证明: by rw [one_divp]

Depends on / 依赖: one_divp
-/
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]

/--
theorem `val_div_eq_divp` / 定理 `val_div_eq_divp`

English:
theorem val_div_eq_divp
  given: (u₁ u₂ : αˣ)
  statement: ↑(u₁ / u₂) = ↑u₁ /ₚ u₂
  proof: by
  rw [divp]; rw [division_def]; rw [Units.val_mul]

中文:
定理 val_div_eq_divp
  条件: (u₁ u₂ : αˣ)
  结论: ↑(u₁ / u₂) = ↑u₁ /ₚ u₂
  证明: by
  rw [divp]; rw [division_def]; rw [Units.val_mul]

Depends on / 依赖: Units.val_mul, division_def, val_mul
-/
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp]; rw [division_def]; rw [Units.val_mul]

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
/--
Definition of `IsUnit` / `IsUnit` 的定义

English:
definition IsUnit
  signature: [Monoid M] (a : M)
  body: exists u : Mˣ, (u : M) = a

中文:
定义 是单位
  签名: [幺半群 M] (a : M)
  定义体: exists u : Mˣ, (u : M) = a
-/
def IsUnit [Monoid M] (a : M) : Prop :=
  exists u : Mˣ, (u : M) = a

/-- See `isUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/
@[to_additive
/-- See `isAddUnit_iff_exists_and_exists` for a similar lemma with two existentials. -/]
/--
lemma `isUnit_iff_exists` / 引理 `isUnit_iff_exists`

English:
lemma isUnit_iff_exists
  given: [Monoid M] {x : M}
  statement: IsUnit x ↔ exists b, x * b = 1 ∧ b * x = 1
  proof: by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

中文:
引理 isUnit_iff_存在
  条件: [幺半群 M] {x : M}
  结论: 是单位 x ↔ 存在 b, x * b = 1 ∧ b * x = 1
  证明: by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

Depends on / 依赖: inv_val, u.inv, u.inv_val, u.val_inv, val_inv
-/
lemma isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exists b, x * b = 1 ∧ b * x = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨b, h1b, h2b⟩ => ⟨⟨x, b, h1b, h2b⟩, rfl⟩⟩
  subst x
  exact ⟨u.inv, u.val_inv, u.inv_val⟩

/-- See `isUnit_iff_exists` for a similar lemma with one existential. -/
@[to_additive /-- See `isAddUnit_iff_exists` for a similar lemma with one existential. -/]
/--
theorem `isUnit_iff_exists_and_exists` / 定理 `isUnit_iff_exists_and_exists`

English:
theorem isUnit_iff_exists_and_exists
  given: [Monoid M] {a : M}
  proof: isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := simp)]

中文:
定理 isUnit_iff_存在_and_存在
  条件: [幺半群 M] {a : M}
  证明: isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: isUnit_iff_exists, isUnit_iff_exists.trans, left_inv_eq_right_inv
-/
theorem isUnit_iff_exists_and_exists [Monoid M] {a : M} :
    IsUnit a ↔ (exists b, a * b = 1) ∧ (exists c, c * a = 1) :=
  isUnit_iff_exists.trans
    ⟨fun ⟨b, hba, hab⟩ => ⟨⟨b, hba⟩, ⟨b, hab⟩⟩,
      fun ⟨⟨b, hb⟩, ⟨_, hc⟩⟩ => ⟨b, hb, left_inv_eq_right_inv hc hb ▸ hc⟩⟩

@[to_additive (attr := simp)]
/--
theorem `Units.isUnit` / 定理 `Units.isUnit`

English:
theorem Units.isUnit
  given: [Monoid M] (u : Mˣ)
  statement: IsUnit (u : M)
  proof: ⟨u, rfl⟩

@[to_additive (attr := simp, grind ←)]

中文:
定理 单位群.isUnit
  条件: [幺半群 M] (u : Mˣ)
  结论: 是单位 (u : M)
  证明: ⟨u, rfl⟩

@[to_additive (attr := simp, grind ←)]
-/
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩

@[to_additive (attr := simp, grind ←)]
/--
theorem `isUnit_one` / 定理 `isUnit_one`

English:
theorem isUnit_one
  given: [Monoid M]
  statement: IsUnit (1 : M)
  proof: ⟨1, rfl⟩

@[to_additive]

中文:
定理 isUnit_one
  条件: [幺半群 M]
  结论: 是单位 (1 : M)
  证明: ⟨1, rfl⟩

@[to_additive]
-/
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩

@[to_additive]
/--
theorem `IsUnit.of_mul_eq_one` / 定理 `IsUnit.of_mul_eq_one`

English:
theorem IsUnit.of_mul_eq_one
  given: [Monoid M] [IsDedekindFiniteMonoid M] {a : M} (b : M) (h : a * b = 1)
  proof: ⟨.mkOfMulEqOne a b h, rfl⟩

@[to_additive]

中文:
定理 是单位.of_mul_eq_one
  条件: [幺半群 M] [是DedekindFinite幺半群 M] {a : M} (b : M) (h : a * b = 1)
  证明: ⟨.mkOfMulEqOne a b h, rfl⟩

@[to_additive]

Depends on / 依赖: mkOfMulEqOne
-/
theorem IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteMonoid M] {a : M} (b : M) (h : a * b = 1) :
    IsUnit a :=
  ⟨.mkOfMulEqOne a b h, rfl⟩

@[to_additive]
/--
theorem `IsUnit.of_mul_eq_one_right` / 定理 `IsUnit.of_mul_eq_one_right`

English:
theorem IsUnit.of_mul_eq_one_right
  statement: [Monoid M] [IsDedekindFiniteMonoid M] {b : M} (a : M)
  proof: .of_mul_eq_one a mul_eq_one_symm h

中文:
定理 是单位.of_mul_eq_one_right
  结论: [幺半群 M] [是DedekindFinite幺半群 M] {b : M} (a : M)
  证明: .of_mul_eq_one a mul_eq_one_symm h

Depends on / 依赖: mul_eq_one_symm, of_mul_eq_one
-/
theorem IsUnit.of_mul_eq_one_right [Monoid M] [IsDedekindFiniteMonoid M] {b : M} (a : M)
    (h : a * b = 1) : IsUnit b :=
.of_mul_eq_one a mul_eq_one_symm h

section Monoid
variable [Monoid M] {a b : M}

@[to_additive IsAddUnit.exists_neg]
/--
lemma `IsUnit.exists_right_inv` / 引理 `IsUnit.exists_right_inv`

English:
lemma IsUnit.exists_right_inv
  given: (h : IsUnit a)
  statement: exists b, a * b = 1
  proof: by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']

中文:
引理 是单位.存在_right_inv
  条件: (h : 是单位 a)
  结论: 存在 b, a * b = 1
  证明: by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']
-/
lemma IsUnit.exists_right_inv (h : IsUnit a) : exists b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩

@[to_additive IsAddUnit.exists_neg']
/--
lemma `IsUnit.exists_left_inv` / 引理 `IsUnit.exists_left_inv`

English:
lemma IsUnit.exists_left_inv
  given: {a : M} (h : IsUnit a)
  statement: exists b, b * a = 1
  proof: by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩

中文:
引理 是单位.存在_left_inv
  条件: {a : M} (h : 是单位 a)
  结论: 存在 b, b * a = 1
  证明: by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩
-/
lemma IsUnit.exists_left_inv {a : M} (h : IsUnit a) : exists b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩

/--
lemma `IsUnit.mul` / 引理 `IsUnit.mul`

English:
lemma IsUnit.mul
  statement: IsUnit a -> IsUnit b -> IsUnit (a * b)
  proof: by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, rfl⟩

中文:
引理 是单位.mul
  结论: 是单位 a -> 是单位 b -> 是单位 (a * b)
  证明: by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, rfl⟩
-/
@[to_additive] lemma IsUnit.mul : IsUnit a -> IsUnit b -> IsUnit (a * b) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, rfl⟩

/--
lemma `IsUnit.pow` / 引理 `IsUnit.pow`

English:
lemma IsUnit.pow
  given: (n : Nat)
  statement: IsUnit a -> IsUnit (a ^ n)
  proof: by
  rintro ⟨u, rfl⟩; exact ⟨u ^ n, rfl⟩

中文:
引理 是单位.pow
  条件: (n : 自然数)
  结论: 是单位 a -> 是单位 (a ^ n)
  证明: by
  rintro ⟨u, rfl⟩; exact ⟨u ^ n, rfl⟩
-/
@[to_additive] lemma IsUnit.pow (n : Nat) : IsUnit a -> IsUnit (a ^ n) := by
  rintro ⟨u, rfl⟩; exact ⟨u ^ n, rfl⟩

/--
lemma `Subsingleton.units_of_isUnit` / 引理 `Subsingleton.units_of_isUnit`

English:
lemma Subsingleton.units_of_isUnit
  given: (h : forall a : M, IsUnit a -> a = 1)
  proof: subsingleton_of_forall_eq 1 fun u => Units.ext h u u.isUnit

中文:
引理 子单例.units_of_isUnit
  条件: (h : 对任意 a : M, 是单位 a -> a = 1)
  证明: subsingleton_of_forall_eq 1 fun u => Units.ext h u u.isUnit
-/
@[to_additive] lemma Subsingleton.units_of_isUnit (h : forall a : M, IsUnit a -> a = 1) :
Subsingleton Mˣ := subsingleton_of_forall_eq 1 fun u => Units.ext h u u.isUnit

variable [Subsingleton Mˣ]

/--
lemma `Units.eq_one` / 引理 `Units.eq_one`

English:
lemma Units.eq_one
  given: (u : Mˣ)
  statement: u = 1
  proof: Subsingleton.elim ..

中文:
引理 单位群.eq_one
  条件: (u : Mˣ)
  结论: u = 1
  证明: Subsingleton.elim ..
-/
@[to_additive] lemma Units.eq_one (u : Mˣ) : u = 1 := Subsingleton.elim ..
/--
lemma `IsUnit.eq_one` / 引理 `IsUnit.eq_one`

English:
lemma IsUnit.eq_one
  statement: IsUnit a -> a = 1
  proof: by rintro ⟨u, rfl⟩; simp [u.eq_one]

@[to_additive (attr := simp)]

中文:
引理 是单位.eq_one
  结论: 是单位 a -> a = 1
  证明: by rintro ⟨u, rfl⟩; simp [u.eq_one]

@[to_additive (attr := simp)]
-/
@[to_additive] lemma IsUnit.eq_one : IsUnit a -> a = 1 := by rintro ⟨u, rfl⟩; simp [u.eq_one]

@[to_additive (attr := simp)]
/--
lemma `isUnit_iff_eq_one` / 引理 `isUnit_iff_eq_one`

English:
lemma isUnit_iff_eq_one
  statement: IsUnit a ↔ a = 1 where
  proof: IsUnit.eq_one
  mpr := by rintro rfl; exact isUnit_one

中文:
引理 isUnit_iff_eq_one
  结论: 是单位 a ↔ a = 1 where
  证明: IsUnit.eq_one
  mpr := by rintro rfl; exact isUnit_one

Depends on / 依赖: IsUnit, IsUnit.eq_one, eq_one
-/
lemma isUnit_iff_eq_one : IsUnit a ↔ a = 1 where
  mp := IsUnit.eq_one
  mpr := by rintro rfl; exact isUnit_one

end Monoid

@[to_additive]
/--
theorem `isUnit_iff_exists_inv` / 定理 `isUnit_iff_exists_inv`

English:
theorem isUnit_iff_exists_inv
  given: [Monoid M] [IsDedekindFiniteMonoid M] {a : M}
  proof: ⟨(·.exists_right_inv), fun ⟨b, hab⟩ => .of_mul_eq_one b hab⟩

@[to_additive]

中文:
定理 isUnit_iff_存在_inv
  条件: [幺半群 M] [是DedekindFinite幺半群 M] {a : M}
  证明: ⟨(·.exists_right_inv), fun ⟨b, hab⟩ => .of_mul_eq_one b hab⟩

@[to_additive]

Depends on / 依赖: exists_right_inv, of_mul_eq_one
-/
theorem isUnit_iff_exists_inv [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ exists b, a * b = 1 :=
  ⟨(·.exists_right_inv), fun ⟨b, hab⟩ => .of_mul_eq_one b hab⟩

@[to_additive]
/--
theorem `isUnit_iff_exists_inv'` / 定理 `isUnit_iff_exists_inv'`

English:
theorem isUnit_iff_exists_inv'
  given: [Monoid M] [IsDedekindFiniteMonoid M] {a : M}
  proof: ⟨(·.exists_left_inv), fun ⟨b, hba⟩ => .of_mul_eq_one_right b hba⟩

中文:
定理 isUnit_iff_存在_inv'
  条件: [幺半群 M] [是DedekindFinite幺半群 M] {a : M}
  证明: ⟨(·.exists_left_inv), fun ⟨b, hba⟩ => .of_mul_eq_one_right b hba⟩

Depends on / 依赖: exists_left_inv, of_mul_eq_one_right
-/
theorem isUnit_iff_exists_inv' [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ exists b, b * a = 1 :=
  ⟨(·.exists_left_inv), fun ⟨b, hba⟩ => .of_mul_eq_one_right b hba⟩

/-- Multiplication by a `u : Mˣ` on the right doesn't affect `IsUnit`. -/
@[to_additive (attr := simp)
/-- Addition of a `u : AddUnits M` on the right doesn't affect `IsAddUnit`. -/]
/--
theorem `Units.isUnit_mul_units` / 定理 `Units.isUnit_mul_units`

English:
theorem Units.isUnit_mul_units
  given: [Monoid M] (a : M) (u : Mˣ)
  statement: IsUnit (a * u) ↔ IsUnit a
  proof: Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

中文:
定理 单位群.isUnit_mul_units
  条件: [幺半群 M] (a : M) (u : Mˣ)
  结论: 是单位 (a * u) ↔ 是单位 a
  证明: Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

Depends on / 依赖: Iff.intro, IsUnit, Units.mul_inv, Units.val_mul, isUnit, mul_assoc, mul_inv, mul_one, u.isUnit, v.mul, val_mul
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
/--
theorem `Units.isUnit_units_mul` / 定理 `Units.isUnit_units_mul`

English:
theorem Units.isUnit_units_mul
  given: {M : Type*} [Monoid M] (u : Mˣ) (a : M)
  proof: Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul

@[to_additive]

中文:
定理 单位群.isUnit_units_mul
  条件: {M : 类型} [幺半群 M] (u : Mˣ) (a : M)
  证明: Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul

@[to_additive]

Depends on / 依赖: Iff.intro, IsUnit, Units.inv_mul, Units.val_mul, inv_mul, isUnit, mul_assoc, one_mul, u.isUnit.mul, val_mul
-/
theorem Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul

@[to_additive]
/--
theorem `isUnit_of_mul_isUnit_left` / 定理 `isUnit_of_mul_isUnit_left`

English:
theorem isUnit_of_mul_isUnit_left
  statement: [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
  proof: let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

@[to_additive]

中文:
定理 isUnit_of_mul_isUnit_left
  结论: [幺半群 M] [是DedekindFinite幺半群 M] {x y : M}
  证明: let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

@[to_additive]

Depends on / 依赖: isUnit_iff_exists_inv, mul_assoc
-/
theorem isUnit_of_mul_isUnit_left [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩

@[to_additive]
/--
theorem `isUnit_of_mul_isUnit_right` / 定理 `isUnit_of_mul_isUnit_right`

English:
theorem isUnit_of_mul_isUnit_right
  statement: [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
  proof: let ⟨z, hz⟩ := isUnit_iff_exists_inv'.1 hu
  isUnit_iff_exists_inv'.2 ⟨z * x, by rwa [mul_assoc]⟩

中文:
定理 isUnit_of_mul_isUnit_right
  结论: [幺半群 M] [是DedekindFinite幺半群 M] {x y : M}
  证明: let ⟨z, hz⟩ := isUnit_iff_exists_inv'.1 hu
  isUnit_iff_exists_inv'.2 ⟨z * x, by rwa [mul_assoc]⟩

Depends on / 依赖: isUnit_iff_exists_inv, mul_assoc
-/
theorem isUnit_of_mul_isUnit_right [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
    (hu : IsUnit (x * y)) : IsUnit y :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv'.1 hu
  isUnit_iff_exists_inv'.2 ⟨z * x, by rwa [mul_assoc]⟩

namespace IsUnit

@[to_additive (attr := simp, grind =)]
/--
theorem `mul_iff` / 定理 `mul_iff`

English:
theorem mul_iff
  given: [Monoid M] [IsDedekindFiniteMonoid M] {x y : M}
  proof: ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

中文:
定理 mul_iff
  条件: [幺半群 M] [是DedekindFinite幺半群 M] {x y : M}
  证明: ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩,
   fun h => IsUnit.mul h.1 h.2⟩

Depends on / 依赖: IsUnit, IsUnit.mul, isUnit_of_mul_isUnit_left, isUnit_of_mul_isUnit_right
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
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def unit (h : IsUnit a)
  body: (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

@[to_additive (attr := simp)]

中文:
定义 noncomputable
  签名: def unit (h : 是单位 a)
  定义体: (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

@[to_additive (attr := simp)]
-/
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl

@[to_additive (attr := simp)]
/--
theorem `unit_of_val_units` / 定理 `unit_of_val_units`

English:
theorem unit_of_val_units
  given: {a : Mˣ} (h : IsUnit (a : M))
  statement: h.unit = a
  proof: Units.ext rfl

@[to_additive (attr := simp)]

中文:
定理 unit_of_val_units
  条件: {a : Mˣ} (h : 是单位 (a : M))
  结论: h.unit = a
  证明: Units.ext rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Units.ext
-/
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.unit = a :=
  Units.ext rfl

@[to_additive (attr := simp)]
/--
theorem `unit_spec` / 定理 `unit_spec`

English:
theorem unit_spec
  given: (h : IsUnit a)
  statement: ↑h.unit = a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unit_spec
  条件: (h : 是单位 a)
  结论: ↑h.unit = a
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, mem_mul, mul_zero_subset, s.mul_zero_subset.antisymm
-/
theorem unit_spec (h : IsUnit a) : ↑h.unit = a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unit_one` / 定理 `unit_one`

English:
theorem unit_one
  given: (h : IsUnit (1 : M))
  statement: h.unit = 1
  proof: Units.ext rfl

@[to_additive]

中文:
定理 unit_one
  条件: (h : 是单位 (1 : M))
  结论: h.unit = 1
  证明: Units.ext rfl

@[to_additive]

Depends on / 依赖: Units.ext, antisymm, mem_mul, s.zero_mul_subset.antisymm, zero_mul_subset
-/
theorem unit_one (h : IsUnit (1 : M)) : h.unit = 1 :=
  Units.ext rfl

@[to_additive]
/--
theorem `unit_mul` / 定理 `unit_mul`

English:
theorem unit_mul
  given: (ha : IsUnit a) (hb : IsUnit b)
  statement: (ha.mul hb).unit = ha.unit * hb.unit
  proof: Units.ext rfl

@[to_additive]

中文:
定理 unit_mul
  条件: (ha : 是单位 a) (hb : 是单位 b)
  结论: (ha.mul hb).unit = ha.unit * hb.unit
  证明: Units.ext rfl

@[to_additive]

Depends on / 依赖: Units.ext
-/
theorem unit_mul (ha : IsUnit a) (hb : IsUnit b) : (ha.mul hb).unit = ha.unit * hb.unit :=
  Units.ext rfl

@[to_additive]
/--
theorem `unit_pow` / 定理 `unit_pow`

English:
theorem unit_pow
  given: (h : IsUnit a) (n : Nat)
  statement: (h.pow n).unit = h.unit ^ n
  proof: Units.ext rfl

@[to_additive (attr := simp)]

中文:
定理 unit_pow
  条件: (h : 是单位 a) (n : 自然数)
  结论: (h.pow n).unit = h.unit ^ n
  证明: Units.ext rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Units.ext
-/
theorem unit_pow (h : IsUnit a) (n : Nat) : (h.pow n).unit = h.unit ^ n :=
  Units.ext rfl

@[to_additive (attr := simp)]
/--
theorem `val_inv_mul` / 定理 `val_inv_mul`

English:
theorem val_inv_mul
  given: (h : IsUnit a)
  statement: ↑h.unit⁻¹ * a = 1
  proof: Units.mul_inv _

@[to_additive (attr := simp)]

中文:
定理 val_inv_mul
  条件: (h : 是单位 a)
  结论: ↑h.unit⁻¹ * a = 1
  证明: Units.mul_inv _

@[to_additive (attr := simp)]

Depends on / 依赖: Units.mul_inv, antisymm, div_zero_subset, mem_div, mul_inv, s.div_zero_subset.antisymm
-/
theorem val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1 :=
  Units.mul_inv _

@[to_additive (attr := simp)]
/--
theorem `mul_val_inv` / 定理 `mul_val_inv`

English:
theorem mul_val_inv
  given: (h : IsUnit a)
  statement: a * ↑h.unit⁻¹ = 1
  proof: by
  rw [← h.unit.mul_inv]; congr

中文:
定理 mul_val_inv
  条件: (h : 是单位 a)
  结论: a * ↑h.unit⁻¹ = 1
  证明: by
  rw [← h.unit.mul_inv]; congr

Depends on / 依赖: antisymm, h.unit.mul_inv, mem_div, mul_inv, s.zero_div_subset.antisymm, zero_div_subset
-/
theorem mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1 := by
  rw [← h.unit.mul_inv]; congr

/-- `IsUnit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive /-- `IsAddUnit x` is decidable if we can decide if `x` comes from `AddUnits M`. -/]
instance (x : M) [h : Decidable (exists u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

/--
theorem `mul_left_iff` / 定理 `mul_left_iff`

English:
theorem mul_left_iff
  given: {a b : M} (ha : IsUnit a)
  proof: show IsUnit (ha.unit * b) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)

中文:
定理 mul_left_iff
  条件: {a b : M} (ha : 是单位 a)
  证明: show IsUnit (ha.unit * b) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)

Depends on / 依赖: IsUnit, IsUnit.unit_spec, ha.unit, unit_spec
-/
theorem mul_left_iff {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b :=
  show IsUnit (ha.unit * b) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)

/--
theorem `mul_right_iff` / 定理 `mul_right_iff`

English:
theorem mul_right_iff
  given: {a b : M} (hb : IsUnit b)
  proof: show IsUnit (a * hb.unit) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

中文:
定理 mul_right_iff
  条件: {a b : M} (hb : 是单位 b)
  证明: show IsUnit (a * hb.unit) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

Depends on / 依赖: IsUnit, IsUnit.unit_spec, hb.unit, unit_spec
-/
theorem mul_right_iff {a b : M} (hb : IsUnit b) :
    IsUnit (a * b) ↔ IsUnit a :=
  show IsUnit (a * hb.unit) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_right_iff => IsUnit b, IsUnit (a * b)

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  statement: IsUnit a -> a⁻¹ * a = 1
  proof: by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.inv_mul]

@[to_additive (attr := simp)]

中文:
定理 inv_mul_cancel
  结论: 是单位 a -> a⁻¹ * a = 1
  证明: by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.inv_mul]

@[to_additive (attr := simp)]
-/
protected theorem inv_mul_cancel : IsUnit a -> a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.inv_mul]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  statement: IsUnit a -> a * a⁻¹ = 1
  proof: by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.mul_inv]

中文:
定理 mul_inv_cancel
  结论: 是单位 a -> a * a⁻¹ = 1
  证明: by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.mul_inv]
-/
protected theorem mul_inv_cancel : IsUnit a -> a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val]; rw [Units.mul_inv]

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `IsUnit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `Units α` to `α`. See also `toUnits`. -/
@[to_additive (attr := simps val)
/-- The element of the additive group of additive units, corresponding to an element of
an additive monoid which is an additive unit. As opposed to `IsAddUnit.addUnit`, the negation is
computable and comes from the negation on `α`. This is useful to transfer properties of negation
in `AddUnits α` to `α`. See also `toAddUnits`. -/]
/--
Definition of `unit'` / `unit'` 的定义

English:
definition unit'
  signature: (h : IsUnit a)
  body: ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

中文:
定义 unit'
  签名: (h : 是单位 a)
  定义体: ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

Depends on / 依赖: h.inv_mul_cancel, h.mul_inv_cancel, inv_mul_cancel, mul_inv_cancel
-/
def unit' (h : IsUnit a) : αˣ := ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

/--
lemma `val_inv_unit'` / 引理 `val_inv_unit'`

English:
lemma val_inv_unit'
  given: (h : IsUnit a)
  statement: ↑(h.unit'⁻¹) = a⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 val_inv_unit'
  条件: (h : 是单位 a)
  结论: ↑(h.unit'⁻¹) = a⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] lemma val_inv_unit' (h : IsUnit a) : ↑(h.unit'⁻¹) = a⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `mul_inv_cancel_left` / 引理 `mul_inv_cancel_left`

English:
lemma mul_inv_cancel_left
  given: (h : IsUnit a)
  statement: forall b, a * (a⁻¹ * b) = b
  proof: h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]

中文:
引理 mul_inv_cancel_left
  条件: (h : 是单位 a)
  结论: 对任意 b, a * (a⁻¹ * b) = b
  证明: h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
-/
protected lemma mul_inv_cancel_left (h : IsUnit a) : forall b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[to_additive (attr := simp)]
/--
lemma `inv_mul_cancel_left` / 引理 `inv_mul_cancel_left`

English:
lemma inv_mul_cancel_left
  given: (h : IsUnit a)
  statement: forall b, a⁻¹ * (a * b) = b
  proof: h.unit'.inv_mul_cancel_left

@[to_additive]

中文:
引理 inv_mul_cancel_left
  条件: (h : 是单位 a)
  结论: 对任意 b, a⁻¹ * (a * b) = b
  证明: h.unit'.inv_mul_cancel_left

@[to_additive]
-/
protected lemma inv_mul_cancel_left (h : IsUnit a) : forall b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[to_additive]
/--
lemma `div_self` / 引理 `div_self`

English:
lemma div_self
  given: (h : IsUnit a)
  statement: a / a = 1
  proof: by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]

中文:
引理 div_self
  条件: (h : 是单位 a)
  结论: a / a = 1
  证明: by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
-/
protected lemma div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: (h : IsUnit a)
  statement: IsUnit a⁻¹
  proof: by
  obtain ⟨u, hu⟩ := h
  rw [← hu]; rw [← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]

中文:
引理 inv
  条件: (h : 是单位 a)
  结论: 是单位 a⁻¹
  证明: by
  obtain ⟨u, hu⟩ := h
  rw [← hu]; rw [← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]

Depends on / 依赖: Units.isUnit, Units.val_inv_eq_inv_val, isUnit, val_inv_eq_inv_val
-/
lemma inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu]; rw [← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

@[to_additive]
/--
lemma `unit_inv` / 引理 `unit_inv`

English:
lemma unit_inv
  given: (h : IsUnit a)
  statement: h.inv.unit = h.unit⁻¹
  proof: Units.ext h.unit.val_inv_eq_inv_val.symm

@[to_additive]

中文:
引理 unit_inv
  条件: (h : 是单位 a)
  结论: h.inv.unit = h.unit⁻¹
  证明: Units.ext h.unit.val_inv_eq_inv_val.symm

@[to_additive]

Depends on / 依赖: Units.ext, h.unit.val_inv_eq_inv_val.symm, val_inv_eq_inv_val
-/
lemma unit_inv (h : IsUnit a) : h.inv.unit = h.unit⁻¹ :=
  Units.ext h.unit.val_inv_eq_inv_val.symm

@[to_additive]
/--
lemma `div` / 引理 `div`

English:
lemma div
  given: (ha : IsUnit a) (hb : IsUnit b)
  statement: IsUnit (a / b)
  proof: by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]

中文:
引理 div
  条件: (ha : 是单位 a) (hb : 是单位 b)
  结论: 是单位 (a / b)
  证明: by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, ha.mul, hb.inv
-/
lemma div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]
/--
lemma `unit_div` / 引理 `unit_div`

English:
lemma unit_div
  given: (ha : IsUnit a) (hb : IsUnit b)
  statement: (ha.div hb).unit = ha.unit / hb.unit
  proof: Units.ext (ha.unit.val_div_eq_div_val hb.unit).symm

@[to_additive]

中文:
引理 unit_div
  条件: (ha : 是单位 a) (hb : 是单位 b)
  结论: (ha.div hb).unit = ha.unit / hb.unit
  证明: Units.ext (ha.unit.val_div_eq_div_val hb.unit).symm

@[to_additive]

Depends on / 依赖: Units.ext, ha.unit.val_div_eq_div_val, hb.unit, val_div_eq_div_val
-/
lemma unit_div (ha : IsUnit a) (hb : IsUnit b) : (ha.div hb).unit = ha.unit / hb.unit :=
  Units.ext (ha.unit.val_div_eq_div_val hb.unit).symm

@[to_additive]
/--
lemma `div_mul_cancel_right` / 引理 `div_mul_cancel_right`

English:
lemma div_mul_cancel_right
  given: (h : IsUnit b) (a : α)
  statement: b / (a * b) = a⁻¹
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [h.mul_inv_cancel_left]

@[to_additive]

中文:
引理 div_mul_cancel_right
  条件: (h : 是单位 b) (a : α)
  结论: b / (a * b) = a⁻¹
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [h.mul_inv_cancel_left]

@[to_additive]
-/
protected lemma div_mul_cancel_right (h : IsUnit b) (a : α) : b / (a * b) = a⁻¹ := by
  rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [h.mul_inv_cancel_left]

@[to_additive]
/--
lemma `mul_div_mul_right` / 引理 `mul_div_mul_right`

English:
lemma mul_div_mul_right
  given: (h : IsUnit c) (a b : α)
  statement: a * c / (b * c) = a / b
  proof: by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

中文:
引理 mul_div_mul_right
  条件: (h : 是单位 c) (a b : α)
  结论: a * c / (b * c) = a / b
  证明: by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]
-/
protected lemma mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a c : α}

@[to_additive]
/--
lemma `div_mul_cancel_left` / 引理 `div_mul_cancel_left`

English:
lemma div_mul_cancel_left
  given: (h : IsUnit a) (b : α)
  statement: a / (a * b) = b⁻¹
  proof: by
  rw [mul_comm]; rw [h.div_mul_cancel_right]

@[to_additive]

中文:
引理 div_mul_cancel_left
  条件: (h : 是单位 a) (b : α)
  结论: a / (a * b) = b⁻¹
  证明: by
  rw [mul_comm]; rw [h.div_mul_cancel_right]

@[to_additive]
-/
protected lemma div_mul_cancel_left (h : IsUnit a) (b : α) : a / (a * b) = b⁻¹ := by
  rw [mul_comm]; rw [h.div_mul_cancel_right]

@[to_additive]
/--
lemma `mul_div_mul_left` / 引理 `mul_div_mul_left`

English:
lemma mul_div_mul_left
  given: (h : IsUnit c) (a b : α)
  statement: c * a / (c * b) = a / b
  proof: by
  rw [mul_comm c]; rw [mul_comm c]; rw [h.mul_div_mul_right]

中文:
引理 mul_div_mul_left
  条件: (h : 是单位 c) (a b : α)
  结论: c * a / (c * b) = a / b
  证明: by
  rw [mul_comm c]; rw [mul_comm c]; rw [h.mul_div_mul_right]
-/
protected lemma mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c]; rw [mul_comm c]; rw [h.mul_div_mul_right]

end DivisionCommMonoid
end IsUnit

/--
lemma `divp_eq_div` / 引理 `divp_eq_div`

English:
lemma divp_eq_div
  given: [DivisionMonoid α] (a : α) (u : αˣ)
  statement: a /ₚ u = a / u
  proof: by
  rw [div_eq_mul_inv]; rw [divp]; rw [u.val_inv_eq_inv_val]

@[to_additive]

中文:
引理 divp_eq_div
  条件: [Division幺半群 α] (a : α) (u : αˣ)
  结论: a /ₚ u = a / u
  证明: by
  rw [div_eq_mul_inv]; rw [divp]; rw [u.val_inv_eq_inv_val]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, u.val_inv_eq_inv_val, val_inv_eq_inv_val
-/
lemma divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv]; rw [divp]; rw [u.val_inv_eq_inv_val]

@[to_additive]
/--
lemma `Group.isUnit` / 引理 `Group.isUnit`

English:
lemma Group.isUnit
  given: [Group α] (a : α)
  statement: IsUnit a
  proof: ⟨⟨a, a⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩, rfl⟩

中文:
引理 群.isUnit
  条件: [群 α] (a : α)
  结论: 是单位 a
  证明: ⟨⟨a, a⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩, rfl⟩

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel
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
/--
Definition of `invOfIsUnit` / `invOfIsUnit` 的定义

English:
definition invOfIsUnit
  signature: [Monoid M] (h : forall a : M, IsUnit a)
  body: fun a => ↑(h a).unit⁻¹

中文:
定义 invOfIsUnit
  签名: [幺半群 M] (h : 对任意 a : M, 是单位 a)
  定义体: fun a => ↑(h a).unit⁻¹
-/
noncomputable def invOfIsUnit [Monoid M] (h : forall a : M, IsUnit a) : Inv M where
  inv := fun a => ↑(h a).unit⁻¹

/-- Constructs a `Group` structure on a `Monoid` consisting only of units. -/
@[instance_reducible]
/--
Definition of `groupOfIsUnit` / `groupOfIsUnit` 的定义

English:
definition groupOfIsUnit
  signature: [hM : Monoid M] (h : forall a : M, IsUnit a)
  body: { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

中文:
定义 groupOfIsUnit
  签名: [hM : 幺半群 M] (h : 对任意 a : M, 是单位 a)
  定义体: { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

Depends on / 依赖: Units.inv_mul_eq_iff_eq_mul, invOfIsUnit, inv_mul_cancel, inv_mul_eq_iff_eq_mul, mul_one, unit_spec
-/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : forall a : M, IsUnit a) : Group M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

/-- Constructs a `CommGroup` structure on a `CommMonoid` consisting only of units. -/
@[instance_reducible]
/--
Definition of `commGroupOfIsUnit` / `commGroupOfIsUnit` 的定义

English:
definition commGroupOfIsUnit
  signature: [hM : CommMonoid M] (h : forall a : M, IsUnit a)
  body: { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

中文:
定义 commGroupOfIsUnit
  签名: [hM : 交换幺半群 M] (h : 对任意 a : M, 是单位 a)
  定义体: { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

Depends on / 依赖: Units.inv_mul_eq_iff_eq_mul, invOfIsUnit, inv_mul_cancel, inv_mul_eq_iff_eq_mul, mul_one, unit_spec
-/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : forall a : M, IsUnit a) : CommGroup M :=
  { hM with
    toInv := invOfIsUnit h,
    inv_mul_cancel := fun a => by
      change ↑(h a).unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [(h a).unit_spec]; rw [mul_one] }

end NoncomputableDefs
