/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplicative actions with zero on and by `Mˣ`

This file provides the multiplicative actions with zero of a unit on a type `α`, `SMul Mˣ α`, in the
presence of `SMulWithZero M α`, with the obvious definition stated in `Units.smul_def`.

Additionally, a `MulDistribMulAction G M` for some group `G` satisfying some additional properties
admits a `MulDistribMulAction G Mˣ` structure, again with the obvious definition stated in
`Units.coe_smul`. This instance uses a primed name.

## Implementation notes

We previously had
```
instance mulDistribMulAction' [Group G] [Monoid M] [MulDistribMulAction G M] [SMulCommClass G M M]
  [IsScalarTower G M M] : MulDistribMulAction G Mˣ
```
as a strengthening of `Units.mulAction'`, but in fact this instance (almost) never applies!
`MulDistribMulAction G M` means `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = g • m₁ * g • m₂`, while
`SMulCommClass G M M` means `∀ (g : G) (m₁ m₂ : M), g • (m₁ * m₂) = m₁ * g • m₂`.
In particular, if `M` is cancellative, then we obtain
`∀ (g : G) (m : M), g • m = m`, i.e. the action is trivial!

## See also

* `Algebra.GroupWithZero.Action.Opposite`
* `Algebra.GroupWithZero.Action.Pi`
* `Algebra.GroupWithZero.Action.Prod`
-/

@[expose] public section

assert_not_exists Ring

variable {G₀ G M α β : Type*}

namespace Units
variable [GroupWithZero G₀]

@[simp]
/--
lemma `smul_mk0` / 引理 `smul_mk0`

English:
lemma smul_mk0
  given: {α : Type*} [SMul G₀ α] {g : G₀} (hg : g != 0) (a : α)
  statement: mk0 g hg • a = g • a
  proof: rfl

中文:
引理 smul_mk0
  条件: {α : 类型} [标量乘法 G₀ α] {g : G₀} (hg : g != 0) (a : α)
  结论: mk0 g hg • a = g • a
  证明: rfl
-/
lemma smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g != 0) (a : α) : mk0 g hg • a = g • a := rfl

end Units

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {a : α}

/--
lemma `inv_smul_smul₀` / 引理 `inv_smul_smul₀`

English:
lemma inv_smul_smul₀
  given: (ha : a != 0) (x : β)
  statement: a⁻¹ • a • x = x
  proof: inv_smul_smul (Units.mk0 a ha) x

@[simp]

中文:
引理 inv_smul_smul₀
  条件: (ha : a != 0) (x : β)
  结论: a⁻¹ • a • x = x
  证明: inv_smul_smul (Units.mk0 a ha) x

@[simp]
-/
@[simp] lemma inv_smul_smul₀ (ha : a != 0) (x : β) : a⁻¹ • a • x = x :=
  inv_smul_smul (Units.mk0 a ha) x

@[simp]
/--
lemma `smul_inv_smul₀` / 引理 `smul_inv_smul₀`

English:
lemma smul_inv_smul₀
  given: (ha : a != 0) (x : β)
  statement: a • a⁻¹ • x = x
  proof: smul_inv_smul (Units.mk0 a ha) x

中文:
引理 smul_inv_smul₀
  条件: (ha : a != 0) (x : β)
  结论: a • a⁻¹ • x = x
  证明: smul_inv_smul (Units.mk0 a ha) x

Depends on / 依赖: Units.mk0, smul_inv_smul
-/
lemma smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x := smul_inv_smul (Units.mk0 a ha) x

/--
lemma `inv_smul_eq_iff₀` / 引理 `inv_smul_eq_iff₀`

English:
lemma inv_smul_eq_iff₀
  given: (ha : a != 0) {x y : β}
  statement: a⁻¹ • x = y ↔ x = a • y
  proof: inv_smul_eq_iff (g := Units.mk0 a ha)

中文:
引理 inv_smul_eq_iff₀
  条件: (ha : a != 0) {x y : β}
  结论: a⁻¹ • x = y ↔ x = a • y
  证明: inv_smul_eq_iff (g := Units.mk0 a ha)

Depends on / 依赖: Units.mk0, inv_smul_eq_iff
-/
lemma inv_smul_eq_iff₀ (ha : a != 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  inv_smul_eq_iff (g := Units.mk0 a ha)

/--
lemma `eq_inv_smul_iff₀` / 引理 `eq_inv_smul_iff₀`

English:
lemma eq_inv_smul_iff₀
  given: (ha : a != 0) {x y : β}
  statement: x = a⁻¹ • y ↔ a • x = y
  proof: eq_inv_smul_iff (g := Units.mk0 a ha)

@[simp]

中文:
引理 eq_inv_smul_iff₀
  条件: (ha : a != 0) {x y : β}
  结论: x = a⁻¹ • y ↔ a • x = y
  证明: eq_inv_smul_iff (g := Units.mk0 a ha)

@[simp]

Depends on / 依赖: Units.mk0, eq_inv_smul_iff
-/
lemma eq_inv_smul_iff₀ (ha : a != 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  eq_inv_smul_iff (g := Units.mk0 a ha)

@[simp]
/--
lemma `SemiconjBy.smul_right_iff₀` / 引理 `SemiconjBy.smul_right_iff₀`

English:
lemma SemiconjBy.smul_right_iff₀
  statement: [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
  proof: smul_right_iff (r := Units.mk0 a ha)

@[simp]

中文:
引理 SemiconjBy.smul_right_iff₀
  结论: [乘法 β] [标量交换类 α β β] [标量塔 α β β] {x y z : β}
  证明: smul_right_iff (r := Units.mk0 a ha)

@[simp]

Depends on / 依赖: Units.mk0, smul_right_iff
-/
lemma SemiconjBy.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
    (ha : a != 0) : SemiconjBy x (a • y) (a • z) ↔ SemiconjBy x y z :=
  smul_right_iff (r := Units.mk0 a ha)

@[simp]
/--
lemma `SemiconjBy.smul_left_iff₀` / 引理 `SemiconjBy.smul_left_iff₀`

English:
lemma SemiconjBy.smul_left_iff₀
  statement: [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
  proof: smul_left_iff (r := Units.mk0 a ha)

@[simp]

中文:
引理 SemiconjBy.smul_left_iff₀
  结论: [乘法 β] [标量交换类 α β β] [标量塔 α β β] {x y z : β}
  证明: smul_left_iff (r := Units.mk0 a ha)

@[simp]

Depends on / 依赖: Units.mk0, smul_left_iff
-/
lemma SemiconjBy.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
    (ha : a != 0) : SemiconjBy (a • x) y z ↔ SemiconjBy x y z :=
  smul_left_iff (r := Units.mk0 a ha)

@[simp]
/--
lemma `Commute.smul_right_iff₀` / 引理 `Commute.smul_right_iff₀`

English:
lemma Commute.smul_right_iff₀
  statement: [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
  proof: SemiconjBy.smul_right_iff₀ ha

@[simp]

中文:
引理 Commute.smul_right_iff₀
  结论: [乘法 β] [标量交换类 α β β] [标量塔 α β β] {x y : β}
  证明: SemiconjBy.smul_right_iff₀ ha

@[simp]

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_right_iff
-/
lemma Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a != 0) : Commute x (a • y) ↔ Commute x y :=
  SemiconjBy.smul_right_iff₀ ha

@[simp]
/--
lemma `Commute.smul_left_iff₀` / 引理 `Commute.smul_left_iff₀`

English:
lemma Commute.smul_left_iff₀
  statement: [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
  proof: SemiconjBy.smul_left_iff₀ ha

中文:
引理 Commute.smul_left_iff₀
  结论: [乘法 β] [标量交换类 α β β] [标量塔 α β β] {x y : β}
  证明: SemiconjBy.smul_left_iff₀ ha

Depends on / 依赖: SemiconjBy, SemiconjBy.smul_left_iff
-/
lemma Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a != 0) : Commute (a • x) y ↔ Commute x y :=
  SemiconjBy.smul_left_iff₀ ha

/--
Definition of `Equiv.smulRight` / `Equiv.smulRight` 的定义

English:
definition Equiv.smulRight
  signature: (ha : a != 0)
  body: a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

中文:
定义 等价.smulRight
  签名: (ha : a != 0)
  定义体: a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

Depends on / 依赖: CochainComplex, CochainComplex.mapBifunctorShift, CochainComplex.shiftFunctorZero_eq, NatIso, NatIso.ofComponents, commShiftIso_add, commShiftIso_zero, ofComponents, shiftFunctorZero_eq
-/
@[simps] def Equiv.smulRight (ha : a != 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

end GroupWithZero

namespace Units


/--
Instance `instSMulZeroClass` / 实例 `instSMulZeroClass`

English:
instance instSMulZeroClass
  signature: [Monoid M] [Zero α] [SMulZeroClass M α]
  body: smul_zero (m : M)

中文:
实例 instSMulZeroClass
  签名: [幺半群 M] [零 α] [SMulZero类 M α]
  定义体: smul_zero (m : M)

Depends on / 依赖: smul_zero
-/
instance instSMulZeroClass [Monoid M] [Zero α] [SMulZeroClass M α] : SMulZeroClass Mˣ α where
  smul_zero m := smul_zero (m : M)

/--
Instance `instDistribSMulUnits` / 实例 `instDistribSMulUnits`

English:
instance instDistribSMulUnits
  signature: [Monoid M] [AddZeroClass α] [DistribSMul M α]
  body: smul_add (m : M)

中文:
实例 instDistribSMulUnits
  签名: [幺半群 M] [加法零类 α] [分配标量乘法 M α]
  定义体: smul_add (m : M)

Depends on / 依赖: smul_add
-/
instance instDistribSMulUnits [Monoid M] [AddZeroClass α] [DistribSMul M α] :
    DistribSMul Mˣ α where smul_add m := smul_add (m : M)

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid M] [AddMonoid α] [DistribMulAction M α]
  body: instDistribSMulUnits
  one_smul := fun b => one_smul M b
  mul_smul := fun x y b => mul_smul (x : M) y b

中文:
实例 instDistribMulAction
  签名: [幺半群 M] [加法幺半群 α] [分配乘法作用 M α]
  定义体: instDistribSMulUnits
  one_smul := fun b => one_smul M b
  mul_smul := fun x y b => mul_smul (x : M) y b

Depends on / 依赖: CochainComplex, instDistribSMulUnits
-/
instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction Mˣ α where
  __ := instDistribSMulUnits
  one_smul := fun b => one_smul M b
  mul_smul := fun x y b => mul_smul (x : M) y b

/--
Instance `instMulDistribMulAction` / 实例 `instMulDistribMulAction`

English:
instance instMulDistribMulAction
  signature: [Monoid M] [Monoid α] [MulDistribMulAction M α]
  body: smul_mul' (m : M)
  smul_one m := smul_one (m : M)

中文:
实例 instMulDistribMulAction
  签名: [幺半群 M] [幺半群 α] [MulDistribMul作用 M α]
  定义体: smul_mul' (m : M)
  smul_one m := smul_one (m : M)

Depends on / 依赖: CochainComplex, CochainComplex.mapBifunctorShift, CochainComplex.shiftFunctorZero_eq, NatIso, NatIso.ofComponents, commShiftIso_add, commShiftIso_zero, ofComponents, shiftFunctorZero_eq, smul_mul
-/
instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction Mˣ α where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one (m : M)

end Units

section Monoid
variable [Monoid G] [AddMonoid M] [DistribMulAction G M] {u : G} {x : M}

/--
lemma `IsUnit.smul_eq_zero` / 引理 `IsUnit.smul_eq_zero`

English:
lemma IsUnit.smul_eq_zero
  given: (hu : IsUnit u)
  statement: u • x = 0 ↔ x = 0
  proof: smul_eq_zero_iff_eq hu.unit

中文:
引理 是单位.smul_eq_zero
  条件: (hu : 是单位 u)
  结论: u • x = 0 ↔ x = 0
  证明: smul_eq_zero_iff_eq hu.unit
-/
@[simp] lemma IsUnit.smul_eq_zero (hu : IsUnit u) : u • x = 0 ↔ x = 0 := smul_eq_zero_iff_eq hu.unit

end Monoid
