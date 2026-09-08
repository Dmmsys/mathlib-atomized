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
/-
**Units.smul_mk0** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g != 0) (a : α) : mk0 g hg
 • a = g • a
参数：hg : g != 0；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a := rfl

end Units

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {a : α}

/-
**inv_smul_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
@[simp] lemma inv_smul_smul₀ (ha : a ≠ 0) (x : β) : a⁻¹ • a • x = x :=
  inv_smul_smul (Units.mk0 a ha) x

@[simp]
/-
**smul_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma smul_inv_smul₀ (ha : a ≠ 0) (x : β) : a • a⁻¹ • x = x := smul_inv_smul (Units.mk0 a ha) x
/-
**inv_smul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
lemma inv_smul_eq_iff₀ (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  inv_smul_eq_iff (g := Units.mk0 a ha)
/-
**eq_inv_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
lemma eq_inv_smul_iff₀ (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  eq_inv_smul_iff (g := Units.mk0 a ha)

@[simp]
/-
**SemiconjBy.smul_right_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_right_iff {a b x : H} {r : G} : SemiconjBy x (r • a) (r • 
b) ↔ SemiconjBy x a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `SemiconjBy.smul_right`：SemiconjBy.smul_right [Mul α] [SMulCommClass M α 
α] [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy
 x (r • a) …
-/
lemma SemiconjBy.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
    (ha : a ≠ 0) : SemiconjBy x (a • y) (a • z) ↔ SemiconjBy x y z :=
  smul_right_iff (r := Units.mk0 a ha)

@[simp]
/-
**SemiconjBy.smul_left_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.smul_left_iff {a b x : H} {r : G} : SemiconjBy (r • x) a b ↔ Se
miconjBy x a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `SemiconjBy.smul_left`：SemiconjBy.smul_left [Mul α] [SMulCommClass M α α]
 [IsScalarTower M α α] {x a b : α} (h : SemiconjBy x a b) (r : M) : SemiconjBy (
r • x) a b
-/
lemma SemiconjBy.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y z : β}
    (ha : a ≠ 0) : SemiconjBy (a • x) y z ↔ SemiconjBy x y z :=
  smul_left_iff (r := Units.mk0 a ha)

@[simp]
/-
**Commute.smul_right_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_right_iff : Commute a (g • b) ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_right_iff`：SemiconjBy.smul_right_iff {a b x : H} {r : G}
 : SemiconjBy x (r • a) (r • b) ↔ SemiconjBy x a b
-/
lemma Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute x (a • y) ↔ Commute x y :=
  SemiconjBy.smul_right_iff₀ ha

@[simp]
/-
**Commute.smul_left_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.smul_left_iff : Commute (g • a) b ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.smul_left_iff`：SemiconjBy.smul_left_iff {a b x : H} {r : G} :
 SemiconjBy (r • x) a b ↔ SemiconjBy x a b
-/
lemma Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute (a • x) y ↔ Commute x y :=
  SemiconjBy.smul_left_iff₀ ha

/-- Right scalar multiplication as a bijection. -/
/-
**Equiv.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_4} → {β : Type u_5} → [inst : GroupWithZero α] → [MulAction α 
β] → {a : α} → a ≠ 0 → β ≃ β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x

--- 原说明 ---
Right scalar multiplication as a bijection.
-/
@[simps] def Equiv.smulRight (ha : a ≠ 0) : β ≃ β where
  toFun b := a • b
  invFun b := a⁻¹ • b
  left_inv := inv_smul_smul₀ ha
  right_inv := smul_inv_smul₀ ha

end GroupWithZero

namespace Units

/-! ### Action of the units of `M` on a type `α` -/

/-
**Units.instSMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instSMulZeroClass [Monoid M] [Zero α] [SMulZeroClass M α] : SMulZeroClass 
Mˣ α where smul_zero m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Action of the units of `M` on a type `α`
-/
instance instSMulZeroClass [Monoid M] [Zero α] [SMulZeroClass M α] : SMulZeroClass Mˣ α where
  smul_zero m := smul_zero (m : M)
/-
**Units.instDistribSMulUnits** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instDistribSMulUnits [Monoid M] [AddZeroClass α] [DistribSMul M α] : Distr
ibSMul Mˣ α where smul_add m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMulUnits [Monoid M] [AddZeroClass α] [DistribSMul M α] :
    DistribSMul Mˣ α where smul_add m := smul_add (m : M)
/-
**Units.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] : Dis
tribMulAction Mˣ α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid M] [AddMonoid α] [DistribMulAction M α] :
    DistribMulAction Mˣ α where
  __ := instDistribSMulUnits
  one_smul := fun b => one_smul M b
  mul_smul := fun x y b => mul_smul (x : M) y b
/-
**Units.instMulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] : 
MulDistribMulAction Mˣ α where smul_mul m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulDistribMulAction [Monoid M] [Monoid α] [MulDistribMulAction M α] :
    MulDistribMulAction Mˣ α where
  smul_mul m := smul_mul' (m : M)
  smul_one m := smul_one (m : M)

end Units

section Monoid
variable [Monoid G] [AddMonoid M] [DistribMulAction G M] {u : G} {x : M}

/-
**IsUnit.smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {G : Type u_2} {M : Type u_3} [inst : Monoid G] [inst_1 : AddMonoid M] [
inst_2 : DistribMulAction G M] {u : G}   {x : M}, IsUnit u → (u • x = 0 ↔ x = 0)
参数：u • x = 0 ↔ x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_eq_zero_iff_eq`：smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x
 = 0
-/
@[simp] lemma IsUnit.smul_eq_zero (hu : IsUnit u) : u • x = 0 ↔ x = 0 := smul_eq_zero_iff_eq hu.unit

end Monoid

