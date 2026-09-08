/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove lemmas of the following form: if `β` has a group structure and `α ≃ β`
then `α` has a group structure, and similarly for monoids, semigroups and so on.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please use
`abbrev`. See note [reducible non-instances].
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

library_note «instance transfer via equivalence» /--
For many type classes, we have a definition that lets us transfer instances from one type to another
using an equivalence, such as `Equiv.mul` for `Mul`.
Constructing data instances in this way is discouraged because the resulting data is inefficient
to unfold. To somewhat mitigate this problem, in these definitions we don't write the
projections on `Equiv` in the usual way using `Equiv.symm` and `DFunLike.coe`, and instead use
`Equiv.toFun` and `Equiv.invFun` directly. As a result, unification has to do less unfolding.

Note also that when constructing data instances in this way, it usually helps to use
`fast_instance%` to get a faster instance.
-/

namespace Equiv
variable {M α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer `One` across an `Equiv` -/
@[to_additive /-- Transfer `Zero` across an `Equiv` -/]
/-
**Equiv.one** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [One β] → One α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `One` across an `Equiv`
-/
protected abbrev one [One β] : One α where one := e.invFun 1

@[to_additive]
/-
**Equiv.one_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：one_def [One β] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def [One β] :
    letI := e.one
    1 = e.symm 1 := rfl

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive /-- Transfer `Add` across an `Equiv` -/]
/-
**Equiv.mul** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Mul β] → Mul α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Mul` across an `Equiv`
-/
protected abbrev mul [Mul β] : Mul α where mul x y := e.invFun (e.toFun x * e.toFun y)

@[to_additive]
/-
**Equiv.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：mul_def [Mul β] (x y : α) : letI
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

/-- Transfer `Div` across an `Equiv` -/
@[to_additive /-- Transfer `Sub` across an `Equiv` -/]
/-
**Equiv.div** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Div β] → Div α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Div` across an `Equiv`
-/
protected abbrev div [Div β] : Div α :=
  ⟨fun x y => e.invFun (e.toFun x / e.toFun y)⟩

@[to_additive]
/-
**Equiv.div_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：div_def [Div β] (x y : α) : letI
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) := rfl

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive /-- Transfer `Neg` across an `Equiv` -/]
/-
**Equiv.Inv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Inv β] → Inv α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Inv` across an `Equiv`
-/
protected abbrev Inv [Inv β] : Inv α where inv x := e.invFun (e.toFun x)⁻¹

@[to_additive]
/-
**Equiv.inv_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：inv_def [Inv β] (x : α) : letI
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

variable (M) in
/-- Transfer `Pow` across an `Equiv` -/
@[to_additive (attr := to_additive /-- Transfer `VAdd` across an `Equiv` -/) smul
/-- Transfer `SMul` across an `Equiv` -/]
/-
**Equiv.pow** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) → {α : Type u_2} → {β : Type u_3} → α ≃ β → [Pow β M] → Pow
 α M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev pow [Pow β M] : Pow α M where pow x n := e.invFun (e.toFun x ^ n)

@[to_additive (attr := to_additive) smul_def]
/-
**Equiv.pow_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：pow_def [Pow β M] (n : M) (x : α) : letI
参数：n : M；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive /-- An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`. -/]
/-
**Equiv.mulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：mulEquiv (e : α ≃ β) [Mul β] : let _
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquiv (e : α ≃ β) [Mul β] :
    let _ := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        simp [mul_def] }

@[to_additive (attr := simp)]
/-
**Equiv.mulEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a
参数：e : α ≃ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a := rfl

@[to_additive (attr := simp)]
/-
**Equiv.mulEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) : letI
参数：e : α ≃ β；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive /-- Transfer `add_semigroup` across an `Equiv` -/]
/-
**Equiv.semigroup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Semigroup β] → Semigroup α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Semigroup` across an `Equiv`
-/
protected abbrev semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommSemigroup` across an `Equiv` -/]
/-
**Equiv.commSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [CommSemigroup β] → CommSemigrou
p α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CommSemigroup` across an `Equiv`
-/
protected abbrev commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `IsLeftCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsLeftCancelAdd` across an `Equiv` -/]
/-
**Equiv.isLeftCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (e : α ≃ β) [inst : Mul β] [IsLeftCancelMu
l β], IsLeftCancelMul α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [i
nst : Mul M₁] [inst_1 : Mul M₂] [IsLeftCancelMul M₂] (f : M₁ → M₂),   Function.I
njective f → (∀ (x y : M…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Transfer `IsLeftCancelMul` across an `Equiv`
-/
protected lemma isLeftCancelMul [Mul β] [IsLeftCancelMul β] :
    letI := e.mul
    IsLeftCancelMul α := by
  let := e.mul; exact e.injective.isLeftCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `IsRightCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsRightCancelAdd` across an `Equiv` -/]
/-
**Equiv.isRightCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (e : α ≃ β) [inst : Mul β] [IsRightCancelM
ul β], IsRightCancelMul α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [
inst : Mul M₁] [inst_1 : Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂),   Function
.Injective f → (∀ (x y : …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Transfer `IsRightCancelMul` across an `Equiv`
-/
protected lemma isRightCancelMul [Mul β] [IsRightCancelMul β] :
    letI := e.mul
    IsRightCancelMul α := by
  let := e.mul; exact e.injective.isRightCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `IsCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsCancelAdd` across an `Equiv` -/]
/-
**Equiv.isCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} (e : α ≃ β) [inst : Mul β] [IsCancelMul β]
, IsCancelMul α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [inst 
: Mul M₁] [inst_1 : Mul M₂] [IsCancelMul M₂] (f : M₁ → M₂),   Function.Injective
 f → (∀ (x y : M₁), …
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
Transfer `IsCancelMul` across an `Equiv`
-/
protected lemma isCancelMul [Mul β] [IsCancelMul β] :
    letI := e.mul
    IsCancelMul α := by
  let := e.mul; exact e.injective.isCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive /-- Transfer `AddZeroClass` across an `Equiv` -/]
/-
**Equiv.mulOneClass** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [MulOneClass β] → MulOneClass α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `MulOneClass` across an `Equiv`
-/
protected abbrev mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddMonoid` across an `Equiv` -/]
/-
**Equiv.monoid** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Monoid β] → Monoid α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Monoid` across an `Equiv`
-/
protected abbrev monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommMonoid` across an `Equiv` -/]
/-
**Equiv.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [CommMonoid β] → CommMonoid α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CommMonoid` across an `Equiv`
-/
protected abbrev commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Group` across an `Equiv` -/
@[to_additive /-- Transfer `AddGroup` across an `Equiv` -/]
/-
**Equiv.group** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [Group β] → Group α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Group` across an `Equiv`
-/
protected abbrev group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommGroup` across an `Equiv` -/]
/-
**Equiv.commGroup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → α ≃ β → [CommGroup β] → CommGroup α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CommGroup` across an `Equiv`
-/
protected abbrev commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

end Equiv

namespace Finite

/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/
@[to_additive
/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/]
/-
**Finite.exists_type_univ_nonempty_mulEquiv.** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_type_univ_nonempty_mulEquiv.{u, v} (G : Type u) [Group G] [Finite G] :
    ∃ (G' : Type v) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  let groupH : Group (ULift (Fin n)) := e.symm.group
  exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm <| e.symm.mulEquiv⟩⟩

end Finite

