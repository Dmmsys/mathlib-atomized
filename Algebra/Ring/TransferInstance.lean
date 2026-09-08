/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Field Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

/-- An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
/-
**Equiv.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ringEquiv (e : α ≃ β) [Add β] [Mul β] : by let add
参数：e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }

@[simp]
/-
**Equiv.ringEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : ringEquiv e a = e a
参数：e : α ≃ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : ringEquiv e a = e a := rfl
/-
**Equiv.ringEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by letI
参数：e : α ≃ β；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

/-- Transfer `NonUnitalNonAssocSemiring` across an `Equiv` -/
/-
**Equiv.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalNonAssocSemiring β] → 
NonUnitalNonAssocSemiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalNonAssocSemiring` across an `Equiv`
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalSemiring` across an `Equiv` -/
/-
**Equiv.nonUnitalSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalSemiring β] → NonUnita
lSemiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalSemiring` across an `Equiv`
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

-- See note [instance transfer via equivalence]
/-- Transfer `AddMonoidWithOne` across an `Equiv` -/
/-
**Equiv.addMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [AddMonoidWithOne β] → AddMonoid
WithOne α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `AddMonoidWithOne` across an `Equiv`
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.invFun n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }

/-- Transfer `AddGroupWithOne` across an `Equiv` -/
/-
**Equiv.addGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [AddGroupWithOne β] → AddGroupWi
thOne α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.neg_add_cancel`：∀ {A : Type u} [self : AddGroup A] (a : A), -a 
+ a = 0

--- 原说明 ---
Transfer `AddGroupWithOne` across an `Equiv`
-/
protected abbrev addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.invFun n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
      congr_arg e.invFun <| (Int.cast_negSucc _).trans <| congr_arg _ (e.apply_symm_apply _).symm }

/-- Transfer `NonAssocSemiring` across an `Equiv` -/
/-
**Equiv.nonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonAssocSemiring β] → NonAssocS
emiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonAssocSemiring` across an `Equiv`
-/
protected abbrev nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Semiring` across an `Equiv` -/
/-
**Equiv.semiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Semiring β] → Semiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Semiring` across an `Equiv`
-/
protected abbrev semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalCommSemiring` across an `Equiv` -/
/-
**Equiv.nonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalCommSemiring β] → NonU
nitalCommSemiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalCommSemiring` across an `Equiv`
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul ℕ
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommSemiring` across an `Equiv` -/
/-
**Equiv.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [CommSemiring β] → CommSemiring 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CommSemiring` across an `Equiv`
-/
protected abbrev commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow ℕ
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalNonAssocRing` across an `Equiv` -/
/-
**Equiv.nonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalNonAssocRing β] → NonU
nitalNonAssocRing α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalNonAssocRing` across an `Equiv`
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalRing` across an `Equiv` -/
/-
**Equiv.nonUnitalRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalRing β] → NonUnitalRin
g α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalRing` across an `Equiv`
-/
protected abbrev nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonAssocRing` across an `Equiv` -/
/-
**Equiv.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonAssocRing β] → NonAssocRing 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonAssocRing` across an `Equiv`
-/
protected abbrev nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Ring` across an `Equiv` -/
/-
**Equiv.ring** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Ring β] → Ring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Ring` across an `Equiv`
-/
protected abbrev ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `NonUnitalCommRing` across an `Equiv` -/
/-
**Equiv.nonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NonUnitalCommRing β] → NonUnita
lCommRing α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `NonUnitalCommRing` across an `Equiv`
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul ℕ
  let zsmul := e.smul ℤ
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommRing` across an `Equiv` -/
/-
**Equiv.commRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [CommRing β] → CommRing α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `CommRing` across an `Equiv`
-/
protected abbrev commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow ℕ
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `IsDomain` across an `Equiv` -/
/-
**Equiv.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Semiring β] [IsDomain β] (e : α ≃ 
β), IsDomain α
参数：e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `IsDomain` across an `Equiv`
-/
protected lemma isDomain [Semiring β] [IsDomain β] (e : α ≃ β) :
    letI := e.semiring
    IsDomain α :=
  letI := e.semiring; e.injective.isDomain e.ringEquiv

end Equiv

