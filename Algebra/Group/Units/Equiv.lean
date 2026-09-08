/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Multiplicative and additive equivalence acting on units.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {F α M N G : Type*}

/-- A group is isomorphic to its group of units. -/
@[to_additive (attr := simps apply_val symm_apply)
/-- An additive group is isomorphic to its group of additive units -/]
/-
**toUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toUnits [Group G] : G ≃* Gˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_cancel _, inv_mul_cancel _⟩
  invFun x := x
  map_mul' _ _ := Units.ext rfl

@[to_additive (attr := simp)]
/-
**toUnits_val_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x
参数：x : Gˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toUnits_symm_apply`：∀ {G : Type u_5} [inst : Group G] (x : Gˣ), toUnits.
symm x = ↑x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [← MulEquiv.eq_symm_apply, toUnits_symm_apply]

namespace Units

variable [Monoid M] [Monoid N]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
/-
**Units.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ
参数：h : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units.
-/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom,
    left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }

@[simp]
/-
**Units.mapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm
参数：h : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
/-
**Units.coe_mapEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x
参数：h : M ≃* N；x : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
  /-- Left addition of an additive unit is a permutation of the underlying type. -/]
/-
**Units.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mulLeft (u : Mˣ) : Equiv.Perm M where toFun x
参数：u : Mˣ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
-/
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[to_additive (attr := simp)]
/-
**Units.mulLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft
参数：u : Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun _ => rfl

@[to_additive]
/-
**Units.mulLeft_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M -> M)
参数：a : Mˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((a * ·) : M → M) :=
  (mulLeft a).bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive (attr := simps -fullyApplied apply)
/-- Right addition of an additive unit is a permutation of the underlying type. -/]
/-
**Units.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mulRight (u : Mˣ) : Equiv.Perm M where toFun x
参数：u : Mˣ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
-/
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[to_additive (attr := simp)]
/-
**Units.mulRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight
参数：u : Mˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun _ => rfl

@[to_additive]
/-
**Units.mulRight_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M -> M)
参数：a : Mˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).bijective

end Units

namespace Equiv

section Group

variable [Group G]

/-- Left multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive /-- Left addition in an `AddGroup` is a permutation of the underlying type. -/]
/-
**Equiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → Equiv.Perm G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication in a `Group` is a permutation of the underlying type.
-/
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft

@[to_additive (attr := simp)]
/-
**Equiv.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (a * ·) :=
  rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp)
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/]
/-
**Equiv.mulLeft_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G -> G) = (a⁻¹ * ·)
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (a⁻¹ * ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**Equiv.mulLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun _ => rfl

@[to_additive]
/-
**Equiv._root_.Group.mulLeft_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Group.mulLeft_bijective (a : G) : Function.Bijective (a * ·) :=
  (Equiv.mulLeft a).bijective

/-- Right multiplication in a `Group` is a permutation of the underlying type. -/
@[to_additive /-- Right addition in an `AddGroup` is a permutation of the underlying type. -/]
/-
**Equiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → Equiv.Perm G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication in a `Group` is a permutation of the underlying type.
-/
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight

@[to_additive (attr := simp)]
/-
**Equiv.coe_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl

@[to_additive (attr := simp)]
/-
**Equiv.mulRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun _ => rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[to_additive (attr := simp)
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/]
/-
**Equiv.mulRight_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G -> G) = fun x =
> x * a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl

@[to_additive]
/-
**Equiv._root_.Group.mulRight_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).bijective

/-- A version of `Equiv.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps) /-- A version of `Equiv.addLeft a (-b)` that is defeq to `a - b`. -/]
/-
**Equiv.divLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → G ≃ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.mulLeft a b⁻¹` that is defeq to `a / b`.
-/
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
/-
**Equiv.divLeft_eq_inv_trans_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：divLeft_eq_inv_trans_mulLeft (a : G) : Equiv.divLeft a = (Equiv.inv G).tra
ns (Equiv.mulLeft a)
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _

/-- A version of `Equiv.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps) /-- A version of `Equiv.addRight (-a) b` that is defeq to `b - a`. -/]
/-
**Equiv.divRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → G ≃ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.mulRight a⁻¹ b` that is defeq to `b / a`.
-/
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
/-
**Equiv.divRight_eq_mulRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _

end Group

section CommGroup

variable [CommGroup G]

@[to_additive]
/-
**Equiv.symm_divLeft** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：symm_divLeft (a : G) : (Equiv.divLeft a).symm = Equiv.divLeft a
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
-/
lemma symm_divLeft (a : G) : (Equiv.divLeft a).symm = Equiv.divLeft a :=
  ext fun _ ↦ inv_mul_eq_div _ _

@[to_additive (attr := simp)]
/-
**Equiv.divLeft_involutive** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：divLeft_involutive (a : G) : Function.Involutive (Equiv.divLeft a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_div_cancel`：div_div_cancel (a b : G) : a / (a / b) = b
-/
lemma divLeft_involutive (a : G) : Function.Involutive (Equiv.divLeft a) :=
  fun _ ↦ div_div_cancel ..

end CommGroup

end Equiv

variable (α) in
/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
/-
**unitsEquivProdSubtype** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 
* p.1 = 1} where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `αˣ` type is equivalent to a subtype of `α × α`.
-/
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2

/-- In a `DivisionCommMonoid`, `Equiv.inv` is a `MulEquiv`. There is a variant of this
`MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive (attr := simps apply)
  /-- When the `AddGroup` is commutative, `Equiv.neg` is an `AddEquiv`. -/]
/-
**MulEquiv.inv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G
参数：G : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
-/
def MulEquiv.inv (G : Type*) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[to_additive (attr := simp)]
/-
**MulEquiv.inv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] : (MulEquiv.inv G).sy
mm = MulEquiv.inv G
参数：G : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulEquiv.inv_symm (G : Type*) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl

section EquivLike
variable [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {x : M}

-- Higher priority to take over the non-additivisable `isUnit_map_iff`
@[to_additive (attr := simp high)]
/-
**MulEquiv.isUnit_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulEquiv.isUnit_map : IsUnit (f x) ↔ IsUnit x where mp hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `EquivLike.inv_apply_apply`：inv_apply_apply (e : E) (a : α) : inv e (e a)
 = a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
lemma MulEquiv.isUnit_map : IsUnit (f x) ↔ IsUnit x where
  mp hx := by
    simpa using hx.map <| MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f <| by simp⟩
      fun x y ↦ EquivLike.injective f <| by simp
  mpr := .map f
/-
**isLocalHom_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N] (f : F), IsLocalHo
m f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[instance] theorem isLocalHom_equiv : IsLocalHom f where map_nonunit := by simp

end EquivLike

