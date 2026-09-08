/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Submonoid.Pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.leftInv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `fromCommLeftInv : N.leftInv →* N`
since the inverses are unique. When `N ≤ IsUnit.Submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `leftInvEquiv : S.leftInv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to the file
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.

`N.leftInv` is distinct from `N.units`, which is the subgroup of `Mˣ` containing all units that are
in `N`. See the implementation notes of `Mathlib/Algebra/Group/Submonoid/Units.lean` for more
details on related constructions.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of https://github.com/leanprover-community/mathlib4/pull/10679 for a possible
implementation.
-/

@[expose] public section


variable {M : Type*}

namespace Submonoid

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Monoid M] : Group (IsUnit.submonoid M) :=
  { (inferInstance : Monoid (IsUnit.submonoid M)) with
    inv := fun x ↦ ⟨x.prop.unit⁻¹.val, x.prop.unit⁻¹.isUnit⟩
    inv_mul_cancel := fun x ↦
      Subtype.ext ((Units.val_mul x.prop.unit⁻¹ _).trans x.prop.unit.inv_val) }

@[to_additive]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommMonoid M] : CommGroup (IsUnit.submonoid M) :=
  { (inferInstance : Group (IsUnit.submonoid M)) with
    mul_comm := fun a b ↦ by convert! mul_comm a b }

@[to_additive]
/-
**Submonoid._root_.IsUnit.submonoid.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.submonoid.coe_inv [Monoid M] (x : IsUnit.submonoid M) :
    ↑x⁻¹ = (↑x.prop.unit⁻¹ : M) :=
  rfl

@[deprecated (since := "2026-05-24")]
alias _root_.AddSubmonoid.IsUnit.Submonoid.coe_neg := IsAddUnit.addSubmonoid.coe_neg
set_option linter.dupNamespace false in
@[to_additive existing, deprecated (since := "2026-05-24")]
alias IsUnit.Submonoid.coe_inv := IsUnit.submonoid.coe_inv

section Monoid

variable [Monoid M] (S : Submonoid M)

/-- `S.leftInv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive
/-- `S.leftNeg` is the additive submonoid containing all the left additive inverses of `S`. -/]
/-
**Submonoid.leftInv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：leftInv : Submonoid M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def leftInv : Submonoid M where
  carrier := { x : M | ∃ y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun {a} _b ⟨a', ha⟩ ⟨b', hb⟩ ↦
    ⟨b' * a', by simp only [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩

@[to_additive]
/-
**Submonoid.leftInv_leftInv_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInv_leftInv_le : S.leftInv.leftInv <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem leftInv_leftInv_le : S.leftInv.leftInv ≤ S := by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert! z.prop
  rw [← mul_one x, ← h₁, ← mul_assoc, h₂, one_mul]

@[to_additive]
/-
**Submonoid.unit_mem_leftInv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：unit_mem_leftInv (x : Mˣ) (hx : (x : M) in S) : ((x⁻¹ :) : M) in S.leftInv
参数：x : Mˣ；hx : (x : M) in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
-/
theorem unit_mem_leftInv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ :) : M) ∈ S.leftInv :=
  ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]
/-
**Submonoid.leftInv_leftInv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInv_leftInv_eq (hS : S <= IsUnit.submonoid M) : S.leftInv.leftInv = S
参数：hS : S <= IsUnit.submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submonoid.leftInv_leftInv_le`：leftInv_leftInv_le : S.leftInv.leftInv <= 
S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Submonoid.unit_mem_leftInv`：unit_mem_leftInv (x : Mˣ) (hx : (x : M) in S
) : ((x⁻¹ :) : M) in S.leftInv
-/
theorem leftInv_leftInv_eq (hS : S ≤ IsUnit.submonoid M) : S.leftInv.leftInv = S := by
  refine le_antisymm S.leftInv_leftInv_le ?_
  intro x hx
  have : x = ((hS hx).unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_inv (hS hx).unit]
    rfl
  rw [this]
  exact S.leftInv.unit_mem_leftInv _ (S.unit_mem_leftInv _ hx)

/-- The function from `S.leftInv` to `S` sending an element to its right inverse in `S`.
This is a `MonoidHom` when `M` is commutative. -/
@[to_additive
/-- The function from `S.leftAdd` to `S` sending an element to its right additive
inverse in `S`. This is an `AddMonoidHom` when `M` is commutative. -/]
/-
**Submonoid.fromLeftInv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv : S.leftInv -> S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fromLeftInv : S.leftInv → S := fun x ↦ x.prop.choose

@[to_additive (attr := simp)]
/-
**Submonoid.mul_fromLeftInv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_fromLeftInv (x : S.leftInv) : (x : M) * S.fromLeftInv x = 1
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mul_fromLeftInv (x : S.leftInv) : (x : M) * S.fromLeftInv x = 1 :=
  x.prop.choose_spec

@[to_additive (attr := simp)]
/-
**Submonoid.fromLeftInv_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv_one : S.fromLeftInv 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submonoid.mul_fromLeftInv`：mul_fromLeftInv (x : S.leftInv) : (x : M) * S
.fromLeftInv x = 1
-/
theorem fromLeftInv_one : S.fromLeftInv 1 = 1 :=
  (one_mul _).symm.trans (Subtype.ext <| S.mul_fromLeftInv 1)

end Monoid

section CommMonoid

variable [CommMonoid M] (S : Submonoid M)

@[to_additive (attr := simp)]
/-
**Submonoid.fromLeftInv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv_mul (x : S.leftInv) : (S.fromLeftInv x : M) * x = 1
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.mul_fromLeftInv`：mul_fromLeftInv (x : S.leftInv) : (x : M) * S
.fromLeftInv x = 1
-/
theorem fromLeftInv_mul (x : S.leftInv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm, mul_fromLeftInv]

@[to_additive]
/-
**Submonoid.leftInv_le_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInv_le_isUnit : S.leftInv <= IsUnit.submonoid M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem leftInv_le_isUnit : S.leftInv ≤ IsUnit.submonoid M := fun x ⟨y, hx⟩ ↦
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
/-
**Submonoid.fromLeftInv_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv_eq_iff (a : S.leftInv) (b : M) : (S.fromLeftInv a : M) = b ↔ (
a : M) * b = 1
参数：a : S.leftInv；b : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `Submonoid.leftInv_le_isUnit`：leftInv_le_isUnit : S.leftInv <= IsUnit.sub
monoid M
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submonoid.mul_fromLeftInv`：mul_fromLeftInv (x : S.leftInv) : (x : M) * S
.fromLeftInv x = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fromLeftInv_eq_iff (a : S.leftInv) (b : M) :
    (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (leftInv_le_isUnit _ a.prop), S.mul_fromLeftInv, eq_comm]

/-- The `MonoidHom` from `S.leftInv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive (attr := simps) /-- The `AddMonoidHom` from `S.leftNeg` to `S` sending an element to
its right additive inverse in  `S`. -/]
/-
**Submonoid.fromCommLeftInv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：fromCommLeftInv : S.leftInv ->* S where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fromCommLeftInv : S.leftInv →* S where
  toFun := S.fromLeftInv
  map_one' := S.fromLeftInv_one
  map_mul' x y :=
    Subtype.ext <| by
      rw [fromLeftInv_eq_iff, mul_comm x, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, ←
        mul_assoc (x : M), mul_fromLeftInv, one_mul, mul_fromLeftInv]

variable (hS : S ≤ IsUnit.submonoid M)

set_option backward.isDefEq.respectTransparency false in
/-- The submonoid of pointwise inverse of `S` is `MulEquiv` to `S`. -/
@[to_additive (attr := simps apply) /-- The additive submonoid of pointwise additive inverse of `S`
is `AddEquiv` to `S`. -/]
/-
**Submonoid.leftInvEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：leftInvEquiv : S.leftInv ≃* S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def leftInvEquiv : S.leftInv ≃* S :=
  { S.fromCommLeftInv with
    invFun := fun x ↦ ⟨↑(hS x.2).unit⁻¹, x, by simp⟩
    left_inv := by
      intro x
      ext
      simp [← Units.mul_eq_one_iff_inv_eq]
    right_inv := by
      rintro ⟨x, hx⟩
      ext
      simp [fromLeftInv_eq_iff] }

@[to_additive (attr := simp)]
/-
**Submonoid.fromLeftInv_leftInvEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv_leftInvEquiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS)
.symm x) = x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem fromLeftInv_leftInvEquiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x

@[to_additive (attr := simp)]
/-
**Submonoid.leftInvEquiv_symm_fromLeftInv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInvEquiv_symm_fromLeftInv (x : S.leftInv) : (S.leftInvEquiv hS).symm (
S.fromLeftInv x) = x
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInvEquiv_symm_fromLeftInv (x : S.leftInv) :
    (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x

@[to_additive]
/-
**Submonoid.leftInvEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInvEquiv_mul (x : S.leftInv) : (S.leftInvEquiv hS x : M) * x = 1
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.leftInvEquiv_apply`：∀ {M : Type u_1} [inst : CommMonoid M] (S 
: Submonoid M) (hS : S ≤ IsUnit.submonoid M) (a : ↥S.leftInv),   (S.leftInvEquiv
 hS) a = (↑S.fromC…
· 使用定理 `Submonoid.fromLeftInv_mul`：fromLeftInv_mul (x : S.leftInv) : (S.fromLeft
Inv x : M) * x = 1
-/
theorem leftInvEquiv_mul (x : S.leftInv) : (S.leftInvEquiv hS x : M) * x = 1 := by
  simpa only [leftInvEquiv_apply, fromCommLeftInv] using fromLeftInv_mul S x

@[to_additive]
/-
**Submonoid.mul_leftInvEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_leftInvEquiv (x : S.leftInv) : (x : M) * S.leftInvEquiv hS x = 1
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.leftInvEquiv_apply`：∀ {M : Type u_1} [inst : CommMonoid M] (S 
: Submonoid M) (hS : S ≤ IsUnit.submonoid M) (a : ↥S.leftInv),   (S.leftInvEquiv
 hS) a = (↑S.fromC…
· 使用定理 `Submonoid.mul_fromLeftInv`：mul_fromLeftInv (x : S.leftInv) : (x : M) * S
.fromLeftInv x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_leftInvEquiv (x : S.leftInv) : (x : M) * S.leftInvEquiv hS x = 1 := by
  simp only [leftInvEquiv_apply, fromCommLeftInv, mul_fromLeftInv]

@[to_additive (attr := simp)]
/-
**Submonoid.leftInvEquiv_symm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInvEquiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submonoid.mul_leftInvEquiv`：mul_leftInvEquiv (x : S.leftInv) : (x : M) *
 S.leftInvEquiv hS x = 1
-/
theorem leftInvEquiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 := by
  convert! S.mul_leftInvEquiv hS ((S.leftInvEquiv hS).symm x)
  simp

@[to_additive (attr := simp)]
/-
**Submonoid.mul_leftInvEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mul_leftInvEquiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submonoid.leftInvEquiv_mul`：leftInvEquiv_mul (x : S.leftInv) : (S.leftIn
vEquiv hS x : M) * x = 1
-/
theorem mul_leftInvEquiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 := by
  convert! S.leftInvEquiv_mul hS ((S.leftInvEquiv hS).symm x)
  simp

end CommMonoid

section Group

variable [Group M] (S : Submonoid M)

open scoped Pointwise

@[to_additive]
/-
**Submonoid.leftInv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInv_eq_inv : S.leftInv = S⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_inv`：mem_inv {g : G} {S : Submonoid G} : g in S⁻¹ ↔ g⁻¹ in
 S
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem leftInv_eq_inv : S.leftInv = S⁻¹ :=
  Submonoid.ext fun _ ↦
    ⟨fun h ↦ Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.choose_spec).symm ▸
      h.choose.prop),
      fun h ↦ ⟨⟨_, h⟩, mul_inv_cancel _⟩⟩

@[to_additive (attr := simp)]
/-
**Submonoid.fromLeftInv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：fromLeftInv_eq_inv (x : S.leftInv) : (S.fromLeftInv x : M) = (x : M)⁻¹
参数：x : S.leftInv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Submonoid.mul_fromLeftInv`：mul_fromLeftInv (x : S.leftInv) : (x : M) * S
.fromLeftInv x = 1
-/
theorem fromLeftInv_eq_inv (x : S.leftInv) : (S.fromLeftInv x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_inv_cancel, mul_fromLeftInv]

end Group

section CommGroup

variable [CommGroup M] (S : Submonoid M) (hS : S ≤ IsUnit.submonoid M)

@[to_additive (attr := simp)]
/-
**Submonoid.leftInvEquiv_symm_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：leftInvEquiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = (x :
 M)⁻¹
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Submonoid.mul_leftInvEquiv_symm`：mul_leftInvEquiv_symm (x : S) : (x : M)
 * (S.leftInvEquiv hS).symm x = 1
-/
theorem leftInvEquiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = (x : M)⁻¹ := by
  rw [← mul_right_inj (x : M), mul_inv_cancel, mul_leftInvEquiv_symm]

end CommGroup

end Submonoid

