/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Group-like elements in a bialgebra

This file proves that group-like elements in a bialgebra form a monoid.
-/

@[expose] public section

open Coalgebra Bialgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

/-- In a bialgebra, `1` is a group-like element. -/
/-
**IsGroupLikeElem.one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where counit_eq_one
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1

--- 原说明 ---
In a bialgebra, `1` is a group-like element.
-/
lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  counit_eq_one := counit_one
  comul_eq_tmul_self := comul_one

/-- Group-like elements in a bialgebra are stable under multiplication. -/
/-
**IsGroupLikeElem.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) 
: IsGroupLikeElem R (a * b) where counit_eq_one
参数：ha : IsGroupLikeElem R a；hb : IsGroupLikeElem R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Bialgebra.counit_mul`：counit_mul (a b : A) : counit (R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Bialgebra.comul_mul`：comul_mul (a b : A) : comul (R
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…

--- 原说明 ---
Group-like elements in a bialgebra are stable under multiplication.
-/
lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  counit_eq_one := by simp [ha, hb]
  comul_eq_tmul_self := by simp [ha, hb]

variable (R A) in
/-- The group-like elements form a submonoid. -/
/-
**groupLikeSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupLikeSubmonoid : Submonoid A where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsGroupLikeElem.mul`：IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb 
: IsGroupLikeElem R b) : IsGroupLikeElem R (a * b) where counit_eq_one
· 使用引理 `IsGroupLikeElem.one`：IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) whe
re counit_eq_one

--- 原说明 ---
The group-like elements form a submonoid.
-/
def groupLikeSubmonoid : Submonoid A where
  carrier := {a | IsGroupLikeElem R a}
  one_mem' := .one
  mul_mem' := .mul

/-- Group-like elements in a bialgebra are stable under power. -/
/-
**IsGroupLikeElem.pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.pow {n : Nat} (ha : IsGroupLikeElem R a) : IsGroupLikeElem
 R (a ^ n)
参数：ha : IsGroupLikeElem R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.pow_mem`：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) 
{x : M}, x ∈ S → ∀ (n : ℕ), x ^ n ∈ S

--- 原说明 ---
Group-like elements in a bialgebra are stable under power.
-/
lemma IsGroupLikeElem.pow {n : ℕ} (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (a ^ n) :=
  (groupLikeSubmonoid R A).pow_mem ha _

/-- Group-like elements in a bialgebra are stable under inverses, when they exist. -/
/-
**IsGroupLikeElem.of_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) (ha : Is
GroupLikeElem R a) : IsGroupLikeElem R b where counit_eq_one
参数：hab : a * b = 1；hba : b * a = 1；ha : IsGroupLikeElem R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bialgebra.counit_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R
} {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.counit 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Group-like elements in a bialgebra are stable under inverses, when they exist.
-/
lemma IsGroupLikeElem.of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R b where
  counit_eq_one :=
    left_inv_eq_right_inv (a := counit a) (by simp [← counit_mul, hba]) (by simp [ha])
  comul_eq_tmul_self := left_inv_eq_right_inv (a := comul a) (by simp [← comul_mul, hba])
    (by simp [ha, hab, Algebra.TensorProduct.one_def])

/-- Group-like elements in a bialgebra are stable under inverses, when they exist. -/
/-
**isGroupLikeElem_iff_of_mul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isGroupLikeElem_iff_of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) : Is
GroupLikeElem R a ↔ IsGroupLikeElem R b
参数：hab : a * b = 1；hba : b * a = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsGroupLikeElem.of_mul_eq_one`：IsGroupLikeElem.of_mul_eq_one (hab : a * 
b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) : IsGroupLikeElem R b where 
counit_eq_one

--- 原说明 ---
Group-like elements in a bialgebra are stable under inverses, when they exist.
-/
lemma isGroupLikeElem_iff_of_mul_eq_one (hab : a * b = 1) (hba : b * a = 1) :
    IsGroupLikeElem R a ↔ IsGroupLikeElem R b := ⟨.of_mul_eq_one hab hba, .of_mul_eq_one hba hab⟩
/-
**isGroupLikeElem_unitsInv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Bialgebra R A] {u : Aˣ},   IsGroupLikeElem R ↑u⁻¹ ↔ IsGroupLikeEle
m R ↑u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isGroupLikeElem_iff_of_mul_eq_one`：isGroupLikeElem_iff_of_mul_eq_one (ha
b : a * b = 1) (hba : b * a = 1) : IsGroupLikeElem R a ↔ IsGroupLikeElem R b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
@[simp] lemma isGroupLikeElem_unitsInv {u : Aˣ} :
    IsGroupLikeElem R u⁻¹.val ↔ IsGroupLikeElem R u.val :=
  isGroupLikeElem_iff_of_mul_eq_one (by simp) (by simp)

alias ⟨IsGroupLikeElem.of_unitsInv, IsGroupLikeElem.unitsInv⟩ := isGroupLikeElem_unitsInv

namespace GroupLike

/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (GroupLike R A) where one := ⟨1, .one⟩
/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (GroupLike R A) where mul a b := ⟨a * b, a.2.mul b.2⟩
/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (GroupLike R A) ℕ where pow a n := ⟨a ^ n, a.2.pow⟩
/-
**GroupLike.val_one** 是 Mathlib 中的一个定理，位于命名空间 `GroupLike`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Bialgebra R A], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_one : (1 : GroupLike R A) = (1 : A) := rfl
/-
**GroupLike.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `GroupLike`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Bialgebra R A]   (a b : GroupLike R A), ↑(a * b) = ↑a * ↑b
参数：a b : GroupLike R A；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_mul (a b : GroupLike R A) : ↑(a * b) = (a * b : A) := rfl
/-
**GroupLike.val_pow** 是 Mathlib 中的一个定理，位于命名空间 `GroupLike`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Bialgebra R A]   (a : GroupLike R A) (n : ℕ), ↑(a ^ n) = ↑a ^ n
参数：a : GroupLike R A；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_pow (a : GroupLike R A) (n : ℕ) : ↑(a ^ n) = (a ^ n : A) := rfl
/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (GroupLike R A) := val_injective.monoid val val_one val_mul val_pow

variable (R A) in
/-- `GroupLike.val` as a monoid hom. -/
/-
**GroupLike.valMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `GroupLike`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) → [inst : CommSemiring R] → [inst_1 : Se
miring A] → [inst_2 : Bialgebra R A] → GroupLike R A →* A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupLike.val_one`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A], ↑1 = 1
· 使用定理 `GroupLike.val_mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Bialgebra R A]   (a b : GroupLike R A), ↑(a *
 b) = ↑…

--- 原说明 ---
`GroupLike.val` as a monoid hom.
-/
@[simps] def valMonoidHom : GroupLike R A →* A where
  toFun := val
  map_one' := val_one
  map_mul' := val_mul

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [Bialgebra R A] {a b : A}

/-
**GroupLike.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GroupLike.instCommMonoid : CommMonoid (GroupLike R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance GroupLike.instCommMonoid : CommMonoid (GroupLike R A) :=
  val_injective.commMonoid val val_one val_mul val_pow
