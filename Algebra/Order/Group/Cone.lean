/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide the structure `GroupCone` and the predicate `IsMaxCone` that encode
the axioms of ordered groups in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

@[expose] public section

/-- `AddGroupConeClass S G` says that `S` is a type of cones in `G`. -/
/-
**AddGroupConeClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (G : outParam (Type u_2)) → [AddCommGroup G] → [SetLike S
 G] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddGroupConeClass S G` says that `S` is a type of cones in `G`.
-/
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
/-
**GroupConeClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (G : outParam (Type u_2)) → [CommGroup G] → [SetLike S G]
 → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GroupConeClass S G` says that `S` is a type of cones in `G`.
-/
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] : Prop
    extends SubmonoidClass S G where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
/-
**AddGroupCone** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [AddCommGroup G] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group.
-/
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive]
/-
**GroupCone** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [CommGroup G] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group.
-/
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1

@[to_additive]
/-
**GroupCone.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G 
where coe C
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : Type*) [CommGroup G] : PartialOrder (GroupCone G) := .ofSetLike (GroupCone G) G

@[to_additive]
/-
**GroupCone.instGroupConeClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GroupCone.instGroupConeClass (G : Type*) [CommGroup G] : GroupConeClass (G
roupCone G) G where mul_mem {C}
参数：G : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用定理 `GroupCone.eq_one_of_mem_of_inv_mem'`：∀ {G : Type u_1} [inst : CommGroup 
G] (self : GroupCone G) {a : G}, a ∈ self.carrier → a⁻¹ ∈ self.carrier → a = 1
-/
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier → coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier → coe, as_prefix coe)

namespace GroupCone
variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

variable (H) in
/-- The cone of elements that are at least 1. -/
@[to_additive /-- The cone of non-negative elements. -/]
/-
**GroupCone.oneLE** 是 Mathlib 中的一个定义，位于命名空间 `GroupCone`。
形式化陈述：oneLE : GroupCone H where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone of elements that are at least 1.
-/
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp)]
/-
**GroupCone.oneLE_toSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `GroupCone`。
形式化陈述：oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp)]
/-
**GroupCone.mem_oneLE** 是 Mathlib 中的一个引理，位于命名空间 `GroupCone`。
形式化陈述：mem_oneLE : a in oneLE H ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
@[to_additive (attr := simp, norm_cast)]
/-
**GroupCone.coe_oneLE** 是 Mathlib 中的一个引理，位于命名空间 `GroupCone`。
形式化陈述：coe_oneLE : oneLE H = {x : H | 1 <= x}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

@[to_additive]
/-
**GroupCone.oneLE.hasMemOrInvMem** 是 Mathlib 中的一个定理，位于命名空间 `GroupCone.oneLE`。
形式化陈述：∀ {H : Type u_2} [inst : CommGroup H] [inst_1 : LinearOrder H] [inst_2 : I
sOrderedMonoid H],   HasMemOrInvMem (GroupCone.oneLE H)
参数：GroupCone.oneLE H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
instance oneLE.hasMemOrInvMem {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H] :
    HasMemOrInvMem (oneLE H) where
  mem_or_inv_mem := by simpa using le_total 1

end GroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
/-
**PartialOrder.mkOfGroupCone** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where le 
a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a partial order by designating a cone in an abelian group.
-/
abbrev PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
/-
**PartialOrder.mkOfGroupCone_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G
] [GroupConeClass S G] {C : S} {a b : G} : (mkOfGroupCone C).le a b ↔ b / a in C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := Iff.rfl

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
/-
**LinearOrder.mkOfGroupCone** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.mkOfGroupCone [GroupConeClass S G] [HasMemOrInvMem C] [Decidab
lePred (· in C)] : LinearOrder G where __
参数：· in C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a linear order by designating a maximal cone in an abelian group.
-/
abbrev LinearOrder.mkOfGroupCone
    [GroupConeClass S G] [HasMemOrInvMem C] [DecidablePred (· ∈ C)] : LinearOrder G where
  __ := PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
/-
**IsOrderedMonoid.mkOfCone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderedMonoid.mkOfCone [GroupConeClass S G] : let _ : PartialOrder G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_mul_right_eq_div`：mul_div_mul_right_eq_div (a b c : G) : a * c /
 (b * c) = a / b
-/
lemma IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }
