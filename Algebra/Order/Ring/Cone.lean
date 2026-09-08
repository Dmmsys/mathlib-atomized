/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone` that encodes axioms of ordered rings
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

@[expose] public section

/-- `RingConeClass S R` says that `S` is a type of cones in `R`. -/
/-
**RingConeClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u_2)) → [Ring R] → [SetLike S R] → Pr
op
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingConeClass S R` says that `S` is a type of cones in `R`.
-/
class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R] : Prop
    extends AddGroupConeClass S R, SubsemiringClass S R

/-- A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring. -/
/-
**RingCone** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Ring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (positive) cone in a ring is a subsemiring that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the ring into a partially ordered ring.
-/
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

/-
**RingCone.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where c
oe C
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Ring R] : PartialOrder (RingCone R) := .ofSetLike (RingCone R) R
/-
**RingCone.instRingConeClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingCone.instRingConeClass (R : Type*) [Ring R] : RingConeClass (RingCone 
R) R where add_mem {C}
参数：R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.add_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self :
 Subsemiring R) {a b : R},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.
carrier
· 使用定理 `Subsemiring.zero_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self 
: Subsemiring R), 0 ∈ self.carrier
· 使用定理 `RingCone.eq_zero_of_mem_of_neg_mem'`：∀ {R : Type u_1} [inst : Ring R] (s
elf : RingCone R) {a : R}, a ∈ self.carrier → -a ∈ self.carrier → a = 0
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
-/
instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp]
/-
**RingCone.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R} (eq_z
ero_of_mem_of_neg_mem) {x : R} : x in mk toSubsemiring eq_zero_of_mem_of_neg_mem
 ↔ x in toSubsemiring
参数：eq_zero_of_mem_of_neg_mem。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x ∈ mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x ∈ toSubsemiring := .rfl

@[simp]
/-
**RingCone.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R} (
eq_zero_of_mem_of_neg_mem) : (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R
) = toSubsemiring
参数：eq_zero_of_mem_of_neg_mem。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

namespace RingCone

variable {T : Type*} [Ring T] [PartialOrder T] [IsOrderedRing T] {a : T}

variable (T) in
/-- Construct a cone from the set of non-negative elements of a partially ordered ring. -/
/-
**RingCone.nonneg** 是 Mathlib 中的一个定义，位于命名空间 `RingCone`。
形式化陈述：nonneg : RingCone T where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cone from the set of non-negative elements of a partially ordered ri
ng.
-/
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm
/-
**RingCone.nonneg_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `RingCone`。
形式化陈述：∀ {T : Type u_1} [inst : Ring T] [inst_1 : PartialOrder T] [inst_2 : IsOrd
eredRing T],   (RingCone.nonneg T).toSubsemiring = Subsemiring.nonneg T
参数：RingCone.nonneg T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
/-
**RingCone.nonneg_toAddGroupCone** 是 Mathlib 中的一个定理，位于命名空间 `RingCone`。
形式化陈述：∀ {T : Type u_1} [inst : Ring T] [inst_1 : PartialOrder T] [inst_2 : IsOrd
eredRing T],   (RingCone.nonneg T).toAddGroupCone = AddGroupCone.nonneg T
参数：RingCone.nonneg T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nonneg_toAddGroupCone : (nonneg T).toAddGroupCone = .nonneg T := rfl
/-
**RingCone.mem_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `RingCone`。
形式化陈述：∀ {T : Type u_1} [inst : Ring T] [inst_1 : PartialOrder T] [inst_2 : IsOrd
eredRing T] {a : T},   a ∈ RingCone.nonneg T ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_nonneg : a ∈ nonneg T ↔ 0 ≤ a := Iff.rfl
/-
**RingCone.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `RingCone`。
形式化陈述：∀ {T : Type u_1} [inst : Ring T] [inst_1 : PartialOrder T] [inst_2 : IsOrd
eredRing T],   ↑(RingCone.nonneg T) = {x | 0 ≤ x}
参数：RingCone.nonneg T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 ≤ x} := rfl
/-
**RingCone.nonneg.hasMemOrNegMem** 是 Mathlib 中的一个定理，位于命名空间 `RingCone.nonneg`。
形式化陈述：∀ {T : Type u_2} [inst : Ring T] [inst_1 : LinearOrder T] [inst_2 : IsOrde
redRing T], HasMemOrNegMem (RingCone.nonneg T)
参数：RingCone.nonneg T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMemOrNegMem.mem_or_neg_mem`：∀ {S : Type u_3} {G : Type u_4} {inst : N
eg G} {inst_1 : SetLike S G} (s : S) [self : HasMemOrNegMem s] (a : G),   a ∈ s 
∨ -a ∈ s
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `AddGroupCone.nonneg.hasMemOrNegMem`：∀ {H : Type u_2} [inst : AddCommGrou
p H] [inst_1 : LinearOrder H] [inst_2 : IsOrderedAddMonoid H],   HasMemOrNegMem 
(AddGroupCone.nonneg H)
-/
instance nonneg.hasMemOrNegMem {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    HasMemOrNegMem (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

/-- Construct a partially ordered ring by designating a cone in a ring. -/
/-
**IsOrderedRing.mkOfCone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOrderedRing.mkOfCone [RingConeClass S R] : letI _ : PartialOrder R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOrderedRing.of_mul_nonneg`：IsOrderedRing.of_mul_nonneg [Ring R] [Parti
alOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] (mul_nonneg : forall a b : 
R, 0 <= a -> 0 <=…
· 使用定理 `RingConeClass.toAddGroupConeClass`：∀ {S : Type u_1} {R : outParam (Type 
u_2)} {inst : Ring R} {inst_1 : SetLike S R} [self : RingConeClass S R],   AddGr
oupConeClass S R
· 使用定理 `IsOrderedAddMonoid.mkOfCone`：∀ {S : Type u_1} {G : Type u_2} [inst : Add
CommGroup G] [inst_1 : SetLike S G] (C : S) [inst_2 : AddGroupConeClass S G],   
have x := Partial…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `RingConeClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u
_2)} [inst : Ring R] [inst_1 : SetLike S R] [self : RingConeClass S R],   Subsem
iringClass S R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …

--- 原说明 ---
Construct a partially ordered ring by designating a cone in a ring.
-/
lemma IsOrderedRing.mkOfCone [RingConeClass S R] :
    letI _ : PartialOrder R := .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ ∈ C by simp⟩
  .of_mul_nonneg fun x y xnn ynn ↦ show _ ∈ C by simpa using mul_mem xnn ynn
