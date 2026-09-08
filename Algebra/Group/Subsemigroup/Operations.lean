/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Operations on `Subsemigroup`s

In this file we define various operations on `Subsemigroup`s and `MulHom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Subsemigroup.toAddSubsemigroup`, `Subsemigroup.toAddSubsemigroup'`,
  `AddSubsemigroup.toSubsemigroup`, `AddSubsemigroup.toSubsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) semigroup structure on a subsemigroup

* `Subsemigroup.toSemigroup`, `Subsemigroup.toCommSemigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `Subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `Subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `Subsemigroup.prod`: product of two subsemigroups `s : Subsemigroup M` and `t : Subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `Subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `Subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `MulEquiv.subsemigroupCongr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `Subsemigroup.prodEquiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `MulHom`s

* `MulHom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `MulHom.domRestrict`: restrict a semigroup homomorphism to a subsemigroup of its domain;
* `MulHom.codRestrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `MulHom.srangeRestrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `Mathlib/Algebra/Group/Submonoid/Operations.lean`, omitting only that
which is necessary.

## Tags

subsemigroup, range, product, map, comap
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N P σ : Type*}

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

variable [Mul M]

/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `Additive M`. -/
@[simps]
/-
**Subsemigroup.toAddSubsemigroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additi
ve M) where toFun S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mul_mem'`：∀ {M : Type u_3} [inst : Mul M] (self : Subsemigr
oup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier

--- 原说明 ---
Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `Addi
tive M`.
-/
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  map_rel_iff' := Iff.rfl

/-- Additive subsemigroups of an additive semigroup `Additive M` are isomorphic to subsemigroups
of `M`. -/
/-
**AddSubsemigroup.toSubsemigroup'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemig
roup M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive subsemigroups of an additive semigroup `Additive M` are isomorphic to s
ubsemigroups
of `M`.
-/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm
/-
**Subsemigroup.toAddSubsemigroup_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsemigroup.toAddSubsemigroup_closure (S : Set M) : Subsemigroup.toAddSub
semigroup (Subsemigroup.closure S) = AddSubsemigroup.closure (Additive.toMul ⁻¹'
 S)
参数：S : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubsemigroup.subset_closure`：∀ {M : Type u_1} [inst : Add M] {s : Set
 M}, s ⊆ ↑(AddSubsemigroup.closure s)
· 使用定理 `AddSubsemigroup.closure_le`：∀ {M : Type u_1} [inst : Add M] {s : Set M} 
{S : AddSubsemigroup M}, AddSubsemigroup.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    Subsemigroup.toAddSubsemigroup (Subsemigroup.closure S) =
    AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
/-
**AddSubsemigroup.toSubsemigroup'_closure** 是 Mathlib 中的一个定理，位于命名空间 `AddSubsemig
roup`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (S : Set (Additive M)),   AddSubsemigroup.
toSubsemigroup' (AddSubsemigroup.closure S) = Subsemigroup.closure (⇑Additive.of
Mul ⁻¹' S)
参数：S : Set (Additive M)；AddSubsemigroup.closure S；⇑Additive.ofMul ⁻¹' S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubsemigroup.closure_le`：∀ {M : Type u_1} [inst : Add M] {s : Set M} 
{S : AddSubsemigroup M}, AddSubsemigroup.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubsemigroup.subset_closure`：∀ {M : Type u_1} [inst : Add M] {s : Set
 M}, s ⊆ ↑(AddSubsemigroup.closure s)
-/
theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    AddSubsemigroup.toSubsemigroup' (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))

end

section

variable {A : Type*} [Add A]

/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `Multiplicative A`. -/
@[simps]
/-
**AddSubsemigroup.toSubsemigroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multip
licative A) where toFun S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubsemigroup.add_mem'`：∀ {M : Type u_3} [inst : Add M] (self : AddSub
semigroup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.car
rier

--- 原说明 ---
Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `Multiplicative A`.
-/
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  map_rel_iff' := Iff.rfl

/-- Subsemigroups of a semigroup `Multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
/-
**Subsemigroup.toAddSubsemigroup'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSu
bsemigroup A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subsemigroups of a semigroup `Multiplicative A` are isomorphic to additive subse
migroups
of `A`.
-/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm
/-
**AddSubsemigroup.toSubsemigroup_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubsemigroup.toSubsemigroup_closure (S : Set A) : AddSubsemigroup.toSub
semigroup (AddSubsemigroup.closure S) = Subsemigroup.closure (Multiplicative.toA
dd ⁻¹' S)
参数：S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubsemigroup.closure_le`：∀ {M : Type u_1} [inst : Add M] {s : Set M} 
{S : AddSubsemigroup M}, AddSubsemigroup.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubsemigroup.subset_closure`：∀ {M : Type u_1} [inst : Add M] {s : Set
 M}, s ⊆ ↑(AddSubsemigroup.closure s)
-/
theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    AddSubsemigroup.toSubsemigroup (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
      AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))
/-
**Subsemigroup.toAddSubsemigroup'_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigrou
p`。
形式化陈述：∀ {A : Type u_5} [inst : Add A] (S : Set (Multiplicative A)),   Subsemigro
up.toAddSubsemigroup' (Subsemigroup.closure S) = AddSubsemigroup.closure (⇑Multi
plicative.ofAdd ⁻¹' S)
参数：S : Set (Multiplicative A)；Subsemigroup.closure S；⇑Multiplicative.ofAdd ⁻¹' S
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubsemigroup.subset_closure`：∀ {M : Type u_1} [inst : Add M] {s : Set
 M}, s ⊆ ↑(AddSubsemigroup.closure s)
· 使用定理 `AddSubsemigroup.closure_le`：∀ {M : Type u_1} [inst : Add M] {s : Set M} 
{S : AddSubsemigroup M}, AddSubsemigroup.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    Subsemigroup.toAddSubsemigroup' (Subsemigroup.closure S) =
      AddSubsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
      Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      /-- The preimage of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is an
      `AddSubsemigroup`. -/]
/-
**Subsemigroup.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：comap (f : M ->ₙ* N) (S : Subsemigroup N) : Subsemigroup M where carrier
参数：f : M ->ₙ* N；S : Subsemigroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap (f : M →ₙ* N) (S : Subsemigroup N) :
    Subsemigroup M where
  carrier := f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact mul_mem ha hb

@[to_additive (attr := simp)]
/-
**Subsemigroup.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_comap (S : Subsemigroup N) (f : M ->ₙ* N) : (S.comap f : Set M) = f ⁻¹
' S
参数：S : Subsemigroup N；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_comap {S : Subsemigroup N} {f : M ->ₙ* N} {x : M} : x in S.comap f ↔ f
 x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[to_additive]
/-
**Subsemigroup.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_comap (S : Subsemigroup P) (g : N ->ₙ* P) (f : M ->ₙ* N) : (S.comap 
g).comap f = S.comap (g.comp f)
参数：S : Subsemigroup P；g : N ->ₙ* P；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S
参数：S : Subsemigroup P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.ext`：ext {S T : Subsemigroup M} (h : forall x, x in S ↔ x i
n T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulHom.id_apply`：∀ (M : Type u_10) [inst : Mul M] (x : M), (MulHom.id M)
 x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext (by simp)

/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      /-- The image of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is
      an `AddSubsemigroup`. -/]
/-
**Subsemigroup.map** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：map (f : M ->ₙ* N) (S : Subsemigroup M) : Subsemigroup N where carrier
参数：f : M ->ₙ* N；S : Subsemigroup M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N where
  carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
/-
**Subsemigroup.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_map (f : M ->ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S
参数：f : M ->ₙ* N；S : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_map {f : M ->ₙ* N} {S : Subsemigroup M} {y : N} : y in S.map f ↔ exist
s x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image _ _ _

@[to_additive]
/-
**Subsemigroup.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_map_of_mem (f : M ->ₙ* N) {S : Subsemigroup M} {x : M} (hx : x in S) :
 f x in S.map f
参数：f : M ->ₙ* N；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[to_additive]
/-
**Subsemigroup.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：apply_coe_mem_map (f : M ->ₙ* N) (S : Subsemigroup M) (x : S) : f x in S.m
ap f
参数：f : M ->ₙ* N；S : Subsemigroup M；x : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_map_of_mem`：mem_map_of_mem (f : M ->ₙ* N) {S : Subsemig
roup M} {x : M} (hx : x in S) : f x in S.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop

@[to_additive]
/-
**Subsemigroup.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_map (g : N ->ₙ* P) (f : M ->ₙ* N) : (S.map f).map g = S.map (g.comp f)
参数：g : N ->ₙ* P；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

@[to_additive (attr := simp high)]
/-
**Subsemigroup.mem_map_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_map_iff_mem {f : M ->ₙ* N} (hf : Function.Injective f) {S : Subsemigro
up M} {x : M} : f x in S.map f ↔ x in S
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[to_additive]
/-
**Subsemigroup.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_le_iff_le_comap {f : M ->ₙ* N} {S : Subsemigroup M} {T : Subsemigroup 
N} : S.map f <= T ↔ S <= T.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[to_additive]
/-
**Subsemigroup.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：gc_map_comap (f : M ->ₙ* N) : GaloisConnection (map f) (comap f)
参数：f : M ->ₙ* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₙ* N} {S 
: Subsemigroup M} {T : Subsemigroup N} : S.map f <= T ↔ S <= T.comap f
-/
theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
/-
**Subsemigroup.map_le_of_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_le_of_le_comap {T : Subsemigroup N} {f : M ->ₙ* N} : S <= T.comap f ->
 S.map f <= T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[to_additive]
/-
**Subsemigroup.le_comap_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：le_comap_of_map_le {T : Subsemigroup N} {f : M ->ₙ* N} : S.map f <= T -> S
 <= T.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ {a : α}
 {b : β}, l…
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
/-
**Subsemigroup.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：le_comap_map {f : M ->ₙ* N} : S <= (S.map f).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/-
**Subsemigroup.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_comap_le {S : Subsemigroup N} {f : M ->ₙ* N} : (S.comap f).map f <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[to_additive]
/-
**Subsemigroup.monotone_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：monotone_map {f : M ->ₙ* N} : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem monotone_map {f : M →ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive]
/-
**Subsemigroup.monotone_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：monotone_comap {f : M ->ₙ* N} : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem monotone_comap {f : M →ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]
/-
**Subsemigroup.map_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_comap_map {f : M ->ₙ* N} : ((S.map f).comap f).map f = S.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]
/-
**Subsemigroup.comap_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_map_comap {S : Subsemigroup N} {f : M ->ₙ* N} : ((S.comap f).map f).
comap f = S.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
/-
**Subsemigroup.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_sup (S T : Subsemigroup M) (f : M ->ₙ* N) : (S ⊔ T).map f = S.map f ⊔ 
T.map f
参数：S T : Subsemigroup M；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
/-
**Subsemigroup.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_iSup {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup M) : (iSup s).m
ap f = ⨆ i, (s i).map f
参数：f : M ->ₙ* N；s : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup M) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
/-
**Subsemigroup.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_inf (S T : Subsemigroup M) (f : M ->ₙ* N) (hf : Function.Injective f) 
: (S ⊓ T).map f = S.map f ⊓ T.map f
参数：S T : Subsemigroup M；f : M ->ₙ* N；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (S T : Subsemigroup M) (f : M →ₙ* N) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/-
**Subsemigroup.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : M ->ₙ* N) (hf : Function.Injective 
f) (s : ι -> Subsemigroup M) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : M ->ₙ* N；hf : Function.Injective f；s : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subsemigroup M} : 
(↑(⨅ i, S i) : Set M) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : M →ₙ* N) (hf : Function.Injective f)
    (s : ι → Subsemigroup M) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/-
**Subsemigroup.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_inf (S T : Subsemigroup N) (f : M ->ₙ* N) : (S ⊓ T).comap f = S.coma
p f ⊓ T.comap f
参数：S T : Subsemigroup N；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
/-
**Subsemigroup.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_iInf {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup N) : (iInf s)
.comap f = ⨅ i, (s i).comap f
参数：f : M ->ₙ* N；s : ι -> Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive (attr := simp)]
/-
**Subsemigroup.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_bot (f : M ->ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_top (f : M ->ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
-/
theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[to_additive (attr := simp)]
/-
**Subsemigroup.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S
参数：S : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.ext`：ext {S T : Subsemigroup M} (h : forall x, x in S ↔ x i
n T) : S = T
-/
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type*} {f : M →ₙ* N}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/]
/-
**Subsemigroup.gciMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap
 f)
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.
-/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

@[to_additive]
/-
**Subsemigroup.comap_map_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup
`。
形式化陈述：comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S
参数：S : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
/-
**Subsemigroup.comap_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemig
roup`。
形式化陈述：comap_surjective_of_injective : Function.Surjective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

@[to_additive]
/-
**Subsemigroup.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigrou
p`。
形式化陈述：map_injective_of_injective : Function.Injective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

@[to_additive]
/-
**Subsemigroup.comap_inf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigrou
p`。
形式化陈述：comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).co
map f = S ⊓ T
参数：S T : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
/-
**Subsemigroup.comap_iInf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：comap_iInf_map_of_injective (S : ι -> Subsemigroup M) : (⨅ i, (S i).map f)
.comap f = iInf S
参数：S : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iInf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iInf_map_of_injective (S : ι → Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

@[to_additive]
/-
**Subsemigroup.comap_sup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigrou
p`。
形式化陈述：comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).co
map f = S ⊔ T
参数：S T : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
/-
**Subsemigroup.comap_iSup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：comap_iSup_map_of_injective (S : ι -> Subsemigroup M) : (⨆ i, (S i).map f)
.comap f = iSup S
参数：S : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iSup_map_of_injective (S : ι → Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

@[to_additive]
/-
**Subsemigroup.map_le_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f <= T.map f ↔ 
S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
/-
**Subsemigroup.map_strictMono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：map_strictMono_of_injective : StrictMono (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/]
/-
**Subsemigroup.giMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：giMapComap : GaloisInsertion (map f) (comap f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

@[to_additive]
/-
**Subsemigroup.map_comap_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigrou
p`。
形式化陈述：map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S
参数：S : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
/-
**Subsemigroup.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigr
oup`。
形式化陈述：map_surjective_of_surjective : Function.Surjective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

@[to_additive]
/-
**Subsemigroup.comap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemig
roup`。
形式化陈述：comap_injective_of_surjective : Function.Injective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

@[to_additive]
/-
**Subsemigroup.map_inf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：map_inf_comap_of_surjective (S T : Subsemigroup N) : (S.comap f ⊓ T.comap 
f).map f = S ⊓ T
参数：S T : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
/-
**Subsemigroup.map_iInf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigr
oup`。
形式化陈述：map_iInf_comap_of_surjective (S : ι -> Subsemigroup N) : (⨅ i, (S i).comap
 f).map f = iInf S
参数：S : ι -> Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem map_iInf_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

@[to_additive]
/-
**Subsemigroup.map_sup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigro
up`。
形式化陈述：map_sup_comap_of_surjective (S T : Subsemigroup N) : (S.comap f ⊔ T.comap 
f).map f = S ⊔ T
参数：S T : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
/-
**Subsemigroup.map_iSup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigr
oup`。
形式化陈述：map_iSup_comap_of_surjective (S : ι -> Subsemigroup N) : (⨆ i, (S i).comap
 f).map f = iSup S
参数：S : ι -> Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem map_iSup_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

@[to_additive]
/-
**Subsemigroup.comap_le_comap_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subse
migroup`。
形式化陈述：comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f <= T.c
omap f ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
-/
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
/-
**Subsemigroup.comap_strictMono_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemi
group`。
形式化陈述：comap_strictMono_of_surjective : StrictMono (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.strictMono_u`：strictMono_u [Preorder α] [Preorder β] (gi
 : GaloisInsertion l u) : StrictMono u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

end Subsemigroup

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive (attr := simps)
  /-- The top additive subsemigroup is isomorphic to the additive semigroup. -/]
/-
**Subsemigroup.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：topEquiv : (⊤ : Subsemigroup M) ≃* M where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `Subsemigroup.mem_top`：mem_top (x : M) : x in (⊤ : Subsemigroup M)
-/
def topEquiv : (⊤ : Subsemigroup M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.topEquiv_toMulHom** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：topEquiv_toMulHom : ((topEquiv : _ ≃* M) : _ ->ₙ* M) = MulMemClass.subtype
 (⊤ : Subsemigroup M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem topEquiv_toMulHom :
    ((topEquiv : _ ≃* M) : _ →ₙ* M) = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive
/-- An additive subsemigroup is isomorphic to its image under an injective function -/]
/-
**Subsemigroup.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：equivMapOfInjective (f : M ->ₙ* N) (hf : Function.Injective f) : S ≃* S.ma
p f
参数：f : M ->ₙ* N；hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
noncomputable def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[to_additive (attr := simp)]
/-
**Subsemigroup.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subsemig
roup`。
形式化陈述：coe_equivMapOfInjective_apply (f : M ->ₙ* N) (hf : Function.Injective f) (
x : S) : (equivMapOfInjective S f hf x : N) = f x
参数：f : M ->ₙ* N；hf : Function.Injective f；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
theorem coe_equivMapOfInjective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.closure_closure_coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigr
oup`。
形式化陈述：closure_closure_coe_preimage {s : Set M} : closure ((Subtype.val : closure
 s -> M) ⁻¹' s) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subsemigroup.closure_induction`：closure_induction {p : (x : M) -> x in c
losure s -> Prop} (mem : forall (x) (h : x in s), p x (subset_closure h)) (mul :
 forall x y hx hy, p…
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
-/
theorem closure_closure_coe_preimage {s : Set M} :
    closure ((Subtype.val : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    closure_induction (fun _ h ↦ subset_closure h) (fun _ _ _ _ ↦ mul_mem) hx'

/-- Given `Subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive prod
      /-- Given `AddSubsemigroup`s `s`, `t` of `AddSemigroup`s `A`, `B` respectively,
      `s × t` as an `AddSubsemigroup` of `A × B`. -/]
/-
**Subsemigroup.prod** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) wher
e carrier
参数：s : Subsemigroup M；t : Subsemigroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) where
  carrier := s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
/-
**Subsemigroup.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_prod (s : Subsemigroup M) (t : Subsemigroup N) : (s.prod t : Set (M × 
N)) = (s : Set M) ×ˢ (t : Set N)
参数：s : Subsemigroup M；t : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
/-
**Subsemigroup.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} : p in s.pr
od t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[to_additive prod_mono]
/-
**Subsemigroup.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ <= s₂
) (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
参数：hs : s₁ <= s₂；ht : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
/-
**Subsemigroup.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：prod_top (s : Subsemigroup M) : s.prod (⊤ : Subsemigroup N) = s.comap (Mul
Hom.fst M N)
参数：s : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.ext`：ext {S T : Subsemigroup M} (h : forall x, x in S ↔ x i
n T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (s : Subsemigroup M) : s.prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_fst]

@[to_additive top_prod]
/-
**Subsemigroup.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).prod s = s.comap (Mul
Hom.snd M N)
参数：s : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.ext`：ext {S T : Subsemigroup M} (h : forall x, x in S ↔ x i
n T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/-
**Subsemigroup.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsemigroup.top_prod`：top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup
 M).prod s = s.comap (MulHom.snd M N)
· 使用定理 `Subsemigroup.comap_top`：comap_top (f : M ->ₙ* N) : (⊤ : Subsemigroup N).
comap f = ⊤
-/
theorem top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive bot_prod_bot]
/-
**Subsemigroup.bot_prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod]

/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prodEquiv
/-- The product of additive subsemigroups is isomorphic to their product as additive semigroups -/]
/-
**Subsemigroup.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.prod t ≃* s × t
参数：s : Subsemigroup M；t : Subsemigroup N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

open MulHom

@[to_additive]
/-
**Subsemigroup.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} : x in K.map (f : 
M ->ₙ* N) ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map (f : M →ₙ* N) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

@[to_additive]
/-
**Subsemigroup.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) : K.map (f : M -
>ₙ* N) = K.comap (f.symm : N ->ₙ* M)
参数：f : M ≃* N；K : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map (f : M →ₙ* N) = K.comap (f.symm : N →ₙ* M) :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/-
**Subsemigroup.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) : K.comap (f : N
 ->ₙ* M) = K.map (f.symm : M ->ₙ* N)
参数：f : N ≃* M；K : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subsemigroup.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : M ≃* 
N) (K : Subsemigroup M) : K.map (f : M ->ₙ* N) = K.comap (f.symm : N ->ₙ* M)
-/
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap (f : N →ₙ* M) = K.map (f.symm : M →ₙ* N) :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]
/-
**Subsemigroup.map_equiv_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M ->ₙ* N) = ⊤
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M →ₙ* N) = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
/-
**Subsemigroup.le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M
 × N)} : u <= s.prod t ↔ u.map (fst M N) <= s ∧ u.map (snd M N) <= t
参数：M × N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
    u ≤ s.prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive /-- The range of an `AddHom` is an `AddSubsemigroup`. -/]
/-
**MulHom.srange** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：srange (f : M ->ₙ* N) : Subsemigroup N
参数：f : M ->ₙ* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pa
ttern].
-/
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
/-
**MulHom.coe_srange** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_srange (f : M ->ₙ* N) : (f.srange : Set N) = Set.range f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/-
**MulHom.mem_srange** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：mem_srange {f : M ->ₙ* N} {y : N} : y in f.srange ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
/-
**MulHom.srange_mk_aux_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f :=
  (srange ⟨f, hf⟩).mul_mem hx hy
/-
**MulHom.srange_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Mul M] [inst_1 : Mul N] (f : M → N
) (hf : ∀ (x y : M), f (x * y) = f x * f y),   { toFun := f, map_mul' := hf }.sr
ange = { carrier := Set.range f, mul_mem' := ⋯ }
参数：f : M → N；hf : ∀ (x y : M), f (x * y) = f x * f y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem srange_mk (f : M → N) (hf) :
    srange ⟨f, hf⟩ = ⟨Set.range f, by exact srange_mk_aux_mul hf⟩ := rfl

@[to_additive]
/-
**MulHom.srange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：srange_eq_map (f : M ->ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.copy_eq`：copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S
-/
theorem srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _

@[to_additive]
/-
**MulHom.map_srange** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：map_srange (g : N ->ₙ* P) (f : M ->ₙ* N) : f.srange.map g = (g.comp f).sra
nge
参数：g : N ->ₙ* P；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulHom.srange_eq_map`：srange_eq_map (f : M ->ₙ* N) : f.srange = (⊤ : Sub
semigroup M).map f
· 使用定理 `Subsemigroup.map_map`：map_map (g : N ->ₙ* P) (f : M ->ₙ* N) : (S.map f).
map g = S.map (g.comp f)
-/
theorem map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]
/-
**MulHom.srange_eq_top_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：srange_eq_top_iff_surjective {N} [Mul N] {f : M ->ₙ* N} : f.srange = (⊤ : 
Subsemigroup N) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulHom.coe_srange`：coe_srange (f : M ->ₙ* N) : (f.srange : Set N) = Set.
range f
· 使用定理 `Subsemigroup.coe_top`：coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.uni
v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem srange_eq_top_iff_surjective {N} [Mul N] {f : M →ₙ* N} :
    f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddSemigroup` hom is the whole of the codomain. -/]
/-
**MulHom.srange_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：srange_eq_top_of_surjective {N} [Mul N] (f : M ->ₙ* N) (hf : Function.Surj
ective f) : f.srange = (⊤ : Subsemigroup N)
参数：f : M ->ₙ* N；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulHom.srange_eq_top_iff_surjective`：srange_eq_top_iff_surjective {N} [M
ul N] {f : M ->ₙ* N} : f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f
-/
theorem srange_eq_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_eq_top_iff_surjective.2 hf

@[to_additive]
/-
**MulHom.mclosure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：mclosure_preimage_le (f : M ->ₙ* N) (s : Set N) : closure (f ⁻¹' s) <= (cl
osure s).comap f
参数：f : M ->ₙ* N；s : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subsemigroup.mem_comap`：mem_comap {S : Subsemigroup N} {f : M ->ₙ* N} {x
 : M} : x in S.comap f ↔ f x in S
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mclosure_preimage_le (f : M →ₙ* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      /-- The image under an `AddSemigroup` hom of the `AddSubsemigroup` generated by a set
      equals the `AddSubsemigroup` generated by the image of the set. -/]
/-
**MulHom.map_mclosure** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：map_mclosure (f : M ->ₙ* N) (s : Set M) : (closure s).map f = closure (f '
' s)
参数：f : M ->ₙ* N；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Subsemigroup.gc_map_comap`：gc_map_comap (f : M ->ₙ* N) : GaloisConnectio
n (map f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemigroup.gi N).gc (Subsemigroup.gi M).gc
    fun _ ↦ rfl

/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive /-- Restriction of an AddSemigroup hom to an `AddSubsemigroup` of the domain. -/]
/-
**MulHom.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：domRestrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M ->ₙ
* N) (S : σ) : S ->ₙ* N
参数：f : M ->ₙ* N；S : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a semigroup hom to a subsemigroup of the domain.
-/
def domRestrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N)
    (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)

@[to_additive (attr := simp)]
/-
**MulHom.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：domRestrict_apply {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f :
 M ->ₙ* N) {S : σ} (x : S) : f.domRestrict S x = f x
参数：f : M ->ₙ* N；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M]
    (f : M →ₙ* N) {S : σ} (x : S) : f.domRestrict S x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias _root_.AddHom.restrict := _root_.AddHom.domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddHom.restrict_apply := _root_.AddHom.domRestrict_apply

/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive (attr := simps)
  /-- Restriction of an `AddSemigroup` hom to an `AddSubsemigroup` of the codomain. -/]
/-
**MulHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：codRestrict [SetLike σ N] [MulMemClass σ N] (f : M ->ₙ* N) (S : σ) (h : fo
rall x, f x in S) : M ->ₙ* S where toFun n
参数：f : M ->ₙ* N；S : σ；h : forall x, f x in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) :
    M →ₙ* S where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)

/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive
/-- Restriction of an `AddSemigroup` hom to its range interpreted as a subsemigroup. -/]
/-
**MulHom.srangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：srangeRestrict {N} [Mul N] (f : M ->ₙ* N) : M ->ₙ* f.srange
参数：f : M ->ₙ* N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/-
**MulHom.coe_srangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_srangeRestrict {N} [Mul N] (f : M ->ₙ* N) (x : M) : (f.srangeRestrict 
x : N) = f x
参数：f : M ->ₙ* N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
theorem coe_srangeRestrict {N} [Mul N] (f : M →ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl

@[to_additive]
/-
**MulHom.srangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：srangeRestrict_surjective (f : M ->ₙ* N) : Function.Surjective f.srangeRes
trict
参数：f : M ->ₙ* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
theorem srangeRestrict_surjective (f : M →ₙ* N) : Function.Surjective f.srangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive prod_map_comap_prod']
/-
**MulHom.prod_map_comap_prod'** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：prod_map_comap_prod' {M' : Type*} {N' : Type*} [Mul M'] [Mul N'] (f : M ->
ₙ* N) (g : M' ->ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') : (S.prod S')
.comap (prodMap f g) = (S.comap f).prod (S'.comap g)
参数：f : M ->ₙ* N；g : M' ->ₙ* N'；S : Subsemigroup N；S' : Subsemigroup N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_prod_map_prod`：preimage_prod_map_prod (f : α -> β) (g : γ -
> δ) (s : Set β) (t : Set δ) : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t)
-/
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [Mul M'] [Mul N'] (f : M →ₙ* N)
    (g : M' →ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

/-- The `MulHom` from the preimage of a subsemigroup to itself. -/
@[to_additive (attr := simps)
  /-- The `AddHom` from the preimage of an additive subsemigroup to itself. -/]
/-
**MulHom.subsemigroupComap** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：subsemigroupComap (f : M ->ₙ* N) (N' : Subsemigroup N) : N'.comap f ->ₙ* N
' where toFun x
参数：f : M ->ₙ* N；N' : Subsemigroup N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) :
    N'.comap f →ₙ* N' where
  toFun x := ⟨f x, x.prop⟩
  map_mul' x y := Subtype.ext <| map_mul (M := M) (N := N) f x y

/-- The `MulHom` from a subsemigroup to its image.
See `MulEquiv.subsemigroupMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
      /-- the `AddHom` from an additive subsemigroup to its image. See
      `AddEquiv.addSubsemigroupMap` for a variant for `AddEquiv`s. -/]
/-
**MulHom.subsemigroupMap** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：subsemigroupMap (f : M ->ₙ* N) (M' : Subsemigroup M) : M' ->ₙ* M'.map f wh
ere toFun x
参数：f : M ->ₙ* N；M' : Subsemigroup M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) :
    M' →ₙ* M'.map f where
  toFun x := ⟨f x, ⟨x, x.prop, rfl⟩⟩
  map_mul' x y := Subtype.ext <| map_mul (M := M) (N := N) f x y

@[to_additive]
/-
**MulHom.subsemigroupMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：subsemigroupMap_surjective (f : M ->ₙ* N) (M' : Subsemigroup M) : Function
.Surjective (f.subsemigroupMap M')
参数：f : M ->ₙ* N；M' : Subsemigroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
theorem subsemigroupMap_surjective (f : M →ₙ* N) (M' : Subsemigroup M) :
    Function.Surjective (f.subsemigroupMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

@[to_additive (attr := simp)]
/-
**Subsemigroup.srange_fst** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：srange_fst [Nonempty N] : (fst M N).srange = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.srange_eq_top_of_surjective`：srange_eq_top_of_surjective {N} [Mul
 N] (f : M ->ₙ* N) (hf : Function.Surjective f) : f.srange = (⊤ : Subsemigroup N
)
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
  (fst M N).srange_eq_top_of_surjective <| Prod.fst_surjective

@[to_additive (attr := simp)]
/-
**Subsemigroup.srange_snd** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：srange_snd [Nonempty M] : (snd M N).srange = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.srange_eq_top_of_surjective`：srange_eq_top_of_surjective {N} [Mul
 N] (f : M ->ₙ* N) (hf : Function.Surjective f) : f.srange = (⊤ : Subsemigroup N
)
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
  (snd M N).srange_eq_top_of_surjective <| Prod.snd_surjective

@[to_additive prod_eq_top_iff]
/-
**Subsemigroup.prod_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsem
igroup N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsemigroup.srange_fst`：srange_fst [Nonempty N] : (fst M N).srange = ⊤
· 使用定理 `Subsemigroup.srange_snd`：srange_snd [Nonempty M] : (snd M N).srange = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← srange_eq_map, srange_fst, srange_snd]

/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive /-- The `AddSemigroup` hom associated to an inclusion of subsemigroups. -/]
/-
**Subsemigroup.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：inclusion {S T : Subsemigroup M} (h : S <= T) : S ->ₙ* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M

--- 原说明 ---
The semigroup hom associated to an inclusion of subsemigroups.
-/
def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]
/-
**Subsemigroup.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s
参数：s : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulHom.coe_srange`：coe_srange (f : M ->ₙ* N) : (f.srange : Set N) = Set.
range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans <| Subtype.range_coe

@[to_additive]
/-
**Subsemigroup.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：eq_top_iff' : S = ⊤ ↔ forall x : M, x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subsemigroup.mem_top`：mem_top (x : M) : x in (⊤ : Subsemigroup M)
-/
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
semigroup are equal. -/
@[to_additive
      /-- Makes the identity additive isomorphism from a proof two
      subsemigroups of an additive semigroup are equal. -/]
/-
**MulEquiv.subsemigroupCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：subsemigroupCongr (h : S = T) : S ≃* T
参数：h : S = T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `MulHom.srangeRestrict`. -/
@[to_additive (attr := simps +simpRhs)
      /-- An additive semigroup homomorphism `f : M →+ N` with a left-inverse
      `g : N → M` defines an additive equivalence between `M` and `f.srange`.
      This is a bidirectional version of `AddHom.srangeRestrict`. -/]
/-
**MulEquiv.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：ofLeftInverse (f : M ->ₙ* N) {g : N -> M} (h : Function.LeftInverse g f) :
 M ≃* f.srange
参数：f : M ->ₙ* N；h : Function.LeftInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

/-- A `MulEquiv` `φ` between two semigroups `M` and `N` induces a `MulEquiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `MulHom.subsemigroupMap` for a variant for `MulHom`s. -/
@[to_additive (attr := simps)
      /-- An `AddEquiv` `φ` between two additive semigroups `M` and `N` induces an `AddEquiv`
      between a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
      See `AddHom.addSubsemigroupMap` for a variant for `AddHom`s. -/]
/-
**MulEquiv.subsemigroupMap** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map (e : M ->ₙ*
 N)
参数：e : M ≃* N；S : Subsemigroup M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
-/
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map (e : M →ₙ* N) :=
  { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M →ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }

end MulEquiv

namespace Subsemigroup

variable [Mul M] [Mul N]

@[to_additive]
/-
**Subsemigroup.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_comap_eq (f : M ->ₙ* N) (S : Subsemigroup N) : (S.comap f).map f = S ⊓
 f.srange
参数：f : M ->ₙ* N；S : Subsemigroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : M →ₙ* N) (S : Subsemigroup N) : (S.comap f).map f = S ⊓ f.srange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]
/-
**Subsemigroup.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：map_comap_eq_self {f : M ->ₙ* N} {S : Subsemigroup N} (h : S <= f.srange) 
: (S.comap f).map f = S
参数：h : S <= f.srange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subsemigroup.map_comap_eq`：map_comap_eq (f : M ->ₙ* N) (S : Subsemigroup
 N) : (S.comap f).map f = S ⊓ f.srange
-/
theorem map_comap_eq_self {f : M →ₙ* N} {S : Subsemigroup N} (h : S ≤ f.srange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

end Subsemigroup

