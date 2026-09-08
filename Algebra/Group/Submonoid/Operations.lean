/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Operations on `Submonoid`s

In this file we define various operations on `Submonoid`s and `MonoidHom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Submonoid.toAddSubmonoid`, `Submonoid.toAddSubmonoid'`, `AddSubmonoid.toSubmonoid`,
  `AddSubmonoid.toSubmonoid'`: convert between multiplicative and additive submonoids of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) monoid structure on a submonoid

* `Submonoid.toMonoid`, `Submonoid.toCommMonoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `Submonoid.MulAction`, `Submonoid.DistribMulAction`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `Submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `Submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `Submonoid.prod`: product of two submonoids `s : Submonoid M` and `t : Submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `Submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `Submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `MulEquiv.submonoidCongr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `Submonoid.prodEquiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `MonoidHom`s

* `MonoidHom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `MonoidHom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `MonoidHom.domRestrict`: restrict a monoid homomorphism to a submonoid of its domain;
* `MonoidHom.restrict`: restrict the domain and codomain of a monoid homomorphism;
* `MonoidHom.codRestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `MonoidHom.mrangeRestrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `Additive M`. -/
@[simps]
/-
**Submonoid.toAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where 
toFun S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier

--- 原说明 ---
Submonoids of monoid `M` are isomorphic to additive submonoids of `Additive M`.
-/
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl

/-- Additive submonoids of an additive monoid `Additive M` are isomorphic to submonoids of `M`. -/
/-
**AddSubmonoid.toSubmonoid'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive submonoids of an additive monoid `Additive M` are isomorphic to submono
ids of `M`.
-/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm
/-
**Submonoid.toAddSubmonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.toAddSubmonoid_closure (S : Set M) : Submonoid.toAddSubmonoid (S
ubmonoid.closure S) = AddSubmonoid.closure (Additive.toMul ⁻¹' S)
参数：S : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem Submonoid.toAddSubmonoid_closure (S : Set M) :
    Submonoid.toAddSubmonoid (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <|
      Submonoid.closure_le.2 (AddSubmonoid.subset_closure (M := Additive M)))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := M))
/-
**AddSubmonoid.toSubmonoid'_closure** 是 Mathlib 中的一个定理，位于命名空间 `AddSubmonoid`。
形式化陈述：∀ {M : Type u_1} [inst : MulOneClass M] (S : Set (Additive M)),   AddSubmo
noid.toSubmonoid' (AddSubmonoid.closure S) = Submonoid.closure (⇑Additive.ofMul 
⁻¹' S)
参数：S : Set (Additive M)；AddSubmonoid.closure S；⇑Additive.ofMul ⁻¹' S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
-/
theorem AddSubmonoid.toSubmonoid'_closure (S : Set (Additive M)) :
    AddSubmonoid.toSubmonoid' (AddSubmonoid.closure S)
      = Submonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 (Submonoid.subset_closure (M := M)))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := Additive M))

end

section

variable {A : Type*} [AddZeroClass A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `Multiplicative A`. -/
@[simps]
/-
**AddSubmonoid.toSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) 
where toFun S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.zero_mem'`：∀ {M : Type u_3} [inst : AddZeroClass M] (self :
 AddSubmonoid M), 0 ∈ self.carrier

--- 原说明 ---
Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `Multiplicative A`.
-/
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl

/-- Submonoids of a monoid `Multiplicative A` are isomorphic to additive submonoids of `A`. -/
/-
**Submonoid.toAddSubmonoid'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Submonoids of a monoid `Multiplicative A` are isomorphic to additive submonoids 
of `A`.
-/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm
/-
**AddSubmonoid.toSubmonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.toSubmonoid_closure (S : Set A) : (AddSubmonoid.toSubmonoid) 
(AddSubmonoid.closure S) = Submonoid.closure (Multiplicative.toAdd ⁻¹' S)
参数：S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
-/
theorem AddSubmonoid.toSubmonoid_closure (S : Set A) :
    (AddSubmonoid.toSubmonoid) (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
      AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))
/-
**Submonoid.toAddSubmonoid'_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {A : Type u_4} [inst : AddZeroClass A] (S : Set (Multiplicative A)),   S
ubmonoid.toAddSubmonoid' (Submonoid.closure S) = AddSubmonoid.closure (⇑Multipli
cative.ofAdd ⁻¹' S)
参数：S : Set (Multiplicative A)；Submonoid.closure S；⇑Multiplicative.ofAdd ⁻¹' S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem Submonoid.toAddSubmonoid'_closure (S : Set (Multiplicative A)) :
    Submonoid.toAddSubmonoid' (Submonoid.closure S)
      = AddSubmonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
      Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))

end

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Set

/-!
### `comap` and `map`
-/

/-- The preimage of a `Submonoid` along a `MonoidHom` is a `Submonoid`. -/
@[to_additive
  /-- The preimage of an `AddSubmonoid` along an `AddMonoidHom` is an `AddSubmonoid`. -/]
/-
**Submonoid.comap** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：comap (f : F) (S : Submonoid N) : Submonoid M where carrier
参数：f : F；S : Submonoid N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap (f : F) (S : Submonoid N) :
    Submonoid M where
  carrier := f ⁻¹' S
  one_mem' := show f 1 ∈ S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact S.mul_mem ha hb

@[to_additive (attr := simp)]
/-
**Submonoid.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S
参数：S : Submonoid N；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_comap {S : Submonoid N} {f : F} {x : M} : x in S.comap f ↔ f x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[to_additive]
/-
**Submonoid.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_comap (S : Submonoid P) (g : N ->* P) (f : M ->* N) : (S.comap g).co
map f = S.comap (g.comp f)
参数：S : Submonoid P；g : N ->* P；f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S
参数：S : Submonoid P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext (by simp)

/-- The image of a `Submonoid` along a `MonoidHom` is a `Submonoid`. -/
@[to_additive
  /-- The image of an `AddSubmonoid` along an `AddMonoidHom` is an `AddSubmonoid`. -/]
/-
**Submonoid.map** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：map (f : F) (S : Submonoid M) : Submonoid N where carrier
参数：f : F；S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : F) (S : Submonoid M) :
    Submonoid N where
  carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
/-
**Submonoid.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S
参数：f : F；S : Submonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.map_coe_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_coe_toMonoidHom (f : F) (S : Submonoid M) : S.map (f : M ->* N) = S.ma
p f
参数：f : F；S : Submonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe_toMonoidHom (f : F) (S : Submonoid M) : S.map (f : M →* N) = S.map f :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.map_coe_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_coe_toMulEquiv {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) (S 
: Submonoid M) : S.map (f : M ≃* N) = S.map f
参数：f : F；S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem map_coe_toMulEquiv {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) (S : Submonoid M) :
    S.map (f : M ≃* N) = S.map f :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_map {f : F} {S : Submonoid M} {y : N} : y in S.map f ↔ exists x in S, 
f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := Iff.rfl

@[to_additive]
/-
**Submonoid.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x in S) : f x in S.
map f
参数：f : F；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[to_additive]
/-
**Submonoid.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x in S.map f
参数：f : F；S : Submonoid M；x : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_map_of_mem`：mem_map_of_mem (f : F) {S : Submonoid M} {x : 
M} (hx : x in S) : f x in S.map f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.2

@[to_additive]
/-
**Submonoid.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_map (g : N ->* P) (f : M ->* N) : (S.map f).map g = S.map (g.comp f)
参数：g : N ->* P；f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

@[to_additive (attr := simp 1100)]
/-
**Submonoid.mem_map_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x :
 M} : f x in S.map f ↔ x in S
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[to_additive]
/-
**Submonoid.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} : S.map f 
<= T ↔ S <= T.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[to_additive]
/-
**Submonoid.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：gc_map_comap (f : F) : GaloisConnection (map f) (comap f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {S : Submonoi
d M} {T : Submonoid N} : S.map f <= T ↔ S <= T.comap f
-/
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

@[to_additive]
/-
**Submonoid.map_le_of_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_le_of_le_comap {T : Submonoid N} {f : F} : S <= T.comap f -> S.map f <
= T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[to_additive]
/-
**Submonoid.le_comap_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f <= T -> S <= T.coma
p f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ {a : α}
 {b : β}, l…
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
/-
**Submonoid.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_comap_map {f : F} : S <= (S.map f).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem le_comap_map {f : F} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/-
**Submonoid.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[to_additive (attr := gcongr)]
/-
**Submonoid.monotone_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：monotone_map {f : F} : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive (attr := gcongr)]
/-
**Submonoid.monotone_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：monotone_comap {f : F} : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]
/-
**Submonoid.map_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]
/-
**Submonoid.comap_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = 
S.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
/-
**Submonoid.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f
参数：S T : Submonoid M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[to_additive]
/-
**Submonoid.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_iSup {ι : Sort*} (f : F) (s : ι -> Submonoid M) : (iSup s).map f = ⨆ i
, (s i).map f
参数：f : F；s : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι → Submonoid M) : (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[to_additive]
/-
**Submonoid.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_inf (S T : Submonoid M) (f : F) (hf : Function.Injective f) : (S ⊓ T).
map f = S.map f ⊓ T.map f
参数：S T : Submonoid M；f : F；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (S T : Submonoid M) (f : F) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/-
**Submonoid.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f) (s :
 ι -> Submonoid M) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : F；hf : Function.Injective f；s : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Submonoid M} : (↑(⨅ i
, S i) : Set M) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι → Submonoid M) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/-
**Submonoid.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.co
map f
参数：S T : Submonoid N；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf

@[to_additive]
/-
**Submonoid.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_iInf {ι : Sort*} (f : F) (s : ι -> Submonoid N) : (iInf s).comap f =
 ⨅ i, (s i).comap f
参数：f : F；s : ι -> Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι → Submonoid N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

@[to_additive (attr := simp)]
/-
**Submonoid.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive]
/-
**Submonoid.disjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : 
Disjoint H K) : Disjoint (H.map f) (K.map f)
参数：hf : Function.Injective f；h : Disjoint H K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.map_inf`：map_inf (S T : Submonoid M) (f : F) (hf : Function.In
jective f) : (S ⊓ T).map f = S.map f ⊓ T.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.map_bot`：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
-/
lemma disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← map_inf _ _ f hf, disjoint_iff.mp h, map_bot]

@[to_additive (attr := simp)]
/-
**Submonoid.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
-/
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[to_additive (attr := simp)]
/-
**Submonoid.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
-/
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type*} {f : F}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/]
/-
**Submonoid.gciMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap
 f)
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.
-/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

@[to_additive]
/-
**Submonoid.comap_map_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
/-
**Submonoid.comap_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.comap_inf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap
 f = S ⊓ T
参数：S T : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
/-
**Submonoid.comap_iInf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_iInf_map_of_injective (S : ι -> Submonoid M) : (⨅ i, (S i).map f).co
map f = iInf S
参数：S : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iInf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iInf_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

@[to_additive]
/-
**Submonoid.comap_sup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap
 f = S ⊔ T
参数：S T : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
/-
**Submonoid.comap_iSup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_iSup_map_of_injective (S : ι -> Submonoid M) : (⨆ i, (S i).map f).co
map f = iSup S
参数：S : ι -> Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iSup_map_of_injective (S : ι → Submonoid M) : (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

@[to_additive]
/-
**Submonoid.map_le_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_le_map_iff_of_injective {S T : Submonoid M} : S.map f <= T.map f ↔ S <
= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
/-
**Submonoid.map_strictMono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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

variable {ι : Type*} {f : F}

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/]
/-
**Submonoid.giMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：giMapComap (hf : Function.Surjective f) : GaloisInsertion (map f) (comap f
)
参数：hf : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
-/
def giMapComap (hf : Function.Surjective f) : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

variable (hf : Function.Surjective f)
include hf

@[to_additive]
/-
**Submonoid.map_comap_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S
参数：S : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
/-
**Submonoid.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.comap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.map_inf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).
map f = S ⊓ T
参数：S T : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
/-
**Submonoid.map_iInf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_iInf_comap_of_surjective (S : ι -> Submonoid N) : (⨅ i, (S i).comap f)
.map f = iInf S
参数：S : ι -> Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem map_iInf_comap_of_surjective (S : ι → Submonoid N) : (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

@[to_additive]
/-
**Submonoid.map_sup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).
map f = S ⊔ T
参数：S T : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
/-
**Submonoid.map_iSup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_iSup_comap_of_surjective (S : ι -> Submonoid N) : (⨆ i, (S i).comap f)
.map f = iSup S
参数：S : ι -> Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem map_iSup_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

@[to_additive]
/-
**Submonoid.comap_le_comap_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoi
d`。
形式化陈述：comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f <= T.coma
p f ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
-/
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
/-
**Submonoid.comap_strictMono_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`
。
形式化陈述：comap_strictMono_of_surjective : StrictMono (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.strictMono_u`：strictMono_u [Preorder α] [Preorder β] (gi
 : GaloisInsertion l u) : StrictMono u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

/-- The top `Submonoid` is isomorphic to the `Monoid`. -/
@[to_additive (attr := simps)
/-- The top `AddSubmonoid` is isomorphic to the `AddMonoid`. -/]
/-
**Submonoid.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：topEquiv : (⊤ : Submonoid M) ≃* M where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
-/
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**Submonoid.topEquiv_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：topEquiv_toMonoidHom : ((topEquiv : _ ≃* M) : _ ->* M) = (⊤ : Submonoid M)
.subtype
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem topEquiv_toMonoidHom : ((topEquiv : _ ≃* M) : _ →* M) = (⊤ : Submonoid M).subtype :=
  rfl

/-- A `Subgroup` is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.submonoidMap` for better definitional equalities. -/
@[to_additive /-- An `AddSubgroup` is isomorphic to its image under an injective function. If
you have an isomorphism, use `AddEquiv.addSubmonoidMap` for better definitional equalities. -/]
/-
**Submonoid.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：equivMapOfInjective (f : M ->* N) (hf : Function.Injective f) : S ≃* S.map
 f
参数：f : M ->* N；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]
/-
**Submonoid.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_equivMapOfInjective_apply (f : M ->* N) (hf : Function.Injective f) (x
 : S) : (equivMapOfInjective S f hf x : N) = f x
参数：f : M ->* N；hf : Function.Injective f；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivMapOfInjective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.closure_closure_coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s -> M)
 ⁻¹' s) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
-/
theorem closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    closure_induction (fun _ h ↦ subset_closure h) (one_mem _) (fun _ _ _ _ ↦ mul_mem) hx'

/-- Given `Submonoid`s `s`, `t` of `Monoid`s `M`, `N` respectively, `s × t` as a `Submonoid` of
`M × N`. -/
@[to_additive prod
  /-- Given `AddSubmonoid`s `s`, `t` of `AddMonoid`s `A`, `B` respectively, `s × t` as an
  `AddSubmonoid` of `A × B`. -/]
/-
**Submonoid.prod** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N) where carrier
参数：s : Submonoid M；t : Submonoid N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N) where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
/-
**Submonoid.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_prod (s : Submonoid M) (t : Submonoid N) : (s.prod t : Set (M × N)) = 
(s : Set M) ×ˢ (t : Set N)
参数：s : Submonoid M；t : Submonoid N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : Submonoid M) (t : Submonoid N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
/-
**Submonoid.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} : p in s.prod t ↔
 p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[to_additive prod_mono]
/-
**Submonoid.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ <= s₂) (ht 
: t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
参数：hs : s₁ <= s₂；ht : t₁ <= t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
/-
**Submonoid.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom
.fst M N)
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]
/-
**Submonoid.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom
.snd M N)
参数：s : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
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
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/-
**Submonoid.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.top_prod`：top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod 
s = s.comap (MonoidHom.snd M N)
· 使用定理 `Submonoid.comap_top`：comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤
-/
theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive bot_prod_bot]
/-
**Submonoid.bot_prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥
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
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod]

/-- The product of `Submonoid`s is isomorphic to their product as `Monoid`s. -/
@[to_additive prodEquiv
  /-- The product of `AddSubmonoid`s is isomorphic to their product as `AddMonoid`s. -/]
/-
**Submonoid.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t
参数：s : Submonoid M；t : Submonoid N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

open MonoidHom

@[to_additive]
/-
**Submonoid.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.ext rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
/-
**Submonoid.map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s
参数：s : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive (attr := simp) prod_bot_sup_bot_prod]
/-
**Submonoid.prod_bot_sup_bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) : (prod s ⊥) ⊔ (
prod ⊥ t) = prod s t
参数：s : Submonoid M；t : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Submonoid.prod_mono`：prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid 
N} (hs : s₁ <= s₂) (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Prod.fst_mul_snd`：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N
) : (p.fst, 1) * (1, p.snd) = p
-/
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (prod s ⊥) ⊔ (prod ⊥ t) = prod s t :=
  (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : prod s ⊥ ≤ prod s ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t ≤ prod s ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

@[to_additive]
/-
**Submonoid.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} : x in K.map f.toMono
idHom ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  Set.mem_image_equiv

@[to_additive]
/-
**Submonoid.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) : K.map f = K.comap
 f.symm
参数：f : M ≃* N；K : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/-
**Submonoid.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) : K.comap f = K.map
 f.symm
参数：f : N ≃* M；K : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Submonoid.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : M ≃* N) 
(K : Submonoid M) : K.map f = K.comap f.symm
-/
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]
/-
**Submonoid.map_equiv_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
/-
**Submonoid.le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} : 
u <= s.prod t ↔ u.map (fst M N) <= s ∧ u.map (snd M N) <= t
参数：M × N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
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

@[to_additive prod_le_iff]
/-
**Submonoid.prod_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} : 
s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) <= u
参数：M × N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.prod t ≤ u ↔ s.map (inl M N) ≤ u ∧ t.map (inr M N) ≤ u := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 ∈ u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 ∈ u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'

@[to_additive closure_prod]
/-
**Submonoid.closure_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_prod {s : Set M} {t : Set N} (hs : 1 in s) (ht : 1 in t) : closure
 (s ×ˢ t) = (closure s).prod (closure t)
参数：hs : 1 in s；ht : 1 in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.prod_le_iff`：prod_le_iff {s : Submonoid M} {t : Submonoid N} {
u : Submonoid (M × N)} : s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) 
<= u
· 使用定理 `Submonoid.map_le_of_le_comap`：map_le_of_le_comap {T : Submonoid N} {f : 
F} : S <= T.comap f -> S.map f <= T
-/
theorem closure_prod {s : Set M} {t : Set N} (hs : 1 ∈ s) (ht : 1 ∈ t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
      map_le_of_le_comap _ <| closure_le.2 fun _x hx => subset_closure ⟨hx, ht⟩,
      map_le_of_le_comap _ <| closure_le.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

@[to_additive (attr := simp) closure_prod_zero]
/-
**Submonoid.closure_prod_one** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_prod_one (s : Set M) : closure (s ×ˢ ({1} : Set N)) = (closure s).
prod ⊥
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Submonoid.prod_le_iff`：prod_le_iff {s : Submonoid M} {t : Submonoid N} {
u : Submonoid (M × N)} : s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) 
<= u
· 使用定理 `Submonoid.map_le_of_le_comap`：map_le_of_le_comap {T : Submonoid N} {f : 
F} : S <= T.comap f -> S.map f <= T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_bot`：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
-/
lemma closure_prod_one (s : Set M) : closure (s ×ˢ ({1} : Set N)) = (closure s).prod ⊥ :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (prod_le_iff.2 ⟨
      map_le_of_le_comap _ <| closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩, by simp⟩)

@[to_additive (attr := simp) closure_zero_prod]
/-
**Submonoid.closure_one_prod** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：closure_one_prod (t : Set N) : closure (({1} : Set M) ×ˢ t) = .prod ⊥ (clo
sure t)
参数：t : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.prod_le_iff`：prod_le_iff {s : Submonoid M} {t : Submonoid N} {
u : Submonoid (M × N)} : s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) 
<= u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_bot`：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
· 使用定理 `Submonoid.map_le_of_le_comap`：map_le_of_le_comap {T : Submonoid N} {f : 
F} : S <= T.comap f -> S.map f <= T
-/
lemma closure_one_prod (t : Set N) : closure (({1} : Set M) ×ˢ t) = .prod ⊥ (closure t) :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (prod_le_iff.2 ⟨by simp,
      map_le_of_le_comap _ <| closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

end Submonoid

namespace MonoidHom

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Submonoid

library_note «range copy pattern» /--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`Set.range f`. In particular this means that the types `↥(Set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`Set.range` could have been defined as `f '' Set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `Set.range`, and that it introduces a redundant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`MonoidHom.mrange` would be `(⊤ : Submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `Submonoid.copy` as follows:
```lean
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M :=
  { carrier  := s,
    one_mem' := hs.symm ▸ S.one_mem',
    mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

/-- The range of a `MonoidHom` is a `Submonoid`. See Note [range copy pattern]. -/
@[to_additive /-- The range of an `AddMonoidHom` is an `AddSubmonoid`. -/]
/-
**MonoidHom.mrange** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：mrange (f : M →* N) : Submonoid N
参数：f : M →* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a `MonoidHom` is a `Submonoid`. See Note [range copy pattern].
-/
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_mrange** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_mrange (f : F) : (mrange f : Set N) = Set.range f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_mrange** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mem_mrange {f : F} {y : N} : y in mrange f ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mrange {f : F} {y : N} : y ∈ mrange f ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
/-
**MonoidHom.mrange_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_comp {O : Type*} [MulOneClass O] (f : N ->* O) (g : M ->* N) : mran
ge (f.comp g) = (mrange g).map f
参数：f : N ->* O；g : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma mrange_comp {O : Type*} [MulOneClass O] (f : N →* O) (g : M →* N) :
    mrange (f.comp g) = (mrange g).map f := SetLike.coe_injective <| Set.range_comp f _

@[to_additive]
/-
**MonoidHom.mrange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.copy_eq`：copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S
-/
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  Submonoid.copy_eq _

@[to_additive (attr := simp)]
/-
**MonoidHom.mrange_id** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_id : mrange (MonoidHom.id M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.map_id`：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mrange_id : mrange (MonoidHom.id M) = ⊤ := by
  simp [mrange_eq_map]

@[to_additive]
/-
**MonoidHom.map_mrange** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_mrange (g : N ->* P) (f : M ->* N) : (mrange f).map g = mrange (comp g
 f)
参数：g : N ->* P；f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.map_map`：map_map (g : N ->* P) (f : M ->* N) : (S.map f).map g
 = S.map (g.comp f)
-/
theorem map_mrange (g : N →* P) (f : M →* N) : (mrange f).map g = mrange (comp g f) := by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f

@[to_additive]
/-
**MonoidHom.mrange_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_eq_top {f : F} : mrange f = (⊤ : Submonoid N) ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.coe_mrange`：coe_mrange (f : F) : (mrange f : Set N) = Set.rang
e f
· 使用定理 `Submonoid.coe_top`：coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem mrange_eq_top {f : F} : mrange f = (⊤ : Submonoid N) ↔ Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_mrange, coe_top]) Set.range_eq_univ

@[to_additive (attr := simp) mrange_prodMap]
/-
**MonoidHom.mrange_prodMap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_prodMap {M' N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->
* N) (g : M' ->* N') : MonoidHom.mrange (f.prodMap g) = (MonoidHom.mrange f).pro
d (MonoidHom.mrange g)
参数：f : M ->* N；g : M' ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
-/
lemma mrange_prodMap {M' N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') :
    MonoidHom.mrange (f.prodMap g) = (MonoidHom.mrange f).prod (MonoidHom.mrange g) :=
  SetLike.coe_injective Set.range_prodMap

/-- The range of a surjective `MonoidHom` is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddMonoidHom` is the whole of the codomain. -/]
/-
**MonoidHom.mrange_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrange_eq_top_of_surjective (f : F) (hf : Function.Surjective f) : mrange 
f = (⊤ : Submonoid N)
参数：f : F；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.mrange_eq_top`：mrange_eq_top {f : F} : mrange f = (⊤ : Submono
id N) ↔ Surjective f
-/
theorem mrange_eq_top_of_surjective (f : F) (hf : Function.Surjective f) :
    mrange f = (⊤ : Submonoid N) :=
  mrange_eq_top.2 hf

@[to_additive]
/-
**MonoidHom.mclosure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) <= (closure s
).comap f
参数：f : F；s : Set N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submonoid.mem_comap`：mem_comap {S : Submonoid N} {f : F} {x : M} : x in 
S.comap f ↔ f x in S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a `MonoidHom` of the `Submonoid` generated by a set equals the `Submonoid`
generated by the image of the set. -/
@[to_additive
  /-- The image under an `AddMonoidHom` of the `AddSubmonoid` generated by a set equals the
  `AddSubmonoid` generated by the image of the set. -/]
/-
**MonoidHom.map_mclosure** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s)
参数：f : F；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Submonoid.gi N).gc (Submonoid.gi M).gc
    fun _ ↦ rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.mclosure_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mclosure_range (f : F) : closure (Set.range f) = mrange f
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.closure_univ`：closure_univ : closure (univ : Set M) = ⊤
-/
theorem mclosure_range (f : F) : closure (Set.range f) = mrange f := by
  rw [← Set.image_univ, ← map_mclosure, mrange_eq_map, closure_univ]

/-- Restriction of a `MonoidHom` to a `Submonoid` of the domain. -/
@[to_additive /-- Restriction of an `AddMonoidHom` to an `AddSubmonoid` of the domain. -/]
/-
**MonoidHom.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S 
M] (f : M ->* N) (s : S) : s ->* N
参数：f : M ->* N；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a `MonoidHom` to a `Submonoid` of the domain.
-/
def domRestrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
    (s : S) : s →* N :=
  f.comp (SubmonoidClass.subtype _)

@[to_additive (attr := simp)]
/-
**MonoidHom.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict_apply {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidCl
ass S M] (f : M ->* N) (s : S) (x : s) : f.domRestrict s x = f x
参数：f : M ->* N；s : S；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M →* N) (s : S) (x : s) : f.domRestrict s x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_apply := _root_.AddMonoidHom.domRestrict_apply

@[to_additive (attr := simp)]
/-
**MonoidHom.domRestrict_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict_eq_one_iff {N S : Type*} [MulOneClass N] {f : M ->* N} [SetLik
e S M] [SubmonoidClass S M] {s : S} : f.domRestrict s = 1 ↔ forall x in s, f x =
 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem domRestrict_eq_one_iff {N S : Type*} [MulOneClass N] {f : M →* N} [SetLike S M]
    [SubmonoidClass S M] {s : S} :
    f.domRestrict s = 1 ↔ ∀ x ∈ s, f x = 1 := by
  simp [MonoidHom.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_eq_zero_iff := _root_.AddMonoidHom.domRestrict_eq_zero_iff

@[to_additive (attr := simp)]
/-
**MonoidHom.domRestrict_mrange** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict_mrange (f : M ->* N) : mrange (f.domRestrict S) = S.map f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem domRestrict_mrange (f : M →* N) : mrange (f.domRestrict S) = S.map f := by
  simp [SetLike.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_mrange := domRestrict_mrange
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mrange := _root_.AddMonoidHom.domRestrict_mrange

/-- A version of `MonoidHom.domRestrict` as a homomorphism. -/
@[to_additive (attr := simps apply)
  /-- A version of `AddMonoidHom.domRestrict` as a homomorphism. -/]
/-
**MonoidHom.domRestrictHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：domRestrictHom {S : Type*} [SetLike S M] [SubmonoidClass S M] (M' : S) (A 
: Type*) [CommMonoid A] : (M ->* A) ->* (M' ->* A) where toFun f
参数：M' : S；A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def domRestrictHom {S : Type*} [SetLike S M] [SubmonoidClass S M] (M' : S) (A : Type*)
    [CommMonoid A] : (M →* A) →* (M' →* A) where
  toFun f := f.domRestrict M'
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom := _root_.AddMonoidHom.domRestrictHom
@[deprecated (since := "2026-07-19")] alias restrictHom_apply := domRestrictHom_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom_apply := _root_.AddMonoidHom.domRestrictHom_apply

/-- Restriction of a `MonoidHom` to a `Submonoid` of the codomain. -/
@[to_additive (attr := simps apply)
  /-- Restriction of an `AddMonoidHom` to an `AddSubmonoid` of the codomain. -/]
/-
**MonoidHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N) (s : S) (
h : forall x, f x in s) : M ->* s where toFun n
参数：f : M ->* N；s : S；h : forall x, f x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive (attr := simp)]
/-
**MonoidHom.injective_codRestrict** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N)
 (s : S) (h : forall x, f x in s) : Function.Injective (f.codRestrict s h) ↔ Fun
ction.Injective f
参数：f : M ->* N；s : S；h : forall x, f x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S)
    (h : ∀ x, f x ∈ s) : Function.Injective (f.codRestrict s h) ↔ Function.Injective f :=
  ⟨fun H _ _ hxy ↦ H <| Subtype.ext hxy, fun H _ _ hxy ↦ H (congr_arg Subtype.val hxy)⟩

/-- Restriction of a `MonoidHom` to its range interpreted as a `Submonoid`. -/
@[to_additive
  /-- Restriction of an `AddMonoidHom` to its range interpreted as an `AddSubmonoid`. -/]
/-
**MonoidHom.mrangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：mrangeRestrict {N} [MulOneClass N] (f : M ->* N) : M ->* (mrange f)
参数：f : M ->* N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
def mrangeRestrict {N} [MulOneClass N] (f : M →* N) : M →* (mrange f) :=
  (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_mrangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_mrangeRestrict {N} [MulOneClass N] (f : M ->* N) (x : M) : (f.mrangeRe
strict x : N) = f x
参数：f : M ->* N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mrangeRestrict {N} [MulOneClass N] (f : M →* N) (x : M) :
    (f.mrangeRestrict x : N) = f x :=
  rfl

@[to_additive]
/-
**MonoidHom.mrangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrangeRestrict_surjective (f : M ->* N) : Function.Surjective f.mrangeRest
rict
参数：f : M ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mrangeRestrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

/-- The multiplicative kernel of a `MonoidHom` is the `Submonoid` of elements `x : G` such that
`f x = 1`. -/
@[to_additive
  /-- The additive kernel of an `AddMonoidHom` is the `AddSubmonoid` of elements such that
  `f x = 0`. -/]
/-
**MonoidHom.mker** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：mker (f : F) : Submonoid M
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_mker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mem_mker {f : F} {x : M} : x in mker f ↔ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mker {f : F} {x : M} : x ∈ mker f ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
/-
**MonoidHom.coe_mker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_mker (f : F) : (mker f : Set M) = (f : M -> N) ⁻¹' {1}
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mker (f : F) : (mker f : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl

@[to_additive]
/-
**MonoidHom.decidableMemMker** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· in mker f)
参数：f : F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.mem_mker`：mem_mker {f : F} {x : M} : x in mker f ↔ f x = 1
-/
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· ∈ mker f) := fun x =>
  decidable_of_iff (f x = 1) mem_mker

@[to_additive]
/-
**MonoidHom.comap_mker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comap_mker (g : N ->* P) (f : M ->* N) : (mker g).comap f = mker (comp g f
)
参数：g : N ->* P；f : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mker (g : N →* P) (f : M →* N) : (mker g).comap f = mker (comp g f) :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comap_bot'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.domRestrict_mker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict_mker (f : M ->* N) : mker (f.domRestrict S) = (MonoidHom.mker 
f).comap S.subtype
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem domRestrict_mker (f : M →* N) :
    mker (f.domRestrict S) = (MonoidHom.mker f).comap S.subtype :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_mker := domRestrict_mker
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mker := _root_.AddMonoidHom.domRestrict_mker

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MonoidHom.mrangeRestrict_mker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mrangeRestrict_mker (f : M ->* N) : mker (mrangeRestrict f) = mker f
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mrangeRestrict_mker (f : M →* N) : mker (mrangeRestrict f) = mker f := by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

@[to_additive (attr := simp)]
/-
**MonoidHom.mker_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mker_one : mker (1 : M ->* N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mker_one : mker (1 : M →* N) = ⊤ := by
  ext
  simp [mem_mker]

@[to_additive prod_map_comap_prod']
/-
**MonoidHom.prod_map_comap_prod'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prod_map_comap_prod' {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneCla
ss N'] (f : M ->* N) (g : M' ->* N') (S : Submonoid N) (S' : Submonoid N') : (S.
prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g)
参数：f : M ->* N；g : M' ->* N'；S : Submonoid N；S' : Submonoid N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_prod_map_prod`：preimage_prod_map_prod (f : α -> β) (g : γ -
> δ) (s : Set β) (t : Set δ) : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t)
-/
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N']
    (f : M →* N) (g : M' →* N') (S : Submonoid N) (S' : Submonoid N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

@[to_additive mker_prod_map]
/-
**MonoidHom.mker_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mker_prod_map {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] 
(f : M ->* N) (g : M' ->* N') : mker (prodMap f g) = (mker f).prod (mker g)
参数：f : M ->* N；g : M' ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_bot'`：comap_bot' (f : F) : (⊥ : Submonoid N).comap f = m
ker f
· 使用定理 `MonoidHom.prod_map_comap_prod'`：prod_map_comap_prod' {M' : Type*} {N' : 
Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->* N) (g : M' ->* N') (S : Subm
onoid N) (S' : Submo…
· 使用定理 `Submonoid.bot_prod_bot`：bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submo
noid N) = ⊥
-/
theorem mker_prod_map {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') : mker (prodMap f g) = (mker f).prod (mker g) := by
  rw [← comap_bot', ← comap_bot', ← comap_bot', ← prod_map_comap_prod', bot_prod_bot]

@[to_additive (attr := simp)]
/-
**MonoidHom.mker_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mker_inl : mker (inl M N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mker_inl : mker (inl M N) = ⊥ := by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]
/-
**MonoidHom.mker_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mker_inr : mker (inr M N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mker_inr : mker (inr M N) = ⊥ := by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]
/-
**MonoidHom.mker_fst** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mker_fst : mker (fst M N) = .prod ⊥ ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mker_fst : mker (fst M N) = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]
/-
**MonoidHom.mker_snd** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mker_snd : mker (snd M N) = .prod ⊤ ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma mker_snd : mker (snd M N) = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

/-- The `MonoidHom` from the preimage of a `Submonoid` to itself. -/
@[to_additive (attr := simps)
  /-- The `AddMonoidHom` from the preimage of an `AddSubmonoid` to itself. -/]
/-
**MonoidHom.submonoidComap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：submonoidComap (f : M ->* N) (N' : Submonoid N) : N'.comap f ->* N' where 
toFun x
参数：f : M ->* N；N' : Submonoid N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submonoidComap (f : M →* N) (N' : Submonoid N) :
    N'.comap f →* N' where
  toFun x := ⟨f x, x.2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive]
/-
**MonoidHom.submonoidComap_surjective_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `M
onoidHom`。
形式化陈述：submonoidComap_surjective_of_surjective (f : M ->* N) (N' : Submonoid N) (
hf : Surjective f) : Surjective (f.submonoidComap N')
参数：f : M ->* N；N' : Submonoid N；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.mem_comap`：mem_comap {S : Submonoid N} {f : F} {x : M} : x in 
S.comap f ↔ f x in S
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.submonoidComap_apply_coe`：∀ {M : Type u_1} {N : Type u_2} [ins
t : MulOneClass M] [inst_1 : MulOneClass N] (f : M →* N) (N' : Submonoid N)   (x
 : ↥(Submonoid.comap f N…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma submonoidComap_surjective_of_surjective (f : M →* N) (N' : Submonoid N) (hf : Surjective f) :
    Surjective (f.submonoidComap N') := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

/-- The `MonoidHom` from a `Submonoid` to its image.
See `MulEquiv.SubmonoidMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
  /-- The `AddMonoidHom` from an `AddSubmonoid` to its image.
  See `AddEquiv.AddSubmonoidMap` for a variant for `AddEquiv`s. -/]
/-
**MonoidHom.submonoidMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：submonoidMap (f : M ->* N) (M' : Submonoid M) : M' ->* M'.map f where toFu
n x
参数：f : M ->* N；M' : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submonoidMap (f : M →* N) (M' : Submonoid M) : M' →* M'.map f where
  toFun x := ⟨f x, ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext <| f.map_one
  map_mul' x y := Subtype.ext <| f.map_mul x y

@[to_additive]
/-
**MonoidHom.submonoidMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：submonoidMap_surjective (f : M ->* N) (M' : Submonoid M) : Function.Surjec
tive (f.submonoidMap M')
参数：f : M ->* N；M' : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[to_additive (attr := grind inj)]
/-
**MonoidHom.submonoidMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：submonoidMap_injective {f : M ->* N} (hf : Injective f) (M' : Submonoid M)
 : Injective (f.submonoidMap M')
参数：hf : Injective f；M' : Submonoid M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submonoidMap_injective {f : M →* N} (hf : Injective f) (M' : Submonoid M) :
    Injective (f.submonoidMap M') := by
  grind [Injective, submonoidMap_apply_coe]

end MonoidHom

namespace Submonoid

@[to_additive]
/-
**Submonoid.surjOn_iff_le_map** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：surjOn_iff_le_map {f : M ->* N} {H : Submonoid M} {K : Submonoid N} : Set.
SurjOn f H K ↔ K <= H.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma surjOn_iff_le_map {f : M →* N} {H : Submonoid M} {K : Submonoid N} :
    Set.SurjOn f H K ↔ K ≤ H.map f :=
  Iff.rfl

open MonoidHom

@[to_additive]
/-
**Submonoid.mrange_inl** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_inl : mrange (inl M N) = prod ⊤ ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.map_inl`：map_inl (s : Submonoid M) : s.map (inl M N) = s.prod 
⊥
-/
theorem mrange_inl : mrange (inl M N) = prod ⊤ ⊥ := by simpa only [mrange_eq_map] using map_inl ⊤

@[to_additive]
/-
**Submonoid.mrange_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_inr : mrange (inr M N) = prod ⊥ ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Submonoid.map_inr`：map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ 
s
-/
theorem mrange_inr : mrange (inr M N) = prod ⊥ ⊤ := by simpa only [mrange_eq_map] using map_inr ⊤

@[to_additive]
/-
**Submonoid.mrange_inl'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_inl' : mrange (inl M N) = comap (snd M N) ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.mrange_inl`：mrange_inl : mrange (inl M N) = prod ⊤ ⊥
· 使用定理 `Submonoid.top_prod`：top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod 
s = s.comap (MonoidHom.snd M N)
-/
theorem mrange_inl' : mrange (inl M N) = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)

@[to_additive]
/-
**Submonoid.mrange_inr'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_inr' : mrange (inr M N) = comap (fst M N) ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.mrange_inr`：mrange_inr : mrange (inr M N) = prod ⊥ ⊤
· 使用定理 `Submonoid.prod_top`：prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N
) = s.comap (MonoidHom.fst M N)
-/
theorem mrange_inr' : mrange (inr M N) = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)

@[to_additive (attr := simp)]
/-
**Submonoid.mrange_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_fst : mrange (fst M N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
theorem mrange_fst : mrange (fst M N) = ⊤ :=
  mrange_eq_top_of_surjective (fst M N) <| @Prod.fst_surjective _ _ ⟨1⟩

@[to_additive (attr := simp)]
/-
**Submonoid.mrange_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_snd : mrange (snd M N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem mrange_snd : mrange (snd M N) = ⊤ :=
  mrange_eq_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩

@[to_additive prod_eq_bot_iff]
/-
**Submonoid.prod_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥
 ∧ t = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `Submonoid.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (map f) 
(comap f)
· 使用定理 `MonoidHom.mker_inl`：mker_inl : mker (inl M N) = ⊥
· 使用定理 `MonoidHom.mker_inr`：mker_inr : mker (inr M N) = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]

@[to_additive prod_eq_top_iff]
/-
**Submonoid.prod_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤
 ∧ t = ⊤
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
· 使用定理 `Submonoid.mrange_fst`：mrange_fst : mrange (fst M N) = ⊤
· 使用定理 `Submonoid.mrange_snd`：mrange_snd : mrange (snd M N) = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← mrange_eq_map, mrange_fst, mrange_snd]

@[to_additive (attr := simp)]
/-
**Submonoid.mrange_inl_sup_mrange_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_inl_sup_mrange_inr : mrange (inl M N) ⊔ mrange (inr M N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submonoid.mrange_inl`：mrange_inl : mrange (inl M N) = prod ⊤ ⊥
· 使用定理 `Submonoid.mrange_inr`：mrange_inr : mrange (inr M N) = prod ⊥ ⊤
· 使用定理 `Submonoid.prod_bot_sup_bot_prod`：prod_bot_sup_bot_prod (s : Submonoid M)
 (t : Submonoid N) : (prod s ⊥) ⊔ (prod ⊥ t) = prod s t
· 使用定理 `Submonoid.top_prod_top`：top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submo
noid N) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mrange_inl_sup_mrange_inr : mrange (inl M N) ⊔ mrange (inr M N) = ⊤ := by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

/-- The `MonoidHom` associated to an inclusion of `Submonoid`s. -/
@[to_additive /-- The `AddMonoidHom` associated to an inclusion of `AddSubmonoid`s. -/]
/-
**Submonoid.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：inclusion {S T : Submonoid M} (h : S <= T) : S ->* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M

--- 原说明 ---
The `MonoidHom` associated to an inclusion of `Submonoid`s.
-/
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]
/-
**Submonoid.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_inclusion {S T : Submonoid M} (h : S <= T) (a : S) : (inclusion h a : 
M) = a
参数：h : S <= T；a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_inclusion`：coe_inclusion (h : s subseteq t) (x : s) : (inclusion
 h x : α) = (x : α)
-/
theorem coe_inclusion {S T : Submonoid M} (h : S ≤ T) (a : S) : (inclusion h a : M) = a :=
  Set.coe_inclusion h a

@[to_additive]
/-
**Submonoid.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inclusion_injective {S T : Submonoid M} (h : S <= T) : Function.Injective 
inclusion h
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem inclusion_injective {S T : Submonoid M} (h : S ≤ T) : Function.Injective <| inclusion h :=
  Set.inclusion_injective h

@[to_additive (attr := simp)]
/-
**Submonoid.inclusion_inj** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：inclusion_inj {S T : Submonoid M} (h : S <= T) {x y : S} : inclusion h x =
 inclusion h y ↔ x = y
参数：h : S <= T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submonoid.inclusion_injective`：inclusion_injective {S T : Submonoid M} (
h : S <= T) : Function.Injective inclusion h
-/
lemma inclusion_inj {S T : Submonoid M} (h : S ≤ T) {x y : S} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]
/-
**Submonoid.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subtype_comp_inclusion {S T : Submonoid M} (h : S <= T) : T.subtype.comp (
inclusion h) = S.subtype
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_inclusion {S T : Submonoid M} (h : S ≤ T) :
    T.subtype.comp (inclusion h) = S.subtype :=
  rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mrange_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mrange_subtype (s : Submonoid M) : mrange s.subtype = s
参数：s : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHom.coe_mrange`：coe_mrange (f : F) : (mrange f : Set N) = Set.rang
e f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem mrange_subtype (s : Submonoid M) : mrange s.subtype = s :=
  SetLike.coe_injective <| (coe_mrange _).trans <| Subtype.range_coe

@[to_additive]
/-
**Submonoid.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：eq_top_iff' : S = ⊤ ↔ forall x : M, x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
-/
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

@[to_additive]
/-
**Submonoid.eq_bot_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：eq_bot_iff_forall : S = ⊥ ↔ forall x in S, x = (1 : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) :=
  SetLike.ext_iff.trans <| by simp +contextual [iff_def, S.one_mem]

@[to_additive]
/-
**Submonoid.eq_bot_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：eq_bot_of_subsingleton [Subsingleton S] : S = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.eq_bot_iff_forall`：eq_bot_iff_forall : S = ⊥ ↔ forall x in S, 
x = (1 : M)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  rw [eq_bot_iff_forall]
  intro y hy
  simpa using congr_arg ((↑) : S → M) <| Subsingleton.elim (⟨y, hy⟩ : S) 1

@[to_additive]
/-
**Submonoid.nontrivial_iff_exists_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ exists x i
n S, x != (1 : M)
参数：S : Submonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) :=
  calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _) (hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by simp [Ne]

/-- A `Submonoid` is either the trivial `Submonoid` or nontrivial. -/
@[to_additive /-- An `AddSubmonoid` is either the trivial `AddSubmonoid` or nontrivial. -/]
/-
**Submonoid.bot_or_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A `Submonoid` is either the trivial `Submonoid` or nontrivial.
-/
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

/-- A `Submonoid` is either the trivial `Submonoid` or contains a nonzero element. -/
@[to_additive
  /-- An `AddSubmonoid` is either the trivial `AddSubmonoid` or contains a nonzero element. -/]
/-
**Submonoid.bot_or_exists_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ exists x in S, x != (1 : 
M)
参数：S : Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.nontrivial_iff_exists_ne_one`：nontrivial_iff_exists_ne_one (S 
: Submonoid M) : Nontrivial S ↔ exists x in S, x != (1 : M)
· 使用定理 `Submonoid.bot_or_nontrivial`：bot_or_nontrivial (S : Submonoid M) : S = ⊥
 ∨ Nontrivial S
-/
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

@[to_additive]
/-
**Submonoid.codisjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F} 
(hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) : Codisjoi
nt (H.map f) (K.map f)
参数：hf : Function.Surjective f；h : Codisjoint H K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.map_sup`：map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f =
 S.map f ⊔ T.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
-/
lemma codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) :
    Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← map_sup, codisjoint_iff.mp h, ← MonoidHom.mrange_eq_map,
    mrange_eq_top_of_surjective _ hf]

section Pi

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

/-- A version of `Set.pi` for `Submonoid`s. Given an index set `I` and a family of `Submonoid`s
`s : Π i, Submonoid f i`, `pi I s` is the `Submonoid` of dependent functions `f : Π i, f i` such
that `f i` belongs to `Pi I s` whenever `i ∈ I`. -/
@[to_additive /-- A version of `Set.pi` for `AddSubmonoid`s. Given an index set `I` and a family
  of `AddSubmonoid`s `s : Π i, AddSubmonoid f i`, `pi I s` is the `AddSubmonoid` of dependent
  functions `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
/-
**Submonoid.pi** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：pi (I : Set ι) (S : forall i, Submonoid (M i)) : Submonoid (forall i, M i)
 where carrier
参数：I : Set ι；S : forall i, Submonoid (M i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pi (I : Set ι) (S : ∀ i, Submonoid (M i)) : Submonoid (∀ i, M i) where
  carrier := I.pi fun i => (S i).carrier
  one_mem' i _ := (S i).one_mem
  mul_mem' hp hq i hI := (S i).mul_mem (hp i hI) (hq i hI)

@[to_additive]
/-
**Submonoid.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_pi (I : Set ι) (S : forall i, Submonoid (M i)) : (pi I S : Set (forall
 i, M i)) = Set.pi I fun i => (S i : Set (M i))
参数：I : Set ι；S : forall i, Submonoid (M i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi (I : Set ι) (S : ∀ i, Submonoid (M i)) :
    (pi I S : Set (∀ i, M i)) = Set.pi I fun i => (S i : Set (M i)) :=
  rfl

@[to_additive]
/-
**Submonoid.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_pi (I : Set ι) {S : forall i, Submonoid (M i)} {p : forall i, M i} : p
 in Submonoid.pi I S ↔ forall i, i in I -> p i in S i
参数：I : Set ι；M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pi (I : Set ι) {S : ∀ i, Submonoid (M i)} {p : ∀ i, M i} :
    p ∈ Submonoid.pi I S ↔ ∀ i, i ∈ I → p i ∈ S i :=
  Iff.rfl

@[to_additive]
/-
**Submonoid.pi_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_top (I : Set ι) : (pi I fun i => (⊤ : Submonoid (M i))) = ⊤
参数：I : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_top (I : Set ι) : (pi I fun i => (⊤ : Submonoid (M i))) = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/-
**Submonoid.pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_empty (H : forall i, Submonoid (M i)) : pi ∅ H = ⊤
参数：H : forall i, Submonoid (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_empty (H : ∀ i, Submonoid (M i)) : pi ∅ H = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/-
**Submonoid.pi_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_bot : (pi Set.univ fun i => (⊥ : Submonoid (M i))) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_bot : (pi Set.univ fun i => (⊥ : Submonoid (M i))) = ⊥ :=
  ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]
/-
**Submonoid.le_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_pi_iff {I : Set ι} {S : forall i, Submonoid (M i)} {J : Submonoid (fora
ll i, M i)} : J <= pi I S ↔ forall i in I, J <= comap (Pi.evalMonoidHom M i) (S 
i)
参数：M i；forall i, M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_pi_iff`：subset_pi_iff {s'} : s' subseteq pi s t ↔ forall i in
 s, s' subseteq (· i) ⁻¹' t i
-/
theorem le_pi_iff {I : Set ι} {S : ∀ i, Submonoid (M i)} {J : Submonoid (∀ i, M i)} :
    J ≤ pi I S ↔ ∀ i ∈ I, J ≤ comap (Pi.evalMonoidHom M i) (S i) :=
  Set.subset_pi_iff

@[to_additive (attr := simp)]
/-
**Submonoid.mulSingle_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid (M i
)} (i : ι) (x : M i) : Pi.mulSingle i x in pi I S ↔ i in I -> x in S i
参数：M i；i : ι；x : M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.update_mem_pi_iff_of_mem`：update_mem_pi_iff_of_mem [DecidableEq ι] {
a : forall i, α i} {i : ι} {b : α i} (ha : a in pi s t) : update a i b in pi s t
 ↔ i in s -> b in …
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} (i : ι) (x : M i) :
    Pi.mulSingle i x ∈ pi I S ↔ i ∈ I → x ∈ S i :=
  Set.update_mem_pi_iff_of_mem (one_mem (pi I _))

@[to_additive]
/-
**Submonoid.pi_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_eq_bot_iff (S : forall i, Submonoid (M i)) : pi Set.univ S = ⊥ ↔ forall
 i, S i = ⊥
参数：S : forall i, Submonoid (M i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.univ_pi_eq_singleton_iff`：univ_pi_eq_singleton_iff {a} : pi univ t =
 {a} ↔ forall i, t i = {a i}
-/
theorem pi_eq_bot_iff (S : ∀ i, Submonoid (M i)) : pi Set.univ S = ⊥ ↔ ∀ i, S i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

@[to_additive]
/-
**Submonoid.le_comap_mulSingle_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_comap_mulSingle_pi [DecidableEq ι] (S : forall i, Submonoid (M i)) {I i
} : S i <= comap (MonoidHom.mulSingle M i) (pi I S)
参数：S : forall i, Submonoid (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem le_comap_mulSingle_pi [DecidableEq ι] (S : ∀ i, Submonoid (M i)) {I i} :
    S i ≤ comap (MonoidHom.mulSingle M i) (pi I S) :=
  fun x hx => by simp [hx]

@[to_additive]
/-
**Submonoid.iSup_map_mulSingle_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid
 (M i)} : ⨆ i, map (MonoidHom.mulSingle M i) (S i) <= pi I S
参数：M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {S : Submonoi
d M} {T : Submonoid N} : S.map f <= T ↔ S <= T.comap f
· 使用定理 `Submonoid.le_comap_mulSingle_pi`：le_comap_mulSingle_pi [DecidableEq ι] (
S : forall i, Submonoid (M i)) {I i} : S i <= comap (MonoidHom.mulSingle M i) (p
i I S)
-/
theorem iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} :
    ⨆ i, map (MonoidHom.mulSingle M i) (S i) ≤ pi I S :=
  iSup_le fun _ => map_le_iff_le_comap.mpr (le_comap_mulSingle_pi _)

end Pi

end Submonoid

/-- Restrict the domain and codomain of a `MonoidHom`. -/
@[to_additive /-- Restrict the domain and codomain of an `AddMonoidHom`. -/]
/-
**MonoidHom.restrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.restrict {M' : Submonoid M} {N' : Submonoid N} {f : M ->* N} (h 
: Set.MapsTo f M' N') : M' ->* N'
参数：h : Set.MapsTo f M' N'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M

--- 原说明 ---
Restrict the domain and codomain of a `MonoidHom`.
-/
def MonoidHom.restrict {M' : Submonoid M} {N' : Submonoid N} {f : M →* N}
    (h : Set.MapsTo f M' N') : M' →* N' := (f.domRestrict M').codRestrict N' <| SetLike.forall.mpr h
/-
**MonoidHom.restrict_injective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N] {M' : Submonoid M} {N' : Submonoid N}   {f : M →* N} (h : Set.MapsTo ⇑f ↑M
' ↑N'), Function.Injective ⇑f → Function.Injective ⇑(MonoidHom.restrict h)
参数：h : Set.MapsTo ⇑f ↑M' ↑N'；MonoidHom.restrict h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
@[to_additive] lemma MonoidHom.restrict_injective {M' : Submonoid M} {N' : Submonoid N} {f : M →* N}
    (h : Set.MapsTo f M' N') (hf' : Function.Injective f) : Function.Injective <| f.restrict h :=
  fun _ _ h => Subtype.ext <| hf' <| Subtype.ext_iff.mp h

namespace MulEquiv

variable {S} {T : Submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
monoid are equal. -/
@[to_additive
  /-- Makes the identity additive isomorphism from a proof two submonoids of an additive monoid are
  equal. -/]
/-
**MulEquiv.submonoidCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：submonoidCongr (h : S = T) : S ≃* T
参数：h : S = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submonoidCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.
This is a bidirectional version of `MonoidHom.mrangeRestrict`. -/
@[to_additive (attr := simps +simpRhs)
  /-- An additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an
  additive equivalence between `M` and `f.mrange`. This is a bidirectional version of
  `AddMonoidHom.mrangeRestrict`. -/]
/-
**MulEquiv.ofLeftInverse'** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：ofLeftInverse' (f : M ->* N) {g : N -> M} (h : Function.LeftInverse g f) :
 M ≃* MonoidHom.mrange f
参数：f : M ->* N；h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ (MonoidHom.mrange f).subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }

/-- A `MulEquiv` `φ` between two monoids `M` and `N` induces a `MulEquiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `MonoidHom.submonoidMap` for a variant for `MonoidHom`s. -/
@[to_additive
  /-- An `AddEquiv` `φ` between two additive monoids `M` and `N` induces an `AddEquiv`
  between a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See
  `AddMonoidHom.addSubmonoidMap` for a variant for `AddMonoidHom`s. -/]
/-
**MulEquiv.submonoidMap** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e
参数：e : M ≃* N；S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e :=
  { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_submonoidMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_submonoidMap_apply (e : M ≃* N) (S : Submonoid M) (g : S) : ((submonoi
dMap e S g : S.map (e : M ->* N)) : N) = e g
参数：e : M ≃* N；S : Submonoid M；g : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem coe_submonoidMap_apply (e : M ≃* N) (S : Submonoid M) (g : S) :
    ((submonoidMap e S g : S.map (e : M →* N)) : N) = e g :=
  rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.submonoidMap_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：submonoidMap_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M -
>* N)) : (e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 Set.mem_image_
equiv.1 g.2⟩
参数：e : M ≃* N；S : Submonoid M；g : S.map (e : M ->* N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem submonoidMap_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M →* N)) :
    (e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

@[to_additive (attr := simp)]
/-
**Submonoid.equivMapOfInjective_coe_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.equivMapOfInjective_coe_mulEquiv (e : M ≃* N) : S.equivMapOfInje
ctive (e : M ->* N) (EquivLike.injective e) = e.submonoidMap S
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem Submonoid.equivMapOfInjective_coe_mulEquiv (e : M ≃* N) :
    S.equivMapOfInjective (e : M →* N) (EquivLike.injective e) = e.submonoidMap S := by
  ext
  rfl

@[to_additive]
/-
**Submonoid.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.faithfulSMul {M' α : Type*} [MulOneClass M'] [SMul M' α] {S : Su
bmonoid M'} [FaithfulSMul M' α] : FaithfulSMul S α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
-/
instance Submonoid.faithfulSMul {M' α : Type*} [MulOneClass M'] [SMul M' α] {S : Submonoid M'}
    [FaithfulSMul M' α] : FaithfulSMul S α :=
  ⟨fun h => Subtype.ext <| eq_of_smul_eq_smul h⟩

section Units

namespace Submonoid

set_option backward.isDefEq.respectTransparency false in
/-- The multiplicative equivalence between the type of units of `M` and the submonoid of unit
elements of `M`. -/
@[to_additive (attr := simps!) /-- The additive equivalence between the type of additive units of
`M` and the additive submonoid whose elements are the additive units of `M`. -/]
/-
**Submonoid.unitsTypeEquivIsUnitSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：unitsTypeEquivIsUnitSubmonoid {M : Type*} [Monoid M] : Mˣ ≃* IsUnit.submon
oid M where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
noncomputable def unitsTypeEquivIsUnitSubmonoid {M : Type*} [Monoid M] :
    Mˣ ≃* IsUnit.submonoid M where
  toFun x := ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv _ := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

end Submonoid

end Units

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

@[to_additive]
/-
**Submonoid.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_comap_eq (f : F) (S : Submonoid N) : (S.comap f).map f = S ⊓ MonoidHom
.mrange f
参数：f : F；S : Submonoid N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : F) (S : Submonoid N) : (S.comap f).map f = S ⊓ MonoidHom.mrange f :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]
/-
**Submonoid.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：map_comap_eq_self {f : F} {S : Submonoid N} (h : S <= MonoidHom.mrange f) 
: (S.comap f).map f = S
参数：h : S <= MonoidHom.mrange f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Submonoid.map_comap_eq`：map_comap_eq (f : F) (S : Submonoid N) : (S.coma
p f).map f = S ⊓ MonoidHom.mrange f
-/
theorem map_comap_eq_self {f : F} {S : Submonoid N} (h : S ≤ MonoidHom.mrange f) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

@[to_additive]
/-
**Submonoid.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
`。
形式化陈述：map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : S
ubmonoid N} : map f (comap f S) = S
参数：h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.map_comap_eq_self`：map_comap_eq_self {f : F} {S : Submonoid N}
 (h : S <= MonoidHom.mrange f) : (S.comap f).map f = S
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
-/
theorem map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : Submonoid N} :
    map f (comap f S) = S :=
  map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

end Submonoid

