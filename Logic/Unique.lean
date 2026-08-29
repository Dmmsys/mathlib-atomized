/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Tactic.Inhabit

/-!
# Types with a unique term

In this file we define a typeclass `Unique`,
which expresses that a type has a unique term.
In other words, a type that is `Inhabited` and a `Subsingleton`.

## Main declaration

* `Unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `Unique.mk'`: an inhabited subsingleton type is `Unique`. This cannot be an instance because it
  would lead to loops in typeclass inference.

* `Function.Surjective.unique`: if the domain of a surjective function is `Unique`, then its
  codomain is `Unique` as well.

* `Function.Injective.subsingleton`: if the codomain of an injective function is `Subsingleton`,
  then its domain is `Subsingleton` as well.

* `Function.Injective.unique`: if the codomain of an injective function is `Subsingleton` and its
  domain is `Inhabited`, then its domain is `Unique`.

## Implementation details

The typeclass `Unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/

@[expose] public section

universe u v w

-- Don't generate injectivity lemmas, which the `simpNF` linter will complain about.
set_option genInjectivity false in
/-- `Unique α` expresses that `α` is a type with a unique term `default`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
@[ext]
/--
Definition of `Unique` / `Unique` 的定义

English:
structure Unique
  parameters: (α : Sort u)
  extends: Inhabited α
  axioms and operations (1):
    - uniq : forall a : α, a = default

中文:
结构 Unique
  参数: (α : Sort u)
  继承: Inhabited α
  公理与运算 (1 个):
    - uniq : 对任意 a : α, a = default
-/
structure Unique (α : Sort u) extends Inhabited α where
  /-- In a `Unique` type, every term is equal to the default element (from `Inhabited`). -/
  uniq : forall a : α, a = default

attribute [class] Unique

/--
theorem `unique_iff_existsUnique` / 定理 `unique_iff_existsUnique`

English:
theorem unique_iff_existsUnique
  given: (α : Sort u)
  statement: Nonempty (Unique α) ↔ exists! _ : α, True
  proof: ⟨fun ⟨u⟩ => ⟨u.default, trivial, fun a _ => u.uniq a⟩,
   fun ⟨a, _, h⟩ => ⟨⟨⟨a⟩, fun _ => h _ trivial⟩⟩⟩

中文:
定理 unique_iff_existsUnique
  条件: (α : Sort u)
  结论: Nonempty (Unique α) ↔ 存在! _ : α, True
  证明: ⟨fun ⟨u⟩ => ⟨u.default, trivial, fun a _ => u.uniq a⟩,
   fun ⟨a, _, h⟩ => ⟨⟨⟨a⟩, fun _ => h _ trivial⟩⟩⟩

Depends on / 依赖: u.default, u.uniq
-/
theorem unique_iff_existsUnique (α : Sort u) : Nonempty (Unique α) ↔ exists! _ : α, True :=
  ⟨fun ⟨u⟩ => ⟨u.default, trivial, fun a _ => u.uniq a⟩,
   fun ⟨a, _, h⟩ => ⟨⟨⟨a⟩, fun _ => h _ trivial⟩⟩⟩

/--
theorem `unique_subtype_iff_existsUnique` / 定理 `unique_subtype_iff_existsUnique`

English:
theorem unique_subtype_iff_existsUnique
  given: {α} (p : α -> Prop)
  proof: ⟨fun ⟨u⟩ => ⟨u.default.1, u.default.2, fun a h => congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ => ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ => by
      congr
      exact he b hb⟩⟩⟩

中文:
定理 unique_subtype_iff_existsUnique
  条件: {α} (p : α -> 命题)
  证明: ⟨fun ⟨u⟩ => ⟨u.default.1, u.default.2, fun a h => congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ => ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ => by
      congr
      exact he b hb⟩⟩⟩

Depends on / 依赖: Subtype, Subtype.val, congr_arg, u.default, u.uniq
-/
theorem unique_subtype_iff_existsUnique {α} (p : α -> Prop) :
    Nonempty (Unique (Subtype p)) ↔ exists! a, p a :=
  ⟨fun ⟨u⟩ => ⟨u.default.1, u.default.2, fun a h => congr_arg Subtype.val (u.uniq ⟨a, h⟩)⟩,
   fun ⟨a, ha, he⟩ => ⟨⟨⟨⟨a, ha⟩⟩, fun ⟨b, hb⟩ => by
      congr
      exact he b hb⟩⟩⟩

/--
Definition of `uniqueOfSubsingleton` / `uniqueOfSubsingleton` 的定义

English:
abbreviation uniqueOfSubsingleton
  signature: {α : Sort*} [Subsingleton α] (a : α)
  body: a
  uniq _ := Subsingleton.elim _ _

中文:
缩写 uniqueOfSubsingleton
  签名: {α : Sort*} [Subsingleton α] (a : α)
  定义体: a
  uniq _ := Subsingleton.elim _ _
-/
abbrev uniqueOfSubsingleton {α : Sort*} [Subsingleton α] (a : α) : Unique α where
  default := a
  uniq _ := Subsingleton.elim _ _

/--
Instance `PUnit.instUnique` / 实例 `PUnit.instUnique`

English:
instance PUnit.instUnique
  signature: : Unique PUnit.{u} where
  body: PUnit.unit
  uniq x := ext x _

@[simp]

中文:
实例 PUnit.instUnique
  签名: : Unique PUnit.{u} where
  定义体: PUnit.unit
  uniq x := ext x _

@[simp]

Depends on / 依赖: PUnit.unit
-/
instance PUnit.instUnique : Unique PUnit.{u} where
  default := PUnit.unit
  uniq x := ext x _

@[simp]
/--
theorem `PUnit.default_eq_unit` / 定理 `PUnit.default_eq_unit`

English:
theorem PUnit.default_eq_unit
  statement: (default : PUnit) = PUnit.unit
  proof: rfl

中文:
定理 PUnit.default_eq_unit
  结论: (default : PUnit) = PUnit.unit
  证明: rfl
-/
theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit :=
  rfl

/-- Every provable proposition is unique, as all proofs are equal. -/
@[instance_reducible]
/--
Definition of `uniqueProp` / `uniqueProp` 的定义

English:
definition uniqueProp
  signature: {p : Prop} (h : p)
  body: h
  uniq _ := rfl

中文:
定义 uniqueProp
  签名: {p : 命题} (h : p)
  定义体: h
  uniq _ := rfl
-/
def uniqueProp {p : Prop} (h : p) : Unique.{0} p where
  default := h
  uniq _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique True
  body: uniqueProp trivial

中文:
实例 :
  签名: Unique True
  定义体: uniqueProp trivial

Depends on / 依赖: uniqueProp
-/
instance : Unique True :=
  uniqueProp trivial

namespace Unique

open Function

section

variable {α : Sort*} [Unique α]

-- see Note [lower instance priority]
instance (priority := 100) : Inhabited α :=
  toInhabited ‹Unique α›

/--
theorem `eq_default` / 定理 `eq_default`

English:
theorem eq_default
  given: (a : α)
  statement: a = default
  proof: uniq _ a

中文:
定理 eq_default
  条件: (a : α)
  结论: a = default
  证明: uniq _ a
-/
theorem eq_default (a : α) : a = default :=
  uniq _ a

/--
theorem `default_eq` / 定理 `default_eq`

English:
theorem default_eq
  given: (a : α)
  statement: default = a
  proof: (uniq _ a).symm

中文:
定理 default_eq
  条件: (a : α)
  结论: default = a
  证明: (uniq _ a).symm
-/
theorem default_eq (a : α) : default = a :=
  (uniq _ a).symm

-- see Note [lower instance priority]
instance (priority := 100) instSubsingleton : Subsingleton α :=
  subsingleton_of_forall_eq _ eq_default

/--
theorem `forall_iff` / 定理 `forall_iff`

English:
theorem forall_iff
  given: {p : α -> Prop}
  statement: (forall a, p a) ↔ p default
  proof: ⟨fun h => h _, fun h x => by rwa [Unique.eq_default x]⟩

中文:
定理 forall_iff
  条件: {p : α -> 命题}
  结论: (对任意 a, p a) ↔ p default
  证明: ⟨fun h => h _, fun h x => by rwa [Unique.eq_default x]⟩

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem forall_iff {p : α -> Prop} : (forall a, p a) ↔ p default :=
  ⟨fun h => h _, fun h x => by rwa [Unique.eq_default x]⟩

/--
theorem `exists_iff` / 定理 `exists_iff`

English:
theorem exists_iff
  given: {p : α -> Prop}
  statement: Exists p ↔ p default
  proof: ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.intro default⟩

中文:
定理 exists_iff
  条件: {p : α -> 命题}
  结论: Exists p ↔ p default
  证明: ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.intro default⟩

Depends on / 依赖: Exists, Exists.intro, add_mul, eq_default, mul_pow, pow_ne_zero, right_ne_zero_of_mul
-/
theorem exists_iff {p : α -> Prop} : Exists p ↔ p default :=
  ⟨fun ⟨a, ha⟩ => eq_default a ▸ ha, Exists.intro default⟩

end

variable {α : Sort*}

@[ext]
/--
theorem `subsingleton_unique'` / 定理 `subsingleton_unique'`

English:
theorem subsingleton_unique'
  statement: forall h₁ h₂ : Unique α, h₁ = h₂

中文:
定理 subsingleton_unique'
  结论: 对任意 h₁ h₂ : Unique α, h₁ = h₂

Depends on / 依赖: Iff.intro, fermatLastTheoremWith, h.fermatLastTheoremWith
-/
protected theorem subsingleton_unique' : forall h₁ h₂ : Unique α, h₁ = h₂
  | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => by congr; rw [h x, h y]

/--
Instance `subsingleton_unique` / 实例 `subsingleton_unique`

English:
instance subsingleton_unique
  signature: : Subsingleton (Unique α)
  body: ⟨Unique.subsingleton_unique'⟩

中文:
实例 subsingleton_unique
  签名: : Subsingleton (Unique α)
  定义体: ⟨Unique.subsingleton_unique'⟩

Depends on / 依赖: Int.reduceAdd, Nat.isUnit_iff, Nat.reduceAdd, OfNat.ofNat_ne_one, Unique, Unique.subsingleton_unique, _iff_fermatLastTheoremWith, fermatLastTheoremFor_iff_int, fermatLastTheoremWith, isUnit_iff, isUnit_pow_i, ne_eq, not_false_eq_true, ofNat_ne_one, one_pow, pow_zero, reduceAdd, subsingleton_unique, tfae_have
-/
instance subsingleton_unique : Subsingleton (Unique α) :=
  ⟨Unique.subsingleton_unique'⟩

/--
Definition of `mk'` / `mk'` 的定义

English:
abbreviation mk'
  signature: (α : Sort u) [h₁ : Inhabited α] [Subsingleton α]
  body: { h₁ with uniq := fun _ => Subsingleton.elim _ _ }

中文:
缩写 mk'
  签名: (α : Sort u) [h₁ : Inhabited α] [Subsingleton α]
  定义体: { h₁ with uniq := fun _ => Subsingleton.elim _ _ }

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
abbrev mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ => Subsingleton.elim _ _ }

end Unique

/--
theorem `nonempty_unique` / 定理 `nonempty_unique`

English:
theorem nonempty_unique
  given: (α : Sort u) [Subsingleton α] [Nonempty α]
  statement: Nonempty (Unique α)
  proof: by
  inhabit α
  exact ⟨Unique.mk' α⟩

中文:
定理 nonempty_unique
  条件: (α : Sort u) [Subsingleton α] [Nonempty α]
  结论: Nonempty (Unique α)
  证明: by
  inhabit α
  exact ⟨Unique.mk' α⟩

Depends on / 依赖: Unique, Unique.mk, inhabit
-/
theorem nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty α] : Nonempty (Unique α) := by
  inhabit α
  exact ⟨Unique.mk' α⟩

/--
theorem `unique_iff_subsingleton_and_nonempty` / 定理 `unique_iff_subsingleton_and_nonempty`

English:
theorem unique_iff_subsingleton_and_nonempty
  given: (α : Sort u)
  proof: ⟨fun ⟨u⟩ => by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ => nonempty_unique α⟩

中文:
定理 unique_iff_subsingleton_and_nonempty
  条件: (α : Sort u)
  证明: ⟨fun ⟨u⟩ => by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ => nonempty_unique α⟩

Depends on / 依赖: nonempty_unique
-/
theorem unique_iff_subsingleton_and_nonempty (α : Sort u) :
    Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α :=
  ⟨fun ⟨u⟩ => by constructor <;> exact inferInstance,
   fun ⟨hs, hn⟩ => nonempty_unique α⟩

variable {α : Sort*}

@[simp, push ←]
/--
theorem `Pi.default_def` / 定理 `Pi.default_def`

English:
theorem Pi.default_def
  given: {β : α -> Sort v} [forall a, Inhabited (β a)]
  proof: rfl

中文:
定理 Pi.default_def
  条件: {β : α -> Sort v} [对任意 a, Inhabited (β a)]
  证明: rfl
-/
theorem Pi.default_def {β : α -> Sort v} [forall a, Inhabited (β a)] :
    @default (forall a, β a) _ = fun a : α => @default (β a) _ :=
  rfl

/--
theorem `Pi.default_apply` / 定理 `Pi.default_apply`

English:
theorem Pi.default_apply
  given: {β : α -> Sort v} [forall a, Inhabited (β a)] (a : α)
  proof: rfl

中文:
定理 Pi.default_apply
  条件: {β : α -> Sort v} [对任意 a, Inhabited (β a)] (a : α)
  证明: rfl
-/
theorem Pi.default_apply {β : α -> Sort v} [forall a, Inhabited (β a)] (a : α) :
    @default (forall a, β a) _ a = default :=
  rfl

/--
Instance `Pi.unique` / 实例 `Pi.unique`

English:
instance Pi.unique
  signature: {β : α -> Sort v} [forall a, Unique (β a)]
  body: fun _ => funext fun _ => Unique.eq_default _

中文:
实例 Pi.unique
  签名: {β : α -> Sort v} [对任意 a, Unique (β a)]
  定义体: fun _ => funext fun _ => Unique.eq_default _

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
instance Pi.unique {β : α -> Sort v} [forall a, Unique (β a)] : Unique (forall a, β a) where
  uniq := fun _ => funext fun _ => Unique.eq_default _

/--
Instance `Pi.uniqueOfIsEmpty` / 实例 `Pi.uniqueOfIsEmpty`

English:
instance Pi.uniqueOfIsEmpty
  signature: [IsEmpty α] (β : α -> Sort v)
  body: isEmptyElim
  uniq _ := funext isEmptyElim

中文:
实例 Pi.uniqueOfIsEmpty
  签名: [IsEmpty α] (β : α -> Sort v)
  定义体: isEmptyElim
  uniq _ := funext isEmptyElim

Depends on / 依赖: isEmptyElim
-/
instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α -> Sort v) : Unique (forall a, β a) where
  default := isEmptyElim
  uniq _ := funext isEmptyElim

/--
theorem `eq_const_of_subsingleton` / 定理 `eq_const_of_subsingleton`

English:
theorem eq_const_of_subsingleton
  given: {β : Sort*} [Subsingleton α] (f : α -> β) (a : α)
  proof: funext fun x => Subsingleton.elim x a ▸ rfl

中文:
定理 eq_const_of_subsingleton
  条件: {β : Sort*} [Subsingleton α] (f : α -> β) (a : α)
  证明: funext fun x => Subsingleton.elim x a ▸ rfl

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem eq_const_of_subsingleton {β : Sort*} [Subsingleton α] (f : α -> β) (a : α) :
    f = Function.const α (f a) :=
  funext fun x => Subsingleton.elim x a ▸ rfl

/--
theorem `eq_const_of_unique` / 定理 `eq_const_of_unique`

English:
theorem eq_const_of_unique
  given: {β : Sort*} [Unique α] (f : α -> β)
  statement: f = Function.const α (f default)
  proof: eq_const_of_subsingleton ..

中文:
定理 eq_const_of_unique
  条件: {β : Sort*} [Unique α] (f : α -> β)
  结论: f = Function.const α (f default)
  证明: eq_const_of_subsingleton ..

Depends on / 依赖: eq_const_of_subsingleton
-/
theorem eq_const_of_unique {β : Sort*} [Unique α] (f : α -> β) : f = Function.const α (f default) :=
  eq_const_of_subsingleton ..

/--
theorem `heq_const_of_unique` / 定理 `heq_const_of_unique`

English:
theorem heq_const_of_unique
  given: [Unique α] {β : α -> Sort v} (f : forall a, β a)
  proof: (Function.hfunext rfl) fun i _ _ => by rw [Subsingleton.elim i default]; rfl

中文:
定理 heq_const_of_unique
  条件: [Unique α] {β : α -> Sort v} (f : 对任意 a, β a)
  证明: (Function.hfunext rfl) fun i _ _ => by rw [Subsingleton.elim i default]; rfl

Depends on / 依赖: Function, Function.hfunext, Subsingleton, Subsingleton.elim, hfunext
-/
theorem heq_const_of_unique [Unique α] {β : α -> Sort v} (f : forall a, β a) :
    f ≍ Function.const α (f default) :=
  (Function.hfunext rfl) fun i _ _ => by rw [Subsingleton.elim i default]; rfl

namespace Function

variable {β : Sort*} {f : α -> β}

/--
theorem `Injective.subsingleton` / 定理 `Injective.subsingleton`

English:
theorem Injective.subsingleton
  given: (hf : Injective f) [Subsingleton β]
  statement: Subsingleton α
  proof: ⟨fun _ _ => hf Subsingleton.elim _ _⟩

中文:
定理 Injective.subsingleton
  条件: (hf : Injective f) [Subsingleton β]
  结论: Subsingleton α
  证明: ⟨fun _ _ => hf Subsingleton.elim _ _⟩
-/
protected theorem Injective.subsingleton (hf : Injective f) [Subsingleton β] : Subsingleton α :=
⟨fun _ _ => hf Subsingleton.elim _ _⟩

/--
theorem `Surjective.subsingleton` / 定理 `Surjective.subsingleton`

English:
theorem Surjective.subsingleton
  given: [Subsingleton α] (hf : Surjective f)
  statement: Subsingleton β
  proof: ⟨hf.forall₂.2 fun x y => congr_arg f Subsingleton.elim x y⟩

中文:
定理 Surjective.subsingleton
  条件: [Subsingleton α] (hf : Surjective f)
  结论: Subsingleton β
  证明: ⟨hf.forall₂.2 fun x y => congr_arg f Subsingleton.elim x y⟩
-/
protected theorem Surjective.subsingleton [Subsingleton α] (hf : Surjective f) : Subsingleton β :=
⟨hf.forall₂.2 fun x y => congr_arg f Subsingleton.elim x y⟩

/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
@[instance_reducible]
/--
Definition of `Surjective.unique` / `Surjective.unique` 的定义

English:
definition Surjective.unique
  signature: {α : Sort u} (f : α -> β) (hf : Surjective f) [Unique.{u} α]
  body: @Unique.mk' _ ⟨f default⟩ hf.subsingleton

中文:
定义 Surjective.unique
  签名: {α : Sort u} (f : α -> β) (hf : Surjective f) [Unique.{u} α]
  定义体: @Unique.mk' _ ⟨f default⟩ hf.subsingleton
-/
protected def Surjective.unique {α : Sort u} (f : α -> β) (hf : Surjective f) [Unique.{u} α] :
    Unique β :=
  @Unique.mk' _ ⟨f default⟩ hf.subsingleton

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `Unique`. -/
@[instance_reducible]
/--
Definition of `Injective.unique` / `Injective.unique` 的定义

English:
definition Injective.unique
  signature: [Inhabited α] [Subsingleton β] (hf : Injective f)
  body: @Unique.mk' _ _ hf.subsingleton

中文:
定义 Injective.unique
  签名: [Inhabited α] [Subsingleton β] (hf : Injective f)
  定义体: @Unique.mk' _ _ hf.subsingleton
-/
protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
  @Unique.mk' _ _ hf.subsingleton

/-- If a constant function is surjective, then the codomain is a singleton. -/
@[instance_reducible]
/--
Definition of `Surjective.uniqueOfSurjectiveConst` / `Surjective.uniqueOfSurjectiveConst` 的定义

English:
definition Surjective.uniqueOfSurjectiveConst
  signature: (α : Type*) {β : Type*} (b : β)
  body: @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ => rfl) b

中文:
定义 Surjective.uniqueOfSurjectiveConst
  签名: (α : 类型) {β : 类型} (b : β)
  定义体: @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ => rfl) b

Depends on / 依赖: h.forall.mpr, subsingleton_of_forall_eq, uniqueOfSubsingleton
-/
def Surjective.uniqueOfSurjectiveConst (α : Type*) {β : Type*} (b : β)
    (h : Function.Surjective (Function.const α b)) : Unique β :=
  @uniqueOfSubsingleton _ (subsingleton_of_forall_eq b <| h.forall.mpr fun _ => rfl) b

end Function

section Pi

variable {ι : Sort*} {α : ι -> Sort*}

/--
Definition of `uniqueElim` / `uniqueElim` 的定义

English:
definition uniqueElim
  signature: [Unique ι] (x : α (default : ι)) (i : ι)
  body: by
  rw [Unique.eq_default i]
  exact x

@[simp]

中文:
定义 uniqueElim
  签名: [Unique ι] (x : α (default : ι)) (i : ι)
  定义体: by
  rw [Unique.eq_default i]
  exact x

@[simp]

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
def uniqueElim [Unique ι] (x : α (default : ι)) (i : ι) : α i := by
  rw [Unique.eq_default i]
  exact x

@[simp]
/--
theorem `uniqueElim_default` / 定理 `uniqueElim_default`

English:
theorem uniqueElim_default
  given: {_ : Unique ι} (x : α (default : ι))
  statement: uniqueElim x (default : ι) = x
  proof: rfl

@[simp]

中文:
定理 uniqueElim_default
  条件: {_ : Unique ι} (x : α (default : ι))
  结论: uniqueElim x (default : ι) = x
  证明: rfl

@[simp]
-/
theorem uniqueElim_default {_ : Unique ι} (x : α (default : ι)) : uniqueElim x (default : ι) = x :=
  rfl

@[simp]
/--
theorem `uniqueElim_const` / 定理 `uniqueElim_const`

English:
theorem uniqueElim_const
  given: {β : Sort*} {_ : Unique ι} (x : β) (i : ι)
  proof: rfl

中文:
定理 uniqueElim_const
  条件: {β : Sort*} {_ : Unique ι} (x : β) (i : ι)
  证明: rfl
-/
theorem uniqueElim_const {β : Sort*} {_ : Unique ι} (x : β) (i : ι) :
    uniqueElim (α := fun _ => β) x i = x :=
  rfl

end Pi

-- TODO: Mario turned this off as a simp lemma in Batteries, wanting to profile it.
attribute [local simp] eq_iff_true_of_subsingleton in
/--
theorem `Unique.bijective` / 定理 `Unique.bijective`

English:
theorem Unique.bijective
  given: {A B} [Unique A] [Unique B] {f : A -> B}
  statement: Function.Bijective f
  proof: by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨default, ?_, ?_⟩ <;> intro x <;> simp

中文:
定理 Unique.bijective
  条件: {A B} [Unique A] [Unique B] {f : A -> B}
  结论: Function.Bijective f
  证明: by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨default, ?_, ?_⟩ <;> intro x <;> simp

Depends on / 依赖: Function, Function.bijective_iff_has_inverse, bijective_iff_has_inverse
-/
theorem Unique.bijective {A B} [Unique A] [Unique B] {f : A -> B} : Function.Bijective f := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨default, ?_, ?_⟩ <;> intro x <;> simp

namespace Option

/--
theorem `subsingleton_iff_isEmpty` / 定理 `subsingleton_iff_isEmpty`

English:
theorem subsingleton_iff_isEmpty
  given: {α : Type u}
  statement: Subsingleton (Option α) ↔ IsEmpty α
  proof: ⟨fun h => ⟨fun x => Option.noConfusion rfl (heq_of_eq (@Subsingleton.elim _ h x none))⟩,
   fun h => ⟨fun x y =>
     Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩

中文:
定理 subsingleton_iff_isEmpty
  条件: {α : 类型u}
  结论: Subsingleton (Option α) ↔ IsEmpty α
  证明: ⟨fun h => ⟨fun x => Option.noConfusion rfl (heq_of_eq (@Subsingleton.elim _ h x none))⟩,
   fun h => ⟨fun x y =>
     Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩

Depends on / 依赖: Option.casesOn, Option.noConfusion, Subsingleton, Subsingleton.elim, casesOn, h.elim, heq_of_eq, noConfusion
-/
theorem subsingleton_iff_isEmpty {α : Type u} : Subsingleton (Option α) ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => Option.noConfusion rfl (heq_of_eq (@Subsingleton.elim _ h x none))⟩,
   fun h => ⟨fun x y =>
     Option.casesOn x (Option.casesOn y rfl fun x => h.elim x) fun x => h.elim x⟩⟩

instance {α} [IsEmpty α] : Unique (Option α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

end Option

section Subtype

/--
Instance `Unique.subtypeEq` / 实例 `Unique.subtypeEq`

English:
instance Unique.subtypeEq
  signature: (y : α)
  body: ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by congr

中文:
实例 Unique.subtypeEq
  签名: (y : α)
  定义体: ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by congr
-/
instance Unique.subtypeEq (y : α) : Unique { x // x = y } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by congr

/--
Instance `Unique.subtypeEq'` / 实例 `Unique.subtypeEq'`

English:
instance Unique.subtypeEq'
  signature: (y : α)
  body: ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by subst hx; congr

中文:
实例 Unique.subtypeEq'
  签名: (y : α)
  定义体: ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by subst hx; congr
-/
instance Unique.subtypeEq' (y : α) : Unique { x // y = x } where
  default := ⟨y, rfl⟩
  uniq := fun ⟨x, hx⟩ => by subst hx; congr

end Subtype

/--
Instance `Fin.instUnique` / 实例 `Fin.instUnique`

English:
instance Fin.instUnique
  signature: : Unique (Fin 1) where uniq _
  body: Subsingleton.elim _ _

中文:
实例 Fin.instUnique
  签名: : Unique (Fin 1) where uniq _
  定义体: Subsingleton.elim _ _

Depends on / 依赖: FermatLastTheoremWith, IsIntegrallyClosed, IsIntegrallyClosed.pow_dvd_pow_iff, Subsingleton, Subsingleton.elim, classical, eq_a, eq_b, eq_c, gcd_dvd_left, gcd_dvd_right, gcd_ne_zero_of_left, heq.symm, mul_add, mul_ne_zero_iff, mul_pow, pow_dvd_pow_iff
-/
instance Fin.instUnique : Unique (Fin 1) where uniq _ := Subsingleton.elim _ _
