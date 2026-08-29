/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# Types that are empty

In this file we define a typeclass `IsEmpty`, which expresses that a type has no elements.

## Main declaration

* `IsEmpty`: a typeclass that expresses that a type is empty.
-/

@[expose] public section

universe u v

variable {α : Sort u} {β : Sort v}

/--
Definition of `IsEmpty` / `IsEmpty` 的定义

English:
class IsEmpty
  parameters: (α : Sort u)
  axioms and operations (1):
    - false : α -> False

中文:
类 IsEmpty
  参数: (α : Sort u)
  公理与运算 (1 个):
    - false : α -> False
-/
class IsEmpty (α : Sort u) : Prop where
  protected false : α -> False

/--
Instance `Empty.instIsEmpty` / 实例 `Empty.instIsEmpty`

English:
instance Empty.instIsEmpty
  signature: : IsEmpty Empty
  body: ⟨Empty.elim⟩

中文:
实例 Empty.instIsEmpty
  签名: : IsEmpty Empty
  定义体: ⟨Empty.elim⟩

Depends on / 依赖: Empty.elim
-/
instance Empty.instIsEmpty : IsEmpty Empty :=
  ⟨Empty.elim⟩

/--
Instance `PEmpty.instIsEmpty` / 实例 `PEmpty.instIsEmpty`

English:
instance PEmpty.instIsEmpty
  signature: : IsEmpty PEmpty
  body: ⟨PEmpty.elim⟩

中文:
实例 PEmpty.instIsEmpty
  签名: : IsEmpty PEmpty
  定义体: ⟨PEmpty.elim⟩

Depends on / 依赖: PEmpty, PEmpty.elim
-/
instance PEmpty.instIsEmpty : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty False
  body: ⟨id⟩

中文:
实例 :
  签名: IsEmpty False
  定义体: ⟨id⟩
-/
instance : IsEmpty False :=
  ⟨id⟩

/--
Instance `Fin.isEmpty` / 实例 `Fin.isEmpty`

English:
instance Fin.isEmpty
  signature: : IsEmpty (Fin 0)
  body: ⟨fun n => Nat.not_lt_zero n.1 n.2⟩

中文:
实例 Fin.isEmpty
  签名: : IsEmpty (Fin 0)
  定义体: ⟨fun n => Nat.not_lt_zero n.1 n.2⟩

Depends on / 依赖: Nat.not_lt_zero, not_lt_zero
-/
instance Fin.isEmpty : IsEmpty (Fin 0) :=
  ⟨fun n => Nat.not_lt_zero n.1 n.2⟩

/--
Instance `Fin.isEmpty'` / 实例 `Fin.isEmpty'`

English:
instance Fin.isEmpty'
  signature: : IsEmpty (Fin Nat.zero)
  body: Fin.isEmpty

中文:
实例 Fin.isEmpty'
  签名: : IsEmpty (Fin 自然数.zero)
  定义体: Fin.isEmpty

Depends on / 依赖: Fin.isEmpty, isEmpty
-/
instance Fin.isEmpty' : IsEmpty (Fin Nat.zero) :=
  Fin.isEmpty

/--
theorem `Function.isEmpty` / 定理 `Function.isEmpty`

English:
theorem Function.isEmpty
  given: [IsEmpty β] (f : α -> β)
  statement: IsEmpty α
  proof: ⟨fun x => IsEmpty.false (f x)⟩

中文:
定理 Function.isEmpty
  条件: [IsEmpty β] (f : α -> β)
  结论: IsEmpty α
  证明: ⟨fun x => IsEmpty.false (f x)⟩
-/
protected theorem Function.isEmpty [IsEmpty β] (f : α -> β) : IsEmpty α :=
  ⟨fun x => IsEmpty.false (f x)⟩

/--
theorem `Function.Surjective.isEmpty` / 定理 `Function.Surjective.isEmpty`

English:
theorem Function.Surjective.isEmpty
  given: [IsEmpty α] {f : α -> β} (hf : f.Surjective)
  statement: IsEmpty β
  proof: ⟨fun y => let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

中文:
定理 Function.Surjective.isEmpty
  条件: [IsEmpty α] {f : α -> β} (hf : f.Surjective)
  结论: IsEmpty β
  证明: ⟨fun y => let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

Depends on / 依赖: IsEmpty, IsEmpty.false
-/
theorem Function.Surjective.isEmpty [IsEmpty α] {f : α -> β} (hf : f.Surjective) : IsEmpty β :=
  ⟨fun y => let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

-- See note [instance argument order]
instance {p : α -> Sort v} [forall x, IsEmpty (p x)] [h : Nonempty α] : IsEmpty (forall x, p x) :=
  h.elim fun x => Function.isEmpty fun f => f x

/--
Instance `PProd.isEmpty_left` / 实例 `PProd.isEmpty_left`

English:
instance PProd.isEmpty_left
  signature: [IsEmpty α]
  body: Function.isEmpty PProd.fst

中文:
实例 PProd.isEmpty_left
  签名: [IsEmpty α]
  定义体: Function.isEmpty PProd.fst

Depends on / 依赖: Function, Function.isEmpty, PProd.fst, isEmpty
-/
instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst

/--
Instance `PProd.isEmpty_right` / 实例 `PProd.isEmpty_right`

English:
instance PProd.isEmpty_right
  signature: [IsEmpty β]
  body: Function.isEmpty PProd.snd

中文:
实例 PProd.isEmpty_right
  签名: [IsEmpty β]
  定义体: Function.isEmpty PProd.snd

Depends on / 依赖: Function, Function.isEmpty, PProd.snd, isEmpty
-/
instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd

/--
Instance `Prod.isEmpty_left` / 实例 `Prod.isEmpty_left`

English:
instance Prod.isEmpty_left
  signature: {α β} [IsEmpty α]
  body: Function.isEmpty Prod.fst

中文:
实例 Prod.isEmpty_left
  签名: {α β} [IsEmpty α]
  定义体: Function.isEmpty Prod.fst

Depends on / 依赖: Function, Function.isEmpty, Prod.fst, isEmpty
-/
instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst

/--
Instance `Prod.isEmpty_right` / 实例 `Prod.isEmpty_right`

English:
instance Prod.isEmpty_right
  signature: {α β} [IsEmpty β]
  body: Function.isEmpty Prod.snd

中文:
实例 Prod.isEmpty_right
  签名: {α β} [IsEmpty β]
  定义体: Function.isEmpty Prod.snd

Depends on / 依赖: Function, Function.isEmpty, Prod.snd, isEmpty
-/
instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd

/--
Instance `Quot.instIsEmpty` / 实例 `Quot.instIsEmpty`

English:
instance Quot.instIsEmpty
  signature: [IsEmpty α] {r : α -> α -> Prop}
  body: Function.Surjective.isEmpty Quot.exists_rep

中文:
实例 Quot.instIsEmpty
  签名: [IsEmpty α] {r : α -> α -> 命题}
  定义体: Function.Surjective.isEmpty Quot.exists_rep

Depends on / 依赖: Function, Function.Surjective.isEmpty, Quot.exists_rep, Surjective, exists_rep, isEmpty
-/
instance Quot.instIsEmpty [IsEmpty α] {r : α -> α -> Prop} : IsEmpty (Quot r) :=
  Function.Surjective.isEmpty Quot.exists_rep

/--
Instance `Quotient.instIsEmpty` / 实例 `Quotient.instIsEmpty`

English:
instance Quotient.instIsEmpty
  signature: [IsEmpty α] {s : Setoid α}
  body: Quot.instIsEmpty

中文:
实例 Quotient.instIsEmpty
  签名: [IsEmpty α] {s : Setoid α}
  定义体: Quot.instIsEmpty

Depends on / 依赖: Quot.instIsEmpty, instIsEmpty
-/
instance Quotient.instIsEmpty [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s) :=
  Quot.instIsEmpty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] [IsEmpty β] : IsEmpty (α oplus' β)
  body: ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

中文:
实例 [IsEmpty
  签名: α] [IsEmpty β] : IsEmpty (α oplus' β)
  定义体: ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

Depends on / 依赖: IsEmpty, IsEmpty.false, PSum.rec
-/
instance [IsEmpty α] [IsEmpty β] : IsEmpty (α oplus' β) :=
  ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

/--
Instance `instIsEmptySum` / 实例 `instIsEmptySum`

English:
instance instIsEmptySum
  signature: {α β} [IsEmpty α] [IsEmpty β]
  body: ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

中文:
实例 instIsEmptySum
  签名: {α β} [IsEmpty α] [IsEmpty β]
  定义体: ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

Depends on / 依赖: IsEmpty, IsEmpty.false, Sum.rec
-/
instance instIsEmptySum {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (α oplus β) :=
  ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] (p
  body: ⟨fun x => IsEmpty.false x.1⟩

中文:
实例 [IsEmpty
  签名: α] (p
  定义体: ⟨fun x => IsEmpty.false x.1⟩
-/
instance [IsEmpty α] (p : α -> Prop) : IsEmpty (Subtype p) :=
  ⟨fun x => IsEmpty.false x.1⟩

/--
theorem `Subtype.isEmpty_of_false` / 定理 `Subtype.isEmpty_of_false`

English:
theorem Subtype.isEmpty_of_false
  given: {p : α -> Prop} (hp : forall a, ¬p a)
  statement: IsEmpty (Subtype p)
  proof: ⟨fun x => hp _ x.2⟩

中文:
定理 Subtype.isEmpty_of_false
  条件: {p : α -> 命题} (hp : 对任意 a, ¬p a)
  结论: IsEmpty (Subtype p)
  证明: ⟨fun x => hp _ x.2⟩
-/
theorem Subtype.isEmpty_of_false {p : α -> Prop} (hp : forall a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x => hp _ x.2⟩

/--
Instance `Subtype.isEmpty_false` / 实例 `Subtype.isEmpty_false`

English:
instance Subtype.isEmpty_false
  signature: : IsEmpty { _a : α // False }
  body: Subtype.isEmpty_of_false fun _ => id

中文:
实例 Subtype.isEmpty_false
  签名: : IsEmpty { _a : α // False }
  定义体: Subtype.isEmpty_of_false fun _ => id

Depends on / 依赖: Subtype, Subtype.isEmpty_of_false, isEmpty_of_false
-/
instance Subtype.isEmpty_false : IsEmpty { _a : α // False } :=
  Subtype.isEmpty_of_false fun _ => id

/--
Instance `Sigma.isEmpty_left` / 实例 `Sigma.isEmpty_left`

English:
instance Sigma.isEmpty_left
  signature: {α} [IsEmpty α] {E : α -> Type v}
  body: Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α -> β) := by infer_instance

中文:
实例 Sigma.isEmpty_left
  签名: {α} [IsEmpty α] {E : α -> 类型v}
  定义体: Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α -> β) := by infer_instance

Depends on / 依赖: Function, Function.isEmpty, Sigma.fst, isEmpty
-/
instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α -> Type v} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst

example [h : Nonempty α] [IsEmpty β] : IsEmpty (α -> β) := by infer_instance

/-- Eliminate out of a type that `IsEmpty` (without using projection notation). -/
@[elab_as_elim]
/--
Definition of `isEmptyElim` / `isEmptyElim` 的定义

English:
definition isEmptyElim
  signature: [IsEmpty α] {p : α -> Sort v} (a : α)
  body: (IsEmpty.false a).elim

中文:
定义 isEmptyElim
  签名: [IsEmpty α] {p : α -> Sort v} (a : α)
  定义体: (IsEmpty.false a).elim

Depends on / 依赖: IsEmpty, IsEmpty.false
-/
def isEmptyElim [IsEmpty α] {p : α -> Sort v} (a : α) : p a :=
  (IsEmpty.false a).elim

/--
theorem `isEmpty_iff` / 定理 `isEmpty_iff`

English:
theorem isEmpty_iff
  statement: IsEmpty α ↔ α -> False
  proof: ⟨@IsEmpty.false α, IsEmpty.mk⟩

中文:
定理 isEmpty_iff
  结论: IsEmpty α ↔ α -> False
  证明: ⟨@IsEmpty.false α, IsEmpty.mk⟩

Depends on / 依赖: IsEmpty, IsEmpty.false, IsEmpty.mk
-/
theorem isEmpty_iff : IsEmpty α ↔ α -> False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

/-- Eliminate out of a type that `IsEmpty` (using projection notation). -/
@[elab_as_elim]
/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: (_ : IsEmpty α) {p : α -> Sort v} (a : α)
  body: isEmptyElim a

中文:
定义 elim
  签名: (_ : IsEmpty α) {p : α -> Sort v} (a : α)
  定义体: isEmptyElim a
-/
protected def elim (_ : IsEmpty α) {p : α -> Sort v} (a : α) : p a :=
  isEmptyElim a

/--
Definition of `elim'` / `elim'` 的定义

English:
definition elim'
  signature: (h : IsEmpty α) (a : α)
  body: (h.false a).elim

中文:
定义 elim'
  签名: (h : IsEmpty α) (a : α)
  定义体: (h.false a).elim
-/
protected def elim' (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim

/--
theorem `prop_iff` / 定理 `prop_iff`

English:
theorem prop_iff
  given: {p : Prop}
  statement: IsEmpty p ↔ ¬p
  proof: isEmpty_iff

中文:
定理 prop_iff
  条件: {p : 命题}
  结论: IsEmpty p ↔ ¬p
  证明: isEmpty_iff
-/
protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff

variable [IsEmpty α]

@[simp]
/--
theorem `forall_iff` / 定理 `forall_iff`

English:
theorem forall_iff
  given: {p : α -> Prop}
  statement: (forall a, p a) ↔ True
  proof: iff_true_intro isEmptyElim

@[simp]

中文:
定理 forall_iff
  条件: {p : α -> 命题}
  结论: (对任意 a, p a) ↔ True
  证明: iff_true_intro isEmptyElim

@[simp]

Depends on / 依赖: iff_true_intro, isEmptyElim
-/
theorem forall_iff {p : α -> Prop} : (forall a, p a) ↔ True :=
  iff_true_intro isEmptyElim

@[simp]
/--
theorem `exists_iff` / 定理 `exists_iff`

English:
theorem exists_iff
  given: {p : α -> Prop}
  statement: (exists a, p a) ↔ False
  proof: iff_false_intro fun ⟨x, _⟩ => IsEmpty.false x

中文:
定理 exists_iff
  条件: {p : α -> 命题}
  结论: (存在 a, p a) ↔ False
  证明: iff_false_intro fun ⟨x, _⟩ => IsEmpty.false x

Depends on / 依赖: IsEmpty, IsEmpty.false, iff_false_intro
-/
theorem exists_iff {p : α -> Prop} : (exists a, p a) ↔ False :=
  iff_false_intro fun ⟨x, _⟩ => IsEmpty.false x

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty
