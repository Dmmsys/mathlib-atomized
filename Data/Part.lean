/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Equiv.Defs

/-!
# Partial values of a type

This file defines `Part α`, the partial values of a type.
`o : Part α` carries a proposition `o.Dom`, its domain, along with a function `get : o.Dom → α`, its
value. The rule is then that every partial value has a value but, to access it, you need to provide
a proof of the domain.
`Part α` behaves the same as `Option α` except that `o : Option α` is decidably `none` or `some a`
for some `a : α`, while the domain of `o : Part α` doesn't have to be decidable. That means you can
translate back and forth between a partial value with a decidable domain and an option, and
`Option α` and `Part α` are classically equivalent. In general, `Part α` is bigger than `Option α`.

## Main declarations
`Option`-like declarations:
* `Part.none`: The partial value whose domain is `False`.
* `Part.some a`: The partial value whose domain is `True` and whose value is `a`.
* `Part.ofOption`: Converts an `Option α` to a `Part α` by sending `none` to `none` and `some a` to
  `some a`.
* `Part.toOption`: Converts a `Part α` with a decidable domain to an `Option α`.
* `Part.equivOption`: Classical equivalence between `Part α` and `Option α`.

Monadic structure:
* `Part.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* `Part.map`: Maps the value and keeps the same domain.

Other:
* `Part.restrict`: `Part.restrict p o` replaces the domain of `o : Part α` by `p : Prop` so long as
  `p → o.Dom`.
* `Part.assert`: `assert p f` appends `p` to the domains of the values of a partial function.
* `Part.unwrap`: Gets the value of a partial value regardless of its domain. Unsound.

## Notation
For `a : α`, `o : Part α`, `a ∈ o` means that `o` is defined and equal to `a`. Formally, it means
`o.Dom` and `o.get _ = a`.
-/

@[expose] public section

assert_not_exists RelIso

open Function

/--
Definition of `Part.` / `Part.` 的定义

English:
structure Part.{u}
  parameters: (α : Type u)
  axioms and operations (2):
    - Dom : Prop
    - get : Dom -> α

中文:
结构 Part.{u}
  参数: (α : 类型u)
  公理与运算 (2 个):
    - Dom : 命题
    - get : Dom -> α
-/
structure Part.{u} (α : Type u) : Type u where
  /-- The domain of a partial value -/
  Dom : Prop
  /-- Extract a value from a partial value given a proof of `Dom` -/
  get : Dom -> α

namespace Part

variable {α : Type*} {β : Type*} {γ : Type*}

/--
Definition of `toOption` / `toOption` 的定义

English:
definition toOption
  signature: (o : Part α) [Decidable o.Dom]
  body: if h : Dom o then some (o.get h) else none

中文:
定义 toOption
  签名: (o : Part α) [可判定 o.Dom]
  定义体: if h : Dom o then some (o.get h) else none

Depends on / 依赖: o.get
-/
def toOption (o : Part α) [Decidable o.Dom] : Option α :=
  if h : Dom o then some (o.get h) else none

/--
lemma `toOption_isSome` / 引理 `toOption_isSome`

English:
lemma toOption_isSome
  given: (o : Part α) [Decidable o.Dom]
  statement: o.toOption.isSome ↔ o.Dom
  proof: by
  by_cases h : o.Dom <;> simp [h, toOption]

中文:
引理 toOption_isSome
  条件: (o : Part α) [可判定 o.Dom]
  结论: o.toOption.isSome ↔ o.Dom
  证明: by
  by_cases h : o.Dom <;> simp [h, toOption]
-/
@[simp] lemma toOption_isSome (o : Part α) [Decidable o.Dom] : o.toOption.isSome ↔ o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]

/--
lemma `toOption_eq_none` / 引理 `toOption_eq_none`

English:
lemma toOption_eq_none
  given: (o : Part α) [Decidable o.Dom]
  statement: o.toOption = none ↔ ¬o.Dom
  proof: by
  by_cases h : o.Dom <;> simp [h, toOption]

中文:
引理 toOption_eq_none
  条件: (o : Part α) [可判定 o.Dom]
  结论: o.toOption = none ↔ ¬o.Dom
  证明: by
  by_cases h : o.Dom <;> simp [h, toOption]
-/
@[simp] lemma toOption_eq_none (o : Part α) [Decidable o.Dom] : o.toOption = none ↔ ¬o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h₂, o.get h₁ = p.get h₂) -> o = p
  proof: propext H1
    cases t; rw [show o = p from funext fun p => H2 p p]

中文:
定理 ext'
  结论: 对任意 {o p : Part α}, (o.Dom ↔ p.Dom) -> (对任意 h₁ h₂, o.get h₁ = p.get h₂) -> o = p
  证明: propext H1
    cases t; rw [show o = p from funext fun p => H2 p p]

Depends on / 依赖: propext
-/
theorem ext' : forall {o p : Part α}, (o.Dom ↔ p.Dom) -> (forall h₁ h₂, o.get h₁ = p.get h₂) -> o = p
  | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by
    have t : od = pd := propext H1
    cases t; rw [show o = p from funext fun p => H2 p p]

/-- `Part` eta expansion -/
@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  statement: forall o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o

中文:
定理 eta
  结论: 对任意 o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o

Depends on / 依赖: o.get
-/
theorem eta : forall o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o
  | ⟨_, _⟩ => rfl

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (o : Part α) (a : α)
  body: exists h, o.get h = a

中文:
定义 Mem
  签名: (o : Part α) (a : α)
  定义体: exists h, o.get h = a
-/
protected def Mem (o : Part α) (a : α) : Prop :=
  exists h, o.get h = a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Part α)
  body: ⟨Part.Mem⟩

中文:
实例 :
  签名: Membership α (Part α)
  定义体: ⟨Part.Mem⟩

Depends on / 依赖: Part.Mem
-/
instance : Membership α (Part α) :=
  ⟨Part.Mem⟩

/--
theorem `mem_eq` / 定理 `mem_eq`

English:
theorem mem_eq
  given: (a : α) (o : Part α)
  statement: (a in o) = exists h, o.get h = a
  proof: rfl

中文:
定理 mem_eq
  条件: (a : α) (o : Part α)
  结论: (a in o) = 存在 h, o.get h = a
  证明: rfl
-/
theorem mem_eq (a : α) (o : Part α) : (a in o) = exists h, o.get h = a :=
  rfl

/--
theorem `dom_iff_mem` / 定理 `dom_iff_mem`

English:
theorem dom_iff_mem
  statement: forall {o : Part α}, o.Dom ↔ exists y, y in o

中文:
定理 dom_iff_mem
  结论: 对任意 {o : Part α}, o.Dom ↔ 存在 y, y in o
-/
theorem dom_iff_mem : forall {o : Part α}, o.Dom ↔ exists y, y in o
  | ⟨_, f⟩ => ⟨fun h => ⟨f h, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩

/--
theorem `get_mem` / 定理 `get_mem`

English:
theorem get_mem
  given: {o : Part α} (h)
  statement: get o h in o
  proof: ⟨_, rfl⟩

@[simp]

中文:
定理 get_mem
  条件: {o : Part α} (h)
  结论: get o h in o
  证明: ⟨_, rfl⟩

@[simp]
-/
theorem get_mem {o : Part α} (h) : get o h in o :=
  ⟨_, rfl⟩

@[simp]
/--
theorem `mem_mk_iff` / 定理 `mem_mk_iff`

English:
theorem mem_mk_iff
  given: {p : Prop} {o : p -> α} {a : α}
  statement: a in Part.mk p o ↔ exists h, o h = a
  proof: Iff.rfl

中文:
定理 mem_mk_iff
  条件: {p : 命题} {o : p -> α} {a : α}
  结论: a in Part.mk p o ↔ 存在 h, o h = a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff {p : Prop} {o : p -> α} {a : α} : a in Part.mk p o ↔ exists h, o h = a :=
  Iff.rfl

/-- `Part` extensionality -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {o p : Part α} (H : forall a, a in o ↔ a in p)
  statement: o = p
  proof: (ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩) fun _ _ =>
    ((H _).2 ⟨_, rfl⟩).snd

中文:
定理 ext
  条件: {o p : Part α} (H : 对任意 a, a in o ↔ a in p)
  结论: o = p
  证明: (ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩) fun _ _ =>
    ((H _).2 ⟨_, rfl⟩).snd
-/
theorem ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p :=
  (ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩) fun _ _ =>
    ((H _).2 ⟨_, rfl⟩).snd

/--
Definition of `none` / `none` 的定义

English:
definition none
  signature: : Part α
  body: ⟨False, False.rec⟩

中文:
定义 none
  签名: : Part α
  定义体: ⟨False, False.rec⟩

Depends on / 依赖: False.rec
-/
def none : Part α :=
  ⟨False, False.rec⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Part α)
  body: ⟨none⟩

@[simp]

中文:
实例 :
  签名: 可居 (Part α)
  定义体: ⟨none⟩

@[simp]
-/
instance : Inhabited (Part α) :=
  ⟨none⟩

@[simp]
/--
theorem `notMem_none` / 定理 `notMem_none`

English:
theorem notMem_none
  given: (a : α)
  statement: a ∉ @none α
  proof: fun h => h.fst

中文:
定理 notMem_none
  条件: (a : α)
  结论: a ∉ @none α
  证明: fun h => h.fst

Depends on / 依赖: h.fst
-/
theorem notMem_none (a : α) : a ∉ @none α := fun h => h.fst

/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: (a : α)
  body: ⟨True, fun _ => a⟩

@[simp]

中文:
定义 some
  签名: (a : α)
  定义体: ⟨True, fun _ => a⟩

@[simp]
-/
def some (a : α) : Part α :=
  ⟨True, fun _ => a⟩

@[simp]
/--
theorem `some_dom` / 定理 `some_dom`

English:
theorem some_dom
  given: (a : α)
  statement: (some a).Dom
  proof: trivial

中文:
定理 some_dom
  条件: (a : α)
  结论: (some a).Dom
  证明: trivial
-/
theorem some_dom (a : α) : (some a).Dom :=
  trivial

/--
theorem `mem_unique` / 定理 `mem_unique`

English:
theorem mem_unique
  statement: forall {a b : α} {o : Part α}, a in o -> b in o -> a = b

中文:
定理 mem_unique
  结论: 对任意 {a b : α} {o : Part α}, a in o -> b in o -> a = b
-/
theorem mem_unique : forall {a b : α} {o : Part α}, a in o -> b in o -> a = b
  | _, _, ⟨_, _⟩, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

/--
theorem `mem_right_unique` / 定理 `mem_right_unique`

English:
theorem mem_right_unique
  statement: forall {a : α} {o p : Part α}, a in o -> a in p -> o = p

中文:
定理 mem_right_unique
  结论: 对任意 {a : α} {o p : Part α}, a in o -> a in p -> o = p
-/
theorem mem_right_unique : forall {a : α} {o p : Part α}, a in o -> a in p -> o = p
  | _, _, _, ⟨ho, _⟩, ⟨hp, _⟩ => ext' (iff_of_true ho hp) (by simp [*])

/--
theorem `Mem.left_unique` / 定理 `Mem.left_unique`

English:
theorem Mem.left_unique
  statement: Relator.LeftUnique ((· in ·) : α -> Part α -> Prop)
  proof: fun _ _ _ =>
  mem_unique

中文:
定理 Mem.left_unique
  结论: Relator.LeftUnique ((· in ·) : α -> Part α -> 命题)
  证明: fun _ _ _ =>
  mem_unique
-/
theorem Mem.left_unique : Relator.LeftUnique ((· in ·) : α -> Part α -> Prop) := fun _ _ _ =>
  mem_unique

/--
theorem `Mem.right_unique` / 定理 `Mem.right_unique`

English:
theorem Mem.right_unique
  statement: Relator.RightUnique ((· in ·) : α -> Part α -> Prop)
  proof: fun _ _ _ =>
  mem_right_unique

中文:
定理 Mem.right_unique
  结论: Relator.RightUnique ((· in ·) : α -> Part α -> 命题)
  证明: fun _ _ _ =>
  mem_right_unique
-/
theorem Mem.right_unique : Relator.RightUnique ((· in ·) : α -> Part α -> Prop) := fun _ _ _ =>
  mem_right_unique

/--
theorem `get_eq_of_mem` / 定理 `get_eq_of_mem`

English:
theorem get_eq_of_mem
  given: {o : Part α} {a} (h : a in o) (h')
  statement: get o h' = a
  proof: mem_unique ⟨_, rfl⟩ h

中文:
定理 get_eq_of_mem
  条件: {o : Part α} {a} (h : a in o) (h')
  结论: get o h' = a
  证明: mem_unique ⟨_, rfl⟩ h

Depends on / 依赖: mem_unique
-/
theorem get_eq_of_mem {o : Part α} {a} (h : a in o) (h') : get o h' = a :=
  mem_unique ⟨_, rfl⟩ h

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (o : Part α)
  statement: Set.Subsingleton { a | a in o }
  proof: fun _ ha _ hb =>
  mem_unique ha hb

@[simp]

中文:
定理 subsingleton
  条件: (o : Part α)
  结论: 集合.子单例 { a | a in o }
  证明: fun _ ha _ hb =>
  mem_unique ha hb

@[simp]
-/
protected theorem subsingleton (o : Part α) : Set.Subsingleton { a | a in o } := fun _ ha _ hb =>
  mem_unique ha hb

@[simp]
/--
theorem `get_some` / 定理 `get_some`

English:
theorem get_some
  given: {a : α} (ha : (some a).Dom)
  statement: get (some a) ha = a
  proof: rfl

中文:
定理 get_some
  条件: {a : α} (ha : (some a).Dom)
  结论: get (some a) ha = a
  证明: rfl
-/
theorem get_some {a : α} (ha : (some a).Dom) : get (some a) ha = a :=
  rfl

/--
theorem `mem_some` / 定理 `mem_some`

English:
theorem mem_some
  given: (a : α)
  statement: a in some a
  proof: ⟨trivial, rfl⟩

@[simp]

中文:
定理 mem_some
  条件: (a : α)
  结论: a in some a
  证明: ⟨trivial, rfl⟩

@[simp]
-/
theorem mem_some (a : α) : a in some a :=
  ⟨trivial, rfl⟩

@[simp]
/--
theorem `mem_some_iff` / 定理 `mem_some_iff`

English:
theorem mem_some_iff
  given: {a b}
  statement: b in (some a : Part α) ↔ b = a
  proof: ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨trivial, e.symm⟩⟩

中文:
定理 mem_some_iff
  条件: {a b}
  结论: b in (some a : Part α) ↔ b = a
  证明: ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨trivial, e.symm⟩⟩

Depends on / 依赖: e.symm
-/
theorem mem_some_iff {a b} : b in (some a : Part α) ↔ b = a :=
  ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨trivial, e.symm⟩⟩

/--
theorem `eq_some_iff` / 定理 `eq_some_iff`

English:
theorem eq_some_iff
  given: {a : α} {o : Part α}
  statement: o = some a ↔ a in o
  proof: ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩

中文:
定理 eq_some_iff
  条件: {a : α} {o : Part α}
  结论: o = some a ↔ a in o
  证明: ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩

Depends on / 依赖: e.symm, iff_true_intro, mem_some
-/
theorem eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o :=
  ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩

/--
theorem `eq_none_iff` / 定理 `eq_none_iff`

English:
theorem eq_none_iff
  given: {o : Part α}
  statement: o = none ↔ forall a, a ∉ o
  proof: ⟨fun e => e.symm ▸ notMem_none, fun h => ext (by simpa)⟩

中文:
定理 eq_none_iff
  条件: {o : Part α}
  结论: o = none ↔ 对任意 a, a ∉ o
  证明: ⟨fun e => e.symm ▸ notMem_none, fun h => ext (by simpa)⟩

Depends on / 依赖: e.symm, notMem_none
-/
theorem eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o :=
  ⟨fun e => e.symm ▸ notMem_none, fun h => ext (by simpa)⟩

/--
theorem `eq_none_iff'` / 定理 `eq_none_iff'`

English:
theorem eq_none_iff'
  given: {o : Part α}
  statement: o = none ↔ ¬o.Dom
  proof: ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun _ h' => h h'.fst⟩

@[simp]

中文:
定理 eq_none_iff'
  条件: {o : Part α}
  结论: o = none ↔ ¬o.Dom
  证明: ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun _ h' => h h'.fst⟩

@[simp]

Depends on / 依赖: e.symm, eq_none_iff
-/
theorem eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom :=
  ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun _ h' => h h'.fst⟩

@[simp]
/--
theorem `not_none_dom` / 定理 `not_none_dom`

English:
theorem not_none_dom
  statement: ¬(none : Part α).Dom
  proof: id

@[simp]

中文:
定理 not_none_dom
  结论: ¬(none : Part α).Dom
  证明: id

@[simp]
-/
theorem not_none_dom : ¬(none : Part α).Dom :=
  id

@[simp]
/--
theorem `some_ne_none` / 定理 `some_ne_none`

English:
theorem some_ne_none
  given: (x : α)
  statement: some x != none
  proof: by
  intro h
  exact true_ne_false (congr_arg Dom h)

@[simp]

中文:
定理 some_ne_none
  条件: (x : α)
  结论: some x != none
  证明: by
  intro h
  exact true_ne_false (congr_arg Dom h)

@[simp]

Depends on / 依赖: congr_arg, true_ne_false
-/
theorem some_ne_none (x : α) : some x != none := by
  intro h
  exact true_ne_false (congr_arg Dom h)

@[simp]
/--
theorem `none_ne_some` / 定理 `none_ne_some`

English:
theorem none_ne_some
  given: (x : α)
  statement: none != some x
  proof: (some_ne_none x).symm

中文:
定理 none_ne_some
  条件: (x : α)
  结论: none != some x
  证明: (some_ne_none x).symm

Depends on / 依赖: some_ne_none
-/
theorem none_ne_some (x : α) : none != some x :=
  (some_ne_none x).symm

/--
theorem `ne_none_iff` / 定理 `ne_none_iff`

English:
theorem ne_none_iff
  given: {o : Part α}
  statement: o != none ↔ exists x, o = some x
  proof: by
  constructor
  · rw [Ne, eq_none_iff', not_not]
    exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
  · rintro ⟨x, rfl⟩
    apply some_ne_none

中文:
定理 ne_none_iff
  条件: {o : Part α}
  结论: o != none ↔ 存在 x, o = some x
  证明: by
  constructor
  · rw [Ne, eq_none_iff', not_not]
    exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
  · rintro ⟨x, rfl⟩
    apply some_ne_none

Depends on / 依赖: eq_none_iff, eq_some_iff, get_mem, not_not, o.get, some_ne_none
-/
theorem ne_none_iff {o : Part α} : o != none ↔ exists x, o = some x := by
  constructor
  · rw [Ne, eq_none_iff', not_not]
    exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
  · rintro ⟨x, rfl⟩
    apply some_ne_none

/--
theorem `eq_none_or_eq_some` / 定理 `eq_none_or_eq_some`

English:
theorem eq_none_or_eq_some
  given: (o : Part α)
  statement: o = none ∨ exists x, o = some x
  proof: or_iff_not_imp_left.2 ne_none_iff.1

中文:
定理 eq_none_or_eq_some
  条件: (o : Part α)
  结论: o = none ∨ 存在 x, o = some x
  证明: or_iff_not_imp_left.2 ne_none_iff.1

Depends on / 依赖: ne_none_iff, or_iff_not_imp_left
-/
theorem eq_none_or_eq_some (o : Part α) : o = none ∨ exists x, o = some x :=
  or_iff_not_imp_left.2 ne_none_iff.1

/--
theorem `some_injective` / 定理 `some_injective`

English:
theorem some_injective
  statement: Injective (@Part.some α)
  proof: fun _ _ h =>
  congr_fun (eq_of_heq (Part.mk.inj h).2) trivial

@[simp]

中文:
定理 some_injective
  结论: 单射 (@Part.some α)
  证明: fun _ _ h =>
  congr_fun (eq_of_heq (Part.mk.inj h).2) trivial

@[simp]
-/
theorem some_injective : Injective (@Part.some α) := fun _ _ h =>
  congr_fun (eq_of_heq (Part.mk.inj h).2) trivial

@[simp]
/--
theorem `some_inj` / 定理 `some_inj`

English:
theorem some_inj
  given: {a b : α}
  statement: Part.some a = some b ↔ a = b
  proof: some_injective.eq_iff

@[simp]

中文:
定理 some_inj
  条件: {a b : α}
  结论: Part.some a = some b ↔ a = b
  证明: some_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, some_injective, some_injective.eq_iff
-/
theorem some_inj {a b : α} : Part.some a = some b ↔ a = b :=
  some_injective.eq_iff

@[simp]
/--
theorem `some_get` / 定理 `some_get`

English:
theorem some_get
  given: {a : Part α} (ha : a.Dom)
  statement: Part.some (Part.get a ha) = a
  proof: Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

中文:
定理 some_get
  条件: {a : Part α} (ha : a.Dom)
  结论: Part.some (Part.get a ha) = a
  证明: Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

Depends on / 依赖: Eq.symm, eq_some_iff
-/
theorem some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get a ha) = a :=
  Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

/--
theorem `get_eq_iff_eq_some` / 定理 `get_eq_iff_eq_some`

English:
theorem get_eq_iff_eq_some
  given: {a : Part α} {ha : a.Dom} {b : α}
  statement: a.get ha = b ↔ a = some b
  proof: ⟨fun h => by simp [h.symm], fun h => by simp [h]⟩

中文:
定理 get_eq_iff_eq_some
  条件: {a : Part α} {ha : a.Dom} {b : α}
  结论: a.get ha = b ↔ a = some b
  证明: ⟨fun h => by simp [h.symm], fun h => by simp [h]⟩

Depends on / 依赖: h.symm
-/
theorem get_eq_iff_eq_some {a : Part α} {ha : a.Dom} {b : α} : a.get ha = b ↔ a = some b :=
  ⟨fun h => by simp [h.symm], fun h => by simp [h]⟩

/--
theorem `get_eq_get_of_eq` / 定理 `get_eq_get_of_eq`

English:
theorem get_eq_get_of_eq
  given: (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b)
  proof: by
  congr

中文:
定理 get_eq_get_of_eq
  条件: (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b)
  证明: by
  congr
-/
theorem get_eq_get_of_eq (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b) :
    a.get ha = b.get (h ▸ ha) := by
  congr

/--
theorem `get_eq_iff_mem` / 定理 `get_eq_iff_mem`

English:
theorem get_eq_iff_mem
  given: {o : Part α} {a : α} (h : o.Dom)
  statement: o.get h = a ↔ a in o
  proof: ⟨fun H => ⟨h, H⟩, fun ⟨_, H⟩ => H⟩

中文:
定理 get_eq_iff_mem
  条件: {o : Part α} {a : α} (h : o.Dom)
  结论: o.get h = a ↔ a in o
  证明: ⟨fun H => ⟨h, H⟩, fun ⟨_, H⟩ => H⟩
-/
theorem get_eq_iff_mem {o : Part α} {a : α} (h : o.Dom) : o.get h = a ↔ a in o :=
  ⟨fun H => ⟨h, H⟩, fun ⟨_, H⟩ => H⟩

/--
theorem `eq_get_iff_mem` / 定理 `eq_get_iff_mem`

English:
theorem eq_get_iff_mem
  given: {o : Part α} {a : α} (h : o.Dom)
  statement: a = o.get h ↔ a in o
  proof: eq_comm.trans (get_eq_iff_mem h)

中文:
定理 eq_get_iff_mem
  条件: {o : Part α} {a : α} (h : o.Dom)
  结论: a = o.get h ↔ a in o
  证明: eq_comm.trans (get_eq_iff_mem h)

Depends on / 依赖: eq_comm, eq_comm.trans, get_eq_iff_mem
-/
theorem eq_get_iff_mem {o : Part α} {a : α} (h : o.Dom) : a = o.get h ↔ a in o :=
  eq_comm.trans (get_eq_iff_mem h)

/--
theorem `eq_of_get_eq_get` / 定理 `eq_of_get_eq_get`

English:
theorem eq_of_get_eq_get
  given: {a b : Part α} (ha : a.Dom) (hb : b.Dom) (hab : a.get ha = b.get hb)
  proof: ext' (iff_of_true ha hb) fun _ _ => hab

中文:
定理 eq_of_get_eq_get
  条件: {a b : Part α} (ha : a.Dom) (hb : b.Dom) (hab : a.get ha = b.get hb)
  证明: ext' (iff_of_true ha hb) fun _ _ => hab

Depends on / 依赖: iff_of_true
-/
theorem eq_of_get_eq_get {a b : Part α} (ha : a.Dom) (hb : b.Dom) (hab : a.get ha = b.get hb) :
    a = b :=
  ext' (iff_of_true ha hb) fun _ _ => hab

/--
theorem `eq_iff_of_dom` / 定理 `eq_iff_of_dom`

English:
theorem eq_iff_of_dom
  given: {a b : Part α} (ha : a.Dom) (hb : b.Dom)
  statement: a.get ha = b.get hb ↔ a = b
  proof: ⟨eq_of_get_eq_get ha hb, get_eq_get_of_eq a ha⟩

中文:
定理 eq_iff_of_dom
  条件: {a b : Part α} (ha : a.Dom) (hb : b.Dom)
  结论: a.get ha = b.get hb ↔ a = b
  证明: ⟨eq_of_get_eq_get ha hb, get_eq_get_of_eq a ha⟩

Depends on / 依赖: eq_of_get_eq_get, get_eq_get_of_eq
-/
theorem eq_iff_of_dom {a b : Part α} (ha : a.Dom) (hb : b.Dom) : a.get ha = b.get hb ↔ a = b :=
  ⟨eq_of_get_eq_get ha hb, get_eq_get_of_eq a ha⟩

/--
theorem `eq_of_mem` / 定理 `eq_of_mem`

English:
theorem eq_of_mem
  given: {a b : Part α} (ha : a.Dom) (hb : a.get ha in b)
  statement: a = b
  proof: by
  have hb' : b.Dom := Part.dom_iff_mem.mpr ⟨a.get ha, hb⟩
  rwa [← eq_get_iff_mem hb', eq_iff_of_dom ha hb'] at hb

@[simp]

中文:
定理 eq_of_mem
  条件: {a b : Part α} (ha : a.Dom) (hb : a.get ha in b)
  结论: a = b
  证明: by
  have hb' : b.Dom := Part.dom_iff_mem.mpr ⟨a.get ha, hb⟩
  rwa [← eq_get_iff_mem hb', eq_iff_of_dom ha hb'] at hb

@[simp]

Depends on / 依赖: Part.dom_iff_mem.mpr, a.get, b.Dom, dom_iff_mem, eq_get_iff_mem, eq_iff_of_dom
-/
theorem eq_of_mem {a b : Part α} (ha : a.Dom) (hb : a.get ha in b) : a = b := by
  have hb' : b.Dom := Part.dom_iff_mem.mpr ⟨a.get ha, hb⟩
  rwa [← eq_get_iff_mem hb', eq_iff_of_dom ha hb'] at hb

@[simp]
/--
theorem `none_toOption` / 定理 `none_toOption`

English:
theorem none_toOption
  given: [Decidable (@none α).Dom]
  statement: (none : Part α).toOption = Option.none
  proof: dif_neg id

@[simp]

中文:
定理 none_toOption
  条件: [可判定 (@none α).Dom]
  结论: (none : Part α).toOption = 选项类型.none
  证明: dif_neg id

@[simp]

Depends on / 依赖: dif_neg
-/
theorem none_toOption [Decidable (@none α).Dom] : (none : Part α).toOption = Option.none :=
  dif_neg id

@[simp]
/--
theorem `some_toOption` / 定理 `some_toOption`

English:
theorem some_toOption
  given: (a : α) [Decidable (some a).Dom]
  statement: (some a).toOption = Option.some a
  proof: dif_pos trivial

中文:
定理 some_toOption
  条件: (a : α) [可判定 (some a).Dom]
  结论: (some a).toOption = 选项类型.some a
  证明: dif_pos trivial

Depends on / 依赖: dif_pos
-/
theorem some_toOption (a : α) [Decidable (some a).Dom] : (some a).toOption = Option.some a :=
  dif_pos trivial

/--
Instance `noneDecidable` / 实例 `noneDecidable`

English:
instance noneDecidable
  signature: : Decidable (@none α).Dom
  body: instDecidableFalse

中文:
实例 noneDecidable
  签名: : 可判定 (@none α).Dom
  定义体: instDecidableFalse

Depends on / 依赖: instDecidableFalse
-/
instance noneDecidable : Decidable (@none α).Dom :=
  instDecidableFalse

/--
Instance `someDecidable` / 实例 `someDecidable`

English:
instance someDecidable
  signature: (a : α)
  body: instDecidableTrue

中文:
实例 someDecidable
  签名: (a : α)
  定义体: instDecidableTrue

Depends on / 依赖: instDecidableTrue
-/
instance someDecidable (a : α) : Decidable (some a).Dom :=
  instDecidableTrue

/--
Definition of `getOrElse` / `getOrElse` 的定义

English:
definition getOrElse
  signature: (a : Part α) [Decidable a.Dom] (d : α)
  body: if ha : a.Dom then a.get ha else d

中文:
定义 getOrElse
  签名: (a : Part α) [可判定 a.Dom] (d : α)
  定义体: if ha : a.Dom then a.get ha else d

Depends on / 依赖: a.Dom, a.get
-/
def getOrElse (a : Part α) [Decidable a.Dom] (d : α) :=
  if ha : a.Dom then a.get ha else d

/--
theorem `getOrElse_of_dom` / 定理 `getOrElse_of_dom`

English:
theorem getOrElse_of_dom
  given: (a : Part α) (h : a.Dom) [Decidable a.Dom] (d : α)
  proof: dif_pos h

中文:
定理 getOrElse_of_dom
  条件: (a : Part α) (h : a.Dom) [可判定 a.Dom] (d : α)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
theorem getOrElse_of_dom (a : Part α) (h : a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = a.get h :=
  dif_pos h

/--
theorem `getOrElse_of_not_dom` / 定理 `getOrElse_of_not_dom`

English:
theorem getOrElse_of_not_dom
  given: (a : Part α) (h : ¬a.Dom) [Decidable a.Dom] (d : α)
  proof: dif_neg h

@[simp]

中文:
定理 getOrElse_of_not_dom
  条件: (a : Part α) (h : ¬a.Dom) [可判定 a.Dom] (d : α)
  证明: dif_neg h

@[simp]

Depends on / 依赖: dif_neg
-/
theorem getOrElse_of_not_dom (a : Part α) (h : ¬a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = d :=
  dif_neg h

@[simp]
/--
theorem `getOrElse_none` / 定理 `getOrElse_none`

English:
theorem getOrElse_none
  given: (d : α) [Decidable (none : Part α).Dom]
  statement: getOrElse none d = d
  proof: none.getOrElse_of_not_dom not_none_dom d

@[simp]

中文:
定理 getOrElse_none
  条件: (d : α) [可判定 (none : Part α).Dom]
  结论: getOrElse none d = d
  证明: none.getOrElse_of_not_dom not_none_dom d

@[simp]

Depends on / 依赖: getOrElse_of_not_dom, none.getOrElse_of_not_dom, not_none_dom
-/
theorem getOrElse_none (d : α) [Decidable (none : Part α).Dom] : getOrElse none d = d :=
  none.getOrElse_of_not_dom not_none_dom d

@[simp]
/--
theorem `getOrElse_some` / 定理 `getOrElse_some`

English:
theorem getOrElse_some
  given: (a : α) (d : α) [Decidable (some a).Dom]
  statement: getOrElse (some a) d = a
  proof: (some a).getOrElse_of_dom (some_dom a) d

中文:
定理 getOrElse_some
  条件: (a : α) (d : α) [可判定 (some a).Dom]
  结论: getOrElse (some a) d = a
  证明: (some a).getOrElse_of_dom (some_dom a) d

Depends on / 依赖: getOrElse_of_dom, some_dom
-/
theorem getOrElse_some (a : α) (d : α) [Decidable (some a).Dom] : getOrElse (some a) d = a :=
  (some a).getOrElse_of_dom (some_dom a) d

-- `simp`-normal form is `toOption_eq_some_iff`.
/--
theorem `mem_toOption` / 定理 `mem_toOption`

English:
theorem mem_toOption
  given: {o : Part α} [Decidable o.Dom] {a : α}
  statement: a in toOption o ↔ a in o
  proof: by
  unfold toOption
  by_cases h : o.Dom
  · simpa [h] using ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  · simp only [h, ↓reduceDIte, Option.mem_def, reduceCtorEq, false_iff]
    exact mt Exists.fst h

@[simp]

中文:
定理 mem_toOption
  条件: {o : Part α} [可判定 o.Dom] {a : α}
  结论: a in toOption o ↔ a in o
  证明: by
  unfold toOption
  by_cases h : o.Dom
  · simpa [h] using ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  · simp only [h, ↓reduceDIte, Option.mem_def, reduceCtorEq, false_iff]
    exact mt Exists.fst h

@[simp]

Depends on / 依赖: Exists, Exists.fst, Option.mem_def, false_iff, mem_def, o.Dom, reduceCtorEq, reduceDIte, toOption
-/
theorem mem_toOption {o : Part α} [Decidable o.Dom] {a : α} : a in toOption o ↔ a in o := by
  unfold toOption
  by_cases h : o.Dom
  · simpa [h] using ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  · simp only [h, ↓reduceDIte, Option.mem_def, reduceCtorEq, false_iff]
    exact mt Exists.fst h

@[simp]
/--
theorem `toOption_eq_some_iff` / 定理 `toOption_eq_some_iff`

English:
theorem toOption_eq_some_iff
  given: {o : Part α} [Decidable o.Dom] {a : α}
  proof: by
  rw [← Option.mem_def]; rw [mem_toOption]

中文:
定理 toOption_eq_some_iff
  条件: {o : Part α} [可判定 o.Dom] {a : α}
  证明: by
  rw [← Option.mem_def]; rw [mem_toOption]

Depends on / 依赖: Option.mem_def, mem_def, mem_toOption
-/
theorem toOption_eq_some_iff {o : Part α} [Decidable o.Dom] {a : α} :
    toOption o = Option.some a ↔ a in o := by
  rw [← Option.mem_def]; rw [mem_toOption]

/--
theorem `Dom.toOption` / 定理 `Dom.toOption`

English:
theorem Dom.toOption
  given: {o : Part α} [Decidable o.Dom] (h : o.Dom)
  statement: o.toOption = o.get h
  proof: dif_pos h

中文:
定理 Dom.toOption
  条件: {o : Part α} [可判定 o.Dom] (h : o.Dom)
  结论: o.toOption = o.get h
  证明: dif_pos h
-/
protected theorem Dom.toOption {o : Part α} [Decidable o.Dom] (h : o.Dom) : o.toOption = o.get h :=
  dif_pos h

/--
theorem `toOption_eq_none_iff` / 定理 `toOption_eq_none_iff`

English:
theorem toOption_eq_none_iff
  given: {a : Part α} [Decidable a.Dom]
  statement: a.toOption = Option.none ↔ ¬a.Dom
  proof: Ne.dite_eq_right_iff fun _ => Option.some_ne_none _

@[simp]

中文:
定理 toOption_eq_none_iff
  条件: {a : Part α} [可判定 a.Dom]
  结论: a.toOption = 选项类型.none ↔ ¬a.Dom
  证明: Ne.dite_eq_right_iff fun _ => Option.some_ne_none _

@[simp]

Depends on / 依赖: Ne.dite_eq_right_iff, Option.some_ne_none, dite_eq_right_iff, some_ne_none
-/
theorem toOption_eq_none_iff {a : Part α} [Decidable a.Dom] : a.toOption = Option.none ↔ ¬a.Dom :=
  Ne.dite_eq_right_iff fun _ => Option.some_ne_none _

@[simp]
/--
theorem `elim_toOption` / 定理 `elim_toOption`

English:
theorem elim_toOption
  given: {α β : Type*} (a : Part α) [Decidable a.Dom] (b : β) (f : α -> β)
  proof: by
  split_ifs with h
  · rw [h.toOption]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    rfl

中文:
定理 elim_toOption
  条件: {α β : 类型} (a : Part α) [可判定 a.Dom] (b : β) (f : α -> β)
  证明: by
  split_ifs with h
  · rw [h.toOption]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    rfl

Depends on / 依赖: Part.toOption_eq_none_iff, h.toOption, split_ifs, toOption, toOption_eq_none_iff
-/
theorem elim_toOption {α β : Type*} (a : Part α) [Decidable a.Dom] (b : β) (f : α -> β) :
    a.toOption.elim b f = if h : a.Dom then f (a.get h) else b := by
  split_ifs with h
  · rw [h.toOption]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    rfl

/-- Converts an `Option α` into a `Part α`. -/
@[coe]
/--
Definition of `ofOption` / `ofOption` 的定义

English:
definition ofOption
  signature: : Option α -> Part α

中文:
定义 ofOption
  签名: : 选项类型 α -> Part α
-/
def ofOption : Option α -> Part α
  | Option.none => none
  | Option.some a => some a

@[simp]
/--
theorem `mem_ofOption` / 定理 `mem_ofOption`

English:
theorem mem_ofOption
  given: {a : α}
  statement: forall {o : Option α}, a in ofOption o ↔ a in o

中文:
定理 mem_ofOption
  条件: {a : α}
  结论: 对任意 {o : 选项类型 α}, a in ofOption o ↔ a in o

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, RatFunc, RatFunc.induction_on, RatFunc.mk, RingHom, RingHom.coe_mk, algebraMap, coe_mk, induction_on, map_add, map_mul, map_one, map_zero, mk_def_of_ne, mk_one, mk_smul, ofFractionRing_add
-/
theorem mem_ofOption {a : α} : forall {o : Option α}, a in ofOption o ↔ a in o
  | Option.none => ⟨fun h => h.fst.elim, fun h => Option.noConfusion rfl (heq_of_eq h)⟩
  | Option.some _ => ⟨fun h => congr_arg Option.some h.snd, fun h => ⟨trivial, Option.some.inj h⟩⟩

@[simp]
/--
theorem `ofOption_dom` / 定理 `ofOption_dom`

English:
theorem ofOption_dom
  given: {α}
  statement: forall o : Option α, (ofOption o).Dom ↔ o.isSome

中文:
定理 ofOption_dom
  条件: {α}
  结论: 对任意 o : 选项类型 α, (ofOption o).Dom ↔ o.isSome
-/
theorem ofOption_dom {α} : forall o : Option α, (ofOption o).Dom ↔ o.isSome
  | Option.none => by simp [ofOption, none]
  | Option.some a => by simp [ofOption]

/--
theorem `ofOption_eq_get` / 定理 `ofOption_eq_get`

English:
theorem ofOption_eq_get
  given: {α} (o : Option α)
  statement: ofOption o = ⟨_, @Option.get _ o⟩
  proof: Part.ext' (ofOption_dom o) fun h₁ h₂ => by
    cases o
    · simp at h₂
    · rfl

中文:
定理 ofOption_eq_get
  条件: {α} (o : 选项类型 α)
  结论: ofOption o = ⟨_, @选项类型.get _ o⟩
  证明: Part.ext' (ofOption_dom o) fun h₁ h₂ => by
    cases o
    · simp at h₂
    · rfl

Depends on / 依赖: Part.ext, ofOption_dom
-/
theorem ofOption_eq_get {α} (o : Option α) : ofOption o = ⟨_, @Option.get _ o⟩ :=
  Part.ext' (ofOption_dom o) fun h₁ h₂ => by
    cases o
    · simp at h₂
    · rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Option α) (Part α)
  body: ⟨ofOption⟩

中文:
实例 :
  签名: Coe (选项类型 α) (Part α)
  定义体: ⟨ofOption⟩

Depends on / 依赖: ofOption
-/
instance : Coe (Option α) (Part α) :=
  ⟨ofOption⟩

/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {a : α} {o : Option α}
  statement: a in (o : Part α) ↔ a in o
  proof: mem_ofOption

@[simp]

中文:
定理 mem_coe
  条件: {a : α} {o : 选项类型 α}
  结论: a in (o : Part α) ↔ a in o
  证明: mem_ofOption

@[simp]

Depends on / 依赖: mem_ofOption
-/
theorem mem_coe {a : α} {o : Option α} : a in (o : Part α) ↔ a in o :=
  mem_ofOption

@[simp]
/--
theorem `coe_none` / 定理 `coe_none`

English:
theorem coe_none
  statement: (@Option.none α : Part α) = none
  proof: rfl

@[simp]

中文:
定理 coe_none
  结论: (@选项类型.none α : Part α) = none
  证明: rfl

@[simp]
-/
theorem coe_none : (@Option.none α : Part α) = none :=
  rfl

@[simp]
/--
theorem `coe_some` / 定理 `coe_some`

English:
theorem coe_some
  given: (a : α)
  statement: (Option.some a : Part α) = some a
  proof: rfl

@[elab_as_elim]

中文:
定理 coe_some
  条件: (a : α)
  结论: (选项类型.some a : Part α) = some a
  证明: rfl

@[elab_as_elim]
-/
theorem coe_some (a : α) : (Option.some a : Part α) = some a :=
  rfl

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {P : Part α -> Prop} (a : Part α) (hnone : P none)
  proof: (Classical.em a.Dom).elim (fun h => Part.some_get h ▸ hsome _) fun h =>
    (eq_none_iff'.2 h).symm ▸ hnone

中文:
定理 induction_on
  结论: {P : Part α -> 命题} (a : Part α) (hnone : P none)
  证明: (Classical.em a.Dom).elim (fun h => Part.some_get h ▸ hsome _) fun h =>
    (eq_none_iff'.2 h).symm ▸ hnone
-/
protected theorem induction_on {P : Part α -> Prop} (a : Part α) (hnone : P none)
    (hsome : forall a : α, P (some a)) : P a :=
  (Classical.em a.Dom).elim (fun h => Part.some_get h ▸ hsome _) fun h =>
    (eq_none_iff'.2 h).symm ▸ hnone

/--
Instance `ofOptionDecidable` / 实例 `ofOptionDecidable`

English:
instance ofOptionDecidable
  signature: : forall o : Option α, Decidable (ofOption o).Dom

中文:
实例 ofOptionDecidable
  签名: : 对任意 o : 选项类型 α, 可判定 (ofOption o).Dom
-/
instance ofOptionDecidable : forall o : Option α, Decidable (ofOption o).Dom
  | Option.none => Part.noneDecidable
  | Option.some a => Part.someDecidable a

@[simp]
/--
theorem `to_ofOption` / 定理 `to_ofOption`

English:
theorem to_ofOption
  given: (o : Option α)
  statement: toOption (ofOption o) = o
  proof: by cases o <;> rfl

@[simp]

中文:
定理 to_ofOption
  条件: (o : 选项类型 α)
  结论: toOption (ofOption o) = o
  证明: by cases o <;> rfl

@[simp]
-/
theorem to_ofOption (o : Option α) : toOption (ofOption o) = o := by cases o <;> rfl

@[simp]
/--
theorem `of_toOption` / 定理 `of_toOption`

English:
theorem of_toOption
  given: (o : Part α) [Decidable o.Dom]
  statement: ofOption (toOption o) = o
  proof: ext fun _ => mem_ofOption.trans mem_toOption

中文:
定理 of_toOption
  条件: (o : Part α) [可判定 o.Dom]
  结论: ofOption (toOption o) = o
  证明: ext fun _ => mem_ofOption.trans mem_toOption

Depends on / 依赖: mem_ofOption, mem_ofOption.trans, mem_toOption
-/
theorem of_toOption (o : Part α) [Decidable o.Dom] : ofOption (toOption o) = o :=
  ext fun _ => mem_ofOption.trans mem_toOption

/--
Definition of `equivOption` / `equivOption` 的定义

English:
definition equivOption
  signature: : Part α ≃ Option α
  body: haveI := Classical.dec
  ⟨fun o => toOption o, ofOption, fun o => of_toOption o, fun o =>
    Eq.trans (by dsimp; congr) (to_ofOption o)⟩

中文:
定义 equivOption
  签名: : Part α ≃ 选项类型 α
  定义体: haveI := Classical.dec
  ⟨fun o => toOption o, ofOption, fun o => of_toOption o, fun o =>
    Eq.trans (by dsimp; congr) (to_ofOption o)⟩

Depends on / 依赖: Classical, Classical.dec, Eq.trans, ofOption, of_toOption, toOption, to_ofOption
-/
noncomputable def equivOption : Part α ≃ Option α :=
  haveI := Classical.dec
  ⟨fun o => toOption o, ofOption, fun o => of_toOption o, fun o =>
    Eq.trans (by dsimp; congr) (to_ofOption o)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Part
  body: forall i, i in x -> i in y
  le_refl _ _ := id
  le_trans _ _ _ f g _ := g _ ∘ f _
  le_antisymm _ _ f g := Part.ext fun _ => ⟨f _, g _⟩

中文:
实例 :
  签名: 偏序 (Part
  定义体: forall i, i in x -> i in y
  le_refl _ _ := id
  le_trans _ _ _ f g _ := g _ ∘ f _
  le_antisymm _ _ f g := Part.ext fun _ => ⟨f _, g _⟩
-/
instance : PartialOrder (Part
        α) where
  le x y := forall i, i in x -> i in y
  le_refl _ _ := id
  le_trans _ _ _ f g _ := g _ ∘ f _
  le_antisymm _ _ f g := Part.ext fun _ => ⟨f _, g _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Part α)
  body: none
  bot_le := by rintro x _ ⟨⟨_⟩, _⟩

中文:
实例 :
  签名: 有底序 (Part α)
  定义体: none
  bot_le := by rintro x _ ⟨⟨_⟩, _⟩
-/
instance : OrderBot (Part α) where
  bot := none
  bot_le := by rintro x _ ⟨⟨_⟩, _⟩

/--
theorem `le_total_of_le_of_le` / 定理 `le_total_of_le_of_le`

English:
theorem le_total_of_le_of_le
  given: {x y : Part α} (z : Part α) (hx : x <= z) (hy : y <= z)
  proof: by
  rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
  · rw [h]
    left
    apply OrderBot.bot_le _
  right; intro b' h₁
  rw [Part.eq_some_iff] at h₀
  have hx := hx _ h₀; have hy := hy _ h₁
  have hx := Part.mem_unique hx hy; subst hx
  exact h₀

中文:
定理 le_total_of_le_of_le
  条件: {x y : Part α} (z : Part α) (hx : x <= z) (hy : y <= z)
  证明: by
  rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
  · rw [h]
    left
    apply OrderBot.bot_le _
  right; intro b' h₁
  rw [Part.eq_some_iff] at h₀
  have hx := hx _ h₀; have hy := hy _ h₁
  have hx := Part.mem_unique hx hy; subst hx
  exact h₀

Depends on / 依赖: OrderBot, OrderBot.bot_le, Part.eq_none_or_eq_some, Part.eq_some_iff, Part.mem_unique, bot_le, eq_none_or_eq_some, eq_some_iff, mem_unique
-/
theorem le_total_of_le_of_le {x y : Part α} (z : Part α) (hx : x <= z) (hy : y <= z) :
    x <= y ∨ y <= x := by
  rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
  · rw [h]
    left
    apply OrderBot.bot_le _
  right; intro b' h₁
  rw [Part.eq_some_iff] at h₀
  have hx := hx _ h₀; have hy := hy _ h₁
  have hx := Part.mem_unique hx hy; subst hx
  exact h₀

/--
Definition of `assert` / `assert` 的定义

English:
definition assert
  signature: (p : Prop) (f : p -> Part α)
  body: ⟨exists h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩

中文:
定义 assert
  签名: (p : 命题) (f : p -> Part α)
  定义体: ⟨exists h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩

Depends on / 依赖: ha.fst, ha.snd
-/
def assert (p : Prop) (f : p -> Part α) : Part α :=
  ⟨exists h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (f : Part α) (g : α -> Part β)
  body: assert (Dom f) fun b => g (f.get b)

中文:
定义 bind
  签名: (f : Part α) (g : α -> Part β)
  定义体: assert (Dom f) fun b => g (f.get b)
-/
protected def bind (f : Part α) (g : α -> Part β) : Part β :=
  assert (Dom f) fun b => g (f.get b)

/-- The map operation for `Part` just maps the value and maintains the same domain. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (o : Part α)
  body: ⟨o.Dom, f ∘ o.get⟩

中文:
定义 map
  签名: (f : α -> β) (o : Part α)
  定义体: ⟨o.Dom, f ∘ o.get⟩

Depends on / 依赖: o.Dom, o.get
-/
def map (f : α -> β) (o : Part α) : Part β :=
  ⟨o.Dom, f ∘ o.get⟩

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (f : α -> β) {o : Part α}
  statement: forall {a}, a in o -> f a in map f o

中文:
定理 mem_map
  条件: (f : α -> β) {o : Part α}
  结论: 对任意 {a}, a in o -> f a in map f o
-/
theorem mem_map (f : α -> β) {o : Part α} : forall {a}, a in o -> f a in map f o
  | _, ⟨_, rfl⟩ => ⟨_, rfl⟩

@[simp]
/--
theorem `mem_map_iff` / 定理 `mem_map_iff`

English:
theorem mem_map_iff
  given: (f : α -> β) {o : Part α} {b}
  statement: b in map f o ↔ exists a in o, f a = b
  proof: ⟨fun hb => match b, hb with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨_, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩

@[simp]

中文:
定理 mem_map_iff
  条件: (f : α -> β) {o : Part α} {b}
  结论: b in map f o ↔ 存在 a in o, f a = b
  证明: ⟨fun hb => match b, hb with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨_, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩

@[simp]

Depends on / 依赖: mem_map
-/
theorem mem_map_iff (f : α -> β) {o : Part α} {b} : b in map f o ↔ exists a in o, f a = b :=
  ⟨fun hb => match b, hb with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨_, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩

@[simp]
/--
theorem `map_none` / 定理 `map_none`

English:
theorem map_none
  given: (f : α -> β)
  statement: map f none = none
  proof: eq_none_iff.2 fun a => by simp

@[simp]

中文:
定理 map_none
  条件: (f : α -> β)
  结论: map f none = none
  证明: eq_none_iff.2 fun a => by simp

@[simp]

Depends on / 依赖: eq_none_iff
-/
theorem map_none (f : α -> β) : map f none = none :=
  eq_none_iff.2 fun a => by simp

@[simp]
/--
theorem `map_some` / 定理 `map_some`

English:
theorem map_some
  given: (f : α -> β) (a : α)
  statement: map f (some a) = some (f a)
  proof: eq_some_iff.2 mem_map f mem_some _

中文:
定理 map_some
  条件: (f : α -> β) (a : α)
  结论: map f (some a) = some (f a)
  证明: eq_some_iff.2 mem_map f mem_some _

Depends on / 依赖: eq_some_iff, mem_map, mem_some
-/
theorem map_some (f : α -> β) (a : α) : map f (some a) = some (f a) :=
eq_some_iff.2 mem_map f mem_some _

/--
theorem `mem_assert` / 定理 `mem_assert`

English:
theorem mem_assert
  given: {p : Prop} {f : p -> Part α}
  statement: forall {a} (h : p), a in f h -> a in assert p f

中文:
定理 mem_assert
  条件: {p : 命题} {f : p -> Part α}
  结论: 对任意 {a} (h : p), a in f h -> a in assert p f
-/
theorem mem_assert {p : Prop} {f : p -> Part α} : forall {a} (h : p), a in f h -> a in assert p f
  | _, x, ⟨h, rfl⟩ => ⟨⟨x, h⟩, rfl⟩

@[simp, grind =]
/--
theorem `mem_assert_iff` / 定理 `mem_assert_iff`

English:
theorem mem_assert_iff
  given: {p : Prop} {f : p -> Part α} {a}
  statement: a in assert p f ↔ exists h : p, a in f h
  proof: ⟨fun ha => match a, ha with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨_, h⟩ => mem_assert _ h⟩

中文:
定理 mem_assert_iff
  条件: {p : 命题} {f : p -> Part α} {a}
  结论: a in assert p f ↔ 存在 h : p, a in f h
  证明: ⟨fun ha => match a, ha with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨_, h⟩ => mem_assert _ h⟩

Depends on / 依赖: mem_assert
-/
theorem mem_assert_iff {p : Prop} {f : p -> Part α} {a} : a in assert p f ↔ exists h : p, a in f h :=
  ⟨fun ha => match a, ha with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨_, h⟩ => mem_assert _ h⟩

/--
theorem `assert_pos` / 定理 `assert_pos`

English:
theorem assert_pos
  given: {p : Prop} {f : p -> Part α} (h : p)
  statement: assert p f = f h
  proof: by
  ext
  simp_all

中文:
定理 assert_pos
  条件: {p : 命题} {f : p -> Part α} (h : p)
  结论: assert p f = f h
  证明: by
  ext
  simp_all
-/
theorem assert_pos {p : Prop} {f : p -> Part α} (h : p) : assert p f = f h := by
  ext
  simp_all

/--
theorem `assert_neg` / 定理 `assert_neg`

English:
theorem assert_neg
  given: {p : Prop} {f : p -> Part α} (h : ¬p)
  statement: assert p f = none
  proof: by
  ext
  simp_all

中文:
定理 assert_neg
  条件: {p : 命题} {f : p -> Part α} (h : ¬p)
  结论: assert p f = none
  证明: by
  ext
  simp_all
-/
theorem assert_neg {p : Prop} {f : p -> Part α} (h : ¬p) : assert p f = none := by
  ext
  simp_all

/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  given: {f : Part α} {g : α -> Part β}
  statement: forall {a b}, a in f -> b in g a -> b in f.bind g

中文:
定理 mem_bind
  条件: {f : Part α} {g : α -> Part β}
  结论: 对任意 {a b}, a in f -> b in g a -> b in f.bind g
-/
theorem mem_bind {f : Part α} {g : α -> Part β} : forall {a b}, a in f -> b in g a -> b in f.bind g
  | _, _, ⟨h, rfl⟩, ⟨h₂, rfl⟩ => ⟨⟨h, h₂⟩, rfl⟩

@[simp, grind =]
/--
theorem `mem_bind_iff` / 定理 `mem_bind_iff`

English:
theorem mem_bind_iff
  given: {f : Part α} {g : α -> Part β} {b}
  statement: b in f.bind g ↔ exists a in f, b in g a
  proof: ⟨fun hb => match b, hb with
    | _, ⟨⟨_, _⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨_, h₁, h₂⟩ => mem_bind h₁ h₂⟩

中文:
定理 mem_bind_iff
  条件: {f : Part α} {g : α -> Part β} {b}
  结论: b in f.bind g ↔ 存在 a in f, b in g a
  证明: ⟨fun hb => match b, hb with
    | _, ⟨⟨_, _⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨_, h₁, h₂⟩ => mem_bind h₁ h₂⟩

Depends on / 依赖: mem_bind
-/
theorem mem_bind_iff {f : Part α} {g : α -> Part β} {b} : b in f.bind g ↔ exists a in f, b in g a :=
  ⟨fun hb => match b, hb with
    | _, ⟨⟨_, _⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨_, h₁, h₂⟩ => mem_bind h₁ h₂⟩

/--
theorem `bind_eq_some_iff` / 定理 `bind_eq_some_iff`

English:
theorem bind_eq_some_iff
  given: {b : β} {x : Part α} {f : α -> Part β}
  proof: by
  simp only [eq_some_iff, mem_bind_iff]

中文:
定理 bind_eq_some_iff
  条件: {b : β} {x : Part α} {f : α -> Part β}
  证明: by
  simp only [eq_some_iff, mem_bind_iff]

Depends on / 依赖: eq_some_iff, mem_bind_iff
-/
theorem bind_eq_some_iff {b : β} {x : Part α} {f : α -> Part β} :
    x.bind f = some b ↔ exists a, x = some a ∧ f a = some b := by
  simp only [eq_some_iff, mem_bind_iff]

/--
theorem `Dom.bind` / 定理 `Dom.bind`

English:
theorem Dom.bind
  given: {o : Part α} (h : o.Dom) (f : α -> Part β)
  statement: o.bind f = f (o.get h)
  proof: by
  ext b
  simp only [Part.mem_bind_iff]
  refine ⟨?_, fun hb => ⟨o.get h, Part.get_mem _, hb⟩⟩
  rintro ⟨a, ha, hb⟩
  rwa [Part.get_eq_of_mem ha]

中文:
定理 Dom.bind
  条件: {o : Part α} (h : o.Dom) (f : α -> Part β)
  结论: o.bind f = f (o.get h)
  证明: by
  ext b
  simp only [Part.mem_bind_iff]
  refine ⟨?_, fun hb => ⟨o.get h, Part.get_mem _, hb⟩⟩
  rintro ⟨a, ha, hb⟩
  rwa [Part.get_eq_of_mem ha]
-/
protected theorem Dom.bind {o : Part α} (h : o.Dom) (f : α -> Part β) : o.bind f = f (o.get h) := by
  ext b
  simp only [Part.mem_bind_iff]
  refine ⟨?_, fun hb => ⟨o.get h, Part.get_mem _, hb⟩⟩
  rintro ⟨a, ha, hb⟩
  rwa [Part.get_eq_of_mem ha]

/--
theorem `Dom.of_bind` / 定理 `Dom.of_bind`

English:
theorem Dom.of_bind
  given: {f : α -> Part β} {a : Part α} (h : (a.bind f).Dom)
  statement: a.Dom
  proof: h.1

@[simp]

中文:
定理 Dom.of_bind
  条件: {f : α -> Part β} {a : Part α} (h : (a.bind f).Dom)
  结论: a.Dom
  证明: h.1

@[simp]
-/
theorem Dom.of_bind {f : α -> Part β} {a : Part α} (h : (a.bind f).Dom) : a.Dom :=
  h.1

@[simp]
/--
theorem `bind_none` / 定理 `bind_none`

English:
theorem bind_none
  given: (f : α -> Part β)
  statement: none.bind f = none
  proof: eq_none_iff.2 fun a => by simp

@[simp]

中文:
定理 bind_none
  条件: (f : α -> Part β)
  结论: none.bind f = none
  证明: eq_none_iff.2 fun a => by simp

@[simp]

Depends on / 依赖: eq_none_iff
-/
theorem bind_none (f : α -> Part β) : none.bind f = none :=
  eq_none_iff.2 fun a => by simp

@[simp]
/--
theorem `bind_some` / 定理 `bind_some`

English:
theorem bind_some
  given: (a : α) (f : α -> Part β)
  statement: (some a).bind f = f a
  proof: ext by simp

中文:
定理 bind_some
  条件: (a : α) (f : α -> Part β)
  结论: (some a).bind f = f a
  证明: ext by simp
-/
theorem bind_some (a : α) (f : α -> Part β) : (some a).bind f = f a :=
ext by simp

/--
theorem `bind_of_mem` / 定理 `bind_of_mem`

English:
theorem bind_of_mem
  given: {o : Part α} {a : α} (h : a in o) (f : α -> Part β)
  statement: o.bind f = f a
  proof: by
  rw [eq_some_iff.2 h]; rw [bind_some]

中文:
定理 bind_of_mem
  条件: {o : Part α} {a : α} (h : a in o) (f : α -> Part β)
  结论: o.bind f = f a
  证明: by
  rw [eq_some_iff.2 h]; rw [bind_some]

Depends on / 依赖: bind_some, eq_some_iff
-/
theorem bind_of_mem {o : Part α} {a : α} (h : a in o) (f : α -> Part β) : o.bind f = f a := by
  rw [eq_some_iff.2 h]; rw [bind_some]

/--
theorem `bind_some_eq_map` / 定理 `bind_some_eq_map`

English:
theorem bind_some_eq_map
  given: (f : α -> β) (x : Part α)
  statement: x.bind (fun y => some (f y)) = map f x
  proof: ext by simp [eq_comm]

中文:
定理 bind_some_eq_map
  条件: (f : α -> β) (x : Part α)
  结论: x.bind (fun y => some (f y)) = map f x
  证明: ext by simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem bind_some_eq_map (f : α -> β) (x : Part α) : x.bind (fun y => some (f y)) = map f x :=
ext by simp [eq_comm]

/--
theorem `bind_toOption` / 定理 `bind_toOption`

English:
theorem bind_toOption
  statement: (f : α -> Part β) (o : Part α) [Decidable o.Dom] [forall a, Decidable (f a).Dom]
  proof: by
  by_cases h : o.Dom
  · simp_rw [h.toOption, h.bind]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    exact Part.toOption_eq_none_iff.2 fun ho => h ho.of_bind

中文:
定理 bind_toOption
  结论: (f : α -> Part β) (o : Part α) [可判定 o.Dom] [对任意 a, 可判定 (f a).Dom]
  证明: by
  by_cases h : o.Dom
  · simp_rw [h.toOption, h.bind]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    exact Part.toOption_eq_none_iff.2 fun ho => h ho.of_bind

Depends on / 依赖: Part.toOption_eq_none_iff, h.bind, h.toOption, ho.of_bind, o.Dom, of_bind, simp_rw, toOption, toOption_eq_none_iff
-/
theorem bind_toOption (f : α -> Part β) (o : Part α) [Decidable o.Dom] [forall a, Decidable (f a).Dom]
    [Decidable (o.bind f).Dom] :
    (o.bind f).toOption = o.toOption.elim Option.none fun a => (f a).toOption := by
  by_cases h : o.Dom
  · simp_rw [h.toOption, h.bind]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    exact Part.toOption_eq_none_iff.2 fun ho => h ho.of_bind

/--
theorem `bind_assoc` / 定理 `bind_assoc`

English:
theorem bind_assoc
  given: {γ} (f : Part α) (g : α -> Part β) (k : β -> Part γ)
  proof: ext fun a => by
    simp only [mem_bind_iff]
    exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩,
           fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp]

中文:
定理 bind_assoc
  条件: {γ} (f : Part α) (g : α -> Part β) (k : β -> Part γ)
  证明: ext fun a => by
    simp only [mem_bind_iff]
    exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩,
           fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp]

Depends on / 依赖: mem_bind_iff
-/
theorem bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β -> Part γ) :
    (f.bind g).bind k = f.bind fun x => (g x).bind k :=
  ext fun a => by
    simp only [mem_bind_iff]
    exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩,
           fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp]
/--
theorem `bind_map` / 定理 `bind_map`

English:
theorem bind_map
  given: {γ} (f : α -> β) (x) (g : β -> Part γ)
  proof: by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp]

中文:
定理 bind_map
  条件: {γ} (f : α -> β) (x) (g : β -> Part γ)
  证明: by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp]

Depends on / 依赖: bind_assoc, bind_some_eq_map
-/
theorem bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) :
    (map f x).bind g = x.bind fun y => g (f y) := by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp]
/--
theorem `map_bind` / 定理 `map_bind`

English:
theorem map_bind
  given: {γ} (f : α -> Part β) (x : Part α) (g : β -> γ)
  proof: by
  rw [← bind_some_eq_map]; rw [bind_assoc]; simp [bind_some_eq_map]

中文:
定理 map_bind
  条件: {γ} (f : α -> Part β) (x : Part α) (g : β -> γ)
  证明: by
  rw [← bind_some_eq_map]; rw [bind_assoc]; simp [bind_some_eq_map]

Depends on / 依赖: bind_assoc, bind_some_eq_map
-/
theorem map_bind {γ} (f : α -> Part β) (x : Part α) (g : β -> γ) :
    map g (x.bind f) = x.bind fun y => map g (f y) := by
  rw [← bind_some_eq_map]; rw [bind_assoc]; simp [bind_some_eq_map]

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> γ) (f : α -> β) (o : Part α)
  statement: map g (map f o) = map (g ∘ f) o
  proof: by
  simp [map, Function.comp_assoc]

中文:
定理 map_map
  条件: (g : β -> γ) (f : α -> β) (o : Part α)
  结论: map g (map f o) = map (g ∘ f) o
  证明: by
  simp [map, Function.comp_assoc]

Depends on / 依赖: Function, Function.comp_assoc, IsScalarTower, IsScalarTower.to, comp_assoc
-/
theorem map_map (g : β -> γ) (f : α -> β) (o : Part α) : map g (map f o) = map (g ∘ f) o := by
  simp [map, Function.comp_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad Part
  body: @some
  map := @map
  bind := @Part.bind

中文:
实例 :
  签名: 单子 Part
  定义体: @some
  map := @map
  bind := @Part.bind

Depends on / 依赖: IsScalarTower, IsScalarTower.to
-/
instance : Monad Part where
  pure := @some
  map := @map
  bind := @Part.bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad
  body: @bind_some_eq_map
  id_map f := by cases f; rfl
  pure_bind := @bind_some
  bind_assoc := @bind_assoc
  map_const := by simp [Functor.mapConst, Functor.map]
  --Porting TODO : In Lean3 these were automatic by a tactic
  seqLeft_eq x y := ext'
    (by simp [SeqLeft.seqLeft, Part.bind, assert, Seq.seq

中文:
实例 :
  签名: 合法单子
  定义体: @bind_some_eq_map
  id_map f := by cases f; rfl
  pure_bind := @bind_some
  bind_assoc := @bind_assoc
  map_const := by simp [Functor.mapConst, Functor.map]
  --Porting TODO : In Lean3 these were automatic by a tactic
  seqLeft_eq x y := ext'
    (by simp [SeqLeft.seqLeft, Part.bind, assert, Seq.seq

Depends on / 依赖: Algebra, Algebra.smul_def, RatFunc, RatFunc.induction_on, bind_some_eq_map, induction_on, simp_rw, smul_assoc, smul_def, smul_right_inj
-/
instance : LawfulMonad
      Part where
  bind_pure_comp := @bind_some_eq_map
  id_map f := by cases f; rfl
  pure_bind := @bind_some
  bind_assoc := @bind_assoc
  map_const := by simp [Functor.mapConst, Functor.map]
  --Porting TODO : In Lean3 these were automatic by a tactic
  seqLeft_eq x y := ext'
    (by simp [SeqLeft.seqLeft, Part.bind, assert, Seq.seq, (· <$> ·), and_comm])
    (fun _ _ => rfl)
  seqRight_eq x y := ext'
    (by simp [SeqRight.seqRight, Part.bind, assert, Seq.seq, (· <$> ·)])
    (fun _ _ => rfl)
  pure_seq x y := ext'
    (by simp [Seq.seq, Part.bind, assert, (· <$> ·), pure])
    (fun _ _ => rfl)
  bind_map x y := ext'
    (by simp [(· >>= ·), Part.bind, assert, Seq.seq, (· <$> ·)])
    (fun _ _ => rfl)

/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: {f : α -> α} (H : forall x : α, f x = x) (o)
  statement: map f o = o
  proof: by
  rw [show f = id from funext H]; exact id_map o

@[simp]

中文:
定理 map_id'
  条件: {f : α -> α} (H : 对任意 x : α, f x = x) (o)
  结论: map f o = o
  证明: by
  rw [show f = id from funext H]; exact id_map o

@[simp]

Depends on / 依赖: id_map
-/
theorem map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map f o = o := by
  rw [show f = id from funext H]; exact id_map o

@[simp]
/--
theorem `bind_some_right` / 定理 `bind_some_right`

English:
theorem bind_some_right
  given: (x : Part α)
  statement: x.bind some = x
  proof: by
  rw [bind_some_eq_map]
  simp [map_id']

@[simp]

中文:
定理 bind_some_right
  条件: (x : Part α)
  结论: x.bind some = x
  证明: by
  rw [bind_some_eq_map]
  simp [map_id']

@[simp]

Depends on / 依赖: bind_some_eq_map, map_id
-/
theorem bind_some_right (x : Part α) : x.bind some = x := by
  rw [bind_some_eq_map]
  simp [map_id']

@[simp]
/--
theorem `pure_eq_some` / 定理 `pure_eq_some`

English:
theorem pure_eq_some
  given: (a : α)
  statement: pure a = some a
  proof: rfl

@[simp]

中文:
定理 pure_eq_some
  条件: (a : α)
  结论: pure a = some a
  证明: rfl

@[simp]
-/
theorem pure_eq_some (a : α) : pure a = some a :=
  rfl

@[simp]
/--
theorem `ret_eq_some` / 定理 `ret_eq_some`

English:
theorem ret_eq_some
  given: (a : α)
  statement: (return a : Part α) = some a
  proof: rfl

@[simp]

中文:
定理 ret_eq_some
  条件: (a : α)
  结论: (return a : Part α) = some a
  证明: rfl

@[simp]
-/
theorem ret_eq_some (a : α) : (return a : Part α) = some a :=
  rfl

@[simp]
/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  given: {α β} (f : α -> β) (o : Part α)
  statement: f < > o = map f o
  proof: rfl

@[simp]

中文:
定理 map_eq_map
  条件: {α β} (f : α -> β) (o : Part α)
  结论: f < > o = map f o
  证明: rfl

@[simp]
-/
theorem map_eq_map {α β} (f : α -> β) (o : Part α) : f < > o = map f o :=
  rfl

@[simp]
/--
theorem `bind_eq_bind` / 定理 `bind_eq_bind`

English:
theorem bind_eq_bind
  given: {α β} (f : Part α) (g : α -> Part β)
  statement: f >>= g = f.bind g
  proof: rfl

中文:
定理 bind_eq_bind
  条件: {α β} (f : Part α) (g : α -> Part β)
  结论: f >>= g = f.bind g
  证明: rfl
-/
theorem bind_eq_bind {α β} (f : Part α) (g : α -> Part β) : f >>= g = f.bind g :=
  rfl

/--
theorem `bind_le` / 定理 `bind_le`

English:
theorem bind_le
  given: {α} (x : Part α) (f : α -> Part β) (y : Part β)
  proof: by
  constructor <;> intro h
  · intro a h' b
    have h := h b
    simp only [and_imp, bind_eq_bind, mem_bind_iff, exists_imp] at h
    apply h _ h'
  · intro b h'
    simp only [bind_eq_bind, mem_bind_iff] at h'
    rcases h' with ⟨a, h₀, h₁⟩
    apply h _ h₀ _ h₁

中文:
定理 bind_le
  条件: {α} (x : Part α) (f : α -> Part β) (y : Part β)
  证明: by
  constructor <;> intro h
  · intro a h' b
    have h := h b
    simp only [and_imp, bind_eq_bind, mem_bind_iff, exists_imp] at h
    apply h _ h'
  · intro b h'
    simp only [bind_eq_bind, mem_bind_iff] at h'
    rcases h' with ⟨a, h₀, h₁⟩
    apply h _ h₀ _ h₁

Depends on / 依赖: and_imp, bind_eq_bind, exists_imp, mem_bind_iff
-/
theorem bind_le {α} (x : Part α) (f : α -> Part β) (y : Part β) :
    x >>= f <= y ↔ forall a, a in x -> f a <= y := by
  constructor <;> intro h
  · intro a h' b
    have h := h b
    simp only [and_imp, bind_eq_bind, mem_bind_iff, exists_imp] at h
    apply h _ h'
  · intro b h'
    simp only [bind_eq_bind, mem_bind_iff] at h'
    rcases h' with ⟨a, h₀, h₁⟩
    apply h _ h₀ _ h₁

-- TODO: if `MonadFail` is defined, define the below instance.
-- instance : MonadFail Part :=
-- { Part.monad with fail := fun _ _ => none }

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (p : Prop) (o : Part α) (H : p -> o.Dom)
  body: ⟨p, fun h => o.get (H h)⟩

@[simp]

中文:
定义 restrict
  签名: (p : 命题) (o : Part α) (H : p -> o.Dom)
  定义体: ⟨p, fun h => o.get (H h)⟩

@[simp]

Depends on / 依赖: o.get
-/
def restrict (p : Prop) (o : Part α) (H : p -> o.Dom) : Part α :=
  ⟨p, fun h => o.get (H h)⟩

@[simp]
/--
theorem `mem_restrict` / 定理 `mem_restrict`

English:
theorem mem_restrict
  given: (p : Prop) (o : Part α) (h : p -> o.Dom) (a : α)
  proof: by
  dsimp [restrict, mem_eq]; constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, ⟨_, h₁⟩⟩
  rintro ⟨h₀, _, h₂⟩; exact ⟨h₀, h₂⟩

中文:
定理 mem_restrict
  条件: (p : 命题) (o : Part α) (h : p -> o.Dom) (a : α)
  证明: by
  dsimp [restrict, mem_eq]; constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, ⟨_, h₁⟩⟩
  rintro ⟨h₀, _, h₂⟩; exact ⟨h₀, h₂⟩

Depends on / 依赖: mem_eq, restrict
-/
theorem mem_restrict (p : Prop) (o : Part α) (h : p -> o.Dom) (a : α) :
    a in restrict p o h ↔ p ∧ a in o := by
  dsimp [restrict, mem_eq]; constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, ⟨_, h₁⟩⟩
  rintro ⟨h₀, _, h₂⟩; exact ⟨h₀, h₂⟩

/-- `unwrap o` gets the value at `o`, ignoring the condition. This function is unsound. -/
unsafe def unwrap (o : Part α) : α :=
  o.get lcProof

/--
theorem `assert_defined` / 定理 `assert_defined`

English:
theorem assert_defined
  given: {p : Prop} {f : p -> Part α}
  statement: forall h : p, (f h).Dom -> (assert p f).Dom
  proof: Exists.intro

中文:
定理 assert_defined
  条件: {p : 命题} {f : p -> Part α}
  结论: 对任意 h : p, (f h).Dom -> (assert p f).Dom
  证明: Exists.intro

Depends on / 依赖: Exists, Exists.intro
-/
theorem assert_defined {p : Prop} {f : p -> Part α} : forall h : p, (f h).Dom -> (assert p f).Dom :=
  Exists.intro

/--
theorem `bind_defined` / 定理 `bind_defined`

English:
theorem bind_defined
  given: {f : Part α} {g : α -> Part β}
  proof: assert_defined

@[simp]

中文:
定理 bind_defined
  条件: {f : Part α} {g : α -> Part β}
  证明: assert_defined

@[simp]

Depends on / 依赖: assert_defined
-/
theorem bind_defined {f : Part α} {g : α -> Part β} :
    forall h : f.Dom, (g (f.get h)).Dom -> (f.bind g).Dom :=
  assert_defined

@[simp]
/--
theorem `bind_dom` / 定理 `bind_dom`

English:
theorem bind_dom
  given: {f : Part α} {g : α -> Part β}
  statement: (f.bind g).Dom ↔ exists h : f.Dom, (g (f.get h)).Dom
  proof: Iff.rfl

中文:
定理 bind_dom
  条件: {f : Part α} {g : α -> Part β}
  结论: (f.bind g).Dom ↔ 存在 h : f.Dom, (g (f.get h)).Dom
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem bind_dom {f : Part α} {g : α -> Part β} : (f.bind g).Dom ↔ exists h : f.Dom, (g (f.get h)).Dom :=
  Iff.rfl

section Instances

/-!
We define several instances for constants and operations on `Part α` inherited from `α`.

This section could be moved to a separate file to avoid the import of
`Mathlib/Algebra/Notation/Defs.lean`.
-/

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One (Part α) where one
  body: pure 1

@[to_additive]

中文:
实例 [幺
  签名: α] : 幺 (Part α) where one
  定义体: pure 1

@[to_additive]
-/
instance [One α] : One (Part α) where one := pure 1

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul (Part α) where mul a b
  body: (· * ·) < > a <*> b

@[to_additive]

中文:
实例 [乘法
  签名: α] : 乘法 (Part α) where mul a b
  定义体: (· * ·) < > a <*> b

@[to_additive]
-/
instance [Mul α] : Mul (Part α) where mul a b := (· * ·) < > a <*> b

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv (Part α) where inv
  body: map Inv.inv

@[to_additive]

中文:
实例 [取逆
  签名: α] : 取逆 (Part α) where inv
  定义体: map Inv.inv

@[to_additive]

Depends on / 依赖: Inv.inv
-/
instance [Inv α] : Inv (Part α) where inv := map Inv.inv

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: α] : Div (Part α) where div a b
  body: (· / ·) < > a <*> b

中文:
实例 [除法
  签名: α] : 除法 (Part α) where div a b
  定义体: (· / ·) < > a <*> b
-/
instance [Div α] : Div (Part α) where div a b := (· / ·) < > a <*> b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mod
  signature: α] : Mod (Part α) where mod a b
  body: (· % ·) < > a <*> b

中文:
实例 [取模
  签名: α] : 取模 (Part α) where mod a b
  定义体: (· % ·) < > a <*> b
-/
instance [Mod α] : Mod (Part α) where mod a b := (· % ·) < > a <*> b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Append
  signature: α] : Append (Part α) where append a b
  body: (· ++ ·) < > a <*> b

中文:
实例 [Append
  签名: α] : Append (Part α) where append a b
  定义体: (· ++ ·) < > a <*> b
-/
instance [Append α] : Append (Part α) where append a b := (· ++ ·) < > a <*> b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inter
  signature: α] : Inter (Part α) where inter a b
  body: (· inter ·) < > a <*> b

中文:
实例 [交集
  签名: α] : 交集 (Part α) where inter a b
  定义体: (· inter ·) < > a <*> b
-/
instance [Inter α] : Inter (Part α) where inter a b := (· inter ·) < > a <*> b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Union
  signature: α] : Union (Part α) where union a b
  body: (· union ·) < > a <*> b

中文:
实例 [并集
  签名: α] : 并集 (Part α) where union a b
  定义体: (· union ·) < > a <*> b
-/
instance [Union α] : Union (Part α) where union a b := (· union ·) < > a <*> b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SDiff
  signature: α] : SDiff (Part α) where sdiff a b
  body: (· \ ·) < > a <*> b

中文:
实例 [对称差
  签名: α] : 对称差 (Part α) where sdiff a b
  定义体: (· \ ·) < > a <*> b
-/
instance [SDiff α] : SDiff (Part α) where sdiff a b := (· \ ·) < > a <*> b

section

@[to_additive]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: [Mul α] (a b : Part α)
  statement: a * b = bind a fun y => map (y * ·) b
  proof: rfl

@[to_additive]

中文:
定理 mul_def
  条件: [乘法 α] (a b : Part α)
  结论: a * b = bind a fun y => map (y * ·) b
  证明: rfl

@[to_additive]
-/
theorem mul_def [Mul α] (a b : Part α) : a * b = bind a fun y => map (y * ·) b := rfl

@[to_additive]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  given: [One α]
  statement: (1 : Part α) = some 1
  proof: rfl

@[to_additive]

中文:
定理 one_def
  条件: [幺 α]
  结论: (1 : Part α) = some 1
  证明: rfl

@[to_additive]
-/
theorem one_def [One α] : (1 : Part α) = some 1 := rfl

@[to_additive]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: [Inv α] (a : Part α)
  statement: a⁻¹ = Part.map (·⁻¹) a
  proof: rfl

@[to_additive]

中文:
定理 inv_def
  条件: [取逆 α] (a : Part α)
  结论: a⁻¹ = Part.map (·⁻¹) a
  证明: rfl

@[to_additive]
-/
theorem inv_def [Inv α] (a : Part α) : a⁻¹ = Part.map (·⁻¹) a := rfl

@[to_additive]
/--
theorem `div_def` / 定理 `div_def`

English:
theorem div_def
  given: [Div α] (a b : Part α)
  statement: a / b = bind a fun y => map (y / ·) b
  proof: rfl

中文:
定理 div_def
  条件: [除法 α] (a b : Part α)
  结论: a / b = bind a fun y => map (y / ·) b
  证明: rfl
-/
theorem div_def [Div α] (a b : Part α) : a / b = bind a fun y => map (y / ·) b := rfl

/--
theorem `mod_def` / 定理 `mod_def`

English:
theorem mod_def
  given: [Mod α] (a b : Part α)
  statement: a % b = bind a fun y => map (y % ·) b
  proof: rfl

中文:
定理 mod_def
  条件: [取模 α] (a b : Part α)
  结论: a % b = bind a fun y => map (y % ·) b
  证明: rfl
-/
theorem mod_def [Mod α] (a b : Part α) : a % b = bind a fun y => map (y % ·) b := rfl
/--
theorem `append_def` / 定理 `append_def`

English:
theorem append_def
  given: [Append α] (a b : Part α)
  statement: a ++ b = bind a fun y => map (y ++ ·) b
  proof: rfl

中文:
定理 append_def
  条件: [Append α] (a b : Part α)
  结论: a ++ b = bind a fun y => map (y ++ ·) b
  证明: rfl
-/
theorem append_def [Append α] (a b : Part α) : a ++ b = bind a fun y => map (y ++ ·) b := rfl
/--
theorem `inter_def` / 定理 `inter_def`

English:
theorem inter_def
  given: [Inter α] (a b : Part α)
  statement: a inter b = bind a fun y => map (y inter ·) b
  proof: rfl

中文:
定理 inter_def
  条件: [交集 α] (a b : Part α)
  结论: a inter b = bind a fun y => map (y inter ·) b
  证明: rfl
-/
theorem inter_def [Inter α] (a b : Part α) : a inter b = bind a fun y => map (y inter ·) b := rfl
/--
theorem `union_def` / 定理 `union_def`

English:
theorem union_def
  given: [Union α] (a b : Part α)
  statement: a union b = bind a fun y => map (y union ·) b
  proof: rfl

中文:
定理 union_def
  条件: [并集 α] (a b : Part α)
  结论: a union b = bind a fun y => map (y union ·) b
  证明: rfl
-/
theorem union_def [Union α] (a b : Part α) : a union b = bind a fun y => map (y union ·) b := rfl
/--
theorem `sdiff_def` / 定理 `sdiff_def`

English:
theorem sdiff_def
  given: [SDiff α] (a b : Part α)
  statement: a \ b = bind a fun y => map (y \ ·) b
  proof: rfl

中文:
定理 sdiff_def
  条件: [对称差 α] (a b : Part α)
  结论: a \ b = bind a fun y => map (y \ ·) b
  证明: rfl
-/
theorem sdiff_def [SDiff α] (a b : Part α) : a \ b = bind a fun y => map (y \ ·) b := rfl

end

@[to_additive]
/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  given: [One α]
  statement: (1 : α) in (1 : Part α)
  proof: ⟨trivial, rfl⟩

@[to_additive]

中文:
定理 one_mem_one
  条件: [幺 α]
  结论: (1 : α) in (1 : Part α)
  证明: ⟨trivial, rfl⟩

@[to_additive]
-/
theorem one_mem_one [One α] : (1 : α) in (1 : Part α) :=
  ⟨trivial, rfl⟩

@[to_additive]
/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  given: [Mul α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: ⟨⟨ha.1, hb.1⟩, by simp only [← ha.2, ← hb.2]; rfl⟩

@[to_additive]

中文:
定理 mul_mem_mul
  条件: [乘法 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: ⟨⟨ha.1, hb.1⟩, by simp only [← ha.2, ← hb.2]; rfl⟩

@[to_additive]
-/
theorem mul_mem_mul [Mul α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma * mb in a * b := ⟨⟨ha.1, hb.1⟩, by simp only [← ha.2, ← hb.2]; rfl⟩

@[to_additive]
/--
theorem `left_dom_of_mul_dom` / 定理 `left_dom_of_mul_dom`

English:
theorem left_dom_of_mul_dom
  given: [Mul α] {a b : Part α} (hab : Dom (a * b))
  statement: a.Dom
  proof: hab.1

@[to_additive]

中文:
定理 left_dom_of_mul_dom
  条件: [乘法 α] {a b : Part α} (hab : Dom (a * b))
  结论: a.Dom
  证明: hab.1

@[to_additive]
-/
theorem left_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : a.Dom := hab.1

@[to_additive]
/--
theorem `right_dom_of_mul_dom` / 定理 `right_dom_of_mul_dom`

English:
theorem right_dom_of_mul_dom
  given: [Mul α] {a b : Part α} (hab : Dom (a * b))
  statement: b.Dom
  proof: hab.2

@[to_additive (attr := simp)]

中文:
定理 right_dom_of_mul_dom
  条件: [乘法 α] {a b : Part α} (hab : Dom (a * b))
  结论: b.Dom
  证明: hab.2

@[to_additive (attr := simp)]
-/
theorem right_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : b.Dom := hab.2

@[to_additive (attr := simp)]
/--
theorem `mul_get_eq` / 定理 `mul_get_eq`

English:
theorem mul_get_eq
  given: [Mul α] (a b : Part α) (hab : Dom (a * b))
  proof: rfl

@[to_additive]

中文:
定理 mul_get_eq
  条件: [乘法 α] (a b : Part α) (hab : Dom (a * b))
  证明: rfl

@[to_additive]
-/
theorem mul_get_eq [Mul α] (a b : Part α) (hab : Dom (a * b)) :
    (a * b).get hab = a.get (left_dom_of_mul_dom hab) * b.get (right_dom_of_mul_dom hab) := rfl

@[to_additive]
/--
theorem `some_mul_some` / 定理 `some_mul_some`

English:
theorem some_mul_some
  given: [Mul α] (a b : α)
  statement: some a * some b = some (a * b)
  proof: by simp [mul_def]

@[to_additive]

中文:
定理 some_mul_some
  条件: [乘法 α] (a b : α)
  结论: some a * some b = some (a * b)
  证明: by simp [mul_def]

@[to_additive]

Depends on / 依赖: mul_def
-/
theorem some_mul_some [Mul α] (a b : α) : some a * some b = some (a * b) := by simp [mul_def]

@[to_additive]
/--
theorem `inv_mem_inv` / 定理 `inv_mem_inv`

English:
theorem inv_mem_inv
  given: [Inv α] (a : Part α) (ma : α) (ha : ma in a)
  statement: ma⁻¹ in a⁻¹
  proof: by
  simp [inv_def]; aesop

@[to_additive]

中文:
定理 inv_mem_inv
  条件: [取逆 α] (a : Part α) (ma : α) (ha : ma in a)
  结论: ma⁻¹ in a⁻¹
  证明: by
  simp [inv_def]; aesop

@[to_additive]

Depends on / 依赖: inv_def
-/
theorem inv_mem_inv [Inv α] (a : Part α) (ma : α) (ha : ma in a) : ma⁻¹ in a⁻¹ := by
  simp [inv_def]; aesop

@[to_additive]
/--
theorem `inv_some` / 定理 `inv_some`

English:
theorem inv_some
  given: [Inv α] (a : α)
  statement: (some a)⁻¹ = some a⁻¹
  proof: rfl

@[to_additive]

中文:
定理 inv_some
  条件: [取逆 α] (a : α)
  结论: (some a)⁻¹ = some a⁻¹
  证明: rfl

@[to_additive]
-/
theorem inv_some [Inv α] (a : α) : (some a)⁻¹ = some a⁻¹ :=
  rfl

@[to_additive]
/--
theorem `div_mem_div` / 定理 `div_mem_div`

English:
theorem div_mem_div
  given: [Div α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [div_def]; aesop

@[to_additive]

中文:
定理 div_mem_div
  条件: [除法 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [div_def]; aesop

@[to_additive]

Depends on / 依赖: div_def
-/
theorem div_mem_div [Div α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma / mb in a / b := by simp [div_def]; aesop

@[to_additive]
/--
theorem `left_dom_of_div_dom` / 定理 `left_dom_of_div_dom`

English:
theorem left_dom_of_div_dom
  given: [Div α] {a b : Part α} (hab : Dom (a / b))
  statement: a.Dom
  proof: hab.1

@[to_additive]

中文:
定理 left_dom_of_div_dom
  条件: [除法 α] {a b : Part α} (hab : Dom (a / b))
  结论: a.Dom
  证明: hab.1

@[to_additive]
-/
theorem left_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : a.Dom := hab.1

@[to_additive]
/--
theorem `right_dom_of_div_dom` / 定理 `right_dom_of_div_dom`

English:
theorem right_dom_of_div_dom
  given: [Div α] {a b : Part α} (hab : Dom (a / b))
  statement: b.Dom
  proof: hab.2

@[to_additive (attr := simp)]

中文:
定理 right_dom_of_div_dom
  条件: [除法 α] {a b : Part α} (hab : Dom (a / b))
  结论: b.Dom
  证明: hab.2

@[to_additive (attr := simp)]
-/
theorem right_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : b.Dom := hab.2

@[to_additive (attr := simp)]
/--
theorem `div_get_eq` / 定理 `div_get_eq`

English:
theorem div_get_eq
  given: [Div α] (a b : Part α) (hab : Dom (a / b))
  proof: by
  simp [div_def]; aesop

@[to_additive]

中文:
定理 div_get_eq
  条件: [除法 α] (a b : Part α) (hab : Dom (a / b))
  证明: by
  simp [div_def]; aesop

@[to_additive]

Depends on / 依赖: div_def
-/
theorem div_get_eq [Div α] (a b : Part α) (hab : Dom (a / b)) :
    (a / b).get hab = a.get (left_dom_of_div_dom hab) / b.get (right_dom_of_div_dom hab) := by
  simp [div_def]; aesop

@[to_additive]
/--
theorem `some_div_some` / 定理 `some_div_some`

English:
theorem some_div_some
  given: [Div α] (a b : α)
  statement: some a / some b = some (a / b)
  proof: by simp [div_def]

中文:
定理 some_div_some
  条件: [除法 α] (a b : α)
  结论: some a / some b = some (a / b)
  证明: by simp [div_def]

Depends on / 依赖: div_def
-/
theorem some_div_some [Div α] (a b : α) : some a / some b = some (a / b) := by simp [div_def]

/--
theorem `mod_mem_mod` / 定理 `mod_mem_mod`

English:
theorem mod_mem_mod
  given: [Mod α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [mod_def]; aesop

中文:
定理 mod_mem_mod
  条件: [取模 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [mod_def]; aesop

Depends on / 依赖: mod_def
-/
theorem mod_mem_mod [Mod α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma % mb in a % b := by simp [mod_def]; aesop

/--
theorem `left_dom_of_mod_dom` / 定理 `left_dom_of_mod_dom`

English:
theorem left_dom_of_mod_dom
  given: [Mod α] {a b : Part α} (hab : Dom (a % b))
  statement: a.Dom
  proof: hab.1

中文:
定理 left_dom_of_mod_dom
  条件: [取模 α] {a b : Part α} (hab : Dom (a % b))
  结论: a.Dom
  证明: hab.1
-/
theorem left_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : a.Dom := hab.1

/--
theorem `right_dom_of_mod_dom` / 定理 `right_dom_of_mod_dom`

English:
theorem right_dom_of_mod_dom
  given: [Mod α] {a b : Part α} (hab : Dom (a % b))
  statement: b.Dom
  proof: hab.2

@[simp]

中文:
定理 right_dom_of_mod_dom
  条件: [取模 α] {a b : Part α} (hab : Dom (a % b))
  结论: b.Dom
  证明: hab.2

@[simp]
-/
theorem right_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : b.Dom := hab.2

@[simp]
/--
theorem `mod_get_eq` / 定理 `mod_get_eq`

English:
theorem mod_get_eq
  given: [Mod α] (a b : Part α) (hab : Dom (a % b))
  proof: by
  simp [mod_def]; aesop

中文:
定理 mod_get_eq
  条件: [取模 α] (a b : Part α) (hab : Dom (a % b))
  证明: by
  simp [mod_def]; aesop

Depends on / 依赖: mod_def
-/
theorem mod_get_eq [Mod α] (a b : Part α) (hab : Dom (a % b)) :
    (a % b).get hab = a.get (left_dom_of_mod_dom hab) % b.get (right_dom_of_mod_dom hab) := by
  simp [mod_def]; aesop

/--
theorem `some_mod_some` / 定理 `some_mod_some`

English:
theorem some_mod_some
  given: [Mod α] (a b : α)
  statement: some a % some b = some (a % b)
  proof: by simp [mod_def]

中文:
定理 some_mod_some
  条件: [取模 α] (a b : α)
  结论: some a % some b = some (a % b)
  证明: by simp [mod_def]

Depends on / 依赖: mod_def
-/
theorem some_mod_some [Mod α] (a b : α) : some a % some b = some (a % b) := by simp [mod_def]

/--
theorem `append_mem_append` / 定理 `append_mem_append`

English:
theorem append_mem_append
  given: [Append α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [append_def]; aesop

中文:
定理 append_mem_append
  条件: [Append α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [append_def]; aesop

Depends on / 依赖: append_def
-/
theorem append_mem_append [Append α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma ++ mb in a ++ b := by simp [append_def]; aesop

/--
theorem `left_dom_of_append_dom` / 定理 `left_dom_of_append_dom`

English:
theorem left_dom_of_append_dom
  given: [Append α] {a b : Part α} (hab : Dom (a ++ b))
  statement: a.Dom
  proof: hab.1

中文:
定理 left_dom_of_append_dom
  条件: [Append α] {a b : Part α} (hab : Dom (a ++ b))
  结论: a.Dom
  证明: hab.1
-/
theorem left_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : a.Dom := hab.1

/--
theorem `right_dom_of_append_dom` / 定理 `right_dom_of_append_dom`

English:
theorem right_dom_of_append_dom
  given: [Append α] {a b : Part α} (hab : Dom (a ++ b))
  statement: b.Dom
  proof: hab.2

@[simp]

中文:
定理 right_dom_of_append_dom
  条件: [Append α] {a b : Part α} (hab : Dom (a ++ b))
  结论: b.Dom
  证明: hab.2

@[simp]
-/
theorem right_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : b.Dom := hab.2

@[simp]
/--
theorem `append_get_eq` / 定理 `append_get_eq`

English:
theorem append_get_eq
  given: [Append α] (a b : Part α) (hab : Dom (a ++ b))
  statement: (a ++ b).get hab =
  proof: by
  simp [append_def]; aesop

中文:
定理 append_get_eq
  条件: [Append α] (a b : Part α) (hab : Dom (a ++ b))
  结论: (a ++ b).get hab =
  证明: by
  simp [append_def]; aesop

Depends on / 依赖: append_def
-/
theorem append_get_eq [Append α] (a b : Part α) (hab : Dom (a ++ b)) : (a ++ b).get hab =
    a.get (left_dom_of_append_dom hab) ++ b.get (right_dom_of_append_dom hab) := by
  simp [append_def]; aesop

/--
theorem `some_append_some` / 定理 `some_append_some`

English:
theorem some_append_some
  given: [Append α] (a b : α)
  statement: some a ++ some b = some (a ++ b)
  proof: by
  simp [append_def]

中文:
定理 some_append_some
  条件: [Append α] (a b : α)
  结论: some a ++ some b = some (a ++ b)
  证明: by
  simp [append_def]

Depends on / 依赖: append_def
-/
theorem some_append_some [Append α] (a b : α) : some a ++ some b = some (a ++ b) := by
  simp [append_def]

/--
theorem `inter_mem_inter` / 定理 `inter_mem_inter`

English:
theorem inter_mem_inter
  given: [Inter α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [inter_def]; aesop

中文:
定理 inter_mem_inter
  条件: [交集 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [inter_def]; aesop

Depends on / 依赖: inter_def
-/
theorem inter_mem_inter [Inter α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma inter mb in a inter b := by simp [inter_def]; aesop

/--
theorem `left_dom_of_inter_dom` / 定理 `left_dom_of_inter_dom`

English:
theorem left_dom_of_inter_dom
  given: [Inter α] {a b : Part α} (hab : Dom (a inter b))
  statement: a.Dom
  proof: hab.1

中文:
定理 left_dom_of_inter_dom
  条件: [交集 α] {a b : Part α} (hab : Dom (a inter b))
  结论: a.Dom
  证明: hab.1
-/
theorem left_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a inter b)) : a.Dom := hab.1

/--
theorem `right_dom_of_inter_dom` / 定理 `right_dom_of_inter_dom`

English:
theorem right_dom_of_inter_dom
  given: [Inter α] {a b : Part α} (hab : Dom (a inter b))
  statement: b.Dom
  proof: hab.2

@[simp]

中文:
定理 right_dom_of_inter_dom
  条件: [交集 α] {a b : Part α} (hab : Dom (a inter b))
  结论: b.Dom
  证明: hab.2

@[simp]

Depends on / 依赖: RatFunc, RatFunc.liftOn, RatFunc.liftOn_mk, _condition, liftOn, liftOn_condition_of_liftOn, liftOn_mk
-/
theorem right_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a inter b)) : b.Dom := hab.2

@[simp]
/--
theorem `inter_get_eq` / 定理 `inter_get_eq`

English:
theorem inter_get_eq
  given: [Inter α] (a b : Part α) (hab : Dom (a inter b))
  proof: by
  simp [inter_def]; aesop

中文:
定理 inter_get_eq
  条件: [交集 α] (a b : Part α) (hab : Dom (a inter b))
  证明: by
  simp [inter_def]; aesop

Depends on / 依赖: inter_def
-/
theorem inter_get_eq [Inter α] (a b : Part α) (hab : Dom (a inter b)) :
    (a inter b).get hab = a.get (left_dom_of_inter_dom hab) inter b.get (right_dom_of_inter_dom hab) := by
  simp [inter_def]; aesop

/--
theorem `some_inter_some` / 定理 `some_inter_some`

English:
theorem some_inter_some
  given: [Inter α] (a b : α)
  statement: some a inter some b = some (a inter b)
  proof: by
  simp [inter_def]

中文:
定理 some_inter_some
  条件: [交集 α] (a b : α)
  结论: some a inter some b = some (a inter b)
  证明: by
  simp [inter_def]

Depends on / 依赖: inter_def
-/
theorem some_inter_some [Inter α] (a b : α) : some a inter some b = some (a inter b) := by
  simp [inter_def]

/--
theorem `union_mem_union` / 定理 `union_mem_union`

English:
theorem union_mem_union
  given: [Union α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [union_def]; aesop

中文:
定理 union_mem_union
  条件: [并集 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [union_def]; aesop

Depends on / 依赖: union_def
-/
theorem union_mem_union [Union α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma union mb in a union b := by simp [union_def]; aesop

/--
theorem `left_dom_of_union_dom` / 定理 `left_dom_of_union_dom`

English:
theorem left_dom_of_union_dom
  given: [Union α] {a b : Part α} (hab : Dom (a union b))
  statement: a.Dom
  proof: hab.1

中文:
定理 left_dom_of_union_dom
  条件: [并集 α] {a b : Part α} (hab : Dom (a union b))
  结论: a.Dom
  证明: hab.1
-/
theorem left_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a union b)) : a.Dom := hab.1

/--
theorem `right_dom_of_union_dom` / 定理 `right_dom_of_union_dom`

English:
theorem right_dom_of_union_dom
  given: [Union α] {a b : Part α} (hab : Dom (a union b))
  statement: b.Dom
  proof: hab.2

@[simp]

中文:
定理 right_dom_of_union_dom
  条件: [并集 α] {a b : Part α} (hab : Dom (a union b))
  结论: b.Dom
  证明: hab.2

@[simp]
-/
theorem right_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a union b)) : b.Dom := hab.2

@[simp]
/--
theorem `union_get_eq` / 定理 `union_get_eq`

English:
theorem union_get_eq
  given: [Union α] (a b : Part α) (hab : Dom (a union b))
  proof: by
  simp [union_def]; aesop

中文:
定理 union_get_eq
  条件: [并集 α] (a b : Part α) (hab : Dom (a union b))
  证明: by
  simp [union_def]; aesop

Depends on / 依赖: union_def
-/
theorem union_get_eq [Union α] (a b : Part α) (hab : Dom (a union b)) :
    (a union b).get hab = a.get (left_dom_of_union_dom hab) union b.get (right_dom_of_union_dom hab) := by
  simp [union_def]; aesop

/--
theorem `some_union_some` / 定理 `some_union_some`

English:
theorem some_union_some
  given: [Union α] (a b : α)
  statement: some a union some b = some (a union b)
  proof: by simp [union_def]

中文:
定理 some_union_some
  条件: [并集 α] (a b : α)
  结论: some a union some b = some (a union b)
  证明: by simp [union_def]

Depends on / 依赖: union_def
-/
theorem some_union_some [Union α] (a b : α) : some a union some b = some (a union b) := by simp [union_def]

/--
theorem `sdiff_mem_sdiff` / 定理 `sdiff_mem_sdiff`

English:
theorem sdiff_mem_sdiff
  given: [SDiff α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  proof: by simp [sdiff_def]; aesop

中文:
定理 sdiff_mem_sdiff
  条件: [对称差 α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b)
  证明: by simp [sdiff_def]; aesop

Depends on / 依赖: sdiff_def
-/
theorem sdiff_mem_sdiff [SDiff α] (a b : Part α) (ma mb : α) (ha : ma in a) (hb : mb in b) :
    ma \ mb in a \ b := by simp [sdiff_def]; aesop

/--
theorem `left_dom_of_sdiff_dom` / 定理 `left_dom_of_sdiff_dom`

English:
theorem left_dom_of_sdiff_dom
  given: [SDiff α] {a b : Part α} (hab : Dom (a \ b))
  statement: a.Dom
  proof: hab.1

中文:
定理 left_dom_of_sdiff_dom
  条件: [对称差 α] {a b : Part α} (hab : Dom (a \ b))
  结论: a.Dom
  证明: hab.1
-/
theorem left_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : a.Dom := hab.1

/--
theorem `right_dom_of_sdiff_dom` / 定理 `right_dom_of_sdiff_dom`

English:
theorem right_dom_of_sdiff_dom
  given: [SDiff α] {a b : Part α} (hab : Dom (a \ b))
  statement: b.Dom
  proof: hab.2

@[simp]

中文:
定理 right_dom_of_sdiff_dom
  条件: [对称差 α] {a b : Part α} (hab : Dom (a \ b))
  结论: b.Dom
  证明: hab.2

@[simp]
-/
theorem right_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : b.Dom := hab.2

@[simp]
/--
theorem `sdiff_get_eq` / 定理 `sdiff_get_eq`

English:
theorem sdiff_get_eq
  given: [SDiff α] (a b : Part α) (hab : Dom (a \ b))
  proof: by
  simp [sdiff_def]; aesop

中文:
定理 sdiff_get_eq
  条件: [对称差 α] (a b : Part α) (hab : Dom (a \ b))
  证明: by
  simp [sdiff_def]; aesop

Depends on / 依赖: sdiff_def
-/
theorem sdiff_get_eq [SDiff α] (a b : Part α) (hab : Dom (a \ b)) :
    (a \ b).get hab = a.get (left_dom_of_sdiff_dom hab) \ b.get (right_dom_of_sdiff_dom hab) := by
  simp [sdiff_def]; aesop

/--
theorem `some_sdiff_some` / 定理 `some_sdiff_some`

English:
theorem some_sdiff_some
  given: [SDiff α] (a b : α)
  statement: some a \ some b = some (a \ b)
  proof: by simp [sdiff_def]

中文:
定理 some_sdiff_some
  条件: [对称差 α] (a b : α)
  结论: some a \ some b = some (a \ b)
  证明: by simp [sdiff_def]

Depends on / 依赖: sdiff_def
-/
theorem some_sdiff_some [SDiff α] (a b : α) : some a \ some b = some (a \ b) := by simp [sdiff_def]

end Instances

end Part
