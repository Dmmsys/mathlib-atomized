/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib/Data/Option/`.
Other basic operations on `Option` are defined in the core library.
-/

@[expose] public section

namespace Option

/--
Definition of `traverse.` / `traverse.` 的定义

English:
definition traverse.{u,
  signature: v}
  body: Option.mapA f

中文:
定义 traverse.{u,
  签名: v}
  定义体: Option.mapA f
-/
protected def traverse.{u, v}
    {F : Type u -> Type v} [Applicative F] {α : Type*} {β : Type u} (f : α -> F β) :
    Option α -> F (Option β) := Option.mapA f

variable {α : Type*} {β : Type*}

/--
Definition of `elim'` / `elim'` 的定义

English:
definition elim'
  signature: (b : β) (f : α -> β)

中文:
定义 elim'
  签名: (b : β) (f : α -> β)
-/
protected def elim' (b : β) (f : α -> β) : Option α -> β
  | some a => f a
  | none => b

@[simp]
/--
theorem `elim'_none` / 定理 `elim'_none`

English:
theorem elim'_none
  given: (b : β) (f : α -> β)
  statement: Option.elim' b f none = b
  proof: rfl

@[simp]

中文:
定理 elim'_none
  条件: (b : β) (f : α -> β)
  结论: Option.elim' b f none = b
  证明: rfl

@[simp]
-/
theorem elim'_none (b : β) (f : α -> β) : Option.elim' b f none = b := rfl

@[simp]
/--
theorem `elim'_some` / 定理 `elim'_some`

English:
theorem elim'_some
  given: {a : α} (b : β) (f : α -> β)
  statement: Option.elim' b f (some a) = f a
  proof: rfl

@[simp]

中文:
定理 elim'_some
  条件: {a : α} (b : β) (f : α -> β)
  结论: Option.elim' b f (some a) = f a
  证明: rfl

@[simp]
-/
theorem elim'_some {a : α} (b : β) (f : α -> β) : Option.elim' b f (some a) = f a := rfl

@[simp]
/--
theorem `elim'_none_some` / 定理 `elim'_none_some`

English:
theorem elim'_none_some
  given: (f : Option α -> β)
  statement: (Option.elim' (f none) (f ∘ some)) = f
  proof: funext fun o => by cases o <;> rfl

中文:
定理 elim'_none_some
  条件: (f : Option α -> β)
  结论: (Option.elim' (f none) (f ∘ some)) = f
  证明: funext fun o => by cases o <;> rfl
-/
theorem elim'_none_some (f : Option α -> β) : (Option.elim' (f none) (f ∘ some)) = f :=
  funext fun o => by cases o <;> rfl

/--
lemma `elim'_eq_elim` / 引理 `elim'_eq_elim`

English:
lemma elim'_eq_elim
  given: {α β : Type*} (b : β) (f : α -> β) (a : Option α)
  proof: by
  cases a <;> rfl

中文:
引理 elim'_eq_elim
  条件: {α β : 类型} (b : β) (f : α -> β) (a : Option α)
  证明: by
  cases a <;> rfl
-/
lemma elim'_eq_elim {α β : Type*} (b : β) (f : α -> β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[deprecated "Use `Option.get!` (which will panic on `none`) or \
    `Option.getD` (which takes an explicit default value)." (since := "2026-01-05")]
/--
Definition of `iget` / `iget` 的定义

English:
abbreviation iget
  signature: [Inhabited α]

中文:
缩写 iget
  签名: [Inhabited α]
-/
abbrev iget [Inhabited α] : Option α -> α
  | some x => x
  | none => default

@[deprecated "Use `Option.getD`." (since := "2026-01-05")]
/--
theorem `iget_some` / 定理 `iget_some`

English:
theorem iget_some
  given: [Inhabited α] {a : α}
  statement: (some a).iget = a
  proof: rfl

中文:
定理 iget_some
  条件: [Inhabited α] {a : α}
  结论: (some a).iget = a
  证明: rfl
-/
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

end Option
