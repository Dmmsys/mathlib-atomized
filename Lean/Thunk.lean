/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Init

/-!
# Basic facts about `Thunk`.
-/

@[expose] public section

namespace Thunk

/--
theorem `get_pure` / 定理 `get_pure`

English:
theorem get_pure
  given: {α} (x : α)
  statement: (Thunk.pure x).get = x
  proof: rfl

中文:
定理 get_pure
  条件: {α} (x : α)
  结论: (Thunk.pure x).get = x
  证明: rfl
-/
@[simp] theorem get_pure {α} (x : α) : (Thunk.pure x).get = x := rfl
/--
theorem `get_mk` / 定理 `get_mk`

English:
theorem get_mk
  given: {α} (f : Unit -> α)
  statement: (Thunk.mk f).get = f ()
  proof: rfl

universe u v

中文:
定理 get_mk
  条件: {α} (f : Unit -> α)
  结论: (Thunk.mk f).get = f ()
  证明: rfl

universe u v
-/
@[simp] theorem get_mk {α} (f : Unit -> α) : (Thunk.mk f).get = f () := rfl

universe u v
variable {α : Type u} {β : Type v}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Thunk α)
  body: by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Thunk α)
  定义体: by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

Depends on / 依赖: a.get, b.get, infer_instance
-/
instance [DecidableEq α] : DecidableEq (Thunk α) := by
  intro a b
  have : a = b ↔ a.get = b.get := ⟨by intro x; rw [x], by intro; ext; assumption⟩
  rw [this]
  infer_instance

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (a : Thunk α) (b : Thunk β)
  body: Thunk.mk fun _ => (a.get, b.get)

中文:
定义 prod
  签名: (a : Thunk α) (b : Thunk β)
  定义体: Thunk.mk fun _ => (a.get, b.get)

Depends on / 依赖: Thunk.mk, a.get, b.get
-/
def prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

/--
theorem `prod_get_fst` / 定理 `prod_get_fst`

English:
theorem prod_get_fst
  given: {a : Thunk α} {b : Thunk β}
  statement: (prod a b).get.1 = a.get
  proof: rfl

中文:
定理 prod_get_fst
  条件: {a : Thunk α} {b : Thunk β}
  结论: (prod a b).get.1 = a.get
  证明: rfl
-/
@[simp] theorem prod_get_fst {a : Thunk α} {b : Thunk β} : (prod a b).get.1 = a.get := rfl
/--
theorem `prod_get_snd` / 定理 `prod_get_snd`

English:
theorem prod_get_snd
  given: {a : Thunk α} {b : Thunk β}
  statement: (prod a b).get.2 = b.get
  proof: rfl

中文:
定理 prod_get_snd
  条件: {a : Thunk α} {b : Thunk β}
  结论: (prod a b).get.2 = b.get
  证明: rfl
-/
@[simp] theorem prod_get_snd {a : Thunk α} {b : Thunk β} : (prod a b).get.2 = b.get := rfl

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: [Add α] (a b : Thunk α)
  body: Thunk.mk fun _ => a.get + b.get

中文:
定义 add
  签名: [Add α] (a b : Thunk α)
  定义体: Thunk.mk fun _ => a.get + b.get

Depends on / 依赖: Thunk.mk, a.get, b.get
-/
def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] : Add (Thunk α)
  body: ⟨add⟩

中文:
实例 [Add
  签名: α] : Add (Thunk α)
  定义体: ⟨add⟩
-/
instance [Add α] : Add (Thunk α) := ⟨add⟩

/--
theorem `add_get` / 定理 `add_get`

English:
theorem add_get
  given: [Add α] {a b : Thunk α}
  statement: (a + b).get = a.get + b.get
  proof: rfl

中文:
定理 add_get
  条件: [Add α] {a b : Thunk α}
  结论: (a + b).get = a.get + b.get
  证明: rfl
-/
@[simp] theorem add_get [Add α] {a b : Thunk α} : (a + b).get = a.get + b.get := rfl

end Thunk
