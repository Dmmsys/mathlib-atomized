/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero/one to semigroups and mapping
-/

@[expose] public section

variable {α β γ : Type*}

namespace WithOne

/-- Lift a map `f : α → β` to `WithOne α → WithOne β`. Implemented using `Option.map`.

Note: the definition previously known as `WithOne.map` is now called `WithOne.mapMulHom`. -/
@[to_additive
/-- Lift a map `f : α → β` to `WithZero α → WithZero β`. Implemented using `Option.map`.

Note: the definition previously known as `WithZero.map` is now called `WithZero.mapAddHom`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: Option.map f

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : α -> β)
  定义体: Option.map f

@[to_additive (attr := simp)]

Depends on / 依赖: Option.map
-/
def map (f : α -> β) : WithOne α -> WithOne β := Option.map f

@[to_additive (attr := simp)]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : α -> β)
  statement: map f 1 = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_bot
  条件: (f : α -> β)
  结论: map f 1 = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_bot (f : α -> β) : map f 1 = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (f : α -> β) (a : α)
  statement: map f a = f a
  proof: rfl

中文:
定理 map_coe
  条件: (f : α -> β) (a : α)
  结论: map f a = f a
  证明: rfl
-/
theorem map_coe (f : α -> β) (a : α) : map f a = f a :=
  rfl

/-- The image of a binary function `f : α → β → γ` as a function
`WithOne α → WithOne β → WithOne γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_additive
/-- The image of a binary function `f : α → β → γ` as a function
`WithZero α → WithZero β → WithZero γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: : (α -> β -> γ) -> WithOne α -> WithOne β -> WithOne γ
  body: Option.map₂

@[to_additive]

中文:
定义 map₂
  签名: : (α -> β -> γ) -> WithOne α -> WithOne β -> WithOne γ
  定义体: Option.map₂

@[to_additive]

Depends on / 依赖: Option.map
-/
def map₂ : (α -> β -> γ) -> WithOne α -> WithOne β -> WithOne γ := Option.map₂

@[to_additive]
/--
lemma `map₂_coe_coe` / 引理 `map₂_coe_coe`

English:
lemma map₂_coe_coe
  given: (f : α -> β -> γ) (a : α) (b : β)
  statement: map₂ f a b = f a b
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 map₂_coe_coe
  条件: (f : α -> β -> γ) (a : α) (b : β)
  结论: map₂ f a b = f a b
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma map₂_coe_coe (f : α -> β -> γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[to_additive (attr := simp)]
/--
lemma `map₂_bot_left` / 引理 `map₂_bot_left`

English:
lemma map₂_bot_left
  given: (f : α -> β -> γ) (b)
  statement: map₂ f 1 b = 1
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 map₂_bot_left
  条件: (f : α -> β -> γ) (b)
  结论: map₂ f 1 b = 1
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma map₂_bot_left (f : α -> β -> γ) (b) : map₂ f 1 b = 1 := rfl
@[to_additive (attr := simp)]
/--
lemma `map₂_bot_right` / 引理 `map₂_bot_right`

English:
lemma map₂_bot_right
  given: (f : α -> β -> γ) (a)
  statement: map₂ f a 1 = 1
  proof: by cases a <;> rfl
@[to_additive (attr := simp)]

中文:
引理 map₂_bot_right
  条件: (f : α -> β -> γ) (a)
  结论: map₂ f a 1 = 1
  证明: by cases a <;> rfl
@[to_additive (attr := simp)]

Depends on / 依赖: to_additive
-/
lemma map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 1 = 1 := by cases a <;> rfl
@[to_additive (attr := simp)]
/--
lemma `map₂_coe_left` / 引理 `map₂_coe_left`

English:
lemma map₂_coe_left
  given: (f : α -> β -> γ) (a : α) (b)
  statement: map₂ f a b = b.map fun b => f a b
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 map₂_coe_left
  条件: (f : α -> β -> γ) (a : α) (b)
  结论: map₂ f a b = b.map fun b => f a b
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma map₂_coe_left (f : α -> β -> γ) (a : α) (b) : map₂ f a b = b.map fun b => f a b := rfl
@[to_additive (attr := simp)]
/--
lemma `map₂_coe_right` / 引理 `map₂_coe_right`

English:
lemma map₂_coe_right
  given: (f : α -> β -> γ) (a) (b : β)
  statement: map₂ f a b = a.map (f · b)
  proof: by
  cases a <;> rfl

@[to_additive (attr := simp)]

中文:
引理 map₂_coe_right
  条件: (f : α -> β -> γ) (a) (b : β)
  结论: map₂ f a b = a.map (f · b)
  证明: by
  cases a <;> rfl

@[to_additive (attr := simp)]
-/
lemma map₂_coe_right (f : α -> β -> γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[to_additive (attr := simp)]
/--
lemma `map₂_eq_bot_iff` / 引理 `map₂_eq_bot_iff`

English:
lemma map₂_eq_bot_iff
  given: {f : α -> β -> γ} {a : WithOne α} {b : WithOne β}
  proof: Option.map₂_eq_none_iff

中文:
引理 map₂_eq_bot_iff
  条件: {f : α -> β -> γ} {a : WithOne α} {b : WithOne β}
  证明: Option.map₂_eq_none_iff

Depends on / 依赖: Option.map
-/
lemma map₂_eq_bot_iff {f : α -> β -> γ} {a : WithOne α} {b : WithOne β} :
    map₂ f a b = 1 ↔ a = 1 ∨ b = 1 := Option.map₂_eq_none_iff

end WithOne
