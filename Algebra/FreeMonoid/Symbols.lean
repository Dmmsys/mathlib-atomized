/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# The finite set of symbols in a FreeMonoid element

This is separated from the main FreeMonoid file, as it imports the finiteness hierarchy
-/

@[expose] public section

variable {α : Type*} [DecidableEq α]

namespace FreeMonoid

/-- the set of unique symbols in a free monoid element -/
@[to_additive /-- The set of unique symbols in an additive free monoid element -/]
/--
Definition of `symbols` / `symbols` 的定义

English:
definition symbols
  signature: (a : FreeMonoid α)
  body: List.toFinset a

@[to_additive (attr := simp)]

中文:
定义 symbols
  签名: (a : 自由幺半群 α)
  定义体: List.toFinset a

@[to_additive (attr := simp)]

Depends on / 依赖: List.toFinset, toFinset
-/
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

@[to_additive (attr := simp)]
/--
theorem `symbols_one` / 定理 `symbols_one`

English:
theorem symbols_one
  statement: symbols (1 : FreeMonoid α) = ∅
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symbols_one
  结论: symbols (1 : 自由幺半群 α) = ∅
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl

@[to_additive (attr := simp)]
/--
theorem `symbols_of` / 定理 `symbols_of`

English:
theorem symbols_of
  given: {m : α}
  statement: symbols (of m) = {m}
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 symbols_of
  条件: {m : α}
  结论: symbols (of m) = {m}
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem symbols_of {m : α} : symbols (of m) = {m} := rfl

@[to_additive (attr := simp)]
/--
theorem `symbols_mul` / 定理 `symbols_mul`

English:
theorem symbols_mul
  given: {a b : FreeMonoid α}
  statement: symbols (a * b) = symbols a union symbols b
  proof: List.toFinset_append

@[to_additive (attr := simp)]

中文:
定理 symbols_mul
  条件: {a b : 自由幺半群 α}
  结论: symbols (a * b) = symbols a union symbols b
  证明: List.toFinset_append

@[to_additive (attr := simp)]

Depends on / 依赖: List.toFinset_append, toFinset_append
-/
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a union symbols b :=
  List.toFinset_append

@[to_additive (attr := simp)]
/--
theorem `mem_symbols` / 定理 `mem_symbols`

English:
theorem mem_symbols
  given: {m : α} {a : FreeMonoid α}
  statement: m in symbols a ↔ m in a
  proof: List.mem_toFinset

中文:
定理 mem_symbols
  条件: {m : α} {a : 自由幺半群 α}
  结论: m in symbols a ↔ m in a
  证明: List.mem_toFinset

Depends on / 依赖: List.mem_toFinset, mem_toFinset
-/
theorem mem_symbols {m : α} {a : FreeMonoid α} : m in symbols a ↔ m in a :=
  List.mem_toFinset

end FreeMonoid
