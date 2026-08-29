/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Defs

/-!
# Coercing sets to types.

This file defines `Set.Elem s` as the type of all elements of the set `s`.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- `Set.Elem`: coercion of a set to a type; it is reducibly equal to `{x // x ∈ s}`;
-/

@[expose] public section

namespace Set

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/--
Definition of `Elem` / `Elem` 的定义

English:
definition Elem
  signature: (s : Set α)
  body: {x // x in s}

中文:
定义 Elem
  签名: (s : Set α)
  定义体: {x // x in s}
-/
@[coe, reducible] def Elem (s : Set α) : Type u := {x // x in s}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (Set α) (Type u)
  body: ⟨Elem⟩

中文:
实例 :
  签名: CoeSort (Set α) (类型u)
  定义体: ⟨Elem⟩
-/
instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

/--
theorem `elem_mem` / 定理 `elem_mem`

English:
theorem elem_mem
  given: {σ α} [Membership σ α] {S : α}
  proof: rfl

中文:
定理 elem_mem
  条件: {σ α} [Membership σ α] {S : α}
  证明: rfl

Depends on / 依赖: oneTangentSpaceIcc
-/
@[simp] theorem elem_mem {σ α} [Membership σ α] {S : α} :
    ↑{x : σ | x in S} = {x // x in S} :=
  rfl

end Set
