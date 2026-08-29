/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Insert

/-!
# Booleans and set operations

This file contains three trivial lemmas about `Bool`, `Set.univ`, and `Set.range`.
-/

public section


open Set

namespace Bool

@[simp]
/--
theorem `univ_eq` / 定理 `univ_eq`

English:
theorem univ_eq
  statement: (univ : Set Bool) = {false, true}
  proof: by grind

@[simp, grind =]

中文:
定理 univ_eq
  结论: (univ : 集合 布尔值) = {false, true}
  证明: by grind

@[simp, grind =]
-/
theorem univ_eq : (univ : Set Bool) = {false, true} := by grind

@[simp, grind =]
/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: {α : Type*} (f : Bool -> α)
  statement: range f = {f false, f true}
  proof: by grind [cases Bool]

@[simp, grind =]

中文:
定理 range_eq
  条件: {α : 类型} (f : 布尔值 -> α)
  结论: range f = {f false, f true}
  证明: by grind [cases Bool]

@[simp, grind =]
-/
theorem range_eq {α : Type*} (f : Bool -> α) : range f = {f false, f true} := by grind [cases Bool]

@[simp, grind =]
/--
theorem `compl_singleton` / 定理 `compl_singleton`

English:
theorem compl_singleton
  given: (b : Bool)
  statement: ({b}ᶜ : Set Bool) = {!b}
  proof: by grind [cases Bool]

中文:
定理 compl_singleton
  条件: (b : 布尔值)
  结论: ({b}ᶜ : 集合 布尔值) = {!b}
  证明: by grind [cases Bool]
-/
theorem compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b} := by grind [cases Bool]

end Bool
