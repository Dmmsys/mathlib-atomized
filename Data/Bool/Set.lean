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
/-
**Bool.univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：univ_eq : (univ : Set Bool) = {false, true}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_eq : (univ : Set Bool) = {false, true} := by grind

@[simp, grind =]
/-
**Bool.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：range_eq {α : Type*} (f : Bool -> α) : range f = {f false, f true}
参数：f : Bool -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_eq {α : Type*} (f : Bool → α) : range f = {f false, f true} := by grind [cases Bool]

@[simp, grind =]
/-
**Bool.compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b}
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b} := by grind [cases Bool]

end Bool

