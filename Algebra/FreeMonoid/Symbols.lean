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
/-
**FreeMonoid.symbols** 是 Mathlib 中的一个定义，位于命名空间 `FreeMonoid`。
形式化陈述：symbols (a : FreeMonoid α) : Finset α
参数：a : FreeMonoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the set of unique symbols in a free monoid element
-/
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

@[to_additive (attr := simp)]
/-
**FreeMonoid.symbols_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：symbols_one : symbols (1 : FreeMonoid α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl

@[to_additive (attr := simp)]
/-
**FreeMonoid.symbols_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：symbols_of {m : α} : symbols (of m) = {m}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symbols_of {m : α} : symbols (of m) = {m} := rfl

@[to_additive (attr := simp)]
/-
**FreeMonoid.symbols_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a union symbo
ls b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.toFinset_append`：toFinset_append : toFinset (l ++ l') = l.toFinset 
union l'.toFinset
-/
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a ∪ symbols b :=
  List.toFinset_append

@[to_additive (attr := simp)]
/-
**FreeMonoid.mem_symbols** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：mem_symbols {m : α} {a : FreeMonoid α} : m in symbols a ↔ m in a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
-/
theorem mem_symbols {m : α} {a : FreeMonoid α} : m ∈ symbols a ↔ m ∈ a :=
  List.mem_toFinset

end FreeMonoid

