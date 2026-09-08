/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Set.Subsingleton

/-!
# Lemmas about `List.find?`
-/

public section

namespace List
variable {α : Type*}

/-- If there is at most one element satisfying `p`, then `find?` agrees on permuted lists. -/
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is at most one element satisfying `p`, then `find?` agrees on permuted 
lists.
-/
theorem find?_eq_find?_of_perm {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (hp : {x ∈ l₁ | p x}.Subsingleton) :
    l₁.find? p = l₂.find? p := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    grind
  | swap x y l =>
    dsimp [Set.Subsingleton] at hp
    by_cases p x <;> by_cases p y <;> grind
  | trans _ _ ih1 ih2 =>
    refine (ih1 ?_).trans (ih2 ?_) <;> grind

/-- If two predicates agree on all the elements, so does `find?`. -/
@[congr]
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two predicates agree on all the elements, so does `find?`.
-/
theorem find?_congr {p₁ p₂ : α → Bool} {l : List α} (h : ∀ x ∈ l, p₁ x = p₂ x) :
    l.find? p₁ = l.find? p₂ := by
  induction l with grind

end List

