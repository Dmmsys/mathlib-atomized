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

/--
theorem `find?_eq_find?_of_perm` / 定理 `find?_eq_find?_of_perm`

English:
theorem find?_eq_find?_of_perm
  statement: {p : α -> Bool} {l₁ l₂ : List α}
  proof: by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    grind
  | swap x y l =>
    dsimp [Set.Subsingleton] at hp
    by_cases p x <;> by_cases p y <;> grind
  | trans _ _ ih1 ih2 =>
    refine (ih1 ?_).trans (ih2 ?_) <;> grind

中文:
定理 find?_eq_find?_of_perm
  结论: {p : α -> 布尔值} {l₁ l₂ : 列表 α}
  证明: by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    grind
  | swap x y l =>
    dsimp [Set.Subsingleton] at hp
    by_cases p x <;> by_cases p y <;> grind
  | trans _ _ ih1 ih2 =>
    refine (ih1 ?_).trans (ih2 ?_) <;> grind

Depends on / 依赖: Set.Subsingleton, Subsingleton
-/
theorem find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (hp : {x in l₁ | p x}.Subsingleton) :
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
/--
theorem `find?_congr` / 定理 `find?_congr`

English:
theorem find?_congr
  given: {p₁ p₂ : α -> Bool} {l : List α} (h : forall x in l, p₁ x = p₂ x)
  proof: by
  induction l with grind

中文:
定理 find?_congr
  条件: {p₁ p₂ : α -> 布尔值} {l : 列表 α} (h : 对任意 x in l, p₁ x = p₂ x)
  证明: by
  induction l with grind
-/
theorem find?_congr {p₁ p₂ : α -> Bool} {l : List α} (h : forall x in l, p₁ x = p₂ x) :
    l.find? p₁ = l.find? p₂ := by
  induction l with grind

end List
