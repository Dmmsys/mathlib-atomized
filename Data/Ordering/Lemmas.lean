/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Ordering.Basic
public import Mathlib.Order.Defs.Unbundled

/-!
# Some `Ordering` lemmas
-/

public section

universe u

namespace Ordering

@[simp]
/--
theorem `ite_eq_lt_distrib` / 定理 `ite_eq_lt_distrib`

English:
theorem ite_eq_lt_distrib
  given: (c : Prop) [Decidable c] (a b : Ordering)
  proof: by
  by_cases c <;> simp [*]

@[simp]

中文:
定理 ite_eq_lt_distrib
  条件: (c : 命题) [可判定 c] (a b : Ordering)
  证明: by
  by_cases c <;> simp [*]

@[simp]
-/
theorem ite_eq_lt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.lt) = if c then a = Ordering.lt else b = Ordering.lt := by
  by_cases c <;> simp [*]

@[simp]
/--
theorem `ite_eq_eq_distrib` / 定理 `ite_eq_eq_distrib`

English:
theorem ite_eq_eq_distrib
  given: (c : Prop) [Decidable c] (a b : Ordering)
  proof: by
  by_cases c <;> simp [*]

@[simp]

中文:
定理 ite_eq_eq_distrib
  条件: (c : 命题) [可判定 c] (a b : Ordering)
  证明: by
  by_cases c <;> simp [*]

@[simp]
-/
theorem ite_eq_eq_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.eq) = if c then a = Ordering.eq else b = Ordering.eq := by
  by_cases c <;> simp [*]

@[simp]
/--
theorem `ite_eq_gt_distrib` / 定理 `ite_eq_gt_distrib`

English:
theorem ite_eq_gt_distrib
  given: (c : Prop) [Decidable c] (a b : Ordering)
  proof: by
  by_cases c <;> simp [*]

@[simp]

中文:
定理 ite_eq_gt_distrib
  条件: (c : 命题) [可判定 c] (a b : Ordering)
  证明: by
  by_cases c <;> simp [*]

@[simp]
-/
theorem ite_eq_gt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.gt) = if c then a = Ordering.gt else b = Ordering.gt := by
  by_cases c <;> simp [*]

@[simp]
/--
lemma `dthen_eq_then` / 引理 `dthen_eq_then`

English:
lemma dthen_eq_then
  given: (o₁ o₂ : Ordering)
  statement: o₁.dthen (fun _ => o₂) = o₁.then o₂
  proof: by
  cases o₁ <;> rfl

中文:
引理 dthen_eq_then
  条件: (o₁ o₂ : Ordering)
  结论: o₁.dthen (fun _ => o₂) = o₁.then o₂
  证明: by
  cases o₁ <;> rfl
-/
lemma dthen_eq_then (o₁ o₂ : Ordering) : o₁.dthen (fun _ => o₂) = o₁.then o₂ := by
  cases o₁ <;> rfl

end Ordering

section

variable {α : Type u} {lt : α -> α -> Prop} [DecidableRel lt]

attribute [local simp] cmpUsing

@[simp]
/--
theorem `cmpUsing_eq_lt` / 定理 `cmpUsing_eq_lt`

English:
theorem cmpUsing_eq_lt
  given: (a b : α)
  statement: (cmpUsing lt a b = Ordering.lt) = lt a b
  proof: by
  simp only [cmpUsing, Ordering.ite_eq_lt_distrib, ite_self, if_false_right, and_true, reduceCtorEq]

@[simp]

中文:
定理 cmpUsing_eq_lt
  条件: (a b : α)
  结论: (cmpUsing lt a b = Ordering.lt) = lt a b
  证明: by
  simp only [cmpUsing, Ordering.ite_eq_lt_distrib, ite_self, if_false_right, and_true, reduceCtorEq]

@[simp]

Depends on / 依赖: Ordering, Ordering.ite_eq_lt_distrib, and_true, cmpUsing, if_false_right, ite_eq_lt_distrib, ite_self, reduceCtorEq
-/
theorem cmpUsing_eq_lt (a b : α) : (cmpUsing lt a b = Ordering.lt) = lt a b := by
  simp only [cmpUsing, Ordering.ite_eq_lt_distrib, ite_self, if_false_right, and_true, reduceCtorEq]

@[simp]
/--
theorem `cmpUsing_eq_gt` / 定理 `cmpUsing_eq_gt`

English:
theorem cmpUsing_eq_gt
  given: [IsStrictOrder α lt] (a b : α)
  statement: cmpUsing lt a b = Ordering.gt ↔ lt b a
  proof: by
  simp only [cmpUsing, Ordering.ite_eq_gt_distrib, if_false_right, and_true, if_false_left,
    and_iff_right_iff_imp, reduceCtorEq]
  exact fun hba hab => (irrefl a) (_root_.trans hab hba)

@[simp]

中文:
定理 cmpUsing_eq_gt
  条件: [是Strict序 α lt] (a b : α)
  结论: cmpUsing lt a b = Ordering.gt ↔ lt b a
  证明: by
  simp only [cmpUsing, Ordering.ite_eq_gt_distrib, if_false_right, and_true, if_false_left,
    and_iff_right_iff_imp, reduceCtorEq]
  exact fun hba hab => (irrefl a) (_root_.trans hab hba)

@[simp]

Depends on / 依赖: Ordering, Ordering.ite_eq_gt_distrib, _root_, _root_.trans, and_iff_right_iff_imp, and_true, cmpUsing, if_false_left, if_false_right, irrefl, ite_eq_gt_distrib, reduceCtorEq
-/
theorem cmpUsing_eq_gt [IsStrictOrder α lt] (a b : α) : cmpUsing lt a b = Ordering.gt ↔ lt b a := by
  simp only [cmpUsing, Ordering.ite_eq_gt_distrib, if_false_right, and_true, if_false_left,
    and_iff_right_iff_imp, reduceCtorEq]
  exact fun hba hab => (irrefl a) (_root_.trans hab hba)

@[simp]
/--
theorem `cmpUsing_eq_eq` / 定理 `cmpUsing_eq_eq`

English:
theorem cmpUsing_eq_eq
  given: (a b : α)
  statement: cmpUsing lt a b = Ordering.eq ↔ ¬lt a b ∧ ¬lt b a
  proof: by simp

中文:
定理 cmpUsing_eq_eq
  条件: (a b : α)
  结论: cmpUsing lt a b = Ordering.eq ↔ ¬lt a b ∧ ¬lt b a
  证明: by simp
-/
theorem cmpUsing_eq_eq (a b : α) : cmpUsing lt a b = Ordering.eq ↔ ¬lt a b ∧ ¬lt b a := by simp

end
