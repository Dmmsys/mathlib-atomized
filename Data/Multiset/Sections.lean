/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# Sections of a multiset
-/

@[expose] public section

assert_not_exists Ring

namespace Multiset

variable {α : Type*}

section Sections

/--
Definition of `Sections` / `Sections` 的定义

English:
definition Sections
  signature: (s : Multiset (Multiset α))
  body: Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]

中文:
定义 Sections
  签名: (s : Multiset (Multiset α))
  定义体: Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]

Depends on / 依赖: Multiset, Multiset.cons, Multiset.recOn, bind_bind, c.map, cons_swap, map_bind, s.bind
-/
def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]

@[simp]
/--
theorem `sections_zero` / 定理 `sections_zero`

English:
theorem sections_zero
  statement: Sections (0 : Multiset (Multiset α)) = {0}
  proof: rfl

@[simp]

中文:
定理 sections_zero
  结论: Sections (0 : Multiset (Multiset α)) = {0}
  证明: rfl

@[simp]
-/
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl

@[simp]
/--
theorem `sections_cons` / 定理 `sections_cons`

English:
theorem sections_cons
  given: (s : Multiset (Multiset α)) (m : Multiset α)
  proof: recOn_cons m s

中文:
定理 sections_cons
  条件: (s : Multiset (Multiset α)) (m : Multiset α)
  证明: recOn_cons m s

Depends on / 依赖: recOn_cons
-/
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s

/--
theorem `coe_sections` / 定理 `coe_sections`

English:
theorem coe_sections

中文:
定理 coe_sections
-/
theorem coe_sections :
    forall l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sections]
    rw [← cons_coe]; rw [sections_cons]; rw [bind_map_comm]; rw [coe_sections l]
    simp [Function.comp_def, List.flatMap]

@[simp]
/--
theorem `sections_add` / 定理 `sections_add`

English:
theorem sections_add
  given: (s t : Multiset (Multiset α))
  proof: Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]

中文:
定理 sections_add
  条件: (s t : Multiset (Multiset α))
  证明: Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]

Depends on / 依赖: Multiset, Multiset.induction_on, bind_assoc, bind_map, induction_on, map_bind
-/
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map (m + ·) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]

/--
theorem `mem_sections` / 定理 `mem_sections`

English:
theorem mem_sections
  given: {s : Multiset (Multiset α)}
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih, rel_cons_left, eq_comm]

中文:
定理 mem_sections
  条件: {s : Multiset (Multiset α)}
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih, rel_cons_left, eq_comm]

Depends on / 依赖: Multiset, Multiset.induction_on, eq_comm, induction_on, rel_cons_left
-/
theorem mem_sections {s : Multiset (Multiset α)} :
    forall {a}, a in Sections s ↔ s.Rel (fun s a => a in s) a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih, rel_cons_left, eq_comm]

/--
theorem `card_sections` / 定理 `card_sections`

English:
theorem card_sections
  given: {s : Multiset (Multiset α)}
  statement: card (Sections s) = prod (s.map card)
  proof: Multiset.induction_on s (by simp) (by simp +contextual)

中文:
定理 card_sections
  条件: {s : Multiset (Multiset α)}
  结论: card (Sections s) = 乘积 (s.map card)
  证明: Multiset.induction_on s (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp +contextual)

end Sections

end Multiset
