/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Init

/-! ### List.modifyLast -/

public section

variable {α : Type*}

namespace List

/--
theorem `modifyLast.go_concat` / 定理 `modifyLast.go_concat`

English:
theorem modifyLast.go_concat
  given: (f : α -> α) (a : α) (tl : List α) (r : Array α)
  proof: by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; simp
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go]; rw [modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat _ _ tl _]; rw [modifyLast.go_concat _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.toList_push, nil_append,
      append_assoc]

中文:
定理 modifyLast.go_concat
  条件: (f : α -> α) (a : α) (tl : 列表 α) (r : 数组 α)
  证明: by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; simp
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go]; rw [modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat _ _ tl _]; rw [modifyLast.go_concat _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.toList_push, nil_append,
      append_assoc]
-/
private theorem modifyLast.go_concat (f : α -> α) (a : α) (tl : List α) (r : Array α) :
    modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[]) := by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; simp
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go]; rw [modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat _ _ tl _]; rw [modifyLast.go_concat _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.toList_push, nil_append,
      append_assoc]

/--
theorem `modifyLast_concat` / 定理 `modifyLast_concat`

English:
theorem modifyLast_concat
  given: (f : α -> α) (a : α) (l : List α)
  proof: by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat]; rw [Array.toListAppend_eq]; rw [Array.toList_push]; rw [List.toList_toArray]; rw [nil_append]; rw [cons_append]; rw [nil_append]; rw [cons_inj_right]
    exact modifyLast_concat _ _ tl

中文:
定理 modifyLast_concat
  条件: (f : α -> α) (a : α) (l : 列表 α)
  证明: by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat]; rw [Array.toListAppend_eq]; rw [Array.toList_push]; rw [List.toList_toArray]; rw [nil_append]; rw [cons_append]; rw [nil_append]; rw [cons_inj_right]
    exact modifyLast_concat _ _ tl

Depends on / 依赖: Array.toListAppend_eq, Array.toList_push, List.toList_toArray, append_ne_nil_of_right_ne_nil, cons_append, cons_inj_right, cons_ne_nil, go_concat, modifyLast, modifyLast.go, modifyLast.go_concat, modifyLast_concat, nil_append, toListAppend_eq, toList_push, toList_toArray
-/
theorem modifyLast_concat (f : α -> α) (a : α) (l : List α) :
    modifyLast f (l ++ [a]) = l ++ [f a] := by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat]; rw [Array.toListAppend_eq]; rw [Array.toList_push]; rw [List.toList_toArray]; rw [nil_append]; rw [cons_append]; rw [nil_append]; rw [cons_inj_right]
    exact modifyLast_concat _ _ tl

/--
theorem `modifyLast_append_of_right_ne_nil` / 定理 `modifyLast_append_of_right_ne_nil`

English:
theorem modifyLast_append_of_right_ne_nil
  given: (f : α -> α) (l₁ l₂ : List α) (_ : l₂ != [])
  proof: by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil =>
      simp only [modifyLast, modifyLast.go, Array.toListAppend_eq, nil_append]
      exact modifyLast_concat _ hd _
    | cons hd' tl' =>
      rw [append_cons]; rw [← nil_append (hd :: hd' :: tl')]; rw [append_cons [], nil_append,
        modifyLast_append_of_right_ne_nil _ (l₁ ++ [hd]) (hd' :: tl') _,
        modifyLast_append_of_right_ne_nil _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

中文:
定理 modifyLast_append_of_right_ne_nil
  条件: (f : α -> α) (l₁ l₂ : 列表 α) (_ : l₂ != [])
  证明: by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil =>
      simp only [modifyLast, modifyLast.go, Array.toListAppend_eq, nil_append]
      exact modifyLast_concat _ hd _
    | cons hd' tl' =>
      rw [append_cons]; rw [← nil_append (hd :: hd' :: tl')]; rw [append_cons [], nil_append,
        modifyLast_append_of_right_ne_nil _ (l₁ ++ [hd]) (hd' :: tl') _,
        modifyLast_append_of_right_ne_nil _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

Depends on / 依赖: Array.toListAppend_eq, all_goals, append_assoc, append_cons, cons_ne_nil, modifyLast, modifyLast.go, modifyLast_append_of_right_ne_nil, modifyLast_concat, nil_append, toListAppend_eq
-/
theorem modifyLast_append_of_right_ne_nil (f : α -> α) (l₁ l₂ : List α) (_ : l₂ != []) :
    modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂ := by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil =>
      simp only [modifyLast, modifyLast.go, Array.toListAppend_eq, nil_append]
      exact modifyLast_concat _ hd _
    | cons hd' tl' =>
      rw [append_cons]; rw [← nil_append (hd :: hd' :: tl')]; rw [append_cons [], nil_append,
        modifyLast_append_of_right_ne_nil _ (l₁ ++ [hd]) (hd' :: tl') _,
        modifyLast_append_of_right_ne_nil _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

end List
