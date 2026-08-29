/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses

/-!
# Lexicographic ordering of lists.

The lexicographic order on `List α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `Mathlib/Combinatorics/Colex.lean`: Colexicographic order on finite sets.
* `Mathlib/Data/PSigma/Order.lean`: Lexicographic order on `Σ' i, α i`.
* `Mathlib/Order/PiLex.lean`: Lexicographic order on `Πₗ i, α i`.
* `Mathlib/Data/Sigma/Order.lean`: Lexicographic order on `Σ i, α i`.
* `Mathlib/Data/Prod/Lex.lean`: Lexicographic order on `α × β`.
-/

public section


namespace List

open Nat

universe u

variable {α : Type u}


/--
theorem `lex_cons_iff` / 定理 `lex_cons_iff`

English:
theorem lex_cons_iff
  given: {r : α -> α -> Prop} [Std.Irrefl r] {a l₁ l₂}
  proof: ⟨fun h => by obtain - | h | h := h; exacts [(irrefl_of r a h).elim, h], Lex.cons⟩

中文:
定理 lex_cons_iff
  条件: {r : α -> α -> 命题} [Std.Irrefl r] {a l₁ l₂}
  证明: ⟨fun h => by obtain - | h | h := h; exacts [(irrefl_of r a h).elim, h], Lex.cons⟩

Depends on / 依赖: Lex.cons, exacts, irrefl_of
-/
theorem lex_cons_iff {r : α -> α -> Prop} [Std.Irrefl r] {a l₁ l₂} :
    Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂ :=
  ⟨fun h => by obtain - | h | h := h; exacts [(irrefl_of r a h).elim, h], Lex.cons⟩

/--
theorem `lex_nil_or_eq_nil` / 定理 `lex_nil_or_eq_nil`

English:
theorem lex_nil_or_eq_nil
  given: {r : α -> α -> Prop} (l : List α)
  statement: List.Lex r [] l ∨ l = []
  proof: match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil

@[simp]

中文:
定理 lex_nil_or_eq_nil
  条件: {r : α -> α -> 命题} (l : 列表 α)
  结论: 列表.Lex r [] l ∨ l = []
  证明: match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil

@[simp]

Depends on / 依赖: Or.inr
-/
theorem lex_nil_or_eq_nil {r : α -> α -> Prop} (l : List α) : List.Lex r [] l ∨ l = [] :=
  match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil

@[simp]
/--
theorem `lex_singleton_iff` / 定理 `lex_singleton_iff`

English:
theorem lex_singleton_iff
  given: {r : α -> α -> Prop} (a b : α)
  statement: List.Lex r [a] [b] ↔ r a b
  proof: ⟨fun | .rel h => h, .rel⟩

中文:
定理 lex_singleton_iff
  条件: {r : α -> α -> 命题} (a b : α)
  结论: 列表.Lex r [a] [b] ↔ r a b
  证明: ⟨fun | .rel h => h, .rel⟩
-/
theorem lex_singleton_iff {r : α -> α -> Prop} (a b : α) : List.Lex r [a] [b] ↔ r a b :=
  ⟨fun | .rel h => h, .rel⟩

namespace Lex

/--
Instance `isOrderConnected` / 实例 `isOrderConnected`

English:
instance isOrderConnected
  signature: (r : α -> α -> Prop) [IsOrderConnected α r] [Std.Trichotomous r]
  body: aux where
    aux
    | _, [], _ :: _, nil => Or.inr nil
    | _, [], _ :: _, rel _ => Or.inr nil
    | _, [], _ :: _, cons _ => Or.inr nil
    | _, _ :: _, _ :: _, nil => Or.inl nil
    | _ :: _, b :: _, _ :: _, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, c

中文:
实例 isOrderConnected
  签名: (r : α -> α -> 命题) [是OrderConnected α r] [Std.三歧 r]
  定义体: aux where
    aux
    | _, [], _ :: _, nil => Or.inr nil
    | _, [], _ :: _, rel _ => Or.inr nil
    | _, [], _ :: _, cons _ => Or.inr nil
    | _, _ :: _, _ :: _, nil => Or.inl nil
    | _ :: _, b :: _, _ :: _, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, c
-/
instance isOrderConnected (r : α -> α -> Prop) [IsOrderConnected α r] [Std.Trichotomous r] :
    IsOrderConnected (List α) (Lex r) where
  conn := aux where
    aux
    | _, [], _ :: _, nil => Or.inr nil
    | _, [], _ :: _, rel _ => Or.inr nil
    | _, [], _ :: _, cons _ => Or.inr nil
    | _, _ :: _, _ :: _, nil => Or.inl nil
    | _ :: _, b :: _, _ :: _, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, cons h => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
      · exact (aux _ l₂ _ h).imp cons cons
      · exact Or.inr (rel ab)

/--
Instance `trichotomous` / 实例 `trichotomous`

English:
instance trichotomous
  signature: (r : α -> α -> Prop) [Std.Trichotomous r]
  body: aux where
    aux
    | [], [], _, _ => rfl
.elim | [], _ :: _, hab, _ => hab nil
.elim | _ :: _, [], _, hba => hba nil
    | a :: l₁, b :: l₂, hab, hba => by
      obtain rfl := Std.Trichotomous.trichotomous a b (mt rel hab) (mt rel hba)
      rw [aux l₁ l₂ (mt cons hab) (mt cons hba)]

中文:
实例 trichotomous
  签名: (r : α -> α -> 命题) [Std.三歧 r]
  定义体: aux where
    aux
    | [], [], _, _ => rfl
.elim | [], _ :: _, hab, _ => hab nil
.elim | _ :: _, [], _, hba => hba nil
    | a :: l₁, b :: l₂, hab, hba => by
      obtain rfl := Std.Trichotomous.trichotomous a b (mt rel hab) (mt rel hba)
      rw [aux l₁ l₂ (mt cons hab) (mt cons hba)]
-/
instance trichotomous (r : α -> α -> Prop) [Std.Trichotomous r] : Std.Trichotomous (Lex r) where
  trichotomous := aux where
    aux
    | [], [], _, _ => rfl
.elim | [], _ :: _, hab, _ => hab nil
.elim | _ :: _, [], _, hba => hba nil
    | a :: l₁, b :: l₂, hab, hba => by
      obtain rfl := Std.Trichotomous.trichotomous a b (mt rel hab) (mt rel hba)
      rw [aux l₁ l₂ (mt cons hab) (mt cons hba)]

/--
Instance `asymm` / 实例 `asymm`

English:
instance asymm
  signature: (r : α -> α -> Prop) [Std.Asymm r]
  body: aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => _root_.asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => _root_.asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => _root_.asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂

中文:
实例 asymm
  签名: (r : α -> α -> 命题) [Std.Asymm r]
  定义体: aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => _root_.asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => _root_.asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => _root_.asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂
-/
instance asymm (r : α -> α -> Prop) [Std.Asymm r] : Std.Asymm (Lex r) where
  asymm := aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => _root_.asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => _root_.asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => _root_.asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂

/--
Instance `decidableRel` / 实例 `decidableRel`

English:
instance decidableRel
  signature: [DecidableEq α] (r : α -> α -> Prop) [DecidableRel r]
  body: decidableRel r l₁ l₂
    refine decidable_of_iff (r a b ∨ a = b ∧ Lex r l₁ l₂) ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with (h | ⟨rfl, h⟩)
      · exact Lex.rel h
      · exact Lex.cons h
    · rcases h with (_ | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩

中文:
实例 decidableRel
  签名: [DecidableEq α] (r : α -> α -> 命题) [DecidableRel r]
  定义体: decidableRel r l₁ l₂
    refine decidable_of_iff (r a b ∨ a = b ∧ Lex r l₁ l₂) ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with (h | ⟨rfl, h⟩)
      · exact Lex.rel h
      · exact Lex.cons h
    · rcases h with (_ | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩

Depends on / 依赖: decidableRel
-/
instance decidableRel [DecidableEq α] (r : α -> α -> Prop) [DecidableRel r] : DecidableRel (Lex r)
  | l₁, [] => isFalse fun h => by cases h
  | [], _ :: _ => isTrue Lex.nil
  | a :: l₁, b :: l₂ => by
    haveI := decidableRel r l₁ l₂
    refine decidable_of_iff (r a b ∨ a = b ∧ Lex r l₁ l₂) ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with (h | ⟨rfl, h⟩)
      · exact Lex.rel h
      · exact Lex.cons h
    · rcases h with (_ | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩

/--
theorem `append_right` / 定理 `append_right`

English:
theorem append_right
  given: (r : α -> α -> Prop)
  statement: forall {s₁ s₂} (t), Lex r s₁ s₂ -> Lex r s₁ (s₂ ++ t)

中文:
定理 append_right
  条件: (r : α -> α -> 命题)
  结论: 对任意 {s₁ s₂} (t), Lex r s₁ s₂ -> Lex r s₁ (s₂ ++ t)
-/
theorem append_right (r : α -> α -> Prop) : forall {s₁ s₂} (t), Lex r s₁ s₂ -> Lex r s₁ (s₂ ++ t)
  | _, _, _, nil => nil
  | _, _, _, cons h => cons (append_right r _ h)
  | _, _, _, rel r => rel r

/--
theorem `append_left` / 定理 `append_left`

English:
theorem append_left
  given: (R : α -> α -> Prop) {t₁ t₂} (h : Lex R t₁ t₂)
  statement: forall s, Lex R (s ++ t₁) (s ++ t₂)

中文:
定理 append_left
  条件: (R : α -> α -> 命题) {t₁ t₂} (h : Lex R t₁ t₂)
  结论: 对任意 s, Lex R (s ++ t₁) (s ++ t₂)
-/
theorem append_left (R : α -> α -> Prop) {t₁ t₂} (h : Lex R t₁ t₂) : forall s, Lex R (s ++ t₁) (s ++ t₂)
  | [] => h
  | _ :: l => cons (append_left R h l)

/--
theorem `imp` / 定理 `imp`

English:
theorem imp
  given: {r s : α -> α -> Prop} (H : forall a b, r a b -> s a b)
  statement: forall l₁ l₂, Lex r l₁ l₂ -> Lex s l₁ l₂

中文:
定理 imp
  条件: {r s : α -> α -> 命题} (H : 对任意 a b, r a b -> s a b)
  结论: 对任意 l₁ l₂, Lex r l₁ l₂ -> Lex s l₁ l₂
-/
theorem imp {r s : α -> α -> Prop} (H : forall a b, r a b -> s a b) : forall l₁ l₂, Lex r l₁ l₂ -> Lex s l₁ l₂
  | _, _, nil => nil
  | _, _, cons h => cons (imp H _ _ h)
  | _, _, rel r => rel (H _ _ r)

/--
theorem `to_ne` / 定理 `to_ne`

English:
theorem to_ne
  statement: forall {l₁ l₂ : List α}, Lex (· != ·) l₁ l₂ -> l₁ != l₂

中文:
定理 to_ne
  结论: 对任意 {l₁ l₂ : 列表 α}, Lex (· != ·) l₁ l₂ -> l₁ != l₂
-/
theorem to_ne : forall {l₁ l₂ : List α}, Lex (· != ·) l₁ l₂ -> l₁ != l₂
  | _, _, cons h, e => to_ne h (List.cons.inj e).2
  | _, _, rel r, e => r (List.cons.inj e).1

/--
theorem `_root_.Decidable.List.Lex.ne_iff` / 定理 `_root_.Decidable.List.Lex.ne_iff`

English:
theorem _root_.Decidable.List.Lex.ne_iff
  statement: [DecidableEq α] {l₁ l₂ : List α}
  proof: ⟨to_ne, fun h => by
    induction l₁ generalizing l₂ <;> rcases l₂ with - | ⟨b, l₂⟩
    · contradiction
    · apply nil
    · exact (not_lt_of_ge H).elim (succ_pos _)
    case cons.cons a l₁ IH =>
      by_cases ab : a = b
      · subst b
exact .cons IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
  

中文:
定理 _root_.可判定.列表.Lex.ne_iff
  结论: [DecidableEq α] {l₁ l₂ : 列表 α}
  证明: ⟨to_ne, fun h => by
    induction l₁ generalizing l₂ <;> rcases l₂ with - | ⟨b, l₂⟩
    · contradiction
    · apply nil
    · exact (not_lt_of_ge H).elim (succ_pos _)
    case cons.cons a l₁ IH =>
      by_cases ab : a = b
      · subst b
exact .cons IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
  

Depends on / 依赖: congr_arg, cons.cons, generalizing, le_of_succ_le_succ, not_lt_of_ge, succ_pos, to_ne
-/
theorem _root_.Decidable.List.Lex.ne_iff [DecidableEq α] {l₁ l₂ : List α}
    (H : length l₁ <= length l₂) : Lex (· != ·) l₁ l₂ ↔ l₁ != l₂ :=
  ⟨to_ne, fun h => by
    induction l₁ generalizing l₂ <;> rcases l₂ with - | ⟨b, l₂⟩
    · contradiction
    · apply nil
    · exact (not_lt_of_ge H).elim (succ_pos _)
    case cons.cons a l₁ IH =>
      by_cases ab : a = b
      · subst b
exact .cons IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
      · exact .rel ab ⟩

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {l₁ l₂ : List α} (H : length l₁ <= length l₂)
  statement: Lex (· != ·) l₁ l₂ ↔ l₁ != l₂
  proof: by
  classical
  exact Decidable.List.Lex.ne_iff H

中文:
定理 ne_iff
  条件: {l₁ l₂ : 列表 α} (H : length l₁ <= length l₂)
  结论: Lex (· != ·) l₁ l₂ ↔ l₁ != l₂
  证明: by
  classical
  exact Decidable.List.Lex.ne_iff H

Depends on / 依赖: Decidable, Decidable.List.Lex.ne_iff, classical, ne_iff
-/
theorem ne_iff {l₁ l₂ : List α} (H : length l₁ <= length l₂) : Lex (· != ·) l₁ l₂ ↔ l₁ != l₂ := by
  classical
  exact Decidable.List.Lex.ne_iff H

end Lex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : LinearOrder (List α)
  body: have : forall {r} [IsStrictTotalOrder α r], IsStrictTotalOrder (List α) (Lex r) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  linearOrderOfSTO (Lex (· < ·))

中文:
实例 [线性序
  签名: α] : 线性序 (列表 α)
  定义体: have : forall {r} [IsStrictTotalOrder α r], IsStrictTotalOrder (List α) (Lex r) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  linearOrderOfSTO (Lex (· < ·))

Depends on / 依赖: IsStrictTotalOrder, isStrictWeakOrder_of_isOrderConnected, linearOrderOfSTO
-/
instance [LinearOrder α] : LinearOrder (List α) :=
  have : forall {r} [IsStrictTotalOrder α r], IsStrictTotalOrder (List α) (Lex r) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  linearOrderOfSTO (Lex (· < ·))

--Note: this overrides an instance in core lean
/--
Instance `LE'` / 实例 `LE'`

English:
instance LE'
  signature: [LinearOrder α]
  body: Preorder.toLE

中文:
实例 LE'
  签名: [线性序 α]
  定义体: Preorder.toLE

Depends on / 依赖: Preorder, Preorder.toLE
-/
instance LE' [LinearOrder α] : LE (List α) :=
  Preorder.toLE

/--
theorem `lt_iff_lex_lt` / 定理 `lt_iff_lex_lt`

English:
theorem lt_iff_lex_lt
  given: [LT α] (l l' : List α)
  statement: List.lt l l' ↔ Lex (· < ·) l l'
  proof: by
  rw [List.lt]

中文:
定理 lt_iff_lex_lt
  条件: [LT α] (l l' : 列表 α)
  结论: 列表.lt l l' ↔ Lex (· < ·) l l'
  证明: by
  rw [List.lt]

Depends on / 依赖: List.lt
-/
theorem lt_iff_lex_lt [LT α] (l l' : List α) : List.lt l l' ↔ Lex (· < ·) l l' := by
  rw [List.lt]

/--
theorem `head_le_of_lt` / 定理 `head_le_of_lt`

English:
theorem head_le_of_lt
  given: [Preorder α] {a a' : α} {l l' : List α} (h : (a' :: l') < (a :: l))
  proof: match h with
  | .cons _ => le_rfl
  | .rel h => h.le

中文:
定理 head_le_of_lt
  条件: [预序 α] {a a' : α} {l l' : 列表 α} (h : (a' :: l') < (a :: l))
  证明: match h with
  | .cons _ => le_rfl
  | .rel h => h.le

Depends on / 依赖: h.le, le_rfl
-/
theorem head_le_of_lt [Preorder α] {a a' : α} {l l' : List α} (h : (a' :: l') < (a :: l)) :
    a' <= a :=
  match h with
  | .cons _ => le_rfl
  | .rel h => h.le

/--
theorem `head!_le_of_lt` / 定理 `head!_le_of_lt`

English:
theorem head!_le_of_lt
  given: [Preorder α] [Inhabited α] (l l' : List α) (h : l' < l) (hl' : l' != [])
  proof: by
  replace h : List.Lex (· < ·) l' l := h
  by_cases hl : l = []
  · simp [hl] at h
  · rw [← List.cons_head!_tail hl', ← List.cons_head!_tail hl] at h
    exact head_le_of_lt h

中文:
定理 head!_le_of_lt
  条件: [预序 α] [可居 α] (l l' : 列表 α) (h : l' < l) (hl' : l' != [])
  证明: by
  replace h : List.Lex (· < ·) l' l := h
  by_cases hl : l = []
  · simp [hl] at h
  · rw [← List.cons_head!_tail hl', ← List.cons_head!_tail hl] at h
    exact head_le_of_lt h
-/
theorem head!_le_of_lt [Preorder α] [Inhabited α] (l l' : List α) (h : l' < l) (hl' : l' != []) :
    l'.head! <= l.head! := by
  replace h : List.Lex (· < ·) l' l := h
  by_cases hl : l = []
  · simp [hl] at h
  · rw [← List.cons_head!_tail hl', ← List.cons_head!_tail hl] at h
    exact head_le_of_lt h

/--
theorem `cons_le_cons` / 定理 `cons_le_cons`

English:
theorem cons_le_cons
  given: [LinearOrder α] (a : α) {l l' : List α} (h : l' <= l)
  proof: by
  rw [le_iff_lt_or_eq] at h ⊢
  exact h.imp .cons (congr_arg _)

中文:
定理 cons_le_cons
  条件: [线性序 α] (a : α) {l l' : 列表 α} (h : l' <= l)
  证明: by
  rw [le_iff_lt_or_eq] at h ⊢
  exact h.imp .cons (congr_arg _)

Depends on / 依赖: congr_arg, h.imp, le_iff_lt_or_eq
-/
theorem cons_le_cons [LinearOrder α] (a : α) {l l' : List α} (h : l' <= l) :
    a :: l' <= a :: l := by
  rw [le_iff_lt_or_eq] at h ⊢
  exact h.imp .cons (congr_arg _)

end List
