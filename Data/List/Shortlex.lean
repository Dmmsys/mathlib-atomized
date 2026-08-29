/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum

/-!
# Shortlex ordering of lists.

Given a relation `r` on `α`, the shortlex order on `List α` is defined by `L < M` iff
* `L.length < M.length`
* `L.length = M.length` and `L < M` under the lexicographic ordering over `r` on lists

## Main results

We show that if `r` is well-founded, so too is the shortlex order over `r`

## See also

Related files are:
* `Mathlib/Data/List/Lex.lean`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded.lean`: Well-foundedness of lexicographic orders on `DFinsupp`
  and `Pi`.
-/

@[expose] public section

/-! ### shortlex ordering -/

namespace List

/--
Definition of `Shortlex` / `Shortlex` 的定义

English:
definition Shortlex
  signature: {α : Type*} (r : α -> α -> Prop)
  body: InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a => (a.length, a)

中文:
定义 Shortlex
  签名: {α : 类型} (r : α -> α -> 命题)
  定义体: InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a => (a.length, a)

Depends on / 依赖: InvImage, List.Lex, Prod.Lex, a.length, length
-/
def Shortlex {α : Type*} (r : α -> α -> Prop) : List α -> List α -> Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a => (a.length, a)

variable {α : Type*} {r : α -> α -> Prop}

/--
theorem `Shortlex.of_length_lt` / 定理 `Shortlex.of_length_lt`

English:
theorem Shortlex.of_length_lt
  given: {s t : List α} (h : s.length < t.length)
  statement: Shortlex r s t
  proof: Prod.Lex.left _ _ h

中文:
定理 Shortlex.of_length_lt
  条件: {s t : 列表 α} (h : s.length < t.length)
  结论: Shortlex r s t
  证明: Prod.Lex.left _ _ h

Depends on / 依赖: Prod.Lex.left
-/
theorem Shortlex.of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/--
theorem `Shortlex.of_lex` / 定理 `Shortlex.of_lex`

English:
theorem Shortlex.of_lex
  given: {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t)
  proof: by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

中文:
定理 Shortlex.of_lex
  条件: {s t : 列表 α} (len_eq : s.length = t.length) (h_lex : 列表.Lex r s t)
  证明: by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

Depends on / 依赖: Prod.lex_def.mpr, h_lex, len_eq, lex_def
-/
theorem Shortlex.of_lex {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩

/--
theorem `shortlex_def` / 定理 `shortlex_def`

English:
theorem shortlex_def
  given: {s t : List α}
  proof: Prod.lex_def

中文:
定理 shortlex_def
  条件: {s t : 列表 α}
  证明: Prod.lex_def

Depends on / 依赖: Prod.lex_def, lex_def
-/
theorem shortlex_def {s t : List α} :
    Shortlex r s t ↔ s.length < t.length ∨ s.length = t.length ∧ Lex r s t := Prod.lex_def

/--
theorem `shortlex_iff_lex` / 定理 `shortlex_iff_lex`

English:
theorem shortlex_iff_lex
  given: {s t : List α} (h : s.length = t.length)
  proof: by
  simp [shortlex_def, h]

中文:
定理 shortlex_iff_lex
  条件: {s t : 列表 α} (h : s.length = t.length)
  证明: by
  simp [shortlex_def, h]

Depends on / 依赖: shortlex_def
-/
theorem shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  simp [shortlex_def, h]

/--
theorem `shortlex_cons_iff` / 定理 `shortlex_cons_iff`

English:
theorem shortlex_cons_iff
  given: [Std.Irrefl r] {a : α} {s t : List α}
  proof: by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff

@[simp]

中文:
定理 shortlex_cons_iff
  条件: [Std.Irrefl r] {a : α} {s t : 列表 α}
  证明: by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff

@[simp]

Depends on / 依赖: List.lex_cons_iff, add_left_inj, add_lt_add_iff_right, length_cons, lex_cons_iff, shortlex_def
-/
theorem shortlex_cons_iff [Std.Irrefl r] {a : α} {s t : List α} :
    Shortlex r (a :: s) (a :: t) ↔ Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff

@[simp]
/--
theorem `not_shortlex_nil_right` / 定理 `not_shortlex_nil_right`

English:
theorem not_shortlex_nil_right
  given: {s : List α}
  statement: ¬ Shortlex r s []
  proof: by
  simp [shortlex_def]

中文:
定理 not_shortlex_nil_right
  条件: {s : 列表 α}
  结论: ¬ Shortlex r s []
  证明: by
  simp [shortlex_def]

Depends on / 依赖: shortlex_def
-/
theorem not_shortlex_nil_right {s : List α} : ¬ Shortlex r s [] := by
  simp [shortlex_def]

/--
theorem `shortlex_nil_or_eq_nil` / 定理 `shortlex_nil_or_eq_nil`

English:
theorem shortlex_nil_or_eq_nil
  statement: forall s : List α, Shortlex r [] s ∨ s = []

中文:
定理 shortlex_nil_or_eq_nil
  结论: 对任意 s : 列表 α, Shortlex r [] s ∨ s = []
-/
theorem shortlex_nil_or_eq_nil : forall s : List α, Shortlex r [] s ∨ s = []
  | [] => .inr rfl
| _ :: tail => .inl .of_length_lt tail.length.succ_pos

@[simp]
/--
theorem `shortlex_singleton_iff` / 定理 `shortlex_singleton_iff`

English:
theorem shortlex_singleton_iff
  given: (a b : α)
  statement: Shortlex r [a] [b] ↔ r a b
  proof: by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, lex_singleton_iff, true_and,
    false_or]

中文:
定理 shortlex_singleton_iff
  条件: (a b : α)
  结论: Shortlex r [a] [b] ↔ r a b
  证明: by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, lex_singleton_iff, true_and,
    false_or]

Depends on / 依赖: false_or, length_singleton, lex_singleton_iff, lt_self_iff_false, shortlex_def, true_and
-/
theorem shortlex_singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, lex_singleton_iff, true_and,
    false_or]

namespace Shortlex

/--
Instance `trichotomous` / 实例 `trichotomous`

English:
instance trichotomous
  signature: [Std.Trichotomous r]
  body: ⟨(InvImage.trichotomous (by simp [Function.Injective])).trichotomous⟩

中文:
实例 trichotomous
  签名: [Std.三歧 r]
  定义体: ⟨(InvImage.trichotomous (by simp [Function.Injective])).trichotomous⟩

Depends on / 依赖: Function, Function.Injective, Injective, InvImage, InvImage.trichotomous, trichotomous
-/
instance trichotomous [Std.Trichotomous r] : Std.Trichotomous (Shortlex r) :=
  ⟨(InvImage.trichotomous (by simp [Function.Injective])).trichotomous⟩

/--
Instance `asymm` / 实例 `asymm`

English:
instance asymm
  signature: [Std.Asymm r]
  body: inferInstanceAs Std.Asymm (InvImage _ _)

中文:
实例 asymm
  签名: [Std.Asymm r]
  定义体: inferInstanceAs Std.Asymm (InvImage _ _)

Depends on / 依赖: InvImage, Std.Asymm
-/
instance asymm [Std.Asymm r] : Std.Asymm (Shortlex r) :=
inferInstanceAs Std.Asymm (InvImage _ _)

/--
theorem `append_right` / 定理 `append_right`

English:
theorem append_right
  given: {s₁ s₂ : List α} (t : List α) (h : Shortlex r s₁ s₂)
  proof: by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    lia
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append]; rw [List.length_cons]
    lia

中文:
定理 append_right
  条件: {s₁ s₂ : 列表 α} (t : 列表 α) (h : Shortlex r s₁ s₂)
  证明: by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    lia
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append]; rw [List.length_cons]
    lia

Depends on / 依赖: List.append_nil, List.length_append, List.length_cons, append_nil, length_append, length_cons, of_length_lt, shortlex_def, shortlex_def.mp
-/
theorem append_right {s₁ s₂ : List α} (t : List α) (h : Shortlex r s₁ s₂) :
    Shortlex r s₁ (s₂ ++ t) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    lia
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append]; rw [List.length_cons]
    lia

/--
theorem `append_left` / 定理 `append_left`

English:
theorem append_left
  given: {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α)
  proof: by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]; rw [List.length_append]
    lia
  cases s with
  | nil =>
    rw [List.nil_append]; rw [List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

中文:
定理 append_left
  条件: {t₁ t₂ : 列表 α} (h : Shortlex r t₁ t₂) (s : 列表 α)
  证明: by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]; rw [List.length_append]
    lia
  cases s with
  | nil =>
    rw [List.nil_append]; rw [List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

Depends on / 依赖: List.Lex.append_left, List.cons_append, List.length_append, List.length_cons, List.nil_append, add_left_inj, add_right_inj, append_left, cons_append, length_append, length_cons, nil_append, of_length_lt, of_lex, shortlex_def, shortlex_def.mp
-/
theorem append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) :
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]; rw [List.length_append]
    lia
  cases s with
  | nil =>
    rw [List.nil_append]; rw [List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

section WellFounded

variable {h : WellFounded r}

/--
theorem `_root_.Acc.shortlex` / 定理 `_root_.Acc.shortlex`

English:
theorem _root_.Acc.shortlex
  statement: {a : α} {b : List α} (aca : Acc r a)
  proof: by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction acb with
    | intro xb _ ihb =>
      refine Acc.intro (xa :: xb) fun p lt => ?_
      rcases shortlex_def.mp lt with h1 | ⟨h2len, h2lex⟩
      · exact ih _ h1
      · cases h2lex with
        | nil => simp at h2len
        | @cons x xs _ h =>
          simp only [length_cons, add_left_inj] at h2len
          refine ihb _ (of_lex h2len h) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl
        | @rel x xs _ _ h =>
          simp only [List.length_cons, add_left_inj] at h2len
          refine iha _ h (ih xs (by rw [h2len]; simp)) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl

中文:
定理 _root_.Acc.shortlex
  结论: {a : α} {b : 列表 α} (aca : Acc r a)
  证明: by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction acb with
    | intro xb _ ihb =>
      refine Acc.intro (xa :: xb) fun p lt => ?_
      rcases shortlex_def.mp lt with h1 | ⟨h2len, h2lex⟩
      · exact ih _ h1
      · cases h2lex with
        | nil => simp at h2len
        | @cons x xs _ h =>
          simp only [length_cons, add_left_inj] at h2len
          refine ihb _ (of_lex h2len h) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl
        | @rel x xs _ _ h =>
          simp only [List.length_cons, add_left_inj] at h2len
          refine iha _ h (ih xs (by rw [h2len]; simp)) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl
-/
private theorem _root_.Acc.shortlex {a : α} {b : List α} (aca : Acc r a)
    (acb : Acc (Shortlex r) b)
    (ih : forall s : List α, s.length < (a :: b).length -> Acc (Shortlex r) s) :
    Acc (Shortlex r) (a :: b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction acb with
    | intro xb _ ihb =>
      refine Acc.intro (xa :: xb) fun p lt => ?_
      rcases shortlex_def.mp lt with h1 | ⟨h2len, h2lex⟩
      · exact ih _ h1
      · cases h2lex with
        | nil => simp at h2len
        | @cons x xs _ h =>
          simp only [length_cons, add_left_inj] at h2len
          refine ihb _ (of_lex h2len h) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl
        | @rel x xs _ _ h =>
          simp only [List.length_cons, add_left_inj] at h2len
          refine iha _ h (ih xs (by rw [h2len]; simp)) fun l hl => ?_
          apply ih
          rw [List.length_cons]; rw [← h2len]
          exact hl

/--
theorem `wf` / 定理 `wf`

English:
theorem wf
  given: (h : WellFounded r)
  statement: WellFounded (Shortlex r)
  proof: .intro fun a => by
  induction len_a : a.length using Nat.caseStrongRecOn generalizing a with
  | zero =>
    rw [List.length_eq_zero_iff] at len_a
    rw [len_a]
exact Acc.intro _ fun _ ylt => (not_shortlex_nil_right ylt).elim
  | ind n ih =>
    obtain ⟨head, tail, rfl⟩ := List.exists_of_length_succ a len_a
    rw [List.length_cons]; rw [add_left_inj] at len_a
    apply Acc.shortlex (WellFounded.apply h head) (ih n le_rfl tail len_a)
    intro l ll
    apply ih l.length _ _ rfl
    rw [← len_a]
    exact Nat.le_of_lt_succ ll

中文:
定理 wf
  条件: (h : 良基 r)
  结论: 良基 (Shortlex r)
  证明: .intro fun a => by
  induction len_a : a.length using Nat.caseStrongRecOn generalizing a with
  | zero =>
    rw [List.length_eq_zero_iff] at len_a
    rw [len_a]
exact Acc.intro _ fun _ ylt => (not_shortlex_nil_right ylt).elim
  | ind n ih =>
    obtain ⟨head, tail, rfl⟩ := List.exists_of_length_succ a len_a
    rw [List.length_cons]; rw [add_left_inj] at len_a
    apply Acc.shortlex (WellFounded.apply h head) (ih n le_rfl tail len_a)
    intro l ll
    apply ih l.length _ _ rfl
    rw [← len_a]
    exact Nat.le_of_lt_succ ll

Depends on / 依赖: Acc.intro, Acc.shortlex, List.exists_of_length_succ, List.length_cons, List.length_eq_zero_iff, Nat.caseStrongRecOn, Nat.le_of_lt_succ, WellFounded, WellFounded.apply, a.length, add_left_inj, caseStrongRecOn, exists_of_length_succ, generalizing, l.length, le_of_lt_succ, le_rfl, len_a, length, length_cons
-/
theorem wf (h : WellFounded r) : WellFounded (Shortlex r) := .intro fun a => by
  induction len_a : a.length using Nat.caseStrongRecOn generalizing a with
  | zero =>
    rw [List.length_eq_zero_iff] at len_a
    rw [len_a]
exact Acc.intro _ fun _ ylt => (not_shortlex_nil_right ylt).elim
  | ind n ih =>
    obtain ⟨head, tail, rfl⟩ := List.exists_of_length_succ a len_a
    rw [List.length_cons]; rw [add_left_inj] at len_a
    apply Acc.shortlex (WellFounded.apply h head) (ih n le_rfl tail len_a)
    intro l ll
    apply ih l.length _ _ rfl
    rw [← len_a]
    exact Nat.le_of_lt_succ ll

end WellFounded

end Shortlex

end List
