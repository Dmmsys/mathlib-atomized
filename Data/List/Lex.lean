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

/-! ### lexicographic ordering -/

/-
**List.lex_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lex_cons_iff {r : α -> α -> Prop} [Std.Irrefl r] {a l₁ l₂} : Lex r (a :: l
₁) (a :: l₂) ↔ Lex r l₁ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
### lexicographic ordering
-/
theorem lex_cons_iff {r : α → α → Prop} [Std.Irrefl r] {a l₁ l₂} :
    Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂ :=
  ⟨fun h => by obtain - | h | h := h; exacts [(irrefl_of r a h).elim, h], Lex.cons⟩
/-
**List.lex_nil_or_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lex_nil_or_eq_nil {r : α -> α -> Prop} (l : List α) : List.Lex r [] l ∨ l 
= []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lex_nil_or_eq_nil {r : α → α → Prop} (l : List α) : List.Lex r [] l ∨ l = [] :=
  match l with
  | [] => Or.inr rfl
  | _ :: _ => .inl .nil

@[simp]
/-
**List.lex_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lex_singleton_iff {r : α -> α -> Prop} (a b : α) : List.Lex r [a] [b] ↔ r 
a b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lex_singleton_iff {r : α → α → Prop} (a b : α) : List.Lex r [a] [b] ↔ r a b :=
  ⟨fun | .rel h => h, .rel⟩

namespace Lex

/-
**List.Lex.isOrderConnected** 是 Mathlib 中的一个实例，位于命名空间 `List.Lex`。
形式化陈述：isOrderConnected (r : α -> α -> Prop) [IsOrderConnected α r] [Std.Trichoto
mous r] : IsOrderConnected (List α) (Lex r) where conn
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.Lex.0.List.Lex.isOrderConnected.aux`：∀ {α : T
ype u} (r : α → α → Prop) [IsOrderConnected α r] [Std.Trichotomous r] (x x_1 x_2
 : List α),   List.Lex r x x_2 → List.Lex r x x_1 ∨ …
-/
instance isOrderConnected (r : α → α → Prop) [IsOrderConnected α r] [Std.Trichotomous r] :
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
/-
**List.Lex.trichotomous** 是 Mathlib 中的一个实例，位于命名空间 `List.Lex`。
形式化陈述：trichotomous (r : α -> α -> Prop) [Std.Trichotomous r] : Std.Trichotomous 
(Lex r) where trichotomous
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.Lex.0.List.Lex.trichotomous.aux`：∀ {α : Type 
u} (r : α → α → Prop) [Std.Trichotomous r] (x x_1 : List α), ¬List.Lex r x x_1 →
 ¬List.Lex r x_1 x → x = x_1
-/
instance trichotomous (r : α → α → Prop) [Std.Trichotomous r] : Std.Trichotomous (Lex r) where
  trichotomous := aux where
    aux
    | [], [], _, _ => rfl
    | [], _ :: _, hab, _ => hab nil |>.elim
    | _ :: _, [], _, hba => hba nil |>.elim
    | a :: l₁, b :: l₂, hab, hba => by
      obtain rfl := Std.Trichotomous.trichotomous a b (mt rel hab) (mt rel hba)
      rw [aux l₁ l₂ (mt cons hab) (mt cons hba)]
/-
**List.Lex.asymm** 是 Mathlib 中的一个实例，位于命名空间 `List.Lex`。
形式化陈述：asymm (r : α -> α -> Prop) [Std.Asymm r] : Std.Asymm (Lex r) where asymm
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.Lex.0.List.Lex.asymm.aux`：∀ {α : Type u} (r :
 α → α → Prop) [Std.Asymm r] (x x_1 : List α), List.Lex r x x_1 → List.Lex r x_1
 x → False
-/
instance asymm (r : α → α → Prop) [Std.Asymm r] : Std.Asymm (Lex r) where
  asymm := aux where
    aux
    | _, _, Lex.rel h₁, Lex.rel h₂ => _root_.asymm h₁ h₂
    | _, _, Lex.rel h₁, Lex.cons _ => _root_.asymm h₁ h₁
    | _, _, Lex.cons _, Lex.rel h₂ => _root_.asymm h₂ h₂
    | _, _, Lex.cons h₁, Lex.cons h₂ => aux _ _ h₁ h₂
/-
**List.Lex.decidableRel** 是 Mathlib 中的一个实例，位于命名空间 `List.Lex`。
形式化陈述：decidableRel [DecidableEq α] (r : α -> α -> Prop) [DecidableRel r] : Decid
ableRel (Lex r) | l₁, [] => isFalse fun h => by cases h | [], _ :: _ => isTrue L
ex.nil | a :: l₁, b :: l₂ => by haveI
参数：r : α -> α -> Prop。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableRel [DecidableEq α] (r : α → α → Prop) [DecidableRel r] : DecidableRel (Lex r)
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
/-
**List.Lex.append_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`。
形式化陈述：∀ {α : Type u} (r : α → α → Prop) {s₁ s₂ : List α} (t : List α), List.Lex 
r s₁ s₂ → List.Lex r s₁ (s₂ ++ t)
参数：r : α → α → Prop；t : List α；s₂ ++ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_right (r : α → α → Prop) : ∀ {s₁ s₂} (t), Lex r s₁ s₂ → Lex r s₁ (s₂ ++ t)
  | _, _, _, nil => nil
  | _, _, _, cons h => cons (append_right r _ h)
  | _, _, _, rel r => rel r
/-
**List.Lex.append_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`。
形式化陈述：∀ {α : Type u} (R : α → α → Prop) {t₁ t₂ : List α}, List.Lex R t₁ t₂ → ∀ (
s : List α), List.Lex R (s ++ t₁) (s ++ t₂)
参数：R : α → α → Prop；s : List α；s ++ t₁；s ++ t₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_left (R : α → α → Prop) {t₁ t₂} (h : Lex R t₁ t₂) : ∀ s, Lex R (s ++ t₁) (s ++ t₂)
  | [] => h
  | _ :: l => cons (append_left R h l)
/-
**List.Lex.imp** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`。
形式化陈述：∀ {α : Type u} {r s : α → α → Prop},   (∀ (a b : α), r a b → s a b) → ∀ (l
₁ l₂ : List α), List.Lex r l₁ l₂ → List.Lex s l₁ l₂
参数：∀ (a b : α), r a b → s a b；l₁ l₂ : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Lex.brecOn`：∀ {α : Type u} {r : α → α → Prop} {motive : (as bs : Li
st α) → List.Lex r as bs → Prop} {as bs : List α}   (t : List.Lex r as bs),   (∀
 (as …
-/
theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) : ∀ l₁ l₂, Lex r l₁ l₂ → Lex s l₁ l₂
  | _, _, nil => nil
  | _, _, cons h => cons (imp H _ _ h)
  | _, _, rel r => rel (H _ _ r)
/-
**List.Lex.to_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, List.Lex (fun x1 x2 => x1 ≠ x2) l₁ l₂ → l
₁ ≠ l₂
参数：fun x1 x2 => x1 ≠ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Lex.brecOn`：∀ {α : Type u} {r : α → α → Prop} {motive : (as bs : Li
st α) → List.Lex r as bs → Prop} {as bs : List α}   (t : List.Lex r as bs),   (∀
 (as …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.cons.inj`：∀ {α : Type u} {head : α} {tail : List α} {head_1 : α} {t
ail_1 : List α},   head :: tail = head_1 :: tail_1 → head = head_1 ∧ tail = tail
_1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem to_ne : ∀ {l₁ l₂ : List α}, Lex (· ≠ ·) l₁ l₂ → l₁ ≠ l₂
  | _, _, cons h, e => to_ne h (List.cons.inj e).2
  | _, _, rel r, e => r (List.cons.inj e).1
/-
**List.Lex._root_.Decidable.List.Lex.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Decidable.List.Lex.ne_iff [DecidableEq α] {l₁ l₂ : List α}
    (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ :=
  ⟨to_ne, fun h => by
    induction l₁ generalizing l₂ <;> rcases l₂ with - | ⟨b, l₂⟩
    · contradiction
    · apply nil
    · exact (not_lt_of_ge H).elim (succ_pos _)
    case cons.cons a l₁ IH =>
      by_cases ab : a = b
      · subst b
        exact .cons <| IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
      · exact .rel ab ⟩
/-
**List.Lex.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Lex`。
形式化陈述：ne_iff {l₁ l₂ : List α} (H : length l₁ <= length l₂) : Lex (· != ·) l₁ l₂ 
↔ l₁ != l₂
参数：H : length l₁ <= length l₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.List.Lex.ne_iff`：∀ {α : Type u} [DecidableEq α] {l₁ l₂ : List 
α},   l₁.length ≤ l₂.length → (List.Lex (fun x1 x2 => x1 ≠ x2) l₁ l₂ ↔ l₁ ≠ l₂)
-/
theorem ne_iff {l₁ l₂ : List α} (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ := by
  classical
  exact Decidable.List.Lex.ne_iff H

end Lex

/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : LinearOrder (List α) :=
  have : ∀ {r} [IsStrictTotalOrder α r], IsStrictTotalOrder (List α) (Lex r) :=
    { isStrictWeakOrder_of_isOrderConnected with }
  linearOrderOfSTO (Lex (· < ·))

--Note: this overrides an instance in core lean
/-
**List.LE'** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：LE' [LinearOrder α] : LE (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LE' [LinearOrder α] : LE (List α) :=
  Preorder.toLE
/-
**List.lt_iff_lex_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lt_iff_lex_lt [LT α] (l l' : List α) : List.lt l l' ↔ Lex (· < ·) l l'
参数：l l' : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.lt.eq_1`：∀ {α : Type u} [inst : LT α], List.lt = List.Lex fun x1 x2
 => x1 < x2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_lex_lt [LT α] (l l' : List α) : List.lt l l' ↔ Lex (· < ·) l l' := by
  rw [List.lt]
/-
**List.head_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_le_of_lt [Preorder α] {a a' : α} {l l' : List α} (h : (a' :: l') < (a
 :: l)) : a' <= a
参数：h : (a' :: l') < (a :: l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem head_le_of_lt [Preorder α] {a a' : α} {l l' : List α} (h : (a' :: l') < (a :: l)) :
    a' ≤ a :=
  match h with
  | .cons _ => le_rfl
  | .rel h => h.le
/-
**List.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) : (List.replic
ate n l).flatten.head? = l.head?
参数：h : n != 0；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head!_le_of_lt [Preorder α] [Inhabited α] (l l' : List α) (h : l' < l) (hl' : l' ≠ []) :
    l'.head! ≤ l.head! := by
  replace h : List.Lex (· < ·) l' l := h
  by_cases hl : l = []
  · simp [hl] at h
  · rw [← List.cons_head!_tail hl', ← List.cons_head!_tail hl] at h
    exact head_le_of_lt h
/-
**List.cons_le_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_le_cons [LinearOrder α] (a : α) {l l' : List α} (h : l' <= l) : a :: 
l' <= a :: l
参数：a : α；h : l' <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cons_le_cons [LinearOrder α] (a : α) {l l' : List α} (h : l' ≤ l) :
    a :: l' ≤ a :: l := by
  rw [le_iff_lt_or_eq] at h ⊢
  exact h.imp .cons (congr_arg _)

end List

