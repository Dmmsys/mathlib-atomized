/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Dedup

/-!
# Destuttering of Lists

This file proves theorems about `List.destutter` (in `Data.List.Defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `List.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `List.isChain_destutter'`: `l.destutter` satisfies `IsChain R`.
* Analogies of these theorems for `List.destutter'`, which is the `destutter` equivalent of `Chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/

public section

open Function

variable {α β : Type*} (l l₁ l₂ : List α) (R : α → α → Prop) [DecidableRel R] {a b : α}

variable {R₂ : β → β → Prop} [DecidableRel R₂]

namespace List

@[simp]
/-
**List.destutter'_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] {a : α}, List.
destutter' R a [] = [a]
参数：R : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
-/
theorem destutter'_nil : destutter' R a [] = [a] :=
  rfl
/-
**List.destutter'_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] {
a b : α},   List.destutter' R a (b :: l) = if R a b then a :: List.destutter' R 
b l else List.destutter' R a l
参数：l : List α；R : α → α → Prop；b :: l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
-/
theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

variable {R}

@[simp]
/-
**List.destutter'_cons_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {
a b : α},   R b a → List.destutter' R b (a :: l) = b :: List.destutter' R a l
参数：l : List α；a :: l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'.eq_2`：∀ {α : Type u_1} (R : α → α → Prop) [inst : Decida
bleRel R] (x h : α) (l : List α),   List.destutter' R x (h :: l) = if R x h then
 x :: List…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter', if_pos h]

@[simp]
/-
**List.destutter'_cons_neg** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {
a b : α},   ¬R b a → List.destutter' R b (a :: l) = List.destutter' R b l
参数：l : List α；a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'.eq_2`：∀ {α : Type u_1} (R : α → α → Prop) [inst : Decida
bleRel R] (x h : α) (l : List α),   List.destutter' R x (h :: l) = if R x h then
 x :: List…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter', if_neg h]

variable (R)

@[simp]
/-
**List.destutter'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] {a b : α},   L
ist.destutter' R a [b] = if R a b then [a, b] else [a]
参数：R : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]
/-
**List.destutter'_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] (
a : α),   (List.destutter' R a l).Sublist (a :: l)
参数：l : List α；R : α → α → Prop；a : α；List.destutter' R a l；a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'.eq_2`：∀ {α : Type u_1} (R : α → α → Prop) [inst : Decida
bleRel R] (x h : α) (l : List α),   List.destutter' R x (h :: l) = if R x h then
 x :: List…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.sublist_cons_self`：∀ {α : Type u_1} (a : α) (l : List α), l.Sublist
 (a :: l)
-/
theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · exact Sublist.cons_cons a (hl b)
    · exact (hl a).trans ((l.sublist_cons_self b).cons_cons a)
/-
**List.mem_destutter'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_destutter' (a) : a in l.destutter' R a
参数：a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.destutter'.eq_2`：∀ {α : Type u_1} (R : α → α → Prop) [inst : Decida
bleRel R] (x h : α) (l : List α),   List.destutter' R x (h :: l) = if R x h then
 x :: List…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem mem_destutter' (a) : a ∈ l.destutter' R a := by
  induction l with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · simp
    · assumption
/-
**List.isChain_destutter'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_destutter' (l : List α) (a : α) : (l.destutter' R a).IsChain R
参数：l : List α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'_singleton`：∀ {α : Type u_1} (R : α → α → Prop) [inst : D
ecidableRel R] {a b : α},   List.destutter' R a [b] = if R a b then [a, b] else 
[a]
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isChain_destutter' (l : List α) (a : α) : (l.destutter' R a).IsChain R := by
  induction l using twoStepInduction generalizing a with
  | nil => simp
  | singleton => simp [apply_ite]
  | cons_cons b c l IH IH2 =>
    simp_rw [destutter'_cons, apply_ite (IsChain R ·), IH, if_true_right] at IH2
    simp_rw [destutter'_cons, apply_ite (IsChain R ·),
      apply_ite (IsChain R <| a :: ·), IH, isChain_cons_cons,
      if_true_right, ite_prop_iff_and, imp_and]
    exact ⟨⟨⟨Function.swap <| fun _ => id, fun _ => IH2 c b⟩,
      Function.swap <| fun _ => IH2 b a⟩, fun _ => IH2 c a⟩
/-
**List.isChain_cons_destutter'_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] (l : List α) {
a b : α},   R a b → List.IsChain R (a :: List.destutter' R b l)
参数：R : α → α → Prop；l : List α；a :: List.destutter' R b l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'_cons_pos`：∀ {α : Type u_1} (l : List α) {R : α → α → Pro
p} [inst : DecidableRel R] {a b : α},   R b a → List.destutter' R b (a :: l) = b
 :: List.destu…
· 使用定理 `List.isChain_destutter'`：isChain_destutter' (l : List α) (a : α) : (l.de
stutter' R a).IsChain R
-/
theorem isChain_cons_destutter'_of_rel (l : List α) {a b} (hab : R a b) :
    (a :: l.destutter' R b).IsChain R := by
  simpa [destutter'_cons, hab] using isChain_destutter' R (b :: l) a
/-
**List.destutter'_of_isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] {
a : α},   List.IsChain R (a :: l) → List.destutter' R a l = a :: l
参数：l : List α；R : α → α → Prop；a :: l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.destutter'_cons_pos`：∀ {α : Type u_1} (l : List α) {R : α → α → Pro
p} [inst : DecidableRel R] {a b : α},   R b a → List.destutter' R b (a :: l) = b
 :: List.destu…
-/
theorem destutter'_of_isChain_cons (h : (a :: l).IsChain R) : l.destutter' R a = a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hb =>
    obtain ⟨h, hc⟩ := isChain_cons_cons.mp h
    rw [l.destutter'_cons_pos h, hb hc]

@[simp]
/-
**List.destutter'_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] (
a : α),   List.destutter' R a l = a :: l ↔ List.IsChain R (a :: l)
参数：l : List α；R : α → α → Prop；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.isChain_destutter'`：isChain_destutter' (l : List α) (a : α) : (l.de
stutter' R a).IsChain R
· 使用定理 `List.destutter'_of_isChain_cons`：∀ {α : Type u_1} (l : List α) (R : α → 
α → Prop) [inst : DecidableRel R] {a : α},   List.IsChain R (a :: l) → List.dest
utter' R a l = a :: l
-/
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ (a :: l).IsChain R :=
  ⟨fun h => by
    rw [← h]
    exact l.isChain_destutter' R a, destutter'_of_isChain_cons _ _⟩
/-
**List.destutter'_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] {
a : α}, List.destutter' R a l ≠ []
参数：l : List α；R : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `List.mem_destutter'`：mem_destutter' (a) : a in l.destutter' R a
-/
theorem destutter'_ne_nil : l.destutter' R a ≠ [] :=
  ne_nil_of_mem <| l.mem_destutter' R a

@[simp]
/-
**List.destutter_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_nil : ([] : List α).destutter R = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl
/-
**List.destutter_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_cons' : (a :: l).destutter R = destutter' R a l
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl
/-
**List.destutter_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_cons_cons : (a :: b :: l).destutter R = if R a b then a :: destu
tter' R b l else destutter' R a l
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

@[simp]
/-
**List.destutter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_singleton : destutter R [a] = [a]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl

@[simp]
/-
**List.destutter_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter_cons_cons`：destutter_cons_cons : (a :: b :: l).destutter 
R = if R a b then a :: destutter' R b l else destutter' R a l
-/
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R
/-
**List.destutter_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] (l : List α), 
(List.destutter R l).Sublist l
参数：R : α → α → Prop；l : List α；List.destutter R l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'_sublist`：∀ {α : Type u_1} (l : List α) (R : α → α → Prop
) [inst : DecidableRel R] (a : α),   (List.destutter' R a l).Sublist (a :: l)
-/
theorem destutter_sublist : ∀ l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h
/-
**List.isChain_destutter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] (l : List α), 
List.IsChain R (List.destutter R l)
参数：R : α → α → Prop；l : List α；List.destutter R l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_destutter'`：isChain_destutter' (l : List α) (a : α) : (l.de
stutter' R a).IsChain R
-/
theorem isChain_destutter : ∀ l : List α, (l.destutter R).IsChain R
  | [] => .nil
  | h :: l => l.isChain_destutter' R h
/-
**List.destutter_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] (l : List α), 
List.IsChain R l → List.destutter R l = l
参数：R : α → α → Prop；l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'_of_isChain_cons`：∀ {α : Type u_1} (l : List α) (R : α → 
α → Prop) [inst : DecidableRel R] {a : α},   List.IsChain R (a :: l) → List.dest
utter' R a l = a :: l
-/
theorem destutter_of_isChain : ∀ l : List α, l.IsChain R → l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_isChain_cons _ h

@[simp]
/-
**List.destutter_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] (l : List α), 
List.destutter R l = l ↔ List.IsChain R l
参数：R : α → α → Prop；l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.destutter'_eq_self_iff`：∀ {α : Type u_1} (l : List α) (R : α → α → 
Prop) [inst : DecidableRel R] (a : α),   List.destutter' R a l = a :: l ↔ List.I
sChain R (a :: l)
-/
theorem destutter_eq_self_iff : ∀ l : List α, l.destutter R = l ↔ l.IsChain R
  | [] => by simp
  | a :: l => l.destutter'_eq_self_iff R a
/-
**List.destutter_idem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter_idem : (l.destutter R).destutter R = l.destutter R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter_of_isChain`：∀ {α : Type u_1} (R : α → α → Prop) [inst : D
ecidableRel R] (l : List α), List.IsChain R l → List.destutter R l = l
· 使用定理 `List.isChain_destutter`：∀ {α : Type u_1} (R : α → α → Prop) [inst : Deci
dableRel R] (l : List α), List.IsChain R (List.destutter R l)
-/
theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
  destutter_of_isChain R _ <| l.isChain_destutter R

@[simp]
/-
**List.destutter_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (R : α → α → Prop) [inst : DecidableRel R] {l : List α}, 
List.destutter R l = [] ↔ l = []
参数：R : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `List.destutter'_ne_nil`：∀ {α : Type u_1} (l : List α) (R : α → α → Prop)
 [inst : DecidableRel R] {a : α}, List.destutter' R a l ≠ []
-/
theorem destutter_eq_nil : ∀ {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
  | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R, fun h => nomatch h⟩

variable {R}

/-- For a relation-preserving map, `destutter` commutes with `map`. -/
/-
**List.map_destutter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_destutter {f : α -> β} : forall {l : List α}, (forall a in l, forall b
 in l, R a b ↔ R₂ (f a) (f b)) -> (l.destutter R).map f = (l.map f).destutter R₂
 | [], hl => by simp | [a], hl => by simp | a :: b :: l, hl => by have
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_destutter._unary`：∀ {α : Type u_1} {β : Type u_2} {R : α → α → 
Prop} [inst : DecidableRel R] {R₂ : β → β → Prop}   [inst_1 : DecidableRel R₂] {
f : α → β} (_x …

--- 原说明 ---
For a relation-preserving map, `destutter` commutes with `map`.
-/
theorem map_destutter {f : α → β} : ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, R a b ↔ R₂ (f a) (f b)) →
    (l.destutter R).map f = (l.map f).destutter R₂
  | [], hl => by simp
  | [a], hl => by simp
  | a :: b :: l, hl => by
    have := hl a (by simp) b (by simp)
    simp_rw [map_cons, destutter_cons_cons, ← this]
    by_cases hr : R a b <;>
      simp [hr, ← destutter_cons', map_destutter fun c hc d hd ↦ hl _ (cons_subset_cons _
        (subset_cons_self _ _) hc) _ (cons_subset_cons _ (subset_cons_self _ _) hd),
        map_destutter fun c hc d hd ↦ hl _ (subset_cons_self _ _ hc) _ (subset_cons_self _ _ hd)]

/-- For an injective function `f`, `destutter' (·≠·)` commutes with `map f`. -/
/-
**List.map_destutter_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_destutter_ne {f : α -> β} (h : Injective f) [DecidableEq α] [Decidable
Eq β] : (l.destutter (· != ·)).map f = (l.map f).destutter (· != ·)
参数：h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_destutter`：map_destutter {f : α -> β} : forall {l : List α}, (f
orall a in l, forall b in l, R a b ↔ R₂ (f a) (f b)) -> (l.destutter R).map f = 
(l.map f…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y

--- 原说明 ---
For an injective function `f`, `destutter' (·≠·)` commutes with `map f`.
-/
theorem map_destutter_ne {f : α → β} (h : Injective f) [DecidableEq α] [DecidableEq β] :
    (l.destutter (· ≠ ·)).map f = (l.map f).destutter (· ≠ ·) :=
  map_destutter fun _ _ _ _ ↦ h.ne_iff.symm

/-- `destutter'` on a relation like ≠ or <, whose negation is transitive, has length monotone
under a `¬R` changing of the first element. -/
/-
**List.length_destutter'_cotrans_ge** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [inst : DecidableRel R] {b : α} [i : I
sTrans α Rᶜ] {a : α} {l : List α},   ¬R b a → (List.destutter' R b l).length ≤ (
List.destutter' R a l).length
参数：List.destutter' R b l；List.destutter' R a l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]

--- 原说明 ---
`destutter'` on a relation like ≠ or <, whose negation is transitive, has length
 monotone
under a `¬R` changing of the first element.
-/
theorem length_destutter'_cotrans_ge [i : IsTrans α Rᶜ] :
    ∀ {a} {l : List α}, ¬R b a → (l.destutter' R b).length ≤ (l.destutter' R a).length
  | a, [], hba => by simp
  | a, c :: l, hba => by
    by_cases hbc : R b c
    case pos =>
      have hac : ¬Rᶜ a c := (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_le (length_destutter'_cotrans_ge hbc)
      case neg =>
        simp only [if_neg hac]
        exact length_destutter'_cotrans_ge hba

/-- `List.destutter'` on a relation like `≠`, whose negation is an equivalence, gives the same
length if the first elements are not related. -/
/-
**List.length_destutter'_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {
a b : α} [IsEquiv α Rᶜ],   ¬R a b → (List.destutter' R a l).length = (List.destu
tter' R b l).length
参数：l : List α；List.destutter' R a l；List.destutter' R b l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `List.length_destutter'_cotrans_ge`：∀ {α : Type u_1} {R : α → α → Prop} [
inst : DecidableRel R] {b : α} [i : IsTrans α Rᶜ] {a : α} {l : List α},   ¬R b a
 → (List.destutter' R b…
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r

--- 原说明 ---
`List.destutter'` on a relation like `≠`, whose negation is an equivalence, give
s the same
length if the first elements are not related.
-/
theorem length_destutter'_congr [IsEquiv α Rᶜ] (hab : ¬R a b) :
    (l.destutter' R a).length = (l.destutter' R b).length :=
  (length_destutter'_cotrans_ge hab).antisymm <| length_destutter'_cotrans_ge (symm hab : Rᶜ b a)

/-- `List.destutter'` on a relation like ≠, whose negation is an equivalence, has length
monotonic under List.cons -/
/-
TODO: Replace this lemma by the more general version:
theorem Sublist.length_destutter'_mono [IsEquiv α Rᶜ] (h : a :: l₁ <+ b :: l₂) :
    (List.destutter' R a l₁).length ≤ (List.destutter' R b l₂).length
-/
/-
**List.le_length_destutter'_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [inst : DecidableRel R] {a b : α} [IsE
quiv α Rᶜ] {l : List α},   (List.destutter' R b l).length ≤ (List.destutter' R a
 (b :: l)).length
参数：List.destutter' R b l；List.destutter' R a (b :: l)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.destutter'_cons_pos`：∀ {α : Type u_1} (l : List α) {R : α → α → Pro
p} [inst : DecidableRel R] {a b : α},   R b a → List.destutter' R b (a :: l) = b
 :: List.destu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.destutter'_cons_neg`：∀ {α : Type u_1} (l : List α) {R : α → α → Pro
p} [inst : DecidableRel R] {a b : α},   ¬R b a → List.destutter' R b (a :: l) = 
List.destutter…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `List.length_destutter'_congr`：∀ {α : Type u_1} (l : List α) {R : α → α →
 Prop} [inst : DecidableRel R] {a b : α} [IsEquiv α Rᶜ],   ¬R a b → (List.destut
ter' R a l).length…

--- 原说明 ---
TODO: Replace this lemma by the more general version:
theorem Sublist.length_destutter'_mono [IsEquiv α Rᶜ] (h : a :: l₁ <+ b :: l₂) :
    (List.destutter' R a l₁).length ≤ (List.destutter' R b l₂).length
-/
theorem le_length_destutter'_cons [IsEquiv α Rᶜ] :
    ∀ {l : List α}, (l.destutter' R b).length ≤ ((b :: l).destutter' R a).length
  | [] => by by_cases hab : (R a b) <;> simp_all [Nat.le_succ]
  | c :: cs => by
    by_cases hab : R a b
    case pos => simp [destutter', if_pos hab, Nat.le_succ]
    obtain hac | hac : R a c ∨ Rᶜ a c := em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs hab).ge

/-- `List.destutter` on a relation like ≠, whose negation is an equivalence, has length
monotone under List.cons -/
/-
**List.length_destutter_le_length_destutter_cons** 是 Mathlib 中的一个定理，位于命名空间 `List
`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [inst : DecidableRel R] {a : α} [IsEqu
iv α Rᶜ] {l : List α},   (List.destutter R l).length ≤ (List.destutter R (a :: l
)).length
参数：List.destutter R l；List.destutter R (a :: l)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.le_length_destutter'_cons`：∀ {α : Type u_1} {R : α → α → Prop} [ins
t : DecidableRel R] {a b : α} [IsEquiv α Rᶜ] {l : List α},   (List.destutter' R 
b l).length ≤ (List.…

--- 原说明 ---
`List.destutter` on a relation like ≠, whose negation is an equivalence, has len
gth
monotone under List.cons
-/
theorem length_destutter_le_length_destutter_cons [IsEquiv α Rᶜ] :
    ∀ {l : List α}, (l.destutter R).length ≤ ((a :: l).destutter R).length
  | [] => by simp [destutter]
  | b :: l => le_length_destutter'_cons

variable {l l₁ l₂}

/-- `destutter ≠` has length monotone under `List.cons`. -/
/-
**List.length_destutter_ne_le_length_destutter_cons** 是 Mathlib 中的一个定理，位于命名空间 `L
ist`。
形式化陈述：length_destutter_ne_le_length_destutter_cons [DecidableEq α] : (l.destutte
r (· != ·)).length <= ((a :: l).destutter (· != ·)).length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_destutter_le_length_destutter_cons`：∀ {α : Type u_1} {R : α 
→ α → Prop} [inst : DecidableRel R] {a : α} [IsEquiv α Rᶜ] {l : List α},   (List
.destutter R l).length ≤ (List.destu…

--- 原说明 ---
`destutter ≠` has length monotone under `List.cons`.
-/
theorem length_destutter_ne_le_length_destutter_cons [DecidableEq α] :
    (l.destutter (· ≠ ·)).length ≤ ((a :: l).destutter (· ≠ ·)).length :=
  length_destutter_le_length_destutter_cons

/-- `destutter` of relations like `≠`, whose negation is an equivalence relation,
gives a list of maximal length over any chain.

In other words, `l.destutter R` is an `R`-chain sublist of `l`, and is at least as long as any other
`R`-chain sublist. -/
/-
**List.IsChain.length_le_length_destutter** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChai
n`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [inst : DecidableRel R] [IsEquiv α Rᶜ]
 {l₁ l₂ : List α},   l₁.Sublist l₂ → List.IsChain R l₁ → l₁.length ≤ (List.destu
tter R l₂).length
参数：List.destutter R l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.length_le_length_destutter._unary`：∀ {α : Type u_1} {R : α 
→ α → Prop} [inst : DecidableRel R] [IsEquiv α Rᶜ]   (_x : (l₁ : List α) ×' (l₂ 
: List α) ×' (_ : l₁.Sublist l₂) ×' …

--- 原说明 ---
`destutter` of relations like `≠`, whose negation is an equivalence relation,
gives a list of maximal length over any chain.

In other words, `l.destutter R` is an `R`-chain sublist of `l`, and is at least 
as long as any other
`R`-chain sublist.
-/
lemma IsChain.length_le_length_destutter [IsEquiv α Rᶜ] :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → l₁.IsChain R → l₁.length ≤ (l₂.destutter R).length
  -- `l₁ := []`, `l₂ := []`
  | [], [], _, _ => by simp
  -- `l₁ := l₁`, `l₂ := a :: l₂`
  | l₁, _, .cons (l₂ := l₂) a hl, hl₁ =>
    (hl₁.length_le_length_destutter hl).trans length_destutter_le_length_destutter_cons
  -- `l₁ := [a]`, `l₂ := a :: l₂`
  | _, _, .cons_cons (l₁ := []) (l₂ := l₁) a hl, hl₁ => by simp [Nat.one_le_iff_ne_zero]
  -- `l₁ := a :: l₁`, `l₂ := a :: b :: l₂`
  | _, _, .cons_cons a <| .cons (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    by_cases hab : R a b
    · simpa [destutter_cons_cons, hab] using! hl₁.tail.length_le_length_destutter (hl.cons _)
    · simpa [destutter_cons_cons, hab] using! hl₁.length_le_length_destutter (hl.cons_cons _)
  -- `l₁ := a :: b :: l₁`, `l₂ := a :: b :: l₂`
  | _, _, .cons_cons a <| .cons_cons (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    simpa [destutter_cons_cons, rel_of_isChain_cons_cons hl₁]
      using! hl₁.tail.length_le_length_destutter (hl.cons_cons _)

/-- `destutter` of `≠` gives a list of maximal length over any chain.

In other words, `l.destutter (· ≠ ·)` is a `≠`-chain sublist of `l`, and is at least as long as any
other `≠`-chain sublist. -/
/-
**List.IsChain.length_le_length_destutter_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.IsC
hain`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α} [inst : DecidableEq α],   l₁.Sublist l₂ 
→ List.IsChain (fun x1 x2 => x1 ≠ x2) l₁ → l₁.length ≤ (List.destutter (fun x1 x
2 => x1 ≠ x2) l₂).length
参数：fun x1 x2 => x1 ≠ x2；List.destutter (fun x1 x2 => x1 ≠ x2) l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.length_le_length_destutter`：∀ {α : Type u_1} {R : α → α → P
rop} [inst : DecidableRel R] [IsEquiv α Rᶜ] {l₁ l₂ : List α},   l₁.Sublist l₂ → 
List.IsChain R l₁ → l₁.length…

--- 原说明 ---
`destutter` of `≠` gives a list of maximal length over any chain.

In other words, `l.destutter (· ≠ ·)` is a `≠`-chain sublist of `l`, and is at l
east as long as any
other `≠`-chain sublist.
-/
lemma IsChain.length_le_length_destutter_ne [DecidableEq α] (hl : l₁ <+ l₂)
    (hl₁ : l₁.IsChain (· ≠ ·)) : l₁.length ≤ (l₂.destutter (· ≠ ·)).length :=
  hl₁.length_le_length_destutter hl

/--
If the elements of a list `l` are related pairwise by an antisymmetric relation `r`, then
destuttering `l` by disequality produces the same result as deduplicating `l`.
This is most useful when `r` is a strict or weak ordering.
-/
/-
**List.Pairwise.destutter_eq_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {r : α → α → Prop} [Std.Antisymm r
] {l : List α},   List.Pairwise r l → List.destutter (fun x1 x2 => x1 ≠ x2) l = 
l.dedup
参数：fun x1 x2 => x1 ≠ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.destutter_eq_dedup._unary`：∀ {α : Type u_1} [inst : Decida
bleEq α] {r : α → α → Prop} [Std.Antisymm r] (_x : (l : List α) ×' List.Pairwise
 r l),   List.destutter (fun …

--- 原说明 ---
If the elements of a list `l` are related pairwise by an antisymmetric relation 
`r`, then
destuttering `l` by disequality produces the same result as deduplicating `l`.
This is most useful when `r` is a strict or weak ordering.
-/
lemma Pairwise.destutter_eq_dedup [DecidableEq α] {r : α → α → Prop} [Std.Antisymm r] :
    ∀ {l : List α}, l.Pairwise r → l.destutter (· ≠ ·) = l.dedup
  | [], h => by simp
  | [x], h => by simp
  | x :: y :: xs, h => by
    rw [pairwise_cons] at h
    rw [destutter_cons_cons, ← destutter_cons', ← destutter_cons', h.2.destutter_eq_dedup]
    obtain rfl | hxy := eq_or_ne x y
    · simpa using h.2.destutter_eq_dedup
    · simp only [mem_cons, forall_eq_or_imp, pairwise_cons] at h
      have : x ∉ xs := fun hx ↦ hxy (antisymm h.1.1 (h.2.1 x hx))
      rw [if_pos hxy, dedup_cons_of_notMem (a := x) (by simp [*])]

end List

