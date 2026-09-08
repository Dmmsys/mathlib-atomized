/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
module

public import Mathlib.Tactic.GCongr.Core

/-!
# Join of a list of lists

This file proves basic properties of `List.flatten`, which concatenates a list of lists. It is
defined in `Init.Prelude`.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α β : Type*}

namespace List

@[gcongr]
/-
**List.Sublist.flatten** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁.Sublist l₂ → l₁.flatten.Subli
st l₂.flatten
参数：List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Sublist.flatten {l₁ l₂ : List (List α)} (h : l₁ <+ l₂) :
    l₁.flatten <+ l₂.flatten := by
  induction h with grind

@[gcongr]
/-
**List.Sublist.flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α},   l₁.Sublist l₂ → ∀ (f :
 α → List β), (List.flatMap f l₁).Sublist (List.flatMap f l₂)
参数：f : α → List β；List.flatMap f l₁；List.flatMap f l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.flatten`：∀ {α : Type u_1} {l₁ l₂ : List (List α)}, l₁.Subli
st l₂ → l₁.flatten.Sublist l₂.flatten
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
protected theorem Sublist.flatMap {l₁ l₂ : List α} (h : l₁ <+ l₂) (f : α → List β) :
    l₁.flatMap f <+ l₂.flatMap f :=
  (h.map f).flatten
/-
**List.Sublist.flatMap_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (l : List α) {f g : α → List β},   (∀ a ∈ 
l, (f a).Sublist (g a)) → (List.flatMap f l).Sublist (List.flatMap g l)
参数：l : List α；∀ a ∈ l, (f a).Sublist (g a)；List.flatMap f l；List.flatMap g l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Sublist.flatMap_right (l : List α) {f g : α → List β} (h : ∀ a ∈ l, f a <+ g a) :
    l.flatMap f <+ l.flatMap g := by
  induction l with grind

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
/-
**List.drop_take_succ_eq_cons_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：drop_take_succ_eq_cons_getElem (L : List α) (i : Nat) (h : i < L.length) :
 (L.take (i + 1)).drop i = [L[i]]
参数：L : List α；i : Nat；h : i < L.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking only the first `i+1` elements in a list, and then dropping the first `i` 
ones, one is
left with a list of length `1` made of the `i`-th element of the original list.
-/
theorem drop_take_succ_eq_cons_getElem (L : List α) (i : Nat) (h : i < L.length) :
    (L.take (i + 1)).drop i = [L[i]] := by
  induction L generalizing i with grind

/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
/-
**List.append_flatten_map_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：append_flatten_map_append (L : List (List α)) (x : List α) : x ++ (L.map (
· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x
参数：L : List (List α)；x : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`.
-/
theorem append_flatten_map_append (L : List (List α)) (x : List α) :
    x ++ (L.map (· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x := by
  induction L with grind

/-- See also `head_flatten_eq_head_head`, which switches around the proof obligations. -/
/-
**List.head_head_eq_head_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_head_eq_head_flatten {l : List (List α)} (hl : l != []) (hl' : l.head
 hl != []) : (l.head hl).head hl' = l.flatten.head (flatten_ne_nil_iff.2 ⟨_, hea
d_mem hl, hl'⟩)
参数：List α；hl : l != []；hl' : l.head hl != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
See also `head_flatten_eq_head_head`, which switches around the proof obligation
s.
-/
theorem head_head_eq_head_flatten {l : List (List α)} (hl : l ≠ []) (hl' : l.head hl ≠ []) :
    (l.head hl).head hl' = l.flatten.head (flatten_ne_nil_iff.2 ⟨_, head_mem hl, hl'⟩) := by
  cases l with grind

/-- See also `head_head_eq_head_flatten`, which switches around the proof obligations. -/
/-
**List.head_flatten_eq_head_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_flatten_eq_head_head {l : List (List α)} (hl : l.flatten != []) (hl' 
: l.head (by grind) != []) : l.flatten.head hl = (l.head (by grind)).head hl'
参数：List α；hl : l.flatten != []；hl' : l.head (by grind) != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `List.head_head_eq_head_flatten`：head_head_eq_head_flatten {l : List (Lis
t α)} (hl : l != []) (hl' : l.head hl != []) : (l.head hl).head hl' = l.flatten.
head (flatten_ne_nil…

--- 原说明 ---
See also `head_head_eq_head_flatten`, which switches around the proof obligation
s.
-/
theorem head_flatten_eq_head_head {l : List (List α)} (hl : l.flatten ≠ [])
    (hl' : l.head (by grind) ≠ []) : l.flatten.head hl = (l.head (by grind)).head hl' :=
  (head_head_eq_head_flatten ..).symm

/-- See also `getLast_flatten_eq_getLast_getLast`, which switches around the proof obligations. -/
/-
**List.getLast_getLast_eq_getLast_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_getLast_eq_getLast_flatten {l : List (List α)} (hl : l != []) (hl'
 : l.getLast hl != []) : (l.getLast hl).getLast hl' = l.flatten.getLast (flatten
_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩)
参数：List α；hl : l != []；hl' : l.getLast hl != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.eq_nil_or_concat`：∀ {α : Type u_1} (l : List α), l = [] ∨ ∃ l' b, l
 = l'.concat b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l

--- 原说明 ---
See also `getLast_flatten_eq_getLast_getLast`, which switches around the proof o
bligations.
-/
theorem getLast_getLast_eq_getLast_flatten {l : List (List α)}
    (hl : l ≠ []) (hl' : l.getLast hl ≠ []) :
    (l.getLast hl).getLast hl' =
      l.flatten.getLast (flatten_ne_nil_iff.2 ⟨_, getLast_mem hl, hl'⟩) := by
  cases eq_nil_or_concat l with grind

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_getLast_ne_nil := getLast_getLast_eq_getLast_flatten

/-- See also `getLast_getLast_eq_getLast_flatten`, which switches around the proof obligations. -/
/-
**List.getLast_flatten_eq_getLast_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_flatten_eq_getLast_getLast {l : List (List α)} (hl : l.flatten != 
[]) (hl' : l.getLast (by grind) != []) : l.flatten.getLast hl = (l.getLast (by g
rind)).getLast hl'
参数：List α；hl : l.flatten != []；hl' : l.getLast (by grind) != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `List.getLast_getLast_eq_getLast_flatten`：getLast_getLast_eq_getLast_flat
ten {l : List (List α)} (hl : l != []) (hl' : l.getLast hl != []) : (l.getLast h
l).getLast hl' = l.flatten.ge…

--- 原说明 ---
See also `getLast_getLast_eq_getLast_flatten`, which switches around the proof o
bligations.
-/
theorem getLast_flatten_eq_getLast_getLast {l : List (List α)}
    (hl : l.flatten ≠ []) (hl' : l.getLast (by grind) ≠ []) :
    l.flatten.getLast hl = (l.getLast (by grind)).getLast hl' :=
  (getLast_getLast_eq_getLast_flatten ..).symm

@[deprecated (since := "2026-01-31")]
alias getLast_flatten_of_flatten_ne_nil := getLast_flatten_eq_getLast_getLast

end List

