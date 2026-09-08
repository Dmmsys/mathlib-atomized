/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.FunLike.Basic

/-!
# Big operators on a list in ordered groups with zeros

This file contains the results concerning the interaction of list big operators with ordered
groups with zeros.
-/

public section

namespace List
variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

/-
**List.prod_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_nonneg {s : List R} (h : forall a in s, 0 <= a) : 0 <= s.prod
参数：h : forall a in s, 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prod_nonneg {s : List R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_nonneg h.1 (hind h.2)
/-
**List.one_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：one_le_prod {s : List R} (h : forall a in s, 1 <= a) : 1 <= s.prod
参数：h : forall a in s, 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma one_le_prod {s : List R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)
/-
**List.prod_map_le_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_or]
/-
**List.prod_map_le_pow_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_map_le_pow_length₀ {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : List L}
    (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, f x ≤ r) :
    (map f t).prod ≤ r ^ length t := by
  convert! prod_map_le_prod_map₀ f (Function.const L r) hf0 hf
  simp [map_const, prod_replicate]

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]
/-
**List.prod_pos** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：prod_pos {s : List R} (h : forall a in s, 0 < a) : 0 < s.prod
参数：h : forall a in s, 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prod_pos {s : List R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact mul_pos h.1 (hind h.2)
/-
**List.prod_map_lt_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s != []) (f : ι -> R) 
(g : ι -> R) (h0 : forall i in s, 0 < f i) (h : forall i in s, f i < g i) : (map
 f s).prod < (map g s).prod
参数：hs : s != []；f : ι -> R；g : ι -> R；h0 : forall i in s, 0 < f i；h : forall i i
n s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulStrictMono_iff_mulPosStrictMono`：posMulStrictMono_iff_mulPosStrict
Mono : PosMulStrictMono α ↔ MulPosStrictMono α
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `List.prod_map_le_prod_map₀`：prod_map_le_prod_map₀ {ι : Type*} {s : List 
ι} (f : ι -> R) (g : ι -> R) (h0 : forall i in s, 0 <= f i) (h : forall i in s, 
f i <= g i) : (m…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `List.prod_pos`：prod_pos {s : List R} (h : forall a in s, 0 < a) : 0 < s.
prod
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s ≠ [])
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  match s with
  | [] => contradiction
  | a :: s =>
    simp only [map_cons, prod_cons]
    have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
    apply mul_lt_mul
    · apply h
      simp
    · apply prod_map_le_prod_map₀
      · intro i hi
        apply le_of_lt
        apply h0
        simp [hi]
      · intro i hi
        apply le_of_lt
        apply h
        simp [hi]
    · apply prod_pos
      grind
    · apply le_of_lt ((h0 _ _).trans (h _ _)) <;> simp

end List

