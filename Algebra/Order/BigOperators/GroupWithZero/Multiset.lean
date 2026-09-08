/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Big operators on a multiset in ordered groups with zeros

This file contains the results concerning the interaction of multiset big operators with ordered
groups with zeros.
-/

public section

namespace Multiset

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

/-
**Multiset.prod_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_nonneg {s : Multiset R} (h : forall a in s, 0 <= a) : 0 <= s.prod
参数：h : forall a in s, 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用引理 `List.prod_nonneg`：prod_nonneg {s : List R} (h : forall a in s, 0 <= a) :
 0 <= s.prod
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma prod_nonneg {s : Multiset R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h
/-
**Multiset.one_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：one_le_prod {s : Multiset R} (h : forall a in s, 1 <= a) : 1 <= s.prod
参数：h : forall a in s, 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用引理 `List.one_le_prod`：one_le_prod {s : List R} (h : forall a in s, 1 <= a) :
 1 <= s.prod
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma one_le_prod {s : Multiset R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h
/-
**Multiset.prod_map_le_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_le_prod_map [MulLeftMono α] {s : Multiset ι} (f : ι -> α) (g : ι 
-> α) (h : forall i, i in s -> f i <= g i) : (s.map f).prod <= (s.map g).prod
参数：f : ι -> α；g : ι -> α；h : forall i, i in s -> f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_le_prod_of_rel_le`：prod_le_prod_of_rel_le [MulLeftMono α] 
(h : s.Rel (· <= ·) t) : s.prod <= t.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_map`：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ}
 {g : β -> δ} : Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
· 使用定理 `Multiset.rel_refl_of_refl_on`：rel_refl_of_refl_on {m : Multiset α} {r : 
α -> α -> Prop} : (forall x in m, r x x) -> Rel r m m
-/
theorem prod_map_le_prod_map₀ {ι : Type*} {s : Multiset ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h
/-
**Multiset.prod_map_le_pow_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_le_pow_card {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : Mu
ltiset L} (hf0 : forall x in t, 0 <= f x) (hf : forall x in t, f x <= r) : (map 
f t).prod <= r ^ card t
参数：hf0 : forall x in t, 0 <= f x；hf : forall x in t, f x <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_map_le_pow_card {F L : Type*} [FunLike F L R] {f : F} {r : R} {t : Multiset L}
    (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, f x ≤ r) :
    (map f t).prod ≤ r ^ card t := by
  induction t using Quotient.inductionOn
  simp_all [List.prod_map_le_pow_length₀]

variable {α : Type*}
/-
**Multiset.prod_map_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_nonneg {s : Multiset α} {f : α -> R} (h : forall a in s, 0 <= f a
) : 0 <= (s.map f).prod
参数：h : forall a in s, 0 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.prod_nonneg`：prod_nonneg {s : Multiset R} (h : forall a in s, 0
 <= a) : 0 <= s.prod
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
lemma prod_map_nonneg {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 0 ≤ f a) :
    0 ≤ (s.map f).prod := by
  refine prod_nonneg fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha
/-
**Multiset.one_le_prod_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：one_le_prod_map {s : Multiset α} {f : α -> R} (h : forall a in s, 1 <= f a
) : 1 <= (s.map f).prod
参数：h : forall a in s, 1 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.one_le_prod`：one_le_prod {s : Multiset R} (h : forall a in s, 1
 <= a) : 1 <= s.prod
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
lemma one_le_prod_map {s : Multiset α} {f : α → R} (h : ∀ a ∈ s, 1 ≤ f a) :
    1 ≤ (s.map f).prod := by
  refine one_le_prod fun r hr ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hr
  exact h a ha

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]
/-
**Multiset.prod_pos** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_pos {s : Multiset R} (h : forall a in s, 0 < a) : 0 < s.prod
参数：h : forall a in s, 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用引理 `List.prod_pos`：prod_pos {s : List R} (h : forall a in s, 0 < a) : 0 < s.
prod
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma prod_pos {s : Multiset R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h
/-
**Multiset.prod_map_lt_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_map_lt_prod_map {ι : Type*} {s : Multiset ι} (hs : s != 0) (f : ι -> 
R) (g : ι -> R) (h0 : forall i in s, 0 < f i) (h : forall i in s, f i < g i) : (
map f s).prod < (map g s).prod
参数：hs : s != 0；f : ι -> R；g : ι -> R；h0 : forall i in s, 0 < f i；h : forall i in
 s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `List.prod_map_lt_prod_map`：prod_map_lt_prod_map {ι : Type*} {s : List ι}
 (hs : s != []) (f : ι -> R) (g : ι -> R) (h0 : forall i in s, 0 < f i) (h : for
all i in s, f i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_map_lt_prod_map {ι : Type*} {s : Multiset ι} (hs : s ≠ 0)
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

end Multiset

