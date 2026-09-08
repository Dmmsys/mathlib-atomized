/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators

/-!
# Inclusion-exclusion principle

This file proves several variants of the inclusion-exclusion principle.

The inclusion-exclusion principle says that the sum/integral of a function over a finite union of
sets can be calculated as the alternating sum over `n > 0` of the sum/integral of the function over
the intersection of `n` of the sets.

By taking complements, it also says that the sum/integral of a function over a finite intersection
of complements of sets can be calculated as the alternating sum over `n ≥ 0` of the sum/integral of
the function over the intersection of `n` of the sets.

By taking the function to be constant `1`, we instead get a result about the cardinality/measure of
the sets.

## Main declarations

Per the above explanation, this file contains the following variants of inclusion-exclusion:
* `Finset.inclusion_exclusion_sum_biUnion`: Sum of a function over a finite union of sets
* `Finset.inclusion_exclusion_card_biUnion`: Cardinality of a finite union of sets
* `Finset.inclusion_exclusion_sum_inf_compl`: Sum of a function over a finite intersection of
  complements of sets
* `Finset.inclusion_exclusion_card_inf_compl`: Cardinality of a finite intersection of
  complements of sets

See also `MeasureTheory.integral_biUnion_eq_sum_powerset` for the version with integrals, and
`MeasureTheory.measureReal_biUnion_eq_sum_powerset` for the version with measures.

## TODO

* Prove that truncating the series alternatively gives an upper/lower bound to the true value.
-/

public section

assert_not_exists Field

namespace Finset
variable {ι α G : Type*} [AddCommGroup G] {s : Finset ι}

/-
**Finset.prod_indicator_biUnion_sub_indicator** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι -> Set α) (a
 : α) : ∏ i in s, (Set.indicator (⋃ i in s, S i) 1 a - Set.indicator (S i) 1 a) 
= (0 : Int)
参数：hs : s.Nonempty；S : ι -> Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
-/
lemma prod_indicator_biUnion_sub_indicator (hs : s.Nonempty) (S : ι → Set α) (a : α) :
    ∏ i ∈ s, (Set.indicator (⋃ i ∈ s, S i) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by
  by_cases ha : a ∈ ⋃ i ∈ s, S i
  · have ha' := ha
    simp only [Set.mem_iUnion, exists_prop] at ha
    obtain ⟨i, hi, ha⟩ := ha
    apply prod_eq_zero hi (by simp [ha, ha'])
  · obtain ⟨i, hi⟩ := hs
    have ha : a ∉ S i := by aesop
    exact prod_eq_zero hi <| by simp [*, -coe_biUnion]

/-- **Inclusion-exclusion principle**, indicator version over a finite union of sets. -/
/-
**Finset.indicator_biUnion_eq_sum_powerset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：indicator_biUnion_eq_sum_powerset (s : Finset ι) (S : ι -> Set α) (f : α -
> G) (a : α) : Set.indicator (⋃ i in s, S i) f a = ∑ t in s.powerset with t.None
mpty, (-1) ^ (#t + 1) • Set.indicator (⋂ i in t, S i) f a
参数：s : Finset ι；S : ι -> Set α；f : α -> G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用引理 `Finset.prod_sub`：prod_sub [DecidableEq ι] (f g : ι -> R) (s : Finset ι) 
: ∏ i in s, (f i - g i) = ∑ t in s.powerset, (-1) ^ #t * (∏ i in s \ t, f i) * ∏
 i in…
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
**Inclusion-exclusion principle**, indicator version over a finite union of sets
.
-/
lemma indicator_biUnion_eq_sum_powerset (s : Finset ι) (S : ι → Set α) (f : α → G) (a : α) :
    Set.indicator (⋃ i ∈ s, S i) f a = ∑ t ∈ s.powerset with t.Nonempty,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i ∈ t, S i) f a := by
  classical
  by_cases ha : a ∈ ⋃ i ∈ s, S i; swap
  · simp only [ha, not_false_eq_true, Set.indicator_of_notMem, Int.reduceNeg, pow_succ, mul_neg,
      mul_one, neg_smul]
    symm
    apply sum_eq_zero
    simp only [Int.reduceNeg, neg_eq_zero, mem_filter, mem_powerset, and_imp]
    intro t hts ht
    rw [Set.indicator_of_notMem]
    · simp
    · contrapose ha
      simp only [Set.mem_iInter] at ha
      rcases ht with ⟨i, hi⟩
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨i, hts hi, ha _ hi⟩
  rw [← sub_eq_zero]
  calc
    Set.indicator (⋃ i ∈ s, S i) f a - ∑ t ∈ s.powerset with t.Nonempty,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i ∈ t.1, S i) f a
    _ = ∑ t ∈ s.powerset with t.Nonempty, (-1) ^ #t • Set.indicator (⋂ i ∈ t, S i) f a +
        ∑ t ∈ s.powerset with ¬ t.Nonempty, (-1) ^ #t • Set.indicator (⋂ i ∈ t, S i) f a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', pow_succ, ha]
    _ = ∑ t ∈ s.powerset, (-1) ^ #t • Set.indicator (⋂ i ∈ t, S i) f a := by
      rw [sum_filter_add_sum_filter_not]
    _ = (∏ i ∈ s, (1 - Set.indicator (S i) 1 a : ℤ)) • f a := by
      simp only [Int.reduceNeg, prod_sub, prod_const_one, mul_one, sum_smul]
      congr! 1 with t
      simp only [prod_const_one, prod_indicator_apply]
      simp [Set.indicator]
    _ = 0 := by
      have : Set.indicator (⋃ i ∈ s, S i) 1 a = (1 : ℤ) := Set.indicator_of_mem ha 1
      rw [← this, prod_indicator_biUnion_sub_indicator, zero_smul]
      simp only [Set.mem_iUnion, exists_prop] at ha
      rcases ha with ⟨i, hi, -⟩
      exact ⟨i, hi⟩

variable [DecidableEq α]
/-
**Finset.prod_indicator_biUnion_finset_sub_indicator** 是 Mathlib 中的一个引理，位于命名空间 `
Finset`。
形式化陈述：prod_indicator_biUnion_finset_sub_indicator (hs : s.Nonempty) (S : ι -> Fi
nset α) (a : α) : ∏ i in s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S 
i) 1 a) = (0 : Int)
参数：hs : s.Nonempty；S : ι -> Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.prod_indicator_biUnion_sub_indicator`：prod_indicator_biUnion_sub_
indicator (hs : s.Nonempty) (S : ι -> Set α) (a : α) : ∏ i in s, (Set.indicator 
(⋃ i in s, S i) 1 a - Set.indicat…
-/
lemma prod_indicator_biUnion_finset_sub_indicator (hs : s.Nonempty) (S : ι → Finset α) (a : α) :
    ∏ i ∈ s, (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) = (0 : ℤ) := by
  convert! prod_indicator_biUnion_sub_indicator hs (fun i ↦ S i) a
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **Inclusion-exclusion principle** for the sum of a function over a union.

The sum of a function `f` over the union of the `S i` over `i ∈ s` is the alternating sum of the
sums of `f` over the intersections of the `S i`. -/
/-
**Finset.inclusion_exclusion_sum_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inclusion_exclusion_sum_biUnion (s : Finset ι) (S : ι -> Finset α) (f : α 
-> G) : ∑ a in s.biUnion S, f a = ∑ t : s.powerset.filter (·.Nonempty), (-1) ^ (
#t.1 + 1) • ∑ a in t.1.inf' (mem_filter.1 t.2).2 S, f a
参数：s : Finset ι；S : ι -> Finset α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `smul_dite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : p → α) (b : ¬p → α) (c : β),   (c • if h : p then a…
· 使用定理 `Finset.sum_dite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f : (x : ι) → p x 
→ M) …
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
**Inclusion-exclusion principle** for the sum of a function over a union.

The sum of a function `f` over the union of the `S i` over `i ∈ s` is the altern
ating sum of the
sums of `f` over the intersections of the `S i`.
-/
theorem inclusion_exclusion_sum_biUnion (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.biUnion S, f a = ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a := by
  classical
  rw [← sub_eq_zero]
  calc
    ∑ a ∈ s.biUnion S, f a - ∑ t : s.powerset.filter (·.Nonempty),
      (-1) ^ (#t.1 + 1) • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a
      = ∑ t : s.powerset.filter (·.Nonempty),
          (-1) ^ #t.1 • ∑ a ∈ t.1.inf' (mem_filter.1 t.2).2 S, f a +
          ∑ t ∈ s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a ∈ s.biUnion S, f a := by
      simp [sub_eq_neg_add, ← sum_neg_distrib, filter_eq', pow_succ]
    _ = ∑ t ∈ s.powerset, (-1) ^ #t •
          if ht : t.Nonempty then ∑ a ∈ t.inf' ht S, f a else ∑ a ∈ s.biUnion S, f a := by
      rw [← sum_attach (filter ..)]; simp [sum_dite]
    _ = ∑ a ∈ s.biUnion S, (∏ i ∈ s, (1 - Set.indicator (S i) 1 a : ℤ)) • f a := by
      simp only [Int.reduceNeg, prod_sub, sum_comm (s := s.biUnion S), sum_smul, mul_assoc]
      congr! with t
      split_ifs with ht
      · obtain ⟨i, hi⟩ := ht
        simp only [prod_const_one, prod_indicator_apply]
        simp only [smul_sum, Set.indicator, Set.mem_iInter, mem_coe, Pi.one_apply, mul_ite, mul_one,
          mul_zero, ite_smul, zero_smul, sum_ite, not_forall, sum_const_zero, add_zero]
        congr
        aesop
      · obtain rfl := not_nonempty_iff_eq_empty.1 ht
        simp
    _ = ∑ a ∈ s.biUnion S, (∏ i ∈ s,
          (Set.indicator (s.biUnion S) 1 a - Set.indicator (S i) 1 a) : ℤ) • f a := by
      congr! with t; rw [Set.indicator_of_mem ‹_›, Pi.one_apply]
    _ = 0 := by
      obtain rfl | hs := s.eq_empty_or_nonempty <;>
        simp [-coe_biUnion, prod_indicator_biUnion_finset_sub_indicator, *]

/-- **Inclusion-exclusion principle** for the cardinality of a union.

The cardinality of the union of the `S i` over `i ∈ s` is the alternating sum of the cardinalities
of the intersections of the `S i`. -/
/-
**Finset.inclusion_exclusion_card_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inclusion_exclusion_card_biUnion (s : Finset ι) (S : ι -> Finset α) : #(s.
biUnion S) = ∑ t : s.powerset.filter (·.Nonempty), (-1 : Int) ^ (#t.1 + 1) * #(t
.1.inf' (mem_filter.1 t.2).2 S)
参数：s : Finset ι；S : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.inclusion_exclusion_sum_biUnion`：inclusion_exclusion_sum_biUnion 
(s : Finset ι) (S : ι -> Finset α) (f : α -> G) : ∑ a in s.biUnion S, f a = ∑ t 
: s.powerset.filter (·.Nonem…

--- 原说明 ---
**Inclusion-exclusion principle** for the cardinality of a union.

The cardinality of the union of the `S i` over `i ∈ s` is the alternating sum of
 the cardinalities
of the intersections of the `S i`.
-/
theorem inclusion_exclusion_card_biUnion (s : Finset ι) (S : ι → Finset α) :
    #(s.biUnion S) = ∑ t : s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t.1 + 1) * #(t.1.inf' (mem_filter.1 t.2).2 S) := by
  simpa using inclusion_exclusion_sum_biUnion (G := ℤ) s S (f := 1)

variable [Fintype α]

/-- **Inclusion-exclusion principle** for the sum of a function over an intersection of complements.

The sum of a function `f` over the intersection of the complements of the `S i` over `i ∈ s` is the
alternating sum of the sums of `f` over the intersections of the `S i`. -/
/-
**Finset.inclusion_exclusion_sum_inf_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inclusion_exclusion_sum_inf_compl (s : Finset ι) (S : ι -> Finset α) (f : 
α -> G) : ∑ a in s.inf fun i => (S i)ᶜ, f a = ∑ t in s.powerset, (-1) ^ #t • ∑ a
 in t.inf S, f a
参数：s : Finset ι；S : ι -> Finset α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compl_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : BooleanAlgebra
 α] (s : Finset ι) (f : ι → α), (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Finset.sum_compl_add_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.inclusion_exclusion_sum_biUnion`：inclusion_exclusion_sum_biUnion 
(s : Finset ι) (S : ι -> Finset α) (f : α -> G) : ∑ a in s.biUnion S, f a = ∑ t 
: s.powerset.filter (·.Nonem…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.inf'_eq_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeI
nf α] [inst_1 : OrderTop α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.inf
' H f = …
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Inclusion-exclusion principle** for the sum of a function over an intersection
 of complements.

The sum of a function `f` over the intersection of the complements of the `S i` 
over `i ∈ s` is the
alternating sum of the sums of `f` over the intersections of the `S i`.
-/
theorem inclusion_exclusion_sum_inf_compl (s : Finset ι) (S : ι → Finset α) (f : α → G) :
    ∑ a ∈ s.inf fun i ↦ (S i)ᶜ, f a = ∑ t ∈ s.powerset, (-1) ^ #t • ∑ a ∈ t.inf S, f a := by
  classical
  calc
    ∑ a ∈ s.inf fun i ↦ (S i)ᶜ, f a
      = ∑ a, f a - ∑ a ∈ s.biUnion S, f a := by
      rw [← Finset.compl_sup, sup_eq_biUnion, eq_sub_iff_add_eq, sum_compl_add_sum]
    _ = ∑ t ∈ s.powerset.filter (¬ ·.Nonempty), (-1) ^ #t • ∑ a ∈ t.inf S, f a
          + ∑ t ∈ s.powerset.filter (·.Nonempty), (-1) ^ #t • ∑ a ∈ t.inf S, f a := by
      simp [← sum_attach (filter ..), inclusion_exclusion_sum_biUnion, inf'_eq_inf, filter_eq',
        sub_eq_add_neg, pow_succ]
    _ = ∑ t ∈ s.powerset, (-1) ^ #t • ∑ a ∈ t.inf S, f a := sum_filter_not_add_sum_filter ..

/-- **Inclusion-exclusion principle** for the cardinality of an intersection of complements.

The cardinality of the intersection of the complements of the `S i` over `i ∈ s` is the
alternating sum of the cardinalities of the intersections of the `S i`. -/
/-
**Finset.inclusion_exclusion_card_inf_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inclusion_exclusion_card_inf_compl (s : Finset ι) (S : ι -> Finset α) : #(
s.inf fun i => (S i)ᶜ) = ∑ t in s.powerset, (-1 : Int) ^ #t * #(t.inf S)
参数：s : Finset ι；S : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.inclusion_exclusion_sum_inf_compl`：inclusion_exclusion_sum_inf_co
mpl (s : Finset ι) (S : ι -> Finset α) (f : α -> G) : ∑ a in s.inf fun i => (S i
)ᶜ, f a = ∑ t in s.powerset, (…

--- 原说明 ---
**Inclusion-exclusion principle** for the cardinality of an intersection of comp
lements.

The cardinality of the intersection of the complements of the `S i` over `i ∈ s`
 is the
alternating sum of the cardinalities of the intersections of the `S i`.
-/
theorem inclusion_exclusion_card_inf_compl (s : Finset ι) (S : ι → Finset α) :
    #(s.inf fun i ↦ (S i)ᶜ) = ∑ t ∈ s.powerset, (-1 : ℤ) ^ #t * #(t.inf S) := by
  simpa using inclusion_exclusion_sum_inf_compl (G := ℤ) s S (f := 1)

end Finset

