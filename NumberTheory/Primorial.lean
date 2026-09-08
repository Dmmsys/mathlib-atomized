/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Squarefree

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notation

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

@[expose] public section


open Finset

open Nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
/-
**primorial** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：primorial (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The primorial `n#` of `n` is the product of the primes less than or equal to `n`
.
-/
def primorial (n : ℕ) : ℕ := ∏ p ∈ range (n + 1) with p.Prime, p

local notation x "#" => primorial x
/-
**primorial_eq_prod_primesLE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：primorial_eq_prod_primesLE (n : Nat) : n # = ∏ p in primesLE n, p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma primorial_eq_prod_primesLE (n : ℕ) : n # = ∏ p ∈ primesLE n, p := rfl
/-
**primeFactors_primorial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：primeFactors_primorial (n : Nat) : primeFactors (n#) = primesLE n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `primorial_eq_prod_primesLE`：primorial_eq_prod_primesLE (n : Nat) : n # =
 ∏ p in primesLE n, p
· 使用引理 `Nat.primeFactors_prod`：primeFactors_prod (hs : forall p in s, p.Prime) :
 primeFactors (∏ p in s, p) = s
· 使用引理 `Nat.prime_of_mem_primesLE`：prime_of_mem_primesLE (hp : p in primesLE n) 
: p.Prime
-/
lemma primeFactors_primorial (n : ℕ) : primeFactors (n#) = primesLE n := by
  rw [primorial_eq_prod_primesLE]
  exact primeFactors_prod fun _ hp ↦ prime_of_mem_primesLE hp
/-
**primorial_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
@[simp] theorem primorial_zero : 0 # = 1 := by decide
/-
**primorial_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
@[simp] theorem primorial_one : 1 # = 1 := by decide
/-
**primorial_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial 2 = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
@[simp] theorem primorial_two : 2 # = 2 := by decide
/-
**primorial_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_pos (n : Nat) : 0 < n#
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem primorial_pos (n : ℕ) : 0 < n# :=
  prod_pos fun _p hp ↦ (mem_filter.1 hp).2.pos
/-
**primorial_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：primorial_ne_zero (n : Nat) : n# != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `primorial_pos`：primorial_pos (n : Nat) : 0 < n#
-/
lemma primorial_ne_zero (n : ℕ) : n# ≠ 0 := (primorial_pos n).ne'
/-
**primorial_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_mono {m n : Nat} (h : m <= n) : m# <= n#
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le'`：prod_le_prod_of_subset_of_one_
le' [MulLeftMono N] (h : s subseteq t) (hf : forall i in t, i ∉ s -> 1 <= f i) :
 ∏ i in s, f i <= ∏ i in t, f …
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
· 使用定理 `Finset.range_subset_range._gcongr_1`：∀ {n m : ℕ}, n ≤ m → Finset.range n
 ⊆ Finset.range m
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem primorial_mono {m n : ℕ} (h : m ≤ n) : m# ≤ n# :=
  prod_le_prod_of_subset_of_one_le' (by gcongr) (by grind)
/-
**primorial_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_monotone : Monotone primorial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `primorial_mono`：primorial_mono {m n : Nat} (h : m <= n) : m# <= n#
-/
theorem primorial_monotone : Monotone primorial := fun _ _ ↦ primorial_mono
/-
**primorial_dvd_primorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_dvd_primorial {m n : Nat} (h : m <= n) : m# ∣ n#
参数：h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dvd_prod_of_subset`：prod_dvd_prod_of_subset {ι M : Type*} [C
ommMonoid M] (s t : Finset ι) (f : ι -> M) (h : s subseteq t) : (∏ i in s, f i) 
∣ ∏ i in t, f i
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
· 使用定理 `Finset.range_subset_range._gcongr_1`：∀ {n m : ℕ}, n ≤ m → Finset.range n
 ⊆ Finset.range m
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem primorial_dvd_primorial {m n : ℕ} (h : m ≤ n) : m# ∣ n# :=
  prod_dvd_prod_of_subset _ _ _ (by gcongr)
/-
**primorial_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_succ {n : Nat} (hn1 : n != 1) (hn : Odd n) : (n + 1)# = n#
参数：hn1 : n != 1；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Nat.Prime.even_sub_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Even (p - 1)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
-/
theorem primorial_succ {n : ℕ} (hn1 : n ≠ 1) (hn : Odd n) : (n + 1)# = n# := by
  refine prod_congr ?_ fun _ _ ↦ rfl
  rw [range_add_one, filter_insert, if_neg fun h ↦ not_even_iff_odd.2 hn _]
  exact fun h ↦ h.even_sub_one <| mt succ.inj hn1
/-
**primorial_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_add (m n : Nat) : (m + n)# = m# * ∏ p in Ico (m + 1) (m + n + 1)
 with p.Prime, p
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_filter_filter`：∀ {α : Type u_1} {s t : Finset α} {p q : 
α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred q],   Disjoint s t → 
Disjoint (Finset.fi…
· 使用定理 `Finset.Ico_disjoint_Ico_consecutive`：Ico_disjoint_Ico_consecutive (a b c
 : α) : Disjoint (Ico a b) (Ico b c)
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `Finset.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <
= b) (hbc : b <= c) : Ico a b union Ico b c = Ico a c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem primorial_add (m n : ℕ) :
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union, ← filter_union, Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]
/-
**primorial_add_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_add_dvd {m n : Nat} (h : n <= m) : (m + n)# ∣ m# * choose (m + n
) m
参数：h : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `primorial_add`：primorial_add (m n : Nat) : (m + n)# = m# * ∏ p in Ico (m
 + 1) (m + n + 1) with p.Prime, p
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Finset.prod_primes_dvd`：Finset.prod_primes_dvd [CommMonoidWithZero M₀] [
IsCancelMulZero M₀] [Subsingleton M₀ˣ] {s : Finset M₀} (n : M₀) (h : forall a in
 s, Prime a)…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Nat.Prime.dvd_choose_add`：dvd_choose_add (hp : Prime p) (hap : a < p) (h
bp : b < p) (h : p <= a + b) : p ∣ choose (a + b) a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
-/
theorem primorial_add_dvd {m n : ℕ} (h : n ≤ m) : (m + n)# ∣ m# * choose (m + n) m :=
  calc
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
      mul_dvd_mul_left _ <|
        prod_primes_dvd _ (fun _ hk ↦ (mem_filter.1 hk).2.prime) fun p hp ↦ by
          rw [mem_filter, mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)
/-
**primorial_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_add_le {m n : Nat} (h : n <= m) : (m + n)# <= m# * choose (m + n
) m
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `primorial_pos`：primorial_pos (n : Nat) : 0 < n#
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `primorial_add_dvd`：primorial_add_dvd {m n : Nat} (h : n <= m) : (m + n)#
 ∣ m# * choose (m + n) m
-/
theorem primorial_add_le {m n : ℕ} (h : n ≤ m) : (m + n)# ≤ m# * choose (m + n) m :=
  le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)
/-
**Nat.Prime.dvd_primorial_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Prime.dvd_primorial_iff {p n : Nat} (hp : Prime p) : p ∣ n# ↔ p <= n
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
-/
lemma Nat.Prime.dvd_primorial_iff {p n : ℕ} (hp : Prime p) : p ∣ n# ↔ p ≤ n := by
  refine ⟨?_, fun h ↦ dvd_prod_of_mem _ (by grind)⟩
  intro h
  simp only [primorial, hp.prime.dvd_finsetProd_iff, mem_filter, mem_range_succ_iff] at h
  obtain ⟨q, ⟨hqn, hq⟩, hpq⟩ := h
  exact (Nat.le_of_dvd hq.pos hpq).trans hqn
/-
**Nat.Prime.dvd_primorial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Prime.dvd_primorial {p : Nat} (hp : Prime p) : p ∣ p#
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.Prime.dvd_primorial_iff`：Nat.Prime.dvd_primorial_iff {p n : Nat} (hp
 : Prime p) : p ∣ n# ↔ p <= n
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Nat.Prime.dvd_primorial {p : ℕ} (hp : Prime p) : p ∣ p# :=
  hp.dvd_primorial_iff.2 le_rfl
/-
**Squarefree.dvd_primorial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Squarefree.dvd_primorial {n : Nat} (hn : Squarefree n) : n ∣ n#
参数：hn : Squarefree n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_dvd_prod_of_subset`：prod_dvd_prod_of_subset {ι M : Type*} [C
ommMonoid M] (s t : Finset ι) (f : ι -> M) (h : s subseteq t) : (∏ i in s, f i) 
∣ ∏ i in t, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
-/
lemma Squarefree.dvd_primorial {n : ℕ} (hn : Squarefree n) : n ∣ n# := by
  have : (∏ p ∈ n.primeFactors, p) ∣ (∏ p ∈ range (n + 1) with p.Prime, p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by grind [le_of_dvd])
  rwa [Nat.prod_primeFactors_of_squarefree hn] at this
/-
**lt_primorial_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_primorial_self {n : Nat} (hn : 2 < n) : n < n#
参数：hn : 2 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.single_le_prod'`：single_le_prod' [MulLeftMono N] (hf : forall i i
n s, 1 <= f i) {a} (h : a in s) : f a <= ∏ x in s, f x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.Prime.dvd_primorial_iff`：Nat.Prime.dvd_primorial_iff {p n : Nat} (hp
 : Prime p) : p ∣ n# ↔ p <= n
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
-/
lemma lt_primorial_self {n : ℕ} (hn : 2 < n) : n < n# := by
  have : 3 ≤ n# := single_le_prod' (f := id) (by grind [→ Prime.pos]) (by grind [prime_three])
  let q := (n# - 1).minFac
  have : n < q := by
    by_contra! h1
    replace h1 : q ∣ n# := (minFac_prime (by lia)).dvd_primorial_iff.2 h1
    grind [minFac_eq_one_iff, dvd_one, dvd_sub_iff_right, minFac_dvd]
  grind [Nat.minFac_le]
/-
**le_primorial_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_primorial_self {n : Nat} : n <= n#
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_primorial_self`：lt_primorial_self {n : Nat} (hn : 2 < n) : n < n#
-/
lemma le_primorial_self {n : ℕ} : n ≤ n# := by
  obtain hn | hn := le_or_gt n 2
  · decide +revert
  · exact (lt_primorial_self hn).le
/-
**primorial_lt_four_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_lt_four_pow (n : Nat) (hn : n != 0) : n# < 4 ^ n
参数：n : Nat；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `primorial_add_le`：primorial_add_le {m n : Nat} (h : n <= m) : (m + n)# <
= m# * choose (m + n) m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.mul_lt_mul_of_lt_of_le`：∀ {a c b d : ℕ}, a < c → b ≤ d → 0 < d → a *
 b < c * d
· 使用定理 `Nat.choose_middle_le_pow`：choose_middle_le_pow (n : Nat) : (2 * n + 1).c
hoose n <= 4 ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `primorial_succ`：primorial_succ {n : Nat} (hn1 : n != 1) (hn : Odd n) : (
n + 1)# = n#
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `four_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Partial
Order α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem primorial_lt_four_pow (n : ℕ) (hn : n ≠ 0) : n# < 4 ^ n := by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ ≤ (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ ≤ 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ ≤ 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ
/-
**primorial_le_four_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：primorial_le_four_pow (n : Nat) : n# <= 4 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `primorial_lt_four_pow`：primorial_lt_four_pow (n : Nat) (hn : n != 0) : n
# < 4 ^ n
-/
theorem primorial_le_four_pow (n : ℕ) : n# ≤ 4 ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

@[deprecated (since := "2026-03-21")] alias primorial_le_4_pow := primorial_le_four_pow
/-
**squarefree_primorial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：squarefree_primorial (n : Nat) : Squarefree (n#)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `primorial_eq_prod_primesLE`：primorial_eq_prod_primesLE (n : Nat) : n # =
 ∏ p in primesLE n, p
· 使用定理 `Finset.squarefree_prod_of_pairwise_isCoprime`：Finset.squarefree_prod_of_
pairwise_isCoprime {ι : Type*} {s : Finset ι} {f : ι -> R} (hs : Set.Pairwise s 
(IsRelPrime on f)) (hs' : forall i…
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
· 使用引理 `Nat.prime_of_mem_primesLE`：prime_of_mem_primesLE (hp : p in primesLE n) 
: p.Prime
· 使用定理 `Irreducible.squarefree`：Irreducible.squarefree [CommMonoid R] {x : R} (h
 : Irreducible x) : Squarefree x
-/
lemma squarefree_primorial (n : ℕ) : Squarefree (n#) := by
  rw [primorial_eq_prod_primesLE]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq ↦ ?_)
    fun _ hp ↦ (prime_of_mem_primesLE hp).squarefree
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq
