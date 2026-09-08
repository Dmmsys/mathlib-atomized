/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Data.Nat.Squarefree

/-!
# The Marica-Schönheim special case of Graham's conjecture

Graham's conjecture states that if $0 < a_1 < \dots a_n$ are integers, then
$\max_{i, j} \frac{a_i}{\gcd(a_i, a_j)} \ge n$. This file proves the conjecture when the $a_i$ are
squarefree as a corollary of the Marica-Schönheim inequality.

## References

[*Applications of the FKG Inequality and Its Relatives*, Graham][Graham1983]
-/

@[expose] public section

open Finset
open scoped FinsetFamily

namespace Nat

/-- Statement of Graham's conjecture (which is now a theorem in the literature).

Graham's conjecture states that if $0 < a_1 < \dots a_n$ are integers, then
$\max_{i, j} \frac{a_i}{\gcd(a_i, a_j)} \ge n$. -/
/-
**Nat.GrahamConjecture** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：GrahamConjecture (n : Nat) (f : Nat -> Nat) : Prop
参数：n : Nat；f : Nat -> Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Statement of Graham's conjecture (which is now a theorem in the literature).

Graham's conjecture states that if $0 < a_1 < \dots a_n$ are integers, then
$\max_{i, j} \frac{a_i}{\gcd(a_i, a_j)} \ge n$.
-/
def GrahamConjecture (n : ℕ) (f : ℕ → ℕ) : Prop :=
  n ≠ 0 → StrictMonoOn f (Set.Iio n) → ∃ i < n, ∃ j < n, (f i).gcd (f j) * n ≤ f i

/-- The special case of Graham's conjecture where all numbers are squarefree. -/
/-
**Nat.grahamConjecture_of_squarefree** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：grahamConjecture_of_squarefree {n : Nat} (f : Nat -> Nat) (hf' : forall k 
< n, Squarefree (f k)) : GrahamConjecture n f
参数：f : Nat -> Nat；hf' : forall k < n, Squarefree (f k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Nat.prod_primeFactors_invOn_squarefree`：prod_primeFactors_invOn_squarefr
ee : Set.InvOn (fun n : Nat => (factorization n).support) (fun s => ∏ p in s, p)
 {s | forall p in s, p.Prime…
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Nat.card_Iio`：card_Iio : #(Iio b) = b
· 使用引理 `Finset.card_le_card_diffs`：Finset.card_le_card_diffs (s : Finset α) : #s
 <= #(s \\ s)
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_div_gcd`：primeFactors_div_gcd (hm : Squarefree m) (hn :
 n != 0) : primeFactors (m / m.gcd n) = primeFactors m \ primeFactors n
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.gcd_le_left`：∀ {m : ℕ} (n : ℕ), 0 < m → m.gcd n ≤ m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `Nat.div_lt_of_lt_mul`：∀ {m n k : ℕ}, m < n * k → m / n < k
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Nat.card_Ioo`：∀ (a b : ℕ), (Finset.Ioo a b).card = b - a - 1
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The special case of Graham's conjecture where all numbers are squarefree.
-/
lemma grahamConjecture_of_squarefree {n : ℕ} (f : ℕ → ℕ) (hf' : ∀ k < n, Squarefree (f k)) :
    GrahamConjecture n f := by
  rintro hn hf
  by_contra!
  set 𝒜 := (Iio n).image fun n ↦ primeFactors (f n)
  have hf'' : ∀ i < n, ∀ j, Squarefree (f i / (f i).gcd (f j)) :=
    fun i hi j ↦ (hf' _ hi).squarefree_of_dvd <| div_dvd_of_dvd <| gcd_dvd_left _ _
  refine lt_irrefl n ?_
  calc
    n = #𝒜 := ?_
    _ ≤ #(𝒜 \\ 𝒜) := 𝒜.card_le_card_diffs
    _ ≤ #(Ioo 0 n) := card_le_card_of_injOn (fun s ↦ ∏ p ∈ s, p) ?_ ?_
    _ = n - 1 := by rw [card_Ioo, tsub_zero]
    _ < n := tsub_lt_self hn.bot_lt zero_lt_one
  · rw [Finset.card_image_of_injOn, card_Iio]
    simpa using! prod_primeFactors_invOn_squarefree.2.injOn.comp hf.injOn hf'
  · simp only [𝒜, forall_mem_diffs, forall_mem_image, mem_Ioo, mem_Iio, Set.MapsTo, mem_coe]
    rintro i hi j hj
    rw [← primeFactors_div_gcd (hf' _ hi) (hf' _ hj).ne_zero,
      prod_primeFactors_of_squarefree <| hf'' _ hi _]
    exact ⟨Nat.div_pos (gcd_le_left _ (hf' _ hi).ne_zero.bot_lt) <|
      Nat.gcd_pos_of_pos_left _ (hf' _ hi).ne_zero.bot_lt, Nat.div_lt_of_lt_mul <| this _ hi _ hj⟩
  · simp only [𝒜, Set.InjOn, mem_coe, forall_mem_diffs, forall_mem_image, mem_Iio]
    rintro a ha b hb c hc d hd
    rw [← primeFactors_div_gcd (hf' _ ha) (hf' _ hb).ne_zero, ← primeFactors_div_gcd
      (hf' _ hc) (hf' _ hd).ne_zero, prod_primeFactors_of_squarefree (hf'' _ ha _),
      prod_primeFactors_of_squarefree (hf'' _ hc _)]
    rintro h
    rw [h]

end Nat

