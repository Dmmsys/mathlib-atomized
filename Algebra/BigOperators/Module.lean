/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel

/-!
# Summation by parts
-/

public section

namespace Finset
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i ∈ range n, g i

/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
/-
**Finset.sum_Ico_by_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_Ico_by_parts (hmn : m < n) : ∑ i in Ico m n, f i • g i = f (n - 1) • G
 n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f i) • G (i + 1)
参数：hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Finset.sum_Ico_add'`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAdd
Monoid α]…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_Ico_sub_bot`：∀ {M : Type u_4} (f : ℕ → M) {m n : ℕ} [inst : A
ddCommGroup M],   m < n → ∑ i ∈ Finset.Ico m n, f i - f m = ∑ i ∈ Finset.Ico (m 
+ 1) n, f i
· 使用定理 `Finset.sum_Ico_succ_sub_top`：∀ {M : Type u_4} (f : ℕ → M) {m n : ℕ} [ins
t : AddCommGroup M],   m ≤ n → ∑ i ∈ Finset.Ico m (n + 1), f i - f n = ∑ i ∈ Fin
set.Ico m n, f i
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Finset.sum_eq_sum_Ico_succ_bot`：∀ {M : Type u_2} [inst : AddCommMonoid M
] {a b : ℕ},   a < b → ∀ (f : ℕ → M), ∑ k ∈ Finset.Ico a b, f k = f a + ∑ k ∈ Fi
nset.Ico (a + 1) b, …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `_private.Mathlib.Algebra.BigOperators.Module.0.Finset.sum_Ico_by_parts._
abel_1_1`：∀ {R : Type u_2} {M : Type u_1} [inst : Ring R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M] (f : ℕ → R)   (g : ℕ → M) (i : ℕ),   …
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
**Summation by parts**, also known as **Abel's lemma** or an **Abel transformati
on**
-/
theorem sum_Ico_by_parts (hmn : m < n) :
    ∑ i ∈ Ico m n, f i • g i =
      f (n - 1) • G n - f m • G m - ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  have h₁ : (∑ i ∈ Ico (m + 1) n, f i • G i) = ∑ i ∈ Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn), ← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i ∈ Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i ∈ Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) := by
    rw [← sum_Ico_sub_bot _ hmn, ← sum_Ico_succ_sub_top _ (Nat.le_sub_one_of_lt hmn),
      Nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  conv in (occs := 3) (f _ • g _) => rw [← sum_range_succ_sub_sum g]
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  conv_lhs => congr; rfl; rw [← add_sub, add_comm, ← add_sub, ← sum_sub_distrib]
  have : ∀ i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) := by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  abel
/-
**Finset.sum_Ioc_by_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_Ioc_by_parts (hmn : m < n) : ∑ i in Ioc m n, f i • g i = f n • G (n + 
1) - f (m + 1) • G (m + 1) - ∑ i in Ioc m (n - 1), (f (i + 1) - f i) • G (i + 1)
参数：hmn : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Finset.sum_Ico_by_parts`：sum_Ico_by_parts (hmn : m < n) : ∑ i in Ico m n
, f i • g i = f (n - 1) • G n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f
 i) • G (i + …
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
-/
theorem sum_Ioc_by_parts (hmn : m < n) :
    ∑ i ∈ Ioc m n, f i • g i =
      f n • G (n + 1) - f (m + 1) • G (m + 1)
        - ∑ i ∈ Ioc m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  simpa only [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    add_tsub_cancel_right] using! sum_Ico_by_parts f g (Nat.succ_lt_succ hmn)

variable (n)

/-- **Summation by parts** for ranges -/
/-
**Finset.sum_range_by_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_range_by_parts : ∑ i in range n, f i • g i = f (n - 1) • G n - ∑ i in 
range (n - 1), (f (i + 1) - f i) • G (i + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.sum_Ico_by_parts`：sum_Ico_by_parts (hmn : m < n) : ∑ i in Ico m n
, f i • g i = f (n - 1) • G n - f m • G m - ∑ i in Ico m (n - 1), (f (i + 1) - f
 i) • G (i + …
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Finset.sum_range_zero`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f : ℕ 
→ M), ∑ k ∈ Finset.range 0, f k = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
**Summation by parts** for ranges
-/
theorem sum_range_by_parts :
    ∑ i ∈ range n, f i • g i =
      f (n - 1) • G n - ∑ i ∈ range (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [range_eq_Ico]
    rw [sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn), sum_range_zero, smul_zero, sub_zero]
    simp only [← range_eq_Ico]

end Finset

