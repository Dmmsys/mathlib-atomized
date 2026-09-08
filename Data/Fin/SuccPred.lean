/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# Successors and predecessor operations of `Fin n`

This file contains a number of definitions and lemmas
related to `Fin.succ`, `Fin.pred`, and related operations on `Fin n`.

## Main definitions

* `finCongr` : `Fin.cast` as an `Equiv`, equivalence between `Fin n` and `Fin m` when `n = m`;
* `Fin.succAbove` : embeds `Fin n` into `Fin (n + 1)` skipping `p`.
* `Fin.predAbove` : the (partial) inverse of `Fin.succAbove`.

-/

@[expose] public section

assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

namespace Fin

variable {n m : ℕ}

section Succ

/-!
### succ and casts into larger Fin types
-/

/-
**Fin.succ_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succ_injective (n : Nat) : Injective (@Fin.succ n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
### succ and casts into larger Fin types
-/
lemma succ_injective (n : ℕ) : Injective (@Fin.succ n) := fun a b ↦ by simp [Fin.ext_iff]

@[simp]
/-
**Fin.exists_succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_succ_eq {x : Fin (n + 1)} : (exists y, Fin.succ y = x) ↔ x != 0
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
-/
theorem exists_succ_eq {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩
/-
**Fin.exists_succ_eq_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x != 0) : exists y, Fin.s
ucc y = x
参数：n + 1；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_succ_eq`：exists_succ_eq {x : Fin (n + 1)} : (exists y, Fin.su
cc y = x) ↔ x != 0
-/
theorem exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x ≠ 0) :
    ∃ y, Fin.succ y = x := exists_succ_eq.mpr h

@[simp]
/-
**Fin.succ_zero_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl
/-
**Fin.one_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Fin.succ_zero_eq_one'`：succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin 
n) = 1
-/
theorem one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1 := succ_zero_eq_one' (n := n) ▸ succ_pos _
/-
**Fin.zero_ne_one'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：zero_ne_one' [NeZero n] : (0 : Fin (n + 1)) != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.one_pos'`：one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1
-/
theorem zero_ne_one' [NeZero n] : (0 : Fin (n + 1)) ≠ 1 := Fin.ne_of_lt one_pos'

/--
The `Fin.succ_one_eq_two` in `Lean` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/-
**Fin.succ_one_eq_two'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `Fin.succ_one_eq_two` in `Lean` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

-- Version of `succ_one_eq_two` to be used by `dsimp`.
-- Note the `'` swapped around due to a move to std4.

/--
The `Fin.le_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[deprecated "use `nonpos_iff_eq_zero`" (since := "2026-05-11")]
/-
**Fin.le_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_zero_iff' {n : Nat} [NeZero n] {k : Fin n} : k <= 0 ↔ k = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `Fin.le_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem le_zero_iff' {n : ℕ} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.ext <| by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩

-- TODO: Move to Batteries
/-
**Fin.castLE_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n m : ℕ} {hmn : m ≤ n} {a b : Fin m}, Fin.castLE hmn a = Fin.castLE hmn
 b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma castLE_inj {hmn : m ≤ n} {a b : Fin m} : castLE hmn a = castLE hmn b ↔ a = b := by
  simp [Fin.ext_iff]
/-
**Fin.castAdd_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n m : ℕ} {a b : Fin m}, Fin.castAdd n a = Fin.castAdd n b ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [Fin.ext_iff]

attribute [simp] castSucc_inj
/-
**Fin.castLE_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castLE_injective (hmn : m <= n) : Injective (castLE hmn)
参数：hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma castLE_injective (hmn : m ≤ n) : Injective (castLE hmn) :=
  fun _ _ hab ↦ Fin.ext (congr_arg val hab :)
/-
**Fin.castAdd_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castAdd_injective (m n : Nat) : Injective (@Fin.castAdd m n)
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.castLE_injective`：castLE_injective (hmn : m <= n) : Injective (castL
E hmn)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
lemma castAdd_injective (m n : ℕ) : Injective (@Fin.castAdd m n) := castLE_injective _
/-
**Fin.castSucc_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castSucc_injective (n : Nat) : Injective (@Fin.castSucc n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.castAdd_injective`：castAdd_injective (m n : Nat) : Injective (@Fin.c
astAdd m n)
-/
lemma castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) := castAdd_injective _ _
/-
**Fin.castLE_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n m : ℕ} (i : Fin n) (h : n + 1 ≤ m), Fin.castLE h i.castSucc = Fin.cas
tLE ⋯ i
参数：i : Fin n；h : n + 1 ≤ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma castLE_castSucc {n m} (i : Fin n) (h : n + 1 ≤ m) :
    i.castSucc.castLE h = i.castLE (Nat.le_of_succ_le h) :=
  rfl
/-
**Fin.castLE_comp_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n m : ℕ} (h : n + 1 ≤ m), Fin.castLE h ∘ Fin.castSucc = Fin.castLE ⋯
参数：h : n + 1 ≤ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma castLE_comp_castSucc {n m} (h : n + 1 ≤ m) :
    Fin.castLE h ∘ Fin.castSucc = Fin.castLE (Nat.le_of_succ_le h) :=
  rfl
/-
**Fin.castLE_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ), Fin.castLE ⋯ = id
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] lemma castLE_rfl (n : ℕ) : Fin.castLE (le_refl n) = id :=
  rfl

@[simp]
/-
**Fin.range_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_castLE {n k : Nat} (h : n <= k) : Set.range (castLE h) = { i : Fin k
 | (i : Nat) < n }
参数：h : n <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem range_castLE {n k : ℕ} (h : n ≤ k) : Set.range (castLE h) = { i : Fin k | (i : ℕ) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

@[simp]
/-
**Fin.coe_of_injective_castLE_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_of_injective_castLE_symm {n k : Nat} (h : n <= k) (i : Fin k) (hi) : (
(Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : Nat) = i
参数：h : n <= k；i : Fin k；hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Fin.castLE_injective`：castLE_injective (hmn : m <= n) : Injective (castL
E hmn)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_castLE`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), ↑(Fin.castLE h i) =
 ↑i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
-/
theorem coe_of_injective_castLE_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← val_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)
/-
**Fin.leftInverse_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：leftInverse_cast (eq : n = m) : LeftInverse (Fin.cast eq.symm) (Fin.cast e
q)
参数：eq : n = m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem leftInverse_cast (eq : n = m) : LeftInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl
/-
**Fin.rightInverse_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rightInverse_cast (eq : n = m) : RightInverse (Fin.cast eq.symm) (Fin.cast
 eq)
参数：eq : n = m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem rightInverse_cast (eq : n = m) : RightInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl

@[simp]
/-
**Fin.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_inj (eq : n = m) {a b : Fin n} : a.cast eq = b.cast eq ↔ a = b
参数：eq : n = m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cast_inj (eq : n = m) {a b : Fin n} : a.cast eq = b.cast eq ↔ a = b := by
  simp [← val_inj]

@[simp]
/-
**Fin.cast_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_lt_cast (eq : n = m) {a b : Fin n} : a.cast eq < b.cast eq ↔ a < b
参数：eq : n = m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt_cast (eq : n = m) {a b : Fin n} : a.cast eq < b.cast eq ↔ a < b :=
  Iff.rfl

@[simp]
/-
**Fin.cast_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_le_cast (eq : n = m) {a b : Fin n} : a.cast eq <= b.cast eq ↔ a <= b
参数：eq : n = m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_le_cast (eq : n = m) {a b : Fin n} : a.cast eq ≤ b.cast eq ↔ a ≤ b :=
  Iff.rfl

/-- The 'identity' equivalence between `Fin m` and `Fin n` when `m = n`. -/
@[simps apply]
/-
**Fin._root_.finCongr** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 'identity' equivalence between `Fin m` and `Fin n` when `m = n`.
-/
def _root_.finCongr (eq : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast eq
  invFun := Fin.cast eq.symm
  left_inv := leftInverse_cast eq
  right_inv := rightInverse_cast eq
/-
**Fin._root_.finCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.finCongr_symm_apply (eq : n = m) (a : Fin m) :
    (finCongr eq).symm a = a.cast eq.symm := rfl
/-
**Fin._root_.finCongr_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.finCongr_apply_mk (h : m = n) (k : ℕ) (hk : k < m) :
    finCongr h ⟨k, hk⟩ = ⟨k, h ▸ hk⟩ := rfl

@[simp]
/-
**Fin._root_.finCongr_refl** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.finCongr_refl (h : n = n := rfl) : finCongr h = Equiv.refl (Fin n) := by ext; simp
/-
**Fin._root_.finCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.finCongr_symm (h : m = n) : (finCongr h).symm = finCongr h.symm := rfl
/-
**Fin._root_.finCongr_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.finCongr_apply_coe (h : m = n) (k : Fin m) : (finCongr h k : ℕ) = k := rfl
/-
**Fin._root_.finCongr_symm_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.finCongr_symm_apply_coe (h : m = n) (k : Fin n) : ((finCongr h).symm k : ℕ) = k := rfl

/-- While in many cases `finCongr` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
/-
**Fin._root_.finCongr_eq_equivCast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While in many cases `finCongr` is better than `Equiv.cast`/`cast`, sometimes we 
want to apply
a generic theorem about `cast`.
-/
lemma _root_.finCongr_eq_equivCast (h : n = m) : finCongr h = .cast (h ▸ rfl) := by subst h; simp

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
/-
**Fin.cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_eq_cast (h : n = m) : (Fin.cast h : Fin n -> Fin m) = _root_.cast (h 
▸ rfl)
参数：h : n = m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we 
want to apply
a generic theorem about `cast`.
-/
theorem cast_eq_cast (h : n = m) : (Fin.cast h : Fin n → Fin m) = _root_.cast (h ▸ rfl) := by
  grind
/-
**Fin.castSucc_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem castSucc_le_succ {n} (i : Fin n) : i.castSucc ≤ i.succ := Nat.le_succ i
/-
**Fin.castSucc_le_castSucc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.castSucc ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem castSucc_le_castSucc_iff {a b : Fin n} : castSucc a ≤ castSucc b ↔ a ≤ b := .rfl
/-
**Fin.succ_le_castSucc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.castSucc ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem succ_le_castSucc_iff {a b : Fin n} : succ a ≤ castSucc b ↔ a < b := by
  rw [le_castSucc_iff, succ_lt_succ_iff]
/-
**Fin.castSucc_lt_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.succ ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem castSucc_lt_succ_iff {a b : Fin n} : castSucc a < succ b ↔ a ≤ b := by
  rw [castSucc_lt_iff_succ_le, succ_le_succ_iff]
/-
**Fin.le_of_castSucc_lt_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n} (hl : castSuc
c i < a) (hu : b < succ i) : b < a
参数：n + 1；hl : castSucc i < a；hu : b < succ i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n}
    (hl : castSucc i < a) (hu : b < succ i) : b < a := by
  simp [Fin.lt_def, -val_fin_lt] at *; lia
/-
**Fin.castSucc_lt_or_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p 
< i.succ
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ := by
  simp [Fin.lt_def, -val_fin_lt]
  lia
/-
**Fin.succ_le_or_le_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i <= p ∨ p <= 
i.castSucc
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `Fin.castSucc_lt_or_lt_succ`：castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i 
: Fin n) : castSucc i < p ∨ p < i.succ
-/
theorem succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i ≤ p ∨ p ≤ i.castSucc := by
  rw [le_castSucc_iff, ← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i
/-
**Fin.eq_castSucc_of_ne_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：eq_castSucc_of_ne_last {x : Fin (n + 1)} (h : x != (last _)) : exists y, F
in.castSucc y = x
参数：n + 1；h : x != (last _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_castSucc_eq`：∀ {n : ℕ} {i : Fin (n + 1)}, (∃ j, j.castSucc = 
i) ↔ i ≠ Fin.last n
-/
theorem eq_castSucc_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h
/-
**Fin.forall_fin_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_fin_succ' {P : Fin (n + 1) -> Prop} : (forall i, P i) ↔ (forall i :
 Fin n, P i.castSucc) ∧ P (.last _)
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_fin_succ' {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

-- to match `Fin.eq_zero_or_eq_succ`
/-
**Fin.eq_castSucc_or_eq_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) : (exists j : Fin n, i 
= j.castSucc) ∨ i = last n
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = j.castSucc) ∨ i = last n := i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

@[simp]
/-
**Fin.castSucc_ne_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_ne_last {n : Nat} (i : Fin n) : i.castSucc != .last n
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
-/
theorem castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ .last n :=
  Fin.ne_of_lt i.castSucc_lt_last
/-
**Fin.exists_fin_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_fin_succ' {P : Fin (n + 1) -> Prop} : (exists i, P i) ↔ (exists i :
 Fin n, P i.castSucc) ∨ P (.last _)
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem exists_fin_succ' {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (.last _) :=
  ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

/--
The `Fin.castSucc_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/-
**Fin.castSucc_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Fin.castSucc_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0 := rfl

@[simp]
/-
**Fin.castSucc_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_pos_iff [NeZero n] {i : Fin n} : 0 < castSucc i ↔ 0 < i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem castSucc_pos_iff [NeZero n] {i : Fin n} : 0 < castSucc i ↔ 0 < i := by simp [← val_pos_iff]

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis. -/
alias ⟨_, castSucc_pos'⟩ := castSucc_pos_iff

/-
**Fin.castSucc_ne_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i != 0
参数：h : p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i ≠ 0 := by
  cases n
  · exact i.elim0
  · grind [castSucc_ne_zero_iff]
/-
**Fin.succ_ne_last_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_ne_last_iff (a : Fin (n + 1)) : succ a != last (n + 1) ↔ a != last n
参数：a : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Fin.succ_eq_last_succ`：∀ {n : ℕ} {i : Fin n.succ}, i.succ = Fin.last (n 
+ 1) ↔ i = Fin.last n
-/
theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a ≠ last (n + 1) ↔ a ≠ last n :=
  not_iff_not.mpr <| succ_eq_last_succ
/-
**Fin.succ_ne_last_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i != last n
参数：h : i < p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i ≠ last n := by
  grind

open Fin.NatCast in
@[norm_cast, simp]
/-
**Fin.coe_eq_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_eq_castSucc {a : Fin n} : ((a : Nat) : Fin (n + 1)) = castSucc a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.val_cast_of_lt`：val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a
 < n) : (a : Fin n).val = a
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem coe_eq_castSucc {a : Fin n} : ((a : Nat) : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt_succ_of_lt a.is_lt)

open Fin.NatCast in
/-
**Fin.coe_succ_lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_succ_lt_iff_lt {n : Nat} {j k : Fin n} : (j : Fin (n + 1)) < k ↔ j < k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.coe_eq_castSucc`：coe_eq_castSucc {a : Fin n} : ((a : Nat) : Fin (n +
 1)) = castSucc a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin (n + 1)) < k ↔ j < k := by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]
/-
**Fin.range_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_castSucc {n : Nat} : Set.range (castSucc : Fin n -> Fin n.succ) = ({
 i | (i : Nat) < n } : Set (Fin n.succ))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.range_castLE`：range_castLE {n k : Nat} (h : n <= k) : Set.range (cas
tLE h) = { i : Fin k | (i : Nat) < n }
-/
theorem range_castSucc {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) := range_castLE (by lia)

@[simp]
/-
**Fin.coe_of_injective_castSucc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_of_injective_castSucc_symm {n : Nat} (i : Fin n.succ) (hi) : ((Equiv.o
fInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : Nat) = i
参数：i : Fin n.succ；hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Fin.castSucc_injective`：castSucc_injective (n : Nat) : Injective (@Fin.c
astSucc n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_castSucc`：∀ {n : ℕ} (i : Fin n), ↑i.castSucc = ↑i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
-/
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← val_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)
/-
**Fin.castSucc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_castAdd (i : Fin n) : castSucc (castAdd m i) = castAdd (m + 1) i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem castSucc_castAdd (i : Fin n) : castSucc (castAdd m i) = castAdd (m + 1) i := rfl
/-
**Fin.succ_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_castAdd (i : Fin n) : succ (castAdd m i) = if h : i.succ = last _ the
n natAdd n (0 : Fin (m + 1)) else castAdd (m + 1) ⟨i.1 + 1, lt_of_le_of_ne i.2 (
Fin.val_ne_iff.mpr h)⟩
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.val_ne_iff`：∀ {n : ℕ} {a b : Fin n}, ↑a ≠ ↑b ↔ a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem succ_castAdd (i : Fin n) : succ (castAdd m i) =
    if h : i.succ = last _ then natAdd n (0 : Fin (m + 1))
      else castAdd (m + 1) ⟨i.1 + 1, lt_of_le_of_ne i.2 (Fin.val_ne_iff.mpr h)⟩ := by
  split_ifs with h
  exacts [Fin.ext (congr_arg Fin.val h :), rfl]
/-
**Fin.succ_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_natAdd (i : Fin m) : succ (natAdd n i) = natAdd n (succ i)
参数：i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_natAdd (i : Fin m) : succ (natAdd n i) = natAdd n (succ i) := rfl
/-
**Fin.sub_castAdd_eq_castAdd_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sub_castAdd_eq_castAdd_sub_of_le {n : Nat} {a b : Fin n} (h : b <= a) : a.
castAdd m - b.castAdd m = (a - b).castAdd m
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_castAdd_eq_castAdd_sub_of_le {n : ℕ} {a b : Fin n} (h : b ≤ a) :
    a.castAdd m - b.castAdd m = (a - b).castAdd m := by
  grind [Fin.sub_val_of_le]
/-
**Fin.sub_castSucc_eq_castSucc_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sub_castSucc_eq_castSucc_sub_of_le {n : Nat} {a b : Fin n} (h : b <= a) : 
a.castSucc - b.castSucc = (a - b).castSucc
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.sub_castAdd_eq_castAdd_sub_of_le`：sub_castAdd_eq_castAdd_sub_of_le {
n : Nat} {a b : Fin n} (h : b <= a) : a.castAdd m - b.castAdd m = (a - b).castAd
d m
-/
theorem sub_castSucc_eq_castSucc_sub_of_le {n : ℕ} {a b : Fin n} (h : b ≤ a) :
    a.castSucc - b.castSucc = (a - b).castSucc := sub_castAdd_eq_castAdd_sub_of_le h

end Succ

section Pred

/-!
### pred
-/

/-
**Fin.pred_one'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_one' [NeZero n] (h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
### pred
-/
theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm) :
    Fin.pred (1 : Fin (n + 1)) h = 0 := by
  simp_rw [Fin.ext_iff, val_pred, val_one', val_zero, Nat.sub_eq_zero_iff_le, Nat.mod_le]
/-
**Fin.pred_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_last (h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pred_last (h := Fin.ext_iff.not.2 last_pos'.ne') :
    pred (last (n + 1)) h = last n := by simp_rw [← succ_last, pred_succ]
/-
**Fin.pred_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : pred i hi < j ↔ 
i < succ j
参数：n + 1；hi : i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi < j ↔ i < succ j := by
  rw [← succ_lt_succ_iff, succ_pred]
/-
**Fin.lt_pred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : j < pred i hi ↔ 
succ j < i
参数：n + 1；hi : i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : j < pred i hi ↔ succ j < i := by
  rw [← succ_lt_succ_iff, succ_pred]
/-
**Fin.pred_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : pred i hi <= j ↔
 i <= succ j
参数：n + 1；hi : i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi ≤ j ↔ i ≤ succ j := by
  rw [← succ_le_succ_iff, succ_pred]
/-
**Fin.le_pred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : j <= pred i hi ↔
 succ j <= i
参数：n + 1；hi : i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : j ≤ pred i hi ↔ succ j ≤ i := by
  rw [← succ_le_succ_iff, succ_pred]
/-
**Fin.castSucc_pred_eq_pred_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a != 0) : (a.pred h
a).castSucc = (castSucc a).pred (castSucc_ne_zero_iff.mpr ha)
参数：n + 1；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0) :
    (a.pred ha).castSucc = (castSucc a).pred (castSucc_ne_zero_iff.mpr ha) := rfl
/-
**Fin.castSucc_pred_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_pred_add_one_eq {a : Fin (n + 1)} (ha : a != 0) : (a.pred ha).cas
tSucc + 1 = a
参数：n + 1；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coeSucc_eq_succ`：∀ {n : ℕ} {a : Fin n}, a.castSucc + 1 = a.succ
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem castSucc_pred_add_one_eq {a : Fin (n + 1)} (ha : a ≠ 0) :
    (a.pred ha).castSucc + 1 = a := by
  simp
/-
**Fin.le_pred_castSucc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_pred_castSucc_iff {a b : Fin (n + 1)} (ha : castSucc a != 0) : b <= (ca
stSucc a).pred ha ↔ b < a
参数：n + 1；ha : castSucc a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_pred_iff`：le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
 : j <= pred i hi ↔ succ j <= i
· 使用定理 `Fin.succ_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.castSucc ↔
 a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_pred_castSucc_iff {a b : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    b ≤ (castSucc a).pred ha ↔ b < a := by
  rw [le_pred_iff, succ_le_castSucc_iff]
/-
**Fin.pred_castSucc_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha : castSucc a != 0) : (castSuc
c a).pred ha < b ↔ a <= b
参数：n + 1；ha : castSucc a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.pred_lt_iff`：pred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
 : pred i hi < j ↔ i < succ j
· 使用定理 `Fin.castSucc_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.succ ↔
 a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    (castSucc a).pred ha < b ↔ a ≤ b := by
  rw [pred_lt_iff, castSucc_lt_succ_iff]
/-
**Fin.pred_castSucc_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_castSucc_lt {a : Fin (n + 1)} (ha : castSucc a != 0) : (castSucc a).p
red ha < a
参数：n + 1；ha : castSucc a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.pred_castSucc_lt_iff`：pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha :
 castSucc a != 0) : (castSucc a).pred ha < b ↔ a <= b
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem pred_castSucc_lt {a : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    (castSucc a).pred ha < a := by rw [pred_castSucc_lt_iff, le_def]
/-
**Fin.le_castSucc_pred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_castSucc_pred_iff {a b : Fin (n + 1)} (ha : a != 0) : b <= castSucc (a.
pred ha) ↔ b < a
参数：n + 1；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, a.cas
tSucc ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castSucc_pred_eq_pred_castSucc`：castSucc_pred_eq_pred_castSucc {a : 
Fin (n + 1)} (ha : a != 0) : (a.pred ha).castSucc = (castSucc a).pred (castSucc_
ne_zero_iff.mpr ha)
· 使用定理 `Fin.le_pred_castSucc_iff`：le_pred_castSucc_iff {a b : Fin (n + 1)} (ha :
 castSucc a != 0) : b <= (castSucc a).pred ha ↔ b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_castSucc_pred_iff {a b : Fin (n + 1)} (ha : a ≠ 0) :
    b ≤ castSucc (a.pred ha) ↔ b < a := by
  rw [castSucc_pred_eq_pred_castSucc, le_pred_castSucc_iff]
/-
**Fin.castSucc_pred_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha : a != 0) : castSucc (a.pred 
ha) < b ↔ a <= b
参数：n + 1；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, a.cas
tSucc ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castSucc_pred_eq_pred_castSucc`：castSucc_pred_eq_pred_castSucc {a : 
Fin (n + 1)} (ha : a != 0) : (a.pred ha).castSucc = (castSucc a).pred (castSucc_
ne_zero_iff.mpr ha)
· 使用定理 `Fin.pred_castSucc_lt_iff`：pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha :
 castSucc a != 0) : (castSucc a).pred ha < b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha : a ≠ 0) :
    castSucc (a.pred ha) < b ↔ a ≤ b := by
  rw [castSucc_pred_eq_pred_castSucc, pred_castSucc_lt_iff]
/-
**Fin.castSucc_pred_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_pred_lt {a : Fin (n + 1)} (ha : a != 0) : castSucc (a.pred ha) < 
a
参数：n + 1；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castSucc_pred_lt_iff`：castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha :
 a != 0) : castSucc (a.pred ha) < b ↔ a <= b
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem castSucc_pred_lt {a : Fin (n + 1)} (ha : a ≠ 0) :
    castSucc (a.pred ha) < a := by rw [castSucc_pred_lt_iff, le_def]

end Pred

section CastPred

/-- `castPred i` sends `i : Fin (n + 1)` to `Fin n` as long as i ≠ last n. -/
/-
**Fin.castPred** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：{n : ℕ} → (i : Fin (n + 1)) → i ≠ Fin.last n → Fin n
参数：i : Fin (n + 1)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n

--- 原说明 ---
`castPred i` sends `i : Fin (n + 1)` to `Fin n` as long as i ≠ last n.
-/
@[inline] def castPred (i : Fin (n + 1)) (h : i ≠ last n) : Fin n := castLT i (val_lt_last h)

@[simp]
/-
**Fin.castLT_eq_castPred** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h'
参数：i : Fin (n + 1)；h : i < last _。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`castPred i` sends `i : Fin (n + 1)` to `Fin n` as long as i ≠ last n.
-/
lemma castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h' := Fin.ext_iff.not.2 h.ne) :
    castLT i h = castPred i h' := rfl

@[simp]
/-
**Fin.coe_castPred** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：coe_castPred (i : Fin (n + 1)) (h : i != last _) : (castPred i h : Nat) = 
i
参数：i : Fin (n + 1)；h : i != last _。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_castPred (i : Fin (n + 1)) (h : i ≠ last _) : (castPred i h : ℕ) = i := rfl

@[simp]
/-
**Fin.castPred_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_castSucc {i : Fin n} (h'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem castPred_castSucc {i : Fin n} (h' := Fin.ext_iff.not.2 (castSucc_lt_last i).ne) :
    castPred (castSucc i) h' = i := rfl

@[simp]
/-
**Fin.castSucc_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castSucc_castPred (i : Fin (n + 1)) (h : i != last n) : castSucc (i.castPr
ed h) = i
参数：i : Fin (n + 1)；h : i != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_castSucc_eq`：∀ {n : ℕ} {i : Fin (n + 1)}, (∃ j, j.castSucc = 
i) ↔ i ≠ Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
-/
theorem castSucc_castPred (i : Fin (n + 1)) (h : i ≠ last n) :
    castSucc (i.castPred h) = i := by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]
/-
**Fin.castPred_eq_iff_eq_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_eq_iff_eq_castSucc (i : Fin (n + 1)) (hi : i != last _) (j : Fin 
n) : castPred i hi = j ↔ i = castSucc j
参数：i : Fin (n + 1)；hi : i != last _；j : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.castPred.congr_simp`：∀ {n : ℕ} (i i_1 : Fin (n + 1)) (e_i : i = i_1)
 (h : i ≠ Fin.last n), i.castPred h = i_1.castPred ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem castPred_eq_iff_eq_castSucc (i : Fin (n + 1)) (hi : i ≠ last _) (j : Fin n) :
    castPred i hi = j ↔ i = castSucc j :=
  ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]
/-
**Fin.castPred_mk** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_mk (i : Nat) (h₁ : i < n) (h₂
参数：i : Nat；h₁ : i < n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem castPred_mk (i : ℕ) (h₁ : i < n) (h₂ := h₁.trans (Nat.lt_succ_self _))
    (h₃ : ⟨i, h₂⟩ ≠ last _ := (ne_iff_vne _ _).mpr (val_last _ ▸ h₁.ne)) :
    castPred ⟨i, h₂⟩ h₃ = ⟨i, h₁⟩ := rfl

@[simp]
/-
**Fin.castPred_le_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_le_castPred_iff {i j : Fin (n + 1)} {hi : i != last n} {hj : j !=
 last n} : castPred i hi <= castPred j hj ↔ i <= j
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_le_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi ≤ castPred j hj ↔ i ≤ j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_le_castPred_iff`
that deduces `i ≠ last n` from `i ≤ j` and `j ≠ last n`. -/
@[gcongr]
/-
**Fin.castPred_le_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_le_castPred {i j : Fin (n + 1)} (h : i <= j) (hj : j != last n) :
 castPred i (by rw [← lt_last_iff_ne_last] at hj ⊢; exact Fin.lt_of_le_of_lt h h
j) <= castPred j hj
参数：n + 1；h : i <= j；hj : j != last n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of the right-to-left implication of `castPred_le_castPred_iff`
that deduces `i ≠ last n` from `i ≤ j` and `j ≠ last n`.
-/
theorem castPred_le_castPred {i j : Fin (n + 1)} (h : i ≤ j) (hj : j ≠ last n) :
    castPred i (by rw [← lt_last_iff_ne_last] at hj ⊢; exact Fin.lt_of_le_of_lt h hj) ≤
      castPred j hj :=
  h

@[simp]
/-
**Fin.castPred_lt_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_lt_castPred_iff {i j : Fin (n + 1)} {hi : i != last n} {hj : j !=
 last n} : castPred i hi < castPred j hj ↔ i < j
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_lt_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi < castPred j hj ↔ i < j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_lt_castPred_iff`
that deduces `i ≠ last n` from `i < j`. -/
@[gcongr]
/-
**Fin.castPred_lt_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_lt_castPred {i j : Fin (n + 1)} (h : i < j) (hj : j != last n) : 
castPred i (ne_last_of_lt h) < castPred j hj
参数：n + 1；h : i < j；hj : j != last n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of the right-to-left implication of `castPred_lt_castPred_iff`
that deduces `i ≠ last n` from `i < j`.
-/
theorem castPred_lt_castPred {i j : Fin (n + 1)} (h : i < j) (hj : j ≠ last n) :
    castPred i (ne_last_of_lt h) < castPred j hj := h
/-
**Fin.castPred_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) : castPre
d i hi < j ↔ i < castSucc j
参数：n + 1；hi : i != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi < j ↔ i < castSucc j := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]
/-
**Fin.lt_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) : j < cas
tPred i hi ↔ castSucc j < i
参数：n + 1；hi : i != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    j < castPred i hi ↔ castSucc j < i := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]
/-
**Fin.castPred_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) : castPre
d i hi <= j ↔ i <= castSucc j
参数：n + 1；hi : i != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.ca
stSucc ↔ a ≤ b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi ≤ j ↔ i ≤ castSucc j := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]
/-
**Fin.le_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) : j <= ca
stPred i hi ↔ castSucc j <= i
参数：n + 1；hi : i != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.ca
stSucc ↔ a ≤ b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    j ≤ castPred i hi ↔ castSucc j ≤ i := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]

@[simp]
/-
**Fin.castPred_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_inj {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n} : c
astPred i hi = castPred j hj ↔ i = j
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem castPred_inj {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi = castPred j hj ↔ i = j := by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

@[simp]
/-
**Fin.castPred_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_zero [NeZero n] : castPred (0 : Fin (n + 1)) (Fin.ext_iff.not.2 l
ast_pos'.ne) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.last_pos'`：last_pos' [NeZero n] : 0 < last n
-/
theorem castPred_zero [NeZero n] :
    castPred (0 : Fin (n + 1)) (Fin.ext_iff.not.2 last_pos'.ne) = 0 := rfl

@[simp]
/-
**Fin.castPred_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_eq_zero [NeZero n] {i : Fin (n + 1)} (h : i != last n) : Fin.cast
Pred i h = 0 ↔ i = 0
参数：n + 1；h : i != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.last_pos'`：last_pos' [NeZero n] : 0 < last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castPred_zero`：castPred_zero [NeZero n] : castPred (0 : Fin (n + 1))
 (Fin.ext_iff.not.2 last_pos'.ne) = 0
· 使用定理 `Fin.castPred_inj`：castPred_inj {i j : Fin (n + 1)} {hi : i != last n} {h
j : j != last n} : castPred i hi = castPred j hj ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_eq_zero [NeZero n] {i : Fin (n + 1)} (h : i ≠ last n) :
    Fin.castPred i h = 0 ↔ i = 0 := by
  rw [← castPred_zero, castPred_inj]
/-
**Fin.castPred_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_ne_zero [NeZero n] {i : Fin (n + 1)} (h₁ : i != last n) (h₂ : i !
= 0) : castPred i h₁ != 0
参数：n + 1；h₁ : i != last n；h₂ : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.castPred_eq_zero`：castPred_eq_zero [NeZero n] {i : Fin (n + 1)} (h :
 i != last n) : Fin.castPred i h = 0 ↔ i = 0
-/
theorem castPred_ne_zero [NeZero n] {i : Fin (n + 1)} (h₁ : i ≠ last n) (h₂ : i ≠ 0) :
    castPred i h₁ ≠ 0 :=
  (castPred_eq_zero h₁).not.mpr h₂

@[simp]
/-
**Fin.castPred_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_one [NeZero n] : castPred (1 : Fin (n + 2)) (Fin.ext_iff.not.2 on
e_lt_last.ne) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.one_lt_last`：one_lt_last [NeZero n] : 1 < last (n + 1)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem castPred_one [NeZero n] :
    castPred (1 : Fin (n + 2)) (Fin.ext_iff.not.2 one_lt_last.ne) = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl
/-
**Fin.succ_castPred_eq_castPred_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a != last n) (ha'
参数：n + 1；ha : a != last n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a ≠ last n)
    (ha' := a.succ_ne_last_iff.mpr ha) :
    (a.castPred ha).succ = (succ a).castPred ha' := rfl
/-
**Fin.succ_castPred_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_castPred_eq_add_one {a : Fin (n + 1)} (ha : a != last n) : (a.castPre
d ha).succ = a + 1
参数：n + 1；ha : a != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
· 使用定理 `Fin.coeSucc_eq_succ`：∀ {n : ℕ} {a : Fin n}, a.castSucc + 1 = a.succ
-/
theorem succ_castPred_eq_add_one {a : Fin (n + 1)} (ha : a ≠ last n) :
    (a.castPred ha).succ = a + 1 := by
  cases a using lastCases
  · exact (ha rfl).elim
  · rw [castPred_castSucc, coeSucc_eq_succ]
/-
**Fin.castpred_succ_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castpred_succ_le_iff {a b : Fin (n + 1)} (ha : succ a != last (n + 1)) : (
succ a).castPred ha <= b ↔ a < b
参数：n + 1；ha : succ a != last (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castPred_le_iff`：castPred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi :
 i != last n) : castPred i hi <= j ↔ i <= castSucc j
· 使用定理 `Fin.succ_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.castSucc ↔
 a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castpred_succ_le_iff {a b : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    (succ a).castPred ha ≤ b ↔ a < b := by
  rw [castPred_le_iff, succ_le_castSucc_iff]
/-
**Fin.lt_castPred_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_castPred_succ_iff {a b : Fin (n + 1)} (ha : succ a != last (n + 1)) : b
 < (succ a).castPred ha ↔ b <= a
参数：n + 1；ha : succ a != last (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_castPred_iff`：lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi :
 i != last n) : j < castPred i hi ↔ castSucc j < i
· 使用定理 `Fin.castSucc_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.succ ↔
 a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_castPred_succ_iff {a b : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    b < (succ a).castPred ha ↔ b ≤ a := by
  rw [lt_castPred_iff, castSucc_lt_succ_iff]
/-
**Fin.lt_castPred_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_castPred_succ {a : Fin (n + 1)} (ha : succ a != last (n + 1)) : a < (su
cc a).castPred ha
参数：n + 1；ha : succ a != last (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_castPred_succ_iff`：lt_castPred_succ_iff {a b : Fin (n + 1)} (ha :
 succ a != last (n + 1)) : b < (succ a).castPred ha ↔ b <= a
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lt_castPred_succ {a : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    a < (succ a).castPred ha := by rw [lt_castPred_succ_iff, le_def]
/-
**Fin.succ_castPred_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_castPred_le_iff {a b : Fin (n + 1)} (ha : a != last n) : succ (a.cast
Pred ha) <= b ↔ a < b
参数：n + 1；ha : a != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_ne_last_iff`：succ_ne_last_iff (a : Fin (n + 1)) : succ a != las
t (n + 1) ↔ a != last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succ_castPred_eq_castPred_succ`：succ_castPred_eq_castPred_succ {a : 
Fin (n + 1)} (ha : a != last n) (ha'
· 使用定理 `Fin.castpred_succ_le_iff`：castpred_succ_le_iff {a b : Fin (n + 1)} (ha :
 succ a != last (n + 1)) : (succ a).castPred ha <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem succ_castPred_le_iff {a b : Fin (n + 1)} (ha : a ≠ last n) :
    succ (a.castPred ha) ≤ b ↔ a < b := by
  rw [succ_castPred_eq_castPred_succ ha, castpred_succ_le_iff]
/-
**Fin.lt_succ_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_succ_castPred_iff {a b : Fin (n + 1)} (ha : a != last n) : b < succ (a.
castPred ha) ↔ b <= a
参数：n + 1；ha : a != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_ne_last_iff`：succ_ne_last_iff (a : Fin (n + 1)) : succ a != las
t (n + 1) ↔ a != last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succ_castPred_eq_castPred_succ`：succ_castPred_eq_castPred_succ {a : 
Fin (n + 1)} (ha : a != last n) (ha'
· 使用定理 `Fin.lt_castPred_succ_iff`：lt_castPred_succ_iff {a b : Fin (n + 1)} (ha :
 succ a != last (n + 1)) : b < (succ a).castPred ha ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_succ_castPred_iff {a b : Fin (n + 1)} (ha : a ≠ last n) :
    b < succ (a.castPred ha) ↔ b ≤ a := by
  rw [succ_castPred_eq_castPred_succ ha, lt_castPred_succ_iff]
/-
**Fin.lt_succ_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_succ_castPred {a : Fin (n + 1)} (ha : a != last n) : a < succ (a.castPr
ed ha)
参数：n + 1；ha : a != last n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_succ_castPred_iff`：lt_succ_castPred_iff {a b : Fin (n + 1)} (ha :
 a != last n) : b < succ (a.castPred ha) ↔ b <= a
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lt_succ_castPred {a : Fin (n + 1)} (ha : a ≠ last n) :
    a < succ (a.castPred ha) := by rw [lt_succ_castPred_iff, le_def]
/-
**Fin.castPred_le_pred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castPred_le_pred_iff {a b : Fin (n + 1)} (ha : a != last n) (hb : b != 0) 
: castPred a ha <= pred b hb ↔ a < b
参数：n + 1；ha : a != last n；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_pred_iff`：le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
 : j <= pred i hi ↔ succ j <= i
· 使用定理 `Fin.succ_castPred_le_iff`：succ_castPred_le_iff {a b : Fin (n + 1)} (ha :
 a != last n) : succ (a.castPred ha) <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castPred_le_pred_iff {a b : Fin (n + 1)} (ha : a ≠ last n) (hb : b ≠ 0) :
    castPred a ha ≤ pred b hb ↔ a < b := by
  rw [le_pred_iff, succ_castPred_le_iff]
/-
**Fin.pred_lt_castPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_lt_castPred_iff {a b : Fin (n + 1)} (ha : a != 0) (hb : b != last n) 
: pred a ha < castPred b hb ↔ a <= b
参数：n + 1；ha : a != 0；hb : b != last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_castPred_iff`：lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi :
 i != last n) : j < castPred i hi ↔ castSucc j < i
· 使用定理 `Fin.castSucc_pred_lt_iff`：castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha :
 a != 0) : castSucc (a.pred ha) < b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pred_lt_castPred_iff {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ last n) :
    pred a ha < castPred b hb ↔ a ≤ b := by
  rw [lt_castPred_iff, castSucc_pred_lt_iff ha]
/-
**Fin.pred_lt_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pred_lt_castPred {a : Fin (n + 1)} (h₁ : a != 0) (h₂ : a != last n) : pred
 a h₁ < castPred a h₂
参数：n + 1；h₁ : a != 0；h₂ : a != last n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.pred_lt_castPred_iff`：pred_lt_castPred_iff {a b : Fin (n + 1)} (ha :
 a != 0) (hb : b != last n) : pred a ha < castPred b hb ↔ a <= b
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem pred_lt_castPred {a : Fin (n + 1)} (h₁ : a ≠ 0) (h₂ : a ≠ last n) :
    pred a h₁ < castPred a h₂ := by
  rw [pred_lt_castPred_iff, le_def]
/-
**Fin.val_sub_castLT_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_sub_castLT_of_le {a b : Fin m} (ha : a.val < n) (h : b <= a) : (a.cast
LT ha - b.castLT (lt_of_le_of_lt h ha)).val = (a - b).val
参数：ha : a.val < n；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem val_sub_castLT_of_le {a b : Fin m} (ha : a.val < n) (h : b ≤ a) :
    (a.castLT ha - b.castLT (lt_of_le_of_lt h ha)).val = (a - b).val := by
  have : b.castLT (lt_of_le_of_lt h ha) ≤ a.castLT ha := by simpa [← val_fin_le] using h
  simp [sub_val_of_le, h, this]
/-
**Fin.sub_castLT_eq_castLT_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sub_castLT_eq_castLT_sub_of_le {a b : Fin m} (ha : a.val < n) (h : b <= a)
 : a.castLT ha - b.castLT (lt_of_le_of_lt h ha) = (a - b).castLT (val_sub_lt_of_
lt_of_le ha h)
参数：ha : a.val < n；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Fin.val_sub_lt_of_lt_of_le`：val_sub_lt_of_lt_of_le {a b : Fin n} (ha : a
.val < m) (hab : b <= a) : (a - b).val < m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Fin.val_sub_castLT_of_le`：val_sub_castLT_of_le {a b : Fin m} (ha : a.val
 < n) (h : b <= a) : (a.castLT ha - b.castLT (lt_of_le_of_lt h ha)).val = (a - b
).val
-/
theorem sub_castLT_eq_castLT_sub_of_le {a b : Fin m} (ha : a.val < n) (h : b ≤ a) :
    a.castLT ha - b.castLT (lt_of_le_of_lt h ha) =
      (a - b).castLT (val_sub_lt_of_lt_of_le ha h) := by
  rw [Fin.ext_iff]
  exact val_sub_castLT_of_le ha h
/-
**Fin.val_sub_castLT_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_sub_castLT_of_lt {a b : Fin m} (hb : b < n) (h : a < b) : (a.castLT (l
t_trans h hb) - b.castLT hb).val = (a - b).val + n - m
参数：hb : b < n；h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem val_sub_castLT_of_lt {a b : Fin m} (hb : b < n) (h : a < b) :
    (a.castLT (lt_trans h hb) - b.castLT hb).val = (a - b).val + n - m := by
  simp only [val_sub, val_castLT]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  have h' : a.val < b.val := h
  omega
/-
**Fin.val_sub_castPred_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_sub_castPred_of_le {a b : Fin (n + 1)} (ha : a != last n) (h : b <= a)
 : (a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h)).val = (a - b).va
l
参数：n + 1；ha : a != last n；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_sub_castLT_of_le`：val_sub_castLT_of_le {a b : Fin m} (ha : a.val
 < n) (h : b <= a) : (a.castLT ha - b.castLT (lt_of_le_of_lt h ha)).val = (a - b
).val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
-/
theorem val_sub_castPred_of_le {a b : Fin (n + 1)} (ha : a ≠ last n)
    (h : b ≤ a) :
    (a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h)).val = (a - b).val :=
  val_sub_castLT_of_le (lt_last_iff_ne_last.mpr ha) h
/-
**Fin.sub_castPred_eq_castPred_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sub_castPred_eq_castPred_sub_of_le {a b : Fin (n + 1)} (ha : a != last n) 
(h : b <= a) : a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h) = (a -
 b).castPred (sub_ne_last_of_ne_last_of_le ha h)
参数：n + 1；ha : a != last n；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.sub_castLT_eq_castLT_sub_of_le`：sub_castLT_eq_castLT_sub_of_le {a b 
: Fin m} (ha : a.val < n) (h : b <= a) : a.castLT ha - b.castLT (lt_of_le_of_lt 
h ha) = (a - b).castLT (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
-/
theorem sub_castPred_eq_castPred_sub_of_le {a b : Fin (n + 1)} (ha : a ≠ last n)
    (h : b ≤ a) :
    a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h) =
      (a - b).castPred (sub_ne_last_of_ne_last_of_le ha h) :=
  sub_castLT_eq_castLT_sub_of_le (lt_last_iff_ne_last.mpr ha) h
/-
**Fin.val_sub_castPred_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_sub_castPred_of_ge {a b : Fin (n + 1)} (hb : b != last n) (h : a <= b)
 : (a.castPred (ne_last_of_ne_last_of_le hb h) - b.castPred hb).val = (a - b).va
l - 1
参数：n + 1；hb : b != last n；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.ne_last_of_ne_last_of_le`：ne_last_of_ne_last_of_le {a b : Fin (n + 1
)} (hb : b != last n) (hab : a <= b) : a != last n
· 使用定理 `Fin.eq_or_lt_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Fin.is_le`：∀ {n : ℕ} (i : Fin (n + 1)), ↑i ≤ n
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sub_self`：∀ {n : ℕ} [inst : NeZero n] {x : Fin n}, x - x = 0
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem val_sub_castPred_of_ge {a b : Fin (n + 1)} (hb : b ≠ last n)
    (h : a ≤ b) :
    (a.castPred (ne_last_of_ne_last_of_le hb h) - b.castPred hb).val = (a - b).val - 1 := by
  obtain (rfl | h') := Fin.eq_or_lt_of_le h
  · simp [val_sub, Nat.sub_add_cancel a.is_le]
  grind [castPred, val_sub_castLT_of_lt]

end CastPred

section SuccAbove
variable {p : Fin (n + 1)} {i j : Fin n}

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
/-
**Fin.succAbove** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1)
参数：p : Fin (n + 1)；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`.
-/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
/-
**Fin.succAbove_of_castSucc_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p
) : p.succAbove i = castSucc i
参数：p : Fin (n + 1)；i : Fin n；h : castSucc i < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`.
-/
lemma succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h
/-
**Fin.succAbove_of_succ_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_of_succ_le (p : Fin (n + 1)) (i : Fin n) (h : succ i <= p) : p.s
uccAbove i = castSucc i
参数：p : Fin (n + 1)；i : Fin n；h : succ i <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
-/
lemma succAbove_of_succ_le (p : Fin (n + 1)) (i : Fin n) (h : succ i ≤ p) :
    p.succAbove i = castSucc i :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
/-
**Fin.succAbove_of_le_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p <= castSucc 
i) : p.succAbove i = i.succ
参数：p : Fin (n + 1)；i : Fin n；h : p <= castSucc i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a

--- 原说明 ---
Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`.
-/
lemma succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := if_neg (Fin.not_lt.2 h)
/-
**Fin.succAbove_of_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fin n) (h : p < succ i) : p.su
ccAbove i = succ i
参数：p : Fin (n + 1)；i : Fin n；h : p < succ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
-/
lemma succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fin n) (h : p < succ i) :
    p.succAbove i = succ i := succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)
/-
**Fin.succAbove_succ_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_succ_of_lt (p i : Fin n) (h : p < i) : succAbove p.succ i = i.su
cc
参数：p i : Fin n；h : p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
-/
lemma succAbove_succ_of_lt (p i : Fin n) (h : p < i) : succAbove p.succ i = i.succ :=
  succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)
/-
**Fin.succAbove_succ_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_succ_of_le (p i : Fin n) (h : i <= p) : succAbove p.succ i = i.c
astSucc
参数：p i : Fin n；h : i <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_succ_le`：succAbove_of_succ_le (p : Fin (n + 1)) (i : Fi
n n) (h : succ i <= p) : p.succAbove i = castSucc i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
-/
lemma succAbove_succ_of_le (p i : Fin n) (h : i ≤ p) : succAbove p.succ i = i.castSucc :=
  succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)
/-
**Fin.succAbove_succ_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (j : Fin n), j.succ.succAbove j = j.castSucc
参数：j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_succ_of_le`：succAbove_succ_of_le (p i : Fin n) (h : i <= p
) : succAbove p.succ i = i.castSucc
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
@[simp] lemma succAbove_succ_self (j : Fin n) : j.succ.succAbove j = j.castSucc :=
  succAbove_succ_of_le _ _ Fin.le_rfl
/-
**Fin.succAbove_castSucc_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_castSucc_of_lt (p i : Fin n) (h : i < p) : succAbove p.castSucc 
i = i.castSucc
参数：p i : Fin n；h : i < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
-/
lemma succAbove_castSucc_of_lt (p i : Fin n) (h : i < p) : succAbove p.castSucc i = i.castSucc :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)
/-
**Fin.succAbove_castSucc_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_castSucc_of_le (p i : Fin n) (h : p <= i) : succAbove p.castSucc
 i = i.succ
参数：p i : Fin n；h : p <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.ca
stSucc ↔ a ≤ b
-/
lemma succAbove_castSucc_of_le (p i : Fin n) (h : p ≤ i) : succAbove p.castSucc i = i.succ :=
  succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.2 h)
/-
**Fin.succAbove_castSucc_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (j : Fin n), j.castSucc.succAbove j = j.succ
参数：j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_castSucc_of_le`：succAbove_castSucc_of_le (p i : Fin n) (h 
: p <= i) : succAbove p.castSucc i = i.succ
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
@[simp] lemma succAbove_castSucc_self (j : Fin n) : succAbove j.castSucc j = j.succ :=
  succAbove_castSucc_of_le _ _ Fin.le_rfl
/-
**Fin.succAbove_pred_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i) : succAbove p (i.pred
 (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) = i
参数：p i : Fin (n + 1)；h : p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
-/
lemma succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) = i := by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h), succ_pred]
/-
**Fin.succAbove_pred_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_pred_of_le (p i : Fin (n + 1)) (h : i <= p) (hi : i != 0) : succ
Above p (i.pred hi) = (i.pred hi).castSucc
参数：p i : Fin (n + 1)；h : i <= p；hi : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.succAbove_of_succ_le`：succAbove_of_succ_le (p : Fin (n + 1)) (i : Fi
n n) (h : succ i <= p) : p.succAbove i = castSucc i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
-/
lemma succAbove_pred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hi : i ≠ 0) :
    succAbove p (i.pred hi) = (i.pred hi).castSucc := succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)
/-
**Fin.succAbove_pred_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (p : Fin (n + 1)) (h : p ≠ 0), p.succAbove (p.pred h) = (p.pred 
h).castSucc
参数：p : Fin (n + 1)；h : p ≠ 0；p.pred h；p.pred h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.succAbove_pred_of_le`：succAbove_pred_of_le (p i : Fin (n + 1)) (h : 
i <= p) (hi : i != 0) : succAbove p (i.pred hi) = (i.pred hi).castSucc
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
@[simp] lemma succAbove_pred_self (p : Fin (n + 1)) (h : p ≠ 0) :
    succAbove p (p.pred h) = (p.pred h).castSucc := succAbove_pred_of_le _ _ Fin.le_rfl h
/-
**Fin.succAbove_castPred_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p) : succAbove p (i.
castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p.le_last)) = i
参数：p i : Fin (n + 1)；h : i < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
-/
lemma succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p.le_last)) = i := by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h), castSucc_castPred]
/-
**Fin.succAbove_castPred_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p <= i) (hi : i != last 
n) : succAbove p (i.castPred hi) = (i.castPred hi).succ
参数：p i : Fin (n + 1)；h : p <= i；hi : i != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
-/
lemma succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hi : i ≠ last n) :
    succAbove p (i.castPred hi) = (i.castPred hi).succ :=
  succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)
/-
**Fin.succAbove_castPred_self** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_castPred_self (p : Fin (n + 1)) (h : p != last n) : succAbove p 
(p.castPred h) = (p.castPred h).succ
参数：p : Fin (n + 1)；h : p != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_castPred_of_le`：succAbove_castPred_of_le (p i : Fin (n + 1
)) (h : p <= i) (hi : i != last n) : succAbove p (i.castPred hi) = (i.castPred h
i).succ
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
lemma succAbove_castPred_self (p : Fin (n + 1)) (h : p ≠ last n) :
    succAbove p (p.castPred h) = (p.castPred h).succ := succAbove_castPred_of_le _ _ Fin.le_rfl h

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
@[simp]
/-
**Fin.succAbove_ne** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i != p
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_lt_or_lt_succ`：castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i 
: Fin n) : castSucc i < p ∨ p < i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a

--- 原说明 ---
Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself
-/
lemma succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

@[simp]
/-
**Fin.ne_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p != p.succAbove i
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Fin.succAbove_ne`：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbo
ve i != p
-/
lemma ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p ≠ p.succAbove i := (succAbove_ne _ _).symm

/-- Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective. -/
/-
**Fin.succAbove_right_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_right_injective : Injective p.succAbove
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.castSucc_injective`：castSucc_injective (n : Nat) : Injective (@Fin.c
astSucc n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)

--- 原说明 ---
Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective.
-/
lemma succAbove_right_injective : Injective p.succAbove := by
  rintro i j hij
  unfold succAbove at hij
  split_ifs at hij with hi hj hj
  · exact castSucc_injective _ hij
  · rw [hij] at hi
    cases hj <| Nat.lt_trans j.castSucc_lt_succ hi
  · rw [← hij] at hj
    cases hi <| Nat.lt_trans i.castSucc_lt_succ hj
  · exact succ_injective _ hij

/-- Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective. -/
/-
**Fin.succAbove_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_right_inj : p.succAbove i = p.succAbove j ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Fin.succAbove_right_injective`：succAbove_right_injective : Injective p.s
uccAbove

--- 原说明 ---
Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective.
-/
lemma succAbove_right_inj : p.succAbove i = p.succAbove j ↔ i = j :=
  succAbove_right_injective.eq_iff

@[simp]
/-
**Fin.succAbove_ne_zero_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a != 0) : a.succ
Above 0 = 0
参数：n + 1；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
· 使用定理 `Fin.castSucc_zero'`：castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0
-/
lemma succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact Fin.pos_iff_ne_zero.2 ha
/-
**Fin.succAbove_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 
0) : a.succAbove b = 0 ↔ b = 0
参数：n + 1；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用引理 `Fin.succAbove_right_inj`：succAbove_right_inj : p.succAbove i = p.succAbo
ve j ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  rw [← succAbove_ne_zero_zero ha, succAbove_right_inj]
/-
**Fin.succAbove_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 0) (
hb : b != 0) : a.succAbove b != 0
参数：n + 1；ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.succAbove_eq_zero_iff`：succAbove_eq_zero_iff [NeZero n] {a : Fin (n 
+ 1)} {b : Fin n} (ha : a != 0) : a.succAbove b = 0 ↔ b = 0
-/
lemma succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 := mt (succAbove_eq_zero_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
/-
**Fin.succAbove_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`.
-/
@[simp] lemma succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ := rfl
/-
**Fin.succAbove_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_zero_apply (i : Fin n) : succAbove 0 i = succ i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ

--- 原说明 ---
Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`.
-/
lemma succAbove_zero_apply (i : Fin n) : succAbove 0 i = succ i := by rw [succAbove_zero]
/-
**Fin.succAbove_ne_last_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {a : Fin (n + 2)}, a ≠ Fin.last (n + 1) → a.succAbove (Fin.last 
n) = Fin.last (n + 1)
参数：n + 2；n + 1；Fin.last n；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_last`：∀ (n : ℕ), (Fin.last n).succ = Fin.last n.succ
-/
@[simp] lemma succAbove_ne_last_last {a : Fin (n + 2)} (h : a ≠ last (n + 1)) :
    a.succAbove (last n) = last (n + 1) := by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_last_iff_ne_last.2 h), succ_last]
/-
**Fin.succAbove_eq_last_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last 
_) : a.succAbove b = last _ ↔ b = last _
参数：n + 2；n + 1；ha : a != last _。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_ne_last_last`：∀ {n : ℕ} {a : Fin (n + 2)}, a ≠ Fin.last (n
 + 1) → a.succAbove (Fin.last n) = Fin.last (n + 1)
· 使用引理 `Fin.succAbove_right_inj`：succAbove_right_inj : p.succAbove i = p.succAbo
ve j ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma succAbove_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) :
    a.succAbove b = last _ ↔ b = last _ := by
  rw [← succAbove_ne_last_last ha, succAbove_right_inj]
/-
**Fin.succAbove_ne_last** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last _) (
hb : b != last _) : a.succAbove b != last _
参数：n + 2；n + 1；ha : a != last _；hb : b != last _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.succAbove_eq_last_iff`：succAbove_eq_last_iff {a : Fin (n + 2)} {b : 
Fin (n + 1)} (ha : a != last _) : a.succAbove b = last _ ↔ b = last _
-/
lemma succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) (hb : b ≠ last _) :
    a.succAbove b ≠ last _ := mt (succAbove_eq_last_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
/-
**Fin.succAbove_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
参数：Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `cast
Succ`.
-/
@[simp] lemma succAbove_last : succAbove (last n) = castSucc := by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]
/-
**Fin.succAbove_last_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
-/
lemma succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i := by rw [succAbove_last]

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
/-
**Fin.succAbove_lt_iff_castSucc_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) : p.succAbove i
 < p ↔ castSucc i < p
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_lt_or_lt_succ`：castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i 
: Fin n) : castSucc i < p ∨ p < i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true_right`：∀ {a b : Prop}, a → ((b ↔ a) ↔ b)
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `iff_false_right`：∀ {a b : Prop}, ¬a → ((b ↔ a) ↔ ¬b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.not_le`：∀ {n : ℕ} {a b : Fin n}, ¬a ≤ b ↔ b < a
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b

--- 原说明 ---
Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`.
-/
lemma succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right (Fin.not_le.2 H), succAbove_of_lt_succ _ _ H]
    exact Fin.not_lt.2 <| Fin.le_of_lt H
/-
**Fin.succAbove_lt_iff_succ_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) : p.succAbove i < p
 ↔ succ i <= p
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_lt_iff_castSucc_lt`：succAbove_lt_iff_castSucc_lt (p : Fin 
(n + 1)) (i : Fin n) : p.succAbove i < p ↔ castSucc i < p
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ succ i ≤ p := by
  rw [succAbove_lt_iff_castSucc_lt, castSucc_lt_iff_succ_le]

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
/-
**Fin.lt_succAbove_iff_le_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) : p < p.succAbo
ve i ↔ p <= castSucc i
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_lt_or_lt_succ`：castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i 
: Fin n) : castSucc i < p ∨ p < i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false_right`：∀ {a b : Prop}, ¬a → ((b ↔ a) ↔ ¬b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.not_le`：∀ {n : ℕ} {a b : Fin n}, ¬a ≤ b ↔ b < a
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用定理 `iff_true_left`：∀ {a b : Prop}, a → ((a ↔ b) ↔ b)
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ

--- 原说明 ---
Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`.
-/
lemma lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p ≤ castSucc i := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rw [iff_false_right (Fin.not_le.2 H), succAbove_of_castSucc_lt _ _ H]
    exact Fin.not_lt.2 <| Fin.le_of_lt H
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]
/-
**Fin.lt_succAbove_iff_lt_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_succAbove_iff_lt_castSucc (p : Fin (n + 1)) (i : Fin n) : p < p.succAbo
ve i ↔ p < succ i
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.lt_succAbove_iff_le_castSucc`：lt_succAbove_iff_le_castSucc (p : Fin 
(n + 1)) (i : Fin n) : p < p.succAbove i ↔ p <= castSucc i
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_succAbove_iff_lt_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p < succ i := by rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
/-
**Fin.succAbove_pos** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p
.succAbove i
参数：p : Fin (n + 1)；i : Fin n；h : 0 < i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.castSucc_pos'`：∀ {n : ℕ} [inst : NeZero n] {i : Fin n}, 0 < i → 0 < 
i.castSucc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a

--- 原说明 ---
Embedding a positive `Fin n` results in a positive `Fin (n + 1)`
-/
lemma succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 H)]
/-
**Fin.castPred_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castPred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y) (h'
参数：x : Fin n；y : Fin (n + 1)；h : castSucc x < y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castPred_eq_iff_eq_castSucc`：castPred_eq_iff_eq_castSucc (i : Fin (n
 + 1)) (hi : i != last _) (j : Fin n) : castPred i hi = j ↔ i = castSucc j
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
-/
lemma castPred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y)
    (h' := Fin.ne_last_of_lt <| (succAbove_lt_iff_castSucc_lt ..).2 h) :
    (y.succAbove x).castPred h' = x := by
  rw [castPred_eq_iff_eq_castSucc, succAbove_of_castSucc_lt _ _ h]
/-
**Fin.pred_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y <= castSucc x) (h'
参数：x : Fin n；y : Fin (n + 1)；h : y <= castSucc x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Fin.pred.congr_simp`：∀ {n : ℕ} (i i_1 : Fin (n + 1)) (e_i : i = i_1) (h 
: i ≠ 0), i.pred h = i_1.pred ⋯
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y ≤ castSucc x)
    (h' := Fin.ne_zero_of_lt <| (lt_succAbove_iff_le_castSucc ..).2 h) :
    (y.succAbove x).pred h' = x := by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]
/-
**Fin.exists_succAbove_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：exists_succAbove_eq {x y : Fin (n + 1)} (h : x != y) : exists z, y.succAbo
ve z = x
参数：n + 1；h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_lt_of_ne`：∀ {n : ℕ} {a b : Fin n}, a ≠ b → a < b ∨ b < a
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用引理 `Fin.succAbove_pred_of_lt`：succAbove_pred_of_lt (p i : Fin (n + 1)) (h : 
p < i) : succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) =
 i
-/
lemma exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  obtain hxy | hyx := Fin.lt_or_lt_of_ne h
  exacts [⟨_, succAbove_castPred_of_lt _ _ hxy⟩, ⟨_, succAbove_pred_of_lt _ _ hyx⟩]
/-
**Fin.exists_succAbove_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {x y : Fin (n + 1)}, (∃ z, x.succAbove z = y) ↔ y ≠ x
参数：n + 1；∃ z, x.succAbove z = y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_ne`：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbo
ve i != p
· 使用引理 `Fin.exists_succAbove_eq`：exists_succAbove_eq {x y : Fin (n + 1)} (h : x 
!= y) : exists z, y.succAbove z = x
-/
@[simp] lemma exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x :=
  ⟨by rintro ⟨y, rfl⟩; exact succAbove_ne _ _, exists_succAbove_eq⟩

/-- The range of `p.succAbove` is everything except `p`. -/
/-
**Fin.range_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (p : Fin (n + 1)), Set.range p.succAbove = {p}ᶜ
参数：p : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Fin.exists_succAbove_eq_iff`：∀ {n : ℕ} {x y : Fin (n + 1)}, (∃ z, x.succ
Above z = y) ↔ y ≠ x

--- 原说明 ---
The range of `p.succAbove` is everything except `p`.
-/
@[simp] lemma range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff
/-
**Fin.range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ), Set.range Fin.succ = {0}ᶜ
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
· 使用定理 `Fin.range_succAbove`：∀ {n : ℕ} (p : Fin (n + 1)), Set.range p.succAbove 
= {p}ᶜ
-/
@[simp] lemma range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero, range_succAbove]

/-- `succAbove` is injective at the pivot -/
/-
**Fin.succAbove_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_left_injective : Injective (@succAbove n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.range_succAbove`：∀ {n : ℕ} (p : Fin (n + 1)), Set.range p.succAbove 
= {p}ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
`succAbove` is injective at the pivot
-/
lemma succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n → Fin (n + 1) => (Set.range f)ᶜ) h

/-- `succAbove` is injective at the pivot -/
/-
**Fin.succAbove_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {x y : Fin (n + 1)}, x.succAbove = y.succAbove ↔ x = y
参数：n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Fin.succAbove_left_injective`：succAbove_left_injective : Injective (@suc
cAbove n)

--- 原说明 ---
`succAbove` is injective at the pivot
-/
@[simp] lemma succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff
/-
**Fin.zero_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin n), Fin.succAbove 0 i = i.succ
参数：i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := rfl
/-
**Fin.succ_succAbove_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succ_succAbove_zero {n : Nat} [NeZero n] (i : Fin n) : succAbove i.succ 0 
= 0
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 := by simp

/-- `succ` commutes with `succAbove`. -/
/-
**Fin.succ_succAbove_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ.succAbove j.succ = (i.succ
Above j).succ
参数：i : Fin (n + 1)；j : Fin n；i.succAbove j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_ge`：∀ {n : ℕ} (a b : Fin n), a < b ∨ b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_lt_succ`：succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fi
n n) (h : p < succ i) : p.succAbove i = succ i
· 使用引理 `Fin.succAbove_succ_of_lt`：succAbove_succ_of_lt (p i : Fin n) (h : p < i)
 : succAbove p.succ i = i.succ
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用引理 `Fin.succAbove_succ_of_le`：succAbove_succ_of_le (p i : Fin n) (h : i <= p
) : succAbove p.succ i = i.castSucc
· 使用定理 `Fin.succ_castSucc`：∀ {n : ℕ} (i : Fin n), i.castSucc.succ = i.succ.castS
ucc

--- 原说明 ---
`succ` commutes with `succAbove`.
-/
@[simp] lemma succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ := by
  obtain h | h := i.lt_or_ge (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
/-
**Fin.castSucc_succAbove_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castSucc_succAbove_castSucc {n : Nat} {i : Fin (n + 1)} {j : Fin n} : i.ca
stSucc.succAbove j.castSucc = (i.succAbove j).castSucc
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.le_or_gt`：∀ {n : ℕ} (a b : Fin n), a ≤ b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用引理 `Fin.succAbove_castSucc_of_le`：succAbove_castSucc_of_le (p i : Fin n) (h 
: p <= i) : succAbove p.castSucc i = i.succ
· 使用定理 `Fin.succ_castSucc`：∀ {n : ℕ} (i : Fin n), i.castSucc.succ = i.succ.castS
ucc
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用引理 `Fin.succAbove_castSucc_of_lt`：succAbove_castSucc_of_lt (p i : Fin n) (h 
: i < p) : succAbove p.castSucc i = i.castSucc

--- 原说明 ---
`castSucc` commutes with `succAbove`.
-/
lemma castSucc_succAbove_castSucc {n : ℕ} {i : Fin (n + 1)} {j : Fin n} :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases i.le_or_gt (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

/-- `pred` commutes with `succAbove`. -/
/-
**Fin.pred_succAbove_pred** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != 0) (hb 
: b != 0) (hk
参数：n + 2；n + 1；ha : a != 0；hb : b != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_inj`：∀ {n : ℕ} {a b : Fin n}, a.succ = b.succ ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`pred` commutes with `succAbove`.
-/
lemma pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]

/-- `castPred` commutes with `succAbove`. -/
/-
**Fin.castPred_succAbove_castPred** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castPred_succAbove_castPred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a !=
 last (n + 1)) (hb : b != last n) (hk
参数：n + 2；n + 1；ha : a != last (n + 1)；hb : b != last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_inj`：∀ {n : ℕ} {a b : Fin n}, a.castSucc = b.castSucc ↔ a =
 b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`castPred` commutes with `succAbove`.
-/
lemma castPred_succAbove_castPred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last (n + 1))
    (hb : b ≠ last n) (hk := succAbove_ne_last ha hb) :
    (a.castPred ha).succAbove (b.castPred hb) = (a.succAbove b).castPred hk := by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]
/-
**Fin.one_succAbove_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：one_succAbove_zero {n : Nat} : (1 : Fin (n + 2)).succAbove 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma one_succAbove_zero {n : ℕ} : (1 : Fin (n + 2)).succAbove 0 = 0 := rfl

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
/-
**Fin.succ_succAbove_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] (i : Fin (n + 1)), i.succ.succAbove 1 = (i.suc
cAbove 0).succ
参数：i : Fin (n + 1)；i.succAbove 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_zero_eq_one'`：succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin 
n) = 1
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ

--- 原说明 ---
By moving `succ` to the outside of this expression, we create opportunities for 
further
simplification using `succAbove_zero` or `succ_succAbove_zero`.
-/
@[simp] lemma succ_succAbove_one {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one']
  exact succ_succAbove_succ i 0
/-
**Fin.one_succAbove_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (j : Fin n), Fin.succAbove 1 j.succ = j.succ.succ
参数：j : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.zero_succAbove`：∀ {n : ℕ} (i : Fin n), Fin.succAbove 0 i = i.succ
· 使用定理 `Fin.succ_zero_eq_one`：∀ {n : ℕ}, Fin.succ 0 = 1
-/
@[simp] lemma one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j; rwa [succ_zero_eq_one, zero_succAbove] at this
/-
**Fin.one_succAbove_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, Fin.succAbove 1 1 = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  simpa only [succ_zero_eq_one, val_zero, zero_succAbove, succ_one_eq_two]
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 1))

end SuccAbove

section PredAbove

/-- `predAbove p i` surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
/-
**Fin.predAbove** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n
参数：p : Fin n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`predAbove p i` surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p <
 i`.
-/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))
/-
**Fin.predAbove_of_le_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i <= castSucc 
p) : p.predAbove i = i.castPred (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| castSuc
c_lt_last _)
参数：p : Fin n；i : Fin (n + 1)；h : i <= castSucc p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a
-/
lemma predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castPred (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| castSucc_lt_last _) :=
  dif_neg <| Fin.not_lt.2 h
/-
**Fin.predAbove_of_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p) : p.pr
edAbove i = i.castPred (Fin.ne_last_of_lt h)
参数：p : Fin n；i : Fin (n + 1)；h : i < succ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
-/
lemma predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p) :
    p.predAbove i = i.castPred (Fin.ne_last_of_lt h) :=
  predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)
/-
**Fin.predAbove_of_castSucc_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i
) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
参数：p : Fin n；i : Fin (n + 1)；h : castSucc p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred (Fin.ne_zero_of_lt h) := dif_pos h
/-
**Fin.predAbove_of_succ_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p <= i) : p.p
redAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (succ_pos _) h)
参数：p : Fin n；i : Fin (n + 1)；h : succ p <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
-/
lemma predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p ≤ i) :
    p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (succ_pos _) h) :=
  predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)
/-
**Fin.predAbove_succ_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_succ_of_lt (p i : Fin n) (h : i < p) : p.predAbove (succ i) = (i
.succ).castPred (succ_ne_last_of_lt h)
参数：p i : Fin n；h : i < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.succ_ne_last_of_lt`：succ_ne_last_of_lt {p i : Fin n} (h : i < p) : s
ucc i != last n
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_lt_succ`：predAbove_of_lt_succ (p : Fin n) (i : Fin (n +
 1)) (h : i < succ p) : p.predAbove i = i.castPred (Fin.ne_last_of_lt h)
-/
lemma predAbove_succ_of_lt (p i : Fin n) (h : i < p) :
    p.predAbove (succ i) = (i.succ).castPred (succ_ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]
/-
**Fin.predAbove_succ_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_succ_of_le (p i : Fin n) (h : p <= i) : p.predAbove (succ i) = i
参数：p i : Fin n；h : p <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_lt_of_le`：∀ {n : ℕ} {a b c : Fin n}, a < b → b ≤ c → a < c
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_succ_le`：predAbove_of_succ_le (p : Fin n) (i : Fin (n +
 1)) (h : succ p <= i) : p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of
_le (succ_pos …
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
-/
lemma predAbove_succ_of_le (p i : Fin n) (h : p ≤ i) : p.predAbove (succ i) = i := by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h), pred_succ]
/-
**Fin.predAbove_succ_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (p : Fin n), p.predAbove p.succ = p
参数：p : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_succ_of_le`：predAbove_succ_of_le (p i : Fin n) (h : p <= i
) : p.predAbove (succ i) = i
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
@[simp] lemma predAbove_succ_self (p : Fin n) : p.predAbove (succ p) = p :=
  predAbove_succ_of_le _ _ Fin.le_rfl
/-
**Fin.predAbove_castSucc_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) : p.predAbove (castSucc
 i) = i.castSucc.pred (castSucc_ne_zero_of_lt h)
参数：p i : Fin n；h : p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_ne_zero_of_lt`：castSucc_ne_zero_of_lt {p i : Fin n} (h : p 
< i) : castSucc i != 0
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
-/
lemma predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) :
    p.predAbove (castSucc i) = i.castSucc.pred (castSucc_ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]
/-
**Fin.predAbove_castSucc_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_castSucc_of_le (p i : Fin n) (h : i <= p) : p.predAbove (castSuc
c i) = i
参数：p i : Fin n；h : i <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.ca
stSucc ↔ a ≤ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
-/
lemma predAbove_castSucc_of_le (p i : Fin n) (h : i ≤ p) : p.predAbove (castSucc i) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h), castPred_castSucc]
/-
**Fin.predAbove_castSucc_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (p : Fin n), p.predAbove p.castSucc = p
参数：p : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_castSucc_of_le`：predAbove_castSucc_of_le (p i : Fin n) (h 
: i <= p) : p.predAbove (castSucc i) = i
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
@[simp] lemma predAbove_castSucc_self (p : Fin n) : p.predAbove (castSucc p) = p :=
  predAbove_castSucc_of_le _ _ Fin.le_rfl
/-
**Fin.predAbove_pred_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) : (pred p (Fin.ne_zer
o_of_lt h)).predAbove i = castPred i (Fin.ne_last_of_lt h)
参数：p i : Fin (n + 1)；h : i < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_lt_succ`：predAbove_of_lt_succ (p : Fin n) (i : Fin (n +
 1)) (h : i < succ p) : p.predAbove i = i.castPred (Fin.ne_last_of_lt h)
-/
lemma predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    (pred p (Fin.ne_zero_of_lt h)).predAbove i = castPred i (Fin.ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]
/-
**Fin.predAbove_pred_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_pred_of_le (p i : Fin (n + 1)) (h : p <= i) (hp : p != 0) : (pre
d p hp).predAbove i = pred i (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (Fin.pos_iff_ne
_zero.2 hp) h)
参数：p i : Fin (n + 1)；h : p <= i；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `Fin.lt_of_lt_of_le`：∀ {n : ℕ} {a b c : Fin n}, a < b → b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_succ_le`：predAbove_of_succ_le (p : Fin n) (i : Fin (n +
 1)) (h : succ p <= i) : p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of
_le (succ_pos …
-/
lemma predAbove_pred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hp : p ≠ 0) :
    (pred p hp).predAbove i =
      pred i (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (Fin.pos_iff_ne_zero.2 hp) h) := by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]
/-
**Fin.predAbove_pred_self** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_pred_self (p : Fin (n + 1)) (hp : p != 0) : (pred p hp).predAbov
e p = pred p hp
参数：p : Fin (n + 1)；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.predAbove_pred_of_le`：predAbove_pred_of_le (p i : Fin (n + 1)) (h : 
p <= i) (hp : p != 0) : (pred p hp).predAbove i = pred i (Fin.ne_of_gt <| Fin.lt
_of_lt_of_le (…
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
lemma predAbove_pred_self (p : Fin (n + 1)) (hp : p ≠ 0) : (pred p hp).predAbove p = pred p hp :=
  predAbove_pred_of_le _ _ Fin.le_rfl hp
/-
**Fin.predAbove_castPred_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i) : (castPred p (Fi
n.ne_last_of_lt h)).predAbove i = pred i (Fin.ne_zero_of_lt h)
参数：p i : Fin (n + 1)；h : p < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
-/
lemma predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    (castPred p (Fin.ne_last_of_lt h)).predAbove i = pred i (Fin.ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]
/-
**Fin.predAbove_castPred_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i <= p) (hp : p != last 
n) : (castPred p hp).predAbove i = castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_l
t h <| Fin.lt_last_iff_ne_last.2 hp)
参数：p i : Fin (n + 1)；h : i <= p；hp : p != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
-/
lemma predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hp : p ≠ last n) :
    (castPred p hp).predAbove i =
      castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| Fin.lt_last_iff_ne_last.2 hp) := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]
/-
**Fin.predAbove_castPred_self** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_castPred_self (p : Fin (n + 1)) (hp : p != last n) : (castPred p
 hp).predAbove p = castPred p hp
参数：p : Fin (n + 1)；hp : p != last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_castPred_of_le`：predAbove_castPred_of_le (p i : Fin (n + 1
)) (h : i <= p) (hp : p != last n) : (castPred p hp).predAbove i = castPred i (F
in.ne_of_lt <| Fin…
· 使用定理 `Fin.le_rfl`：∀ {n : ℕ} {a : Fin n}, a ≤ a
-/
lemma predAbove_castPred_self (p : Fin (n + 1)) (hp : p ≠ last n) :
    (castPred p hp).predAbove p = castPred p hp := predAbove_castPred_of_le _ _ Fin.le_rfl hp
/-
**Fin.predAbove_right_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] {i : Fin n}, i.predAbove 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.last_pos'`：last_pos' [NeZero n] : 0 < last n
· 使用定理 `Fin.castPred_zero`：castPred_zero [NeZero n] : castPred (0 : Fin (n + 1))
 (Fin.ext_iff.not.2 last_pos'.ne) = 0
-/
@[simp] lemma predAbove_right_zero [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]
/-
**Fin.predAbove_zero_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 i.succ = i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_succ_of_le`：predAbove_succ_of_le (p i : Fin n) (h : p <= i
) : p.predAbove (succ i) = i
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
lemma predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 i.succ = i := by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le _)]
/-
**Fin.predAbove_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0), Fin.predAbove 
0 i = i.pred hi
参数：n + 1；hi : i ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_succ_eq`：exists_succ_eq {x : Fin (n + 1)} : (exists y, Fin.su
cc y = x) ↔ x != 0
· 使用引理 `Fin.predAbove_zero_succ`：predAbove_zero_succ [NeZero n] {i : Fin n} : pr
edAbove 0 i.succ = i
-/
@[simp] lemma predAbove_zero_of_ne_zero [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi
  exact predAbove_zero_succ
/-
**Fin.succ_predAbove_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j != 0) : succ (pred
Above 0 j) = j
参数：n + 1；h : j != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.predAbove_zero_of_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {i : Fin (n +
 1)} (hi : i ≠ 0), Fin.predAbove 0 i = i.pred hi
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j ≠ 0) : succ (predAbove 0 j) = j := by
  simp [h]
/-
**Fin.predAbove_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_zero [NeZero n] {i : Fin (n + 1)} : predAbove (0 : Fin n) i = if
 hi : i = 0 then 0 else i.pred hi
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Fin.predAbove_right_zero`：∀ {n : ℕ} [inst : NeZero n] {i : Fin n}, i.pre
dAbove 0 = 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Fin.predAbove_zero_of_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {i : Fin (n +
 1)} (hi : i ≠ 0), Fin.predAbove 0 i = i.pred hi
-/
lemma predAbove_zero [NeZero n] {i : Fin (n + 1)} :
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]
/-
**Fin.predAbove_right_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)}, i.predAbove (Fin.last (n + 1)) = Fin.last n
参数：n + 1；Fin.last (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.last_pos'`：last_pos' [NeZero n] : 0 < last n
· 使用定理 `Fin.pred_last`：pred_last (h
-/
@[simp] lemma predAbove_right_last {i : Fin (n + 1)} : predAbove i (last (n + 1)) = last n := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _), pred_last]
/-
**Fin.predAbove_last_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_last_castSucc {i : Fin (n + 1)} : predAbove (last n) (i.castSucc
) = i
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_le_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc ≤ b.ca
stSucc ↔ a ≤ b
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
-/
lemma predAbove_last_castSucc {i : Fin (n + 1)} : predAbove (last n) (i.castSucc) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr (le_last _)), castPred_castSucc]
/-
**Fin.predAbove_last_of_ne_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 2)} (hi : i ≠ Fin.last (n + 1)), (Fin.last n).pred
Above i = i.castPred hi
参数：n + 2；hi : i ≠ Fin.last (n + 1)；Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.exists_castSucc_eq`：∀ {n : ℕ} {i : Fin (n + 1)}, (∃ j, j.castSucc = 
i) ↔ i ≠ Fin.last n
· 使用引理 `Fin.predAbove_last_castSucc`：predAbove_last_castSucc {i : Fin (n + 1)} :
 predAbove (last n) (i.castSucc) = i
-/
@[simp] lemma predAbove_last_of_ne_last {i : Fin (n + 2)} (hi : i ≠ last (n + 1)) :
    predAbove (last n) i = castPred i hi := by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc
/-
**Fin.predAbove_last_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_last_apply {i : Fin (n + 2)} : predAbove (last n) i = if hi : i 
= last _ then last _ else i.castPred hi
参数：n + 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Fin.predAbove_right_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i.predAbove (Fin.
last (n + 1)) = Fin.last n
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Fin.predAbove_last_of_ne_last`：∀ {n : ℕ} {i : Fin (n + 2)} (hi : i ≠ Fin
.last (n + 1)), (Fin.last n).predAbove i = i.castPred hi
-/
lemma predAbove_last_apply {i : Fin (n + 2)} :
    predAbove (last n) i = if hi : i = last _ then last _ else i.castPred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]
/-
**Fin.predAbove_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_surjective {n : Nat} (p : Fin n) : Function.Surjective p.predAbo
ve
参数：p : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_castSucc_of_le`：predAbove_castSucc_of_le (p i : Fin n) (h 
: i <= p) : p.predAbove (castSucc i) = i
· 使用引理 `Fin.predAbove_succ_of_le`：predAbove_succ_of_le (p i : Fin n) (h : p <= i
) : p.predAbove (succ i) = i
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.not_le`：∀ {n : ℕ} {a b : Fin n}, ¬a ≤ b ↔ b < a
-/
lemma predAbove_surjective {n : ℕ} (p : Fin n) :
    Function.Surjective p.predAbove := by
  intro i
  by_cases hi : i ≤ p
  · exact ⟨i.castSucc, predAbove_castSucc_of_le p i hi⟩
  · rw [Fin.not_le] at hi
    exact ⟨i.succ, predAbove_succ_of_le p i (Fin.le_of_lt hi)⟩

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
/-
**Fin.succAbove_predAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i != castSucc p) : 
p.castSucc.succAbove (p.predAbove i) = i
参数：n + 1；h : i != castSucc p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_lt_of_ne`：∀ {n : ℕ} {a b : Fin n}, a ≠ b → a < b ∨ b < a
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用引理 `Fin.succAbove_pred_of_lt`：succAbove_pred_of_lt (p i : Fin (n + 1)) (h : 
p < i) : succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) =
 i

--- 原说明 ---
Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`.
-/
lemma succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p.succ` is the identity away from `p.succ`. -/
@[simp]
/-
**Fin.succ_succAbove_predAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succ_succAbove_predAbove {n : Nat} {p : Fin n} {i : Fin (n + 1)} (h : i !=
 p.succ) : p.succ.succAbove (p.predAbove i) = i
参数：n + 1；h : i != p.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_lt_of_ne`：∀ {n : ℕ} {a b : Fin n}, a ≠ b → a < b ∨ b < a
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用引理 `Fin.succAbove_pred_of_lt`：succAbove_pred_of_lt (p i : Fin (n + 1)) (h : 
p < i) : succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) =
 i

--- 原说明 ---
Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p.succ` is the identity away from `p
.succ`.
-/
lemma succ_succAbove_predAbove {n : ℕ} {p : Fin n} {i : Fin (n + 1)} (h : i ≠ p.succ) :
    p.succ.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (le_castSucc_iff.2 h),
      succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ (Fin.lt_of_le_of_lt (p.castSucc_le_succ) h),
      succAbove_pred_of_lt _ _ h]

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
/-
**Fin.predAbove_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_succAbove (p : Fin n) (i : Fin n) : p.predAbove ((castSucc p).su
ccAbove i) = i
参数：p : Fin n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.le_or_gt`：∀ {n : ℕ} (a b : Fin n), a ≤ b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_castSucc_of_le`：succAbove_castSucc_of_le (p i : Fin n) (h 
: p <= i) : succAbove p.castSucc i = i.succ
· 使用引理 `Fin.predAbove_succ_of_le`：predAbove_succ_of_le (p i : Fin n) (h : p <= i
) : p.predAbove (succ i) = i
· 使用引理 `Fin.succAbove_castSucc_of_lt`：succAbove_castSucc_of_lt (p i : Fin n) (h 
: i < p) : succAbove p.castSucc i = i.castSucc
· 使用引理 `Fin.predAbove_castSucc_of_le`：predAbove_castSucc_of_le (p i : Fin n) (h 
: i <= p) : p.predAbove (castSucc i) = i
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b

--- 原说明 ---
Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity.
-/
lemma predAbove_succAbove (p : Fin n) (i : Fin n) : p.predAbove ((castSucc p).succAbove i) = i := by
  obtain h | h := p.le_or_gt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

/-- `succ` commutes with `predAbove`. -/
/-
**Fin.succ_predAbove_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (a : Fin n) (b : Fin (n + 1)), a.succ.predAbove b.succ = (a.pred
Above b).succ
参数：a : Fin n；b : Fin (n + 1)；a.predAbove b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.le_or_gt`：∀ {n : ℕ} (a b : Fin n), a ≤ b ∨ b < a
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用引理 `Fin.predAbove_succ_of_le`：predAbove_succ_of_le (p i : Fin n) (h : p <= i
) : p.predAbove (succ i) = i
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用引理 `Fin.predAbove_of_lt_succ`：predAbove_of_lt_succ (p : Fin n) (i : Fin (n +
 1)) (h : i < succ p) : p.predAbove i = i.castPred (Fin.ne_last_of_lt h)
· 使用定理 `Fin.succ_ne_last_of_lt`：succ_ne_last_of_lt {p i : Fin n} (h : i < p) : s
ucc i != last n
· 使用引理 `Fin.predAbove_succ_of_lt`：predAbove_succ_of_lt (p i : Fin n) (h : i < p)
 : p.predAbove (succ i) = (i.succ).castPred (succ_ne_last_of_lt h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_ne_last_iff`：succ_ne_last_iff (a : Fin (n + 1)) : succ a != las
t (n + 1) ↔ a != last n
· 使用定理 `Fin.succ_castPred_eq_castPred_succ`：succ_castPred_eq_castPred_succ {a : 
Fin (n + 1)} (ha : a != last n) (ha'

--- 原说明 ---
`succ` commutes with `predAbove`.
-/
@[simp] lemma succ_predAbove_succ (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h | h := Fin.le_or_gt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]

/-- `castSucc` commutes with `predAbove`. -/
/-
**Fin.castSucc_predAbove_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (a : Fin n) (b : Fin (n + 1)), a.castSucc.predAbove b.castSucc =
 (a.predAbove b).castSucc
参数：a : Fin n；b : Fin (n + 1)；a.predAbove b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_ge`：∀ {n : ℕ} (a b : Fin n), a < b ∨ b ≤ a
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Fin.castSucc_ne_zero_of_lt`：castSucc_ne_zero_of_lt {p i : Fin n} (h : p 
< i) : castSucc i != 0
· 使用引理 `Fin.predAbove_castSucc_of_lt`：predAbove_castSucc_of_lt (p i : Fin n) (h 
: p < i) : p.predAbove (castSucc i) = i.castSucc.pred (castSucc_ne_zero_of_lt h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.castSucc_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, a.cas
tSucc ≠ 0 ↔ a ≠ 0
· 使用定理 `Fin.castSucc_pred_eq_pred_castSucc`：castSucc_pred_eq_pred_castSucc {a : 
Fin (n + 1)} (ha : a != 0) : (a.pred ha).castSucc = (castSucc a).pred (castSucc_
ne_zero_iff.mpr ha)
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用引理 `Fin.predAbove_castSucc_of_le`：predAbove_castSucc_of_le (p i : Fin n) (h 
: i <= p) : p.predAbove (castSucc i) = i
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i

--- 原说明 ---
`castSucc` commutes with `predAbove`.
-/
@[simp] lemma castSucc_predAbove_castSucc {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.castSucc.predAbove b.castSucc = (a.predAbove b).castSucc := by
  obtain h | h := a.castSucc.lt_or_ge b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]
/-
**Fin.predAbove_predAbove_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：predAbove_predAbove_succAbove {n : Nat} (i : Fin (n + 1)) (j : Fin n) : (j
.predAbove i).predAbove (i.succAbove j) = j
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_le`：∀ {n : ℕ} (a b : Fin n), a < b ∨ b ≤ a
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
-/
theorem predAbove_predAbove_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (j.predAbove i).predAbove (i.succAbove j) = j := by
  cases j.castSucc.lt_or_le i with
  | inl h =>
    rw [predAbove_of_castSucc_lt _ _ h, succAbove_of_castSucc_lt _ _ h, predAbove_of_le_castSucc,
      castPred_castSucc]
    rwa [le_castSucc_iff, succ_pred]
  | inr h =>
    rw [predAbove_of_le_castSucc _ _ h, succAbove_of_le_castSucc _ _ h, predAbove_of_castSucc_lt,
      pred_succ]
    rwa [castSucc_castPred, ← le_castSucc_iff]
/-
**Fin.succAbove_succAbove_predAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succAbove_succAbove_predAbove {n : Nat} (i : Fin (n + 1)) (j : Fin n) : (i
.succAbove j).succAbove (j.predAbove i) = i
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_le`：∀ {n : ℕ} (a b : Fin n), a < b ∨ b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用引理 `Fin.succAbove_predAbove`：succAbove_predAbove {p : Fin n} {i : Fin (n + 1
)} (h : i != castSucc p) : p.castSucc.succAbove (p.predAbove i) = i
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用引理 `Fin.succ_succAbove_predAbove`：succ_succAbove_predAbove {n : Nat} {p : Fi
n n} {i : Fin (n + 1)} (h : i != p.succ) : p.succ.succAbove (p.predAbove i) = i
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
-/
theorem succAbove_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).succAbove (j.predAbove i) = i := by
  cases Fin.lt_or_le j.castSucc i with
  | inl h => rw [succAbove_of_castSucc_lt _ _ h, succAbove_predAbove (Fin.ne_of_gt h)]
  | inr h =>
    rw [succAbove_of_le_castSucc _ _ h,
      succ_succAbove_predAbove (Fin.ne_of_lt <| le_castSucc_iff.mp h)]

/-- Given `i : Fin (n + 2)` and `j : Fin (n + 1)`,
there are two ways to represent the order embedding `Fin n → Fin (n + 2)`
leaving holes at `i` and `i.succAbove j`.

One is `i.succAbove ∘ j.succAbove`.
It corresponds to embedding `Fin n` to `Fin (n + 1)` leaving a hole at `j`,
then embedding the result to `Fin (n + 2)` leaving a hole at `i`.
The other one is `(i.succAbove j).succAbove ∘ (j.predAbove i).succAbove`.
It corresponds to swapping the roles of `i` and `j`.

This lemma says that these two ways are equal.
It is used in `Fin.removeNth_removeNth_eq_swap`
to show that two ways of removing 2 elements from a sequence give the same answer.
-/
/-
**Fin.succAbove_succAbove_succAbove_predAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succAbove_succAbove_succAbove_predAbove {n : Nat} (i : Fin (n + 2)) (j : F
in (n + 1)) (k : Fin n) : (i.succAbove j).succAbove ((j.predAbove i).succAbove k
) = i.succAbove (j.succAbove k)
参数：i : Fin (n + 2)；j : Fin (n + 1)；k : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
Given `i : Fin (n + 2)` and `j : Fin (n + 1)`,
there are two ways to represent the order embedding `Fin n → Fin (n + 2)`
leaving holes at `i` and `i.succAbove j`.

One is `i.succAbove ∘ j.succAbove`.
It corresponds to embedding `Fin n` to `Fin (n + 1)` leaving a hole at `j`,
then embedding the result to `Fin (n + 2)` leaving a hole at `i`.
The other one is `(i.succAbove j).succAbove ∘ (j.predAbove i).succAbove`.
It corresponds to swapping the roles of `i` and `j`.

This lemma says that these two ways are equal.
It is used in `Fin.removeNth_removeNth_eq_swap`
to show that two ways of removing 2 elements from a sequence give the same answe
r.
-/
theorem succAbove_succAbove_succAbove_predAbove {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  /- While it is possible to give a "morally correct" proof
  by saying that both functions are strictly monotone and have the same range `{i, i.succAbove j}ᶜ`,
  we give a direct proof by case analysis to avoid extra dependencies. -/
  ext
  simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val, val_pred, coe_castPred,
    dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> lia

end PredAbove

end Fin

