/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Lawrence Wu, Jeremy Tan
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cyclic permutations on `Fin n`

This file defines
* `finRotate`, which corresponds to the cycle `(1, ..., n)` on `Fin n`
* `finCycle`, the permutation that adds a fixed number to each element of `Fin n`
and proves various lemmas about them.
-/

@[expose] public section

open Nat

variable {n : ℕ}

/-- Rotate `Fin n` one step to the right. -/
/-
**finRotate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(n : ℕ) → Equiv.Perm (Fin n)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Rotate `Fin n` one step to the right.
-/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))
/-
**finRotate_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate 0 = Equiv.refl (Fin 0)
参数：Fin 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma finRotate_zero : finRotate 0 = Equiv.refl _ := rfl
/-
**finRotate_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finRotate_succ (n : Nat) : finRotate (n + 1) = finAddFlip.trans (finCongr 
(Nat.add_comm 1 n))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finRotate_succ (n : ℕ) :
    finRotate (n + 1) = finAddFlip.trans (finCongr (Nat.add_comm 1 n)) := rfl
/-
**finRotate_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_of_lt {k : Nat} (h : k < n) : finRotate (n + 1) ⟨k, h.trans_le n
.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩
参数：h : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `finAddFlip_apply_mk_left`：finAddFlip_apply_mk_left {k : Nat} (h : k < m)
 (hk : k < m + n
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finRotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]
/-
**finRotate_last'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, Nat.zero_lt_succ _⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finAddFlip_apply_mk_right`：finAddFlip_apply_mk_right {k : Nat} (h₁ : m <
= k) (h₂ : k < m + n) : finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by lia⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNeZeroNatHAdd`：∀ {n m : ℕ} [h : NeZero n], NeZero (n + m)
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp
/-
**finRotate_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_last : finRotate (n + 1) (Fin.last _) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finRotate_last'`：finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, N
at.zero_lt_succ _⟩
-/
theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'
/-
**Fin.snoc_eq_cons_rotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n -> α) (a : α) : @Fin.snoc _
 (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i)
参数：v : Fin n -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `finRotate_of_lt`：finRotate_of_lt {k : Nat} (h : k < n) : finRotate (n + 
1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩
· 使用定理 `Fin.snoc.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : (i : Fin n) →
 α i.castSucc) (x : α (Fin.last n)) (i : Fin (n + 1)),   Fin.snoc p x i = if h :
 ↑i…
· 使用定理 `Fin.cons.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u} (x : α 0) (p : (i : 
Fin n) → α i.succ) (j : Fin (n + 1)),   Fin.cons x p j = Fin.cases x p j
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_of_le_of_lt_succ`：∀ {n m : ℕ}, n ≤ m → m < n + 1 → m = n
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `finRotate_last'`：finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, N
at.zero_lt_succ _⟩
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last', Fin.snoc, Fin.cons, dif_neg (lt_irrefl _)]
    rfl

@[simp]
/-
**finRotate_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_one : finRotate 1 = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _

@[simp]
/-
**finRotate_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_apply (i : Fin n) : haveI
参数：i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Fin.eq_or_lt_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a = b ∨ a < b
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_last`：finRotate_last : finRotate (n + 1) (Fin.last _) = 0
· 使用定理 `Fin.last_add_one`：∀ (n : ℕ), Fin.last n + 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `finRotate_of_lt`：finRotate_of_lt {k : Nat} (h : k < n) : finRotate (n + 
1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
-/
theorem finRotate_apply (i : Fin n) : haveI := i.neZero; finRotate n i = i + 1 := by
  match n with
  | 0 => exact i.elim0
  | 1 => exact @Subsingleton.elim (Fin 1) _ _ _
  | n + 2 =>
    obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
    · simp [finRotate_last]
    · cases i
      simp only [Fin.lt_def, Fin.val_last] at h
      simp [finRotate_of_lt h, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]

@[deprecated finRotate_apply (since := "2026-03-29")]
/-
**finRotate_succ_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := by
  simp
/-
**finRotate_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_apply_zero : finRotate n.succ 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finRotate_apply_zero : finRotate n.succ 0 = 1 := by
  simp
/-
**coe_finRotate_of_ne_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_finRotate_of_ne_last {i : Fin n.succ} (h : i != Fin.last n) : (finRota
te (n + 1) i : Nat) = i + 1
参数：h : i != Fin.last n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `Fin.val_add_one_of_lt`：∀ {n : ℕ} {i : Fin n.succ}, i < Fin.last n → ↑(i 
+ 1) = ↑i + 1
-/
theorem coe_finRotate_of_ne_last {i : Fin n.succ} (h : i ≠ Fin.last n) :
    (finRotate (n + 1) i : ℕ) = i + 1 := by
  rw [finRotate_apply]
  have : (i : ℕ) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this
/-
**coe_finRotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_finRotate (i : Fin n.succ) : (finRotate n.succ i : Nat) = if i = Fin.l
ast n then (0 : Nat) else i + 1
参数：i : Fin n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.val_add_one`：∀ {n : ℕ} (i : Fin (n + 1)), ↑(i + 1) = if i = Fin.last
 n then 0 else ↑i + 1
-/
theorem coe_finRotate (i : Fin n.succ) :
    (finRotate n.succ i : ℕ) = if i = Fin.last n then (0 : ℕ) else i + 1 := by
  rw [finRotate_apply, Fin.val_add_one i]
/-
**lt_finRotate_iff_ne_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_finRotate_iff_ne_last (i : Fin (n + 1)) : i < finRotate _ i ↔ i != Fin.
last n
参数：i : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
-/
theorem lt_finRotate_iff_ne_last (i : Fin (n + 1)) :
    i < finRotate _ i ↔ i ≠ Fin.last n := by
  simpa using Fin.lt_last_iff_ne_last
/-
**lt_finRotate_iff_ne_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) : i < finRotate _ i ↔ i
 != -1
参数：i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_finRotate_iff_ne_last`：lt_finRotate_iff_ne_last (i : Fin (n + 1)) : i
 < finRotate _ i ↔ i != Fin.last n
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.neg_last`：∀ (n : ℕ), -Fin.last n = 1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) :
    i < finRotate _ i ↔ i ≠ -1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last, ne_eq, not_iff_not, ← Fin.neg_last, neg_neg]

@[simp]
/-
**finRotate_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finRotate_symm_apply (i : Fin n) : haveI
参数：i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma finRotate_symm_apply (i : Fin n) : haveI := i.neZero; (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero i.pos.ne'
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_apply, sub_add_cancel]

@[deprecated finRotate_symm_apply (since := "2026-03-29")]
/-
**finRotate_succ_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = 
i - 1
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `finRotate_symm_apply`：finRotate_symm_apply (i : Fin n) : haveI
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = i - 1 := by
  simp
/-
**coe_finRotate_symm_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i != 0) : ((fin
Rotate _).symm i : Nat) = i - 1
参数：hi : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `finRotate_symm_apply`：finRotate_symm_apply (i : Fin n) : haveI
· 使用引理 `Fin.val_sub_one_of_ne_zero`：val_sub_one_of_ne_zero {i : Fin n} : haveI
-/
lemma coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    ((finRotate _).symm i : ℕ) = i - 1 := by
  rwa [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]
/-
**finRotate_symm_lt_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) : (finRotate _).symm 
i < i ↔ i != 0
参数：i : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用引理 `coe_finRotate_symm_of_ne_zero`：coe_finRotate_symm_of_ne_zero [NeZero n] 
{i : Fin n} (hi : i != 0) : ((finRotate _).symm i : Nat) = i - 1
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.val_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, ↑a ≠ 0 ↔ a
 ≠ 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) :
    (finRotate _).symm i < i ↔ i ≠ 0 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨ne_zero_of_lt, fun hi ↦ ?_⟩
  rw [Fin.lt_def, coe_finRotate_symm_of_ne_zero hi]
  exact sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) zero_lt_one

/-- The permutation on `Fin n` that adds `k` to each number. -/
@[simps]
/-
**finCycle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finCycle (k : Fin n) : Equiv.Perm (Fin n) where toFun i
参数：k : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permutation on `Fin n` that adds `k` to each number.
-/
def finCycle (k : Fin n) : Equiv.Perm (Fin n) where
  toFun i := i + k
  invFun i := i - k
  left_inv i := by have := NeZero.of_pos k.pos; simp
  right_inv i := by have := NeZero.of_pos k.pos; simp
/-
**finCycle_eq_finRotate_iterate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finCycle_eq_finRotate_iterate {k : Fin n} : finCycle k = (finRotate n)^[k.
1]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finCycle_apply`：∀ {n : ℕ} (k i : Fin n), (finCycle k) i = i + k
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.val_succ`：∀ {n : ℕ} (j : Fin n), ↑j.succ = ↑j + 1
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_castSucc`：∀ {n : ℕ} (i : Fin n), ↑i.castSucc = ↑i
· 使用定理 `Fin.val_eq_val`：val_eq_val (a b : Fin n) : (a : Nat) = b ↔ a = b
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Fin.coeSucc_eq_succ`：∀ {n : ℕ} {a : Fin n}, a.castSucc + 1 = a.succ
-/
lemma finCycle_eq_finRotate_iterate {k : Fin n} : finCycle k = (finRotate n)^[k.1] := by
  match n with
  | 0 => exact k.elim0
  | n + 1 =>
    ext i; induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      rw [Fin.val_eq_val, Fin.val_castSucc] at ih
      rw [Fin.val_succ, Function.iterate_succ', Function.comp_apply, ← ih, finRotate_apply,
        finCycle_apply, finCycle_apply, add_assoc, Fin.coeSucc_eq_succ]
