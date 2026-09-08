/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Conditions for `Fin.insertNth` to be monotone or strictly monotone

-/

public section

namespace Fin

variable {n : ℕ} {α : Type*} [Preorder α]

/-
**Fin.insertNth_zero_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_zero_monotone {f : Fin (n + 1) -> α} (hf : Monotone f) (x : α) (
hx : x <= f 0) : Monotone (Fin.insertNth 0 (α
参数：n + 1；hf : Monotone f；x : α；hx : x <= f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.monotone_iff_le_succ`：monotone_iff_le_succ : Monotone f ↔ forall i :
 Fin n, f (castSucc i) <= f i.succ
· 使用定理 `Fin.eq_zero_or_eq_succ`：∀ {n : ℕ} (i : Fin (n + 1)), i = 0 ∨ ∃ j, i = j.
succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_zero'`：insertNth_zero' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) 0 x p = cons x p
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
-/
lemma insertNth_zero_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (x : α) (hx : x ≤ f 0) :
    Monotone (Fin.insertNth 0 (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i.castSucc_le_succ
/-
**Fin.strictMono_insertNth_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_insertNth_zero {f : Fin (n + 1) -> α} (hf : StrictMono f) (x : 
α) (hx : x < f 0) : StrictMono (Fin.insertNth 0 (α
参数：n + 1；hf : StrictMono f；x : α；hx : x < f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用定理 `Fin.eq_zero_or_eq_succ`：∀ {n : ℕ} (i : Fin (n + 1)), i = 0 ∨ ∃ j, i = j.
succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_zero'`：insertNth_zero' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) 0 x p = cons x p
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
lemma strictMono_insertNth_zero
    {f : Fin (n + 1) → α} (hf : StrictMono f) (x : α) (hx : x < f 0) :
    StrictMono (Fin.insertNth 0 (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i
/-
**Fin.insertNth_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_monotone {f : Fin (n + 1) -> α} (hf : Monotone f) (i : Fin n) (x
 : α) (hx₁ : f i.castSucc <= x) (hx₂ : x <= f i.succ) : Monotone (Fin.insertNth 
i.castSucc.succ (α
参数：n + 1；hf : Monotone f；i : Fin n；x : α；hx₁ : f i.castSucc <= x；hx₂ : x <= f i.
succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.monotone_iff_le_succ`：monotone_iff_le_succ : Monotone f ↔ forall i :
 Fin n, f (castSucc i) <= f i.succ
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Fin.eq_castSucc_of_ne_last`：eq_castSucc_of_ne_last {x : Fin (n + 1)} (h 
: x != (last _)) : exists y, Fin.castSucc y = x
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_succ_self`：∀ {n : ℕ} (j : Fin n), j.succ.succAbove j = j.c
astSucc
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.eq_succ_of_ne_zero`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ 0 → ∃ j, i = j.
succ
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
-/
lemma insertNth_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc ≤ x) (hx₂ : x ≤ f i.succ) :
    Monotone (Fin.insertNth i.castSucc.succ (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc, hf j.castSucc_le_succ]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above, hf j.castSucc_le_succ]
/-
**Fin.strictMono_insertNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_insertNth {f : Fin (n + 1) -> α} (hf : StrictMono f) (i : Fin n
) (x : α) (hx₁ : f i.castSucc < x) (hx₂ : x < f i.succ) : StrictMono (Fin.insert
Nth i.castSucc.succ (α
参数：n + 1；hf : StrictMono f；i : Fin n；x : α；hx₁ : f i.castSucc < x；hx₂ : x < f i.
succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Fin.eq_castSucc_of_ne_last`：eq_castSucc_of_ne_last {x : Fin (n + 1)} (h 
: x != (last _)) : exists y, Fin.castSucc y = x
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_succ_self`：∀ {n : ℕ} (j : Fin n), j.succ.succAbove j = j.c
astSucc
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.eq_succ_of_ne_zero`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ 0 → ∃ j, i = j.
succ
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
-/
lemma strictMono_insertNth
    {f : Fin (n + 1) → α} (hf : StrictMono f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc < x) (hx₂ : x < f i.succ) :
    StrictMono (Fin.insertNth i.castSucc.succ (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above]
/-
**Fin.insertNth_last_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_last_monotone {f : Fin (n + 1) -> α} (hf : Monotone f) (x : α) (
hx : f (Fin.last n) <= x) : Monotone (Fin.insertNth (Fin.last (n + 1)) (α
参数：n + 1；hf : Monotone f；x : α；hx : f (Fin.last n) <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.monotone_iff_le_succ`：monotone_iff_le_succ : Monotone f ↔ forall i :
 Fin n, f (castSucc i) <= f i.succ
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
-/
lemma insertNth_last_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (x : α) (hx : f (Fin.last n) ≤ x) :
    Monotone (Fin.insertNth (Fin.last (n + 1)) (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i.castSucc_le_succ
  · simpa
/-
**Fin.strictMono_insertNth_last** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_insertNth_last {f : Fin (n + 1) -> α} (hf : StrictMono f) (x : 
α) (hx : f (Fin.last n) < x) : StrictMono (Fin.insertNth (Fin.last (n + 1)) (α
参数：n + 1；hf : StrictMono f；x : α；hx : f (Fin.last n) < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
-/
lemma strictMono_insertNth_last
    {f : Fin (n + 1) → α} (hf : StrictMono f) (x : α) (hx : f (Fin.last n) < x) :
    StrictMono (Fin.insertNth (Fin.last (n + 1)) (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i
  · simpa

end Fin

