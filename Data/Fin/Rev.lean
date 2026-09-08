/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Joel Riou, Yury Kudryashov
-/
module

public import Mathlib.Data.Fin.SuccPred
/-!
# Reverse on `Fin n`

This file contains lemmas about `Fin.rev : Fin n → Fin n` which maps `i` to `n - 1 - i`.

## Definitions

* `Fin.revPerm : Equiv.Perm (Fin n)` : `Fin.rev` as an `Equiv.Perm`, the antitone involution given
  by `i ↦ n-(i+1)`
-/

@[expose] public section

assert_not_exists Monoid Fintype

open Fin Nat Function

namespace Fin

variable {n m : ℕ}

/-
**Fin.rev_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_involutive : Involutive (rev : Fin n -> Fin n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
-/
theorem rev_involutive : Involutive (rev : Fin n → Fin n) := rev_rev

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
@[simps! apply]
/-
**Fin.revPerm** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：revPerm : Equiv.Perm (Fin n)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.rev_involutive`：rev_involutive : Involutive (rev : Fin n -> Fin n)

--- 原说明 ---
`Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`.
-/
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm rev rev_involutive
/-
**Fin.rev_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_injective : Injective (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `Fin.rev_involutive`：rev_involutive : Involutive (rev : Fin n -> Fin n)
-/
theorem rev_injective : Injective (@rev n) :=
  rev_involutive.injective
/-
**Fin.rev_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_surjective : Surjective (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `Fin.rev_involutive`：rev_involutive : Involutive (rev : Fin n -> Fin n)
-/
theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.surjective
/-
**Fin.rev_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_bijective : Bijective (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `Fin.rev_involutive`：rev_involutive : Involutive (rev : Fin n -> Fin n)
-/
theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.bijective

@[simp]
/-
**Fin.revPerm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：revPerm_symm : (@revPerm n).symm = revPerm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl
/-
**Fin.cast_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_rev (i : Fin n) (h : n = m) : i.rev.cast h = (i.cast h).rev
参数：i : Fin n；h : n = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_rev (i : Fin n) (h : n = m) :
    i.rev.cast h = (i.cast h).rev := by
  subst h; simp
/-
**Fin.rev_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_inj`：∀ {n : ℕ} {i j : Fin n}, i.rev = j.rev ↔ i = j
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j := by
  rw [← rev_inj, rev_rev]
/-
**Fin.rev_ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_ne_iff {i j : Fin n} : rev i != j ↔ i != rev j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.rev_eq_iff`：rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j
-/
theorem rev_ne_iff {i j : Fin n} : rev i ≠ j ↔ i ≠ rev j := rev_eq_iff.not
/-
**Fin.rev_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_lt_iff {i j : Fin n} : rev i < j ↔ rev j < i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_lt_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev < j.rev ↔ j < i
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rev_lt_iff {i j : Fin n} : rev i < j ↔ rev j < i := by
  rw [← rev_lt_rev, rev_rev]
/-
**Fin.rev_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_le_iff {i j : Fin n} : rev i <= j ↔ rev j <= i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_le_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev ≤ j.rev ↔ j ≤ i
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rev_le_iff {i j : Fin n} : rev i ≤ j ↔ rev j ≤ i := by
  rw [← rev_le_rev, rev_rev]
/-
**Fin.lt_rev_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：lt_rev_iff {i j : Fin n} : i < rev j ↔ j < rev i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_lt_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev < j.rev ↔ j < i
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_rev_iff {i j : Fin n} : i < rev j ↔ j < rev i := by
  rw [← rev_lt_rev, rev_rev]
/-
**Fin.le_rev_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_rev_iff {i j : Fin n} : i <= rev j ↔ j <= rev i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_le_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev ≤ j.rev ↔ j ≤ i
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_rev_iff {i j : Fin n} : i ≤ rev j ↔ j ≤ rev i := by
  rw [← rev_le_rev, rev_rev]
/-
**Fin.val_rev_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_rev_zero [NeZero n] : ((rev 0 : Fin n) : Nat) = n.pred
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_rev_zero [NeZero n] : ((rev 0 : Fin n) : ℕ) = n.pred := rfl
/-
**Fin.rev_pred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_pred {i : Fin (n + 1)} (h : i != 0) (h'
参数：n + 1；h : i != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_inj`：∀ {n : ℕ} {a b : Fin n}, a.castSucc = b.castSucc ↔ a =
 b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Fin.rev_succ`：∀ {n : ℕ} (k : Fin n), k.succ.rev = k.rev.castSucc
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
-/
theorem rev_pred {i : Fin (n + 1)} (h : i ≠ 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h)) :
    rev (pred i h) = castPred (rev i) h' := by
  rw [← castSucc_inj, castSucc_castPred, ← rev_succ, succ_pred]
/-
**Fin.rev_castPred** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_castPred {i : Fin (n + 1)} (h : i != last n) (h'
参数：n + 1；h : i != last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_inj`：∀ {n : ℕ} {a b : Fin n}, a.succ = b.succ ↔ a = b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Fin.rev_castSucc`：∀ {n : ℕ} (k : Fin n), k.castSucc.rev = k.rev.succ
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
-/
theorem rev_castPred {i : Fin (n + 1)}
    (h : i ≠ last n) (h' := rev_ne_iff.mpr ((rev_zero _).symm ▸ h)) :
    rev (castPred i h) = pred (rev i) h' := by
  rw [← succ_inj, succ_pred, ← rev_castSucc, castSucc_castPred]
/-
**Fin.succAbove_rev_left** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_rev_left (p : Fin (n + 1)) (i : Fin n) : p.rev.succAbove i = (p.
succAbove i.rev).rev
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.succ_le_or_le_castSucc`：succ_le_or_le_castSucc (p : Fin (n + 1)) (i 
: Fin n) : succ i <= p ∨ p <= i.castSucc
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_succ_le`：succAbove_of_succ_le (p : Fin (n + 1)) (i : Fi
n n) (h : succ i <= p) : p.succAbove i = castSucc i
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_rev_iff`：le_rev_iff {i j : Fin n} : i <= rev j ↔ j <= rev i
· 使用定理 `Fin.rev_succ`：∀ {n : ℕ} (k : Fin n), k.succ.rev = k.rev.castSucc
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Fin.rev_le_iff`：rev_le_iff {i j : Fin n} : rev i <= j ↔ rev j <= i
· 使用定理 `Fin.rev_castSucc`：∀ {n : ℕ} (k : Fin n), k.castSucc.rev = k.rev.succ
-/
lemma succAbove_rev_left (p : Fin (n + 1)) (i : Fin n) :
    p.rev.succAbove i = (p.succAbove i.rev).rev := by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSucc, rev_rev]
/-
**Fin.succAbove_rev_right** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_rev_right (p : Fin (n + 1)) (i : Fin n) : p.succAbove i.rev = (p
.rev.succAbove i).rev
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_rev_left`：succAbove_rev_left (p : Fin (n + 1)) (i : Fin n)
 : p.rev.succAbove i = (p.succAbove i.rev).rev
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
-/
lemma succAbove_rev_right (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i.rev = (p.rev.succAbove i).rev := by rw [succAbove_rev_left, rev_rev]

/-- `rev` commutes with `succAbove`. -/
/-
**Fin.rev_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_succAbove (p : Fin (n + 1)) (i : Fin n) : rev (succAbove p i) = succAb
ove (rev p) (rev i)
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_rev_left`：succAbove_rev_left (p : Fin (n + 1)) (i : Fin n)
 : p.rev.succAbove i = (p.succAbove i.rev).rev
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i

--- 原说明 ---
`rev` commutes with `succAbove`.
-/
lemma rev_succAbove (p : Fin (n + 1)) (i : Fin n) :
    rev (succAbove p i) = succAbove (rev p) (rev i) := by
  rw [succAbove_rev_left, rev_rev]
/-
**Fin.predAbove_rev_left** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_rev_left (p : Fin n) (i : Fin (n + 1)) : p.rev.predAbove i = (p.
predAbove i.rev).rev
参数：p : Fin n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.succ_le_or_le_castSucc`：succ_le_or_le_castSucc (p : Fin (n + 1)) (i 
: Fin n) : succ i <= p ∨ p <= i.castSucc
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_lt_of_le`：∀ {n : ℕ} {a b c : Fin n}, a < b → b ≤ c → a < c
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_succ_le`：predAbove_of_succ_le (p : Fin n) (i : Fin (n +
 1)) (h : succ p <= i) : p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of
_le (succ_pos …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.rev_ne_iff`：rev_ne_iff {i j : Fin n} : rev i != j ↔ i != rev j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `Fin.rev_pred`：rev_pred {i : Fin (n + 1)} (h : i != 0) (h'
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.le_rev_iff`：le_rev_iff {i j : Fin n} : i <= rev j ↔ j <= rev i
· 使用定理 `Fin.rev_succ`：∀ {n : ℕ} (k : Fin n), k.succ.rev = k.rev.castSucc
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Fin.castPred_inj`：castPred_inj {i j : Fin (n + 1)} {hi : i != last n} {h
j : j != last n} : castPred i hi = castPred j hj ↔ i = j
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `Fin.rev_castPred`：rev_castPred {i : Fin (n + 1)} (h : i != last n) (h'
· 使用定理 `Fin.rev_le_iff`：rev_le_iff {i j : Fin n} : rev i <= j ↔ rev j <= i
· 使用定理 `Fin.rev_castSucc`：∀ {n : ℕ} (k : Fin n), k.castSucc.rev = k.rev.succ
· 使用定理 `Fin.pred_inj`：∀ {n : ℕ} {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a
.pred ha = b.pred hb ↔ a = b
-/
lemma predAbove_rev_left (p : Fin n) (i : Fin (n + 1)) :
    p.rev.predAbove i = (p.predAbove i.rev).rev := by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), pred_inj, rev_rev]
/-
**Fin.predAbove_rev_right** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_rev_right (p : Fin n) (i : Fin (n + 1)) : p.predAbove i.rev = (p
.rev.predAbove i).rev
参数：p : Fin n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_rev_left`：predAbove_rev_left (p : Fin n) (i : Fin (n + 1))
 : p.rev.predAbove i = (p.predAbove i.rev).rev
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
-/
lemma predAbove_rev_right (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i.rev = (p.rev.predAbove i).rev := by rw [predAbove_rev_left, rev_rev]

/-- `rev` commutes with `predAbove`. -/
/-
**Fin.rev_predAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_predAbove {n : Nat} (p : Fin n) (i : Fin (n + 1)) : (predAbove p i).re
v = predAbove p.rev i.rev
参数：p : Fin n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_rev_left`：predAbove_rev_left (p : Fin n) (i : Fin (n + 1))
 : p.rev.predAbove i = (p.predAbove i.rev).rev
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i

--- 原说明 ---
`rev` commutes with `predAbove`.
-/
lemma rev_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (predAbove p i).rev = predAbove p.rev i.rev := by rw [predAbove_rev_left, rev_rev]
/-
**Fin.add_rev_cast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：add_rev_cast (j : Fin (n + 1)) : j.1 + j.rev.1 = n
参数：j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_rev_cast (j : Fin (n + 1)) : j.1 + j.rev.1 = n := by
  obtain ⟨j, hj⟩ := j
  simp [Nat.add_sub_cancel' <| le_of_lt_succ hj]
/-
**Fin.rev_add_cast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_add_cast (j : Fin (n + 1)) : j.rev.1 + j.1 = n
参数：j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用引理 `Fin.add_rev_cast`：add_rev_cast (j : Fin (n + 1)) : j.1 + j.rev.1 = n
-/
lemma rev_add_cast (j : Fin (n + 1)) : j.rev.1 + j.1 = n := by
  rw [Nat.add_comm, j.add_rev_cast]

end Fin

