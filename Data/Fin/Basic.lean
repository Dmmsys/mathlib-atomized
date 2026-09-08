/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Data.Int.DivMod
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Common
public import Batteries.Data.Fin.Basic

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
  Further definitions and eliminators can be found in `Init.Data.Fin.Lemmas`
* `Fin.equivSubtype` : Equivalence between `Fin n` and `{ i // i < n }`.

-/

@[expose] public section


assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

/-
**Nat.forall_lt_iff_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.forall_lt_iff_fin {n : Nat} {p : forall k, k < n -> Prop} : (forall k 
hk, p k hk) ↔ forall k : Fin n, p k k.is_lt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Fin.forall_iff`：∀ {n : ℕ} {p : Fin n → Prop}, (∀ (i : Fin n), p i) ↔ ∀ (
i : ℕ) (h : i < n), p ⟨i, h⟩
-/
theorem Nat.forall_lt_iff_fin {n : ℕ} {p : ∀ k, k < n → Prop} :
    (∀ k hk, p k hk) ↔ ∀ k : Fin n, p k k.is_lt :=
  .symm <| Fin.forall_iff
/-
**Nat.exists_lt_iff_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.exists_lt_iff_fin {n : Nat} {p : forall k, k < n -> Prop} : (exists k 
hk, p k hk) ↔ exists k : Fin n, p k k.is_lt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Fin.exists_iff`：∀ {n : ℕ} {p : Fin n → Prop}, (∃ i, p i) ↔ ∃ i, ∃ (h : i
 < n), p ⟨i, h⟩
-/
theorem Nat.exists_lt_iff_fin {n : ℕ} {p : ∀ k, k < n → Prop} :
    (∃ k hk, p k hk) ↔ ∃ k : Fin n, p k k.is_lt :=
  .symm <| Fin.exists_iff

/-- Elimination principle for the empty set `Fin 0`, dependent version. -/
/-
**finZeroElim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finZeroElim {α : Fin 0 -> Sort*} (x : Fin 0) : α x
参数：x : Fin 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elimination principle for the empty set `Fin 0`, dependent version.
-/
def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0

namespace Fin

/-
**Fin.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n a : ℕ} {ha : a < n + 2}, ⟨a, ha⟩ = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.mk.inj_iff`：∀ {n a b : ℕ} {ha : a < n} {hb : b < n}, ⟨a, ha⟩ = ⟨b, h
b⟩ ↔ a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] theorem mk_eq_one {n a : Nat} {ha : a < n + 2} :
    (⟨a, ha⟩ : Fin (n + 2)) = 1 ↔ a = 1 :=
  mk.inj_iff
/-
**Fin.one_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n a : ℕ} {ha : a < n + 2}, 1 = ⟨a, ha⟩ ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem one_eq_mk {n a : Nat} {ha : a < n + 2} :
    1 = (⟨a, ha⟩ : Fin (n + 2)) ↔ a = 1 := by
  simp [eq_comm]
/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : CanLift ℕ (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/-- A dependent variant of `Fin.elim0`. -/
/-
**Fin.rec0** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：rec0 {α : Fin 0 -> Sort*} (i : Fin 0) : α i
参数：i : Fin 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent variant of `Fin.elim0`.
-/
def rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

variable {n m : ℕ}
/-
**Fin.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_injective : Function.Injective (@Fin.val n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.eq_of_val_eq`：∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
-/
theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_val_eq n

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
/-
**Fin.size_positive** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：size_positive : Fin n -> 0 < n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n

--- 原说明 ---
If you actually have an element of `Fin n`, then the `n` is always positive
-/
lemma size_positive : Fin n → 0 < n := Fin.pos
/-
**Fin.size_positive'** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：size_positive' [Nonempty (Fin n)] : 0 < n
参数：Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
-/
lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim Fin.pos
/-
**Fin.prop** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (a : Fin n), ↑a < n
参数：a : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
protected theorem prop (a : Fin n) : a.val < n :=
  a.2
/-
**Fin.lt_last_iff_ne_last** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：lt_last_iff_ne_last {a : Fin (n + 1)} : a < last n ↔ a != last n
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_last_iff_ne_last {a : Fin (n + 1)} : a < last n ↔ a ≠ last n := by
  simp [Fin.lt_iff_le_and_ne, le_last]
/-
**Fin.ne_zero_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b != 0
参数：n + 1；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
lemma ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b ≠ 0 :=
  Fin.ne_of_gt <| Fin.lt_of_le_of_lt a.zero_le hab
/-
**Fin.ne_last_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a != last n
参数：n + 1；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_lt_of_le`：∀ {n : ℕ} {a b c : Fin n}, a < b → b ≤ c → a < c
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
-/
lemma ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a ≠ last n :=
  Fin.ne_of_lt <| Fin.lt_of_lt_of_le hab b.le_last
/-
**Fin.ne_last_of_ne_last_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (hb : b != last n) (hab : a <
= b) : a != last n
参数：n + 1；hb : b != last n；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_lt_of_le`：∀ {a b : ℕ}, a ≤ b → ¬b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (hb : b ≠ last n) (hab : a ≤ b) :
    a ≠ last n := by
  intro rfl
  exact Nat.not_lt_of_le hab (lt_last_iff_ne_last.mpr hb)
/-
**Fin.val_sub_lt_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：val_sub_lt_of_lt_of_le {a b : Fin n} (ha : a.val < m) (hab : b <= a) : (a 
- b).val < m
参数：ha : a.val < m；hab : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `Nat.sub_lt_of_lt`：∀ {a b c : ℕ}, a < c → a - b < c
-/
lemma val_sub_lt_of_lt_of_le {a b : Fin n} (ha : a.val < m) (hab : b ≤ a) :
    (a - b).val < m := by
  rw [Fin.sub_val_of_le hab]
  exact sub_lt_of_lt ha
/-
**Fin.sub_ne_last_of_ne_last_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sub_ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (ha : a != last n) (hab :
 b <= a) : a - b != last n
参数：n + 1；ha : a != last n；hab : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.lt_last_iff_ne_last`：lt_last_iff_ne_last {a : Fin (n + 1)} : a < las
t n ↔ a != last n
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用引理 `Fin.val_sub_lt_of_lt_of_le`：val_sub_lt_of_lt_of_le {a b : Fin n} (ha : a
.val < m) (hab : b <= a) : (a - b).val < m
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
-/
lemma sub_ne_last_of_ne_last_of_le {a b : Fin (n + 1)} (ha : a ≠ last n) (hab : b ≤ a) :
    a - b ≠ last n := by
  rw [← lt_last_iff_ne_last, lt_def]
  exact val_sub_lt_of_lt_of_le (val_lt_last ha) hab

/-- Equivalence between `Fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
/-
**Fin.equivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：equivSubtype : Fin n ≃ { i // i < n } where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n

--- 原说明 ---
Equivalence between `Fin n` and `{ i // i < n }`.
-/
def equivSubtype : Fin n ≃ { i // i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
/-
**Fin.neZero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：neZero {n : Nat} (i : Fin n) : NeZero n
参数：i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma neZero {n : ℕ} (i : Fin n) : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩

section coe

/-!
### coercions and constructions
-/

/-
**Fin.val_eq_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_eq_val (a b : Fin n) : (a : Nat) = b ↔ a = b
参数：a b : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b

--- 原说明 ---
### coercions and constructions
-/
theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  Fin.ext_iff.symm
/-
**Fin.ne_iff_vne** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：ne_iff_vne (a b : Fin n) : a != b ↔ a.1 != b.1
参数：a b : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
-/
theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  Fin.ext_iff.not
/-
**Fin.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
-/
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  Fin.ext_iff

/-- Assume `k = l`. If two functions defined on `Fin k` and `Fin l` are equal on each element,
then they coincide (in the heq sense). -/
/-
**Fin.heq_fun_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Sort u_1} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α}, f 
≍ g ↔ ∀ (i : Fin k), f i = g ⟨↑i, ⋯⟩
参数：h : k = l；i : Fin k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Assume `k = l`. If two functions defined on `Fin k` and `Fin l` are equal on eac
h element,
then they coincide (in the heq sense).
-/
protected theorem heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    f ≍ g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [funext_iff]

/-- Assume `k = l` and `k' = l'`.
If two functions `Fin k → Fin k' → α` and `Fin l → Fin l' → α` are equal on each pair,
then they coincide (in the heq sense). -/
/-
**Fin.heq_fun** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume `k = l` and `k' = l'`.
If two functions `Fin k → Fin k' → α` and `Fin l → Fin l' → α` are equal on each
 pair,
then they coincide (in the heq sense).
-/
protected theorem heq_fun₂_iff {α : Sort*} {k l k' l' : ℕ} (h : k = l) (h' : k' = l')
    {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α} :
    f ≍ g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g ⟨(i : ℕ), h ▸ i.2⟩ ⟨(j : ℕ), h' ▸ j.2⟩ := by
  subst h
  subst h'
  simp [funext_iff]

/-- Two elements of `Fin k` and `Fin l` are heq iff their values in `ℕ` coincide. This requires
`k = l`. For the left implication without this assumption, see `val_eq_val_of_heq`. -/
/-
**Fin.heq_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {k l : ℕ}, k = l → ∀ {i : Fin k} {j : Fin l}, i ≍ j ↔ ↑i = ↑j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two elements of `Fin k` and `Fin l` are heq iff their values in `ℕ` coincide. Th
is requires
`k = l`. For the left implication without this assumption, see `val_eq_val_of_he
q`.
-/
protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    i ≍ j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  simp [val_eq_val]

end coe


section Order

/-!
### order
-/

/-- `Fin.lt_or_ge` is an alias of `Fin.lt_or_le`.
It is preferred since it follows the mathlib naming convention. -/
protected alias lt_or_ge := Fin.lt_or_le
/-- `Fin.le_or_gt` is an alias of `Fin.le_or_lt`.
It is preferred since it follows the mathlib naming convention. -/
protected alias le_or_gt := Fin.le_or_lt

/-
**Fin.le_iff_val_le_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : Nat) <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_val_le_val {a b : Fin n} : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast, simp]
/-
**Fin.val_fin_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_fin_lt {n : Nat} {a b : Fin n} : (a : Nat) < (b : Nat) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`a < b` as natural numbers if and only if `a < b` in `Fin n`.
-/
theorem val_fin_lt {n : ℕ} {a b : Fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
  Iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `Fin n`. -/
@[norm_cast, simp]
/-
**Fin.val_fin_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_fin_le {n : Nat} {a b : Fin n} : (a : Nat) <= (b : Nat) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`a ≤ b` as natural numbers if and only if `a ≤ b` in `Fin n`.
-/
theorem val_fin_le {n : ℕ} {a b : Fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
  Iff.rfl
/-
**Fin.min_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：min_val {a : Fin n} : min (a : Nat) n = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp
/-
**Fin.max_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：max_val {a : Fin n} : max (a : Nat) n = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp

/-- Use the ordering on `Fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `WellFoundedRelation` instance:
```lean
def factorial {n : ℕ} : Fin n → ℕ
  | ⟨0, _⟩ := 1
  | ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the ordering on `Fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker
,
unless we declare the `WellFoundedRelation` instance:
```lean
def factorial {n : ℕ} : Fin n → ℕ
  | ⟨0, _⟩ := 1
  | ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : WellFoundedRelation (Fin n) :=
  measure (val : Fin n → ℕ)

/-- `Fin.mk_zero` in `Lean` only applies in `Fin (n + 1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/-
**Fin.mk_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：mk_zero' (n : Nat) [NeZero n] : (⟨0, pos_of_neZero n⟩ : Fin n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n

--- 原说明 ---
`Fin.mk_zero` in `Lean` only applies in `Fin (n + 1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem mk_zero' (n : ℕ) [NeZero n] : (⟨0, pos_of_neZero n⟩ : Fin n) = 0 := rfl

@[simp, norm_cast]
/-
**Fin.val_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_pos_iff [NeZero n] {a : Fin n} : 0 < a.val ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_fin_lt`：val_fin_lt {n : Nat} {a b : Fin n} : (a : Nat) < (b : Na
t) ↔ a < b
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_pos_iff [NeZero n] {a : Fin n} : 0 < a.val ↔ 0 < a := by
  rw [← val_fin_lt, val_zero]

/--
The `Fin.pos_iff_ne_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
/-
**Fin.pos_iff_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a != 0
参数：a : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_pos_iff`：val_pos_iff [NeZero n] {a : Fin n} : 0 < a.val ↔ 0 < a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Fin.val_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, ↑a ≠ 0 ↔ a
 ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `Fin.pos_iff_ne_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← val_pos_iff, Nat.pos_iff_ne_zero, val_ne_zero_iff]
/-
**Fin.cast_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (a : Fin n), Fin.cast ⋯ a = a
参数：a : Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma cast_eq_self (a : Fin n) : a.cast rfl = a := rfl
/-
**Fin.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {k l : ℕ} [inst : NeZero k] [inst_1 : NeZero l] (h : k = l) (x : Fin k),
 Fin.cast h x = 0 ↔ x = 0
参数：h : k = l；x : Fin k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem cast_eq_zero {k l : ℕ} [NeZero k] [NeZero l]
    (h : k = l) (x : Fin k) : Fin.cast h x = 0 ↔ x = 0 := by
  simp [← val_eq_zero_iff]
/-
**Fin.cast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：cast_injective {k l : Nat} (h : k = l) : Injective (Fin.cast h)
参数：h : k = l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_injective {k l : ℕ} (h : k = l) : Injective (Fin.cast h) :=
  fun a b hab ↦ by simpa [← val_eq_val] using hab
/-
**Fin.last_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：last_pos' [NeZero n] : 0 < last n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
-/
theorem last_pos' [NeZero n] : 0 < last n := n.pos_of_neZero
/-
**Fin.one_lt_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：one_lt_last [NeZero n] : 1 < last (n + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.val_one`：∀ (n : ℕ), ↑1 = 1
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `Nat.lt_add_left_iff_pos`：∀ {n k : ℕ}, n < k + n ↔ 0 < k
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem one_lt_last [NeZero n] : 1 < last (n + 1) := by
  rw [lt_def, val_one, val_last, Nat.lt_add_left_iff_pos, Nat.pos_iff_ne_zero]
  exact NeZero.ne n

end Order

/-! ### Coercions to `ℤ` and the `fin_omega` tactic. -/

open Int

/-
**Fin.coe_int_sub_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_int_sub_eq_ite {n : Nat} (u v : Fin n) : ((u - v : Fin n) : Int) = if 
v <= u then (u - v : Int) else (u - v : Int) + n
参数：u v : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sub_def`：∀ {n : ℕ} (a b : Fin n), a - b = ⟨(n - ↑b + ↑a) % n, ⋯⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Int.natCast_emod`：∀ (m n : ℕ), ↑(m % n) = ↑m % ↑n
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Int.emod_eq_sub_self_emod`：emod_eq_sub_self_emod {a b : Int} : a % b = (
a - b) % b
-/
theorem coe_int_sub_eq_ite {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = if v ≤ u then (u - v : Int) else (u - v : Int) + n := by
  rw [Fin.sub_def]
  split
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega
/-
**Fin.coe_int_sub_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_int_sub_eq_mod {n : Nat} (u v : Fin n) : ((u - v : Fin n) : Int) = ((u
 : Int) - (v : Int)) % n
参数：u v : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_int_sub_eq_ite`：coe_int_sub_eq_ite {n : Nat} (u v : Fin n) : ((u
 - v : Fin n) : Int) = if v <= u then (u - v : Int) else (u - v : Int) + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Int.emod_eq_add_self_emod`：∀ {a b : ℤ}, a % b = (a + b) % b
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coe_int_sub_eq_mod {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = ((u : Int) - (v : Int)) % n := by
  rw [coe_int_sub_eq_ite]
  split
  · rw [Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega
/-
**Fin.coe_int_add_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_int_add_eq_ite {n : Nat} (u v : Fin n) : ((u + v : Fin n) : Int) = if 
(u + v : Nat) < n then (u + v : Int) else (u + v : Int) - n
参数：u v : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.add_def`：∀ {n : ℕ} (a b : Fin n), a + b = ⟨(↑a + ↑b) % n, ⋯⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Int.natCast_emod`：∀ (m n : ℕ), ↑(m % n) = ↑m % ↑n
· 使用定理 `Int.emod_eq_sub_self_emod`：emod_eq_sub_self_emod {a b : Int} : a % b = (
a - b) % b
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coe_int_add_eq_ite {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = if (u + v : ℕ) < n then (u + v : Int) else (u + v : Int) - n := by
  rw [Fin.add_def]
  split
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> lia
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> lia
/-
**Fin.coe_int_add_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_int_add_eq_mod {n : Nat} (u v : Fin n) : ((u + v : Fin n) : Int) = ((u
 : Int) + (v : Int)) % n
参数：u v : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem coe_int_add_eq_mod {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = ((u : Int) + (v : Int)) % n := by
  omega

-- Write `a + b` as `if (a + b : ℕ) < n then (a + b : ℤ) else (a + b : ℤ) - n` and
-- similarly `a - b` as `if (b : ℕ) ≤ a then (a - b : ℤ) else (a - b : ℤ) + n`.
attribute [fin_omega] coe_int_sub_eq_ite coe_int_add_eq_ite

-- Rewrite inequalities in `Fin` to inequalities in `ℕ`
attribute [fin_omega] Fin.lt_iff_val_lt_val Fin.le_iff_val_le_val

-- Rewrite `1 : Fin (n + 2)` to `1 : ℤ`
attribute [fin_omega] val_one

/--
`fin_omega` is a preprocessor for `omega` to handle inequalities in `Fin`.
It rewrites all hypotheses and the goal, turning statements about addition, subtraction and
inequalities in `Fin n` into statements that `omega` can use/solve.
Note that this involves a lot of case splitting, so may be slow.
-/
-- Further adjustment to the simp set can probably make this more powerful.
-- Please experiment and PR updates!
macro "fin_omega" : tactic => `(tactic|
  { try simp only [fin_omega, ← Int.ofNat_lt, ← Int.ofNat_le] at *
    omega })

section Add

/-!
### addition, numerals, and coercion from Nat
-/

/-
**Fin.val_one'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_one' (n : Nat) [NeZero n] : ((1 : Fin n) : Nat) = 1 % n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### addition, numerals, and coercion from Nat
-/
theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl
/-
**Fin.nontrivial_iff_two_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  simp [← not_subsingleton_iff_nontrivial, subsingleton_iff_le_one]; lia
/-
**Fin.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instNontrivial [n.AtLeastTwo] : Nontrivial (Fin n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.nontrivial_iff_two_le`：nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 
2 <= n
· 使用引理 `Nat.AtLeastTwo.one_lt`：one_lt : 1 < n
-/
instance instNontrivial [n.AtLeastTwo] : Nontrivial (Fin n) :=
  nontrivial_iff_two_le.2 Nat.AtLeastTwo.one_lt

/-- If working with more than two elements, we can always pick a third distinct from two existing
elements. -/
/-
**Fin.exists_ne_and_ne_of_two_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_ne_and_ne_of_two_lt (i j : Fin n) (h : 2 < n) : exists k, k != i ∧ 
k != j
参数：i j : Fin n；h : 2 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
If working with more than two elements, we can always pick a third distinct from
 two existing
elements.
-/
theorem exists_ne_and_ne_of_two_lt (i j : Fin n) (h : 2 < n) : ∃ k, k ≠ i ∧ k ≠ j := by
  have : NeZero n := ⟨by lia⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 ≠ i ∧ 0 ≠ j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
    · exact ⟨⟨1, by lia⟩, h1⟩
    · refine ⟨⟨2, by lia⟩, ?_⟩
      dsimp only
      lia

section Monoid

/-
**Fin.inhabitedFinOneAdd** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：inhabitedFinOneAdd (n : Nat) : Inhabited (Fin (1 + n))
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Fin (1 + n)) :=
  haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]
/-
**Fin.default_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：default_eq_zero (n : Nat) [NeZero n] : (default : Fin n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_eq_zero (n : ℕ) [NeZero n] : (default : Fin n) = 0 :=
  rfl

end Monoid

/-
**Fin.val_add_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_add_eq_ite {n : Nat} (a b : Fin n) : (↑(a + b) : Nat) = if n <= a + b 
then a + b - n else a + b
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
· 使用定理 `Nat.add_mod_eq_ite`：∀ {k m n : ℕ}, (m + n) % k = if k ≤ m % k + n % k th
en m % k + n % k - k else m % k + n % k
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem val_add_eq_ite {n : ℕ} (a b : Fin n) :
    (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2),
    Nat.mod_eq_of_lt (show ↑b < n from b.2)]
/-
**Fin.val_add_eq_of_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_add_eq_of_add_lt {n : Nat} {a b : Fin n} (huv : a.val + b.val < n) : (
a + b).val = a.val + b.val
参数：huv : a.val + b.val < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem val_add_eq_of_add_lt {n : ℕ} {a b : Fin n} (huv : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [val_add]
  simp [Nat.mod_eq_of_lt huv]
/-
**Fin.intCast_val_sub_eq_sub_add_ite** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：intCast_val_sub_eq_sub_add_ite {n : Nat} (a b : Fin n) : ((a - b).val : In
t) = a.val - b.val + if b <= a then 0 else n
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.coe_int_sub_eq_ite`：coe_int_sub_eq_ite {n : Nat} (u v : Fin n) : ((u
 - v : Fin n) : Int) = if v <= u then (u - v : Int) else (u - v : Int) + n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma intCast_val_sub_eq_sub_add_ite {n : ℕ} (a b : Fin n) :
    ((a - b).val : ℤ) = a.val - b.val + if b ≤ a then 0 else n := by
  split <;> fin_omega
/-
**Fin.sub_val_lt_sub** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j) : (j - i).val < n - 
i.val
参数：hij : i <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.sub_lt_sub_right`：∀ {a b c : ℕ}, c ≤ a → a < b → a - c < b - c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma sub_val_lt_sub {n : ℕ} {i j : Fin n} (hij : i ≤ j) : (j - i).val < n - i.val := by
  simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]
/-
**Fin.castLT_sub_nezero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castLT_sub_nezero {n : Nat} {i j : Fin n} (hij : i < j) : haveI : NeZero (
n - i.1)
参数：hij : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `Fin.ne_of_val_ne`：∀ {n : ℕ} {i j : Fin n}, ↑i ≠ ↑j → i ≠ j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_sub_iff_le`：∀ {n : ℕ} {a b : Fin n}, ↑(a - b) = ↑a - ↑b ↔ b ≤ a
-/
lemma castLT_sub_nezero {n : ℕ} {i j : Fin n} (hij : i < j) :
    haveI : NeZero (n - i.1) := neZero_iff.mpr (by lia)
    (j - i).castLT (sub_val_lt_sub (Fin.le_of_lt hij)) ≠ 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simp [coe_sub_iff_le.mpr (Fin.le_of_lt hij)]
  lia
/-
**Fin.one_le_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：one_le_of_ne_zero {n : Nat} {k : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.le_iff_val_le_val`：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : N
at) <= b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.val_one`：∀ (n : ℕ), ↑1 = 1
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Fin.val_ne_zero_iff`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, ↑a ≠ 0 ↔ a
 ≠ 0
-/
lemma one_le_of_ne_zero {n : ℕ} {k : Fin n} :
    haveI := k.neZero
    (hk : k ≠ 0) → 1 ≤ k := by
  have : NeZero n := k.neZero
  intro hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  cases n with
  | zero => simp only [Fin.isValue, Fin.zero_le]
  | succ n => rwa [Fin.le_iff_val_le_val, Fin.val_one, Nat.one_le_iff_ne_zero, val_ne_zero_iff]
/-
**Fin.val_sub_one_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：val_sub_one_of_ne_zero {i : Fin n} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用引理 `Fin.one_le_of_ne_zero`：one_le_of_ne_zero {n : Nat} {k : Fin n} : haveI
· 使用定理 `Fin.val_one'`：val_one' (n : Nat) [NeZero n] : ((1 : Fin n) : Nat) = 1 % 
n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.nontrivial_iff_two_le`：nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 
2 <= n
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma val_sub_one_of_ne_zero {i : Fin n} :
    haveI := i.neZero
    (hi : i ≠ 0) → (i - 1).val = i - 1 := by
  have := i.neZero
  intro hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sub_val_of_le (one_le_of_ne_zero hi), Fin.val_one', Nat.mod_eq_of_lt
    (Nat.succ_le_iff.mpr (nontrivial_iff_two_le.mp <| nontrivial_of_ne i 0 hi))]

section OfNatCoe

-- We allow the coercion from `Nat` to `Fin` in this section.
open Fin.NatCast

@[simp]
/-
**Fin.ofNat_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：ofNat_eq_cast (n : Nat) [NeZero n] (a : Nat) : Fin.ofNat n a = (a : Fin n)
参数：n : Nat；a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_eq_cast (n : ℕ) [NeZero n] (a : ℕ) : Fin.ofNat n a = (a : Fin n) :=
  rfl
/-
**Fin.val_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (a n : ℕ) [inst : NeZero n], ↑↑a = a % n
参数：a n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_natCast (a n : ℕ) [NeZero n] : (a : Fin n).val = a % n := rfl

/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number. -/
/-
**Fin.val_cast_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a < n) : (a : Fin n).va
l = a
参数：h : a < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a

--- 原说明 ---
Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number.
-/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h

/-- Converting the value of a `Fin n` to `Fin n` results in the same value. -/
/-
**Fin.cast_val_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (a : Fin n), ↑↑a = a
参数：a : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Fin.val_cast_of_lt`：val_cast_of_lt {n : Nat} [NeZero n] {a : Nat} (h : a
 < n) : (a : Fin n).val = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n

--- 原说明 ---
Converting the value of a `Fin n` to `Fin n` results in the same value.
-/
@[simp, norm_cast] theorem cast_val_eq_self {n : ℕ} (a : Fin n) :
    haveI := a.neZero
    (a.val : Fin n) = a :=
  have := a.neZero
  Fin.ext <| val_cast_of_lt a.isLt

-- This is a special case of `CharP.cast_eq_zero` that doesn't require typeclass search
/-
**Fin.natCast_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ) [inst : NeZero n], ↑n = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp high] lemma natCast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp
/-
**Fin.natCast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {a n : ℕ} [inst : NeZero n], ↑a = 0 ↔ n ∣ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma natCast_eq_zero {a n : ℕ} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]
/-
**Fin.natCast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n], ↑0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma natCast_zero {n : ℕ} [NeZero n] : ((0 : ℕ) : Fin n) = 0 := by
  simp

@[simp]
/-
**Fin.natCast_eq_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp
/-
**Fin.natCast_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natCast_eq_mk {m n : Nat} (h : m < n) : have : NeZero n
参数：h : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Fin.val_inj`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b ↔ a = b
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem natCast_eq_mk {m n : ℕ} (h : m < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)
/-
**Fin.one_eq_mk_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：one_eq_mk_of_lt {n : Nat} (h : 1 < n) : have : NeZero n
参数：h : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Fin.val_inj`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b ↔ a = b
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem one_eq_mk_of_lt {n : ℕ} (h : 1 < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)
/-
**Fin.le_val_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_val_last (i : Fin (n + 1)) : i <= n
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.natCast_eq_last`：natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last 
n
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
-/
theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i

variable {a b : ℕ}
/-
**Fin.natCast_le_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：natCast_le_natCast (han : a <= n) (hbn : b <= n) : (a : Fin (n + 1)) <= b 
↔ a <= b
参数：han : a <= n；hbn : b <= n。
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
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_le_natCast (han : a ≤ n) (hbn : b ≤ n) : (a : Fin (n + 1)) ≤ b ↔ a ≤ b := by
  rw [← Nat.lt_succ_iff] at han hbn
  simp [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, han, hbn]
/-
**Fin.natCast_lt_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：natCast_lt_natCast (han : a <= n) (hbn : b <= n) : (a : Fin (n + 1)) < b ↔
 a < b
参数：han : a <= n；hbn : b <= n。
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
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_lt_natCast (han : a ≤ n) (hbn : b ≤ n) : (a : Fin (n + 1)) < b ↔ a < b := by
  rw [← Nat.lt_succ_iff] at han hbn; simp [lt_def, Nat.mod_eq_of_lt, han, hbn]
/-
**Fin.natCast_mono** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：natCast_mono (hbn : b <= n) (hab : a <= b) : (a : Fin (n + 1)) <= b
参数：hbn : b <= n；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.natCast_le_natCast`：natCast_le_natCast (han : a <= n) (hbn : b <= n)
 : (a : Fin (n + 1)) <= b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma natCast_mono (hbn : b ≤ n) (hab : a ≤ b) : (a : Fin (n + 1)) ≤ b :=
  (natCast_le_natCast (hab.trans hbn) hbn).2 hab
/-
**Fin.natCast_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：natCast_strictMono (hbn : b <= n) (hab : a < b) : (a : Fin (n + 1)) < b
参数：hbn : b <= n；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.natCast_lt_natCast`：natCast_lt_natCast (han : a <= n) (hbn : b <= n)
 : (a : Fin (n + 1)) < b ↔ a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma natCast_strictMono (hbn : b ≤ n) (hab : a < b) : (a : Fin (n + 1)) < b :=
  (natCast_lt_natCast (hab.le.trans hbn) hbn).2 hab

@[simp]
/-
**Fin.castLE_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castLE_natCast {m n : Nat} [NeZero m] (h : m <= n) (a : Nat) : haveI : NeZ
ero n
参数：h : m <= n；a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
-/
lemma castLE_natCast {m n : ℕ} [NeZero m] (h : m ≤ n) (a : ℕ) :
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le m.pos_of_neZero h)⟩
    Fin.castLE h (a.cast : Fin m) = (a % m : ℕ) := by
  ext
  simp only [val_castLE, val_natCast]
  rw [Nat.mod_eq_of_lt (a := a % m) (lt_of_lt_of_le (Nat.mod_lt _ m.pos_of_neZero) h)]

end OfNatCoe

end Add

section DivMod

/-
**Fin.modNat_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.rev
参数：i : Fin (m * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_add_mod'`：∀ (a b : ℕ), a / b * b + a % b = a
· 使用定理 `Nat.mul_sub_right_distrib`：∀ (n m k : ℕ), (n - m) * k = n * k - m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.sub_add_sub_cancel`：∀ {a b c : ℕ}, b ≤ a → c ≤ b → a - b + (b - c) =
 a - c
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `Nat.le_sub_of_add_le'`：∀ {n k m : ℕ}, m + n ≤ k → n ≤ k - m
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_add_mod`：∀ (m x y : ℕ), (m * x + y) % m = y % m
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.rev := by
  ext
  have H₁ : i % n + 1 ≤ n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [val_rev]
  calc
    (m * n - (i + 1)) % n = (m * n - ((i / n) * n + i % n + 1)) % n := by rw [Nat.div_add_mod']
    _ = ((m - i / n - 1) * n + (n - (i % n + 1))) % n := by
      rw [Nat.mul_sub_right_distrib, Nat.one_mul, Nat.sub_add_sub_cancel _ H₁,
        Nat.mul_sub_right_distrib, Nat.sub_sub, Nat.add_assoc]
      exact Nat.le_mul_of_pos_left _ <| Nat.le_sub_of_add_le' H₂
    _ = n - (i % n + 1) := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt]; exact i.modNat.rev.is_lt

end DivMod

section Rec

/-!
### recursion and induction principles
-/

@[elab_as_elim]
/-
**Fin.strong_induction_on** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strong_induction_on {n : Nat} {motive : Fin n -> Prop} (h : forall (j : Fi
n n) (_ : forall (k : Fin n), k < j -> motive k), motive j) (i : Fin n) : motive
 i
参数：h : forall (j : Fin n) (_ : forall (k : Fin n), k < j -> motive k), motive j；
i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n

--- 原说明 ---
### recursion and induction principles
-/
lemma strong_induction_on {n : ℕ} {motive : Fin n → Prop}
    (h : ∀ (j : Fin n) (_ : ∀ (k : Fin n), k < j → motive k), motive j) (i : Fin n) :
    motive i := by
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | h j hj => exact h _ (fun ⟨k, hk₁⟩ hk₂ ↦ hj _ hk₂ hk₁)

end Rec

open scoped Relator in
/-
**Fin.liftFun_iff_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (
n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (f (castSucc i)) (f i.suc
c)
参数：r : α -> α -> Prop；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.le_def`：∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ ↑a ≤ ↑b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem liftFun_iff_succ {α : Type*} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h ↦ ?_) ?_
    · simp at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · exact _root_.trans (ihj hij) (H j)

section AddGroup

/-
**Fin.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：eq_zero (n : Fin 1) : n = 0
参数：n : Fin 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem eq_zero (n : Fin 1) : n = 0 := Subsingleton.elim _ _
/-
**Fin.eq_one_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：eq_one_of_ne_zero (i : Fin 2) (hi : i != 0) : i = 1
参数：i : Fin 2；hi : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma eq_one_of_ne_zero (i : Fin 2) (hi : i ≠ 0) : i = 1 := by lia

@[simp]
/-
**Fin.coe_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_neg_one : ↑(-1 : Fin (n + 1)) = n
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
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_neg'`：∀ {n : ℕ} (a : Fin n), ↑(-a) = (n - ↑a) % n
· 使用定理 `Fin.val_one`：∀ (n : ℕ), ↑1 = 1
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.val_neg', Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt]
  constructor
/-
**Fin.last_sub** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.coe_sub_iff_le`：∀ {n : ℕ} {a b : Fin n}, ↑(a - b) = ↑a - ↑b ↔ b ≤ a
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `Fin.val_rev`：∀ {n : ℕ} (i : Fin n), ↑i.rev = n - (↑i + 1)
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
-/
theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  Fin.ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]
/-
**Fin.add_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：add_one_le_of_lt {n : Nat} {a b : Fin (n + 1)} (h : a < b) : a + 1 <= b
参数：n + 1；h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_int_add_eq_ite`：coe_int_add_eq_ite {n : Nat} (u v : Fin n) : ((u
 + v : Fin n) : Int) = if (u + v : Nat) < n then (u + v : Int) else (u + v : Int
) - n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
-/
theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b := by
  cases n <;> fin_omega
/-
**Fin.exists_eq_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_eq_add_of_le {n : Nat} {a b : Fin n} (h : a <= b) : exists k <= b, 
b = a + k
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_eq_add_of_le {n : ℕ} {a b : Fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k ≤ b := by lia
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]
/-
**Fin.exists_eq_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_eq_add_of_lt {n : Nat} {a b : Fin (n + 1)} (h : a < b) : exists k <
 b, k + 1 <= b ∧ b = a + k + 1
参数：n + 1；h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_int_add_eq_ite`：coe_int_add_eq_ite {n : Nat} (u v : Fin n) : ((u
 + v : Fin n) : Int) = if (u + v : Nat) < n then (u + v : Int) else (u + v : Int
) - n
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_eq_add_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) :
    ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := by
  cases n
  · lia
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by lia
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]
/-
**Fin.pos_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：pos_of_ne_zero {n : Nat} {a : Fin (n + 1)} (h : a != 0) : 0 < a
参数：n + 1；h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Fin.val_ne_of_ne`：∀ {n : ℕ} {i j : Fin n}, i ≠ j → ↑i ≠ ↑j
-/
lemma pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) : 0 < a :=
  Nat.pos_of_ne_zero (val_ne_of_ne h)
/-
**Fin.sub_succ_le_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sub_succ_le_sub_of_le {n : Nat} {u v : Fin (n + 2)} (h : u < v) : v - (u +
 1) < v - u
参数：n + 2；h : u < v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_int_sub_eq_ite`：coe_int_sub_eq_ite {n : Nat} (u v : Fin n) : ((u
 - v : Fin n) : Int) = if v <= u then (u - v : Int) else (u - v : Int) + n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.coe_int_add_eq_ite`：coe_int_add_eq_ite {n : Nat} (u v : Fin n) : ((u
 + v : Fin n) : Int) = if (u + v : Nat) < n then (u + v : Int) else (u + v : Int
) - n
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma sub_succ_le_sub_of_le {n : ℕ} {u v : Fin (n + 2)} (h : u < v) : v - (u + 1) < v - u := by
  fin_omega

end AddGroup

open Fin.NatCast in
@[simp]
/-
**Fin.coe_natCast_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_natCast_eq_mod (m n : Nat) [NeZero m] : ((n : Fin m) : Nat) = n % m
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast_eq_mod (m n : ℕ) [NeZero m] :
    ((n : Fin m) : ℕ) = n % m :=
  rfl

@[simp]
/-
**Fin.coe_ofNat_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_ofNat_eq_mod (m n : Nat) [NeZero m] : ((ofNat(n) : Fin m) : Nat) = ofN
at(n) % m
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((ofNat(n) : Fin m) : ℕ) = ofNat(n) % m :=
  rfl
/-
**Fin.val_add_one_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_add_one_of_lt' {n : Nat} {i : Fin n} (h : i + 1 < n) : haveI
参数：h : i + 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
theorem val_add_one_of_lt' {n : ℕ} {i : Fin n} (h : i + 1 < n) :
    haveI := i.neZero
    (i + 1).val = i.val + 1 := by
  simpa [add_def] using Nat.mod_eq_of_lt (by lia)
/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NeZero n] [NeZero ofNat(m)] : NeZero (ofNat(m) : Fin (n + ofNat(m))) := by
  suffices m % (n + m) = m by simpa [neZero_iff, Fin.ext_iff, OfNat.ofNat, this] using! NeZero.ne m
  apply Nat.mod_eq_of_lt
  simpa using! zero_lt_of_ne_zero (NeZero.ne n)

section Mul

/-!
### mul
-/

end Mul

end Fin

