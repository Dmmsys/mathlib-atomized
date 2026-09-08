/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `emultiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity a b`: a `ℕ`-valued version of `multiplicity`, defaulting for `1` instead of `⊤`.
  The reason for using `1` as a default value instead of `0` is to have `multiplicity_eq_zero_iff`.
* `FiniteMultiplicity a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/

@[expose] public section

assert_not_exists Field

variable {α β : Type*}

open Nat

/-- `FiniteMultiplicity a b` indicates that the multiplicity of `a` in `b` is finite. -/
/-
**FiniteMultiplicity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FiniteMultiplicity [Monoid α] (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FiniteMultiplicity a b` indicates that the multiplicity of `a` in `b` is finite
.
-/
abbrev FiniteMultiplicity [Monoid α] (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

open scoped Classical in
/-- `emultiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `ℕ∞`. If `∀ n, a ^ n ∣ b` then it returns `⊤`. -/
/-
**emultiplicity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：emultiplicity [Monoid α] (a b : α) : Nat∞
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`emultiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `ℕ∞`. If `∀ n, a ^ n ∣ b` then it returns `⊤`.
-/
noncomputable def emultiplicity [Monoid α] (a b : α) : ℕ∞ :=
  if h : FiniteMultiplicity a b then Nat.find h else ⊤

/-- A `ℕ`-valued version of `emultiplicity`, returning `1` instead of `⊤`. -/
/-
**multiplicity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multiplicity [Monoid α] (a b : α) : Nat
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ℕ`-valued version of `emultiplicity`, returning `1` instead of `⊤`.
-/
noncomputable def multiplicity [Monoid α] (a b : α) : ℕ :=
  (emultiplicity a b).untopD 1

section Monoid

variable [Monoid α] [Monoid β] {a b : α}

@[simp]
/-
**emultiplicity_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬FiniteMultiplicity a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem emultiplicity_eq_top :
    emultiplicity a b = ⊤ ↔ ¬FiniteMultiplicity a b := by
  simp [emultiplicity]
/-
**emultiplicity_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_lt_top {a b : α} : emultiplicity a b < ⊤ ↔ FiniteMultiplicit
y a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem emultiplicity_lt_top {a b : α} : emultiplicity a b < ⊤ ↔ FiniteMultiplicity a b := by
  simp [lt_top_iff_ne_top, emultiplicity_eq_top]
/-
**finiteMultiplicity_iff_emultiplicity_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finiteMultiplicity_iff_emultiplicity_ne_top : FiniteMultiplicity a b ↔ emu
ltiplicity a b != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finiteMultiplicity_iff_emultiplicity_ne_top :
    FiniteMultiplicity a b ↔ emultiplicity a b ≠ ⊤ := by simp
/-
**finiteMultiplicity_of_emultiplicity_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finiteMultiplicity_of_emultiplicity_eq_natCast {n : Nat} (h : emultiplicit
y a b = n) : FiniteMultiplicity a b
参数：h : emultiplicity a b = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
-/
theorem finiteMultiplicity_of_emultiplicity_eq_natCast {n : ℕ} (h : emultiplicity a b = n) :
    FiniteMultiplicity a b := by
  by_contra nh
  rw [← emultiplicity_eq_top, h] at nh
  trivial
/-
**multiplicity_eq_of_emultiplicity_eq_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_of_emultiplicity_eq_some {n : Nat} (h : emultiplicity a b 
= n) : multiplicity a b = n
参数：h : emultiplicity a b = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem multiplicity_eq_of_emultiplicity_eq_some {n : ℕ} (h : emultiplicity a b = n) :
    multiplicity a b = n := by
  simp [multiplicity, h]
  rfl
/-
**emultiplicity_ne_of_multiplicity_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_ne_of_multiplicity_ne {n : Nat} : multiplicity a b != n -> e
multiplicity a b != n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
-/
theorem emultiplicity_ne_of_multiplicity_ne {n : ℕ} :
    multiplicity a b ≠ n → emultiplicity a b ≠ n :=
  mt multiplicity_eq_of_emultiplicity_eq_some
/-
**FiniteMultiplicity.emultiplicity_eq_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.emultiplicity_eq_multiplicity (h : FiniteMultiplicity a
 b) : emultiplicity a b = multiplicity a b
参数：h : FiniteMultiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
-/
theorem FiniteMultiplicity.emultiplicity_eq_multiplicity (h : FiniteMultiplicity a b) :
    emultiplicity a b = multiplicity a b := by
  cases hm : emultiplicity a b
  · simp [h] at hm
  rw [multiplicity_eq_of_emultiplicity_eq_some hm]
/-
**FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq {n : Nat} (h : Fin
iteMultiplicity a b) : emultiplicity a b = n ↔ multiplicity a b = n
参数：h : FiniteMultiplicity a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq {n : ℕ}
    (h : FiniteMultiplicity a b) : emultiplicity a b = n ↔ multiplicity a b = n := by
  simp [h.emultiplicity_eq_multiplicity]

set_option backward.isDefEq.respectTransparency false in
/-
**emultiplicity_eq_iff_multiplicity_eq_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_iff_multiplicity_eq_of_ne_one {n : Nat} (h : n != 1) : em
ultiplicity a b = n ↔ multiplicity a b = n
参数：h : n != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem emultiplicity_eq_iff_multiplicity_eq_of_ne_one {n : ℕ} (h : n ≠ 1) :
    emultiplicity a b = n ↔ multiplicity a b = n := by
  constructor
  · exact multiplicity_eq_of_emultiplicity_eq_some
  · intro h₂
    simpa [multiplicity, WithTop.untopD_eq_iff, h] using! h₂
/-
**emultiplicity_eq_zero_iff_multiplicity_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_zero_iff_multiplicity_eq_zero : emultiplicity a b = 0 ↔ m
ultiplicity a b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_eq_iff_multiplicity_eq_of_ne_one`：emultiplicity_eq_iff_mul
tiplicity_eq_of_ne_one {n : Nat} (h : n != 1) : emultiplicity a b = n ↔ multipli
city a b = n
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem emultiplicity_eq_zero_iff_multiplicity_eq_zero :
    emultiplicity a b = 0 ↔ multiplicity a b = 0 :=
  emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one

@[simp]
/-
**multiplicity_eq_one_of_not_finiteMultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_one_of_not_finiteMultiplicity (h : ¬FiniteMultiplicity a b
) : multiplicity a b = 1
参数：h : ¬FiniteMultiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multiplicity.eq_1`：∀ {α : Type u_1} [inst : Monoid α] (a b : α), multipl
icity a b = WithTop.untopD 1 (emultiplicity a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem multiplicity_eq_one_of_not_finiteMultiplicity (h : ¬FiniteMultiplicity a b) :
    multiplicity a b = 1 := by
  rw [multiplicity, emultiplicity_eq_top.mpr h]
  decide

@[simp]
/-
**multiplicity_le_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_le_emultiplicity : multiplicity a b <= emultiplicity a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `multiplicity_eq_one_of_not_finiteMultiplicity`：multiplicity_eq_one_of_no
t_finiteMultiplicity (h : ¬FiniteMultiplicity a b) : multiplicity a b = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
-/
theorem multiplicity_le_emultiplicity :
    multiplicity a b ≤ emultiplicity a b := by
  by_cases hf : FiniteMultiplicity a b
  · simp [hf.emultiplicity_eq_multiplicity]
  · simp [hf, emultiplicity_eq_top.2]

-- Cannot be @[simp] because `β`, `c`, and `d` cannot be inferred by `simp`.
/-
**multiplicity_eq_of_emultiplicity_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_of_emultiplicity_eq {c d : β} (h : emultiplicity a b = emu
ltiplicity c d) : multiplicity a b = multiplicity c d
参数：h : emultiplicity a b = emultiplicity c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem multiplicity_eq_of_emultiplicity_eq {c d : β}
    (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = multiplicity c d := by
  unfold multiplicity
  rw [h]
/-
**multiplicity_le_of_emultiplicity_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_le_of_emultiplicity_le {n : Nat} (h : emultiplicity a b <= n)
 : multiplicity a b <= n
参数：h : emultiplicity a b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `multiplicity_le_emultiplicity`：multiplicity_le_emultiplicity : multiplic
ity a b <= emultiplicity a b
-/
theorem multiplicity_le_of_emultiplicity_le {n : ℕ} (h : emultiplicity a b ≤ n) :
    multiplicity a b ≤ n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans h
/-
**FiniteMultiplicity.emultiplicity_le_of_multiplicity_le** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：FiniteMultiplicity.emultiplicity_le_of_multiplicity_le (hfin : FiniteMulti
plicity a b) {n : Nat} (h : multiplicity a b <= n) : emultiplicity a b <= n
参数：hfin : FiniteMultiplicity a b；h : multiplicity a b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem FiniteMultiplicity.emultiplicity_le_of_multiplicity_le (hfin : FiniteMultiplicity a b)
    {n : ℕ} (h : multiplicity a b ≤ n) : emultiplicity a b ≤ n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast
/-
**le_emultiplicity_of_le_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_emultiplicity_of_le_multiplicity {n : Nat} (h : n <= multiplicity a b) 
: n <= emultiplicity a b
参数：h : n <= multiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `WithTop.coe_mono`：∀ {α : Type u_1} [inst : Preorder α], Monotone fun a =
> ↑a
· 使用定理 `multiplicity_le_emultiplicity`：multiplicity_le_emultiplicity : multiplic
ity a b <= emultiplicity a b
-/
theorem le_emultiplicity_of_le_multiplicity {n : ℕ} (h : n ≤ multiplicity a b) :
    n ≤ emultiplicity a b := by
  exact_mod_cast (WithTop.coe_mono h).trans multiplicity_le_emultiplicity
/-
**FiniteMultiplicity.le_multiplicity_of_le_emultiplicity** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：FiniteMultiplicity.le_multiplicity_of_le_emultiplicity (hfin : FiniteMulti
plicity a b) {n : Nat} (h : n <= emultiplicity a b) : n <= multiplicity a b
参数：hfin : FiniteMultiplicity a b；h : n <= emultiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
-/
theorem FiniteMultiplicity.le_multiplicity_of_le_emultiplicity (hfin : FiniteMultiplicity a b)
    {n : ℕ} (h : n ≤ emultiplicity a b) : n ≤ multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast
/-
**multiplicity_lt_of_emultiplicity_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_lt_of_emultiplicity_lt {n : Nat} (h : emultiplicity a b < n) 
: multiplicity a b < n
参数：h : emultiplicity a b < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `multiplicity_le_emultiplicity`：multiplicity_le_emultiplicity : multiplic
ity a b <= emultiplicity a b
-/
theorem multiplicity_lt_of_emultiplicity_lt {n : ℕ} (h : emultiplicity a b < n) :
    multiplicity a b < n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans_lt h
/-
**FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt (hfin : FiniteMulti
plicity a b) {n : Nat} (h : multiplicity a b < n) : emultiplicity a b < n
参数：hfin : FiniteMultiplicity a b；h : multiplicity a b < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem FiniteMultiplicity.emultiplicity_lt_of_multiplicity_lt (hfin : FiniteMultiplicity a b)
    {n : ℕ} (h : multiplicity a b < n) : emultiplicity a b < n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast
/-
**lt_emultiplicity_of_lt_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_emultiplicity_of_lt_multiplicity {n : Nat} (h : n < multiplicity a b) :
 n < emultiplicity a b
参数：h : n < multiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithTop.coe_strictMono`：∀ {α : Type u_1} [inst : Preorder α], StrictMono
 fun a => ↑a
· 使用定理 `multiplicity_le_emultiplicity`：multiplicity_le_emultiplicity : multiplic
ity a b <= emultiplicity a b
-/
theorem lt_emultiplicity_of_lt_multiplicity {n : ℕ} (h : n < multiplicity a b) :
    n < emultiplicity a b := by
  exact_mod_cast (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity
/-
**FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity (hfin : FiniteMulti
plicity a b) {n : Nat} (h : n < emultiplicity a b) : n < multiplicity a b
参数：hfin : FiniteMultiplicity a b；h : n < emultiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
-/
theorem FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity (hfin : FiniteMultiplicity a b)
    {n : ℕ} (h : n < emultiplicity a b) : n < multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast
/-
**emultiplicity_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pos_iff : 0 < emultiplicity a b ↔ 0 < multiplicity a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem emultiplicity_pos_iff :
    0 < emultiplicity a b ↔ 0 < multiplicity a b := by
  simp [pos_iff_ne_zero, pos_iff_ne_zero, emultiplicity_eq_zero_iff_multiplicity_eq_zero]
/-
**FiniteMultiplicity.def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.def : FiniteMultiplicity a b ↔ exists n : Nat, ¬a ^ (n 
+ 1) ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem FiniteMultiplicity.def : FiniteMultiplicity a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl
/-
**FiniteMultiplicity.not_dvd_of_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_dvd_of_one_right : FiniteMultiplicity a 1 -> ¬a ∣ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul_pow_eq_one`：∀ {M : Type u_4} [inst : Monoid M] {a b : M} (n : ℕ)
, a * b = 1 → a ^ n * b ^ n = 1
-/
theorem FiniteMultiplicity.not_dvd_of_one_right : FiniteMultiplicity a 1 → ¬a ∣ 1 :=
  fun ⟨n, hn⟩ ⟨d, hd⟩ => hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]
/-
**Int.natCast_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.natCast_emultiplicity (a b : Nat) : emultiplicity (a : Int) (b : Int) 
= emultiplicity a b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem Int.natCast_emultiplicity (a b : ℕ) :
    emultiplicity (a : ℤ) (b : ℤ) = emultiplicity a b := by
  unfold emultiplicity FiniteMultiplicity
  congr! <;> norm_cast

@[norm_cast]
/-
**Int.natCast_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.natCast_multiplicity (a b : Nat) : multiplicity (a : Int) (b : Int) = 
multiplicity a b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `Int.natCast_emultiplicity`：Int.natCast_emultiplicity (a b : Nat) : emult
iplicity (a : Int) (b : Int) = emultiplicity a b
-/
theorem Int.natCast_multiplicity (a b : ℕ) : multiplicity (a : ℤ) (b : ℤ) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (natCast_emultiplicity a b)
/-
**FiniteMultiplicity.not_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_iff_forall : ¬FiniteMultiplicity a b ↔ forall n : N
at, a ^ n ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem FiniteMultiplicity.not_iff_forall : ¬FiniteMultiplicity a b ↔ ∀ n : ℕ, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [FiniteMultiplicity] using h),
    by simp [FiniteMultiplicity]; tauto⟩
/-
**FiniteMultiplicity.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_isUnit (h : FiniteMultiplicity a b) : ¬IsUnit a
参数：h : FiniteMultiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
theorem FiniteMultiplicity.not_isUnit (h : FiniteMultiplicity a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

@[deprecated (since := "2026-08-02")]
alias FiniteMultiplicity.not_unit := FiniteMultiplicity.not_isUnit
/-
**FiniteMultiplicity.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.mul_left {c : α} : FiniteMultiplicity a (b * c) -> Fini
teMultiplicity a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem FiniteMultiplicity.mul_left {c : α} :
    FiniteMultiplicity a (b * c) → FiniteMultiplicity a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩
/-
**pow_dvd_of_le_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_dvd_of_le_emultiplicity {k : Nat} (hk : k <= emultiplicity a b) : a ^ 
k ∣ b
参数：hk : k <= emultiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteMultiplicity.not_iff_forall`：FiniteMultiplicity.not_iff_forall : ¬
FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem pow_dvd_of_le_emultiplicity {k : ℕ} (hk : k ≤ emultiplicity a b) :
    a ^ k ∣ b := by classical
  cases k
  · simp
  unfold emultiplicity at hk
  split at hk
  · norm_cast at hk
    simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply FiniteMultiplicity.not_iff_forall.mp ‹_›
/-
**pow_dvd_of_le_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_dvd_of_le_multiplicity {k : Nat} (hk : k <= multiplicity a b) : a ^ k 
∣ b
参数：hk : k <= multiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用定理 `le_emultiplicity_of_le_multiplicity`：le_emultiplicity_of_le_multiplicity
 {n : Nat} (h : n <= multiplicity a b) : n <= emultiplicity a b
-/
theorem pow_dvd_of_le_multiplicity {k : ℕ} (hk : k ≤ multiplicity a b) :
    a ^ k ∣ b := pow_dvd_of_le_emultiplicity (le_emultiplicity_of_le_multiplicity hk)

@[simp]
/-
**pow_multiplicity_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity a b) ∣ b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_dvd_of_le_multiplicity`：pow_dvd_of_le_multiplicity {k : Nat} (hk : k
 <= multiplicity a b) : a ^ k ∣ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem pow_multiplicity_dvd (a b : α) : a ^ (multiplicity a b) ∣ b :=
  pow_dvd_of_le_multiplicity le_rfl
/-
**not_pow_dvd_of_emultiplicity_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_pow_dvd_of_emultiplicity_lt {m : Nat} (hm : emultiplicity a b < m) : ¬
a ^ m ∣ b
参数：hm : emultiplicity a b < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
-/
theorem not_pow_dvd_of_emultiplicity_lt {m : ℕ} (hm : emultiplicity a b < m) :
    ¬a ^ m ∣ b := fun nh => by
  unfold emultiplicity at hm
  split at hm
  · simp only [cast_lt, find_lt_iff] at hm
    obtain ⟨n, hn1, hn2⟩ := hm
    exact hn2 ((pow_dvd_pow _ hn1).trans nh)
  · simp at hm
/-
**FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity
 a b) {m : Nat} (hm : multiplicity a b < m) : ¬a ^ m ∣ b
参数：hf : FiniteMultiplicity a b；hm : multiplicity a b < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_pow_dvd_of_emultiplicity_lt`：not_pow_dvd_of_emultiplicity_lt {m : Na
t} (hm : emultiplicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : ℕ}
    (hm : multiplicity a b < m) : ¬a ^ m ∣ b := by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [hf.emultiplicity_eq_multiplicity]
  norm_cast
/-
**multiplicity_pos_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < multiplicity a b
参数：hdiv : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`：FiniteMultiplicity.no
t_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat} (hm : multi
plicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `multiplicity_eq_one_of_not_finiteMultiplicity`：multiplicity_eq_one_of_no
t_finiteMultiplicity (h : ¬FiniteMultiplicity a b) : multiplicity a b = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
-/
theorem multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < multiplicity a b := by
  refine Nat.pos_iff_ne_zero.2 fun h => ?_
  simpa [hdiv] using FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt
    (by by_contra! nh; simp [nh] at h) (lt_one_iff.mpr h)
/-
**emultiplicity_pos_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < emultiplicity a b
参数：hdiv : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_emultiplicity_of_lt_multiplicity`：lt_emultiplicity_of_lt_multiplicity
 {n : Nat} (h : n < multiplicity a b) : n < emultiplicity a b
· 使用定理 `multiplicity_pos_of_dvd`：multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < mu
ltiplicity a b
-/
theorem emultiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < emultiplicity a b :=
  lt_emultiplicity_of_lt_multiplicity (multiplicity_pos_of_dvd hdiv)
/-
**emultiplicity_eq_of_dvd_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_of_dvd_of_not_dvd {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a 
^ (k + 1) ∣ b) : emultiplicity a b = k
参数：hk : a ^ k ∣ b；hsucc : ¬a ^ (k + 1) ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
-/
theorem emultiplicity_eq_of_dvd_of_not_dvd {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    emultiplicity a b = k := by classical
  have : FiniteMultiplicity a b := ⟨k, hsucc⟩
  simp only [emultiplicity, this, ↓reduceDIte, Nat.cast_inj, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn ↦ (pow_dvd_pow _ hn).trans hk
/-
**multiplicity_eq_of_dvd_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_of_dvd_of_not_dvd {k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^
 (k + 1) ∣ b) : multiplicity a b = k
参数：hk : a ^ k ∣ b；hsucc : ¬a ^ (k + 1) ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `emultiplicity_eq_of_dvd_of_not_dvd`：emultiplicity_eq_of_dvd_of_not_dvd {
k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : emultiplicity a b = k
-/
theorem multiplicity_eq_of_dvd_of_not_dvd {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    multiplicity a b = k :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_of_dvd_of_not_dvd hk hsucc)
/-
**le_emultiplicity_of_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_emultiplicity_of_pow_dvd {k : Nat} (hk : a ^ k ∣ b) : k <= emultiplicit
y a b
参数：hk : a ^ k ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_pow_dvd_of_emultiplicity_lt`：not_pow_dvd_of_emultiplicity_lt {m : Na
t} (hm : emultiplicity a b < m) : ¬a ^ m ∣ b
-/
theorem le_emultiplicity_of_pow_dvd {k : ℕ} (hk : a ^ k ∣ b) :
    k ≤ emultiplicity a b :=
  le_of_not_gt fun hk' => not_pow_dvd_of_emultiplicity_lt hk' hk
/-
**FiniteMultiplicity.le_multiplicity_of_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.le_multiplicity_of_pow_dvd (hf : FiniteMultiplicity a b
) {k : Nat} (hk : a ^ k ∣ b) : k <= multiplicity a b
参数：hf : FiniteMultiplicity a b；hk : a ^ k ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.le_multiplicity_of_le_emultiplicity`：FiniteMultiplici
ty.le_multiplicity_of_le_emultiplicity (hfin : FiniteMultiplicity a b) {n : Nat}
 (h : n <= emultiplicity a b) : n <= multipl…
· 使用定理 `le_emultiplicity_of_pow_dvd`：le_emultiplicity_of_pow_dvd {k : Nat} (hk :
 a ^ k ∣ b) : k <= emultiplicity a b
-/
theorem FiniteMultiplicity.le_multiplicity_of_pow_dvd (hf : FiniteMultiplicity a b)
    {k : ℕ} (hk : a ^ k ∣ b) : k ≤ multiplicity a b :=
  hf.le_multiplicity_of_le_emultiplicity (le_emultiplicity_of_pow_dvd hk)
/-
**pow_dvd_iff_le_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_dvd_iff_le_emultiplicity {k : Nat} : a ^ k ∣ b ↔ k <= emultiplicity a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_emultiplicity_of_pow_dvd`：le_emultiplicity_of_pow_dvd {k : Nat} (hk :
 a ^ k ∣ b) : k <= emultiplicity a b
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
-/
theorem pow_dvd_iff_le_emultiplicity {k : ℕ} :
    a ^ k ∣ b ↔ k ≤ emultiplicity a b :=
  ⟨le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity⟩
/-
**FiniteMultiplicity.pow_dvd_iff_le_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.pow_dvd_iff_le_multiplicity (hf : FiniteMultiplicity a 
b) {k : Nat} : a ^ k ∣ b ↔ k <= multiplicity a b
参数：hf : FiniteMultiplicity a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
-/
theorem FiniteMultiplicity.pow_dvd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : ℕ} :
    a ^ k ∣ b ↔ k ≤ multiplicity a b := by
  exact_mod_cast hf.emultiplicity_eq_multiplicity ▸ pow_dvd_iff_le_emultiplicity
/-
**emultiplicity_lt_iff_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_lt_iff_not_dvd {k : Nat} : emultiplicity a b < k ↔ ¬a ^ k ∣ 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem emultiplicity_lt_iff_not_dvd {k : ℕ} :
    emultiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_emultiplicity, not_le]
/-
**FiniteMultiplicity.multiplicity_lt_iff_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.multiplicity_lt_iff_not_dvd {k : Nat} (hf : FiniteMulti
plicity a b) : multiplicity a b < k ↔ ¬a ^ k ∣ b
参数：hf : FiniteMultiplicity a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`：FiniteMultiplicity.pow_d
vd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : Nat} : a ^ k ∣ b ↔ k <
= multiplicity a b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem FiniteMultiplicity.multiplicity_lt_iff_not_dvd {k : ℕ} (hf : FiniteMultiplicity a b) :
    multiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [hf.pow_dvd_iff_le_multiplicity, not_le]
/-
**emultiplicity_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_coe {n : Nat} : emultiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ 
(n + 1) ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_pow_dvd_of_emultiplicity_lt`：not_pow_dvd_of_emultiplicity_lt {m : Na
t} (hm : emultiplicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `emultiplicity_eq_of_dvd_of_not_dvd`：emultiplicity_eq_of_dvd_of_not_dvd {
k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : emultiplicity a b = k
-/
theorem emultiplicity_eq_coe {n : ℕ} :
    emultiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  constructor
  · intro h
    constructor
    · apply pow_dvd_of_le_emultiplicity
      simp [h]
    · apply not_pow_dvd_of_emultiplicity_lt
      rw [h]
      norm_cast
      simp
  · rw [and_imp]
    apply emultiplicity_eq_of_dvd_of_not_dvd
/-
**FiniteMultiplicity.multiplicity_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.multiplicity_eq_iff (hf : FiniteMultiplicity a b) {n : 
Nat} : multiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
参数：hf : FiniteMultiplicity a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem FiniteMultiplicity.multiplicity_eq_iff (hf : FiniteMultiplicity a b) {n : ℕ} :
    multiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  simp [← emultiplicity_eq_coe, hf.emultiplicity_eq_multiplicity]
/-
**emultiplicity_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_ofNat {a b n : Nat} [n.AtLeastTwo] : emultiplicity a b = 
(ofNat(n) : Nat∞) ↔ a ^ ofNat(n) ∣ b ∧ ¬a ^ (ofNat(n) + 1) ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
-/
theorem emultiplicity_eq_ofNat {a b n : ℕ} [n.AtLeastTwo] :
    emultiplicity a b = (ofNat(n) : ℕ∞) ↔ a ^ ofNat(n) ∣ b ∧ ¬a ^ (ofNat(n) + 1) ∣ b :=
  emultiplicity_eq_coe

@[simp]
/-
**FiniteMultiplicity.not_of_isUnit_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_of_isUnit_left (b : α) (ha : IsUnit a) : ¬FiniteMul
tiplicity a b
参数：b : α；ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.not_isUnit`：FiniteMultiplicity.not_isUnit (h : Finite
Multiplicity a b) : ¬IsUnit a
-/
theorem FiniteMultiplicity.not_of_isUnit_left (b : α) (ha : IsUnit a) : ¬FiniteMultiplicity a b :=
  (·.not_isUnit ha)
/-
**FiniteMultiplicity.not_of_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_of_one_left (b : α) : ¬ FiniteMultiplicity 1 b
参数：b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem FiniteMultiplicity.not_of_one_left (b : α) : ¬ FiniteMultiplicity 1 b := by simp

@[simp]
/-
**emultiplicity_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_one_left (b : α) : emultiplicity 1 b = ⊤
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
· 使用定理 `FiniteMultiplicity.not_of_one_left`：FiniteMultiplicity.not_of_one_left (
b : α) : ¬ FiniteMultiplicity 1 b
-/
theorem emultiplicity_one_left (b : α) : emultiplicity 1 b = ⊤ :=
  emultiplicity_eq_top.2 (FiniteMultiplicity.not_of_one_left _)

@[simp]
/-
**FiniteMultiplicity.one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.one_right (ha : FiniteMultiplicity a 1) : multiplicity 
a 1 = 0
参数：ha : FiniteMultiplicity a 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FiniteMultiplicity.multiplicity_eq_iff`：FiniteMultiplicity.multiplicity_
eq_iff (hf : FiniteMultiplicity a b) {n : Nat} : multiplicity a b = n ↔ a ^ n ∣ 
b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FiniteMultiplicity.not_dvd_of_one_right`：FiniteMultiplicity.not_dvd_of_o
ne_right : FiniteMultiplicity a 1 -> ¬a ∣ 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem FiniteMultiplicity.one_right (ha : FiniteMultiplicity a 1) : multiplicity a 1 = 0 := by
  simp [ha.multiplicity_eq_iff, ha.not_dvd_of_one_right]
/-
**FiniteMultiplicity.not_of_unit_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.not_of_unit_left (a : α) (u : αˣ) : ¬ FiniteMultiplicit
y (u : α) a
参数：a : α；u : αˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.not_of_isUnit_left`：FiniteMultiplicity.not_of_isUnit_
left (b : α) (ha : IsUnit a) : ¬FiniteMultiplicity a b
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem FiniteMultiplicity.not_of_unit_left (a : α) (u : αˣ) : ¬ FiniteMultiplicity (u : α) a :=
  FiniteMultiplicity.not_of_isUnit_left a u.isUnit
/-
**emultiplicity_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_zero`：natCast_zero : ((0 : Nat) : Nat∞) = 0
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteMultiplicity.not_iff_forall`：FiniteMultiplicity.not_iff_forall : ¬
FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b
-/
theorem emultiplicity_eq_zero :
    emultiplicity a b = 0 ↔ ¬a ∣ b := by
  by_cases hf : FiniteMultiplicity a b
  · rw [← ENat.natCast_zero, emultiplicity_eq_coe]
    simp
  · simpa [emultiplicity_eq_top.2 hf] using FiniteMultiplicity.not_iff_forall.1 hf 1
/-
**emultiplicity_eq_zero_of_irreducible_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_zero_of_irreducible_ne {R : Type*} [CommMonoidWithZero R]
 [Subsingleton Rˣ] {a b : R} (ha : Irreducible a) (hb : Irreducible b) (h : a !=
 b) : emultiplicity a b = 0
参数：ha : Irreducible a；hb : Irreducible b；h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Irreducible.dvd_irreducible_iff_associated`：Irreducible.dvd_irreducible_
iff_associated [Monoid M] {p q : M} (pp : Irreducible p) (qp : Irreducible q) : 
p ∣ q ↔ Associated p q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem emultiplicity_eq_zero_of_irreducible_ne {R : Type*} [CommMonoidWithZero R]
    [Subsingleton Rˣ] {a b : R} (ha : Irreducible a) (hb : Irreducible b) (h : a ≠ b) :
    emultiplicity a b = 0 :=
  emultiplicity_eq_zero.2 ((ha.dvd_irreducible_iff_associated hb).not.2 fun ⟨u, _⟩ ↦ by
    simp_all [Subsingleton.elim u 1])
/-
**multiplicity_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_zero : multiplicity a b = 0 ↔ ¬a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `emultiplicity_eq_iff_multiplicity_eq_of_ne_one`：emultiplicity_eq_iff_mul
tiplicity_eq_of_ne_one {n : Nat} (h : n != 1) : emultiplicity a b = n ↔ multipli
city a b = n
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
-/
theorem multiplicity_eq_zero :
    multiplicity a b = 0 ↔ ¬a ∣ b :=
  (emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one).symm.trans emultiplicity_eq_zero
/-
**emultiplicity_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_ne_zero : emultiplicity a b != 0 ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem emultiplicity_ne_zero :
    emultiplicity a b ≠ 0 ↔ a ∣ b := by
  simp [emultiplicity_eq_zero]
/-
**multiplicity_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_ne_zero : multiplicity a b != 0 ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem multiplicity_ne_zero :
    multiplicity a b ≠ 0 ↔ a ∣ b := by
  simp [multiplicity_eq_zero]
/-
**FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicit
y a b) : exists c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c
参数：hfin : FiniteMultiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteMultiplicity.multiplicity_eq_iff`：FiniteMultiplicity.multiplicity_
eq_iff (hf : FiniteMultiplicity a b) {n : Nat} : multiplicity a b = n ↔ a ^ n ∣ 
b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd (hfin : FiniteMultiplicity a b) :
    ∃ c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c := by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁
/-
**emultiplicity_le_emultiplicity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_le_emultiplicity_iff {c d : β} : emultiplicity a b <= emulti
plicity c d ↔ forall n : Nat, a ^ n ∣ b -> c ^ n ∣ d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_emultiplicity_of_pow_dvd`：le_emultiplicity_of_pow_dvd {k : Nat} (hk :
 a ^ k ∣ b) : k <= emultiplicity a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
theorem emultiplicity_le_emultiplicity_iff {c d : β} :
    emultiplicity a b ≤ emultiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d := by classical
  constructor
  · exact fun h n hab ↦ pow_dvd_of_le_emultiplicity (le_trans (le_emultiplicity_of_pow_dvd hab) h)
  · intro h
    unfold emultiplicity
    -- aesop? says
    split
    next h_1 =>
      obtain ⟨w, h_1⟩ := h_1
      split
      next h_2 =>
        simp_all only [cast_le, le_find_iff, lt_find_iff, Decidable.not_not, le_refl,
          not_true_eq_false, not_false_eq_true, implies_true]
      next h_2 => simp_all only [not_exists, Decidable.not_not, le_top]
    next h_1 =>
      simp_all only [not_exists, Decidable.not_not, not_true_eq_false, top_le_iff,
        dite_eq_right_iff, ENat.natCast_ne_top, imp_false, not_false_eq_true, implies_true]
/-
**FiniteMultiplicity.multiplicity_le_multiplicity_iff** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：FiniteMultiplicity.multiplicity_le_multiplicity_iff {c d : β} (hab : Finit
eMultiplicity a b) (hcd : FiniteMultiplicity c d) : multiplicity a b <= multipli
city c d ↔ forall n : Nat, a ^ n ∣ b -> c ^ n ∣ d
参数：hab : FiniteMultiplicity a b；hcd : FiniteMultiplicity c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem FiniteMultiplicity.multiplicity_le_multiplicity_iff {c d : β} (hab : FiniteMultiplicity a b)
    (hcd : FiniteMultiplicity c d) :
    multiplicity a b ≤ multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d := by
  rw [← ENat.natCast_le_natCast, ← hab.emultiplicity_eq_multiplicity,
    ← hcd.emultiplicity_eq_multiplicity, emultiplicity_le_emultiplicity_iff]
/-
**emultiplicity_eq_emultiplicity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_emultiplicity_iff {c d : β} : emultiplicity a b = emultip
licity c d ↔ forall n : Nat, a ^ n ∣ b ↔ c ^ n ∣ d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem emultiplicity_eq_emultiplicity_iff {c d : β} :
    emultiplicity a b = emultiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨emultiplicity_le_emultiplicity_iff.1 h.le n, emultiplicity_le_emultiplicity_iff.1 h.ge n⟩,
    fun h => le_antisymm (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mp)
      (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mpr)⟩
/-
**le_emultiplicity_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_emultiplicity_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β] (f
 : F) {a b : α} : emultiplicity a b <= emultiplicity (f a) (f b)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem le_emultiplicity_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
    (f : F) {a b : α} :
    emultiplicity a b ≤ emultiplicity (f a) (f b) :=
  emultiplicity_le_emultiplicity_iff.2 fun n ↦ by rw [← map_pow]; exact map_dvd f
/-
**emultiplicity_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β] (
f : F) {a b : α} : emultiplicity (f a) (f b) = emultiplicity a b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem emultiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : emultiplicity (f a) (f b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← map_pow, map_dvd_iff]
/-
**multiplicity_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β] (f
 : F) {a b : α} : multiplicity (f a) (f b) = multiplicity a b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `emultiplicity_map_eq`：emultiplicity_map_eq {F : Type*} [EquivLike F α β]
 [MulEquivClass F α β] (f : F) {a b : α} : emultiplicity (f a) (f b) = emultipli
city a b
-/
theorem multiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : multiplicity (f a) (f b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_map_eq f)
/-
**emultiplicity_le_emultiplicity_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_le_emultiplicity_of_dvd_right {a b c : α} (h : b ∣ c) : emul
tiplicity a b <= emultiplicity a c
参数：h : b ∣ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
theorem emultiplicity_le_emultiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
    emultiplicity a b ≤ emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun _ hb => hb.trans h
/-
**emultiplicity_eq_of_associated_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) : em
ultiplicity a b = emultiplicity a c
参数：h : Associated b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_right`：emultiplicity_le_emultiplic
ity_of_dvd_right {a b c : α} (h : b ∣ c) : emultiplicity a b <= emultiplicity a 
c
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
-/
theorem emultiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    emultiplicity a b = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_right h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_right h.symm.dvd)
/-
**multiplicity_eq_of_associated_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) : mul
tiplicity a b = multiplicity a c
参数：h : Associated b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `emultiplicity_eq_of_associated_right`：emultiplicity_eq_of_associated_rig
ht {a b c : α} (h : Associated b c) : emultiplicity a b = emultiplicity a c
-/
theorem multiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    multiplicity a b = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_right h)
/-
**dvd_of_emultiplicity_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_emultiplicity_pos {a b : α} (h : 0 < emultiplicity a b) : a ∣ b
参数：h : 0 < emultiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem dvd_of_emultiplicity_pos {a b : α} (h : 0 < emultiplicity a b) : a ∣ b :=
  pow_one a ▸ pow_dvd_of_le_emultiplicity (Order.add_one_le_of_lt h)
/-
**dvd_of_multiplicity_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_multiplicity_pos {a b : α} (h : 0 < multiplicity a b) : a ∣ b
参数：h : 0 < multiplicity a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_emultiplicity_pos`：dvd_of_emultiplicity_pos {a b : α} (h : 0 < em
ultiplicity a b) : a ∣ b
· 使用定理 `lt_emultiplicity_of_lt_multiplicity`：lt_emultiplicity_of_lt_multiplicity
 {n : Nat} (h : n < multiplicity a b) : n < emultiplicity a b
-/
theorem dvd_of_multiplicity_pos {a b : α} (h : 0 < multiplicity a b) : a ∣ b :=
  dvd_of_emultiplicity_pos (lt_emultiplicity_of_lt_multiplicity h)
/-
**dvd_iff_multiplicity_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_iff_multiplicity_pos {a b : α} : 0 < multiplicity a b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_multiplicity_pos`：dvd_of_multiplicity_pos {a b : α} (h : 0 < mult
iplicity a b) : a ∣ b
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem dvd_iff_multiplicity_pos {a b : α} : 0 < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩
/-
**dvd_iff_emultiplicity_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_iff_emultiplicity_pos {a b : α} : 0 < emultiplicity a b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `emultiplicity_pos_iff`：emultiplicity_pos_iff : 0 < emultiplicity a b ↔ 0
 < multiplicity a b
· 使用定理 `dvd_iff_multiplicity_pos`：dvd_iff_multiplicity_pos {a b : α} : 0 < multi
plicity a b ↔ a ∣ b
-/
theorem dvd_iff_emultiplicity_pos {a b : α} : 0 < emultiplicity a b ↔ a ∣ b :=
  emultiplicity_pos_iff.trans dvd_iff_multiplicity_pos
/-
**Nat.finiteMultiplicity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.finiteMultiplicity_iff {a b : Nat} : FiniteMultiplicity a b ↔ a != 1 ∧
 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `FiniteMultiplicity.not_iff_forall`：FiniteMultiplicity.not_iff_forall : ¬
FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Nat.finiteMultiplicity_iff {a b : ℕ} : FiniteMultiplicity a b ↔ a ≠ 1 ∧ 0 < b := by
  rw [← not_iff_not, FiniteMultiplicity.not_iff_forall, not_and_or, not_ne_iff, not_lt,
    Nat.le_zero]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
        have ha : a ≠ 0 := fun ha => hb <| zero_dvd_iff.mp <| by rw [ha] at h; exact h 1
        Classical.by_contradiction fun ha1 : a ≠ 1 =>
          have ha_gt_one : 1 < a :=
            lt_of_not_ge fun _ =>
              match a with
              | 0 => ha rfl
              | 1 => ha1 rfl
              | b+2 => by lia
          not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (b.lt_pow_self ha_gt_one),
      fun h => by cases h <;> simp [*]⟩

alias ⟨_, Dvd.multiplicity_pos⟩ := dvd_iff_multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

/-
**FiniteMultiplicity.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.mul_right {a b c : α} (hf : FiniteMultiplicity a (b * c
)) : FiniteMultiplicity a c
参数：hf : FiniteMultiplicity a (b * c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.mul_left`：FiniteMultiplicity.mul_left {c : α} : Finit
eMultiplicity a (b * c) -> FiniteMultiplicity a b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem FiniteMultiplicity.mul_right {a b c : α} (hf : FiniteMultiplicity a (b * c)) :
    FiniteMultiplicity a c := (mul_comm b c ▸ hf).mul_left
/-
**emultiplicity_of_isUnit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) :
 emultiplicity a b = 0
参数：ha : ¬IsUnit a；hb : IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem emultiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : emultiplicity a b = 0 :=
  emultiplicity_eq_zero.mpr fun h ↦ ha (isUnit_of_dvd_unit h hb)
/-
**multiplicity_of_isUnit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) : 
multiplicity a b = 0
参数：ha : ¬IsUnit a；hb : IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multiplicity_eq_zero`：multiplicity_eq_zero : multiplicity a b = 0 ↔ ¬a ∣
 b
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem multiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : multiplicity a b = 0 :=
  multiplicity_eq_zero.mpr fun h ↦ ha (isUnit_of_dvd_unit h hb)
/-
**emultiplicity_of_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : emultiplicity a 1 = 
0
参数：ha : ¬IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_of_isUnit_right`：emultiplicity_of_isUnit_right {a b : α} (
ha : ¬IsUnit a) (hb : IsUnit b) : emultiplicity a b = 0
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem emultiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : emultiplicity a 1 = 0 :=
  emultiplicity_of_isUnit_right ha isUnit_one
/-
**multiplicity_of_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0
参数：ha : ¬IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_of_isUnit_right`：multiplicity_of_isUnit_right {a b : α} (ha
 : ¬IsUnit a) (hb : IsUnit b) : multiplicity a b = 0
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem multiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  multiplicity_of_isUnit_right ha isUnit_one
/-
**emultiplicity_of_unit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : emultiplic
ity a u = 0
参数：ha : ¬IsUnit a；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_of_isUnit_right`：emultiplicity_of_isUnit_right {a b : α} (
ha : ¬IsUnit a) (hb : IsUnit b) : emultiplicity a b = 0
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem emultiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : emultiplicity a u = 0 :=
  emultiplicity_of_isUnit_right ha u.isUnit
/-
**multiplicity_of_unit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicit
y a u = 0
参数：ha : ¬IsUnit a；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_of_isUnit_right`：multiplicity_of_isUnit_right {a b : α} (ha
 : ¬IsUnit a) (hb : IsUnit b) : multiplicity a b = 0
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem multiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  multiplicity_of_isUnit_right ha u.isUnit
/-
**emultiplicity_le_emultiplicity_of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_le_emultiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) : em
ultiplicity b c <= emultiplicity a c
参数：hdvd : a ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `pow_dvd_pow_of_dvd`：pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b
 ^ n
-/
theorem emultiplicity_le_emultiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
    emultiplicity b c ≤ emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h
/-
**emultiplicity_eq_of_associated_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) : emu
ltiplicity b c = emultiplicity a c
参数：h : Associated a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_left`：emultiplicity_le_emultiplici
ty_of_dvd_left {a b c : α} (hdvd : a ∣ b) : emultiplicity b c <= emultiplicity a
 c
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
-/
theorem emultiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    emultiplicity b c = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_left h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_left h.symm.dvd)
/-
**multiplicity_eq_of_associated_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) : mult
iplicity b c = multiplicity a c
参数：h : Associated a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `emultiplicity_eq_of_associated_left`：emultiplicity_eq_of_associated_left
 {a b c : α} (h : Associated a b) : emultiplicity b c = emultiplicity a c
-/
theorem multiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    multiplicity b c = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_left h)
/-
**emultiplicity_mk_eq_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_mk_eq_emultiplicity {a b : α} : emultiplicity (Associates.mk
 a) (Associates.mk b) = emultiplicity a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem emultiplicity_mk_eq_emultiplicity {a b : α} :
    emultiplicity (Associates.mk a) (Associates.mk b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← Associates.mk_pow, Associates.mk_dvd_mk]

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

/-
**FiniteMultiplicity.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.ne_zero {a b : α} (h : FiniteMultiplicity a b) : b != 0
参数：h : FiniteMultiplicity a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem FiniteMultiplicity.ne_zero {a b : α} (h : FiniteMultiplicity a b) : b ≠ 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]
/-
**emultiplicity_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
· 使用定理 `FiniteMultiplicity.ne_zero`：FiniteMultiplicity.ne_zero {a b : α} (h : Fi
niteMultiplicity a b) : b != 0
-/
theorem emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤ :=
  emultiplicity_eq_top.2 (fun v ↦ v.ne_zero rfl)
/-
**multiplicity_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_zero (a : α) : multiplicity a 0 = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_one_of_not_finiteMultiplicity`：multiplicity_eq_one_of_no
t_finiteMultiplicity (h : ¬FiniteMultiplicity a b) : multiplicity a b = 1
· 使用定理 `FiniteMultiplicity.ne_zero`：FiniteMultiplicity.ne_zero {a b : α} (h : Fi
niteMultiplicity a b) : b != 0
-/
theorem multiplicity_zero (a : α) : multiplicity a 0 = 1 :=
  multiplicity_eq_one_of_not_finiteMultiplicity fun h ↦ h.ne_zero rfl

@[simp]
/-
**emultiplicity_zero_eq_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a != 0) : emultiplicit
y 0 a = 0
参数：a : α；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
-/
theorem emultiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : emultiplicity 0 a = 0 :=
  emultiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha

@[simp]
/-
**multiplicity_zero_eq_zero_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a != 0) : multiplicity 
0 a = 0
参数：a : α；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `multiplicity_eq_zero`：multiplicity_eq_zero : multiplicity a b = 0 ↔ ¬a ∣
 b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
-/
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha

end MonoidWithZero

section Semiring

variable [Semiring α]

/-
**FiniteMultiplicity.or_of_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.or_of_add {p a b : α} (hf : FiniteMultiplicity p (a + b
)) : FiniteMultiplicity p a ∨ FiniteMultiplicity p b
参数：hf : FiniteMultiplicity p (a + b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem FiniteMultiplicity.or_of_add {p a b : α} (hf : FiniteMultiplicity p (a + b)) :
    FiniteMultiplicity p a ∨ FiniteMultiplicity p b := by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]
/-
**min_le_emultiplicity_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_le_emultiplicity_add {p a b : α} : min (emultiplicity p a) (emultiplic
ity p b) <= emultiplicity p (a + b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.or_of_add`：FiniteMultiplicity.or_of_add {p a b : α} (
hf : FiniteMultiplicity p (a + b)) : FiniteMultiplicity p a ∨ FiniteMultiplicity
 p b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_emultiplicity_of_pow_dvd`：le_emultiplicity_of_pow_dvd {k : Nat} (hk :
 a ^ k ∣ b) : k <= emultiplicity a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem min_le_emultiplicity_add {p a b : α} :
    min (emultiplicity p a) (emultiplicity p b) ≤ emultiplicity p (a + b) := by
  cases hm : min (emultiplicity p a) (emultiplicity p b)
  · simp only [top_le_iff, min_eq_top, emultiplicity_eq_top] at hm ⊢
    contrapose hm
    simp only [not_and_or, not_not] at hm ⊢
    exact hm.or_of_add
  · apply le_emultiplicity_of_pow_dvd
    simp [dvd_add, pow_dvd_of_le_emultiplicity, ← hm]

end Semiring

section Ring

variable [Ring α]

@[simp]
/-
**FiniteMultiplicity.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.neg_iff {a b : α} : FiniteMultiplicity a (-b) ↔ FiniteM
ultiplicity a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem FiniteMultiplicity.neg_iff {a b : α} :
    FiniteMultiplicity a (-b) ↔ FiniteMultiplicity a b := by
  unfold FiniteMultiplicity
  congr! 3
  simp only [dvd_neg]

alias ⟨_, FiniteMultiplicity.neg⟩ := FiniteMultiplicity.neg_iff

@[simp]
/-
**emultiplicity_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_neg (a b : α) : emultiplicity a (-b) = emultiplicity a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `emultiplicity_eq_emultiplicity_iff`：emultiplicity_eq_emultiplicity_iff {
c d : β} : emultiplicity a b = emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ↔ c
 ^ n ∣ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem emultiplicity_neg (a b : α) : emultiplicity a (-b) = emultiplicity a b := by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp

@[simp]
/-
**multiplicity_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_neg (a b : α) : multiplicity a (-b) = multiplicity a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `emultiplicity_neg`：emultiplicity_neg (a b : α) : emultiplicity a (-b) = 
emultiplicity a b
-/
theorem multiplicity_neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_neg a b)
/-
**Int.emultiplicity_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.emultiplicity_natAbs (a : Nat) (b : Int) : emultiplicity a b.natAbs = 
emultiplicity (a : Int) b
参数：a : Nat；b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_emultiplicity`：Int.natCast_emultiplicity (a b : Nat) : emult
iplicity (a : Int) (b : Int) = emultiplicity a b
· 使用定理 `emultiplicity_neg`：emultiplicity_neg (a b : α) : emultiplicity a (-b) = 
emultiplicity a b
-/
theorem Int.emultiplicity_natAbs (a : ℕ) (b : ℤ) :
    emultiplicity a b.natAbs = emultiplicity (a : ℤ) b := by
  rcases Int.natAbs_eq b with h | h <;> conv_rhs => rw [h]
  · rw [Int.natCast_emultiplicity]
  · rw [emultiplicity_neg, Int.natCast_emultiplicity]
/-
**Int.multiplicity_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.multiplicity_natAbs (a : Nat) (b : Int) : multiplicity a b.natAbs = mu
ltiplicity (a : Int) b
参数：a : Nat；b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `Int.emultiplicity_natAbs`：Int.emultiplicity_natAbs (a : Nat) (b : Int) :
 emultiplicity a b.natAbs = emultiplicity (a : Int) b
-/
theorem Int.multiplicity_natAbs (a : ℕ) (b : ℤ) :
    multiplicity a b.natAbs = multiplicity (a : ℤ) b :=
  multiplicity_eq_of_emultiplicity_eq (Int.emultiplicity_natAbs a b)
/-
**emultiplicity_add_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_add_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity
 p a) : emultiplicity p (a + b) = emultiplicity p b
参数：h : emultiplicity p b < emultiplicity p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `finiteMultiplicity_iff_emultiplicity_ne_top`：finiteMultiplicity_iff_emul
tiplicity_ne_top : FiniteMultiplicity a b ↔ emultiplicity a b != ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `emultiplicity_eq_of_dvd_of_not_dvd`：emultiplicity_eq_of_dvd_of_not_dvd {
k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : emultiplicity a b = k
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `pow_dvd_of_le_emultiplicity`：pow_dvd_of_le_emultiplicity {k : Nat} (hk :
 k <= emultiplicity a b) : a ^ k ∣ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dvd_add_right`：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`：FiniteMultiplicity.no
t_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat} (hm : multi
plicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem emultiplicity_add_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a + b) = emultiplicity p b := by
  have : FiniteMultiplicity p b := finiteMultiplicity_iff_emultiplicity_ne_top.2 (by simp [·] at h)
  rw [this.emultiplicity_eq_multiplicity] at *
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · apply dvd_add
    · apply pow_dvd_of_le_emultiplicity
      exact h.le
    · simp
  · rw [dvd_add_right]
    · apply this.not_pow_dvd_of_multiplicity_lt
      simp
    apply pow_dvd_of_le_emultiplicity
    exact Order.add_one_le_of_lt h
/-
**FiniteMultiplicity.multiplicity_add_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.multiplicity_add_of_gt {p a b : α} (hf : FiniteMultipli
city p b) (h : multiplicity p b < multiplicity p a) : multiplicity p (a + b) = m
ultiplicity p b
参数：hf : FiniteMultiplicity p b；h : multiplicity p b < multiplicity p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq`：multiplicity_eq_of_emultiplicity_eq
 {c d : β} (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = mult
iplicity c d
· 使用定理 `emultiplicity_add_of_gt`：emultiplicity_add_of_gt {p a b : α} (h : emulti
plicity p b < emultiplicity p a) : emultiplicity p (a + b) = emultiplicity p b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithTop.coe_strictMono`：∀ {α : Type u_1} [inst : Preorder α], StrictMono
 fun a => ↑a
· 使用定理 `multiplicity_le_emultiplicity`：multiplicity_le_emultiplicity : multiplic
ity a b <= emultiplicity a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
-/
theorem FiniteMultiplicity.multiplicity_add_of_gt {p a b : α} (hf : FiniteMultiplicity p b)
    (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
  multiplicity_eq_of_emultiplicity_eq <| emultiplicity_add_of_gt (hf.emultiplicity_eq_multiplicity ▸
      (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity)
/-
**emultiplicity_sub_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_sub_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity
 p a) : emultiplicity p (a - b) = emultiplicity p b
参数：h : emultiplicity p b < emultiplicity p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `emultiplicity_add_of_gt`：emultiplicity_add_of_gt {p a b : α} (h : emulti
plicity p b < emultiplicity p a) : emultiplicity p (a + b) = emultiplicity p b
· 使用定理 `emultiplicity_neg`：emultiplicity_neg (a b : α) : emultiplicity a (-b) = 
emultiplicity a b
-/
theorem emultiplicity_sub_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a - b) = emultiplicity p b := by
  rw [sub_eq_add_neg, emultiplicity_add_of_gt] <;> rw [emultiplicity_neg]; assumption
/-
**multiplicity_sub_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p 
a) (hfin : FiniteMultiplicity p b) : multiplicity p (a - b) = multiplicity p b
参数：h : multiplicity p b < multiplicity p a；hfin : FiniteMultiplicity p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `FiniteMultiplicity.multiplicity_add_of_gt`：FiniteMultiplicity.multiplici
ty_add_of_gt {p a b : α} (hf : FiniteMultiplicity p b) (h : multiplicity p b < m
ultiplicity p a) : multiplicity…
· 使用定理 `FiniteMultiplicity.neg`：∀ {α : Type u_1} [inst : Ring α] {a b : α}, Fini
teMultiplicity a b → FiniteMultiplicity a (-b)
· 使用定理 `multiplicity_neg`：multiplicity_neg (a b : α) : multiplicity a (-b) = mul
tiplicity a b
-/
theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a)
    (hfin : FiniteMultiplicity p b) : multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg, hfin.neg.multiplicity_add_of_gt] <;> rw [multiplicity_neg]; assumption
/-
**emultiplicity_add_eq_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_add_eq_min {p a b : α} (h : emultiplicity p a != emultiplici
ty p b) : emultiplicity p (a + b) = min (emultiplicity p a) (emultiplicity p b)
参数：h : emultiplicity p a != emultiplicity p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `emultiplicity_add_of_gt`：emultiplicity_add_of_gt {p a b : α} (h : emulti
plicity p b < emultiplicity p a) : emultiplicity p (a + b) = emultiplicity p b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem emultiplicity_add_eq_min {p a b : α}
    (h : emultiplicity p a ≠ emultiplicity p b) :
    emultiplicity p (a + b) = min (emultiplicity p a) (emultiplicity p b) := by
  rcases lt_trichotomy (emultiplicity p a) (emultiplicity p b) with (hab | _ | hab)
  · rw [add_comm, emultiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [emultiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab
/-
**multiplicity_add_eq_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_add_eq_min {p a b : α} (ha : FiniteMultiplicity p a) (hb : Fi
niteMultiplicity p b) (h : multiplicity p a != multiplicity p b) : multiplicity 
p (a + b) = min (multiplicity p a) (multiplicity p b)
参数：ha : FiniteMultiplicity p a；hb : FiniteMultiplicity p b；h : multiplicity p a 
!= multiplicity p b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `FiniteMultiplicity.multiplicity_add_of_gt`：FiniteMultiplicity.multiplici
ty_add_of_gt {p a b : α} (hf : FiniteMultiplicity p b) (h : multiplicity p b < m
ultiplicity p a) : multiplicity…
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem multiplicity_add_eq_min {p a b : α} (ha : FiniteMultiplicity p a)
    (hb : FiniteMultiplicity p b) (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) := by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, ha.multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [hb.multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

end Ring

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α]

/-
**finiteMultiplicity_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finiteMultiplicity_mul_aux {p : α} (hp : Prime p) {a b : α} : forall {n m 
: Nat}, ¬p ^ (n + 1) ∣ a -> ¬p ^ (m + 1) ∣ b -> ¬p ^ (n + m + 1) ∣ a * b | n, m 
=> fun ha hb ⟨s, hs⟩ => have : p ∣ a * b
参数：hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteMultiplicity_mul_aux._unary`：∀ {α : Type u_1} [inst : CommMonoidWi
thZero α] [IsCancelMulZero α] {p : α},   Prime p →     ∀ (_x : (_ : α) ×' (_ : α
) ×' (_ : ℕ) ×' ℕ),    …
-/
theorem finiteMultiplicity_mul_aux {p : α} (hp : Prime p) {a b : α} :
    ∀ {n m : ℕ}, ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
  | n, m => fun ha hb ⟨s, hs⟩ =>
    have : p ∣ a * b := ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by simp [hx, hn0] at ha
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha (hx.symm ▸ ⟨y, mul_right_cancel₀ hp.1 <| by
            rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy
            simp [hy, pow_add, mul_comm, mul_left_comm]⟩)
        have : 1 ≤ n + m := le_trans hn0 (Nat.le_add_right n m)
        finiteMultiplicity_mul_aux hp hpx hb
          ⟨s, mul_right_cancel₀ hp.1 (by
                rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0), tsub_add_cancel_of_le this]
                simp_all [mul_comm, mul_left_comm, pow_add])⟩)
      fun ⟨x, hx⟩ =>
        have hm0 : 0 < m :=
          Nat.pos_of_ne_zero fun hm0 => by simp [hx, hm0] at hb
        have hpx : ¬p ^ (m - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          hb
            (hx.symm ▸
              ⟨y,
                mul_right_cancel₀ hp.1 <| by
                  rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy
                  simp [hy, pow_add, mul_comm, mul_left_comm]⟩)
        finiteMultiplicity_mul_aux hp ha hpx
        ⟨s, mul_right_cancel₀ hp.1 (by
              rw [add_assoc, tsub_add_cancel_of_le (succ_le_of_lt hm0)]
              simp_all [mul_comm, mul_left_comm, pow_add])⟩
/-
**Prime.finiteMultiplicity_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.finiteMultiplicity_mul {p a b : α} (hp : Prime p) : FiniteMultiplici
ty p a -> FiniteMultiplicity p b -> FiniteMultiplicity p (a * b)
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteMultiplicity_mul_aux`：finiteMultiplicity_mul_aux {p : α} (hp : Pri
me p) {a b : α} : forall {n m : Nat}, ¬p ^ (n + 1) ∣ a -> ¬p ^ (m + 1) ∣ b -> ¬p
 ^ (n + m + 1) ∣…
-/
theorem Prime.finiteMultiplicity_mul {p a b : α} (hp : Prime p) :
    FiniteMultiplicity p a → FiniteMultiplicity p b → FiniteMultiplicity p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finiteMultiplicity_mul_aux hp hn hm⟩
/-
**FiniteMultiplicity.mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.mul_iff {p a b : α} (hp : Prime p) : FiniteMultiplicity
 p (a * b) ↔ FiniteMultiplicity p a ∧ FiniteMultiplicity p b
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.mul_left`：FiniteMultiplicity.mul_left {c : α} : Finit
eMultiplicity a (b * c) -> FiniteMultiplicity a b
· 使用定理 `FiniteMultiplicity.mul_right`：FiniteMultiplicity.mul_right {a b c : α} (
hf : FiniteMultiplicity a (b * c)) : FiniteMultiplicity a c
· 使用定理 `Prime.finiteMultiplicity_mul`：Prime.finiteMultiplicity_mul {p a b : α} (
hp : Prime p) : FiniteMultiplicity p a -> FiniteMultiplicity p b -> FiniteMultip
licity p (a * b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem FiniteMultiplicity.mul_iff {p a b : α} (hp : Prime p) :
    FiniteMultiplicity p (a * b) ↔ FiniteMultiplicity p a ∧ FiniteMultiplicity p b :=
  ⟨fun h => ⟨h.mul_left, h.mul_right⟩, fun h =>
    hp.finiteMultiplicity_mul h.1 h.2⟩
/-
**FiniteMultiplicity.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.pow {p a : α} (hp : Prime p) (hfin : FiniteMultiplicity
 p a) {k : Nat} : FiniteMultiplicity p (a ^ k)
参数：hp : Prime p；hfin : FiniteMultiplicity p a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FiniteMultiplicity.pow {p a : α} (hp : Prime p)
    (hfin : FiniteMultiplicity p a) {k : ℕ} : FiniteMultiplicity p (a ^ k) :=
  match k, hfin with
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact hp.finiteMultiplicity_mul ha (ha.pow hp)

@[simp]
/-
**multiplicity_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_self {a : α} : multiplicity a a = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.multiplicity_eq_iff`：FiniteMultiplicity.multiplicity_
eq_iff (hf : FiniteMultiplicity a b) {n : Nat} : multiplicity a b = n ↔ a ^ n ∣ 
b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `FiniteMultiplicity.not_isUnit`：FiniteMultiplicity.not_isUnit (h : Finite
Multiplicity a b) : ¬IsUnit a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FiniteMultiplicity.ne_zero`：FiniteMultiplicity.ne_zero {a b : α} (h : Fi
niteMultiplicity a b) : b != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `multiplicity_eq_one_of_not_finiteMultiplicity`：multiplicity_eq_one_of_no
t_finiteMultiplicity (h : ¬FiniteMultiplicity a b) : multiplicity a b = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem multiplicity_self {a : α} : multiplicity a a = 1 := by
  by_cases ha : FiniteMultiplicity a a
  · rw [ha.multiplicity_eq_iff]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := .of_mul_eq_one v hv.symm
      simpa [this] using ha.not_isUnit
    · simpa using ha.ne_zero
  · simp [ha]

@[simp]
/-
**FiniteMultiplicity.emultiplicity_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteMultiplicity.emultiplicity_self {a : α} (hfin : FiniteMultiplicity a
 a) : emultiplicity a a = 1
参数：hfin : FiniteMultiplicity a a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `multiplicity_self`：multiplicity_self {a : α} : multiplicity a a = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FiniteMultiplicity.emultiplicity_self {a : α} (hfin : FiniteMultiplicity a a) :
    emultiplicity a a = 1 := by
  simp [hfin.emultiplicity_eq_multiplicity]
/-
**multiplicity_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : FiniteMultiplicity p (
a * b)) : multiplicity p (a * b) = multiplicity p a + multiplicity p b
参数：hp : Prime p；hfin : FiniteMultiplicity p (a * b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`：FiniteMultiplicity.no
t_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat} (hm : multi
plicity a b < m) : ¬a ^ m ∣ b
· 使用定理 `FiniteMultiplicity.mul_left`：FiniteMultiplicity.mul_left {c : α} : Finit
eMultiplicity a (b * c) -> FiniteMultiplicity a b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `FiniteMultiplicity.mul_right`：FiniteMultiplicity.mul_right {a b c : α} (
hf : FiniteMultiplicity a (b * c)) : FiniteMultiplicity a c
· 使用定理 `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`：succ_dvd_or_succ_dvd_of_succ_s
um_dvd_mul (hp : Prime p) {a b : M} {k l : Nat} : p ^ k ∣ a -> p ^ l ∣ b -> p ^ 
(k + l + 1) ∣ a * b -> p ^ (k …
· 使用定理 `FiniteMultiplicity.multiplicity_eq_iff`：FiniteMultiplicity.multiplicity_
eq_iff (hf : FiniteMultiplicity a b) {n : Nat} : multiplicity a b = n ↔ a ^ n ∣ 
b ∧ ¬a ^ (n + 1) ∣ b
-/
theorem multiplicity_mul {p a b : α} (hp : Prime p) (hfin : FiniteMultiplicity p (a * b)) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b := by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [pow_add]; gcongr
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * b :=
    fun h =>
    not_or_intro (hfin.mul_left.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (hfin.mul_right.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [hfin.multiplicity_eq_iff]
  exact ⟨hdiv, hsucc⟩
/-
**emultiplicity_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_mul {p a b : α} (hp : Prime p) : emultiplicity p (a * b) = e
multiplicity p a + emultiplicity p b
参数：hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `FiniteMultiplicity.mul_left`：FiniteMultiplicity.mul_left {c : α} : Finit
eMultiplicity a (b * c) -> FiniteMultiplicity a b
· 使用定理 `FiniteMultiplicity.mul_right`：FiniteMultiplicity.mul_right {a b c : α} (
hf : FiniteMultiplicity a (b * c)) : FiniteMultiplicity a c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `multiplicity_mul`：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Fi
niteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multip
licity…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENat.add_eq_top`：∀ {a b : ℕ∞}, a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
· 使用定理 `FiniteMultiplicity.mul_iff`：FiniteMultiplicity.mul_iff {p a b : α} (hp :
 Prime p) : FiniteMultiplicity p (a * b) ↔ FiniteMultiplicity p a ∧ FiniteMultip
licity p b
-/
theorem emultiplicity_mul {p a b : α} (hp : Prime p) :
    emultiplicity p (a * b) = emultiplicity p a + emultiplicity p b := by
  by_cases hfin : FiniteMultiplicity p (a * b)
  · rw [hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity,
      hfin.mul_right.emultiplicity_eq_multiplicity]
    norm_cast
    exact multiplicity_mul hp hfin
  · rw [emultiplicity_eq_top.mpr hfin, eq_comm, ENat.add_eq_top, emultiplicity_eq_top,
      emultiplicity_eq_top]
    simpa only [FiniteMultiplicity.mul_iff hp, not_and_or] using hfin
/-
**Finset.emultiplicity_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.emultiplicity_prod {β : Type*} {p : α} (hp : Prime p) (s : Finset β
) (f : β -> α) : emultiplicity p (∏ x in s, f x) = ∑ x in s, emultiplicity p (f 
x)
参数：hp : Prime p；s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `emultiplicity_of_one_right`：emultiplicity_of_one_right {a : α} (ha : ¬Is
Unit a) : emultiplicity a 1 = 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
-/
theorem Finset.emultiplicity_prod {β : Type*} {p : α} (hp : Prime p) (s : Finset β) (f : β → α) :
    emultiplicity p (∏ x ∈ s, f x) = ∑ x ∈ s, emultiplicity p (f x) := by classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact emultiplicity_of_one_right hp.not_isUnit
  | insert a s has ih => simpa [has, ← ih] using emultiplicity_mul hp
/-
**emultiplicity_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow {p a : α} (hp : Prime p) {k : Nat} : emultiplicity p (a 
^ k) = k * emultiplicity p a
参数：hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `emultiplicity_of_one_right`：emultiplicity_of_one_right {a : α} (ha : ¬Is
Unit a) : emultiplicity a 1 = 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem emultiplicity_pow {p a : α} (hp : Prime p) {k : ℕ} :
    emultiplicity p (a ^ k) = k * emultiplicity p a := by
  induction k with
  | zero => simp [emultiplicity_of_one_right hp.not_isUnit]
  | succ k hk => simp [pow_succ, emultiplicity_mul hp, hk, add_mul]
/-
**FiniteMultiplicity.multiplicity_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteMultiplic
ity`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCancelMulZero α] {p a : 
α},   Prime p → FiniteMultiplicity p a → ∀ {k : ℕ}, multiplicity p (a ^ k) = k *
 multiplicity p a
参数：a ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `emultiplicity_pow`：emultiplicity_pow {p a : α} (hp : Prime p) {k : Nat} 
: emultiplicity p (a ^ k) = k * emultiplicity p a
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `FiniteMultiplicity.pow`：FiniteMultiplicity.pow {p a : α} (hp : Prime p) 
(hfin : FiniteMultiplicity p a) {k : Nat} : FiniteMultiplicity p (a ^ k)
-/
protected theorem FiniteMultiplicity.multiplicity_pow {p a : α} (hp : Prime p)
    (ha : FiniteMultiplicity p a) {k : ℕ} : multiplicity p (a ^ k) = k * multiplicity p a := by
  exact_mod_cast (ha.pow hp).emultiplicity_eq_multiplicity ▸
    ha.emultiplicity_eq_multiplicity ▸ emultiplicity_pow hp
/-
**emultiplicity_pow_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow_self {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat) : 
emultiplicity p (p ^ n) = n
参数：h0 : p != 0；hu : ¬IsUnit p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_eq_of_dvd_of_not_dvd`：emultiplicity_eq_of_dvd_of_not_dvd {
k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : emultiplicity a b = k
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_dvd_pow_iff`：pow_dvd_pow_iff (ha₀ : a != 0) (ha : ¬IsUnit a) : a ^ n
 ∣ a ^ m ↔ n <= m
· 使用定理 `Nat.not_succ_le_self`：∀ (n : ℕ), ¬n.succ ≤ n
-/
theorem emultiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    emultiplicity p (p ^ n) = n := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self
/-
**multiplicity_pow_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_pow_self {p : α} (h0 : p != 0) (hu : ¬IsUnit p) (n : Nat) : m
ultiplicity p (p ^ n) = n
参数：h0 : p != 0；hu : ¬IsUnit p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `emultiplicity_pow_self`：emultiplicity_pow_self {p : α} (h0 : p != 0) (hu
 : ¬IsUnit p) (n : Nat) : emultiplicity p (p ^ n) = n
-/
theorem multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_pow_self h0 hu n)
/-
**emultiplicity_pow_self_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : Nat) : emultip
licity p (p ^ n) = n
参数：hp : Prime p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_pow_self`：emultiplicity_pow_self {p : α} (h0 : p != 0) (hu
 : ¬IsUnit p) (n : Nat) : emultiplicity p (p ^ n) = n
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
-/
theorem emultiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    emultiplicity p (p ^ n) = n :=
  emultiplicity_pow_self hp.ne_zero hp.not_isUnit n
/-
**multiplicity_pow_self_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : Nat) : multipli
city p (p ^ n) = n
参数：hp : Prime p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiplicity_pow_self`：multiplicity_pow_self {p : α} (h0 : p != 0) (hu :
 ¬IsUnit p) (n : Nat) : multiplicity p (p ^ n) = n
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
-/
theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.ne_zero hp.not_isUnit n

end CancelCommMonoidWithZero

section Nat

/-
**multiplicity_eq_zero_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_eq_zero_of_coprime {p a b : Nat} (hp : p != 1) (hle : multipl
icity p a <= multiplicity p b) (hab : Nat.Coprime a b) : multiplicity p a = 0
参数：hp : p != 1；hle : multiplicity p a <= multiplicity p b；hab : Nat.Coprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_not_pos`：∀ {n : ℕ}, ¬0 < n → n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
-/
theorem multiplicity_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
    (hle : multiplicity p a ≤ multiplicity p b) (hab : Nat.Coprime a b) : multiplicity p a = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro nh
  have da : p ∣ a := by simpa [multiplicity_eq_zero] using nh.ne.symm
  have db : p ∣ b := by simpa [multiplicity_eq_zero] using (nh.trans_le hle).ne.symm
  have := Nat.dvd_gcd da db
  rw [Coprime.gcd_eq_one hab, Nat.dvd_one] at this
  exact hp this

end Nat

/-
**Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs {a b : Int} : FiniteM
ultiplicity a b ↔ FiniteMultiplicity a.natAbs b.natAbs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs {a b : ℤ} :
    FiniteMultiplicity a b ↔ FiniteMultiplicity a.natAbs b.natAbs := by
  simp only [FiniteMultiplicity.def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]
/-
**Int.finiteMultiplicity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.finiteMultiplicity_iff {a b : Int} : FiniteMultiplicity a b ↔ a.natAbs
 != 1 ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.finiteMultiplicity_iff_finiteMultiplicity_natAbs`：Int.finiteMultipli
city_iff_finiteMultiplicity_natAbs {a b : Int} : FiniteMultiplicity a b ↔ Finite
Multiplicity a.natAbs b.natAbs
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Int.finiteMultiplicity_iff {a b : ℤ} : FiniteMultiplicity a b ↔ a.natAbs ≠ 1 ∧ b ≠ 0 := by
  rw [finiteMultiplicity_iff_finiteMultiplicity_natAbs, Nat.finiteMultiplicity_iff,
    pos_iff_ne_zero, Int.natAbs_ne_zero]
/-
**Nat.decidableFiniteMultiplicity** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.decidableFiniteMultiplicity : DecidableRel fun a b : Nat => FiniteMult
iplicity a b
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
-/
instance Nat.decidableFiniteMultiplicity : DecidableRel fun a b : ℕ => FiniteMultiplicity a b :=
  fun _ _ ↦ decidable_of_iff' _ Nat.finiteMultiplicity_iff
/-
**Int.decidableMultiplicityFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.decidableMultiplicityFinite : DecidableRel fun a b : Int => FiniteMult
iplicity a b
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.finiteMultiplicity_iff`：Int.finiteMultiplicity_iff {a b : Int} : Fin
iteMultiplicity a b ↔ a.natAbs != 1 ∧ b != 0
-/
instance Int.decidableMultiplicityFinite : DecidableRel fun a b : ℤ => FiniteMultiplicity a b :=
  fun _ _ ↦ decidable_of_iff' _ Int.finiteMultiplicity_iff
