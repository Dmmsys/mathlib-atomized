/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.PNat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe
public import Mathlib.Tactic.Lift

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `Data.PNat.Basic`, as they need more imports.
-/

@[expose] public section

deriving instance LinearOrder for PNat

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℕ+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [NeZero n] : OfNat ℕ+ n :=
  ⟨⟨n, Nat.pos_of_ne_zero <| NeZero.ne n⟩⟩

namespace PNat

-- Note: similar to Subtype.coe_mk
@[simp]
/-
**PNat.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mk_coe (n h) : (PNat.val (⟨n, h⟩ : Nat+) : Nat) = n
参数：n h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
/-
**PNat.natPred** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：natPred (i : Nat+) : Nat
参数：i : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predecessor of a `ℕ+`, as a `ℕ`.
-/
def natPred (i : ℕ+) : ℕ :=
  i - 1

@[simp]
/-
**PNat.natPred_eq_pred** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_eq_pred {n : Nat} (h : 0 < n) : natPred (⟨n, h⟩ : Nat+) = n.pred
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natPred_eq_pred {n : ℕ} (h : 0 < n) : natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl

end PNat

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
/-
**Nat.toPNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：toPNat (n : Nat) (h : 0 < n
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`.
-/
def toPNat (n : ℕ) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
/-
**Nat.succPNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：succPNat (n : Nat) : Nat+
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
Write a successor as an element of `ℕ+`.
-/
def succPNat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
/-
**Nat.succPNat_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_coe (n : Nat) : (succPNat n : Nat) = succ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succPNat_coe (n : ℕ) : (succPNat n : ℕ) = succ n :=
  rfl

@[simp]
/-
**Nat.natPred_succPNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：natPred_succPNat (n : Nat) : n.succPNat.natPred = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natPred_succPNat (n : ℕ) : n.succPNat.natPred = n :=
  rfl

@[simp]
/-
**Nat._root_.PNat.succPNat_natPred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PNat.succPNat_natPred (n : ℕ+) : n.natPred.succPNat = n :=
  Subtype.ext <| succ_pred_eq_of_pos n.2

/-- Convert a natural number to a `PNat`. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
/-
**Nat.toPNat'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：toPNat' (n : Nat) : Nat+
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a natural number to a `PNat`. `n+1` is mapped to itself,
  and `0` becomes `1`.
-/
def toPNat' (n : ℕ) : ℕ+ :=
  succPNat (pred n)

@[simp]
/-
**Nat.toPNat'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.toPNat' 0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPNat'_zero : Nat.toPNat' 0 = 1 := rfl

@[simp]
/-
**Nat.toPNat'_coe** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), ↑n.toPNat' = if 0 < n then n else 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem toPNat'_coe : ∀ n : ℕ, (toPNat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
similar structures on ℕ. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
/-
**PNat.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mk_le_mk (n k : Nat) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : Nat+) <= ⟨k, h
k⟩ ↔ n <= k
参数：n k : Nat；hn : 0 < n；hk : 0 < k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
We now define a long list of structures on ℕ+ induced by
similar structures on ℕ. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k := by simp
/-
**PNat.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mk_lt_mk (n k : Nat) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : Nat+) < ⟨k, hk
⟩ ↔ n < k
参数：n k : Nat；hn : 0 < n；hk : 0 < k。
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
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k := by simp

@[simp, norm_cast]
/-
**PNat.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_le_coe (n k : Nat+) : (n : Nat) <= k ↔ n <= k
参数：n k : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, norm_cast]
/-
**PNat.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_lt_coe (n k : Nat+) : (n : Nat) < k ↔ n < k
参数：n k : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
/-
**PNat.pos** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：pos (n : Nat+) : 0 < (n : Nat)
参数：n : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2
/-
**PNat.eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：eq {m n : Nat+} : (m : Nat) = n -> m = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.ext
/-
**PNat.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_injective : Function.Injective PNat.val
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Function.Injective PNat.val :=
  Subtype.coe_injective

@[simp]
/-
**PNat.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：ne_zero (n : Nat+) : (n : Nat) != 0
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'
/-
**PNat._root_.NeZero.pnat** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.NeZero.pnat {a : ℕ+} : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩
/-
**PNat.toPNat'_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ {n : ℕ}, 0 < n → ↑n.toPNat' = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem toPNat'_coe {n : ℕ} : 0 < n → (n.toPNat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
/-
**PNat.coe_toPNat'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_toPNat' (n : Nat+) : (n : Nat).toPNat' = n
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `PNat.toPNat'_coe`：∀ {n : ℕ}, 0 < n → ↑n.toPNat' = n
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
-/
theorem coe_toPNat' (n : ℕ+) : (n : ℕ).toPNat' = n :=
  eq (toPNat'_coe n.pos)

@[deprecated "use `one_le`" (since := "2026-05-07")]
/-
**PNat.one_le** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ (n : ℕ+), 1 ≤ n
参数：n : ℕ+。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

@[deprecated "use `not_lt_one`" (since := "2026-05-07")]
/-
**PNat.not_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ (n : ℕ+), ¬n < 1
参数：n : ℕ+。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_ge n.2
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `PNat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
/-
**PNat.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mk_one {h} : (⟨1, h⟩ : Nat+) = (1 : Nat+)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl

@[norm_cast]
/-
**PNat.one_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_coe : ((1 : Nat+) : Nat) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp, norm_cast]
/-
**PNat.coe_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_eq_one_iff {m : Nat+} : (m : Nat) = 1 ↔ m = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.one_coe`：one_coe : ((1 : Nat+) : Nat) = 1
-/
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation ℕ+ :=
  measure (fun (a : ℕ+) => (a : ℕ))

/-- Strong induction on `ℕ+`. -/
/-
**PNat.strongInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：{p : ℕ+ → Sort u_1} → (n : ℕ+) → ((k : ℕ+) → ((m : ℕ+) → m < k → p m) → p 
k) → p n
参数：n : ℕ+；(k : ℕ+) → ((m : ℕ+) → m < k → p m) → p k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strong induction on `ℕ+`.
-/
def strongInductionOn {p : ℕ+ → Sort*} (n : ℕ+) : (∀ k, (∀ m, m < k → p m) → p k) → p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by n.1

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
/-
**PNat.modDivAux** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：ℕ+ → ℕ → ℕ → ℕ+ × ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | _, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
/-
**PNat.modDiv** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：modDiv (m k : Nat+) : Nat+ × Nat
参数：m k : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
/-
**PNat.mod** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：mod (m k : Nat+) : Nat+
参数：m k : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is 
always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
/-
**PNat.div** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：div (m k : Nat+) : Nat
参数：m k : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we tak
e
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. L
ater we
  define a function `div_exact` which gives the usual `m / k` in the case where 
`k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2
/-
**PNat.mod_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mod_coe (m k : Nat+) : (mod m k : Nat) = ite ((m : Nat) % (k : Nat) = 0) (
k : Nat) ((m : Nat) % (k : Nat))
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem mod_coe (m k : ℕ+) :
    (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp [mod, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl
/-
**PNat.div_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：div_coe (m k : Nat+) : (div m k : Nat) = ite ((m : Nat) % (k : Nat) = 0) (
(m : Nat) / (k : Nat)).pred ((m : Nat) / (k : Nat))
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem div_coe (m k : ℕ+) :
    (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) := by
  dsimp [div, modDiv]
  cases (m : ℕ) % (k : ℕ) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
/-
**PNat.divExact** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：divExact (m k : Nat+) : Nat+
参数：m k : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `
m / k`.
-/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩

end PNat

section CanLift

/-
**Nat.canLiftPNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.canLiftPNat : CanLift Nat Nat+ (↑) (fun n => 0 < n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.toPNat'_coe`：∀ {n : ℕ}, 0 < n → ↑n.toPNat' = n
-/
instance Nat.canLiftPNat : CanLift ℕ ℕ+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩
/-
**Int.canLiftPNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.canLiftPNat : CanLift Int Nat+ (↑) ((0 < ·))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.toPNat'_coe`：∀ (n : ℕ), ↑n.toPNat' = if 0 < n then n else 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_pos`：∀ {a : ℤ}, 0 < a.natAbs ↔ a ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
instance Int.canLiftPNat : CanLift ℤ ℕ+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe, if_pos (Int.natAbs_pos.2 hn.ne'),
        Int.natAbs_of_nonneg hn.le]⟩⟩

end CanLift

