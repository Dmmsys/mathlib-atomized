/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Hom.Basic

/-!
# `Fin n` forms a bounded linear order

This file contains the linear ordered instance on `Fin n`.

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `Fin.orderIsoSubtype` : coercion to `{i // i < n}` as an `OrderIso`;
* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.valOrderEmb` : coercion to natural numbers as an `OrderEmbedding`;
* `Fin.succOrderEmb` : `Fin.succ` as an `OrderEmbedding`;
* `Fin.castLEOrderEmb h` : `Fin.castLE` as an `OrderEmbedding`, embed `Fin n` into `Fin m` when
  `h : n ≤ m`;
* `Fin.castOrderIso` : `Fin.cast` as an `OrderIso`, order isomorphism between `Fin n` and `Fin m`
  provided that `n = m`, see also `Equiv.finCongr`;
* `Fin.castAddOrderEmb m` : `Fin.castAdd` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccOrderEmb` : `Fin.castSucc` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatOrderEmb m i` : `Fin.addNat` as an `OrderEmbedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddOrderEmb n i` : `Fin.natAdd` as an `OrderEmbedding`, adds `n` on `i` on the left;
* `Fin.revOrderIso`: `Fin.rev` as an `OrderIso`, the antitone involution given by `i ↦ n-(i+1)`
-/

@[expose] public section

assert_not_exists Monoid

open Function Nat Set

namespace Fin
variable {m n : ℕ}

/-! ### Instances -/

/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Instances
-/
instance : Max (Fin n) where max x y := ⟨max x y, max_rec' (· < n) x.2 y.2⟩
/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Fin n) where min x y := ⟨min x y, min_rec' (· < n) x.2 y.2⟩

@[simp, norm_cast]
/-
**Fin.coe_max** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_max (a b : Fin n) : ↑(max a b) = (max a b : Nat)
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_max (a b : Fin n) : ↑(max a b) = (max a b : ℕ) := rfl

@[simp, norm_cast]
/-
**Fin.coe_min** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_min (a b : Fin n) : ↑(min a b) = (min a b : Nat)
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_min (a b : Fin n) : ↑(min a b) = (min a b : ℕ) := rfl
/-
**Fin.compare_eq_compare_val** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：compare_eq_compare_val (a b : Fin n) : compare a b = compare a.val b.val
参数：a b : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compare_eq_compare_val (a b : Fin n) : compare a b = compare a.val b.val := rfl
/-
**Fin.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instLinearOrder : LinearOrder (Fin n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_injective`：val_injective : Function.Injective (@Fin.val n)
· 使用定理 `Fin.le_iff_val_le_val`：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : N
at) <= b
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.coe_min`：coe_min (a b : Fin n) : ↑(min a b) = (min a b : Nat)
· 使用定理 `Fin.coe_max`：coe_max (a b : Fin n) : ↑(max a b) = (max a b : Nat)
· 使用定理 `Fin.compare_eq_compare_val`：compare_eq_compare_val (a b : Fin n) : compa
re a b = compare a.val b.val
-/
instance instLinearOrder : LinearOrder (Fin n) :=
  Fin.val_injective.linearOrder _
    Fin.le_iff_val_le_val Fin.lt_def coe_min coe_max compare_eq_compare_val
/-
**Fin.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instBoundedOrder [NeZero n] : BoundedOrder (Fin n) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
instance instBoundedOrder [NeZero n] : BoundedOrder (Fin n) where
  top := rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le
/-
**Fin.instBiheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instBiheytingAlgebra [NeZero n] : BiheytingAlgebra (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBiheytingAlgebra [NeZero n] : BiheytingAlgebra (Fin n) :=
  LinearOrder.toBiheytingAlgebra (Fin n)

/- There is a slight asymmetry here, in the sense that `0` is of type `Fin n` when we have
`[NeZero n]` whereas `last n` is of type `Fin (n + 1)`. To address this properly would
require a change to std4, defining `NeZero n` and thus re-defining `last n`
(and possibly make its argument implicit) as `rev 0`, of type `Fin n`. As we can see from these
lemmas, this would be equivalent to the existing definition. -/

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

/-
**Fin.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instPartialOrder : PartialOrder (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instan
ces non-computably.
-/
instance instPartialOrder : PartialOrder (Fin n) := inferInstance
/-
**Fin.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instLattice : Lattice (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice : Lattice (Fin n) := inferInstance
/-
**Fin.instHeytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instHeytingAlgebra [NeZero n] : HeytingAlgebra (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHeytingAlgebra [NeZero n] : HeytingAlgebra (Fin n) := inferInstance
/-
**Fin.instCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：instCoheytingAlgebra [NeZero n] : CoheytingAlgebra (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoheytingAlgebra [NeZero n] : CoheytingAlgebra (Fin n) := inferInstance

/-! ### Miscellaneous lemmas -/

/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Miscellaneous lemmas
-/
instance [NeZero n] : IsBotZeroClass (Fin n) where
  isBot_zero := isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/-
**Fin.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ) [inst : NeZero n], ⊥ = 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
-/
protected lemma bot_eq_zero (n : ℕ) [NeZero n] : ⊥ = (0 : Fin n) := _root_.bot_eq_zero
/-
**Fin.top_eq_last** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：top_eq_last (n : Nat) : ⊤ = Fin.last n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma top_eq_last (n : ℕ) : ⊤ = Fin.last n := rfl
/-
**Fin.rev_bot** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n], ⊥.rev = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rev_bot [NeZero n] : rev (⊥ : Fin n) = ⊤ := rfl
/-
**Fin.rev_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n], ⊤.rev = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
-/
@[simp] theorem rev_top [NeZero n] : rev (⊤ : Fin n) = ⊥ := rev_rev _
/-
**Fin.rev_zero_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_zero_eq_top (n : Nat) [NeZero n] : rev (0 : Fin n) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rev_zero_eq_top (n : ℕ) [NeZero n] : rev (0 : Fin n) = ⊤ := rfl
/-
**Fin.rev_last_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：rev_last_eq_bot (n : Nat) : rev (last n) = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
-/
theorem rev_last_eq_bot (n : ℕ) : rev (last n) = ⊥ := by rw [rev_last, bot_eq_zero]

@[simp]
/-
**Fin.succ_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succ_top (n : Nat) [NeZero n] : (⊤ : Fin n).succ = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.rev_zero_eq_top`：rev_zero_eq_top (n : Nat) [NeZero n] : rev (0 : Fin
 n) = ⊤
· 使用定理 `Fin.rev_castSucc`：∀ {n : ℕ} (k : Fin n), k.castSucc.rev = k.rev.succ
· 使用定理 `Fin.castSucc_zero'`：castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0
-/
theorem succ_top (n : ℕ) [NeZero n] : (⊤ : Fin n).succ = ⊤ := by
  rw [← rev_zero_eq_top, ← rev_zero_eq_top, ← rev_castSucc, castSucc_zero']

@[simp]
/-
**Fin.val_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：val_top (n : Nat) [NeZero n] : ((⊤ : Fin n) : Nat) = n - 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_top (n : ℕ) [NeZero n] : ((⊤ : Fin n) : ℕ) = n - 1 := rfl

@[simp]
/-
**Fin.zero_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：zero_eq_top {n : Nat} [NeZero n] : (0 : Fin n) = ⊤ ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `Fin.subsingleton_iff_le_one`：∀ {n : ℕ}, Subsingleton (Fin n) ↔ n ≤ 1
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_eq_top {n : ℕ} [NeZero n] : (0 : Fin n) = ⊤ ↔ n = 1 := by
  rw [← bot_eq_zero, subsingleton_iff_bot_eq_top, subsingleton_iff_le_one,
    le_one_iff_eq_zero_or_eq_one, or_iff_right (NeZero.ne n)]

@[simp]
/-
**Fin.top_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：top_eq_zero {n : Nat} [NeZero n] : (⊤ : Fin n) = 0 ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Fin.zero_eq_top`：zero_eq_top {n : Nat} [NeZero n] : (0 : Fin n) = ⊤ ↔ n 
= 1
-/
theorem top_eq_zero {n : ℕ} [NeZero n] : (⊤ : Fin n) = 0 ↔ n = 1 :=
  eq_comm.trans zero_eq_top

@[simp]
/-
**Fin.cast_top** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cast_top {m n : Nat} [NeZero m] [NeZero n] (h : m = n) : (⊤ : Fin m).cast 
h = ⊤
参数：h : m = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_top {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) : (⊤ : Fin m).cast h = ⊤ := by
  simp [← val_inj, h]

section ToFin
variable {α : Type*} [Preorder α] {f : α → Fin (n + 1)}

/-
**Fin.strictMono_pred_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_pred_comp (hf : forall a, f a != 0) (hf₂ : StrictMono f) : Stri
ctMono (fun a => pred (f a) (hf a))
参数：hf : forall a, f a != 0；hf₂ : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pred_lt_pred_iff`：∀ {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b 
≠ 0}, a.pred ha < b.pred hb ↔ a < b
-/
lemma strictMono_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : StrictMono f) :
    StrictMono (fun a => pred (f a) (hf a)) := fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)
/-
**Fin.monotone_pred_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：monotone_pred_comp (hf : forall a, f a != 0) (hf₂ : Monotone f) : Monotone
 (fun a => pred (f a) (hf a))
参数：hf : forall a, f a != 0；hf₂ : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.pred_le_pred_iff`：∀ {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b 
≠ 0}, a.pred ha ≤ b.pred hb ↔ a ≤ b
-/
lemma monotone_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : Monotone f) :
    Monotone (fun a => pred (f a) (hf a)) := fun _ _ h => pred_le_pred_iff.2 (hf₂ h)
/-
**Fin.strictMono_castPred_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_castPred_comp (hf : forall a, f a != last n) (hf₂ : StrictMono 
f) : StrictMono (fun a => castPred (f a) (hf a))
参数：hf : forall a, f a != last n；hf₂ : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castPred_lt_castPred_iff`：castPred_lt_castPred_iff {i j : Fin (n + 1
)} {hi : i != last n} {hj : j != last n} : castPred i hi < castPred j hj ↔ i < j
-/
lemma strictMono_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : StrictMono f) :
    StrictMono (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)
/-
**Fin.monotone_castPred_comp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：monotone_castPred_comp (hf : forall a, f a != last n) (hf₂ : Monotone f) :
 Monotone (fun a => castPred (f a) (hf a))
参数：hf : forall a, f a != last n；hf₂ : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castPred_le_castPred_iff`：castPred_le_castPred_iff {i j : Fin (n + 1
)} {hi : i != last n} {hj : j != last n} : castPred i hi <= castPred j hj ↔ i <=
 j
-/
lemma monotone_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : Monotone f) :
    Monotone (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

end ToFin

section FromFin
variable {α : Type*} [Preorder α] {f : Fin (n + 1) → α}

/-- A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
/-
**Fin.strictMono_iff_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_iff_lt_succ : StrictMono f ↔ forall i : Fin n, f (castSucc i) <
 f i.succ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2

--- 原说明 ---
A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i 
+ 1)`
for all `i`.
-/
lemma strictMono_iff_lt_succ : StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)

/-- A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
/-
**Fin.monotone_iff_le_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：monotone_iff_le_succ : Monotone f ↔ forall i : Fin n, f (castSucc i) <= f 
i.succ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2

--- 原说明 ---
A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for
 all `i`.
-/
lemma monotone_iff_le_succ : Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)

/-- A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
/-
**Fin.strictAnti_iff_succ_lt** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictAnti_iff_succ_lt : StrictAnti f ↔ forall i : Fin n, f i.succ < f (ca
stSucc i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1

--- 原说明 ---
A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) <
 f i`
for all `i`.
-/
lemma strictAnti_iff_succ_lt : StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)

/-- A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
/-
**Fin.antitone_iff_succ_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：antitone_iff_succ_le : Antitone f ↔ forall i : Fin n, f i.succ <= f (castS
ucc i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
· 使用定理 `Fin.liftFun_iff_succ`：liftFun_iff_succ {α : Type*} (r : α -> α -> Prop) 
[IsTrans α r] {f : Fin (n + 1) -> α} : ((· < ·) ⇒ r) f f ↔ forall i : Fin n, r (
f (castSuc…
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1

--- 原说明 ---
A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for
 all `i`.
-/
lemma antitone_iff_succ_le : Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)
/-
**Fin.orderHom_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderHom_injective_iff {α : Type*} [PartialOrder α] {n : Nat} (f : Fin (n 
+ 1) ->o α) : Function.Injective f ↔ forall (i : Fin n), f i.castSucc != f i.suc
c
参数：f : Fin (n + 1) ->o α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
-/
lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
    Function.Injective f ↔ ∀ (i : Fin n), f i.castSucc ≠ f i.succ := by
  constructor
  · intro hf i hi
    have := hf hi
    simp [Fin.ext_iff] at this
  · intro hf
    refine (strictMono_iff_lt_succ (f := f).2 fun i ↦ ?_).injective
    exact lt_of_le_of_ne (f.monotone (Fin.castSucc_le_succ i)) (hf i)

end FromFin

/-! #### Monotonicity -/

/-
**Fin.val_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：val_strictMono : StrictMono (val : Fin n -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### Monotonicity
-/
lemma val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ ↦ id
/-
**Fin.cast_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：cast_strictMono {k l : Nat} (h : k = l) : StrictMono (Fin.cast h)
参数：h : k = l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cast_strictMono {k l : ℕ} (h : k = l) : StrictMono (Fin.cast h) := fun {_ _} h ↦ h
/-
**Fin.strictMono_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_succ : StrictMono (succ : Fin n -> Fin (n + 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
-/
lemma strictMono_succ : StrictMono (succ : Fin n → Fin (n + 1)) := fun _ _ ↦ succ_lt_succ
/-
**Fin.strictMono_castLE** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_castLE (h : n <= m) : StrictMono (castLE h : Fin n -> Fin m)
参数：h : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strictMono_castLE (h : n ≤ m) : StrictMono (castLE h : Fin n → Fin m) := fun _ _ ↦ id
/-
**Fin.strictMono_castAdd** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_castAdd (m) : StrictMono (castAdd m : Fin n -> Fin (n + m))
参数：m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_castLE`：strictMono_castLE (h : n <= m) : StrictMono (cast
LE h : Fin n -> Fin m)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
lemma strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) := strictMono_castLE _
/-
**Fin.strictMono_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_castSucc : StrictMono (castSucc : Fin n -> Fin (n + 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_castAdd`：strictMono_castAdd (m) : StrictMono (castAdd m :
 Fin n -> Fin (n + m))
-/
lemma strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) := strictMono_castAdd _
/-
**Fin.strictMono_natAdd** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_natAdd (n) : StrictMono (natAdd n : Fin m -> Fin (n + m))
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
-/
lemma strictMono_natAdd (n) : StrictMono (natAdd n : Fin m → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_left (show i.val < j.val from h) _
/-
**Fin.strictMono_addNat** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n -> Fin (n + m))
参数：m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
-/
lemma strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_right (show i.val < j.val from h) _
/-
**Fin.strictMono_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p)
参数：p : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.ite`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: Preorder β] {f g : α → β},   StrictMono f →     StrictMono g →       ∀ {p : α 
→ Pr…
· 使用引理 `Fin.strictMono_castSucc`：strictMono_castSucc : StrictMono (castSucc : Fi
n n -> Fin (n + 1))
· 使用引理 `Fin.strictMono_succ`：strictMono_succ : StrictMono (succ : Fin n -> Fin (
n + 1))
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
-/
lemma strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun _ => castSucc_lt_succ.le

variable {p : Fin (n + 1)} {i j : Fin n}

@[simp]
/-
**Fin.succAbove_inj** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_inj : succAbove p i = succAbove p j ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
-/
lemma succAbove_inj : succAbove p i = succAbove p j ↔ i = j :=
  (strictMono_succAbove p).injective.eq_iff

@[simp, gcongr]
/-
**Fin.succAbove_le_succAbove_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_le_succAbove_iff : succAbove p i <= succAbove p j ↔ i <= j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
-/
lemma succAbove_le_succAbove_iff : succAbove p i ≤ succAbove p j ↔ i ≤ j :=
  (strictMono_succAbove p).le_iff_le

@[simp, gcongr]
/-
**Fin.succAbove_lt_succAbove_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
-/
lemma succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j :=
  (strictMono_succAbove p).lt_iff_lt

@[simp]
/-
**Fin.natAdd_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natAdd_inj (m) {i j : Fin n} : natAdd m i = natAdd m j ↔ i = j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
-/
theorem natAdd_inj (m) {i j : Fin n} : natAdd m i = natAdd m j ↔ i = j :=
  (strictMono_natAdd _).injective.eq_iff
/-
**Fin.natAdd_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natAdd_injective (m n : Nat) : Function.Injective (Fin.natAdd n : Fin m ->
 _)
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
-/
theorem natAdd_injective (m n : ℕ) :
    Function.Injective (Fin.natAdd n : Fin m → _) :=
  (strictMono_natAdd _).injective

@[simp, gcongr]
/-
**Fin.natAdd_le_natAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natAdd_le_natAdd_iff (m) {i j : Fin n} : natAdd m i <= natAdd m j ↔ i <= j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
-/
theorem natAdd_le_natAdd_iff (m) {i j : Fin n} : natAdd m i ≤ natAdd m j ↔ i ≤ j :=
  (strictMono_natAdd _).le_iff_le

@[simp, gcongr]
/-
**Fin.natAdd_lt_natAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：natAdd_lt_natAdd_iff (m) {i j : Fin n} : natAdd m i < natAdd m j ↔ i < j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))
-/
theorem natAdd_lt_natAdd_iff (m) {i j : Fin n} : natAdd m i < natAdd m j ↔ i < j :=
  (strictMono_natAdd _).lt_iff_lt

@[simp]
/-
**Fin.addNat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：addNat_inj (m) {i j : Fin n} : i.addNat m = j.addNat m ↔ i = j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
-/
theorem addNat_inj (m) {i j : Fin n} : i.addNat m = j.addNat m ↔ i = j :=
  (strictMono_addNat _).injective.eq_iff

@[simp, gcongr]
/-
**Fin.addNat_le_addNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：addNat_le_addNat_iff (m) {i j : Fin n} : i.addNat m <= j.addNat m ↔ i <= j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
-/
theorem addNat_le_addNat_iff (m) {i j : Fin n} : i.addNat m ≤ j.addNat m ↔ i ≤ j :=
  (strictMono_addNat _).le_iff_le

@[simp, gcongr]
/-
**Fin.addNat_lt_addNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：addNat_lt_addNat_iff (m) {i j : Fin n} : i.addNat m < j.addNat m ↔ i < j
参数：m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))
-/
theorem addNat_lt_addNat_iff (m) {i j : Fin n} : i.addNat m < j.addNat m ↔ i < j :=
  (strictMono_addNat _).lt_iff_lt

@[simp, gcongr]
/-
**Fin.castLE_le_castLE_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castLE_le_castLE_iff {i j : Fin n} (h : n <= m) : i.castLE h <= j.castLE h
 ↔ i <= j
参数：h : n <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castLE_le_castLE_iff {i j : Fin n} (h : n ≤ m) : i.castLE h ≤ j.castLE h ↔ i ≤ j := .rfl

@[simp, gcongr]
/-
**Fin.castLE_lt_castLE_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：castLE_lt_castLE_iff {i j : Fin n} (h : n <= m) : i.castLE h < j.castLE h 
↔ i < j
参数：h : n <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem castLE_lt_castLE_iff {i j : Fin n} (h : n ≤ m) : i.castLE h < j.castLE h ↔ i < j := .rfl
/-
**Fin.predAbove_right_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_right_monotone (p : Fin n) : Monotone p.predAbove
参数：p : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.pred_le_pred`：∀ {n m : ℕ}, n ≤ m → n.pred ≤ m.pred
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
lemma predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, val_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H
/-
**Fin.predAbove_left_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p => predAbove p 
i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p ↦ predAbove p i := fun a b H ↦ by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_ge
  · rfl

@[gcongr]
/-
**Fin.predAbove_le_predAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_le_predAbove {p q : Fin n} (hpq : p <= q) {i j : Fin (n + 1)} (h
ij : i <= j) : p.predAbove i <= q.predAbove j
参数：hpq : p <= q；n + 1；hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Fin.predAbove_right_monotone`：predAbove_right_monotone (p : Fin n) : Mon
otone p.predAbove
· 使用引理 `Fin.predAbove_left_monotone`：predAbove_left_monotone (i : Fin (n + 1)) :
 Monotone fun p => predAbove p i
-/
lemma predAbove_le_predAbove {p q : Fin n} (hpq : p ≤ q) {i j : Fin (n + 1)} (hij : i ≤ j) :
    p.predAbove i ≤ q.predAbove j :=
  (predAbove_right_monotone p hij).trans (predAbove_left_monotone j hpq)

/-- `Fin.predAbove p` as an `OrderHom`. -/
/-
**Fin.predAboveOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：{n : ℕ} → Fin n → Fin (n + 1) →o Fin n
参数：n + 1。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_right_monotone`：predAbove_right_monotone (p : Fin n) : Mon
otone p.predAbove

--- 原说明 ---
`Fin.predAbove p` as an `OrderHom`.
-/
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩

/-- `predAbove` is injective at the pivot -/
/-
**Fin.predAbove_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：predAbove_left_injective : Injective (@predAbove n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.exists_add_one_eq`：∀ {a : ℕ}, (∃ n, n + 1 = a) ↔ 0 < a
· 使用引理 `Fin.size_positive`：size_positive : Fin n -> 0 < n
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.castSucc_inj`：∀ {n : ℕ} {a b : Fin n}, a.castSucc = b.castSucc ↔ a =
 b
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Fin.predAbove_succ_self`：∀ {n : ℕ} (p : Fin n), p.predAbove p.succ = p
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b

--- 原说明 ---
`predAbove` is injective at the pivot
-/
lemma predAbove_left_injective : Injective (@predAbove n) := by
  intro i j hij
  obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.2 i.size_positive
  wlog! h : i < j generalizing i j
  · obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  replace hij := congr_fun hij i.succ
  rw [predAbove_succ_self, Fin.predAbove_of_le_castSucc _ _ (by simpa),
    ← Fin.castSucc_inj, castSucc_castPred] at hij
  exact (i.castSucc_lt_succ.ne hij).elim

/-- `predAbove` is injective at the pivot -/
/-
**Fin.predAbove_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {x y : Fin n}, x.predAbove = y.predAbove ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Fin.predAbove_left_injective`：predAbove_left_injective : Injective (@pre
dAbove n)

--- 原说明 ---
`predAbove` is injective at the pivot
-/
@[simp] lemma predAbove_left_inj {x y : Fin n} : x.predAbove = y.predAbove ↔ x = y :=
  predAbove_left_injective.eq_iff

/-! #### Order isomorphisms -/

/-- The equivalence `Fin n ≃ {i // i < n}` is an order isomorphism. -/
@[simps! apply symm_apply]
/-
**Fin.orderIsoSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：orderIsoSubtype : Fin n ≃o {i // i < n}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Fin n ≃ {i // i < n}` is an order isomorphism.
-/
def orderIsoSubtype : Fin n ≃o {i // i < n} :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

/-- `Fin.cast` as an `OrderIso`.

`castOrderIso eq i` embeds `i` into an equal `Fin` type. -/
@[simps]
/-
**Fin.castOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castOrderIso (eq : n = m) : Fin n ≃o Fin m where toEquiv
参数：eq : n = m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.leftInverse_cast`：leftInverse_cast (eq : n = m) : LeftInverse (Fin.c
ast eq.symm) (Fin.cast eq)
· 使用定理 `Fin.rightInverse_cast`：rightInverse_cast (eq : n = m) : RightInverse (Fi
n.cast eq.symm) (Fin.cast eq)
· 使用定理 `Fin.cast_le_cast`：cast_le_cast (eq : n = m) {a b : Fin n} : a.cast eq <=
 b.cast eq ↔ a <= b

--- 原说明 ---
`Fin.cast` as an `OrderIso`.

`castOrderIso eq i` embeds `i` into an equal `Fin` type.
-/
def castOrderIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨Fin.cast eq, Fin.cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq

@[simp]
/-
**Fin.symm_castOrderIso** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.sym
m
参数：h : n = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm := by subst h; rfl

@[simp]
/-
**Fin.castOrderIso_refl** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castOrderIso_refl (h : n = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.castOrderIso_apply`：∀ {m n : ℕ} (eq : n = m) (i : Fin n), (Fin.castO
rderIso eq) i = Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; simp

/-- While in many cases `Fin.castOrderIso` is better than `Equiv.cast`/`cast`, sometimes we want to
apply a generic lemma about `cast`. -/
/-
**Fin.castOrderIso_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (
h ▸ rfl)
参数：h : n = m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While in many cases `Fin.castOrderIso` is better than `Equiv.cast`/`cast`, somet
imes we want to
apply a generic lemma about `cast`.
-/
lemma castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; rfl

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
/-
**Fin.revOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：revOrderIso : (Fin n)ᵒᵈ ≃o Fin n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`Fin.rev n` as an order-reversing isomorphism.
-/
def revOrderIso : (Fin n)ᵒᵈ ≃o Fin n := ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩

@[simp]
/-
**Fin.revOrderIso_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual
 (rev i)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) := rfl
/-
**Fin.rev_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_strictAnti : StrictAnti (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.rev_lt_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev < j.rev ↔ j < i
-/
lemma rev_strictAnti : StrictAnti (@rev n) := fun _ _ ↦ rev_lt_rev.mpr
/-
**Fin.rev_anti** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：rev_anti : Antitone (@rev n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用引理 `Fin.rev_strictAnti`：rev_strictAnti : StrictAnti (@rev n)
-/
lemma rev_anti : Antitone (@rev n) := rev_strictAnti.antitone

/-! #### Order embeddings -/

/-- The inclusion map `Fin n → ℕ` is an order embedding. -/
@[simps! apply]
/-
**Fin.valOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：valOrderEmb (n) : Fin n ↪o Nat
参数：n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map `Fin n → ℕ` is an order embedding.
-/
def valOrderEmb (n) : Fin n ↪o ℕ := ⟨valEmbedding, Iff.rfl⟩

namespace OrderEmbedding

@[simps]
/-
**Fin.OrderEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `Fin.OrderEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Fin n ↪o ℕ) where
  default := Fin.valOrderEmb n

end OrderEmbedding

/-- The ordering on `Fin n` is a well order. -/
/-
**Fin.Lt.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Lt`。
形式化陈述：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
参数：n : ℕ；Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.isWellOrder`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] [IsWellOrder β fun x1 x2 => x1 < x2]   (f : α ↪o β
), IsWellOrder α…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
The ordering on `Fin n` is a well order.
-/
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) := (valOrderEmb n).isWellOrder

/-- `Fin.succ` as an `OrderEmbedding` -/
/-
**Fin.succOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succOrderEmb (n : Nat) : Fin n ↪o Fin (n + 1)
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_succ`：strictMono_succ : StrictMono (succ : Fin n -> Fin (
n + 1))

--- 原说明 ---
`Fin.succ` as an `OrderEmbedding`
-/
def succOrderEmb (n : ℕ) : Fin n ↪o Fin (n + 1) := .ofStrictMono succ strictMono_succ
/-
**Fin.coe_succOrderEmb** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, ⇑(Fin.succOrderEmb n) = Fin.succ
参数：Fin.succOrderEmb n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_succOrderEmb : ⇑(succOrderEmb n) = Fin.succ := rfl
/-
**Fin.succOrderEmb_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ}, (Fin.succOrderEmb n).toEmbedding = Fin.succEmb n
参数：Fin.succOrderEmb n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma succOrderEmb_toEmbedding : (succOrderEmb n).toEmbedding = succEmb n := rfl

/-- `Fin.castLE` as an `OrderEmbedding`.

`castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps! apply toEmbedding]
/-
**Fin.castLEOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castLEOrderEmb (h : n <= m) : Fin n ↪o Fin m
参数：h : n <= m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_castLE`：strictMono_castLE (h : n <= m) : StrictMono (cast
LE h : Fin n -> Fin m)

--- 原说明 ---
`Fin.castLE` as an `OrderEmbedding`.

`castLEEmb h i` embeds `i` into a larger `Fin` type.
-/
def castLEOrderEmb (h : n ≤ m) : Fin n ↪o Fin m := .ofStrictMono (castLE h) (strictMono_castLE h)

/-- `Fin.castAdd` as an `OrderEmbedding`.

`castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
/-
**Fin.castAddOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castAddOrderEmb (m) : Fin n ↪o Fin (n + m)
参数：m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_castAdd`：strictMono_castAdd (m) : StrictMono (castAdd m :
 Fin n -> Fin (n + m))

--- 原说明 ---
`Fin.castAdd` as an `OrderEmbedding`.

`castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAddEmb` and
 `Fin.addNatEmb`.
-/
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (castAdd m) (strictMono_castAdd m)

/-- `Fin.castSucc` as an `OrderEmbedding`.

`castSuccOrderEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
/-
**Fin.castSuccOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：castSuccOrderEmb : Fin n ↪o Fin (n + 1)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_castSucc`：strictMono_castSucc : StrictMono (castSucc : Fi
n n -> Fin (n + 1))

--- 原说明 ---
`Fin.castSucc` as an `OrderEmbedding`.

`castSuccOrderEmb i` embeds `i : Fin n` in `Fin (n+1)`.
-/
def castSuccOrderEmb : Fin n ↪o Fin (n + 1) := .ofStrictMono castSucc strictMono_castSucc

/-- `Fin.addNat` as an `OrderEmbedding`.

`addNatOrderEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply toEmbedding]
/-
**Fin.addNatOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：addNatOrderEmb (m) : Fin n ↪o Fin (n + m)
参数：m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_addNat`：strictMono_addNat (m) : StrictMono ((addNat · m) 
: Fin n -> Fin (n + m))

--- 原说明 ---
`Fin.addNat` as an `OrderEmbedding`.

`addNatOrderEmb m i` adds `m` to `i`, generalizes `Fin.succ`.
-/
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (addNat · m) (strictMono_addNat m)

/-- `Fin.natAdd` as an `OrderEmbedding`.

`natAddOrderEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply toEmbedding]
/-
**Fin.natAddOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：natAddOrderEmb (n) : Fin m ↪o Fin (n + m)
参数：n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_natAdd`：strictMono_natAdd (n) : StrictMono (natAdd n : Fi
n m -> Fin (n + m))

--- 原说明 ---
`Fin.natAdd` as an `OrderEmbedding`.

`natAddOrderEmb n i` adds `n` to `i` "on the left".
-/
def natAddOrderEmb (n) : Fin m ↪o Fin (n + m) := .ofStrictMono (natAdd n) (strictMono_natAdd n)

/-- `Fin.succAbove p` as an `OrderEmbedding`. -/
@[simps! apply toEmbedding]
/-
**Fin.succAboveOrderEmb** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1)
参数：p : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)

--- 原说明 ---
`Fin.succAbove p` as an `OrderEmbedding`.
-/
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)

@[simp]
/-
**Fin.range_succAboveOrderEmb** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：range_succAboveOrderEmb {n : Nat} (i : Fin (n + 1)) : Set.range (Fin.succA
boveOrderEmb i) = {i}ᶜ
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `Fin.succAboveOrderEmb_apply`：∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.
succAboveOrderEmb i = p.succAbove i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    Set.range (Fin.succAboveOrderEmb i) = {i}ᶜ := by
  aesop

/-! ### Uniqueness of order isomorphisms -/

variable {α : Type*} [Preorder α]

/-- If `e` is an `orderIso` between `Fin n` and `Fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : Fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
/-
**Fin.coe_orderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {m n : ℕ} (e : Fin n ≃o Fin m) (i : Fin n), ↑(e i) = ↑i
参数：e : Fin n ≃o Fin m；i : Fin n；e i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_lt_iff_le`：forall_lt_iff_le : (forall ⦃c⦄, c < a -> c < b) ↔ a <=
 b
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `OrderIso.lt_symm_apply`：lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
 e.symm y ↔ e x < y
· 使用定理 `Fin.mk_lt_of_lt_val`：∀ {n : ℕ} {b : Fin n} {a : ℕ} (h : a < ↑b), ⟨a, ⋯⟩ 
< b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y

--- 原说明 ---
If `e` is an `orderIso` between `Fin n` and `Fin m`, then `n = m` and `e` is the
 identity
map. In this lemma we state that for each `i : Fin n` we have `(e i : ℕ) = (i : 
ℕ)`.
-/
@[simp] lemma coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction i using Nat.strong_induction_on with | _ i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_symm_apply.1 (mk_lt_of_lt_val hj)
    specialize h _ this (e.symm _).is_lt
    simp only [Fin.eta, OrderIso.apply_symm_apply] at h
    rwa [h]
  · rwa [← h j hj (hj.trans hi), ← lt_def, e.lt_iff_lt]

end Fin

