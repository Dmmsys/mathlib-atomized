/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of continuum

In this file we define `Cardinal.continuum` (notation: `𝔠`, localized in `Cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`.
-/

@[expose] public section


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of the continuum. -/
/-
**Cardinal.continuum** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：continuum : Cardinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cardinality of the continuum.
-/
def continuum : Cardinal.{u} :=
  2 ^ ℵ₀

@[inherit_doc] scoped notation "𝔠" => Cardinal.continuum

@[simp]
/-
**Cardinal.two_power_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem two_power_aleph0 : 2 ^ ℵ₀ = 𝔠 :=
  rfl

@[simp]
/-
**Cardinal.lift_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_continuum : lift.{v} 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.two_power_aleph0`：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
· 使用定理 `Cardinal.lift_two_power`：lift_two_power (a : Cardinal) : lift.{v} (2 ^ a
) = 2 ^ lift.{v} a
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
-/
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0, lift_two_power, lift_aleph0, two_power_aleph0]

@[simp]
/-
**Cardinal.continuum_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_le_lift {c : Cardinal.{u}} : 𝔠 <= lift.{v} c ↔ 𝔠 <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuum_le_lift {c : Cardinal.{u}} : 𝔠 ≤ lift.{v} c ↔ 𝔠 ≤ c := by
  rw [← lift_continuum.{v, u}, lift_le]

@[simp]
/-
**Cardinal.lift_le_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_le_continuum {c : Cardinal.{u}} : lift.{v} c <= 𝔠 ↔ c <= 𝔠
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_le_continuum {c : Cardinal.{u}} : lift.{v} c ≤ 𝔠 ↔ c ≤ 𝔠 := by
  rw [← lift_continuum.{v, u}, lift_le]

@[simp]
/-
**Cardinal.continuum_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum.{v, u}, lift_lt]

@[simp]
/-
**Cardinal.lift_lt_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠 := by
  rw [← lift_continuum.{v, u}, lift_lt]

/-!
### Inequalities
-/


/-
**Cardinal.aleph0_lt_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_lt_continuum : ℵ₀ < 𝔠
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a

--- 原说明 ---
### Inequalities
-/
theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀
/-
**Cardinal.aleph0_le_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_le_continuum : ℵ₀ <= 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
-/
theorem aleph0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph0_lt_continuum.le

@[simp]
/-
**Cardinal.beth_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_one : ℶ_ 1 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Cardinal.beth_zero`：beth_zero : ℶ_ 0 = ℵ₀
· 使用定理 `Cardinal.beth_succ`：beth_succ (o : Ordinal) : ℶ_ (succ o) = 2 ^ ℶ_ o
-/
theorem beth_one : ℶ_ 1 = 𝔠 := by simpa using beth_succ 0
/-
**Cardinal.nat_lt_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_lt_continuum (n : Nat) : ↑n < 𝔠
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
-/
theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  natCast_lt_aleph0.trans aleph0_lt_continuum
/-
**Cardinal.mk_set_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_set_nat : #(Set Nat) = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_set`：mk_set {α : Type u} : #(Set α) = 2 ^ #α
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_set_nat : #(Set ℕ) = 𝔠 := by simp
/-
**Cardinal.continuum_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_pos : 0 < 𝔠
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_lt_continuum`：nat_lt_continuum (n : Nat) : ↑n < 𝔠
-/
theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0
/-
**Cardinal.continuum_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_ne_zero : 𝔠 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.continuum_pos`：continuum_pos : 0 < 𝔠
-/
theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'
/-
**Cardinal.aleph_one_le_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_one_le_continuum : ℵ₁ <= 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
-/
theorem aleph_one_le_continuum : ℵ₁ ≤ 𝔠 := by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum

@[simp]
/-
**Cardinal.continuum_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_toNat : toNat continuum = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
-/
theorem continuum_toNat : toNat continuum = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum

@[simp]
/-
**Cardinal.continuum_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_toENat : toENat continuum = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.toENat_eq_top`：∀ {c : Cardinal.{u}}, Cardinal.toENat c = ⊤ ↔ Ca
rdinal.aleph0 ≤ c
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
-/
theorem continuum_toENat : toENat continuum = ⊤ :=
  (toENat_eq_top.2 aleph0_le_continuum)

/-!
### Addition
-/


@[simp]
/-
**Cardinal.aleph0_add_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_eq_right`：add_eq_right {a b : Cardinal} (hb : ℵ₀ <= b) (ha 
: a <= b) : a + b = b
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠

--- 原说明 ---
### Addition
-/
theorem aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum

@[simp]
/-
**Cardinal.continuum_add_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.aleph0_add_continuum`：aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠
-/
theorem continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum

@[simp]
/-
**Cardinal.continuum_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_add_self : 𝔠 + 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_eq_self`：add_eq_self {c : Cardinal} (h : ℵ₀ <= c) : c + c =
 c
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
-/
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_self aleph0_le_continuum

@[simp]
/-
**Cardinal.nat_add_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_add_continuum (n : Nat) : ↑n + 𝔠 = 𝔠
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_add_eq`：nat_add_eq {a : Cardinal} (n : Nat) (ha : ℵ₀ <= a) 
: n + a = a
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
-/
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  nat_add_eq n aleph0_le_continuum

@[simp]
/-
**Cardinal.continuum_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_add_nat (n : Nat) : 𝔠 + n = 𝔠
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.nat_add_continuum`：nat_add_continuum (n : Nat) : ↑n + 𝔠 = 𝔠
-/
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)

@[simp]
/-
**Cardinal.ofNat_add_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_add_continuum {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) + 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_add_continuum`：nat_add_continuum (n : Nat) : ↑n + 𝔠 = 𝔠
-/
theorem ofNat_add_continuum {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) + 𝔠 = 𝔠 :=
  nat_add_continuum n

@[simp]
/-
**Cardinal.continuum_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_add_ofNat {n : Nat} [Nat.AtLeastTwo n] : 𝔠 + ofNat(n) = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.continuum_add_nat`：continuum_add_nat (n : Nat) : 𝔠 + n = 𝔠
-/
theorem continuum_add_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 + ofNat(n) = 𝔠 :=
  continuum_add_nat n

/-!
### Multiplication
-/


@[simp]
/-
**Cardinal.continuum_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_mul_self : 𝔠 * 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.continuum_ne_zero`：continuum_ne_zero : 𝔠 != 0

--- 原说明 ---
### Multiplication
-/
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero

@[simp]
/-
**Cardinal.continuum_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0
-/
theorem continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero

@[simp]
/-
**Cardinal.aleph0_mul_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.continuum_mul_aleph0`：continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠
-/
theorem aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0

@[simp]
/-
**Cardinal.nat_mul_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_mul_continuum {n : Nat} (hn : n != 0) : ↑n * 𝔠 = 𝔠
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mul_eq_right`：mul_eq_right {a b : Cardinal} (hb : ℵ₀ <= b) (ha 
: a <= b) (ha' : a != 0) : a * b = b
· 使用定理 `Cardinal.aleph0_le_continuum`：aleph0_le_continuum : ℵ₀ <= 𝔠
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.nat_lt_continuum`：nat_lt_continuum (n : Nat) : ↑n < 𝔠
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
/-
**Cardinal.continuum_mul_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_mul_nat {n : Nat} (hn : n != 0) : 𝔠 * n = 𝔠
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.nat_mul_continuum`：nat_mul_continuum {n : Nat} (hn : n != 0) : 
↑n * 𝔠 = 𝔠
-/
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

@[simp]
/-
**Cardinal.ofNat_mul_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_mul_continuum {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) * 𝔠 = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_mul_continuum`：nat_mul_continuum {n : Nat} (hn : n != 0) : 
↑n * 𝔠 = 𝔠
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
-/
theorem ofNat_mul_continuum {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) * 𝔠 = 𝔠 :=
  nat_mul_continuum (OfNat.ofNat_ne_zero n)

@[simp]
/-
**Cardinal.continuum_mul_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_mul_ofNat {n : Nat} [Nat.AtLeastTwo n] : 𝔠 * ofNat(n) = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.continuum_mul_nat`：continuum_mul_nat {n : Nat} (hn : n != 0) : 
𝔠 * n = 𝔠
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
-/
theorem continuum_mul_ofNat {n : ℕ} [Nat.AtLeastTwo n] : 𝔠 * ofNat(n) = 𝔠 :=
  continuum_mul_nat (OfNat.ofNat_ne_zero n)

/-!
### Power
-/


@[simp]
/-
**Cardinal.aleph0_power_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
### Power
-/
theorem aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠 :=
  power_self_eq le_rfl

@[simp]
/-
**Cardinal.nat_power_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_power_aleph0 {n : Nat} (hn : 2 <= n) : n ^ ℵ₀ = 𝔠
参数：hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_power_eq`：nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ <= c) {n 
: Nat} (hn : 2 <= n) : (n : Cardinal.{u}) ^ c = 2 ^ c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nat_power_aleph0 {n : ℕ} (hn : 2 ≤ n) : n ^ ℵ₀ = 𝔠 :=
  nat_power_eq le_rfl hn

@[simp]
/-
**Cardinal.continuum_power_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.two_power_aleph0`：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
· 使用定理 `Cardinal.power_mul`：power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b)
 ^ c
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Cardinal.aleph0_ne_zero`：aleph0_ne_zero : ℵ₀ != 0
-/
theorem continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := by
  rw [← two_power_aleph0, ← power_mul, mul_eq_left le_rfl le_rfl aleph0_ne_zero]
/-
**Cardinal.power_aleph0_of_le_continuum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_aleph0_of_le_continuum {x : Cardinal} (h₁ : 2 <= x) (h₂ : x <= 𝔠) : 
x ^ ℵ₀ = 𝔠
参数：h₁ : 2 <= x；h₂ : x <= 𝔠。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.continuum_power_aleph0`：continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠
· 使用定理 `Cardinal.power_le_power_right`：power_le_power_right {a b c : Cardinal} :
 a <= b -> a ^ c <= b ^ c
· 使用定理 `Cardinal.two_power_aleph0`：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
-/
theorem power_aleph0_of_le_continuum {x : Cardinal} (h₁ : 2 ≤ x) (h₂ : x ≤ 𝔠) : x ^ ℵ₀ = 𝔠 := by
  apply le_antisymm
  · rw [← continuum_power_aleph0]
    exact power_le_power_right h₂
  · rw [← two_power_aleph0]
    exact power_le_power_right h₁

end Cardinal

