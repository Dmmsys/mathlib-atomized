/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Algebra.CharZero.Defs

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modEq_and_modEq_iff_modEq_mul`.

## Notation

`a ≡ b [MOD n]` is notation for `Nat.ModEq n a b`, which is defined to mean `a % n = b % n`.

## Tags

ModEq, congruence, mod, MOD, modulo
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Function.support

/-- Modular equality. `n.ModEq a b`, or `a ≡ b [MOD n]`, means that `a % n = b % n`. -/
/-
**Nat.ModEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.ModEq (n a b : Nat)
参数：n a b : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Modular equality. `n.ModEq a b`, or `a ≡ b [MOD n]`, means that `a % n = b % n`.
-/
def Nat.ModEq (n a b : ℕ) :=
  a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => Nat.ModEq n a b

namespace AddCommGroup

@[simp]
/-
**AddCommGroup.modEq_iff_natModEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_natModEq {a b n : Nat} : a ≡ b [PMOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `Nat.ModEq.eq_1`：∀ (n a b : ℕ), (a ≡ b [MOD n]) = (a % n = b % n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.mul_add_mod_self_right`：∀ (a b c : ℕ), (a * b + c) % b = c % b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod'`：∀ (a b : ℕ), a / b * b + a % b = a
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n
· 使用定理 `AddCommGroup.ModEq.trans`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b
 c p : M}, a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p]
· 使用定理 `AddCommGroup.nsmul_add_modEq`：nsmul_add_modEq (n : Nat) : n • p + a ≡ a 
[PMOD p]
· 使用定理 `AddCommGroup.ModEq.symm`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b 
p : M}, a ≡ b [PMOD p] → b ≡ a [PMOD p]
-/
theorem modEq_iff_natModEq {a b n : ℕ} : a ≡ b [PMOD n] ↔ a ≡ b [MOD n] := by
  constructor
  · rw [modEq_iff_nsmul, Nat.ModEq]
    rintro ⟨k, l, h⟩
    simpa using congr($h % n)
  · rw [Nat.ModEq]
    intro h
    rw [← Nat.div_add_mod' a n, ← Nat.div_add_mod' b n, ← Nat.nsmul_eq_mul, ← Nat.nsmul_eq_mul, h]
    exact nsmul_add_modEq _ |>.trans (nsmul_add_modEq _).symm

variable {M : Type*} [AddCommMonoidWithOne M]
/-
**AddCommGroup.ModEq.natCast** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoidWithOne M] {a b n : ℕ}, a ≡ b [MOD n
] → ↑a ≡ ↑b [PMOD ↑n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.map`：map {N F : Type*} [AddCommMonoid N] [FunLike F M
 N] [AddMonoidHomClass F M N] (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p
]
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGroup.modEq_iff_natModEq`：modEq_iff_natModEq {a b n : Nat} : a ≡ 
b [PMOD n] ↔ a ≡ b [MOD n]
-/
theorem ModEq.natCast {a b n : ℕ} (h : a ≡ b [MOD n]) : a ≡ b [PMOD (n : M)] := by
  rw [← modEq_iff_natModEq] at h
  exact h.map (Nat.castAddMonoidHom M)

@[simp, norm_cast]
/-
**AddCommGroup.natCast_modEq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：natCast_modEq_natCast [CharZero M] {a b n : Nat} : a ≡ b [PMOD (n : M)] ↔ 
a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.map_modEq_iff`：map_modEq_iff {N F : Type*} [AddCommMonoid N
] [FunLike F M N] [AddMonoidHomClass F M N] (f : F) (hf : Function.Injective f) 
: f a ≡ f b [PMO…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
theorem natCast_modEq_natCast [CharZero M] {a b n : ℕ} : a ≡ b [PMOD (n : M)] ↔ a ≡ b [MOD n] := by
  simpa using map_modEq_iff (Nat.castAddMonoidHom M) Nat.cast_injective

alias ⟨_root_.Nat.ModEq.of_natCast, _⟩ := natCast_modEq_natCast

end AddCommGroup

namespace Nat

variable {m n a b c d : ℕ}

-- Since `ModEq` is semi-reducible, we need to provide the decidable instance manually
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Decidable (ModEq n a b) := inferInstanceAs <| Decidable (a % n = b % n)

namespace ModEq

@[refl]
/-
**Nat.ModEq.refl** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]
参数：a : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem refl (a : ℕ) : a ≡ a [MOD n] := rfl
/-
**Nat.ModEq.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a : ℕ}, a ≡ a [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.refl`：∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]
-/
protected theorem rfl : a ≡ a [MOD n] :=
  ModEq.refl _
/-
**Nat.ModEq.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.ModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
/-
**Nat.ModEq.symm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] :=
  Eq.symm

@[trans]
/-
**Nat.ModEq.trans** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] :=
  Eq.trans
/-
**Nat.ModEq.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.ModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (ModEq n) (ModEq n) (ModEq n) where
  trans := Nat.ModEq.trans
/-
**Nat.ModEq.comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] :=
  ⟨ModEq.symm, ModEq.symm⟩

end ModEq

/-
**Nat.modEq_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ModEq.eq_1`：∀ (n a b : ℕ), (a ≡ b [MOD n]) = (a % n = b % n)
· 使用定理 `Nat.zero_mod`：∀ (b : ℕ), 0 % b = 0
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a := by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]
/-
**Nat._root_.Dvd.dvd.modEq_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dvd.dvd.modEq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] :=
  modEq_zero_iff_dvd.2 h
/-
**Nat._root_.Dvd.dvd.zero_modEq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dvd.dvd.zero_modEq_nat (h : n ∣ a) : 0 ≡ a [MOD n] :=
  h.modEq_zero_nat.symm
/-
**Nat.modEq_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ModEq.eq_1`：∀ (n a b : ℕ), (a ≡ b [MOD n]) = (a % n = b % n)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.natCast_mod`：∀ (m n : ℕ), ↑(m % n) = ↑m % ↑n
· 使用定理 `Int.emod_eq_emod_iff_emod_sub_eq_zero`：∀ {m n k : ℤ}, m % n = k % n ↔ (m
 - k) % n = 0
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a := by
  rw [ModEq, eq_comm, ← Int.natCast_inj, Int.natCast_mod, Int.natCast_mod,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

/-- A variant of `modEq_iff_dvd` with `Nat` divisibility -/
/-
**Nat.modEq_iff_dvd'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b - a
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `modEq_iff_dvd` with `Nat` divisibility
-/
theorem modEq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a := by
  rw [modEq_iff_dvd, ← Int.natCast_dvd_natCast, Int.ofNat_sub h]

/-- The forward direction of `modEq_iff_dvd'`, which does not require the `a ≤ b` assumption. -/
/-
**Nat.ModEq.dvd'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ}, a ≡ b [MOD n] → n ∣ b - a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.dvd_zero`：∀ (a : ℕ), a ∣ 0

--- 原说明 ---
The forward direction of `modEq_iff_dvd'`, which does not require the `a ≤ b` as
sumption.
-/
theorem ModEq.dvd' (h : a ≡ b [MOD n]) : n ∣ b - a := by
  obtain h0 | h0 : a ≤ b ∨ b ≤ a := le_total a b
  · exact (modEq_iff_dvd' h0).mp h
  · rw [Nat.sub_eq_zero_of_le h0]
    exact Nat.dvd_zero n

alias ⟨_, modEq_of_dvd'⟩ := modEq_iff_dvd'
/-
**Nat.mod_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mod_modEq (a n) : a % n ≡ a [MOD n]
参数：a n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
-/
theorem mod_modEq (a n) : a % n ≡ a [MOD n] :=
  mod_mod _ _

namespace ModEq

/-
**Nat.ModEq.modulus_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：modulus_mul_add : m * a + b ≡ b [MOD m]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_add_mod_self_left`：∀ (a b c : ℕ), (a * b + c) % a = c % a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modulus_mul_add : m * a + b ≡ b [MOD m] := by simp [Nat.ModEq]
/-
**Nat.ModEq.of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]
参数：d : m ∣ n；h : a ≡ b [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.modEq_of_dvd`：∀ {n a b : ℕ}, ↑n ∣ ↑b - ↑a → a ≡ b [MOD n]
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.ModEq.dvd`：∀ {n a b : ℕ}, a ≡ b [MOD n] → ↑n ∣ ↑b - ↑a
-/
lemma of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
  modEq_of_dvd <| Int.ofNat_dvd.mpr d |>.trans h.dvd
/-
**Nat.ModEq.mul_left'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * b [MOD c * n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_mod_mul_left`：∀ (z x y : ℕ), z * x % (z * y) = z * (x % y)
-/
protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD c * n] := by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]
/-
**Nat.ModEq.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * b [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.of_dvd`：of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Nat.ModEq.mul_left'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * 
b [MOD c * n]
-/
protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  (h.mul_left' _).of_dvd (dvd_mul_left _ _)
/-
**Nat.ModEq.mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * c [MOD n * c]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.ModEq.mul_left'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * 
b [MOD c * n]
-/
protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' c
/-
**Nat.ModEq.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * c [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.ModEq.mul_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * b
 [MOD n]
-/
protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] := by
  rw [mul_comm a, mul_comm b]; exact h.mul_left c

@[gcongr]
/-
**Nat.ModEq.mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a * c ≡ b * d [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.mul_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * b
 [MOD n]
· 使用定理 `Nat.ModEq.mul_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * 
c [MOD n]
-/
protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr]
/-
**Nat.ModEq.pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD n] → a ^ m ≡ b ^ m [MOD n]
参数：m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Nat.ModEq.mul`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a * c 
≡ b * d [MOD n]
-/
protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact hd.mul h

@[gcongr]
/-
**Nat.ModEq.add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c ≡ b + d [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `Int.dvd_add`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Nat.ModEq.dvd`：∀ {n a b : ℕ}, a ≡ b [MOD n] → ↑n ∣ ↑b - ↑a
-/
protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  rw [modEq_iff_dvd, Int.natCast_add, Int.natCast_add, add_sub_add_comm]
  exact Int.dvd_add h₁.dvd h₂.dvd
/-
**Nat.ModEq.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
  ModEq.rfl.add h
/-
**Nat.ModEq.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a + c ≡ b + c [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
  h.add ModEq.rfl
/-
**Nat.ModEq.add_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b + d [MOD n] → c ≡ d [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Int.dvd_sub`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b - c
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
-/
protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    c ≡ d [MOD n] := by
  simp only [modEq_iff_dvd, Int.natCast_add] at *
  rw [add_sub_add_comm] at h₂
  convert! Int.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel_left]
/-
**Nat.ModEq.add_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), c + a ≡ c + b [MOD n] → a ≡ b [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_left_cancel`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b 
+ d [MOD n] → c ≡ d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected theorem add_left_cancel' (c : ℕ) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_left_cancel h

@[simp]
/-
**Nat.ModEq.add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → (a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n])
参数：a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_left_cancel`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b 
+ d [MOD n] → c ≡ d [MOD n]
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
-/
protected theorem add_iff_left (h : a ≡ b [MOD n]) : a + c ≡ b + d [MOD n] ↔ c ≡ d [MOD n] :=
  ⟨h.add_left_cancel, h.add⟩
/-
**Nat.ModEq.add_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a + c ≡ b + d [MOD n] → a ≡ b [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_left_cancel`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b 
+ d [MOD n] → c ≡ d [MOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    a ≡ b [MOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂
/-
**Nat.ModEq.add_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n] → a ≡ b [MOD n]
参数：c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_right_cancel`：∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a + c ≡ b
 + d [MOD n] → a ≡ b [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected theorem add_right_cancel' (c : ℕ) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_right_cancel h

@[simp]
/-
**Nat.ModEq.add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, c ≡ d [MOD n] → (a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n])
参数：a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.add_right_cancel`：∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a + c ≡ b
 + d [MOD n] → a ≡ b [MOD n]
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
-/
protected theorem add_iff_right (h : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n] :=
  ⟨h.add_right_cancel, (.add · h)⟩
/-
**Nat.ModEq.sub'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → a ≡ b [MOD n] → c ≡ d [MOD n] → a - c
 ≡ b - d [MOD n]
参数：c ≤ a ↔ d ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Nat.ModEq.refl`：∀ {n : ℕ} (a : ℕ), a ≡ a [MOD n]
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Int.natCast_sub`：∀ {n m : ℕ}, n ≤ m → ↑(m - n) = ↑m - ↑n
· 使用定理 `sub_sub_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b - (c - d) = a - c - (b - d)
· 使用定理 `Int.dvd_sub`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b - c
· 使用定理 `Nat.ModEq.dvd`：∀ {n a b : ℕ}, a ≡ b [MOD n] → ↑n ∣ ↑b - ↑a
-/
protected lemma sub' (h : c ≤ a ↔ d ≤ b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a - c ≡ b - d [MOD n] := by
  obtain hac | hca := lt_or_ge a c
  · rw [Nat.sub_eq_zero_of_le hac.le, Nat.sub_eq_zero_of_le ((lt_iff_lt_of_le_iff_le h).1 hac).le]
  rw [modEq_iff_dvd, Int.natCast_sub hca, Int.natCast_sub <| h.1 hca, sub_sub_sub_comm]
  exact Int.dvd_sub hab.dvd hcd.dvd
/-
**Nat.ModEq.sub_left'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c : ℕ}, (b ≤ a ↔ c ≤ a) → b ≡ c [MOD n] → a - b ≡ a - c [MOD n]
参数：b ≤ a ↔ c ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.sub'`：∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → a ≡ b [MOD n] → c ≡
 d [MOD n] → a - c ≡ b - d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected lemma sub_left' (h : b ≤ a ↔ c ≤ a) (hbc : b ≡ c [MOD n]) : a - b ≡ a - c [MOD n] :=
  .sub' h .rfl hbc
/-
**Nat.ModEq.sub_right'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c : ℕ}, (a ≤ b ↔ a ≤ c) → b ≡ c [MOD n] → b - a ≡ c - a [MOD n]
参数：a ≤ b ↔ a ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.sub'`：∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → a ≡ b [MOD n] → c ≡
 d [MOD n] → a - c ≡ b - d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected lemma sub_right' (h : a ≤ b ↔ a ≤ c) (hbc : b ≡ c [MOD n]) : b - a ≡ c - a [MOD n] :=
  .sub' h hbc .rfl

@[gcongr]
/-
**Nat.ModEq.sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c d : ℕ}, c ≤ a → d ≤ b → a ≡ b [MOD n] → c ≡ d [MOD n] → a - c ≡
 b - d [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.sub'`：∀ {n a b c d : ℕ}, (c ≤ a ↔ d ≤ b) → a ≡ b [MOD n] → c ≡
 d [MOD n] → a - c ≡ b - d [MOD n]
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
-/
protected lemma sub (hca : c ≤ a) (hdb : d ≤ b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a - c ≡ b - d [MOD n] := .sub' (iff_of_true hca hdb) hab hcd

@[gcongr]
/-
**Nat.ModEq.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c : ℕ}, b ≤ a → c ≤ a → b ≡ c [MOD n] → a - b ≡ a - c [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.sub`：∀ {n a b c d : ℕ}, c ≤ a → d ≤ b → a ≡ b [MOD n] → c ≡ d 
[MOD n] → a - c ≡ b - d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected lemma sub_left (hba : b ≤ a) (hca : c ≤ a) (hbc : b ≡ c [MOD n]) :
    a - b ≡ a - c [MOD n] := .sub hba hca .rfl hbc

@[gcongr]
/-
**Nat.ModEq.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {n a b c : ℕ}, a ≤ b → a ≤ c → b ≡ c [MOD n] → b - a ≡ c - a [MOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.sub`：∀ {n a b c d : ℕ}, c ≤ a → d ≤ b → a ≡ b [MOD n] → c ≡ d 
[MOD n] → a - c ≡ b - d [MOD n]
· 使用定理 `Nat.ModEq.rfl`：∀ {n a : ℕ}, a ≡ a [MOD n]
-/
protected lemma sub_right (hab : a ≤ b) (hac : a ≤ c) (hbc : b ≡ c [MOD n]) :
    b - a ≡ c - a [MOD n] := .sub hab hac hbc .rfl

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Nat.ModEq.of_mul_left`. -/
/-
**Nat.ModEq.mul_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {a b c m : ℕ}, c ≠ 0 → c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_of_mul_dvd_mul_left`：∀ {a m n : ℤ}, a ≠ 0 → a * m ∣ a * n → m ∣ 
n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0

--- 原说明 ---
Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Nat.ModEq.of_mul_left`.
-/
protected theorem mul_left_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.mul_sub]
  exact fun h => (Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr hc) h)
/-
**Nat.ModEq.mul_left_cancel_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {a b c m : ℕ}, c ≠ 0 → (c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m])
参数：c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.mul_left_cancel'`：∀ {a b c m : ℕ}, c ≠ 0 → c * a ≡ c * b [MOD 
c * m] → a ≡ b [MOD m]
· 使用定理 `Nat.ModEq.mul_left'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * 
b [MOD c * n]
-/
protected theorem mul_left_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Nat.ModEq.of_mul_right`. -/
/-
**Nat.ModEq.mul_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {a b c m : ℕ}, c ≠ 0 → a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_of_mul_dvd_mul_right`：∀ {a m n : ℤ}, a ≠ 0 → m * a ∣ n * a → m ∣
 n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0

--- 原说明 ---
Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Nat.ModEq.of_mul_right`
.
-/
protected theorem mul_right_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.sub_mul]
  exact fun h => (Int.dvd_of_mul_dvd_mul_right (Int.ofNat_ne_zero.mpr hc) h)
/-
**Nat.ModEq.mul_right_cancel_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：∀ {a b c m : ℕ}, c ≠ 0 → (a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m])
参数：a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.mul_right_cancel'`：∀ {a b c m : ℕ}, c ≠ 0 → a * c ≡ b * c [MOD
 m * c] → a ≡ b [MOD m]
· 使用定理 `Nat.ModEq.mul_right'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b *
 c [MOD n * c]
-/
protected theorem mul_right_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩

/-- Cancel left multiplication in the modulus.

For cancelling left multiplication on both sides of the `≡`, see `nat.modeq.mul_left_cancel'`. -/
/-
**Nat.ModEq.of_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n]
参数：m : Nat；h : a ≡ b [MOD m * n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a

--- 原说明 ---
Cancel left multiplication in the modulus.

For cancelling left multiplication on both sides of the `≡`, see `nat.modeq.mul_
left_cancel'`.
-/
lemma of_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] := by
  rw [modEq_iff_dvd] at *
  exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h

/-- Cancel right multiplication in the modulus.

For cancelling right multiplication on both sides of the `≡`, see `nat.modeq.mul_right_cancel'`. -/
/-
**Nat.ModEq.of_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：of_mul_right (m : Nat) : a ≡ b [MOD n * m] -> a ≡ b [MOD n]
参数：m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.of_mul_left`：of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a
 ≡ b [MOD n]
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Cancel right multiplication in the modulus.

For cancelling right multiplication on both sides of the `≡`, see `nat.modeq.mul
_right_cancel'`.
-/
lemma of_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] := mul_comm m n ▸ of_mul_left _
/-
**Nat.ModEq.of_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣
 m) : a ≡ b [MOD m]
参数：h : a / c ≡ b / c [MOD m / c]；ha : c ∣ a；ha : c ∣ b；ha : c ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.ModEq.mul_left'`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * 
b [MOD c * n]
-/
theorem of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [MOD m] := by convert! h.mul_left' c <;> rwa [Nat.mul_div_cancel']

end ModEq

@[simp]
/-
**Nat.modulus_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modulus_modEq_zero : n ≡ 0 [MOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modulus_modEq_zero : n ≡ 0 [MOD n] := by simp [ModEq]

@[simp]
/-
**Nat.add_modEq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_modEq_left_iff : a + b ≡ a [MOD n] ↔ n ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modEq_left_iff : a + b ≡ a [MOD n] ↔ n ∣ b := by
  simp [modEq_iff_dvd, Int.natCast_dvd_natCast]

@[simp]
/-
**Nat.add_modEq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_modEq_right_iff : a + b ≡ b [MOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_modEq_left_iff`：add_modEq_left_iff : a + b ≡ a [MOD n] ↔ n ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_modEq_right_iff : a + b ≡ b [MOD n] ↔ n ∣ a := by
  rw [add_comm, add_modEq_left_iff]

@[simp]
/-
**Nat.left_modEq_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：left_modEq_add_iff : a ≡ a + b [MOD n] ↔ n ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `Nat.add_modEq_left_iff`：add_modEq_left_iff : a + b ≡ a [MOD n] ↔ n ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem left_modEq_add_iff : a ≡ a + b [MOD n] ↔ n ∣ b := by
  rw [ModEq.comm, add_modEq_left_iff]

@[simp]
/-
**Nat.right_modEq_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：right_modEq_add_iff : b ≡ a + b [MOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `Nat.add_modEq_right_iff`：add_modEq_right_iff : a + b ≡ b [MOD n] ↔ n ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem right_modEq_add_iff : b ≡ a + b [MOD n] ↔ n ∣ a := by
  rw [ModEq.comm, add_modEq_right_iff]

@[simp]
/-
**Nat.add_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_modulus_modEq_iff : a + n ≡ b [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modulus_modEq_iff : a + n ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.modulus_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modulus_add_modEq_iff : n + a ≡ b [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_modulus_modEq_iff`：add_modulus_modEq_iff : a + n ≡ b [MOD n] ↔ a
 ≡ b [MOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modulus_add_modEq_iff : n + a ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  rw [add_comm, add_modulus_modEq_iff]

@[simp]
/-
**Nat.modEq_add_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_add_modulus_iff : a ≡ b + n [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_modulus_iff : a ≡ b + n [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.modEq_modulus_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_modulus_add_iff : a ≡ n + b [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mod_left`：∀ (x z : ℕ), (x + z) % x = z % x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_modulus_add_iff : a ≡ n + b [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.add_mul_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_mul_modulus_modEq_iff : a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mul_mod_self_right`：∀ (x y z : ℕ), (x + y * z) % z = x % z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_mul_modulus_modEq_iff : a + b * n ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.mul_modulus_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mul_modulus_add_modEq_iff : b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_mul_modulus_modEq_iff`：add_mul_modulus_modEq_iff : a + b * n ≡ c
 [MOD n] ↔ a ≡ c [MOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_modulus_add_modEq_iff : b * n + a ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm, add_mul_modulus_modEq_iff]

@[simp]
/-
**Nat.modEq_add_mul_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_add_mul_modulus_iff : a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mul_mod_self_right`：∀ (x y z : ℕ), (x + y * z) % z = x % z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_mul_modulus_iff : a ≡ b + c * n [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.modEq_mul_modulus_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_mul_modulus_add_iff : a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.modEq_add_mul_modulus_iff`：modEq_add_mul_modulus_iff : a ≡ b + c * n
 [MOD n] ↔ a ≡ b [MOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_mul_modulus_add_iff : a ≡ b * n + c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm, modEq_add_mul_modulus_iff]

@[simp]
/-
**Nat.add_modulus_mul_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_modulus_mul_modEq_iff : a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modulus_mul_modEq_iff : a + n * b ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.modulus_mul_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modulus_mul_add_modEq_iff : n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_modulus_mul_modEq_iff`：add_modulus_mul_modEq_iff : a + n * b ≡ c
 [MOD n] ↔ a ≡ c [MOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modulus_mul_add_modEq_iff : n * b + a ≡ c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm, add_modulus_mul_modEq_iff]

@[simp]
/-
**Nat.modEq_add_modulus_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_add_modulus_mul_iff : a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_modulus_mul_iff : a ≡ b + n * c [MOD n] ↔ a ≡ b [MOD n] := by
  simp [ModEq]

@[simp]
/-
**Nat.modEq_modulus_mul_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_modulus_mul_add_iff : a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.modEq_add_modulus_mul_iff`：modEq_add_modulus_mul_iff : a ≡ b + n * c
 [MOD n] ↔ a ≡ b [MOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_modulus_mul_add_iff : a ≡ n * b + c [MOD n] ↔ a ≡ c [MOD n] := by
  rw [add_comm, modEq_add_modulus_mul_iff]

@[simp]
/-
**Nat.sub_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sub_modulus_modEq_iff (h : n <= a) : a - n ≡ b [MOD n] ↔ a ≡ b [MOD n]
参数：h : n <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_modulus_modEq_iff`：add_modulus_modEq_iff : a + n ≡ b [MOD n] ↔ a
 ≡ b [MOD n]
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_modulus_modEq_iff (h : n ≤ a) : a - n ≡ b [MOD n] ↔ a ≡ b [MOD n] := by
  rw [← add_modulus_modEq_iff, Nat.sub_add_cancel h]

@[simp]
/-
**Nat.modEq_sub_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_sub_modulus_iff (h : n <= b) : a ≡ b - n [MOD n] ↔ a ≡ b [MOD n]
参数：h : n <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.modEq_add_modulus_iff`：modEq_add_modulus_iff : a ≡ b + n [MOD n] ↔ a
 ≡ b [MOD n]
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_sub_modulus_iff (h : n ≤ b) : a ≡ b - n [MOD n] ↔ a ≡ b [MOD n] := by
  rw [← modEq_add_modulus_iff, Nat.sub_add_cancel h]
/-
**Nat.modEq_sub** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：modEq_sub (h : b <= a) : a ≡ b [MOD a - b]
参数：h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.modEq_of_dvd`：∀ {n a b : ℕ}, ↑n ∣ ↑b - ↑a → a ≡ b [MOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
lemma modEq_sub (h : b ≤ a) : a ≡ b [MOD a - b] := (modEq_of_dvd <| by rw [Int.ofNat_sub h]).symm
/-
**Nat.modEq_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：modEq_one : a ≡ b [MOD 1]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.modEq_of_dvd`：∀ {n a b : ℕ}, ↑n ∣ ↑b - ↑a → a ≡ b [MOD n]
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
lemma modEq_one : a ≡ b [MOD 1] := modEq_of_dvd <| one_dvd _
/-
**Nat.modEq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a b : ℕ}, a ≡ b [MOD 0] ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ModEq.eq_1`：∀ (n a b : ℕ), (a ≡ b [MOD n]) = (a % n = b % n)
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma modEq_zero_iff : a ≡ b [MOD 0] ↔ a = b := by rw [ModEq, mod_zero, mod_zero]
/-
**Nat.add_modEq_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：add_modEq_left : n + a ≡ a [MOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma add_modEq_left : n + a ≡ a [MOD n] := by simp
/-
**Nat.add_modEq_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：add_modEq_right : a + n ≡ a [MOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma add_modEq_right : a + n ≡ a [MOD n] := by simp
/-
**Nat.modEq_iff_exists_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_iff_exists_eq_add (h : a <= b) : a ≡ b [MOD n] ↔ exists (t : Nat), b
 = a + n * t
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `dvd_def`：dvd_def : a ∣ b ↔ exists c, b = a * c
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Nat.sub_eq_iff_eq_add'`：∀ {b a c : ℕ}, b ≤ a → (a - b = c ↔ a = b + c)
-/
theorem modEq_iff_exists_eq_add (h : a ≤ b) : a ≡ b [MOD n] ↔ ∃ (t : ℕ), b = a + n * t := by
  rw [modEq_iff_dvd' h, dvd_def]
  exact exists_congr (fun _ => Nat.sub_eq_iff_eq_add' h)

namespace ModEq

/-
**Nat.ModEq.le_of_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a <= b
参数：h1 : a ≡ b [MOD m]；h2 : a < b + m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Nat.le_of_sub_eq_zero`：∀ {n m : ℕ}, n - m = 0 → n ≤ m
· 使用定理 `Nat.eq_zero_of_dvd_of_lt`：∀ {a b : ℕ}, a ∣ b → b < a → b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
theorem le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a ≤ b :=
  (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) (by lia))
/-
**Nat.ModEq.add_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m <= b
参数：h1 : a ≡ b [MOD m]；h2 : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.le_of_lt_add`：le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + 
m) : a <= b
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用引理 `Nat.add_modEq_right`：add_modEq_right : a + n ≡ a [MOD n]
-/
theorem add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m ≤ b :=
  le_of_lt_add (add_modEq_right.trans h1) (by lia)
/-
**Nat.ModEq.dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b
参数：h : a ≡ b [MOD m]；hdm : d ∣ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.ModEq.of_dvd`：of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
theorem dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩
/-
**Nat.ModEq.gcd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.ModEq`。
形式化陈述：gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m
参数：h : a ≡ b [MOD m]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ModEq.dvd_iff`：dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d
 ∣ b
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m := by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)
/-
**Nat.ModEq.eq_of_abs_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : Int) - a| < m) : a = b
参数：h : a ≡ b [MOD m]；h2 : |(b : Int) - a| < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ofNat.inj`：∀ {a a_1 : ℕ}, Int.ofNat a = Int.ofNat a_1 → a = a_1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `Int.eq_zero_of_abs_lt_dvd`：eq_zero_of_abs_lt_dvd {m x : Int} (h1 : m ∣ x
) (h2 : |x| < m) : x = 0
· 使用定理 `Nat.ModEq.dvd`：∀ {n a b : ℕ}, a ≡ b [MOD n] → ↑n ∣ ↑b - ↑a
-/
lemma eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : ℤ) - a| < m) : a = b := by
  apply Int.ofNat.inj
  rw [eq_comm, ← sub_eq_zero]
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2
/-
**Nat.ModEq.eq_of_lt_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b
参数：h : a ≡ b [MOD m]；ha : a < m；hb : b < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.eq_of_abs_lt`：eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : Int
) - a| < m) : a = b
· 使用引理 `Int.abs_sub_lt_of_lt_lt`：abs_sub_lt_of_lt_lt {m a b : Nat} (ha : a < m) 
(hb : b < m) : |(b : Int) - a| < m
-/
lemma eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
  h.eq_of_abs_lt <| Int.abs_sub_lt_of_lt_lt ha hb

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
/-
**Nat.ModEq.cancel_left_div_gcd** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD 
m / gcd m c]
参数：hm : 0 < m；h : c * a ≡ c * b [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Int.dvd_of_dvd_mul_right_of_gcd_one`：dvd_of_dvd_mul_right_of_gcd_one {a 
b c : Int} (habc : a ∣ b * c) (hab : gcd a b = 1) : a ∣ c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.mul_ediv_assoc`：∀ (a : ℤ) {b c : ℤ}, c ∣ b → a * b / c = a * (b / c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.ediv_dvd_ediv`：∀ {a b c : ℤ}, a ∣ b → b ∣ c → b / a ∣ c / a
· 使用定理 `Int.mul_sub`：∀ (a b c : ℤ), a * (b - c) = a * b - a * c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Nat.gcd_div`：∀ {m n k : ℕ}, k ∣ m → k ∣ n → (m / k).gcd (n / k) = m.gcd 
n / k
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `
gcd m c`
-/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  let d := gcd m c
  have hmd := gcd_dvd_left m c
  have hcd := gcd_dvd_right m c
  rw [modEq_iff_dvd]
  refine @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) ?_ ?_
  · show (m / d : ℤ) ∣ c / d * (b - a)
    rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (Int.natCast_dvd_natCast.mpr hcd), mul_comm]
    apply Int.ediv_dvd_ediv (Int.natCast_dvd_natCast.mpr hmd)
    rw [Int.mul_sub]
    exact modEq_iff_dvd.mp h
  · show Int.gcd (m / d) (c / d) = 1
    simp only [d, ← Int.natCast_div, Int.gcd_natCast_natCast (m / d) (c / d),
      gcd_div hmd hcd, Nat.div_self (gcd_pos_of_pos_left c hm)]

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
/-
**Nat.ModEq.cancel_right_div_gcd** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD
 m / gcd m c]
参数：hm : 0 < m；h : a * c ≡ b * c [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.cancel_left_div_gcd`：cancel_left_div_gcd (hm : 0 < m) (h : c *
 a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `
gcd m c`
-/
lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  apply cancel_left_div_gcd hm
  simpa [mul_comm] using h
/-
**Nat.ModEq.cancel_left_div_gcd'** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b
 [MOD m]) : a ≡ b [MOD m / gcd m c]
参数：hm : 0 < m；hcd : c ≡ d [MOD m]；h : c * a ≡ d * b [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.cancel_left_div_gcd`：cancel_left_div_gcd (hm : 0 < m) (h : c *
 a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.mul_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * 
c [MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
lemma cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_right b).cancel_left_div_gcd hm
/-
**Nat.ModEq.cancel_right_div_gcd'** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * 
d [MOD m]) : a ≡ b [MOD m / gcd m c]
参数：hm : 0 < m；hcd : c ≡ d [MOD m]；h : a * c ≡ b * d [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.cancel_right_div_gcd`：cancel_right_div_gcd (hm : 0 < m) (h : a
 * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.mul_left`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c * a ≡ c * b
 [MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
-/
lemma cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_left b).cancel_right_div_gcd hm

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
/-
**Nat.ModEq.cancel_left_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a
 ≡ b [MOD m]
参数：hmc : gcd m c = 1；h : c * a ≡ c * b [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用引理 `Nat.ModEq.cancel_left_div_gcd`：cancel_left_div_gcd (hm : 0 < m) (h : c *
 a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c]

--- 原说明 ---
A common factor that's coprime with the modulus can be cancelled from a `ModEq`
-/
lemma cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [gcd_zero_left] at hmc
    simp only [hmc, one_mul, modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
/-
**Nat.ModEq.cancel_right_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 `Nat.ModEq`。
形式化陈述：cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : 
a ≡ b [MOD m]
参数：hmc : gcd m c = 1；h : a * c ≡ b * c [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.cancel_left_of_coprime`：cancel_left_of_coprime (hmc : gcd m c 
= 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
A common factor that's coprime with the modulus can be cancelled from a `ModEq`
-/
lemma cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
  cancel_left_of_coprime hmc <| by simpa [mul_comm] using h

end ModEq

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
/-
**Nat.chineseRemainder'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：chineseRemainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b
 [MOD m] }
参数：h : a ≡ b [MOD gcd n m]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m`
-/
def chineseRemainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  if hn : n = 0 then ⟨a, by
    rw [hn, gcd_zero_left] at h; constructor
    · rfl
    · exact h⟩
  else
    if hm : m = 0 then ⟨b, by
      rw [hm, gcd_zero_right] at h; constructor
      · exact h.symm
      · rfl⟩
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) / gcd n m % lcm n m), by
        rw [xgcd_val]
        dsimp
        rw [modEq_iff_dvd, modEq_iff_dvd,
          Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.2 (lcm_ne_zero hn hm)))]
        have hnonzero : (gcd n m : ℤ) ≠ 0 := by
          norm_cast
          rw [Nat.gcd_eq_zero_iff, not_and]
          exact fun _ => hm
        have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t * (b - a) := fun t => h.dvd.mul_left _
        have := gcd_eq_gcd_ab n m
        constructor <;> rw [Int.emod_def, ← sub_add] <;>
            refine Int.dvd_add ?_ (dvd_mul_of_dvd_left ?_ _) <;>
          try norm_cast
        · rw [← sub_eq_iff_eq_add'] at this
          rw [← this, Int.sub_mul, ← add_sub_assoc, add_comm, add_sub_assoc, ← Int.mul_sub,
            Int.add_ediv_of_dvd_left, Int.mul_ediv_cancel_left _ hnonzero,
            Int.mul_ediv_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, Int.dvd_neg, mul_assoc]
          · exact dvd_mul_right _ _
          norm_cast
          exact dvd_mul_right _ _
        · exact dvd_lcm_left n m
        · rw [← sub_eq_iff_eq_add] at this
          rw [← this, Int.sub_mul, sub_add, ← Int.mul_sub, Int.sub_ediv_of_dvd,
            Int.mul_ediv_cancel_left _ hnonzero, Int.mul_ediv_assoc _ h.dvd, ← sub_add, sub_self,
            zero_add, mul_assoc]
          · exact dvd_mul_right _ _
          · exact hcoedvd _
        · exact dvd_lcm_right n m⟩

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
/-
**Nat.chineseRemainder** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：chineseRemainder (co : n.Coprime m) (a b : Nat) : { k // k ≡ a [MOD n] ∧ k
 ≡ b [MOD m] }
参数：co : n.Coprime m；a b : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m`
-/
def chineseRemainder (co : n.Coprime m) (a b : ℕ) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  chineseRemainder' (by convert! @modEq_one a b)
/-
**Nat.chineseRemainder'_lt_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]), n ≠ 0 → m ≠ 0 → ↑(Nat.chineseRe
mainder' h) < n.lcm m
参数：h : a ≡ b [MOD n.gcd m]；Nat.chineseRemainder' h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Nat.xgcd_val`：xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `Int.toNat_lt_toNat`：∀ {n m : ℤ}, 0 < m → (n.toNat < m.toNat ↔ n < m)
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
-/
theorem chineseRemainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder' h) < lcm n m := by
  dsimp only [chineseRemainder']
  rw [dif_neg hn, dif_neg hm, Subtype.coe_mk, xgcd_val, ← Int.toNat_natCast (lcm n m)]
  have lcm_pos := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)
/-
**Nat.chineseRemainder_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainder_lt_mul (co : n.Coprime m) (a b : Nat) (hn : n != 0) (hm :
 m != 0) : ↑(chineseRemainder co a b) < n * m
参数：co : n.Coprime m；a b : Nat；hn : n != 0；hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.chineseRemainder'_lt_lcm`：∀ {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]),
 n ≠ 0 → m ≠ 0 → ↑(Nat.chineseRemainder' h) < n.lcm m
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Nat.Coprime.lcm_eq_mul`：∀ {m n : ℕ}, m.Coprime n → m.lcm n = m * n
-/
theorem chineseRemainder_lt_mul (co : n.Coprime m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder co a b) < n * m :=
  lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)
/-
**Nat.mod_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mod_lcm (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m]) : a ≡ b [MOD lcm n m]
参数：hn : a ≡ b [MOD n]；hm : a ≡ b [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Int.coe_lcm_dvd`：∀ {a b c : ℤ}, a ∣ c → b ∣ c → ↑(a.lcm b) ∣ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mod_lcm (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m]) : a ≡ b [MOD lcm n m] :=
  Nat.modEq_iff_dvd.mpr <| Int.coe_lcm_dvd (Nat.modEq_iff_dvd.mp hn) (Nat.modEq_iff_dvd.mp hm)
/-
**Nat.chineseRemainder_modEq_unique** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：chineseRemainder_modEq_unique (co : n.Coprime m) {a b z} (hzan : z ≡ a [MO
D n]) (hzbm : z ≡ b [MOD m]) : z ≡ chineseRemainder co a b [MOD n * m]
参数：co : n.Coprime m；hzan : z ≡ a [MOD n]；hzbm : z ≡ b [MOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.lcm_eq_mul`：∀ {m n : ℕ}, m.Coprime n → m.lcm n = m * n
· 使用定理 `Nat.mod_lcm`：mod_lcm (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m]) : a ≡ b [
MOD lcm n m]
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem chineseRemainder_modEq_unique (co : n.Coprime m) {a b z}
    (hzan : z ≡ a [MOD n]) (hzbm : z ≡ b [MOD m]) : z ≡ chineseRemainder co a b [MOD n * m] := by
  simpa [Nat.Coprime.lcm_eq_mul co] using
    mod_lcm (hzan.trans ((chineseRemainder co a b).prop.1).symm)
      (hzbm.trans ((chineseRemainder co a b).prop.2).symm)
/-
**Nat.modEq_and_modEq_iff_modEq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_and_modEq_iff_modEq_mul {a b m n : Nat} (hmn : m.Coprime n) : a ≡ b 
[MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n]
参数：hmn : m.Coprime n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Nat.ModEq.of_mul_right`：of_mul_right (m : Nat) : a ≡ b [MOD n * m] -> a 
≡ b [MOD n]
· 使用引理 `Nat.ModEq.of_mul_left`：of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a
 ≡ b [MOD n]
-/
theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℕ} (hmn : m.Coprime n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] :=
  ⟨fun h => by
    rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast,
      ← Int.dvd_natAbs, Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,
   fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩
/-
**Nat.coprime_of_mul_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_of_mul_modEq_one (b : Nat) {a n : Nat} (h : a * b ≡ 1 [MOD n]) : a
.Coprime n
参数：b : Nat；h : a * b ≡ 1 [MOD n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用引理 `Nat.ModEq.of_mul_right`：of_mul_right (m : Nat) : a ≡ b [MOD n * m] -> a 
≡ b [MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.ModEq.mul_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * 
c [MOD n]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem coprime_of_mul_modEq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : a.Coprime n := by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.dvd_one, ← Nat.modEq_zero_iff_dvd]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 0 := by rw [zero_mul]
/-
**Nat.add_mod_add_ite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_mod_add_ite (a b c : Nat) : ((a + b) % c + if c <= a % c + b % c then 
c else 0) = a % c + b % c
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.ModEq.add`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a + c 
≡ b + d [MOD n]
· 使用定理 `Nat.mod_modEq`：mod_modEq (a n) : a % n ≡ a [MOD n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.div_lt_of_lt_mul`：∀ {m n k : ℕ}, m < n * k → m / n < k
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Nat.add_lt_add`：∀ {a b c d : ℕ}, a < b → c < d → a + c < b + d
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 33 条，此处仅展示前 30 条）
-/
theorem add_mod_add_ite (a b c : ℕ) :
    ((a + b) % c + if c ≤ a % c + b % c then c else 0) = a % c + b % c :=
  have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
  else by
    rw [this]
    split_ifs with h
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
            exact
              add_lt_add (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0))
                (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0)))
      have h0 : 0 < (a % c + b % c) / c := Nat.div_pos h (Nat.pos_of_ne_zero hc0)
      rw [← @add_right_cancel_iff _ _ _ (c * ((a % c + b % c) / c)), add_comm _ c, add_assoc,
        mod_add_div, le_antisymm (le_of_lt_succ h2) h0, mul_one, add_comm]
    · rw [Nat.mod_eq_of_lt (lt_of_not_ge h), add_zero]
/-
**Nat.add_mod_of_add_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_mod_of_add_mod_lt {a b c : Nat} (hc : a % c + b % c < c) : (a + b) % c
 = a % c + b % c
参数：hc : a % c + b % c < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_mod_add_ite`：add_mod_add_ite (a b c : Nat) : ((a + b) % c + if c
 <= a % c + b % c then c else 0) = a % c + b % c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem add_mod_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
    (a + b) % c = a % c + b % c := by rw [← add_mod_add_ite, if_neg (not_le_of_gt hc), add_zero]
/-
**Nat.add_mod_add_of_le_add_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_mod_add_of_le_add_mod {a b c : Nat} (hc : c <= a % c + b % c) : (a + b
) % c + c = a % c + b % c
参数：hc : c <= a % c + b % c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_mod_add_ite`：add_mod_add_ite (a b c : Nat) : ((a + b) % c + if c
 <= a % c + b % c then c else 0) = a % c + b % c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) :
    (a + b) % c + c = a % c + b % c := by rw [← add_mod_add_ite, if_pos hc]
/-
**Nat.add_div_eq_of_add_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_div_eq_of_add_mod_lt {a b c : Nat} (hc : a % c + b % c < c) : (a + b) 
/ c = a / c + b / c
参数：hc : a % c + b % c < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_div`：∀ {a b c : ℕ}, 0 < c → (a + b) / c = a / c + b / c + if c ≤
 a % c + b % c then 1 else 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
    (a + b) / c = a / c + b / c :=
  if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_gt hc), add_zero]
/-
**Nat.add_div_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a b c : ℕ}, c ∣ a → (a + b) / c = a / c + b / c
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_div_eq_of_add_mod_lt`：add_div_eq_of_add_mod_lt {a b c : Nat} (hc
 : a % c + b % c < c) : (a + b) / c = a / c + b / c
· 使用定理 `Nat.mod_eq_zero_of_dvd`：∀ {m n : ℕ}, m ∣ n → n % m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
-/
protected theorem add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca, zero_add]
        exact Nat.mod_lt _ (zero_lt_of_ne_zero h))
/-
**Nat.add_div_of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a b c : ℕ}, c ∣ b → (a + b) / c = a / c + b / c
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_div_of_dvd_right`：∀ {a b c : ℕ}, c ∣ a → (a + b) / c = a / c + b
 / c
-/
protected theorem add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) : (a + b) / c = a / c + b / c := by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]
/-
**Nat.add_div_eq_of_le_mod_add_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_div_eq_of_le_mod_add_mod {a b c : Nat} (hc : c <= a % c + b % c) (hc0 
: 0 < c) : (a + b) / c = a / c + b / c + 1
参数：hc : c <= a % c + b % c；hc0 : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_div`：∀ {a b c : ℕ}, 0 < c → (a + b) / c = a / c + b / c + if c ≤
 a % c + b % c then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) :
    (a + b) / c = a / c + b / c + 1 := by rw [Nat.add_div hc0, if_pos hc]

@[deprecated Nat.div_add_div_le_add_div (since := "2026-08-05")]
/-
**Nat.add_div_le_add_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_div_le_add_div (a b c : Nat) : a / c + b / c <= (a + b) / c
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_add_div_le_add_div`：∀ {x y z : ℕ}, x / z + y / z ≤ (x + y) / z
-/
theorem add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
  Nat.div_add_div_le_add_div
/-
**Nat.add_div_le_div_add_div_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_div_le_div_add_div_add_one (a b c : Nat) : (a + b) / c <= a / c + b / 
c + 1
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.add_div`：∀ {a b c : ℕ}, 0 < c → (a + b) / c = a / c + b / c + if c ≤
 a % c + b % c then 1 else 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem add_div_le_div_add_div_add_one (a b c : ℕ) : (a + b) / c ≤ a / c + b / c + 1 := by
  by_cases h : c = 0
  · simp [h]
  · rw [Nat.add_div (Nat.pos_of_ne_zero h), Nat.add_le_add_iff_left]
    split <;> decide
/-
**Nat.le_mod_add_mod_of_dvd_add_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : Nat} (h : c ∣ a + b) (ha : ¬
c ∣ a) : c <= a % c + b % c
参数：h : c ∣ a + b；ha : ¬c ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Nat.add_mod_of_add_mod_lt`：add_mod_of_add_mod_lt {a b c : Nat} (hc : a %
 c + b % c < c) : (a + b) % c = a % c + b % c
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c ≤ a % c + b % c :=
  by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    simp_all [dvd_iff_mod_eq_zero]
/-
**Nat.mod_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mod_sub_of_le {a b n : Nat} (h : b <= a % n) : a % n - b = (a - b) % n
参数：h : b <= a % n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.mul_add_mod`：∀ (m x y : ℕ), (m * x + y) % m = y % m
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
-/
lemma mod_sub_of_le {a b n : ℕ} (h : b ≤ a % n) : a % n - b = (a - b) % n := by
  rcases n.eq_zero_or_pos with rfl | hn; · simp only [mod_zero]
  nth_rw 2 [← div_add_mod a n]; rw [Nat.add_sub_assoc h, mul_add_mod]
  exact (mod_eq_of_lt <| (sub_le ..).trans_lt (mod_lt a hn)).symm
/-
**Nat.odd_mul_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_mul_odd {n m : Nat} : n % 2 = 1 -> m % 2 = 1 -> n * m % 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.ModEq.mul`：∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] → a * c 
≡ b * d [MOD n]
-/
theorem odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → n * m % 2 = 1 := by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1
/-
**Nat.odd_mul_odd_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_mul_odd_div_two {m n : Nat} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) : m * 
n / 2 = m * (n / 2) + m / 2
参数：hm1 : m % 2 = 1；hn1 : n % 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `Nat.two_mul_odd_div_two`：two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n /
 2) = n - 1
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.odd_mul_odd`：odd_mul_odd {n m : Nat} : n % 2 = 1 -> m % 2 = 1 -> n *
 m % 2 = 1
· 使用定理 `Nat.mul_sub`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
-/
theorem odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
    m * n / 2 = m * (n / 2) + m / 2 :=
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
  mul_right_injective₀ two_ne_zero <| by
    dsimp
    rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
      two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1), Nat.mul_sub, mul_one, ←
      Nat.add_sub_assoc (by lia), Nat.sub_add_cancel (Nat.le_mul_of_pos_right m hn0)]
/-
**Nat.odd_of_mod_four_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_of_mod_four_eq_one {n : Nat} : n % 4 = 1 -> n % 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用引理 `Nat.ModEq.of_mul_left`：of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a
 ≡ b [MOD n]
-/
theorem odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 1 2
/-
**Nat.odd_of_mod_four_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_of_mod_four_eq_three {n : Nat} : n % 4 = 3 -> n % 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用引理 `Nat.ModEq.of_mul_left`：of_mul_left (m : Nat) (h : a ≡ b [MOD m * n]) : a
 ≡ b [MOD n]
-/
theorem odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 3 2

/-- A natural number is odd iff it has residue `1` or `3` mod `4`. -/
/-
**Nat.odd_mod_four_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_mod_four_iff {n : Nat} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.odd_of_mod_four_eq_one`：odd_of_mod_four_eq_one {n : Nat} : n % 4 = 1
 -> n % 2 = 1
· 使用定理 `Nat.odd_of_mod_four_eq_three`：odd_of_mod_four_eq_three {n : Nat} : n % 4
 = 3 -> n % 2 = 1

--- 原说明 ---
A natural number is odd iff it has residue `1` or `3` mod `4`.
-/
theorem odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := by decide
  ⟨fun hn =>
    help (n % 4) (mod_lt n (by lia)) <| (mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn,
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩
/-
**Nat.mod_eq_of_modEq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b
参数：h : a ≡ b [MOD n]；hb : b < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
-/
lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b :=
  Eq.trans h (mod_eq_of_lt hb)
/-
**Nat.ext_div_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ext_div_modEq {n a b : Nat} (h0 : a / n = b / n) (h1 : a ≡ b [MOD n]) : a 
= b
参数：h0 : a / n = b / n；h1 : a ≡ b [MOD n]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ext_div_mod`：∀ {n a b : ℕ}, a / n = b / n → a % n = b % n → a = b
-/
theorem ext_div_modEq {n a b : ℕ} (h0 : a / n = b / n) (h1 : a ≡ b [MOD n]) : a = b :=
  ext_div_mod h0 h1
/-
**Nat.ext_div_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ext_div_modEq_iff (n a b : Nat) : a = b ↔ a / n = b / n ∧ a ≡ b [MOD n]
参数：n a b : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ext_div_mod_iff`：∀ (n a b : ℕ), a = b ↔ a / n = b / n ∧ a % n = b % 
n
-/
theorem ext_div_modEq_iff (n a b : ℕ) : a = b ↔ a / n = b / n ∧ a ≡ b [MOD n] :=
  ext_div_mod_iff _ _ _
/-
**Nat.modEq_iff_eq_of_div_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_iff_eq_of_div_eq {n a b : Nat} (h : a / n = b / n) : a ≡ b [MOD n] ↔
 a = b
参数：h : a / n = b / n。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modEq_iff_eq_of_div_eq {n a b : ℕ} (h : a / n = b / n) :
    a ≡ b [MOD n] ↔ a = b := by grind [ext_div_modEq_iff]

end Nat

