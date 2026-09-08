/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Logic.Basic

/-!

# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`CharZero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## TODO

* Unify with `CharP` (possibly using an out-parameter)
-/

public section

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.)

*Warning*: for a semiring `R`, `CharZero R` and `CharP R 0` need not coincide.
* `CharZero R` requires an injection `ℕ ↪ R`;
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.
  For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
  `CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
  This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
/-
**CharZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [AddMonoidWithOne R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid w
ith 1.)

*Warning*: for a semiring `R`, `CharZero R` and `CharP R 0` need not coincide.
* `CharZero R` requires an injection `ℕ ↪ R`;
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.
  For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is abso
rbing), shows that
  `CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
  This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : ℕ → R)

variable {R : Type*}
/-
**charZero_of_inj_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charZero_of_inj_zero [AddGroupWithOne R] (H : forall n : Nat, (n : R) = 0 
-> n = 0) : CharZero R
参数：H : forall n : Nat, (n : R) = 0 -> n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem charZero_of_inj_zero [AddGroupWithOne R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) :
    CharZero R :=
  ⟨@fun m n h => by
    induction m generalizing n with
    | zero => rw [H n]; rw [← h, Nat.cast_zero]
    | succ m ih =>
      cases n
      · apply H; rw [h, Nat.cast_zero]
      · simp only [Nat.cast_succ, add_right_cancel_iff] at h; rwa [ih]⟩

namespace Nat

variable [AddMonoidWithOne R] [CharZero R]

/-
**Nat.cast_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_injective : Function.Injective (Nat.cast : Nat -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
-/
theorem cast_injective : Function.Injective (Nat.cast : ℕ → R) :=
  CharZero.cast_injective

@[simp, norm_cast]
/-
**Nat.cast_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff

@[simp, norm_cast]
/-
**Nat.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]

@[norm_cast]
/-
**Nat.cast_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
-/
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
/-
**Nat.cast_add_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 :=
  mod_cast n.succ_ne_zero

@[simp, norm_cast]
/-
**Nat.cast_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]

@[norm_cast]
/-
**Nat.cast_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_ne_one {n : Nat} : (n : R) != 1 ↔ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
-/
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.not

end Nat

namespace OfNat

variable [AddMonoidWithOne R] [CharZero R]

/-
**OfNat.ofNat_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `OfNat`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ) [inst_2 
: n.AtLeastTwo], OfNat.ofNat n ≠ 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
@[simp] lemma ofNat_ne_zero (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne n)
/-
**OfNat.zero_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `OfNat`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ) [inst_2 
: n.AtLeastTwo], 0 ≠ OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
-/
@[simp] lemma zero_ne_ofNat (n : ℕ) [n.AtLeastTwo] : 0 ≠ (ofNat(n) : R) :=
  (ofNat_ne_zero n).symm
/-
**OfNat.ofNat_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `OfNat`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ) [inst_2 
: n.AtLeastTwo], OfNat.ofNat n ≠ 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_one`：cast_ne_one {n : Nat} : (n : R) != 1 ↔ n != 1
· 使用引理 `Nat.AtLeastTwo.ne_one`：ne_one : n != 1
-/
@[simp] lemma ofNat_ne_one (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) ≠ 1 :=
  Nat.cast_ne_one.2 (Nat.AtLeastTwo.ne_one)
/-
**OfNat.one_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `OfNat`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ) [inst_2 
: n.AtLeastTwo], 1 ≠ OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `OfNat.ofNat_ne_one`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZe
ro R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 1
-/
@[simp] lemma one_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (1 : R) ≠ ofNat(n) :=
  (ofNat_ne_one n).symm
/-
**OfNat.ofNat_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `OfNat`。
形式化陈述：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] {m n : ℕ} [inst_
2 : m.AtLeastTwo] [inst_3 : n.AtLeastTwo],   OfNat.ofNat m = OfNat.ofNat n ↔ OfN
at.ofNat m = OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
-/
@[simp] lemma ofNat_eq_ofNat {m n : ℕ} [m.AtLeastTwo] [n.AtLeastTwo] :
    (ofNat(m) : R) = ofNat(n) ↔ (ofNat m : ℕ) = ofNat n :=
  Nat.cast_inj

end OfNat

namespace NeZero

/-
**NeZero.charZero** 是 Mathlib 中的一个实例，位于命名空间 `NeZero`。
形式化陈述：charZero {M} {n : Nat} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZe
ro (n : M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
instance charZero {M} {n : ℕ} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩
/-
**NeZero.charZero_one** 是 Mathlib 中的一个实例，位于命名空间 `NeZero`。
形式化陈述：charZero_one {M} [AddMonoidWithOne M] [CharZero M] : NeZero (1 : M) where 
out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance charZero_one {M} [AddMonoidWithOne M] [CharZero M] : NeZero (1 : M) where
  out := by
    rw [← Nat.cast_one, Nat.cast_ne_zero]
    trivial
/-
**NeZero.charZero_ofNat** 是 Mathlib 中的一个实例，位于命名空间 `NeZero`。
形式化陈述：charZero_ofNat {M} {n : Nat} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero
 M] : NeZero (OfNat.ofNat n : M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0
-/
instance charZero_ofNat {M} {n : ℕ} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M] :
    NeZero (OfNat.ofNat n : M) :=
  ⟨OfNat.ofNat_ne_zero n⟩

end NeZero

