/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.SplitIfs

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`AddMonoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as the coercion `Nat.cast`.

## Main declarations

* `NatCast`: Type class for `Nat.cast`.
* `AddMonoidWithOne`: Type class for which `Nat.cast` is a canonical monoid homomorphism from `ℕ`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/

@[expose] public section

variable {R : Type*}

/-- The numeral `((0+1)+⋯)+1`. -/
/-
**Nat.unaryCast** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{R : Type u_1} → [One R] → [Zero R] → [Add R] → ℕ → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The numeral `((0+1)+⋯)+1`.
-/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`
. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` a
re not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidW
ithOne`) through
`Zero` and `One`, respectively.
-/
instance (priority := 100) instOfNatAtLeastTwo {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast

library_note «no_index around OfNat.ofNat»
/--
When writing lemmas about `OfNat.ofNat` that assume `Nat.AtLeastTwo`, the term needs to be wrapped
in `no_index` so as not to confuse `simp`, as `no_index (OfNat.ofNat n)`.

Rather than referencing this library note, use `ofNat(n)` as a shorthand for
`no_index (OfNat.ofNat n)`.

Some discussion is [on Zulip here](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20Polynomial.2Ecoeff.20example/near/395438147).
-/

/-
**Nat.cast_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.AtLeastTwo], ↑(OfN
at.ofNat n) = OfNat.ofNat n
参数：OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When writing lemmas about `OfNat.ofNat` that assume `Nat.AtLeastTwo`, the term n
eeds to be wrapped
in `no_index` so as not to confuse `simp`, as `no_index (OfNat.ofNat n)`.

Rather than referencing this library note, use `ofNat(n)` as a shorthand for
`no_index (OfNat.ofNat n)`.

Some discussion is [on Zulip here](https://leanprover.zulipchat.com/#narrow/stre
am/287929-mathlib4/topic/.E2.9C.94.20Polynomial.2Ecoeff.20example/near/395438147
).
-/
@[simp, norm_cast] theorem Nat.cast_ofNat {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast ofNat(n) : R) = ofNat(n) := rfl

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
/-
**AddMonoidWithOne** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where n
atCast
参数：R : Type*。
继承自：NatCast R, AddMonoid R, One R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`. -/
/-
**AddCommMonoidWithOne** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.
-/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R

namespace Nat

variable [AddMonoidWithOne R]

@[simp, norm_cast]
/-
**Nat.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_zero : ((0 : Nat) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
-/
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero

-- Lemmas about `Nat.succ` need to get a low priority, so that they are tried last.
-- This is because `Nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[norm_cast 500]
/-
**Nat.cast_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _

@[simp, norm_cast]
/-
**Nat.cast_ite** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m n : Nat) : R) = 
ite P (m : R) (n : R)
参数：P : Prop；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) :
    ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl

@[simp, norm_cast]
/-
**Nat.cast_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_one : ((1 : Nat) : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem cast_one : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]

@[simp, norm_cast]
/-
**Nat.cast_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem cast_add (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]
/-
**Nat.cast_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
-/
theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
/-
**Nat.cast_one_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_one_add (n : Nat) : ((1 + n : Nat) : R) = 1 + n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem cast_one_add (n : ℕ) : ((1 + n : ℕ) : R) = 1 + n := by
  rw [Nat.cast_add, Nat.cast_one]

end Nat

namespace Nat

/-- Computationally friendlier cast than `Nat.unaryCast`, using binary representation. -/
/-
**Nat.binCast** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{R : Type u_1} → [Zero R] → [One R] → [Add R] → ℕ → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computationally friendlier cast than `Nat.unaryCast`, using binary representatio
n.
-/
protected def binCast [Zero R] [One R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1

@[simp]
/-
**Nat.binCast_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binCast_eq [AddMonoidWithOne R] (n : Nat) : (Nat.binCast n : R) = ((n : Na
t) : R)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binCast.eq_1`：∀ {R : Type u_1} [inst : Zero R] [inst_1 : One R] [ins
t_2 : Add R], Nat.binCast 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.binCast.eq_2`：∀ {R : Type u_1} [inst : Zero R] [inst_1 : One R] [ins
t_2 : Add R] (n : ℕ),   n.succ.binCast =     if (n + 1) % 2 = 0 then ((n + 1) / 
2).bin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.mod_two_eq_zero_or_one`：∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binCast_eq [AddMonoidWithOne R] (n : ℕ) :
    (Nat.binCast n : R) = ((n : ℕ) : R) := by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_pos h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        rw [h, Nat.zero_add, Nat.succ_mul, Nat.one_mul]
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_neg h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        have h1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one (succ k)) h
        rw [h1, Nat.add_comm 1, Nat.succ_mul, Nat.one_mul]
        simp only [Nat.cast_add, Nat.cast_one]
/-
**Nat.cast_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_two [NatCast R] : ((2 : ℕ) : R) = (2 : R) := rfl
/-
**Nat.cast_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_three [NatCast R] : ((3 : Nat) : R) = (3 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_three [NatCast R] : ((3 : ℕ) : R) = (3 : R) := rfl
/-
**Nat.cast_four** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_four [NatCast R] : ((4 : Nat) : R) = (4 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_four [NatCast R] : ((4 : ℕ) : R) = (4 : R) := rfl

attribute [simp, norm_cast] Int.natAbs_natCast

end Nat

/-- `AddMonoidWithOne` implementation using unary recursion. -/
/-
**AddMonoidWithOne.unary** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidWithOne`。
形式化陈述：{R : Type u_1} → [AddMonoid R] → [One R] → AddMonoidWithOne R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidWithOne` implementation using unary recursion.
-/
protected abbrev AddMonoidWithOne.unary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }

/-- `AddMonoidWithOne` implementation using binary recursion. -/
/-
**AddMonoidWithOne.binary** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidWithOne`。
形式化陈述：{R : Type u_1} → [AddMonoid R] → [One R] → AddMonoidWithOne R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidWithOne` implementation using binary recursion.
-/
protected abbrev AddMonoidWithOne.binary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast],
    natCast_succ := fun n => by
      let : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq, Nat.binCast_eq, Nat.cast_succ] }
/-
**one_add_one_eq_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2 : R) := by
  rw [← Nat.cast_one, ← Nat.cast_add]
  apply congrArg
  decide
/-
**two_add_one_eq_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 = (3 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 = (3 : R) := by
  rw [← one_add_one_eq_two, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide
/-
**three_add_one_eq_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：three_add_one_eq_four [AddMonoidWithOne R] : 3 + 1 = (4 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_add_one_eq_three`：two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 
= (3 : R)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem three_add_one_eq_four [AddMonoidWithOne R] : 3 + 1 = (4 : R) := by
  rw [← two_add_one_eq_three, ← one_add_one_eq_two, ← Nat.cast_one,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide
/-
**two_add_two_eq_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = (4 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = (4 : R) := by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]

section nsmul

/-
**nsmul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nsmul_one {A} [AddMonoidWithOne A] : ∀ n : ℕ, n • (1 : A) = n
  | 0 => by simp [zero_nsmul]
  | n + 1 => by simp [succ_nsmul, nsmul_one n]

end nsmul

