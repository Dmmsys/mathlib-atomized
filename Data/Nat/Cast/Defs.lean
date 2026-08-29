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
`AddMonoid` with a one. In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as the coercion `Nat.cast`.

## Main declarations

* `NatCast`: Type class for `Nat.cast`.
* `AddMonoidWithOne`: Type class for which `Nat.cast` is a canonical monoid homomorphism from `ℕ`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/

@[expose] public section

variable {R : Type*}

/--
Definition of `Nat.unaryCast` / `Nat.unaryCast` 的定义

English:
definition Nat.unaryCast
  signature: [One R] [Zero R] [Add R]

中文:
定义 自然数.unaryCast
  签名: [幺 R] [零 R] [加法 R]
-/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : Nat -> R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check. Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
instance (priority := 100) instOfNatAtLeastTwo {n : Nat} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast

library_note «no_index around OfNat.ofNat»

/--
theorem `Nat.cast_ofNat` / 定理 `Nat.cast_ofNat`

English:
theorem Nat.cast_ofNat
  given: {n : Nat} [NatCast R] [Nat.AtLeastTwo n]
  proof: rfl

中文:
定理 自然数.cast_of自然数
  条件: {n : 自然数} [自然数嵌入 R] [自然数.AtLeastTwo n]
  证明: rfl
-/
@[simp, norm_cast] theorem Nat.cast_ofNat {n : Nat} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast ofNat(n) : R) = ofNat(n) := rfl

/-! ### Additive monoids with one -/

/--
Definition of `AddMonoidWithOne` / `AddMonoidWithOne` 的定义

English:
class AddMonoidWithOne
  parameters: (R : Type*)
  extends: NatCast R, AddMonoid R, One R
  axioms and operations (3):
    - natCast : = Nat.unaryCast
    - natCast_zero : natCast 0 = 0  [default: by intros; rfl]
    - natCast_succ : forall n, natCast (n + 1) = natCast n + 1  [default: by intros; rfl]

中文:
类 加法带幺幺半群
  参数: (R : 类型)
  继承: 自然数嵌入 R, 加法幺半群 R, 幺 R
  公理与运算 (3 个):
    - natCast : = 自然数.unaryCast
    - natCast_zero : natCast 0 = 0  [默认: by intros; rfl]
    - natCast_succ : 对任意 n, natCast (n + 1) = natCast n + 1  [默认: by intros; rfl]

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : forall n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/--
Definition of `AddCommMonoidWithOne` / `AddCommMonoidWithOne` 的定义

English:
class AddCommMonoidWithOne
  parameters: (R : Type*)
  extends: AddMonoidWithOne R, AddCommMonoid R
  (no additional axioms)

中文:
类 加法交换带幺幺半群
  参数: (R : 类型)
  继承: 加法带幺幺半群 R, 加法交换幺半群 R
  (无附加公理)
-/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R

namespace Nat

variable [AddMonoidWithOne R]

@[simp, norm_cast]
/--
theorem `cast_zero` / 定理 `cast_zero`

English:
theorem cast_zero
  statement: ((0 : Nat) : R) = 0
  proof: AddMonoidWithOne.natCast_zero

中文:
定理 cast_zero
  结论: ((0 : 自然数) : R) = 0
  证明: AddMonoidWithOne.natCast_zero

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.natCast_zero, natCast_zero
-/
theorem cast_zero : ((0 : Nat) : R) = 0 :=
  AddMonoidWithOne.natCast_zero

-- Lemmas about `Nat.succ` need to get a low priority, so that they are tried last.
-- This is because `Nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[norm_cast 500]
/--
theorem `cast_succ` / 定理 `cast_succ`

English:
theorem cast_succ
  given: (n : Nat)
  statement: ((succ n : Nat) : R) = n + 1
  proof: AddMonoidWithOne.natCast_succ _

@[simp, norm_cast]

中文:
定理 cast_succ
  条件: (n : 自然数)
  结论: ((succ n : 自然数) : R) = n + 1
  证明: AddMonoidWithOne.natCast_succ _

@[simp, norm_cast]

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.natCast_succ, natCast_succ
-/
theorem cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _

@[simp, norm_cast]
/--
theorem `cast_ite` / 定理 `cast_ite`

English:
theorem cast_ite
  given: (P : Prop) [Decidable P] (m n : Nat)
  proof: by
  split_ifs <;> rfl

@[simp, norm_cast]

中文:
定理 cast_ite
  条件: (P : 命题) [可判定 P] (m n : 自然数)
  证明: by
  split_ifs <;> rfl

@[simp, norm_cast]

Depends on / 依赖: split_ifs
-/
theorem cast_ite (P : Prop) [Decidable P] (m n : Nat) :
    ((ite P m n : Nat) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl

@[simp, norm_cast]
/--
theorem `cast_one` / 定理 `cast_one`

English:
theorem cast_one
  statement: ((1 : Nat) : R) = 1
  proof: by
  rw [cast_succ]; rw [Nat.cast_zero]; rw [zero_add]

@[simp, norm_cast]

中文:
定理 cast_one
  结论: ((1 : 自然数) : R) = 1
  证明: by
  rw [cast_succ]; rw [Nat.cast_zero]; rw [zero_add]

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_zero, cast_succ, cast_zero, zero_add
-/
theorem cast_one : ((1 : Nat) : R) = 1 := by
  rw [cast_succ]; rw [Nat.cast_zero]; rw [zero_add]

@[simp, norm_cast]
/--
theorem `cast_add` / 定理 `cast_add`

English:
theorem cast_add
  given: (m n : Nat)
  statement: ((m + n : Nat) : R) = m + n
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]

中文:
定理 cast_add
  条件: (m n : 自然数)
  结论: ((m + n : 自然数) : R) = m + n
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]

Depends on / 依赖: add_assoc, add_succ, cast_succ
-/
theorem cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]

/--
theorem `cast_add_one` / 定理 `cast_add_one`

English:
theorem cast_add_one
  given: (n : Nat)
  statement: ((n + 1 : Nat) : R) = n + 1
  proof: cast_succ _

中文:
定理 cast_add_one
  条件: (n : 自然数)
  结论: ((n + 1 : 自然数) : R) = n + 1
  证明: cast_succ _

Depends on / 依赖: cast_succ
-/
theorem cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1 :=
  cast_succ _

/--
theorem `cast_one_add` / 定理 `cast_one_add`

English:
theorem cast_one_add
  given: (n : Nat)
  statement: ((1 + n : Nat) : R) = 1 + n
  proof: by
  rw [Nat.cast_add]; rw [Nat.cast_one]

中文:
定理 cast_one_add
  条件: (n : 自然数)
  结论: ((1 + n : 自然数) : R) = 1 + n
  证明: by
  rw [Nat.cast_add]; rw [Nat.cast_one]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one
-/
theorem cast_one_add (n : Nat) : ((1 + n : Nat) : R) = 1 + n := by
  rw [Nat.cast_add]; rw [Nat.cast_one]

end Nat

namespace Nat

/--
Definition of `binCast` / `binCast` 的定义

English:
definition binCast
  signature: [Zero R] [One R] [Add R]

中文:
定义 binCast
  签名: [零 R] [幺 R] [加法 R]
-/
protected def binCast [Zero R] [One R] [Add R] : Nat -> R
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1

@[simp]
/--
theorem `binCast_eq` / 定理 `binCast_eq`

English:
theorem binCast_eq
  given: [AddMonoidWithOne R] (n : Nat)
  proof: by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_pos h]; rw [hk _ <| Nat.div_lt_self (Na

中文:
定理 binCast_eq
  条件: [加法带幺幺半群 R] (n : 自然数)
  证明: by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_pos h]; rw [hk _ <| Nat.div_lt_self (Na

Depends on / 依赖: Nat.binCast, Nat.cast_add, Nat.cast_zero, Nat.div_lt_self, Nat.le_ref, Nat.le_refl, Nat.mod_add_div, Nat.one_mul, Nat.strongRecOn, Nat.succ_mul, Nat.succ_pos, Nat.zero_add, binCast, cast_add, cast_zero, div_lt_self, if_neg, if_pos, le_ref, le_refl
-/
theorem binCast_eq [AddMonoidWithOne R] (n : Nat) :
    (Nat.binCast n : R) = ((n : Nat) : R) := by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_pos h]; rw [hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2)]; rw [← Nat.cast_add]
        rw [h]; rw [Nat.zero_add]; rw [Nat.succ_mul]; rw [Nat.one_mul]
      · conv => rhs; rw [← Nat.mod_add_div (k + 1) 2]
        rw [if_neg h]; rw [hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2)]; rw [← Nat.cast_add]
        have h1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one (succ k)) h
        rw [h1]; rw [Nat.add_comm 1]; rw [Nat.succ_mul]; rw [Nat.one_mul]
        simp only [Nat.cast_add, Nat.cast_one]

/--
theorem `cast_two` / 定理 `cast_two`

English:
theorem cast_two
  given: [NatCast R]
  statement: ((2 : Nat) : R) = (2 : R)
  proof: rfl

中文:
定理 cast_two
  条件: [自然数嵌入 R]
  结论: ((2 : 自然数) : R) = (2 : R)
  证明: rfl
-/
theorem cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R) := rfl

/--
theorem `cast_three` / 定理 `cast_three`

English:
theorem cast_three
  given: [NatCast R]
  statement: ((3 : Nat) : R) = (3 : R)
  proof: rfl

中文:
定理 cast_three
  条件: [自然数嵌入 R]
  结论: ((3 : 自然数) : R) = (3 : R)
  证明: rfl
-/
theorem cast_three [NatCast R] : ((3 : Nat) : R) = (3 : R) := rfl

/--
theorem `cast_four` / 定理 `cast_four`

English:
theorem cast_four
  given: [NatCast R]
  statement: ((4 : Nat) : R) = (4 : R)
  proof: rfl

中文:
定理 cast_four
  条件: [自然数嵌入 R]
  结论: ((4 : 自然数) : R) = (4 : R)
  证明: rfl
-/
theorem cast_four [NatCast R] : ((4 : Nat) : R) = (4 : R) := rfl

attribute [simp, norm_cast] Int.natAbs_natCast

end Nat

/--
Definition of `AddMonoidWithOne.unary` / `AddMonoidWithOne.unary` 的定义

English:
abbreviation AddMonoidWithOne.unary
  signature: [AddMonoid R] [One R]
  body: { ‹One R›, ‹AddMonoid R› with }

中文:
缩写 加法带幺幺半群.unary
  签名: [加法幺半群 R] [幺 R]
  定义体: { ‹One R›, ‹AddMonoid R› with }
-/
protected abbrev AddMonoidWithOne.unary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }

/--
Definition of `AddMonoidWithOne.binary` / `AddMonoidWithOne.binary` 的定义

English:
abbreviation AddMonoidWithOne.binary
  signature: [AddMonoid R] [One R]
  body: { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast],
    natCast_succ := fun n => by
      let : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq]; rw [Nat.binCast_eq]; rw [Nat.cast_succ] }

中文:
缩写 加法带幺幺半群.binary
  签名: [加法幺半群 R] [幺 R]
  定义体: { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast],
    natCast_succ := fun n => by
      let : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq]; rw [Nat.binCast_eq]; rw [Nat.cast_succ] }
-/
protected abbrev AddMonoidWithOne.binary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast],
    natCast_succ := fun n => by
      let : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq]; rw [Nat.binCast_eq]; rw [Nat.cast_succ] }

/--
theorem `one_add_one_eq_two` / 定理 `one_add_one_eq_two`

English:
theorem one_add_one_eq_two
  given: [AddMonoidWithOne R]
  statement: 1 + 1 = (2 : R)
  proof: by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]
  apply congrArg
  decide

中文:
定理 one_add_one_eq_two
  条件: [加法带幺幺半群 R]
  结论: 1 + 1 = (2 : R)
  证明: by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]
  apply congrArg
  decide

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one
-/
theorem one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2 : R) := by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]
  apply congrArg
  decide

/--
theorem `two_add_one_eq_three` / 定理 `two_add_one_eq_three`

English:
theorem two_add_one_eq_three
  given: [AddMonoidWithOne R]
  statement: 2 + 1 = (3 : R)
  proof: by
  rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

中文:
定理 two_add_one_eq_three
  条件: [加法带幺幺半群 R]
  结论: 2 + 1 = (3 : R)
  证明: by
  rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one, one_add_one_eq_two
-/
theorem two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 = (3 : R) := by
  rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

/--
theorem `three_add_one_eq_four` / 定理 `three_add_one_eq_four`

English:
theorem three_add_one_eq_four
  given: [AddMonoidWithOne R]
  statement: 3 + 1 = (4 : R)
  proof: by
  rw [← two_add_one_eq_three]; rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

中文:
定理 three_add_one_eq_four
  条件: [加法带幺幺半群 R]
  结论: 3 + 1 = (4 : R)
  证明: by
  rw [← two_add_one_eq_three]; rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

Depends on / 依赖: Nat.cast_add, Nat.cast_one, cast_add, cast_one, one_add_one_eq_two, two_add_one_eq_three
-/
theorem three_add_one_eq_four [AddMonoidWithOne R] : 3 + 1 = (4 : R) := by
  rw [← two_add_one_eq_three]; rw [← one_add_one_eq_two]; rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [← Nat.cast_add]; rw [← Nat.cast_add]
  apply congrArg
  decide

/--
theorem `two_add_two_eq_four` / 定理 `two_add_two_eq_four`

English:
theorem two_add_two_eq_four
  given: [AddMonoidWithOne R]
  statement: 2 + 2 = (4 : R)
  proof: by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]

中文:
定理 two_add_two_eq_four
  条件: [加法带幺幺半群 R]
  结论: 2 + 2 = (4 : R)
  证明: by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]

Depends on / 依赖: Nat.cast_one, add_assoc, cast_one, one_add_one_eq_two, three_add_one_eq_four, two_add_one_eq_three
-/
theorem two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = (4 : R) := by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]

section nsmul

/--
lemma `nsmul_one` / 引理 `nsmul_one`

English:
lemma nsmul_one
  given: {A} [AddMonoidWithOne A]
  statement: forall n : Nat, n • (1 : A) = n

中文:
引理 nsmul_one
  条件: {A} [加法带幺幺半群 A]
  结论: 对任意 n : 自然数, n • (1 : A) = n
-/
@[simp] lemma nsmul_one {A} [AddMonoidWithOne A] : forall n : Nat, n • (1 : A) = n
  | 0 => by simp [zero_nsmul]
  | n + 1 => by simp [succ_nsmul, nsmul_one n]

end nsmul
