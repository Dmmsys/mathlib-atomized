/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Aesop
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Mathlib/Algebra/Group/Defs.lean`.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Function

variable {α β G M : Type*}

section ite
variable [Pow α β]

@[to_additive (attr := simp, to_additive) dite_smul]
/--
lemma `pow_dite` / 引理 `pow_dite`

English:
lemma pow_dite
  given: (p : Prop) [Decidable p] (a : α) (b : p -> β) (c : ¬ p -> β)
  proof: by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) smul_dite]

中文:
引理 pow_dite
  条件: (p : 命题) [Decidable p] (a : α) (b : p -> β) (c : ¬ p -> β)
  证明: by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) smul_dite]

Depends on / 依赖: split_ifs
-/
lemma pow_dite (p : Prop) [Decidable p] (a : α) (b : p -> β) (c : ¬ p -> β) :
    a ^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c h := by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) smul_dite]
/--
lemma `dite_pow` / 引理 `dite_pow`

English:
lemma dite_pow
  given: (p : Prop) [Decidable p] (a : p -> α) (b : ¬ p -> α) (c : β)
  proof: by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) ite_smul]

中文:
引理 dite_pow
  条件: (p : 命题) [Decidable p] (a : p -> α) (b : ¬ p -> α) (c : β)
  证明: by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) ite_smul]

Depends on / 依赖: split_ifs
-/
lemma dite_pow (p : Prop) [Decidable p] (a : p -> α) (b : ¬ p -> α) (c : β) :
    (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ c := by split_ifs <;> rfl

@[to_additive (attr := simp, to_additive) ite_smul]
/--
lemma `pow_ite` / 引理 `pow_ite`

English:
lemma pow_ite
  given: (p : Prop) [Decidable p] (a : α) (b c : β)
  proof: pow_dite _ _ _ _

@[to_additive (attr := simp, to_additive) smul_ite]

中文:
引理 pow_ite
  条件: (p : 命题) [Decidable p] (a : α) (b c : β)
  证明: pow_dite _ _ _ _

@[to_additive (attr := simp, to_additive) smul_ite]

Depends on / 依赖: pow_dite
-/
lemma pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) :
    a ^ (if p then b else c) = if p then a ^ b else a ^ c := pow_dite _ _ _ _

@[to_additive (attr := simp, to_additive) smul_ite]
/--
lemma `ite_pow` / 引理 `ite_pow`

English:
lemma ite_pow
  given: (p : Prop) [Decidable p] (a b : α) (c : β)
  proof: dite_pow _ _ _ _

中文:
引理 ite_pow
  条件: (p : 命题) [Decidable p] (a b : α) (c : β)
  证明: dite_pow _ _ _ _

Depends on / 依赖: dite_pow
-/
lemma ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) :
    (if p then a else b) ^ c = if p then a ^ c else b ^ c := dite_pow _ _ _ _

end ite

section Semigroup
variable [Semigroup α]

@[to_additive]
/--
Instance `Semigroup.to_isAssociative` / 实例 `Semigroup.to_isAssociative`

English:
instance Semigroup.to_isAssociative
  signature: : Std.Associative (α := α) (· * ·)
  body: ⟨mul_assoc⟩

中文:
实例 Semigroup.to_isAssociative
  签名: : Std.Associative (α := α) (· * ·)
  定义体: ⟨mul_assoc⟩

Depends on / 依赖: mul_assoc
-/
instance Semigroup.to_isAssociative : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the left by `y` then `x`
is equal to an addition on the left by `x + y`. -/]
/--
theorem `comp_mul_left` / 定理 `comp_mul_left`

English:
theorem comp_mul_left
  given: (x y : α)
  statement: (x * ·) ∘ (y * ·) = (x * y * ·)
  proof: by
  ext z
  simp [mul_assoc]

中文:
定理 comp_mul_left
  条件: (x y : α)
  结论: (x * ·) ∘ (y * ·) = (x * y * ·)
  证明: by
  ext z
  simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the right by `y` and `x`
is equal to an addition on the right by `y + x`. -/]
/--
theorem `comp_mul_right` / 定理 `comp_mul_right`

English:
theorem comp_mul_right
  given: (x y : α)
  statement: (· * x) ∘ (· * y) = (· * (y * x))
  proof: by
  ext z
  simp [mul_assoc]

中文:
定理 comp_mul_right
  条件: (x y : α)
  结论: (· * x) ∘ (· * y) = (· * (y * x))
  证明: by
  ext z
  simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]

end Semigroup

section MulOneClass

variable [MulOneClass M]

@[to_additive]
/--
Instance `Semigroup.to_isLawfulIdentity` / 实例 `Semigroup.to_isLawfulIdentity`

English:
instance Semigroup.to_isLawfulIdentity
  signature: : Std.LawfulIdentity (α := M) (· * ·) 1 where
  body: one_mul
  right_id := mul_one

@[to_additive]

中文:
实例 Semigroup.to_isLawfulIdentity
  签名: : Std.LawfulIdentity (α := M) (· * ·) 1 where
  定义体: one_mul
  right_id := mul_one

@[to_additive]
-/
instance Semigroup.to_isLawfulIdentity : Std.LawfulIdentity (α := M) (· * ·) 1 where
  left_id := one_mul
  right_id := mul_one

@[to_additive]
/--
theorem `ite_mul_one` / 定理 `ite_mul_one`

English:
theorem ite_mul_one
  given: {P : Prop} [Decidable P] {a b : M}
  proof: by
  by_cases h : P <;> simp [h]

@[to_additive]

中文:
定理 ite_mul_one
  条件: {P : 命题} [Decidable P] {a b : M}
  证明: by
  by_cases h : P <;> simp [h]

@[to_additive]
-/
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h : P <;> simp [h]

@[to_additive]
/--
theorem `ite_one_mul` / 定理 `ite_one_mul`

English:
theorem ite_one_mul
  given: {P : Prop} [Decidable P] {a b : M}
  proof: by
  by_cases h : P <;> simp [h]

@[to_additive]

中文:
定理 ite_one_mul
  条件: {P : 命题} [Decidable P] {a b : M}
  证明: by
  by_cases h : P <;> simp [h]

@[to_additive]
-/
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h : P <;> simp [h]

@[to_additive]
/--
theorem `eq_one_iff_eq_one_of_mul_eq_one` / 定理 `eq_one_iff_eq_one_of_mul_eq_one`

English:
theorem eq_one_iff_eq_one_of_mul_eq_one
  given: {a b : M} (h : a * b = 1)
  statement: a = 1 ↔ b = 1
  proof: by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]

中文:
定理 eq_one_iff_eq_one_of_mul_eq_one
  条件: {a b : M} (h : a * b = 1)
  结论: a = 1 ↔ b = 1
  证明: by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]
-/
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]
/--
theorem `one_mul_eq_id` / 定理 `one_mul_eq_id`

English:
theorem one_mul_eq_id
  statement: ((1 : M) * ·) = id
  proof: funext one_mul

@[to_additive]

中文:
定理 one_mul_eq_id
  结论: ((1 : M) * ·) = id
  证明: funext one_mul

@[to_additive]

Depends on / 依赖: one_mul
-/
theorem one_mul_eq_id : ((1 : M) * ·) = id :=
  funext one_mul

@[to_additive]
/--
theorem `mul_one_eq_id` / 定理 `mul_one_eq_id`

English:
theorem mul_one_eq_id
  statement: (· * (1 : M)) = id
  proof: funext mul_one

中文:
定理 mul_one_eq_id
  结论: (· * (1 : M)) = id
  证明: funext mul_one

Depends on / 依赖: mul_one
-/
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
/--
theorem `mul_left_comm` / 定理 `mul_left_comm`

English:
theorem mul_left_comm
  given: (a b c : G)
  statement: a * (b * c) = b * (a * c)
  proof: by
  rw [← mul_assoc]; rw [mul_comm a]; rw [mul_assoc]

@[to_additive]

中文:
定理 mul_left_comm
  条件: (a b c : G)
  结论: a * (b * c) = b * (a * c)
  证明: by
  rw [← mul_assoc]; rw [mul_comm a]; rw [mul_assoc]

@[to_additive]

Depends on / 依赖: mul_assoc, mul_comm
-/
theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]; rw [mul_comm a]; rw [mul_assoc]

@[to_additive]
/--
theorem `mul_right_comm` / 定理 `mul_right_comm`

English:
theorem mul_right_comm
  given: (a b c : G)
  statement: a * b * c = a * c * b
  proof: by
  rw [mul_assoc]; rw [mul_comm b]; rw [mul_assoc]

@[to_additive]

中文:
定理 mul_right_comm
  条件: (a b c : G)
  结论: a * b * c = a * c * b
  证明: by
  rw [mul_assoc]; rw [mul_comm b]; rw [mul_assoc]

@[to_additive]

Depends on / 依赖: mul_assoc, mul_comm
-/
theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc]; rw [mul_comm b]; rw [mul_assoc]

@[to_additive]
/--
theorem `mul_mul_mul_comm` / 定理 `mul_mul_mul_comm`

English:
theorem mul_mul_mul_comm
  given: (a b c d : G)
  statement: a * b * (c * d) = a * c * (b * d)
  proof: by
  simp only [mul_left_comm, mul_assoc]

@[to_additive]

中文:
定理 mul_mul_mul_comm
  条件: (a b c d : G)
  结论: a * b * (c * d) = a * c * (b * d)
  证明: by
  simp only [mul_left_comm, mul_assoc]

@[to_additive]

Depends on / 依赖: mul_assoc, mul_left_comm
-/
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]

@[to_additive]
/--
theorem `mul_mul_mul_comm'` / 定理 `mul_mul_mul_comm'`

English:
theorem mul_mul_mul_comm'
  given: (a b c d : G)
  statement: a * b * c * d = a * c * b * d
  proof: by
  grind

@[to_additive]

中文:
定理 mul_mul_mul_comm'
  条件: (a b c d : G)
  结论: a * b * c * d = a * c * b * d
  证明: by
  grind

@[to_additive]
-/
theorem mul_mul_mul_comm' (a b c d : G) : a * b * c * d = a * c * b * d := by
  grind

@[to_additive]
/--
theorem `mul_rotate` / 定理 `mul_rotate`

English:
theorem mul_rotate
  given: (a b c : G)
  statement: a * b * c = b * c * a
  proof: by
  simp only [mul_left_comm, mul_comm]

@[to_additive]

中文:
定理 mul_rotate
  条件: (a b c : G)
  结论: a * b * c = b * c * a
  证明: by
  simp only [mul_left_comm, mul_comm]

@[to_additive]

Depends on / 依赖: mul_comm, mul_left_comm
-/
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]

@[to_additive]
/--
theorem `mul_rotate'` / 定理 `mul_rotate'`

English:
theorem mul_rotate'
  given: (a b c : G)
  statement: a * (b * c) = b * (c * a)
  proof: by
  simp only [mul_left_comm, mul_comm]

中文:
定理 mul_rotate'
  条件: (a b c : G)
  结论: a * (b * c) = b * (c * a)
  证明: by
  simp only [mul_left_comm, mul_comm]

Depends on / 依赖: mul_comm, mul_left_comm
-/
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]

end CommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section Monoid
variable [Monoid M] {a b : M} {m n : Nat}

@[to_additive boole_nsmul]
/--
lemma `pow_boole` / 引理 `pow_boole`

English:
lemma pow_boole
  given: (P : Prop) [Decidable P] (a : M)
  proof: by simp only [pow_ite, pow_one, pow_zero]

@[to_additive nsmul_add_sub_nsmul]

中文:
引理 pow_boole
  条件: (P : 命题) [Decidable P] (a : M)
  证明: by simp only [pow_ite, pow_one, pow_zero]

@[to_additive nsmul_add_sub_nsmul]

Depends on / 依赖: pow_ite, pow_one, pow_zero
-/
lemma pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp only [pow_ite, pow_one, pow_zero]

@[to_additive nsmul_add_sub_nsmul]
/--
lemma `pow_mul_pow_sub` / 引理 `pow_mul_pow_sub`

English:
lemma pow_mul_pow_sub
  given: (a : M) (h : m <= n)
  statement: a ^ m * a ^ (n - m) = a ^ n
  proof: by
  rw [← pow_add]; rw [Nat.add_comm]; rw [Nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]

中文:
引理 pow_mul_pow_sub
  条件: (a : M) (h : m <= n)
  结论: a ^ m * a ^ (n - m) = a ^ n
  证明: by
  rw [← pow_add]; rw [Nat.add_comm]; rw [Nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]

Depends on / 依赖: Nat.add_comm, Nat.sub_add_cancel, add_comm, pow_add, sub_add_cancel
-/
lemma pow_mul_pow_sub (a : M) (h : m <= n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add]; rw [Nat.add_comm]; rw [Nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]
/--
lemma `pow_sub_mul_pow` / 引理 `pow_sub_mul_pow`

English:
lemma pow_sub_mul_pow
  given: (a : M) (h : m <= n)
  statement: a ^ (n - m) * a ^ m = a ^ n
  proof: by
  rw [← pow_add]; rw [Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]

中文:
引理 pow_sub_mul_pow
  条件: (a : M) (h : m <= n)
  结论: a ^ (n - m) * a ^ m = a ^ n
  证明: by
  rw [← pow_add]; rw [Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]

Depends on / 依赖: Nat.sub_add_cancel, pow_add, sub_add_cancel
-/
lemma pow_sub_mul_pow (a : M) (h : m <= n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add]; rw [Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]
/--
lemma `mul_pow_sub_one` / 引理 `mul_pow_sub_one`

English:
lemma mul_pow_sub_one
  given: (hn : n != 0) (a : M)
  statement: a * a ^ (n - 1) = a ^ n
  proof: by
  rw [← pow_succ']; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]

中文:
引理 mul_pow_sub_one
  条件: (hn : n != 0) (a : M)
  结论: a * a ^ (n - 1) = a ^ n
  证明: by
  rw [← pow_succ']; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]

Depends on / 依赖: Nat.one_le_iff_ne_zero, Nat.sub_add_cancel, one_le_iff_ne_zero, pow_succ, sub_add_cancel
-/
lemma mul_pow_sub_one (hn : n != 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ']; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]
/--
lemma `pow_sub_one_mul` / 引理 `pow_sub_one_mul`

English:
lemma pow_sub_one_mul
  given: (hn : n != 0) (a : M)
  statement: a ^ (n - 1) * a = a ^ n
  proof: by
  rw [← pow_succ]; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

中文:
引理 pow_sub_one_mul
  条件: (hn : n != 0) (a : M)
  结论: a ^ (n - 1) * a = a ^ n
  证明: by
  rw [← pow_succ]; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

Depends on / 依赖: Nat.one_le_iff_ne_zero, Nat.sub_add_cancel, one_le_iff_ne_zero, pow_succ, sub_add_cancel
-/
lemma pow_sub_one_mul (hn : n != 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ]; rw [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul /-- If `n • x = 0`, then `m • x` is the same as `(m % n) • x` -/]
/--
lemma `pow_eq_pow_mod` / 引理 `pow_eq_pow_mod`

English:
lemma pow_eq_pow_mod
  given: (m : Nat) (ha : a ^ n = 1)
  statement: a ^ m = a ^ (m % n)
  proof: by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

中文:
引理 pow_eq_pow_mod
  条件: (m : 自然数) (ha : a ^ n = 1)
  结论: a ^ m = a ^ (m % n)
  证明: by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

Depends on / 依赖: Nat.mod_add_div, mod_add_div, pow_add, pow_mul
-/
lemma pow_eq_pow_mod (m : Nat) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

/--
lemma `pow_mul_pow_eq_one` / 引理 `pow_mul_pow_eq_one`

English:
lemma pow_mul_pow_eq_one
  statement: forall n, a * b = 1 -> a ^ n * b ^ n = 1
  proof: by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]

@[to_additive (attr := simp)]

中文:
引理 pow_mul_pow_eq_one
  结论: 对任意 n, a * b = 1 -> a ^ n * b ^ n = 1
  证明: by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]

@[to_additive (attr := simp)]
-/
@[to_additive] lemma pow_mul_pow_eq_one : forall n, a * b = 1 -> a ^ n * b ^ n = 1
  | 0, _ => by simp
  | n + 1, h =>
    calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]

@[to_additive (attr := simp)]
/--
lemma `mul_left_iterate` / 引理 `mul_left_iterate`

English:
lemma mul_left_iterate
  given: (a : M)
  statement: forall n : Nat, (a * ·)^[n] = (a ^ n * ·)

中文:
引理 mul_left_iterate
  条件: (a : M)
  结论: 对任意 n : 自然数, (a * ·)^[n] = (a ^ n * ·)
-/
lemma mul_left_iterate (a : M) : forall n : Nat, (a * ·)^[n] = (a ^ n * ·)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ, mul_left_iterate]

@[to_additive (attr := simp)]
/--
lemma `mul_right_iterate` / 引理 `mul_right_iterate`

English:
lemma mul_right_iterate
  given: (a : M)
  statement: forall n : Nat, (· * a)^[n] = (· * a ^ n)

中文:
引理 mul_right_iterate
  条件: (a : M)
  结论: 对任意 n : 自然数, (· * a)^[n] = (· * a ^ n)
-/
lemma mul_right_iterate (a : M) : forall n : Nat, (· * a)^[n] = (· * a ^ n)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ', mul_right_iterate]

/-- Version of `mul_left_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_left_iterate` that is fully applied, for `rw`. -/]
/--
lemma `mul_left_iterate_apply` / 引理 `mul_left_iterate_apply`

English:
lemma mul_left_iterate_apply
  given: (a b : M)
  statement: (a * ·)^[n] b = a ^ n * b
  proof: by simp

中文:
引理 mul_left_iterate_apply
  条件: (a b : M)
  结论: (a * ·)^[n] b = a ^ n * b
  证明: by simp
-/
lemma mul_left_iterate_apply (a b : M) : (a * ·)^[n] b = a ^ n * b := by simp

/-- Version of `mul_right_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_right_iterate` that is fully applied, for `rw`. -/ ]
/--
lemma `mul_right_iterate_apply` / 引理 `mul_right_iterate_apply`

English:
lemma mul_right_iterate_apply
  given: (a b : M)
  statement: (· * a)^[n] b = b * a ^ n
  proof: by simp

@[to_additive]

中文:
引理 mul_right_iterate_apply
  条件: (a b : M)
  结论: (· * a)^[n] b = b * a ^ n
  证明: by simp

@[to_additive]
-/
lemma mul_right_iterate_apply (a b : M) : (· * a)^[n] b = b * a ^ n := by simp

@[to_additive]
/--
lemma `mul_left_iterate_apply_one` / 引理 `mul_left_iterate_apply_one`

English:
lemma mul_left_iterate_apply_one
  given: (a : M)
  statement: (a * ·)^[n] 1 = a ^ n
  proof: by simp

@[to_additive]

中文:
引理 mul_left_iterate_apply_one
  条件: (a : M)
  结论: (a * ·)^[n] 1 = a ^ n
  证明: by simp

@[to_additive]
-/
lemma mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n := by simp

@[to_additive]
/--
lemma `mul_right_iterate_apply_one` / 引理 `mul_right_iterate_apply_one`

English:
lemma mul_right_iterate_apply_one
  given: (a : M)
  statement: (· * a)^[n] 1 = a ^ n
  proof: by simp [mul_right_iterate]

@[to_additive, simp]

中文:
引理 mul_right_iterate_apply_one
  条件: (a : M)
  结论: (· * a)^[n] 1 = a ^ n
  证明: by simp [mul_right_iterate]

@[to_additive, simp]

Depends on / 依赖: mul_right_iterate
-/
lemma mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n := by simp [mul_right_iterate]

@[to_additive, simp]
/--
lemma `pow_iterate` / 引理 `pow_iterate`

English:
lemma pow_iterate
  given: (k : Nat)
  statement: forall n : Nat, (fun x : M => x ^ k)^[n] = (· ^ k ^ n)

中文:
引理 pow_iterate
  条件: (k : 自然数)
  结论: 对任意 n : 自然数, (fun x : M => x ^ k)^[n] = (· ^ k ^ n)
-/
lemma pow_iterate (k : Nat) : forall n : Nat, (fun x : M => x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp
  | n + 1 => by ext; simp [pow_iterate, Nat.pow_succ', pow_mul]

end Monoid

section CommMonoid
variable [CommMonoid M] {x y z : M}

@[to_additive]
/--
theorem `inv_unique` / 定理 `inv_unique`

English:
theorem inv_unique
  given: (hy : x * y = 1) (hz : x * z = 1)
  statement: y = z
  proof: left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

中文:
定理 inv_unique
  条件: (hy : x * y = 1) (hz : x * z = 1)
  结论: y = z
  证明: left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

Depends on / 依赖: Trans.trans, left_inv_eq_right_inv, mul_comm
-/
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

/--
lemma `mul_pow` / 引理 `mul_pow`

English:
lemma mul_pow
  given: (a b : M)
  statement: forall n, (a * b) ^ n = a ^ n * b ^ n

中文:
引理 mul_pow
  条件: (a b : M)
  结论: 对任意 n, (a * b) ^ n = a ^ n * b ^ n
-/
@[to_additive nsmul_add] lemma mul_pow (a b : M) : forall n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by rw [pow_succ', pow_succ', pow_succ', mul_pow, mul_mul_mul_comm]

end CommMonoid

section LeftCancelMonoid

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

@[to_additive (attr := simp)]
/--
theorem `mul_eq_left` / 定理 `mul_eq_left`

English:
theorem mul_eq_left
  statement: a * b = a ↔ b = 1
  proof: calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[to_additive (attr := simp)]

中文:
定理 mul_eq_left
  结论: a * b = a ↔ b = 1
  证明: calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[to_additive (attr := simp)]
-/
theorem mul_eq_left : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[to_additive (attr := simp)]
/--
theorem `left_eq_mul` / 定理 `left_eq_mul`

English:
theorem left_eq_mul
  statement: a = a * b ↔ b = 1
  proof: eq_comm.trans mul_eq_left

@[to_additive]

中文:
定理 left_eq_mul
  结论: a = a * b ↔ b = 1
  证明: eq_comm.trans mul_eq_left

@[to_additive]

Depends on / 依赖: eq_comm, eq_comm.trans, mul_eq_left
-/
theorem left_eq_mul : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_eq_left

@[to_additive]
/--
theorem `mul_ne_left` / 定理 `mul_ne_left`

English:
theorem mul_ne_left
  statement: a * b != a ↔ b != 1
  proof: mul_eq_left.not

@[to_additive]

中文:
定理 mul_ne_left
  结论: a * b != a ↔ b != 1
  证明: mul_eq_left.not

@[to_additive]

Depends on / 依赖: mul_eq_left, mul_eq_left.not
-/
theorem mul_ne_left : a * b != a ↔ b != 1 := mul_eq_left.not

@[to_additive]
/--
theorem `left_ne_mul` / 定理 `left_ne_mul`

English:
theorem left_ne_mul
  statement: a != a * b ↔ b != 1
  proof: left_eq_mul.not

中文:
定理 left_ne_mul
  结论: a != a * b ↔ b != 1
  证明: left_eq_mul.not

Depends on / 依赖: left_eq_mul, left_eq_mul.not
-/
theorem left_ne_mul : a != a * b ↔ b != 1 := left_eq_mul.not

end LeftCancelMonoid

section RightCancelMonoid

variable [Monoid M] [IsRightCancelMul M] {a b : M}

@[to_additive (attr := simp)]
/--
theorem `mul_eq_right` / 定理 `mul_eq_right`

English:
theorem mul_eq_right
  statement: a * b = b ↔ a = 1
  proof: calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[to_additive (attr := simp)]

中文:
定理 mul_eq_right
  结论: a * b = b ↔ a = 1
  证明: calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[to_additive (attr := simp)]
-/
theorem mul_eq_right : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[to_additive (attr := simp)]
/--
theorem `right_eq_mul` / 定理 `right_eq_mul`

English:
theorem right_eq_mul
  statement: b = a * b ↔ a = 1
  proof: eq_comm.trans mul_eq_right

@[to_additive]

中文:
定理 right_eq_mul
  结论: b = a * b ↔ a = 1
  证明: eq_comm.trans mul_eq_right

@[to_additive]

Depends on / 依赖: eq_comm, eq_comm.trans, mul_eq_right
-/
theorem right_eq_mul : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_eq_right

@[to_additive]
/--
theorem `mul_ne_right` / 定理 `mul_ne_right`

English:
theorem mul_ne_right
  statement: a * b != b ↔ a != 1
  proof: mul_eq_right.not

@[to_additive]

中文:
定理 mul_ne_right
  结论: a * b != b ↔ a != 1
  证明: mul_eq_right.not

@[to_additive]

Depends on / 依赖: mul_eq_right, mul_eq_right.not
-/
theorem mul_ne_right : a * b != b ↔ a != 1 := mul_eq_right.not

@[to_additive]
/--
theorem `right_ne_mul` / 定理 `right_ne_mul`

English:
theorem right_ne_mul
  statement: b != a * b ↔ a != 1
  proof: right_eq_mul.not

中文:
定理 right_ne_mul
  结论: b != a * b ↔ a != 1
  证明: right_eq_mul.not

Depends on / 依赖: right_eq_mul, right_eq_mul.not
-/
theorem right_ne_mul : b != a * b ↔ a != 1 := right_eq_mul.not

end RightCancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] {a b c d : α}

/--
lemma `eq_iff_eq_of_mul_eq_mul` / 引理 `eq_iff_eq_of_mul_eq_mul`

English:
lemma eq_iff_eq_of_mul_eq_mul
  given: (h : a * b = c * d)
  statement: a = c ↔ b = d
  proof: by aesop

中文:
引理 eq_iff_eq_of_mul_eq_mul
  条件: (h : a * b = c * d)
  结论: a = c ↔ b = d
  证明: by aesop
-/
@[to_additive] lemma eq_iff_eq_of_mul_eq_mul (h : a * b = c * d) : a = c ↔ b = d := by aesop
/--
lemma `ne_iff_ne_of_mul_eq_mul` / 引理 `ne_iff_ne_of_mul_eq_mul`

English:
lemma ne_iff_ne_of_mul_eq_mul
  given: (h : a * b = c * d)
  statement: a != c ↔ b != d
  proof: by aesop

中文:
引理 ne_iff_ne_of_mul_eq_mul
  条件: (h : a * b = c * d)
  结论: a != c ↔ b != d
  证明: by aesop
-/
@[to_additive] lemma ne_iff_ne_of_mul_eq_mul (h : a * b = c * d) : a != c ↔ b != d := by aesop

end CancelCommMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := simp)]
/--
theorem `inv_involutive` / 定理 `inv_involutive`

English:
theorem inv_involutive
  statement: Function.Involutive (Inv.inv : G -> G)
  proof: inv_inv

@[to_additive]

中文:
定理 inv_involutive
  结论: Function.Involutive (Inv.inv : G -> G)
  证明: inv_inv

@[to_additive]

Depends on / 依赖: inv_inv
-/
theorem inv_involutive : Function.Involutive (Inv.inv : G -> G) :=
  inv_inv

@[to_additive]
/--
theorem `inv_bijective` / 定理 `inv_bijective`

English:
theorem inv_bijective
  statement: Function.Bijective (Inv.inv : G -> G)
  proof: inv_involutive.bijective

@[to_additive (attr := simp)]

中文:
定理 inv_bijective
  结论: Function.Bijective (Inv.inv : G -> G)
  证明: inv_involutive.bijective

@[to_additive (attr := simp)]

Depends on / 依赖: bijective, inv_involutive, inv_involutive.bijective
-/
theorem inv_bijective : Function.Bijective (Inv.inv : G -> G) :=
  inv_involutive.bijective

@[to_additive (attr := simp)]
/--
theorem `inv_surjective` / 定理 `inv_surjective`

English:
theorem inv_surjective
  statement: Function.Surjective (Inv.inv : G -> G)
  proof: inv_involutive.surjective

@[to_additive]

中文:
定理 inv_surjective
  结论: Function.Surjective (Inv.inv : G -> G)
  证明: inv_involutive.surjective

@[to_additive]

Depends on / 依赖: inv_involutive, inv_involutive.surjective, surjective
-/
theorem inv_surjective : Function.Surjective (Inv.inv : G -> G) :=
  inv_involutive.surjective

@[to_additive]
/--
theorem `inv_injective` / 定理 `inv_injective`

English:
theorem inv_injective
  statement: Function.Injective (Inv.inv : G -> G)
  proof: inv_involutive.injective

@[to_additive (attr := simp)]

中文:
定理 inv_injective
  结论: Function.Injective (Inv.inv : G -> G)
  证明: inv_involutive.injective

@[to_additive (attr := simp)]

Depends on / 依赖: injective, inv_involutive, inv_involutive.injective
-/
theorem inv_injective : Function.Injective (Inv.inv : G -> G) :=
  inv_involutive.injective

@[to_additive (attr := simp)]
/--
theorem `inv_inj` / 定理 `inv_inj`

English:
theorem inv_inj
  statement: a⁻¹ = b⁻¹ ↔ a = b
  proof: inv_injective.eq_iff

@[to_additive]

中文:
定理 inv_inj
  结论: a⁻¹ = b⁻¹ ↔ a = b
  证明: inv_injective.eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, inv_injective, inv_injective.eq_iff
-/
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

@[to_additive]
/--
theorem `inv_eq_iff_eq_inv` / 定理 `inv_eq_iff_eq_inv`

English:
theorem inv_eq_iff_eq_inv
  statement: a⁻¹ = b ↔ a = b⁻¹
  proof: inv_involutive.eq_iff

中文:
定理 inv_eq_iff_eq_inv
  结论: a⁻¹ = b ↔ a = b⁻¹
  证明: inv_involutive.eq_iff

Depends on / 依赖: eq_iff, inv_involutive, inv_involutive.eq_iff
-/
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  inv_involutive.eq_iff

variable (G)

@[to_additive]
/--
theorem `inv_comp_inv` / 定理 `inv_comp_inv`

English:
theorem inv_comp_inv
  statement: Inv.inv ∘ Inv.inv = @id G
  proof: inv_involutive.comp_self

@[to_additive]

中文:
定理 inv_comp_inv
  结论: Inv.inv ∘ Inv.inv = @id G
  证明: inv_involutive.comp_self

@[to_additive]

Depends on / 依赖: comp_self, inv_involutive, inv_involutive.comp_self
-/
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

@[to_additive]
/--
theorem `leftInverse_inv` / 定理 `leftInverse_inv`

English:
theorem leftInverse_inv
  statement: LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹
  proof: inv_inv

@[to_additive]

中文:
定理 leftInverse_inv
  结论: LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹
  证明: inv_inv

@[to_additive]

Depends on / 依赖: inv_inv
-/
theorem leftInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

@[to_additive]
/--
theorem `rightInverse_inv` / 定理 `rightInverse_inv`

English:
theorem rightInverse_inv
  statement: RightInverse (fun a : G => a⁻¹) fun a => a⁻¹
  proof: inv_inv

中文:
定理 rightInverse_inv
  结论: RightInverse (fun a : G => a⁻¹) fun a => a⁻¹
  证明: inv_inv

Depends on / 依赖: inv_inv
-/
theorem rightInverse_inv : RightInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
/--
theorem `mul_one_div` / 定理 `mul_one_div`

English:
theorem mul_one_div
  given: (x y : G)
  statement: x * (1 / y) = x / y
  proof: by
  rw [div_eq_mul_inv]; rw [one_mul]; rw [div_eq_mul_inv]

@[to_additive]

中文:
定理 mul_one_div
  条件: (x y : G)
  结论: x * (1 / y) = x / y
  证明: by
  rw [div_eq_mul_inv]; rw [one_mul]; rw [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, one_mul
-/
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv]; rw [one_mul]; rw [div_eq_mul_inv]

@[to_additive]
/--
theorem `mul_div_assoc'` / 定理 `mul_div_assoc'`

English:
theorem mul_div_assoc'
  given: (a b c : G)
  statement: a * (b / c) = a * b / c
  proof: (mul_div_assoc _ _ _).symm

@[to_additive]

中文:
定理 mul_div_assoc'
  条件: (a b c : G)
  结论: a * (b / c) = a * b / c
  证明: (mul_div_assoc _ _ _).symm

@[to_additive]

Depends on / 依赖: mul_div_assoc
-/
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

@[to_additive]
/--
theorem `mul_div` / 定理 `mul_div`

English:
theorem mul_div
  given: (a b c : G)
  statement: a * (b / c) = a * b / c
  proof: by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]

中文:
定理 mul_div
  条件: (a b c : G)
  结论: a * (b / c) = a * b / c
  证明: by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_assoc
-/
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]
/--
theorem `div_eq_mul_one_div` / 定理 `div_eq_mul_one_div`

English:
theorem div_eq_mul_one_div
  given: (a b : G)
  statement: a / b = a * (1 / b)
  proof: by rw [div_eq_mul_inv, one_div]

中文:
定理 div_eq_mul_one_div
  条件: (a b : G)
  结论: a / b = a * (1 / b)
  证明: by rw [div_eq_mul_inv, one_div]

Depends on / 依赖: div_eq_mul_inv, one_div
-/
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[to_additive (attr := simp)]
/--
theorem `div_one` / 定理 `div_one`

English:
theorem div_one
  given: (a : G)
  statement: a / 1 = a
  proof: by simp [div_eq_mul_inv]

@[to_additive]

中文:
定理 div_one
  条件: (a : G)
  结论: a / 1 = a
  证明: by simp [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv
-/
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `one_div_one` / 定理 `one_div_one`

English:
theorem one_div_one
  statement: (1 : G) / 1 = 1
  proof: div_one _

中文:
定理 one_div_one
  结论: (1 : G) / 1 = 1
  证明: div_one _

Depends on / 依赖: div_one
-/
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c d : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
/--
theorem `eq_inv_of_mul_eq_one_right` / 定理 `eq_inv_of_mul_eq_one_right`

English:
theorem eq_inv_of_mul_eq_one_right
  given: (h : a * b = 1)
  statement: b = a⁻¹
  proof: (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]

中文:
定理 eq_inv_of_mul_eq_one_right
  条件: (h : a * b = 1)
  结论: b = a⁻¹
  证明: (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]

Depends on / 依赖: inv_eq_of_mul_eq_one_right
-/
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
/--
theorem `eq_one_div_of_mul_eq_one_left` / 定理 `eq_one_div_of_mul_eq_one_left`

English:
theorem eq_one_div_of_mul_eq_one_left
  given: (h : b * a = 1)
  statement: b = 1 / a
  proof: by
  rw [eq_inv_of_mul_eq_one_left h]; rw [one_div]

@[to_additive]

中文:
定理 eq_one_div_of_mul_eq_one_left
  条件: (h : b * a = 1)
  结论: b = 1 / a
  证明: by
  rw [eq_inv_of_mul_eq_one_left h]; rw [one_div]

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, one_div
-/
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h]; rw [one_div]

@[to_additive]
/--
theorem `eq_one_div_of_mul_eq_one_right` / 定理 `eq_one_div_of_mul_eq_one_right`

English:
theorem eq_one_div_of_mul_eq_one_right
  given: (h : a * b = 1)
  statement: b = 1 / a
  proof: by
  rw [eq_inv_of_mul_eq_one_right h]; rw [one_div]

@[to_additive]

中文:
定理 eq_one_div_of_mul_eq_one_right
  条件: (h : a * b = 1)
  结论: b = 1 / a
  证明: by
  rw [eq_inv_of_mul_eq_one_right h]; rw [one_div]

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_right, one_div
-/
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h]; rw [one_div]

@[to_additive]
/--
theorem `eq_of_div_eq_one` / 定理 `eq_of_div_eq_one`

English:
theorem eq_of_div_eq_one
  given: (h : a / b = 1)
  statement: a = b
  proof: inv_injective inv_eq_of_mul_eq_one_right by rwa [← div_eq_mul_inv]

@[to_additive]

中文:
定理 eq_of_div_eq_one
  条件: (h : a / b = 1)
  结论: a = b
  证明: inv_injective inv_eq_of_mul_eq_one_right by rwa [← div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_eq_of_mul_eq_one_right, inv_injective
-/
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
inv_injective inv_eq_of_mul_eq_one_right by rwa [← div_eq_mul_inv]

@[to_additive]
/--
lemma `eq_of_inv_mul_eq_one` / 引理 `eq_of_inv_mul_eq_one`

English:
lemma eq_of_inv_mul_eq_one
  given: (h : a⁻¹ * b = 1)
  statement: a = b
  proof: by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]

中文:
引理 eq_of_inv_mul_eq_one
  条件: (h : a⁻¹ * b = 1)
  结论: a = b
  证明: by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_left
-/
lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
/--
lemma `eq_of_mul_inv_eq_one` / 引理 `eq_of_mul_inv_eq_one`

English:
lemma eq_of_mul_inv_eq_one
  given: (h : a * b⁻¹ = 1)
  statement: a = b
  proof: by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]

中文:
引理 eq_of_mul_inv_eq_one
  条件: (h : a * b⁻¹ = 1)
  结论: a = b
  证明: by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_left
-/
lemma eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
/--
theorem `div_ne_one_of_ne` / 定理 `div_ne_one_of_ne`

English:
theorem div_ne_one_of_ne
  statement: a != b -> a / b != 1
  proof: mt eq_of_div_eq_one

中文:
定理 div_ne_one_of_ne
  结论: a != b -> a / b != 1
  证明: mt eq_of_div_eq_one

Depends on / 依赖: eq_of_div_eq_one
-/
theorem div_ne_one_of_ne : a != b -> a / b != 1 :=
  mt eq_of_div_eq_one

variable (a b c)

@[to_additive]
/--
theorem `one_div_mul_one_div_rev` / 定理 `one_div_mul_one_div_rev`

English:
theorem one_div_mul_one_div_rev
  statement: 1 / a * (1 / b) = 1 / (b * a)
  proof: by simp

@[to_additive]

中文:
定理 one_div_mul_one_div_rev
  结论: 1 / a * (1 / b) = 1 / (b * a)
  证明: by simp

@[to_additive]
-/
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

@[to_additive]
/--
theorem `inv_div_left` / 定理 `inv_div_left`

English:
theorem inv_div_left
  statement: a⁻¹ / b = (b * a)⁻¹
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 inv_div_left
  结论: a⁻¹ / b = (b * a)⁻¹
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

@[to_additive (attr := simp)]
/--
theorem `inv_div` / 定理 `inv_div`

English:
theorem inv_div
  statement: (a / b)⁻¹ = b / a
  proof: by simp

@[to_additive]

中文:
定理 inv_div
  结论: (a / b)⁻¹ = b / a
  证明: by simp

@[to_additive]
-/
theorem inv_div : (a / b)⁻¹ = b / a := by simp

@[to_additive]
/--
theorem `one_div_div` / 定理 `one_div_div`

English:
theorem one_div_div
  statement: 1 / (a / b) = b / a
  proof: by simp

@[to_additive]

中文:
定理 one_div_div
  结论: 1 / (a / b) = b / a
  证明: by simp

@[to_additive]
-/
theorem one_div_div : 1 / (a / b) = b / a := by simp

@[to_additive]
/--
theorem `one_div_one_div` / 定理 `one_div_one_div`

English:
theorem one_div_one_div
  statement: 1 / (1 / a) = a
  proof: by simp

@[to_additive]

中文:
定理 one_div_one_div
  结论: 1 / (1 / a) = a
  证明: by simp

@[to_additive]
-/
theorem one_div_one_div : 1 / (1 / a) = a := by simp

@[to_additive]
/--
theorem `div_eq_div_iff_comm` / 定理 `div_eq_div_iff_comm`

English:
theorem div_eq_div_iff_comm
  statement: a / b = c / d ↔ b / a = d / c
  proof: inv_inj.symm.trans by simp only [inv_div]

@[to_additive]

中文:
定理 div_eq_div_iff_comm
  结论: a / b = c / d ↔ b / a = d / c
  证明: inv_inj.symm.trans by simp only [inv_div]

@[to_additive]

Depends on / 依赖: inv_div, inv_inj, inv_inj.symm.trans
-/
theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c :=
inv_inj.symm.trans by simp only [inv_div]

@[to_additive]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

@[to_additive (attr := simp)]
/--
lemma `inv_pow` / 引理 `inv_pow`

English:
lemma inv_pow
  given: (a : α)
  statement: forall n : Nat, a⁻¹ ^ n = (a ^ n)⁻¹

中文:
引理 inv_pow
  条件: (a : α)
  结论: 对任意 n : 自然数, a⁻¹ ^ n = (a ^ n)⁻¹
-/
lemma inv_pow (a : α) : forall n : Nat, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
/--
lemma `one_zpow` / 引理 `one_zpow`

English:
lemma one_zpow
  statement: forall n : Int, (1 : α) ^ n = 1

中文:
引理 one_zpow
  结论: 对任意 n : 整数, (1 : α) ^ n = 1
-/
lemma one_zpow : forall n : Int, (1 : α) ^ n = 1
  | (n : Nat) => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]

@[to_additive (attr := simp) neg_zsmul]
/--
lemma `zpow_neg` / 引理 `zpow_neg`

English:
lemma zpow_neg
  given: (a : α)
  statement: forall n : Int, a ^ (-n) = (a ^ n)⁻¹

中文:
引理 zpow_neg
  条件: (a : α)
  结论: 对任意 n : 整数, a ^ (-n) = (a ^ n)⁻¹
-/
lemma zpow_neg (a : α) : forall n : Int, a ^ (-n) = (a ^ n)⁻¹
  | (_ + 1 : Nat) => DivInvMonoid.zpow_neg' _ _
  | 0 => by simp
  | Int.negSucc n => by
    rw [zpow_negSucc]; rw [inv_inv]; rw [← zpow_natCast]
    rfl

@[to_additive neg_one_zsmul_add]
/--
lemma `mul_zpow_neg_one` / 引理 `mul_zpow_neg_one`

English:
lemma mul_zpow_neg_one
  given: (a b : α)
  statement: (a * b) ^ (-1 : Int) = b ^ (-1 : Int) * a ^ (-1 : Int)
  proof: by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[to_additive zsmul_neg]

中文:
引理 mul_zpow_neg_one
  条件: (a b : α)
  结论: (a * b) ^ (-1 : 整数) = b ^ (-1 : 整数) * a ^ (-1 : 整数)
  证明: by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[to_additive zsmul_neg]

Depends on / 依赖: mul_inv_rev, zpow_neg, zpow_one
-/
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : Int) = b ^ (-1 : Int) * a ^ (-1 : Int) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[to_additive zsmul_neg]
/--
lemma `inv_zpow` / 引理 `inv_zpow`

English:
lemma inv_zpow
  given: (a : α)
  statement: forall n : Int, a⁻¹ ^ n = (a ^ n)⁻¹

中文:
引理 inv_zpow
  条件: (a : α)
  结论: 对任意 n : 整数, a⁻¹ ^ n = (a ^ n)⁻¹
-/
lemma inv_zpow (a : α) : forall n : Int, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : Nat) => by rw [zpow_natCast, zpow_natCast, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]

@[to_additive (attr := simp) zsmul_neg']
/--
lemma `inv_zpow'` / 引理 `inv_zpow'`

English:
lemma inv_zpow'
  given: (a : α) (n : Int)
  statement: a⁻¹ ^ n = a ^ (-n)
  proof: by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]

中文:
引理 inv_zpow'
  条件: (a : α) (n : 整数)
  结论: a⁻¹ ^ n = a ^ (-n)
  证明: by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]

Depends on / 依赖: inv_zpow, zpow_neg
-/
lemma inv_zpow' (a : α) (n : Int) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]
/--
lemma `one_div_pow` / 引理 `one_div_pow`

English:
lemma one_div_pow
  given: (a : α) (n : Nat)
  statement: (1 / a) ^ n = 1 / a ^ n
  proof: by simp only [one_div, inv_pow]

@[to_additive zsmul_zero_sub]

中文:
引理 one_div_pow
  条件: (a : α) (n : 自然数)
  结论: (1 / a) ^ n = 1 / a ^ n
  证明: by simp only [one_div, inv_pow]

@[to_additive zsmul_zero_sub]

Depends on / 依赖: inv_pow, one_div
-/
lemma one_div_pow (a : α) (n : Nat) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]

@[to_additive zsmul_zero_sub]
/--
lemma `one_div_zpow` / 引理 `one_div_zpow`

English:
lemma one_div_zpow
  given: (a : α) (n : Int)
  statement: (1 / a) ^ n = 1 / a ^ n
  proof: by simp only [one_div, inv_zpow]

中文:
引理 one_div_zpow
  条件: (a : α) (n : 整数)
  结论: (1 / a) ^ n = 1 / a ^ n
  证明: by simp only [one_div, inv_zpow]

Depends on / 依赖: inv_zpow, one_div
-/
lemma one_div_zpow (a : α) (n : Int) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]

variable {a b c}

@[to_additive (attr := simp)]
/--
theorem `inv_eq_one` / 定理 `inv_eq_one`

English:
theorem inv_eq_one
  statement: a⁻¹ = 1 ↔ a = 1
  proof: inv_injective.eq_iff' inv_one

@[to_additive (attr := simp)]

中文:
定理 inv_eq_one
  结论: a⁻¹ = 1 ↔ a = 1
  证明: inv_injective.eq_iff' inv_one

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, inv_injective, inv_injective.eq_iff, inv_one
-/
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

@[to_additive (attr := simp)]
/--
theorem `one_eq_inv` / 定理 `one_eq_inv`

English:
theorem one_eq_inv
  statement: 1 = a⁻¹ ↔ a = 1
  proof: eq_comm.trans inv_eq_one

@[to_additive]

中文:
定理 one_eq_inv
  结论: 1 = a⁻¹ ↔ a = 1
  证明: eq_comm.trans inv_eq_one

@[to_additive]

Depends on / 依赖: eq_comm, eq_comm.trans, inv_eq_one
-/
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

@[to_additive]
/--
theorem `inv_ne_one` / 定理 `inv_ne_one`

English:
theorem inv_ne_one
  statement: a⁻¹ != 1 ↔ a != 1
  proof: inv_eq_one.not

@[to_additive]

中文:
定理 inv_ne_one
  结论: a⁻¹ != 1 ↔ a != 1
  证明: inv_eq_one.not

@[to_additive]

Depends on / 依赖: inv_eq_one, inv_eq_one.not
-/
theorem inv_ne_one : a⁻¹ != 1 ↔ a != 1 :=
  inv_eq_one.not

@[to_additive]
/--
theorem `eq_of_one_div_eq_one_div` / 定理 `eq_of_one_div_eq_one_div`

English:
theorem eq_of_one_div_eq_one_div
  given: (h : 1 / a = 1 / b)
  statement: a = b
  proof: by
  rw [← one_div_one_div a]; rw [h]; rw [one_div_one_div]

中文:
定理 eq_of_one_div_eq_one_div
  条件: (h : 1 / a = 1 / b)
  结论: a = b
  证明: by
  rw [← one_div_one_div a]; rw [h]; rw [one_div_one_div]

Depends on / 依赖: one_div_one_div
-/
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a]; rw [h]; rw [one_div_one_div]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
/--
lemma `zpow_mul` / 引理 `zpow_mul`

English:
lemma zpow_mul
  given: (a : α)
  statement: forall m n : Int, a ^ (m * n) = (a ^ m) ^ n

中文:
引理 zpow_mul
  条件: (a : α)
  结论: 对任意 m n : 整数, a ^ (m * n) = (a ^ m) ^ n
-/
@[to_additive mul_zsmul'] lemma zpow_mul (a : α) : forall m n : Int, a ^ (m * n) = (a ^ m) ^ n
  | (m : Nat), (n : Nat) => by
    rw [zpow_natCast]; rw [zpow_natCast]; rw [← pow_mul]; rw [← zpow_natCast]
    rfl
  | (m : Nat), .negSucc n => by
    rw [zpow_natCast]; rw [zpow_negSucc]; rw [← pow_mul]; rw [Int.ofNat_mul_negSucc]; rw [zpow_neg]; rw [inv_inj]; rw [← zpow_natCast]
  | .negSucc m, (n : Nat) => by
    rw [zpow_natCast]; rw [zpow_negSucc]; rw [← inv_pow]; rw [← pow_mul]; rw [Int.negSucc_mul_ofNat]; rw [zpow_neg]; rw [inv_pow]; rw [inv_inj]; rw [← zpow_natCast]
  | .negSucc m, .negSucc n => by
    rw [zpow_negSucc]; rw [zpow_negSucc]; rw [Int.negSucc_mul_negSucc]; rw [inv_pow]; rw [inv_inv]; rw [← pow_mul]; rw [←
      zpow_natCast]
    rfl

@[to_additive mul_zsmul]
/--
lemma `zpow_mul'` / 引理 `zpow_mul'`

English:
lemma zpow_mul'
  given: (a : α) (m n : Int)
  statement: a ^ (m * n) = (a ^ n) ^ m
  proof: by rw [Int.mul_comm, zpow_mul]

@[to_additive]

中文:
引理 zpow_mul'
  条件: (a : α) (m n : 整数)
  结论: a ^ (m * n) = (a ^ n) ^ m
  证明: by rw [Int.mul_comm, zpow_mul]

@[to_additive]

Depends on / 依赖: Int.mul_comm, mul_comm, zpow_mul
-/
lemma zpow_mul' (a : α) (m n : Int) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]

@[to_additive]
/--
theorem `zpow_comm` / 定理 `zpow_comm`

English:
theorem zpow_comm
  given: (a : α) (m n : Int)
  statement: (a ^ m) ^ n = (a ^ n) ^ m
  proof: by rw [← zpow_mul, zpow_mul']

中文:
定理 zpow_comm
  条件: (a : α) (m n : 整数)
  结论: (a ^ m) ^ n = (a ^ n) ^ m
  证明: by rw [← zpow_mul, zpow_mul']

Depends on / 依赖: zpow_mul
-/
theorem zpow_comm (a : α) (m n : Int) : (a ^ m) ^ n = (a ^ n) ^ m := by rw [← zpow_mul, zpow_mul']

variable (a b c)

@[to_additive]
/--
theorem `div_div_eq_mul_div` / 定理 `div_div_eq_mul_div`

English:
theorem div_div_eq_mul_div
  statement: a / (b / c) = a * c / b
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 div_div_eq_mul_div
  结论: a / (b / c) = a * c / b
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

@[to_additive (attr := simp)]
/--
theorem `div_inv_eq_mul` / 定理 `div_inv_eq_mul`

English:
theorem div_inv_eq_mul
  statement: a / b⁻¹ = a * b
  proof: by simp

@[to_additive]

中文:
定理 div_inv_eq_mul
  结论: a / b⁻¹ = a * b
  证明: by simp

@[to_additive]
-/
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

@[to_additive]
/--
theorem `div_mul_eq_div_div_swap` / 定理 `div_mul_eq_div_div_swap`

English:
theorem div_mul_eq_div_div_swap
  statement: a / (b * c) = a / c / b
  proof: by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

中文:
定理 div_mul_eq_div_div_swap
  结论: a / (b * c) = a / c / b
  证明: by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, mul_assoc, mul_inv_rev
-/
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  statement: (a * b)⁻¹ = a⁻¹ * b⁻¹
  proof: by simp

@[to_additive]

中文:
定理 mul_inv
  结论: (a * b)⁻¹ = a⁻¹ * b⁻¹
  证明: by simp

@[to_additive]
-/
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

@[to_additive]
/--
theorem `inv_div'` / 定理 `inv_div'`

English:
theorem inv_div'
  statement: (a / b)⁻¹ = a⁻¹ / b⁻¹
  proof: by simp

@[to_additive]

中文:
定理 inv_div'
  结论: (a / b)⁻¹ = a⁻¹ / b⁻¹
  证明: by simp

@[to_additive]
-/
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

@[to_additive]
/--
theorem `div_eq_inv_mul` / 定理 `div_eq_inv_mul`

English:
theorem div_eq_inv_mul
  statement: a / b = b⁻¹ * a
  proof: by simp

@[to_additive]

中文:
定理 div_eq_inv_mul
  结论: a / b = b⁻¹ * a
  证明: by simp

@[to_additive]
-/
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

@[to_additive]
/--
theorem `inv_mul_eq_div` / 定理 `inv_mul_eq_div`

English:
theorem inv_mul_eq_div
  statement: a⁻¹ * b = b / a
  proof: by simp

中文:
定理 inv_mul_eq_div
  结论: a⁻¹ * b = b / a
  证明: by simp
-/
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp

/--
lemma `inv_div_comm` / 引理 `inv_div_comm`

English:
lemma inv_div_comm
  given: (a b : α)
  statement: a⁻¹ / b = b⁻¹ / a
  proof: by simp

@[to_additive]

中文:
引理 inv_div_comm
  条件: (a b : α)
  结论: a⁻¹ / b = b⁻¹ / a
  证明: by simp

@[to_additive]
-/
@[to_additive] lemma inv_div_comm (a b : α) : a⁻¹ / b = b⁻¹ / a := by simp

@[to_additive]
/--
theorem `inv_mul'` / 定理 `inv_mul'`

English:
theorem inv_mul'
  statement: (a * b)⁻¹ = a⁻¹ / b
  proof: by simp

@[to_additive]

中文:
定理 inv_mul'
  结论: (a * b)⁻¹ = a⁻¹ / b
  证明: by simp

@[to_additive]
-/
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

@[to_additive]
/--
theorem `inv_div_inv` / 定理 `inv_div_inv`

English:
theorem inv_div_inv
  statement: a⁻¹ / b⁻¹ = b / a
  proof: by simp

@[to_additive]

中文:
定理 inv_div_inv
  结论: a⁻¹ / b⁻¹ = b / a
  证明: by simp

@[to_additive]
-/
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

@[to_additive]
/--
theorem `inv_inv_div_inv` / 定理 `inv_inv_div_inv`

English:
theorem inv_inv_div_inv
  statement: (a⁻¹ / b⁻¹)⁻¹ = a / b
  proof: by simp

@[to_additive]

中文:
定理 inv_inv_div_inv
  结论: (a⁻¹ / b⁻¹)⁻¹ = a / b
  证明: by simp

@[to_additive]
-/
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

@[to_additive]
/--
theorem `one_div_mul_one_div` / 定理 `one_div_mul_one_div`

English:
theorem one_div_mul_one_div
  statement: 1 / a * (1 / b) = 1 / (a * b)
  proof: by simp

@[to_additive]

中文:
定理 one_div_mul_one_div
  结论: 1 / a * (1 / b) = 1 / (a * b)
  证明: by simp

@[to_additive]
-/
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

@[to_additive]
/--
theorem `div_right_comm` / 定理 `div_right_comm`

English:
theorem div_right_comm
  statement: a / b / c = a / c / b
  proof: by simp

@[to_additive]

中文:
定理 div_right_comm
  结论: a / b / c = a / c / b
  证明: by simp

@[to_additive]
-/
theorem div_right_comm : a / b / c = a / c / b := by simp

@[to_additive]
/--
theorem `div_div` / 定理 `div_div`

English:
theorem div_div
  statement: a / b / c = a / (b * c)
  proof: by simp

@[to_additive]

中文:
定理 div_div
  结论: a / b / c = a / (b * c)
  证明: by simp

@[to_additive]
-/
theorem div_div : a / b / c = a / (b * c) := by simp

@[to_additive]
/--
theorem `div_mul` / 定理 `div_mul`

English:
theorem div_mul
  statement: a / b * c = a / (b / c)
  proof: by simp

@[to_additive]

中文:
定理 div_mul
  结论: a / b * c = a / (b / c)
  证明: by simp

@[to_additive]
-/
theorem div_mul : a / b * c = a / (b / c) := by simp

@[to_additive]
/--
theorem `mul_div_left_comm` / 定理 `mul_div_left_comm`

English:
theorem mul_div_left_comm
  statement: a * (b / c) = b * (a / c)
  proof: by simp

@[to_additive]

中文:
定理 mul_div_left_comm
  结论: a * (b / c) = b * (a / c)
  证明: by simp

@[to_additive]
-/
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

@[to_additive]
/--
theorem `mul_div_right_comm` / 定理 `mul_div_right_comm`

English:
theorem mul_div_right_comm
  statement: a * b / c = a / c * b
  proof: by simp

@[to_additive]

中文:
定理 mul_div_right_comm
  结论: a * b / c = a / c * b
  证明: by simp

@[to_additive]
-/
theorem mul_div_right_comm : a * b / c = a / c * b := by simp

@[to_additive]
/--
theorem `div_mul_eq_div_div` / 定理 `div_mul_eq_div_div`

English:
theorem div_mul_eq_div_div
  statement: a / (b * c) = a / b / c
  proof: by simp

@[to_additive]

中文:
定理 div_mul_eq_div_div
  结论: a / (b * c) = a / b / c
  证明: by simp

@[to_additive]
-/
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

@[to_additive]
/--
theorem `div_mul_eq_mul_div` / 定理 `div_mul_eq_mul_div`

English:
theorem div_mul_eq_mul_div
  statement: a / b * c = a * c / b
  proof: by simp

@[to_additive]

中文:
定理 div_mul_eq_mul_div
  结论: a / b * c = a * c / b
  证明: by simp

@[to_additive]
-/
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

@[to_additive]
/--
theorem `one_div_mul_eq_div` / 定理 `one_div_mul_eq_div`

English:
theorem one_div_mul_eq_div
  statement: 1 / a * b = b / a
  proof: by simp

@[to_additive]

中文:
定理 one_div_mul_eq_div
  结论: 1 / a * b = b / a
  证明: by simp

@[to_additive]
-/
theorem one_div_mul_eq_div : 1 / a * b = b / a := by simp

@[to_additive]
/--
theorem `mul_comm_div` / 定理 `mul_comm_div`

English:
theorem mul_comm_div
  statement: a / b * c = a * (c / b)
  proof: by simp

@[to_additive]

中文:
定理 mul_comm_div
  结论: a / b * c = a * (c / b)
  证明: by simp

@[to_additive]
-/
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

@[to_additive]
/--
theorem `div_mul_comm` / 定理 `div_mul_comm`

English:
theorem div_mul_comm
  statement: a / b * c = c / b * a
  proof: by simp

@[to_additive]

中文:
定理 div_mul_comm
  结论: a / b * c = c / b * a
  证明: by simp

@[to_additive]
-/
theorem div_mul_comm : a / b * c = c / b * a := by simp

@[to_additive]
/--
theorem `div_mul_eq_div_mul_one_div` / 定理 `div_mul_eq_div_mul_one_div`

English:
theorem div_mul_eq_div_mul_one_div
  statement: a / (b * c) = a / b * (1 / c)
  proof: by simp

@[to_additive]

中文:
定理 div_mul_eq_div_mul_one_div
  结论: a / (b * c) = a / b * (1 / c)
  证明: by simp

@[to_additive]
-/
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

@[to_additive]
/--
theorem `div_div_div_eq` / 定理 `div_div_div_eq`

English:
theorem div_div_div_eq
  statement: a / b / (c / d) = a * d / (b * c)
  proof: by simp

@[to_additive]

中文:
定理 div_div_div_eq
  结论: a / b / (c / d) = a * d / (b * c)
  证明: by simp

@[to_additive]
-/
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

@[to_additive]
/--
theorem `div_div_div_comm` / 定理 `div_div_div_comm`

English:
theorem div_div_div_comm
  statement: a / b / (c / d) = a / c / (b / d)
  proof: by simp

@[to_additive]

中文:
定理 div_div_div_comm
  结论: a / b / (c / d) = a / c / (b / d)
  证明: by simp

@[to_additive]
-/
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp

@[to_additive]
/--
theorem `div_mul_div_comm` / 定理 `div_mul_div_comm`

English:
theorem div_mul_div_comm
  statement: a / b * (c / d) = a * c / (b * d)
  proof: by simp

@[to_additive]

中文:
定理 div_mul_div_comm
  结论: a / b * (c / d) = a * c / (b * d)
  证明: by simp

@[to_additive]
-/
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp

@[to_additive]
/--
theorem `mul_div_mul_comm` / 定理 `mul_div_mul_comm`

English:
theorem mul_div_mul_comm
  statement: a * b / (c * d) = a / c * (b / d)
  proof: by simp

中文:
定理 mul_div_mul_comm
  结论: a * b / (c * d) = a / c * (b / d)
  证明: by simp
-/
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp

/--
lemma `mul_zpow` / 引理 `mul_zpow`

English:
lemma mul_zpow
  statement: forall n : Int, (a * b) ^ n = a ^ n * b ^ n

中文:
引理 mul_zpow
  结论: 对任意 n : 整数, (a * b) ^ n = a ^ n * b ^ n
-/
@[to_additive zsmul_add] lemma mul_zpow : forall n : Int, (a * b) ^ n = a ^ n * b ^ n
  | (n : Nat) => by simp_rw [zpow_natCast, mul_pow]
  | .negSucc n => by simp_rw [zpow_negSucc, ← inv_pow, mul_inv, mul_pow]

@[to_additive nsmul_sub]
/--
lemma `div_pow` / 引理 `div_pow`

English:
lemma div_pow
  given: (a b : α) (n : Nat)
  statement: (a / b) ^ n = a ^ n / b ^ n
  proof: by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[to_additive zsmul_sub]

中文:
引理 div_pow
  条件: (a b : α) (n : 自然数)
  结论: (a / b) ^ n = a ^ n / b ^ n
  证明: by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[to_additive zsmul_sub]

Depends on / 依赖: div_eq_mul_inv, inv_pow, mul_pow
-/
lemma div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[to_additive zsmul_sub]
/--
lemma `div_zpow` / 引理 `div_zpow`

English:
lemma div_zpow
  given: (a b : α) (n : Int)
  statement: (a / b) ^ n = a ^ n / b ^ n
  proof: by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

中文:
引理 div_zpow
  条件: (a b : α) (n : 整数)
  结论: (a / b) ^ n = a ^ n / b ^ n
  证明: by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

Depends on / 依赖: div_eq_mul_inv, inv_zpow, mul_zpow
-/
lemma div_zpow (a b : α) (n : Int) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G} {n : Int}

@[to_additive (attr := simp)]
/--
theorem `div_eq_inv_self` / 定理 `div_eq_inv_self`

English:
theorem div_eq_inv_self
  statement: a / b = b⁻¹ ↔ a = 1
  proof: by rw [div_eq_mul_inv, mul_eq_right]

@[to_additive]

中文:
定理 div_eq_inv_self
  结论: a / b = b⁻¹ ↔ a = 1
  证明: by rw [div_eq_mul_inv, mul_eq_right]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_eq_right
-/
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_eq_right]

@[to_additive]
/--
theorem `mul_left_surjective` / 定理 `mul_left_surjective`

English:
theorem mul_left_surjective
  given: (a : G)
  statement: Surjective (a * ·)
  proof: fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]

中文:
定理 mul_left_surjective
  条件: (a : G)
  结论: Surjective (a * ·)
  证明: fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left
-/
theorem mul_left_surjective (a : G) : Surjective (a * ·) :=
  fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
/--
theorem `mul_right_surjective` / 定理 `mul_right_surjective`

English:
theorem mul_right_surjective
  given: (a : G)
  statement: Function.Surjective fun x => x * a
  proof: fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]

中文:
定理 mul_right_surjective
  条件: (a : G)
  结论: Function.Surjective fun x => x * a
  证明: fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]
-/
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]
/--
theorem `eq_mul_inv_of_mul_eq` / 定理 `eq_mul_inv_of_mul_eq`

English:
theorem eq_mul_inv_of_mul_eq
  given: (h : a * c = b)
  statement: a = b * c⁻¹
  proof: by simp [h.symm]

@[to_additive]

中文:
定理 eq_mul_inv_of_mul_eq
  条件: (h : a * c = b)
  结论: a = b * c⁻¹
  证明: by simp [h.symm]

@[to_additive]

Depends on / 依赖: h.symm
-/
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]

@[to_additive]
/--
theorem `eq_inv_mul_of_mul_eq` / 定理 `eq_inv_mul_of_mul_eq`

English:
theorem eq_inv_mul_of_mul_eq
  given: (h : b * a = c)
  statement: a = b⁻¹ * c
  proof: by simp [h.symm]

@[to_additive]

中文:
定理 eq_inv_mul_of_mul_eq
  条件: (h : b * a = c)
  结论: a = b⁻¹ * c
  证明: by simp [h.symm]

@[to_additive]

Depends on / 依赖: h.symm
-/
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]

@[to_additive]
/--
theorem `inv_mul_eq_of_eq_mul` / 定理 `inv_mul_eq_of_eq_mul`

English:
theorem inv_mul_eq_of_eq_mul
  given: (h : b = a * c)
  statement: a⁻¹ * b = c
  proof: by simp [h]

@[to_additive]

中文:
定理 inv_mul_eq_of_eq_mul
  条件: (h : b = a * c)
  结论: a⁻¹ * b = c
  证明: by simp [h]

@[to_additive]
-/
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]

@[to_additive]
/--
theorem `mul_inv_eq_of_eq_mul` / 定理 `mul_inv_eq_of_eq_mul`

English:
theorem mul_inv_eq_of_eq_mul
  given: (h : a = c * b)
  statement: a * b⁻¹ = c
  proof: by simp [h]

@[to_additive]

中文:
定理 mul_inv_eq_of_eq_mul
  条件: (h : a = c * b)
  结论: a * b⁻¹ = c
  证明: by simp [h]

@[to_additive]
-/
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

@[to_additive]
/--
theorem `eq_mul_of_mul_inv_eq` / 定理 `eq_mul_of_mul_inv_eq`

English:
theorem eq_mul_of_mul_inv_eq
  given: (h : a * c⁻¹ = b)
  statement: a = b * c
  proof: by simp [h.symm]

@[to_additive]

中文:
定理 eq_mul_of_mul_inv_eq
  条件: (h : a * c⁻¹ = b)
  结论: a = b * c
  证明: by simp [h.symm]

@[to_additive]

Depends on / 依赖: h.symm
-/
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]

@[to_additive]
/--
theorem `eq_mul_of_inv_mul_eq` / 定理 `eq_mul_of_inv_mul_eq`

English:
theorem eq_mul_of_inv_mul_eq
  given: (h : b⁻¹ * a = c)
  statement: a = b * c
  proof: by simp [h.symm, mul_inv_cancel_left]

@[to_additive]

中文:
定理 eq_mul_of_inv_mul_eq
  条件: (h : b⁻¹ * a = c)
  结论: a = b * c
  证明: by simp [h.symm, mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: h.symm, mul_inv_cancel_left
-/
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

@[to_additive]
/--
theorem `mul_eq_of_eq_inv_mul` / 定理 `mul_eq_of_eq_inv_mul`

English:
theorem mul_eq_of_eq_inv_mul
  given: (h : b = a⁻¹ * c)
  statement: a * b = c
  proof: by rw [h, mul_inv_cancel_left]

@[to_additive]

中文:
定理 mul_eq_of_eq_inv_mul
  条件: (h : b = a⁻¹ * c)
  结论: a * b = c
  证明: by rw [h, mul_inv_cancel_left]

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left
-/
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

@[to_additive]
/--
theorem `mul_eq_of_eq_mul_inv` / 定理 `mul_eq_of_eq_mul_inv`

English:
theorem mul_eq_of_eq_mul_inv
  given: (h : a = c * b⁻¹)
  statement: a * b = c
  proof: by simp [h]

@[to_additive]

中文:
定理 mul_eq_of_eq_mul_inv
  条件: (h : a = c * b⁻¹)
  结论: a * b = c
  证明: by simp [h]

@[to_additive]
-/
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]

@[to_additive]
/--
theorem `mul_eq_one_iff_eq_inv` / 定理 `mul_eq_one_iff_eq_inv`

English:
theorem mul_eq_one_iff_eq_inv
  statement: a * b = 1 ↔ a = b⁻¹
  proof: ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, inv_mul_cancel]⟩

@[to_additive]

中文:
定理 mul_eq_one_iff_eq_inv
  结论: a * b = 1 ↔ a = b⁻¹
  证明: ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, inv_mul_cancel]⟩

@[to_additive]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, inv_mul_cancel
-/
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, inv_mul_cancel]⟩

@[to_additive]
/--
theorem `mul_eq_one_iff_inv_eq` / 定理 `mul_eq_one_iff_inv_eq`

English:
theorem mul_eq_one_iff_inv_eq
  statement: a * b = 1 ↔ a⁻¹ = b
  proof: by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_iff_eq_inv]

中文:
定理 mul_eq_one_iff_inv_eq
  结论: a * b = 1 ↔ a⁻¹ = b
  证明: by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_iff_eq_inv]

Depends on / 依赖: inv_eq_iff_eq_inv, mul_eq_one_iff_eq_inv
-/
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv]; rw [inv_eq_iff_eq_inv]

/-- Variant of `mul_eq_one_iff_eq_inv` with swapped equality. -/
@[to_additive]
/--
theorem `mul_eq_one_iff_eq_inv'` / 定理 `mul_eq_one_iff_eq_inv'`

English:
theorem mul_eq_one_iff_eq_inv'
  statement: a * b = 1 ↔ b = a⁻¹
  proof: by
  rw [mul_eq_one_iff_inv_eq]; rw [eq_comm]

中文:
定理 mul_eq_one_iff_eq_inv'
  结论: a * b = 1 ↔ b = a⁻¹
  证明: by
  rw [mul_eq_one_iff_inv_eq]; rw [eq_comm]

Depends on / 依赖: eq_comm, mul_eq_one_iff_inv_eq
-/
theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq]; rw [eq_comm]

/-- Variant of `mul_eq_one_iff_inv_eq` with swapped equality. -/
@[to_additive]
/--
theorem `mul_eq_one_iff_inv_eq'` / 定理 `mul_eq_one_iff_inv_eq'`

English:
theorem mul_eq_one_iff_inv_eq'
  statement: a * b = 1 ↔ b⁻¹ = a
  proof: by
  rw [mul_eq_one_iff_eq_inv]; rw [eq_comm]

@[to_additive]

中文:
定理 mul_eq_one_iff_inv_eq'
  结论: a * b = 1 ↔ b⁻¹ = a
  证明: by
  rw [mul_eq_one_iff_eq_inv]; rw [eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, mul_eq_one_iff_eq_inv
-/
theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv]; rw [eq_comm]

@[to_additive]
/--
theorem `eq_inv_iff_mul_eq_one` / 定理 `eq_inv_iff_mul_eq_one`

English:
theorem eq_inv_iff_mul_eq_one
  statement: a = b⁻¹ ↔ a * b = 1
  proof: mul_eq_one_iff_eq_inv.symm

@[to_additive]

中文:
定理 eq_inv_iff_mul_eq_one
  结论: a = b⁻¹ ↔ a * b = 1
  证明: mul_eq_one_iff_eq_inv.symm

@[to_additive]

Depends on / 依赖: mul_eq_one_iff_eq_inv, mul_eq_one_iff_eq_inv.symm
-/
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

@[to_additive]
/--
theorem `inv_eq_iff_mul_eq_one` / 定理 `inv_eq_iff_mul_eq_one`

English:
theorem inv_eq_iff_mul_eq_one
  statement: a⁻¹ = b ↔ a * b = 1
  proof: mul_eq_one_iff_inv_eq.symm

@[to_additive]

中文:
定理 inv_eq_iff_mul_eq_one
  结论: a⁻¹ = b ↔ a * b = 1
  证明: mul_eq_one_iff_inv_eq.symm

@[to_additive]

Depends on / 依赖: mul_eq_one_iff_inv_eq, mul_eq_one_iff_inv_eq.symm
-/
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

@[to_additive]
/--
theorem `eq_mul_inv_iff_mul_eq` / 定理 `eq_mul_inv_iff_mul_eq`

English:
theorem eq_mul_inv_iff_mul_eq
  statement: a = b * c⁻¹ ↔ a * c = b
  proof: ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]

中文:
定理 eq_mul_inv_iff_mul_eq
  结论: a = b * c⁻¹ ↔ a * c = b
  证明: ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_inv_cancel_right
-/
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
/--
theorem `eq_inv_mul_iff_mul_eq` / 定理 `eq_inv_mul_iff_mul_eq`

English:
theorem eq_inv_mul_iff_mul_eq
  statement: a = b⁻¹ * c ↔ b * a = c
  proof: ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]

中文:
定理 eq_inv_mul_iff_mul_eq
  结论: a = b⁻¹ * c ↔ b * a = c
  证明: ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left, mul_inv_cancel_left
-/
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
/--
theorem `inv_mul_eq_iff_eq_mul` / 定理 `inv_mul_eq_iff_eq_mul`

English:
theorem inv_mul_eq_iff_eq_mul
  statement: a⁻¹ * b = c ↔ b = a * c
  proof: ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]

中文:
定理 inv_mul_eq_iff_eq_mul
  结论: a⁻¹ * b = c ↔ b = a * c
  证明: ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left, mul_inv_cancel_left
-/
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
/--
theorem `mul_inv_eq_iff_eq_mul` / 定理 `mul_inv_eq_iff_eq_mul`

English:
theorem mul_inv_eq_iff_eq_mul
  statement: a * b⁻¹ = c ↔ a = c * b
  proof: ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]

中文:
定理 mul_inv_eq_iff_eq_mul
  结论: a * b⁻¹ = c ↔ a = c * b
  证明: ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_inv_cancel_right
-/
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
/--
theorem `mul_inv_eq_one` / 定理 `mul_inv_eq_one`

English:
theorem mul_inv_eq_one
  statement: a * b⁻¹ = 1 ↔ a = b
  proof: by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]

中文:
定理 mul_inv_eq_one
  结论: a * b⁻¹ = 1 ↔ a = b
  证明: by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]

Depends on / 依赖: inv_inv, mul_eq_one_iff_eq_inv
-/
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
/--
theorem `inv_mul_eq_one` / 定理 `inv_mul_eq_one`

English:
theorem inv_mul_eq_one
  statement: a⁻¹ * b = 1 ↔ a = b
  proof: by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive (attr := simp)]

中文:
定理 inv_mul_eq_one
  结论: a⁻¹ * b = 1 ↔ a = b
  证明: by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inj, mul_eq_one_iff_eq_inv
-/
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive (attr := simp)]
/--
theorem `conj_eq_one_iff` / 定理 `conj_eq_one_iff`

English:
theorem conj_eq_one_iff
  statement: a * b * a⁻¹ = 1 ↔ b = 1
  proof: by
  rw [mul_inv_eq_one]; rw [mul_eq_left]

@[to_additive]

中文:
定理 conj_eq_one_iff
  结论: a * b * a⁻¹ = 1 ↔ b = 1
  证明: by
  rw [mul_inv_eq_one]; rw [mul_eq_left]

@[to_additive]

Depends on / 依赖: mul_eq_left, mul_inv_eq_one
-/
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one]; rw [mul_eq_left]

@[to_additive]
/--
theorem `div_left_injective` / 定理 `div_left_injective`

English:
theorem div_left_injective
  statement: Function.Injective fun a => a / b
  proof: by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h => mul_left_injective b⁻¹ h

@[to_additive]

中文:
定理 div_left_injective
  结论: Function.Injective fun a => a / b
  证明: by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h => mul_left_injective b⁻¹ h

@[to_additive]
-/
theorem div_left_injective : Function.Injective fun a => a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h => mul_left_injective b⁻¹ h

@[to_additive]
/--
theorem `div_right_injective` / 定理 `div_right_injective`

English:
theorem div_right_injective
  statement: Function.Injective fun a => b / a
  proof: by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h => inv_injective (mul_right_injective b h)

@[to_additive (attr := simp)]

中文:
定理 div_right_injective
  结论: Function.Injective fun a => b / a
  证明: by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h => inv_injective (mul_right_injective b h)

@[to_additive (attr := simp)]
-/
theorem div_right_injective : Function.Injective fun a => b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h => inv_injective (mul_right_injective b h)

@[to_additive (attr := simp)]
/--
lemma `div_mul_cancel_right` / 引理 `div_mul_cancel_right`

English:
lemma div_mul_cancel_right
  given: (a b : G)
  statement: a / (b * a) = b⁻¹
  proof: by rw [← inv_div, mul_div_cancel_right]

@[to_additive (attr := simp)]

中文:
引理 div_mul_cancel_right
  条件: (a b : G)
  结论: a / (b * a) = b⁻¹
  证明: by rw [← inv_div, mul_div_cancel_right]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_div, mul_div_cancel_right
-/
lemma div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]

@[to_additive (attr := simp)]
/--
theorem `mul_div_mul_right_eq_div` / 定理 `mul_div_mul_right_eq_div`

English:
theorem mul_div_mul_right_eq_div
  given: (a b c : G)
  statement: a * c / (b * c) = a / b
  proof: by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

@[to_additive eq_sub_of_add_eq]

中文:
定理 mul_div_mul_right_eq_div
  条件: (a b c : G)
  结论: a * c / (b * c) = a / b
  证明: by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

@[to_additive eq_sub_of_add_eq]

Depends on / 依赖: div_mul_eq_div_div_swap, mul_div_cancel_right
-/
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

@[to_additive eq_sub_of_add_eq]
/--
theorem `eq_div_of_mul_eq'` / 定理 `eq_div_of_mul_eq'`

English:
theorem eq_div_of_mul_eq'
  given: (h : a * c = b)
  statement: a = b / c
  proof: by simp [← h]

@[to_additive sub_eq_of_eq_add]

中文:
定理 eq_div_of_mul_eq'
  条件: (h : a * c = b)
  结论: a = b / c
  证明: by simp [← h]

@[to_additive sub_eq_of_eq_add]
-/
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

@[to_additive sub_eq_of_eq_add]
/--
theorem `div_eq_of_eq_mul''` / 定理 `div_eq_of_eq_mul''`

English:
theorem div_eq_of_eq_mul''
  given: (h : a = c * b)
  statement: a / b = c
  proof: by simp [h]

@[to_additive]

中文:
定理 div_eq_of_eq_mul''
  条件: (h : a = c * b)
  结论: a / b = c
  证明: by simp [h]

@[to_additive]
-/
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

@[to_additive]
/--
theorem `eq_mul_of_div_eq` / 定理 `eq_mul_of_div_eq`

English:
theorem eq_mul_of_div_eq
  given: (h : a / c = b)
  statement: a = b * c
  proof: by simp [← h]

@[to_additive]

中文:
定理 eq_mul_of_div_eq
  条件: (h : a / c = b)
  结论: a = b * c
  证明: by simp [← h]

@[to_additive]
-/
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

@[to_additive]
/--
theorem `mul_eq_of_eq_div` / 定理 `mul_eq_of_eq_div`

English:
theorem mul_eq_of_eq_div
  given: (h : a = c / b)
  statement: a * b = c
  proof: by simp [h]

@[to_additive (attr := simp)]

中文:
定理 mul_eq_of_eq_div
  条件: (h : a = c / b)
  结论: a * b = c
  证明: by simp [h]

@[to_additive (attr := simp)]
-/
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

@[to_additive (attr := simp)]
/--
theorem `div_right_inj` / 定理 `div_right_inj`

English:
theorem div_right_inj
  statement: a / b = a / c ↔ b = c
  proof: div_right_injective.eq_iff

@[to_additive (attr := simp)]

中文:
定理 div_right_inj
  结论: a / b = a / c ↔ b = c
  证明: div_right_injective.eq_iff

@[to_additive (attr := simp)]

Depends on / 依赖: div_right_injective, div_right_injective.eq_iff, eq_iff
-/
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

@[to_additive (attr := simp)]
/--
theorem `div_left_inj` / 定理 `div_left_inj`

English:
theorem div_left_inj
  statement: b / a = c / a ↔ b = c
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_left_inj _

@[to_additive (attr := simp)]

中文:
定理 div_left_inj
  结论: b / a = c / a ↔ b = c
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_left_inj _

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mul_left_inj
-/
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact mul_left_inj _

@[to_additive (attr := simp)]
/--
theorem `div_mul_div_cancel` / 定理 `div_mul_div_cancel`

English:
theorem div_mul_div_cancel
  given: (a b c : G)
  statement: a / b * (b / c) = a / c
  proof: by
  rw [← mul_div_assoc]; rw [div_mul_cancel]

@[to_additive (attr := simp)]

中文:
定理 div_mul_div_cancel
  条件: (a b c : G)
  结论: a / b * (b / c) = a / c
  证明: by
  rw [← mul_div_assoc]; rw [div_mul_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: div_mul_cancel, mul_div_assoc
-/
theorem div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc]; rw [div_mul_cancel]

@[to_additive (attr := simp)]
/--
lemma `mul_mul_inv_mul_cancel` / 引理 `mul_mul_inv_mul_cancel`

English:
lemma mul_mul_inv_mul_cancel
  given: (a b c : G)
  statement: a * b * (b⁻¹ * c) = a * c
  proof: by
  rw [mul_assoc]; rw [← mul_assoc b]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

中文:
引理 mul_mul_inv_mul_cancel
  条件: (a b c : G)
  结论: a * b * (b⁻¹ * c) = a * c
  证明: by
  rw [mul_assoc]; rw [← mul_assoc b]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_inv_cancel, one_mul
-/
lemma mul_mul_inv_mul_cancel (a b c : G) : a * b * (b⁻¹ * c) = a * c := by
  rw [mul_assoc]; rw [← mul_assoc b]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]
/--
lemma `mul_inv_mul_mul_cancel` / 引理 `mul_inv_mul_mul_cancel`

English:
lemma mul_inv_mul_mul_cancel
  given: (a b c : G)
  statement: a * b⁻¹ * (b * c) = a * c
  proof: by
  rw [mul_assoc]; rw [← mul_assoc b⁻¹]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

中文:
引理 mul_inv_mul_mul_cancel
  条件: (a b c : G)
  结论: a * b⁻¹ * (b * c) = a * c
  证明: by
  rw [mul_assoc]; rw [← mul_assoc b⁻¹]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_assoc, one_mul
-/
lemma mul_inv_mul_mul_cancel (a b c : G) : a * b⁻¹ * (b * c) = a * c := by
  rw [mul_assoc]; rw [← mul_assoc b⁻¹]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]
/--
theorem `div_div_div_cancel_right` / 定理 `div_div_div_cancel_right`

English:
theorem div_div_div_cancel_right
  given: (a b c : G)
  statement: a / c / (b / c) = a / b
  proof: by
  rw [← inv_div c b]; rw [div_inv_eq_mul]; rw [div_mul_div_cancel]

@[to_additive]

中文:
定理 div_div_div_cancel_right
  条件: (a b c : G)
  结论: a / c / (b / c) = a / b
  证明: by
  rw [← inv_div c b]; rw [div_inv_eq_mul]; rw [div_mul_div_cancel]

@[to_additive]

Depends on / 依赖: div_inv_eq_mul, div_mul_div_cancel, inv_div
-/
theorem div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b]; rw [div_inv_eq_mul]; rw [div_mul_div_cancel]

@[to_additive]
/--
theorem `div_eq_one` / 定理 `div_eq_one`

English:
theorem div_eq_one
  statement: a / b = 1 ↔ a = b
  proof: ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

@[to_additive]

中文:
定理 div_eq_one
  结论: a / b = 1 ↔ a = b
  证明: ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

@[to_additive]

Depends on / 依赖: div_self, eq_of_div_eq_one
-/
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

@[to_additive]
/--
theorem `div_ne_one` / 定理 `div_ne_one`

English:
theorem div_ne_one
  statement: a / b != 1 ↔ a != b
  proof: not_congr div_eq_one

@[to_additive (attr := simp)]

中文:
定理 div_ne_one
  结论: a / b != 1 ↔ a != b
  证明: not_congr div_eq_one

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_one, not_congr
-/
theorem div_ne_one : a / b != 1 ↔ a != b :=
  not_congr div_eq_one

@[to_additive (attr := simp)]
/--
theorem `div_eq_self` / 定理 `div_eq_self`

English:
theorem div_eq_self
  statement: a / b = a ↔ b = 1
  proof: by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]

中文:
定理 div_eq_self
  结论: a / b = a ↔ b = 1
  证明: by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]

Depends on / 依赖: div_eq_mul_inv, inv_eq_one, mul_eq_left
-/
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]
/--
theorem `eq_div_iff_mul_eq'` / 定理 `eq_div_iff_mul_eq'`

English:
theorem eq_div_iff_mul_eq'
  statement: a = b / c ↔ a * c = b
  proof: by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]

中文:
定理 eq_div_iff_mul_eq'
  结论: a = b / c ↔ a * c = b
  证明: by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, eq_mul_inv_iff_mul_eq
-/
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]
/--
theorem `div_eq_iff_eq_mul` / 定理 `div_eq_iff_eq_mul`

English:
theorem div_eq_iff_eq_mul
  statement: a / b = c ↔ a = c * b
  proof: by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]

中文:
定理 div_eq_iff_eq_mul
  结论: a / b = c ↔ a = c * b
  证明: by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, mul_inv_eq_iff_eq_mul
-/
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]
/--
theorem `eq_iff_eq_of_div_eq_div` / 定理 `eq_iff_eq_of_div_eq_div`

English:
theorem eq_iff_eq_of_div_eq_div
  given: (H : a / b = c / d)
  statement: a = b ↔ c = d
  proof: by
  rw [← div_eq_one]; rw [H]; rw [div_eq_one]

@[to_additive]

中文:
定理 eq_iff_eq_of_div_eq_div
  条件: (H : a / b = c / d)
  结论: a = b ↔ c = d
  证明: by
  rw [← div_eq_one]; rw [H]; rw [div_eq_one]

@[to_additive]

Depends on / 依赖: div_eq_one
-/
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one]; rw [H]; rw [div_eq_one]

@[to_additive]
/--
theorem `leftInverse_div_mul_left` / 定理 `leftInverse_div_mul_left`

English:
theorem leftInverse_div_mul_left
  given: (c : G)
  statement: Function.LeftInverse (fun x => x / c) fun x => x * c
  proof: fun x => mul_div_cancel_right x c

@[to_additive]

中文:
定理 leftInverse_div_mul_left
  条件: (c : G)
  结论: Function.LeftInverse (fun x => x / c) fun x => x * c
  证明: fun x => mul_div_cancel_right x c

@[to_additive]

Depends on / 依赖: mul_div_cancel_right
-/
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c :=
  fun x => mul_div_cancel_right x c

@[to_additive]
/--
theorem `leftInverse_mul_left_div` / 定理 `leftInverse_mul_left_div`

English:
theorem leftInverse_mul_left_div
  given: (c : G)
  statement: Function.LeftInverse (fun x => x * c) fun x => x / c
  proof: fun x => div_mul_cancel x c

@[to_additive]

中文:
定理 leftInverse_mul_left_div
  条件: (c : G)
  结论: Function.LeftInverse (fun x => x * c) fun x => x / c
  证明: fun x => div_mul_cancel x c

@[to_additive]

Depends on / 依赖: div_mul_cancel
-/
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c :=
  fun x => div_mul_cancel x c

@[to_additive]
/--
theorem `leftInverse_mul_right_inv_mul` / 定理 `leftInverse_mul_right_inv_mul`

English:
theorem leftInverse_mul_right_inv_mul
  given: (c : G)
  proof: fun x => mul_inv_cancel_left c x

@[to_additive]

中文:
定理 leftInverse_mul_right_inv_mul
  条件: (c : G)
  证明: fun x => mul_inv_cancel_left c x

@[to_additive]

Depends on / 依赖: mul_inv_cancel_left
-/
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x :=
  fun x => mul_inv_cancel_left c x

@[to_additive]
/--
theorem `leftInverse_inv_mul_mul_right` / 定理 `leftInverse_inv_mul_mul_right`

English:
theorem leftInverse_inv_mul_mul_right
  given: (c : G)
  proof: fun x => inv_mul_cancel_left c x

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]

中文:
定理 leftInverse_inv_mul_mul_right
  条件: (c : G)
  证明: fun x => inv_mul_cancel_left c x

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]

Depends on / 依赖: inv_mul_cancel_left
-/
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x :=
  fun x => inv_mul_cancel_left c x

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]
/--
lemma `pow_natAbs_eq_one` / 引理 `pow_natAbs_eq_one`

English:
lemma pow_natAbs_eq_one
  statement: a ^ n.natAbs = 1 ↔ a ^ n = 1
  proof: by cases n <;> simp

@[to_additive sub_nsmul]

中文:
引理 pow_natAbs_eq_one
  结论: a ^ n.natAbs = 1 ↔ a ^ n = 1
  证明: by cases n <;> simp

@[to_additive sub_nsmul]
-/
lemma pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by cases n <;> simp

@[to_additive sub_nsmul]
/--
lemma `pow_sub` / 引理 `pow_sub`

English:
lemma pow_sub
  given: (a : G) {m n : Nat} (h : n <= m)
  statement: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  proof: eq_mul_inv_of_mul_eq by rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_neg]

中文:
引理 pow_sub
  条件: (a : G) {m n : 自然数} (h : n <= m)
  结论: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  证明: eq_mul_inv_of_mul_eq by rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_neg]

Depends on / 依赖: Nat.sub_add_cancel, eq_mul_inv_of_mul_eq, pow_add, sub_add_cancel
-/
lemma pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
eq_mul_inv_of_mul_eq by rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_neg]
/--
theorem `inv_pow_sub` / 定理 `inv_pow_sub`

English:
theorem inv_pow_sub
  given: (a : G) {m n : Nat} (h : n <= m)
  statement: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  proof: by
  rw [pow_sub a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

@[to_additive add_one_zsmul]

中文:
定理 inv_pow_sub
  条件: (a : G) {m n : 自然数} (h : n <= m)
  结论: a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
  证明: by
  rw [pow_sub a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

@[to_additive add_one_zsmul]

Depends on / 依赖: inv_inv, inv_pow, pow_sub
-/
theorem inv_pow_sub (a : G) {m n : Nat} (h : n <= m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h]; rw [inv_pow]; rw [inv_pow]; rw [inv_inv]

@[to_additive add_one_zsmul]
/--
lemma `zpow_add_one` / 引理 `zpow_add_one`

English:
lemma zpow_add_one
  given: (a : G)
  statement: forall n : Int, a ^ (n + 1) = a ^ n * a

中文:
引理 zpow_add_one
  条件: (a : G)
  结论: 对任意 n : 整数, a ^ (n + 1) = a ^ n * a
-/
lemma zpow_add_one (a : G) : forall n : Int, a ^ (n + 1) = a ^ n * a
  | (n : Nat) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [Int.add_left_neg]
  | .negSucc (n + 1) => by
    rw [zpow_negSucc]; rw [pow_succ']; rw [mul_inv_rev]; rw [inv_mul_cancel_right]
    rw [Int.negSucc_eq]; rw [Int.neg_add]; rw [Int.neg_add_cancel_right]
    exact zpow_negSucc _ _

@[to_additive sub_one_zsmul]
/--
lemma `zpow_sub_one` / 引理 `zpow_sub_one`

English:
lemma zpow_sub_one
  given: (a : G) (n : Int)
  statement: a ^ (n - 1) = a ^ n * a⁻¹
  proof: calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[to_additive add_zsmul]

中文:
引理 zpow_sub_one
  条件: (a : G) (n : 整数)
  结论: a ^ (n - 1) = a ^ n * a⁻¹
  证明: calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[to_additive add_zsmul]

Depends on / 依赖: Int.sub_add_cancel, mul_inv_cancel_right, sub_add_cancel, zpow_add_one
-/
lemma zpow_sub_one (a : G) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[to_additive add_zsmul]
/--
lemma `zpow_add` / 引理 `zpow_add`

English:
lemma zpow_add
  given: (a : G) (m n : Int)
  statement: a ^ (m + n) = a ^ m * a ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

@[to_additive one_add_zsmul]

中文:
引理 zpow_add
  条件: (a : G) (m n : 整数)
  结论: a ^ (m + n) = a ^ m * a ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

@[to_additive one_add_zsmul]

Depends on / 依赖: Int.add_assoc, Int.add_sub_assoc, add_assoc, add_sub_assoc, mul_assoc, zpow_add_one, zpow_sub_one
-/
lemma zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

@[to_additive one_add_zsmul]
/--
lemma `zpow_one_add` / 引理 `zpow_one_add`

English:
lemma zpow_one_add
  given: (a : G) (n : Int)
  statement: a ^ (1 + n) = a * a ^ n
  proof: by rw [zpow_add, zpow_one]

@[to_additive add_zsmul_self]

中文:
引理 zpow_one_add
  条件: (a : G) (n : 整数)
  结论: a ^ (1 + n) = a * a ^ n
  证明: by rw [zpow_add, zpow_one]

@[to_additive add_zsmul_self]

Depends on / 依赖: zpow_add, zpow_one
-/
lemma zpow_one_add (a : G) (n : Int) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]

@[to_additive add_zsmul_self]
/--
lemma `mul_self_zpow` / 引理 `mul_self_zpow`

English:
lemma mul_self_zpow
  given: (a : G) (n : Int)
  statement: a * a ^ n = a ^ (n + 1)
  proof: by
  rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]

@[to_additive add_self_zsmul]

中文:
引理 mul_self_zpow
  条件: (a : G) (n : 整数)
  结论: a * a ^ n = a ^ (n + 1)
  证明: by
  rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]

@[to_additive add_self_zsmul]

Depends on / 依赖: Int.add_comm, add_comm, zpow_add, zpow_one
-/
lemma mul_self_zpow (a : G) (n : Int) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]

@[to_additive add_self_zsmul]
/--
lemma `mul_zpow_self` / 引理 `mul_zpow_self`

English:
lemma mul_zpow_self
  given: (a : G) (n : Int)
  statement: a ^ n * a = a ^ (n + 1)
  proof: (zpow_add_one ..).symm

中文:
引理 mul_zpow_self
  条件: (a : G) (n : 整数)
  结论: a ^ n * a = a ^ (n + 1)
  证明: (zpow_add_one ..).symm

Depends on / 依赖: zpow_add_one
-/
lemma mul_zpow_self (a : G) (n : Int) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm

/--
lemma `zpow_sub` / 引理 `zpow_sub`

English:
lemma zpow_sub
  given: (a : G) (m n : Int)
  statement: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  proof: by
  rw [Int.sub_eq_add_neg]; rw [zpow_add]; rw [zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]

中文:
引理 zpow_sub
  条件: (a : G) (m n : 整数)
  结论: a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  证明: by
  rw [Int.sub_eq_add_neg]; rw [zpow_add]; rw [zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]
-/
@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : Int) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg]; rw [zpow_add]; rw [zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]
/--
lemma `zpow_natCast_sub_natCast` / 引理 `zpow_natCast_sub_natCast`

English:
lemma zpow_natCast_sub_natCast
  given: (a : G) (m n : Nat)
  statement: a ^ (m - n : Int) = a ^ m / a ^ n
  proof: by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[to_additive natCast_sub_one_zsmul]

中文:
引理 zpow_natCast_sub_natCast
  条件: (a : G) (m n : 自然数)
  结论: a ^ (m - n : 整数) = a ^ m / a ^ n
  证明: by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[to_additive natCast_sub_one_zsmul]

Depends on / 依赖: div_eq_mul_inv, zpow_sub
-/
lemma zpow_natCast_sub_natCast (a : G) (m n : Nat) : a ^ (m - n : Int) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[to_additive natCast_sub_one_zsmul]
/--
lemma `zpow_natCast_sub_one` / 引理 `zpow_natCast_sub_one`

English:
lemma zpow_natCast_sub_one
  given: (a : G) (n : Nat)
  statement: a ^ (n - 1 : Int) = a ^ n / a
  proof: by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

@[to_additive one_sub_natCast_zsmul]

中文:
引理 zpow_natCast_sub_one
  条件: (a : G) (n : 自然数)
  结论: a ^ (n - 1 : 整数) = a ^ n / a
  证明: by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

@[to_additive one_sub_natCast_zsmul]

Depends on / 依赖: div_eq_mul_inv, zpow_sub
-/
lemma zpow_natCast_sub_one (a : G) (n : Nat) : a ^ (n - 1 : Int) = a ^ n / a := by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

@[to_additive one_sub_natCast_zsmul]
/--
lemma `zpow_one_sub_natCast` / 引理 `zpow_one_sub_natCast`

English:
lemma zpow_one_sub_natCast
  given: (a : G) (n : Nat)
  statement: a ^ (1 - n : Int) = a / a ^ n
  proof: by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

中文:
引理 zpow_one_sub_natCast
  条件: (a : G) (n : 自然数)
  结论: a ^ (1 - n : 整数) = a / a ^ n
  证明: by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

Depends on / 依赖: div_eq_mul_inv, zpow_sub
-/
lemma zpow_one_sub_natCast (a : G) (n : Nat) : a ^ (1 - n : Int) = a / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

/--
lemma `zpow_mul_comm` / 引理 `zpow_mul_comm`

English:
lemma zpow_mul_comm
  given: (a : G) (m n : Int)
  statement: a ^ m * a ^ n = a ^ n * a ^ m
  proof: by
  rw [← zpow_add]; rw [Int.add_comm]; rw [zpow_add]

中文:
引理 zpow_mul_comm
  条件: (a : G) (m n : 整数)
  结论: a ^ m * a ^ n = a ^ n * a ^ m
  证明: by
  rw [← zpow_add]; rw [Int.add_comm]; rw [zpow_add]
-/
@[to_additive] lemma zpow_mul_comm (a : G) (m n : Int) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← zpow_add]; rw [Int.add_comm]; rw [zpow_add]

/--
lemma `mul_zpow_mul` / 引理 `mul_zpow_mul`

English:
lemma mul_zpow_mul
  given: (a b : G)
  statement: forall n : Int, (a * b) ^ n * a = a * (b * a) ^ n

中文:
引理 mul_zpow_mul
  条件: (a b : G)
  结论: 对任意 n : 整数, (a * b) ^ n * a = a * (b * a) ^ n
-/
@[to_additive] lemma mul_zpow_mul (a b : G) : forall n : Int, (a * b) ^ n * a = a * (b * a) ^ n
  | (n : Nat) => by simp [mul_pow_mul]
  | .negSucc n => by simp [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq, mul_assoc, mul_pow_mul]

/--
theorem `zpow_eq_zpow_emod` / 定理 `zpow_eq_zpow_emod`

English:
theorem zpow_eq_zpow_emod
  given: {x : G} (m : Int) {n : Int} (h : x ^ n = 1)
  proof: calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

中文:
定理 zpow_eq_zpow_emod
  条件: {x : G} (m : 整数) {n : 整数} (h : x ^ n = 1)
  证明: calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

Depends on / 依赖: Int.emod_add_mul_ediv, emod_add_mul_ediv, zpow_add, zpow_mul
-/
theorem zpow_eq_zpow_emod {x : G} (m : Int) {n : Int} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) :=
  calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

/--
theorem `zpow_eq_zpow_emod'` / 定理 `zpow_eq_zpow_emod'`

English:
theorem zpow_eq_zpow_emod'
  given: {x : G} (m : Int) {n : Nat} (h : x ^ n = 1)
  proof: zpow_eq_zpow_emod m (by simpa)

@[to_additive, simp]

中文:
定理 zpow_eq_zpow_emod'
  条件: {x : G} (m : 整数) {n : 自然数} (h : x ^ n = 1)
  证明: zpow_eq_zpow_emod m (by simpa)

@[to_additive, simp]

Depends on / 依赖: zpow_eq_zpow_emod
-/
theorem zpow_eq_zpow_emod' {x : G} (m : Int) {n : Nat} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : Int)) := zpow_eq_zpow_emod m (by simpa)

@[to_additive, simp]
/--
lemma `zpow_iterate` / 引理 `zpow_iterate`

English:
lemma zpow_iterate
  given: (k : Int)
  statement: forall n : Nat, (fun x : G => x ^ k)^[n] = (· ^ k ^ n)

中文:
引理 zpow_iterate
  条件: (k : 整数)
  结论: 对任意 n : 自然数, (fun x : G => x ^ k)^[n] = (· ^ k ^ n)
-/
lemma zpow_iterate (k : Int) : forall n : Nat, (fun x : G => x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp [Int.pow_zero]
  | n + 1 => by ext; simp [zpow_iterate, Int.pow_succ', zpow_mul]

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`. -/]
/--
lemma `zpow_induction_left` / 引理 `zpow_induction_left`

English:
lemma zpow_induction_left
  statement: {g : G} {P : G -> Prop} (h_one : P (1 : G))
  proof: by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg]; rw [Int.add_comm]; rw [zpow_add]; rw [zpow_neg_one]
    exact h_inv _ ih

中文:
引理 zpow_induction_left
  结论: {g : G} {P : G -> 命题} (h_one : P (1 : G))
  证明: by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg]; rw [Int.add_comm]; rw [zpow_add]; rw [zpow_neg_one]
    exact h_inv _ ih

Depends on / 依赖: Int.add_comm, Int.sub_eq_add_neg, add_comm, h_inv, h_mul, sub_eq_add_neg, zpow_add, zpow_neg_one, zpow_one, zpow_zero
-/
lemma zpow_induction_left {g : G} {P : G -> Prop} (h_one : P (1 : G))
    (h_mul : forall a, P a -> P (g * a)) (h_inv : forall a, P a -> P (g⁻¹ * a)) (n : Int) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm]; rw [zpow_add]; rw [zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg]; rw [Int.add_comm]; rw [zpow_add]; rw [zpow_neg_one]
    exact h_inv _ ih

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`. -/]
/--
lemma `zpow_induction_right` / 引理 `zpow_induction_right`

English:
lemma zpow_induction_right
  statement: {g : G} {P : G -> Prop} (h_one : P (1 : G))
  proof: by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

中文:
引理 zpow_induction_right
  结论: {g : G} {P : G -> 命题} (h_one : P (1 : G))
  证明: by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

Depends on / 依赖: h_inv, h_mul, zpow_add_one, zpow_sub_one, zpow_zero
-/
lemma zpow_induction_right {g : G} {P : G -> Prop} (h_one : P (1 : G))
    (h_mul : forall a, P a -> P (a * g)) (h_inv : forall a, P a -> P (a * g⁻¹)) (n : Int) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
/--
theorem `div_eq_of_eq_mul'` / 定理 `div_eq_of_eq_mul'`

English:
theorem div_eq_of_eq_mul'
  given: {a b c : G} (h : a = b * c)
  statement: a / b = c
  proof: by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm]; rw [inv_mul_cancel_left]

@[to_additive (attr := simp)]

中文:
定理 div_eq_of_eq_mul'
  条件: {a b c : G} (h : a = b * c)
  结论: a / b = c
  证明: by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm]; rw [inv_mul_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_left, mul_comm
-/
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm]; rw [inv_mul_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `mul_div_mul_left_eq_div` / 定理 `mul_div_mul_left_eq_div`

English:
theorem mul_div_mul_left_eq_div
  given: (a b c : G)
  statement: c * a / (c * b) = a / b
  proof: by
  simp

@[to_additive eq_sub_of_add_eq']

中文:
定理 mul_div_mul_left_eq_div
  条件: (a b c : G)
  结论: c * a / (c * b) = a / b
  证明: by
  simp

@[to_additive eq_sub_of_add_eq']
-/
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  simp

@[to_additive eq_sub_of_add_eq']
/--
theorem `eq_div_of_mul_eq''` / 定理 `eq_div_of_mul_eq''`

English:
theorem eq_div_of_mul_eq''
  given: (h : c * a = b)
  statement: a = b / c
  proof: by simp [h.symm]

@[to_additive]

中文:
定理 eq_div_of_mul_eq''
  条件: (h : c * a = b)
  结论: a = b / c
  证明: by simp [h.symm]

@[to_additive]

Depends on / 依赖: h.symm
-/
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

@[to_additive]
/--
theorem `eq_mul_of_div_eq'` / 定理 `eq_mul_of_div_eq'`

English:
theorem eq_mul_of_div_eq'
  given: (h : a / b = c)
  statement: a = b * c
  proof: by simp [h.symm]

@[to_additive]

中文:
定理 eq_mul_of_div_eq'
  条件: (h : a / b = c)
  结论: a = b * c
  证明: by simp [h.symm]

@[to_additive]

Depends on / 依赖: h.symm
-/
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

@[to_additive]
/--
theorem `mul_eq_of_eq_div'` / 定理 `mul_eq_of_eq_div'`

English:
theorem mul_eq_of_eq_div'
  given: (h : b = c / a)
  statement: a * b = c
  proof: by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm c]; rw [mul_inv_cancel_left]

@[to_additive sub_sub_self]

中文:
定理 mul_eq_of_eq_div'
  条件: (h : b = c / a)
  结论: a * b = c
  证明: by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm c]; rw [mul_inv_cancel_left]

@[to_additive sub_sub_self]

Depends on / 依赖: div_eq_mul_inv, mul_comm, mul_inv_cancel_left
-/
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h]; rw [div_eq_mul_inv]; rw [mul_comm c]; rw [mul_inv_cancel_left]

@[to_additive sub_sub_self]
/--
theorem `div_div_self'` / 定理 `div_div_self'`

English:
theorem div_div_self'
  given: (a b : G)
  statement: a / (a / b) = b
  proof: by simp

@[to_additive]

中文:
定理 div_div_self'
  条件: (a b : G)
  结论: a / (a / b) = b
  证明: by simp

@[to_additive]
-/
theorem div_div_self' (a b : G) : a / (a / b) = b := by simp

@[to_additive]
/--
theorem `div_eq_div_mul_div` / 定理 `div_eq_div_mul_div`

English:
theorem div_eq_div_mul_div
  given: (a b c : G)
  statement: a / b = c / b * (a / c)
  proof: by simp [mul_left_comm c]

@[to_additive (attr := simp)]

中文:
定理 div_eq_div_mul_div
  条件: (a b c : G)
  结论: a / b = c / b * (a / c)
  证明: by simp [mul_left_comm c]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_left_comm
-/
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

@[to_additive (attr := simp)]
/--
theorem `div_div_cancel` / 定理 `div_div_cancel`

English:
theorem div_div_cancel
  given: (a b : G)
  statement: a / (a / b) = b
  proof: div_div_self' a b

@[to_additive (attr := simp)]

中文:
定理 div_div_cancel
  条件: (a b : G)
  结论: a / (a / b) = b
  证明: div_div_self' a b

@[to_additive (attr := simp)]

Depends on / 依赖: div_div_self
-/
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

@[to_additive (attr := simp)]
/--
theorem `div_div_cancel_left` / 定理 `div_div_cancel_left`

English:
theorem div_div_cancel_left
  given: (a b : G)
  statement: a / b / a = b⁻¹
  proof: by simp

@[to_additive eq_sub_iff_add_eq']

中文:
定理 div_div_cancel_left
  条件: (a b : G)
  结论: a / b / a = b⁻¹
  证明: by simp

@[to_additive eq_sub_iff_add_eq']
-/
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

@[to_additive eq_sub_iff_add_eq']
/--
theorem `eq_div_iff_mul_eq''` / 定理 `eq_div_iff_mul_eq''`

English:
theorem eq_div_iff_mul_eq''
  statement: a = b / c ↔ c * a = b
  proof: by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]

中文:
定理 eq_div_iff_mul_eq''
  结论: a = b / c ↔ c * a = b
  证明: by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]

Depends on / 依赖: eq_div_iff_mul_eq, mul_comm
-/
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]
/--
theorem `div_eq_iff_eq_mul'` / 定理 `div_eq_iff_eq_mul'`

English:
theorem div_eq_iff_eq_mul'
  statement: a / b = c ↔ a = b * c
  proof: by rw [div_eq_iff_eq_mul, mul_comm]

@[to_additive]

中文:
定理 div_eq_iff_eq_mul'
  结论: a / b = c ↔ a = b * c
  证明: by rw [div_eq_iff_eq_mul, mul_comm]

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, mul_comm
-/
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

@[to_additive]
/--
theorem `div_eq_iff_comm` / 定理 `div_eq_iff_comm`

English:
theorem div_eq_iff_comm
  statement: a / b = c ↔ a / c = b
  proof: by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

@[to_additive (attr := simp)]

中文:
定理 div_eq_iff_comm
  结论: a / b = c ↔ a / c = b
  证明: by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_iff_eq_mul
-/
theorem div_eq_iff_comm : a / b = c ↔ a / c = b := by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

@[to_additive (attr := simp)]
/--
theorem `mul_div_cancel_left` / 定理 `mul_div_cancel_left`

English:
theorem mul_div_cancel_left
  given: (a b : G)
  statement: a * b / a = b
  proof: by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[to_additive (attr := simp)]

中文:
定理 mul_div_cancel_left
  条件: (a b : G)
  结论: a * b / a = b
  证明: by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_inv_mul, inv_mul_cancel_left
-/
theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `mul_div_cancel` / 定理 `mul_div_cancel`

English:
theorem mul_div_cancel
  given: (a b : G)
  statement: a * (b / a) = b
  proof: by
  rw [← mul_div_assoc]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]

中文:
定理 mul_div_cancel
  条件: (a b : G)
  结论: a * (b / a) = b
  证明: by
  rw [← mul_div_assoc]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_div_assoc, mul_div_cancel_left
-/
theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `div_mul_cancel_left` / 定理 `div_mul_cancel_left`

English:
theorem div_mul_cancel_left
  given: (a b : G)
  statement: a / (a * b) = b⁻¹
  proof: by rw [← inv_div, mul_div_cancel_left]

中文:
定理 div_mul_cancel_left
  条件: (a b : G)
  结论: a / (a * b) = b⁻¹
  证明: by rw [← inv_div, mul_div_cancel_left]

Depends on / 依赖: inv_div, mul_div_cancel_left
-/
theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`
@[to_additive]
/--
theorem `mul_mul_inv_cancel'_right` / 定理 `mul_mul_inv_cancel'_right`

English:
theorem mul_mul_inv_cancel'_right
  given: (a b : G)
  statement: a * (b * a⁻¹) = b
  proof: by
  rw [← div_eq_mul_inv]; rw [mul_div_cancel a b]

@[to_additive (attr := simp)]

中文:
定理 mul_mul_inv_cancel'_right
  条件: (a b : G)
  结论: a * (b * a⁻¹) = b
  证明: by
  rw [← div_eq_mul_inv]; rw [mul_div_cancel a b]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mul_div_cancel
-/
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv]; rw [mul_div_cancel a b]

@[to_additive (attr := simp)]
/--
theorem `mul_mul_div_cancel` / 定理 `mul_mul_div_cancel`

English:
theorem mul_mul_div_cancel
  given: (a b c : G)
  statement: a * c * (b / c) = a * b
  proof: by
  rw [mul_assoc]; rw [mul_div_cancel]

@[to_additive (attr := simp)]

中文:
定理 mul_mul_div_cancel
  条件: (a b c : G)
  结论: a * c * (b / c) = a * b
  证明: by
  rw [mul_assoc]; rw [mul_div_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_div_cancel
-/
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc]; rw [mul_div_cancel]

@[to_additive (attr := simp)]
/--
theorem `div_mul_mul_cancel` / 定理 `div_mul_mul_cancel`

English:
theorem div_mul_mul_cancel
  given: (a b c : G)
  statement: a / c * (b * c) = a * b
  proof: by
  rw [mul_left_comm]; rw [div_mul_cancel]; rw [mul_comm]

@[to_additive (attr := simp)]

中文:
定理 div_mul_mul_cancel
  条件: (a b c : G)
  结论: a / c * (b * c) = a * b
  证明: by
  rw [mul_left_comm]; rw [div_mul_cancel]; rw [mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: div_mul_cancel, mul_comm, mul_left_comm
-/
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm]; rw [div_mul_cancel]; rw [mul_comm]

@[to_additive (attr := simp)]
/--
theorem `div_mul_div_cancel'` / 定理 `div_mul_div_cancel'`

English:
theorem div_mul_div_cancel'
  given: (a b c : G)
  statement: a / b * (c / a) = c / b
  proof: by
  rw [mul_comm]; apply div_mul_div_cancel

@[to_additive (attr := simp)]

中文:
定理 div_mul_div_cancel'
  条件: (a b c : G)
  结论: a / b * (c / a) = c / b
  证明: by
  rw [mul_comm]; apply div_mul_div_cancel

@[to_additive (attr := simp)]

Depends on / 依赖: div_mul_div_cancel, mul_comm
-/
theorem div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel

@[to_additive (attr := simp)]
/--
theorem `mul_div_div_cancel` / 定理 `mul_div_div_cancel`

English:
theorem mul_div_div_cancel
  given: (a b c : G)
  statement: a * b / (a / c) = b * c
  proof: by
  rw [← div_mul]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]

中文:
定理 mul_div_div_cancel
  条件: (a b c : G)
  结论: a * b / (a / c) = b * c
  证明: by
  rw [← div_mul]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: div_mul, mul_div_cancel_left
-/
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul]; rw [mul_div_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `div_div_div_cancel_left` / 定理 `div_div_div_cancel_left`

English:
theorem div_div_div_cancel_left
  given: (a b c : G)
  statement: c / a / (c / b) = b / a
  proof: by
  rw [← inv_div b c]; rw [div_inv_eq_mul]; rw [mul_comm]; rw [div_mul_div_cancel]

@[to_additive]

中文:
定理 div_div_div_cancel_left
  条件: (a b c : G)
  结论: c / a / (c / b) = b / a
  证明: by
  rw [← inv_div b c]; rw [div_inv_eq_mul]; rw [mul_comm]; rw [div_mul_div_cancel]

@[to_additive]

Depends on / 依赖: div_inv_eq_mul, div_mul_div_cancel, inv_div, mul_comm
-/
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c]; rw [div_inv_eq_mul]; rw [mul_comm]; rw [div_mul_div_cancel]

@[to_additive]
/--
theorem `div_eq_div_iff_mul_eq_mul` / 定理 `div_eq_div_iff_mul_eq_mul`

English:
theorem div_eq_div_iff_mul_eq_mul
  statement: a / b = c / d ↔ a * d = c * b
  proof: by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [eq_comm]; rw [div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]

中文:
定理 div_eq_div_iff_mul_eq_mul
  结论: a / b = c / d ↔ a * d = c * b
  证明: by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [eq_comm]; rw [div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, mul_comm
-/
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [eq_comm]; rw [div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]
/--
theorem `mul_inv_eq_mul_inv_iff_mul_eq_mul` / 定理 `mul_inv_eq_mul_inv_iff_mul_eq_mul`

English:
theorem mul_inv_eq_mul_inv_iff_mul_eq_mul
  statement: a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
  proof: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]

中文:
定理 mul_inv_eq_mul_inv_iff_mul_eq_mul
  结论: a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
  证明: by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]

Depends on / 依赖: div_eq_div_iff_mul_eq_mul, div_eq_mul_inv
-/
theorem mul_inv_eq_mul_inv_iff_mul_eq_mul : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv]; rw [← div_eq_mul_inv]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]
/--
theorem `inv_mul_eq_inv_mul_iff_mul_eq_mul` / 定理 `inv_mul_eq_inv_mul_iff_mul_eq_mul`

English:
theorem inv_mul_eq_inv_mul_iff_mul_eq_mul
  statement: b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
  proof: by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]

中文:
定理 inv_mul_eq_inv_mul_iff_mul_eq_mul
  结论: b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
  证明: by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]

Depends on / 依赖: div_eq_div_iff_mul_eq_mul, div_eq_inv_mul
-/
theorem inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul]; rw [← div_eq_inv_mul]; rw [div_eq_div_iff_mul_eq_mul]

@[to_additive]
/--
theorem `div_eq_div_iff_div_eq_div` / 定理 `div_eq_div_iff_div_eq_div`

English:
theorem div_eq_div_iff_div_eq_div
  statement: a / b = c / d ↔ a / c = b / d
  proof: by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [div_eq_iff_eq_mul']; rw [mul_div_assoc]

@[to_additive (attr := simp)]

中文:
定理 div_eq_div_iff_div_eq_div
  结论: a / b = c / d ↔ a / c = b / d
  证明: by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [div_eq_iff_eq_mul']; rw [mul_div_assoc]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_iff_eq_mul, div_mul_eq_mul_div, mul_div_assoc
-/
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul]; rw [div_mul_eq_mul_div]; rw [div_eq_iff_eq_mul']; rw [mul_div_assoc]

@[to_additive (attr := simp)]
/--
lemma `const_div_involutive` / 引理 `const_div_involutive`

English:
lemma const_div_involutive
  given: (a : G)
  statement: Function.Involutive (a / ·)
  proof: fun _ => div_div_cancel ..

中文:
引理 const_div_involutive
  条件: (a : G)
  结论: Function.Involutive (a / ·)
  证明: fun _ => div_div_cancel ..

Depends on / 依赖: div_div_cancel
-/
lemma const_div_involutive (a : G) : Function.Involutive (a / ·) :=
  fun _ => div_div_cancel ..

end CommGroup

section multiplicative

variable [Monoid β] (p r : α -> α -> Prop) [Std.Total r] (f : α -> α -> β)

@[to_additive additive_of_symm_of_total]
/--
lemma `multiplicative_of_symm_of_total` / 引理 `multiplicative_of_symm_of_total`

English:
lemma multiplicative_of_symm_of_total
  statement: [Std.Symm p]
  proof: by
  have hmul' : forall {b c}, r b c -> p a b -> p b c -> p a c -> f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c)]; rw [← hf_swap pab]; rw [mul_assoc]
    obtain rac | rca := total_of r 

中文:
引理 multiplicative_of_symm_of_total
  结论: [Std.Symm p]
  证明: by
  have hmul' : forall {b c}, r b c -> p a b -> p b c -> p a c -> f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c)]; rw [← hf_swap pab]; rw [mul_assoc]
    obtain rac | rca := total_of r 

Depends on / 依赖: hf_swap, mul_assoc, mul_one, one_mul, total_of
-/
lemma multiplicative_of_symm_of_total [Std.Symm p]
    (hf_swap : forall {a b}, p a b -> f a b * f b a = 1)
    (hmul : forall {a b c}, r a b -> r b c -> p a b -> p b c -> p a c -> f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : forall {b c}, r b c -> p a b -> p b c -> p a c -> f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c)]; rw [← hf_swap pab]; rw [mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (symm pab) pac pbc]
    · rw [hmul rbc rca pbc (symm pac) (symm pab), mul_assoc, hf_swap (symm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (symm pbc) pab, mul_assoc, hf_swap (symm pbc), mul_one]

@[deprecated (since := "2026-06-10")]
alias additive_of_symmetric_of_total := additive_of_symm_of_total
@[to_additive existing additive_of_symmetric_of_total, deprecated (since := "2026-06-10")]
alias multiplicative_of_symmetric_of_total := multiplicative_of_symm_of_total

@[deprecated (since := "2026-01-09")]
alias additive_of_symmetric_of_isTotal := additive_of_symm_of_total
@[to_additive existing additive_of_symmetric_of_isTotal, deprecated (since := "2026-01-09")]
alias multiplicative_of_symmetric_of_isTotal := multiplicative_of_symm_of_total

/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_total /-- If a binary function from a type equipped with a total
  relation `r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in
  order to show it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and
  `r b c` are satisfied. We allow restricting to a subset specified by a predicate `p`. -/]
/--
theorem `multiplicative_of_total` / 定理 `multiplicative_of_total`

English:
theorem multiplicative_of_total
  statement: (p : α -> Prop) (hswap : forall {a b}, p a -> p b -> f a b * f b a = 1)
  proof: by
  have : Std.Symm (p · ∧ p ·) := { symm _ _ := And.symm }
  apply multiplicative_of_symm_of_total (p · ∧ p ·) r f
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

@[deprecated (since := "2026-01-09")]

中文:
定理 multiplicative_of_total
  结论: (p : α -> 命题) (hswap : 对任意 {a b}, p a -> p b -> f a b * f b a = 1)
  证明: by
  have : Std.Symm (p · ∧ p ·) := { symm _ _ := And.symm }
  apply multiplicative_of_symm_of_total (p · ∧ p ·) r f
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

@[deprecated (since := "2026-01-09")]

Depends on / 依赖: And.symm, Std.Symm, _pbc, and_imp, exacts, multiplicative_of_symm_of_total, simp_rw
-/
theorem multiplicative_of_total (p : α -> Prop) (hswap : forall {a b}, p a -> p b -> f a b * f b a = 1)
    (hmul : forall {a b c}, r a b -> r b c -> p a -> p b -> p c -> f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  have : Std.Symm (p · ∧ p ·) := { symm _ _ := And.symm }
  apply multiplicative_of_symm_of_total (p · ∧ p ·) r f
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

@[deprecated (since := "2026-01-09")]
alias additive_of_isTotal := additive_of_total
@[to_additive existing additive_of_isTotal, deprecated (since := "2026-01-09")]
alias multiplicative_of_isTotal := multiplicative_of_total

end multiplicative

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`. -/
@[to_additive]
/--
lemma `hom_coe_pow` / 引理 `hom_coe_pow`

English:
lemma hom_coe_pow
  statement: {F : Type*} [Monoid F] (c : F -> M -> M) (h1 : c 1 = id)

中文:
引理 hom_coe_pow
  结论: {F : 类型} [Monoid F] (c : F -> M -> M) (h1 : c 1 = id)
-/
lemma hom_coe_pow {F : Type*} [Monoid F] (c : F -> M -> M) (h1 : c 1 = id)
    (hmul : forall f g, c (f * g) = c f ∘ c g) (f : F) : forall n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero]; rw [h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ, hmul, hom_coe_pow c h1 hmul f n]

/-!
### Instances for `grind`.
-/

open Lean

variable (α : Type*)

/--
Instance `AddCommMonoid.toGrindNatModule` / 实例 `AddCommMonoid.toGrindNatModule`

English:
instance AddCommMonoid.toGrindNatModule
  signature: [s : AddCommMonoid α]
  body: { s with
    nsmul := ⟨s.nsmul⟩
    zero_nsmul := AddMonoid.nsmul_zero
    add_one_nsmul n a := by change (n + 1) • a = n • a + a; rw [add_nsmul, one_nsmul] }

中文:
实例 AddCommMonoid.toGrindNatModule
  签名: [s : AddCommMonoid α]
  定义体: { s with
    nsmul := ⟨s.nsmul⟩
    zero_nsmul := AddMonoid.nsmul_zero
    add_one_nsmul n a := by change (n + 1) • a = n • a + a; rw [add_nsmul, one_nsmul] }

Depends on / 依赖: AddMonoid, AddMonoid.nsmul_zero, add_nsmul, add_one_nsmul, nsmul_zero, one_nsmul, s.nsmul, zero_nsmul
-/
instance AddCommMonoid.toGrindNatModule [s : AddCommMonoid α] :
    Grind.NatModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zero_nsmul := AddMonoid.nsmul_zero
    add_one_nsmul n a := by change (n + 1) • a = n • a + a; rw [add_nsmul, one_nsmul] }

/--
Instance `AddCommGroup.toGrindIntModule` / 实例 `AddCommGroup.toGrindIntModule`

English:
instance AddCommGroup.toGrindIntModule
  signature: [s : AddCommGroup α]
  body: { s with
    nsmul := ⟨s.nsmul⟩
    zsmul := ⟨s.zsmul⟩
    zero_zsmul := SubNegMonoid.zsmul_zero'
    one_zsmul := one_zsmul
    add_zsmul n m a := add_zsmul a n m
    zsmul_natCast_eq_nsmul n a := by simp }

中文:
实例 AddCommGroup.toGrindIntModule
  签名: [s : AddCommGroup α]
  定义体: { s with
    nsmul := ⟨s.nsmul⟩
    zsmul := ⟨s.zsmul⟩
    zero_zsmul := SubNegMonoid.zsmul_zero'
    one_zsmul := one_zsmul
    add_zsmul n m a := add_zsmul a n m
    zsmul_natCast_eq_nsmul n a := by simp }

Depends on / 依赖: SubNegMonoid, SubNegMonoid.zsmul_zero, add_zsmul, one_zsmul, s.nsmul, s.zsmul, zero_zsmul, zsmul_natCast_eq_nsmul, zsmul_zero
-/
instance AddCommGroup.toGrindIntModule [s : AddCommGroup α] :
    Grind.IntModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zsmul := ⟨s.zsmul⟩
    zero_zsmul := SubNegMonoid.zsmul_zero'
    one_zsmul := one_zsmul
    add_zsmul n m a := add_zsmul a n m
    zsmul_natCast_eq_nsmul n a := by simp }

/--
Instance `IsRightCancelAdd.toGrindAddRightCancel` / 实例 `IsRightCancelAdd.toGrindAddRightCancel`

English:
instance IsRightCancelAdd.toGrindAddRightCancel
  signature: [AddSemigroup α] [IsRightCancelAdd α]
  body: add_right_cancel

中文:
实例 IsRightCancelAdd.toGrindAddRightCancel
  签名: [AddSemigroup α] [IsRightCancelAdd α]
  定义体: add_right_cancel

Depends on / 依赖: add_right_cancel
-/
instance IsRightCancelAdd.toGrindAddRightCancel [AddSemigroup α] [IsRightCancelAdd α] :
    Grind.AddRightCancel α where
  add_right_cancel _ _ _ := add_right_cancel
