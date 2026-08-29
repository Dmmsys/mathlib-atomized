/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

/--
Inductive type `DihedralGroup` / 归纳类型 `DihedralGroup`

English:
inductive DihedralGroup
  parameters: (n : Nat)
  constructors (2):
    - r: ZMod n -> DihedralGroup n
    - sr: ZMod n -> DihedralGroup n

中文:
归纳类型 Dihedral群
  参数: (n : 自然数)
  构造子 (2 个):
    - r: ZMod n -> Dihedral群 n
    - sr: ZMod n -> Dihedral群 n
-/
inductive DihedralGroup (n : Nat) : Type
  | r : ZMod n -> DihedralGroup n
  | sr : ZMod n -> DihedralGroup n
  deriving DecidableEq

namespace DihedralGroup

variable {n : Nat}

set_option backward.privateInPublic true in
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : DihedralGroup n -> DihedralGroup n -> DihedralGroup n

中文:
定义 mul
  签名: : Dihedral群 n -> Dihedral群 n -> Dihedral群 n
-/
private def mul : DihedralGroup n -> DihedralGroup n -> DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

set_option backward.privateInPublic true in
/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : DihedralGroup n
  body: r 0

中文:
定义 one
  签名: : Dihedral群 n
  定义体: r 0
-/
private def one : DihedralGroup n :=
  r 0

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (DihedralGroup n)
  body: ⟨one⟩

中文:
实例 :
  签名: 可居 (Dihedral群 n)
  定义体: ⟨one⟩
-/
instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

set_option backward.privateInPublic true in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : DihedralGroup n -> DihedralGroup n

中文:
定义 inv
  签名: : Dihedral群 n -> Dihedral群 n
-/
private def inv : DihedralGroup n -> DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (DihedralGroup n)
  body: mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro (a | a)
    · exact congr_arg r (neg_add_cancel a)
    · exact congr_arg r (sub_self a)

@[simp]

中文:
实例 :
  签名: 群 (Dihedral群 n)
  定义体: mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro (a | a)
    · exact congr_arg r (neg_add_cancel a)
    · exact congr_arg r (sub_self a)

@[simp]
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro (a | a)
    · exact congr_arg r (neg_add_cancel a)
    · exact congr_arg r (sub_self a)

@[simp]
/--
theorem `r_mul_r` / 定理 `r_mul_r`

English:
theorem r_mul_r
  given: (i j : ZMod n)
  statement: r i * r j = r (i + j)
  proof: rfl

@[simp]

中文:
定理 r_mul_r
  条件: (i j : ZMod n)
  结论: r i * r j = r (i + j)
  证明: rfl

@[simp]
-/
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
/--
theorem `r_mul_sr` / 定理 `r_mul_sr`

English:
theorem r_mul_sr
  given: (i j : ZMod n)
  statement: r i * sr j = sr (j - i)
  proof: rfl

@[simp]

中文:
定理 r_mul_sr
  条件: (i j : ZMod n)
  结论: r i * sr j = sr (j - i)
  证明: rfl

@[simp]
-/
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
/--
theorem `sr_mul_r` / 定理 `sr_mul_r`

English:
theorem sr_mul_r
  given: (i j : ZMod n)
  statement: sr i * r j = sr (i + j)
  proof: rfl

@[simp]

中文:
定理 sr_mul_r
  条件: (i j : ZMod n)
  结论: sr i * r j = sr (i + j)
  证明: rfl

@[simp]
-/
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
/--
theorem `sr_mul_sr` / 定理 `sr_mul_sr`

English:
theorem sr_mul_sr
  given: (i j : ZMod n)
  statement: sr i * sr j = r (j - i)
  proof: rfl

@[simp]

中文:
定理 sr_mul_sr
  条件: (i j : ZMod n)
  结论: sr i * sr j = r (j - i)
  证明: rfl

@[simp]
-/
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl

@[simp]
/--
theorem `inv_r` / 定理 `inv_r`

English:
theorem inv_r
  given: (i : ZMod n)
  statement: (r i)⁻¹ = r (-i)
  proof: rfl

@[simp]

中文:
定理 inv_r
  条件: (i : ZMod n)
  结论: (r i)⁻¹ = r (-i)
  证明: rfl

@[simp]
-/
theorem inv_r (i : ZMod n) : (r i)⁻¹ = r (-i) :=
  rfl

@[simp]
/--
theorem `inv_sr` / 定理 `inv_sr`

English:
theorem inv_sr
  given: (i : ZMod n)
  statement: (sr i)⁻¹ = sr i
  proof: rfl

@[simp]

中文:
定理 inv_sr
  条件: (i : ZMod n)
  结论: (sr i)⁻¹ = sr i
  证明: rfl

@[simp]
-/
theorem inv_sr (i : ZMod n) : (sr i)⁻¹ = sr i :=
  rfl

@[simp]
/--
theorem `r_zero` / 定理 `r_zero`

English:
theorem r_zero
  statement: r 0 = (1 : DihedralGroup n)
  proof: rfl

中文:
定理 r_zero
  结论: r 0 = (1 : Dihedral群 n)
  证明: rfl
-/
theorem r_zero : r 0 = (1 : DihedralGroup n) :=
  rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : DihedralGroup n) = r 0
  proof: rfl

@[simp]

中文:
定理 one_def
  结论: (1 : Dihedral群 n) = r 0
  证明: rfl

@[simp]
-/
theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl

@[simp]
/--
theorem `r_pow` / 定理 `r_pow`

English:
theorem r_pow
  given: (i : ZMod n) (k : Nat)
  statement: (r i) ^ k = r (i * k : ZMod n)
  proof: by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, r_zero]
  | succ k IH =>
    rw [pow_add]; rw [pow_one]; rw [IH]; rw [r_mul_r]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [r.injEq]; rw [mul_add]; rw [mul_one]

@[simp]

中文:
定理 r_pow
  条件: (i : ZMod n) (k : 自然数)
  结论: (r i) ^ k = r (i * k : ZMod n)
  证明: by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, r_zero]
  | succ k IH =>
    rw [pow_add]; rw [pow_one]; rw [IH]; rw [r_mul_r]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [r.injEq]; rw [mul_add]; rw [mul_one]

@[simp]

Depends on / 依赖: Nat.cast_add, Nat.cast_one, Nat.cast_zero, cast_add, cast_one, cast_zero, mul_add, mul_one, mul_zero, pow_add, pow_one, pow_zero, r.injEq, r_mul_r, r_zero
-/
theorem r_pow (i : ZMod n) (k : Nat) : (r i) ^ k = r (i * k : ZMod n) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, r_zero]
  | succ k IH =>
    rw [pow_add]; rw [pow_one]; rw [IH]; rw [r_mul_r]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [r.injEq]; rw [mul_add]; rw [mul_one]

@[simp]
/--
theorem `r_zpow` / 定理 `r_zpow`

English:
theorem r_zpow
  given: (i : ZMod n) (k : Int)
  statement: (r i) ^ k = r (i * k : ZMod n)
  proof: by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

中文:
定理 r_zpow
  条件: (i : ZMod n) (k : 整数)
  结论: (r i) ^ k = r (i * k : ZMod n)
  证明: by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

Depends on / 依赖: neg_mul_eq_mul_neg, r_pow
-/
theorem r_zpow (i : ZMod n) (k : Int) : (r i) ^ k = r (i * k : ZMod n) := by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

/-- The equivalence between the dihedral group and the sum of `ZMod`s. -/
@[simps]
/--
Definition of `equivSum` / `equivSum` 的定义

English:
definition equivSum
  signature: : DihedralGroup n ≃ (ZMod n) oplus (ZMod n) where
  body: by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

中文:
定义 equivSum
  签名: : Dihedral群 n ≃ (ZMod n) oplus (ZMod n) where
  定义体: by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

Depends on / 依赖: right_inv
-/
def equivSum : DihedralGroup n ≃ (ZMod n) oplus (ZMod n) where
  toFun
    | r j => .inl j
    | sr j => .inr j
  invFun
    | .inl j => r j
    | .inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] : Fintype (DihedralGroup n)
  body: Fintype.ofEquiv _ equivSum.symm

中文:
实例 [NeZero
  签名: n] : 有限类型 (Dihedral群 n)
  定义体: Fintype.ofEquiv _ equivSum.symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, equivSum, equivSum.symm, ofEquiv
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ equivSum.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Infinite (DihedralGroup 0)
  body: equivSum.symm.infinite_iff.mp inferInstance

中文:
实例 :
  签名: 无限 (Dihedral群 0)
  定义体: equivSum.symm.infinite_iff.mp inferInstance

Depends on / 依赖: equivSum, equivSum.symm.infinite_iff.mp, infinite_iff
-/
instance : Infinite (DihedralGroup 0) :=
  equivSum.symm.infinite_iff.mp inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (DihedralGroup n)
  body: ⟨⟨r 0, sr 0, by by_contra h; injection h⟩⟩

中文:
实例 :
  签名: 非平凡 (Dihedral群 n)
  定义体: ⟨⟨r 0, sr 0, by by_contra h; injection h⟩⟩

Depends on / 依赖: injection
-/
instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by by_contra h; injection h⟩⟩

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: [NeZero n]
  statement: Fintype.card (DihedralGroup n) = 2 * n
  proof: by
  rw [← Fintype.card_eq.mpr ⟨equivSum.symm⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]

中文:
定理 card
  条件: [NeZero n]
  结论: 有限类型.card (Dihedral群 n) = 2 * n
  证明: by
  rw [← Fintype.card_eq.mpr ⟨equivSum.symm⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]

Depends on / 依赖: Fintype, Fintype.card_eq.mpr, Fintype.card_sum, ZMod.card, card_eq, card_sum, equivSum, equivSum.symm, two_mul
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨equivSum.symm⟩]; rw [Fintype.card_sum]; rw [ZMod.card]; rw [two_mul]

/--
theorem `nat_card` / 定理 `nat_card`

English:
theorem nat_card
  statement: Nat.card (DihedralGroup n) = 2 * n
  proof: by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]

中文:
定理 nat_card
  结论: 自然数.card (Dihedral群 n) = 2 * n
  证明: by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]

Depends on / 依赖: Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, card_eq_fintype_card, card_eq_zero_of_infinite
-/
theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]

/--
theorem `r_one_pow` / 定理 `r_one_pow`

English:
theorem r_one_pow
  given: (k : Nat)
  statement: (r 1 : DihedralGroup n) ^ k = r k
  proof: by
  simp only [r_pow, one_mul]

中文:
定理 r_one_pow
  条件: (k : 自然数)
  结论: (r 1 : Dihedral群 n) ^ k = r k
  证明: by
  simp only [r_pow, one_mul]

Depends on / 依赖: one_mul, r_pow
-/
theorem r_one_pow (k : Nat) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_pow, one_mul]

/--
theorem `r_one_zpow` / 定理 `r_one_zpow`

English:
theorem r_one_zpow
  given: (k : Int)
  statement: (r 1 : DihedralGroup n) ^ k = r k
  proof: by
  simp only [r_zpow, one_mul]

中文:
定理 r_one_zpow
  条件: (k : 整数)
  结论: (r 1 : Dihedral群 n) ^ k = r k
  证明: by
  simp only [r_zpow, one_mul]

Depends on / 依赖: one_mul, r_zpow
-/
theorem r_one_zpow (k : Int) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_zpow, one_mul]

/--
theorem `r_one_pow_n` / 定理 `r_one_pow_n`

English:
theorem r_one_pow_n
  statement: r (1 : ZMod n) ^ n = 1
  proof: by
  simp

中文:
定理 r_one_pow_n
  结论: r (1 : ZMod n) ^ n = 1
  证明: by
  simp
-/
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  simp

/--
theorem `sr_mul_self` / 定理 `sr_mul_self`

English:
theorem sr_mul_self
  given: (i : ZMod n)
  statement: sr i * sr i = 1
  proof: by
  simp

中文:
定理 sr_mul_self
  条件: (i : ZMod n)
  结论: sr i * sr i = 1
  证明: by
  simp
-/
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by
  simp

/-- `sr i` has order 2.
-/
@[simp]
/--
theorem `orderOf_sr` / 定理 `orderOf_sr`

English:
theorem orderOf_sr
  given: (i : ZMod n)
  statement: orderOf (sr i) = 2
  proof: by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · simp [← r_zero]

中文:
定理 orderOf_sr
  条件: (i : ZMod n)
  结论: orderOf (sr i) = 2
  证明: by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · simp [← r_zero]

Depends on / 依赖: orderOf_eq_prime, r_zero, sr_mul_self
-/
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · simp [← r_zero]

/-- `r 1` has order `n`.
-/
@[simp]
/--
theorem `orderOf_r_one` / 定理 `orderOf_r_one`

English:
theorem orderOf_r_one
  statement: orderOf (r 1 : DihedralGroup n) = n
  proof: by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow]; rw [one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
orderOf_dvd_of_pow_eq_one @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero]; rw [ZMod.val_natCast]; rw [Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

中文:
定理 orderOf_r_one
  结论: orderOf (r 1 : Dihedral群 n) = n
  证明: by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow]; rw [one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
orderOf_dvd_of_pow_eq_one @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero]; rw [ZMod.val_natCast]; rw [Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

Depends on / 依赖: DihedralGroup, Nat.le_of_dvd, Nat.mod_eq_of_lt, NeZero, NeZero.pos, ZMod.val_eq_zero, ZMod.val_natCast, absurd, eq_zero_or_neZero, h2.symm, hn.ne, injection, le_of_dvd, lt_or_eq, lt_or_eq.resolve_left, mod_eq_of_lt, one_def, orderOf, orderOf_dvd_of_pow_eq_one, orderOf_eq_zero_iff
-/
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow]; rw [one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
orderOf_dvd_of_pow_eq_one @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero]; rw [ZMod.val_natCast]; rw [Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

/--
theorem `orderOf_r` / 定理 `orderOf_r`

English:
theorem orderOf_r
  given: [NeZero n] (i : ZMod n)
  statement: orderOf (r i) = n / Nat.gcd n i.val
  proof: by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow]; rw [orderOf_pow]; rw [orderOf_r_one]

中文:
定理 orderOf_r
  条件: [NeZero n] (i : ZMod n)
  结论: orderOf (r i) = n / 自然数.最大公约数 n i.val
  证明: by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow]; rw [orderOf_pow]; rw [orderOf_r_one]

Depends on / 依赖: ZMod.natCast_zmod_val, conv_lhs, natCast_zmod_val, orderOf_pow, orderOf_r_one, r_one_pow
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow]; rw [orderOf_pow]; rw [orderOf_r_one]

/--
theorem `exponent` / 定理 `exponent`

English:
theorem exponent
  statement: Monoid.exponent (DihedralGroup n) = lcm n 2
  proof: by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert! Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm

中文:
定理 exponent
  结论: 幺半群.exponent (Dihedral群 n) = 最小公倍数 n 2
  证明: by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert! Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm

Depends on / 依赖: Monoid, Monoid.exponent_dvd_of_forall_pow_eq_one, Monoid.exponent_eq_zero_of_order_zero, Monoid.order_dvd_exponent, Nat.div_mul_cancel, Nat.dvd_antisymm, Nat.dvd_trans, Nat.gcd_dvd_left, convert, div_mul_cancel, dvd_antisymm, dvd_lcm_left, dvd_lcm_right, dvd_trans, eq_zero_or_neZero, exponent_dvd_of_forall_pow_eq_one, exponent_eq_zero_of_order_zero, gcd_dvd_left, lcm_dvd, m.val
-/
theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert! Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert! Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm

/--
lemma `not_commutative` / 引理 `not_commutative`

English:
lemma not_commutative
  statement: forall {n : Nat}, n != 1 -> n != 2 -> ¬IsMulCommutative (DihedralGroup n)
  proof: h'.is_comm.comm (r 1) (sr 0)
    rw [r_mul_sr]; rw [zero_sub]; rw [sr_mul_r]; rw [zero_add]; rw [sr.injEq]; rw [neg_eq_iff_add_eq_zero]; rw [one_add_one_eq_two]; rw [← ZMod.val_eq_zero]; rw [ZMod.val_two_eq_two_mod] at this
simpa using Nat.le_of_dvd Nat.zero_lt_two Nat.dvd_of_mod_eq_zero this

中文:
引理 not_commutative
  结论: 对任意 {n : 自然数}, n != 1 -> n != 2 -> ¬是MulCommutative (Dihedral群 n)
  证明: h'.is_comm.comm (r 1) (sr 0)
    rw [r_mul_sr]; rw [zero_sub]; rw [sr_mul_r]; rw [zero_add]; rw [sr.injEq]; rw [neg_eq_iff_add_eq_zero]; rw [one_add_one_eq_two]; rw [← ZMod.val_eq_zero]; rw [ZMod.val_two_eq_two_mod] at this
simpa using Nat.le_of_dvd Nat.zero_lt_two Nat.dvd_of_mod_eq_zero this

Depends on / 依赖: is_comm, is_comm.comm
-/
lemma not_commutative : forall {n : Nat}, n != 1 -> n != 2 -> ¬IsMulCommutative (DihedralGroup n)
  | 0, _, _, h' => by simpa using h'.is_comm.comm (r 1) (sr 0)
  | n + 3, _, _, h' => by
    have := h'.is_comm.comm (r 1) (sr 0)
    rw [r_mul_sr]; rw [zero_sub]; rw [sr_mul_r]; rw [zero_add]; rw [sr.injEq]; rw [neg_eq_iff_add_eq_zero]; rw [one_add_one_eq_two]; rw [← ZMod.val_eq_zero]; rw [ZMod.val_two_eq_two_mod] at this
simpa using Nat.le_of_dvd Nat.zero_lt_two Nat.dvd_of_mod_eq_zero this

/--
lemma `commutative_iff` / 引理 `commutative_iff`

English:
lemma commutative_iff
  statement: IsMulCommutative (DihedralGroup n) ↔ n = 1 ∨ n = 2 where
  proof: by contrapose!; rintro ⟨h1, h2⟩; exact not_commutative h1 h2
  mpr := by rintro (rfl | rfl) <;> exact ⟨⟨by decide⟩⟩

中文:
引理 commutative_iff
  结论: 是MulCommutative (Dihedral群 n) ↔ n = 1 ∨ n = 2 where
  证明: by contrapose!; rintro ⟨h1, h2⟩; exact not_commutative h1 h2
  mpr := by rintro (rfl | rfl) <;> exact ⟨⟨by decide⟩⟩

Depends on / 依赖: contrapose, not_commutative
-/
lemma commutative_iff : IsMulCommutative (DihedralGroup n) ↔ n = 1 ∨ n = 2 where
  mp := by contrapose!; rintro ⟨h1, h2⟩; exact not_commutative h1 h2
  mpr := by rintro (rfl | rfl) <;> exact ⟨⟨by decide⟩⟩

/--
lemma `not_isCyclic` / 引理 `not_isCyclic`

English:
lemma not_isCyclic
  given: (h1 : n != 1)
  statement: ¬ IsCyclic (DihedralGroup n)
  proof: fun h => by
  by_cases h2 : n = 2
  · simpa [exponent, card, h2] using h.exponent_eq_card
  · exact not_commutative h1 h2 h.isMulCommutative

中文:
引理 not_isCyclic
  条件: (h1 : n != 1)
  结论: ¬ 是循环 (Dihedral群 n)
  证明: fun h => by
  by_cases h2 : n = 2
  · simpa [exponent, card, h2] using h.exponent_eq_card
  · exact not_commutative h1 h2 h.isMulCommutative

Depends on / 依赖: exponent, exponent_eq_card, h.exponent_eq_card, h.isMulCommutative, isMulCommutative, not_commutative
-/
lemma not_isCyclic (h1 : n != 1) : ¬ IsCyclic (DihedralGroup n) := fun h => by
  by_cases h2 : n = 2
  · simpa [exponent, card, h2] using h.exponent_eq_card
  · exact not_commutative h1 h2 h.isMulCommutative

/--
lemma `isCyclic_iff` / 引理 `isCyclic_iff`

English:
lemma isCyclic_iff
  statement: IsCyclic (DihedralGroup n) ↔ n = 1 where
  proof: not_imp_not.mp not_isCyclic
  mpr h := h ▸ isCyclic_of_prime_card (p := 2) nat_card

中文:
引理 isCyclic_iff
  结论: 是循环 (Dihedral群 n) ↔ n = 1 where
  证明: not_imp_not.mp not_isCyclic
  mpr h := h ▸ isCyclic_of_prime_card (p := 2) nat_card

Depends on / 依赖: Countable, Encodable, countable, not_imp_not, not_imp_not.mp, not_isCyclic
-/
lemma isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1 where
  mp := not_imp_not.mp not_isCyclic
  mpr h := h ▸ isCyclic_of_prime_card (p := 2) nat_card

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsKleinFour (DihedralGroup 2)
  body: DihedralGroup.nat_card
  exponent_two := DihedralGroup.exponent

中文:
实例 :
  签名: 是KleinFour (Dihedral群 2)
  定义体: DihedralGroup.nat_card
  exponent_two := DihedralGroup.exponent

Depends on / 依赖: DihedralGroup, DihedralGroup.nat_card, nat_card
-/
instance : IsKleinFour (DihedralGroup 2) where
  card_four := DihedralGroup.nat_card
  exponent_two := DihedralGroup.exponent

set_option backward.isDefEq.respectTransparency false in
/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represented as
$n + n + n + n*n$) of commuting elements. -/
@[simps]
/--
Definition of `oddCommuteEquiv` / `oddCommuteEquiv` 的定义

English:
definition oddCommuteEquiv
  signature: (hn : Odd n)
  body: let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : forall a : ZMod n, a + a = 0 ↔ a = 0 := fun _ => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r _, r _⟩, _⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)]
          using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)]
          using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub]; rw [neg_eq_iff_add_eq_zero]; rw [hu]; rw [sub_eq_zero] at h
        rw [Subtype.ext_iff]; rw [Prod.ext_iff]; rw [sr.injEq]; rw [sr.injEq]; rw [h]; rw [and_self]; rw [← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl _ => rfl
      | .inr (.inl _) => rfl
      | .inr (.inr (.inl k)) =>
congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨_, _⟩)) => rfl }

中文:
定义 oddCommuteEquiv
  签名: (hn : Odd n)
  定义体: let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : forall a : ZMod n, a + a = 0 ↔ a = 0 := fun _ => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r _, r _⟩, _⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)]
          using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)]
          using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub]; rw [neg_eq_iff_add_eq_zero]; rw [hu]; rw [sub_eq_zero] at h
        rw [Subtype.ext_iff]; rw [Prod.ext_iff]; rw [sr.injEq]; rw [sr.injEq]; rw [h]; rw [and_self]; rw [← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl _ => rfl
      | .inr (.inl _) => rfl
      | .inr (.inr (.inl k)) =>
congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨_, _⟩)) => rfl }

Depends on / 依赖: Nat.prime_two.coprime_iff_not_dvd.mpr, Sum.inl, Sum.inr, ZMod.add_self_eq_zero_iff_eq_zero, ZMod.unitOfCoprime, add_self_eq_zero_iff_eq_zero, add_zero, coprime_iff_not_dvd, hn.not_two_dvd_nat, invFun, not_two_dvd_nat, prime_two, sub_zero, unitOfCoprime
-/
def oddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃
    ZMod n oplus ZMod n oplus ZMod n oplus ZMod n × ZMod n :=
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : forall a : ZMod n, a + a = 0 ↔ a = 0 := fun _ => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r _, r _⟩, _⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)]
          using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [-r_zero, sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)]
          using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub]; rw [neg_eq_iff_add_eq_zero]; rw [hu]; rw [sub_eq_zero] at h
        rw [Subtype.ext_iff]; rw [Prod.ext_iff]; rw [sr.injEq]; rw [sr.injEq]; rw [h]; rw [and_self]; rw [← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl _ => rfl
      | .inr (.inl _) => rfl
      | .inr (.inr (.inl k)) =>
congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨_, _⟩)) => rfl }

/--
lemma `card_commute_odd` / 引理 `card_commute_odd`

English:
lemma card_commute_odd
  given: (hn : Odd n)
  proof: by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (oddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

中文:
引理 card_commute_odd
  条件: (hn : Odd n)
  证明: by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (oddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

Depends on / 依赖: Nat.card_congr, Nat.card_prod, Nat.card_sum, Nat.card_zmod, NeZero, card_congr, card_prod, card_sum, card_zmod, hn.pos.ne, oddCommuteEquiv, simp_rw
-/
lemma card_commute_odd (hn : Odd n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (oddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

/--
lemma `card_conjClasses_odd` / 引理 `card_conjClasses_odd`

English:
lemma card_conjClasses_odd
  given: (hn : Odd n)
  proof: by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos]; rw [← card_commute_odd hn]; rw [mul_comm]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [nat_card]; rw [Nat.mul_div_left _ (mul_pos two_pos hn.pos)]

中文:
引理 card_conjClasses_odd
  条件: (hn : Odd n)
  证明: by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos]; rw [← card_commute_odd hn]; rw [mul_comm]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [nat_card]; rw [Nat.mul_div_left _ (mul_pos two_pos hn.pos)]

Depends on / 依赖: Nat.mul_div_left, Nat.mul_div_mul_left, card_comm_eq_card_conjClasses_mul_card, card_commute_odd, hn.pos, mul_comm, mul_div_left, mul_div_mul_left, mul_pos, nat_card, two_pos
-/
lemma card_conjClasses_odd (hn : Odd n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 := by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos]; rw [← card_commute_odd hn]; rw [mul_comm]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [nat_card]; rw [Nat.mul_div_left _ (mul_pos two_pos hn.pos)]

/--
theorem `center_eq_bot_of_odd_ne_one` / 定理 `center_eq_bot_of_odd_ne_one`

English:
theorem center_eq_bot_of_odd_ne_one
  given: (hodd : Odd n) (hne1 : n != 1)
  proof: by
  simp only [Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff]
  rintro (i | i) h
  · have heq := sr.inj (h (sr i))
    simp_all
  · have heq := sr.inj (h (r 1))
    have : Fact (1 < n) := ⟨by grind⟩
    simp [sub_eq_iff_eq_add, add_assoc, ZMod.add_self_eq_zero_iff_eq_zero hodd] at heq

中文:
定理 center_eq_bot_of_odd_ne_one
  条件: (hodd : Odd n) (hne1 : n != 1)
  证明: by
  simp only [Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff]
  rintro (i | i) h
  · have heq := sr.inj (h (sr i))
    simp_all
  · have heq := sr.inj (h (r 1))
    have : Fact (1 < n) := ⟨by grind⟩
    simp [sub_eq_iff_eq_add, add_assoc, ZMod.add_self_eq_zero_iff_eq_zero hodd] at heq

Depends on / 依赖: Subgroup, Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff, ZMod.add_self_eq_zero_iff_eq_zero, add_assoc, add_self_eq_zero_iff_eq_zero, eq_bot_iff_forall, mem_center_iff, sr.inj, sub_eq_iff_eq_add
-/
theorem center_eq_bot_of_odd_ne_one (hodd : Odd n) (hne1 : n != 1) :
    Subgroup.center (DihedralGroup n) = ⊥ := by
  simp only [Subgroup.eq_bot_iff_forall, Subgroup.mem_center_iff]
  rintro (i | i) h
  · have heq := sr.inj (h (sr i))
    simp_all
  · have heq := sr.inj (h (r 1))
    have : Fact (1 < n) := ⟨by grind⟩
    simp [sub_eq_iff_eq_add, add_assoc, ZMod.add_self_eq_zero_iff_eq_zero hodd] at heq

end DihedralGroup
