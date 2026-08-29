/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`Set.Icc`, `Set.Ioc`, `Set.Ioc`, and `Set.Ioo`) from `0` to `1`.
Note: Instances for the interval `Ici 0` are dealt with in
`Mathlib/Algebra/Order/Nonneg/Basic.lean`.

## Main definitions

The strongest typeclass provided on each interval is:
* `Set.Icc.commMonoidWithZero`
* `Set.Icc.instIsCancelMulZero`
* `Set.Ico.commSemigroup`
* `Set.Ioc.commMonoid`
* `Set.Ioo.commSemigroup`

## TODO

* algebraic instances for intervals -1 to 1
* algebraic instances for `Ici 1`
* algebraic instances for `(Ioo (-1) 1)ᶜ`
* provide `distribNeg` instances where applicable
* prove versions of `mul_le_{left,right}` for other intervals
* prove versions of the lemmas in `Topology/UnitInterval` with `ℝ` generalized to
  some arbitrary ordered semiring
-/

@[expose] public section

assert_not_exists RelIso

open Set

variable {R : Type*}

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-! ### Instances for `↥(Set.Icc 0 1)` -/


namespace Set.Icc

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (Icc (0 : R) 1) where zero
  body: ⟨0, left_mem_Icc.2 zero_le_one⟩

中文:
实例 instZero
  签名: : Zero (Icc (0 : R) 1) where zero
  定义体: ⟨0, left_mem_Icc.2 zero_le_one⟩

Depends on / 依赖: left_mem_Icc, zero_le_one
-/
instance instZero : Zero (Icc (0 : R) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (Icc (0 : R) 1) where one
  body: ⟨1, right_mem_Icc.2 zero_le_one⟩

中文:
实例 instOne
  签名: : One (Icc (0 : R) 1) where one
  定义体: ⟨1, right_mem_Icc.2 zero_le_one⟩

Depends on / 依赖: right_mem_Icc, zero_le_one
-/
instance instOne : One (Icc (0 : R) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩

/--
Instance `instZeroLEOneClass` / 实例 `instZeroLEOneClass`

English:
instance instZeroLEOneClass
  signature: : ZeroLEOneClass (Icc (0 : R) 1)
  body: ⟨Subtype.coe_le_coe.mp zero_le_one⟩

@[simp, norm_cast]

中文:
实例 instZeroLEOneClass
  签名: : ZeroLEOneClass (Icc (0 : R) 1)
  定义体: ⟨Subtype.coe_le_coe.mp zero_le_one⟩

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, zero_le_one
-/
instance instZeroLEOneClass : ZeroLEOneClass (Icc (0 : R) 1) := ⟨Subtype.coe_le_coe.mp zero_le_one⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : Icc (0 : R) 1) = (0 : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ↑(0 : Icc (0 : R) 1) = (0 : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ↑(0 : Icc (0 : R) 1) = (0 : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : Icc (0 : R) 1) = (1 : R)
  proof: rfl

@[simp, grind =]

中文:
定理 coe_one
  结论: ↑(1 : Icc (0 : R) 1) = (1 : R)
  证明: rfl

@[simp, grind =]
-/
theorem coe_one : ↑(1 : Icc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: (h : (0 : R) in Icc (0 : R) 1)
  statement: (⟨0, h⟩ : Icc (0 : R) 1) = 0
  proof: rfl

@[simp, grind =]

中文:
定理 mk_zero
  条件: (h : (0 : R) in Icc (0 : R) 1)
  结论: (⟨0, h⟩ : Icc (0 : R) 1) = 0
  证明: rfl

@[simp, grind =]
-/
theorem mk_zero (h : (0 : R) in Icc (0 : R) 1) : (⟨0, h⟩ : Icc (0 : R) 1) = 0 :=
  rfl

@[simp, grind =]
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: (h : (1 : R) in Icc (0 : R) 1)
  statement: (⟨1, h⟩ : Icc (0 : R) 1) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_one
  条件: (h : (1 : R) in Icc (0 : R) 1)
  结论: (⟨1, h⟩ : Icc (0 : R) 1) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_one (h : (1 : R) in Icc (0 : R) 1) : (⟨1, h⟩ : Icc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : Icc (0 : R) 1}
  statement: (x : R) = 0 ↔ x = 0
  proof: by
  symm
  exact Subtype.ext_iff

中文:
定理 coe_eq_zero
  条件: {x : Icc (0 : R) 1}
  结论: (x : R) = 0 ↔ x = 0
  证明: by
  symm
  exact Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: {x : Icc (0 : R) 1}
  statement: (x : R) != 0 ↔ x != 0
  proof: not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]

中文:
定理 coe_ne_zero
  条件: {x : Icc (0 : R) 1}
  结论: (x : R) != 0 ↔ x != 0
  证明: not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]

Depends on / 依赖: coe_eq_zero, not_iff_not, not_iff_not.mpr
-/
theorem coe_ne_zero {x : Icc (0 : R) 1} : (x : R) != 0 ↔ x != 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : Icc (0 : R) 1}
  statement: (x : R) = 1 ↔ x = 1
  proof: by
  symm
  exact Subtype.ext_iff

中文:
定理 coe_eq_one
  条件: {x : Icc (0 : R) 1}
  结论: (x : R) = 1 ↔ x = 1
  证明: by
  symm
  exact Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {x : Icc (0 : R) 1}
  statement: (x : R) != 1 ↔ x != 1
  proof: not_iff_not.mpr coe_eq_one

omit [IsOrderedRing R] in

中文:
定理 coe_ne_one
  条件: {x : Icc (0 : R) 1}
  结论: (x : R) != 1 ↔ x != 1
  证明: not_iff_not.mpr coe_eq_one

omit [IsOrderedRing R] in

Depends on / 依赖: coe_eq_one, not_iff_not, not_iff_not.mpr
-/
theorem coe_ne_one {x : Icc (0 : R) 1} : (x : R) != 1 ↔ x != 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsOrderedRing R] in
/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: (x : Icc (0 : R) 1)
  statement: 0 <= (x : R)
  proof: x.2.1

omit [IsOrderedRing R] in

中文:
定理 coe_nonneg
  条件: (x : Icc (0 : R) 1)
  结论: 0 <= (x : R)
  证明: x.2.1

omit [IsOrderedRing R] in
-/
theorem coe_nonneg (x : Icc (0 : R) 1) : 0 <= (x : R) :=
  x.2.1

omit [IsOrderedRing R] in
/--
theorem `coe_le_one` / 定理 `coe_le_one`

English:
theorem coe_le_one
  given: (x : Icc (0 : R) 1)
  statement: (x : R) <= 1
  proof: x.2.2

中文:
定理 coe_le_one
  条件: (x : Icc (0 : R) 1)
  结论: (x : R) <= 1
  证明: x.2.2
-/
theorem coe_le_one (x : Icc (0 : R) 1) : (x : R) <= 1 :=
  x.2.2

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: {t : Icc (0 : R) 1}
  statement: 0 <= t
  proof: t.2.1

中文:
定理 nonneg
  条件: {t : Icc (0 : R) 1}
  结论: 0 <= t
  证明: t.2.1
-/
theorem nonneg {t : Icc (0 : R) 1} : 0 <= t :=
  t.2.1

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: {t : Icc (0 : R) 1}
  statement: t <= 1
  proof: t.2.2

中文:
定理 le_one
  条件: {t : Icc (0 : R) 1}
  结论: t <= 1
  证明: t.2.2
-/
theorem le_one {t : Icc (0 : R) 1} : t <= 1 :=
  t.2.2

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Icc (0 : R) 1) where
  body: ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one₀ p.2.2 q.2.1 q.2.2⟩⟩

中文:
实例 instMul
  签名: : Mul (Icc (0 : R) 1) where
  定义体: ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one₀ p.2.2 q.2.1 q.2.2⟩⟩

Depends on / 依赖: mul_nonneg
-/
instance instMul : Mul (Icc (0 : R) 1) where
  mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one₀ p.2.2 q.2.1 q.2.2⟩⟩

/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow (Icc (0 : R) 1) Nat where
  body: ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]

中文:
实例 instPow
  签名: : Pow (Icc (0 : R) 1) 自然数 where
  定义体: ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: pow_nonneg
-/
instance instPow : Pow (Icc (0 : R) 1) Nat where
  pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Icc (0 : R) 1)
  statement: ↑(x * y) = (x * y : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : Icc (0 : R) 1)
  结论: ↑(x * y) = (x * y : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : Icc (0 : R) 1) (n : Nat)
  statement: ↑(x ^ n) = ((x : R) ^ n)
  proof: rfl

中文:
定理 coe_pow
  条件: (x : Icc (0 : R) 1) (n : 自然数)
  结论: ↑(x ^ n) = ((x : R) ^ n)
  证明: rfl
-/
theorem coe_pow (x : Icc (0 : R) 1) (n : Nat) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl

/--
theorem `mul_le_left` / 定理 `mul_le_left`

English:
theorem mul_le_left
  given: {x y : Icc (0 : R) 1}
  statement: x * y <= x
  proof: (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

中文:
定理 mul_le_left
  条件: {x y : Icc (0 : R) 1}
  结论: x * y <= x
  证明: (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_one, trans_eq
-/
theorem mul_le_left {x y : Icc (0 : R) 1} : x * y <= x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

/--
theorem `mul_le_right` / 定理 `mul_le_right`

English:
theorem mul_le_right
  given: {x y : Icc (0 : R) 1}
  statement: x * y <= y
  proof: (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

中文:
定理 mul_le_right
  条件: {x y : Icc (0 : R) 1}
  结论: x * y <= y
  证明: (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

Depends on / 依赖: mul_le_mul_of_nonneg_right, one_mul, trans_eq
-/
theorem mul_le_right {x y : Icc (0 : R) 1} : x * y <= y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: : MonoidWithZero (Icc (0 : R) 1)
  body: fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

中文:
实例 instMonoidWithZero
  签名: : MonoidWithZero (Icc (0 : R) 1)
  定义体: fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance instMonoidWithZero : MonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

中文:
实例 instCommMonoidWithZero
  签名: {R : 类型} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance instCommMonoidWithZero {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommMonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

/--
Instance `instIsCancelMulZero` / 实例 `instIsCancelMulZero`

English:
instance instIsCancelMulZero
  signature: {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
  body: @Function.Injective.isCancelMulZero _ R _ _ _ _ _ Subtype.coe_injective coe_zero coe_mul
    NoZeroDivisors.toIsCancelMulZero

中文:
实例 instIsCancelMulZero
  签名: {R : 类型} [Ring R] [PartialOrder R] [IsOrderedRing R]
  定义体: @Function.Injective.isCancelMulZero _ R _ _ _ _ _ Subtype.coe_injective coe_zero coe_mul
    NoZeroDivisors.toIsCancelMulZero

Depends on / 依赖: Function, Function.Injective.isCancelMulZero, Injective, NoZeroDivisors, NoZeroDivisors.toIsCancelMulZero, Subtype, Subtype.coe_injective, coe_injective, coe_mul, coe_zero, isCancelMulZero, toIsCancelMulZero
-/
instance instIsCancelMulZero {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [NoZeroDivisors R] :
    IsCancelMulZero (Icc (0 : R) 1) :=
  @Function.Injective.isCancelMulZero _ R _ _ _ _ _ Subtype.coe_injective coe_zero coe_mul
    NoZeroDivisors.toIsCancelMulZero

/-- The coercion from `Set.Icc 0 1` as a `MonoidWithZeroHom`. -/
@[simps]
/--
Definition of `coeMonoidWithZeroHom` / `coeMonoidWithZeroHom` 的定义

English:
definition coeMonoidWithZeroHom
  signature: : (Icc (0 : R) 1) ->*₀ R where
  body: (↑)
  map_mul' := coe_mul
  map_one' := rfl
  map_zero' := rfl

中文:
定义 coeMonoidWithZeroHom
  签名: : (Icc (0 : R) 1) ->*₀ R where
  定义体: (↑)
  map_mul' := coe_mul
  map_one' := rfl
  map_zero' := rfl
-/
def coeMonoidWithZeroHom : (Icc (0 : R) 1) ->*₀ R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl
  map_zero' := rfl

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

/--
theorem `one_sub_mem` / 定理 `one_sub_mem`

English:
theorem one_sub_mem
  given: {t : β} (ht : t in Icc (0 : β) 1)
  statement: 1 - t in Icc (0 : β) 1
  proof: by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

中文:
定理 one_sub_mem
  条件: {t : β} (ht : t in Icc (0 : β) 1)
  结论: 1 - t in Icc (0 : β) 1
  证明: by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

Depends on / 依赖: mem_Icc, sub_le_self_iff, sub_nonneg
-/
theorem one_sub_mem {t : β} (ht : t in Icc (0 : β) 1) : 1 - t in Icc (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

/--
theorem `mem_iff_one_sub_mem` / 定理 `mem_iff_one_sub_mem`

English:
theorem mem_iff_one_sub_mem
  given: {t : β}
  statement: t in Icc (0 : β) 1 ↔ 1 - t in Icc (0 : β) 1
  proof: ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

中文:
定理 mem_iff_one_sub_mem
  条件: {t : β}
  结论: t in Icc (0 : β) 1 ↔ 1 - t in Icc (0 : β) 1
  证明: ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

Depends on / 依赖: one_sub_mem, sub_sub_cancel
-/
theorem mem_iff_one_sub_mem {t : β} : t in Icc (0 : β) 1 ↔ 1 - t in Icc (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

/--
theorem `one_sub_nonneg` / 定理 `one_sub_nonneg`

English:
theorem one_sub_nonneg
  given: (x : Icc (0 : β) 1)
  statement: 0 <= 1 - (x : β)
  proof: by simpa using x.2.2

中文:
定理 one_sub_nonneg
  条件: (x : Icc (0 : β) 1)
  结论: 0 <= 1 - (x : β)
  证明: by simpa using x.2.2
-/
theorem one_sub_nonneg (x : Icc (0 : β) 1) : 0 <= 1 - (x : β) := by simpa using x.2.2

/--
theorem `one_sub_le_one` / 定理 `one_sub_le_one`

English:
theorem one_sub_le_one
  given: (x : Icc (0 : β) 1)
  statement: 1 - (x : β) <= 1
  proof: by simpa using x.2.1

中文:
定理 one_sub_le_one
  条件: (x : Icc (0 : β) 1)
  结论: 1 - (x : β) <= 1
  证明: by simpa using x.2.1
-/
theorem one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) <= 1 := by simpa using x.2.1

end Set.Icc

/-! ### Instances for `↥(Set.Ico 0 1)` -/


namespace Set.Ico

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Nontrivial R]
  body: ⟨0, by simp⟩

@[simp, norm_cast]

中文:
实例 instZero
  签名: [Nontrivial R]
  定义体: ⟨0, by simp⟩

@[simp, norm_cast]
-/
instance instZero [Nontrivial R] : Zero (Ico (0 : R) 1) where zero := ⟨0, by simp⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  given: [Nontrivial R]
  statement: ↑(0 : Ico (0 : R) 1) = (0 : R)
  proof: rfl

@[simp, grind =]

中文:
定理 coe_zero
  条件: [Nontrivial R]
  结论: ↑(0 : Ico (0 : R) 1) = (0 : R)
  证明: rfl

@[simp, grind =]
-/
theorem coe_zero [Nontrivial R] : ↑(0 : Ico (0 : R) 1) = (0 : R) :=
  rfl

@[simp, grind =]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: [Nontrivial R] (h : (0 : R) in Ico (0 : R) 1)
  statement: (⟨0, h⟩ : Ico (0 : R) 1) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_zero
  条件: [Nontrivial R] (h : (0 : R) in Ico (0 : R) 1)
  结论: (⟨0, h⟩ : Ico (0 : R) 1) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_zero [Nontrivial R] (h : (0 : R) in Ico (0 : R) 1) : (⟨0, h⟩ : Ico (0 : R) 1) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: [Nontrivial R] {x : Ico (0 : R) 1}
  statement: (x : R) = 0 ↔ x = 0
  proof: by
  symm
  exact Subtype.ext_iff

中文:
定理 coe_eq_zero
  条件: [Nontrivial R] {x : Ico (0 : R) 1}
  结论: (x : R) = 0 ↔ x = 0
  证明: by
  symm
  exact Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem coe_eq_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: [Nontrivial R] {x : Ico (0 : R) 1}
  statement: (x : R) != 0 ↔ x != 0
  proof: not_iff_not.mpr coe_eq_zero

omit [IsOrderedRing R] in

中文:
定理 coe_ne_zero
  条件: [Nontrivial R] {x : Ico (0 : R) 1}
  结论: (x : R) != 0 ↔ x != 0
  证明: not_iff_not.mpr coe_eq_zero

omit [IsOrderedRing R] in

Depends on / 依赖: coe_eq_zero, not_iff_not, not_iff_not.mpr
-/
theorem coe_ne_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) != 0 ↔ x != 0 :=
  not_iff_not.mpr coe_eq_zero

omit [IsOrderedRing R] in
/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: (x : Ico (0 : R) 1)
  statement: 0 <= (x : R)
  proof: x.2.1

omit [IsOrderedRing R] in

中文:
定理 coe_nonneg
  条件: (x : Ico (0 : R) 1)
  结论: 0 <= (x : R)
  证明: x.2.1

omit [IsOrderedRing R] in
-/
theorem coe_nonneg (x : Ico (0 : R) 1) : 0 <= (x : R) :=
  x.2.1

omit [IsOrderedRing R] in
/--
theorem `coe_lt_one` / 定理 `coe_lt_one`

English:
theorem coe_lt_one
  given: (x : Ico (0 : R) 1)
  statement: (x : R) < 1
  proof: x.2.2

中文:
定理 coe_lt_one
  条件: (x : Ico (0 : R) 1)
  结论: (x : R) < 1
  证明: x.2.2
-/
theorem coe_lt_one (x : Ico (0 : R) 1) : (x : R) < 1 :=
  x.2.2

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: [Nontrivial R] {t : Ico (0 : R) 1}
  statement: 0 <= t
  proof: t.2.1

中文:
定理 nonneg
  条件: [Nontrivial R] {t : Ico (0 : R) 1}
  结论: 0 <= t
  证明: t.2.1
-/
theorem nonneg [Nontrivial R] {t : Ico (0 : R) 1} : 0 <= t :=
  t.2.1

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Ico (0 : R) 1) where
  body: ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]

中文:
实例 instMul
  签名: : Mul (Ico (0 : R) 1) where
  定义体: ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: mul_lt_one_of_nonneg_of_lt_one_right, mul_nonneg
-/
instance instMul : Mul (Ico (0 : R) 1) where
  mul p q :=
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Ico (0 : R) 1)
  statement: ↑(x * y) = (x * y : R)
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : Ico (0 : R) 1)
  结论: ↑(x * y) = (x * y : R)
  证明: rfl
-/
theorem coe_mul (x y : Ico (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: : Semigroup (Ico (0 : R) 1)
  body: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

中文:
实例 instSemigroup
  签名: : Semigroup (Ico (0 : R) 1)
  定义体: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instSemigroup : Semigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

中文:
实例 instCommSemigroup
  签名: {R : 类型} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommSemigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ico 0 1` as a `MulHom`. -/
@[simps]
/--
Definition of `coeMulHom` / `coeMulHom` 的定义

English:
definition coeMulHom
  signature: : (Ico (0 : R) 1) ->ₙ* R where
  body: (↑)
  map_mul' := coe_mul

中文:
定义 coeMulHom
  签名: : (Ico (0 : R) 1) ->ₙ* R where
  定义体: (↑)
  map_mul' := coe_mul
-/
def coeMulHom : (Ico (0 : R) 1) ->ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

end Set.Ico

end OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-! ### Instances for `↥(Set.Ioc 0 1)` -/


namespace Set.Ioc

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (Ioc (0 : R) 1) where one
  body: ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]

中文:
实例 instOne
  签名: : One (Ioc (0 : R) 1) where one
  定义体: ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]

Depends on / 依赖: le_refl, zero_lt_one
-/
instance instOne : One (Ioc (0 : R) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : Ioc (0 : R) 1) = (1 : R)
  proof: rfl

@[simp, grind =]

中文:
定理 coe_one
  结论: ↑(1 : Ioc (0 : R) 1) = (1 : R)
  证明: rfl

@[simp, grind =]
-/
theorem coe_one : ↑(1 : Ioc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: (h : (1 : R) in Ioc (0 : R) 1)
  statement: (⟨1, h⟩ : Ioc (0 : R) 1) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_one
  条件: (h : (1 : R) in Ioc (0 : R) 1)
  结论: (⟨1, h⟩ : Ioc (0 : R) 1) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_one (h : (1 : R) in Ioc (0 : R) 1) : (⟨1, h⟩ : Ioc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : Ioc (0 : R) 1}
  statement: (x : R) = 1 ↔ x = 1
  proof: by
  symm
  exact Subtype.ext_iff

中文:
定理 coe_eq_one
  条件: {x : Ioc (0 : R) 1}
  结论: (x : R) = 1 ↔ x = 1
  证明: by
  symm
  exact Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem coe_eq_one {x : Ioc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {x : Ioc (0 : R) 1}
  statement: (x : R) != 1 ↔ x != 1
  proof: not_iff_not.mpr coe_eq_one

omit [IsStrictOrderedRing R] in

中文:
定理 coe_ne_one
  条件: {x : Ioc (0 : R) 1}
  结论: (x : R) != 1 ↔ x != 1
  证明: not_iff_not.mpr coe_eq_one

omit [IsStrictOrderedRing R] in

Depends on / 依赖: coe_eq_one, not_iff_not, not_iff_not.mpr
-/
theorem coe_ne_one {x : Ioc (0 : R) 1} : (x : R) != 1 ↔ x != 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsStrictOrderedRing R] in
/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  given: (x : Ioc (0 : R) 1)
  statement: 0 < (x : R)
  proof: x.2.1

omit [IsStrictOrderedRing R] in

中文:
定理 coe_pos
  条件: (x : Ioc (0 : R) 1)
  结论: 0 < (x : R)
  证明: x.2.1

omit [IsStrictOrderedRing R] in
-/
theorem coe_pos (x : Ioc (0 : R) 1) : 0 < (x : R) :=
  x.2.1

omit [IsStrictOrderedRing R] in
/--
theorem `coe_le_one` / 定理 `coe_le_one`

English:
theorem coe_le_one
  given: (x : Ioc (0 : R) 1)
  statement: (x : R) <= 1
  proof: x.2.2

中文:
定理 coe_le_one
  条件: (x : Ioc (0 : R) 1)
  结论: (x : R) <= 1
  证明: x.2.2
-/
theorem coe_le_one (x : Ioc (0 : R) 1) : (x : R) <= 1 :=
  x.2.2

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: {t : Ioc (0 : R) 1}
  statement: t <= 1
  proof: t.2.2

中文:
定理 le_one
  条件: {t : Ioc (0 : R) 1}
  结论: t <= 1
  证明: t.2.2
-/
theorem le_one {t : Ioc (0 : R) 1} : t <= 1 :=
  t.2.2

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Ioc (0 : R) 1) where
  body: ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one₀ p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩

中文:
实例 instMul
  签名: : Mul (Ioc (0 : R) 1) where
  定义体: ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one₀ p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩

Depends on / 依赖: le_of_lt, mul_pos
-/
instance instMul : Mul (Ioc (0 : R) 1) where
  mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one₀ p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩

/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: : Pow (Ioc (0 : R) 1) Nat where
  body: ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]

中文:
实例 instPow
  签名: : Pow (Ioc (0 : R) 1) 自然数 where
  定义体: ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: le_of_lt, pow_pos
-/
instance instPow : Pow (Ioc (0 : R) 1) Nat where
  pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Ioc (0 : R) 1)
  statement: ↑(x * y) = (x * y : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : Ioc (0 : R) 1)
  结论: ↑(x * y) = (x * y : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (x y : Ioc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : Ioc (0 : R) 1) (n : Nat)
  statement: ↑(x ^ n) = ((x : R) ^ n)
  proof: rfl

中文:
定理 coe_pow
  条件: (x : Ioc (0 : R) 1) (n : 自然数)
  结论: ↑(x ^ n) = ((x : R) ^ n)
  证明: rfl
-/
theorem coe_pow (x : Ioc (0 : R) 1) (n : Nat) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl

/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: : Semigroup (Ioc (0 : R) 1)
  body: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

中文:
实例 instSemigroup
  签名: : Semigroup (Ioc (0 : R) 1)
  定义体: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instSemigroup : Semigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (Ioc (0 : R) 1)
  body: fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

中文:
实例 instMonoid
  签名: : Monoid (Ioc (0 : R) 1)
  定义体: fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance instMonoid : Monoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

中文:
实例 instCommSemigroup
  签名: {R : 类型} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow

中文:
实例 instCommMonoid
  签名: {R : 类型} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance instCommMonoid {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow

/--
Instance `instCancelMonoid` / 实例 `instCancelMonoid`

English:
instance instCancelMonoid
  signature: {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: { Set.Ioc.instMonoid with
    mul_left_cancel := fun a _ _ h =>
Subtype.ext mul_left_cancel₀ a.prop.1.ne' (congr_arg Subtype.val h :)
    mul_right_cancel := fun b _ _ h =>
Subtype.ext mul_right_cancel₀ b.prop.1.ne' (congr_arg Subtype.val h :) }

中文:
实例 instCancelMonoid
  签名: {R : 类型} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: { Set.Ioc.instMonoid with
    mul_left_cancel := fun a _ _ h =>
Subtype.ext mul_left_cancel₀ a.prop.1.ne' (congr_arg Subtype.val h :)
    mul_right_cancel := fun b _ _ h =>
Subtype.ext mul_right_cancel₀ b.prop.1.ne' (congr_arg Subtype.val h :) }

Depends on / 依赖: Set.Ioc.instMonoid, Subtype, Subtype.ext, Subtype.val, a.prop, b.prop, congr_arg, instMonoid, mul_left_cancel, mul_right_cancel
-/
instance instCancelMonoid {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [IsDomain R] : CancelMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instMonoid with
    mul_left_cancel := fun a _ _ h =>
Subtype.ext mul_left_cancel₀ a.prop.1.ne' (congr_arg Subtype.val h :)
    mul_right_cancel := fun b _ _ h =>
Subtype.ext mul_right_cancel₀ b.prop.1.ne' (congr_arg Subtype.val h :) }

/--
Instance `instCancelCommMonoid` / 实例 `instCancelCommMonoid`

English:
instance instCancelCommMonoid
  signature: {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  body: { Set.Ioc.instCommMonoid, Set.Ioc.instCancelMonoid with }

中文:
实例 instCancelCommMonoid
  签名: {R : 类型} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: { Set.Ioc.instCommMonoid, Set.Ioc.instCancelMonoid with }

Depends on / 依赖: Set.Ioc.instCancelMonoid, Set.Ioc.instCommMonoid, instCancelMonoid, instCommMonoid
-/
instance instCancelCommMonoid {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
    [IsDomain R] :
    CancelCommMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instCommMonoid, Set.Ioc.instCancelMonoid with }

/-- The coercion from `Set.Ioc 0 1` as a `MonoidHom`. -/
@[simps]
/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : (Ioc (0 : R) 1) ->* R where
  body: (↑)
  map_mul' := coe_mul
  map_one' := rfl

中文:
定义 coeMonoidHom
  签名: : (Ioc (0 : R) 1) ->* R where
  定义体: (↑)
  map_mul' := coe_mul
  map_one' := rfl
-/
def coeMonoidHom : (Ioc (0 : R) 1) ->* R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl

end Set.Ioc

/-! ### Instances for `↥(Set.Ioo 0 1)` -/


namespace Set.Ioo

omit [IsStrictOrderedRing R] in
/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  given: (x : Ioo (0 : R) 1)
  statement: 0 < (x : R)
  proof: x.2.1

omit [IsStrictOrderedRing R] in

中文:
定理 pos
  条件: (x : Ioo (0 : R) 1)
  结论: 0 < (x : R)
  证明: x.2.1

omit [IsStrictOrderedRing R] in
-/
theorem pos (x : Ioo (0 : R) 1) : 0 < (x : R) :=
  x.2.1

omit [IsStrictOrderedRing R] in
/--
theorem `lt_one` / 定理 `lt_one`

English:
theorem lt_one
  given: (x : Ioo (0 : R) 1)
  statement: (x : R) < 1
  proof: x.2.2

中文:
定理 lt_one
  条件: (x : Ioo (0 : R) 1)
  结论: (x : R) < 1
  证明: x.2.2
-/
theorem lt_one (x : Ioo (0 : R) 1) : (x : R) < 1 :=
  x.2.2

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (Ioo (0 : R) 1) where
  body: ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]

中文:
实例 instMul
  签名: : Mul (Ioo (0 : R) 1) where
  定义体: ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: mul_lt_one_of_nonneg_of_lt_one_right, mul_pos
-/
instance instMul : Mul (Ioo (0 : R) 1) where
  mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Ioo (0 : R) 1)
  statement: ↑(x * y) = (x * y : R)
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : Ioo (0 : R) 1)
  结论: ↑(x * y) = (x * y : R)
  证明: rfl
-/
theorem coe_mul (x y : Ioo (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: : Semigroup (Ioo (0 : R) 1)
  body: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

中文:
实例 instSemigroup
  签名: : Semigroup (Ioo (0 : R) 1)
  定义体: fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instSemigroup : Semigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

中文:
实例 instCommSemigroup
  签名: {R : 类型} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

Depends on / 依赖: fast_instance
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ioo 0 1` as a `MulHom`. -/
@[simps]
/--
Definition of `coeMulHom` / `coeMulHom` 的定义

English:
definition coeMulHom
  signature: : (Ioo (0 : R) 1) ->ₙ* R where
  body: (↑)
  map_mul' := coe_mul

中文:
定义 coeMulHom
  签名: : (Ioo (0 : R) 1) ->ₙ* R where
  定义体: (↑)
  map_mul' := coe_mul
-/
def coeMulHom : (Ioo (0 : R) 1) ->ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]

/--
theorem `one_sub_mem` / 定理 `one_sub_mem`

English:
theorem one_sub_mem
  given: {t : β} (ht : t in Ioo (0 : β) 1)
  statement: 1 - t in Ioo (0 : β) 1
  proof: by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]

中文:
定理 one_sub_mem
  条件: {t : β} (ht : t in Ioo (0 : β) 1)
  结论: 1 - t in Ioo (0 : β) 1
  证明: by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]

Depends on / 依赖: and_self, mem_Ioo, sub_lt_self_iff, sub_pos
-/
theorem one_sub_mem {t : β} (ht : t in Ioo (0 : β) 1) : 1 - t in Ioo (0 : β) 1 := by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]

/--
theorem `mem_iff_one_sub_mem` / 定理 `mem_iff_one_sub_mem`

English:
theorem mem_iff_one_sub_mem
  given: {t : β}
  statement: t in Ioo (0 : β) 1 ↔ 1 - t in Ioo (0 : β) 1
  proof: ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

中文:
定理 mem_iff_one_sub_mem
  条件: {t : β}
  结论: t in Ioo (0 : β) 1 ↔ 1 - t in Ioo (0 : β) 1
  证明: ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

Depends on / 依赖: one_sub_mem, sub_sub_cancel
-/
theorem mem_iff_one_sub_mem {t : β} : t in Ioo (0 : β) 1 ↔ 1 - t in Ioo (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

/--
theorem `one_minus_pos` / 定理 `one_minus_pos`

English:
theorem one_minus_pos
  given: (x : Ioo (0 : β) 1)
  statement: 0 < 1 - (x : β)
  proof: by simpa using x.2.2

中文:
定理 one_minus_pos
  条件: (x : Ioo (0 : β) 1)
  结论: 0 < 1 - (x : β)
  证明: by simpa using x.2.2
-/
theorem one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2

/--
theorem `one_minus_lt_one` / 定理 `one_minus_lt_one`

English:
theorem one_minus_lt_one
  given: (x : Ioo (0 : β) 1)
  statement: 1 - (x : β) < 1
  proof: by simpa using x.2.1

中文:
定理 one_minus_lt_one
  条件: (x : Ioo (0 : β) 1)
  结论: 1 - (x : β) < 1
  证明: by simpa using x.2.1
-/
theorem one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

end Set.Ioo
