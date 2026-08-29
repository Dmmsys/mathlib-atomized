/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Basic

/-!
# The integers are a ring

This file contains the commutative ring instance on `ℤ`.

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing Int where
  body: instAddCommGroup
  __ := instCommSemigroup
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp
  npow_succ _ _ := by simp [Int.pow_succ]
  nat

中文:
实例 instCommRing
  签名: : CommRing 整数 where
  定义体: instAddCommGroup
  __ := instCommSemigroup
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp
  npow_succ _ _ := by simp [Int.pow_succ]
  nat

Depends on / 依赖: instAddCommGroup
-/
instance instCommRing : CommRing Int where
  __ := instAddCommGroup
  __ := instCommSemigroup
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp
  npow_succ _ _ := by simp [Int.pow_succ]
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCancelMulZero Int
  body: (mul_eq_mul_left_iff ha).1
  mul_right_cancel_of_ne_zero ha _ _ := (mul_eq_mul_right_iff ha).1

中文:
实例 :
  签名: IsCancelMulZero 整数
  定义体: (mul_eq_mul_left_iff ha).1
  mul_right_cancel_of_ne_zero ha _ _ := (mul_eq_mul_right_iff ha).1

Depends on / 依赖: mul_eq_mul_left_iff
-/
instance : IsCancelMulZero Int where
  mul_left_cancel_of_ne_zero ha _ _ := (mul_eq_mul_left_iff ha).1
  mul_right_cancel_of_ne_zero ha _ _ := (mul_eq_mul_right_iff ha).1

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: : IsDomain Int where

中文:
实例 instIsDomain
  签名: : IsDomain 整数 where
-/
instance instIsDomain : IsDomain Int where

/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Int where cast_injective _ _
  body: ofNat.inj

中文:
实例 instCharZero
  签名: : CharZero 整数 where cast_injective _ _
  定义体: ofNat.inj

Depends on / 依赖: ofNat.inj
-/
instance instCharZero : CharZero Int where cast_injective _ _ := ofNat.inj

/--
Instance `instMulDivCancelClass` / 实例 `instMulDivCancelClass`

English:
instance instMulDivCancelClass
  signature: : MulDivCancelClass Int where mul_div_cancel _ _
  body: mul_ediv_cancel _

@[simp, norm_cast]

中文:
实例 instMulDivCancelClass
  签名: : MulDivCancelClass 整数 where mul_div_cancel _ _
  定义体: mul_ediv_cancel _

@[simp, norm_cast]

Depends on / 依赖: mul_ediv_cancel
-/
instance instMulDivCancelClass : MulDivCancelClass Int where mul_div_cancel _ _ := mul_ediv_cancel _

@[simp, norm_cast]
/--
lemma `cast_mul` / 引理 `cast_mul`

English:
lemma cast_mul
  given: {α : Type*} [NonAssocRing α]
  statement: forall m n, ((m * n : Int) : α) = m * n
  proof: fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]

中文:
引理 cast_mul
  条件: {α : 类型} [NonAssocRing α]
  结论: 对任意 m n, ((m * n : 整数) : α) = m * n
  证明: fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]

Depends on / 依赖: Int.eq_nat_or_neg, add_mul, eq_nat_or_neg, isLocallyNoetherian_of_isOpenImmersion
-/
lemma cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * n : Int) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]

/--
lemma `cast_mul_eq_zsmul_cast` / 引理 `cast_mul_eq_zsmul_cast`

English:
lemma cast_mul_eq_zsmul_cast
  given: {α : Type*} [AddGroupWithOne α]
  proof: fun m => Int.induction_on m (by simp) (fun _ ih => by simp [add_mul, add_zsmul, ih]) fun _ ih => by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]

中文:
引理 cast_mul_eq_zsmul_cast
  条件: {α : 类型} [AddGroupWithOne α]
  证明: fun m => Int.induction_on m (by simp) (fun _ ih => by simp [add_mul, add_zsmul, ih]) fun _ ih => by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]

Depends on / 依赖: Int.induction_on, add_mul, add_zsmul, cast_sub, forall_const, induction_on, isLocallyNoetherian_of_isOpenImmersion, one_mul, one_zsmul, sub_eq_add_neg, sub_mul, sub_zsmul
-/
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddGroupWithOne α] :
    forall m n : Int, ↑(m * n) = m • (n : α) :=
  fun m => Int.induction_on m (by simp) (fun _ ih => by simp [add_mul, add_zsmul, ih]) fun _ ih => by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]

/--
lemma `cast_pow` / 引理 `cast_pow`

English:
lemma cast_pow
  given: {R : Type*} [Ring R] (n : Int) (m : Nat)
  proof: by
  induction m <;> simp [_root_.pow_succ, *]

中文:
引理 cast_pow
  条件: {R : 类型} [Ring R] (n : 整数) (m : 自然数)
  证明: by
  induction m <;> simp [_root_.pow_succ, *]
-/
@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : Int) (m : Nat) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction m <;> simp [_root_.pow_succ, *]

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

set_option linter.style.whitespace false -- manual alignment is not recognised

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring Int
  body: inferInstance

中文:
实例 instCommSemiring
  签名: : CommSemiring 整数
  定义体: inferInstance

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.instNoetherianSpace, convert, instNoetherianSpace
-/
instance instCommSemiring : CommSemiring Int := inferInstance
/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring Int
  body: inferInstance

中文:
实例 instSemiring
  签名: : Semiring 整数
  定义体: inferInstance
-/
instance instSemiring : Semiring Int := inferInstance
/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring Int
  body: inferInstance

中文:
实例 instRing
  签名: : Ring 整数
  定义体: inferInstance
-/
instance instRing : Ring Int := inferInstance
/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: : Distrib Int
  body: inferInstance

中文:
实例 instDistrib
  签名: : Distrib 整数
  定义体: inferInstance

Depends on / 依赖: Scheme, commRingCatIsoToRingEquiv, isAffineOpen_top, isLocallyNoetherian_of_affine_cover, isNoetherianRing_of_ringEquiv, symm.commRingCatIsoToRingEquiv
-/
instance instDistrib : Distrib Int := inferInstance

set_option linter.style.whitespace true

end Int
