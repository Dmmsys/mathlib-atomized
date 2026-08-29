/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.GrindInstances -- shake: keep (used in `example` only)
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Ring.Nat

/-!
# Definition of `ZMod n` + basic results.

This file provides the basic details of `ZMod n`, including its commutative ring structure.

## Implementation details

This used to be inlined into `Data.ZMod.Basic`. This file imports `CharP.Lemmas`, which is an
issue; all `CharP` instances create an `Algebra (ZMod p) R` instance; however, this instance may
not be definitionally equal to other `Algebra` instances (for example, `GaloisField` also has an
`Algebra` instance as it is defined as a `SplittingField`). The way to fix this is to use the
forgetful inheritance pattern, and make `CharP` carry the data of what the `smul` should be (so
for example, the `smul` on the `GaloisField` `CharP` instance should be equal to the `smul` from
its `SplittingField` structure); there is only one possible `ZMod p` algebra for any `p`, so this
is not an issue mathematically. For this to be possible, however, we need `CharP.Lemmas` to be
able to import some part of `ZMod`.

-/

@[expose] public section


namespace Fin

/-!
## Ring structure on `Fin n`

We define a commutative ring structure on `Fin n`.
Afterwards, when we define `ZMod n` in terms of `Fin n`, we use these definitions
to register the ring structure on `ZMod n` as type class instance.
-/


open Nat.ModEq Int

open scoped Fin.IntCast Fin.NatCast

/--
theorem `val_intCast` / 定理 `val_intCast`

English:
theorem val_intCast
  given: {n : Nat} [NeZero n] (x : Int)
  proof: by
  rw [Fin.intCast_def']
  split <;> rename_i h
  · simp [Int.emod_natAbs_of_nonneg h]
  · simp only [Fin.val_neg, Fin.natCast_eq_zero, Fin.val_natCast]
    split <;> rename_i h
    · rw [← Int.natCast_dvd] at h
      rw [Int.emod_eq_zero_of_dvd h]; rw [Int.toNat_zero]
    · rw [Int.emod_natAbs_of_neg (by lia) (NeZero.ne n),
        if_neg (by rwa [← Int.natCast_dvd] at h)]
      have : x % n < n := Int.emod_lt_of_pos x (by have := NeZero.ne n; lia)
      lia

中文:
定理 val_intCast
  条件: {n : 自然数} [NeZero n] (x : 整数)
  证明: by
  rw [Fin.intCast_def']
  split <;> rename_i h
  · simp [Int.emod_natAbs_of_nonneg h]
  · simp only [Fin.val_neg, Fin.natCast_eq_zero, Fin.val_natCast]
    split <;> rename_i h
    · rw [← Int.natCast_dvd] at h
      rw [Int.emod_eq_zero_of_dvd h]; rw [Int.toNat_zero]
    · rw [Int.emod_natAbs_of_neg (by lia) (NeZero.ne n),
        if_neg (by rwa [← Int.natCast_dvd] at h)]
      have : x % n < n := Int.emod_lt_of_pos x (by have := NeZero.ne n; lia)
      lia

Depends on / 依赖: mapsTo_smul_orbit, restrict
-/
@[simp] theorem val_intCast {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n).val = (x % n).toNat := by
  rw [Fin.intCast_def']
  split <;> rename_i h
  · simp [Int.emod_natAbs_of_nonneg h]
  · simp only [Fin.val_neg, Fin.natCast_eq_zero, Fin.val_natCast]
    split <;> rename_i h
    · rw [← Int.natCast_dvd] at h
      rw [Int.emod_eq_zero_of_dvd h]; rw [Int.toNat_zero]
    · rw [Int.emod_natAbs_of_neg (by lia) (NeZero.ne n),
        if_neg (by rwa [← Int.natCast_dvd] at h)]
      have : x % n < n := Int.emod_lt_of_pos x (by have := NeZero.ne n; lia)
      lia

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: (n : Nat)
  body: fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
      calc
        a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
        _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
        _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
  mul_comm := Fin.mul_comm

中文:
实例 instCommSemigroup
  签名: (n : 自然数)
  定义体: fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
      calc
        a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
        _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
        _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
  mul_comm := Fin.mul_comm
-/
instance instCommSemigroup (n : Nat) : CommSemigroup (Fin n) where
  mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
      calc
        a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
        _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
        _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
  mul_comm := Fin.mul_comm

-- Shortcut instances to replace the power operation on `Fin` with a more efficient one
instance (n : Nat) [NeZero n] : HPow (Fin n) Nat (Fin n) where
  hPow a m := npowRecAuto m a

instance (n : Nat) [NeZero n] : Pow (Fin n) Nat where
  pow a m := npowRecAuto m a

/--
theorem `left_distrib_aux` / 定理 `left_distrib_aux`

English:
theorem left_distrib_aux
  given: (n : Nat)
  statement: forall a b c : Fin n, a * (b + c) = a * b + a * c
  proof: fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
    calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm

中文:
定理 left_distrib_aux
  条件: (n : 自然数)
  结论: 对任意 a b c : 有限集 n, a * (b + c) = a * b + a * c
  证明: fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
    calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm
-/
private theorem left_distrib_aux (n : Nat) : forall a b c : Fin n, a * (b + c) = a * b + a * c :=
  fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
Fin.eq_of_val_eq
    calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: (n : Nat)
  body: private left_distrib_aux n
  right_distrib := fun a b c => by
    rw [mul_comm]; rw [left_distrib_aux]; rw [mul_comm _ b]; rw [mul_comm]

中文:
实例 instDistrib
  签名: (n : 自然数)
  定义体: private left_distrib_aux n
  right_distrib := fun a b c => by
    rw [mul_comm]; rw [left_distrib_aux]; rw [mul_comm _ b]; rw [mul_comm]

Depends on / 依赖: left_distrib_aux, private
-/
instance instDistrib (n : Nat) : Distrib (Fin n) where
  left_distrib := private left_distrib_aux n
  right_distrib := fun a b c => by
    rw [mul_comm]; rw [left_distrib_aux]; rw [mul_comm _ b]; rw [mul_comm]

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: (n : Nat) [NeZero n]
  body: Fin.zero_mul
  mul_zero := Fin.mul_zero

中文:
实例 instNonUnitalCommRing
  签名: (n : 自然数) [NeZero n]
  定义体: Fin.zero_mul
  mul_zero := Fin.mul_zero

Depends on / 依赖: Fin.zero_mul, zero_mul
-/
instance instNonUnitalCommRing (n : Nat) [NeZero n] : NonUnitalCommRing (Fin n) where
  zero_mul := Fin.zero_mul
  mul_zero := Fin.mul_zero

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: (n : Nat) [NeZero n]
  body: Fin.one_mul
  mul_one := Fin.mul_one

中文:
实例 instCommMonoid
  签名: (n : 自然数) [NeZero n]
  定义体: Fin.one_mul
  mul_one := Fin.mul_one

Depends on / 依赖: Fin.one_mul, one_mul
-/
instance instCommMonoid (n : Nat) [NeZero n] : CommMonoid (Fin n) where
  one_mul := Fin.one_mul
  mul_one := Fin.mul_one

/--
Instance `instHasDistribNeg` / 实例 `instHasDistribNeg`

English:
instance instHasDistribNeg
  signature: (n : Nat)
  body: Nat.casesOn n finZeroElim fun _i => mul_neg
  neg_mul := Nat.casesOn n finZeroElim fun _i => neg_mul

中文:
实例 instHasDistribNeg
  签名: (n : 自然数)
  定义体: Nat.casesOn n finZeroElim fun _i => mul_neg
  neg_mul := Nat.casesOn n finZeroElim fun _i => neg_mul

Depends on / 依赖: Nat.casesOn, casesOn, finZeroElim, mul_neg
-/
instance instHasDistribNeg (n : Nat) : HasDistribNeg (Fin n) where
  mul_neg := Nat.casesOn n finZeroElim fun _i => mul_neg
  neg_mul := Nat.casesOn n finZeroElim fun _i => neg_mul

/--
Commutative ring structure on `Fin n`.

This is not a global instance, but can introduced locally using `open Fin.CommRing in ...`.

This is not an instance because the `binop%` elaborator assumes that
there are no non-trivial coercion loops,
but this instance would introduce a coercion from `Nat` to `Fin n` and back.
Non-trivial loops lead to undesirable and counterintuitive elaboration behavior.

For example, for `x : Fin k` and `n : Nat`,
it causes `x < n` to be elaborated as `x < ↑n` rather than `↑x < n`,
silently introducing wraparound arithmetic.
-/
@[instance_reducible]
/--
Definition of `instCommRing` / `instCommRing` 的定义

English:
definition instCommRing
  signature: (n : Nat) [NeZero n]
  body: Fin.intCast n

中文:
定义 instCommRing
  签名: (n : 自然数) [NeZero n]
  定义体: Fin.intCast n

Depends on / 依赖: Fin.intCast, intCast
-/
def instCommRing (n : Nat) [NeZero n] : CommRing (Fin n) where
  intCast n := Fin.intCast n

namespace CommRing

attribute [scoped instance] Fin.instCommRing

end CommRing

instance (n : Nat) [NeZero n] : NeZero (1 : Fin (n + 1)) where
  out := by simp

end Fin

/-- The integers modulo `n : ℕ`. -/
@[to_additive_dont_translate]
/--
Definition of `ZMod` / `ZMod` 的定义

English:
definition ZMod
  signature: : Nat -> Type

中文:
定义 ZMod
  签名: : 自然数 -> 类型
-/
def ZMod : Nat -> Type
  | 0 => Int
  | n + 1 => Fin (n + 1)

/--
Instance `ZMod.decidableEq` / 实例 `ZMod.decidableEq`

English:
instance ZMod.decidableEq
  signature: : forall n : Nat, DecidableEq (ZMod n)

中文:
实例 ZMod.decidableEq
  签名: : 对任意 n : 自然数, DecidableEq (ZMod n)
-/
instance ZMod.decidableEq : forall n : Nat, DecidableEq (ZMod n)
| 0 => inferInstanceAs DecidableEq Int
| n + 1 => inferInstanceAs DecidableEq (Fin (n + 1))

/--
Instance `ZMod.repr` / 实例 `ZMod.repr`

English:
instance ZMod.repr
  signature: : forall n : Nat, Repr (ZMod n)

中文:
实例 ZMod.repr
  签名: : 对任意 n : 自然数, Repr (ZMod n)
-/
instance ZMod.repr : forall n : Nat, Repr (ZMod n)
| 0 => inferInstanceAs Repr Int
| n + 1 => inferInstanceAs Repr (Fin (n + 1))

namespace ZMod

/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: : Unique (ZMod 1)
  body: Fin.instUnique

中文:
实例 instUnique
  签名: : 唯一 (ZMod 1)
  定义体: Fin.instUnique

Depends on / 依赖: Fin.instUnique, instUnique
-/
instance instUnique : Unique (ZMod 1) := Fin.instUnique

/--
Instance `fintype` / 实例 `fintype`

English:
instance fintype
  signature: : forall (n : Nat) [NeZero n], Fintype (ZMod n)

中文:
实例 fintype
  签名: : 对任意 (n : 自然数) [NeZero n], 有限类型 (ZMod n)
-/
instance fintype : forall (n : Nat) [NeZero n], Fintype (ZMod n)
  | 0, h => (h.ne _ rfl).elim
  | n + 1, _ => Fin.fintype (n + 1)

/--
Instance `infinite` / 实例 `infinite`

English:
instance infinite
  signature: : Infinite (ZMod 0)
  body: Int.infinite

@[simp]

中文:
实例 infinite
  签名: : 无限 (ZMod 0)
  定义体: Int.infinite

@[simp]

Depends on / 依赖: Int.infinite, infinite
-/
instance infinite : Infinite (ZMod 0) :=
  Int.infinite

@[simp]
/--
theorem `card` / 定理 `card`

English:
theorem card
  given: (n : Nat) [Fintype (ZMod n)]
  statement: Fintype.card (ZMod n) = n
  proof: by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert! Fintype.card_fin (n + 1) using 2

中文:
定理 card
  条件: (n : 自然数) [有限类型 (ZMod n)]
  结论: 有限类型.card (ZMod n) = n
  证明: by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert! Fintype.card_fin (n + 1) using 2

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, convert, not_finite
-/
theorem card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n := by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert! Fintype.card_fin (n + 1) using 2

open Fin.CommRing in
/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: (n : Nat)
  body: Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Fin n.succ) _
  add_assoc := Nat.casesOn n (@add_assoc Int _) fun n => @add_assoc (Fin n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Fin n.succ)
  zero_add := Nat.casesOn n (@zero_add Int _) fun n => @zero_add (Fin n.succ) _
  add_zero := Nat.casesOn n (@add_zero Int _) fun n => @add_zero (Fin n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Fin n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Fin n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Fin n.succ) _
  zsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul
  zsmul_zero' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_zero'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_zero'
  zsmul_succ' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_succ'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_succ'
  zsmul_neg' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_neg'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_neg'
  nsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul
  nsmul_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_zero
  nsmul_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_succ
  neg_add_cancel := Nat.casesOn n (@neg_add_cancel Int _) fun n => @neg_add_cancel (Fin n.succ) _
  add_comm := Nat.casesOn n (@add_comm Int _) fun n => @add_comm (Fin n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Fin n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Fin n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Fin n.succ)
  one_mul := Nat.casesOn n (@one_mul Int _) fun n => @one_mul (Fin n.succ) _
  mul_one := Nat.casesOn n (@mul_one Int _) fun n => @mul_one (Fin n.succ) _
  natCast := Nat.casesOn n ((↑) : Nat -> Int) fun n => ((↑) : Nat -> Fin n.succ)
  natCast_zero := Nat.casesOn n (@Nat.cast_zero Int _) fun n => @Nat.cast_zero (Fin n.succ) _
  natCast_succ := Nat.casesOn n (@Nat.cast_succ Int _) fun n => @Nat.cast_succ (Fin n.succ) _
  intCast := Nat.casesOn n ((↑) : Int -> Int) fun n => ((↑) : Int -> Fin n.succ)
  intCast_ofNat := Nat.casesOn n (@Int.cast_natCast Int _) fun n => @Int.cast_natCast (Fin n.succ) _
  intCast_negSucc :=
    Nat.casesOn n (@Int.cast_negSucc Int _) fun n => @Int.cast_negSucc (Fin n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Fin n.succ) _ _ _
  right_distrib :=
    Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Fin n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Fin n.succ) _
  zero_mul := Nat.casesOn n (@zero_mul Int _) fun n => @zero_mul (Fin n.succ) _
  mul_zero := Nat.casesOn n (@mul_zero Int _) fun n => @mul_zero (Fin n.succ) _
  npow := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow fun n => ((inferInstance : CommRing (Fin n.succ))).npow
  npow_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_zero
  npow_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_succ

中文:
实例 commRing
  签名: (n : 自然数)
  定义体: Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Fin n.succ) _
  add_assoc := Nat.casesOn n (@add_assoc Int _) fun n => @add_assoc (Fin n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Fin n.succ)
  zero_add := Nat.casesOn n (@zero_add Int _) fun n => @zero_add (Fin n.succ) _
  add_zero := Nat.casesOn n (@add_zero Int _) fun n => @add_zero (Fin n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Fin n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Fin n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Fin n.succ) _
  zsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul
  zsmul_zero' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_zero'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_zero'
  zsmul_succ' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_succ'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_succ'
  zsmul_neg' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_neg'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_neg'
  nsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul
  nsmul_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_zero
  nsmul_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_succ
  neg_add_cancel := Nat.casesOn n (@neg_add_cancel Int _) fun n => @neg_add_cancel (Fin n.succ) _
  add_comm := Nat.casesOn n (@add_comm Int _) fun n => @add_comm (Fin n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Fin n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Fin n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Fin n.succ)
  one_mul := Nat.casesOn n (@one_mul Int _) fun n => @one_mul (Fin n.succ) _
  mul_one := Nat.casesOn n (@mul_one Int _) fun n => @mul_one (Fin n.succ) _
  natCast := Nat.casesOn n ((↑) : Nat -> Int) fun n => ((↑) : Nat -> Fin n.succ)
  natCast_zero := Nat.casesOn n (@Nat.cast_zero Int _) fun n => @Nat.cast_zero (Fin n.succ) _
  natCast_succ := Nat.casesOn n (@Nat.cast_succ Int _) fun n => @Nat.cast_succ (Fin n.succ) _
  intCast := Nat.casesOn n ((↑) : Int -> Int) fun n => ((↑) : Int -> Fin n.succ)
  intCast_ofNat := Nat.casesOn n (@Int.cast_natCast Int _) fun n => @Int.cast_natCast (Fin n.succ) _
  intCast_negSucc :=
    Nat.casesOn n (@Int.cast_negSucc Int _) fun n => @Int.cast_negSucc (Fin n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Fin n.succ) _ _ _
  right_distrib :=
    Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Fin n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Fin n.succ) _
  zero_mul := Nat.casesOn n (@zero_mul Int _) fun n => @zero_mul (Fin n.succ) _
  mul_zero := Nat.casesOn n (@mul_zero Int _) fun n => @mul_zero (Fin n.succ) _
  npow := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow fun n => ((inferInstance : CommRing (Fin n.succ))).npow
  npow_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_zero
  npow_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_succ

Depends on / 依赖: Add.add, Nat.casesOn, Submonoid, Submonoid.smul_def, casesOn, n.succ, simp_rw, smul_def, smul_eq_mul, smul_mul
-/
instance commRing (n : Nat) : CommRing (ZMod n) where
  add := Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Fin n.succ) _
  add_assoc := Nat.casesOn n (@add_assoc Int _) fun n => @add_assoc (Fin n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Fin n.succ)
  zero_add := Nat.casesOn n (@zero_add Int _) fun n => @zero_add (Fin n.succ) _
  add_zero := Nat.casesOn n (@add_zero Int _) fun n => @add_zero (Fin n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Fin n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Fin n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Fin n.succ) _
  zsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul
  zsmul_zero' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_zero'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_zero'
  zsmul_succ' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_succ'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_succ'
  zsmul_neg' := Nat.casesOn n
    ((inferInstance : CommRing Int)).zsmul_neg'
    fun n => ((inferInstance : CommRing (Fin n.succ))).zsmul_neg'
  nsmul := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul
  nsmul_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_zero
  nsmul_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).nsmul_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).nsmul_succ
  neg_add_cancel := Nat.casesOn n (@neg_add_cancel Int _) fun n => @neg_add_cancel (Fin n.succ) _
  add_comm := Nat.casesOn n (@add_comm Int _) fun n => @add_comm (Fin n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Fin n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Fin n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Fin n.succ)
  one_mul := Nat.casesOn n (@one_mul Int _) fun n => @one_mul (Fin n.succ) _
  mul_one := Nat.casesOn n (@mul_one Int _) fun n => @mul_one (Fin n.succ) _
  natCast := Nat.casesOn n ((↑) : Nat -> Int) fun n => ((↑) : Nat -> Fin n.succ)
  natCast_zero := Nat.casesOn n (@Nat.cast_zero Int _) fun n => @Nat.cast_zero (Fin n.succ) _
  natCast_succ := Nat.casesOn n (@Nat.cast_succ Int _) fun n => @Nat.cast_succ (Fin n.succ) _
  intCast := Nat.casesOn n ((↑) : Int -> Int) fun n => ((↑) : Int -> Fin n.succ)
  intCast_ofNat := Nat.casesOn n (@Int.cast_natCast Int _) fun n => @Int.cast_natCast (Fin n.succ) _
  intCast_negSucc :=
    Nat.casesOn n (@Int.cast_negSucc Int _) fun n => @Int.cast_negSucc (Fin n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Fin n.succ) _ _ _
  right_distrib :=
    Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Fin n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Fin n.succ) _
  zero_mul := Nat.casesOn n (@zero_mul Int _) fun n => @zero_mul (Fin n.succ) _
  mul_zero := Nat.casesOn n (@mul_zero Int _) fun n => @mul_zero (Fin n.succ) _
  npow := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow fun n => ((inferInstance : CommRing (Fin n.succ))).npow
  npow_zero := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_zero
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_zero
  npow_succ := Nat.casesOn n
    ((inferInstance : CommRing Int)).npow_succ
    fun n => ((inferInstance : CommRing (Fin n.succ))).npow_succ

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: (n : Nat)
  body: ⟨0⟩

中文:
实例 inhabited
  签名: (n : 自然数)
  定义体: ⟨0⟩
-/
instance inhabited (n : Nat) : Inhabited (ZMod n) :=
  ⟨0⟩

-- Verify that we can use `ZMod n` in `grind`.
example (n : Nat) : Lean.Grind.CommRing (ZMod n) := inferInstance

end ZMod
