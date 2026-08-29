/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.ZMod
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient ring `ℤ ⧸ Ideal.span {(n : ℤ)}`.

## Main definitions

- `ZMod.quotient_span_nat_equiv_zmod` and `ZMod.quotientSpanEquivZMod `:
  `ZMod n` is the ring quotient of `ℤ` by `n ℤ : Ideal.span {n}`
  (where `n : ℕ` and `n : ℤ` respectively)

## Tags

zmod, quotient ring, ideal quotient
-/

@[expose] public section

open QuotientAddGroup Set ZMod

variable (n : Nat) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

/--
Definition of `quotientSpanNatEquivZMod` / `quotientSpanNatEquivZMod` 的定义

English:
definition quotientSpanNatEquivZMod
  signature: : Int ⧸ Ideal.span {(n : Int)} ≃+* ZMod n
  body: (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans
RingHom.quotientKerEquivOfRightInverse
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast

中文:
定义 quotientSpanNatEquivZMod
  签名: : 整数 ⧸ Ideal.span {(n : 整数)} ≃+* ZMod n
  定义体: (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans
RingHom.quotientKerEquivOfRightInverse
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast

Depends on / 依赖: Function, Function.RightInverse, Ideal.quotEquivOfEq, Int.castRingHom, RightInverse, RingHom, RingHom.quotientKerEquivOfRightInverse, ZMod.cast, ZMod.ker_intCastRingHom, castRingHom, intCast_zmod_cast, ker_intCastRingHom, quotEquivOfEq, quotientKerEquivOfRightInverse, symm.trans
-/
def quotientSpanNatEquivZMod : Int ⧸ Ideal.span {(n : Int)} ≃+* ZMod n :=
(Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans
RingHom.quotientKerEquivOfRightInverse
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast

/--
Definition of `quotientSpanEquivZMod` / `quotientSpanEquivZMod` 的定义

English:
definition quotientSpanEquivZMod
  signature: (a : Int)
  body: (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)

@[simp]

中文:
定义 quotientSpanEquivZMod
  签名: (a : 整数)
  定义体: (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, a.natAbs, natAbs, quotEquivOfEq, quotientSpanNatEquivZMod, span_natAbs, symm.trans
-/
def quotientSpanEquivZMod (a : Int) : Int ⧸ Ideal.span ({a} : Set Int) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)

@[simp]
/--
theorem `quotientSpanNatEquivZMod_comp_Quotient_mk` / 定理 `quotientSpanNatEquivZMod_comp_Quotient_mk`

English:
theorem quotientSpanNatEquivZMod_comp_Quotient_mk
  given: (n : Nat)
  proof: rfl

@[simp]

中文:
定理 quotientSpanNatEquivZMod_comp_Quotient_mk
  条件: (n : 自然数)
  证明: rfl

@[simp]
-/
theorem quotientSpanNatEquivZMod_comp_Quotient_mk (n : Nat) :
    (Int.quotientSpanNatEquivZMod n : _ ->+* _).comp (Ideal.Quotient.mk (Ideal.span {(n : Int)})) =
      Int.castRingHom (ZMod n) := rfl

@[simp]
/--
theorem `quotientSpanNatEquivZMod_comp_castRingHom` / 定理 `quotientSpanNatEquivZMod_comp_castRingHom`

English:
theorem quotientSpanNatEquivZMod_comp_castRingHom
  given: (n : Nat)
  proof: by ext; simp

@[simp]

中文:
定理 quotientSpanNatEquivZMod_comp_castRingHom
  条件: (n : 自然数)
  证明: by ext; simp

@[simp]
-/
theorem quotientSpanNatEquivZMod_comp_castRingHom (n : Nat) :
    ((Int.quotientSpanNatEquivZMod n).symm : _ ->+* _).comp (Int.castRingHom (ZMod n)) =
      Ideal.Quotient.mk (Ideal.span {(n : Int)}) := by ext; simp

@[simp]
/--
theorem `quotientSpanEquivZMod_comp_Quotient_mk` / 定理 `quotientSpanEquivZMod_comp_Quotient_mk`

English:
theorem quotientSpanEquivZMod_comp_Quotient_mk
  given: (n : Int)
  proof: rfl

@[simp]

中文:
定理 quotientSpanEquivZMod_comp_Quotient_mk
  条件: (n : 整数)
  证明: rfl

@[simp]
-/
theorem quotientSpanEquivZMod_comp_Quotient_mk (n : Int) :
    (Int.quotientSpanEquivZMod n : _ ->+* _).comp (Ideal.Quotient.mk (Ideal.span {(n : Int)})) =
      Int.castRingHom (ZMod n.natAbs) := rfl

@[simp]
/--
theorem `quotientSpanEquivZMod_comp_castRingHom` / 定理 `quotientSpanEquivZMod_comp_castRingHom`

English:
theorem quotientSpanEquivZMod_comp_castRingHom
  given: (n : Int)
  proof: by ext; simp

中文:
定理 quotientSpanEquivZMod_comp_castRingHom
  条件: (n : 整数)
  证明: by ext; simp
-/
theorem quotientSpanEquivZMod_comp_castRingHom (n : Int) :
    ((Int.quotientSpanEquivZMod n).symm : _ ->+* _).comp (Int.castRingHom (ZMod n.natAbs)) =
      Ideal.Quotient.mk (Ideal.span {(n : Int)}) := by ext; simp

instance {n : Int} [NeZero n] : Finite (Int ⧸ Ideal.span {n}) :=
  Finite.of_equiv _ n.quotientSpanEquivZMod.symm.toEquiv

end Int

noncomputable section ChineseRemainder
open Ideal

open scoped Function in -- required for scoped `on` notation
/--
Definition of `ZMod.prodEquivPi` / `ZMod.prodEquivPi` 的定义

English:
definition ZMod.prodEquivPi
  signature: {ι : Type*} [Fintype ι] (a : ι -> Nat)
  body: have : Pairwise fun i j => IsCoprime (span {(a i : Int)}) (span {(a j : Int)}) :=
    fun _i _j h => (isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R := Int))
.symm.trans Int.quotientSpanNatEquivZMod _
.symm.trans quotEquivOfEq (iInf_span_singleton_natCast (R := Int) coprime)
.trans quoti

中文:
定义 ZMod.prodEquivPi
  签名: {ι : 类型} [Fintype ι] (a : ι -> 自然数)
  定义体: have : Pairwise fun i j => IsCoprime (span {(a i : Int)}) (span {(a j : Int)}) :=
    fun _i _j h => (isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R := Int))
.symm.trans Int.quotientSpanNatEquivZMod _
.symm.trans quotEquivOfEq (iInf_span_singleton_natCast (R := Int) coprime)
.trans quoti

Depends on / 依赖: Int.quotientSpanNatEquivZMod, IsCoprime, Pairwise, RingEquiv, RingEquiv.piCongrRight, coprime, iInf_span_singleton_natCast, isCoprime_span_singleton_iff, piCongrRight, quotEquivOfEq, quotientInfRingEquivPiQuotient, quotientSpanNatEquivZMod, symm.trans
-/
def ZMod.prodEquivPi {ι : Type*} [Fintype ι] (a : ι -> Nat)
    (coprime : Pairwise (Nat.Coprime on a)) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  have : Pairwise fun i j => IsCoprime (span {(a i : Int)}) (span {(a j : Int)}) :=
    fun _i _j h => (isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R := Int))
.symm.trans Int.quotientSpanNatEquivZMod _
.symm.trans quotEquivOfEq (iInf_span_singleton_natCast (R := Int) coprime)
.trans quotientInfRingEquivPiQuotient _ this
  RingEquiv.piCongrRight fun i => Int.quotientSpanNatEquivZMod (a i)

open Finset Function in
@[simp]
/--
theorem `ZMod.prodEquivPi_apply` / 定理 `ZMod.prodEquivPi_apply`

English:
theorem ZMod.prodEquivPi_apply
  statement: {ι : Type*} [Fintype ι] (a : ι -> Nat)
  proof: RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom (fun _ => ZMod _) i).comp
    (prodEquivPi a coprime).toRingHom) _) b

中文:
定理 ZMod.prodEquivPi_apply
  结论: {ι : 类型} [Fintype ι] (a : ι -> 自然数)
  证明: RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom (fun _ => ZMod _) i).comp
    (prodEquivPi a coprime).toRingHom) _) b

Depends on / 依赖: Pi.evalRingHom, RingHom, RingHom.congr_fun, Subsingleton, Subsingleton.elim, congr_fun, coprime, evalRingHom, prodEquivPi, toRingHom
-/
theorem ZMod.prodEquivPi_apply {ι : Type*} [Fintype ι] (a : ι -> Nat)
    (coprime : Pairwise (Nat.Coprime on a)) (b : ZMod (∏ i, a i)) (i : ι) :
    prodEquivPi a coprime b i = castHom (dvd_prod_of_mem a (mem_univ i)) _ b :=
  RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom (fun _ => ZMod _) i).comp
    (prodEquivPi a coprime).toRingHom) _) b

/--
Definition of `ZMod.equivPi` / `ZMod.equivPi` 的定义

English:
definition ZMod.equivPi
  signature: (hn : n != 0)
  body: (ringEquivCongr <| Nat.prod_primeFactors_coe_pow_factorization hn).trans
 prodEquivPi (fun (p : n.primeFactors) => (p : Nat) ^ (n.factorization p))
      n.pairwise_coprime_pow_primeFactors_factorization

中文:
定义 ZMod.equivPi
  签名: (hn : n != 0)
  定义体: (ringEquivCongr <| Nat.prod_primeFactors_coe_pow_factorization hn).trans
 prodEquivPi (fun (p : n.primeFactors) => (p : Nat) ^ (n.factorization p))
      n.pairwise_coprime_pow_primeFactors_factorization

Depends on / 依赖: Nat.prod_primeFactors_coe_pow_factorization, factorization, n.factorization, n.pairwise_coprime_pow_primeFactors_factorization, n.primeFactors, pairwise_coprime_pow_primeFactors_factorization, primeFactors, prodEquivPi, prod_primeFactors_coe_pow_factorization, ringEquivCongr
-/
def ZMod.equivPi (hn : n != 0) :
    ZMod n ≃+* Π (p : n.primeFactors), ZMod (p ^ (n.factorization p)) :=
  (ringEquivCongr <| Nat.prod_primeFactors_coe_pow_factorization hn).trans
 prodEquivPi (fun (p : n.primeFactors) => (p : Nat) ^ (n.factorization p))
      n.pairwise_coprime_pow_primeFactors_factorization

end ChineseRemainder
