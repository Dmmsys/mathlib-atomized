/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Data.Int.Cast.Basic

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps

## Implementation note

The `nsmul` and `zsmul` assumptions on any transfer definition for an algebraic structure involving
both addition and multiplication (e.g. `AddMonoidWithOne`) is `∀ n x, f (n • x) = n • f x`, which is
what we would expect.
However, we cannot do the same for transfer definitions built using `to_additive` (e.g. `AddMonoid`)
as we want the multiplicative versions to be `∀ x n, f (x ^ n) = f x ^ n`.
As a result, we must use `Function.swap` when using additivised transfer definitions in
non-additivised ones.
-/

public section

variable {R S : Type*}

namespace Function.Injective
variable (f : S -> R) (hf : Injective f)
include hf

variable [Add S] [Mul S]

/--
theorem `leftDistribClass` / 定理 `leftDistribClass`

English:
theorem leftDistribClass
  statement: [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f (x + y) = f x + f y)
  proof: hf by simp only [*, left_distrib]

中文:
定理 leftDistribClass
  结论: [乘法 R] [加法 R] [LeftDistrib类 R] (add : 对任意 x y, f (x + y) = f x + f y)
  证明: hf by simp only [*, left_distrib]

Depends on / 依赖: left_distrib
-/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : LeftDistribClass S where
left_distrib x y z := hf by simp only [*, left_distrib]

/--
theorem `rightDistribClass` / 定理 `rightDistribClass`

English:
theorem rightDistribClass
  statement: [Mul R] [Add R] [RightDistribClass R] (add : forall x y, f (x + y) = f x + f y)
  proof: hf by simp only [*, right_distrib]

中文:
定理 rightDistribClass
  结论: [乘法 R] [加法 R] [RightDistrib类 R] (add : 对任意 x y, f (x + y) = f x + f y)
  证明: hf by simp only [*, right_distrib]

Depends on / 依赖: right_distrib
-/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : RightDistribClass S where
right_distrib x y z := hf by simp only [*, right_distrib]

variable [Zero S] [One S] [Neg S] [Sub S] [SMul Nat S] [SMul Int S]
  [Pow S Nat] [NatCast S] [IntCast S]

-- See note [reducible non-instances]
/--
Definition of `distrib` / `distrib` 的定义

English:
abbreviation distrib
  signature: [Distrib R] (add : forall x y, f (x + y) = f x + f y)
  body: hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

中文:
缩写 distrib
  签名: [Distrib R] (add : 对任意 x y, f (x + y) = f x + f y)
  定义体: hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul
-/
protected abbrev distrib [Distrib R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

-- See note [reducible non-instances]
/--
Definition of `hasDistribNeg` / `hasDistribNeg` 的定义

English:
abbreviation hasDistribNeg
  signature: (f : S -> R) (hf : Injective f) [Mul R] [HasDistribNeg R]
  body: { hf.involutiveNeg _ neg, ‹Mul S› with
neg_mul := fun x y => hf by rw [neg, mul, neg, neg_mul, mul],
mul_neg := fun x y => hf by rw [neg, mul, neg, mul_neg, mul] }

中文:
缩写 hasDistribNeg
  签名: (f : S -> R) (hf : 单射 f) [乘法 R] [有DistribNeg R]
  定义体: { hf.involutiveNeg _ neg, ‹Mul S› with
neg_mul := fun x y => hf by rw [neg, mul, neg, neg_mul, mul],
mul_neg := fun x y => hf by rw [neg, mul, neg, mul_neg, mul] }
-/
protected abbrev hasDistribNeg (f : S -> R) (hf : Injective f) [Mul R] [HasDistribNeg R]
    (neg : forall a, f (-a) = -f a)
    (mul : forall a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
neg_mul := fun x y => hf by rw [neg, mul, neg, neg_mul, mul],
mul_neg := fun x y => hf by rw [neg, mul, neg, mul_neg, mul] }

/--
Definition of `addMonoidWithOne` / `addMonoidWithOne` 的定义

English:
abbreviation addMonoidWithOne
  signature: [AddMonoidWithOne R]
  body: { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]) }

中文:
缩写 addMonoidWithOne
  签名: [加法带幺幺半群 R]
  定义体: { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]) }
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne R]
    (f : S -> R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]) }

/--
Definition of `addCommMonoidWithOne` / `addCommMonoidWithOne` 的定义

English:
abbreviation addCommMonoidWithOne
  signature: {S} [Zero S] [One S] [Add S] [SMul Nat S] [NatCast S]
  body: hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

中文:
缩写 addCommMonoidWithOne
  签名: {S} [零 S] [幺 S] [加法 S] [标量乘法 自然数 S] [自然数嵌入 S]
  定义体: hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
-/
protected abbrev addCommMonoidWithOne {S} [Zero S] [One S] [Add S] [SMul Nat S] [NatCast S]
    [AddCommMonoidWithOne R] (f : S -> R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/--
Definition of `addGroupWithOne` / `addGroupWithOne` 的定义

English:
abbreviation addGroupWithOne
  signature: {S} [Zero S] [One S] [Add S] [SMul Nat S] [Neg S] [Sub S]
  body: { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc]) }

中文:
缩写 addGroupWithOne
  签名: {S} [零 S] [幺 S] [加法 S] [标量乘法 自然数 S] [取负 S] [减法 S]
  定义体: { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc]) }
-/
protected abbrev addGroupWithOne {S} [Zero S] [One S] [Add S] [SMul Nat S] [Neg S] [Sub S]
    [SMul Int S] [NatCast S] [IntCast S] [AddGroupWithOne R] (f : S -> R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : AddGroupWithOne S :=
  { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc]) }

/--
Definition of `addCommGroupWithOne` / `addCommGroupWithOne` 的定义

English:
abbreviation addCommGroupWithOne
  signature: {S} [Zero S] [One S] [Add S] [SMul Nat S] [Neg S] [Sub S]
  body: { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

中文:
缩写 addCommGroupWithOne
  签名: {S} [零 S] [幺 S] [加法 S] [标量乘法 自然数 S] [取负 S] [减法 S]
  定义体: { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
-/
protected abbrev addCommGroupWithOne {S} [Zero S] [One S] [Add S] [SMul Nat S] [Neg S] [Sub S]
    [SMul Int S] [NatCast S] [IntCast S] [AddCommGroupWithOne R] (f : S -> R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocSemiring` / `nonUnitalNonAssocSemiring` 的定义

English:
abbreviation nonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
  body: hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

中文:
缩写 nonUnitalNonAssocSemiring
  签名: [非幺非结合半环 R] (zero : f 0 = 0)
  定义体: hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalSemiring` / `nonUnitalSemiring` 的定义

English:
abbreviation nonUnitalSemiring
  signature: [NonUnitalSemiring R]
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

中文:
缩写 nonUnitalSemiring
  签名: [非幺半环 R]
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring R]
    (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) :
    NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

-- See note [reducible non-instances]
/--
Definition of `nonAssocSemiring` / `nonAssocSemiring` 的定义

English:
abbreviation nonAssocSemiring
  signature: [NonAssocSemiring R]
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

中文:
缩写 nonAssocSemiring
  签名: [非结合半环 R]
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
-/
protected abbrev nonAssocSemiring [NonAssocSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

-- See note [reducible non-instances]
/--
Definition of `semiring` / `semiring` 的定义

English:
abbreviation semiring
  signature: [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

中文:
缩写 semiring
  签名: [半环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow
-/
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocRing` / `nonUnitalNonAssocRing` 的定义

English:
abbreviation nonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R] (f : S -> R)
  body: hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

中文:
缩写 nonUnitalNonAssocRing
  签名: [非幺非结合环 R] (f : S -> R)
  定义体: hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) : NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalRing` / `nonUnitalRing` 的定义

English:
abbreviation nonUnitalRing
  signature: [NonUnitalRing R]
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

中文:
缩写 nonUnitalRing
  签名: [非幺环 R]
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
-/
protected abbrev nonUnitalRing [NonUnitalRing R]
    (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonAssocRing` / `nonAssocRing` 的定义

English:
abbreviation nonAssocRing
  signature: [NonAssocRing R]
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

中文:
缩写 nonAssocRing
  签名: [非结合环 R]
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
-/
protected abbrev nonAssocRing [NonAssocRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

-- See note [reducible non-instances]
/--
Definition of `ring` / `ring` 的定义

English:
abbreviation ring
  signature: [Ring R] (zero : f 0 = 0)
  body: hf.semiring f zero one add mul nsmul npow natCast
  -- zsmul included here explicitly to make sure it's picked correctly by `fast_instance%`.
  zsmul := fun n x => n • x
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

中文:
缩写 ring
  签名: [环 R] (zero : f 0 = 0)
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  -- zsmul included here explicitly to make sure it's picked correctly by `fast_instance%`.
  zsmul := fun n x => n • x
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
-/
protected abbrev ring [Ring R] (zero : f 0 = 0)
    (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  -- zsmul included here explicitly to make sure it's picked correctly by `fast_instance%`.
  zsmul := fun n x => n • x
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocCommSemiring` / `nonUnitalNonAssocCommSemiring` 的定义

English:
abbreviation nonUnitalNonAssocCommSemiring
  signature: [NonUnitalNonAssocCommSemiring R]
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

中文:
缩写 nonUnitalNonAssocCommSemiring
  签名: [非幺非结合交换半环 R]
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul
-/
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalCommSemiring` / `nonUnitalCommSemiring` 的定义

English:
abbreviation nonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R] (f : S -> R)
  body: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

中文:
缩写 nonUnitalCommSemiring
  签名: [非幺交换半环 R] (f : S -> R)
  定义体: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) :
    NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

-- See note [reducible non-instances]
/--
Definition of `nonAssocCommSemiring` / `nonAssocCommSemiring` 的定义

English:
abbreviation nonAssocCommSemiring
  signature: [NonAssocCommSemiring R] (f : S -> R)
  body: hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

中文:
缩写 nonAssocCommSemiring
  签名: [非结合交换半环 R] (f : S -> R)
  定义体: hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.prodFanIsLimit, Iso.unop_inv, Scheme, Scheme.Spec, Scheme.Spec_map, Spec.map, Spec.map_co, Spec.map_comp, Spec_map, coprod, coprod.inl_desc, coprod.inr_desc, coprodComparison, coprodComparison_inl_assoc, coprodComparison_inr_assoc, coprodSpec, inl_desc
-/
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

-- See note [reducible non-instances]
/--
Definition of `commSemiring` / `commSemiring` 的定义

English:
abbreviation commSemiring
  signature: [CommSemiring R]
  body: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

中文:
缩写 commSemiring
  签名: [交换半环 R]
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul
-/
protected abbrev commSemiring [CommSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (natCast : forall n : Nat, f n = n) :
    CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocCommRing` / `nonUnitalNonAssocCommRing` 的定义

English:
abbreviation nonUnitalNonAssocCommRing
  signature: [NonUnitalNonAssocCommRing R] (f : S -> R)
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

中文:
缩写 nonUnitalNonAssocCommRing
  签名: [非幺非结合交换环 R] (f : S -> R)
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul
-/
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalCommRing` / `nonUnitalCommRing` 的定义

English:
abbreviation nonUnitalCommRing
  signature: [NonUnitalCommRing R] (f : S -> R)
  body: hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

中文:
缩写 nonUnitalCommRing
  签名: [非幺交换环 R] (f : S -> R)
  定义体: hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

Depends on / 依赖: PreservesFiniteCoproducts, PreservesFiniteCoproducts.of_preserves_binary_and_initial, of_preserves_binary_and_initial
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) : NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

-- See note [reducible non-instances]
/--
Definition of `nonAssocCommRing` / `nonAssocCommRing` 的定义

English:
abbreviation nonAssocCommRing
  signature: [NonAssocCommRing R] (f : S -> R)
  body: hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

中文:
缩写 nonAssocCommRing
  签名: [非结合交换环 R] (f : S -> R)
  定义体: hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
-/
protected abbrev nonAssocCommRing [NonAssocCommRing R] (f : S -> R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

-- See note [reducible non-instances]
/--
Definition of `commRing` / `commRing` 的定义

English:
abbreviation commRing
  signature: [CommRing R]
  body: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

中文:
缩写 commRing
  签名: [交换环 R]
  定义体: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow
-/
protected abbrev commRing [CommRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Injective

namespace Function.Surjective
variable (f : R -> S) (hf : Surjective f)
include hf

variable [Add S] [Mul S]

/--
theorem `leftDistribClass` / 定理 `leftDistribClass`

English:
theorem leftDistribClass
  statement: [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f (x + y) = f x + f y)
  proof: hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

中文:
定理 leftDistribClass
  结论: [乘法 R] [加法 R] [LeftDistrib类 R] (add : 对任意 x y, f (x + y) = f x + f y)
  证明: hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

Depends on / 依赖: Function, Function.surjective_eval, Function.update, IsLocalization, IsLocalization.Away, IsLocalization.away_of_isIdempotentElem_of_mul, IsOpenImmersion, IsOpenImmersion.of_isLocalization, Pi.evalRingHom, away_of_isIdempotentElem_of_mul, classical, congr_fun, evalRingHom, hf.forall, left_distrib, of_isLocalization, surjective_eval, toAlgebra, update
-/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

/--
theorem `rightDistribClass` / 定理 `rightDistribClass`

English:
theorem rightDistribClass
  statement: [Mul R] [Add R] [RightDistribClass R] (add : forall x y, f (x + y) = f x + f y)
  proof: hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

中文:
定理 rightDistribClass
  结论: [乘法 R] [加法 R] [RightDistrib类 R] (add : 对任意 x y, f (x + y) = f x + f y)
  证明: hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

Depends on / 依赖: DFinsupp, DFinsupp.single, Ideal.eq_top_iff_one, PrimeSpectrum, PrimeSpectrum.ext_iff.mp, Set.disjoint_iff_forall_ne.mpr, asIdeal, classical, disjoint_iff_forall_ne, eq_top_iff_one, ext_iff, h.symm, hf.forall, isOpenImmersion_sigmaDesc, ne_top, right_distrib, single, x.asIdeal, y.asIdeal
-/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

-- See note [reducible non-instances]
/--
Definition of `distrib` / `distrib` 的定义

English:
abbreviation distrib
  signature: [Distrib R] (add : forall x y, f (x + y) = f x + f y)
  body: hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

中文:
缩写 distrib
  签名: [Distrib R] (add : 对任意 x y, f (x + y) = f x + f y)
  定义体: hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul
-/
protected abbrev distrib [Distrib R] (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

variable [Zero S] [One S] [Neg S] [Sub S] [SMul Nat S] [SMul Int S]
  [Pow S Nat] [NatCast S] [IntCast S]

-- See note [reducible non-instances]
/--
Definition of `hasDistribNeg` / `hasDistribNeg` 的定义

English:
abbreviation hasDistribNeg
  signature: [Mul R] [HasDistribNeg R]
  body: { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := hf.forall₂.2 fun x y => by rw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by rw [← neg, ← mul, mul_neg, neg, mul] }

中文:
缩写 hasDistribNeg
  签名: [乘法 R] [有DistribNeg R]
  定义体: { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := hf.forall₂.2 fun x y => by rw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by rw [← neg, ← mul, mul_neg, neg, mul] }
-/
protected abbrev hasDistribNeg [Mul R] [HasDistribNeg R]
    (neg : forall a, f (-a) = -f a) (mul : forall a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := hf.forall₂.2 fun x y => by rw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by rw [← neg, ← mul, mul_neg, neg, mul] }


/--
Definition of `addMonoidWithOne` / `addMonoidWithOne` 的定义

English:
abbreviation addMonoidWithOne
  signature: [AddMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
  body: { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← natCast, Nat.cast_succ, add, one, natCast] }

中文:
缩写 addMonoidWithOne
  签名: [加法带幺幺半群 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← natCast, Nat.cast_succ, add, one, natCast] }
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← natCast, Nat.cast_succ, add, one, natCast] }

/--
Definition of `addCommMonoidWithOne` / `addCommMonoidWithOne` 的定义

English:
abbreviation addCommMonoidWithOne
  signature: [AddCommMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

中文:
缩写 addCommMonoidWithOne
  签名: [加法交换带幺幺半群 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
-/
protected abbrev addCommMonoidWithOne [AddCommMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/--
Definition of `addGroupWithOne` / `addGroupWithOne` 的定义

English:
abbreviation addGroupWithOne
  signature: [AddGroupWithOne R]
  body: { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← intCast]; rw [Int.cast_negSucc]; rw [neg]; rw [natCast] }

中文:
缩写 addGroupWithOne
  签名: [加法带幺群 R]
  定义体: { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← intCast]; rw [Int.cast_negSucc]; rw [neg]; rw [natCast] }
-/
protected abbrev addGroupWithOne [AddGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : AddGroupWithOne S :=
  { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← intCast]; rw [Int.cast_negSucc]; rw [neg]; rw [natCast] }

/--
Definition of `addCommGroupWithOne` / `addCommGroupWithOne` 的定义

English:
abbreviation addCommGroupWithOne
  signature: [AddCommGroupWithOne R]
  body: { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

中文:
缩写 addCommGroupWithOne
  签名: [加法交换带幺群 R]
  定义体: { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
-/
protected abbrev addCommGroupWithOne [AddCommGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

/--
Definition of `nonUnitalNonAssocSemiring` / `nonUnitalNonAssocSemiring` 的定义

English:
abbreviation nonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
  body: hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

中文:
缩写 nonUnitalNonAssocSemiring
  签名: [非幺非结合半环 R] (zero : f 0 = 0)
  定义体: hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

Depends on / 依赖: DiscreteTopology, Finite, IsAffine
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalSemiring` / `nonUnitalSemiring` 的定义

English:
abbreviation nonUnitalSemiring
  signature: [NonUnitalSemiring R] (zero : f 0 = 0)
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

中文:
缩写 nonUnitalSemiring
  签名: [非幺半环 R] (zero : f 0 = 0)
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

Depends on / 依赖: f.isOpenEmbedding.injective, g.isOpenEmbedding.injective, injective, isOpenEmbedding, mono_iff_injective
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) : NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

-- See note [reducible non-instances]
/--
Definition of `nonAssocSemiring` / `nonAssocSemiring` 的定义

English:
abbreviation nonAssocSemiring
  signature: [NonAssocSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

中文:
缩写 nonAssocSemiring
  签名: [非结合半环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, WidePushoutShape, WidePushoutShape.hom_id, hom_id, infer_instance, map_id
-/
protected abbrev nonAssocSemiring [NonAssocSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

-- See note [reducible non-instances]
/--
Definition of `semiring` / `semiring` 的定义

English:
abbreviation semiring
  signature: [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

中文:
缩写 semiring
  签名: [半环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow
-/
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (natCast : forall n : Nat, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocRing` / `nonUnitalNonAssocRing` 的定义

English:
abbreviation nonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R] (zero : f 0 = 0)
  body: hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

中文:
缩写 nonUnitalNonAssocRing
  签名: [非幺非结合环 R] (zero : f 0 = 0)
  定义体: hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalRing` / `nonUnitalRing` 的定义

English:
abbreviation nonUnitalRing
  signature: [NonUnitalRing R] (zero : f 0 = 0)
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

中文:
缩写 nonUnitalRing
  签名: [非幺环 R] (zero : f 0 = 0)
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
-/
protected abbrev nonUnitalRing [NonUnitalRing R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonAssocRing` / `nonAssocRing` 的定义

English:
abbreviation nonAssocRing
  signature: [NonAssocRing R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

中文:
缩写 nonAssocRing
  签名: [非结合环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
-/
protected abbrev nonAssocRing [NonAssocRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

-- See note [reducible non-instances]
/--
Definition of `ring` / `ring` 的定义

English:
abbreviation ring
  signature: [Ring R] (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
  body: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

中文:
缩写 ring
  签名: [环 R] (zero : f 0 = 0) (one : f 1 = 1) (add : 对任意 x y, f (x + y) = f x + f y)
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

Depends on / 依赖: f.left.isOpenEmbedding.injective, g.left.isOpenEmbedding.injective, injective, isOpenEmbedding, mono_iff_injective
-/
protected abbrev ring [Ring R] (zero : f 0 = 0) (one : f 1 = 1) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (natCast : forall n : Nat, f n = n)
    (intCast : forall n : Int, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocCommSemiring` / `nonUnitalNonAssocCommSemiring` 的定义

English:
abbreviation nonUnitalNonAssocCommSemiring
  signature: [NonUnitalNonAssocCommSemiring R] (zero : f 0 = 0)
  body: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

中文:
缩写 nonUnitalNonAssocCommSemiring
  签名: [非幺非结合交换半环 R] (zero : f 0 = 0)
  定义体: hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, WidePushoutShape, WidePushoutShape.hom_id, hom_id, infer_instance, map_id
-/
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalCommSemiring` / `nonUnitalCommSemiring` 的定义

English:
abbreviation nonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R] (zero : f 0 = 0)
  body: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

中文:
缩写 nonUnitalCommSemiring
  签名: [非幺交换半环 R] (zero : f 0 = 0)
  定义体: hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) : NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

-- See note [reducible non-instances]
/--
Definition of `nonAssocCommSemiring` / `nonAssocCommSemiring` 的定义

English:
abbreviation nonAssocCommSemiring
  signature: [NonAssocCommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

中文:
缩写 nonAssocCommSemiring
  签名: [非结合交换半环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul
-/
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

-- See note [reducible non-instances]
/--
Definition of `commSemiring` / `commSemiring` 的定义

English:
abbreviation commSemiring
  signature: [CommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

中文:
缩写 commSemiring
  签名: [交换半环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul
-/
protected abbrev commSemiring [CommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) : CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalNonAssocCommRing` / `nonUnitalNonAssocCommRing` 的定义

English:
abbreviation nonUnitalNonAssocCommRing
  signature: [NonUnitalNonAssocCommRing R]
  body: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

中文:
缩写 nonUnitalNonAssocCommRing
  签名: [非幺非结合交换环 R]
  定义体: hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

Depends on / 依赖: CategoryTheory, IsOpenImmersion, MorphismProperty, MorphismProperty.Over.forget, MorphismProperty.Over.forget_comp_forget_map, MorphismProperty.cancel_right_of_respectsIso, Over.forget, cancel_right_of_respectsIso, colimit, e.hom, forget, forget_comp_forget_map, preservesColimitIso
-/
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R]
    (zero : f 0 = 0) (add : forall x y, f (x + y) = f x + f y)
    (mul : forall x y, f (x * y) = f x * f y) (neg : forall x, f (-x) = -f x)
    (sub : forall x y, f (x - y) = f x - f y) (nsmul : forall (n : Nat) (x), f (n • x) = n • f x)
    (zsmul : forall (n : Int) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

-- See note [reducible non-instances]
/--
Definition of `nonUnitalCommRing` / `nonUnitalCommRing` 的定义

English:
abbreviation nonUnitalCommRing
  signature: [NonUnitalCommRing R] (zero : f 0 = 0)
  body: hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

中文:
缩写 nonUnitalCommRing
  签名: [非幺交换环 R] (zero : f 0 = 0)
  定义体: hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (zero : f 0 = 0)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x) :
    NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

-- See note [reducible non-instances]
/--
Definition of `nonAssocCommRing` / `nonAssocCommRing` 的定义

English:
abbreviation nonAssocCommRing
  signature: [NonAssocCommRing R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonAssocCommSemiring f zero one add mul nsmul natCast

中文:
缩写 nonAssocCommRing
  签名: [非结合交换环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonAssocCommSemiring f zero one add mul nsmul natCast
-/
protected abbrev nonAssocCommRing [NonAssocCommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonAssocCommSemiring f zero one add mul nsmul natCast

-- See note [reducible non-instances]
/--
Definition of `commRing` / `commRing` 的定义

English:
abbreviation commRing
  signature: [CommRing R] (zero : f 0 = 0) (one : f 1 = 1)
  body: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

中文:
缩写 commRing
  签名: [交换环 R] (zero : f 0 = 0) (one : f 1 = 1)
  定义体: hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow
-/
protected abbrev commRing [CommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y)
    (neg : forall x, f (-x) = -f x) (sub : forall x y, f (x - y) = f x - f y)
    (nsmul : forall (n : Nat) (x), f (n • x) = n • f x) (zsmul : forall (n : Int) (x), f (n • x) = n • f x)
    (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (natCast : forall n : Nat, f n = n) (intCast : forall n : Int, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Surjective

variable [Mul R] [HasDistribNeg R]

/--
Instance `AddOpposite.instHasDistribNeg` / 实例 `AddOpposite.instHasDistribNeg`

English:
instance AddOpposite.instHasDistribNeg
  signature: : HasDistribNeg Rᵃᵒᵖ
  body: unop_injective.hasDistribNeg _ unop_neg unop_mul

中文:
实例 AddOpposite.instHasDistribNeg
  签名: : 有DistribNeg Rᵃᵒᵖ
  定义体: unop_injective.hasDistribNeg _ unop_neg unop_mul

Depends on / 依赖: hasDistribNeg, unop_injective, unop_injective.hasDistribNeg, unop_mul, unop_neg
-/
instance AddOpposite.instHasDistribNeg : HasDistribNeg Rᵃᵒᵖ :=
  unop_injective.hasDistribNeg _ unop_neg unop_mul
