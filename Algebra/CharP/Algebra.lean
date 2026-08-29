/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `FractionRing R`.


## Main results

- `charP_of_injective_algebraMap` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `FreeAlgebra R X` has the same characteristic as `R`.
- The `FractionRing R` of an integral domain `R` has the same characteristic as `R`.

-/

public section

variable {R A : Type*}

/--
theorem `CharP.dvd_of_ringHom` / 定理 `CharP.dvd_of_ringHom`

English:
theorem CharP.dvd_of_ringHom
  statement: [NonAssocSemiring R] [NonAssocSemiring A]
  proof: by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p]; rw [CharP.cast_eq_zero]; rw [map_zero]

中文:
定理 特征p.dvd_of_ringHom
  结论: [非结合半环 R] [非结合半环 A]
  证明: by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p]; rw [CharP.cast_eq_zero]; rw [map_zero]

Depends on / 依赖: CharP.cast_eq_zero, CharP.cast_eq_zero_iff, cast_eq_zero, cast_eq_zero_iff, map_natCast, map_zero
-/
theorem CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R ->+* A) (p q : Nat) [CharP R p] [CharP A q] : q ∣ p := by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p]; rw [CharP.cast_eq_zero]; rw [map_zero]

/--
theorem `CharP.of_ringHom_of_ne_zero` / 定理 `CharP.of_ringHom_of_ne_zero`

English:
theorem CharP.of_ringHom_of_ne_zero
  statement: [NonAssocSemiring R] [NoZeroDivisors R]
  proof: by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this]; rw [mul_one] at e
  ex

中文:
定理 特征p.of_ringHom_of_ne_zero
  结论: [非结合半环 R] [无零因子 R]
  证明: by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this]; rw [mul_one] at e
  ex

Depends on / 依赖: CharP.char_is_prime_or_zero, CharP.exists, Nat.isUnit_iff.mp, Nat.isUnit_iff.not.mpr, char_is_prime_or_zero, char_ne_one, domain_nontrivial, dvd_of_ringHom, f.domain_nontrivial, isUnit_iff, mul_one, resolve_left, resolve_right
-/
theorem CharP.of_ringHom_of_ne_zero [NonAssocSemiring R] [NoZeroDivisors R]
    [NonAssocSemiring A] [Nontrivial A]
    (f : R ->+* A) (p : Nat) (hp : p != 0) [CharP R p] : CharP A p := by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this]; rw [mul_one] at e
  exact e ▸ hq

/--
theorem `charP_of_injective_ringHom` / 定理 `charP_of_injective_ringHom`

English:
theorem charP_of_injective_ringHom
  statement: [NonAssocSemiring R] [NonAssocSemiring A]
  proof: by
    rw [← CharP.cast_eq_zero_iff R p x]; rw [← map_natCast f x]; rw [map_eq_zero_iff f h]

中文:
定理 charP_of_injective_ringHom
  结论: [非结合半环 R] [非结合半环 A]
  证明: by
    rw [← CharP.cast_eq_zero_iff R p x]; rw [← map_natCast f x]; rw [map_eq_zero_iff f h]

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, map_eq_zero_iff, map_natCast
-/
theorem charP_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R ->+* A} (h : Function.Injective f) (p : Nat) [CharP R p] : CharP A p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff R p x]; rw [← map_natCast f x]; rw [map_eq_zero_iff f h]

/--
theorem `charP_of_injective_algebraMap` / 定理 `charP_of_injective_algebraMap`

English:
theorem charP_of_injective_algebraMap
  statement: [CommSemiring R] [Semiring A] [Algebra R A]
  proof: charP_of_injective_ringHom h p

中文:
定理 charP_of_injective_algebraMap
  结论: [交换半环 R] [半环 A] [代数 R A]
  证明: charP_of_injective_ringHom h p

Depends on / 依赖: charP_of_injective_ringHom
-/
theorem charP_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : Nat) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom h p

/--
theorem `charP_of_injective_algebraMap'` / 定理 `charP_of_injective_algebraMap'`

English:
theorem charP_of_injective_algebraMap'
  statement: (R : Type*) [CommRing R] [Semiring A]
  proof: charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

中文:
定理 charP_of_injective_algebraMap'
  结论: (R : 类型) [交换环 R] [半环 A]
  证明: charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, charP_of_injective_ringHom
-/
theorem charP_of_injective_algebraMap' (R : Type*) [CommRing R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] (p : Nat) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

/--
theorem `charZero_of_injective_ringHom` / 定理 `charZero_of_injective_ringHom`

English:
theorem charZero_of_injective_ringHom
  statement: [NonAssocSemiring R] [NonAssocSemiring A]
  proof: CharZero.cast_injective h by simpa only [map_natCast f]

中文:
定理 charZero_of_injective_ringHom
  结论: [非结合半环 R] [非结合半环 A]
  证明: CharZero.cast_injective h by simpa only [map_natCast f]

Depends on / 依赖: CharZero, CharZero.cast_injective, cast_injective, map_natCast
-/
theorem charZero_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R ->+* A} (h : Function.Injective f) [CharZero R] : CharZero A where
cast_injective _ _ _ := CharZero.cast_injective h by simpa only [map_natCast f]

/--
theorem `charZero_of_injective_algebraMap` / 定理 `charZero_of_injective_algebraMap`

English:
theorem charZero_of_injective_algebraMap
  statement: [CommSemiring R] [Semiring A] [Algebra R A]
  proof: charZero_of_injective_ringHom h

中文:
定理 charZero_of_injective_algebraMap
  结论: [交换半环 R] [半环 A] [代数 R A]
  证明: charZero_of_injective_ringHom h

Depends on / 依赖: charZero_of_injective_ringHom
-/
theorem charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  charZero_of_injective_ringHom h

/--
theorem `RingHom.charP` / 定理 `RingHom.charP`

English:
theorem RingHom.charP
  statement: [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
  proof: by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

中文:
定理 环态射.charP
  结论: [非结合半环 R] [非结合半环 A] (f : R ->+* A)
  证明: by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

Depends on / 依赖: CharP.eq, CharP.exists, charP_of_injective_ringHom
-/
theorem RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
    (H : Function.Injective f) (p : Nat) [CharP A p] : CharP R p := by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

/--
theorem `RingHom.charP_iff` / 定理 `RingHom.charP_iff`

English:
theorem RingHom.charP_iff
  statement: [NonAssocSemiring R] [NonAssocSemiring A]
  proof: ⟨fun _ => charP_of_injective_ringHom H p, fun _ => f.charP H p⟩

中文:
定理 环态射.charP_iff
  结论: [非结合半环 R] [非结合半环 A]
  证明: ⟨fun _ => charP_of_injective_ringHom H p, fun _ => f.charP H p⟩
-/
protected theorem RingHom.charP_iff [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R ->+* A) (H : Function.Injective f) (p : Nat) : CharP R p ↔ CharP A p :=
  ⟨fun _ => charP_of_injective_ringHom H p, fun _ => f.charP H p⟩

/--
lemma `expChar_of_injective_ringHom` / 引理 `expChar_of_injective_ringHom`

English:
lemma expChar_of_injective_ringHom
  proof: by
  rcases hR with _ | hprime
  · have := charZero_of_injective_ringHom h; exact .zero
  have := charP_of_injective_ringHom h q; exact .prime hprime

中文:
引理 expChar_of_injective_ringHom
  证明: by
  rcases hR with _ | hprime
  · have := charZero_of_injective_ringHom h; exact .zero
  have := charP_of_injective_ringHom h q; exact .prime hprime

Depends on / 依赖: charP_of_injective_ringHom, charZero_of_injective_ringHom, hprime
-/
lemma expChar_of_injective_ringHom
    [NonAssocSemiring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f)
    (q : Nat) [hR : ExpChar R q] : ExpChar A q := by
  rcases hR with _ | hprime
  · have := charZero_of_injective_ringHom h; exact .zero
  have := charP_of_injective_ringHom h q; exact .prime hprime

/--
lemma `RingHom.expChar` / 引理 `RingHom.expChar`

English:
lemma RingHom.expChar
  statement: [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
  proof: by
  cases ‹ExpChar A p› with
  | zero => have := f.charZero; exact .zero
  | prime hp => have := f.charP H p; exact .prime hp

中文:
引理 环态射.expChar
  结论: [非结合半环 R] [非结合半环 A] (f : R ->+* A)
  证明: by
  cases ‹ExpChar A p› with
  | zero => have := f.charZero; exact .zero
  | prime hp => have := f.charP H p; exact .prime hp

Depends on / 依赖: ExpChar, R.carrier, Semiring, carrier, charZero, f.charP, f.charZero
-/
lemma RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
    (H : Function.Injective f) (p : Nat) [ExpChar A p] : ExpChar R p := by
  cases ‹ExpChar A p› with
  | zero => have := f.charZero; exact .zero
  | prime hp => have := f.charP H p; exact .prime hp

/--
lemma `RingHom.expChar_iff` / 引理 `RingHom.expChar_iff`

English:
lemma RingHom.expChar_iff
  statement: [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
  proof: ⟨fun _ => expChar_of_injective_ringHom H p, fun _ => f.expChar H p⟩

中文:
引理 环态射.expChar_iff
  结论: [非结合半环 R] [非结合半环 A] (f : R ->+* A)
  证明: ⟨fun _ => expChar_of_injective_ringHom H p, fun _ => f.expChar H p⟩

Depends on / 依赖: expChar, expChar_of_injective_ringHom, f.expChar
-/
lemma RingHom.expChar_iff [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A)
    (H : Function.Injective f) (p : Nat) : ExpChar R p ↔ ExpChar A p :=
  ⟨fun _ => expChar_of_injective_ringHom H p, fun _ => f.expChar H p⟩

/--
lemma `expChar_of_injective_algebraMap` / 引理 `expChar_of_injective_algebraMap`

English:
lemma expChar_of_injective_algebraMap
  statement: [CommSemiring R] [Semiring A] [Algebra R A]
  proof: expChar_of_injective_ringHom h q

中文:
引理 expChar_of_injective_algebraMap
  结论: [交换半环 R] [半环 A] [代数 R A]
  证明: expChar_of_injective_ringHom h q

Depends on / 依赖: expChar_of_injective_ringHom
-/
lemma expChar_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (q : Nat) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom h q

variable (R) in
/--
theorem `ExpChar.of_injective_algebraMap'` / 定理 `ExpChar.of_injective_algebraMap'`

English:
theorem ExpChar.of_injective_algebraMap'
  statement: [CommRing R] [CommRing A]
  proof: expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

中文:
定理 ExpChar.of_injective_algebraMap'
  结论: [交换环 R] [交换环 A]
  证明: expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, expChar_of_injective_ringHom
-/
theorem ExpChar.of_injective_algebraMap' [CommRing R] [CommRing A]
    [Algebra R A] [FaithfulSMul R A] (q : Nat) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

namespace Subfield

variable [DivisionRing R] (L : Subfield R) (p : Nat)

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: [CharP R p]
  body: L.subtype.charP L.subtype_injective p

中文:
实例 charP
  签名: [特征p R p]
  定义体: L.subtype.charP L.subtype_injective p

Depends on / 依赖: L.subtype.charP, L.subtype_injective, subtype, subtype_injective
-/
instance charP [CharP R p] : CharP L p := L.subtype.charP L.subtype_injective p
/--
Instance `expChar` / 实例 `expChar`

English:
instance expChar
  signature: [ExpChar R p]
  body: L.subtype.expChar L.subtype_injective p

中文:
实例 expChar
  签名: [ExpChar R p]
  定义体: L.subtype.expChar L.subtype_injective p

Depends on / 依赖: L.subtype.expChar, L.subtype_injective, expChar, subtype, subtype_injective
-/
instance expChar [ExpChar R p] : ExpChar L p := L.subtype.expChar L.subtype_injective p

end Subfield

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/

-- `CharP.charP_to_charZero A _ (charP_of_injective_algebraMap h 0)` does not work
-- here as it would require `Ring A`.
section QAlgebra

variable (R : Type*) [Nontrivial R]

/--
theorem `algebraRat.charP_zero` / 定理 `algebraRat.charP_zero`

English:
theorem algebraRat.charP_zero
  given: [Semiring R] [Algebra Rat R]
  statement: CharP R 0
  proof: charP_of_injective_algebraMap (algebraMap Rat R).injective 0

中文:
定理 algebraRat.charP_zero
  条件: [半环 R] [代数 有理数 R]
  结论: 特征p R 0
  证明: charP_of_injective_algebraMap (algebraMap Rat R).injective 0

Depends on / 依赖: algebraMap, charP_of_injective_algebraMap, injective
-/
theorem algebraRat.charP_zero [Semiring R] [Algebra Rat R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap Rat R).injective 0

/--
theorem `algebraRat.charZero` / 定理 `algebraRat.charZero`

English:
theorem algebraRat.charZero
  given: [Ring R] [Algebra Rat R]
  statement: CharZero R
  proof: @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

中文:
定理 algebraRat.charZero
  条件: [环 R] [代数 有理数 R]
  结论: 特征零 R
  证明: @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

Depends on / 依赖: CharP.charP_to_charZero, algebraRat, algebraRat.charP_zero, charP_to_charZero, charP_zero
-/
theorem algebraRat.charZero [Ring R] [Algebra Rat R] : CharZero R :=
  @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

end QAlgebra


/--
lemma `RingHom.charP_iff_charP` / 引理 `RingHom.charP_iff_charP`

English:
lemma RingHom.charP_iff_charP
  statement: {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
  proof: by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

中文:
引理 环态射.charP_iff_charP
  结论: {K L : 类型} [除环 K] [非结合半环 L] [非平凡 L]
  证明: by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

Depends on / 依赖: charP_iff, eq_iff, f.injective.eq_iff, injective, map_natCast, map_zero
-/
lemma RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
    (f : K ->+* L) (p : Nat) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

section

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

/--
theorem `Algebra.charP_iff` / 定理 `Algebra.charP_iff`

English:
theorem Algebra.charP_iff
  given: (p : Nat)
  statement: CharP K p ↔ CharP L p
  proof: (algebraMap K L).charP_iff_charP p

中文:
定理 代数.charP_iff
  条件: (p : 自然数)
  结论: 特征p K p ↔ 特征p L p
  证明: (algebraMap K L).charP_iff_charP p
-/
protected theorem Algebra.charP_iff (p : Nat) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p

/--
theorem `Algebra.ringChar_eq` / 定理 `Algebra.ringChar_eq`

English:
theorem Algebra.ringChar_eq
  statement: ringChar K = ringChar L
  proof: by
  rw [ringChar.eq_iff]; rw [Algebra.charP_iff K L]
  apply ringChar.charP

中文:
定理 代数.ringChar_eq
  结论: ringChar K = ringChar L
  证明: by
  rw [ringChar.eq_iff]; rw [Algebra.charP_iff K L]
  apply ringChar.charP

Depends on / 依赖: Algebra, Algebra.charP_iff, ConcreteCategory, ConcreteCategory.hom, RingCat, charP_iff, eq_iff, ringChar, ringChar.charP, ringChar.eq_iff
-/
theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff]; rw [Algebra.charP_iff K L]
  apply ringChar.charP

end

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R] (p : Nat)

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: [CharP R p]
  body: charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p

中文:
实例 charP
  签名: [特征p R p]
  定义体: charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p

Depends on / 依赖: FreeAlgebra, FreeAlgebra.algebraMap_leftInverse.injective, algebraMap_leftInverse, charP_of_injective_algebraMap, injective
-/
instance charP [CharP R p] : CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [CharZero R]
  body: charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective

中文:
实例 charZero
  签名: [特征零 R]
  定义体: charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective

Depends on / 依赖: FreeAlgebra, FreeAlgebra.algebraMap_leftInverse.injective, algebraMap_leftInverse, charZero_of_injective_algebraMap, f.hom, injective
-/
instance charZero [CharZero R] : CharZero (FreeAlgebra R X) :=
  charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective

end FreeAlgebra

namespace IsFractionRing

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (p : Nat)

/--
theorem `charP_of_isFractionRing` / 定理 `charP_of_isFractionRing`

English:
theorem charP_of_isFractionRing
  given: [CharP R p]
  statement: CharP K p
  proof: charP_of_injective_algebraMap (IsFractionRing.injective R K) p

中文:
定理 charP_of_isFractionRing
  条件: [特征p R p]
  结论: 特征p K p
  证明: charP_of_injective_algebraMap (IsFractionRing.injective R K) p

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, charP_of_injective_algebraMap, injective
-/
theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p

/--
theorem `charZero_of_isFractionRing` / 定理 `charZero_of_isFractionRing`

English:
theorem charZero_of_isFractionRing
  given: [CharZero R]
  statement: CharZero K
  proof: @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)

中文:
定理 charZero_of_isFractionRing
  条件: [特征零 R]
  结论: 特征零 K
  证明: @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)

Depends on / 依赖: CharP.charP_to_charZero, charP_of_isFractionRing, charP_to_charZero
-/
theorem charZero_of_isFractionRing [CharZero R] : CharZero K :=
  @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)

variable [IsDomain R]

/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: [CharP R p]
  body: charP_of_isFractionRing R p

中文:
实例 charP
  签名: [特征p R p]
  定义体: charP_of_isFractionRing R p

Depends on / 依赖: charP_of_isFractionRing
-/
instance charP [CharP R p] : CharP (FractionRing R) p :=
  charP_of_isFractionRing R p

/--
Instance `charZero` / 实例 `charZero`

English:
instance charZero
  signature: [CharZero R]
  body: charZero_of_isFractionRing R

中文:
实例 charZero
  签名: [特征零 R]
  定义体: charZero_of_isFractionRing R

Depends on / 依赖: charZero_of_isFractionRing
-/
instance charZero [CharZero R] : CharZero (FractionRing R) :=
  charZero_of_isFractionRing R

end IsFractionRing
