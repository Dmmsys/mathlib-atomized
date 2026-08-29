/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Cast.Prod
public import Mathlib.Data.ULift
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Ring.GrindInstances

/-!
# Characteristic of semirings

This file collects some fundamental results on the characteristic of rings that don't need the extra
imports of `Mathlib/Algebra/CharP/Lemmas.lean`.

As such, we can probably reorganize and find a better home for most of these lemmas.
-/

public section

assert_not_exists Finset TwoSidedIdeal

open Set

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : Nat)

variable [CharP R p] {a b : Nat}

/--
lemma `natCast_eq_natCast'` / 引理 `natCast_eq_natCast'`

English:
lemma natCast_eq_natCast'
  given: (h : a ≡ b [MOD p])
  statement: (a : R) = b
  proof: by
  wlog hle : a <= b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle]; rw [Nat.cast_add]; rw [(cast_eq_zero_iff R p _).mpr h]; rw [zero_add]

中文:
引理 natCast_eq_natCast'
  条件: (h : a ≡ b [MOD p])
  结论: (a : R) = b
  证明: by
  wlog hle : a <= b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle]; rw [Nat.cast_add]; rw [(cast_eq_zero_iff R p _).mpr h]; rw [zero_add]

Depends on / 依赖: Nat.cast_add, Nat.modEq_iff_dvd, Nat.sub_add_cancel, cast_add, cast_eq_zero_iff, h.symm, le_of_not_ge, modEq_iff_dvd, sub_add_cancel, zero_add
-/
lemma natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a <= b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle]; rw [Nat.cast_add]; rw [(cast_eq_zero_iff R p _).mpr h]; rw [zero_add]

/--
lemma `natCast_eq_natCast_mod` / 引理 `natCast_eq_natCast_mod`

English:
lemma natCast_eq_natCast_mod
  given: (a : Nat)
  statement: (a : R) = a % p
  proof: natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

中文:
引理 natCast_eq_natCast_mod
  条件: (a : 自然数)
  结论: (a : R) = a % p
  证明: natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

Depends on / 依赖: Nat.mod_modEq, mod_modEq, natCast_eq_natCast
-/
lemma natCast_eq_natCast_mod (a : Nat) : (a : R) = a % p :=
  natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

variable [IsRightCancelAdd R]

/--
lemma `natCast_eq_natCast` / 引理 `natCast_eq_natCast`

English:
lemma natCast_eq_natCast
  statement: (a : R) = b ↔ a ≡ b [MOD p]
  proof: by
  wlog hle : a <= b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle]; rw [← cast_eq_zero_iff R p (b - a)]; rw [← add_right_cancel_iff (G := R) (a := a) (b := b - a)]; rw [zero_add]; rw [← Nat.cast_add]; rw [Nat.sub_add_cancel hle]; rw [eq_comm]

中文:
引理 natCast_eq_natCast
  结论: (a : R) = b ↔ a ≡ b [MOD p]
  证明: by
  wlog hle : a <= b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle]; rw [← cast_eq_zero_iff R p (b - a)]; rw [← add_right_cancel_iff (G := R) (a := a) (b := b - a)]; rw [zero_add]; rw [← Nat.cast_add]; rw [Nat.sub_add_cancel hle]; rw [eq_comm]

Depends on / 依赖: Nat.ModEq.comm, Nat.cast_add, Nat.modEq_iff_dvd, Nat.sub_add_cancel, add_right_cancel_iff, cast_add, cast_eq_zero_iff, eq_comm, le_of_not_ge, modEq_iff_dvd, sub_add_cancel, zero_add
-/
lemma natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a <= b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle]; rw [← cast_eq_zero_iff R p (b - a)]; rw [← add_right_cancel_iff (G := R) (a := a) (b := b - a)]; rw [zero_add]; rw [← Nat.cast_add]; rw [Nat.sub_add_cancel hle]; rw [eq_comm]

/--
lemma `natCast_injOn_Iio` / 引理 `natCast_injOn_Iio`

English:
lemma natCast_injOn_Iio
  statement: (Set.Iio p).InjOn ((↑) : Nat -> R)
  proof: fun _a ha _b hb hab => ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

中文:
引理 natCast_injOn_Iio
  结论: (Set.Iio p).InjOn ((↑) : 自然数 -> R)
  证明: fun _a ha _b hb hab => ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

Depends on / 依赖: eq_of_lt_of_lt, natCast_eq_natCast
-/
lemma natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : Nat -> R) :=
  fun _a ha _b hb hab => ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : Nat) [CharP R p] {a b : Int}

/--
lemma `intCast_eq_intCast` / 引理 `intCast_eq_intCast`

English:
lemma intCast_eq_intCast
  statement: (a : R) = b ↔ a ≡ b [ZMOD p]
  proof: by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← Int.cast_sub]; rw [CharP.intCast_eq_zero_iff R p]; rw [Int.modEq_iff_dvd]

中文:
引理 intCast_eq_intCast
  结论: (a : R) = b ↔ a ≡ b [ZMOD p]
  证明: by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← Int.cast_sub]; rw [CharP.intCast_eq_zero_iff R p]; rw [Int.modEq_iff_dvd]

Depends on / 依赖: CharP.intCast_eq_zero_iff, Int.cast_sub, Int.modEq_iff_dvd, cast_sub, eq_comm, intCast_eq_zero_iff, modEq_iff_dvd, sub_eq_zero
-/
lemma intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← Int.cast_sub]; rw [CharP.intCast_eq_zero_iff R p]; rw [Int.modEq_iff_dvd]

/--
lemma `intCast_eq_intCast_mod` / 引理 `intCast_eq_intCast_mod`

English:
lemma intCast_eq_intCast_mod
  statement: (a : R) = a % (p : Int)
  proof: (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

中文:
引理 intCast_eq_intCast_mod
  结论: (a : R) = a % (p : 整数)
  证明: (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

Depends on / 依赖: CharP.intCast_eq_intCast, Int.mod_modEq, intCast_eq_intCast, mod_modEq
-/
lemma intCast_eq_intCast_mod : (a : R) = a % (p : Int) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

/--
lemma `intCast_injOn_Ico` / 引理 `intCast_injOn_Ico`

English:
lemma intCast_injOn_Ico
  given: [IsRightCancelAdd R]
  statement: InjOn (Int.cast : Int -> R) (Ico 0 p)
  proof: by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to Nat using ha₀
  lift b to Nat using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

中文:
引理 intCast_injOn_Ico
  条件: [IsRightCancelAdd R]
  结论: InjOn (整数.cast : 整数 -> R) (Ico 0 p)
  证明: by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to Nat using ha₀
  lift b to Nat using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

Depends on / 依赖: natCast_injOn_Iio
-/
lemma intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : Int -> R) (Ico 0 p) := by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to Nat using ha₀
  lift b to Nat using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

end AddGroupWithOne
end CharP

namespace CharP

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

variable (R) in
/--
lemma `cast_ne_zero_of_ne_of_prime` / 引理 `cast_ne_zero_of_ne_of_prime`

English:
lemma cast_ne_zero_of_ne_of_prime
  statement: [Nontrivial R]
  proof: fun h => by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with rfl | h
  · exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h

中文:
引理 cast_ne_zero_of_ne_of_prime
  结论: [Nontrivial R]
  证明: fun h => by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with rfl | h
  · exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h

Depends on / 依赖: cast_eq_zero_iff, eq_one_or_self_of_dvd, false_of_nontrivial_of_char_one, hq.eq_one_or_self_of_dvd
-/
lemma cast_ne_zero_of_ne_of_prime [Nontrivial R]
    {p q : Nat} [CharP R p] (hq : q.Prime) (hneq : p != q) : (q : R) != 0 := fun h => by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with rfl | h
  · exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h

/--
lemma `ringChar_of_prime_eq_zero` / 引理 `ringChar_of_prime_eq_zero`

English:
lemma ringChar_of_prime_eq_zero
  statement: [Nontrivial R] {p : Nat} (hprime : Nat.Prime p)
  proof: Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

中文:
引理 ringChar_of_prime_eq_zero
  结论: [Nontrivial R] {p : 自然数} (hprime : 自然数.Prime p)
  证明: Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

Depends on / 依赖: Nat.dvd_prime, Or.resolve_left, dvd_prime, hprime, resolve_left, ringChar, ringChar.dvd, ringChar_ne_one
-/
lemma ringChar_of_prime_eq_zero [Nontrivial R] {p : Nat} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

/--
lemma `charP_iff_prime_eq_zero` / 引理 `charP_iff_prime_eq_zero`

English:
lemma charP_iff_prime_eq_zero
  given: [Nontrivial R] {p : Nat} (hp : p.Prime)
  proof: ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

中文:
引理 charP_iff_prime_eq_zero
  条件: [Nontrivial R] {p : 自然数} (hp : p.Prime)
  证明: ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

Depends on / 依赖: R.carrier, carrier, cast_eq_zero, ringChar_of_prime_eq_zero
-/
lemma charP_iff_prime_eq_zero [Nontrivial R] {p : Nat} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring
end CharP

section

/--
lemma `Ring.two_ne_zero` / 引理 `Ring.two_ne_zero`

English:
lemma Ring.two_ne_zero
  statement: {R : Type*} [NonAssocSemiring R] [Nontrivial R]
  proof: by
  rw [Ne]; rw [(by norm_cast : (2 : R) = (2 : Nat))]; rw [ringChar.spec]; rw [Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one

中文:
引理 Ring.two_ne_zero
  结论: {R : 类型} [NonAssocSemiring R] [Nontrivial R]
  证明: by
  rw [Ne]; rw [(by norm_cast : (2 : R) = (2 : Nat))]; rw [ringChar.spec]; rw [Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one
-/
protected lemma Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R != 2) : (2 : R) != 0 := by
  rw [Ne]; rw [(by norm_cast : (2 : R) = (2 : Nat))]; rw [ringChar.spec]; rw [Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one

-- We have `CharP.neg_one_ne_one`, which assumes `[Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)]`.
-- This is a version using `ringChar` instead.
/--
lemma `Ring.neg_one_ne_one_of_char_ne_two` / 引理 `Ring.neg_one_ne_one_of_char_ne_two`

English:
lemma Ring.neg_one_ne_one_of_char_ne_two
  statement: {R : Type*} [NonAssocRing R] [Nontrivial R]
  proof: fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)

中文:
引理 Ring.neg_one_ne_one_of_char_ne_two
  结论: {R : 类型} [NonAssocRing R] [Nontrivial R]
  证明: fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)
-/
lemma Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R != 2) : (-1 : R) != 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)

/--
lemma `Ring.eq_self_iff_eq_zero_of_char_ne_two` / 引理 `Ring.eq_self_iff_eq_zero_of_char_ne_two`

English:
lemma Ring.eq_self_iff_eq_zero_of_char_ne_two
  statement: {R : Type*} [NonAssocRing R] [Nontrivial R]
  proof: ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

中文:
引理 Ring.eq_self_iff_eq_zero_of_char_ne_two
  结论: {R : 类型} [NonAssocRing R] [Nontrivial R]
  证明: ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

Depends on / 依赖: Ring.two_ne_zero, congr_arg, h.symm, mul_eq_zero, mul_eq_zero.mp, neg_eq_iff_add_eq_zero, neg_eq_iff_add_eq_zero.mp, neg_zero, resolve_left, two_mul, two_ne_zero
-/
lemma Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R != 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

end

section Prod
variable (S : Type*) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : Nat) [CharP R p]

/--
Instance `Nat.lcm.charP` / 实例 `Nat.lcm.charP`

English:
instance Nat.lcm.charP
  signature: [CharP S q]
  body: by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

中文:
实例 Nat.lcm.charP
  签名: [CharP S q]
  定义体: by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.lcm_dvd_iff, Prod.ext_iff, cast_eq_zero_iff, ext_iff, lcm_dvd_iff
-/
instance Nat.lcm.charP [CharP S q] : CharP (R × S) (Nat.lcm p q) where
  cast_eq_zero_iff := by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

/--
Instance `Prod.charP` / 实例 `Prod.charP`

English:
instance Prod.charP
  signature: [CharP S p]
  body: by
  convert! Nat.lcm.charP R S p p; simp

中文:
实例 Prod.charP
  签名: [CharP S p]
  定义体: by
  convert! Nat.lcm.charP R S p p; simp

Depends on / 依赖: Nat.lcm.charP, convert
-/
instance Prod.charP [CharP S p] : CharP (R × S) p := by
  convert! Nat.lcm.charP R S p p; simp

/--
Instance `Prod.charZero_of_left` / 实例 `Prod.charZero_of_left`

English:
instance Prod.charZero_of_left
  signature: [CharZero R]
  body: CharZero.cast_injective congr(Prod.fst $h)

中文:
实例 Prod.charZero_of_left
  签名: [CharZero R]
  定义体: CharZero.cast_injective congr(Prod.fst $h)

Depends on / 依赖: CharZero, CharZero.cast_injective, Prod.fst, cast_injective
-/
instance Prod.charZero_of_left [CharZero R] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.fst $h)

/--
Instance `Prod.charZero_of_right` / 实例 `Prod.charZero_of_right`

English:
instance Prod.charZero_of_right
  signature: [CharZero S]
  body: CharZero.cast_injective congr(Prod.snd $h)

中文:
实例 Prod.charZero_of_right
  签名: [CharZero S]
  定义体: CharZero.cast_injective congr(Prod.snd $h)

Depends on / 依赖: CharZero, CharZero.cast_injective, Prod.snd, cast_injective
-/
instance Prod.charZero_of_right [CharZero S] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.snd $h)

end Prod

/--
Instance `ULift.charP` / 实例 `ULift.charP`

English:
instance ULift.charP
  signature: [AddMonoidWithOne R] (p : Nat) [CharP R p]
  body: Iff.trans ULift.ext_iff CharP.cast_eq_zero_iff R p n

中文:
实例 ULift.charP
  签名: [AddMonoidWithOne R] (p : 自然数) [CharP R p]
  定义体: Iff.trans ULift.ext_iff CharP.cast_eq_zero_iff R p n

Depends on / 依赖: CharP.cast_eq_zero_iff, Iff.trans, ULift.ext_iff, cast_eq_zero_iff, ext_iff
-/
instance ULift.charP [AddMonoidWithOne R] (p : Nat) [CharP R p] : CharP (ULift R) p where
cast_eq_zero_iff n := Iff.trans ULift.ext_iff CharP.cast_eq_zero_iff R p n

/--
Instance `MulOpposite.charP` / 实例 `MulOpposite.charP`

English:
instance MulOpposite.charP
  signature: [AddMonoidWithOne R] (p : Nat) [CharP R p]
  body: MulOpposite.unop_inj.symm.trans CharP.cast_eq_zero_iff R p n

中文:
实例 MulOpposite.charP
  签名: [AddMonoidWithOne R] (p : 自然数) [CharP R p]
  定义体: MulOpposite.unop_inj.symm.trans CharP.cast_eq_zero_iff R p n

Depends on / 依赖: CharP.cast_eq_zero_iff, MulOpposite, MulOpposite.unop_inj.symm.trans, cast_eq_zero_iff, unop_inj
-/
instance MulOpposite.charP [AddMonoidWithOne R] (p : Nat) [CharP R p] : CharP Rᵐᵒᵖ p where
cast_eq_zero_iff n := MulOpposite.unop_inj.symm.trans CharP.cast_eq_zero_iff R p n

section

/--
lemma `Int.cast_injOn_of_ringChar_ne_two` / 引理 `Int.cast_injOn_of_ringChar_ne_two`

English:
lemma Int.cast_injOn_of_ringChar_ne_two
  statement: {R : Type*} [NonAssocRing R] [Nontrivial R]
  proof: by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

中文:
引理 Int.cast_injOn_of_ringChar_ne_two
  结论: {R : 类型} [NonAssocRing R] [Nontrivial R]
  证明: by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

Depends on / 依赖: Ring.neg_one_ne_one_of_char_ne_two, cast_neg, cast_one, cast_zero, neg_eq_zero, neg_one_ne_one_of_char_ne_two, one_ne_zero, zero_eq_neg, zero_ne_one
-/
lemma Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R != 2) : ({0, 1, -1} : Set Int).InjOn ((↑) : Int -> R) := by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

end

namespace CharZero

/--
lemma `charZero_iff_forall_prime_ne_zero` / 引理 `charZero_iff_forall_prime_ne_zero`

English:
lemma charZero_iff_forall_prime_ne_zero
  given: [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R]
  proof: by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

中文:
引理 charZero_iff_forall_prime_ne_zero
  条件: [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R]
  证明: by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

Depends on / 依赖: CharP.charP_to_charZero, CharP.char_is_prime_or_zero, charP_to_charZero, char_is_prime_or_zero, hp.ne_zero, ne_zero, ringChar
-/
lemma charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ forall p : Nat, p.Prime -> (p : R) != 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

end CharZero

namespace Fin

open Fin.NatCast

/-- The characteristic of `F_p` is `p`. -/
@[stacks 09FS "First part. We don't require `p` to be a prime in mathlib."]
/--
Instance `charP` / 实例 `charP`

English:
instance charP
  signature: (n : Nat) [NeZero n]
  body: natCast_eq_zero

中文:
实例 charP
  签名: (n : 自然数) [NeZero n]
  定义体: natCast_eq_zero

Depends on / 依赖: CommSemiRingCat, ConcreteCategory, ConcreteCategory.hom, natCast_eq_zero
-/
instance charP (n : Nat) [NeZero n] : CharP (Fin n) n where cast_eq_zero_iff _ := natCast_eq_zero

end Fin

section AddMonoidWithOne
variable [AddMonoidWithOne R]

instance (S : Type*) [Semiring S] (p) [ExpChar R p] [ExpChar S p] : ExpChar (R × S) p := by
  obtain hp | ⟨hp⟩ := ‹ExpChar R p›
  · constructor
  obtain _ | _ := ‹ExpChar S p›
  · exact (Nat.not_prime_one hp).elim
  · have := Prod.charP R S p; exact .prime hp

end AddMonoidWithOne

section CommRing

instance (α : Type*) [Semiring α] [IsLeftCancelAdd α] (n : Nat) [CharP α n] :
    Lean.Grind.IsCharP α n where
  ofNat_ext_iff {a b} := by
    rw [Lean.Grind.Semiring.ofNat_eq_natCast]; rw [Lean.Grind.Semiring.ofNat_eq_natCast]
    exact CharP.cast_eq_iff_mod_eq α n

end CommRing
