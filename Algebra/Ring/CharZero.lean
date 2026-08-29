/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Characteristic zero rings
-/

@[expose] public section

assert_not_exists Field

open Function Set

variable {α R S : Type*} {n : Nat}

section AddMonoidWithOne
variable [AddMonoidWithOne R] [CharZero R]

/-- `Nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
/--
Definition of `Nat.castEmbedding` / `Nat.castEmbedding` 的定义

English:
definition Nat.castEmbedding
  signature: : Nat ↪ R
  body: ⟨Nat.cast, cast_injective⟩

中文:
定义 Nat.castEmbedding
  签名: : 自然数 ↪ R
  定义体: ⟨Nat.cast, cast_injective⟩

Depends on / 依赖: Nat.cast, cast_injective
-/
def Nat.castEmbedding : Nat ↪ R := ⟨Nat.cast, cast_injective⟩

/--
Instance `CharZero.NeZero.two` / 实例 `CharZero.NeZero.two`

English:
instance CharZero.NeZero.two
  signature: : NeZero (2 : R) where
  body: by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

中文:
实例 CharZero.NeZero.two
  签名: : NeZero (2 : R) where
  定义体: by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

Depends on / 依赖: Nat.cast_ne_zero, Nat.cast_two, cast_ne_zero, cast_two
-/
instance CharZero.NeZero.two : NeZero (2 : R) where
  out := by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

namespace Function

/--
lemma `support_natCast` / 引理 `support_natCast`

English:
lemma support_natCast
  given: (hn : n != 0)
  statement: support (n : α -> R) = univ
  proof: support_const Nat.cast_ne_zero.2 hn

中文:
引理 support_natCast
  条件: (hn : n != 0)
  结论: support (n : α -> R) = univ
  证明: support_const Nat.cast_ne_zero.2 hn

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, support_const
-/
lemma support_natCast (hn : n != 0) : support (n : α -> R) = univ :=
support_const Nat.cast_ne_zero.2 hn

/--
lemma `mulSupport_natCast` / 引理 `mulSupport_natCast`

English:
lemma mulSupport_natCast
  given: (hn : n != 1)
  statement: mulSupport (n : α -> R) = univ
  proof: mulSupport_const Nat.cast_ne_one.2 hn

中文:
引理 mulSupport_natCast
  条件: (hn : n != 1)
  结论: mulSupport (n : α -> R) = univ
  证明: mulSupport_const Nat.cast_ne_one.2 hn

Depends on / 依赖: Nat.cast_ne_one, cast_ne_one, mulSupport_const
-/
lemma mulSupport_natCast (hn : n != 1) : mulSupport (n : α -> R) = univ :=
mulSupport_const Nat.cast_ne_one.2 hn

end Function
end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R] [NonAssocSemiring S]

namespace RingHom

/--
lemma `charZero` / 引理 `charZero`

English:
lemma charZero
  given: (ϕ : R ->+* S) [CharZero S]
  statement: CharZero R where
  proof: CharZero.cast_injective (R := S) by
    rw [← map_natCast ϕ]; rw [← map_natCast ϕ]; rw [h]

中文:
引理 charZero
  条件: (ϕ : R ->+* S) [CharZero S]
  结论: CharZero R where
  证明: CharZero.cast_injective (R := S) by
    rw [← map_natCast ϕ]; rw [← map_natCast ϕ]; rw [h]

Depends on / 依赖: CharZero, CharZero.cast_injective, cast_injective, map_natCast
-/
lemma charZero (ϕ : R ->+* S) [CharZero S] : CharZero R where
cast_injective a b h := CharZero.cast_injective (R := S) by
    rw [← map_natCast ϕ]; rw [← map_natCast ϕ]; rw [h]

/--
lemma `charZero_iff` / 引理 `charZero_iff`

English:
lemma charZero_iff
  given: {ϕ : R ->+* S} (hϕ : Injective ϕ)
  statement: CharZero R ↔ CharZero S
  proof: ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩

中文:
引理 charZero_iff
  条件: {ϕ : R ->+* S} (hϕ : Injective ϕ)
  结论: CharZero R ↔ CharZero S
  证明: ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩

Depends on / 依赖: Nat.cast_inj, cast_inj, charZero, eq_iff, map_natCast
-/
lemma charZero_iff {ϕ : R ->+* S} (hϕ : Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩

/--
lemma `injective_nat` / 引理 `injective_nat`

English:
lemma injective_nat
  given: (f : Nat ->+* R) [CharZero R]
  statement: Injective f
  proof: Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

中文:
引理 injective_nat
  条件: (f : 自然数 ->+* R) [CharZero R]
  结论: Injective f
  证明: Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

Depends on / 依赖: Nat.castRingHom, Nat.cast_injective, Subsingleton, Subsingleton.elim, castRingHom, cast_injective
-/
lemma injective_nat (f : Nat ->+* R) [CharZero R] : Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

end RingHom

variable [NoZeroDivisors R] [CharZero R] {a : R}

@[simp]
/--
theorem `add_self_eq_zero` / 定理 `add_self_eq_zero`

English:
theorem add_self_eq_zero
  given: {a : R}
  statement: a + a = 0 ↔ a = 0
  proof: by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

中文:
定理 add_self_eq_zero
  条件: {a : R}
  结论: a + a = 0 ↔ a = 0
  证明: by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

Depends on / 依赖: false_or, mul_eq_zero, two_mul, two_ne_zero
-/
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

end NonAssocSemiring

section Semiring
variable [Semiring R] [CharZero R]

/--
lemma `Nat.cast_pow_eq_one` / 引理 `Nat.cast_pow_eq_one`

English:
lemma Nat.cast_pow_eq_one
  given: {a : Nat} (hn : n != 0)
  statement: (a : R) ^ n = 1 ↔ a = 1
  proof: by
  simp [← cast_pow, cast_eq_one, hn]

中文:
引理 Nat.cast_pow_eq_one
  条件: {a : 自然数} (hn : n != 0)
  结论: (a : R) ^ n = 1 ↔ a = 1
  证明: by
  simp [← cast_pow, cast_eq_one, hn]
-/
@[simp] lemma Nat.cast_pow_eq_one {a : Nat} (hn : n != 0) : (a : R) ^ n = 1 ↔ a = 1 := by
  simp [← cast_pow, cast_eq_one, hn]

variable [IsCancelMulZero R]

/-- A characteristic zero domain is torsion-free. -/
instance (priority := 100) IsAddTorsionFree.of_isCancelMulZero_charZero : IsAddTorsionFree R where
  nsmul_right_injective n hn a b hab := by simpa [hn] using hab

end Semiring

section NonAssocRing
variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

-- `scoped` attribute here and below because the `simp` keys are weak
-- (see https://github.com/leanprover-community/mathlib4/pull/15631)
/--
theorem `CharZero.neg_eq_self_iff` / 定理 `CharZero.neg_eq_self_iff`

English:
theorem CharZero.neg_eq_self_iff
  given: {a : R}
  statement: -a = a ↔ a = 0
  proof: neg_eq_iff_add_eq_zero.trans add_self_eq_zero

中文:
定理 CharZero.neg_eq_self_iff
  条件: {a : R}
  结论: -a = a ↔ a = 0
  证明: neg_eq_iff_add_eq_zero.trans add_self_eq_zero
-/
@[scoped simp] theorem CharZero.neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero

/--
theorem `CharZero.eq_neg_self_iff` / 定理 `CharZero.eq_neg_self_iff`

English:
theorem CharZero.eq_neg_self_iff
  given: {a : R}
  statement: a = -a ↔ a = 0
  proof: eq_neg_iff_add_eq_zero.trans add_self_eq_zero

中文:
定理 CharZero.eq_neg_self_iff
  条件: {a : R}
  结论: a = -a ↔ a = 0
  证明: eq_neg_iff_add_eq_zero.trans add_self_eq_zero

Depends on / 依赖: IsAffine, IsAffine.affine, affine
-/
@[scoped simp] theorem CharZero.eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero

/--
theorem `nat_mul_inj` / 定理 `nat_mul_inj`

English:
theorem nat_mul_inj
  given: {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b)
  statement: n = 0 ∨ a = b
  proof: by
  rw [← sub_eq_zero]; rw [← mul_sub]; rw [mul_eq_zero]; rw [sub_eq_zero] at h
  exact mod_cast h

中文:
定理 nat_mul_inj
  条件: {n : 自然数} {a b : R} (h : (n : R) * a = (n : R) * b)
  结论: n = 0 ∨ a = b
  证明: by
  rw [← sub_eq_zero]; rw [← mul_sub]; rw [mul_eq_zero]; rw [sub_eq_zero] at h
  exact mod_cast h

Depends on / 依赖: mod_cast, mul_eq_zero, mul_sub, sub_eq_zero
-/
theorem nat_mul_inj {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero]; rw [← mul_sub]; rw [mul_eq_zero]; rw [sub_eq_zero] at h
  exact mod_cast h

/--
theorem `nat_mul_inj'` / 定理 `nat_mul_inj'`

English:
theorem nat_mul_inj'
  given: {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n != 0)
  statement: a = b
  proof: by
  simpa [w] using nat_mul_inj h

中文:
定理 nat_mul_inj'
  条件: {n : 自然数} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n != 0)
  结论: a = b
  证明: by
  simpa [w] using nat_mul_inj h

Depends on / 依赖: nat_mul_inj
-/
theorem nat_mul_inj' {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n != 0) : a = b := by
  simpa [w] using nat_mul_inj h

end NonAssocRing

section Ring
variable [Ring R] [CharZero R]

@[simp]
/--
theorem `units_ne_neg_self` / 定理 `units_ne_neg_self`

English:
theorem units_ne_neg_self
  given: (u : Rˣ)
  statement: u != -u
  proof: by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]

中文:
定理 units_ne_neg_self
  条件: (u : Rˣ)
  结论: u != -u
  证明: by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]

Depends on / 依赖: Units.ext_iff, Units.mul_left_eq_zero, Units.val_neg, eq_neg_iff_add_eq_zero, ext_iff, mul_left_eq_zero, ne_eq, not_false_iff, simp_rw, two_mul, two_ne_zero, val_neg
-/
theorem units_ne_neg_self (u : Rˣ) : u != -u := by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]
/--
theorem `neg_units_ne_self` / 定理 `neg_units_ne_self`

English:
theorem neg_units_ne_self
  given: (u : Rˣ)
  statement: -u != u
  proof: (units_ne_neg_self u).symm

中文:
定理 neg_units_ne_self
  条件: (u : Rˣ)
  结论: -u != u
  证明: (units_ne_neg_self u).symm

Depends on / 依赖: units_ne_neg_self
-/
theorem neg_units_ne_self (u : Rˣ) : -u != u := (units_ne_neg_self u).symm

end Ring
