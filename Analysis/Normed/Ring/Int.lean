/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

public section


namespace Int

/--
theorem `nnnorm_coe_units` / 定理 `nnnorm_coe_units`

English:
theorem nnnorm_coe_units
  given: (e : Intˣ)
  statement: ‖(e : Int)‖₊ = 1
  proof: by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

中文:
定理 nnnorm_coe_units
  条件: (e : 整数ˣ)
  结论: ‖(e : 整数)‖₊ = 1
  证明: by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

Depends on / 依赖: Units.coe_neg_one, Units.val_one, coe_neg_one, nnnorm_neg, nnnorm_one, units_eq_one_or, val_one
-/
theorem nnnorm_coe_units (e : Intˣ) : ‖(e : Int)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

/--
theorem `norm_coe_units` / 定理 `norm_coe_units`

English:
theorem norm_coe_units
  given: (e : Intˣ)
  statement: ‖(e : Int)‖ = 1
  proof: by
  rw [← coe_nnnorm]; rw [nnnorm_coe_units]; rw [NNReal.coe_one]

@[simp]

中文:
定理 norm_coe_units
  条件: (e : 整数ˣ)
  结论: ‖(e : 整数)‖ = 1
  证明: by
  rw [← coe_nnnorm]; rw [nnnorm_coe_units]; rw [NNReal.coe_one]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_one, coe_nnnorm, coe_one, nnnorm_coe_units
-/
theorem norm_coe_units (e : Intˣ) : ‖(e : Int)‖ = 1 := by
  rw [← coe_nnnorm]; rw [nnnorm_coe_units]; rw [NNReal.coe_one]

@[simp]
/--
theorem `nnnorm_natCast` / 定理 `nnnorm_natCast`

English:
theorem nnnorm_natCast
  given: (n : Nat)
  statement: ‖(n : Int)‖₊ = n
  proof: Real.nnnorm_natCast _

中文:
定理 nnnorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 整数)‖₊ = n
  证明: Real.nnnorm_natCast _

Depends on / 依赖: Real.nnnorm_natCast, nnnorm_natCast
-/
theorem nnnorm_natCast (n : Nat) : ‖(n : Int)‖₊ = n :=
  Real.nnnorm_natCast _

/--
lemma `enorm_natCast` / 引理 `enorm_natCast`

English:
lemma enorm_natCast
  given: (n : Nat)
  statement: ‖(n : Int)‖ₑ = n
  proof: Real.enorm_natCast _

@[simp]

中文:
引理 enorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 整数)‖ₑ = n
  证明: Real.enorm_natCast _

@[simp]
-/
@[simp] lemma enorm_natCast (n : Nat) : ‖(n : Int)‖ₑ = n := Real.enorm_natCast _

@[simp]
/--
theorem `toNat_add_toNat_neg_eq_nnnorm` / 定理 `toNat_add_toNat_neg_eq_nnnorm`

English:
theorem toNat_add_toNat_neg_eq_nnnorm
  given: (n : Int)
  statement: ↑n.toNat + ↑(-n).toNat = ‖n‖₊
  proof: by
  rw [← Nat.cast_add]; rw [toNat_add_toNat_neg_eq_natAbs]; rw [NNReal.natCast_natAbs]

@[simp]

中文:
定理 to自然数_add_to自然数_neg_eq_nnnorm
  条件: (n : 整数)
  结论: ↑n.to自然数 + ↑(-n).to自然数 = ‖n‖₊
  证明: by
  rw [← Nat.cast_add]; rw [toNat_add_toNat_neg_eq_natAbs]; rw [NNReal.natCast_natAbs]

@[simp]

Depends on / 依赖: NNReal, NNReal.natCast_natAbs, Nat.cast_add, cast_add, natCast_natAbs, toNat_add_toNat_neg_eq_natAbs
-/
theorem toNat_add_toNat_neg_eq_nnnorm (n : Int) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add]; rw [toNat_add_toNat_neg_eq_natAbs]; rw [NNReal.natCast_natAbs]

@[simp]
/--
theorem `toNat_add_toNat_neg_eq_norm` / 定理 `toNat_add_toNat_neg_eq_norm`

English:
theorem toNat_add_toNat_neg_eq_norm
  given: (n : Int)
  statement: ↑n.toNat + ↑(-n).toNat = ‖n‖
  proof: by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

中文:
定理 to自然数_add_to自然数_neg_eq_norm
  条件: (n : 整数)
  结论: ↑n.to自然数 + ↑(-n).to自然数 = ‖n‖
  证明: by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

Depends on / 依赖: NNReal, NNReal.coe_add, NNReal.coe_natCast, NNReal.toReal, coe_add, coe_natCast, toNat_add_toNat_neg_eq_nnnorm, toReal
-/
theorem toNat_add_toNat_neg_eq_norm (n : Int) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

end Int
