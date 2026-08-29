/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.Rify
public import Qq

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

@[expose] public section

noncomputable section

open Real NNReal ENNReal ComplexConjugate Finset Function Set

namespace NNReal
variable {x : Real>=0} {w y z : Real}

/--
Definition of `rpow` / `rpow` 的定义

English:
definition rpow
  signature: (x : Real>=0) (y : Real)
  body: ⟨(x : Real) ^ y, Real.rpow_nonneg x.2 y⟩

中文:
定义 rpow
  签名: (x : 实数>=0) (y : 实数)
  定义体: ⟨(x : Real) ^ y, Real.rpow_nonneg x.2 y⟩

Depends on / 依赖: Hom.ext, Modification, Modification.ext, Real.rpow_nonneg, rpow_nonneg
-/
noncomputable def rpow (x : Real>=0) (y : Real) : Real>=0 :=
  ⟨(x : Real) ^ y, Real.rpow_nonneg x.2 y⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow Real>=0 Real
  body: ⟨rpow⟩

@[simp]

中文:
实例 :
  签名: 幂 实数>=0 实数
  定义体: ⟨rpow⟩

@[simp]
-/
noncomputable instance : Pow Real>=0 Real :=
  ⟨rpow⟩

@[simp]
/--
theorem `rpow_eq_pow` / 定理 `rpow_eq_pow`

English:
theorem rpow_eq_pow
  given: (x : Real>=0) (y : Real)
  statement: rpow x y = x ^ y
  proof: rfl

@[simp, norm_cast]

中文:
定理 rpow_eq_pow
  条件: (x : 实数>=0) (y : 实数)
  结论: rpow x y = x ^ y
  证明: rfl

@[simp, norm_cast]
-/
theorem rpow_eq_pow (x : Real>=0) (y : Real) : rpow x y = x ^ y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_rpow` / 定理 `coe_rpow`

English:
theorem coe_rpow
  given: (x : Real>=0) (y : Real)
  statement: ((x ^ y : Real>=0) : Real) = (x : Real) ^ y
  proof: rfl

@[simp]

中文:
定理 coe_rpow
  条件: (x : 实数>=0) (y : 实数)
  结论: ((x ^ y : 实数>=0) : 实数) = (x : 实数) ^ y
  证明: rfl

@[simp]
-/
theorem coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) : Real) = (x : Real) ^ y :=
  rfl

@[simp]
/--
theorem `rpow_zero` / 定理 `rpow_zero`

English:
theorem rpow_zero
  given: (x : Real>=0)
  statement: x ^ (0 : Real) = 1
  proof: NNReal.eq Real.rpow_zero _

中文:
定理 rpow_zero
  条件: (x : 实数>=0)
  结论: x ^ (0 : 实数) = 1
  证明: NNReal.eq Real.rpow_zero _

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_zero, rpow_zero
-/
theorem rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1 :=
NNReal.eq Real.rpow_zero _

/--
theorem `rpow_zero_pos` / 定理 `rpow_zero_pos`

English:
theorem rpow_zero_pos
  given: (x : Real>=0)
  statement: 0 < x ^ (0 : Real)
  proof: by rw [rpow_zero]; exact one_pos

@[simp]

中文:
定理 rpow_zero_pos
  条件: (x : 实数>=0)
  结论: 0 < x ^ (0 : 实数)
  证明: by rw [rpow_zero]; exact one_pos

@[simp]

Depends on / 依赖: one_pos, rpow_zero
-/
theorem rpow_zero_pos (x : Real>=0) : 0 < x ^ (0 : Real) := by rw [rpow_zero]; exact one_pos

@[simp]
/--
theorem `rpow_eq_zero_iff` / 定理 `rpow_eq_zero_iff`

English:
theorem rpow_eq_zero_iff
  given: {x : Real>=0} {y : Real}
  statement: x ^ y = 0 ↔ x = 0 ∧ y != 0
  proof: by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2

中文:
定理 rpow_eq_zero_iff
  条件: {x : 实数>=0} {y : 实数}
  结论: x ^ y = 0 ↔ x = 0 ∧ y != 0
  证明: by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2

Depends on / 依赖: NNReal, NNReal.coe_eq_zero, NNReal.coe_inj, Real.rpow_eq_zero_iff_of_nonneg, coe_eq_zero, coe_inj, coe_rpow, rpow_eq_zero_iff_of_nonneg
-/
theorem rpow_eq_zero_iff {x : Real>=0} {y : Real} : x ^ y = 0 ↔ x = 0 ∧ y != 0 := by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2

/--
lemma `rpow_eq_zero` / 引理 `rpow_eq_zero`

English:
lemma rpow_eq_zero
  given: (hy : y != 0)
  statement: x ^ y = 0 ↔ x = 0
  proof: by simp [hy]

@[simp]

中文:
引理 rpow_eq_zero
  条件: (hy : y != 0)
  结论: x ^ y = 0 ↔ x = 0
  证明: by simp [hy]

@[simp]
-/
lemma rpow_eq_zero (hy : y != 0) : x ^ y = 0 ↔ x = 0 := by simp [hy]

@[simp]
/--
theorem `zero_rpow` / 定理 `zero_rpow`

English:
theorem zero_rpow
  given: {x : Real} (h : x != 0)
  statement: (0 : Real>=0) ^ x = 0
  proof: NNReal.eq Real.zero_rpow h

中文:
定理 zero_rpow
  条件: {x : 实数} (h : x != 0)
  结论: (0 : 实数>=0) ^ x = 0
  证明: NNReal.eq Real.zero_rpow h

Depends on / 依赖: NNReal, NNReal.eq, Real.zero_rpow, zero_rpow
-/
theorem zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x = 0 :=
NNReal.eq Real.zero_rpow h

/--
theorem `zero_rpow_def` / 定理 `zero_rpow_def`

English:
theorem zero_rpow_def
  given: (y : Real)
  statement: (0 : Real>=0) ^ y = if y = 0 then 1 else 0
  proof: by
  split_ifs with h <;> simp [h]

@[simp]

中文:
定理 zero_rpow_def
  条件: (y : 实数)
  结论: (0 : 实数>=0) ^ y = if y = 0 then 1 else 0
  证明: by
  split_ifs with h <;> simp [h]

@[simp]

Depends on / 依赖: Hom.ext, Modification, Modification.ext, split_ifs
-/
theorem zero_rpow_def (y : Real) : (0 : Real>=0) ^ y = if y = 0 then 1 else 0 := by
  split_ifs with h <;> simp [h]

@[simp]
/--
theorem `rpow_one` / 定理 `rpow_one`

English:
theorem rpow_one
  given: (x : Real>=0)
  statement: x ^ (1 : Real) = x
  proof: NNReal.eq Real.rpow_one _

中文:
定理 rpow_one
  条件: (x : 实数>=0)
  结论: x ^ (1 : 实数) = x
  证明: NNReal.eq Real.rpow_one _

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_one, rpow_one
-/
theorem rpow_one (x : Real>=0) : x ^ (1 : Real) = x :=
NNReal.eq Real.rpow_one _

/--
lemma `rpow_neg` / 引理 `rpow_neg`

English:
lemma rpow_neg
  given: (x : Real>=0) (y : Real)
  statement: x ^ (-y) = (x ^ y)⁻¹
  proof: NNReal.eq Real.rpow_neg x.2 _

@[simp, norm_cast]

中文:
引理 rpow_neg
  条件: (x : 实数>=0) (y : 实数)
  结论: x ^ (-y) = (x ^ y)⁻¹
  证明: NNReal.eq Real.rpow_neg x.2 _

@[simp, norm_cast]

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_neg, rpow_neg
-/
lemma rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻¹ :=
NNReal.eq Real.rpow_neg x.2 _

@[simp, norm_cast]
/--
lemma `rpow_natCast` / 引理 `rpow_natCast`

English:
lemma rpow_natCast
  given: (x : Real>=0) (n : Nat)
  statement: x ^ (n : Real) = x ^ n
  proof: NNReal.eq by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]

中文:
引理 rpow_natCast
  条件: (x : 实数>=0) (n : 自然数)
  结论: x ^ (n : 实数) = x ^ n
  证明: NNReal.eq by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_natCast, coe_pow, coe_rpow, rpow_natCast
-/
lemma rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Real) = x ^ n :=
NNReal.eq by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]
/--
lemma `rpow_intCast` / 引理 `rpow_intCast`

English:
lemma rpow_intCast
  given: (x : Real>=0) (n : Int)
  statement: x ^ (n : Real) = x ^ n
  proof: by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]

中文:
引理 rpow_intCast
  条件: (x : 实数>=0) (n : 整数)
  结论: x ^ (n : 实数) = x ^ n
  证明: by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, Int.ofNat_eq_natCast, cast_natCast, cast_negSucc, ofNat_eq_natCast, rpow_natCast, rpow_neg, zpow_natCast, zpow_negSucc
-/
lemma rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Real) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]
/--
theorem `one_rpow` / 定理 `one_rpow`

English:
theorem one_rpow
  given: (x : Real)
  statement: (1 : Real>=0) ^ x = 1
  proof: NNReal.eq Real.one_rpow _

中文:
定理 one_rpow
  条件: (x : 实数)
  结论: (1 : 实数>=0) ^ x = 1
  证明: NNReal.eq Real.one_rpow _

Depends on / 依赖: NNReal, NNReal.eq, Real.one_rpow, one_rpow
-/
theorem one_rpow (x : Real) : (1 : Real>=0) ^ x = 1 :=
NNReal.eq Real.one_rpow _

/--
theorem `rpow_add` / 定理 `rpow_add`

English:
theorem rpow_add
  given: {x : Real>=0} (hx : x != 0) (y z : Real)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: NNReal.eq Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _

中文:
定理 rpow_add
  条件: {x : 实数>=0} (hx : x != 0) (y z : 实数)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: NNReal.eq Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _

Depends on / 依赖: NNReal, NNReal.coe_pos.trans, NNReal.eq, Real.rpow_add, coe_pos, pos_iff_ne_zero, rpow_add
-/
theorem rpow_add {x : Real>=0} (hx : x != 0) (y z : Real) : x ^ (y + z) = x ^ y * x ^ z :=
NNReal.eq Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _

/--
theorem `rpow_add'` / 定理 `rpow_add'`

English:
theorem rpow_add'
  given: (h : y + z != 0) (x : Real>=0)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: NNReal.eq Real.rpow_add' x.2 h

中文:
定理 rpow_add'
  条件: (h : y + z != 0) (x : 实数>=0)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: NNReal.eq Real.rpow_add' x.2 h

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_add, rpow_add
-/
theorem rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z) = x ^ y * x ^ z :=
NNReal.eq Real.rpow_add' x.2 h

/--
lemma `rpow_add_intCast` / 引理 `rpow_add_intCast`

English:
lemma rpow_add_intCast
  given: (hx : x != 0) (y : Real) (n : Int)
  statement: x ^ (y + n) = x ^ y * x ^ n
  proof: by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _

中文:
引理 rpow_add_intCast
  条件: (hx : x != 0) (y : 实数) (n : 整数)
  结论: x ^ (y + n) = x ^ y * x ^ n
  证明: by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _

Depends on / 依赖: Real.rpow_add_intCast, mod_cast, rpow_add_intCast
-/
lemma rpow_add_intCast (hx : x != 0) (y : Real) (n : Int) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _

/--
lemma `rpow_add_natCast` / 引理 `rpow_add_natCast`

English:
lemma rpow_add_natCast
  given: (hx : x != 0) (y : Real) (n : Nat)
  statement: x ^ (y + n) = x ^ y * x ^ n
  proof: by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _

中文:
引理 rpow_add_natCast
  条件: (hx : x != 0) (y : 实数) (n : 自然数)
  结论: x ^ (y + n) = x ^ y * x ^ n
  证明: by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _

Depends on / 依赖: Hom.ext, Modification, Modification.ext, Real.rpow_add_natCast, mod_cast, rpow_add_natCast
-/
lemma rpow_add_natCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _

/--
lemma `rpow_sub_intCast` / 引理 `rpow_sub_intCast`

English:
lemma rpow_sub_intCast
  given: (hx : x != 0) (y : Real) (n : Nat)
  statement: x ^ (y - n) = x ^ y / x ^ n
  proof: by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _

中文:
引理 rpow_sub_intCast
  条件: (hx : x != 0) (y : 实数) (n : 自然数)
  结论: x ^ (y - n) = x ^ y / x ^ n
  证明: by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _

Depends on / 依赖: Real.rpow_sub_intCast, mod_cast, rpow_sub_intCast
-/
lemma rpow_sub_intCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _

/--
lemma `rpow_sub_natCast` / 引理 `rpow_sub_natCast`

English:
lemma rpow_sub_natCast
  given: (hx : x != 0) (y : Real) (n : Nat)
  statement: x ^ (y - n) = x ^ y / x ^ n
  proof: by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _

中文:
引理 rpow_sub_natCast
  条件: (hx : x != 0) (y : 实数) (n : 自然数)
  结论: x ^ (y - n) = x ^ y / x ^ n
  证明: by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _

Depends on / 依赖: Real.rpow_sub_natCast, mod_cast, rpow_sub_natCast
-/
lemma rpow_sub_natCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _

/--
lemma `rpow_add_intCast'` / 引理 `rpow_add_intCast'`

English:
lemma rpow_add_intCast'
  given: {n : Int} (h : y + n != 0) (x : Real>=0)
  statement: x ^ (y + n) = x ^ y * x ^ n
  proof: by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h

中文:
引理 rpow_add_intCast'
  条件: {n : 整数} (h : y + n != 0) (x : 实数>=0)
  结论: x ^ (y + n) = x ^ y * x ^ n
  证明: by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h

Depends on / 依赖: Real.rpow_add_intCast, mod_cast, rpow_add_intCast
-/
lemma rpow_add_intCast' {n : Int} (h : y + n != 0) (x : Real>=0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h

/--
lemma `rpow_add_natCast'` / 引理 `rpow_add_natCast'`

English:
lemma rpow_add_natCast'
  given: {n : Nat} (h : y + n != 0) (x : Real>=0)
  statement: x ^ (y + n) = x ^ y * x ^ n
  proof: by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h

中文:
引理 rpow_add_natCast'
  条件: {n : 自然数} (h : y + n != 0) (x : 实数>=0)
  结论: x ^ (y + n) = x ^ y * x ^ n
  证明: by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h

Depends on / 依赖: Real.rpow_add_natCast, mod_cast, rpow_add_natCast
-/
lemma rpow_add_natCast' {n : Nat} (h : y + n != 0) (x : Real>=0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h

/--
lemma `rpow_sub_intCast'` / 引理 `rpow_sub_intCast'`

English:
lemma rpow_sub_intCast'
  given: {n : Int} (h : y - n != 0) (x : Real>=0)
  statement: x ^ (y - n) = x ^ y / x ^ n
  proof: by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h

中文:
引理 rpow_sub_intCast'
  条件: {n : 整数} (h : y - n != 0) (x : 实数>=0)
  结论: x ^ (y - n) = x ^ y / x ^ n
  证明: by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h

Depends on / 依赖: Real.rpow_sub_intCast, mod_cast, rpow_sub_intCast
-/
lemma rpow_sub_intCast' {n : Int} (h : y - n != 0) (x : Real>=0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h

/--
lemma `rpow_sub_natCast'` / 引理 `rpow_sub_natCast'`

English:
lemma rpow_sub_natCast'
  given: {n : Nat} (h : y - n != 0) (x : Real>=0)
  statement: x ^ (y - n) = x ^ y / x ^ n
  proof: by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h

中文:
引理 rpow_sub_natCast'
  条件: {n : 自然数} (h : y - n != 0) (x : 实数>=0)
  结论: x ^ (y - n) = x ^ y / x ^ n
  证明: by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h

Depends on / 依赖: Real.rpow_sub_natCast, mod_cast, rpow_sub_natCast
-/
lemma rpow_sub_natCast' {n : Nat} (h : y - n != 0) (x : Real>=0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h

/--
lemma `rpow_add_one` / 引理 `rpow_add_one`

English:
lemma rpow_add_one
  given: (hx : x != 0) (y : Real)
  statement: x ^ (y + 1) = x ^ y * x
  proof: by
  simpa using rpow_add_natCast hx y 1

中文:
引理 rpow_add_one
  条件: (hx : x != 0) (y : 实数)
  结论: x ^ (y + 1) = x ^ y * x
  证明: by
  simpa using rpow_add_natCast hx y 1

Depends on / 依赖: rpow_add_natCast
-/
lemma rpow_add_one (hx : x != 0) (y : Real) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1

/--
lemma `rpow_sub_one` / 引理 `rpow_sub_one`

English:
lemma rpow_sub_one
  given: (hx : x != 0) (y : Real)
  statement: x ^ (y - 1) = x ^ y / x
  proof: by
  simpa using rpow_sub_natCast hx y 1

中文:
引理 rpow_sub_one
  条件: (hx : x != 0) (y : 实数)
  结论: x ^ (y - 1) = x ^ y / x
  证明: by
  simpa using rpow_sub_natCast hx y 1

Depends on / 依赖: rpow_sub_natCast
-/
lemma rpow_sub_one (hx : x != 0) (y : Real) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1

/--
lemma `rpow_add_one'` / 引理 `rpow_add_one'`

English:
lemma rpow_add_one'
  given: (h : y + 1 != 0) (x : Real>=0)
  statement: x ^ (y + 1) = x ^ y * x
  proof: by
  rw [rpow_add' h]; rw [rpow_one]

中文:
引理 rpow_add_one'
  条件: (h : y + 1 != 0) (x : 实数>=0)
  结论: x ^ (y + 1) = x ^ y * x
  证明: by
  rw [rpow_add' h]; rw [rpow_one]

Depends on / 依赖: rpow_add, rpow_one
-/
lemma rpow_add_one' (h : y + 1 != 0) (x : Real>=0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' h]; rw [rpow_one]

/--
lemma `rpow_one_add'` / 引理 `rpow_one_add'`

English:
lemma rpow_one_add'
  given: (h : 1 + y != 0) (x : Real>=0)
  statement: x ^ (1 + y) = x * x ^ y
  proof: by
  rw [rpow_add' h]; rw [rpow_one]

中文:
引理 rpow_one_add'
  条件: (h : 1 + y != 0) (x : 实数>=0)
  结论: x ^ (1 + y) = x * x ^ y
  证明: by
  rw [rpow_add' h]; rw [rpow_one]

Depends on / 依赖: rpow_add, rpow_one
-/
lemma rpow_one_add' (h : 1 + y != 0) (x : Real>=0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' h]; rw [rpow_one]

/--
theorem `rpow_add_of_nonneg` / 定理 `rpow_add_of_nonneg`

English:
theorem rpow_add_of_nonneg
  given: (x : Real>=0) {y z : Real} (hy : 0 <= y) (hz : 0 <= z)
  proof: by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

中文:
定理 rpow_add_of_nonneg
  条件: (x : 实数>=0) {y z : 实数} (hy : 0 <= y) (hz : 0 <= z)
  证明: by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

Depends on / 依赖: Real.rpow_add_of_nonneg, rpow_add_of_nonneg
-/
theorem rpow_add_of_nonneg (x : Real>=0) {y z : Real} (hy : 0 <= y) (hz : 0 <= z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

/--
lemma `rpow_of_add_eq` / 引理 `rpow_of_add_eq`

English:
lemma rpow_of_add_eq
  given: (x : Real>=0) (hw : w != 0) (h : y + z = w)
  statement: x ^ w = x ^ y * x ^ z
  proof: by
  rw [← h]; rw [rpow_add']; rwa [h]

中文:
引理 rpow_of_add_eq
  条件: (x : 实数>=0) (hw : w != 0) (h : y + z = w)
  结论: x ^ w = x ^ y * x ^ z
  证明: by
  rw [← h]; rw [rpow_add']; rwa [h]

Depends on / 依赖: rpow_add
-/
lemma rpow_of_add_eq (x : Real>=0) (hw : w != 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h]; rw [rpow_add']; rwa [h]

/--
theorem `rpow_mul` / 定理 `rpow_mul`

English:
theorem rpow_mul
  given: (x : Real>=0) (y z : Real)
  statement: x ^ (y * z) = (x ^ y) ^ z
  proof: NNReal.eq Real.rpow_mul x.2 y z

中文:
定理 rpow_mul
  条件: (x : 实数>=0) (y z : 实数)
  结论: x ^ (y * z) = (x ^ y) ^ z
  证明: NNReal.eq Real.rpow_mul x.2 y z

Depends on / 依赖: Hom.ext, Modification, Modification.ext, NNReal, NNReal.eq, Real.rpow_mul, rpow_mul
-/
theorem rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x ^ y) ^ z :=
NNReal.eq Real.rpow_mul x.2 y z

/--
lemma `rpow_natCast_mul` / 引理 `rpow_natCast_mul`

English:
lemma rpow_natCast_mul
  given: (x : Real>=0) (n : Nat) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul]; rw [rpow_natCast]

中文:
引理 rpow_natCast_mul
  条件: (x : 实数>=0) (n : 自然数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_natCast_mul (x : Real>=0) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul]; rw [rpow_natCast]

/--
lemma `rpow_mul_natCast` / 引理 `rpow_mul_natCast`

English:
lemma rpow_mul_natCast
  given: (x : Real>=0) (y : Real) (n : Nat)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul]; rw [rpow_natCast]

中文:
引理 rpow_mul_natCast
  条件: (x : 实数>=0) (y : 实数) (n : 自然数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_mul_natCast (x : Real>=0) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul]; rw [rpow_natCast]

/--
lemma `rpow_intCast_mul` / 引理 `rpow_intCast_mul`

English:
lemma rpow_intCast_mul
  given: (x : Real>=0) (n : Int) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul]; rw [rpow_intCast]

中文:
引理 rpow_intCast_mul
  条件: (x : 实数>=0) (n : 整数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_mul
-/
lemma rpow_intCast_mul (x : Real>=0) (n : Int) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul]; rw [rpow_intCast]

/--
lemma `rpow_mul_intCast` / 引理 `rpow_mul_intCast`

English:
lemma rpow_mul_intCast
  given: (x : Real>=0) (y : Real) (n : Int)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul]; rw [rpow_intCast]

中文:
引理 rpow_mul_intCast
  条件: (x : 实数>=0) (y : 实数) (n : 整数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_mul
-/
lemma rpow_mul_intCast (x : Real>=0) (y : Real) (n : Int) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul]; rw [rpow_intCast]

/--
theorem `rpow_neg_one` / 定理 `rpow_neg_one`

English:
theorem rpow_neg_one
  given: (x : Real>=0)
  statement: x ^ (-1 : Real) = x⁻¹
  proof: by simp [rpow_neg]

中文:
定理 rpow_neg_one
  条件: (x : 实数>=0)
  结论: x ^ (-1 : 实数) = x⁻¹
  证明: by simp [rpow_neg]

Depends on / 依赖: rpow_neg
-/
theorem rpow_neg_one (x : Real>=0) : x ^ (-1 : Real) = x⁻¹ := by simp [rpow_neg]

/--
theorem `rpow_sub` / 定理 `rpow_sub`

English:
theorem rpow_sub
  given: {x : Real>=0} (hx : x != 0) (y z : Real)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: NNReal.eq Real.rpow_sub ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) y z

中文:
定理 rpow_sub
  条件: {x : 实数>=0} (hx : x != 0) (y z : 实数)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: NNReal.eq Real.rpow_sub ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) y z

Depends on / 依赖: NNReal, NNReal.coe_pos.trans, NNReal.eq, Real.rpow_sub, coe_pos, pos_iff_ne_zero, rpow_sub
-/
theorem rpow_sub {x : Real>=0} (hx : x != 0) (y z : Real) : x ^ (y - z) = x ^ y / x ^ z :=
NNReal.eq Real.rpow_sub ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) y z

/--
theorem `rpow_sub'` / 定理 `rpow_sub'`

English:
theorem rpow_sub'
  given: (h : y - z != 0) (x : Real>=0)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: NNReal.eq Real.rpow_sub' x.2 h

中文:
定理 rpow_sub'
  条件: (h : y - z != 0) (x : 实数>=0)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: NNReal.eq Real.rpow_sub' x.2 h

Depends on / 依赖: NNReal, NNReal.eq, Real.rpow_sub, rpow_sub
-/
theorem rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z) = x ^ y / x ^ z :=
NNReal.eq Real.rpow_sub' x.2 h

/--
lemma `rpow_sub_one'` / 引理 `rpow_sub_one'`

English:
lemma rpow_sub_one'
  given: (h : y - 1 != 0) (x : Real>=0)
  statement: x ^ (y - 1) = x ^ y / x
  proof: by
  rw [rpow_sub' h]; rw [rpow_one]

中文:
引理 rpow_sub_one'
  条件: (h : y - 1 != 0) (x : 实数>=0)
  结论: x ^ (y - 1) = x ^ y / x
  证明: by
  rw [rpow_sub' h]; rw [rpow_one]

Depends on / 依赖: rpow_one, rpow_sub
-/
lemma rpow_sub_one' (h : y - 1 != 0) (x : Real>=0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' h]; rw [rpow_one]

/--
lemma `rpow_one_sub'` / 引理 `rpow_one_sub'`

English:
lemma rpow_one_sub'
  given: (h : 1 - y != 0) (x : Real>=0)
  statement: x ^ (1 - y) = x / x ^ y
  proof: by
  rw [rpow_sub' h]; rw [rpow_one]

中文:
引理 rpow_one_sub'
  条件: (h : 1 - y != 0) (x : 实数>=0)
  结论: x ^ (1 - y) = x / x ^ y
  证明: by
  rw [rpow_sub' h]; rw [rpow_one]

Depends on / 依赖: rpow_one, rpow_sub
-/
lemma rpow_one_sub' (h : 1 - y != 0) (x : Real>=0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' h]; rw [rpow_one]

/--
theorem `rpow_inv_rpow_self` / 定理 `rpow_inv_rpow_self`

English:
theorem rpow_inv_rpow_self
  given: {y : Real} (hy : y != 0) (x : Real>=0)
  statement: (x ^ y) ^ (1 / y) = x
  proof: by
  rw [← rpow_mul]
  field_simp
  simp

中文:
定理 rpow_inv_rpow_self
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0)
  结论: (x ^ y) ^ (1 / y) = x
  证明: by
  rw [← rpow_mul]
  field_simp
  simp

Depends on / 依赖: rpow_mul
-/
theorem rpow_inv_rpow_self {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ y) ^ (1 / y) = x := by
  rw [← rpow_mul]
  field_simp
  simp

/--
theorem `rpow_self_rpow_inv` / 定理 `rpow_self_rpow_inv`

English:
theorem rpow_self_rpow_inv
  given: {y : Real} (hy : y != 0) (x : Real>=0)
  statement: (x ^ (1 / y)) ^ y = x
  proof: by
  rw [← rpow_mul]
  field_simp
  simp

中文:
定理 rpow_self_rpow_inv
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0)
  结论: (x ^ (1 / y)) ^ y = x
  证明: by
  rw [← rpow_mul]
  field_simp
  simp

Depends on / 依赖: rpow_mul
-/
theorem rpow_self_rpow_inv {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ (1 / y)) ^ y = x := by
  rw [← rpow_mul]
  field_simp
  simp

/--
theorem `inv_rpow` / 定理 `inv_rpow`

English:
theorem inv_rpow
  given: (x : Real>=0) (y : Real)
  statement: x⁻¹ ^ y = (x ^ y)⁻¹
  proof: NNReal.eq Real.inv_rpow x.2 y

中文:
定理 inv_rpow
  条件: (x : 实数>=0) (y : 实数)
  结论: x⁻¹ ^ y = (x ^ y)⁻¹
  证明: NNReal.eq Real.inv_rpow x.2 y

Depends on / 依赖: NNReal, NNReal.eq, Real.inv_rpow, inv_rpow
-/
theorem inv_rpow (x : Real>=0) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
NNReal.eq Real.inv_rpow x.2 y

/--
theorem `div_rpow` / 定理 `div_rpow`

English:
theorem div_rpow
  given: (x y : Real>=0) (z : Real)
  statement: (x / y) ^ z = x ^ z / y ^ z
  proof: NNReal.eq Real.div_rpow x.2 y.2 z

中文:
定理 div_rpow
  条件: (x y : 实数>=0) (z : 实数)
  结论: (x / y) ^ z = x ^ z / y ^ z
  证明: NNReal.eq Real.div_rpow x.2 y.2 z

Depends on / 依赖: Hom.ext, Modification, Modification.ext, NNReal, NNReal.eq, Real.div_rpow, div_rpow
-/
theorem div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^ z / y ^ z :=
NNReal.eq Real.div_rpow x.2 y.2 z

/--
theorem `sqrt_eq_rpow` / 定理 `sqrt_eq_rpow`

English:
theorem sqrt_eq_rpow
  given: (x : Real>=0)
  statement: sqrt x = x ^ (1 / (2 : Real))
  proof: by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

@[simp]

中文:
定理 sqrt_eq_rpow
  条件: (x : 实数>=0)
  结论: sqrt x = x ^ (1 / (2 : 实数))
  证明: by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, Real.sqrt_eq_rpow, sqrt_eq_rpow
-/
theorem sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 : Real)) := by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

@[simp]
/--
lemma `rpow_ofNat` / 引理 `rpow_ofNat`

English:
lemma rpow_ofNat
  given: (x : Real>=0) (n : Nat) [n.AtLeastTwo]
  proof: rpow_natCast x n

中文:
引理 rpow_of自然数
  条件: (x : 实数>=0) (n : 自然数) [n.AtLeastTwo]
  证明: rpow_natCast x n

Depends on / 依赖: rpow_natCast
-/
lemma rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] :
    x ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n : Nat) :=
  rpow_natCast x n

/--
theorem `rpow_two` / 定理 `rpow_two`

English:
theorem rpow_two
  given: (x : Real>=0)
  statement: x ^ (2 : Real) = x ^ 2
  proof: rpow_ofNat x 2

中文:
定理 rpow_two
  条件: (x : 实数>=0)
  结论: x ^ (2 : 实数) = x ^ 2
  证明: rpow_ofNat x 2

Depends on / 依赖: rpow_ofNat
-/
theorem rpow_two (x : Real>=0) : x ^ (2 : Real) = x ^ 2 := rpow_ofNat x 2

/--
theorem `mul_rpow` / 定理 `mul_rpow`

English:
theorem mul_rpow
  given: {x y : Real>=0} {z : Real}
  statement: (x * y) ^ z = x ^ z * y ^ z
  proof: NNReal.eq Real.mul_rpow x.2 y.2

中文:
定理 mul_rpow
  条件: {x y : 实数>=0} {z : 实数}
  结论: (x * y) ^ z = x ^ z * y ^ z
  证明: NNReal.eq Real.mul_rpow x.2 y.2

Depends on / 依赖: NNReal, NNReal.eq, Real.mul_rpow, mul_rpow
-/
theorem mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^ z * y ^ z :=
NNReal.eq Real.mul_rpow x.2 y.2

/-- `rpow` as a `MonoidHom` -/
@[simps]
/--
Definition of `rpowMonoidHom` / `rpowMonoidHom` 的定义

English:
definition rpowMonoidHom
  signature: (r : Real)
  body: (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

中文:
定义 rpowMonoidHom
  签名: (r : 实数)
  定义体: (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow
-/
def rpowMonoidHom (r : Real) : Real>=0 ->* Real>=0 where
  toFun := (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

/--
theorem `list_prod_map_rpow` / 定理 `list_prod_map_rpow`

English:
theorem list_prod_map_rpow
  given: (l : List Real>=0) (r : Real)
  proof: l.prod_hom (rpowMonoidHom r)

中文:
定理 list_prod_map_rpow
  条件: (l : 列表 实数>=0) (r : 实数)
  证明: l.prod_hom (rpowMonoidHom r)

Depends on / 依赖: l.prod_hom, prod_hom, rpowMonoidHom
-/
theorem list_prod_map_rpow (l : List Real>=0) (r : Real) :
    (l.map (· ^ r)).prod = l.prod ^ r :=
  l.prod_hom (rpowMonoidHom r)

/--
theorem `list_prod_map_rpow'` / 定理 `list_prod_map_rpow'`

English:
theorem list_prod_map_rpow'
  given: {ι} (l : List ι) (f : ι -> Real>=0) (r : Real)
  proof: by
  rw [← list_prod_map_rpow]; rw [List.map_map]; rfl

中文:
定理 list_prod_map_rpow'
  条件: {ι} (l : 列表 ι) (f : ι -> 实数>=0) (r : 实数)
  证明: by
  rw [← list_prod_map_rpow]; rw [List.map_map]; rfl

Depends on / 依赖: List.map_map, list_prod_map_rpow, map_map
-/
theorem list_prod_map_rpow' {ι} (l : List ι) (f : ι -> Real>=0) (r : Real) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← list_prod_map_rpow]; rw [List.map_map]; rfl

/--
lemma `multiset_prod_map_rpow` / 引理 `multiset_prod_map_rpow`

English:
lemma multiset_prod_map_rpow
  given: {ι} (s : Multiset ι) (f : ι -> Real>=0) (r : Real)
  proof: s.prod_hom' (rpowMonoidHom r) _

中文:
引理 multiset_prod_map_rpow
  条件: {ι} (s : Multiset ι) (f : ι -> 实数>=0) (r : 实数)
  证明: s.prod_hom' (rpowMonoidHom r) _

Depends on / 依赖: prod_hom, rpowMonoidHom, s.prod_hom
-/
lemma multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι -> Real>=0) (r : Real) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r :=
  s.prod_hom' (rpowMonoidHom r) _

/--
lemma `finsetProd_rpow` / 引理 `finsetProd_rpow`

English:
lemma finsetProd_rpow
  given: {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real)
  proof: multiset_prod_map_rpow _ _ _

@[deprecated (since := "2026-04-08")] alias finset_prod_rpow := finsetProd_rpow

中文:
引理 finsetProd_rpow
  条件: {ι} (s : 有限集 ι) (f : ι -> 实数>=0) (r : 实数)
  证明: multiset_prod_map_rpow _ _ _

@[deprecated (since := "2026-04-08")] alias finset_prod_rpow := finsetProd_rpow

Depends on / 依赖: ComonObj, ComonObj.instTensorUnit, instTensorUnit, multiset_prod_map_rpow
-/
lemma finsetProd_rpow {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real) :
    (∏ i in s, f i ^ r) = (∏ i in s, f i) ^ r :=
  multiset_prod_map_rpow _ _ _

@[deprecated (since := "2026-04-08")] alias finset_prod_rpow := finsetProd_rpow

-- note: these don't really belong here, but they're much easier to prove in terms of the above

section Real

/--
theorem `_root_.Real.list_prod_map_rpow` / 定理 `_root_.Real.list_prod_map_rpow`

English:
theorem _root_.Real.list_prod_map_rpow
  given: (l : List Real) (hl : forall x in l, (0 : Real) <= x) (r : Real)
  proof: by
  lift l to List Real>=0 using hl
  have := congr_arg ((↑) : Real>=0 -> Real) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this

中文:
定理 _root_.实数.list_prod_map_rpow
  条件: (l : 列表 实数) (hl : 对任意 x in l, (0 : 实数) <= x) (r : 实数)
  证明: by
  lift l to List Real>=0 using hl
  have := congr_arg ((↑) : Real>=0 -> Real) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this

Depends on / 依赖: List.map_map, NNReal, NNReal.list_prod_map_rpow, congr_arg, list_prod_map_rpow, map_map, mod_cast
-/
theorem _root_.Real.list_prod_map_rpow (l : List Real) (hl : forall x in l, (0 : Real) <= x) (r : Real) :
    (l.map (· ^ r)).prod = l.prod ^ r := by
  lift l to List Real>=0 using hl
  have := congr_arg ((↑) : Real>=0 -> Real) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this

/--
theorem `_root_.Real.list_prod_map_rpow'` / 定理 `_root_.Real.list_prod_map_rpow'`

English:
theorem _root_.Real.list_prod_map_rpow'
  statement: {ι} (l : List ι) (f : ι -> Real)
  proof: by
  rw [← Real.list_prod_map_rpow (l.map f) _ r]; rw [List.map_map]
  · rfl
  simpa using hl

中文:
定理 _root_.实数.list_prod_map_rpow'
  结论: {ι} (l : 列表 ι) (f : ι -> 实数)
  证明: by
  rw [← Real.list_prod_map_rpow (l.map f) _ r]; rw [List.map_map]
  · rfl
  simpa using hl

Depends on / 依赖: List.map_map, Real.list_prod_map_rpow, l.map, list_prod_map_rpow, map_map
-/
theorem _root_.Real.list_prod_map_rpow' {ι} (l : List ι) (f : ι -> Real)
    (hl : forall i in l, (0 : Real) <= f i) (r : Real) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← Real.list_prod_map_rpow (l.map f) _ r]; rw [List.map_map]
  · rfl
  simpa using hl

/--
theorem `_root_.Real.multiset_prod_map_rpow` / 定理 `_root_.Real.multiset_prod_map_rpow`

English:
theorem _root_.Real.multiset_prod_map_rpow
  statement: {ι} (s : Multiset ι) (f : ι -> Real)
  proof: by
  obtain ⟨l⟩ := s
  simpa using Real.list_prod_map_rpow' l f hs r

中文:
定理 _root_.实数.multiset_prod_map_rpow
  结论: {ι} (s : Multiset ι) (f : ι -> 实数)
  证明: by
  obtain ⟨l⟩ := s
  simpa using Real.list_prod_map_rpow' l f hs r

Depends on / 依赖: Real.list_prod_map_rpow, list_prod_map_rpow
-/
theorem _root_.Real.multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι -> Real)
    (hs : forall i in s, (0 : Real) <= f i) (r : Real) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r := by
  obtain ⟨l⟩ := s
  simpa using Real.list_prod_map_rpow' l f hs r

/--
theorem `_root_.Real.finsetProd_rpow` / 定理 `_root_.Real.finsetProd_rpow`

English:
theorem _root_.Real.finsetProd_rpow
  proof: Real.multiset_prod_map_rpow s.val f hs r

@[deprecated (since := "2026-04-08")] alias _root_.Real.finset_prod_rpow := Real.finsetProd_rpow

中文:
定理 _root_.实数.finsetProd_rpow
  证明: Real.multiset_prod_map_rpow s.val f hs r

@[deprecated (since := "2026-04-08")] alias _root_.Real.finset_prod_rpow := Real.finsetProd_rpow

Depends on / 依赖: Real.multiset_prod_map_rpow, multiset_prod_map_rpow, s.val
-/
theorem _root_.Real.finsetProd_rpow
    {ι} (s : Finset ι) (f : ι -> Real) (hs : forall i in s, 0 <= f i) (r : Real) :
    (∏ i in s, f i ^ r) = (∏ i in s, f i) ^ r :=
  Real.multiset_prod_map_rpow s.val f hs r

@[deprecated (since := "2026-04-08")] alias _root_.Real.finset_prod_rpow := Real.finsetProd_rpow

end Real

/--
theorem `rpow_le_rpow` / 定理 `rpow_le_rpow`

English:
theorem rpow_le_rpow
  given: {x y : Real>=0} {z : Real} (h₁ : x <= y) (h₂ : 0 <= z)
  statement: x ^ z <= y ^ z
  proof: Real.rpow_le_rpow x.2 h₁ h₂

中文:
定理 rpow_le_rpow
  条件: {x y : 实数>=0} {z : 实数} (h₁ : x <= y) (h₂ : 0 <= z)
  结论: x ^ z <= y ^ z
  证明: Real.rpow_le_rpow x.2 h₁ h₂
-/
@[gcongr] theorem rpow_le_rpow {x y : Real>=0} {z : Real} (h₁ : x <= y) (h₂ : 0 <= z) : x ^ z <= y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂

/--
theorem `rpow_lt_rpow` / 定理 `rpow_lt_rpow`

English:
theorem rpow_lt_rpow
  given: {x y : Real>=0} {z : Real} (h₁ : x < y) (h₂ : 0 < z)
  statement: x ^ z < y ^ z
  proof: Real.rpow_lt_rpow x.2 h₁ h₂

中文:
定理 rpow_lt_rpow
  条件: {x y : 实数>=0} {z : 实数} (h₁ : x < y) (h₂ : 0 < z)
  结论: x ^ z < y ^ z
  证明: Real.rpow_lt_rpow x.2 h₁ h₂
-/
@[gcongr] theorem rpow_lt_rpow {x y : Real>=0} {z : Real} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂

/--
theorem `rpow_lt_rpow_iff` / 定理 `rpow_lt_rpow_iff`

English:
theorem rpow_lt_rpow_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x ^ z < y ^ z ↔ x < y
  proof: Real.rpow_lt_rpow_iff x.2 y.2 hz

中文:
定理 rpow_lt_rpow_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x ^ z < y ^ z ↔ x < y
  证明: Real.rpow_lt_rpow_iff x.2 y.2 hz

Depends on / 依赖: Comonad, Comonad.ofOplaxFromUnit, Real.rpow_lt_rpow_iff, m.toOplax, ofOplaxFromUnit, rpow_lt_rpow_iff, toOplax
-/
theorem rpow_lt_rpow_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz

/--
theorem `rpow_le_rpow_iff` / 定理 `rpow_le_rpow_iff`

English:
theorem rpow_le_rpow_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x ^ z <= y ^ z ↔ x <= y
  proof: Real.rpow_le_rpow_iff x.2 y.2 hz

中文:
定理 rpow_le_rpow_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x ^ z <= y ^ z ↔ x <= y
  证明: Real.rpow_le_rpow_iff x.2 y.2 hz

Depends on / 依赖: Real.rpow_le_rpow_iff, rpow_le_rpow_iff
-/
theorem rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz

/--
theorem `le_rpow_inv_iff` / 定理 `le_rpow_inv_iff`

English:
theorem le_rpow_inv_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x <= y ^ z⁻¹ ↔ x ^ z <= y
  proof: by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

中文:
定理 le_rpow_inv_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x <= y ^ z⁻¹ ↔ x ^ z <= y
  证明: by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

Depends on / 依赖: hz.ne, one_div, rpow_le_rpow_iff, rpow_self_rpow_inv
-/
theorem le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y := by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

/--
theorem `rpow_inv_le_iff` / 定理 `rpow_inv_le_iff`

English:
theorem rpow_inv_le_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x ^ z⁻¹ <= y ↔ x <= y ^ z
  proof: by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

中文:
定理 rpow_inv_le_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x ^ z⁻¹ <= y ↔ x <= y ^ z
  证明: by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

Depends on / 依赖: hz.ne, one_div, rpow_le_rpow_iff, rpow_self_rpow_inv
-/
theorem rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z := by
  rw [← rpow_le_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz.ne']

/--
theorem `lt_rpow_inv_iff` / 定理 `lt_rpow_inv_iff`

English:
theorem lt_rpow_inv_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x < y ^ z⁻¹ ↔ x ^ z < y
  proof: by
  simp only [← not_le, rpow_inv_le_iff hz]

中文:
定理 lt_rpow_inv_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x < y ^ z⁻¹ ↔ x ^ z < y
  证明: by
  simp only [← not_le, rpow_inv_le_iff hz]

Depends on / 依赖: not_le, rpow_inv_le_iff
-/
theorem lt_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  simp only [← not_le, rpow_inv_le_iff hz]

/--
theorem `rpow_inv_lt_iff` / 定理 `rpow_inv_lt_iff`

English:
theorem rpow_inv_lt_iff
  given: {x y : Real>=0} {z : Real} (hz : 0 < z)
  statement: x ^ z⁻¹ < y ↔ x < y ^ z
  proof: by
  simp only [← not_le, le_rpow_inv_iff hz]

中文:
定理 rpow_inv_lt_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : 0 < z)
  结论: x ^ z⁻¹ < y ↔ x < y ^ z
  证明: by
  simp only [← not_le, le_rpow_inv_iff hz]

Depends on / 依赖: le_rpow_inv_iff, not_le
-/
theorem rpow_inv_lt_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

section
variable {y : Real>=0}

/--
lemma `rpow_lt_rpow_of_neg` / 引理 `rpow_lt_rpow_of_neg`

English:
lemma rpow_lt_rpow_of_neg
  given: (hx : 0 < x) (hxy : x < y) (hz : z < 0)
  statement: y ^ z < x ^ z
  proof: Real.rpow_lt_rpow_of_neg hx hxy hz

中文:
引理 rpow_lt_rpow_of_neg
  条件: (hx : 0 < x) (hxy : x < y) (hz : z < 0)
  结论: y ^ z < x ^ z
  证明: Real.rpow_lt_rpow_of_neg hx hxy hz

Depends on / 依赖: Real.rpow_lt_rpow_of_neg, rpow_lt_rpow_of_neg
-/
lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z :=
  Real.rpow_lt_rpow_of_neg hx hxy hz

/--
lemma `rpow_le_rpow_of_nonpos` / 引理 `rpow_le_rpow_of_nonpos`

English:
lemma rpow_le_rpow_of_nonpos
  given: (hx : 0 < x) (hxy : x <= y) (hz : z <= 0)
  statement: y ^ z <= x ^ z
  proof: Real.rpow_le_rpow_of_nonpos hx hxy hz

中文:
引理 rpow_le_rpow_of_nonpos
  条件: (hx : 0 < x) (hxy : x <= y) (hz : z <= 0)
  结论: y ^ z <= x ^ z
  证明: Real.rpow_le_rpow_of_nonpos hx hxy hz

Depends on / 依赖: Real.rpow_le_rpow_of_nonpos, rpow_le_rpow_of_nonpos
-/
lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x <= y) (hz : z <= 0) : y ^ z <= x ^ z :=
  Real.rpow_le_rpow_of_nonpos hx hxy hz

/--
lemma `rpow_lt_rpow_iff_of_neg` / 引理 `rpow_lt_rpow_iff_of_neg`

English:
lemma rpow_lt_rpow_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z < y ^ z ↔ y < x
  proof: Real.rpow_lt_rpow_iff_of_neg hx hy hz

中文:
引理 rpow_lt_rpow_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z < y ^ z ↔ y < x
  证明: Real.rpow_lt_rpow_iff_of_neg hx hy hz

Depends on / 依赖: Real.rpow_lt_rpow_iff_of_neg, rpow_lt_rpow_iff_of_neg
-/
lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  Real.rpow_lt_rpow_iff_of_neg hx hy hz

/--
lemma `rpow_le_rpow_iff_of_neg` / 引理 `rpow_le_rpow_iff_of_neg`

English:
lemma rpow_le_rpow_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z <= y ^ z ↔ y <= x
  proof: Real.rpow_le_rpow_iff_of_neg hx hy hz

中文:
引理 rpow_le_rpow_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z <= y ^ z ↔ y <= x
  证明: Real.rpow_le_rpow_iff_of_neg hx hy hz

Depends on / 依赖: Real.rpow_le_rpow_iff_of_neg, rpow_le_rpow_iff_of_neg
-/
lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z <= y ^ z ↔ y <= x :=
  Real.rpow_le_rpow_iff_of_neg hx hy hz

/--
lemma `le_rpow_inv_iff_of_pos` / 引理 `le_rpow_inv_iff_of_pos`

English:
lemma le_rpow_inv_iff_of_pos
  given: (hy : 0 <= y) (hz : 0 < z) (x : Real>=0)
  statement: x <= y ^ z⁻¹ ↔ x ^ z <= y
  proof: Real.le_rpow_inv_iff_of_pos x.2 hy hz

中文:
引理 le_rpow_inv_iff_of_pos
  条件: (hy : 0 <= y) (hz : 0 < z) (x : 实数>=0)
  结论: x <= y ^ z⁻¹ ↔ x ^ z <= y
  证明: Real.le_rpow_inv_iff_of_pos x.2 hy hz

Depends on / 依赖: Real.le_rpow_inv_iff_of_pos, le_rpow_inv_iff_of_pos
-/
lemma le_rpow_inv_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x <= y ^ z⁻¹ ↔ x ^ z <= y :=
  Real.le_rpow_inv_iff_of_pos x.2 hy hz

/--
lemma `rpow_inv_le_iff_of_pos` / 引理 `rpow_inv_le_iff_of_pos`

English:
lemma rpow_inv_le_iff_of_pos
  given: (hy : 0 <= y) (hz : 0 < z) (x : Real>=0)
  statement: x ^ z⁻¹ <= y ↔ x <= y ^ z
  proof: Real.rpow_inv_le_iff_of_pos x.2 hy hz

中文:
引理 rpow_inv_le_iff_of_pos
  条件: (hy : 0 <= y) (hz : 0 < z) (x : 实数>=0)
  结论: x ^ z⁻¹ <= y ↔ x <= y ^ z
  证明: Real.rpow_inv_le_iff_of_pos x.2 hy hz

Depends on / 依赖: Real.rpow_inv_le_iff_of_pos, rpow_inv_le_iff_of_pos
-/
lemma rpow_inv_le_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x ^ z⁻¹ <= y ↔ x <= y ^ z :=
  Real.rpow_inv_le_iff_of_pos x.2 hy hz

/--
lemma `lt_rpow_inv_iff_of_pos` / 引理 `lt_rpow_inv_iff_of_pos`

English:
lemma lt_rpow_inv_iff_of_pos
  given: (hy : 0 <= y) (hz : 0 < z) (x : Real>=0)
  statement: x < y ^ z⁻¹ ↔ x ^ z < y
  proof: Real.lt_rpow_inv_iff_of_pos x.2 hy hz

中文:
引理 lt_rpow_inv_iff_of_pos
  条件: (hy : 0 <= y) (hz : 0 < z) (x : 实数>=0)
  结论: x < y ^ z⁻¹ ↔ x ^ z < y
  证明: Real.lt_rpow_inv_iff_of_pos x.2 hy hz

Depends on / 依赖: Real.lt_rpow_inv_iff_of_pos, lt_rpow_inv_iff_of_pos
-/
lemma lt_rpow_inv_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  Real.lt_rpow_inv_iff_of_pos x.2 hy hz

/--
lemma `rpow_inv_lt_iff_of_pos` / 引理 `rpow_inv_lt_iff_of_pos`

English:
lemma rpow_inv_lt_iff_of_pos
  given: (hy : 0 <= y) (hz : 0 < z) (x : Real>=0)
  statement: x ^ z⁻¹ < y ↔ x < y ^ z
  proof: Real.rpow_inv_lt_iff_of_pos x.2 hy hz

中文:
引理 rpow_inv_lt_iff_of_pos
  条件: (hy : 0 <= y) (hz : 0 < z) (x : 实数>=0)
  结论: x ^ z⁻¹ < y ↔ x < y ^ z
  证明: Real.rpow_inv_lt_iff_of_pos x.2 hy hz

Depends on / 依赖: Real.rpow_inv_lt_iff_of_pos, rpow_inv_lt_iff_of_pos
-/
lemma rpow_inv_lt_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  Real.rpow_inv_lt_iff_of_pos x.2 hy hz

/--
lemma `le_rpow_inv_iff_of_neg` / 引理 `le_rpow_inv_iff_of_neg`

English:
lemma le_rpow_inv_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x <= y ^ z⁻¹ ↔ y <= x ^ z
  proof: Real.le_rpow_inv_iff_of_neg hx hy hz

中文:
引理 le_rpow_inv_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x <= y ^ z⁻¹ ↔ y <= x ^ z
  证明: Real.le_rpow_inv_iff_of_neg hx hy hz

Depends on / 依赖: Real.le_rpow_inv_iff_of_neg, le_rpow_inv_iff_of_neg
-/
lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x <= y ^ z⁻¹ ↔ y <= x ^ z :=
  Real.le_rpow_inv_iff_of_neg hx hy hz

/--
lemma `lt_rpow_inv_iff_of_neg` / 引理 `lt_rpow_inv_iff_of_neg`

English:
lemma lt_rpow_inv_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x < y ^ z⁻¹ ↔ y < x ^ z
  proof: Real.lt_rpow_inv_iff_of_neg hx hy hz

中文:
引理 lt_rpow_inv_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x < y ^ z⁻¹ ↔ y < x ^ z
  证明: Real.lt_rpow_inv_iff_of_neg hx hy hz

Depends on / 依赖: Real.lt_rpow_inv_iff_of_neg, lt_rpow_inv_iff_of_neg
-/
lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  Real.lt_rpow_inv_iff_of_neg hx hy hz

/--
lemma `rpow_inv_lt_iff_of_neg` / 引理 `rpow_inv_lt_iff_of_neg`

English:
lemma rpow_inv_lt_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z⁻¹ < y ↔ y ^ z < x
  proof: Real.rpow_inv_lt_iff_of_neg hx hy hz

中文:
引理 rpow_inv_lt_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z⁻¹ < y ↔ y ^ z < x
  证明: Real.rpow_inv_lt_iff_of_neg hx hy hz

Depends on / 依赖: Real.rpow_inv_lt_iff_of_neg, rpow_inv_lt_iff_of_neg
-/
lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  Real.rpow_inv_lt_iff_of_neg hx hy hz

/--
lemma `rpow_inv_le_iff_of_neg` / 引理 `rpow_inv_le_iff_of_neg`

English:
lemma rpow_inv_le_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z⁻¹ <= y ↔ y ^ z <= x
  proof: Real.rpow_inv_le_iff_of_neg hx hy hz

中文:
引理 rpow_inv_le_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z⁻¹ <= y ↔ y ^ z <= x
  证明: Real.rpow_inv_le_iff_of_neg hx hy hz

Depends on / 依赖: Real.rpow_inv_le_iff_of_neg, rpow_inv_le_iff_of_neg
-/
lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ <= y ↔ y ^ z <= x :=
  Real.rpow_inv_le_iff_of_neg hx hy hz

end

/--
theorem `rpow_lt_rpow_of_exponent_lt` / 定理 `rpow_lt_rpow_of_exponent_lt`

English:
theorem rpow_lt_rpow_of_exponent_lt
  given: {x : Real>=0} {y z : Real} (hx : 1 < x) (hyz : y < z)
  proof: Real.rpow_lt_rpow_of_exponent_lt hx hyz

中文:
定理 rpow_lt_rpow_of_exponent_lt
  条件: {x : 实数>=0} {y z : 实数} (hx : 1 < x) (hyz : y < z)
  证明: Real.rpow_lt_rpow_of_exponent_lt hx hyz
-/
@[gcongr] theorem rpow_lt_rpow_of_exponent_lt {x : Real>=0} {y z : Real} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz

/--
theorem `rpow_le_rpow_of_exponent_le` / 定理 `rpow_le_rpow_of_exponent_le`

English:
theorem rpow_le_rpow_of_exponent_le
  given: {x : Real>=0} {y z : Real} (hx : 1 <= x) (hyz : y <= z)
  proof: Real.rpow_le_rpow_of_exponent_le hx hyz

中文:
定理 rpow_le_rpow_of_exponent_le
  条件: {x : 实数>=0} {y z : 实数} (hx : 1 <= x) (hyz : y <= z)
  证明: Real.rpow_le_rpow_of_exponent_le hx hyz
-/
@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : Real>=0} {y z : Real} (hx : 1 <= x) (hyz : y <= z) :
    x ^ y <= x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz

/--
theorem `rpow_lt_rpow_of_exponent_gt` / 定理 `rpow_lt_rpow_of_exponent_gt`

English:
theorem rpow_lt_rpow_of_exponent_gt
  given: {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  proof: Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

中文:
定理 rpow_lt_rpow_of_exponent_gt
  条件: {x : 实数>=0} {y z : 实数} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  证明: Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

Depends on / 依赖: Real.rpow_lt_rpow_of_exponent_gt, rpow_lt_rpow_of_exponent_gt
-/
theorem rpow_lt_rpow_of_exponent_gt {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

/--
theorem `rpow_le_rpow_of_exponent_ge` / 定理 `rpow_le_rpow_of_exponent_ge`

English:
theorem rpow_le_rpow_of_exponent_ge
  given: {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y)
  proof: Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

中文:
定理 rpow_le_rpow_of_exponent_ge
  条件: {x : 实数>=0} {y z : 实数} (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y)
  证明: Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

Depends on / 依赖: Real.rpow_le_rpow_of_exponent_ge, rpow_le_rpow_of_exponent_ge
-/
theorem rpow_le_rpow_of_exponent_ge {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y) :
    x ^ y <= x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

/--
theorem `rpow_pos` / 定理 `rpow_pos`

English:
theorem rpow_pos
  given: {p : Real} {x : Real>=0} (hx_pos : 0 < x)
  statement: 0 < x ^ p
  proof: by
  have rpow_pos_of_nonneg : forall {p : Real}, 0 < p -> 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : Real) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zer

中文:
定理 rpow_pos
  条件: {p : 实数} {x : 实数>=0} (hx_pos : 0 < x)
  结论: 0 < x ^ p
  证明: by
  have rpow_pos_of_nonneg : forall {p : Real}, 0 < p -> 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : Real) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zer

Depends on / 依赖: hp_neg, hp_pos, hp_pos.ne, hx_pos, inv_pos, lt_trichotomy, neg_neg, neg_pos, neg_pos.mpr, rpow_lt_rpow, rpow_neg, rpow_pos_of_nonneg, rpow_zero, zero_lt_one, zero_rpow
-/
theorem rpow_pos {p : Real} {x : Real>=0} (hx_pos : 0 < x) : 0 < x ^ p := by
  have rpow_pos_of_nonneg : forall {p : Real}, 0 < p -> 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : Real) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)

/--
theorem `rpow_lt_one` / 定理 `rpow_lt_one`

English:
theorem rpow_lt_one
  given: {x : Real>=0} {z : Real} (hx1 : x < 1) (hz : 0 < z)
  statement: x ^ z < 1
  proof: Real.rpow_lt_one (coe_nonneg x) hx1 hz

中文:
定理 rpow_lt_one
  条件: {x : 实数>=0} {z : 实数} (hx1 : x < 1) (hz : 0 < z)
  结论: x ^ z < 1
  证明: Real.rpow_lt_one (coe_nonneg x) hx1 hz

Depends on / 依赖: Real.rpow_lt_one, coe_nonneg, rpow_lt_one
-/
theorem rpow_lt_one {x : Real>=0} {z : Real} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz

/--
theorem `rpow_le_one` / 定理 `rpow_le_one`

English:
theorem rpow_le_one
  given: {x : Real>=0} {z : Real} (hx2 : x <= 1) (hz : 0 <= z)
  statement: x ^ z <= 1
  proof: Real.rpow_le_one x.2 hx2 hz

中文:
定理 rpow_le_one
  条件: {x : 实数>=0} {z : 实数} (hx2 : x <= 1) (hz : 0 <= z)
  结论: x ^ z <= 1
  证明: Real.rpow_le_one x.2 hx2 hz

Depends on / 依赖: Real.rpow_le_one, rpow_le_one
-/
theorem rpow_le_one {x : Real>=0} {z : Real} (hx2 : x <= 1) (hz : 0 <= z) : x ^ z <= 1 :=
  Real.rpow_le_one x.2 hx2 hz

/--
theorem `rpow_lt_one_of_one_lt_of_neg` / 定理 `rpow_lt_one_of_one_lt_of_neg`

English:
theorem rpow_lt_one_of_one_lt_of_neg
  given: {x : Real>=0} {z : Real} (hx : 1 < x) (hz : z < 0)
  statement: x ^ z < 1
  proof: Real.rpow_lt_one_of_one_lt_of_neg hx hz

中文:
定理 rpow_lt_one_of_one_lt_of_neg
  条件: {x : 实数>=0} {z : 实数} (hx : 1 < x) (hz : z < 0)
  结论: x ^ z < 1
  证明: Real.rpow_lt_one_of_one_lt_of_neg hx hz

Depends on / 依赖: Real.rpow_lt_one_of_one_lt_of_neg, rpow_lt_one_of_one_lt_of_neg
-/
theorem rpow_lt_one_of_one_lt_of_neg {x : Real>=0} {z : Real} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz

/--
theorem `rpow_le_one_of_one_le_of_nonpos` / 定理 `rpow_le_one_of_one_le_of_nonpos`

English:
theorem rpow_le_one_of_one_le_of_nonpos
  given: {x : Real>=0} {z : Real} (hx : 1 <= x) (hz : z <= 0)
  statement: x ^ z <= 1
  proof: Real.rpow_le_one_of_one_le_of_nonpos hx hz

中文:
定理 rpow_le_one_of_one_le_of_nonpos
  条件: {x : 实数>=0} {z : 实数} (hx : 1 <= x) (hz : z <= 0)
  结论: x ^ z <= 1
  证明: Real.rpow_le_one_of_one_le_of_nonpos hx hz

Depends on / 依赖: Real.rpow_le_one_of_one_le_of_nonpos, rpow_le_one_of_one_le_of_nonpos
-/
theorem rpow_le_one_of_one_le_of_nonpos {x : Real>=0} {z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz

/--
theorem `one_lt_rpow` / 定理 `one_lt_rpow`

English:
theorem one_lt_rpow
  given: {x : Real>=0} {z : Real} (hx : 1 < x) (hz : 0 < z)
  statement: 1 < x ^ z
  proof: Real.one_lt_rpow hx hz

中文:
定理 one_lt_rpow
  条件: {x : 实数>=0} {z : 实数} (hx : 1 < x) (hz : 0 < z)
  结论: 1 < x ^ z
  证明: Real.one_lt_rpow hx hz

Depends on / 依赖: Real.one_lt_rpow, one_lt_rpow
-/
theorem one_lt_rpow {x : Real>=0} {z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz

/--
theorem `one_le_rpow` / 定理 `one_le_rpow`

English:
theorem one_le_rpow
  given: {x : Real>=0} {z : Real} (h : 1 <= x) (h₁ : 0 <= z)
  statement: 1 <= x ^ z
  proof: Real.one_le_rpow h h₁

中文:
定理 one_le_rpow
  条件: {x : 实数>=0} {z : 实数} (h : 1 <= x) (h₁ : 0 <= z)
  结论: 1 <= x ^ z
  证明: Real.one_le_rpow h h₁

Depends on / 依赖: Real.one_le_rpow, one_le_rpow
-/
theorem one_le_rpow {x : Real>=0} {z : Real} (h : 1 <= x) (h₁ : 0 <= z) : 1 <= x ^ z :=
  Real.one_le_rpow h h₁

/--
theorem `one_lt_rpow_of_pos_of_lt_one_of_neg` / 定理 `one_lt_rpow_of_pos_of_lt_one_of_neg`

English:
theorem one_lt_rpow_of_pos_of_lt_one_of_neg
  statement: {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x < 1)
  proof: Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

中文:
定理 one_lt_rpow_of_pos_of_lt_one_of_neg
  结论: {x : 实数>=0} {z : 实数} (hx1 : 0 < x) (hx2 : x < 1)
  证明: Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

Depends on / 依赖: Real.one_lt_rpow_of_pos_of_lt_one_of_neg, one_lt_rpow_of_pos_of_lt_one_of_neg
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

/--
theorem `one_le_rpow_of_pos_of_le_one_of_nonpos` / 定理 `one_le_rpow_of_pos_of_le_one_of_nonpos`

English:
theorem one_le_rpow_of_pos_of_le_one_of_nonpos
  statement: {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x <= 1)
  proof: Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

中文:
定理 one_le_rpow_of_pos_of_le_one_of_nonpos
  结论: {x : 实数>=0} {z : 实数} (hx1 : 0 < x) (hx2 : x <= 1)
  证明: Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

Depends on / 依赖: Real.one_le_rpow_of_pos_of_le_one_of_nonpos, one_le_rpow_of_pos_of_le_one_of_nonpos
-/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x <= 1)
    (hz : z <= 0) : 1 <= x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

/--
theorem `rpow_le_self_of_le_one` / 定理 `rpow_le_self_of_le_one`

English:
theorem rpow_le_self_of_le_one
  given: {x : Real>=0} {z : Real} (hx : x <= 1) (h_one_le : 1 <= z)
  statement: x ^ z <= x
  proof: by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z != 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le

中文:
定理 rpow_le_self_of_le_one
  条件: {x : 实数>=0} {z : 实数} (hx : x <= 1) (h_one_le : 1 <= z)
  结论: x ^ z <= x
  证明: by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z != 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le

Depends on / 依赖: NNReal, NNReal.rpow_le_rpow_of_exponent_ge, NNReal.rpow_one, eq_bot_or_bot_lt, h_one_le, nth_rw, rpow_le_rpow_of_exponent_ge, rpow_one
-/
theorem rpow_le_self_of_le_one {x : Real>=0} {z : Real} (hx : x <= 1) (h_one_le : 1 <= z) : x ^ z <= x := by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z != 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le

/--
theorem `rpow_left_injective` / 定理 `rpow_left_injective`

English:
theorem rpow_left_injective
  given: {x : Real} (hx : x != 0)
  statement: Function.Injective fun y : Real>=0 => y ^ x
  proof: fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz

中文:
定理 rpow_left_injective
  条件: {x : 实数} (hx : x != 0)
  结论: 函数.单射 fun y : 实数>=0 => y ^ x
  证明: fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz

Depends on / 依赖: congr_arg, rpow_inv_rpow_self
-/
theorem rpow_left_injective {x : Real} (hx : x != 0) : Function.Injective fun y : Real>=0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz

/--
theorem `rpow_eq_rpow_iff` / 定理 `rpow_eq_rpow_iff`

English:
theorem rpow_eq_rpow_iff
  given: {x y : Real>=0} {z : Real} (hz : z != 0)
  statement: x ^ z = y ^ z ↔ x = y
  proof: (rpow_left_injective hz).eq_iff

中文:
定理 rpow_eq_rpow_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : z != 0)
  结论: x ^ z = y ^ z ↔ x = y
  证明: (rpow_left_injective hz).eq_iff

Depends on / 依赖: eq_iff, rpow_left_injective
-/
theorem rpow_eq_rpow_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff

/--
theorem `rpow_left_surjective` / 定理 `rpow_left_surjective`

English:
theorem rpow_left_surjective
  given: {x : Real} (hx : x != 0)
  statement: Function.Surjective fun y : Real>=0 => y ^ x
  proof: fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, inv_mul_cancel₀ hx, rpow_one]⟩

中文:
定理 rpow_left_surjective
  条件: {x : 实数} (hx : x != 0)
  结论: 函数.满射 fun y : 实数>=0 => y ^ x
  证明: fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, inv_mul_cancel₀ hx, rpow_one]⟩

Depends on / 依赖: rpow_mul, rpow_one, simp_rw
-/
theorem rpow_left_surjective {x : Real} (hx : x != 0) : Function.Surjective fun y : Real>=0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, inv_mul_cancel₀ hx, rpow_one]⟩

/--
theorem `rpow_left_bijective` / 定理 `rpow_left_bijective`

English:
theorem rpow_left_bijective
  given: {x : Real} (hx : x != 0)
  statement: Function.Bijective fun y : Real>=0 => y ^ x
  proof: ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

中文:
定理 rpow_left_bijective
  条件: {x : 实数} (hx : x != 0)
  结论: 函数.双射 fun y : 实数>=0 => y ^ x
  证明: ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

Depends on / 依赖: rpow_left_injective, rpow_left_surjective
-/
theorem rpow_left_bijective {x : Real} (hx : x != 0) : Function.Bijective fun y : Real>=0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

/--
lemma `rpow_right_inj` / 引理 `rpow_right_inj`

English:
lemma rpow_right_inj
  given: {y z : Real} (hx₀ : x != 0) (hx₁ : x != 1)
  statement: x ^ y = x ^ z ↔ y = z
  proof: by
  rw [← pos_iff_ne_zero] at hx₀
  rify at *
  grind [Real.rpow_right_inj]

中文:
引理 rpow_right_inj
  条件: {y z : 实数} (hx₀ : x != 0) (hx₁ : x != 1)
  结论: x ^ y = x ^ z ↔ y = z
  证明: by
  rw [← pos_iff_ne_zero] at hx₀
  rify at *
  grind [Real.rpow_right_inj]

Depends on / 依赖: Real.rpow_right_inj, pos_iff_ne_zero, rpow_right_inj
-/
lemma rpow_right_inj {y z : Real} (hx₀ : x != 0) (hx₁ : x != 1) : x ^ y = x ^ z ↔ y = z := by
  rw [← pos_iff_ne_zero] at hx₀
  rify at *
  grind [Real.rpow_right_inj]

/--
lemma `rpow_eq_rpow_right_iff` / 引理 `rpow_eq_rpow_right_iff`

English:
lemma rpow_eq_rpow_right_iff
  given: {y z : Real}
  proof: by
  obtain rfl | hx₀ := eq_or_ne x 0
  · obtain rfl | hz := eq_or_ne z 0
    · simp [zero_rpow_def]
    · simp +contextual [hz]
  obtain rfl | hx₁ := eq_or_ne x 1
  · simp
  simpa [hx₀, hx₁] using rpow_right_inj (y := y) (z := z) hx₀ hx₁

@[simp]

中文:
引理 rpow_eq_rpow_right_iff
  条件: {y z : 实数}
  证明: by
  obtain rfl | hx₀ := eq_or_ne x 0
  · obtain rfl | hz := eq_or_ne z 0
    · simp [zero_rpow_def]
    · simp +contextual [hz]
  obtain rfl | hx₁ := eq_or_ne x 1
  · simp
  simpa [hx₀, hx₁] using rpow_right_inj (y := y) (z := z) hx₀ hx₁

@[simp]

Depends on / 依赖: contextual, eq_or_ne, rpow_right_inj, zero_rpow_def
-/
lemma rpow_eq_rpow_right_iff {y z : Real} :
    x ^ y = x ^ z ↔ y = z ∨ x = 1 ∨ (x = 0 ∧ (y = 0 ↔ z = 0)) := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · obtain rfl | hz := eq_or_ne z 0
    · simp [zero_rpow_def]
    · simp +contextual [hz]
  obtain rfl | hx₁ := eq_or_ne x 1
  · simp
  simpa [hx₀, hx₁] using rpow_right_inj (y := y) (z := z) hx₀ hx₁

@[simp]
/--
lemma `rpow_eq_left_iff` / 引理 `rpow_eq_left_iff`

English:
lemma rpow_eq_left_iff
  given: {y : Real}
  statement: x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y != 0)
  proof: by
  simpa [or_left_comm] using rpow_eq_rpow_right_iff (x := x) (y := y) (z := 1)

中文:
引理 rpow_eq_left_iff
  条件: {y : 实数}
  结论: x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y != 0)
  证明: by
  simpa [or_left_comm] using rpow_eq_rpow_right_iff (x := x) (y := y) (z := 1)

Depends on / 依赖: or_left_comm, rpow_eq_rpow_right_iff
-/
lemma rpow_eq_left_iff {y : Real} : x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y != 0) := by
  simpa [or_left_comm] using rpow_eq_rpow_right_iff (x := x) (y := y) (z := 1)

/--
theorem `eq_rpow_inv_iff` / 定理 `eq_rpow_inv_iff`

English:
theorem eq_rpow_inv_iff
  given: {x y : Real>=0} {z : Real} (hz : z != 0)
  statement: x = y ^ z⁻¹ ↔ x ^ z = y
  proof: by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

中文:
定理 eq_rpow_inv_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : z != 0)
  结论: x = y ^ z⁻¹ ↔ x ^ z = y
  证明: by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

Depends on / 依赖: one_div, rpow_eq_rpow_iff, rpow_self_rpow_inv
-/
theorem eq_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

/--
theorem `rpow_inv_eq_iff` / 定理 `rpow_inv_eq_iff`

English:
theorem rpow_inv_eq_iff
  given: {x y : Real>=0} {z : Real} (hz : z != 0)
  statement: x ^ z⁻¹ = y ↔ x = y ^ z
  proof: by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

中文:
定理 rpow_inv_eq_iff
  条件: {x y : 实数>=0} {z : 实数} (hz : z != 0)
  结论: x ^ z⁻¹ = y ↔ x = y ^ z
  证明: by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

Depends on / 依赖: one_div, rpow_eq_rpow_iff, rpow_self_rpow_inv
-/
theorem rpow_inv_eq_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz]; rw [← one_div]; rw [rpow_self_rpow_inv hz]

/--
lemma `rpow_rpow_inv` / 引理 `rpow_rpow_inv`

English:
lemma rpow_rpow_inv
  given: {y : Real} (hy : y != 0) (x : Real>=0)
  statement: (x ^ y) ^ y⁻¹ = x
  proof: by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

中文:
引理 rpow_rpow_inv
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0)
  结论: (x ^ y) ^ y⁻¹ = x
  证明: by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]
-/
@[simp] lemma rpow_rpow_inv {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

/--
lemma `rpow_inv_rpow` / 引理 `rpow_inv_rpow`

English:
lemma rpow_inv_rpow
  given: {y : Real} (hy : y != 0) (x : Real>=0)
  statement: (x ^ y⁻¹) ^ y = x
  proof: by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]

中文:
引理 rpow_inv_rpow
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0)
  结论: (x ^ y⁻¹) ^ y = x
  证明: by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]
-/
@[simp] lemma rpow_inv_rpow {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]
/--
lemma `rpow_rpow_inv_eq_iff` / 引理 `rpow_rpow_inv_eq_iff`

English:
lemma rpow_rpow_inv_eq_iff
  given: {y : Real}
  statement: (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1
  proof: by
  grind only [rpow_rpow_inv, rpow_zero]

@[simp]

中文:
引理 rpow_rpow_inv_eq_iff
  条件: {y : 实数}
  结论: (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1
  证明: by
  grind only [rpow_rpow_inv, rpow_zero]

@[simp]

Depends on / 依赖: rpow_rpow_inv, rpow_zero
-/
lemma rpow_rpow_inv_eq_iff {y : Real} : (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1 := by
  grind only [rpow_rpow_inv, rpow_zero]

@[simp]
/--
lemma `rpow_inv_rpow_eq_iff` / 引理 `rpow_inv_rpow_eq_iff`

English:
lemma rpow_inv_rpow_eq_iff
  given: {y : Real}
  statement: (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1
  proof: by
  grind [rpow_rpow_inv_eq_iff]

中文:
引理 rpow_inv_rpow_eq_iff
  条件: {y : 实数}
  结论: (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1
  证明: by
  grind [rpow_rpow_inv_eq_iff]

Depends on / 依赖: rpow_rpow_inv_eq_iff
-/
lemma rpow_inv_rpow_eq_iff {y : Real} : (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]

/--
theorem `pow_rpow_inv_natCast` / 定理 `pow_rpow_inv_natCast`

English:
theorem pow_rpow_inv_natCast
  given: (x : Real>=0) {n : Nat} (hn : n != 0)
  statement: (x ^ n) ^ (n⁻¹ : Real) = x
  proof: by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn

中文:
定理 pow_rpow_inv_natCast
  条件: (x : 实数>=0) {n : 自然数} (hn : n != 0)
  结论: (x ^ n) ^ (n⁻¹ : 实数) = x
  证明: by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_pow, Real.pow_rpow_inv_natCast, coe_inj, coe_pow, coe_rpow, pow_rpow_inv_natCast
-/
theorem pow_rpow_inv_natCast (x : Real>=0) {n : Nat} (hn : n != 0) : (x ^ n) ^ (n⁻¹ : Real) = x := by
  rw [← NNReal.coe_inj]; rw [coe_rpow]; rw [NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn

/--
theorem `rpow_inv_natCast_pow` / 定理 `rpow_inv_natCast_pow`

English:
theorem rpow_inv_natCast_pow
  given: (x : Real>=0) {n : Nat} (hn : n != 0)
  statement: (x ^ (n⁻¹ : Real)) ^ n = x
  proof: by
  rw [← NNReal.coe_inj]; rw [NNReal.coe_pow]; rw [coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn

中文:
定理 rpow_inv_natCast_pow
  条件: (x : 实数>=0) {n : 自然数} (hn : n != 0)
  结论: (x ^ (n⁻¹ : 实数)) ^ n = x
  证明: by
  rw [← NNReal.coe_inj]; rw [NNReal.coe_pow]; rw [coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_pow, Real.rpow_inv_natCast_pow, coe_inj, coe_pow, coe_rpow, rpow_inv_natCast_pow
-/
theorem rpow_inv_natCast_pow (x : Real>=0) {n : Nat} (hn : n != 0) : (x ^ (n⁻¹ : Real)) ^ n = x := by
  rw [← NNReal.coe_inj]; rw [NNReal.coe_pow]; rw [coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn

/--
theorem `_root_.Real.toNNReal_rpow_of_nonneg` / 定理 `_root_.Real.toNNReal_rpow_of_nonneg`

English:
theorem _root_.Real.toNNReal_rpow_of_nonneg
  given: {x y : Real} (hx : 0 <= x)
  proof: by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow]; rw [Real.toNNReal_coe]

中文:
定理 _root_.实数.toNN实数_rpow_of_nonneg
  条件: {x y : 实数} (hx : 0 <= x)
  证明: by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow]; rw [Real.toNNReal_coe]

Depends on / 依赖: NNReal, NNReal.coe_rpow, Real.coe_toNNReal, Real.toNNReal_coe, coe_rpow, coe_toNNReal, nth_rw, toNNReal_coe
-/
theorem _root_.Real.toNNReal_rpow_of_nonneg {x y : Real} (hx : 0 <= x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y := by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow]; rw [Real.toNNReal_coe]

/--
theorem `strictMono_rpow_of_pos` / 定理 `strictMono_rpow_of_pos`

English:
theorem strictMono_rpow_of_pos
  given: {z : Real} (h : 0 < z)
  statement: StrictMono fun x : Real>=0 => x ^ z
  proof: fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h]

中文:
定理 strictMono_rpow_of_pos
  条件: {z : 实数} (h : 0 < z)
  结论: 严格递增 fun x : 实数>=0 => x ^ z
  证明: fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h]

Depends on / 依赖: NNReal, NNReal.rpow_lt_rpow, rpow_lt_rpow
-/
theorem strictMono_rpow_of_pos {z : Real} (h : 0 < z) : StrictMono fun x : Real>=0 => x ^ z :=
  fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h]

/--
theorem `monotone_rpow_of_nonneg` / 定理 `monotone_rpow_of_nonneg`

English:
theorem monotone_rpow_of_nonneg
  given: {z : Real} (h : 0 <= z)
  statement: Monotone fun x : Real>=0 => x ^ z
  proof: h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

中文:
定理 monotone_rpow_of_nonneg
  条件: {z : 实数} (h : 0 <= z)
  结论: 递增 fun x : 实数>=0 => x ^ z
  证明: h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

Depends on / 依赖: eq_or_lt, h.eq_or_lt.elim, monotone, monotone_const, rpow_zero, strictMono_rpow_of_pos
-/
theorem monotone_rpow_of_nonneg {z : Real} (h : 0 <= z) : Monotone fun x : Real>=0 => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0 => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0 => x ^ (1 / y)`. -/
@[simps! apply]
/--
Definition of `orderIsoRpow` / `orderIsoRpow` 的定义

English:
definition orderIsoRpow
  signature: (y : Real) (hy : 0 < y)
  body: (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

中文:
定义 orderIsoRpow
  签名: (y : 实数) (hy : 0 < y)
  定义体: (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

Depends on / 依赖: hy.ne.symm, one_div_mul_cancel, orderIsoOfRightInverse, rpow_mul, rpow_one, strictMono_rpow_of_pos
-/
def orderIsoRpow (y : Real) (hy : 0 < y) : Real>=0 ≃o Real>=0 :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

/--
theorem `orderIsoRpow_symm_eq` / 定理 `orderIsoRpow_symm_eq`

English:
theorem orderIsoRpow_symm_eq
  given: (y : Real) (hy : 0 < y)
  proof: by
  simp only [orderIsoRpow, one_div_one_div]; rfl

中文:
定理 orderIsoRpow_symm_eq
  条件: (y : 实数) (hy : 0 < y)
  证明: by
  simp only [orderIsoRpow, one_div_one_div]; rfl

Depends on / 依赖: one_div_one_div, orderIsoRpow
-/
theorem orderIsoRpow_symm_eq (y : Real) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]; rfl

/--
theorem `_root_.Real.nnnorm_rpow_of_nonneg` / 定理 `_root_.Real.nnnorm_rpow_of_nonneg`

English:
theorem _root_.Real.nnnorm_rpow_of_nonneg
  given: {x y : Real} (hx : 0 <= x)
  statement: ‖x ^ y‖₊ = ‖x‖₊ ^ y
  proof: by
  ext; exact Real.norm_rpow_of_nonneg hx

中文:
定理 _root_.实数.nnnorm_rpow_of_nonneg
  条件: {x y : 实数} (hx : 0 <= x)
  结论: ‖x ^ y‖₊ = ‖x‖₊ ^ y
  证明: by
  ext; exact Real.norm_rpow_of_nonneg hx

Depends on / 依赖: Real.norm_rpow_of_nonneg, norm_rpow_of_nonneg
-/
theorem _root_.Real.nnnorm_rpow_of_nonneg {x y : Real} (hx : 0 <= x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

end NNReal

namespace ENNReal

/--
Definition of `rpow` / `rpow` 的定义

English:
definition rpow
  signature: : Real>=0∞ -> Real -> Real>=0∞

中文:
定义 rpow
  签名: : 实数>=0∞ -> 实数 -> 实数>=0∞
-/
noncomputable def rpow : Real>=0∞ -> Real -> Real>=0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : Real>=0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow Real>=0∞ Real
  body: ⟨rpow⟩

@[simp]

中文:
实例 :
  签名: 幂 实数>=0∞ 实数
  定义体: ⟨rpow⟩

@[simp]
-/
noncomputable instance : Pow Real>=0∞ Real :=
  ⟨rpow⟩

@[simp]
/--
theorem `rpow_eq_pow` / 定理 `rpow_eq_pow`

English:
theorem rpow_eq_pow
  given: (x : Real>=0∞) (y : Real)
  statement: rpow x y = x ^ y
  proof: rfl

@[simp]

中文:
定理 rpow_eq_pow
  条件: (x : 实数>=0∞) (y : 实数)
  结论: rpow x y = x ^ y
  证明: rfl

@[simp]
-/
theorem rpow_eq_pow (x : Real>=0∞) (y : Real) : rpow x y = x ^ y :=
  rfl

@[simp]
/--
theorem `rpow_zero` / 定理 `rpow_zero`

English:
theorem rpow_zero
  given: {x : Real>=0∞}
  statement: x ^ (0 : Real) = 1
  proof: by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [← none_eq_top]

中文:
定理 rpow_zero
  条件: {x : 实数>=0∞}
  结论: x ^ (0 : 实数) = 1
  证明: by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [← none_eq_top]

Depends on / 依赖: Pow.pow, none_eq_top
-/
theorem rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [← none_eq_top]

/--
theorem `rpow_zero_pos` / 定理 `rpow_zero_pos`

English:
theorem rpow_zero_pos
  given: (x : Real>=0∞)
  statement: 0 < x ^ (0 : Real)
  proof: by rw [rpow_zero]; exact one_pos

中文:
定理 rpow_zero_pos
  条件: (x : 实数>=0∞)
  结论: 0 < x ^ (0 : 实数)
  证明: by rw [rpow_zero]; exact one_pos

Depends on / 依赖: one_pos, rpow_zero
-/
theorem rpow_zero_pos (x : Real>=0∞) : 0 < x ^ (0 : Real) := by rw [rpow_zero]; exact one_pos

/--
theorem `top_rpow_def` / 定理 `top_rpow_def`

English:
theorem top_rpow_def
  given: (y : Real)
  statement: (⊤ : Real>=0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0
  proof: rfl

@[simp]

中文:
定理 top_rpow_def
  条件: (y : 实数)
  结论: (⊤ : 实数>=0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0
  证明: rfl

@[simp]
-/
theorem top_rpow_def (y : Real) : (⊤ : Real>=0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl

@[simp]
/--
theorem `top_rpow_of_pos` / 定理 `top_rpow_of_pos`

English:
theorem top_rpow_of_pos
  given: {y : Real} (h : 0 < y)
  statement: (⊤ : Real>=0∞) ^ y = ⊤
  proof: by simp [top_rpow_def, h]

@[simp]

中文:
定理 top_rpow_of_pos
  条件: {y : 实数} (h : 0 < y)
  结论: (⊤ : 实数>=0∞) ^ y = ⊤
  证明: by simp [top_rpow_def, h]

@[simp]

Depends on / 依赖: top_rpow_def
-/
theorem top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : Real>=0∞) ^ y = ⊤ := by simp [top_rpow_def, h]

@[simp]
/--
theorem `top_rpow_of_neg` / 定理 `top_rpow_of_neg`

English:
theorem top_rpow_of_neg
  given: {y : Real} (h : y < 0)
  statement: (⊤ : Real>=0∞) ^ y = 0
  proof: by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]

中文:
定理 top_rpow_of_neg
  条件: {y : 实数} (h : y < 0)
  结论: (⊤ : 实数>=0∞) ^ y = 0
  证明: by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]

Depends on / 依赖: ne_of_lt, top_rpow_def
-/
theorem top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : Real>=0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]
/--
theorem `zero_rpow_of_pos` / 定理 `zero_rpow_of_pos`

English:
theorem zero_rpow_of_pos
  given: {y : Real} (h : 0 < y)
  statement: (0 : Real>=0∞) ^ y = 0
  proof: by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [asymm h, ne_of_gt h]

@[simp]

中文:
定理 zero_rpow_of_pos
  条件: {y : 实数} (h : 0 < y)
  结论: (0 : 实数>=0∞) ^ y = 0
  证明: by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [asymm h, ne_of_gt h]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.some_eq_coe, Pow.pow, coe_zero, ne_of_gt, some_eq_coe
-/
theorem zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 : Real>=0∞) ^ y = 0 := by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [asymm h, ne_of_gt h]

@[simp]
/--
theorem `zero_rpow_of_neg` / 定理 `zero_rpow_of_neg`

English:
theorem zero_rpow_of_neg
  given: {y : Real} (h : y < 0)
  statement: (0 : Real>=0∞) ^ y = ⊤
  proof: by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h]

中文:
定理 zero_rpow_of_neg
  条件: {y : 实数} (h : y < 0)
  结论: (0 : 实数>=0∞) ^ y = ⊤
  证明: by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h]

Depends on / 依赖: ENNReal, ENNReal.coe_zero, ENNReal.some_eq_coe, Pow.pow, coe_zero, some_eq_coe
-/
theorem zero_rpow_of_neg {y : Real} (h : y < 0) : (0 : Real>=0∞) ^ y = ⊤ := by
  rw [← ENNReal.coe_zero]; rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h]

/--
theorem `zero_rpow_def` / 定理 `zero_rpow_def`

English:
theorem zero_rpow_def
  given: (y : Real)
  statement: (0 : Real>=0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤
  proof: by
  rcases lt_trichotomy (0 : Real) y with (H | rfl | H)
  · simp [H, zero_rpow_of_pos]
  · simp
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]

中文:
定理 zero_rpow_def
  条件: (y : 实数)
  结论: (0 : 实数>=0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤
  证明: by
  rcases lt_trichotomy (0 : Real) y with (H | rfl | H)
  · simp [H, zero_rpow_of_pos]
  · simp
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]

Depends on / 依赖: lt_trichotomy, ne_of_lt, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem zero_rpow_def (y : Real) : (0 : Real>=0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ := by
  rcases lt_trichotomy (0 : Real) y with (H | rfl | H)
  · simp [H, zero_rpow_of_pos]
  · simp
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]
/--
theorem `zero_rpow_mul_self` / 定理 `zero_rpow_mul_self`

English:
theorem zero_rpow_mul_self
  given: (y : Real)
  statement: (0 : Real>=0∞) ^ y * (0 : Real>=0∞) ^ y = (0 : Real>=0∞) ^ y
  proof: by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

@[norm_cast]

中文:
定理 zero_rpow_mul_self
  条件: (y : 实数)
  结论: (0 : 实数>=0∞) ^ y * (0 : 实数>=0∞) ^ y = (0 : 实数>=0∞) ^ y
  证明: by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

@[norm_cast]

Depends on / 依赖: exacts, one_mul, split_ifs, top_mul_top, zero_mul, zero_rpow_def
-/
theorem zero_rpow_mul_self (y : Real) : (0 : Real>=0∞) ^ y * (0 : Real>=0∞) ^ y = (0 : Real>=0∞) ^ y := by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

@[norm_cast]
/--
theorem `coe_rpow_of_ne_zero` / 定理 `coe_rpow_of_ne_zero`

English:
theorem coe_rpow_of_ne_zero
  given: {x : Real>=0} (h : x != 0) (y : Real)
  statement: (↑(x ^ y) : Real>=0∞) = x ^ y
  proof: by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]

@[norm_cast]

中文:
定理 coe_rpow_of_ne_zero
  条件: {x : 实数>=0} (h : x != 0) (y : 实数)
  结论: (↑(x ^ y) : 实数>=0∞) = x ^ y
  证明: by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]

@[norm_cast]

Depends on / 依赖: ENNReal, ENNReal.some_eq_coe, Pow.pow, some_eq_coe
-/
theorem coe_rpow_of_ne_zero {x : Real>=0} (h : x != 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y := by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]

@[norm_cast]
/--
theorem `coe_rpow_of_nonneg` / 定理 `coe_rpow_of_nonneg`

English:
theorem coe_rpow_of_nonneg
  given: (x : Real>=0) {y : Real} (h : 0 <= y)
  statement: ↑(x ^ y) = (x : Real>=0∞) ^ y
  proof: by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _

中文:
定理 coe_rpow_of_nonneg
  条件: (x : 实数>=0) {y : 实数} (h : 0 <= y)
  结论: ↑(x ^ y) = (x : 实数>=0∞) ^ y
  证明: by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _

Depends on / 依赖: H.symm, NNReal, NNReal.zero_rpow, coe_rpow_of_ne_zero, le_iff_eq_or_lt, ne_of_gt, zero_rpow, zero_rpow_of_pos
-/
theorem coe_rpow_of_nonneg (x : Real>=0) {y : Real} (h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y := by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _

/--
theorem `coe_rpow_def` / 定理 `coe_rpow_def`

English:
theorem coe_rpow_def
  given: (x : Real>=0) (y : Real)
  proof: rfl

中文:
定理 coe_rpow_def
  条件: (x : 实数>=0) (y : 实数)
  证明: rfl
-/
theorem coe_rpow_def (x : Real>=0) (y : Real) :
    (x : Real>=0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else ↑(x ^ y) :=
  rfl

/--
theorem `rpow_ofNNReal` / 定理 `rpow_ofNNReal`

English:
theorem rpow_ofNNReal
  given: {M : Real>=0} {P : Real} (hP : 0 <= P)
  statement: (M : Real>=0∞) ^ P = ↑(M ^ P)
  proof: by
  rw [ENNReal.coe_rpow_of_nonneg _ hP]; rw [← ENNReal.rpow_eq_pow]

@[simp]

中文:
定理 rpow_ofNN实数
  条件: {M : 实数>=0} {P : 实数} (hP : 0 <= P)
  结论: (M : 实数>=0∞) ^ P = ↑(M ^ P)
  证明: by
  rw [ENNReal.coe_rpow_of_nonneg _ hP]; rw [← ENNReal.rpow_eq_pow]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_eq_pow, coe_rpow_of_nonneg, rpow_eq_pow
-/
theorem rpow_ofNNReal {M : Real>=0} {P : Real} (hP : 0 <= P) : (M : Real>=0∞) ^ P = ↑(M ^ P) := by
  rw [ENNReal.coe_rpow_of_nonneg _ hP]; rw [← ENNReal.rpow_eq_pow]

@[simp]
/--
theorem `rpow_one` / 定理 `rpow_one`

English:
theorem rpow_one
  given: (x : Real>=0∞)
  statement: x ^ (1 : Real) = x
  proof: by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_gt

@[simp]

中文:
定理 rpow_one
  条件: (x : 实数>=0∞)
  结论: x ^ (1 : 实数) = x
  证明: by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_gt

@[simp]

Depends on / 依赖: NNReal, NNReal.rpow_one, and_imp, dif_pos, ite_eq_right_iff, not_gt, rpow_one, top_ne_coe, zero_le_one, zero_le_one.not_gt, zero_lt_one
-/
theorem rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_gt

@[simp]
/--
theorem `one_rpow` / 定理 `one_rpow`

English:
theorem one_rpow
  given: (x : Real)
  statement: (1 : Real>=0∞) ^ x = 1
  proof: by
  rw [← coe_one]; rw [← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]

中文:
定理 one_rpow
  条件: (x : 实数)
  结论: (1 : 实数>=0∞) ^ x = 1
  证明: by
  rw [← coe_one]; rw [← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]

Depends on / 依赖: coe_one, coe_rpow_of_ne_zero, one_ne_zero
-/
theorem one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1 := by
  rw [← coe_one]; rw [← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]
/--
theorem `rpow_eq_zero_iff` / 定理 `rpow_eq_zero_iff`

English:
theorem rpow_eq_zero_iff
  given: {x : Real>=0∞} {y : Real}
  statement: x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0
  proof: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · si

中文:
定理 rpow_eq_zero_iff
  条件: {x : 实数>=0∞} {y : 实数}
  结论: x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0
  证明: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · si

Depends on / 依赖: coe_rpow_of_ne_zero, le_of_lt, lt_trichotomy, top_rpow_of_neg, top_rpow_of_pos, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem rpow_eq_zero_iff {x : Real>=0∞} {y : Real} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

/--
lemma `rpow_eq_zero_iff_of_pos` / 引理 `rpow_eq_zero_iff_of_pos`

English:
lemma rpow_eq_zero_iff_of_pos
  given: {x : Real>=0∞} {y : Real} (hy : 0 < y)
  statement: x ^ y = 0 ↔ x = 0
  proof: by
  simp [hy, hy.not_gt]

@[simp]

中文:
引理 rpow_eq_zero_iff_of_pos
  条件: {x : 实数>=0∞} {y : 实数} (hy : 0 < y)
  结论: x ^ y = 0 ↔ x = 0
  证明: by
  simp [hy, hy.not_gt]

@[simp]

Depends on / 依赖: hy.not_gt, not_gt
-/
lemma rpow_eq_zero_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y = 0 ↔ x = 0 := by
  simp [hy, hy.not_gt]

@[simp]
/--
theorem `rpow_eq_top_iff` / 定理 `rpow_eq_top_iff`

English:
theorem rpow_eq_top_iff
  given: {x : Real>=0∞} {y : Real}
  statement: x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y
  proof: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · si

中文:
定理 rpow_eq_top_iff
  条件: {x : 实数>=0∞} {y : 实数}
  结论: x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y
  证明: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · si

Depends on / 依赖: coe_rpow_of_ne_zero, le_of_lt, lt_trichotomy, top_rpow_of_neg, top_rpow_of_pos, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem rpow_eq_top_iff {x : Real>=0∞} {y : Real} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

/--
theorem `rpow_eq_top_iff_of_pos` / 定理 `rpow_eq_top_iff_of_pos`

English:
theorem rpow_eq_top_iff_of_pos
  given: {x : Real>=0∞} {y : Real} (hy : 0 < y)
  statement: x ^ y = ⊤ ↔ x = ⊤
  proof: by
  simp [rpow_eq_top_iff, hy, asymm hy]

中文:
定理 rpow_eq_top_iff_of_pos
  条件: {x : 实数>=0∞} {y : 实数} (hy : 0 < y)
  结论: x ^ y = ⊤ ↔ x = ⊤
  证明: by
  simp [rpow_eq_top_iff, hy, asymm hy]

Depends on / 依赖: rpow_eq_top_iff
-/
theorem rpow_eq_top_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]

/--
lemma `rpow_lt_top_iff_of_pos` / 引理 `rpow_lt_top_iff_of_pos`

English:
lemma rpow_lt_top_iff_of_pos
  given: {x : Real>=0∞} {y : Real} (hy : 0 < y)
  statement: x ^ y < ∞ ↔ x < ∞
  proof: by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]

中文:
引理 rpow_lt_top_iff_of_pos
  条件: {x : 实数>=0∞} {y : 实数} (hy : 0 < y)
  结论: x ^ y < ∞ ↔ x < ∞
  证明: by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]

Depends on / 依赖: lt_top_iff_ne_top, rpow_eq_top_iff_of_pos
-/
lemma rpow_lt_top_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y < ∞ ↔ x < ∞ := by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]

/--
theorem `rpow_eq_top_of_nonneg` / 定理 `rpow_eq_top_of_nonneg`

English:
theorem rpow_eq_top_of_nonneg
  given: (x : Real>=0∞) {y : Real} (hy0 : 0 <= y)
  statement: x ^ y = ⊤ -> x = ⊤
  proof: by
  simp +contextual [ENNReal.rpow_eq_top_iff, hy0.not_gt]

中文:
定理 rpow_eq_top_of_nonneg
  条件: (x : 实数>=0∞) {y : 实数} (hy0 : 0 <= y)
  结论: x ^ y = ⊤ -> x = ⊤
  证明: by
  simp +contextual [ENNReal.rpow_eq_top_iff, hy0.not_gt]

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_top_iff, contextual, hy0.not_gt, not_gt, rpow_eq_top_iff
-/
theorem rpow_eq_top_of_nonneg (x : Real>=0∞) {y : Real} (hy0 : 0 <= y) : x ^ y = ⊤ -> x = ⊤ := by
  simp +contextual [ENNReal.rpow_eq_top_iff, hy0.not_gt]

-- This is an unsafe rule since we want to try `rpow_ne_top_of_ne_zero` if `y < 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
theorem `rpow_ne_top_of_nonneg` / 定理 `rpow_ne_top_of_nonneg`

English:
theorem rpow_ne_top_of_nonneg
  given: {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤)
  statement: x ^ y != ⊤
  proof: mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

中文:
定理 rpow_ne_top_of_nonneg
  条件: {x : 实数>=0∞} {y : 实数} (hy0 : 0 <= y) (h : x != ⊤)
  结论: x ^ y != ⊤
  证明: mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_top_of_nonneg, rpow_eq_top_of_nonneg
-/
theorem rpow_ne_top_of_nonneg {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y != ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg'` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
theorem `rpow_ne_top_of_nonneg'` / 定理 `rpow_ne_top_of_nonneg'`

English:
theorem rpow_ne_top_of_nonneg'
  given: {y : Real} {x : Real>=0∞} (hx : 0 < x) (hx' : x != ⊤)
  statement: x ^ y != ⊤
  proof: fun h => by simp [rpow_eq_top_iff, hx.ne', hx'] at h

中文:
定理 rpow_ne_top_of_nonneg'
  条件: {y : 实数} {x : 实数>=0∞} (hx : 0 < x) (hx' : x != ⊤)
  结论: x ^ y != ⊤
  证明: fun h => by simp [rpow_eq_top_iff, hx.ne', hx'] at h

Depends on / 依赖: hx.ne, rpow_eq_top_iff
-/
theorem rpow_ne_top_of_nonneg' {y : Real} {x : Real>=0∞} (hx : 0 < x) (hx' : x != ⊤) : x ^ y != ⊤ :=
  fun h => by simp [rpow_eq_top_iff, hx.ne', hx'] at h

/--
theorem `rpow_lt_top_of_nonneg` / 定理 `rpow_lt_top_of_nonneg`

English:
theorem rpow_lt_top_of_nonneg
  given: {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤)
  statement: x ^ y < ⊤
  proof: lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

中文:
定理 rpow_lt_top_of_nonneg
  条件: {x : 实数>=0∞} {y : 实数} (hy0 : 0 <= y) (h : x != ⊤)
  结论: x ^ y < ⊤
  证明: lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

Depends on / 依赖: ENNReal, ENNReal.rpow_ne_top_of_nonneg, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, rpow_ne_top_of_nonneg
-/
theorem rpow_lt_top_of_nonneg {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/--
theorem `rpow_ne_top_of_ne_zero` / 定理 `rpow_ne_top_of_ne_zero`

English:
theorem rpow_ne_top_of_ne_zero
  given: {x : Real>=0∞} {y : Real} (hx : x != 0) (hx' : x != ⊤)
  statement: x ^ y != ⊤
  proof: by
  simp [rpow_eq_top_iff, hx, hx']

中文:
定理 rpow_ne_top_of_ne_zero
  条件: {x : 实数>=0∞} {y : 实数} (hx : x != 0) (hx' : x != ⊤)
  结论: x ^ y != ⊤
  证明: by
  simp [rpow_eq_top_iff, hx, hx']

Depends on / 依赖: rpow_eq_top_iff
-/
theorem rpow_ne_top_of_ne_zero {x : Real>=0∞} {y : Real} (hx : x != 0) (hx' : x != ⊤) : x ^ y != ⊤ := by
  simp [rpow_eq_top_iff, hx, hx']

/--
theorem `rpow_add` / 定理 `rpow_add`

English:
theorem rpow_add
  given: {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: by
  cases x with
  | top => exact (h'x rfl).elim
  | coe x =>
    have : x != 0 := fun h => by simp [h] at hx
    simp [← coe_rpow_of_ne_zero this, NNReal.rpow_add this]

中文:
定理 rpow_add
  条件: {x : 实数>=0∞} (y z : 实数) (hx : x != 0) (h'x : x != ⊤)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: by
  cases x with
  | top => exact (h'x rfl).elim
  | coe x =>
    have : x != 0 := fun h => by simp [h] at hx
    simp [← coe_rpow_of_ne_zero this, NNReal.rpow_add this]

Depends on / 依赖: NNReal, NNReal.rpow_add, coe_rpow_of_ne_zero, rpow_add
-/
theorem rpow_add {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤) : x ^ (y + z) = x ^ y * x ^ z := by
  cases x with
  | top => exact (h'x rfl).elim
  | coe x =>
    have : x != 0 := fun h => by simp [h] at hx
    simp [← coe_rpow_of_ne_zero this, NNReal.rpow_add this]

/--
theorem `rpow_add_of_nonneg` / 定理 `rpow_add_of_nonneg`

English:
theorem rpow_add_of_nonneg
  given: {x : Real>=0∞} (y z : Real) (hy : 0 <= y) (hz : 0 <= z)
  proof: by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl | hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl | hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.

中文:
定理 rpow_add_of_nonneg
  条件: {x : 实数>=0∞} (y z : 实数) (hy : 0 <= y) (hz : 0 <= z)
  证明: by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl | hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl | hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.

Depends on / 依赖: NNReal, NNReal.rpow_add_of_nonneg, add_nonneg, add_pos, add_zero, coe_rpow_of_nonneg, eq_or_lt, hy.eq_or_lt, hz.eq_or_lt, mul_one, one_mul, recTopCoe, rpow_add_of_nonneg, rpow_zero, top_rpow_of_pos, zero_add
-/
theorem rpow_add_of_nonneg {x : Real>=0∞} (y z : Real) (hy : 0 <= y) (hz : 0 <= z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl | hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl | hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

/--
lemma `rpow_add_of_add_pos` / 引理 `rpow_add_of_add_pos`

English:
lemma rpow_add_of_add_pos
  given: {x : Real>=0∞} (hx : x != ⊤) (y z : Real) (hyz : 0 < y + z)
  proof: by
  obtain (rfl | hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by linarith
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]

中文:
引理 rpow_add_of_add_pos
  条件: {x : 实数>=0∞} (hx : x != ⊤) (y z : 实数) (hyz : 0 < y + z)
  证明: by
  obtain (rfl | hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by linarith
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]

Depends on / 依赖: ENNReal, ENNReal.rpow_add, ENNReal.zero_rpow_of_pos, eq_or_ne, rpow_add, zero_rpow_of_pos
-/
lemma rpow_add_of_add_pos {x : Real>=0∞} (hx : x != ⊤) (y z : Real) (hyz : 0 < y + z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  obtain (rfl | hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by linarith
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]

/--
theorem `rpow_neg` / 定理 `rpow_neg`

English:
theorem rpow_neg
  given: (x : Real>=0∞) (y : Real)
  statement: x ^ (-y) = (x ^ y)⁻¹
  proof: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
  

中文:
定理 rpow_neg
  条件: (x : 实数>=0∞) (y : 实数)
  结论: x ^ (-y) = (x ^ y)⁻¹
  证明: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
  

Depends on / 依赖: NNReal, NNReal.rpow_neg, coe_inv, coe_rpow_of_ne_zero, lt_trichotomy, neg_pos, neg_pos.mpr, rpow_neg, top_rpow_of_neg, top_rpow_of_pos, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y)⁻¹ := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y != 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]

/--
theorem `rpow_sub` / 定理 `rpow_sub`

English:
theorem rpow_sub
  given: {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: by
  rw [sub_eq_add_neg]; rw [rpow_add _ _ hx h'x]; rw [rpow_neg]; rw [div_eq_mul_inv]

中文:
定理 rpow_sub
  条件: {x : 实数>=0∞} (y z : 实数) (hx : x != 0) (h'x : x != ⊤)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: by
  rw [sub_eq_add_neg]; rw [rpow_add _ _ hx h'x]; rw [rpow_neg]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, rpow_add, rpow_neg, sub_eq_add_neg
-/
theorem rpow_sub {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg]; rw [rpow_add _ _ hx h'x]; rw [rpow_neg]; rw [div_eq_mul_inv]

/--
theorem `rpow_neg_one` / 定理 `rpow_neg_one`

English:
theorem rpow_neg_one
  given: (x : Real>=0∞)
  statement: x ^ (-1 : Real) = x⁻¹
  proof: by simp [rpow_neg]

中文:
定理 rpow_neg_one
  条件: (x : 实数>=0∞)
  结论: x ^ (-1 : 实数) = x⁻¹
  证明: by simp [rpow_neg]

Depends on / 依赖: rpow_neg
-/
theorem rpow_neg_one (x : Real>=0∞) : x ^ (-1 : Real) = x⁻¹ := by simp [rpow_neg]

/--
theorem `rpow_mul` / 定理 `rpow_mul`

English:
theorem rpow_mul
  given: (x : Real>=0∞) (y z : Real)
  statement: x ^ (y * z) = (x ^ y) ^ z
  proof: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of

中文:
定理 rpow_mul
  条件: (x : 实数>=0∞) (y z : 实数)
  结论: x ^ (y * z) = (x ^ y) ^ z
  证明: by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of

Depends on / 依赖: lt_trichotomy, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg, mul_pos, mul_pos_of_neg_of_neg, top_rpow_of_neg, top_rpow_of_pos, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (x ^ y) ^ z := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y != 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero, h, this, NNReal.rpow_mul]

@[simp, norm_cast]
/--
theorem `rpow_natCast` / 定理 `rpow_natCast`

English:
theorem rpow_natCast
  given: (x : Real>=0∞) (n : Nat)
  statement: x ^ (n : Real) = x ^ n
  proof: by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_ne_zero _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

@[simp]

中文:
定理 rpow_natCast
  条件: (x : 实数>=0∞) (n : 自然数)
  结论: x ^ (n : 实数) = x ^ n
  证明: by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_ne_zero _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

@[simp]

Depends on / 依赖: Nat.cast_add_one_pos, Nat.cast_nonneg, Nat.succ_ne_zero, cast_add_one_pos, cast_nonneg, coe_rpow_of_nonneg, succ_ne_zero, top_pow, top_rpow_of_pos
-/
theorem rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : Real) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_ne_zero _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

@[simp]
/--
lemma `rpow_ofNat` / 引理 `rpow_ofNat`

English:
lemma rpow_ofNat
  given: (x : Real>=0∞) (n : Nat) [n.AtLeastTwo]
  proof: rpow_natCast x n

@[simp, norm_cast]

中文:
引理 rpow_of自然数
  条件: (x : 实数>=0∞) (n : 自然数) [n.AtLeastTwo]
  证明: rpow_natCast x n

@[simp, norm_cast]

Depends on / 依赖: rpow_natCast
-/
lemma rpow_ofNat (x : Real>=0∞) (n : Nat) [n.AtLeastTwo] :
    x ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n) :=
  rpow_natCast x n

@[simp, norm_cast]
/--
lemma `rpow_intCast` / 引理 `rpow_intCast`

English:
lemma rpow_intCast
  given: (x : Real>=0∞) (n : Int)
  statement: x ^ (n : Real) = x ^ n
  proof: by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

中文:
引理 rpow_intCast
  条件: (x : 实数>=0∞) (n : 整数)
  结论: x ^ (n : 实数) = x ^ n
  证明: by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, Int.ofNat_eq_natCast, cast_natCast, cast_negSucc, ofNat_eq_natCast, rpow_natCast, rpow_neg, zpow_natCast, zpow_negSucc
-/
lemma rpow_intCast (x : Real>=0∞) (n : Int) : x ^ (n : Real) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

/--
theorem `rpow_two` / 定理 `rpow_two`

English:
theorem rpow_two
  given: (x : Real>=0∞)
  statement: x ^ (2 : Real) = x ^ 2
  proof: rpow_ofNat x 2

中文:
定理 rpow_two
  条件: (x : 实数>=0∞)
  结论: x ^ (2 : 实数) = x ^ 2
  证明: rpow_ofNat x 2

Depends on / 依赖: rpow_ofNat
-/
theorem rpow_two (x : Real>=0∞) : x ^ (2 : Real) = x ^ 2 := rpow_ofNat x 2

/--
theorem `mul_rpow_eq_ite` / 定理 `mul_rpow_eq_ite`

English:
theorem mul_rpow_eq_ite
  given: (x y : Real>=0∞) (z : Real)
  proof: by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_gt
  wlog hxy : x <= y
  · convert! this y x z hz (le_of_not_ge hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_gt]

中文:
定理 mul_rpow_eq_ite
  条件: (x y : 实数>=0∞) (z : 实数)
  证明: by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_gt
  wlog hxy : x <= y
  · convert! this y x z hz (le_of_not_ge hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_gt]

Depends on / 依赖: and_comm, bot_unique, coe_eq_zero, convert, eq_or_ne, hz.lt_or_gt, hz.not_gt, le_of_not_ge, lt_or_gt, mul_comm, ne_eq, not_gt, or_comm, replace, top_unique
-/
theorem mul_rpow_eq_ite (x y : Real>=0∞) (z : Real) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_gt
  wlog hxy : x <= y
  · convert! this y x z hz (le_of_not_ge hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_gt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x
  · rcases hz with hz | hz <;> simp [hz, top_unique hxy]
  induction y
  · rw [ne_eq, coe_eq_zero] at hx0
    rcases hz with hz | hz <;> simp [*]
  simp only [*]
  norm_cast at *
  rw [← coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0)]; rw [NNReal.mul_rpow]
  norm_cast

/--
theorem `mul_rpow_of_ne_top` / 定理 `mul_rpow_of_ne_top`

English:
theorem mul_rpow_of_ne_top
  given: {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) (z : Real)
  proof: by simp [*, mul_rpow_eq_ite]

@[norm_cast]

中文:
定理 mul_rpow_of_ne_top
  条件: {x y : 实数>=0∞} (hx : x != ⊤) (hy : y != ⊤) (z : 实数)
  证明: by simp [*, mul_rpow_eq_ite]

@[norm_cast]

Depends on / 依赖: mul_rpow_eq_ite
-/
theorem mul_rpow_of_ne_top {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) (z : Real) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

@[norm_cast]
/--
theorem `coe_mul_rpow` / 定理 `coe_mul_rpow`

English:
theorem coe_mul_rpow
  given: (x y : Real>=0) (z : Real)
  statement: ((x : Real>=0∞) * y) ^ z = (x : Real>=0∞) ^ z * (y : Real>=0∞) ^ z
  proof: mul_rpow_of_ne_top coe_ne_top coe_ne_top z

中文:
定理 coe_mul_rpow
  条件: (x y : 实数>=0) (z : 实数)
  结论: ((x : 实数>=0∞) * y) ^ z = (x : 实数>=0∞) ^ z * (y : 实数>=0∞) ^ z
  证明: mul_rpow_of_ne_top coe_ne_top coe_ne_top z

Depends on / 依赖: HasPullback, coe_ne_top, hasPullback_ofHasPullbacksAgainst, hasPullback_symmetry, mul_rpow_of_ne_top
-/
theorem coe_mul_rpow (x y : Real>=0) (z : Real) : ((x : Real>=0∞) * y) ^ z = (x : Real>=0∞) ^ z * (y : Real>=0∞) ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z

/--
theorem `prod_coe_rpow` / 定理 `prod_coe_rpow`

English:
theorem prod_coe_rpow
  given: {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

中文:
定理 prod_coe_rpow
  条件: {ι} (s : 有限集 ι) (f : ι -> 实数>=0) (r : 实数)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

Depends on / 依赖: Finset, Finset.induction, IsStableUnderBaseChangeAgainst, MorphismProperty, MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong, classical, coe_mul, coe_mul_rpow, insert, isStableUnderBaseChangeAlong, prod_insert, simp_rw
-/
theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real) :
    ∏ i in s, (f i : Real>=0∞) ^ r = ((∏ i in s, f i : Real>=0) : Real>=0∞) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

/--
theorem `mul_rpow_of_ne_zero` / 定理 `mul_rpow_of_ne_zero`

English:
theorem mul_rpow_of_ne_zero
  given: {x y : Real>=0∞} (hx : x != 0) (hy : y != 0) (z : Real)
  proof: by simp [*, mul_rpow_eq_ite]

中文:
定理 mul_rpow_of_ne_zero
  条件: {x y : 实数>=0∞} (hx : x != 0) (hy : y != 0) (z : 实数)
  证明: by simp [*, mul_rpow_eq_ite]

Depends on / 依赖: IsStableUnderBaseChangeAgainst, MorphismProperty, MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong, isStableUnderBaseChangeAlong, mul_rpow_eq_ite
-/
theorem mul_rpow_of_ne_zero {x y : Real>=0∞} (hx : x != 0) (hy : y != 0) (z : Real) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

/--
theorem `mul_rpow_of_nonneg` / 定理 `mul_rpow_of_nonneg`

English:
theorem mul_rpow_of_nonneg
  given: (x y : Real>=0∞) {z : Real} (hz : 0 <= z)
  statement: (x * y) ^ z = x ^ z * y ^ z
  proof: by
  simp [hz.not_gt, mul_rpow_eq_ite]

中文:
定理 mul_rpow_of_nonneg
  条件: (x y : 实数>=0∞) {z : 实数} (hz : 0 <= z)
  结论: (x * y) ^ z = x ^ z * y ^ z
  证明: by
  simp [hz.not_gt, mul_rpow_eq_ite]

Depends on / 依赖: hz.not_gt, mul_rpow_eq_ite, not_gt
-/
theorem mul_rpow_of_nonneg (x y : Real>=0∞) {z : Real} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_gt, mul_rpow_eq_ite]

/--
theorem `prod_rpow_of_ne_top` / 定理 `prod_rpow_of_ne_top`

English:
theorem prod_rpow_of_ne_top
  given: {ι} {s : Finset ι} {f : ι -> Real>=0∞} (hf : forall i in s, f i != ∞) (r : Real)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
have h2f : forall i in s, f i != ∞ := fun i hi => hf i mem_insert_of_mem hi
    rw [prod_insert hi]; rw [prod_insert hi]; rw [ih h2f]; rw [← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply 

中文:
定理 prod_rpow_of_ne_top
  条件: {ι} {s : 有限集 ι} {f : ι -> 实数>=0∞} (hf : 对任意 i in s, f i != ∞) (r : 实数)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
have h2f : forall i in s, f i != ∞ := fun i hi => hf i mem_insert_of_mem hi
    rw [prod_insert hi]; rw [prod_insert hi]; rw [ih h2f]; rw [← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply 

Depends on / 依赖: Finset, Finset.induction, classical, insert, mem_insert_of_mem, mem_insert_self, mul_rpow_of_ne_top, prod_insert, prod_ne_top
-/
theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι -> Real>=0∞} (hf : forall i in s, f i != ∞) (r : Real) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
have h2f : forall i in s, f i != ∞ := fun i hi => hf i mem_insert_of_mem hi
    rw [prod_insert hi]; rw [prod_insert hi]; rw [ih h2f]; rw [← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_ne_top h2f

/--
theorem `prod_rpow_of_nonneg` / 定理 `prod_rpow_of_nonneg`

English:
theorem prod_rpow_of_nonneg
  given: {ι} {s : Finset ι} {f : ι -> Real>=0∞} {r : Real} (hr : 0 <= r)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

中文:
定理 prod_rpow_of_nonneg
  条件: {ι} {s : 有限集 ι} {f : ι -> 实数>=0∞} {r : 实数} (hr : 0 <= r)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

Depends on / 依赖: Finset, Finset.induction, classical, insert, mul_rpow_of_nonneg, prod_insert, simp_rw
-/
theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι -> Real>=0∞} {r : Real} (hr : 0 <= r) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

/--
theorem `inv_rpow` / 定理 `inv_rpow`

English:
theorem inv_rpow
  given: (x : Real>=0∞) (y : Real)
  statement: x⁻¹ ^ y = (x ^ y)⁻¹
  proof: by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_gt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zer

中文:
定理 inv_rpow
  条件: (x : 实数>=0∞) (y : 实数)
  结论: x⁻¹ ^ y = (x ^ y)⁻¹
  证明: by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_gt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zer

Depends on / 依赖: Bicategory, Bicategory.Strict, Category, ENNReal, ENNReal.eq_inv_of_mul_eq_one_left, ENNReal.inv_mul_cancel, ENNReal.inv_ne_zero, Strict, StrictBicategory, StrictBicategory.category, category, eq_inv_of_mul_eq_one_left, eq_or_ne, h_top, hy.lt_or_gt, inv_mul_cancel, inv_ne_zero, inv_one, lt_or_gt, mul_rpow_of_ne_zero
-/
theorem inv_rpow (x : Real>=0∞) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_gt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0]; rw [ENNReal.inv_mul_cancel h0 h_top]; rw [one_rpow]

/--
theorem `div_rpow_of_nonneg` / 定理 `div_rpow_of_nonneg`

English:
theorem div_rpow_of_nonneg
  given: (x y : Real>=0∞) {z : Real} (hz : 0 <= z)
  statement: (x / y) ^ z = x ^ z / y ^ z
  proof: by
  rw [div_eq_mul_inv]; rw [mul_rpow_of_nonneg _ _ hz]; rw [inv_rpow]; rw [div_eq_mul_inv]

中文:
定理 div_rpow_of_nonneg
  条件: (x y : 实数>=0∞) {z : 实数} (hz : 0 <= z)
  结论: (x / y) ^ z = x ^ z / y ^ z
  证明: by
  rw [div_eq_mul_inv]; rw [mul_rpow_of_nonneg _ _ hz]; rw [inv_rpow]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, inv_rpow, mul_rpow_of_nonneg
-/
theorem div_rpow_of_nonneg (x y : Real>=0∞) {z : Real} (hz : 0 <= z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv]; rw [mul_rpow_of_nonneg _ _ hz]; rw [inv_rpow]; rw [div_eq_mul_inv]

/--
theorem `strictMono_rpow_of_pos` / 定理 `strictMono_rpow_of_pos`

English:
theorem strictMono_rpow_of_pos
  given: {z : Real} (h : 0 < z)
  statement: StrictMono fun x : Real>=0∞ => x ^ z
  proof: by
  intro x y hxy
  lift x to Real>=0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to Real>=0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_c

中文:
定理 strictMono_rpow_of_pos
  条件: {z : 实数} (h : 0 < z)
  结论: 严格递增 fun x : 实数>=0∞ => x ^ z
  证明: by
  intro x y hxy
  lift x to Real>=0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to Real>=0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_c

Depends on / 依赖: NNReal, NNReal.rpow_lt_rpow, coe_lt_coe, coe_lt_top, coe_rpow_of_nonneg, eq_or_ne, h.le, ne_top_of_lt, rpow_lt_rpow, top_rpow_of_pos
-/
theorem strictMono_rpow_of_pos {z : Real} (h : 0 < z) : StrictMono fun x : Real>=0∞ => x ^ z := by
  intro x y hxy
  lift x to Real>=0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to Real>=0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]

/--
theorem `monotone_rpow_of_nonneg` / 定理 `monotone_rpow_of_nonneg`

English:
theorem monotone_rpow_of_nonneg
  given: {z : Real} (h : 0 <= z)
  statement: Monotone fun x : Real>=0∞ => x ^ z
  proof: h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

中文:
定理 monotone_rpow_of_nonneg
  条件: {z : 实数} (h : 0 <= z)
  结论: 递增 fun x : 实数>=0∞ => x ^ z
  证明: h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

Depends on / 依赖: Category, Category.id_comp, F.map, F.mapComp_id_right_hom, PrelaxFunctor, PrelaxFunctor.map, Strict, Strict.rightUnitor_eqToIso, eqToHom_refl, eqToHom_trans, eqToIso, eqToIso.hom, eq_or_lt, h.eq_or_lt.elim, id_comp, mapComp, mapComp_id_right_hom, monotone, monotone_const, rightUnitor_eqToIso
-/
theorem monotone_rpow_of_nonneg {z : Real} (h : 0 <= z) : Monotone fun x : Real>=0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`. -/
@[simps! apply]
/--
Definition of `orderIsoRpow` / `orderIsoRpow` 的定义

English:
definition orderIsoRpow
  signature: (y : Real) (hy : 0 < y)
  body: (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

中文:
定义 orderIsoRpow
  签名: (y : 实数) (hy : 0 < y)
  定义体: (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

Depends on / 依赖: _comp_id, hy.ne.symm, mapComp, one_div_mul_cancel, orderIsoOfRightInverse, rpow_mul, rpow_one, strictMono_rpow_of_pos
-/
def orderIsoRpow (y : Real) (hy : 0 < y) : Real>=0∞ ≃o Real>=0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul]; rw [one_div_mul_cancel hy.ne.symm]; rw [rpow_one]

/--
theorem `orderIsoRpow_symm_apply` / 定理 `orderIsoRpow_symm_apply`

English:
theorem orderIsoRpow_symm_apply
  given: (y : Real) (hy : 0 < y)
  proof: by
  simp only [orderIsoRpow, one_div_one_div]
  rfl

中文:
定理 orderIsoRpow_symm_apply
  条件: (y : 实数) (hy : 0 < y)
  证明: by
  simp only [orderIsoRpow, one_div_one_div]
  rfl

Depends on / 依赖: _comp_id, mapComp, one_div_one_div, orderIsoRpow
-/
theorem orderIsoRpow_symm_apply (y : Real) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]
  rfl

/--
theorem `rpow_le_rpow` / 定理 `rpow_le_rpow`

English:
theorem rpow_le_rpow
  given: {x y : Real>=0∞} {z : Real} (h₁ : x <= y) (h₂ : 0 <= z)
  statement: x ^ z <= y ^ z
  proof: monotone_rpow_of_nonneg h₂ h₁

中文:
定理 rpow_le_rpow
  条件: {x y : 实数>=0∞} {z : 实数} (h₁ : x <= y) (h₂ : 0 <= z)
  结论: x ^ z <= y ^ z
  证明: monotone_rpow_of_nonneg h₂ h₁

Depends on / 依赖: Category, Category.id_comp, F.map, F.mapComp_id_left_hom, PrelaxFunctor, PrelaxFunctor.map, Strict, Strict.leftUnitor_eqToIso, eqToHom_refl, eqToHom_trans, eqToIso, eqToIso.hom, id_comp, leftUnitor_eqToIso, mapComp, mapComp_id_left_hom
-/
@[gcongr] theorem rpow_le_rpow {x y : Real>=0∞} {z : Real} (h₁ : x <= y) (h₂ : 0 <= z) : x ^ z <= y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁

/--
theorem `rpow_lt_rpow` / 定理 `rpow_lt_rpow`

English:
theorem rpow_lt_rpow
  given: {x y : Real>=0∞} {z : Real} (h₁ : x < y) (h₂ : 0 < z)
  statement: x ^ z < y ^ z
  proof: strictMono_rpow_of_pos h₂ h₁

中文:
定理 rpow_lt_rpow
  条件: {x y : 实数>=0∞} {z : 实数} (h₁ : x < y) (h₂ : 0 < z)
  结论: x ^ z < y ^ z
  证明: strictMono_rpow_of_pos h₂ h₁

Depends on / 依赖: _id_comp, mapComp
-/
@[gcongr] theorem rpow_lt_rpow {x y : Real>=0∞} {z : Real} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁

/--
theorem `rpow_le_rpow_iff` / 定理 `rpow_le_rpow_iff`

English:
theorem rpow_le_rpow_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x ^ z <= y ^ z ↔ x <= y
  proof: (strictMono_rpow_of_pos hz).le_iff_le

中文:
定理 rpow_le_rpow_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x ^ z <= y ^ z ↔ x <= y
  证明: (strictMono_rpow_of_pos hz).le_iff_le

Depends on / 依赖: _id_comp, le_iff_le, mapComp, strictMono_rpow_of_pos
-/
theorem rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y :=
  (strictMono_rpow_of_pos hz).le_iff_le

/--
theorem `rpow_lt_rpow_iff` / 定理 `rpow_lt_rpow_iff`

English:
theorem rpow_lt_rpow_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x ^ z < y ^ z ↔ x < y
  proof: (strictMono_rpow_of_pos hz).lt_iff_lt

中文:
定理 rpow_lt_rpow_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x ^ z < y ^ z ↔ x < y
  证明: (strictMono_rpow_of_pos hz).lt_iff_lt

Depends on / 依赖: Strict, Strict.associator_eqToIso, associator_eqToIso, lt_iff_lt, mapComp, mapComp_assoc_right_hom, strictMono_rpow_of_pos
-/
theorem rpow_lt_rpow_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt

/--
lemma `max_rpow` / 引理 `max_rpow`

English:
lemma max_rpow
  given: {x y : Real>=0∞} {p : Real} (hp : 0 <= p)
  statement: max x y ^ p = max (x ^ p) (y ^ p)
  proof: by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]

中文:
引理 max_rpow
  条件: {x y : 实数>=0∞} {p : 实数} (hp : 0 <= p)
  结论: 最大值 x y ^ p = 最大值 (x ^ p) (y ^ p)
  证明: by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]

Depends on / 依赖: F.mapComp, Iso.hom_inv_id_assoc, _hom_assoc, cancel_epi, hom_inv_id_assoc, le_total, mapComp, max_eq_left, max_eq_right, rpow_le_rpow
-/
lemma max_rpow {x y : Real>=0∞} {p : Real} (hp : 0 <= p) : max x y ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]

/--
theorem `le_rpow_inv_iff` / 定理 `le_rpow_inv_iff`

English:
theorem le_rpow_inv_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x <= y ^ z⁻¹ ↔ x ^ z <= y
  proof: by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul]; rw [@rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]

中文:
定理 le_rpow_inv_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x <= y ^ z⁻¹ ↔ x ^ z <= y
  证明: by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul]; rw [@rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]

Depends on / 依赖: hz.ne, nth_rw, rpow_le_rpow_iff, rpow_mul, rpow_one
-/
theorem le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul]; rw [@rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]

/--
theorem `rpow_inv_lt_iff` / 定理 `rpow_inv_lt_iff`

English:
theorem rpow_inv_lt_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x ^ z⁻¹ < y ↔ x < y ^ z
  proof: by
  simp only [← not_le, le_rpow_inv_iff hz]

中文:
定理 rpow_inv_lt_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x ^ z⁻¹ < y ↔ x < y ^ z
  证明: by
  simp only [← not_le, le_rpow_inv_iff hz]

Depends on / 依赖: F.mapComp, _hom_assoc, cat_disch, le_rpow_inv_iff, mapComp, not_le
-/
theorem rpow_inv_lt_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

/--
theorem `lt_rpow_inv_iff` / 定理 `lt_rpow_inv_iff`

English:
theorem lt_rpow_inv_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x < y ^ z⁻¹ ↔ x ^ z < y
  proof: by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul]; rw [@rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]

中文:
定理 lt_rpow_inv_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x < y ^ z⁻¹ ↔ x ^ z < y
  证明: by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul]; rw [@rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]

Depends on / 依赖: Iso.hom_inv_id_assoc, _inv_comp_mapComp, hom_inv_id_assoc, ne_of_lt, nth_rw, rpow_lt_rpow_iff, rpow_mul, rpow_one, whiskerLeft_mapComp
-/
theorem lt_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul]; rw [@rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]

/--
theorem `rpow_inv_le_iff` / 定理 `rpow_inv_le_iff`

English:
theorem rpow_inv_le_iff
  given: {x y : Real>=0∞} {z : Real} (hz : 0 < z)
  statement: x ^ z⁻¹ <= y ↔ x <= y ^ z
  proof: by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul]; rw [ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

@[gcongr]

中文:
定理 rpow_inv_le_iff
  条件: {x y : 实数>=0∞} {z : 实数} (hz : 0 < z)
  结论: x ^ z⁻¹ <= y ↔ x <= y ^ z
  证明: by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul]; rw [ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

@[gcongr]

Depends on / 依赖: ENNReal, ENNReal.rpow_le_rpow_iff, ENNReal.rpow_mul, ENNReal.rpow_one, _inv_comp_mapComp, hz.ne.symm, inv_pos, nth_rw, rpow_le_rpow_iff, rpow_mul, rpow_one, whiskerLeft_mapComp
-/
theorem rpow_inv_le_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul]; rw [ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

@[gcongr]
/--
theorem `rpow_lt_rpow_of_exponent_lt` / 定理 `rpow_lt_rpow_of_exponent_lt`

English:
theorem rpow_lt_rpow_of_exponent_lt
  given: {x : Real>=0∞} {y z : Real} (hx : 1 < x) (hx' : x != ⊤) (hyz : y < z)
  proof: by
  lift x to Real>=0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (lt_trans zero_lt_one hx).ne',
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]

中文:
定理 rpow_lt_rpow_of_exponent_lt
  条件: {x : 实数>=0∞} {y z : 实数} (hx : 1 < x) (hx' : x != ⊤) (hyz : y < z)
  证明: by
  lift x to Real>=0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (lt_trans zero_lt_one hx).ne',
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]

Depends on / 依赖: F.mapComp, Iso.inv_hom_id, NNReal, NNReal.rpow_lt_rpow_of_exponent_lt, cancel_epi, coe_rpow_of_ne_zero, inv_hom_id, lt_trans, mapComp, one_lt_coe_iff, rpow_lt_rpow_of_exponent_lt, zero_lt_one
-/
theorem rpow_lt_rpow_of_exponent_lt {x : Real>=0∞} {y z : Real} (hx : 1 < x) (hx' : x != ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to Real>=0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (lt_trans zero_lt_one hx).ne',
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]

/--
theorem `rpow_le_rpow_of_exponent_le` / 定理 `rpow_le_rpow_of_exponent_le`

English:
theorem rpow_le_rpow_of_exponent_le
  given: {x : Real>=0∞} {y z : Real} (hx : 1 <= x) (hyz : y <= z)
  proof: by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos] <;>
    linarith
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),

中文:
定理 rpow_le_rpow_of_exponent_le
  条件: {x : 实数>=0∞} {y z : 实数} (hx : 1 <= x) (hyz : y <= z)
  证明: by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos] <;>
    linarith
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),

Depends on / 依赖: _hom_whiskerRight_assoc, mapComp
-/
@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : Real>=0∞} {y z : Real} (hx : 1 <= x) (hyz : y <= z) :
    x ^ y <= x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos] <;>
    linarith
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]

/--
theorem `rpow_lt_rpow_of_exponent_gt` / 定理 `rpow_lt_rpow_of_exponent_gt`

English:
theorem rpow_lt_rpow_of_exponent_gt
  given: {x : Real>=0∞} {y z : Real} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]

中文:
定理 rpow_lt_rpow_of_exponent_gt
  条件: {x : 实数>=0∞} {y z : 实数} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]

Depends on / 依赖: F.mapComp, Iso.hom_inv_id, NNReal, NNReal.rpow_lt_rpow_of_exponent_gt, cancel_epi, coe_lt_one_iff, coe_pos, coe_rpow_of_ne_zero, hom_inv_id, le_top, lt_of_lt_of_le, mapComp, ne_of_gt, ne_of_lt, rpow_lt_rpow_of_exponent_gt
-/
theorem rpow_lt_rpow_of_exponent_gt {x : Real>=0∞} {y z : Real} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]

/--
theorem `rpow_le_rpow_of_exponent_ge` / 定理 `rpow_le_rpow_of_exponent_ge`

English:
theorem rpow_le_rpow_of_exponent_ge
  given: {x : Real>=0∞} {y z : Real} (hx1 : x <= 1) (hyz : z <= y)
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos] <;>
    linarith
  · rw [coe_le_one_iff] at hx

中文:
定理 rpow_le_rpow_of_exponent_ge
  条件: {x : 实数>=0∞} {y z : 实数} (hx1 : x <= 1) (hyz : z <= y)
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos] <;>
    linarith
  · rw [coe_le_one_iff] at hx

Depends on / 依赖: NNReal, NNReal.rpow_le_rpow_of_exponent_ge, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, coe_le_one_iff, coe_lt_top, coe_rpow_of_ne_zero, lt_of_le_of_lt, lt_trichotomy, mapComp, ne_of_lt, rpow_le_rpow_of_exponent_ge, zero_rpow_of_neg, zero_rpow_of_pos
-/
theorem rpow_le_rpow_of_exponent_ge {x : Real>=0∞} {y z : Real} (hx1 : x <= 1) (hyz : z <= y) :
    x ^ y <= x ^ z := by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [← coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]

/--
theorem `rpow_le_self_of_le_one` / 定理 `rpow_le_self_of_le_one`

English:
theorem rpow_le_self_of_le_one
  given: {x : Real>=0∞} {z : Real} (hx : x <= 1) (h_one_le : 1 <= z)
  statement: x ^ z <= x
  proof: by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le

中文:
定理 rpow_le_self_of_le_one
  条件: {x : 实数>=0∞} {z : 实数} (hx : x <= 1) (h_one_le : 1 <= z)
  结论: x ^ z <= x
  证明: by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le

Depends on / 依赖: ENNReal, ENNReal.rpow_le_rpow_of_exponent_ge, ENNReal.rpow_one, h_one_le, nth_rw, rpow_le_rpow_of_exponent_ge, rpow_one
-/
theorem rpow_le_self_of_le_one {x : Real>=0∞} {z : Real} (hx : x <= 1) (h_one_le : 1 <= z) : x ^ z <= x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le

/--
theorem `le_rpow_self_of_one_le` / 定理 `le_rpow_self_of_one_le`

English:
theorem le_rpow_self_of_one_le
  given: {x : Real>=0∞} {z : Real} (hx : 1 <= x) (h_one_le : 1 <= z)
  statement: x <= x ^ z
  proof: by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le

中文:
定理 le_rpow_self_of_one_le
  条件: {x : 实数>=0∞} {z : 实数} (hx : 1 <= x) (h_one_le : 1 <= z)
  结论: x <= x ^ z
  证明: by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le

Depends on / 依赖: ENNReal, ENNReal.rpow_le_rpow_of_exponent_le, ENNReal.rpow_one, h_one_le, nth_rw, rpow_le_rpow_of_exponent_le, rpow_one
-/
theorem le_rpow_self_of_one_le {x : Real>=0∞} {z : Real} (hx : 1 <= x) (h_one_le : 1 <= z) : x <= x ^ z := by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le

/--
theorem `rpow_pos_of_nonneg` / 定理 `rpow_pos_of_nonneg`

English:
theorem rpow_pos_of_nonneg
  given: {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hp_nonneg : 0 <= p)
  statement: 0 < x ^ p
  proof: by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos

中文:
定理 rpow_pos_of_nonneg
  条件: {p : 实数} {x : 实数>=0∞} (hx_pos : 0 < x) (hp_nonneg : 0 <= p)
  结论: 0 < x ^ p
  证明: by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos

Depends on / 依赖: hp_nonneg, hp_pos, hp_zero, hp_zero.symm, hx_pos, lt_of_le_of_ne, rpow_lt_rpow, zero_lt_one, zero_rpow_of_pos
-/
theorem rpow_pos_of_nonneg {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hp_nonneg : 0 <= p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos

/--
theorem `rpow_pos` / 定理 `rpow_pos`

English:
theorem rpow_pos
  given: {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hx_ne_top : x != ⊤)
  statement: 0 < x ^ p
  proof: by
  rcases lt_or_ge 0 p with hp_pos | hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

中文:
定理 rpow_pos
  条件: {p : 实数} {x : 实数>=0∞} (hx_pos : 0 < x) (hx_ne_top : x != ⊤)
  结论: 0 < x ^ p
  证明: by
  rcases lt_or_ge 0 p with hp_pos | hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

Depends on / 依赖: ENNReal, ENNReal.inv_pos, Right.nonneg_neg_iff.mpr, hp_nonpos, hp_pos, hx_ne_top, hx_pos, inv_pos, le_of_lt, lt_or_ge, neg_neg, nonneg_neg_iff, rpow_ne_top_of_nonneg, rpow_neg, rpow_pos_of_nonneg
-/
theorem rpow_pos {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hx_ne_top : x != ⊤) : 0 < x ^ p := by
  rcases lt_or_ge 0 p with hp_pos | hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

/--
theorem `rpow_lt_one` / 定理 `rpow_lt_one`

English:
theorem rpow_lt_one
  given: {x : Real>=0∞} {z : Real} (hx : x < 1) (hz : 0 < z)
  statement: x ^ z < 1
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]

中文:
定理 rpow_lt_one
  条件: {x : 实数>=0∞} {z : 实数} (hx : x < 1) (hz : 0 < z)
  结论: x ^ z < 1
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]

Depends on / 依赖: NNReal, NNReal.rpow_lt_one, coe_lt_one_iff, coe_rpow_of_nonneg, le_of_lt, le_top, lt_of_lt_of_le, ne_of_lt, rpow_lt_one
-/
theorem rpow_lt_one {x : Real>=0∞} {z : Real} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]

/--
theorem `rpow_le_one` / 定理 `rpow_le_one`

English:
theorem rpow_le_one
  given: {x : Real>=0∞} {z : Real} (hx : x <= 1) (hz : 0 <= z)
  statement: x ^ z <= 1
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]

中文:
定理 rpow_le_one
  条件: {x : 实数>=0∞} {z : 实数} (hx : x <= 1) (hz : 0 <= z)
  结论: x ^ z <= 1
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]

Depends on / 依赖: Iso.hom_inv_id_assoc, NNReal, NNReal.rpow_le_one, _comp_mapComp, coe_le_one_iff, coe_lt_top, coe_rpow_of_nonneg, hom_inv_id_assoc, lt_of_le_of_lt, ne_of_lt, rpow_le_one, whiskerLeft_mapComp
-/
theorem rpow_le_one {x : Real>=0∞} {z : Real} (hx : x <= 1) (hz : 0 <= z) : x ^ z <= 1 := by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]

/--
theorem `rpow_lt_one_of_one_lt_of_neg` / 定理 `rpow_lt_one_of_one_lt_of_neg`

English:
theorem rpow_lt_one_of_one_lt_of_neg
  given: {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : z < 0)
  statement: x ^ z < 1
  proof: by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]

中文:
定理 rpow_lt_one_of_one_lt_of_neg
  条件: {x : 实数>=0∞} {z : 实数} (hx : 1 < x) (hz : z < 0)
  结论: x ^ z < 1
  证明: by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]

Depends on / 依赖: F.map, NNReal, NNReal.rpow_lt_one_of_one_lt_of_neg, OplaxFunctor, OplaxFunctor.mapComp, PrelaxFunctor, PrelaxFunctor.map, Strict, Strict.associator_eqToIso, associator_eqToIso, coe_rpow_of_ne_zero, eqToIso, eqToIso.hom, lt_trans, mapComp, ne_of_gt, one_lt_coe_iff, rpow_lt_one_of_one_lt_of_neg, top_rpow_of_neg, zero_lt_one
-/
theorem rpow_lt_one_of_one_lt_of_neg {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]

/--
theorem `rpow_le_one_of_one_le_of_neg` / 定理 `rpow_le_one_of_one_le_of_neg`

English:
theorem rpow_le_one_of_one_le_of_neg
  given: {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz : z < 0)
  statement: x ^ z <= 1
  proof: by
  cases x
  · simp [top_rpow_of_neg hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

中文:
定理 rpow_le_one_of_one_le_of_neg
  条件: {x : 实数>=0∞} {z : 实数} (hx : 1 <= x) (hz : z < 0)
  结论: x ^ z <= 1
  证明: by
  cases x
  · simp [top_rpow_of_neg hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

Depends on / 依赖: F.mapComp, NNReal, NNReal.rpow_le_one_of_one_le_of_nonpos, _assoc, _comp_whiskerLeft_mapComp, cat_disch, coe_rpow_of_ne_zero, le_of_lt, lt_of_lt_of_le, mapComp, ne_of_gt, one_le_coe_iff, rpow_le_one_of_one_le_of_nonpos, top_rpow_of_neg, zero_lt_one
-/
theorem rpow_le_one_of_one_le_of_neg {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz : z < 0) : x ^ z <= 1 := by
  cases x
  · simp [top_rpow_of_neg hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

/--
theorem `one_lt_rpow` / 定理 `one_lt_rpow`

English:
theorem one_lt_rpow
  given: {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : 0 < z)
  statement: 1 < x ^ z
  proof: by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]

中文:
定理 one_lt_rpow
  条件: {x : 实数>=0∞} {z : 实数} (hx : 1 < x) (hz : 0 < z)
  结论: 1 < x ^ z
  证明: by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]

Depends on / 依赖: NNReal, NNReal.one_lt_rpow, coe_rpow_of_nonneg, le_of_lt, one_lt_coe_iff, one_lt_rpow, top_rpow_of_pos
-/
theorem one_lt_rpow {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]

/--
theorem `one_le_rpow` / 定理 `one_le_rpow`

English:
theorem one_le_rpow
  given: {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz : 0 < z)
  statement: 1 <= x ^ z
  proof: by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]

中文:
定理 one_le_rpow
  条件: {x : 实数>=0∞} {z : 实数} (hx : 1 <= x) (hz : 0 < z)
  结论: 1 <= x ^ z
  证明: by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]

Depends on / 依赖: NNReal, NNReal.one_le_rpow, coe_rpow_of_nonneg, le_of_lt, one_le_coe_iff, one_le_rpow, top_rpow_of_pos
-/
theorem one_le_rpow {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz : 0 < z) : 1 <= x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]

/--
theorem `one_lt_rpow_of_pos_of_lt_one_of_neg` / 定理 `one_lt_rpow_of_pos_of_lt_one_of_neg`

English:
theorem one_lt_rpow_of_pos_of_lt_one_of_neg
  statement: {x : Real>=0∞} {z : Real} (hx1 : 0 < x) (hx2 : x < 1)
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

中文:
定理 one_lt_rpow_of_pos_of_lt_one_of_neg
  结论: {x : 实数>=0∞} {z : 实数} (hx1 : 0 < x) (hx2 : x < 1)
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

Depends on / 依赖: NNReal, NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg, coe_lt_one_iff, coe_pos, coe_rpow_of_ne_zero, le_top, lt_of_lt_of_le, ne_of_gt, ne_of_lt, one_lt_rpow_of_pos_of_lt_one_of_neg
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : Real>=0∞} {z : Real} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to Real>=0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

/--
theorem `one_le_rpow_of_pos_of_le_one_of_neg` / 定理 `one_le_rpow_of_pos_of_le_one_of_neg`

English:
theorem one_le_rpow_of_pos_of_le_one_of_neg
  statement: {x : Real>=0∞} {z : Real} (hx1 : 0 < x) (hx2 : x <= 1)
  proof: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

中文:
定理 one_le_rpow_of_pos_of_le_one_of_neg
  结论: {x : 实数>=0∞} {z : 实数} (hx1 : 0 < x) (hx2 : x <= 1)
  证明: by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

Depends on / 依赖: NNReal, NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos, coe_le_one_iff, coe_lt_top, coe_pos, coe_rpow_of_ne_zero, le_of_lt, lt_of_le_of_lt, ne_of_gt, ne_of_lt, one_le_rpow_of_pos_of_le_one_of_nonpos
-/
theorem one_le_rpow_of_pos_of_le_one_of_neg {x : Real>=0∞} {z : Real} (hx1 : 0 < x) (hx2 : x <= 1)
    (hz : z < 0) : 1 <= x ^ z := by
  lift x to Real>=0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

/--
lemma `toNNReal_rpow` / 引理 `toNNReal_rpow`

English:
lemma toNNReal_rpow
  given: (x : Real>=0∞) (z : Real)
  statement: (x ^ z).toNNReal = x.toNNReal ^ z
  proof: by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt

中文:
引理 toNN实数_rpow
  条件: (x : 实数>=0∞) (z : 实数)
  结论: (x ^ z).toNN实数 = x.toNN实数 ^ z
  证明: by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt
-/
@[simp] lemma toNNReal_rpow (x : Real>=0∞) (z : Real) : (x ^ z).toNNReal = x.toNNReal ^ z := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt H)]

/--
theorem `toReal_rpow` / 定理 `toReal_rpow`

English:
theorem toReal_rpow
  given: (x : Real>=0∞) (z : Real)
  statement: x.toReal ^ z = (x ^ z).toReal
  proof: by
  rw [ENNReal.toReal]; rw [ENNReal.toReal]; rw [← NNReal.coe_rpow]; rw [ENNReal.toNNReal_rpow]

中文:
定理 to实数_rpow
  条件: (x : 实数>=0∞) (z : 实数)
  结论: x.to实数 ^ z = (x ^ z).to实数
  证明: by
  rw [ENNReal.toReal]; rw [ENNReal.toReal]; rw [← NNReal.coe_rpow]; rw [ENNReal.toNNReal_rpow]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_rpow, ENNReal.toReal, NNReal, NNReal.coe_rpow, coe_rpow, toNNReal_rpow, toReal
-/
theorem toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal]; rw [ENNReal.toReal]; rw [← NNReal.coe_rpow]; rw [ENNReal.toNNReal_rpow]

/--
theorem `ofReal_rpow_of_pos` / 定理 `ofReal_rpow_of_pos`

English:
theorem ofReal_rpow_of_pos
  given: {x p : Real} (hx_pos : 0 < x)
  proof: by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero]; rw [coe_inj]; rw [Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]

中文:
定理 of实数_rpow_of_pos
  条件: {x p : 实数} (hx_pos : 0 < x)
  证明: by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero]; rw [coe_inj]; rw [Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_rpow_of_nonneg, coe_inj, coe_rpow_of_ne_zero, hx_pos, hx_pos.le, ofReal, simp_rw, toNNReal_rpow_of_nonneg
-/
theorem ofReal_rpow_of_pos {x p : Real} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero]; rw [coe_inj]; rw [Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]

/--
theorem `ofReal_rpow_of_nonneg` / 定理 `ofReal_rpow_of_nonneg`

English:
theorem ofReal_rpow_of_nonneg
  given: {x p : Real} (hx_nonneg : 0 <= x) (hp_nonneg : 0 <= p)
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

中文:
定理 of实数_rpow_of_nonneg
  条件: {x p : 实数} (hx_nonneg : 0 <= x) (hp_nonneg : 0 <= p)
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

Depends on / 依赖: hp0.symm, hp_nonneg, hp_pos, hp_pos.ne.symm, hx0.symm, hx_nonneg, hx_nonneg.lt_of_ne, lt_of_le_of_ne, lt_of_ne, ofReal_rpow_of_pos
-/
theorem ofReal_rpow_of_nonneg {x p : Real} (hx_nonneg : 0 <= x) (hp_nonneg : 0 <= p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

/--
lemma `rpow_rpow_inv` / 引理 `rpow_rpow_inv`

English:
lemma rpow_rpow_inv
  given: {y : Real} (hy : y != 0) (x : Real>=0∞)
  statement: (x ^ y) ^ y⁻¹ = x
  proof: by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

中文:
引理 rpow_rpow_inv
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0∞)
  结论: (x ^ y) ^ y⁻¹ = x
  证明: by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]
-/
@[simp] lemma rpow_rpow_inv {y : Real} (hy : y != 0) (x : Real>=0∞) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

/--
lemma `rpow_inv_rpow` / 引理 `rpow_inv_rpow`

English:
lemma rpow_inv_rpow
  given: {y : Real} (hy : y != 0) (x : Real>=0∞)
  statement: (x ^ y⁻¹) ^ y = x
  proof: by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]

中文:
引理 rpow_inv_rpow
  条件: {y : 实数} (hy : y != 0) (x : 实数>=0∞)
  结论: (x ^ y⁻¹) ^ y = x
  证明: by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]
-/
@[simp] lemma rpow_inv_rpow {y : Real} (hy : y != 0) (x : Real>=0∞) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

@[simp]
/--
lemma `rpow_rpow_inv_eq_iff` / 引理 `rpow_rpow_inv_eq_iff`

English:
lemma rpow_rpow_inv_eq_iff
  given: {x : Real>=0∞} {y : Real}
  statement: (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1
  proof: by
  grind [rpow_zero, rpow_rpow_inv]

@[simp]

中文:
引理 rpow_rpow_inv_eq_iff
  条件: {x : 实数>=0∞} {y : 实数}
  结论: (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1
  证明: by
  grind [rpow_zero, rpow_rpow_inv]

@[simp]

Depends on / 依赖: rpow_rpow_inv, rpow_zero
-/
lemma rpow_rpow_inv_eq_iff {x : Real>=0∞} {y : Real} : (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1 := by
  grind [rpow_zero, rpow_rpow_inv]

@[simp]
/--
lemma `rpow_inv_rpow_eq_iff` / 引理 `rpow_inv_rpow_eq_iff`

English:
lemma rpow_inv_rpow_eq_iff
  given: {x : Real>=0∞} {y : Real}
  statement: (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1
  proof: by
  grind [rpow_rpow_inv_eq_iff]

中文:
引理 rpow_inv_rpow_eq_iff
  条件: {x : 实数>=0∞} {y : 实数}
  结论: (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1
  证明: by
  grind [rpow_rpow_inv_eq_iff]

Depends on / 依赖: rpow_rpow_inv_eq_iff
-/
lemma rpow_inv_rpow_eq_iff {x : Real>=0∞} {y : Real} : (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]

/--
lemma `pow_rpow_inv_natCast` / 引理 `pow_rpow_inv_natCast`

English:
lemma pow_rpow_inv_natCast
  given: {n : Nat} (hn : n != 0) (x : Real>=0∞)
  statement: (x ^ n) ^ (n⁻¹ : Real) = x
  proof: by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [mul_inv_cancel₀ (by positivity)]; rw [rpow_one]

中文:
引理 pow_rpow_inv_natCast
  条件: {n : 自然数} (hn : n != 0) (x : 实数>=0∞)
  结论: (x ^ n) ^ (n⁻¹ : 实数) = x
  证明: by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [mul_inv_cancel₀ (by positivity)]; rw [rpow_one]

Depends on / 依赖: rpow_mul, rpow_natCast, rpow_one
-/
lemma pow_rpow_inv_natCast {n : Nat} (hn : n != 0) (x : Real>=0∞) : (x ^ n) ^ (n⁻¹ : Real) = x := by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [mul_inv_cancel₀ (by positivity)]; rw [rpow_one]

/--
lemma `rpow_inv_natCast_pow` / 引理 `rpow_inv_natCast_pow`

English:
lemma rpow_inv_natCast_pow
  given: {n : Nat} (hn : n != 0) (x : Real>=0∞)
  statement: (x ^ (n⁻¹ : Real)) ^ n = x
  proof: by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [inv_mul_cancel₀ (by positivity)]; rw [rpow_one]

中文:
引理 rpow_inv_natCast_pow
  条件: {n : 自然数} (hn : n != 0) (x : 实数>=0∞)
  结论: (x ^ (n⁻¹ : 实数)) ^ n = x
  证明: by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [inv_mul_cancel₀ (by positivity)]; rw [rpow_one]

Depends on / 依赖: rpow_mul, rpow_natCast, rpow_one
-/
lemma rpow_inv_natCast_pow {n : Nat} (hn : n != 0) (x : Real>=0∞) : (x ^ (n⁻¹ : Real)) ^ n = x := by
  rw [← rpow_natCast]; rw [← rpow_mul]; rw [inv_mul_cancel₀ (by positivity)]; rw [rpow_one]

/--
lemma `rpow_natCast_mul` / 引理 `rpow_natCast_mul`

English:
lemma rpow_natCast_mul
  given: (x : Real>=0∞) (n : Nat) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul]; rw [rpow_natCast]

中文:
引理 rpow_natCast_mul
  条件: (x : 实数>=0∞) (n : 自然数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_natCast_mul (x : Real>=0∞) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul]; rw [rpow_natCast]

/--
lemma `rpow_mul_natCast` / 引理 `rpow_mul_natCast`

English:
lemma rpow_mul_natCast
  given: (x : Real>=0∞) (y : Real) (n : Nat)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul]; rw [rpow_natCast]

中文:
引理 rpow_mul_natCast
  条件: (x : 实数>=0∞) (y : 实数) (n : 自然数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_mul_natCast (x : Real>=0∞) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul]; rw [rpow_natCast]

/--
lemma `rpow_intCast_mul` / 引理 `rpow_intCast_mul`

English:
lemma rpow_intCast_mul
  given: (x : Real>=0∞) (n : Int) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul]; rw [rpow_intCast]

中文:
引理 rpow_intCast_mul
  条件: (x : 实数>=0∞) (n : 整数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_mul
-/
lemma rpow_intCast_mul (x : Real>=0∞) (n : Int) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul]; rw [rpow_intCast]

/--
lemma `rpow_mul_intCast` / 引理 `rpow_mul_intCast`

English:
lemma rpow_mul_intCast
  given: (x : Real>=0∞) (y : Real) (n : Int)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul]; rw [rpow_intCast]

中文:
引理 rpow_mul_intCast
  条件: (x : 实数>=0∞) (y : 实数) (n : 整数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_mul
-/
lemma rpow_mul_intCast (x : Real>=0∞) (y : Real) (n : Int) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul]; rw [rpow_intCast]

/--
lemma `rpow_left_injective` / 引理 `rpow_left_injective`

English:
lemma rpow_left_injective
  given: {x : Real} (hx : x != 0)
  statement: Injective fun y : Real>=0∞ => y ^ x
  proof: HasLeftInverse.injective ⟨fun y => y ^ x⁻¹, rpow_rpow_inv hx⟩

中文:
引理 rpow_left_injective
  条件: {x : 实数} (hx : x != 0)
  结论: 单射 fun y : 实数>=0∞ => y ^ x
  证明: HasLeftInverse.injective ⟨fun y => y ^ x⁻¹, rpow_rpow_inv hx⟩

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, injective, rpow_rpow_inv
-/
lemma rpow_left_injective {x : Real} (hx : x != 0) : Injective fun y : Real>=0∞ => y ^ x :=
  HasLeftInverse.injective ⟨fun y => y ^ x⁻¹, rpow_rpow_inv hx⟩

/--
theorem `rpow_left_surjective` / 定理 `rpow_left_surjective`

English:
theorem rpow_left_surjective
  given: {x : Real} (hx : x != 0)
  statement: Function.Surjective fun y : Real>=0∞ => y ^ x
  proof: HasRightInverse.surjective ⟨fun y => y ^ x⁻¹, rpow_inv_rpow hx⟩

中文:
定理 rpow_left_surjective
  条件: {x : 实数} (hx : x != 0)
  结论: 函数.满射 fun y : 实数>=0∞ => y ^ x
  证明: HasRightInverse.surjective ⟨fun y => y ^ x⁻¹, rpow_inv_rpow hx⟩

Depends on / 依赖: HasRightInverse, HasRightInverse.surjective, rpow_inv_rpow, surjective
-/
theorem rpow_left_surjective {x : Real} (hx : x != 0) : Function.Surjective fun y : Real>=0∞ => y ^ x :=
  HasRightInverse.surjective ⟨fun y => y ^ x⁻¹, rpow_inv_rpow hx⟩

/--
theorem `rpow_left_bijective` / 定理 `rpow_left_bijective`

English:
theorem rpow_left_bijective
  given: {x : Real} (hx : x != 0)
  statement: Function.Bijective fun y : Real>=0∞ => y ^ x
  proof: ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

中文:
定理 rpow_left_bijective
  条件: {x : 实数} (hx : x != 0)
  结论: 函数.双射 fun y : 实数>=0∞ => y ^ x
  证明: ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

Depends on / 依赖: rpow_left_injective, rpow_left_surjective
-/
theorem rpow_left_bijective {x : Real} (hx : x != 0) : Function.Bijective fun y : Real>=0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩

/--
lemma `_root_.Real.enorm_rpow_of_nonneg` / 引理 `_root_.Real.enorm_rpow_of_nonneg`

English:
lemma _root_.Real.enorm_rpow_of_nonneg
  given: {x y : Real} (hx : 0 <= x) (hy : 0 <= y)
  proof: by simp [enorm, nnnorm_rpow_of_nonneg hx, coe_rpow_of_nonneg _ hy]

中文:
引理 _root_.实数.enorm_rpow_of_nonneg
  条件: {x y : 实数} (hx : 0 <= x) (hy : 0 <= y)
  证明: by simp [enorm, nnnorm_rpow_of_nonneg hx, coe_rpow_of_nonneg _ hy]

Depends on / 依赖: coe_rpow_of_nonneg, nnnorm_rpow_of_nonneg
-/
lemma _root_.Real.enorm_rpow_of_nonneg {x y : Real} (hx : 0 <= x) (hy : 0 <= y) :
    ‖x ^ y‖ₑ = ‖x‖ₑ ^ y := by simp [enorm, nnnorm_rpow_of_nonneg hx, coe_rpow_of_nonneg _ hy]

/--
lemma `add_rpow_le_two_rpow_mul_rpow_add_rpow` / 引理 `add_rpow_le_two_rpow_mul_rpow_add_rpow`

English:
lemma add_rpow_le_two_rpow_mul_rpow_add_rpow
  given: {p : Real} (a b : Real>=0∞) (hp : 0 <= p)
  proof: calc
  (a + b) ^ p <= (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [max_rpow hp]
  _ <= 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp

中文:
引理 add_rpow_le_two_rpow_mul_rpow_add_rpow
  条件: {p : 实数} (a b : 实数>=0∞) (hp : 0 <= p)
  证明: calc
  (a + b) ^ p <= (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [max_rpow hp]
  _ <= 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp
-/
lemma add_rpow_le_two_rpow_mul_rpow_add_rpow {p : Real} (a b : Real>=0∞) (hp : 0 <= p) :
    (a + b) ^ p <= 2 ^ p * (a ^ p + b ^ p) := calc
  (a + b) ^ p <= (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [max_rpow hp]
  _ <= 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp

end ENNReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- section Tactics

-- /-!
-- ## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-- -/


-- namespace NormNum

-- theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
-- a ^ b = c := by rw [← h, hb, NNReal.rpow_natCast]

-- theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
-- (hc : c⁻¹ = c') : a ^ (-b) = c' := by
-- rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_natCast]

-- theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
-- a ^ b = c := by rw [← h, hb, ENNReal.rpow_natCast]

-- theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
-- (hc : c⁻¹ = c') : a ^ (-b) = c' := by
-- rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_natCast]

-- /-- Evaluate `NNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
-- prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))

-- /-- Evaluate `ENNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
-- prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))

-- /-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_nnrpow_ennrpow : expr → tactic (expr × expr)
-- | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
-- | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
-- | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
-- | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
-- | _ => tactic.failed

-- end NormNum

-- namespace Tactic

-- namespace Positivity

-- private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
-- NNReal.rpow_pos ha

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals.
-- -/
-- unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
-- let strictness_a ← core a
-- match strictness_a with
-- | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
-- | _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0`
-- private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
-- ENNReal.rpow_pos_of_nonneg ha hb.le

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of extended
-- nonnegative reals. -/
-- unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
-- let strictness_a ← core a
-- let strictness_b ← core b
-- match strictness_a, strictness_b with
-- | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
-- | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
-- | _, _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
-- end Positivity

-- open Positivity

-- /-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
-- the base is nonnegative and positive when the base is positive. -/
-- @[positivity]
-- unsafe def positivity_nnrpow_ennrpow : expr → tactic strictness
-- | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
-- | q(NNReal.rpow $(a) $(b)) => prove_nnrpow a b
-- | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
-- | q(ENNReal.rpow $(a) $(b)) => prove_ennrpow a b
-- | _ => failed

-- end Tactic

-- end Tactics

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `NNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : Real>=0) ^ (_ : Real)]
meta def evalNNRealRpow : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0), ~q($a ^ (0 : Real)) =>
    assertInstancesCommute
    pure (.positive q(NNReal.rpow_zero_pos $a))
  | 0, ~q(Real>=0), ~q($a ^ ($b : Real)) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa =>
      pure (.positive q(NNReal.rpow_pos $pa))
    | _ =>
      pure (.nonnegative q(zero_le (a := $e)))
  | _, _, _ => throwError "not NNReal.rpow"

private meta def isFiniteM? (x : Q(Real>=0∞)) : MetaM (Option Q($x != (⊤ : Real>=0∞))) := do
  let mvar ← mkFreshExprMVar q($x != (⊤ : Real>=0∞))
  let save ← saveState
let (goals, _) ← Elab.runTactic mvar.mvarId! ← `(tactic| finiteness)
  if goals.isEmpty then
pure some ← instantiateMVars mvar
  else
    restoreState save
    pure none

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `ENNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : Real>=0∞) ^ (_ : Real)]
meta def evalENNRealRpow : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0∞), ~q($a ^ (0 : Real)) =>
    assertInstancesCommute
    pure (.positive q(ENNReal.rpow_zero_pos $a))
  | 0, ~q(Real>=0∞), ~q($a ^ ($b : Real)) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
let rb ← catchNone core q(inferInstance) (some q(inferInstance)) b
    match ra, rb with
    | .positive pa, .positive pb =>
      pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa <| le_of_lt $pb))
    | .positive pa, .nonnegative pb =>
      pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa $pb))
    | .positive pa, _ =>
let some ha ← isFiniteM? a | pure .nonnegative q(zero_le (a := $e))
pure .positive q(ENNReal.rpow_pos $pa $ha)
    | _, _ =>
pure .nonnegative q(zero_le (a := $e))
  | _, _, _ => throwError "not ENNReal.rpow"

end Mathlib.Meta.Positivity

/-!
## NormNum extension for NNReal powers
-/

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/--
theorem `IsNat.nnreal_rpow_eq_nnreal_pow` / 定理 `IsNat.nnreal_rpow_eq_nnreal_pow`

English:
theorem IsNat.nnreal_rpow_eq_nnreal_pow
  given: {b : Real} {n : Nat} (h : IsNat b n) (a : Real>=0)
  proof: by
  rw [h.1]; rw [NNReal.rpow_natCast]

中文:
定理 是自然数.nnreal_rpow_eq_nnreal_pow
  条件: {b : 实数} {n : 自然数} (h : 是自然数 b n) (a : 实数>=0)
  证明: by
  rw [h.1]; rw [NNReal.rpow_natCast]

Depends on / 依赖: NNReal, NNReal.rpow_natCast, rpow_natCast
-/
theorem IsNat.nnreal_rpow_eq_nnreal_pow {b : Real} {n : Nat} (h : IsNat b n) (a : Real>=0) :
    a ^ b = a ^ n := by
  rw [h.1]; rw [NNReal.rpow_natCast]

/--
theorem `IsInt.nnreal_rpow_eq_inv_nnreal_pow` / 定理 `IsInt.nnreal_rpow_eq_inv_nnreal_pow`

English:
theorem IsInt.nnreal_rpow_eq_inv_nnreal_pow
  given: {b : Real} {n : Nat} (h : IsInt b (.negOfNat n)) (a : Real>=0)
  proof: by
  rw [h.1]; rw [NNReal.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

中文:
定理 是整数.nnreal_rpow_eq_inv_nnreal_pow
  条件: {b : 实数} {n : 自然数} (h : 是整数 b (.negOf自然数 n)) (a : 实数>=0)
  证明: by
  rw [h.1]; rw [NNReal.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

Depends on / 依赖: Int.negOfNat_eq, Int.ofNat_eq_natCast, NNReal, NNReal.rpow_intCast, negOfNat_eq, ofNat_eq_natCast, rpow_intCast, zpow_natCast, zpow_neg
-/
theorem IsInt.nnreal_rpow_eq_inv_nnreal_pow {b : Real} {n : Nat} (h : IsInt b (.negOfNat n)) (a : Real>=0) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1]; rw [NNReal.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

/--
theorem `IsNat.nnreal_rpow_isNNRat` / 定理 `IsNat.nnreal_rpow_isNNRat`

English:
theorem IsNat.nnreal_rpow_isNNRat
  statement: {a : Real>=0} {b : Real} {m n d r : Nat} (ha : IsNat a m)
  proof: by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [NNReal.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [NNReal.pow_rpow_inv_natCast]
  positivity

中文:
定理 是自然数.nnreal_rpow_isNNRat
  结论: {a : 实数>=0} {b : 实数} {m n d r : 自然数} (ha : 是自然数 a m)
  证明: by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [NNReal.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [NNReal.pow_rpow_inv_natCast]
  positivity

Depends on / 依赖: NNReal, NNReal.pow_rpow_inv_natCast, NNReal.rpow_natCast_mul, Nat.cast_pow, cast_pow, den_nz, div_eq_mul_inv, hb.den_nz, hb.to_eq, mod_cast, pow_rpow_inv_natCast, rpow_natCast_mul, to_eq
-/
theorem IsNat.nnreal_rpow_isNNRat {a : Real>=0} {b : Real} {m n d r : Nat} (ha : IsNat a m)
    (hb : IsNNRat b n d) (k : Nat) (hr : r ^ d = k) (l : Nat) (hm : m ^ n = l) (hkl : k = l) :
    IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [NNReal.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [NNReal.pow_rpow_inv_natCast]
  positivity

/--
theorem `IsNNRat.nnreal_rpow_isNNRat` / 定理 `IsNNRat.nnreal_rpow_isNNRat`

English:
theorem IsNNRat.nnreal_rpow_isNNRat
  statement: (a : Real>=0) (b : Real) (na da : Nat) (ha : IsNNRat a na da)
  proof: by
  suffices IsNNRat (nr / dr : Real>=0) nr dr by
    simpa [ha.to_eq, NNReal.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  simp [← hden.1, ha.den_nz]

中文:
定理 是NNRat.nnreal_rpow_isNNRat
  结论: (a : 实数>=0) (b : 实数) (na da : 自然数) (ha : 是NNRat a na da)
  证明: by
  suffices IsNNRat (nr / dr : Real>=0) nr dr by
    simpa [ha.to_eq, NNReal.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  simp [← hden.1, ha.den_nz]

Depends on / 依赖: IsNNRat, IsNNRat.of_raw, NNReal, NNReal.div_rpow, den_nz, div_rpow, ha.den_nz, ha.to_eq, of_raw, to_eq
-/
theorem IsNNRat.nnreal_rpow_isNNRat (a : Real>=0) (b : Real) (na da : Nat) (ha : IsNNRat a na da)
    (nr dr : Nat) (hnum : IsNat ((na : Real>=0) ^ b) nr) (hden : IsNat ((da : Real>=0) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : Real>=0) nr dr by
    simpa [ha.to_eq, NNReal.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  simp [← hden.1, ha.den_nz]

/--
theorem `nnreal_rpow_isRat_eq_inv_nnreal_rpow` / 定理 `nnreal_rpow_isRat_eq_inv_nnreal_rpow`

English:
theorem nnreal_rpow_isRat_eq_inv_nnreal_rpow
  statement: (a : Real>=0) (b : Real) (n d : Nat)
  proof: by
  rw [NNReal.inv_rpow]; rw [← NNReal.rpow_neg]; rw [hb.neg_to_eq rfl rfl]

中文:
定理 nnreal_rpow_isRat_eq_inv_nnreal_rpow
  结论: (a : 实数>=0) (b : 实数) (n d : 自然数)
  证明: by
  rw [NNReal.inv_rpow]; rw [← NNReal.rpow_neg]; rw [hb.neg_to_eq rfl rfl]

Depends on / 依赖: NNReal, NNReal.inv_rpow, NNReal.rpow_neg, hb.neg_to_eq, inv_rpow, neg_to_eq, rpow_neg
-/
theorem nnreal_rpow_isRat_eq_inv_nnreal_rpow (a : Real>=0) (b : Real) (n d : Nat)
    (hb : IsRat b (Int.negOfNat n) d) : a ^ b = (a⁻¹) ^ (n / d : Real) := by
  rw [NNReal.inv_rpow]; rw [← NNReal.rpow_neg]; rw [hb.neg_to_eq rfl rfl]

open Lean

/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatNNRealRPowIsNNRat
    (a : Q(Real>=0)) (na : Q(Nat)) (pa : Q(IsNat $a $na))
    (b : Q(Real)) (nb db : Q(Nat)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (Nat × Σ r : Q(Nat), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(Nat) := mkRawNatLit r
  -- avoid evaluating powers in kernel
let .some ⟨c, pc⟩ ← liftM OptionT.run evalNatPow er db | failure
let .some ⟨d, pd⟩ ← liftM OptionT.run evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.nnreal_rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a : ℝ≥0` and `b : ℝ`.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers.
-/
@[norm_num (_ : Real>=0) ^ (_ : Real)]
meta def evalNNRealRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(Real>=0), ~q(($a : Real>=0)^($b : Real)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.nnreal_rpow_eq_nnreal_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.nnreal_rpow_eq_inv_nnreal_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatNNRealRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.nnreal_rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : Real))
      assumeInstancesCommute
      return .eqTrans q(nnreal_rpow_isRat_eq_inv_nnreal_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum
