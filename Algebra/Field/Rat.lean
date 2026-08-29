/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.NNRat.Defs

/-!
# The rational numbers form a field

This file contains the field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

@[expose] public section

namespace Rat

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field Rat where
  body: commRing
  __ := commGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← NNRat.den_coe]; rw [← Int.cast_natCast q.num]; rw [← NNRat.num_coe]; exact (num_div_den _).symm
  ratCast_def _ := (num_div_den _).symm

中文:
实例 instField
  签名: : 域 有理数 where
  定义体: commRing
  __ := commGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← NNRat.den_coe]; rw [← Int.cast_natCast q.num]; rw [← NNRat.num_coe]; exact (num_div_den _).symm
  ratCast_def _ := (num_div_den _).symm

Depends on / 依赖: commRing
-/
instance instField : Field Rat where
  __ := commRing
  __ := commGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← NNRat.den_coe]; rw [← Int.cast_natCast q.num]; rw [← NNRat.num_coe]; exact (num_div_den _).symm
  ratCast_def _ := (num_div_den _).symm


/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: : DivisionRing Rat
  body: inferInstance

中文:
实例 instDivisionRing
  签名: : 除环 有理数
  定义体: inferInstance
-/
instance instDivisionRing : DivisionRing Rat := inferInstance

/--
lemma `inv_nonneg` / 引理 `inv_nonneg`

English:
lemma inv_nonneg
  given: {a : Rat} (ha : 0 <= a)
  statement: 0 <= a⁻¹
  proof: by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)

中文:
引理 inv_nonneg
  条件: {a : 有理数} (ha : 0 <= a)
  结论: 0 <= a⁻¹
  证明: by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)
-/
protected lemma inv_nonneg {a : Rat} (ha : 0 <= a) : 0 <= a⁻¹ := by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)

/--
lemma `div_nonneg` / 引理 `div_nonneg`

English:
lemma div_nonneg
  given: {a b : Rat} (ha : 0 <= a) (hb : 0 <= b)
  statement: 0 <= a / b
  proof: mul_nonneg ha (Rat.inv_nonneg hb)

中文:
引理 div_nonneg
  条件: {a b : 有理数} (ha : 0 <= a) (hb : 0 <= b)
  结论: 0 <= a / b
  证明: mul_nonneg ha (Rat.inv_nonneg hb)
-/
protected lemma div_nonneg {a b : Rat} (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b :=
  mul_nonneg ha (Rat.inv_nonneg hb)

end Rat

namespace NNRat

/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv Rat>=0 where
  body: ⟨x⁻¹, Rat.inv_nonneg x.2⟩

中文:
实例 instInv
  签名: : 取逆 有理数>=0 where
  定义体: ⟨x⁻¹, Rat.inv_nonneg x.2⟩

Depends on / 依赖: Rat.inv_nonneg, inv_nonneg
-/
instance instInv : Inv Rat>=0 where
  inv x := ⟨x⁻¹, Rat.inv_nonneg x.2⟩

/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: : Div Rat>=0 where
  body: ⟨x / y, Rat.div_nonneg x.2 y.2⟩

中文:
实例 instDiv
  签名: : 除法 有理数>=0 where
  定义体: ⟨x / y, Rat.div_nonneg x.2 y.2⟩

Depends on / 依赖: Rat.div_nonneg, div_nonneg
-/
instance instDiv : Div Rat>=0 where
  div x y := ⟨x / y, Rat.div_nonneg x.2 y.2⟩

/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: : Pow Rat>=0 Int where
  body: ⟨x ^ n, Rat.zpow_nonneg x.2⟩

中文:
实例 instZPow
  签名: : 幂 有理数>=0 整数 where
  定义体: ⟨x ^ n, Rat.zpow_nonneg x.2⟩

Depends on / 依赖: Rat.zpow_nonneg, zpow_nonneg
-/
instance instZPow : Pow Rat>=0 Int where
  pow x n := ⟨x ^ n, Rat.zpow_nonneg x.2⟩

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (q : Rat>=0)
  statement: ((q⁻¹ : Rat>=0) : Rat) = (q : Rat)⁻¹
  proof: rfl

中文:
引理 coe_inv
  条件: (q : 有理数>=0)
  结论: ((q⁻¹ : 有理数>=0) : 有理数) = (q : 有理数)⁻¹
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inv (q : Rat>=0) : ((q⁻¹ : Rat>=0) : Rat) = (q : Rat)⁻¹ := rfl
/--
lemma `coe_div` / 引理 `coe_div`

English:
lemma coe_div
  given: (p q : Rat>=0)
  statement: ((p / q : Rat>=0) : Rat) = p / q
  proof: rfl

中文:
引理 coe_div
  条件: (p q : 有理数>=0)
  结论: ((p / q : 有理数>=0) : 有理数) = p / q
  证明: rfl
-/
@[simp, norm_cast] lemma coe_div (p q : Rat>=0) : ((p / q : Rat>=0) : Rat) = p / q := rfl
/--
lemma `coe_zpow` / 引理 `coe_zpow`

English:
lemma coe_zpow
  given: (p : Rat>=0) (n : Int)
  statement: ((p ^ n : Rat>=0) : Rat) = p ^ n
  proof: rfl

中文:
引理 coe_zpow
  条件: (p : 有理数>=0) (n : 整数)
  结论: ((p ^ n : 有理数>=0) : 有理数) = p ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zpow (p : Rat>=0) (n : Int) : ((p ^ n : Rat>=0) : Rat) = p ^ n := rfl

/--
lemma `inv_def` / 引理 `inv_def`

English:
lemma inv_def
  given: (q : Rat>=0)
  statement: q⁻¹ = divNat q.den q.num
  proof: by ext; simp [Rat.inv_def, num_coe, den_coe]

中文:
引理 inv_def
  条件: (q : 有理数>=0)
  结论: q⁻¹ = div自然数 q.den q.num
  证明: by ext; simp [Rat.inv_def, num_coe, den_coe]

Depends on / 依赖: Rat.inv_def, den_coe, inv_def, num_coe
-/
lemma inv_def (q : Rat>=0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def, num_coe, den_coe]
/--
lemma `div_def` / 引理 `div_def`

English:
lemma div_def
  given: (p q : Rat>=0)
  statement: p / q = divNat (p.num * q.den) (p.den * q.num)
  proof: by
  ext; simp [Rat.div_def', num_coe, den_coe]

中文:
引理 div_def
  条件: (p q : 有理数>=0)
  结论: p / q = div自然数 (p.num * q.den) (p.den * q.num)
  证明: by
  ext; simp [Rat.div_def', num_coe, den_coe]

Depends on / 依赖: Rat.div_def, den_coe, div_def, num_coe
-/
lemma div_def (p q : Rat>=0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]

/--
theorem `divNat_eq_div` / 定理 `divNat_eq_div`

English:
theorem divNat_eq_div
  given: (a b : Nat)
  statement: divNat a b = a / b
  proof: by
  ext
  simp [Rat.mkRat_eq_div]

中文:
定理 div自然数_eq_div
  条件: (a b : 自然数)
  结论: div自然数 a b = a / b
  证明: by
  ext
  simp [Rat.mkRat_eq_div]

Depends on / 依赖: Rat.mkRat_eq_div, mkRat_eq_div
-/
theorem divNat_eq_div (a b : Nat) : divNat a b = a / b := by
  ext
  simp [Rat.mkRat_eq_div]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `num_inv_of_ne_zero` / 引理 `num_inv_of_ne_zero`

English:
lemma num_inv_of_ne_zero
  given: {q : Rat>=0} (hq : q != 0)
  statement: q⁻¹.num = q.den
  proof: by
  rw [inv_def]; rw [divNat]; rw [num]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]; rw [Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

中文:
引理 num_inv_of_ne_zero
  条件: {q : 有理数>=0} (hq : q != 0)
  结论: q⁻¹.num = q.den
  证明: by
  rw [inv_def]; rw [divNat]; rw [num]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]; rw [Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

Depends on / 依赖: Int.natAbs_natCast, Rat.divInt_ofNat, Rat.mk_eq_mkRat, coe_mk, coprime_num_den, divInt_ofNat, divNat, inv_def, mk_eq_mkRat, natAbs_natCast, num_ne_zero, num_ne_zero.mpr, q.coprime_num_den.symm
-/
lemma num_inv_of_ne_zero {q : Rat>=0} (hq : q != 0) : q⁻¹.num = q.den := by
  rw [inv_def]; rw [divNat]; rw [num]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]; rw [Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `den_inv_of_ne_zero` / 引理 `den_inv_of_ne_zero`

English:
lemma den_inv_of_ne_zero
  given: {q : Rat>=0} (hq : q != 0)
  statement: q⁻¹.den = q.num
  proof: by
  rw [inv_def]; rw [divNat]; rw [den]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

@[simp]

中文:
引理 den_inv_of_ne_zero
  条件: {q : 有理数>=0} (hq : q != 0)
  结论: q⁻¹.den = q.num
  证明: by
  rw [inv_def]; rw [divNat]; rw [den]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

@[simp]

Depends on / 依赖: Rat.divInt_ofNat, Rat.mk_eq_mkRat, coe_mk, coprime_num_den, divInt_ofNat, divNat, inv_def, mk_eq_mkRat, num_ne_zero, num_ne_zero.mpr, q.coprime_num_den.symm
-/
lemma den_inv_of_ne_zero {q : Rat>=0} (hq : q != 0) : q⁻¹.den = q.num := by
  rw [inv_def]; rw [divNat]; rw [den]; rw [coe_mk]; rw [Rat.divInt_ofNat]; rw [← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

@[simp]
/--
lemma `num_div_den` / 引理 `num_div_den`

English:
lemma num_div_den
  given: (q : Rat>=0)
  statement: (q.num : Rat>=0) / q.den = q
  proof: by
  ext1
  rw [coe_div]; rw [coe_natCast]; rw [coe_natCast]; rw [num]; rw [← Int.cast_natCast]
  exact (cast_def _).symm

中文:
引理 num_div_den
  条件: (q : 有理数>=0)
  结论: (q.num : 有理数>=0) / q.den = q
  证明: by
  ext1
  rw [coe_div]; rw [coe_natCast]; rw [coe_natCast]; rw [num]; rw [← Int.cast_natCast]
  exact (cast_def _).symm

Depends on / 依赖: Int.cast_natCast, cast_def, cast_natCast, coe_div, coe_natCast
-/
lemma num_div_den (q : Rat>=0) : (q.num : Rat>=0) / q.den = q := by
  ext1
  rw [coe_div]; rw [coe_natCast]; rw [coe_natCast]; rw [num]; rw [← Int.cast_natCast]
  exact (cast_def _).symm

/--
Instance `instSemifield` / 实例 `instSemifield`

English:
instance instSemifield
  signature: : Semifield Rat>=0 where
  body: by ext; simp
  mul_inv_cancel q h := by ext; simp [h]
  nnratCast_def q := q.num_div_den.symm
  nnqsmul q a := q * a
  nnqsmul_def q a := rfl
  zpow n a := a ^ n
  zpow_zero' a := by ext; apply Field.zpow_zero'
  zpow_succ' n a := by ext; apply Field.zpow_succ'
  zpow_neg' n a := by ext; apply Field.zpow_neg'

中文:
实例 instSemifield
  签名: : 半域 有理数>=0 where
  定义体: by ext; simp
  mul_inv_cancel q h := by ext; simp [h]
  nnratCast_def q := q.num_div_den.symm
  nnqsmul q a := q * a
  nnqsmul_def q a := rfl
  zpow n a := a ^ n
  zpow_zero' a := by ext; apply Field.zpow_zero'
  zpow_succ' n a := by ext; apply Field.zpow_succ'
  zpow_neg' n a := by ext; apply Field.zpow_neg'

Depends on / 依赖: Field.zpow_neg, Field.zpow_succ, Field.zpow_zero, mul_inv_cancel, nnqsmul, nnqsmul_def, nnratCast_def, num_div_den, q.num_div_den.symm, zpow_neg, zpow_succ, zpow_zero
-/
instance instSemifield : Semifield Rat>=0 where
  inv_zero := by ext; simp
  mul_inv_cancel q h := by ext; simp [h]
  nnratCast_def q := q.num_div_den.symm
  nnqsmul q a := q * a
  nnqsmul_def q a := rfl
  zpow n a := a ^ n
  zpow_zero' a := by ext; apply Field.zpow_zero'
  zpow_succ' n a := by ext; apply Field.zpow_succ'
  zpow_neg' n a := by ext; apply Field.zpow_neg'

end NNRat

/--
theorem `NNRatCast.ofScientific_eq_ite` / 定理 `NNRatCast.ofScientific_eq_ite`

English:
theorem NNRatCast.ofScientific_eq_ite
  given: {K} [NNRatCast K] (m : Nat) (b : Bool) (d : Nat)
  proof: by
  rw [NNRatCast.toOfScientific_def]
  split_ifs
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_pos ‹_›]
    congr
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_neg ‹_›]
    congr

中文:
定理 非负有理数嵌入.ofScientific_eq_ite
  条件: {K} [非负有理数嵌入 K] (m : 自然数) (b : 布尔值) (d : 自然数)
  证明: by
  rw [NNRatCast.toOfScientific_def]
  split_ifs
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_pos ‹_›]
    congr
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_neg ‹_›]
    congr

Depends on / 依赖: NNRatCast, NNRatCast.toOfScientific_def, Rat.ofScientific_def, Rat.ofScientific_eq_ofScientific, if_neg, if_pos, ofScientific_def, ofScientific_eq_ofScientific, split_ifs, toOfScientific_def
-/
theorem NNRatCast.ofScientific_eq_ite {K} [NNRatCast K] (m : Nat) (b : Bool) (d : Nat) :
    (OfScientific.ofScientific m b d : K) =
      if b = true then NNRat.divNat m (10 ^ d) else ↑(m * 10 ^ d) := by
  rw [NNRatCast.toOfScientific_def]
  split_ifs
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_pos ‹_›]
    congr
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific]; rw [Rat.ofScientific_def]; rw [if_neg ‹_›]
    congr
