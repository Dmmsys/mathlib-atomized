/-
Copyright (c) 2026 Yael Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yael Dillies
-/
module

public import Mathlib.Data.Set.Card

import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite intervals of naturals

This file calculates the cardinality of intervals of natural numbers as sets.
-/

public section

namespace Set

/--
lemma `ncard_Icc_nat` / 引理 `ncard_Icc_nat`

English:
lemma ncard_Icc_nat
  given: (a b : Nat)
  statement: (Icc a b).ncard = b + 1 - a
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Icc a b

中文:
引理 ncard_Icc_nat
  条件: (a b : 自然数)
  结论: (闭区间 a b).ncard = b + 1 - a
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Icc a b
-/
@[simp] lemma ncard_Icc_nat (a b : Nat) : (Icc a b).ncard = b + 1 - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Icc a b

/--
lemma `ncard_Ico_nat` / 引理 `ncard_Ico_nat`

English:
lemma ncard_Ico_nat
  given: (a b : Nat)
  statement: (Ico a b).ncard = b - a
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ico a b

中文:
引理 ncard_Ico_nat
  条件: (a b : 自然数)
  结论: (左闭右开区间 a b).ncard = b - a
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ico a b
-/
@[simp] lemma ncard_Ico_nat (a b : Nat) : (Ico a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ico a b

/--
lemma `ncard_Ioc_nat` / 引理 `ncard_Ioc_nat`

English:
lemma ncard_Ioc_nat
  given: (a b : Nat)
  statement: (Ioc a b).ncard = b - a
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioc a b

中文:
引理 ncard_Ioc_nat
  条件: (a b : 自然数)
  结论: (左开右闭区间 a b).ncard = b - a
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioc a b
-/
@[simp] lemma ncard_Ioc_nat (a b : Nat) : (Ioc a b).ncard = b - a := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioc a b

/--
lemma `ncard_Ioo_nat` / 引理 `ncard_Ioo_nat`

English:
lemma ncard_Ioo_nat
  given: (a b : Nat)
  statement: (Ioo a b).ncard = b - a - 1
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioo a b

中文:
引理 ncard_Ioo_nat
  条件: (a b : 自然数)
  结论: (开区间 a b).ncard = b - a - 1
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioo a b
-/
@[simp] lemma ncard_Ioo_nat (a b : Nat) : (Ioo a b).ncard = b - a - 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Ioo a b

/--
lemma `ncard_uIcc_nat` / 引理 `ncard_uIcc_nat`

English:
lemma ncard_uIcc_nat
  given: (a b : Nat)
  statement: (uIcc a b).ncard = (b - a : Int).natAbs + 1
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_uIcc a b

中文:
引理 ncard_uIcc_nat
  条件: (a b : 自然数)
  结论: (uIcc a b).ncard = (b - a : 整数).natAbs + 1
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_uIcc a b
-/
@[simp] lemma ncard_uIcc_nat (a b : Nat) : (uIcc a b).ncard = (b - a : Int).natAbs + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_uIcc a b

/--
lemma `ncard_Iic_nat` / 引理 `ncard_Iic_nat`

English:
lemma ncard_Iic_nat
  given: (b : Nat)
  statement: (Iic b).ncard = b + 1
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iic b

中文:
引理 ncard_Iic_nat
  条件: (b : 自然数)
  结论: (左无界右闭区间 b).ncard = b + 1
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iic b
-/
@[simp] lemma ncard_Iic_nat (b : Nat) : (Iic b).ncard = b + 1 := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iic b

/--
lemma `ncard_Iio_nat` / 引理 `ncard_Iio_nat`

English:
lemma ncard_Iio_nat
  given: (b : Nat)
  statement: (Iio b).ncard = b
  proof: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iio b

中文:
引理 ncard_Iio_nat
  条件: (b : 自然数)
  结论: (左无界右开区间 b).ncard = b
  证明: by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iio b
-/
@[simp] lemma ncard_Iio_nat (b : Nat) : (Iio b).ncard = b := by
  simpa [← Set.ncard_coe_finset] using Nat.card_Iio b

end Set
