/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

@[expose] public section

open Real Topology Filter ComplexConjugate Finset Set

namespace Complex

/--
Definition of `cpow` / `cpow` 的定义

English:
definition cpow
  signature: (x y : Complex)
  body: if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)

中文:
定义 cpow
  签名: (x y : Complex)
  定义体: if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
-/
noncomputable def cpow (x y : Complex) : Complex :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow Complex Complex
  body: ⟨cpow⟩

@[simp]

中文:
实例 :
  签名: Pow Complex Complex
  定义体: ⟨cpow⟩

@[simp]
-/
noncomputable instance : Pow Complex Complex :=
  ⟨cpow⟩

@[simp]
/--
theorem `cpow_eq_pow` / 定理 `cpow_eq_pow`

English:
theorem cpow_eq_pow
  given: (x y : Complex)
  statement: cpow x y = x ^ y
  proof: rfl

中文:
定理 cpow_eq_pow
  条件: (x y : Complex)
  结论: cpow x y = x ^ y
  证明: rfl
-/
theorem cpow_eq_pow (x y : Complex) : cpow x y = x ^ y :=
  rfl

/--
theorem `cpow_def` / 定理 `cpow_def`

English:
theorem cpow_def
  given: (x y : Complex)
  statement: x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
  proof: rfl

中文:
定理 cpow_def
  条件: (x y : Complex)
  结论: x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
  证明: rfl
-/
theorem cpow_def (x y : Complex) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl

/--
theorem `cpow_def_of_ne_zero` / 定理 `cpow_def_of_ne_zero`

English:
theorem cpow_def_of_ne_zero
  given: {x : Complex} (hx : x != 0) (y : Complex)
  statement: x ^ y = exp (log x * y)
  proof: if_neg hx

@[simp]

中文:
定理 cpow_def_of_ne_zero
  条件: {x : Complex} (hx : x != 0) (y : Complex)
  结论: x ^ y = exp (log x * y)
  证明: if_neg hx

@[simp]

Depends on / 依赖: if_neg
-/
theorem cpow_def_of_ne_zero {x : Complex} (hx : x != 0) (y : Complex) : x ^ y = exp (log x * y) :=
  if_neg hx

@[simp]
/--
theorem `cpow_zero` / 定理 `cpow_zero`

English:
theorem cpow_zero
  given: (x : Complex)
  statement: x ^ (0 : Complex) = 1
  proof: by simp [cpow_def]

@[simp]

中文:
定理 cpow_zero
  条件: (x : Complex)
  结论: x ^ (0 : Complex) = 1
  证明: by simp [cpow_def]

@[simp]

Depends on / 依赖: cpow_def
-/
theorem cpow_zero (x : Complex) : x ^ (0 : Complex) = 1 := by simp [cpow_def]

@[simp]
/--
theorem `cpow_eq_zero_iff` / 定理 `cpow_eq_zero_iff`

English:
theorem cpow_eq_zero_iff
  given: (x y : Complex)
  statement: x ^ y = 0 ↔ x = 0 ∧ y != 0
  proof: by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]

中文:
定理 cpow_eq_zero_iff
  条件: (x y : Complex)
  结论: x ^ y = 0 ↔ x = 0 ∧ y != 0
  证明: by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]

Depends on / 依赖: cpow_def, exp_ne_zero, split_ifs
-/
theorem cpow_eq_zero_iff (x y : Complex) : x ^ y = 0 ↔ x = 0 ∧ y != 0 := by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]

/--
theorem `cpow_ne_zero_iff` / 定理 `cpow_ne_zero_iff`

English:
theorem cpow_ne_zero_iff
  given: {x y : Complex}
  proof: by
  rw [ne_eq]; rw [cpow_eq_zero_iff]; rw [not_and_or]; rw [ne_eq]; rw [not_not]

中文:
定理 cpow_ne_zero_iff
  条件: {x y : Complex}
  证明: by
  rw [ne_eq]; rw [cpow_eq_zero_iff]; rw [not_and_or]; rw [ne_eq]; rw [not_not]

Depends on / 依赖: cpow_eq_zero_iff, ne_eq, not_and_or, not_not
-/
theorem cpow_ne_zero_iff {x y : Complex} :
    x ^ y != 0 ↔ x != 0 ∨ y = 0 := by
  rw [ne_eq]; rw [cpow_eq_zero_iff]; rw [not_and_or]; rw [ne_eq]; rw [not_not]

/--
theorem `cpow_ne_zero_iff_of_exponent_ne_zero` / 定理 `cpow_ne_zero_iff_of_exponent_ne_zero`

English:
theorem cpow_ne_zero_iff_of_exponent_ne_zero
  given: {x y : Complex} (hy : y != 0)
  proof: by simp [hy]

@[simp]

中文:
定理 cpow_ne_zero_iff_of_exponent_ne_zero
  条件: {x y : Complex} (hy : y != 0)
  证明: by simp [hy]

@[simp]
-/
theorem cpow_ne_zero_iff_of_exponent_ne_zero {x y : Complex} (hy : y != 0) :
    x ^ y != 0 ↔ x != 0 := by simp [hy]

@[simp]
/--
theorem `zero_cpow` / 定理 `zero_cpow`

English:
theorem zero_cpow
  given: {x : Complex} (h : x != 0)
  statement: (0 : Complex) ^ x = 0
  proof: by simp [cpow_def, *]

中文:
定理 zero_cpow
  条件: {x : Complex} (h : x != 0)
  结论: (0 : Complex) ^ x = 0
  证明: by simp [cpow_def, *]

Depends on / 依赖: cpow_def
-/
theorem zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) ^ x = 0 := by simp [cpow_def, *]

/--
theorem `zero_cpow_eq_iff` / 定理 `zero_cpow_eq_iff`

English:
theorem zero_cpow_eq_iff
  given: {x : Complex} {a : Complex}
  statement: (0 : Complex) ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  proof: by
  constructor
  · intro hyp
    simp only [cpow_def, if_true] at hyp
    grind
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _

中文:
定理 zero_cpow_eq_iff
  条件: {x : Complex} {a : Complex}
  结论: (0 : Complex) ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  证明: by
  constructor
  · intro hyp
    simp only [cpow_def, if_true] at hyp
    grind
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _

Depends on / 依赖: cpow_def, cpow_zero, if_true, zero_cpow
-/
theorem zero_cpow_eq_iff {x : Complex} {a : Complex} : (0 : Complex) ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [cpow_def, if_true] at hyp
    grind
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _

/--
theorem `eq_zero_cpow_iff` / 定理 `eq_zero_cpow_iff`

English:
theorem eq_zero_cpow_iff
  given: {x : Complex} {a : Complex}
  statement: a = (0 : Complex) ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  proof: by
  rw [← zero_cpow_eq_iff]; rw [eq_comm]

@[simp]

中文:
定理 eq_zero_cpow_iff
  条件: {x : Complex} {a : Complex}
  结论: a = (0 : Complex) ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  证明: by
  rw [← zero_cpow_eq_iff]; rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, zero_cpow_eq_iff
-/
theorem eq_zero_cpow_iff {x : Complex} {a : Complex} : a = (0 : Complex) ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff]; rw [eq_comm]

@[simp]
/--
theorem `cpow_one` / 定理 `cpow_one`

English:
theorem cpow_one
  given: (x : Complex)
  statement: x ^ (1 : Complex) = x
  proof: if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : Complex) != 0), if_neg hx, mul_one, exp_log hx]

@[simp]

中文:
定理 cpow_one
  条件: (x : Complex)
  结论: x ^ (1 : Complex) = x
  证明: if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : Complex) != 0), if_neg hx, mul_one, exp_log hx]

@[simp]

Depends on / 依赖: cpow_def, exp_log, if_neg, mul_one, one_ne_zero
-/
theorem cpow_one (x : Complex) : x ^ (1 : Complex) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : Complex) != 0), if_neg hx, mul_one, exp_log hx]

@[simp]
/--
theorem `one_cpow` / 定理 `one_cpow`

English:
theorem one_cpow
  given: (x : Complex)
  statement: (1 : Complex) ^ x = 1
  proof: by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]

中文:
定理 one_cpow
  条件: (x : Complex)
  结论: (1 : Complex) ^ x = 1
  证明: by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]

Depends on / 依赖: cpow_def, one_ne_zero, split_ifs
-/
theorem one_cpow (x : Complex) : (1 : Complex) ^ x = 1 := by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]

/--
theorem `cpow_add` / 定理 `cpow_add`

English:
theorem cpow_add
  given: {x : Complex} (y z : Complex) (hx : x != 0)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: by
  simp only [cpow_def, ite_mul, mul_ite]
  simp_all [exp_add, mul_add]

中文:
定理 cpow_add
  条件: {x : Complex} (y z : Complex) (hx : x != 0)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: by
  simp only [cpow_def, ite_mul, mul_ite]
  simp_all [exp_add, mul_add]

Depends on / 依赖: cpow_def, exp_add, ite_mul, mul_add, mul_ite
-/
theorem cpow_add {x : Complex} (y z : Complex) (hx : x != 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, mul_ite]
  simp_all [exp_add, mul_add]

/--
theorem `cpow_mul` / 定理 `cpow_mul`

English:
theorem cpow_mul
  given: {x y : Complex} (z : Complex) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im <= π)
  proof: by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]

中文:
定理 cpow_mul
  条件: {x y : Complex} (z : Complex) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im <= π)
  证明: by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]

Depends on / 依赖: cpow_def, exp_ne_zero, log_exp, mul_assoc, split_ifs
-/
theorem cpow_mul {x y : Complex} (z : Complex) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im <= π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]

/--
theorem `cpow_neg` / 定理 `cpow_neg`

English:
theorem cpow_neg
  given: (x y : Complex)
  statement: x ^ (-y) = (x ^ y)⁻¹
  proof: by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  split_ifs <;> simp [exp_neg]

中文:
定理 cpow_neg
  条件: (x y : Complex)
  结论: x ^ (-y) = (x ^ y)⁻¹
  证明: by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  split_ifs <;> simp [exp_neg]

Depends on / 依赖: cpow_def, exp_neg, mul_neg, neg_eq_zero, split_ifs
-/
theorem cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  split_ifs <;> simp [exp_neg]

/--
theorem `cpow_sub` / 定理 `cpow_sub`

English:
theorem cpow_sub
  given: {x : Complex} (y z : Complex) (hx : x != 0)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: by
  rw [sub_eq_add_neg]; rw [cpow_add _ _ hx]; rw [cpow_neg]; rw [div_eq_mul_inv]

中文:
定理 cpow_sub
  条件: {x : Complex} (y z : Complex) (hx : x != 0)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: by
  rw [sub_eq_add_neg]; rw [cpow_add _ _ hx]; rw [cpow_neg]; rw [div_eq_mul_inv]

Depends on / 依赖: cpow_add, cpow_neg, div_eq_mul_inv, sub_eq_add_neg
-/
theorem cpow_sub {x : Complex} (y z : Complex) (hx : x != 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg]; rw [cpow_add _ _ hx]; rw [cpow_neg]; rw [div_eq_mul_inv]

/--
theorem `cpow_neg_one` / 定理 `cpow_neg_one`

English:
theorem cpow_neg_one
  given: (x : Complex)
  statement: x ^ (-1 : Complex) = x⁻¹
  proof: by simpa using cpow_neg x 1

中文:
定理 cpow_neg_one
  条件: (x : Complex)
  结论: x ^ (-1 : Complex) = x⁻¹
  证明: by simpa using cpow_neg x 1

Depends on / 依赖: cpow_neg
-/
theorem cpow_neg_one (x : Complex) : x ^ (-1 : Complex) = x⁻¹ := by simpa using cpow_neg x 1

/--
lemma `cpow_int_mul` / 引理 `cpow_int_mul`

English:
lemma cpow_int_mul
  given: (x : Complex) (n : Int) (y : Complex)
  statement: x ^ (n * y) = (x ^ y) ^ n
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy <;> simp [*, zero_zpow]
  · rw [cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hx, mul_left_comm, exp_int_mul]

中文:
引理 cpow_int_mul
  条件: (x : Complex) (n : 整数) (y : Complex)
  结论: x ^ (n * y) = (x ^ y) ^ n
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy <;> simp [*, zero_zpow]
  · rw [cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hx, mul_left_comm, exp_int_mul]

Depends on / 依赖: F.map, F.mapId, F.obj, cat_disch, cpow_def_of_ne_zero, eqToIso, eq_or_ne, exp_int_mul, mul_left_comm, zero_zpow
-/
lemma cpow_int_mul (x : Complex) (n : Int) (y : Complex) : x ^ (n * y) = (x ^ y) ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy <;> simp [*, zero_zpow]
  · rw [cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hx, mul_left_comm, exp_int_mul]

/--
lemma `cpow_mul_int` / 引理 `cpow_mul_int`

English:
lemma cpow_mul_int
  given: (x y : Complex) (n : Int)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by rw [mul_comm, cpow_int_mul]

中文:
引理 cpow_mul_int
  条件: (x y : Complex) (n : 整数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by rw [mul_comm, cpow_int_mul]

Depends on / 依赖: cpow_int_mul, mul_comm
-/
lemma cpow_mul_int (x y : Complex) (n : Int) : x ^ (y * n) = (x ^ y) ^ n := by rw [mul_comm, cpow_int_mul]

/--
lemma `cpow_nat_mul` / 引理 `cpow_nat_mul`

English:
lemma cpow_nat_mul
  given: (x : Complex) (n : Nat) (y : Complex)
  statement: x ^ (n * y) = (x ^ y) ^ n
  proof: mod_cast cpow_int_mul x n y

中文:
引理 cpow_nat_mul
  条件: (x : Complex) (n : 自然数) (y : Complex)
  结论: x ^ (n * y) = (x ^ y) ^ n
  证明: mod_cast cpow_int_mul x n y

Depends on / 依赖: cpow_int_mul, mod_cast
-/
lemma cpow_nat_mul (x : Complex) (n : Nat) (y : Complex) : x ^ (n * y) = (x ^ y) ^ n :=
  mod_cast cpow_int_mul x n y

/--
lemma `cpow_ofNat_mul` / 引理 `cpow_ofNat_mul`

English:
lemma cpow_ofNat_mul
  given: (x : Complex) (n : Nat) [n.AtLeastTwo] (y : Complex)
  proof: cpow_nat_mul x n y

中文:
引理 cpow_ofNat_mul
  条件: (x : Complex) (n : 自然数) [n.AtLeastTwo] (y : Complex)
  证明: cpow_nat_mul x n y

Depends on / 依赖: cpow_nat_mul
-/
lemma cpow_ofNat_mul (x : Complex) (n : Nat) [n.AtLeastTwo] (y : Complex) :
    x ^ (ofNat(n) * y) = (x ^ y) ^ ofNat(n) :=
  cpow_nat_mul x n y

/--
lemma `cpow_mul_nat` / 引理 `cpow_mul_nat`

English:
lemma cpow_mul_nat
  given: (x y : Complex) (n : Nat)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [mul_comm]; rw [cpow_nat_mul]

中文:
引理 cpow_mul_nat
  条件: (x y : Complex) (n : 自然数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [mul_comm]; rw [cpow_nat_mul]

Depends on / 依赖: F.map, F.mapComp, cat_disch, cpow_nat_mul, eqToIso, mapComp, mul_comm
-/
lemma cpow_mul_nat (x y : Complex) (n : Nat) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [mul_comm]; rw [cpow_nat_mul]

/--
lemma `cpow_mul_ofNat` / 引理 `cpow_mul_ofNat`

English:
lemma cpow_mul_ofNat
  given: (x y : Complex) (n : Nat) [n.AtLeastTwo]
  proof: cpow_mul_nat x y n

@[simp, norm_cast]

中文:
引理 cpow_mul_ofNat
  条件: (x y : Complex) (n : 自然数) [n.AtLeastTwo]
  证明: cpow_mul_nat x y n

@[simp, norm_cast]

Depends on / 依赖: cpow_mul_nat, mapComp
-/
lemma cpow_mul_ofNat (x y : Complex) (n : Nat) [n.AtLeastTwo] :
    x ^ (y * ofNat(n)) = (x ^ y) ^ ofNat(n) :=
  cpow_mul_nat x y n

@[simp, norm_cast]
/--
theorem `cpow_natCast` / 定理 `cpow_natCast`

English:
theorem cpow_natCast
  given: (x : Complex) (n : Nat)
  statement: x ^ (n : Complex) = x ^ n
  proof: by simpa using cpow_nat_mul x n 1

@[simp]

中文:
定理 cpow_natCast
  条件: (x : Complex) (n : 自然数)
  结论: x ^ (n : Complex) = x ^ n
  证明: by simpa using cpow_nat_mul x n 1

@[simp]

Depends on / 依赖: cpow_nat_mul
-/
theorem cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Complex) = x ^ n := by simpa using cpow_nat_mul x n 1

@[simp]
/--
lemma `cpow_ofNat` / 引理 `cpow_ofNat`

English:
lemma cpow_ofNat
  given: (x : Complex) (n : Nat) [n.AtLeastTwo]
  proof: cpow_natCast x n

中文:
引理 cpow_ofNat
  条件: (x : Complex) (n : 自然数) [n.AtLeastTwo]
  证明: cpow_natCast x n

Depends on / 依赖: cpow_natCast
-/
lemma cpow_ofNat (x : Complex) (n : Nat) [n.AtLeastTwo] :
    x ^ (ofNat(n) : Complex) = x ^ ofNat(n) :=
  cpow_natCast x n

/--
theorem `cpow_two` / 定理 `cpow_two`

English:
theorem cpow_two
  given: (x : Complex)
  statement: x ^ (2 : Complex) = x ^ (2 : Nat)
  proof: cpow_ofNat x 2

@[simp, norm_cast]

中文:
定理 cpow_two
  条件: (x : Complex)
  结论: x ^ (2 : Complex) = x ^ (2 : 自然数)
  证明: cpow_ofNat x 2

@[simp, norm_cast]

Depends on / 依赖: cpow_ofNat
-/
theorem cpow_two (x : Complex) : x ^ (2 : Complex) = x ^ (2 : Nat) := cpow_ofNat x 2

@[simp, norm_cast]
/--
theorem `cpow_intCast` / 定理 `cpow_intCast`

English:
theorem cpow_intCast
  given: (x : Complex) (n : Int)
  statement: x ^ (n : Complex) = x ^ n
  proof: by simpa using cpow_int_mul x n 1

@[simp]

中文:
定理 cpow_intCast
  条件: (x : Complex) (n : 整数)
  结论: x ^ (n : Complex) = x ^ n
  证明: by simpa using cpow_int_mul x n 1

@[simp]

Depends on / 依赖: cpow_int_mul
-/
theorem cpow_intCast (x : Complex) (n : Int) : x ^ (n : Complex) = x ^ n := by simpa using cpow_int_mul x n 1

@[simp]
/--
theorem `cpow_nat_inv_pow` / 定理 `cpow_nat_inv_pow`

English:
theorem cpow_nat_inv_pow
  given: (x : Complex) {n : Nat} (hn : n != 0)
  statement: (x ^ (n⁻¹ : Complex)) ^ n = x
  proof: by
  rw [← cpow_nat_mul]; rw [mul_inv_cancel₀]; rw [cpow_one]
  assumption_mod_cast

@[simp]

中文:
定理 cpow_nat_inv_pow
  条件: (x : Complex) {n : 自然数} (hn : n != 0)
  结论: (x ^ (n⁻¹ : Complex)) ^ n = x
  证明: by
  rw [← cpow_nat_mul]; rw [mul_inv_cancel₀]; rw [cpow_one]
  assumption_mod_cast

@[simp]

Depends on / 依赖: assumption_mod_cast, cpow_nat_mul, cpow_one
-/
theorem cpow_nat_inv_pow (x : Complex) {n : Nat} (hn : n != 0) : (x ^ (n⁻¹ : Complex)) ^ n = x := by
  rw [← cpow_nat_mul]; rw [mul_inv_cancel₀]; rw [cpow_one]
  assumption_mod_cast

@[simp]
/--
lemma `cpow_ofNat_inv_pow` / 引理 `cpow_ofNat_inv_pow`

English:
lemma cpow_ofNat_inv_pow
  given: (x : Complex) (n : Nat) [n.AtLeastTwo]
  proof: cpow_nat_inv_pow _ (NeZero.ne n)

中文:
引理 cpow_ofNat_inv_pow
  条件: (x : Complex) (n : 自然数) [n.AtLeastTwo]
  证明: cpow_nat_inv_pow _ (NeZero.ne n)

Depends on / 依赖: NeZero, NeZero.ne, cpow_nat_inv_pow
-/
lemma cpow_ofNat_inv_pow (x : Complex) (n : Nat) [n.AtLeastTwo] :
    (x ^ ((ofNat(n) : Complex)⁻¹)) ^ (ofNat(n) : Nat) = x :=
  cpow_nat_inv_pow _ (NeZero.ne n)

/--
lemma `cpow_int_mul'` / 引理 `cpow_int_mul'`

English:
lemma cpow_int_mul'
  given: {x : Complex} {n : Int} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex)
  proof: by
  rw [mul_comm] at hlt hle
  rw [cpow_mul]; rw [cpow_intCast] <;> simpa [log_im]

中文:
引理 cpow_int_mul'
  条件: {x : Complex} {n : 整数} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex)
  证明: by
  rw [mul_comm] at hlt hle
  rw [cpow_mul]; rw [cpow_intCast] <;> simpa [log_im]

Depends on / 依赖: cpow_intCast, cpow_mul, log_im, mul_comm
-/
lemma cpow_int_mul' {x : Complex} {n : Int} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex) :
    x ^ (n * y) = (x ^ n) ^ y := by
  rw [mul_comm] at hlt hle
  rw [cpow_mul]; rw [cpow_intCast] <;> simpa [log_im]

/--
lemma `cpow_nat_mul'` / 引理 `cpow_nat_mul'`

English:
lemma cpow_nat_mul'
  given: {x : Complex} {n : Nat} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex)
  proof: cpow_int_mul' hlt hle y

中文:
引理 cpow_nat_mul'
  条件: {x : Complex} {n : 自然数} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex)
  证明: cpow_int_mul' hlt hle y

Depends on / 依赖: cpow_int_mul
-/
lemma cpow_nat_mul' {x : Complex} {n : Nat} (hlt : -π < n * x.arg) (hle : n * x.arg <= π) (y : Complex) :
    x ^ (n * y) = (x ^ n) ^ y :=
  cpow_int_mul' hlt hle y

/--
lemma `cpow_ofNat_mul'` / 引理 `cpow_ofNat_mul'`

English:
lemma cpow_ofNat_mul'
  statement: {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -π < OfNat.ofNat n * x.arg)
  proof: cpow_nat_mul' hlt hle y

中文:
引理 cpow_ofNat_mul'
  结论: {x : Complex} {n : 自然数} [n.AtLeastTwo] (hlt : -π < Of自然数.of自然数 n * x.arg)
  证明: cpow_nat_mul' hlt hle y

Depends on / 依赖: cpow_nat_mul
-/
lemma cpow_ofNat_mul' {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -π < OfNat.ofNat n * x.arg)
    (hle : OfNat.ofNat n * x.arg <= π) (y : Complex) :
    x ^ (OfNat.ofNat n * y) = (x ^ ofNat(n)) ^ y :=
  cpow_nat_mul' hlt hle y

/--
lemma `pow_cpow_nat_inv` / 引理 `pow_cpow_nat_inv`

English:
lemma pow_cpow_nat_inv
  given: {x : Complex} {n : Nat} (h₀ : n != 0) (hlt : -(π / n) < x.arg) (hle : x.arg <= π / n)
  proof: by
  rw [← cpow_nat_mul']; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 h₀)]; rw [cpow_one]
  · rwa [← div_lt_iff₀' (Nat.cast_pos.2 h₀.bot_lt), neg_div]
  · rwa [← le_div_iff₀' (Nat.cast_pos.2 h₀.bot_lt)]

中文:
引理 pow_cpow_nat_inv
  条件: {x : Complex} {n : 自然数} (h₀ : n != 0) (hlt : -(π / n) < x.arg) (hle : x.arg <= π / n)
  证明: by
  rw [← cpow_nat_mul']; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 h₀)]; rw [cpow_one]
  · rwa [← div_lt_iff₀' (Nat.cast_pos.2 h₀.bot_lt), neg_div]
  · rwa [← le_div_iff₀' (Nat.cast_pos.2 h₀.bot_lt)]

Depends on / 依赖: Nat.cast_ne_zero, Nat.cast_pos, bot_lt, cast_ne_zero, cast_pos, cpow_nat_mul, cpow_one, neg_div
-/
lemma pow_cpow_nat_inv {x : Complex} {n : Nat} (h₀ : n != 0) (hlt : -(π / n) < x.arg) (hle : x.arg <= π / n) :
    (x ^ n) ^ (n⁻¹ : Complex) = x := by
  rw [← cpow_nat_mul']; rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 h₀)]; rw [cpow_one]
  · rwa [← div_lt_iff₀' (Nat.cast_pos.2 h₀.bot_lt), neg_div]
  · rwa [← le_div_iff₀' (Nat.cast_pos.2 h₀.bot_lt)]

/--
lemma `pow_cpow_ofNat_inv` / 引理 `pow_cpow_ofNat_inv`

English:
lemma pow_cpow_ofNat_inv
  statement: {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg)
  proof: pow_cpow_nat_inv (NeZero.ne n) hlt hle

中文:
引理 pow_cpow_ofNat_inv
  结论: {x : Complex} {n : 自然数} [n.AtLeastTwo] (hlt : -(π / Of自然数.of自然数 n) < x.arg)
  证明: pow_cpow_nat_inv (NeZero.ne n) hlt hle

Depends on / 依赖: NeZero, NeZero.ne, pow_cpow_nat_inv
-/
lemma pow_cpow_ofNat_inv {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg)
    (hle : x.arg <= π / OfNat.ofNat n) :
    (x ^ ofNat(n)) ^ ((OfNat.ofNat n : Complex)⁻¹) = x :=
  pow_cpow_nat_inv (NeZero.ne n) hlt hle

/--
lemma `sq_cpow_two_inv` / 引理 `sq_cpow_two_inv`

English:
lemma sq_cpow_two_inv
  given: {x : Complex} (hx : 0 < x.re)
  statement: (x ^ (2 : Nat)) ^ (2⁻¹ : Complex) = x
  proof: pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)

中文:
引理 sq_cpow_two_inv
  条件: {x : Complex} (hx : 0 < x.re)
  结论: (x ^ (2 : 自然数)) ^ (2⁻¹ : Complex) = x
  证明: pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)

Depends on / 依赖: arg_le_pi_div_two_iff, hx.le, neg_pi_div_two_lt_arg_iff, pow_cpow_ofNat_inv
-/
lemma sq_cpow_two_inv {x : Complex} (hx : 0 < x.re) : (x ^ (2 : Nat)) ^ (2⁻¹ : Complex) = x :=
  pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)

/--
lemma `isSquare` / 引理 `isSquare`

English:
lemma isSquare
  given: (x : Complex)
  statement: IsSquare x
  proof: ⟨x ^ (2⁻¹ : Complex), by simp [← sq]⟩

中文:
引理 isSquare
  条件: (x : Complex)
  结论: IsSquare x
  证明: ⟨x ^ (2⁻¹ : Complex), by simp [← sq]⟩
-/
@[simp] lemma isSquare (x : Complex) : IsSquare x := ⟨x ^ (2⁻¹ : Complex), by simp [← sq]⟩

/--
theorem `mul_cpow_ofReal_nonneg` / 定理 `mul_cpow_ofReal_nonneg`

English:
theorem mul_cpow_ofReal_nonneg
  given: {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Complex)
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : Complex

中文:
定理 mul_cpow_ofReal_nonneg
  条件: {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (r : Complex)
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : Complex

Depends on / 依赖: add_mul, cpow_def_of_ne_zero, cpow_zero, eq_or_lt_of_le, eq_or_ne, log_ofReal_mul, mul_ne_zero, mul_one, mul_zero, ofReal_log, ofReal_ne_zero, ofReal_ne_zero.mpr, ofReal_zero, zero_cpow, zero_mul
-/
theorem mul_cpow_ofReal_nonneg {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Complex) :
    ((a : Complex) * (b : Complex)) ^ r = (a : Complex) ^ r * (b : Complex) ^ r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : Complex) != 0 := ofReal_ne_zero.mpr ha'.ne'
  have hb'' : (b : Complex) != 0 := ofReal_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb'')]; rw [log_ofReal_mul ha' hb'']; rw [ofReal_log ha]; rw [add_mul]; rw [exp_add]; rw [← cpow_def_of_ne_zero ha'']; rw [← cpow_def_of_ne_zero hb'']

/--
lemma `natCast_mul_natCast_cpow` / 引理 `natCast_mul_natCast_cpow`

English:
lemma natCast_mul_natCast_cpow
  given: (m n : Nat) (s : Complex)
  statement: (m * n : Complex) ^ s = m ^ s * n ^ s
  proof: ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

中文:
引理 natCast_mul_natCast_cpow
  条件: (m n : 自然数) (s : Complex)
  结论: (m * n : Complex) ^ s = m ^ s * n ^ s
  证明: ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

Depends on / 依赖: cast_nonneg, m.cast_nonneg, mul_cpow_ofReal_nonneg, n.cast_nonneg, ofReal_natCast
-/
lemma natCast_mul_natCast_cpow (m n : Nat) (s : Complex) : (m * n : Complex) ^ s = m ^ s * n ^ s :=
  ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

/--
lemma `natCast_cpow_natCast_mul` / 引理 `natCast_cpow_natCast_mul`

English:
lemma natCast_cpow_natCast_mul
  given: (n m : Nat) (z : Complex)
  statement: (n : Complex) ^ (m * z) = ((n : Complex) ^ m) ^ z
  proof: by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]

中文:
引理 natCast_cpow_natCast_mul
  条件: (n m : 自然数) (z : Complex)
  结论: (n : Complex) ^ (m * z) = ((n : Complex) ^ m) ^ z
  证明: by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]

Depends on / 依赖: Left.neg_neg_iff, cpow_nat_mul, mul_zero, natCast_arg, neg_neg_iff, pi_pos, pi_pos.le
-/
lemma natCast_cpow_natCast_mul (n m : Nat) (z : Complex) : (n : Complex) ^ (m * z) = ((n : Complex) ^ m) ^ z := by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]

/--
theorem `inv_cpow_eq_ite` / 定理 `inv_cpow_eq_ite`

English:
theorem inv_cpow_eq_ite
  given: (x : Complex) (n : Complex)
  proof: by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl

中文:
定理 inv_cpow_eq_ite
  条件: (x : Complex) (n : Complex)
  证明: by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl

Depends on / 依赖: Complex.cpow_def, Inv.inv, RCLike, RCLike.conj_inv, apply_ite, conj_conj, conj_inv, cpow_def, exp_conj, exp_neg, inv_eq_zero, inv_one, inv_zero, ite_mul, log_inv_eq_ite, map_eq_zero, map_mul, map_one, map_zero, neg_mul
-/
theorem inv_cpow_eq_ite (x : Complex) (n : Complex) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ := by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl

/--
theorem `inv_cpow` / 定理 `inv_cpow`

English:
theorem inv_cpow
  given: (x : Complex) (n : Complex) (hx : x.arg != π)
  statement: x⁻¹ ^ n = (x ^ n)⁻¹
  proof: by
  rw [inv_cpow_eq_ite]; rw [if_neg hx]

中文:
定理 inv_cpow
  条件: (x : Complex) (n : Complex) (hx : x.arg != π)
  结论: x⁻¹ ^ n = (x ^ n)⁻¹
  证明: by
  rw [inv_cpow_eq_ite]; rw [if_neg hx]

Depends on / 依赖: if_neg, inv_cpow_eq_ite
-/
theorem inv_cpow (x : Complex) (n : Complex) (hx : x.arg != π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite]; rw [if_neg hx]

/--
lemma `inv_cpow_ofReal_nonneg` / 引理 `inv_cpow_ofReal_nonneg`

English:
lemma inv_cpow_ofReal_nonneg
  given: {a : Real} (ha : 0 <= a) (r : Complex)
  proof: inv_cpow _ _ by simpa [arg_ofReal_of_nonneg ha] using Real.pi_ne_zero.symm

中文:
引理 inv_cpow_ofReal_nonneg
  条件: {a : 实数} (ha : 0 <= a) (r : Complex)
  证明: inv_cpow _ _ by simpa [arg_ofReal_of_nonneg ha] using Real.pi_ne_zero.symm

Depends on / 依赖: Real.pi_ne_zero.symm, arg_ofReal_of_nonneg, inv_cpow, pi_ne_zero
-/
lemma inv_cpow_ofReal_nonneg {a : Real} (ha : 0 <= a) (r : Complex) :
    ((a : Complex)⁻¹) ^ r = (a ^ r : Complex)⁻¹ :=
inv_cpow _ _ by simpa [arg_ofReal_of_nonneg ha] using Real.pi_ne_zero.symm

/--
lemma `div_cpow_ofReal_nonneg` / 引理 `div_cpow_ofReal_nonneg`

English:
lemma div_cpow_ofReal_nonneg
  given: {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Complex)
  proof: by
  rw [div_eq_mul_inv]; rw [← ofReal_inv]; rw [mul_cpow_ofReal_nonneg ha (inv_nonneg_of_nonneg hb)]; rw [ofReal_inv]; rw [inv_cpow_ofReal_nonneg hb]; rw [div_eq_mul_inv]

中文:
引理 div_cpow_ofReal_nonneg
  条件: {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (r : Complex)
  证明: by
  rw [div_eq_mul_inv]; rw [← ofReal_inv]; rw [mul_cpow_ofReal_nonneg ha (inv_nonneg_of_nonneg hb)]; rw [ofReal_inv]; rw [inv_cpow_ofReal_nonneg hb]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, inv_cpow_ofReal_nonneg, inv_nonneg_of_nonneg, mul_cpow_ofReal_nonneg, ofReal_inv
-/
lemma div_cpow_ofReal_nonneg {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Complex) :
    ((a : Complex) / (b : Complex)) ^ r = (a : Complex) ^ r / (b : Complex) ^ r := by
  rw [div_eq_mul_inv]; rw [← ofReal_inv]; rw [mul_cpow_ofReal_nonneg ha (inv_nonneg_of_nonneg hb)]; rw [ofReal_inv]; rw [inv_cpow_ofReal_nonneg hb]; rw [div_eq_mul_inv]

/--
theorem `inv_cpow_eq_ite'` / 定理 `inv_cpow_eq_ite'`

English:
theorem inv_cpow_eq_ite'
  given: (x : Complex) (n : Complex)
  proof: by
  rw [inv_cpow_eq_ite]; rw [apply_ite conj]; rw [conj_conj]; rw [conj_conj]
  split_ifs with h
  · rfl
  · rw [inv_cpow _ _ h]

中文:
定理 inv_cpow_eq_ite'
  条件: (x : Complex) (n : Complex)
  证明: by
  rw [inv_cpow_eq_ite]; rw [apply_ite conj]; rw [conj_conj]; rw [conj_conj]
  split_ifs with h
  · rfl
  · rw [inv_cpow _ _ h]

Depends on / 依赖: apply_ite, conj_conj, inv_cpow, inv_cpow_eq_ite, split_ifs
-/
theorem inv_cpow_eq_ite' (x : Complex) (n : Complex) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n := by
  rw [inv_cpow_eq_ite]; rw [apply_ite conj]; rw [conj_conj]; rw [conj_conj]
  split_ifs with h
  · rfl
  · rw [inv_cpow _ _ h]

/--
theorem `conj_cpow_eq_ite` / 定理 `conj_cpow_eq_ite`

English:
theorem conj_cpow_eq_ite
  given: (x : Complex) (n : Complex)
  proof: by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl

中文:
定理 conj_cpow_eq_ite
  条件: (x : Complex) (n : Complex)
  证明: by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl

Depends on / 依赖: apply_ite, conj_conj, cpow_def, exp_conj, log_conj_eq_ite, map_eq_zero, map_mul, map_one, map_zero, simp_rw, split_ifs
-/
theorem conj_cpow_eq_ite (x : Complex) (n : Complex) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) := by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl

/--
theorem `conj_cpow` / 定理 `conj_cpow`

English:
theorem conj_cpow
  given: (x : Complex) (n : Complex) (hx : x.arg != π)
  statement: conj x ^ n = conj (x ^ conj n)
  proof: by
  rw [conj_cpow_eq_ite]; rw [if_neg hx]

中文:
定理 conj_cpow
  条件: (x : Complex) (n : Complex) (hx : x.arg != π)
  结论: conj x ^ n = conj (x ^ conj n)
  证明: by
  rw [conj_cpow_eq_ite]; rw [if_neg hx]

Depends on / 依赖: conj_cpow_eq_ite, if_neg
-/
theorem conj_cpow (x : Complex) (n : Complex) (hx : x.arg != π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite]; rw [if_neg hx]

/--
theorem `cpow_conj` / 定理 `cpow_conj`

English:
theorem cpow_conj
  given: (x : Complex) (n : Complex) (hx : x.arg != π)
  statement: x ^ conj n = conj (conj x ^ n)
  proof: by
  rw [conj_cpow _ _ hx]; rw [conj_conj]

中文:
定理 cpow_conj
  条件: (x : Complex) (n : Complex) (hx : x.arg != π)
  结论: x ^ conj n = conj (conj x ^ n)
  证明: by
  rw [conj_cpow _ _ hx]; rw [conj_conj]

Depends on / 依赖: conj_conj, conj_cpow
-/
theorem cpow_conj (x : Complex) (n : Complex) (hx : x.arg != π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx]; rw [conj_conj]

/--
lemma `natCast_add_one_cpow_ne_zero` / 引理 `natCast_add_one_cpow_ne_zero`

English:
lemma natCast_add_one_cpow_ne_zero
  given: (n : Nat) (z : Complex)
  statement: (n + 1 : Complex) ^ z != 0
  proof: mt (cpow_eq_zero_iff ..).mp fun H => by norm_cast at H; exact H.1

中文:
引理 natCast_add_one_cpow_ne_zero
  条件: (n : 自然数) (z : Complex)
  结论: (n + 1 : Complex) ^ z != 0
  证明: mt (cpow_eq_zero_iff ..).mp fun H => by norm_cast at H; exact H.1

Depends on / 依赖: cpow_eq_zero_iff
-/
lemma natCast_add_one_cpow_ne_zero (n : Nat) (z : Complex) : (n + 1 : Complex) ^ z != 0 :=
  mt (cpow_eq_zero_iff ..).mp fun H => by norm_cast at H; exact H.1

end Complex

-- section Tactics

-- /-!
-- ## Tactic extensions for complex powers
-- -/


-- namespace NormNum

-- theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
-- rw [← h, hb, Complex.cpow_natCast]

-- theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
-- a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_natCast]

-- open Tactic

-- /-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
-- unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
-- let na ← a.to_rat
-- let icα ← mk_instance_cache α
-- let icβ ← mk_instance_cache β
-- match match_sign b with
-- | Sum.inl b => do
-- let nc ← mk_instance_cache q(ℕ)
-- let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
-- let (icα, c, h) ← prove_pow a na icα b'
-- let cr ← c
-- let (icα, c', hc) ← prove_inv icα c cr
-- pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
-- | Sum.inr ff => pure (one, expr.const zero [] a)
-- | Sum.inr tt => do
-- let nc ← mk_instance_cache q(ℕ)
-- let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
-- let (icα, c, h) ← prove_pow a na icα b'
-- pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])

-- /-- Evaluate `Complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
-- prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))

-- /-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_cpow : expr → tactic (expr × expr)
-- | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
-- | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
-- | _ => tactic.failed

-- end NormNum

-- end Tactics
