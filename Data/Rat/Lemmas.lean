/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.PNat.Defs

/-!
# Further lemmas for the Rational Numbers

-/

@[expose] public section


namespace Rat

-- TODO: move this to Lean
attribute [norm_cast] num_intCast den_intCast

/--
theorem `num_dvd` / 定理 `num_dvd`

English:
theorem num_dvd
  given: (a) {b : Int} (b0 : b != 0)
  statement: (a /. b).num ∣ a
  proof: by
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [Rat.mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (mod_cast h)] at e
refine Int.natAbs_dvd.1 Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at this;

中文:
定理 num_dvd
  条件: (a) {b : 整数} (b0 : b != 0)
  结论: (a /. b).num ∣ a
  证明: by
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [Rat.mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (mod_cast h)] at e
refine Int.natAbs_dvd.1 Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at this;

Depends on / 依赖: Int.dvd_natAbs, Int.natAbs, Int.natAbs_dvd, Int.natAbs_mul, Int.natAbs_natCast, Int.natCast_dvd_natCast, Rat.mk_eq_divInt, c.dvd_of_dvd_mul_right, congr_arg, divInt_eq_divInt_iff, dvd_natAbs, dvd_of_dvd_mul_right, mk_eq_divInt, mod_cast, natAbs, natAbs_dvd, natAbs_mul, natAbs_natCast, natCast_dvd_natCast
-/
theorem num_dvd (a) {b : Int} (b0 : b != 0) : (a /. b).num ∣ a := by
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [Rat.mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (mod_cast h)] at e
refine Int.natAbs_dvd.1 Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at this; simp [this]

/--
theorem `den_dvd` / 定理 `den_dvd`

English:
theorem den_dvd
  given: (a b : Int)
  statement: ((a /. b).den : Int) ∣ b
  proof: by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
refine Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2 c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul]; rw [← Int.

中文:
定理 den_dvd
  条件: (a b : 整数)
  结论: ((a /. b).den : 整数) ∣ b
  证明: by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
refine Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2 c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul]; rw [← Int.

Depends on / 依赖: Int.dvd_natAbs, Int.natAbs_mul, Int.natCast_dvd_natCast, Int.natCast_pos, Nat.pos_of_ne_zero, c.symm.dvd_of_dvd_mul_left, divInt_eq_divInt_iff, dvd_natAbs, dvd_of_dvd_mul_left, mk_eq_divInt, natAbs_mul, natCast_dvd_natCast, natCast_pos, ne_of_gt, pos_of_ne_zero
-/
theorem den_dvd (a b : Int) : ((a /. b).den : Int) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk_eq_divInt]; rw [divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
refine Int.dvd_natAbs.1 Int.natCast_dvd_natCast.2 c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul]; rw [← Int.natCast_dvd_natCast]; rw [Int.dvd_natAbs]; rw [← e]; simp

/--
theorem `num_den_mk` / 定理 `num_den_mk`

English:
theorem num_den_mk
  given: {q : Rat} {n d : Int} (hd : d != 0) (qdf : q = n /. d)
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_divInt_iff ?_ hd).mp ?_
    · exact Int.natCast_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_divInt_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine ⟨n / q.

中文:
定理 num_den_mk
  条件: {q : Rat} {n d : 整数} (hd : d != 0) (qdf : q = n /. d)
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_divInt_iff ?_ hd).mp ?_
    · exact Int.natCast_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_divInt_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine ⟨n / q.

Depends on / 依赖: Int.ediv_mul_cancel, Int.eq_mul_div_of_mul_eq_mul_of_dvd_left, Int.natCast_ne_zero.mpr, Rat.den_nz, Rat.num_dvd, Rat.num_ne_zero, den_nz, divInt_eq_divInt_iff, divInt_ne_zero, ediv_mul_cancel, eq_mul_div_of_mul_eq_mul_of_dvd_left, eq_or_ne, natCast_ne_zero, num_divInt_den, num_dvd, num_ne_zero, q.den, q.num
-/
theorem num_den_mk {q : Rat} {n d : Int} (hd : d != 0) (qdf : q = n /. d) :
    exists c : Int, n = c * q.num ∧ d = c * q.den := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_divInt_iff ?_ hd).mp ?_
    · exact Int.natCast_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_divInt_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine ⟨n / q.num, ?_, ?_⟩
  · rw [Int.ediv_mul_cancel hqdn]
  · refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ hqdn this
    rw [qdf]
    exact Rat.num_ne_zero.2 ((divInt_ne_zero hd).mpr hn)

/--
theorem `add_den_dvd_lcm` / 定理 `add_den_dvd_lcm`

English:
theorem add_den_dvd_lcm
  given: (q₁ q₂ : Rat)
  statement: (q₁ + q₂).den ∣ q₁.den.lcm q₂.den
  proof: by
  rw [add_def]; rw [normalize_eq]; rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← In

中文:
定理 add_den_dvd_lcm
  条件: (q₁ q₂ : Rat)
  结论: (q₁ + q₂).den ∣ q₁.den.lcm q₂.den
  证明: by
  rw [add_def]; rw [normalize_eq]; rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← In

Depends on / 依赖: Int.dvd_add, Int.dvd_natAbs, Int.natCast_dvd_natCast, Nat.div_dvd_iff_dvd_mul, Nat.dvd_gcd_iff, Nat.gcd_dvd_left, Nat.gcd_dvd_right, Nat.gcd_mul_lcm, Nat.gcd_pos_of_pos_right, Nat.lcm_ne_zero, Nat.pos_iff_ne_zero, add_def, div_dvd_iff_dvd_mul, dvd_add, dvd_gcd_iff, dvd_mul_of_dvd_right, dvd_mul_right, dvd_natAbs, gcd_dvd_left, gcd_dvd_right
-/
theorem add_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den := by
  rw [add_def]; rw [normalize_eq]; rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← Int.natCast_dvd_natCast]; rw [Int.dvd_natAbs]
  apply Int.dvd_add
    <;> apply dvd_mul_of_dvd_right <;> rw [Int.natCast_dvd_natCast]
    <;> [exact Nat.gcd_dvd_right _ _; exact Nat.gcd_dvd_left _ _]

/--
theorem `sub_den_dvd_lcm` / 定理 `sub_den_dvd_lcm`

English:
theorem sub_den_dvd_lcm
  given: (q₁ q₂ : Rat)
  statement: (q₁ - q₂).den ∣ q₁.den.lcm q₂.den
  proof: by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)

中文:
定理 sub_den_dvd_lcm
  条件: (q₁ q₂ : Rat)
  结论: (q₁ - q₂).den ∣ q₁.den.lcm q₂.den
  证明: by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)

Depends on / 依赖: add_den_dvd_lcm, neg_den, sub_eq_add_neg
-/
theorem sub_den_dvd_lcm (q₁ q₂ : Rat) : (q₁ - q₂).den ∣ q₁.den.lcm q₂.den := by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)

/--
theorem `add_den_dvd` / 定理 `add_den_dvd`

English:
theorem add_den_dvd
  given: (q₁ q₂ : Rat)
  statement: (q₁ + q₂).den ∣ q₁.den * q₂.den
  proof: (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

中文:
定理 add_den_dvd
  条件: (q₁ q₂ : Rat)
  结论: (q₁ + q₂).den ∣ q₁.den * q₂.den
  证明: (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

Depends on / 依赖: Nat.lcm_dvd_mul, add_den_dvd_lcm, lcm_dvd_mul
-/
theorem add_den_dvd (q₁ q₂ : Rat) : (q₁ + q₂).den ∣ q₁.den * q₂.den :=
  (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

/--
theorem `sub_den_dvd` / 定理 `sub_den_dvd`

English:
theorem sub_den_dvd
  given: (q₁ q₂ : Rat)
  statement: (q₁ - q₂).den ∣ q₁.den * q₂.den
  proof: (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

中文:
定理 sub_den_dvd
  条件: (q₁ q₂ : Rat)
  结论: (q₁ - q₂).den ∣ q₁.den * q₂.den
  证明: (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

Depends on / 依赖: Nat.lcm_dvd_mul, lcm_dvd_mul, sub_den_dvd_lcm
-/
theorem sub_den_dvd (q₁ q₂ : Rat) : (q₁ - q₂).den ∣ q₁.den * q₂.den :=
  (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

/--
theorem `mul_den_dvd` / 定理 `mul_den_dvd`

English:
theorem mul_den_dvd
  given: (q₁ q₂ : Rat)
  statement: (q₁ * q₂).den ∣ q₁.den * q₂.den
  proof: by
  rw [mul_def]; rw [normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right

中文:
定理 mul_den_dvd
  条件: (q₁ q₂ : Rat)
  结论: (q₁ * q₂).den ∣ q₁.den * q₂.den
  证明: by
  rw [mul_def]; rw [normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right

Depends on / 依赖: Nat.div_dvd_of_dvd, Nat.gcd_dvd_right, div_dvd_of_dvd, gcd_dvd_right, mul_def, normalize_eq
-/
theorem mul_den_dvd (q₁ q₂ : Rat) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def]; rw [normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right

/--
theorem `mul_num` / 定理 `mul_num`

English:
theorem mul_num
  given: (q₁ q₂ : Rat)
  proof: by
  rw [mul_def]; rw [normalize_eq]

中文:
定理 mul_num
  条件: (q₁ q₂ : Rat)
  证明: by
  rw [mul_def]; rw [normalize_eq]

Depends on / 依赖: mul_def, normalize_eq
-/
theorem mul_num (q₁ q₂ : Rat) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def]; rw [normalize_eq]

/--
theorem `mul_den` / 定理 `mul_den`

English:
theorem mul_den
  given: (q₁ q₂ : Rat)
  proof: by
  rw [mul_def]; rw [normalize_eq]

@[simp]

中文:
定理 mul_den
  条件: (q₁ q₂ : Rat)
  证明: by
  rw [mul_def]; rw [normalize_eq]

@[simp]

Depends on / 依赖: mul_def, normalize_eq
-/
theorem mul_den (q₁ q₂ : Rat) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def]; rw [normalize_eq]

@[simp]
/--
theorem `add_intCast_den` / 定理 `add_intCast_den`

English:
theorem add_intCast_den
  given: (q : Rat) (n : Int)
  statement: (q + n).den = q.den
  proof: by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]

中文:
定理 add_intCast_den
  条件: (q : Rat) (n : 整数)
  结论: (q + n).den = q.den
  证明: by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]

Depends on / 依赖: Nat.dvd_antisymm, add_den_dvd, dvd_antisymm
-/
theorem add_intCast_den (q : Rat) (n : Int) : (q + n).den = q.den := by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]
/--
theorem `intCast_add_den` / 定理 `intCast_add_den`

English:
theorem intCast_add_den
  given: (n : Int) (q : Rat)
  statement: (n + q).den = q.den
  proof: by
  rw [add_comm]; rw [add_intCast_den]

@[simp]

中文:
定理 intCast_add_den
  条件: (n : 整数) (q : Rat)
  结论: (n + q).den = q.den
  证明: by
  rw [add_comm]; rw [add_intCast_den]

@[simp]

Depends on / 依赖: add_comm, add_intCast_den
-/
theorem intCast_add_den (n : Int) (q : Rat) : (n + q).den = q.den := by
  rw [add_comm]; rw [add_intCast_den]

@[simp]
/--
theorem `sub_intCast_den` / 定理 `sub_intCast_den`

English:
theorem sub_intCast_den
  given: (q : Rat) (n : Int)
  statement: (q - n).den = q.den
  proof: by
  rw [sub_eq_add_neg]; rw [← Int.cast_neg]; rw [add_intCast_den]

@[simp]

中文:
定理 sub_intCast_den
  条件: (q : Rat) (n : 整数)
  结论: (q - n).den = q.den
  证明: by
  rw [sub_eq_add_neg]; rw [← Int.cast_neg]; rw [add_intCast_den]

@[simp]

Depends on / 依赖: Int.cast_neg, add_intCast_den, cast_neg, sub_eq_add_neg
-/
theorem sub_intCast_den (q : Rat) (n : Int) : (q - n).den = q.den := by
  rw [sub_eq_add_neg]; rw [← Int.cast_neg]; rw [add_intCast_den]

@[simp]
/--
theorem `intCast_sub_den` / 定理 `intCast_sub_den`

English:
theorem intCast_sub_den
  given: (n : Int) (q : Rat)
  statement: (n - q).den = q.den
  proof: by
  rw [sub_eq_add_neg]; rw [intCast_add_den]; rw [neg_den]

@[simp]

中文:
定理 intCast_sub_den
  条件: (n : 整数) (q : Rat)
  结论: (n - q).den = q.den
  证明: by
  rw [sub_eq_add_neg]; rw [intCast_add_den]; rw [neg_den]

@[simp]

Depends on / 依赖: intCast_add_den, neg_den, sub_eq_add_neg
-/
theorem intCast_sub_den (n : Int) (q : Rat) : (n - q).den = q.den := by
  rw [sub_eq_add_neg]; rw [intCast_add_den]; rw [neg_den]

@[simp]
/--
theorem `add_natCast_den` / 定理 `add_natCast_den`

English:
theorem add_natCast_den
  given: (q : Rat) (n : Nat)
  statement: (q + n).den = q.den
  proof: mod_cast add_intCast_den q n

@[simp]

中文:
定理 add_natCast_den
  条件: (q : Rat) (n : 自然数)
  结论: (q + n).den = q.den
  证明: mod_cast add_intCast_den q n

@[simp]

Depends on / 依赖: add_intCast_den, mod_cast
-/
theorem add_natCast_den (q : Rat) (n : Nat) : (q + n).den = q.den := mod_cast add_intCast_den q n

@[simp]
/--
theorem `natCast_add_den` / 定理 `natCast_add_den`

English:
theorem natCast_add_den
  given: (n : Nat) (q : Rat)
  statement: (n + q).den = q.den
  proof: mod_cast intCast_add_den n q

@[simp]

中文:
定理 natCast_add_den
  条件: (n : 自然数) (q : Rat)
  结论: (n + q).den = q.den
  证明: mod_cast intCast_add_den n q

@[simp]

Depends on / 依赖: intCast_add_den, mod_cast
-/
theorem natCast_add_den (n : Nat) (q : Rat) : (n + q).den = q.den := mod_cast intCast_add_den n q

@[simp]
/--
theorem `sub_natCast_den` / 定理 `sub_natCast_den`

English:
theorem sub_natCast_den
  given: (q : Rat) (n : Nat)
  statement: (q - n).den = q.den
  proof: mod_cast sub_intCast_den q n

@[simp]

中文:
定理 sub_natCast_den
  条件: (q : Rat) (n : 自然数)
  结论: (q - n).den = q.den
  证明: mod_cast sub_intCast_den q n

@[simp]

Depends on / 依赖: mod_cast, sub_intCast_den
-/
theorem sub_natCast_den (q : Rat) (n : Nat) : (q - n).den = q.den := mod_cast sub_intCast_den q n

@[simp]
/--
theorem `natCast_sub_den` / 定理 `natCast_sub_den`

English:
theorem natCast_sub_den
  given: (n : Nat) (q : Rat)
  statement: (n - q).den = q.den
  proof: mod_cast intCast_sub_den n q

中文:
定理 natCast_sub_den
  条件: (n : 自然数) (q : Rat)
  结论: (n - q).den = q.den
  证明: mod_cast intCast_sub_den n q

Depends on / 依赖: intCast_sub_den, mod_cast
-/
theorem natCast_sub_den (n : Nat) (q : Rat) : (n - q).den = q.den := mod_cast intCast_sub_den n q

/--
theorem `add_ofNat_den` / 定理 `add_ofNat_den`

English:
theorem add_ofNat_den
  given: (q : Rat) (n : Nat)
  statement: (q + ofNat(n)).den = q.den
  proof: add_natCast_den q n

中文:
定理 add_ofNat_den
  条件: (q : Rat) (n : 自然数)
  结论: (q + of自然数(n)).den = q.den
  证明: add_natCast_den q n
-/
@[simp] theorem add_ofNat_den (q : Rat) (n : Nat) : (q + ofNat(n)).den = q.den := add_natCast_den q n
/--
theorem `ofNat_add_den` / 定理 `ofNat_add_den`

English:
theorem ofNat_add_den
  given: (n : Nat) (q : Rat)
  statement: (ofNat(n) + q).den = q.den
  proof: natCast_add_den n q

中文:
定理 ofNat_add_den
  条件: (n : 自然数) (q : Rat)
  结论: (of自然数(n) + q).den = q.den
  证明: natCast_add_den n q
-/
@[simp] theorem ofNat_add_den (n : Nat) (q : Rat) : (ofNat(n) + q).den = q.den := natCast_add_den n q
/--
theorem `sub_ofNat_den` / 定理 `sub_ofNat_den`

English:
theorem sub_ofNat_den
  given: (q : Rat) (n : Nat)
  statement: (q - ofNat(n)).den = q.den
  proof: sub_natCast_den ..

中文:
定理 sub_ofNat_den
  条件: (q : Rat) (n : 自然数)
  结论: (q - of自然数(n)).den = q.den
  证明: sub_natCast_den ..
-/
@[simp] theorem sub_ofNat_den (q : Rat) (n : Nat) : (q - ofNat(n)).den = q.den := sub_natCast_den ..
/--
theorem `ofNat_sub_den` / 定理 `ofNat_sub_den`

English:
theorem ofNat_sub_den
  given: (n : Nat) (q : Rat)
  statement: (ofNat(n) - q).den = q.den
  proof: natCast_sub_den ..

中文:
定理 ofNat_sub_den
  条件: (n : 自然数) (q : Rat)
  结论: (of自然数(n) - q).den = q.den
  证明: natCast_sub_den ..
-/
@[simp] theorem ofNat_sub_den (n : Nat) (q : Rat) : (ofNat(n) - q).den = q.den := natCast_sub_den ..

/--
theorem `den_mul_den_eq_den_mul_gcd` / 定理 `den_mul_den_eq_den_mul_gcd`

English:
theorem den_mul_den_eq_den_mul_gcd
  given: (q₁ q₂ : Rat)
  proof: by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

中文:
定理 den_mul_den_eq_den_mul_gcd
  条件: (q₁ q₂ : Rat)
  证明: by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

Depends on / 依赖: Nat.dvd_iff_div_mul_eq, Nat.gcd_dvd_right, dvd_iff_div_mul_eq, gcd_dvd_right, mul_den
-/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : Rat) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

/--
theorem `num_mul_num_eq_num_mul_gcd` / 定理 `num_mul_num_eq_num_mul_gcd`

English:
theorem num_mul_num_eq_num_mul_gcd
  given: (q₁ q₂ : Rat)
  proof: by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)

中文:
定理 num_mul_num_eq_num_mul_gcd
  条件: (q₁ q₂ : Rat)
  证明: by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)

Depends on / 依赖: Int.dvd_natAbs, Int.ediv_mul_cancel, Int.ofNat_dvd.mpr, Nat.gcd_dvd_left, dvd_natAbs, ediv_mul_cancel, gcd_dvd_left, mul_num, ofNat_dvd
-/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : Rat) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)

/--
theorem `mul_self_num` / 定理 `mul_self_num`

English:
theorem mul_self_num
  given: (q : Rat)
  statement: (q * q).num = q.num * q.num
  proof: by
  rw [mul_num]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Int.ofNat_one]; rw [Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

中文:
定理 mul_self_num
  条件: (q : Rat)
  结论: (q * q).num = q.num * q.num
  证明: by
  rw [mul_num]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Int.ofNat_one]; rw [Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

Depends on / 依赖: Coprime, Int.ediv_one, Int.natAbs_mul, Int.ofNat_one, Nat.Coprime.gcd_eq_one, ediv_one, gcd_eq_one, mul_left, mul_num, mul_right, natAbs_mul, ofNat_one, q.reduced, q.reduced.mul_right, reduced
-/
theorem mul_self_num (q : Rat) : (q * q).num = q.num * q.num := by
  rw [mul_num]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Int.ofNat_one]; rw [Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

/--
theorem `mul_self_den` / 定理 `mul_self_den`

English:
theorem mul_self_den
  given: (q : Rat)
  statement: (q * q).den = q.den * q.den
  proof: by
  rw [Rat.mul_den]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

中文:
定理 mul_self_den
  条件: (q : Rat)
  结论: (q * q).den = q.den * q.den
  证明: by
  rw [Rat.mul_den]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

Depends on / 依赖: Coprime, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Nat.div_one, Rat.mul_den, div_one, gcd_eq_one, mul_den, mul_left, mul_right, natAbs_mul, q.reduced, q.reduced.mul_right, reduced
-/
theorem mul_self_den (q : Rat) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den]; rw [Int.natAbs_mul]; rw [Nat.Coprime.gcd_eq_one]; rw [Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

/--
theorem `add_num_den` / 定理 `add_num_den`

English:
theorem add_num_den
  given: (q r : Rat)
  proof: by
  have hqd : (q.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]

中文:
定理 add_num_den
  条件: (q r : Rat)
  证明: by
  have hqd : (q.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]

Depends on / 依赖: Int.natCast_ne_zero_iff_pos, conv_lhs, den_pos, divInt_add_divInt, mul_comm, natCast_ne_zero_iff_pos, num_divInt_den, q.den, q.den_pos, r.den, r.den_pos, r.num
-/
theorem add_num_den (q r : Rat) :
    q + r = (q.num * r.den + q.den * r.num : Int) /. (↑q.den * ↑r.den : Int) := by
  have hqd : (q.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]


/--
theorem `isSquare_iff` / 定理 `isSquare_iff`

English:
theorem isSquare_iff
  given: {q : Rat}
  statement: IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den
  proof: by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num]; rw [mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm]; rw [← Int.cast_mul]; rw [← Nat.cast_mul]; rw [← hnr]; rw [← hdr]; rw [num_div_den]

@[n

中文:
定理 isSquare_iff
  条件: {q : Rat}
  结论: IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den
  证明: by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num]; rw [mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm]; rw [← Int.cast_mul]; rw [← Nat.cast_mul]; rw [← hnr]; rw [← hdr]; rw [num_div_den]

@[n

Depends on / 依赖: Int.cast_mul, IsSquare, IsSquare.mul_self, Nat.cast_mul, Rat.mul_self_num, and_self, cast_mul, div_mul_div_comm, mul_self, mul_self_den, mul_self_num, num_div_den
-/
theorem isSquare_iff {q : Rat} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den := by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num]; rw [mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm]; rw [← Int.cast_mul]; rw [← Nat.cast_mul]; rw [← hnr]; rw [← hdr]; rw [num_div_den]

@[norm_cast, simp]
/--
theorem `isSquare_natCast_iff` / 定理 `isSquare_natCast_iff`

English:
theorem isSquare_natCast_iff
  given: {n : Nat}
  statement: IsSquare (n : Rat) ↔ IsSquare n
  proof: by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]

中文:
定理 isSquare_natCast_iff
  条件: {n : 自然数}
  结论: IsSquare (n : Rat) ↔ IsSquare n
  证明: by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]

Depends on / 依赖: Int.isSquare_natCast_iff, IsSquare, IsSquare.one, and_true, den_natCast, isSquare_iff, isSquare_natCast_iff, num_natCast, simp_rw
-/
theorem isSquare_natCast_iff {n : Nat} : IsSquare (n : Rat) ↔ IsSquare n := by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]
/--
theorem `isSquare_intCast_iff` / 定理 `isSquare_intCast_iff`

English:
theorem isSquare_intCast_iff
  given: {z : Int}
  statement: IsSquare (z : Rat) ↔ IsSquare z
  proof: by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp]

中文:
定理 isSquare_intCast_iff
  条件: {z : 整数}
  结论: IsSquare (z : Rat) ↔ IsSquare z
  证明: by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp]

Depends on / 依赖: IsSquare, IsSquare.one, and_true, den_intCast, isSquare_iff, num_intCast, simp_rw
-/
theorem isSquare_intCast_iff {z : Int} : IsSquare (z : Rat) ↔ IsSquare z := by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp]
/--
theorem `isSquare_ofNat_iff` / 定理 `isSquare_ofNat_iff`

English:
theorem isSquare_ofNat_iff
  given: {n : Nat}
  proof: isSquare_natCast_iff

中文:
定理 isSquare_ofNat_iff
  条件: {n : 自然数}
  证明: isSquare_natCast_iff

Depends on / 依赖: isSquare_natCast_iff
-/
theorem isSquare_ofNat_iff {n : Nat} :
    IsSquare (ofNat(n) : Rat) ↔ IsSquare (OfNat.ofNat n : Nat) :=
  isSquare_natCast_iff

/--
theorem `mkRat_add_mkRat_of_den` / 定理 `mkRat_add_mkRat_of_den`

English:
theorem mkRat_add_mkRat_of_den
  given: (n₁ n₂ : Int) {d : Nat} (h : d != 0)
  proof: by
  rw [mkRat_add_mkRat _ _ h h]; rw [← add_mul]; rw [mkRat_mul_right h]

中文:
定理 mkRat_add_mkRat_of_den
  条件: (n₁ n₂ : 整数) {d : 自然数} (h : d != 0)
  证明: by
  rw [mkRat_add_mkRat _ _ h h]; rw [← add_mul]; rw [mkRat_mul_right h]

Depends on / 依赖: add_mul, mkRat_add_mkRat, mkRat_mul_right
-/
theorem mkRat_add_mkRat_of_den (n₁ n₂ : Int) {d : Nat} (h : d != 0) :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  rw [mkRat_add_mkRat _ _ h h]; rw [← add_mul]; rw [mkRat_mul_right h]

section Casts

/--
theorem `exists_eq_mul_div_num_and_eq_mul_div_den` / 定理 `exists_eq_mul_div_num_and_eq_mul_div_den`

English:
theorem exists_eq_mul_div_num_and_eq_mul_div_den
  given: (n : Int) {d : Int} (d_ne_zero : d != 0)
  proof: haveI : (n : Rat) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this

中文:
定理 exists_eq_mul_div_num_and_eq_mul_div_den
  条件: (n : 整数) {d : 整数} (d_ne_zero : d != 0)
  证明: haveI : (n : Rat) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this

Depends on / 依赖: Rat.divInt, Rat.divInt_eq_div, Rat.num_den_mk, d_ne_zero, divInt, divInt_eq_div, num_den_mk
-/
theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : Int) {d : Int} (d_ne_zero : d != 0) :
    exists c : Int, n = c * ((n : Rat) / d).num ∧ (d : Int) = c * ((n : Rat) / d).den :=
  haveI : (n : Rat) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this

/--
theorem `mul_num_den'` / 定理 `mul_num_den'`

English:
theorem mul_num_den'
  given: (q r : Rat)
  proof: by
  let s := q.num * r.num /. (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num]; rw [mul_assoc]; rw [mul_c

中文:
定理 mul_num_den'
  条件: (q r : Rat)
  证明: by
  let s := q.num * r.num /. (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num]; rw [mul_assoc]; rw [mul_c

Depends on / 依赖: Int.mul_assoc, Int.natCast_ne_zero_iff_pos.mpr, Nat.mul_pos, c_mul_den, c_mul_num, divInt_mul_divInt, exists_eq_mul_div_num_and_eq_mul_div_den, mul_assoc, mul_comm, mul_eq_mul_left_iff, mul_pos, natCast_ne_zero_iff_pos, nth_rw, num_divInt_den, or_iff_not_imp_right, q.den, q.num, q.pos, r.den, r.num
-/
theorem mul_num_den' (q r : Rat) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  let s := q.num * r.num /. (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num]; rw [mul_assoc]; rw [mul_comm]
  nth_rw 1 [c_mul_den]
  rw [Int.mul_assoc]; rw [Int.mul_assoc]; rw [mul_eq_mul_left_iff]; rw [or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_mul_divInt q.num r.num
  rw [num_divInt_den]; rw [num_divInt_den] at h
  rw [h]; rw [mul_comm]; rw [← Rat.eq_iff_mul_eq_mul]; rw [← divInt_eq_div]

/--
theorem `add_num_den'` / 定理 `add_num_den'`

English:
theorem add_num_den'
  given: (q r : Rat)
  proof: by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw 

中文:
定理 add_num_den'
  条件: (q r : Rat)
  证明: by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw 

Depends on / 依赖: Int.mul_assoc, Int.natCast_ne_zero_iff_pos.mpr, Nat.mul_pos, c_mul_den, c_mul_num, divInt, divInt_add_divInt, exists_eq_mul_div_num_and_eq_mul_div_den, mod_cast, mul_assoc, mul_comm, mul_eq_mul_left_iff, mul_pos, natCast_ne_zero_iff_pos, nth_rw, or_iff_not_imp_right, q.de, q.den, q.num, q.pos
-/
theorem add_num_den' (q r : Rat) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : Int)
  have hs : (q.den * r.den : Int) != 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw [c_mul_num]; rw [mul_assoc]; rw [mul_comm]
  nth_rw 1 [c_mul_den]
  repeat rw [Int.mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_add_divInt q.num r.num (mod_cast q.den_ne_zero) (mod_cast r.den_ne_zero)
  rw [num_divInt_den]; rw [num_divInt_den] at h
  rw [h]
  rw [mul_comm]
  apply Rat.eq_iff_mul_eq_mul.mp
  rw [← divInt_eq_div]

/--
theorem `substr_num_den'` / 定理 `substr_num_den'`

English:
theorem substr_num_den'
  given: (q r : Rat)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← num_neg_eq_neg_num]; rw [← den_neg_eq_den r]; rw [add_num_den' q (-r)]

中文:
定理 substr_num_den'
  条件: (q r : Rat)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← num_neg_eq_neg_num]; rw [← den_neg_eq_den r]; rw [add_num_den' q (-r)]

Depends on / 依赖: add_num_den, den_neg_eq_den, neg_mul, num_neg_eq_neg_num, sub_eq_add_neg
-/
theorem substr_num_den' (q r : Rat) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← num_neg_eq_neg_num]; rw [← den_neg_eq_den r]; rw [add_num_den' q (-r)]

end Casts

/--
theorem `inv_neg` / 定理 `inv_neg`

English:
theorem inv_neg
  given: (q : Rat)
  statement: (-q)⁻¹ = -q⁻¹
  proof: by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt, Rat.divInt_neg]

中文:
定理 inv_neg
  条件: (q : Rat)
  结论: (-q)⁻¹ = -q⁻¹
  证明: by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt, Rat.divInt_neg]
-/
protected theorem inv_neg (q : Rat) : (-q)⁻¹ = -q⁻¹ := by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt, Rat.divInt_neg]

/--
theorem `num_div_eq_of_coprime` / 定理 `num_div_eq_of_coprime`

English:
theorem num_div_eq_of_coprime
  given: {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs)
  proof: by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

中文:
定理 num_div_eq_of_coprime
  条件: {a b : 整数} (hb0 : 0 < b) (h : 自然数.Coprime a.natAbs b.natAbs)
  证明: by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

Depends on / 依赖: Int.natAbs_natCast, Int.natCast_pos, Rat.divInt_eq_div, divInt_eq_div, hb0.le, hb0.ne, mk_eq_divInt, natAbs_natCast, natCast_pos
-/
theorem num_div_eq_of_coprime {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    (a / b : Rat).num = a := by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

/--
theorem `den_div_eq_of_coprime` / 定理 `den_div_eq_of_coprime`

English:
theorem den_div_eq_of_coprime
  given: {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs)
  proof: by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

中文:
定理 den_div_eq_of_coprime
  条件: {a b : 整数} (hb0 : 0 < b) (h : 自然数.Coprime a.natAbs b.natAbs)
  证明: by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

Depends on / 依赖: Int.natAbs_natCast, Int.natCast_pos, Rat.divInt_eq_div, divInt_eq_div, hb0.le, hb0.ne, mk_eq_divInt, natAbs_natCast, natCast_pos
-/
theorem den_div_eq_of_coprime {a b : Int} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : Rat).den : Int) = b := by
  lift b to Nat using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div]; rw [← mk_eq_divInt (nz := hb0.ne') (c := h)]

/--
theorem `div_int_inj` / 定理 `div_int_inj`

English:
theorem div_int_inj
  statement: {a b c d : Int} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
  proof: by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]

中文:
定理 div_int_inj
  结论: {a b c d : 整数} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : 自然数.Coprime a.natAbs b.natAbs)
  证明: by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]

Depends on / 依赖: And.intro, den_div_eq_of_coprime, num_div_eq_of_coprime
-/
theorem div_int_inj {a b c d : Int} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : Rat) / b = (c : Rat) / d) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]
/--
theorem `intCast_div_self` / 定理 `intCast_div_self`

English:
theorem intCast_div_self
  given: (n : Int)
  statement: ((n / n : Int) : Rat) = n / n
  proof: by
  by_cases hn : n = 0
  · subst hn
    simp
  · have : (n : Rat) != 0 := by rwa [← intCast_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, div_self this]

@[norm_cast]

中文:
定理 intCast_div_self
  条件: (n : 整数)
  结论: ((n / n : 整数) : Rat) = n / n
  证明: by
  by_cases hn : n = 0
  · subst hn
    simp
  · have : (n : Rat) != 0 := by rwa [← intCast_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, div_self this]

@[norm_cast]

Depends on / 依赖: Int.cast_one, Int.ediv_self, cast_one, div_self, ediv_self, intCast_inj
-/
theorem intCast_div_self (n : Int) : ((n / n : Int) : Rat) = n / n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have : (n : Rat) != 0 := by rwa [← intCast_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, div_self this]

@[norm_cast]
/--
theorem `natCast_div_self` / 定理 `natCast_div_self`

English:
theorem natCast_div_self
  given: (n : Nat)
  statement: ((n / n : Nat) : Rat) = n / n
  proof: intCast_div_self n

中文:
定理 natCast_div_self
  条件: (n : 自然数)
  结论: ((n / n : 自然数) : Rat) = n / n
  证明: intCast_div_self n

Depends on / 依赖: intCast_div_self
-/
theorem natCast_div_self (n : Nat) : ((n / n : Nat) : Rat) = n / n :=
  intCast_div_self n

/--
theorem `intCast_div` / 定理 `intCast_div`

English:
theorem intCast_div
  given: (a b : Int) (h : b ∣ a)
  statement: ((a / b : Int) : Rat) = a / b
  proof: by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b]; rw [Int.mul_ediv_assoc c (dvd_refl b)]; rw [Int.cast_mul]; rw [intCast_div_self]; rw [Int.cast_mul]; rw [mul_div_assoc]

中文:
定理 intCast_div
  条件: (a b : 整数) (h : b ∣ a)
  结论: ((a / b : 整数) : Rat) = a / b
  证明: by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b]; rw [Int.mul_ediv_assoc c (dvd_refl b)]; rw [Int.cast_mul]; rw [intCast_div_self]; rw [Int.cast_mul]; rw [mul_div_assoc]

Depends on / 依赖: Int.cast_mul, Int.mul_ediv_assoc, cast_mul, dvd_refl, intCast_div_self, mul_comm, mul_div_assoc, mul_ediv_assoc
-/
theorem intCast_div (a b : Int) (h : b ∣ a) : ((a / b : Int) : Rat) = a / b := by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b]; rw [Int.mul_ediv_assoc c (dvd_refl b)]; rw [Int.cast_mul]; rw [intCast_div_self]; rw [Int.cast_mul]; rw [mul_div_assoc]

/--
theorem `natCast_div` / 定理 `natCast_div`

English:
theorem natCast_div
  given: (a b : Nat) (h : b ∣ a)
  statement: ((a / b : Nat) : Rat) = a / b
  proof: intCast_div a b (Int.ofNat_dvd.mpr h)

中文:
定理 natCast_div
  条件: (a b : 自然数) (h : b ∣ a)
  结论: ((a / b : 自然数) : Rat) = a / b
  证明: intCast_div a b (Int.ofNat_dvd.mpr h)

Depends on / 依赖: Int.ofNat_dvd.mpr, intCast_div, ofNat_dvd
-/
theorem natCast_div (a b : Nat) (h : b ∣ a) : ((a / b : Nat) : Rat) = a / b :=
  intCast_div a b (Int.ofNat_dvd.mpr h)

/--
theorem `den_div_intCast_eq_one_iff` / 定理 `den_div_intCast_eq_one_iff`

English:
theorem den_div_intCast_eq_one_iff
  given: (m n : Int) (hn : n != 0)
  statement: ((m : Rat) / n).den = 1 ↔ n ∣ m
  proof: by
  replace hn : (n : Rat) != 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)

中文:
定理 den_div_intCast_eq_one_iff
  条件: (m n : 整数) (hn : n != 0)
  结论: ((m : Rat) / n).den = 1 ↔ n ∣ m
  证明: by
  replace hn : (n : Rat) != 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)

Depends on / 依赖: Dvd.intro_left, Rat.den_eq_one_iff, den_eq_one_iff, eq_div_iff, intCast_div, intro_left, mod_cast, num_ne_zero, num_ne_zero.mp, replace
-/
theorem den_div_intCast_eq_one_iff (m n : Int) (hn : n != 0) : ((m : Rat) / n).den = 1 ↔ n ∣ m := by
  replace hn : (n : Rat) != 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)

/--
theorem `den_div_natCast_eq_one_iff` / 定理 `den_div_natCast_eq_one_iff`

English:
theorem den_div_natCast_eq_one_iff
  given: (m n : Nat) (hn : n != 0)
  statement: ((m : Rat) / n).den = 1 ↔ n ∣ m
  proof: (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd

中文:
定理 den_div_natCast_eq_one_iff
  条件: (m n : 自然数) (hn : n != 0)
  结论: ((m : Rat) / n).den = 1 ↔ n ∣ m
  证明: (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd

Depends on / 依赖: Int.ofNat_dvd, Int.ofNat_ne_zero.mpr, den_div_intCast_eq_one_iff, ofNat_dvd, ofNat_ne_zero
-/
theorem den_div_natCast_eq_one_iff (m n : Nat) (hn : n != 0) : ((m : Rat) / n).den = 1 ↔ n ∣ m :=
  (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd

/--
theorem `inv_intCast_num_of_pos` / 定理 `inv_intCast_num_of_pos`

English:
theorem inv_intCast_num_of_pos
  given: {a : Int} (ha0 : 0 < a)
  statement: (a : Rat)⁻¹.num = 1
  proof: by
  simp [*]

中文:
定理 inv_intCast_num_of_pos
  条件: {a : 整数} (ha0 : 0 < a)
  结论: (a : Rat)⁻¹.num = 1
  证明: by
  simp [*]
-/
theorem inv_intCast_num_of_pos {a : Int} (ha0 : 0 < a) : (a : Rat)⁻¹.num = 1 := by
  simp [*]

/--
theorem `inv_natCast_num_of_pos` / 定理 `inv_natCast_num_of_pos`

English:
theorem inv_natCast_num_of_pos
  given: {a : Nat} (ha0 : 0 < a)
  statement: (a : Rat)⁻¹.num = 1
  proof: inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : Int))

中文:
定理 inv_natCast_num_of_pos
  条件: {a : 自然数} (ha0 : 0 < a)
  结论: (a : Rat)⁻¹.num = 1
  证明: inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : Int))

Depends on / 依赖: inv_intCast_num_of_pos, mod_cast
-/
theorem inv_natCast_num_of_pos {a : Nat} (ha0 : 0 < a) : (a : Rat)⁻¹.num = 1 :=
  inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : Int))

/--
theorem `inv_intCast_den_of_pos` / 定理 `inv_intCast_den_of_pos`

English:
theorem inv_intCast_den_of_pos
  given: {a : Int} (ha0 : 0 < a)
  statement: ((a : Rat)⁻¹.den : Int) = a
  proof: by
  simp only [den_inv, num_intCast]
  grind

中文:
定理 inv_intCast_den_of_pos
  条件: {a : 整数} (ha0 : 0 < a)
  结论: ((a : Rat)⁻¹.den : 整数) = a
  证明: by
  simp only [den_inv, num_intCast]
  grind

Depends on / 依赖: den_inv, num_intCast
-/
theorem inv_intCast_den_of_pos {a : Int} (ha0 : 0 < a) : ((a : Rat)⁻¹.den : Int) = a := by
  simp only [den_inv, num_intCast]
  grind

/--
theorem `inv_natCast_den_of_pos` / 定理 `inv_natCast_den_of_pos`

English:
theorem inv_natCast_den_of_pos
  given: {a : Nat} (ha0 : 0 < a)
  statement: (a : Rat)⁻¹.den = a
  proof: by
  rw [← Int.ofNat_inj]; rw [← Int.cast_natCast a]; rw [inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]

中文:
定理 inv_natCast_den_of_pos
  条件: {a : 自然数} (ha0 : 0 < a)
  结论: (a : Rat)⁻¹.den = a
  证明: by
  rw [← Int.ofNat_inj]; rw [← Int.cast_natCast a]; rw [inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]

Depends on / 依赖: Int.cast_natCast, Int.natCast_pos, Int.ofNat_inj, cast_natCast, inv_intCast_den_of_pos, natCast_pos, ofNat_inj
-/
theorem inv_natCast_den_of_pos {a : Nat} (ha0 : 0 < a) : (a : Rat)⁻¹.den = a := by
  rw [← Int.ofNat_inj]; rw [← Int.cast_natCast a]; rw [inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]

/--
theorem `inv_intCast_num` / 定理 `inv_intCast_num`

English:
theorem inv_intCast_num
  given: (a : Int)
  statement: (a : Rat)⁻¹.num = Int.sign a
  proof: by simp

中文:
定理 inv_intCast_num
  条件: (a : 整数)
  结论: (a : Rat)⁻¹.num = 整数.sign a
  证明: by simp
-/
theorem inv_intCast_num (a : Int) : (a : Rat)⁻¹.num = Int.sign a := by simp

/--
theorem `inv_natCast_num` / 定理 `inv_natCast_num`

English:
theorem inv_natCast_num
  given: (a : Nat)
  statement: (a : Rat)⁻¹.num = Int.sign a
  proof: by simp

中文:
定理 inv_natCast_num
  条件: (a : 自然数)
  结论: (a : Rat)⁻¹.num = 整数.sign a
  证明: by simp
-/
theorem inv_natCast_num (a : Nat) : (a : Rat)⁻¹.num = Int.sign a := by simp

/--
theorem `inv_ofNat_num` / 定理 `inv_ofNat_num`

English:
theorem inv_ofNat_num
  given: (a : Nat) [a.AtLeastTwo]
  statement: (ofNat(a) : Rat)⁻¹.num = 1
  proof: by
  -- This proof is quite unpleasant: golf / find better simp lemmas?
  have : 2 <= a := Nat.AtLeastTwo.prop
  simp only [num_inv, num_ofNat, den_ofNat, Nat.cast_one, mul_one, Int.sign_eq_one_iff_pos,
    gt_iff_lt]
  change 0 < (a : Int)
  lia

中文:
定理 inv_ofNat_num
  条件: (a : 自然数) [a.AtLeastTwo]
  结论: (of自然数(a) : Rat)⁻¹.num = 1
  证明: by
  -- This proof is quite unpleasant: golf / find better simp lemmas?
  have : 2 <= a := Nat.AtLeastTwo.prop
  simp only [num_inv, num_ofNat, den_ofNat, Nat.cast_one, mul_one, Int.sign_eq_one_iff_pos,
    gt_iff_lt]
  change 0 < (a : Int)
  lia
-/
theorem inv_ofNat_num (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Rat)⁻¹.num = 1 := by
  -- This proof is quite unpleasant: golf / find better simp lemmas?
  have : 2 <= a := Nat.AtLeastTwo.prop
  simp only [num_inv, num_ofNat, den_ofNat, Nat.cast_one, mul_one, Int.sign_eq_one_iff_pos,
    gt_iff_lt]
  change 0 < (a : Int)
  lia

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_intCast_den` / 定理 `inv_intCast_den`

English:
theorem inv_intCast_den
  given: (a : Int)
  statement: (a : Rat)⁻¹.den = if a = 0 then 1 else a.natAbs
  proof: by simp

中文:
定理 inv_intCast_den
  条件: (a : 整数)
  结论: (a : Rat)⁻¹.den = if a = 0 then 1 else a.natAbs
  证明: by simp
-/
theorem inv_intCast_den (a : Int) : (a : Rat)⁻¹.den = if a = 0 then 1 else a.natAbs := by simp

/--
theorem `inv_natCast_den` / 定理 `inv_natCast_den`

English:
theorem inv_natCast_den
  given: (a : Nat)
  statement: (a : Rat)⁻¹.den = if a = 0 then 1 else a
  proof: by simp

中文:
定理 inv_natCast_den
  条件: (a : 自然数)
  结论: (a : Rat)⁻¹.den = if a = 0 then 1 else a
  证明: by simp
-/
theorem inv_natCast_den (a : Nat) : (a : Rat)⁻¹.den = if a = 0 then 1 else a := by simp

/--
theorem `inv_ofNat_den` / 定理 `inv_ofNat_den`

English:
theorem inv_ofNat_den
  given: (a : Nat) [a.AtLeastTwo]
  statement: (ofNat(a) : Rat)⁻¹.den = OfNat.ofNat a
  proof: by
  simp [den_inv, Int.natAbs_eq_iff]

中文:
定理 inv_ofNat_den
  条件: (a : 自然数) [a.AtLeastTwo]
  结论: (of自然数(a) : Rat)⁻¹.den = Of自然数.of自然数 a
  证明: by
  simp [den_inv, Int.natAbs_eq_iff]

Depends on / 依赖: Int.natAbs_eq_iff, den_inv, natAbs_eq_iff
-/
theorem inv_ofNat_den (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Rat)⁻¹.den = OfNat.ofNat a := by
  simp [den_inv, Int.natAbs_eq_iff]

/--
theorem `den_inv_of_ne_zero` / 定理 `den_inv_of_ne_zero`

English:
theorem den_inv_of_ne_zero
  given: {q : Rat} (hq : q != 0)
  statement: (q⁻¹).den = q.num.natAbs
  proof: by
  simp [*]

中文:
定理 den_inv_of_ne_zero
  条件: {q : Rat} (hq : q != 0)
  结论: (q⁻¹).den = q.num.natAbs
  证明: by
  simp [*]
-/
theorem den_inv_of_ne_zero {q : Rat} (hq : q != 0) : (q⁻¹).den = q.num.natAbs := by
  simp [*]

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : Rat -> Prop}
  statement: (forall r, p r) ↔ forall a b : Int, b != 0 -> p (a / b) where
  proof: h _
  mpr h q := by simpa [num_div_den] using h q.num q.den (mod_cast q.den_ne_zero)

中文:
定理 «forall»
  条件: {p : Rat -> 命题}
  结论: (对任意 r, p r) ↔ 对任意 a b : 整数, b != 0 -> p (a / b) where
  证明: h _
  mpr h q := by simpa [num_div_den] using h q.num q.den (mod_cast q.den_ne_zero)
-/
protected theorem «forall» {p : Rat -> Prop} : (forall r, p r) ↔ forall a b : Int, b != 0 -> p (a / b) where
  mp h _ _ _ := h _
  mpr h q := by simpa [num_div_den] using h q.num q.den (mod_cast q.den_ne_zero)

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : Rat -> Prop}
  statement: (exists r, p r) ↔ exists a b : Int, b != 0 ∧ p (a / b)
  proof: by
  simpa using Rat.forall (p := (¬ p ·)).not

中文:
定理 «exists»
  条件: {p : Rat -> 命题}
  结论: (存在 r, p r) ↔ 存在 a b : 整数, b != 0 ∧ p (a / b)
  证明: by
  simpa using Rat.forall (p := (¬ p ·)).not
-/
protected theorem «exists» {p : Rat -> Prop} : (exists r, p r) ↔ exists a b : Int, b != 0 ∧ p (a / b) := by
  simpa using Rat.forall (p := (¬ p ·)).not

/-!
### Denominator as `ℕ+`
-/


section PNatDen

/--
Definition of `pnatDen` / `pnatDen` 的定义

English:
definition pnatDen
  signature: (x : Rat)
  body: ⟨x.den, x.pos⟩

@[simp]

中文:
定义 pnatDen
  签名: (x : Rat)
  定义体: ⟨x.den, x.pos⟩

@[simp]

Depends on / 依赖: x.den, x.pos
-/
def pnatDen (x : Rat) : Nat+ :=
  ⟨x.den, x.pos⟩

@[simp]
/--
theorem `coe_pnatDen` / 定理 `coe_pnatDen`

English:
theorem coe_pnatDen
  given: (x : Rat)
  statement: (x.pnatDen : Nat) = x.den
  proof: rfl

中文:
定理 coe_pnatDen
  条件: (x : Rat)
  结论: (x.pnatDen : 自然数) = x.den
  证明: rfl
-/
theorem coe_pnatDen (x : Rat) : (x.pnatDen : Nat) = x.den :=
  rfl

/--
theorem `pnatDen_eq_iff_den_eq` / 定理 `pnatDen_eq_iff_den_eq`

English:
theorem pnatDen_eq_iff_den_eq
  given: {x : Rat} {n : Nat+}
  statement: x.pnatDen = n ↔ x.den = ↑n
  proof: Subtype.ext_iff

@[simp]

中文:
定理 pnatDen_eq_iff_den_eq
  条件: {x : Rat} {n : 自然数+}
  结论: x.pnatDen = n ↔ x.den = ↑n
  证明: Subtype.ext_iff

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem pnatDen_eq_iff_den_eq {x : Rat} {n : Nat+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff

@[simp]
/--
theorem `pnatDen_one` / 定理 `pnatDen_one`

English:
theorem pnatDen_one
  statement: (1 : Rat).pnatDen = 1
  proof: rfl

@[simp]

中文:
定理 pnatDen_one
  结论: (1 : Rat).pnatDen = 1
  证明: rfl

@[simp]
-/
theorem pnatDen_one : (1 : Rat).pnatDen = 1 :=
  rfl

@[simp]
/--
theorem `pnatDen_zero` / 定理 `pnatDen_zero`

English:
theorem pnatDen_zero
  statement: (0 : Rat).pnatDen = 1
  proof: rfl

中文:
定理 pnatDen_zero
  结论: (0 : Rat).pnatDen = 1
  证明: rfl
-/
theorem pnatDen_zero : (0 : Rat).pnatDen = 1 :=
  rfl

end PNatDen

end Rat
