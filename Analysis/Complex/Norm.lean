/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
  # Norm on the complex numbers
-/

@[expose] public section

noncomputable section

open ComplexConjugate Topology Filter Set

namespace Complex
variable {z : Complex}

@[no_expose]
/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm Complex where
  body: √(normSq z)

中文:
实例 instNorm
  签名: : 范数 复形 where
  定义体: √(normSq z)

Depends on / 依赖: normSq
-/
instance instNorm : Norm Complex where
  norm z := √(normSq z)

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (z : Complex)
  statement: ‖z‖ = √(normSq z)
  proof: (rfl)

中文:
定理 norm_def
  条件: (z : 复形)
  结论: ‖z‖ = √(normSq z)
  证明: (rfl)
-/
theorem norm_def (z : Complex) : ‖z‖ = √(normSq z) := (rfl)

/--
theorem `norm_mul_self_eq_normSq` / 定理 `norm_mul_self_eq_normSq`

English:
theorem norm_mul_self_eq_normSq
  given: (z : Complex)
  statement: ‖z‖ * ‖z‖ = normSq z
  proof: Real.mul_self_sqrt (normSq_nonneg _)

中文:
定理 norm_mul_self_eq_normSq
  条件: (z : 复形)
  结论: ‖z‖ * ‖z‖ = normSq z
  证明: Real.mul_self_sqrt (normSq_nonneg _)

Depends on / 依赖: Real.mul_self_sqrt, mul_self_sqrt, normSq_nonneg
-/
theorem norm_mul_self_eq_normSq (z : Complex) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

/--
theorem `norm_nonneg` / 定理 `norm_nonneg`

English:
theorem norm_nonneg
  given: (z : Complex)
  statement: 0 <= ‖z‖
  proof: Real.sqrt_nonneg _

@[bound]

中文:
定理 norm_nonneg
  条件: (z : 复形)
  结论: 0 <= ‖z‖
  证明: Real.sqrt_nonneg _

@[bound]
-/
protected theorem norm_nonneg (z : Complex) : 0 <= ‖z‖ :=
  Real.sqrt_nonneg _

@[bound]
/--
theorem `abs_re_le_norm` / 定理 `abs_re_le_norm`

English:
theorem abs_re_le_norm
  given: (z : Complex)
  statement: |z.re| <= ‖z‖
  proof: by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (Complex.norm_nonneg _)]; rw [abs_mul_abs_self]; rw [norm_mul_self_eq_normSq]
  apply re_sq_le_normSq

中文:
定理 abs_re_le_norm
  条件: (z : 复形)
  结论: |z.re| <= ‖z‖
  证明: by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (Complex.norm_nonneg _)]; rw [abs_mul_abs_self]; rw [norm_mul_self_eq_normSq]
  apply re_sq_le_normSq

Depends on / 依赖: Complex.norm_nonneg, abs_mul_abs_self, abs_nonneg, mul_self_le_mul_self_iff, norm_mul_self_eq_normSq, norm_nonneg, re_sq_le_normSq, z.re
-/
theorem abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (Complex.norm_nonneg _)]; rw [abs_mul_abs_self]; rw [norm_mul_self_eq_normSq]
  apply re_sq_le_normSq

/--
theorem `re_le_norm` / 定理 `re_le_norm`

English:
theorem re_le_norm
  given: (z : Complex)
  statement: z.re <= ‖z‖
  proof: (abs_le.1 (abs_re_le_norm _)).2

中文:
定理 re_le_norm
  条件: (z : 复形)
  结论: z.re <= ‖z‖
  证明: (abs_le.1 (abs_re_le_norm _)).2

Depends on / 依赖: abs_le, abs_re_le_norm
-/
theorem re_le_norm (z : Complex) : z.re <= ‖z‖ :=
  (abs_le.1 (abs_re_le_norm _)).2

/--
theorem `norm_add_le'` / 定理 `norm_add_le'`

English:
theorem norm_add_le'
  given: (z w : Complex)
  statement: ‖z + w‖ <= ‖z‖ + ‖w‖
  proof: (mul_self_le_mul_self_iff (Complex.norm_nonneg (z + w)) (add_nonneg (Complex.norm_nonneg z)
    (Complex.norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq]; rw [add_mul_self_eq]; rw [norm_mul_self_eq_normSq]; rw [norm_mul_self_eq_normSq]; rw [add_right_comm]; rw [normSq_add]; rw [mul_assoc]; 

中文:
定理 norm_add_le'
  条件: (z w : 复形)
  结论: ‖z + w‖ <= ‖z‖ + ‖w‖
  证明: (mul_self_le_mul_self_iff (Complex.norm_nonneg (z + w)) (add_nonneg (Complex.norm_nonneg z)
    (Complex.norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq]; rw [add_mul_self_eq]; rw [norm_mul_self_eq_normSq]; rw [norm_mul_self_eq_normSq]; rw [add_right_comm]; rw [normSq_add]; rw [mul_assoc]; 
-/
protected theorem norm_add_le' (z w : Complex) : ‖z + w‖ <= ‖z‖ + ‖w‖ :=
  (mul_self_le_mul_self_iff (Complex.norm_nonneg (z + w)) (add_nonneg (Complex.norm_nonneg z)
    (Complex.norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq]; rw [add_mul_self_eq]; rw [norm_mul_self_eq_normSq]; rw [norm_mul_self_eq_normSq]; rw [add_right_comm]; rw [normSq_add]; rw [mul_assoc]; rw [norm_def]; rw [norm_def]; rw [← Real.sqrt_mul normSq_nonneg z]; rw [← normSq_conj w]; rw [← map_mul]
    gcongr
    exact re_le_norm (z * conj w)

/--
theorem `norm_eq_zero_iff` / 定理 `norm_eq_zero_iff`

English:
theorem norm_eq_zero_iff
  given: {z : Complex}
  statement: ‖z‖ = 0 ↔ z = 0
  proof: (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero

中文:
定理 norm_eq_zero_iff
  条件: {z : 复形}
  结论: ‖z‖ = 0 ↔ z = 0
  证明: (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero
-/
protected theorem norm_eq_zero_iff {z : Complex} : ‖z‖ = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero

/--
theorem `norm_map_zero'` / 定理 `norm_map_zero'`

English:
theorem norm_map_zero'
  statement: ‖(0 : Complex)‖ = 0
  proof: Complex.norm_eq_zero_iff.mpr rfl

中文:
定理 norm_map_zero'
  结论: ‖(0 : 复形)‖ = 0
  证明: Complex.norm_eq_zero_iff.mpr rfl
-/
protected theorem norm_map_zero' : ‖(0 : Complex)‖ = 0 :=
  Complex.norm_eq_zero_iff.mpr rfl

/--
theorem `norm_neg'` / 定理 `norm_neg'`

English:
theorem norm_neg'
  given: (z : Complex)
  statement: ‖-z‖ = ‖z‖
  proof: by
  rw [Complex.norm_def]; rw [norm_def]; rw [normSq_neg]

中文:
定理 norm_neg'
  条件: (z : 复形)
  结论: ‖-z‖ = ‖z‖
  证明: by
  rw [Complex.norm_def]; rw [norm_def]; rw [normSq_neg]
-/
protected theorem norm_neg' (z : Complex) : ‖-z‖ = ‖z‖ := by
  rw [Complex.norm_def]; rw [norm_def]; rw [normSq_neg]

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: : NormedAddCommGroup Complex
  body: AddGroupNorm.toNormedAddCommGroup
  { toFun := norm
    map_zero' := Complex.norm_map_zero'
    add_le' := Complex.norm_add_le'
    neg' := Complex.norm_neg'
    eq_zero_of_map_eq_zero' := fun _ => Complex.norm_eq_zero_iff.mp }

@[simp 1100]

中文:
实例 instNormedAddCommGroup
  签名: : 赋范交换加群 复形
  定义体: AddGroupNorm.toNormedAddCommGroup
  { toFun := norm
    map_zero' := Complex.norm_map_zero'
    add_le' := Complex.norm_add_le'
    neg' := Complex.norm_neg'
    eq_zero_of_map_eq_zero' := fun _ => Complex.norm_eq_zero_iff.mp }

@[simp 1100]

Depends on / 依赖: AddGroupNorm, AddGroupNorm.toNormedAddCommGroup, Complex.norm_add_le, Complex.norm_eq_zero_iff.mp, Complex.norm_map_zero, Complex.norm_neg, add_le, eq_zero_of_map_eq_zero, map_zero, norm_add_le, norm_eq_zero_iff, norm_map_zero, norm_neg, toNormedAddCommGroup
-/
instance instNormedAddCommGroup : NormedAddCommGroup Complex :=
  AddGroupNorm.toNormedAddCommGroup
  { toFun := norm
    map_zero' := Complex.norm_map_zero'
    add_le' := Complex.norm_add_le'
    neg' := Complex.norm_neg'
    eq_zero_of_map_eq_zero' := fun _ => Complex.norm_eq_zero_iff.mp }

@[simp 1100]
/--
theorem `norm_mul` / 定理 `norm_mul`

English:
theorem norm_mul
  given: (z w : Complex)
  statement: ‖z * w‖ = ‖z‖ * ‖w‖
  proof: by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_mul]; rw [Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]

中文:
定理 norm_mul
  条件: (z w : 复形)
  结论: ‖z * w‖ = ‖z‖ * ‖w‖
  证明: by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_mul]; rw [Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]
-/
protected theorem norm_mul (z w : Complex) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_mul]; rw [Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]
/--
theorem `norm_div` / 定理 `norm_div`

English:
theorem norm_div
  given: (z w : Complex)
  statement: ‖z / w‖ = ‖z‖ / ‖w‖
  proof: by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_div]; rw [Real.sqrt_div (normSq_nonneg _)]

中文:
定理 norm_div
  条件: (z w : 复形)
  结论: ‖z / w‖ = ‖z‖ / ‖w‖
  证明: by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_div]; rw [Real.sqrt_div (normSq_nonneg _)]
-/
protected theorem norm_div (z w : Complex) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
  rw [norm_def]; rw [norm_def]; rw [norm_def]; rw [normSq_div]; rw [Real.sqrt_div (normSq_nonneg _)]

/--
Instance `isAbsoluteValueNorm` / 实例 `isAbsoluteValueNorm`

English:
instance isAbsoluteValueNorm
  signature: : IsAbsoluteValue (‖·‖ : Complex -> Real) where
  body: norm_nonneg
  abv_eq_zero' := Complex.norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul

中文:
实例 isAbsoluteValueNorm
  签名: : 是绝对值 (‖·‖ : 复形 -> 实数) where
  定义体: norm_nonneg
  abv_eq_zero' := Complex.norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul

Depends on / 依赖: norm_nonneg
-/
instance isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : Complex -> Real) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := Complex.norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul

/--
theorem `norm_pow` / 定理 `norm_pow`

English:
theorem norm_pow
  given: (z : Complex) (n : Nat)
  statement: ‖z ^ n‖ = ‖z‖ ^ n
  proof: map_pow isAbsoluteValueNorm.abvHom _ _

中文:
定理 norm_pow
  条件: (z : 复形) (n : 自然数)
  结论: ‖z ^ n‖ = ‖z‖ ^ n
  证明: map_pow isAbsoluteValueNorm.abvHom _ _
-/
protected theorem norm_pow (z : Complex) (n : Nat) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_pow isAbsoluteValueNorm.abvHom _ _

/--
theorem `norm_zpow` / 定理 `norm_zpow`

English:
theorem norm_zpow
  given: (z : Complex) (n : Int)
  statement: ‖z ^ n‖ = ‖z‖ ^ n
  proof: map_zpow₀ isAbsoluteValueNorm.abvHom _ _

中文:
定理 norm_zpow
  条件: (z : 复形) (n : 整数)
  结论: ‖z ^ n‖ = ‖z‖ ^ n
  证明: map_zpow₀ isAbsoluteValueNorm.abvHom _ _
-/
protected theorem norm_zpow (z : Complex) (n : Int) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_zpow₀ isAbsoluteValueNorm.abvHom _ _

/--
theorem `norm_prod` / 定理 `norm_prod`

English:
theorem norm_prod
  given: {ι : Type*} (s : Finset ι) (f : ι -> Complex)
  proof: map_prod isAbsoluteValueNorm.abvHom _ _

中文:
定理 norm_prod
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 复形)
  证明: map_prod isAbsoluteValueNorm.abvHom _ _
-/
protected theorem norm_prod {ι : Type*} (s : Finset ι) (f : ι -> Complex) :
    ‖s.prod f‖ = s.prod fun i => ‖f i‖ :=
  map_prod isAbsoluteValueNorm.abvHom _ _

/--
theorem `norm_conj` / 定理 `norm_conj`

English:
theorem norm_conj
  given: (z : Complex)
  statement: ‖conj z‖ = ‖z‖
  proof: by simp [norm_def]

中文:
定理 norm_conj
  条件: (z : 复形)
  结论: ‖conj z‖ = ‖z‖
  证明: by simp [norm_def]

Depends on / 依赖: norm_def
-/
theorem norm_conj (z : Complex) : ‖conj z‖ = ‖z‖ := by simp [norm_def]

/--
lemma `norm_I` / 引理 `norm_I`

English:
lemma norm_I
  statement: ‖I‖ = 1
  proof: by simp [norm]

中文:
引理 norm_I
  结论: ‖I‖ = 1
  证明: by simp [norm]
-/
@[simp] lemma norm_I : ‖I‖ = 1 := by simp [norm]

/--
lemma `nnnorm_I` / 引理 `nnnorm_I`

English:
lemma nnnorm_I
  statement: ‖I‖₊ = 1
  proof: by simp [nnnorm]

@[simp 1100, norm_cast]

中文:
引理 nnnorm_I
  结论: ‖I‖₊ = 1
  证明: by simp [nnnorm]

@[simp 1100, norm_cast]
-/
@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

@[simp 1100, norm_cast]
/--
lemma `norm_real` / 引理 `norm_real`

English:
lemma norm_real
  given: (r : Real)
  statement: ‖(r : Complex)‖ = ‖r‖
  proof: by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

中文:
引理 norm_real
  条件: (r : 实数)
  结论: ‖(r : 复形)‖ = ‖r‖
  证明: by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

Depends on / 依赖: Real.sqrt_mul_self_eq_abs, norm_def, sqrt_mul_self_eq_abs
-/
lemma norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖ := by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]

/--
theorem `norm_of_nonneg` / 定理 `norm_of_nonneg`

English:
theorem norm_of_nonneg
  given: {r : Real} (h : 0 <= r)
  statement: ‖(r : Complex)‖ = r
  proof: (norm_real _).trans (abs_of_nonneg h)

@[simp, norm_cast]

中文:
定理 norm_of_nonneg
  条件: {r : 实数} (h : 0 <= r)
  结论: ‖(r : 复形)‖ = r
  证明: (norm_real _).trans (abs_of_nonneg h)

@[simp, norm_cast]
-/
protected theorem norm_of_nonneg {r : Real} (h : 0 <= r) : ‖(r : Complex)‖ = r :=
  (norm_real _).trans (abs_of_nonneg h)

@[simp, norm_cast]
/--
lemma `nnnorm_real` / 引理 `nnnorm_real`

English:
lemma nnnorm_real
  given: (r : Real)
  statement: ‖(r : Complex)‖₊ = ‖r‖₊
  proof: by ext; exact norm_real _

@[norm_cast]

中文:
引理 nnnorm_real
  条件: (r : 实数)
  结论: ‖(r : 复形)‖₊ = ‖r‖₊
  证明: by ext; exact norm_real _

@[norm_cast]

Depends on / 依赖: norm_real
-/
lemma nnnorm_real (r : Real) : ‖(r : Complex)‖₊ = ‖r‖₊ := by ext; exact norm_real _

@[norm_cast]
/--
lemma `norm_natCast` / 引理 `norm_natCast`

English:
lemma norm_natCast
  given: (n : Nat)
  statement: ‖(n : Complex)‖ = n
  proof: Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]

中文:
引理 norm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 复形)‖ = n
  证明: Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]

Depends on / 依赖: Complex.norm_of_nonneg, cast_nonneg, n.cast_nonneg, norm_of_nonneg
-/
lemma norm_natCast (n : Nat) : ‖(n : Complex)‖ = n := Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]
/--
lemma `norm_ofNat` / 引理 `norm_ofNat`

English:
lemma norm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: norm_natCast n

中文:
引理 norm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: norm_natCast n

Depends on / 依赖: norm_natCast
-/
lemma norm_ofNat (n : Nat) [n.AtLeastTwo] :
    ‖(ofNat(n) : Complex)‖ = OfNat.ofNat n := norm_natCast n

/--
lemma `norm_two` / 引理 `norm_two`

English:
lemma norm_two
  statement: ‖(2 : Complex)‖ = 2
  proof: norm_ofNat 2

@[simp 1100, norm_cast]

中文:
引理 norm_two
  结论: ‖(2 : 复形)‖ = 2
  证明: norm_ofNat 2

@[simp 1100, norm_cast]
-/
protected lemma norm_two : ‖(2 : Complex)‖ = 2 := norm_ofNat 2

@[simp 1100, norm_cast]
/--
lemma `nnnorm_natCast` / 引理 `nnnorm_natCast`

English:
lemma nnnorm_natCast
  given: (n : Nat)
  statement: ‖(n : Complex)‖₊ = n
  proof: Subtype.ext by simp [norm_natCast]

@[simp 1100]

中文:
引理 nnnorm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 复形)‖₊ = n
  证明: Subtype.ext by simp [norm_natCast]

@[simp 1100]

Depends on / 依赖: Subtype, Subtype.ext, norm_natCast
-/
lemma nnnorm_natCast (n : Nat) : ‖(n : Complex)‖₊ = n := Subtype.ext by simp [norm_natCast]

@[simp 1100]
/--
lemma `nnnorm_ofNat` / 引理 `nnnorm_ofNat`

English:
lemma nnnorm_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: nnnorm_natCast n

@[simp 1100, norm_cast]

中文:
引理 nnnorm_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: nnnorm_natCast n

@[simp 1100, norm_cast]

Depends on / 依赖: nnnorm_natCast
-/
lemma nnnorm_ofNat (n : Nat) [n.AtLeastTwo] :
    ‖(ofNat(n) : Complex)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[simp 1100, norm_cast]
/--
lemma `norm_intCast` / 引理 `norm_intCast`

English:
lemma norm_intCast
  given: (n : Int)
  statement: ‖(n : Complex)‖ = |(n : Real)|
  proof: by
  rw [← ofReal_intCast]; rw [norm_real]; rw [Real.norm_eq_abs]

中文:
引理 norm_intCast
  条件: (n : 整数)
  结论: ‖(n : 复形)‖ = |(n : 实数)|
  证明: by
  rw [← ofReal_intCast]; rw [norm_real]; rw [Real.norm_eq_abs]

Depends on / 依赖: Real.norm_eq_abs, norm_eq_abs, norm_real, ofReal_intCast
-/
lemma norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : Real)| := by
  rw [← ofReal_intCast]; rw [norm_real]; rw [Real.norm_eq_abs]

/--
theorem `norm_int_of_nonneg` / 定理 `norm_int_of_nonneg`

English:
theorem norm_int_of_nonneg
  given: {n : Int} (hn : 0 <= n)
  statement: ‖(n : Complex)‖ = n
  proof: by
  rw [norm_intCast]; rw [← Int.cast_abs]; rw [abs_of_nonneg hn]

@[simp 1100, norm_cast]

中文:
定理 norm_int_of_nonneg
  条件: {n : 整数} (hn : 0 <= n)
  结论: ‖(n : 复形)‖ = n
  证明: by
  rw [norm_intCast]; rw [← Int.cast_abs]; rw [abs_of_nonneg hn]

@[simp 1100, norm_cast]

Depends on / 依赖: Int.cast_abs, abs_of_nonneg, cast_abs, norm_intCast
-/
theorem norm_int_of_nonneg {n : Int} (hn : 0 <= n) : ‖(n : Complex)‖ = n := by
  rw [norm_intCast]; rw [← Int.cast_abs]; rw [abs_of_nonneg hn]

@[simp 1100, norm_cast]
/--
lemma `norm_ratCast` / 引理 `norm_ratCast`

English:
lemma norm_ratCast
  given: (q : Rat)
  statement: ‖(q : Complex)‖ = |(q : Real)|
  proof: norm_real _

@[simp 1100, norm_cast]

中文:
引理 norm_ratCast
  条件: (q : 有理数)
  结论: ‖(q : 复形)‖ = |(q : 实数)|
  证明: norm_real _

@[simp 1100, norm_cast]

Depends on / 依赖: norm_real
-/
lemma norm_ratCast (q : Rat) : ‖(q : Complex)‖ = |(q : Real)| := norm_real _

@[simp 1100, norm_cast]
/--
lemma `norm_nnratCast` / 引理 `norm_nnratCast`

English:
lemma norm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : Complex)‖ = q
  proof: Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]

中文:
引理 norm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : 复形)‖ = q
  证明: Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]

Depends on / 依赖: Complex.norm_of_nonneg, cast_nonneg, norm_of_nonneg, q.cast_nonneg
-/
lemma norm_nnratCast (q : Rat>=0) : ‖(q : Complex)‖ = q := Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
/--
lemma `nnnorm_ratCast` / 引理 `nnnorm_ratCast`

English:
lemma nnnorm_ratCast
  given: (q : Rat)
  statement: ‖(q : Complex)‖₊ = ‖(q : Real)‖₊
  proof: nnnorm_real q

@[simp 1100, norm_cast]

中文:
引理 nnnorm_ratCast
  条件: (q : 有理数)
  结论: ‖(q : 复形)‖₊ = ‖(q : 实数)‖₊
  证明: nnnorm_real q

@[simp 1100, norm_cast]

Depends on / 依赖: nnnorm_real
-/
lemma nnnorm_ratCast (q : Rat) : ‖(q : Complex)‖₊ = ‖(q : Real)‖₊ := nnnorm_real q

@[simp 1100, norm_cast]
/--
lemma `nnnorm_nnratCast` / 引理 `nnnorm_nnratCast`

English:
lemma nnnorm_nnratCast
  given: (q : Rat>=0)
  statement: ‖(q : Complex)‖₊ = q
  proof: by simp [nnnorm]; rfl

中文:
引理 nnnorm_nnratCast
  条件: (q : 有理数>=0)
  结论: ‖(q : 复形)‖₊ = q
  证明: by simp [nnnorm]; rfl

Depends on / 依赖: nnnorm
-/
lemma nnnorm_nnratCast (q : Rat>=0) : ‖(q : Complex)‖₊ = q := by simp [nnnorm]; rfl

/--
lemma `normSq_eq_norm_sq` / 引理 `normSq_eq_norm_sq`

English:
lemma normSq_eq_norm_sq
  given: (z : Complex)
  statement: normSq z = ‖z‖ ^ 2
  proof: by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]

中文:
引理 normSq_eq_norm_sq
  条件: (z : 复形)
  结论: normSq z = ‖z‖ ^ 2
  证明: by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]

Depends on / 依赖: Real.mul_self_sqrt, mul_self_sqrt, normSq_nonneg, norm_def
-/
lemma normSq_eq_norm_sq (z : Complex) : normSq z = ‖z‖ ^ 2 := by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]

/--
theorem `sq_norm` / 定理 `sq_norm`

English:
theorem sq_norm
  given: (z : Complex)
  statement: ‖z‖ ^ 2 = normSq z
  proof: (normSq_eq_norm_sq z).symm

中文:
定理 sq_norm
  条件: (z : 复形)
  结论: ‖z‖ ^ 2 = normSq z
  证明: (normSq_eq_norm_sq z).symm
-/
protected theorem sq_norm (z : Complex) : ‖z‖ ^ 2 = normSq z := (normSq_eq_norm_sq z).symm

/--
lemma `one_lt_normSq_iff` / 引理 `one_lt_normSq_iff`

English:
lemma one_lt_normSq_iff
  given: {x : Complex}
  statement: 1 < normSq x ↔ 1 < ‖x‖
  proof: by
  rw [← one_lt_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

中文:
引理 one_lt_normSq_iff
  条件: {x : 复形}
  结论: 1 < normSq x ↔ 1 < ‖x‖
  证明: by
  rw [← one_lt_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

Depends on / 依赖: normSq_eq_norm_sq, norm_nonneg
-/
lemma one_lt_normSq_iff {x : Complex} : 1 < normSq x ↔ 1 < ‖x‖ := by
  rw [← one_lt_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

/--
lemma `one_le_normSq_iff` / 引理 `one_le_normSq_iff`

English:
lemma one_le_normSq_iff
  given: {x : Complex}
  statement: 1 <= normSq x ↔ 1 <= ‖x‖
  proof: by
  rw [← one_le_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

@[simp]

中文:
引理 one_le_normSq_iff
  条件: {x : 复形}
  结论: 1 <= normSq x ↔ 1 <= ‖x‖
  证明: by
  rw [← one_le_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

@[simp]

Depends on / 依赖: normSq_eq_norm_sq, norm_nonneg
-/
lemma one_le_normSq_iff {x : Complex} : 1 <= normSq x ↔ 1 <= ‖x‖ := by
  rw [← one_le_sq_iff₀ (norm_nonneg _)]; rw [normSq_eq_norm_sq]

@[simp]
/--
theorem `sq_norm_sub_sq_re` / 定理 `sq_norm_sub_sq_re`

English:
theorem sq_norm_sub_sq_re
  given: (z : Complex)
  statement: ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2
  proof: by
  rw [Complex.sq_norm]; rw [normSq_apply]; rw [← sq]; rw [← sq]; rw [add_sub_cancel_left]

@[simp]

中文:
定理 sq_norm_sub_sq_re
  条件: (z : 复形)
  结论: ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2
  证明: by
  rw [Complex.sq_norm]; rw [normSq_apply]; rw [← sq]; rw [← sq]; rw [add_sub_cancel_left]

@[simp]

Depends on / 依赖: Complex.sq_norm, add_sub_cancel_left, normSq_apply, sq_norm
-/
theorem sq_norm_sub_sq_re (z : Complex) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [Complex.sq_norm]; rw [normSq_apply]; rw [← sq]; rw [← sq]; rw [add_sub_cancel_left]

@[simp]
/--
theorem `sq_norm_sub_sq_im` / 定理 `sq_norm_sub_sq_im`

English:
theorem sq_norm_sub_sq_im
  given: (z : Complex)
  statement: ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2
  proof: by
  rw [← sq_norm_sub_sq_re]; rw [sub_sub_cancel]

中文:
定理 sq_norm_sub_sq_im
  条件: (z : 复形)
  结论: ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2
  证明: by
  rw [← sq_norm_sub_sq_re]; rw [sub_sub_cancel]

Depends on / 依赖: sq_norm_sub_sq_re, sub_sub_cancel
-/
theorem sq_norm_sub_sq_im (z : Complex) : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_norm_sub_sq_re]; rw [sub_sub_cancel]

/--
lemma `norm_add_mul_I` / 引理 `norm_add_mul_I`

English:
lemma norm_add_mul_I
  given: (x y : Real)
  statement: ‖x + y * I‖ = √(x ^ 2 + y ^ 2)
  proof: by
  rw [← normSq_add_mul_I]; rfl

中文:
引理 norm_add_mul_I
  条件: (x y : 实数)
  结论: ‖x + y * I‖ = √(x ^ 2 + y ^ 2)
  证明: by
  rw [← normSq_add_mul_I]; rfl

Depends on / 依赖: normSq_add_mul_I
-/
lemma norm_add_mul_I (x y : Real) : ‖x + y * I‖ = √(x ^ 2 + y ^ 2) := by
  rw [← normSq_add_mul_I]; rfl

/--
lemma `norm_eq_sqrt_sq_add_sq` / 引理 `norm_eq_sqrt_sq_add_sq`

English:
lemma norm_eq_sqrt_sq_add_sq
  given: (z : Complex)
  statement: ‖z‖ = √(z.re ^ 2 + z.im ^ 2)
  proof: by
  rw [norm_def]; rw [normSq_apply]; rw [sq]; rw [sq]

@[simp 1100]

中文:
引理 norm_eq_sqrt_sq_add_sq
  条件: (z : 复形)
  结论: ‖z‖ = √(z.re ^ 2 + z.im ^ 2)
  证明: by
  rw [norm_def]; rw [normSq_apply]; rw [sq]; rw [sq]

@[simp 1100]

Depends on / 依赖: normSq_apply, norm_def
-/
lemma norm_eq_sqrt_sq_add_sq (z : Complex) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
  rw [norm_def]; rw [normSq_apply]; rw [sq]; rw [sq]

@[simp 1100]
/--
theorem `range_norm` / 定理 `range_norm`

English:
theorem range_norm
  statement: range (‖·‖ : Complex -> Real) = Set.Ici 0
  proof: Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx => ⟨x, Complex.norm_of_nonneg hx⟩

@[simp]

中文:
定理 range_norm
  结论: range (‖·‖ : 复形 -> 实数) = 集合.左闭右无界区间 0
  证明: Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx => ⟨x, Complex.norm_of_nonneg hx⟩

@[simp]
-/
protected theorem range_norm : range (‖·‖ : Complex -> Real) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx => ⟨x, Complex.norm_of_nonneg hx⟩

@[simp]
/--
theorem `range_normSq` / 定理 `range_normSq`

English:
theorem range_normSq
  statement: range normSq = Ici 0
  proof: Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨√x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

中文:
定理 range_normSq
  结论: range normSq = 左闭右无界区间 0
  证明: Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨√x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

Depends on / 依赖: Real.mul_self_sqrt, Subset, Subset.antisymm, antisymm, mul_self_sqrt, normSq_nonneg, normSq_ofReal, range_subset_iff
-/
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨√x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

/--
theorem `norm_le_abs_re_add_abs_im` / 定理 `norm_le_abs_re_add_abs_im`

English:
theorem norm_le_abs_re_add_abs_im
  given: (z : Complex)
  statement: ‖z‖ <= |z.re| + |z.im|
  proof: by
    simpa [re_add_im] using norm_add_le (z.re : Complex) (z.im * I)

@[bound]

中文:
定理 norm_le_abs_re_add_abs_im
  条件: (z : 复形)
  结论: ‖z‖ <= |z.re| + |z.im|
  证明: by
    simpa [re_add_im] using norm_add_le (z.re : Complex) (z.im * I)

@[bound]

Depends on / 依赖: norm_add_le, re_add_im, z.im, z.re
-/
theorem norm_le_abs_re_add_abs_im (z : Complex) : ‖z‖ <= |z.re| + |z.im| := by
    simpa [re_add_im] using norm_add_le (z.re : Complex) (z.im * I)

@[bound]
/--
theorem `abs_im_le_norm` / 定理 `abs_im_le_norm`

English:
theorem abs_im_le_norm
  given: (z : Complex)
  statement: |z.im| <= ‖z‖
  proof: Real.abs_le_sqrt by
    rw [normSq_apply]; rw [← sq]; rw [← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

中文:
定理 abs_im_le_norm
  条件: (z : 复形)
  结论: |z.im| <= ‖z‖
  证明: Real.abs_le_sqrt by
    rw [normSq_apply]; rw [← sq]; rw [← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

Depends on / 依赖: Real.abs_le_sqrt, abs_le_sqrt, le_add_of_nonneg_left, normSq_apply, sq_nonneg
-/
theorem abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖ :=
Real.abs_le_sqrt by
    rw [normSq_apply]; rw [← sq]; rw [← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

/--
theorem `im_le_norm` / 定理 `im_le_norm`

English:
theorem im_le_norm
  given: (z : Complex)
  statement: z.im <= ‖z‖
  proof: (abs_le.1 (abs_im_le_norm _)).2

@[simp]

中文:
定理 im_le_norm
  条件: (z : 复形)
  结论: z.im <= ‖z‖
  证明: (abs_le.1 (abs_im_le_norm _)).2

@[simp]

Depends on / 依赖: abs_im_le_norm, abs_le
-/
theorem im_le_norm (z : Complex) : z.im <= ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

@[simp]
/--
theorem `abs_re_lt_norm` / 定理 `abs_re_lt_norm`

English:
theorem abs_re_lt_norm
  given: {z : Complex}
  statement: |z.re| < ‖z‖ ↔ z.im != 0
  proof: by
  rw [norm_def]; rw [Real.lt_sqrt (abs_nonneg _)]; rw [normSq_apply]; rw [sq_abs]; rw [← sq]; rw [lt_add_iff_pos_right]; rw [mul_self_pos]

@[simp]

中文:
定理 abs_re_lt_norm
  条件: {z : 复形}
  结论: |z.re| < ‖z‖ ↔ z.im != 0
  证明: by
  rw [norm_def]; rw [Real.lt_sqrt (abs_nonneg _)]; rw [normSq_apply]; rw [sq_abs]; rw [← sq]; rw [lt_add_iff_pos_right]; rw [mul_self_pos]

@[simp]

Depends on / 依赖: Real.lt_sqrt, abs_nonneg, lt_add_iff_pos_right, lt_sqrt, mul_self_pos, normSq_apply, norm_def, sq_abs
-/
theorem abs_re_lt_norm {z : Complex} : |z.re| < ‖z‖ ↔ z.im != 0 := by
  rw [norm_def]; rw [Real.lt_sqrt (abs_nonneg _)]; rw [normSq_apply]; rw [sq_abs]; rw [← sq]; rw [lt_add_iff_pos_right]; rw [mul_self_pos]

@[simp]
/--
theorem `abs_im_lt_norm` / 定理 `abs_im_lt_norm`

English:
theorem abs_im_lt_norm
  given: {z : Complex}
  statement: |z.im| < ‖z‖ ↔ z.re != 0
  proof: by
  simpa using @abs_re_lt_norm (z * I)

@[simp]

中文:
定理 abs_im_lt_norm
  条件: {z : 复形}
  结论: |z.im| < ‖z‖ ↔ z.re != 0
  证明: by
  simpa using @abs_re_lt_norm (z * I)

@[simp]

Depends on / 依赖: abs_re_lt_norm
-/
theorem abs_im_lt_norm {z : Complex} : |z.im| < ‖z‖ ↔ z.re != 0 := by
  simpa using @abs_re_lt_norm (z * I)

@[simp]
/--
lemma `abs_re_eq_norm` / 引理 `abs_re_eq_norm`

English:
lemma abs_re_eq_norm
  given: {z : Complex}
  statement: |z.re| = ‖z‖ ↔ z.im = 0
  proof: not_iff_not.1 (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]

中文:
引理 abs_re_eq_norm
  条件: {z : 复形}
  结论: |z.re| = ‖z‖ ↔ z.im = 0
  证明: not_iff_not.1 (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]

Depends on / 依赖: abs_re_le_norm, abs_re_lt_norm, lt_iff_ne, lt_iff_ne.symm.trans, not_iff_not
-/
lemma abs_re_eq_norm {z : Complex} : |z.re| = ‖z‖ ↔ z.im = 0 :=
not_iff_not.1 (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]
/--
lemma `abs_im_eq_norm` / 引理 `abs_im_eq_norm`

English:
lemma abs_im_eq_norm
  given: {z : Complex}
  statement: |z.im| = ‖z‖ ↔ z.re = 0
  proof: not_iff_not.1 (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm

中文:
引理 abs_im_eq_norm
  条件: {z : 复形}
  结论: |z.im| = ‖z‖ ↔ z.re = 0
  证明: not_iff_not.1 (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm

Depends on / 依赖: abs_im_le_norm, abs_im_lt_norm, lt_iff_ne, lt_iff_ne.symm.trans, not_iff_not
-/
lemma abs_im_eq_norm {z : Complex} : |z.im| = ‖z‖ ↔ z.re = 0 :=
not_iff_not.1 (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm

/--
theorem `norm_le_sqrt_two_mul_max` / 定理 `norm_le_sqrt_two_mul_max`

English:
theorem norm_le_sqrt_two_mul_max
  given: (z : Complex)
  statement: ‖z‖ <= √2 * max |z.re| |z.im|
  proof: by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  set m := max |x| |y|
  have hm₀ : 0 <= m := by positivity
  calc
    √(x ^ 2 + y ^ 2) <= √(m ^ 2 + m ^ 2) := by
      gcongr √(?_ + ?_) <;> rw [sq_le_sq, abs_of_nonneg hm₀]
      exacts [le_max_left _ _, le_max_right _ _]
  

中文:
定理 norm_le_sqrt_two_mul_max
  条件: (z : 复形)
  结论: ‖z‖ <= √2 * 最大值 |z.re| |z.im|
  证明: by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  set m := max |x| |y|
  have hm₀ : 0 <= m := by positivity
  calc
    √(x ^ 2 + y ^ 2) <= √(m ^ 2 + m ^ 2) := by
      gcongr √(?_ + ?_) <;> rw [sq_le_sq, abs_of_nonneg hm₀]
      exacts [le_max_left _ _, le_max_right _ _]
  

Depends on / 依赖: Real.sqrt_mul, Real.sqrt_sq, abs_of_nonneg, exacts, le_max_left, le_max_right, normSq_mk, norm_def, sq_le_sq, sqrt_mul, sqrt_sq, two_mul
-/
theorem norm_le_sqrt_two_mul_max (z : Complex) : ‖z‖ <= √2 * max |z.re| |z.im| := by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  set m := max |x| |y|
  have hm₀ : 0 <= m := by positivity
  calc
    √(x ^ 2 + y ^ 2) <= √(m ^ 2 + m ^ 2) := by
      gcongr √(?_ + ?_) <;> rw [sq_le_sq, abs_of_nonneg hm₀]
      exacts [le_max_left _ _, le_max_right _ _]
    _ = √2 * m := by
      rw [← two_mul]; rw [Real.sqrt_mul]; rw [Real.sqrt_sq] <;> positivity

/--
theorem `abs_re_div_norm_le_one` / 定理 `abs_re_div_norm_le_one`

English:
theorem abs_re_div_norm_le_one
  given: (z : Complex)
  statement: |z.re / ‖z‖| <= 1
  proof: if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]

中文:
定理 abs_re_div_norm_le_one
  条件: (z : 复形)
  结论: |z.re / ‖z‖| <= 1
  证明: if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]

Depends on / 依赖: abs_div, abs_norm, abs_re_le_norm, norm_pos_iff, norm_pos_iff.mpr, one_mul, simp_rw, zero_le_one
-/
theorem abs_re_div_norm_le_one (z : Complex) : |z.re / ‖z‖| <= 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]

/--
theorem `abs_im_div_norm_le_one` / 定理 `abs_im_div_norm_le_one`

English:
theorem abs_im_div_norm_le_one
  given: (z : Complex)
  statement: |z.im / ‖z‖| <= 1
  proof: if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]

中文:
定理 abs_im_div_norm_le_one
  条件: (z : 复形)
  结论: |z.im / ‖z‖| <= 1
  证明: if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]

Depends on / 依赖: _root_, _root_.abs_div, abs_div, abs_im_le_norm, abs_norm, norm_pos_iff, norm_pos_iff.mpr, one_mul, simp_rw, zero_le_one
-/
theorem abs_im_div_norm_le_one (z : Complex) : |z.im / ‖z‖| <= 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (z w : Complex)
  statement: dist z w = ‖z - w‖
  proof: dist_eq_norm _ _

中文:
定理 dist_eq
  条件: (z w : 复形)
  结论: dist z w = ‖z - w‖
  证明: dist_eq_norm _ _

Depends on / 依赖: dist_eq_norm
-/
theorem dist_eq (z w : Complex) : dist z w = ‖z - w‖ := dist_eq_norm _ _

/--
theorem `dist_eq_re_im` / 定理 `dist_eq_re_im`

English:
theorem dist_eq_re_im
  given: (z w : Complex)
  statement: dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2)
  proof: by
  rw [sq]; rw [sq]; rw [dist_eq]
  rfl

@[simp]

中文:
定理 dist_eq_re_im
  条件: (z w : 复形)
  结论: dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2)
  证明: by
  rw [sq]; rw [sq]; rw [dist_eq]
  rfl

@[simp]

Depends on / 依赖: dist_eq
-/
theorem dist_eq_re_im (z w : Complex) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq]; rw [sq]; rw [dist_eq]
  rfl

@[simp]
/--
theorem `dist_mk` / 定理 `dist_mk`

English:
theorem dist_mk
  given: (x₁ y₁ x₂ y₂ : Real)
  proof: dist_eq_re_im _ _

中文:
定理 dist_mk
  条件: (x₁ y₁ x₂ y₂ : 实数)
  证明: dist_eq_re_im _ _

Depends on / 依赖: dist_eq_re_im
-/
theorem dist_mk (x₁ y₁ x₂ y₂ : Real) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _

/--
theorem `dist_of_re_eq` / 定理 `dist_of_re_eq`

English:
theorem dist_of_re_eq
  given: {z w : Complex} (h : z.re = w.re)
  statement: dist z w = dist z.im w.im
  proof: by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [zero_add]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

中文:
定理 dist_of_re_eq
  条件: {z w : 复形} (h : z.re = w.re)
  结论: dist z w = dist z.im w.im
  证明: by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [zero_add]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

Depends on / 依赖: Real.dist_eq, Real.sqrt_sq_eq_abs, dist_eq, dist_eq_re_im, sqrt_sq_eq_abs, sub_self, two_ne_zero, zero_add, zero_pow
-/
theorem dist_of_re_eq {z w : Complex} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [zero_add]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

/--
theorem `nndist_of_re_eq` / 定理 `nndist_of_re_eq`

English:
theorem nndist_of_re_eq
  given: {z w : Complex} (h : z.re = w.re)
  statement: nndist z w = nndist z.im w.im
  proof: NNReal.eq dist_of_re_eq h

中文:
定理 nndist_of_re_eq
  条件: {z w : 复形} (h : z.re = w.re)
  结论: nndist z w = nndist z.im w.im
  证明: NNReal.eq dist_of_re_eq h

Depends on / 依赖: NNReal, NNReal.eq, dist_of_re_eq
-/
theorem nndist_of_re_eq {z w : Complex} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
NNReal.eq dist_of_re_eq h

/--
theorem `edist_of_re_eq` / 定理 `edist_of_re_eq`

English:
theorem edist_of_re_eq
  given: {z w : Complex} (h : z.re = w.re)
  statement: edist z w = edist z.im w.im
  proof: by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_re_eq h]

中文:
定理 edist_of_re_eq
  条件: {z w : 复形} (h : z.re = w.re)
  结论: edist z w = edist z.im w.im
  证明: by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_re_eq h]

Depends on / 依赖: edist_nndist, nndist_of_re_eq
-/
theorem edist_of_re_eq {z w : Complex} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_re_eq h]

/--
theorem `dist_of_im_eq` / 定理 `dist_of_im_eq`

English:
theorem dist_of_im_eq
  given: {z w : Complex} (h : z.im = w.im)
  statement: dist z w = dist z.re w.re
  proof: by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

中文:
定理 dist_of_im_eq
  条件: {z w : 复形} (h : z.im = w.im)
  结论: dist z w = dist z.re w.re
  证明: by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

Depends on / 依赖: Real.dist_eq, Real.sqrt_sq_eq_abs, add_zero, dist_eq, dist_eq_re_im, sqrt_sq_eq_abs, sub_self, two_ne_zero, zero_pow
-/
theorem dist_of_im_eq {z w : Complex} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im]; rw [h]; rw [sub_self]; rw [zero_pow two_ne_zero]; rw [add_zero]; rw [Real.sqrt_sq_eq_abs]; rw [Real.dist_eq]

/--
theorem `nndist_of_im_eq` / 定理 `nndist_of_im_eq`

English:
theorem nndist_of_im_eq
  given: {z w : Complex} (h : z.im = w.im)
  statement: nndist z w = nndist z.re w.re
  proof: NNReal.eq dist_of_im_eq h

中文:
定理 nndist_of_im_eq
  条件: {z w : 复形} (h : z.im = w.im)
  结论: nndist z w = nndist z.re w.re
  证明: NNReal.eq dist_of_im_eq h

Depends on / 依赖: NNReal, NNReal.eq, dist_of_im_eq
-/
theorem nndist_of_im_eq {z w : Complex} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
NNReal.eq dist_of_im_eq h

/--
theorem `edist_of_im_eq` / 定理 `edist_of_im_eq`

English:
theorem edist_of_im_eq
  given: {z w : Complex} (h : z.im = w.im)
  statement: edist z w = edist z.re w.re
  proof: by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_im_eq h]

中文:
定理 edist_of_im_eq
  条件: {z w : 复形} (h : z.im = w.im)
  结论: edist z w = edist z.re w.re
  证明: by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_im_eq h]

Depends on / 依赖: edist_nndist, nndist_of_im_eq
-/
theorem edist_of_im_eq {z w : Complex} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist]; rw [edist_nndist]; rw [nndist_of_im_eq h]

/--
theorem `dist_conj_self` / 定理 `dist_conj_self`

English:
theorem dist_conj_self
  given: (z : Complex)
  statement: dist (conj z) z = 2 * |z.im|
  proof: by
  rw [dist_of_re_eq (conj_re z)]; rw [conj_im]; rw [dist_comm]; rw [Real.dist_eq]; rw [sub_neg_eq_add]; rw [← two_mul]; rw [_root_.abs_mul]; rw [abs_of_pos (zero_lt_two' Real)]

中文:
定理 dist_conj_self
  条件: (z : 复形)
  结论: dist (conj z) z = 2 * |z.im|
  证明: by
  rw [dist_of_re_eq (conj_re z)]; rw [conj_im]; rw [dist_comm]; rw [Real.dist_eq]; rw [sub_neg_eq_add]; rw [← two_mul]; rw [_root_.abs_mul]; rw [abs_of_pos (zero_lt_two' Real)]

Depends on / 依赖: Real.dist_eq, _root_, _root_.abs_mul, abs_mul, abs_of_pos, conj_im, conj_re, dist_comm, dist_eq, dist_of_re_eq, sub_neg_eq_add, two_mul, zero_lt_two
-/
theorem dist_conj_self (z : Complex) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z)]; rw [conj_im]; rw [dist_comm]; rw [Real.dist_eq]; rw [sub_neg_eq_add]; rw [← two_mul]; rw [_root_.abs_mul]; rw [abs_of_pos (zero_lt_two' Real)]

/--
theorem `nndist_conj_self` / 定理 `nndist_conj_self`

English:
theorem nndist_conj_self
  given: (z : Complex)
  statement: nndist (conj z) z = 2 * Real.nnabs z.im
  proof: NNReal.eq by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

中文:
定理 nndist_conj_self
  条件: (z : 复形)
  结论: nndist (conj z) z = 2 * 实数.nnabs z.im
  证明: NNReal.eq by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.coe_two, NNReal.eq, Real.coe_nnabs, coe_mul, coe_nnabs, coe_two, dist_conj_self, dist_nndist
-/
theorem nndist_conj_self (z : Complex) : nndist (conj z) z = 2 * Real.nnabs z.im :=
NNReal.eq by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

/--
theorem `dist_self_conj` / 定理 `dist_self_conj`

English:
theorem dist_self_conj
  given: (z : Complex)
  statement: dist z (conj z) = 2 * |z.im|
  proof: by rw [dist_comm, dist_conj_self]

中文:
定理 dist_self_conj
  条件: (z : 复形)
  结论: dist z (conj z) = 2 * |z.im|
  证明: by rw [dist_comm, dist_conj_self]

Depends on / 依赖: dist_comm, dist_conj_self
-/
theorem dist_self_conj (z : Complex) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]

/--
theorem `nndist_self_conj` / 定理 `nndist_self_conj`

English:
theorem nndist_self_conj
  given: (z : Complex)
  statement: nndist z (conj z) = 2 * Real.nnabs z.im
  proof: by
  rw [nndist_comm]; rw [nndist_conj_self]

中文:
定理 nndist_self_conj
  条件: (z : 复形)
  结论: nndist z (conj z) = 2 * 实数.nnabs z.im
  证明: by
  rw [nndist_comm]; rw [nndist_conj_self]

Depends on / 依赖: nndist_comm, nndist_conj_self
-/
theorem nndist_self_conj (z : Complex) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm]; rw [nndist_conj_self]


/--
theorem `isCauSeq_re` / 定理 `isCauSeq_re`

English:
theorem isCauSeq_re
  given: (f : CauSeq Complex (‖·‖))
  statement: IsCauSeq abs fun n => (f n).re
  proof: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)

中文:
定理 isCauSeq_re
  条件: (f : CauSeq 复形 (‖·‖))
  结论: IsCauSeq abs fun n => (f n).re
  证明: fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)
-/
theorem isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq abs fun n => (f n).re := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)

/--
theorem `isCauSeq_im` / 定理 `isCauSeq_im`

English:
theorem isCauSeq_im
  given: (f : CauSeq Complex (‖·‖))
  statement: IsCauSeq abs fun n => (f n).im
  proof: fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij => by
simpa only [← ofReal_sub, norm_real, sub_re, sub_im] using (abs_im_le_norm _).trans_lt H _ ij

中文:
定理 isCauSeq_im
  条件: (f : CauSeq 复形 (‖·‖))
  结论: IsCauSeq abs fun n => (f n).im
  证明: fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij => by
simpa only [← ofReal_sub, norm_real, sub_re, sub_im] using (abs_im_le_norm _).trans_lt H _ ij
-/
theorem isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq abs fun n => (f n).im := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij => by
simpa only [← ofReal_sub, norm_real, sub_re, sub_im] using (abs_im_le_norm _).trans_lt H _ ij

/--
Definition of `cauSeqRe` / `cauSeqRe` 的定义

English:
definition cauSeqRe
  signature: (f : CauSeq Complex (‖·‖))
  body: ⟨_, isCauSeq_re f⟩

中文:
定义 cauSeqRe
  签名: (f : CauSeq 复形 (‖·‖))
  定义体: ⟨_, isCauSeq_re f⟩

Depends on / 依赖: isCauSeq_re
-/
noncomputable def cauSeqRe (f : CauSeq Complex (‖·‖)) : CauSeq Real abs :=
  ⟨_, isCauSeq_re f⟩

/--
Definition of `cauSeqIm` / `cauSeqIm` 的定义

English:
definition cauSeqIm
  signature: (f : CauSeq Complex (‖·‖))
  body: ⟨_, isCauSeq_im f⟩

中文:
定义 cauSeqIm
  签名: (f : CauSeq 复形 (‖·‖))
  定义体: ⟨_, isCauSeq_im f⟩

Depends on / 依赖: isCauSeq_im
-/
noncomputable def cauSeqIm (f : CauSeq Complex (‖·‖)) : CauSeq Real abs :=
  ⟨_, isCauSeq_im f⟩

/--
theorem `isCauSeq_norm` / 定理 `isCauSeq_norm`

English:
theorem isCauSeq_norm
  given: {f : Nat -> Complex} (hf : IsCauSeq (‖·‖) f)
  proof: fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

中文:
定理 isCauSeq_norm
  条件: {f : 自然数 -> 复形} (hf : IsCauSeq (‖·‖) f)
  证明: fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
-/
theorem isCauSeq_norm {f : Nat -> Complex} (hf : IsCauSeq (‖·‖) f) :
    IsCauSeq abs ((‖·‖) ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/--
Definition of `limAux` / `limAux` 的定义

English:
definition limAux
  signature: (f : CauSeq Complex (‖·‖))
  body: ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

中文:
定义 limAux
  签名: (f : CauSeq 复形 (‖·‖))
  定义体: ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

Depends on / 依赖: CauSeq, CauSeq.lim, cauSeqIm, cauSeqRe
-/
noncomputable def limAux (f : CauSeq Complex (‖·‖)) : Complex :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

/--
theorem `equiv_limAux` / 定理 `equiv_limAux`

English:
theorem equiv_limAux
  given: (f : CauSeq Complex (‖·‖))
  proof: fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij => by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    simpa using! add_lt_add H₁ H₂

中文:
定理 equiv_limAux
  条件: (f : CauSeq 复形 (‖·‖))
  证明: fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij => by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    simpa using! add_lt_add H₁ H₂
-/
theorem equiv_limAux (f : CauSeq Complex (‖·‖)) :
    f ≈ CauSeq.const (‖·‖) (limAux f) := fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij => by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    simpa using! add_lt_add H₁ H₂

/--
Instance `instIsComplete` / 实例 `instIsComplete`

English:
instance instIsComplete
  signature: : CauSeq.IsComplete Complex (‖·‖)
  body: ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

中文:
实例 instIsComplete
  签名: : CauSeq.是完备 复形 (‖·‖)
  定义体: ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

Depends on / 依赖: equiv_limAux, limAux
-/
instance instIsComplete : CauSeq.IsComplete Complex (‖·‖) :=
  ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

/--
theorem `lim_eq_lim_im_add_lim_re` / 定理 `lim_eq_lim_im_add_lim_re`

English:
theorem lim_eq_lim_im_add_lim_re
  given: (f : CauSeq Complex (‖·‖))
  proof: lim_eq_of_equiv_const
    letI : IsAbsoluteValue (‖·‖ : Complex -> Real) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by 

中文:
定理 lim_eq_lim_im_add_lim_re
  条件: (f : CauSeq 复形 (‖·‖))
  证明: lim_eq_of_equiv_const
    letI : IsAbsoluteValue (‖·‖ : Complex -> Real) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by 

Depends on / 依赖: CauSeq, CauSeq.const, CauSeq.ext, Complex.ext, IsAbsoluteValue, cauSeqIm, cauSeqRe, equiv_limAux, limAux, lim_eq_of_equiv_const, ofReal
-/
theorem lim_eq_lim_im_add_lim_re (f : CauSeq Complex (‖·‖)) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
lim_eq_of_equiv_const
    letI : IsAbsoluteValue (‖·‖ : Complex -> Real) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by simp [limAux, cauSeqIm, ofReal])

/--
theorem `lim_re` / 定理 `lim_re`

English:
theorem lim_re
  given: (f : CauSeq Complex (‖·‖))
  statement: lim (cauSeqRe f) = (lim f).re
  proof: by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

中文:
定理 lim_re
  条件: (f : CauSeq 复形 (‖·‖))
  结论: lim (cauSeqRe f) = (lim f).re
  证明: by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

Depends on / 依赖: lim_eq_lim_im_add_lim_re, ofReal
-/
theorem lim_re (f : CauSeq Complex (‖·‖)) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

/--
theorem `lim_im` / 定理 `lim_im`

English:
theorem lim_im
  given: (f : CauSeq Complex (‖·‖))
  statement: lim (cauSeqIm f) = (lim f).im
  proof: by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

中文:
定理 lim_im
  条件: (f : CauSeq 复形 (‖·‖))
  结论: lim (cauSeqIm f) = (lim f).im
  证明: by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

Depends on / 依赖: lim_eq_lim_im_add_lim_re, ofReal
-/
theorem lim_im (f : CauSeq Complex (‖·‖)) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]

/--
theorem `isCauSeq_conj` / 定理 `isCauSeq_conj`

English:
theorem isCauSeq_conj
  given: (f : CauSeq Complex (‖·‖))
  proof: fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← map_sub, norm_conj]; exact hi j hj⟩

中文:
定理 isCauSeq_conj
  条件: (f : CauSeq 复形 (‖·‖))
  证明: fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← map_sub, norm_conj]; exact hi j hj⟩
-/
theorem isCauSeq_conj (f : CauSeq Complex (‖·‖)) :
    IsCauSeq (‖·‖) fun n => conj (f n) := fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← map_sub, norm_conj]; exact hi j hj⟩

/--
Definition of `cauSeqConj` / `cauSeqConj` 的定义

English:
definition cauSeqConj
  signature: (f : CauSeq Complex (‖·‖))
  body: ⟨_, isCauSeq_conj f⟩

中文:
定义 cauSeqConj
  签名: (f : CauSeq 复形 (‖·‖))
  定义体: ⟨_, isCauSeq_conj f⟩

Depends on / 依赖: isCauSeq_conj
-/
noncomputable def cauSeqConj (f : CauSeq Complex (‖·‖)) : CauSeq Complex (‖·‖) :=
  ⟨_, isCauSeq_conj f⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lim_conj` / 定理 `lim_conj`

English:
theorem lim_conj
  given: (f : CauSeq Complex (‖·‖))
  statement: lim (cauSeqConj f) = conj (lim f)
  proof: Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

中文:
定理 lim_conj
  条件: (f : CauSeq 复形 (‖·‖))
  结论: lim (cauSeqConj f) = conj (lim f)
  证明: Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

Depends on / 依赖: Complex.ext, cauSeqConj, cauSeqIm, cauSeqRe, lim_im, lim_neg, lim_re
-/
theorem lim_conj (f : CauSeq Complex (‖·‖)) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

/--
Definition of `cauSeqNorm` / `cauSeqNorm` 的定义

English:
definition cauSeqNorm
  signature: (f : CauSeq Complex (‖·‖))
  body: ⟨_, isCauSeq_norm f.2⟩

中文:
定义 cauSeqNorm
  签名: (f : CauSeq 复形 (‖·‖))
  定义体: ⟨_, isCauSeq_norm f.2⟩

Depends on / 依赖: isCauSeq_norm
-/
noncomputable def cauSeqNorm (f : CauSeq Complex (‖·‖)) : CauSeq Real abs :=
  ⟨_, isCauSeq_norm f.2⟩

/--
theorem `lim_norm` / 定理 `lim_norm`

English:
theorem lim_norm
  given: (f : CauSeq Complex (‖·‖))
  statement: lim (cauSeqNorm f) = ‖lim f‖
  proof: lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

中文:
定理 lim_norm
  条件: (f : CauSeq 复形 (‖·‖))
  结论: lim (cauSeqNorm f) = ‖lim f‖
  证明: lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

Depends on / 依赖: abs_norm_sub_norm_le, equiv_lim, lim_eq_of_equiv_const, lt_of_le_of_lt
-/
theorem lim_norm (f : CauSeq Complex (‖·‖)) : lim (cauSeqNorm f) = ‖lim f‖ :=
  lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/--
lemma `ne_zero_of_re_pos` / 引理 `ne_zero_of_re_pos`

English:
lemma ne_zero_of_re_pos
  given: {s : Complex} (hs : 0 < s.re)
  statement: s != 0
  proof: fun h => (zero_re ▸ h ▸ hs).false

中文:
引理 ne_zero_of_re_pos
  条件: {s : 复形} (hs : 0 < s.re)
  结论: s != 0
  证明: fun h => (zero_re ▸ h ▸ hs).false

Depends on / 依赖: zero_re
-/
lemma ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : s != 0 :=
  fun h => (zero_re ▸ h ▸ hs).false

/--
lemma `ne_zero_of_one_lt_re` / 引理 `ne_zero_of_one_lt_re`

English:
lemma ne_zero_of_one_lt_re
  given: {s : Complex} (hs : 1 < s.re)
  statement: s != 0
  proof: ne_zero_of_re_pos zero_lt_one.trans hs

中文:
引理 ne_zero_of_one_lt_re
  条件: {s : 复形} (hs : 1 < s.re)
  结论: s != 0
  证明: ne_zero_of_re_pos zero_lt_one.trans hs

Depends on / 依赖: ne_zero_of_re_pos, zero_lt_one, zero_lt_one.trans
-/
lemma ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : s != 0 :=
ne_zero_of_re_pos zero_lt_one.trans hs

/--
lemma `re_neg_ne_zero_of_re_pos` / 引理 `re_neg_ne_zero_of_re_pos`

English:
lemma re_neg_ne_zero_of_re_pos
  given: {s : Complex} (hs : 0 < s.re)
  statement: (-s).re != 0
  proof: ne_iff_lt_or_gt.mpr Or.inl neg_re s ▸ (neg_lt_zero.mpr hs)

中文:
引理 re_neg_ne_zero_of_re_pos
  条件: {s : 复形} (hs : 0 < s.re)
  结论: (-s).re != 0
  证明: ne_iff_lt_or_gt.mpr Or.inl neg_re s ▸ (neg_lt_zero.mpr hs)

Depends on / 依赖: Or.inl, ne_iff_lt_or_gt, ne_iff_lt_or_gt.mpr, neg_lt_zero, neg_lt_zero.mpr, neg_re
-/
lemma re_neg_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : (-s).re != 0 :=
ne_iff_lt_or_gt.mpr Or.inl neg_re s ▸ (neg_lt_zero.mpr hs)

/--
lemma `re_neg_ne_zero_of_one_lt_re` / 引理 `re_neg_ne_zero_of_one_lt_re`

English:
lemma re_neg_ne_zero_of_one_lt_re
  given: {s : Complex} (hs : 1 < s.re)
  statement: (-s).re != 0
  proof: re_neg_ne_zero_of_re_pos zero_lt_one.trans hs

中文:
引理 re_neg_ne_zero_of_one_lt_re
  条件: {s : 复形} (hs : 1 < s.re)
  结论: (-s).re != 0
  证明: re_neg_ne_zero_of_re_pos zero_lt_one.trans hs

Depends on / 依赖: re_neg_ne_zero_of_re_pos, zero_lt_one, zero_lt_one.trans
-/
lemma re_neg_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : (-s).re != 0 :=
re_neg_ne_zero_of_re_pos zero_lt_one.trans hs

/--
lemma `norm_sub_one_sq_eq_of_norm_eq_one` / 引理 `norm_sub_one_sq_eq_of_norm_eq_one`

English:
lemma norm_sub_one_sq_eq_of_norm_eq_one
  given: {z : Complex} (hz : ‖z‖ = 1)
  proof: by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm]; rw [normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring

中文:
引理 norm_sub_one_sq_eq_of_norm_eq_one
  条件: {z : 复形} (hz : ‖z‖ = 1)
  证明: by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm]; rw [normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring

Depends on / 依赖: Complex.sq_norm, normSq_apply, replace, sq_eq_one_iff, sq_eq_one_iff.mpr, sq_norm, z.im, z.re
-/
lemma norm_sub_one_sq_eq_of_norm_eq_one {z : Complex} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm]; rw [normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring

/--
lemma `norm_sub_one_sq_eqOn_sphere` / 引理 `norm_sub_one_sq_eqOn_sphere`

English:
lemma norm_sub_one_sq_eqOn_sphere
  proof: fun z hz => norm_sub_one_sq_eq_of_norm_eq_one (by simpa using hz)

中文:
引理 norm_sub_one_sq_eqOn_sphere
  证明: fun z hz => norm_sub_one_sq_eq_of_norm_eq_one (by simpa using hz)

Depends on / 依赖: norm_sub_one_sq_eq_of_norm_eq_one
-/
lemma norm_sub_one_sq_eqOn_sphere :
    (Metric.sphere (0 : Complex) 1).EqOn (‖· - 1‖ ^ 2) (fun z => 2 * (1 - z.re)) :=
  fun z hz => norm_sub_one_sq_eq_of_norm_eq_one (by simpa using hz)

/--
lemma `normSq_ofReal_add_I_mul_sqrt_one_sub` / 引理 `normSq_ofReal_add_I_mul_sqrt_one_sub`

English:
lemma normSq_ofReal_add_I_mul_sqrt_one_sub
  given: {x : Real} (hx : ‖x‖ <= 1)
  proof: by
  simp [mul_comm I, normSq_add_mul_I,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]

中文:
引理 normSq_of实数_add_I_mul_sqrt_one_sub
  条件: {x : 实数} (hx : ‖x‖ <= 1)
  证明: by
  simp [mul_comm I, normSq_add_mul_I,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]

Depends on / 依赖: Real.sq_sqrt, abs_le, abs_le.mp, mul_comm, normSq_add_mul_I, sq_sqrt
-/
lemma normSq_ofReal_add_I_mul_sqrt_one_sub {x : Real} (hx : ‖x‖ <= 1) :
    normSq (x + I * √(1 - x ^ 2)) = 1 := by
  simp [mul_comm I, normSq_add_mul_I,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]

/--
lemma `normSq_ofReal_sub_I_mul_sqrt_one_sub` / 引理 `normSq_ofReal_sub_I_mul_sqrt_one_sub`

English:
lemma normSq_ofReal_sub_I_mul_sqrt_one_sub
  given: {x : Real} (hx : ‖x‖ <= 1)
  proof: by
  rw [← normSq_neg]; rw [neg_sub']; rw [sub_neg_eq_add]
  simpa using normSq_ofReal_add_I_mul_sqrt_one_sub (x := -x) (by simpa)

中文:
引理 normSq_of实数_sub_I_mul_sqrt_one_sub
  条件: {x : 实数} (hx : ‖x‖ <= 1)
  证明: by
  rw [← normSq_neg]; rw [neg_sub']; rw [sub_neg_eq_add]
  simpa using normSq_ofReal_add_I_mul_sqrt_one_sub (x := -x) (by simpa)

Depends on / 依赖: neg_sub, normSq_neg, normSq_ofReal_add_I_mul_sqrt_one_sub, sub_neg_eq_add
-/
lemma normSq_ofReal_sub_I_mul_sqrt_one_sub {x : Real} (hx : ‖x‖ <= 1) :
    normSq (x - I * √(1 - x ^ 2)) = 1 := by
  rw [← normSq_neg]; rw [neg_sub']; rw [sub_neg_eq_add]
  simpa using normSq_ofReal_add_I_mul_sqrt_one_sub (x := -x) (by simpa)

end Complex
