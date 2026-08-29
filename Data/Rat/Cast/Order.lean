/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Core

/-!
# Casts of rational numbers into linear ordered fields.
-/

@[expose] public section

variable {F ι α β : Type*}

namespace Rat
variable {p q : Rat}

@[simp]
/--
theorem `castHom_rat` / 定理 `castHom_rat`

English:
theorem castHom_rat
  statement: castHom Rat = RingHom.id Rat
  proof: RingHom.ext cast_id

中文:
定理 castHom_rat
  结论: castHom 有理数 = 环态射.id 有理数
  证明: RingHom.ext cast_id

Depends on / 依赖: RingHom, RingHom.ext, cast_id
-/
theorem castHom_rat : castHom Rat = RingHom.id Rat :=
  RingHom.ext cast_id

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
theorem `cast_pos_of_pos` / 定理 `cast_pos_of_pos`

English:
theorem cast_pos_of_pos
  given: (hq : 0 < q)
  statement: (0 : K) < q
  proof: by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]

中文:
定理 cast_pos_of_pos
  条件: (hq : 0 < q)
  结论: (0 : K) < q
  证明: by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]

Depends on / 依赖: Int.cast_pos, Nat.cast_pos, Rat.cast_def, cast_def, cast_pos, div_pos, num_pos, q.pos
-/
theorem cast_pos_of_pos (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]
/--
theorem `cast_strictMono` / 定理 `cast_strictMono`

English:
theorem cast_strictMono
  statement: StrictMono ((↑) : Rat -> K)
  proof: fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]

中文:
定理 cast_strictMono
  结论: 严格递增 ((↑) : 有理数 -> K)
  证明: fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]

Depends on / 依赖: cast_pos_of_pos, cast_sub, sub_pos
-/
theorem cast_strictMono : StrictMono ((↑) : Rat -> K) := fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]
/--
theorem `cast_mono` / 定理 `cast_mono`

English:
theorem cast_mono
  statement: Monotone ((↑) : Rat -> K)
  proof: cast_strictMono.monotone

中文:
定理 cast_mono
  结论: 递增 ((↑) : 有理数 -> K)
  证明: cast_strictMono.monotone

Depends on / 依赖: cast_strictMono, cast_strictMono.monotone, monotone
-/
theorem cast_mono : Monotone ((↑) : Rat -> K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
/--
Definition of `castOrderEmbedding` / `castOrderEmbedding` 的定义

English:
definition castOrderEmbedding
  signature: : Rat ↪o K
  body: OrderEmbedding.ofStrictMono (↑) cast_strictMono

中文:
定义 castOrderEmbedding
  签名: : 有理数 ↪o K
  定义体: OrderEmbedding.ofStrictMono (↑) cast_strictMono

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, cast_strictMono, ofStrictMono
-/
def castOrderEmbedding : Rat ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono

/--
lemma `cast_le` / 引理 `cast_le`

English:
lemma cast_le
  statement: (p : K) <= q ↔ p <= q
  proof: castOrderEmbedding.le_iff_le

中文:
引理 cast_le
  结论: (p : K) <= q ↔ p <= q
  证明: castOrderEmbedding.le_iff_le
-/
@[simp, norm_cast] lemma cast_le : (p : K) <= q ↔ p <= q := castOrderEmbedding.le_iff_le

/--
lemma `cast_lt` / 引理 `cast_lt`

English:
lemma cast_lt
  statement: (p : K) < q ↔ p < q
  proof: cast_strictMono.lt_iff_lt

中文:
引理 cast_lt
  结论: (p : K) < q ↔ p < q
  证明: cast_strictMono.lt_iff_lt
-/
@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt

/--
lemma `cast_nonneg` / 引理 `cast_nonneg`

English:
lemma cast_nonneg
  statement: 0 <= (q : K) ↔ 0 <= q
  proof: by norm_cast

中文:
引理 cast_nonneg
  结论: 0 <= (q : K) ↔ 0 <= q
  证明: by norm_cast
-/
@[simp] lemma cast_nonneg : 0 <= (q : K) ↔ 0 <= q := by norm_cast

/--
lemma `cast_nonpos` / 引理 `cast_nonpos`

English:
lemma cast_nonpos
  statement: (q : K) <= 0 ↔ q <= 0
  proof: by norm_cast

中文:
引理 cast_nonpos
  结论: (q : K) <= 0 ↔ q <= 0
  证明: by norm_cast
-/
@[simp] lemma cast_nonpos : (q : K) <= 0 ↔ q <= 0 := by norm_cast

/--
lemma `cast_pos` / 引理 `cast_pos`

English:
lemma cast_pos
  statement: (0 : K) < q ↔ 0 < q
  proof: by norm_cast

中文:
引理 cast_pos
  结论: (0 : K) < q ↔ 0 < q
  证明: by norm_cast
-/
@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast

/--
lemma `cast_lt_zero` / 引理 `cast_lt_zero`

English:
lemma cast_lt_zero
  statement: (q : K) < 0 ↔ q < 0
  proof: by norm_cast

@[simp, norm_cast]

中文:
引理 cast_lt_zero
  结论: (q : K) < 0 ↔ q < 0
  证明: by norm_cast

@[simp, norm_cast]
-/
@[simp] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast

@[simp, norm_cast]
/--
theorem `cast_le_natCast` / 定理 `cast_le_natCast`

English:
theorem cast_le_natCast
  given: {m : Rat} {n : Nat}
  statement: (m : K) <= n ↔ m <= (n : Rat)
  proof: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 cast_le_natCast
  条件: {m : 有理数} {n : 自然数}
  结论: (m : K) <= n ↔ m <= (n : 有理数)
  证明: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_le, cast_natCast
-/
theorem cast_le_natCast {m : Rat} {n : Nat} : (m : K) <= n ↔ m <= (n : Rat) := by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `natCast_le_cast` / 定理 `natCast_le_cast`

English:
theorem natCast_le_cast
  given: {m : Nat} {n : Rat}
  statement: (m : K) <= n ↔ (m : Rat) <= n
  proof: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 natCast_le_cast
  条件: {m : 自然数} {n : 有理数}
  结论: (m : K) <= n ↔ (m : 有理数) <= n
  证明: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_le, cast_natCast
-/
theorem natCast_le_cast {m : Nat} {n : Rat} : (m : K) <= n ↔ (m : Rat) <= n := by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `cast_le_intCast` / 定理 `cast_le_intCast`

English:
theorem cast_le_intCast
  given: {m : Rat} {n : Int}
  statement: (m : K) <= n ↔ m <= (n : Rat)
  proof: by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

中文:
定理 cast_le_intCast
  条件: {m : 有理数} {n : 整数}
  结论: (m : K) <= n ↔ m <= (n : 有理数)
  证明: by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

Depends on / 依赖: cast_intCast, cast_le
-/
theorem cast_le_intCast {m : Rat} {n : Int} : (m : K) <= n ↔ m <= (n : Rat) := by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]
/--
theorem `intCast_le_cast` / 定理 `intCast_le_cast`

English:
theorem intCast_le_cast
  given: {m : Int} {n : Rat}
  statement: (m : K) <= n ↔ (m : Rat) <= n
  proof: by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

中文:
定理 intCast_le_cast
  条件: {m : 整数} {n : 有理数}
  结论: (m : K) <= n ↔ (m : 有理数) <= n
  证明: by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

Depends on / 依赖: cast_intCast, cast_le
-/
theorem intCast_le_cast {m : Int} {n : Rat} : (m : K) <= n ↔ (m : Rat) <= n := by
  rw [← cast_le (K := K)]; rw [cast_intCast]

@[simp, norm_cast]
/--
theorem `cast_lt_natCast` / 定理 `cast_lt_natCast`

English:
theorem cast_lt_natCast
  given: {m : Rat} {n : Nat}
  statement: (m : K) < n ↔ m < (n : Rat)
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 cast_lt_natCast
  条件: {m : 有理数} {n : 自然数}
  结论: (m : K) < n ↔ m < (n : 有理数)
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_lt, cast_natCast
-/
theorem cast_lt_natCast {m : Rat} {n : Nat} : (m : K) < n ↔ m < (n : Rat) := by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `natCast_lt_cast` / 定理 `natCast_lt_cast`

English:
theorem natCast_lt_cast
  given: {m : Nat} {n : Rat}
  statement: (m : K) < n ↔ (m : Rat) < n
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 natCast_lt_cast
  条件: {m : 自然数} {n : 有理数}
  结论: (m : K) < n ↔ (m : 有理数) < n
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_lt, cast_natCast
-/
theorem natCast_lt_cast {m : Nat} {n : Rat} : (m : K) < n ↔ (m : Rat) < n := by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `cast_lt_intCast` / 定理 `cast_lt_intCast`

English:
theorem cast_lt_intCast
  given: {m : Rat} {n : Int}
  statement: (m : K) < n ↔ m < (n : Rat)
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

中文:
定理 cast_lt_intCast
  条件: {m : 有理数} {n : 整数}
  结论: (m : K) < n ↔ m < (n : 有理数)
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

Depends on / 依赖: cast_intCast, cast_lt
-/
theorem cast_lt_intCast {m : Rat} {n : Int} : (m : K) < n ↔ m < (n : Rat) := by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]
/--
theorem `intCast_lt_cast` / 定理 `intCast_lt_cast`

English:
theorem intCast_lt_cast
  given: {m : Int} {n : Rat}
  statement: (m : K) < n ↔ (m : Rat) < n
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

中文:
定理 intCast_lt_cast
  条件: {m : 整数} {n : 有理数}
  结论: (m : K) < n ↔ (m : 有理数) < n
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]

Depends on / 依赖: cast_intCast, cast_lt
-/
theorem intCast_lt_cast {m : Int} {n : Rat} : (m : K) < n ↔ (m : Rat) < n := by
  rw [← cast_lt (K := K)]; rw [cast_intCast]

@[simp, norm_cast]
/--
lemma `cast_min` / 引理 `cast_min`

English:
lemma cast_min
  given: (p q : Rat)
  statement: (↑(min p q) : K) = min (p : K) (q : K)
  proof: (@cast_mono K _).map_min

@[simp, norm_cast]

中文:
引理 cast_min
  条件: (p q : 有理数)
  结论: (↑(最小值 p q) : K) = 最小值 (p : K) (q : K)
  证明: (@cast_mono K _).map_min

@[simp, norm_cast]

Depends on / 依赖: cast_mono, map_min
-/
lemma cast_min (p q : Rat) : (↑(min p q) : K) = min (p : K) (q : K) := (@cast_mono K _).map_min

@[simp, norm_cast]
/--
lemma `cast_max` / 引理 `cast_max`

English:
lemma cast_max
  given: (p q : Rat)
  statement: (↑(max p q) : K) = max (p : K) (q : K)
  proof: (@cast_mono K _).map_max

中文:
引理 cast_max
  条件: (p q : 有理数)
  结论: (↑(最大值 p q) : K) = 最大值 (p : K) (q : K)
  证明: (@cast_mono K _).map_max

Depends on / 依赖: cast_mono, map_max
-/
lemma cast_max (p q : Rat) : (↑(max p q) : K) = max (p : K) (q : K) := (@cast_mono K _).map_max

/--
lemma `cast_abs` / 引理 `cast_abs`

English:
lemma cast_abs
  given: (q : Rat)
  statement: ((|q| : Rat) : K) = |(q : K)|
  proof: by simp [abs_eq_max_neg]

中文:
引理 cast_abs
  条件: (q : 有理数)
  结论: ((|q| : 有理数) : K) = |(q : K)|
  证明: by simp [abs_eq_max_neg]
-/
@[simp, norm_cast] lemma cast_abs (q : Rat) : ((|q| : Rat) : K) = |(q : K)| := by simp [abs_eq_max_neg]

open Set

@[simp]
/--
theorem `preimage_cast_Icc` / 定理 `preimage_cast_Icc`

English:
theorem preimage_cast_Icc
  given: (p q : Rat)
  statement: (↑) ⁻¹' Icc (p : K) q = Icc p q
  proof: castOrderEmbedding.preimage_Icc ..

@[simp]

中文:
定理 preimage_cast_Icc
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' 闭区间 (p : K) q = 闭区间 p q
  证明: castOrderEmbedding.preimage_Icc ..

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Icc, preimage_Icc
-/
theorem preimage_cast_Icc (p q : Rat) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
/--
theorem `preimage_cast_Ico` / 定理 `preimage_cast_Ico`

English:
theorem preimage_cast_Ico
  given: (p q : Rat)
  statement: (↑) ⁻¹' Ico (p : K) q = Ico p q
  proof: castOrderEmbedding.preimage_Ico ..

@[simp]

中文:
定理 preimage_cast_Ico
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' 左闭右开区间 (p : K) q = 左闭右开区间 p q
  证明: castOrderEmbedding.preimage_Ico ..

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ico, preimage_Ico
-/
theorem preimage_cast_Ico (p q : Rat) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
/--
theorem `preimage_cast_Ioc` / 定理 `preimage_cast_Ioc`

English:
theorem preimage_cast_Ioc
  given: (p q : Rat)
  statement: (↑) ⁻¹' Ioc (p : K) q = Ioc p q
  proof: castOrderEmbedding.preimage_Ioc p q

@[simp]

中文:
定理 preimage_cast_Ioc
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' 左开右闭区间 (p : K) q = 左开右闭区间 p q
  证明: castOrderEmbedding.preimage_Ioc p q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioc, preimage_Ioc
-/
theorem preimage_cast_Ioc (p q : Rat) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
/--
theorem `preimage_cast_Ioo` / 定理 `preimage_cast_Ioo`

English:
theorem preimage_cast_Ioo
  given: (p q : Rat)
  statement: (↑) ⁻¹' Ioo (p : K) q = Ioo p q
  proof: castOrderEmbedding.preimage_Ioo p q

@[simp]

中文:
定理 preimage_cast_Ioo
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' 开区间 (p : K) q = 开区间 p q
  证明: castOrderEmbedding.preimage_Ioo p q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioo, preimage_Ioo
-/
theorem preimage_cast_Ioo (p q : Rat) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
/--
theorem `preimage_cast_Ici` / 定理 `preimage_cast_Ici`

English:
theorem preimage_cast_Ici
  given: (q : Rat)
  statement: (↑) ⁻¹' Ici (q : K) = Ici q
  proof: castOrderEmbedding.preimage_Ici q

@[simp]

中文:
定理 preimage_cast_Ici
  条件: (q : 有理数)
  结论: (↑) ⁻¹' 左闭右无界区间 (q : K) = 左闭右无界区间 q
  证明: castOrderEmbedding.preimage_Ici q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ici, preimage_Ici
-/
theorem preimage_cast_Ici (q : Rat) : (↑) ⁻¹' Ici (q : K) = Ici q :=
  castOrderEmbedding.preimage_Ici q

@[simp]
/--
theorem `preimage_cast_Iic` / 定理 `preimage_cast_Iic`

English:
theorem preimage_cast_Iic
  given: (q : Rat)
  statement: (↑) ⁻¹' Iic (q : K) = Iic q
  proof: castOrderEmbedding.preimage_Iic q

@[simp]

中文:
定理 preimage_cast_Iic
  条件: (q : 有理数)
  结论: (↑) ⁻¹' 左无界右闭区间 (q : K) = 左无界右闭区间 q
  证明: castOrderEmbedding.preimage_Iic q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Iic, preimage_Iic
-/
theorem preimage_cast_Iic (q : Rat) : (↑) ⁻¹' Iic (q : K) = Iic q :=
  castOrderEmbedding.preimage_Iic q

@[simp]
/--
theorem `preimage_cast_Ioi` / 定理 `preimage_cast_Ioi`

English:
theorem preimage_cast_Ioi
  given: (q : Rat)
  statement: (↑) ⁻¹' Ioi (q : K) = Ioi q
  proof: castOrderEmbedding.preimage_Ioi q

@[simp]

中文:
定理 preimage_cast_Ioi
  条件: (q : 有理数)
  结论: (↑) ⁻¹' 左开右无界区间 (q : K) = 左开右无界区间 q
  证明: castOrderEmbedding.preimage_Ioi q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioi, preimage_Ioi
-/
theorem preimage_cast_Ioi (q : Rat) : (↑) ⁻¹' Ioi (q : K) = Ioi q :=
  castOrderEmbedding.preimage_Ioi q

@[simp]
/--
theorem `preimage_cast_Iio` / 定理 `preimage_cast_Iio`

English:
theorem preimage_cast_Iio
  given: (q : Rat)
  statement: (↑) ⁻¹' Iio (q : K) = Iio q
  proof: castOrderEmbedding.preimage_Iio q

@[simp]

中文:
定理 preimage_cast_Iio
  条件: (q : 有理数)
  结论: (↑) ⁻¹' 左无界右开区间 (q : K) = 左无界右开区间 q
  证明: castOrderEmbedding.preimage_Iio q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Iio, preimage_Iio
-/
theorem preimage_cast_Iio (q : Rat) : (↑) ⁻¹' Iio (q : K) = Iio q :=
  castOrderEmbedding.preimage_Iio q

@[simp]
/--
theorem `preimage_cast_uIcc` / 定理 `preimage_cast_uIcc`

English:
theorem preimage_cast_uIcc
  given: (p q : Rat)
  statement: (↑) ⁻¹' uIcc (p : K) q = uIcc p q
  proof: (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]

中文:
定理 preimage_cast_uIcc
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' uIcc (p : K) q = uIcc p q
  证明: (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]

Depends on / 依赖: castOrderEmbedding, preimage_uIcc
-/
theorem preimage_cast_uIcc (p q : Rat) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
/--
theorem `preimage_cast_uIoc` / 定理 `preimage_cast_uIoc`

English:
theorem preimage_cast_uIoc
  given: (p q : Rat)
  statement: (↑) ⁻¹' uIoc (p : K) q = uIoc p q
  proof: (castOrderEmbedding (K := K)).preimage_uIoc p q

中文:
定理 preimage_cast_uIoc
  条件: (p q : 有理数)
  结论: (↑) ⁻¹' uIoc (p : K) q = uIoc p q
  证明: (castOrderEmbedding (K := K)).preimage_uIoc p q

Depends on / 依赖: castOrderEmbedding, preimage_uIoc
-/
theorem preimage_cast_uIoc (p q : Rat) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end LinearOrderedField
end Rat

namespace NNRat

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {p q : Rat>=0}

/--
theorem `cast_strictMono` / 定理 `cast_strictMono`

English:
theorem cast_strictMono
  statement: StrictMono ((↑) : Rat>=0 -> K)
  proof: fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff₀, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt (α := K), ← NNRat.lt_def]
  · simp
  · simp

@[gcongr, mono]

中文:
定理 cast_strictMono
  结论: 严格递增 ((↑) : 有理数>=0 -> K)
  证明: fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff₀, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt (α := K), ← NNRat.lt_def]
  · simp
  · simp

@[gcongr, mono]

Depends on / 依赖: NNRat.cast_def, NNRat.lt_def, Nat.cast_lt, Nat.cast_mul, cast_def, cast_lt, cast_mul, lt_def
-/
theorem cast_strictMono : StrictMono ((↑) : Rat>=0 -> K) := fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff₀, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt (α := K), ← NNRat.lt_def]
  · simp
  · simp

@[gcongr, mono]
/--
theorem `cast_mono` / 定理 `cast_mono`

English:
theorem cast_mono
  statement: Monotone ((↑) : Rat>=0 -> K)
  proof: cast_strictMono.monotone

中文:
定理 cast_mono
  结论: 递增 ((↑) : 有理数>=0 -> K)
  证明: cast_strictMono.monotone

Depends on / 依赖: cast_strictMono, cast_strictMono.monotone, monotone
-/
theorem cast_mono : Monotone ((↑) : Rat>=0 -> K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
/--
Definition of `castOrderEmbedding` / `castOrderEmbedding` 的定义

English:
definition castOrderEmbedding
  signature: : Rat>=0 ↪o K
  body: OrderEmbedding.ofStrictMono (↑) cast_strictMono

中文:
定义 castOrderEmbedding
  签名: : 有理数>=0 ↪o K
  定义体: OrderEmbedding.ofStrictMono (↑) cast_strictMono

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, cast_strictMono, ofStrictMono
-/
def castOrderEmbedding : Rat>=0 ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono

/--
lemma `cast_le` / 引理 `cast_le`

English:
lemma cast_le
  statement: (p : K) <= q ↔ p <= q
  proof: castOrderEmbedding.le_iff_le

中文:
引理 cast_le
  结论: (p : K) <= q ↔ p <= q
  证明: castOrderEmbedding.le_iff_le
-/
@[simp, norm_cast] lemma cast_le : (p : K) <= q ↔ p <= q := castOrderEmbedding.le_iff_le
/--
lemma `cast_lt` / 引理 `cast_lt`

English:
lemma cast_lt
  statement: (p : K) < q ↔ p < q
  proof: cast_strictMono.lt_iff_lt

中文:
引理 cast_lt
  结论: (p : K) < q ↔ p < q
  证明: cast_strictMono.lt_iff_lt
-/
@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt
/--
lemma `cast_nonpos` / 引理 `cast_nonpos`

English:
lemma cast_nonpos
  statement: (q : K) <= 0 ↔ q <= 0
  proof: by norm_cast

中文:
引理 cast_nonpos
  结论: (q : K) <= 0 ↔ q <= 0
  证明: by norm_cast
-/
@[simp] lemma cast_nonpos : (q : K) <= 0 ↔ q <= 0 := by norm_cast
/--
lemma `cast_pos` / 引理 `cast_pos`

English:
lemma cast_pos
  statement: (0 : K) < q ↔ 0 < q
  proof: by norm_cast

中文:
引理 cast_pos
  结论: (0 : K) < q ↔ 0 < q
  证明: by norm_cast
-/
@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast
/--
lemma `cast_lt_zero` / 引理 `cast_lt_zero`

English:
lemma cast_lt_zero
  statement: (q : K) < 0 ↔ q < 0
  proof: by norm_cast

中文:
引理 cast_lt_zero
  结论: (q : K) < 0 ↔ q < 0
  证明: by norm_cast
-/
@[norm_cast] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast
/--
lemma `not_cast_lt_zero` / 引理 `not_cast_lt_zero`

English:
lemma not_cast_lt_zero
  statement: ¬(q : K) < 0
  proof: mod_cast not_lt_zero

中文:
引理 not_cast_lt_zero
  结论: ¬(q : K) < 0
  证明: mod_cast not_lt_zero
-/
@[simp] lemma not_cast_lt_zero : ¬(q : K) < 0 := mod_cast not_lt_zero
/--
lemma `cast_le_one` / 引理 `cast_le_one`

English:
lemma cast_le_one
  statement: (p : K) <= 1 ↔ p <= 1
  proof: by norm_cast

中文:
引理 cast_le_one
  结论: (p : K) <= 1 ↔ p <= 1
  证明: by norm_cast
-/
@[simp] lemma cast_le_one : (p : K) <= 1 ↔ p <= 1 := by norm_cast
/--
lemma `one_le_cast` / 引理 `one_le_cast`

English:
lemma one_le_cast
  statement: 1 <= (p : K) ↔ 1 <= p
  proof: by norm_cast

中文:
引理 one_le_cast
  结论: 1 <= (p : K) ↔ 1 <= p
  证明: by norm_cast
-/
@[simp] lemma one_le_cast : 1 <= (p : K) ↔ 1 <= p := by norm_cast
/--
lemma `cast_lt_one` / 引理 `cast_lt_one`

English:
lemma cast_lt_one
  statement: (p : K) < 1 ↔ p < 1
  proof: by norm_cast

中文:
引理 cast_lt_one
  结论: (p : K) < 1 ↔ p < 1
  证明: by norm_cast
-/
@[simp] lemma cast_lt_one : (p : K) < 1 ↔ p < 1 := by norm_cast
/--
lemma `one_lt_cast` / 引理 `one_lt_cast`

English:
lemma one_lt_cast
  statement: 1 < (p : K) ↔ 1 < p
  proof: by norm_cast

中文:
引理 one_lt_cast
  结论: 1 < (p : K) ↔ 1 < p
  证明: by norm_cast
-/
@[simp] lemma one_lt_cast : 1 < (p : K) ↔ 1 < p := by norm_cast

section ofNat
variable {n : Nat} [n.AtLeastTwo]

/--
lemma `cast_le_ofNat` / 引理 `cast_le_ofNat`

English:
lemma cast_le_ofNat
  statement: (p : K) <= ofNat(n) ↔ p <= OfNat.ofNat n
  proof: by
  simp [← cast_le (K := K)]

中文:
引理 cast_le_of自然数
  结论: (p : K) <= of自然数(n) ↔ p <= Of自然数.of自然数 n
  证明: by
  simp [← cast_le (K := K)]
-/
@[simp] lemma cast_le_ofNat : (p : K) <= ofNat(n) ↔ p <= OfNat.ofNat n := by
  simp [← cast_le (K := K)]

/--
lemma `ofNat_le_cast` / 引理 `ofNat_le_cast`

English:
lemma ofNat_le_cast
  statement: ofNat(n) <= (p : K) ↔ OfNat.ofNat n <= p
  proof: by
  simp [← cast_le (K := K)]

中文:
引理 of自然数_le_cast
  结论: of自然数(n) <= (p : K) ↔ Of自然数.of自然数 n <= p
  证明: by
  simp [← cast_le (K := K)]
-/
@[simp] lemma ofNat_le_cast : ofNat(n) <= (p : K) ↔ OfNat.ofNat n <= p := by
  simp [← cast_le (K := K)]

/--
lemma `cast_lt_ofNat` / 引理 `cast_lt_ofNat`

English:
lemma cast_lt_ofNat
  statement: (p : K) < ofNat(n) ↔ p < OfNat.ofNat n
  proof: by
  simp [← cast_lt (K := K)]

中文:
引理 cast_lt_of自然数
  结论: (p : K) < of自然数(n) ↔ p < Of自然数.of自然数 n
  证明: by
  simp [← cast_lt (K := K)]
-/
@[simp] lemma cast_lt_ofNat : (p : K) < ofNat(n) ↔ p < OfNat.ofNat n := by
  simp [← cast_lt (K := K)]

/--
lemma `ofNat_lt_cast` / 引理 `ofNat_lt_cast`

English:
lemma ofNat_lt_cast
  statement: ofNat(n) < (p : K) ↔ OfNat.ofNat n < p
  proof: by
  simp [← cast_lt (K := K)]

中文:
引理 of自然数_lt_cast
  结论: of自然数(n) < (p : K) ↔ Of自然数.of自然数 n < p
  证明: by
  simp [← cast_lt (K := K)]
-/
@[simp] lemma ofNat_lt_cast : ofNat(n) < (p : K) ↔ OfNat.ofNat n < p := by
  simp [← cast_lt (K := K)]

end ofNat

@[simp, norm_cast]
/--
theorem `cast_le_natCast` / 定理 `cast_le_natCast`

English:
theorem cast_le_natCast
  given: {m : Rat>=0} {n : Nat}
  statement: (m : K) <= n ↔ m <= (n : Rat>=0)
  proof: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 cast_le_natCast
  条件: {m : 有理数>=0} {n : 自然数}
  结论: (m : K) <= n ↔ m <= (n : 有理数>=0)
  证明: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_le, cast_natCast
-/
theorem cast_le_natCast {m : Rat>=0} {n : Nat} : (m : K) <= n ↔ m <= (n : Rat>=0) := by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `natCast_le_cast` / 定理 `natCast_le_cast`

English:
theorem natCast_le_cast
  given: {m : Nat} {n : Rat>=0}
  statement: (m : K) <= n ↔ (m : Rat>=0) <= n
  proof: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 natCast_le_cast
  条件: {m : 自然数} {n : 有理数>=0}
  结论: (m : K) <= n ↔ (m : 有理数>=0) <= n
  证明: by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_le, cast_natCast
-/
theorem natCast_le_cast {m : Nat} {n : Rat>=0} : (m : K) <= n ↔ (m : Rat>=0) <= n := by
  rw [← cast_le (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `cast_lt_natCast` / 定理 `cast_lt_natCast`

English:
theorem cast_lt_natCast
  given: {m : Rat>=0} {n : Nat}
  statement: (m : K) < n ↔ m < (n : Rat>=0)
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

中文:
定理 cast_lt_natCast
  条件: {m : 有理数>=0} {n : 自然数}
  结论: (m : K) < n ↔ m < (n : 有理数>=0)
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]

Depends on / 依赖: cast_lt, cast_natCast
-/
theorem cast_lt_natCast {m : Rat>=0} {n : Nat} : (m : K) < n ↔ m < (n : Rat>=0) := by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

@[simp, norm_cast]
/--
theorem `natCast_lt_cast` / 定理 `natCast_lt_cast`

English:
theorem natCast_lt_cast
  given: {m : Nat} {n : Rat>=0}
  statement: (m : K) < n ↔ (m : Rat>=0) < n
  proof: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

中文:
定理 natCast_lt_cast
  条件: {m : 自然数} {n : 有理数>=0}
  结论: (m : K) < n ↔ (m : 有理数>=0) < n
  证明: by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

Depends on / 依赖: cast_lt, cast_natCast
-/
theorem natCast_lt_cast {m : Nat} {n : Rat>=0} : (m : K) < n ↔ (m : Rat>=0) < n := by
  rw [← cast_lt (K := K)]; rw [cast_natCast]

/--
lemma `cast_min` / 引理 `cast_min`

English:
lemma cast_min
  given: (p q : Rat>=0)
  statement: (↑(min p q) : K) = min (p : K) (q : K)
  proof: (@cast_mono K _).map_min

中文:
引理 cast_min
  条件: (p q : 有理数>=0)
  结论: (↑(最小值 p q) : K) = 最小值 (p : K) (q : K)
  证明: (@cast_mono K _).map_min
-/
@[simp, norm_cast] lemma cast_min (p q : Rat>=0) : (↑(min p q) : K) = min (p : K) (q : K) :=
  (@cast_mono K _).map_min

/--
lemma `cast_max` / 引理 `cast_max`

English:
lemma cast_max
  given: (p q : Rat>=0)
  statement: (↑(max p q) : K) = max (p : K) (q : K)
  proof: (@cast_mono K _).map_max

中文:
引理 cast_max
  条件: (p q : 有理数>=0)
  结论: (↑(最大值 p q) : K) = 最大值 (p : K) (q : K)
  证明: (@cast_mono K _).map_max
-/
@[simp, norm_cast] lemma cast_max (p q : Rat>=0) : (↑(max p q) : K) = max (p : K) (q : K) :=
  (@cast_mono K _).map_max

open Set

@[simp]
/--
theorem `preimage_cast_Icc` / 定理 `preimage_cast_Icc`

English:
theorem preimage_cast_Icc
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' Icc (p : K) q = Icc p q
  proof: castOrderEmbedding.preimage_Icc ..

@[simp]

中文:
定理 preimage_cast_Icc
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' 闭区间 (p : K) q = 闭区间 p q
  证明: castOrderEmbedding.preimage_Icc ..

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Icc, preimage_Icc
-/
theorem preimage_cast_Icc (p q : Rat>=0) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
/--
theorem `preimage_cast_Ico` / 定理 `preimage_cast_Ico`

English:
theorem preimage_cast_Ico
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' Ico (p : K) q = Ico p q
  proof: castOrderEmbedding.preimage_Ico ..

@[simp]

中文:
定理 preimage_cast_Ico
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' 左闭右开区间 (p : K) q = 左闭右开区间 p q
  证明: castOrderEmbedding.preimage_Ico ..

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ico, preimage_Ico
-/
theorem preimage_cast_Ico (p q : Rat>=0) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
/--
theorem `preimage_cast_Ioc` / 定理 `preimage_cast_Ioc`

English:
theorem preimage_cast_Ioc
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' Ioc (p : K) q = Ioc p q
  proof: castOrderEmbedding.preimage_Ioc p q

@[simp]

中文:
定理 preimage_cast_Ioc
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' 左开右闭区间 (p : K) q = 左开右闭区间 p q
  证明: castOrderEmbedding.preimage_Ioc p q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioc, preimage_Ioc
-/
theorem preimage_cast_Ioc (p q : Rat>=0) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
/--
theorem `preimage_cast_Ioo` / 定理 `preimage_cast_Ioo`

English:
theorem preimage_cast_Ioo
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' Ioo (p : K) q = Ioo p q
  proof: castOrderEmbedding.preimage_Ioo p q

@[simp]

中文:
定理 preimage_cast_Ioo
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' 开区间 (p : K) q = 开区间 p q
  证明: castOrderEmbedding.preimage_Ioo p q

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioo, preimage_Ioo
-/
theorem preimage_cast_Ioo (p q : Rat>=0) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
/--
theorem `preimage_cast_Ici` / 定理 `preimage_cast_Ici`

English:
theorem preimage_cast_Ici
  given: (p : Rat>=0)
  statement: (↑) ⁻¹' Ici (p : K) = Ici p
  proof: castOrderEmbedding.preimage_Ici p

@[simp]

中文:
定理 preimage_cast_Ici
  条件: (p : 有理数>=0)
  结论: (↑) ⁻¹' 左闭右无界区间 (p : K) = 左闭右无界区间 p
  证明: castOrderEmbedding.preimage_Ici p

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ici, preimage_Ici
-/
theorem preimage_cast_Ici (p : Rat>=0) : (↑) ⁻¹' Ici (p : K) = Ici p :=
  castOrderEmbedding.preimage_Ici p

@[simp]
/--
theorem `preimage_cast_Iic` / 定理 `preimage_cast_Iic`

English:
theorem preimage_cast_Iic
  given: (p : Rat>=0)
  statement: (↑) ⁻¹' Iic (p : K) = Iic p
  proof: castOrderEmbedding.preimage_Iic p

@[simp]

中文:
定理 preimage_cast_Iic
  条件: (p : 有理数>=0)
  结论: (↑) ⁻¹' 左无界右闭区间 (p : K) = 左无界右闭区间 p
  证明: castOrderEmbedding.preimage_Iic p

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Iic, preimage_Iic
-/
theorem preimage_cast_Iic (p : Rat>=0) : (↑) ⁻¹' Iic (p : K) = Iic p :=
  castOrderEmbedding.preimage_Iic p

@[simp]
/--
theorem `preimage_cast_Ioi` / 定理 `preimage_cast_Ioi`

English:
theorem preimage_cast_Ioi
  given: (p : Rat>=0)
  statement: (↑) ⁻¹' Ioi (p : K) = Ioi p
  proof: castOrderEmbedding.preimage_Ioi p

@[simp]

中文:
定理 preimage_cast_Ioi
  条件: (p : 有理数>=0)
  结论: (↑) ⁻¹' 左开右无界区间 (p : K) = 左开右无界区间 p
  证明: castOrderEmbedding.preimage_Ioi p

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Ioi, preimage_Ioi
-/
theorem preimage_cast_Ioi (p : Rat>=0) : (↑) ⁻¹' Ioi (p : K) = Ioi p :=
  castOrderEmbedding.preimage_Ioi p

@[simp]
/--
theorem `preimage_cast_Iio` / 定理 `preimage_cast_Iio`

English:
theorem preimage_cast_Iio
  given: (p : Rat>=0)
  statement: (↑) ⁻¹' Iio (p : K) = Iio p
  proof: castOrderEmbedding.preimage_Iio p

@[simp]

中文:
定理 preimage_cast_Iio
  条件: (p : 有理数>=0)
  结论: (↑) ⁻¹' 左无界右开区间 (p : K) = 左无界右开区间 p
  证明: castOrderEmbedding.preimage_Iio p

@[simp]

Depends on / 依赖: castOrderEmbedding, castOrderEmbedding.preimage_Iio, preimage_Iio
-/
theorem preimage_cast_Iio (p : Rat>=0) : (↑) ⁻¹' Iio (p : K) = Iio p :=
  castOrderEmbedding.preimage_Iio p

@[simp]
/--
theorem `preimage_cast_uIcc` / 定理 `preimage_cast_uIcc`

English:
theorem preimage_cast_uIcc
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' uIcc (p : K) q = uIcc p q
  proof: (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]

中文:
定理 preimage_cast_uIcc
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' uIcc (p : K) q = uIcc p q
  证明: (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]

Depends on / 依赖: castOrderEmbedding, preimage_uIcc
-/
theorem preimage_cast_uIcc (p q : Rat>=0) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
/--
theorem `preimage_cast_uIoc` / 定理 `preimage_cast_uIoc`

English:
theorem preimage_cast_uIoc
  given: (p q : Rat>=0)
  statement: (↑) ⁻¹' uIoc (p : K) q = uIoc p q
  proof: (castOrderEmbedding (K := K)).preimage_uIoc p q

中文:
定理 preimage_cast_uIoc
  条件: (p q : 有理数>=0)
  结论: (↑) ⁻¹' uIoc (p : K) q = uIoc p q
  证明: (castOrderEmbedding (K := K)).preimage_uIoc p q

Depends on / 依赖: castOrderEmbedding, preimage_uIoc
-/
theorem preimage_cast_uIoc (p q : Rat>=0) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end NNRat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for Rat.cast. -/
@[positivity Rat.cast _]
meta def evalRatCast : PositivityExt where eval {u α} _zα pα? e := do
  let ~q(@Rat.cast _ (_) ($a : Rat)) := e | throwError "not Rat.cast"
  match ← core q(inferInstance) (some q(inferInstance)) a with
| .positive pa => id
    match pα? with
    | none => do
      let _oα ← synthInstanceQ q(DivisionRing $α)
      let _cα ← synthInstanceQ q(CharZero $α)
      assumeInstancesCommute
      return .nonzero q((Rat.cast_ne_zero (α := $α)).mpr ($pa).ne')
    | some _ => do
      let _oα ← synthInstanceQ q(Field $α)
      let _oα ← synthInstanceQ q(LinearOrder $α)
      let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .positive q((Rat.cast_pos (K := $α)).mpr $pa)
| .nonnegative pa => id
    match pα? with | none => pure .none | some _ => do
    let _oα ← synthInstanceQ q(Field $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .nonnegative q((Rat.cast_nonneg (K := $α)).mpr $pa)
  | .nonzero pa =>
    let _oα ← synthInstanceQ q(DivisionRing $α)
    let _cα ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    return .nonzero q((Rat.cast_ne_zero (α := $α)).mpr $pa)
  | .none => pure .none

/-- Extension for NNRat.cast. -/
@[positivity NNRat.cast _]
meta def evalNNRatCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let ~q(@NNRat.cast _ (_) ($a : Rat>=0)) := e | throwError "not NNRat.cast"
  match ← core q(inferInstance) (some q(inferInstance)) a with
  | .positive pa =>
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .positive q((NNRat.cast_pos (K := $α)).mpr $pa)
  | _ =>
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .nonnegative q(NNRat.cast_nonneg _)

end Mathlib.Meta.Positivity
