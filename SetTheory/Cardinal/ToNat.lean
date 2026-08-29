/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Projection from cardinal numbers to natural numbers

In this file we define `Cardinal.toNat` to be the natural projection `Cardinal → ℕ`,
sending all infinite cardinals to zero.
We also prove basic lemmas about this definition.
-/

@[expose] public section

assert_not_exists Field

universe u v
open Function Set

namespace Cardinal

variable {α : Type u} {c d : Cardinal.{u}}

/--
Definition of `toNat` / `toNat` 的定义

English:
definition toNat
  signature: : Cardinal ->*₀ Nat
  body: ENat.toNatHom.comp (.ofClass toENat)

中文:
定义 to自然数
  签名: : 基数 ->*₀ 自然数
  定义体: ENat.toNatHom.comp (.ofClass toENat)

Depends on / 依赖: ENat.toNatHom.comp, ofClass, toENat, toNatHom
-/
noncomputable def toNat : Cardinal ->*₀ Nat :=
  ENat.toNatHom.comp (.ofClass toENat)

/--
lemma `toNat_toENat` / 引理 `toNat_toENat`

English:
lemma toNat_toENat
  given: (a : Cardinal)
  statement: ENat.toNat (toENat a) = toNat a
  proof: rfl

@[simp]

中文:
引理 to自然数_toE自然数
  条件: (a : 基数)
  结论: E自然数.to自然数 (toE自然数 a) = to自然数 a
  证明: rfl

@[simp]
-/
@[simp] lemma toNat_toENat (a : Cardinal) : ENat.toNat (toENat a) = toNat a := rfl

@[simp]
/--
theorem `toNat_ofENat` / 定理 `toNat_ofENat`

English:
theorem toNat_ofENat
  given: (n : Nat∞)
  statement: toNat n = ENat.toNat n
  proof: congr_arg ENat.toNat toENat_ofENat n

中文:
定理 to自然数_ofE自然数
  条件: (n : 自然数∞)
  结论: to自然数 n = E自然数.to自然数 n
  证明: congr_arg ENat.toNat toENat_ofENat n

Depends on / 依赖: ENat.toNat, congr_arg, toENat_ofENat
-/
theorem toNat_ofENat (n : Nat∞) : toNat n = ENat.toNat n :=
congr_arg ENat.toNat toENat_ofENat n

/--
theorem `toNat_natCast` / 定理 `toNat_natCast`

English:
theorem toNat_natCast
  given: (n : Nat)
  statement: toNat n = n
  proof: toNat_ofENat n

@[simp]

中文:
定理 to自然数_natCast
  条件: (n : 自然数)
  结论: to自然数 n = n
  证明: toNat_ofENat n

@[simp]
-/
@[simp, norm_cast] theorem toNat_natCast (n : Nat) : toNat n = n := toNat_ofENat n

@[simp]
/--
lemma `toNat_eq_zero` / 引理 `toNat_eq_zero`

English:
lemma toNat_eq_zero
  statement: toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
  proof: by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_zero]; rw [toENat_eq_zero]; rw [toENat_eq_top]

中文:
引理 to自然数_eq_zero
  结论: to自然数 c = 0 ↔ c = 0 ∨ ℵ₀ <= c
  证明: by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_zero]; rw [toENat_eq_zero]; rw [toENat_eq_top]

Depends on / 依赖: ENat.toNat_eq_zero, toENat_eq_top, toENat_eq_zero, toNat_eq_zero, toNat_toENat
-/
lemma toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c := by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_zero]; rw [toENat_eq_zero]; rw [toENat_eq_top]

/--
lemma `toNat_ne_zero` / 引理 `toNat_ne_zero`

English:
lemma toNat_ne_zero
  statement: toNat c != 0 ↔ c != 0 ∧ c < ℵ₀
  proof: by simp [not_or]

中文:
引理 to自然数_ne_zero
  结论: to自然数 c != 0 ↔ c != 0 ∧ c < ℵ₀
  证明: by simp [not_or]

Depends on / 依赖: not_or, pos_iff_ne_zero, pos_iff_ne_zero.trans, toNat_ne_zero, toNat_pos
-/
lemma toNat_ne_zero : toNat c != 0 ↔ c != 0 ∧ c < ℵ₀ := by simp [not_or]
/--
lemma `toNat_pos` / 引理 `toNat_pos`

English:
lemma toNat_pos
  statement: 0 < toNat c ↔ c != 0 ∧ c < ℵ₀
  proof: pos_iff_ne_zero.trans toNat_ne_zero

中文:
引理 to自然数_pos
  结论: 0 < to自然数 c ↔ c != 0 ∧ c < ℵ₀
  证明: pos_iff_ne_zero.trans toNat_ne_zero
-/
@[simp] lemma toNat_pos : 0 < toNat c ↔ c != 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans toNat_ne_zero

/--
theorem `cast_toNat_of_lt_aleph0` / 定理 `cast_toNat_of_lt_aleph0`

English:
theorem cast_toNat_of_lt_aleph0
  given: {c : Cardinal} (h : c < ℵ₀)
  statement: ↑(toNat c) = c
  proof: by
  lift c to Nat using h
  rw [toNat_natCast]

中文:
定理 cast_to自然数_of_lt_aleph0
  条件: {c : 基数} (h : c < ℵ₀)
  结论: ↑(to自然数 c) = c
  证明: by
  lift c to Nat using h
  rw [toNat_natCast]

Depends on / 依赖: toNat_natCast
-/
theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑(toNat c) = c := by
  lift c to Nat using h
  rw [toNat_natCast]

/--
theorem `toNat_apply_of_lt_aleph0` / 定理 `toNat_apply_of_lt_aleph0`

English:
theorem toNat_apply_of_lt_aleph0
  given: {c : Cardinal.{u}} (h : c < ℵ₀)
  proof: Nat.cast_injective (R := Cardinal.{u}) by
    rw [cast_toNat_of_lt_aleph0 h]; rw [← Classical.choose_spec (lt_aleph0.1 h)]

中文:
定理 to自然数_apply_of_lt_aleph0
  条件: {c : 基数.{u}} (h : c < ℵ₀)
  证明: Nat.cast_injective (R := Cardinal.{u}) by
    rw [cast_toNat_of_lt_aleph0 h]; rw [← Classical.choose_spec (lt_aleph0.1 h)]

Depends on / 依赖: Cardinal, Classical, Classical.choose_spec, Nat.cast_injective, cast_injective, cast_toNat_of_lt_aleph0, choose_spec, lt_aleph0
-/
theorem toNat_apply_of_lt_aleph0 {c : Cardinal.{u}} (h : c < ℵ₀) :
    toNat c = Classical.choose (lt_aleph0.1 h) :=
Nat.cast_injective (R := Cardinal.{u}) by
    rw [cast_toNat_of_lt_aleph0 h]; rw [← Classical.choose_spec (lt_aleph0.1 h)]

/--
theorem `toNat_apply_of_aleph0_le` / 定理 `toNat_apply_of_aleph0_le`

English:
theorem toNat_apply_of_aleph0_le
  given: {c : Cardinal} (h : ℵ₀ <= c)
  statement: toNat c = 0
  proof: by simp [h]

中文:
定理 to自然数_apply_of_aleph0_le
  条件: {c : 基数} (h : ℵ₀ <= c)
  结论: to自然数 c = 0
  证明: by simp [h]
-/
theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ <= c) : toNat c = 0 := by simp [h]

/--
theorem `cast_toNat_of_aleph0_le` / 定理 `cast_toNat_of_aleph0_le`

English:
theorem cast_toNat_of_aleph0_le
  given: {c : Cardinal} (h : ℵ₀ <= c)
  statement: ↑(toNat c) = (0 : Cardinal)
  proof: by
  rw [toNat_apply_of_aleph0_le h]; rw [Nat.cast_zero]

中文:
定理 cast_to自然数_of_aleph0_le
  条件: {c : 基数} (h : ℵ₀ <= c)
  结论: ↑(to自然数 c) = (0 : 基数)
  证明: by
  rw [toNat_apply_of_aleph0_le h]; rw [Nat.cast_zero]

Depends on / 依赖: Nat.cast_zero, cast_zero, toNat_apply_of_aleph0_le
-/
theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ <= c) : ↑(toNat c) = (0 : Cardinal) := by
  rw [toNat_apply_of_aleph0_le h]; rw [Nat.cast_zero]

/--
theorem `cast_toNat_eq_iff_lt_aleph0` / 定理 `cast_toNat_eq_iff_lt_aleph0`

English:
theorem cast_toNat_eq_iff_lt_aleph0
  given: {c : Cardinal}
  statement: toNat c = c ↔ c < ℵ₀ where
  proof: by rw [← h]; simp
  mpr := cast_toNat_of_lt_aleph0

中文:
定理 cast_to自然数_eq_iff_lt_aleph0
  条件: {c : 基数}
  结论: to自然数 c = c ↔ c < ℵ₀ where
  证明: by rw [← h]; simp
  mpr := cast_toNat_of_lt_aleph0

Depends on / 依赖: BoundedSpace, CompactSpace, cast_toNat_of_lt_aleph0, isBounded, isCompact_univ, isCompact_univ.isBounded
-/
theorem cast_toNat_eq_iff_lt_aleph0 {c : Cardinal} : toNat c = c ↔ c < ℵ₀ where
  mp h := by rw [← h]; simp
  mpr := cast_toNat_of_lt_aleph0

/--
theorem `toNat_strictMonoOn` / 定理 `toNat_strictMonoOn`

English:
theorem toNat_strictMonoOn
  statement: StrictMonoOn toNat (Iio ℵ₀)
  proof: by
  simp only [← range_natCast, StrictMonoOn, forall_mem_range, toNat_natCast, Nat.cast_lt]
  exact fun _ _ => id

中文:
定理 to自然数_strictMonoOn
  结论: StrictMonoOn to自然数 (左无界右开区间 ℵ₀)
  证明: by
  simp only [← range_natCast, StrictMonoOn, forall_mem_range, toNat_natCast, Nat.cast_lt]
  exact fun _ _ => id

Depends on / 依赖: Nat.cast_lt, StrictMonoOn, cast_lt, forall_mem_range, range_natCast, toNat_natCast
-/
theorem toNat_strictMonoOn : StrictMonoOn toNat (Iio ℵ₀) := by
  simp only [← range_natCast, StrictMonoOn, forall_mem_range, toNat_natCast, Nat.cast_lt]
  exact fun _ _ => id

/--
theorem `toNat_monotoneOn` / 定理 `toNat_monotoneOn`

English:
theorem toNat_monotoneOn
  statement: MonotoneOn toNat (Iio ℵ₀)
  proof: toNat_strictMonoOn.monotoneOn

中文:
定理 to自然数_monotoneOn
  结论: MonotoneOn to自然数 (左无界右开区间 ℵ₀)
  证明: toNat_strictMonoOn.monotoneOn

Depends on / 依赖: monotoneOn, toNat_strictMonoOn, toNat_strictMonoOn.monotoneOn
-/
theorem toNat_monotoneOn : MonotoneOn toNat (Iio ℵ₀) := toNat_strictMonoOn.monotoneOn

/--
theorem `toNat_injOn` / 定理 `toNat_injOn`

English:
theorem toNat_injOn
  statement: InjOn toNat (Iio ℵ₀)
  proof: toNat_strictMonoOn.injOn

中文:
定理 to自然数_injOn
  结论: 单射限制 to自然数 (左无界右开区间 ℵ₀)
  证明: toNat_strictMonoOn.injOn

Depends on / 依赖: toNat_strictMonoOn, toNat_strictMonoOn.injOn
-/
theorem toNat_injOn : InjOn toNat (Iio ℵ₀) := toNat_strictMonoOn.injOn

/--
theorem `toNat_inj_of_lt_aleph0` / 定理 `toNat_inj_of_lt_aleph0`

English:
theorem toNat_inj_of_lt_aleph0
  given: (hc : c < ℵ₀) (hd : d < ℵ₀)
  proof: toNat_injOn.eq_iff hc hd

中文:
定理 to自然数_inj_of_lt_aleph0
  条件: (hc : c < ℵ₀) (hd : d < ℵ₀)
  证明: toNat_injOn.eq_iff hc hd

Depends on / 依赖: eq_iff, toNat_injOn, toNat_injOn.eq_iff
-/
theorem toNat_inj_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c = toNat d ↔ c = d :=
  toNat_injOn.eq_iff hc hd

/--
theorem `toNat_le_iff_le_of_lt_aleph0` / 定理 `toNat_le_iff_le_of_lt_aleph0`

English:
theorem toNat_le_iff_le_of_lt_aleph0
  given: (hc : c < ℵ₀) (hd : d < ℵ₀)
  proof: toNat_strictMonoOn.le_iff_le hc hd

中文:
定理 to自然数_le_iff_le_of_lt_aleph0
  条件: (hc : c < ℵ₀) (hd : d < ℵ₀)
  证明: toNat_strictMonoOn.le_iff_le hc hd

Depends on / 依赖: le_iff_le, toNat_strictMonoOn, toNat_strictMonoOn.le_iff_le
-/
theorem toNat_le_iff_le_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c <= toNat d ↔ c <= d :=
  toNat_strictMonoOn.le_iff_le hc hd

/--
theorem `toNat_lt_iff_lt_of_lt_aleph0` / 定理 `toNat_lt_iff_lt_of_lt_aleph0`

English:
theorem toNat_lt_iff_lt_of_lt_aleph0
  given: (hc : c < ℵ₀) (hd : d < ℵ₀)
  proof: toNat_strictMonoOn.lt_iff_lt hc hd

@[gcongr]

中文:
定理 to自然数_lt_iff_lt_of_lt_aleph0
  条件: (hc : c < ℵ₀) (hd : d < ℵ₀)
  证明: toNat_strictMonoOn.lt_iff_lt hc hd

@[gcongr]

Depends on / 依赖: lt_iff_lt, toNat_strictMonoOn, toNat_strictMonoOn.lt_iff_lt
-/
theorem toNat_lt_iff_lt_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c < toNat d ↔ c < d :=
  toNat_strictMonoOn.lt_iff_lt hc hd

@[gcongr]
/--
theorem `toNat_le_toNat` / 定理 `toNat_le_toNat`

English:
theorem toNat_le_toNat
  given: (hcd : c <= d) (hd : d < ℵ₀)
  statement: toNat c <= toNat d
  proof: toNat_monotoneOn (hcd.trans_lt hd) hd hcd

中文:
定理 to自然数_le_to自然数
  条件: (hcd : c <= d) (hd : d < ℵ₀)
  结论: to自然数 c <= to自然数 d
  证明: toNat_monotoneOn (hcd.trans_lt hd) hd hcd

Depends on / 依赖: hcd.trans_lt, toNat_monotoneOn, trans_lt
-/
theorem toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : toNat c <= toNat d :=
  toNat_monotoneOn (hcd.trans_lt hd) hd hcd

/--
theorem `toNat_lt_toNat` / 定理 `toNat_lt_toNat`

English:
theorem toNat_lt_toNat
  given: (hcd : c < d) (hd : d < ℵ₀)
  statement: toNat c < toNat d
  proof: toNat_strictMonoOn (hcd.trans hd) hd hcd

@[simp]

中文:
定理 to自然数_lt_to自然数
  条件: (hcd : c < d) (hd : d < ℵ₀)
  结论: to自然数 c < to自然数 d
  证明: toNat_strictMonoOn (hcd.trans hd) hd hcd

@[simp]

Depends on / 依赖: hcd.trans, toNat_strictMonoOn
-/
theorem toNat_lt_toNat (hcd : c < d) (hd : d < ℵ₀) : toNat c < toNat d :=
  toNat_strictMonoOn (hcd.trans hd) hd hcd

@[simp]
/--
theorem `toNat_ofNat` / 定理 `toNat_ofNat`

English:
theorem toNat_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: toNat_natCast n

中文:
定理 to自然数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: toNat_natCast n

Depends on / 依赖: toNat_natCast
-/
theorem toNat_ofNat (n : Nat) [n.AtLeastTwo] :
    Cardinal.toNat ofNat(n) = OfNat.ofNat n :=
  toNat_natCast n

/--
theorem `toNat_rightInverse` / 定理 `toNat_rightInverse`

English:
theorem toNat_rightInverse
  statement: Function.RightInverse ((↑) : Nat -> Cardinal) toNat
  proof: toNat_natCast

中文:
定理 to自然数_rightInverse
  结论: 函数.右逆 ((↑) : 自然数 -> 基数) to自然数
  证明: toNat_natCast

Depends on / 依赖: toNat_natCast
-/
theorem toNat_rightInverse : Function.RightInverse ((↑) : Nat -> Cardinal) toNat :=
  toNat_natCast

/--
theorem `toNat_surjective` / 定理 `toNat_surjective`

English:
theorem toNat_surjective
  statement: Surjective toNat
  proof: toNat_rightInverse.surjective

@[simp]

中文:
定理 to自然数_surjective
  结论: 满射 to自然数
  证明: toNat_rightInverse.surjective

@[simp]

Depends on / 依赖: surjective, toNat_rightInverse, toNat_rightInverse.surjective
-/
theorem toNat_surjective : Surjective toNat :=
  toNat_rightInverse.surjective

@[simp]
/--
theorem `mk_toNat_of_infinite` / 定理 `mk_toNat_of_infinite`

English:
theorem mk_toNat_of_infinite
  given: [h : Infinite α]
  statement: toNat #α = 0
  proof: by simp

@[simp]

中文:
定理 mk_to自然数_of_infinite
  条件: [h : 无限 α]
  结论: to自然数 #α = 0
  证明: by simp

@[simp]
-/
theorem mk_toNat_of_infinite [h : Infinite α] : toNat #α = 0 := by simp

@[simp]
/--
theorem `aleph0_toNat` / 定理 `aleph0_toNat`

English:
theorem aleph0_toNat
  statement: toNat ℵ₀ = 0
  proof: toNat_apply_of_aleph0_le le_rfl

中文:
定理 aleph0_to自然数
  结论: to自然数 ℵ₀ = 0
  证明: toNat_apply_of_aleph0_le le_rfl

Depends on / 依赖: le_rfl, toNat_apply_of_aleph0_le
-/
theorem aleph0_toNat : toNat ℵ₀ = 0 :=
  toNat_apply_of_aleph0_le le_rfl

/--
theorem `mk_toNat_eq_card` / 定理 `mk_toNat_eq_card`

English:
theorem mk_toNat_eq_card
  given: [Fintype α]
  statement: toNat #α = Fintype.card α
  proof: by simp

@[simp]

中文:
定理 mk_to自然数_eq_card
  条件: [有限类型 α]
  结论: to自然数 #α = 有限类型.card α
  证明: by simp

@[simp]
-/
theorem mk_toNat_eq_card [Fintype α] : toNat #α = Fintype.card α := by simp

@[simp]
/--
theorem `zero_toNat` / 定理 `zero_toNat`

English:
theorem zero_toNat
  statement: toNat 0 = 0
  proof: map_zero _

中文:
定理 zero_to自然数
  结论: to自然数 0 = 0
  证明: map_zero _

Depends on / 依赖: map_zero
-/
theorem zero_toNat : toNat 0 = 0 := map_zero _

/--
theorem `one_toNat` / 定理 `one_toNat`

English:
theorem one_toNat
  statement: toNat 1 = 1
  proof: map_one _

中文:
定理 one_to自然数
  结论: to自然数 1 = 1
  证明: map_one _

Depends on / 依赖: map_one
-/
theorem one_toNat : toNat 1 = 1 := map_one _

/--
theorem `toNat_eq_iff` / 定理 `toNat_eq_iff`

English:
theorem toNat_eq_iff
  given: {n : Nat} (hn : n != 0)
  statement: toNat c = n ↔ c = n
  proof: by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_iff hn]; rw [toENat_eq_natCast]

中文:
定理 to自然数_eq_iff
  条件: {n : 自然数} (hn : n != 0)
  结论: to自然数 c = n ↔ c = n
  证明: by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_iff hn]; rw [toENat_eq_natCast]

Depends on / 依赖: ENat.toNat_eq_iff, toENat_eq_natCast, toNat_eq_iff, toNat_toENat
-/
theorem toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = n ↔ c = n := by
  rw [← toNat_toENat]; rw [ENat.toNat_eq_iff hn]; rw [toENat_eq_natCast]

/--
theorem `toNat_eq_ofNat` / 定理 `toNat_eq_ofNat`

English:
theorem toNat_eq_ofNat
  given: {n : Nat} [Nat.AtLeastTwo n]
  proof: toNat_eq_iff OfNat.ofNat_ne_zero n

@[simp]

中文:
定理 to自然数_eq_of自然数
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  证明: toNat_eq_iff OfNat.ofNat_ne_zero n

@[simp]

Depends on / 依赖: OfNat.ofNat_ne_zero, ofNat_ne_zero, toNat_eq_iff
-/
theorem toNat_eq_ofNat {n : Nat} [Nat.AtLeastTwo n] :
    toNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n :=
toNat_eq_iff OfNat.ofNat_ne_zero n

@[simp]
/--
theorem `toNat_eq_one` / 定理 `toNat_eq_one`

English:
theorem toNat_eq_one
  statement: toNat c = 1 ↔ c = 1
  proof: by
  rw [toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]

中文:
定理 to自然数_eq_one
  结论: to自然数 c = 1 ↔ c = 1
  证明: by
  rw [toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]

Depends on / 依赖: Nat.cast_one, cast_one, one_ne_zero, toNat_eq_iff
-/
theorem toNat_eq_one : toNat c = 1 ↔ c = 1 := by
  rw [toNat_eq_iff one_ne_zero]; rw [Nat.cast_one]

/--
theorem `toNat_eq_one_iff_unique` / 定理 `toNat_eq_one_iff_unique`

English:
theorem toNat_eq_one_iff_unique
  statement: toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α
  proof: toNat_eq_one.trans eq_one_iff_unique

@[simp]

中文:
定理 to自然数_eq_one_iff_unique
  结论: to自然数 #α = 1 ↔ 子单例 α ∧ 非空 α
  证明: toNat_eq_one.trans eq_one_iff_unique

@[simp]

Depends on / 依赖: eq_one_iff_unique, toNat_eq_one, toNat_eq_one.trans
-/
theorem toNat_eq_one_iff_unique : toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique

@[simp]
/--
theorem `toNat_lift` / 定理 `toNat_lift`

English:
theorem toNat_lift
  given: (c : Cardinal.{v})
  statement: toNat (lift.{u, v} c) = toNat c
  proof: by
  simp only [← toNat_toENat, toENat_lift]

中文:
定理 to自然数_lift
  条件: (c : 基数.{v})
  结论: to自然数 (lift.{u, v} c) = to自然数 c
  证明: by
  simp only [← toNat_toENat, toENat_lift]

Depends on / 依赖: toENat_lift, toNat_toENat
-/
theorem toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} c) = toNat c := by
  simp only [← toNat_toENat, toENat_lift]

/--
theorem `toNat_congr` / 定理 `toNat_congr`

English:
theorem toNat_congr
  given: {β : Type v} (e : α ≃ β)
  statement: toNat #α = toNat #β
  proof: by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift]; rw [(lift_mk_eq.{_]; rw [_]; rw [v}).mpr ⟨e⟩]; rw [toNat_lift]

中文:
定理 to自然数_congr
  条件: {β : 类型v} (e : α ≃ β)
  结论: to自然数 #α = to自然数 #β
  证明: by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift]; rw [(lift_mk_eq.{_]; rw [_]; rw [v}).mpr ⟨e⟩]; rw [toNat_lift]
-/
theorem toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = toNat #β := by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift]; rw [(lift_mk_eq.{_]; rw [_]; rw [v}).mpr ⟨e⟩]; rw [toNat_lift]

/--
theorem `toNat_mul` / 定理 `toNat_mul`

English:
theorem toNat_mul
  given: (x y : Cardinal)
  statement: toNat (x * y) = toNat x * toNat y
  proof: map_mul toNat x y

@[simp]

中文:
定理 to自然数_mul
  条件: (x y : 基数)
  结论: to自然数 (x * y) = to自然数 x * to自然数 y
  证明: map_mul toNat x y

@[simp]

Depends on / 依赖: map_mul
-/
theorem toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x * toNat y := map_mul toNat x y

@[simp]
/--
theorem `toNat_add` / 定理 `toNat_add`

English:
theorem toNat_add
  given: (hc : c < ℵ₀) (hd : d < ℵ₀)
  statement: toNat (c + d) = toNat c + toNat d
  proof: by
  lift c to Nat using hc
  lift d to Nat using hd
  norm_cast

中文:
定理 to自然数_add
  条件: (hc : c < ℵ₀) (hd : d < ℵ₀)
  结论: to自然数 (c + d) = to自然数 c + to自然数 d
  证明: by
  lift c to Nat using hc
  lift d to Nat using hd
  norm_cast
-/
theorem toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d) = toNat c + toNat d := by
  lift c to Nat using hc
  lift d to Nat using hd
  norm_cast

/--
theorem `toNat_lift_add_lift` / 定理 `toNat_lift_add_lift`

English:
theorem toNat_lift_add_lift
  given: {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀)
  proof: by
  simp [*]

@[simp]

中文:
定理 to自然数_lift_add_lift
  条件: {a : 基数.{u}} {b : 基数.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀)
  证明: by
  simp [*]

@[simp]
-/
theorem toNat_lift_add_lift {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    toNat (lift.{v} a + lift.{u} b) = toNat a + toNat b := by
  simp [*]

@[simp]
/--
lemma `natCast_toNat_le` / 引理 `natCast_toNat_le`

English:
lemma natCast_toNat_le
  given: (a : Cardinal)
  statement: (toNat a : Cardinal) <= a
  proof: by
  obtain h | h := lt_or_ge a ℵ₀
  · simp [cast_toNat_of_lt_aleph0 h]
  · simp [Cardinal.toNat_apply_of_aleph0_le h]

中文:
引理 natCast_to自然数_le
  条件: (a : 基数)
  结论: (to自然数 a : 基数) <= a
  证明: by
  obtain h | h := lt_or_ge a ℵ₀
  · simp [cast_toNat_of_lt_aleph0 h]
  · simp [Cardinal.toNat_apply_of_aleph0_le h]

Depends on / 依赖: Cardinal, Cardinal.toNat_apply_of_aleph0_le, cast_toNat_of_lt_aleph0, lt_or_ge, toNat_apply_of_aleph0_le
-/
lemma natCast_toNat_le (a : Cardinal) : (toNat a : Cardinal) <= a := by
  obtain h | h := lt_or_ge a ℵ₀
  · simp [cast_toNat_of_lt_aleph0 h]
  · simp [Cardinal.toNat_apply_of_aleph0_le h]

/--
lemma `toNat_le_iff_of_lt_aleph0` / 引理 `toNat_le_iff_of_lt_aleph0`

English:
lemma toNat_le_iff_of_lt_aleph0
  given: {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.aleph0)
  proof: by
  nth_rw 1 [← Cardinal.toNat_natCast.{u} n,
    Cardinal.toNat_le_iff_le_of_lt_aleph0 lt (Cardinal.natCast_lt_aleph0)]

中文:
引理 to自然数_le_iff_of_lt_aleph0
  条件: {a : 基数.{u}} (n : 自然数) (lt : a < 基数.aleph0)
  证明: by
  nth_rw 1 [← Cardinal.toNat_natCast.{u} n,
    Cardinal.toNat_le_iff_le_of_lt_aleph0 lt (Cardinal.natCast_lt_aleph0)]

Depends on / 依赖: Cardinal, Cardinal.natCast_lt_aleph0, Cardinal.toNat_le_iff_le_of_lt_aleph0, Cardinal.toNat_natCast, natCast_lt_aleph0, nth_rw, toNat_le_iff_le_of_lt_aleph0, toNat_natCast
-/
lemma toNat_le_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.aleph0) :
    a.toNat <= n ↔ a <= n := by
  nth_rw 1 [← Cardinal.toNat_natCast.{u} n,
    Cardinal.toNat_le_iff_le_of_lt_aleph0 lt (Cardinal.natCast_lt_aleph0)]

/--
lemma `toNat_eq_iff_of_lt_aleph0` / 引理 `toNat_eq_iff_of_lt_aleph0`

English:
lemma toNat_eq_iff_of_lt_aleph0
  given: {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.aleph0)
  proof: by
  nth_rw 2 [← Cardinal.cast_toNat_of_lt_aleph0 lt]
  exact Nat.cast_inj.symm

中文:
引理 to自然数_eq_iff_of_lt_aleph0
  条件: {a : 基数.{u}} (n : 自然数) (lt : a < 基数.aleph0)
  证明: by
  nth_rw 2 [← Cardinal.cast_toNat_of_lt_aleph0 lt]
  exact Nat.cast_inj.symm

Depends on / 依赖: Cardinal, Cardinal.cast_toNat_of_lt_aleph0, Nat.cast_inj.symm, cast_inj, cast_toNat_of_lt_aleph0, nth_rw
-/
lemma toNat_eq_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.aleph0) :
    a.toNat = n ↔ a = n := by
  nth_rw 2 [← Cardinal.cast_toNat_of_lt_aleph0 lt]
  exact Nat.cast_inj.symm

/--
theorem `toNat_eq_of_forall_le_iff` / 定理 `toNat_eq_of_forall_le_iff`

English:
theorem toNat_eq_of_forall_le_iff
  statement: {c : Cardinal.{u}} {d : Cardinal.{v}}
  proof: by
  have h' := forall_congr' h
  rw [← Cardinal.aleph0_le]; rw [← Cardinal.aleph0_le] at h'
  rcases iff_iff_and_or_not_and_not.mp h' with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · simp [Cardinal.toNat_apply_of_aleph0_le, hc, hd]
  · apply eq_of_forall_le_iff
    rw [← cast_toNat_of_lt_aleph0 (not_le.mp hc)]; rw [← 

中文:
定理 to自然数_eq_of_对任意_le_iff
  结论: {c : 基数.{u}} {d : 基数.{v}}
  证明: by
  have h' := forall_congr' h
  rw [← Cardinal.aleph0_le]; rw [← Cardinal.aleph0_le] at h'
  rcases iff_iff_and_or_not_and_not.mp h' with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · simp [Cardinal.toNat_apply_of_aleph0_le, hc, hd]
  · apply eq_of_forall_le_iff
    rw [← cast_toNat_of_lt_aleph0 (not_le.mp hc)]; rw [← 

Depends on / 依赖: Cardinal, Cardinal.aleph0_le, Cardinal.toNat_apply_of_aleph0_le, aleph0_le, cast_toNat_of_lt_aleph0, eq_of_forall_le_iff, forall_congr, iff_iff_and_or_not_and_not, iff_iff_and_or_not_and_not.mp, not_le, not_le.mp, toNat_apply_of_aleph0_le
-/
theorem toNat_eq_of_forall_le_iff {c : Cardinal.{u}} {d : Cardinal.{v}}
    (h : forall n : Nat, n <= c ↔ n <= d) : c.toNat = d.toNat := by
  have h' := forall_congr' h
  rw [← Cardinal.aleph0_le]; rw [← Cardinal.aleph0_le] at h'
  rcases iff_iff_and_or_not_and_not.mp h' with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · simp [Cardinal.toNat_apply_of_aleph0_le, hc, hd]
  · apply eq_of_forall_le_iff
    rw [← cast_toNat_of_lt_aleph0 (not_le.mp hc)]; rw [← cast_toNat_of_lt_aleph0 (not_le.mp hd)] at h
    simpa using h

end Cardinal
