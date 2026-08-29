/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/

@[expose] public section

open Set

universe u v w

namespace Valuation

section Ring

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)

/--
Definition of `integer` / `integer` 的定义

English:
definition integer
  signature: : Subring R where
  body: { x | v x <= 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, map_mul, mul_le_one' hx hy]
  zero_mem' := by simp
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at hx; simpa only [Set.mem_ofPred_eq, map_neg]

中文:
定义 integer
  签名: : 子环 R where
  定义体: { x | v x <= 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, map_mul, mul_le_one' hx hy]
  zero_mem' := by simp
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at hx; simpa only [Set.mem_ofPred_eq, map_neg]
-/
def integer : Subring R where
  carrier := { x | v x <= 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, map_mul, mul_le_one' hx hy]
  zero_mem' := by simp
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at hx; simpa only [Set.mem_ofPred_eq, map_neg]

/--
lemma `mem_integer_iff` / 引理 `mem_integer_iff`

English:
lemma mem_integer_iff
  given: (r : R)
  statement: r in v.integer ↔ v r <= 1
  proof: by rfl

中文:
引理 mem_integer_iff
  条件: (r : R)
  结论: r in v.integer ↔ v r <= 1
  证明: by rfl
-/
lemma mem_integer_iff (r : R) : r in v.integer ↔ v r <= 1 := by rfl

end Ring

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
variable (O : Type w) [CommRing O] [Algebra O R]

/--
Definition of `Integers` / `Integers` 的定义

English:
structure Integers
  parameters: : Prop where
  axioms and operations (3):
    - hom_inj : Function.Injective (algebraMap O R)
    - map_le_one : forall x, v (algebraMap O R x) <= 1
    - exists_of_le_one : forall ⦃r⦄, v r <= 1 -> exists x, algebraMap O R x = r

中文:
结构 整数egers
  参数: : 命题 where
  公理与运算 (3 个):
    - hom_inj : 函数.单射 (algebraMap O R)
    - map_le_one : 对任意 x, v (algebraMap O R x) <= 1
    - exists_of_le_one : 对任意 ⦃r⦄, v r <= 1 -> 存在 x, algebraMap O R x = r
-/
structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : forall x, v (algebraMap O R x) <= 1
  exists_of_le_one : forall ⦃r⦄, v r <= 1 -> exists x, algebraMap O R x = r

-- typeclass shortcut
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra v.integer R
  body: inferInstance

中文:
实例 :
  签名: 代数 v.integer R
  定义体: inferInstance
-/
instance : Algebra v.integer R :=
  inferInstance

/--
theorem `integer.integers` / 定理 `integer.integers`

English:
theorem integer.integers
  statement: v.Integers v.integer
  proof: { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

中文:
定理 integer.integers
  结论: v.整数egers v.integer
  证明: { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, exists_of_le_one, hom_inj, map_le_one
-/
theorem integer.integers : v.Integers v.integer :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

namespace Integers

variable {v O}

/--
theorem `one_of_isUnit'` / 定理 `one_of_isUnit'`

English:
theorem one_of_isUnit'
  given: {x : O} (hx : IsUnit x) (H : forall x, v (algebraMap O R x) <= 1)
  proof: let ⟨u, hu⟩ := hx
le_antisymm (H _) by
    grw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul, H (u⁻¹ : Units O)]

中文:
定理 one_of_isUnit'
  条件: {x : O} (hx : 是单位 x) (H : 对任意 x, v (algebraMap O R x) <= 1)
  证明: let ⟨u, hu⟩ := hx
le_antisymm (H _) by
    grw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul, H (u⁻¹ : Units O)]

Depends on / 依赖: algebraMap, le_antisymm, map_mul, map_one, mul_inv, mul_one, u.mul_inv, v.map_mul, v.map_one
-/
theorem one_of_isUnit' {x : O} (hx : IsUnit x) (H : forall x, v (algebraMap O R x) <= 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
le_antisymm (H _) by
    grw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul, H (u⁻¹ : Units O)]

/--
theorem `one_of_isUnit` / 定理 `one_of_isUnit`

English:
theorem one_of_isUnit
  given: (hv : Integers v O) {x : O} (hx : IsUnit x)
  statement: v (algebraMap O R x) = 1
  proof: one_of_isUnit' hx hv.map_le_one

中文:
定理 one_of_isUnit
  条件: (hv : 整数egers v O) {x : O} (hx : 是单位 x)
  结论: v (algebraMap O R x) = 1
  证明: one_of_isUnit' hx hv.map_le_one

Depends on / 依赖: hv.map_le_one, map_le_one, one_of_isUnit
-/
theorem one_of_isUnit (hv : Integers v O) {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  one_of_isUnit' hx hv.map_le_one

/--
theorem `isUnit_of_one` / 定理 `isUnit_of_one`

English:
theorem isUnit_of_one
  statement: (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
  proof: let ⟨u, hu⟩ := hx
  have h1 : v u <= 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) <= 1 := by
    rw [← one_mul (v _)]; rw [← hvx]; rw [← v.map_mul]; rw [← hu]; rw [u.mul_inv]; rw [hu]; rw [hvx]; rw [v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
⟨⟨r1, r2, hv.1 by rw [map_mul, map_one, hr1, hr2, Units.mul_inv],
hv.1 by rw [map_mul, map_one, hr1, hr2, Units.inv_mul]⟩,
hv.1 hr1.trans hu⟩

中文:
定理 isUnit_of_one
  结论: (hv : 整数egers v O) {x : O} (hx : 是单位 (algebraMap O R x))
  证明: let ⟨u, hu⟩ := hx
  have h1 : v u <= 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) <= 1 := by
    rw [← one_mul (v _)]; rw [← hvx]; rw [← v.map_mul]; rw [← hu]; rw [u.mul_inv]; rw [hu]; rw [hvx]; rw [v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
⟨⟨r1, r2, hv.1 by rw [map_mul, map_one, hr1, hr2, Units.mul_inv],
hv.1 by rw [map_mul, map_one, hr1, hr2, Units.inv_mul]⟩,
hv.1 hr1.trans hu⟩

Depends on / 依赖: Units.inv_mul, Units.mul_inv, hr1.trans, hu.symm, inv_mul, map_mul, map_one, mul_inv, one_mul, u.mul_inv, v.map_mul, v.map_one
-/
theorem isUnit_of_one (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
    (hvx : v (algebraMap O R x) = 1) : IsUnit x :=
  let ⟨u, hu⟩ := hx
  have h1 : v u <= 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) <= 1 := by
    rw [← one_mul (v _)]; rw [← hvx]; rw [← v.map_mul]; rw [← hu]; rw [u.mul_inv]; rw [hu]; rw [hvx]; rw [v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
⟨⟨r1, r2, hv.1 by rw [map_mul, map_one, hr1, hr2, Units.mul_inv],
hv.1 by rw [map_mul, map_one, hr1, hr2, Units.inv_mul]⟩,
hv.1 hr1.trans hu⟩

/--
theorem `le_of_dvd` / 定理 `le_of_dvd`

English:
theorem le_of_dvd
  given: (hv : Integers v O) {x y : O} (h : x ∣ y)
  proof: by
  obtain ⟨z, rfl⟩ := h
  grw [← mul_one (v (algebraMap O R x)), map_mul, v.map_mul, hv.2 z]

中文:
定理 le_of_dvd
  条件: (hv : 整数egers v O) {x y : O} (h : x ∣ y)
  证明: by
  obtain ⟨z, rfl⟩ := h
  grw [← mul_one (v (algebraMap O R x)), map_mul, v.map_mul, hv.2 z]

Depends on / 依赖: algebraMap, map_mul, mul_one, v.map_mul
-/
theorem le_of_dvd (hv : Integers v O) {x y : O} (h : x ∣ y) :
    v (algebraMap O R y) <= v (algebraMap O R x) := by
  obtain ⟨z, rfl⟩ := h
  grw [← mul_one (v (algebraMap O R x)), map_mul, v.map_mul, hv.2 z]

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  given: (hv : v.Integers O)
  statement: Nontrivial O ↔ Nontrivial R
  proof: by
  constructor <;> intro h
  · exact hv.hom_inj.nontrivial
  · obtain ⟨o0, ho0⟩ := hv.exists_of_le_one (r := 0) (by simp)
    obtain ⟨o1, ho1⟩ := hv.exists_of_le_one (r := 1) (by simp)
    refine ⟨o0, o1, ?_⟩
    rintro rfl
    simp [ho1] at ho0

中文:
引理 nontrivial_iff
  条件: (hv : v.整数egers O)
  结论: 非平凡 O ↔ 非平凡 R
  证明: by
  constructor <;> intro h
  · exact hv.hom_inj.nontrivial
  · obtain ⟨o0, ho0⟩ := hv.exists_of_le_one (r := 0) (by simp)
    obtain ⟨o1, ho1⟩ := hv.exists_of_le_one (r := 1) (by simp)
    refine ⟨o0, o1, ?_⟩
    rintro rfl
    simp [ho1] at ho0

Depends on / 依赖: exists_of_le_one, hom_inj, hv.exists_of_le_one, hv.hom_inj.nontrivial, nontrivial
-/
lemma nontrivial_iff (hv : v.Integers O) : Nontrivial O ↔ Nontrivial R := by
  constructor <;> intro h
  · exact hv.hom_inj.nontrivial
  · obtain ⟨o0, ho0⟩ := hv.exists_of_le_one (r := 0) (by simp)
    obtain ⟨o1, ho1⟩ := hv.exists_of_le_one (r := 1) (by simp)
    refine ⟨o0, o1, ?_⟩
    rintro rfl
    simp [ho1] at ho0

end Integers

/--
theorem `IsTrivialOn.of_le_one` / 定理 `IsTrivialOn.of_le_one`

English:
theorem IsTrivialOn.of_le_one
  statement: {k : Type*} [Field k] [Algebra k R] (v : Valuation R Γ₀)
  proof: Valuation.Integers.one_of_isUnit' (IsUnit.mk0 a ha) hle

中文:
定理 是TrivialOn.of_le_one
  结论: {k : 类型} [域 k] [代数 k R] (v : 赋值 R Γ₀)
  证明: Valuation.Integers.one_of_isUnit' (IsUnit.mk0 a ha) hle

Depends on / 依赖: Integers, IsUnit, IsUnit.mk0, Valuation, Valuation.Integers.one_of_isUnit, one_of_isUnit
-/
theorem IsTrivialOn.of_le_one {k : Type*} [Field k] [Algebra k R] (v : Valuation R Γ₀)
    (hle : forall (x : k), v (algebraMap k R x) <= 1) : v.IsTrivialOn k where
  eq_one a ha := Valuation.Integers.one_of_isUnit' (IsUnit.mk0 a ha) hle

/--
lemma `integers_nontrivial` / 引理 `integers_nontrivial`

English:
lemma integers_nontrivial
  given: (v : Valuation R Γ₀)
  proof: (Valuation.integer.integers v).nontrivial_iff

中文:
引理 integers_nontrivial
  条件: (v : 赋值 R Γ₀)
  证明: (Valuation.integer.integers v).nontrivial_iff

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, nontrivial_iff
-/
lemma integers_nontrivial (v : Valuation R Γ₀) :
    Nontrivial v.integer ↔ Nontrivial R :=
  (Valuation.integer.integers v).nontrivial_iff

end CommRing

section Field

variable {F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {O : Type w} [CommRing O] [Algebra O F]

namespace Integers

/--
theorem `dvd_of_le` / 定理 `dvd_of_le`

English:
theorem dvd_of_le
  statement: (hv : Integers v O) {x y : O}
  proof: by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
hv.1
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y != 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) <= 1 := by
      grw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul, h]
    let ⟨z, hz⟩ := hv.3 this
⟨z, hv.1 ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

中文:
定理 dvd_of_le
  结论: (hv : 整数egers v O) {x y : O}
  证明: by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
hv.1
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y != 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) <= 1 := by
      grw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul, h]
    let ⟨z, hz⟩ := hv.3 this
⟨z, hv.1 ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

Depends on / 依赖: algebraMap, dvd_zero, hx.symm, hz.symm, le_zero_iff, map_mul, map_one, map_zero, map_zero.symm, v.map_mul, v.map_one, v.map_zero, v.zero_iff, zero_iff
-/
theorem dvd_of_le (hv : Integers v O) {x y : O}
    (h : v (algebraMap O F x) <= v (algebraMap O F y)) : y ∣ x :=
  by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
hv.1
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y != 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) <= 1 := by
      grw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul, h]
    let ⟨z, hz⟩ := hv.3 this
⟨z, hv.1 ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

/--
theorem `dvd_iff_le` / 定理 `dvd_iff_le`

English:
theorem dvd_iff_le
  given: (hv : Integers v O) {x y : O}
  proof: ⟨hv.le_of_dvd, hv.dvd_of_le⟩

中文:
定理 dvd_iff_le
  条件: (hv : 整数egers v O) {x y : O}
  证明: ⟨hv.le_of_dvd, hv.dvd_of_le⟩

Depends on / 依赖: dvd_of_le, hv.dvd_of_le, hv.le_of_dvd, le_of_dvd
-/
theorem dvd_iff_le (hv : Integers v O) {x y : O} :
    x ∣ y ↔ v (algebraMap O F y) <= v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩

/--
theorem `le_iff_dvd` / 定理 `le_iff_dvd`

English:
theorem le_iff_dvd
  given: (hv : Integers v O) {x y : O}
  proof: ⟨hv.dvd_of_le, hv.le_of_dvd⟩

中文:
定理 le_iff_dvd
  条件: (hv : 整数egers v O) {x y : O}
  证明: ⟨hv.dvd_of_le, hv.le_of_dvd⟩

Depends on / 依赖: dvd_of_le, hv.dvd_of_le, hv.le_of_dvd, le_of_dvd
-/
theorem le_iff_dvd (hv : Integers v O) {x y : O} :
    v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩

/--
theorem `isUnit_of_one'` / 定理 `isUnit_of_one'`

English:
theorem isUnit_of_one'
  given: (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1)
  statement: IsUnit x
  proof: by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]

中文:
定理 isUnit_of_one'
  条件: (hv : 整数egers v O) {x : O} (hvx : v (algebraMap O F x) = 1)
  结论: 是单位 x
  证明: by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]

Depends on / 依赖: IsUnit, IsUnit.mk0, isUnit_of_one, ne_eq, ne_zero_iff, not_false_eq_true, one_ne_zero, v.ne_zero_iff
-/
theorem isUnit_of_one' (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1) : IsUnit x := by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]

/--
lemma `isUnit_iff_valuation_eq_one` / 引理 `isUnit_iff_valuation_eq_one`

English:
lemma isUnit_iff_valuation_eq_one
  given: (hv : Integers v O) {x : O}
  proof: ⟨hv.one_of_isUnit, hv.isUnit_of_one'⟩

中文:
引理 isUnit_iff_valuation_eq_one
  条件: (hv : 整数egers v O) {x : O}
  证明: ⟨hv.one_of_isUnit, hv.isUnit_of_one'⟩

Depends on / 依赖: hv.isUnit_of_one, hv.one_of_isUnit, isUnit_of_one, one_of_isUnit
-/
lemma isUnit_iff_valuation_eq_one (hv : Integers v O) {x : O} :
    IsUnit x ↔ v (algebraMap O F x) = 1 :=
  ⟨hv.one_of_isUnit, hv.isUnit_of_one'⟩

/--
lemma `valuation_irreducible_lt_one` / 引理 `valuation_irreducible_lt_one`

English:
lemma valuation_irreducible_lt_one
  given: (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ)
  proof: lt_of_le_of_ne (hv.map_le_one ϖ) (mt hv.isUnit_iff_valuation_eq_one.mpr h.not_isUnit)

中文:
引理 valuation_irreducible_lt_one
  条件: (hv : 整数egers v O) {ϖ : O} (h : 不可约 ϖ)
  证明: lt_of_le_of_ne (hv.map_le_one ϖ) (mt hv.isUnit_iff_valuation_eq_one.mpr h.not_isUnit)

Depends on / 依赖: h.not_isUnit, hv.isUnit_iff_valuation_eq_one.mpr, hv.map_le_one, isUnit_iff_valuation_eq_one, lt_of_le_of_ne, map_le_one, not_isUnit
-/
lemma valuation_irreducible_lt_one (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    v (algebraMap O F ϖ) < 1 :=
  lt_of_le_of_ne (hv.map_le_one ϖ) (mt hv.isUnit_iff_valuation_eq_one.mpr h.not_isUnit)

/--
lemma `valuation_unit` / 引理 `valuation_unit`

English:
lemma valuation_unit
  given: (hv : Integers v O) (x : Oˣ)
  proof: by
  simp [← hv.isUnit_iff_valuation_eq_one]

中文:
引理 valuation_unit
  条件: (hv : 整数egers v O) (x : Oˣ)
  证明: by
  simp [← hv.isUnit_iff_valuation_eq_one]

Depends on / 依赖: hv.isUnit_iff_valuation_eq_one, isUnit_iff_valuation_eq_one
-/
lemma valuation_unit (hv : Integers v O) (x : Oˣ) :
    v (algebraMap O F x) = 1 := by
  simp [← hv.isUnit_iff_valuation_eq_one]

/--
lemma `valuation_pos_iff_ne_zero` / 引理 `valuation_pos_iff_ne_zero`

English:
lemma valuation_pos_iff_ne_zero
  given: (hv : Integers v O) {x : O}
  proof: by
  rw [← not_le]
  refine not_congr ?_
  simp [map_eq_zero_iff _ hv.hom_inj]

中文:
引理 valuation_pos_iff_ne_zero
  条件: (hv : 整数egers v O) {x : O}
  证明: by
  rw [← not_le]
  refine not_congr ?_
  simp [map_eq_zero_iff _ hv.hom_inj]

Depends on / 依赖: hom_inj, hv.hom_inj, map_eq_zero_iff, not_congr, not_le
-/
lemma valuation_pos_iff_ne_zero (hv : Integers v O) {x : O} :
    0 < v (algebraMap O F x) ↔ x != 0 := by
  rw [← not_le]
  refine not_congr ?_
  simp [map_eq_zero_iff _ hv.hom_inj]

/--
lemma `valuation_irreducible_pos` / 引理 `valuation_irreducible_pos`

English:
lemma valuation_irreducible_pos
  given: (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ)
  proof: hv.valuation_pos_iff_ne_zero.mpr h.ne_zero

中文:
引理 valuation_irreducible_pos
  条件: (hv : 整数egers v O) {ϖ : O} (h : 不可约 ϖ)
  证明: hv.valuation_pos_iff_ne_zero.mpr h.ne_zero

Depends on / 依赖: h.ne_zero, hv.valuation_pos_iff_ne_zero.mpr, ne_zero, valuation_pos_iff_ne_zero
-/
lemma valuation_irreducible_pos (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    0 < v (algebraMap O F ϖ) :=
  hv.valuation_pos_iff_ne_zero.mpr h.ne_zero

/--
theorem `dvdNotUnit_iff_lt` / 定理 `dvdNotUnit_iff_lt`

English:
theorem dvdNotUnit_iff_lt
  given: (hv : Integers v O) {x y : O}
  proof: by
  rw [lt_iff_le_not_ge]; rw [hv.le_iff_dvd]; rw [hv.le_iff_dvd]
  refine ⟨?_, And.elim dvdNotUnit_of_dvd_of_not_dvd⟩
  rintro ⟨hx0, d, hdu, rfl⟩
  refine ⟨⟨d, rfl⟩, ?_⟩
  rw [hv.isUnit_iff_valuation_eq_one]; rw [← ne_eq]; rw [ne_iff_lt_iff_le.mpr (hv.map_le_one d)] at hdu
  rw [dvd_iff_le hv]
  simp only [map_mul, not_le]
  contrapose! hdu
  refine one_le_of_le_mul_left₀ ?_ hdu
  simp [hv.valuation_pos_iff_ne_zero, hx0]

中文:
定理 dvdNotUnit_iff_lt
  条件: (hv : 整数egers v O) {x y : O}
  证明: by
  rw [lt_iff_le_not_ge]; rw [hv.le_iff_dvd]; rw [hv.le_iff_dvd]
  refine ⟨?_, And.elim dvdNotUnit_of_dvd_of_not_dvd⟩
  rintro ⟨hx0, d, hdu, rfl⟩
  refine ⟨⟨d, rfl⟩, ?_⟩
  rw [hv.isUnit_iff_valuation_eq_one]; rw [← ne_eq]; rw [ne_iff_lt_iff_le.mpr (hv.map_le_one d)] at hdu
  rw [dvd_iff_le hv]
  simp only [map_mul, not_le]
  contrapose! hdu
  refine one_le_of_le_mul_left₀ ?_ hdu
  simp [hv.valuation_pos_iff_ne_zero, hx0]

Depends on / 依赖: And.elim, contrapose, dvdNotUnit_of_dvd_of_not_dvd, dvd_iff_le, hv.isUnit_iff_valuation_eq_one, hv.le_iff_dvd, hv.map_le_one, hv.valuation_pos_iff_ne_zero, isUnit_iff_valuation_eq_one, le_iff_dvd, lt_iff_le_not_ge, map_le_one, map_mul, ne_eq, ne_iff_lt_iff_le, ne_iff_lt_iff_le.mpr, not_le, valuation_pos_iff_ne_zero
-/
theorem dvdNotUnit_iff_lt (hv : Integers v O) {x y : O} :
    DvdNotUnit x y ↔ v (algebraMap O F y) < v (algebraMap O F x) := by
  rw [lt_iff_le_not_ge]; rw [hv.le_iff_dvd]; rw [hv.le_iff_dvd]
  refine ⟨?_, And.elim dvdNotUnit_of_dvd_of_not_dvd⟩
  rintro ⟨hx0, d, hdu, rfl⟩
  refine ⟨⟨d, rfl⟩, ?_⟩
  rw [hv.isUnit_iff_valuation_eq_one]; rw [← ne_eq]; rw [ne_iff_lt_iff_le.mpr (hv.map_le_one d)] at hdu
  rw [dvd_iff_le hv]
  simp only [map_mul, not_le]
  contrapose! hdu
  refine one_le_of_le_mul_left₀ ?_ hdu
  simp [hv.valuation_pos_iff_ne_zero, hx0]

/--
theorem `eq_algebraMap_or_inv_eq_algebraMap` / 定理 `eq_algebraMap_or_inv_eq_algebraMap`

English:
theorem eq_algebraMap_or_inv_eq_algebraMap
  given: (hv : Integers v O) (x : F)
  proof: by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]

中文:
定理 eq_algebraMap_or_inv_eq_algebraMap
  条件: (hv : 整数egers v O) (x : F)
  证明: by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]

Depends on / 依赖: Or.inl, Or.inr, exacts, exists_of_le_one, ha.symm, val_le_one_or_val_inv_le_one
-/
theorem eq_algebraMap_or_inv_eq_algebraMap (hv : Integers v O) (x : F) :
    exists a : O, x = algebraMap O F a ∨ x⁻¹ = algebraMap O F a := by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]

/--
lemma `coe_span_singleton_eq_setOfPred_le_v_algebraMap` / 引理 `coe_span_singleton_eq_setOfPred_le_v_algebraMap`

English:
lemma coe_span_singleton_eq_setOfPred_le_v_algebraMap
  given: (hv : Integers v O) (x : O)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero, map_eq_zero_iff _ hv.hom_inj]
  ext
  simp [SetLike.mem_coe, Ideal.mem_span_singleton, hv.dvd_iff_le]

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_algebraMap := coe_span_singleton_eq_setOfPred_le_v_algebraMap

中文:
引理 coe_span_singleton_eq_setOfPred_le_v_algebraMap
  条件: (hv : 整数egers v O) (x : O)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero, map_eq_zero_iff _ hv.hom_inj]
  ext
  simp [SetLike.mem_coe, Ideal.mem_span_singleton, hv.dvd_iff_le]

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_algebraMap := coe_span_singleton_eq_setOfPred_le_v_algebraMap

Depends on / 依赖: Ideal.mem_span_singleton, Set.singleton_zero, SetLike, SetLike.mem_coe, dvd_iff_le, eq_or_ne, hom_inj, hv.dvd_iff_le, hv.hom_inj, map_eq_zero_iff, mem_coe, mem_span_singleton, singleton_zero
-/
lemma coe_span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O) :
    (Ideal.span {x} : Set O) = {y : O | v (algebraMap O F y) <= v (algebraMap O F x)} := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero, map_eq_zero_iff _ hv.hom_inj]
  ext
  simp [SetLike.mem_coe, Ideal.mem_span_singleton, hv.dvd_iff_le]

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_algebraMap := coe_span_singleton_eq_setOfPred_le_v_algebraMap

/--
lemma `bijective_algebraMap_of_subsingleton_units_mrange` / 引理 `bijective_algebraMap_of_subsingleton_units_mrange`

English:
lemma bijective_algebraMap_of_subsingleton_units_mrange
  statement: (hv : Integers v O)
  proof: by
  refine ⟨hv.hom_inj, fun x => hv.exists_of_le_one ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (congr_arg Units.val (Subsingleton.elim (α := (MonoidHom.mrange v)ˣ)
      ((isUnit_iff_ne_zero.mpr hx).unit.map v.toMonoidHom.mrangeRestrict) 1)).le

中文:
引理 bijective_algebraMap_of_subsingleton_units_mrange
  结论: (hv : 整数egers v O)
  证明: by
  refine ⟨hv.hom_inj, fun x => hv.exists_of_le_one ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (congr_arg Units.val (Subsingleton.elim (α := (MonoidHom.mrange v)ˣ)
      ((isUnit_iff_ne_zero.mpr hx).unit.map v.toMonoidHom.mrangeRestrict) 1)).le

Depends on / 依赖: MonoidHom, MonoidHom.mrange, Subsingleton, Subsingleton.elim, Units.val, congr_arg, eq_or_ne, exists_of_le_one, hom_inj, hv.exists_of_le_one, hv.hom_inj, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, mrange, mrangeRestrict, toMonoidHom, unit.map, v.toMonoidHom.mrangeRestrict
-/
lemma bijective_algebraMap_of_subsingleton_units_mrange (hv : Integers v O)
    [Subsingleton (MonoidHom.mrange v)ˣ] :
    Function.Bijective (algebraMap O F) := by
  refine ⟨hv.hom_inj, fun x => hv.exists_of_le_one ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (congr_arg Units.val (Subsingleton.elim (α := (MonoidHom.mrange v)ˣ)
      ((isUnit_iff_ne_zero.mpr hx).unit.map v.toMonoidHom.mrangeRestrict) 1)).le

/--
lemma `isPrincipal_iff_exists_isGreatest` / 引理 `isPrincipal_iff_exists_isGreatest`

English:
lemma isPrincipal_iff_exists_isGreatest
  given: (hv : Integers v O) {I : Ideal O}
  proof: by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact ⟨fun hb => dvd_of_le hv (hx.2 <| mem_image_of_mem _ hb), fun hb => I.mem_of_dvd hb ha⟩

中文:
引理 isPrincipal_iff_存在_isGreatest
  条件: (hv : 整数egers v O) {I : 理想 O}
  证明: by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact ⟨fun hb => dvd_of_le hv (hx.2 <| mem_image_of_mem _ hb), fun hb => I.mem_of_dvd hb ha⟩

Depends on / 依赖: Function, Function.comp_apply, Ideal.mem_span_singleton, Ideal.submodule_span_eq, Set.mem_image, Set.mem_image_of_mem, SetLike, SetLike.mem_coe, algebraMap, comp_apply, hx.left, le_of_dvd, mem_coe, mem_image, mem_image_of_mem, mem_span_singleton, submodule_span_eq
-/
lemma isPrincipal_iff_exists_isGreatest (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ exists x, IsGreatest (v ∘ algebraMap O F '' I) x := by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact ⟨fun hb => dvd_of_le hv (hx.2 <| mem_image_of_mem _ hb), fun hb => I.mem_of_dvd hb ha⟩

/--
lemma `isPrincipal_iff_exists_eq_setOfPred_valuation_le` / 引理 `isPrincipal_iff_exists_eq_setOfPred_valuation_le`

English:
lemma isPrincipal_iff_exists_eq_setOfPred_valuation_le
  given: (hv : Integers v O) {I : Ideal O}
  proof: by
  rw [isPrincipal_iff_exists_isGreatest hv]
  constructor <;> rintro ⟨x, hx⟩
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [SetLike.mem_coe, mem_ofPred_eq]
    constructor <;> intro h
    · exact hx.right (Set.mem_image_of_mem _ h)
    · rw [le_iff_dvd hv] at h
      exact Ideal.mem_of_dvd I h ha
  · refine ⟨v (algebraMap O F x), Set.mem_image_of_mem _ ?_, ?_⟩
    · simp [hx]
    · simp [hx, mem_upperBounds]

@[deprecated (since := "2026-07-09")]
alias isPrincipal_iff_exists_eq_setOf_valuation_le :=
  isPrincipal_iff_exists_eq_setOfPred_valuation_le

中文:
引理 isPrincipal_iff_存在_eq_setOfPred_valuation_le
  条件: (hv : 整数egers v O) {I : 理想 O}
  证明: by
  rw [isPrincipal_iff_exists_isGreatest hv]
  constructor <;> rintro ⟨x, hx⟩
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [SetLike.mem_coe, mem_ofPred_eq]
    constructor <;> intro h
    · exact hx.right (Set.mem_image_of_mem _ h)
    · rw [le_iff_dvd hv] at h
      exact Ideal.mem_of_dvd I h ha
  · refine ⟨v (algebraMap O F x), Set.mem_image_of_mem _ ?_, ?_⟩
    · simp [hx]
    · simp [hx, mem_upperBounds]

@[deprecated (since := "2026-07-09")]
alias isPrincipal_iff_exists_eq_setOf_valuation_le :=
  isPrincipal_iff_exists_eq_setOfPred_valuation_le

Depends on / 依赖: Ideal.mem_of_dvd, Set.mem_image_of_mem, SetLike, SetLike.mem_coe, algebraMap, hx.left, hx.right, isPrincipal_iff_exists_isGreatest, le_iff_dvd, mem_coe, mem_image_of_mem, mem_ofPred_eq, mem_of_dvd, mem_upperBounds
-/
lemma isPrincipal_iff_exists_eq_setOfPred_valuation_le (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ exists x, (I : Set O) = {y | v (algebraMap O F y) <= v (algebraMap O F x)} := by
  rw [isPrincipal_iff_exists_isGreatest hv]
  constructor <;> rintro ⟨x, hx⟩
  · obtain ⟨a, ha, rfl⟩ : exists a in I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [SetLike.mem_coe, mem_ofPred_eq]
    constructor <;> intro h
    · exact hx.right (Set.mem_image_of_mem _ h)
    · rw [le_iff_dvd hv] at h
      exact Ideal.mem_of_dvd I h ha
  · refine ⟨v (algebraMap O F x), Set.mem_image_of_mem _ ?_, ?_⟩
    · simp [hx]
    · simp [hx, mem_upperBounds]

@[deprecated (since := "2026-07-09")]
alias isPrincipal_iff_exists_eq_setOf_valuation_le :=
  isPrincipal_iff_exists_eq_setOfPred_valuation_le

set_option backward.isDefEq.respectTransparency false in
/--
lemma `not_denselyOrdered_of_isPrincipalIdealRing` / 引理 `not_denselyOrdered_of_isPrincipalIdealRing`

English:
lemma not_denselyOrdered_of_isPrincipalIdealRing
  given: [IsPrincipalIdealRing O] (hv : Integers v O)
  proof: by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := v ∘ algebraMap O F ⁻¹' Iio (1 : Γ₀)
    add_mem' := fun {a b} ha hb => by simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [mem_preimage, Function.comp_apply, mem_Iio, smul_eq_mul, map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  }
  obtain ⟨x, hx₁, hx⟩ :
    exists x, v (algebraMap O F x) < 1 ∧
      v (algebraMap O F x) in upperBounds (Iio 1 inter range (v ∘ algebraMap O F)) := by
    simpa [I, IsGreatest, hv.isPrincipal_iff_exists_isGreatest, ← image_preimage_eq_inter_range]
      using IsPrincipalIdealRing.principal I
  obtain ⟨y, hy, hy₁⟩ : exists y, v (algebraMap O F x) < v y ∧ v y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, exists_range_iff, exists_prop]
      using H.dense ⟨v (algebraMap O F x), mem_range_self _⟩ ⟨1, 1, v.map_one⟩ hx₁
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hy₁.le
exact hy.not_ge hx ⟨hy₁, mem_range_self _⟩

中文:
引理 not_denselyOrdered_of_isPrincipalIdealRing
  条件: [是主理想环 O] (hv : 整数egers v O)
  证明: by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := v ∘ algebraMap O F ⁻¹' Iio (1 : Γ₀)
    add_mem' := fun {a b} ha hb => by simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [mem_preimage, Function.comp_apply, mem_Iio, smul_eq_mul, map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  }
  obtain ⟨x, hx₁, hx⟩ :
    exists x, v (algebraMap O F x) < 1 ∧
      v (algebraMap O F x) in upperBounds (Iio 1 inter range (v ∘ algebraMap O F)) := by
    simpa [I, IsGreatest, hv.isPrincipal_iff_exists_isGreatest, ← image_preimage_eq_inter_range]
      using IsPrincipalIdealRing.principal I
  obtain ⟨y, hy, hy₁⟩ : exists y, v (algebraMap O F x) < v y ∧ v y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, exists_range_iff, exists_prop]
      using H.dense ⟨v (algebraMap O F x), mem_range_self _⟩ ⟨1, 1, v.map_one⟩ hx₁
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hy₁.le
exact hy.not_ge hx ⟨hy₁, mem_range_self _⟩
-/
lemma not_denselyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : Integers v O) :
    ¬ DenselyOrdered (range v) := by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := v ∘ algebraMap O F ⁻¹' Iio (1 : Γ₀)
    add_mem' := fun {a b} ha hb => by simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [mem_preimage, Function.comp_apply, mem_Iio, smul_eq_mul, map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  }
  obtain ⟨x, hx₁, hx⟩ :
    exists x, v (algebraMap O F x) < 1 ∧
      v (algebraMap O F x) in upperBounds (Iio 1 inter range (v ∘ algebraMap O F)) := by
    simpa [I, IsGreatest, hv.isPrincipal_iff_exists_isGreatest, ← image_preimage_eq_inter_range]
      using IsPrincipalIdealRing.principal I
  obtain ⟨y, hy, hy₁⟩ : exists y, v (algebraMap O F x) < v y ∧ v y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, exists_range_iff, exists_prop]
      using H.dense ⟨v (algebraMap O F x), mem_range_self _⟩ ⟨1, 1, v.map_one⟩ hx₁
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hy₁.le
exact hy.not_ge hx ⟨hy₁, mem_range_self _⟩

end Integers

open Integers in
/--
theorem `Integer.not_isUnit_iff_valuation_lt_one` / 定理 `Integer.not_isUnit_iff_valuation_lt_one`

English:
theorem Integer.not_isUnit_iff_valuation_lt_one
  given: {x : v.integer}
  statement: ¬IsUnit x ↔ v x < 1
  proof: by
  rw [← not_le]; rw [not_iff_not]; rw [isUnit_iff_valuation_eq_one (F := F) (Γ₀ := Γ₀)]; rw [le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v]

中文:
定理 整数eger.not_isUnit_iff_valuation_lt_one
  条件: {x : v.integer}
  结论: ¬是单位 x ↔ v x < 1
  证明: by
  rw [← not_le]; rw [not_iff_not]; rw [isUnit_iff_valuation_eq_one (F := F) (Γ₀ := Γ₀)]; rw [le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v]

Depends on / 依赖: and_iff_right, exacts, integer, integer.integers, integers, isUnit_iff_valuation_eq_one, le_antisymm_iff, not_iff_not, not_le
-/
theorem Integer.not_isUnit_iff_valuation_lt_one {x : v.integer} : ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le]; rw [not_iff_not]; rw [isUnit_iff_valuation_eq_one (F := F) (Γ₀ := Γ₀)]; rw [le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v]

namespace integer

/--
lemma `v_irreducible_lt_one` / 引理 `v_irreducible_lt_one`

English:
lemma v_irreducible_lt_one
  given: {ϖ : v.integer} (h : Irreducible ϖ)
  proof: (Valuation.integer.integers v).valuation_irreducible_lt_one h

中文:
引理 v_irreducible_lt_one
  条件: {ϖ : v.integer} (h : 不可约 ϖ)
  证明: (Valuation.integer.integers v).valuation_irreducible_lt_one h

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, valuation_irreducible_lt_one
-/
lemma v_irreducible_lt_one {ϖ : v.integer} (h : Irreducible ϖ) :
    v ϖ < 1 :=
  (Valuation.integer.integers v).valuation_irreducible_lt_one h

/--
lemma `v_irreducible_pos` / 引理 `v_irreducible_pos`

English:
lemma v_irreducible_pos
  given: {ϖ : v.integer} (h : Irreducible ϖ)
  statement: 0 < v ϖ
  proof: (Valuation.integer.integers v).valuation_irreducible_pos h

中文:
引理 v_irreducible_pos
  条件: {ϖ : v.integer} (h : 不可约 ϖ)
  结论: 0 < v ϖ
  证明: (Valuation.integer.integers v).valuation_irreducible_pos h

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, valuation_irreducible_pos
-/
lemma v_irreducible_pos {ϖ : v.integer} (h : Irreducible ϖ) : 0 < v ϖ :=
  (Valuation.integer.integers v).valuation_irreducible_pos h

/--
lemma `coe_span_singleton_eq_setOfPred_le_v_coe` / 引理 `coe_span_singleton_eq_setOfPred_le_v_coe`

English:
lemma coe_span_singleton_eq_setOfPred_le_v_coe
  given: (x : v.integer)
  proof: (Valuation.integer.integers v).coe_span_singleton_eq_setOfPred_le_v_algebraMap x

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_coe := coe_span_singleton_eq_setOfPred_le_v_coe

中文:
引理 coe_span_singleton_eq_setOfPred_le_v_coe
  条件: (x : v.integer)
  证明: (Valuation.integer.integers v).coe_span_singleton_eq_setOfPred_le_v_algebraMap x

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_coe := coe_span_singleton_eq_setOfPred_le_v_coe

Depends on / 依赖: Valuation, Valuation.integer.integers, coe_span_singleton_eq_setOfPred_le_v_algebraMap, integer, integers
-/
lemma coe_span_singleton_eq_setOfPred_le_v_coe (x : v.integer) :
    (Ideal.span {x} : Set v.integer) = {y : v.integer | v y <= v x} :=
  (Valuation.integer.integers v).coe_span_singleton_eq_setOfPred_le_v_algebraMap x

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_coe := coe_span_singleton_eq_setOfPred_le_v_coe

end integer

end Field

section Ideal

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
local notation "𝓞" => v.integer

/--
Definition of `leSubmodule` / `leSubmodule` 的定义

English:
definition leSubmodule
  signature: (γ : Γ₀)
  body: leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

中文:
定义 leSubmodule
  签名: (γ : Γ₀)
  定义体: leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

Depends on / 依赖: leAddSubgroup
-/
def leSubmodule (γ : Γ₀) : Submodule 𝓞 R where
  __ := leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

/--
Definition of `ltSubmodule` / `ltSubmodule` 的定义

English:
definition ltSubmodule
  signature: (γ : Γ₀ˣ)
  body: ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

中文:
定义 ltSubmodule
  签名: (γ : Γ₀ˣ)
  定义体: ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

Depends on / 依赖: ltAddSubgroup
-/
def ltSubmodule (γ : Γ₀ˣ) : Submodule 𝓞 R where
  __ := ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

/--
lemma `leSubmodule_monotone` / 引理 `leSubmodule_monotone`

English:
lemma leSubmodule_monotone
  statement: Monotone (leSubmodule v)
  proof: leAddSubgroup_monotone v

中文:
引理 leSubmodule_monotone
  结论: 递增 (leSubmodule v)
  证明: leAddSubgroup_monotone v

Depends on / 依赖: leAddSubgroup_monotone
-/
lemma leSubmodule_monotone : Monotone (leSubmodule v) :=
  leAddSubgroup_monotone v

/--
lemma `ltSubmodule_monotone` / 引理 `ltSubmodule_monotone`

English:
lemma ltSubmodule_monotone
  statement: Monotone (ltSubmodule v)
  proof: ltAddSubgroup_monotone v

中文:
引理 ltSubmodule_monotone
  结论: 递增 (ltSubmodule v)
  证明: ltAddSubgroup_monotone v

Depends on / 依赖: ltAddSubgroup_monotone
-/
lemma ltSubmodule_monotone : Monotone (ltSubmodule v) :=
  ltAddSubgroup_monotone v

/--
lemma `ltSubmodule_le_leSubmodule` / 引理 `ltSubmodule_le_leSubmodule`

English:
lemma ltSubmodule_le_leSubmodule
  given: (γ : Γ₀ˣ)
  proof: ltAddSubgroup_le_leAddSubgroup v γ

中文:
引理 ltSubmodule_le_leSubmodule
  条件: (γ : Γ₀ˣ)
  证明: ltAddSubgroup_le_leAddSubgroup v γ

Depends on / 依赖: ltAddSubgroup_le_leAddSubgroup
-/
lemma ltSubmodule_le_leSubmodule (γ : Γ₀ˣ) :
    ltSubmodule v γ <= leSubmodule v (γ : Γ₀) :=
  ltAddSubgroup_le_leAddSubgroup v γ

variable {v} in
@[simp]
/--
lemma `mem_leSubmodule_iff` / 引理 `mem_leSubmodule_iff`

English:
lemma mem_leSubmodule_iff
  given: {γ : Γ₀} {x : R}
  proof: Iff.rfl

中文:
引理 mem_leSubmodule_iff
  条件: {γ : Γ₀} {x : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_leSubmodule_iff {γ : Γ₀} {x : R} :
    x in leSubmodule v γ ↔ v x <= γ :=
  Iff.rfl

variable {v} in
@[simp]
/--
lemma `mem_ltSubmodule_iff` / 引理 `mem_ltSubmodule_iff`

English:
lemma mem_ltSubmodule_iff
  given: {γ : Γ₀ˣ} {x : R}
  proof: Iff.rfl

@[simp]

中文:
引理 mem_ltSubmodule_iff
  条件: {γ : Γ₀ˣ} {x : R}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_ltSubmodule_iff {γ : Γ₀ˣ} {x : R} :
    x in ltSubmodule v γ ↔ v x < γ :=
  Iff.rfl

@[simp]
/--
lemma `leSubmodule_zero` / 引理 `leSubmodule_zero`

English:
lemma leSubmodule_zero
  given: (K : Type*) [Field K] (v : Valuation K Γ₀)
  proof: by
  ext; simp

中文:
引理 leSubmodule_zero
  条件: (K : 类型) [域 K] (v : 赋值 K Γ₀)
  证明: by
  ext; simp
-/
lemma leSubmodule_zero (K : Type*) [Field K] (v : Valuation K Γ₀) :
    leSubmodule v (0 : Γ₀) = ⊥ := by
  ext; simp

/--
lemma `leSubmodule_v_le_of_mem` / 引理 `leSubmodule_v_le_of_mem`

English:
lemma leSubmodule_v_le_of_mem
  statement: {K : Type*} [Field K] (v : Valuation K Γ₀)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simp [div_le_one_of_le₀ hy]
  simpa [Subring.smul_def, div_mul_cancel₀ _ hx0] using S.smul_mem ⟨_, this⟩ hx

中文:
引理 leSubmodule_v_le_of_mem
  结论: {K : 类型} [域 K] (v : 赋值 K Γ₀)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simp [div_le_one_of_le₀ hy]
  simpa [Subring.smul_def, div_mul_cancel₀ _ hx0] using S.smul_mem ⟨_, this⟩ hx

Depends on / 依赖: S.smul_mem, Subring, Subring.smul_def, eq_or_ne, smul_def, smul_mem
-/
lemma leSubmodule_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀)
    {S : Submodule v.integer K} {x : K} (hx : x in S) :
    leSubmodule v (v x) <= S := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simp [div_le_one_of_le₀ hy]
  simpa [Subring.smul_def, div_mul_cancel₀ _ hx0] using S.smul_mem ⟨_, this⟩ hx

/--
lemma `ltSubmodule_v_le_of_mem` / 引理 `ltSubmodule_v_le_of_mem`

English:
lemma ltSubmodule_v_le_of_mem
  statement: {K : Type*} [Field K] {v : Valuation K Γ₀}
  proof: (leSubmodule_v_le_of_mem v hx).trans' (ltSubmodule_le_leSubmodule _ _)

中文:
引理 ltSubmodule_v_le_of_mem
  结论: {K : 类型} [域 K] {v : 赋值 K Γ₀}
  证明: (leSubmodule_v_le_of_mem v hx).trans' (ltSubmodule_le_leSubmodule _ _)

Depends on / 依赖: leSubmodule_v_le_of_mem, ltSubmodule_le_leSubmodule
-/
lemma ltSubmodule_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀}
    {S : Submodule v.integer K} {x : K} (hx : x in S) (hxv : v x != 0) :
    ltSubmodule v (Units.mk0 _ hxv) <= S :=
  (leSubmodule_v_le_of_mem v hx).trans' (ltSubmodule_le_leSubmodule _ _)

-- the ideals do not use the submodules due to `Submodule.comap _ (Algebra.linearMap _ _)`
-- requiring commutativity

/--
Definition of `leIdeal` / `leIdeal` 的定义

English:
definition leIdeal
  signature: (γ : Γ₀)
  body: AddSubgroup.addSubgroupOf (leAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h :=
    -- need to specify the subgroup, it is not inferred otherwise
(AddSubgroup.mem_addSubgroupOf (K := v.integer.toAddSubgroup)).mpr by
      simpa using mul_le_of_le_one_of_le r.prop h

中文:
定义 leIdeal
  签名: (γ : Γ₀)
  定义体: AddSubgroup.addSubgroupOf (leAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h :=
    -- need to specify the subgroup, it is not inferred otherwise
(AddSubgroup.mem_addSubgroupOf (K := v.integer.toAddSubgroup)).mpr by
      simpa using mul_le_of_le_one_of_le r.prop h

Depends on / 依赖: AddSubgroup, AddSubgroup.addSubgroupOf, TopologicalSpace, TopologicalSpace.isOpen_inter, addSubgroupOf, integer, isOpen_inter, leAddSubgroup, toAddSubgroup, v.integer.toAddSubgroup
-/
def leIdeal (γ : Γ₀) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (leAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h :=
    -- need to specify the subgroup, it is not inferred otherwise
(AddSubgroup.mem_addSubgroupOf (K := v.integer.toAddSubgroup)).mpr by
      simpa using mul_le_of_le_one_of_le r.prop h

/--
Definition of `ltIdeal` / `ltIdeal` 的定义

English:
definition ltIdeal
  signature: (γ : Γ₀ˣ)
  body: AddSubgroup.addSubgroupOf (ltAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) < γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

中文:
定义 ltIdeal
  签名: (γ : Γ₀ˣ)
  定义体: AddSubgroup.addSubgroupOf (ltAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) < γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

Depends on / 依赖: AddSubgroup, AddSubgroup.addSubgroupOf, addSubgroupOf, integer, ltAddSubgroup, toAddSubgroup, v.integer.toAddSubgroup
-/
def ltIdeal (γ : Γ₀ˣ) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (ltAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) < γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

-- Can't use `leAddSubgroup` because `addSubgroupOf` is a dependent function
/--
lemma `leIdeal_mono` / 引理 `leIdeal_mono`

English:
lemma leIdeal_mono
  statement: Monotone (leIdeal v)
  proof: fun _ _ h _ => h.trans'

中文:
引理 leIdeal_mono
  结论: 递增 (leIdeal v)
  证明: fun _ _ h _ => h.trans'

Depends on / 依赖: h.trans
-/
lemma leIdeal_mono : Monotone (leIdeal v) :=
  fun _ _ h _ => h.trans'

/--
lemma `ltIdeal_mono` / 引理 `ltIdeal_mono`

English:
lemma ltIdeal_mono
  statement: Monotone (ltIdeal v)
  proof: fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

中文:
引理 ltIdeal_mono
  结论: 递增 (ltIdeal v)
  证明: fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

Depends on / 依赖: Units.val_le_val.mpr, trans_lt, val_le_val
-/
lemma ltIdeal_mono : Monotone (ltIdeal v) :=
  fun _ _ h _ => (Units.val_le_val.mpr h).trans_lt'

/--
lemma `ltIdeal_le_leIdeal` / 引理 `ltIdeal_le_leIdeal`

English:
lemma ltIdeal_le_leIdeal
  given: (γ : Γ₀ˣ)
  proof: fun _ h => h.le

中文:
引理 ltIdeal_le_leIdeal
  条件: (γ : Γ₀ˣ)
  证明: fun _ h => h.le

Depends on / 依赖: h.le
-/
lemma ltIdeal_le_leIdeal (γ : Γ₀ˣ) :
    ltIdeal v γ <= leIdeal v (γ : Γ₀) :=
  fun _ h => h.le

variable {v} in
@[simp]
/--
lemma `mem_leIdeal_iff` / 引理 `mem_leIdeal_iff`

English:
lemma mem_leIdeal_iff
  given: {γ : Γ₀} {x : 𝓞}
  proof: Iff.rfl

中文:
引理 mem_leIdeal_iff
  条件: {γ : Γ₀} {x : 𝓞}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_leIdeal_iff {γ : Γ₀} {x : 𝓞} :
    x in leIdeal v γ ↔ v (x : R) <= γ :=
  Iff.rfl

variable {v} in
@[simp]
/--
lemma `mem_ltIdeal_iff` / 引理 `mem_ltIdeal_iff`

English:
lemma mem_ltIdeal_iff
  given: {γ : Γ₀ˣ} {x : 𝓞}
  proof: Iff.rfl

@[simp]

中文:
引理 mem_ltIdeal_iff
  条件: {γ : Γ₀ˣ} {x : 𝓞}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_ltIdeal_iff {γ : Γ₀ˣ} {x : 𝓞} :
    x in ltIdeal v γ ↔ v (x : R) < γ :=
  Iff.rfl

@[simp]
/--
lemma `leIdeal_zero` / 引理 `leIdeal_zero`

English:
lemma leIdeal_zero
  given: (K : Type*) [Field K] (v : Valuation K Γ₀)
  proof: by
  ext; simp

中文:
引理 leIdeal_zero
  条件: (K : 类型) [域 K] (v : 赋值 K Γ₀)
  证明: by
  ext; simp
-/
lemma leIdeal_zero (K : Type*) [Field K] (v : Valuation K Γ₀) :
    leIdeal v (0 : Γ₀) = ⊥ := by
  ext; simp

/--
lemma `leSubmodule_comap_algebraMap_eq_leIdeal` / 引理 `leSubmodule_comap_algebraMap_eq_leIdeal`

English:
lemma leSubmodule_comap_algebraMap_eq_leIdeal
  given: {K : Type*} [Field K] (v : Valuation K Γ₀) (γ : Γ₀)
  proof: Submodule.ext fun _ => Iff.rfl

中文:
引理 leSubmodule_comap_algebraMap_eq_leIdeal
  条件: {K : 类型} [域 K] (v : 赋值 K Γ₀) (γ : Γ₀)
  证明: Submodule.ext fun _ => Iff.rfl

Depends on / 依赖: Iff.rfl, Submodule, Submodule.ext
-/
lemma leSubmodule_comap_algebraMap_eq_leIdeal {K : Type*} [Field K] (v : Valuation K Γ₀) (γ : Γ₀) :
    (leSubmodule v γ).comap (Algebra.linearMap _ _) = leIdeal v γ :=
  Submodule.ext fun _ => Iff.rfl

/--
lemma `leIdeal_map_algebraMap_eq_leSubmodule_min` / 引理 `leIdeal_map_algebraMap_eq_leSubmodule_min`

English:
lemma leIdeal_map_algebraMap_eq_leSubmodule_min
  statement: {K : Type*} [Field K] (v : Valuation K Γ₀)
  proof: by
  ext x
  simp only [Submodule.mem_map, mem_leIdeal_iff, Algebra.linearMap_apply, mem_leSubmodule_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases min_cases 1 γ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact y.prop
    · rw [h]
      exact hy
  · intro hx
    rcases min_cases 1 γ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hx
    · exact ⟨⟨x, hx⟩, hx.trans h', rfl⟩
    · exact ⟨⟨x, hx.trans h'.le⟩, hx, rfl⟩

中文:
引理 leIdeal_map_algebraMap_eq_leSubmodule_min
  结论: {K : 类型} [域 K] (v : 赋值 K Γ₀)
  证明: by
  ext x
  simp only [Submodule.mem_map, mem_leIdeal_iff, Algebra.linearMap_apply, mem_leSubmodule_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases min_cases 1 γ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact y.prop
    · rw [h]
      exact hy
  · intro hx
    rcases min_cases 1 γ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hx
    · exact ⟨⟨x, hx⟩, hx.trans h', rfl⟩
    · exact ⟨⟨x, hx.trans h'.le⟩, hx, rfl⟩

Depends on / 依赖: Algebra, Algebra.linearMap_apply, Submodule, Submodule.mem_map, hx.trans, linearMap_apply, mem_leIdeal_iff, mem_leSubmodule_iff, mem_map, min_cases, y.prop
-/
lemma leIdeal_map_algebraMap_eq_leSubmodule_min {K : Type*} [Field K] (v : Valuation K Γ₀)
    (γ : Γ₀) :
    Submodule.map (Algebra.linearMap _ _) (leIdeal v γ) = leSubmodule v (min 1 γ) := by
  ext x
  simp only [Submodule.mem_map, mem_leIdeal_iff, Algebra.linearMap_apply, mem_leSubmodule_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases min_cases 1 γ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact y.prop
    · rw [h]
      exact hy
  · intro hx
    rcases min_cases 1 γ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hx
    · exact ⟨⟨x, hx⟩, hx.trans h', rfl⟩
    · exact ⟨⟨x, hx.trans h'.le⟩, hx, rfl⟩

-- Ideally, this would follow from `leSubmodule_v_le_of_mem`
/--
lemma `leIdeal_v_le_of_mem` / 引理 `leIdeal_v_le_of_mem`

English:
lemma leIdeal_v_le_of_mem
  statement: {K : Type*} [Field K] (v : Valuation K Γ₀)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simpa using div_le_one_of_le₀ hy zero_le
  convert! I.smul_mem ⟨_, this⟩ hx using 1
  simp [Subtype.ext_iff, div_mul_cancel₀ _ (ZeroMemClass.coe_eq_zero.not.mpr hx0)]

中文:
引理 leIdeal_v_le_of_mem
  结论: {K : 类型} [域 K] (v : 赋值 K Γ₀)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simpa using div_le_one_of_le₀ hy zero_le
  convert! I.smul_mem ⟨_, this⟩ hx using 1
  simp [Subtype.ext_iff, div_mul_cancel₀ _ (ZeroMemClass.coe_eq_zero.not.mpr hx0)]

Depends on / 依赖: I.smul_mem, Subtype, Subtype.ext_iff, ZeroMemClass, ZeroMemClass.coe_eq_zero.not.mpr, coe_eq_zero, convert, eq_or_ne, ext_iff, smul_mem, zero_le
-/
lemma leIdeal_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀)
    {I : Ideal v.integer} {x : v.integer} (hx : x in I) :
    leIdeal v (v (x : K)) <= I := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) <= 1 := by simpa using div_le_one_of_le₀ hy zero_le
  convert! I.smul_mem ⟨_, this⟩ hx using 1
  simp [Subtype.ext_iff, div_mul_cancel₀ _ (ZeroMemClass.coe_eq_zero.not.mpr hx0)]

/--
lemma `ltIdeal_v_le_of_mem` / 引理 `ltIdeal_v_le_of_mem`

English:
lemma ltIdeal_v_le_of_mem
  statement: {K : Type*} [Field K] {v : Valuation K Γ₀}
  proof: (leIdeal_v_le_of_mem v hx).trans' (ltIdeal_le_leIdeal _ _)

中文:
引理 ltIdeal_v_le_of_mem
  结论: {K : 类型} [域 K] {v : 赋值 K Γ₀}
  证明: (leIdeal_v_le_of_mem v hx).trans' (ltIdeal_le_leIdeal _ _)

Depends on / 依赖: leIdeal_v_le_of_mem, ltIdeal_le_leIdeal
-/
lemma ltIdeal_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀}
    {I : Ideal v.integer} {x : v.integer} (hx : x in I) (hxv : v (x : K) != 0) :
    ltIdeal v (Units.mk0 _ hxv) <= I :=
  (leIdeal_v_le_of_mem v hx).trans' (ltIdeal_le_leIdeal _ _)

end Ideal

end Valuation
