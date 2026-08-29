/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/

module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Order of vanishing in Noetherian rings.

In this file we define various properties of the order of vanishing in Noetherian rings, including
some API for computing the order of vanishing in discrete valuation rings.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ring

section NoetherianDimLEOne

variable {R : Type*} [CommRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors
/--
Order of vanishing function as a monoid homomorphism
-/
noncomputable
/--
Definition of `ordMonoidHom` / `ordMonoidHom` 的定义

English:
definition ordMonoidHom
  signature: : R⁰ ->* Multiplicative Nat where
  body: .ofAdd (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]

@[simp]

中文:
定义 ordMonoidHom
  签名: : R⁰ ->* Multiplicative 自然数 where
  定义体: .ofAdd (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]

@[simp]

Depends on / 依赖: Ring.ord
-/
def ordMonoidHom : R⁰ ->* Multiplicative Nat where
toFun x := .ofAdd (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]

@[simp]
/--
lemma `ordMonoidHom_eq_ord` / 引理 `ordMonoidHom_eq_ord`

English:
lemma ordMonoidHom_eq_ord
  given: (x : R⁰)
  statement: (ordMonoidHom x).toAdd = Ring.ord R x
  proof: (ENat.natCast_toNat (ord_ne_top x.2))

@[simp]

中文:
引理 ordMonoidHom_eq_ord
  条件: (x : R⁰)
  结论: (ordMonoidHom x).toAdd = 环.ord R x
  证明: (ENat.natCast_toNat (ord_ne_top x.2))

@[simp]

Depends on / 依赖: ENat.natCast_toNat, natCast_toNat, ord_ne_top
-/
lemma ordMonoidHom_eq_ord (x : R⁰) : (ordMonoidHom x).toAdd = Ring.ord R x :=
  (ENat.natCast_toNat (ord_ne_top x.2))

@[simp]
/--
lemma `ordMonoidWithZeroHom_eq_ordMonoidHom` / 引理 `ordMonoidWithZeroHom_eq_ordMonoidHom`

English:
lemma ordMonoidWithZeroHom_eq_ordMonoidHom
  given: [Nontrivial R] (x : R⁰)
  proof: by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← ENat.natCast_lift (ord R x.1) (ord_lt_top x.2)]; rw [ENat.recTopCoe_natCast]; rw [ENat.natCast_lift]; rw [ENat.lift_eq_toNat_of_lt_top]

中文:
引理 ordMonoidWithZeroHom_eq_ordMonoidHom
  条件: [非平凡 R] (x : R⁰)
  证明: by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← ENat.natCast_lift (ord R x.1) (ord_lt_top x.2)]; rw [ENat.recTopCoe_natCast]; rw [ENat.natCast_lift]; rw [ENat.lift_eq_toNat_of_lt_top]

Depends on / 依赖: ENat.lift_eq_toNat_of_lt_top, ENat.natCast_lift, ENat.recTopCoe_natCast, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, SetLike, SetLike.coe_mem, coe_mem, coe_mk, lift_eq_toNat_of_lt_top, natCast_lift, ordMonoidHom, ordMonoidWithZeroHom_eq_ord, ord_lt_top, recTopCoe_natCast, toAdd_ofAdd
-/
lemma ordMonoidWithZeroHom_eq_ordMonoidHom [Nontrivial R] (x : R⁰) :
    .coe (.ofAdd ((ordMonoidHom x).toAdd : Int)) = ordMonoidWithZeroHom R x := by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← ENat.natCast_lift (ord R x.1) (ord_lt_top x.2)]; rw [ENat.recTopCoe_natCast]; rw [ENat.natCast_lift]; rw [ENat.lift_eq_toNat_of_lt_top]

/--
lemma `ordMonoidWithZeroHom_ne_zero` / 引理 `ordMonoidWithZeroHom_ne_zero`

English:
lemma ordMonoidWithZeroHom_ne_zero
  given: [Nontrivial R] {a : R} (ha : a in nonZeroDivisors R)
  proof: by
  lift a to R⁰ using ha
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom]

中文:
引理 ordMonoidWithZeroHom_ne_zero
  条件: [非平凡 R] {a : R} (ha : a in nonZeroDivisors R)
  证明: by
  lift a to R⁰ using ha
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom]

Depends on / 依赖: ordMonoidWithZeroHom_eq_ordMonoidHom
-/
lemma ordMonoidWithZeroHom_ne_zero [Nontrivial R] {a : R} (ha : a in nonZeroDivisors R) :
    ordMonoidWithZeroHom R a != 0 := by
  lift a to R⁰ using ha
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom]

variable [Nontrivial R]

/--
lemma `ord_le_iff` / 引理 `ord_le_iff`

English:
lemma ord_le_iff
  given: {a b : R} (ha : a in nonZeroDivisors R) (hb : b in nonZeroDivisors R)
  proof: by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom, ← ordMonoidHom_eq_ord]

中文:
引理 ord_le_iff
  条件: {a b : R} (ha : a in nonZeroDivisors R) (hb : b in nonZeroDivisors R)
  证明: by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom, ← ordMonoidHom_eq_ord]

Depends on / 依赖: ordMonoidHom_eq_ord, ordMonoidWithZeroHom_eq_ordMonoidHom
-/
lemma ord_le_iff {a b : R} (ha : a in nonZeroDivisors R) (hb : b in nonZeroDivisors R) :
    ord R a <= ord R b ↔ ordMonoidWithZeroHom R a <= ordMonoidWithZeroHom R b := by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom, ← ordMonoidHom_eq_ord]

end NoetherianDimLEOne

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/--
In a discrete valuation ring, `ord R x` is the same as `addVal R x`. We prefer the second spelling
here for most purposes.
-/
@[simp]
/--
lemma `ord_eq_addVal` / 引理 `ord_eq_addVal`

English:
lemma ord_eq_addVal
  given: (x : R)
  statement: ord R x = IsDiscreteValuationRing.addVal R x
  proof: by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact IsDiscreteValuationRing.not_krullDimLE_zero R inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul]; rw [ord_pow]; rw [ord_of_irreducible hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

中文:
引理 ord_eq_addVal
  条件: (x : R)
  结论: ord R x = 是离散赋值环.addVal R x
  证明: by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact IsDiscreteValuationRing.not_krullDimLE_zero R inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul]; rw [ord_pow]; rw [ord_of_irreducible hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

Depends on / 依赖: AddValuation, AddValuation.map_zero, Ideal.span_singleton_zero, IsArtinianRing, IsDiscreteVal, IsDiscreteValuationRing, IsDiscreteValuationRing.exists_irreducible, IsDiscreteValuationRing.not_krullDimLE_zero, LinearEquiv, LinearEquiv.isArtinian_iff, Module, Module.length_ne_top_iff, Submodule, Submodule.quotEquivOfEqBot, exists_irreducible, isArtinian_iff, isFiniteLength_iff_isNoetherian_isArtinian, length_ne_top_iff, map_zero, not_krullDimLE_zero
-/
lemma ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact IsDiscreteValuationRing.not_krullDimLE_zero R inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul]; rw [ord_pow]; rw [ord_of_irreducible hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

open IsDiscreteValuationRing

/--
lemma `ord_eq_iff_associated` / 引理 `ord_eq_iff_associated`

English:
lemma ord_eq_iff_associated
  given: (x y : R)
  proof: by simp [addVal_eq_iff_associated]

中文:
引理 ord_eq_iff_associated
  条件: (x y : R)
  证明: by simp [addVal_eq_iff_associated]

Depends on / 依赖: addVal_eq_iff_associated
-/
lemma ord_eq_iff_associated (x y : R) :
    ord R x = ord R y ↔ Associated x y := by simp [addVal_eq_iff_associated]

/--
theorem `ord_add` / 定理 `ord_add`

English:
theorem ord_add
  given: (x y : R)
  statement: min (Ring.ord R x) (Ring.ord R y) <= Ring.ord R (x + y)
  proof: by
  grw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y), IsDiscreteValuationRing.addVal_add]

中文:
定理 ord_add
  条件: (x y : R)
  结论: 最小值 (环.ord R x) (环.ord R y) <= 环.ord R (x + y)
  证明: by
  grw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y), IsDiscreteValuationRing.addVal_add]

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.addVal_add, addVal_add, ord_eq_addVal
-/
theorem ord_add (x y : R) : min (Ring.ord R x) (Ring.ord R y) <= Ring.ord R (x + y) := by
  grw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y), IsDiscreteValuationRing.addVal_add]

end IsDiscreteValuationRing

section ordFrac

variable [IsDomain R] [IsNoetherianRing R] [KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
lemma `ordFrac_ge_one_of_ne_zero` / 引理 `ordFrac_ge_one_of_ne_zero`

English:
lemma ordFrac_ge_one_of_ne_zero
  given: {x : R} (hx : x != 0)
  proof: by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top (a := x) (by simpa))
  simp_rw [ordFrac_eq_ord R hx, ordMonoidWithZeroHom_eq_coe _ (by simpa) hm.symm,
    WithZero.one_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le, Nat.cast_nonneg _]

中文:
引理 ordFrac_ge_one_of_ne_zero
  条件: {x : R} (hx : x != 0)
  证明: by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top (a := x) (by simpa))
  simp_rw [ordFrac_eq_ord R hx, ordMonoidWithZeroHom_eq_coe _ (by simpa) hm.symm,
    WithZero.one_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le, Nat.cast_nonneg _]

Depends on / 依赖: ENat.ne_top_iff_exists.mp, Multiplicative, Multiplicative.ofAdd_le, Nat.cast_nonneg, WithZero, WithZero.one_le_coe, cast_nonneg, hm.symm, ne_top_iff_exists, ofAdd_le, ofAdd_zero, one_le_coe, ordFrac_eq_ord, ordMonoidWithZeroHom_eq_coe, ord_ne_top, simp_rw
-/
lemma ordFrac_ge_one_of_ne_zero {x : R} (hx : x != 0) :
    1 <= ordFrac R (algebraMap R K x) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top (a := x) (by simpa))
  simp_rw [ordFrac_eq_ord R hx, ordMonoidWithZeroHom_eq_coe _ (by simpa) hm.symm,
    WithZero.one_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le, Nat.cast_nonneg _]

/--
lemma `ordFrac_le_smul` / 引理 `ordFrac_le_smul`

English:
lemma ordFrac_le_smul
  statement: {S : Type*} [CommRing S] [Algebra S R] [Algebra S K]
  proof: by
  by_cases j : f = 0
  · simp [j]
  suffices ordFrac R f <= ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  apply le_mul_of_one_le_left'
  simp [IsScalarTower.algebraMap_eq S R K, ordFrac_ge_one_of_ne_zero ha]

@[simp]

中文:
引理 ordFrac_le_smul
  结论: {S : 类型} [交换环 S] [代数 S R] [代数 S K]
  证明: by
  by_cases j : f = 0
  · simp [j]
  suffices ordFrac R f <= ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  apply le_mul_of_one_le_left'
  simp [IsScalarTower.algebraMap_eq S R K, ordFrac_ge_one_of_ne_zero ha]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, algebraMap_smul, le_mul_of_one_le_left, map_mul, ne_eq, ordFrac, ordFrac_ge_one_of_ne_zero, smul_eq_mul
-/
lemma ordFrac_le_smul {S : Type*} [CommRing S] [Algebra S R] [Algebra S K]
    [IsScalarTower S R K] (a : S) (ha : algebraMap S R a != 0) (f : K) :
    Ring.ordFrac R f <= Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp [j]
  suffices ordFrac R f <= ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  apply le_mul_of_one_le_left'
  simp [IsScalarTower.algebraMap_eq S R K, ordFrac_ge_one_of_ne_zero ha]

@[simp]
/--
lemma `ordFrac_of_isUnit` / 引理 `ordFrac_of_isUnit`

English:
lemma ordFrac_of_isUnit
  given: {x : R} (hx : IsUnit x)
  statement: ordFrac R (algebraMap R K x) = 1
  proof: by
  simp [ordFrac_eq_ord R (IsUnit.ne_zero hx), IsUnit.mem_nonZeroDivisors hx,
      ordMonoidWithZeroHom_eq_ord, ord_of_isUnit hx]

中文:
引理 ordFrac_of_isUnit
  条件: {x : R} (hx : 是单位 x)
  结论: ordFrac R (algebraMap R K x) = 1
  证明: by
  simp [ordFrac_eq_ord R (IsUnit.ne_zero hx), IsUnit.mem_nonZeroDivisors hx,
      ordMonoidWithZeroHom_eq_ord, ord_of_isUnit hx]

Depends on / 依赖: IsUnit, IsUnit.mem_nonZeroDivisors, IsUnit.ne_zero, mem_nonZeroDivisors, ne_zero, ordFrac_eq_ord, ordMonoidWithZeroHom_eq_ord, ord_of_isUnit
-/
lemma ordFrac_of_isUnit {x : R} (hx : IsUnit x) : ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_ord R (IsUnit.ne_zero hx), IsUnit.mem_nonZeroDivisors hx,
      ordMonoidWithZeroHom_eq_ord, ord_of_isUnit hx]

end ordFrac
section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
lemma `ordMonoidWithZeroHom_eq_intValuation` / 引理 `ordMonoidWithZeroHom_eq_intValuation`

English:
lemma ordMonoidWithZeroHom_eq_intValuation
  given: {x : R} (h : x in nonZeroDivisors R)
  proof: by
  simp [ordMonoidWithZeroHom_eq_ord h, IsDiscreteValuationRing.intValuation_maximalIdeal]

中文:
引理 ordMonoidWithZeroHom_eq_intValuation
  条件: {x : R} (h : x in nonZeroDivisors R)
  证明: by
  simp [ordMonoidWithZeroHom_eq_ord h, IsDiscreteValuationRing.intValuation_maximalIdeal]

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.intValuation_maximalIdeal, intValuation_maximalIdeal, ordMonoidWithZeroHom_eq_ord
-/
lemma ordMonoidWithZeroHom_eq_intValuation {x : R} (h : x in nonZeroDivisors R) :
    (ordMonoidWithZeroHom R) x = ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  simp [ordMonoidWithZeroHom_eq_ord h, IsDiscreteValuationRing.intValuation_maximalIdeal]

/--
lemma `ordFrac_eq_intValuation` / 引理 `ordFrac_eq_intValuation`

English:
lemma ordFrac_eq_intValuation
  given: {x : R} (h : x != 0)
  statement: (ordFrac R) ((algebraMap R K) x) =
  proof: by
  rw [ordFrac_eq_ord R h]; rw [ordMonoidWithZeroHom_eq_intValuation (mem_nonZeroDivisors_of_ne_zero h)]

中文:
引理 ordFrac_eq_intValuation
  条件: {x : R} (h : x != 0)
  结论: (ordFrac R) ((algebraMap R K) x) =
  证明: by
  rw [ordFrac_eq_ord R h]; rw [ordMonoidWithZeroHom_eq_intValuation (mem_nonZeroDivisors_of_ne_zero h)]

Depends on / 依赖: mem_nonZeroDivisors_of_ne_zero, ordFrac_eq_ord, ordMonoidWithZeroHom_eq_intValuation
-/
lemma ordFrac_eq_intValuation {x : R} (h : x != 0) : (ordFrac R) ((algebraMap R K) x) =
    ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  rw [ordFrac_eq_ord R h]; rw [ordMonoidWithZeroHom_eq_intValuation (mem_nonZeroDivisors_of_ne_zero h)]

/--
theorem `ordFrac_eq_inverse_comp_valuation` / 定理 `ordFrac_eq_inverse_comp_valuation`

English:
theorem ordFrac_eq_inverse_comp_valuation
  proof: by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_intValuation _, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal]

中文:
定理 ordFrac_eq_inverse_comp_valuation
  证明: by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_intValuation _, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal]

Depends on / 依赖: HeightOneSpectrum, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDiscreteValuationRing, IsDiscreteValuationRing.intValuation_maximalIdeal, IsFractionRing, IsFractionRing.div_surjective, div_surjective, intValuation_maximalIdeal, ordFrac_eq_intValuation, valuation_of_algebraMap
-/
theorem ordFrac_eq_inverse_comp_valuation :
    ordFrac R = MonoidWithZeroHom.comp MonoidWithZero.inverse
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).toMonoidWithZeroHom := by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_intValuation _, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal]

/--
theorem `ordFrac_eq_valuation_inv` / 定理 `ordFrac_eq_valuation_inv`

English:
theorem ordFrac_eq_valuation_inv
  given: (x : K)
  proof: by
  simp [ordFrac_eq_inverse_comp_valuation]

中文:
定理 ordFrac_eq_valuation_inv
  条件: (x : K)
  证明: by
  simp [ordFrac_eq_inverse_comp_valuation]

Depends on / 依赖: ordFrac_eq_inverse_comp_valuation
-/
theorem ordFrac_eq_valuation_inv (x : K) :
    ordFrac R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹ := by
  simp [ordFrac_eq_inverse_comp_valuation]

/--
lemma `ordFrac_irreducible` / 引理 `ordFrac_irreducible`

English:
lemma ordFrac_irreducible
  proof: by
  simp [ordFrac_eq_valuation_inv, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, ← WithZero.exp_eq_coe_ofAdd]

中文:
引理 ordFrac_irreducible
  证明: by
  simp [ordFrac_eq_valuation_inv, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, ← WithZero.exp_eq_coe_ofAdd]

Depends on / 依赖: HeightOneSpectrum, IsDedekindDomain, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDiscreteValuationRing, IsDiscreteValuationRing.addVal_uniformizer, IsDiscreteValuationRing.intValuation_maximalIdeal, WithZero, WithZero.exp_eq_coe_ofAdd, addVal_uniformizer, exp_eq_coe_ofAdd, intValuation_maximalIdeal, ordFrac_eq_valuation_inv, valuation_of_algebraMap
-/
lemma ordFrac_irreducible
    {ϖ : R} (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R K ϖ) = WithZero.exp 1 := by
  simp [ordFrac_eq_valuation_inv, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, ← WithZero.exp_eq_coe_ofAdd]

open IsDedekindDomain HeightOneSpectrum

/--
lemma `isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` / 引理 `isUnit_iff_ordFrac_one_of_isDiscreteValuationRing`

English:
lemma isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
  given: {x : R}
  proof: by
  simp [ordFrac_eq_valuation_inv, IsDiscreteValuationRing.maximalIdeal]

中文:
引理 isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
  条件: {x : R}
  证明: by
  simp [ordFrac_eq_valuation_inv, IsDiscreteValuationRing.maximalIdeal]

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.maximalIdeal, maximalIdeal, ordFrac_eq_valuation_inv
-/
lemma isUnit_iff_ordFrac_one_of_isDiscreteValuationRing {x : R} :
    IsUnit x ↔ ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_valuation_inv, IsDiscreteValuationRing.maximalIdeal]

/--
lemma `mker_ordFrac_eq_isUnitSubmonoid` / 引理 `mker_ordFrac_eq_isUnitSubmonoid`

English:
lemma mker_ordFrac_eq_isUnitSubmonoid
  proof: by
  rw [ordFrac_eq_inverse_comp_valuation]; rw [← MonoidWithZeroHom.comap_mker]; rw [MonoidWithZeroHom.mker_inverse]
  exact IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid

中文:
引理 mker_ordFrac_eq_isUnitSubmonoid
  证明: by
  rw [ordFrac_eq_inverse_comp_valuation]; rw [← MonoidWithZeroHom.comap_mker]; rw [MonoidWithZeroHom.mker_inverse]
  exact IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid, MonoidWithZeroHom, MonoidWithZeroHom.comap_mker, MonoidWithZeroHom.mker_inverse, comap_mker, mker_inverse, mker_valuation_eq_isUnitSubmonoid, ordFrac_eq_inverse_comp_valuation
-/
lemma mker_ordFrac_eq_isUnitSubmonoid :
    MonoidHom.mker (ordFrac R) = (IsUnit.submonoid R).map (algebraMap R K) := by
  rw [ordFrac_eq_inverse_comp_valuation]; rw [← MonoidWithZeroHom.comap_mker]; rw [MonoidWithZeroHom.mker_inverse]
  exact IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid

/--
theorem `ordFrac_add` / 定理 `ordFrac_add`

English:
theorem ordFrac_add
  given: (x y : K) (h1 : x + y != 0)
  proof: by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]

中文:
定理 ordFrac_add
  条件: (x y : K) (h1 : x + y != 0)
  证明: by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]

Depends on / 依赖: Valuation, Valuation.map_add, WithZero, WithZero.pos_iff_ne_zero, map_add, min_inv_inv_le, ordFrac_eq_valuation_inv, pos_iff_ne_zero
-/
theorem ordFrac_add (x y : K) (h1 : x + y != 0) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) <= Ring.ordFrac R (x + y) := by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]

/--
theorem `associated_of_ordFrac_eq` / 定理 `associated_of_ordFrac_eq`

English:
theorem associated_of_ordFrac_eq
  statement: (x y : K)
  proof: by
  rw [ordFrac_eq_valuation_inv]; rw [ordFrac_eq_valuation_inv]; rw [inv_inj] at h
  exact IsDiscreteValuationRing.associated_of_valuation_eq _ _ h

中文:
定理 associated_of_ordFrac_eq
  结论: (x y : K)
  证明: by
  rw [ordFrac_eq_valuation_inv]; rw [ordFrac_eq_valuation_inv]; rw [inv_inj] at h
  exact IsDiscreteValuationRing.associated_of_valuation_eq _ _ h

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.associated_of_valuation_eq, associated_of_valuation_eq, inv_inj, ordFrac_eq_valuation_inv
-/
theorem associated_of_ordFrac_eq (x y : K)
    (h : ordFrac R x = ordFrac R y) : exists u : Rˣ, u • x = y := by
  rw [ordFrac_eq_valuation_inv]; rw [ordFrac_eq_valuation_inv]; rw [inv_inj] at h
  exact IsDiscreteValuationRing.associated_of_valuation_eq _ _ h

end IsDiscreteValuationRing

end Ring
