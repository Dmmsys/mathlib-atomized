/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Extension of Valuations

In this file, we define the typeclass for valuation extensions and prove basic facts about the
extension of valuations. Let `A` be an `R` algebra, equipped with valuations `vA` and `vR`
respectively. Here, the extension of a valuation means that the pullback of valuation `vA` to `R`
is equivalent to the valuation `vR` on `R`. We only require equivalence, not equality, of
valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. This holds automatically
when `R` is a division ring and `A` is nontrivial.

A motivation for choosing the more flexible `Valuation.Equiv` rather than strict equality here is
to allow for possible normalization. As an example, consider a finite extension `K` of `ℚ_[p]`,
which is a discretely valued field. We may choose the valuation on `K` to be either:

1. the valuation where the uniformizer is mapped to one (more precisely, `-1` in `ℤᵐ⁰`) or

2. the valuation where `p` is mapped to one.

For the algebraic closure of `ℚ_[p]`, if we choose the valuation of `p` to be one, then the
restriction of this valuation to `K` equals the second valuation, but is only equivalent to the
first valuation. The flexibility of equivalence here allows us to develop theory for both cases
without first determining the normalizations once and for all.

## Main Definition

* `Valuation.HasExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation
  `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuations

-/

@[expose] public section

open Module

namespace Valuation

variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)

/--
Definition of `HasExtension` / `HasExtension` 的定义

English:
class HasExtension
  parameters: : Prop where
  axioms and operations (1):
    - val_isEquiv_comap : vR.IsEquiv vA.comap (algebraMap R A)

中文:
类 HasExtension
  参数: : 命题 where
  公理与运算 (1 个):
    - val_isEquiv_comap : vR.IsEquiv vA.comap (algebraMap R A)
-/
class HasExtension : Prop where
  /-- The valuation `vR` on `R` is equivalent to the comap of the valuation `vA` on `A` -/
val_isEquiv_comap : vR.IsEquiv vA.comap (algebraMap R A)

namespace HasExtension

section algebraMap

variable [vR.HasExtension vA]

-- @[simp] does not work because `vR` cannot be inferred from `R`.
/--
theorem `val_map_le_iff` / 定理 `val_map_le_iff`

English:
theorem val_map_le_iff
  given: (x y : R)
  statement: vA (algebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
  proof: val_isEquiv_comap.symm x y

中文:
定理 val_map_le_iff
  条件: (x y : R)
  结论: vA (algebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
  证明: val_isEquiv_comap.symm x y

Depends on / 依赖: val_isEquiv_comap, val_isEquiv_comap.symm
-/
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y :=
  val_isEquiv_comap.symm x y

/--
theorem `val_map_lt_iff` / 定理 `val_map_lt_iff`

English:
theorem val_map_lt_iff
  given: (x y : R)
  statement: vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y
  proof: by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)

中文:
定理 val_map_lt_iff
  条件: (x y : R)
  结论: vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y
  证明: by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)

Depends on / 依赖: not_le, val_map_le_iff
-/
theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y := by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)

/--
theorem `val_map_eq_iff` / 定理 `val_map_eq_iff`

English:
theorem val_map_eq_iff
  given: (x y : R)
  statement: vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y
  proof: (IsEquiv.eq_iff val_isEquiv_comap).symm

中文:
定理 val_map_eq_iff
  条件: (x y : R)
  结论: vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y
  证明: (IsEquiv.eq_iff val_isEquiv_comap).symm

Depends on / 依赖: IsEquiv, IsEquiv.eq_iff, eq_iff, val_isEquiv_comap
-/
theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.eq_iff val_isEquiv_comap).symm

/--
theorem `val_map_le_one_iff` / 定理 `val_map_le_one_iff`

English:
theorem val_map_le_one_iff
  given: (x : R)
  statement: vA (algebraMap R A x) <= 1 ↔ vR x <= 1
  proof: by
  simpa only [map_one] using val_map_le_iff vR vA x 1

中文:
定理 val_map_le_one_iff
  条件: (x : R)
  结论: vA (algebraMap R A x) <= 1 ↔ vR x <= 1
  证明: by
  simpa only [map_one] using val_map_le_iff vR vA x 1

Depends on / 依赖: map_one, val_map_le_iff
-/
theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) <= 1 ↔ vR x <= 1 := by
  simpa only [map_one] using val_map_le_iff vR vA x 1

/--
theorem `val_map_lt_one_iff` / 定理 `val_map_lt_one_iff`

English:
theorem val_map_lt_one_iff
  given: (x : R)
  statement: vA (algebraMap R A x) < 1 ↔ vR x < 1
  proof: by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not

中文:
定理 val_map_lt_one_iff
  条件: (x : R)
  结论: vA (algebraMap R A x) < 1 ↔ vR x < 1
  证明: by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not

Depends on / 依赖: map_one, not_le, val_map_le_iff
-/
theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 := by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not

/--
theorem `val_map_eq_one_iff` / 定理 `val_map_eq_one_iff`

English:
theorem val_map_eq_one_iff
  given: (x : R)
  statement: vA (algebraMap R A x) = 1 ↔ vR x = 1
  proof: by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

中文:
定理 val_map_eq_one_iff
  条件: (x : R)
  结论: vA (algebraMap R A x) = 1 ↔ vR x = 1
  证明: by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

Depends on / 依赖: and_congr, le_antisymm_iff, map_one, val_map_le_iff
-/
theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 := by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

end algebraMap

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : vR.HasExtension vR where
  body: by
    simp only [Algebra.algebraMap_self, comap_id, IsEquiv.refl]

中文:
实例 id
  签名: : vR.HasExtension vR where
  定义体: by
    simp only [Algebra.algebraMap_self, comap_id, IsEquiv.refl]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, IsEquiv, IsEquiv.refl, algebraMap_self, comap_id
-/
instance id : vR.HasExtension vR where
  val_isEquiv_comap := by
    simp only [Algebra.algebraMap_self, comap_id, IsEquiv.refl]

section integer

variable {K : Type*} [Field K] [Algebra K A] {ΓR ΓA ΓK : Type*}
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [vR.HasExtension vA]

/--
theorem `ofComapInteger` / 定理 `ofComapInteger`

English:
theorem ofComapInteger
  given: (h : vA.integer.comap (algebraMap K A) = vK.integer)
  proof: by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]

中文:
定理 ofComapInteger
  条件: (h : vA.integer.comap (algebraMap K A) = vK.integer)
  证明: by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]

Depends on / 依赖: Subring, Subring.mem_comap, Valuation, Valuation.mem_integer_iff, comap_apply, isEquiv_iff_val_le_one, mem_comap, mem_integer_iff, simp_rw
-/
theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    vK.HasExtension vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]

/--
Instance `instAlgebraInteger` / 实例 `instAlgebraInteger`

English:
instance instAlgebraInteger
  signature: : Algebra vR.integer vA.integer where
  body: ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  algebraMap := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Su

中文:
实例 instAlgebraInteger
  签名: : Algebra vR.integer vA.integer where
  定义体: ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  algebraMap := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Su
-/
instance instAlgebraInteger : Algebra vR.integer vA.integer where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  algebraMap := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

@[simp, norm_cast]
/--
theorem `val_smul` / 定理 `val_smul`

English:
theorem val_smul
  given: (r : vR.integer) (a : vA.integer)
  statement: ↑(r • a : vA.integer) = (r : R) • (a : A)
  proof: by
  rfl

@[simp]

中文:
定理 val_smul
  条件: (r : vR.integer) (a : vA.integer)
  结论: ↑(r • a : vA.integer) = (r : R) • (a : A)
  证明: by
  rfl

@[simp]
-/
theorem val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : R) • (a : A) := by
  rfl

@[simp]
/--
lemma `mk_smul_mk` / 引理 `mk_smul_mk`

English:
lemma mk_smul_mk
  given: (r : R) (hr) (a : A) (ha)
  proof: rfl

@[simp, norm_cast]

中文:
引理 mk_smul_mk
  条件: (r : R) (hr) (a : A) (ha)
  证明: rfl

@[simp, norm_cast]
-/
lemma mk_smul_mk (r : R) (hr) (a : A) (ha) :
    (⟨r, hr⟩ : vR.integer) • (⟨a, ha⟩ : vA.integer) =
      ⟨r • a, Algebra.smul_def r a ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr hr) ha⟩ := rfl

@[simp, norm_cast]
/--
theorem `val_algebraMap` / 定理 `val_algebraMap`

English:
theorem val_algebraMap
  given: (r : vR.integer)
  proof: by
  rfl

中文:
定理 val_algebraMap
  条件: (r : vR.integer)
  证明: by
  rfl
-/
theorem val_algebraMap (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl

/--
Instance `instIsScalarTowerInteger` / 实例 `instIsScalarTowerInteger`

English:
instance instIsScalarTowerInteger
  signature: : IsScalarTower vR.integer vA.integer A where
  body: by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

中文:
实例 instIsScalarTowerInteger
  签名: : IsScalarTower vR.integer vA.integer A where
  定义体: by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

Depends on / 依赖: Algebra, Algebra.smul_def, mul_assoc, smul_def
-/
instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

/--
Instance `instIsTorsionFreeInteger` / 实例 `instIsTorsionFreeInteger`

English:
instance instIsTorsionFreeInteger
  signature: [IsDomain R] [IsTorsionFree R A]
  body: .of_smul_eq_zero by simp

中文:
实例 instIsTorsionFreeInteger
  签名: [IsDomain R] [IsTorsionFree R A]
  定义体: .of_smul_eq_zero by simp

Depends on / 依赖: of_smul_eq_zero
-/
instance instIsTorsionFreeInteger [IsDomain R] [IsTorsionFree R A] :
IsTorsionFree vR.integer vA.integer := .of_smul_eq_zero by simp

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  given: [vK.HasExtension vA] [Nontrivial A]
  proof: FaithfulSMul.algebraMap_injective _ _

@[instance]

中文:
定理 algebraMap_injective
  条件: [vK.HasExtension vA] [Nontrivial A]
  证明: FaithfulSMul.algebraMap_injective _ _

@[instance]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
theorem algebraMap_injective [vK.HasExtension vA] [Nontrivial A] :
    Function.Injective (algebraMap vK.integer vA.integer) :=
  FaithfulSMul.algebraMap_injective _ _

@[instance]
/--
theorem `instIsLocalHomValuationInteger` / 定理 `instIsLocalHomValuationInteger`

English:
theorem instIsLocalHomValuationInteger
  statement: {S ΓS : Type*} [CommRing S]
  proof: by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

中文:
定理 instIsLocalHomValuationInteger
  结论: {S ΓS : 类型} [CommRing S]
  证明: by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

Depends on / 依赖: Valuation, Valuation.integer.integers, algebraMap, hr.map, integer, integers, isUnit_map_iff, isUnit_of_one, one_of_isUnit, val_map_eq_one_iff
-/
theorem instIsLocalHomValuationInteger {S ΓS : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero ΓS]
    [Algebra R S] [IsLocalHom (algebraMap R S)] {vS : Valuation S ΓS}
    [vR.HasExtension vS] : IsLocalHom (algebraMap vR.integer vS.integer) where
  map_nonunit r hr := by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

end integer

section AlgebraInstances

open IsLocalRing Valuation ValuationSubring

variable {K L Γ₀ Γ₁ : outParam Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀)
  (vL : Valuation L Γ₁) [vK.HasExtension vL]

local notation "K₀" => Valuation.valuationSubring vK
local notation "L₀" => Valuation.valuationSubring vL

/--
lemma `algebraMap_mem_valuationSubring` / 引理 `algebraMap_mem_valuationSubring`

English:
lemma algebraMap_mem_valuationSubring
  given: (x : K₀)
  statement: algebraMap K L x in L₀
  proof: by
  rw [mem_valuationSubring_iff]; rw [← _root_.map_one vL]; rw [← _root_.map_one (algebraMap K L)]; rw [val_map_le_iff (vR := vK)]; rw [_root_.map_one]
  exact x.2

中文:
引理 algebraMap_mem_valuationSubring
  条件: (x : K₀)
  结论: algebraMap K L x in L₀
  证明: by
  rw [mem_valuationSubring_iff]; rw [← _root_.map_one vL]; rw [← _root_.map_one (algebraMap K L)]; rw [val_map_le_iff (vR := vK)]; rw [_root_.map_one]
  exact x.2

Depends on / 依赖: _root_, _root_.map_one, algebraMap, map_one, mem_valuationSubring_iff, val_map_le_iff
-/
lemma algebraMap_mem_valuationSubring (x : K₀) : algebraMap K L x in L₀ := by
  rw [mem_valuationSubring_iff]; rw [← _root_.map_one vL]; rw [← _root_.map_one (algebraMap K L)]; rw [val_map_le_iff (vR := vK)]; rw [_root_.map_one]
  exact x.2

/--
Instance `instAlgebra_valuationSubring` / 实例 `instAlgebra_valuationSubring`

English:
instance instAlgebra_valuationSubring
  signature: : Algebra K₀ L₀
  body: inferInstanceAs (Algebra vK.integer vL.integer)

@[simp]

中文:
实例 instAlgebra_valuationSubring
  签名: : Algebra K₀ L₀
  定义体: inferInstanceAs (Algebra vK.integer vL.integer)

@[simp]

Depends on / 依赖: Algebra, integer, vK.integer, vL.integer
-/
instance instAlgebra_valuationSubring : Algebra K₀ L₀ :=
  inferInstanceAs (Algebra vK.integer vL.integer)

@[simp]
/--
lemma `coe_algebraMap_valuationSubring_eq` / 引理 `coe_algebraMap_valuationSubring_eq`

English:
lemma coe_algebraMap_valuationSubring_eq
  given: (x : K₀)
  proof: rfl

中文:
引理 coe_algebraMap_valuationSubring_eq
  条件: (x : K₀)
  证明: rfl
-/
lemma coe_algebraMap_valuationSubring_eq (x : K₀) :
    (algebraMap K₀ L₀ x : L) = algebraMap K L (x : K) := rfl

/--
Instance `instIsScalarTower_valuationSubring` / 实例 `instIsScalarTower_valuationSubring`

English:
instance instIsScalarTower_valuationSubring
  signature: : IsScalarTower K₀ K L
  body: inferInstanceAs (IsScalarTower vK.integer K L)

中文:
实例 instIsScalarTower_valuationSubring
  签名: : IsScalarTower K₀ K L
  定义体: inferInstanceAs (IsScalarTower vK.integer K L)

Depends on / 依赖: IsScalarTower, integer, vK.integer
-/
instance instIsScalarTower_valuationSubring : IsScalarTower K₀ K L :=
  inferInstanceAs (IsScalarTower vK.integer K L)

/--
Instance `instIsScalarTower_valuationSubring'` / 实例 `instIsScalarTower_valuationSubring'`

English:
instance instIsScalarTower_valuationSubring'
  signature: : IsScalarTower K₀ L₀ L
  body: instIsScalarTowerInteger

中文:
实例 instIsScalarTower_valuationSubring'
  签名: : IsScalarTower K₀ L₀ L
  定义体: instIsScalarTowerInteger

Depends on / 依赖: instIsScalarTowerInteger
-/
instance instIsScalarTower_valuationSubring' : IsScalarTower K₀ L₀ L :=
  instIsScalarTowerInteger

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (algebraMap K₀ L₀)
  body: instIsLocalHomValuationInteger

中文:
实例 :
  签名: IsLocalHom (algebraMap K₀ L₀)
  定义体: instIsLocalHomValuationInteger

Depends on / 依赖: instIsLocalHomValuationInteger
-/
instance : IsLocalHom (algebraMap K₀ L₀) := instIsLocalHomValuationInteger

/--
lemma `algebraMap_mem_maximalIdeal_iff` / 引理 `algebraMap_mem_maximalIdeal_iff`

English:
lemma algebraMap_mem_maximalIdeal_iff
  given: {x : K₀}
  proof: by
  simp [mem_maximalIdeal, map_mem_nonunits_iff, _root_.mem_nonunits_iff]

中文:
引理 algebraMap_mem_maximalIdeal_iff
  条件: {x : K₀}
  证明: by
  simp [mem_maximalIdeal, map_mem_nonunits_iff, _root_.mem_nonunits_iff]

Depends on / 依赖: _root_, _root_.mem_nonunits_iff, map_mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff
-/
lemma algebraMap_mem_maximalIdeal_iff {x : K₀} :
    algebraMap K₀ L₀ x in (maximalIdeal L₀) ↔ x in maximalIdeal K₀ := by
  simp [mem_maximalIdeal, map_mem_nonunits_iff, _root_.mem_nonunits_iff]

/--
lemma `maximalIdeal_comap_algebraMap_eq_maximalIdeal` / 引理 `maximalIdeal_comap_algebraMap_eq_maximalIdeal`

English:
lemma maximalIdeal_comap_algebraMap_eq_maximalIdeal
  proof: Ideal.ext fun _ => by rw [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]

中文:
引理 maximalIdeal_comap_algebraMap_eq_maximalIdeal
  证明: Ideal.ext fun _ => by rw [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]

Depends on / 依赖: Ideal.ext, Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff, mem_comap
-/
lemma maximalIdeal_comap_algebraMap_eq_maximalIdeal :
    (maximalIdeal L₀).comap (algebraMap K₀ L₀) = maximalIdeal K₀ :=
  Ideal.ext fun _ => by rw [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀)
  body: ⟨(maximalIdeal_comap_algebraMap_eq_maximalIdeal _ _).symm⟩

中文:
实例 :
  签名: Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀)
  定义体: ⟨(maximalIdeal_comap_algebraMap_eq_maximalIdeal _ _).symm⟩

Depends on / 依赖: maximalIdeal_comap_algebraMap_eq_maximalIdeal
-/
instance : Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀) :=
  ⟨(maximalIdeal_comap_algebraMap_eq_maximalIdeal _ _).symm⟩

/--
lemma `algebraMap_residue_eq_residue_algebraMap` / 引理 `algebraMap_residue_eq_residue_algebraMap`

English:
lemma algebraMap_residue_eq_residue_algebraMap
  given: (x : K₀)
  proof: rfl

中文:
引理 algebraMap_residue_eq_residue_algebraMap
  条件: (x : K₀)
  证明: rfl
-/
lemma algebraMap_residue_eq_residue_algebraMap (x : K₀) :
    (algebraMap (ResidueField K₀) (ResidueField L₀)) (IsLocalRing.residue K₀ x) =
      IsLocalRing.residue L₀ (algebraMap K₀ L₀ x) :=
  rfl

end AlgebraInstances

end HasExtension

end Valuation
