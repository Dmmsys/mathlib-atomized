/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Units of a number field

We prove some basic results on the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K` and its torsion subgroup.

## Main definition

* `NumberField.Units.torsion`: the torsion subgroup of a number field.

## Main results

* `NumberField.isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if
  `|norm ℚ x| = 1`.

* `NumberField.Units.mem_torsion`: a unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite
  places `w` of `K`.

## Tags
number field, units
-/

@[expose] public section

open scoped NumberField

noncomputable section

open NumberField Units

section Rat

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Rat.RingOfIntegers.isUnit_iff` / 定理 `Rat.RingOfIntegers.isUnit_iff`

English:
theorem Rat.RingOfIntegers.isUnit_iff
  given: {x : 𝓞 Rat}
  statement: IsUnit x ↔ (x : Rat) = 1 ∨ (x : Rat) = -1
  proof: by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 Rat ->+* Int) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

中文:
定理 有理数.RingOf整数egers.isUnit_iff
  条件: {x : 𝓞 有理数}
  结论: 是单位 x ↔ (x : 有理数) = 1 ∨ (x : 有理数) = -1
  证明: by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 Rat ->+* Int) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

Depends on / 依赖: Int.isUnit_iff, Rat.ringOfIntegersEquiv, RingEquiv, RingEquiv.coe_toRingHom, RingEquiv.map_eq_neg_one_iff, RingEquiv.map_eq_one_iff, Subtype, Subtype.coe_injective.eq_iff, coe_injective, coe_toRingHom, eq_iff, isUnit_iff, isUnit_map_iff, map_eq_neg_one_iff, map_eq_one_iff, ringOfIntegersEquiv, simp_rw
-/
theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 Rat} : IsUnit x ↔ (x : Rat) = 1 ∨ (x : Rat) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 Rat ->+* Int) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

/--
theorem `NumberField.isUnit_iff_norm` / 定理 `NumberField.isUnit_iff_norm`

English:
theorem NumberField.isUnit_iff_norm
  given: [NumberField K] {x : 𝓞 K}
  proof: by
  convert! (RingOfIntegers.isUnit_norm Rat (F := K)).symm
  rw [← abs_one]; rw [abs_eq_abs]; rw [← Rat.RingOfIntegers.isUnit_iff]

中文:
定理 数域.isUnit_iff_norm
  条件: [数域 K] {x : 𝓞 K}
  证明: by
  convert! (RingOfIntegers.isUnit_norm Rat (F := K)).symm
  rw [← abs_one]; rw [abs_eq_abs]; rw [← Rat.RingOfIntegers.isUnit_iff]

Depends on / 依赖: Rat.RingOfIntegers.isUnit_iff, RingOfIntegers, RingOfIntegers.isUnit_norm, abs_eq_abs, abs_one, convert, isUnit_iff, isUnit_norm
-/
theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm Rat x : Rat)| = 1 := by
  convert! (RingOfIntegers.isUnit_norm Rat (F := K)).symm
  rw [← abs_one]; rw [abs_eq_abs]; rw [← Rat.RingOfIntegers.isUnit_iff]

end IsUnit

namespace NumberField.Units

section coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeHTC (𝓞 K)ˣ K
  body: ⟨fun x => algebraMap _ K (Units.val x)⟩

中文:
实例 :
  签名: CoeHTC (𝓞 K)ˣ K
  定义体: ⟨fun x => algebraMap _ K (Units.val x)⟩

Depends on / 依赖: Units.val, algebraMap
-/
instance : CoeHTC (𝓞 K)ˣ K :=
  ⟨fun x => algebraMap _ K (Units.val x)⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : (𝓞 K)ˣ -> K)
  proof: RingOfIntegers.coe_injective.comp Units.val_injective

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : (𝓞 K)ˣ -> K)
  证明: RingOfIntegers.coe_injective.comp Units.val_injective

Depends on / 依赖: RingOfIntegers, RingOfIntegers.coe_injective.comp, Units.val_injective, coe_injective, val_injective
-/
theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ -> K) :=
  RingOfIntegers.coe_injective.comp Units.val_injective

variable {K}

/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (u : (𝓞 K)ˣ)
  statement: ((u : 𝓞 K) : K) = (u : K)
  proof: rfl

中文:
定理 coe_coe
  条件: (u : (𝓞 K)ˣ)
  结论: ((u : 𝓞 K) : K) = (u : K)
  证明: rfl
-/
theorem coe_coe (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) = (u : K) := rfl

/--
theorem `_root_.IsPrimitiveRoot.coe_coe_iff` / 定理 `_root_.IsPrimitiveRoot.coe_coe_iff`

English:
theorem _root_.IsPrimitiveRoot.coe_coe_iff
  given: {ν : (𝓞 K)ˣ} {n : Nat}
  proof: IsPrimitiveRoot.map_iff_of_injective
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))) (coe_injective K)

中文:
定理 _root_.是PrimitiveRoot.coe_coe_iff
  条件: {ν : (𝓞 K)ˣ} {n : 自然数}
  证明: IsPrimitiveRoot.map_iff_of_injective
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))) (coe_injective K)

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.map_iff_of_injective, Units.coeHom, algebraMap, coeHom, coe_injective, map_iff_of_injective, toMonoidHom, toMonoidHom.comp
-/
theorem _root_.IsPrimitiveRoot.coe_coe_iff {ν : (𝓞 K)ˣ} {n : Nat} :
    IsPrimitiveRoot (ν : K) n ↔ IsPrimitiveRoot ν n :=
  IsPrimitiveRoot.map_iff_of_injective
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))) (coe_injective K)

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : (𝓞 K)ˣ)
  statement: ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K)
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : (𝓞 K)ˣ)
  结论: ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K)
  证明: rfl
-/
theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : (𝓞 K)ˣ) (n : Nat)
  statement: ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n
  proof: by
  rw [← map_pow]; rw [← val_pow_eq_pow_val]

中文:
定理 coe_pow
  条件: (x : (𝓞 K)ˣ) (n : 自然数)
  结论: ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n
  证明: by
  rw [← map_pow]; rw [← val_pow_eq_pow_val]

Depends on / 依赖: map_pow, val_pow_eq_pow_val
-/
theorem coe_pow (x : (𝓞 K)ˣ) (n : Nat) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n := by
  rw [← map_pow]; rw [← val_pow_eq_pow_val]

/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (x : (𝓞 K)ˣ) (n : Int)
  statement: (↑(x ^ n) : K) = (x : K) ^ n
  proof: by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

中文:
定理 coe_zpow
  条件: (x : (𝓞 K)ˣ) (n : 整数)
  结论: (↑(x ^ n) : K) = (x : K) ^ n
  证明: by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

Depends on / 依赖: Units.coeHom, algebraMap, coeHom, map_zpow
-/
theorem coe_zpow (x : (𝓞 K)ˣ) (n : Int) : (↑(x ^ n) : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : (𝓞 K)ˣ) : K) = (1 : K)
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : (𝓞 K)ˣ) : K) = (1 : K)
  证明: rfl
-/
theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

/--
theorem `coe_neg_one` / 定理 `coe_neg_one`

English:
theorem coe_neg_one
  statement: ((-1 : (𝓞 K)ˣ) : K) = (-1 : K)
  proof: rfl

中文:
定理 coe_neg_one
  结论: ((-1 : (𝓞 K)ˣ) : K) = (-1 : K)
  证明: rfl
-/
theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: (x : (𝓞 K)ˣ)
  statement: (x : K) != 0
  proof: Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

中文:
定理 coe_ne_zero
  条件: (x : (𝓞 K)ˣ)
  结论: (x : K) != 0
  证明: Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

Depends on / 依赖: Subtype, Subtype.coe_injective.ne_iff.mpr, _root_, _root_.Units.ne_zero, coe_injective, ne_iff, ne_zero
-/
theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

variable {K}

/--
Definition of `complexEmbedding` / `complexEmbedding` 的定义

English:
definition complexEmbedding
  signature: (φ : K ->+* Complex)
  body: (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp]

中文:
定义 complexEmbedding
  签名: (φ : K ->+* 复形)
  定义体: (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp]
-/
protected def complexEmbedding (φ : K ->+* Complex) : (𝓞 K)ˣ ->* Complexˣ :=
  (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp]
/--
theorem `complexEmbedding_apply` / 定理 `complexEmbedding_apply`

English:
theorem complexEmbedding_apply
  given: (φ : K ->+* Complex) (u : (𝓞 K)ˣ)
  proof: rfl

中文:
定理 complexEmbedding_apply
  条件: (φ : K ->+* 复形) (u : (𝓞 K)ˣ)
  证明: rfl
-/
protected theorem complexEmbedding_apply (φ : K ->+* Complex) (u : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = φ u := rfl

/--
theorem `complexEmbedding_injective` / 定理 `complexEmbedding_injective`

English:
theorem complexEmbedding_injective
  given: (φ : K ->+* Complex)
  proof: (map_injective φ.injective).comp (map_injective RingOfIntegers.coe_injective)

@[simp]

中文:
定理 complexEmbedding_injective
  条件: (φ : K ->+* 复形)
  证明: (map_injective φ.injective).comp (map_injective RingOfIntegers.coe_injective)

@[simp]
-/
protected theorem complexEmbedding_injective (φ : K ->+* Complex) :
    Function.Injective (Units.complexEmbedding φ) :=
  (map_injective φ.injective).comp (map_injective RingOfIntegers.coe_injective)

@[simp]
/--
theorem `complexEmbedding_inj` / 定理 `complexEmbedding_inj`

English:
theorem complexEmbedding_inj
  given: (φ : K ->+* Complex) (u v : (𝓞 K)ˣ)
  proof: (Units.complexEmbedding_injective φ).eq_iff

中文:
定理 complexEmbedding_inj
  条件: (φ : K ->+* 复形) (u v : (𝓞 K)ˣ)
  证明: (Units.complexEmbedding_injective φ).eq_iff
-/
protected theorem complexEmbedding_inj (φ : K ->+* Complex) (u v : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = Units.complexEmbedding φ v ↔ u = v :=
  (Units.complexEmbedding_injective φ).eq_iff

open NumberField.InfinitePlace

variable (K)

@[simp]
/--
theorem `norm` / 定理 `norm`

English:
theorem norm
  given: [NumberField K] (x : (𝓞 K)ˣ)
  proof: by
  rw [← RingOfIntegers.coe_norm]; rw [isUnit_iff_norm.mp x.isUnit]

中文:
定理 norm
  条件: [数域 K] (x : (𝓞 K)ˣ)
  证明: by
  rw [← RingOfIntegers.coe_norm]; rw [isUnit_iff_norm.mp x.isUnit]
-/
protected theorem norm [NumberField K] (x : (𝓞 K)ˣ) :
    |Algebra.norm Rat (x : K)| = 1 := by
  rw [← RingOfIntegers.coe_norm]; rw [isUnit_iff_norm.mp x.isUnit]

variable {K} in
/--
theorem `pos_at_place` / 定理 `pos_at_place`

English:
theorem pos_at_place
  given: (x : (𝓞 K)ˣ) (w : InfinitePlace K)
  proof: pos_iff.mpr (coe_ne_zero x)

中文:
定理 pos_at_place
  条件: (x : (𝓞 K)ˣ) (w : InfinitePlace K)
  证明: pos_iff.mpr (coe_ne_zero x)

Depends on / 依赖: coe_ne_zero, pos_iff, pos_iff.mpr
-/
theorem pos_at_place (x : (𝓞 K)ˣ) (w : InfinitePlace K) :
    0 < w x := pos_iff.mpr (coe_ne_zero x)

variable {K} in
/--
theorem `sum_mult_mul_log` / 定理 `sum_mult_mul_log`

English:
theorem sum_mult_mul_log
  given: [NumberField K] (x : (𝓞 K)ˣ)
  proof: by
  simpa [Units.norm, Real.log_prod, Real.log_pow] using
    congr_arg Real.log (prod_eq_abs_norm (x : K))

中文:
定理 sum_mult_mul_log
  条件: [数域 K] (x : (𝓞 K)ˣ)
  证明: by
  simpa [Units.norm, Real.log_prod, Real.log_pow] using
    congr_arg Real.log (prod_eq_abs_norm (x : K))

Depends on / 依赖: Real.log, Real.log_pow, Real.log_prod, Units.norm, congr_arg, log_pow, log_prod, prod_eq_abs_norm
-/
theorem sum_mult_mul_log [NumberField K] (x : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, w.mult * Real.log (w x) = 0 := by
  simpa [Units.norm, Real.log_prod, Real.log_pow] using
    congr_arg Real.log (prod_eq_abs_norm (x : K))

section torsion

/--
Definition of `torsion` / `torsion` 的定义

English:
definition torsion
  signature: : Subgroup (𝓞 K)ˣ
  body: CommGroup.torsion (𝓞 K)ˣ

中文:
定义 torsion
  签名: : 子群 (𝓞 K)ˣ
  定义体: CommGroup.torsion (𝓞 K)ˣ

Depends on / 依赖: CommGroup, CommGroup.torsion, torsion
-/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (torsion K)
  body: One.instNonempty

中文:
实例 :
  签名: 非空 (torsion K)
  定义体: One.instNonempty

Depends on / 依赖: One.instNonempty, instNonempty
-/
instance : Nonempty (torsion K) := One.instNonempty

variable [NumberField K]

/--
theorem `mem_torsion` / 定理 `mem_torsion`

English:
theorem mem_torsion
  given: {x : (𝓞 K)ˣ}
  proof: by
  rw [eq_iff_eq (x : K) 1]; rw [torsion]; rw [CommGroup.mem_torsion]
  refine ⟨fun hx φ => (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h => isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one

中文:
定理 mem_torsion
  条件: {x : (𝓞 K)ˣ}
  证明: by
  rw [eq_iff_eq (x : K) 1]; rw [torsion]; rw [CommGroup.mem_torsion]
  refine ⟨fun hx φ => (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h => isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one

Depends on / 依赖: CommGroup, CommGroup.mem_torsion, Embeddings, Embeddings.pow_eq_one_of_norm_eq_one, NumberField, NumberField.RingOfIntegers.coe_eq_algebraMap, RingOfIntegers, Units.coeHom, algebraMap, coeHom, coe_eq_algebraMap, coe_one, coe_pow, eq_iff_eq, isIntegral_coe, isOfFinOrder, isOfFinOrder_iff_pow_eq_one, mem_torsion, norm_eq_one, pow_eq_one_of_norm_eq_one
-/
theorem mem_torsion {x : (𝓞 K)ˣ} :
    x in torsion K ↔ forall w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1]; rw [torsion]; rw [CommGroup.mem_torsion]
  refine ⟨fun hx φ => (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h => isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K Complex x.val.isIntegral_coe h
  exact ⟨n, hn, by ext; rw [NumberField.RingOfIntegers.coe_eq_algebraMap, coe_pow, hx,
    NumberField.RingOfIntegers.coe_eq_algebraMap, coe_one]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (torsion K)
  body: by
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K Complex 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

中文:
实例 :
  签名: 有限 (torsion K)
  定义体: by
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K Complex 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

Depends on / 依赖: Embeddings, Embeddings.finite_of_norm_le, Finite, Set.Finite.of_finite_image, coe_injective, eq_iff_eq, finite_of_norm_le, h_tors, h_ua, le_of_eq, mem_torsion, of_finite_image, subset, u.val.prop
-/
instance : Finite (torsion K) := by
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K Complex 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCyclic (torsion K)
  body: isCyclic_subgroup_units _

中文:
实例 :
  签名: 是循环 (torsion K)
  定义体: isCyclic_subgroup_units _

Depends on / 依赖: isCyclic_subgroup_units
-/
instance : IsCyclic (torsion K) := isCyclic_subgroup_units _

/--
Definition of `torsionOrder` / `torsionOrder` 的定义

English:
definition torsionOrder
  signature: : Nat
  body: Nat.card (torsion K)

中文:
定义 torsionOrder
  签名: : 自然数
  定义体: Nat.card (torsion K)

Depends on / 依赖: Nat.card, torsion
-/
def torsionOrder : Nat := Nat.card (torsion K)

/--
theorem `torsionOrder_pos` / 定理 `torsionOrder_pos`

English:
theorem torsionOrder_pos
  statement: 0 < torsionOrder K
  proof: Nat.card_pos

中文:
定理 torsionOrder_pos
  结论: 0 < torsionOrder K
  证明: Nat.card_pos

Depends on / 依赖: Nat.card_pos, card_pos
-/
theorem torsionOrder_pos : 0 < torsionOrder K :=
  Nat.card_pos

/--
theorem `torsionOrder_ne_zero` / 定理 `torsionOrder_ne_zero`

English:
theorem torsionOrder_ne_zero
  statement: torsionOrder K != 0
  proof: (torsionOrder_pos K).ne'

中文:
定理 torsionOrder_ne_zero
  结论: torsionOrder K != 0
  证明: (torsionOrder_pos K).ne'

Depends on / 依赖: torsionOrder_pos
-/
theorem torsionOrder_ne_zero : torsionOrder K != 0 :=
  (torsionOrder_pos K).ne'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NeZero (torsionOrder K)
  body: ⟨torsionOrder_ne_zero K⟩

omit [NumberField K] in

中文:
实例 :
  签名: NeZero (torsionOrder K)
  定义体: ⟨torsionOrder_ne_zero K⟩

omit [NumberField K] in

Depends on / 依赖: torsionOrder_ne_zero
-/
instance : NeZero (torsionOrder K) :=
  ⟨torsionOrder_ne_zero K⟩

omit [NumberField K] in
/--
theorem `rootsOfUnity_eq_one` / 定理 `rootsOfUnity_eq_one`

English:
theorem rootsOfUnity_eq_one
  statement: {k : Nat+} (hc : Nat.Coprime k (torsionOrder K))
  proof: by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ in torsion K := by
      rw [torsion]; rw [CommGroup.mem_torsion]; rw [isOfFinOrder_iff_pow_eq_one

中文:
定理 rootsOfUnity_eq_one
  结论: {k : 自然数+} (hc : 自然数.Coprime k (torsionOrder K))
  证明: by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ in torsion K := by
      rw [torsion]; rw [CommGroup.mem_torsion]; rw [isOfFinOrder_iff_pow_eq_one

Depends on / 依赖: CommGroup, CommGroup.mem_torsion, Nat.eq_one_of_dvd_coprimes, eq_one_of_dvd_coprimes, isOfFinOrder_iff_pow_eq_one, k.prop, mem_rootsOfUnity, mem_torsion, one_pow, orderOf_dvd_natCard, orderOf_dvd_of_pow_eq_one, orderOf_eq_one_iff, orderOf_eq_one_iff.mp, orderOf_submonoid, torsion
-/
theorem rootsOfUnity_eq_one {k : Nat+} (hc : Nat.Coprime k (torsionOrder K))
    {ζ : (𝓞 K)ˣ} : ζ in rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ in torsion K := by
      rw [torsion]; rw [CommGroup.mem_torsion]; rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ]; rw [hζ⟩ : torsion K)]
    apply orderOf_dvd_natCard

/--
theorem `rootsOfUnity_eq_torsion` / 定理 `rootsOfUnity_eq_torsion`

English:
theorem rootsOfUnity_eq_torsion
  proof: by
  ext ζ
  rw [torsion]; rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨torsionOrder K, torsionOrder_pos K, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one' (torsion K) _ ⟨ζ, h⟩)

中文:
定理 rootsOfUnity_eq_torsion
  证明: by
  ext ζ
  rw [torsion]; rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨torsionOrder K, torsionOrder_pos K, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one' (torsion K) _ ⟨ζ, h⟩)

Depends on / 依赖: CommGroup, CommGroup.mem_torsion, Subtype, Subtype.ext_iff.mp, ext_iff, isOfFinOrder_iff_pow_eq_one, mem_rootsOfUnity, mem_torsion, pow_card_eq_one, torsion, torsionOrder, torsionOrder_pos
-/
theorem rootsOfUnity_eq_torsion :
    rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion]; rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨torsionOrder K, torsionOrder_pos K, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one' (torsion K) _ ⟨ζ, h⟩)

/--
theorem `map_complexEmbedding_torsion` / 定理 `map_complexEmbedding_torsion`

English:
theorem map_complexEmbedding_torsion
  given: (φ : K ->+* Complex)
  proof: by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← rootsOfUnity_eq_torsion]
    exact map_rootsOfUnity _ (torsionOrder K)
  · let e := ((torsion K).equivMapOfInjective (Units.complexEmbedding φ)
      (Units.complexEmbedding_injective φ)).symm.toEquiv
    rw [Complex.card_rootsOfUnity]; rw [Nat.card_

中文:
定理 map_complexEmbedding_torsion
  条件: (φ : K ->+* 复形)
  证明: by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← rootsOfUnity_eq_torsion]
    exact map_rootsOfUnity _ (torsionOrder K)
  · let e := ((torsion K).equivMapOfInjective (Units.complexEmbedding φ)
      (Units.complexEmbedding_injective φ)).symm.toEquiv
    rw [Complex.card_rootsOfUnity]; rw [Nat.card_

Depends on / 依赖: Complex.card_rootsOfUnity, Nat.card_congr, Subgroup, Subgroup.eq_of_le_of_card_ge, Units.complexEmbedding, Units.complexEmbedding_injective, card_congr, card_rootsOfUnity, complexEmbedding, complexEmbedding_injective, eq_of_le_of_card_ge, equivMapOfInjective, map_rootsOfUnity, rootsOfUnity_eq_torsion, symm.toEquiv, toEquiv, torsion, torsionOrder
-/
theorem map_complexEmbedding_torsion (φ : K ->+* Complex) :
    (torsion K).map (Units.complexEmbedding φ) = rootsOfUnity (torsionOrder K) Complex := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← rootsOfUnity_eq_torsion]
    exact map_rootsOfUnity _ (torsionOrder K)
  · let e := ((torsion K).equivMapOfInjective (Units.complexEmbedding φ)
      (Units.complexEmbedding_injective φ)).symm.toEquiv
    rw [Complex.card_rootsOfUnity]; rw [Nat.card_congr e]; rw [torsionOrder]

/--
theorem `even_torsionOrder` / 定理 `even_torsionOrder`

English:
theorem even_torsionOrder
  proof: by
  suffices orderOf (⟨-1, neg_one_mem_torsion⟩ : torsion K) = 2 by
    rw [even_iff_two_dvd]; rw [← this]
    apply orderOf_dvd_natCard
  rw [← Subgroup.orderOf_coe]; rw [← orderOf_units]; rw [Units.val_neg]; rw [val_one]; rw [orderOf_neg_one]; rw [ringChar.eq_zero]; rw [if_neg (by decide)]

中文:
定理 even_torsionOrder
  证明: by
  suffices orderOf (⟨-1, neg_one_mem_torsion⟩ : torsion K) = 2 by
    rw [even_iff_two_dvd]; rw [← this]
    apply orderOf_dvd_natCard
  rw [← Subgroup.orderOf_coe]; rw [← orderOf_units]; rw [Units.val_neg]; rw [val_one]; rw [orderOf_neg_one]; rw [ringChar.eq_zero]; rw [if_neg (by decide)]

Depends on / 依赖: Subgroup, Subgroup.orderOf_coe, Units.val_neg, eq_zero, even_iff_two_dvd, if_neg, neg_one_mem_torsion, orderOf, orderOf_coe, orderOf_dvd_natCard, orderOf_neg_one, orderOf_units, ringChar, ringChar.eq_zero, torsion, val_neg, val_one
-/
theorem even_torsionOrder :
    Even (torsionOrder K) := by
  suffices orderOf (⟨-1, neg_one_mem_torsion⟩ : torsion K) = 2 by
    rw [even_iff_two_dvd]; rw [← this]
    apply orderOf_dvd_natCard
  rw [← Subgroup.orderOf_coe]; rw [← orderOf_units]; rw [Units.val_neg]; rw [val_one]; rw [orderOf_neg_one]; rw [ringChar.eq_zero]; rw [if_neg (by decide)]

section odd

variable {K}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `torsion_eq_one_or_neg_one_of_odd_finrank` / 定理 `torsion_eq_one_or_neg_one_of_odd_finrank`

English:
theorem torsion_eq_one_or_neg_one_of_odd_finrank
  proof: by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K)),
        NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank h]
  · interval_cases hi : orderOf (

中文:
定理 torsion_eq_one_or_neg_one_of_odd_finrank
  证明: by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K)),
        NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank h]
  · interval_cases hi : orderOf (

Depends on / 依赖: CharP.orderOf_eq_two_iff, CommGroup, CommGroup.mem_torsion, InfinitePlace, IsPrimitiveRoot, IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt, IsPrimitiveRoot.orderOf, NumberField, NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank, Or.intro_left, Units.val_in, interval_cases, intro_left, mem_torsion, nrRealPlaces_eq_zero_of_two_lt, nrRealPlaces_pos_of_odd_finrank, orderOf, orderOf_eq_one_iff, orderOf_eq_two_iff, orderOf_pos_iff
-/
theorem torsion_eq_one_or_neg_one_of_odd_finrank
    (h : Odd (Module.finrank Rat K)) (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K)),
        NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank h]
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

/--
theorem `torsionOrder_eq_two_of_odd_finrank` / 定理 `torsionOrder_eq_two_of_odd_finrank`

English:
theorem torsionOrder_eq_two_of_odd_finrank
  given: (h : Odd (Module.finrank Rat K))
  proof: by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder]; rw [Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x => ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert]; rw [Fins

中文:
定理 torsionOrder_eq_two_of_odd_finrank
  条件: (h : Odd (模.finrank 有理数 K))
  证明: by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder]; rw [Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x => ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert]; rw [Fins

Depends on / 依赖: Finset, Finset.card_eq_two, Finset.ext, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Subtype, Subtype.coe_ne_coe, Subtype.val_inj, card_eq_fintype_card, card_eq_two, classical, coe_ne_coe, mem_insert, mem_singleton, mem_univ, neg_one_mem_torsion
-/
theorem torsionOrder_eq_two_of_odd_finrank (h : Odd (Module.finrank Rat K)) :
    torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder]; rw [Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x => ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert]; rw [Finset.mem_singleton]; rw [← Subtype.val_inj]; rw [← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one_of_odd_finrank h x

end odd

end torsion

end Units

end NumberField
