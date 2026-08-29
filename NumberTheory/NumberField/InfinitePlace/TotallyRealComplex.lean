/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Xavier Roblot
-/
module

public import Mathlib.FieldTheory.PrimeField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Totally real and totally complex number fields

This file defines the type of totally real and totally complex number fields.

## Main Definitions and Results

* `NumberField.IsTotallyReal`: a field `K` is totally real if all of its infinite places
  are real. In other words, the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
* `NumberField.IsTotallyComplex`: a field `K` is totally complex if all of its infinite
  places are complex.
* `NumberField.maximalRealSubfield`: the maximal real subfield of `K`. It is totally real,
  see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
  subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`

## Tags

number field, infinite places, totally real, totally complex
-/

@[expose] public section

namespace NumberField

open InfinitePlace Module

section TotallyRealField

/-

## Totally real number fields

-/

/--
Definition of `IsTotallyReal` / `IsTotallyReal` 的定义

English:
class IsTotallyReal
  parameters: (K : Type*) [Field K]
  axioms and operations (1):
    - isReal : forall v : InfinitePlace K, v.IsReal

中文:
类 是Totally实数
  参数: (K : 类型) [域 K]
  公理与运算 (1 个):
    - isReal : 对任意 v : InfinitePlace K, v.Is实数
-/
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] where
  isReal : forall v : InfinitePlace K, v.IsReal

variable {F : Type*} [Field F] {K : Type*} [Field K]

/--
theorem `nrComplexPlaces_eq_zero_iff` / 定理 `nrComplexPlaces_eq_zero_iff`

English:
theorem nrComplexPlaces_eq_zero_iff
  given: [NumberField K]
  proof: by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

中文:
定理 nrComplexPlaces_eq_zero_iff
  条件: [数域 K]
  证明: by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff, card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff
-/
theorem nrComplexPlaces_eq_zero_iff [NumberField K] :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]

/--
theorem `IsTotallyReal.complexEmbedding_isReal` / 定理 `IsTotallyReal.complexEmbedding_isReal`

English:
theorem IsTotallyReal.complexEmbedding_isReal
  given: [IsTotallyReal K] (φ : K ->+* Complex)
  proof: isReal_mk_iff.mp isReal (InfinitePlace.mk φ)

@[simp]

中文:
定理 是Totally实数.complexEmbedding_is实数
  条件: [是Totally实数 K] (φ : K ->+* 复形)
  证明: isReal_mk_iff.mp isReal (InfinitePlace.mk φ)

@[simp]

Depends on / 依赖: InfinitePlace, InfinitePlace.mk, isReal, isReal_mk_iff, isReal_mk_iff.mp
-/
theorem IsTotallyReal.complexEmbedding_isReal [IsTotallyReal K] (φ : K ->+* Complex) :
    ComplexEmbedding.IsReal φ :=
isReal_mk_iff.mp isReal (InfinitePlace.mk φ)

@[simp]
/--
theorem `IsTotallyReal.mult_eq` / 定理 `IsTotallyReal.mult_eq`

English:
theorem IsTotallyReal.mult_eq
  given: [IsTotallyReal K] (w : InfinitePlace K)
  statement: mult w = 1
  proof: mult_isReal ⟨w, isReal w⟩

中文:
定理 是Totally实数.mult_eq
  条件: [是Totally实数 K] (w : InfinitePlace K)
  结论: mult w = 1
  证明: mult_isReal ⟨w, isReal w⟩

Depends on / 依赖: isReal, mult_isReal
-/
theorem IsTotallyReal.mult_eq [IsTotallyReal K] (w : InfinitePlace K) : mult w = 1 :=
  mult_isReal ⟨w, isReal w⟩

/--
theorem `IsTotallyReal.ofRingEquiv` / 定理 `IsTotallyReal.ofRingEquiv`

English:
theorem IsTotallyReal.ofRingEquiv
  given: [IsTotallyReal F] (f : F ≃+* K)
  statement: IsTotallyReal K where
  proof: (isReal_comap_iff f).mp IsTotallyReal.isReal _

中文:
定理 是Totally实数.ofRingEquiv
  条件: [是Totally实数 F] (f : F ≃+* K)
  结论: 是Totally实数 K where
  证明: (isReal_comap_iff f).mp IsTotallyReal.isReal _

Depends on / 依赖: IsTotallyReal, IsTotallyReal.isReal, isReal, isReal_comap_iff
-/
theorem IsTotallyReal.ofRingEquiv [IsTotallyReal F] (f : F ≃+* K) : IsTotallyReal K where
isReal _ := (isReal_comap_iff f).mp IsTotallyReal.isReal _

variable (F K) in
/--
theorem `IsTotallyReal.of_algebra` / 定理 `IsTotallyReal.of_algebra`

English:
theorem IsTotallyReal.of_algebra
  given: [IsTotallyReal K] [Algebra F K] [Algebra.IsAlgebraic F K]
  proof: by
    obtain ⟨W, rfl⟩ : exists W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)

中文:
定理 是Totally实数.of_algebra
  条件: [是Totally实数 K] [代数 F K] [代数.是代数 F K]
  证明: by
    obtain ⟨W, rfl⟩ : exists W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)

Depends on / 依赖: InfinitePlace, IsReal, IsReal.comap, IsTotallyReal, IsTotallyReal.isReal, W.comap, algebraMap, comap_surjective, isReal
-/
theorem IsTotallyReal.of_algebra [IsTotallyReal K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    IsTotallyReal F where
  isReal w := by
    obtain ⟨W, rfl⟩ : exists W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)

/--
theorem `isTotallyReal_iff_ofRingEquiv` / 定理 `isTotallyReal_iff_ofRingEquiv`

English:
theorem isTotallyReal_iff_ofRingEquiv
  given: (f : F ≃+* K)
  statement: IsTotallyReal F ↔ IsTotallyReal K
  proof: ⟨fun _ => .ofRingEquiv f, fun _ => .ofRingEquiv f.symm⟩

@[simp]

中文:
定理 isTotally实数_iff_ofRingEquiv
  条件: (f : F ≃+* K)
  结论: 是Totally实数 F ↔ 是Totally实数 K
  证明: ⟨fun _ => .ofRingEquiv f, fun _ => .ofRingEquiv f.symm⟩

@[simp]

Depends on / 依赖: f.symm, ofRingEquiv
-/
theorem isTotallyReal_iff_ofRingEquiv (f : F ≃+* K) : IsTotallyReal F ↔ IsTotallyReal K :=
  ⟨fun _ => .ofRingEquiv f, fun _ => .ofRingEquiv f.symm⟩

@[simp]
/--
theorem `isTotallyReal_top_iff` / 定理 `isTotallyReal_top_iff`

English:
theorem isTotallyReal_top_iff
  statement: IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K
  proof: isTotallyReal_iff_ofRingEquiv Subfield.topEquiv

中文:
定理 isTotally实数_top_iff
  结论: 是Totally实数 (⊤ : 子域 K) ↔ 是Totally实数 K
  证明: isTotallyReal_iff_ofRingEquiv Subfield.topEquiv

Depends on / 依赖: Subfield, Subfield.topEquiv, isTotallyReal_iff_ofRingEquiv, topEquiv
-/
theorem isTotallyReal_top_iff : IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K :=
  isTotallyReal_iff_ofRingEquiv Subfield.topEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTotallyReal
  signature: K] [CharZero K] (F
  body: IsTotallyReal.of_algebra F K

中文:
实例 [是Totally实数
  签名: K] [特征零 K] (F
  定义体: IsTotallyReal.of_algebra F K

Depends on / 依赖: IsTotallyReal, IsTotallyReal.of_algebra, of_algebra
-/
instance [IsTotallyReal K] [CharZero K] (F : IntermediateField Rat K) [Algebra.IsAlgebraic F K] :
    IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTotallyReal
  signature: K] (F
  body: IsTotallyReal.of_algebra F K

中文:
实例 [是Totally实数
  签名: K] (F
  定义体: IsTotallyReal.of_algebra F K

Depends on / 依赖: IsTotallyReal, IsTotallyReal.of_algebra, of_algebra
-/
instance [IsTotallyReal K] (F : Subfield K) [Algebra.IsAlgebraic F K] : IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

variable (K)

@[simp]
/--
theorem `IsTotallyReal.nrComplexPlaces_eq_zero` / 定理 `IsTotallyReal.nrComplexPlaces_eq_zero`

English:
theorem IsTotallyReal.nrComplexPlaces_eq_zero
  given: [NumberField K] [h : IsTotallyReal K]
  proof: nrComplexPlaces_eq_zero_iff.mpr h

中文:
定理 是Totally实数.nrComplexPlaces_eq_zero
  条件: [数域 K] [h : 是Totally实数 K]
  证明: nrComplexPlaces_eq_zero_iff.mpr h

Depends on / 依赖: nrComplexPlaces_eq_zero_iff, nrComplexPlaces_eq_zero_iff.mpr
-/
theorem IsTotallyReal.nrComplexPlaces_eq_zero [NumberField K] [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h

/--
theorem `IsTotallyReal.finrank` / 定理 `IsTotallyReal.finrank`

English:
theorem IsTotallyReal.finrank
  given: [NumberField K] [h : IsTotallyReal K]
  proof: by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrComplexPlaces_eq_zero_iff.mpr h]; rw [mul_zero]; rw [add_zero]

中文:
定理 是Totally实数.finrank
  条件: [数域 K] [h : 是Totally实数 K]
  证明: by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrComplexPlaces_eq_zero_iff.mpr h]; rw [mul_zero]; rw [add_zero]
-/
protected theorem IsTotallyReal.finrank [NumberField K] [h : IsTotallyReal K] :
    finrank Rat K = nrRealPlaces K := by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrComplexPlaces_eq_zero_iff.mpr h]; rw [mul_zero]; rw [add_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTotallyReal Rat
  body: by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

中文:
实例 :
  签名: 是Totally实数 有理数
  定义体: by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

Depends on / 依赖: Rat.infinitePlace, Rat.isReal_infinitePlace, Subsingleton, Subsingleton.elim, infinitePlace, isReal_infinitePlace
-/
instance : IsTotallyReal Rat where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTotallyReal
  signature: K] :
  body: isTotallyReal_top_iff.mpr ‹_›

中文:
实例 [是Totally实数
  签名: K] :
  定义体: isTotallyReal_top_iff.mpr ‹_›

Depends on / 依赖: isTotallyReal_top_iff, isTotallyReal_top_iff.mpr
-/
instance [IsTotallyReal K] :
    IsTotallyReal (⊤ : Subfield K) := isTotallyReal_top_iff.mpr ‹_›

/--
Instance `_root_.IntermediateField.isTotallyReal_bot` / 实例 `_root_.IntermediateField.isTotallyReal_bot`

English:
instance _root_.IntermediateField.isTotallyReal_bot
  signature: [CharZero K]
  body: IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv Rat K).symm.toRingEquiv

中文:
实例 _root_.中间域.isTotally实数_bot
  签名: [特征零 K]
  定义体: IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv Rat K).symm.toRingEquiv

Depends on / 依赖: IntermediateField, IntermediateField.botEquiv, IsTotallyReal, IsTotallyReal.ofRingEquiv, botEquiv, ofRingEquiv, symm.toRingEquiv, toRingEquiv
-/
instance _root_.IntermediateField.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : IntermediateField Rat K) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv Rat K).symm.toRingEquiv

/--
Instance `_root_.Subfield.isTotallyReal_bot` / 实例 `_root_.Subfield.isTotallyReal_bot`

English:
instance _root_.Subfield.isTotallyReal_bot
  signature: [CharZero K]
  body: by
  rw [Subfield.bot_eq_of_charZero]
  exact IsTotallyReal.ofRingEquiv (algebraMap Rat K).rangeRestrictFieldEquiv

中文:
实例 _root_.子域.isTotally实数_bot
  签名: [特征零 K]
  定义体: by
  rw [Subfield.bot_eq_of_charZero]
  exact IsTotallyReal.ofRingEquiv (algebraMap Rat K).rangeRestrictFieldEquiv

Depends on / 依赖: IsTotallyReal, IsTotallyReal.ofRingEquiv, Subfield, Subfield.bot_eq_of_charZero, algebraMap, bot_eq_of_charZero, ofRingEquiv, rangeRestrictFieldEquiv
-/
instance _root_.Subfield.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : Subfield K) := by
  rw [Subfield.bot_eq_of_charZero]
  exact IsTotallyReal.ofRingEquiv (algebraMap Rat K).rangeRestrictFieldEquiv

section maximalRealSubfield

open ComplexEmbedding

/--
Definition of `maximalRealSubfield` / `maximalRealSubfield` 的定义

English:
definition maximalRealSubfield
  signature: : Subfield K where
  body: {x | forall φ : K ->+* Complex, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

中文:
定义 maximal实数Subfield
  签名: : 子域 K where
  定义体: {x | forall φ : K ->+* Complex, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp
-/
def maximalRealSubfield : Subfield K where
  carrier := {x | forall φ : K ->+* Complex, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

variable {K}

/--
theorem `mem_maximalRealSubfield_iff` / 定理 `mem_maximalRealSubfield_iff`

English:
theorem mem_maximalRealSubfield_iff
  given: (x : K)
  proof: .rfl

中文:
定理 mem_maximal实数Subfield_iff
  条件: (x : K)
  证明: .rfl
-/
theorem mem_maximalRealSubfield_iff (x : K) :
    x in maximalRealSubfield K ↔ forall φ : K ->+* Complex, star (φ x) = φ x := .rfl

/--
theorem `IsTotallyReal.le_maximalRealSubfield` / 定理 `IsTotallyReal.le_maximalRealSubfield`

English:
theorem IsTotallyReal.le_maximalRealSubfield
  given: (E : Subfield K) [IsTotallyReal E]
  proof: by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x]; rw [hx⟩ by simp]; rw [RCLike.star_def]; rw [← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
exact ComplexEmbedding.isReal_iff.mp isReal_mk_iff.mp isReal _

@[simp]

中文:
定理 是Totally实数.le_maximal实数Subfield
  条件: (E : 子域 K) [是Totally实数 E]
  证明: by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x]; rw [hx⟩ by simp]; rw [RCLike.star_def]; rw [← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
exact ComplexEmbedding.isReal_iff.mp isReal_mk_iff.mp isReal _

@[simp]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff.mp, E.subtype, RCLike, RCLike.star_def, RingHom, RingHom.congr_fun, congr_fun, conjugate_coe_eq, isReal, isReal_iff, isReal_mk_iff, isReal_mk_iff.mp, star_def, subtype
-/
theorem IsTotallyReal.le_maximalRealSubfield (E : Subfield K) [IsTotallyReal E] :
    E <= maximalRealSubfield K := by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x]; rw [hx⟩ by simp]; rw [RCLike.star_def]; rw [← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
exact ComplexEmbedding.isReal_iff.mp isReal_mk_iff.mp isReal _

@[simp]
/--
theorem `IsTotallyReal.maximalRealSubfield_eq_top` / 定理 `IsTotallyReal.maximalRealSubfield_eq_top`

English:
theorem IsTotallyReal.maximalRealSubfield_eq_top
  given: [IsTotallyReal K]
  proof: top_unique NumberField.IsTotallyReal.le_maximalRealSubfield _

中文:
定理 是Totally实数.maximal实数Subfield_eq_top
  条件: [是Totally实数 K]
  证明: top_unique NumberField.IsTotallyReal.le_maximalRealSubfield _

Depends on / 依赖: IsTotallyReal, NumberField, NumberField.IsTotallyReal.le_maximalRealSubfield, le_maximalRealSubfield, top_unique
-/
theorem IsTotallyReal.maximalRealSubfield_eq_top [IsTotallyReal K] :
    maximalRealSubfield K = ⊤ :=
top_unique NumberField.IsTotallyReal.le_maximalRealSubfield _

variable [CharZero K] [Algebra.IsAlgebraic Rat K]

local instance (k : Subfield K) : Algebra.IsAlgebraic k K :=
  Algebra.IsAlgebraic.tower_top k (K := Rat) (A := K)

/--
Instance `isTotallyReal_maximalRealSubfield` / 实例 `isTotallyReal_maximalRealSubfield`

English:
instance isTotallyReal_maximalRealSubfield
  signature: :
  body: by
    rw [InfinitePlace.isReal_iff]; rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply]; rw [← lift_algebraMap_apply K w.embedding]
    exact x.prop _

中文:
实例 isTotally实数_maximal实数Subfield
  签名: :
  定义体: by
    rw [InfinitePlace.isReal_iff]; rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply]; rw [← lift_algebraMap_apply K w.embedding]
    exact x.prop _

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff, InfinitePlace, InfinitePlace.isReal_iff, RingHom, RingHom.star_apply, embedding, isReal_iff, lift_algebraMap_apply, star_apply, w.embedding, x.prop
-/
instance isTotallyReal_maximalRealSubfield :
    IsTotallyReal (maximalRealSubfield K) where
  isReal w := by
    rw [InfinitePlace.isReal_iff]; rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply]; rw [← lift_algebraMap_apply K w.embedding]
    exact x.prop _

/--
theorem `isTotallyReal_iff_le_maximalRealSubfield` / 定理 `isTotallyReal_iff_le_maximalRealSubfield`

English:
theorem isTotallyReal_iff_le_maximalRealSubfield
  given: {E : Subfield K}
  proof: by
  refine ⟨fun h => h.le_maximalRealSubfield, fun h => ?_⟩
let _ : Algebra E (maximalRealSubfield K) := RingHom.toAlgebra Subfield.inclusion h
  have : IsScalarTower E (maximalRealSubfield K) K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic E (maximalRealSubfield K) :=
      Algebra.IsAlgebraic.tower_bot E (maximalRealSubfield K) K
  exact IsTotallyReal.of_algebra _ (maximalRealSubfield K)

中文:
定理 isTotally实数_iff_le_maximal实数Subfield
  条件: {E : 子域 K}
  证明: by
  refine ⟨fun h => h.le_maximalRealSubfield, fun h => ?_⟩
let _ : Algebra E (maximalRealSubfield K) := RingHom.toAlgebra Subfield.inclusion h
  have : IsScalarTower E (maximalRealSubfield K) K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic E (maximalRealSubfield K) :=
      Algebra.IsAlgebraic.tower_bot E (maximalRealSubfield K) K
  exact IsTotallyReal.of_algebra _ (maximalRealSubfield K)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.tower_bot, IsAlgebraic, IsScalarTower, IsScalarTower.of_algebraMap_eq, IsTotallyReal, IsTotallyReal.of_algebra, RingHom, RingHom.toAlgebra, Subfield, Subfield.inclusion, h.le_maximalRealSubfield, inclusion, le_maximalRealSubfield, maximalRealSubfield, of_algebra, of_algebraMap_eq, toAlgebra, tower_bot
-/
theorem isTotallyReal_iff_le_maximalRealSubfield {E : Subfield K} :
    IsTotallyReal E ↔ E <= maximalRealSubfield K := by
  refine ⟨fun h => h.le_maximalRealSubfield, fun h => ?_⟩
let _ : Algebra E (maximalRealSubfield K) := RingHom.toAlgebra Subfield.inclusion h
  have : IsScalarTower E (maximalRealSubfield K) K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic E (maximalRealSubfield K) :=
      Algebra.IsAlgebraic.tower_bot E (maximalRealSubfield K) K
  exact IsTotallyReal.of_algebra _ (maximalRealSubfield K)

/--
Instance `isTotallyReal_sup` / 实例 `isTotallyReal_sup`

English:
instance isTotallyReal_sup
  signature: {E F : Subfield K} [hE : IsTotallyReal E] [hF : IsTotallyReal F]
  body: by
  rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [sup_le_iff]; rw [← isTotallyReal_iff_le_maximalRealSubfield]; rw [← isTotallyReal_iff_le_maximalRealSubfield]
  exact ⟨hE, hF⟩

中文:
实例 isTotally实数_sup
  签名: {E F : 子域 K} [hE : 是Totally实数 E] [hF : 是Totally实数 F]
  定义体: by
  rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [sup_le_iff]; rw [← isTotallyReal_iff_le_maximalRealSubfield]; rw [← isTotallyReal_iff_le_maximalRealSubfield]
  exact ⟨hE, hF⟩

Depends on / 依赖: isTotallyReal_iff_le_maximalRealSubfield, sup_le_iff
-/
instance isTotallyReal_sup {E F : Subfield K} [hE : IsTotallyReal E] [hF : IsTotallyReal F] :
    IsTotallyReal (E ⊔ F : Subfield K) := by
  rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [sup_le_iff]; rw [← isTotallyReal_iff_le_maximalRealSubfield]; rw [← isTotallyReal_iff_le_maximalRealSubfield]
  exact ⟨hE, hF⟩

/--
Instance `isTotallyReal_iSup` / 实例 `isTotallyReal_iSup`

English:
instance isTotallyReal_iSup
  signature: {ι : Type*} {k : ι -> Subfield K} [forall i, IsTotallyReal (k i)]
  body: by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  · rw [isTotallyReal_iff_le_maximalRealSubfield, iSup_le_iff]
    exact fun i => IsTotallyReal.le_maximalRealSubfield (k i)

中文:
实例 isTotally实数_iSup
  签名: {ι : 类型} {k : ι -> 子域 K} [对任意 i, 是Totally实数 (k i)]
  定义体: by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  · rw [isTotallyReal_iff_le_maximalRealSubfield, iSup_le_iff]
    exact fun i => IsTotallyReal.le_maximalRealSubfield (k i)

Depends on / 依赖: IsTotallyReal, IsTotallyReal.le_maximalRealSubfield, iSup_le_iff, iSup_of_empty, infer_instance, isEmpty_or_nonempty, isTotallyReal_iff_le_maximalRealSubfield, le_maximalRealSubfield
-/
instance isTotallyReal_iSup {ι : Type*} {k : ι -> Subfield K} [forall i, IsTotallyReal (k i)] :
    IsTotallyReal (⨆ i, k i : Subfield K) := by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  · rw [isTotallyReal_iff_le_maximalRealSubfield, iSup_le_iff]
    exact fun i => IsTotallyReal.le_maximalRealSubfield (k i)

/--
theorem `maximalRealSubfield_eq_top_iff_isTotallyReal` / 定理 `maximalRealSubfield_eq_top_iff_isTotallyReal`

English:
theorem maximalRealSubfield_eq_top_iff_isTotallyReal
  proof: by
    have : Algebra.IsIntegral (⊤ : Subfield K) K := Algebra.IsIntegral.tower_top Rat
    rw [← isTotallyReal_top_iff]; rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [h]
  mpr _ := IsTotallyReal.maximalRealSubfield_eq_top

中文:
定理 maximal实数Subfield_eq_top_iff_isTotally实数
  证明: by
    have : Algebra.IsIntegral (⊤ : Subfield K) K := Algebra.IsIntegral.tower_top Rat
    rw [← isTotallyReal_top_iff]; rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [h]
  mpr _ := IsTotallyReal.maximalRealSubfield_eq_top

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.IsIntegral.tower_top, IsIntegral, IsTotallyReal, IsTotallyReal.maximalRealSubfield_eq_top, Subfield, isTotallyReal_iff_le_maximalRealSubfield, isTotallyReal_top_iff, maximalRealSubfield_eq_top, tower_top
-/
theorem maximalRealSubfield_eq_top_iff_isTotallyReal :
    maximalRealSubfield K = ⊤ ↔ IsTotallyReal K where
  mp h := by
    have : Algebra.IsIntegral (⊤ : Subfield K) K := Algebra.IsIntegral.tower_top Rat
    rw [← isTotallyReal_top_iff]; rw [isTotallyReal_iff_le_maximalRealSubfield]; rw [h]
  mpr _ := IsTotallyReal.maximalRealSubfield_eq_top

end maximalRealSubfield

end TotallyRealField

section TotallyComplexField

/-
## Totally complex number fields
-/

open InfinitePlace

/--
Definition of `IsTotallyComplex` / `IsTotallyComplex` 的定义

English:
class IsTotallyComplex
  parameters: (K : Type*) [Field K]
  axioms and operations (1):
    - isComplex : forall v : InfinitePlace K, v.IsComplex

中文:
类 是TotallyComplex
  参数: (K : 类型) [域 K]
  公理与运算 (1 个):
    - isComplex : 对任意 v : InfinitePlace K, v.是复形
-/
@[mk_iff] class IsTotallyComplex (K : Type*) [Field K] where
  isComplex : forall v : InfinitePlace K, v.IsComplex

variable (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]

/--
theorem `nrRealPlaces_eq_zero_iff` / 定理 `nrRealPlaces_eq_zero_iff`

English:
theorem nrRealPlaces_eq_zero_iff
  given: [NumberField K]
  proof: by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

中文:
定理 nr实数Places_eq_zero_iff
  条件: [数域 K]
  证明: by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff, card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff
-/
theorem nrRealPlaces_eq_zero_iff [NumberField K] :
    nrRealPlaces K = 0 ↔ IsTotallyComplex K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]

/--
theorem `IsTotallyComplex.complexEmbedding_not_isReal` / 定理 `IsTotallyComplex.complexEmbedding_not_isReal`

English:
theorem IsTotallyComplex.complexEmbedding_not_isReal
  given: [IsTotallyComplex K] (φ : K ->+* Complex)
  proof: isReal_mk_iff.not.mp not_isReal_iff_isComplex.mpr isComplex (InfinitePlace.mk φ)

@[simp]

中文:
定理 是TotallyComplex.complexEmbedding_not_is实数
  条件: [是TotallyComplex K] (φ : K ->+* 复形)
  证明: isReal_mk_iff.not.mp not_isReal_iff_isComplex.mpr isComplex (InfinitePlace.mk φ)

@[simp]

Depends on / 依赖: InfinitePlace, InfinitePlace.mk, isComplex, isReal_mk_iff, isReal_mk_iff.not.mp, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr
-/
theorem IsTotallyComplex.complexEmbedding_not_isReal [IsTotallyComplex K] (φ : K ->+* Complex) :
    ¬ ComplexEmbedding.IsReal φ :=
isReal_mk_iff.not.mp not_isReal_iff_isComplex.mpr isComplex (InfinitePlace.mk φ)

@[simp]
/--
theorem `IsTotallyComplex.mult_eq` / 定理 `IsTotallyComplex.mult_eq`

English:
theorem IsTotallyComplex.mult_eq
  given: [IsTotallyComplex K] (w : InfinitePlace K)
  statement: mult w = 2
  proof: mult_isComplex ⟨w, isComplex w⟩

中文:
定理 是TotallyComplex.mult_eq
  条件: [是TotallyComplex K] (w : InfinitePlace K)
  结论: mult w = 2
  证明: mult_isComplex ⟨w, isComplex w⟩

Depends on / 依赖: isComplex, mult_isComplex
-/
theorem IsTotallyComplex.mult_eq [IsTotallyComplex K] (w : InfinitePlace K) : mult w = 2 :=
  mult_isComplex ⟨w, isComplex w⟩

variable (K)

/--
theorem `isTotallyComplex_of_algebra` / 定理 `isTotallyComplex_of_algebra`

English:
theorem isTotallyComplex_of_algebra
  given: [IsTotallyComplex F]
  proof: IsComplex.of_comap (algebraMap F K) IsTotallyComplex.isComplex _

@[simp]

中文:
定理 isTotallyComplex_of_algebra
  条件: [是TotallyComplex F]
  证明: IsComplex.of_comap (algebraMap F K) IsTotallyComplex.isComplex _

@[simp]

Depends on / 依赖: IsComplex, IsComplex.of_comap, IsTotallyComplex, IsTotallyComplex.isComplex, algebraMap, isComplex, of_comap
-/
theorem isTotallyComplex_of_algebra [IsTotallyComplex F] :
    IsTotallyComplex K where
isComplex _ := IsComplex.of_comap (algebraMap F K) IsTotallyComplex.isComplex _

@[simp]
/--
theorem `IsTotallyComplex.nrRealPlaces_eq_zero` / 定理 `IsTotallyComplex.nrRealPlaces_eq_zero`

English:
theorem IsTotallyComplex.nrRealPlaces_eq_zero
  given: [NumberField K] [h : IsTotallyComplex K]
  proof: nrRealPlaces_eq_zero_iff.mpr h

中文:
定理 是TotallyComplex.nr实数Places_eq_zero
  条件: [数域 K] [h : 是TotallyComplex K]
  证明: nrRealPlaces_eq_zero_iff.mpr h

Depends on / 依赖: nrRealPlaces_eq_zero_iff, nrRealPlaces_eq_zero_iff.mpr
-/
theorem IsTotallyComplex.nrRealPlaces_eq_zero [NumberField K] [h : IsTotallyComplex K] :
    nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr h

/--
theorem `IsTotallyComplex.finrank` / 定理 `IsTotallyComplex.finrank`

English:
theorem IsTotallyComplex.finrank
  given: [NumberField K] [h : IsTotallyComplex K]
  proof: by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrRealPlaces_eq_zero_iff.mpr h]; rw [zero_add]

中文:
定理 是TotallyComplex.finrank
  条件: [数域 K] [h : 是TotallyComplex K]
  证明: by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrRealPlaces_eq_zero_iff.mpr h]; rw [zero_add]
-/
protected theorem IsTotallyComplex.finrank [NumberField K] [h : IsTotallyComplex K] :
    finrank Rat K = 2 * nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank]; rw [nrRealPlaces_eq_zero_iff.mpr h]; rw [zero_add]

end TotallyComplexField

end NumberField
