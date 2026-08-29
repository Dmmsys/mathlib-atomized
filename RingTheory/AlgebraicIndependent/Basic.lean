/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic Independence

This file contains basic results on algebraic independence of a family of elements of an `R`-algebra

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

@[expose] public section


noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v v'

variable {ι : Type u} {ι' R : Type*} {A : Type v} {A' : Type v'} {x : ι -> A}
variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

variable (R A) in
/--
Definition of `Algebra.trdeg` / `Algebra.trdeg` 的定义

English:
definition Algebra.trdeg
  signature: : Cardinal.{v}
  body: ⨆ ι : { s : Set A // AlgebraicIndepOn R _root_.id s }, Cardinal.mk ι.1

中文:
定义 代数.trdeg
  签名: : 基数.{v}
  定义体: ⨆ ι : { s : Set A // AlgebraicIndepOn R _root_.id s }, Cardinal.mk ι.1
-/
@[stacks 030G] def Algebra.trdeg : Cardinal.{v} :=
  ⨆ ι : { s : Set A // AlgebraicIndepOn R _root_.id s }, Cardinal.mk ι.1

/--
theorem `algebraicIndependent_iff_ker_eq_bot` / 定理 `algebraicIndependent_iff_ker_eq_bot`

English:
theorem algebraicIndependent_iff_ker_eq_bot
  proof: RingHom.injective_iff_ker_eq_bot _

@[simp]

中文:
定理 algebraicIndependent_iff_ker_eq_bot
  证明: RingHom.injective_iff_ker_eq_bot _

@[simp]

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, injective_iff_ker_eq_bot
-/
theorem algebraicIndependent_iff_ker_eq_bot :
    AlgebraicIndependent R x ↔
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι R ->ₐ[R] A).toRingHom = ⊥ :=
  RingHom.injective_iff_ker_eq_bot _

@[simp]
/--
theorem `algebraicIndependent_empty_type_iff` / 定理 `algebraicIndependent_empty_type_iff`

English:
theorem algebraicIndependent_empty_type_iff
  given: [IsEmpty ι]
  proof: by
  rw [algebraicIndependent_iff_injective_aeval]; rw [MvPolynomial.aeval_injective_iff_of_isEmpty]

中文:
定理 algebraicIndependent_empty_type_iff
  条件: [是空 ι]
  证明: by
  rw [algebraicIndependent_iff_injective_aeval]; rw [MvPolynomial.aeval_injective_iff_of_isEmpty]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_injective_iff_of_isEmpty, aeval_injective_iff_of_isEmpty, algebraicIndependent_iff_injective_aeval
-/
theorem algebraicIndependent_empty_type_iff [IsEmpty ι] :
    AlgebraicIndependent R x ↔ Injective (algebraMap R A) := by
  rw [algebraicIndependent_iff_injective_aeval]; rw [MvPolynomial.aeval_injective_iff_of_isEmpty]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: R A] : Nonempty { s
  body: ⟨∅, algebraicIndependent_empty_type_iff.mpr FaithfulSMul.algebraMap_injective R A⟩

中文:
实例 [忠实标量乘法
  签名: R A] : 非空 { s
  定义体: ⟨∅, algebraicIndependent_empty_type_iff.mpr FaithfulSMul.algebraMap_injective R A⟩
-/
instance [FaithfulSMul R A] : Nonempty { s : Set A // AlgebraicIndepOn R id s } :=
⟨∅, algebraicIndependent_empty_type_iff.mpr FaithfulSMul.algebraMap_injective R A⟩

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: Injective (algebraMap R A)
  proof: by
  simpa [Function.comp_def] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)

中文:
定理 algebraMap_injective
  结论: 单射 (algebraMap R A)
  证明: by
  simpa [Function.comp_def] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)

Depends on / 依赖: C_injective, Function, Function.comp_def, Injective, Injective.of_comp_iff, MvPolynomial, MvPolynomial.C, MvPolynomial.C_injective, algebraicIndependent_iff_injective_aeval, comp_def, of_comp_iff
-/
theorem algebraMap_injective : Injective (algebraMap R A) := by
  simpa [Function.comp_def] using
    (Injective.of_comp_iff (algebraicIndependent_iff_injective_aeval.1 hx) MvPolynomial.C).2
      (MvPolynomial.C_injective _ _)

/--
theorem `linearIndependent` / 定理 `linearIndependent`

English:
theorem linearIndependent
  statement: LinearIndependent R x
  proof: by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have : Finsupp.linearCombination R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.linearCombination R X) := by
    ext
    simp
  rw [this]
  refine (algebraicIndependent_iff_injective_aeval.mp hx).comp ?_
  rw [← linea

中文:
定理 linearIndependent
  结论: LinearIndependent R x
  证明: by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have : Finsupp.linearCombination R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.linearCombination R X) := by
    ext
    simp
  rw [this]
  refine (algebraicIndependent_iff_injective_aeval.mp hx).comp ?_
  rw [← linea

Depends on / 依赖: Finsupp, Finsupp.linearCombination, MvPolynomial, MvPolynomial.aeval, algebraicIndependent_iff_injective_aeval, algebraicIndependent_iff_injective_aeval.mp, linearCombination, linearIndependent_X, linearIndependent_iff_injective_finsuppLinearCombination, toLinearMap, toLinearMap.comp
-/
theorem linearIndependent : LinearIndependent R x := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have : Finsupp.linearCombination R x =
      (MvPolynomial.aeval x).toLinearMap.comp (Finsupp.linearCombination R X) := by
    ext
    simp
  rw [this]
  refine (algebraicIndependent_iff_injective_aeval.mp hx).comp ?_
  rw [← linearIndependent_iff_injective_finsuppLinearCombination]
  exact linearIndependent_X _ _

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: [Nontrivial R]
  statement: Injective x
  proof: hx.linearIndependent.injective

中文:
定理 injective
  条件: [非平凡 R]
  结论: 单射 x
  证明: hx.linearIndependent.injective
-/
protected theorem injective [Nontrivial R] : Injective x :=
  hx.linearIndependent.injective

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial R] (i : ι)
  statement: x i != 0
  proof: hx.linearIndependent.ne_zero i

中文:
定理 ne_zero
  条件: [非平凡 R] (i : ι)
  结论: x i != 0
  证明: hx.linearIndependent.ne_zero i

Depends on / 依赖: hx.linearIndependent.ne_zero, linearIndependent, ne_zero
-/
theorem ne_zero [Nontrivial R] (i : ι) : x i != 0 :=
  hx.linearIndependent.ne_zero i

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x)))
  proof: by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : forall p : MvPolynomial ι R, aeval x p in (@aeval R _ _ _ _ _ ((↑) : range x -> A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, ?_⟩
    simp [Func

中文:
定理 map
  条件: {f : A ->ₐ[R] A'} (hf_inj : 集合.单射限制 f (adjoin R (range x)))
  证明: by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : forall p : MvPolynomial ι R, aeval x p in (@aeval R _ _ _ _ _ ((↑) : range x -> A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, ?_⟩
    simp [Func

Depends on / 依赖: AlgHom, AlgHom.mem_range, Function, Function.comp_def, MvPolynomial, MvPolynomial.rename, adjoin_eq_range, aeval_rename, codRestrict, comp_def, f.comp, hf_inj, mem_range, mem_range_self
-/
theorem map {f : A ->ₐ[R] A'} (hf_inj : Set.InjOn f (adjoin R (range x))) :
    AlgebraicIndependent R (f ∘ x) := by
  have : aeval (f ∘ x) = f.comp (aeval x) := by ext; simp
  have h : forall p : MvPolynomial ι R, aeval x p in (@aeval R _ _ _ _ _ ((↑) : range x -> A)).range := by
    intro p
    rw [AlgHom.mem_range]
    refine ⟨MvPolynomial.rename (codRestrict x (range x) mem_range_self) p, ?_⟩
    simp [Function.comp_def, aeval_rename]
  intro x y hxy
  rw [this] at hxy
  rw [adjoin_eq_range] at hf_inj
  exact hx (hf_inj (h x) (h y) hxy)

/--
theorem `map'` / 定理 `map'`

English:
theorem map'
  given: {f : A ->ₐ[R] A'} (hf_inj : Injective f)
  statement: AlgebraicIndependent R (f ∘ x)
  proof: hx.map hf_inj.injOn

中文:
定理 map'
  条件: {f : A ->ₐ[R] A'} (hf_inj : 单射 f)
  结论: AlgebraicIndependent R (f ∘ x)
  证明: hx.map hf_inj.injOn

Depends on / 依赖: hf_inj, hf_inj.injOn, hx.map
-/
theorem map' {f : A ->ₐ[R] A'} (hf_inj : Injective f) : AlgebraicIndependent R (f ∘ x) :=
  hx.map hf_inj.injOn

/--
theorem `aeval_of_algebraicIndependent` / 定理 `aeval_of_algebraicIndependent`

English:
theorem aeval_of_algebraicIndependent
  proof: by
  rw [algebraicIndependent_iff] at hx hf ⊢
  intro p hp
  exact hf _ (hx _ (by rwa [← aeval_comp_bind₁, AlgHom.comp_apply] at hp))

omit hx in

中文:
定理 aeval_of_algebraicIndependent
  证明: by
  rw [algebraicIndependent_iff] at hx hf ⊢
  intro p hp
  exact hf _ (hx _ (by rwa [← aeval_comp_bind₁, AlgHom.comp_apply] at hp))

omit hx in

Depends on / 依赖: AlgHom, AlgHom.comp_apply, algebraicIndependent_iff, comp_apply
-/
theorem aeval_of_algebraicIndependent
    {f : ι -> MvPolynomial ι R} (hf : AlgebraicIndependent R f) :
    AlgebraicIndependent R fun i => aeval x (f i) := by
  rw [algebraicIndependent_iff] at hx hf ⊢
  intro p hp
  exact hf _ (hx _ (by rwa [← aeval_comp_bind₁, AlgHom.comp_apply] at hp))

omit hx in
/--
theorem `of_aeval` / 定理 `of_aeval`

English:
theorem of_aeval
  statement: {f : ι -> MvPolynomial ι R}
  proof: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp_bind₁, AlgHom.comp_apply, bind₁, hp, map_zero])

中文:
定理 of_aeval
  结论: {f : ι -> 多元多项式 ι R}
  证明: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp_bind₁, AlgHom.comp_apply, bind₁, hp, map_zero])

Depends on / 依赖: AlgHom, AlgHom.comp_apply, algebraicIndependent_iff, comp_apply, map_zero
-/
theorem of_aeval {f : ι -> MvPolynomial ι R}
    (H : AlgebraicIndependent R fun i => aeval x (f i)) :
    AlgebraicIndependent R f := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp_bind₁, AlgHom.comp_apply, bind₁, hp, map_zero])

end AlgebraicIndependent

/--
theorem `isEmpty_algebraicIndependent` / 定理 `isEmpty_algebraicIndependent`

English:
theorem isEmpty_algebraicIndependent
  given: (h : ¬ Injective (algebraMap R A))
  proof: h s.2.algebraMap_injective

中文:
定理 isEmpty_algebraicIndependent
  条件: (h : ¬ 单射 (algebraMap R A))
  证明: h s.2.algebraMap_injective

Depends on / 依赖: algebraMap_injective
-/
theorem isEmpty_algebraicIndependent (h : ¬ Injective (algebraMap R A)) :
    IsEmpty { s : Set A // AlgebraicIndepOn R id s } where
  false s := h s.2.algebraMap_injective

/--
theorem `trdeg_eq_zero_of_not_injective` / 定理 `trdeg_eq_zero_of_not_injective`

English:
theorem trdeg_eq_zero_of_not_injective
  given: (h : ¬ Injective (algebraMap R A))
  statement: trdeg R A = 0
  proof: by
  have := isEmpty_algebraicIndependent h
  rw [trdeg]; rw [ciSup_of_empty]; rw [bot_eq_zero]

中文:
定理 trdeg_eq_zero_of_not_injective
  条件: (h : ¬ 单射 (algebraMap R A))
  结论: trdeg R A = 0
  证明: by
  have := isEmpty_algebraicIndependent h
  rw [trdeg]; rw [ciSup_of_empty]; rw [bot_eq_zero]

Depends on / 依赖: bot_eq_zero, ciSup_of_empty, isEmpty_algebraicIndependent
-/
theorem trdeg_eq_zero_of_not_injective (h : ¬ Injective (algebraMap R A)) : trdeg R A = 0 := by
  have := isEmpty_algebraicIndependent h
  rw [trdeg]; rw [ciSup_of_empty]; rw [bot_eq_zero]

/--
theorem `MvPolynomial.algebraicIndependent_X` / 定理 `MvPolynomial.algebraicIndependent_X`

English:
theorem MvPolynomial.algebraicIndependent_X
  given: (σ R : Type*) [CommRing R]
  proof: by
  rw [AlgebraicIndependent]; rw [aeval_X_left]
  exact injective_id

中文:
定理 多元多项式.algebraicIndependent_X
  条件: (σ R : 类型) [交换环 R]
  证明: by
  rw [AlgebraicIndependent]; rw [aeval_X_left]
  exact injective_id

Depends on / 依赖: AlgebraicIndependent, aeval_X_left, injective_id
-/
theorem MvPolynomial.algebraicIndependent_X (σ R : Type*) [CommRing R] :
    AlgebraicIndependent R (X (R := R) (σ := σ)) := by
  rw [AlgebraicIndependent]; rw [aeval_X_left]
  exact injective_id

open AlgebraicIndependent

/--
theorem `AlgHom.algebraicIndependent_iff` / 定理 `AlgHom.algebraicIndependent_iff`

English:
theorem AlgHom.algebraicIndependent_iff
  given: (f : A ->ₐ[R] A') (hf : Injective f)
  proof: ⟨fun h => h.of_comp f, fun h => h.map hf.injOn⟩

@[nontriviality]

中文:
定理 代数态射.algebraicIndependent_iff
  条件: (f : A ->ₐ[R] A') (hf : 单射 f)
  证明: ⟨fun h => h.of_comp f, fun h => h.map hf.injOn⟩

@[nontriviality]

Depends on / 依赖: h.map, h.of_comp, hf.injOn, of_comp
-/
theorem AlgHom.algebraicIndependent_iff (f : A ->ₐ[R] A') (hf : Injective f) :
    AlgebraicIndependent R (f ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun h => h.of_comp f, fun h => h.map hf.injOn⟩

@[nontriviality]
/--
theorem `AlgebraicIndependent.of_subsingleton` / 定理 `AlgebraicIndependent.of_subsingleton`

English:
theorem AlgebraicIndependent.of_subsingleton
  given: [Subsingleton R]
  statement: AlgebraicIndependent R x
  proof: algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _

中文:
定理 AlgebraicIndependent.of_subsingleton
  条件: [子单例 R]
  结论: AlgebraicIndependent R x
  证明: algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, algebraicIndependent_iff
-/
theorem AlgebraicIndependent.of_subsingleton [Subsingleton R] : AlgebraicIndependent R x :=
  algebraicIndependent_iff.2 fun _ _ => Subsingleton.elim _ _

/--
theorem `isTranscendenceBasis_iff_of_subsingleton` / 定理 `isTranscendenceBasis_iff_of_subsingleton`

English:
theorem isTranscendenceBasis_iff_of_subsingleton
  given: [Subsingleton R] (x : ι -> A)
  proof: by
  have := Module.subsingleton R A
  refine ⟨fun h => ?_, fun h => ⟨.of_subsingleton, fun s hs hx =>
    hx.antisymm fun a _ => ⟨Classical.arbitrary _, Subsingleton.elim ..⟩⟩⟩
  by_contra! hι
  have := h.2 {0} .of_subsingleton
  simp [range_eq_empty, eq_comm (a := ∅)] at this

中文:
定理 isTranscendenceBasis_iff_of_subsingleton
  条件: [子单例 R] (x : ι -> A)
  证明: by
  have := Module.subsingleton R A
  refine ⟨fun h => ?_, fun h => ⟨.of_subsingleton, fun s hs hx =>
    hx.antisymm fun a _ => ⟨Classical.arbitrary _, Subsingleton.elim ..⟩⟩⟩
  by_contra! hι
  have := h.2 {0} .of_subsingleton
  simp [range_eq_empty, eq_comm (a := ∅)] at this

Depends on / 依赖: Classical, Classical.arbitrary, Module, Module.subsingleton, Subsingleton, Subsingleton.elim, antisymm, arbitrary, eq_comm, hx.antisymm, of_subsingleton, range_eq_empty, subsingleton
-/
theorem isTranscendenceBasis_iff_of_subsingleton [Subsingleton R] (x : ι -> A) :
    IsTranscendenceBasis R x ↔ Nonempty ι := by
  have := Module.subsingleton R A
  refine ⟨fun h => ?_, fun h => ⟨.of_subsingleton, fun s hs hx =>
    hx.antisymm fun a _ => ⟨Classical.arbitrary _, Subsingleton.elim ..⟩⟩⟩
  by_contra! hι
  have := h.2 {0} .of_subsingleton
  simp [range_eq_empty, eq_comm (a := ∅)] at this

/--
theorem `IsTranscendenceBasis.of_subsingleton` / 定理 `IsTranscendenceBasis.of_subsingleton`

English:
theorem IsTranscendenceBasis.of_subsingleton
  given: [Subsingleton R] [Nonempty ι]
  proof: (isTranscendenceBasis_iff_of_subsingleton x).mpr ‹_›

中文:
定理 IsTranscendenceBasis.of_subsingleton
  条件: [子单例 R] [非空 ι]
  证明: (isTranscendenceBasis_iff_of_subsingleton x).mpr ‹_›
-/
@[nontriviality] theorem IsTranscendenceBasis.of_subsingleton [Subsingleton R] [Nonempty ι] :
    IsTranscendenceBasis R x :=
  (isTranscendenceBasis_iff_of_subsingleton x).mpr ‹_›

/--
theorem `trdeg_subsingleton` / 定理 `trdeg_subsingleton`

English:
theorem trdeg_subsingleton
  given: [Subsingleton R]
  statement: trdeg R A = 1
  proof: have := Module.subsingleton R A
(ciSup_le' fun s => by simpa using Set.subsingleton_of_subsingleton).antisymm le_ciSup_of_le
    Cardinal.bddAbove_of_small ⟨{0}, .of_subsingleton⟩ (by simp)

中文:
定理 trdeg_subsingleton
  条件: [子单例 R]
  结论: trdeg R A = 1
  证明: have := Module.subsingleton R A
(ciSup_le' fun s => by simpa using Set.subsingleton_of_subsingleton).antisymm le_ciSup_of_le
    Cardinal.bddAbove_of_small ⟨{0}, .of_subsingleton⟩ (by simp)
-/
@[nontriviality] theorem trdeg_subsingleton [Subsingleton R] : trdeg R A = 1 :=
  have := Module.subsingleton R A
(ciSup_le' fun s => by simpa using Set.subsingleton_of_subsingleton).antisymm le_ciSup_of_le
    Cardinal.bddAbove_of_small ⟨{0}, .of_subsingleton⟩ (by simp)

/--
theorem `algebraicIndependent_adjoin` / 定理 `algebraicIndependent_adjoin`

English:
theorem algebraicIndependent_adjoin
  given: (hs : AlgebraicIndependent R x)
  proof: AlgebraicIndependent.of_comp (adjoin R (range x)).val hs

中文:
定理 algebraicIndependent_adjoin
  条件: (hs : AlgebraicIndependent R x)
  证明: AlgebraicIndependent.of_comp (adjoin R (range x)).val hs

Depends on / 依赖: AlgebraicIndependent, AlgebraicIndependent.of_comp, adjoin, of_comp
-/
theorem algebraicIndependent_adjoin (hs : AlgebraicIndependent R x) :
    @AlgebraicIndependent ι R (adjoin R (range x))
      (fun i : ι => ⟨x i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
  AlgebraicIndependent.of_comp (adjoin R (range x)).val hs

/--
theorem `AlgebraicIndependent.restrictScalars` / 定理 `AlgebraicIndependent.restrictScalars`

English:
theorem AlgebraicIndependent.restrictScalars
  statement: {K : Type*} [CommRing K] [Algebra R K] [Algebra K A]
  proof: by
  have : (aeval x : MvPolynomial ι K ->ₐ[K] A).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (aeval x : MvPolynomial ι R ->ₐ[R] A).toRingHom := by
    ext <;> simp [algebraMap_eq_smul_one]
  change Injective (aeval x).toRingHom
  rw [← this]; rw [RingHom.coe_comp]
  exact Injective.c

中文:
定理 AlgebraicIndependent.restrictScalars
  结论: {K : 类型} [交换环 K] [代数 R K] [代数 K A]
  证明: by
  have : (aeval x : MvPolynomial ι K ->ₐ[K] A).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (aeval x : MvPolynomial ι R ->ₐ[R] A).toRingHom := by
    ext <;> simp [algebraMap_eq_smul_one]
  change Injective (aeval x).toRingHom
  rw [← this]; rw [RingHom.coe_comp]
  exact Injective.c

Depends on / 依赖: Injective, Injective.comp, MvPolynomial, MvPolynomial.map, MvPolynomial.map_injective, RingHom, RingHom.coe_comp, algebraMap, algebraMap_eq_smul_one, coe_comp, map_injective, toRingHom, toRingHom.comp
-/
theorem AlgebraicIndependent.restrictScalars {K : Type*} [CommRing K] [Algebra R K] [Algebra K A]
    [IsScalarTower R K A] (hinj : Function.Injective (algebraMap R K))
    (ai : AlgebraicIndependent K x) : AlgebraicIndependent R x := by
  have : (aeval x : MvPolynomial ι K ->ₐ[K] A).toRingHom.comp (MvPolynomial.map (algebraMap R K)) =
      (aeval x : MvPolynomial ι R ->ₐ[R] A).toRingHom := by
    ext <;> simp [algebraMap_eq_smul_one]
  change Injective (aeval x).toRingHom
  rw [← this]; rw [RingHom.coe_comp]
  exact Injective.comp ai (MvPolynomial.map_injective _ hinj)

section RingHom

variable {S B FRS FAB : Type*} [CommRing S] [CommRing B] [Algebra S B]

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/--
theorem `AlgebraicIndependent.of_ringHom_of_comp_eq` / 定理 `AlgebraicIndependent.of_ringHom_of_comp_eq`

English:
theorem AlgebraicIndependent.of_ringHom_of_comp_eq
  statement: (H : AlgebraicIndependent S (g ∘ x))
  proof: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
have := H (p.map f) by
    have : (g : A ->+* B) _ = _ := congr(g $hp)
    rwa [map_zero, map_aeval, ← h, ← eval₂Hom_map_hom, ← aeval_eq_eval₂Hom] at this
  exact map_injective (f : R ->+* S) hf (by rwa [map_zero])

中文:
定理 AlgebraicIndependent.of_ringHom_of_comp_eq
  结论: (H : AlgebraicIndependent S (g ∘ x))
  证明: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
have := H (p.map f) by
    have : (g : A ->+* B) _ = _ := congr(g $hp)
    rwa [map_zero, map_aeval, ← h, ← eval₂Hom_map_hom, ← aeval_eq_eval₂Hom] at this
  exact map_injective (f : R ->+* S) hf (by rwa [map_zero])

Depends on / 依赖: algebraicIndependent_iff, map_aeval, map_injective, map_zero, p.map
-/
theorem AlgebraicIndependent.of_ringHom_of_comp_eq (H : AlgebraicIndependent S (g ∘ x))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent R x := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
have := H (p.map f) by
    have : (g : A ->+* B) _ = _ := congr(g $hp)
    rwa [map_zero, map_aeval, ← h, ← eval₂Hom_map_hom, ← aeval_eq_eval₂Hom] at this
  exact map_injective (f : R ->+* S) hf (by rwa [map_zero])

/--
theorem `AlgebraicIndependent.ringHom_of_comp_eq` / 定理 `AlgebraicIndependent.ringHom_of_comp_eq`

English:
theorem AlgebraicIndependent.ringHom_of_comp_eq
  statement: (H : AlgebraicIndependent R x)
  proof: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  rw [H q (hg (by rwa [map_zero]; rw [← RingHom.coe_coe g]; rw [map_aeval]; rw [← h]; rw [← eval₂Hom_map_hom]; rw [← aeval_eq_eval₂Hom])), map_zero]

中文:
定理 AlgebraicIndependent.ringHom_of_comp_eq
  结论: (H : AlgebraicIndependent R x)
  证明: by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  rw [H q (hg (by rwa [map_zero]; rw [← RingHom.coe_coe g]; rw [map_aeval]; rw [← h]; rw [← eval₂Hom_map_hom]; rw [← aeval_eq_eval₂Hom])), map_zero]

Depends on / 依赖: RingHom, RingHom.coe_coe, algebraicIndependent_iff, coe_coe, map_aeval, map_surjective, map_zero
-/
theorem AlgebraicIndependent.ringHom_of_comp_eq (H : AlgebraicIndependent R x)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) := by
  rw [algebraicIndependent_iff] at H ⊢
  intro p hp
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  rw [H q (hg (by rwa [map_zero]; rw [← RingHom.coe_coe g]; rw [map_aeval]; rw [← h]; rw [← eval₂Hom_map_hom]; rw [← aeval_eq_eval₂Hom])), map_zero]

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/--
theorem `algebraicIndependent_ringHom_iff_of_comp_eq` / 定理 `algebraicIndependent_ringHom_iff_of_comp_eq`

English:
theorem algebraicIndependent_ringHom_iff_of_comp_eq
  proof: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.injective f) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.surjective f) hg h⟩

中文:
定理 algebraicIndependent_ringHom_iff_of_comp_eq
  证明: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.injective f) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.surjective f) hg h⟩

Depends on / 依赖: EquivLike, EquivLike.injective, EquivLike.surjective, H.of_ringHom_of_comp_eq, H.ringHom_of_comp_eq, injective, of_ringHom_of_comp_eq, ringHom_of_comp_eq, surjective
-/
theorem algebraicIndependent_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    AlgebraicIndependent S (g ∘ x) ↔ AlgebraicIndependent R x :=
  ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.injective f) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.surjective f) hg h⟩

end

end RingHom

/--
theorem `algebraicIndependent_finset_map_embedding_subtype` / 定理 `algebraicIndependent_finset_map_embedding_subtype`

English:
theorem algebraicIndependent_finset_map_embedding_subtype
  statement: (s : Set A)
  proof: by
  let f : t.map (Embedding.subtype (· in s)) -> s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert! AlgebraicIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Fi

中文:
定理 algebraicIndependent_finset_map_embedding_subtype
  结论: (s : 集合 A)
  证明: by
  let f : t.map (Embedding.subtype (· in s)) -> s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert! AlgebraicIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Fi

Depends on / 依赖: AlgebraicIndependent, AlgebraicIndependent.comp, Embedding, Embedding.coe_subtype, Embedding.subtype, Finset, Finset.mem_map, Subtype, Subtype.coe_prop, Subtype.mk_eq_mk, coe_prop, coe_subtype, convert, imp_self, mem_map, mk_eq_mk, subtype, t.map
-/
theorem algebraicIndependent_finset_map_embedding_subtype (s : Set A)
    (li : AlgebraicIndependent R ((↑) : s -> A)) (t : Finset s) :
    AlgebraicIndependent R ((↑) : Finset.map (Embedding.subtype (· in s)) t -> A) := by
  let f : t.map (Embedding.subtype (· in s)) -> s := fun x =>
    ⟨x.1, by
      obtain ⟨x, h⟩ := x
      rw [Finset.mem_map] at h
      obtain ⟨a, _, rfl⟩ := h
      simp only [Subtype.coe_prop, Embedding.coe_subtype]⟩
  convert! AlgebraicIndependent.comp li f _
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Finset.mem_map] at hx hy
  obtain ⟨a, _, rfl⟩ := hx
  obtain ⟨b, _, rfl⟩ := hy
  simp only [f, imp_self, Subtype.mk_eq_mk]

/--
theorem `algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded` / 定理 `algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded`

English:
theorem algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded
  statement: {n : Nat}
  proof: by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply algebraicIndependent_finset_map_embedding_subtype _ li

中文:
定理 algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded
  结论: {n : 自然数}
  证明: by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply algebraicIndependent_finset_map_embedding_subtype _ li

Depends on / 依赖: Cardinal, Cardinal.card_le_of, Embedding, Embedding.subtype, Finset, Finset.card_map, algebraicIndependent_finset_map_embedding_subtype, card_le_of, card_map, subtype
-/
theorem algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded {n : Nat}
    (H : forall s : Finset A, (AlgebraicIndependent R fun i : s => (i : A)) -> s.card <= n) :
    forall s : Set A, AlgebraicIndependent R ((↑) : s -> A) -> Cardinal.mk s <= n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· in s))]
  apply H
  apply algebraicIndependent_finset_map_embedding_subtype _ li

section Subtype

/--
theorem `AlgebraicIndependent.restrict_of_comp_subtype` / 定理 `AlgebraicIndependent.restrict_of_comp_subtype`

English:
theorem AlgebraicIndependent.restrict_of_comp_subtype
  statement: {s : Set ι}
  proof: hs

中文:
定理 AlgebraicIndependent.restrict_of_comp_subtype
  结论: {s : 集合 ι}
  证明: hs
-/
theorem AlgebraicIndependent.restrict_of_comp_subtype {s : Set ι}
    (hs : AlgebraicIndependent R (x ∘ (↑) : s -> A)) : AlgebraicIndependent R (s.domRestrict x) :=
  hs

variable (R A)

/--
theorem `algebraicIndependent_empty_iff` / 定理 `algebraicIndependent_empty_iff`

English:
theorem algebraicIndependent_empty_iff
  proof: by simp

中文:
定理 algebraicIndependent_empty_iff
  证明: by simp
-/
theorem algebraicIndependent_empty_iff :
    AlgebraicIndependent R ((↑) : (∅ : Set A) -> A) ↔ Injective (algebraMap R A) := by simp

end Subtype

/--
theorem `AlgebraicIndependent.to_subtype_range` / 定理 `AlgebraicIndependent.to_subtype_range`

English:
theorem AlgebraicIndependent.to_subtype_range
  given: (hx : AlgebraicIndependent R x)
  proof: by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hx.injective]

中文:
定理 AlgebraicIndependent.to_subtype_range
  条件: (hx : AlgebraicIndependent R x)
  证明: by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hx.injective]

Depends on / 依赖: algebraicIndependent_subtype_range, hx.injective, injective, nontriviality
-/
theorem AlgebraicIndependent.to_subtype_range (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R ((↑) : range x -> A) := by
  nontriviality R
  rwa [algebraicIndependent_subtype_range hx.injective]

/--
theorem `AlgebraicIndependent.to_subtype_range'` / 定理 `AlgebraicIndependent.to_subtype_range'`

English:
theorem AlgebraicIndependent.to_subtype_range'
  statement: (hx : AlgebraicIndependent R x) {t}
  proof: ht ▸ hx.to_subtype_range

中文:
定理 AlgebraicIndependent.to_subtype_range'
  结论: (hx : AlgebraicIndependent R x) {t}
  证明: ht ▸ hx.to_subtype_range

Depends on / 依赖: hx.to_subtype_range, to_subtype_range
-/
theorem AlgebraicIndependent.to_subtype_range' (hx : AlgebraicIndependent R x) {t}
    (ht : range x = t) : AlgebraicIndependent R ((↑) : t -> A) :=
  ht ▸ hx.to_subtype_range

/--
theorem `IsTranscendenceBasis.to_subtype_range` / 定理 `IsTranscendenceBasis.to_subtype_range`

English:
theorem IsTranscendenceBasis.to_subtype_range
  given: (hx : IsTranscendenceBasis R x)
  proof: by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  · rwa [isTranscendenceBasis_subtype_range hx.1.injective]

中文:
定理 IsTranscendenceBasis.to_subtype_range
  条件: (hx : IsTranscendenceBasis R x)
  证明: by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  · rwa [isTranscendenceBasis_subtype_range hx.1.injective]

Depends on / 依赖: infer_instance, injective, isTranscendenceBasis_iff_of_subsingleton, isTranscendenceBasis_subtype_range, subsingleton_or_nontrivial
-/
theorem IsTranscendenceBasis.to_subtype_range (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis R ((↑) : range x -> A) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  · rwa [isTranscendenceBasis_subtype_range hx.1.injective]

/--
theorem `IsTranscendenceBasis.to_subtype_range'` / 定理 `IsTranscendenceBasis.to_subtype_range'`

English:
theorem IsTranscendenceBasis.to_subtype_range'
  statement: (hx : IsTranscendenceBasis R x) {t}
  proof: ht ▸ hx.to_subtype_range

中文:
定理 IsTranscendenceBasis.to_subtype_range'
  结论: (hx : IsTranscendenceBasis R x) {t}
  证明: ht ▸ hx.to_subtype_range

Depends on / 依赖: hx.to_subtype_range, to_subtype_range
-/
theorem IsTranscendenceBasis.to_subtype_range' (hx : IsTranscendenceBasis R x) {t}
    (ht : range x = t) : IsTranscendenceBasis R ((↑) : t -> A) :=
  ht ▸ hx.to_subtype_range

/--
lemma `IsTranscendenceBasis.of_comp` / 引理 `IsTranscendenceBasis.of_comp`

English:
lemma IsTranscendenceBasis.of_comp
  statement: {x : ι -> A} (f : A ->ₐ[R] A') (h : Function.Injective f)
  proof: by
  refine ⟨(AlgHom.algebraicIndependent_iff f h).mp H.1, ?_⟩
  intro s hs hs'
  have := H.2 (f '' s)
    ((algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs))
    (by rw [Set.range_comp]; exact Set.image_mono hs')
  rwa [Set.range_comp, (Set.image_injective.mpr h

中文:
引理 IsTranscendenceBasis.of_comp
  结论: {x : ι -> A} (f : A ->ₐ[R] A') (h : 函数.单射 f)
  证明: by
  refine ⟨(AlgHom.algebraicIndependent_iff f h).mp H.1, ?_⟩
  intro s hs hs'
  have := H.2 (f '' s)
    ((algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs))
    (by rw [Set.range_comp]; exact Set.image_mono hs')
  rwa [Set.range_comp, (Set.image_injective.mpr h

Depends on / 依赖: AlgHom, AlgHom.algebraicIndependent_iff, Set.image_injective.mpr, Set.image_mono, Set.range_comp, algebraicIndependent_iff, algebraicIndependent_image, eq_iff, h.injOn, image_injective, image_mono, range_comp
-/
lemma IsTranscendenceBasis.of_comp {x : ι -> A} (f : A ->ₐ[R] A') (h : Function.Injective f)
    (H : IsTranscendenceBasis R (f ∘ x)) :
    IsTranscendenceBasis R x := by
  refine ⟨(AlgHom.algebraicIndependent_iff f h).mp H.1, ?_⟩
  intro s hs hs'
  have := H.2 (f '' s)
    ((algebraicIndependent_image h.injOn).mp ((AlgHom.algebraicIndependent_iff f h).mpr hs))
    (by rw [Set.range_comp]; exact Set.image_mono hs')
  rwa [Set.range_comp, (Set.image_injective.mpr h).eq_iff] at this

/--
lemma `IsTranscendenceBasis.of_comp_algebraMap` / 引理 `IsTranscendenceBasis.of_comp_algebraMap`

English:
lemma IsTranscendenceBasis.of_comp_algebraMap
  statement: [Algebra A A'] [IsScalarTower R A A']
  proof: .of_comp (IsScalarTower.toAlgHom R A A') (FaithfulSMul.algebraMap_injective A A') H

中文:
引理 IsTranscendenceBasis.of_comp_algebraMap
  结论: [代数 A A'] [标量塔 R A A']
  证明: .of_comp (IsScalarTower.toAlgHom R A A') (FaithfulSMul.algebraMap_injective A A') H

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsScalarTower, IsScalarTower.toAlgHom, algebraMap_injective, of_comp, toAlgHom
-/
lemma IsTranscendenceBasis.of_comp_algebraMap [Algebra A A'] [IsScalarTower R A A']
    [FaithfulSMul A A'] {x : ι -> A} (H : IsTranscendenceBasis R (algebraMap A A' ∘ x)) :
    IsTranscendenceBasis R x :=
  .of_comp (IsScalarTower.toAlgHom R A A') (FaithfulSMul.algebraMap_injective A A') H

/--
theorem `AlgEquiv.isTranscendenceBasis` / 定理 `AlgEquiv.isTranscendenceBasis`

English:
theorem AlgEquiv.isTranscendenceBasis
  given: (e : A ≃ₐ[R] A') (hx : IsTranscendenceBasis R x)
  proof: .of_comp e.symm.toAlgHom e.symm.injective (by convert! hx; ext; simp)

中文:
定理 代数等价.isTranscendenceBasis
  条件: (e : A ≃ₐ[R] A') (hx : IsTranscendenceBasis R x)
  证明: .of_comp e.symm.toAlgHom e.symm.injective (by convert! hx; ext; simp)

Depends on / 依赖: convert, e.symm.injective, e.symm.toAlgHom, injective, of_comp, toAlgHom
-/
theorem AlgEquiv.isTranscendenceBasis (e : A ≃ₐ[R] A') (hx : IsTranscendenceBasis R x) :
    IsTranscendenceBasis R (e ∘ x) :=
  .of_comp e.symm.toAlgHom e.symm.injective (by convert! hx; ext; simp)

/--
theorem `AlgEquiv.isTranscendenceBasis_iff` / 定理 `AlgEquiv.isTranscendenceBasis_iff`

English:
theorem AlgEquiv.isTranscendenceBasis_iff
  given: (e : A ≃ₐ[R] A')
  proof: ⟨fun hx => by convert! e.symm.isTranscendenceBasis hx; ext; simp, e.isTranscendenceBasis⟩

中文:
定理 代数等价.isTranscendenceBasis_iff
  条件: (e : A ≃ₐ[R] A')
  证明: ⟨fun hx => by convert! e.symm.isTranscendenceBasis hx; ext; simp, e.isTranscendenceBasis⟩

Depends on / 依赖: convert, e.isTranscendenceBasis, e.symm.isTranscendenceBasis, isTranscendenceBasis
-/
theorem AlgEquiv.isTranscendenceBasis_iff (e : A ≃ₐ[R] A') :
    IsTranscendenceBasis R (e ∘ x) ↔ IsTranscendenceBasis R x :=
  ⟨fun hx => by convert! e.symm.isTranscendenceBasis hx; ext; simp, e.isTranscendenceBasis⟩

section trdeg

open Cardinal

/--
theorem `AlgebraicIndependent.lift_cardinalMk_le_trdeg` / 定理 `AlgebraicIndependent.lift_cardinalMk_le_trdeg`

English:
theorem AlgebraicIndependent.lift_cardinalMk_le_trdeg
  statement: [Nontrivial R]
  proof: by
  rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.injective⟩]; rw [lift_le]
  exact le_ciSup_of_le bddAbove_of_small ⟨_, hx.to_subtype_range⟩ le_rfl

中文:
定理 AlgebraicIndependent.lift_cardinalMk_le_trdeg
  结论: [非平凡 R]
  证明: by
  rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.injective⟩]; rw [lift_le]
  exact le_ciSup_of_le bddAbove_of_small ⟨_, hx.to_subtype_range⟩ le_rfl

Depends on / 依赖: bddAbove_of_small, hx.injective, hx.to_subtype_range, injective, le_ciSup_of_le, le_rfl, lift_le, lift_mk_eq, ofInjective, to_subtype_range
-/
theorem AlgebraicIndependent.lift_cardinalMk_le_trdeg [Nontrivial R]
    (hx : AlgebraicIndependent R x) : lift.{v} #ι <= lift.{u} (trdeg R A) := by
  rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.injective⟩]; rw [lift_le]
  exact le_ciSup_of_le bddAbove_of_small ⟨_, hx.to_subtype_range⟩ le_rfl

/--
theorem `AlgebraicIndependent.cardinalMk_le_trdeg` / 定理 `AlgebraicIndependent.cardinalMk_le_trdeg`

English:
theorem AlgebraicIndependent.cardinalMk_le_trdeg
  statement: [Nontrivial R] {ι : Type v} {x : ι -> A}
  proof: by
  rw [← (#ι).lift_id]; rw [← (trdeg R A).lift_id]; exact hx.lift_cardinalMk_le_trdeg

中文:
定理 AlgebraicIndependent.cardinalMk_le_trdeg
  结论: [非平凡 R] {ι : 类型v} {x : ι -> A}
  证明: by
  rw [← (#ι).lift_id]; rw [← (trdeg R A).lift_id]; exact hx.lift_cardinalMk_le_trdeg

Depends on / 依赖: hx.lift_cardinalMk_le_trdeg, lift_cardinalMk_le_trdeg, lift_id
-/
theorem AlgebraicIndependent.cardinalMk_le_trdeg [Nontrivial R] {ι : Type v} {x : ι -> A}
    (hx : AlgebraicIndependent R x) : #ι <= trdeg R A := by
  rw [← (#ι).lift_id]; rw [← (trdeg R A).lift_id]; exact hx.lift_cardinalMk_le_trdeg

/--
theorem `lift_trdeg_le_of_injective` / 定理 `lift_trdeg_le_of_injective`

English:
theorem lift_trdeg_le_of_injective
  given: (f : A ->ₐ[R] A') (hf : Injective f)
  proof: by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => (i.2.map' hf).lift_cardinalMk_le_trdeg

中文:
定理 lift_trdeg_le_of_injective
  条件: (f : A ->ₐ[R] A') (hf : 单射 f)
  证明: by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => (i.2.map' hf).lift_cardinalMk_le_trdeg

Depends on / 依赖: bddAbove_of_small, ciSup_le, lift_cardinalMk_le_trdeg, lift_iSup, nontriviality
-/
theorem lift_trdeg_le_of_injective (f : A ->ₐ[R] A') (hf : Injective f) :
    lift.{v'} (trdeg R A) <= lift.{v} (trdeg R A') := by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  exact ciSup_le' fun i => (i.2.map' hf).lift_cardinalMk_le_trdeg

/--
theorem `trdeg_le_of_injective` / 定理 `trdeg_le_of_injective`

English:
theorem trdeg_le_of_injective
  statement: {A' : Type v} [CommRing A'] [Algebra R A'] (f : A ->ₐ[R] A')
  proof: by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_injective f hf

中文:
定理 trdeg_le_of_injective
  结论: {A' : 类型v} [交换环 A'] [代数 R A'] (f : A ->ₐ[R] A')
  证明: by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_injective f hf

Depends on / 依赖: lift_id, lift_trdeg_le_of_injective
-/
theorem trdeg_le_of_injective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A ->ₐ[R] A')
    (hf : Injective f) : trdeg R A <= trdeg R A' := by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_injective f hf

/--
theorem `lift_trdeg_le_of_surjective` / 定理 `lift_trdeg_le_of_surjective`

English:
theorem lift_trdeg_le_of_surjective
  given: (f : A ->ₐ[R] A') (hf : Surjective f)
  proof: by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  refine ciSup_le' fun i => (lift_cardinalMk_le_trdeg (x := fun a : i.1 => (⇑f).invFun a) <|
    of_comp f ?_)
  convert! i.2; simp [invFun_eq (hf _)]

中文:
定理 lift_trdeg_le_of_surjective
  条件: (f : A ->ₐ[R] A') (hf : 满射 f)
  证明: by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  refine ciSup_le' fun i => (lift_cardinalMk_le_trdeg (x := fun a : i.1 => (⇑f).invFun a) <|
    of_comp f ?_)
  convert! i.2; simp [invFun_eq (hf _)]

Depends on / 依赖: bddAbove_of_small, ciSup_le, convert, invFun, invFun_eq, lift_cardinalMk_le_trdeg, lift_iSup, nontriviality, of_comp
-/
theorem lift_trdeg_le_of_surjective (f : A ->ₐ[R] A') (hf : Surjective f) :
    lift.{v} (trdeg R A') <= lift.{v'} (trdeg R A) := by
  nontriviality R
  rw [trdeg]; rw [lift_iSup bddAbove_of_small]
  refine ciSup_le' fun i => (lift_cardinalMk_le_trdeg (x := fun a : i.1 => (⇑f).invFun a) <|
    of_comp f ?_)
  convert! i.2; simp [invFun_eq (hf _)]

/--
theorem `trdeg_le_of_surjective` / 定理 `trdeg_le_of_surjective`

English:
theorem trdeg_le_of_surjective
  statement: {A' : Type v} [CommRing A'] [Algebra R A'] (f : A ->ₐ[R] A')
  proof: by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_surjective f hf

中文:
定理 trdeg_le_of_surjective
  结论: {A' : 类型v} [交换环 A'] [代数 R A'] (f : A ->ₐ[R] A')
  证明: by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_surjective f hf

Depends on / 依赖: lift_id, lift_trdeg_le_of_surjective
-/
theorem trdeg_le_of_surjective {A' : Type v} [CommRing A'] [Algebra R A'] (f : A ->ₐ[R] A')
    (hf : Surjective f) : trdeg R A' <= trdeg R A := by
  rw [← (trdeg R A).lift_id]; rw [← (trdeg R A').lift_id]; exact lift_trdeg_le_of_surjective f hf

/--
theorem `AlgEquiv.lift_trdeg_eq` / 定理 `AlgEquiv.lift_trdeg_eq`

English:
theorem AlgEquiv.lift_trdeg_eq
  given: (e : A ≃ₐ[R] A')
  proof: (lift_trdeg_le_of_injective e.toAlgHom e.injective).antisymm
    (lift_trdeg_le_of_surjective e.toAlgHom e.surjective)

中文:
定理 代数等价.lift_trdeg_eq
  条件: (e : A ≃ₐ[R] A')
  证明: (lift_trdeg_le_of_injective e.toAlgHom e.injective).antisymm
    (lift_trdeg_le_of_surjective e.toAlgHom e.surjective)

Depends on / 依赖: antisymm, e.injective, e.surjective, e.toAlgHom, injective, lift_trdeg_le_of_injective, lift_trdeg_le_of_surjective, surjective, toAlgHom
-/
theorem AlgEquiv.lift_trdeg_eq (e : A ≃ₐ[R] A') :
    lift.{v'} (trdeg R A) = lift.{v} (trdeg R A') :=
  (lift_trdeg_le_of_injective e.toAlgHom e.injective).antisymm
    (lift_trdeg_le_of_surjective e.toAlgHom e.surjective)

/--
theorem `AlgEquiv.trdeg_eq` / 定理 `AlgEquiv.trdeg_eq`

English:
theorem AlgEquiv.trdeg_eq
  given: {A' : Type v} [CommRing A'] [Algebra R A'] (e : A ≃ₐ[R] A')
  proof: by
  rw [← (trdeg R A).lift_id]; rw [e.lift_trdeg_eq]; rw [lift_id]

中文:
定理 代数等价.trdeg_eq
  条件: {A' : 类型v} [交换环 A'] [代数 R A'] (e : A ≃ₐ[R] A')
  证明: by
  rw [← (trdeg R A).lift_id]; rw [e.lift_trdeg_eq]; rw [lift_id]

Depends on / 依赖: e.lift_trdeg_eq, lift_id, lift_trdeg_eq
-/
theorem AlgEquiv.trdeg_eq {A' : Type v} [CommRing A'] [Algebra R A'] (e : A ≃ₐ[R] A') :
    trdeg R A = trdeg R A' := by
  rw [← (trdeg R A).lift_id]; rw [e.lift_trdeg_eq]; rw [lift_id]

end trdeg

/--
theorem `algebraicIndependent_comp_subtype` / 定理 `algebraicIndependent_comp_subtype`

English:
theorem algebraicIndependent_comp_subtype
  given: {s : Set ι}
  proof: by
  have : (aeval (x ∘ (↑) : s -> A) : _ ->ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : forall p : MvPolynomial s R, rename ((↑) : s -> ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s -> ι) : MvPolynomial s R ->ₐ[R] _).toRingHom).1
      (rename_injective _ Su

中文:
定理 algebraicIndependent_comp_subtype
  条件: {s : 集合 ι}
  证明: by
  have : (aeval (x ∘ (↑) : s -> A) : _ ->ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : forall p : MvPolynomial s R, rename ((↑) : s -> ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s -> ι) : MvPolynomial s R ->ₐ[R] _).toRingHom).1
      (rename_injective _ Su

Depends on / 依赖: MvPolynomial, Subtype, Subtype.val_injective, algebraicIndependent_iff, injective_iff_map_eq_zero, rename_injective, supported_eq_range_rename, toRingHom, val_injective
-/
theorem algebraicIndependent_comp_subtype {s : Set ι} :
    AlgebraicIndependent R (x ∘ (↑) : s -> A) ↔
      forall p in MvPolynomial.supported R s, aeval x p = 0 -> p = 0 := by
  have : (aeval (x ∘ (↑) : s -> A) : _ ->ₐ[R] _) = (aeval x).comp (rename (↑)) := by ext; simp
  have : forall p : MvPolynomial s R, rename ((↑) : s -> ι) p = 0 ↔ p = 0 :=
    (injective_iff_map_eq_zero' (rename ((↑) : s -> ι) : MvPolynomial s R ->ₐ[R] _).toRingHom).1
      (rename_injective _ Subtype.val_injective)
  simp [algebraicIndependent_iff, supported_eq_range_rename, *]

/--
theorem `algebraicIndependent_subtype` / 定理 `algebraicIndependent_subtype`

English:
theorem algebraicIndependent_subtype
  given: {s : Set A}
  proof: by
  apply @algebraicIndependent_comp_subtype _ _ _ id

中文:
定理 algebraicIndependent_subtype
  条件: {s : 集合 A}
  证明: by
  apply @algebraicIndependent_comp_subtype _ _ _ id

Depends on / 依赖: algebraicIndependent_comp_subtype
-/
theorem algebraicIndependent_subtype {s : Set A} :
    AlgebraicIndependent R ((↑) : s -> A) ↔
      forall p : MvPolynomial A R, p in MvPolynomial.supported R s -> aeval id p = 0 -> p = 0 := by
  apply @algebraicIndependent_comp_subtype _ _ _ id

/--
theorem `algebraicIndependent_of_finite` / 定理 `algebraicIndependent_of_finite`

English:
theorem algebraicIndependent_of_finite
  statement: (s : Set A)
  proof: algebraicIndependent_subtype.2 fun p hp =>
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)

中文:
定理 algebraicIndependent_of_finite
  结论: (s : 集合 A)
  证明: algebraicIndependent_subtype.2 fun p hp =>
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)

Depends on / 依赖: Finset, Finset.finite_toSet, algebraicIndependent_subtype, finite_toSet, mem_supported
-/
theorem algebraicIndependent_of_finite (s : Set A)
    (H : forall t subseteq s, t.Finite -> AlgebraicIndependent R ((↑) : t -> A)) :
    AlgebraicIndependent R ((↑) : s -> A) :=
  algebraicIndependent_subtype.2 fun p hp =>
    algebraicIndependent_subtype.1 (H _ (mem_supported.1 hp) (Finset.finite_toSet _)) _ (by simp)

/--
theorem `algebraicIndependent_of_finite_type` / 定理 `algebraicIndependent_of_finite_type`

English:
theorem algebraicIndependent_of_finite_type
  proof: (injective_iff_map_eq_zero _).mpr fun p =>
    algebraicIndependent_comp_subtype.1 (H _ p.vars.finite_toSet) _ p.mem_supported_vars

中文:
定理 algebraicIndependent_of_finite_type
  证明: (injective_iff_map_eq_zero _).mpr fun p =>
    algebraicIndependent_comp_subtype.1 (H _ p.vars.finite_toSet) _ p.mem_supported_vars

Depends on / 依赖: algebraicIndependent_comp_subtype, finite_toSet, injective_iff_map_eq_zero, mem_supported_vars, p.mem_supported_vars, p.vars.finite_toSet
-/
theorem algebraicIndependent_of_finite_type
    (H : forall t : Set ι, t.Finite -> AlgebraicIndependent R fun i : t => x i) :
    AlgebraicIndependent R x :=
  (injective_iff_map_eq_zero _).mpr fun p =>
    algebraicIndependent_comp_subtype.1 (H _ p.vars.finite_toSet) _ p.mem_supported_vars

/--
theorem `AlgebraicIndependent.image_of_comp` / 定理 `AlgebraicIndependent.image_of_comp`

English:
theorem AlgebraicIndependent.image_of_comp
  statement: {ι ι'} (s : Set ι) (f : ι -> ι') (g : ι' -> A)
  proof: by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

中文:
定理 AlgebraicIndependent.image_of_comp
  结论: {ι ι'} (s : 集合 ι) (f : ι -> ι') (g : ι' -> A)
  证明: by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

Depends on / 依赖: Equiv.Set.imageOfInjOn, algebraicIndependent_equiv, hs.injective.of_comp, imageOfInjOn, injOn_iff_injective, injective, nontriviality, of_comp
-/
theorem AlgebraicIndependent.image_of_comp {ι ι'} (s : Set ι) (f : ι -> ι') (g : ι' -> A)
    (hs : AlgebraicIndependent R fun x : s => g (f x)) :
    AlgebraicIndependent R fun x : f '' s => g x := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (algebraicIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

/--
theorem `AlgebraicIndependent.image` / 定理 `AlgebraicIndependent.image`

English:
theorem AlgebraicIndependent.image
  statement: {ι} {s : Set ι} {f : ι -> A}
  proof: by
  convert! AlgebraicIndependent.image_of_comp s f id hs

中文:
定理 AlgebraicIndependent.像
  结论: {ι} {s : 集合 ι} {f : ι -> A}
  证明: by
  convert! AlgebraicIndependent.image_of_comp s f id hs

Depends on / 依赖: AlgebraicIndependent, AlgebraicIndependent.image_of_comp, convert, image_of_comp
-/
theorem AlgebraicIndependent.image {ι} {s : Set ι} {f : ι -> A}
    (hs : AlgebraicIndependent R fun x : s => f x) :
    AlgebraicIndependent R fun x : f '' s => (x : A) := by
  convert! AlgebraicIndependent.image_of_comp s f id hs

/--
theorem `algebraicIndependent_iUnion_of_directed` / 定理 `algebraicIndependent_iUnion_of_directed`

English:
theorem algebraicIndependent_iUnion_of_directed
  statement: {η : Type*} [Nonempty η] {s : η -> Set A}
  proof: by
  refine algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => ?_
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))

中文:
定理 algebraicIndependent_iUnion_of_directed
  结论: {η : 类型} [非空 η] {s : η -> 集合 A}
  证明: by
  refine algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => ?_
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))

Depends on / 依赖: Subset, Subset.trans, algebraicIndependent_of_finite, fi.mem_toFinset, fi.toFinset, finite_subset_iUnion, finset_le, hs.finset_le, mem_toFinset, toFinset
-/
theorem algebraicIndependent_iUnion_of_directed {η : Type*} [Nonempty η] {s : η -> Set A}
    (hs : Directed (· subseteq ·) s) (h : forall i, AlgebraicIndependent R ((↑) : s i -> A)) :
    AlgebraicIndependent R ((↑) : (⋃ i, s i) -> A) := by
  refine algebraicIndependent_of_finite (⋃ i, s i) fun t ht ft => ?_
  rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
  rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
  exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))

/--
theorem `algebraicIndependent_sUnion_of_directed` / 定理 `algebraicIndependent_sUnion_of_directed`

English:
theorem algebraicIndependent_sUnion_of_directed
  statement: {s : Set (Set A)} (hsn : s.Nonempty)
  proof: by
  let : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)

中文:
定理 algebraicIndependent_sUnion_of_directed
  结论: {s : 集合 (集合 A)} (hsn : s.非空)
  证明: by
  let : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)

Depends on / 依赖: Nonempty, Nonempty.to_subtype, algebraicIndependent_iUnion_of_directed, directed_val, hs.directed_val, sUnion_eq_iUnion, to_subtype
-/
theorem algebraicIndependent_sUnion_of_directed {s : Set (Set A)} (hsn : s.Nonempty)
    (hs : DirectedOn (· subseteq ·) s) (h : forall a in s, AlgebraicIndependent R ((↑) : a -> A)) :
    AlgebraicIndependent R ((↑) : ⋃₀ s -> A) := by
  let : Nonempty s := Nonempty.to_subtype hsn
  rw [sUnion_eq_iUnion]
  exact algebraicIndependent_iUnion_of_directed hs.directed_val (by simpa using h)

/--
theorem `exists_maximal_algebraicIndependent` / 定理 `exists_maximal_algebraicIndependent`

English:
theorem exists_maximal_algebraicIndependent
  statement: (s t : Set A) (hst : s subseteq t)
  proof: by
  refine zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u -> A) ∧ u subseteq t}
    (fun c hc chainc hcn => ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ => subset_sUnion_of_mem⟩) s ⟨hs, hst⟩
  · exact algebraicIndependent_sUnion_of_directed hcn chainc.directedOn (fun x hxc => (hc hxc).1)
  exact fun 

中文:
定理 存在_maximal_algebraicIndependent
  结论: (s t : 集合 A) (hst : s subseteq t)
  证明: by
  refine zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u -> A) ∧ u subseteq t}
    (fun c hc chainc hcn => ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ => subset_sUnion_of_mem⟩) s ⟨hs, hst⟩
  · exact algebraicIndependent_sUnion_of_directed hcn chainc.directedOn (fun x hxc => (hc hxc).1)
  exact fun 

Depends on / 依赖: AlgebraicIndependent, algebraicIndependent_sUnion_of_directed, chainc, chainc.directedOn, directedOn, subset_sUnion_of_mem, subseteq, zorn_subset_nonempty
-/
theorem exists_maximal_algebraicIndependent (s t : Set A) (hst : s subseteq t)
    (hs : AlgebraicIndepOn R id s) : exists u, s subseteq u ∧
      Maximal (fun (x : Set A) => AlgebraicIndepOn R id x ∧ x subseteq t) u := by
  refine zorn_subset_nonempty { u : Set A | AlgebraicIndependent R ((↑) : u -> A) ∧ u subseteq t}
    (fun c hc chainc hcn => ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ => subset_sUnion_of_mem⟩) s ⟨hs, hst⟩
  · exact algebraicIndependent_sUnion_of_directed hcn chainc.directedOn (fun x hxc => (hc hxc).1)
  exact fun x ⟨w, hyc, hwy⟩ => (hc hyc).2 hwy

/--
theorem `AlgebraicIndependent.repr_ker` / 定理 `AlgebraicIndependent.repr_ker`

English:
theorem AlgebraicIndependent.repr_ker
  given: (hx : AlgebraicIndependent R x)
  proof: (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

中文:
定理 AlgebraicIndependent.repr_ker
  条件: (hx : AlgebraicIndependent R x)
  证明: (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

Depends on / 依赖: AlgEquiv, AlgEquiv.injective, RingHom, RingHom.injective_iff_ker_eq_bot, injective, injective_iff_ker_eq_bot
-/
theorem AlgebraicIndependent.repr_ker (hx : AlgebraicIndependent R x) :
    RingHom.ker (hx.repr : adjoin R (range x) ->+* MvPolynomial ι R) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).1 (AlgEquiv.injective _)

-- TODO - make this an `AlgEquiv`
/--
Definition of `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin` / `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin` 的定义

English:
definition AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin
  signature: (hx : AlgebraicIndependent R x)
  body: (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)

@[simp]

中文:
定义 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin
  签名: (hx : AlgebraicIndependent R x)
  定义体: (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.optionEquivLeft, Polynomial, Polynomial.mapEquiv, aevalEquiv, hx.aevalEquiv.toRingEquiv, mapEquiv, optionEquivLeft, toRingEquiv, toRingEquiv.trans
-/
def AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin (hx : AlgebraicIndependent R x) :
    MvPolynomial (Option ι) R ≃+* Polynomial (adjoin R (Set.range x)) :=
  (MvPolynomial.optionEquivLeft _ _).toRingEquiv.trans
    (Polynomial.mapEquiv hx.aevalEquiv.toRingEquiv)

@[simp]
/--
theorem `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply` / 定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply`

English:
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
  proof: rfl

中文:
定理 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
  证明: rfl
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply
    (hx : AlgebraicIndependent R x) (y) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin y =
      Polynomial.map (hx.aevalEquiv : MvPolynomial ι R ->+* adjoin R (range x))
        (aeval (fun o : Option ι => o.elim Polynomial.X fun s : ι => Polynomial.C (X s)) y) :=
  rfl

/-- `simp`-normal form of `mvPolynomialOptionEquivPolynomialAdjoin_C` -/
@[simp]
/--
theorem `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'` / 定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'`

English:
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'
  proof: by
  congr
  apply_fun Subtype.val using Subtype.val_injective
  simp

中文:
定理 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'
  证明: by
  congr
  apply_fun Subtype.val using Subtype.val_injective
  simp

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, apply_fun, val_injective
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C'
    (hx : AlgebraicIndependent R x) (r) :
    Polynomial.C (hx.aevalEquiv (C r)) = Polynomial.C (algebraMap _ _ r) := by
  congr
  apply_fun Subtype.val using Subtype.val_injective
  simp

/--
theorem `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C` / 定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C`

English:
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
  proof: by
  simp

中文:
定理 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
  证明: by
  simp
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_C
    (hx : AlgebraicIndependent R x) (r) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (C r) = Polynomial.C (algebraMap _ _ r) := by
  simp

/--
theorem `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none` / 定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none`

English:
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
  proof: by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_X]

中文:
定理 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
  证明: by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_X]

Depends on / 依赖: AlgebraicIndependent, AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, Option.elim, Polynomial, Polynomial.map_X, aeval_X, map_X, mvPolynomialOptionEquivPolynomialAdjoin_apply
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_none
    (hx : AlgebraicIndependent R x) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X none) = Polynomial.X := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_X]

/--
theorem `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some` / 定理 `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some`

English:
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
  proof: by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_C]; rw [RingHom.coe_coe]

中文:
定理 AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
  证明: by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_C]; rw [RingHom.coe_coe]

Depends on / 依赖: AlgebraicIndependent, AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply, Option.elim, Polynomial, Polynomial.map_C, RingHom, RingHom.coe_coe, aeval_X, coe_coe, map_C, mvPolynomialOptionEquivPolynomialAdjoin_apply
-/
theorem AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_X_some
    (hx : AlgebraicIndependent R x) (i) :
    hx.mvPolynomialOptionEquivPolynomialAdjoin (X (some i)) =
      Polynomial.C (hx.aevalEquiv (X i)) := by
  rw [AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin_apply]; rw [aeval_X]; rw [Option.elim]; rw [Polynomial.map_C]; rw [RingHom.coe_coe]

/--
theorem `AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin` / 定理 `AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin`

English:
theorem AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
  proof: by
  refine MvPolynomial.ringHom_ext ?_ ?_ <;>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
  · intro r
    rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_C]; rw [aeval_C]; rw [Polynomial.aeval_C]; rw [IsSca

中文:
定理 AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
  证明: by
  refine MvPolynomial.ringHom_ext ?_ ?_ <;>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
  · intro r
    rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_C]; rw [aeval_C]; rw [Polynomial.aeval_C]; rw [IsSca

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, IsScalarTower, IsScalarTower.algebraMap_apply, MvPolynomial, MvPolynomial.ringHom_ext, Option.elim, Polynomial, Polynomial.aeval_C, Polynomial.aeval_X, RingEquiv, RingEquiv.coe_toRingHom, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.comp_apply, adjoin, aeval_C, aeval_X, algebraMap_apply, coe_toRingHom
-/
theorem AlgebraicIndependent.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin
    (hx : AlgebraicIndependent R x) (a : A) :
    RingHom.comp
        (↑(Polynomial.aeval a : Polynomial (adjoin R (Set.range x)) ->ₐ[_] A) :
          Polynomial (adjoin R (Set.range x)) ->+* A)
        hx.mvPolynomialOptionEquivPolynomialAdjoin.toRingHom =
      ↑(MvPolynomial.aeval fun o : Option ι => o.elim a x : MvPolynomial (Option ι) R ->ₐ[R] A) := by
  refine MvPolynomial.ringHom_ext ?_ ?_ <;>
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.coe_toRingHom, AlgHom.coe_toRingHom]
  · intro r
    rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_C]; rw [aeval_C]; rw [Polynomial.aeval_C]; rw [IsScalarTower.algebraMap_apply R (adjoin R (range x)) A]
  · rintro (⟨⟩ | ⟨i⟩)
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_none, aeval_X, Polynomial.aeval_X,
        Option.elim]
    · rw [hx.mvPolynomialOptionEquivPolynomialAdjoin_X_some, Polynomial.aeval_C,
        hx.algebraMap_aevalEquiv, aeval_X, aeval_X, Option.elim]

section Field

variable {K : Type*} [Field K] [Algebra K A]

/--
theorem `algebraicIndependent_empty_type` / 定理 `algebraicIndependent_empty_type`

English:
theorem algebraicIndependent_empty_type
  given: [IsEmpty ι] [Nontrivial A]
  statement: AlgebraicIndependent K x
  proof: by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _

中文:
定理 algebraicIndependent_empty_type
  条件: [是空 ι] [非平凡 A]
  结论: AlgebraicIndependent K x
  证明: by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _

Depends on / 依赖: RingHom, RingHom.injective, algebraicIndependent_empty_type_iff, injective
-/
theorem algebraicIndependent_empty_type [IsEmpty ι] [Nontrivial A] : AlgebraicIndependent K x := by
  rw [algebraicIndependent_empty_type_iff]
  exact RingHom.injective _

/--
theorem `algebraicIndependent_empty` / 定理 `algebraicIndependent_empty`

English:
theorem algebraicIndependent_empty
  given: [Nontrivial A]
  proof: algebraicIndependent_empty_type

中文:
定理 algebraicIndependent_empty
  条件: [非平凡 A]
  证明: algebraicIndependent_empty_type

Depends on / 依赖: algebraicIndependent_empty_type
-/
theorem algebraicIndependent_empty [Nontrivial A] :
    AlgebraicIndependent K ((↑) : (∅ : Set A) -> A) :=
  algebraicIndependent_empty_type

end Field
