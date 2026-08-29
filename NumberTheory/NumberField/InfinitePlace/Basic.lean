/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Instances.Complex

/-!
# Infinite places of a number field

This file defines the infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace`: the type of infinite places of a number field `K`.
* `NumberField.InfinitePlace.mk_eq_iff`: two complex embeddings define the same infinite place iff
  they are equal or complex conjugates.
* `NumberField.InfinitePlace.IsReal`: The predicate on infinite places saying
  that a place is real, i.e., defined by a real embedding.
* `NumberField.InfinitePlace.IsComplex`: The predicate on infinite places saying
  that a place is complex, i.e., defined by a complex embedding that is not real.
* `NumberField.InfinitePlace.mult`: the multiplicity of an infinite place, that is the number of
  distinct complex embeddings that define it. So it is equal to `1` if the place is real and `2`
  if the place is complex.
* `NumberField.InfinitePlace.prod_eq_abs_norm`: the infinite part of the product formula, that is
  for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where the product is over the infinite place `w` and
  `‖·‖_w` is the normalized absolute value for `w`.
* `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`: the degree of `K` is equal to the
  number of real places plus twice the number of complex places.
* `NumberField.InfinitePlace.denseRange_algebraMap_pi`: the image of `K` by the diagonal embedding
  into the product of its infinite completions is dense.

## Tags

number field, infinite places
-/

@[expose] public section


open scoped Finset Topology

namespace NumberField

open Fintype Module

variable (K : Type*) [Field K]

/--
Definition of `InfinitePlace` / `InfinitePlace` 的定义

English:
definition InfinitePlace
  body: { w : AbsoluteValue K Real // exists φ : K ->+* Complex, place φ = w }

中文:
定义 InfinitePlace
  定义体: { w : AbsoluteValue K Real // exists φ : K ->+* Complex, place φ = w }

Depends on / 依赖: AbsoluteValue
-/
def InfinitePlace := { w : AbsoluteValue K Real // exists φ : K ->+* Complex, place φ = w }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: (K ->+* Complex)] : Nonempty (InfinitePlace K)
  body: Set.instNonemptyRange _

中文:
实例 [非空
  签名: (K ->+* 复形)] : 非空 (InfinitePlace K)
  定义体: Set.instNonemptyRange _

Depends on / 依赖: Set.instNonemptyRange, instNonemptyRange
-/
instance [Nonempty (K ->+* Complex)] : Nonempty (InfinitePlace K) := Set.instNonemptyRange _

variable {K}

/--
Definition of `InfinitePlace.mk` / `InfinitePlace.mk` 的定义

English:
definition InfinitePlace.mk
  signature: (φ : K ->+* Complex)
  body: ⟨place φ, ⟨φ, rfl⟩⟩

中文:
定义 InfinitePlace.mk
  签名: (φ : K ->+* 复形)
  定义体: ⟨place φ, ⟨φ, rfl⟩⟩
-/
noncomputable def InfinitePlace.mk (φ : K ->+* Complex) : InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩

/--
Definition of `IsInfinitePlace` / `IsInfinitePlace` 的定义

English:
definition IsInfinitePlace
  signature: (w : AbsoluteValue K Real)
  body: exists φ : K ->+* Complex, place φ = w

中文:
定义 IsInfinitePlace
  签名: (w : 绝对值 K 实数)
  定义体: exists φ : K ->+* Complex, place φ = w
-/
def IsInfinitePlace (w : AbsoluteValue K Real) : Prop :=
  exists φ : K ->+* Complex, place φ = w

/--
lemma `InfinitePlace.isInfinitePlace` / 引理 `InfinitePlace.isInfinitePlace`

English:
lemma InfinitePlace.isInfinitePlace
  given: (v : InfinitePlace K)
  statement: IsInfinitePlace v.val
  proof: by
  simp [IsInfinitePlace, v.prop]

中文:
引理 InfinitePlace.isInfinitePlace
  条件: (v : InfinitePlace K)
  结论: IsInfinitePlace v.val
  证明: by
  simp [IsInfinitePlace, v.prop]

Depends on / 依赖: IsInfinitePlace, v.prop
-/
lemma InfinitePlace.isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]

/--
lemma `isInfinitePlace_iff` / 引理 `isInfinitePlace_iff`

English:
lemma isInfinitePlace_iff
  given: (v : AbsoluteValue K Real)
  proof: ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isInfinitePlace⟩

中文:
引理 isInfinitePlace_iff
  条件: (v : 绝对值 K 实数)
  证明: ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isInfinitePlace⟩

Depends on / 依赖: isInfinitePlace, w.isInfinitePlace
-/
lemma isInfinitePlace_iff (v : AbsoluteValue K Real) :
    IsInfinitePlace v ↔ exists w : InfinitePlace K, w.val = v :=
  ⟨fun H => ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.isInfinitePlace⟩

namespace InfinitePlace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (InfinitePlace K) K Real
  body: w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext fun x => congr_fun h x)

中文:
实例 :
  签名: 函数状 (InfinitePlace K) K 实数
  定义体: w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext fun x => congr_fun h x)
-/
instance : FunLike (InfinitePlace K) K Real where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext fun x => congr_fun h x)

/--
lemma `coe_apply` / 引理 `coe_apply`

English:
lemma coe_apply
  given: (v : InfinitePlace K) (x : K)
  statement: v x = v.1 x
  proof: rfl

@[ext]

中文:
引理 coe_apply
  条件: (v : InfinitePlace K) (x : K)
  结论: v x = v.1 x
  证明: rfl

@[ext]
-/
lemma coe_apply (v : InfinitePlace K) (x : K) : v x = v.1 x := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (v₁ v₂ : InfinitePlace K) (h : forall k, v₁ k = v₂ k)
  statement: v₁ = v₂
  proof: Subtype.ext AbsoluteValue.ext h

中文:
引理 ext
  条件: (v₁ v₂ : InfinitePlace K) (h : 对任意 k, v₁ k = v₂ k)
  结论: v₁ = v₂
  证明: Subtype.ext AbsoluteValue.ext h

Depends on / 依赖: AbsoluteValue, AbsoluteValue.ext, Subtype, Subtype.ext
-/
lemma ext (v₁ v₂ : InfinitePlace K) (h : forall k, v₁ k = v₂ k) : v₁ = v₂ :=
Subtype.ext AbsoluteValue.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZeroHomClass (InfinitePlace K) K Real
  body: w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

中文:
实例 :
  签名: 带零幺半群态射类 (InfinitePlace K) K 实数
  定义体: w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

Depends on / 依赖: map_mul
-/
instance : MonoidWithZeroHomClass (InfinitePlace K) K Real where
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonnegHomClass (InfinitePlace K) K Real
  body: w.1.nonneg _

@[simp]

中文:
实例 :
  签名: Nonneg态射类 (InfinitePlace K) K 实数
  定义体: w.1.nonneg _

@[simp]

Depends on / 依赖: nonneg
-/
instance : NonnegHomClass (InfinitePlace K) K Real where
  apply_nonneg w _ := w.1.nonneg _

@[simp]
/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: (φ : K ->+* Complex) (x : K)
  statement: (mk φ) x = ‖φ x‖
  proof: rfl

中文:
定理 apply
  条件: (φ : K ->+* 复形) (x : K)
  结论: (mk φ) x = ‖φ x‖
  证明: rfl
-/
theorem apply (φ : K ->+* Complex) (x : K) : (mk φ) x = ‖φ x‖ := rfl

/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: (w : InfinitePlace K)
  body: w.2.choose

@[simp]

中文:
定义 embedding
  签名: (w : InfinitePlace K)
  定义体: w.2.choose

@[simp]
-/
noncomputable def embedding (w : InfinitePlace K) : K ->+* Complex := w.2.choose

@[simp]
/--
theorem `mk_embedding` / 定理 `mk_embedding`

English:
theorem mk_embedding
  given: (w : InfinitePlace K)
  statement: mk (embedding w) = w
  proof: Subtype.ext w.2.choose_spec

@[simp]

中文:
定理 mk_embedding
  条件: (w : InfinitePlace K)
  结论: mk (embedding w) = w
  证明: Subtype.ext w.2.choose_spec

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, choose_spec
-/
theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w := Subtype.ext w.2.choose_spec

@[simp]
/--
theorem `mk_conjugate_eq` / 定理 `mk_conjugate_eq`

English:
theorem mk_conjugate_eq
  given: (φ : K ->+* Complex)
  statement: mk (ComplexEmbedding.conjugate φ) = mk φ
  proof: by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [apply]; rw [apply]; rw [ComplexEmbedding.conjugate_coe_eq]; rw [Complex.norm_conj]

中文:
定理 mk_conjugate_eq
  条件: (φ : K ->+* 复形)
  结论: mk (ComplexEmbedding.conjugate φ) = mk φ
  证明: by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [apply]; rw [apply]; rw [ComplexEmbedding.conjugate_coe_eq]; rw [Complex.norm_conj]

Depends on / 依赖: Complex.norm_conj, ComplexEmbedding, ComplexEmbedding.conjugate_coe_eq, DFunLike, DFunLike.ext, conjugate_coe_eq, norm_conj
-/
theorem mk_conjugate_eq (φ : K ->+* Complex) : mk (ComplexEmbedding.conjugate φ) = mk φ := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [apply]; rw [apply]; rw [ComplexEmbedding.conjugate_coe_eq]; rw [Complex.norm_conj]

/--
theorem `norm_embedding_eq` / 定理 `norm_embedding_eq`

English:
theorem norm_embedding_eq
  given: (w : InfinitePlace K) (x : K)
  proof: by
  nth_rewrite 2 [← mk_embedding w]
  rfl

中文:
定理 norm_embedding_eq
  条件: (w : InfinitePlace K) (x : K)
  证明: by
  nth_rewrite 2 [← mk_embedding w]
  rfl

Depends on / 依赖: mk_embedding, nth_rewrite
-/
theorem norm_embedding_eq (w : InfinitePlace K) (x : K) :
    ‖(embedding w) x‖ = w x := by
  nth_rewrite 2 [← mk_embedding w]
  rfl

variable (K) in
/--
theorem `embedding_injective` / 定理 `embedding_injective`

English:
theorem embedding_injective
  statement: (embedding (K := K)).Injective
  proof: fun _ _ h => by simpa using congr_arg mk h

@[simp]

中文:
定理 embedding_injective
  结论: (embedding (K := K)).单射
  证明: fun _ _ h => by simpa using congr_arg mk h

@[simp]

Depends on / 依赖: Injective
-/
theorem embedding_injective : (embedding (K := K)).Injective :=
  fun _ _ h => by simpa using congr_arg mk h

@[simp]
/--
theorem `embedding_inj` / 定理 `embedding_inj`

English:
theorem embedding_inj
  given: {v₁ v₂ : InfinitePlace K}
  statement: v₁.embedding = v₂.embedding ↔ v₁ = v₂
  proof: (embedding_injective _).eq_iff

中文:
定理 embedding_inj
  条件: {v₁ v₂ : InfinitePlace K}
  结论: v₁.embedding = v₂.embedding ↔ v₁ = v₂
  证明: (embedding_injective _).eq_iff

Depends on / 依赖: embedding_injective, eq_iff
-/
theorem embedding_inj {v₁ v₂ : InfinitePlace K} : v₁.embedding = v₂.embedding ↔ v₁ = v₂ :=
  (embedding_injective _).eq_iff

variable (K) in
/--
theorem `conjugate_embedding_injective` / 定理 `conjugate_embedding_injective`

English:
theorem conjugate_embedding_injective
  proof: star_injective.comp embedding_injective K

中文:
定理 conjugate_embedding_injective
  证明: star_injective.comp embedding_injective K

Depends on / 依赖: embedding_injective, star_injective, star_injective.comp
-/
theorem conjugate_embedding_injective :
    (fun (v : InfinitePlace K) => ComplexEmbedding.conjugate v.embedding).Injective :=
star_injective.comp embedding_injective K

variable (K) in
/--
theorem `eq_of_embedding_eq_conjugate` / 定理 `eq_of_embedding_eq_conjugate`

English:
theorem eq_of_embedding_eq_conjugate
  statement: {v₁ v₂ : InfinitePlace K}
  proof: by
  rw [← mk_embedding v₁]; rw [h]; rw [mk_conjugate_eq]; rw [mk_embedding]

中文:
定理 eq_of_embedding_eq_conjugate
  结论: {v₁ v₂ : InfinitePlace K}
  证明: by
  rw [← mk_embedding v₁]; rw [h]; rw [mk_conjugate_eq]; rw [mk_embedding]

Depends on / 依赖: mk_conjugate_eq, mk_embedding
-/
theorem eq_of_embedding_eq_conjugate {v₁ v₂ : InfinitePlace K}
    (h : v₁.embedding = ComplexEmbedding.conjugate v₂.embedding) : v₁ = v₂ := by
  rw [← mk_embedding v₁]; rw [h]; rw [mk_conjugate_eq]; rw [mk_embedding]

/--
theorem `eq_iff_eq` / 定理 `eq_iff_eq`

English:
theorem eq_iff_eq
  given: (x : K) (r : Real)
  statement: (forall w : InfinitePlace K, w x = r) ↔ forall φ : K ->+* Complex, ‖φ x‖ = r
  proof: ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

中文:
定理 eq_iff_eq
  条件: (x : K) (r : 实数)
  结论: (对任意 w : InfinitePlace K, w x = r) ↔ 对任意 φ : K ->+* 复形, ‖φ x‖ = r
  证明: ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
-/
theorem eq_iff_eq (x : K) (r : Real) : (forall w : InfinitePlace K, w x = r) ↔ forall φ : K ->+* Complex, ‖φ x‖ = r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: (x : K) (r : Real)
  statement: (forall w : InfinitePlace K, w x <= r) ↔ forall φ : K ->+* Complex, ‖φ x‖ <= r
  proof: ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

中文:
定理 le_iff_le
  条件: (x : K) (r : 实数)
  结论: (对任意 w : InfinitePlace K, w x <= r) ↔ 对任意 φ : K ->+* 复形, ‖φ x‖ <= r
  证明: ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
-/
theorem le_iff_le (x : K) (r : Real) : (forall w : InfinitePlace K, w x <= r) ↔ forall φ : K ->+* Complex, ‖φ x‖ <= r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  given: {w : InfinitePlace K} {x : K}
  statement: 0 < w x ↔ x != 0
  proof: AbsoluteValue.pos_iff w.1

@[simp]

中文:
定理 pos_iff
  条件: {w : InfinitePlace K} {x : K}
  结论: 0 < w x ↔ x != 0
  证明: AbsoluteValue.pos_iff w.1

@[simp]

Depends on / 依赖: AbsoluteValue, AbsoluteValue.pos_iff, pos_iff
-/
theorem pos_iff {w : InfinitePlace K} {x : K} : 0 < w x ↔ x != 0 := AbsoluteValue.pos_iff w.1

@[simp]
/--
theorem `mk_eq_iff` / 定理 `mk_eq_iff`

English:
theorem mk_eq_iff
  given: {φ ψ : K ->+* Complex}
  statement: mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
  proof: by
  constructor
  · -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using `Complex.uniformContinuous_ringHom_eq_id_or_conj`
    intro h₀
    obtain ⟨j, hiφ⟩ := (φ.injective).hasLeftInverse
    let ι := RingEquiv.ofLeftInverse hiφ
    have hlip : LipschitzWith 1 (RingHom.comp ψ ι.symm.toRingHom) := by
      change LipschitzWith 1 (ψ ∘ ι.symm)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← map_sub]; rw [← map_sub]
      apply le_of_eq
      suffices ‖φ (ι.symm (x - y))‖ = ‖ψ (ι.symm (x - y))‖ by
        rw [← this]; rw [← RingEquiv.ofLeftInverse_apply hiφ _]; rw [RingEquiv.apply_symm_apply ι _]; rw [dist_eq_norm]
        rfl
      exact congrFun (congrArg (↑) h₀) _
    cases
      Complex.uniformContinuous_ringHom_eq_id_or_conj φ.fieldRange hlip.uniformContinuous with
    | inl h =>
        left; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
    | inr h =>
        right; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
  · rintro (⟨h⟩ | ⟨h⟩)
    · exact congr_arg mk h
    · rw [← mk_conjugate_eq]
      exact congr_arg mk h

中文:
定理 mk_eq_iff
  条件: {φ ψ : K ->+* 复形}
  结论: mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
  证明: by
  constructor
  · -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using `Complex.uniformContinuous_ringHom_eq_id_or_conj`
    intro h₀
    obtain ⟨j, hiφ⟩ := (φ.injective).hasLeftInverse
    let ι := RingEquiv.ofLeftInverse hiφ
    have hlip : LipschitzWith 1 (RingHom.comp ψ ι.symm.toRingHom) := by
      change LipschitzWith 1 (ψ ∘ ι.symm)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← map_sub]; rw [← map_sub]
      apply le_of_eq
      suffices ‖φ (ι.symm (x - y))‖ = ‖ψ (ι.symm (x - y))‖ by
        rw [← this]; rw [← RingEquiv.ofLeftInverse_apply hiφ _]; rw [RingEquiv.apply_symm_apply ι _]; rw [dist_eq_norm]
        rfl
      exact congrFun (congrArg (↑) h₀) _
    cases
      Complex.uniformContinuous_ringHom_eq_id_or_conj φ.fieldRange hlip.uniformContinuous with
    | inl h =>
        left; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
    | inr h =>
        right; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
  · rintro (⟨h⟩ | ⟨h⟩)
    · exact congr_arg mk h
    · rw [← mk_conjugate_eq]
      exact congr_arg mk h

Depends on / 依赖: between, continuous, either, uniform
-/
theorem mk_eq_iff {φ ψ : K ->+* Complex} : mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ := by
  constructor
  · -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using `Complex.uniformContinuous_ringHom_eq_id_or_conj`
    intro h₀
    obtain ⟨j, hiφ⟩ := (φ.injective).hasLeftInverse
    let ι := RingEquiv.ofLeftInverse hiφ
    have hlip : LipschitzWith 1 (RingHom.comp ψ ι.symm.toRingHom) := by
      change LipschitzWith 1 (ψ ∘ ι.symm)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [Function.comp_apply]; rw [Function.comp_apply]; rw [← map_sub]; rw [← map_sub]
      apply le_of_eq
      suffices ‖φ (ι.symm (x - y))‖ = ‖ψ (ι.symm (x - y))‖ by
        rw [← this]; rw [← RingEquiv.ofLeftInverse_apply hiφ _]; rw [RingEquiv.apply_symm_apply ι _]; rw [dist_eq_norm]
        rfl
      exact congrFun (congrArg (↑) h₀) _
    cases
      Complex.uniformContinuous_ringHom_eq_id_or_conj φ.fieldRange hlip.uniformContinuous with
    | inl h =>
        left; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
    | inr h =>
        right; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
  · rintro (⟨h⟩ | ⟨h⟩)
    · exact congr_arg mk h
    · rw [← mk_conjugate_eq]
      exact congr_arg mk h

/--
Definition of `LiesOver` / `LiesOver` 的定义

English:
abbreviation LiesOver
  signature: {L : Type*} [Field L] [Algebra K L]
  body: w.val.LiesOver v.val

中文:
缩写 LiesOver
  签名: {L : 类型} [域 L] [代数 K L]
  定义体: w.val.LiesOver v.val
-/
protected abbrev LiesOver {L : Type*} [Field L] [Algebra K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :=
  w.val.LiesOver v.val

/--
Definition of `IsReal` / `IsReal` 的定义

English:
definition IsReal
  signature: (w : InfinitePlace K)
  body: exists φ : K ->+* Complex, ComplexEmbedding.IsReal φ ∧ mk φ = w

中文:
定义 Is实数
  签名: (w : InfinitePlace K)
  定义体: exists φ : K ->+* Complex, ComplexEmbedding.IsReal φ ∧ mk φ = w

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, IsReal
-/
def IsReal (w : InfinitePlace K) : Prop := exists φ : K ->+* Complex, ComplexEmbedding.IsReal φ ∧ mk φ = w

/--
Definition of `IsComplex` / `IsComplex` 的定义

English:
definition IsComplex
  signature: (w : InfinitePlace K)
  body: exists φ : K ->+* Complex, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w

中文:
定义 是复形
  签名: (w : InfinitePlace K)
  定义体: exists φ : K ->+* Complex, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, IsReal
-/
def IsComplex (w : InfinitePlace K) : Prop := exists φ : K ->+* Complex, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w

/--
theorem `embedding_mk_eq` / 定理 `embedding_mk_eq`

English:
theorem embedding_mk_eq
  given: (φ : K ->+* Complex)
  proof: by
  rw [@eq_comm _ _ φ]; rw [@eq_comm _ _ (ComplexEmbedding.conjugate φ)]; rw [← mk_eq_iff]; rw [mk_embedding]

@[simp]

中文:
定理 embedding_mk_eq
  条件: (φ : K ->+* 复形)
  证明: by
  rw [@eq_comm _ _ φ]; rw [@eq_comm _ _ (ComplexEmbedding.conjugate φ)]; rw [← mk_eq_iff]; rw [mk_embedding]

@[simp]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.conjugate, conjugate, eq_comm, mk_embedding, mk_eq_iff
-/
theorem embedding_mk_eq (φ : K ->+* Complex) :
    embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ := by
  rw [@eq_comm _ _ φ]; rw [@eq_comm _ _ (ComplexEmbedding.conjugate φ)]; rw [← mk_eq_iff]; rw [mk_embedding]

@[simp]
/--
theorem `embedding_mk_eq_of_isReal` / 定理 `embedding_mk_eq_of_isReal`

English:
theorem embedding_mk_eq_of_isReal
  given: {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ)
  proof: by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this

中文:
定理 embedding_mk_eq_of_is实数
  条件: {φ : K ->+* 复形} (h : ComplexEmbedding.Is实数 φ)
  证明: by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff.mp, embedding_mk_eq, isReal_iff, or_self
-/
theorem embedding_mk_eq_of_isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) :
    embedding (mk φ) = φ := by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this

/--
theorem `isReal_iff` / 定理 `isReal_iff`

English:
theorem isReal_iff
  given: {w : InfinitePlace K}
  proof: by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]

中文:
定理 is实数_iff
  条件: {w : InfinitePlace K}
  证明: by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]

Depends on / 依赖: embedding, embedding_mk_eq_of_isReal, mk_embedding
-/
theorem isReal_iff {w : InfinitePlace K} :
    IsReal w ↔ ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]

/--
theorem `isComplex_iff` / 定理 `isComplex_iff`

English:
theorem isComplex_iff
  given: {w : InfinitePlace K}
  proof: by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ

@[simp]

中文:
定理 isComplex_iff
  条件: {w : InfinitePlace K}
  证明: by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ

@[simp]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_conjugate_iff, contrapose, embedding, isReal_conjugate_iff, mk_embedding, mk_eq_iff, mk_eq_iff.mp
-/
theorem isComplex_iff {w : InfinitePlace K} :
    IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ

@[simp]
/--
theorem `conjugate_embedding_eq_of_isReal` / 定理 `conjugate_embedding_eq_of_isReal`

English:
theorem conjugate_embedding_eq_of_isReal
  given: {w : InfinitePlace K} (h : IsReal w)
  proof: ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]

中文:
定理 conjugate_embedding_eq_of_is实数
  条件: {w : InfinitePlace K} (h : Is实数 w)
  证明: ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff.mpr, isReal_iff, isReal_iff.mp
-/
theorem conjugate_embedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) :
    ComplexEmbedding.conjugate (embedding w) = embedding w :=
  ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]
/--
theorem `not_isReal_iff_isComplex` / 定理 `not_isReal_iff_isComplex`

English:
theorem not_isReal_iff_isComplex
  given: {w : InfinitePlace K}
  statement: ¬IsReal w ↔ IsComplex w
  proof: by
  rw [isComplex_iff]; rw [isReal_iff]

@[simp]

中文:
定理 not_is实数_iff_isComplex
  条件: {w : InfinitePlace K}
  结论: ¬Is实数 w ↔ 是复形 w
  证明: by
  rw [isComplex_iff]; rw [isReal_iff]

@[simp]

Depends on / 依赖: isComplex_iff, isReal_iff
-/
theorem not_isReal_iff_isComplex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w := by
  rw [isComplex_iff]; rw [isReal_iff]

@[simp]
/--
theorem `not_isComplex_iff_isReal` / 定理 `not_isComplex_iff_isReal`

English:
theorem not_isComplex_iff_isReal
  given: {w : InfinitePlace K}
  statement: ¬IsComplex w ↔ IsReal w
  proof: by
  rw [isComplex_iff]; rw [isReal_iff]; rw [not_not]

中文:
定理 not_isComplex_iff_is实数
  条件: {w : InfinitePlace K}
  结论: ¬是复形 w ↔ Is实数 w
  证明: by
  rw [isComplex_iff]; rw [isReal_iff]; rw [not_not]

Depends on / 依赖: isComplex_iff, isReal_iff, not_not
-/
theorem not_isComplex_iff_isReal {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w := by
  rw [isComplex_iff]; rw [isReal_iff]; rw [not_not]

/--
theorem `isReal_or_isComplex` / 定理 `isReal_or_isComplex`

English:
theorem isReal_or_isComplex
  given: (w : InfinitePlace K)
  statement: IsReal w ∨ IsComplex w
  proof: by
  rw [← not_isReal_iff_isComplex]; exact em _

中文:
定理 is实数_or_isComplex
  条件: (w : InfinitePlace K)
  结论: Is实数 w ∨ 是复形 w
  证明: by
  rw [← not_isReal_iff_isComplex]; exact em _

Depends on / 依赖: not_isReal_iff_isComplex
-/
theorem isReal_or_isComplex (w : InfinitePlace K) : IsReal w ∨ IsComplex w := by
  rw [← not_isReal_iff_isComplex]; exact em _

/--
theorem `ne_of_isReal_isComplex` / 定理 `ne_of_isReal_isComplex`

English:
theorem ne_of_isReal_isComplex
  given: {w w' : InfinitePlace K} (h : IsReal w) (h' : IsComplex w')
  proof: fun h_eq => not_isReal_iff_isComplex.mpr h' (h_eq ▸ h)

中文:
定理 ne_of_is实数_isComplex
  条件: {w w' : InfinitePlace K} (h : Is实数 w) (h' : 是复形 w')
  证明: fun h_eq => not_isReal_iff_isComplex.mpr h' (h_eq ▸ h)

Depends on / 依赖: h_eq, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr
-/
theorem ne_of_isReal_isComplex {w w' : InfinitePlace K} (h : IsReal w) (h' : IsComplex w') :
    w != w' := fun h_eq => not_isReal_iff_isComplex.mpr h' (h_eq ▸ h)

variable (K) in
/--
theorem `disjoint_isReal_isComplex` / 定理 `disjoint_isReal_isComplex`

English:
theorem disjoint_isReal_isComplex
  proof: Set.disjoint_iff.2 fun _ hw => not_isReal_iff_isComplex.2 hw.2 hw.1

中文:
定理 disjoint_is实数_isComplex
  证明: Set.disjoint_iff.2 fun _ hw => not_isReal_iff_isComplex.2 hw.2 hw.1

Depends on / 依赖: Set.disjoint_iff, disjoint_iff, not_isReal_iff_isComplex
-/
theorem disjoint_isReal_isComplex :
    Disjoint {(w : InfinitePlace K) | IsReal w} {(w : InfinitePlace K) | IsComplex w} :=
Set.disjoint_iff.2 fun _ hw => not_isReal_iff_isComplex.2 hw.2 hw.1

/--
Definition of `embedding_of_isReal` / `embedding_of_isReal` 的定义

English:
definition embedding_of_isReal
  signature: {w : InfinitePlace K} (hw : IsReal w)
  body: ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)

@[simp]

中文:
定义 embedding_of_is实数
  签名: {w : InfinitePlace K} (hw : Is实数 w)
  定义体: ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)

@[simp]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal.embedding, IsReal, embedding, isReal_iff, isReal_iff.mp
-/
noncomputable def embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) : K ->+* Real :=
  ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)

@[simp]
/--
theorem `embedding_of_isReal_apply` / 定理 `embedding_of_isReal_apply`

English:
theorem embedding_of_isReal_apply
  given: {w : InfinitePlace K} (hw : IsReal w) (x : K)
  proof: ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x

中文:
定理 embedding_of_is实数_apply
  条件: {w : InfinitePlace K} (hw : Is实数 w) (x : K)
  证明: ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal.coe_embedding_apply, IsReal, coe_embedding_apply, isReal_iff, isReal_iff.mp
-/
theorem embedding_of_isReal_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ((embedding_of_isReal hw) x : Complex) = (embedding w) x :=
  ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x

/--
theorem `norm_embedding_of_isReal` / 定理 `norm_embedding_of_isReal`

English:
theorem norm_embedding_of_isReal
  given: {w : InfinitePlace K} (hw : IsReal w) (x : K)
  proof: by
  rw [← norm_embedding_eq]; rw [← embedding_of_isReal_apply hw]; rw [Complex.norm_real]

@[simp]

中文:
定理 norm_embedding_of_is实数
  条件: {w : InfinitePlace K} (hw : Is实数 w) (x : K)
  证明: by
  rw [← norm_embedding_eq]; rw [← embedding_of_isReal_apply hw]; rw [Complex.norm_real]

@[simp]

Depends on / 依赖: Complex.norm_real, embedding_of_isReal_apply, norm_embedding_eq, norm_real
-/
theorem norm_embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ‖embedding_of_isReal hw x‖ = w x := by
  rw [← norm_embedding_eq]; rw [← embedding_of_isReal_apply hw]; rw [Complex.norm_real]

@[simp]
/--
theorem `isReal_of_mk_isReal` / 定理 `isReal_of_mk_isReal`

English:
theorem isReal_of_mk_isReal
  given: {φ : K ->+* Complex} (h : IsReal (mk φ))
  proof: by
  contrapose h
  rw [not_isReal_iff_isComplex]
  exact ⟨φ, h, rfl⟩

中文:
定理 is实数_of_mk_is实数
  条件: {φ : K ->+* 复形} (h : Is实数 (mk φ))
  证明: by
  contrapose h
  rw [not_isReal_iff_isComplex]
  exact ⟨φ, h, rfl⟩

Depends on / 依赖: contrapose, not_isReal_iff_isComplex
-/
theorem isReal_of_mk_isReal {φ : K ->+* Complex} (h : IsReal (mk φ)) :
    ComplexEmbedding.IsReal φ := by
  contrapose h
  rw [not_isReal_iff_isComplex]
  exact ⟨φ, h, rfl⟩

/--
lemma `isReal_mk_iff` / 引理 `isReal_mk_iff`

English:
lemma isReal_mk_iff
  given: {φ : K ->+* Complex}
  proof: ⟨isReal_of_mk_isReal, fun H => ⟨_, H, rfl⟩⟩

中文:
引理 is实数_mk_iff
  条件: {φ : K ->+* 复形}
  证明: ⟨isReal_of_mk_isReal, fun H => ⟨_, H, rfl⟩⟩

Depends on / 依赖: isReal_of_mk_isReal
-/
lemma isReal_mk_iff {φ : K ->+* Complex} :
    IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ :=
  ⟨isReal_of_mk_isReal, fun H => ⟨_, H, rfl⟩⟩

/--
lemma `isComplex_mk_iff` / 引理 `isComplex_mk_iff`

English:
lemma isComplex_mk_iff
  given: {φ : K ->+* Complex}
  proof: not_isReal_iff_isComplex.symm.trans isReal_mk_iff.not

@[simp]

中文:
引理 isComplex_mk_iff
  条件: {φ : K ->+* 复形}
  证明: not_isReal_iff_isComplex.symm.trans isReal_mk_iff.not

@[simp]

Depends on / 依赖: isReal_mk_iff, isReal_mk_iff.not, not_isReal_iff_isComplex, not_isReal_iff_isComplex.symm.trans
-/
lemma isComplex_mk_iff {φ : K ->+* Complex} :
    IsComplex (mk φ) ↔ ¬ ComplexEmbedding.IsReal φ :=
  not_isReal_iff_isComplex.symm.trans isReal_mk_iff.not

@[simp]
/--
theorem `not_isReal_of_mk_isComplex` / 定理 `not_isReal_of_mk_isComplex`

English:
theorem not_isReal_of_mk_isComplex
  given: {φ : K ->+* Complex} (h : IsComplex (mk φ))
  proof: by rwa [← isComplex_mk_iff]

中文:
定理 not_is实数_of_mk_isComplex
  条件: {φ : K ->+* 复形} (h : 是复形 (mk φ))
  证明: by rwa [← isComplex_mk_iff]

Depends on / 依赖: isComplex_mk_iff
-/
theorem not_isReal_of_mk_isComplex {φ : K ->+* Complex} (h : IsComplex (mk φ)) :
    ¬ ComplexEmbedding.IsReal φ := by rwa [← isComplex_mk_iff]

open scoped Classical in
/--
Definition of `mult` / `mult` 的定义

English:
definition mult
  signature: (w : InfinitePlace K)
  body: if (IsReal w) then 1 else 2

中文:
定义 mult
  签名: (w : InfinitePlace K)
  定义体: if (IsReal w) then 1 else 2

Depends on / 依赖: IsReal
-/
noncomputable def mult (w : InfinitePlace K) : Nat := if (IsReal w) then 1 else 2

/--
theorem `IsReal.mult_eq_one` / 定理 `IsReal.mult_eq_one`

English:
theorem IsReal.mult_eq_one
  given: {w : InfinitePlace K} (hw : IsReal w)
  statement: mult w = 1
  proof: if_pos hw

中文:
定理 Is实数.mult_eq_one
  条件: {w : InfinitePlace K} (hw : Is实数 w)
  结论: mult w = 1
  证明: if_pos hw

Depends on / 依赖: if_pos
-/
theorem IsReal.mult_eq_one {w : InfinitePlace K} (hw : IsReal w) : mult w = 1 :=
  if_pos hw

/--
theorem `IsComplex.mult_eq_two` / 定理 `IsComplex.mult_eq_two`

English:
theorem IsComplex.mult_eq_two
  given: {w : InfinitePlace K} (hw : IsComplex w)
  statement: mult w = 2
  proof: if_neg (not_isReal_iff_isComplex.mpr hw)

@[simp]

中文:
定理 是复形.mult_eq_two
  条件: {w : InfinitePlace K} (hw : 是复形 w)
  结论: mult w = 2
  证明: if_neg (not_isReal_iff_isComplex.mpr hw)

@[simp]

Depends on / 依赖: if_neg, not_isReal_iff_isComplex, not_isReal_iff_isComplex.mpr
-/
theorem IsComplex.mult_eq_two {w : InfinitePlace K} (hw : IsComplex w) : mult w = 2 :=
  if_neg (not_isReal_iff_isComplex.mpr hw)

@[simp]
/--
theorem `mult_isReal` / 定理 `mult_isReal`

English:
theorem mult_isReal
  given: (w : {w : InfinitePlace K // IsReal w})
  proof: w.2.mult_eq_one

@[simp]

中文:
定理 mult_is实数
  条件: (w : {w : InfinitePlace K // Is实数 w})
  证明: w.2.mult_eq_one

@[simp]

Depends on / 依赖: mult_eq_one
-/
theorem mult_isReal (w : {w : InfinitePlace K // IsReal w}) :
    mult w.1 = 1 :=
  w.2.mult_eq_one

@[simp]
/--
theorem `mult_isComplex` / 定理 `mult_isComplex`

English:
theorem mult_isComplex
  given: (w : {w : InfinitePlace K // IsComplex w})
  proof: w.2.mult_eq_two

中文:
定理 mult_isComplex
  条件: (w : {w : InfinitePlace K // 是复形 w})
  证明: w.2.mult_eq_two

Depends on / 依赖: mult_eq_two
-/
theorem mult_isComplex (w : {w : InfinitePlace K // IsComplex w}) :
    mult w.1 = 2 :=
  w.2.mult_eq_two

/--
theorem `mult_pos` / 定理 `mult_pos`

English:
theorem mult_pos
  given: {w : InfinitePlace K}
  statement: 0 < mult w
  proof: by
  rw [mult]
  split_ifs <;> norm_num

@[simp]

中文:
定理 mult_pos
  条件: {w : InfinitePlace K}
  结论: 0 < mult w
  证明: by
  rw [mult]
  split_ifs <;> norm_num

@[simp]

Depends on / 依赖: split_ifs
-/
theorem mult_pos {w : InfinitePlace K} : 0 < mult w := by
  rw [mult]
  split_ifs <;> norm_num

@[simp]
/--
theorem `mult_ne_zero` / 定理 `mult_ne_zero`

English:
theorem mult_ne_zero
  given: {w : InfinitePlace K}
  statement: mult w != 0
  proof: ne_of_gt mult_pos

中文:
定理 mult_ne_zero
  条件: {w : InfinitePlace K}
  结论: mult w != 0
  证明: ne_of_gt mult_pos

Depends on / 依赖: mult_pos, ne_of_gt
-/
theorem mult_ne_zero {w : InfinitePlace K} : mult w != 0 := ne_of_gt mult_pos

/--
theorem `mult_coe_ne_zero` / 定理 `mult_coe_ne_zero`

English:
theorem mult_coe_ne_zero
  given: {w : InfinitePlace K}
  statement: (mult w : Real) != 0
  proof: Nat.cast_ne_zero.mpr mult_ne_zero

中文:
定理 mult_coe_ne_zero
  条件: {w : InfinitePlace K}
  结论: (mult w : 实数) != 0
  证明: Nat.cast_ne_zero.mpr mult_ne_zero

Depends on / 依赖: Nat.cast_ne_zero.mpr, cast_ne_zero, mult_ne_zero
-/
theorem mult_coe_ne_zero {w : InfinitePlace K} : (mult w : Real) != 0 :=
  Nat.cast_ne_zero.mpr mult_ne_zero

/--
theorem `one_le_mult` / 定理 `one_le_mult`

English:
theorem one_le_mult
  given: {w : InfinitePlace K}
  statement: (1 : Real) <= mult w
  proof: by
  rw [← Nat.cast_one]; rw [Nat.cast_le]
  exact mult_pos

中文:
定理 one_le_mult
  条件: {w : InfinitePlace K}
  结论: (1 : 实数) <= mult w
  证明: by
  rw [← Nat.cast_one]; rw [Nat.cast_le]
  exact mult_pos

Depends on / 依赖: Nat.cast_le, Nat.cast_one, cast_le, cast_one, mult_pos
-/
theorem one_le_mult {w : InfinitePlace K} : (1 : Real) <= mult w := by
  rw [← Nat.cast_one]; rw [Nat.cast_le]
  exact mult_pos

open scoped Classical in
/--
theorem `card_filter_mk_eq` / 定理 `card_filter_mk_eq`

English:
theorem card_filter_mk_eq
  given: [NumberField K] (w : InfinitePlace K)
  statement: #{φ | mk φ = w} = mult w
  proof: by
  conv_lhs =>
    congr; congr; ext
    rw [← mk_embedding w]; rw [mk_eq_iff]; rw [ComplexEmbedding.conjugate]; rw [star_involutive.eq_iff]
  simp_rw [Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w)),
    Finset.mem_univ, ite_true, mult]
  split_ifs with hw
  · rw [ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw), Finset.union_idempotent,
      Finset.card_singleton]
  · refine Finset.card_pair ?_
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

中文:
定理 card_filter_mk_eq
  条件: [数域 K] (w : InfinitePlace K)
  结论: #{φ | mk φ = w} = mult w
  证明: by
  conv_lhs =>
    congr; congr; ext
    rw [← mk_embedding w]; rw [mk_eq_iff]; rw [ComplexEmbedding.conjugate]; rw [star_involutive.eq_iff]
  simp_rw [Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w)),
    Finset.mem_univ, ite_true, mult]
  split_ifs with hw
  · rw [ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw), Finset.union_idempotent,
      Finset.card_singleton]
  · refine Finset.card_pair ?_
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.conjugate, ComplexEmbedding.isReal_iff, ComplexEmbedding.isReal_iff.mp, Finset, Finset.card_pair, Finset.card_singleton, Finset.filter_eq, Finset.filter_or, Finset.mem_univ, Finset.union_idempotent, card_pair, card_singleton, conjugate, conv_lhs, embedding, eq_comm, eq_iff, filter_eq, filter_or
-/
theorem card_filter_mk_eq [NumberField K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w := by
  conv_lhs =>
    congr; congr; ext
    rw [← mk_embedding w]; rw [mk_eq_iff]; rw [ComplexEmbedding.conjugate]; rw [star_involutive.eq_iff]
  simp_rw [Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w)),
    Finset.mem_univ, ite_true, mult]
  split_ifs with hw
  · rw [ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw), Finset.union_idempotent,
      Finset.card_singleton]
  · refine Finset.card_pair ?_
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

open scoped Classical in
/--
Instance `noncomputable` / 实例 `noncomputable`

English:
instance noncomputable
  signature: instance fintype [NumberField K]
  body: Set.fintypeRange _

中文:
实例 noncomputable
  签名: instance fintype [数域 K]
  定义体: Set.fintypeRange _
-/
protected noncomputable instance fintype [NumberField K] :
    Fintype (InfinitePlace K) := Set.fintypeRange _

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias NumberField.InfinitePlace.fintype := InfinitePlace.fintype

open scoped Classical in
@[to_additive]
/--
theorem `prod_eq_prod_mul_prod` / 定理 `prod_eq_prod_mul_prod`

English:
theorem prod_eq_prod_mul_prod
  given: {α : Type*} [CommMonoid α] [NumberField K] (f : InfinitePlace K -> α)
  proof: by
  rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))]
  simp [Fintype.prod_subtype_mul_prod_subtype]

中文:
定理 prod_eq_prod_mul_prod
  条件: {α : 类型} [交换幺半群 α] [数域 K] (f : InfinitePlace K -> α)
  证明: by
  rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))]
  simp [Fintype.prod_subtype_mul_prod_subtype]

Depends on / 依赖: Equiv.prod_comp, Equiv.subtypeEquivRight, Fintype, Fintype.prod_subtype_mul_prod_subtype, not_isReal_iff_isComplex, prod_comp, prod_subtype_mul_prod_subtype, subtypeEquivRight
-/
theorem prod_eq_prod_mul_prod {α : Type*} [CommMonoid α] [NumberField K] (f : InfinitePlace K -> α) :
    ∏ w, f w = (∏ w : {w // IsReal w}, f w.1) * (∏ w : {w // IsComplex w}, f w.1) := by
  rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))]
  simp [Fintype.prod_subtype_mul_prod_subtype]

/--
theorem `sum_mult_eq` / 定理 `sum_mult_eq`

English:
theorem sum_mult_eq
  given: [NumberField K]
  proof: by
  classical
  rw [← Embeddings.card K Complex]; rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.univ.sum_fiberwise
    (fun φ => InfinitePlace.mk φ)]
  exact Finset.sum_congr rfl
    (fun _ _ => by rw [Finset.sum_const, smul_eq_mul, mul_one, card_filter_mk_eq])

中文:
定理 sum_mult_eq
  条件: [数域 K]
  证明: by
  classical
  rw [← Embeddings.card K Complex]; rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.univ.sum_fiberwise
    (fun φ => InfinitePlace.mk φ)]
  exact Finset.sum_congr rfl
    (fun _ _ => by rw [Finset.sum_const, smul_eq_mul, mul_one, card_filter_mk_eq])

Depends on / 依赖: Embeddings, Embeddings.card, Finset, Finset.card_eq_sum_ones, Finset.sum_congr, Finset.sum_const, Finset.univ.sum_fiberwise, Fintype, Fintype.card, InfinitePlace, InfinitePlace.mk, card_eq_sum_ones, card_filter_mk_eq, classical, mul_one, smul_eq_mul, sum_congr, sum_const, sum_fiberwise
-/
theorem sum_mult_eq [NumberField K] :
    ∑ w : InfinitePlace K, mult w = Module.finrank Rat K := by
  classical
  rw [← Embeddings.card K Complex]; rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.univ.sum_fiberwise
    (fun φ => InfinitePlace.mk φ)]
  exact Finset.sum_congr rfl
    (fun _ _ => by rw [Finset.sum_const, smul_eq_mul, mul_one, card_filter_mk_eq])

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mkReal` / `mkReal` 的定义

English:
definition mkReal
  signature: :
  body: by
  refine (Equiv.ofBijective (fun φ => ⟨mk φ, ?_⟩) ⟨fun φ ψ h => ?_, fun w => ?_⟩)
  · exact ⟨φ, φ.prop, rfl⟩
  · rwa [Subtype.mk.injEq, mk_eq_iff, ComplexEmbedding.isReal_iff.mp φ.prop, or_self,
      ← Subtype.ext_iff] at h
  · exact ⟨⟨embedding w, isReal_iff.mp w.prop⟩, by simp⟩

中文:
定义 mk实数
  签名: :
  定义体: by
  refine (Equiv.ofBijective (fun φ => ⟨mk φ, ?_⟩) ⟨fun φ ψ h => ?_, fun w => ?_⟩)
  · exact ⟨φ, φ.prop, rfl⟩
  · rwa [Subtype.mk.injEq, mk_eq_iff, ComplexEmbedding.isReal_iff.mp φ.prop, or_self,
      ← Subtype.ext_iff] at h
  · exact ⟨⟨embedding w, isReal_iff.mp w.prop⟩, by simp⟩

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff.mp, Equiv.ofBijective, Subtype, Subtype.ext_iff, Subtype.mk.injEq, embedding, ext_iff, isReal_iff, isReal_iff.mp, mk_eq_iff, ofBijective, or_self, w.prop
-/
noncomputable def mkReal :
    { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } ≃ { w : InfinitePlace K // IsReal w } := by
  refine (Equiv.ofBijective (fun φ => ⟨mk φ, ?_⟩) ⟨fun φ ψ h => ?_, fun w => ?_⟩)
  · exact ⟨φ, φ.prop, rfl⟩
  · rwa [Subtype.mk.injEq, mk_eq_iff, ComplexEmbedding.isReal_iff.mp φ.prop, or_self,
      ← Subtype.ext_iff] at h
  · exact ⟨⟨embedding w, isReal_iff.mp w.prop⟩, by simp⟩

/--
Definition of `mkComplex` / `mkComplex` 的定义

English:
definition mkComplex
  signature: :
  body: Subtype.map mk fun φ hφ => ⟨φ, hφ, rfl⟩

@[simp]

中文:
定义 mkComplex
  签名: :
  定义体: Subtype.map mk fun φ hφ => ⟨φ, hφ, rfl⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.map
-/
noncomputable def mkComplex :
    { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ } -> { w : InfinitePlace K // IsComplex w } :=
  Subtype.map mk fun φ hφ => ⟨φ, hφ, rfl⟩

@[simp]
/--
theorem `mkReal_coe` / 定理 `mkReal_coe`

English:
theorem mkReal_coe
  given: (φ : { φ : K ->+* Complex // ComplexEmbedding.IsReal φ })
  proof: rfl

@[simp]

中文:
定理 mk实数_coe
  条件: (φ : { φ : K ->+* 复形 // ComplexEmbedding.Is实数 φ })
  证明: rfl

@[simp]
-/
theorem mkReal_coe (φ : { φ : K ->+* Complex // ComplexEmbedding.IsReal φ }) :
    (mkReal φ : InfinitePlace K) = mk (φ : K ->+* Complex) := rfl

@[simp]
/--
theorem `mkComplex_coe` / 定理 `mkComplex_coe`

English:
theorem mkComplex_coe
  given: (φ : { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ })
  proof: rfl

中文:
定理 mkComplex_coe
  条件: (φ : { φ : K ->+* 复形 // ¬ComplexEmbedding.Is实数 φ })
  证明: rfl
-/
theorem mkComplex_coe (φ : { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ }) :
    (mkComplex φ : InfinitePlace K) = mk (φ : K ->+* Complex) := rfl

variable [NumberField K]

/--
theorem `prod_eq_abs_norm` / 定理 `prod_eq_abs_norm`

English:
theorem prod_eq_abs_norm
  given: (x : K)
  proof: by
  classical
  convert! (congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings Rat Complex x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K Complex) (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
    rw [← Finset.prod_fiberwise Finset.univ mk (fun φ => ‖φ x‖)]
    have (w : InfinitePlace K) (φ) (hφ : φ in ({φ | mk φ = w} : Finset _)) :
        ‖φ x‖ = w x := by rw [← (Finset.mem_filter.mp hφ).2, apply]
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

中文:
定理 prod_eq_abs_norm
  条件: (x : K)
  证明: by
  classical
  convert! (congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings Rat Complex x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K Complex) (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
    rw [← Finset.prod_fiberwise Finset.univ mk (fun φ => ‖φ x‖)]
    have (w : InfinitePlace K) (φ) (hφ : φ in ({φ | mk φ = w} : Finset _)) :
        ‖φ x‖ = w x := by rw [← (Finset.mem_filter.mp hφ).2, apply]
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

Depends on / 依赖: Algebra, Algebra.norm_eq_prod_embeddings, Finset, Finset.mem_filter.mp, Finset.prod_congr, Finset.prod_cons, Finset.prod_fiberwise, Finset.univ, Fintype, Fintype.prod_equiv, InfinitePlace, RingHom, RingHom.equivRatAlgHom, RingHom.equivRatAlgHom_apply, classical, congr_arg, convert, equivRatAlgHom, equivRatAlgHom_apply, mem_filter
-/
theorem prod_eq_abs_norm (x : K) :
    ∏ w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x) := by
  classical
  convert! (congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings Rat Complex x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K Complex) (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
    rw [← Finset.prod_fiberwise Finset.univ mk (fun φ => ‖φ x‖)]
    have (w : InfinitePlace K) (φ) (hφ : φ in ({φ | mk φ = w} : Finset _)) :
        ‖φ x‖ = w x := by rw [← (Finset.mem_filter.mp hφ).2, apply]
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

/--
theorem `one_le_of_lt_one` / 定理 `one_le_of_lt_one`

English:
theorem one_le_of_lt_one
  statement: {w : InfinitePlace K} {a : (𝓞 K)} (ha : a != 0)
  proof: by
  suffices (1 : Real) <= |Algebra.norm Rat (a : K)| by
    contrapose! this
    rw [← InfinitePlace.prod_eq_abs_norm]; rw [← Finset.prod_const_one]
    refine Finset.prod_lt_prod_of_nonempty (fun _ _ => ?_) (fun z _ => ?_) Finset.univ_nonempty
    · exact pow_pos (pos_iff.mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)) _
    · refine pow_lt_one₀ (apply_nonneg _ _) ?_ (by rw [mult]; split_ifs <;> norm_num)
      by_cases hz : z = w
      · rwa [hz]
      · exact h hz
  rw [← Algebra.coe_norm_int]; rw [← Int.cast_one]; rw [← Int.cast_abs]; rw [Rat.cast_intCast]; rw [Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

中文:
定理 one_le_of_lt_one
  结论: {w : InfinitePlace K} {a : (𝓞 K)} (ha : a != 0)
  证明: by
  suffices (1 : Real) <= |Algebra.norm Rat (a : K)| by
    contrapose! this
    rw [← InfinitePlace.prod_eq_abs_norm]; rw [← Finset.prod_const_one]
    refine Finset.prod_lt_prod_of_nonempty (fun _ _ => ?_) (fun z _ => ?_) Finset.univ_nonempty
    · exact pow_pos (pos_iff.mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)) _
    · refine pow_lt_one₀ (apply_nonneg _ _) ?_ (by rw [mult]; split_ifs <;> norm_num)
      by_cases hz : z = w
      · rwa [hz]
      · exact h hz
  rw [← Algebra.coe_norm_int]; rw [← Int.cast_one]; rw [← Int.cast_abs]; rw [Rat.cast_intCast]; rw [Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

Depends on / 依赖: Algebra, Algebra.coe_norm_int, Algebra.norm, Finset, Finset.prod_const_one, Finset.prod_lt_prod_of_nonempty, Finset.univ_nonempty, InfinitePlace, InfinitePlace.prod_eq_abs_norm, Int.cast_abs, Int.cast_one, Subalgebra, Subalgebra.coe_eq_zero, apply_nonneg, cast_abs, cast_one, coe_eq_zero, coe_norm_int, contrapose, not.mpr
-/
theorem one_le_of_lt_one {w : InfinitePlace K} {a : (𝓞 K)} (ha : a != 0)
    (h : forall ⦃z⦄, z != w -> z a < 1) : 1 <= w a := by
  suffices (1 : Real) <= |Algebra.norm Rat (a : K)| by
    contrapose! this
    rw [← InfinitePlace.prod_eq_abs_norm]; rw [← Finset.prod_const_one]
    refine Finset.prod_lt_prod_of_nonempty (fun _ _ => ?_) (fun z _ => ?_) Finset.univ_nonempty
    · exact pow_pos (pos_iff.mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)) _
    · refine pow_lt_one₀ (apply_nonneg _ _) ?_ (by rw [mult]; split_ifs <;> norm_num)
      by_cases hz : z = w
      · rwa [hz]
      · exact h hz
  rw [← Algebra.coe_norm_int]; rw [← Int.cast_one]; rw [← Int.cast_abs]; rw [Rat.cast_intCast]; rw [Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

open scoped IntermediateField in
/--
theorem `_root_.NumberField.is_primitive_element_of_infinitePlace_lt` / 定理 `_root_.NumberField.is_primitive_element_of_infinitePlace_lt`

English:
theorem _root_.NumberField.is_primitive_element_of_infinitePlace_lt
  statement: {x : 𝓞 K}
  proof: by
  rw [Field.primitive_element_iff_algHom_eq_of_eval Rat Complex ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 <= w x := one_le_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      simp only [RingHom.toRatAlgHom_apply] at hψ
      rw [← norm_embedding_eq]; rw [hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm]; rw [mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw]; rw [or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' => hw.not_ge ?_)
      have : (embedding w x).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        have := RingHom.congr_fun h' x
        simp only [ComplexEmbedding.conjugate_coe_eq, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe] at this
        rw [this]
        exact hψ.symm
      rwa [← norm_embedding_eq, ← Complex.re_add_im (embedding w x), this, Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real] at h
  · exact fun x => IsAlgClosed.splits _

中文:
定理 _root_.数域.is_primitive_element_of_infinitePlace_lt
  结论: {x : 𝓞 K}
  证明: by
  rw [Field.primitive_element_iff_algHom_eq_of_eval Rat Complex ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 <= w x := one_le_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      simp only [RingHom.toRatAlgHom_apply] at hψ
      rw [← norm_embedding_eq]; rw [hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm]; rw [mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw]; rw [or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' => hw.not_ge ?_)
      have : (embedding w x).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        have := RingHom.congr_fun h' x
        simp only [ComplexEmbedding.conjugate_coe_eq, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe] at this
        rw [this]
        exact hψ.symm
      rwa [← norm_embedding_eq, ← Complex.re_add_im (embedding w x), this, Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real] at h
  · exact fun x => IsAlgClosed.splits _

Depends on / 依赖: Field.primitive_element_iff_algHom_eq_of_eval, InfinitePlace, InfinitePlace.mk, RingHom, RingHom.toRatAlgHom, RingHom.toRatAlgHom_apply, congr_arg, conjugate_embedding_eq_of_isReal, contrapose, embedding, h.symm, mk_embedding, mk_eq_iff, norm_embedding_eq, one_le_of_lt_one, or_self, primitive_element_iff_algHom_eq_of_eval, toRatAlgHom, toRatAlgHom_apply, toRingHom
-/
theorem _root_.NumberField.is_primitive_element_of_infinitePlace_lt {x : 𝓞 K}
    {w : InfinitePlace K} (h₁ : x != 0) (h₂ : forall ⦃w'⦄, w' != w -> w' x < 1)
    (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) : Rat⟮(x : K)⟯ = ⊤ := by
  rw [Field.primitive_element_iff_algHom_eq_of_eval Rat Complex ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 <= w x := one_le_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      simp only [RingHom.toRatAlgHom_apply] at hψ
      rw [← norm_embedding_eq]; rw [hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm]; rw [mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw]; rw [or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' => hw.not_ge ?_)
      have : (embedding w x).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        have := RingHom.congr_fun h' x
        simp only [ComplexEmbedding.conjugate_coe_eq, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe] at this
        rw [this]
        exact hψ.symm
      rwa [← norm_embedding_eq, ← Complex.re_add_im (embedding w x), this, Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real] at h
  · exact fun x => IsAlgClosed.splits _

/--
theorem `_root_.NumberField.adjoin_eq_top_of_infinitePlace_lt` / 定理 `_root_.NumberField.adjoin_eq_top_of_infinitePlace_lt`

English:
theorem _root_.NumberField.adjoin_eq_top_of_infinitePlace_lt
  statement: {x : 𝓞 K} {w : InfinitePlace K}
  proof: by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite Rat _)]
exact congr_arg IntermediateField.toSubalgebra
    NumberField.is_primitive_element_of_infinitePlace_lt h₁ h₂ h₃

中文:
定理 _root_.数域.adjoin_eq_top_of_infinitePlace_lt
  结论: {x : 𝓞 K} {w : InfinitePlace K}
  证明: by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite Rat _)]
exact congr_arg IntermediateField.toSubalgebra
    NumberField.is_primitive_element_of_infinitePlace_lt h₁ h₂ h₃

Depends on / 依赖: IntermediateField, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic, IntermediateField.toSubalgebra, IsAlgebraic, IsAlgebraic.of_finite, NumberField, NumberField.is_primitive_element_of_infinitePlace_lt, adjoin_simple_toSubalgebra_of_isAlgebraic, congr_arg, is_primitive_element_of_infinitePlace_lt, of_finite, toSubalgebra
-/
theorem _root_.NumberField.adjoin_eq_top_of_infinitePlace_lt {x : 𝓞 K} {w : InfinitePlace K}
    (h₁ : x != 0) (h₂ : forall ⦃w'⦄, w' != w -> w' x < 1) (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) :
    Algebra.adjoin Rat {(x : K)} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite Rat _)]
exact congr_arg IntermediateField.toSubalgebra
    NumberField.is_primitive_element_of_infinitePlace_lt h₁ h₂ h₃

variable (K)

open scoped Classical in
/--
Definition of `nrRealPlaces` / `nrRealPlaces` 的定义

English:
abbreviation nrRealPlaces
  body: card { w : InfinitePlace K // IsReal w }

中文:
缩写 nr实数Places
  定义体: card { w : InfinitePlace K // IsReal w }

Depends on / 依赖: InfinitePlace, IsReal
-/
noncomputable abbrev nrRealPlaces := card { w : InfinitePlace K // IsReal w }

open scoped Classical in
/--
Definition of `nrComplexPlaces` / `nrComplexPlaces` 的定义

English:
abbreviation nrComplexPlaces
  body: card { w : InfinitePlace K // IsComplex w }

中文:
缩写 nrComplexPlaces
  定义体: card { w : InfinitePlace K // IsComplex w }

Depends on / 依赖: InfinitePlace, IsComplex
-/
noncomputable abbrev nrComplexPlaces := card { w : InfinitePlace K // IsComplex w }

open scoped Classical in
/--
theorem `card_real_embeddings` / 定理 `card_real_embeddings`

English:
theorem card_real_embeddings
  proof: Fintype.card_congr mkReal

中文:
定理 card_real_embeddings
  证明: Fintype.card_congr mkReal

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, mkReal
-/
theorem card_real_embeddings :
    card { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } = nrRealPlaces K := Fintype.card_congr mkReal

/--
theorem `card_eq_nrRealPlaces_add_nrComplexPlaces` / 定理 `card_eq_nrRealPlaces_add_nrComplexPlaces`

English:
theorem card_eq_nrRealPlaces_add_nrComplexPlaces
  proof: by
  classical
  convert!
    Fintype.card_subtype_or_disjoint (IsReal (K := K)) (IsComplex (K := K))
      (disjoint_isReal_isComplex K) using 1
  exact (Fintype.card_of_subtype _ (fun w => ⟨fun _ => isReal_or_isComplex w, fun _ => by simp⟩)).symm

中文:
定理 card_eq_nr实数Places_add_nrComplexPlaces
  证明: by
  classical
  convert!
    Fintype.card_subtype_or_disjoint (IsReal (K := K)) (IsComplex (K := K))
      (disjoint_isReal_isComplex K) using 1
  exact (Fintype.card_of_subtype _ (fun w => ⟨fun _ => isReal_or_isComplex w, fun _ => by simp⟩)).symm

Depends on / 依赖: Fintype, Fintype.card_of_subtype, Fintype.card_subtype_or_disjoint, IsComplex, IsReal, card_of_subtype, card_subtype_or_disjoint, classical, convert, disjoint_isReal_isComplex, isReal_or_isComplex
-/
theorem card_eq_nrRealPlaces_add_nrComplexPlaces :
    Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K := by
  classical
  convert!
    Fintype.card_subtype_or_disjoint (IsReal (K := K)) (IsComplex (K := K))
      (disjoint_isReal_isComplex K) using 1
  exact (Fintype.card_of_subtype _ (fun w => ⟨fun _ => isReal_or_isComplex w, fun _ => by simp⟩)).symm

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/--
theorem `card_complex_embeddings` / 定理 `card_complex_embeddings`

English:
theorem card_complex_embeddings
  proof: by
  suffices forall w : { w : InfinitePlace K // IsComplex w },
     #{φ : {φ //¬ ComplexEmbedding.IsReal φ} | mkComplex φ = w} = 2 by
    rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
  rintro ⟨w, hw⟩
  convert! card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]

中文:
定理 card_complex_embeddings
  证明: by
  suffices forall w : { w : InfinitePlace K // IsComplex w },
     #{φ : {φ //¬ ComplexEmbedding.IsReal φ} | mkComplex φ = w} = 2 by
    rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
  rintro ⟨w, hw⟩
  convert! card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, Finset, Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_const, Finset.sum_fiberwise, Fintype, Fintype.card, Fintype.card_c, Fintype.card_subtype, InfinitePlace, IsComplex, IsReal, card_c, card_eq_sum_ones, card_filter_mk_eq, card_subtype, convert, mkComplex
-/
theorem card_complex_embeddings :
    card { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K := by
  suffices forall w : { w : InfinitePlace K // IsComplex w },
     #{φ : {φ //¬ ComplexEmbedding.IsReal φ} | mkComplex φ = w} = 2 by
    rw [Fintype.card]; rw [Finset.card_eq_sum_ones]; rw [← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
  rintro ⟨w, hw⟩
  convert! card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]

/--
theorem `card_add_two_mul_card_eq_rank` / 定理 `card_add_two_mul_card_eq_rank`

English:
theorem card_add_two_mul_card_eq_rank
  proof: by
  classical
  rw [← card_real_embeddings]; rw [← card_complex_embeddings]; rw [Fintype.card_subtype_compl]; rw [← Embeddings.card K Complex]; rw [Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

中文:
定理 card_add_two_mul_card_eq_rank
  证明: by
  classical
  rw [← card_real_embeddings]; rw [← card_complex_embeddings]; rw [Fintype.card_subtype_compl]; rw [← Embeddings.card K Complex]; rw [Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

Depends on / 依赖: Embeddings, Embeddings.card, Fintype, Fintype.card_subtype_compl, Fintype.card_subtype_le, Nat.add_sub_of_le, add_sub_of_le, card_complex_embeddings, card_real_embeddings, card_subtype_compl, card_subtype_le, classical
-/
theorem card_add_two_mul_card_eq_rank :
    nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K := by
  classical
  rw [← card_real_embeddings]; rw [← card_complex_embeddings]; rw [Fintype.card_subtype_compl]; rw [← Embeddings.card K Complex]; rw [Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `ComplexEmbedding.conjugate_sign` / 定理 `ComplexEmbedding.conjugate_sign`

English:
theorem ComplexEmbedding.conjugate_sign
  proof: by
  rw [Equiv.Perm.sign_of_pow_two_eq_one]; rw [Embeddings.card]; rw [← card_add_two_mul_card_eq_rank]; rw [← card_real_embeddings]; rw [Fintype.card]; rw [Fintype.card]; rw [Nat.add_sub_cancel_left]; rw [Nat.mul_div_cancel_left _ zero_lt_two]
  exact Equiv.ext (ComplexEmbedding.involutive_conjugate K).toPerm_involutive

中文:
定理 ComplexEmbedding.conjugate_sign
  证明: by
  rw [Equiv.Perm.sign_of_pow_two_eq_one]; rw [Embeddings.card]; rw [← card_add_two_mul_card_eq_rank]; rw [← card_real_embeddings]; rw [Fintype.card]; rw [Fintype.card]; rw [Nat.add_sub_cancel_left]; rw [Nat.mul_div_cancel_left _ zero_lt_two]
  exact Equiv.ext (ComplexEmbedding.involutive_conjugate K).toPerm_involutive

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.involutive_conjugate, Embeddings, Embeddings.card, Equiv.Perm.sign_of_pow_two_eq_one, Equiv.ext, Fintype, Fintype.card, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left, add_sub_cancel_left, card_add_two_mul_card_eq_rank, card_real_embeddings, involutive_conjugate, mul_div_cancel_left, sign_of_pow_two_eq_one, toPerm_involutive, zero_lt_two
-/
theorem ComplexEmbedding.conjugate_sign :
    (ComplexEmbedding.involutive_conjugate K).toPerm.sign = (-1) ^ nrComplexPlaces K := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one]; rw [Embeddings.card]; rw [← card_add_two_mul_card_eq_rank]; rw [← card_real_embeddings]; rw [Fintype.card]; rw [Fintype.card]; rw [Nat.add_sub_cancel_left]; rw [Nat.mul_div_cancel_left _ zero_lt_two]
  exact Equiv.ext (ComplexEmbedding.involutive_conjugate K).toPerm_involutive

variable {K}

/--
theorem `nrComplexPlaces_eq_zero_of_finrank_eq_one` / 定理 `nrComplexPlaces_eq_zero_of_finrank_eq_one`

English:
theorem nrComplexPlaces_eq_zero_of_finrank_eq_one
  given: (h : finrank Rat K = 1)
  proof: by linarith [card_add_two_mul_card_eq_rank K]

中文:
定理 nrComplexPlaces_eq_zero_of_finrank_eq_one
  条件: (h : finrank 有理数 K = 1)
  证明: by linarith [card_add_two_mul_card_eq_rank K]

Depends on / 依赖: card_add_two_mul_card_eq_rank
-/
theorem nrComplexPlaces_eq_zero_of_finrank_eq_one (h : finrank Rat K = 1) :
    nrComplexPlaces K = 0 := by linarith [card_add_two_mul_card_eq_rank K]

/--
theorem `nrRealPlaces_eq_one_of_finrank_eq_one` / 定理 `nrRealPlaces_eq_one_of_finrank_eq_one`

English:
theorem nrRealPlaces_eq_one_of_finrank_eq_one
  given: (h : finrank Rat K = 1)
  proof: by
  have := card_add_two_mul_card_eq_rank K
  rwa [nrComplexPlaces_eq_zero_of_finrank_eq_one h, h, mul_zero, add_zero] at this

中文:
定理 nr实数Places_eq_one_of_finrank_eq_one
  条件: (h : finrank 有理数 K = 1)
  证明: by
  have := card_add_two_mul_card_eq_rank K
  rwa [nrComplexPlaces_eq_zero_of_finrank_eq_one h, h, mul_zero, add_zero] at this

Depends on / 依赖: add_zero, card_add_two_mul_card_eq_rank, mul_zero, nrComplexPlaces_eq_zero_of_finrank_eq_one
-/
theorem nrRealPlaces_eq_one_of_finrank_eq_one (h : finrank Rat K = 1) :
    nrRealPlaces K = 1 := by
  have := card_add_two_mul_card_eq_rank K
  rwa [nrComplexPlaces_eq_zero_of_finrank_eq_one h, h, mul_zero, add_zero] at this

/--
theorem `nrRealPlaces_pos_of_odd_finrank` / 定理 `nrRealPlaces_pos_of_odd_finrank`

English:
theorem nrRealPlaces_pos_of_odd_finrank
  given: (h : Odd (finrank Rat K))
  proof: by
  refine Nat.pos_of_ne_zero ?_
  by_contra hc
  refine (Nat.not_odd_iff_even.mpr ?_) h
  rw [← card_add_two_mul_card_eq_rank]; rw [hc]; rw [zero_add]
  exact even_two_mul (nrComplexPlaces K)

中文:
定理 nr实数Places_pos_of_odd_finrank
  条件: (h : Odd (finrank 有理数 K))
  证明: by
  refine Nat.pos_of_ne_zero ?_
  by_contra hc
  refine (Nat.not_odd_iff_even.mpr ?_) h
  rw [← card_add_two_mul_card_eq_rank]; rw [hc]; rw [zero_add]
  exact even_two_mul (nrComplexPlaces K)

Depends on / 依赖: Nat.not_odd_iff_even.mpr, Nat.pos_of_ne_zero, card_add_two_mul_card_eq_rank, even_two_mul, not_odd_iff_even, nrComplexPlaces, pos_of_ne_zero, zero_add
-/
theorem nrRealPlaces_pos_of_odd_finrank (h : Odd (finrank Rat K)) :
    0 < nrRealPlaces K := by
  refine Nat.pos_of_ne_zero ?_
  by_contra hc
  refine (Nat.not_odd_iff_even.mpr ?_) h
  rw [← card_add_two_mul_card_eq_rank]; rw [hc]; rw [zero_add]
  exact even_two_mul (nrComplexPlaces K)

namespace IsPrimitiveRoot

variable {ζ : K} {k : Nat}

/--
theorem `nrRealPlaces_eq_zero_of_two_lt` / 定理 `nrRealPlaces_eq_zero_of_two_lt`

English:
theorem nrRealPlaces_eq_zero_of_two_lt
  given: (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k)
  proof: by
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff] at hwreal
  let f := w.embedding
  have hζ' : IsPrimitiveRoot (f ζ) k := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    rw [← Complex.conj_eq_iff_im]; rw [← NumberField.ComplexEmbedding.conjugate_coe_eq]
    congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    rw [← Complex.abs_re_eq_norm] at him
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by lia)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
exact hζ'.ne_one (by lia) Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero] at hζ'
    lia

中文:
定理 nr实数Places_eq_zero_of_two_lt
  条件: (hk : 2 < k) (hζ : 是PrimitiveRoot ζ k)
  证明: by
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff] at hwreal
  let f := w.embedding
  have hζ' : IsPrimitiveRoot (f ζ) k := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    rw [← Complex.conj_eq_iff_im]; rw [← NumberField.ComplexEmbedding.conjugate_coe_eq]
    congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    rw [← Complex.abs_re_eq_norm] at him
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by lia)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
exact hζ'.ne_one (by lia) Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero] at hζ'
    lia

Depends on / 依赖: Complex.abs_re_eq_norm, Complex.conj_eq_iff_im, Complex.norm_eq_one_of_pow_eq_one, ComplexEmbedding, Fintype, Fintype.card_eq_zero_iff, InfinitePlace, IsPrimitiveRoot, NumberField, NumberField.ComplexEmbedding.conjugate_coe_eq, NumberField.InfinitePlace.isReal_iff, abs_, abs_re_eq_norm, card_eq_zero_iff, conj_eq_iff_im, conjugate_coe_eq, embedding, f.injective, hwreal, injective
-/
theorem nrRealPlaces_eq_zero_of_two_lt (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k) :
    NumberField.InfinitePlace.nrRealPlaces K = 0 := by
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff] at hwreal
  let f := w.embedding
  have hζ' : IsPrimitiveRoot (f ζ) k := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    rw [← Complex.conj_eq_iff_im]; rw [← NumberField.ComplexEmbedding.conjugate_coe_eq]
    congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    rw [← Complex.abs_re_eq_norm] at him
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by lia)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
exact hζ'.ne_one (by lia) Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero] at hζ'
    lia

end IsPrimitiveRoot

end NumberField.InfinitePlace

/-!

## The infinite place of the rationals.

-/

namespace Rat

open NumberField

/--
Definition of `infinitePlace` / `infinitePlace` 的定义

English:
definition infinitePlace
  signature: : InfinitePlace Rat
  body: .mk (Rat.castHom _)

@[simp]

中文:
定义 infinitePlace
  签名: : InfinitePlace 有理数
  定义体: .mk (Rat.castHom _)

@[simp]

Depends on / 依赖: Rat.castHom, castHom
-/
noncomputable def infinitePlace : InfinitePlace Rat := .mk (Rat.castHom _)

@[simp]
/--
lemma `infinitePlace_apply` / 引理 `infinitePlace_apply`

English:
lemma infinitePlace_apply
  given: (v : InfinitePlace Rat) (x : Rat)
  statement: v x = |x|
  proof: by
  rw [NumberField.InfinitePlace.coe_apply]
  obtain ⟨_, _, rfl⟩ := v
  simp

中文:
引理 infinitePlace_apply
  条件: (v : InfinitePlace 有理数) (x : 有理数)
  结论: v x = |x|
  证明: by
  rw [NumberField.InfinitePlace.coe_apply]
  obtain ⟨_, _, rfl⟩ := v
  simp

Depends on / 依赖: InfinitePlace, NumberField, NumberField.InfinitePlace.coe_apply, coe_apply
-/
lemma infinitePlace_apply (v : InfinitePlace Rat) (x : Rat) : v x = |x| := by
  rw [NumberField.InfinitePlace.coe_apply]
  obtain ⟨_, _, rfl⟩ := v
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (InfinitePlace Rat)
  body: by ext; simp

中文:
实例 :
  签名: 子单例 (InfinitePlace 有理数)
  定义体: by ext; simp
-/
instance : Subsingleton (InfinitePlace Rat) where
  allEq a b := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (InfinitePlace Rat)
  body: ⟨⟨infinitePlace⟩, fun _ => Subsingleton.elim _ infinitePlace⟩

中文:
实例 :
  签名: 唯一 (InfinitePlace 有理数)
  定义体: ⟨⟨infinitePlace⟩, fun _ => Subsingleton.elim _ infinitePlace⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, infinitePlace
-/
noncomputable instance : Unique (InfinitePlace Rat) :=
  ⟨⟨infinitePlace⟩, fun _ => Subsingleton.elim _ infinitePlace⟩

/--
lemma `isReal_infinitePlace` / 引理 `isReal_infinitePlace`

English:
lemma isReal_infinitePlace
  statement: InfinitePlace.IsReal (infinitePlace)
  proof: ⟨Rat.castHom Complex, by ext; simp, rfl⟩

中文:
引理 is实数_infinitePlace
  结论: InfinitePlace.Is实数 (infinitePlace)
  证明: ⟨Rat.castHom Complex, by ext; simp, rfl⟩

Depends on / 依赖: Rat.castHom, castHom
-/
lemma isReal_infinitePlace : InfinitePlace.IsReal (infinitePlace) :=
  ⟨Rat.castHom Complex, by ext; simp, rfl⟩

end Rat

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] {v w : InfinitePlace K}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `map_ratCast` / 定理 `map_ratCast`

English:
theorem map_ratCast
  given: (v : InfinitePlace K) (x : Rat)
  statement: v x = ‖x‖
  proof: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

中文:
定理 map_ratCast
  条件: (v : InfinitePlace K) (x : 有理数)
  结论: v x = ‖x‖
  证明: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])
-/
protected theorem map_ratCast (v : InfinitePlace K) (x : Rat) : v x = ‖x‖ := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  given: (v : InfinitePlace K) (n : Nat)
  statement: v n = n
  proof: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

中文:
定理 map_natCast
  条件: (v : InfinitePlace K) (n : 自然数)
  结论: v n = n
  证明: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])
-/
protected theorem map_natCast (v : InfinitePlace K) (n : Nat) : v n = n := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `map_intCast` / 定理 `map_intCast`

English:
theorem map_intCast
  given: (v : InfinitePlace K) (z : Int)
  statement: v z = ‖z‖
  proof: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

中文:
定理 map_intCast
  条件: (v : InfinitePlace K) (z : 整数)
  结论: v z = ‖z‖
  证明: by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])
-/
protected theorem map_intCast (v : InfinitePlace K) (z : Int) : v z = ‖z‖ := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

/--
theorem `eq_one_of_rpow_eq` / 定理 `eq_one_of_rpow_eq`

English:
theorem eq_one_of_rpow_eq
  given: {t : Real} (h : (w ·) ^ t = v)
  statement: t = 1
  proof: by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ((n : Real).rpow_right_inj (by grind [Nat.cast_pos]) (by aesop)).1
    by simpa using funext_iff.1 h n

中文:
定理 eq_one_of_rpow_eq
  条件: {t : 实数} (h : (w ·) ^ t = v)
  结论: t = 1
  证明: by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ((n : Real).rpow_right_inj (by grind [Nat.cast_pos]) (by aesop)).1
    by simpa using funext_iff.1 h n

Depends on / 依赖: Nat.cast_pos, cast_pos, exists_gt, funext_iff, rpow_right_inj
-/
theorem eq_one_of_rpow_eq {t : Real} (h : (w ·) ^ t = v) : t = 1 := by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ((n : Real).rpow_right_inj (by grind [Nat.cast_pos]) (by aesop)).1
    by simpa using funext_iff.1 h n

/--
theorem `eq_iff_isEquiv` / 定理 `eq_iff_isEquiv`

English:
theorem eq_iff_isEquiv
  statement: w = v ↔ w.1.IsEquiv v.1
  proof: by
  refine ⟨fun h => h ▸ .rfl, fun h => ?_⟩
  obtain ⟨t, _, h⟩ := w.1.isEquiv_iff_exists_rpow_eq.1 h
  exact ext _ _ fun k => by simpa [eq_one_of_rpow_eq h, ext, coe_apply] using funext_iff.1 h k

中文:
定理 eq_iff_isEquiv
  结论: w = v ↔ w.1.Is等价 v.1
  证明: by
  refine ⟨fun h => h ▸ .rfl, fun h => ?_⟩
  obtain ⟨t, _, h⟩ := w.1.isEquiv_iff_exists_rpow_eq.1 h
  exact ext _ _ fun k => by simpa [eq_one_of_rpow_eq h, ext, coe_apply] using funext_iff.1 h k

Depends on / 依赖: coe_apply, eq_one_of_rpow_eq, funext_iff, isEquiv_iff_exists_rpow_eq
-/
theorem eq_iff_isEquiv : w = v ↔ w.1.IsEquiv v.1 := by
  refine ⟨fun h => h ▸ .rfl, fun h => ?_⟩
  obtain ⟨t, _, h⟩ := w.1.isEquiv_iff_exists_rpow_eq.1 h
  exact ext _ _ fun k => by simpa [eq_one_of_rpow_eq h, ext, coe_apply] using funext_iff.1 h k

variable (v)

/--
theorem `isNontrivial` / 定理 `isNontrivial`

English:
theorem isNontrivial
  statement: v.1.IsNontrivial
  proof: by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ⟨n, v.pos_iff.1 zero_lt_one.trans (by simpa), by simp [← coe_apply]; grind⟩

中文:
定理 isNontrivial
  结论: v.1.是非平凡
  证明: by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ⟨n, v.pos_iff.1 zero_lt_one.trans (by simpa), by simp [← coe_apply]; grind⟩

Depends on / 依赖: coe_apply, exists_gt, pos_iff, v.pos_iff, zero_lt_one, zero_lt_one.trans
-/
theorem isNontrivial : v.1.IsNontrivial := by
  obtain ⟨n, hn⟩ := exists_gt (1 : Nat)
exact ⟨n, v.pos_iff.1 zero_lt_one.trans (by simpa), by simp [← coe_apply]; grind⟩

variable {v} (K)

/--
theorem `denseRange_algebraMap_pi` / 定理 `denseRange_algebraMap_pi`

English:
theorem denseRange_algebraMap_pi
  given: [NumberField K]
  proof: AbsoluteValue.denseRange_algebraMap_pi (fun v => v.isNontrivial)
    fun _ _ h => (eq_iff_isEquiv (K := K)).not.mp h

中文:
定理 denseRange_algebraMap_pi
  条件: [数域 K]
  证明: AbsoluteValue.denseRange_algebraMap_pi (fun v => v.isNontrivial)
    fun _ _ h => (eq_iff_isEquiv (K := K)).not.mp h

Depends on / 依赖: AbsoluteValue, AbsoluteValue.denseRange_algebraMap_pi, denseRange_algebraMap_pi, eq_iff_isEquiv, isNontrivial, not.mp, v.isNontrivial
-/
theorem denseRange_algebraMap_pi [NumberField K] :
DenseRange algebraMap K ((v : InfinitePlace K) -> WithAbs v.1) :=
  AbsoluteValue.denseRange_algebraMap_pi (fun v => v.isNontrivial)
    fun _ _ h => (eq_iff_isEquiv (K := K)).not.mp h

end NumberField.InfinitePlace
