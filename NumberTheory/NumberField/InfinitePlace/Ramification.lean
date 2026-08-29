/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Ramification of infinite places of a number field

This file studies the ramification of infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace.comap`: the restriction of an infinite place along an embedding.
* `NumberField.InfinitePlace.orbitRelEquiv`: the equiv between the orbits of infinite places under
  the action of the Galois group and the infinite places of the base field.
* `NumberField.InfinitePlace.IsUnramified`: an infinite place is unramified in a field extension
  if the restriction has the same multiplicity.
* `NumberField.InfinitePlace.not_isUnramified_iff`: an infinite place is not unramified
  (i.e., is ramified) iff it is a complex place above a real place.
* `NumberField.InfinitePlace.IsUnramifiedIn`: an infinite place of the base field is unramified
  in a field extension if every infinite place over it is unramified.
* `IsUnramifiedAtInfinitePlaces`: a field extension is unramified at infinite places if every
  infinite place is unramified.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

open NumberField Fintype Module ComplexEmbedding

namespace NumberField.InfinitePlace

open scoped Finset

variable {k : Type*} [Field k] {K : Type*} [Field K] {F : Type*} [Field F]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (w : InfinitePlace K) (f : k ->+* K)
  body: ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; change _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]

中文:
定义 comap
  签名: (w : InfinitePlace K) (f : k ->+* K)
  定义体: ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; change _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]

Depends on / 依赖: choose_spec, embedding, f.injective, injective, w.embedding.comp
-/
def comap (w : InfinitePlace K) (f : k ->+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; change _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]
/--
lemma `comap_mk` / 引理 `comap_mk`

English:
lemma comap_mk
  given: (φ : K ->+* Complex) (f : k ->+* K)
  statement: (mk φ).comap f = mk (φ.comp f)
  proof: rfl

中文:
引理 comap_mk
  条件: (φ : K ->+* 复形) (f : k ->+* K)
  结论: (mk φ).comap f = mk (φ.comp f)
  证明: rfl
-/
lemma comap_mk (φ : K ->+* Complex) (f : k ->+* K) : (mk φ).comap f = mk (φ.comp f) := rfl

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (w : InfinitePlace K)
  statement: w.comap (RingHom.id K) = w
  proof: rfl

中文:
引理 comap_id
  条件: (w : InfinitePlace K)
  结论: w.comap (环态射.id K) = w
  证明: rfl
-/
lemma comap_id (w : InfinitePlace K) : w.comap (RingHom.id K) = w := rfl

/--
lemma `comap_comp` / 引理 `comap_comp`

English:
lemma comap_comp
  given: (w : InfinitePlace K) (f : F ->+* K) (g : k ->+* F)
  proof: rfl

@[simp]

中文:
引理 comap_comp
  条件: (w : InfinitePlace K) (f : F ->+* K) (g : k ->+* F)
  证明: rfl

@[simp]
-/
lemma comap_comp (w : InfinitePlace K) (f : F ->+* K) (g : k ->+* F) :
    w.comap (f.comp g) = (w.comap f).comap g := rfl

@[simp]
/--
lemma `comap_apply` / 引理 `comap_apply`

English:
lemma comap_apply
  given: (w : InfinitePlace K) (f : k ->+* K) (x : k)
  proof: rfl

中文:
引理 comap_apply
  条件: (w : InfinitePlace K) (f : k ->+* K) (x : k)
  证明: rfl
-/
lemma comap_apply (w : InfinitePlace K) (f : k ->+* K) (x : k) :
    w.comap f x = w (f x) := rfl

/--
lemma `comp_of_comap_eq` / 引理 `comp_of_comap_eq`

English:
lemma comp_of_comap_eq
  statement: {v : InfinitePlace k} {w : InfinitePlace K} {f : k ->+* K}
  proof: by
  simp [← h]

中文:
引理 comp_of_comap_eq
  结论: {v : InfinitePlace k} {w : InfinitePlace K} {f : k ->+* K}
  证明: by
  simp [← h]
-/
lemma comp_of_comap_eq {v : InfinitePlace k} {w : InfinitePlace K} {f : k ->+* K}
    (h : w.comap f = v) (x : k) : w (f x) = v x := by
  simp [← h]

/--
lemma `coe_mk_comp` / 引理 `coe_mk_comp`

English:
lemma coe_mk_comp
  statement: {ψ : K ->+* Complex} {f : k ->+* K}
  proof: rfl

中文:
引理 coe_mk_comp
  结论: {ψ : K ->+* 复形} {f : k ->+* K}
  证明: rfl
-/
lemma coe_mk_comp {ψ : K ->+* Complex} {f : k ->+* K}
    (h : Function.Injective f) : (mk (ψ.comp f)).1 = (mk ψ).1.comp h := rfl

/--
lemma `comap_mk_lift` / 引理 `comap_mk_lift`

English:
lemma comap_mk_lift
  given: [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex)
  proof: by simp

中文:
引理 comap_mk_lift
  条件: [代数 k K] [代数.是代数 k K] (φ : k ->+* 复形)
  证明: by simp
-/
lemma comap_mk_lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) :
    (mk (ComplexEmbedding.lift K φ)).comap (algebraMap k K) = mk φ := by simp

/--
lemma `IsReal.comap` / 引理 `IsReal.comap`

English:
lemma IsReal.comap
  given: (f : k ->+* K) {w : InfinitePlace K} (hφ : IsReal w)
  proof: by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]
  rw [← mk_embedding w]; rw [isReal_mk_iff] at hφ
  exact hφ.comp f

中文:
引理 Is实数.comap
  条件: (f : k ->+* K) {w : InfinitePlace K} (hφ : Is实数 w)
  证明: by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]
  rw [← mk_embedding w]; rw [isReal_mk_iff] at hφ
  exact hφ.comp f

Depends on / 依赖: comap_mk, isReal_mk_iff, mk_embedding
-/
lemma IsReal.comap (f : k ->+* K) {w : InfinitePlace K} (hφ : IsReal w) :
    IsReal (w.comap f) := by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]
  rw [← mk_embedding w]; rw [isReal_mk_iff] at hφ
  exact hφ.comp f

/--
lemma `IsComplex.of_comap` / 引理 `IsComplex.of_comap`

English:
lemma IsComplex.of_comap
  given: (f : k ->+* K) {w : InfinitePlace K} (hf : IsComplex (w.comap f))
  proof: by
  rw [← not_isReal_iff_isComplex] at hf ⊢
  exact (IsReal.comap f).mt hf

中文:
引理 是复形.of_comap
  条件: (f : k ->+* K) {w : InfinitePlace K} (hf : 是复形 (w.comap f))
  证明: by
  rw [← not_isReal_iff_isComplex] at hf ⊢
  exact (IsReal.comap f).mt hf

Depends on / 依赖: IsReal, IsReal.comap, not_isReal_iff_isComplex
-/
lemma IsComplex.of_comap (f : k ->+* K) {w : InfinitePlace K} (hf : IsComplex (w.comap f)) :
    IsComplex w := by
  rw [← not_isReal_iff_isComplex] at hf ⊢
  exact (IsReal.comap f).mt hf

/--
lemma `isReal_comap_iff` / 引理 `isReal_comap_iff`

English:
lemma isReal_comap_iff
  given: (f : k ≃+* K) {w : InfinitePlace K}
  proof: by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [ComplexEmbedding.isReal_comp_iff]

中文:
引理 is实数_comap_iff
  条件: (f : k ≃+* K) {w : InfinitePlace K}
  证明: by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [ComplexEmbedding.isReal_comp_iff]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_comp_iff, comap_mk, isReal_comp_iff, isReal_mk_iff, mk_embedding
-/
lemma isReal_comap_iff (f : k ≃+* K) {w : InfinitePlace K} :
    IsReal (w.comap (f : k ->+* K)) ↔ IsReal w := by
  rw [← mk_embedding w]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [ComplexEmbedding.isReal_comp_iff]

/--
lemma `comap_surjective` / 引理 `comap_surjective`

English:
lemma comap_surjective
  given: [Algebra k K] [Algebra.IsAlgebraic k K]
  proof: fun w =>
  ⟨(mk (ComplexEmbedding.lift K w.embedding)), by simp⟩

中文:
引理 comap_surjective
  条件: [代数 k K] [代数.是代数 k K]
  证明: fun w =>
  ⟨(mk (ComplexEmbedding.lift K w.embedding)), by simp⟩
-/
lemma comap_surjective [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective (comap · (algebraMap k K)) := fun w =>
  ⟨(mk (ComplexEmbedding.lift K w.embedding)), by simp⟩

/--
theorem `comap_embedding_of_isReal` / 定理 `comap_embedding_of_isReal`

English:
theorem comap_embedding_of_isReal
  given: (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal)
  proof: by
   rw [← mk_embedding w]; rw [comap_mk]; rw [mk_embedding]; rw [embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding])]

中文:
定理 comap_embedding_of_is实数
  条件: (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).Is实数)
  证明: by
   rw [← mk_embedding w]; rw [comap_mk]; rw [mk_embedding]; rw [embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding])]

Depends on / 依赖: comap_mk, embedding_mk_eq_of_isReal, isReal_mk_iff, mk_embedding
-/
theorem comap_embedding_of_isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) :
    (w.comap f).embedding = w.embedding.comp f := by
   rw [← mk_embedding w]; rw [comap_mk]; rw [mk_embedding]; rw [embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding])]

/--
lemma `mult_comap_le` / 引理 `mult_comap_le`

English:
lemma mult_comap_le
  given: (f : k ->+* K) (w : InfinitePlace K)
  statement: mult (w.comap f) <= mult w
  proof: by
  rw [mult]; rw [mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

中文:
引理 mult_comap_le
  条件: (f : k ->+* K) (w : InfinitePlace K)
  结论: mult (w.comap f) <= mult w
  证明: by
  rw [mult]; rw [mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

Depends on / 依赖: all_goals, pick_goal, split_ifs
-/
lemma mult_comap_le (f : k ->+* K) (w : InfinitePlace K) : mult (w.comap f) <= mult w := by
  rw [mult]; rw [mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

variable [Algebra k K] (σ : Gal(K/k)) (w : InfinitePlace K)
variable (k K)

/--
lemma `card_mono` / 引理 `card_mono`

English:
lemma card_mono
  given: [NumberField k] [NumberField K]
  proof: have := Module.Finite.of_restrictScalars_finite Rat k K
  Fintype.card_le_of_surjective _ comap_surjective

中文:
引理 card_mono
  条件: [数域 k] [数域 K]
  证明: have := Module.Finite.of_restrictScalars_finite Rat k K
  Fintype.card_le_of_surjective _ comap_surjective

Depends on / 依赖: Finite, Fintype, Fintype.card_le_of_surjective, Module, Module.Finite.of_restrictScalars_finite, card_le_of_surjective, comap_surjective, of_restrictScalars_finite
-/
lemma card_mono [NumberField k] [NumberField K] :
    card (InfinitePlace k) <= card (InfinitePlace K) :=
  have := Module.Finite.of_restrictScalars_finite Rat k K
  Fintype.card_le_of_surjective _ comap_surjective

variable {k K}

/-- The action of the Galois group on infinite places. -/
@[simps! smul_coe_apply]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Gal(K/k) (InfinitePlace K)
  body: fun σ w => w.comap σ.symm
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

中文:
实例 :
  签名: 乘法作用 Gal(K/k) (InfinitePlace K)
  定义体: fun σ w => w.comap σ.symm
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

Depends on / 依赖: w.comap
-/
instance : MulAction Gal(K/k) (InfinitePlace K) where
  smul := fun σ w => w.comap σ.symm
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

/--
lemma `smul_eq_comap` / 引理 `smul_eq_comap`

English:
lemma smul_eq_comap
  statement: σ • w = w.comap σ.symm
  proof: rfl

中文:
引理 smul_eq_comap
  结论: σ • w = w.comap σ.symm
  证明: rfl
-/
lemma smul_eq_comap : σ • w = w.comap σ.symm := rfl

/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (x)
  statement: (σ • w) x = w (σ.symm x)
  proof: rfl

中文:
引理 smul_apply
  条件: (x)
  结论: (σ • w) x = w (σ.symm x)
  证明: rfl
-/
@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl

/--
lemma `smul_mk` / 引理 `smul_mk`

English:
lemma smul_mk
  given: (φ : K ->+* Complex)
  statement: σ • mk φ = mk (φ.comp σ.symm)
  proof: rfl

中文:
引理 smul_mk
  条件: (φ : K ->+* 复形)
  结论: σ • mk φ = mk (φ.comp σ.symm)
  证明: rfl
-/
@[simp] lemma smul_mk (φ : K ->+* Complex) : σ • mk φ = mk (φ.comp σ.symm) := rfl

/--
lemma `comap_smul` / 引理 `comap_smul`

English:
lemma comap_smul
  given: {f : F ->+* K}
  statement: (σ • w).comap f = w.comap (RingHom.comp σ.symm f)
  proof: rfl

中文:
引理 comap_smul
  条件: {f : F ->+* K}
  结论: (σ • w).comap f = w.comap (环态射.comp σ.symm f)
  证明: rfl
-/
lemma comap_smul {f : F ->+* K} : (σ • w).comap f = w.comap (RingHom.comp σ.symm f) := rfl

variable {σ w}

/--
lemma `isReal_smul_iff` / 引理 `isReal_smul_iff`

English:
lemma isReal_smul_iff
  statement: IsReal (σ • w) ↔ IsReal w
  proof: isReal_comap_iff (f := σ.symm.toRingEquiv)

中文:
引理 is实数_smul_iff
  结论: Is实数 (σ • w) ↔ Is实数 w
  证明: isReal_comap_iff (f := σ.symm.toRingEquiv)

Depends on / 依赖: isReal_comap_iff, symm.toRingEquiv, toRingEquiv
-/
lemma isReal_smul_iff : IsReal (σ • w) ↔ IsReal w := isReal_comap_iff (f := σ.symm.toRingEquiv)

/--
lemma `isComplex_smul_iff` / 引理 `isComplex_smul_iff`

English:
lemma isComplex_smul_iff
  statement: IsComplex (σ • w) ↔ IsComplex w
  proof: by
  rw [← not_isReal_iff_isComplex]; rw [← not_isReal_iff_isComplex]; rw [isReal_smul_iff]

中文:
引理 isComplex_smul_iff
  结论: 是复形 (σ • w) ↔ 是复形 w
  证明: by
  rw [← not_isReal_iff_isComplex]; rw [← not_isReal_iff_isComplex]; rw [isReal_smul_iff]

Depends on / 依赖: isReal_smul_iff, not_isReal_iff_isComplex
-/
lemma isComplex_smul_iff : IsComplex (σ • w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex]; rw [← not_isReal_iff_isComplex]; rw [isReal_smul_iff]

/--
lemma `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq` / 引理 `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`

English:
lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
  statement: [IsGalois k K] (φ ψ : K ->+* Complex)
  proof: NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq φ ψ h

中文:
引理 ComplexEmbedding.存在_comp_symm_eq_of_comp_eq
  结论: [是Galois k K] (φ ψ : K ->+* 复形)
  证明: NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq φ ψ h

Depends on / 依赖: ComplexEmbedding, NumberField, NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq, exists_comp_symm_eq_of_comp_eq
-/
lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [IsGalois k K] (φ ψ : K ->+* Complex)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    exists σ : Gal(K/k), φ.comp σ.symm = ψ :=
  NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq φ ψ h

/--
lemma `exists_smul_eq_of_comap_eq` / 引理 `exists_smul_eq_of_comap_eq`

English:
lemma exists_smul_eq_of_comap_eq
  statement: [IsGalois k K] {w w' : InfinitePlace K}
  proof: by
  rw [← mk_embedding w]; rw [← mk_embedding w']; rw [comap_mk]; rw [comap_mk]; rw [mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd Complex).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [mk_eq_iff]
    exact Or.inr hσ

中文:
引理 存在_smul_eq_of_comap_eq
  结论: [是Galois k K] {w w' : InfinitePlace K}
  证明: by
  rw [← mk_embedding w]; rw [← mk_embedding w']; rw [comap_mk]; rw [comap_mk]; rw [mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd Complex).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [mk_eq_iff]
    exact Or.inr hσ

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.exists_comp_symm_eq_of_comp_eq, comap_mk, embedding, exists_comp_symm_eq_of_comp_eq, mk_embedding, mk_eq_iff, smul_mk, starRingEnd, w.embedding
-/
lemma exists_smul_eq_of_comap_eq [IsGalois k K] {w w' : InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) : exists σ : Gal(K/k), σ • w = w' := by
  rw [← mk_embedding w]; rw [← mk_embedding w']; rw [comap_mk]; rw [comap_mk]; rw [mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd Complex).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w]; rw [← mk_embedding w']; rw [smul_mk]; rw [mk_eq_iff]
    exact Or.inr hσ

/--
lemma `mem_orbit_iff` / 引理 `mem_orbit_iff`

English:
lemma mem_orbit_iff
  given: [IsGalois k K] {w w' : InfinitePlace K}
  proof: by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w]; rw [comap_mk]; rw [smul_mk]; rw [comap_mk]
  congr 1; ext1; simp

中文:
引理 mem_orbit_iff
  条件: [是Galois k K] {w w' : InfinitePlace K}
  证明: by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w]; rw [comap_mk]; rw [smul_mk]; rw [comap_mk]
  congr 1; ext1; simp

Depends on / 依赖: comap_mk, exists_smul_eq_of_comap_eq, mk_embedding, smul_mk
-/
lemma mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} :
    w' in MulAction.orbit Gal(K/k) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K) := by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w]; rw [comap_mk]; rw [smul_mk]; rw [comap_mk]
  congr 1; ext1; simp

/-- The orbits of infinite places under the action of the Galois group are indexed by
the infinite places of the base field. -/
noncomputable
/--
Definition of `orbitRelEquiv` / `orbitRelEquiv` 的定义

English:
definition orbitRelEquiv
  signature: [IsGalois k K]
  body: by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e => (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩

中文:
定义 orbitRelEquiv
  签名: [是Galois k K]
  定义体: by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e => (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩

Depends on / 依赖: Equiv.ofBijective, Quotient, Quotient.lift, Quotient.sound, algebraMap, comap_surjective, e.symm, mem_orbit_iff, mem_orbit_iff.mp, mem_orbit_iff.mpr, ofBijective
-/
def orbitRelEquiv [IsGalois k K] :
    Quotient (MulAction.orbitRel Gal(K/k) (InfinitePlace K)) ≃ InfinitePlace k := by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e => (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩

/--
lemma `orbitRelEquiv_apply_mk''` / 引理 `orbitRelEquiv_apply_mk''`

English:
lemma orbitRelEquiv_apply_mk''
  given: [IsGalois k K] (w : InfinitePlace K)
  proof: rfl

中文:
引理 orbitRelEquiv_apply_mk''
  条件: [是Galois k K] (w : InfinitePlace K)
  证明: rfl
-/
lemma orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' w) = comap w (algebraMap k K) := rfl

variable (k w)

/--
Definition of `IsUnramified` / `IsUnramified` 的定义

English:
definition IsUnramified
  signature: : Prop
  body: mult (w.comap (algebraMap k K)) = mult w

中文:
定义 IsUnramified
  签名: : 命题
  定义体: mult (w.comap (algebraMap k K)) = mult w

Depends on / 依赖: algebraMap, w.comap
-/
def IsUnramified : Prop := mult (w.comap (algebraMap k K)) = mult w

/--
Definition of `IsRamified` / `IsRamified` 的定义

English:
abbreviation IsRamified
  signature: : Prop
  body: ¬w.IsUnramified k

中文:
缩写 IsRamified
  签名: : 命题
  定义体: ¬w.IsUnramified k

Depends on / 依赖: IsUnramified, w.IsUnramified
-/
abbrev IsRamified : Prop := ¬w.IsUnramified k

/--
lemma `isUnramified_or_isRamified` / 引理 `isUnramified_or_isRamified`

English:
lemma isUnramified_or_isRamified
  statement: w.IsUnramified k ∨ w.IsRamified k
  proof: or_not

中文:
引理 isUnramified_or_isRamified
  结论: w.IsUnramified k ∨ w.IsRamified k
  证明: or_not

Depends on / 依赖: or_not
-/
lemma isUnramified_or_isRamified : w.IsUnramified k ∨ w.IsRamified k :=
  or_not

variable {k}

/--
lemma `isUnramified_self` / 引理 `isUnramified_self`

English:
lemma isUnramified_self
  statement: IsUnramified K w
  proof: rfl

中文:
引理 isUnramified_self
  结论: IsUnramified K w
  证明: rfl
-/
lemma isUnramified_self : IsUnramified K w := rfl

variable {w}

/--
lemma `IsUnramified.eq` / 引理 `IsUnramified.eq`

English:
lemma IsUnramified.eq
  given: (h : IsUnramified k w)
  statement: mult (w.comap (algebraMap k K)) = mult w
  proof: h

中文:
引理 IsUnramified.eq
  条件: (h : IsUnramified k w)
  结论: mult (w.comap (algebraMap k K)) = mult w
  证明: h
-/
lemma IsUnramified.eq (h : IsUnramified k w) : mult (w.comap (algebraMap k K)) = mult w := h

/--
lemma `isUnramified_iff_mult_le` / 引理 `isUnramified_iff_mult_le`

English:
lemma isUnramified_iff_mult_le
  proof: by
  rw [IsUnramified]; rw [le_antisymm_iff]; rw [and_iff_right]
  exact mult_comap_le _ _

中文:
引理 isUnramified_iff_mult_le
  证明: by
  rw [IsUnramified]; rw [le_antisymm_iff]; rw [and_iff_right]
  exact mult_comap_le _ _

Depends on / 依赖: IsUnramified, and_iff_right, le_antisymm_iff, mult_comap_le
-/
lemma isUnramified_iff_mult_le :
    IsUnramified k w ↔ mult w <= mult (w.comap (algebraMap k K)) := by
  rw [IsUnramified]; rw [le_antisymm_iff]; rw [and_iff_right]
  exact mult_comap_le _ _

variable [Algebra k F]

/--
lemma `IsUnramified.comap_algHom` / 引理 `IsUnramified.comap_algHom`

English:
lemma IsUnramified.comap_algHom
  given: {w : InfinitePlace F} (h : IsUnramified k w) (f : K ->ₐ[k] F)
  proof: by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← InfinitePlace.comap_comp]; rw [f.comp_algebraMap]; rw [h.eq]
  exact InfinitePlace.mult_comap_le _ _

中文:
引理 IsUnramified.comap_algHom
  条件: {w : InfinitePlace F} (h : IsUnramified k w) (f : K ->ₐ[k] F)
  证明: by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← InfinitePlace.comap_comp]; rw [f.comp_algebraMap]; rw [h.eq]
  exact InfinitePlace.mult_comap_le _ _

Depends on / 依赖: InfinitePlace, InfinitePlace.comap_comp, InfinitePlace.isUnramified_iff_mult_le, InfinitePlace.mult_comap_le, comap_comp, comp_algebraMap, f.comp_algebraMap, h.eq, isUnramified_iff_mult_le, mult_comap_le
-/
lemma IsUnramified.comap_algHom {w : InfinitePlace F} (h : IsUnramified k w) (f : K ->ₐ[k] F) :
    IsUnramified k (w.comap (f : K ->+* F)) := by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← InfinitePlace.comap_comp]; rw [f.comp_algebraMap]; rw [h.eq]
  exact InfinitePlace.mult_comap_le _ _

variable (K)
variable [Algebra K F] [IsScalarTower k K F]

/--
lemma `IsUnramified.of_restrictScalars` / 引理 `IsUnramified.of_restrictScalars`

English:
lemma IsUnramified.of_restrictScalars
  given: {w : InfinitePlace F} (h : IsUnramified k w)
  proof: by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← h.eq]; rw [IsScalarTower.algebraMap_eq k K F]; rw [InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _

中文:
引理 IsUnramified.of_restrictScalars
  条件: {w : InfinitePlace F} (h : IsUnramified k w)
  证明: by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← h.eq]; rw [IsScalarTower.algebraMap_eq k K F]; rw [InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _

Depends on / 依赖: InfinitePlace, InfinitePlace.comap_comp, InfinitePlace.isUnramified_iff_mult_le, InfinitePlace.mult_comap_le, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, comap_comp, h.eq, isUnramified_iff_mult_le, mult_comap_le
-/
lemma IsUnramified.of_restrictScalars {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified K w := by
  rw [InfinitePlace.isUnramified_iff_mult_le]; rw [← h.eq]; rw [IsScalarTower.algebraMap_eq k K F]; rw [InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _

/--
lemma `IsUnramified.comap` / 引理 `IsUnramified.comap`

English:
lemma IsUnramified.comap
  given: {w : InfinitePlace F} (h : IsUnramified k w)
  proof: h.comap_algHom (IsScalarTower.toAlgHom k K F)

中文:
引理 IsUnramified.comap
  条件: {w : InfinitePlace F} (h : IsUnramified k w)
  证明: h.comap_algHom (IsScalarTower.toAlgHom k K F)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, comap_algHom, h.comap_algHom, toAlgHom
-/
lemma IsUnramified.comap {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified k (w.comap (algebraMap K F)) :=
  h.comap_algHom (IsScalarTower.toAlgHom k K F)

variable {K}

/--
lemma `not_isUnramified_iff` / 引理 `not_isUnramified_iff`

English:
lemma not_isUnramified_iff
  proof: by
  rw [IsUnramified]; rw [mult]; rw [mult]; rw [← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)

中文:
引理 not_isUnramified_iff
  证明: by
  rw [IsUnramified]; rw [mult]; rw [mult]; rw [← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, IsUnramified, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, and_self, false_iff, forall_iff, forall_true_left, not_and, not_false_eq_true, not_isReal_iff_isComplex, not_true_eq_false, ofNat_ne_one, one_ne_ofNat, split_ifs, true_iff
-/
lemma not_isUnramified_iff :
    ¬ IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K)) := by
  rw [IsUnramified]; rw [mult]; rw [mult]; rw [← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)

/--
lemma `isUnramified_iff` / 引理 `isUnramified_iff`

English:
lemma isUnramified_iff
  proof: by
  rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [not_or]; rw [not_isReal_iff_isComplex]; rw [not_isComplex_iff_isReal]

中文:
引理 isUnramified_iff
  证明: by
  rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [not_or]; rw [not_isReal_iff_isComplex]; rw [not_isComplex_iff_isReal]

Depends on / 依赖: not_iff_not, not_isComplex_iff_isReal, not_isReal_iff_isComplex, not_isUnramified_iff, not_or
-/
lemma isUnramified_iff :
    IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K)) := by
  rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [not_or]; rw [not_isReal_iff_isComplex]; rw [not_isComplex_iff_isReal]

/--
theorem `isRamified_iff` / 定理 `isRamified_iff`

English:
theorem isRamified_iff
  statement: w.IsRamified k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
  proof: not_isUnramified_iff

中文:
定理 isRamified_iff
  结论: w.IsRamified k ↔ w.是复形 ∧ (w.comap (algebraMap k K)).Is实数
  证明: not_isUnramified_iff

Depends on / 依赖: not_isUnramified_iff
-/
theorem isRamified_iff : w.IsRamified k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal :=
  not_isUnramified_iff

/--
theorem `IsRamified.isComplex` / 定理 `IsRamified.isComplex`

English:
theorem IsRamified.isComplex
  given: (h : w.IsRamified k)
  statement: w.IsComplex
  proof: (isRamified_iff.1 h).1

中文:
定理 IsRamified.isComplex
  条件: (h : w.IsRamified k)
  结论: w.是复形
  证明: (isRamified_iff.1 h).1

Depends on / 依赖: isRamified_iff
-/
theorem IsRamified.isComplex (h : w.IsRamified k) : w.IsComplex := (isRamified_iff.1 h).1

/--
theorem `IsRamified.isReal` / 定理 `IsRamified.isReal`

English:
theorem IsRamified.isReal
  given: (h : w.IsRamified k)
  statement: (w.comap (algebraMap k K)).IsReal
  proof: (isRamified_iff.1 h).2

中文:
定理 IsRamified.is实数
  条件: (h : w.IsRamified k)
  结论: (w.comap (algebraMap k K)).Is实数
  证明: (isRamified_iff.1 h).2

Depends on / 依赖: isRamified_iff
-/
theorem IsRamified.isReal (h : w.IsRamified k) : (w.comap (algebraMap k K)).IsReal :=
  (isRamified_iff.1 h).2

/--
theorem `IsRamified.ne_conjugate` / 定理 `IsRamified.ne_conjugate`

English:
theorem IsRamified.ne_conjugate
  given: {w₁ w₂ : InfinitePlace K} (h : w₂.IsRamified k)
  proof: by
  by_cases h_eq : w₁ = w₂
  · rw [isRamified_iff, isComplex_iff] at h
    exact Ne.symm (h_eq ▸ h.1)
  · contrapose h_eq
    rw [← mk_embedding w₁]; rw [h_eq]; rw [mk_conjugate_eq]; rw [mk_embedding]

中文:
定理 IsRamified.ne_conjugate
  条件: {w₁ w₂ : InfinitePlace K} (h : w₂.IsRamified k)
  证明: by
  by_cases h_eq : w₁ = w₂
  · rw [isRamified_iff, isComplex_iff] at h
    exact Ne.symm (h_eq ▸ h.1)
  · contrapose h_eq
    rw [← mk_embedding w₁]; rw [h_eq]; rw [mk_conjugate_eq]; rw [mk_embedding]

Depends on / 依赖: Ne.symm, contrapose, h_eq, isComplex_iff, isRamified_iff, mk_conjugate_eq, mk_embedding
-/
theorem IsRamified.ne_conjugate {w₁ w₂ : InfinitePlace K} (h : w₂.IsRamified k) :
    w₁.embedding != ComplexEmbedding.conjugate w₂.embedding := by
  by_cases h_eq : w₁ = w₂
  · rw [isRamified_iff, isComplex_iff] at h
    exact Ne.symm (h_eq ▸ h.1)
  · contrapose h_eq
    rw [← mk_embedding w₁]; rw [h_eq]; rw [mk_conjugate_eq]; rw [mk_embedding]

/--
lemma `IsRamified.comap_embedding` / 引理 `IsRamified.comap_embedding`

English:
lemma IsRamified.comap_embedding
  given: {w : InfinitePlace K} (h : w.IsRamified k)
  proof: by
  rw [← comap_embedding_of_isReal _ (isRamified_iff.1 h).2]

中文:
引理 IsRamified.comap_embedding
  条件: {w : InfinitePlace K} (h : w.IsRamified k)
  证明: by
  rw [← comap_embedding_of_isReal _ (isRamified_iff.1 h).2]

Depends on / 依赖: comap_embedding_of_isReal, isRamified_iff
-/
lemma IsRamified.comap_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    (w.comap (algebraMap k K)).embedding = w.embedding.comp (algebraMap k K) := by
  rw [← comap_embedding_of_isReal _ (isRamified_iff.1 h).2]

/--
lemma `IsRamified.comap_embedding_conjugate` / 引理 `IsRamified.comap_embedding_conjugate`

English:
lemma IsRamified.comap_embedding_conjugate
  given: {w : InfinitePlace K} (h : w.IsRamified k)
  proof: by
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 ((isRamified_iff.1 h).2)]
  simp [conjugate_comp, comap_embedding_of_isReal _ ((isRamified_iff.1 h).2)]

中文:
引理 IsRamified.comap_embedding_conjugate
  条件: {w : InfinitePlace K} (h : w.IsRamified k)
  证明: by
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 ((isRamified_iff.1 h).2)]
  simp [conjugate_comp, comap_embedding_of_isReal _ ((isRamified_iff.1 h).2)]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff, comap_embedding_of_isReal, conjugate_comp, isRamified_iff, isReal_iff
-/
lemma IsRamified.comap_embedding_conjugate {w : InfinitePlace K} (h : w.IsRamified k) :
    (w.comap (algebraMap k K)).embedding = (conjugate w.embedding).comp (algebraMap k K) := by
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 ((isRamified_iff.1 h).2)]
  simp [conjugate_comp, comap_embedding_of_isReal _ ((isRamified_iff.1 h).2)]

/--
lemma `IsRamified.isMixed_embedding` / 引理 `IsRamified.isMixed_embedding`

English:
lemma IsRamified.isMixed_embedding
  given: {w : InfinitePlace K} (h : w.IsRamified k)
  proof: ⟨comap_embedding_of_isReal _ h.isReal ▸ isReal_iff.1 h.isReal, isComplex_iff.1 h.isComplex⟩

中文:
引理 IsRamified.isMixed_embedding
  条件: {w : InfinitePlace K} (h : w.IsRamified k)
  证明: ⟨comap_embedding_of_isReal _ h.isReal ▸ isReal_iff.1 h.isReal, isComplex_iff.1 h.isComplex⟩

Depends on / 依赖: comap_embedding_of_isReal, h.isComplex, h.isReal, isComplex, isComplex_iff, isReal, isReal_iff
-/
lemma IsRamified.isMixed_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    IsMixed k w.embedding :=
  ⟨comap_embedding_of_isReal _ h.isReal ▸ isReal_iff.1 h.isReal, isComplex_iff.1 h.isComplex⟩

/--
lemma `IsRamified.isMixed_conjugate_embedding` / 引理 `IsRamified.isMixed_conjugate_embedding`

English:
lemma IsRamified.isMixed_conjugate_embedding
  given: {w : InfinitePlace K} (h : w.IsRamified k)
  proof: ⟨h.comap_embedding_conjugate ▸ isReal_iff.1 h.isReal,
by simpa using isComplex_iff.1 h.isComplex⟩

中文:
引理 IsRamified.isMixed_conjugate_embedding
  条件: {w : InfinitePlace K} (h : w.IsRamified k)
  证明: ⟨h.comap_embedding_conjugate ▸ isReal_iff.1 h.isReal,
by simpa using isComplex_iff.1 h.isComplex⟩

Depends on / 依赖: comap_embedding_conjugate, h.comap_embedding_conjugate, h.isComplex, h.isReal, isComplex, isComplex_iff, isReal, isReal_iff
-/
lemma IsRamified.isMixed_conjugate_embedding {w : InfinitePlace K} (h : w.IsRamified k) :
    IsMixed k (conjugate w.embedding) :=
  ⟨h.comap_embedding_conjugate ▸ isReal_iff.1 h.isReal,
by simpa using isComplex_iff.1 h.isComplex⟩

/--
theorem `isRamified_mk_iff_isMixed` / 定理 `isRamified_mk_iff_isMixed`

English:
theorem isRamified_mk_iff_isMixed
  given: {φ : K ->+* Complex}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isMixed_embedding
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isMixed_conjugate_embedding
  · rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, embedding_mk_eq_of_isReal h.1]
    exact ⟨by rcases embedding_mk_eq φ with (_ | _) <;> aesop, h.1⟩

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsMixed.mk_isRamified⟩ := isRamified_mk_iff_isMixed

中文:
定理 isRamified_mk_iff_isMixed
  条件: {φ : K ->+* 复形}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isMixed_embedding
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isMixed_conjugate_embedding
  · rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, embedding_mk_eq_of_isReal h.1]
    exact ⟨by rcases embedding_mk_eq φ with (_ | _) <;> aesop, h.1⟩

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsMixed.mk_isRamified⟩ := isRamified_mk_iff_isMixed

Depends on / 依赖: comap_mk, conjugate, embedding_mk_eq, embedding_mk_eq_of_isReal, h.isMixed_conjugate_embedding, h.isMixed_embedding, isComplex_iff, isMixed_conjugate_embedding, isMixed_embedding, isRamified_iff, isReal_iff, star_star
-/
theorem isRamified_mk_iff_isMixed {φ : K ->+* Complex} :
    (mk φ).IsRamified k ↔ IsMixed k φ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isMixed_embedding
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isMixed_conjugate_embedding
  · rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, embedding_mk_eq_of_isReal h.1]
    exact ⟨by rcases embedding_mk_eq φ with (_ | _) <;> aesop, h.1⟩

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsMixed.mk_isRamified⟩ := isRamified_mk_iff_isMixed

/--
lemma `IsUnramified.isUnmixed` / 引理 `IsUnramified.isUnmixed`

English:
lemma IsUnramified.isUnmixed
  given: {w : InfinitePlace K} (h : w.IsUnramified k)
  proof: by
  intro hw
  rw [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding] at hw
exact isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

中文:
引理 IsUnramified.isUnmixed
  条件: {w : InfinitePlace K} (h : w.IsUnramified k)
  证明: by
  intro hw
  rw [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding] at hw
exact isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

Depends on / 依赖: comap_mk, isReal_iff, isReal_mk_iff, isUnramified_iff, mk_embedding, not_isComplex_iff_isReal, resolve_right
-/
lemma IsUnramified.isUnmixed {w : InfinitePlace K} (h : w.IsUnramified k) :
    IsUnmixed k w.embedding := by
  intro hw
  rw [← isReal_mk_iff]; rw [← comap_mk]; rw [mk_embedding] at hw
exact isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

/--
lemma `IsUnramified.isUnmixed_conjugate` / 引理 `IsUnramified.isUnmixed_conjugate`

English:
lemma IsUnramified.isUnmixed_conjugate
  given: {w : InfinitePlace K} (h : w.IsUnramified k)
  proof: by
  intro hw
  simp_rw [conjugate_comp, IsSelfAdjoint.star_iff, ← isReal_mk_iff, ← comap_mk, mk_embedding] at hw
simpa using isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

中文:
引理 IsUnramified.isUnmixed_conjugate
  条件: {w : InfinitePlace K} (h : w.IsUnramified k)
  证明: by
  intro hw
  simp_rw [conjugate_comp, IsSelfAdjoint.star_iff, ← isReal_mk_iff, ← comap_mk, mk_embedding] at hw
simpa using isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_iff, comap_mk, conjugate_comp, isReal_iff, isReal_mk_iff, isUnramified_iff, mk_embedding, not_isComplex_iff_isReal, resolve_right, simp_rw, star_iff
-/
lemma IsUnramified.isUnmixed_conjugate {w : InfinitePlace K} (h : w.IsUnramified k) :
    IsUnmixed k (conjugate w.embedding) := by
  intro hw
  simp_rw [conjugate_comp, IsSelfAdjoint.star_iff, ← isReal_mk_iff, ← comap_mk, mk_embedding] at hw
simpa using isReal_iff.1 (isUnramified_iff.1 h).resolve_right (not_isComplex_iff_isReal.2 hw)

/--
theorem `isUnramified_mk_iff_isUnmixed` / 定理 `isUnramified_mk_iff_isUnmixed`

English:
theorem isUnramified_mk_iff_isUnmixed
  given: {φ : K ->+* Complex}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isUnmixed
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isUnmixed_conjugate
  · rw [isUnramified_iff, isReal_iff]
    by_cases hv : ComplexEmbedding.IsReal (φ.comp (algebraMap k K))
· exact .inl by simp [embedding_mk_eq_of_isReal, h hv]
· exact .inr by simpa using (isReal_mk_iff.not.2 hv)

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsUnmixed.mk_isUnramified⟩ :=
  isUnramified_mk_iff_isUnmixed

中文:
定理 isUnramified_mk_iff_isUnmixed
  条件: {φ : K ->+* 复形}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isUnmixed
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isUnmixed_conjugate
  · rw [isUnramified_iff, isReal_iff]
    by_cases hv : ComplexEmbedding.IsReal (φ.comp (algebraMap k K))
· exact .inl by simp [embedding_mk_eq_of_isReal, h hv]
· exact .inr by simpa using (isReal_mk_iff.not.2 hv)

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsUnmixed.mk_isUnramified⟩ :=
  isUnramified_mk_iff_isUnmixed

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsReal, IsReal, algebraMap, conjugate, embedding_mk_eq, embedding_mk_eq_of_isReal, h.isUnmixed, h.isUnmixed_conjugate, isReal_iff, isReal_mk_iff, isReal_mk_iff.not, isUnmixed, isUnmixed_conjugate, isUnramified_iff, star_star
-/
theorem isUnramified_mk_iff_isUnmixed {φ : K ->+* Complex} :
    (mk φ).IsUnramified k ↔ IsUnmixed k φ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases embedding_mk_eq φ with (hl | hr)
    · exact hl ▸ h.isUnmixed
    · rw [← star_star φ]; simpa [← congrArg conjugate hr] using h.isUnmixed_conjugate
  · rw [isUnramified_iff, isReal_iff]
    by_cases hv : ComplexEmbedding.IsReal (φ.comp (algebraMap k K))
· exact .inl by simp [embedding_mk_eq_of_isReal, h hv]
· exact .inr by simpa using (isReal_mk_iff.not.2 hv)

alias ⟨_, _root_.NumberField.ComplexEmbedding.IsUnmixed.mk_isUnramified⟩ :=
  isUnramified_mk_iff_isUnmixed

variable (k)

/--
lemma `IsReal.isUnramified` / 引理 `IsReal.isUnramified`

English:
lemma IsReal.isUnramified
  given: (h : IsReal w)
  statement: IsUnramified k w
  proof: isUnramified_iff.mpr (Or.inl h)

中文:
引理 Is实数.isUnramified
  条件: (h : Is实数 w)
  结论: IsUnramified k w
  证明: isUnramified_iff.mpr (Or.inl h)

Depends on / 依赖: Or.inl, isUnramified_iff, isUnramified_iff.mpr
-/
lemma IsReal.isUnramified (h : IsReal w) : IsUnramified k w := isUnramified_iff.mpr (Or.inl h)

variable {k}

/--
lemma `_root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff` / 引理 `_root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff`

English:
lemma _root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff
  proof: by
  rw [h.ext_iff]; rw [ComplexEmbedding.isConj_one_iff]; rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [← not_isReal_iff_isComplex]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [eq_true h.isReal_comp]; rw [and_true]

中文:
引理 _root_.数域.ComplexEmbedding.IsConj.isUnramified_mk_iff
  证明: by
  rw [h.ext_iff]; rw [ComplexEmbedding.isConj_one_iff]; rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [← not_isReal_iff_isComplex]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [eq_true h.isReal_comp]; rw [and_true]

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isConj_one_iff, and_true, comap_mk, eq_true, ext_iff, h.ext_iff, h.isReal_comp, isConj_one_iff, isReal_comp, isReal_mk_iff, not_iff_not, not_isReal_iff_isComplex, not_isUnramified_iff
-/
lemma _root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff
    {φ : K ->+* Complex} (h : ComplexEmbedding.IsConj φ σ) :
    IsUnramified k (mk φ) ↔ σ = 1 := by
  rw [h.ext_iff]; rw [ComplexEmbedding.isConj_one_iff]; rw [← not_iff_not]; rw [not_isUnramified_iff]; rw [← not_isReal_iff_isComplex]; rw [comap_mk]; rw [isReal_mk_iff]; rw [isReal_mk_iff]; rw [eq_true h.isReal_comp]; rw [and_true]

/--
lemma `isUnramified_mk_iff_forall_isConj` / 引理 `isUnramified_mk_iff_forall_isConj`

English:
lemma isUnramified_mk_iff_forall_isConj
  given: [IsGalois k K] {φ : K ->+* Complex}
  proof: by
  refine ⟨fun H σ hσ => hσ.isUnramified_mk_iff.mp H,
    fun H => ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk]; rw [isReal_mk_iff]; rw [← not_isReal_iff_isComplex]; rw [isReal_mk_iff]; rw [← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K ->ₐ[k] Complex := { star φ with
    commutes' := fun r => by simpa using! RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer Gal(K/k)

中文:
引理 isUnramified_mk_iff_对任意_isConj
  条件: [是Galois k K] {φ : K ->+* 复形}
  证明: by
  refine ⟨fun H σ hσ => hσ.isUnramified_mk_iff.mp H,
    fun H => ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk]; rw [isReal_mk_iff]; rw [← not_isReal_iff_isComplex]; rw [isReal_mk_iff]; rw [← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K ->ₐ[k] Complex := { star φ with
    commutes' := fun r => by simpa using! RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer Gal(K/k)

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isConj_one_iff, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.congr_fun, algebraMap, comap_mk, commutes, congr_fun, isConj_one_iff, isReal_mk_iff, isUnramified_mk_iff, isUnramified_mk_iff.mp, not_isReal_iff_isComplex, not_isUnramified_iff, of_algebraMap_eq, toAlgebra
-/
lemma isUnramified_mk_iff_forall_isConj [IsGalois k K] {φ : K ->+* Complex} :
    IsUnramified k (mk φ) ↔ forall σ : Gal(K/k), ComplexEmbedding.IsConj φ σ -> σ = 1 := by
  refine ⟨fun H σ hσ => hσ.isUnramified_mk_iff.mp H,
    fun H => ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk]; rw [isReal_mk_iff]; rw [← not_isReal_iff_isComplex]; rw [isReal_mk_iff]; rw [← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K Complex := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K ->ₐ[k] Complex := { star φ with
    commutes' := fun r => by simpa using! RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer Gal(K/k)

/--
lemma `mem_stabilizer_mk_iff` / 引理 `mem_stabilizer_mk_iff`

English:
lemma mem_stabilizer_mk_iff
  given: (φ : K ->+* Complex) (σ : Gal(K/k))
  proof: by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm]; rw [ComplexEmbedding.conjugate]; rw [star_eq_iff_star_eq]
  refine or_congr ⟨fun H => ?_, fun H => H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x => φ.injective (RingHom.congr_fun H x))

中文:
引理 mem_stabilizer_mk_iff
  条件: (φ : K ->+* 复形) (σ : Gal(K/k))
  证明: by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm]; rw [ComplexEmbedding.conjugate]; rw [star_eq_iff_star_eq]
  refine or_congr ⟨fun H => ?_, fun H => H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x => φ.injective (RingHom.congr_fun H x))

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.refl, AlgEquiv.symm, ComplexEmbedding, ComplexEmbedding.conjugate, ComplexEmbedding.isConj_symm, Iff.rfl, MulAction, MulAction.mem_stabilizer_iff, RingHom, RingHom.congr_fun, congr_arg, congr_fun, conjugate, injective, isConj_symm, mem_stabilizer_iff, mk_eq_iff, or_congr
-/
lemma mem_stabilizer_mk_iff (φ : K ->+* Complex) (σ : Gal(K/k)) :
    σ in Stab (mk φ) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm]; rw [ComplexEmbedding.conjugate]; rw [star_eq_iff_star_eq]
  refine or_congr ⟨fun H => ?_, fun H => H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x => φ.injective (RingHom.congr_fun H x))

/--
lemma `IsUnramified.stabilizer_eq_bot` / 引理 `IsUnramified.stabilizer_eq_bot`

English:
lemma IsUnramified.stabilizer_eq_bot
  given: (h : IsUnramified k w)
  statement: Stab w = ⊥
  proof: by
  rw [eq_bot_iff]; rw [← mk_embedding w]; rw [SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ => hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)

中文:
引理 IsUnramified.stabilizer_eq_bot
  条件: (h : IsUnramified k w)
  结论: Stab w = ⊥
  证明: by
  rw [eq_bot_iff]; rw [← mk_embedding w]; rw [SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ => hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)

Depends on / 依赖: SetLike, SetLike.le_def, Subgroup, Subgroup.mem_bot, eq_bot_iff, forall_eq_or_imp, isUnramified_mk_iff, isUnramified_mk_iff.mp, le_def, mem_bot, mem_stabilizer_mk_iff, mk_embedding, true_and
-/
lemma IsUnramified.stabilizer_eq_bot (h : IsUnramified k w) : Stab w = ⊥ := by
  rw [eq_bot_iff]; rw [← mk_embedding w]; rw [SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ => hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)

/--
lemma `_root_.NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk` / 引理 `_root_.NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk`

English:
lemma _root_.NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk
  proof: by
  ext
  rw [SetLike.mem_coe]; rw [mem_stabilizer_mk_iff]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff]; rw [← h.ext_iff]; rw [eq_comm (a := σ)]

中文:
引理 _root_.数域.ComplexEmbedding.IsConj.coe_stabilizer_mk
  证明: by
  ext
  rw [SetLike.mem_coe]; rw [mem_stabilizer_mk_iff]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff]; rw [← h.ext_iff]; rw [eq_comm (a := σ)]

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, SetLike, SetLike.mem_coe, eq_comm, ext_iff, h.ext_iff, mem_coe, mem_insert_iff, mem_singleton_iff, mem_stabilizer_mk_iff
-/
lemma _root_.NumberField.ComplexEmbedding.IsConj.coe_stabilizer_mk
    {φ : K ->+* Complex} (h : ComplexEmbedding.IsConj φ σ) :
    (Stab (mk φ) : Set Gal(K/k)) = {1, σ} := by
  ext
  rw [SetLike.mem_coe]; rw [mem_stabilizer_mk_iff]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff]; rw [← h.ext_iff]; rw [eq_comm (a := σ)]

variable (k w)

/--
lemma `nat_card_stabilizer_eq_one_or_two` / 引理 `nat_card_stabilizer_eq_one_or_two`

English:
lemma nat_card_stabilizer_eq_one_or_two
  proof: by
  classical
  rw [← SetLike.coe_sort_coe]; rw [← mk_embedding w]
  by_cases! h : exists σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    rw [hσ.coe_stabilizer_mk]
    simp
  · left
    trans Nat.card ({1} : Set Gal(K/k))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

中文:
引理 nat_card_stabilizer_eq_one_or_two
  证明: by
  classical
  rw [← SetLike.coe_sort_coe]; rw [← mk_embedding w]
  by_cases! h : exists σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    rw [hσ.coe_stabilizer_mk]
    simp
  · left
    trans Nat.card ({1} : Set Gal(K/k))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.IsConj, IsConj, IsEmpty, IsEmpty.forall_iff, Nat.card, Set.mem_singleton_iff, SetLike, SetLike.coe_sort_coe, SetLike.mem_coe, classical, coe_sort_coe, coe_stabilizer_mk, embedding, forall_iff, mem_coe, mem_singleton_iff, mem_stabilizer_mk_iff, mk_embedding, or_iff_left_iff_imp
-/
lemma nat_card_stabilizer_eq_one_or_two :
    Nat.card (Stab w) = 1 ∨ Nat.card (Stab w) = 2 := by
  classical
  rw [← SetLike.coe_sort_coe]; rw [← mk_embedding w]
  by_cases! h : exists σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    rw [hσ.coe_stabilizer_mk]
    simp
  · left
    trans Nat.card ({1} : Set Gal(K/k))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

variable {k w}

/--
lemma `isUnramified_iff_stabilizer_eq_bot` / 引理 `isUnramified_iff_stabilizer_eq_bot`

English:
lemma isUnramified_iff_stabilizer_eq_bot
  given: [IsGalois k K]
  statement: IsUnramified k w ↔ Stab w = ⊥
  proof: by
  rw [← mk_embedding w]; rw [isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]

中文:
引理 isUnramified_iff_stabilizer_eq_bot
  条件: [是Galois k K]
  结论: IsUnramified k w ↔ Stab w = ⊥
  证明: by
  rw [← mk_embedding w]; rw [isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]

Depends on / 依赖: SetLike, SetLike.le_def, Subgroup, Subgroup.mem_bot, eq_bot_iff, forall_eq_or_imp, isUnramified_mk_iff_forall_isConj, le_def, mem_bot, mem_stabilizer_mk_iff, mk_embedding, true_and
-/
lemma isUnramified_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Stab w = ⊥ := by
  rw [← mk_embedding w]; rw [isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]

/--
lemma `isUnramified_iff_card_stabilizer_eq_one` / 引理 `isUnramified_iff_card_stabilizer_eq_one`

English:
lemma isUnramified_iff_card_stabilizer_eq_one
  given: [IsGalois k K]
  proof: by
  rw [isUnramified_iff_stabilizer_eq_bot]; rw [Subgroup.card_eq_one]

中文:
引理 isUnramified_iff_card_stabilizer_eq_one
  条件: [是Galois k K]
  证明: by
  rw [isUnramified_iff_stabilizer_eq_bot]; rw [Subgroup.card_eq_one]

Depends on / 依赖: Subgroup, Subgroup.card_eq_one, card_eq_one, isUnramified_iff_stabilizer_eq_bot
-/
lemma isUnramified_iff_card_stabilizer_eq_one [IsGalois k K] :
    IsUnramified k w ↔ Nat.card (Stab w) = 1 := by
  rw [isUnramified_iff_stabilizer_eq_bot]; rw [Subgroup.card_eq_one]

/--
lemma `not_isUnramified_iff_card_stabilizer_eq_two` / 引理 `not_isUnramified_iff_card_stabilizer_eq_two`

English:
lemma not_isUnramified_iff_card_stabilizer_eq_two
  given: [IsGalois k K]
  proof: by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e | e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide

中文:
引理 not_isUnramified_iff_card_stabilizer_eq_two
  条件: [是Galois k K]
  证明: by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e | e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide

Depends on / 依赖: isUnramified_iff_card_stabilizer_eq_one, nat_card_stabilizer_eq_one_or_two
-/
lemma not_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] :
    ¬ IsUnramified k w ↔ Nat.card (Stab w) = 2 := by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e | e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide

/--
lemma `isRamified_iff_card_stabilizer_eq_two` / 引理 `isRamified_iff_card_stabilizer_eq_two`

English:
lemma isRamified_iff_card_stabilizer_eq_two
  given: [IsGalois k K]
  proof: not_isUnramified_iff_card_stabilizer_eq_two

中文:
引理 isRamified_iff_card_stabilizer_eq_two
  条件: [是Galois k K]
  证明: not_isUnramified_iff_card_stabilizer_eq_two

Depends on / 依赖: not_isUnramified_iff_card_stabilizer_eq_two
-/
lemma isRamified_iff_card_stabilizer_eq_two [IsGalois k K] :
    IsRamified k w ↔ Nat.card (Stab w) = 2 :=
  not_isUnramified_iff_card_stabilizer_eq_two

/--
lemma `exists_isConj_of_isRamified` / 引理 `exists_isConj_of_isRamified`

English:
lemma exists_isConj_of_isRamified
  given: [IsGalois k K] {φ : K ->+* Complex} (h : IsRamified k (mk φ))
  proof: by
  rw [isRamified_iff_card_stabilizer_eq_two]; rw [Nat.card_eq_two_iff] at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h₁, -⟩ := h
  rw [mem_stabilizer_mk_iff] at hx hy
  grind

中文:
引理 存在_isConj_of_isRamified
  条件: [是Galois k K] {φ : K ->+* 复形} (h : IsRamified k (mk φ))
  证明: by
  rw [isRamified_iff_card_stabilizer_eq_two]; rw [Nat.card_eq_two_iff] at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h₁, -⟩ := h
  rw [mem_stabilizer_mk_iff] at hx hy
  grind

Depends on / 依赖: Nat.card_eq_two_iff, card_eq_two_iff, isRamified_iff_card_stabilizer_eq_two, mem_stabilizer_mk_iff
-/
lemma exists_isConj_of_isRamified [IsGalois k K] {φ : K ->+* Complex} (h : IsRamified k (mk φ)) :
    exists σ : Gal(K/k), ComplexEmbedding.IsConj φ σ := by
  rw [isRamified_iff_card_stabilizer_eq_two]; rw [Nat.card_eq_two_iff] at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h₁, -⟩ := h
  rw [mem_stabilizer_mk_iff] at hx hy
  grind

open scoped Classical in
/--
lemma `card_stabilizer` / 引理 `card_stabilizer`

English:
lemma card_stabilizer
  given: [IsGalois k K]
  proof: by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

中文:
引理 card_stabilizer
  条件: [是Galois k K]
  证明: by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

Depends on / 依赖: isUnramified_iff_card_stabilizer_eq_one, not_isUnramified_iff_card_stabilizer_eq_two
-/
lemma card_stabilizer [IsGalois k K] :
    Nat.card (Stab w) = if IsUnramified k w then 1 else 2 := by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

/--
lemma `even_nat_card_aut_of_not_isUnramified` / 引理 `even_nat_card_aut_of_not_isUnramified`

English:
lemma even_nat_card_aut_of_not_isUnramified
  given: [IsGalois k K] (hw : ¬ IsUnramified k w)
  proof: by
  by_cases H : Finite Gal(K/k)
  · cases nonempty_fintype Gal(K/k)
    rw [even_iff_two_dvd]; rw [← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert! Even.zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)

中文:
引理 even_nat_card_aut_of_not_isUnramified
  条件: [是Galois k K] (hw : ¬ IsUnramified k w)
  证明: by
  by_cases H : Finite Gal(K/k)
  · cases nonempty_fintype Gal(K/k)
    rw [even_iff_two_dvd]; rw [← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert! Even.zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)

Depends on / 依赖: Even.zero, Finite, Nat.finite_of_card_ne_zero, Subgroup, Subgroup.card_subgroup_dvd_card, card_subgroup_dvd_card, convert, even_iff_two_dvd, finite_of_card_ne_zero, nonempty_fintype, not_isUnramified_iff_card_stabilizer_eq_two, not_isUnramified_iff_card_stabilizer_eq_two.mp
-/
lemma even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card Gal(K/k)) := by
  by_cases H : Finite Gal(K/k)
  · cases nonempty_fintype Gal(K/k)
    rw [even_iff_two_dvd]; rw [← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert! Even.zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)

/--
lemma `even_card_aut_of_not_isUnramified` / 引理 `even_card_aut_of_not_isUnramified`

English:
lemma even_card_aut_of_not_isUnramified
  given: [IsGalois k K] (hw : ¬ IsUnramified k w)
  proof: even_nat_card_aut_of_not_isUnramified hw

中文:
引理 even_card_aut_of_not_isUnramified
  条件: [是Galois k K] (hw : ¬ IsUnramified k w)
  证明: even_nat_card_aut_of_not_isUnramified hw

Depends on / 依赖: even_nat_card_aut_of_not_isUnramified
-/
lemma even_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card Gal(K/k)) :=
  even_nat_card_aut_of_not_isUnramified hw

/--
lemma `even_finrank_of_not_isUnramified` / 引理 `even_finrank_of_not_isUnramified`

English:
lemma even_finrank_of_not_isUnramified
  statement: [IsGalois k K]
  proof: by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ Even.zero

中文:
引理 even_finrank_of_not_isUnramified
  结论: [是Galois k K]
  证明: by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ Even.zero

Depends on / 依赖: Even.zero, FiniteDimensional, IsGalois, IsGalois.card_aut_eq_finrank, card_aut_eq_finrank, even_card_aut_of_not_isUnramified, finrank_of_not_finite
-/
lemma even_finrank_of_not_isUnramified [IsGalois k K]
    (hw : ¬ IsUnramified k w) : Even (finrank k K) := by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ Even.zero

/--
lemma `isUnramified_smul_iff` / 引理 `isUnramified_smul_iff`

English:
lemma isUnramified_smul_iff
  proof: by
  rw [isUnramified_iff]; rw [isUnramified_iff]; rw [isReal_smul_iff]; rw [comap_smul]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

中文:
引理 isUnramified_smul_iff
  证明: by
  rw [isUnramified_iff]; rw [isUnramified_iff]; rw [isReal_smul_iff]; rw [comap_smul]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom_toRingHom, AlgHom, AlgHom.comp_algebraMap, comap_smul, comp_algebraMap, isReal_smul_iff, isUnramified_iff, toAlgHom_toRingHom
-/
lemma isUnramified_smul_iff :
    IsUnramified k (σ • w) ↔ IsUnramified k w := by
  rw [isUnramified_iff]; rw [isUnramified_iff]; rw [isReal_smul_iff]; rw [comap_smul]; rw [← AlgEquiv.toAlgHom_toRingHom]; rw [AlgHom.comp_algebraMap]

variable (K) in
/--
Definition of `IsUnramifiedIn` / `IsUnramifiedIn` 的定义

English:
definition IsUnramifiedIn
  signature: (w : InfinitePlace k)
  body: forall v, comap v (algebraMap k K) = w -> IsUnramified k v

中文:
定义 IsUnramifiedIn
  签名: (w : InfinitePlace k)
  定义体: forall v, comap v (algebraMap k K) = w -> IsUnramified k v

Depends on / 依赖: IsUnramified, algebraMap
-/
def IsUnramifiedIn (w : InfinitePlace k) : Prop :=
  forall v, comap v (algebraMap k K) = w -> IsUnramified k v

/--
lemma `isUnramifiedIn_comap` / 引理 `isUnramifiedIn_comap`

English:
lemma isUnramifiedIn_comap
  given: [IsGalois k K] {w : InfinitePlace K}
  proof: by
  refine ⟨fun H => H _ rfl, fun H v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H

中文:
引理 isUnramifiedIn_comap
  条件: [是Galois k K] {w : InfinitePlace K}
  证明: by
  refine ⟨fun H => H _ rfl, fun H v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H

Depends on / 依赖: exists_smul_eq_of_comap_eq, isUnramified_smul_iff
-/
lemma isUnramifiedIn_comap [IsGalois k K] {w : InfinitePlace K} :
    (w.comap (algebraMap k K)).IsUnramifiedIn K ↔ w.IsUnramified k := by
  refine ⟨fun H => H _ rfl, fun H v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H

/--
lemma `even_card_aut_of_not_isUnramifiedIn` / 引理 `even_card_aut_of_not_isUnramifiedIn`

English:
lemma even_card_aut_of_not_isUnramifiedIn
  statement: [IsGalois k K]
  proof: by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

中文:
引理 even_card_aut_of_not_isUnramifiedIn
  结论: [是Galois k K]
  证明: by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

Depends on / 依赖: comap_surjective, even_card_aut_of_not_isUnramified, isUnramifiedIn_comap
-/
lemma even_card_aut_of_not_isUnramifiedIn [IsGalois k K]
    {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (Nat.card Gal(K/k)) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

/--
lemma `even_finrank_of_not_isUnramifiedIn` / 引理 `even_finrank_of_not_isUnramifiedIn`

English:
lemma even_finrank_of_not_isUnramifiedIn
  proof: by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

中文:
引理 even_finrank_of_not_isUnramifiedIn
  证明: by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

Depends on / 依赖: comap_surjective, even_finrank_of_not_isUnramified, isUnramifiedIn_comap
-/
lemma even_finrank_of_not_isUnramifiedIn
    [IsGalois k K] {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (finrank k K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

variable (k K)
variable [NumberField K]

open Finset in
open scoped Classical in
/--
lemma `card_isUnramified` / 引理 `card_isUnramified`

English:
lemma card_isUnramified
  given: [NumberField k] [IsGalois k K]
  proof: by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K})]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [mem_filter_univ] at hw
    trans #(MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [mem_filter_univ]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [@eq_comm _ (comap w' _)]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

中文:
引理 card_isUnramified
  条件: [数域 k] [是Galois k K]
  证明: by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K})]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [mem_filter_univ] at hw
    trans #(MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [mem_filter_univ]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [@eq_comm _ (comap w' _)]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

Depends on / 依赖: Finset, Finset.card_eq_sum_card_fiberwise, InfinitePlace, IsGalois, IsGalois.card_aut_eq_finrank, IsUnramifiedIn, MulAction, MulAction.orbit, Set.mem_toFinset, algebraMap, and_iff_, card_aut_eq_finrank, card_eq_sum_card_fiberwise, comap_surjective, eq_comm, mem_filter, mem_filter_univ, mem_orbit_iff, mem_toFinset, smul_eq_mul
-/
lemma card_isUnramified [NumberField k] [IsGalois k K] :
    #{w : InfinitePlace K | w.IsUnramified k} =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K := by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K})]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [mem_filter_univ] at hw
    trans #(MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [mem_filter_univ]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [@eq_comm _ (comap w' _)]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open Finset in
open scoped Classical in
/--
lemma `card_isUnramified_compl` / 引理 `card_isUnramified_compl`

English:
lemma card_isUnramified_compl
  given: [NumberField k] [IsGalois k K]
  proof: by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ)]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [compl_filter]; rw [mem_filter_univ] at hw
    trans Finset.card (MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [compl_filter]; rw [mem_filter_univ]; rw [@eq_comm _ (comap w' _)]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
        Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

中文:
引理 card_isUnramified_compl
  条件: [数域 k] [是Galois k K]
  证明: by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ)]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [compl_filter]; rw [mem_filter_univ] at hw
    trans Finset.card (MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [compl_filter]; rw [mem_filter_univ]; rw [@eq_comm _ (comap w' _)]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
        Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

Depends on / 依赖: Finset, Finset.card, Finset.card_eq_sum_card_fiberwise, InfinitePlace, IsGalois, IsGalois.card_aut_eq_finrank, IsUnramifiedIn, MulAction, MulAction.orbit, algebraMap, card_aut_eq_finrank, card_eq_sum_card_fiberwise, comap_surjective, compl_filter, eq_comm, mem_filter, mem_filter_univ, smul_eq_mul, sum_congr, sum_const
-/
lemma card_isUnramified_compl [NumberField k] [IsGalois k K] :
    #({w : InfinitePlace K | w.IsUnramified k} : Finset _)ᶜ =
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← IsGalois.card_aut_eq_finrank]; rw [Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ)]; rw [← smul_eq_mul]; rw [← sum_const]
  · refine sum_congr rfl (fun w hw => ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    rw [compl_filter]; rw [mem_filter_univ] at hw
    trans Finset.card (MulAction.orbit Gal(K/k) w).toFinset
    · congr; ext w'
      rw [mem_filter]; rw [compl_filter]; rw [mem_filter_univ]; rw [@eq_comm _ (comap w' _)]; rw [Set.mem_toFinset]; rw [mem_orbit_iff]; rw [and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [Nat.card_eq_fintype_card,
        ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
        Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open scoped Classical in
/--
lemma `card_eq_card_isUnramifiedIn` / 引理 `card_eq_card_isUnramifiedIn`

English:
lemma card_eq_card_isUnramifiedIn
  given: [NumberField k] [IsGalois k K]
  proof: by
  rw [← card_isUnramified]; rw [← card_isUnramified_compl]; rw [Finset.card_add_card_compl]

中文:
引理 card_eq_card_isUnramifiedIn
  条件: [数域 k] [是Galois k K]
  证明: by
  rw [← card_isUnramified]; rw [← card_isUnramified_compl]; rw [Finset.card_add_card_compl]

Depends on / 依赖: Finset, Finset.card_add_card_compl, card_add_card_compl, card_isUnramified, card_isUnramified_compl
-/
lemma card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K +
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← card_isUnramified]; rw [← card_isUnramified_compl]; rw [Finset.card_add_card_compl]

end NumberField.InfinitePlace

open NumberField

variable (k : Type*) [Field k] (K : Type*) [Field K] (F : Type*) [Field F]

variable [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]

/--
Definition of `IsUnramifiedAtInfinitePlaces` / `IsUnramifiedAtInfinitePlaces` 的定义

English:
class IsUnramifiedAtInfinitePlaces
  parameters: : Prop where
  axioms and operations (1):
    - isUnramified : forall w : InfinitePlace K, w.IsUnramified k

中文:
类 是UnramifiedAtInfinitePlaces
  参数: : 命题 where
  公理与运算 (1 个):
    - isUnramified : 对任意 w : InfinitePlace K, w.IsUnramified k
-/
class IsUnramifiedAtInfinitePlaces : Prop where
  isUnramified : forall w : InfinitePlace K, w.IsUnramified k

/--
Instance `IsUnramifiedAtInfinitePlaces.id` / 实例 `IsUnramifiedAtInfinitePlaces.id`

English:
instance IsUnramifiedAtInfinitePlaces.id
  signature: : IsUnramifiedAtInfinitePlaces K K where
  body: w.isUnramified_self

中文:
实例 是UnramifiedAtInfinitePlaces.id
  签名: : 是UnramifiedAtInfinitePlaces K K where
  定义体: w.isUnramified_self

Depends on / 依赖: isUnramified_self, w.isUnramified_self
-/
instance IsUnramifiedAtInfinitePlaces.id : IsUnramifiedAtInfinitePlaces K K where
  isUnramified w := w.isUnramified_self

/--
lemma `IsUnramifiedAtInfinitePlaces.trans` / 引理 `IsUnramifiedAtInfinitePlaces.trans`

English:
lemma IsUnramifiedAtInfinitePlaces.trans
  proof: Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)

中文:
引理 是UnramifiedAtInfinitePlaces.trans
  证明: Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)

Depends on / 依赖: Eq.trans, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, w.comap
-/
lemma IsUnramifiedAtInfinitePlaces.trans
    [h₁ : IsUnramifiedAtInfinitePlaces k K] [h₂ : IsUnramifiedAtInfinitePlaces K F] :
    IsUnramifiedAtInfinitePlaces k F where
  isUnramified w :=
    Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)

/--
lemma `IsUnramifiedAtInfinitePlaces.top` / 引理 `IsUnramifiedAtInfinitePlaces.top`

English:
lemma IsUnramifiedAtInfinitePlaces.top
  given: [h : IsUnramifiedAtInfinitePlaces k F]
  proof: (h.1 w).of_restrictScalars K

中文:
引理 是UnramifiedAtInfinitePlaces.top
  条件: [h : 是UnramifiedAtInfinitePlaces k F]
  证明: (h.1 w).of_restrictScalars K

Depends on / 依赖: of_restrictScalars
-/
lemma IsUnramifiedAtInfinitePlaces.top [h : IsUnramifiedAtInfinitePlaces k F] :
    IsUnramifiedAtInfinitePlaces K F where
  isUnramified w := (h.1 w).of_restrictScalars K

/--
lemma `IsUnramifiedAtInfinitePlaces.bot` / 引理 `IsUnramifiedAtInfinitePlaces.bot`

English:
lemma IsUnramifiedAtInfinitePlaces.bot
  statement: [h₁ : IsUnramifiedAtInfinitePlaces k F]
  proof: by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

中文:
引理 是UnramifiedAtInfinitePlaces.bot
  结论: [h₁ : 是UnramifiedAtInfinitePlaces k F]
  证明: by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

Depends on / 依赖: InfinitePlace, InfinitePlace.comap_surjective, comap_surjective
-/
lemma IsUnramifiedAtInfinitePlaces.bot [h₁ : IsUnramifiedAtInfinitePlaces k F]
    [Algebra.IsAlgebraic K F] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

variable {K}

/--
lemma `NumberField.InfinitePlace.isUnramified` / 引理 `NumberField.InfinitePlace.isUnramified`

English:
lemma NumberField.InfinitePlace.isUnramified
  statement: [IsUnramifiedAtInfinitePlaces k K]
  proof: IsUnramifiedAtInfinitePlaces.isUnramified w

中文:
引理 数域.InfinitePlace.isUnramified
  结论: [是UnramifiedAtInfinitePlaces k K]
  证明: IsUnramifiedAtInfinitePlaces.isUnramified w

Depends on / 依赖: IsUnramifiedAtInfinitePlaces, IsUnramifiedAtInfinitePlaces.isUnramified, isUnramified
-/
lemma NumberField.InfinitePlace.isUnramified [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace K) : IsUnramified k w := IsUnramifiedAtInfinitePlaces.isUnramified w

variable {k} (K)

/--
lemma `NumberField.InfinitePlace.isUnramifiedIn` / 引理 `NumberField.InfinitePlace.isUnramifiedIn`

English:
lemma NumberField.InfinitePlace.isUnramifiedIn
  statement: [IsUnramifiedAtInfinitePlaces k K]
  proof: fun v _ => v.isUnramified k

中文:
引理 数域.InfinitePlace.isUnramifiedIn
  结论: [是UnramifiedAtInfinitePlaces k K]
  证明: fun v _ => v.isUnramified k

Depends on / 依赖: isUnramified, v.isUnramified
-/
lemma NumberField.InfinitePlace.isUnramifiedIn [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace k) : IsUnramifiedIn K w := fun v _ => v.isUnramified k

variable {K}

/--
lemma `IsUnramifiedAtInfinitePlaces_of_odd_card_aut` / 引理 `IsUnramifiedAtInfinitePlaces_of_odd_card_aut`

English:
lemma IsUnramifiedAtInfinitePlaces_of_odd_card_aut
  statement: [IsGalois k K]
  proof: ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩

中文:
引理 IsUnramifiedAtInfinitePlaces_of_odd_card_aut
  结论: [是Galois k K]
  证明: ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩

Depends on / 依赖: InfinitePlace, InfinitePlace.even_card_aut_of_not_isUnramified, Nat.not_even_iff_odd, even_card_aut_of_not_isUnramified, not_even_iff_odd, not_not, not_not.mp
-/
lemma IsUnramifiedAtInfinitePlaces_of_odd_card_aut [IsGalois k K]
    (h : Odd (Nat.card Gal(K/k))) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩

/--
lemma `IsUnramifiedAtInfinitePlaces_of_odd_finrank` / 引理 `IsUnramifiedAtInfinitePlaces_of_odd_finrank`

English:
lemma IsUnramifiedAtInfinitePlaces_of_odd_finrank
  statement: [IsGalois k K]
  proof: ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

中文:
引理 IsUnramifiedAtInfinitePlaces_of_odd_finrank
  结论: [是Galois k K]
  证明: ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

Depends on / 依赖: InfinitePlace, InfinitePlace.even_finrank_of_not_isUnramified, Nat.not_even_iff_odd, even_finrank_of_not_isUnramified, not_even_iff_odd, not_not, not_not.mp
-/
lemma IsUnramifiedAtInfinitePlaces_of_odd_finrank [IsGalois k K]
    (h : Odd (Module.finrank k K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ => not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

variable (k K)

open Module in
/--
lemma `IsUnramifiedAtInfinitePlaces.card_infinitePlace` / 引理 `IsUnramifiedAtInfinitePlaces.card_infinitePlace`

English:
lemma IsUnramifiedAtInfinitePlaces.card_infinitePlace
  statement: [NumberField k] [NumberField K]
  proof: by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K)]; rw [Finset.filter_true_of_mem]; rw [Finset.card_univ]; rw [Finset.card_eq_zero.mpr]; rw [zero_mul]; rw [add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left]
  exact InfinitePlace.isUnramifiedIn K

中文:
引理 是UnramifiedAtInfinitePlaces.card_infinitePlace
  结论: [数域 k] [数域 K]
  证明: by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K)]; rw [Finset.filter_true_of_mem]; rw [Finset.card_univ]; rw [Finset.card_eq_zero.mpr]; rw [zero_mul]; rw [add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left]
  exact InfinitePlace.isUnramifiedIn K

Depends on / 依赖: Finset, Finset.card_eq_zero.mpr, Finset.card_univ, Finset.compl_univ, Finset.filter_true_of_mem, Finset.mem_univ, InfinitePlace, InfinitePlace.card_eq_card_isUnramifiedIn, InfinitePlace.isUnramifiedIn, add_zero, card_eq_card_isUnramifiedIn, card_eq_zero, card_univ, classical, compl_univ, filter_true_of_mem, forall_true_left, isUnramifiedIn, mem_univ, zero_mul
-/
lemma IsUnramifiedAtInfinitePlaces.card_infinitePlace [NumberField k] [NumberField K]
    [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace k) * finrank k K := by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K)]; rw [Finset.filter_true_of_mem]; rw [Finset.card_univ]; rw [Finset.card_eq_zero.mpr]; rw [zero_mul]; rw [add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left]
  exact InfinitePlace.isUnramifiedIn K

namespace NumberField.InfinitePlace

open ComplexEmbedding AbsoluteValue

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section LiesOver

variable (w : InfinitePlace L) (v : InfinitePlace K) [w.LiesOver v]

namespace LiesOver

instance {φ : K ->+* Complex} {ψ : L ->+* Complex} [ComplexEmbedding.LiesOver ψ φ] :
    AbsoluteValue.LiesOver (mk ψ).1 (mk φ).1 where
  comp_eq := by simp [← LiesOver.over ψ φ, ← coe_mk_comp]

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  statement: w.comap (algebraMap K L) = v
  proof: by
  ext
  simpa only [coe_apply] using! AbsoluteValue.ext_iff.1 (LiesOver.comp_eq w.1 v.1) _

中文:
定理 comap_eq
  结论: w.comap (algebraMap K L) = v
  证明: by
  ext
  simpa only [coe_apply] using! AbsoluteValue.ext_iff.1 (LiesOver.comp_eq w.1 v.1) _

Depends on / 依赖: AbsoluteValue, AbsoluteValue.ext_iff, LiesOver, LiesOver.comp_eq, coe_apply, comp_eq, ext_iff
-/
theorem comap_eq : w.comap (algebraMap K L) = v := by
  ext
  simpa only [coe_apply] using! AbsoluteValue.ext_iff.1 (LiesOver.comp_eq w.1 v.1) _

/--
theorem `mk_embedding_comp` / 定理 `mk_embedding_comp`

English:
theorem mk_embedding_comp
  statement: InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v
  proof: by
  rw [← comap_mk]; rw [w.mk_embedding]; rw [comap_eq w v]

中文:
定理 mk_embedding_comp
  结论: InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v
  证明: by
  rw [← comap_mk]; rw [w.mk_embedding]; rw [comap_eq w v]

Depends on / 依赖: comap_eq, comap_mk, mk_embedding, w.mk_embedding
-/
theorem mk_embedding_comp : InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk]; rw [w.mk_embedding]; rw [comap_eq w v]

/--
theorem `embedding_comp_eq_or_conjugate_embedding_comp_eq` / 定理 `embedding_comp_eq_or_conjugate_embedding_comp_eq`

English:
theorem embedding_comp_eq_or_conjugate_embedding_comp_eq
  proof: by
  cases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with
  | inl hl => exact .inl (hl ▸ congrArg embedding (mk_embedding_comp w v))
  | inr hr => simpa using .inr (hr ▸ congrArg embedding (mk_embedding_comp w v))

中文:
定理 embedding_comp_eq_or_conjugate_embedding_comp_eq
  证明: by
  cases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with
  | inl hl => exact .inl (hl ▸ congrArg embedding (mk_embedding_comp w v))
  | inr hr => simpa using .inr (hr ▸ congrArg embedding (mk_embedding_comp w v))

Depends on / 依赖: algebraMap, embedding, embedding_mk_eq, mk_embedding_comp, w.embedding.comp
-/
theorem embedding_comp_eq_or_conjugate_embedding_comp_eq :
    w.embedding.comp (algebraMap K L) = v.embedding ∨
      (conjugate w.embedding).comp (algebraMap K L) = v.embedding := by
  cases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with
  | inl hl => exact .inl (hl ▸ congrArg embedding (mk_embedding_comp w v))
  | inr hr => simpa using .inr (hr ▸ congrArg embedding (mk_embedding_comp w v))

variable {v}

/--
theorem `isComplex_of_isComplex_under` / 定理 `isComplex_of_isComplex_under`

English:
theorem isComplex_of_isComplex_under
  given: (hv : v.IsComplex)
  statement: w.IsComplex
  proof: by
  rw [isComplex_iff]; rw [ComplexEmbedding.isReal_iff]; rw [RingHom.ext_iff]; rw [not_forall] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← comap_eq w v]; rw [← mk_embedding w]; rw [comap_mk] at hx
  rcases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with (_ | _) <;> aesop

中文:
定理 isComplex_of_isComplex_under
  条件: (hv : v.是复形)
  结论: w.是复形
  证明: by
  rw [isComplex_iff]; rw [ComplexEmbedding.isReal_iff]; rw [RingHom.ext_iff]; rw [not_forall] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← comap_eq w v]; rw [← mk_embedding w]; rw [comap_mk] at hx
  rcases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with (_ | _) <;> aesop

Depends on / 依赖: ComplexEmbedding, ComplexEmbedding.isReal_iff, RingHom, RingHom.ext_iff, algebraMap, comap_eq, comap_mk, embedding, embedding_mk_eq, ext_iff, isComplex_iff, isReal_iff, mk_embedding, not_forall, w.embedding.comp
-/
theorem isComplex_of_isComplex_under (hv : v.IsComplex) : w.IsComplex := by
  rw [isComplex_iff]; rw [ComplexEmbedding.isReal_iff]; rw [RingHom.ext_iff]; rw [not_forall] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← comap_eq w v]; rw [← mk_embedding w]; rw [comap_mk] at hx
  rcases embedding_mk_eq (w.embedding.comp (algebraMap K L)) with (_ | _) <;> aesop

/--
theorem `isReal_of_isReal_over` / 定理 `isReal_of_isReal_over`

English:
theorem isReal_of_isReal_over
  given: (hw : w.IsReal)
  statement: v.IsReal
  proof: by
  rw [← not_isComplex_iff_isReal] at hw ⊢
  exact mt (isComplex_of_isComplex_under w) hw

中文:
定理 is实数_of_is实数_over
  条件: (hw : w.Is实数)
  结论: v.Is实数
  证明: by
  rw [← not_isComplex_iff_isReal] at hw ⊢
  exact mt (isComplex_of_isComplex_under w) hw

Depends on / 依赖: isComplex_of_isComplex_under, not_isComplex_iff_isReal
-/
theorem isReal_of_isReal_over (hw : w.IsReal) : v.IsReal := by
  rw [← not_isComplex_iff_isReal] at hw ⊢
  exact mt (isComplex_of_isComplex_under w) hw

end LiesOver

/--
theorem `IsRamified.liesOver_isReal_under` / 定理 `IsRamified.liesOver_isReal_under`

English:
theorem IsRamified.liesOver_isReal_under
  given: (hw : w.IsRamified K)
  proof: LiesOver.comap_eq w v ▸ (isRamified_iff.1 hw).2

中文:
定理 IsRamified.liesOver_is实数_under
  条件: (hw : w.IsRamified K)
  证明: LiesOver.comap_eq w v ▸ (isRamified_iff.1 hw).2

Depends on / 依赖: LiesOver, LiesOver.comap_eq, comap_eq, isRamified_iff
-/
theorem IsRamified.liesOver_isReal_under (hw : w.IsRamified K) :
    v.IsReal := LiesOver.comap_eq w v ▸ (isRamified_iff.1 hw).2

/--
theorem `IsUnramified.liesOver_isReal_over` / 定理 `IsUnramified.liesOver_isReal_over`

English:
theorem IsUnramified.liesOver_isReal_over
  given: (hw : w.IsUnramified K) (hv : v.IsReal)
  statement: w.IsReal
  proof: (InfinitePlace.isUnramified_iff.1 hw).resolve_right
    (by simpa [LiesOver.comap_eq w v] using not_isComplex_iff_isReal.2 hv)

中文:
定理 IsUnramified.liesOver_is实数_over
  条件: (hw : w.IsUnramified K) (hv : v.Is实数)
  结论: w.Is实数
  证明: (InfinitePlace.isUnramified_iff.1 hw).resolve_right
    (by simpa [LiesOver.comap_eq w v] using not_isComplex_iff_isReal.2 hv)

Depends on / 依赖: InfinitePlace, InfinitePlace.isUnramified_iff, LiesOver, LiesOver.comap_eq, comap_eq, isUnramified_iff, not_isComplex_iff_isReal, resolve_right
-/
theorem IsUnramified.liesOver_isReal_over (hw : w.IsUnramified K) (hv : v.IsReal) : w.IsReal :=
  (InfinitePlace.isUnramified_iff.1 hw).resolve_right
    (by simpa [LiesOver.comap_eq w v] using not_isComplex_iff_isReal.2 hv)

end LiesOver

section placesOver

variable (v : InfinitePlace K) (L)

/--
Definition of `placesOver` / `placesOver` 的定义

English:
definition placesOver
  signature: : Set (InfinitePlace L)
  body: { w | w.LiesOver v }

中文:
定义 placesOver
  签名: : 集合 (InfinitePlace L)
  定义体: { w | w.LiesOver v }

Depends on / 依赖: LiesOver, w.LiesOver
-/
def placesOver : Set (InfinitePlace L) := { w | w.LiesOver v }

/--
Definition of `unramifiedPlacesOver` / `unramifiedPlacesOver` 的定义

English:
definition unramifiedPlacesOver
  signature: : Set (InfinitePlace L)
  body: { w | w.LiesOver v ∧ w.IsUnramified K }

中文:
定义 unramifiedPlacesOver
  签名: : 集合 (InfinitePlace L)
  定义体: { w | w.LiesOver v ∧ w.IsUnramified K }

Depends on / 依赖: IsUnramified, LiesOver, w.IsUnramified, w.LiesOver
-/
def unramifiedPlacesOver : Set (InfinitePlace L) := { w | w.LiesOver v ∧ w.IsUnramified K }

/--
Definition of `ramifiedPlacesOver` / `ramifiedPlacesOver` 的定义

English:
definition ramifiedPlacesOver
  signature: : Set (InfinitePlace L)
  body: { w | w.LiesOver v ∧ w.IsRamified K }

中文:
定义 ramifiedPlacesOver
  签名: : 集合 (InfinitePlace L)
  定义体: { w | w.LiesOver v ∧ w.IsRamified K }

Depends on / 依赖: IsRamified, LiesOver, w.IsRamified, w.LiesOver
-/
def ramifiedPlacesOver : Set (InfinitePlace L) := { w | w.LiesOver v ∧ w.IsRamified K }

variable {L} {v} {w : InfinitePlace L}

/--
theorem `mk_mem_unramifiedPlacesOver` / 定理 `mk_mem_unramifiedPlacesOver`

English:
theorem mk_mem_unramifiedPlacesOver
  given: {φ : L ->+* Complex} (h : φ in unmixedEmbeddingsOver L (v.embedding))
  proof: ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩,
    h.2.mk_isUnramified⟩

中文:
定理 mk_mem_unramifiedPlacesOver
  条件: {φ : L ->+* 复形} (h : φ in unmixedEmbeddingsOver L (v.embedding))
  证明: ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩,
    h.2.mk_isUnramified⟩

Depends on / 依赖: LiesOver, LiesOver.comp_eq, comp_eq, embedding, mk_embedding, mk_isUnramified, v.embedding
-/
theorem mk_mem_unramifiedPlacesOver {φ : L ->+* Complex} (h : φ in unmixedEmbeddingsOver L (v.embedding)) :
    mk φ in unramifiedPlacesOver L v :=
  ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩,
    h.2.mk_isUnramified⟩

/--
theorem `liesOver_embedding_of_mem_ramifiedPlacesOver` / 定理 `liesOver_embedding_of_mem_ramifiedPlacesOver`

English:
theorem liesOver_embedding_of_mem_ramifiedPlacesOver
  given: (hw : w in ramifiedPlacesOver L v)
  proof: have := hw.1; hw.2.comap_embedding ▸ congrArg embedding (LiesOver.comap_eq w v)

中文:
定理 liesOver_embedding_of_mem_ramifiedPlacesOver
  条件: (hw : w in ramifiedPlacesOver L v)
  证明: have := hw.1; hw.2.comap_embedding ▸ congrArg embedding (LiesOver.comap_eq w v)

Depends on / 依赖: LiesOver, LiesOver.comap_eq, comap_embedding, comap_eq, embedding
-/
theorem liesOver_embedding_of_mem_ramifiedPlacesOver (hw : w in ramifiedPlacesOver L v) :
    ComplexEmbedding.LiesOver w.embedding v.embedding where
  over := have := hw.1; hw.2.comap_embedding ▸ congrArg embedding (LiesOver.comap_eq w v)

/--
theorem `liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver` / 定理 `liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver`

English:
theorem liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver
  proof: have := hw.1; hw.2.comap_embedding_conjugate ▸ congrArg embedding (LiesOver.comap_eq w v)

中文:
定理 liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver
  证明: have := hw.1; hw.2.comap_embedding_conjugate ▸ congrArg embedding (LiesOver.comap_eq w v)

Depends on / 依赖: LiesOver, LiesOver.comap_eq, comap_embedding_conjugate, comap_eq, embedding
-/
theorem liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver
    (hw : w in ramifiedPlacesOver L v) :
    ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding where
  over := have := hw.1; hw.2.comap_embedding_conjugate ▸ congrArg embedding (LiesOver.comap_eq w v)

/--
theorem `mk_mem_ramifiedPlacesOver` / 定理 `mk_mem_ramifiedPlacesOver`

English:
theorem mk_mem_ramifiedPlacesOver
  given: {φ : L ->+* Complex} (h : φ in mixedEmbeddingsOver L (v.embedding))
  proof: ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩, h.2.mk_isRamified⟩

中文:
定理 mk_mem_ramifiedPlacesOver
  条件: {φ : L ->+* 复形} (h : φ in mixedEmbeddingsOver L (v.embedding))
  证明: ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩, h.2.mk_isRamified⟩

Depends on / 依赖: LiesOver, LiesOver.comp_eq, comp_eq, embedding, mk_embedding, mk_isRamified, v.embedding
-/
theorem mk_mem_ramifiedPlacesOver {φ : L ->+* Complex} (h : φ in mixedEmbeddingsOver L (v.embedding)) :
    mk φ in ramifiedPlacesOver L v :=
  ⟨⟨have := h.1; mk_embedding v ▸ LiesOver.comp_eq (mk φ).1 (mk v.embedding).1⟩, h.2.mk_isRamified⟩

variable (w)

/--
theorem `embedding_mem_mixedEmbeddingsOver` / 定理 `embedding_mem_mixedEmbeddingsOver`

English:
theorem embedding_mem_mixedEmbeddingsOver
  given: (hw : w in ramifiedPlacesOver L v)
  proof: ⟨liesOver_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_embedding⟩

中文:
定理 embedding_mem_mixedEmbeddingsOver
  条件: (hw : w in ramifiedPlacesOver L v)
  证明: ⟨liesOver_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_embedding⟩

Depends on / 依赖: isMixed_embedding, liesOver_embedding_of_mem_ramifiedPlacesOver
-/
theorem embedding_mem_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver L v) :
    w.embedding in mixedEmbeddingsOver L (v.embedding) :=
  ⟨liesOver_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_embedding⟩

/--
theorem `conjugate_embedding_mem_mixedEmbeddingsOver` / 定理 `conjugate_embedding_mem_mixedEmbeddingsOver`

English:
theorem conjugate_embedding_mem_mixedEmbeddingsOver
  given: (hw : w in ramifiedPlacesOver L v)
  proof: ⟨liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_conjugate_embedding⟩

中文:
定理 conjugate_embedding_mem_mixedEmbeddingsOver
  条件: (hw : w in ramifiedPlacesOver L v)
  证明: ⟨liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_conjugate_embedding⟩

Depends on / 依赖: isMixed_conjugate_embedding, liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver
-/
theorem conjugate_embedding_mem_mixedEmbeddingsOver (hw : w in ramifiedPlacesOver L v) :
    conjugate w.embedding in mixedEmbeddingsOver L (v.embedding) :=
  ⟨liesOver_conjugate_embedding_of_mem_ramifiedPlacesOver hw, hw.2.isMixed_conjugate_embedding⟩

variable (L) (v)

/--
theorem `disjoint_ramifiedPlacesOver_unramifiedPlacesOver` / 定理 `disjoint_ramifiedPlacesOver_unramifiedPlacesOver`

English:
theorem disjoint_ramifiedPlacesOver_unramifiedPlacesOver
  proof: by
  grind [ramifiedPlacesOver, unramifiedPlacesOver]

中文:
定理 disjoint_ramifiedPlacesOver_unramifiedPlacesOver
  证明: by
  grind [ramifiedPlacesOver, unramifiedPlacesOver]

Depends on / 依赖: ramifiedPlacesOver, unramifiedPlacesOver
-/
theorem disjoint_ramifiedPlacesOver_unramifiedPlacesOver :
    Disjoint (ramifiedPlacesOver L v) (unramifiedPlacesOver L v) := by
  grind [ramifiedPlacesOver, unramifiedPlacesOver]

/--
theorem `union_ramifiedPlacesOver_unramifiedPlacesOver` / 定理 `union_ramifiedPlacesOver_unramifiedPlacesOver`

English:
theorem union_ramifiedPlacesOver_unramifiedPlacesOver
  proof: by
  rw [placesOver]; rw [ramifiedPlacesOver]; rw [unramifiedPlacesOver]; rw [← Set.ofPred_or]
  grind

中文:
定理 union_ramifiedPlacesOver_unramifiedPlacesOver
  证明: by
  rw [placesOver]; rw [ramifiedPlacesOver]; rw [unramifiedPlacesOver]; rw [← Set.ofPred_or]
  grind

Depends on / 依赖: Set.ofPred_or, ofPred_or, placesOver, ramifiedPlacesOver, unramifiedPlacesOver
-/
theorem union_ramifiedPlacesOver_unramifiedPlacesOver :
    (ramifiedPlacesOver L v) union (unramifiedPlacesOver L v) = placesOver L v := by
  rw [placesOver]; rw [ramifiedPlacesOver]; rw [unramifiedPlacesOver]; rw [← Set.ofPred_or]
  grind

/--
theorem `bijOn_sumElim_conjugate` / 定理 `bijOn_sumElim_conjugate`

English:
theorem bijOn_sumElim_conjugate
  proof: ⟨.sumElim embedding_mem_mixedEmbeddingsOver conjugate_embedding_mem_mixedEmbeddingsOver,
    (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h => h.2.ne_conjugate), fun ψ h => by cases embedding_mk_eq ψ with
        | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
        | inr hr => simpa using .inr ⟨mk ψ, mk_mem_ramifiedPlacesOver h, by aesop⟩⟩

中文:
定理 bijOn_sumElim_conjugate
  证明: ⟨.sumElim embedding_mem_mixedEmbeddingsOver conjugate_embedding_mem_mixedEmbeddingsOver,
    (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h => h.2.ne_conjugate), fun ψ h => by cases embedding_mk_eq ψ with
        | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
        | inr hr => simpa using .inr ⟨mk ψ, mk_mem_ramifiedPlacesOver h, by aesop⟩⟩

Depends on / 依赖: conjugate_embedding_mem_mixedEmbeddingsOver, embedding_injective, embedding_mem_mixedEmbeddingsOver, embedding_mk_eq, injOn.sumElim, mk_mem_ramifiedPlacesOver, ne_conjugate, star_injective, star_injective.comp, sumElim
-/
theorem bijOn_sumElim_conjugate :
    (Set.sumEquiv.symm (ramifiedPlacesOver L v, ramifiedPlacesOver L v)).BijOn
      (Sum.elim embedding (conjugate ∘ embedding)) (mixedEmbeddingsOver L v.embedding) :=
  ⟨.sumElim embedding_mem_mixedEmbeddingsOver conjugate_embedding_mem_mixedEmbeddingsOver,
    (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h => h.2.ne_conjugate), fun ψ h => by cases embedding_mk_eq ψ with
        | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
        | inr hr => simpa using .inr ⟨mk ψ, mk_mem_ramifiedPlacesOver h, by aesop⟩⟩

/--
theorem `ramifiedPlacesOver_ncard` / 定理 `ramifiedPlacesOver_ncard`

English:
theorem ramifiedPlacesOver_ncard
  proof: by
  rw [← (bijOn_sumElim_conjugate L v).ncard_eq]; rw [two_mul]; rw [Set.ncard_sumEquiv_symm_apply]

中文:
定理 ramifiedPlacesOver_ncard
  证明: by
  rw [← (bijOn_sumElim_conjugate L v).ncard_eq]; rw [two_mul]; rw [Set.ncard_sumEquiv_symm_apply]

Depends on / 依赖: Set.ncard_sumEquiv_symm_apply, bijOn_sumElim_conjugate, ncard_eq, ncard_sumEquiv_symm_apply, two_mul
-/
theorem ramifiedPlacesOver_ncard :
    2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).ncard := by
  rw [← (bijOn_sumElim_conjugate L v).ncard_eq]; rw [two_mul]; rw [Set.ncard_sumEquiv_symm_apply]

variable {L}

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def embeddingConjugateIte
  body: if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding

中文:
定义 noncomputable
  签名: def embeddingConjugateIte
  定义体: if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding
-/
private noncomputable def embeddingConjugateIte : L ->+* Complex :=
  if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding

variable {v w}

/--
theorem `embeddingConjugateIte_pos` / 定理 `embeddingConjugateIte_pos`

English:
theorem embeddingConjugateIte_pos
  given: (h : ComplexEmbedding.LiesOver w.embedding v.embedding)
  proof: by simp [embeddingConjugateIte, h]

中文:
定理 embeddingConjugateIte_pos
  条件: (h : ComplexEmbedding.LiesOver w.embedding v.embedding)
  证明: by simp [embeddingConjugateIte, h]
-/
private theorem embeddingConjugateIte_pos (h : ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte v w = w.embedding := by simp [embeddingConjugateIte, h]

/--
theorem `embeddingConjugateIte_neg` / 定理 `embeddingConjugateIte_neg`

English:
theorem embeddingConjugateIte_neg
  given: (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding)
  proof: by simp [embeddingConjugateIte, h]

中文:
定理 embeddingConjugateIte_neg
  条件: (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding)
  证明: by simp [embeddingConjugateIte, h]
-/
private theorem embeddingConjugateIte_neg (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte v w = conjugate w.embedding := by simp [embeddingConjugateIte, h]

variable (L v)

/--
theorem `mapsTo_embeddingConjugateIte` / 定理 `mapsTo_embeddingConjugateIte`

English:
theorem mapsTo_embeddingConjugateIte
  statement: (unramifiedPlacesOver L v).MapsTo
  proof: by
  rintro w ⟨_, hw⟩
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left
        (liesOver_iff.not.1 h)⟩, hw.isUnmixed_conjugate⟩

中文:
定理 mapsTo_embeddingConjugateIte
  结论: (unramifiedPlacesOver L v).映射到
  证明: by
  rintro w ⟨_, hw⟩
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left
        (liesOver_iff.not.1 h)⟩, hw.isUnmixed_conjugate⟩
-/
private theorem mapsTo_embeddingConjugateIte : (unramifiedPlacesOver L v).MapsTo
    (embeddingConjugateIte v) (unmixedEmbeddingsOver L v.embedding) := by
  rintro w ⟨_, hw⟩
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left
        (liesOver_iff.not.1 h)⟩, hw.isUnmixed_conjugate⟩

/--
theorem `surjOn_embeddingConjugateIte` / 定理 `surjOn_embeddingConjugateIte`

English:
theorem surjOn_embeddingConjugateIte
  statement: (unramifiedPlacesOver L v).SurjOn
  proof: by
  refine fun ψ h => ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · simpa [embeddingConjugateIte, hψ] using fun ⟨_⟩ =>
h.2.isReal_iff_isReal.1 by have := h.1.over; aesop

中文:
定理 surjOn_embeddingConjugateIte
  结论: (unramifiedPlacesOver L v).满射限制
  证明: by
  refine fun ψ h => ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · simpa [embeddingConjugateIte, hψ] using fun ⟨_⟩ =>
h.2.isReal_iff_isReal.1 by have := h.1.over; aesop
-/
private theorem surjOn_embeddingConjugateIte : (unramifiedPlacesOver L v).SurjOn
    (embeddingConjugateIte v) (unmixedEmbeddingsOver L v.embedding) := by
  refine fun ψ h => ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · simpa [embeddingConjugateIte, hψ] using fun ⟨_⟩ =>
h.2.isReal_iff_isReal.1 by have := h.1.over; aesop

open scoped Classical in
/--
theorem `bijOn_extensionIte` / 定理 `bijOn_extensionIte`

English:
theorem bijOn_extensionIte
  statement: (unramifiedPlacesOver L v).BijOn (embeddingConjugateIte v)
  proof: ⟨mapsTo_embeddingConjugateIte L v, ((embedding_injective _).ite (star_injective.comp
    (embedding_injective _)) (fun _ _ => eq_of_embedding_eq_conjugate L)).injOn,
      surjOn_embeddingConjugateIte L v⟩

中文:
定理 bijOn_extensionIte
  结论: (unramifiedPlacesOver L v).双射限制 (embeddingConjugateIte v)
  证明: ⟨mapsTo_embeddingConjugateIte L v, ((embedding_injective _).ite (star_injective.comp
    (embedding_injective _)) (fun _ _ => eq_of_embedding_eq_conjugate L)).injOn,
      surjOn_embeddingConjugateIte L v⟩
-/
private theorem bijOn_extensionIte : (unramifiedPlacesOver L v).BijOn (embeddingConjugateIte v)
    (unmixedEmbeddingsOver L v.embedding) :=
  ⟨mapsTo_embeddingConjugateIte L v, ((embedding_injective _).ite (star_injective.comp
    (embedding_injective _)) (fun _ _ => eq_of_embedding_eq_conjugate L)).injOn,
      surjOn_embeddingConjugateIte L v⟩

/--
theorem `unramifiedPlacesOver_ncard` / 定理 `unramifiedPlacesOver_ncard`

English:
theorem unramifiedPlacesOver_ncard
  proof: by
  rw [(bijOn_extensionIte L v).ncard_eq]

中文:
定理 unramifiedPlacesOver_ncard
  证明: by
  rw [(bijOn_extensionIte L v).ncard_eq]

Depends on / 依赖: bijOn_extensionIte, ncard_eq
-/
theorem unramifiedPlacesOver_ncard :
    (unramifiedPlacesOver L v).ncard = (unmixedEmbeddingsOver L v.embedding).ncard := by
  rw [(bijOn_extensionIte L v).ncard_eq]

open Finset in
/--
theorem `unramifedPlacesOver_ncard_add_eq_finrank` / 定理 `unramifedPlacesOver_ncard_add_eq_finrank`

English:
theorem unramifedPlacesOver_ncard_add_eq_finrank
  given: [NumberField K] [NumberField L]
  proof: by
  classical
  let : Algebra K Complex := v.embedding.toAlgebra
  rw [← AlgHom.card K L Complex]; rw [ramifiedPlacesOver_ncard]; rw [unramifiedPlacesOver_ncard]; rw [← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding)]; rw [union_unmixedEmbeddingsOver_mixedEmbeddingsOver]; rw [Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ => by simpa using ⟨by aesop⟩)
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ => ?_)).symm
  simp only [Set.Finite.toFinset_ofPred, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hψ
  exact ⟨⟨ψ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

中文:
定理 unramifedPlacesOver_ncard_add_eq_finrank
  条件: [数域 K] [数域 L]
  证明: by
  classical
  let : Algebra K Complex := v.embedding.toAlgebra
  rw [← AlgHom.card K L Complex]; rw [ramifiedPlacesOver_ncard]; rw [unramifiedPlacesOver_ncard]; rw [← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding)]; rw [union_unmixedEmbeddingsOver_mixedEmbeddingsOver]; rw [Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ => by simpa using ⟨by aesop⟩)
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ => ?_)).symm
  simp only [Set.Finite.toFinset_ofPred, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hψ
  exact ⟨⟨ψ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

Depends on / 依赖: AlgHom, AlgHom.card, AlgHom.coe_ringHom_injective.injOn, AlgHom.toRingHom, Algebra, Finite, Set.Finite.toFinset_, Set.ncard_eq_toFinset_card, Set.ncard_union_eq, card_nbij, classical, coe_ringHom_injective, disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver, embedding, ncard_eq_toFinset_card, ncard_union_eq, ramifiedPlacesOver_ncard, toAlgebra, toFinset_, toRingHom
-/
theorem unramifedPlacesOver_ncard_add_eq_finrank [NumberField K] [NumberField L] :
    (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L := by
  classical
  let : Algebra K Complex := v.embedding.toAlgebra
  rw [← AlgHom.card K L Complex]; rw [ramifiedPlacesOver_ncard]; rw [unramifiedPlacesOver_ncard]; rw [← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding)]; rw [union_unmixedEmbeddingsOver_mixedEmbeddingsOver]; rw [Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ => by simpa using ⟨by aesop⟩)
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ => ?_)).symm
  simp only [Set.Finite.toFinset_ofPred, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hψ
  exact ⟨⟨ψ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

end placesOver

end NumberField.InfinitePlace
