/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Essentially of finite type algebras

## Main results
- `Algebra.EssFiniteType`: The class of essentially of finite type algebras. An `R`-algebra is
  essentially of finite type if it is the localization of an algebra of finite type.
- `Algebra.EssFiniteType.algHom_ext`: The algebra homomorphisms out from an algebra essentially of
  finite type is determined by its values on a finite set.

-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/--
Definition of `EssFiniteType` / `EssFiniteType` 的定义

English:
class EssFiniteType
  parameters: : Prop where
  axioms and operations (1):
    - cond : exists s : Finset S, IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S

中文:
类 EssFiniteType
  参数: : 命题 where
  公理与运算 (1 个):
    - cond : 存在 s : 有限集 S, 是Localization ((是单位.submonoid S).comap (algebraMap (adjoin R (s : 集合 S)) S)) S
-/
class EssFiniteType : Prop where
  cond : exists s : Finset S,
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S

/-- Let `S` be an `R`-algebra essentially of finite type, this is a choice of a finset `s ⊆ S`
such that `S` is the localization of `R[s]`. -/
noncomputable
/--
Definition of `EssFiniteType.finset` / `EssFiniteType.finset` 的定义

English:
definition EssFiniteType.finset
  signature: [h : EssFiniteType R S]
  body: h.cond.choose

中文:
定义 EssFiniteType.finset
  签名: [h : EssFiniteType R S]
  定义体: h.cond.choose

Depends on / 依赖: h.cond.choose
-/
def EssFiniteType.finset [h : EssFiniteType R S] : Finset S := h.cond.choose

/-- A choice of a subalgebra of finite type in an essentially of finite type algebra, such that
its localization is the whole ring. -/
noncomputable
/--
Definition of `EssFiniteType.subalgebra` / `EssFiniteType.subalgebra` 的定义

English:
abbreviation EssFiniteType.subalgebra
  signature: [EssFiniteType R S]
  body: Algebra.adjoin R (finset R S : Set S)

中文:
缩写 EssFiniteType.subalgebra
  签名: [EssFiniteType R S]
  定义体: Algebra.adjoin R (finset R S : Set S)

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin, finset
-/
abbrev EssFiniteType.subalgebra [EssFiniteType R S] : Subalgebra R S :=
  Algebra.adjoin R (finset R S : Set S)

/--
lemma `EssFiniteType.adjoin_mem_finset` / 引理 `EssFiniteType.adjoin_mem_finset`

English:
lemma EssFiniteType.adjoin_mem_finset
  given: [EssFiniteType R S]
  proof: adjoin_adjoin_coe_preimage

中文:
引理 EssFiniteType.adjoin_mem_finset
  条件: [EssFiniteType R S]
  证明: adjoin_adjoin_coe_preimage

Depends on / 依赖: adjoin_adjoin_coe_preimage
-/
lemma EssFiniteType.adjoin_mem_finset [EssFiniteType R S] :
    adjoin R { x : subalgebra R S | x.1 in finset R S } = ⊤ := adjoin_adjoin_coe_preimage

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssFiniteType
  signature: R S] : Algebra.FiniteType R (EssFiniteType.subalgebra R S)
  body: by
  constructor
  rw [Subalgebra.fg_top]; rw [EssFiniteType.subalgebra]
  exact ⟨_, rfl⟩

中文:
实例 [EssFiniteType
  签名: R S] : 代数.有限型 R (EssFiniteType.subalgebra R S)
  定义体: by
  constructor
  rw [Subalgebra.fg_top]; rw [EssFiniteType.subalgebra]
  exact ⟨_, rfl⟩

Depends on / 依赖: EssFiniteType, EssFiniteType.subalgebra, Subalgebra, Subalgebra.fg_top, fg_top, subalgebra
-/
instance [EssFiniteType R S] : Algebra.FiniteType R (EssFiniteType.subalgebra R S) := by
  constructor
  rw [Subalgebra.fg_top]; rw [EssFiniteType.subalgebra]
  exact ⟨_, rfl⟩

/-- A submonoid of `EssFiniteType.subalgebra R S`, whose localization is the whole algebra `S`. -/
noncomputable
/--
Definition of `EssFiniteType.submonoid` / `EssFiniteType.submonoid` 的定义

English:
definition EssFiniteType.submonoid
  signature: [EssFiniteType R S]
  body: ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))

中文:
定义 EssFiniteType.submonoid
  签名: [EssFiniteType R S]
  定义体: ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))

Depends on / 依赖: EssFiniteType, EssFiniteType.subalgebra, IsUnit, IsUnit.submonoid, algebraMap, subalgebra, submonoid
-/
def EssFiniteType.submonoid [EssFiniteType R S] : Submonoid (EssFiniteType.subalgebra R S) :=
  ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))

/--
Instance `EssFiniteType.isLocalization` / 实例 `EssFiniteType.isLocalization`

English:
instance EssFiniteType.isLocalization
  signature: [h : EssFiniteType R S]
  body: h.cond.choose_spec

中文:
实例 EssFiniteType.isLocalization
  签名: [h : EssFiniteType R S]
  定义体: h.cond.choose_spec

Depends on / 依赖: choose_spec, h.cond.choose_spec
-/
instance EssFiniteType.isLocalization [h : EssFiniteType R S] :
    IsLocalization (EssFiniteType.submonoid R S) S :=
  h.cond.choose_spec

/--
lemma `essFiniteType_cond_iff` / 引理 `essFiniteType_cond_iff`

English:
lemma essFiniteType_cond_iff
  given: (σ : Finset S)
  proof: by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.1.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor; constructor
    · exact fun y => y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intro x y e
      e

中文:
引理 essFiniteType_cond_iff
  条件: (σ : 有限集 S)
  证明: by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.1.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor; constructor
    · exact fun y => y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intro x y e
      e

Depends on / 依赖: Subtype, Subtype.ext, y.prop
-/
lemma essFiniteType_cond_iff (σ : Finset S) :
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (σ : Set S)) S)) S ↔
    (forall s : S, exists t in Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t in Algebra.adjoin R (σ : Set S)) := by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.1.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor; constructor
    · exact fun y => y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intro x y e
      exact ⟨1, by simpa using Subtype.ext e⟩

/--
lemma `essFiniteType_iff` / 引理 `essFiniteType_iff`

English:
lemma essFiniteType_iff
  proof: by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ => ⟨a, b⟩

中文:
引理 essFiniteType_iff
  证明: by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ => ⟨a, b⟩

Depends on / 依赖: essFiniteType_cond_iff, simp_rw
-/
lemma essFiniteType_iff :
    EssFiniteType R S ↔ exists (σ : Finset S),
      (forall s : S, exists t in Algebra.adjoin R (σ : Set S),
        IsUnit t ∧ s * t in Algebra.adjoin R (σ : Set S)) := by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ => ⟨a, b⟩

/--
Instance `EssFiniteType.of_finiteType` / 实例 `EssFiniteType.of_finiteType`

English:
instance EssFiniteType.of_finiteType
  signature: [FiniteType R S]
  body: by
  obtain ⟨s, hs⟩ := ‹FiniteType R S›
  rw [essFiniteType_iff]
  exact ⟨s, fun _ => by simpa only [hs, mem_top, and_true, true_and] using ⟨1, isUnit_one⟩⟩

中文:
实例 EssFiniteType.of_finiteType
  签名: [有限型 R S]
  定义体: by
  obtain ⟨s, hs⟩ := ‹FiniteType R S›
  rw [essFiniteType_iff]
  exact ⟨s, fun _ => by simpa only [hs, mem_top, and_true, true_and] using ⟨1, isUnit_one⟩⟩

Depends on / 依赖: FiniteType, and_true, essFiniteType_iff, isUnit_one, mem_top, true_and
-/
instance EssFiniteType.of_finiteType [FiniteType R S] : EssFiniteType R S := by
  obtain ⟨s, hs⟩ := ‹FiniteType R S›
  rw [essFiniteType_iff]
  exact ⟨s, fun _ => by simpa only [hs, mem_top, and_true, true_and] using ⟨1, isUnit_one⟩⟩

variable {R} in
/--
lemma `EssFiniteType.of_isLocalization` / 引理 `EssFiniteType.of_isLocalization`

English:
lemma EssFiniteType.of_isLocalization
  given: (M : Submonoid R) [IsLocalization M S]
  proof: by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

中文:
引理 EssFiniteType.of_isLocalization
  条件: (M : 子幺半群 R) [是Localization M S]
  证明: by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

Depends on / 依赖: Algebra, Algebra.adjoin_empty, Algebra.mem_bot, Finset, Finset.coe_empty, IsLocalization, IsLocalization.map_units, IsLocalization.surj, Set.mem_range, adjoin_empty, coe_empty, e.symm, essFiniteType_iff, exists_exists_eq_and, map_units, mem_bot, mem_range
-/
lemma EssFiniteType.of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    EssFiniteType R S := by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

/--
lemma `EssFiniteType.of_id` / 引理 `EssFiniteType.of_id`

English:
lemma EssFiniteType.of_id
  statement: EssFiniteType R R
  proof: inferInstance

中文:
引理 EssFiniteType.of_id
  结论: EssFiniteType R R
  证明: inferInstance
-/
lemma EssFiniteType.of_id : EssFiniteType R R := inferInstance

section
variable [Algebra S T] [IsScalarTower R S T]

/--
lemma `EssFiniteType.aux` / 引理 `EssFiniteType.aux`

English:
lemma EssFiniteType.aux
  statement: (σ : Subalgebra R S)
  proof: by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw

中文:
引理 EssFiniteType.aux
  结论: (σ : 子代数 R S)
  证明: by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw

Depends on / 依赖: Algebra, Algebra.adjoin_induction, Algebra.mem_sup_left, Algebra.mem_sup_right, Algebra.smul_def, Algebra.subset_adjoin, Subalgebra, Subalgebra.one_mem, adjoin_induction, isUnit_one, map_mul, mem_sup_left, mem_sup_right, mul_comm, mul_mem, mul_smul, one_mem, one_smul, smul_add, smul_def
-/
lemma EssFiniteType.aux (σ : Subalgebra R S)
    (hσ : forall s : S, exists t in σ, IsUnit t ∧ s * t in σ)
    (τ : Set T) (t : T) (ht : t in Algebra.adjoin S τ) :
    exists s in σ, IsUnit s ∧ s • t in σ.map (IsScalarTower.toAlgHom R S T) ⊔ Algebra.adjoin R τ := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw [Algebra.smul_def]; rw [← map_mul]; rw [mul_comm]
    exact ⟨_, hs₃, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [smul_add]; rw [mul_smul]; rw [mul_smul]; rw [Algebra.smul_def sx (sy • y)]; rw [smul_comm]; rw [Algebra.smul_def sy (sx • x)]
    apply add_mem (mul_mem _ hsx'') (mul_mem _ hsy'') <;>
      exact Algebra.mem_sup_left ⟨_, ‹_›, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [mul_smul]; rw [← smul_eq_mul]; rw [smul_comm sy x]; rw [← smul_assoc]; rw [smul_eq_mul]
    exact mul_mem hsx'' hsy''

/--
lemma `EssFiniteType.comp` / 引理 `EssFiniteType.comp`

English:
lemma EssFiniteType.comp
  given: [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T]
  proof: by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) union t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t

中文:
引理 EssFiniteType.comp
  条件: [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T]
  证明: by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) union t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t

Depends on / 依赖: Algebra, Algebra.adjoin_image, Algebra.adjoin_union, Algebra.mem_sup_left, Algebra.smul_def, EssFiniteType, EssFiniteType.aux, Finset, Finset.coe_image, Finset.coe_union, IsScalarTower, IsScalarTower.toAlgHom, adjoin_image, adjoin_union, classical, coe_image, coe_union, essFiniteType_iff, mem_sup_left, mul_mem
-/
lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
    EssFiniteType R T := by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) union t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t₁, h₁, h₂, h₃⟩ := EssFiniteType.aux _ _ _ _ hs _ y hy₁
  obtain ⟨t₂, h₄, h₅, h₆⟩ := EssFiniteType.aux _ _ _ _ hs _ _ hy₃
  refine ⟨t₂ • t₁ • y, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₄, rfl⟩) h₃
  · rw [Algebra.smul_def, Algebra.smul_def]
    exact (h₅.map _).mul ((h₂.map _).mul hy₂)
  · rw [← mul_smul, mul_comm, smul_mul_assoc, mul_comm, mul_comm y, mul_smul, Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₁, rfl⟩) h₆

open EssFiniteType in
/--
lemma `essFiniteType_iff_exists_subalgebra` / 引理 `essFiniteType_iff_exists_subalgebra`

English:
lemma essFiniteType_iff_exists_subalgebra
  statement: EssFiniteType R S ↔
  proof: by
  refine ⟨fun h => ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  let := of_isLocalization S M
  exact comp R S₀ S

中文:
引理 essFiniteType_iff_存在_subalgebra
  结论: EssFiniteType R S ↔
  证明: by
  refine ⟨fun h => ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  let := of_isLocalization S M
  exact comp R S₀ S

Depends on / 依赖: of_isLocalization, subalgebra, submonoid
-/
lemma essFiniteType_iff_exists_subalgebra : EssFiniteType R S ↔
    exists (S₀ : Subalgebra R S) (M : Submonoid S₀), FiniteType R S₀ ∧ IsLocalization M S := by
  refine ⟨fun h => ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  let := of_isLocalization S M
  exact comp R S₀ S

/--
Instance `EssFiniteType.baseChange` / 实例 `EssFiniteType.baseChange`

English:
instance EssFiniteType.baseChange
  signature: [h : EssFiniteType R S]
  body: by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
  | tmul x y =>
    obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H (x :

中文:
实例 EssFiniteType.baseChange
  签名: [h : EssFiniteType R S]
  定义体: by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
  | tmul x y =>
    obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H (x :

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.adjoin, Finset, TensorProduct, TensorProduct.induction_on, adjoin, classical, essFiniteType_iff, includeRight, induction_on, isUnit_one, one_mem, otimes
-/
instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T otimes[R] S) := by
  classical
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ.image Algebra.TensorProduct.includeRight
  intro s
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
  | tmul x y =>
    obtain ⟨t, h₁, h₂, h₃⟩ := hσ y
    have H (x : S) (hx : x in Algebra.adjoin R (σ : Set S)) :
        1 otimesₜ[R] x in Algebra.adjoin T
          ((σ.image Algebra.TensorProduct.includeRight : Finset (T otimes[R] S)) : Set (T otimes[R] S)) := by
      have : Algebra.TensorProduct.includeRight x in
          (Algebra.adjoin R (σ : Set S)).map (Algebra.TensorProduct.includeRight (A := T)) :=
        Subalgebra.mem_map.mpr ⟨_, hx, rfl⟩
      rw [← Algebra.adjoin_adjoin_of_tower R]
      apply Algebra.subset_adjoin
      simpa [← Algebra.adjoin_image] using this
    refine ⟨Algebra.TensorProduct.includeRight t, H _ h₁, h₂.map _, ?_⟩
    simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
    rw [← mul_one x]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
    apply Subalgebra.smul_mem
    exact H _ h₃
  | add x y hx hy =>
    obtain ⟨tx, hx₁, hx₂, hx₃⟩ := hx
    obtain ⟨ty, hy₁, hy₂, hy₃⟩ := hy
    refine ⟨_, mul_mem hx₁ hy₁, hx₂.mul hy₂, ?_⟩
    rw [add_mul]; rw [← mul_assoc]; rw [mul_comm tx ty]; rw [← mul_assoc]
    exact add_mem (mul_mem hx₃ hy₁) (mul_mem hy₃ hx₁)

/--
lemma `EssFiniteType.of_comp` / 引理 `EssFiniteType.of_comp`

English:
lemma EssFiniteType.of_comp
  given: [h : EssFiniteType R T]
  statement: EssFiniteType S T
  proof: by
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩

中文:
引理 EssFiniteType.of_comp
  条件: [h : EssFiniteType R T]
  结论: EssFiniteType S T
  证明: by
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩

Depends on / 依赖: Algebra, Algebra.adjoin_adjoin_of_tower, Algebra.subset_adjoin, adjoin_adjoin_of_tower, essFiniteType_iff, simp_rw, subset_adjoin
-/
lemma EssFiniteType.of_comp [h : EssFiniteType R T] : EssFiniteType S T := by
  rw [essFiniteType_iff] at h ⊢
  obtain ⟨σ, hσ⟩ := h
  use σ
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := hσ x
  simp_rw [← Algebra.adjoin_adjoin_of_tower R (S := S) (σ : Set T)]
  exact ⟨y, Algebra.subset_adjoin hy₁, hy₂, Algebra.subset_adjoin hy₃⟩

/--
lemma `EssFiniteType.comp_iff` / 引理 `EssFiniteType.comp_iff`

English:
lemma EssFiniteType.comp_iff
  given: [EssFiniteType R S]
  proof: ⟨fun _ => of_comp R S T, fun _ => comp R S T⟩

中文:
引理 EssFiniteType.comp_iff
  条件: [EssFiniteType R S]
  证明: ⟨fun _ => of_comp R S T, fun _ => comp R S T⟩

Depends on / 依赖: of_comp
-/
lemma EssFiniteType.comp_iff [EssFiniteType R S] :
    EssFiniteType R T ↔ EssFiniteType S T :=
  ⟨fun _ => of_comp R S T, fun _ => comp R S T⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssFiniteType
  signature: R S] (I
  body: .comp R S _

中文:
实例 [EssFiniteType
  签名: R S] (I
  定义体: .comp R S _
-/
instance [EssFiniteType R S] (I : Ideal S) : EssFiniteType R (S ⧸ I) :=
  .comp R S _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssFiniteType
  signature: R S] (M
  body: have : EssFiniteType S (Localization M) := .of_isLocalization _ M
  .comp R S _

中文:
实例 [EssFiniteType
  签名: R S] (M
  定义体: have : EssFiniteType S (Localization M) := .of_isLocalization _ M
  .comp R S _

Depends on / 依赖: EssFiniteType, Localization, of_isLocalization
-/
instance [EssFiniteType R S] (M : Submonoid S) : EssFiniteType R (Localization M) :=
  have : EssFiniteType S (Localization M) := .of_isLocalization _ M
  .comp R S _

end

variable {R S T} in
/--
lemma `EssFiniteType.of_surjective` / 引理 `EssFiniteType.of_surjective`

English:
lemma EssFiniteType.of_surjective
  statement: (f : S ->ₐ[R] T) (hf : Function.Surjective f)
  proof: by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap S T) hf
  exact .comp R S T

中文:
引理 EssFiniteType.of_surjective
  结论: (f : S ->ₐ[R] T) (hf : 函数.满射 f)
  证明: by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap S T) hf
  exact .comp R S T

Depends on / 依赖: Algebra, Algebra.linearMap, Finite, IsScalarTower, Module, Module.Finite, comp_algebraMap, f.comp_algebraMap.symm, f.toAlgebra, linearMap, of_algebraMap_eq, of_surjective, toAlgebra
-/
lemma EssFiniteType.of_surjective (f : S ->ₐ[R] T) (hf : Function.Surjective f)
    [EssFiniteType R S] : EssFiniteType R T := by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap S T) hf
  exact .comp R S T

variable {R S T} in
/--
lemma `EssFiniteType.iff_of_algEquiv` / 引理 `EssFiniteType.iff_of_algEquiv`

English:
lemma EssFiniteType.iff_of_algEquiv
  given: (f : S ≃ₐ[R] T)
  proof: .of_surjective f.toAlgHom f.surjective
  mpr _ := .of_surjective f.symm.toAlgHom f.symm.surjective

中文:
引理 EssFiniteType.iff_of_algEquiv
  条件: (f : S ≃ₐ[R] T)
  证明: .of_surjective f.toAlgHom f.surjective
  mpr _ := .of_surjective f.symm.toAlgHom f.symm.surjective

Depends on / 依赖: f.surjective, f.toAlgHom, of_surjective, surjective, toAlgHom
-/
lemma EssFiniteType.iff_of_algEquiv (f : S ≃ₐ[R] T) :
    EssFiniteType R S ↔ EssFiniteType R T where
  mp _ := .of_surjective f.toAlgHom f.surjective
  mpr _ := .of_surjective f.symm.toAlgHom f.symm.surjective

variable {R S} in
/--
lemma `EssFiniteType.algHom_ext` / 引理 `EssFiniteType.algHom_ext`

English:
lemma EssFiniteType.algHom_ext
  statement: [EssFiniteType R S]
  proof: by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adj

中文:
引理 EssFiniteType.algHom_ext
  结论: [EssFiniteType R S]
  证明: by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adj

Depends on / 依赖: AlgHom, AlgHom.congr_fun, AlgHom.ext_of_adjoin_eq_top, EssFiniteType, EssFiniteType.submonoid, IsLocalization, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.toAlgHom, RingHom, RingHom.congr_fun, adjoin_mem_finset, congr_fun, ext_of_adjoin_eq_top, f.comp, f.toRingHom, finset, g.comp, g.toRingHom, ringHom_ext
-/
lemma EssFiniteType.algHom_ext [EssFiniteType R S]
    (f g : S ->ₐ[R] T) (H : forall s in finset R S, f s = g s) : f = g := by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adjoin_eq_top (s := { x | x.1 in finset R S })
  · exact adjoin_mem_finset R S
  · rintro ⟨x, hx⟩ hx'; exact H x hx'

/--
Instance `EssFiniteType.quotient_map` / 实例 `EssFiniteType.quotient_map`

English:
instance EssFiniteType.quotient_map
  signature: [EssFiniteType R S] (p : Ideal R)
  body: .of_surjective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.toAlgHom
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.surjective

中文:
实例 EssFiniteType.quotient_map
  签名: [EssFiniteType R S] (p : 理想 R)
  定义体: .of_surjective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.toAlgHom
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.surjective

Depends on / 依赖: Algebra, Algebra.TensorProduct.quotIdealMapEquivQuotTensor, TensorProduct, of_surjective, quotIdealMapEquivQuotTensor, surjective, symm.surjective, symm.toAlgHom, toAlgHom
-/
instance EssFiniteType.quotient_map [EssFiniteType R S] (p : Ideal R) :
    EssFiniteType (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
  .of_surjective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.toAlgHom
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).symm.surjective

end Algebra

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R ->+* S}

/-- A ring hom is essentially of finite type if it is the composition of a localization map
and a ring hom of finite type. See `Algebra.EssFiniteType`. -/
@[algebraize Algebra.EssFiniteType]
/--
Definition of `EssFiniteType` / `EssFiniteType` 的定义

English:
definition EssFiniteType
  signature: (f : R ->+* S)
  body: letI := f.toAlgebra
  Algebra.EssFiniteType R S

中文:
定义 EssFiniteType
  签名: (f : R ->+* S)
  定义体: letI := f.toAlgebra
  Algebra.EssFiniteType R S

Depends on / 依赖: Algebra, Algebra.EssFiniteType, EssFiniteType, f.toAlgebra, toAlgebra
-/
def EssFiniteType (f : R ->+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.EssFiniteType R S

/--
lemma `essFiniteType_algebraMap` / 引理 `essFiniteType_algebraMap`

English:
lemma essFiniteType_algebraMap
  statement: {R S : Type*} [CommRing R] [CommRing S]
  proof: by
  rw [RingHom.EssFiniteType]; rw [toAlgebra_algebraMap]

中文:
引理 essFiniteType_algebraMap
  结论: {R S : 类型} [交换环 R] [交换环 S]
  证明: by
  rw [RingHom.EssFiniteType]; rw [toAlgebra_algebraMap]

Depends on / 依赖: EssFiniteType, RingHom, RingHom.EssFiniteType, toAlgebra_algebraMap
-/
lemma essFiniteType_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).EssFiniteType ↔ Algebra.EssFiniteType R S := by
  rw [RingHom.EssFiniteType]; rw [toAlgebra_algebraMap]

/-- A choice of "essential generators" for a ring hom essentially of finite type.
See `Algebra.EssFiniteType.ext`. -/
noncomputable
/--
Definition of `EssFiniteType.finset` / `EssFiniteType.finset` 的定义

English:
definition EssFiniteType.finset
  signature: (hf : f.EssFiniteType)
  body: letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hf
  Algebra.EssFiniteType.finset R S

中文:
定义 EssFiniteType.finset
  签名: (hf : f.EssFiniteType)
  定义体: letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hf
  Algebra.EssFiniteType.finset R S
-/
def EssFiniteType.finset (hf : f.EssFiniteType) : Finset S :=
  letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hf
  Algebra.EssFiniteType.finset R S

/--
lemma `FiniteType.essFiniteType` / 引理 `FiniteType.essFiniteType`

English:
lemma FiniteType.essFiniteType
  given: (hf : f.FiniteType)
  statement: f.EssFiniteType
  proof: by
  algebraize [f]
  change Algebra.EssFiniteType R S
  infer_instance

中文:
引理 有限型.essFiniteType
  条件: (hf : f.有限型)
  结论: f.EssFiniteType
  证明: by
  algebraize [f]
  change Algebra.EssFiniteType R S
  infer_instance

Depends on / 依赖: Algebra, Algebra.EssFiniteType, EssFiniteType, algebraize, infer_instance
-/
lemma FiniteType.essFiniteType (hf : f.FiniteType) : f.EssFiniteType := by
  algebraize [f]
  change Algebra.EssFiniteType R S
  infer_instance

/--
lemma `EssFiniteType.ext` / 引理 `EssFiniteType.ext`

English:
lemma EssFiniteType.ext
  statement: (hf : f.EssFiniteType) {g₁ g₂ : S ->+* T}
  proof: by
  algebraize [f, g₁.comp f]
  ext x
  exact DFunLike.congr_fun (Algebra.EssFiniteType.algHom_ext T
    ⟨g₁, fun _ => rfl⟩ ⟨g₂, DFunLike.congr_fun h₁.symm⟩ h₂) x

中文:
引理 EssFiniteType.ext
  结论: (hf : f.EssFiniteType) {g₁ g₂ : S ->+* T}
  证明: by
  algebraize [f, g₁.comp f]
  ext x
  exact DFunLike.congr_fun (Algebra.EssFiniteType.algHom_ext T
    ⟨g₁, fun _ => rfl⟩ ⟨g₂, DFunLike.congr_fun h₁.symm⟩ h₂) x

Depends on / 依赖: Algebra, Algebra.EssFiniteType.algHom_ext, DFunLike, DFunLike.congr_fun, EssFiniteType, algHom_ext, algebraize, congr_fun
-/
lemma EssFiniteType.ext (hf : f.EssFiniteType) {g₁ g₂ : S ->+* T}
    (h₁ : g₁.comp f = g₂.comp f) (h₂ : forall x in hf.finset, g₁ x = g₂ x) : g₁ = g₂ := by
  algebraize [f, g₁.comp f]
  ext x
  exact DFunLike.congr_fun (Algebra.EssFiniteType.algHom_ext T
    ⟨g₁, fun _ => rfl⟩ ⟨g₂, DFunLike.congr_fun h₁.symm⟩ h₂) x

end RingHom
