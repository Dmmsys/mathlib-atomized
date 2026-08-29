/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Complementary embeddings

Given two embeddings `e₁ : c₁.Embedding c` and `e₂ : c₂.Embedding c`
of complex shapes, we introduce a property `e₁.AreComplementary e₂`
saying that the image subsets of the indices of `c₁` and `c₂` form
a partition of the indices of `c`.

If `e₁.IsTruncLE` and `e₂.IsTruncGE`, and `K : HomologicalComplex C c`,
we construct a quasi-isomorphism `shortComplexTruncLEX₃ToTruncGE` between
the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K` and `K.truncGE e₂`.

-/

@[expose] public section

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape

namespace Embedding

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

/--
Definition of `AreComplementary` / `AreComplementary` 的定义

English:
structure AreComplementary
  parameters: : Prop where
  axioms and operations (2):
    - disjoint((i₁ : ι₁) (i₂ : ι₂)) : e₁.f i₁ != e₂.f i₂
    - union((i : ι)) : (exists i₁, e₁.f i₁ = i) ∨ exists i₂, e₂.f i₂ = i

中文:
结构 AreComplementary
  参数: : 命题 where
  公理与运算 (2 个):
    - disjoint((i₁ : ι₁) (i₂ : ι₂)) : e₁.f i₁ != e₂.f i₂
    - union((i : ι)) : (存在 i₁, e₁.f i₁ = i) ∨ 存在 i₂, e₂.f i₂ = i
-/
structure AreComplementary : Prop where
  disjoint (i₁ : ι₁) (i₂ : ι₂) : e₁.f i₁ != e₂.f i₂
  union (i : ι) : (exists i₁, e₁.f i₁ = i) ∨ exists i₂, e₂.f i₂ = i

variable {e₁ e₂}

namespace AreComplementary

variable (ac : AreComplementary e₁ e₂)

include ac
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: AreComplementary e₂ e₁ where
  proof: (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

中文:
引理 symm
  结论: AreComplementary e₂ e₁ where
  证明: (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

Depends on / 依赖: ac.disjoint, disjoint
-/
lemma symm : AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

/--
lemma `exists_i₁` / 引理 `exists_i₁`

English:
lemma exists_i₁
  given: (i : ι) (hi : forall i₂, e₂.f i₂ != i)
  proof: by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

中文:
引理 存在_i₁
  条件: (i : ι) (hi : 对任意 i₂, e₂.f i₂ != i)
  证明: by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

Depends on / 依赖: ac.union
-/
lemma exists_i₁ (i : ι) (hi : forall i₂, e₂.f i₂ != i) :
    exists i₁, i = e₁.f i₁ := by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

/--
lemma `exists_i₂` / 引理 `exists_i₂`

English:
lemma exists_i₂
  given: (i : ι) (hi : forall i₁, e₁.f i₁ != i)
  proof: ac.symm.exists_i₁ i hi

中文:
引理 存在_i₂
  条件: (i : ι) (hi : 对任意 i₁, e₁.f i₁ != i)
  证明: ac.symm.exists_i₁ i hi

Depends on / 依赖: ac.symm.exists_i
-/
lemma exists_i₂ (i : ι) (hi : forall i₁, e₁.f i₁ != i) :
    exists i₂, i = e₂.f i₂ :=
  ac.symm.exists_i₁ i hi

variable (e₁ e₂) in
/-- Given complementary embeddings of complex shapes
`e₁ : Embedding c₁ c` and `e₂ : Embedding c₂ c`, this is
the obvious map `ι₁ ⊕ ι₂ → ι` from the sum of the index
types of `c₁` and `c₂` to the index type of `c`. -/
@[simp]
/--
Definition of `fromSum` / `fromSum` 的定义

English:
definition fromSum
  signature: : ι₁ oplus ι₂ -> ι

中文:
定义 fromSum
  签名: : ι₁ oplus ι₂ -> ι
-/
def fromSum : ι₁ oplus ι₂ -> ι
  | Sum.inl i₁ => e₁.f i₁
  | Sum.inr i₂ => e₂.f i₂

/--
lemma `fromSum_bijective` / 引理 `fromSum_bijective`

English:
lemma fromSum_bijective
  statement: Function.Bijective (fromSum e₁ e₂)
  proof: by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ h.symm).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.i

中文:
引理 fromSum_bijective
  结论: 函数.双射 (fromSum e₁ e₂)
  证明: by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ h.symm).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.i

Depends on / 依赖: Sum.inl, Sum.inr, ac.disjoint, ac.union, disjoint, h.symm, injective_f
-/
lemma fromSum_bijective : Function.Bijective (fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ h.symm).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : ι₁ oplus ι₂ ≃ ι
  body: Equiv.ofBijective _ (ac.fromSum_bijective)

中文:
定义 equiv
  签名: : ι₁ oplus ι₂ ≃ ι
  定义体: Equiv.ofBijective _ (ac.fromSum_bijective)

Depends on / 依赖: Equiv.ofBijective, ac.fromSum_bijective, fromSum_bijective, ofBijective
-/
noncomputable def equiv : ι₁ oplus ι₂ ≃ ι := Equiv.ofBijective _ (ac.fromSum_bijective)

/--
lemma `equiv_inl` / 引理 `equiv_inl`

English:
lemma equiv_inl
  given: (i₁ : ι₁)
  statement: ac.equiv (Sum.inl i₁) = e₁.f i₁
  proof: rfl

中文:
引理 equiv_inl
  条件: (i₁ : ι₁)
  结论: ac.equiv (和.inl i₁) = e₁.f i₁
  证明: rfl
-/
@[simp] lemma equiv_inl (i₁ : ι₁) : ac.equiv (Sum.inl i₁) = e₁.f i₁ := rfl
/--
lemma `equiv_inr` / 引理 `equiv_inr`

English:
lemma equiv_inr
  given: (i₂ : ι₂)
  statement: ac.equiv (Sum.inr i₂) = e₂.f i₂
  proof: rfl

中文:
引理 equiv_inr
  条件: (i₂ : ι₂)
  结论: ac.equiv (和.inr i₂) = e₂.f i₂
  证明: rfl
-/
@[simp] lemma equiv_inr (i₂ : ι₂) : ac.equiv (Sum.inr i₂) = e₂.f i₂ := rfl

section

variable {X : ι -> Type*} (x₁ : forall i₁, X (e₁.f i₁)) (x₂ : forall i₂, X (e₂.f i₂))

variable (X) in
/--
Definition of `desc.aux` / `desc.aux` 的定义

English:
definition desc.aux
  signature: (i j : ι) (hij : i = j)
  body: by
  subst hij
  rfl

omit ac in
@[simp]

中文:
定义 desc.aux
  签名: (i j : ι) (hij : i = j)
  定义体: by
  subst hij
  rfl

omit ac in
@[simp]
-/
def desc.aux (i j : ι) (hij : i = j) : X i ≃ X j := by
  subst hij
  rfl

omit ac in
@[simp]
/--
lemma `desc.aux_trans` / 引理 `desc.aux_trans`

English:
lemma desc.aux_trans
  given: {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i)
  proof: by
  subst hij hjk
  rfl

中文:
引理 desc.aux_trans
  条件: {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i)
  证明: by
  subst hij hjk
  rfl
-/
lemma desc.aux_trans {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i) :
    desc.aux X j k hjk (aux X i j hij x) = desc.aux X i k (hij.trans hjk) x := by
  subst hij hjk
  rfl

/--
Definition of `desc'` / `desc'` 的定义

English:
definition desc'
  signature: : forall (i : ι₁ oplus ι₂), X (ac.equiv i)

中文:
定义 desc'
  签名: : 对任意 (i : ι₁ oplus ι₂), X (ac.equiv i)
-/
def desc' : forall (i : ι₁ oplus ι₂), X (ac.equiv i)
  | Sum.inl i₁ => x₁ i₁
  | Sum.inr i₂ => x₂ i₂

/--
lemma `desc'_inl` / 引理 `desc'_inl`

English:
lemma desc'_inl
  given: (i : ι₁ oplus ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i)
  proof: by subst h; rfl

中文:
引理 desc'_inl
  条件: (i : ι₁ oplus ι₂) (i₁ : ι₁) (h : 和.inl i₁ = i)
  证明: by subst h; rfl
-/
lemma desc'_inl (i : ι₁ oplus ι₂) (i₁ : ι₁) (h : Sum.inl i₁ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₁ i₁) := by subst h; rfl

/--
lemma `desc'_inr` / 引理 `desc'_inr`

English:
lemma desc'_inr
  given: (i : ι₁ oplus ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i)
  proof: by subst h; rfl

中文:
引理 desc'_inr
  条件: (i : ι₁ oplus ι₂) (i₂ : ι₂) (h : 和.inr i₂ = i)
  证明: by subst h; rfl
-/
lemma desc'_inr (i : ι₁ oplus ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i) :
    ac.desc' x₁ x₂ i = desc.aux _ _ _ (by subst h; simp) (x₂ i₂) := by subst h; rfl

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (i : ι)
  body: desc.aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))

中文:
定义 desc
  签名: (i : ι)
  定义体: desc.aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))

Depends on / 依赖: ac.desc, ac.equiv.symm, desc.aux
-/
noncomputable def desc (i : ι) : X i :=
  desc.aux _ _ _ (by simp) (ac.desc' x₁ x₂ (ac.equiv.symm i))

/--
lemma `desc_inl` / 引理 `desc_inl`

English:
lemma desc_inl
  given: (i₁ : ι₁)
  statement: ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁
  proof: by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

中文:
引理 desc_inl
  条件: (i₁ : ι₁)
  结论: ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁
  证明: by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

Depends on / 依赖: _inl, ac.desc, ac.equiv.injective, aux_trans, desc.aux_trans, injective
-/
lemma desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [desc]
  rw [ac.desc'_inl _ _ _ i₁ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

/--
lemma `desc_inr` / 引理 `desc_inr`

English:
lemma desc_inr
  given: (i₂ : ι₂)
  statement: ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂
  proof: by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

中文:
引理 desc_inr
  条件: (i₂ : ι₂)
  结论: ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂
  证明: by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

Depends on / 依赖: _inr, ac.desc, ac.equiv.injective, aux_trans, desc.aux_trans, injective
-/
lemma desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂ := by
  dsimp [desc]
  rw [ac.desc'_inr _ _ _ i₂ (ac.equiv.injective (by simp))]; rw [desc.aux_trans]
  rfl

end

variable (K L : HomologicalComplex C c)

/--
lemma `isStrictlySupportedOutside₁_iff` / 引理 `isStrictlySupportedOutside₁_iff`

English:
lemma isStrictlySupportedOutside₁_iff
  proof: by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

中文:
引理 isStrictlySupportedOutside₁_iff
  证明: by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

Depends on / 依赖: K.isZero_X_of_isStrictlySupported, ac.disjoint, ac.exists_i, disjoint, h.isZero, isZero, isZero_X_of_isStrictlySupported
-/
lemma isStrictlySupportedOutside₁_iff :
    K.IsStrictlySupportedOutside e₁ ↔ K.IsStrictlySupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

/--
lemma `isStrictlySupportedOutside₂_iff` / 引理 `isStrictlySupportedOutside₂_iff`

English:
lemma isStrictlySupportedOutside₂_iff
  proof: ac.symm.isStrictlySupportedOutside₁_iff K

中文:
引理 isStrictlySupportedOutside₂_iff
  证明: ac.symm.isStrictlySupportedOutside₁_iff K

Depends on / 依赖: ac.symm.isStrictlySupportedOutside
-/
lemma isStrictlySupportedOutside₂_iff :
    K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictlySupported e₁ :=
  ac.symm.isStrictlySupportedOutside₁_iff K

/--
lemma `isSupportedOutside₁_iff` / 引理 `isSupportedOutside₁_iff`

English:
lemma isSupportedOutside₁_iff
  proof: by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

中文:
引理 isSupportedOutside₁_iff
  证明: by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

Depends on / 依赖: K.exactAt_of_isSupported, ac.disjoint, ac.exists_i, disjoint, exactAt, exactAt_of_isSupported, h.exactAt
-/
lemma isSupportedOutside₁_iff :
    K.IsSupportedOutside e₁ ↔ K.IsSupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ac.exists_i₁ i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => (ac.disjoint i₁ i₂).symm)⟩

/--
lemma `isSupportedOutside₂_iff` / 引理 `isSupportedOutside₂_iff`

English:
lemma isSupportedOutside₂_iff
  proof: ac.symm.isSupportedOutside₁_iff K

中文:
引理 isSupportedOutside₂_iff
  证明: ac.symm.isSupportedOutside₁_iff K

Depends on / 依赖: ac.symm.isSupportedOutside
-/
lemma isSupportedOutside₂_iff :
    K.IsSupportedOutside e₂ ↔ K.IsSupported e₁ :=
  ac.symm.isSupportedOutside₁_iff K

variable {K L}

/--
lemma `hom_ext'` / 引理 `hom_ext'`

English:
lemma hom_ext'
  statement: (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
  proof: by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

中文:
引理 hom_ext'
  结论: (φ : K ⟶ L) (hK : K.是StrictlySupportedOutside e₂)
  证明: by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

Depends on / 依赖: ac.union, eq_of_src, eq_of_tgt, hK.isZero, hL.isZero, isZero
-/
lemma hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
    (hL : L.IsStrictlySupportedOutside e₁) :
    φ = 0 := by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L)
  proof: by
  apply ac.hom_ext'
  · rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  · rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

中文:
引理 hom_ext
  条件: [K.是StrictlySupported e₁] [L.是StrictlySupported e₂] (φ : K ⟶ L)
  证明: by
  apply ac.hom_ext'
  · rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  · rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

Depends on / 依赖: ac.hom_ext, ac.isStrictlySupportedOutside, hom_ext, infer_instance
-/
lemma hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) :
    φ = 0 := by
  apply ac.hom_ext'
  · rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  · rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

/-- If `e₁` and `e₂` are complementary embeddings into a complex shape `c`,
indices `i₁` and `i₂` are at the boundary if `c.Rel (e₁.f i₁) (e₂.f i₂)`. -/
@[nolint unusedArguments]
/--
Definition of `Boundary` / `Boundary` 的定义

English:
definition Boundary
  signature: (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂)
  body: c.Rel (e₁.f i₁) (e₂.f i₂)

中文:
定义 边界
  签名: (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂)
  定义体: c.Rel (e₁.f i₁) (e₂.f i₂)

Depends on / 依赖: c.Rel
-/
def Boundary (_ : AreComplementary e₁ e₂) (i₁ : ι₁) (i₂ : ι₂) : Prop :=
  c.Rel (e₁.f i₁) (e₂.f i₂)

namespace Boundary

variable {ac}

section

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

include h

/--
lemma `fst` / 引理 `fst`

English:
lemma fst
  statement: e₁.BoundaryLE i₁
  proof: e₁.boundaryLE h (fun _ => ac.disjoint _ _)

中文:
引理 fst
  结论: e₁.BoundaryLE i₁
  证明: e₁.boundaryLE h (fun _ => ac.disjoint _ _)

Depends on / 依赖: ac.disjoint, boundaryLE, disjoint
-/
lemma fst : e₁.BoundaryLE i₁ :=
  e₁.boundaryLE h (fun _ => ac.disjoint _ _)

/--
lemma `snd` / 引理 `snd`

English:
lemma snd
  statement: e₂.BoundaryGE i₂
  proof: e₂.boundaryGE h (fun _ => ac.symm.disjoint _ _)

中文:
引理 snd
  结论: e₂.BoundaryGE i₂
  证明: e₂.boundaryGE h (fun _ => ac.symm.disjoint _ _)

Depends on / 依赖: ac.symm.disjoint, boundaryGE, disjoint
-/
lemma snd : e₂.BoundaryGE i₂ :=
  e₂.boundaryGE h (fun _ => ac.symm.disjoint _ _)

end

/--
lemma `fst_inj` / 引理 `fst_inj`

English:
lemma fst_inj
  given: {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁' i₂)
  proof: e₁.injective_f (c.prev_eq h h')

中文:
引理 fst_inj
  条件: {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.边界 i₁ i₂) (h' : ac.边界 i₁' i₂)
  证明: e₁.injective_f (c.prev_eq h h')

Depends on / 依赖: c.prev_eq, injective_f, prev_eq
-/
lemma fst_inj {i₁ i₁' : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁' i₂) :
    i₁ = i₁' :=
  e₁.injective_f (c.prev_eq h h')

/--
lemma `snd_inj` / 引理 `snd_inj`

English:
lemma snd_inj
  given: {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁ i₂')
  proof: e₂.injective_f (c.next_eq h h')

中文:
引理 snd_inj
  条件: {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.边界 i₁ i₂) (h' : ac.边界 i₁ i₂')
  证明: e₂.injective_f (c.next_eq h h')

Depends on / 依赖: c.next_eq, injective_f, next_eq
-/
lemma snd_inj {i₁ : ι₁} {i₂ i₂' : ι₂} (h : ac.Boundary i₁ i₂) (h' : ac.Boundary i₁ i₂') :
    i₂ = i₂' :=
  e₂.injective_f (c.next_eq h h')

variable (ac)

/--
lemma `exists₁` / 引理 `exists₁`

English:
lemma exists₁
  given: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  proof: by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ac.exists_i₂ (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using! h₁))
  exact ⟨i₂, by simpa only [hi₂] using! h₁⟩

中文:
引理 存在₁
  条件: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  证明: by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ac.exists_i₂ (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using! h₁))
  exact ⟨i₂, by simpa only [hi₂] using! h₁⟩

Depends on / 依赖: ac.exists_i, c.next
-/
lemma exists₁ {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    exists i₂, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ac.exists_i₂ (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using! h₁))
  exact ⟨i₂, by simpa only [hi₂] using! h₁⟩

/--
lemma `exists₂` / 引理 `exists₂`

English:
lemma exists₂
  given: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  proof: by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ac.exists_i₁ (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using! h₁))
  exact ⟨i₁, by simpa only [hi₁] using! h₁⟩

中文:
引理 存在₂
  条件: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  证明: by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ac.exists_i₁ (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using! h₁))
  exact ⟨i₁, by simpa only [hi₁] using! h₁⟩

Depends on / 依赖: ac.exists_i, c.prev
-/
lemma exists₂ {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    exists i₁, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ac.exists_i₁ (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using! h₁))
  exact ⟨i₁, by simpa only [hi₁] using! h₁⟩

/--
Definition of `indexOfBoundaryLE` / `indexOfBoundaryLE` 的定义

English:
definition indexOfBoundaryLE
  signature: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  body: (exists₁ ac h).choose

中文:
定义 indexOfBoundaryLE
  签名: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  定义体: (exists₁ ac h).choose
-/
noncomputable def indexOfBoundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) : ι₂ :=
    (exists₁ ac h).choose

/--
lemma `of_boundaryLE` / 引理 `of_boundaryLE`

English:
lemma of_boundaryLE
  given: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  proof: (exists₁ ac h).choose_spec

中文:
引理 of_boundaryLE
  条件: {i₁ : ι₁} (h : e₁.BoundaryLE i₁)
  证明: (exists₁ ac h).choose_spec

Depends on / 依赖: choose_spec
-/
lemma of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (indexOfBoundaryLE ac h) := (exists₁ ac h).choose_spec

/--
Definition of `indexOfBoundaryGE` / `indexOfBoundaryGE` 的定义

English:
definition indexOfBoundaryGE
  signature: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  body: (exists₂ ac h).choose

中文:
定义 indexOfBoundaryGE
  签名: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  定义体: (exists₂ ac h).choose
-/
noncomputable def indexOfBoundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) : ι₁ :=
    (exists₂ ac h).choose

/--
lemma `of_boundaryGE` / 引理 `of_boundaryGE`

English:
lemma of_boundaryGE
  given: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  proof: (exists₂ ac h).choose_spec

中文:
引理 of_boundaryGE
  条件: {i₂ : ι₂} (h : e₂.BoundaryGE i₂)
  证明: (exists₂ ac h).choose_spec

Depends on / 依赖: choose_spec
-/
lemma of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (indexOfBoundaryGE ac h) i₂ := (exists₂ ac h).choose_spec

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE where
  body: fun ⟨i₁, h⟩ => ⟨_, (of_boundaryLE ac h).snd⟩
  invFun := fun ⟨i₂, h⟩ => ⟨_, (of_boundaryGE ac h).fst⟩
  left_inv := fun ⟨i₁, h⟩ => by
    ext
    have h' := of_boundaryLE ac h
    have h'' := of_boundaryGE ac h'.snd
    exact fst_inj h'' h'
  right_inv := fun ⟨i₂, h⟩ => by
    ext
    have h' := of_

中文:
定义 equiv
  签名: : 子类型 e₁.BoundaryLE ≃ 子类型 e₂.BoundaryGE where
  定义体: fun ⟨i₁, h⟩ => ⟨_, (of_boundaryLE ac h).snd⟩
  invFun := fun ⟨i₂, h⟩ => ⟨_, (of_boundaryGE ac h).fst⟩
  left_inv := fun ⟨i₁, h⟩ => by
    ext
    have h' := of_boundaryLE ac h
    have h'' := of_boundaryGE ac h'.snd
    exact fst_inj h'' h'
  right_inv := fun ⟨i₂, h⟩ => by
    ext
    have h' := of_

Depends on / 依赖: of_boundaryLE
-/
noncomputable def equiv : Subtype e₁.BoundaryLE ≃ Subtype e₂.BoundaryGE where
  toFun := fun ⟨i₁, h⟩ => ⟨_, (of_boundaryLE ac h).snd⟩
  invFun := fun ⟨i₂, h⟩ => ⟨_, (of_boundaryGE ac h).fst⟩
  left_inv := fun ⟨i₁, h⟩ => by
    ext
    have h' := of_boundaryLE ac h
    have h'' := of_boundaryGE ac h'.snd
    exact fst_inj h'' h'
  right_inv := fun ⟨i₂, h⟩ => by
    ext
    have h' := of_boundaryGE ac h
    have h'' := of_boundaryLE ac h'.fst
    exact snd_inj h'' h'

end Boundary

end AreComplementary

set_option backward.defeqAttrib.useBackward true in
/--
lemma `embeddingUpInt_areComplementary` / 引理 `embeddingUpInt_areComplementary`

English:
lemma embeddingUpInt_areComplementary
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁)
  proof: by dsimp; lia
  union i := by
    by_cases hi : i <= n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ <= i by lia)
      exact Or.inr ⟨k, rfl⟩

中文:
引理 embeddingUp整数_areComplementary
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁)
  证明: by dsimp; lia
  union i := by
    by_cases hi : i <= n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ <= i by lia)
      exact Or.inr ⟨k, rfl⟩

Depends on / 依赖: Int.exists_add_of_le, Or.inl, Or.inr, exists_add_of_le
-/
lemma embeddingUpInt_areComplementary (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    AreComplementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where
  disjoint i₁ i₂ := by dsimp; lia
  union i := by
    by_cases hi : i <= n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ <= i by lia)
      exact Or.inr ⟨k, rfl⟩

end Embedding

end ComplexShape

namespace HomologicalComplex

section

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

/--
Definition of `shortComplexTruncLEX₃ToTruncGE` / `shortComplexTruncLEX₃ToTruncGE` 的定义

English:
definition shortComplexTruncLEX₃ToTruncGE
  signature: :
  body: cokernel.desc _ (K.πTruncGE e₂) (ac.hom_ext _)

@[reassoc (attr := simp)]

中文:
定义 shortComplexTruncLEX₃ToTruncGE
  签名: :
  定义体: cokernel.desc _ (K.πTruncGE e₂) (ac.hom_ext _)

@[reassoc (attr := simp)]

Depends on / 依赖: ac.hom_ext, cokernel, cokernel.desc, hom_ext
-/
noncomputable def shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).X₃ ⟶ K.truncGE e₂ :=
  cokernel.desc _ (K.πTruncGE e₂) (ac.hom_ext _)

@[reassoc (attr := simp)]
/--
lemma `g_shortComplexTruncLEX₃ToTruncGE` / 引理 `g_shortComplexTruncLEX₃ToTruncGE`

English:
lemma g_shortComplexTruncLEX₃ToTruncGE
  proof: cokernel.π_desc _ _ _

中文:
引理 g_shortComplexTruncLEX₃ToTruncGE
  证明: cokernel.π_desc _ _ _

Depends on / 依赖: cokernel
-/
lemma g_shortComplexTruncLEX₃ToTruncGE :
    (K.shortComplexTruncLE e₁).g ≫ K.shortComplexTruncLEX₃ToTruncGE ac = K.πTruncGE e₂ :=
  cokernel.π_desc _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (K.shortComplexTruncLEX₃ToTruncGE ac)
  body: by
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₁ := ((ac.isSupportedOutside₁_iff (K.truncGE e₂)).2 inferInstance).exactAt i₁
      have h₂ := (K.shortComplexTruncLE_X₃_isSupportedOutside e₁).exactAt i₁
      simpa only [quasiIsoAt_iff_exactAt _ _ h₂] using h₁
    · have := quasiIsoAt_

中文:
实例 :
  签名: 拟同构 (K.shortComplexTruncLEX₃ToTruncGE ac)
  定义体: by
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₁ := ((ac.isSupportedOutside₁_iff (K.truncGE e₂)).2 inferInstance).exactAt i₁
      have h₂ := (K.shortComplexTruncLE_X₃_isSupportedOutside e₁).exactAt i₁
      simpa only [quasiIsoAt_iff_exactAt _ _ h₂] using h₁
    · have := quasiIsoAt_

Depends on / 依赖: K.shortComplexTruncLE, K.shortComplexTruncLEX, K.shortComplexTruncLE_X, K.truncGE, ac.disjoint, ac.isSupportedOutside, ac.union, disjoint, exactAt, infer_instance, quasiIsoAt_iff_comp_left, quasiIsoAt_iff_exactAt, quasiIsoAt_shortComplexTruncLE_g, shortComplexTruncLE, truncGE
-/
instance : QuasiIso (K.shortComplexTruncLEX₃ToTruncGE ac) where
  quasiIsoAt i := by
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
    · have h₁ := ((ac.isSupportedOutside₁_iff (K.truncGE e₂)).2 inferInstance).exactAt i₁
      have h₂ := (K.shortComplexTruncLE_X₃_isSupportedOutside e₁).exactAt i₁
      simpa only [quasiIsoAt_iff_exactAt _ _ h₂] using h₁
    · have := quasiIsoAt_shortComplexTruncLE_g K e₁ (e₂.f i₂) (fun _ => ac.disjoint _ _)
      rw [← quasiIsoAt_iff_comp_left (K.shortComplexTruncLE e₁).g
        (K.shortComplexTruncLEX₃ToTruncGE ac)]; rw [g_shortComplexTruncLEX₃ToTruncGE]
      dsimp
      infer_instance

end

end HomologicalComplex
