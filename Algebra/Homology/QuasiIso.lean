/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

-/

@[expose] public section


open CategoryTheory Limits

universe v u

open HomologicalComplex

section

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

/--
Definition of `QuasiIsoAt` / `QuasiIsoAt` 的定义

English:
class QuasiIsoAt
  parameters: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  axioms and operations (1):
    - quasiIso : ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)

中文:
类 在处拟同构
  参数: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  公理与运算 (1 个):
    - quasiIso : 短复形.拟同构 ((shortComplexFunctor C c i).map f)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.zero, rightHomologyMap
-/
class QuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : Prop where
  quasiIso : ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f)

/--
lemma `quasiIsoAt_iff` / 引理 `quasiIsoAt_iff`

English:
lemma quasiIsoAt_iff
  given: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

中文:
引理 quasiIsoAt_iff
  条件: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.zero, h.quasiIso, opcyclesMap, quasiIso
-/
lemma quasiIsoAt_iff (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((shortComplexFunctor C c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

/--
Instance `quasiIsoAt_of_isIso` / 实例 `quasiIsoAt_of_isIso`

English:
instance quasiIsoAt_of_isIso
  signature: (f : K ⟶ L) [IsIso f] (i : ι) [K.HasHomology i] [L.HasHomology i]
  body: by
  rw [quasiIsoAt_iff]
  infer_instance

中文:
实例 quasiIsoAt_of_isIso
  签名: (f : K ⟶ L) [是同构 f] (i : ι) [K.有同调 i] [L.有同调 i]
  定义体: by
  rw [quasiIsoAt_iff]
  infer_instance

Depends on / 依赖: infer_instance, quasiIsoAt_iff
-/
instance quasiIsoAt_of_isIso (f : K ⟶ L) [IsIso f] (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff]
  infer_instance

/--
lemma `quasiIsoAt_iff'` / 引理 `quasiIsoAt_iff'`

English:
lemma quasiIsoAt_iff'
  statement: (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  proof: by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))

中文:
引理 quasiIsoAt_iff'
  结论: (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  证明: by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, ShortComplex, ShortComplex.quasiIso_iff_of_arrow_mk_iso, isoOfNatIso, natIsoSc, quasiIsoAt_iff, quasiIso_iff_of_arrow_mk_iso
-/
lemma quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    QuasiIsoAt f j ↔
      ShortComplex.QuasiIso ((shortComplexFunctor' C c i j k).map f) := by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (natIsoSc' C c i j k hi hk) (Arrow.mk f))

/--
lemma `quasiIsoAt_of_retract` / 引理 `quasiIsoAt_of_retract`

English:
lemma quasiIsoAt_of_retract
  statement: {f : K ⟶ L} {f' : K' ⟶ L'}
  proof: by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

中文:
引理 quasiIsoAt_of_retract
  结论: {f : K ⟶ L} {f' : K' ⟶ L'}
  证明: by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.comp_, ShortComplex, ShortComplex.quasiIso_of_retract, h.map, quasiIsoAt_iff, quasiIso_of_retract, rightHomologyMap, rightHomologyMapData, shortComplexFunctor
-/
lemma quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i]
    [K'.HasHomology i] [L'.HasHomology i] [hf' : QuasiIsoAt f' i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

/--
lemma `quasiIsoAt_iff_isIso_homologyMap` / 引理 `quasiIsoAt_iff_isIso_homologyMap`

English:
lemma quasiIsoAt_iff_isIso_homologyMap
  statement: (f : K ⟶ L) (i : ι)
  proof: by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  rfl

中文:
引理 quasiIsoAt_iff_isIso_homologyMap
  结论: (f : K ⟶ L) (i : ι)
  证明: by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  rfl

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.comp_, ShortComplex, ShortComplex.quasiIso_iff, opcyclesMap, quasiIsoAt_iff, quasiIso_iff, rightHomologyMapData
-/
lemma quasiIsoAt_iff_isIso_homologyMap (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso (homologyMap f i) := by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  rfl

/--
lemma `quasiIsoAt_iff_exactAt` / 引理 `quasiIsoAt_iff_exactAt`

English:
lemma quasiIsoAt_iff_exactAt
  statement: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

中文:
引理 quasiIsoAt_iff_exactAt
  结论: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

Depends on / 依赖: IsZero, IsZero.eq_of_src, IsZero.eq_of_tgt, IsZero.of_iso, ShortComplex, ShortComplex.exact_iff_isZero_homology, ShortComplex.quasiIso_iff, eq_of_src, eq_of_tgt, exactAt_iff, exact_iff_isZero_homology, of_iso, quasiIsoAt_iff, quasiIso_iff
-/
lemma quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) :
    QuasiIsoAt f i ↔ L.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

/--
lemma `quasiIsoAt_iff_exactAt'` / 引理 `quasiIsoAt_iff_exactAt'`

English:
lemma quasiIsoAt_iff_exactAt'
  statement: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

中文:
引理 quasiIsoAt_iff_exactAt'
  结论: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

Depends on / 依赖: IsZero, IsZero.eq_of_src, IsZero.eq_of_tgt, IsZero.of_iso, ShortComplex, ShortComplex.exact_iff_isZero_homology, ShortComplex.quasiIso_iff, eq_of_src, eq_of_tgt, exactAt_iff, exact_iff_isZero_homology, of_iso, quasiIsoAt_iff, quasiIso_iff
-/
lemma quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hL : L.ExactAt i) :
    QuasiIsoAt f i ↔ K.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

/--
lemma `exactAt_iff_of_quasiIsoAt` / 引理 `exactAt_iff_of_quasiIsoAt`

English:
lemma exactAt_iff_of_quasiIsoAt
  statement: (f : K ⟶ L) (i : ι)
  proof: ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

中文:
引理 exactAt_iff_of_quasiIsoAt
  结论: (f : K ⟶ L) (i : ι)
  证明: ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

Depends on / 依赖: quasiIsoAt_iff_exactAt
-/
lemma exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

instance (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] [hf : QuasiIsoAt f i] :
    IsIso (homologyMap f i) := by
  simpa only [quasiIsoAt_iff, ShortComplex.quasiIso_iff] using! hf

/-- The isomorphism `K.homology i ≅ L.homology i` induced by a morphism `f : K ⟶ L` such
that `[QuasiIsoAt f i]` holds. -/
@[simps! hom]
/--
Definition of `isoOfQuasiIsoAt` / `isoOfQuasiIsoAt` 的定义

English:
definition isoOfQuasiIsoAt
  signature: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  body: asIso (homologyMap f i)

@[reassoc (attr := simp)]

中文:
定义 isoOfQuasiIsoAt
  签名: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  定义体: asIso (homologyMap f i)

@[reassoc (attr := simp)]

Depends on / 依赖: homologyMap
-/
noncomputable def isoOfQuasiIsoAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] : K.homology i ≅ L.homology i :=
  asIso (homologyMap f i)

@[reassoc (attr := simp)]
/--
lemma `isoOfQuasiIsoAt_hom_inv_id` / 引理 `isoOfQuasiIsoAt_hom_inv_id`

English:
lemma isoOfQuasiIsoAt_hom_inv_id
  statement: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoOfQuasiIsoAt_hom_inv_id
  结论: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id, isoOfQuasiIsoAt
-/
lemma isoOfQuasiIsoAt_hom_inv_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoOfQuasiIsoAt_inv_hom_id` / 引理 `isoOfQuasiIsoAt_inv_hom_id`

English:
lemma isoOfQuasiIsoAt_inv_hom_id
  statement: (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
  proof: (isoOfQuasiIsoAt f i).inv_hom_id

中文:
引理 isoOfQuasiIsoAt_inv_hom_id
  结论: (f : K ⟶ L) (i : ι) [K.有同调 i] [L.有同调 i]
  证明: (isoOfQuasiIsoAt f i).inv_hom_id

Depends on / 依赖: inv_hom_id, isoOfQuasiIsoAt
-/
lemma isoOfQuasiIsoAt_inv_hom_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    (isoOfQuasiIsoAt f i).inv ≫ homologyMap f i = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).inv_hom_id

/--
lemma `CochainComplex.quasiIsoAt₀_iff` / 引理 `CochainComplex.quasiIsoAt₀_iff`

English:
lemma CochainComplex.quasiIsoAt₀_iff
  statement: {K L : CochainComplex C Nat} (f : K ⟶ L)
  proof: quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

中文:
引理 上链复形.quasiIsoAt₀_iff
  结论: {K L : 上链复形 C 自然数} (f : K ⟶ L)
  证明: quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

Depends on / 依赖: quasiIsoAt_iff
-/
lemma CochainComplex.quasiIsoAt₀_iff {K L : CochainComplex C Nat} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 0 0 1).HasHomology] [(L.sc' 0 0 1).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 0 0 1).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

/--
lemma `ChainComplex.quasiIsoAt₀_iff` / 引理 `ChainComplex.quasiIsoAt₀_iff`

English:
lemma ChainComplex.quasiIsoAt₀_iff
  statement: {K L : ChainComplex C Nat} (f : K ⟶ L)
  proof: quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

中文:
引理 链复形.quasiIsoAt₀_iff
  结论: {K L : 链复形 C 自然数} (f : K ⟶ L)
  证明: quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

Depends on / 依赖: quasiIsoAt_iff
-/
lemma ChainComplex.quasiIsoAt₀_iff {K L : ChainComplex C Nat} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 1 0 0).HasHomology] [(L.sc' 1 0 0).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' C _ 1 0 0).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

/--
Definition of `QuasiIso` / `QuasiIso` 的定义

English:
class QuasiIso
  parameters: (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomology i]
  axioms and operations (1):
    - quasiIsoAt : forall i, QuasiIsoAt f i  [default: by infer_instance]

中文:
类 拟同构
  参数: (f : K ⟶ L) [对任意 i, K.有同调 i] [对任意 i, L.有同调 i]
  公理与运算 (1 个):
    - quasiIsoAt : 对任意 i, 在处拟同构 f i  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class QuasiIso (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomology i] : Prop where
  quasiIsoAt : forall i, QuasiIsoAt f i := by infer_instance

/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomology i]
  proof: ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

中文:
引理 quasiIso_iff
  条件: (f : K ⟶ L) [对任意 i, K.有同调 i] [对任意 i, L.有同调 i]
  证明: ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

Depends on / 依赖: h.quasiIsoAt, quasiIsoAt
-/
lemma quasiIso_iff (f : K ⟶ L) [forall i, K.HasHomology i] [forall i, L.HasHomology i] :
    QuasiIso f ↔ forall i, QuasiIsoAt f i :=
  ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

attribute [instance] QuasiIso.quasiIsoAt

/--
Instance `quasiIso_of_isIso` / 实例 `quasiIso_of_isIso`

English:
instance quasiIso_of_isIso
  signature: (f : K ⟶ L) [IsIso f] [forall i, K.HasHomology i] [forall i, L.HasHomology i]

中文:
实例 quasiIso_of_isIso
  签名: (f : K ⟶ L) [是同构 f] [对任意 i, K.有同调 i] [对任意 i, L.有同调 i]
-/
instance quasiIso_of_isIso (f : K ⟶ L) [IsIso f] [forall i, K.HasHomology i] [forall i, L.HasHomology i] :
    QuasiIso f where

/--
Instance `quasiIsoAt_comp` / 实例 `quasiIsoAt_comp`

English:
instance quasiIsoAt_comp
  signature: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
  body: by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

中文:
实例 quasiIsoAt_comp
  签名: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.有同调 i]
  定义体: by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

Depends on / 依赖: Functor, Functor.map_comp, ShortComplex, ShortComplex.quasiIso_comp, map_comp, quasiIsoAt_iff, quasiIso_comp
-/
instance quasiIsoAt_comp (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i := by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

/--
Instance `quasiIso_comp` / 实例 `quasiIso_comp`

English:
instance quasiIso_comp
  signature: (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]

中文:
实例 quasiIso_comp
  签名: (φ : K ⟶ L) (φ' : L ⟶ M) [对任意 i, K.有同调 i]
-/
instance quasiIso_comp (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
    [forall i, L.HasHomology i] [forall i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') where

/--
lemma `quasiIsoAt_of_comp_left` / 引理 `quasiIsoAt_of_comp_left`

English:
lemma quasiIsoAt_of_comp_left
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
  proof: by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)

中文:
引理 quasiIsoAt_of_comp_left
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.有同调 i]
  证明: by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)

Depends on / 依赖: IsIso.of_isIso_comp_left, homologyMap, homologyMap_comp, of_isIso_comp_left, quasiIsoAt_iff_isIso_homologyMap
-/
lemma quasiIsoAt_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ' i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_left (homologyMap φ i) (homologyMap φ' i)

/--
lemma `quasiIsoAt_iff_comp_left` / 引理 `quasiIsoAt_iff_comp_left`

English:
lemma quasiIsoAt_iff_comp_left
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
  proof: by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance

中文:
引理 quasiIsoAt_iff_comp_left
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.有同调 i]
  证明: by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance

Depends on / 依赖: infer_instance, quasiIsoAt_of_comp_left
-/
lemma quasiIsoAt_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ' i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_left φ φ' i
  · intro
    infer_instance

/--
lemma `quasiIso_iff_comp_left` / 引理 `quasiIso_iff_comp_left`

English:
lemma quasiIso_iff_comp_left
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_left φ φ']

中文:
引理 quasiIso_iff_comp_left
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) [对任意 i, K.有同调 i]
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_left φ φ']

Depends on / 依赖: quasiIsoAt_iff_comp_left, quasiIso_iff
-/
lemma quasiIso_iff_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
    [forall i, L.HasHomology i] [forall i, M.HasHomology i]
    [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_left φ φ']

/--
lemma `quasiIso_of_comp_left` / 引理 `quasiIso_of_comp_left`

English:
lemma quasiIso_of_comp_left
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
  proof: by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance

中文:
引理 quasiIso_of_comp_left
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) [对任意 i, K.有同调 i]
  证明: by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance

Depends on / 依赖: infer_instance, quasiIso_iff_comp_left
-/
lemma quasiIso_of_comp_left (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
    [forall i, L.HasHomology i] [forall i, M.HasHomology i]
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' := by
  rw [← quasiIso_iff_comp_left φ φ']
  infer_instance

/--
lemma `quasiIsoAt_of_comp_right` / 引理 `quasiIsoAt_of_comp_right`

English:
lemma quasiIsoAt_of_comp_right
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
  proof: by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ i) (homologyMap φ' i)

中文:
引理 quasiIsoAt_of_comp_right
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.有同调 i]
  证明: by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ i) (homologyMap φ' i)

Depends on / 依赖: IsIso.of_isIso_comp_right, homologyMap, homologyMap_comp, of_isIso_comp_right, quasiIsoAt_iff_isIso_homologyMap
-/
lemma quasiIsoAt_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] [hφφ' : QuasiIsoAt (φ ≫ φ') i] :
    QuasiIsoAt φ i := by
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ' hφφ' ⊢
  rw [homologyMap_comp] at hφφ'
  exact IsIso.of_isIso_comp_right (homologyMap φ i) (homologyMap φ' i)

/--
lemma `quasiIsoAt_iff_comp_right` / 引理 `quasiIsoAt_iff_comp_right`

English:
lemma quasiIsoAt_iff_comp_right
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
  proof: by
  constructor
  · intro
    exact quasiIsoAt_of_comp_right φ φ' i
  · intro
    infer_instance

中文:
引理 quasiIsoAt_iff_comp_right
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.有同调 i]
  证明: by
  constructor
  · intro
    exact quasiIsoAt_of_comp_right φ φ' i
  · intro
    infer_instance

Depends on / 依赖: infer_instance, quasiIsoAt_of_comp_right
-/
lemma quasiIsoAt_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [M.HasHomology i]
    [hφ' : QuasiIsoAt φ' i] :
    QuasiIsoAt (φ ≫ φ') i ↔ QuasiIsoAt φ i := by
  constructor
  · intro
    exact quasiIsoAt_of_comp_right φ φ' i
  · intro
    infer_instance

/--
lemma `quasiIso_iff_comp_right` / 引理 `quasiIso_iff_comp_right`

English:
lemma quasiIso_iff_comp_right
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']

中文:
引理 quasiIso_iff_comp_right
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) [对任意 i, K.有同调 i]
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']

Depends on / 依赖: quasiIsoAt_iff_comp_right, quasiIso_iff
-/
lemma quasiIso_iff_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
    [forall i, L.HasHomology i] [forall i, M.HasHomology i]
    [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_iff_comp_right φ φ']

/--
lemma `quasiIso_of_comp_right` / 引理 `quasiIso_of_comp_right`

English:
lemma quasiIso_of_comp_right
  statement: (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
  proof: by
  rw [← quasiIso_iff_comp_right φ φ']
  infer_instance

中文:
引理 quasiIso_of_comp_right
  结论: (φ : K ⟶ L) (φ' : L ⟶ M) [对任意 i, K.有同调 i]
  证明: by
  rw [← quasiIso_iff_comp_right φ φ']
  infer_instance

Depends on / 依赖: infer_instance, quasiIso_iff_comp_right
-/
lemma quasiIso_of_comp_right (φ : K ⟶ L) (φ' : L ⟶ M) [forall i, K.HasHomology i]
    [forall i, L.HasHomology i] [forall i, M.HasHomology i]
    [hφ : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ := by
  rw [← quasiIso_iff_comp_right φ φ']
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_iff_of_arrow_mk_iso` / 引理 `quasiIso_iff_of_arrow_mk_iso`

English:
lemma quasiIso_iff_of_arrow_mk_iso
  statement: (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
  proof: by
  simp [← quasiIso_iff_comp_left (show K' ⟶ K from e.inv.left) φ,
    ← quasiIso_iff_comp_right φ' (show L' ⟶ L from e.inv.right)]

中文:
引理 quasiIso_iff_of_arrow_mk_iso
  结论: (φ : K ⟶ L) (φ' : K' ⟶ L') (e : 箭头.mk φ ≅ 箭头.mk φ')
  证明: by
  simp [← quasiIso_iff_comp_left (show K' ⟶ K from e.inv.left) φ,
    ← quasiIso_iff_comp_right φ' (show L' ⟶ L from e.inv.right)]

Depends on / 依赖: e.inv.left, e.inv.right, quasiIso_iff_comp_left, quasiIso_iff_comp_right
-/
lemma quasiIso_iff_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [forall i, K.HasHomology i] [forall i, L.HasHomology i]
    [forall i, K'.HasHomology i] [forall i, L'.HasHomology i] :
    QuasiIso φ ↔ QuasiIso φ' := by
  simp [← quasiIso_iff_comp_left (show K' ⟶ K from e.inv.left) φ,
    ← quasiIso_iff_comp_right φ' (show L' ⟶ L from e.inv.right)]

/--
lemma `quasiIso_of_arrow_mk_iso` / 引理 `quasiIso_of_arrow_mk_iso`

English:
lemma quasiIso_of_arrow_mk_iso
  statement: (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
  proof: by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]

中文:
引理 quasiIso_of_arrow_mk_iso
  结论: (φ : K ⟶ L) (φ' : K' ⟶ L') (e : 箭头.mk φ ≅ 箭头.mk φ')
  证明: by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]

Depends on / 依赖: quasiIso_iff_of_arrow_mk_iso
-/
lemma quasiIso_of_arrow_mk_iso (φ : K ⟶ L) (φ' : K' ⟶ L') (e : Arrow.mk φ ≅ Arrow.mk φ')
    [forall i, K.HasHomology i] [forall i, L.HasHomology i]
    [forall i, K'.HasHomology i] [forall i, L'.HasHomology i]
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  simpa only [← quasiIso_iff_of_arrow_mk_iso φ φ' e]

/--
lemma `quasiIso_of_retractArrow` / 引理 `quasiIso_of_retractArrow`

English:
lemma quasiIso_of_retractArrow
  statement: {f : K ⟶ L} {f' : K' ⟶ L'}
  proof: quasiIsoAt_of_retract h i

中文:
引理 quasiIso_of_retractArrow
  结论: {f : K ⟶ L} {f' : K' ⟶ L'}
  证明: quasiIsoAt_of_retract h i

Depends on / 依赖: quasiIsoAt_of_retract
-/
lemma quasiIso_of_retractArrow {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') [forall i, K.HasHomology i] [forall i, L.HasHomology i]
    [forall i, K'.HasHomology i] [forall i, L'.HasHomology i] [QuasiIso f'] :
    QuasiIso f where
  quasiIsoAt i := quasiIsoAt_of_retract h i

namespace HomologicalComplex

section PreservesHomology

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁] [Preadditive C₂]
  {K L : HomologicalComplex C₁ c} (φ : K ⟶ L) (F : C₁ ⥤ C₂) [F.Additive]
  [F.PreservesHomology]

section

variable (i : ι) [K.HasHomology i] [L.HasHomology i]
  [((F.mapHomologicalComplex c).obj K).HasHomology i]
  [((F.mapHomologicalComplex c).obj L).HasHomology i]

/--
Instance `quasiIsoAt_map_of_preservesHomology` / 实例 `quasiIsoAt_map_of_preservesHomology`

English:
instance quasiIsoAt_map_of_preservesHomology
  signature: [hφ : QuasiIsoAt φ i]
  body: by
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

中文:
实例 quasiIsoAt_map_of_preservesHomology
  签名: [hφ : 在处拟同构 φ i]
  定义体: by
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

Depends on / 依赖: ShortComplex, ShortComplex.quasiIso_map_of_preservesLeftHomology, quasiIsoAt_iff, quasiIso_map_of_preservesLeftHomology, shortComplexFunctor
-/
instance quasiIsoAt_map_of_preservesHomology [hφ : QuasiIsoAt φ i] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i := by
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

/--
lemma `quasiIsoAt_map_iff_of_preservesHomology` / 引理 `quasiIsoAt_map_iff_of_preservesHomology`

English:
lemma quasiIsoAt_map_iff_of_preservesHomology
  given: [F.ReflectsIsomorphisms]
  proof: by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

中文:
引理 quasiIsoAt_map_iff_of_preservesHomology
  条件: [F.反映同构]
  证明: by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

Depends on / 依赖: ShortComplex, ShortComplex.quasiIso_map_iff_of_preservesLeftHomology, quasiIsoAt_iff, quasiIso_map_iff_of_preservesLeftHomology, shortComplexFunctor
-/
lemma quasiIsoAt_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

end

section

variable [forall i, K.HasHomology i] [forall i, L.HasHomology i]
  [forall i, ((F.mapHomologicalComplex c).obj K).HasHomology i]
  [forall i, ((F.mapHomologicalComplex c).obj L).HasHomology i]

/--
Instance `quasiIso_map_of_preservesHomology` / 实例 `quasiIso_map_of_preservesHomology`

English:
instance quasiIso_map_of_preservesHomology
  signature: [hφ : QuasiIso φ]

中文:
实例 quasiIso_map_of_preservesHomology
  签名: [hφ : 拟同构 φ]
-/
instance quasiIso_map_of_preservesHomology [hφ : QuasiIso φ] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) where

/--
lemma `quasiIso_map_iff_of_preservesHomology` / 引理 `quasiIso_map_iff_of_preservesHomology`

English:
lemma quasiIso_map_iff_of_preservesHomology
  given: [F.ReflectsIsomorphisms]
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_map_iff_of_preservesHomology φ F]

中文:
引理 quasiIso_map_iff_of_preservesHomology
  条件: [F.反映同构]
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_map_iff_of_preservesHomology φ F]

Depends on / 依赖: quasiIsoAt_map_iff_of_preservesHomology, quasiIso_iff
-/
lemma quasiIso_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIso ((F.mapHomologicalComplex c).map φ) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_map_iff_of_preservesHomology φ F]

end

end PreservesHomology

variable (C c)

/--
Definition of `quasiIso` / `quasiIso` 的定义

English:
definition quasiIso
  signature: [CategoryWithHomology C]
  body: fun _ _ f => QuasiIso f

中文:
定义 quasiIso
  签名: [带同调范畴 C]
  定义体: fun _ _ f => QuasiIso f

Depends on / 依赖: QuasiIso
-/
def quasiIso [CategoryWithHomology C] :
    MorphismProperty (HomologicalComplex C c) := fun _ _ f => QuasiIso f

variable {C c} [CategoryWithHomology C]

@[simp]
/--
lemma `mem_quasiIso_iff` / 引理 `mem_quasiIso_iff`

English:
lemma mem_quasiIso_iff
  given: (f : K ⟶ L)
  statement: quasiIso C c f ↔ QuasiIso f
  proof: by rfl

中文:
引理 mem_quasiIso_iff
  条件: (f : K ⟶ L)
  结论: quasiIso C c f ↔ 拟同构 f
  证明: by rfl
-/
lemma mem_quasiIso_iff (f : K ⟶ L) : quasiIso C c f ↔ QuasiIso f := by rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C c).IsMultiplicative
  body: by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem _ _ hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    infer_instance

中文:
实例 :
  签名: (quasiIso C c).是Multiplicative
  定义体: by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem _ _ hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    infer_instance

Depends on / 依赖: comp_mem, infer_instance, mem_quasiIso_iff
-/
instance : (quasiIso C c).IsMultiplicative where
  id_mem _ := by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem _ _ hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C c).HasTwoOutOfThreeProperty
  body: by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    rwa [← quasiIso_iff_comp_right f g]
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    rwa [← quasiIso_iff_comp_left f g]

中文:
实例 :
  签名: (quasiIso C c).有TwoOutOfThreeProperty
  定义体: by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    rwa [← quasiIso_iff_comp_right f g]
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    rwa [← quasiIso_iff_comp_left f g]

Depends on / 依赖: mem_quasiIso_iff, of_precomp, quasiIso_iff_comp_left, quasiIso_iff_comp_right
-/
instance : (quasiIso C c).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    rwa [← quasiIso_iff_comp_right f g]
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    rwa [← quasiIso_iff_comp_left f g]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C c).IsStableUnderRetracts
  body: by
    rw [mem_quasiIso_iff] at hg ⊢
    exact quasiIso_of_retractArrow h

中文:
实例 :
  签名: (quasiIso C c).是StableUnderRetracts
  定义体: by
    rw [mem_quasiIso_iff] at hg ⊢
    exact quasiIso_of_retractArrow h

Depends on / 依赖: mem_quasiIso_iff, quasiIso_of_retractArrow
-/
instance : (quasiIso C c).IsStableUnderRetracts where
  of_retract h hg := by
    rw [mem_quasiIso_iff] at hg ⊢
    exact quasiIso_of_retractArrow h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C c).RespectsIso
  body: MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ (_ : IsIso _) => by rw [mem_quasiIso_iff]; infer_instance)

中文:
实例 :
  签名: (quasiIso C c).RespectsIso
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ (_ : IsIso _) => by rw [mem_quasiIso_iff]; infer_instance)

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, infer_instance, mem_quasiIso_iff, respectsIso_of_isStableUnderComposition
-/
instance : (quasiIso C c).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ _ (_ : IsIso _) => by rw [mem_quasiIso_iff]; infer_instance)

end HomologicalComplex

end

namespace HomotopyEquiv

variable {ι : Type*} {C : Type u} [Category.{v} C] [Preadditive C]
  {c : ComplexShape ι} {K L : HomologicalComplex C c}
  (e : HomotopyEquiv K L)

/--
Instance `quasiIsoAt_hom` / 实例 `quasiIsoAt_hom`

English:
instance quasiIsoAt_hom
  signature: (n : ι) [K.HasHomology n] [L.HasHomology n]
  body: by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  exact (e.toHomologyIso n).isIso_hom

中文:
实例 quasiIsoAt_hom
  签名: (n : ι) [K.有同调 n] [L.有同调 n]
  定义体: by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  exact (e.toHomologyIso n).isIso_hom

Depends on / 依赖: ShortComplex, ShortComplex.quasiIso_iff, e.toHomologyIso, isIso_hom, quasiIsoAt_iff, quasiIso_iff, toHomologyIso
-/
instance quasiIsoAt_hom (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.hom n := by
  rw [quasiIsoAt_iff]; rw [ShortComplex.quasiIso_iff]
  exact (e.toHomologyIso n).isIso_hom

/--
Instance `quasiIsoAt_inv` / 实例 `quasiIsoAt_inv`

English:
instance quasiIsoAt_inv
  signature: (n : ι) [K.HasHomology n] [L.HasHomology n]
  body: e.symm.quasiIsoAt_hom n

中文:
实例 quasiIsoAt_inv
  签名: (n : ι) [K.有同调 n] [L.有同调 n]
  定义体: e.symm.quasiIsoAt_hom n

Depends on / 依赖: e.symm.quasiIsoAt_hom, quasiIsoAt_hom
-/
instance quasiIsoAt_inv (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.inv n :=
  e.symm.quasiIsoAt_hom n

/--
Instance `quasiIso_hom` / 实例 `quasiIso_hom`

English:
instance quasiIso_hom
  signature: [forall n, K.HasHomology n] [forall n, L.HasHomology n]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 quasiIso_hom
  签名: [对任意 n, K.有同调 n] [对任意 n, L.有同调 n]
  定义体: ⟨fun _ => inferInstance⟩
-/
instance quasiIso_hom [forall n, K.HasHomology n] [forall n, L.HasHomology n] :
    QuasiIso e.hom :=
  ⟨fun _ => inferInstance⟩

/--
Instance `quasiIso_inv` / 实例 `quasiIso_inv`

English:
instance quasiIso_inv
  signature: [forall n, K.HasHomology n] [forall n, L.HasHomology n]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 quasiIso_inv
  签名: [对任意 n, K.有同调 n] [对任意 n, L.有同调 n]
  定义体: ⟨fun _ => inferInstance⟩
-/
instance quasiIso_inv [forall n, K.HasHomology n] [forall n, L.HasHomology n] :
    QuasiIso e.inv :=
  ⟨fun _ => inferInstance⟩

end HomotopyEquiv

/--
lemma `homotopyEquivalences_le_quasiIso` / 引理 `homotopyEquivalences_le_quasiIso`

English:
lemma homotopyEquivalences_le_quasiIso
  proof: by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance

中文:
引理 homotopyEquivalences_le_quasiIso
  证明: by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance

Depends on / 依赖: HomologicalComplex, HomologicalComplex.mem_quasiIso_iff, infer_instance, mem_quasiIso_iff
-/
lemma homotopyEquivalences_le_quasiIso
    {ι : Type*} (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) [CategoryWithHomology C] :
    homotopyEquivalences C c <= quasiIso C c := by
  rintro K L _ ⟨e, rfl⟩
  simp only [HomologicalComplex.mem_quasiIso_iff]
  infer_instance
