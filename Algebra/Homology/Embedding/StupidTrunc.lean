/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The stupid truncation of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we define
a functor `stupidTruncFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
which sends `K` to `K.stupidTrunc e` which is defined as `(K.restriction e).extend e`.

## TODO (@joelriou)
* define the inclusion `e.stupidTruncFunctor C ⟶ 𝟭 _` when `[e.IsTruncGE]`;
* define the projection `𝟭 _ ⟶ e.stupidTruncFunctor C` when `[e.IsTruncLE]`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

/--
Definition of `stupidTrunc` / `stupidTrunc` 的定义

English:
definition stupidTrunc
  signature: : HomologicalComplex C c'
  body: ((K.restriction e).extend e)

中文:
定义 stupidTrunc
  签名: : HomologicalComplex C c'
  定义体: ((K.restriction e).extend e)

Depends on / 依赖: K.restriction, extend, restriction
-/
noncomputable def stupidTrunc : HomologicalComplex C c' := ((K.restriction e).extend e)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictlySupported (K.stupidTrunc e) e
  body: by
  dsimp [stupidTrunc]
  infer_instance

中文:
实例 :
  签名: IsStrictlySupported (K.stupidTrunc e) e
  定义体: by
  dsimp [stupidTrunc]
  infer_instance

Depends on / 依赖: infer_instance, stupidTrunc
-/
instance : IsStrictlySupported (K.stupidTrunc e) e := by
  dsimp [stupidTrunc]
  infer_instance

/--
Definition of `stupidTruncXIso` / `stupidTruncXIso` 的定义

English:
definition stupidTruncXIso
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i')
  body: (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

中文:
定义 stupidTruncXIso
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i')
  定义体: (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

Depends on / 依赖: K.restriction, eqToIso, extendXIso, restriction
-/
noncomputable def stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.stupidTrunc e).X i' ≅ K.X i' :=
  (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

/--
lemma `isZero_stupidTrunc_X` / 引理 `isZero_stupidTrunc_X`

English:
lemma isZero_stupidTrunc_X
  given: (i' : ι') (hi' : forall i, e.f i != i')
  proof: isZero_extend_X _ _ _ hi'

中文:
引理 isZero_stupidTrunc_X
  条件: (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: isZero_extend_X _ _ _ hi'

Depends on / 依赖: isZero_extend_X
-/
lemma isZero_stupidTrunc_X (i' : ι') (hi' : forall i, e.f i != i') :
    IsZero ((K.stupidTrunc e).X i') :=
  isZero_extend_X _ _ _ hi'

instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] :
    IsStrictlySupported (K.stupidTrunc e) e' where
  isZero i' hi' := by
    by_cases hi'' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso (K.stupidTruncXIso e hi)
    · apply isZero_stupidTrunc_X
      simpa using hi''

/--
lemma `isZero_stupidTrunc_iff` / 引理 `isZero_stupidTrunc_iff`

English:
lemma isZero_stupidTrunc_iff
  proof: by
  constructor
  · exact fun h => ⟨fun i =>
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i => (h.isZero i).of_iso (K.stupid

中文:
引理 isZero_stupidTrunc_iff
  证明: by
  constructor
  · exact fun h => ⟨fun i =>
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i => (h.isZero i).of_iso (K.stupid

Depends on / 依赖: K.stupidTruncXIso, h.isZero, infer_instance, isZero, isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside, map_isZero, of_iso, stupidTruncXIso
-/
lemma isZero_stupidTrunc_iff :
    IsZero (K.stupidTrunc e) ↔ K.IsStrictlySupportedOutside e := by
  constructor
  · exact fun h => ⟨fun i =>
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i => (h.isZero i).of_iso (K.stupidTruncXIso e rfl)⟩

variable {K L M}

/--
Definition of `stupidTruncMap` / `stupidTruncMap` 的定义

English:
definition stupidTruncMap
  signature: : K.stupidTrunc e ⟶ L.stupidTrunc e
  body: extendMap (restrictionMap φ e) e

中文:
定义 stupidTruncMap
  签名: : K.stupidTrunc e ⟶ L.stupidTrunc e
  定义体: extendMap (restrictionMap φ e) e

Depends on / 依赖: extendMap, restrictionMap
-/
noncomputable def stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e :=
  extendMap (restrictionMap φ e) e

variable (K) in
@[simp]
/--
lemma `stupidTruncMap_id` / 引理 `stupidTruncMap_id`

English:
lemma stupidTruncMap_id
  statement: stupidTruncMap (𝟙 K) e = 𝟙 _
  proof: by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]

中文:
引理 stupidTruncMap_id
  结论: stupidTruncMap (𝟙 K) e = 𝟙 _
  证明: by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]

Depends on / 依赖: stupidTrunc, stupidTruncMap
-/
lemma stupidTruncMap_id : stupidTruncMap (𝟙 K) e = 𝟙 _ := by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]
/--
lemma `stupidTruncMap_comp` / 引理 `stupidTruncMap_comp`

English:
lemma stupidTruncMap_comp
  proof: by
  simp [stupidTruncMap, stupidTrunc]

中文:
引理 stupidTruncMap_comp
  证明: by
  simp [stupidTruncMap, stupidTrunc]

Depends on / 依赖: stupidTrunc, stupidTruncMap
-/
lemma stupidTruncMap_comp :
    stupidTruncMap (φ ≫ φ') e = stupidTruncMap φ e ≫ stupidTruncMap φ' e := by
  simp [stupidTruncMap, stupidTrunc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `stupidTruncMap_stupidTruncXIso_hom` / 引理 `stupidTruncMap_stupidTruncXIso_hom`

English:
lemma stupidTruncMap_stupidTruncXIso_hom
  given: {i : ι} {i' : ι'} (hi : e.f i = i')
  proof: by
  subst hi
  simp [stupidTruncMap, stupidTruncXIso, extendMap_f _ _ rfl]

中文:
引理 stupidTruncMap_stupidTruncXIso_hom
  条件: {i : ι} {i' : ι'} (hi : e.f i = i')
  证明: by
  subst hi
  simp [stupidTruncMap, stupidTruncXIso, extendMap_f _ _ rfl]

Depends on / 依赖: extendMap_f, stupidTruncMap, stupidTruncXIso
-/
lemma stupidTruncMap_stupidTruncXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (stupidTruncMap φ e).f i' ≫ (L.stupidTruncXIso e hi).hom =
      (K.stupidTruncXIso e hi).hom ≫ φ.f i' := by
  subst hi
  simp [stupidTruncMap, stupidTruncXIso, extendMap_f _ _ rfl]

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The stupid truncation functor `HomologicalComplex C c' ⥤ HomologicalComplex C c'`
given by an embedding `e : Embedding c c'` of complex shapes. -/
@[simps]
/--
Definition of `stupidTruncFunctor` / `stupidTruncFunctor` 的定义

English:
definition stupidTruncFunctor
  signature: [e.IsRelIff]
  body: K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

中文:
定义 stupidTruncFunctor
  签名: [e.IsRelIff]
  定义体: K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

Depends on / 依赖: K.stupidTrunc, stupidTrunc
-/
noncomputable def stupidTruncFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

end ComplexShape.Embedding
