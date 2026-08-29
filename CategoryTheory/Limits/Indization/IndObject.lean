/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Filtered.Small
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Presheaf

/-!
# Ind-objects

For a presheaf `A : Cᵒᵖ ⥤ Type v` we define the type `IndObjectPresentation A` of presentations
of `A` as a small filtered colimit of representable presheaves and define the predicate
`IsIndObject A` asserting that there is at least one such presentation.

A presheaf is an ind-object if and only if the category `CostructuredArrow yoneda A` is filtered
and finally small. In this way, `CostructuredArrow yoneda A` can be thought of the universal
indexing category for the representation of `A` as a small filtered colimit of representable
presheaves.

## Future work

There are various useful ways to understand natural transformations between ind-objects in terms
of their presentations.

The ind-objects form a locally `v`-small category `IndCategory C` which has numerous interesting
properties.

## Implementation notes

One might be tempted to introduce another universe parameter and consider being a `w`-ind-object
as a property of presheaves `C ⥤ Type max v w`. This comes with significant technical hurdles.
The recommended alternative is to consider ind-objects over `ULiftHom.{w} C` instead.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Limits

section NonSmall

variable {C : Type u} [Category.{v} C]

/--
Definition of `IndObjectPresentation` / `IndObjectPresentation` 的定义

English:
structure IndObjectPresentation
  parameters: (A : Cᵒᵖ ⥤ Type v)
  axioms and operations (6):
    - I : Type v
    - [ℐ : SmallCategory I]
    - [hI : IsFiltered I]
    - F : I ⥤ C
    - ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
    - isColimit : IsColimit (Cocone.mk A ι)

中文:
结构 IndObjectPresentation
  参数: (A : Cᵒᵖ ⥤ 类型v)
  公理与运算 (6 个):
    - I : 类型v
    - [ℐ : 小范畴 I]
    - [hI : 是Filtered I]
    - F : I ⥤ C
    - ι : F ⋙ yoneda ⟶ (函子.const I).obj A
    - isColimit : 是余极限 (余锥.mk A ι)
-/
structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  /-- The indexing category of the filtered colimit presentation -/
  I : Type v
  /-- The indexing category of the filtered colimit presentation -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram of the filtered colimit presentation -/
  F : I ⥤ C
  /-- Use `IndObjectPresentation.cocone` instead. -/
  ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- Use `IndObjectPresentation.coconeIsColimit` instead. -/
  isColimit : IsColimit (Cocone.mk A ι)

namespace IndObjectPresentation

/-- Alternative constructor for `IndObjectPresentation` taking a cocone instead of its defining
natural transformation. -/
@[simps]
/--
Definition of `ofCocone` / `ofCocone` 的定义

English:
definition ofCocone
  signature: {I : Type v} [SmallCategory I] [IsFiltered I] {F : I ⥤ C}
  body: I
  F := F
  ι := c.ι
  isColimit := hc

中文:
定义 ofCocone
  签名: {I : 类型v} [小范畴 I] [是Filtered I] {F : I ⥤ C}
  定义体: I
  F := F
  ι := c.ι
  isColimit := hc
-/
def ofCocone {I : Type v} [SmallCategory I] [IsFiltered I] {F : I ⥤ C}
    (c : Cocone (F ⋙ yoneda)) (hc : IsColimit c) : IndObjectPresentation c.pt where
  I := I
  F := F
  ι := c.ι
  isColimit := hc

variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory P.I
  body: P.ℐ

中文:
实例 :
  签名: 小范畴 P.I
  定义体: P.ℐ
-/
instance : SmallCategory P.I := P.ℐ
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiltered P.I
  body: P.hI

中文:
实例 :
  签名: 是Filtered P.I
  定义体: P.hI

Depends on / 依赖: P.hI
-/
instance : IsFiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps pt]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone (P.F ⋙ yoneda) where
  body: A
  ι := P.ι

中文:
定义 cocone
  签名: : 余锥 (P.F ⋙ yoneda) where
  定义体: A
  ι := P.ι
-/
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι

/--
Definition of `coconeIsColimit` / `coconeIsColimit` 的定义

English:
definition coconeIsColimit
  signature: : IsColimit P.cocone
  body: P.isColimit

中文:
定义 coconeIsColimit
  签名: : 是余极限 P.cocone
  定义体: P.isColimit

Depends on / 依赖: P.isColimit, isColimit
-/
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit

set_option backward.isDefEq.respectTransparency false in
/-- If `A` and `B` are isomorphic, then an ind-object presentation of `A` can be extended to an
ind-object presentation of `B`. -/
@[simps! +dsimpLhs]
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: {A B : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) (η : A ⟶ B)
  body: .ofCocone (P.cocone.extend η) (P.coconeIsColimit.extendIso η)

#adaptation_note

中文:
定义 extend
  签名: {A B : Cᵒᵖ ⥤ 类型v} (P : IndObjectPresentation A) (η : A ⟶ B)
  定义体: .ofCocone (P.cocone.extend η) (P.coconeIsColimit.extendIso η)

#adaptation_note

Depends on / 依赖: P.cocone.extend, P.coconeIsColimit.extendIso, cocone, coconeIsColimit, extend, extendIso, ofCocone
-/
noncomputable def extend {A B : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) (η : A ⟶ B)
    [IsIso η] : IndObjectPresentation B :=
  .ofCocone (P.cocone.extend η) (P.coconeIsColimit.extendIso η)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison functor between the indexing category of the presentation and the
comma category `CostructuredArrow yoneda A`. This functor is always final. -/
@[simps! obj_left obj_right_as obj_hom map_left]
/--
Definition of `toCostructuredArrow` / `toCostructuredArrow` 的定义

English:
definition toCostructuredArrow
  signature: : P.I ⥤ CostructuredArrow yoneda A
  body: P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

中文:
定义 toCostructuredArrow
  签名: : P.I ⥤ CostructuredArrow yoneda A
  定义体: P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, P.cocone.toCostructuredArrow, cocone, toCostructuredArrow
-/
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.toCostructuredArrow.Final
  body: Presheaf.final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

中文:
实例 :
  签名: P.toCostructuredArrow.终
  定义体: Presheaf.final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

Depends on / 依赖: P.coconeIsColimit, Presheaf, Presheaf.final_toCostructuredArrow_comp_pre, coconeIsColimit, final_toCostructuredArrow_comp_pre
-/
instance : P.toCostructuredArrow.Final :=
  Presheaf.final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

set_option backward.defeqAttrib.useBackward true in
/-- Representable presheaves are (trivially) ind-objects. -/
@[simps]
/--
Definition of `yoneda` / `yoneda` 的定义

English:
definition yoneda
  signature: (X : C)
  body: Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun _ => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun _ _ h => h ⟨PUnit.unit⟩ }

中文:
定义 yoneda
  签名: (X : C)
  定义体: Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun _ => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun _ _ h => h ⟨PUnit.unit⟩ }

Depends on / 依赖: Discrete
-/
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun _ => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun _ _ h => h ⟨PUnit.unit⟩ }

end IndObjectPresentation

/--
Definition of `IsIndObject` / `IsIndObject` 的定义

English:
structure IsIndObject
  parameters: (A : Cᵒᵖ ⥤ Type v)
  axioms and operations (1):
    - mk' : : nonempty_presentation : Nonempty (IndObjectPresentation A)

中文:
结构 是IndObject
  参数: (A : Cᵒᵖ ⥤ 类型v)
  公理与运算 (1 个):
    - mk' : : nonempty_presentation : 非空 (IndObjectPresentation A)
-/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)

/--
theorem `IsIndObject.mk` / 定理 `IsIndObject.mk`

English:
theorem IsIndObject.mk
  given: {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)
  statement: IsIndObject A
  proof: ⟨⟨P⟩⟩

中文:
定理 是IndObject.mk
  条件: {A : Cᵒᵖ ⥤ 类型v} (P : IndObjectPresentation A)
  结论: 是IndObject A
  证明: ⟨⟨P⟩⟩
-/
theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩

/--
theorem `isIndObject_yoneda` / 定理 `isIndObject_yoneda`

English:
theorem isIndObject_yoneda
  given: (X : C)
  statement: IsIndObject (yoneda.obj X)
  proof: .mk IndObjectPresentation.yoneda X

中文:
定理 isIndObject_yoneda
  条件: (X : C)
  结论: 是IndObject (yoneda.obj X)
  证明: .mk IndObjectPresentation.yoneda X

Depends on / 依赖: IndObjectPresentation, IndObjectPresentation.yoneda, yoneda
-/
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
.mk IndObjectPresentation.yoneda X

namespace IsIndObject

variable {A : Cᵒᵖ ⥤ Type v}

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η]
  statement: IsIndObject A -> IsIndObject B

中文:
定理 map
  条件: {A B : Cᵒᵖ ⥤ 类型v} (η : A ⟶ B) [是同构 η]
  结论: 是IndObject A -> 是IndObject B
-/
theorem map {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] : IsIndObject A -> IsIndObject B
  | ⟨⟨P⟩⟩ => ⟨⟨P.extend η⟩⟩

/--
theorem `iff_of_iso` / 定理 `iff_of_iso`

English:
theorem iff_of_iso
  given: {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η]
  proof: ⟨.map η, .map (inv η)⟩

中文:
定理 iff_of_iso
  条件: {A B : Cᵒᵖ ⥤ 类型v} (η : A ⟶ B) [是同构 η]
  证明: ⟨.map η, .map (inv η)⟩
-/
theorem iff_of_iso {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] :
    IsIndObject A ↔ IsIndObject B :=
  ⟨.map η, .map (inv η)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsClosedUnderIsomorphisms (IsIndObject (C := C))
  body: h.map i.hom

中文:
实例 :
  签名: ObjectProperty.在同构下封闭 (是IndObject (C := C))
  定义体: h.map i.hom
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (IsIndObject (C := C)) where
  of_iso i h := h.map i.hom

/--
Definition of `presentation` / `presentation` 的定义

English:
definition presentation
  signature: : IsIndObject A -> IndObjectPresentation A

中文:
定义 presentation
  签名: : 是IndObject A -> IndObjectPresentation A
-/
noncomputable def presentation : IsIndObject A -> IndObjectPresentation A
  | ⟨P⟩ => P.some

/--
theorem `isFiltered` / 定理 `isFiltered`

English:
theorem isFiltered
  given: (h : IsIndObject A)
  statement: IsFiltered (CostructuredArrow yoneda A)
  proof: IsFiltered.of_final h.presentation.toCostructuredArrow

中文:
定理 isFiltered
  条件: (h : 是IndObject A)
  结论: 是Filtered (CostructuredArrow yoneda A)
  证明: IsFiltered.of_final h.presentation.toCostructuredArrow

Depends on / 依赖: IsFiltered, IsFiltered.of_final, h.presentation.toCostructuredArrow, of_final, presentation, toCostructuredArrow
-/
theorem isFiltered (h : IsIndObject A) : IsFiltered (CostructuredArrow yoneda A) :=
  IsFiltered.of_final h.presentation.toCostructuredArrow

/--
theorem `finallySmall` / 定理 `finallySmall`

English:
theorem finallySmall
  given: (h : IsIndObject A)
  statement: FinallySmall.{v} (CostructuredArrow yoneda A)
  proof: FinallySmall.mk' h.presentation.toCostructuredArrow

中文:
定理 finallySmall
  条件: (h : 是IndObject A)
  结论: FinallySmall.{v} (CostructuredArrow yoneda A)
  证明: FinallySmall.mk' h.presentation.toCostructuredArrow

Depends on / 依赖: FinallySmall, FinallySmall.mk, h.presentation.toCostructuredArrow, presentation, toCostructuredArrow
-/
theorem finallySmall (h : IsIndObject A) : FinallySmall.{v} (CostructuredArrow yoneda A) :=
  FinallySmall.mk' h.presentation.toCostructuredArrow

end IsIndObject

open IsFiltered.SmallFilteredIntermediate

/--
theorem `isIndObject_of_isFiltered_of_finallySmall` / 定理 `isIndObject_of_isFiltered_of_finallySmall`

English:
theorem isIndObject_of_isFiltered_of_finallySmall
  statement: (A : Cᵒᵖ ⥤ Type v)
  proof: by
  have h₁ : (factoring (fromFinalModel (CostructuredArrow yoneda A)) ⋙
      inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final := Functor.final_of_natIso
    (factoringCompInclusion (fromFinalModel <| CostructuredArrow yoneda A)).symm
  have h₂ : Functor.Final (inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
    Functor.final_of_comp_full_faithful' (factoring _) (inclusion _)
  let c := (Presheaf.tautologicalCocone A).whisker
    (inclusion (fromFinalModel (CostructuredArrow yoneda A)))
  let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm
    (Presheaf.isColimitTautologicalCocone A)
  have hq : Nonempty (FinalModel (CostructuredArrow yoneda A)) := Nonempty.map
    (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
  exact ⟨_, inclusion (fromFinalModel _) ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩

中文:
定理 isIndObject_of_isFiltered_of_finallySmall
  结论: (A : Cᵒᵖ ⥤ 类型v)
  证明: by
  have h₁ : (factoring (fromFinalModel (CostructuredArrow yoneda A)) ⋙
      inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final := Functor.final_of_natIso
    (factoringCompInclusion (fromFinalModel <| CostructuredArrow yoneda A)).symm
  have h₂ : Functor.Final (inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
    Functor.final_of_comp_full_faithful' (factoring _) (inclusion _)
  let c := (Presheaf.tautologicalCocone A).whisker
    (inclusion (fromFinalModel (CostructuredArrow yoneda A)))
  let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm
    (Presheaf.isColimitTautologicalCocone A)
  have hq : Nonempty (FinalModel (CostructuredArrow yoneda A)) := Nonempty.map
    (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
  exact ⟨_, inclusion (fromFinalModel _) ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩

Depends on / 依赖: CostructuredArrow, Functor, Functor.Final, Functor.final_of_comp_full_faithful, Functor.final_of_natIso, Presheaf, Presheaf.tautologicalCocone, factoring, factoringCompInclusion, final_of_comp_full_faithful, final_of_natIso, fromFinalModel, inclusion, tautologicalCocone, whisker, yoneda
-/
theorem isIndObject_of_isFiltered_of_finallySmall (A : Cᵒᵖ ⥤ Type v)
    [IsFiltered (CostructuredArrow yoneda A)] [FinallySmall.{v} (CostructuredArrow yoneda A)] :
    IsIndObject A := by
  have h₁ : (factoring (fromFinalModel (CostructuredArrow yoneda A)) ⋙
      inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final := Functor.final_of_natIso
    (factoringCompInclusion (fromFinalModel <| CostructuredArrow yoneda A)).symm
  have h₂ : Functor.Final (inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
    Functor.final_of_comp_full_faithful' (factoring _) (inclusion _)
  let c := (Presheaf.tautologicalCocone A).whisker
    (inclusion (fromFinalModel (CostructuredArrow yoneda A)))
  let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm
    (Presheaf.isColimitTautologicalCocone A)
  have hq : Nonempty (FinalModel (CostructuredArrow yoneda A)) := Nonempty.map
    (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
  exact ⟨_, inclusion (fromFinalModel _) ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩

/--
theorem `isIndObject_iff` / 定理 `isIndObject_iff`

English:
theorem isIndObject_iff
  given: (A : Cᵒᵖ ⥤ Type v)
  statement: IsIndObject A ↔
  proof: ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩

中文:
定理 isIndObject_iff
  条件: (A : Cᵒᵖ ⥤ 类型v)
  结论: 是IndObject A ↔
  证明: ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩

Depends on / 依赖: finallySmall, h.finallySmall, h.isFiltered, isFiltered, isIndObject_of_isFiltered_of_finallySmall
-/
theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) : IsIndObject A ↔
    (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) :=
  ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩

/--
theorem `isIndObject_limit_comp_yoneda` / 定理 `isIndObject_limit_comp_yoneda`

English:
theorem isIndObject_limit_comp_yoneda
  given: {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F]
  proof: IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

中文:
定理 isIndObject_limit_comp_yoneda
  条件: {J : 类型u'} [范畴.{v'} J] (F : J ⥤ C) [有极限 F]
  证明: IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

Depends on / 依赖: IsIndObject, IsIndObject.map, isIndObject_yoneda, preservesLimitIso, yoneda
-/
theorem isIndObject_limit_comp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F] :
    IsIndObject (limit (F ⋙ yoneda)) :=
  IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

end NonSmall

section Small

variable {C : Type u} [SmallCategory C]

/--
lemma `isIndObject_iff_preservesFiniteLimits` / 引理 `isIndObject_iff_preservesFiniteLimits`

English:
lemma isIndObject_iff_preservesFiniteLimits
  given: [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type u)
  proof: (isIndObject_iff A).trans by
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
    · apply preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    · exact isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A
    · have := essentiallySmallSelf (CostructuredArrow yoneda A)
      apply finallySmall_of_essentiallySmall

中文:
引理 isIndObject_iff_preservesFiniteLimits
  条件: [有有限余极限 C] (A : Cᵒᵖ ⥤ 类型u)
  证明: (isIndObject_iff A).trans by
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
    · apply preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    · exact isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A
    · have := essentiallySmallSelf (CostructuredArrow yoneda A)
      apply finallySmall_of_essentiallySmall

Depends on / 依赖: CostructuredArrow, essentiallySmallSelf, finallySmall_of_essentiallySmall, isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits, isIndObject_iff, preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda, yoneda
-/
lemma isIndObject_iff_preservesFiniteLimits [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type u) :
    IsIndObject A ↔ PreservesFiniteLimits A :=
(isIndObject_iff A).trans by
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
    · apply preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    · exact isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A
    · have := essentiallySmallSelf (CostructuredArrow yoneda A)
      apply finallySmall_of_essentiallySmall

end Small

end CategoryTheory.Limits
