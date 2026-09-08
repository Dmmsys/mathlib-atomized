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

/-- The data that witnesses that a presheaf `A` is an ind-object. It consists of a small
filtered indexing category `I`, a diagram `F : I ⥤ C` and the data for a colimit cocone on
`F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v` with cocone point `A`. -/
/-
**CategoryTheory.Limits.IndObjectPresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor Cᵒᵖ (Type v) → Type (max u (v + 1))
参数：Type v；max u (v + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data that witnesses that a presheaf `A` is an ind-object. It consists of a s
mall
filtered indexing category `I`, a diagram `F : I ⥤ C` and the data for a colimit
 cocone on
`F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v` with cocone point `A`.
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
/-
**CategoryTheory.Limits.IndObjectPresentation.ofCocone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：ofCocone {I : Type v} [SmallCategory I] [IsFiltered I] {F : I ⥤ C} (c : Co
cone (F ⋙ yoneda)) (hc : IsColimit c) : IndObjectPresentation c.pt where I
参数：c : Cocone (F ⋙ yoneda)；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for `IndObjectPresentation` taking a cocone instead of i
ts defining
natural transformation.
-/
def ofCocone {I : Type v} [SmallCategory I] [IsFiltered I] {F : I ⥤ C}
    (c : Cocone (F ⋙ yoneda)) (hc : IsColimit c) : IndObjectPresentation c.pt where
  I := I
  F := F
  ι := c.ι
  isColimit := hc

variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)
/-
**CategoryTheory.Limits.IndObjectPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits.IndObjectPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SmallCategory P.I := P.ℐ
/-
**CategoryTheory.Limits.IndObjectPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits.IndObjectPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps pt]
/-
**CategoryTheory.Limits.IndObjectPresentation.cocone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：cocone : Cocone (P.F ⋙ yoneda) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (colimit) cocone with cocone point `A`.
-/
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι

/-- `P.cocone` is a colimit cocone. -/
/-
**CategoryTheory.Limits.IndObjectPresentation.coconeIsColimit** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：coconeIsColimit : IsColimit P.cocone
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.cocone` is a colimit cocone.
-/
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit

set_option backward.isDefEq.respectTransparency false in
/-- If `A` and `B` are isomorphic, then an ind-object presentation of `A` can be extended to an
ind-object presentation of `B`. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Limits.IndObjectPresentation.extend** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：extend {A B : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) (η : A ⟶ B) [IsI
so η] : IndObjectPresentation B
参数：P : IndObjectPresentation A；η : A ⟶ B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instIsFilteredI`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (T
ype v)}   (P : CategoryTheory.Limits.IndObjectPre…

--- 原说明 ---
If `A` and `B` are isomorphic, then an ind-object presentation of `A` can be ext
ended to an
ind-object presentation of `B`.
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
/-
**CategoryTheory.Limits.IndObjectPresentation.toCostructuredArrow** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical comparison functor between the indexing category of the presentati
on and the
comma category `CostructuredArrow yoneda A`. This functor is always final.
-/
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _
/-
**CategoryTheory.Limits.IndObjectPresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits.IndObjectPresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.toCostructuredArrow.Final :=
  Presheaf.final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

set_option backward.defeqAttrib.useBackward true in
/-- Representable presheaves are (trivially) ind-objects. -/
@[simps]
/-
**CategoryTheory.Limits.IndObjectPresentation.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.IndObjectPresentation`。
形式化陈述：yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where I
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsFilteredDiscretePUnit`：CategoryTheory.IsFiltered (C
ategoryTheory.Discrete PUnit.{u_1 + 1})

--- 原说明 ---
Representable presheaves are (trivially) ind-objects.
-/
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun _ => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun _ _ h => h ⟨PUnit.unit⟩ }

end IndObjectPresentation

/-- A presheaf is called an ind-object if it can be written as a filtered colimit of representable
presheaves. -/
/-
**CategoryTheory.Limits.IsIndObject** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor Cᵒᵖ (Type v) → Prop
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf is called an ind-object if it can be written as a filtered colimit of
 representable
presheaves.
-/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)
/-
**CategoryTheory.Limits.IsIndObject.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.IsIndObject`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   (P : CategoryTheory.Limits.IndObjectPresentation A), 
CategoryTheory.Limits.IsIndObject A
参数：Type v；P : CategoryTheory.Limits.IndObjectPresentation A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩

/-- Representable presheaves are (trivially) ind-objects. -/
/-
**CategoryTheory.Limits.isIndObject_yoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsIndObject.mk`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (Type v)}   (P : Category
Theory.Limits.IndObjectPre…

--- 原说明 ---
Representable presheaves are (trivially) ind-objects.
-/
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
  .mk <| IndObjectPresentation.yoneda X

namespace IsIndObject

variable {A : Cᵒᵖ ⥤ Type v}

/-
**CategoryTheory.Limits.IsIndObject.map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.IsIndObject`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B : CategoryTh
eory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B)   [CategoryTheory.IsIso η], CategoryTheor
y.Limits.IsIndObject A → CategoryTheory.Limits.IsIndObject B
参数：Type v；η : A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] : IsIndObject A → IsIndObject B
  | ⟨⟨P⟩⟩ => ⟨⟨P.extend η⟩⟩
/-
**CategoryTheory.Limits.IsIndObject.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.IsIndObject`。
形式化陈述：iff_of_iso {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] : IsIndObject A ↔ Is
IndObject B
参数：η : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
-/
theorem iff_of_iso {A B : Cᵒᵖ ⥤ Type v} (η : A ⟶ B) [IsIso η] :
    IsIndObject A ↔ IsIndObject B :=
  ⟨.map η, .map (inv η)⟩
/-
**CategoryTheory.Limits.IsIndObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits.IsIndObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (IsIndObject (C := C)) where
  of_iso i h := h.map i.hom

/-- Pick a presentation for an ind-object using choice. -/
/-
**CategoryTheory.Limits.IsIndObject.presentation** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.IsIndObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A : Cate
goryTheory.Functor Cᵒᵖ (Type v)} →       CategoryTheory.Limits.IsIndObject A → C
ategoryTheory.Limits.IndObjectPresentation A
参数：Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pick a presentation for an ind-object using choice.
-/
noncomputable def presentation : IsIndObject A → IndObjectPresentation A
  | ⟨P⟩ => P.some
/-
**CategoryTheory.Limits.IsIndObject.isFiltered** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.IsIndObject`。
形式化陈述：isFiltered (h : IsIndObject A) : IsFiltered (CostructuredArrow yoneda A)
参数：h : IsIndObject A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_final`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instFinalICostructuredArrowF
unctorOppositeTypeYonedaToCostructuredArrow`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (Type v)}   (P : CategoryT
heory.Limits.IndObjectPre…
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instIsFilteredI`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (T
ype v)}   (P : CategoryTheory.Limits.IndObjectPre…
-/
theorem isFiltered (h : IsIndObject A) : IsFiltered (CostructuredArrow yoneda A) :=
  IsFiltered.of_final h.presentation.toCostructuredArrow
/-
**CategoryTheory.Limits.IsIndObject.finallySmall** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.IsIndObject`。
形式化陈述：finallySmall (h : IsIndObject A) : FinallySmall.{v} (CostructuredArrow yon
eda A)
参数：h : IsIndObject A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinallySmall.mk'`：∀ {J : Type u} [inst : CategoryTheory.C
ategory.{v, u} J] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (F : 
CategoryTheory.Functo…
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instFinalICostructuredArrowF
unctorOppositeTypeYonedaToCostructuredArrow`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (Type v)}   (P : CategoryT
heory.Limits.IndObjectPre…
-/
theorem finallySmall (h : IsIndObject A) : FinallySmall.{v} (CostructuredArrow yoneda A) :=
  FinallySmall.mk' h.presentation.toCostructuredArrow

end IsIndObject

open IsFiltered.SmallFilteredIntermediate

/-
**CategoryTheory.Limits.isIndObject_of_isFiltered_of_finallySmall** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIndObject_of_isFiltered_of_finallySmall (A : Cᵒᵖ ⥤ Type v) [IsFiltered (
CostructuredArrow yoneda A)] [FinallySmall.{v} (CostructuredArrow yoneda A)] : I
sIndObject A
参数：A : Cᵒᵖ ⥤ Type v；CostructuredArrow yoneda A；CostructuredArrow yoneda A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.Functor.final_of_natIso`：final_of_natIso {F F' : C ⥤ D} [
Final F] (i : F ≅ F') : Final F' where out _
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful'`：final_of_comp_full_
faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final G
· 使用定理 `CategoryTheory.IsFiltered.SmallFilteredIntermediate.instFullInclusion`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.IsFilteredOrEmpty C] {D : Type u₁}   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsFiltered.SmallFilteredIntermediate.instFaithfulInclusio
n`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTh
eory.IsFilteredOrEmpty C] {D : Type u₁}   [inst_2 : CategoryThe…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `CategoryTheory.IsFiltered.SmallFilteredIntermediate.instOfNonempty`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Is
FilteredOrEmpty C] {D : Type u₁}   [inst_2 : CategoryThe…
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

/-- The recognition theorem for ind-objects: `A : Cᵒᵖ ⥤ Type v` is an ind-object if and only if
`CostructuredArrow yoneda A` is filtered and finally `v`-small.
Theorem 6.1.5 of [Kashiwara2006] -/
/-
**CategoryTheory.Limits.isIndObject_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：isIndObject_iff (A : Cᵒᵖ ⥤ Type v) : IsIndObject A ↔ (IsFiltered (Costruct
uredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A))
参数：A : Cᵒᵖ ⥤ Type v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsIndObject.isFiltered`：isFiltered (h : IsIndObjec
t A) : IsFiltered (CostructuredArrow yoneda A)
· 使用定理 `CategoryTheory.Limits.IsIndObject.finallySmall`：finallySmall (h : IsIndO
bject A) : FinallySmall.{v} (CostructuredArrow yoneda A)
· 使用定理 `CategoryTheory.Limits.isIndObject_of_isFiltered_of_finallySmall`：isIndOb
ject_of_isFiltered_of_finallySmall (A : Cᵒᵖ ⥤ Type v) [IsFiltered (CostructuredA
rrow yoneda A)] [FinallySmall.{v} (CostructuredArrow …

--- 原说明 ---
The recognition theorem for ind-objects: `A : Cᵒᵖ ⥤ Type v` is an ind-object if 
and only if
`CostructuredArrow yoneda A` is filtered and finally `v`-small.
Theorem 6.1.5 of [Kashiwara2006]
-/
theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) : IsIndObject A ↔
    (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) :=
  ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩

/-- If a limit already exists in `C`, then the limit of the image of the diagram under the Yoneda
embedding is an ind-object. -/
/-
**CategoryTheory.Limits.isIndObject_limit_comp_yoneda** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isIndObject_limit_comp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) 
[HasLimit F] : IsIndObject (limit (F ⋙ yoneda))
参数：F : J ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsIndObject.map`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B : CategoryTheory.Functor Cᵒᵖ (Type v)} (η : A ⟶ B) 
  [CategoryTheory.IsIso η],…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.isIndObject_yoneda`：isIndObject_yoneda (X : C) : I
sIndObject (yoneda.obj X)

--- 原说明 ---
If a limit already exists in `C`, then the limit of the image of the diagram und
er the Yoneda
embedding is an ind-object.
-/
theorem isIndObject_limit_comp_yoneda {J : Type u'} [Category.{v'} J] (F : J ⥤ C) [HasLimit F] :
    IsIndObject (limit (F ⋙ yoneda)) :=
  IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

end NonSmall

section Small

variable {C : Type u} [SmallCategory C]

/-- Presheaves over a small finitely cocomplete category `C : Type u` are Ind-objects if and only if
they are left-exact. -/
/-
**CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIndObject_iff_preservesFiniteLimits [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Typ
e u) : IsIndObject A ↔ PreservesFiniteLimits A
参数：A : Cᵒᵖ ⥤ Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.isIndObject_iff`：isIndObject_iff (A : Cᵒᵖ ⥤ Type v
) : IsIndObject A ↔ (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} 
(CostructuredArrow yoneda A…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_isFiltered_costructuredAr
row_yoneda`：preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda [IsFilt
ered (CostructuredArrow yoneda A)] : PreservesFiniteLimits A where prese…
· 使用定理 `CategoryTheory.Limits.isFiltered_costructuredArrow_yoneda_of_preservesFi
niteLimits`：isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits [Preser
vesFiniteLimits A] : IsFiltered (CostructuredArrow yoneda A)
· 使用定理 `CategoryTheory.essentiallySmallSelf`：essentiallySmallSelf : EssentiallyS
mall.{max w v u} C
· 使用定理 `CategoryTheory.finallySmall_of_essentiallySmall`：finallySmall_of_essenti
allySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J

--- 原说明 ---
Presheaves over a small finitely cocomplete category `C : Type u` are Ind-object
s if and only if
they are left-exact.
-/
lemma isIndObject_iff_preservesFiniteLimits [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type u) :
    IsIndObject A ↔ PreservesFiniteLimits A :=
  (isIndObject_iff A).trans <| by
    refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
    · apply preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    · exact isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A
    · have := essentiallySmallSelf (CostructuredArrow yoneda A)
      apply finallySmall_of_essentiallySmall

end Small

end CategoryTheory.Limits

