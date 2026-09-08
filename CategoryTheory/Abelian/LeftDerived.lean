/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Riccardo Brasca, Adam Topaz, Jujian Zhang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Left-derived functors

We define the left-derived functors `F.leftDerived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

We first define a functor
`F.leftDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which is
`projectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`P : ProjectiveResolution X`, then `F.leftDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `P.complex`
(this isomorphism is `P.isoLeftDerivedToHomotopyCategoryObj F`).

Then, the left-derived functors `F.leftDerived n : C ⥤ D` are obtained by composing
`F.leftDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_leftDerived_obj_projective_succ`: projective objects have no higher
  left derived functor.
* `NatTrans.leftDerived`: the natural transformation between left derived functors
  induced by a natural transformation.
* `Functor.fromLeftDerivedZero`: the natural transformation `F.leftDerived 0 ⟶ F`,
  which is an isomorphism when `F` is right exact (i.e. preserves finite colimits),
  see also `Functor.leftDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.leftDerived` (and `Functor.rightDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a left derived functor
  `F.leftDerivedFunctorMinus : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D`,
  and `F.leftDerived` shall be redefined using `F.leftDerivedFunctorMinus`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]

/-- When `F : C ⥤ D` is an additive functor, this is
the functor `C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which
sends `X : C` to `F` applied to a projective resolution of `X`. -/
/-
**CategoryTheory.Functor.leftDerivedToHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [CategoryTheory.HasProjectiveResolutions
 C] →             [inst_4 : CategoryTheory.Abelian D] →               (F : Categ
oryTheory.Functor C D) →                 [F.Additive] → CategoryTheory.Functor C
 (HomotopyCategory D (ComplexShape.down ℕ))
参数：F : CategoryTheory.Functor C D；HomotopyCategory D (ComplexShape.down ℕ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
When `F : C ⥤ D` is an additive functor, this is
the functor `C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which
sends `X : C` to `F` applied to a projective resolution of `X`.
-/
noncomputable def Functor.leftDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.down ℕ) :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _

/-- If `P : ProjectiveResolution Z` and `F : C ⥤ D` is an additive functor, this is
an isomorphism between `F.leftDerivedToHomotopyCategory.obj X` and the complex
obtained by applying `F` to `P.complex`. -/
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasProjectiveRe
solutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {
X : C} →                 (P : CategoryTheory.ProjectiveResolution X) →          
         (F : CategoryTheory.Functor C D) →                     [inst_5 : F.Addi
tive] →                       F.leftDerivedToHomotopyCategory.obj X ≅           
              ((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp             
                  (HomotopyCategory.quotient D (ComplexShape.down ℕ))).obj      
                     P.complex
参数：P : CategoryTheory.ProjectiveResolution X；F : CategoryTheory.Functor C D；(F.m
apHomologicalComplex (ComplexShape.down ℕ)).comp                               (
HomotopyCategory.quotient D (ComplexShape.down ℕ))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `P : ProjectiveResolution Z` and `F : C ⥤ D` is an additive functor, this is
an isomorphism between `F.leftDerivedToHomotopyCategory.obj X` and the complex
obtained by applying `F` to `P.complex`.
-/
noncomputable def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj P.complex :=
  (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_na
turality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {X Y : C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)
   (Q : CategoryTheory.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   Ca
tegoryTheory.CategoryStruct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStru
ct.comp (P.π.f 0) f →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additiv
e],       CategoryTheory.CategoryStruct.comp (P.isoLeftDerivedToHomotopyCategory
Obj F).inv           (F.leftDerivedToHomotopyCategory.map f) =         CategoryT
heory.CategoryStruct.comp           (((F.mapHomologicalComplex (ComplexShape.dow
n ℕ)).comp                 (HomotopyCategory.quotient D (ComplexShape.down ℕ))).
map             φ)           (Q.isoLeftDerivedToHomotopyCategoryObj F).inv
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；F : CategoryThe
ory.Functor C D；P.isoLeftDerivedToHomotopyCategoryObj F；F.leftDerivedToHomotopyC
ategory.map f；((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp             
    (HomotopyCategory.quotient D (ComplexShape.down ℕ))).map             φ；Q.iso
LeftDerivedToHomotopyCategoryObj F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.ProjectiveResolution.iso_inv_naturality`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [
inst_2 : CategoryTheory.HasProjectiveResolut…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    (P.isoLeftDerivedToHomotopyCategoryObj F).inv ≫ F.leftDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (Q.isoLeftDerivedToHomotopyCategoryObj F).inv := by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [assoc, ← Functor.map_comp, iso_inv_naturality f P Q φ comm, Functor.map_comp]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down ℕ)).inv.naturality_assoc]
  rfl

@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_na
turality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {X Y : C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)
   (Q : CategoryTheory.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   Ca
tegoryTheory.CategoryStruct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStru
ct.comp (P.π.f 0) f →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additiv
e],       CategoryTheory.CategoryStruct.comp (F.leftDerivedToHomotopyCategory.ma
p f)           (Q.isoLeftDerivedToHomotopyCategoryObj F).hom =         CategoryT
heory.CategoryStruct.comp (P.isoLeftDerivedToHomotopyCategoryObj F).hom         
  (((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp                 (Homoto
pyCategory.quotient D (ComplexShape.down ℕ))).map             φ)
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；F : CategoryThe
ory.Functor C D；F.leftDerivedToHomotopyCategory.map f；Q.isoLeftDerivedToHomotopy
CategoryObj F；P.isoLeftDerivedToHomotopyCategoryObj F；((F.mapHomologicalComplex 
(ComplexShape.down ℕ)).comp                 (HomotopyCategory.quotient D (Comple
xShape.down ℕ))).map             φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_
inv_naturality_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {
D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Catego
ry…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.map f ≫ (Q.isoLeftDerivedToHomotopyCategoryObj F).hom =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
    dsimp
    rw [← cancel_epi (P.isoLeftDerivedToHomotopyCategoryObj F).inv, Iso.inv_hom_id_assoc,
      isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc f P Q φ comm F,
      Iso.inv_hom_id, comp_id]

/-- The left derived functors of an additive functor. -/
/-
**CategoryTheory.Functor.leftDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [CategoryTheory.HasProjectiveResolutions
 C] →             [inst_4 : CategoryTheory.Abelian D] →               (F : Categ
oryTheory.Functor C D) → [F.Additive] → ℕ → CategoryTheory.Functor C D
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The left derived functors of an additive functor.
-/
noncomputable def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedObj** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasProjectiveRe
solutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {
X : C} →                 (P : CategoryTheory.ProjectiveResolution X) →          
         (F : CategoryTheory.Functor C D) →                     [inst_5 : F.Addi
tive] →                       (n : ℕ) →                         (F.leftDerived n
).obj X ≅                           (HomologicalComplex.homologyFunctor D (Compl
exShape.down ℕ) n).obj                             ((F.mapHomologicalComplex (Co
mplexShape.down ℕ)).obj P.complex)
参数：P : CategoryTheory.ProjectiveResolution X；F : CategoryTheory.Functor C D；n : 
ℕ；F.leftDerived n；HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n；(
F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
We can compute a left derived functor using a chosen projective resolution.
-/
noncomputable def ProjectiveResolution.isoLeftDerivedObj {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).app _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {X Y : C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)
   (Q : CategoryTheory.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   Ca
tegoryTheory.CategoryStruct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStru
ct.comp (P.π.f 0) f →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additiv
e] (n : ℕ),       CategoryTheory.CategoryStruct.comp ((F.leftDerived n).map f) (
Q.isoLeftDerivedObj F n).hom =         CategoryTheory.CategoryStruct.comp (P.iso
LeftDerivedObj F n).hom           (((F.mapHomologicalComplex (ComplexShape.down 
ℕ)).comp                 (HomologicalComplex.homologyFunctor D (ComplexShape.dow
n ℕ) n)).map             φ)
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；F : CategoryThe
ory.Functor C D；n : ℕ；(F.leftDerived n).map f；Q.isoLeftDerivedObj F n；P.isoLeftD
erivedObj F n；((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp             
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n)).map         
    φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_
hom_naturality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Ty
pe u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.leftDerived n).map f ≫ (Q.isoLeftDerivedObj F n).hom =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoLeftDerivedObj, Functor.leftDerived]
  rw [assoc, ← Functor.map_comp_assoc,
    ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F,
    Functor.map_comp, assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality]
  rfl

@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_inv_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {X Y : C} (f : X ⟶ Y) (P : CategoryTheory.ProjectiveResolution X)
   (Q : CategoryTheory.ProjectiveResolution Y) (φ : P.complex ⟶ Q.complex),   Ca
tegoryTheory.CategoryStruct.comp (φ.f 0) (Q.π.f 0) = CategoryTheory.CategoryStru
ct.comp (P.π.f 0) f →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additiv
e] (n : ℕ),       CategoryTheory.CategoryStruct.comp (P.isoLeftDerivedObj F n).i
nv ((F.leftDerived n).map f) =         CategoryTheory.CategoryStruct.comp       
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp                 (Homo
logicalComplex.homologyFunctor D (ComplexShape.down ℕ) n)).map             φ)   
        (Q.isoLeftDerivedObj F n).inv
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；F : CategoryThe
ory.Functor C D；n : ℕ；P.isoLeftDerivedObj F n；(F.leftDerived n).map f；((F.mapHom
ologicalComplex (ComplexShape.down ℕ)).comp                 (HomologicalComplex.
homologyFunctor D (ComplexShape.down ℕ) n)).map             φ；Q.isoLeftDerivedOb
j F n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : 
CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom, assoc, assoc,
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ comm F n,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

/-- The higher derived functors vanish on projective objects. -/
/-
**CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ) (X
 : C)   [CategoryTheory.Projective X], CategoryTheory.Limits.IsZero ((F.leftDeri
ved (n + 1)).obj X)
参数：F : CategoryTheory.Functor C D；n : ℕ；X : C；(F.leftDerived (n + 1)).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
The higher derived functors vanish on projective objects.
-/
lemma Functor.isZero_leftDerived_obj_projective_succ
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Projective X] :
    IsZero ((F.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

set_option backward.isDefEq.respectTransparency false in
/-- We can compute a left derived functor on a morphism using a descent of that morphism
to a chain map between chosen projective resolutions.
-/
/-
**CategoryTheory.Functor.leftDerived_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ) {X
 Y : C}   (f : X ⟶ Y) {P : CategoryTheory.ProjectiveResolution X} {Q : CategoryT
heory.ProjectiveResolution Y}   (g : P.complex ⟶ Q.complex),   CategoryTheory.Ca
tegoryStruct.comp g Q.π = CategoryTheory.CategoryStruct.comp P.π ((ChainComplex.
single₀ C).map f) →     (F.leftDerived n).map f =       CategoryTheory.CategoryS
truct.comp (P.isoLeftDerivedObj F n).hom         (CategoryTheory.CategoryStruct.
comp           (((F.mapHomologicalComplex (ComplexShape.down ℕ)).comp           
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n)).map       
      g)           (Q.isoLeftDerivedObj F n).inv)
参数：F : CategoryTheory.Functor C D；n : ℕ；f : X ⟶ Y；g : P.complex ⟶ Q.complex；(Cha
inComplex.single₀ C).map f；F.leftDerived n；P.isoLeftDerivedObj F n；CategoryTheor
y.CategoryStruct.comp           (((F.mapHomologicalComplex (ComplexShape.down ℕ)
).comp                 (HomologicalComplex.homologyFunctor D (ComplexShape.down 
ℕ) n)).map             g)           (Q.isoLeftDerivedObj F n).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : 
CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用引理 `ChainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶ B
) : ((single₀ V).map f).f 0 = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
We can compute a left derived functor on a morphism using a descent of that morp
hism
to a chain map between chosen projective resolutions.
-/
theorem Functor.leftDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {P : ProjectiveResolution X} {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex)
    (w : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom,
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q g _ F n,
    assoc, assoc, Iso.inv_hom_id, comp_id]
  rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero]

/-- The natural transformation
`F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory` induced by
a natural transformation `F ⟶ G` between additive functors. -/
/-
**CategoryTheory.NatTrans.leftDerivedToHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasProjectiveRe
solutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {
F G : CategoryTheory.Functor C D} →                 [inst_5 : F.Additive] →     
              [inst_6 : G.Additive] → (F ⟶ G) → (F.leftDerivedToHomotopyCategory
 ⟶ G.leftDerivedToHomotopyCategory)
参数：F ⟶ G；F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The natural transformation
`F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory` induced by
a natural transformation `F ⟶ G` between additive functors.
-/
noncomputable def NatTrans.leftDerivedToHomotopyCategory
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory :=
  Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down ℕ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {F G : CategoryTheory.Functor C D} [inst_5 : F.Additive] [inst_6 
: G.Additive]   (α : F ⟶ G) {X : C} (P : CategoryTheory.ProjectiveResolution X),
   (CategoryTheory.NatTrans.leftDerivedToHomotopyCategory α).app X =     Categor
yTheory.CategoryStruct.comp (P.isoLeftDerivedToHomotopyCategoryObj F).hom       
(CategoryTheory.CategoryStruct.comp         ((HomotopyCategory.quotient D (Compl
exShape.down ℕ)).map           ((CategoryTheory.NatTrans.mapHomologicalComplex α
 (ComplexShape.down ℕ)).app P.complex))         (P.isoLeftDerivedToHomotopyCateg
oryObj G).inv)
参数：α : F ⟶ G；P : CategoryTheory.ProjectiveResolution X；CategoryTheory.NatTrans.l
eftDerivedToHomotopyCategory α；P.isoLeftDerivedToHomotopyCategoryObj F；CategoryT
heory.CategoryStruct.comp         ((HomotopyCategory.quotient D (ComplexShape.do
wn ℕ)).map           ((CategoryTheory.NatTrans.mapHomologicalComplex α (ComplexS
hape.down ℕ)).app P.complex))         (P.isoLeftDerivedToHomotopyCategoryObj G).
inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.mapHomologicalComplex_naturality`：∀ {ι : Type u_
1} {W₁ : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁
]   [inst_1 : CategoryTheory.Category.{v_3, u_…
-/
lemma ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    (NatTrans.leftDerivedToHomotopyCategory α).app X =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
          (P.isoLeftDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom, assoc, assoc,
      Iso.inv_hom_id, comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.leftDerivedToHomotopyCategory_id** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive],   Categor
yTheory.NatTrans.leftDerivedToHomotopyCategory (CategoryTheory.CategoryStruct.id
 F) =     CategoryTheory.CategoryStruct.id F.leftDerivedToHomotopyCategory
参数：F : CategoryTheory.Functor C D；CategoryTheory.CategoryStruct.id F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma NatTrans.leftDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.NatTrans.leftDerivedToHomotopyCategory_comp** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {F G H : CategoryTheory.Functor C D} (α : F ⟶ G) (β : G ⟶ H) [ins
t_5 : F.Additive]   [inst_6 : G.Additive] [inst_7 : H.Additive],   CategoryTheor
y.NatTrans.leftDerivedToHomotopyCategory (CategoryTheory.CategoryStruct.comp α β
) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.leftDerivedT
oHomotopyCategory α)       (CategoryTheory.NatTrans.leftDerivedToHomotopyCategor
y β)
参数：α : F ⟶ G；β : G ⟶ H；CategoryTheory.CategoryStruct.comp α β；CategoryTheory.Nat
Trans.leftDerivedToHomotopyCategory α；CategoryTheory.NatTrans.leftDerivedToHomot
opyCategory β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma NatTrans.leftDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.leftDerivedToHomotopyCategory α ≫
        NatTrans.leftDerivedToHomotopyCategory β := rfl

/-- The natural transformation between left-derived functors induced by a natural transformation. -/
/-
**CategoryTheory.NatTrans.leftDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasProjectiveRe
solutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {
F G : CategoryTheory.Functor C D} →                 [inst_5 : F.Additive] → [ins
t_6 : G.Additive] → (F ⟶ G) → (n : ℕ) → F.leftDerived n ⟶ G.leftDerived n
参数：F ⟶ G；n : ℕ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural transformation between left-derived functors induced by a natural tr
ansformation.
-/
noncomputable def NatTrans.leftDerived
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.leftDerived n ⟶ G.leftDerived n :=
  Functor.whiskerRight (NatTrans.leftDerivedToHomotopyCategory α) _

@[simp]
/-
**CategoryTheory.NatTrans.leftDerived_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ),  
 CategoryTheory.NatTrans.leftDerived (CategoryTheory.CategoryStruct.id F) n =   
  CategoryTheory.CategoryStruct.id (F.leftDerived n)
参数：F : CategoryTheory.Functor C D；n : ℕ；CategoryTheory.CategoryStruct.id F；F.lef
tDerived n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
-/
theorem NatTrans.leftDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.leftDerived (𝟙 F) n = 𝟙 (F.leftDerived n) := by
  dsimp only [leftDerived]
  simp only [leftDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**CategoryTheory.NatTrans.leftDerived_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {F G H : CategoryTheory.Functor C D} [inst_5 : F.Additive] [inst_
6 : G.Additive]   [inst_7 : H.Additive] (α : F ⟶ G) (β : G ⟶ H) (n : ℕ),   Categ
oryTheory.NatTrans.leftDerived (CategoryTheory.CategoryStruct.comp α β) n =     
CategoryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.leftDerived α n)    
   (CategoryTheory.NatTrans.leftDerived β n)
参数：α : F ⟶ G；β : G ⟶ H；n : ℕ；CategoryTheory.CategoryStruct.comp α β；CategoryTheo
ry.NatTrans.leftDerived α n；CategoryTheory.NatTrans.leftDerived β n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem NatTrans.leftDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.leftDerived (α ≫ β) n = NatTrans.leftDerived α n ≫ NatTrans.leftDerived β n := by
  simp [NatTrans.leftDerived]

namespace ProjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution. -/
/-
**CategoryTheory.ProjectiveResolution.leftDerived_app_eq** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：leftDerived_app_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X 
: C} (P : ProjectiveResolution X) (n : Nat) : (NatTrans.leftDerived α n).app X =
 (P.isoLeftDerivedObj F n).hom ≫ (HomologicalComplex.homologyFunctor D (ComplexS
hape.down Nat) n).map ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫ (P.
isoLeftDerivedObj G n).inv
参数：α : F ⟶ G；P : ProjectiveResolution X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_
1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A component of the natural transformation between left-derived functors can be c
omputed
using a chosen projective resolution.
-/
lemma leftDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X)
    (n : ℕ) : (NatTrans.leftDerived α n).app X =
      (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
        (P.isoLeftDerivedObj G n).inv := by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P,
    Functor.map_comp, Functor.map_comp, assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P : ProjectiveResolution X` and `F` is an additive functor, this is
the canonical morphism from the opcycles in degree `0` of
`(F.mapHomologicalComplex _).obj P.complex` to `F.obj X`. -/
/-
**CategoryTheory.ProjectiveResolution.fromLeftDerivedZero'** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：fromLeftDerivedZero' {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.A
dditive] : ((F.mapHomologicalComplex _).obj P.complex).opcycles 0 ⟶ F.obj X
参数：P : ProjectiveResolution X；F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `P : ProjectiveResolution X` and `F` is an additive functor, this is
the canonical morphism from the opcycles in degree `0` of
`(F.mapHomologicalComplex _).obj P.complex` to `F.obj X`.
-/
noncomputable def fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj P.complex).opcycles 0 ⟶ F.obj X :=
  HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp, complex_d_comp_π_f_zero, F.map_zero])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：pOpcycles_comp_fromLeftDerivedZero' {C} [Category* C] [Abelian C] {X : C} 
(P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] : HomologicalComplex.pOpcy
cles _ _ ≫ P.fromLeftDerivedZero' F = F.map (P.π.f 0)
参数：P : ProjectiveResolution X；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.p_descOpcycles`：p_descOpcycles {A : C} (k : K.X i ⟶ A
) (j : ι) (hj : c.prev i = j) (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpc
ycles k j hj hk = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pOpcycles_comp_fromLeftDerivedZero' {C} [Category* C] [Abelian C] {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.pOpcycles _ _ ≫ P.fromLeftDerivedZero' F = F.map (P.π.f 0) := by
  simp [fromLeftDerivedZero']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.ProjectiveResolution.fromLeftDerivedZero'_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : C
ategoryTheory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory.Category.{v_2
, u_2} C] [inst_3 : CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)   (P : Categ
oryTheory.ProjectiveResolution X) (Q : CategoryTheory.ProjectiveResolution Y) (φ
 : P.complex ⟶ Q.complex),   CategoryTheory.CategoryStruct.comp (φ.f 0) (Q.π.f 0
) = CategoryTheory.CategoryStruct.comp (P.π.f 0) f →     ∀ (F : CategoryTheory.F
unctor C D) [inst_4 : F.Additive],       CategoryTheory.CategoryStruct.comp     
      (HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex (ComplexShape.do
wn ℕ)).map φ) 0)           (Q.fromLeftDerivedZero' F) =         CategoryTheory.C
ategoryStruct.comp (P.fromLeftDerivedZero' F) (F.map f)
参数：f : X ⟶ Y；P : CategoryTheory.ProjectiveResolution X；Q : CategoryTheory.Projec
tiveResolution Y；φ : P.complex ⟶ Q.complex；φ.f 0；Q.π.f 0；P.π.f 0；F : CategoryThe
ory.Functor C D；HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex (Comple
xShape.down ℕ)).map φ) 0；Q.fromLeftDerivedZero' F；P.fromLeftDerivedZero' F；F.map
 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
· 使用引理 `CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'`
：pOpcycles_comp_fromLeftDerivedZero' {C} [Category* C] [Abelian C] {X : C} (P : 
ProjectiveResolution X) (F : C ⥤ D) [F.Additive] : Homologica…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_
assoc`：∀ {D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : 
CategoryTheory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromLeftDerivedZero'_naturality {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex _).map φ) 0 ≫
        Q.fromLeftDerivedZero' F = P.fromLeftDerivedZero' F ≫ F.map f := by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← F.map_comp, comm,
    HomologicalComplex.p_opcyclesMap_assoc, Functor.mapHomologicalComplex_map_f,
    pOpcycles_comp_fromLeftDerivedZero', pOpcycles_comp_fromLeftDerivedZero'_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso ((ProjectiveResolution.self X).fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff]
  refine ⟨ShortComplex.Splitting.exact ?_, inferInstance⟩
  exact
    { r := 0
      s := 𝟙 _
      f_r := (F.map_isZero (isZero_zero _)).eq_of_src _ _ }

end ProjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F.leftDerived 0 ⟶ F`. -/
/-
**CategoryTheory.Functor.fromLeftDerivedZero** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasProjectiveRe
solutions C] →             [inst_4 : CategoryTheory.Abelian D] →               (
F : CategoryTheory.Functor C D) → [inst_5 : F.Additive] → F.leftDerived 0 ⟶ F
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural transformation `F.leftDerived 0 ⟶ F`.
-/
noncomputable def Functor.fromLeftDerivedZero (F : C ⥤ D) [F.Additive] :
    F.leftDerived 0 ⟶ F where
  app X := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down ℕ) 0).hom.app _ ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫ (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    dsimp [leftDerived]
    rw [assoc, assoc, ← ProjectiveResolution.fromLeftDerivedZero'_naturality f
      (projectiveResolution X) (projectiveResolution Y)
      (ProjectiveResolution.lift f _ _) (by simp),
      ← HomologicalComplex.homologyι_naturality_assoc]
    erw [← NatTrans.naturality_assoc]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasProjectiveResolutions C]   [inst_4 : CategoryThe
ory.Abelian D] {X : C} (P : CategoryTheory.ProjectiveResolution X)   (F : Catego
ryTheory.Functor C D) [inst_5 : F.Additive],   F.fromLeftDerivedZero.app X =    
 CategoryTheory.CategoryStruct.comp (P.isoLeftDerivedObj F 0).hom       (Categor
yTheory.CategoryStruct.comp         (ChainComplex.isoHomologyι₀ ((F.mapHomologic
alComplex (ComplexShape.down ℕ)).obj P.complex)).hom         (P.fromLeftDerivedZ
ero' F))
参数：P : CategoryTheory.ProjectiveResolution X；F : CategoryTheory.Functor C D；P.is
oLeftDerivedObj F 0；CategoryTheory.CategoryStruct.comp         (ChainComplex.iso
Homologyι₀ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom 
        (P.fromLeftDerivedZero' F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.HasProjectiveResolutions.out`：∀ {C : Type u} {inst : Cate
goryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroObject C}  
 {inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.ProjectiveResolution.fromLeftDerivedZero'_naturality`：∀ {
D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : CategoryTh
eory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ProjectiveResolution.lift_commutes_zero`：lift_commutes_ze
ro {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution 
Z) : (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `HomologicalComplex.homologyι_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma ProjectiveResolution.fromLeftDerivedZero_eq
    {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.fromLeftDerivedZero.app X = (P.isoLeftDerivedObj F 0).hom ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫
        P.fromLeftDerivedZero' F := by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ := ProjectiveResolution.fromLeftDerivedZero'_naturality
    (𝟙 X) P (projectiveResolution X) (lift (𝟙 X) _ _) (by simp) F
  have h₂ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (lift (𝟙 X) _ _) :=
      id_comp _
  simp only [Functor.map_id, comp_id] at h₁
  rw [assoc, ← cancel_epi ((HomotopyCategory.homologyFunctor _ _ 0).map
      (P.isoLeftDerivedToHomotopyCategoryObj F).inv), ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Functor.map_id, id_comp, ← h₁, h₂,
      ← HomologicalComplex.homologyι_naturality_assoc]
  erw [← NatTrans.naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso (F.fromLeftDerivedZero.app X) := by
  rw [(ProjectiveResolution.self X).fromLeftDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (P : ProjectiveResolution X) :
    IsIso (P.fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff, ShortComplex.exact_and_epi_g_iff_g_is_cokernel]
  exact ⟨CokernelCofork.mapIsColimit _ (P.isColimitCokernelCofork) F⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : IsIso (F.fromLeftDerivedZero.app X) := by
  dsimp [Functor.fromLeftDerivedZero]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso F.fromLeftDerivedZero :=
  NatIso.isIso_of_isIso_app _

namespace Functor

/-- The canonical isomorphism `F.leftDerived 0 ≅ F` when `F` is right exact
(i.e. preserves finite colimits). -/
@[simps! hom]
/-
**CategoryTheory.Functor.leftDerivedZeroIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instIsIsoFunctorFromLeftDerivedZero`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Cat
egory.{v_1, u_1} D]   [inst_2 : Category…

--- 原说明 ---
The canonical isomorphism `F.leftDerived 0 ≅ F` when `F` is right exact
(i.e. preserves finite colimits).
-/
noncomputable def leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F :=
  (asIso F.fromLeftDerivedZero)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedZeroIsoSelf_hom_inv_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：leftDerivedZeroIsoSelf_hom_inv_id : F.fromLeftDerivedZero ≫ F.leftDerivedZ
eroIsoSelf.inv = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma leftDerivedZeroIsoSelf_hom_inv_id :
    F.fromLeftDerivedZero ≫ F.leftDerivedZeroIsoSelf.inv = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedZeroIsoSelf_inv_hom_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：leftDerivedZeroIsoSelf_inv_hom_id : F.leftDerivedZeroIsoSelf.inv ≫ F.fromL
eftDerivedZero = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma leftDerivedZeroIsoSelf_inv_hom_id :
    F.leftDerivedZeroIsoSelf.inv ≫ F.fromLeftDerivedZero = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedZeroIsoSelf_hom_inv_id_app** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftDerivedZeroIsoSelf_hom_inv_id_app (X : C) : F.fromLeftDerivedZero.app 
X ≫ F.leftDerivedZeroIsoSelf.inv.app X = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma leftDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.fromLeftDerivedZero.app X ≫ F.leftDerivedZeroIsoSelf.inv.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.leftDerivedZeroIsoSelf_inv_hom_id_app** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：leftDerivedZeroIsoSelf_inv_hom_id_app (X : C) : F.leftDerivedZeroIsoSelf.i
nv.app X ≫ F.fromLeftDerivedZero.app X = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma leftDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.leftDerivedZeroIsoSelf.inv.app X ≫ F.fromLeftDerivedZero.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id_app X

end Functor

end

end CategoryTheory

