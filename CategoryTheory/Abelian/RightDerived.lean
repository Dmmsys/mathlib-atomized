/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Right-derived functors

We define the right-derived functors `F.rightDerived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

We first define a functor
`F.rightDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.up ℕ)` which is
`injectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`I : InjectiveResolution X`, then `F.rightDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `I.cocomplex`
(this isomorphism is `I.isoRightDerivedToHomotopyCategoryObj F`).

Then, the right-derived functors `F.rightDerived n : C ⥤ D` are obtained by composing
`F.rightDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_rightDerived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `NatTrans.rightDerived`: the natural transformation between right derived functors
  induced by a natural transformation.
* `Functor.toRightDerivedZero`: the natural transformation `F ⟶ F.rightDerived 0`,
  which is an isomorphism when `F` is left exact (i.e. preserves finite limits),
  see also `Functor.rightDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a right derived functor
  `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`,
  and `F.rightDerived` shall be redefined using `F.rightDerivedFunctorPlus`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- When `F : C ⥤ D` is an additive functor, this is
the functor `C ⥤ HomotopyCategory D (ComplexShape.up ℕ)` which
sends `X : C` to `F` applied to an injective resolution of `X`. -/
/-
**CategoryTheory.Functor.rightDerivedToHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [CategoryTheory.HasInjectiveResolutions 
C] →             [inst_4 : CategoryTheory.Abelian D] →               (F : Catego
ryTheory.Functor C D) →                 [F.Additive] → CategoryTheory.Functor C 
(HomotopyCategory D (ComplexShape.up ℕ))
参数：F : CategoryTheory.Functor C D；HomotopyCategory D (ComplexShape.up ℕ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
When `F : C ⥤ D` is an additive functor, this is
the functor `C ⥤ HomotopyCategory D (ComplexShape.up ℕ)` which
sends `X : C` to `F` applied to an injective resolution of `X`.
-/
noncomputable def Functor.rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.up ℕ) :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _

/-- If `I : InjectiveResolution Z` and `F : C ⥤ D` is an additive functor, this is
an isomorphism between `F.rightDerivedToHomotopyCategory.obj X` and the complex
obtained by applying `F` to `I.cocomplex`. -/
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasInjectiveRes
olutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {X
 : C} →                 (I : CategoryTheory.InjectiveResolution X) →            
       (F : CategoryTheory.Functor C D) →                     [inst_5 : F.Additi
ve] →                       F.rightDerivedToHomotopyCategory.obj X ≅            
             ((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp                
               (HomotopyCategory.quotient D (ComplexShape.up ℕ))).obj           
                I.cocomplex
参数：I : CategoryTheory.InjectiveResolution X；F : CategoryTheory.Functor C D；(F.ma
pHomologicalComplex (ComplexShape.up ℕ)).comp                               (Hom
otopyCategory.quotient D (ComplexShape.up ℕ))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `I : InjectiveResolution Z` and `F : C ⥤ D` is an additive functor, this is
an isomorphism between `F.rightDerivedToHomotopyCategory.obj X` and the complex
obtained by applying `F` to `I.cocomplex`.
-/
noncomputable def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj {X : C}
    (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj I.cocomplex :=
  (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_na
turality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {X Y : C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)  
 (J : CategoryTheory.InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   C
ategoryTheory.CategoryStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStr
uct.comp f (J.ι.f 0) →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additi
ve],       CategoryTheory.CategoryStruct.comp (F.rightDerivedToHomotopyCategory.
map f)           (J.isoRightDerivedToHomotopyCategoryObj F).hom =         Catego
ryTheory.CategoryStruct.comp (I.isoRightDerivedToHomotopyCategoryObj F).hom     
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp (HomotopyCategory.quo
tient D (ComplexShape.up ℕ))).map φ)
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；F : CategoryT
heory.Functor C D；F.rightDerivedToHomotopyCategory.map f；J.isoRightDerivedToHomo
topyCategoryObj F；I.isoRightDerivedToHomotopyCategoryObj F；((F.mapHomologicalCom
plex (ComplexShape.up ℕ)).comp (HomotopyCategory.quotient D (ComplexShape.up ℕ))
).map φ。
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
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.InjectiveResolution.iso_hom_naturality`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [i
nst_2 : CategoryTheory.HasInjectiveResoluti…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.map f ≫ (J.isoRightDerivedToHomotopyCategoryObj F).hom =
      (I.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
  dsimp [Functor.rightDerivedToHomotopyCategory, isoRightDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc, iso_hom_naturality f I J φ comm, Functor.map_comp,
    assoc, assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).hom.naturality]
  rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_na
turality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {X Y : C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)  
 (J : CategoryTheory.InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   C
ategoryTheory.CategoryStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStr
uct.comp f (J.ι.f 0) →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additi
ve],       CategoryTheory.CategoryStruct.comp (I.isoRightDerivedToHomotopyCatego
ryObj F).inv           (F.rightDerivedToHomotopyCategory.map f) =         Catego
ryTheory.CategoryStruct.comp           (((F.mapHomologicalComplex (ComplexShape.
up ℕ)).comp (HomotopyCategory.quotient D (ComplexShape.up ℕ))).map φ)           
(J.isoRightDerivedToHomotopyCategoryObj F).inv
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；F : CategoryT
heory.Functor C D；I.isoRightDerivedToHomotopyCategoryObj F；F.rightDerivedToHomot
opyCategory.map f；((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp (HomotopyC
ategory.quotient D (ComplexShape.up ℕ))).map φ；J.isoRightDerivedToHomotopyCatego
ryObj F。
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
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_
hom_naturality_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {
D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Catego
ry…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    (I.isoRightDerivedToHomotopyCategoryObj F).inv ≫ F.rightDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (J.isoRightDerivedToHomotopyCategoryObj F).inv := by
    rw [← cancel_epi (I.isoRightDerivedToHomotopyCategoryObj F).hom, Iso.hom_inv_id_assoc]
    dsimp
    rw [← isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc f I J φ comm F,
      Iso.hom_inv_id, comp_id]

/-- The right derived functors of an additive functor. -/
/-
**CategoryTheory.Functor.rightDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [CategoryTheory.HasInjectiveResolutions 
C] →             [inst_4 : CategoryTheory.Abelian D] →               (F : Catego
ryTheory.Functor C D) → [F.Additive] → ℕ → CategoryTheory.Functor C D
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The right derived functors of an additive functor.
-/
noncomputable def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

/-- We can compute a right derived functor using a chosen injective resolution. -/
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedObj** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.InjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasInjectiveRes
olutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {X
 : C} →                 (I : CategoryTheory.InjectiveResolution X) →            
       (F : CategoryTheory.Functor C D) →                     [inst_5 : F.Additi
ve] →                       (n : ℕ) →                         (F.rightDerived n)
.obj X ≅                           (HomologicalComplex.homologyFunctor D (Comple
xShape.up ℕ) n).obj                             ((F.mapHomologicalComplex (Compl
exShape.up ℕ)).obj I.cocomplex)
参数：I : CategoryTheory.InjectiveResolution X；F : CategoryTheory.Functor C D；n : ℕ
；F.rightDerived n；HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n；(F.
mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
We can compute a right derived functor using a chosen injective resolution.
-/
noncomputable def InjectiveResolution.isoRightDerivedObj {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
    (I.isoRightDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {X Y : C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)  
 (J : CategoryTheory.InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   C
ategoryTheory.CategoryStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStr
uct.comp f (J.ι.f 0) →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additi
ve] (n : ℕ),       CategoryTheory.CategoryStruct.comp ((F.rightDerived n).map f)
 (J.isoRightDerivedObj F n).hom =         CategoryTheory.CategoryStruct.comp (I.
isoRightDerivedObj F n).hom           (((F.mapHomologicalComplex (ComplexShape.u
p ℕ)).comp                 (HomologicalComplex.homologyFunctor D (ComplexShape.u
p ℕ) n)).map             φ)
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；F : CategoryT
heory.Functor C D；n : ℕ；(F.rightDerived n).map f；J.isoRightDerivedObj F n；I.isoR
ightDerivedObj F n；((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp          
       (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n)).map        
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
· 使用定理 `CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_
hom_naturality`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Ty
pe u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma InjectiveResolution.isoRightDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoRightDerivedObj, Functor.rightDerived]
  rw [assoc, ← Functor.map_comp_assoc,
    InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f I J φ comm F,
    Functor.map_comp, assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.naturality]
  rfl

@[reassoc]
/-
**CategoryTheory.InjectiveResolution.isoRightDerivedObj_inv_naturality** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {X Y : C} (f : X ⟶ Y) (I : CategoryTheory.InjectiveResolution X)  
 (J : CategoryTheory.InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex),   C
ategoryTheory.CategoryStruct.comp (I.ι.f 0) (φ.f 0) = CategoryTheory.CategoryStr
uct.comp f (J.ι.f 0) →     ∀ (F : CategoryTheory.Functor C D) [inst_5 : F.Additi
ve] (n : ℕ),       CategoryTheory.CategoryStruct.comp (I.isoRightDerivedObj F n)
.inv ((F.rightDerived n).map f) =         CategoryTheory.CategoryStruct.comp    
       (((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp                 (Hom
ologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n)).map             φ)    
       (J.isoRightDerivedObj F n).inv
参数：f : X ⟶ Y；I : CategoryTheory.InjectiveResolution X；J : CategoryTheory.Injecti
veResolution Y；φ : I.cocomplex ⟶ J.cocomplex；I.ι.f 0；φ.f 0；J.ι.f 0；F : CategoryT
heory.Functor C D；n : ℕ；I.isoRightDerivedObj F n；(F.rightDerived n).map f；((F.ma
pHomologicalComplex (ComplexShape.up ℕ)).comp                 (HomologicalComple
x.homologyFunctor D (ComplexShape.up ℕ) n)).map             φ；J.isoRightDerivedO
bj F n。
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
· 使用定理 `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality`：∀ 
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
lemma InjectiveResolution.isoRightDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (J.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom, assoc, assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

/-- The higher derived functors vanish on injective objects. -/
/-
**CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ) (X 
: C)   [CategoryTheory.Injective X], CategoryTheory.Limits.IsZero ((F.rightDeriv
ed (n + 1)).obj X)
参数：F : CategoryTheory.Functor C D；n : ℕ；X : C；(F.rightDerived (n + 1)).obj X。
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
The higher derived functors vanish on injective objects.
-/
lemma Functor.isZero_rightDerived_obj_injective_succ
    (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    IsZero ((F.rightDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((InjectiveResolution.self X).isoRightDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

set_option backward.isDefEq.respectTransparency false in
/-- We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
/-
**CategoryTheory.Functor.rightDerived_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ) {X 
Y : C}   (f : X ⟶ Y) {P : CategoryTheory.InjectiveResolution X} {Q : CategoryThe
ory.InjectiveResolution Y}   (g : P.cocomplex ⟶ Q.cocomplex),   CategoryTheory.C
ategoryStruct.comp P.ι g = CategoryTheory.CategoryStruct.comp ((CochainComplex.s
ingle₀ C).map f) Q.ι →     (F.rightDerived n).map f =       CategoryTheory.Categ
oryStruct.comp (P.isoRightDerivedObj F n).hom         (CategoryTheory.CategorySt
ruct.comp           (((F.mapHomologicalComplex (ComplexShape.up ℕ)).comp        
         (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n)).map      
       g)           (Q.isoRightDerivedObj F n).inv)
参数：F : CategoryTheory.Functor C D；n : ℕ；f : X ⟶ Y；g : P.cocomplex ⟶ Q.cocomplex；
(CochainComplex.single₀ C).map f；F.rightDerived n；P.isoRightDerivedObj F n；Categ
oryTheory.CategoryStruct.comp           (((F.mapHomologicalComplex (ComplexShape
.up ℕ)).comp                 (HomologicalComplex.homologyFunctor D (ComplexShape
.up ℕ) n)).map             g)           (Q.isoRightDerivedObj F n).inv。
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
· 使用定理 `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : 
CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : Category…
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用引理 `CochainComplex.single₀_map_f_zero`：single₀_map_f_zero {A B : V} (f : A ⟶
 B) : ((single₀ V).map f).f 0 = f
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
We can compute a right derived functor on a morphism using a descent of that mor
phism
to a cochain map between chosen injective resolutions.
-/
theorem Functor.rightDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : X ⟶ Y)
    {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : P.cocomplex ⟶ Q.cocomplex)
    (w : P.ι ≫ g = (CochainComplex.single₀ C).map f ≫ Q.ι) :
    (F.rightDerived n).map f =
      (P.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoRightDerivedObj F n).hom,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q g _ F n,
    assoc, assoc, Iso.inv_hom_id, comp_id]
  rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero]

/-- The natural transformation
`F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory` induced by
a natural transformation `F ⟶ G` between additive functors. -/
/-
**CategoryTheory.NatTrans.rightDerivedToHomotopyCategory** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasInjectiveRes
olutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {F
 G : CategoryTheory.Functor C D} →                 [inst_5 : F.Additive] →      
             [inst_6 : G.Additive] →                     (F ⟶ G) → (F.rightDeriv
edToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory)
参数：F ⟶ G；F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
The natural transformation
`F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory` induced by
a natural transformation `F ⟶ G` between additive functors.
-/
noncomputable def NatTrans.rightDerivedToHomotopyCategory
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory :=
  Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.up ℕ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.rightDerivedToHomotopyCategory_app_eq** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {F G : CategoryTheory.Functor C D} [inst_5 : F.Additive] [inst_6 :
 G.Additive]   (α : F ⟶ G) {X : C} (P : CategoryTheory.InjectiveResolution X),  
 (CategoryTheory.NatTrans.rightDerivedToHomotopyCategory α).app X =     Category
Theory.CategoryStruct.comp (P.isoRightDerivedToHomotopyCategoryObj F).hom       
(CategoryTheory.CategoryStruct.comp         ((HomotopyCategory.quotient D (Compl
exShape.up ℕ)).map           ((CategoryTheory.NatTrans.mapHomologicalComplex α (
ComplexShape.up ℕ)).app P.cocomplex))         (P.isoRightDerivedToHomotopyCatego
ryObj G).inv)
参数：α : F ⟶ G；P : CategoryTheory.InjectiveResolution X；CategoryTheory.NatTrans.ri
ghtDerivedToHomotopyCategory α；P.isoRightDerivedToHomotopyCategoryObj F；Category
Theory.CategoryStruct.comp         ((HomotopyCategory.quotient D (ComplexShape.u
p ℕ)).map           ((CategoryTheory.NatTrans.mapHomologicalComplex α (ComplexSh
ape.up ℕ)).app P.cocomplex))         (P.isoRightDerivedToHomotopyCategoryObj G).
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
lemma InjectiveResolution.rightDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X) :
    (NatTrans.rightDerivedToHomotopyCategory α).app X =
      (P.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (P.isoRightDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoRightDerivedToHomotopyCategoryObj G).hom, assoc, assoc,
      Iso.inv_hom_id, comp_id]
  dsimp [isoRightDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.rightDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.rightDerivedToHomotopyCategory_id** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive],   Category
Theory.NatTrans.rightDerivedToHomotopyCategory (CategoryTheory.CategoryStruct.id
 F) =     CategoryTheory.CategoryStruct.id F.rightDerivedToHomotopyCategory
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
lemma NatTrans.rightDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.NatTrans.rightDerivedToHomotopyCategory_comp** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {F G H : CategoryTheory.Functor C D} (α : F ⟶ G) (β : G ⟶ H) [inst
_5 : F.Additive]   [inst_6 : G.Additive] [inst_7 : H.Additive],   CategoryTheory
.NatTrans.rightDerivedToHomotopyCategory (CategoryTheory.CategoryStruct.comp α β
) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.rightDerived
ToHomotopyCategory α)       (CategoryTheory.NatTrans.rightDerivedToHomotopyCateg
ory β)
参数：α : F ⟶ G；β : G ⟶ H；CategoryTheory.CategoryStruct.comp α β；CategoryTheory.Nat
Trans.rightDerivedToHomotopyCategory α；CategoryTheory.NatTrans.rightDerivedToHom
otopyCategory β。
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
lemma NatTrans.rightDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.rightDerivedToHomotopyCategory α ≫
        NatTrans.rightDerivedToHomotopyCategory β := rfl

/-- The natural transformation between right-derived functors
induced by a natural transformation. -/
/-
**CategoryTheory.NatTrans.rightDerived** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasInjectiveRes
olutions C] →             [inst_4 : CategoryTheory.Abelian D] →               {F
 G : CategoryTheory.Functor C D} →                 [inst_5 : F.Additive] → [inst
_6 : G.Additive] → (F ⟶ G) → (n : ℕ) → F.rightDerived n ⟶ G.rightDerived n
参数：F ⟶ G；n : ℕ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural transformation between right-derived functors
induced by a natural transformation.
-/
noncomputable def NatTrans.rightDerived
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.rightDerived n ⟶ G.rightDerived n :=
  Functor.whiskerRight (NatTrans.rightDerivedToHomotopyCategory α) _

@[simp]
/-
**CategoryTheory.NatTrans.rightDerived_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive] (n : ℕ),   
CategoryTheory.NatTrans.rightDerived (CategoryTheory.CategoryStruct.id F) n =   
  CategoryTheory.CategoryStruct.id (F.rightDerived n)
参数：F : CategoryTheory.Functor C D；n : ℕ；CategoryTheory.CategoryStruct.id F；F.rig
htDerived n。
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
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) := by
  dsimp only [rightDerived]
  simp only [rightDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**CategoryTheory.NatTrans.rightDerived_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.NatTrans`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {F G H : CategoryTheory.Functor C D} [inst_5 : F.Additive] [inst_6
 : G.Additive]   [inst_7 : H.Additive] (α : F ⟶ G) (β : G ⟶ H) (n : ℕ),   Catego
ryTheory.NatTrans.rightDerived (CategoryTheory.CategoryStruct.comp α β) n =     
CategoryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.rightDerived α n)   
    (CategoryTheory.NatTrans.rightDerived β n)
参数：α : F ⟶ G；β : G ⟶ H；n : ℕ；CategoryTheory.CategoryStruct.comp α β；CategoryTheo
ry.NatTrans.rightDerived α n；CategoryTheory.NatTrans.rightDerived β n。
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
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [NatTrans.rightDerived]

namespace InjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution. -/
/-
**CategoryTheory.InjectiveResolution.rightDerived_app_eq** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：rightDerived_app_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X
 : C} (P : InjectiveResolution X) (n : Nat) : (NatTrans.rightDerived α n).app X 
= (P.isoRightDerivedObj F n).hom ≫ (HomologicalComplex.homologyFunctor D (Comple
xShape.up Nat) n).map ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫ (
P.isoRightDerivedObj G n).inv
参数：α : F ⟶ G；P : InjectiveResolution X；n : Nat。
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
· 使用定理 `CategoryTheory.InjectiveResolution.rightDerivedToHomotopyCategory_app_eq
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
A component of the natural transformation between right-derived functors can be 
computed
using a chosen injective resolution.
-/
lemma rightDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X)
    (n : ℕ) : (NatTrans.rightDerived α n).app X =
      (P.isoRightDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
        (P.isoRightDerivedObj G n).inv := by
  dsimp [NatTrans.rightDerived, isoRightDerivedObj]
  rw [InjectiveResolution.rightDerivedToHomotopyCategory_app_eq α P,
    Functor.map_comp, Functor.map_comp, assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P : InjectiveResolution X` and `F` is an additive functor, this is
the canonical morphism from `F.obj X` to the cycles in degree `0` of
`(F.mapHomologicalComplex _).obj P.cocomplex`. -/
/-
**CategoryTheory.InjectiveResolution.toRightDerivedZero'** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：toRightDerivedZero' {X : C} (P : InjectiveResolution X) (F : C ⥤ D) [F.Add
itive] : F.obj X ⟶ ((F.mapHomologicalComplex _).obj P.cocomplex).cycles 0
参数：P : InjectiveResolution X；F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C

--- 原说明 ---
If `P : InjectiveResolution X` and `F` is an additive functor, this is
the canonical morphism from `F.obj X` to the cycles in degree `0` of
`(F.mapHomologicalComplex _).obj P.cocomplex`.
-/
noncomputable def toRightDerivedZero' {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.obj X ⟶ ((F.mapHomologicalComplex _).obj P.cocomplex).cycles 0 :=
  HomologicalComplex.liftCycles _ (F.map (P.ι.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp, HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d,
      zero_comp, F.map_zero])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : C
ategoryTheory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory.Category.{v_2
, u_2} C] [inst_3 : CategoryTheory.Abelian C] {X : C}   (P : CategoryTheory.Inje
ctiveResolution X) (F : CategoryTheory.Functor C D) [inst_4 : F.Additive],   Cat
egoryTheory.CategoryStruct.comp (P.toRightDerivedZero' F)       (((F.mapHomologi
calComplex (ComplexShape.up ℕ)).obj P.cocomplex).iCycles 0) =     F.map (P.ι.f 0
)
参数：P : CategoryTheory.InjectiveResolution X；F : CategoryTheory.Functor C D；P.toR
ightDerivedZero' F；((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomple
x).iCycles 0；P.ι.f 0。
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
· 使用引理 `HomologicalComplex.liftCycles_i`：liftCycles_i {A : C} (k : A ⟶ K.X i) (j
 : ι) (hj : c.next i = j) (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iC
ycles i = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toRightDerivedZero'_comp_iCycles {C} [Category* C] [Abelian C] {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    P.toRightDerivedZero' F ≫
      HomologicalComplex.iCycles _ _ = F.map (P.ι.f 0) := by
  simp [toRightDerivedZero']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.toRightDerivedZero'_naturality** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : C
ategoryTheory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory.Category.{v_2
, u_2} C] [inst_3 : CategoryTheory.Abelian C] {X Y : C} (f : X ⟶ Y)   (P : Categ
oryTheory.InjectiveResolution X) (Q : CategoryTheory.InjectiveResolution Y) (φ :
 P.cocomplex ⟶ Q.cocomplex),   CategoryTheory.CategoryStruct.comp (P.ι.f 0) (φ.f
 0) = CategoryTheory.CategoryStruct.comp f (Q.ι.f 0) →     ∀ (F : CategoryTheory
.Functor C D) [inst_4 : F.Additive],       CategoryTheory.CategoryStruct.comp (F
.map f) (Q.toRightDerivedZero' F) =         CategoryTheory.CategoryStruct.comp (
P.toRightDerivedZero' F)           (HomologicalComplex.cyclesMap ((F.mapHomologi
calComplex (ComplexShape.up ℕ)).map φ) 0)
参数：f : X ⟶ Y；P : CategoryTheory.InjectiveResolution X；Q : CategoryTheory.Injecti
veResolution Y；φ : P.cocomplex ⟶ Q.cocomplex；P.ι.f 0；φ.f 0；Q.ι.f 0；F : CategoryT
heory.Functor C D；F.map f；Q.toRightDerivedZero' F；P.toRightDerivedZero' F；Homolo
gicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0。
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
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.instMonoICycles`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {ι : Type u_2} {c : Com…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles`：∀ {
D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : CategoryTh
eory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `HomologicalComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ i ≫ L.iCycles 
i = K.iCycles i ≫ φ.f i
· 使用定理 `CategoryTheory.Functor.mapHomologicalComplex_map_f`：∀ {ι : Type u_1} {W₁
 : Type u_3} {W₂ : Type u_4} [inst : CategoryTheory.Category.{v_2, u_3} W₁]   [i
nst_1 : CategoryTheory.Category.{v_3, u_…
· 使用定理 `CategoryTheory.InjectiveResolution.toRightDerivedZero'_comp_iCycles_asso
c`：∀ {D : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : Cate
goryTheory.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toRightDerivedZero'_naturality {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y)
    (φ : P.cocomplex ⟶ Q.cocomplex) (comm : P.ι.f 0 ≫ φ.f 0 = f ≫ Q.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.map f ≫ Q.toRightDerivedZero' F =
      P.toRightDerivedZero' F ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map φ) 0 := by
  simp only [← cancel_mono (HomologicalComplex.iCycles _ _), assoc,
    toRightDerivedZero'_comp_iCycles,
    CochainComplex.single₀_obj_zero, HomologicalComplex.cyclesMap_i,
    Functor.mapHomologicalComplex_map_f, toRightDerivedZero'_comp_iCycles_assoc,
    ← F.map_comp, comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso ((InjectiveResolution.self X).toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  rw [CochainComplex.isIso_liftCycles_iff]
  refine ⟨ShortComplex.Splitting.exact ?_, inferInstance⟩
  exact
    { r := 𝟙 _
      s := 0
      s_g := (F.map_isZero (isZero_zero _)).eq_of_src _ _ }

end InjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `F ⟶ F.rightDerived 0`. -/
/-
**CategoryTheory.Functor.toRightDerivedZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         [inst_2 
: CategoryTheory.Abelian C] →           [inst_3 : CategoryTheory.HasInjectiveRes
olutions C] →             [inst_4 : CategoryTheory.Abelian D] →               (F
 : CategoryTheory.Functor C D) → [inst_5 : F.Additive] → F ⟶ F.rightDerived 0
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural transformation `F ⟶ F.rightDerived 0`.
-/
noncomputable def Functor.toRightDerivedZero (F : C ⥤ D) [F.Additive] :
    F ⟶ F.rightDerived 0 where
  app X := (injectiveResolution X).toRightDerivedZero' F ≫
    (CochainComplex.isoHomologyπ₀ _).hom ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) 0).inv.app _
  naturality {X Y} f := by
    dsimp [rightDerived]
    rw [assoc, assoc, InjectiveResolution.toRightDerivedZero'_naturality_assoc f
      (injectiveResolution X) (injectiveResolution Y)
      (InjectiveResolution.desc f _ _) (by simp),
      ← HomologicalComplex.homologyπ_naturality_assoc]
    erw [← NatTrans.naturality]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.toRightDerivedZero_eq** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   [inst_2 : CategoryTheory.Abelian
 C] [inst_3 : CategoryTheory.HasInjectiveResolutions C]   [inst_4 : CategoryTheo
ry.Abelian D] {X : C} (I : CategoryTheory.InjectiveResolution X)   (F : Category
Theory.Functor C D) [inst_5 : F.Additive],   F.toRightDerivedZero.app X =     Ca
tegoryTheory.CategoryStruct.comp (I.toRightDerivedZero' F)       (CategoryTheory
.CategoryStruct.comp         (CochainComplex.isoHomologyπ₀ ((F.mapHomologicalCom
plex (ComplexShape.up ℕ)).obj I.cocomplex)).hom         (I.isoRightDerivedObj F 
0).inv)
参数：I : CategoryTheory.InjectiveResolution X；F : CategoryTheory.Functor C D；I.toR
ightDerivedZero' F；CategoryTheory.CategoryStruct.comp         (CochainComplex.is
oHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom
         (I.isoRightDerivedObj F 0).inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
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
· 使用定理 `CategoryTheory.HasInjectiveResolutions.out`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroObject C}   
{inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.InjectiveResolution.toRightDerivedZero'_naturality`：∀ {D 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} D] [inst_1 : CategoryTheo
ry.Abelian D] {C : Type u_2}   [inst_2 : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.InjectiveResolution.desc_commutes_zero`：desc_commutes_zer
o {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) 
: J.ι.f 0 ≫ (desc f I J).f 0 = f ≫ I.ι.f 0
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
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
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
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
· 使用定理 `CategoryTheory.instIsSplitMonoMap`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {X Y : C} (f : Y ⟶…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
（共 37 条，此处仅展示前 30 条）
-/
lemma InjectiveResolution.toRightDerivedZero_eq
    {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.toRightDerivedZero.app X = I.toRightDerivedZero' F ≫
      (CochainComplex.isoHomologyπ₀ _).hom ≫ (I.isoRightDerivedObj F 0).inv := by
  dsimp [Functor.toRightDerivedZero, isoRightDerivedObj]
  have h₁ := InjectiveResolution.toRightDerivedZero'_naturality
    (𝟙 X) (injectiveResolution X) I (desc (𝟙 X) _ _) (by simp) F
  simp only [Functor.map_id, id_comp] at h₁
  have h₂ : (I.isoRightDerivedToHomotopyCategoryObj F).hom =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (desc (𝟙 X) _ _) :=
    comp_id _
  rw [← cancel_mono ((HomotopyCategory.homologyFunctor _ _ 0).map
      (I.isoRightDerivedToHomotopyCategoryObj F).hom),
    assoc, assoc, assoc, assoc, assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, comp_id,
    reassoc_of% h₁, h₂, ← HomologicalComplex.homologyπ_naturality_assoc]
  erw [← NatTrans.naturality]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso (F.toRightDerivedZero.app X) := by
  rw [(InjectiveResolution.self X).toRightDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (P : InjectiveResolution X) :
    IsIso (P.toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  rw [CochainComplex.isIso_liftCycles_iff, ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  exact ⟨KernelFork.mapIsLimit _ (P.isLimitKernelFork) F⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : IsIso (F.toRightDerivedZero.app X) := by
  dsimp [Functor.toRightDerivedZero]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso F.toRightDerivedZero :=
  NatIso.isIso_of_isIso_app _

namespace Functor

/-- The canonical isomorphism `F.rightDerived 0 ≅ F` when `F` is left exact
(i.e. preserves finite limits). -/
@[simps! inv]
/-
**CategoryTheory.Functor.rightDerivedZeroIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instIsIsoFunctorToRightDerivedZero`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} D]   [inst_2 : Category…

--- 原说明 ---
The canonical isomorphism `F.rightDerived 0 ≅ F` when `F` is left exact
(i.e. preserves finite limits).
-/
noncomputable def rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F :=
  (asIso F.toRightDerivedZero).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedZeroIsoSelf_hom_inv_id** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightDerivedZeroIsoSelf_hom_inv_id : F.rightDerivedZeroIsoSelf.hom ≫ F.toR
ightDerivedZero = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma rightDerivedZeroIsoSelf_hom_inv_id :
    F.rightDerivedZeroIsoSelf.hom ≫ F.toRightDerivedZero = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedZeroIsoSelf_inv_hom_id** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightDerivedZeroIsoSelf_inv_hom_id : F.toRightDerivedZero ≫ F.rightDerived
ZeroIsoSelf.hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma rightDerivedZeroIsoSelf_inv_hom_id :
    F.toRightDerivedZero ≫ F.rightDerivedZeroIsoSelf.hom = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedZeroIsoSelf_hom_inv_id_app** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightDerivedZeroIsoSelf_hom_inv_id_app (X : C) : F.rightDerivedZeroIsoSelf
.hom.app X ≫ F.toRightDerivedZero.app X = 𝟙 _
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
lemma rightDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.rightDerivedZeroIsoSelf.hom.app X ≫ F.toRightDerivedZero.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.rightDerivedZeroIsoSelf_inv_hom_id_app** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：rightDerivedZeroIsoSelf_inv_hom_id_app (X : C) : F.toRightDerivedZero.app 
X ≫ F.rightDerivedZeroIsoSelf.hom.app X = 𝟙 _
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
lemma rightDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.toRightDerivedZero.app X ≫ F.rightDerivedZeroIsoSelf.hom.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id_app X

end Functor

end

end CategoryTheory

