/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheaves of modules over a sheaf of rings

In this file, we define the category `SheafOfModules R` when `R : Sheaf J RingCat`
is a sheaf of rings on a category `C` equipped with a Grothendieck topology `J`.

-/

@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A sheaf of modules is a presheaf of modules such that the underlying presheaf
of abelian groups is a sheaf. -/
/-
**SheafOfModules** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       CategoryTheory.Sheaf J RingCat → T
ype (max (max (max u u₁) (v + 1)) v₁)
参数：max (max (max u u₁) (v + 1)) v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf of modules is a presheaf of modules such that the underlying presheaf
of abelian groups is a sheaf.
-/
structure SheafOfModules where
  /-- the underlying presheaf of modules of a sheaf of modules -/
  val : PresheafOfModules.{v} R.obj
  isSheaf : Presheaf.IsSheaf J val.presheaf

namespace SheafOfModules

variable {R}

/-- A morphism between sheaves of modules is a morphism between the underlying
presheaves of modules. -/
@[ext]
/-
**SheafOfModules.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SheafOfModules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Sheaf J RingCa
t} → SheafOfModules R → SheafOfModules R → Type (max u₁ v)
参数：max u₁ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between sheaves of modules is a morphism between the underlying
presheaves of modules.
-/
structure Hom (X Y : SheafOfModules.{v} R) where
  /-- a morphism between the underlying presheaves of modules -/
  val : X.val ⟶ Y.val
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (SheafOfModules.{v} R) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]
/-
**SheafOfModules.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val) : f
 = g
参数：h : f.val = g.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Category.
{v₁, u₁} C} {J : CategoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sh
eaf J RingCa…
-/
lemma hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext h

@[simp]
/-
**SheafOfModules.id_val** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：id_val (X : SheafOfModules.{v} R) : Hom.val (𝟙 X) = 𝟙 X.val
参数：X : SheafOfModules.{v} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_val (X : SheafOfModules.{v} R) : Hom.val (𝟙 X) = 𝟙 X.val := rfl

@[simp, reassoc]
/-
**SheafOfModules.comp_val** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：comp_val {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).
val = f.val ≫ g.val
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_val {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val := rfl

variable (R)
/-- The forgetful functor `SheafOfModules.{v} R ⥤ PresheafOfModules R.val`. -/
@[simps]
/-
**SheafOfModules.forget** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `SheafOfModules.{v} R ⥤ PresheafOfModules R.val`.
-/
def forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where
  obj F := F.val
  map φ := φ.val

/-- The forget functor `SheafOfModules R ⥤ PresheafOfModules R.val` is fully faithful. -/
@[simps]
/-
**SheafOfModules.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：fullyFaithfulForget : (forget.{v} R).FullyFaithful where preimage φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forget functor `SheafOfModules R ⥤ PresheafOfModules R.val` is fully faithfu
l.
-/
def fullyFaithfulForget : (forget.{v} R).FullyFaithful where
  preimage φ := ⟨φ⟩
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget.{v} R).Faithful := (fullyFaithfulForget R).faithful
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget.{v} R).Full := (fullyFaithfulForget R).full
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget.{v} R).ReflectsIsomorphisms := (fullyFaithfulForget R).reflectsIsomorphisms

/-- Evaluation on an object `X` gives a functor
`SheafOfModules R ⥤ ModuleCat (R.val.obj X)`. -/
/-
**SheafOfModules.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj X)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation on an object `X` gives a functor
`SheafOfModules R ⥤ ModuleCat (R.val.obj X)`.
-/
def evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj X) :=
  forget _ ⋙ PresheafOfModules.evaluation _ X

/-- The forget functor `SheafOfModules R ⥤ Sheaf J AddCommGrpCat`. -/
@[simps]
/-
**SheafOfModules.toSheaf** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：toSheaf : SheafOfModules.{v} R ⥤ Sheaf J AddCommGrpCat.{v} where obj M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.isSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.
{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sh
eaf J RingCa…

--- 原说明 ---
The forget functor `SheafOfModules R ⥤ Sheaf J AddCommGrpCat`.
-/
noncomputable def toSheaf : SheafOfModules.{v} R ⥤ Sheaf J AddCommGrpCat.{v} where
  obj M := ⟨_, M.isSheaf⟩
  map f := { hom := (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f }

/--
The forgetful functor from sheaves of modules over sheaf of ring `R` to sheaves of `R(X)`-module
when `X` is initial.
-/
@[simps]
/-
**SheafOfModules.forgetToSheafModuleCat** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModule
s`。
形式化陈述：forgetToSheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) : SheafOfModule
s.{w} R ⥤ Sheaf J (ModuleCat.{w} (R.1.obj X)) where obj M
参数：X : Cᵒᵖ；hX : Limits.IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from sheaves of modules over sheaf of ring `R` to sheaves 
of `R(X)`-module
when `X` is initial.
-/
noncomputable def forgetToSheafModuleCat
      (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    SheafOfModules.{w} R ⥤ Sheaf J (ModuleCat.{w} (R.1.obj X)) where
  obj M := ⟨(PresheafOfModules.forgetToPresheafModuleCat X hX).obj M.1,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{w} (R.1.obj X)) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom := (PresheafOfModules.forgetToPresheafModuleCat X hX).map f.1 }

set_option backward.defeqAttrib.useBackward true in
/-- Isomorphism on `forgetToSheafModuleCat` when given isomorphic initial objects. -/
/-
**SheafOfModules.forgetToSheafModuleCatOfIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfM
odules`。
形式化陈述：forgetToSheafModuleCatOfIso (X Y : Cᵒᵖ) (hX : Limits.IsInitial X) (hY : Li
mits.IsInitial Y) (φ : X ≅ Y) : forgetToSheafModuleCat R X hX ≅ forgetToSheafMod
uleCat R Y hY ⋙ sheafCompose J (ModuleCat.restrictScalars (R.obj.map φ.hom).hom)
参数：X Y : Cᵒᵖ；hX : Limits.IsInitial X；hY : Limits.IsInitial Y；φ : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphism on `forgetToSheafModuleCat` when given isomorphic initial objects.
-/
noncomputable def forgetToSheafModuleCatOfIso (X Y : Cᵒᵖ) (hX : Limits.IsInitial X)
    (hY : Limits.IsInitial Y) (φ : X ≅ Y) :
    forgetToSheafModuleCat R X hX ≅ forgetToSheafModuleCat R Y hY ⋙
      sheafCompose J (ModuleCat.restrictScalars (R.obj.map φ.hom).hom) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · dsimp [PresheafOfModules.forgetToPresheafModuleCatObjObj]
      refine ModuleCat.restrictScalarsComp'App _ _ _ ?_ _
      simpa using congr((R.obj.map $(hX.hom_ext (hX.to U) (φ.hom ≫ hY.to U))).hom)
    cat_disch
  cat_disch

/-- The canonical isomorphism between
`SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v}`
and `SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.val`. -/
/-
**SheafOfModules.toSheafCompSheafToPresheafIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafO
fModules`。
形式化陈述：toSheafCompSheafToPresheafIso : toSheaf R ⋙ sheafToPresheaf J AddCommGrpCa
t.{v} ≅ forget R ⋙ PresheafOfModules.toPresheaf R.obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between
`SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v}`
and `SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.val`.
-/
noncomputable def toSheafCompSheafToPresheafIso :
    toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v} ≅
      forget R ⋙ PresheafOfModules.toPresheaf R.obj := Iso.refl _
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toSheaf.{v} R).Faithful :=
  Functor.Faithful.of_comp_iso (toSheafCompSheafToPresheafIso.{v} R)
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M N : SheafOfModules.{v} R) : AddCommGroup (M ⟶ N) :=
  (fullyFaithfulForget R).homEquiv.addCommGroup

@[simp]
/-
**SheafOfModules.add_val** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：add_val {M N : SheafOfModules.{v} R} (f g : M ⟶ N) : (f + g).val = f.val +
 g.val
参数：f g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_val {M N : SheafOfModules.{v} R} (f g : M ⟶ N) :
    (f + g).val = f.val + g.val := rfl
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (SheafOfModules.{v} R) where
  add_comp := by intros; ext1; dsimp; simp only [Preadditive.add_comp]
  comp_add := by tauto
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget R).Additive where
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toSheaf R).Additive where

variable {R}

/-- The type of sections of a sheaf of modules. -/
/-
**SheafOfModules.sections** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModules`。
形式化陈述：sections (M : SheafOfModules.{v} R) : Type _
参数：M : SheafOfModules.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of sections of a sheaf of modules.
-/
abbrev sections (M : SheafOfModules.{v} R) : Type _ := M.val.sections

/-- The map `M.sections → N.sections` induced by a morphism `M ⟶ N` of sheaves of modules. -/
/-
**SheafOfModules.sectionsMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModules`。
形式化陈述：sectionsMap {M N : SheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.
sections
参数：f : M ⟶ N；s : M.sections。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `M.sections → N.sections` induced by a morphism `M ⟶ N` of sheaves of mo
dules.
-/
abbrev sectionsMap {M N : SheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  PresheafOfModules.sectionsMap f.val s

@[simp]
/-
**SheafOfModules.sectionsMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} {M N P : Sh
eafOfModules R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections),   SheafOfModules.secti
onsMap (CategoryTheory.CategoryStruct.comp f g) s =     SheafOfModules.sectionsM
ap g (SheafOfModules.sectionsMap f s)
参数：f : M ⟶ N；g : N ⟶ P；s : M.sections；CategoryTheory.CategoryStruct.comp f g；She
afOfModules.sectionsMap f s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectionsMap_comp {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
/-
**SheafOfModules.sectionsMap_id** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} {M : SheafO
fModules R} (s : M.sections),   SheafOfModules.sectionsMap (CategoryTheory.Categ
oryStruct.id M) s = s
参数：s : M.sections；CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectionsMap_id {M : SheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

variable (R) in
/-- The functor which sends a sheaf of modules to its type of sections. -/
@[simps]
/-
**SheafOfModules.sectionsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：sectionsFunctor : SheafOfModules.{v} R ⥤ Type _ where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a sheaf of modules to its type of sections.
-/
def sectionsFunctor : SheafOfModules.{v} R ⥤ Type _ where
  obj M := M.sections
  map f := ↾(sectionsMap f)

variable (R) in
/-- The obvious free sheaf of modules of rank `1`. -/
@[simps]
/-
**SheafOfModules.unit** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：unit : SheafOfModules R where val
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious free sheaf of modules of rank `1`.
-/
noncomputable def unit : SheafOfModules R where
  val := PresheafOfModules.unit R.obj
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj R).property

/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : SheafOfModules R`. -/
/-
**SheafOfModules.unitHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：unitHomEquiv (M : SheafOfModules R) : (unit R ⟶ M) ≃ M.sections
参数：M : SheafOfModules R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The bijection `(unit R ⟶ M) ≃ M.sections` for `M : SheafOfModules R`.
-/
noncomputable def unitHomEquiv (M : SheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections :=
  (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]
/-
**SheafOfModules.unitHomEquiv_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModule
s`。
形式化陈述：unitHomEquiv_apply_coe (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ) :
 (M.unitHomEquiv f).val X = f.val.app X (1 : R.obj.obj X)
参数：M : SheafOfModules R；f : unit R ⟶ M；X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitHomEquiv_apply_coe (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ) :
    (M.unitHomEquiv f).val X = f.val.app X (1 : R.obj.obj X) := rfl
/-
**SheafOfModules.unitHomEquiv_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModul
es`。
形式化陈述：unitHomEquiv_comp_apply {M N : SheafOfModules.{u} R} (f : unit R ⟶ M) (p :
 M ⟶ N) : N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f)
参数：f : unit R ⟶ M；p : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitHomEquiv_comp_apply {M N : SheafOfModules.{u} R}
    (f : unit R ⟶ M) (p : M ⟶ N) :
    N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f) := rfl
/-
**SheafOfModules.unitHomEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModule
s`。
形式化陈述：unitHomEquiv_symm_comp {M N : SheafOfModules.{u} R} (s : M.sections) (p : 
M ⟶ N) : M.unitHomEquiv.symm s ≫ p = N.unitHomEquiv.symm (sectionsMap p s)
参数：s : M.sections；p : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitHomEquiv_symm_comp {M N : SheafOfModules.{u} R} (s : M.sections) (p : M ⟶ N) :
    M.unitHomEquiv.symm s ≫ p = N.unitHomEquiv.symm (sectionsMap p s) :=
  N.unitHomEquiv.injective (by simp [unitHomEquiv_comp_apply])

end SheafOfModules

namespace PresheafOfModules

variable (J)
variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{v} R} (f : M₁ ⟶ M₂)

/-- A morphism of presheaves of modules is locally surjective
if the underlying morphism of presheaves of abelian groups is. -/
/-
**PresheafOfModules.IsLocallySurjective** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfMod
ules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     Catego
ryTheory.GrothendieckTopology C →       {R : CategoryTheory.Functor Cᵒᵖ RingCat}
 → {M₁ M₂ : PresheafOfModules R} → (M₁ ⟶ M₂) → Prop
参数：M₁ ⟶ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of presheaves of modules is locally surjective
if the underlying morphism of presheaves of abelian groups is.
-/
abbrev IsLocallySurjective : Prop :=
  Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f)

/-- A morphism of presheaves of modules is locally injective
if the underlying morphism of presheaves of abelian groups is. -/
/-
**PresheafOfModules.IsLocallyInjective** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModu
les`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     Catego
ryTheory.GrothendieckTopology C →       {R : CategoryTheory.Functor Cᵒᵖ RingCat}
 → {M₁ M₂ : PresheafOfModules R} → (M₁ ⟶ M₂) → Prop
参数：M₁ ⟶ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of presheaves of modules is locally injective
if the underlying morphism of presheaves of abelian groups is.
-/
abbrev IsLocallyInjective : Prop :=
  Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f)

variable {N : PresheafOfModules.{v} R} (hN : Presheaf.IsSheaf J N.presheaf)
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [IsLocallySurjective J f] [IsLocallyInjective J f]

variable {J}

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(M₂ ⟶ N) ≃ (M₁ ⟶ N)` induced by a locally bijective morphism
`f : M₁ ⟶ M₂` of presheaves of modules, when `N` is a sheaf. -/
@[simps]
/-
**PresheafOfModules.homEquivOfIsLocallyBijective** 是 Mathlib 中的一个定义，位于命名空间 `Pres
heafOfModules`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R : CategoryTheory.Functor Cᵒᵖ Ri
ngCat} →         {M₁ M₂ : PresheafOfModules R} →           (f : M₁ ⟶ M₂) →      
       {N : PresheafOfModules R} →               CategoryTheory.Presheaf.IsSheaf
 J N.presheaf →                 [J.WEqualsLocallyBijective AddCommGrpCat] →     
              [PresheafOfModules.IsLocallySurjective J f] →                     
[PresheafOfModules.IsLocallyInjective J f] → (M₂ ⟶ N) ≃ (M₁ ⟶ N)
参数：f : M₁ ⟶ M₂；M₂ ⟶ N；M₁ ⟶ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `(M₂ ⟶ N) ≃ (M₁ ⟶ N)` induced by a locally bijective morphism
`f : M₁ ⟶ M₂` of presheaves of modules, when `N` is a sheaf.
-/
noncomputable def homEquivOfIsLocallyBijective : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  toFun φ := f ≫ φ
  invFun ψ := homMk (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surjective
          ((PresheafOfModules.toPresheaf R).map ψ)
        simp only [← hφ, Equiv.symm_apply_apply]
        replace hφ : ∀ (Z : Cᵒᵖ) (x : M₁.obj Z), φ.app Z (f.app Z x) = ψ.app Z x :=
          fun Z x ↦ CategoryTheory.congr_fun (congr_app hφ Z) x
        intro X r y
        apply hN.isSeparated _ _
          (Presheaf.imageSieve_mem J ((toPresheaf R).map f) y)
        rintro Y p ⟨x : M₁.obj _, hx : f.app _ x = M₂.map p.op y⟩
        have hφ' : ∀ (z : M₂.obj X), φ.app _ (M₂.map p.op z) =
            N.map p.op (φ.app _ z) := CategoryTheory.congr_fun (φ.naturality p.op)
        change N.map p.op (φ.app X (r • y)) = N.map p.op (r • φ.app X y)
        rw [← hφ', M₂.map_smul, ← hx, ← (f.app _).hom.map_smul, hφ, (ψ.app _).hom.map_smul,
          ← hφ, hx, N.map_smul, hφ'])
  left_inv φ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).left_inv
      ((PresheafOfModules.toPresheaf R).map φ))
  right_inv ψ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).right_inv
      ((PresheafOfModules.toPresheaf R).map ψ))

end PresheafOfModules

