/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# The sheafification functor for presheaves of modules

In this file, we construct a functor
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R`
for a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings.
In particular, if `α` is the identity of `R.val`, we obtain the
sheafification functor `PresheafOfModules R.val ⥤ SheafOfModules R`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory Category Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PresheafOfModules

/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  have : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), this is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R`. -/
@[simps! -isSimp map]
/-
**PresheafOfModules.sheafification** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`
。
形式化陈述：sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where obj
 M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of 
rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), th
is is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModul
es.{v} R`.
-/
noncomputable def sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  obj M₀ := sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f
    ((toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat).map f)
      (by apply toSheafify_naturality)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
/-
**PresheafOfModules.sheafificationCompToSheaf** 是 Mathlib 中的一个定义，位于命名空间 `Preshea
fOfModules`。
形式化陈述：sheafificationCompToSheaf : sheafification.{v} α ⋙ SheafOfModules.toSheaf 
_ ≅ toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of presheaves of modules commutes with the functor which
forgets the module structures.
-/
noncomputable def sheafificationCompToSheaf :
    sheafification.{v} α ⋙ SheafOfModules.toSheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat :=
  Iso.refl _

/-- The sheafification of presheaves of modules commutes with the functor which
forgets the module structures. -/
/-
**PresheafOfModules.sheafificationCompForgetCompToPresheaf** 是 Mathlib 中的一个定义，位于
命名空间 `PresheafOfModules`。
形式化陈述：sheafificationCompForgetCompToPresheaf : sheafification.{v} α ⋙ SheafOfMod
ules.forget _ ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat ⋙ 
sheafToPresheaf J AddCommGrpCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of presheaves of modules commutes with the functor which
forgets the module structures.
-/
noncomputable def sheafificationCompForgetCompToPresheaf :
    sheafification.{v} α ⋙ SheafOfModules.forget _ ⋙ toPresheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat ⋙ sheafToPresheaf J AddCommGrpCat :=
  Iso.refl _

/-- The bijection between types of morphisms which is part of the adjunction
`sheafificationAdjunction`. -/
/-
**PresheafOfModules.sheafificationHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOf
Modules`。
形式化陈述：sheafificationHomEquiv {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.
{v} R} : ((sheafification α).obj P ⟶ F) ≃ (P ⟶ (restrictScalars α).obj ((SheafOf
Modules.forget _).obj F))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between types of morphisms which is part of the adjunction
`sheafificationAdjunction`.
-/
noncomputable def sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R} :
    ((sheafification α).obj P ⟶ F) ≃
      (P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) := by
  apply sheafifyHomEquiv
/-
**PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def** 是 Mathlib 中的一个引理
，位于命名空间 `PresheafOfModules`。
形式化陈述：toPresheaf_map_sheafificationHomEquiv_def {P : PresheafOfModules.{v} R₀} {
F : SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) : (toPresheaf R₀).m
ap (sheafificationHomEquiv α f) = CategoryTheory.toSheafify J P.presheaf ≫ (toPr
esheaf R.obj).map f.val
参数：f : (sheafification α).obj P ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresheaf_map_sheafificationHomEquiv_def
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      CategoryTheory.toSheafify J P.presheaf ≫ (toPresheaf R.obj).map f.val := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.toPresheaf_map_sheafificationHomEquiv** 是 Mathlib 中的一个引理，位于命
名空间 `PresheafOfModules`。
形式化陈述：toPresheaf_map_sheafificationHomEquiv {P : PresheafOfModules.{v} R₀} {F : 
SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) : (toPresheaf R₀).map (
sheafificationHomEquiv α f) = (sheafificationAdjunction J AddCommGrpCat).homEqui
v P.presheaf ((SheafOfModules.toSheaf _).obj F) ((SheafOfModules.toSheaf _).map 
f)
参数：f : (sheafification α).obj P ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def`：toPresheaf_
map_sheafificationHomEquiv_def {P : PresheafOfModules.{v} R₀} {F : SheafOfModule
s.{v} R} (f : (sheafification α).obj P ⟶ F) : (to…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
-/
lemma toPresheaf_map_sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      (sheafificationAdjunction J AddCommGrpCat).homEquiv P.presheaf
        ((SheafOfModules.toSheaf _).obj F) ((SheafOfModules.toSheaf _).map f) := by
  rw [toPresheaf_map_sheafificationHomEquiv_def, Adjunction.homEquiv_unit]
  dsimp

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm** 是 Mathlib 中的一个引理，位
于命名空间 `PresheafOfModules`。
形式化陈述：toSheaf_map_sheafificationHomEquiv_symm {P : PresheafOfModules.{v} R₀} {F 
: SheafOfModules.{v} R} (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget
 _).obj F)) : (SheafOfModules.toSheaf _).map ((sheafificationHomEquiv α).symm g)
 = (((sheafificationAdjunction J AddCommGrpCat).homEquiv P.presheaf ((SheafOfMod
ules.toSheaf R).obj F)).symm ((toPresheaf R₀).map g))
参数：g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma toSheaf_map_sheafificationHomEquiv_symm
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    (SheafOfModules.toSheaf _).map ((sheafificationHomEquiv α).symm g) =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm ((toPresheaf R₀).map g)) := by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings, this is the adjunction
`sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α`. -/
/-
**PresheafOfModules.sheafificationAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Presheaf
OfModules`。
形式化陈述：sheafificationAdjunction : sheafification.{v} α ⊣ SheafOfModules.forget R 
⋙ restrictScalars α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of 
rings
and `R` a sheaf of rings, this is the adjunction
`sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α`.
-/
noncomputable def sheafificationAdjunction :
    sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g ↦ by
        apply (SheafOfModules.toSheaf _).map_injective
        simp only [Functor.comp_obj, Functor.map_comp]
        rw [toSheaf_map_sheafificationHomEquiv_symm α (f ≫ g),
          toSheaf_map_sheafificationHomEquiv_symm α g, Functor.map_comp]
        apply (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).homEquiv_naturality_left_symm
      homEquiv_naturality_right := fun {P₀ M N} f g ↦ by
        apply (toPresheaf _).map_injective
        erw [toPresheaf_map_sheafificationHomEquiv] }
/-
**PresheafOfModules.sheafificationAdjunction_homEquiv_apply** 是 Mathlib 中的一个引理，位
于命名空间 `PresheafOfModules`。
形式化陈述：sheafificationAdjunction_homEquiv_apply {P : PresheafOfModules.{v} R₀} {F 
: SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) : (sheafificationAdju
nction α).homEquiv P F f = sheafificationHomEquiv α f
参数：f : (sheafification α).obj P ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafificationAdjunction_homEquiv_apply {P : PresheafOfModules.{v} R₀}
    {F : SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) :
    (sheafificationAdjunction α).homEquiv P F f = sheafificationHomEquiv α f := rfl

@[simp]
/-
**PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app** 是 Mathlib
 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：toPresheaf_map_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{
v} R₀) : (toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀) = Categor
yTheory.toSheafify J M₀.presheaf
参数：M₀ : PresheafOfModules.{v} R₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresheaf_map_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀) :
    (toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀) =
      CategoryTheory.toSheafify J M₀.presheaf := rfl

@[simp]
/-
**PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app** 是 Mathlib 
中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：toSheaf_map_sheafificationAdjunction_counit_app (M : SheafOfModules.{v} R)
 : (SheafOfModules.toSheaf R).map ((sheafificationAdjunction α).counit.app M) = 
(CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{v}).counit.app ((Sheaf
OfModules.toSheaf R).obj M)
参数：M : SheafOfModules.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm`：toSheaf_map_s
heafificationHomEquiv_symm {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v
} R} (g : P ⟶ (restrictScalars α).obj ((SheafOf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_symm_id`：homEquiv_symm_id (X : D) : (
adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X
-/
lemma toSheaf_map_sheafificationAdjunction_counit_app (M : SheafOfModules.{v} R) :
    (SheafOfModules.toSheaf R).map ((sheafificationAdjunction α).counit.app M) =
      (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).counit.app ((SheafOfModules.toSheaf R).obj M) :=
  (toSheaf_map_sheafificationHomEquiv_symm _ _).trans
    (by rw [← Adjunction.homEquiv_symm_id]; rfl)
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (sheafification.{v} α).IsLeftAdjoint :=
  (sheafificationAdjunction α).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (sheafificationAdjunction α).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  simp only [Functor.id_obj, toSheaf_map_sheafificationAdjunction_counit_app]
  infer_instance
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Full :=
  (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.full
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Faithful :=
  (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.faithful

end

section

variable [HasSheafify J AddCommGrpCat.{v}]

/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    PreservesFiniteLimits (sheafification.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
  comp_preservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGrpCat)
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_comp (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R) where
  reflects _ _ _ := inferInstance
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (sheafification.{v} α) :=
  preservesFiniteLimits_of_reflects_of_preserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

end

end PresheafOfModules

