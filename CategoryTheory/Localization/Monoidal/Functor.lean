/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Trifunctor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.Tactic.CategoryTheory.Coherence

/-!

# Universal property of localized monoidal categories

This file proves that, given a monoidal localization functor `L : C ⥤ D`, and a functor
`F : D ⥤ E` to a monoidal category, such that `F` lifts along `L` to a monoidal functor `G`,
then `F` is monoidal. See `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

namespace CategoryTheory

open CategoryTheory MonoidalCategory CategoryTheory.Functor MonoidalCategory.Functor Monoidal
open LaxMonoidal OplaxMonoidal

namespace Localization.Monoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

@[simps]
/-
**CategoryTheory.Localization.Monoidal.lifting** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lifting₂CurriedTensorPre :
    Lifting₂ L L W W (curriedTensorPre G) (curriedTensorPre F) where
  iso := curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]
/-
**CategoryTheory.Localization.Monoidal.lifting** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lifting₂CurriedTensorPost :
    Lifting₂ L L W W (curriedTensorPost G) (curriedTensorPost F) where
  iso := (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

/--
The natural isomorphism of bifunctors `F - ⊗ F - ≅ F (- ⊗ -)`, given that `F` lifts along `L`
to a monoidal functor `G`, where `L` is a monoidal localization functor.
-/
/-
**CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：curriedTensorPreIsoPost : curriedTensorPre F ≅ curriedTensorPost F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism of bifunctors `F - ⊗ F - ≅ F (- ⊗ -)`, given that `F` li
fts along `L`
to a monoidal functor `G`, where `L` is a monoidal localization functor.
-/
noncomputable def curriedTensorPreIsoPost : curriedTensorPre F ≅ curriedTensorPost F :=
  lift₂NatIso L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    (Functor.curriedTensorPreIsoPost G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：curriedTensorPreIsoPost_hom_app_app (X₁ X₂ : C) : letI e
参数：X₁ X₂ : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.lift₂NatTrans_app_app`：lift₂NatTrans_app_app
 (τ : F₁ ⟶ F₂) (X₁ : C₁) (X₂ : C₂) : ((lift₂NatTrans L₁ L₂ W₁ W₂ F₁ F₂ F₁' F₂' τ
).app (L₁.obj X₁)).app (L₂.obj X₂) = ((…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma curriedTensorPreIsoPost_hom_app_app (X₁ X₂ : C) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ ⊗ₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [curriedTensorPreIsoPost]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：curriedTensorPreIsoPost_hom_app_app' {X₁ X₂ : C} {Y₁ Y₂ : D} (e₁ : Y₁ ≅ L.
obj X₁) (e₂ : Y₂ ≅ L.obj X₂) : letI e
参数：e₁ : Y₁ ≅ L.obj X₁；e₂ : Y₂ ≅ L.obj X₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
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
· 使用引理 `CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app
`：curriedTensorPreIsoPost_hom_app_app (X₁ X₂ : C) : letI e
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {X₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g :…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma curriedTensorPreIsoPost_hom_app_app' {X₁ X₂ : C} {Y₁ Y₂ : D}
    (e₁ : Y₁ ≅ L.obj X₁) (e₂ : Y₂ ≅ L.obj X₂) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) ⊗ₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _ ≫ (e₁.inv ⊗ₘ e₂.inv)) := by
  have h₁ := ((curriedTensorPreIsoPost L W F G).hom.app Y₁).naturality e₂.hom
  have h₂ := congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality e₁.hom)
  dsimp at h₁ h₂ ⊢
  rw [← cancel_mono (F.map (Y₁ ◁ e₂.hom)), ← h₁, ← cancel_mono (F.map (e₁.hom ▷ L.obj X₂)),
    Category.assoc, ← h₂, curriedTensorPreIsoPost_hom_app_app, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, ← tensorHom_def'_assoc, tensorHom_comp_tensorHom_assoc,
    ← Functor.map_comp, ← tensorHom_def', ← Functor.map_comp, Category.assoc,
    tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id, tensorHom_id, id_whiskerRight,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor `G`,
where `L` is a monoidal localization functor.
-/
@[simps!]
/-
**CategoryTheory.Localization.Monoidal.functorCoreMonoidalOfComp** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：functorCoreMonoidalOfComp : F.CoreMonoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor 
`G`,
where `L` is a monoidal localization functor.
-/
noncomputable def functorCoreMonoidalOfComp : F.CoreMonoidal := by
  letI e := Lifting.iso L W G F
  refine Functor.CoreMonoidal.ofBifunctor
    (εIso G ≪≫ e.symm.app _ ≪≫ F.mapIso (εIso L).symm) (curriedTensorPreIsoPost L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ ↦ ?_)
    dsimp [e]
    rw [curriedTensorPreIsoPost_hom_app_app, curriedTensorPreIsoPost_hom_app_app,
      curriedTensorPreIsoPost_hom_app_app' L W F G (μIso L _ _) (Iso.refl _),
      curriedTensorPreIsoPost_hom_app_app' L W F G (Iso.refl _) (μIso L _ _)]
    monoidal_simps
    /-
    The following `simp only` block was generated by:
    ```
    simp? [← comp_whiskerRight_assoc, -comp_whiskerRight, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]
    ```
    -/
    simp only [comp_obj, μIso_hom, Iso.refl_hom, map_id, Category.id_comp, μIso_inv, Iso.refl_inv,
      MonoidalCategory.whiskerLeft_id, Category.comp_id, map_comp, Category.assoc,
      ← comp_whiskerRight_assoc, map_δ_μ_assoc, Iso.inv_hom_id_app, id_whiskerRight,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, whiskerRight_tensor]
    simp [← whisker_exchange_assoc, tensor_whiskerLeft_symm, -tensor_whiskerLeft,
      ← LaxMonoidal.associativity_assoc G, ← Functor.map_comp]
  · refine natTrans_ext L W (fun X₂ ↦ ?_)
    have := NatTrans.congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality (εIso L).inv)
      (L.obj X₂)
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, ← comp_whiskerRight_assoc,
      -comp_whiskerRight, tensorHom_def, ← whisker_exchange_assoc, ← map_comp]
  · refine natTrans_ext L W (fun X₁ ↦ ?_)
    have := ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).naturality (εIso L).inv
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, tensorHom_def,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← map_comp]

/--
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor `G`,
where `L` is a monoidal localization functor.
-/
@[instance_reducible]
/-
**CategoryTheory.Localization.Monoidal.functorMonoidalOfComp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：functorMonoidalOfComp : F.Monoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor 
`G`,
where `L` is a monoidal localization functor.
-/
noncomputable def functorMonoidalOfComp : F.Monoidal :=
  (functorCoreMonoidalOfComp L W F G).toMonoidal

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorMonoidalOfComp_ε : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    ε F = ε G ≫ e.inv.app _ ≫ F.map (η L) :=
  rfl

@[reassoc]
/-
**CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Localization.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorMonoidalOfComp_μ (X Y : C) : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    μ F (L.obj X) (L.obj Y) = (e.hom.app _ ⊗ₘ e.hom.app _) ≫ μ G X Y ≫ e.inv.app _ ≫
        F.map (δ L _ _) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, curriedTensorPreIsoPost_hom_app_app]

/--
When `F` is given the monoidal structure `functorMonoidalOfComp` that is obtained by lifting along
a monoidal localization functor `L`, then the lifting isomorphism is a monoidal natural
transformation.
-/
/-
**CategoryTheory.Localization.Monoidal.lifting_isMonoidal** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Localization.Monoidal`。
形式化陈述：lifting_isMonoidal : letI : F.Monoidal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.Monoidal.map_η_ε`：map_η_ε (G : D ⥤ C') : G.map (η
 F) ≫ G.map (ε F) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_μ`：functorMon
oidalOfComp_μ (X Y : C) : letI
· 使用引理 `CategoryTheory.Functor.Monoidal.map_δ_μ`：map_δ_μ (G : D ⥤ C') (X Y : C) 
: G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _

--- 原说明 ---
When `F` is given the monoidal structure `functorMonoidalOfComp` that is obtaine
d by lifting along
a monoidal localization functor `L`, then the lifting isomorphism is a monoidal 
natural
transformation.
-/
instance lifting_isMonoidal :
    letI : F.Monoidal := functorMonoidalOfComp L W F G
    (Lifting.iso L W G F).hom.IsMonoidal := by
  let : F.Monoidal := functorMonoidalOfComp L W F G
  refine ⟨?_, fun _ _ ↦ ?_⟩
  · simp [functorMonoidalOfComp_ε]
  · simp [functorMonoidalOfComp_μ]

end CategoryTheory.Localization.Monoidal

