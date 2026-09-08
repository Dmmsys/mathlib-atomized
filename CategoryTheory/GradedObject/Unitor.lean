/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Associator
public import Mathlib.CategoryTheory.GradedObject.Single
/-!
# The left and right unitors

Given a bifunctor `F : C ⥤ D ⥤ D`, an object `X : C` such that `F.obj X ≅ 𝟭 D` and a
map `p : I × J → J` such that `hp : ∀ (j : J), p ⟨0, j⟩ = j`,
we define an isomorphism of `J`-graded objects for any `Y : GradedObject J D`.
`mapBifunctorLeftUnitor F X e p hp Y : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`.
Under similar assumptions, we also obtain a right unitor isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`. Finally,
the lemma `mapBifunctor_triangle` promotes a triangle identity involving functors
to a triangle identity for the induced functors on graded objects.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace GradedObject

section LeftUnitor

variable {C D I J : Type*} [Category* C] [Category* D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : C ⥤ D ⥤ D) (X : C) (e : F.obj X ≅ 𝟭 D)
  [∀ (Y : D), PreservesColimit (Functor.empty.{0} C) (F.flip.obj Y)]
  (p : I × J → J) (hp : ∀ (j : J), p ⟨0, j⟩ = j)
  (Y Y' : GradedObject J D) (φ : Y ⟶ Y')

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D` and `Y : GradedObject J D`,
this is the isomorphism `((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2`
when `a : I × J` is such that `a.1 = 0`. -/
@[simps!]
/-
**CategoryTheory.GradedObject.mapBifunctorObjSingle** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GradedObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D` and `Y : GradedObject J D`,
this is the isomorphism `((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a 
≅ Y a.2`
when `a : I × J` is such that `a.1 = 0`.
-/
noncomputable def mapBifunctorObjSingle₀ObjIso (a : I × J) (ha : a.1 = 0) :
    ((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a ≅ Y a.2 :=
  (F.mapIso (singleObjApplyIsoOfEq _ X _ ha)).app _ ≪≫ e.app (Y a.2)

/-- Given `F : C ⥤ D ⥤ D`, `X : C` and `Y : GradedObject J D`,
`((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a` is an initial object
when `a : I × J` is such that `a.1 ≠ 0`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorObjSingle** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GradedObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D ⥤ D`, `X : C` and `Y : GradedObject J D`,
`((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a` is an initial object
when `a : I × J` is such that `a.1 ≠ 0`.
-/
noncomputable def mapBifunctorObjSingle₀ObjIsInitial (a : I × J) (ha : a.1 ≠ 0) :
    IsInitial (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y a) :=
  IsInitial.isInitialObj (F.flip.obj (Y a.2)) _ (isInitialSingleObjApply _ _ _ ha)

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`, see `mapBifunctorLeftUnitor`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitorCofan** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitorCofan (hp : forall (j : J), p ⟨0, j⟩ = j) (Y) (j : J
) : (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y).CofanMapObjFun p j
参数：hp : forall (j : J), p ⟨0, j⟩ = j；Y；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`, see `mapBifunctorLeftUnitor`
.
-/
noncomputable def mapBifunctorLeftUnitorCofan (hp : ∀ (j : J), p ⟨0, j⟩ = j) (Y) (j : J) :
    (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (Y j) (fun a ha =>
    if ha : a.1 = 0 then
      (mapBifunctorObjSingle₀ObjIso F X e Y a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjSingle₀ObjIsInitial F X Y a ha).to _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitorCofan_inj** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitorCofan_inj (j : J) : (mapBifunctorLeftUnitorCofan F X
 e p hp Y j).inj ⟨⟨0, j⟩, hp j⟩ = (F.map (singleObjApplyIso (0 : I) X).hom).app 
(Y j) ≫ e.hom.app (Y j)
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mapBifunctorLeftUnitorCofan_inj (j : J) :
    (mapBifunctorLeftUnitorCofan F X e p hp Y j).inj ⟨⟨0, j⟩, hp j⟩ =
      (F.map (singleObjApplyIso (0 : I) X).hom).app (Y j) ≫ e.hom.app (Y j) := by
  simp [mapBifunctorLeftUnitorCofan]

set_option backward.isDefEq.respectTransparency false in
/-- The cofan `mapBifunctorLeftUnitorCofan F X e p hp Y j` is a colimit. -/
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitorCofanIsColimit** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitorCofanIsColimit (j : J) : IsColimit (mapBifunctorLeft
UnitorCofan F X e p hp Y j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan `mapBifunctorLeftUnitorCofan F X e p hp Y j` is a colimit.
-/
noncomputable def mapBifunctorLeftUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorLeftUnitorCofan F X e p hp Y j) :=
  Cofan.IsColimit.mk _
    (fun s => e.inv.app (Y j) ≫
      (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫ s.inj ⟨⟨0, j⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨i, j'⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        simp
      · apply IsInitial.hom_ext
        exact mapBifunctorObjSingle₀ObjIsInitial _ _ _ _ hi)
    (fun s m hm => by simp [← hm ⟨⟨0, j⟩, hp j⟩])

include e hp in
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitor_hasMap** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitor_hasMap : HasMap (((mapBifunctor F I J).obj ((single
₀ I).obj X)).obj Y) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.CofanMapObjFun.hasMap`：hasMap (c : forall j,
 CofanMapObjFun X p j) (hc : forall j, IsColimit (c j)) : X.HasMap p
-/
lemma mapBifunctorLeftUnitor_hasMap :
    HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y)

variable [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y) p]
  [HasMap (((mapBifunctor F I J).obj ((single₀ I).obj X)).obj Y') p]

/-- Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the left unitor isomorphism `mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitor : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : C ⥤ D ⥤ D`, `X : C`, `e : F.obj X ≅ 𝟭 D`, `Y : GradedObject J D` and
`p : I × J → J` such that `p ⟨0, j⟩ = j` for all `j`,
this is the left unitor isomorphism `mapBifunctorMapObj F p ((single₀ I).obj X) 
Y ≅ Y`.
-/
noncomputable def mapBifunctorLeftUnitor : mapBifunctorMapObj F p ((single₀ I).obj X) Y ≅ Y :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorLeftUnitorCofanIsColimit F X e p hp Y j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorLeftUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) ≫
      (mapBifunctorLeftUnitor F X e p hp Y).hom j =
      (F.map (singleObjApplyIso (0 : I) X).hom).app _ ≫ e.hom.app (Y j) := by
  dsimp [mapBifunctorLeftUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorLeftUnitorCofan_inj]
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitor_inv_apply** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitor_inv_apply (j : J) : (mapBifunctorLeftUnitor F X e p
 hp Y).inv j = e.inv.app (Y j) ≫ (F.map (singleObjApplyIso (0 : I) X).inv).app (
Y j) ≫ ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j)
参数：j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapBifunctorLeftUnitor_inv_apply (j : J) :
    (mapBifunctorLeftUnitor F X e p hp Y).inv j =
      e.inv.app (Y j) ≫ (F.map (singleObjApplyIso (0 : I) X).inv).app (Y j) ≫
      ιMapBifunctorMapObj F p ((single₀ I).obj X) Y 0 j j (hp j) := rfl

variable {Y Y'}

@[reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitor_inv_naturality** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitor_inv_naturality : φ ≫ (mapBifunctorLeftUnitor F X e 
p hp Y').inv = (mapBifunctorLeftUnitor F X e p hp Y).inv ≫ mapBifunctorMapMap F 
p (𝟙 _) φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorLeftUnitor_inv_apply`：mapBifunct
orLeftUnitor_inv_apply (j : J) : (mapBifunctorLeftUnitor F X e p hp Y).inv j = e
.inv.app (Y j) ≫ (F.map (singleObjApplyIso (0 : I)…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.ι_mapBifunctorMapMap`：ι_mapBifunctorMapMap {
X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂) {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y
₂) [HasMap (((mapBifunctor F I J).obj …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma mapBifunctorLeftUnitor_inv_naturality :
    φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').inv =
      (mapBifunctorLeftUnitor F X e p hp Y).inv ≫ mapBifunctorMapMap F p (𝟙 _) φ := by
  ext j
  dsimp
  rw [mapBifunctorLeftUnitor_inv_apply, mapBifunctorLeftUnitor_inv_apply, assoc, assoc,
    ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id, NatTrans.id_app, id_comp, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc]
  rfl

@[reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorLeftUnitor_naturality** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorLeftUnitor_naturality : mapBifunctorMapMap F p (𝟙 _) φ ≫ (mapB
ifunctorLeftUnitor F X e p hp Y').hom = (mapBifunctorLeftUnitor F X e p hp Y).ho
m ≫ φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorLeftUnitor_inv_naturality`：mapBi
functorLeftUnitor_inv_naturality : φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').in
v = (mapBifunctorLeftUnitor F X e p hp Y).inv ≫ mapBifu…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapBifunctorLeftUnitor_naturality :
    mapBifunctorMapMap F p (𝟙 _) φ ≫ (mapBifunctorLeftUnitor F X e p hp Y').hom =
      (mapBifunctorLeftUnitor F X e p hp Y).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e p hp Y').inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorLeftUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end LeftUnitor

section RightUnitor

variable {C D I J : Type*} [Category* C] [Category* D]
  [Zero I] [DecidableEq I] [HasInitial C]
  (F : D ⥤ C ⥤ D) (Y : C) (e : F.flip.obj Y ≅ 𝟭 D)
  [∀ (X : D), PreservesColimit (Functor.empty.{0} C) (F.obj X)]
  (p : J × I → J)
  (hp : ∀ (j : J), p ⟨j, 0⟩ = j) (X X' : GradedObject J D) (φ : X ⟶ X')

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj X ≅ 𝟭 D` and `X : GradedObject J D`,
this is the isomorphism `((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ Y a.2`
when `a : J × I` is such that `a.2 = 0`. -/
@[simps!]
/-
**CategoryTheory.GradedObject.mapBifunctorObjObjSingle** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GradedObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj X ≅ 𝟭 D` and `X : GradedObject J
 D`,
this is the isomorphism `((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a 
≅ Y a.2`
when `a : J × I` is such that `a.2 = 0`.
-/
noncomputable def mapBifunctorObjObjSingle₀Iso (a : J × I) (ha : a.2 = 0) :
    ((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a ≅ X a.1 :=
  Functor.mapIso _ (singleObjApplyIsoOfEq _ Y _ ha) ≪≫ e.app (X a.1)

/-- Given `F : D ⥤ C ⥤ D`, `Y : C` and `X : GradedObject J D`,
`((mapBifunctor F J I).obj X).obj ((single₀ I).obj X) a` is an initial when `a : J × I`
is such that `a.2 ≠ 0`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorObjObjSingle** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GradedObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : D ⥤ C ⥤ D`, `Y : C` and `X : GradedObject J D`,
`((mapBifunctor F J I).obj X).obj ((single₀ I).obj X) a` is an initial when `a :
 J × I`
is such that `a.2 ≠ 0`.
-/
noncomputable def mapBifunctorObjObjSingle₀IsInitial (a : J × I) (ha : a.2 ≠ 0) :
    IsInitial (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y) a) :=
  IsInitial.isInitialObj (F.obj (X a.1)) _ (isInitialSingleObjApply _ _ _ ha)

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D` and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`, see `mapBifunctorRightUnitor`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitorCofan** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitorCofan (hp : forall (j : J), p ⟨j, 0⟩ = j) (X) (j : 
J) : (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)).CofanMapObjFun p j
参数：hp : forall (j : J), p ⟨j, 0⟩ = j；X；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D`
 and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the (colimit) cofan which shall be used to construct the isomorphism
`mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`, see `mapBifunctorRightUnitor
`.
-/
noncomputable def mapBifunctorRightUnitorCofan (hp : ∀ (j : J), p ⟨j, 0⟩ = j) (X) (j : J) :
    (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)).CofanMapObjFun p j :=
  CofanMapObjFun.mk _ _ _ (X j) (fun a ha =>
    if ha : a.2 = 0 then
      (mapBifunctorObjObjSingle₀Iso F Y e X a ha).hom ≫ eqToHom (by aesop)
    else
      (mapBifunctorObjObjSingle₀IsInitial F Y X a ha).to _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitorCofan_inj** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitorCofan_inj (j : J) : (mapBifunctorRightUnitorCofan F
 Y e p hp X j).inj ⟨⟨j, 0⟩, hp j⟩ = (F.obj (X j)).map (singleObjApplyIso (0 : I)
 Y).hom ≫ e.hom.app (X j)
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mapBifunctorRightUnitorCofan_inj (j : J) :
    (mapBifunctorRightUnitorCofan F Y e p hp X j).inj ⟨⟨j, 0⟩, hp j⟩ =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  simp [mapBifunctorRightUnitorCofan]

set_option backward.isDefEq.respectTransparency false in
/-- The cofan `mapBifunctorRightUnitorCofan F Y e p hp X j` is a colimit. -/
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitorCofanIsColimit** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitorCofanIsColimit (j : J) : IsColimit (mapBifunctorRig
htUnitorCofan F Y e p hp X j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan `mapBifunctorRightUnitorCofan F Y e p hp X j` is a colimit.
-/
noncomputable def mapBifunctorRightUnitorCofanIsColimit (j : J) :
    IsColimit (mapBifunctorRightUnitorCofan F Y e p hp X j) :=
  Cofan.IsColimit.mk _
    (fun s => e.inv.app (X j) ≫
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫ s.inj ⟨⟨j, 0⟩, hp j⟩)
    (fun s => by
      rintro ⟨⟨j', i⟩, h⟩
      by_cases hi : i = 0
      · subst hi
        simp only [Set.mem_preimage, hp, Set.mem_singleton_iff] at h
        subst h
        rw [mapBifunctorRightUnitorCofan_inj, assoc, Iso.hom_inv_id_app_assoc,
          ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, id_comp]
      · apply IsInitial.hom_ext
        exact mapBifunctorObjObjSingle₀IsInitial _ _ _ _ hi)
    (fun s m hm => by
      rw [← hm ⟨⟨j, 0⟩, hp j⟩, mapBifunctorRightUnitorCofan_inj, assoc, ← Functor.map_comp_assoc,
        Iso.inv_hom_id, Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc])

include e hp in
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitor_hasMap** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitor_hasMap : HasMap (((mapBifunctor F J I).obj X).obj 
((single₀ I).obj Y)) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.CofanMapObjFun.hasMap`：hasMap (c : forall j,
 CofanMapObjFun X p j) (hc : forall j, IsColimit (c j)) : X.HasMap p
-/
lemma mapBifunctorRightUnitor_hasMap :
    HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p :=
  CofanMapObjFun.hasMap _ _ _ (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X)

variable [HasMap (((mapBifunctor F J I).obj X).obj ((single₀ I).obj Y)) p]
  [HasMap (((mapBifunctor F J I).obj X').obj ((single₀ I).obj Y)) p]

/-- Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D` and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the right unitor isomorphism `mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X`. -/
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitor** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitor : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : D ⥤ C ⥤ D`, `Y : C`, `e : F.flip.obj Y ≅ 𝟭 D`, `X : GradedObject J D`
 and
`p : J × I → J` such that `p ⟨j, 0⟩ = j` for all `j`,
this is the right unitor isomorphism `mapBifunctorMapObj F p X ((single₀ I).obj 
Y) ≅ X`.
-/
noncomputable def mapBifunctorRightUnitor : mapBifunctorMapObj F p X ((single₀ I).obj Y) ≅ X :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (mapBifunctorRightUnitorCofanIsColimit F Y e p hp X j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapBifunctorRightUnitor_hom_apply (j : J) :
    ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) ≫
        (mapBifunctorRightUnitor F Y e p hp X).hom j =
      (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).hom ≫ e.hom.app (X j) := by
  dsimp [mapBifunctorRightUnitor]
  erw [CofanMapObjFun.ιMapObj_iso_inv]
  rw [mapBifunctorRightUnitorCofan_inj]
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitor_inv_apply** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitor_inv_apply (j : J) : (mapBifunctorRightUnitor F Y e
 p hp X).inv j = e.inv.app (X j) ≫ (F.obj (X j)).map (singleObjApplyIso (0 : I) 
Y).inv ≫ ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j)
参数：j : J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapBifunctorRightUnitor_inv_apply (j : J) :
    (mapBifunctorRightUnitor F Y e p hp X).inv j =
      e.inv.app (X j) ≫ (F.obj (X j)).map (singleObjApplyIso (0 : I) Y).inv ≫
        ιMapBifunctorMapObj F p X ((single₀ I).obj Y) j 0 j (hp j) := rfl

variable {Y}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitor_inv_naturality** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitor_inv_naturality : φ ≫ (mapBifunctorRightUnitor F Y 
e p hp X').inv = (mapBifunctorRightUnitor F Y e p hp X).inv ≫ mapBifunctorMapMap
 F p φ (𝟙 _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorRightUnitor_inv_apply`：mapBifunc
torRightUnitor_inv_apply (j : J) : (mapBifunctorRightUnitor F Y e p hp X).inv j 
= e.inv.app (X j) ≫ (F.obj (X j)).map (singleObjApp…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.ι_mapBifunctorMapMap`：ι_mapBifunctorMapMap {
X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂) {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y
₂) [HasMap (((mapBifunctor F I J).obj …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapBifunctorRightUnitor_inv_naturality :
    φ ≫ (mapBifunctorRightUnitor F Y e p hp X').inv =
      (mapBifunctorRightUnitor F Y e p hp X).inv ≫ mapBifunctorMapMap F p φ (𝟙 _) := by
  ext j
  dsimp
  rw [mapBifunctorRightUnitor_inv_apply, mapBifunctorRightUnitor_inv_apply, assoc, assoc,
    ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id, id_comp, NatTrans.naturality_assoc]
  erw [← NatTrans.naturality_assoc e.inv]
  rfl

@[reassoc]
/-
**CategoryTheory.GradedObject.mapBifunctorRightUnitor_naturality** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.GradedObject`。
形式化陈述：mapBifunctorRightUnitor_naturality : mapBifunctorMapMap F p φ (𝟙 _) ≫ (map
BifunctorRightUnitor F Y e p hp X').hom = (mapBifunctorRightUnitor F Y e p hp X)
.hom ≫ φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorRightUnitor_inv_naturality`：mapB
ifunctorRightUnitor_inv_naturality : φ ≫ (mapBifunctorRightUnitor F Y e p hp X')
.inv = (mapBifunctorRightUnitor F Y e p hp X).inv ≫ mapB…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma mapBifunctorRightUnitor_naturality :
    mapBifunctorMapMap F p φ (𝟙 _) ≫ (mapBifunctorRightUnitor F Y e p hp X').hom =
      (mapBifunctorRightUnitor F Y e p hp X).hom ≫ φ := by
  rw [← cancel_mono (mapBifunctorRightUnitor F Y e p hp X').inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorRightUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end RightUnitor

section

variable {I₁ I₂ I₃ J : Type*} [Zero I₂]

/-- Given two maps `r : I₁ × I₂ × I₃ → J` and `π : I₁ × I₃ → J`, this structure is the
input in the formulation of the triangle equality `mapBifunctor_triangle` which
relates the left and right unitor and the associator for `GradedObject.mapBifunctor`. -/
/-
**CategoryTheory.GradedObject.TriangleIndexData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.GradedObject`。
形式化陈述：{I₁ : Type u_1} →   {I₂ : Type u_2} →     {I₃ : Type u_3} → {J : Type u_4}
 → [Zero I₂] → (I₁ × I₂ × I₃ → J) → (I₁ × I₃ → J) → Type (max (max u_1 u_2) u_3)
参数：I₁ × I₂ × I₃ → J；I₁ × I₃ → J；max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two maps `r : I₁ × I₂ × I₃ → J` and `π : I₁ × I₃ → J`, this structure is t
he
input in the formulation of the triangle equality `mapBifunctor_triangle` which
relates the left and right unitor and the associator for `GradedObject.mapBifunc
tor`.
-/
structure TriangleIndexData (r : I₁ × I₂ × I₃ → J) (π : I₁ × I₃ → J) where
  /-- a map `I₁ × I₂ → I₁` -/
  p₁₂ : I₁ × I₂ → I₁
  hp₁₂ (i : I₁ × I₂ × I₃) : π ⟨p₁₂ ⟨i.1, i.2.1⟩, i.2.2⟩ = r i
  /-- a map `I₂ × I₃ → I₃` -/
  p₂₃ : I₂ × I₃ → I₃
  hp₂₃ (i : I₁ × I₂ × I₃) : π ⟨i.1, p₂₃ i.2⟩ = r i
  h₁ (i₁ : I₁) : p₁₂ (i₁, 0) = i₁
  h₃ (i₃ : I₃) : p₂₃ (0, i₃) = i₃

variable {r : I₁ × I₂ × I₃ → J} {π : I₁ × I₃ → J} (τ : TriangleIndexData r π)
include τ

namespace TriangleIndexData

attribute [simp] h₁ h₃

/-
**CategoryTheory.GradedObject.TriangleIndexData.r_zero** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GradedObject.TriangleIndexData`。
形式化陈述：r_zero (i₁ : I₁) (i₃ : I₃) : r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩
参数：i₁ : I₁；i₃ : I₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.hp₂₃`：∀ {I₁ : Type u_1} {I
₂ : Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ 
→ J}   {π : I₁ × I₃ → J} (self : Categor…
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.h₃`：∀ {I₁ : Type u_1} {I₂ 
: Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ → 
J}   {π : I₁ × I₃ → J} (self : Categor…
-/
lemma r_zero (i₁ : I₁) (i₃ : I₃) : r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩ := by
  rw [← τ.hp₂₃, τ.h₃ i₃]

/-- The `BifunctorComp₁₂IndexData r` attached to a `TriangleIndexData r π`. -/
@[reducible]
/-
**CategoryTheory.GradedObject.TriangleIndexData.** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GradedObject.TriangleIndexData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BifunctorComp₁₂IndexData r` attached to a `TriangleIndexData r π`.
-/
def ρ₁₂ : BifunctorComp₁₂IndexData r where
  I₁₂ := I₁
  p := τ.p₁₂
  q := π
  hpq := τ.hp₁₂

/-- The `BifunctorComp₂₃IndexData r` attached to a `TriangleIndexData r π`. -/
@[reducible]
/-
**CategoryTheory.GradedObject.TriangleIndexData.** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GradedObject.TriangleIndexData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BifunctorComp₂₃IndexData r` attached to a `TriangleIndexData r π`.
-/
def ρ₂₃ : BifunctorComp₂₃IndexData r where
  I₂₃ := I₃
  p := τ.p₂₃
  q := π
  hpq := τ.hp₂₃

end TriangleIndexData

end

section Triangle

variable {C₁ C₂ C₃ D I₁ I₂ I₃ J : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* D]
  [Zero I₂] [DecidableEq I₂] [HasInitial C₂]
  {F₁ : C₁ ⥤ C₂ ⥤ C₁} {F₂ : C₂ ⥤ C₃ ⥤ C₃} {G : C₁ ⥤ C₃ ⥤ D}
  (associator : bifunctorComp₁₂ F₁ G ≅ bifunctorComp₂₃ G F₂)
  (X₂ : C₂) (e₁ : F₁.flip.obj X₂ ≅ 𝟭 C₁) (e₂ : F₂.obj X₂ ≅ 𝟭 C₃)
  [∀ (X₁ : C₁), PreservesColimit (Functor.empty.{0} C₂) (F₁.obj X₁)]
  [∀ (X₃ : C₃), PreservesColimit (Functor.empty.{0} C₂) (F₂.flip.obj X₃)]
  {r : I₁ × I₂ × I₃ → J} {π : I₁ × I₃ → J}
  (τ : TriangleIndexData r π)
  (X₁ : GradedObject I₁ C₁) (X₃ : GradedObject I₃ C₃)
  [HasMap (((mapBifunctor F₁ I₁ I₂).obj X₁).obj ((single₀ I₂).obj X₂)) τ.p₁₂]
  [HasMap (((mapBifunctor G I₁ I₃).obj
    (mapBifunctorMapObj F₁ τ.p₁₂ X₁ ((single₀ I₂).obj X₂))).obj X₃) π]
  [HasMap (((mapBifunctor F₂ I₂ I₃).obj ((single₀ I₂).obj X₂)).obj X₃) τ.p₂₃]
  [HasMap (((mapBifunctor G I₁ I₃).obj X₁).obj
      (mapBifunctorMapObj F₂ τ.p₂₃ ((single₀ I₂).obj X₂) X₃)) π]
  [HasGoodTrifunctor₁₂Obj F₁ G τ.ρ₁₂ X₁ ((single₀ I₂).obj X₂) X₃]
  [HasGoodTrifunctor₂₃Obj G F₂ τ.ρ₂₃ X₁ ((single₀ I₂).obj X₂) X₃]
  [HasMap (((mapBifunctor G I₁ I₃).obj X₁).obj X₃) π]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GradedObject.mapBifunctor_triangle** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GradedObject`。
形式化陈述：mapBifunctor_triangle (triangle : forall (X₁ : C₁) (X₃ : C₃), ((associator
.hom.app X₁).app X₂).app X₃ ≫ (G.obj X₁).map (e₂.hom.app X₃) = (G.map (e₁.hom.ap
p X₁)).app X₃) : (mapBifunctorAssociator associator τ.ρ₁₂ τ.ρ₂₃ X₁ ((single₀ I₂)
.obj X₂) X₃).hom ≫ mapBifunctorMapMap G π (𝟙 X₁) (mapBifunctorLeftUnitor F₂ X₂ e
₂ τ.p₂₃ τ.h₃ X₃).hom = mapBifunctorMapMap G π (mapBifunctorRightUnitor F₁ X₂ e₁ 
τ.p₁₂ τ.h₁ X₁).hom (𝟙 X₃)
参数：triangle : forall (X₁ : C₁) (X₃ : C₃), ((associator.hom.app X₁).app X₂).app X
₃ ≫ (G.obj X₁).map (e₂.hom.app X₃) = (G.map (e₁.hom.app X₁)).app X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.h₃`：∀ {I₁ : Type u_1} {I₂ 
: Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ → 
J}   {π : I₁ × I₃ → J} (self : Categor…
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.h₁`：∀ {I₁ : Type u_1} {I₂ 
: Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ → 
J}   {π : I₁ × I₃ → J} (self : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.GradedObject.instIsIsoMapBifunctorMapMap`：∀ {C₁ : Type u_
1} {C₂ : Type u_2} {C₃ : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁
]   [inst_1 : CategoryTheory.Category.{v_2, u…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorMapObj_ext`：mapBifunctorMapObj_e
xt {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K} [HasMap (((m
apBifunctor F I J).obj X).obj Y) p] {f g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GradedObject.ι_mapBifunctorMapMap_assoc`：∀ {C₁ : Type u_1
} {C₂ : Type u_2} {C₃ : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₁]
   [inst_1 : CategoryTheory.Category.{v_2, u…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.ι_mapBifunctorMapMap`：ι_mapBifunctorMapMap {
X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂) {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y
₂) [HasMap (((mapBifunctor F I J).obj …
· 使用引理 `CategoryTheory.GradedObject.TriangleIndexData.r_zero`：r_zero (i₁ : I₁) (
i₃ : I₃) : r ⟨i₁, 0, i₃⟩ = π ⟨i₁, i₃⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GradedObject.ιMapBifunctor₁₂BifunctorMapObj_eq_assoc`：∀ {
C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {C₄ : Type u_4} {C₁₂ : Type u_5} 
  [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1 …
· 使用定理 `CategoryTheory.GradedObject.ι_mapBifunctorAssociator_hom_assoc`：∀ {C₁ : 
Type u_1} {C₂ : Type u_2} {C₁₂ : Type u_3} {C₂₃ : Type u_4} {C₃ : Type u_5} {C₄ 
: Type u_6}   [inst : CategoryTheory.Category.{v_1, …
· 使用定理 `CategoryTheory.GradedObject.ιMapBifunctorBifunctor₂₃MapObj_eq_assoc`：∀ {
C₁ : Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {C₄ : Type u_4} {C₂₃ : Type u_6} 
  [inst : CategoryTheory.Category.{v_1, u_1} C₁] [inst_1 …
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.comp_app_assoc`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F G H : CategoryT…
（共 33 条，此处仅展示前 30 条）
-/
lemma mapBifunctor_triangle
    (triangle : ∀ (X₁ : C₁) (X₃ : C₃), ((associator.hom.app X₁).app X₂).app X₃ ≫
    (G.obj X₁).map (e₂.hom.app X₃) = (G.map (e₁.hom.app X₁)).app X₃) :
    (mapBifunctorAssociator associator τ.ρ₁₂ τ.ρ₂₃ X₁ ((single₀ I₂).obj X₂) X₃).hom ≫
    mapBifunctorMapMap G π (𝟙 X₁) (mapBifunctorLeftUnitor F₂ X₂ e₂ τ.p₂₃ τ.h₃ X₃).hom =
      mapBifunctorMapMap G π (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).hom (𝟙 X₃) := by
  rw [← cancel_epi ((mapBifunctorMapMap G π
    (mapBifunctorRightUnitor F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁).inv (𝟙 X₃)))]
  ext j i₁ i₃ hj
  simp only [categoryOfGradedObjects_comp, ι_mapBifunctorMapMap_assoc,
    mapBifunctorRightUnitor_inv_apply, Functor.id_obj, Functor.map_comp,
    NatTrans.comp_app, categoryOfGradedObjects_id, Functor.map_id, id_comp, assoc,
    ι_mapBifunctorMapMap]
  congr 2
  rw [← ιMapBifunctor₁₂BifunctorMapObj_eq_assoc F₁ G τ.ρ₁₂ _ _ _ i₁ 0 i₃ j
    (by rw [τ.r_zero, hj]) i₁ (by simp), ι_mapBifunctorAssociator_hom_assoc,
    ιMapBifunctorBifunctor₂₃MapObj_eq_assoc G F₂ τ.ρ₂₃ _ _ _ i₁ 0 i₃ j
    (by rw [τ.r_zero, hj]) i₃ (by simp), ι_mapBifunctorMapMap]
  dsimp
  rw [Functor.map_id, NatTrans.id_app, id_comp,
    ← Functor.map_comp_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    ι_mapBifunctorLeftUnitor_hom_apply F₂ X₂ e₂ τ.p₂₃ τ.h₃ X₃ i₃,
    ι_mapBifunctorRightUnitor_hom_apply F₁ X₂ e₁ τ.p₁₂ τ.h₁ X₁ i₁]
  dsimp
  simp only [Functor.map_comp, NatTrans.comp_app, ← triangle (X₁ i₁) (X₃ i₃), ← assoc]
  congr 2
  symm
  apply NatTrans.naturality_app (associator.hom.app (X₁ i₁))

end Triangle

end GradedObject

end CategoryTheory

