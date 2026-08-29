/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

namespace NatTrans

open Functor.LaxMonoidal

/--
Definition of `IsMonoidal` / `IsMonoidal` 的定义

English:
class IsMonoidal
  parameters: : Prop where
  axioms and operations (2):
    - unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂  [default: by cat_disch]
    - tensor((X Y : C)) : μ F₁ _ _ ≫ τ.app (X otimes Y) = (τ.app X otimesₘ τ.app Y) ≫ μ F₂ _ _  [default: by cat_disch]

中文:
类 IsMonoidal
  参数: : 命题 where
  公理与运算 (2 个):
    - unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂  [默认: by cat_disch]
    - tensor((X Y : C)) : μ F₁ _ _ ≫ τ.app (X otimes Y) = (τ.app X otimesₘ τ.app Y) ≫ μ F₂ _ _  [默认: by cat_disch]

Depends on / 依赖: cat_disch, otimes, tensor
-/
class IsMonoidal : Prop where
  unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂ := by cat_disch
  tensor (X Y : C) : μ F₁ _ _ ≫ τ.app (X otimes Y) = (τ.app X otimesₘ τ.app Y) ≫ μ F₂ _ _ := by cat_disch

namespace IsMonoidal

attribute [reassoc (attr := simp)] unit tensor

/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : IsMonoidal (𝟙 F₁) where

中文:
实例 id
  签名: : IsMonoidal (𝟙 F₁) where
-/
instance id : IsMonoidal (𝟙 F₁) where

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ']

中文:
实例 comp
  签名: (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ']
-/
instance comp (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ'] :
    IsMonoidal (τ ≫ τ') where

set_option backward.defeqAttrib.useBackward true in
/--
Instance `hcomp` / 实例 `hcomp`

English:
instance hcomp
  signature: {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
  body: by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, ← tensorHom_comp_tensorHom, μ_natural_assoc]
    simp only [← map_comp, tensor]

中文:
实例 hcomp
  签名: {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
  定义体: by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, ← tensorHom_comp_tensorHom, μ_natural_assoc]
    simp only [← map_comp, tensor]

Depends on / 依赖: comp_obj, hcomp_app, map_comp, naturality_assoc, tensor, tensorHom_comp_tensorHom, tensor_assoc, unit_assoc
-/
instance hcomp {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
    [IsMonoidal τ] [IsMonoidal τ'] : IsMonoidal (τ ◫ τ') where
  unit := by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, ← tensorHom_comp_tensorHom, μ_natural_assoc]
    simp only [← map_comp, tensor]

/--
Instance `whiskerRight` / 实例 `whiskerRight`

English:
instance whiskerRight
  signature: {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ]
  body: by
  rw [← Functor.hcomp_id]
  infer_instance

中文:
实例 whiskerRight
  签名: {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ]
  定义体: by
  rw [← Functor.hcomp_id]
  infer_instance

Depends on / 依赖: Functor, Functor.hcomp_id, hcomp_id, infer_instance
-/
instance whiskerRight {G₁ : D ⥤ E} [G₁.LaxMonoidal] [IsMonoidal τ] :
    IsMonoidal (Functor.whiskerRight τ G₁) := by
  rw [← Functor.hcomp_id]
  infer_instance

/--
Instance `whiskerLeft` / 实例 `whiskerLeft`

English:
instance whiskerLeft
  signature: {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
  body: by
  rw [← Functor.id_hcomp]
  infer_instance

中文:
实例 whiskerLeft
  签名: {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
  定义体: by
  rw [← Functor.id_hcomp]
  infer_instance

Depends on / 依赖: Functor, Functor.id_hcomp, id_hcomp, infer_instance
-/
instance whiskerLeft {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal]
    (τ' : G₁ ⟶ G₂) [IsMonoidal τ'] :
    IsMonoidal (Functor.whiskerLeft F₁ τ') := by
  rw [← Functor.id_hcomp]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.leftUnitor.hom where

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.rightUnitor.hom where

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] :
    NatTrans.IsMonoidal (Functor.associator F G H).hom where
  unit := by
    simp only [comp_obj, comp_ε, assoc, Functor.map_comp, associator_hom_app, comp_id,
      Functor.comp_map]
  tensor X Y := by
    simp only [comp_obj, comp_μ, associator_hom_app, Functor.comp_map, map_comp,
      comp_id, tensorHom_id, id_whiskerRight, assoc, id_comp]

end IsMonoidal

set_option backward.isDefEq.respectTransparency false in
instance {F G : C ⥤ D} {H K : C ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
    [F.LaxMonoidal] [G.LaxMonoidal] [IsMonoidal α]
    [H.LaxMonoidal] [K.LaxMonoidal] [IsMonoidal β] :
    IsMonoidal (NatTrans.prod' α β) where
  unit := by
    ext
    · rw [prod_comp_fst, prod'_ε_fst, prod'_ε_fst, prod'_app_fst, IsMonoidal.unit]
    · rw [prod_comp_snd, prod'_ε_snd, prod'_ε_snd, prod'_app_snd, IsMonoidal.unit]
  tensor X Y := by
    ext
    · simp only [prod_comp_fst, prod'_μ_fst, prod'_app_fst,
        prodMonoidal_tensorHom, IsMonoidal.tensor]
    · simp only [prod_comp_snd, prod'_μ_snd, prod'_app_snd,
        prodMonoidal_tensorHom, IsMonoidal.tensor]

end NatTrans

namespace Iso

variable (e : F₁ ≅ F₂) [NatTrans.IsMonoidal e.hom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal e.inv
  body: by rw [← NatTrans.IsMonoidal.unit (τ := e.hom), assoc, hom_inv_id_app, comp_id]
  tensor X Y := by
    rw [← cancel_mono (e.hom.app (X otimes Y))]; rw [assoc]; rw [assoc]; rw [inv_hom_id_app]; rw [comp_id]; rw [NatTrans.IsMonoidal.tensor]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [in

中文:
实例 :
  签名: 自然数Trans.IsMonoidal e.inv
  定义体: by rw [← NatTrans.IsMonoidal.unit (τ := e.hom), assoc, hom_inv_id_app, comp_id]
  tensor X Y := by
    rw [← cancel_mono (e.hom.app (X otimes Y))]; rw [assoc]; rw [assoc]; rw [inv_hom_id_app]; rw [comp_id]; rw [NatTrans.IsMonoidal.tensor]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [in

Depends on / 依赖: IsMonoidal, MonoidalCategory, MonoidalCategory.tensorHom_comp_tensorHom_assoc, NatTrans, NatTrans.IsMonoidal.tensor, NatTrans.IsMonoidal.unit, cancel_mono, comp_id, e.hom, e.hom.app, hom_inv_id_app, id_comp, id_whiskerRight, inv_hom_id_app, otimes, tensor, tensorHom_comp_tensorHom_assoc, tensorHom_id
-/
instance : NatTrans.IsMonoidal e.inv where
  unit := by rw [← NatTrans.IsMonoidal.unit (τ := e.hom), assoc, hom_inv_id_app, comp_id]
  tensor X Y := by
    rw [← cancel_mono (e.hom.app (X otimes Y))]; rw [assoc]; rw [assoc]; rw [inv_hom_id_app]; rw [comp_id]; rw [NatTrans.IsMonoidal.tensor]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [inv_hom_id_app]; rw [inv_hom_id_app]; rw [tensorHom_id]; rw [id_whiskerRight]; rw [id_comp]

end Iso

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace IsMonoidal

variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal adj.unit
  body: by
    dsimp
    rw [id_comp]; rw [← unit_app_unit_comp_map_η adj]; rw [assoc]; rw [Monoidal.map_η_ε]
    dsimp
    rw [comp_id]
  tensor X Y := by
    dsimp
    rw [← unit_app_tensor_comp_map_δ_assoc]; rw [id_comp]; rw [Monoidal.map_δ_μ]; rw [comp_id]

中文:
实例 :
  签名: 自然数Trans.IsMonoidal adj.unit
  定义体: by
    dsimp
    rw [id_comp]; rw [← unit_app_unit_comp_map_η adj]; rw [assoc]; rw [Monoidal.map_η_ε]
    dsimp
    rw [comp_id]
  tensor X Y := by
    dsimp
    rw [← unit_app_tensor_comp_map_δ_assoc]; rw [id_comp]; rw [Monoidal.map_δ_μ]; rw [comp_id]

Depends on / 依赖: Monoidal, Monoidal.map_, comp_id, id_comp, tensor
-/
instance : NatTrans.IsMonoidal adj.unit where
  unit := by
    dsimp
    rw [id_comp]; rw [← unit_app_unit_comp_map_η adj]; rw [assoc]; rw [Monoidal.map_η_ε]
    dsimp
    rw [comp_id]
  tensor X Y := by
    dsimp
    rw [← unit_app_tensor_comp_map_δ_assoc]; rw [id_comp]; rw [Monoidal.map_δ_μ]; rw [comp_id]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal adj.counit
  body: by
    dsimp
    rw [assoc]; rw [map_ε_comp_counit_app_unit adj]; rw [ε_η]
  tensor X Y := by
    dsimp
    rw [assoc]; rw [map_μ_comp_counit_app_tensor]; rw [μ_δ_assoc]; rw [comp_id]

中文:
实例 :
  签名: 自然数Trans.IsMonoidal adj.counit
  定义体: by
    dsimp
    rw [assoc]; rw [map_ε_comp_counit_app_unit adj]; rw [ε_η]
  tensor X Y := by
    dsimp
    rw [assoc]; rw [map_μ_comp_counit_app_tensor]; rw [μ_δ_assoc]; rw [comp_id]

Depends on / 依赖: comp_id, tensor
-/
instance : NatTrans.IsMonoidal adj.counit where
  unit := by
    dsimp
    rw [assoc]; rw [map_ε_comp_counit_app_unit adj]; rw [ε_η]
  tensor X Y := by
    dsimp
    rw [assoc]; rw [map_μ_comp_counit_app_tensor]; rw [μ_δ_assoc]; rw [comp_id]

end IsMonoidal

namespace Equivalence

variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal e.unit
  body: inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.unit)

中文:
实例 :
  签名: 自然数Trans.IsMonoidal e.unit
  定义体: inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.unit)

Depends on / 依赖: IsMonoidal, NatTrans, NatTrans.IsMonoidal, e.toAdjunction.unit, toAdjunction
-/
instance : NatTrans.IsMonoidal e.unit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.unit)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal e.counit
  body: inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.counit)

中文:
实例 :
  签名: 自然数Trans.IsMonoidal e.counit
  定义体: inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.counit)

Depends on / 依赖: IsMonoidal, NatTrans, NatTrans.IsMonoidal, counit, e.toAdjunction.counit, toAdjunction
-/
instance : NatTrans.IsMonoidal e.counit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.counit)

end Equivalence

end Adjunction

namespace LaxMonoidalFunctor

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (F G : LaxMonoidalFunctor C D)
  axioms and operations (2):
    - hom : F.toFunctor ⟶ G.toFunctor
    - isMonoidal : NatTrans.IsMonoidal hom  [default: by infer_instance]

中文:
结构 Hom
  参数: (F G : LaxMonoidalFunctor C D)
  公理与运算 (2 个):
    - hom : F.toFunctor ⟶ G.toFunctor
    - isMonoidal : 自然数Trans.IsMonoidal hom  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure Hom (F G : LaxMonoidalFunctor C D) where
  /-- the natural transformation between the underlying functors -/
  hom : F.toFunctor ⟶ G.toFunctor
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (LaxMonoidalFunctor C D)
  body: Hom
  comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[simp]

中文:
实例 :
  签名: Category (LaxMonoidalFunctor C D)
  定义体: Hom
  comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[simp]
-/
instance : Category (LaxMonoidalFunctor C D) where
  Hom := Hom
  comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (F : LaxMonoidalFunctor C D)
  statement: Hom.hom (𝟙 F) = 𝟙 _
  proof: rfl

@[reassoc, simp]

中文:
引理 id_hom
  条件: (F : LaxMonoidalFunctor C D)
  结论: Hom.hom (𝟙 F) = 𝟙 _
  证明: rfl

@[reassoc, simp]
-/
lemma id_hom (F : LaxMonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 _ := rfl

@[reassoc, simp]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

@[ext]

中文:
引理 comp_hom
  条件: {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl

@[ext]
-/
lemma comp_hom {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom)
  statement: α = β
  proof: by
  cases α; cases β; subst h; rfl

中文:
引理 hom_ext
  条件: {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom)
  结论: α = β
  证明: by
  cases α; cases β; subst h; rfl

Depends on / 依赖: Subtype, Subtype.val
-/
lemma hom_ext {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β := by
  cases α; cases β; subst h; rfl

/-- Constructor for morphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f]
  body: ⟨f, inferInstance⟩

中文:
定义 homMk
  签名: {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [自然数Trans.IsMonoidal f]
  定义体: ⟨f, inferInstance⟩
-/
def homMk {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

/-- Constructor for isomorphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
  body: homMk e.hom
  inv := homMk e.inv

中文:
定义 isoMk
  签名: {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
  定义体: homMk e.hom
  inv := homMk e.inv

Depends on / 依赖: e.hom
-/
def isoMk {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

open Functor.LaxMonoidal

/-- Constructor for isomorphisms between lax monoidal functors. -/
@[simps!]
/--
Definition of `isoOfComponents` / `isoOfComponents` 的定义

English:
definition isoOfComponents
  signature: {F G : LaxMonoidalFunctor C D} (e : forall X, F.obj X ≅ G.obj X)
  body: @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

中文:
定义 isoOfComponents
  签名: {F G : LaxMonoidalFunctor C D} (e : 对任意 X, F.obj X ≅ G.obj X)
  定义体: @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

Depends on / 依赖: F.toFunctor, G.toFunctor, NatIso, NatIso.ofComponents, cat_disch, naturality, ofComponents, otimes, tensor, toFunctor
-/
def isoOfComponents {F G : LaxMonoidalFunctor C D} (e : forall X, F.obj X ≅ G.obj X)
    (naturality : forall {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : forall X Y, μ F.toFunctor X Y ≫ (e (X otimes Y)).hom =
      ((e X).hom otimesₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

end LaxMonoidalFunctor

namespace Functor.Monoidal

/--
lemma `natTransIsMonoidal_of_transport` / 引理 `natTransIsMonoidal_of_transport`

English:
lemma natTransIsMonoidal_of_transport
  given: {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G)
  proof: transport e
    e.hom.IsMonoidal := by
  let : G.Monoidal := transport e
  refine ⟨rfl, fun X Y => ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

中文:
引理 natTransIsMonoidal_of_transport
  条件: {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G)
  证明: transport e
    e.hom.IsMonoidal := by
  let : G.Monoidal := transport e
  refine ⟨rfl, fun X Y => ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

Depends on / 依赖: NatTrans, NatTrans.ext, Subtype, Subtype.ext, Subtype.val, congr_app, congr_arg, congr_hom, hom_ext, transport
-/
lemma natTransIsMonoidal_of_transport {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G) :
    letI : G.Monoidal := transport e
    e.hom.IsMonoidal := by
  let : G.Monoidal := transport e
  refine ⟨rfl, fun X Y => ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

end Functor.Monoidal

end CategoryTheory
