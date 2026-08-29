/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

## Implementation details

`Functor.Additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
@[stacks 00ZY]
/--
Definition of `Functor.Additive` / `Functor.Additive` 的定义

English:
class Functor.Additive
  parameters: {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  axioms and operations (1):
    - map_add : forall {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g  [default: by cat_disch]

中文:
类 函子.加性
  参数: {C D : 类型} [范畴* C] [范畴* D] [预加性 C] [预加性 D]
  公理与运算 (1 个):
    - map_add : 对任意 {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Functor.Additive {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) : Prop where
  /-- the addition of two morphisms is mapped to the sum of their images -/
  map_add : forall {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by cat_disch

section Preadditive

namespace Functor

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: {X Y : C} {f g : X ⟶ Y}
  statement: F.map (f + g) = F.map f + F.map g
  proof: Functor.Additive.map_add

中文:
定理 map_add
  条件: {X Y : C} {f g : X ⟶ Y}
  结论: F.map (f + g) = F.map f + F.map g
  证明: Functor.Additive.map_add

Depends on / 依赖: Additive, Functor, Functor.Additive.map_add, map_add
-/
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  Functor.Additive.map_add

/-- `F.mapAddHom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps!]
/--
Definition of `mapAddHom` / `mapAddHom` 的定义

English:
definition mapAddHom
  signature: {X Y : C}
  body: AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add

中文:
定义 mapAddHom
  签名: {X Y : C}
  定义体: AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, F.map, F.map_add, map_add
-/
def mapAddHom {X Y : C} : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun _ _ => F.map_add

/--
theorem `coe_mapAddHom` / 定理 `coe_mapAddHom`

English:
theorem coe_mapAddHom
  given: {X Y : C}
  statement: ⇑(F.mapAddHom : (X ⟶ Y) ->+ _) = F.map
  proof: rfl

中文:
定理 coe_mapAddHom
  条件: {X Y : C}
  结论: ⇑(F.mapAddHom : (X ⟶ Y) ->+ _) = F.map
  证明: rfl
-/
theorem coe_mapAddHom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) ->+ _) = F.map :=
  rfl

instance (priority := 100) preservesZeroMorphisms_of_additive : PreservesZeroMorphisms F where
  map_zero _ _ := F.mapAddHom.map_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Additive (𝟭 C)

中文:
实例 :
  签名: 加性 (𝟭 C)
-/
instance : Additive (𝟭 C) where

instance {E : Type*} [Category* E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] :
    Additive (F ⋙ G) where

instance {J : Type*} [Category* J] (j : J) : ((evaluation J C).obj j).Additive where

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: {X Y : C} {f : X ⟶ Y}
  statement: F.map (-f) = -F.map f
  proof: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]

中文:
定理 map_neg
  条件: {X Y : C} {f : X ⟶ Y}
  结论: F.map (-f) = -F.map f
  证明: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]

Depends on / 依赖: F.mapAddHom, F.obj, mapAddHom, map_neg
-/
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]
/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: {X Y : C} {f g : X ⟶ Y}
  statement: F.map (f - g) = F.map f - F.map g
  proof: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_sub _ _

中文:
定理 map_sub
  条件: {X Y : C} {f g : X ⟶ Y}
  结论: F.map (f - g) = F.map f - F.map g
  证明: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_sub _ _

Depends on / 依赖: F.mapAddHom, F.obj, mapAddHom, map_sub
-/
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_sub _ _

/--
theorem `map_nsmul` / 定理 `map_nsmul`

English:
theorem map_nsmul
  given: {X Y : C} {f : X ⟶ Y} {n : Nat}
  statement: F.map (n • f) = n • F.map f
  proof: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

中文:
定理 map_nsmul
  条件: {X Y : C} {f : X ⟶ Y} {n : 自然数}
  结论: F.map (n • f) = n • F.map f
  证明: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

Depends on / 依赖: F.mapAddHom, F.obj, mapAddHom, map_nsmul
-/
theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : Nat} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

-- You can alternatively just use `Functor.map_smul` here, with an explicit `(r : ℤ)` argument.
/--
theorem `map_zsmul` / 定理 `map_zsmul`

English:
theorem map_zsmul
  given: {X Y : C} {f : X ⟶ Y} {r : Int}
  statement: F.map (r • f) = r • F.map f
  proof: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α -> (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  map_sum F.mapAddHom f s

中文:
定理 map_zsmul
  条件: {X Y : C} {f : X ⟶ Y} {r : 整数}
  结论: F.map (r • f) = r • F.map f
  证明: (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α -> (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  map_sum F.mapAddHom f s

Depends on / 依赖: F.mapAddHom, F.obj, mapAddHom, map_zsmul
-/
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : Int} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) ->+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

@[simp]
nonrec theorem map_sum {X Y : C} {α : Type*} (f : α -> (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  map_sum F.mapAddHom f s

variable {F}

/--
lemma `additive_of_iso` / 引理 `additive_of_iso`

English:
lemma additive_of_iso
  given: {G : C ⥤ D} (e : F ≅ G)
  statement: G.Additive
  proof: by
  constructor
  intro X Y f g
  simp only [← NatIso.naturality_1 e (f + g), map_add, Preadditive.add_comp,
    NatTrans.naturality, Preadditive.comp_add, Iso.inv_hom_id_app_assoc]

omit [F.Additive] in

中文:
引理 additive_of_iso
  条件: {G : C ⥤ D} (e : F ≅ G)
  结论: G.加性
  证明: by
  constructor
  intro X Y f g
  simp only [← NatIso.naturality_1 e (f + g), map_add, Preadditive.add_comp,
    NatTrans.naturality, Preadditive.comp_add, Iso.inv_hom_id_app_assoc]

omit [F.Additive] in

Depends on / 依赖: Iso.inv_hom_id_app_assoc, NatIso, NatIso.naturality_1, NatTrans, NatTrans.naturality, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, comp_add, inv_hom_id_app_assoc, map_add, naturality, naturality_1
-/
lemma additive_of_iso {G : C ⥤ D} (e : F ≅ G) : G.Additive := by
  constructor
  intro X Y f g
  simp only [← NatIso.naturality_1 e (f + g), map_add, Preadditive.add_comp,
    NatTrans.naturality, Preadditive.comp_add, Iso.inv_hom_id_app_assoc]

omit [F.Additive] in
/--
lemma `additive_iff_of_iso` / 引理 `additive_iff_of_iso`

English:
lemma additive_iff_of_iso
  given: {G : C ⥤ D} (e : F ≅ G)
  statement: F.Additive ↔ G.Additive
  proof: ⟨fun _ => additive_of_iso e, fun _ => additive_of_iso e.symm⟩

中文:
引理 additive_iff_of_iso
  条件: {G : C ⥤ D} (e : F ≅ G)
  结论: F.加性 ↔ G.加性
  证明: ⟨fun _ => additive_of_iso e, fun _ => additive_of_iso e.symm⟩

Depends on / 依赖: additive_of_iso, e.symm
-/
lemma additive_iff_of_iso {G : C ⥤ D} (e : F ≅ G) : F.Additive ↔ G.Additive :=
  ⟨fun _ => additive_of_iso e, fun _ => additive_of_iso e.symm⟩

variable (F)

/--
lemma `additive_of_full_essSurj_comp` / 引理 `additive_of_full_essSurj_comp`

English:
lemma additive_of_full_essSurj_comp
  statement: [Full F] [EssSurj F] (G : D ⥤ E)
  proof: by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    obtain ⟨g', hg'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ g ≫
      (F.objObjPreimageIso Y).inv)
    simp only [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom),
      Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
    erw [← hf', ← hg', ← (F ⋙ G).map_add]
    dsimp
    rw [F.map_add]

中文:
引理 additive_of_full_essSurj_comp
  结论: [满 F] [本质满射 F] (G : D ⥤ E)
  证明: by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    obtain ⟨g', hg'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ g ≫
      (F.objObjPreimageIso Y).inv)
    simp only [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom),
      Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
    erw [← hf', ← hg', ← (F ⋙ G).map_add]
    dsimp
    rw [F.map_add]

Depends on / 依赖: F.map_add, F.map_surjective, F.objObjPreimageIso, Functor, Functor.map_comp, G.map, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, cancel_epi, cancel_mono, comp_add, map_add, map_comp, map_surjective, objObjPreimageIso
-/
lemma additive_of_full_essSurj_comp [Full F] [EssSurj F] (G : D ⥤ E)
    [(F ⋙ G).Additive] : G.Additive where
  map_add {X Y f g} := by
    obtain ⟨f', hf'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫
      (F.objObjPreimageIso Y).inv)
    obtain ⟨g', hg'⟩ := F.map_surjective ((F.objObjPreimageIso X).hom ≫ g ≫
      (F.objObjPreimageIso Y).inv)
    simp only [← cancel_mono (G.map (F.objObjPreimageIso Y).inv),
      ← cancel_epi (G.map (F.objObjPreimageIso X).hom),
      Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
    erw [← hf', ← hg', ← (F ⋙ G).map_add]
    dsimp
    rw [F.map_add]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `additive_of_comp_faithful` / 引理 `additive_of_comp_faithful`

English:
lemma additive_of_comp_faithful
  proof: G.map_injective (by
    rw [← Functor.comp_map]; rw [G.map_add]; rw [(F ⋙ G).map_add]; rw [Functor.comp_map]; rw [Functor.comp_map])

中文:
引理 additive_of_comp_faithful
  证明: G.map_injective (by
    rw [← Functor.comp_map]; rw [G.map_add]; rw [(F ⋙ G).map_add]; rw [Functor.comp_map]; rw [Functor.comp_map])

Depends on / 依赖: Functor, Functor.comp_map, G.map_add, G.map_injective, comp_map, map_add, map_injective
-/
lemma additive_of_comp_faithful
    (F : C ⥤ D) (G : D ⥤ E) [G.Additive] [(F ⋙ G).Additive] [Faithful G] :
    F.Additive where
  map_add {_ _ f₁ f₂} := G.map_injective (by
    rw [← Functor.comp_map]; rw [G.map_add]; rw [(F ⋙ G).map_add]; rw [Functor.comp_map]; rw [Functor.comp_map])

open ZeroObject Limits in
include F in
/--
lemma `hasZeroObject_of_additive` / 引理 `hasZeroObject_of_additive`

English:
lemma hasZeroObject_of_additive
  given: [HasZeroObject C]
  proof: ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩

中文:
引理 hasZeroObject_of_additive
  条件: [有ZeroObject C]
  证明: ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩

Depends on / 依赖: F.map_id, F.map_zero, F.obj, IsZero, IsZero.iff_id_eq_zero, id_zero, iff_id_eq_zero, map_id, map_zero
-/
lemma hasZeroObject_of_additive [HasZeroObject C] :
    HasZeroObject D where
  zero := ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩

open Limits ZeroObject

/--
lemma `Additive.of_isZero` / 引理 `Additive.of_isZero`

English:
lemma Additive.of_isZero
  given: {F : C ⥤ D} (hF : IsZero F)
  proof: IsZero.eq_of_tgt (by
      rw [IsZero.iff_id_eq_zero]
      exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hF) _) _ _

中文:
引理 加性.of_isZero
  条件: {F : C ⥤ D} (hF : 是零 F)
  证明: IsZero.eq_of_tgt (by
      rw [IsZero.iff_id_eq_zero]
      exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hF) _) _ _

Depends on / 依赖: IsZero, IsZero.eq_of_tgt, IsZero.iff_id_eq_zero, NatTrans, NatTrans.congr_app, congr_app, eq_of_tgt, iff_id_eq_zero
-/
lemma Additive.of_isZero {F : C ⥤ D} (hF : IsZero F) :
    F.Additive where
  map_add {_ _ _ _} :=
    IsZero.eq_of_tgt (by
      rw [IsZero.iff_id_eq_zero]
      exact NatTrans.congr_app ((IsZero.iff_id_eq_zero _).1 hF) _) _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: D] : Functor.Additive (0
  body: .of_isZero (isZero_zero _)

omit [Preadditive C] in

中文:
实例 [有ZeroObject
  签名: D] : 函子.加性 (0
  定义体: .of_isZero (isZero_zero _)

omit [Preadditive C] in

Depends on / 依赖: isZero_zero, of_isZero
-/
instance [HasZeroObject D] : Functor.Additive (0 : C ⥤ D) :=
  .of_isZero (isZero_zero _)

omit [Preadditive C] in
instance (F : D ⥤ E) [F.Additive] : ((Functor.whiskeringRight C D E).obj F).Additive where

omit [Preadditive C] [Preadditive D] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Functor.whiskeringRight C D E).Additive

中文:
实例 :
  签名: (函子.whiskeringRight C D E).加性
-/
instance : (Functor.whiskeringRight C D E).Additive where

omit [Preadditive C] [Preadditive D] in
instance (F : C ⥤ D) : ((Functor.whiskeringLeft C D E).obj F).Additive where

set_option backward.defeqAttrib.useBackward true in
omit [Preadditive D] in
instance {E' : Type*} [Category* E'] [Preadditive E'] (G : C ⥤ D ⥤ E) (F : E ⥤ E')
    [F.Additive] [G.Additive] : ((Functor.postcompose₂.obj F).obj G).Additive := by
  dsimp [Functor.postcompose₂]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
universe w in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoproducts.{w}
  signature: C] : (sigmaConst.{w} (C := C)).Additive where

中文:
实例 [HasCoproducts.{w}
  签名: C] : (sigmaConst.{w} (C := C)).加性 where

Depends on / 依赖: Additive
-/
instance [HasCoproducts.{w} C] : (sigmaConst.{w} (C := C)).Additive where

end

section InducedCategory

variable {C : Type*} {D : Type*} [Category* D] [Preadditive D] (F : C -> D)

/--
Instance `inducedFunctor_additive` / 实例 `inducedFunctor_additive`

English:
instance inducedFunctor_additive
  signature: : Functor.Additive (inducedFunctor F) where

中文:
实例 inducedFunctor_additive
  签名: : 函子.加性 (inducedFunctor F) where
-/
instance inducedFunctor_additive : Functor.Additive (inducedFunctor F) where

end InducedCategory

/--
Instance `fullSubcategoryInclusion_additive` / 实例 `fullSubcategoryInclusion_additive`

English:
instance fullSubcategoryInclusion_additive
  signature: {C : Type*} [Category* C] [Preadditive C]

中文:
实例 fullSubcategoryInclusion_additive
  签名: {C : 类型} [范畴* C] [预加性 C]
-/
instance fullSubcategoryInclusion_additive {C : Type*} [Category* C] [Preadditive C]
    (Z : ObjectProperty C) : Z.ι.Additive where

instance {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : D ⥤ C) [F.Additive] (P : ObjectProperty C)
    (hF : forall (X : D), P (F.obj X)) :
    (P.lift F hF).Additive where

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false in
instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts F where
  preserves := fun {J} _ =>
    let ⟨_⟩ := nonempty_fintype J
    { preserves :=
      { preserves := fun hb =>
          ⟨isBilimitOfTotal _ (by
            simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
            erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩ } }

instance (priority := 100) preservesFiniteCoproductsOfAdditive [Additive F] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesCoproductsOfShape_of_preservesBiproductsOfShape F

instance (priority := 100) preservesFiniteProductsOfAdditive [Additive F] :
    PreservesFiniteProducts F where
  preserves _ := preservesProductsOfShape_of_preservesBiproductsOfShape F

/--
lemma `hasFiniteProducts_of_additive_of_essSurj` / 引理 `hasFiniteProducts_of_additive_of_essSurj`

English:
lemma hasFiniteProducts_of_additive_of_essSurj
  statement: [HasFiniteProducts C] [Additive F]
  proof: ⟨fun _ => ⟨fun K => hasLimit_of_iso
    (F := Discrete.functor (fun i => F.objPreimage (K.obj ⟨i⟩)) ⋙ F)
      (Discrete.natIso (fun _ => F.objObjPreimageIso _))⟩⟩

中文:
引理 hasFiniteProducts_of_additive_of_essSurj
  结论: [有FiniteProducts C] [加性 F]
  证明: ⟨fun _ => ⟨fun K => hasLimit_of_iso
    (F := Discrete.functor (fun i => F.objPreimage (K.obj ⟨i⟩)) ⋙ F)
      (Discrete.natIso (fun _ => F.objObjPreimageIso _))⟩⟩

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, F.objObjPreimageIso, F.objPreimage, K.obj, functor, hasLimit_of_iso, natIso, objObjPreimageIso, objPreimage
-/
lemma hasFiniteProducts_of_additive_of_essSurj [HasFiniteProducts C] [Additive F]
    [EssSurj F] : HasFiniteProducts D :=
  ⟨fun _ => ⟨fun K => hasLimit_of_iso
    (F := Discrete.functor (fun i => F.objPreimage (K.obj ⟨i⟩)) ⋙ F)
      (Discrete.natIso (fun _ => F.objObjPreimageIso _))⟩⟩

/--
theorem `additive_of_preservesBinaryBiproducts` / 定理 `additive_of_preservesBinaryBiproducts`

English:
theorem additive_of_preservesBinaryBiproducts
  statement: [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
  proof: by
    rw [biprod.add_eq_lift_id_desc]; rw [F.map_comp]; rw [← biprod.lift_mapBiprod]; rw [← biprod.mapBiprod_hom_desc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [F.map_id]; rw [biprod.add_eq_lift_id_desc]

中文:
定理 additive_of_preservesBinaryBiproducts
  结论: [有BinaryBiproducts C] [保持ZeroMorphisms F]
  证明: by
    rw [biprod.add_eq_lift_id_desc]; rw [F.map_comp]; rw [← biprod.lift_mapBiprod]; rw [← biprod.mapBiprod_hom_desc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [F.map_id]; rw [biprod.add_eq_lift_id_desc]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.inv_hom_id_assoc, add_eq_lift_id_desc, biprod, biprod.add_eq_lift_id_desc, biprod.lift_mapBiprod, biprod.mapBiprod_hom_desc, inv_hom_id_assoc, lift_mapBiprod, mapBiprod_hom_desc, map_comp, map_id
-/
theorem additive_of_preservesBinaryBiproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F where
  map_add {X Y f g} := by
    rw [biprod.add_eq_lift_id_desc]; rw [F.map_comp]; rw [← biprod.lift_mapBiprod]; rw [← biprod.mapBiprod_hom_desc]; rw [Category.assoc]; rw [Iso.inv_hom_id_assoc]; rw [F.map_id]; rw [biprod.add_eq_lift_id_desc]

/--
lemma `additive_of_preserves_binary_products` / 引理 `additive_of_preserves_binary_products`

English:
lemma additive_of_preserves_binary_products
  proof: by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

中文:
引理 additive_of_preserves_binary_products
  证明: by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryProducts, additive_of_preservesBinaryBiproducts, of_hasBinaryProducts, preservesBinaryBiproducts_of_preservesBinaryProducts
-/
lemma additive_of_preserves_binary_products
    [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [F.PreservesZeroMorphisms] : F.Additive := by
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

end

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `inverse_additive` / 实例 `inverse_additive`

English:
instance inverse_additive
  signature: (e : C ≌ D) [e.functor.Additive]
  body: e.functor.map_injective (by simp)

中文:
实例 inverse_additive
  签名: (e : C ≌ D) [e.functor.加性]
  定义体: e.functor.map_injective (by simp)

Depends on / 依赖: e.functor.map_injective, functor, map_injective
-/
instance inverse_additive (e : C ≌ D) [e.functor.Additive] : e.inverse.Additive where
  map_add {f g} := e.functor.map_injective (by simp)

end Equivalence

section

variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/--
Definition of `additiveFunctor` / `additiveFunctor` 的定义

English:
definition additiveFunctor
  signature: : ObjectProperty (C ⥤ D)
  body: fun F => F.Additive

中文:
定义 additiveFunctor
  签名: : ObjectProperty (C ⥤ D)
  定义体: fun F => F.Additive

Depends on / 依赖: Additive, F.Additive
-/
def additiveFunctor : ObjectProperty (C ⥤ D) := fun F => F.Additive

variable {C D} in
/--
lemma `additiveFunctor_iff` / 引理 `additiveFunctor_iff`

English:
lemma additiveFunctor_iff
  given: (F : C ⥤ D)
  proof: Iff.rfl

中文:
引理 additiveFunctor_iff
  条件: (F : C ⥤ D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma additiveFunctor_iff (F : C ⥤ D) :
    additiveFunctor C D F ↔ F.Additive := Iff.rfl

/--
Definition of `AdditiveFunctor` / `AdditiveFunctor` 的定义

English:
abbreviation AdditiveFunctor
  body: (additiveFunctor C D).FullSubcategory

中文:
缩写 AdditiveFunctor
  定义体: (additiveFunctor C D).FullSubcategory

Depends on / 依赖: FullSubcategory, additiveFunctor
-/
abbrev AdditiveFunctor := (additiveFunctor C D).FullSubcategory

instance (F : AdditiveFunctor C D) : F.obj.Additive := F.property

/-- the category of additive functors is denoted `C ⥤+ D` -/
infixr:26 " ⥤+ " => AdditiveFunctor

/--
Definition of `AdditiveFunctor.forget` / `AdditiveFunctor.forget` 的定义

English:
abbreviation AdditiveFunctor.forget
  signature: : (C ⥤+ D) ⥤ C ⥤ D
  body: ObjectProperty.ι _

中文:
缩写 AdditiveFunctor.forget
  签名: : (C ⥤+ D) ⥤ C ⥤ D
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

variable {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
@[simps]
/--
Definition of `AdditiveFunctor.of` / `AdditiveFunctor.of` 的定义

English:
definition AdditiveFunctor.of
  signature: (F : C ⥤ D) [F.Additive]
  body: ⟨F, by simpa⟩

@[simp]

中文:
定义 AdditiveFunctor.of
  签名: (F : C ⥤ D) [F.加性]
  定义体: ⟨F, by simpa⟩

@[simp]
-/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, by simpa⟩

@[simp]
/--
theorem `AdditiveFunctor.of_fst` / 定理 `AdditiveFunctor.of_fst`

English:
theorem AdditiveFunctor.of_fst
  given: (F : C ⥤ D) [F.Additive]
  statement: (AdditiveFunctor.of F).1 = F
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.of_fst
  条件: (F : C ⥤ D) [F.加性]
  结论: (AdditiveFunctor.of F).1 = F
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.forget_obj` / 定理 `AdditiveFunctor.forget_obj`

English:
theorem AdditiveFunctor.forget_obj
  given: (F : C ⥤+ D)
  statement: (AdditiveFunctor.forget C D).obj F = F.1
  proof: rfl

中文:
定理 AdditiveFunctor.forget_obj
  条件: (F : C ⥤+ D)
  结论: (AdditiveFunctor.forget C D).obj F = F.1
  证明: rfl
-/
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl

/--
theorem `AdditiveFunctor.forget_obj_of` / 定理 `AdditiveFunctor.forget_obj_of`

English:
theorem AdditiveFunctor.forget_obj_of
  given: (F : C ⥤ D) [F.Additive]
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.forget_obj_of
  条件: (F : C ⥤ D) [F.加性]
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.forget_map` / 定理 `AdditiveFunctor.forget_map`

English:
theorem AdditiveFunctor.forget_map
  given: (F G : C ⥤+ D) (α : F ⟶ G)
  proof: rfl

中文:
定理 AdditiveFunctor.forget_map
  条件: (F G : C ⥤+ D) (α : F ⟶ G)
  证明: rfl
-/
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) :
    (AdditiveFunctor.forget C D).map α = α.hom :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Additive (AdditiveFunctor.forget C D)
  body: rfl

中文:
实例 :
  签名: 函子.加性 (AdditiveFunctor.forget C D)
  定义体: rfl
-/
instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add := rfl

instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/--
lemma `leftExactFunctor_le_additiveFunctor` / 引理 `leftExactFunctor_le_additiveFunctor`

English:
lemma leftExactFunctor_le_additiveFunctor
  proof: fun F h => by
    simp only [leftExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

中文:
引理 leftExactFunctor_le_additiveFunctor
  证明: fun F h => by
    simp only [leftExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, additive_of_preservesBinaryBiproducts, leftExactFunctor_iff
-/
lemma leftExactFunctor_le_additiveFunctor :
    leftExactFunctor C D <= additiveFunctor C D :=
  fun F h => by
    simp only [leftExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

/--
lemma `rightExactFunctor_le_additiveFunctor` / 引理 `rightExactFunctor_le_additiveFunctor`

English:
lemma rightExactFunctor_le_additiveFunctor
  proof: fun F h => by
    simp only [rightExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

中文:
引理 rightExactFunctor_le_additiveFunctor
  证明: fun F h => by
    simp only [rightExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

Depends on / 依赖: Functor, Functor.additive_of_preservesBinaryBiproducts, additive_of_preservesBinaryBiproducts, rightExactFunctor_iff
-/
lemma rightExactFunctor_le_additiveFunctor :
    rightExactFunctor C D <= additiveFunctor C D :=
  fun F h => by
    simp only [rightExactFunctor_iff] at h
    exact Functor.additive_of_preservesBinaryBiproducts F

/--
lemma `exactFunctor_le_additiveFunctor` / 引理 `exactFunctor_le_additiveFunctor`

English:
lemma exactFunctor_le_additiveFunctor
  proof: (exactFunctor_le_leftExactFunctor C D).trans
    (leftExactFunctor_le_additiveFunctor C D)

中文:
引理 exactFunctor_le_additiveFunctor
  证明: (exactFunctor_le_leftExactFunctor C D).trans
    (leftExactFunctor_le_additiveFunctor C D)

Depends on / 依赖: exactFunctor_le_leftExactFunctor, leftExactFunctor_le_additiveFunctor
-/
lemma exactFunctor_le_additiveFunctor :
    exactFunctor C D <= additiveFunctor C D :=
  (exactFunctor_le_leftExactFunctor C D).trans
    (leftExactFunctor_le_additiveFunctor C D)

/--
Definition of `AdditiveFunctor.ofLeftExact` / `AdditiveFunctor.ofLeftExact` 的定义

English:
abbreviation AdditiveFunctor.ofLeftExact
  signature: : (C ⥤ₗ D) ⥤ C ⥤+ D
  body: ObjectProperty.ιOfLE (leftExactFunctor_le_additiveFunctor C D)

中文:
缩写 AdditiveFunctor.ofLeftExact
  签名: : (C ⥤ₗ D) ⥤ C ⥤+ D
  定义体: ObjectProperty.ιOfLE (leftExactFunctor_le_additiveFunctor C D)

Depends on / 依赖: ObjectProperty, leftExactFunctor_le_additiveFunctor
-/
abbrev AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (leftExactFunctor_le_additiveFunctor C D)

/--
Definition of `AdditiveFunctor.ofRightExact` / `AdditiveFunctor.ofRightExact` 的定义

English:
abbreviation AdditiveFunctor.ofRightExact
  signature: : (C ⥤ᵣ D) ⥤ C ⥤+ D
  body: ObjectProperty.ιOfLE (rightExactFunctor_le_additiveFunctor C D)

中文:
缩写 AdditiveFunctor.ofRightExact
  签名: : (C ⥤ᵣ D) ⥤ C ⥤+ D
  定义体: ObjectProperty.ιOfLE (rightExactFunctor_le_additiveFunctor C D)

Depends on / 依赖: ObjectProperty, rightExactFunctor_le_additiveFunctor
-/
abbrev AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (rightExactFunctor_le_additiveFunctor C D)

/--
Definition of `AdditiveFunctor.ofExact` / `AdditiveFunctor.ofExact` 的定义

English:
abbreviation AdditiveFunctor.ofExact
  signature: : (C ⥤ₑ D) ⥤ C ⥤+ D
  body: ObjectProperty.ιOfLE (exactFunctor_le_additiveFunctor C D)

中文:
缩写 AdditiveFunctor.ofExact
  签名: : (C ⥤ₑ D) ⥤ C ⥤+ D
  定义体: ObjectProperty.ιOfLE (exactFunctor_le_additiveFunctor C D)

Depends on / 依赖: ObjectProperty, exactFunctor_le_additiveFunctor
-/
abbrev AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_additiveFunctor C D)

end

variable {C D}

@[simp]
/--
theorem `AdditiveFunctor.ofLeftExact_obj_fst` / 定理 `AdditiveFunctor.ofLeftExact_obj_fst`

English:
theorem AdditiveFunctor.ofLeftExact_obj_fst
  given: (F : C ⥤ₗ D)
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.ofLeftExact_obj_fst
  条件: (F : C ⥤ₗ D)
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.ofLeftExact_obj_fst (F : C ⥤ₗ D) :
    ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.ofRightExact_obj_fst` / 定理 `AdditiveFunctor.ofRightExact_obj_fst`

English:
theorem AdditiveFunctor.ofRightExact_obj_fst
  given: (F : C ⥤ᵣ D)
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.ofRightExact_obj_fst
  条件: (F : C ⥤ᵣ D)
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.ofRightExact_obj_fst (F : C ⥤ᵣ D) :
    ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.ofExact_obj_fst` / 定理 `AdditiveFunctor.ofExact_obj_fst`

English:
theorem AdditiveFunctor.ofExact_obj_fst
  given: (F : C ⥤ₑ D)
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.ofExact_obj_fst
  条件: (F : C ⥤ₑ D)
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.ofExact_obj_fst (F : C ⥤ₑ D) :
    ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.ofLeftExact_map_hom` / 定理 `AdditiveFunctor.ofLeftExact_map_hom`

English:
theorem AdditiveFunctor.ofLeftExact_map_hom
  given: {F G : C ⥤ₗ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.ofLeftExact_map_hom
  条件: {F G : C ⥤ₗ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.ofLeftExact_map_hom {F G : C ⥤ₗ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofLeftExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.ofRightExact_map_hom` / 定理 `AdditiveFunctor.ofRightExact_map_hom`

English:
theorem AdditiveFunctor.ofRightExact_map_hom
  given: {F G : C ⥤ᵣ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 AdditiveFunctor.ofRightExact_map_hom
  条件: {F G : C ⥤ᵣ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem AdditiveFunctor.ofRightExact_map_hom {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofRightExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/--
theorem `AdditiveFunctor.ofExact_map_hom` / 定理 `AdditiveFunctor.ofExact_map_hom`

English:
theorem AdditiveFunctor.ofExact_map_hom
  given: {F G : C ⥤ₑ D} (α : F ⟶ G)
  proof: rfl

中文:
定理 AdditiveFunctor.ofExact_map_hom
  条件: {F G : C ⥤ₑ D} (α : F ⟶ G)
  证明: rfl
-/
theorem AdditiveFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((AdditiveFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

end Exact

end Preadditive

end CategoryTheory
