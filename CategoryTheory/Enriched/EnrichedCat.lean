/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The bicategory of `V`-enriched categories

We define the bicategory `EnrichedCat V` of (bundled) `V`-enriched categories for a fixed monoidal
category `V`.

## Future work

* Define change of base and `ForgetEnrichment` as 2-functors.
* Define the bicategory of enriched ordinary categories.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe w v u u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/--
Definition of `EnrichedCat` / `EnrichedCat` 的定义

English:
definition EnrichedCat
  body: Bundled (EnrichedCategory.{w, v, u} V)

中文:
定义 EnrichedCat
  定义体: Bundled (EnrichedCategory.{w, v, u} V)

Depends on / 依赖: Bundled, EnrichedCategory
-/
def EnrichedCat := Bundled (EnrichedCategory.{w, v, u} V)

namespace EnrichedCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (EnrichedCat V) (Type u)
  body: ⟨Bundled.α⟩

中文:
实例 :
  签名: CoeSort (EnrichedCat V) (类型u)
  定义体: ⟨Bundled.α⟩

Depends on / 依赖: Bundled
-/
instance : CoeSort (EnrichedCat V) (Type u) :=
  ⟨Bundled.α⟩

/--
Instance `str` / 实例 `str`

English:
instance str
  signature: (C : EnrichedCat.{w, v, u} V)
  body: Bundled.str C

中文:
实例 str
  签名: (C : EnrichedCat.{w, v, u} V)
  定义体: Bundled.str C

Depends on / 依赖: Bundled, Bundled.str
-/
instance str (C : EnrichedCat.{w, v, u} V) : EnrichedCategory.{w, v, u} V C :=
  Bundled.str C

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (C : Type u) [EnrichedCategory.{w} V C]
  body: Bundled.of C

中文:
定义 of
  签名: (C : 类型u) [Enriched范畴.{w} V C]
  定义体: Bundled.of C

Depends on / 依赖: Bundled, Bundled.of
-/
def of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V :=
  Bundled.of C

open EnrichedCategory ForgetEnrichment

variable {V} {C : Type u} [EnrichedCategory V C] {D : Type u₁} [EnrichedCategory V D]
  {E : Type u₂} [EnrichedCategory V E] {E' : Type u₃} [EnrichedCategory V E']

/-- Whisker a `V`-enriched natural transformation on the left. -/
@[simps!]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  body: ⟨(F.forgetComp G).hom ≫ F.forget.whiskerLeft α.out ≫ (F.forgetComp H).inv⟩

中文:
定义 whiskerLeft
  定义体: ⟨(F.forgetComp G).hom ≫ F.forget.whiskerLeft α.out ≫ (F.forgetComp H).inv⟩

Depends on / 依赖: F.forget.whiskerLeft, F.forgetComp, forget, forgetComp, whiskerLeft
-/
def whiskerLeft
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : G ⟶ H) :
    F.comp V G ⟶ F.comp V H :=
  ⟨(F.forgetComp G).hom ≫ F.forget.whiskerLeft α.out ≫ (F.forgetComp H).inv⟩

/-- Whisker a `V`-enriched natural transformation on the right. -/
@[simps!]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  body: ⟨(F.forgetComp H).hom ≫ Functor.whiskerRight α.out H.forget ≫ (G.forgetComp H).inv⟩

中文:
定义 whiskerRight
  定义体: ⟨(F.forgetComp H).hom ≫ Functor.whiskerRight α.out H.forget ≫ (G.forgetComp H).inv⟩

Depends on / 依赖: F.forgetComp, Functor, Functor.whiskerRight, G.forgetComp, H.forget, forget, forgetComp, whiskerRight
-/
def whiskerRight
    {F G : EnrichedFunctor V C D} (α : F ⟶ G) (H : EnrichedFunctor V D E) :
    F.comp V H ⟶ G.comp V H :=
  ⟨(F.forgetComp H).hom ≫ Functor.whiskerRight α.out H.forget ≫ (G.forgetComp H).inv⟩

/-- Composing the `V`-enriched identity functor with any functor is isomorphic to that functor. -/
@[simps!]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (F : EnrichedFunctor V C D)
  body: EnrichedFunctor.isoMk (EnrichedFunctor.id V C).forgetComp F ≪≫
    Functor.isoWhiskerRight (EnrichedFunctor.forgetId V C) _ ≪≫ Functor.leftUnitor F.forget

中文:
定义 leftUnitor
  签名: (F : Enriched函子 V C D)
  定义体: EnrichedFunctor.isoMk (EnrichedFunctor.id V C).forgetComp F ≪≫
    Functor.isoWhiskerRight (EnrichedFunctor.forgetId V C) _ ≪≫ Functor.leftUnitor F.forget

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.forgetId, EnrichedFunctor.id, EnrichedFunctor.isoMk, F.forget, Functor, Functor.isoWhiskerRight, Functor.leftUnitor, forget, forgetComp, forgetId, isoWhiskerRight, leftUnitor
-/
def leftUnitor (F : EnrichedFunctor V C D) : (EnrichedFunctor.id V _).comp V F ≅ F :=
EnrichedFunctor.isoMk (EnrichedFunctor.id V C).forgetComp F ≪≫
    Functor.isoWhiskerRight (EnrichedFunctor.forgetId V C) _ ≪≫ Functor.leftUnitor F.forget

/-- Composing any `V`-enriched functor with the identity functor is isomorphic to the former
functor. -/
@[simps!]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (F : EnrichedFunctor V C D)
  body: EnrichedFunctor.isoMk F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

中文:
定义 rightUnitor
  签名: (F : Enriched函子 V C D)
  定义体: EnrichedFunctor.isoMk F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.forgetId, EnrichedFunctor.isoMk, F.forget, F.forgetComp, Functor, Functor.isoWhiskerLeft, Functor.rightUnitor, forget, forgetComp, forgetId, isoWhiskerLeft, rightUnitor
-/
def rightUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V _) ≅ F :=
EnrichedFunctor.isoMk F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

/-- Composition of `V`-enriched functors is associative up to isomorphism. -/
@[simps!]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
  body: EnrichedFunctor.isoMk (F.comp V G).forgetComp H ≪≫
    Functor.isoWhiskerRight (F.forgetComp G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.forgetComp H).symm ≪≫
    (F.forgetComp _).symm

中文:
定义 associator
  签名: (F : Enriched函子 V C D) (G : Enriched函子 V D E)
  定义体: EnrichedFunctor.isoMk (F.comp V G).forgetComp H ≪≫
    Functor.isoWhiskerRight (F.forgetComp G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.forgetComp H).symm ≪≫
    (F.forgetComp _).symm

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.isoMk, F.comp, F.forgetComp, Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, G.forgetComp, associator, forgetComp, isoWhiskerLeft, isoWhiskerRight
-/
def associator (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    (H : EnrichedFunctor V E E') :
    EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H ≅
    EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H) :=
EnrichedFunctor.isoMk (F.comp V G).forgetComp H ≪≫
    Functor.isoWhiskerRight (F.forgetComp G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.forgetComp H).symm ≪≫
    (F.forgetComp _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_whiskerRight` / 引理 `comp_whiskerRight`

English:
lemma comp_whiskerRight
  statement: {F G H : EnrichedFunctor V C D} (α : F ⟶ G)
  proof: by
  ext X
  simp only [whiskerRight_out_app, NatTrans.comp_app, EnrichedFunctor.category_comp_out,
    EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map]
  simp [← ForgetEnrichment.homOf_comp]

中文:
引理 comp_whiskerRight
  结论: {F G H : Enriched函子 V C D} (α : F ⟶ G)
  证明: by
  ext X
  simp only [whiskerRight_out_app, NatTrans.comp_app, EnrichedFunctor.category_comp_out,
    EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map]
  simp [← ForgetEnrichment.homOf_comp]

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.category_comp_out, EnrichedFunctor.comp_map, EnrichedFunctor.comp_obj, EnrichedFunctor.forget, ForgetEnrichment, ForgetEnrichment.homOf_comp, NatTrans, NatTrans.comp_app, category_comp_out, comp_app, comp_map, comp_obj, forget, homOf_comp, whiskerRight_out_app
-/
lemma comp_whiskerRight {F G H : EnrichedFunctor V C D} (α : F ⟶ G)
    (β : G ⟶ H) (I : EnrichedFunctor V D E) :
    whiskerRight ⟨α.out ≫ β.out⟩ I = whiskerRight α I ≫ whiskerRight β I := by
  ext X
  simp only [whiskerRight_out_app, NatTrans.comp_app, EnrichedFunctor.category_comp_out,
    EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map]
  simp [← ForgetEnrichment.homOf_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `whisker_exchange` / 引理 `whisker_exchange`

English:
lemma whisker_exchange
  statement: {F G : EnrichedFunctor V C D} {H I : EnrichedFunctor V D E}
  proof: by
  ext X
  simp only [EnrichedFunctor.forget_obj, EnrichedFunctor.comp_obj,
    EnrichedFunctor.category_comp_out, NatTrans.comp_app, whiskerLeft_out_app,
    whiskerRight_out_app]
  exact (β.out.naturality (α.out.app (ForgetEnrichment.of V X))).symm

中文:
引理 whisker_exchange
  结论: {F G : Enriched函子 V C D} {H I : Enriched函子 V D E}
  证明: by
  ext X
  simp only [EnrichedFunctor.forget_obj, EnrichedFunctor.comp_obj,
    EnrichedFunctor.category_comp_out, NatTrans.comp_app, whiskerLeft_out_app,
    whiskerRight_out_app]
  exact (β.out.naturality (α.out.app (ForgetEnrichment.of V X))).symm

Depends on / 依赖: EnrichedFunctor, EnrichedFunctor.category_comp_out, EnrichedFunctor.comp_obj, EnrichedFunctor.forget_obj, ForgetEnrichment, ForgetEnrichment.of, NatTrans, NatTrans.comp_app, category_comp_out, comp_app, comp_obj, forget_obj, naturality, out.app, out.naturality, whiskerLeft_out_app, whiskerRight_out_app
-/
lemma whisker_exchange {F G : EnrichedFunctor V C D} {H I : EnrichedFunctor V D E}
    (α : F ⟶ G) (β : H ⟶ I) :
    whiskerLeft F β ≫ whiskerRight α I = whiskerRight α H ≫ whiskerLeft G β := by
  ext X
  simp only [EnrichedFunctor.forget_obj, EnrichedFunctor.comp_obj,
    EnrichedFunctor.category_comp_out, NatTrans.comp_app, whiskerLeft_out_app,
    whiskerRight_out_app]
  exact (β.out.naturality (α.out.app (ForgetEnrichment.of V X))).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `bicategory` / 实例 `bicategory`

English:
instance bicategory
  signature: : Bicategory (EnrichedCat.{w, v, u} V) where
  body: EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H := whiskerLeft F
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerRight := comp_whiskerRight
  whisker_ex

中文:
实例 bicategory
  签名: : 双范畴 (EnrichedCat.{w, v, u} V) where
  定义体: EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H := whiskerLeft F
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerRight := comp_whiskerRight
  whisker_ex

Depends on / 依赖: EnrichedFunctor
-/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H := whiskerLeft F
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerRight := comp_whiskerRight
  whisker_exchange := whisker_exchange

end EnrichedCat

end CategoryTheory
