/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Hom

/-!
# The Yoneda embedding

Let `C : Type u₁` be a category (with `Category.{v₁} C`). We define
the Yoneda embedding as a fully faithful functor `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`,
In addition to `yoneda`, we also define `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)`
with the additional universe parameter `w`. When `C` is locally `w`-small,
one may also use `shrinkYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type w` from the file
`Mathlib/CategoryTheory/ShrinkYoneda.lean`.

The naturality of the bijection `yonedaEquiv` involved in the
Yoneda lemma is also expressed as a natural isomorphism
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Opposite CategoryTheory.Functor

universe w v v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C]

/-- The Yoneda embedding, as a functor from `C` into presheaves on `C`. -/
@[implicit_reducible, simps obj_obj obj_map map_app, stacks 001O]
/--
Definition of `yoneda` / `yoneda` 的定义

English:
definition yoneda
  signature: : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  body: { obj Y := (unop Y) ⟶ X
      map f := ↾fun g => f.unop ≫ g }
  map f :=
    { app _ := ↾fun g => g ≫ f }

中文:
定义 yoneda
  签名: : C ⥤ Cᵒᵖ ⥤ 类型v₁ where
  定义体: { obj Y := (unop Y) ⟶ X
      map f := ↾fun g => f.unop ≫ g }
  map f :=
    { app _ := ↾fun g => g ≫ f }

Depends on / 依赖: f.unop
-/
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := (unop Y) ⟶ X
      map f := ↾fun g => f.unop ≫ g }
  map f :=
    { app _ := ↾fun g => g ≫ f }

/-- Unification hint for `(yoneda.obj X).obj (op Y) = Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj (op Y) ≟ Y' ⟶ X'

/-- Unification hint for `(yoneda.obj X).obj Y = unop Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj Y ≟ unop Y' ⟶ X'

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps! obj_obj obj_map map_app]
/--
Definition of `uliftYoneda` / `uliftYoneda` 的定义

English:
definition uliftYoneda
  signature: : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)
  body: yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

中文:
定义 uliftYoneda
  签名: : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)
  定义体: yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

Depends on / 依赖: uliftFunctor, whiskeringRight, yoneda
-/
def uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

/-- Unification hint for `(uliftYoneda.obj X).obj (op Y) ≃ ULift (Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj (op Y) ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftYoneda.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj Y ≟ ULift (unop Y' ⟶ X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`. -/
@[simps! inv_app_app hom_app_app]
/--
Definition of `uliftYonedaIsoYoneda` / `uliftYonedaIsoYoneda` 的定义

English:
definition uliftYonedaIsoYoneda
  signature: {C : Type u₁} [Category.{max w v₁} C]
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

中文:
定义 uliftYonedaIsoYoneda
  签名: {C : 类型u₁} [Category.{max w v₁} C]
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

Depends on / 依赖: yoneda
-/
def uliftYonedaIsoYoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftYoneda.{w} (C := C) ≅ yoneda :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

/--
Definition of `coyoneda` / `coyoneda` 的定义

English:
abbreviation coyoneda
  signature: : Cᵒᵖ ⥤ C ⥤ Type v₁
  body: yoneda.flip

中文:
缩写 coyoneda
  签名: : Cᵒᵖ ⥤ C ⥤ 类型v₁
  定义体: yoneda.flip

Depends on / 依赖: yoneda, yoneda.flip
-/
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

/-- Unification hint for `(coyoneda.obj (op X)).obj Y = X ⟶ Y`. -/
unif_hint coyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj (op X)).obj Y ≟ X' ⟶ Y'

/-- Unification hint for `(coyoneda.obj Y).obj X = unop Y ⟶ X`. -/
unif_hint coyoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj Y).obj X ≟ unop Y' ⟶ X'

/-- Variant of the Coyoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ]
/--
Definition of `uliftCoyoneda` / `uliftCoyoneda` 的定义

English:
abbreviation uliftCoyoneda
  signature: : Cᵒᵖ ⥤ C ⥤ Type (max w v₁)
  body: uliftYoneda.{w}.flip

中文:
缩写 uliftCoyoneda
  签名: : Cᵒᵖ ⥤ C ⥤ Type (max w v₁)
  定义体: uliftYoneda.{w}.flip

Depends on / 依赖: uliftYoneda
-/
abbrev uliftCoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max w v₁) := uliftYoneda.{w}.flip

/-- Unification hint for `(uliftCoyoneda.{w}.obj (op X)).obj Y = ULift (Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj (op X)).obj Y ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftCoyoneda.{w}.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom' (X X' : Cᵒᵖ) (Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj X).obj Y ≟ ULift (Y' ⟶ unop X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftCoyoneda.{w} (C := C) ≅ coyoneda`. -/
@[simps! inv_app_app hom_app_app]
/--
Definition of `uliftCoyonedaIsoCoyoneda` / `uliftCoyonedaIsoCoyoneda` 的定义

English:
definition uliftCoyonedaIsoCoyoneda
  signature: {C : Type u₁} [Category.{max w v₁} C]
  body: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

中文:
定义 uliftCoyonedaIsoCoyoneda
  签名: {C : 类型u₁} [Category.{max w v₁} C]
  定义体: NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

Depends on / 依赖: coyoneda
-/
def uliftCoyonedaIsoCoyoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftCoyoneda.{w} (C := C) ≅ coyoneda :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.ulift.toIso))

namespace Yoneda

/--
theorem `obj_map_id` / 定理 `obj_map_id`

English:
theorem obj_map_id
  given: {X Y : C} (f : op X ⟶ op Y)
  proof: by
  simp

中文:
定理 obj_map_id
  条件: {X Y : C} (f : op X ⟶ op Y)
  证明: by
  simp
-/
theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) := by
  simp

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
definition fullyFaithful
  signature: : (yoneda (C := C)).FullyFaithful where
  body: f.app _ (𝟙 _)
  map_preimage := by -- this was automatic
    intro Z W f
    ext X x
    have := f.naturality_apply x.op (𝟙 Z)
    cat_disch

中文:
定义 fullyFaithful
  签名: : (yoneda (C := C)).FullyFaithful where
  定义体: f.app _ (𝟙 _)
  map_preimage := by -- this was automatic
    intro Z W f
    ext X x
    have := f.naturality_apply x.op (𝟙 Z)
    cat_disch

Depends on / 依赖: FullyFaithful
-/
def fullyFaithful : (yoneda (C := C)).FullyFaithful where
  preimage f := f.app _ (𝟙 _)
  map_preimage := by -- this was automatic
    intro Z W f
    ext X x
    have := f.naturality_apply x.op (𝟙 Z)
    cat_disch

/--
lemma `fullyFaithful_preimage` / 引理 `fullyFaithful_preimage`

English:
lemma fullyFaithful_preimage
  given: {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y)
  proof: rfl

中文:
引理 fullyFaithful_preimage
  条件: {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y)
  证明: rfl
-/
lemma fullyFaithful_preimage {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y) :
    fullyFaithful.preimage f = f.app (op X) (𝟙 X) := rfl

/-- The Yoneda embedding is full. -/
@[stacks 001P]
/--
Instance `yoneda_full` / 实例 `yoneda_full`

English:
instance yoneda_full
  signature: : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full
  body: fullyFaithful.full

中文:
实例 yoneda_full
  签名: : (yoneda : C ⥤ Cᵒᵖ ⥤ 类型v₁).Full
  定义体: fullyFaithful.full

Depends on / 依赖: fullyFaithful, fullyFaithful.full
-/
instance yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full :=
  fullyFaithful.full

/-- The Yoneda embedding is faithful. -/
@[stacks 001P]
/--
Instance `yoneda_faithful` / 实例 `yoneda_faithful`

English:
instance yoneda_faithful
  signature: : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful
  body: fullyFaithful.faithful

中文:
实例 yoneda_faithful
  签名: : (yoneda : C ⥤ Cᵒᵖ ⥤ 类型v₁).Faithful
  定义体: fullyFaithful.faithful

Depends on / 依赖: faithful, fullyFaithful, fullyFaithful.faithful
-/
instance yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: (X Y : C) (p : forall {Z : C}, (Z ⟶ X) -> (Z ⟶ Y))
  body: fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := ↾p
        inv := ↾q })

中文:
定义 ext
  签名: (X Y : C) (p : 对任意 {Z : C}, (Z ⟶ X) -> (Z ⟶ Y))
  定义体: fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := ↾p
        inv := ↾q })

Depends on / 依赖: NatIso, NatIso.ofComponents, fullyFaithful, fullyFaithful.preimageIso, ofComponents, preimageIso
-/
def ext (X Y : C) (p : forall {Z : C}, (Z ⟶ X) -> (Z ⟶ Y))
    (q : forall {Z : C}, (Z ⟶ Y) -> (Z ⟶ X))
    (h₁ : forall {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : forall {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : forall {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := ↾p
        inv := ↾q })

/--
theorem `isIso` / 定理 `isIso`

English:
theorem isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)]
  statement: IsIso f
  proof: isIso_of_fully_faithful yoneda f

中文:
定理 isIso
  条件: {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)]
  结论: IsIso f
  证明: isIso_of_fully_faithful yoneda f

Depends on / 依赖: isIso_of_fully_faithful, yoneda
-/
theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f

end Yoneda

namespace ULiftYoneda

variable (C)

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
definition fullyFaithful
  signature: : (uliftYoneda.{w} (C := C)).FullyFaithful
  body: Yoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

中文:
定义 fullyFaithful
  签名: : (uliftYoneda.{w} (C := C)).FullyFaithful
  定义体: Yoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

Depends on / 依赖: FullyFaithful
-/
def fullyFaithful : (uliftYoneda.{w} (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftYoneda.{w} (C := C)).Full
  body: (fullyFaithful C).full

中文:
实例 :
  签名: (uliftYoneda.{w} (C := C)).Full
  定义体: (fullyFaithful C).full
-/
instance : (uliftYoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftYoneda.{w} (C := C)).Faithful
  body: (fullyFaithful C).faithful

中文:
实例 :
  签名: (uliftYoneda.{w} (C := C)).Faithful
  定义体: (fullyFaithful C).faithful

Depends on / 依赖: Faithful
-/
instance : (uliftYoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftYoneda

namespace Coyoneda

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
definition fullyFaithful
  signature: : (coyoneda (C := C)).FullyFaithful where
  body: (f.app _ (𝟙 _)).op
  map_preimage := by
    intro Z W f
    ext X x
    have := f.naturality_apply x (𝟙 (unop Z))
    cat_disch

中文:
定义 fullyFaithful
  签名: : (coyoneda (C := C)).FullyFaithful where
  定义体: (f.app _ (𝟙 _)).op
  map_preimage := by
    intro Z W f
    ext X x
    have := f.naturality_apply x (𝟙 (unop Z))
    cat_disch

Depends on / 依赖: FullyFaithful
-/
def fullyFaithful : (coyoneda (C := C)).FullyFaithful where
  preimage f := (f.app _ (𝟙 _)).op
  map_preimage := by
    intro Z W f
    ext X x
    have := f.naturality_apply x (𝟙 (unop Z))
    cat_disch

/--
lemma `fullyFaithful_preimage` / 引理 `fullyFaithful_preimage`

English:
lemma fullyFaithful_preimage
  given: {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y)
  proof: rfl

中文:
引理 fullyFaithful_preimage
  条件: {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y)
  证明: rfl
-/
lemma fullyFaithful_preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) :
    fullyFaithful.preimage f = (f.app X.unop (𝟙 X.unop)).op := rfl

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y)
  body: (f.app _ (𝟙 X.unop)).op

中文:
定义 preimage
  签名: {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y)
  定义体: (f.app _ (𝟙 X.unop)).op

Depends on / 依赖: X.unop, f.app
-/
def preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y :=
  (f.app _ (𝟙 X.unop)).op

/--
Instance `coyoneda_full` / 实例 `coyoneda_full`

English:
instance coyoneda_full
  signature: : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full
  body: fullyFaithful.full

中文:
实例 coyoneda_full
  签名: : (coyoneda : Cᵒᵖ ⥤ C ⥤ 类型v₁).Full
  定义体: fullyFaithful.full

Depends on / 依赖: fullyFaithful, fullyFaithful.full
-/
instance coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full :=
  fullyFaithful.full

/--
Instance `coyoneda_faithful` / 实例 `coyoneda_faithful`

English:
instance coyoneda_faithful
  signature: : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful
  body: fullyFaithful.faithful

中文:
实例 coyoneda_faithful
  签名: : (coyoneda : Cᵒᵖ ⥤ C ⥤ 类型v₁).Faithful
  定义体: fullyFaithful.faithful

Depends on / 依赖: faithful, fullyFaithful, fullyFaithful.faithful
-/
instance coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: (X Y : C) (p : forall {Z : C}, (X ⟶ Z) -> (Y ⟶ Z))
  body: fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Z =>
      { hom := ↾q
        inv := ↾p })) |>.unop

中文:
定义 ext
  签名: (X Y : C) (p : 对任意 {Z : C}, (X ⟶ Z) -> (Y ⟶ Z))
  定义体: fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Z =>
      { hom := ↾q
        inv := ↾p })) |>.unop

Depends on / 依赖: NatIso, NatIso.ofComponents, fullyFaithful, fullyFaithful.preimageIso, ofComponents, preimageIso
-/
def ext (X Y : C) (p : forall {Z : C}, (X ⟶ Z) -> (Y ⟶ Z))
    (q : forall {Z : C}, (Y ⟶ Z) -> (X ⟶ Z))
    (h₁ : forall {Z : C} (f : X ⟶ Z), q (p f) = f) (h₂ : forall {Z : C} (f : Y ⟶ Z), p (q f) = f)
    (n : forall {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'), q (f ≫ g) = q f ≫ g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Z =>
      { hom := ↾q
        inv := ↾p })) |>.unop

/--
theorem `isIso` / 定理 `isIso`

English:
theorem isIso
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)]
  statement: IsIso f
  proof: isIso_of_fully_faithful coyoneda f

中文:
定理 isIso
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)]
  结论: IsIso f
  证明: isIso_of_fully_faithful coyoneda f

Depends on / 依赖: coyoneda, isIso_of_fully_faithful
-/
theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f

/--
Definition of `punitIso` / `punitIso` 的定义

English:
definition punitIso
  signature: : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁)
  body: NatIso.ofComponents fun X =>
    { hom := ↾fun f => f.hom ⟨⟩
      inv := ↾fun x => ↾fun _ => x }

中文:
定义 punitIso
  签名: : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (类型v₁)
  定义体: NatIso.ofComponents fun X =>
    { hom := ↾fun f => f.hom ⟨⟩
      inv := ↾fun x => ↾fun _ => x }

Depends on / 依赖: NatIso, NatIso.ofComponents, f.hom, ofComponents
-/
def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents fun X =>
    { hom := ↾fun f => f.hom ⟨⟩
      inv := ↾fun x => ↾fun _ => x }

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps! inv_app hom_app]
/--
Definition of `objOpOp` / `objOpOp` 的定义

English:
definition objOpOp
  signature: (X : C)
  body: NatIso.ofComponents fun _ => (opEquiv _ _).toIso

中文:
定义 objOpOp
  签名: (X : C)
  定义体: NatIso.ofComponents fun _ => (opEquiv _ _).toIso

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, opEquiv
-/
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents fun _ => (opEquiv _ _).toIso

/--
Definition of `opIso` / `opIso` 的定义

English:
definition opIso
  signature: : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda
  body: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => (opEquiv (op Y) X).toIso)
    (fun _ => rfl)) (fun _ => rfl)

中文:
定义 opIso
  签名: : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => (opEquiv (op Y) X).toIso)
    (fun _ => rfl)) (fun _ => rfl)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, opEquiv
-/
def opIso : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => (opEquiv (op Y) X).toIso)
    (fun _ => rfl)) (fun _ => rfl)

namespace ULiftCoyoneda

variable (C)

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
definition fullyFaithful
  signature: : (uliftCoyoneda.{w} (C := C)).FullyFaithful
  body: Coyoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

中文:
定义 fullyFaithful
  签名: : (uliftCoyoneda.{w} (C := C)).FullyFaithful
  定义体: Coyoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

Depends on / 依赖: FullyFaithful
-/
def fullyFaithful : (uliftCoyoneda.{w} (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftCoyoneda.{w} (C := C)).Full
  body: (fullyFaithful C).full

中文:
实例 :
  签名: (uliftCoyoneda.{w} (C := C)).Full
  定义体: (fullyFaithful C).full
-/
instance : (uliftCoyoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftCoyoneda.{w} (C := C)).Faithful
  body: (fullyFaithful C).faithful

中文:
实例 :
  签名: (uliftCoyoneda.{w} (C := C)).Faithful
  定义体: (fullyFaithful C).faithful

Depends on / 依赖: Faithful
-/
instance : (uliftCoyoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftCoyoneda

end Coyoneda

namespace Functor

/--
Definition of `RepresentableBy` / `RepresentableBy` 的定义

English:
structure RepresentableBy
  parameters: (F : Cᵒᵖ ⥤ Type v) (Y : C)
  axioms and operations (2):
    - homEquiv({X : C}) : (X ⟶ Y) ≃ F.obj (op X)
    - homEquiv_comp({X X' : C} (f : X ⟶ X') (g : X' ⟶ Y)) : homEquiv (f ≫ g) = F.map f.op (homEquiv g)  [default: by cat_disch]

中文:
结构 RepresentableBy
  参数: (F : Cᵒᵖ ⥤ 类型v) (Y : C)
  公理与运算 (2 个):
    - homEquiv({X : C}) : (X ⟶ Y) ≃ F.obj (op X)
    - homEquiv_comp({X X' : C} (f : X ⟶ X') (g : X' ⟶ Y)) : homEquiv (f ≫ g) = F.map f.op (homEquiv g)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    homEquiv (f ≫ g) = F.map f.op (homEquiv g) := by cat_disch

/--
lemma `RepresentableBy.comp_homEquiv_symm` / 引理 `RepresentableBy.comp_homEquiv_symm`

English:
lemma RepresentableBy.comp_homEquiv_symm
  statement: {F : Cᵒᵖ ⥤ Type v} {Y : C}
  proof: e.homEquiv.injective (by simp [homEquiv_comp])

中文:
引理 RepresentableBy.comp_homEquiv_symm
  结论: {F : Cᵒᵖ ⥤ 类型v} {Y : C}
  证明: e.homEquiv.injective (by simp [homEquiv_comp])

Depends on / 依赖: e.homEquiv.injective, homEquiv, homEquiv_comp, injective
-/
lemma RepresentableBy.comp_homEquiv_symm {F : Cᵒᵖ ⥤ Type v} {Y : C}
    (e : F.RepresentableBy Y) {X X' : C} (x : F.obj (op X')) (f : X ⟶ X') :
    f ≫ e.homEquiv.symm x = e.homEquiv.symm (F.map f.op x) :=
  e.homEquiv.injective (by simp [homEquiv_comp])

/--
lemma `RepresentableBy.homEquiv_unop_comp` / 引理 `RepresentableBy.homEquiv_unop_comp`

English:
lemma RepresentableBy.homEquiv_unop_comp
  statement: {F : Cᵒᵖ ⥤ Type*} {Y : C}
  proof: h.homEquiv_comp _ _

中文:
引理 RepresentableBy.homEquiv_unop_comp
  结论: {F : Cᵒᵖ ⥤ 类型} {Y : C}
  证明: h.homEquiv_comp _ _

Depends on / 依赖: h.homEquiv_comp, homEquiv_comp
-/
lemma RepresentableBy.homEquiv_unop_comp {F : Cᵒᵖ ⥤ Type*} {Y : C}
    (h : F.RepresentableBy Y) {X : Cᵒᵖ} {X' : C} (f : Opposite.op X' ⟶ X) (g : X' ⟶ Y) :
    h.homEquiv (f.unop ≫ g) = F.map f (h.homEquiv g) :=
  h.homEquiv_comp _ _

/--
Definition of `RepresentableBy.ofIso` / `RepresentableBy.ofIso` 的定义

English:
definition RepresentableBy.ofIso
  signature: {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
  body: e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

中文:
定义 RepresentableBy.ofIso
  签名: {F F' : Cᵒᵖ ⥤ 类型v} {Y : C} (e : F.RepresentableBy Y)
  定义体: e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

Depends on / 依赖: e.homEquiv.trans, homEquiv, toEquiv
-/
def RepresentableBy.ofIso {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    (e' : F ≅ F') : F'.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

/--
Definition of `CorepresentableBy` / `CorepresentableBy` 的定义

English:
structure CorepresentableBy
  parameters: (F : C ⥤ Type v) (X : C)
  axioms and operations (2):
    - homEquiv({Y : C}) : (X ⟶ Y) ≃ F.obj Y
    - homEquiv_comp({Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y)) : homEquiv (f ≫ g) = F.map g (homEquiv f)  [default: by cat_disch]

中文:
结构 CorepresentableBy
  参数: (F : C ⥤ 类型v) (X : C)
  公理与运算 (2 个):
    - homEquiv({Y : C}) : (X ⟶ Y) ≃ F.obj Y
    - homEquiv_comp({Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y)) : homEquiv (f ≫ g) = F.map g (homEquiv f)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CorepresentableBy (F : C ⥤ Type v) (X : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj Y`. -/
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f) := by cat_disch

/--
lemma `CorepresentableBy.homEquiv_symm_comp` / 引理 `CorepresentableBy.homEquiv_symm_comp`

English:
lemma CorepresentableBy.homEquiv_symm_comp
  statement: {F : C ⥤ Type v} {X : C}
  proof: e.homEquiv.injective (by simp [homEquiv_comp])

中文:
引理 CorepresentableBy.homEquiv_symm_comp
  结论: {F : C ⥤ 类型v} {X : C}
  证明: e.homEquiv.injective (by simp [homEquiv_comp])

Depends on / 依赖: e.homEquiv.injective, homEquiv, homEquiv_comp, injective
-/
lemma CorepresentableBy.homEquiv_symm_comp {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) {Y Y' : C} (y : F.obj Y) (g : Y ⟶ Y') :
    e.homEquiv.symm y ≫ g = e.homEquiv.symm (F.map g y) :=
  e.homEquiv.injective (by simp [homEquiv_comp])

/--
Definition of `CorepresentableBy.ofIso` / `CorepresentableBy.ofIso` 的定义

English:
definition CorepresentableBy.ofIso
  signature: {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
  body: e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

中文:
定义 CorepresentableBy.ofIso
  签名: {F F' : C ⥤ 类型v} {X : C} (e : F.CorepresentableBy X)
  定义体: e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

Depends on / 依赖: e.homEquiv.trans, homEquiv, toEquiv
-/
def CorepresentableBy.ofIso {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    (e' : F ≅ F') :
    F'.CorepresentableBy X where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

/--
lemma `RepresentableBy.homEquiv_eq` / 引理 `RepresentableBy.homEquiv_eq`

English:
lemma RepresentableBy.homEquiv_eq
  statement: {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
  proof: by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

中文:
引理 RepresentableBy.homEquiv_eq
  结论: {F : Cᵒᵖ ⥤ 类型v} {Y : C} (e : F.RepresentableBy Y)
  证明: by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

Depends on / 依赖: Category, Category.comp_id, comp_id, conv_lhs, e.homEquiv_comp, homEquiv_comp
-/
lemma RepresentableBy.homEquiv_eq {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    {X : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f.op (e.homEquiv (𝟙 Y)) := by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

/--
lemma `CorepresentableBy.homEquiv_eq` / 引理 `CorepresentableBy.homEquiv_eq`

English:
lemma CorepresentableBy.homEquiv_eq
  statement: {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
  proof: by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

中文:
引理 CorepresentableBy.homEquiv_eq
  结论: {F : C ⥤ 类型v} {X : C} (e : F.CorepresentableBy X)
  证明: by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

Depends on / 依赖: Category, Category.id_comp, conv_lhs, e.homEquiv_comp, homEquiv_comp, id_comp
-/
lemma CorepresentableBy.homEquiv_eq {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    {Y : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f (e.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

/-- Representing objects are unique up to isomorphism. -/
@[simps!]
/--
Definition of `RepresentableBy.uniqueUpToIso` / `RepresentableBy.uniqueUpToIso` 的定义

English:
definition RepresentableBy.uniqueUpToIso
  signature: {F : Cᵒᵖ ⥤ Type v} {Y Y' : C} (e : F.RepresentableBy Y)
  body: let ε {X} := (@e.homEquiv X).trans e'.homEquiv.symm
  Yoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, comp_homEquiv_symm, homEquiv_comp])

中文:
定义 RepresentableBy.uniqueUpToIso
  签名: {F : Cᵒᵖ ⥤ 类型v} {Y Y' : C} (e : F.RepresentableBy Y)
  定义体: let ε {X} := (@e.homEquiv X).trans e'.homEquiv.symm
  Yoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, comp_homEquiv_symm, homEquiv_comp])

Depends on / 依赖: Yoneda, Yoneda.ext, comp_homEquiv_symm, e.homEquiv, homEquiv, homEquiv.symm, homEquiv_comp
-/
def RepresentableBy.uniqueUpToIso {F : Cᵒᵖ ⥤ Type v} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') : Y ≅ Y' :=
  let ε {X} := (@e.homEquiv X).trans e'.homEquiv.symm
  Yoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, comp_homEquiv_symm, homEquiv_comp])

/-- Corepresenting objects are unique up to isomorphism. -/
@[simps!]
/--
Definition of `CorepresentableBy.uniqueUpToIso` / `CorepresentableBy.uniqueUpToIso` 的定义

English:
definition CorepresentableBy.uniqueUpToIso
  signature: {F : C ⥤ Type v} {X X' : C} (e : F.CorepresentableBy X)
  body: let ε {Y} := (@e.homEquiv Y).trans e'.homEquiv.symm
  Coyoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, homEquiv_symm_comp, homEquiv_comp])

@[ext]

中文:
定义 CorepresentableBy.uniqueUpToIso
  签名: {F : C ⥤ 类型v} {X X' : C} (e : F.CorepresentableBy X)
  定义体: let ε {Y} := (@e.homEquiv Y).trans e'.homEquiv.symm
  Coyoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, homEquiv_symm_comp, homEquiv_comp])

@[ext]

Depends on / 依赖: Coyoneda, Coyoneda.ext, e.homEquiv, homEquiv, homEquiv.symm, homEquiv_comp, homEquiv_symm_comp
-/
def CorepresentableBy.uniqueUpToIso {F : C ⥤ Type v} {X X' : C} (e : F.CorepresentableBy X)
    (e' : F.CorepresentableBy X') : X ≅ X' :=
  let ε {Y} := (@e.homEquiv Y).trans e'.homEquiv.symm
  Coyoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, homEquiv_symm_comp, homEquiv_comp])

@[ext]
/--
lemma `RepresentableBy.ext` / 引理 `RepresentableBy.ext`

English:
lemma RepresentableBy.ext
  statement: {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
  proof: by
  have : forall {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]

中文:
引理 RepresentableBy.ext
  结论: {F : Cᵒᵖ ⥤ 类型v} {Y : C} {e e' : F.RepresentableBy Y}
  证明: by
  have : forall {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]

Depends on / 依赖: e.homEquiv, e.homEquiv_eq, homEquiv, homEquiv_eq
-/
lemma RepresentableBy.ext {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
    (h : e.homEquiv (𝟙 Y) = e'.homEquiv (𝟙 Y)) : e = e' := by
  have : forall {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]
/--
lemma `CorepresentableBy.ext` / 引理 `CorepresentableBy.ext`

English:
lemma CorepresentableBy.ext
  statement: {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
  proof: by
  have : forall {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

中文:
引理 CorepresentableBy.ext
  结论: {F : C ⥤ 类型v} {X : C} {e e' : F.CorepresentableBy X}
  证明: by
  have : forall {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

Depends on / 依赖: e.homEquiv, e.homEquiv_eq, homEquiv, homEquiv_eq
-/
lemma CorepresentableBy.ext {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
    (h : e.homEquiv (𝟙 X) = e'.homEquiv (𝟙 X)) : e = e' := by
  have : forall {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f => by
    rw [e.homEquiv_eq]; rw [e'.homEquiv_eq]; rw [h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

/--
Definition of `representableByEquiv` / `representableByEquiv` 的定义

English:
definition representableByEquiv
  signature: {F : Cᵒᵖ ⥤ Type v₁} {Y : C}
  body: NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

中文:
定义 representableByEquiv
  签名: {F : Cᵒᵖ ⥤ 类型v₁} {Y : C}
  定义体: NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

Depends on / 依赖: NatIso, NatIso.ofComponents, e.app, e.hom.naturality_apply, homEquiv, homEquiv_comp, invFun, naturality_apply, ofComponents, r.homEquiv.toIso, r.homEquiv_comp, toEquiv
-/
def representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun r := NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

/--
Definition of `RepresentableBy.yoneda` / `RepresentableBy.yoneda` 的定义

English:
definition RepresentableBy.yoneda
  signature: (X : C)
  body: Functor.representableByEquiv.symm (Iso.refl _)

@[simp]

中文:
定义 RepresentableBy.yoneda
  签名: (X : C)
  定义体: Functor.representableByEquiv.symm (Iso.refl _)

@[simp]
-/
protected def RepresentableBy.yoneda (X : C) : (yoneda.obj X).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

@[simp]
/--
lemma `RepresentableBy.coyoneda_homEquiv` / 引理 `RepresentableBy.coyoneda_homEquiv`

English:
lemma RepresentableBy.coyoneda_homEquiv
  given: (X Y : C)
  proof: rfl

中文:
引理 RepresentableBy.coyoneda_homEquiv
  条件: (X Y : C)
  证明: rfl
-/
lemma RepresentableBy.coyoneda_homEquiv (X Y : C) :
    (RepresentableBy.yoneda X).homEquiv = Equiv.refl (Y ⟶ X) :=
  rfl

/--
Definition of `RepresentableBy.toIso` / `RepresentableBy.toIso` 的定义

English:
definition RepresentableBy.toIso
  signature: {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y)
  body: representableByEquiv e

中文:
定义 RepresentableBy.toIso
  签名: {F : Cᵒᵖ ⥤ 类型v₁} {Y : C} (e : F.RepresentableBy Y)
  定义体: representableByEquiv e

Depends on / 依赖: representableByEquiv
-/
def RepresentableBy.toIso {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y) :
    yoneda.obj Y ≅ F :=
  representableByEquiv e

/--
Definition of `corepresentableByEquiv` / `corepresentableByEquiv` 的定义

English:
definition corepresentableByEquiv
  signature: {F : C ⥤ Type v₁} {X : C}
  body: NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

中文:
定义 corepresentableByEquiv
  签名: {F : C ⥤ 类型v₁} {X : C}
  定义体: NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

Depends on / 依赖: NatIso, NatIso.ofComponents, e.app, e.hom.naturality_apply, homEquiv, homEquiv_comp, invFun, naturality_apply, ofComponents, r.homEquiv.toIso, r.homEquiv_comp, toEquiv
-/
def corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} :
    F.CorepresentableBy X ≃ (coyoneda.obj (op X) ≅ F) where
  toFun r := NatIso.ofComponents (fun _ => r.homEquiv.toIso) (fun {X X'} f => by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g => by apply e.hom.naturality_apply }

/--
Definition of `CorepresentableBy.coyoneda` / `CorepresentableBy.coyoneda` 的定义

English:
definition CorepresentableBy.coyoneda
  signature: (X : Cᵒᵖ)
  body: Functor.corepresentableByEquiv.symm (Iso.refl _)

@[simp]

中文:
定义 CorepresentableBy.coyoneda
  签名: (X : Cᵒᵖ)
  定义体: Functor.corepresentableByEquiv.symm (Iso.refl _)

@[simp]
-/
protected def CorepresentableBy.coyoneda (X : Cᵒᵖ) :
    (coyoneda.obj X).CorepresentableBy X.unop :=
  Functor.corepresentableByEquiv.symm (Iso.refl _)

@[simp]
/--
lemma `CorepresentableBy.coyoneda_homEquiv` / 引理 `CorepresentableBy.coyoneda_homEquiv`

English:
lemma CorepresentableBy.coyoneda_homEquiv
  given: (X : Cᵒᵖ) (Y : C)
  proof: rfl

中文:
引理 CorepresentableBy.coyoneda_homEquiv
  条件: (X : Cᵒᵖ) (Y : C)
  证明: rfl
-/
lemma CorepresentableBy.coyoneda_homEquiv (X : Cᵒᵖ) (Y : C) :
    (CorepresentableBy.coyoneda X).homEquiv = Equiv.refl (X.unop ⟶ Y) :=
  rfl

/--
Definition of `CorepresentableBy.toIso` / `CorepresentableBy.toIso` 的定义

English:
definition CorepresentableBy.toIso
  signature: {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X)
  body: corepresentableByEquiv e

中文:
定义 CorepresentableBy.toIso
  签名: {F : C ⥤ 类型v₁} {X : C} (e : F.CorepresentableBy X)
  定义体: corepresentableByEquiv e

Depends on / 依赖: corepresentableByEquiv
-/
def CorepresentableBy.toIso {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X) :
    coyoneda.obj (op X) ≅ F :=
  corepresentableByEquiv e

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
/--
Definition of `RepresentableBy.ofIsoObj` / `RepresentableBy.ofIsoObj` 的定义

English:
definition RepresentableBy.ofIsoObj
  signature: {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
  body: e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

中文:
定义 RepresentableBy.ofIsoObj
  签名: {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
  定义体: e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

Depends on / 依赖: R.homEquiv, e.homToEquiv.trans, homEquiv, homToEquiv
-/
def RepresentableBy.ofIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
    (e : Y ≅ X) :
    F.RepresentableBy Y where
  homEquiv {Z} := e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
/--
Definition of `CorepresentableBy.ofIsoObj` / `CorepresentableBy.ofIsoObj` 的定义

English:
definition CorepresentableBy.ofIsoObj
  signature: {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
  body: e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

中文:
定义 CorepresentableBy.ofIsoObj
  签名: {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
  定义体: e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

Depends on / 依赖: R.homEquiv, e.homFromEquiv.trans, homEquiv, homFromEquiv
-/
def CorepresentableBy.ofIsoObj {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
    (e : Y ≅ X) :
    F.CorepresentableBy Y where
  homEquiv {Z} := e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- If `Y` is isomorphic to `X`, representations of `F` by `X` are equivalent
to representations of `F` by `Y`. -/
@[simps]
/--
Definition of `RepresentableBy.equivOfIsoObj` / `RepresentableBy.equivOfIsoObj` 的定义

English:
definition RepresentableBy.equivOfIsoObj
  signature: {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X)
  body: R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 RepresentableBy.equivOfIsoObj
  签名: {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X)
  定义体: R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: R.ofIsoObj, ofIsoObj
-/
def RepresentableBy.equivOfIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.RepresentableBy X ≃ F.RepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- If `Y` is isomorphic to `X`, corepresentations of `F` by `X` are equivalent
to corepresentations of `F` by `Y`. -/
@[simps]
/--
Definition of `CorepresentableBy.equivOfIsoObj` / `CorepresentableBy.equivOfIsoObj` 的定义

English:
definition CorepresentableBy.equivOfIsoObj
  signature: {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X)
  body: R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

中文:
定义 CorepresentableBy.equivOfIsoObj
  签名: {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X)
  定义体: R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

Depends on / 依赖: R.ofIsoObj, ofIsoObj
-/
def CorepresentableBy.equivOfIsoObj {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.CorepresentableBy X ≃ F.CorepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Representing `F` composed with universe lifting is the same as representing `F`. -/
@[simps]
/--
Definition of `representableByUliftFunctorEquiv` / `representableByUliftFunctorEquiv` 的定义

English:
definition representableByUliftFunctorEquiv
  signature: {F : Cᵒᵖ ⥤ Type v} {X : C}
  body: { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

中文:
定义 representableByUliftFunctorEquiv
  签名: {F : Cᵒᵖ ⥤ 类型v} {X : C}
  定义体: { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

Depends on / 依赖: Equiv.ulift, Equiv.ulift.symm, R.homEquiv.trans, R.homEquiv_comp, homEquiv, homEquiv_comp, invFun
-/
def representableByUliftFunctorEquiv {F : Cᵒᵖ ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).RepresentableBy X ≃ F.RepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Corepresenting `F` composed with universe lifting is the same as corepresenting `F`. -/
@[simps]
/--
Definition of `corepresentableByUliftFunctorEquiv` / `corepresentableByUliftFunctorEquiv` 的定义

English:
definition corepresentableByUliftFunctorEquiv
  signature: {F : C ⥤ Type v} {X : C}
  body: { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

中文:
定义 corepresentableByUliftFunctorEquiv
  签名: {F : C ⥤ 类型v} {X : C}
  定义体: { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

Depends on / 依赖: Equiv.ulift, Equiv.ulift.symm, R.homEquiv.trans, R.homEquiv_comp, homEquiv, homEquiv_comp, invFun
-/
def corepresentableByUliftFunctorEquiv {F : C ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).CorepresentableBy X ≃ F.CorepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

/-- Version of `representableByEquiv` with more general universe assumptions. -/
@[simps]
/--
Definition of `RepresentableBy.equivUliftYonedaIso` / `RepresentableBy.equivUliftYonedaIso` 的定义

English:
definition RepresentableBy.equivUliftYonedaIso
  signature: (F : Cᵒᵖ ⥤ Type (max w v₁)) (X : C)
  body: NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

中文:
定义 RepresentableBy.equivUliftYonedaIso
  签名: (F : Cᵒᵖ ⥤ Type (max w v₁)) (X : C)
  定义体: NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

Depends on / 依赖: Equiv.ulift.symm.trans, Equiv.ulift.trans, NatIso, NatIso.ofComponents, R.homEquiv, R.homEquiv_comp, e.app, e.hom.naturality, equivEquivIso, equivEquivIso.symm, f.op, f.unop, homEquiv, homEquiv_comp, invFun, naturality, ofComponents
-/
def RepresentableBy.equivUliftYonedaIso (F : Cᵒᵖ ⥤ Type (max w v₁)) (X : C) :
    F.RepresentableBy X ≃ (uliftYoneda.obj X ≅ F) where
toFun R := NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

/-- Version of `corepresentableByEquiv` with more general universe assumptions. -/
@[simps]
/--
Definition of `CorepresentableBy.equivUliftCoyonedaIso` / `CorepresentableBy.equivUliftCoyonedaIso` 的定义

English:
definition CorepresentableBy.equivUliftCoyonedaIso
  signature: (F : C ⥤ Type (max w v₁)) (X : C)
  body: NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

中文:
定义 CorepresentableBy.equivUliftCoyonedaIso
  签名: (F : C ⥤ Type (max w v₁)) (X : C)
  定义体: NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

Depends on / 依赖: Equiv.ulift.symm.trans, Equiv.ulift.trans, NatIso, NatIso.ofComponents, R.homEquiv, R.homEquiv_comp, e.app, e.hom.naturality, equivEquivIso, equivEquivIso.symm, homEquiv, homEquiv_comp, invFun, naturality, ofComponents
-/
def CorepresentableBy.equivUliftCoyonedaIso (F : C ⥤ Type (max w v₁)) (X : C) :
    F.CorepresentableBy X ≃ (uliftCoyoneda.obj (op X) ≅ F) where
toFun R := NatIso.ofComponents (fun X => equivEquivIso (Equiv.ulift.trans R.homEquiv)) by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

/-- A functor `F : Cᵒᵖ ⥤ Type v` is representable if there is an object `Y` with a structure
`F.RepresentableBy Y`, i.e. there is a natural bijection `(X ⟶ Y) ≃ F.obj (op X)`,
which may also be rephrased as a natural isomorphism `yoneda.obj X ≅ F` when `Category.{v} C`. -/
@[stacks 001Q]
/--
Definition of `IsRepresentable` / `IsRepresentable` 的定义

English:
class IsRepresentable
  parameters: (F : Cᵒᵖ ⥤ Type v)
  axioms and operations (1):
    - has_representation : exists (Y : C), Nonempty (F.RepresentableBy Y)

中文:
类 IsRepresentable
  参数: (F : Cᵒᵖ ⥤ 类型v)
  公理与运算 (1 个):
    - has_representation : 存在 (Y : C), Nonempty (F.RepresentableBy Y)
-/
class IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
  has_representation : exists (Y : C), Nonempty (F.RepresentableBy Y)

/--
lemma `RepresentableBy.isRepresentable` / 引理 `RepresentableBy.isRepresentable`

English:
lemma RepresentableBy.isRepresentable
  given: {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
  proof: ⟨Y, ⟨e⟩⟩

中文:
引理 RepresentableBy.isRepresentable
  条件: {F : Cᵒᵖ ⥤ 类型v} {Y : C} (e : F.RepresentableBy Y)
  证明: ⟨Y, ⟨e⟩⟩
-/
lemma RepresentableBy.isRepresentable {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) :
    F.IsRepresentable where
  has_representation := ⟨Y, ⟨e⟩⟩

/--
lemma `IsRepresentable.mk'` / 引理 `IsRepresentable.mk'`

English:
lemma IsRepresentable.mk'
  given: {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F)
  proof: (representableByEquiv.symm e).isRepresentable

中文:
引理 IsRepresentable.mk'
  条件: {F : Cᵒᵖ ⥤ 类型v₁} {X : C} (e : yoneda.obj X ≅ F)
  证明: (representableByEquiv.symm e).isRepresentable

Depends on / 依赖: isRepresentable, representableByEquiv, representableByEquiv.symm
-/
lemma IsRepresentable.mk' {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F) :
    F.IsRepresentable :=
  (representableByEquiv.symm e).isRepresentable

instance {X : C} : IsRepresentable (yoneda.obj X) :=
  IsRepresentable.mk' (Iso.refl _)

instance {X : C} : IsRepresentable (uliftYoneda.{w}.obj X) :=
  RepresentableBy.isRepresentable (representableByUliftFunctorEquiv.symm (RepresentableBy.yoneda X))

/--
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.
-/
@[stacks 001Q]
/--
Definition of `IsCorepresentable` / `IsCorepresentable` 的定义

English:
class IsCorepresentable
  parameters: (F : C ⥤ Type v)
  axioms and operations (1):
    - has_corepresentation : exists (X : C), Nonempty (F.CorepresentableBy X)

中文:
类 IsCorepresentable
  参数: (F : C ⥤ 类型v)
  公理与运算 (1 个):
    - has_corepresentation : 存在 (X : C), Nonempty (F.CorepresentableBy X)
-/
class IsCorepresentable (F : C ⥤ Type v) : Prop where
  has_corepresentation : exists (X : C), Nonempty (F.CorepresentableBy X)

/--
lemma `CorepresentableBy.isCorepresentable` / 引理 `CorepresentableBy.isCorepresentable`

English:
lemma CorepresentableBy.isCorepresentable
  statement: {F : C ⥤ Type v} {X : C}
  proof: ⟨X, ⟨e⟩⟩

中文:
引理 CorepresentableBy.isCorepresentable
  结论: {F : C ⥤ 类型v} {X : C}
  证明: ⟨X, ⟨e⟩⟩
-/
lemma CorepresentableBy.isCorepresentable {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) : F.IsCorepresentable where
  has_corepresentation := ⟨X, ⟨e⟩⟩

/--
lemma `IsCorepresentable.mk'` / 引理 `IsCorepresentable.mk'`

English:
lemma IsCorepresentable.mk'
  given: {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F)
  proof: (corepresentableByEquiv.symm e).isCorepresentable

中文:
引理 IsCorepresentable.mk'
  条件: {F : C ⥤ 类型v₁} {X : C} (e : coyoneda.obj (op X) ≅ F)
  证明: (corepresentableByEquiv.symm e).isCorepresentable

Depends on / 依赖: corepresentableByEquiv, corepresentableByEquiv.symm, isCorepresentable
-/
lemma IsCorepresentable.mk' {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F) :
    F.IsCorepresentable :=
  (corepresentableByEquiv.symm e).isCorepresentable

instance {X : Cᵒᵖ} : IsCorepresentable (coyoneda.obj X) :=
  IsCorepresentable.mk' (Iso.refl _)

instance {X : Cᵒᵖ} : IsCorepresentable (uliftCoyoneda.{w}.obj X) :=
  CorepresentableBy.isCorepresentable
    (corepresentableByUliftFunctorEquiv.symm (CorepresentableBy.coyoneda X))

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable]

/--
Definition of `reprX` / `reprX` 的定义

English:
definition reprX
  signature: : C
  body: hF.has_representation.choose

中文:
定义 reprX
  签名: : C
  定义体: hF.has_representation.choose

Depends on / 依赖: hF.has_representation.choose, has_representation
-/
noncomputable def reprX : C :=
  hF.has_representation.choose

/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: : F.RepresentableBy F.reprX
  body: hF.has_representation.choose_spec.some

中文:
定义 representableBy
  签名: : F.RepresentableBy F.reprX
  定义体: hF.has_representation.choose_spec.some

Depends on / 依赖: choose_spec, hF.has_representation.choose_spec.some, has_representation
-/
noncomputable def representableBy : F.RepresentableBy F.reprX :=
  hF.has_representation.choose_spec.some

/--
Definition of `RepresentableBy.isoReprX` / `RepresentableBy.isoReprX` 的定义

English:
definition RepresentableBy.isoReprX
  signature: {Y : C} (e : F.RepresentableBy Y)
  body: RepresentableBy.uniqueUpToIso e (representableBy F)

中文:
定义 RepresentableBy.isoReprX
  签名: {Y : C} (e : F.RepresentableBy Y)
  定义体: RepresentableBy.uniqueUpToIso e (representableBy F)

Depends on / 依赖: RepresentableBy, RepresentableBy.uniqueUpToIso, representableBy, uniqueUpToIso
-/
noncomputable def RepresentableBy.isoReprX {Y : C} (e : F.RepresentableBy Y) :
    Y ≅ F.reprX :=
  RepresentableBy.uniqueUpToIso e (representableBy F)

/--
Definition of `reprx` / `reprx` 的定义

English:
definition reprx
  signature: : F.obj (op F.reprX)
  body: F.representableBy.homEquiv (𝟙 _)

中文:
定义 reprx
  签名: : F.obj (op F.reprX)
  定义体: F.representableBy.homEquiv (𝟙 _)

Depends on / 依赖: F.representableBy.homEquiv, homEquiv, representableBy
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 _)

/--
Definition of `reprW` / `reprW` 的定义

English:
definition reprW
  signature: (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
  body: F.representableBy.toIso

中文:
定义 reprW
  签名: (F : Cᵒᵖ ⥤ 类型v₁) [F.IsRepresentable]
  定义体: F.representableBy.toIso

Depends on / 依赖: F.representableBy.toIso, representableBy
-/
noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F := F.representableBy.toIso

/--
theorem `reprW_hom_app` / 定理 `reprW_hom_app`

English:
theorem reprW_hom_app
  statement: (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
  proof: by
  apply RepresentableBy.homEquiv_eq

中文:
定理 reprW_hom_app
  结论: (F : Cᵒᵖ ⥤ 类型v₁) [F.IsRepresentable]
  证明: by
  apply RepresentableBy.homEquiv_eq

Depends on / 依赖: RepresentableBy, RepresentableBy.homEquiv_eq, homEquiv_eq
-/
theorem reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    F.reprW.hom.app X f = F.map f.op F.reprx := by
  apply RepresentableBy.homEquiv_eq

/--
Definition of `uliftYonedaReprXIso` / `uliftYonedaReprXIso` 的定义

English:
definition uliftYonedaReprXIso
  signature: (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
  body: (RepresentableBy.equivUliftYonedaIso F _) F.representableBy

中文:
定义 uliftYonedaReprXIso
  签名: (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
  定义体: (RepresentableBy.equivUliftYonedaIso F _) F.representableBy

Depends on / 依赖: F.representableBy, RepresentableBy, RepresentableBy.equivUliftYonedaIso, equivUliftYonedaIso, representableBy
-/
noncomputable def uliftYonedaReprXIso (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable] :
    uliftYoneda.{v}.obj F.reprX ≅ F :=
  (RepresentableBy.equivUliftYonedaIso F _) F.representableBy

/--
lemma `uliftYonedaReprXIso_hom_app` / 引理 `uliftYonedaReprXIso_hom_app`

English:
lemma uliftYonedaReprXIso_hom_app
  statement: (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
  proof: RepresentableBy.homEquiv_eq _ _

中文:
引理 uliftYonedaReprXIso_hom_app
  结论: (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
  证明: RepresentableBy.homEquiv_eq _ _

Depends on / 依赖: RepresentableBy, RepresentableBy.homEquiv_eq, homEquiv_eq
-/
lemma uliftYonedaReprXIso_hom_app (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : ULift (unop X ⟶ F.reprX)) :
    F.uliftYonedaReprXIso.hom.app X f = F.map f.down.op F.reprx :=
  RepresentableBy.homEquiv_eq _ _

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [hF : F.IsCorepresentable]

/--
Definition of `coreprX` / `coreprX` 的定义

English:
definition coreprX
  signature: : C
  body: hF.has_corepresentation.choose

中文:
定义 coreprX
  签名: : C
  定义体: hF.has_corepresentation.choose

Depends on / 依赖: hF.has_corepresentation.choose, has_corepresentation
-/
noncomputable def coreprX : C :=
  hF.has_corepresentation.choose

/--
Definition of `corepresentableBy` / `corepresentableBy` 的定义

English:
definition corepresentableBy
  signature: : F.CorepresentableBy F.coreprX
  body: hF.has_corepresentation.choose_spec.some

中文:
定义 corepresentableBy
  签名: : F.CorepresentableBy F.coreprX
  定义体: hF.has_corepresentation.choose_spec.some

Depends on / 依赖: choose_spec, hF.has_corepresentation.choose_spec.some, has_corepresentation
-/
noncomputable def corepresentableBy : F.CorepresentableBy F.coreprX :=
  hF.has_corepresentation.choose_spec.some

variable {F} in
/--
Definition of `CorepresentableBy.isoCoreprX` / `CorepresentableBy.isoCoreprX` 的定义

English:
definition CorepresentableBy.isoCoreprX
  signature: {Y : C} (e : F.CorepresentableBy Y)
  body: CorepresentableBy.uniqueUpToIso e (corepresentableBy F)

中文:
定义 CorepresentableBy.isoCoreprX
  签名: {Y : C} (e : F.CorepresentableBy Y)
  定义体: CorepresentableBy.uniqueUpToIso e (corepresentableBy F)

Depends on / 依赖: CorepresentableBy, CorepresentableBy.uniqueUpToIso, corepresentableBy, uniqueUpToIso
-/
noncomputable def CorepresentableBy.isoCoreprX {Y : C} (e : F.CorepresentableBy Y) :
    Y ≅ F.coreprX :=
  CorepresentableBy.uniqueUpToIso e (corepresentableBy F)

/--
Definition of `coreprx` / `coreprx` 的定义

English:
definition coreprx
  signature: : F.obj F.coreprX
  body: F.corepresentableBy.homEquiv (𝟙 _)

中文:
定义 coreprx
  签名: : F.obj F.coreprX
  定义体: F.corepresentableBy.homEquiv (𝟙 _)

Depends on / 依赖: F.corepresentableBy.homEquiv, corepresentableBy, homEquiv
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.corepresentableBy.homEquiv (𝟙 _)

/--
Definition of `coreprW` / `coreprW` 的定义

English:
definition coreprW
  signature: (F : C ⥤ Type v₁) [F.IsCorepresentable]
  body: F.corepresentableBy.toIso

中文:
定义 coreprW
  签名: (F : C ⥤ 类型v₁) [F.IsCorepresentable]
  定义体: F.corepresentableBy.toIso

Depends on / 依赖: F.corepresentableBy.toIso, corepresentableBy
-/
noncomputable def coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] :
    coyoneda.obj (op F.coreprX) ≅ F :=
  F.corepresentableBy.toIso

/--
theorem `coreprW_hom_app` / 定理 `coreprW_hom_app`

English:
theorem coreprW_hom_app
  given: (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X)
  proof: by
  apply CorepresentableBy.homEquiv_eq

中文:
定理 coreprW_hom_app
  条件: (F : C ⥤ 类型v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X)
  证明: by
  apply CorepresentableBy.homEquiv_eq

Depends on / 依赖: CorepresentableBy, CorepresentableBy.homEquiv_eq, homEquiv_eq
-/
theorem coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X) :
    F.coreprW.hom.app X f = F.map f F.coreprx := by
  apply CorepresentableBy.homEquiv_eq

/--
Definition of `uliftCoyonedaCoreprXIso` / `uliftCoyonedaCoreprXIso` 的定义

English:
definition uliftCoyonedaCoreprXIso
  signature: (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
  body: (CorepresentableBy.equivUliftCoyonedaIso F _) F.corepresentableBy

中文:
定义 uliftCoyonedaCoreprXIso
  签名: (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
  定义体: (CorepresentableBy.equivUliftCoyonedaIso F _) F.corepresentableBy

Depends on / 依赖: CorepresentableBy, CorepresentableBy.equivUliftCoyonedaIso, F.corepresentableBy, corepresentableBy, equivUliftCoyonedaIso
-/
noncomputable def uliftCoyonedaCoreprXIso (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable] :
    uliftCoyoneda.{v}.obj (op F.coreprX) ≅ F :=
  (CorepresentableBy.equivUliftCoyonedaIso F _) F.corepresentableBy

/--
lemma `uliftCoyonedaCoreprXIso_hom_app` / 引理 `uliftCoyonedaCoreprXIso_hom_app`

English:
lemma uliftCoyonedaCoreprXIso_hom_app
  statement: (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
  proof: CorepresentableBy.homEquiv_eq _ _

中文:
引理 uliftCoyonedaCoreprXIso_hom_app
  结论: (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
  证明: CorepresentableBy.homEquiv_eq _ _

Depends on / 依赖: CorepresentableBy, CorepresentableBy.homEquiv_eq, homEquiv_eq
-/
lemma uliftCoyonedaCoreprXIso_hom_app (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
    (X : C) (f : ULift (F.coreprX ⟶ X)) :
    F.uliftCoyonedaCoreprXIso.hom.app X f = F.map f.down F.coreprx :=
  CorepresentableBy.homEquiv_eq _ _

end Corepresentable

/--
lemma `isRepresentable_comp_uliftFunctor_iff` / 引理 `isRepresentable_comp_uliftFunctor_iff`

English:
lemma isRepresentable_comp_uliftFunctor_iff
  given: {F : Cᵒᵖ ⥤ Type v}

中文:
引理 isRepresentable_comp_uliftFunctor_iff
  条件: {F : Cᵒᵖ ⥤ 类型v}
-/
lemma isRepresentable_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsRepresentable ↔ F.IsRepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv.symm R⟩⟩

/--
lemma `isCorepresentable_comp_uliftFunctor_iff` / 引理 `isCorepresentable_comp_uliftFunctor_iff`

English:
lemma isCorepresentable_comp_uliftFunctor_iff
  given: {F : C ⥤ Type v}

中文:
引理 isCorepresentable_comp_uliftFunctor_iff
  条件: {F : C ⥤ 类型v}
-/
lemma isCorepresentable_comp_uliftFunctor_iff {F : C ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsCorepresentable ↔ F.IsCorepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv.symm R⟩⟩

instance (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] : (F ⋙ uliftFunctor.{w}).IsRepresentable :=
  isRepresentable_comp_uliftFunctor_iff.mpr ‹_›

instance (F : C ⥤ Type v) [F.IsCorepresentable] : (F ⋙ uliftFunctor.{w}).IsCorepresentable :=
  isCorepresentable_comp_uliftFunctor_iff.mpr ‹_›

end Functor

/--
theorem `isRepresentable_of_natIso` / 定理 `isRepresentable_of_natIso`

English:
theorem isRepresentable_of_natIso
  given: (F : Cᵒᵖ ⥤ Type v) {G} (i : F ≅ G) [F.IsRepresentable]
  proof: (F.representableBy.ofIso i).isRepresentable

中文:
定理 isRepresentable_of_natIso
  条件: (F : Cᵒᵖ ⥤ 类型v) {G} (i : F ≅ G) [F.IsRepresentable]
  证明: (F.representableBy.ofIso i).isRepresentable

Depends on / 依赖: F.representableBy.ofIso, isRepresentable, representableBy
-/
theorem isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

/--
theorem `corepresentable_of_natIso` / 定理 `corepresentable_of_natIso`

English:
theorem corepresentable_of_natIso
  given: (F : C ⥤ Type v) {G} (i : F ≅ G) [F.IsCorepresentable]
  proof: (F.corepresentableBy.ofIso i).isCorepresentable

中文:
定理 corepresentable_of_natIso
  条件: (F : C ⥤ 类型v) {G} (i : F ≅ G) [F.IsCorepresentable]
  证明: (F.corepresentableBy.ofIso i).isCorepresentable

Depends on / 依赖: F.corepresentableBy.ofIso, corepresentableBy, isCorepresentable
-/
theorem corepresentable_of_natIso (F : C ⥤ Type v) {G} (i : F ≅ G) [F.IsCorepresentable] :
    G.IsCorepresentable :=
  (F.corepresentableBy.ofIso i).isCorepresentable

/--
Definition of `Functor.CorepresentableBy.id` / `Functor.CorepresentableBy.id` 的定义

English:
definition Functor.CorepresentableBy.id
  signature: : (𝟭 (Type v)).CorepresentableBy PUnit
  body: corepresentableByEquiv.symm Coyoneda.punitIso

中文:
定义 Functor.CorepresentableBy.id
  签名: : (𝟭 (类型v)).CorepresentableBy PUnit
  定义体: corepresentableByEquiv.symm Coyoneda.punitIso

Depends on / 依赖: Coyoneda, Coyoneda.punitIso, corepresentableByEquiv, corepresentableByEquiv.symm, punitIso
-/
def Functor.CorepresentableBy.id : (𝟭 (Type v)).CorepresentableBy PUnit :=
  corepresentableByEquiv.symm Coyoneda.punitIso

/--
lemma `Functor.CorepresentableBy.id_homEquiv_apply` / 引理 `Functor.CorepresentableBy.id_homEquiv_apply`

English:
lemma Functor.CorepresentableBy.id_homEquiv_apply
  statement: (X : Type v)
  proof: rfl

中文:
引理 Functor.CorepresentableBy.id_homEquiv_apply
  结论: (X : 类型v)
  证明: rfl
-/
@[simp] lemma Functor.CorepresentableBy.id_homEquiv_apply (X : Type v)
    (a : PUnit ⟶ X) : dsimp% id.homEquiv a = a ⟨⟩ :=
  rfl

/--
lemma `Functor.CorepresentableBy.id_homEquiv_symm_apply` / 引理 `Functor.CorepresentableBy.id_homEquiv_symm_apply`

English:
lemma Functor.CorepresentableBy.id_homEquiv_symm_apply
  statement: (X : Type v) (x : X)
  proof: rfl

中文:
引理 Functor.CorepresentableBy.id_homEquiv_symm_apply
  结论: (X : 类型v) (x : X)
  证明: rfl
-/
@[simp] lemma Functor.CorepresentableBy.id_homEquiv_symm_apply (X : Type v) (x : X)
    (a : PUnit) : dsimp% id.homEquiv.symm x a = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.IsCorepresentable (𝟭 (Type v))
  body: Functor.CorepresentableBy.id.isCorepresentable

中文:
实例 :
  签名: Functor.IsCorepresentable (𝟭 (类型v))
  定义体: Functor.CorepresentableBy.id.isCorepresentable

Depends on / 依赖: CorepresentableBy, Functor, Functor.CorepresentableBy.id.isCorepresentable, isCorepresentable
-/
instance : Functor.IsCorepresentable (𝟭 (Type v)) :=
  Functor.CorepresentableBy.id.isCorepresentable

open Opposite

variable (C)

-- We need to help typeclass inference with some awkward universe levels here.
/--
Instance `prodCategoryInstance1` / 实例 `prodCategoryInstance1`

English:
instance prodCategoryInstance1
  signature: : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ)
  body: CategoryTheory.prod'.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

中文:
实例 prodCategoryInstance1
  签名: : Category ((Cᵒᵖ ⥤ 类型v₁) × Cᵒᵖ)
  定义体: CategoryTheory.prod'.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

Depends on / 依赖: CategoryTheory, CategoryTheory.prod
-/
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod'.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

/--
Instance `prodCategoryInstance2` / 实例 `prodCategoryInstance2`

English:
instance prodCategoryInstance2
  signature: : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁))
  body: CategoryTheory.prod'.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

中文:
实例 prodCategoryInstance2
  签名: : Category (Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁))
  定义体: CategoryTheory.prod'.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

Depends on / 依赖: CategoryTheory, CategoryTheory.prod
-/
instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod'.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
@[implicit_reducible]
/--
Definition of `yonedaEquiv` / `yonedaEquiv` 的定义

English:
definition yonedaEquiv
  signature: {X : C} {F : Cᵒᵖ ⥤ Type v₁}
  body: η.app (op X) (𝟙 X)
  invFun ξ := { app _ := ↾fun f => F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

中文:
定义 yonedaEquiv
  签名: {X : C} {F : Cᵒᵖ ⥤ 类型v₁}
  定义体: η.app (op X) (𝟙 X)
  invFun ξ := { app _ := ↾fun f => F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app _ := ↾fun f => F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

/--
theorem `yonedaEquiv_apply` / 定理 `yonedaEquiv_apply`

English:
theorem yonedaEquiv_apply
  given: {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
  proof: rfl

@[simp]

中文:
定理 yonedaEquiv_apply
  条件: {X : C} {F : Cᵒᵖ ⥤ 类型v₁} (f : yoneda.obj X ⟶ F)
  证明: rfl

@[simp]
-/
theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
/--
theorem `yonedaEquiv_symm_app` / 定理 `yonedaEquiv_symm_app`

English:
theorem yonedaEquiv_symm_app
  given: {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
  proof: rfl

中文:
定理 yonedaEquiv_symm_app
  条件: {X : C} {F : Cᵒᵖ ⥤ 类型v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
  证明: rfl
-/
theorem yonedaEquiv_symm_app {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ) :
    (yonedaEquiv.symm x).app Y = ↾fun f => F.map f.op x :=
  rfl

/--
theorem `yonedaEquiv_symm_app_apply` / 定理 `yonedaEquiv_symm_app_apply`

English:
theorem yonedaEquiv_symm_app_apply
  statement: {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
  proof: rfl

中文:
定理 yonedaEquiv_symm_app_apply
  结论: {X : C} {F : Cᵒᵖ ⥤ 类型v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
  证明: rfl
-/
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : dsimp% (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

/--
lemma `yonedaEquiv_naturality` / 引理 `yonedaEquiv_naturality`

English:
lemma yonedaEquiv_naturality
  statement: {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
  proof: by
  simp [yonedaEquiv, ← f.naturality_apply]

中文:
引理 yonedaEquiv_naturality
  结论: {X Y : C} {F : Cᵒᵖ ⥤ 类型v₁} (f : yoneda.obj X ⟶ F)
  证明: by
  simp [yonedaEquiv, ← f.naturality_apply]

Depends on / 依赖: f.naturality_apply, naturality_apply, yonedaEquiv
-/
lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  simp [yonedaEquiv, ← f.naturality_apply]

/--
lemma `yonedaEquiv_naturality'` / 引理 `yonedaEquiv_naturality'`

English:
lemma yonedaEquiv_naturality'
  statement: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
  proof: yonedaEquiv_naturality _ _

中文:
引理 yonedaEquiv_naturality'
  结论: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ 类型v₁} (f : yoneda.obj (unop X) ⟶ F)
  证明: yonedaEquiv_naturality _ _

Depends on / 依赖: yonedaEquiv_naturality
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

/--
lemma `yonedaEquiv_comp` / 引理 `yonedaEquiv_comp`

English:
lemma yonedaEquiv_comp
  given: {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G)
  proof: rfl

中文:
引理 yonedaEquiv_comp
  条件: {X : C} {F G : Cᵒᵖ ⥤ 类型v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G)
  证明: rfl
-/
lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

/--
lemma `yonedaEquiv_yoneda_map` / 引理 `yonedaEquiv_yoneda_map`

English:
lemma yonedaEquiv_yoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  statement: yonedaEquiv (yoneda.map f) = f
  proof: by
  rw [yonedaEquiv_apply]
  simp

中文:
引理 yonedaEquiv_yoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  结论: yonedaEquiv (yoneda.map f) = f
  证明: by
  rw [yonedaEquiv_apply]
  simp

Depends on / 依赖: yonedaEquiv_apply
-/
lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `yonedaEquiv_symm_naturality_left` / 引理 `yonedaEquiv_symm_naturality_left`

English:
lemma yonedaEquiv_symm_naturality_left
  statement: {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v₁)
  proof: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv]

中文:
引理 yonedaEquiv_symm_naturality_left
  结论: {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ 类型v₁)
  证明: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv]

Depends on / 依赖: injective, yonedaEquiv, yonedaEquiv.injective
-/
lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v₁)
    (x : F.obj ⟨X⟩) : yoneda.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm ((F.map f.op) x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv]

/--
lemma `yonedaEquiv_symm_naturality_right` / 引理 `yonedaEquiv_symm_naturality_right`

English:
lemma yonedaEquiv_symm_naturality_right
  statement: (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ F')
  proof: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

中文:
引理 yonedaEquiv_symm_naturality_right
  结论: (X : C) {F F' : Cᵒᵖ ⥤ 类型v₁} (f : F ⟶ F')
  证明: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

Depends on / 依赖: injective, yonedaEquiv, yonedaEquiv.injective, yonedaEquiv_comp
-/
lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ F')
    (x : F.obj ⟨X⟩) : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app ⟨X⟩ x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/--
lemma `map_yonedaEquiv` / 引理 `map_yonedaEquiv`

English:
lemma map_yonedaEquiv
  statement: {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
  proof: by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

中文:
引理 map_yonedaEquiv
  结论: {X Y : C} {F : Cᵒᵖ ⥤ 类型v₁} (f : yoneda.obj X ⟶ F)
  证明: by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

Depends on / 依赖: yonedaEquiv_comp, yonedaEquiv_naturality, yonedaEquiv_yoneda_map
-/
lemma map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g := by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

/--
lemma `map_yonedaEquiv'` / 引理 `map_yonedaEquiv'`

English:
lemma map_yonedaEquiv'
  statement: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
  proof: by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

中文:
引理 map_yonedaEquiv'
  结论: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ 类型v₁} (f : yoneda.obj (unop X) ⟶ F)
  证明: by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

Depends on / 依赖: yonedaEquiv_comp, yonedaEquiv_naturality, yonedaEquiv_yoneda_map
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop := by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

/--
lemma `yonedaEquiv_symm_map` / 引理 `yonedaEquiv_symm_map`

English:
lemma yonedaEquiv_symm_map
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X)
  proof: by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

中文:
引理 yonedaEquiv_symm_map
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ 类型v₁} (t : F.obj X)
  证明: by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, surjective, symm_apply_apply, yonedaEquiv, yonedaEquiv.surjective, yonedaEquiv_naturality
-/
lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

/--
lemma `hom_ext_yoneda` / 引理 `hom_ext_yoneda`

English:
lemma hom_ext_yoneda
  statement: {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
  proof: by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

中文:
引理 hom_ext_yoneda
  结论: {P Q : Cᵒᵖ ⥤ 类型v₁} {f g : P ⟶ Q}
  证明: by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, congr_arg, yonedaEquiv, yonedaEquiv.symm, yonedaEquiv_comp
-/
lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : forall (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

/--
Definition of `yonedaEvaluation` / `yonedaEvaluation` 的定义

English:
definition yonedaEvaluation
  signature: : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)
  body: evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]

中文:
定义 yonedaEvaluation
  签名: : Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁) ⥤ Type (max u₁ v₁)
  定义体: evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]

Depends on / 依赖: evaluationUncurried, uliftFunctor
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
/--
theorem `yonedaEvaluation_map_down` / 定理 `yonedaEvaluation_map_down`

English:
theorem yonedaEvaluation_map_down
  statement: (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
  proof: rfl

中文:
定理 yonedaEvaluation_map_down
  结论: (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁)) (α : P ⟶ Q)
  证明: rfl
-/
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/--
Definition of `yonedaPairing` / `yonedaPairing` 的定义

English:
definition yonedaPairing
  signature: : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁)
  body: Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]

中文:
定义 yonedaPairing
  签名: : Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁) ⥤ Type (max u₁ v₁)
  定义体: Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]

Depends on / 依赖: Functor, Functor.hom, Functor.prod, yoneda, yoneda.op
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]
/--
lemma `yonedaPairingExt` / 引理 `yonedaPairingExt`

English:
lemma yonedaPairingExt
  statement: {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
  proof: NatTrans.ext (funext w)

@[simp]

中文:
引理 yonedaPairingExt
  结论: {X : Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁)} {x y : (yonedaPairing C).obj X}
  证明: NatTrans.ext (funext w)

@[simp]

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : forall Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
/--
theorem `yonedaPairing_map` / 定理 `yonedaPairing_map`

English:
theorem yonedaPairing_map
  given: (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
  proof: rfl

中文:
定理 yonedaPairing_map
  条件: (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ 类型v₁)) (α : P ⟶ Q)
  证明: rfl
-/
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) :
    (yonedaPairing C).map α = ↾fun β => yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
/--
Definition of `yonedaLemma` / `yonedaLemma` 的定义

English:
definition yonedaLemma
  signature: : yonedaPairing C ≅ yonedaEvaluation C
  body: NatIso.ofComponents
    (fun _ => Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        dsimp [yonedaEvaluation, yonedaEquiv]
        simp [← NatTrans.naturality_apply])

中文:
定义 yonedaLemma
  签名: : yonedaPairing C ≅ yonedaEvaluation C
  定义体: NatIso.ofComponents
    (fun _ => Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        dsimp [yonedaEvaluation, yonedaEquiv]
        simp [← NatTrans.naturality_apply])

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, ULift.ext, X.unop, naturality_apply, ofComponents, yoneda, yoneda.obj, yonedaEquiv, yonedaEquiv.trans, yonedaEvaluation
-/
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        dsimp [yonedaEvaluation, yonedaEquiv]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/--
Definition of `curriedYonedaLemma` / `curriedYonedaLemma` 的定义

English:
definition curriedYonedaLemma
  signature: {C : Type u₁} [SmallCategory C]
  body: NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [yonedaEquiv, ← NatTrans.naturality_apply])

中文:
定义 curriedYonedaLemma
  签名: {C : 类型u₁} [SmallCategory C]
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [yonedaEquiv, ← NatTrans.naturality_apply])

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, naturality_apply, ofComponents, yonedaEquiv
-/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅
      evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [yonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `largeCurriedYonedaLemma` / `largeCurriedYonedaLemma` 的定义

English:
definition largeCurriedYonedaLemma
  signature: {C : Type u₁} [Category.{v₁} C]
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        simp [yonedaEquiv]))
    (by
      intro Y Z f
      ext F g
      simpa [← ULift.down_inj] using! (yonedaEquiv_naturality _ _)

中文:
定义 largeCurriedYonedaLemma
  签名: {C : 类型u₁} [Category.{v₁} C]
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        simp [yonedaEquiv]))
    (by
      intro Y Z f
      ext F g
      simpa [← ULift.down_inj] using! (yonedaEquiv_naturality _ _)

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, ULift.down_inj, down_inj, ofComponents, yonedaEquiv, yonedaEquiv.trans, yonedaEquiv_naturality
-/
def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        simp [yonedaEquiv]))
    (by
      intro Y Z f
      ext F g
      simpa [← ULift.down_inj] using! (yonedaEquiv_naturality _ _).symm)

/--
Definition of `yonedaOpCompYonedaObj` / `yonedaOpCompYonedaObj` 的定义

English:
definition yonedaOpCompYonedaObj
  signature: {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁)
  body: isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

中文:
定义 yonedaOpCompYonedaObj
  签名: {C : 类型u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ 类型v₁)
  定义体: isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

Depends on / 依赖: evaluation, isoWhiskerRight, largeCurriedYonedaLemma
-/
def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `curriedYonedaLemma'` / `curriedYonedaLemma'` 的定义

English:
definition curriedYonedaLemma'
  signature: {C : Type u₁} [SmallCategory C]
  body: NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← NatTrans.naturality_apply]))

中文:
定义 curriedYonedaLemma'
  签名: {C : 类型u₁} [SmallCategory C]
  定义体: NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← NatTrans.naturality_apply]))

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, naturality_apply, ofComponents, yonedaEquiv
-/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← NatTrans.naturality_apply]))

/--
lemma `isIso_of_yoneda_map_bijective` / 引理 `isIso_of_yoneda_map_bijective`

English:
lemma isIso_of_yoneda_map_bijective
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by cat_disch), hg⟩

中文:
引理 isIso_of_yoneda_map_bijective
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by cat_disch), hg⟩

Depends on / 依赖: cat_disch
-/
lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : forall (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by cat_disch), hg⟩

/--
lemma `isIso_iff_yoneda_map_bijective` / 引理 `isIso_iff_yoneda_map_bijective`

English:
lemma isIso_iff_yoneda_map_bijective
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun _ => ?_, fun hf => isIso_of_yoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))

中文:
引理 isIso_iff_yoneda_map_bijective
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun _ => ?_, fun hf => isIso_of_yoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))

Depends on / 依赖: bijective_iff_isIso_ofHom, isIso_of_yoneda_map_bijective, yoneda, yoneda.map
-/
lemma isIso_iff_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (forall (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) := by
  refine ⟨fun _ => ?_, fun hf => isIso_of_yoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))

/--
lemma `isIso_iff_isIso_yoneda_map` / 引理 `isIso_iff_isIso_yoneda_map`

English:
lemma isIso_iff_isIso_yoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ => (bijective_iff_isIso_ofHom _)

中文:
引理 isIso_iff_isIso_yoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ => (bijective_iff_isIso_ofHom _)

Depends on / 依赖: bijective_iff_isIso_ofHom, forall_congr, isIso_iff_yoneda_map_bijective
-/
lemma isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ forall c : C, IsIso ((yoneda.map f).app ⟨c⟩) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ => (bijective_iff_isIso_ofHom _)

set_option backward.defeqAttrib.useBackward true in
/-- Yoneda's lemma as a bijection `(uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
/--
Definition of `uliftYonedaEquiv` / `uliftYonedaEquiv` 的定义

English:
definition uliftYonedaEquiv
  signature: {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)}
  body: τ.app (op X) (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down.op x }
  left_inv τ := by
    ext ⟨Y⟩ ⟨y⟩
    simp [← NatTrans.naturality_apply]
  right_inv x := by simp

中文:
定义 uliftYonedaEquiv
  签名: {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)}
  定义体: τ.app (op X) (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down.op x }
  left_inv τ := by
    ext ⟨Y⟩ ⟨y⟩
    simp [← NatTrans.naturality_apply]
  right_inv x := by simp

Depends on / 依赖: ULift.up
-/
def uliftYonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)} :
    (uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X) where
  toFun τ := τ.app (op X) (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down.op x }
  left_inv τ := by
    ext ⟨Y⟩ ⟨y⟩
    simp [← NatTrans.naturality_apply]
  right_inv x := by simp

attribute [simp] uliftYonedaEquiv_symm_apply_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `uliftYonedaEquiv_naturality` / 引理 `uliftYonedaEquiv_naturality`

English:
lemma uliftYonedaEquiv_naturality
  statement: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)}
  proof: by
  simp [uliftYonedaEquiv, uliftYoneda, ← f.naturality_apply]

中文:
引理 uliftYonedaEquiv_naturality
  结论: {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)}
  证明: by
  simp [uliftYonedaEquiv, uliftYoneda, ← f.naturality_apply]

Depends on / 依赖: f.naturality_apply, naturality_apply, uliftYoneda, uliftYonedaEquiv
-/
lemma uliftYonedaEquiv_naturality {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftYonedaEquiv.{w} f) = uliftYonedaEquiv.{w} (uliftYoneda.map g.unop ≫ f) := by
  simp [uliftYonedaEquiv, uliftYoneda, ← f.naturality_apply]

/--
lemma `uliftYonedaEquiv_comp` / 引理 `uliftYonedaEquiv_comp`

English:
lemma uliftYonedaEquiv_comp
  statement: {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)}
  proof: rfl

@[reassoc]

中文:
引理 uliftYonedaEquiv_comp
  结论: {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)}
  证明: rfl

@[reassoc]
-/
lemma uliftYonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)}
    (α : uliftYoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftYonedaEquiv.{w} (α ≫ β) = β.app _ (uliftYonedaEquiv α) :=
  rfl

@[reassoc]
/--
lemma `uliftYonedaEquiv_symm_map` / 引理 `uliftYonedaEquiv_symm_map`

English:
lemma uliftYonedaEquiv_symm_map
  statement: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v₁)}
  proof: by
  obtain ⟨u, rfl⟩ := uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality]
  simp

@[reassoc]

中文:
引理 uliftYonedaEquiv_symm_map
  结论: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v₁)}
  证明: by
  obtain ⟨u, rfl⟩ := uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality]
  simp

@[reassoc]

Depends on / 依赖: surjective, uliftYonedaEquiv, uliftYonedaEquiv.surjective, uliftYonedaEquiv_naturality
-/
lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftYonedaEquiv.{w}.symm (F.map f t) =
      uliftYoneda.map f.unop ≫ uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality]
  simp

@[reassoc]
/--
lemma `uliftYonedaEquiv_symm_comp` / 引理 `uliftYonedaEquiv_symm_comp`

English:
lemma uliftYonedaEquiv_symm_comp
  proof: uliftYonedaEquiv.injective (by rw [uliftYonedaEquiv_comp]; simp)

中文:
引理 uliftYonedaEquiv_symm_comp
  证明: uliftYonedaEquiv.injective (by rw [uliftYonedaEquiv_comp]; simp)

Depends on / 依赖: injective, uliftYonedaEquiv, uliftYonedaEquiv.injective, uliftYonedaEquiv_comp
-/
lemma uliftYonedaEquiv_symm_comp
    {F G : Cᵒᵖ ⥤ Type max w v₁} {X : Cᵒᵖ} (x : F.obj X) (f : F ⟶ G) :
    uliftYonedaEquiv.symm x ≫ f = uliftYonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv.injective (by rw [uliftYonedaEquiv_comp]; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `uliftYonedaEquiv_uliftYoneda_map` / 引理 `uliftYonedaEquiv_uliftYoneda_map`

English:
lemma uliftYonedaEquiv_uliftYoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [uliftYonedaEquiv, uliftYoneda]

中文:
引理 uliftYonedaEquiv_uliftYoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [uliftYonedaEquiv, uliftYoneda]
-/
lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ => ULift.{w} (X ⟶ Y))
        uliftYonedaEquiv.{w} (uliftYoneda.map f) = ULift.up f := by
  simp [uliftYonedaEquiv, uliftYoneda]

/--
lemma `hom_ext_uliftYoneda` / 引理 `hom_ext_uliftYoneda`

English:
lemma hom_ext_uliftYoneda
  statement: {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q}
  proof: by
  ext X x
  simpa [-op_unop, uliftYonedaEquiv_comp] using
    congr_arg uliftYonedaEquiv.{w} (h _ (uliftYonedaEquiv.symm x))

中文:
引理 hom_ext_uliftYoneda
  结论: {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q}
  证明: by
  ext X x
  simpa [-op_unop, uliftYonedaEquiv_comp] using
    congr_arg uliftYonedaEquiv.{w} (h _ (uliftYonedaEquiv.symm x))

Depends on / 依赖: congr_arg, op_unop, uliftYonedaEquiv, uliftYonedaEquiv.symm, uliftYonedaEquiv_comp
-/
lemma hom_ext_uliftYoneda {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : forall (X : C) (p : uliftYoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [-op_unop, uliftYonedaEquiv_comp] using
    congr_arg uliftYonedaEquiv.{w} (h _ (uliftYonedaEquiv.symm x))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `uliftYonedaOpCompCoyoneda` / `uliftYonedaOpCompCoyoneda` 的定义

English:
definition uliftYonedaOpCompCoyoneda
  signature: {C : Type u₁} [Category.{v₁} C]
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftYonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftYonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [

中文:
定义 uliftYonedaOpCompCoyoneda
  签名: {C : 类型u₁} [Category.{v₁} C]
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftYonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftYonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, ULift.down_inj, down_inj, intros, ofComponents, uliftYonedaEquiv, uliftYonedaEquiv.trans, uliftYonedaEquiv_comp, uliftYonedaEquiv_naturality
-/
def uliftYonedaOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftYoneda.{w}.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftYonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftYonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftYonedaEquiv_naturality _ _).symm)

end YonedaLemma

section CoyonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the coyoneda embedding
and elements of `F.obj X.unop`, without any universe switching.
-/
@[implicit_reducible]
/--
Definition of `coyonedaEquiv` / `coyonedaEquiv` 的定义

English:
definition coyonedaEquiv
  signature: {X : C} {F : C ⥤ Type v₁}
  body: η.app X (𝟙 X)
  invFun ξ := { app _ := ↾fun x => F.map x ξ }
  left_inv := fun η => by
    ext Y (x : X ⟶ Y)
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

中文:
定义 coyonedaEquiv
  签名: {X : C} {F : C ⥤ 类型v₁}
  定义体: η.app X (𝟙 X)
  invFun ξ := { app _ := ↾fun x => F.map x ξ }
  left_inv := fun η => by
    ext Y (x : X ⟶ Y)
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp
-/
def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X where
  toFun η := η.app X (𝟙 X)
  invFun ξ := { app _ := ↾fun x => F.map x ξ }
  left_inv := fun η => by
    ext Y (x : X ⟶ Y)
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

/--
theorem `coyonedaEquiv_apply` / 定理 `coyonedaEquiv_apply`

English:
theorem coyonedaEquiv_apply
  given: {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
  proof: rfl

@[simp]

中文:
定理 coyonedaEquiv_apply
  条件: {X : C} {F : C ⥤ 类型v₁} (f : coyoneda.obj (op X) ⟶ F)
  证明: rfl

@[simp]
-/
theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
/--
theorem `coyonedaEquiv_symm_app_apply` / 定理 `coyonedaEquiv_symm_app_apply`

English:
theorem coyonedaEquiv_symm_app_apply
  statement: {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
  proof: rfl

中文:
定理 coyonedaEquiv_symm_app_apply
  结论: {X : C} {F : C ⥤ 类型v₁} (x : F.obj X) (Y : C)
  证明: rfl
-/
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : dsimp% (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

/--
lemma `coyonedaEquiv_naturality` / 引理 `coyonedaEquiv_naturality`

English:
lemma coyonedaEquiv_naturality
  statement: {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
  proof: by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  simp

中文:
引理 coyonedaEquiv_naturality
  结论: {X Y : C} {F : C ⥤ 类型v₁} (f : coyoneda.obj (op X) ⟶ F)
  证明: by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  simp

Depends on / 依赖: F.map, f.app, f.naturality, naturality
-/
lemma coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g.op ≫ f) := by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  simp

/--
lemma `coyonedaEquiv_comp` / 引理 `coyonedaEquiv_comp`

English:
lemma coyonedaEquiv_comp
  given: {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G)
  proof: by
  rfl

中文:
引理 coyonedaEquiv_comp
  条件: {X : C} {F G : C ⥤ 类型v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G)
  证明: by
  rfl
-/
lemma coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) :
    coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α) := by
  rfl

/--
lemma `coyonedaEquiv_coyoneda_map` / 引理 `coyonedaEquiv_coyoneda_map`

English:
lemma coyonedaEquiv_coyoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [coyonedaEquiv_apply]
  simp

中文:
引理 coyonedaEquiv_coyoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [coyonedaEquiv_apply]
  simp

Depends on / 依赖: coyonedaEquiv_apply
-/
lemma coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    coyonedaEquiv (coyoneda.map f.op) = f := by
  rw [coyonedaEquiv_apply]
  simp

/--
lemma `map_coyonedaEquiv` / 引理 `map_coyonedaEquiv`

English:
lemma map_coyonedaEquiv
  statement: {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
  proof: by
  rw [coyonedaEquiv_naturality]; rw [coyonedaEquiv_comp]; rw [coyonedaEquiv_coyoneda_map]

中文:
引理 map_coyonedaEquiv
  结论: {X Y : C} {F : C ⥤ 类型v₁} (f : coyoneda.obj (op X) ⟶ F)
  证明: by
  rw [coyonedaEquiv_naturality]; rw [coyonedaEquiv_comp]; rw [coyonedaEquiv_coyoneda_map]

Depends on / 依赖: coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map, coyonedaEquiv_naturality
-/
lemma map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g := by
  rw [coyonedaEquiv_naturality]; rw [coyonedaEquiv_comp]; rw [coyonedaEquiv_coyoneda_map]

/--
lemma `coyonedaEquiv_symm_map` / 引理 `coyonedaEquiv_symm_map`

English:
lemma coyonedaEquiv_symm_map
  given: {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X)
  proof: by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

中文:
引理 coyonedaEquiv_symm_map
  条件: {X Y : C} (f : X ⟶ Y) {F : C ⥤ 类型v₁} (t : F.obj X)
  证明: by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

Depends on / 依赖: coyonedaEquiv, coyonedaEquiv.surjective, coyonedaEquiv_naturality, surjective
-/
lemma coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X) :
    coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

variable (C)

/--
Definition of `coyonedaEvaluation` / `coyonedaEvaluation` 的定义

English:
definition coyonedaEvaluation
  signature: : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁)
  body: evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]

中文:
定义 coyonedaEvaluation
  签名: : C × (C ⥤ 类型v₁) ⥤ Type (max u₁ v₁)
  定义体: evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]

Depends on / 依赖: evaluationUncurried, uliftFunctor
-/
def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]
/--
theorem `coyonedaEvaluation_map_down` / 定理 `coyonedaEvaluation_map_down`

English:
theorem coyonedaEvaluation_map_down
  statement: (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
  proof: rfl

中文:
定理 coyonedaEvaluation_map_down
  结论: (P Q : C × (C ⥤ 类型v₁)) (α : P ⟶ Q)
  证明: rfl
-/
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/--
Definition of `coyonedaPairing` / `coyonedaPairing` 的定义

English:
definition coyonedaPairing
  signature: : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁)
  body: Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]

中文:
定义 coyonedaPairing
  签名: : C × (C ⥤ 类型v₁) ⥤ Type (max u₁ v₁)
  定义体: Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]

Depends on / 依赖: Functor, Functor.hom, Functor.prod, coyoneda, coyoneda.rightOp, rightOp
-/
def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]
/--
lemma `coyonedaPairingExt` / 引理 `coyonedaPairingExt`

English:
lemma coyonedaPairingExt
  statement: {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
  proof: NatTrans.ext (funext w)

@[simp]

中文:
引理 coyonedaPairingExt
  结论: {X : C × (C ⥤ 类型v₁)} {x y : (coyonedaPairing C).obj X}
  证明: NatTrans.ext (funext w)

@[simp]

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : forall Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
/--
theorem `coyonedaPairing_map` / 定理 `coyonedaPairing_map`

English:
theorem coyonedaPairing_map
  given: (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P)
  proof: rfl

中文:
定理 coyonedaPairing_map
  条件: (P Q : C × (C ⥤ 类型v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P)
  证明: rfl
-/
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Coyoneda lemma asserts that the Coyoneda pairing
`(X : C, F : C ⥤ Type) ↦ (coyoneda.obj X ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
/--
Definition of `coyonedaLemma` / `coyonedaLemma` 的定义

English:
definition coyonedaLemma
  signature: : coyonedaPairing C ≅ coyonedaEvaluation C
  body: NatIso.ofComponents
    (fun _ => Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        dsimp [coyonedaEquiv, coyonedaEvaluation]
        simp [← NatTrans.naturality_apply])

中文:
定义 coyonedaLemma
  签名: : coyonedaPairing C ≅ coyonedaEvaluation C
  定义体: NatIso.ofComponents
    (fun _ => Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        dsimp [coyonedaEquiv, coyonedaEvaluation]
        simp [← NatTrans.naturality_apply])

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, ULift.ext, coyoneda, coyoneda.obj, coyonedaEquiv, coyonedaEquiv.trans, coyonedaEvaluation, naturality_apply, ofComponents
-/
def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        dsimp [coyonedaEquiv, coyonedaEvaluation]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/--
Definition of `curriedCoyonedaLemma` / `curriedCoyonedaLemma` 的定义

English:
definition curriedCoyonedaLemma
  signature: {C : Type u₁} [SmallCategory C]
  body: NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← NatTrans.naturality_apply])

中文:
定义 curriedCoyonedaLemma
  签名: {C : 类型u₁} [SmallCategory C]
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← NatTrans.naturality_apply])

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, coyonedaEquiv, naturality_apply, ofComponents
-/
def curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `largeCurriedCoyonedaLemma` / `largeCurriedCoyonedaLemma` 的定义

English:
definition largeCurriedCoyonedaLemma
  signature: {C : Type u₁} [Category.{v₁} C]
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.

中文:
定义 largeCurriedCoyonedaLemma
  签名: {C : 类型u₁} [Category.{v₁} C]
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, ULift.down_inj, coyonedaEquiv, coyonedaEquiv.trans, coyonedaEquiv_comp, coyonedaEquiv_naturality, down_inj, ofComponents
-/
def largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] :
    coyoneda.rightOp ⋙ coyoneda ≅
      evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (coyonedaEquiv_naturality _ _).symm)

/--
Definition of `coyonedaCompYonedaObj` / `coyonedaCompYonedaObj` 的定义

English:
definition coyonedaCompYonedaObj
  signature: {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁)
  body: isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

中文:
定义 coyonedaCompYonedaObj
  签名: {C : 类型u₁} [Category.{v₁} C] (P : C ⥤ 类型v₁)
  定义体: isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

Depends on / 依赖: evaluation, isoWhiskerRight, largeCurriedCoyonedaLemma
-/
def coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) :
    coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `curriedCoyonedaLemma'` / `curriedCoyonedaLemma'` 的定义

English:
definition curriedCoyonedaLemma'
  signature: {C : Type u₁} [SmallCategory C]
  body: NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← NatTrans.naturality_apply]))

中文:
定义 curriedCoyonedaLemma'
  签名: {C : 类型u₁} [SmallCategory C]
  定义体: NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← NatTrans.naturality_apply]))

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_apply, coyonedaEquiv, naturality_apply, ofComponents
-/
def curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp
      ≅ 𝟭 (C ⥤ Type u₁) :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← NatTrans.naturality_apply]))

/--
lemma `isIso_of_coyoneda_map_bijective` / 引理 `isIso_of_coyoneda_map_bijective`

English:
lemma isIso_of_coyoneda_map_bijective
  statement: {X Y : C} (f : X ⟶ Y)
  proof: by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

中文:
引理 isIso_of_coyoneda_map_bijective
  结论: {X Y : C} (f : X ⟶ Y)
  证明: by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, comp_id, id_comp
-/
lemma isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : forall (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) :
    IsIso f := by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

/--
lemma `isIso_iff_coyoneda_map_bijective` / 引理 `isIso_iff_coyoneda_map_bijective`

English:
lemma isIso_iff_coyoneda_map_bijective
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun _ => ?_, fun hf => isIso_of_coyoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))

中文:
引理 isIso_iff_coyoneda_map_bijective
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun _ => ?_, fun hf => isIso_of_coyoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))

Depends on / 依赖: bijective_iff_isIso_ofHom, coyoneda, coyoneda.map, f.op, isIso_of_coyoneda_map_bijective
-/
lemma isIso_iff_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (forall (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) := by
  refine ⟨fun _ => ?_, fun hf => isIso_of_coyoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))

/--
lemma `isIso_iff_isIso_coyoneda_map` / 引理 `isIso_iff_isIso_coyoneda_map`

English:
lemma isIso_iff_isIso_coyoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ => bijective_iff_isIso_ofHom _

中文:
引理 isIso_iff_isIso_coyoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ => bijective_iff_isIso_ofHom _

Depends on / 依赖: bijective_iff_isIso_ofHom, forall_congr, isIso_iff_coyoneda_map_bijective
-/
lemma isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ forall c : C, IsIso ((coyoneda.map f.op).app c) := by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ => bijective_iff_isIso_ofHom _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Coyoneda's lemma as a bijection `(uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
/--
Definition of `uliftCoyonedaEquiv` / `uliftCoyonedaEquiv` 的定义

English:
definition uliftCoyonedaEquiv
  signature: {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)}
  body: τ.app X.unop (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down x }
  left_inv τ := by
    ext Y ⟨x⟩
    simp [← comp_apply, ← τ.naturality]
  right_inv x := by simp

中文:
定义 uliftCoyonedaEquiv
  签名: {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)}
  定义体: τ.app X.unop (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down x }
  left_inv τ := by
    ext Y ⟨x⟩
    simp [← comp_apply, ← τ.naturality]
  right_inv x := by simp

Depends on / 依赖: ULift.up, X.unop
-/
def uliftCoyonedaEquiv {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)} :
    (uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj X.unop where
  toFun τ := τ.app X.unop (ULift.up (𝟙 _))
  invFun x := { app Y := ↾fun y => F.map y.down x }
  left_inv τ := by
    ext Y ⟨x⟩
    simp [← comp_apply, ← τ.naturality]
  right_inv x := by simp

attribute [simp] uliftCoyonedaEquiv_symm_apply_app

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `uliftCoyonedaEquiv_naturality` / 引理 `uliftCoyonedaEquiv_naturality`

English:
lemma uliftCoyonedaEquiv_naturality
  statement: {X Y : C} {F : C ⥤ Type max w v₁}
  proof: by
  simp [uliftCoyonedaEquiv, ← comp_apply, ← f.naturality]

中文:
引理 uliftCoyonedaEquiv_naturality
  结论: {X Y : C} {F : C ⥤ Type max w v₁}
  证明: by
  simp [uliftCoyonedaEquiv, ← comp_apply, ← f.naturality]

Depends on / 依赖: comp_apply, f.naturality, naturality, uliftCoyonedaEquiv
-/
lemma uliftCoyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type max w v₁}
    (f : uliftCoyoneda.{w}.obj (op X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftCoyonedaEquiv.{w} f) = uliftCoyonedaEquiv.{w} (uliftCoyoneda.map g.op ≫ f) := by
  simp [uliftCoyonedaEquiv, ← comp_apply, ← f.naturality]

/--
lemma `uliftCoyonedaEquiv_comp` / 引理 `uliftCoyonedaEquiv_comp`

English:
lemma uliftCoyonedaEquiv_comp
  statement: {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)}
  proof: rfl

@[reassoc]

中文:
引理 uliftCoyonedaEquiv_comp
  结论: {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)}
  证明: rfl

@[reassoc]
-/
lemma uliftCoyonedaEquiv_comp {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)}
    (α : uliftCoyoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftCoyonedaEquiv.{w} (α ≫ β) = β.app _ (uliftCoyonedaEquiv α) :=
  rfl

@[reassoc]
/--
lemma `uliftCoyonedaEquiv_symm_map` / 引理 `uliftCoyonedaEquiv_symm_map`

English:
lemma uliftCoyonedaEquiv_symm_map
  statement: {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)}
  proof: by
  obtain ⟨u, rfl⟩ := uliftCoyonedaEquiv.surjective t
  rw [uliftCoyonedaEquiv_naturality]
  simp

中文:
引理 uliftCoyonedaEquiv_symm_map
  结论: {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)}
  证明: by
  obtain ⟨u, rfl⟩ := uliftCoyonedaEquiv.surjective t
  rw [uliftCoyonedaEquiv_naturality]
  simp

Depends on / 依赖: surjective, uliftCoyonedaEquiv, uliftCoyonedaEquiv.surjective, uliftCoyonedaEquiv_naturality
-/
lemma uliftCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftCoyonedaEquiv.{w}.symm (F.map f t) =
      uliftCoyoneda.map f.op ≫ uliftCoyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftCoyonedaEquiv.surjective t
  rw [uliftCoyonedaEquiv_naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `uliftCoyonedaEquiv_uliftCoyoneda_map` / 引理 `uliftCoyonedaEquiv_uliftCoyoneda_map`

English:
lemma uliftCoyonedaEquiv_uliftCoyoneda_map
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  simp [uliftCoyonedaEquiv, uliftYoneda]

中文:
引理 uliftCoyonedaEquiv_uliftCoyoneda_map
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  simp [uliftCoyonedaEquiv, uliftYoneda]

Depends on / 依赖: X.unop, Y.unop
-/
lemma uliftCoyonedaEquiv_uliftCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ => ULift.{w} (Y.unop ⟶ X.unop))
        uliftCoyonedaEquiv.{w} (uliftCoyoneda.map f) = ULift.up f.unop := by
  simp [uliftCoyonedaEquiv, uliftYoneda]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hom_ext_uliftCoyoneda` / 引理 `hom_ext_uliftCoyoneda`

English:
lemma hom_ext_uliftCoyoneda
  statement: {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q}
  proof: by
  ext X x
  simpa [uliftCoyonedaEquiv]
    using congr_arg uliftCoyonedaEquiv.{w} (h _ (uliftCoyonedaEquiv.symm x))

中文:
引理 hom_ext_uliftCoyoneda
  结论: {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q}
  证明: by
  ext X x
  simpa [uliftCoyonedaEquiv]
    using congr_arg uliftCoyonedaEquiv.{w} (h _ (uliftCoyonedaEquiv.symm x))

Depends on / 依赖: congr_arg, uliftCoyonedaEquiv, uliftCoyonedaEquiv.symm
-/
lemma hom_ext_uliftCoyoneda {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : forall (X : Cᵒᵖ) (p : uliftCoyoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [uliftCoyonedaEquiv]
    using congr_arg uliftCoyonedaEquiv.{w} (h _ (uliftCoyonedaEquiv.symm x))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `uliftCoyonedaRightOpCompCoyoneda` / `uliftCoyonedaRightOpCompCoyoneda` 的定义

English:
definition uliftCoyonedaRightOpCompCoyoneda
  signature: {C : Type u₁} [Category.{v₁} C]
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftCoyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftCoyonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      

中文:
定义 uliftCoyonedaRightOpCompCoyoneda
  签名: {C : 类型u₁} [Category.{v₁} C]
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftCoyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftCoyonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, ULift.down_inj, down_inj, intros, ofComponents, uliftCoyonedaEquiv, uliftCoyonedaEquiv.trans, uliftCoyonedaEquiv_comp, uliftCoyonedaEquiv_naturality
-/
def uliftCoyonedaRightOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftCoyoneda.{w}.rightOp ⋙ coyoneda ≅
      evaluation C (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftCoyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftCoyonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftCoyonedaEquiv_naturality _ _).symm)

end CoyonedaLemma

section

variable {C}
variable {D : Type*} [Category.{v₁} D] (F : C ⥤ D)

/--
Definition of `yonedaMap` / `yonedaMap` 的定义

English:
definition yonedaMap
  signature: (X : C)
  body: ↾fun f => F.map f

@[simp]

中文:
定义 yonedaMap
  签名: (X : C)
  定义体: ↾fun f => F.map f

@[simp]

Depends on / 依赖: F.map
-/
def yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where
  app _ := ↾fun f => F.map f

@[simp]
/--
lemma `yonedaMap_app_apply` / 引理 `yonedaMap_app_apply`

English:
lemma yonedaMap_app_apply
  given: {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y)
  proof: rfl

中文:
引理 yonedaMap_app_apply
  条件: {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y)
  证明: rfl
-/
lemma yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (yonedaMap F Y).app X f = F.map f := rfl

end

section

variable {C}
variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/--
Definition of `uliftYonedaMap` / `uliftYonedaMap` 的定义

English:
definition uliftYonedaMap
  signature: (X : C)
  body: ↾fun f => ULift.up (F.map (ULift.down f))

@[simp]

中文:
定义 uliftYonedaMap
  签名: (X : C)
  定义体: ↾fun f => ULift.up (F.map (ULift.down f))

@[simp]

Depends on / 依赖: F.map, ULift.down, ULift.up
-/
def uliftYonedaMap (X : C) :
    uliftYoneda.{max w v₂}.obj X ⟶ F.op ⋙ uliftYoneda.{max w v₁}.obj (F.obj X) where
  app _ := ↾fun f => ULift.up (F.map (ULift.down f))

@[simp]
/--
lemma `uliftYonedaMap_app_apply` / 引理 `uliftYonedaMap_app_apply`

English:
lemma uliftYonedaMap_app_apply
  given: {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y)
  proof: rfl

中文:
引理 uliftYonedaMap_app_apply
  条件: {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y)
  证明: rfl
-/
lemma uliftYonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (uliftYonedaMap.{w} F Y).app X (ULift.up f) = ULift.up (F.map f) := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- A type-level equivalence between sections of a functor and morphisms from a terminal functor
to it. We use the constant functor on a given singleton type here as a specific choice of terminal
functor. -/
@[simps apply_app]
/--
Definition of `Functor.sectionsEquivHom` / `Functor.sectionsEquivHom` 的定义

English:
definition Functor.sectionsEquivHom
  signature: (F : C ⥤ Type u₂) (X : Type u₂) [Unique X]
  body: { app j := ↾fun _ => s.1 j
      naturality _ _ _ := by ext x; simp }
  invFun τ := by
    refine ⟨fun j => τ.app _ (default : X), fun φ => ?_⟩
    simp [-const_obj_obj, ← comp_apply, -types_comp_apply, ← NatTrans.naturality]
    rfl
  right_inv τ := by
    ext _ (x : X)
    rw [Unique.eq_default x]

中文:
定义 Functor.sectionsEquivHom
  签名: (F : C ⥤ 类型u₂) (X : 类型u₂) [Unique X]
  定义体: { app j := ↾fun _ => s.1 j
      naturality _ _ _ := by ext x; simp }
  invFun τ := by
    refine ⟨fun j => τ.app _ (default : X), fun φ => ?_⟩
    simp [-const_obj_obj, ← comp_apply, -types_comp_apply, ← NatTrans.naturality]
    rfl
  right_inv τ := by
    ext _ (x : X)
    rw [Unique.eq_default x]

Depends on / 依赖: NatTrans, NatTrans.naturality, Unique, Unique.eq_default, comp_apply, const_obj_obj, eq_default, invFun, naturality, right_inv, types_comp_apply
-/
def Functor.sectionsEquivHom (F : C ⥤ Type u₂) (X : Type u₂) [Unique X] :
    F.sections ≃ ((const _).obj X ⟶ F) where
  toFun s :=
    { app j := ↾fun _ => s.1 j
      naturality _ _ _ := by ext x; simp }
  invFun τ := by
    refine ⟨fun j => τ.app _ (default : X), fun φ => ?_⟩
    simp [-const_obj_obj, ← comp_apply, -types_comp_apply, ← NatTrans.naturality]
    rfl
  right_inv τ := by
    ext _ (x : X)
    rw [Unique.eq_default x]
    rfl

/--
lemma `Functor.sectionsEquivHom_naturality` / 引理 `Functor.sectionsEquivHom_naturality`

English:
lemma Functor.sectionsEquivHom_naturality
  statement: {F G : C ⥤ Type u₂} (f : F ⟶ G) (X : Type u₂)
  proof: by
  rfl

中文:
引理 Functor.sectionsEquivHom_naturality
  结论: {F G : C ⥤ 类型u₂} (f : F ⟶ G) (X : 类型u₂)
  证明: by
  rfl
-/
lemma Functor.sectionsEquivHom_naturality {F G : C ⥤ Type u₂} (f : F ⟶ G) (X : Type u₂)
    [Unique X] (x : F.sections) :
    (G.sectionsEquivHom X) ((sectionsFunctor C).map f x) = (F.sectionsEquivHom X) x ≫ f := by
  rfl

/--
lemma `Functor.sectionsEquivHom_naturality_symm` / 引理 `Functor.sectionsEquivHom_naturality_symm`

English:
lemma Functor.sectionsEquivHom_naturality_symm
  statement: {F G : C ⥤ Type u₂} (f : F ⟶ G)
  proof: by
  rfl

中文:
引理 Functor.sectionsEquivHom_naturality_symm
  结论: {F G : C ⥤ 类型u₂} (f : F ⟶ G)
  证明: by
  rfl
-/
lemma Functor.sectionsEquivHom_naturality_symm {F G : C ⥤ Type u₂} (f : F ⟶ G)
    (X : Type u₂) [Unique X] (τ : (const C).obj X ⟶ F) :
    (G.sectionsEquivHom X).symm (τ ≫ f) =
      (sectionsFunctor C).map f ((F.sectionsEquivHom X).symm τ) := by
  rfl

/-- A natural isomorphism between the sections functor `(C ⥤ Type) ⥤ Type` and the co-Yoneda
embedding of a terminal functor, specifically a constant functor on a given singleton type `X`. -/
@[simps! +dsimpLhs]
/--
Definition of `sectionsFunctorNatIsoCoyoneda` / `sectionsFunctorNatIsoCoyoneda` 的定义

English:
definition sectionsFunctorNatIsoCoyoneda
  signature: (X : Type (max u₁ u₂)) [Unique X]
  body: NatIso.ofComponents fun F => (F.sectionsEquivHom X).toIso

中文:
定义 sectionsFunctorNatIsoCoyoneda
  签名: (X : Type (max u₁ u₂)) [Unique X]
  定义体: NatIso.ofComponents fun F => (F.sectionsEquivHom X).toIso

Depends on / 依赖: F.sectionsEquivHom, NatIso, NatIso.ofComponents, ofComponents, sectionsEquivHom
-/
noncomputable def sectionsFunctorNatIsoCoyoneda (X : Type (max u₁ u₂)) [Unique X] :
    Functor.sectionsFunctor.{v₁, max u₁ u₂} C ≅ coyoneda.obj (op ((Functor.const C).obj X)) :=
  NatIso.ofComponents fun F => (F.sectionsEquivHom X).toIso

end

namespace Functor.FullyFaithful

variable {C : Type u₁} [Category.{v₁} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! hom_app inv_app]
/--
Definition of `homNatIso` / `homNatIso` 的定义

English:
definition homNatIso
  signature: {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
  body: NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

中文:
定义 homNatIso
  签名: {D : 类型u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
  定义体: NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

Depends on / 依赖: Equiv.toIso, Equiv.ulift.injective, Equiv.ulift.symm, Equiv.ulift.trans, NatIso, NatIso.ofComponents, hF.homEquiv.symm.trans, hF.map_injective, homEquiv, injective, map_injective, ofComponents
-/
def homNatIso {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F.op ⋙ uliftYoneda.{v₁}.obj (F.obj X) ≅ uliftYoneda.{v₂}.obj X :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! +dsimpLhs]
/--
Definition of `compUliftYonedaCompWhiskeringLeft` / `compUliftYonedaCompWhiskeringLeft` 的定义

English:
definition compUliftYonedaCompWhiskeringLeft
  signature: {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  body: NatIso.ofComponents (fun X => hF.homNatIso _) fun f => by
    ext; exact Equiv.ulift.injective (hF.map_injective (by simp))

中文:
定义 compUliftYonedaCompWhiskeringLeft
  签名: {D : 类型u₂} [Category.{v₂} D] {F : C ⥤ D}
  定义体: NatIso.ofComponents (fun X => hF.homNatIso _) fun f => by
    ext; exact Equiv.ulift.injective (hF.map_injective (by simp))

Depends on / 依赖: Equiv.ulift.injective, NatIso, NatIso.ofComponents, hF.homNatIso, hF.map_injective, homNatIso, injective, map_injective, ofComponents
-/
def compUliftYonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F ⋙ uliftYoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F.op ≅ uliftYoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso _) fun f => by
    ext; exact Equiv.ulift.injective (hF.map_injective (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! hom_app inv_app]
/--
Definition of `homNatIso'` / `homNatIso'` 的定义

English:
definition homNatIso'
  signature: {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
  body: NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

中文:
定义 homNatIso'
  签名: {D : 类型u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
  定义体: NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

Depends on / 依赖: Equiv.toIso, Equiv.ulift.injective, Equiv.ulift.symm, Equiv.ulift.trans, NatIso, NatIso.ofComponents, hF.homEquiv.symm.trans, hF.map_injective, homEquiv, injective, map_injective, ofComponents
-/
def homNatIso' {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F ⋙ uliftCoyoneda.{v₁}.obj (op (F.obj X)) ≅ uliftCoyoneda.{v₂}.obj (op X) :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

set_option backward.isDefEq.respectTransparency.types false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! +dsimpLhs]
/--
Definition of `compUliftCoyonedaCompWhiskeringLeft` / `compUliftCoyonedaCompWhiskeringLeft` 的定义

English:
definition compUliftCoyonedaCompWhiskeringLeft
  signature: {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  body: NatIso.ofComponents (fun X => hF.homNatIso' _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

中文:
定义 compUliftCoyonedaCompWhiskeringLeft
  签名: {D : 类型u₂} [Category.{v₂} D] {F : C ⥤ D}
  定义体: NatIso.ofComponents (fun X => hF.homNatIso' _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

Depends on / 依赖: Equiv.ulift.injective, NatIso, NatIso.ofComponents, hF.homNatIso, hF.map_injective, homNatIso, injective, map_injective, ofComponents
-/
def compUliftCoyonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F.op ⋙ uliftCoyoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F ≅ uliftCoyoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso' _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

end Functor.FullyFaithful

end CategoryTheory
