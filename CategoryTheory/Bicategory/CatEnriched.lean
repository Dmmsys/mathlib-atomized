/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The strict bicategory associated to a Cat-enriched category

If `C` is a type with an `EnrichedCategory Cat C` structure, then it has hom-categories, whose
objects define 1-dimensional arrows on `C` and whose morphisms define 2-dimensional arrows between
these. The enriched category axioms equip this data with the structure of a strict bicategory.

We define a type alias `CatEnriched C` for a type `C` with an `EnrichedCategory Cat C` structure. We
provide this with an instance of a strict bicategory structure constructing
`Bicategory.Strict (CatEnriched C)`.

If `C` is a type with an `EnrichedOrdinaryCategory Cat C` structure, then it has an
`EnrichedCategory Cat C` structure, so the previous construction would again produce a strict
bicategory. However, in this setting `C` is also given a `Category C` structure, together with an
equivalence between this category and the underlying category of the `EnrichedCategory Cat C`, and
in examples the given category structure is the preferred one.

Thus, we define a type alias `CatEnrichedOrdinary C` for a type `C` with an
`EnrichedOrdinaryCategory Cat C` structure. We provide this with an instance of a strict bicategory
structure extending the category structure provided by the given instance `Category C` constructing
`Bicategory.Strict (CatEnrichedOrdinary C)`.

-/

@[expose] public section

universe u v u' v'
namespace CategoryTheory
open Category

section
variable {C : Type*} [EnrichedCategory Cat C]

/--
Definition of `CatEnriched` / `CatEnriched` 的定义

English:
definition CatEnriched
  signature: (C : Type*)
  body: C

中文:
定义 CatEnriched
  签名: (C : 类型)
  定义体: C
-/
def CatEnriched (C : Type*) := C

namespace CatEnriched

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedCategory Cat (CatEnriched C)
  body: inferInstanceAs (EnrichedCategory Cat C)

中文:
实例 :
  签名: Enriched范畴 Cat (CatEnriched C)
  定义体: inferInstanceAs (EnrichedCategory Cat C)

Depends on / 依赖: EnrichedCategory
-/
instance : EnrichedCategory Cat (CatEnriched C) := inferInstanceAs (EnrichedCategory Cat C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (CatEnriched C)
  body: X ⟶[Cat] Y
  id X := (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).toFunctor.obj (f, g)

中文:
实例 :
  签名: CategoryStruct (CatEnriched C)
  定义体: X ⟶[Cat] Y
  id X := (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).toFunctor.obj (f, g)
-/
instance : CategoryStruct (CatEnriched C) where
  Hom X Y := X ⟶[Cat] Y
  id X := (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).toFunctor.obj (f, g)

/--
theorem `id_eq` / 定理 `id_eq`

English:
theorem id_eq
  given: (X : CatEnriched C)
  statement: 𝟙 X = (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  proof: rfl

中文:
定理 id_eq
  条件: (X : CatEnriched C)
  结论: 𝟙 X = (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  证明: rfl
-/
theorem id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩ := rfl

/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  given: {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_eq
  条件: {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (eComp Cat X Y Z).toFunctor.obj (f, g) := rfl

instance {X Y : CatEnriched C} : Category (X ⟶ Y) := inferInstanceAs (Category (X ⟶[Cat] Y).α)

/--
Definition of `hComp` / `hComp` 的定义

English:
definition hComp
  signature: {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  body: (eComp Cat a b c).toFunctor.map (η, θ)

@[simp]

中文:
定义 hComp
  签名: {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  定义体: (eComp Cat a b c).toFunctor.map (η, θ)

@[simp]

Depends on / 依赖: toFunctor, toFunctor.map
-/
def hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat a b c).toFunctor.map (η, θ)

@[simp]
/--
theorem `id_hComp_id` / 定理 `id_hComp_id`

English:
theorem id_hComp_id
  given: {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c)
  proof: Functor.map_id ..

@[simp]

中文:
定理 id_hComp_id
  条件: {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c)
  证明: Functor.map_id ..

@[simp]

Depends on / 依赖: Functor, Functor.map_id, map_id
-/
theorem id_hComp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := Functor.map_id ..

@[simp]
/--
theorem `eqToHom_hComp_eqToHom` / 定理 `eqToHom_hComp_eqToHom`

English:
theorem eqToHom_hComp_eqToHom
  statement: {a b c : CatEnriched C}
  proof: by cases α; cases β; simp

中文:
定理 eqToHom_hComp_eqToHom
  结论: {a b c : CatEnriched C}
  证明: by cases α; cases β; simp
-/
theorem eqToHom_hComp_eqToHom {a b c : CatEnriched C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
/--
theorem `hComp_comp` / 定理 `hComp_comp`

English:
theorem hComp_comp
  statement: {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
  proof: ((eComp Cat a b c).toFunctor.map_comp (Y := (_, _)) (_, _) (_, _)).symm

中文:
定理 hComp_comp
  结论: {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
  证明: ((eComp Cat a b c).toFunctor.map_comp (Y := (_, _)) (_, _) (_, _)).symm

Depends on / 依赖: map_comp, toFunctor, toFunctor.map_comp
-/
theorem hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).toFunctor.map_comp (Y := (_, _)) (_, _) (_, _)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CatEnriched C)
  body: congrArg (·.toFunctor.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.toFunctor.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.toFunctor.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

中文:
实例 :
  签名: 范畴 (CatEnriched C)
  定义体: congrArg (·.toFunctor.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.toFunctor.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.toFunctor.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

Depends on / 依赖: e_id_comp, toFunctor, toFunctor.obj
-/
instance : Category (CatEnriched C) where
  id_comp {X Y} f := congrArg (·.toFunctor.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.toFunctor.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.toFunctor.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedOrdinaryCategory Cat (CatEnriched C)
  body: ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm
  homEquiv_comp _ _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl
  homEquiv_id _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl

中文:
实例 :
  签名: EnrichedOrdinary范畴 Cat (CatEnriched C)
  定义体: ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm
  homEquiv_comp _ _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl
  homEquiv_id _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl

Depends on / 依赖: Cat.Hom.equivFunctor, Cat.fromChosenTerminalEquiv, equivFunctor, fromChosenTerminalEquiv
-/
instance : EnrichedOrdinaryCategory Cat (CatEnriched C) where
  homEquiv := ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm
  homEquiv_comp _ _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl
  homEquiv_id _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `id_hComp_heq` / 定理 `id_hComp_heq`

English:
theorem id_hComp_heq
  given: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_id_comp (V := Cat) a b)

中文:
定理 id_hComp_heq
  条件: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_id_comp (V := Cat) a b)

Depends on / 依赖: Functor, Functor.map_id, congr_arg_heq, e_id_comp, id_eq, map_id, toFunctor, toFunctor.map
-/
theorem id_hComp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_id_comp (V := Cat) a b)

/--
theorem `id_hComp` / 定理 `id_hComp`

English:
theorem id_hComp
  given: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  simp [← heq_eq_eq, id_hComp_heq]

中文:
定理 id_hComp
  条件: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  simp [← heq_eq_eq, id_hComp_heq]

Depends on / 依赖: heq_eq_eq, id_hComp_heq
-/
theorem id_hComp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  simp [← heq_eq_eq, id_hComp_heq]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hComp_id_heq` / 定理 `hComp_id_heq`

English:
theorem hComp_id_heq
  given: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_comp_id (V := Cat) a b)

中文:
定理 hComp_id_heq
  条件: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_comp_id (V := Cat) a b)

Depends on / 依赖: Functor, Functor.map_id, congr_arg_heq, e_comp_id, id_eq, map_id, toFunctor, toFunctor.map
-/
theorem hComp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by
  rw [id_eq]; rw [← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_comp_id (V := Cat) a b)

/--
theorem `hComp_id` / 定理 `hComp_id`

English:
theorem hComp_id
  given: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  simp [← heq_eq_eq, hComp_id_heq]

中文:
定理 hComp_id
  条件: {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  simp [← heq_eq_eq, hComp_id_heq]

Depends on / 依赖: hComp_id_heq, heq_eq_eq
-/
theorem hComp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  simp [← heq_eq_eq, hComp_id_heq]

/--
theorem `hComp_assoc_heq` / 定理 `hComp_assoc_heq`

English:
theorem hComp_assoc_heq
  statement: {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  proof: congr_arg_heq (·.toFunctor.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ))
    (e_assoc (V := Cat) a b c d)

中文:
定理 hComp_assoc_heq
  结论: {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  证明: congr_arg_heq (·.toFunctor.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ))
    (e_assoc (V := Cat) a b c d)

Depends on / 依赖: congr_arg_heq, e_assoc, toFunctor, toFunctor.map
-/
theorem hComp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) :=
  congr_arg_heq (·.toFunctor.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ))
    (e_assoc (V := Cat) a b c d)

/--
theorem `hComp_assoc` / 定理 `hComp_assoc`

English:
theorem hComp_assoc
  statement: {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  proof: by
  simp [← heq_eq_eq, hComp_assoc_heq]

中文:
定理 hComp_assoc
  结论: {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  证明: by
  simp [← heq_eq_eq, hComp_assoc_heq]

Depends on / 依赖: hComp_assoc_heq, heq_eq_eq
-/
theorem hComp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  simp [← heq_eq_eq, hComp_assoc_heq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory (CatEnriched C)
  body: inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp

中文:
实例 :
  签名: 双范畴 (CatEnriched C)
  定义体: inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp
-/
instance : Bicategory (CatEnriched C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp_assoc]
  whiskerRight_id := hComp_id
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon f g h i := by
    generalize_proofs h1 h2 h3 h4; revert h1 h2 h3 h4
    generalize (f ≫ g) ≫ h = x, (g ≫ h) ≫ i = w
    rintro rfl _ rfl _; simp
  triangle f g := by
    generalize_proofs h1 h2 h3; revert h1 h2 h3
    generalize 𝟙 _ ≫ g = g, f ≫ 𝟙 _ = f
    rintro _ rfl rfl; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory.Strict (CatEnriched C)

中文:
实例 :
  签名: 双范畴.Strict (CatEnriched C)
-/
instance : Bicategory.Strict (CatEnriched C) where

end CatEnriched

end

section
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{v', u'} C]

/--
Definition of `CatEnrichedOrdinary` / `CatEnrichedOrdinary` 的定义

English:
definition CatEnrichedOrdinary
  signature: (C : Type*)
  body: C

中文:
定义 CatEnrichedOrdinary
  签名: (C : 类型)
  定义体: C
-/
def CatEnrichedOrdinary (C : Type*) := C

namespace CatEnrichedOrdinary

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CatEnrichedOrdinary C)
  body: inferInstanceAs (Category C)

中文:
实例 :
  签名: 范畴 (CatEnrichedOrdinary C)
  定义体: inferInstanceAs (Category C)

Depends on / 依赖: Category
-/
instance : Category (CatEnrichedOrdinary C) := inferInstanceAs (Category C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedCategory Cat (CatEnrichedOrdinary C)
  body: inferInstanceAs (EnrichedCategory Cat C)

中文:
实例 :
  签名: Enriched范畴 Cat (CatEnrichedOrdinary C)
  定义体: inferInstanceAs (EnrichedCategory Cat C)

Depends on / 依赖: EnrichedCategory
-/
instance : EnrichedCategory Cat (CatEnrichedOrdinary C) := inferInstanceAs (EnrichedCategory Cat C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedOrdinaryCategory Cat (CatEnrichedOrdinary C)
  body: inferInstanceAs (EnrichedOrdinaryCategory Cat C)

中文:
实例 :
  签名: EnrichedOrdinary范畴 Cat (CatEnrichedOrdinary C)
  定义体: inferInstanceAs (EnrichedOrdinaryCategory Cat C)

Depends on / 依赖: EnrichedOrdinaryCategory
-/
instance : EnrichedOrdinaryCategory Cat (CatEnrichedOrdinary C) :=
  inferInstanceAs (EnrichedOrdinaryCategory Cat C)

/--
Definition of `toBase` / `toBase` 的定义

English:
definition toBase
  signature: (a : CatEnrichedOrdinary C)
  body: a

中文:
定义 toBase
  签名: (a : CatEnrichedOrdinary C)
  定义体: a
-/
def toBase (a : CatEnrichedOrdinary C) : CatEnriched C := a

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {a b : CatEnrichedOrdinary C}
  body: (eHomEquiv (V := Cat)).trans (Equiv.trans (Cat.Hom.equivFunctor _ _) Cat.fromChosenTerminalEquiv)

中文:
定义 homEquiv
  签名: {a b : CatEnrichedOrdinary C}
  定义体: (eHomEquiv (V := Cat)).trans (Equiv.trans (Cat.Hom.equivFunctor _ _) Cat.fromChosenTerminalEquiv)

Depends on / 依赖: Cat.Hom.equivFunctor, Cat.fromChosenTerminalEquiv, Equiv.trans, eHomEquiv, equivFunctor, fromChosenTerminalEquiv
-/
def homEquiv {a b : CatEnrichedOrdinary C} : (a ⟶ b) ≃ (a.toBase ⟶ b.toBase) :=
  (eHomEquiv (V := Cat)).trans (Equiv.trans (Cat.Hom.equivFunctor _ _) Cat.fromChosenTerminalEquiv)

/--
theorem `homEquiv_id` / 定理 `homEquiv_id`

English:
theorem homEquiv_id
  given: {a : CatEnrichedOrdinary C}
  statement: homEquiv (𝟙 a) = 𝟙 a.toBase
  proof: by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl

中文:
定理 homEquiv_id
  条件: {a : CatEnrichedOrdinary C}
  结论: homEquiv (𝟙 a) = 𝟙 a.toBase
  证明: by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl

Depends on / 依赖: Equiv.trans_apply, eHomEquiv_id, homEquiv, trans_apply
-/
theorem homEquiv_id {a : CatEnrichedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl

/--
theorem `homEquiv_comp` / 定理 `homEquiv_comp`

English:
theorem homEquiv_comp
  given: {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_comp]
  rfl

中文:
定理 homEquiv_comp
  条件: {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_comp]
  rfl

Depends on / 依赖: Equiv.trans_apply, eHomEquiv_comp, homEquiv, trans_apply
-/
theorem homEquiv_comp {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = homEquiv f ≫ homEquiv g := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_comp]
  rfl

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: {X Y : CatEnrichedOrdinary C} (f g : X ⟶ Y)
  (no additional axioms)

中文:
结构 态射
  参数: {X Y : CatEnrichedOrdinary C} (f g : X ⟶ Y)
  (无附加公理)
-/
structure Hom {X Y : CatEnrichedOrdinary C} (f g : X ⟶ Y) where mk' ::
  /-- A 2-cell from `f` to `g` is a 2-cell from `homEquiv f` to `homEquiv g`. -/
  base' : homEquiv f ⟶ homEquiv g

instance {X Y : CatEnrichedOrdinary C} : Quiver (X ⟶ Y) where
  Hom f g := Hom f g

/--
Definition of `Hom.base` / `Hom.base` 的定义

English:
definition Hom.base
  signature: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g)
  body: α.base'

中文:
定义 态射.base
  签名: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g)
  定义体: α.base'
-/
def Hom.base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    homEquiv f ⟶ homEquiv g := α.base'

/--
Definition of `Hom.mk` / `Hom.mk` 的定义

English:
definition Hom.mk
  signature: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g)
  body: .mk' α

中文:
定义 态射.mk
  签名: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g)
  定义体: .mk' α

Depends on / 依赖: Unique
-/
def Hom.mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    f ⟶ g := .mk' α

/--
theorem `mk_base` / 定理 `mk_base`

English:
theorem mk_base
  given: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g)
  proof: rfl

中文:
定理 mk_base
  条件: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g)
  证明: rfl
-/
@[simp] theorem mk_base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    Hom.mk (Hom.base α) = α := rfl

/--
theorem `base_mk` / 定理 `base_mk`

English:
theorem base_mk
  given: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g)
  proof: rfl

中文:
定理 base_mk
  条件: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g)
  证明: rfl
-/
@[simp] theorem base_mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    Hom.base (Hom.mk α) = α := rfl

instance {X Y : CatEnrichedOrdinary C} : CategoryStruct (X ⟶ Y) where
  id f := Hom.mk (𝟙 (homEquiv f))
  comp α β := Hom.mk (Hom.base α ≫ Hom.base β)

/--
theorem `Hom.id_eq` / 定理 `Hom.id_eq`

English:
theorem Hom.id_eq
  given: {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 态射.id_eq
  条件: {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y)
  证明: rfl
-/
theorem Hom.id_eq {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    𝟙 f = Hom.mk (𝟙 (homEquiv f)) := rfl

/--
theorem `Hom.base_id` / 定理 `Hom.base_id`

English:
theorem Hom.base_id
  given: {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 态射.base_id
  条件: {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y)
  证明: rfl
-/
@[simp] theorem Hom.base_id {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    Hom.base (𝟙 f) = 𝟙 (homEquiv f) := rfl

/--
theorem `Hom.comp_eq` / 定理 `Hom.comp_eq`

English:
theorem Hom.comp_eq
  statement: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  proof: rfl

中文:
定理 态射.comp_eq
  结论: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  证明: rfl
-/
theorem Hom.comp_eq {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : (α ≫ β) = Hom.mk (Hom.base α ≫ Hom.base β) := rfl

/--
theorem `Hom.base_comp` / 定理 `Hom.base_comp`

English:
theorem Hom.base_comp
  statement: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  proof: rfl

中文:
定理 态射.base_comp
  结论: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  证明: rfl
-/
@[simp] theorem Hom.base_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : Hom.base (α ≫ β) = Hom.base α ≫ Hom.base β := rfl

/--
theorem `Hom.mk_comp` / 定理 `Hom.mk_comp`

English:
theorem Hom.mk_comp
  statement: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  proof: rfl

中文:
定理 态射.mk_comp
  结论: {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
  证明: rfl
-/
theorem Hom.mk_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : homEquiv f ⟶ homEquiv g) (β : homEquiv g ⟶ homEquiv h) :
    Hom.mk (α ≫ β) = Hom.mk α ≫ Hom.mk β := rfl

/--
theorem `Hom.ext` / 定理 `Hom.ext`

English:
theorem Hom.ext
  statement: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α β : f ⟶ g)
  proof: by cases α; cases β; cases H; rfl

中文:
定理 态射.ext
  结论: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α β : f ⟶ g)
  证明: by cases α; cases β; cases H; rfl
-/
@[ext] theorem Hom.ext {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α β : f ⟶ g)
    (H : Hom.base α = Hom.base β) : α = β := by cases α; cases β; cases H; rfl

/-- A `Cat`-enriched ordinary category comes with hom-categories `X ⟶[Cat] Y` whose underlying type
of objects is equivalent to the type `X ⟶ Y` defined by the category structure on `C`. The following
definition transfers the category structure to the latter type of objects. -/
instance {X Y : CatEnrichedOrdinary C} : Category (X ⟶ Y) where

/--
theorem `Hom.base_eqToHom` / 定理 `Hom.base_eqToHom`

English:
theorem Hom.base_eqToHom
  given: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f = g)
  proof: by cases α; rfl

中文:
定理 态射.base_eqToHom
  条件: {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f = g)
  证明: by cases α; rfl
-/
@[simp] theorem Hom.base_eqToHom {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f = g) :
    Hom.base (eqToHom α) = eqToHom (congrArg _ α) := by cases α; rfl

/--
Definition of `hComp` / `hComp` 的定义

English:
definition hComp
  signature: {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  body: .mk
    eqToHom (homEquiv_comp f g) ≫ CatEnriched.hComp (Hom.base η) (Hom.base θ) ≫
    eqToHom (homEquiv_comp f' g').symm

@[simp]

中文:
定义 hComp
  签名: {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c}
  定义体: .mk
    eqToHom (homEquiv_comp f g) ≫ CatEnriched.hComp (Hom.base η) (Hom.base θ) ≫
    eqToHom (homEquiv_comp f' g').symm

@[simp]

Depends on / 依赖: CatEnriched, CatEnriched.hComp, Hom.base, eqToHom, homEquiv_comp
-/
def hComp {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' :=
.mk
    eqToHom (homEquiv_comp f g) ≫ CatEnriched.hComp (Hom.base η) (Hom.base θ) ≫
    eqToHom (homEquiv_comp f' g').symm

@[simp]
/--
theorem `id_hComp_id` / 定理 `id_hComp_id`

English:
theorem id_hComp_id
  given: {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c)
  proof: by simp [hComp, Hom.id_eq]

@[simp]

中文:
定理 id_hComp_id
  条件: {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c)
  证明: by simp [hComp, Hom.id_eq]

@[simp]

Depends on / 依赖: Hom.id_eq, id_eq
-/
theorem id_hComp_id {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := by simp [hComp, Hom.id_eq]

@[simp]
/--
theorem `eqToHom_hComp_eqToHom` / 定理 `eqToHom_hComp_eqToHom`

English:
theorem eqToHom_hComp_eqToHom
  statement: {a b c : CatEnrichedOrdinary C}
  proof: by cases α; cases β; simp

中文:
定理 eqToHom_hComp_eqToHom
  结论: {a b c : CatEnrichedOrdinary C}
  证明: by cases α; cases β; simp
-/
theorem eqToHom_hComp_eqToHom {a b c : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
/--
theorem `hComp_comp` / 定理 `hComp_comp`

English:
theorem hComp_comp
  statement: {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
  proof: by
  simp [hComp, ← CatEnriched.hComp_comp, Hom.comp_eq]

中文:
定理 hComp_comp
  结论: {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
  证明: by
  simp [hComp, ← CatEnriched.hComp_comp, Hom.comp_eq]

Depends on / 依赖: CatEnriched, CatEnriched.hComp_comp, Hom.comp_eq, comp_eq, hComp_comp
-/
theorem hComp_comp {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') := by
  simp [hComp, ← CatEnriched.hComp_comp, Hom.comp_eq]

/--
theorem `id_hComp` / 定理 `id_hComp`

English:
theorem id_hComp
  given: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]; simp [CatEnriched.id_hComp_heq]

中文:
定理 id_hComp
  条件: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]; simp [CatEnriched.id_hComp_heq]

Depends on / 依赖: CatEnriched, CatEnriched.id_hComp_heq, Hom.base_id, base_id, base_mk, comp_eqToHom_heq_iff, eqToHom_comp_heq_iff, heq_eq_eq, homEquiv_id, id_hComp_heq
-/
theorem id_hComp {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]; simp [CatEnriched.id_hComp_heq]

/--
theorem `id_hComp_heq` / 定理 `id_hComp_heq`

English:
theorem id_hComp_heq
  given: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by simp [id_hComp]

中文:
定理 id_hComp_heq
  条件: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by simp [id_hComp]

Depends on / 依赖: id_hComp
-/
theorem id_hComp_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by simp [id_hComp]

/--
theorem `hComp_id` / 定理 `hComp_id`

English:
theorem hComp_id
  given: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]
  simp [CatEnriched.hComp_id_heq]

中文:
定理 hComp_id
  条件: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]
  simp [CatEnriched.hComp_id_heq]

Depends on / 依赖: CatEnriched, CatEnriched.hComp_id_heq, Hom.base_id, base_id, base_mk, comp_eqToHom_heq_iff, eqToHom_comp_heq_iff, hComp_id_heq, heq_eq_eq, homEquiv_id
-/
theorem hComp_id {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]
  simp [CatEnriched.hComp_id_heq]

/--
theorem `hComp_id_heq` / 定理 `hComp_id_heq`

English:
theorem hComp_id_heq
  given: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  proof: by simp [hComp_id]

中文:
定理 hComp_id_heq
  条件: {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f')
  证明: by simp [hComp_id]

Depends on / 依赖: hComp_id
-/
theorem hComp_id_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by simp [hComp_id]

/--
theorem `id_eq_eqToHom` / 定理 `id_eq_eqToHom`

English:
theorem id_eq_eqToHom
  given: {C} [Category* C] (X : C)
  statement: 𝟙 X = eqToHom rfl
  proof: rfl

中文:
定理 id_eq_eqToHom
  条件: {C} [范畴* C] (X : C)
  结论: 𝟙 X = eqToHom rfl
  证明: rfl
-/
theorem id_eq_eqToHom {C} [Category* C] (X : C) : 𝟙 X = eqToHom rfl := rfl

/--
theorem `hComp_assoc` / 定理 `hComp_assoc`

English:
theorem hComp_assoc
  statement: {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  proof: by
  ext
  simp only [hComp, base_mk, Hom.base_comp, Hom.base_eqToHom,
    ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  conv => enter [1, 2]; exact ((id_comp _).trans (comp_id _)).symm
  conv => enter [2, 1]; exact ((id_comp _).trans (com

中文:
定理 hComp_assoc
  结论: {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
  证明: by
  ext
  simp only [hComp, base_mk, Hom.base_comp, Hom.base_eqToHom,
    ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  conv => enter [1, 2]; exact ((id_comp _).trans (comp_id _)).symm
  conv => enter [2, 1]; exact ((id_comp _).trans (com

Depends on / 依赖: CatEnriched, CatEnriched.eqToHom_hComp_eqToHom, CatEnriched.hComp_assoc_heq, CatEnriched.hComp_comp, Hom.base_comp, Hom.base_eqToHom, base_comp, base_eqToHom, base_mk, comp_eqToHom_heq_iff, comp_id, eqToHom_comp_heq_iff, eqToHom_hComp_eqToHom, hComp_assoc_heq, hComp_comp, heq_comp_eqToHom_iff, heq_eqToHom_comp_iff, heq_eq_eq, id_comp, id_eq_eqToHom
-/
theorem hComp_assoc {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  ext
  simp only [hComp, base_mk, Hom.base_comp, Hom.base_eqToHom,
    ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  conv => enter [1, 2]; exact ((id_comp _).trans (comp_id _)).symm
  conv => enter [2, 1]; exact ((id_comp _).trans (comp_id _)).symm
  iterate 4 rw [← CatEnriched.hComp_comp, id_eq_eqToHom, CatEnriched.eqToHom_hComp_eqToHom]
  simp [CatEnriched.hComp_assoc_heq]

/--
theorem `hComp_assoc_heq` / 定理 `hComp_assoc_heq`

English:
theorem hComp_assoc_heq
  statement: {a b c d : CatEnrichedOrdinary C}
  proof: by simp [hComp_assoc]

中文:
定理 hComp_assoc_heq
  结论: {a b c d : CatEnrichedOrdinary C}
  证明: by simp [hComp_assoc]

Depends on / 依赖: hComp_assoc
-/
theorem hComp_assoc_heq {a b c d : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) := by simp [hComp_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory (CatEnrichedOrdinary C)
  body: inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := by simp [id_hComp]
  comp_whiskerLeft := by simp [← hComp_as

中文:
实例 :
  签名: 双范畴 (CatEnrichedOrdinary C)
  定义体: inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := by simp [id_hComp]
  comp_whiskerLeft := by simp [← hComp_as
-/
instance : Bicategory (CatEnrichedOrdinary C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := by simp [id_hComp]
  comp_whiskerLeft := by simp [← hComp_assoc]
  whiskerRight_id := by simp [hComp_id]
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon := by simp [id_eq_eqToHom, -eqToHom_refl]
  triangle := by simp [id_eq_eqToHom, -eqToHom_refl]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory.Strict (CatEnrichedOrdinary C)

中文:
实例 :
  签名: 双范畴.Strict (CatEnrichedOrdinary C)
-/
instance : Bicategory.Strict (CatEnrichedOrdinary C) where

end CatEnrichedOrdinary

end

end CategoryTheory
