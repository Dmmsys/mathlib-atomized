/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Trifunctor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Localization of monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure: this means `W`
is multiplicative and stable by left and right whiskerings (this is
the type class `W.IsMonoidal`). Let `L : C ⥤ D` be a localization functor
for `W`. In the file, we construct a monoidal category structure
on `D` such that the localization functor is monoidal. The structure
is actually defined on a type synonym `LocalizedMonoidal L W ε`.
Here, the data `ε : L.obj (𝟙_ C) ≅ unit` is an isomorphism to some
object `unit : D` which allows the user to provide a preferred choice
of a unit object.

The symmetric case is considered in the file
`Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

/--
Definition of `IsMonoidal` / `IsMonoidal` 的定义

English:
class IsMonoidal
  parameters: : Prop extends W.IsMultiplicative where
  extends: W.IsMultiplicative
  axioms and operations (2):
    - whiskerLeft((X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g)) : W (X ◁ g)
    - whiskerRight({X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C)) : W (f ▷ Y)

中文:
类 是幺半群
  参数: : 命题 extends W.是Multiplicative where
  继承: W.是Multiplicative
  公理与运算 (2 个):
    - whiskerLeft((X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g)) : W (X ◁ g)
    - whiskerRight({X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C)) : W (f ▷ Y)
-/
class IsMonoidal : Prop extends W.IsMultiplicative where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

/--
lemma `IsMonoidal.mk'` / 引理 `IsMonoidal.mk'`

English:
lemma IsMonoidal.mk'
  statement: [W.IsMultiplicative]
  proof: by simpa using h (𝟙 X) g (W.id_mem _) hg
  whiskerRight f hf Y := by simpa using h f (𝟙 Y) hf (W.id_mem _)

中文:
引理 是幺半群.mk'
  结论: [W.是Multiplicative]
  证明: by simpa using h (𝟙 X) g (W.id_mem _) hg
  whiskerRight f hf Y := by simpa using h f (𝟙 Y) hf (W.id_mem _)

Depends on / 依赖: W.id_mem, id_mem, whiskerRight
-/
lemma IsMonoidal.mk' [W.IsMultiplicative]
    (h : forall {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (_ : W f) (_ : W g), W (f otimesₘ g)) :
    W.IsMonoidal where
  whiskerLeft X _ _ g hg := by simpa using h (𝟙 X) g (W.id_mem _) hg
  whiskerRight f hf Y := by simpa using h f (𝟙 Y) hf (W.id_mem _)

variable [W.IsMonoidal]

/--
lemma `whiskerLeft_mem` / 引理 `whiskerLeft_mem`

English:
lemma whiskerLeft_mem
  given: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g)
  statement: W (X ◁ g)
  proof: IsMonoidal.whiskerLeft _ _ hg

中文:
引理 whiskerLeft_mem
  条件: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g)
  结论: W (X ◁ g)
  证明: IsMonoidal.whiskerLeft _ _ hg

Depends on / 依赖: IsMonoidal, IsMonoidal.whiskerLeft, whiskerLeft
-/
lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  IsMonoidal.whiskerLeft _ _ hg

/--
lemma `whiskerRight_mem` / 引理 `whiskerRight_mem`

English:
lemma whiskerRight_mem
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C)
  statement: W (f ▷ Y)
  proof: IsMonoidal.whiskerRight _ hf Y

中文:
引理 whiskerRight_mem
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C)
  结论: W (f ▷ Y)
  证明: IsMonoidal.whiskerRight _ hf Y

Depends on / 依赖: IsMonoidal, IsMonoidal.whiskerRight, whiskerRight
-/
lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  IsMonoidal.whiskerRight _ hf Y

/--
lemma `tensorHom_mem` / 引理 `tensorHom_mem`

English:
lemma tensorHom_mem
  statement: {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  proof: by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

中文:
引理 tensorHom_mem
  结论: {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  证明: by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

Depends on / 依赖: comp_mem, tensorHom_def, whiskerLeft_mem, whiskerRight_mem
-/
lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f otimesₘ g) := by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

/-- The inverse image under a monoidal functor of a monoidal morphism property which respects
isomorphisms is monoidal. -/
instance {C' : Type*} [Category* C'] [MonoidalCategory C'] (F : C' ⥤ C) [F.Monoidal]
    [W.RespectsIso] : (W.inverseImage F).IsMonoidal := .mk' _ fun f g hf hg => by
  simp only [inverseImage_iff] at hf hg ⊢
  rw [Functor.Monoidal.map_tensor _ f g]
  apply MorphismProperty.RespectsIso.precomp
  apply MorphismProperty.RespectsIso.postcomp
  exact tensorHom_mem _ _ _ hf hg

end MorphismProperty

/-- Given a monoidal category `C`, a localization functor `L : C ⥤ D` with respect
to `W : MorphismProperty C` which satisfies `W.IsMonoidal`, and a choice
of object `unit : D` with an isomorphism `L.obj (𝟙_ C) ≅ unit`, this is a
type synonym for `D` on which we define the localized monoidal category structure. -/
@[nolint unusedArguments]
/--
Definition of `LocalizedMonoidal` / `LocalizedMonoidal` 的定义

English:
definition LocalizedMonoidal
  signature: (L : C ⥤ D) (W : MorphismProperty C)
  body: D

中文:
定义 LocalizedMonoidal
  签名: (L : C ⥤ D) (W : MorphismProperty C)
  定义体: D
-/
def LocalizedMonoidal (L : C ⥤ D) (W : MorphismProperty C)
    [W.IsMonoidal] [L.IsLocalization W] {unit : D} (_ : L.obj (𝟙_ C) ≅ unit) :=
  D

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

namespace Localization

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (LocalizedMonoidal L W ε)
  body: inferInstanceAs (Category D)

中文:
实例 :
  签名: 范畴 (LocalizedMonoidal L W ε)
  定义体: inferInstanceAs (Category D)

Depends on / 依赖: Category
-/
instance : Category (LocalizedMonoidal L W ε) :=
  inferInstanceAs (Category D)

namespace Monoidal

/--
Definition of `toMonoidalCategory` / `toMonoidalCategory` 的定义

English:
definition toMonoidalCategory
  signature: : C ⥤ LocalizedMonoidal L W ε
  body: L

中文:
定义 toMonoidalCategory
  签名: : C ⥤ LocalizedMonoidal L W ε
  定义体: L
-/
def toMonoidalCategory : C ⥤ LocalizedMonoidal L W ε := L

/--
Definition of `ε'` / `ε'` 的定义

English:
abbreviation ε'
  signature: : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit
  body: ε

local notation "L'" => toMonoidalCategory L W ε

中文:
缩写 ε'
  签名: : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit
  定义体: ε

local notation "L'" => toMonoidalCategory L W ε
-/
abbrev ε' : (toMonoidalCategory L W ε).obj (𝟙_ C) ≅ unit := ε

local notation "L'" => toMonoidalCategory L W ε

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (L').IsLocalization W
  body: inferInstanceAs (L.IsLocalization W)

中文:
实例 :
  签名: (L').是Localization W
  定义体: inferInstanceAs (L.IsLocalization W)

Depends on / 依赖: IsLocalization, L.IsLocalization
-/
instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isInvertedBy₂` / 引理 `isInvertedBy₂`

English:
lemma isInvertedBy₂
  proof: by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

中文:
引理 isInvertedBy₂
  证明: by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

Depends on / 依赖: Localization, Localization.inverts, W.whiskerLeft_mem, W.whiskerRight_mem, infer_instance, inverts, whiskerLeft_mem, whiskerRight_mem
-/
lemma isInvertedBy₂ :
    MorphismProperty.IsInvertedBy₂ W W
      (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L') := by
  rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have := Localization.inverts L' W _ (W.whiskerRight_mem f₁ hf₁ Y₁)
  have := Localization.inverts L' W _ (W.whiskerLeft_mem X₂ f₂ hf₂)
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorBifunctor` / `tensorBifunctor` 的定义

English:
definition tensorBifunctor
  signature: :
  body: Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

中文:
定义 tensorBifunctor
  签名: :
  定义体: Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

Depends on / 依赖: Localization, Localization.lift
-/
noncomputable def tensorBifunctor :
    LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε ⥤ LocalizedMonoidal L W ε :=
  Localization.lift₂ _ (isInvertedBy₂ L W ε) L L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lifting₂ L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
  body: inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

中文:
实例 :
  签名: Lifting₂ L' L' W W (curriedTensor C ⋙ (函子.whiskeringRight C C
  定义体: inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

Depends on / 依赖: Functor, Functor.whiskeringRight, Localization, Localization.lift, curriedTensor, whiskeringRight
-/
noncomputable instance : Lifting₂ L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε) :=
  inferInstanceAs (Lifting₂ L L W W (curriedTensor C ⋙ (Functor.whiskeringRight C C D).obj L')
    (Localization.lift₂ _ (isInvertedBy₂ L W ε) L L))

/--
Definition of `tensorBifunctorIso` / `tensorBifunctorIso` 的定义

English:
abbreviation tensorBifunctorIso
  signature: :
  body: Lifting₂.iso L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε)

中文:
缩写 tensorBifunctorIso
  签名: :
  定义体: Lifting₂.iso L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε)

Depends on / 依赖: Functor, Functor.whiskeringRight, LocalizedMonoidal, curriedTensor, tensorBifunctor, whiskeringRight
-/
noncomputable abbrev tensorBifunctorIso :
    (((Functor.whiskeringLeft₂ D).obj L').obj L').obj (tensorBifunctor L W ε) ≅
      (Functor.postcompose₂.obj L').obj (curriedTensor C) :=
  Lifting₂.iso L' L' W W (curriedTensor C ⋙ (Functor.whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (X : C) :
    Lifting L' W (tensorLeft X ⋙ L') ((tensorBifunctor L W ε).obj ((L').obj X)) := by
  apply Lifting₂.liftingLift₂ (hF := isInvertedBy₂ L W ε)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (Y : C) :
    Lifting L' W (tensorRight Y ⋙ L') ((tensorBifunctor L W ε).flip.obj ((L').obj Y)) := by
  apply Lifting₂.liftingLift₂Flip (hF := isInvertedBy₂ L W ε)

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _
  body: (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

中文:
定义 leftUnitor
  签名: : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _
  定义体: (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

Depends on / 依赖: Functor, Functor.isoWhiskerRight, L.leftUnitor, Localization, Localization.liftNatIso, isoWhiskerRight, leftUnitor, leftUnitorNatIso, liftNatIso, mapIso, tensorBifunctor, tensorLeft
-/
noncomputable def leftUnitor : (tensorBifunctor L W ε).obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorLeft (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (leftUnitorNatIso C) _ ≪≫ L.leftUnitor)

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _
  body: (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

中文:
定义 rightUnitor
  签名: : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _
  定义体: (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

Depends on / 依赖: Functor, Functor.isoWhiskerRight, L.leftUnitor, Localization, Localization.liftNatIso, flip.mapIso, flip.obj, isoWhiskerRight, leftUnitor, liftNatIso, mapIso, rightUnitorNatIso, tensorBifunctor, tensorRight
-/
noncomputable def rightUnitor : (tensorBifunctor L W ε).flip.obj unit ≅ 𝟭 _ :=
  (tensorBifunctor L W ε).flip.mapIso ε.symm ≪≫
    Localization.liftNatIso L' W (tensorRight (𝟙_ C) ⋙ L') L'
      ((tensorBifunctor L W ε).flip.obj ((L').obj (𝟙_ _))) _
        (Functor.isoWhiskerRight (rightUnitorNatIso C) _ ≪≫ L.leftUnitor)

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: :
  body: Localization.associator L' L' L' L' L' L' W W W W W
    (curriedAssociatorNatIso C) (tensorBifunctor L W ε) (tensorBifunctor L W ε)
    (tensorBifunctor L W ε) (tensorBifunctor L W ε)

中文:
定义 associator
  签名: :
  定义体: Localization.associator L' L' L' L' L' L' W W W W W
    (curriedAssociatorNatIso C) (tensorBifunctor L W ε) (tensorBifunctor L W ε)
    (tensorBifunctor L W ε) (tensorBifunctor L W ε)

Depends on / 依赖: Localization, Localization.associator, associator, curriedAssociatorNatIso, tensorBifunctor
-/
noncomputable def associator :
    bifunctorComp₁₂ (tensorBifunctor L W ε) (tensorBifunctor L W ε) ≅
      bifunctorComp₂₃ (tensorBifunctor L W ε) (tensorBifunctor L W ε) :=
  Localization.associator L' L' L' L' L' L' W W W W W
    (curriedAssociatorNatIso C) (tensorBifunctor L W ε) (tensorBifunctor L W ε)
    (tensorBifunctor L W ε) (tensorBifunctor L W ε)

/--
Instance `monoidalCategoryStruct` / 实例 `monoidalCategoryStruct`

English:
instance monoidalCategoryStruct
  signature: :
  body: ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W ε).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W ε).map f).app Y
  tensorUnit := unit
  associator X Y Z := (((associator L W ε).app X).app Y).app Z
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

中文:
实例 monoidalCategoryStruct
  签名: :
  定义体: ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W ε).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W ε).map f).app Y
  tensorUnit := unit
  associator X Y Z := (((associator L W ε).app X).app Y).app Z
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

Depends on / 依赖: tensorBifunctor
-/
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (LocalizedMonoidal L W ε) where
  tensorObj X Y := ((tensorBifunctor L W ε).obj X).obj Y
  whiskerLeft X _ _ g := ((tensorBifunctor L W ε).obj X).map g
  whiskerRight f Y := ((tensorBifunctor L W ε).map f).app Y
  tensorUnit := unit
  associator X Y Z := (((associator L W ε).app X).app Y).app Z
  leftUnitor Y := (leftUnitor L W ε).app Y
  rightUnitor X := (rightUnitor L W ε).app X

/--
Definition of `μ` / `μ` 的定义

English:
definition μ
  signature: (X Y : C)
  body: ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]

中文:
定义 μ
  签名: (X Y : C)
  定义体: ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]

Depends on / 依赖: tensorBifunctorIso
-/
noncomputable def μ (X Y : C) : (L').obj X otimes (L').obj Y ≅ (L').obj (X otimes Y) :=
  ((tensorBifunctorIso L W ε).app X).app Y

@[reassoc (attr := simp)]
/--
lemma `μ_natural_left` / 引理 `μ_natural_left`

English:
lemma μ_natural_left
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  proof: NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]

中文:
引理 μ_natural_left
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  证明: NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.naturality_app, naturality_app, tensorBifunctorIso
-/
lemma μ_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (L').map f ▷ (L').obj Y ≫ (μ L W ε X₂ Y).hom =
      (μ L W ε X₁ Y).hom ≫ (L').map (f ▷ Y) :=
  NatTrans.naturality_app (tensorBifunctorIso L W ε).hom Y f

@[reassoc (attr := simp)]
/--
lemma `μ_inv_natural_left` / 引理 `μ_inv_natural_left`

English:
lemma μ_inv_natural_left
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  proof: by
  simp [Iso.eq_comp_inv]

@[reassoc (attr := simp)]

中文:
引理 μ_inv_natural_left
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  证明: by
  simp [Iso.eq_comp_inv]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv
-/
lemma μ_inv_natural_left {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (μ L W ε X₁ Y).inv ≫ (L').map f ▷ (L').obj Y =
      (L').map (f ▷ Y) ≫ (μ L W ε X₂ Y).inv := by
  simp [Iso.eq_comp_inv]

@[reassoc (attr := simp)]
/--
lemma `μ_natural_right` / 引理 `μ_natural_right`

English:
lemma μ_natural_right
  given: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  proof: ((tensorBifunctorIso L W ε).hom.app X).naturality g

@[reassoc (attr := simp)]

中文:
引理 μ_natural_right
  条件: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  证明: ((tensorBifunctorIso L W ε).hom.app X).naturality g

@[reassoc (attr := simp)]

Depends on / 依赖: hom.app, naturality, tensorBifunctorIso
-/
lemma μ_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (L').obj X ◁ (L').map g ≫ (μ L W ε X Y₂).hom =
      (μ L W ε X Y₁).hom ≫ (L').map (X ◁ g) :=
  ((tensorBifunctorIso L W ε).hom.app X).naturality g

@[reassoc (attr := simp)]
/--
lemma `μ_inv_natural_right` / 引理 `μ_inv_natural_right`

English:
lemma μ_inv_natural_right
  given: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  proof: by
  simp [Iso.eq_comp_inv]

中文:
引理 μ_inv_natural_right
  条件: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  证明: by
  simp [Iso.eq_comp_inv]

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv
-/
lemma μ_inv_natural_right (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (μ L W ε X Y₁).inv ≫ (L').obj X ◁ (L').map g =
      (L').map (X ◁ g) ≫ (μ L W ε X Y₂).inv := by
  simp [Iso.eq_comp_inv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftUnitor_hom_app` / 引理 `leftUnitor_hom_app`

English:
lemma leftUnitor_hom_app
  given: (Y : C)
  proof: by
  dsimp +instances [monoidalCategoryStruct, leftUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

中文:
引理 leftUnitor_hom_app
  条件: (Y : C)
  证明: by
  dsimp +instances [monoidalCategoryStruct, leftUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

Depends on / 依赖: comp_id, instances, leftUnitor, liftNatTrans_app, monoidalCategoryStruct
-/
lemma leftUnitor_hom_app (Y : C) :
    (fun_ ((L').obj Y)).hom =
      (ε' L W ε).inv ▷ (L').obj Y ≫ (μ _ _ _ _ _).hom ≫ (L').map (fun_ Y).hom := by
  dsimp +instances [monoidalCategoryStruct, leftUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightUnitor_hom_app` / 引理 `rightUnitor_hom_app`

English:
lemma rightUnitor_hom_app
  given: (X : C)
  proof: by
  dsimp +instances [monoidalCategoryStruct, rightUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

中文:
引理 rightUnitor_hom_app
  条件: (X : C)
  证明: by
  dsimp +instances [monoidalCategoryStruct, rightUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

Depends on / 依赖: comp_id, instances, liftNatTrans_app, monoidalCategoryStruct, rightUnitor
-/
lemma rightUnitor_hom_app (X : C) :
    (ρ_ ((L').obj X)).hom =
      (L').obj X ◁ (ε' L W ε).inv ≫ (μ _ _ _ _ _).hom ≫
        (L').map (ρ_ X).hom := by
  dsimp +instances [monoidalCategoryStruct, rightUnitor]
  rw [liftNatTrans_app]
  dsimp
  rw [assoc]
  change _ ≫ (μ L W ε _ _).hom ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `associator_hom_app` / 引理 `associator_hom_app`

English:
lemma associator_hom_app
  given: (X₁ X₂ X₃ : C)
  proof: by
  dsimp +instances [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl

中文:
引理 associator_hom_app
  条件: (X₁ X₂ X₃ : C)
  证明: by
  dsimp +instances [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl

Depends on / 依赖: Functor, Functor.map_id, Localization, Localization.associator_hom_app_app_app, NatTrans, NatTrans.id_app, associator, associator_hom_app_app_app, comp_id, id_app, id_comp, instances, map_id, monoidalCategoryStruct
-/
lemma associator_hom_app (X₁ X₂ X₃ : C) :
    (α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom =
      ((μ L W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom ≫ (L').map (α_ X₁ X₂ X₃).hom ≫
        (μ L W ε _ _).inv ≫ (𝟙 _ otimesₘ (μ L W ε _ _).inv) := by
  dsimp +instances [monoidalCategoryStruct, associator]
  simp only [Functor.map_id, comp_id, NatTrans.id_app, id_comp]
  rw [Localization.associator_hom_app_app_app]
  rfl

/--
lemma `id_tensorHom` / 引理 `id_tensorHom`

English:
lemma id_tensorHom
  given: (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂)
  proof: by
  simp +instances [monoidalCategoryStruct]

中文:
引理 id_tensorHom
  条件: (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂)
  证明: by
  simp +instances [monoidalCategoryStruct]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma id_tensorHom (X : LocalizedMonoidal L W ε) {Y₁ Y₂ : LocalizedMonoidal L W ε} (f : Y₁ ⟶ Y₂) :
    𝟙 X otimesₘ f = X ◁ f := by
  simp +instances [monoidalCategoryStruct]

/--
lemma `tensorHom_id` / 引理 `tensorHom_id`

English:
lemma tensorHom_id
  given: {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε)
  proof: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

中文:
引理 tensorHom_id
  条件: {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε)
  证明: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma tensorHom_id {X₁ X₂ : LocalizedMonoidal L W ε} (f : X₁ ⟶ X₂) (Y : LocalizedMonoidal L W ε) :
    f otimesₘ 𝟙 Y = f ▷ Y := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/--
lemma `tensor_comp` / 引理 `tensor_comp`

English:
lemma tensor_comp
  statement: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
  proof: by
  simp +instances [monoidalCategoryStruct]

中文:
引理 tensor_comp
  结论: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
  证明: by
  simp +instances [monoidalCategoryStruct]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) = (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) := by
  simp +instances [monoidalCategoryStruct]

/--
lemma `id_tensorHom_id` / 引理 `id_tensorHom_id`

English:
lemma id_tensorHom_id
  given: (X₁ X₂ : LocalizedMonoidal L W ε)
  statement: 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂)
  proof: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

中文:
引理 id_tensorHom_id
  条件: (X₁ X₂ : LocalizedMonoidal L W ε)
  结论: 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂)
  证明: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma id_tensorHom_id (X₁ X₂ : LocalizedMonoidal L W ε) : 𝟙 X₁ otimesₘ 𝟙 X₂ = 𝟙 (X₁ otimes X₂) := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/--
theorem `whiskerLeft_comp` / 定理 `whiskerLeft_comp`

English:
theorem whiskerLeft_comp
  statement: (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
  proof: by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc]

中文:
定理 whiskerLeft_comp
  结论: (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
  证明: by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc]

Depends on / 依赖: comp_id, id_tensorHom, tensor_comp
-/
theorem whiskerLeft_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Q ◁ (f ≫ g) = Q ◁ f ≫ Q ◁ g := by
  simp only [← id_tensorHom, ← tensor_comp, comp_id]

@[reassoc]
/--
theorem `whiskerRight_comp` / 定理 `whiskerRight_comp`

English:
theorem whiskerRight_comp
  statement: (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
  proof: by
  simp only [← tensorHom_id, ← tensor_comp, comp_id]

中文:
定理 whiskerRight_comp
  结论: (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
  证明: by
  simp only [← tensorHom_id, ← tensor_comp, comp_id]

Depends on / 依赖: comp_id, tensorHom_id, tensor_comp
-/
theorem whiskerRight_comp (Q : LocalizedMonoidal L W ε) {X Y Z : LocalizedMonoidal L W ε}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g) ▷ Q = f ▷ Q ≫ g ▷ Q := by
  simp only [← tensorHom_id, ← tensor_comp, comp_id]

/--
lemma `whiskerLeft_id` / 引理 `whiskerLeft_id`

English:
lemma whiskerLeft_id
  given: (X Y : LocalizedMonoidal L W ε)
  proof: by
  simp +instances [monoidalCategoryStruct]

中文:
引理 whiskerLeft_id
  条件: (X Y : LocalizedMonoidal L W ε)
  证明: by
  simp +instances [monoidalCategoryStruct]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma whiskerLeft_id (X Y : LocalizedMonoidal L W ε) :
    X ◁ (𝟙 Y) = 𝟙 _ := by
  simp +instances [monoidalCategoryStruct]

/--
lemma `whiskerRight_id` / 引理 `whiskerRight_id`

English:
lemma whiskerRight_id
  given: (X Y : LocalizedMonoidal L W ε)
  proof: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

中文:
引理 whiskerRight_id
  条件: (X Y : LocalizedMonoidal L W ε)
  证明: by
  simp +instances [monoidalCategoryStruct]

@[reassoc]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma whiskerRight_id (X Y : LocalizedMonoidal L W ε) :
    (𝟙 X) ▷ Y = 𝟙 _ := by
  simp +instances [monoidalCategoryStruct]

@[reassoc]
/--
lemma `whisker_exchange` / 引理 `whisker_exchange`

English:
lemma whisker_exchange
  given: {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ Z)
  proof: by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

中文:
引理 whisker_exchange
  条件: {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ Z)
  证明: by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

Depends on / 依赖: comp_id, id_comp, id_tensorHom, tensorHom_id, tensor_comp
-/
lemma whisker_exchange {Q X Y Z : LocalizedMonoidal L W ε} (f : Q ⟶ X) (g : Y ⟶ Z) :
    Q ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `associator_naturality` / 引理 `associator_naturality`

English:
lemma associator_naturality
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
  proof: by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp +instances only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁]; rw [assoc]; rw [reassoc_of% h₂]; rw [reassoc_of% h₃]

@[reassoc]

中文:
引理 associator_naturality
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
  证明: by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp +instances only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁]; rw [assoc]; rw [reassoc_of% h₂]; rw [reassoc_of% h₃]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, NatTrans, NatTrans.congr_app, associator, congr_app, hom.app, hom.naturality, instances, map_comp, monoidalCategoryStruct, naturality, reassoc_of
-/
lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ otimesₘ f₂) otimesₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ otimesₘ f₂ otimesₘ f₃) := by
  have h₁ := (((associator L W ε).hom.app Y₁).app Y₂).naturality f₃
  have h₂ := NatTrans.congr_app (((associator L W ε).hom.app Y₁).naturality f₂) X₃
  have h₃ := NatTrans.congr_app (NatTrans.congr_app ((associator L W ε).hom.naturality f₁) X₂) X₃
  simp +instances only [monoidalCategoryStruct, Functor.map_comp, assoc]
  dsimp at h₁ h₂ h₃ ⊢
  rw [h₁]; rw [assoc]; rw [reassoc_of% h₂]; rw [reassoc_of% h₃]

@[reassoc]
/--
lemma `associator_naturality₁` / 引理 `associator_naturality₁`

English:
lemma associator_naturality₁
  given: {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁)
  proof: by
  simp only [← tensorHom_id, associator_naturality, id_tensorHom_id]

@[reassoc]

中文:
引理 associator_naturality₁
  条件: {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁)
  证明: by
  simp only [← tensorHom_id, associator_naturality, id_tensorHom_id]

@[reassoc]

Depends on / 依赖: associator_naturality, id_tensorHom_id, tensorHom_id
-/
lemma associator_naturality₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (f₁ : X₁ ⟶ Y₁) :
    ((f₁ ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ▷ (X₂ otimes X₃)) := by
  simp only [← tensorHom_id, associator_naturality, id_tensorHom_id]

@[reassoc]
/--
lemma `associator_naturality₂` / 引理 `associator_naturality₂`

English:
lemma associator_naturality₂
  given: {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂)
  proof: by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]

中文:
引理 associator_naturality₂
  条件: {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂)
  证明: by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]

Depends on / 依赖: associator_naturality, id_tensorHom, tensorHom_id
-/
lemma associator_naturality₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (f₂ : X₂ ⟶ Y₂) :
    ((X₁ ◁ f₂) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (f₂ ▷ X₃)) := by
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality]

@[reassoc]
/--
lemma `associator_naturality₃` / 引理 `associator_naturality₃`

English:
lemma associator_naturality₃
  given: {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃)
  proof: by
  simp only [← id_tensorHom, ← id_tensorHom_id, associator_naturality]

中文:
引理 associator_naturality₃
  条件: {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃)
  证明: by
  simp only [← id_tensorHom, ← id_tensorHom_id, associator_naturality]

Depends on / 依赖: associator_naturality, id_tensorHom, id_tensorHom_id
-/
lemma associator_naturality₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (f₃ : X₃ ⟶ Y₃) :
    ((X₁ otimes X₂) ◁ f₃) ≫ (α_ X₁ X₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (X₁ ◁ (X₂ ◁ f₃)) := by
  simp only [← id_tensorHom, ← id_tensorHom_id, associator_naturality]

/--
lemma `pentagon_aux₁` / 引理 `pentagon_aux₁`

English:
lemma pentagon_aux₁
  given: {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁)
  proof: by
  simp only [associator_naturality₁_assoc, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, comp_id]

中文:
引理 pentagon_aux₁
  条件: {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁)
  证明: by
  simp only [associator_naturality₁_assoc, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, whiskerRight_comp, whiskerRight_id
-/
lemma pentagon_aux₁ {X₁ X₂ X₃ Y₁ : LocalizedMonoidal L W ε} (i : X₁ ≅ Y₁) :
    ((i.hom ▷ X₂) ▷ X₃) ≫ (α_ Y₁ X₂ X₃).hom ≫ (i.inv ▷ (X₂ otimes X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₁_assoc, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, comp_id]

/--
lemma `pentagon_aux₂` / 引理 `pentagon_aux₂`

English:
lemma pentagon_aux₂
  given: {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂)
  proof: by
  simp only [associator_naturality₂_assoc, ← whiskerLeft_comp, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, whiskerLeft_id, comp_id]

中文:
引理 pentagon_aux₂
  条件: {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂)
  证明: by
  simp only [associator_naturality₂_assoc, ← whiskerLeft_comp, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, whiskerLeft_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, whiskerLeft_comp, whiskerLeft_id, whiskerRight_comp, whiskerRight_id
-/
lemma pentagon_aux₂ {X₁ X₂ X₃ Y₂ : LocalizedMonoidal L W ε} (i : X₂ ≅ Y₂) :
    ((X₁ ◁ i.hom) ▷ X₃) ≫ (α_ X₁ Y₂ X₃).hom ≫ (X₁ ◁ (i.inv ▷ X₃)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₂_assoc, ← whiskerLeft_comp, ← whiskerRight_comp,
    Iso.hom_inv_id, whiskerRight_id, whiskerLeft_id, comp_id]

/--
lemma `pentagon_aux₃` / 引理 `pentagon_aux₃`

English:
lemma pentagon_aux₃
  given: {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃)
  proof: by
  simp only [associator_naturality₃_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]

中文:
引理 pentagon_aux₃
  条件: {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃)
  证明: by
  simp only [associator_naturality₃_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, whiskerLeft_comp, whiskerLeft_id
-/
lemma pentagon_aux₃ {X₁ X₂ X₃ Y₃ : LocalizedMonoidal L W ε} (i : X₃ ≅ Y₃) :
    ((X₁ otimes X₂) ◁ i.hom) ≫ (α_ X₁ X₂ Y₃).hom ≫ (X₁ ◁ (X₂ ◁ i.inv)) = (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality₃_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, comp_id]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (L').EssSurj
  body: Localization.essSurj L' W

中文:
实例 :
  签名: (L').本质满射
  定义体: Localization.essSurj L' W

Depends on / 依赖: Localization, Localization.essSurj, essSurj
-/
instance : (L').EssSurj := Localization.essSurj L' W

variable {L W ε} in
/--
lemma `pentagon` / 引理 `pentagon`

English:
lemma pentagon
  given: (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε)
  proof: by
  obtain ⟨X₁, ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : exists X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : exists X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  suffices Pentagon ((L').obj X₁) ((L').obj X₂) ((L').obj X₃) ((L').obj X₄) by
    dsimp [Pentagon]
    refine Eq.trans ?_ (((((e₁.inv otimesₘ e₂.inv) otimesₘ e₃.inv) otimesₘ e₄.inv) ≫= this =≫
      (e₁.hom otimesₘ e₂.hom otimesₘ e₃.hom otimesₘ e₄.hom)).trans ?_)
    · rw [← id_tensorHom, ← id_tensorHom, ← tensorHom_id, ← tensorHom_id, assoc, assoc,
        ← tensor_comp, ← associator_naturality, id_comp, ← comp_id e₁.hom,
        tensor_comp, ← associator_naturality_assoc, ← comp_id (𝟙 ((L').obj X₄)),
        ← tensor_comp_assoc, associator_naturality, comp_id, comp_id,
        ← tensor_comp_assoc, assoc, e₄.inv_hom_id, ← tensor_comp, e₁.inv_hom_id,
        ← tensor_comp, e₂.inv_hom_id, e₃.inv_hom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
    · rw [assoc, associator_naturality_assoc, associator_naturality_assoc,
        ← tensor_comp, e₁.inv_hom_id, ← tensor_comp, e₂.inv_hom_id, ← tensor_comp,
        e₃.inv_hom_id, e₄.inv_hom_id, id_tensorHom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
  dsimp [Pentagon]
  have : ((L').obj X₁ ◁ (μ L W ε X₂ X₃).inv) ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) ((L').obj X₂ otimes (L').obj X₃) ((L').obj X₄)).hom ≫
        (L').obj X₁ ◁ (μ L W ε X₂ X₃).hom ▷ (L').obj X₄ =
          (α_ ((L').obj X₁) ((L').obj (X₂ otimes X₃)) ((L').obj X₄)).hom :=
    pentagon_aux₂ _ _ _ (μ L W ε X₂ X₃).symm
  rw [associator_hom_app]; rw [tensorHom_id]; rw [id_tensorHom]; rw [associator_hom_app]; rw [tensorHom_id]; rw [whiskerLeft_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [whiskerRight_comp]; rw [assoc]; rw [reassoc_of% this]; rw [associator_hom_app]; rw [tensorHom_id]; rw [← pentagon_aux₁ (X₂ := (L').obj X₃) (X₃ := (L').obj X₄) (i := μ L W ε X₁ X₂)]; rw [← pentagon_aux₃ (X₁ := (L').obj X₁) (X₂ := (L').obj X₂) (i := μ L W ε X₃ X₄)]; rw [associator_hom_app]; rw [associator_hom_app]
  simp only [assoc, ← whiskerRight_comp_assoc, Iso.inv_hom_id, comp_id, μ_natural_left_assoc,
    id_tensorHom, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (L').map_comp_assoc]; rw [whiskerLeft_comp]; rw [μ_inv_natural_right_assoc]; rw [← (L').map_comp_assoc]
  simp only [assoc, MonoidalCategory.pentagon, Functor.map_comp, tensorHom_id,
    whiskerRight_comp_assoc]
  congr 3; simp only [← assoc]; congr
  simp only [← cancel_mono (μ L W ε (X₁ otimes X₂) (X₃ otimes X₄)).inv, assoc, id_comp,
    whisker_exchange_assoc, ← whiskerRight_comp_assoc,
    Iso.inv_hom_id, whiskerRight_id, ← whiskerLeft_comp,
    whiskerLeft_id]

中文:
引理 pentagon
  条件: (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε)
  证明: by
  obtain ⟨X₁, ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : exists X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : exists X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  suffices Pentagon ((L').obj X₁) ((L').obj X₂) ((L').obj X₃) ((L').obj X₄) by
    dsimp [Pentagon]
    refine Eq.trans ?_ (((((e₁.inv otimesₘ e₂.inv) otimesₘ e₃.inv) otimesₘ e₄.inv) ≫= this =≫
      (e₁.hom otimesₘ e₂.hom otimesₘ e₃.hom otimesₘ e₄.hom)).trans ?_)
    · rw [← id_tensorHom, ← id_tensorHom, ← tensorHom_id, ← tensorHom_id, assoc, assoc,
        ← tensor_comp, ← associator_naturality, id_comp, ← comp_id e₁.hom,
        tensor_comp, ← associator_naturality_assoc, ← comp_id (𝟙 ((L').obj X₄)),
        ← tensor_comp_assoc, associator_naturality, comp_id, comp_id,
        ← tensor_comp_assoc, assoc, e₄.inv_hom_id, ← tensor_comp, e₁.inv_hom_id,
        ← tensor_comp, e₂.inv_hom_id, e₃.inv_hom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
    · rw [assoc, associator_naturality_assoc, associator_naturality_assoc,
        ← tensor_comp, e₁.inv_hom_id, ← tensor_comp, e₂.inv_hom_id, ← tensor_comp,
        e₃.inv_hom_id, e₄.inv_hom_id, id_tensorHom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
  dsimp [Pentagon]
  have : ((L').obj X₁ ◁ (μ L W ε X₂ X₃).inv) ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) ((L').obj X₂ otimes (L').obj X₃) ((L').obj X₄)).hom ≫
        (L').obj X₁ ◁ (μ L W ε X₂ X₃).hom ▷ (L').obj X₄ =
          (α_ ((L').obj X₁) ((L').obj (X₂ otimes X₃)) ((L').obj X₄)).hom :=
    pentagon_aux₂ _ _ _ (μ L W ε X₂ X₃).symm
  rw [associator_hom_app]; rw [tensorHom_id]; rw [id_tensorHom]; rw [associator_hom_app]; rw [tensorHom_id]; rw [whiskerLeft_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [whiskerRight_comp]; rw [assoc]; rw [reassoc_of% this]; rw [associator_hom_app]; rw [tensorHom_id]; rw [← pentagon_aux₁ (X₂ := (L').obj X₃) (X₃ := (L').obj X₄) (i := μ L W ε X₁ X₂)]; rw [← pentagon_aux₃ (X₁ := (L').obj X₁) (X₂ := (L').obj X₂) (i := μ L W ε X₃ X₄)]; rw [associator_hom_app]; rw [associator_hom_app]
  simp only [assoc, ← whiskerRight_comp_assoc, Iso.inv_hom_id, comp_id, μ_natural_left_assoc,
    id_tensorHom, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (L').map_comp_assoc]; rw [whiskerLeft_comp]; rw [μ_inv_natural_right_assoc]; rw [← (L').map_comp_assoc]
  simp only [assoc, MonoidalCategory.pentagon, Functor.map_comp, tensorHom_id,
    whiskerRight_comp_assoc]
  congr 3; simp only [← assoc]; congr
  simp only [← cancel_mono (μ L W ε (X₁ otimes X₂) (X₃ otimes X₄)).inv, assoc, id_comp,
    whisker_exchange_assoc, ← whiskerRight_comp_assoc,
    Iso.inv_hom_id, whiskerRight_id, ← whiskerLeft_comp,
    whiskerLeft_id]

Depends on / 依赖: Eq.trans, Nonempty, Pentagon, objObjPreimageIso
-/
lemma pentagon (Y₁ Y₂ Y₃ Y₄ : LocalizedMonoidal L W ε) :
    Pentagon Y₁ Y₂ Y₃ Y₄ := by
  obtain ⟨X₁, ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ Y₁) := ⟨_, ⟨(L').objObjPreimageIso Y₁⟩⟩
  obtain ⟨X₂, ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y₂) := ⟨_, ⟨(L').objObjPreimageIso Y₂⟩⟩
  obtain ⟨X₃, ⟨e₃⟩⟩ : exists X₃, Nonempty ((L').obj X₃ ≅ Y₃) := ⟨_, ⟨(L').objObjPreimageIso Y₃⟩⟩
  obtain ⟨X₄, ⟨e₄⟩⟩ : exists X₄, Nonempty ((L').obj X₄ ≅ Y₄) := ⟨_, ⟨(L').objObjPreimageIso Y₄⟩⟩
  suffices Pentagon ((L').obj X₁) ((L').obj X₂) ((L').obj X₃) ((L').obj X₄) by
    dsimp [Pentagon]
    refine Eq.trans ?_ (((((e₁.inv otimesₘ e₂.inv) otimesₘ e₃.inv) otimesₘ e₄.inv) ≫= this =≫
      (e₁.hom otimesₘ e₂.hom otimesₘ e₃.hom otimesₘ e₄.hom)).trans ?_)
    · rw [← id_tensorHom, ← id_tensorHom, ← tensorHom_id, ← tensorHom_id, assoc, assoc,
        ← tensor_comp, ← associator_naturality, id_comp, ← comp_id e₁.hom,
        tensor_comp, ← associator_naturality_assoc, ← comp_id (𝟙 ((L').obj X₄)),
        ← tensor_comp_assoc, associator_naturality, comp_id, comp_id,
        ← tensor_comp_assoc, assoc, e₄.inv_hom_id, ← tensor_comp, e₁.inv_hom_id,
        ← tensor_comp, e₂.inv_hom_id, e₃.inv_hom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
    · rw [assoc, associator_naturality_assoc, associator_naturality_assoc,
        ← tensor_comp, e₁.inv_hom_id, ← tensor_comp, e₂.inv_hom_id, ← tensor_comp,
        e₃.inv_hom_id, e₄.inv_hom_id, id_tensorHom_id, id_tensorHom_id, id_tensorHom_id, comp_id]
  dsimp [Pentagon]
  have : ((L').obj X₁ ◁ (μ L W ε X₂ X₃).inv) ▷ (L').obj X₄ ≫
      (α_ ((L').obj X₁) ((L').obj X₂ otimes (L').obj X₃) ((L').obj X₄)).hom ≫
        (L').obj X₁ ◁ (μ L W ε X₂ X₃).hom ▷ (L').obj X₄ =
          (α_ ((L').obj X₁) ((L').obj (X₂ otimes X₃)) ((L').obj X₄)).hom :=
    pentagon_aux₂ _ _ _ (μ L W ε X₂ X₃).symm
  rw [associator_hom_app]; rw [tensorHom_id]; rw [id_tensorHom]; rw [associator_hom_app]; rw [tensorHom_id]; rw [whiskerLeft_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [whiskerRight_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [whiskerRight_comp]; rw [assoc]; rw [reassoc_of% this]; rw [associator_hom_app]; rw [tensorHom_id]; rw [← pentagon_aux₁ (X₂ := (L').obj X₃) (X₃ := (L').obj X₄) (i := μ L W ε X₁ X₂)]; rw [← pentagon_aux₃ (X₁ := (L').obj X₁) (X₂ := (L').obj X₂) (i := μ L W ε X₃ X₄)]; rw [associator_hom_app]; rw [associator_hom_app]
  simp only [assoc, ← whiskerRight_comp_assoc, Iso.inv_hom_id, comp_id, μ_natural_left_assoc,
    id_tensorHom, ← whiskerLeft_comp, Iso.inv_hom_id_assoc]
  rw [← (L').map_comp_assoc]; rw [whiskerLeft_comp]; rw [μ_inv_natural_right_assoc]; rw [← (L').map_comp_assoc]
  simp only [assoc, MonoidalCategory.pentagon, Functor.map_comp, tensorHom_id,
    whiskerRight_comp_assoc]
  congr 3; simp only [← assoc]; congr
  simp only [← cancel_mono (μ L W ε (X₁ otimes X₂) (X₃ otimes X₄)).inv, assoc, id_comp,
    whisker_exchange_assoc, ← whiskerRight_comp_assoc,
    Iso.inv_hom_id, whiskerRight_id, ← whiskerLeft_comp,
    whiskerLeft_id]

/--
lemma `leftUnitor_naturality` / 引理 `leftUnitor_naturality`

English:
lemma leftUnitor_naturality
  given: {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y)
  proof: by
  simp +instances [monoidalCategoryStruct]

中文:
引理 leftUnitor_naturality
  条件: {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y)
  证明: by
  simp +instances [monoidalCategoryStruct]

Depends on / 依赖: instances, monoidalCategoryStruct
-/
lemma leftUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    𝟙_ (LocalizedMonoidal L W ε) ◁ f ≫ (fun_ Y).hom = (fun_ X).hom ≫ f := by
  simp +instances [monoidalCategoryStruct]

/--
lemma `rightUnitor_naturality` / 引理 `rightUnitor_naturality`

English:
lemma rightUnitor_naturality
  given: {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y)
  proof: (rightUnitor L W ε).hom.naturality f

@[reassoc]

中文:
引理 rightUnitor_naturality
  条件: {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y)
  证明: (rightUnitor L W ε).hom.naturality f

@[reassoc]

Depends on / 依赖: hom.naturality, naturality, rightUnitor
-/
lemma rightUnitor_naturality {X Y : LocalizedMonoidal L W ε} (f : X ⟶ Y) :
    f ▷ 𝟙_ (LocalizedMonoidal L W ε) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f :=
  (rightUnitor L W ε).hom.naturality f

@[reassoc]
/--
lemma `triangle_aux₁` / 引理 `triangle_aux₁`

English:
lemma triangle_aux₁
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
  proof: by
  simp only [associator_naturality_assoc, ← tensor_comp, Iso.hom_inv_id, id_tensorHom,
    whiskerLeft_id, comp_id]

中文:
引理 triangle_aux₁
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
  证明: by
  simp only [associator_naturality_assoc, ← tensor_comp, Iso.hom_inv_id, id_tensorHom,
    whiskerLeft_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, associator_naturality_assoc, comp_id, hom_inv_id, id_tensorHom, tensor_comp, whiskerLeft_id
-/
lemma triangle_aux₁ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : LocalizedMonoidal L W ε}
    (i₁ : X₁ ≅ Y₁) (i₂ : X₂ ≅ Y₂) (i₃ : X₃ ≅ Y₃) :
    ((i₁.hom otimesₘ i₂.hom) otimesₘ i₃.hom) ≫ (α_ Y₁ Y₂ Y₃).hom ≫ (i₁.inv otimesₘ i₂.inv otimesₘ i₃.inv) =
      (α_ X₁ X₂ X₃).hom := by
  simp only [associator_naturality_assoc, ← tensor_comp, Iso.hom_inv_id, id_tensorHom,
    whiskerLeft_id, comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `triangle_aux₂` / 引理 `triangle_aux₂`

English:
lemma triangle_aux₂
  statement: {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
  proof: by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, comp_id, id_comp,
    ← tensor_comp_assoc, id_comp]
  congr 3
  exact (comp_id _).symm

中文:
引理 triangle_aux₂
  结论: {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
  证明: by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, comp_id, id_comp,
    ← tensor_comp_assoc, id_comp]
  congr 3
  exact (comp_id _).symm

Depends on / 依赖: comp_id, id_comp, id_tensorHom, tensorHom_id, tensor_comp, tensor_comp_assoc
-/
lemma triangle_aux₂ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) :
      e₁.hom otimesₘ (ε.hom otimesₘ e₂.hom) ≫ (fun_ Y).hom =
        (L').obj X' ◁ ((ε' L W ε).hom ▷ (L').obj Y' ≫
          𝟙_ _ ◁ e₂.hom ≫ (fun_ Y).hom) ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, comp_id, id_comp,
    ← tensor_comp_assoc, id_comp]
  congr 3
  exact (comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `triangle_aux₃` / 引理 `triangle_aux₃`

English:
lemma triangle_aux₃
  statement: {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
  proof: by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, assoc, comp_id,
    id_comp, Iso.inv_hom_id]
  congr
  rw [← cancel_mono e₁.inv]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← rightUnitor_naturality]; rw [rightUnitor_hom_app]; rw [← tensorHom_id]; rw [← id_tensorHom]; rw [← tensor_comp_assoc]; rw [comp_id]; rw [id_comp]

中文:
引理 triangle_aux₃
  结论: {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
  证明: by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, assoc, comp_id,
    id_comp, Iso.inv_hom_id]
  congr
  rw [← cancel_mono e₁.inv]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← rightUnitor_naturality]; rw [rightUnitor_hom_app]; rw [← tensorHom_id]; rw [← id_tensorHom]; rw [← tensor_comp_assoc]; rw [comp_id]; rw [id_comp]

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, cancel_mono, comp_id, hom_inv_id, id_comp, id_tensorHom, inv_hom_id, rightUnitor_hom_app, rightUnitor_naturality, tensorHom_id, tensor_comp, tensor_comp_assoc
-/
lemma triangle_aux₃ {X Y : LocalizedMonoidal L W ε} {X' Y' : C}
    (e₁ : (L').obj X' ≅ X) (e₂ : (L').obj Y' ≅ Y) : (ρ_ X).hom ▷ _ =
      ((e₁.inv otimesₘ ε.inv) otimesₘ e₂.inv) ≫ _ ◁ e₂.hom ≫ ((μ L W ε X' (𝟙_ C)).hom ≫
        (L').map (ρ_ X').hom) ▷ Y ≫ e₁.hom ▷ Y := by
  simp only [← tensorHom_id, ← id_tensorHom, ← tensor_comp, assoc, comp_id,
    id_comp, Iso.inv_hom_id]
  congr
  rw [← cancel_mono e₁.inv]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← rightUnitor_naturality]; rw [rightUnitor_hom_app]; rw [← tensorHom_id]; rw [← id_tensorHom]; rw [← tensor_comp_assoc]; rw [comp_id]; rw [id_comp]

set_option backward.isDefEq.respectTransparency.types false in
variable {L W ε} in
/--
lemma `triangle` / 引理 `triangle`

English:
lemma triangle
  given: (X Y : LocalizedMonoidal L W ε)
  proof: by
  obtain ⟨X', ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
  obtain ⟨Y', ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
  have h₁ := (associator_hom_app L W ε X' (𝟙_ _) Y' =≫
    (𝟙 ((L').obj X') otimesₘ (μ L W ε (𝟙_ C) Y').hom))
  simp only [assoc, id_tensorHom, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id, Iso.inv_hom_id,
    ← cancel_mono (μ L W ε X' (𝟙_ C otimes Y')).hom] at h₁
  have h₂ := (ε' L W ε).hom ▷ (L').obj Y' ≫= leftUnitor_hom_app L W ε Y'
  simp only [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id, id_comp] at h₂
  have h₃ := (((μ L W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom) ≫=
    ((L').congr_map (MonoidalCategory.triangle X' Y'))
  simp only [assoc, Functor.map_comp, ← reassoc_of% h₁] at h₃
  rw [← μ_natural_left]; rw [tensorHom_id]; rw [← whiskerRight_comp_assoc]; rw [← μ_natural_right]; rw [← Iso.comp_inv_eq]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← whiskerLeft_comp]; rw [← h₂] at h₃
  replace h₃ := ((e₁.inv otimesₘ ε.inv) otimesₘ e₂.inv) ≫= (h₃ =≫ (_ ◁ e₂.hom)) =≫ (e₁.hom ▷ _)
  simp only [← whiskerLeft_comp, assoc, ← leftUnitor_naturality, ← whisker_exchange] at h₃
  have : _ = (α_ X (𝟙_ (LocalizedMonoidal L W ε)) Y).hom :=
    triangle_aux₁ _ _ _ e₁.symm ε.symm e₂.symm
  simp only [← this, Iso.symm_hom, Iso.symm_inv, assoc,
    ← id_tensorHom, ← tensor_comp, comp_id]
  convert! h₃
  · exact triangle_aux₂ _ _ _ e₁ e₂
  · exact triangle_aux₃ _ _ _ e₁ e₂

中文:
引理 triangle
  条件: (X Y : LocalizedMonoidal L W ε)
  证明: by
  obtain ⟨X', ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
  obtain ⟨Y', ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
  have h₁ := (associator_hom_app L W ε X' (𝟙_ _) Y' =≫
    (𝟙 ((L').obj X') otimesₘ (μ L W ε (𝟙_ C) Y').hom))
  simp only [assoc, id_tensorHom, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id, Iso.inv_hom_id,
    ← cancel_mono (μ L W ε X' (𝟙_ C otimes Y')).hom] at h₁
  have h₂ := (ε' L W ε).hom ▷ (L').obj Y' ≫= leftUnitor_hom_app L W ε Y'
  simp only [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id, id_comp] at h₂
  have h₃ := (((μ L W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom) ≫=
    ((L').congr_map (MonoidalCategory.triangle X' Y'))
  simp only [assoc, Functor.map_comp, ← reassoc_of% h₁] at h₃
  rw [← μ_natural_left]; rw [tensorHom_id]; rw [← whiskerRight_comp_assoc]; rw [← μ_natural_right]; rw [← Iso.comp_inv_eq]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← whiskerLeft_comp]; rw [← h₂] at h₃
  replace h₃ := ((e₁.inv otimesₘ ε.inv) otimesₘ e₂.inv) ≫= (h₃ =≫ (_ ◁ e₂.hom)) =≫ (e₁.hom ▷ _)
  simp only [← whiskerLeft_comp, assoc, ← leftUnitor_naturality, ← whisker_exchange] at h₃
  have : _ = (α_ X (𝟙_ (LocalizedMonoidal L W ε)) Y).hom :=
    triangle_aux₁ _ _ _ e₁.symm ε.symm e₂.symm
  simp only [← this, Iso.symm_hom, Iso.symm_inv, assoc,
    ← id_tensorHom, ← tensor_comp, comp_id]
  convert! h₃
  · exact triangle_aux₂ _ _ _ e₁ e₂
  · exact triangle_aux₃ _ _ _ e₁ e₂

Depends on / 依赖: Iso.inv_hom_id, Nonempty, associator_hom_app, cancel_mono, comp_id, id_tensorHom, inv_hom_id, objObjPreimageIso, otimes, whiskerLeft_comp, whiskerLeft_id
-/
lemma triangle (X Y : LocalizedMonoidal L W ε) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (fun_ Y).hom = (ρ_ X).hom ▷ Y := by
  obtain ⟨X', ⟨e₁⟩⟩ : exists X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
  obtain ⟨Y', ⟨e₂⟩⟩ : exists X₂, Nonempty ((L').obj X₂ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
  have h₁ := (associator_hom_app L W ε X' (𝟙_ _) Y' =≫
    (𝟙 ((L').obj X') otimesₘ (μ L W ε (𝟙_ C) Y').hom))
  simp only [assoc, id_tensorHom, ← whiskerLeft_comp,
    Iso.inv_hom_id, whiskerLeft_id, comp_id, Iso.inv_hom_id,
    ← cancel_mono (μ L W ε X' (𝟙_ C otimes Y')).hom] at h₁
  have h₂ := (ε' L W ε).hom ▷ (L').obj Y' ≫= leftUnitor_hom_app L W ε Y'
  simp only [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id, id_comp] at h₂
  have h₃ := (((μ L W ε _ _).hom otimesₘ 𝟙 _) ≫ (μ L W ε _ _).hom) ≫=
    ((L').congr_map (MonoidalCategory.triangle X' Y'))
  simp only [assoc, Functor.map_comp, ← reassoc_of% h₁] at h₃
  rw [← μ_natural_left]; rw [tensorHom_id]; rw [← whiskerRight_comp_assoc]; rw [← μ_natural_right]; rw [← Iso.comp_inv_eq]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← whiskerLeft_comp]; rw [← h₂] at h₃
  replace h₃ := ((e₁.inv otimesₘ ε.inv) otimesₘ e₂.inv) ≫= (h₃ =≫ (_ ◁ e₂.hom)) =≫ (e₁.hom ▷ _)
  simp only [← whiskerLeft_comp, assoc, ← leftUnitor_naturality, ← whisker_exchange] at h₃
  have : _ = (α_ X (𝟙_ (LocalizedMonoidal L W ε)) Y).hom :=
    triangle_aux₁ _ _ _ e₁.symm ε.symm e₂.symm
  simp only [← this, Iso.symm_hom, Iso.symm_inv, assoc,
    ← id_tensorHom, ← tensor_comp, comp_id]
  convert! h₃
  · exact triangle_aux₂ _ _ _ e₁ e₂
  · exact triangle_aux₃ _ _ _ e₁ e₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: by intros; simp +instances [monoidalCategoryStruct]
  id_tensorHom_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  tensorHom_comp_tensorHom := by intros; simp +instances [monoidalCategoryStruct]
  whiskerLeft_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  id_whiskerRight := by
    intros
    simp +instances [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by apply associator_naturality
  leftUnitor_naturality := by intros; simp +instances [monoidalCategoryStruct]
  rightUnitor_naturality := fun f => (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := triangle

中文:
实例 :
  定义体: by intros; simp +instances [monoidalCategoryStruct]
  id_tensorHom_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  tensorHom_comp_tensorHom := by intros; simp +instances [monoidalCategoryStruct]
  whiskerLeft_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  id_whiskerRight := by
    intros
    simp +instances [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by apply associator_naturality
  leftUnitor_naturality := by intros; simp +instances [monoidalCategoryStruct]
  rightUnitor_naturality := fun f => (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := triangle

Depends on / 依赖: associator_naturality, id_tensorHom_id, id_whiskerRight, instances, intros, leftUnitor_naturality, monoidalCategoryStruc, monoidalCategoryStruct, tensorHom_comp_tensorHom, whiskerLeft_id
-/
noncomputable instance :
    MonoidalCategory (LocalizedMonoidal L W ε) where
  tensorHom_def := by intros; simp +instances [monoidalCategoryStruct]
  id_tensorHom_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  tensorHom_comp_tensorHom := by intros; simp +instances [monoidalCategoryStruct]
  whiskerLeft_id := by
    intros
    simp +instances [monoidalCategoryStruct]
  id_whiskerRight := by
    intros
    simp +instances [monoidalCategoryStruct]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by apply associator_naturality
  leftUnitor_naturality := by intros; simp +instances [monoidalCategoryStruct]
  rightUnitor_naturality := fun f => (rightUnitor L W ε).hom.naturality f
  pentagon := pentagon
  triangle := triangle

end Monoidal

end Localization

open Localization.Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toMonoidalCategory L W ε).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := ε.symm
      μIso X Y := μ L W ε X Y
      associativity X Y Z := by simp [associator_hom_app L W ε X Y Z]
      left_unitality Y := leftUnitor_hom_app L W ε Y
      right_unitality X := rightUnitor_hom_app L W ε X }

local notation "L'" => toMonoidalCategory L W ε

中文:
实例 :
  签名: (toMonoidalCategory L W ε).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := ε.symm
      μIso X Y := μ L W ε X Y
      associativity X Y Z := by simp [associator_hom_app L W ε X Y Z]
      left_unitality Y := leftUnitor_hom_app L W ε Y
      right_unitality X := rightUnitor_hom_app L W ε X }

local notation "L'" => toMonoidalCategory L W ε

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, associativity, associator_hom_app, leftUnitor_hom_app, left_unitality, rightUnitor_hom_app, right_unitality, toMonoidal
-/
noncomputable instance : (toMonoidalCategory L W ε).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ε.symm
      μIso X Y := μ L W ε X Y
      associativity X Y Z := by simp [associator_hom_app L W ε X Y Z]
      left_unitality Y := leftUnitor_hom_app L W ε Y
      right_unitality X := rightUnitor_hom_app L W ε X }

local notation "L'" => toMonoidalCategory L W ε

/--
lemma `associator_hom` / 引理 `associator_hom`

English:
lemma associator_hom
  given: (X Y Z : C)
  proof: by
  simp

中文:
引理 associator_hom
  条件: (X Y Z : C)
  证明: by
  simp
-/
lemma associator_hom (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom =
    (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
      (Functor.LaxMonoidal.μ (L') (X otimes Y) Z) ≫
        (L').map (α_ X Y Z).hom ≫
          (Functor.OplaxMonoidal.δ (L') X (Y otimes Z)) ≫
            ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z) := by
  simp

/--
lemma `associator_inv` / 引理 `associator_inv`

English:
lemma associator_inv
  given: (X Y Z : C)
  proof: by
  simp

中文:
引理 associator_inv
  条件: (X Y Z : C)
  证明: by
  simp
-/
lemma associator_inv (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv =
    (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
      (Functor.LaxMonoidal.μ (L') X (Y otimes Z)) ≫
        (L').map (α_ X Y Z).inv ≫
          (Functor.OplaxMonoidal.δ (L') (X otimes Y) Z) ≫
            (Functor.OplaxMonoidal.δ (L') X Y) ▷ ((L').obj Z) := by
  simp


end CategoryTheory
