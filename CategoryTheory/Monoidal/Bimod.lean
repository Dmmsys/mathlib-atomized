/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Oleksandr Manzyuk
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# The category of bimodule objects over a pair of monoid objects.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

section

open CategoryTheory.Limits

variable [HasCoequalizers C]

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/--
theorem `id_tensor_π_preserves_coequalizer_inv_desc` / 定理 `id_tensor_π_preserves_coequalizer_inv_desc`

English:
theorem id_tensor_π_preserves_coequalizer_inv_desc
  statement: {W X Y Z : C} (f g : X ⟶ Y) (h : Z otimes Y ⟶ W)
  proof: map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

中文:
定理 id_tensor_π_preserves_coequalizer_inv_desc
  结论: {W X Y Z : C} (f g : X ⟶ Y) (h : Z otimes Y ⟶ W)
  证明: map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

Depends on / 依赖: tensorLeft
-/
theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z otimes Y ⟶ W)
    (wh : (Z ◁ f) ≫ h = (Z ◁ g) ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

/--
theorem `id_tensor_π_preserves_coequalizer_inv_colimMap_desc` / 定理 `id_tensor_π_preserves_coequalizer_inv_colimMap_desc`

English:
theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc
  statement: {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
  proof: map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh

中文:
定理 id_tensor_π_preserves_coequalizer_inv_colimMap_desc
  结论: {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
  证明: map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh

Depends on / 依赖: tensorLeft
-/
theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : Z otimes X ⟶ X') (q : Z otimes Y ⟶ Y') (wf : (Z ◁ f) ≫ q = p ≫ f')
    (wg : (Z ◁ g) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫
          colimMap (parallelPairHom (Z ◁ f) (Z ◁ g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh

end

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/--
theorem `π_tensor_id_preserves_coequalizer_inv_desc` / 定理 `π_tensor_id_preserves_coequalizer_inv_desc`

English:
theorem π_tensor_id_preserves_coequalizer_inv_desc
  statement: {W X Y Z : C} (f g : X ⟶ Y) (h : Y otimes Z ⟶ W)
  proof: map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh

中文:
定理 π_tensor_id_preserves_coequalizer_inv_desc
  结论: {W X Y Z : C} (f g : X ⟶ Y) (h : Y otimes Z ⟶ W)
  证明: map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh

Depends on / 依赖: tensorRight
-/
theorem π_tensor_id_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Y otimes Z ⟶ W)
    (wh : (f ▷ Z) ≫ h = (g ▷ Z) ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh

/--
theorem `π_tensor_id_preserves_coequalizer_inv_colimMap_desc` / 定理 `π_tensor_id_preserves_coequalizer_inv_colimMap_desc`

English:
theorem π_tensor_id_preserves_coequalizer_inv_colimMap_desc
  statement: {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
  proof: map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

中文:
定理 π_tensor_id_preserves_coequalizer_inv_colimMap_desc
  结论: {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
  证明: map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

Depends on / 依赖: tensorRight
-/
theorem π_tensor_id_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : X otimes Z ⟶ X') (q : Y otimes Z ⟶ Y') (wf : (f ▷ Z) ≫ q = p ≫ f')
    (wg : (g ▷ Z) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫
          colimMap (parallelPairHom (f ▷ Z) (g ▷ Z) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

end

end

/--
Definition of `Bimod` / `Bimod` 的定义

English:
structure Bimod
  parameters: (A B : Mon C)
  axioms and operations (8):
    - X : C
    - actLeft : A.X otimes X ⟶ X
    - one_actLeft : η ▷ X ≫ actLeft = (fun_ X).hom  [default: by cat_disch]
    - left_assoc : μ ▷ X ≫ actLeft = (α_ A.X A.X X).hom ≫ A.X ◁ actLeft ≫ actLeft  [default: by cat_disch]
    - actRight : X otimes B.X ⟶ X
    - actRight_one : X ◁ η ≫ actRight = (ρ_ X).hom  [default: by cat_disch]
    - right_assoc : X ◁ μ ≫ actRight = (α_ X B.X B.X).inv ≫ actRight ▷ B.X ≫ actRight  [default: by cat_disch]
    - middle_assoc : actLeft ▷ B.X ≫ actRight = (α_ A.X X B.X).hom ≫ A.X ◁ actRight ≫ actLeft  [default: by cat_disch]

中文:
结构 双模
  参数: (A B : 幺半群 C)
  公理与运算 (8 个):
    - X : C
    - actLeft : A.X otimes X ⟶ X
    - one_actLeft : η ▷ X ≫ actLeft = (fun_ X).hom  [默认: by cat_disch]
    - left_assoc : μ ▷ X ≫ actLeft = (α_ A.X A.X X).hom ≫ A.X ◁ actLeft ≫ actLeft  [默认: by cat_disch]
    - actRight : X otimes B.X ⟶ X
    - actRight_one : X ◁ η ≫ actRight = (ρ_ X).hom  [默认: by cat_disch]
    - right_assoc : X ◁ μ ≫ actRight = (α_ X B.X B.X).inv ≫ actRight ▷ B.X ≫ actRight  [默认: by cat_disch]
    - middle_assoc : actLeft ▷ B.X ≫ actRight = (α_ A.X X B.X).hom ≫ A.X ◁ actRight ≫ actLeft  [默认: by cat_disch]

Depends on / 依赖: actLeft, cat_disch, left_assoc
-/
structure Bimod (A B : Mon C) where
  /-- The underlying monoidal category -/
  X : C
  /-- The left action of this bimodule object -/
  actLeft : A.X otimes X ⟶ X
  one_actLeft : η ▷ X ≫ actLeft = (fun_ X).hom := by cat_disch
  left_assoc :
    μ ▷ X ≫ actLeft = (α_ A.X A.X X).hom ≫ A.X ◁ actLeft ≫ actLeft := by cat_disch
  /-- The right action of this bimodule object -/
  actRight : X otimes B.X ⟶ X
  actRight_one : X ◁ η ≫ actRight = (ρ_ X).hom := by cat_disch
  right_assoc :
    X ◁ μ ≫ actRight = (α_ X B.X B.X).inv ≫ actRight ▷ B.X ≫ actRight := by
    cat_disch
  middle_assoc :
    actLeft ▷ B.X ≫ actRight = (α_ A.X X B.X).hom ≫ A.X ◁ actRight ≫ actLeft := by
    cat_disch

attribute [reassoc (attr := simp)] Bimod.one_actLeft Bimod.actRight_one Bimod.left_assoc
  Bimod.right_assoc Bimod.middle_assoc

namespace Bimod

variable {A B : Mon C} (M : Bimod A B)

/-- A morphism of bimodule objects. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : Bimod A B)
  axioms and operations (3):
    - hom : M.X ⟶ N.X
    - left_act_hom : M.actLeft ≫ hom = (A.X ◁ hom) ≫ N.actLeft  [default: by cat_disch]
    - right_act_hom : M.actRight ≫ hom = (hom ▷ B.X) ≫ N.actRight  [default: by cat_disch]

中文:
结构 态射
  参数: (M N : 双模 A B)
  公理与运算 (3 个):
    - hom : M.X ⟶ N.X
    - left_act_hom : M.actLeft ≫ hom = (A.X ◁ hom) ≫ N.actLeft  [默认: by cat_disch]
    - right_act_hom : M.actRight ≫ hom = (hom ▷ B.X) ≫ N.actRight  [默认: by cat_disch]

Depends on / 依赖: M.actRight, N.actRight, actRight, cat_disch, right_act_hom
-/
structure Hom (M N : Bimod A B) where
  /-- The morphism between `M`'s monoidal category and `N`'s monoidal category -/
  hom : M.X ⟶ N.X
  left_act_hom : M.actLeft ≫ hom = (A.X ◁ hom) ≫ N.actLeft := by cat_disch
  right_act_hom : M.actRight ≫ hom = (hom ▷ B.X) ≫ N.actRight := by cat_disch

attribute [reassoc (attr := simp)] Hom.left_act_hom Hom.right_act_hom

/-- The identity morphism on a bimodule object. -/
@[simps]
/--
Definition of `id'` / `id'` 的定义

English:
definition id'
  signature: (M : Bimod A B)
  body: 𝟙 M.X

中文:
定义 id'
  签名: (M : 双模 A B)
  定义体: 𝟙 M.X
-/
def id' (M : Bimod A B) : Hom M M where hom := 𝟙 M.X

/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: (M : Bimod A B)
  body: ⟨id' M⟩

中文:
实例 homInhabited
  签名: (M : 双模 A B)
  定义体: ⟨id' M⟩
-/
instance homInhabited (M : Bimod A B) : Inhabited (Hom M M) :=
  ⟨id' M⟩

/-- Composition of bimodule object morphisms. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N O : Bimod A B} (f : Hom M N) (g : Hom N O)
  body: f.hom ≫ g.hom

中文:
定义 comp
  签名: {M N O : 双模 A B} (f : 态射 M N) (g : 态射 N O)
  定义体: f.hom ≫ g.hom

Depends on / 依赖: f.hom, g.hom
-/
def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Bimod A B)
  body: Hom M N
  id := id'
  comp f g := comp f g

@[ext]

中文:
实例 :
  签名: 范畴 (双模 A B)
  定义体: Hom M N
  id := id'
  comp f g := comp f g

@[ext]
-/
instance : Category (Bimod A B) where
  Hom M N := Hom M N
  id := id'
  comp f g := comp f g

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : Bimod A B} (f g : M ⟶ N) (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 hom_ext
  条件: {M N : 双模 A B} (f g : M ⟶ N) (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : Bimod A B} (f g : M ⟶ N) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
/--
theorem `id_hom'` / 定理 `id_hom'`

English:
theorem id_hom'
  given: (M : Bimod A B)
  statement: (𝟙 M : Hom M M).hom = 𝟙 M.X
  proof: rfl

@[simp]

中文:
定理 id_hom'
  条件: (M : 双模 A B)
  结论: (𝟙 M : 态射 M M).hom = 𝟙 M.X
  证明: rfl

@[simp]
-/
theorem id_hom' (M : Bimod A B) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
/--
theorem `comp_hom'` / 定理 `comp_hom'`

English:
theorem comp_hom'
  given: {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 comp_hom'
  条件: {M N K : 双模 A B} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem comp_hom' {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

/-- Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
/--
Definition of `isoOfIso` / `isoOfIso` 的定义

English:
definition isoOfIso
  signature: {X Y : Mon C} {P Q : Bimod X Y} (f : P.X ≅ Q.X)
  body: { hom := f.hom }
  inv :=
    { hom := f.inv
      left_act_hom := by
        rw [← cancel_mono f.hom]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]; rw [f_left_act_hom]; rw [← Category.assoc]; rw [← whiskerLeft_comp]; rw [Iso.inv_hom_id]; rw [whiskerLeft_id];

中文:
定义 isoOfIso
  签名: {X Y : 幺半群 C} {P Q : 双模 X Y} (f : P.X ≅ Q.X)
  定义体: { hom := f.hom }
  inv :=
    { hom := f.inv
      left_act_hom := by
        rw [← cancel_mono f.hom]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]; rw [f_left_act_hom]; rw [← Category.assoc]; rw [← whiskerLeft_comp]; rw [Iso.inv_hom_id]; rw [whiskerLeft_id];

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Iso.inv_hom_id, cancel_mono, comp_id, comp_whiskerRi, f.hom, f.inv, f_left_act_hom, f_right_act_hom, id_comp, inv_hom_id, left_act_hom, right_act_hom, whiskerLeft_comp, whiskerLeft_id
-/
def isoOfIso {X Y : Mon C} {P Q : Bimod X Y} (f : P.X ≅ Q.X)
    (f_left_act_hom : P.actLeft ≫ f.hom = (X.X ◁ f.hom) ≫ Q.actLeft)
    (f_right_act_hom : P.actRight ≫ f.hom = (f.hom ▷ Y.X) ≫ Q.actRight) : P ≅ Q where
  hom :=
    { hom := f.hom }
  inv :=
    { hom := f.inv
      left_act_hom := by
        rw [← cancel_mono f.hom]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]; rw [f_left_act_hom]; rw [← Category.assoc]; rw [← whiskerLeft_comp]; rw [Iso.inv_hom_id]; rw [whiskerLeft_id]; rw [Category.id_comp]
      right_act_hom := by
        rw [← cancel_mono f.hom]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id]; rw [f_right_act_hom]; rw [← Category.assoc]; rw [← comp_whiskerRight]; rw [Iso.inv_hom_id]; rw [id_whiskerRight]; rw [Category.id_comp] }
  hom_inv_id := by ext; dsimp; rw [Iso.hom_inv_id]
  inv_hom_id := by ext; dsimp; rw [Iso.inv_hom_id]

variable (A)

/-- A monoid object as a bimodule over itself. -/
@[simps]
/--
Definition of `regular` / `regular` 的定义

English:
definition regular
  signature: : Bimod A A where
  body: A.X
  actLeft := μ
  actRight := μ

中文:
定义 regular
  签名: : 双模 A A where
  定义体: A.X
  actLeft := μ
  actRight := μ
-/
def regular : Bimod A A where
  X := A.X
  actLeft := μ
  actRight := μ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Bimod A A)
  body: ⟨regular A⟩

中文:
实例 :
  签名: 可居 (双模 A A)
  定义体: ⟨regular A⟩

Depends on / 依赖: regular
-/
instance : Inhabited (Bimod A A) :=
  ⟨regular A⟩

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Bimod A B ⥤ C where
  body: A.X
  map f := f.hom

中文:
定义 forget
  签名: : 双模 A B ⥤ C where
  定义体: A.X
  map f := f.hom
-/
def forget : Bimod A B ⥤ C where
  obj A := A.X
  map f := f.hom

open CategoryTheory.Limits

variable [HasCoequalizers C]

namespace TensorBimod

variable {R S T : Mon C} (P : Bimod R S) (Q : Bimod S T)

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : C
  body: coequalizer (P.actRight ▷ Q.X) ((α_ _ _ _).hom ≫ (P.X ◁ Q.actLeft))

中文:
定义 X
  签名: : C
  定义体: coequalizer (P.actRight ▷ Q.X) ((α_ _ _ _).hom ≫ (P.X ◁ Q.actLeft))

Depends on / 依赖: P.actRight, Q.actLeft, actLeft, actRight, coequalizer
-/
noncomputable def X : C :=
  coequalizer (P.actRight ▷ Q.X) ((α_ _ _ _).hom ≫ (P.X ◁ Q.actLeft))

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `actLeft` / `actLeft` 的定义

English:
definition actLeft
  signature: : R.X otimes X P Q ⟶ X P Q
  body: (PreservesCoequalizer.iso (tensorLeft R.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).inv ≫ ((α_ _ _ _).inv ▷ _) ≫ (P.actLeft ▷ S.X ▷ Q.X))
        ((α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X))
        (by
          dsimp
          simp only [Category.assoc]
          slice_lh

中文:
定义 actLeft
  签名: : R.X otimes X P Q ⟶ X P Q
  定义体: (PreservesCoequalizer.iso (tensorLeft R.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).inv ≫ ((α_ _ _ _).inv ▷ _) ≫ (P.actLeft ▷ S.X ▷ Q.X))
        ((α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X))
        (by
          dsimp
          simp only [Category.assoc]
          slice_lh

Depends on / 依赖: Category, Category.assoc, P.actLeft, PreservesCoequalizer, PreservesCoequalizer.iso, actLeft, associator_inv_naturality_middle, associator_inv_naturality_right, colimMap, comp_whiskerRight, middle_assoc, parallelPairHom, slice_lhs, slice_rhs, tensorLeft, whiskerLeft_comp, whisker_exch
-/
noncomputable def actLeft : R.X otimes X P Q ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorLeft R.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).inv ≫ ((α_ _ _ _).inv ▷ _) ≫ (P.actLeft ▷ S.X ▷ Q.X))
        ((α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X))
        (by
          dsimp
          simp only [Category.assoc]
          slice_lhs 1 2 => rw [associator_inv_naturality_middle]
          slice_rhs 3 4 => rw [← comp_whiskerRight, middle_assoc, comp_whiskerRight]
          simp)
        (by
          dsimp
          slice_lhs 1 1 => rw [whiskerLeft_comp]
          slice_lhs 2 3 => rw [associator_inv_naturality_right]
          slice_lhs 3 4 => rw [whisker_exchange]
          simp))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `whiskerLeft_π_actLeft` / 定理 `whiskerLeft_π_actLeft`

English:
theorem whiskerLeft_π_actLeft
  proof: by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  simp only [Category.assoc]

中文:
定理 whiskerLeft_π_actLeft
  证明: by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  simp only [Category.assoc]

Depends on / 依赖: Category, Category.assoc, tensorLeft
-/
theorem whiskerLeft_π_actLeft :
    (R.X ◁ coequalizer.π _ _) ≫ actLeft P Q =
      (α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  simp only [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `one_act_left'` / 定理 `one_act_left'`

English:
theorem one_act_left'
  statement: (η ▷ _) ≫ actLeft P Q = (fun_ _).hom
  proof: by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, one_actLeft]
  slice_rhs 1 2 =>

中文:
定理 one_act_left'
  结论: (η ▷ _) ≫ actLeft P Q = (fun_ _).hom
  证明: by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, one_actLeft]
  slice_rhs 1 2 =>

Depends on / 依赖: associator_inv_naturality_left, cancel_epi, coequalizer, comp_whiskerRight, leftUnitor_naturality, monoidal, one_actLeft, slice_lhs, slice_rhs, tensorLeft, whisker_exchange
-/
theorem one_act_left' : (η ▷ _) ≫ actLeft P Q = (fun_ _).hom := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, one_actLeft]
  slice_rhs 1 2 => rw [leftUnitor_naturality]
  monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_assoc'` / 定理 `left_assoc'`

English:
theorem left_assoc'
  proof: by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, left_assoc, comp_whiskerRight, 

中文:
定理 left_assoc'
  证明: by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, left_assoc, comp_whiskerRight, 

Depends on / 依赖: associator_inv_naturality_left, associator_naturality_right, cancel_epi, coequalizer, comp_whiskerRight, left_assoc, slice_lhs, slice_rhs, tensorLeft, whisker, whiskerLeft_comp, whisker_exchange
-/
theorem left_assoc' :
    (μ ▷ _) ≫ actLeft P Q = (α_ R.X R.X _).hom ≫ (R.X ◁ actLeft P Q) ≫ actLeft P Q := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, left_assoc, comp_whiskerRight, comp_whiskerRight]
  slice_rhs 1 2 => rw [associator_naturality_right]
  slice_rhs 2 3 =>
    rw [← whiskerLeft_comp]; rw [whiskerLeft_π_actLeft]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_middle]
  monoidal

end

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `actRight` / `actRight` 的定义

English:
definition actRight
  signature: : X P Q otimes T.X ⟶ X P Q
  body: (PreservesCoequalizer.iso (tensorRight T.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (P.X ◁ S.X ◁ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (P.X ◁ Q.actRight))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator

中文:
定义 actRight
  签名: : X P Q otimes T.X ⟶ X P Q
  定义体: (PreservesCoequalizer.iso (tensorRight T.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (P.X ◁ S.X ◁ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (P.X ◁ Q.actRight))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, PreservesCoequalizer, PreservesCoequalizer.iso, Q.actRight, actRight, associator_naturality_left, colimMap, comp_whiskerRight, inv_hom_id_assoc, middle_assoc, parallelPairHom, slice_lhs, tensorRight, whiskerLeft_comp, whisker_assoc, whisker_exchange
-/
noncomputable def actRight : X P Q otimes T.X ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorRight T.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (P.X ◁ S.X ◁ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (P.X ◁ Q.actRight))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator_naturality_left]
          slice_lhs 2 3 => rw [← whisker_exchange]
          simp)
        (by
          dsimp
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]
          slice_lhs 3 4 =>
            rw [← whiskerLeft_comp]; rw [middle_assoc]; rw [whiskerLeft_comp]
          simp))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `π_tensor_id_actRight` / 定理 `π_tensor_id_actRight`

English:
theorem π_tensor_id_actRight
  proof: by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  simp only [Category.assoc]

中文:
定理 π_tensor_id_actRight
  证明: by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  simp only [Category.assoc]

Depends on / 依赖: Category, Category.assoc, tensorRight
-/
theorem π_tensor_id_actRight :
    (coequalizer.π _ _ ▷ T.X) ≫ actRight P Q =
      (α_ _ _ _).hom ≫ (P.X ◁ Q.actRight) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  simp only [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `actRight_one'` / 定理 `actRight_one'`

English:
theorem actRight_one'
  statement: (_ ◁ η) ≫ actRight P Q = (ρ_ _).hom
  proof: by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, actRight_one]
  simp

中文:
定理 actRight_one'
  结论: (_ ◁ η) ≫ actRight P Q = (ρ_ _).hom
  证明: by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, actRight_one]
  simp

Depends on / 依赖: actRight_one, associator_naturality_right, cancel_epi, coequalizer, slice_lhs, tensorRight, whiskerLeft_comp, whisker_exchange
-/
theorem actRight_one' : (_ ◁ η) ≫ actRight P Q = (ρ_ _).hom := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, actRight_one]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_assoc'` / 定理 `right_assoc'`

English:
theorem right_assoc'
  proof: by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, right_assoc,
    whiskerLeft_comp

中文:
定理 right_assoc'
  证明: by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, right_assoc,
    whiskerLeft_comp

Depends on / 依赖: associator_inv_naturality_left, associator_naturality_right, cancel_epi, coequalizer, comp_whiskerRight, right_assoc, slice_lhs, slice_rhs, tensorRight, whiskerLeft_comp, whisker_exchange
-/
theorem right_assoc' :
    (_ ◁ μ) ≫ actRight P Q =
      (α_ _ T.X T.X).inv ≫ (actRight P Q ▷ T.X) ≫ actRight P Q := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, right_assoc,
    whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_inv_naturality_left]
  slice_rhs 2 3 => rw [← comp_whiskerRight, π_tensor_id_actRight, comp_whiskerRight,
    comp_whiskerRight]
  slice_rhs 4 5 => rw [π_tensor_id_actRight]
  simp

end

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `middle_assoc'` / 定理 `middle_assoc'`

English:
theorem middle_assoc'
  proof: by
  refine (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← comp_whiskerRight, whiskerLeft_π_actLeft, comp_whiskerRight,
    comp_whiskerRight]
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  slice_lhs 2 3 => rw [associator_naturality_le

中文:
定理 middle_assoc'
  证明: by
  refine (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← comp_whiskerRight, whiskerLeft_π_actLeft, comp_whiskerRight,
    comp_whiskerRight]
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  slice_lhs 2 3 => rw [associator_naturality_le

Depends on / 依赖: associator_naturality_left, associator_naturality_middle, cancel_epi, coequalizer, comp_whiskerRight, slice_lhs, slice_rhs, tensorLeft, tensorRight, whiskerLeft_comp
-/
theorem middle_assoc' :
    (actLeft P Q ▷ T.X) ≫ actRight P Q =
      (α_ R.X _ T.X).hom ≫ (R.X ◁ actRight P Q) ≫ actLeft P Q := by
  refine (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← comp_whiskerRight, whiskerLeft_π_actLeft, comp_whiskerRight,
    comp_whiskerRight]
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  slice_lhs 2 3 => rw [associator_naturality_left]
  slice_rhs 1 2 => rw [associator_naturality_middle]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, π_tensor_id_actRight,
    whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_right]
  slice_rhs 4 5 => rw [whisker_exchange]
  simp

end

end TensorBimod

section

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Tensor product of two bimodule objects as a bimodule object. -/
@[simps]
/--
Definition of `tensorBimod` / `tensorBimod` 的定义

English:
definition tensorBimod
  signature: {X Y Z : Mon C} (M : Bimod X Y) (N : Bimod Y Z)
  body: TensorBimod.X M N
  actLeft := TensorBimod.actLeft M N
  actRight := TensorBimod.actRight M N
  one_actLeft := TensorBimod.one_act_left' M N
  actRight_one := TensorBimod.actRight_one' M N
  left_assoc := TensorBimod.left_assoc' M N
  right_assoc := TensorBimod.right_assoc' M N
  middle_assoc := Ten

中文:
定义 tensorBimod
  签名: {X Y Z : 幺半群 C} (M : 双模 X Y) (N : 双模 Y Z)
  定义体: TensorBimod.X M N
  actLeft := TensorBimod.actLeft M N
  actRight := TensorBimod.actRight M N
  one_actLeft := TensorBimod.one_act_left' M N
  actRight_one := TensorBimod.actRight_one' M N
  left_assoc := TensorBimod.left_assoc' M N
  right_assoc := TensorBimod.right_assoc' M N
  middle_assoc := Ten

Depends on / 依赖: TensorBimod, TensorBimod.X
-/
noncomputable def tensorBimod {X Y Z : Mon C} (M : Bimod X Y) (N : Bimod Y Z) : Bimod X Z where
  X := TensorBimod.X M N
  actLeft := TensorBimod.actLeft M N
  actRight := TensorBimod.actRight M N
  one_actLeft := TensorBimod.one_act_left' M N
  actRight_one := TensorBimod.actRight_one' M N
  left_assoc := TensorBimod.left_assoc' M N
  right_assoc := TensorBimod.right_assoc' M N
  middle_assoc := TensorBimod.middle_assoc' M N

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering for morphisms of bimodule objects. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: {X Y Z : Mon C} (M : Bimod X Y) {N₁ N₂ : Bimod Y Z} (f : N₁ ⟶ N₂)
  body: colimMap
      (parallelPairHom _ _ _ _ (_ ◁ f.hom) (_ ◁ f.hom)
        (by rw [whisker_exchange])
        (by
          simp only [Category.assoc, tensor_whiskerLeft, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_hom_left]
          slice_lhs 1 2 => rw [← whiskerLeft_comp, Hom.left_act_hom]
    

中文:
定义 whiskerLeft
  签名: {X Y Z : 幺半群 C} (M : 双模 X Y) {N₁ N₂ : 双模 Y Z} (f : N₁ ⟶ N₂)
  定义体: colimMap
      (parallelPairHom _ _ _ _ (_ ◁ f.hom) (_ ◁ f.hom)
        (by rw [whisker_exchange])
        (by
          simp only [Category.assoc, tensor_whiskerLeft, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_hom_left]
          slice_lhs 1 2 => rw [← whiskerLeft_comp, Hom.left_act_hom]
    

Depends on / 依赖: Category, Category.assoc, Hom.left_act_hom, Iso.cancel_iso_hom_left, Iso.inv_hom_id_assoc, TensorBimod, TensorBimod.whiskerLeft_, cancel_epi, cancel_iso_hom_left, coequalizer, colimMap, f.hom, inv_hom_id_assoc, left_act_hom, parallelPairHom, parallelPairHom_app_one, slice_lhs, slice_rhs, tensorLeft, tensor_whiskerLeft
-/
noncomputable def whiskerLeft {X Y Z : Mon C} (M : Bimod X Y) {N₁ N₂ : Bimod Y Z} (f : N₁ ⟶ N₂) :
    M.tensorBimod N₁ ⟶ M.tensorBimod N₂ where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ (_ ◁ f.hom) (_ ◁ f.hom)
        (by rw [whisker_exchange])
        (by
          simp only [Category.assoc, tensor_whiskerLeft, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_hom_left]
          slice_lhs 1 2 => rw [← whiskerLeft_comp, Hom.left_act_hom]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_rhs 1 2 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one,
      whiskerLeft_comp]
    slice_rhs 2 3 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_right]
    slice_rhs 2 3 => rw [whisker_exchange]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← whiskerLeft_comp, Hom.right_act_hom]
    slice_rhs 1 2 =>
      rw [← comp_whiskerRight]; rw [ι_colimMap]; rw [parallelPairHom_app_one]; rw [comp_whiskerRight]
    slice_rhs 2 3 => rw [TensorBimod.π_tensor_id_actRight]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering for morphisms of bimodule objects. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {X Y Z : Mon C} {M₁ M₂ : Bimod X Y} (f : M₁ ⟶ M₂) (N : Bimod Y Z)
  body: colimMap
      (parallelPairHom _ _ _ _ (f.hom ▷ _ ▷ _) (f.hom ▷ _)
        (by rw [← comp_whiskerRight, Hom.right_act_hom, comp_whiskerRight])
        (by
          slice_lhs 2 3 => rw [whisker_exchange]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π

中文:
定义 whiskerRight
  签名: {X Y Z : 幺半群 C} {M₁ M₂ : 双模 X Y} (f : M₁ ⟶ M₂) (N : 双模 Y Z)
  定义体: colimMap
      (parallelPairHom _ _ _ _ (f.hom ▷ _ ▷ _) (f.hom ▷ _)
        (by rw [← comp_whiskerRight, Hom.right_act_hom, comp_whiskerRight])
        (by
          slice_lhs 2 3 => rw [whisker_exchange]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π

Depends on / 依赖: Hom.left_act_hom, Hom.right_act_hom, TensorBimod, TensorBimod.whiskerLeft_, cancel_epi, coequalizer, colimMap, comp_whiskerRight, f.hom, left_act_hom, parallelPairHom, parallelPairHom_app_one, right_act_hom, slice_lhs, slice_rhs, tensorLeft, whiskerLeft_comp, whisker_exchange
-/
noncomputable def whiskerRight {X Y Z : Mon C} {M₁ M₂ : Bimod X Y} (f : M₁ ⟶ M₂) (N : Bimod Y Z) :
    M₁.tensorBimod N ⟶ M₂.tensorBimod N where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ (f.hom ▷ _ ▷ _) (f.hom ▷ _)
        (by rw [← comp_whiskerRight, Hom.right_act_hom, comp_whiskerRight])
        (by
          slice_lhs 2 3 => rw [whisker_exchange]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← comp_whiskerRight, Hom.left_act_hom]
    slice_rhs 1 2 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one, whiskerLeft_comp]
    slice_rhs 2 3 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_middle]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [whisker_exchange]
    slice_rhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one,
      comp_whiskerRight]
    slice_rhs 2 3 => rw [TensorBimod.π_tensor_id_actRight]
    simp

end

namespace AssociatorBimod

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable {R S T U : Mon C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homAux` / `homAux` 的定义

English:
definition homAux
  signature: : (P.tensorBimod Q).X otimes L.X ⟶ (P.tensorBimod (Q.tensorBimod L)).X
  body: (PreservesCoequalizer.iso (tensorRight L.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).hom ≫ (P.X ◁ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_naturality_left]
        slice_lhs 2 3 => rw [← whisker_exchange]
      

中文:
定义 homAux
  签名: : (P.tensorBimod Q).X otimes L.X ⟶ (P.tensorBimod (Q.tensorBimod L)).X
  定义体: (PreservesCoequalizer.iso (tensorRight L.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).hom ≫ (P.X ◁ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_naturality_left]
        slice_lhs 2 3 => rw [← whisker_exchange]
      

Depends on / 依赖: PreservesCoequalizer, PreservesCoequalizer.iso, TensorBimod, TensorBimod.X, TensorBimod.whiskerLeft_, associator_naturality_left, associator_naturality_right, coequalizer, coequalizer.condition, coequalizer.desc, condition, slice_lhs, tensorRight, whiskerLeft_comp, whisker_exchange
-/
noncomputable def homAux : (P.tensorBimod Q).X otimes L.X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  (PreservesCoequalizer.iso (tensorRight L.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).hom ≫ (P.X ◁ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_naturality_left]
        slice_lhs 2 3 => rw [← whisker_exchange]
        slice_lhs 3 4 => rw [coequalizer.condition]
        slice_lhs 2 3 => rw [associator_naturality_right]
        slice_lhs 3 4 =>
          rw [← whiskerLeft_comp]; rw [TensorBimod.whiskerLeft_π_actLeft]; rw [whiskerLeft_comp]
        simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: :
  body: coequalizer.desc (homAux P Q L)
    (by
      dsimp [homAux]
      refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [← comp_whiskerRight, TensorBimod.π_tensor_id_actRight,
        comp_whiskerRight, comp_whiskerR

中文:
定义 hom
  签名: :
  定义体: coequalizer.desc (homAux P Q L)
    (by
      dsimp [homAux]
      refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [← comp_whiskerRight, TensorBimod.π_tensor_id_actRight,
        comp_whiskerRight, comp_whiskerR

Depends on / 依赖: TensorBimod, TensorBimod.X, associator_naturality_middle, cancel_epi, coequalizer, coequalizer.condition, coequalizer.desc, comp_whiskerRight, condition, homAux, slice_lhs, tensorRight, whiskerLeft_comp
-/
noncomputable def hom :
    ((P.tensorBimod Q).tensorBimod L).X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  coequalizer.desc (homAux P Q L)
    (by
      dsimp [homAux]
      refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [← comp_whiskerRight, TensorBimod.π_tensor_id_actRight,
        comp_whiskerRight, comp_whiskerRight]
      slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      slice_lhs 2 3 => rw [associator_naturality_middle]
      slice_lhs 3 4 =>
        rw [← whiskerLeft_comp]; rw [coequalizer.condition]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
      slice_rhs 1 2 => rw [associator_naturality_left]
      slice_rhs 2 3 => rw [← whisker_exchange]
      slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_left_act_hom'` / 定理 `hom_left_act_hom'`

English:
theorem hom_left_act_hom'
  proof: by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc, 

中文:
定理 hom_left_act_hom'
  证明: by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc, 

Depends on / 依赖: TensorBimod, TensorBimod.X, TensorBimod.whiskerLeft_, associator_inv_naturality_middle, cancel_epi, coequalizer, comp_, curriedTensor_obj_map, homAux, slice_lhs, slice_rhs, tensorLeft, tensorRight, whiskerLeft_comp
-/
theorem hom_left_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actLeft ≫ hom P Q L =
      (R.X ◁ hom P Q L) ≫ (P.tensorBimod (Q.tensorBimod L)).actLeft := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc, whiskerLeft_comp]
  refine (cancel_epi ((tensorRight _ ⋙ tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [TensorBimod.X]
  slice_lhs 1 2 => rw [associator_inv_naturality_middle]
  slice_lhs 2 3 =>
    rw [← comp_whiskerRight]; rw [TensorBimod.whiskerLeft_π_actLeft]; rw [comp_whiskerRight]; rw [comp_whiskerRight]
  slice_lhs 4 6 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [associator_naturality_left]
  slice_rhs 1 3 =>
    rw [← whiskerLeft_comp]; rw [← whiskerLeft_comp]; rw [π_tensor_id_preserves_coequalizer_inv_desc]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_rhs 3 4 => erw [TensorBimod.whiskerLeft_π_actLeft P (Q.tensorBimod L)]
  slice_rhs 2 3 => erw [associator_inv_naturality_right]
  slice_rhs 3 4 => erw [whisker_exchange]
  monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_right_act_hom'` / 定理 `hom_right_act_hom'`

English:
theorem hom_right_act_hom'
  proof: by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRigh

中文:
定理 hom_right_act_hom'
  证明: by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRigh

Depends on / 依赖: Functor, Functor.flip_obj_map, TensorBimod, TensorBimod.X, associator_naturality_left, cancel_epi, coequalizer, comp_whiskerRight, curriedTensor_map_app, flip_obj_map, homAux, slice_lhs, slice_rhs, tensorRight
-/
theorem hom_right_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actRight ≫ hom P Q L =
      (hom P Q L ▷ U.X) ≫ (P.tensorBimod (Q.tensorBimod L)).actRight := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc, comp_whiskerRight]
  refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [TensorBimod.X]
  slice_lhs 1 2 => rw [associator_naturality_left]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_rhs 1 3 =>
    rw [← comp_whiskerRight]; rw [← comp_whiskerRight]; rw [π_tensor_id_preserves_coequalizer_inv_desc]; rw [comp_whiskerRight]; rw [comp_whiskerRight]
  slice_rhs 3 4 => erw [TensorBimod.π_tensor_id_actRight P (Q.tensorBimod L)]
  slice_rhs 2 3 => erw [associator_naturality_middle]
  dsimp
  slice_rhs 3 4 =>
    rw [← whiskerLeft_comp]; rw [TensorBimod.π_tensor_id_actRight]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `invAux` / `invAux` 的定义

English:
definition invAux
  signature: : P.X otimes (Q.tensorBimod L).X ⟶ ((P.tensorBimod Q).tensorBimod L).X
  body: (PreservesCoequalizer.iso (tensorLeft P.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ▷ L.X) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_inv_naturality_middle]
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (P.X

中文:
定义 invAux
  签名: : P.X otimes (Q.tensorBimod L).X ⟶ ((P.tensorBimod Q).tensorBimod L).X
  定义体: (PreservesCoequalizer.iso (tensorLeft P.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ▷ L.X) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_inv_naturality_middle]
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (P.X

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, PreservesCoequalizer, PreservesCoequalizer.iso, Q.actRight, TensorBimod, TensorBimod.X, actRight, associator_inv_naturality_middle, coequalizer, coequalizer.condition, coequalizer.desc, comp_whiskerRight, condition, inv_hom_id_assoc, slice_lhs, tensorLeft, trivial_covering, trivial_covering.mp
-/
noncomputable def invAux : P.X otimes (Q.tensorBimod L).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  (PreservesCoequalizer.iso (tensorLeft P.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ▷ L.X) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_inv_naturality_middle]
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (P.X ◁ Q.actRight)]; rw [comp_whiskerRight]
        slice_lhs 3 4 =>
          rw [← comp_whiskerRight]; rw [Category.assoc]; rw [← TensorBimod.π_tensor_id_actRight]; rw [comp_whiskerRight]
        slice_lhs 4 5 => rw [coequalizer.condition]
        slice_lhs 3 4 => rw [associator_naturality_left]
        slice_rhs 1 2 => rw [whiskerLeft_comp]
        slice_rhs 2 3 => rw [associator_inv_naturality_right]
        slice_rhs 3 4 => rw [whisker_exchange]
        simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: :
  body: coequalizer.desc (invAux P Q L)
    (by
      dsimp [invAux]
      refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [whisker_exchange]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => 

中文:
定义 inv
  签名: :
  定义体: coequalizer.desc (invAux P Q L)
    (by
      dsimp [invAux]
      refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [whisker_exchange]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => 

Depends on / 依赖: TensorBimod, TensorBimod.X, associator_inv_naturality_left, associator_naturality_right, cancel_epi, coequalizer, coequalizer.condition, coequalizer.desc, comp_whiskerRight, condition, invAux, slice_lhs, slice_rhs, tensorLeft, whiskerLeft_c, whisker_exchange
-/
noncomputable def inv :
    (P.tensorBimod (Q.tensorBimod L)).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  coequalizer.desc (invAux P Q L)
    (by
      dsimp [invAux]
      refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [whisker_exchange]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => rw [associator_inv_naturality_left]
      slice_lhs 2 3 =>
        rw [← comp_whiskerRight]; rw [coequalizer.condition]; rw [comp_whiskerRight]; rw [comp_whiskerRight]
      slice_rhs 1 2 => rw [associator_naturality_right]
      slice_rhs 2 3 =>
        rw [← whiskerLeft_comp]; rw [TensorBimod.whiskerLeft_π_actLeft]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
      slice_rhs 4 6 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_rhs 3 4 => rw [associator_inv_naturality_middle]
      monoidal)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_inv_id` / 定理 `hom_inv_id`

English:
theorem hom_inv_id
  statement: hom P Q L ≫ inv P Q L = 𝟙 _
  proof: by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_des

中文:
定理 hom_inv_id
  结论: hom P Q L ≫ inv P Q L = 𝟙 _
  证明: by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_des

Depends on / 依赖: Category, Category.com, Functor, Functor.flip_obj_map, Iso.hom_inv_id_assoc, TensorBimod, TensorBimod.X, cancel_epi, coequalizer, coequalizer.hom_ext, curriedTensor_map_app, flip_obj_map, homAux, hom_ext, hom_inv_id_assoc, invAux, slice_lhs, slice_rhs, tensorRight
-/
theorem hom_inv_id : hom P Q L ≫ inv P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.hom_inv_id_assoc]
  dsimp only [TensorBimod.X]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_hom_id` / 定理 `inv_hom_id`

English:
theorem inv_hom_id
  statement: inv P Q L ≫ hom P Q L = 𝟙 _
  proof: by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => r

中文:
定理 inv_hom_id
  结论: inv P Q L ≫ hom P Q L = 𝟙 _
  证明: by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => r

Depends on / 依赖: Category, Category.comp_id, Iso.inv_hom_id_assoc, TensorBimod, TensorBimod.X, cancel_epi, coequalizer, coequalizer.hom_ext, comp_id, curriedTensor_obj_map, homAux, hom_ext, invAux, inv_hom_id_assoc, slice_lhs, slice_rhs, tensorLeft
-/
theorem inv_hom_id : inv P Q L ≫ hom P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.inv_hom_id_assoc]
  dsimp only [TensorBimod.X]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

end AssociatorBimod

namespace LeftUnitorBimod

variable {R S : Mon C} (P : Bimod R S)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : TensorBimod.X (regular R) P ⟶ P.X
  body: coequalizer.desc P.actLeft (by dsimp; rw [Category.assoc, left_assoc])

中文:
定义 hom
  签名: : TensorBimod.X (regular R) P ⟶ P.X
  定义体: coequalizer.desc P.actLeft (by dsimp; rw [Category.assoc, left_assoc])

Depends on / 依赖: Category, Category.assoc, P.actLeft, actLeft, coequalizer, coequalizer.desc, left_assoc
-/
noncomputable def hom : TensorBimod.X (regular R) P ⟶ P.X :=
  coequalizer.desc P.actLeft (by dsimp; rw [Category.assoc, left_assoc])

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : P.X ⟶ TensorBimod.X (regular R) P
  body: (fun_ P.X).inv ≫ (η[R.X] ▷ _) ≫ coequalizer.π _ _

中文:
定义 inv
  签名: : P.X ⟶ TensorBimod.X (regular R) P
  定义体: (fun_ P.X).inv ≫ (η[R.X] ▷ _) ≫ coequalizer.π _ _

Depends on / 依赖: coequalizer, fun_
-/
noncomputable def inv : P.X ⟶ TensorBimod.X (regular R) P :=
  (fun_ P.X).inv ≫ (η[R.X] ▷ _) ≫ coequalizer.π _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `hom_inv_id` / 定理 `hom_inv_id`

English:
theorem hom_inv_id
  statement: hom P ≫ inv P = 𝟙 _
  proof: by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R.X R.X P.X) (R.X ◁ P.actLeft)]
  slice_lhs 4 6 => rw [← Cate

中文:
定理 hom_inv_id
  结论: hom P ≫ inv P = 𝟙 _
  证明: by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R.X R.X P.X) (R.X ◁ P.actLeft)]
  slice_lhs 4 6 => rw [← Cate

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.inv_hom_id_assoc, MonObj, MonObj.one_mul, P.actLeft, TensorBimod, TensorBimod.X, actLeft, associator_inv_naturality_left, coequalizer, coequalizer.condition, comp_id, comp_whiskerRight, condition, inv_hom_id_assoc, leftUnitor_inv_naturality, monoidal, one_mul
-/
theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R.X R.X P.X) (R.X ◁ P.actLeft)]
  slice_lhs 4 6 => rw [← Category.assoc, ← coequalizer.condition]
  slice_lhs 2 3 => rw [associator_inv_naturality_left]
  slice_lhs 3 4 => rw [← comp_whiskerRight, MonObj.one_mul]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_hom_id` / 定理 `inv_hom_id`

English:
theorem inv_hom_id
  statement: inv P ≫ hom P = 𝟙 _
  proof: by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_actLeft]; rw [Iso.inv_hom_id]

中文:
定理 inv_hom_id
  结论: inv P ≫ hom P = 𝟙 _
  证明: by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_actLeft]; rw [Iso.inv_hom_id]

Depends on / 依赖: Iso.inv_hom_id, coequalizer, inv_hom_id, one_actLeft, slice_lhs
-/
theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_actLeft]; rw [Iso.inv_hom_id]

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_left_act_hom'` / 定理 `hom_left_act_hom'`

English:
theorem hom_left_act_hom'
  proof: by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [left_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_de

中文:
定理 hom_left_act_hom'
  证明: by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [left_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_de

Depends on / 依赖: Iso.inv_hom_id_assoc, TensorBimod, TensorBimod.actLeft, actLeft, cancel_epi, coequalizer, inv_hom_id_assoc, left_assoc, regular, slice_lhs, slice_rhs, tensorLeft, whiskerLeft_comp
-/
theorem hom_left_act_hom' :
    ((regular R).tensorBimod P).actLeft ≫ hom P = (R.X ◁ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [left_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_right_act_hom'` / 定理 `hom_right_act_hom'`

English:
theorem hom_right_act_hom'
  proof: by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middl

中文:
定理 hom_right_act_hom'
  证明: by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middl

Depends on / 依赖: Category, Category.assoc, TensorBimod, TensorBimod.actRight, actRight, cancel_epi, coequalizer, comp_whiskerRight, middle_assoc, regular, slice_lhs, slice_rhs, tensorRight
-/
theorem hom_right_act_hom' :
    ((regular R).tensorBimod P).actRight ≫ hom P = (hom P ▷ S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middle_assoc]
  simp only [Category.assoc]

end LeftUnitorBimod

namespace RightUnitorBimod

variable {R S : Mon C} (P : Bimod R S)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : TensorBimod.X P (regular S) ⟶ P.X
  body: coequalizer.desc P.actRight (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])

中文:
定义 hom
  签名: : TensorBimod.X P (regular S) ⟶ P.X
  定义体: coequalizer.desc P.actRight (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id_assoc, P.actRight, actRight, coequalizer, coequalizer.desc, hom_inv_id_assoc, right_assoc
-/
noncomputable def hom : TensorBimod.X P (regular S) ⟶ P.X :=
  coequalizer.desc P.actRight (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : P.X ⟶ TensorBimod.X P (regular S)
  body: (ρ_ P.X).inv ≫ (_ ◁ η[S.X]) ≫ coequalizer.π _ _

中文:
定义 inv
  签名: : P.X ⟶ TensorBimod.X P (regular S)
  定义体: (ρ_ P.X).inv ≫ (_ ◁ η[S.X]) ≫ coequalizer.π _ _

Depends on / 依赖: coequalizer
-/
noncomputable def inv : P.X ⟶ TensorBimod.X P (regular S) :=
  (ρ_ P.X).inv ≫ (_ ◁ η[S.X]) ≫ coequalizer.π _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `hom_inv_id` / 定理 `hom_inv_id`

English:
theorem hom_inv_id
  statement: hom P ≫ inv P = 𝟙 _
  proof: by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lh

中文:
定理 hom_inv_id
  结论: hom P ≫ inv P = 𝟙 _
  证明: by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lh

Depends on / 依赖: Category, Category.comp_id, MonObj, MonObj.mul_one, TensorBimod, TensorBimod.X, associator_naturality_right, coequalizer, coequalizer.condition, comp_id, condition, monoidal, mul_one, rightUnitor_inv_naturality, slice_lhs, slice_rhs, whiskerLeft_comp, whisker_exchange
-/
theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lhs 3 4 => rw [← whiskerLeft_comp, MonObj.mul_one]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_hom_id` / 定理 `inv_hom_id`

English:
theorem inv_hom_id
  statement: inv P ≫ hom P = 𝟙 _
  proof: by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [actRight_one]; rw [Iso.inv_hom_id]

中文:
定理 inv_hom_id
  结论: inv P ≫ hom P = 𝟙 _
  证明: by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [actRight_one]; rw [Iso.inv_hom_id]

Depends on / 依赖: Iso.inv_hom_id, actRight_one, coequalizer, inv_hom_id, slice_lhs
-/
theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [actRight_one]; rw [Iso.inv_hom_id]

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_left_act_hom'` / 定理 `hom_left_act_hom'`

English:
theorem hom_left_act_hom'
  proof: by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_

中文:
定理 hom_left_act_hom'
  证明: by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_

Depends on / 依赖: Iso.inv_hom_id_assoc, TensorBimod, TensorBimod.actLeft, actLeft, cancel_epi, coequalizer, inv_hom_id_assoc, middle_assoc, regular, slice_lhs, slice_rhs, tensorLeft, whiskerLeft_comp
-/
theorem hom_left_act_hom' :
    (P.tensorBimod (regular S)).actLeft ≫ hom P = (R.X ◁ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_right_act_hom'` / 定理 `hom_right_act_hom'`

English:
theorem hom_right_act_hom'
  proof: by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.

中文:
定理 hom_right_act_hom'
  证明: by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.

Depends on / 依赖: Iso.hom_inv_id_assoc, TensorBimod, TensorBimod.actRight, actRight, cancel_epi, coequalizer, comp_whiskerRight, hom_inv_id_assoc, regular, right_assoc, slice_lhs, slice_rhs, tensorRight
-/
theorem hom_right_act_hom' :
    (P.tensorBimod (regular S)).actRight ≫ hom P = (hom P ▷ S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  rw [Iso.hom_inv_id_assoc]

end RightUnitorBimod

variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [forall X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/--
Definition of `associatorBimod` / `associatorBimod` 的定义

English:
definition associatorBimod
  signature: {W X Y Z : Mon C} (L : Bimod W X) (M : Bimod X Y)
  body: isoOfIso
    { hom := AssociatorBimod.hom L M N
      inv := AssociatorBimod.inv L M N
      hom_inv_id := AssociatorBimod.hom_inv_id L M N
      inv_hom_id := AssociatorBimod.inv_hom_id L M N } (AssociatorBimod.hom_left_act_hom' L M N)
    (AssociatorBimod.hom_right_act_hom' L M N)

中文:
定义 associatorBimod
  签名: {W X Y Z : 幺半群 C} (L : 双模 W X) (M : 双模 X Y)
  定义体: isoOfIso
    { hom := AssociatorBimod.hom L M N
      inv := AssociatorBimod.inv L M N
      hom_inv_id := AssociatorBimod.hom_inv_id L M N
      inv_hom_id := AssociatorBimod.inv_hom_id L M N } (AssociatorBimod.hom_left_act_hom' L M N)
    (AssociatorBimod.hom_right_act_hom' L M N)

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.hom_inv_id, AssociatorBimod.hom_left_act_hom, AssociatorBimod.hom_right_act_hom, AssociatorBimod.inv, AssociatorBimod.inv_hom_id, hom_inv_id, hom_left_act_hom, hom_right_act_hom, inv_hom_id, isoOfIso
-/
noncomputable def associatorBimod {W X Y Z : Mon C} (L : Bimod W X) (M : Bimod X Y)
    (N : Bimod Y Z) : (L.tensorBimod M).tensorBimod N ≅ L.tensorBimod (M.tensorBimod N) :=
  isoOfIso
    { hom := AssociatorBimod.hom L M N
      inv := AssociatorBimod.inv L M N
      hom_inv_id := AssociatorBimod.hom_inv_id L M N
      inv_hom_id := AssociatorBimod.inv_hom_id L M N } (AssociatorBimod.hom_left_act_hom' L M N)
    (AssociatorBimod.hom_right_act_hom' L M N)

/--
Definition of `leftUnitorBimod` / `leftUnitorBimod` 的定义

English:
definition leftUnitorBimod
  signature: {X Y : Mon C} (M : Bimod X Y)
  body: isoOfIso
    { hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id := LeftUnitorBimod.hom_inv_id M
      inv_hom_id := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)

中文:
定义 leftUnitorBimod
  签名: {X Y : 幺半群 C} (M : 双模 X Y)
  定义体: isoOfIso
    { hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id := LeftUnitorBimod.hom_inv_id M
      inv_hom_id := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)

Depends on / 依赖: LeftUnitorBimod, LeftUnitorBimod.hom, LeftUnitorBimod.hom_inv_id, LeftUnitorBimod.hom_left_act_hom, LeftUnitorBimod.hom_right_act_hom, LeftUnitorBimod.inv, LeftUnitorBimod.inv_hom_id, hom_inv_id, hom_left_act_hom, hom_right_act_hom, inv_hom_id, isoOfIso
-/
noncomputable def leftUnitorBimod {X Y : Mon C} (M : Bimod X Y) : (regular X).tensorBimod M ≅ M :=
  isoOfIso
    { hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id := LeftUnitorBimod.hom_inv_id M
      inv_hom_id := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)

/--
Definition of `rightUnitorBimod` / `rightUnitorBimod` 的定义

English:
definition rightUnitorBimod
  signature: {X Y : Mon C} (M : Bimod X Y)
  body: isoOfIso
    { hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id := RightUnitorBimod.hom_inv_id M
      inv_hom_id := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)

中文:
定义 rightUnitorBimod
  签名: {X Y : 幺半群 C} (M : 双模 X Y)
  定义体: isoOfIso
    { hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id := RightUnitorBimod.hom_inv_id M
      inv_hom_id := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)

Depends on / 依赖: RightUnitorBimod, RightUnitorBimod.hom, RightUnitorBimod.hom_inv_id, RightUnitorBimod.hom_left_act_hom, RightUnitorBimod.hom_right_act_hom, RightUnitorBimod.inv, RightUnitorBimod.inv_hom_id, hom_inv_id, hom_left_act_hom, hom_right_act_hom, inv_hom_id, isoOfIso
-/
noncomputable def rightUnitorBimod {X Y : Mon C} (M : Bimod X Y) : M.tensorBimod (regular Y) ≅ M :=
  isoOfIso
    { hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id := RightUnitorBimod.hom_inv_id M
      inv_hom_id := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `whiskerLeft_id_bimod` / 定理 `whiskerLeft_id_bimod`

English:
theorem whiskerLeft_id_bimod
  given: {X Y Z : Mon C} {M : Bimod X Y} {N : Bimod Y Z}
  proof: by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

中文:
定理 whiskerLeft_id_bimod
  条件: {X Y Z : 幺半群 C} {M : 双模 X Y} {N : 双模 Y Z}
  证明: by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

Depends on / 依赖: Limits, Limits.coequalizer.hom_ext, TensorBimod, TensorBimod.X, coequalizer, hom_ext
-/
theorem whiskerLeft_id_bimod {X Y Z : Mon C} {M : Bimod X Y} {N : Bimod Y Z} :
    whiskerLeft M (𝟙 N) = 𝟙 (M.tensorBimod N) := by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_whiskerRight_bimod` / 定理 `id_whiskerRight_bimod`

English:
theorem id_whiskerRight_bimod
  given: {X Y Z : Mon C} {M : Bimod X Y} {N : Bimod Y Z}
  proof: by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

中文:
定理 id_whiskerRight_bimod
  条件: {X Y Z : 幺半群 C} {M : 双模 X Y} {N : 双模 Y Z}
  证明: by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

Depends on / 依赖: Limits, Limits.coequalizer.hom_ext, TensorBimod, TensorBimod.X, coequalizer, full_constantSheaf, hom_ext
-/
theorem id_whiskerRight_bimod {X Y Z : Mon C} {M : Bimod X Y} {N : Bimod Y Z} :
    whiskerRight (𝟙 M) N = 𝟙 (M.tensorBimod N) := by
  ext
  apply Limits.coequalizer.hom_ext
  simp [TensorBimod.X]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `whiskerLeft_comp_bimod` / 定理 `whiskerLeft_comp_bimod`

English:
theorem whiskerLeft_comp_bimod
  statement: {X Y Z : Mon C} (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P)
  proof: by
  ext
  apply Limits.coequalizer.hom_ext
  simp

中文:
定理 whiskerLeft_comp_bimod
  结论: {X Y Z : 幺半群 C} (M : 双模 X Y) {N P Q : 双模 Y Z} (f : N ⟶ P)
  证明: by
  ext
  apply Limits.coequalizer.hom_ext
  simp

Depends on / 依赖: Limits, Limits.coequalizer.hom_ext, coequalizer, faithful_constantSheaf, hom_ext
-/
theorem whiskerLeft_comp_bimod {X Y Z : Mon C} (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P)
    (g : P ⟶ Q) : whiskerLeft M (f ≫ g) = whiskerLeft M f ≫ whiskerLeft M g := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_whiskerLeft_bimod` / 定理 `id_whiskerLeft_bimod`

English:
theorem id_whiskerLeft_bimod
  given: {X Y : Mon C} {M N : Bimod X Y} (f : M ⟶ N)
  proof: by
  dsimp [tensorHom, regular, leftUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [LeftUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  sli

中文:
定理 id_whiskerLeft_bimod
  条件: {X Y : 幺半群 C} {M N : 双模 X Y} (f : M ⟶ N)
  证明: by
  dsimp [tensorHom, regular, leftUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [LeftUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  sli

Depends on / 依赖: Category, Category.assoc, Hom.left_act_hom, Iso.inv_hom_id_assoc, LeftUnitorBimod, LeftUnitorBimod.hom, LeftUnitorBimod.inv, N.actLeft, actLeft, coequalizer, coequalizer.con, coequalizer.hom_ext, hom_ext, inv_hom_id_assoc, leftUnitorBimod, leftUnitor_inv_naturality, left_act_hom, parallelPairHom_app_one, regular, slice_lhs
-/
theorem id_whiskerLeft_bimod {X Y : Mon C} {M N : Bimod X Y} (f : M ⟶ N) :
    whiskerLeft (regular X) f = (leftUnitorBimod M).hom ≫ f ≫ (leftUnitorBimod N).inv := by
  dsimp [tensorHom, regular, leftUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [LeftUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  slice_rhs 2 3 => rw [leftUnitor_inv_naturality]
  slice_rhs 3 4 => rw [whisker_exchange]
  slice_rhs 4 4 => rw [← Iso.inv_hom_id_assoc (α_ X.X X.X N.X) (X.X ◁ N.actLeft)]
  slice_rhs 5 7 => rw [← Category.assoc, ← coequalizer.condition]
  slice_rhs 3 4 => rw [associator_inv_naturality_left]
  slice_rhs 4 5 => rw [← comp_whiskerRight, MonObj.one_mul]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  ```
  have : (λ_ (X.X ⊗ N.X)).inv ≫ (α_ (𝟙_ C) X.X N.X).inv ≫ ((λ_ X.X).hom ▷ N.X) = 𝟙 _ := by
    monoidal
  grind
  ```
  -/
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_whiskerLeft_bimod` / 定理 `comp_whiskerLeft_bimod`

English:
theorem comp_whiskerLeft_bimod
  statement: {W X Y Z : Mon C} (M : Bimod W X) (N : Bimod X Y)
  proof: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux, AssociatorBimod.inv]
  r

中文:
定理 comp_whiskerLeft_bimod
  结论: {W X Y Z : 幺半群 C} (M : 双模 W X) (N : 双模 X Y)
  证明: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux, AssociatorBimod.inv]
  r

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.homAux, AssociatorBimod.inv, Functor, Functor.flip_obj_map, TensorBimod, TensorBimod.X, associatorBimod, cancel_epi, coequalizer, coequalizer.hom_ext, curriedTensor_map_app, flip_obj_map, homAux, hom_ext, parallelPairHom_app_one, slice_lhs, slice_rhs, tensorBimod
-/
theorem comp_whiskerLeft_bimod {W X Y Z : Mon C} (M : Bimod W X) (N : Bimod X Y)
    {P P' : Bimod Y Z} (f : P ⟶ P') :
    whiskerLeft (M.tensorBimod N) f =
      (associatorBimod M N P).hom ≫
        whiskerLeft M (whiskerLeft N f) ≫ (associatorBimod M N P').inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux, AssociatorBimod.inv]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux]
  slice_rhs 2 2 => rw [whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality_right]
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← whisker_exchange]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_whiskerRight_bimod` / 定理 `comp_whiskerRight_bimod`

English:
theorem comp_whiskerRight_bimod
  statement: {X Y Z : Mon C} {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P)
  proof: by
  ext
  apply Limits.coequalizer.hom_ext
  simp

中文:
定理 comp_whiskerRight_bimod
  结论: {X Y Z : 幺半群 C} {M N P : 双模 X Y} (f : M ⟶ N) (g : N ⟶ P)
  证明: by
  ext
  apply Limits.coequalizer.hom_ext
  simp

Depends on / 依赖: Limits, Limits.coequalizer.hom_ext, coequalizer, hom_ext
-/
theorem comp_whiskerRight_bimod {X Y Z : Mon C} {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P)
    (Q : Bimod Y Z) : whiskerRight (f ≫ g) Q = whiskerRight f Q ≫ whiskerRight g Q := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `whiskerRight_id_bimod` / 定理 `whiskerRight_id_bimod`

English:
theorem whiskerRight_id_bimod
  given: {X Y : Mon C} {M N : Bimod X Y} (f : M ⟶ N)
  proof: by
  dsimp [tensorHom, regular, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [RightUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.right_act_hom]
 

中文:
定理 whiskerRight_id_bimod
  条件: {X Y : 幺半群 C} {M N : 双模 X Y} (f : M ⟶ N)
  证明: by
  dsimp [tensorHom, regular, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [RightUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.right_act_hom]
 

Depends on / 依赖: Hom.right_act_hom, RightUnitorBimod, RightUnitorBimod.hom, RightUnitorBimod.inv, associator_naturality_right, coequalizer, coequalizer.condition, coequalizer.hom_ext, condition, hom_ext, parallelPairHom_app_one, regular, rightUnitorBimod, rightUnitor_inv_naturality, right_act_hom, slice_lhs, slice_rhs, tensorHom, whiskerLeft_, whisker_exchange
-/
theorem whiskerRight_id_bimod {X Y : Mon C} {M N : Bimod X Y} (f : M ⟶ N) :
    whiskerRight f (regular Y) = (rightUnitorBimod M).hom ≫ f ≫ (rightUnitorBimod N).inv := by
  dsimp [tensorHom, regular, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [RightUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.right_act_hom]
  slice_rhs 2 3 => rw [rightUnitor_inv_naturality]
  slice_rhs 3 4 => rw [← whisker_exchange]
  slice_rhs 4 5 => rw [coequalizer.condition]
  slice_rhs 3 4 => rw [associator_naturality_right]
  slice_rhs 4 5 => rw [← whiskerLeft_comp, MonObj.mul_one]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `whiskerRight_comp_bimod` / 定理 `whiskerRight_comp_bimod`

English:
theorem whiskerRight_comp_bimod
  statement: {W X Y Z : Mon C} {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y)
  proof: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux, AssociatorBimod.hom]
  r

中文:
定理 whiskerRight_comp_bimod
  结论: {W X Y Z : 幺半群 C} {M M' : 双模 W X} (f : M ⟶ M') (N : 双模 X Y)
  证明: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux, AssociatorBimod.hom]
  r

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.inv, AssociatorBimod.invAux, TensorBimod, TensorBimod.X, associatorBimod, cancel_epi, coequalizer, coequalizer.hom_ext, curriedTensor_obj_map, hom_ext, invAux, parallelPairHom_app_o, parallelPairHom_app_one, slice_lhs, slice_rhs, tensorBimod, tensorHom, tensorLeft
-/
theorem whiskerRight_comp_bimod {W X Y Z : Mon C} {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y)
    (P : Bimod Y Z) :
    whiskerRight f (N.tensorBimod P) =
      (associatorBimod M N P).inv ≫
        whiskerRight (whiskerRight f N) P ≫ (associatorBimod M' N P).hom := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux, AssociatorBimod.hom]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_rhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 2 2 => rw [comp_whiskerRight]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_left]
  slice_rhs 1 3 => rw [Iso.inv_hom_id_assoc]
  slice_lhs 1 2 => rw [whisker_exchange]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `whisker_assoc_bimod` / 定理 `whisker_assoc_bimod`

English:
theorem whisker_assoc_bimod
  statement: {W X Y Z : Mon C} (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N')
  proof: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).m

中文:
定理 whisker_assoc_bimod
  结论: {W X Y Z : 幺半群 C} (M : 双模 W X) {N N' : 双模 X Y} (f : N ⟶ N')
  证明: by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).m

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.homAux, Functor, Functor.flip_obj_map, associatorBimod, cancel_epi, coequalizer, coequalizer.hom_ext, comp_whiskerRight, curriedTensor_map_app, flip_obj_map, homAux, hom_ext, parallelPairHom_app_one, slice_lhs, slice_rhs, tensorBimod, tensorHom, tensorRight
-/
theorem whisker_assoc_bimod {W X Y Z : Mon C} (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N')
    (P : Bimod Y Z) :
    whiskerRight (whiskerLeft M f) P =
      (associatorBimod M N P).hom ≫
        whiskerLeft M (whiskerRight f P) ≫ (associatorBimod M N' P).inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.inv]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux]
  slice_rhs 2 2 => rw [whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `whisker_exchange_bimod` / 定理 `whisker_exchange_bimod`

English:
theorem whisker_exchange_bimod
  statement: {X Y Z : Mon C} {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N)
  proof: by
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 1 2 => rw [whisker_exchange]
  simp

中文:
定理 whisker_exchange_bimod
  结论: {X Y Z : 幺半群 C} {M N : 双模 X Y} {P Q : 双模 Y Z} (f : M ⟶ N)
  证明: by
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 1 2 => rw [whisker_exchange]
  simp

Depends on / 依赖: coequalizer, coequalizer.hom_ext, hom_ext, parallelPairHom_app_one, slice_lhs, whisker_exchange
-/
theorem whisker_exchange_bimod {X Y Z : Mon C} {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N)
    (g : P ⟶ Q) : whiskerLeft M g ≫ whiskerRight f Q =
      whiskerRight f P ≫ whiskerLeft N g := by
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 1 2 => rw [whisker_exchange]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `pentagon_bimod` / 定理 `pentagon_bimod`

English:
theorem pentagon_bimod
  statement: {V W X Y Z : Mon C} (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y)
  proof: by
  dsimp [associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp only [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cance

中文:
定理 pentagon_bimod
  结论: {V W X Y Z : 幺半群 C} (M : 双模 V W) (N : 双模 W X) (P : 双模 X Y)
  证明: by
  dsimp [associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp only [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cance

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.homAux, associatorBimod, cancel_epi, coequalizer, coequalizer.hom_ext, comp_whiskerRight, homAux, hom_ext, parallelPairHom_app_one, slice_lhs, slice_rhs, tensorRight
-/
theorem pentagon_bimod {V W X Y Z : Mon C} (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y)
    (Q : Bimod Y Z) :
    whiskerRight (associatorBimod M N P).hom Q ≫
      (associatorBimod M (N.tensorBimod P) Q).hom ≫
        whiskerLeft M (associatorBimod N P Q).hom =
      (associatorBimod (M.tensorBimod N) P Q).hom ≫
        (associatorBimod M N (P.tensorBimod Q)).hom := by
  dsimp [associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp only [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight]; rw [π_tensor_id_preserves_coequalizer_inv_desc]; rw [comp_whiskerRight]; rw [comp_whiskerRight]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  dsimp only [TensorBimod.X]
  slice_lhs 2 3 => rw [associator_naturality_middle]
  slice_lhs 5 6 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 4 5 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  slice_lhs 3 4 =>
    rw [← whiskerLeft_comp]; rw [π_tensor_id_preserves_coequalizer_inv_desc]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_naturality_left]
  slice_rhs 2 3 => rw [← whisker_exchange]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_right]
  monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `triangle_bimod` / 定理 `triangle_bimod`

English:
theorem triangle_bimod
  given: {X Y Z : Mon C} (M : Bimod X Y) (N : Bimod Y Z)
  proof: by
  dsimp [associatorBimod, leftUnitorBimod, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.ho

中文:
定理 triangle_bimod
  条件: {X Y Z : 幺半群 C} (M : 双模 X Y) (N : 双模 Y Z)
  证明: by
  dsimp [associatorBimod, leftUnitorBimod, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.ho

Depends on / 依赖: AssociatorBimod, AssociatorBimod.hom, AssociatorBimod.homAux, RightUnitorBimod, RightUnitorBimod.hom, associatorBimod, cancel_epi, coequalizer, coequalizer.hom_ext, homAux, hom_ext, leftUnitorBimod, parallelPairHom_app_one, regular, rightUnitorBimod, slice_lhs, slice_rhs, tensorRight
-/
theorem triangle_bimod {X Y Z : Mon C} (M : Bimod X Y) (N : Bimod Y Z) :
    (associatorBimod M (regular Y) N).hom ≫ whiskerLeft M (leftUnitorBimod N).hom =
      whiskerRight (rightUnitorBimod M).hom N := by
  dsimp [associatorBimod, leftUnitorBimod, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [regular]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.condition]
  simp only [Category.assoc]

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
@[instance_reducible]
/--
Definition of `monBicategory` / `monBicategory` 的定义

English:
definition monBicategory
  signature: : Bicategory (Mon C) where
  body: Bimod X Y
  homCategory X Y := (inferInstance : Category (Bimod X Y))
  id X := regular X
  comp M N := tensorBimod M N
  whiskerLeft L _ _ f := whiskerLeft L f
  whiskerRight f N := whiskerRight f N
  associator := associatorBimod
  leftUnitor := leftUnitorBimod
  rightUnitor := rightUnitorBimod
  

中文:
定义 monBicategory
  签名: : 双范畴 (幺半群 C) where
  定义体: Bimod X Y
  homCategory X Y := (inferInstance : Category (Bimod X Y))
  id X := regular X
  comp M N := tensorBimod M N
  whiskerLeft L _ _ f := whiskerLeft L f
  whiskerRight f N := whiskerRight f N
  associator := associatorBimod
  leftUnitor := leftUnitorBimod
  rightUnitor := rightUnitorBimod
  
-/
noncomputable def monBicategory : Bicategory (Mon C) where
  Hom X Y := Bimod X Y
  homCategory X Y := (inferInstance : Category (Bimod X Y))
  id X := regular X
  comp M N := tensorBimod M N
  whiskerLeft L _ _ f := whiskerLeft L f
  whiskerRight f N := whiskerRight f N
  associator := associatorBimod
  leftUnitor := leftUnitorBimod
  rightUnitor := rightUnitorBimod
  whiskerLeft_id _ _ := whiskerLeft_id_bimod
  whiskerLeft_comp M _ _ _ f g := whiskerLeft_comp_bimod M f g
  id_whiskerLeft := id_whiskerLeft_bimod
  comp_whiskerLeft M N _ _ f := comp_whiskerLeft_bimod M N f
  id_whiskerRight _ _ := id_whiskerRight_bimod
  comp_whiskerRight f g Q := comp_whiskerRight_bimod f g Q
  whiskerRight_id := whiskerRight_id_bimod
  whiskerRight_comp := whiskerRight_comp_bimod
  whisker_assoc M _ _ f P := whisker_assoc_bimod M f P
  whisker_exchange := whisker_exchange_bimod
  pentagon := pentagon_bimod
  triangle := triangle_bimod

end Bimod
