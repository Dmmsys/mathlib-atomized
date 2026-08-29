/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.CatCommSq

/-! # Morphisms of categorical cospans.

Given `F : A ⥤ B`, `G : C ⥤ B`, `F' : A' ⥤ B'` and `G' : C' ⥤ B'`,
this file defines `CatCospanTransform F G F' G'`, the category of
"categorical transformations" from the (categorical) cospan `F G` to
the (categorical) cospan `F' G'`. Such a transformation consists of a
diagram

```
    F G
  A ⥤ B ⥢ C
H₁| |H₂ |H₃
  v v v
  A'⥤ B'⥢ C'
    F' G'
```

with specified `CatCommSq`s expressing 2-commutativity of the squares. These
transformations are used to encode 2-functoriality of categorical pullback squares.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃ v₁₄ v₁₅
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ u₁₄ u₁₅

/--
Definition of `CatCospanTransform` / `CatCospanTransform` 的定义

English:
structure CatCospanTransform
  axioms and operations (5):
    - left : A ⥤ A'
    - base : B ⥤ B'
    - right : C ⥤ C'
    - squareLeft : CatCommSq F left base F'  [default: by infer_instance]
    - squareRight : CatCommSq G right base G'  [default: by infer_instance]

中文:
结构 CatCospanTransform
  公理与运算 (5 个):
    - left : A ⥤ A'
    - base : B ⥤ B'
    - right : C ⥤ C'
    - squareLeft : CatCommSq F left base F'  [默认: by infer_instance]
    - squareRight : CatCommSq G right base G'  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure CatCospanTransform
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') where
  /-- the functor on the left component -/
  left : A ⥤ A'
  /-- the functor on the base component -/
  base : B ⥤ B'
  /-- the functor on the right component -/
  right : C ⥤ C'
  /-- a `CatCommSq` bundling the natural isomorphism `F ⋙ base ≅ left ⋙ F'`. -/
  squareLeft : CatCommSq F left base F' := by infer_instance
  /-- a `CatCommSq` bundling the natural isomorphism `G ⋙ base ≅ right ⋙ G'`. -/
  squareRight : CatCommSq G right base G' := by infer_instance

namespace CatCospanTransform

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)

attribute [local instance] CatCommSq.vId in
/-- The identity `CatCospanTransform` -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : CatCospanTransform F G F G where
  body: 𝟭 A
  base := 𝟭 B
  right := 𝟭 C

中文:
定义 id
  签名: : CatCospanTransform F G F G where
  定义体: 𝟭 A
  base := 𝟭 B
  right := 𝟭 C
-/
def id : CatCospanTransform F G F G where
  left := 𝟭 A
  base := 𝟭 B
  right := 𝟭 C

variable {F G}
/-- Composition of `CatCospanTransforms` is defined "componentwise". -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  body: ψ.left ⋙ ψ'.left
  base := ψ.base ⋙ ψ'.base
  right := ψ.right ⋙ ψ'.right
  squareLeft := ψ.squareLeft.vComp' ψ'.squareLeft
  squareRight := ψ.squareRight.vComp' ψ'.squareRight

中文:
定义 comp
  定义体: ψ.left ⋙ ψ'.left
  base := ψ.base ⋙ ψ'.base
  right := ψ.right ⋙ ψ'.right
  squareLeft := ψ.squareLeft.vComp' ψ'.squareLeft
  squareRight := ψ.squareRight.vComp' ψ'.squareRight
-/
def comp
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
    {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}
    (ψ : CatCospanTransform F G F' G') (ψ' : CatCospanTransform F' G' F'' G'') :
    CatCospanTransform F G F'' G'' where
  left := ψ.left ⋙ ψ'.left
  base := ψ.base ⋙ ψ'.base
  right := ψ.right ⋙ ψ'.right
  squareLeft := ψ.squareLeft.vComp' ψ'.squareLeft
  squareRight := ψ.squareRight.vComp' ψ'.squareRight

end

end CatCospanTransform

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {F : A ⥤ B} {G : C ⥤ B}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
    {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/--
Definition of `CatCospanTransformMorphism` / `CatCospanTransformMorphism` 的定义

English:
structure CatCospanTransformMorphism
  axioms and operations (5):
    - left : ψ.left ⟶ ψ'.left
    - right : ψ.right ⟶ ψ'.right
    - base : ψ.base ⟶ ψ'.base
    - left_coherence : ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left F' = Functor.whiskerLeft F base ≫ ψ'.squareLeft.iso.hom  [default: by cat_disch]
    - right_coherence : ψ.squareRight.iso.hom ≫ Functor.whiskerRight right G' = Functor.whiskerLeft G base ≫ ψ'.squareRight.iso.hom  [default: by cat_disch]

中文:
结构 CatCospanTransform态射
  公理与运算 (5 个):
    - left : ψ.left ⟶ ψ'.left
    - right : ψ.right ⟶ ψ'.right
    - base : ψ.base ⟶ ψ'.base
    - left_coherence : ψ.squareLeft.iso.hom ≫ 函子.whiskerRight left F' = 函子.whiskerLeft F base ≫ ψ'.squareLeft.iso.hom  [默认: by cat_disch]
    - right_coherence : ψ.squareRight.iso.hom ≫ 函子.whiskerRight right G' = 函子.whiskerLeft G base ≫ ψ'.squareRight.iso.hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CatCospanTransformMorphism
    (ψ ψ' : CatCospanTransform F G F' G') where
  /-- the natural transformations between the left components -/
  left : ψ.left ⟶ ψ'.left
  /-- the natural transformations between the right components -/
  right : ψ.right ⟶ ψ'.right
  /-- the natural transformations between the base components -/
  base : ψ.base ⟶ ψ'.base
  /-- the coherence condition for the left square -/
  left_coherence :
      ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left F' =
      Functor.whiskerLeft F base ≫ ψ'.squareLeft.iso.hom := by
    cat_disch
  /-- the coherence condition for the right square -/
  right_coherence :
      ψ.squareRight.iso.hom ≫ Functor.whiskerRight right G' =
      Functor.whiskerLeft G base ≫ ψ'.squareRight.iso.hom := by
    cat_disch

namespace CatCospanTransform

attribute [reassoc (attr := simp)]
  CatCospanTransformMorphism.left_coherence
  CatCospanTransformMorphism.right_coherence

@[simps]
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (CatCospanTransform F G F' G') where
  body: CatCospanTransformMorphism ψ ψ'
  id ψ :=
    { left := 𝟙 _
      right := 𝟙 _
      base := 𝟙 _ }
  comp α β :=
    { left := α.left ≫ β.left
      right := α.right ≫ β.right
      base := α.base ≫ β.base }

中文:
实例 category
  签名: : 范畴 (CatCospanTransform F G F' G') where
  定义体: CatCospanTransformMorphism ψ ψ'
  id ψ :=
    { left := 𝟙 _
      right := 𝟙 _
      base := 𝟙 _ }
  comp α β :=
    { left := α.left ≫ β.left
      right := α.right ≫ β.right
      base := α.base ≫ β.base }

Depends on / 依赖: CatCospanTransformMorphism
-/
instance category : Category (CatCospanTransform F G F' G') where
  Hom ψ ψ' := CatCospanTransformMorphism ψ ψ'
  id ψ :=
    { left := 𝟙 _
      right := 𝟙 _
      base := 𝟙 _ }
  comp α β :=
    { left := α.left ≫ β.left
      right := α.right ≫ β.right
      base := α.base ≫ β.base }

attribute [local ext] CatCospanTransformMorphism in
@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'}
  proof: by
  apply CatCospanTransformMorphism.ext <;> assumption

中文:
引理 hom_ext
  结论: {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'}
  证明: by
  apply CatCospanTransformMorphism.ext <;> assumption

Depends on / 依赖: CatCospanTransformMorphism, CatCospanTransformMorphism.ext
-/
lemma hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'}
    (hl : θ.left = θ'.left) (hr : θ.right = θ'.right) (hb : θ.base = θ'.base) :
    θ = θ' := by
  apply CatCospanTransformMorphism.ext <;> assumption

end CatCospanTransform

namespace CatCospanTransformMorphism

@[reassoc (attr := simp)]
/--
lemma `left_coherence_app` / 引理 `left_coherence_app`

English:
lemma left_coherence_app
  statement: {ψ ψ' : CatCospanTransform F G F' G'}
  proof: congr_app α.left_coherence x

@[reassoc (attr := simp)]

中文:
引理 left_coherence_app
  结论: {ψ ψ' : CatCospanTransform F G F' G'}
  证明: congr_app α.left_coherence x

@[reassoc (attr := simp)]

Depends on / 依赖: congr_app, left_coherence
-/
lemma left_coherence_app {ψ ψ' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (x : A) :
    ψ.squareLeft.iso.hom.app x ≫ F'.map (α.left.app x) =
    α.base.app (F.obj x) ≫ ψ'.squareLeft.iso.hom.app x :=
  congr_app α.left_coherence x

@[reassoc (attr := simp)]
/--
lemma `right_coherence_app` / 引理 `right_coherence_app`

English:
lemma right_coherence_app
  statement: {ψ ψ' : CatCospanTransform F G F' G'}
  proof: congr_app α.right_coherence x

中文:
引理 right_coherence_app
  结论: {ψ ψ' : CatCospanTransform F G F' G'}
  证明: congr_app α.right_coherence x

Depends on / 依赖: congr_app, right_coherence
-/
lemma right_coherence_app {ψ ψ' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (x : C) :
    ψ.squareRight.iso.hom.app x ≫ G'.map (α.right.app x) =
    α.base.app (G.obj x) ≫ ψ'.squareRight.iso.hom.app x :=
  congr_app α.right_coherence x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Whiskering left of a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (φ : CatCospanTransform F G F' G')
  body: Functor.whiskerLeft φ.left α.left
  right := Functor.whiskerLeft φ.right α.right
  base := Functor.whiskerLeft φ.base α.base

中文:
定义 whiskerLeft
  签名: (φ : CatCospanTransform F G F' G')
  定义体: Functor.whiskerLeft φ.left α.left
  right := Functor.whiskerLeft φ.right α.right
  base := Functor.whiskerLeft φ.base α.base

Depends on / 依赖: Functor, Functor.whiskerLeft, whiskerLeft
-/
def whiskerLeft (φ : CatCospanTransform F G F' G')
    {ψ ψ' : CatCospanTransform F' G' F'' G''} (α : ψ ⟶ ψ') :
    (φ.comp ψ) ⟶ (φ.comp ψ') where
  left := Functor.whiskerLeft φ.left α.left
  right := Functor.whiskerLeft φ.right α.right
  base := Functor.whiskerLeft φ.base α.base

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Whiskering right of a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
  body: Functor.whiskerRight α.left φ.left
  right := Functor.whiskerRight α.right φ.right
  base := Functor.whiskerRight α.base φ.base
  left_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← left_coherence_app]; rw [Functor.map_comp_assoc]
    simp
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← right_coherence_app]; rw [Functor.map_comp_assoc]
    simp

中文:
定义 whiskerRight
  签名: {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
  定义体: Functor.whiskerRight α.left φ.left
  right := Functor.whiskerRight α.right φ.right
  base := Functor.whiskerRight α.base φ.base
  left_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← left_coherence_app]; rw [Functor.map_comp_assoc]
    simp
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← right_coherence_app]; rw [Functor.map_comp_assoc]
    simp

Depends on / 依赖: Functor, Functor.whiskerRight, whiskerRight
-/
def whiskerRight {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    (ψ.comp φ) ⟶ (ψ'.comp φ) where
  left := Functor.whiskerRight α.left φ.left
  right := Functor.whiskerRight α.right φ.right
  base := Functor.whiskerRight α.base φ.base
  left_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← left_coherence_app]; rw [Functor.map_comp_assoc]
    simp
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc]; rw [← right_coherence_app]; rw [Functor.map_comp_assoc]
    simp

end CatCospanTransformMorphism

namespace CatCospanTransform

/-- A constructor for isomorphisms of `CatCospanTransform`'s. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {ψ ψ' : CatCospanTransform F G F' G'}
  body: { left := left.hom
      right := right.hom
      base := base.hom }
  inv :=
    { left := left.inv
      right := right.inv
      base := base.inv
      left_coherence := by
        simpa using ψ'.squareLeft.iso.hom ≫=
          IsIso.inv_eq_inv.mpr left_coherence =≫
          ψ.squareLeft.iso.hom
      right_coherence := by
        simpa using ψ'.squareRight.iso.hom ≫=
          IsIso.inv_eq_inv.mpr right_coherence =≫
          ψ.squareRight.iso.hom }

中文:
定义 mkIso
  签名: {ψ ψ' : CatCospanTransform F G F' G'}
  定义体: { left := left.hom
      right := right.hom
      base := base.hom }
  inv :=
    { left := left.inv
      right := right.inv
      base := base.inv
      left_coherence := by
        simpa using ψ'.squareLeft.iso.hom ≫=
          IsIso.inv_eq_inv.mpr left_coherence =≫
          ψ.squareLeft.iso.hom
      right_coherence := by
        simpa using ψ'.squareRight.iso.hom ≫=
          IsIso.inv_eq_inv.mpr right_coherence =≫
          ψ.squareRight.iso.hom }

Depends on / 依赖: Functor, Functor.whiskerLeft, Functor.whiskerRight, IsIso.inv_eq_in, IsIso.inv_eq_inv.mpr, base.hom, base.inv, cat_disch, inv_eq_in, inv_eq_inv, left.hom, left.inv, left_coherence, right.hom, right.inv, right_coherence, squareLeft, squareLeft.iso.hom, squareRight, squareRight.iso.hom
-/
def mkIso {ψ ψ' : CatCospanTransform F G F' G'}
    (left : ψ.left ≅ ψ'.left) (right : ψ.right ≅ ψ'.right)
    (base : ψ.base ≅ ψ'.base)
    (left_coherence :
        ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left.hom F' =
        Functor.whiskerLeft F base.hom ≫ ψ'.squareLeft.iso.hom := by
      cat_disch)
    (right_coherence :
        ψ.squareRight.iso.hom ≫ Functor.whiskerRight right.hom G' =
        Functor.whiskerLeft G base.hom ≫ ψ'.squareRight.iso.hom := by
      cat_disch) :
    ψ ≅ ψ' where
  hom :=
    { left := left.hom
      right := right.hom
      base := base.hom }
  inv :=
    { left := left.inv
      right := right.inv
      base := base.inv
      left_coherence := by
        simpa using ψ'.squareLeft.iso.hom ≫=
          IsIso.inv_eq_inv.mpr left_coherence =≫
          ψ.squareLeft.iso.hom
      right_coherence := by
        simpa using ψ'.squareRight.iso.hom ≫=
          IsIso.inv_eq_inv.mpr right_coherence =≫
          ψ.squareRight.iso.hom }

section Iso

variable {ψ ψ' : CatCospanTransform F G F' G'}
  (f : ψ' ⟶ ψ') [IsIso f] (e : ψ ≅ ψ')

/--
Instance `isIso_left` / 实例 `isIso_left`

English:
instance isIso_left
  signature: : IsIso f.left
  body: ⟨(inv f).left, by simp [← CatCospanTransform.category_comp_left]⟩

中文:
实例 isIso_left
  签名: : 是同构 f.left
  定义体: ⟨(inv f).left, by simp [← CatCospanTransform.category_comp_left]⟩

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_left, category_comp_left
-/
instance isIso_left : IsIso f.left :=
  ⟨(inv f).left, by simp [← CatCospanTransform.category_comp_left]⟩

/--
Instance `isIso_right` / 实例 `isIso_right`

English:
instance isIso_right
  signature: : IsIso f.right
  body: ⟨(inv f).right, by simp [← CatCospanTransform.category_comp_right]⟩

中文:
实例 isIso_right
  签名: : 是同构 f.right
  定义体: ⟨(inv f).right, by simp [← CatCospanTransform.category_comp_right]⟩

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_right, category_comp_right
-/
instance isIso_right : IsIso f.right :=
  ⟨(inv f).right, by simp [← CatCospanTransform.category_comp_right]⟩

/--
Instance `isIso_base` / 实例 `isIso_base`

English:
instance isIso_base
  signature: : IsIso f.base
  body: ⟨(inv f).base, by simp [← CatCospanTransform.category_comp_base]⟩

@[simp]

中文:
实例 isIso_base
  签名: : 是同构 f.base
  定义体: ⟨(inv f).base, by simp [← CatCospanTransform.category_comp_base]⟩

@[simp]

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_base, category_comp_base
-/
instance isIso_base : IsIso f.base :=
  ⟨(inv f).base, by simp [← CatCospanTransform.category_comp_base]⟩

@[simp]
/--
lemma `inv_left` / 引理 `inv_left`

English:
lemma inv_left
  statement: inv f.left = (inv f).left
  proof: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_left]

@[simp]

中文:
引理 inv_left
  结论: inv f.left = (inv f).left
  证明: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_left]

@[simp]

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_left, IsIso.eq_inv_of_inv_hom_id, category_comp_left, eq_inv_of_inv_hom_id
-/
lemma inv_left : inv f.left = (inv f).left := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_left]

@[simp]
/--
lemma `inv_right` / 引理 `inv_right`

English:
lemma inv_right
  statement: inv f.right = (inv f).right
  proof: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_right]

@[simp]

中文:
引理 inv_right
  结论: inv f.right = (inv f).right
  证明: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_right]

@[simp]

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_right, IsIso.eq_inv_of_inv_hom_id, category_comp_right, eq_inv_of_inv_hom_id
-/
lemma inv_right : inv f.right = (inv f).right := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_right]

@[simp]
/--
lemma `inv_base` / 引理 `inv_base`

English:
lemma inv_base
  statement: inv f.base = (inv f).base
  proof: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_base]

中文:
引理 inv_base
  结论: inv f.base = (inv f).base
  证明: by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_base]

Depends on / 依赖: CatCospanTransform, CatCospanTransform.category_comp_base, IsIso.eq_inv_of_inv_hom_id, category_comp_base, eq_inv_of_inv_hom_id
-/
lemma inv_base : inv f.base = (inv f).base := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_base]

/-- Extract an isomorphism between left components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/--
Definition of `leftIso` / `leftIso` 的定义

English:
definition leftIso
  signature: : ψ.left ≅ ψ'.left where
  body: e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← category_comp_left]
  inv_hom_id := by simp [← category_comp_left]

中文:
定义 leftIso
  签名: : ψ.left ≅ ψ'.left where
  定义体: e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← category_comp_left]
  inv_hom_id := by simp [← category_comp_left]

Depends on / 依赖: e.hom.left
-/
def leftIso : ψ.left ≅ ψ'.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← category_comp_left]
  inv_hom_id := by simp [← category_comp_left]

/-- Extract an isomorphism between right components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/--
Definition of `rightIso` / `rightIso` 的定义

English:
definition rightIso
  signature: : ψ.right ≅ ψ'.right where
  body: e.hom.right
  inv := e.inv.right
  hom_inv_id := by simp [← category_comp_right]
  inv_hom_id := by simp [← category_comp_right]

中文:
定义 rightIso
  签名: : ψ.right ≅ ψ'.right where
  定义体: e.hom.right
  inv := e.inv.right
  hom_inv_id := by simp [← category_comp_right]
  inv_hom_id := by simp [← category_comp_right]

Depends on / 依赖: e.hom.right
-/
def rightIso : ψ.right ≅ ψ'.right where
  hom := e.hom.right
  inv := e.inv.right
  hom_inv_id := by simp [← category_comp_right]
  inv_hom_id := by simp [← category_comp_right]

/-- Extract an isomorphism between base components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/--
Definition of `baseIso` / `baseIso` 的定义

English:
definition baseIso
  signature: : ψ.base ≅ ψ'.base where
  body: e.hom.base
  inv := e.inv.base
  hom_inv_id := by simp [← category_comp_base]
  inv_hom_id := by simp [← category_comp_base]

中文:
定义 baseIso
  签名: : ψ.base ≅ ψ'.base where
  定义体: e.hom.base
  inv := e.inv.base
  hom_inv_id := by simp [← category_comp_base]
  inv_hom_id := by simp [← category_comp_base]

Depends on / 依赖: e.hom.base
-/
def baseIso : ψ.base ≅ ψ'.base where
  hom := e.hom.base
  inv := e.inv.base
  hom_inv_id := by simp [← category_comp_base]
  inv_hom_id := by simp [← category_comp_base]

set_option backward.isDefEq.respectTransparency.types false in
omit [IsIso f] in
/--
lemma `isIso_iff` / 引理 `isIso_iff`

English:
lemma isIso_iff
  statement: IsIso f ↔ IsIso f.left ∧ IsIso f.base ∧ IsIso f.right where
  proof: ⟨inferInstance, inferInstance, inferInstance⟩
  mpr h := by
    obtain ⟨_, _, _⟩ := h
    use mkIso (asIso f.left) (asIso f.right) (asIso f.base)
.inv f.left_coherence f.right_coherence
    aesop_cat

中文:
引理 isIso_iff
  结论: 是同构 f ↔ 是同构 f.left ∧ 是同构 f.base ∧ 是同构 f.right where
  证明: ⟨inferInstance, inferInstance, inferInstance⟩
  mpr h := by
    obtain ⟨_, _, _⟩ := h
    use mkIso (asIso f.left) (asIso f.right) (asIso f.base)
.inv f.left_coherence f.right_coherence
    aesop_cat
-/
lemma isIso_iff : IsIso f ↔ IsIso f.left ∧ IsIso f.base ∧ IsIso f.right where
  mp h := ⟨inferInstance, inferInstance, inferInstance⟩
  mpr h := by
    obtain ⟨_, _, _⟩ := h
    use mkIso (asIso f.left) (asIso f.right) (asIso f.base)
.inv f.left_coherence f.right_coherence
    aesop_cat

end Iso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for categorical cospan transformations. -/
@[simps!]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (φ : CatCospanTransform F G F' G')
  body: mkIso φ.left.leftUnitor φ.right.leftUnitor φ.base.leftUnitor

中文:
定义 leftUnitor
  签名: (φ : CatCospanTransform F G F' G')
  定义体: mkIso φ.left.leftUnitor φ.right.leftUnitor φ.base.leftUnitor

Depends on / 依赖: base.leftUnitor, left.leftUnitor, leftUnitor, right.leftUnitor
-/
def leftUnitor (φ : CatCospanTransform F G F' G') :
    (CatCospanTransform.id F G).comp φ ≅ φ :=
  mkIso φ.left.leftUnitor φ.right.leftUnitor φ.base.leftUnitor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for categorical cospan transformations. -/
@[simps!]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (φ : CatCospanTransform F G F' G')
  body: mkIso φ.left.rightUnitor φ.right.rightUnitor φ.base.rightUnitor

中文:
定义 rightUnitor
  签名: (φ : CatCospanTransform F G F' G')
  定义体: mkIso φ.left.rightUnitor φ.right.rightUnitor φ.base.rightUnitor

Depends on / 依赖: base.rightUnitor, left.rightUnitor, right.rightUnitor, rightUnitor
-/
def rightUnitor (φ : CatCospanTransform F G F' G') :
    φ.comp (.id F' G') ≅ φ :=
  mkIso φ.left.rightUnitor φ.right.rightUnitor φ.base.rightUnitor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for categorical cospan transformations. -/
@[simps!]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
  body: mkIso
    (φ.left.associator φ'.left φ''.left)
    (φ.right.associator φ'.right φ''.right)
    (φ.base.associator φ'.base φ''.base)

中文:
定义 associator
  签名: {A''' : 类型u₁₀} {B''' : 类型u₁₁} {C''' : 类型u₁₂}
  定义体: mkIso
    (φ.left.associator φ'.left φ''.left)
    (φ.right.associator φ'.right φ''.right)
    (φ.base.associator φ'.base φ''.base)

Depends on / 依赖: associator, base.associator, left.associator, right.associator
-/
def associator {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (φ : CatCospanTransform F G F' G') (φ' : CatCospanTransform F' G' F'' G'')
    (φ'' : CatCospanTransform F'' G'' F''' G''') :
    (φ.comp φ').comp φ'' ≅ φ.comp (φ'.comp φ'') :=
  mkIso
    (φ.left.associator φ'.left φ''.left)
    (φ.right.associator φ'.right φ''.right)
    (φ.base.associator φ'.base φ''.base)

section lemmas

-- We scope the notations with notations from bicategories to make life easier.
-- Due to performance issues, these notations should not be in scope at the same time
-- as the ones in bicategories.

@[inherit_doc] scoped infixr:81 " ◁ " => CatCospanTransformMorphism.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => CatCospanTransformMorphism.whiskerRight
@[inherit_doc] scoped notation "α_" => CatCospanTransform.associator
@[inherit_doc] scoped notation "fun_" => CatCospanTransform.leftUnitor
@[inherit_doc] scoped notation "ρ_" => CatCospanTransform.rightUnitor

variable
    {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    {ψ ψ' ψ'' : CatCospanTransform F G F' G'}
    (η : ψ ⟶ ψ') (η' : ψ' ⟶ ψ'')
    {φ φ' φ'' : CatCospanTransform F' G' F'' G''}
    (θ : φ ⟶ φ') (θ' : φ' ⟶ φ'')
    {τ τ' : CatCospanTransform F'' G'' F''' G'''}
    (γ : τ ⟶ τ')

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `whisker_exchange` / 引理 `whisker_exchange`

English:
lemma whisker_exchange
  statement: ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ
  proof: by cat_disch

@[simp]

中文:
引理 whisker_exchange
  结论: ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma whisker_exchange : ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ := by cat_disch

@[simp]
/--
lemma `id_whiskerRight` / 引理 `id_whiskerRight`

English:
lemma id_whiskerRight
  statement: 𝟙 ψ ▷ φ = 𝟙 _
  proof: by cat_disch

中文:
引理 id_whiskerRight
  结论: 𝟙 ψ ▷ φ = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma id_whiskerRight : 𝟙 ψ ▷ φ = 𝟙 _ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `whiskerRight_id` / 引理 `whiskerRight_id`

English:
lemma whiskerRight_id
  statement: η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv
  proof: by cat_disch

@[simp, reassoc]

中文:
引理 whiskerRight_id
  结论: η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv
  证明: by cat_disch

@[simp, reassoc]

Depends on / 依赖: cat_disch
-/
lemma whiskerRight_id : η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv := by cat_disch

@[simp, reassoc]
/--
lemma `comp_whiskerRight` / 引理 `comp_whiskerRight`

English:
lemma comp_whiskerRight
  statement: (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ
  proof: by cat_disch

中文:
引理 comp_whiskerRight
  结论: (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ
  证明: by cat_disch

Depends on / 依赖: IsStableUnderComposition, MorphismProperty, W.IsStableUnderComposition, cat_disch
-/
lemma comp_whiskerRight : (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `whiskerRight_comp` / 引理 `whiskerRight_comp`

English:
lemma whiskerRight_comp
  proof: by
  cat_disch

@[simp]

中文:
引理 whiskerRight_comp
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma whiskerRight_comp :
    η ▷ (φ.comp τ) = (α_ _ _ _).inv ≫ (η ▷ φ) ▷ τ ≫ (α_ _ _ _).hom := by
  cat_disch

@[simp]
/--
lemma `whiskerleft_id` / 引理 `whiskerleft_id`

English:
lemma whiskerleft_id
  statement: ψ ◁ 𝟙 φ = 𝟙 _
  proof: by cat_disch

中文:
引理 whiskerleft_id
  结论: ψ ◁ 𝟙 φ = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma whiskerleft_id : ψ ◁ 𝟙 φ = 𝟙 _ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `id_whiskerLeft` / 引理 `id_whiskerLeft`

English:
lemma id_whiskerLeft
  statement: (.id _ _) ◁ η = (fun_ _).hom ≫ η ≫ (fun_ _).inv
  proof: by cat_disch

@[simp, reassoc]

中文:
引理 id_whiskerLeft
  结论: (.id _ _) ◁ η = (fun_ _).hom ≫ η ≫ (fun_ _).inv
  证明: by cat_disch

@[simp, reassoc]

Depends on / 依赖: cat_disch
-/
lemma id_whiskerLeft : (.id _ _) ◁ η = (fun_ _).hom ≫ η ≫ (fun_ _).inv := by cat_disch

@[simp, reassoc]
/--
lemma `whiskerLeft_comp` / 引理 `whiskerLeft_comp`

English:
lemma whiskerLeft_comp
  statement: ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ')
  proof: by cat_disch

中文:
引理 whiskerLeft_comp
  结论: ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ')
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma whiskerLeft_comp : ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ') := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `comp_whiskerLeft` / 引理 `comp_whiskerLeft`

English:
lemma comp_whiskerLeft
  proof: by
  cat_disch

中文:
引理 comp_whiskerLeft
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma comp_whiskerLeft :
    (ψ.comp φ) ◁ γ = (α_ _ _ _).hom ≫ (ψ ◁ (φ ◁ γ)) ≫ (α_ _ _ _).inv := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pentagon` / 引理 `pentagon`

English:
lemma pentagon
  proof: by
  cat_disch

中文:
引理 pentagon
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma pentagon
    {A'''' : Type u₁₃} {B'''' : Type u₁₄} {C'''' : Type u₁₅}
    [Category.{v₁₃} A''''] [Category.{v₁₄} B''''] [Category.{v₁₅} C'''']
    {F'''' : A'''' ⥤ B''''} {G'''' : C'''' ⥤ B''''}
    {σ : CatCospanTransform F''' G''' F'''' G''''} :
    (α_ ψ φ τ).hom ▷ σ ≫ (α_ ψ (φ.comp τ) σ).hom ≫ ψ ◁ (α_ φ τ σ).hom =
      (α_ (ψ.comp φ) τ σ).hom ≫ (α_ ψ φ (τ.comp σ)).hom := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `triangle` / 引理 `triangle`

English:
lemma triangle
  proof: by
  cat_disch

中文:
引理 triangle
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma triangle :
    (α_ ψ (.id _ _) φ).hom ≫ ψ ◁ (fun_ φ).hom = (ρ_ ψ).hom ▷ φ := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `triangle_inv` / 引理 `triangle_inv`

English:
lemma triangle_inv
  proof: by
  cat_disch

中文:
引理 triangle_inv
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma triangle_inv :
     (α_ ψ (.id _ _) φ).inv ≫ (ρ_ ψ).hom ▷ φ = ψ ◁ (fun_ φ).hom := by
  cat_disch

section Isos

variable {ψ ψ' : CatCospanTransform F G F' G'} (η : ψ ⟶ ψ') [IsIso η]
    {φ φ' : CatCospanTransform F' G' F'' G''} (θ : φ ⟶ φ') [IsIso θ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (ψ ◁ θ)
  body: ⟨ψ ◁ inv θ, ⟨by simp [← whiskerLeft_comp], by simp [← whiskerLeft_comp]⟩⟩

中文:
实例 :
  签名: 是同构 (ψ ◁ θ)
  定义体: ⟨ψ ◁ inv θ, ⟨by simp [← whiskerLeft_comp], by simp [← whiskerLeft_comp]⟩⟩

Depends on / 依赖: whiskerLeft_comp
-/
instance : IsIso (ψ ◁ θ) :=
    ⟨ψ ◁ inv θ, ⟨by simp [← whiskerLeft_comp], by simp [← whiskerLeft_comp]⟩⟩

/--
lemma `inv_whiskerLeft` / 引理 `inv_whiskerLeft`

English:
lemma inv_whiskerLeft
  statement: inv (ψ ◁ θ) = ψ ◁ inv θ
  proof: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← whiskerLeft_comp]

中文:
引理 inv_whiskerLeft
  结论: inv (ψ ◁ θ) = ψ ◁ inv θ
  证明: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← whiskerLeft_comp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, inv_eq_of_hom_inv_id, whiskerLeft_comp
-/
lemma inv_whiskerLeft : inv (ψ ◁ θ) = ψ ◁ inv θ := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← whiskerLeft_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (η ▷ φ)
  body: ⟨inv η ▷ φ, ⟨by simp [← comp_whiskerRight], by simp [← comp_whiskerRight]⟩⟩

中文:
实例 :
  签名: 是同构 (η ▷ φ)
  定义体: ⟨inv η ▷ φ, ⟨by simp [← comp_whiskerRight], by simp [← comp_whiskerRight]⟩⟩

Depends on / 依赖: comp_whiskerRight
-/
instance : IsIso (η ▷ φ) :=
    ⟨inv η ▷ φ, ⟨by simp [← comp_whiskerRight], by simp [← comp_whiskerRight]⟩⟩

/--
lemma `inv_whiskerRight` / 引理 `inv_whiskerRight`

English:
lemma inv_whiskerRight
  statement: inv (η ▷ φ) = inv η ▷ φ
  proof: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_whiskerRight]

中文:
引理 inv_whiskerRight
  结论: inv (η ▷ φ) = inv η ▷ φ
  证明: by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_whiskerRight]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, comp_whiskerRight, inv_eq_of_hom_inv_id
-/
lemma inv_whiskerRight : inv (η ▷ φ) = inv η ▷ φ := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_whiskerRight]

end Isos

end lemmas

end CatCospanTransform

end CategoryTheory.Limits
