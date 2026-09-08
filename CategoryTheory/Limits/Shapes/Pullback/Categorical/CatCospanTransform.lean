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
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```

with specified `CatCommSq`s expressing 2-commutativity of the squares. These
transformations are used to encode 2-functoriality of categorical pullback squares.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃ v₁₄ v₁₅
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ u₁₄ u₁₅

/-- A `CatCospanTransform F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
with specified `CatCommSq`s expressing 2-commutativity of the squares. -/
/-
**CategoryTheory.Limits.CatCospanTransform** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：CatCospanTransform {A : Type u₁} {B : Type u₂} {C : Type u₃} [Category.{v₁
} A] [Category.{v₂} B] [Category.{v₃} C] (F : A ⥤ B) (G : C ⥤ B) {A' : Type u₄} 
{B' : Type u₅} {C' : Type u₆} [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v
₆} C'] (F' : A' ⥤ B') (G' : C' ⥤ B') where /-- the functor on the left component
 -/ left : A ⥤ A' /-- the functor on the base component -/ base : B ⥤ B' /-- the
 functor on the right component -/ right : C ⥤ C' /-- a `CatCommSq` bundling the
 natural isomorphism `F ⋙ 
参数：F : A ⥤ B；G : C ⥤ B；F' : A' ⥤ B'；G' : C' ⥤ B'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `CatCospanTransform F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
with specified `CatCommSq`s expressing 2-commutativity of the squares. -/
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
/-
**CategoryTheory.Limits.CatCospanTransform.id** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.CatCospanTransform`。
形式化陈述：id : CatCospanTransform F G F G where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `CatCospanTransform`
-/
def id : CatCospanTransform F G F G where
  left := 𝟭 A
  base := 𝟭 B
  right := 𝟭 C

variable {F G}
/-- Composition of `CatCospanTransforms` is defined "componentwise". -/
@[simps]
/-
**CategoryTheory.Limits.CatCospanTransform.comp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.CatCospanTransform`。
形式化陈述：comp {A' : Type u₄} {B' : Type u₅} {C' : Type u₆} [Category.{v₄} A'] [Cate
gory.{v₅} B'] [Category.{v₆} C'] {F' : A' ⥤ B'} {G' : C' ⥤ B'} {A'' : Type u₇} {
B'' : Type u₈} {C'' : Type u₉} [Category.{v₇} A''] [Category.{v₈} B''] [Category
.{v₉} C''] {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''} (ψ : CatCospanTransform F G F' G'
) (ψ' : CatCospanTransform F' G' F'' G'') : CatCospanTransform F G F'' G'' where
 left
参数：ψ : CatCospanTransform F G F' G'；ψ' : CatCospanTransform F' G' F'' G''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `CatCospanTransforms` is defined "componentwise".
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

/-- A morphism of `CatCospanTransform F G F' G'` is a triple of natural
transformations between the component functors, subjects to
coherence conditions respective to the squares. -/
/-
**CategoryTheory.Limits.CatCospanTransformMorphism** 是 Mathlib 中的一个结构，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：CatCospanTransformMorphism (ψ ψ' : CatCospanTransform F G F' G') where /--
 the natural transformations between the left components -/ left : ψ.left ⟶ ψ'.l
eft /-- the natural transformations between the right components -/ right : ψ.ri
ght ⟶ ψ'.right /-- the natural transformations between the base components -/ ba
se : ψ.base ⟶ ψ'.base /-- the coherence condition for the left square -/ left_co
herence : ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left F' = Functor.whiskerL
eft F base ≫ ψ'.squareLeft
参数：ψ ψ' : CatCospanTransform F G F' G'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of `CatCospanTransform F G F' G'` is a triple of natural
transformations between the component functors, subjects to
coherence conditions respective to the squares.
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
/-
**CategoryTheory.Limits.CatCospanTransform.category** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：category : Category (CatCospanTransform F G F' G') where Hom ψ ψ'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Limits.CatCospanTransform.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits.CatCospanTransform`。
形式化陈述：hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left
 = θ'.left) (hr : θ.right = θ'.right) (hb : θ.base = θ'.base) : θ = θ'
参数：hl : θ.left = θ'.left；hr : θ.right = θ'.right；hb : θ.base = θ'.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.ext`：∀ {A : Type u₁} {B
 : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}   {inst :
 CategoryTheory.Category.{v₁, u₁} A} {inst…
-/
lemma hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'}
    (hl : θ.left = θ'.left) (hr : θ.right = θ'.right) (hb : θ.base = θ'.base) :
    θ = θ' := by
  apply CatCospanTransformMorphism.ext <;> assumption

end CatCospanTransform

namespace CatCospanTransformMorphism

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CatCospanTransformMorphism.left_coherence_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Limits.CatCospanTransformMorphism`。
形式化陈述：left_coherence_app {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') (x :
 A) : ψ.squareLeft.iso.hom.app x ≫ F'.map (α.left.app x) = α.base.app (F.obj x) 
≫ ψ'.squareLeft.iso.hom.app x
参数：α : ψ ⟶ ψ'；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.left_coherence`：∀ {A : 
Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆
}   [inst : CategoryTheory.Category.{v₁, u₁} A] [inst…
-/
lemma left_coherence_app {ψ ψ' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (x : A) :
    ψ.squareLeft.iso.hom.app x ≫ F'.map (α.left.app x) =
    α.base.app (F.obj x) ≫ ψ'.squareLeft.iso.hom.app x :=
  congr_app α.left_coherence x

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CatCospanTransformMorphism.right_coherence_app** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CatCospanTransformMorphism`。
形式化陈述：right_coherence_app {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') (x 
: C) : ψ.squareRight.iso.hom.app x ≫ G'.map (α.right.app x) = α.base.app (G.obj 
x) ≫ ψ'.squareRight.iso.hom.app x
参数：α : ψ ⟶ ψ'；x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.right_coherence`：∀ {A :
 Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u
₆}   [inst : CategoryTheory.Category.{v₁, u₁} A] [inst…
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
/-
**CategoryTheory.Limits.CatCospanTransformMorphism.whiskerLeft** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.CatCospanTransformMorphism`。
形式化陈述：whiskerLeft (φ : CatCospanTransform F G F' G') {ψ ψ' : CatCospanTransform 
F' G' F'' G''} (α : ψ ⟶ ψ') : (φ.comp ψ) ⟶ (φ.comp ψ') where left
参数：φ : CatCospanTransform F G F' G'；α : ψ ⟶ ψ'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering left of a `CatCospanTransformMorphism` by a `CatCospanTransform`.
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
/-
**CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.CatCospanTransformMorphism`。
形式化陈述：whiskerRight {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') (φ : CatCo
spanTransform F' G' F'' G'') : (ψ.comp φ) ⟶ (ψ'.comp φ) where left
参数：α : ψ ⟶ ψ'；φ : CatCospanTransform F' G' F'' G''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering right of a `CatCospanTransformMorphism` by a `CatCospanTransform`.
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
    rw [← Functor.map_comp_assoc, ← left_coherence_app, Functor.map_comp_assoc]
    simp
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc, ← right_coherence_app, Functor.map_comp_assoc]
    simp

end CatCospanTransformMorphism

namespace CatCospanTransform

/-- A constructor for isomorphisms of `CatCospanTransform`'s. -/
@[simps]
/-
**CategoryTheory.Limits.CatCospanTransform.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.CatCospanTransform`。
形式化陈述：mkIso {ψ ψ' : CatCospanTransform F G F' G'} (left : ψ.left ≅ ψ'.left) (rig
ht : ψ.right ≅ ψ'.right) (base : ψ.base ≅ ψ'.base) (left_coherence : ψ.squareLef
t.iso.hom ≫ Functor.whiskerRight left.hom F' = Functor.whiskerLeft F base.hom ≫ 
ψ'.squareLeft.iso.hom
参数：left : ψ.left ≅ ψ'.left；right : ψ.right ≅ ψ'.right；base : ψ.base ≅ ψ'.base。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for isomorphisms of `CatCospanTransform`'s.
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

/-
**CategoryTheory.Limits.CatCospanTransform.isIso_left** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：isIso_left : IsIso f.left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_left : IsIso f.left :=
  ⟨(inv f).left, by simp [← CatCospanTransform.category_comp_left]⟩
/-
**CategoryTheory.Limits.CatCospanTransform.isIso_right** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：isIso_right : IsIso f.right
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_right : IsIso f.right :=
  ⟨(inv f).right, by simp [← CatCospanTransform.category_comp_right]⟩
/-
**CategoryTheory.Limits.CatCospanTransform.isIso_base** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：isIso_base : IsIso f.base
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_base : IsIso f.base :=
  ⟨(inv f).base, by simp [← CatCospanTransform.category_comp_base]⟩

@[simp]
/-
**CategoryTheory.Limits.CatCospanTransform.inv_left** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：inv_left : inv f.left = (inv f).left
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_left : inv f.left = (inv f).left := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_left]

@[simp]
/-
**CategoryTheory.Limits.CatCospanTransform.inv_right** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：inv_right : inv f.right = (inv f).right
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_right : inv f.right = (inv f).right := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_right]

@[simp]
/-
**CategoryTheory.Limits.CatCospanTransform.inv_base** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：inv_base : inv f.base = (inv f).base
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_base : inv f.base = (inv f).base := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_base]

/-- Extract an isomorphism between left components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/-
**CategoryTheory.Limits.CatCospanTransform.leftIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.CatCospanTransform`。
形式化陈述：leftIso : ψ.left ≅ ψ'.left where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism between left components from an isomorphism in
`CatCospanTransform F G F' G'`.
-/
def leftIso : ψ.left ≅ ψ'.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← category_comp_left]
  inv_hom_id := by simp [← category_comp_left]

/-- Extract an isomorphism between right components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/-
**CategoryTheory.Limits.CatCospanTransform.rightIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：rightIso : ψ.right ≅ ψ'.right where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism between right components from an isomorphism in
`CatCospanTransform F G F' G'`.
-/
def rightIso : ψ.right ≅ ψ'.right where
  hom := e.hom.right
  inv := e.inv.right
  hom_inv_id := by simp [← category_comp_right]
  inv_hom_id := by simp [← category_comp_right]

/-- Extract an isomorphism between base components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
/-
**CategoryTheory.Limits.CatCospanTransform.baseIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.CatCospanTransform`。
形式化陈述：baseIso : ψ.base ≅ ψ'.base where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract an isomorphism between base components from an isomorphism in
`CatCospanTransform F G F' G'`.
-/
def baseIso : ψ.base ≅ ψ'.base where
  hom := e.hom.base
  inv := e.inv.base
  hom_inv_id := by simp [← category_comp_base]
  inv_hom_id := by simp [← category_comp_base]

set_option backward.isDefEq.respectTransparency.types false in
omit [IsIso f] in
/-
**CategoryTheory.Limits.CatCospanTransform.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：isIso_iff : IsIso f ↔ IsIso f.left ∧ IsIso f.base ∧ IsIso f.right where mp
 h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.left_coherence`：∀ {A : 
Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆
}   [inst : CategoryTheory.Category.{v₁, u₁} A] [inst…
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.right_coherence`：∀ {A :
 Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u
₆}   [inst : CategoryTheory.Category.{v₁, u₁} A] [inst…
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.CatCospanTransform.mkIso_inv_left`：∀ {A : Type u₁}
 {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}   [ins
t : CategoryTheory.Category.{v₁, u₁} A] [inst…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.CatCospanTransform.mkIso_inv_right`：∀ {A : Type u₁
} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}   [in
st : CategoryTheory.Category.{v₁, u₁} A] [inst…
· 使用定理 `CategoryTheory.Limits.CatCospanTransform.mkIso_inv_base`：∀ {A : Type u₁}
 {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}   [ins
t : CategoryTheory.Category.{v₁, u₁} A] [inst…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
lemma isIso_iff : IsIso f ↔ IsIso f.left ∧ IsIso f.base ∧ IsIso f.right where
  mp h := ⟨inferInstance, inferInstance, inferInstance⟩
  mpr h := by
    obtain ⟨_, _, _⟩ := h
    use mkIso (asIso f.left) (asIso f.right) (asIso f.base)
      f.left_coherence f.right_coherence |>.inv
    aesop_cat

end Iso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for categorical cospan transformations. -/
@[simps!]
/-
**CategoryTheory.Limits.CatCospanTransform.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：leftUnitor (φ : CatCospanTransform F G F' G') : (CatCospanTransform.id F G
).comp φ ≅ φ
参数：φ : CatCospanTransform F G F' G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor isomorphism for categorical cospan transformations.
-/
def leftUnitor (φ : CatCospanTransform F G F' G') :
    (CatCospanTransform.id F G).comp φ ≅ φ :=
  mkIso φ.left.leftUnitor φ.right.leftUnitor φ.base.leftUnitor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for categorical cospan transformations. -/
@[simps!]
/-
**CategoryTheory.Limits.CatCospanTransform.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：rightUnitor (φ : CatCospanTransform F G F' G') : φ.comp (.id F' G') ≅ φ
参数：φ : CatCospanTransform F G F' G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor isomorphism for categorical cospan transformations.
-/
def rightUnitor (φ : CatCospanTransform F G F' G') :
    φ.comp (.id F' G') ≅ φ :=
  mkIso φ.left.rightUnitor φ.right.rightUnitor φ.base.rightUnitor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for categorical cospan transformations. -/
@[simps!]
/-
**CategoryTheory.Limits.CatCospanTransform.associator** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：associator {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂} [Category
.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C'''] {F''' : A''' ⥤ B'''} {G
''' : C''' ⥤ B'''} (φ : CatCospanTransform F G F' G') (φ' : CatCospanTransform F
' G' F'' G'') (φ'' : CatCospanTransform F'' G'' F''' G''') : (φ.comp φ').comp φ'
' ≅ φ.comp (φ'.comp φ'')
参数：φ : CatCospanTransform F G F' G'；φ' : CatCospanTransform F' G' F'' G''；φ'' : 
CatCospanTransform F'' G'' F''' G'''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for categorical cospan transformations.
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
@[inherit_doc] scoped notation "λ_" => CatCospanTransform.leftUnitor
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
/-
**CategoryTheory.Limits.CatCospanTransform.whisker_exchange** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：whisker_exchange : ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whisker_exchange : ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ := by cat_disch

@[simp]
/-
**CategoryTheory.Limits.CatCospanTransform.id_whiskerRight** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：id_whiskerRight : 𝟙 ψ ▷ φ = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_left`：∀ {A
 : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type
 u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_right`：∀ {
A : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Typ
e u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_base`：∀ {A
 : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type
 u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
-/
lemma id_whiskerRight : 𝟙 ψ ▷ φ = 𝟙 _ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.whiskerRight_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：whiskerRight_id : η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_id : η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv := by cat_disch

@[simp, reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.comp_whiskerRight** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：comp_whiskerRight : (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_left`：∀ {A
 : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type
 u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_right`：∀ {
A : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Typ
e u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `CategoryTheory.Limits.CatCospanTransformMorphism.whiskerRight_base`：∀ {A
 : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type
 u₆} {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
-/
lemma comp_whiskerRight : (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.whiskerRight_comp** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：whiskerRight_comp : η ▷ (φ.comp τ) = (α_ _ _ _).inv ≫ (η ▷ φ) ▷ τ ≫ (α_ _ 
_ _).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_twice`：whiskerRight_twice {H K : B ⥤
 C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) : whiskerRight (whiskerRight α F) G = (F
unctor.associator _ _ _).hom ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_comp :
    η ▷ (φ.comp τ) = (α_ _ _ _).inv ≫ (η ▷ φ) ▷ τ ≫ (α_ _ _ _).hom := by
  cat_disch

@[simp]
/-
**CategoryTheory.Limits.CatCospanTransform.whiskerleft_id** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：whiskerleft_id : ψ ◁ 𝟙 φ = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerleft_id : ψ ◁ 𝟙 φ = 𝟙 _ := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.id_whiskerLeft** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：id_whiskerLeft : (.id _ _) ◁ η = (fun_ _).hom ≫ η ≫ (fun_ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_whiskerLeft : (.id _ _) ◁ η = (λ_ _).hom ≫ η ≫ (λ_ _).inv := by cat_disch

@[simp, reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.whiskerLeft_comp** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：whiskerLeft_comp : ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_comp : ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ') := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.comp_whiskerLeft** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：comp_whiskerLeft : (ψ.comp φ) ◁ γ = (α_ _ _ _).hom ≫ (ψ ◁ (φ ◁ γ)) ≫ (α_ _
 _ _).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerLeft_twice`：whiskerLeft_twice (F : B ⥤ C) 
(G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) : whiskerLeft F (whiskerLeft G α) = (Funct
or.associator _ _ _).inv ≫ whi…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_whiskerLeft :
    (ψ.comp φ) ◁ γ = (α_ _ _ _).hom ≫ (ψ ◁ (φ ◁ γ)) ≫ (α_ _ _ _).inv := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.pentagon** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：pentagon {A'''' : Type u₁₃} {B'''' : Type u₁₄} {C'''' : Type u₁₅} [Categor
y.{v₁₃} A''''] [Category.{v₁₄} B''''] [Category.{v₁₅} C''''] {F'''' : A'''' ⥤ B'
'''} {G'''' : C'''' ⥤ B''''} {σ : CatCospanTransform F''' G''' F'''' G''''} : (α
_ ψ φ τ).hom ▷ σ ≫ (α_ ψ (φ.comp τ) σ).hom ≫ ψ ◁ (α_ φ τ σ).hom = (α_ (ψ.comp φ)
 τ σ).hom ≫ (α_ ψ φ (τ.comp σ)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.Limits.CatCospanTransform.triangle** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CatCospanTransform`。
形式化陈述：triangle : (α_ ψ (.id _ _) φ).hom ≫ ψ ◁ (fun_ φ).hom = (ρ_ ψ).hom ▷ φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangle :
    (α_ ψ (.id _ _) φ).hom ≫ ψ ◁ (λ_ φ).hom = (ρ_ ψ).hom ▷ φ := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.CatCospanTransform.triangle_inv** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：triangle_inv : (α_ ψ (.id _ _) φ).inv ≫ (ρ_ ψ).hom ▷ φ = ψ ◁ (fun_ φ).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.hom_ext`：hom_ext {ψ ψ' : CatCos
panTransform F G F' G'} {θ θ' : ψ ⟶ ψ'} (hl : θ.left = θ'.left) (hr : θ.right = 
θ'.right) (hb : θ.base = θ'.base) : θ …
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangle_inv :
     (α_ ψ (.id _ _) φ).inv ≫ (ρ_ ψ).hom ▷ φ = ψ ◁ (λ_ φ).hom := by
  cat_disch

section Isos

variable {ψ ψ' : CatCospanTransform F G F' G'} (η : ψ ⟶ ψ') [IsIso η]
    {φ φ' : CatCospanTransform F' G' F'' G''} (θ : φ ⟶ φ') [IsIso θ]

/-
**CategoryTheory.Limits.CatCospanTransform.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.CatCospanTransform`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (ψ ◁ θ) :=
    ⟨ψ ◁ inv θ, ⟨by simp [← whiskerLeft_comp], by simp [← whiskerLeft_comp]⟩⟩
/-
**CategoryTheory.Limits.CatCospanTransform.inv_whiskerLeft** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：inv_whiskerLeft : inv (ψ ◁ θ) = ψ ◁ inv θ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.Limits.CatCospanTransform.instIsIsoWhiskerLeft`：∀ {A : Ty
pe u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆} 
{A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.whiskerleft_id`：whiskerleft_id 
: ψ ◁ 𝟙 φ = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_whiskerLeft : inv (ψ ◁ θ) = ψ ◁ inv θ := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← whiskerLeft_comp]
/-
**CategoryTheory.Limits.CatCospanTransform.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.CatCospanTransform`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (η ▷ φ) :=
    ⟨inv η ▷ φ, ⟨by simp [← comp_whiskerRight], by simp [← comp_whiskerRight]⟩⟩
/-
**CategoryTheory.Limits.CatCospanTransform.inv_whiskerRight** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.CatCospanTransform`。
形式化陈述：inv_whiskerRight : inv (η ▷ φ) = inv η ▷ φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.Limits.CatCospanTransform.instIsIsoWhiskerRight`：∀ {A : T
ype u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
 {A'' : Type u₇} {B'' : Type u₈}   {C'' : Type u₉} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.Limits.CatCospanTransform.id_whiskerRight`：id_whiskerRigh
t : 𝟙 ψ ▷ φ = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_whiskerRight : inv (η ▷ φ) = inv η ▷ φ := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_whiskerRight]

end Isos

end lemmas

end CatCospanTransform

end CategoryTheory.Limits

