/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctors to Cat

In this file, we state naturality properties of `mapId'` and `mapComp'`
for pseudofunctors to `Cat`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : B ⥤ᵖ Cat.{v', u'})

section naturality

variable {b₀ b₁ b₂ : B} {X Y : F.obj b₀}

section

variable (f : b₀ ⟶ b₀) (hf : f = 𝟙 b₀) (a : X ⟶ Y)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.mapId'_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat) {b₀ : B}   {X Y : ↑(F.obj b₀)} (f : b₀ ⟶ b₀) (
hf : f = CategoryTheory.CategoryStruct.id b₀) (a : X ⟶ Y),   CategoryTheory.Cate
goryStruct.comp ((F.map f).toFunctor.map a) ((F.mapId' f hf).hom.toNatTrans.app 
Y) =     CategoryTheory.CategoryStruct.comp ((F.mapId' f hf).hom.toNatTrans.app 
X) a
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₀；hf
 : f = CategoryTheory.CategoryStruct.id b₀；a : X ⟶ Y；(F.map f).toFunctor.map a；(
F.mapId' f hf).hom.toNatTrans.app Y；(F.mapId' f hf).hom.toNatTrans.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pseudofunctor.mapId'`：mapId'_hom_naturality : (F.map f).t
oFunctor.map a ≫ (F.mapId' f hf).hom.toNatTrans.app Y = (F.mapId' f hf).hom.toNa
tTrans.app X ≫ a

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapId'_hom_naturality :
    (F.map f).toFunctor.map a ≫ (F.mapId' f hf).hom.toNatTrans.app Y =
    (F.mapId' f hf).hom.toNatTrans.app X ≫ a :=
  (F.mapId' f hf).hom.toNatTrans.naturality a

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.mapId'_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat) {b₀ : B}   {X Y : ↑(F.obj b₀)} (f : b₀ ⟶ b₀) (
hf : f = CategoryTheory.CategoryStruct.id b₀) (a : X ⟶ Y),   CategoryTheory.Cate
goryStruct.comp ((F.mapId' f hf).inv.toNatTrans.app X) ((F.map f).toFunctor.map 
a) =     CategoryTheory.CategoryStruct.comp a ((F.mapId' f hf).inv.toNatTrans.ap
p Y)
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₀；hf
 : f = CategoryTheory.CategoryStruct.id b₀；a : X ⟶ Y；(F.mapId' f hf).inv.toNatTr
ans.app X；(F.map f).toFunctor.map a；(F.mapId' f hf).inv.toNatTrans.app Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Pseudofunctor.mapId'`：mapId'_hom_naturality : (F.map f).t
oFunctor.map a ≫ (F.mapId' f hf).hom.toNatTrans.app Y = (F.mapId' f hf).hom.toNa
tTrans.app X ≫ a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapId'_inv_naturality :
    (F.mapId' f hf).inv.toNatTrans.app X ≫ (F.map f).toFunctor.map a =
    a ≫ (F.mapId' f hf).inv.toNatTrans.app Y :=
  ((F.mapId' f hf).inv.toNatTrans.naturality a).symm

end

section

variable (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  (hfg : f ≫ g = fg) (a : X ⟶ Y)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.mapComp'_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat)   {b₀ b₁ b₂ : B} {X Y : ↑(F.obj b₀)} (f : b₀ ⟶
 b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)   (hfg : CategoryTheory.CategoryStruct.comp f 
g = fg) (a : X ⟶ Y),   CategoryTheory.CategoryStruct.comp ((F.map fg).toFunctor.
map a) ((F.mapComp' f g fg hfg).hom.toNatTrans.app Y) =     CategoryTheory.Categ
oryStruct.comp ((F.mapComp' f g fg hfg).hom.toNatTrans.app X)       ((F.map g).t
oFunctor.map ((F.map f).toFunctor.map a))
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₁；g 
: b₁ ⟶ b₂；fg : b₀ ⟶ b₂；hfg : CategoryTheory.CategoryStruct.comp f g = fg；a : X ⟶
 Y；(F.map fg).toFunctor.map a；(F.mapComp' f g fg hfg).hom.toNatTrans.app Y；(F.ma
pComp' f g fg hfg).hom.toNatTrans.app X；(F.map g).toFunctor.map ((F.map f).toFun
ctor.map a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapComp'_hom_naturality :
    (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y =
    (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫ (F.map g).toFunctor.map
      ((F.map f).toFunctor.map a) :=
  (F.mapComp' f g fg hfg).hom.toNatTrans.naturality a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed in Sites/Descent/IsPrestack.lean
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pseudofunctor.mapComp'_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat)   {b₀ b₁ b₂ : B} {X Y : ↑(F.obj b₀)} (f : b₀ ⟶
 b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)   (hfg : CategoryTheory.CategoryStruct.comp f 
g = fg) (a : X ⟶ Y),   CategoryTheory.CategoryStruct.comp ((F.map g).toFunctor.m
ap ((F.map f).toFunctor.map a))       ((F.mapComp' f g fg hfg).inv.toNatTrans.ap
p Y) =     CategoryTheory.CategoryStruct.comp ((F.mapComp' f g fg hfg).inv.toNat
Trans.app X) ((F.map fg).toFunctor.map a)
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₁；g 
: b₁ ⟶ b₂；fg : b₀ ⟶ b₂；hfg : CategoryTheory.CategoryStruct.comp f g = fg；a : X ⟶
 Y；(F.map g).toFunctor.map ((F.map f).toFunctor.map a)；(F.mapComp' f g fg hfg).i
nv.toNatTrans.app Y；(F.mapComp' f g fg hfg).inv.toNatTrans.app X；(F.map fg).toFu
nctor.map a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
-/
lemma mapComp'_inv_naturality :
    (F.map g).toFunctor.map ((F.map f).toFunctor.map a) ≫
    (F.mapComp' f g fg hfg).inv.toNatTrans.app Y =
    (F.mapComp' f g fg hfg).inv.toNatTrans.app X ≫ (F.map fg).toFunctor.map a :=
  (F.mapComp' f g fg hfg).inv.toNatTrans.naturality a

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.mapComp'_naturality_1** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat)   {b₀ b₁ b₂ : B} {X Y : ↑(F.obj b₀)} (f : b₀ ⟶
 b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)   (hfg : CategoryTheory.CategoryStruct.comp f 
g = fg) (a : X ⟶ Y),   CategoryTheory.CategoryStruct.comp ((F.mapComp' f g fg hf
g).inv.toNatTrans.app X)       (CategoryTheory.CategoryStruct.comp ((F.map fg).t
oFunctor.map a) ((F.mapComp' f g fg hfg).hom.toNatTrans.app Y)) =     (F.map g).
toFunctor.map ((F.map f).toFunctor.map a)
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₁；g 
: b₁ ⟶ b₂；fg : b₀ ⟶ b₂；hfg : CategoryTheory.CategoryStruct.comp f g = fg；a : X ⟶
 Y；(F.mapComp' f g fg hfg).inv.toNatTrans.app X；CategoryTheory.CategoryStruct.co
mp ((F.map fg).toFunctor.map a) ((F.mapComp' f g fg hfg).hom.toNatTrans.app Y)；F
.map g；(F.map f).toFunctor.map a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
-/
lemma mapComp'_naturality_1 :
    (F.mapComp' f g fg hfg).inv.toNatTrans.app X ≫
      (F.map fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y =
    (F.map g).toFunctor.map ((F.map f).toFunctor.map a) :=
  NatIso.naturality_1 (Cat.Hom.toNatIso (F.mapComp' f g fg hfg)) a

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.mapComp'_naturality_2** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Pseudofunctor`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Ps
eudofunctor B CategoryTheory.Cat)   {b₀ b₁ b₂ : B} {X Y : ↑(F.obj b₀)} (f : b₀ ⟶
 b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)   (hfg : CategoryTheory.CategoryStruct.comp f 
g = fg) (a : X ⟶ Y),   CategoryTheory.CategoryStruct.comp ((F.mapComp' f g fg hf
g).hom.toNatTrans.app X)       (CategoryTheory.CategoryStruct.comp ((F.map g).to
Functor.map ((F.map f).toFunctor.map a))         ((F.mapComp' f g fg hfg).inv.to
NatTrans.app Y)) =     (F.map fg).toFunctor.map a
参数：F : CategoryTheory.Pseudofunctor B CategoryTheory.Cat；F.obj b₀；f : b₀ ⟶ b₁；g 
: b₁ ⟶ b₂；fg : b₀ ⟶ b₂；hfg : CategoryTheory.CategoryStruct.comp f g = fg；a : X ⟶
 Y；(F.mapComp' f g fg hfg).hom.toNatTrans.app X；CategoryTheory.CategoryStruct.co
mp ((F.map g).toFunctor.map ((F.map f).toFunctor.map a))         ((F.mapComp' f 
g fg hfg).inv.toNatTrans.app Y)；F.map fg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
-/
lemma mapComp'_naturality_2 :
    (F.mapComp' f g fg hfg).hom.toNatTrans.app X ≫
      (F.map g).toFunctor.map ((F.map f).toFunctor.map a) ≫
        (F.mapComp' f g fg hfg).inv.toNatTrans.app Y =
    (F.map fg).toFunctor.map a :=
  NatIso.naturality_2 (Cat.Hom.toNatIso (F.mapComp' f g fg hfg)) a

end

end naturality

end Pseudofunctor

end CategoryTheory

