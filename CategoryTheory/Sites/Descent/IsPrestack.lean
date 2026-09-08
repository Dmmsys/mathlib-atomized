/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Prestacks: descent of morphisms

Let `C` be a category and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
Given `S : C`, and objects `M` and `N` in `F.obj (.mk (op S))`,
we define a presheaf of types `F.presheafHom M N` on the category `Over S`:
its sections on an object `T : Over S` corresponding to a morphism `p : X ⟶ S`
are the type of morphisms `p^* M ⟶ p^* N`. We shall say that
`F` satisfies the descent of morphisms for a Grothendieck topology `J`
if these presheaves are all sheaves (typeclass `F.IsPrestack J`).

## Terminological note

In this file, we use the language of pseudofunctors to formalize prestacks.
Similar notions could also be phrased in terms of fibered categories.
In the mathematical literature, various uses of the words "prestacks" and
"stacks" exists. Our definitions are consistent with Giraud's definition II 1.2.1
in *Cohomologie non abélienne*: a prestack is defined by the descent of morphisms
condition with respect to a Grothendieck topology, and a stack by the effectiveness
of the descent. However, contrary to Laumon and Moret-Bailly in *Champs algébriques* 3.1,
we do not require that target categories are groupoids.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

/-- Given a pseudofunctor `F` from  `LocallyDiscrete Cᵒᵖ` to `Cat`, objects `M₁` and `M₂`
of `F` over `X₁` and `X₂`, morphisms `f₁ : Y ⟶ X₁` and `f₂ : Y ⟶ X₂`, this is a version
of the pullback map `(f₁^* M₁ ⟶ f₂^* M₂) → (g^* (f₁^* M₁) ⟶ g^* (f₂^* M₂))` by a
morphism `g : Y' ⟶ Y`, where we actually replace `g^* (f₁^* M₁)` by `gf₁^* M₁`
where `gf₁ : Y' ⟶ X₁` is a morphism such that `g ≫ f₁ = gf₁` (and similarly for `M₂`). -/
/-
**CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`。
形式化陈述：pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ 
⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ 
(F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂
 : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
Given a pseudofunctor `F` from  `LocallyDiscrete Cᵒᵖ` to `Cat`, objects `M₁` and
 `M₂`
of `F` over `X₁` and `X₂`, morphisms `f₁ : Y ⟶ X₁` and `f₂ : Y ⟶ X₂`, this is a 
version
of the pullback map `(f₁^* M₁ ⟶ f₂^* M₂) → (g^* (f₁^* M₁) ⟶ g^* (f₂^* M₂))` by a
morphism `g : Y' ⟶ Y`, where we actually replace `g^* (f₁^* M₁)` by `gf₁^* M₁`
where `gf₁ : Y' ⟶ X₁` is a morphism such that `g ≫ f₁ = gf₁` (and similarly for 
`M₂`).
-/
def pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂ :=
  (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.toNatTrans.app _ ≫
    (F.map g.op.toLoc).toFunctor.map φ ≫
      (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.toNatTrans.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`。
形式化陈述：map_eq_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op
 X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (φ : (F.map f₁.op.toLoc).toFunctor.ob
j M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X
₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) : (F.map g.op.toL
oc).toFunctor.map φ = (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)
).inv.toNatTrans.app _ ≫ pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ (F.mapComp' f₂.op.toLoc
 g.op.toLoc gf₂.op.toLoc (
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Cat.Hom₂.comp_app`：∀ {C D : CategoryTheory.Cat} {F G H : 
C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : ↑C),   (CategoryTheory.CategoryStruct.comp α
 β).toNatTrans.app X =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_eq_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map g.op.toLoc).toFunctor.map φ =
    (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).inv.toNatTrans.app _ ≫
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
    (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).hom.toNatTrans.app _ := by
  simp [Cat.Hom.comp_toFunctor, pullHom, ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`。
形式化陈述：pullHom_id ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂)
)⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁
 ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) : pullHom φ (𝟙 _) f₁ f₂ = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id_hom_app`：∀ {B : Type u_1} 
[inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.Strict 
B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `CategoryTheory.locallyDiscreteBicategory.strict`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C],   CategoryTheory.Bicategory.Strict (CategoryT
heory.LocallyDiscrete C)
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_comp_id_inv_app`：∀ {B : Type u_1} 
[inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.Strict 
B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Cat.Hom₂.comp_app`：∀ {C D : CategoryTheory.Cat} {F G H : 
C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : ↑C),   (CategoryTheory.CategoryStruct.comp α
 β).toNatTrans.app X =…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullHom_id ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
      pullHom φ (𝟙 _) f₁ f₂ = φ := by
  simp [pullHom, mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app,
    ← reassoc_of% Cat.Hom₂.comp_app, Iso.inv_hom_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`。
形式化陈述：pullHom_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (o
p X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (φ : (F.map f₁.op.toLoc).toFunctor.o
bj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ 
X₁) (gf₂ : Y' ⟶ X₂) ⦃Y'' : C⦄ (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁) (g'f₂ : Y'' ⟶ X₂
) (hgf₁ : g ≫ f₁ = gf₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.locallyDiscreteBicategory.strict`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C],   CategoryTheory.Bicategory.Strict (CategoryT
heory.LocallyDiscrete C)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_a
pp`：∀ {B : Type u_1} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheo
ry.Bicategory.Strict B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRi
ght_app_assoc`：∀ {B : Type u_1} [inst : CategoryTheory.Bicategory B] [inst_1 : C
ategoryTheory.Bicategory.Strict B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_inv_naturality_assoc`：∀ {B : Type 
u} [inst : CategoryTheory.Bicategory B] (F : CategoryTheory.Pseudofunctor B Cate
goryTheory.Cat)   {b₀ b₁ b₂ : B} {X Y : ↑(F.obj …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Cat.Hom₂.comp_app`：∀ {C D : CategoryTheory.Cat} {F G H : 
C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : ↑C),   (CategoryTheory.CategoryStruct.comp α
 β).toNatTrans.app X =…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma pullHom_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) ⦃Y'' : C⦄ (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁)
    (g'f₂ : Y'' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hg'f₁ : g' ≫ gf₁ = g'f₁ := by cat_disch) (hg'f₂ : g' ≫ gf₂ = g'f₂ := by cat_disch) :
    pullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) g' g'f₁ g'f₂ hg'f₁ hg'f₂ =
      pullHom φ (g' ≫ g) g'f₁ g'f₂ := by
  dsimp [pullHom]
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ _ rfl (by aesop),
    F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ _ rfl (by aesop)]
  simp [mapComp'_inv_naturality_assoc, ← reassoc_of% Cat.Hom₂.comp_app]

end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

section

variable (F) {S : C} (M N : F.obj (.mk (op S)))

/-- If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat`, and `M` and `N` are objects in
`F.obj (.mk (op S))`, this is the presheaf of morphisms from `M` to `N`: it sends
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $p^* M ⟶ p^* N$. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Pseudofunctor.presheafHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pseudofunctor`。
形式化陈述：presheafHom : (Over S)ᵒᵖ ⥤ Type v' where obj T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat`, and `M` and `N` are objects in
`F.obj (.mk (op S))`, this is the presheaf of morphisms from `M` to `N`: it send
s
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $p^* M ⟶ p^* N$.
-/
def presheafHom : (Over S)ᵒᵖ ⥤ Type v' where
  obj T := (F.map (.toLoc T.unop.hom.op)).toFunctor.obj M ⟶
    (F.map (.toLoc T.unop.hom.op)).toFunctor.obj N
  map {T₁ T₂} p := ↾fun f ↦ pullHom f p.unop.left T₂.unop.hom T₂.unop.hom

/-- The bijection `(M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S)))`. -/
@[simps! -isSimp]
/-
**CategoryTheory.Pseudofunctor.presheafHomObjHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：presheafHomObjHomEquiv {M N : (F.obj (.mk (op S)))} : (M ⟶ N) ≃ (F.preshea
fHom M N).obj (op (Over.mk (𝟙 S)))
参数：F.obj (.mk (op S))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S)))`.
-/
def presheafHomObjHomEquiv {M N : (F.obj (.mk (op S)))} :
    (M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S))) :=
  Iso.homCongr ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).symm.app M)
    ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).symm.app N)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility isomorphism of `Pseudofunctor.presheafHom` with "restrictions". -/
/-
**CategoryTheory.Pseudofunctor.overMapCompPresheafHomIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：overMapCompPresheafHomIso {S' : C} (q : S' ⟶ S) : (Over.map q).op ⋙ F.pres
heafHom M N ≅ F.presheafHom ((F.map (.toLoc q.op)).toFunctor.obj M) ((F.map (.to
Loc q.op)).toFunctor.obj N)
参数：q : S' ⟶ S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
Compatibility isomorphism of `Pseudofunctor.presheafHom` with "restrictions".
-/
def overMapCompPresheafHomIso {S' : C} (q : S' ⟶ S) :
    (Over.map q).op ⋙ F.presheafHom M N ≅
      F.presheafHom ((F.map (.toLoc q.op)).toFunctor.obj M)
        ((F.map (.toLoc q.op)).toFunctor.obj N) :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso (by
    letI e := Cat.Hom.toNatIso (F.mapComp' (.toLoc q.op) (.toLoc T.unop.hom.op)
      (.toLoc ((Over.map q).obj T.unop).hom.op))
    exact (Iso.homFromEquiv (e.app M)).trans (Iso.homToEquiv (e.app N)))) (by
      rintro ⟨T₁⟩ ⟨T₂⟩ ⟨f⟩
      ext g
      dsimp [pullHom]
      simp only [Category.assoc,
        Functor.map_comp]
      rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl _ rfl,
        F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ (by
          simp only [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w_assoc])])

end

variable (F)

/-- The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
satisfies the descent property for morphisms, i.e. is a prestack.
(See the terminological note in the introduction of the file `Sites.Descent.IsPrestack`.) -/
@[stacks 026F "(2)"]
/-
**CategoryTheory.Pseudofunctor.IsPrestack** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Pseudofunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat →   
    CategoryTheory.GrothendieckTopology C → Prop
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
satisfies the descent property for morphisms, i.e. is a prestack.
(See the terminological note in the introduction of the file `Sites.Descent.IsPr
estack`.)
-/
class IsPrestack (J : GrothendieckTopology C) : Prop where
  isSheaf (J) {S : C} (M N : F.obj (.mk (op S))) :
    Presheaf.IsSheaf (J.over S) (F.presheafHom M N)

/-- If `F` is a prestack from `Cᵒᵖ` to `Cat` relatively to a Grothendieck topology `J`,
and `M` and `N` are two objects in `F.obj (.mk (op S))`, this is the sheaf of
morphisms from `M` to `N`: it sends an object `T : Over S` corresponding to
a morphism `p : X ⟶ S` to the type of morphisms $p^* M ⟶ p^* N$. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.sheafHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Pseudofunctor`。
形式化陈述：sheafHom (J : GrothendieckTopology C) [F.IsPrestack J] {S : C} (M N : F.ob
j (.mk (op S))) : Sheaf (J.over S) (Type v') where obj
参数：J : GrothendieckTopology C；M N : F.obj (.mk (op S))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.IsPrestack.isSheaf`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C}   {F : CategoryTheory.Pseudofunctor (CategoryT
heory.LocallyDiscrete Cᵒᵖ) CategoryTh…

--- 原说明 ---
If `F` is a prestack from `Cᵒᵖ` to `Cat` relatively to a Grothendieck topology `
J`,
and `M` and `N` are two objects in `F.obj (.mk (op S))`, this is the sheaf of
morphisms from `M` to `N`: it sends an object `T : Over S` corresponding to
a morphism `p : X ⟶ S` to the type of morphisms $p^* M ⟶ p^* N$.
-/
def sheafHom (J : GrothendieckTopology C) [F.IsPrestack J]
    {S : C} (M N : F.obj (.mk (op S))) :
    Sheaf (J.over S) (Type v') where
  obj := F.presheafHom M N
  property := IsPrestack.isSheaf _ _ _

end Pseudofunctor

end CategoryTheory

