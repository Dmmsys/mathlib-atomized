/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and a family of maps `f i : X i ⟶ S` in the category `C`,
we define the category `F.DescentData f` of objects over the `X i`
equipped with descent data relative to the morphisms `f i : X i ⟶ S`.

We show that up to an equivalence, the category `F.DescentData f` is unchanged
when we replace `S` by an isomorphic object, or the family `f i : X i ⟶ S`
by another family which generates the same sieve
(see `Pseudofunctor.DescentData.pullFunctorEquivalence`).

Given a presieve `R`, we introduce predicates `F.IsPrestackFor R` and `F.IsStackFor R`
saying the functor `F.DescentData (fun (f : R.category) ↦ f.obj.hom)` attached
to `R` is respectively fully faithful or an equivalence. We show that
`F` satisfies `F.IsPrestack J` for a Grothendieck topology `J` iff it
satisfies `F.IsPrestackFor R.arrows` for all covering sieves `R`.

## TODO (@joelriou, @chrisflav)
* Introduce multiple variants of `DescentData` (when `C` has pullbacks,
  when `F` also has a covariant functoriality, etc.).

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe t t' t'' v' v u' u

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, and a family of
morphisms `f i : X i ⟶ S`, the objects of the category of descent data for
the `X i` relative to the morphisms `f i` consist of families of
objects `obj i` in `F.obj (.mk (op (X i)))` together with morphisms `hom`
between the pullbacks of `obj i₁` and `obj i₂` over any object `Y` which maps
to both `X i₁` and `X i₂` (in a way that is compatible with the morphisms to `S`).
The compatibilities these morphisms satisfy imply that the morphisms `hom` are isomorphisms. -/
/-
**CategoryTheory.Pseudofunctor.DescentData** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Pseudofunctor`。
形式化陈述：DescentData where /-- The objects over `X i` for all `i` -/ obj (i : ι) : 
F.obj (.mk (op (X i))) /-- The compatibility morphisms after pullbacks. It follo
ws from the conditions `hom_self` and `hom_comp` that these are isomorphisms, se
e `CategoryTheory.Pseudofunctor.DescentData.iso` below. -/ hom ⦃Y : C⦄ (q : Y ⟶ 
S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (_hf₁ : f₁ ≫ f i₁ = q
参数：i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, and a family of
morphisms `f i : X i ⟶ S`, the objects of the category of descent data for
the `X i` relative to the morphisms `f i` consist of families of
objects `obj i` in `F.obj (.mk (op (X i)))` together with morphisms `hom`
between the pullbacks of `obj i₁` and `obj i₂` over any object `Y` which maps
to both `X i₁` and `X i₂` (in a way that is compatible with the morphisms to `S`
).
The compatibilities these morphisms satisfy imply that the morphisms `hom` are i
somorphisms.
-/
structure DescentData where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pullbacks. It follows from the conditions
  `hom_self` and `hom_comp` that these are isomorphisms, see
  `CategoryTheory.Pseudofunctor.DescentData.iso` below. -/
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
      (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
  pullHom_hom ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
      pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂ := by cat_disch
  hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) :
      hom q g g = 𝟙 _ := by cat_disch
  hom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
      hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃ := by cat_disch

namespace DescentData

variable {F f} (D : F.DescentData f)

attribute [local simp] hom_self pullHom_hom
attribute [reassoc (attr := simp)] hom_comp

/-- The morphisms `DescentData.hom`, as isomorphisms. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.iso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Pseudofunctor.DescentData`。
形式化陈述：iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (_hf₁ 
: f₁ ≫ f i₁ = q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms `DescentData.hom`, as isomorphisms.
-/
def iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁) ≅
      (F.map f₂.op.toLoc).toFunctor.obj (D.obj i₂) where
  hom := D.hom q f₁ f₂
  inv := D.hom q f₂ f₁
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (D.hom q f₁ f₂ hf₁ hf₂) :=
  (D.iso q f₁ f₂).isIso_hom

/-- The type of morphisms in the category `Pseudofunctor.DescentData`. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentData.Hom** 是 Mathlib 中的一个结构，位于命名空间 `Catego
ryTheory.Pseudofunctor.DescentData`。
形式化陈述：Hom (D₁ D₂ : F.DescentData f) where /-- The morphisms between the `obj` fi
elds of descent data. -/ hom (i : ι) : D₁.obj i ⟶ D₂.obj i comm ⦃Y : C⦄ (q : Y ⟶
 S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ 
≫ f i₂ = q) : (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ = D₁.h
om q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂)
参数：D₁ D₂ : F.DescentData f；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Pseudofunctor.DescentData`.
-/
structure Hom (D₁ D₂ : F.DescentData f) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := local simp)] Hom.comm
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (F.DescentData f) where
  Hom := Hom
  id D := { hom _ := 𝟙 _ }
  comp φ φ' := { hom i := φ.hom i ≫ φ'.hom i }

@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentData.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Pseudofunctor.DescentData`。
形式化陈述：hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂} (h : forall i, φ.hom i 
= φ'.hom i) : φ = φ'
参数：h : forall i, φ.hom i = φ'.hom i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.DescentData.Hom.ext`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C}   {F : CategoryTheory.Pseudofunctor (Category
Theory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
/-
**CategoryTheory.Pseudofunctor.DescentData.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Pseudofunctor.DescentData`。
形式化陈述：id_hom (D : F.DescentData f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _
参数：D : F.DescentData f；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (D : F.DescentData f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：comp_hom {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι)
 : (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i
参数：φ : D₁ ⟶ D₂；φ' : D₂ ⟶ D₃；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a family of morphisms `f : X i ⟶ S`, and `M : F.obj (.mk (op S))`,
this is the object in `F.DescentData f` that is obtained by pulling back `M`
over the `X i`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.ofObj** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pseudofunctor.DescentData`。
形式化陈述：ofObj (M : F.obj (.mk (op S))) : F.DescentData f where obj i
参数：M : F.obj (.mk (op S))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
Given a family of morphisms `f : X i ⟶ S`, and `M : F.obj (.mk (op S))`,
this is the object in `F.DescentData f` that is obtained by pulling back `M`
over the `X i`.
-/
def ofObj (M : F.obj (.mk (op S))) : F.DescentData f where
  obj i := (F.map (f i).op.toLoc).toFunctor.obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    simp only [pullHom, Functor.map_comp, Category.assoc,
      F.mapComp'₀₁₃_inv_app (f i₁).op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
        gf₁.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind),
      F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (f i₂).op.toLoc f₂.op.toLoc g.op.toLoc
      q.op.toLoc gf₂.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind)]

/-- Constructor for isomorphisms in `Pseudofunctor.DescentData`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pseudofunctor.DescentData`。
形式化陈述：isoMk {D₁ D₂ : F.DescentData f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i) 
(comm : forall ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (
hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q), (F.map f₁.op.toLoc).toFunctor.map (e
 i₁).hom ≫ D₂.hom q f₁ f₂ = D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (
e i₂).hom
参数：e : forall (i : ι), D₁.obj i ≅ D₂.obj i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `Pseudofunctor.DescentData`.
-/
def isoMk {D₁ D₂ : F.DescentData f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
      D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) : D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (e i₂).hom), Category.assoc,
          Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
          ← cancel_epi ((F.map f₁.op.toLoc).toFunctor.map (e i₁).hom),
          Iso.map_hom_inv_id_assoc, comm q f₁ f₂ hf₁ hf₂] }

end DescentData

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.toDescentData** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Pseudofunctor`。
形式化陈述：toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`.
-/
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f where
  obj M := .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).toFunctor.map φ }

namespace DescentData

section

variable {F f} {S' : C} {p : S' ⟶ S} {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- Auxiliary definition for `pullFunctor`. -/
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorObjHom** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorObjHom (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ 
(f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂) (hf₁ : f₁ ≫ f' j₁ = q
参数：D : F.DescentData f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `pullFunctor`.
-/
def pullFunctorObjHom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj ((F.map (p' j₁).op.toLoc).toFunctor.obj (D.obj (α j₁))) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj ((F.map (p' j₂).op.toLoc).toFunctor.obj (D.obj (α j₂))) :=
  (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

set_option backward.isDefEq.respectTransparency false in -- Needed below.
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorObjHom_eq** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorObjHom_eq (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι
'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂) (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y 
⟶ X (α j₂)) (hf₁ : f₁ ≫ f' j₁ = q
参数：D : F.DescentData f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp`：∀ {B : Type u₁} [inst 
: CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory
 C]   (F : CategoryTheory.Pseudofuncto…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullFunctorObjHom_eq (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch)
    (hq' : q ≫ p = q' := by cat_disch)
    (hf₁' : f₁ ≫ p' j₁ = f₁' := by cat_disch)
    (hf₂' : f₂ ≫ p' j₂ = f₂' := by cat_disch) :
  pullFunctorObjHom w D q f₁ f₂ =
    (F.mapComp' _ _ _).inv.toNatTrans.app _ ≫ D.hom q' f₁' f₂'
      (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
      (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
      (F.mapComp' _ _ _).hom.toNatTrans.app _ := by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `pullFunctor`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorObj (D : F.DescentData f) : F.DescentData f' where obj j
参数：D : F.DescentData f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `pullFunctor`.
-/
def pullFunctorObj (D : F.DescentData f) :
    F.DescentData f' where
  obj j := (F.map (p' _).op.toLoc).toFunctor.obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
    rw [← D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq])
      (f₁ ≫ p' j₁) (f₂ ≫ p' j₂) (by rw [Category.assoc, w, reassoc_of% hf₁])
      (by rw [Category.assoc, w, reassoc_of% hf₂]) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by cat_disch) (by cat_disch)]
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by cat_disch),
      mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]
  hom_self Y q j g hg := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl,
      D.hom_self _ _ (by cat_disch)]
    simp
  hom_comp Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₂ ≫ p' j₂) (f₃ ≫ p' j₃),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₃ ≫ p' j₃)]
    simp

variable (F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a family of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, and suitable
commutative diagrams `p' j ≫ f (α j) = f' j ≫ p`, this is the
induced functor `F.DescentData f ⥤ F.DescentData f'`. (Up to a (unique) isomorphism,
this functor only depends on `f` and `f'`, see `pullFunctorIso`.) -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctor : F.DescentData f ⥤ F.DescentData f' where obj D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, and suitable
commutative diagrams `p' j ≫ f (α j) = f' j ≫ p`, this is the
induced functor `F.DescentData f ⥤ F.DescentData f'`. (Up to a (unique) isomorph
ism,
this functor only depends on `f` and `f'`, see `pullFunctorIso`.)
-/
def pullFunctor : F.DescentData f ⥤ F.DescentData f' where
  obj D := pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).toFunctor.map (φ.hom (α j))
      comm Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by rw [Category.assoc, w, reassoc_of% hf₁])
          (by rw [Category.assoc, w, reassoc_of% hf₂])
        dsimp at this ⊢
        rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂),
          pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
        dsimp
        rw [mapComp'_inv_naturality_assoc, ← mapComp'_hom_naturality,
          reassoc_of% this] }

set_option backward.isDefEq.respectTransparency false in
/-- Given families of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, suitable
commutative diagrams `w j : p' j ≫ f (α j) = f' j ≫ p`, this is the natural
isomorphism between the descent data relative to `f'` that are obtained either:
* by considering the obvious descent data relative to `f` given by an object `M : F.obj (op S)`,
  followed by the application of `pullFunctor F w : F.DescentData f ⥤ F.DescentData f'`;
* by considering the obvious descent data relative to `f'` given by pulling
  back the object `M` to `S'`.
-/
/-
**CategoryTheory.Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：toDescentDataCompPullFunctorIso : F.toDescentData f ⋙ pullFunctor F w ≅ (F
.map p.op.toLoc).toFunctor ⋙ F.toDescentData f'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given families of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, suitable
commutative diagrams `w j : p' j ≫ f (α j) = f' j ≫ p`, this is the natural
isomorphism between the descent data relative to `f'` that are obtained either:
* by considering the obvious descent data relative to `f` given by an object `M 
: F.obj (op S)`,
  followed by the application of `pullFunctor F w : F.DescentData f ⥤ F.DescentD
ata f'`;
* by considering the obvious descent data relative to `f'` given by pulling
  back the object `M` to `S'`.
-/
def toDescentDataCompPullFunctorIso :
    F.toDescentData f ⋙ pullFunctor F w ≅ (F.map p.op.toLoc).toFunctor ⋙ F.toDescentData f' :=
  NatIso.ofComponents
    (fun M ↦ isoMk (fun i ↦ (Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        dsimp
        rw [F.isoMapOfCommSq_eq _ _ rfl, F.isoMapOfCommSq_eq _ _ rfl]
        dsimp
        simp only [Functor.map_comp, Category.assoc]
        rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc p.op.toLoc
            (f' i₁).op.toLoc f₁.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M,
          pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' i₁) (f₂ ≫ p' i₂),
          ← cancel_mono ((F.mapComp' (f' i₂).op.toLoc f₂.op.toLoc q.op.toLoc
            (by grind)).inv.toNatTrans.app _)]
        dsimp
        simp only [Category.assoc,
          ← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app p.op.toLoc
            (f' i₂).op.toLoc f₂.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M,
          ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₁)).op.toLoc
            (p' i₁).op.toLoc f₁.op.toLoc (p.op.toLoc ≫ (f' i₁).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M,
          F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₂)).op.toLoc
            (p' i₂).op.toLoc f₂.op.toLoc (p.op.toLoc ≫ (f' i₂).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M]
        simp))
    (fun f ↦ by
      ext i
      exact (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc).inv.toNatTrans.naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- Up to a (unique) isomorphism, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` does not depend
on the auxiliary data. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorIso {β : ι' -> ι} {p'' : forall j, X' j ⟶ X (β j)} (w' : forall
 j, p'' j ≫ f (β j) = f' j ≫ p) : pullFunctor F w ≅ pullFunctor F w'
参数：β j；w' : forall j, p'' j ≫ f (β j) = f' j ≫ p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to a (unique) isomorphism, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` does not depend
on the auxiliary data.
-/
def pullFunctorIso {β : ι' → ι} {p'' : ∀ j, X' j ⟶ X (β j)}
    (w' : ∀ j, p'' j ≫ f (β j) = f' j ≫ p) :
    pullFunctor F w ≅ pullFunctor F w' :=
  NatIso.ofComponents (fun D ↦ isoMk (fun j ↦ D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch),
      map_eq_pullHom_assoc _ _ (f₁ ≫ p' j₁) (f₁ ≫ p'' j₁) (by cat_disch) (by cat_disch),
      map_eq_pullHom _ _ (f₂ ≫ p' j₂) (f₂ ≫ p'' j₂) (by cat_disch) (by cat_disch)]
    simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.assoc]
    rw [pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₁]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc,
      pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₂]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc]))
    (fun φ ↦ by
      ext j
      exact φ.comm _ _ _ rfl (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- The functor `F.DescentData f ⥤ F.DescentData f` corresponding to `pullFunctor`
applied to identity morphisms is isomorphic to the identity functor. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorIdIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorIdIso : pullFunctor F (p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.DescentData f ⥤ F.DescentData f` corresponding to `pullFunctor`
applied to identity morphisms is isomorphic to the identity functor.
-/
def pullFunctorIdIso :
    pullFunctor F (p := 𝟙 S) (p' := fun _ ↦ 𝟙 _) (w := by simp) ≅ 𝟭 (F.DescentData f) :=
  NatIso.ofComponents (fun D ↦ isoMk (fun i ↦ (Cat.Hom.toNatIso (F.mapId _)).app _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ q f₁ f₂ rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of two functors `pullFunctor` is isomorphic to `pullFunctor` applied
to the compositions. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorCompIso** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorCompIso {S'' : C} {q : S'' ⟶ S'} {ι'' : Type t''} {X'' : ι'' ->
 C} {f'' : forall k, X'' k ⟶ S''} {β : ι'' -> ι'} {q' : forall k, X'' k ⟶ X' (β 
k)} (w' : forall k, q' k ≫ f' (β k) = f'' k ≫ q) (r : S'' ⟶ S) {r' : forall k, X
'' k ⟶ X (α (β k))} (hr : q ≫ p = r
参数：β k；w' : forall k, q' k ≫ f' (β k) = f'' k ≫ q；r : S'' ⟶ S；α (β k)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…

--- 原说明 ---
The composition of two functors `pullFunctor` is isomorphic to `pullFunctor` app
lied
to the compositions.
-/
def pullFunctorCompIso
    {S'' : C} {q : S'' ⟶ S'} {ι'' : Type t''} {X'' : ι'' → C} {f'' : ∀ k, X'' k ⟶ S''}
    {β : ι'' → ι'} {q' : ∀ k, X'' k ⟶ X' (β k)} (w' : ∀ k, q' k ≫ f' (β k) = f'' k ≫ q)
    (r : S'' ⟶ S) {r' : ∀ k, X'' k ⟶ X (α (β k))}
    (hr : q ≫ p = r := by cat_disch) (hr' : ∀ k, q' k ≫ p' (β k) = r' k := by cat_disch) :
    pullFunctor F w ⋙ pullFunctor F w' ≅
      pullFunctor F (p := r) (α := α ∘ β) (p' := r') (fun k ↦ by
        dsimp
        rw [← hr', Category.assoc, w, reassoc_of% w', hr]) :=
  NatIso.ofComponents
    (fun D ↦ isoMk (fun _ ↦ (Cat.Hom.toNatIso (F.mapComp' _ _ _ (by grind))).symm.app _) (by
      intro Y s k₁ k₂ f₁ f₂ hf₁ hf₂
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) _ _ rfl,
        pullFunctorObjHom_eq _ _ _ _ _ (s ≫ q) (f₁ ≫ q' k₁) (f₂ ≫ q' k₂)]
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) (f₁ ≫ r' k₁) (f₂ ≫ r' k₂)
        rfl (by simp [w', reassoc_of% hf₁, reassoc_of% hf₂]) (by
          simp [reassoc_of% w', reassoc_of% hf₁, hr])]
      dsimp
      simp only [Category.assoc]
      rw [mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc _ _ _ _ _ _ _
        (by grind) rfl rfl, mapComp'₀₂₃_hom_app _ _ _ _ _ _ _ _ rfl rfl]))

end

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-- Up to an equivalence, the category `DescentData` for a pseudofunctor `F` and
a family of morphisms `f : X i ⟶ S` is unchanged when we replace `S` by an isomorphic object,
or when we replace `f` by another family which generate the same sieve. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullFunctorEquivalence** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：pullFunctorEquivalence {S' : C} {ι' : Type t'} {X' : ι' -> C} {f' : forall
 j, X' j ⟶ S'} (e : S' ≅ S) {α : ι' -> ι} {p' : forall j, X' j ⟶ X (α j)} (w : f
orall j, p' j ≫ f (α j) = f' j ≫ e.hom) {β : ι -> ι'} {q' : forall i, X i ⟶ X' (
β i)} (w' : forall i, q' i ≫ f' (β i) = f i ≫ e.inv) : F.DescentData f ≌ F.Desce
ntData f' where functor
参数：e : S' ≅ S；α j；w : forall j, p' j ≫ f (α j) = f' j ≫ e.hom；β i；w' : forall i,
 q' i ≫ f' (β i) = f i ≫ e.inv。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …

--- 原说明 ---
Up to an equivalence, the category `DescentData` for a pseudofunctor `F` and
a family of morphisms `f : X i ⟶ S` is unchanged when we replace `S` by an isomo
rphic object,
or when we replace `f` by another family which generate the same sieve.
-/
def pullFunctorEquivalence {S' : C} {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}
    (e : S' ≅ S) {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ e.hom)
    {β : ι → ι'} {q' : ∀ i, X i ⟶ X' (β i)} (w' : ∀ i, q' i ≫ f' (β i) = f i ≫ e.inv) :
    F.DescentData f ≌ F.DescentData f' where
  functor := pullFunctor F w
  inverse := pullFunctor F w'
  unitIso :=
    (pullFunctorIdIso F S).symm ≪≫ pullFunctorIso _ _ _ ≪≫
      (pullFunctorCompIso _ _ _ _ e.inv_hom_id (fun _ ↦ rfl)).symm
  counitIso :=
    pullFunctorCompIso _ _ _ _ e.hom_inv_id (fun _ ↦ rfl) ≪≫
      pullFunctorIso _ _ _ ≪≫ pullFunctorIdIso F S'
  functor_unitIso_comp D := by
    ext j
    dsimp
    simp only [Category.id_comp, Functor.map_comp, Category.assoc]
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (p' _ ≫ f _) (p' _ ≫ q' _ ≫ p' _) (p' _) (by simp)
        (by simp [w', reassoc_of% w]),
      map_eq_pullHom_assoc _ (p' j) (p' j) (p' _ ≫ q' _ ≫ p' _) (by simp) (by simp),
      D.pullHom_hom _ _ (p' j ≫ f _) (by simp) _ _ (by simp)
        (by simp [w, reassoc_of% w']) _ _ (by simp) rfl]
    dsimp
    rw [← F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc _ _ _ _ _ _ rfl rfl (by simp),
      mapComp'_comp_id_hom_app, mapComp'_id_comp_inv_app_assoc, ← Functor.map_comp_assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app]
    simp [D.hom_self _ _ rfl]
/-
**CategoryTheory.Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：exists_equivalence_of_sieve_eq {ι' : Type t'} {X' : ι' -> C} (f' : forall 
i', X' i' ⟶ S) (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') : exists (e : F.De
scentData f ≌ F.DescentData f'), Nonempty (F.toDescentData f ⋙ e.functor ≅ F.toD
escentData f')
参数：f' : forall i', X' i' ⟶ S；h : Sieve.ofArrows _ f = Sieve.ofArrows _ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma exists_equivalence_of_sieve_eq
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    ∃ (e : F.DescentData f ≌ F.DescentData f'),
      Nonempty (F.toDescentData f ⋙ e.functor ≅ F.toDescentData f') := by
  have h₁ (i' : ι') : ∃ (i : ι) (g' : X' i' ⟶ X i), g' ≫ f i = f' i' := by
    obtain ⟨_, _, _, ⟨i⟩, fac⟩ : Sieve.ofArrows X f (f' i') := by
      rw [h]; apply Sieve.ofArrows_mk
    exact ⟨i, _, fac⟩
  have h₂ (i : ι) : ∃ (i' : ι') (g : X i ⟶ X' i'), g ≫ f' i' = f i := by
    obtain ⟨_, _, _, ⟨i'⟩, fac⟩ : Sieve.ofArrows X' f' (f i) := by
      rw [← h]; apply Sieve.ofArrows_mk
    exact ⟨i', _, fac⟩
  choose α p' w using h₁
  choose β q' w' using h₂
  exact ⟨pullFunctorEquivalence (p' := p') (q' := q') F (Iso.refl _)
    (by cat_disch) (by cat_disch), ⟨toDescentDataCompPullFunctorIso _ _ ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _⟩⟩
/-
**CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_toDescentData_
iff_of_sieve_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentD
ata`。
形式化陈述：nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq {ι : Type t} {S : C} 
{X : ι -> C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' -> C} (f' : forall 
i', X' i' ⟶ S) (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') : Nonempty (F.toDe
scentData f).FullyFaithful ↔ Nonempty (F.toDescentData f').FullyFaithful
参数：f : forall i, X i ⟶ S；f' : forall i', X' i' ⟶ S；h : Sieve.ofArrows _ f = Siev
e.ofArrows _ f'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq`
：exists_equivalence_of_sieve_eq {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X
' i' ⟶ S) (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') : ex…
-/
lemma nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    Nonempty (F.toDescentData f).FullyFaithful ↔
      Nonempty (F.toDescentData f').FullyFaithful := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  exact ⟨fun ⟨h⟩ ↦ ⟨(h.comp e.fullyFaithfulFunctor).ofIso iso⟩,
    fun ⟨h⟩ ↦ ⟨(h.comp e.fullyFaithfulInverse).ofIso iso.symm.compInverseIso⟩⟩
/-
**CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_si
eve_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：isEquivalence_toDescentData_iff_of_sieve_eq {ι : Type t} {S : C} {X : ι ->
 C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X' i'
 ⟶ S) (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') : (F.toDescentData f).IsEqu
ivalence ↔ (F.toDescentData f').IsEquivalence
参数：f : forall i, X i ⟶ S；f' : forall i', X' i' ⟶ S；h : Sieve.ofArrows _ f = Siev
e.ofArrows _ f'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq`
：exists_equivalence_of_sieve_eq {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X
' i' ⟶ S) (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') : ex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.isEquivalence_iff_of_iso`：isEquivalence_iff_of_is
o {F G : C ⥤ D} (e : F ≅ G) : F.IsEquivalence ↔ G.IsEquivalence
· 使用定理 `CategoryTheory.Functor.isEquivalence_trans`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_comp_right`：isEquivalence_of_com
p_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence G] [IsE
quivalence (F ⋙ G)] : IsEquivalence F
-/
lemma isEquivalence_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    (F.toDescentData f).IsEquivalence ↔ (F.toDescentData f').IsEquivalence := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ Functor.isEquivalence_of_comp_right _ e.functor⟩

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms between objects in the image of the functor `F.toDescentData f`
identify to compatible families of sections of the presheaf `F.presheafHom M N` on
the object `Over.mk (𝟙 S)`, relatively to the family of morphisms in `Over S`
corresponding to the family `f`. -/
/-
**CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
形式化陈述：subtypeCompatibleHomEquiv {M N : F.obj (.mk (op S))} : Subtype (Presieve.A
rrows.Compatible (F.presheafHom M N) (X
参数：.mk (op S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms between objects in the image of the functor `F.toDescentData f`
identify to compatible families of sections of the presheaf `F.presheafHom M N` 
on
the object `Over.mk (𝟙 S)`, relatively to the family of morphisms in `Over S`
corresponding to the family `f`.
-/
def subtypeCompatibleHomEquiv {M N : F.obj (.mk (op S))} :
    Subtype (Presieve.Arrows.Compatible (F.presheafHom M N)
      (X := fun i ↦ Over.mk (f i)) (B := Over.mk (𝟙 S)) (fun i ↦ Over.homMk (f i))) ≃
    ((F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) where
  toFun φ :=
    { hom := φ.val
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.property i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂) (by cat_disch)
        simp_all [map_eq_pullHom] }
  invFun g :=
    { val := g.hom
      property i₁ i₂ Z f₁ f₂ h := by
        simpa [map_eq_pullHom (g.hom i₁) f₁.left Z.hom Z.hom (Over.w f₁) (Over.w f₁),
          map_eq_pullHom (g.hom i₂) f₂.left Z.hom Z.hom (Over.w f₂) (Over.w f₂),
          cancel_epi, cancel_mono] using g.comm Z.hom f₁.left f₂.left (Over.w f₁) (Over.w f₂) }

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv_toCompatibl
e_presheafHomObjHomEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor
.DescentData`。
形式化陈述：subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv {M N : F.obj
 (.mk (op S))} (φ : M ⟶ N) : subtypeCompatibleHomEquiv F f (Presieve.Arrows.toCo
mpatible _ _ (F.presheafHomObjHomEquiv φ)) = (F.toDescentData f).map φ
参数：.mk (op S)；φ : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.hom_ext`：hom_ext {D₁ D₂ : F.Des
centData f} {φ φ' : D₁ ⟶ D₂} (h : forall i, φ.hom i = φ'.hom i) : φ = φ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Pseudofunctor.mapComp'`：mapComp'_hom_naturality : (F.map 
fg).toFunctor.map a ≫ (F.mapComp' f g fg hfg).hom.toNatTrans.app Y = (F.mapComp'
 f g fg hfg).hom.toNatTrans…
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp_inv_app`：∀ {B : Type u_1} 
[inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.Strict 
B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `CategoryTheory.locallyDiscreteBicategory.strict`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C],   CategoryTheory.Bicategory.Strict (CategoryT
heory.LocallyDiscrete C)
· 使用定理 `CategoryTheory.Pseudofunctor.mapComp'_id_comp_hom_app_assoc`：∀ {B : Type
 u_1} [inst : CategoryTheory.Bicategory B] [inst_1 : CategoryTheory.Bicategory.S
trict B]   (F : CategoryTheory.Pseudofunctor B Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app`：inv_hom_id_toNatTrans_
app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) : e.inv.toNatTrans.app 
A ≫ e.hom.toNatTrans.app A = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app_assoc`：∀ {X Y : Categor
yTheory.Cat} {F G : X ⟶ Y} (e : F ≅ G) (A : ↑X) {Z : ↑Y} (h : G.toFunctor.obj A 
⟶ Z),   CategoryTheory.CategoryStruct.comp (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv
    {M N : F.obj (.mk (op S))} (φ : M ⟶ N) :
    subtypeCompatibleHomEquiv F f (Presieve.Arrows.toCompatible _ _
      (F.presheafHomObjHomEquiv φ)) = (F.toDescentData f).map φ := by
  ext i
  simp [subtypeCompatibleHomEquiv, presheafHomObjHomEquiv, pullHom,
    ← Functor.map_comp, Pseudofunctor.mapComp'_id_comp_hom_app_assoc,
    Pseudofunctor.mapComp'_id_comp_inv_app]

end DescentData

/-- The condition that a pseudofunctor satisfies the descent of morphisms
relative to a presieve. -/
@[mk_iff]
/-
**CategoryTheory.Pseudofunctor.IsPrestackFor** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Pseudofunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat →   
    {S : C} → CategoryTheory.Presieve S → Prop
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a pseudofunctor satisfies the descent of morphisms
relative to a presieve.
-/
structure IsPrestackFor (R : Presieve S) : Prop where
  nonempty_fullyFaithful :
    Nonempty (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).FullyFaithful

variable {F} in
/-- If `R` is a presieve such that `F.IsPrestackFor R`, then the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)` is fully faithful. -/
/-
**CategoryTheory.Pseudofunctor.IsPrestackFor.fullyFaithful** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Pseudofunctor.IsPrestackFor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat
} →       {S : C} → {R : CategoryTheory.Presieve S} → F.IsPrestackFor R → (F.toD
escentData fun f => f.obj.hom).FullyFaithful
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；F.toDescentData fun f => f.obj.hom。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.IsPrestackFor.nonempty_fullyFaithful`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Pseudo
functor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…

--- 原说明 ---
If `R` is a presieve such that `F.IsPrestackFor R`, then the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)` is fully faithful.
-/
noncomputable def IsPrestackFor.fullyFaithful {R : Presieve S} (hF : F.IsPrestackFor R) :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).FullyFaithful :=
  hF.nonempty_fullyFaithful.some
/-
**CategoryTheory.Pseudofunctor.isPrestackFor_iff_of_sieve_eq** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isPrestackFor_iff_of_sieve_eq {R R' : Presieve S} (h : Sieve.generate R = 
Sieve.generate R') : F.IsPrestackFor R ↔ F.IsPrestackFor R'
参数：h : Sieve.generate R = Sieve.generate R'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Pres
ieve X) : exists (ι : Type (max u₁ v₁)) (Y : ι -> C) (f : forall i, Y i ⟶ X), R 
= .ofArrows Y f
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_toDescen
tData_iff_of_sieve_eq`：nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq {ι :
 Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' ->
 C}…
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isPrestackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsPrestackFor R ↔ F.IsPrestackFor R' := by
  simp only [isPrestackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
/-
**CategoryTheory.Pseudofunctor.IsPrestackFor_generate_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：IsPrestackFor_generate_iff (R : Presieve S) : F.IsPrestackFor (Sieve.gener
ate R).arrows ↔ F.IsPrestackFor R
参数：R : Presieve S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.isPrestackFor_iff_of_sieve_eq`：isPrestackFo
r_iff_of_sieve_eq {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R')
 : F.IsPrestackFor R ↔ F.IsPrestackFor R'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPrestackFor_generate_iff (R : Presieve S) :
    F.IsPrestackFor (Sieve.generate R).arrows ↔ F.IsPrestackFor R :=
  F.isPrestackFor_iff_of_sieve_eq (by simp)
/-
**CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isPrestackFor_ofArrows_iff : F.IsPrestackFor (Presieve.ofArrows _ f) ↔ Non
empty (F.toDescentData f).FullyFaithful
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.nonempty_fullyFaithful_toDescen
tData_iff_of_sieve_eq`：nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq {ι :
 Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' ->
 C}…
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
-/
lemma isPrestackFor_ofArrows_iff :
    F.IsPrestackFor (Presieve.ofArrows _ f) ↔
      Nonempty (F.toDescentData f).FullyFaithful := by
  simp only [isPrestackFor_iff]
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

/-- The condition that a pseudofunctor has effective descent
relative to a presieve. -/
@[mk_iff]
/-
**CategoryTheory.Pseudofunctor.IsStackFor** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Pseudofunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat →   
    {S : C} → CategoryTheory.Presieve S → Prop
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a pseudofunctor has effective descent
relative to a presieve.
-/
structure IsStackFor (R : Presieve S) : Prop where
  isEquivalence :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).IsEquivalence

variable {F} in
/-
**CategoryTheory.Pseudofunctor.IsStackFor.isPrestackFor** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Pseudofunctor.IsStackFor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTh
eory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat} {S :
 C}   {R : CategoryTheory.Presieve S}, F.IsStackFor R → F.IsPrestackFor R
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.isStackFor_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C]   (F : CategoryTheory.Pseudofunctor (CategoryTheor
y.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma IsStackFor.isPrestackFor {R : Presieve S} (h : F.IsStackFor R) :
    F.IsPrestackFor R where
  nonempty_fullyFaithful := ⟨by
    rw [isStackFor_iff] at h
    exact .ofFullyFaithful _⟩

variable {F} in
/-
**CategoryTheory.Pseudofunctor.IsStackFor.essSurj** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Pseudofunctor.IsStackFor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTh
eory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat} {S :
 C}   {R : CategoryTheory.Presieve S}, F.IsStackFor R → (F.toDescentData fun f =
> f.obj.hom).EssSurj
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；F.toDescentData fun f => f.obj.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.IsStackFor.isEquivalence`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Pseudofunctor (Cat
egoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma IsStackFor.essSurj {R : Presieve S} (h : F.IsStackFor R) :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).EssSurj := by
  have := h.isEquivalence
  infer_instance
/-
**CategoryTheory.Pseudofunctor.isStackFor_iff_of_sieve_eq** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isStackFor_iff_of_sieve_eq {R R' : Presieve S} (h : Sieve.generate R = Sie
ve.generate R') : F.IsStackFor R ↔ F.IsStackFor R'
参数：h : Sieve.generate R = Sieve.generate R'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Pres
ieve X) : exists (ι : Type (max u₁ v₁)) (Y : ι -> C) (f : forall i, Y i ⟶ X), R 
= .ofArrows Y f
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_iff
_of_sieve_eq`：isEquivalence_toDescentData_iff_of_sieve_eq {ι : Type t} {S : C} {
X : ι -> C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' -> C} (f' : fo…
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isStackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsStackFor R ↔ F.IsStackFor R' := by
  simp only [isStackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
/-
**CategoryTheory.Pseudofunctor.IsStackFor_generate_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：IsStackFor_generate_iff (R : Presieve S) : F.IsStackFor (Sieve.generate R)
.arrows ↔ F.IsStackFor R
参数：R : Presieve S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.isStackFor_iff_of_sieve_eq`：isStackFor_iff_
of_sieve_eq {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') : F.I
sStackFor R ↔ F.IsStackFor R'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStackFor_generate_iff (R : Presieve S) :
    F.IsStackFor (Sieve.generate R).arrows ↔ F.IsStackFor R :=
  F.isStackFor_iff_of_sieve_eq (by simp)
/-
**CategoryTheory.Pseudofunctor.isStackFor_ofArrows_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Pseudofunctor`。
形式化陈述：isStackFor_ofArrows_iff : F.IsStackFor (Presieve.ofArrows _ f) ↔ (F.toDesc
entData f).IsEquivalence
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_iff
_of_sieve_eq`：isEquivalence_toDescentData_iff_of_sieve_eq {ι : Type t} {S : C} {
X : ι -> C} (f : forall i, X i ⟶ S) {ι' : Type t'} {X' : ι' -> C} (f' : fo…
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
-/
lemma isStackFor_ofArrows_iff :
    F.IsStackFor (Presieve.ofArrows _ f) ↔
      (F.toDescentData f).IsEquivalence := by
  simp only [isStackFor_iff]
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

variable {F} in
/-
**CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：bijective_toDescentData_map_iff (M N : F.obj (.mk (op S))) : Function.Bije
ctive ((F.toDescentData f).map : (M ⟶ N) -> _) ↔ Presieve.IsSheafFor (F.presheaf
Hom M N) (X
参数：M N : F.obj (.mk (op S))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible`：
isSheafFor_ofArrows_iff_bijective_toCompabible : IsSheafFor P (ofArrows X π) ↔ F
unction.Bijective (Arrows.toCompatible P π)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Pseudofunctor.DescentData.subtypeCompatibleHomEquiv_toCom
patible_presheafHomObjHomEquiv`：subtypeCompatibleHomEquiv_toCompatible_presheafH
omObjHomEquiv {M N : F.obj (.mk (op S))} (φ : M ⟶ N) : subtypeCompatibleHomEquiv
 F f (Presie…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bijective_toDescentData_map_iff (M N : F.obj (.mk (op S))) :
    Function.Bijective ((F.toDescentData f).map : (M ⟶ N) → _) ↔
  Presieve.IsSheafFor (F.presheafHom M N) (X := Over.mk (𝟙 S))
    (Presieve.ofArrows (Y := fun i ↦ Over.mk (f i)) (fun i ↦ Over.homMk (f i))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← (DescentData.subtypeCompatibleHomEquiv F f).bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (presheafHomObjHomEquiv F).bijective]
  convert! Iff.rfl
  ext φ : 1
  apply DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isPrestackFor_iff_isSheafFor {S : C} (R : Sieve S) : F.IsPrestackFor R.arr
ows ↔ forall (M N : F.obj (.mk (op S))), Presieve.IsSheafFor (P
参数：R : Sieve S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.isPrestackFor_iff`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Pseudofunctor (CategoryTh
eory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用引理 `CategoryTheory.Functor.FullyFaithful.nonempty_iff_map_bijective`：nonempt
y_iff_map_bijective : Nonempty F.FullyFaithful ↔ forall (X Y : C), Function.Bije
ctive (F.map : (X ⟶ Y) -> _)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff`：bijective_
toDescentData_map_iff (M N : F.obj (.mk (op S))) : Function.Bijective ((F.toDesc
entData f).map : (M ⟶ N) -> _) ↔ Presieve.IsSheafF…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Over.mk_surjective`：mk_surjective {S : T} (X : Over S) : 
exists (Y : T) (f : Y ⟶ S), Over.mk f = X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPrestackFor_iff_isSheafFor {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ ∀ (M N : F.obj (.mk (op S))),
      Presieve.IsSheafFor (P := F.presheafHom M N)
        ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  rw [isPrestackFor_iff, Functor.FullyFaithful.nonempty_iff_map_bijective]
  refine forall_congr' (fun M ↦ forall_congr' (fun N ↦ ?_))
  rw [bijective_toDescentData_map_iff]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor'** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：isPrestackFor_iff_isSheafFor' {S : C} (R : Sieve S) : F.IsPrestackFor R.ar
rows ↔ forall ⦃S₀ : C⦄ (M N : F.obj (.mk (op S₀))) (a : S ⟶ S₀), Presieve.IsShea
fFor (F.presheafHom M N) ((Sieve.overEquiv (Over.mk a)).symm R).arrows
参数：R : Sieve S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor`：isPrestackFor
_iff_isSheafFor {S : C} (R : Sieve S) : F.IsPrestackFor R.arrows ↔ forall (M N :
 F.obj (.mk (op S))), Presieve.IsSheafFor (P
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用引理 `CategoryTheory.Presieve.isSheafFor_over_map_op_comp_iff`：isSheafFor_over
_map_op_comp_iff {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w) {X : Over B}
 (R : Sieve X) {X' : Over B'} (e : (Over.map …
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_of_iso`：isSheafFor_iff_of_iso {P'
 : Cᵒᵖ ⥤ Type w} (i : P ≅ P') : IsSheafFor P R ↔ IsSheafFor P' R
-/
lemma isPrestackFor_iff_isSheafFor' {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ ∀ ⦃S₀ : C⦄ (M N : F.obj (.mk (op S₀))) (a : S ⟶ S₀),
      Presieve.IsSheafFor (F.presheafHom M N) ((Sieve.overEquiv (Over.mk a)).symm R).arrows := by
  rw [isPrestackFor_iff_isSheafFor]
  refine ⟨fun h S₀ M N a ↦ ?_, by tauto⟩
  replace h := h ((F.map a.op.toLoc).toFunctor.obj M) ((F.map a.op.toLoc).toFunctor.obj N)
  rw [← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    dsimp at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-
**CategoryTheory.Pseudofunctor.IsPrestackFor.isSheafFor'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Pseudofunctor.IsPrestackFor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTh
eory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat} {S₀ 
: C}   (S : CategoryTheory.Over S₀) {R : CategoryTheory.Sieve S},   F.IsPrestack
For ((CategoryTheory.Sieve.overEquiv S) R).arrows →     ∀ (M N : ↑(F.obj { as :=
 Opposite.op S₀ })), CategoryTheory.Presieve.IsSheafFor (F.presheafHom M N) R.ar
rows
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；S : CategoryTheory.Over S₀；(CategoryTheory
.Sieve.overEquiv S) R；M N : ↑(F.obj { as := Opposite.op S₀ })；F.presheafHom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Over.mk_surjective`：mk_surjective {S : T} (X : Over S) : 
exists (Y : T) (f : Y ⟶ S), Over.mk f = X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用引理 `CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor'`：isPrestackFo
r_iff_isSheafFor' {S : C} (R : Sieve S) : F.IsPrestackFor R.arrows ↔ forall ⦃S₀ 
: C⦄ (M N : F.obj (.mk (op S₀))) (a : S ⟶ S₀), P…
-/
lemma IsPrestackFor.isSheafFor'
    {S₀ : C} (S : Over S₀) {R : Sieve S} (hF : F.IsPrestackFor (Sieve.overEquiv _ R).arrows)
    (M N : F.obj (.mk (op S₀))) :
    Presieve.IsSheafFor (F.presheafHom M N) R.arrows := by
  rw [isPrestackFor_iff_isSheafFor'] at hF
  obtain ⟨S, a, rfl⟩ := S.mk_surjective
  simpa using hF M N a

variable {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F` is a prestack for a Grothendieck topology `J`, and `f` is a covering
family of morphisms, then the functor `F.toDescentData f` is fully faithful. -/
/-
**CategoryTheory.Pseudofunctor.fullyFaithfulToDescentData** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：fullyFaithfulToDescentData [F.IsPrestack J] (hf : Sieve.ofArrows _ f in J 
S) : (F.toDescentData f).FullyFaithful
参数：hf : Sieve.ofArrows _ f in J S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is a prestack for a Grothendieck topology `J`, and `f` is a covering
family of morphisms, then the functor `F.toDescentData f` is fully faithful.
-/
noncomputable def fullyFaithfulToDescentData [F.IsPrestack J] (hf : Sieve.ofArrows _ f ∈ J S) :
    (F.toDescentData f).FullyFaithful :=
  Nonempty.some (by
    rw [← isPrestackFor_ofArrows_iff, ← IsPrestackFor_generate_iff,
      isPrestackFor_iff_isSheafFor]
    intro M N
    refine ((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J M N)).isSheafFor _ ?_
    rwa [GrothendieckTopology.mem_over_iff, Sieve.generate_sieve, OrderIso.apply_symm_apply])
/-
**CategoryTheory.Pseudofunctor.isPrestackFor** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Pseudofunctor`。
形式化陈述：isPrestackFor [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.genera
te R in J S) : F.IsPrestackFor R
参数：R : Presieve S；hR : Sieve.generate R in J S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.isPrestackFor_iff`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Pseudofunctor (CategoryTh
eory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
-/
lemma isPrestackFor [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.generate R ∈ J S) :
    F.IsPrestackFor R := by
  rw [isPrestackFor_iff]
  exact ⟨F.fullyFaithfulToDescentData _ (by rwa [Sieve.ofArrows_category'])⟩
/-
**CategoryTheory.Pseudofunctor.isPrestackFor'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：isPrestackFor' [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R in J S) : F.
IsPrestackFor R.arrows
参数：R : Sieve S；hR : R in J S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Pseudofunctor.isPrestackFor`：isPrestackFor [F.IsPrestack 
J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S) : F.IsPrestackFor R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
-/
lemma isPrestackFor' [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R ∈ J S) :
    F.IsPrestackFor R.arrows :=
  F.isPrestackFor _ (by simpa)

variable {F} in
/-
**CategoryTheory.Pseudofunctor.IsPrestack.of_isPrestackFor** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Pseudofunctor.IsPrestack`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTh
eory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat}   {J
 : CategoryTheory.GrothendieckTopology C}, (∀ (S : C), ∀ R ∈ J S, F.IsPrestackFo
r R.arrows) → F.IsPrestack J
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；∀ (S : C), ∀ R ∈ J S, F.IsPrestackFor R.ar
rows。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用引理 `CategoryTheory.Over.mk_surjective`：mk_surjective {S : T} (X : Over S) : 
exists (Y : T) (f : Y ⟶ S), Over.mk f = X
· 使用定理 `CategoryTheory.Pseudofunctor.IsPrestackFor.isSheafFor'`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Pseudofunctor (Ca
tegoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTh…
-/
lemma IsPrestack.of_isPrestackFor
    (hF : ∀ (S : C) (R : Sieve S) (_ : R ∈ J S), F.IsPrestackFor R.arrows) :
    F.IsPrestack J where
  isSheaf M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS
    obtain ⟨U, u, rfl⟩ := Over.mk_surjective U
    apply (hF _ _ hS).isSheafFor'

end Pseudofunctor

end CategoryTheory

