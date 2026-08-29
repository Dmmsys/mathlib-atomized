/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kenny Lau
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Formal Coproducts

In this file we construct the category of formal coproducts given a category.

## Main definitions

* `FormalCoproduct`: the category of formal coproducts, which are indexed sets of objects in a
  category. A morphism `∐ i : X.I, X.obj i ⟶ ∐ j : Y.I, Y.obj j` is given by a function
  `f : X.I → Y.I` and maps `X.obj i ⟶ Y.obj (f i)` for each `i : X.I`.
* `FormalCoproduct.eval : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct C)ᵒᵖ ⥤ A)`:
  the universal property that a presheaf on `C` where the target category has arbitrary coproducts,
  can be extended to a presheaf on `FormalCoproduct C`.

## TODO

* `FormalCoproduct.incl C : C ⥤ FormalCoproduct.{w} C` probably preserves every limit?

-/

@[expose] public section

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

open Opposite CategoryTheory Functor

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]

variable (C) in
/--
Definition of `FormalCoproduct` / `FormalCoproduct` 的定义

English:
structure FormalCoproduct
  parameters: where
  axioms and operations (2):
    - I : Type w
    - obj((i : I)) : C

中文:
结构 形式余积
  参数: where
  公理与运算 (2 个):
    - I : 类型 w
    - obj((i : I)) : C
-/
structure FormalCoproduct where
  /-- The indexing type. -/
  I : Type w
  /-- The object in the original category indexed by `x : I`. -/
  obj (i : I) : C

namespace FormalCoproduct

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : FormalCoproduct.{w} C)
  axioms and operations (2):
    - f : X.I -> Y.I
    - φ((i : X.I)) : X.obj i ⟶ Y.obj (f i)

中文:
结构 态射
  参数: (X Y : 形式余积.{w} C)
  公理与运算 (2 个):
    - f : X.I -> Y.I
    - φ((i : X.I)) : X.obj i ⟶ Y.obj (f i)
-/
structure Hom (X Y : FormalCoproduct.{w} C) where
  /-- The function on the indexing sets. -/
  f : X.I -> Y.I
  /-- The map on each component. -/
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the full subcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (FormalCoproduct.{w} C) where
  body: Hom
  id X := { f := id, φ := fun _ => 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ => α.φ _ ≫ β.φ _ }

@[ext (iff := false)]

中文:
实例 category
  签名: : 范畴 (形式余积.{w} C) where
  定义体: Hom
  id X := { f := id, φ := fun _ => 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ => α.φ _ ≫ β.φ _ }

@[ext (iff := false)]
-/
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ => 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ => α.φ _ ≫ β.φ _ }

@[ext (iff := false)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
  proof: by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

中文:
引理 hom_ext
  结论: {X Y : 形式余积.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
  证明: by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl
-/
lemma hom_ext {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : forall (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i) : f = g := by
  obtain ⟨f, F⟩ := f
  obtain ⟨g, G⟩ := g
  obtain rfl : f = g := h₁
  obtain rfl : F = G := by ext i; simpa using h₂ i
  rfl

/--
lemma `hom_ext_iff` / 引理 `hom_ext_iff`

English:
lemma hom_ext_iff
  given: {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y)
  proof: ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ => hom_ext h₁ h₂⟩

中文:
引理 hom_ext_iff
  条件: {X Y : 形式余积.{w} C} (f g : X ⟶ Y)
  证明: ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ => hom_ext h₁ h₂⟩

Depends on / 依赖: hom_ext
-/
lemma hom_ext_iff {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ exists h₁ : f.f = g.f, forall (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun ⟨h₁, h₂⟩ => hom_ext h₁ h₂⟩

/--
lemma `hom_ext_iff'` / 引理 `hom_ext_iff'`

English:
lemma hom_ext_iff'
  given: {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y)
  proof: ⟨(· ▸ by simp), fun h => hom_ext (funext fun i => (h i).fst) fun i => (h i).snd⟩

中文:
引理 hom_ext_iff'
  条件: {X Y : 形式余积.{w} C} (f g : X ⟶ Y)
  证明: ⟨(· ▸ by simp), fun h => hom_ext (funext fun i => (h i).fst) fun i => (h i).snd⟩

Depends on / 依赖: hom_ext
-/
lemma hom_ext_iff' {X Y : FormalCoproduct.{w} C} (f g : X ⟶ Y) :
    f = g ↔ forall i : X.I, exists h₁ : f.f i = g.f i, f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i :=
  ⟨(· ▸ by simp), fun h => hom_ext (funext fun i => (h i).fst) fun i => (h i).snd⟩

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoOfComponents` / `isoOfComponents` 的定义

English:
definition isoOfComponents
  signature: {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
  body: { f := e, φ := fun i => (h i).hom }
  inv := { f := e.symm, φ := fun i => eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

中文:
定义 isoOfComponents
  签名: {X Y : 形式余积.{w} C} (e : X.I ≃ Y.I)
  定义体: { f := e, φ := fun i => (h i).hom }
  inv := { f := e.symm, φ := fun i => eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop
-/
@[simps!] def isoOfComponents {X Y : FormalCoproduct.{w} C} (e : X.I ≃ Y.I)
    (h : forall i, X.obj i ≅ Y.obj (e i)) : X ≅ Y where
  hom := { f := e, φ := fun i => (h i).hom }
  inv := { f := e.symm, φ := fun i => eqToHom (by simp) ≫ (h (e.symm i)).inv }
  hom_inv_id := by ext <;> aesop
  inv_hom_id := by ext <;> aesop

variable (C) in
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : C ⥤ FormalCoproduct.{w} C where
  body: ⟨PUnit, fun _ => X⟩
  map f := ⟨fun _ => PUnit.unit, fun _ => f⟩

中文:
定义 incl
  签名: : C ⥤ 形式余积.{w} C where
  定义体: ⟨PUnit, fun _ => X⟩
  map f := ⟨fun _ => PUnit.unit, fun _ => f⟩
-/
@[simps!] def incl : C ⥤ FormalCoproduct.{w} C where
  obj X := ⟨PUnit, fun _ => X⟩
  map f := ⟨fun _ => PUnit.unit, fun _ => f⟩

section fromIncl

variable {X : C} {Y : FormalCoproduct.{w} C}

/--
Definition of `Hom.fromIncl` / `Hom.fromIncl` 的定义

English:
definition Hom.fromIncl
  signature: (i : Y.I) (f : X ⟶ Y.obj i)
  body: ⟨fun _ => i, fun _ => f⟩

中文:
定义 态射.fromIncl
  签名: (i : Y.I) (f : X ⟶ Y.obj i)
  定义体: ⟨fun _ => i, fun _ => f⟩
-/
@[simps!] def Hom.fromIncl (i : Y.I) (f : X ⟶ Y.obj i) : (incl C).obj X ⟶ Y :=
  ⟨fun _ => i, fun _ => f⟩

/--
Definition of `Hom.asSigma` / `Hom.asSigma` 的定义

English:
definition Hom.asSigma
  signature: (f : (incl C).obj X ⟶ Y)
  body: ⟨f.f PUnit.unit, f.φ PUnit.unit⟩

中文:
定义 态射.asSigma
  签名: (f : (incl C).obj X ⟶ Y)
  定义体: ⟨f.f PUnit.unit, f.φ PUnit.unit⟩

Depends on / 依赖: PUnit.unit
-/
def Hom.asSigma (f : (incl C).obj X ⟶ Y) : Σ (i : Y.I), X ⟶ Y.obj i :=
  ⟨f.f PUnit.unit, f.φ PUnit.unit⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.fromIncl_asSigma` / 引理 `Hom.fromIncl_asSigma`

English:
lemma Hom.fromIncl_asSigma
  given: (f : (incl C).obj X ⟶ Y)
  proof: by
  ext <;> aesop

中文:
引理 态射.fromIncl_asSigma
  条件: (f : (incl C).obj X ⟶ Y)
  证明: by
  ext <;> aesop
-/
lemma Hom.fromIncl_asSigma (f : (incl C).obj X ⟶ Y) :
    Hom.fromIncl f.asSigma.fst f.asSigma.snd = f := by
  ext <;> aesop

end fromIncl

-- This is probably some form of adjunction?
/--
Definition of `inclHomEquiv` / `inclHomEquiv` 的定义

English:
definition inclHomEquiv
  signature: (X : C) (Y : FormalCoproduct.{w} C)
  body: f.asSigma
  invFun f := .fromIncl f.1 f.2
  left_inv f := f.fromIncl_asSigma
  right_inv _ := rfl

中文:
定义 inclHomEquiv
  签名: (X : C) (Y : 形式余积.{w} C)
  定义体: f.asSigma
  invFun f := .fromIncl f.1 f.2
  left_inv f := f.fromIncl_asSigma
  right_inv _ := rfl
-/
@[simps!] def inclHomEquiv (X : C) (Y : FormalCoproduct.{w} C) :
    ((incl C).obj X ⟶ Y) ≃ (i : Y.I) × (X ⟶ Y.obj i) where
  toFun f := f.asSigma
  invFun f := .fromIncl f.1 f.2
  left_inv f := f.fromIncl_asSigma
  right_inv _ := rfl

/--
Definition of `fullyFaithfulIncl` / `fullyFaithfulIncl` 的定义

English:
definition fullyFaithfulIncl
  signature: : (incl C).FullyFaithful where
  body: f.φ PUnit.unit

中文:
定义 fullyFaithfulIncl
  签名: : (incl C).满忠实 where
  定义体: f.φ PUnit.unit
-/
@[simps!] def fullyFaithfulIncl : (incl C).FullyFaithful where
  preimage f := f.φ PUnit.unit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl C).Full
  body: fullyFaithfulIncl.full

中文:
实例 :
  签名: (incl C).满
  定义体: fullyFaithfulIncl.full

Depends on / 依赖: fullyFaithfulIncl, fullyFaithfulIncl.full
-/
instance : (incl C).Full :=
  fullyFaithfulIncl.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (incl C).Faithful
  body: fullyFaithfulIncl.faithful

中文:
实例 :
  签名: (incl C).忠实
  定义体: fullyFaithfulIncl.faithful

Depends on / 依赖: faithful, fullyFaithfulIncl, fullyFaithfulIncl.faithful
-/
instance : (incl C).Faithful :=
  fullyFaithfulIncl.faithful

/--
Definition of `homOfPiHom` / `homOfPiHom` 的定义

English:
definition homOfPiHom
  signature: (X : C) {J : Type w} (f : (j : J) -> C) (φ : (j : J) -> f j ⟶ X)
  body: ⟨fun _ => PUnit.unit, φ⟩

中文:
定义 homOfPiHom
  签名: (X : C) {J : 类型 w} (f : (j : J) -> C) (φ : (j : J) -> f j ⟶ X)
  定义体: ⟨fun _ => PUnit.unit, φ⟩
-/
@[simps!] def homOfPiHom (X : C) {J : Type w} (f : (j : J) -> C) (φ : (j : J) -> f j ⟶ X) :
    FormalCoproduct.mk _ f ⟶ (incl C).obj X :=
  ⟨fun _ => PUnit.unit, φ⟩

section Coproduct

variable (𝒜 : Type w) (f : 𝒜 -> FormalCoproduct.{w} C) (t X : FormalCoproduct.{w} C)

/--
Definition of `cofan` / `cofan` 的定义

English:
definition cofan
  signature: : Cofan f
  body: Cofan.mk ⟨(i : 𝒜) × (f i).I, fun p => (f p.1).obj p.2⟩
    fun i => ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩

中文:
定义 cofan
  签名: : Cofan f
  定义体: Cofan.mk ⟨(i : 𝒜) × (f i).I, fun p => (f p.1).obj p.2⟩
    fun i => ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩

Depends on / 依赖: Cofan.mk
-/
def cofan : Cofan f :=
  Cofan.mk ⟨(i : 𝒜) × (f i).I, fun p => (f p.1).obj p.2⟩
    fun i => ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩

section simp_lemmas

variable {𝒜 f}

/--
theorem `cofan_inj` / 定理 `cofan_inj`

English:
theorem cofan_inj
  given: (i : 𝒜)
  statement: (cofan 𝒜 f).inj i = ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩
  proof: rfl

中文:
定理 cofan_inj
  条件: (i : 𝒜)
  结论: (cofan 𝒜 f).inj i = ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩
  证明: rfl
-/
theorem cofan_inj (i : 𝒜) : (cofan 𝒜 f).inj i = ⟨fun x => ⟨i, x⟩, fun x => 𝟙 ((f i).obj x)⟩ := rfl

/--
lemma `cofan_inj_f_fst` / 引理 `cofan_inj_f_fst`

English:
lemma cofan_inj_f_fst
  given: (i : 𝒜) (x)
  statement: (((cofan 𝒜 f).inj i).f x).1 = i
  proof: rfl

中文:
引理 cofan_inj_f_fst
  条件: (i : 𝒜) (x)
  结论: (((cofan 𝒜 f).inj i).f x).1 = i
  证明: rfl
-/
@[simp] lemma cofan_inj_f_fst (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).1 = i := rfl

/--
lemma `cofan_inj_f_snd` / 引理 `cofan_inj_f_snd`

English:
lemma cofan_inj_f_snd
  given: (i : 𝒜) (x)
  statement: (((cofan 𝒜 f).inj i).f x).2 = x
  proof: rfl

中文:
引理 cofan_inj_f_snd
  条件: (i : 𝒜) (x)
  结论: (((cofan 𝒜 f).inj i).f x).2 = x
  证明: rfl
-/
@[simp] lemma cofan_inj_f_snd (i : 𝒜) (x) : (((cofan 𝒜 f).inj i).f x).2 = x := rfl

/--
lemma `cofan_inj_φ` / 引理 `cofan_inj_φ`

English:
lemma cofan_inj_φ
  given: (i : 𝒜) (x)
  statement: ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x)
  proof: rfl

中文:
引理 cofan_inj_φ
  条件: (i : 𝒜) (x)
  结论: ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x)
  证明: rfl
-/
@[simp] lemma cofan_inj_φ (i : 𝒜) (x) : ((cofan 𝒜 f).inj i).φ x = 𝟙 ((f i).obj x) := rfl

end simp_lemmas

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cofanHomEquiv` / `cofanHomEquiv` 的定义

English:
definition cofanHomEquiv
  signature: :
  body: (cofan 𝒜 f).inj i ≫ m
  invFun s := ⟨fun p => (s p.1).f p.2, fun p => (s p.1).φ p.2⟩
  left_inv m := hom_ext rfl (fun ⟨i, x⟩ => by simp [cofan_inj])
  right_inv p := by ext <;> simp

中文:
定义 cofanHomEquiv
  签名: :
  定义体: (cofan 𝒜 f).inj i ≫ m
  invFun s := ⟨fun p => (s p.1).f p.2, fun p => (s p.1).φ p.2⟩
  left_inv m := hom_ext rfl (fun ⟨i, x⟩ => by simp [cofan_inj])
  right_inv p := by ext <;> simp
-/
@[simps!] def cofanHomEquiv :
    ((cofan 𝒜 f).pt ⟶ t) ≃ ((i : 𝒜) -> (f i ⟶ t)) where
  toFun m i := (cofan 𝒜 f).inj i ≫ m
  invFun s := ⟨fun p => (s p.1).f p.2, fun p => (s p.1).φ p.2⟩
  left_inv m := hom_ext rfl (fun ⟨i, x⟩ => by simp [cofan_inj])
  right_inv p := by ext <;> simp

/--
Definition of `isColimitCofan` / `isColimitCofan` 的定义

English:
definition isColimitCofan
  signature: : IsColimit (cofan 𝒜 f)
  body: Cofan.IsColimit.mk (cofan 𝒜 f) (fun t => (cofanHomEquiv _ _ _).symm t.inj)
    (fun t i => congrFun ((cofanHomEquiv _ _ _).right_inv t.inj) i)
    (fun _ _ h => (Equiv.eq_symm_apply _).2 (funext h))

中文:
定义 isColimitCofan
  签名: : 是余极限 (cofan 𝒜 f)
  定义体: Cofan.IsColimit.mk (cofan 𝒜 f) (fun t => (cofanHomEquiv _ _ _).symm t.inj)
    (fun t i => congrFun ((cofanHomEquiv _ _ _).right_inv t.inj) i)
    (fun _ _ h => (Equiv.eq_symm_apply _).2 (funext h))
-/
@[simps!] def isColimitCofan : IsColimit (cofan 𝒜 f) :=
  Cofan.IsColimit.mk (cofan 𝒜 f) (fun t => (cofanHomEquiv _ _ _).symm t.inj)
    (fun t i => congrFun ((cofanHomEquiv _ _ _).right_inv t.inj) i)
    (fun _ _ h => (Equiv.eq_symm_apply _).2 (funext h))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoproducts.{w} (FormalCoproduct.{w} C)
  body: hasCoproducts_of_colimit_cofans _ (isColimitCofan _)

中文:
实例 :
  签名: HasCoproducts.{w} (形式余积.{w} C)
  定义体: hasCoproducts_of_colimit_cofans _ (isColimitCofan _)

Depends on / 依赖: hasCoproducts_of_colimit_cofans, isColimitCofan
-/
instance : HasCoproducts.{w} (FormalCoproduct.{w} C) :=
  hasCoproducts_of_colimit_cofans _ (isColimitCofan _)

/--
Definition of `coproductIsoCofanPt` / `coproductIsoCofanPt` 的定义

English:
definition coproductIsoCofanPt
  signature: : ∐ f ≅ (cofan 𝒜 f).pt
  body: colimit.isoColimitCocone ⟨_, isColimitCofan _ _⟩

中文:
定义 coproductIsoCofanPt
  签名: : ∐ f ≅ (cofan 𝒜 f).pt
  定义体: colimit.isoColimitCocone ⟨_, isColimitCofan _ _⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone, isColimitCofan, isoColimitCocone
-/
noncomputable def coproductIsoCofanPt : ∐ f ≅ (cofan 𝒜 f).pt :=
  colimit.isoColimitCocone ⟨_, isColimitCofan _ _⟩

variable {𝒜 f} in
/--
lemma `ι_comp_coproductIsoCofanPt` / 引理 `ι_comp_coproductIsoCofanPt`

English:
lemma ι_comp_coproductIsoCofanPt
  given: (i)
  proof: colimit.isoColimitCocone_ι_hom _ _

中文:
引理 ι_comp_coproductIsoCofanPt
  条件: (i)
  证明: colimit.isoColimitCocone_ι_hom _ _
-/
@[reassoc (attr := simp)] lemma ι_comp_coproductIsoCofanPt (i) :
    Sigma.ι f i ≫ (coproductIsoCofanPt 𝒜 f).hom = (cofan 𝒜 f).inj i :=
  colimit.isoColimitCocone_ι_hom _ _

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: (X : FormalCoproduct.{w} C)
  body: (incl C).obj ∘ X.obj

中文:
定义 toFun
  签名: (X : 形式余积.{w} C)
  定义体: (incl C).obj ∘ X.obj

Depends on / 依赖: X.obj
-/
def toFun (X : FormalCoproduct.{w} C) : X.I -> FormalCoproduct.{w} C :=
  (incl C).obj ∘ X.obj

/--
Definition of `cofanPtIsoSelf` / `cofanPtIsoSelf` 的定义

English:
definition cofanPtIsoSelf
  signature: : (cofan X.I X.toFun).pt ≅ X
  body: isoOfComponents (Equiv.sigmaPUnit X.I) fun i => Iso.refl (X.obj i.fst)

中文:
定义 cofanPtIsoSelf
  签名: : (cofan X.I X.toFun).pt ≅ X
  定义体: isoOfComponents (Equiv.sigmaPUnit X.I) fun i => Iso.refl (X.obj i.fst)

Depends on / 依赖: Equiv.sigmaPUnit, Iso.refl, X.obj, i.fst, isoOfComponents, sigmaPUnit
-/
def cofanPtIsoSelf : (cofan X.I X.toFun).pt ≅ X :=
  isoOfComponents (Equiv.sigmaPUnit X.I) fun i => Iso.refl (X.obj i.fst)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inj_comp_cofanPtIsoSelf_hom` / 引理 `inj_comp_cofanPtIsoSelf_hom`

English:
lemma inj_comp_cofanPtIsoSelf_hom
  given: (i : X.I)
  proof: hom_ext rfl (fun i => by aesop)

@[reassoc (attr := simp)]

中文:
引理 inj_comp_cofanPtIsoSelf_hom
  条件: (i : X.I)
  证明: hom_ext rfl (fun i => by aesop)

@[reassoc (attr := simp)]

Depends on / 依赖: hom_ext
-/
lemma inj_comp_cofanPtIsoSelf_hom (i : X.I) :
    (cofan X.I X.toFun).inj i ≫ (cofanPtIsoSelf X).hom = .fromIncl i (𝟙 (X.obj i)) :=
  hom_ext rfl (fun i => by aesop)

@[reassoc (attr := simp)]
/--
lemma `fromIncl_comp_cofanPtIsoSelf_inv` / 引理 `fromIncl_comp_cofanPtIsoSelf_inv`

English:
lemma fromIncl_comp_cofanPtIsoSelf_inv
  given: (i : X.I)
  proof: (Iso.comp_inv_eq _).2 (inj_comp_cofanPtIsoSelf_hom _ _).symm

中文:
引理 fromIncl_comp_cofanPtIsoSelf_inv
  条件: (i : X.I)
  证明: (Iso.comp_inv_eq _).2 (inj_comp_cofanPtIsoSelf_hom _ _).symm

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, inj_comp_cofanPtIsoSelf_hom
-/
lemma fromIncl_comp_cofanPtIsoSelf_inv (i : X.I) :
    Hom.fromIncl i (𝟙 (X.obj i)) ≫ (cofanPtIsoSelf X).inv = (cofan X.I X.toFun).inj i :=
  (Iso.comp_inv_eq _).2 (inj_comp_cofanPtIsoSelf_hom _ _).symm

/--
Definition of `coproductIsoSelf` / `coproductIsoSelf` 的定义

English:
definition coproductIsoSelf
  signature: :
  body: coproductIsoCofanPt _ _ ≪≫ cofanPtIsoSelf X

中文:
定义 coproductIsoSelf
  签名: :
  定义体: coproductIsoCofanPt _ _ ≪≫ cofanPtIsoSelf X
-/
@[simps!] noncomputable def coproductIsoSelf :
    ∐ X.toFun ≅ X :=
  coproductIsoCofanPt _ _ ≪≫ cofanPtIsoSelf X

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ι_comp_coproductIsoSelf_hom` / 引理 `ι_comp_coproductIsoSelf_hom`

English:
lemma ι_comp_coproductIsoSelf_hom
  given: (i : X.I)
  proof: by
  simp [coproductIsoSelf]

中文:
引理 ι_comp_coproductIsoSelf_hom
  条件: (i : X.I)
  证明: by
  simp [coproductIsoSelf]
-/
@[reassoc (attr := simp)] lemma ι_comp_coproductIsoSelf_hom (i : X.I) :
    Sigma.ι _ i ≫ (coproductIsoSelf X).hom = .fromIncl i (𝟙 (X.obj i)) := by
  simp [coproductIsoSelf]

/--
lemma `fromIncl_comp_coproductIsoSelf_inv` / 引理 `fromIncl_comp_coproductIsoSelf_inv`

English:
lemma fromIncl_comp_coproductIsoSelf_inv
  given: (i : X.I)
  proof: (Iso.comp_inv_eq _).2 (ι_comp_coproductIsoSelf_hom _ _).symm

中文:
引理 fromIncl_comp_coproductIsoSelf_inv
  条件: (i : X.I)
  证明: (Iso.comp_inv_eq _).2 (ι_comp_coproductIsoSelf_hom _ _).symm
-/
@[reassoc (attr := simp)] lemma fromIncl_comp_coproductIsoSelf_inv (i : X.I) :
    Hom.fromIncl i (𝟙 (X.obj i)) ≫ (coproductIsoSelf X).inv = Sigma.ι X.toFun i :=
  (Iso.comp_inv_eq _).2 (ι_comp_coproductIsoSelf_hom _ _).symm

/--
Definition of `objIsoOfEq` / `objIsoOfEq` 的定义

English:
definition objIsoOfEq
  signature: (X : FormalCoproduct.{w} C) {i j : X.I} (hij : i = j)
  body: eqToIso (by rw [hij])

@[simp]

中文:
定义 objIsoOfEq
  签名: (X : 形式余积.{w} C) {i j : X.I} (hij : i = j)
  定义体: eqToIso (by rw [hij])

@[simp]

Depends on / 依赖: eqToIso
-/
def objIsoOfEq (X : FormalCoproduct.{w} C) {i j : X.I} (hij : i = j) :
    X.obj i ≅ X.obj j :=
  eqToIso (by rw [hij])

@[simp]
/--
lemma `objIsoOfEq_rfl` / 引理 `objIsoOfEq_rfl`

English:
lemma objIsoOfEq_rfl
  given: (X : FormalCoproduct.{w} C) (i : X.I)
  proof: rfl

@[simp]

中文:
引理 objIsoOfEq_rfl
  条件: (X : 形式余积.{w} C) (i : X.I)
  证明: rfl

@[simp]
-/
lemma objIsoOfEq_rfl (X : FormalCoproduct.{w} C) (i : X.I) :
    X.objIsoOfEq (rfl : i = i) = Iso.refl _ :=
  rfl

@[simp]
/--
lemma `objIsoOfEq_trans` / 引理 `objIsoOfEq_trans`

English:
lemma objIsoOfEq_trans
  statement: (X : FormalCoproduct.{w} C) {i j k : X.I}
  proof: by
  subst hij hjk
  simp

@[simp]

中文:
引理 objIsoOfEq_trans
  结论: (X : 形式余积.{w} C) {i j k : X.I}
  证明: by
  subst hij hjk
  simp

@[simp]
-/
lemma objIsoOfEq_trans (X : FormalCoproduct.{w} C) {i j k : X.I}
    (hij : i = j) (hjk : j = k) :
    X.objIsoOfEq hij ≪≫ X.objIsoOfEq hjk = X.objIsoOfEq (hij.trans hjk) := by
  subst hij hjk
  simp

@[simp]
/--
lemma `objIsoOfEq_symm` / 引理 `objIsoOfEq_symm`

English:
lemma objIsoOfEq_symm
  statement: (X : FormalCoproduct.{w} C) {i j : X.I}
  proof: by
  subst hij
  simp

中文:
引理 objIsoOfEq_symm
  结论: (X : 形式余积.{w} C) {i j : X.I}
  证明: by
  subst hij
  simp
-/
lemma objIsoOfEq_symm (X : FormalCoproduct.{w} C) {i j : X.I}
    (hij : i = j) :
    (X.objIsoOfEq hij).symm = X.objIsoOfEq hij.symm := by
  subst hij
  simp

end Coproduct

section Terminal

/--
Definition of `isTerminalIncl` / `isTerminalIncl` 的定义

English:
definition isTerminalIncl
  signature: (T : C) (ht : IsTerminal T)
  body: IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, fun _ => ht.from _⟩)
    (fun _ _ => hom_ext (funext fun _ => rfl) (fun _ => ht.hom_ext _ _))

中文:
定义 isTerminalIncl
  签名: (T : C) (ht : 是终止 T)
  定义体: IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, fun _ => ht.from _⟩)
    (fun _ _ => hom_ext (funext fun _ => rfl) (fun _ => ht.hom_ext _ _))

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, PUnit.unit, hom_ext, ht.from, ht.hom_ext, ofUniqueHom
-/
def isTerminalIncl (T : C) (ht : IsTerminal T) : IsTerminal ((incl C).obj T) :=
  IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => PUnit.unit, fun _ => ht.from _⟩)
    (fun _ _ => hom_ext (funext fun _ => rfl) (fun _ => ht.hom_ext _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasTerminal
  signature: C] : HasTerminal (FormalCoproduct.{w} C)
  body: (isTerminalIncl (⊤_ C) terminalIsTerminal).hasTerminal

中文:
实例 [有终止
  签名: C] : 有终止 (形式余积.{w} C)
  定义体: (isTerminalIncl (⊤_ C) terminalIsTerminal).hasTerminal

Depends on / 依赖: hasTerminal, isTerminalIncl, terminalIsTerminal
-/
instance [HasTerminal C] : HasTerminal (FormalCoproduct.{w} C) :=
  (isTerminalIncl (⊤_ C) terminalIsTerminal).hasTerminal

end Terminal

section Pullback

variable {X Y Z : FormalCoproduct.{w} C} (f : X ⟶ Z) (g : Y ⟶ Z)
  (pb : forall i : Function.Pullback f.f g.f,
    PullbackCone (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2))
  (hpb : forall i, IsLimit (pb i))
  (T : FormalCoproduct.{w} C)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pullbackCone` / `pullbackCone` 的定义

English:
definition pullbackCone
  signature: : PullbackCone f g
  body: .mk (W := ⟨Function.Pullback f.f g.f, fun i => (pb i).pt⟩)
    ⟨fun i => i.1.fst, fun i => (pb i).fst⟩
    ⟨fun i => i.1.snd, fun i => (pb i).snd⟩
    (hom_ext (funext fun i => i.2) (fun i => by simp [(pb i).condition]))

中文:
定义 pullbackCone
  签名: : PullbackCone f g
  定义体: .mk (W := ⟨Function.Pullback f.f g.f, fun i => (pb i).pt⟩)
    ⟨fun i => i.1.fst, fun i => (pb i).fst⟩
    ⟨fun i => i.1.snd, fun i => (pb i).snd⟩
    (hom_ext (funext fun i => i.2) (fun i => by simp [(pb i).condition]))

Depends on / 依赖: Function, Function.Pullback, Pullback, condition, hom_ext
-/
def pullbackCone : PullbackCone f g :=
  .mk (W := ⟨Function.Pullback f.f g.f, fun i => (pb i).pt⟩)
    ⟨fun i => i.1.fst, fun i => (pb i).fst⟩
    ⟨fun i => i.1.snd, fun i => (pb i).snd⟩
    (hom_ext (funext fun i => i.2) (fun i => by simp [(pb i).condition]))

section simp_lemmas

/--
lemma `pullbackCone_fst_f` / 引理 `pullbackCone_fst_f`

English:
lemma pullbackCone_fst_f
  given: (i)
  statement: (pullbackCone f g pb).fst.f i = i.1.1
  proof: rfl

中文:
引理 pullbackCone_fst_f
  条件: (i)
  结论: (pullbackCone f g pb).fst.f i = i.1.1
  证明: rfl
-/
@[simp] lemma pullbackCone_fst_f (i) : (pullbackCone f g pb).fst.f i = i.1.1 := rfl

/--
lemma `pullbackCone_fst_φ` / 引理 `pullbackCone_fst_φ`

English:
lemma pullbackCone_fst_φ
  given: (i)
  statement: (pullbackCone f g pb).fst.φ i = (pb i).fst
  proof: rfl

中文:
引理 pullbackCone_fst_φ
  条件: (i)
  结论: (pullbackCone f g pb).fst.φ i = (pb i).fst
  证明: rfl
-/
@[simp] lemma pullbackCone_fst_φ (i) : (pullbackCone f g pb).fst.φ i = (pb i).fst := rfl

/--
lemma `pullbackCone_snd_f` / 引理 `pullbackCone_snd_f`

English:
lemma pullbackCone_snd_f
  given: (i)
  statement: (pullbackCone f g pb).snd.f i = i.1.2
  proof: rfl

中文:
引理 pullbackCone_snd_f
  条件: (i)
  结论: (pullbackCone f g pb).snd.f i = i.1.2
  证明: rfl
-/
@[simp] lemma pullbackCone_snd_f (i) : (pullbackCone f g pb).snd.f i = i.1.2 := rfl

/--
lemma `pullbackCone_snd_φ` / 引理 `pullbackCone_snd_φ`

English:
lemma pullbackCone_snd_φ
  given: (i)
  statement: (pullbackCone f g pb).snd.φ i = (pb i).snd
  proof: rfl

中文:
引理 pullbackCone_snd_φ
  条件: (i)
  结论: (pullbackCone f g pb).snd.φ i = (pb i).snd
  证明: rfl
-/
@[simp] lemma pullbackCone_snd_φ (i) : (pullbackCone f g pb).snd.φ i = (pb i).snd := rfl

/--
lemma `pullbackCone_condition` / 引理 `pullbackCone_condition`

English:
lemma pullbackCone_condition
  proof: PullbackCone.condition _

中文:
引理 pullbackCone_condition
  证明: PullbackCone.condition _
-/
@[simp] lemma pullbackCone_condition :
    (pullbackCone f g pb).fst ≫ f = (pullbackCone f g pb).snd ≫ g :=
  PullbackCone.condition _

end simp_lemmas

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homPullbackEquiv` / `homPullbackEquiv` 的定义

English:
definition homPullbackEquiv
  signature: : (T ⟶ (pullbackCone f g pb).pt) ≃
  body: ⟨⟨m ≫ (pullbackCone f g pb).fst, m ≫ (pullbackCone f g pb).snd⟩, by simp⟩
  invFun s := ⟨fun i => ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg Hom.f s.2) i⟩,
    fun i => (hpb _).lift (PullbackCone.mk (s.1.1.φ i) (s.1.2.φ i)
      (by simpa using ((hom_ext_iff _ _).1 s.2).2 i))⟩
  left_inv m := hom_e

中文:
定义 homPullbackEquiv
  签名: : (T ⟶ (pullbackCone f g pb).pt) ≃
  定义体: ⟨⟨m ≫ (pullbackCone f g pb).fst, m ≫ (pullbackCone f g pb).snd⟩, by simp⟩
  invFun s := ⟨fun i => ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg Hom.f s.2) i⟩,
    fun i => (hpb _).lift (PullbackCone.mk (s.1.1.φ i) (s.1.2.φ i)
      (by simpa using ((hom_ext_iff _ _).1 s.2).2 i))⟩
  left_inv m := hom_e
-/
@[simps!] def homPullbackEquiv : (T ⟶ (pullbackCone f g pb).pt) ≃
    { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g } where
  toFun m := ⟨⟨m ≫ (pullbackCone f g pb).fst, m ≫ (pullbackCone f g pb).snd⟩, by simp⟩
  invFun s := ⟨fun i => ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg Hom.f s.2) i⟩,
    fun i => (hpb _).lift (PullbackCone.mk (s.1.1.φ i) (s.1.2.φ i)
      (by simpa using ((hom_ext_iff _ _).1 s.2).2 i))⟩
  left_inv m := hom_ext rfl (fun i => by
    simp only [eqToHom_refl, Category.comp_id]
    exact (hpb _).hom_ext ((pb _).equalizer_ext (by aesop) (by aesop)))
  right_inv s := by ext <;> simp

/--
Definition of `isLimitPullbackCone` / `isLimitPullbackCone` 的定义

English:
definition isLimitPullbackCone
  signature: : IsLimit (pullbackCone f g pb)
  body: by
  refine PullbackCone.IsLimit.mk
    (fst := (pullbackCone f g pb).fst) (snd := (pullbackCone f g pb).snd) _
    (fun s => (homPullbackEquiv f g pb hpb s.pt).2 ⟨(s.fst, s.snd), s.condition⟩)
    (fun s => congrArg (·.1.fst)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.co

中文:
定义 isLimitPullbackCone
  签名: : 是极限 (pullbackCone f g pb)
  定义体: by
  refine PullbackCone.IsLimit.mk
    (fst := (pullbackCone f g pb).fst) (snd := (pullbackCone f g pb).snd) _
    (fun s => (homPullbackEquiv f g pb hpb s.pt).2 ⟨(s.fst, s.snd), s.condition⟩)
    (fun s => congrArg (·.1.fst)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.co

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.mk, condition, convert, homPullbackEquiv, left_inv, pullbackCone, right_inv, s.condition, s.fst, s.pt, s.snd
-/
def isLimitPullbackCone : IsLimit (pullbackCone f g pb) := by
  refine PullbackCone.IsLimit.mk
    (fst := (pullbackCone f g pb).fst) (snd := (pullbackCone f g pb).snd) _
    (fun s => (homPullbackEquiv f g pb hpb s.pt).2 ⟨(s.fst, s.snd), s.condition⟩)
    (fun s => congrArg (·.1.fst)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s => congrArg (·.1.snd)
      ((homPullbackEquiv f g pb hpb s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s m h₁ h₂ => ?_)
  convert! ((homPullbackEquiv f g pb hpb s.pt).left_inv m).symm using 3
  rw [← h₁]; rw [← h₂]; rfl

-- Arguments cannot be inferred.
include pb hpb in
/--
theorem `hasPullback_of_pullbackCone` / 定理 `hasPullback_of_pullbackCone`

English:
theorem hasPullback_of_pullbackCone
  statement: HasPullback f g
  proof: ⟨⟨⟨_, isLimitPullbackCone f g pb hpb⟩⟩⟩

include hpb in

中文:
定理 hasPullback_of_pullbackCone
  结论: HasPullback f g
  证明: ⟨⟨⟨_, isLimitPullbackCone f g pb hpb⟩⟩⟩

include hpb in

Depends on / 依赖: isLimitPullbackCone
-/
theorem hasPullback_of_pullbackCone : HasPullback f g :=
  ⟨⟨⟨_, isLimitPullbackCone f g pb hpb⟩⟩⟩

include hpb in
/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  statement: IsPullback (pullbackCone f g pb).fst (pullbackCone f g pb).snd f g
  proof: ⟨⟨pullbackCone_condition f g pb⟩, ⟨isLimitPullbackCone f g pb hpb⟩⟩

omit pb

中文:
引理 isPullback
  结论: 是拉回 (pullbackCone f g pb).fst (pullbackCone f g pb).snd f g
  证明: ⟨⟨pullbackCone_condition f g pb⟩, ⟨isLimitPullbackCone f g pb hpb⟩⟩

omit pb

Depends on / 依赖: isLimitPullbackCone, pullbackCone_condition
-/
lemma isPullback : IsPullback (pullbackCone f g pb).fst (pullbackCone f g pb).snd f g :=
  ⟨⟨pullbackCone_condition f g pb⟩, ⟨isLimitPullbackCone f g pb hpb⟩⟩

omit pb
variable [HasPullbacks C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasPullback f g
  body: hasPullback_of_pullbackCone f g (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _)

中文:
实例 :
  签名: HasPullback f g
  定义体: hasPullback_of_pullbackCone f g (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _)

Depends on / 依赖: hasPullback_of_pullbackCone, isLimit, pullback, pullback.cone, pullback.isLimit
-/
instance : HasPullback f g :=
  hasPullback_of_pullbackCone f g (fun _ => pullback.cone _ _) (fun _ => pullback.isLimit _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasPullbacks (FormalCoproduct.{w} C)
  body: hasPullbacks_of_hasLimit_cospan _

中文:
实例 :
  签名: 有Pullbacks (形式余积.{w} C)
  定义体: hasPullbacks_of_hasLimit_cospan _

Depends on / 依赖: hasPullbacks_of_hasLimit_cospan
-/
instance : HasPullbacks (FormalCoproduct.{w} C) :=
  hasPullbacks_of_hasLimit_cospan _

end Pullback

noncomputable section HasCoproducts

variable [HasCoproducts.{w} A] (C) (J : Type w) (f : J -> FormalCoproduct.{w} C) (F : C ⥤ A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: : (C ⥤ A) ⥤ (FormalCoproduct.{w} C ⥤ A) where
  body: { obj X := ∐ fun (i : X.I) => F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i => F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ => by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i => α.app (f.obj i) }

中文:
定义 eval
  签名: : (C ⥤ A) ⥤ (形式余积.{w} C ⥤ A) where
  定义体: { obj X := ∐ fun (i : X.I) => F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i => F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ => by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i => α.app (f.obj i) }
-/
@[simps!] def eval : (C ⥤ A) ⥤ (FormalCoproduct.{w} C ⥤ A) where
  obj F :=
    { obj X := ∐ fun (i : X.I) => F.obj (X.obj i)
      map {X Y} f := Sigma.desc fun i => F.map (f.φ i) ≫ Sigma.ι (F.obj ∘ Y.obj) (f.f i)
      map_comp _ _ := Sigma.hom_ext _ _ (fun _ => by simp [Sigma.ι_desc]) }
  map α := { app f := Sigma.map fun i => α.app (f.obj i) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evalCompInclIsoId` / `evalCompInclIsoId` 的定义

English:
definition evalCompInclIsoId
  signature: :
  body: NatIso.ofComponents fun F => NatIso.ofComponents
    (fun x => ⟨Sigma.desc fun _ => 𝟙 _, Sigma.ι (fun _ => F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f => Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))

中文:
定义 evalCompInclIsoId
  签名: :
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents
    (fun x => ⟨Sigma.desc fun _ => 𝟙 _, Sigma.ι (fun _ => F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f => Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))
-/
@[simps!] def evalCompInclIsoId :
    eval C A ⋙ (whiskeringLeft _ _ A).obj (incl C) ≅ Functor.id (C ⥤ A) :=
  NatIso.ofComponents fun F => NatIso.ofComponents
    (fun x => ⟨Sigma.desc fun _ => 𝟙 _, Sigma.ι (fun _ => F.obj x) PUnit.unit, by aesop, by simp⟩)
    (fun f => Sigma.hom_ext _ _ (by simp [Sigma.ι_desc]))

variable {C A}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitEvalMapCoconeCofan` / `isColimitEvalMapCoconeCofan` 的定义

English:
definition isColimitEvalMapCoconeCofan
  signature: : IsColimit (((eval.{w} C A).obj F).mapCocone (cofan.{w} J f)) where
  body: Sigma.desc fun i => Sigma.ι (F.obj ∘ (f i.1).obj) i.2 ≫ s.ι.app ⟨i.1⟩
  fac s i := Sigma.hom_ext _ _ fun i => by simp [cofan, Function.comp_def]
  uniq s m h := Sigma.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan, Function.comp_def]

中文:
定义 isColimitEvalMapCoconeCofan
  签名: : 是余极限 (((eval.{w} C A).obj F).mapCocone (cofan.{w} J f)) where
  定义体: Sigma.desc fun i => Sigma.ι (F.obj ∘ (f i.1).obj) i.2 ≫ s.ι.app ⟨i.1⟩
  fac s i := Sigma.hom_ext _ _ fun i => by simp [cofan, Function.comp_def]
  uniq s m h := Sigma.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan, Function.comp_def]

Depends on / 依赖: F.obj, Sigma.desc
-/
def isColimitEvalMapCoconeCofan : IsColimit (((eval.{w} C A).obj F).mapCocone (cofan.{w} J f)) where
  desc s := Sigma.desc fun i => Sigma.ι (F.obj ∘ (f i.1).obj) i.2 ≫ s.ι.app ⟨i.1⟩
  fac s i := Sigma.hom_ext _ _ fun i => by simp [cofan, Function.comp_def]
  uniq s m h := Sigma.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan, Function.comp_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit (Discrete.functor f) ((eval.{w} C A).obj F)
  body: ⟨fun hc => ⟨IsColimit.ofIsoColimit (isColimitEvalMapCoconeCofan J f F)
    ((Cocone.functoriality _ _).mapIso ((isColimitCofan J f).uniqueUpToIso hc))⟩⟩

中文:
实例 :
  签名: 保持余极限 (离散.functor f) ((eval.{w} C A).obj F)
  定义体: ⟨fun hc => ⟨IsColimit.ofIsoColimit (isColimitEvalMapCoconeCofan J f F)
    ((Cocone.functoriality _ _).mapIso ((isColimitCofan J f).uniqueUpToIso hc))⟩⟩

Depends on / 依赖: Cocone, Cocone.functoriality, IsColimit, IsColimit.ofIsoColimit, functoriality, isColimitCofan, isColimitEvalMapCoconeCofan, mapIso, ofIsoColimit, uniqueUpToIso
-/
instance : PreservesColimit (Discrete.functor f) ((eval.{w} C A).obj F) :=
  ⟨fun hc => ⟨IsColimit.ofIsoColimit (isColimitEvalMapCoconeCofan J f F)
    ((Cocone.functoriality _ _).mapIso ((isColimitCofan J f).uniqueUpToIso hc))⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape (Discrete J) ((eval.{w} C A).obj F)
  body: preservesColimitsOfShape_of_discrete _

中文:
实例 :
  签名: 保持形状余极限 (离散 J) ((eval.{w} C A).obj F)
  定义体: preservesColimitsOfShape_of_discrete _

Depends on / 依赖: preservesColimitsOfShape_of_discrete
-/
instance : PreservesColimitsOfShape (Discrete J) ((eval.{w} C A).obj F) :=
  preservesColimitsOfShape_of_discrete _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev yoneda
  body: (eval _ _).obj yoneda

中文:
缩写 noncomputable
  签名: abbrev yoneda
  定义体: (eval _ _).obj yoneda
-/
protected noncomputable abbrev yoneda :
    FormalCoproduct.{v} C ⥤ Cᵒᵖ ⥤ Type v :=
  (eval _ _).obj yoneda

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev uliftYoneda
  body: (eval _ _).obj uliftYoneda

中文:
缩写 noncomputable
  签名: abbrev uliftYoneda
  定义体: (eval _ _).obj uliftYoneda
-/
protected noncomputable abbrev uliftYoneda :
    FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type (max w v) :=
  (eval _ _).obj uliftYoneda

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev shrinkYoneda [LocallySmall.{w} C]
  body: (eval _ _).obj shrinkYoneda

中文:
缩写 noncomputable
  签名: abbrev shrinkYoneda [LocallySmall.{w} C]
  定义体: (eval _ _).obj shrinkYoneda
-/
protected noncomputable abbrev shrinkYoneda [LocallySmall.{w} C] :
    FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type w :=
  (eval _ _).obj shrinkYoneda

end HasCoproducts

noncomputable section HasProducts

variable [HasProducts.{w} A] (C) (J : Type w) (f : J -> FormalCoproduct.{w} C) (F : Cᵒᵖ ⥤ A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evalOp` / `evalOp` 的定义

English:
definition evalOp
  signature: : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  body: { obj X := ∏ᶜ fun (i : X.unop.I) => F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i => Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i => α.app (op (f.unop.obj i)) }

中文:
定义 evalOp
  签名: : (Cᵒᵖ ⥤ A) ⥤ ((形式余积.{w} C)ᵒᵖ ⥤ A) where
  定义体: { obj X := ∏ᶜ fun (i : X.unop.I) => F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i => Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i => α.app (op (f.unop.obj i)) }
-/
@[simps!] def evalOp : (Cᵒᵖ ⥤ A) ⥤ ((FormalCoproduct.{w} C)ᵒᵖ ⥤ A) where
  obj F :=
    { obj X := ∏ᶜ fun (i : X.unop.I) => F.obj (op (X.unop.obj i))
      map f := Pi.lift fun i => Pi.π _ (f.unop.f i) ≫ F.map (f.unop.φ i).op }
  map α := { app f := Pi.map fun i => α.app (op (f.unop.obj i)) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evalOpCompInlIsoId` / `evalOpCompInlIsoId` 的定义

English:
definition evalOpCompInlIsoId
  signature: :
  body: NatIso.ofComponents fun F => NatIso.ofComponents fun x =>
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ => 𝟙 _, by aesop, by simp⟩

中文:
定义 evalOpCompInlIsoId
  签名: :
  定义体: NatIso.ofComponents fun F => NatIso.ofComponents fun x =>
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ => 𝟙 _, by aesop, by simp⟩
-/
@[simps!] def evalOpCompInlIsoId :
    evalOp C A ⋙ (whiskeringLeft _ _ A).obj (incl C).op ≅ Functor.id (Cᵒᵖ ⥤ A) :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun x =>
    ⟨Pi.π _ PUnit.unit, Pi.lift fun _ => 𝟙 _, by aesop, by simp⟩

variable {C A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitEvalMapConeCofanOp` / `isLimitEvalMapConeCofanOp` 的定义

English:
definition isLimitEvalMapConeCofanOp
  signature: : IsLimit (((evalOp.{w} C A).obj F).mapCone (cofan.{w} J f).op) where
  body: Pi.lift fun i => s.π.app ⟨i.1⟩ ≫ Pi.π _ i.2
  fac s i := Pi.hom_ext _ _ fun i => by simp [cofan]
  uniq s m h := Pi.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan]

中文:
定义 isLimitEvalMapConeCofanOp
  签名: : 是极限 (((evalOp.{w} C A).obj F).mapCone (cofan.{w} J f).op) where
  定义体: Pi.lift fun i => s.π.app ⟨i.1⟩ ≫ Pi.π _ i.2
  fac s i := Pi.hom_ext _ _ fun i => by simp [cofan]
  uniq s m h := Pi.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan]

Depends on / 依赖: Pi.lift
-/
def isLimitEvalMapConeCofanOp : IsLimit (((evalOp.{w} C A).obj F).mapCone (cofan.{w} J f).op) where
  lift s := Pi.lift fun i => s.π.app ⟨i.1⟩ ≫ Pi.π _ i.2
  fac s i := Pi.hom_ext _ _ fun i => by simp [cofan]
  uniq s m h := Pi.hom_ext _ _ fun ⟨i₁, i₂⟩ => by simp [← h, cofan]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit (Discrete.functor (op ∘ f)) ((evalOp.{w} C A).obj F)
  body: ⟨fun hc => ⟨IsLimit.ofIsoLimit (isLimitEvalMapConeCofanOp J f F) ((Cone.functoriality _ _).mapIso
    ((Cofan.IsColimit.op (isColimitCofan J f)).uniqueUpToIso hc))⟩⟩

中文:
实例 :
  签名: 保持极限 (离散.functor (op ∘ f)) ((evalOp.{w} C A).obj F)
  定义体: ⟨fun hc => ⟨IsLimit.ofIsoLimit (isLimitEvalMapConeCofanOp J f F) ((Cone.functoriality _ _).mapIso
    ((Cofan.IsColimit.op (isColimitCofan J f)).uniqueUpToIso hc))⟩⟩

Depends on / 依赖: Cofan.IsColimit.op, Cone.functoriality, IsColimit, IsLimit, IsLimit.ofIsoLimit, functoriality, isColimitCofan, isLimitEvalMapConeCofanOp, mapIso, ofIsoLimit, uniqueUpToIso
-/
instance : PreservesLimit (Discrete.functor (op ∘ f)) ((evalOp.{w} C A).obj F) :=
  ⟨fun hc => ⟨IsLimit.ofIsoLimit (isLimitEvalMapConeCofanOp J f F) ((Cone.functoriality _ _).mapIso
    ((Cofan.IsColimit.op (isColimitCofan J f)).uniqueUpToIso hc))⟩⟩

end HasProducts

end FormalCoproduct

end Limits

end CategoryTheory
