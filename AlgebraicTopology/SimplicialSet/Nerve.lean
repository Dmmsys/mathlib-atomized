/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

@[expose] public section

open CategoryTheory Category Simplicial Opposite

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps -isSimp]
/--
Definition of `nerve` / `nerve` 的定义

English:
definition nerve
  signature: (C : Type u) [Category.{v} C]
  body: ComposableArrows C (Δ.unop.len)
  map f := ↾fun x => x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

中文:
定义 nerve
  签名: (C : 类型u) [范畴.{v} C]
  定义体: ComposableArrows C (Δ.unop.len)
  map f := ↾fun x => x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

Depends on / 依赖: ComposableArrows, unop.len
-/
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f := ↾fun x => x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [simp] nerve_obj

instance {C : Type*} [Category* C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
inferInstanceAs Category (ComposableArrows C (Δ.unop.len))

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

/-- Given a functor `C ⥤ D`, we obtain a morphism `nerve C ⟶ nerve D` of simplicial sets. -/
@[simps -isSimp]
/--
Definition of `nerveMap` / `nerveMap` 的定义

English:
definition nerveMap
  signature: {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
  body: { app _ := ↾fun X => (F.mapComposableArrows _).obj X }

中文:
定义 nerveMap
  签名: {C D : 类型u} [范畴.{v} C] [范畴.{v} D] (F : C ⥤ D)
  定义体: { app _ := ↾fun X => (F.mapComposableArrows _).obj X }

Depends on / 依赖: F.mapComposableArrows, mapComposableArrows
-/
def nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) : nerve C ⟶ nerve D :=
  { app _ := ↾fun X => (F.mapComposableArrows _).obj X }

/--
lemma `nerveMap_app_mk₀` / 引理 `nerveMap_app_mk₀`

English:
lemma nerveMap_app_mk₀
  given: (x : C)
  proof: ComposableArrows.ext₀ rfl

中文:
引理 nerveMap_app_mk₀
  条件: (x : C)
  证明: ComposableArrows.ext₀ rfl

Depends on / 依赖: ComposableArrows, ComposableArrows.ext
-/
lemma nerveMap_app_mk₀ (x : C) :
    (nerveMap F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `nerveMap_app_mk₁` / 引理 `nerveMap_app_mk₁`

English:
lemma nerveMap_app_mk₁
  given: {x y : C} (f : x ⟶ y)
  proof: ComposableArrows.ext₁ rfl rfl (by simp [nerveMap_app])

中文:
引理 nerveMap_app_mk₁
  条件: {x y : C} (f : x ⟶ y)
  证明: ComposableArrows.ext₁ rfl rfl (by simp [nerveMap_app])

Depends on / 依赖: ComposableArrows, ComposableArrows.ext, nerveMap_app
-/
lemma nerveMap_app_mk₁ {x y : C} (f : x ⟶ y) :
    (nerveMap F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMap_app])

end

/-- The nerve of a category, as a functor `Cat ⥤ SSet` -/
@[simps]
/--
Definition of `nerveFunctor` / `nerveFunctor` 的定义

English:
definition nerveFunctor
  signature: : Cat.{v, u} ⥤ SSet where
  body: nerve C
  map F := nerveMap F.toFunctor

中文:
定义 nerveFunctor
  签名: : Cat.{v, u} ⥤ SSet where
  定义体: nerve C
  map F := nerveMap F.toFunctor
-/
def nerveFunctor : Cat.{v, u} ⥤ SSet where
  obj C := nerve C
  map F := nerveMap F.toFunctor

/--
Definition of `nerveEquiv` / `nerveEquiv` 的定义

English:
definition nerveEquiv
  signature: {C : Type u} [Category.{v} C]
  body: f.obj ⟨0, by lia⟩
  invFun f := ComposableArrows.mk₀ f
  left_inv f := ComposableArrows.ext₀ rfl

中文:
定义 nerveEquiv
  签名: {C : 类型u} [范畴.{v} C]
  定义体: f.obj ⟨0, by lia⟩
  invFun f := ComposableArrows.mk₀ f
  left_inv f := ComposableArrows.ext₀ rfl

Depends on / 依赖: f.obj
-/
def nerveEquiv {C : Type u} [Category.{v} C] : ComposableArrows C 0 ≃ C where
  toFun f := f.obj ⟨0, by lia⟩
  invFun f := ComposableArrows.mk₀ f
  left_inv f := ComposableArrows.ext₀ rfl

namespace nerve

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: {n : Nat} (α : Type u) [Preorder α] (e : α ≃o Fin (n + 1))
  body: SimplexCategory.homEquivFunctor.trans
    { toFun F := F ⋙ e.symm.monotone.functor
      invFun F := F ⋙ e.monotone.functor
      left_inv F := Functor.ext (fun x => by simp)
      right_inv F := Functor.ext (fun x => by simp) }
  homEquiv_comp _ _ := rfl

中文:
定义 representableBy
  签名: {n : 自然数} (α : 类型u) [预序 α] (e : α ≃o 有限集 (n + 1))
  定义体: SimplexCategory.homEquivFunctor.trans
    { toFun F := F ⋙ e.symm.monotone.functor
      invFun F := F ⋙ e.monotone.functor
      left_inv F := Functor.ext (fun x => by simp)
      right_inv F := Functor.ext (fun x => by simp) }
  homEquiv_comp _ _ := rfl

Depends on / 依赖: SimplexCategory, SimplexCategory.homEquivFunctor.trans, homEquivFunctor
-/
def representableBy {n : Nat} (α : Type u) [Preorder α] (e : α ≃o Fin (n + 1)) :
    (nerve α).RepresentableBy ⦋n⦌ where
  homEquiv := SimplexCategory.homEquivFunctor.trans
    { toFun F := F ⋙ e.symm.monotone.functor
      invFun F := F ⋙ e.monotone.functor
      left_inv F := Functor.ext (fun x => by simp)
      right_inv F := Functor.ext (fun x => by simp) }
  homEquiv_comp _ _ := rfl

variable {C : Type u} [Category.{v} C] {n : Nat}

/--
lemma `δ_obj` / 引理 `δ_obj`

English:
lemma δ_obj
  given: {n : Nat} (i : Fin (n + 2)) (x : ComposableArrows C (n + 1)) (j : Fin (n + 1))
  proof: rfl

中文:
引理 δ_obj
  条件: {n : 自然数} (i : 有限集 (n + 2)) (x : ComposableArrows C (n + 1)) (j : 有限集 (n + 1))
  证明: rfl
-/
lemma δ_obj {n : Nat} (i : Fin (n + 2)) (x : ComposableArrows C (n + 1)) (j : Fin (n + 1)) :
    ((nerve C).δ i x).obj j = x.obj (i.succAbove j) :=
  rfl

/--
lemma `σ_obj` / 引理 `σ_obj`

English:
lemma σ_obj
  given: {n : Nat} (i : Fin (n + 1)) (x : ComposableArrows C n) (j : Fin (n + 2))
  proof: rfl

中文:
引理 σ_obj
  条件: {n : 自然数} (i : 有限集 (n + 1)) (x : ComposableArrows C n) (j : 有限集 (n + 2))
  证明: rfl
-/
lemma σ_obj {n : Nat} (i : Fin (n + 1)) (x : ComposableArrows C n) (j : Fin (n + 2)) :
    ((nerve C).σ i x).obj j = x.obj (i.predAbove j) :=
  rfl

/--
lemma `δ₀_eq` / 引理 `δ₀_eq`

English:
lemma δ₀_eq
  given: {x : ComposableArrows C (n + 1)}
  statement: (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀
  proof: rfl

中文:
引理 δ₀_eq
  条件: {x : ComposableArrows C (n + 1)}
  结论: (nerve C).δ (0 : 有限集 (n + 2)) x = x.δ₀
  证明: rfl
-/
lemma δ₀_eq {x : ComposableArrows C (n + 1)} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `σ₀_mk₀_eq` / 引理 `σ₀_mk₀_eq`

English:
lemma σ₀_mk₀_eq
  given: (x : C)
  statement: (nerve C).σ (0 : Fin 1) (.mk₀ x) = .mk₁ (𝟙 x)
  proof: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

中文:
引理 σ₀_mk₀_eq
  条件: (x : C)
  结论: (nerve C).σ (0 : 有限集 1) (.mk₀ x) = .mk₁ (𝟙 x)
  证明: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext
-/
lemma σ₀_mk₀_eq (x : C) : (nerve C).σ (0 : Fin 1) (.mk₀ x) = .mk₁ (𝟙 x) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

section

variable {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `δ₂_mk₂_eq` / 定理 `δ₂_mk₂_eq`

English:
theorem δ₂_mk₂_eq
  statement: (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f
  proof: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

中文:
定理 δ₂_mk₂_eq
  结论: (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f
  证明: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext
-/
theorem δ₂_mk₂_eq : (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `δ₀_mk₂_eq` / 定理 `δ₀_mk₂_eq`

English:
theorem δ₀_mk₂_eq
  statement: (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g
  proof: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

中文:
定理 δ₀_mk₂_eq
  结论: (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g
  证明: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext
-/
theorem δ₀_mk₂_eq : (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `δ₁_mk₂_eq` / 定理 `δ₁_mk₂_eq`

English:
theorem δ₁_mk₂_eq
  statement: (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g)
  proof: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

中文:
定理 δ₁_mk₂_eq
  结论: (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g)
  证明: ComposableArrows.ext₁ rfl rfl (by simp; rfl)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext
-/
theorem δ₁_mk₂_eq : (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

end

@[ext]
/--
lemma `ext_of_isThin` / 引理 `ext_of_isThin`

English:
lemma ext_of_isThin
  statement: [Quiver.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).obj n}
  proof: ComposableArrows.ext (by simp [h]) (by subsingleton)

中文:
引理 ext_of_isThin
  结论: [箭图.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).obj n}
  证明: ComposableArrows.ext (by simp [h]) (by subsingleton)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext, subsingleton
-/
lemma ext_of_isThin [Quiver.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).obj n}
    (h : x.obj = y.obj) :
    x = y :=
  ComposableArrows.ext (by simp [h]) (by subsingleton)

open SSet

@[simp]
/--
lemma `left_edge` / 引理 `left_edge`

English:
lemma left_edge
  given: {x y : ComposableArrows C 0} (e : (nerve C).Edge x y)
  proof: by
  simp only [← e.src_eq]
  rfl

@[simp]

中文:
引理 left_edge
  条件: {x y : ComposableArrows C 0} (e : (nerve C).边 x y)
  证明: by
  simp only [← e.src_eq]
  rfl

@[simp]

Depends on / 依赖: e.edge, e.src_eq, nerveEquiv, src_eq
-/
lemma left_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.left (n := 1) e.edge = nerveEquiv x := by
  simp only [← e.src_eq]
  rfl

@[simp]
/--
lemma `right_edge` / 引理 `right_edge`

English:
lemma right_edge
  given: {x y : ComposableArrows C 0} (e : (nerve C).Edge x y)
  proof: by
  simp only [← e.tgt_eq]
  rfl

中文:
引理 right_edge
  条件: {x y : ComposableArrows C 0} (e : (nerve C).边 x y)
  证明: by
  simp only [← e.tgt_eq]
  rfl

Depends on / 依赖: e.edge, e.tgt_eq, nerveEquiv, tgt_eq
-/
lemma right_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.right (n := 1) e.edge = nerveEquiv y := by
  simp only [← e.tgt_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ₂_two` / 引理 `δ₂_two`

English:
lemma δ₂_two
  given: (x : ComposableArrows C 2)
  proof: ComposableArrows.ext₁ rfl rfl (by cat_disch)

中文:
引理 δ₂_two
  条件: (x : ComposableArrows C 2)
  证明: ComposableArrows.ext₁ rfl rfl (by cat_disch)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext, cat_disch
-/
lemma δ₂_two (x : ComposableArrows C 2) :
    (nerve C).δ 2 x = .mk₁ (x.map' 0 1) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ₂_zero` / 引理 `δ₂_zero`

English:
lemma δ₂_zero
  given: (x : ComposableArrows C 2)
  proof: ComposableArrows.ext₁ rfl rfl (by cat_disch)

中文:
引理 δ₂_zero
  条件: (x : ComposableArrows C 2)
  证明: ComposableArrows.ext₁ rfl rfl (by cat_disch)

Depends on / 依赖: ComposableArrows, ComposableArrows.ext, cat_disch
-/
lemma δ₂_zero (x : ComposableArrows C 2) :
    (nerve C).δ 0 x = .mk₁ (x.map' 1 2) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

section

attribute [local ext (iff := false)] ComposableArrows.ext₀ ComposableArrows.ext₁

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bijection between edges in the nerve of category and morphisms in the category. -/
@[simps -isSimp]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {x y : ComposableArrows C 0}
  body: eqToHom (by simp) ≫ e.edge.hom ≫ eqToHom (by simp)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by cat_disch
  right_inv f := by simp

中文:
定义 homEquiv
  签名: {x y : ComposableArrows C 0}
  定义体: eqToHom (by simp) ≫ e.edge.hom ≫ eqToHom (by simp)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by cat_disch
  right_inv f := by simp

Depends on / 依赖: e.edge.hom, eqToHom
-/
def homEquiv {x y : ComposableArrows C 0} :
    (nerve C).Edge x y ≃ (nerveEquiv x ⟶ nerveEquiv y) where
  toFun e := eqToHom (by simp) ≫ e.edge.hom ≫ eqToHom (by simp)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by cat_disch
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk₁_homEquiv_apply` / 引理 `mk₁_homEquiv_apply`

English:
lemma mk₁_homEquiv_apply
  given: {x y : ComposableArrows C 0} (e : (nerve C).Edge x y)
  proof: by
  simp [homEquiv, ComposableArrows.mk₁_eqToHom_comp, ComposableArrows.mk₁_comp_eqToHom]

中文:
引理 mk₁_homEquiv_apply
  条件: {x y : ComposableArrows C 0} (e : (nerve C).边 x y)
  证明: by
  simp [homEquiv, ComposableArrows.mk₁_eqToHom_comp, ComposableArrows.mk₁_comp_eqToHom]

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, homEquiv
-/
lemma mk₁_homEquiv_apply {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.mk₁ (homEquiv e) = ComposableArrows.mk₁ e.edge.hom := by
  simp [homEquiv, ComposableArrows.mk₁_eqToHom_comp, ComposableArrows.mk₁_comp_eqToHom]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `edgeMk` / `edgeMk` 的定义

English:
definition edgeMk
  signature: {x y : C} (f : x ⟶ y)
  body: Edge.mk (ComposableArrows.mk₁ f)

@[simp]

中文:
定义 edgeMk
  签名: {x y : C} (f : x ⟶ y)
  定义体: Edge.mk (ComposableArrows.mk₁ f)

@[simp]

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, Edge.mk
-/
def edgeMk {x y : C} (f : x ⟶ y) : (nerve C).Edge (nerveEquiv.symm x) (nerveEquiv.symm y) :=
  Edge.mk (ComposableArrows.mk₁ f)

@[simp]
/--
lemma `edgeMk_edge` / 引理 `edgeMk_edge`

English:
lemma edgeMk_edge
  given: {x y : C} (f : x ⟶ y)
  statement: (edgeMk f).edge = ComposableArrows.mk₁ f
  proof: rfl

中文:
引理 edgeMk_edge
  条件: {x y : C} (f : x ⟶ y)
  结论: (edgeMk f).edge = ComposableArrows.mk₁ f
  证明: rfl
-/
lemma edgeMk_edge {x y : C} (f : x ⟶ y) : (edgeMk f).edge = ComposableArrows.mk₁ f := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `edgeMk_id` / 引理 `edgeMk_id`

English:
lemma edgeMk_id
  given: (x : C)
  statement: edgeMk (𝟙 x) = .id _
  proof: by cat_disch

中文:
引理 edgeMk_id
  条件: (x : C)
  结论: edgeMk (𝟙 x) = .id _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma edgeMk_id (x : C) : edgeMk (𝟙 x) = .id _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `edgeMk_surjective` / 引理 `edgeMk_surjective`

English:
lemma edgeMk_surjective
  given: {x y : C}
  proof: fun e => ⟨eqToHom (by simp) ≫ homEquiv e ≫ eqToHom (by simp), by cat_disch⟩

@[simp]

中文:
引理 edgeMk_surjective
  条件: {x y : C}
  证明: fun e => ⟨eqToHom (by simp) ≫ homEquiv e ≫ eqToHom (by simp), by cat_disch⟩

@[simp]

Depends on / 依赖: cat_disch, eqToHom, homEquiv
-/
lemma edgeMk_surjective {x y : C} :
    Function.Surjective (edgeMk : (x ⟶ y) -> _) :=
  fun e => ⟨eqToHom (by simp) ≫ homEquiv e ≫ eqToHom (by simp), by cat_disch⟩

@[simp]
/--
lemma `homEquiv_edgeMk` / 引理 `homEquiv_edgeMk`

English:
lemma homEquiv_edgeMk
  given: {x y : C} (f : x ⟶ y)
  proof: homEquiv.symm.injective (by cat_disch)

中文:
引理 homEquiv_edgeMk
  条件: {x y : C} (f : x ⟶ y)
  证明: homEquiv.symm.injective (by cat_disch)

Depends on / 依赖: cat_disch, homEquiv, homEquiv.symm.injective, injective
-/
lemma homEquiv_edgeMk {x y : C} (f : x ⟶ y) :
    homEquiv (edgeMk f) = f :=
  homEquiv.symm.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homEquiv_id` / 引理 `homEquiv_id`

English:
lemma homEquiv_id
  given: (x : ComposableArrows C 0)
  proof: by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [homEquiv]
  cat_disch

中文:
引理 homEquiv_id
  条件: (x : ComposableArrows C 0)
  证明: by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [homEquiv]
  cat_disch

Depends on / 依赖: cat_disch, homEquiv, nerveEquiv, nerveEquiv.symm.surjective, surjective
-/
lemma homEquiv_id (x : ComposableArrows C 0) :
    homEquiv (Edge.id x) = 𝟙 _ := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [homEquiv]
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `nonempty_compStruct_iff` / 引理 `nonempty_compStruct_iff`

English:
lemma nonempty_compStruct_iff
  statement: {x₀ x₁ x₂ : C}
  proof: by
  let h' : Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk (f₀₁ ≫ f₁₂)) :=
      Edge.CompStruct.mk (ComposableArrows.mk₂ f₀₁ f₁₂)
        (by cat_disch) (by cat_disch) (by cat_disch)
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨by rwa [← h]⟩⟩
  rw [← Arrow.mk_inj]
  apply ComposableArrows.arrowEquiv.sym

中文:
引理 nonempty_compStruct_iff
  结论: {x₀ x₁ x₂ : C}
  证明: by
  let h' : Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk (f₀₁ ≫ f₁₂)) :=
      Edge.CompStruct.mk (ComposableArrows.mk₂ f₀₁ f₁₂)
        (by cat_disch) (by cat_disch) (by cat_disch)
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨by rwa [← h]⟩⟩
  rw [← Arrow.mk_inj]
  apply ComposableArrows.arrowEquiv.sym

Depends on / 依赖: Arrow.mk_inj, CompStruct, ComposableArrows, ComposableArrows.arrowEquiv.symm.injective, ComposableArrows.mk, Edge.CompStruct, Edge.CompStruct.mk, arrowEquiv, cat_disch, convert_to, edgeMk, edgeMk_e, h.simplex, injective, mk_inj, simplex
-/
lemma nonempty_compStruct_iff {x₀ x₁ x₂ : C}
    (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀₂ : x₀ ⟶ x₂) :
    Nonempty (Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk f₀₂)) ↔
      f₀₁ ≫ f₁₂ = f₀₂ := by
  let h' : Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk (f₀₁ ≫ f₁₂)) :=
      Edge.CompStruct.mk (ComposableArrows.mk₂ f₀₁ f₁₂)
        (by cat_disch) (by cat_disch) (by cat_disch)
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨by rwa [← h]⟩⟩
  rw [← Arrow.mk_inj]
  apply ComposableArrows.arrowEquiv.symm.injective
  convert_to! (nerve C).δ 1 h'.simplex = (nerve C).δ 1 h.simplex
  · exact (h'.d₁).symm
  · exact (h.d₁).symm
  · have h₀ := h.d₀
    have h₂ := h.d₂
    have h'₀ := h'.d₀
    have h'₂ := h'.d₂
    simp only [δ₂_zero, δ₂_two, edgeMk_edge] at h₀ h₂ h'₀ h'₂
    exact congr_arg _ (ComposableArrows.ext₂_of_arrow
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₂, h'₂, ← h₂]))
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₀, h'₀, ← h₀])))

/--
lemma `homEquiv_comp` / 引理 `homEquiv_comp`

English:
lemma homEquiv_comp
  statement: {x₀ x₁ x₂ : ComposableArrows C 0}
  proof: by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
  conv

中文:
引理 homEquiv_comp
  结论: {x₀ x₁ x₂ : ComposableArrows C 0}
  证明: by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
  conv

Depends on / 依赖: convert, edgeMk_surjective, homEquiv_edgeMk, nerve.nonempty_compStruct_iff, nerveEquiv, nerveEquiv.symm.surjective, nonempty_compStruct_iff, surjective
-/
lemma homEquiv_comp {x₀ x₁ x₂ : ComposableArrows C 0}
    {e₀₁ : (nerve C).Edge x₀ x₁}
    {e₁₂ : (nerve C).Edge x₁ x₂} {e₀₂ : (nerve C).Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homEquiv e₀₁ ≫ homEquiv e₁₂ = homEquiv e₀₂ := by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
  convert! (nerve.nonempty_compStruct_iff _ _ _).1 ⟨h⟩ <;> apply homEquiv_edgeMk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `σ_zero_nerveEquiv_symm` / 引理 `σ_zero_nerveEquiv_symm`

English:
lemma σ_zero_nerveEquiv_symm
  given: (x : C)
  proof: by
  cat_disch

中文:
引理 σ_zero_nerveEquiv_symm
  条件: (x : C)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma σ_zero_nerveEquiv_symm (x : C) :
    (nerve C).σ 0 (nerveEquiv.symm x) = ComposableArrows.mk₁ (𝟙 x) := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `homEquiv_edgeMk_map_nerveMap` / 引理 `homEquiv_edgeMk_map_nerveMap`

English:
lemma homEquiv_edgeMk_map_nerveMap
  statement: {D : Type u} [Category.{v} D] {x y : C}
  proof: by
  simp [homEquiv, nerveMap_app]

中文:
引理 homEquiv_edgeMk_map_nerveMap
  结论: {D : 类型u} [范畴.{v} D] {x y : C}
  证明: by
  simp [homEquiv, nerveMap_app]

Depends on / 依赖: homEquiv, nerveMap_app
-/
lemma homEquiv_edgeMk_map_nerveMap {D : Type u} [Category.{v} D] {x y : C}
    (f : x ⟶ y) (F : C ⥤ D) :
    dsimp% homEquiv ((edgeMk f).map (nerveMap F)) = F.map f := by
  simp [homEquiv, nerveMap_app]

end

end nerve

end CategoryTheory

/-- The functor `PartOrd ⥤ SSet` which sends a partially ordered type to its nerve. -/
@[simps]
/--
Definition of `PartOrd.nerveFunctor` / `PartOrd.nerveFunctor` 的定义

English:
definition PartOrd.nerveFunctor
  signature: : PartOrd.{u} ⥤ SSet.{u} where
  body: nerve X
  map f := nerveMap f.hom.monotone.functor

中文:
定义 偏序.nerveFunctor
  签名: : 偏序.{u} ⥤ SSet.{u} where
  定义体: nerve X
  map f := nerveMap f.hom.monotone.functor
-/
def PartOrd.nerveFunctor : PartOrd.{u} ⥤ SSet.{u} where
  obj X := nerve X
  map f := nerveMap f.hom.monotone.functor
