/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Attaching cells

Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
we introduce a structure `AttachCells g f` which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. It means that
there is a pushout diagram of the form
```
⨿ i, A (π i) -----> X₁
  | |f
  v v
⨿ i, B (π i) -----> X₂
```
In other words, the morphism `f` is a pushout of coproducts of morphisms
of the form `g a : A a ⟶ B a`, see `nonempty_attachCells_iff`.

See the file `Mathlib/AlgebraicTopology/RelativeCellComplex/Basic.lean` for transfinite compositions
of morphisms `f` with `AttachCells g f` structures.

-/

@[expose] public section

universe w' w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α -> C} (g : forall a, A a ⟶ B a)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

/--
Definition of `AttachCells` / `AttachCells` 的定义

English:
structure AttachCells
  parameters: where
  axioms and operations (11):
    - ι : Type w
    - π : ι -> α
    - cofan₁ : Cofan (fun i => A (π i))
    - cofan₂ : Cofan (fun i => B (π i))
    - isColimit₁ : IsColimit cofan₁
    - isColimit₂ : IsColimit cofan₂
    - m : cofan₁.pt ⟶ cofan₂.pt
    - hm((i : ι)) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i  [default: by cat_disch]
    - g₁ : cofan₁.pt ⟶ X₁
    - g₂ : cofan₂.pt ⟶ X₂
    - isPushout : IsPushout g₁ m f g₂

中文:
结构 AttachCells
  参数: where
  公理与运算 (11 个):
    - ι : 类型 w
    - π : ι -> α
    - cofan₁ : Cofan (fun i => A (π i))
    - cofan₂ : Cofan (fun i => B (π i))
    - isColimit₁ : 是余极限 cofan₁
    - isColimit₂ : 是余极限 cofan₂
    - m : cofan₁.pt ⟶ cofan₂.pt
    - hm((i : ι)) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i  [默认: by cat_disch]
    - g₁ : cofan₁.pt ⟶ X₁
    - g₂ : cofan₂.pt ⟶ X₂
    - isPushout : 是推出 g₁ m f g₂

Depends on / 依赖: cat_disch
-/
structure AttachCells where
  /-- the index type of the cells -/
  ι : Type w
  /-- for each `i : ι`, we shall attach a cell given by the morphism `g (π i)`. -/
  π : ι -> α
  /-- a colimit cofan which gives the coproduct of the object `A (π i)` -/
  cofan₁ : Cofan (fun i => A (π i))
  /-- a colimit cofan which gives the coproduct of the object `B (π i)` -/
  cofan₂ : Cofan (fun i => B (π i))
  /-- `cofan₁` is colimit -/
  isColimit₁ : IsColimit cofan₁
  /-- `cofan₂` is colimit -/
  isColimit₂ : IsColimit cofan₂
  /-- the coproduct of the maps `g (π i) : A (π i) ⟶ B (π i)` for all `i : ι`. -/
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i := by cat_disch
  /-- the top morphism of the pushout square -/
  g₁ : cofan₁.pt ⟶ X₁
  /-- the bottom morphism of the pushout square -/
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

attribute [reassoc (attr := simp)] hm

variable {g f} (c : AttachCells.{w} g f)

include c

/--
lemma `pushouts_coproducts` / 引理 `pushouts_coproducts`

English:
lemma pushouts_coproducts
  statement: (coproducts.{w} (ofHoms g)).pushouts f
  proof: by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ => by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ => by rw [IsColimit.fac]; exact c.hm i)
  rw [this]; rw [coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, 

中文:
引理 pushouts_coproducts
  结论: (coproducts.{w} (ofHoms g)).pushouts f
  证明: by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ => by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ => by rw [IsColimit.fac]; exact c.hm i)
  rw [this]; rw [coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, 

Depends on / 依赖: Cocone, Cocone.mk, Discrete, Discrete.natTrans, IsColimit, IsColimit.fac, c.cofan, c.hm, c.isColimit, c.isPushout, coproducts_iff, hom_ext, isPushout, natTrans
-/
lemma pushouts_coproducts : (coproducts.{w} (ofHoms g)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ => by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ => by rw [IsColimit.fac]; exact c.hm i)
  rw [this]; rw [coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i => ⟨_⟩⟩⟩

/--
Definition of `cell` / `cell` 的定义

English:
definition cell
  signature: (i : c.ι)
  body: c.cofan₂.inj i ≫ c.g₂

@[reassoc]

中文:
定义 cell
  签名: (i : c.ι)
  定义体: c.cofan₂.inj i ≫ c.g₂

@[reassoc]

Depends on / 依赖: c.cofan
-/
def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂

@[reassoc]
/--
lemma `cell_def` / 引理 `cell_def`

English:
lemma cell_def
  given: (i : c.ι)
  statement: c.cell i = c.cofan₂.inj i ≫ c.g₂
  proof: rfl

中文:
引理 cell_def
  条件: (i : c.ι)
  结论: c.cell i = c.cofan₂.inj i ≫ c.g₂
  证明: rfl
-/
lemma cell_def (i : c.ι) : c.cell i = c.cofan₂.inj i ≫ c.g₂ := rfl

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Z : C} {φ φ' : X₂ ⟶ Z}
  proof: by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

中文:
引理 hom_ext
  结论: {Z : C} {φ φ' : X₂ ⟶ Z}
  证明: by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, c.isColimit, c.isPushout.hom_ext, cell_def, hom_ext, isPushout
-/
lemma hom_ext {Z : C} {φ φ' : X₂ ⟶ Z}
    (h₀ : f ≫ φ = f ≫ φ') (h : forall i, c.cell i ≫ φ = c.cell i ≫ φ') :
    φ = φ' := by
  apply c.isPushout.hom_ext h₀
  apply Cofan.IsColimit.hom_ext c.isColimit₂
  simpa [cell_def] using h

set_option backward.isDefEq.respectTransparency false in
/-- If `f` and `f'` are isomorphic morphisms and the target of `f`
is obtained by attaching cells to the source of `f`,
then the same holds for `f'`. -/
@[simps]
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : Arrow.mk f ≅ Arrow.mk f')
  body: c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  g₁ := c.g₁ ≫ Arrow.leftFunc.map e.hom
  g₂ := c.g₂ ≫ Arrow.rightFunc.map e.hom
  isPushout :=
    c.isPushout.of_iso (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
   

中文:
定义 ofArrowIso
  签名: {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : 箭头.mk f ≅ 箭头.mk f')
  定义体: c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  g₁ := c.g₁ ≫ Arrow.leftFunc.map e.hom
  g₂ := c.g₂ ≫ Arrow.rightFunc.map e.hom
  isPushout :=
    c.isPushout.of_iso (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
   
-/
def ofArrowIso {Y₁ Y₂ : C} {f' : Y₁ ⟶ Y₂} (e : Arrow.mk f ≅ Arrow.mk f') :
    AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  g₁ := c.g₁ ≫ Arrow.leftFunc.map e.hom
  g₂ := c.g₂ ≫ Arrow.rightFunc.map e.hom
  isPushout :=
    c.isPushout.of_iso (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
      (Arrow.rightFunc.mapIso e) (by simp) (by simp) (by simp) (by simp)

/-- This definition allows the replacement of the `ι` field of
a `AttachCells g f` structure by an equivalent type. -/
@[simps]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {ι' : Type w'} (e : ι' ≃ c.ι)
  body: ι'
  π i' := c.π (e i')
  cofan₁ := Cofan.mk c.cofan₁.pt (fun i' => c.cofan₁.inj (e i'))
  cofan₂ := Cofan.mk c.cofan₂.pt (fun i' => c.cofan₂.inj (e i'))
  isColimit₁ := IsColimit.whiskerEquivalence (c.isColimit₁) (Discrete.equivalence e)
  isColimit₂ := IsColimit.whiskerEquivalence (c.isColimit₂) (

中文:
定义 reindex
  签名: {ι' : 类型 w'} (e : ι' ≃ c.ι)
  定义体: ι'
  π i' := c.π (e i')
  cofan₁ := Cofan.mk c.cofan₁.pt (fun i' => c.cofan₁.inj (e i'))
  cofan₂ := Cofan.mk c.cofan₂.pt (fun i' => c.cofan₂.inj (e i'))
  isColimit₁ := IsColimit.whiskerEquivalence (c.isColimit₁) (Discrete.equivalence e)
  isColimit₂ := IsColimit.whiskerEquivalence (c.isColimit₂) (
-/
def reindex {ι' : Type w'} (e : ι' ≃ c.ι) :
    AttachCells.{w'} g f where
  ι := ι'
  π i' := c.π (e i')
  cofan₁ := Cofan.mk c.cofan₁.pt (fun i' => c.cofan₁.inj (e i'))
  cofan₂ := Cofan.mk c.cofan₂.pt (fun i' => c.cofan₂.inj (e i'))
  isColimit₁ := IsColimit.whiskerEquivalence (c.isColimit₁) (Discrete.equivalence e)
  isColimit₂ := IsColimit.whiskerEquivalence (c.isColimit₂) (Discrete.equivalence e)
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  hm i' := c.hm (e i')
  isPushout := c.isPushout

section

variable {α' : Type t'} {A' B' : α' -> C} (g' : forall i', A' i' ⟶ B' i')
  (a : α -> α') (ha : forall (i : α), Arrow.mk (g i) ≅ Arrow.mk (g' (a i)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `reindexCellTypes` / `reindexCellTypes` 的定义

English:
definition reindexCellTypes
  signature: : AttachCells g' f where
  body: c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i => Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i => Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i => A (c.π i)) ≅
       

中文:
定义 reindexCellTypes
  签名: : AttachCells g' f where
  定义体: c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i => Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i => Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i => A (c.π i)) ≅
       
-/
def reindexCellTypes : AttachCells g' f where
  ι := c.ι
  π := a ∘ c.π
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun i => Arrow.leftFunc.map (ha (c.π i)).inv ≫ c.cofan₁.inj i)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun i => Arrow.rightFunc.map (ha (c.π i)).inv ≫ c.cofan₂.inj i)
  isColimit₁ := by
    let e : Discrete.functor (fun i => A (c.π i)) ≅
        Discrete.functor (fun i => A' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ => Arrow.leftFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₁ (Cofan.ext (Iso.refl _) (fun i => ?_)))
    simp [Cocone.precompose, e, Cofan.inj]
  isColimit₂ := by
    let e : Discrete.functor (fun i => B (c.π i)) ≅
        Discrete.functor (fun i => B' (a (c.π i))) :=
      Discrete.natIso (fun ⟨i⟩ => Arrow.rightFunc.mapIso (ha (c.π i)))
    refine (IsColimit.precomposeHomEquiv e _).1
      (IsColimit.ofIsoColimit c.isColimit₂ (Cofan.ext (Iso.refl _) (fun i => ?_)))
    simp [Cocone.precompose, e, Cofan.inj]
  m := c.m
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

end

end AttachCells

set_option backward.isDefEq.respectTransparency false in
open MorphismProperty in
/--
lemma `nonempty_attachCells_iff` / 引理 `nonempty_attachCells_iff`

English:
lemma nonempty_attachCells_iff
  proof: by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    rw [coproducts_iff] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (g

中文:
引理 nonempty_attachCells_iff
  证明: by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    rw [coproducts_iff] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (g

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.mk, Arrow.rightFunc.mapIso, c.pushouts_coproducts, choose_spec, coproducts_iff, eqToIso, leftFunc, mapIso, ofHoms_iff, pushouts_coproducts, rightFunc
-/
lemma nonempty_attachCells_iff :
    Nonempty (AttachCells.{w} g f) ↔ (coproducts.{w} (ofHoms g)).pushouts f := by
  constructor
  · rintro ⟨c⟩
    exact c.pushouts_coproducts
  · rintro ⟨Y₁, Y₂, m, g₁, g₂, h, sq⟩
    rw [coproducts_iff] at h
    obtain ⟨ι, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩ := h
    let π (i : ι) : α := ((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose
    let e (i : ι) : Arrow.mk (φ.app ⟨i⟩) ≅ Arrow.mk (g (π i)) :=
      eqToIso (((ofHoms_iff _ _).1 (hφ ⟨i⟩)).choose_spec)
    let e₁ (i : ι) : F₁.obj ⟨i⟩ ≅ A (π i) := Arrow.leftFunc.mapIso (e i)
    let e₂ (i : ι) : F₂.obj ⟨i⟩ ≅ B (π i) := Arrow.rightFunc.mapIso (e i)
    exact ⟨{
      ι := ι
      π := π
      cofan₁ := Cofan.mk c₁.pt (fun i => (e₁ i).inv ≫ c₁.ι.app ⟨i⟩)
      cofan₂ := Cofan.mk c₂.pt (fun i => (e₂ i).inv ≫ c₂.ι.app ⟨i⟩)
      isColimit₁ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ => e₁ i)) _).1
          (IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _) (by simp)))
      isColimit₂ :=
        (IsColimit.precomposeHomEquiv (Discrete.natIso (fun ⟨i⟩ => e₂ i)) _).1
          (IsColimit.ofIsoColimit h₂ (Cocone.ext (Iso.refl _) (by simp)))
      hm i := by simp [e₁, e₂]
      isPushout := sq, .. }⟩

end HomotopicalAlgebra
