/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The factorization axiom

In this file, we introduce a type-class `HasFactorization W₁ W₂`, which, given
two classes of morphisms `W₁` and `W₂` in a category `C`, asserts that any morphism
in `C` can be factored as a morphism in `W₁` followed by a morphism in `W₂`. The data
of such factorizations can be packaged in the type `FactorizationData W₁ W₂`.

This shall be used in the formalization of model categories for which the CM5 axiom
asserts that any morphism can be factored as a cofibration followed by a trivial
fibration (or a trivial cofibration followed by a fibration).

We also provide a structure `FunctorialFactorizationData W₁ W₂` which contains
the data of a functorial factorization as above. With this design, when we
formalize certain constructions (e.g. cylinder objects in model categories),
we may first construct them using the data `data : FactorizationData W₁ W₂`.
Without duplication of code, it shall be possible to show these cylinders
are functorial when a term `data : FunctorialFactorizationData W₁ W₂` is available,
the existence of which is asserted in the type-class `HasFunctorialFactorization W₁ W₂`.

We also introduce the class `W₁.comp W₂` of morphisms of the form `i ≫ p` with `W₁ i`
and `W₂ p` and show that `W₁.comp W₂ = ⊤` iff `HasFactorization W₁ W₂` holds (this
is `MorphismProperty.comp_eq_top_iff`).

-/

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C D : Type*} [Category* C] [Category* D] (W₁ W₂ : MorphismProperty C)

/--
Definition of `MapFactorizationData` / `MapFactorizationData` 的定义

English:
structure MapFactorizationData
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (6):
    - Z : C
    - i : X ⟶ Z
    - p : Z ⟶ Y
    - fac : i ≫ p = f  [default: by cat_disch]
    - hi : W₁ i
    - hp : W₂ p

中文:
结构 MapFactorizationData
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (6 个):
    - Z : C
    - i : X ⟶ Z
    - p : Z ⟶ Y
    - fac : i ≫ p = f  [默认: by cat_disch]
    - hi : W₁ i
    - hp : W₂ p

Depends on / 依赖: cat_disch
-/
structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  /-- the intermediate object in the factorization -/
  Z : C
  /-- the first morphism in the factorization -/
  i : X ⟶ Z
  /-- the second morphism in the factorization -/
  p : Z ⟶ Y
  fac : i ≫ p = f := by cat_disch
  hi : W₁ i
  hp : W₂ p

namespace MapFactorizationData

attribute [reassoc (attr := simp)] fac

variable {X Y : C} (f : X ⟶ Y)

/-- The opposite of a factorization. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f)
  body: Opposite.op hf.Z
  i := hf.p.op
  p := hf.i.op
  fac := Quiver.Hom.unop_inj (by simp)
  hi := hf.hp
  hp := hf.hi

中文:
定义 op
  签名: {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f)
  定义体: Opposite.op hf.Z
  i := hf.p.op
  p := hf.i.op
  fac := Quiver.Hom.unop_inj (by simp)
  hi := hf.hp
  hp := hf.hi

Depends on / 依赖: Opposite, Opposite.op, hf.Z
-/
def op {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.op W₁.op f.op where
  Z := Opposite.op hf.Z
  i := hf.p.op
  p := hf.i.op
  fac := Quiver.Hom.unop_inj (by simp)
  hi := hf.hp
  hp := hf.hi

/-- The factorization obtained from a factorization in the opposite category. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {W₁ W₂ : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y}
  body: φ.Z.unop
  i := φ.p.unop
  p := φ.i.unop
  hi := φ.hp
  hp := φ.hi
  fac := by simp [← unop_comp]

中文:
定义 unop
  签名: {W₁ W₂ : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y}
  定义体: φ.Z.unop
  i := φ.p.unop
  p := φ.i.unop
  hi := φ.hp
  hp := φ.hi
  fac := by simp [← unop_comp]
-/
protected def unop {W₁ W₂ : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y}
    (φ : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.unop W₁.unop f.unop where
  Z := φ.Z.unop
  i := φ.p.unop
  p := φ.i.unop
  hi := φ.hp
  hp := φ.hi
  fac := by simp [← unop_comp]

/-- The bijection between factorizations in `C` and factorizations in `Cᵒᵖ`. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y}
  body: φ.op
  invFun φ := φ.unop

中文:
定义 opEquiv
  签名: {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y}
  定义体: φ.op
  invFun φ := φ.unop
-/
def opEquiv {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    MapFactorizationData W₁ W₂ f ≃ MapFactorizationData W₂.op W₁.op f.op where
  toFun φ := φ.op
  invFun φ := φ.unop

end MapFactorizationData

/--
Definition of `FactorizationData` / `FactorizationData` 的定义

English:
abbreviation FactorizationData
  body: forall {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

中文:
缩写 FactorizationData
  定义体: forall {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

Depends on / 依赖: MapFactorizationData
-/
abbrev FactorizationData := forall {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

/--
Definition of `HasFactorization` / `HasFactorization` 的定义

English:
class HasFactorization
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_mapFactorizationData({X Y : C} (f : X ⟶ Y)) : Nonempty (MapFactorizationData W₁ W₂ f)

中文:
类 有分解
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_mapFactorizationData({X Y : C} (f : X ⟶ Y)) : 非空 (MapFactorizationData W₁ W₂ f)
-/
class HasFactorization : Prop where
  nonempty_mapFactorizationData {X Y : C} (f : X ⟶ Y) : Nonempty (MapFactorizationData W₁ W₂ f)

/--
Definition of `factorizationData` / `factorizationData` 的定义

English:
definition factorizationData
  signature: [HasFactorization W₁ W₂]
  body: fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)

中文:
定义 factorizationData
  签名: [有分解 W₁ W₂]
  定义体: fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)

Depends on / 依赖: HasFactorization, HasFactorization.nonempty_mapFactorizationData, Nonempty, Nonempty.some, nonempty_mapFactorizationData
-/
noncomputable def factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂ :=
  fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFactorization
  signature: W₁ W₂] : HasFactorization W₂.op W₁.op where
  body: ⟨(factorizationData W₁ W₂ f.unop).op⟩

中文:
实例 [有分解
  签名: W₁ W₂] : 有分解 W₂.op W₁.op where
  定义体: ⟨(factorizationData W₁ W₂ f.unop).op⟩

Depends on / 依赖: f.unop, factorizationData
-/
instance [HasFactorization W₁ W₂] : HasFactorization W₂.op W₁.op where
  nonempty_mapFactorizationData f := ⟨(factorizationData W₁ W₂ f.unop).op⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : MorphismProperty C
  body: fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)

中文:
定义 comp
  签名: : MorphismProperty C
  定义体: fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)

Depends on / 依赖: MapFactorizationData, Nonempty
-/
def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)

/--
lemma `comp_eq_top_iff` / 引理 `comp_eq_top_iff`

English:
lemma comp_eq_top_iff
  statement: W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂
  proof: by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩

中文:
引理 comp_eq_top_iff
  结论: W₁.comp W₂ = ⊤ ↔ 有分解 W₁ W₂
  证明: by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩

Depends on / 依赖: factorizationData, iff_true, this.some, top_apply
-/
lemma comp_eq_top_iff : W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂ := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩

/--
Definition of `FunctorialFactorizationData` / `FunctorialFactorizationData` 的定义

English:
structure FunctorialFactorizationData
  parameters: where
  axioms and operations (6):
    - Z : Arrow C ⥤ C
    - i : Arrow.leftFunc ⟶ Z
    - p : Z ⟶ Arrow.rightFunc
    - fac : i ≫ p = Arrow.leftToRight  [default: by cat_disch]
    - hi((f : Arrow C)) : W₁ (i.app f)
    - hp((f : Arrow C)) : W₂ (p.app f)

中文:
结构 FunctorialFactorizationData
  参数: where
  公理与运算 (6 个):
    - Z : 箭头 C ⥤ C
    - i : 箭头.leftFunc ⟶ Z
    - p : Z ⟶ 箭头.rightFunc
    - fac : i ≫ p = 箭头.leftToRight  [默认: by cat_disch]
    - hi((f : 箭头 C)) : W₁ (i.app f)
    - hp((f : 箭头 C)) : W₂ (p.app f)

Depends on / 依赖: cat_disch, i.app, p.app
-/
structure FunctorialFactorizationData where
  /-- the intermediate objects in the factorizations -/
  Z : Arrow C ⥤ C
  /-- the first morphism in the factorizations -/
  i : Arrow.leftFunc ⟶ Z
  /-- the second morphism in the factorizations -/
  p : Z ⟶ Arrow.rightFunc
  fac : i ≫ p = Arrow.leftToRight := by cat_disch
  hi (f : Arrow C) : W₁ (i.app f)
  hp (f : Arrow C) : W₂ (p.app f)

namespace FunctorialFactorizationData

variable {W₁ W₂}
variable (data : FunctorialFactorizationData W₁ W₂)

attribute [reassoc (attr := simp)] fac

@[reassoc (attr := simp)]
/--
lemma `fac_app` / 引理 `fac_app`

English:
lemma fac_app
  given: {f : Arrow C}
  statement: data.i.app f ≫ data.p.app f = f.hom
  proof: by
  rw [← NatTrans.comp_app]; rw [fac]; rw [Arrow.leftToRight_app]

中文:
引理 fac_app
  条件: {f : 箭头 C}
  结论: data.i.app f ≫ data.p.app f = f.hom
  证明: by
  rw [← NatTrans.comp_app]; rw [fac]; rw [Arrow.leftToRight_app]

Depends on / 依赖: Arrow.leftToRight_app, NatTrans, NatTrans.comp_app, comp_app, leftToRight_app
-/
lemma fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom := by
  rw [← NatTrans.comp_app]; rw [fac]; rw [Arrow.leftToRight_app]

/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {W₁' W₂' : MorphismProperty C} (le₁ : W₁ <= W₁') (le₂ : W₂ <= W₂')
  body: data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)

中文:
定义 ofLE
  签名: {W₁' W₂' : MorphismProperty C} (le₁ : W₁ <= W₁') (le₂ : W₂ <= W₂')
  定义体: data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)

Depends on / 依赖: data.Z
-/
def ofLE {W₁' W₂' : MorphismProperty C} (le₁ : W₁ <= W₁') (le₂ : W₂ <= W₂') :
    FunctorialFactorizationData W₁' W₂' where
  Z := data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `factorizationData` / `factorizationData` 的定义

English:
definition factorizationData
  signature: : FactorizationData W₁ W₂
  body: fun f =>
  { Z := data.Z.obj (Arrow.mk f)
    i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }

中文:
定义 factorizationData
  签名: : FactorizationData W₁ W₂
  定义体: fun f =>
  { Z := data.Z.obj (Arrow.mk f)
    i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }
-/
def factorizationData : FactorizationData W₁ W₂ := fun f =>
  { Z := data.Z.obj (Arrow.mk f)
    i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)

/--
Definition of `mapZ` / `mapZ` 的定义

English:
definition mapZ
  signature: : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z
  body: data.Z.map φ

#adaptation_note

中文:
定义 mapZ
  签名: : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z
  定义体: data.Z.map φ

#adaptation_note

Depends on / 依赖: data.Z.map
-/
def mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z := data.Z.map φ

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `i_mapZ` / 引理 `i_mapZ`

English:
lemma i_mapZ
  proof: (data.i.naturality φ).symm

#adaptation_note

中文:
引理 i_mapZ
  证明: (data.i.naturality φ).symm

#adaptation_note

Depends on / 依赖: F.map_distinguished_exact, L.map_distinguished, data.i.naturality, map_distinguished, map_distinguished_exact, naturality
-/
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `mapZ_p` / 引理 `mapZ_p`

English:
lemma mapZ_p
  proof: data.p.naturality φ

中文:
引理 mapZ_p
  证明: data.p.naturality φ

Depends on / 依赖: data.p.naturality, naturality
-/
lemma mapZ_p :
    data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationData f).p ≫ φ.right :=
  data.p.naturality φ

variable (f) in
@[simp]
/--
lemma `mapZ_id` / 引理 `mapZ_id`

English:
lemma mapZ_id
  statement: data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _
  proof: data.Z.map_id _

@[reassoc, simp]

中文:
引理 mapZ_id
  结论: data.mapZ (𝟙 (箭头.mk f)) = 𝟙 _
  证明: data.Z.map_id _

@[reassoc, simp]

Depends on / 依赖: data.Z.map_id, map_id
-/
lemma mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  data.Z.map_id _

@[reassoc, simp]
/--
lemma `mapZ_comp` / 引理 `mapZ_comp`

English:
lemma mapZ_comp
  given: {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h)
  proof: data.Z.map_comp _ _

中文:
引理 mapZ_comp
  条件: {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : 箭头.mk g ⟶ 箭头.mk h)
  证明: data.Z.map_comp _ _

Depends on / 依赖: data.Z.map_comp, map_comp
-/
lemma mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    data.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ :=
  data.Z.map_comp _ _

end

section

variable (J : Type*) [Category* J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `FunctorialFactorizationData.functorCategory`. -/
@[simps]
/--
Definition of `functorCategory.Z` / `functorCategory.Z` 的定义

English:
definition functorCategory.Z
  signature: : Arrow (J ⥤ C) ⥤ J ⥤ C where
  body: { obj j := (data.factorizationData (f.hom.app j)).Z
      map φ := data.mapZ (Arrow.homMk (f.left.map φ) (f.right.map φ))
      map_id j := by
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp _ _ := by
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app j := data.mapZ (Arrow.homMk (τ.left.app j) (τ.right.app j) (congr_app τ.w j))
      naturality _ _ _ := by
        dsimp
        rw [← data.mapZ_comp]; rw [← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1

中文:
定义 functorCategory.Z
  签名: : 箭头 (J ⥤ C) ⥤ J ⥤ C where
  定义体: { obj j := (data.factorizationData (f.hom.app j)).Z
      map φ := data.mapZ (Arrow.homMk (f.left.map φ) (f.right.map φ))
      map_id j := by
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp _ _ := by
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app j := data.mapZ (Arrow.homMk (τ.left.app j) (τ.right.app j) (congr_app τ.w j))
      naturality _ _ _ := by
        dsimp
        rw [← data.mapZ_comp]; rw [← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1

Depends on / 依赖: Arrow.homMk, congr_app, data.factorizationData, data.mapZ, data.mapZ_comp, data.mapZ_id, f.hom.app, f.left.map, f.right.map, factorizationData, left.app, mapZ_comp, mapZ_id, map_comp, map_id, naturality, right.app
-/
def functorCategory.Z : Arrow (J ⥤ C) ⥤ J ⥤ C where
  obj f :=
    { obj j := (data.factorizationData (f.hom.app j)).Z
      map φ := data.mapZ (Arrow.homMk (f.left.map φ) (f.right.map φ))
      map_id j := by
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp _ _ := by
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app j := data.mapZ (Arrow.homMk (τ.left.app j) (τ.right.app j) (congr_app τ.w j))
      naturality _ _ _ := by
        dsimp
        rw [← data.mapZ_comp]; rw [← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `functorCategory` / `functorCategory` 的定义

English:
definition functorCategory
  signature: :
  body: functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _

中文:
定义 functorCategory
  签名: :
  定义体: functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _

Depends on / 依赖: F.IsHomological, IsHomological, functorCategory, functorCategory.Z
-/
def functorCategory :
    FunctorialFactorizationData (W₁.functorCategory J) (W₂.functorCategory J) where
  Z := functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _

end

end FunctorialFactorizationData

/--
Definition of `HasFunctorialFactorization` / `HasFunctorialFactorization` 的定义

English:
class HasFunctorialFactorization
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)

中文:
类 有FunctorialFactorization
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_functorialFactorizationData : 非空 (FunctorialFactorizationData W₁ W₂)

Depends on / 依赖: Additive, F.Additive, F.IsHomological, IsHomological
-/
class HasFunctorialFactorization : Prop where
  nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)

/--
Definition of `functorialFactorizationData` / `functorialFactorizationData` 的定义

English:
definition functorialFactorizationData
  signature: [HasFunctorialFactorization W₁ W₂]
  body: Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)

中文:
定义 functorialFactorizationData
  签名: [有FunctorialFactorization W₁ W₂]
  定义体: Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)

Depends on / 依赖: HasFunctorialFactorization, HasFunctorialFactorization.nonempty_functorialFactorizationData, Nonempty, Nonempty.some, nonempty_functorialFactorizationData
-/
noncomputable def functorialFactorizationData [HasFunctorialFactorization W₁ W₂] :
    FunctorialFactorizationData W₁ W₂ :=
  Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFunctorialFactorization
  signature: W₁ W₂] : HasFactorization W₁ W₂ where
  body: ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩

中文:
实例 [有FunctorialFactorization
  签名: W₁ W₂] : 有分解 W₁ W₂ where
  定义体: ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩

Depends on / 依赖: factorizationData, functorialFactorizationData
-/
instance [HasFunctorialFactorization W₁ W₂] : HasFactorization W₁ W₂ where
  nonempty_mapFactorizationData f := ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFunctorialFactorization
  signature: W₁ W₂] (J
  body: ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩

中文:
实例 [有FunctorialFactorization
  签名: W₁ W₂] (J
  定义体: ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩

Depends on / 依赖: functorCategory, functorialFactorizationData
-/
instance [HasFunctorialFactorization W₁ W₂] (J : Type*) [Category* J] :
    HasFunctorialFactorization (W₁.functorCategory J) (W₂.functorCategory J) :=
  ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩

set_option backward.defeqAttrib.useBackward true in
variable {W₁ W₂} in
/--
Definition of `MapFactorizationData.ofIsEquivalence` / `MapFactorizationData.ofIsEquivalence` 的定义

English:
definition MapFactorizationData.ofIsEquivalence
  signature: {F : D ⥤ C}
  body: F.objPreimage h.Z
  i := F.preimage (h.i ≫ (F.objObjPreimageIso h.Z).inv)
  p := F.preimage ((F.objObjPreimageIso h.Z).hom ≫ h.p)
  hi := by
    refine (W₁.arrow_mk_iso_iff ?_).1 h.hi
    refine Arrow.isoMk (Iso.refl _) (F.objObjPreimageIso h.Z).symm ?_
    simp [F.map_preimage]
  hp := by
    refine (W₂.arrow_mk_iso_iff ?_).1 h.hp
    refine Arrow.isoMk (F.objObjPreimageIso h.Z).symm (Iso.refl _) ?_
    simp [F.map_preimage]
  fac := F.map_injective (by simp)

中文:
定义 MapFactorizationData.ofIsEquivalence
  签名: {F : D ⥤ C}
  定义体: F.objPreimage h.Z
  i := F.preimage (h.i ≫ (F.objObjPreimageIso h.Z).inv)
  p := F.preimage ((F.objObjPreimageIso h.Z).hom ≫ h.p)
  hi := by
    refine (W₁.arrow_mk_iso_iff ?_).1 h.hi
    refine Arrow.isoMk (Iso.refl _) (F.objObjPreimageIso h.Z).symm ?_
    simp [F.map_preimage]
  hp := by
    refine (W₂.arrow_mk_iso_iff ?_).1 h.hp
    refine Arrow.isoMk (F.objObjPreimageIso h.Z).symm (Iso.refl _) ?_
    simp [F.map_preimage]
  fac := F.map_injective (by simp)

Depends on / 依赖: F.objPreimage, objPreimage
-/
noncomputable def MapFactorizationData.ofIsEquivalence {F : D ⥤ C}
    [F.IsEquivalence] [W₁.RespectsIso] [W₂.RespectsIso]
    {X Y : D} {f : X ⟶ Y} (h : MapFactorizationData W₁ W₂ (F.map f)) :
    MapFactorizationData (W₁.inverseImage F) (W₂.inverseImage F) f where
  Z := F.objPreimage h.Z
  i := F.preimage (h.i ≫ (F.objObjPreimageIso h.Z).inv)
  p := F.preimage ((F.objObjPreimageIso h.Z).hom ≫ h.p)
  hi := by
    refine (W₁.arrow_mk_iso_iff ?_).1 h.hi
    refine Arrow.isoMk (Iso.refl _) (F.objObjPreimageIso h.Z).symm ?_
    simp [F.map_preimage]
  hp := by
    refine (W₂.arrow_mk_iso_iff ?_).1 h.hp
    refine Arrow.isoMk (F.objObjPreimageIso h.Z).symm (Iso.refl _) ?_
    simp [F.map_preimage]
  fac := F.map_injective (by simp)

instance (F : D ⥤ C) [F.IsEquivalence]
    [W₁.RespectsIso] [W₂.RespectsIso] [HasFactorization W₁ W₂] :
    HasFactorization (W₁.inverseImage F) (W₂.inverseImage F) where
  nonempty_mapFactorizationData f :=
    ⟨(factorizationData W₁ W₂ (F.map f)).ofIsEquivalence⟩

end MorphismProperty

end CategoryTheory
