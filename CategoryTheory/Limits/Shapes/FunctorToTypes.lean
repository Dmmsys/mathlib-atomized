/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Binary (co)products of type-valued functors

Defines an explicit construction of binary products and coproducts of type-valued functors.

Also defines isomorphisms to the categorical product and coproduct, respectively.
-/

@[expose] public section


open CategoryTheory Limits ConcreteCategory

universe w v u

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ Type w)

section prod

/-- `prod F G` is the explicit binary product of type-valued functors `F` and `G`. -/
@[simps obj map]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : C ⥤ Type w where
  body: F.obj a × G.obj a
  map f := ↾fun a => (F.map f a.1, G.map f a.2)

中文:
定义 prod
  签名: : C ⥤ Type w where
  定义体: F.obj a × G.obj a
  map f := ↾fun a => (F.map f a.1, G.map f a.2)

Depends on / 依赖: F.obj, G.obj
-/
def prod : C ⥤ Type w where
  obj a := F.obj a × G.obj a
  map f := ↾fun a => (F.map f a.1, G.map f a.2)

variable {F G}

/-- The first projection of `prod F G`, onto `F`. -/
@[simps app]
/--
Definition of `prod.fst` / `prod.fst` 的定义

English:
definition prod.fst
  signature: : prod F G ⟶ F where
  body: ↾fun a => a.1

中文:
定义 prod.fst
  签名: : prod F G ⟶ F where
  定义体: ↾fun a => a.1
-/
def prod.fst : prod F G ⟶ F where
  app _ := ↾fun a => a.1

/-- The second projection of `prod F G`, onto `G`. -/
@[simps app]
/--
Definition of `prod.snd` / `prod.snd` 的定义

English:
definition prod.snd
  signature: : prod F G ⟶ G where
  body: ↾fun a => a.2

中文:
定义 prod.snd
  签名: : prod F G ⟶ G where
  定义体: ↾fun a => a.2
-/
def prod.snd : prod F G ⟶ G where
  app _ := ↾fun a => a.2

set_option backward.isDefEq.respectTransparency.types false in
/-- Given natural transformations `F ⟶ F₁` and `F ⟶ F₂`, construct
a natural transformation `F ⟶ prod F₁ F₂`. -/
@[simps]
/--
Definition of `prod.lift` / `prod.lift` 的定义

English:
definition prod.lift
  signature: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  body: ↾fun y => ⟨τ₁.app x y, τ₂.app x y⟩

中文:
定义 prod.lift
  签名: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  定义体: ↾fun y => ⟨τ₁.app x y, τ₂.app x y⟩
-/
def prod.lift {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ prod F₁ F₂ where
  app x := ↾fun y => ⟨τ₁.app x y, τ₂.app x y⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `prod.lift_fst` / 引理 `prod.lift_fst`

English:
lemma prod.lift_fst
  given: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  proof: rfl

中文:
引理 prod.lift_fst
  条件: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  证明: rfl
-/
lemma prod.lift_fst {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.fst = τ₁ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `prod.lift_snd` / 引理 `prod.lift_snd`

English:
lemma prod.lift_snd
  given: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  proof: rfl

中文:
引理 prod.lift_snd
  条件: {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂)
  证明: rfl
-/
lemma prod.lift_snd {F₁ F₂ : C ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    prod.lift τ₁ τ₂ ≫ prod.snd = τ₂ := rfl

variable (F G)

/-- The binary fan whose point is `prod F G`. -/
@[simps!]
/--
Definition of `binaryProductCone` / `binaryProductCone` 的定义

English:
definition binaryProductCone
  signature: : BinaryFan F G
  body: BinaryFan.mk prod.fst prod.snd

中文:
定义 binaryProductCone
  签名: : BinaryFan F G
  定义体: BinaryFan.mk prod.fst prod.snd

Depends on / 依赖: BinaryFan, BinaryFan.mk, prod.fst, prod.snd
-/
def binaryProductCone : BinaryFan F G :=
  BinaryFan.mk prod.fst prod.snd

set_option backward.isDefEq.respectTransparency.types false in
/-- `prod F G` is a limit cone. -/
@[simps]
/--
Definition of `binaryProductLimit` / `binaryProductLimit` 的定义

English:
definition binaryProductLimit
  signature: : IsLimit (binaryProductCone F G) where
  body: prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

中文:
定义 binaryProductLimit
  签名: : IsLimit (binaryProductCone F G) where
  定义体: prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

Depends on / 依赖: prod.lift, s.fst, s.snd
-/
def binaryProductLimit : IsLimit (binaryProductCone F G) where
  lift (s : BinaryFan F G) := prod.lift s.fst s.snd
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    simp only [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]
    congr

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: : Limits.LimitCone (pair F G)
  body: ⟨_, binaryProductLimit F G⟩

中文:
定义 binaryProductLimitCone
  签名: : Limits.LimitCone (pair F G)
  定义体: ⟨_, binaryProductLimit F G⟩

Depends on / 依赖: binaryProductLimit
-/
def binaryProductLimitCone : Limits.LimitCone (pair F G) :=
  ⟨_, binaryProductLimit F G⟩

/--
Definition of `binaryProductIso` / `binaryProductIso` 的定义

English:
definition binaryProductIso
  signature: : F ⨯ G ≅ prod F G
  body: limit.isoLimitCone (binaryProductLimitCone F G)

中文:
定义 binaryProductIso
  签名: : F ⨯ G ≅ prod F G
  定义体: limit.isoLimitCone (binaryProductLimitCone F G)

Depends on / 依赖: binaryProductLimitCone, isoLimitCone, limit.isoLimitCone
-/
noncomputable def binaryProductIso : F ⨯ G ≅ prod F G :=
  limit.isoLimitCone (binaryProductLimitCone F G)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `binaryProductIso_hom_comp_fst` / 引理 `binaryProductIso_hom_comp_fst`

English:
lemma binaryProductIso_hom_comp_fst
  proof: rfl

中文:
引理 binaryProductIso_hom_comp_fst
  证明: rfl
-/
lemma binaryProductIso_hom_comp_fst :
    (binaryProductIso F G).hom ≫ prod.fst = Limits.prod.fst := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `binaryProductIso_hom_comp_snd` / 引理 `binaryProductIso_hom_comp_snd`

English:
lemma binaryProductIso_hom_comp_snd
  proof: rfl

中文:
引理 binaryProductIso_hom_comp_snd
  证明: rfl
-/
lemma binaryProductIso_hom_comp_snd :
    (binaryProductIso F G).hom ≫ prod.snd = Limits.prod.snd := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `binaryProductIso_inv_comp_fst` / 引理 `binaryProductIso_inv_comp_fst`

English:
lemma binaryProductIso_inv_comp_fst
  proof: by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]

中文:
引理 binaryProductIso_inv_comp_fst
  证明: by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]

Depends on / 依赖: binaryProductIso, binaryProductLimitCone
-/
lemma binaryProductIso_inv_comp_fst :
    (binaryProductIso F G).inv ≫ Limits.prod.fst = prod.fst := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
/--
lemma `binaryProductIso_inv_comp_fst_apply` / 引理 `binaryProductIso_inv_comp_fst_apply`

English:
lemma binaryProductIso_inv_comp_fst_apply
  given: (a : C) (z : (prod F G).obj a)
  proof: congr_hom (congr_app (binaryProductIso_inv_comp_fst F G) a) z

中文:
引理 binaryProductIso_inv_comp_fst_apply
  条件: (a : C) (z : (prod F G).obj a)
  证明: congr_hom (congr_app (binaryProductIso_inv_comp_fst F G) a) z

Depends on / 依赖: binaryProductIso, inv.app
-/
lemma binaryProductIso_inv_comp_fst_apply (a : C) (z : (prod F G).obj a) :
    dsimp% (Limits.prod.fst (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.1 :=
  congr_hom (congr_app (binaryProductIso_inv_comp_fst F G) a) z

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `binaryProductIso_inv_comp_snd` / 引理 `binaryProductIso_inv_comp_snd`

English:
lemma binaryProductIso_inv_comp_snd
  proof: by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]

中文:
引理 binaryProductIso_inv_comp_snd
  证明: by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]

Depends on / 依赖: binaryProductIso, binaryProductLimitCone
-/
lemma binaryProductIso_inv_comp_snd :
    (binaryProductIso F G).inv ≫ Limits.prod.snd = prod.snd := by
  simp [binaryProductIso, binaryProductLimitCone]

@[simp]
/--
lemma `binaryProductIso_inv_comp_snd_apply` / 引理 `binaryProductIso_inv_comp_snd_apply`

English:
lemma binaryProductIso_inv_comp_snd_apply
  given: (a : C) (z : (prod F G).obj a)
  proof: congr_hom (congr_app (binaryProductIso_inv_comp_snd F G) a) z

中文:
引理 binaryProductIso_inv_comp_snd_apply
  条件: (a : C) (z : (prod F G).obj a)
  证明: congr_hom (congr_app (binaryProductIso_inv_comp_snd F G) a) z

Depends on / 依赖: binaryProductIso, inv.app
-/
lemma binaryProductIso_inv_comp_snd_apply (a : C) (z : (prod F G).obj a) :
    dsimp% (Limits.prod.snd (X := F)).app a ((binaryProductIso F G).inv.app a z) = z.2 :=
  congr_hom (congr_app (binaryProductIso_inv_comp_snd F G) a) z

variable {F G}

/-- Construct an element of `(F ⨯ G).obj a` from an element of `F.obj a` and
an element of `G.obj a`. -/
noncomputable
/--
Definition of `prodMk` / `prodMk` 的定义

English:
definition prodMk
  signature: {a : C} (x : F.obj a) (y : G.obj a)
  body: ((binaryProductIso F G).inv).app a ⟨x, y⟩

中文:
定义 prodMk
  签名: {a : C} (x : F.obj a) (y : G.obj a)
  定义体: ((binaryProductIso F G).inv).app a ⟨x, y⟩

Depends on / 依赖: binaryProductIso
-/
def prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a :=
  ((binaryProductIso F G).inv).app a ⟨x, y⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `prodMk_fst` / 引理 `prodMk_fst`

English:
lemma prodMk_fst
  given: {a : C} (x : F.obj a) (y : G.obj a)
  proof: by
  simp [prodMk]

中文:
引理 prodMk_fst
  条件: {a : C} (x : F.obj a) (y : G.obj a)
  证明: by
  simp [prodMk]

Depends on / 依赖: prodMk
-/
lemma prodMk_fst {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.fst (X := F)).app a (prodMk x y) = x := by
  simp [prodMk]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `prodMk_snd` / 引理 `prodMk_snd`

English:
lemma prodMk_snd
  given: {a : C} (x : F.obj a) (y : G.obj a)
  proof: by
  simp [prodMk]

@[ext]

中文:
引理 prodMk_snd
  条件: {a : C} (x : F.obj a) (y : G.obj a)
  证明: by
  simp [prodMk]

@[ext]

Depends on / 依赖: prodMk
-/
lemma prodMk_snd {a : C} (x : F.obj a) (y : G.obj a) :
    (Limits.prod.snd (X := F)).app a (prodMk x y) = y := by
  simp [prodMk]

@[ext]
/--
lemma `prod_ext` / 引理 `prod_ext`

English:
lemma prod_ext
  given: {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2)
  proof: Prod.ext h1 h2

中文:
引理 prod_ext
  条件: {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2)
  证明: Prod.ext h1 h2

Depends on / 依赖: Prod.ext
-/
lemma prod_ext {a : C} (z w : (prod F G).obj a) (h1 : z.1 = w.1) (h2 : z.2 = w.2) :
    z = w := Prod.ext h1 h2

variable (F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- `(F ⨯ G).obj a` is in bijection with the product of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
/--
Definition of `binaryProductEquiv` / `binaryProductEquiv` 的定义

English:
definition binaryProductEquiv
  signature: (a : C)
  body: ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [-prod_obj, prodMk]
  right_inv _ := by simp [-prod_obj, prodMk]

中文:
定义 binaryProductEquiv
  签名: (a : C)
  定义体: ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [-prod_obj, prodMk]
  right_inv _ := by simp [-prod_obj, prodMk]

Depends on / 依赖: binaryProductIso, hom.app
-/
def binaryProductEquiv (a : C) : (F ⨯ G).obj a ≃ (F.obj a) × (G.obj a) where
  toFun z := ⟨((binaryProductIso F G).hom.app a z).1, ((binaryProductIso F G).hom.app a z).2⟩
  invFun z := prodMk z.1 z.2
  left_inv _ := by simp [-prod_obj, prodMk]
  right_inv _ := by simp [-prod_obj, prodMk]

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/--
lemma `prod_ext'` / 引理 `prod_ext'`

English:
lemma prod_ext'
  statement: (a : C) (z w : (F ⨯ G).obj a)
  proof: by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop

中文:
引理 prod_ext'
  结论: (a : C) (z w : (F ⨯ G).obj a)
  证明: by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop

Depends on / 依赖: Limits, Limits.prod.fst
-/
lemma prod_ext' (a : C) (z w : (F ⨯ G).obj a)
    (h1 : (Limits.prod.fst (X := F)).app a z = (Limits.prod.fst (X := F)).app a w)
    (h2 : (Limits.prod.snd (X := F)).app a z = (Limits.prod.snd (X := F)).app a w) :
    z = w := by
  apply Equiv.injective (binaryProductEquiv F G a)
  aesop

end prod

section coprod

/-- `coprod F G` is the explicit binary coproduct of type-valued functors `F` and `G`. -/
@[simps obj map]
/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: : C ⥤ Type w where
  body: F.obj a oplus G.obj a
  map f := ↾(Sum.map (F.map f) (G.map f))
  map_id _ := by ext ⟨⟩ <;> simp
  map_comp _ _ := by ext ⟨⟩ <;> simp

中文:
定义 coprod
  签名: : C ⥤ Type w where
  定义体: F.obj a oplus G.obj a
  map f := ↾(Sum.map (F.map f) (G.map f))
  map_id _ := by ext ⟨⟩ <;> simp
  map_comp _ _ := by ext ⟨⟩ <;> simp

Depends on / 依赖: F.obj, G.obj
-/
def coprod : C ⥤ Type w where
  obj a := F.obj a oplus G.obj a
  map f := ↾(Sum.map (F.map f) (G.map f))
  map_id _ := by ext ⟨⟩ <;> simp
  map_comp _ _ := by ext ⟨⟩ <;> simp

variable {F G}

/-- The left inclusion of `F` into `coprod F G`. -/
@[simps]
/--
Definition of `coprod.inl` / `coprod.inl` 的定义

English:
definition coprod.inl
  signature: : F ⟶ coprod F G where
  body: ↾fun x => .inl x

中文:
定义 coprod.inl
  签名: : F ⟶ coprod F G where
  定义体: ↾fun x => .inl x
-/
def coprod.inl : F ⟶ coprod F G where
  app _ := ↾fun x => .inl x

/-- The right inclusion of `G` into `coprod F G`. -/
@[simps]
/--
Definition of `coprod.inr` / `coprod.inr` 的定义

English:
definition coprod.inr
  signature: : G ⟶ coprod F G where
  body: ↾fun x => .inr x

中文:
定义 coprod.inr
  签名: : G ⟶ coprod F G where
  定义体: ↾fun x => .inr x
-/
def coprod.inr : G ⟶ coprod F G where
  app _ := ↾fun x => .inr x

set_option backward.defeqAttrib.useBackward true in
/-- Given natural transformations `F₁ ⟶ F` and `F₂ ⟶ F`, construct
a natural transformation `coprod F₁ F₂ ⟶ F`. -/
@[simps]
/--
Definition of `coprod.desc` / `coprod.desc` 的定义

English:
definition coprod.desc
  signature: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  body: ↾(Sum.elim (τ₁.app a) (τ₂.app a))
  naturality _ _ _ := by ext ⟨⟩ <;> simp

@[simp]

中文:
定义 coprod.desc
  签名: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  定义体: ↾(Sum.elim (τ₁.app a) (τ₂.app a))
  naturality _ _ _ := by ext ⟨⟩ <;> simp

@[simp]
-/
def coprod.desc {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod F₁ F₂ ⟶ F where
  app a := ↾(Sum.elim (τ₁.app a) (τ₂.app a))
  naturality _ _ _ := by ext ⟨⟩ <;> simp

@[simp]
/--
lemma `coprod.desc_inl` / 引理 `coprod.desc_inl`

English:
lemma coprod.desc_inl
  given: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  proof: rfl

@[simp]

中文:
引理 coprod.desc_inl
  条件: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  证明: rfl

@[simp]
-/
lemma coprod.desc_inl {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inl ≫ coprod.desc τ₁ τ₂ = τ₁ := rfl

@[simp]
/--
lemma `coprod.desc_inr` / 引理 `coprod.desc_inr`

English:
lemma coprod.desc_inr
  given: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  proof: rfl

中文:
引理 coprod.desc_inr
  条件: {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F)
  证明: rfl
-/
lemma coprod.desc_inr {F₁ F₂ : C ⥤ Type w} (τ₁ : F₁ ⟶ F) (τ₂ : F₂ ⟶ F) :
    coprod.inr ≫ coprod.desc τ₁ τ₂ = τ₂ := rfl

variable (F G)

/-- The binary cofan whose point is `coprod F G`. -/
@[simps!]
/--
Definition of `binaryCoproductCocone` / `binaryCoproductCocone` 的定义

English:
definition binaryCoproductCocone
  signature: : BinaryCofan F G
  body: BinaryCofan.mk coprod.inl coprod.inr

中文:
定义 binaryCoproductCocone
  签名: : BinaryCofan F G
  定义体: BinaryCofan.mk coprod.inl coprod.inr

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, coprod, coprod.inl, coprod.inr
-/
def binaryCoproductCocone : BinaryCofan F G :=
  BinaryCofan.mk coprod.inl coprod.inr

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `coprod F G` is a colimit cocone. -/
@[simps]
/--
Definition of `binaryCoproductColimit` / `binaryCoproductColimit` 的定义

English:
definition binaryCoproductColimit
  signature: : IsColimit (binaryCoproductCocone F G) where
  body: coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]

中文:
定义 binaryCoproductColimit
  签名: : IsColimit (binaryCoproductCocone F G) where
  定义体: coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]

Depends on / 依赖: coprod, coprod.desc, s.inl, s.inr
-/
def binaryCoproductColimit : IsColimit (binaryCoproductCocone F G) where
  desc (s : BinaryCofan F G) := coprod.desc s.inl s.inr
  fac _ := fun ⟨j⟩ => WalkingPair.casesOn j rfl rfl
  uniq _ _ h := by
    ext _ x
    cases x with | _ => simp [← h ⟨WalkingPair.right⟩, ← h ⟨WalkingPair.left⟩]

/--
Definition of `binaryCoproductColimitCocone` / `binaryCoproductColimitCocone` 的定义

English:
definition binaryCoproductColimitCocone
  signature: : Limits.ColimitCocone (pair F G)
  body: ⟨_, binaryCoproductColimit F G⟩

中文:
定义 binaryCoproductColimitCocone
  签名: : Limits.ColimitCocone (pair F G)
  定义体: ⟨_, binaryCoproductColimit F G⟩

Depends on / 依赖: binaryCoproductColimit
-/
def binaryCoproductColimitCocone : Limits.ColimitCocone (pair F G) :=
  ⟨_, binaryCoproductColimit F G⟩

/--
Definition of `binaryCoproductIso` / `binaryCoproductIso` 的定义

English:
definition binaryCoproductIso
  signature: : F ⨿ G ≅ coprod F G
  body: colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

中文:
定义 binaryCoproductIso
  签名: : F ⨿ G ≅ coprod F G
  定义体: colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

Depends on / 依赖: SymmetricCategory, binaryCoproductColimitCocone, colimit, colimit.isoColimitCocone, isoColimitCocone, toSymmetricCategory
-/
noncomputable def binaryCoproductIso : F ⨿ G ≅ coprod F G :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone F G)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `inl_comp_binaryCoproductIso_hom` / 引理 `inl_comp_binaryCoproductIso_hom`

English:
lemma inl_comp_binaryCoproductIso_hom
  proof: by
  simp only [binaryCoproductIso]
  aesop

@[simp]

中文:
引理 inl_comp_binaryCoproductIso_hom
  证明: by
  simp only [binaryCoproductIso]
  aesop

@[simp]

Depends on / 依赖: binaryCoproductIso
-/
lemma inl_comp_binaryCoproductIso_hom :
    Limits.coprod.inl ≫ (binaryCoproductIso F G).hom = coprod.inl := by
  simp only [binaryCoproductIso]
  aesop

@[simp]
/--
lemma `inl_comp_binaryCoproductIso_hom_apply` / 引理 `inl_comp_binaryCoproductIso_hom_apply`

English:
lemma inl_comp_binaryCoproductIso_hom_apply
  given: (a : C) (x : F.obj a)
  proof: congr_hom (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x

中文:
引理 inl_comp_binaryCoproductIso_hom_apply
  条件: (a : C) (x : F.obj a)
  证明: congr_hom (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x
-/
lemma inl_comp_binaryCoproductIso_hom_apply (a : C) (x : F.obj a) :
    dsimp% (binaryCoproductIso F G).hom.app a ((Limits.coprod.inl (X := F)).app a x) = .inl x :=
  congr_hom (congr_app (inl_comp_binaryCoproductIso_hom F G) a) x

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `inr_comp_binaryCoproductIso_hom` / 引理 `inr_comp_binaryCoproductIso_hom`

English:
lemma inr_comp_binaryCoproductIso_hom
  proof: by
  simp [binaryCoproductIso]
  aesop

@[simp]

中文:
引理 inr_comp_binaryCoproductIso_hom
  证明: by
  simp [binaryCoproductIso]
  aesop

@[simp]

Depends on / 依赖: binaryCoproductIso
-/
lemma inr_comp_binaryCoproductIso_hom :
    Limits.coprod.inr ≫ (binaryCoproductIso F G).hom = coprod.inr := by
  simp [binaryCoproductIso]
  aesop

@[simp]
/--
lemma `inr_comp_binaryCoproductIso_hom_apply` / 引理 `inr_comp_binaryCoproductIso_hom_apply`

English:
lemma inr_comp_binaryCoproductIso_hom_apply
  given: (a : C) (x : G.obj a)
  proof: congr_hom (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x

@[simp]

中文:
引理 inr_comp_binaryCoproductIso_hom_apply
  条件: (a : C) (x : G.obj a)
  证明: congr_hom (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x

@[simp]

Depends on / 依赖: HasFiniteProducts, Limits, Limits.HasFiniteProducts
-/
lemma inr_comp_binaryCoproductIso_hom_apply (a : C) (x : G.obj a) :
    dsimp% (binaryCoproductIso F G).hom.app a ((Limits.coprod.inr (X := F)).app a x) = .inr x :=
  congr_hom (congr_app (inr_comp_binaryCoproductIso_hom F G) a) x

@[simp]
/--
lemma `inl_comp_binaryCoproductIso_inv` / 引理 `inl_comp_binaryCoproductIso_inv`

English:
lemma inl_comp_binaryCoproductIso_inv
  proof: rfl

@[simp]

中文:
引理 inl_comp_binaryCoproductIso_inv
  证明: rfl

@[simp]
-/
lemma inl_comp_binaryCoproductIso_inv :
    coprod.inl ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inl (X := F)) := rfl

@[simp]
/--
lemma `inl_comp_binaryCoproductIso_inv_apply` / 引理 `inl_comp_binaryCoproductIso_inv_apply`

English:
lemma inl_comp_binaryCoproductIso_inv_apply
  given: (a : C) (x : F.obj a)
  proof: rfl

@[simp]

中文:
引理 inl_comp_binaryCoproductIso_inv_apply
  条件: (a : C) (x : F.obj a)
  证明: rfl

@[simp]
-/
lemma inl_comp_binaryCoproductIso_inv_apply (a : C) (x : F.obj a) :
    dsimp% (binaryCoproductIso F G).inv.app a (.inl x) = (Limits.coprod.inl (X := F)).app a x := rfl

@[simp]
/--
lemma `inr_comp_binaryCoproductIso_inv` / 引理 `inr_comp_binaryCoproductIso_inv`

English:
lemma inr_comp_binaryCoproductIso_inv
  proof: rfl

@[simp]

中文:
引理 inr_comp_binaryCoproductIso_inv
  证明: rfl

@[simp]
-/
lemma inr_comp_binaryCoproductIso_inv :
    coprod.inr ≫ (binaryCoproductIso F G).inv = (Limits.coprod.inr (X := F)) := rfl

@[simp]
/--
lemma `inr_comp_binaryCoproductIso_inv_apply` / 引理 `inr_comp_binaryCoproductIso_inv_apply`

English:
lemma inr_comp_binaryCoproductIso_inv_apply
  given: (a : C) (x : G.obj a)
  proof: rfl

中文:
引理 inr_comp_binaryCoproductIso_inv_apply
  条件: (a : C) (x : G.obj a)
  证明: rfl
-/
lemma inr_comp_binaryCoproductIso_inv_apply (a : C) (x : G.obj a) :
    dsimp% (binaryCoproductIso F G).inv.app a (.inr x) = (Limits.coprod.inr (X := F)).app a x := rfl

variable {F G}

/-- Construct an element of `(F ⨿ G).obj a` from an element of `F.obj a` -/
noncomputable
/--
Definition of `coprodInl` / `coprodInl` 的定义

English:
abbreviation coprodInl
  signature: {a : C} (x : F.obj a)
  body: (binaryCoproductIso F G).inv.app a (.inl x)

中文:
缩写 coprodInl
  签名: {a : C} (x : F.obj a)
  定义体: (binaryCoproductIso F G).inv.app a (.inl x)

Depends on / 依赖: binaryCoproductIso, inv.app
-/
abbrev coprodInl {a : C} (x : F.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inl x)

/-- Construct an element of `(F ⨿ G).obj a` from an element of `G.obj a` -/
noncomputable
/--
Definition of `coprodInr` / `coprodInr` 的定义

English:
abbreviation coprodInr
  signature: {a : C} (x : G.obj a)
  body: (binaryCoproductIso F G).inv.app a (.inr x)

中文:
缩写 coprodInr
  签名: {a : C} (x : G.obj a)
  定义体: (binaryCoproductIso F G).inv.app a (.inr x)

Depends on / 依赖: binaryCoproductIso, inv.app
-/
abbrev coprodInr {a : C} (x : G.obj a) : (F ⨿ G).obj a :=
  (binaryCoproductIso F G).inv.app a (.inr x)

variable (F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- `(F ⨿ G).obj a` is in bijection with disjoint union of `F.obj a` and `G.obj a`. -/
@[simps]
noncomputable
/--
Definition of `binaryCoproductEquiv` / `binaryCoproductEquiv` 的定义

English:
definition binaryCoproductEquiv
  signature: (a : C)
  body: (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp [-coprod_obj]
  right_inv _ := by simp [-coprod_obj]

中文:
定义 binaryCoproductEquiv
  签名: (a : C)
  定义体: (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp [-coprod_obj]
  right_inv _ := by simp [-coprod_obj]

Depends on / 依赖: binaryCoproductIso, hom.app
-/
def binaryCoproductEquiv (a : C) :
    (F ⨿ G).obj a ≃ (F.obj a) oplus (G.obj a) where
  toFun z := (binaryCoproductIso F G).hom.app a z
  invFun z := (binaryCoproductIso F G).inv.app a z
  left_inv _ := by simp [-coprod_obj]
  right_inv _ := by simp [-coprod_obj]

end coprod

end CategoryTheory.FunctorToTypes
