/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# The bicategory of based categories

In this file we define the type `BasedCategory 𝒮`, and give it the structure of a strict
bicategory. Given a category `𝒮`, we define the type `BasedCategory 𝒮` as the type of categories
`𝒳` equipped with a functor `𝒳.p : 𝒳 ⥤ 𝒮`.

We also define a type of functors between based categories `𝒳` and `𝒴`, which we call
`BasedFunctor 𝒳 𝒴` and denote as `𝒳 ⥤ᵇ 𝒴`. These are defined as functors between the underlying
categories `𝒳.obj` and `𝒴.obj` which commute with the projections to `𝒮`.

Natural transformations between based functors `F G : 𝒳 ⥤ᵇ 𝒴 ` are given by the structure
`BasedNatTrans F G`. These are defined as natural transformations `α` between the functors
underlying `F` and `G` such that `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`.
-/

@[expose] public section

universe v₅ u₅ v₄ u₄ v₃ u₃ v₂ u₂ v₁ u₁

namespace CategoryTheory

open CategoryTheory.Functor Category NatTrans IsHomLift

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

set_option linter.checkUnivs false in
/--
Definition of `BasedCategory` / `BasedCategory` 的定义

English:
structure BasedCategory
  parameters: (𝒮 : Type u₁) [Category.{v₁} 𝒮]
  axioms and operations (3):
    - obj : Type u₂
    - category : Category.{v₂} obj  [default: by infer_instance]
    - p : obj ⥤ 𝒮

中文:
结构 BasedCategory
  参数: (𝒮 : 类型u₁) [Category.{v₁} 𝒮]
  公理与运算 (3 个):
    - obj : 类型u₂
    - category : Category.{v₂} obj  [默认: by infer_instance]
    - p : obj ⥤ 𝒮

Depends on / 依赖: infer_instance
-/
structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  /-- The type of objects in a `BasedCategory` -/
  obj : Type u₂
  /-- The underlying category of a `BasedCategory`. -/
  category : Category.{v₂} obj := by infer_instance
  /-- The functor to the base. -/
  p : obj ⥤ 𝒮

instance (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : Category 𝒳.obj := 𝒳.category

/--
Definition of `BasedCategory.ofFunctor` / `BasedCategory.ofFunctor` 的定义

English:
definition BasedCategory.ofFunctor
  signature: {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
  body: 𝒳
  p := p

中文:
定义 BasedCategory.ofFunctor
  签名: {𝒳 : 类型u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
  定义体: 𝒳
  p := p
-/
def BasedCategory.ofFunctor {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) : BasedCategory 𝒮 where
  obj := 𝒳
  p := p

/--
Definition of `BasedFunctor` / `BasedFunctor` 的定义

English:
structure BasedFunctor
  parameters: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  axioms and operations (1):
    - w : toFunctor ⋙ 𝒴.p = 𝒳.p  [default: by cat_disch]

中文:
结构 BasedFunctor
  参数: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  公理与运算 (1 个):
    - w : toFunctor ⋙ 𝒴.p = 𝒳.p  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure BasedFunctor (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) extends
    𝒳.obj ⥤ 𝒴.obj where
  w : toFunctor ⋙ 𝒴.p = 𝒳.p := by cat_disch

/-- Notation for `BasedFunctor`. -/
scoped infixr:26 " ⥤ᵇ " => BasedFunctor

namespace BasedFunctor

initialize_simps_projections BasedFunctor (+toFunctor, -obj, -map)

/-- The identity based functor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
  body: 𝟭 𝒳.obj

中文:
定义 id
  签名: (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
  定义体: 𝟭 𝒳.obj
-/
def id (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ 𝒳 where
  toFunctor := 𝟭 𝒳.obj

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Notation for the identity functor on a based category. -/
scoped notation "𝟭" => BasedFunctor.id

/-- The composition of two based functors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵)
  body: F.toFunctor ⋙ G.toFunctor
  w := by rw [Functor.assoc, G.w, F.w]

中文:
定义 comp
  签名: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵)
  定义体: F.toFunctor ⋙ G.toFunctor
  w := by rw [Functor.assoc, G.w, F.w]

Depends on / 依赖: F.toFunctor, G.toFunctor, toFunctor
-/
def comp {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) : 𝒳 ⥤ᵇ 𝒵 where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  w := by rw [Functor.assoc, G.w, F.w]

/-- Notation for composition of based functors. -/
scoped infixr:80 " ⋙ " => BasedFunctor.comp

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (F : 𝒳 ⥤ᵇ 𝒴)
  statement: F ⋙ 𝟭 𝒴 = F
  proof: rfl

@[simp]

中文:
引理 comp_id
  条件: (F : 𝒳 ⥤ᵇ 𝒴)
  结论: F ⋙ 𝟭 𝒴 = F
  证明: rfl

@[simp]
-/
lemma comp_id (F : 𝒳 ⥤ᵇ 𝒴) : F ⋙ 𝟭 𝒴 = F :=
  rfl

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (F : 𝒳 ⥤ᵇ 𝒴)
  statement: 𝟭 𝒳 ⋙ F = F
  proof: rfl

@[simp]

中文:
引理 id_comp
  条件: (F : 𝒳 ⥤ᵇ 𝒴)
  结论: 𝟭 𝒳 ⋙ F = F
  证明: rfl

@[simp]
-/
lemma id_comp (F : 𝒳 ⥤ᵇ 𝒴) : 𝟭 𝒳 ⋙ F = F :=
  rfl

@[simp]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒜 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
  proof: rfl

@[simp]

中文:
引理 comp_assoc
  结论: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒜 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
  证明: rfl

@[simp]
-/
lemma comp_assoc {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒜 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴 ⥤ᵇ 𝒵) (H : 𝒵 ⥤ᵇ 𝒜) : (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) :=
  rfl

@[simp]
/--
lemma `w_obj` / 引理 `w_obj`

English:
lemma w_obj
  given: (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj)
  statement: 𝒴.p.obj (F.obj a) = 𝒳.p.obj a
  proof: by
  rw [← Functor.comp_obj]; rw [F.w]

中文:
引理 w_obj
  条件: (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj)
  结论: 𝒴.p.obj (F.obj a) = 𝒳.p.obj a
  证明: by
  rw [← Functor.comp_obj]; rw [F.w]

Depends on / 依赖: Functor, Functor.comp_obj, comp_obj
-/
lemma w_obj (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : 𝒴.p.obj (F.obj a) = 𝒳.p.obj a := by
  rw [← Functor.comp_obj]; rw [F.w]

instance (F : 𝒳 ⥤ᵇ 𝒴) (a : 𝒳.obj) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (𝟙 (F.obj a)) :=
  IsHomLift.id (w_obj F a)

section

variable (F : 𝒳 ⥤ᵇ 𝒴) {R S : 𝒮} {a b : 𝒳.obj} (f : R ⟶ S) (φ : a ⟶ b)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `preserves_isHomLift` / 实例 `preserves_isHomLift`

English:
instance preserves_isHomLift
  signature: [IsHomLift 𝒳.p f φ]
  body: by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [← Functor.comp_map]; rw [congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

中文:
实例 preserves_isHomLift
  签名: [IsHomLift 𝒳.p f φ]
  定义体: by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [← Functor.comp_map]; rw [congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

Depends on / 依赖: Eq.trans, F.map, F.w_obj, Functor, Functor.comp_map, codomain_eq, comp_map, congr_hom, domain_eq, of_fac, w_obj
-/
instance preserves_isHomLift [IsHomLift 𝒳.p f φ] : IsHomLift 𝒴.p f (F.map φ) := by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [← Functor.comp_map]; rw [congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isHomLift_map` / 引理 `isHomLift_map`

English:
lemma isHomLift_map
  given: [IsHomLift 𝒴.p f (F.map φ)]
  statement: IsHomLift 𝒳.p f φ
  proof: by
  apply of_fac 𝒳.p f φ (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]

中文:
引理 isHomLift_map
  条件: [IsHomLift 𝒴.p f (F.map φ)]
  结论: IsHomLift 𝒳.p f φ
  证明: by
  apply of_fac 𝒳.p f φ (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]

Depends on / 依赖: F.map, F.w.symm, F.w_obj, codomain_eq, congr_hom, domain_eq, of_fac, w_obj
-/
lemma isHomLift_map [IsHomLift 𝒴.p f (F.map φ)] : IsHomLift 𝒳.p f φ := by
  apply of_fac 𝒳.p f φ (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]

/--
lemma `isHomLift_iff` / 引理 `isHomLift_iff`

English:
lemma isHomLift_iff
  statement: IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ
  proof: ⟨fun _ => isHomLift_map F f φ, fun _ => preserves_isHomLift F f φ⟩

中文:
引理 isHomLift_iff
  结论: IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ
  证明: ⟨fun _ => isHomLift_map F f φ, fun _ => preserves_isHomLift F f φ⟩

Depends on / 依赖: isHomLift_map, preserves_isHomLift
-/
lemma isHomLift_iff : IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ :=
  ⟨fun _ => isHomLift_map F f φ, fun _ => preserves_isHomLift F f φ⟩

end

end BasedFunctor


/--
Definition of `BasedNatTrans` / `BasedNatTrans` 的定义

English:
structure BasedNatTrans
  parameters: {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  extends: CategoryTheory.NatTrans F.toFunctor G.toFunctor
  axioms and operations (1):
    - isHomLift' : forall (a : 𝒳.obj), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (toNatTrans.app a)  [default: by cat_disch]

中文:
结构 BasedNatTrans
  参数: {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  继承: CategoryTheory.NatTrans F.toFunctor G.toFunctor
  公理与运算 (1 个):
    - isHomLift' : 对任意 (a : 𝒳.obj), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (to自然数Trans.app a)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure BasedNatTrans {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F G : 𝒳 ⥤ᵇ 𝒴) extends CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  isHomLift' : forall (a : 𝒳.obj), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (toNatTrans.app a) := by cat_disch

namespace BasedNatTrans

open BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

initialize_simps_projections BasedNatTrans (+toNatTrans, -app)

section

variable {F G : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G)

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans)
  statement: α = β
  proof: by
  cases α; subst h; rfl

中文:
引理 ext
  条件: (β : Based自然数Trans F G) (h : α.to自然数Trans = β.to自然数Trans)
  结论: α = β
  证明: by
  cases α; subst h; rfl
-/
lemma ext (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α; subst h; rfl

/--
Instance `app_isHomLift` / 实例 `app_isHomLift`

English:
instance app_isHomLift
  signature: (a : 𝒳.obj)
  body: α.isHomLift' a

中文:
实例 app_isHomLift
  签名: (a : 𝒳.obj)
  定义体: α.isHomLift' a

Depends on / 依赖: isHomLift
-/
instance app_isHomLift (a : 𝒳.obj) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a) :=
  α.isHomLift' a

/--
lemma `isHomLift` / 引理 `isHomLift`

English:
lemma isHomLift
  given: {a : 𝒳.obj} {S : 𝒮} (ha : 𝒳.p.obj a = S)
  proof: by
  subst ha; infer_instance

中文:
引理 isHomLift
  条件: {a : 𝒳.obj} {S : 𝒮} (ha : 𝒳.p.obj a = S)
  证明: by
  subst ha; infer_instance

Depends on / 依赖: infer_instance
-/
lemma isHomLift {a : 𝒳.obj} {S : 𝒮} (ha : 𝒳.p.obj a = S) :
    IsHomLift 𝒴.p (𝟙 S) (α.toNatTrans.app a) := by
  subst ha; infer_instance

end

/-- The identity natural transformation is a `BasedNatTrans`. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (F : 𝒳 ⥤ᵇ 𝒴)
  body: CategoryTheory.NatTrans.id F.toFunctor
  isHomLift' := fun a => of_fac 𝒴.p _ _ (w_obj F a) (w_obj F a) (by simp)

中文:
定义 id
  签名: (F : 𝒳 ⥤ᵇ 𝒴)
  定义体: CategoryTheory.NatTrans.id F.toFunctor
  isHomLift' := fun a => of_fac 𝒴.p _ _ (w_obj F a) (w_obj F a) (by simp)

Depends on / 依赖: CategoryTheory, CategoryTheory.NatTrans.id, F.toFunctor, NatTrans, toFunctor
-/
def id (F : 𝒳 ⥤ᵇ 𝒴) : BasedNatTrans F F where
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  isHomLift' := fun a => of_fac 𝒴.p _ _ (w_obj F a) (w_obj F a) (by simp)

/-- Composition of `BasedNatTrans`, given by composition of the underlying natural
transformations. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H)
  body: CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  isHomLift' := by
    intro a
    rw [CategoryTheory.NatTrans.vcomp_app]
    infer_instance

@[simps]

中文:
定义 comp
  签名: {F G H : 𝒳 ⥤ᵇ 𝒴} (α : Based自然数Trans F G) (β : Based自然数Trans G H)
  定义体: CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  isHomLift' := by
    intro a
    rw [CategoryTheory.NatTrans.vcomp_app]
    infer_instance

@[simps]

Depends on / 依赖: CategoryTheory, CategoryTheory.NatTrans.vcomp, NatTrans, toNatTrans
-/
def comp {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) : BasedNatTrans F H where
  toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  isHomLift' := by
    intro a
    rw [CategoryTheory.NatTrans.vcomp_app]
    infer_instance

@[simps]
/--
Instance `homCategory` / 实例 `homCategory`

English:
instance homCategory
  signature: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  body: BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp

@[ext]

中文:
实例 homCategory
  签名: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  定义体: BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp

@[ext]

Depends on / 依赖: BasedNatTrans
-/
instance homCategory (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) :
    Category (𝒳 ⥤ᵇ 𝒴) where
  Hom := BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp

@[ext]
/--
lemma `homCategory.ext` / 引理 `homCategory.ext`

English:
lemma homCategory.ext
  given: {F G : 𝒳 ⥤ᵇ 𝒴} (α β : F ⟶ G) (h : α.toNatTrans = β.toNatTrans)
  statement: α = β
  proof: BasedNatTrans.ext α β h

中文:
引理 homCategory.ext
  条件: {F G : 𝒳 ⥤ᵇ 𝒴} (α β : F ⟶ G) (h : α.to自然数Trans = β.to自然数Trans)
  结论: α = β
  证明: BasedNatTrans.ext α β h
-/
lemma homCategory.ext {F G : 𝒳 ⥤ᵇ 𝒴} (α β : F ⟶ G) (h : α.toNatTrans = β.toNatTrans) : α = β :=
  BasedNatTrans.ext α β h

/-- The forgetful functor from the category of based functors `𝒳 ⥤ᵇ 𝒴` to the category of
functors of underlying categories, `𝒳.obj ⥤ 𝒴.obj`. -/
@[simps]
/--
Definition of `forgetful` / `forgetful` 的定义

English:
definition forgetful
  signature: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  body: fun F => F.toFunctor
  map := fun α => α.toNatTrans

中文:
定义 forgetful
  签名: (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮)
  定义体: fun F => F.toFunctor
  map := fun α => α.toNatTrans

Depends on / 依赖: F.toFunctor, toFunctor
-/
def forgetful (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) :
    (𝒳 ⥤ᵇ 𝒴) ⥤ (𝒳.obj ⥤ 𝒴.obj) where
  obj := fun F => F.toFunctor
  map := fun α => α.toNatTrans

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forgetful 𝒳 𝒴).ReflectsIsomorphisms
  body: by
    constructor
    use {
      toNatTrans := inv ((forgetful 𝒳 𝒴).map α)
      isHomLift' := fun a => by simp [lift_id_inv_isIso] }
    aesop

中文:
实例 :
  签名: (forgetful 𝒳 𝒴).ReflectsIsomorphisms
  定义体: by
    constructor
    use {
      toNatTrans := inv ((forgetful 𝒳 𝒴).map α)
      isHomLift' := fun a => by simp [lift_id_inv_isIso] }
    aesop

Depends on / 依赖: forgetful, isHomLift, lift_id_inv_isIso, toNatTrans
-/
instance : (forgetful 𝒳 𝒴).ReflectsIsomorphisms where
  reflects {F G} α _ := by
    constructor
    use {
      toNatTrans := inv ((forgetful 𝒳 𝒴).map α)
      isHomLift' := fun a => by simp [lift_id_inv_isIso] }
    aesop

set_option backward.isDefEq.respectTransparency false in
instance {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) [IsIso α] : IsIso (X := F.toFunctor) α.toNatTrans := by
  rw [← forgetful_map]; infer_instance

end BasedNatTrans

namespace BasedNatIso

open BasedNatTrans

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- The identity natural transformation is a based natural isomorphism. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (F : 𝒳 ⥤ᵇ 𝒴)
  body: 𝟙 F
  inv := 𝟙 F

中文:
定义 id
  签名: (F : 𝒳 ⥤ᵇ 𝒴)
  定义体: 𝟙 F
  inv := 𝟙 F
-/
def id (F : 𝒳 ⥤ᵇ 𝒴) : F ≅ F where
  hom := 𝟙 F
  inv := 𝟙 F

variable {F G : 𝒳 ⥤ᵇ 𝒴}

/--
Definition of `mkNatIso` / `mkNatIso` 的定义

English:
definition mkNatIso
  signature: (α : F.toFunctor ≅ G.toFunctor)
  body: { toNatTrans := α.hom }
  inv := {
    toNatTrans := α.inv
    isHomLift' := fun a => by
      have : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (α.app a).hom := (Iso.app_hom α a) ▸ isHomLift' a
      rw [← Iso.app_inv]
      apply IsHomLift.lift_id_inv }

中文:
定义 mkNatIso
  签名: (α : F.toFunctor ≅ G.toFunctor)
  定义体: { toNatTrans := α.hom }
  inv := {
    toNatTrans := α.inv
    isHomLift' := fun a => by
      have : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (α.app a).hom := (Iso.app_hom α a) ▸ isHomLift' a
      rw [← Iso.app_inv]
      apply IsHomLift.lift_id_inv }

Depends on / 依赖: toNatTrans
-/
def mkNatIso (α : F.toFunctor ≅ G.toFunctor)
    (isHomLift' : forall a : 𝒳.obj, IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.hom.app a)) : F ≅ G where
  hom := { toNatTrans := α.hom }
  inv := {
    toNatTrans := α.inv
    isHomLift' := fun a => by
      have : 𝒴.p.IsHomLift (𝟙 (𝒳.p.obj a)) (α.app a).hom := (Iso.app_hom α a) ▸ isHomLift' a
      rw [← Iso.app_inv]
      apply IsHomLift.lift_id_inv }

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_of_toNatTrans_isIso` / 引理 `isIso_of_toNatTrans_isIso`

English:
lemma isIso_of_toNatTrans_isIso
  given: (α : F ⟶ G) [IsIso (X := F.toFunctor) α.toNatTrans]
  statement: IsIso α
  proof: have : IsIso ((forgetful 𝒳 𝒴).map α) := by simp_all
  Functor.ReflectsIsomorphisms.reflects (forgetful 𝒳 𝒴) α

中文:
引理 isIso_of_toNatTrans_isIso
  条件: (α : F ⟶ G) [IsIso (X := F.toFunctor) α.to自然数Trans]
  结论: IsIso α
  证明: have : IsIso ((forgetful 𝒳 𝒴).map α) := by simp_all
  Functor.ReflectsIsomorphisms.reflects (forgetful 𝒳 𝒴) α

Depends on / 依赖: F.toFunctor, toFunctor, toNatTrans
-/
lemma isIso_of_toNatTrans_isIso (α : F ⟶ G) [IsIso (X := F.toFunctor) α.toNatTrans] : IsIso α :=
  have : IsIso ((forgetful 𝒳 𝒴).map α) := by simp_all
  Functor.ReflectsIsomorphisms.reflects (forgetful 𝒳 𝒴) α

end BasedNatIso

namespace BasedCategory

open BasedFunctor BasedNatTrans

section

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Left-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
and natural transformations. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H)
  body: Functor.whiskerLeft F.toFunctor α.toNatTrans
  isHomLift' := fun a => α.isHomLift (F.w_obj a)

中文:
定义 whiskerLeft
  签名: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H)
  定义体: Functor.whiskerLeft F.toFunctor α.toNatTrans
  isHomLift' := fun a => α.isHomLift (F.w_obj a)

Depends on / 依赖: F.toFunctor, Functor, Functor.whiskerLeft, toFunctor, toNatTrans, whiskerLeft
-/
def whiskerLeft {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  toNatTrans := Functor.whiskerLeft F.toFunctor α.toNatTrans
  isHomLift' := fun a => α.isHomLift (F.w_obj a)

/-- Right-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying
functors and natural transformations. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (H : 𝒴 ⥤ᵇ 𝒵)
  body: Functor.whiskerRight α.toNatTrans H.toFunctor
  isHomLift' := fun _ => BasedFunctor.preserves_isHomLift _ _ _

中文:
定义 whiskerRight
  签名: {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (H : 𝒴 ⥤ᵇ 𝒵)
  定义体: Functor.whiskerRight α.toNatTrans H.toFunctor
  isHomLift' := fun _ => BasedFunctor.preserves_isHomLift _ _ _

Depends on / 依赖: Functor, Functor.whiskerRight, H.toFunctor, toFunctor, toNatTrans, whiskerRight
-/
def whiskerRight {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (H : 𝒴 ⥤ᵇ 𝒵) :
    F ⋙ H ⟶ G ⋙ H where
  toNatTrans := Functor.whiskerRight α.toNatTrans H.toFunctor
  isHomLift' := fun _ => BasedFunctor.preserves_isHomLift _ _ _

end

/-- The category of based categories. -/
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (BasedCategory.{v₂, u₂} 𝒮)
  body: BasedFunctor
  id := id
  comp := comp

中文:
实例 :
  签名: Category (BasedCategory.{v₂, u₂} 𝒮)
  定义体: BasedFunctor
  id := id
  comp := comp

Depends on / 依赖: BasedFunctor
-/
instance : Category (BasedCategory.{v₂, u₂} 𝒮) where
  Hom := BasedFunctor
  id := id
  comp := comp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `bicategory` / 实例 `bicategory`

English:
instance bicategory
  signature: : Bicategory (BasedCategory.{v₂, u₂} 𝒮) where
  body: 𝒳 ⥤ᵇ 𝒴
  id 𝒳 := 𝟭 𝒳
  comp F G := F ⋙ G
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {_ _ _} F {_ _} α := whiskerLeft F α
  whiskerRight {_ _ _} _ _ α H := whiskerRight α H
  associator _ _ _ := BasedNatIso.id _
  leftUnitor {_ _} F := BasedNatIso.id F
  rightUnitor {_ _} F := BasedNatIso.id 

中文:
实例 bicategory
  签名: : Bicategory (BasedCategory.{v₂, u₂} 𝒮) where
  定义体: 𝒳 ⥤ᵇ 𝒴
  id 𝒳 := 𝟭 𝒳
  comp F G := F ⋙ G
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {_ _ _} F {_ _} α := whiskerLeft F α
  whiskerRight {_ _ _} _ _ α H := whiskerRight α H
  associator _ _ _ := BasedNatIso.id _
  leftUnitor {_ _} F := BasedNatIso.id F
  rightUnitor {_ _} F := BasedNatIso.id 
-/
instance bicategory : Bicategory (BasedCategory.{v₂, u₂} 𝒮) where
  Hom 𝒳 𝒴 := 𝒳 ⥤ᵇ 𝒴
  id 𝒳 := 𝟭 𝒳
  comp F G := F ⋙ G
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {_ _ _} F {_ _} α := whiskerLeft F α
  whiskerRight {_ _ _} _ _ α H := whiskerRight α H
  associator _ _ _ := BasedNatIso.id _
  leftUnitor {_ _} F := BasedNatIso.id F
  rightUnitor {_ _} F := BasedNatIso.id F

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory.Strict (BasedCategory.{v₂, u₂} 𝒮)

中文:
实例 :
  签名: Bicategory.Strict (BasedCategory.{v₂, u₂} 𝒮)
-/
instance : Bicategory.Strict (BasedCategory.{v₂, u₂} 𝒮) where

end BasedCategory

end CategoryTheory
