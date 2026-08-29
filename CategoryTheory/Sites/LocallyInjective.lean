/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Locally injective morphisms of (pre)sheaves

Let `C` be a category equipped with a Grothendieck topology `J`,
and let `D` be a concrete category. In this file, we introduce the typeclass
`Presheaf.IsLocallyInjective J φ` for a morphism `φ : F₁ ⟶ F₂` in the category
`Cᵒᵖ ⥤ D`. This means that `φ` is locally injective. More precisely,
if `x` and `y` are two elements of some `F₁.obj U` such
the images of `x` and `y` in `F₂.obj U` coincide, then
the equality `x = y` must hold locally, i.e. after restriction
by the maps of a covering sieve.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D -> D -> Type*} {CD : D -> Type w}
  [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  (J : GrothendieckTopology C)

namespace Presheaf

/-- If `F : Cᵒᵖ ⥤ D` is a presheaf with values in a concrete category, if `x` and `y` are
elements in `F.obj X`, this is the sieve of `X.unop` consisting of morphisms `f`
such that `F.map f.op x = F.map f.op y`. -/
@[simps]
/--
Definition of `equalizerSieve` / `equalizerSieve` 的定义

English:
definition equalizerSieve
  signature: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X))
  body: F.map f.op x = F.map f.op y
  downward_closed {X Y} f hf g := by
    dsimp at hf ⊢
    simp [hf]

@[simp]

中文:
定义 equalizerSieve
  签名: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X))
  定义体: F.map f.op x = F.map f.op y
  downward_closed {X Y} f hf g := by
    dsimp at hf ⊢
    simp [hf]

@[simp]

Depends on / 依赖: F.map, f.op
-/
def equalizerSieve {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X)) : Sieve X.unop where
  arrows _ f := F.map f.op x = F.map f.op y
  downward_closed {X Y} f hf g := by
    dsimp at hf ⊢
    simp [hf]

@[simp]
/--
lemma `equalizerSieve_self_eq_top` / 引理 `equalizerSieve_self_eq_top`

English:
lemma equalizerSieve_self_eq_top
  given: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X))
  proof: by aesop

@[simp]

中文:
引理 equalizerSieve_self_eq_top
  条件: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X))
  证明: by aesop

@[simp]
-/
lemma equalizerSieve_self_eq_top {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X)) :
    equalizerSieve x x = ⊤ := by aesop

@[simp]
/--
lemma `equalizerSieve_eq_top_iff` / 引理 `equalizerSieve_eq_top_iff`

English:
lemma equalizerSieve_eq_top_iff
  given: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X))
  proof: by
  constructor
  · intro h
    simpa using (show equalizerSieve x y (𝟙 _) by simp [h])
  · rintro rfl
    apply equalizerSieve_self_eq_top

中文:
引理 equalizerSieve_eq_top_iff
  条件: {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X))
  证明: by
  constructor
  · intro h
    simpa using (show equalizerSieve x y (𝟙 _) by simp [h])
  · rintro rfl
    apply equalizerSieve_self_eq_top

Depends on / 依赖: equalizerSieve, equalizerSieve_self_eq_top
-/
lemma equalizerSieve_eq_top_iff {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X)) :
    equalizerSieve x y = ⊤ ↔ x = y := by
  constructor
  · intro h
    simpa using (show equalizerSieve x y (𝟙 _) by simp [h])
  · rintro rfl
    apply equalizerSieve_self_eq_top

variable {F₁ F₂ F₃ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

/--
Definition of `IsLocallyInjective` / `IsLocallyInjective` 的定义

English:
class IsLocallyInjective
  parameters: : Prop where
  axioms and operations (1):
    - equalizerSieve_mem({X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y)) : equalizerSieve x y in J X.unop

中文:
类 IsLocallyInjective
  参数: : 命题 where
  公理与运算 (1 个):
    - equalizerSieve_mem({X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y)) : equalizerSieve x y in J X.unop
-/
class IsLocallyInjective : Prop where
  equalizerSieve_mem {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y in J X.unop

/--
lemma `equalizerSieve_mem` / 引理 `equalizerSieve_mem`

English:
lemma equalizerSieve_mem
  statement: [IsLocallyInjective J φ]
  proof: IsLocallyInjective.equalizerSieve_mem x y h

中文:
引理 equalizerSieve_mem
  结论: [IsLocallyInjective J φ]
  证明: IsLocallyInjective.equalizerSieve_mem x y h

Depends on / 依赖: IsLocallyInjective, IsLocallyInjective.equalizerSieve_mem, equalizerSieve_mem
-/
lemma equalizerSieve_mem [IsLocallyInjective J φ]
    {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y in J X.unop :=
  IsLocallyInjective.equalizerSieve_mem x y h

/--
lemma `isLocallyInjective_of_injective` / 引理 `isLocallyInjective_of_injective`

English:
lemma isLocallyInjective_of_injective
  given: (hφ : forall (X : Cᵒᵖ), Function.Injective (φ.app X))
  proof: by
    convert! J.top_mem X.unop
    ext Y f
    simp only [equalizerSieve_apply, op_unop, Sieve.top_apply, iff_true]
    apply hφ
    simp [h]

中文:
引理 isLocallyInjective_of_injective
  条件: (hφ : 对任意 (X : Cᵒᵖ), Function.Injective (φ.app X))
  证明: by
    convert! J.top_mem X.unop
    ext Y f
    simp only [equalizerSieve_apply, op_unop, Sieve.top_apply, iff_true]
    apply hφ
    simp [h]

Depends on / 依赖: J.top_mem, Sieve.top_apply, X.unop, convert, equalizerSieve_apply, iff_true, op_unop, top_apply, top_mem
-/
lemma isLocallyInjective_of_injective (hφ : forall (X : Cᵒᵖ), Function.Injective (φ.app X)) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := by
    convert! J.top_mem X.unop
    ext Y f
    simp only [equalizerSieve_apply, op_unop, Sieve.top_apply, iff_true]
    apply hφ
    simp [h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: φ] : IsLocallyInjective J φ
  body: isLocallyInjective_of_injective J φ (fun X => Function.Bijective.injective (by
    rw [bijective_iff_isIso_ofHom]
    infer_instance))

中文:
实例 [IsIso
  签名: φ] : IsLocallyInjective J φ
  定义体: isLocallyInjective_of_injective J φ (fun X => Function.Bijective.injective (by
    rw [bijective_iff_isIso_ofHom]
    infer_instance))

Depends on / 依赖: Bijective, Function, Function.Bijective.injective, bijective_iff_isIso_ofHom, infer_instance, injective, isLocallyInjective_of_injective
-/
instance [IsIso φ] : IsLocallyInjective J φ :=
  isLocallyInjective_of_injective J φ (fun X => Function.Bijective.injective (by
    rw [bijective_iff_isIso_ofHom]
    infer_instance))

/--
Instance `isLocallyInjective_forget` / 实例 `isLocallyInjective_forget`

English:
instance isLocallyInjective_forget
  signature: [IsLocallyInjective J φ]
  body: equalizerSieve_mem J φ x y h

中文:
实例 isLocallyInjective_forget
  签名: [IsLocallyInjective J φ]
  定义体: equalizerSieve_mem J φ x y h

Depends on / 依赖: equalizerSieve_mem
-/
instance isLocallyInjective_forget [IsLocallyInjective J φ] :
    IsLocallyInjective J (Functor.whiskerRight φ (forget D)) where
  equalizerSieve_mem x y h := equalizerSieve_mem J φ x y h

/--
lemma `isLocallyInjective_forget_iff` / 引理 `isLocallyInjective_forget_iff`

English:
lemma isLocallyInjective_forget_iff
  proof: by
  constructor
  · intro
    exact ⟨fun x y h => equalizerSieve_mem J (Functor.whiskerRight φ (forget D)) x y h⟩
  · intro
    infer_instance

中文:
引理 isLocallyInjective_forget_iff
  证明: by
  constructor
  · intro
    exact ⟨fun x y h => equalizerSieve_mem J (Functor.whiskerRight φ (forget D)) x y h⟩
  · intro
    infer_instance

Depends on / 依赖: Functor, Functor.whiskerRight, equalizerSieve_mem, forget, infer_instance, whiskerRight
-/
lemma isLocallyInjective_forget_iff :
    IsLocallyInjective J (Functor.whiskerRight φ (forget D)) ↔ IsLocallyInjective J φ := by
  constructor
  · intro
    exact ⟨fun x y h => equalizerSieve_mem J (Functor.whiskerRight φ (forget D)) x y h⟩
  · intro
    infer_instance

/--
lemma `isLocallyInjective_iff_equalizerSieve_mem_imp` / 引理 `isLocallyInjective_iff_equalizerSieve_mem_imp`

English:
lemma isLocallyInjective_iff_equalizerSieve_mem_imp
  proof: by
  constructor
  · intro _ X x y h
    let S := equalizerSieve (φ.app _ x) (φ.app _ y)
    let T : forall ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f _ =>
      equalizerSieve (F₁.map f.op x) ((F₁.map f.op y))
    refine J.superset_covering ?_ (J.transitive h (Sieve.bind S.1 T) ?_)
    

中文:
引理 isLocallyInjective_iff_equalizerSieve_mem_imp
  证明: by
  constructor
  · intro _ X x y h
    let S := equalizerSieve (φ.app _ x) (φ.app _ y)
    let T : forall ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f _ =>
      equalizerSieve (F₁.map f.op x) ((F₁.map f.op y))
    refine J.superset_covering ?_ (J.transitive h (Sieve.bind S.1 T) ?_)
    

Depends on / 依赖: J.superset_covering, J.transitive, NatTrans, NatTrans.naturality_apply, Sieve.bind, Sieve.le_pullback_bind, X.unop, equalizerSieve, equalizerSieve_mem, f.op, le_pullback_bind, naturality_apply, superset_covering, transitive
-/
lemma isLocallyInjective_iff_equalizerSieve_mem_imp :
    IsLocallyInjective J φ ↔ forall ⦃X : Cᵒᵖ⦄ (x y : ToType (F₁.obj X)),
      equalizerSieve (φ.app _ x) (φ.app _ y) in J X.unop -> equalizerSieve x y in J X.unop := by
  constructor
  · intro _ X x y h
    let S := equalizerSieve (φ.app _ x) (φ.app _ y)
    let T : forall ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f _ =>
      equalizerSieve (F₁.map f.op x) ((F₁.map f.op y))
    refine J.superset_covering ?_ (J.transitive h (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using! ha
    · intro Y f hf
      refine J.superset_covering (Sieve.le_pullback_bind S.1 T _ hf)
        (equalizerSieve_mem J φ _ _ ?_)
      rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]
      exact hf
  · intro hφ
    exact ⟨fun {X} x y h => hφ x y (by simp [h])⟩

/--
lemma `equalizerSieve_mem_of_equalizerSieve_app_mem` / 引理 `equalizerSieve_mem_of_equalizerSieve_app_mem`

English:
lemma equalizerSieve_mem_of_equalizerSieve_app_mem
  proof: (isLocallyInjective_iff_equalizerSieve_mem_imp J φ).1 inferInstance x y h

中文:
引理 equalizerSieve_mem_of_equalizerSieve_app_mem
  证明: (isLocallyInjective_iff_equalizerSieve_mem_imp J φ).1 inferInstance x y h

Depends on / 依赖: isLocallyInjective_iff_equalizerSieve_mem_imp
-/
lemma equalizerSieve_mem_of_equalizerSieve_app_mem
    {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : equalizerSieve (φ.app _ x) (φ.app _ y) in J X.unop)
    [IsLocallyInjective J φ] :
    equalizerSieve x y in J X.unop :=
  (isLocallyInjective_iff_equalizerSieve_mem_imp J φ).1 inferInstance x y h

/--
Instance `isLocallyInjective_comp` / 实例 `isLocallyInjective_comp`

English:
instance isLocallyInjective_comp
  signature: [IsLocallyInjective J φ] [IsLocallyInjective J ψ]
  body: by
    apply equalizerSieve_mem_of_equalizerSieve_app_mem J φ
    exact equalizerSieve_mem J ψ _ _ (by simpa using h)

中文:
实例 isLocallyInjective_comp
  签名: [IsLocallyInjective J φ] [IsLocallyInjective J ψ]
  定义体: by
    apply equalizerSieve_mem_of_equalizerSieve_app_mem J φ
    exact equalizerSieve_mem J ψ _ _ (by simpa using h)

Depends on / 依赖: equalizerSieve_mem, equalizerSieve_mem_of_equalizerSieve_app_mem
-/
instance isLocallyInjective_comp [IsLocallyInjective J φ] [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) where
  equalizerSieve_mem {X} x y h := by
    apply equalizerSieve_mem_of_equalizerSieve_app_mem J φ
    exact equalizerSieve_mem J ψ _ _ (by simpa using h)

/--
lemma `isLocallyInjective_of_isLocallyInjective` / 引理 `isLocallyInjective_of_isLocallyInjective`

English:
lemma isLocallyInjective_of_isLocallyInjective
  given: [IsLocallyInjective J (φ ≫ ψ)]
  proof: equalizerSieve_mem J (φ ≫ ψ) x y (by simp [h])

中文:
引理 isLocallyInjective_of_isLocallyInjective
  条件: [IsLocallyInjective J (φ ≫ ψ)]
  证明: equalizerSieve_mem J (φ ≫ ψ) x y (by simp [h])

Depends on / 依赖: equalizerSieve_mem
-/
lemma isLocallyInjective_of_isLocallyInjective [IsLocallyInjective J (φ ≫ ψ)] :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := equalizerSieve_mem J (φ ≫ ψ) x y (by simp [h])

variable {φ ψ}

/--
lemma `isLocallyInjective_of_isLocallyInjective_fac` / 引理 `isLocallyInjective_of_isLocallyInjective_fac`

English:
lemma isLocallyInjective_of_isLocallyInjective_fac
  statement: {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
  proof: by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective J φ ψ

中文:
引理 isLocallyInjective_of_isLocallyInjective_fac
  结论: {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
  证明: by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective J φ ψ

Depends on / 依赖: isLocallyInjective_of_isLocallyInjective
-/
lemma isLocallyInjective_of_isLocallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [IsLocallyInjective J φψ] : IsLocallyInjective J φ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective J φ ψ

/--
lemma `isLocallyInjective_iff_of_fac` / 引理 `isLocallyInjective_iff_of_fac`

English:
lemma isLocallyInjective_iff_of_fac
  given: {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ]
  proof: by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

中文:
引理 isLocallyInjective_iff_of_fac
  条件: {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ]
  证明: by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

Depends on / 依赖: infer_instance, isLocallyInjective_of_isLocallyInjective_fac
-/
lemma isLocallyInjective_iff_of_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ] :
    IsLocallyInjective J φψ ↔ IsLocallyInjective J φ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

variable (φ ψ)

/--
lemma `isLocallyInjective_comp_iff` / 引理 `isLocallyInjective_comp_iff`

English:
lemma isLocallyInjective_comp_iff
  given: [IsLocallyInjective J ψ]
  proof: isLocallyInjective_iff_of_fac J rfl

中文:
引理 isLocallyInjective_comp_iff
  条件: [IsLocallyInjective J ψ]
  证明: isLocallyInjective_iff_of_fac J rfl

Depends on / 依赖: isLocallyInjective_iff_of_fac
-/
lemma isLocallyInjective_comp_iff [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) ↔ IsLocallyInjective J φ :=
  isLocallyInjective_iff_of_fac J rfl

/--
lemma `isLocallyInjective_iff_injective_of_separated` / 引理 `isLocallyInjective_iff_injective_of_separated`

English:
lemma isLocallyInjective_iff_injective_of_separated
  proof: by
  constructor
  · intro _ X x y h
    exact (hsep _ (equalizerSieve_mem J φ x y h)).ext (fun _ _ hf => hf)
  · apply isLocallyInjective_of_injective

中文:
引理 isLocallyInjective_iff_injective_of_separated
  证明: by
  constructor
  · intro _ X x y h
    exact (hsep _ (equalizerSieve_mem J φ x y h)).ext (fun _ _ hf => hf)
  · apply isLocallyInjective_of_injective

Depends on / 依赖: equalizerSieve_mem, isLocallyInjective_of_injective
-/
lemma isLocallyInjective_iff_injective_of_separated
    (hsep : Presieve.IsSeparated J (F₁ ⋙ forget D)) :
    IsLocallyInjective J φ ↔ forall (X : Cᵒᵖ), Function.Injective (φ.app X) := by
  constructor
  · intro _ X x y h
    exact (hsep _ (equalizerSieve_mem J φ x y h)).ext (fun _ _ hf => hf)
  · apply isLocallyInjective_of_injective

instance (F : Cᵒᵖ ⥤ Type w) (G : Subfunctor F) :
    IsLocallyInjective J G.ι :=
  isLocallyInjective_of_injective _ _ (fun X => by
    intro ⟨x, _⟩ ⟨y, _⟩ h
    exact Subtype.ext h)

section

open GrothendieckTopology.Plus

/--
Instance `isLocallyInjective_toPlus` / 实例 `isLocallyInjective_toPlus`

English:
instance isLocallyInjective_toPlus
  signature: (P : Cᵒᵖ ⥤ Type (max u v))
  body: by
    rw [toPlus_eq_mk]; rw [toPlus_eq_mk]; rw [eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

中文:
实例 isLocallyInjective_toPlus
  签名: (P : Cᵒᵖ ⥤ Type (max u v))
  定义体: by
    rw [toPlus_eq_mk]; rw [toPlus_eq_mk]; rw [eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

Depends on / 依赖: J.superset_covering, Subtype, Subtype.val, congr_arg, congr_fun, eq_mk_iff_exists, superset_covering, toPlus_eq_mk
-/
instance isLocallyInjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk]; rw [toPlus_eq_mk]; rw [eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isLocallyInjective_toSheafify` / 实例 `isLocallyInjective_toSheafify`

English:
instance isLocallyInjective_toSheafify
  signature: (P : Cᵒᵖ ⥤ Type (max u v))
  body: by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

中文:
实例 isLocallyInjective_toSheafify
  签名: (P : Cᵒᵖ ⥤ Type (max u v))
  定义体: by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.plusMap_toPlus, GrothendieckTopology.toSheafify, infer_instance, plusMap_toPlus, toSheafify
-/
instance isLocallyInjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallyInjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/--
Instance `isLocallyInjective_toSheafify'` / 实例 `isLocallyInjective_toSheafify'`

English:
instance isLocallyInjective_toSheafify'
  signature: {CD : D -> Type (max u v)}
  body: by
  rw [← isLocallyInjective_forget_iff]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

中文:
实例 isLocallyInjective_toSheafify'
  签名: {CD : D -> Type (max u v)}
  定义体: by
  rw [← isLocallyInjective_forget_iff]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

Depends on / 依赖: infer_instance, isLocallyInjective_forget_iff, sheafComposeIso_hom_fac, toSheafify_plusPlusIsoSheafify_hom
-/
instance isLocallyInjective_toSheafify' {CD : D -> Type (max u v)}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max u v} D FD]
    (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] :
    IsLocallyInjective J (toSheafify J P) := by
  rw [← isLocallyInjective_forget_iff]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ : Sheaf J D} (φ : F₁ ⟶ F₂)

/--
Definition of `IsLocallyInjective` / `IsLocallyInjective` 的定义

English:
abbreviation IsLocallyInjective
  body: Presheaf.IsLocallyInjective J φ.hom

中文:
缩写 IsLocallyInjective
  定义体: Presheaf.IsLocallyInjective J φ.hom

Depends on / 依赖: IsLocallyInjective, Presheaf, Presheaf.IsLocallyInjective
-/
abbrev IsLocallyInjective := Presheaf.IsLocallyInjective J φ.hom

/--
lemma `isLocallyInjective_sheafToPresheaf_map_iff` / 引理 `isLocallyInjective_sheafToPresheaf_map_iff`

English:
lemma isLocallyInjective_sheafToPresheaf_map_iff
  proof: by rfl

中文:
引理 isLocallyInjective_sheafToPresheaf_map_iff
  证明: by rfl
-/
lemma isLocallyInjective_sheafToPresheaf_map_iff :
    Presheaf.IsLocallyInjective J ((sheafToPresheaf J D).map φ) ↔ IsLocallyInjective φ := by rfl

/--
Instance `isLocallyInjective_of_iso` / 实例 `isLocallyInjective_of_iso`

English:
instance isLocallyInjective_of_iso
  signature: [IsIso φ]
  body: by
  change Presheaf.IsLocallyInjective J ((sheafToPresheaf _ _).map φ)
  infer_instance

中文:
实例 isLocallyInjective_of_iso
  签名: [IsIso φ]
  定义体: by
  change Presheaf.IsLocallyInjective J ((sheafToPresheaf _ _).map φ)
  infer_instance

Depends on / 依赖: IsLocallyInjective, Presheaf, Presheaf.IsLocallyInjective, infer_instance, sheafToPresheaf
-/
instance isLocallyInjective_of_iso [IsIso φ] : IsLocallyInjective φ := by
  change Presheaf.IsLocallyInjective J ((sheafToPresheaf _ _).map φ)
  infer_instance

/--
lemma `mono_of_injective` / 引理 `mono_of_injective`

English:
lemma mono_of_injective
  proof: have : forall X, Mono (φ.hom.app X) := fun X => ConcreteCategory.mono_of_injective _ (hφ X)
  (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app φ.1)

中文:
引理 mono_of_injective
  证明: have : forall X, Mono (φ.hom.app X) := fun X => ConcreteCategory.mono_of_injective _ (hφ X)
  (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app φ.1)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, NatTrans, NatTrans.mono_of_mono_app, hom.app, mono_of_injective, mono_of_mono_app, mono_of_mono_map, sheafToPresheaf
-/
lemma mono_of_injective
    (hφ : forall (X : Cᵒᵖ), Function.Injective (φ.hom.app X)) : Mono φ :=
  have : forall X, Mono (φ.hom.app X) := fun X => ConcreteCategory.mono_of_injective _ (hφ X)
  (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app φ.1)

variable [J.HasSheafCompose (forget D)]

/--
Instance `isLocallyInjective_forget` / 实例 `isLocallyInjective_forget`

English:
instance isLocallyInjective_forget
  signature: [IsLocallyInjective φ]
  body: Presheaf.isLocallyInjective_forget J φ.1

中文:
实例 isLocallyInjective_forget
  签名: [IsLocallyInjective φ]
  定义体: Presheaf.isLocallyInjective_forget J φ.1

Depends on / 依赖: Presheaf, Presheaf.isLocallyInjective_forget, isLocallyInjective_forget
-/
instance isLocallyInjective_forget [IsLocallyInjective φ] :
    IsLocallyInjective ((sheafCompose J (forget D)).map φ) :=
  Presheaf.isLocallyInjective_forget J φ.1

/--
lemma `isLocallyInjective_iff_injective` / 引理 `isLocallyInjective_iff_injective`

English:
lemma isLocallyInjective_iff_injective
  proof: Presheaf.isLocallyInjective_iff_injective_of_separated _ _ (by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget D)).obj F₁).2)

中文:
引理 isLocallyInjective_iff_injective
  证明: Presheaf.isLocallyInjective_iff_injective_of_separated _ _ (by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget D)).obj F₁).2)

Depends on / 依赖: IsSheaf, Presheaf, Presheaf.isLocallyInjective_iff_injective_of_separated, Presieve, Presieve.IsSheaf.isSeparated, forget, isLocallyInjective_iff_injective_of_separated, isSeparated, isSheaf_iff_isSheaf_of_type, sheafCompose
-/
lemma isLocallyInjective_iff_injective :
    IsLocallyInjective φ ↔ forall (X : Cᵒᵖ), Function.Injective (φ.hom.app X) :=
  Presheaf.isLocallyInjective_iff_injective_of_separated _ _ (by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget D)).obj F₁).2)

/--
lemma `mono_of_isLocallyInjective` / 引理 `mono_of_isLocallyInjective`

English:
lemma mono_of_isLocallyInjective
  given: [IsLocallyInjective φ]
  statement: Mono φ
  proof: by
  apply mono_of_injective
  rw [← isLocallyInjective_iff_injective]
  infer_instance

中文:
引理 mono_of_isLocallyInjective
  条件: [IsLocallyInjective φ]
  结论: Mono φ
  证明: by
  apply mono_of_injective
  rw [← isLocallyInjective_iff_injective]
  infer_instance

Depends on / 依赖: infer_instance, isLocallyInjective_iff_injective, mono_of_injective
-/
lemma mono_of_isLocallyInjective [IsLocallyInjective φ] : Mono φ := by
  apply mono_of_injective
  rw [← isLocallyInjective_iff_injective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallyInjective (Sheaf.imageι f) := by
  dsimp [Sheaf.imageι]
  infer_instance

end Sheaf

end CategoryTheory
